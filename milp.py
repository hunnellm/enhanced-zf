import itertools


def _popcount(x):
    return int(x).bit_count()


def generate_transversal_vectors(
    dim=8,
    min_weight=3,
    min_transversal_size=4,
    target_num_vecs=8,
    find_all=False,
):
    """
    Find sets of binary vectors of length `dim` such that:
      - each selected vector has weight >= min_weight
      - selected set size is exactly target_num_vecs
      - transversal number is exactly t = min_transversal_size:
          (A) every (t-1)-subset S fails to hit all vectors
              <=> for every S, at least one selected vector is zero on all coords in S
          (B) there exists at least one t-subset T that hits all vectors
              <=> there exists T such that every selected vector has at least one 1 in T
    """

    dim = int(dim)
    min_weight = int(min_weight)
    t = int(min_transversal_size)
    target_num_vecs = int(target_num_vecs)

    if dim <= 0:
        return []
    if t < 1 or t > dim:
        return []
    if min_weight < 0 or min_weight > dim:
        return []
    if target_num_vecs < 0:
        return []

    # Candidates: all vectors meeting weight bound
    candidates = [v for v in range(1 << dim) if _popcount(v) >= min_weight]
    n = len(candidates)
    if target_num_vecs > n:
        return []

    # (t-1)-subsets that must each be "covered by a witness vector"
    short_masks = []
    for comb in itertools.combinations(range(dim), t - 1):
        m = 0
        for i in comb:
            m |= (1 << i)
        short_masks.append(m)
    m_short = len(short_masks)
    full_short_cover = (1 << m_short) - 1 if m_short > 0 else 0

    # t-subsets: at least one must be a global hitter
    t_masks = []
    for comb in itertools.combinations(range(dim), t):
        m = 0
        for i in comb:
            m |= (1 << i)
        t_masks.append(m)
    m_t = len(t_masks)

    # Precompute:
    # short_cov_bits[i]: which (t-1)-subsets vector i is zero on (witnesses failure)
    # miss_t_bits[i]: which t-subsets vector i MISSES (i.e., has all zeros on T)
    short_cov_bits = [0] * n
    miss_t_bits = [0] * n

    for i, v in enumerate(candidates):
        sc = 0
        for j, sm in enumerate(short_masks):
            if (v & sm) == 0:
                sc |= (1 << j)
        short_cov_bits[i] = sc

        mt = 0
        for j, tm in enumerate(t_masks):
            if (v & tm) == 0:
                mt |= (1 << j)
        miss_t_bits[i] = mt

    # Necessary feasibility for (A)
    union_all_short = 0
    for b in short_cov_bits:
        union_all_short |= b
    if union_all_short != full_short_cover:
        return []

    # Candidate ordering heuristic
    order = sorted(
        range(n),
        key=lambda i: (_popcount(short_cov_bits[i]), -_popcount(miss_t_bits[i])),
        reverse=True,
    )
    candidates = [candidates[i] for i in order]
    short_cov_bits = [short_cov_bits[i] for i in order]
    miss_t_bits = [miss_t_bits[i] for i in order]

    # Suffix union for short-cover pruning
    suffix_short_union = [0] * (n + 1)
    for i in range(n - 1, -1, -1):
        suffix_short_union[i] = suffix_short_union[i + 1] | short_cov_bits[i]

    solutions_idx = []
    chosen = []

    # miss_union over chosen vectors:
    # bit j=1 means "some chosen vector misses t-subset j"
    # A t-subset hits ALL chosen vectors iff its bit in miss_union is 0.
    def backtrack(start_idx, chosen_count, short_covered, miss_union):
        if not find_all and solutions_idx:
            return

        if chosen_count == target_num_vecs:
            cond_A = (short_covered == full_short_cover)
            cond_B = (miss_union != (1 << m_t) - 1)  # at least one t-subset not missed by anyone
            if cond_A and cond_B:
                solutions_idx.append(chosen.copy())
            return

        need = target_num_vecs - chosen_count
        if n - start_idx < need:
            return

        # prune A
        if (short_covered | suffix_short_union[start_idx]) != full_short_cover:
            return

        # Include
        chosen.append(start_idx)
        backtrack(
            start_idx + 1,
            chosen_count + 1,
            short_covered | short_cov_bits[start_idx],
            miss_union | miss_t_bits[start_idx],
        )
        chosen.pop()

        # Exclude
        backtrack(start_idx + 1, chosen_count, short_covered, miss_union)

    backtrack(0, 0, 0, 0)

    return [[format(candidates[i], f"0{dim}b") for i in sol] for sol in solutions_idx]
