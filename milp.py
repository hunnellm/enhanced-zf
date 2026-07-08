import itertools


def generate_transversal_vectors(
    dim=8,
    min_weight=3,
    min_transversal_size=4,
    target_num_vecs=8,
    find_all=False,
):
    """
    Find sets of binary vectors of length `dim` such that:
      1) each selected vector has Hamming weight >= min_weight
      2) selected set size is exactly target_num_vecs
      3) the minimum transversal size is exactly min_transversal_size, i.e.
         - every coordinate subset of size (min_transversal_size - 1) FAILS to hit all vectors
           (equivalently: for each such subset S, there exists a selected vector with zeros on S)
         - every coordinate subset of size min_transversal_size HITS all vectors
           (equivalently: no selected vector is all-zeros on any such subset)

    Returns:
      list of solutions; each solution is a list of bitstrings.
      If find_all=False, returns at most one solution.
    """

    # --------------------------
    # Basic parameter guards
    # --------------------------
    if dim <= 0:
        return []
    if min_transversal_size < 1 or min_transversal_size > dim:
        return []
    if min_weight < 0 or min_weight > dim:
        return []
    if target_num_vecs < 0:
        return []

    # ------------------------------------------------------------
    # 1) Candidate vectors as integer bitmasks (fast representation)
    # ------------------------------------------------------------
    # No proxy filter; enforce exact transversal property in search.
    candidates = [v for v in range(1 << dim) if v.bit_count() >= min_weight]
    n = len(candidates)
    if target_num_vecs > n:
        return []

    # ------------------------------------------------------------
    # 2) Build subsets:
    #    - short subsets of size t-1 must each be "covered"
    #    - exact subsets of size t must each be "hit" (forbidden all-zero)
    # ------------------------------------------------------------
    t = min_transversal_size

    short_masks = []
    for comb in itertools.combinations(range(dim), t - 1):
        m = 0
        for i in comb:
            m |= (1 << i)
        short_masks.append(m)

    exact_masks = []
    for comb in itertools.combinations(range(dim), t):
        m = 0
        for i in comb:
            m |= (1 << i)
        exact_masks.append(m)

    m_short = len(short_masks)

    # Degenerate case t=1:
    # - (t-1)=0 subset coverage condition is vacuous (single empty subset)
    # - exact size-1 subsets must all hit all vectors => every chosen vector must be all-ones.
    if t == 1:
        all_ones = (1 << dim) - 1
        valid_idxs = [i for i, v in enumerate(candidates) if v == all_ones]
        if len(valid_idxs) < target_num_vecs:
            return []
        vec_to_str = lambda x: format(x, f"0{dim}b")
        if not find_all:
            return [[vec_to_str(candidates[i]) for i in valid_idxs[:target_num_vecs]]]
        out = []
        for comb in itertools.combinations(valid_idxs, target_num_vecs):
            out.append([vec_to_str(candidates[i]) for i in comb])
        return out

    # ------------------------------------------------------------
    # 3) Precompute for each candidate:
    #    short_cov_bits: which (t-1)-subsets it "covers"
    #      (vector has zeros on that subset mask)
    #    exact_bad_mask_bits: which t-subsets it violates
    #      (vector has zeros on that subset mask) -> forbidden if any chosen vector violates any t-subset
    # ------------------------------------------------------------
    short_cov_bits = [0] * n
    exact_bad_bits = [0] * n

    for i, v in enumerate(candidates):
        sc = 0
        for j, sm in enumerate(short_masks):
            if (v & sm) == 0:
                sc |= (1 << j)
        short_cov_bits[i] = sc

        eb = 0
        for j, em in enumerate(exact_masks):
            if (v & em) == 0:
                eb |= (1 << j)
        exact_bad_bits[i] = eb

    full_short_cover = (1 << m_short) - 1

    # Fast impossibility check:
    # if union of all candidate short coverage doesn't cover all short subsets, no solution exists.
    union_all_short = 0
    for x in short_cov_bits:
        union_all_short |= x
    if union_all_short != full_short_cover:
        return []

    # ------------------------------------------------------------
    # 4) Candidate ordering heuristic:
    #    Prefer vectors that cover many short subsets and violate few exact subsets.
    # ------------------------------------------------------------
    order = sorted(
        range(n),
        key=lambda i: (short_cov_bits[i].bit_count(), -exact_bad_bits[i].bit_count()),
        reverse=True,
    )
    candidates = [candidates[i] for i in order]
    short_cov_bits = [short_cov_bits[i] for i in order]
    exact_bad_bits = [exact_bad_bits[i] for i in order]

    # ------------------------------------------------------------
    # 5) Suffix unions for pruning
    # ------------------------------------------------------------
    suffix_short_union = [0] * (n + 1)
    for i in range(n - 1, -1, -1):
        suffix_short_union[i] = suffix_short_union[i + 1] | short_cov_bits[i]

    # ------------------------------------------------------------
    # 6) Backtracking with strong pruning
    # ------------------------------------------------------------
    solutions_idx = []
    chosen = []

    def backtrack(start_idx, chosen_count, short_covered, exact_bad_union):
        # Stop after first if requested
        if not find_all and solutions_idx:
            return

        # If any chosen vector already violates some t-subset, fail immediately.
        # (A t-subset must hit ALL selected vectors.)
        if exact_bad_union != 0:
            return

        # Reached target number of vectors
        if chosen_count == target_num_vecs:
            if short_covered == full_short_cover:
                solutions_idx.append(chosen.copy())
            return

        # Need this many more vectors
        need = target_num_vecs - chosen_count

        # Not enough vectors left
        if n - start_idx < need:
            return

        # Even with all remaining vectors, can't cover all short subsets
        if (short_covered | suffix_short_union[start_idx]) != full_short_cover:
            return

        # Include current
        chosen.append(start_idx)
        backtrack(
            start_idx + 1,
            chosen_count + 1,
            short_covered | short_cov_bits[start_idx],
            exact_bad_union | exact_bad_bits[start_idx],
        )
        chosen.pop()

        # Exclude current
        backtrack(start_idx + 1, chosen_count, short_covered, exact_bad_union)

    backtrack(0, 0, 0, 0)

    # ------------------------------------------------------------
    # 7) Convert solutions to bitstrings
    # ------------------------------------------------------------
    def vec_to_str(x):
        return format(x, f"0{dim}b")

    out = []
    for sol in solutions_idx:
        out.append([vec_to_str(candidates[i]) for i in sol])
    return out
