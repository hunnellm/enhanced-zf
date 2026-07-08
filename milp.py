import itertools

def generate_transversal_vectors(dim=8, min_weight=3, min_transversal_size=4, target_num_vecs=8, find_all=False):
    """
    Generates sets of vectors satisfying weight and minimal transversal constraints.
    
    Arguments:
    - dim: Dimension of the space (vector length)
    - min_weight: Minimum weight of each vector
    - min_transversal_size: The exact size of the minimum coordinate filter needed
    - target_num_vecs: Number of vectors allowed in a final solution set
    - find_all: Boolean. If True, returns ALL valid combinations. If False, returns the first found.
    """
    
    # 1. Generate all valid candidate vectors matching basic filters
    all_vecs = []
    for p in itertools.product([0, 1], repeat=dim):
        # Must have sufficient weight, and must have at least one '1' in our target filter zone
        if sum(p) >= min_weight and any(p[i] == 1 for i in range(min_transversal_size)):
            all_vecs.append(p)
            
    # 2. Define the "shortcuts" that must fail
    # Any combination of size (min_transversal_size - 1) must fail to block the vector pool
    shortcut_size = min_transversal_size - 1
    subsets_shortcut = list(combinations(range(dim), shortcut_size))
    
    # Precalculate which vectors successfully block each shortcut
    # (A vector blocks a shortcut if it contains ALL 0s at those shortcut coordinate indices)
    shortcut_to_blocking_vecs = {}
    for s in subsets_shortcut:
        blocking = [i for i, v in enumerate(all_vecs) if all(v[k] == 0 for k in s)]
        shortcut_to_blocking_vecs[s] = set(blocking)
        
    solutions = []
    
    # 3. Backtracking search to find combinations of size `target_num_vecs`
    def search(start_idx, current_combination, covered_shortcuts):
        # If we already found one and user didn't ask for all, stop searching
        if not find_all and len(solutions) > 0:
            return

        # Check if we hit our target vector set size
        if len(current_combination) == target_num_vecs:
            if len(covered_shortcuts) == len(subsets_shortcut):
                # Valid solution found! Convert indices back to vector strings or tuples
                sol = ["".join(map(str, all_vecs[i])) for i in current_combination]
                solutions.append(sol)
            return
            
        # Pruning condition: Not enough remaining vectors in the candidate pool to hit target size
        if start_idx + (target_num_vecs - len(current_combination)) > len(all_vecs):
            return
            
        # Option A: Include the vector at start_idx
        new_covered = covered_shortcuts.copy()
        for s in subsets_shortcut:
            if start_idx in shortcut_to_blocking_vecs[s]:
                new_covered.add(s)
                
        current_combination.append(start_idx)
        search(start_idx + 1, current_combination, new_covered)
        current_combination.pop() # Backtrack
        
        # Option B: Exclude the vector at start_idx
        search(start_idx + 1, current_combination, covered_shortcuts)

    # Trigger the combinatorial search
    search(0, [], set())
    return solutions

# ==========================================
# HOW TO RUN THE FUNCTION IN SAGEMATH
# ==========================================
"""
# Example 1: Find a single optimal set of 8 vectors matching your original constraints
single_set = generate_transversal_vectors(dim=8, min_weight=3, min_transversal_size=4, target_num_vecs=8, find_all=False)
print(f"Found {len(single_set)} solution set(s):")
print(single_set)
"""

# Example 2: Scale it up! Find a solution set for 10-dimensional space, weight >= 4, transversal size 5
# scaled_set = generate_transversal_vectors(dim=10, min_weight=4, min_transversal_size=5, target_num_vecs=12, find_all=False)
