import itertools

# 1. Generate all 214 valid candidate vectors
all_vecs = []
for p in itertools.product([0, 1], repeat=8):
    # Condition: weight >= 3 AND at least one '1' in the first 4 coordinates
    if sum(p) >= 3 and any(p[i] == 1 for i in range(4)):
        all_vecs.append(p)

# 2. Generate all 56 combinations of 3 coordinates
subsets_3 = list(combinations(range(8), 3))

# 3. Set up the Mixed Integer Linear Program
p = MixedIntegerLinearProgram(maximization=False) # False = Minimization
x = p.new_variable(binary=True)                   # Binary variables (0 or 1)

# 4. Define Objective: Minimize the total number of chosen vectors
p.set_objective(p.sum(x[i] for i in range(len(all_vecs))))

# 5. Add Constraints: Every 3-coordinate combination must be blocked by >= 1 vector
for s in subsets_3:
    # Find all vectors that have 0s at all coordinates in subset 's'
    blocking_vectors = [i for i, v in enumerate(all_vecs) if all(v[k] == 0 for k in s)]
    
    # Enforce that we pick at least one of these blocking vectors
    p.add_constraint(p.sum(x[i] for i in blocking_vectors) >= 1)

# 6. Solve and print the results
try:
    min_vectors = p.solve()
    print(f"Minimum vectors needed: {int(min_vectors)}")
    
    # Extract the selected vectors
    x_val = p.get_values(x)
    for i, v in enumerate(all_vecs):
        if x_val[i] == 1:
            print("".join(map(str, v)))
            
except MipError:
    print("No feasible solution found.")
