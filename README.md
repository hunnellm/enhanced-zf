# enhanced-zf

`enhanced-zf` is a Python module for working with zero forcing on graphs, with explicit support for both **simple** and **looped** forcing rules. The code is written as a single library-style file, `loop-zf.py`, and focuses on graph-theoretic computations such as closures, forcing numbers, forcing paths, chronological force lists, reversal reconfiguration graphs, reordered forcing matrices, forts, blocking sets, and loop configurations.

## What it provides

The module keeps the two forcing models separate in its public API:

- **Simple zero forcing**: only blue vertices may force a unique white neighbor.
- **Looped zero forcing**: any vertex may force when it has exactly one white neighbor in the looped graph, where a chosen subset of vertices may carry loops.

This avoids ambiguous APIs and makes the intended forcing rule explicit in each function name.

## Main features

### Simple zero forcing

- `simple_zero_forcing_closure(g, initial_set)`
- `is_simple_zero_forcing_set(g, initial_set)`
- `simple_zero_forcing_number(g, return_sets=False)`
- `simple_forcing_paths(g, initial_set, verify_minimum=False)`
- `all_chronological_forces_simple(g, initial_set, return_vertex_orders=False)`
- `forcing_order_matrix_simple(g, force_order, include_idle_vertices=True)`
- `forcing_order_matrix_from_acf_entry_simple(g, acf_entry)`
- `reversal_reconfiguration_graph_simple(g, return_classes=False)`
- `reversal_map_simple(g)`
- Alias: `szf(g, return_sets=False)`

### Looped zero forcing

- `looped_zero_forcing_closure(g, initial_set, looped_vertices)`
- `is_looped_zero_forcing_set(g, initial_set, looped_vertices)`
- `looped_zero_forcing_number(g, looped_vertices, return_sets=False)`
- `maximum_looped_zero_forcing_number(g, return_configurations=False, return_sets=False)`
- `looped_forcing_paths(g, initial_set, looped_vertices, verify_minimum=False)`
- `all_chronological_forces_looped(g, initial_set, looped_vertices, return_vertex_orders=False)`
- `forcing_order_matrix_looped(g, force_order, looped_vertices, include_idle_vertices=True)`
- `forcing_order_matrix_from_acf_entry_looped(g, acf_entry, looped_vertices)`
- `reversal_reconfiguration_graph_looped(g, looped_vertices, return_classes=False)`
- `reversal_map_looped(g, looped_vertices)`
- Aliases: `lzf(g, looped_vertices, return_sets=False)`, `EZ(g, ...)`

### Additional graph utilities

The module also includes tools for related combinatorial objects and constructions:

- `loop_forts(...)`
- `is_loop_fort(...)`
- `minimal_loop_forts(...)`
- `loop_blocking_number(...)`
- `loop_blocking_sets(...)`
- `all_loop_configurations(...)`
- `all_loop_vertex_sets(...)`

## Graph input formats

The module accepts multiple graph-like inputs through its normalization layer:

- **Dictionary adjacency form**: `{vertex: [neighbors...]}`
- **NetworkX-like graphs**: objects with `.adjacency()`
- **SageMath-like graphs**: objects with `.vertices()` and `.neighbors(v)`

Vertices are normalized into a deterministic sorted order internally.

## Design notes

A few notable implementation choices:

- Public functions do **not** infer simple vs. looped semantics from missing parameters.
- Looped APIs require `looped_vertices` explicitly, even if it is the empty set.
- Several older ambiguous entry points are kept only as deprecated wrappers that raise guidance errors:
  - `all_chronological_forces(...)`
  - `acf(...)`
  - `forcing_order_matrix(...)`
  - `forcing_order_matrix_from_acf_entry(...)`

## Repository layout

```text
.
└── loop-zf.py   # core zero forcing library
```

## Getting started

Clone the repository:

```bash
git clone https://github.com/hunnellm/enhanced-zf.git
cd enhanced-zf
```

Since the repository currently consists of a single Python module, you can import it into your own scripts or notebooks after renaming the file to a Python-import-friendly module name if desired, or loading it directly.

Example using a dictionary-based graph:

```python
from importlib.machinery import SourceFileLoader

zf = SourceFileLoader("loop_zf", "loop-zf.py").load_module()

g = {
    0: [1],
    1: [0, 2],
    2: [1, 3],
    3: [2],
}

print(zf.simple_zero_forcing_number(g))
print(zf.simple_zero_forcing_closure(g, {0}))
print(zf.looped_zero_forcing_number(g, looped_vertices=set()))
```

## Example ideas

You can use this module to:

- compute minimum zero forcing sets,
- enumerate all valid chronological forcing sequences,
- build forcing-path decompositions,
- study reversal behavior of minimum forcing sets,
- compare simple and looped forcing numbers across loop configurations,
- compute loop forts and loop blocking sets.

## Notes on dependencies

The file is largely self-contained and imports only `itertools.combinations` directly. Some functions attempt to interoperate with environments such as SageMath, NetworkX, or matrix/graph constructors if those objects are available in the runtime.

## Future improvements

Possible next steps for the repository:

- package the module with a Python-friendly import name,
- add tests and worked examples,
- document expected behavior for SageMath and NetworkX usage,
- add benchmarks for exhaustive enumeration routines.
