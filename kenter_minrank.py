"""SageMath implementation of Kenter's alternating-projection idea.

Reference: F. H. J. Kenter, Operations Research Letters 44 (2016),
255--259, doi:10.1016/j.orl.2016.02.001.
The core projections follow the publisher's Section 3 preview. Initialization,
normalization, restarts and acceptance rules below are implementation choices;
the full Algorithm 1 was not accessible when this implementation was written.
All results are floating-point evidence, not exact minimum-rank certificates.
"""

import operator
import numpy as np
from sage.all import RDF, matrix


def _integer(value, name, minimum):
    try:
        value = operator.index(value)
    except TypeError:
        raise ValueError(name + " must be an integer") from None
    if value < minimum:
        raise ValueError(name + " is too small")
    return value


def _graph_data(G, vertices=None):
    if G.is_directed() or G.has_loops() or G.has_multiple_edges():
        raise ValueError("G must be a simple undirected graph")
    vertices = list(G) if vertices is None else list(vertices)
    if len(vertices) != G.order() or set(vertices) != set(G):
        raise ValueError("vertices must list each vertex exactly once")
    n = len(vertices)
    edges = np.zeros((n, n), dtype=bool)
    index = {v: i for i, v in enumerate(vertices)}
    for u, v in G.edge_iterator(labels=False):
        edges[index[u], index[v]] = edges[index[v], index[u]] = True
    return vertices, edges, edges | np.eye(n, dtype=bool)


def _rank_projection(B, k):
    # For real symmetric matrices retain eigenvalues of largest ABSOLUTE value.
    # Keeping only positive eigenvalues would solve a different (PSD) problem.
    w, Q = np.linalg.eigh(B)
    keep = np.argsort(-np.abs(w), kind="stable")[:k]
    X = (Q[:, keep] * w[keep]) @ Q[:, keep].T
    return (X + X.T) / 2.0


def _diagnostics(B, X, edges, k):
    scale = float(np.linalg.norm(B, "fro"))
    if scale == 0.0:
        return dict(relative_gap=float("inf"), relative_tail=float("inf"),
                    relative_min_edge=0.0, numerical_rank=0)
    s = np.linalg.svd(B, compute_uv=False)
    return dict(relative_gap=float(np.linalg.norm(B-X, "fro") / scale),
                relative_tail=float(np.linalg.norm(s[k:]) / scale),
                relative_min_edge=(float(np.min(np.abs(B[edges]))) / scale
                                   if edges.any() else float("inf")),
                numerical_rank=int(np.sum(s > 1e-8 * s[0])))


def kenter_fixed_rank(G, k, *, restarts=20, max_iterations=5000,
                      tol=1e-9, edge_tol=1e-7, seed=None, vertices=None,
                      initial_matrix=None, normalize=True, history=False):
    """Search numerically for a real symmetric rank-at-most-k representation.

    Diagonal entries are unrestricted. Nonedges are set exactly to zero;
    edge weights are free and can have either sign. Each iteration computes
    X=P_rank(B), then B=P_pattern(X). The returned ``matrix`` has exact
    nonedge zeros but only approximate low rank. ``low_rank_matrix`` has
    approximate rank <= k but may have small nonedge entries.

    Success requires BOTH relative projection gap and spectral tail <= tol,
    and min(abs(edge entry))/Frobenius norm > edge_tol. Small changes between
    iterates alone do not imply success. Normalization to unit Frobenius norm
    is a scale safeguard (an extension of the two basic projections).
    The first start uses the adjacency matrix (or supplied initial_matrix);
    subsequent starts use random symmetric pattern matrices.

    ``success=False`` means only that this run found no acceptable candidate.
    ``numerical_rank`` is diagnostic, using a fixed relative threshold 1e-8.
    For an edgeless graph, zero is returned immediately.
    """
    vs, edges, allowed = _graph_data(G, vertices)
    n = len(vs)
    k = _integer(k, "k", 0)
    restarts = _integer(restarts, "restarts", 1)
    max_iterations = _integer(max_iterations, "max_iterations", 1)
    if k > n:
        raise ValueError("k must be at most the graph order")
    if not (np.isfinite(tol) and 0 < tol < 1):
        raise ValueError("tol must be finite and between 0 and 1")
    if not (np.isfinite(edge_tol) and 0 < edge_tol < 1):
        raise ValueError("edge_tol must be finite and between 0 and 1")
    initial = None
    if initial_matrix is not None:
        initial = np.asarray(initial_matrix, dtype=float)
        if initial.shape != (n, n) or not np.isfinite(initial).all():
            raise ValueError("initial_matrix must be finite and n by n")
        if not np.allclose(initial, initial.T, rtol=0, atol=1e-12):
            raise ValueError("initial_matrix must be symmetric")
        initial = (initial + initial.T) / 2.0
    def pack(B, X, d, success, restart, iteration, trace):
        return dict(success=success, target_rank=k, vertices=vs,
                    matrix=matrix(RDF, n, n, B.ravel().tolist()),
                    low_rank_matrix=matrix(RDF, n, n, X.ravel().tolist()),
                    restart=restart, iterations=iteration, history=trace, **d)
    if not edges.any():
        B = np.zeros((n, n))
        d = dict(relative_gap=0.0, relative_tail=0.0,
                 relative_min_edge=float("inf"), numerical_rank=0)
        return pack(B, B, d, True, 0, 0, [])
    rng = np.random.default_rng(seed)
    best, best_score = None, float("inf")
    for restart in range(1, restarts+1):
        if restart == 1 and initial is not None:
            B = initial.copy() * allowed
        elif restart == 1:
            B = edges.astype(float)
        else:
            R = rng.standard_normal((n, n))
            B = ((R+R.T)/2.0) * allowed
        norm = np.linalg.norm(B, "fro")
        if norm and normalize:
            B /= norm
        trace = []
        for iteration in range(1, max_iterations+1):
            X = _rank_projection(B, k)
            B = X * allowed
            norm = np.linalg.norm(B, "fro")
            if norm and normalize:
                B /= norm
                X /= norm
            d = _diagnostics(B, X, edges, k)
            if history:
                trace.append(dict(iteration=iteration, **d))
            valid_edges = d["relative_min_edge"] > edge_tol
            success = (valid_edges and d["relative_gap"] <= tol
                       and d["relative_tail"] <= tol)
            score = max(d["relative_gap"], d["relative_tail"])
            # Prioritize candidates that retain every required edge.
            score = score if valid_edges else 2.0 + min(score, 1.0)
            if best is None or score < best_score or success:
                best = pack(B, X, d, success, restart, iteration, list(trace))
                best_score = score
            if success:
                return best
            if norm == 0 or not np.isfinite(norm):
                break
    return best


def kenter_minrank(G, *, min_rank=0, max_rank=None, seed=None, **kwargs):
    """Try target ranks in ascending order; return first numerical success.

    min_rank can be a known lower bound (e.g. n-Z(G), if Z is known exactly).
    Failure at smaller ranks is NOT a lower bound. ``estimate=None`` means
    no success in the requested interval. ``trials`` retains each rank's report.
    """
    n = G.order()
    lo = _integer(min_rank, "min_rank", 0)
    hi = n if max_rank is None else _integer(max_rank, "max_rank", 0)
    if not 0 <= lo <= hi <= n:
        raise ValueError("require 0 <= min_rank <= max_rank <= order")
    rng = np.random.default_rng(seed)
    trials = []
    # A graph with an edge cannot have a rank-zero representation.
    start = max(lo, 1) if G.size() else lo
    for k in range(start, hi+1):
        report = kenter_fixed_rank(G, k, seed=int(rng.integers(2**32)), **kwargs)
        trials.append(report)
        if report["success"]:
            return dict(estimate=k, candidate=report, trials=trials,
                        certified=False)
    return dict(estimate=None, candidate=None, trials=trials, certified=False)
