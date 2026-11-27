#!/usr/bin/env python3
"""Independently check the six-vertex coloring lemma using only Python's stdlib.

Run from any directory with Python 3.10 or newer:
    python scripts/check_exhaustive.py

The program checks all 32,768 labeled simple graphs on six vertices. For every
triangle-free graph it constructs a vertex coloring from the C5 argument in
docs/proof.md, then checks the required extension for EVERY coloring of its
edges. It prints deterministic JSON and exits unsuccessfully on a failure.

This is an ordinary exhaustive computation, not a Lean kernel certificate.
The source code here is an independent implementation; the previously accepted
upstream proof is acknowledged in docs/proof.md.
"""

from itertools import combinations, permutations
import json


N = 6
VERTICES = tuple(range(N))
ALL_VERTICES = (1 << N) - 1
EDGES = tuple(combinations(VERTICES, 2))
EDGE_INDEX = {edge: index for index, edge in enumerate(EDGES)}


def edge_bit(u: int, v: int) -> int:
    """Encode an unordered pair of distinct vertices."""
    return 1 << EDGE_INDEX[min(u, v), max(u, v)]


TRIANGLES = tuple(
    edge_bit(a, b) | edge_bit(a, c) | edge_bit(b, c)
    for a, b, c in combinations(VERTICES, 3)
)


def five_cycles() -> tuple[tuple[tuple[int, ...], int], ...]:
    """List each undirected five-cycle once, with a fixed starting point."""
    cycles = []
    for vertices in combinations(VERTICES, 5):
        first, *rest = vertices
        for tail in permutations(rest):
            if tail[0] > tail[-1]:
                continue
            cycle = (first,) + tail
            mask = 0
            for i in range(5):
                mask |= edge_bit(cycle[i], cycle[(i + 1) % 5])
            cycles.append((cycle, mask))
    return tuple(cycles)


FIVE_CYCLES = five_cycles()


def same_color_pairs(coloring: int) -> tuple[int, int]:
    """Masks of pairs whose endpoints are both false, or both true."""
    both_false = both_true = 0
    for index, (u, v) in enumerate(EDGES):
        u_true = bool(coloring & (1 << u))
        v_true = bool(coloring & (1 << v))
        if u_true and v_true:
            both_true |= 1 << index
        elif not u_true and not v_true:
            both_false |= 1 << index
    return both_false, both_true


PAIR_COLORS = tuple(same_color_pairs(c) for c in range(1 << N))


def bipartition(graph: int) -> int | None:
    """Return a proper vertex two-coloring, or None if an odd cycle is found."""
    neighbors = [[] for _ in VERTICES]
    for index, (u, v) in enumerate(EDGES):
        if graph & (1 << index):
            neighbors[u].append(v)
            neighbors[v].append(u)

    colors = [-1] * N
    for start in VERTICES:
        if colors[start] != -1:
            continue
        colors[start] = 0
        stack = [start]
        while stack:
            u = stack.pop()
            for v in neighbors[u]:
                if colors[v] == -1:
                    colors[v] = 1 - colors[u]
                    stack.append(v)
                elif colors[v] == colors[u]:
                    return None
    return sum(color << vertex for vertex, color in enumerate(colors))


def c5_coloring(graph: int) -> tuple[int, int]:
    """Implement the structural proof for a nonbipartite triangle-free graph.

    Returns a vertex coloring and the one deleted edge. No search over vertex
    colorings or candidate deleted edges is used.
    """
    cycle = next(
        (vertices for vertices, mask in FIVE_CYCLES if graph & mask == mask),
        None,
    )
    if cycle is None:
        raise AssertionError(f"No C5 in nonbipartite triangle-free graph {graph}")

    outside = next(v for v in VERTICES if v not in cycle)
    positions = [i for i, v in enumerate(cycle) if graph & edge_bit(outside, v)]
    if len(positions) > 2:
        raise AssertionError("The outside vertex has more than two neighbors")

    if len(positions) <= 1:
        removed = edge_bit(cycle[0], cycle[1])
    else:
        i, j = positions
        gap = (j - i) % 5
        if gap == 3:
            removed = edge_bit(cycle[i], cycle[(i + 1) % 5])
        elif gap == 2:
            removed = edge_bit(cycle[j], cycle[(j + 1) % 5])
        else:
            raise AssertionError("The outside vertex has adjacent C5 neighbors")

    coloring = bipartition(graph & ~removed)
    if coloring is None:
        raise AssertionError(f"The selected edge did not make graph {graph} bipartite")
    both_false, both_true = PAIR_COLORS[coloring]
    if graph & (both_false | both_true) != removed:
        raise AssertionError("The deleted edge is not the sole monochromatic edge")
    return coloring, removed


def verify() -> dict[str, object]:
    triangle_free = bipartite = nonbipartite = 0
    edge_colorings = flips = 0

    for graph in range(1 << len(EDGES)):
        if any(graph & triangle == triangle for triangle in TRIANGLES):
            continue
        triangle_free += 1
        base = bipartition(graph)
        special = 0
        if base is None:
            nonbipartite += 1
            base, special = c5_coloring(graph)
        else:
            bipartite += 1

        base_false, base_true = PAIR_COLORS[base]
        if (graph & (base_false | base_true)).bit_count() > 1:
            raise AssertionError("The base coloring has too many monochromatic edges")

        # Every submask of graph specifies which present edges have color true.
        # Values on nonedges and the diagonal do not affect the target statement.
        edge_colors = graph
        while True:
            coloring = base
            special_is_bad = (
                (special & edge_colors & base_true)
                | (special & ~edge_colors & base_false)
            )
            if special_is_bad:
                coloring ^= ALL_VERTICES
                flips += 1

            both_false, both_true = PAIR_COLORS[coloring]
            bad_edges = graph & (
                (edge_colors & both_true) | (~edge_colors & both_false)
            )
            if bad_edges:
                raise AssertionError(
                    f"Failed coloring: graph={graph}, edges={edge_colors}, "
                    f"vertices={coloring}, bad_edges={bad_edges}"
                )
            edge_colorings += 1
            if edge_colors == 0:
                break
            edge_colors = (edge_colors - 1) & graph

    counts = {
        "total_labeled_graphs": 1 << len(EDGES),
        "triangle_free_graphs": triangle_free,
        "bipartite_graphs": bipartite,
        "nonbipartite_triangle_free_graphs": nonbipartite,
    }
    expected = {
        "total_labeled_graphs": 32768,
        "triangle_free_graphs": 5789,
        "bipartite_graphs": 5177,
        "nonbipartite_triangle_free_graphs": 612,
    }
    if counts != expected:
        raise AssertionError(f"Unexpected graph counts: {counts}")

    return {
        "problem": "Erdos151.erdos_151.variants.cliqueFree_four.R1.H2",
        "vertices": N,
        **counts,
        "c5_constructions_checked": nonbipartite,
        "graph_edge_coloring_pairs_checked": edge_colorings,
        "global_color_flips": flips,
        "all_checks_passed": True,
        "method": "C5 structural construction; all edge colorings checked",
        "verification_kind": "Python exhaustive computation, not a Lean certificate",
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
