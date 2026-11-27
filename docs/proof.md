# A six-vertex edge-coloring extension lemma

## Statement and scope

Let **G** be a finite simple undirected graph with at most six vertices and no
triangle. Give each edge an arbitrary color in `{false, true}`. There is a
coloring **d** of the vertices with the same two colors such that no edge has
both endpoints colored with that edge's color:

$$
\forall\{x,y\}\in E(G),\qquad
\neg\bigl(d(x)=c(\{x,y\})\;\land\;d(y)=c(\{x,y\})\bigr).
$$

In the upstream Lean statement, `c x y = c y x` expresses that the edge color
does not depend on the order of its endpoints. Colors assigned to nonedges or
to a repeated vertex are irrelevant.

This is **H2 of one reduction of the K4-free variant of Erdős problem 151**.
It is not a solution of that variant or of the full Erdős problem. The lemma
allows an existing edge coloring to be extended to the edges incident with a
new vertex without creating a monochromatic triangle through that vertex:
color the new edge to `x` with `d(x)`.

## A structural fact

**Claim.** Every triangle-free graph on at most six vertices becomes bipartite
after deleting at most one edge.

If the graph is already bipartite, nothing needs to be deleted. Suppose it is
not. A finite graph is bipartite exactly when it has no odd cycle, so it has an
odd cycle. A simple odd cycle in this graph cannot have length three, because
the graph is triangle-free, or length seven or more, because there are at most
six vertices. It therefore has length five. Denote this cycle by **C**.

There is no chord of C: any chord of a five-cycle closes a triangle along the
shorter two-edge path between its endpoints. Outside C there is at most one
vertex **v**. If it exists, its neighbors on C form an independent set, since
two adjacent neighbors would form a triangle with v. An independent set in a
five-cycle has size at most two, so v has at most two neighbors on C.

There are now two possibilities:

1. **There is no outside vertex, or it has at most one neighbor on C.** Delete
   any edge of C. What remains is a path, possibly with an isolated vertex or
   one additional leaf, and hence a forest. It is bipartite.
2. **The outside vertex has two neighbors a and b.** They are nonadjacent on C.
   The two paths between them along C have lengths two and three; the path
   `a–v–b` also has length two. Delete an edge on the length-three path. The
   remaining graph consists of the four-cycle formed by the two length-two
   paths, with pieces of the broken third path attached. Its only cycle is
   even, so it is bipartite.

These exhaust all possibilities: the five-cycle has no chords, and there are
no further vertices. This proves the claim.

## Constructing the required vertex colors

If G is bipartite, take any proper vertex two-coloring. Every edge has
differently colored endpoints, so the required condition holds for every edge
coloring c.

Otherwise, choose the edge **e = {u, v}** from the structural claim, and take a
proper vertex two-coloring of **G − e**. All edges other than e have differently
colored endpoints. The endpoints of e have the same color: e lay on the
five-cycle, and the other four edges of that cycle still form an even-length
path between u and v.

If their common color differs from c(e), retain the coloring. If it equals
c(e), interchange `false` and `true` at **every vertex**. This changes the common
color of the endpoints of e to the other color; all other edges still have
differently colored endpoints. Thus no edge has both endpoints in its own
edge color. This proves the lemma.

The argument also proves a useful general statement: **any graph that becomes
bipartite after deleting at most one edge satisfies the same edge-coloring
extension property**. The six-vertex and triangle-free hypotheses are used
only to establish the structural claim above.

## Independent exhaustive computation

The script [`check_exhaustive.py`](../scripts/check_exhaustive.py) is an
independently written, dependency-free implementation of this construction.
With Python 3.10 or newer, run:

```bash
python scripts/check_exhaustive.py
```

It enumerates all labeled simple graphs on the vertex set `{0, 1, 2, 3, 4, 5}`.
There are 15 possible edges, hence `2^15 = 32,768` graphs. It checks triangles
directly, and uses graph traversal to test bipartiteness. For each nonbipartite
triangle-free graph, it finds a five-cycle and selects a removable edge by the
two cases of the structural proof. It then tests the resulting construction
against **every coloring of the present edges**.

| Quantity | Count |
| --- | ---: |
| All labeled six-vertex simple graphs | 32,768 |
| Triangle-free graphs | 5,789 |
| Bipartite graphs | 5,177 |
| Nonbipartite triangle-free graphs | 612 |
| Graph/edge-coloring pairs verified | 294,987 |
| Cases requiring a global vertex-color flip | 24,192 |

Graphs with fewer than six vertices are covered by adding isolated vertices
and restricting the resulting coloring to the original vertices. The program
prints deterministic JSON, including the number of graph/edge-coloring pairs
checked, and exits with an error if any graph or coloring violates the claim.

This Python computation is an additional reproducibility check. It is not a
Lean kernel certificate; the mathematical proof above does not rely on its
output.

## Prior work and attribution

The exact target comes from the reduction submitted by **dk8827** in
[upstream PR #4050](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4050).

Before this repository was published, **Salofe** had already submitted and
obtained acceptance for a Lean proof of this H2 in
[upstream PR #5331](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5331).
The checker accepted it on **27 November 2026 at 19:22:28 China Standard Time
(11:22:28 UTC)**, and it was merged three seconds later. The
[checker comment](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5331#issuecomment-7216998704)
records that acceptance.

**We do not claim to be the first to prove or formalize this lemma.** This
repository provides an independent reproduction, explanation, and verification
of the same small result. The prose proof and Python program here were written
independently; they are not copied from the upstream Lean implementation.
Upstream acceptance of H2 also does not establish the parent Erdős conjecture.

### Sources

- [H2 problem page](https://lefttosolve.com/p/Erdos151.erdos_151.variants.cliqueFree_four.R1.H2)
- [The original reduction, including the H2 definition](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/main/reductions/Erdos151.erdos_151.variants.cliqueFree_four.R1.lean)
- [Previously accepted H2 proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/main/proofs/Erdos151.erdos_151.variants.cliqueFree_four.R1.H2.lean)
