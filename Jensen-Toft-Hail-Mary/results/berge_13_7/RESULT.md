# A verified counterexample to Jensen–Toft Problem 13.7

The 13-vertex graph in `graph.json`, with 37 edges and graph6 string
``L?|Cbei`aqk}~O`` (the backtick is a literal graph6 character), has chromatic
number 4. The stored orientation has no directed four-vertex path that is
rainbow under any proper four-coloring. This gives a negative answer to the
exact mathematical question in Jensen–Toft Problem 13.7.

Publication priority and the conjecture's status in 2026 remain separate
questions under an ongoing primary-source audit. A computationally verified
counterexample does not itself establish that no earlier counterexample exists.

## Exact problem and source

Jensen and Toft ask whether every orientation of every four-chromatic graph
admits a directed path together with a proper four-coloring in which the path
meets each color class exactly once. The path therefore has four vertices.
The coloring may be chosen after the orientation; merely defeating one fixed
coloring would not answer the problem.

Source: T.R. Jensen and B. Toft, *Graph Coloring Problems*, Wiley, 1995,
Problem 13.7, pp. 214–215. Publisher chapter record:
https://doi.org/10.1002/9781118032497.ch13 .
Authenticated book text: https://djvu.online/file/sNID8jjCqAw5z .

The book attributes the general problem to C. Berge (1980) and records Meyniel's
1989 negative answer for chromatic number at least 5, leaving 4 unresolved at
the book's publication. Meyniel's primary paper is *About colorings, stability
and paths in directed graphs*, Discrete Mathematics 74 (1989), 149–150,
https://doi.org/10.1016/0012-365X(89)90206-9 .

## Mathematical certificate

One proper coloring has color classes:

| Color | Vertices |
|---|---|
|0|0,1,2,3|
|1|4,5,6|
|2|7,8,9|
|3|10,11,12|

All proper four-colorings induce this same partition, up to renaming colors.
The orientation is acyclic and has 26 directed four-vertex paths; every one
repeats a color in this unique partition. The maximum clique has order 3,
so the graph contains no K4.

Three independent verification mechanisms secure the finite result:

1. Root's independent backtracking enumeration, with no SAT or discovery-code
   imports, finds no proper three-coloring and one proper four-coloring up to
   color permutation. It independently enumerates all directed four-vertex
   paths and finds no rainbow one.
2. A separate standalone verifier independently decodes graph6, checks that
   every undirected edge receives exactly one direction, enumerates canonical
   colorings, and directly enumerates all ordered four-vertex paths.
3. Fresh canonical coloring CNFs and RUP proofs certify non-three-colorability,
   uniqueness after fixing a triangle, and the impossibility of rainbow
   four-coloring for each of the 26 directed paths. All 28 proofs replay with
   75 RUP additions. Empty traces arising from bootstrap unit conflicts were
   completed with an explicit empty clause, accepted only after independent
   RUP verification. A truncated-proof negative control is rejected.

Run `python3 verify_berge137.py`. Requirements: Python standard library and
`g++`; no SAT solver, NetworkX, or discovery scripts are needed for replay.

The record includes edges, the full orientation, a proper four-coloring,
all directed four-vertex paths, their color patterns, adjacency lists,
adjacency matrix, graph6, every CNF/proof, and hashes in the proof catalogue.

## The general parameter boundary

For every integer t ≥ 0, take the complete join of this graph with K_t.
Orient the clique transitively and all joining edges from the clique into
the base graph. The result has chromatic number 4+t, and its optimal coloring
is unique up to permutation. A rainbow directed path meeting all 4+t color
classes would have to visit every clique color and four different base colors.
It enters the base at most once and cannot return to the clique. Its four base
vertices would consequently form a rainbow directed four-vertex path in the
stored base orientation, which is impossible.

Thus this seed extends the negative answer to every chromatic number k ≥ 4.
This does not settle the separately suggested restriction to critical hosts.

## Discovery

The first 600 fixed critical-support/control graphs and 878 eligible planted
four-colorable K4-free random graphs all rejected the orientation attack.
The decisive representation change synthesized graph edges and their
orientations jointly. A proper four-coloring was planted. Each discovered
three-coloring generated an edge cut invalidating it. Each discovered rainbow
path together with a compatible proper four-coloring generated a cut requiring
that a future graph invalidate that coloring or break that directed path.

The partition 4+3+3+3 produced this witness after 17.68 seconds and 50322 cuts:
5,118 three-coloring cuts and 45,204 path/coloring cuts. A separate fixed-graph
orientation search found another failing orientation of the same host. The
secured result uses the original inverse-search orientation, and search halted
for independent audits immediately after discovery.

## A four-case proof of unique four-colorability

Fix the triangle (2,4,8) to colors (0,1,2), which is valid up to renaming colors. Vertex 11 is adjacent to vertices 2 and 8, so it has only colors 1 and 3 available. Vertex 7 is adjacent to vertices 2 and 11. There are consequently just four cases:

| Colors (11,7) | Consequence of neighbor-color forcing | Result |
|---|---|---|
|(1,2)|Vertices 6 and 9 are both forced to color 3.|Contradicts edge 6–9.|
|(1,3)|Vertices 3 and 6 are both forced to color 0.|Contradicts edge 3–6.|
|(3,1)|Vertices 9 and 10 are both forced to color 2.|Contradicts edge 9–10.|
|(3,2)|Every remaining vertex is forced to the displayed coloring.|The only valid coloring.|

The complete ordered forcing chains are in `uniqueness_forcing_tree.json`. The standalone verifier checks that every forced assignment has its other three colors excluded by already assigned neighbors, every branch exhausts all available colors, and every contradiction uses a genuine edge. This proof also rules out three-colorability.

## A nine-case proof that the orientation has no rainbow path

Any directed four-vertex path has a middle arc. The following table exhausts all middle arcs that have both a predecessor and a successor. Each possible color pattern repeats a color.

| Middle arc | Possible color patterns | Number of paths |
|---|---|---:|
|4 → 1|0103|2|
|4 → 8|0120, 0121|4|
|4 → 12|0130|4|
|5 → 1|3103|1|
|5 → 9|3121, 3123|2|
|5 → 12|3130|2|
|7 → 1|0203, 3203|2|
|7 → 12|0230, 3230|4|
|12 → 1|0303, 1303, 2303|5|

The table is stored in `midpoint_certificate.json` and independently regenerated from the full orientation by the standalone verifier.
