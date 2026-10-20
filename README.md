# Counterexamples to the rainbow-path question in Jensen–Toft §13.7

Alex Chan — Harvard University and National Bureau of Economic Research  
achan@hbs.edu

This repository contains Lean proofs for two orientations on 13 vertices,
with 36 and 37 arcs. Each underlying graph is four-chromatic.
For every proper four-coloring, every directed four-vertex path
repeats a color.

The 36-arc orientation is obtained from the 37-arc orientation by
deleting the arc 3 → 4.

## Verification

Install Lean through elan, then run these commands from this directory:

```sh
lake build
lake env lean Audit.lean
```

The Lean version is pinned in `lean-toolchain`.
The project uses Lean and its standard library, without Mathlib.

## Main results

- `JT137.counterexample36`: the complete 36-arc certificate.
- `JT137.counterexample37`: the complete 37-arc certificate.
- `JT137.forced_partition36`: the forced color-class equalities.
- `JT137.no_rainbow36` and `JT137.no_rainbow37`:
  the assertions for every proper four-coloring.

The no-rainbow results cover all directed walks of three arcs,
so they also cover directed paths on four distinct vertices.

## Files

The Lean proofs are in `JT137/`.
`Audit.lean` prints their axiom dependencies.
The original construction data and SAT certificates for §13.7 are
under `Jensen-Toft-Hail-Mary/results/berge_13_7/`.
Those SAT certificates are not required to build the Lean proofs.

The finite construction is verified here. Publication priority and
the interpretation of the cited literature are separate questions.
