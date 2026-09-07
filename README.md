# Erdős 1212: infinite paths in the composite-restricted visible lattice

This repository provides the Lean 4 formalization accompanying **Infinite paths
in the composite-restricted visible lattice**, by Alex Chengyu Li.

The graph consists of natural-coordinate pairs with both coordinates greater
than one, gcd equal to one, and at least one composite coordinate. Edges are
unit horizontal or vertical steps. The theorem establishes an infinite simple
path and, more strongly, a ray with x/y tending to alpha for Lebesgue-almost
every alpha in (4/3,5/3).

- [Original problem](https://www.erdosproblems.com/1212)
- [Paper PDF](paper/Li_Infinite_Paths_Composite_Restricted_Visible_Lattice_2026.pdf)
- [Paper source](paper/erdos1212_algebraic_corridors.tex)
- [Dated preprint](https://doi.org/10.5281/zenodo.22448686)
- [Versioned formalization and compiled artifacts](https://github.com/crabsatellite/erdos-1212-visible-lattice-path/releases/tag/v1.0.0)

## Statements and proof entry

The literal graph definitions are in [Target.lean](kernel/Erdos1212Kernel/Target.lean).
The main statement is in [AlgebraicCorridorTarget.lean](kernel/Erdos1212Kernel/AlgebraicCorridorTarget.lean).
[AlgebraicCorridorPaperClose.lean](kernel/Erdos1212Kernel/AlgebraicCorridorPaperClose.lean)
proves it from the constructed crossing paths. The final
[AlgebraicCorridorKernelAudit.lean](kernel/Erdos1212Kernel/AlgebraicCorridorKernelAudit.lean)
spells out the real interval, injectivity, safety, unit adjacency and real ratio
limit, consumes that theorem, and prints the dependencies of all three endpoints.

Injectivity makes the path eventually leave every finite lattice region. The
interval has positive measure, so the almost-everywhere theorem supplies a
path and answers the original existence question. The optional monotonicity
and bounded-turn strengthening is not asserted.

The final endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`.
There are no additional mathematical axioms in their printed dependencies.
[Recorded kernel output](certificate/kernel-audit.txt) and the
[artifact manifest](certificate/manifest.json) identify this release's evidence.
This is machine verification, not a claim of journal peer review.

## Reproduce

Install the exact Lean version in `kernel/lean-toolchain` and preserve the
dependency revisions in `kernel/lake-manifest.json`.

```text
cd kernel
lake exe cache get
lake build Erdos1212Kernel
lake env lean --trust=0 Erdos1212Kernel/AlgebraicCorridorKernelAudit.lean
```

The Release also supplies `erdos1212-lean-cache-v1.0.0.zip`, containing only
compiled outputs for this repository's project modules. It excludes Mathlib
and other dependency caches. With the pinned dependencies available, extracting
that ZIP into `kernel/` restores `.lake/build/lib/lean/` and permits the final
audit command without rebuilding the unchanged project modules. Check the
archive hash against the release manifest before extraction.

`python scripts/verify_publication.py` checks file identity and the source
inventory only; it does not run Lean or independently prove the theorem.

Release v1.0.0 is the algebraic-corridor proof. Earlier repository history
predates this proof and contains superseded private staging material; it is
not part of this release's mathematical evidence.

## License

Software is Apache-2.0; the manuscript is CC BY 4.0. See [LICENSE.md](LICENSE.md).
