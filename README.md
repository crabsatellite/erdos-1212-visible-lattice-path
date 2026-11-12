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
- [Versioned formalization and compiled artifacts](https://github.com/crabsatellite/erdos-1212-visible-lattice-path/releases/tag/v1.0.1)

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

## Independent reproduction and community review

[Srijan Roy (BlazeSR10hawk)](https://github.com/BlazeSR10hawk) published a
[successful independent rebuild and trust-zero audit](https://github.com/BlazeSR10hawk/formal-conjectures/actions/runs/38012609676)
on 10 October 2026. The
[pinned workflow](https://github.com/BlazeSR10hawk/formal-conjectures/blob/077e32f04c4c42b24d2099565a9bb971d148bb1c/.github/workflows/verify-erdos1212.yml)
checks out this proof at `400001f0847afe36a26c588d34445210dbdc116e`,
builds `Erdos1212Kernel`, and runs the final audit with `--trust=0`.
The printed endpoint dependencies are the three standard axioms listed above.

[Formal Conjectures PR #6788](https://github.com/google-deepmind/formal-conjectures/pull/6788)
was merged on 22 October 2026. Bo Cowgill checked the bridge from this
repository's stronger ray theorem to the original problem and approved after
the public rebuild evidence was linked. Moritz Firsching approved and merged
the update marking the original problem research-solved and citing this
external formalization.

I thank Srijan Roy for making the rebuild inspectable, Bo Cowgill for the
statement-correspondence review and verification request, and Moritz
Firsching for review and integration. These contributions
have distinct scopes: the public run is the independent rebuild; the PR
records the correspondence review and community status update. Their scope is
the pinned proof and original problem.

## Reproduce

The commands below reproduce the fixed proof snapshot
`400001f0847afe36a26c588d34445210dbdc116e`. In a fresh checkout, select it
before verifying the byte inventory or building. The later external-review
notes in this main-branch README are outside the original release's recorded
README bytes; the release manifest and historical receipts remain unchanged.

Install the exact Lean version in `kernel/lean-toolchain` and preserve the
dependency revisions in `kernel/lake-manifest.json`.

```text
git switch --detach 400001f0847afe36a26c588d34445210dbdc116e
cd kernel
lake exe cache get
lake build Erdos1212Kernel
lake env lean --trust=0 Erdos1212Kernel/AlgebraicCorridorKernelAudit.lean
```

The Release also supplies `erdos1212-lean-cache-v1.0.1.zip`, containing only
compiled outputs for this repository's project modules. It excludes Mathlib
and other dependency caches. With the pinned dependencies available, extracting
that ZIP into `kernel/` restores `.lake/build/lib/lean/` and permits the final
audit command without rebuilding the unchanged project modules. Check the
archive hash against the release manifest before extraction.

`python scripts/verify_publication.py` checks file identity and the source
inventory only; it does not run Lean or independently prove the theorem.

Release v1.0.1 is the algebraic-corridor proof. Earlier repository history
predates this proof and contains superseded private staging material; it is
not part of this release's mathematical evidence.

## License

Software is Apache-2.0; the manuscript is CC BY 4.0. See [LICENSE.md](LICENSE.md).
