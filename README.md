# A Machine-Certified Closure of Erdős Problem 1212

This public repository contains only the certificate kernel and the shortest
self-contained proof chain used to close Erdős Problem 1212.

The theorem is the original visible-lattice path statement: there is an
unbounded unit-step path of coprime pairs above the coordinate axes that never
visits a prime-prime vertex. The proof keeps that cut unchanged.

## Public surface

- `paper/erdos1212_minimal_closure.tex`: minimal closed-loop proof.
- `paper/Li_Erdos_1212_Minimal_Closure_2026.pdf`: rendered proof.
- `paper/theorem-map.json`: theorem-to-certificate map.
- `kernel/`: the exact C++/CUDA/Python certificate kernel.
- `certificate/manifest.json`: SHA-256 and byte-length contract for every
  accepted source, small in-repository certificate, and dense replay payload.
- `certificate/admission.txt`: frozen full-state acceptance transcript.
- `certificate/hashimoto.txt`: frozen translation-kernel transcript.
- `scripts/verify_publication.py`: fail-closed public-surface checker.
- `scripts/verify_full_certificate.ps1`: optional full dense-payload replay.

Research logs, route selection, failed arguments, generated status reports,
and exploratory binaries are intentionally absent.

## Closed inequality

The twelve-prime directed interval certificate proves

```text
R_<61 u <= U <= 0.91717912709094451 u < 0.933 u.
```

The disjoint large-repeat tail satisfies `||R_>=61|| < 0.067`. Hence the
complete first-repeat renewal norm is strictly below one. The all-fresh series
is summable, so separating contour mass cannot escape to infinity; the
original unbounded path follows.

The full-state comparison covers 55,076,704 allocated coordinates and reports
zero threshold, positive-over-zero, negative-upper, and nonfinite failures.

## Verification

Metadata, source hashes, exact root enclosures, transcript, and public-surface
checks:

```powershell
python scripts/verify_publication.py
```

Rebuild the manuscript:

```powershell
.\scripts\build_paper.ps1 -Strict
```

The final dense images are about 2.7 GB and are therefore not committed to Git.
They are hash-pinned in `certificate/manifest.json`. With those files in one
payload directory and CUDA 13 or later installed, replay the final directed
comparison with:

```powershell
.\scripts\verify_full_certificate.ps1 -Payload D:\path\to\payload
```

The root tables needed for the exact-rational trigonometric check are small and
are committed under `certificate/roots/`.

## Trust boundary

The machine part is a finite certificate check, not a claim that the CUDA
compiler is a theorem prover. The public trust boundary is explicit:

1. exact-rational verification of every stored binary32 root component;
2. directed-rounding CUDA construction of positive upper images;
3. a proved `500*2^-24` enclosure of the binary64 Fourier centres;
4. a statewise directed comparison against the downward neighbour of `0.933`;
5. SHA-256 binding of all accepted sources and payloads.

## Licensing

See `LICENSE.md`. Kernel source and verification scripts are Apache-2.0. The
manuscript source and PDF are CC BY 4.0.
