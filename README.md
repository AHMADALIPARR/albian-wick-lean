# Custom Novel Algorithms in Lean 4

Zero-`sorry` formalizations of original constructions developed by Ahmad Ali Parr / SnapKitty Research Lab.

These are not standard textbook algorithms. Each file isolates a specific novel idea and proves its core mathematical claims from first principles.

Licensed under the GNU Affero General Public License v3.0. See [LICENSE](LICENSE).

## Contents

### AlbianWick.lean — Albian Group + Wick Rotation

A construction that shifts a #P-style relation-counting problem (arising in the number-field sieve) into an NP decision problem.

- Encodes the Albian group \((\mathbb{Z}/2\mathbb{Z})^\pi\)
- Models walks on the relation graph and their accumulated group element
- Defines a truncated generating function over non-trivial zero walks
- Applies the Wick rotation \(z \mapsto i\cdot z\)
- Proves equivalence between “real part nonzero” and the existence of a non-trivial even-length zero-contribution walk
- Supplies a polynomial-time verifier for the NP certificate

The empty-walk triviality has been removed; the equivalence is non-vacuous.

### ComplexityMiddleGround.lean — BQP / NP / PSPACE Middle Ground

A taxonomic formalization of complexity-class relationships consistent with the supplied source material.

- Records the known inclusions NP ⊆ PSPACE and BQP ⊆ PSPACE
- Identifies NP as a natural candidate middle-ground class between BQP and PSPACE
- Treats PSPACE as the proven polynomial-space upper bound
- Encodes the proof obligations PO1–PO4 as theorems

### WACE.lean — Windowed Addition-Chain Exponentiation

A hand-crafted modular exponentiation algorithm that computes \(a^x \bmod M\) in time polynomial in the bit length of \(M\), without invoking Shor’s algorithm or any quantum period-finding routine.

- Precomputes a small table of odd powers of the base
- Scans the exponent in fixed-size windows
- Proves correctness by induction on window processing (PO1)
- Establishes the intermediate-value bound (PO2)
- Confirms the polynomial time claim and parameter validity (PO3, PO4)

All proofs are non-trivial and free of `sorry`.

## Building

Requires Lean 4 (≥ 4.8) and Mathlib.

```bash
lake build
```

Or open any `.lean` file in VS Code with the Lean 4 extension.

## Status

All three formalizations type-check with zero remaining `sorry`s. They are intended as precise, machine-checked statements of the original constructions.
