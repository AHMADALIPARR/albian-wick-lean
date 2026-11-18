# Albian Group + Wick Rotation, Complexity Middle Ground, and WACE (Lean 4)

Zero-`sorry` Lean 4 formalizations of related constructions.

## AlbianWick.lean

Formalization of the Albian-group / Wick-rotation construction that turns the #P-like relation-counting problem of the number-field sieve into an NP decision problem:

- Albian group \((\mathbb{Z}/2\mathbb{Z})^\pi\)
- Walks and their accumulated group element
- Truncated generating function (non-trivial zero walks only)
- Wick rotation \(z \mapsto i\cdot z\)
- Equivalence of “real part nonzero” with existence of a non-trivial even-length zero-contribution walk
- Polynomial-time verifier

The empty-walk triviality has been eliminated; the equivalence is non-vacuous.

## ComplexityMiddleGround.lean

Formalization of the complexity-class middle ground between BQP and PSPACE, based on the supplied sources:

- NP ⊆ PSPACE (Source 4)
- BQP ⊆ PSPACE (standard theorem)
- NP as a candidate middle-ground class
- PSPACE as the proven polynomial-space upper bound
- Proof obligations PO1–PO4 encoded as theorems

## WACE.lean

Verified Windowed Addition-Chain Exponentiation for modular exponentiation \(a^x \bmod M\):

- Odd-powers lookup table of size \(O(n)\)
- Window scanning of the exponent
- Non-trivial inductive proof of correctness (PO1)
- Intermediate-value bound (PO2)
- Polynomial time claim (PO3) and parameter validity (PO4)

All files type-check with no remaining `sorry`s.

## Usage

Requires Lean 4 (≥ 4.8) and Mathlib.

```bash
lake build
```

(Or open the `.lean` files in VS Code / Lean 4 web editor.)
