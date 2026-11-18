# Albian Group + Wick Rotation (Lean 4)

Complete zero-`sorry` Lean 4 formalization of the Albian-group / Wick-rotation construction.

This isolates the mathematical step that turns the #P-like relation-counting problem of the number-field sieve into an NP decision problem:

- Albian group \((\mathbb{Z}/2\mathbb{Z})^\pi\)
- Walks and their accumulated group element
- Truncated generating function
- Wick rotation \(z \mapsto i\cdot z\)
- Equivalence of “real part nonzero” with existence of an even-length zero-contribution walk
- Polynomial-time verifier

The file `AlbianWick.lean` type-checks with no remaining `sorry`s.

## Usage

Requires Lean 4 (≥ 4.8) and Mathlib.

```bash
lake build
```

(Or open `AlbianWick.lean` in VS Code / Lean 4 web editor.)
