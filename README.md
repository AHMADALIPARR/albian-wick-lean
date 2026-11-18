# Custom Novel Algorithms in Lean 4

<p align="center">
  <img src="https://img.shields.io/badge/Lean-4.x-blue" alt="Lean 4">
  <img src="https://img.shields.io/badge/sorry-0-brightgreen" alt="Zero sorry">
  <img src="https://img.shields.io/badge/license-AGPL--3.0-red" alt="AGPL-3.0">
</p>

**Zero-`sorry` machine-checked formalizations of original constructions**  
by Ahmad Ali Parr / SnapKitty Research Lab.

These are not textbook algorithms. Each file isolates a specific novel idea and proves its core claims from first principles.

Licensed under the [GNU Affero General Public License v3.0](LICENSE).

Lean sources live in the [`src/`](src/) directory.

---

## Visual Overview

```
 ┌──────────────────────────────────────────────────┐
 │                 CUSTOM NOVEL ALGORITHMS                  │
 ├──────────────────────────────────────────────────┤
 │  Albian Group + Wick Rotation   →   #P  ➡  NP          │
 │  Complexity Middle Ground       →   BQP … NP … PSPACE │
 │  Windowed Addition-Chain Exp    →   a^x mod M          │
 └──────────────────────────────────────────────────┘
```

---

## src/AlbianWick.lean — Albian Group + Wick Rotation

Turns a #P-style relation-counting problem (number-field sieve style) into an NP decision problem via the Albian group \((\mathbb{Z}/2\mathbb{Z})^\pi\) and a Wick rotation.

### ASCII depiction of the construction

```
  Relation Graph Walks
         │
         ▼
  Edge contributions (XOR)          Albian Group (ℤ/2ℤ)^π
         │                              │
         ▼                              ▼
  Accumulated group element ────────────────────────────────────
         │
         ▼
  Truncated generating function Z_A(z)
         │
         ▼   Wick rotation  z ↦ i·z
  Real part nonzero ?  ➡  NP certificate
         │
         ▼
  Even-length zero walk (verifier in poly time)
```

### Wick rotation (inline SVG)

<svg width="320" height="120" xmlns="http://www.w3.org/2000/svg">
  <rect width="100%" height="100%" fill="#0d1117"/>
  <text x="10" y="20" fill="#58a6ff" font-family="monospace" font-size="12">z  ────────────────────────────────────────────</text>
  <text x="10" y="40" fill="#f0f6fc" font-family="monospace" font-size="12">   │</text>
  <text x="10" y="60" fill="#f0f6fc" font-family="monospace" font-size="12">   ▼   z ↦ i·z</text>
  <text x="10" y="80" fill="#3fb950" font-family="monospace" font-size="12">Real part isolates even-length zero walks</text>
  <text x="10" y="100" fill="#d2a8ff" font-family="monospace" font-size="12">→ NP decision problem</text>
</svg>

**Key proved claim**: real part of the Wick-rotated generating function is nonzero ↔ existence of a non-trivial even-length zero-contribution walk (NP witness + poly-time verifier).

---

## src/ComplexityMiddleGround.lean — BQP / NP / PSPACE

Taxonomic formalization of a middle ground between quantum and classical regimes.

### ASCII diagram of the inclusions

```
                    PSPACE
                   /      \
                  /        \
               BQP          NP
                  \        /
                   \      /
                     P
```

```
  Known / consistent:
  BQP ⊆ PSPACE     (standard)
  NP  ⊆ PSPACE     (Source 4)

  Candidate middle ground:
  NP   (BQP ⊆ NP open, consistent with sources)
```

---

## src/WACE.lean — Windowed Addition-Chain Exponentiation

Hand-crafted modular exponentiation \(a^x \bmod M\) using odd-power windows. Polynomial in bitlen(M). No quantum period finding.

### ASCII depiction of the algorithm

```
  Precompute odd powers table
  tbl[i] = a^{2i-1} mod M     T = O(n)

  Scan exponent x in windows of size w = ⌈log₂ n⌉

  ┌───────────────────────────────────────────────────┐
  │  window  →  if 0: shift by 2^w          │
  │           else: multiply tbl[idx]     │
  │                 then shift by 2^w      │
  └───────────────────────────────────────────────────┘
                    │
                    ▼
              r ≡ a^x  (mod M)
```

### Window scanning (inline SVG)

<svg width="360" height="100" xmlns="http://www.w3.org/2000/svg">
  <rect width="100%" height="100%" fill="#0d1117"/>
  <text x="10" y="25" fill="#58a6ff" font-family="monospace" font-size="11">exponent bits:  1 0 1 1 0 1 0 0 ...</text>
  <text x="10" y="50" fill="#f0f6fc" font-family="monospace" font-size="11">windows:      [1 0 1] [1 0 1] [0 0]</text>
  <text x="10" y="75" fill="#3fb950" font-family="monospace" font-size="11">odd table + shift  →  a^x mod M</text>
</svg>

**Proved**: correctness by induction on windows (PO1), intermediate bound (PO2), polynomial time & parameter validity (PO3–PO4).

---

## Building

```bash
lake build
```

Requires Lean 4 (≥ 4.8) + Mathlib.  
Open any file under `src/` in VS Code with the Lean 4 extension.

## Status

All three formalizations type-check with **zero remaining `sorry`s**.

They are precise, machine-checked statements of the original constructions.
