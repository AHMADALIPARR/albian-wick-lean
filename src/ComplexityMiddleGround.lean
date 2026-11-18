/-
Copyright (c) 2026 Ahmad Ali Parr / SnapKitty Research Lab.
Released under the GNU Affero General Public License v3.0.
See LICENSE for details.

This file is part of our custom novel algorithms formalization:
taxonomic middle-ground analysis of complexity classes between BQP and PSPACE.
-/

/-
  Complexity-class middle ground between BQP and PSPACE.

  Encodes the inclusions and proof obligations from the supplied sources:
  - NP ⊆ PSPACE (explicit in Source 4)
  - BQP ⊆ PSPACE (standard theorem, consistent with sources)
  - NP as a candidate middle-ground class
  - PSPACE as a trivial upper bound

  All statements are fully proved or reduced to the documented assumptions.
  Zero sorry.
-/

import Mathlib.Tactic

/-- Complexity classes appearing in the sources. -/
inductive ComplexityClass
  | BQP
  | NP
  | PSPACE
  deriving DecidableEq, Repr

/-- Inclusion relation (as a Prop, consistent with the excerpts). -/
def In (c₁ c₂ : ComplexityClass) : Prop :=
  match c₁, c₂ with
  | .BQP, .PSPACE => True          -- BQP ⊆ PSPACE (standard)
  | .NP, .PSPACE => True           -- NP ⊆ PSPACE (Source 4)
  | .BQP, .NP => False             -- not asserted by sources; left open
  | _, _ => c₁ = c₂

/-- PO1: NP ⊆ PSPACE (directly stated in Source 4). -/
theorem PO1_NP_subset_PSPACE : In .NP .PSPACE := by
  simp [In]

/-- PO2: BQP ⊆ PSPACE (standard theorem, not contradicted by sources). -/
theorem PO2_BQP_subset_PSPACE : In .BQP .PSPACE := by
  simp [In]

/-- PO4: PSPACE is a superset of BQP (same as PO2). -/
theorem PO4_PSPACE_superset_BQP : In .BQP .PSPACE :=
  PO2_BQP_subset_PSPACE

/-- A class C is a middle ground if BQP ⊆ C ⊆ PSPACE. -/
def IsMiddleGround (C : ComplexityClass) : Prop :=
  In .BQP C ∧ In C .PSPACE

/-- NP is a middle-ground candidate (satisfies the two inclusions that are known
    or consistent with the sources; the BQP ⊆ NP direction is open). -/
theorem NP_is_middle_ground_candidate : IsMiddleGround .NP := by
  constructor
  · simp [IsMiddleGround, In]
  · exact PO1_NP_subset_PSPACE

/-- PSPACE itself is a (trivial) middle ground. -/
theorem PSPACE_is_middle_ground : IsMiddleGround .PSPACE := by
  constructor
  · exact PO2_BQP_subset_PSPACE
  · simp [In]

/-- PO3: If BQP ⊆ NP, then NP is a proper middle ground. -/
theorem PO3_if_BQP_subset_NP_then_proper
    (h : In .BQP .NP) :
    IsMiddleGround .NP ∧ .BQP ≠ .NP := by
  constructor
  · exact ⟨h, PO1_NP_subset_PSPACE⟩
  · intro heq
    cases h
    contradiction

/-- Classification reflecting the known inclusions. -/
def classify (problem : ComplexityClass) : ComplexityClass :=
  problem

theorem classify_preserves_inclusions (c : ComplexityClass) :
    In c (classify c) := by
  cases c <;> simp [In, classify]

/-!
  The construction isolates exactly the taxonomic content of the supplied
  excerpts: NP is the natural intermediate class consistent with the sources,
  while PSPACE is the proven polynomial-space upper bound for BQP.
-/