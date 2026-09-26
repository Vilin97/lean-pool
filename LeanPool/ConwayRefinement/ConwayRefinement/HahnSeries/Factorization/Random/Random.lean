/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Germ
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Random series

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Definition 1.3: a series `b = ∑ b_γ t^γ ∈ K((ℝ^{≤0}))` is *random* if the set
`cl(supp b) ∖ {0}` is `ℚ`-linearly independent in `ℝ`, or the family of coefficients
`⟨b_γ : γ ∈ supp b⟩` is algebraically independent over `ℚ`. Section 3 extends this to finitely
many series: `b_1, …, b_m` are *mutually random* if the closures of their supports meet pairwise
only in `{0}` and the union of the sets `cl(supp b_i) ∖ {0}` is `ℚ`-linearly independent, or
the joint family of all their coefficients is algebraically independent over `ℚ`.

The coefficient field has characteristic zero, so it is a `ℚ`-algebra through Mathlib's
`DivisionRing.toRatAlgebra`; algebraic independence is Mathlib's `AlgebraicIndependent ℚ`.
The two clauses are recorded as separate predicates, `IsSupportRandom` and
`IsCoefficientRandom`, and `IsRandom` is their disjunction, so that the theorems proved from
each clause can be stated for that clause alone.
-/

open scoped HahnSeries

universe v

public noncomputable section

namespace FLLM24

open Berarducci

variable {K : Type v} [Field K]

/-- The set `cl(supp b) ∖ {0}` of FLLM24, Definition 1.3. -/
def supportClosure (b : Series K) : Set ℝ :=
  closure (b : K⟦ℝ⟧).support \ {0}

theorem mem_supportClosure_iff (b : Series K) (x : ℝ) :
    x ∈ supportClosure b ↔ x ∈ closure (b : K⟦ℝ⟧).support ∧ x ≠ 0 :=
  (Iff.rfl)

/-- The first clause of FLLM24, Definition 1.3: the closure of the support of `b`, with zero
removed, is a `ℚ`-linearly independent subset of `ℝ`. -/
def IsSupportRandom (b : Series K) : Prop :=
  LinearIndependent ℚ (fun x : supportClosure b ↦ (x : ℝ))

theorem IsSupportRandom.linearIndependent {b : Series K} (h : IsSupportRandom b) :
    LinearIndependent ℚ (fun x : supportClosure b ↦ (x : ℝ)) :=
  h

theorem IsSupportRandom.of {b : Series K}
    (h : LinearIndependent ℚ (fun x : supportClosure b ↦ (x : ℝ))) : IsSupportRandom b :=
  h

variable [CharZero K] in
/-- The second clause of FLLM24, Definition 1.3: the coefficients `⟨b_γ : γ ∈ supp b⟩` are
algebraically independent over `ℚ`. -/
def IsCoefficientRandom (b : Series K) : Prop :=
  AlgebraicIndependent ℚ (fun γ : (b : K⟦ℝ⟧).support ↦ (b : K⟦ℝ⟧).coeff γ)

variable [CharZero K] in
theorem IsCoefficientRandom.algebraicIndependent {b : Series K} (h : IsCoefficientRandom b) :
    AlgebraicIndependent ℚ (fun γ : (b : K⟦ℝ⟧).support ↦ (b : K⟦ℝ⟧).coeff γ) :=
  h

variable [CharZero K] in
theorem IsCoefficientRandom.of {b : Series K}
    (h : AlgebraicIndependent ℚ (fun γ : (b : K⟦ℝ⟧).support ↦ (b : K⟦ℝ⟧).coeff γ)) :
    IsCoefficientRandom b :=
  h

variable [CharZero K] in
/-- FLLM24, Definition 1.3: a series is random if its support closure (without zero) is
`ℚ`-linearly independent or its coefficients are algebraically independent over `ℚ`. -/
def IsRandom (b : Series K) : Prop :=
  IsSupportRandom b ∨ IsCoefficientRandom b

variable [CharZero K] in
theorem isRandom_iff (b : Series K) :
    IsRandom b ↔ IsSupportRandom b ∨ IsCoefficientRandom b :=
  (Iff.rfl)

/-- The set `⋃ᵢ cl(supp bᵢ) ∖ {0}` of a family of series. -/
def supportClosureUnion {ι : Type*} (b : ι → Series K) : Set ℝ :=
  (⋃ i, closure ((b i : K⟦ℝ⟧)).support) \ {0}

theorem mem_supportClosureUnion_iff {ι : Type*} (b : ι → Series K) (x : ℝ) :
    x ∈ supportClosureUnion b ↔ (∃ i, x ∈ closure ((b i : K⟦ℝ⟧)).support) ∧ x ≠ 0 := by
  simp [supportClosureUnion]

/-- The support clause of mutual randomness, FLLM24, § 3: the closures of the supports meet
pairwise only in `{0}`, and their union with zero removed is `ℚ`-linearly independent. -/
structure IsMutuallySupportRandom {ι : Type*} (b : ι → Series K) : Prop where
  /-- `cl(supp bᵢ) ∩ cl(supp bⱼ) ⊆ {0}` for `i ≠ j`. -/
  closure_inter_subset : ∀ i j, i ≠ j →
    closure ((b i : K⟦ℝ⟧)).support ∩ closure ((b j : K⟦ℝ⟧)).support ⊆ {0}
  /-- `⋃ᵢ cl(supp bᵢ) ∖ {0}` is `ℚ`-linearly independent. -/
  linearIndependent : LinearIndependent ℚ (fun x : supportClosureUnion b ↦ (x : ℝ))

/-- The index set of the joint coefficient family of a family of series: the pairs `(i, γ)` with
`γ ∈ supp bᵢ`. -/
def coefficientIndex {ι : Type*} (b : ι → Series K) : Set (ι × ℝ) :=
  {p | p.2 ∈ ((b p.1 : K⟦ℝ⟧)).support}

theorem mem_coefficientIndex_iff {ι : Type*} (b : ι → Series K) (p : ι × ℝ) :
    p ∈ coefficientIndex b ↔ ((b p.1 : K⟦ℝ⟧)).coeff p.2 ≠ 0 :=
  (Iff.rfl)

variable [CharZero K] in
/-- The coefficient clause of mutual randomness, FLLM24, § 3: the joint family
`⟨b_{iγ} : i, γ ∈ supp bᵢ⟩` is algebraically independent over `ℚ`. -/
def IsMutuallyCoefficientRandom {ι : Type*} (b : ι → Series K) : Prop :=
  AlgebraicIndependent ℚ (fun p : coefficientIndex b ↦ ((b p.1.1 : K⟦ℝ⟧)).coeff p.1.2)

variable [CharZero K] in
theorem IsMutuallyCoefficientRandom.algebraicIndependent {ι : Type*} {b : ι → Series K}
    (h : IsMutuallyCoefficientRandom b) :
    AlgebraicIndependent ℚ (fun p : coefficientIndex b ↦ ((b p.1.1 : K⟦ℝ⟧)).coeff p.1.2) :=
  h

variable [CharZero K] in
theorem IsMutuallyCoefficientRandom.of {ι : Type*} {b : ι → Series K}
    (h : AlgebraicIndependent ℚ (fun p : coefficientIndex b ↦ ((b p.1.1 : K⟦ℝ⟧)).coeff p.1.2)) :
    IsMutuallyCoefficientRandom b :=
  h

variable [CharZero K] in
/-- FLLM24, § 3: `b₁, …, bₘ` are mutually random if they satisfy the support clause or the
coefficient clause. -/
def IsMutuallyRandom {ι : Type*} (b : ι → Series K) : Prop :=
  IsMutuallySupportRandom b ∨ IsMutuallyCoefficientRandom b

variable [CharZero K] in
theorem isMutuallyRandom_iff {ι : Type*} (b : ι → Series K) :
    IsMutuallyRandom b ↔ IsMutuallySupportRandom b ∨ IsMutuallyCoefficientRandom b :=
  (Iff.rfl)

end FLLM24

end
