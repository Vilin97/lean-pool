/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.HereditaryIndependence
public import Mathlib.LinearAlgebra.Quotient.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeSum
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# The space of reducible classes and the property `(*)_α`

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Definition 4.1, let `R_α` be the set of products `bc` of two principal series not in `K` with
`deg_J(bc) = α`, and `A_α := J_α + Span_K(R_α)`. Property `(*)_α` says: whenever `b_1, …, b_n`
in `P_α` are hereditarily `rv_J`-independent, they are `K`-linearly independent over `A_α`.

This module states `(*)_α` in `P̂`. The class map `rv_J` sends
`J_{ω^(α+1)}` onto the homogeneous component `P_α` with kernel `J_α = J_{ω^α}`, and it sends
`R_α` onto the
products of two homogeneous classes of positive grades `β, γ` with `β + γ = α`. Hence, for series
in `J_{ω^(α+1)}`, membership in `A_α` is the same as membership of the grade-`α` class in

`D_α := Span_K { X · Y : X ∈ P_β, Y ∈ P_γ, β, γ > 0, β + γ = α }`,

and `K`-linear independence over `A_α` is linear independence of the classes modulo `D_α`. Two
repairs of the printed statement are built in. First, `(*)_α` quantifies over all series of
ordinal-value degree `α`, not only the principal ones: the inductive step of the source applies
`(*)_α` to translated truncations, which need not be principal. Second, the classes are compared
modulo `D_α` rather than the series modulo `A_α`; this is the same condition for series of degree
`α`, and it is the form in which the induction is carried out.

The total map `gradeClass α` sends a series of `J_{ω^(α+1)}` to its class in grade `α` and every
other series to zero; it is the map `rv_J^α : J_{α+1} → RV_J^α` of the source extended by zero.
-/

open scoped DirectSum HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci

variable {K : Type v} [Field K]

/-! ### The class of a series in a fixed grade -/

/-- The class of `c` in grade `α` of `P̂`: the image of `c ∈ J_{ω^(α+1)}` in
`P_α = J_{ω^(α+1)} / J_{ω^α}`, and zero when `c ∉ J_{ω^(α+1)}`. -/
def gradeClass (α : NatOrdinal) (c : Series K) : PrincipalSubring K :=
  if h : ordinalValue c < ω^ (α + 1) then
    DirectSum.of (PrincipalComponent K) α (principalComponentMk α c h)
  else
    0

theorem gradeClass_of_lt {α : NatOrdinal} {c : Series K} (h : ordinalValue c < ω^ (α + 1)) :
    gradeClass α c = DirectSum.of (PrincipalComponent K) α (principalComponentMk α c h) := by
  rw [gradeClass, dite_eq_left h]

theorem gradeClass_eq_homogeneousMk {α : NatOrdinal} {c : Series K}
    (h : ordinalValue c < ω^ (α + 1)) :
    gradeClass α c = (ordinalValueDegreeValuation K).homogeneousMk α
      ⟨c, (mem_ordinalValueDegreeValuation_filtrationLE_iff c α).mpr h⟩ := by
  rw [gradeClass_of_lt h, principalComponentMk_eq_componentMk, MaxAddDegree.homogeneousMk_apply]

/-- A series of ordinal value below `ω^α` has zero class in grade `α`. -/
theorem gradeClass_eq_zero_of_lt {α : NatOrdinal} {c : Series K} (h : ordinalValue c < ω^ α) :
    gradeClass α c = 0 := by
  have h' : ordinalValue c < ω^ (α + 1) :=
    h.trans (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one α))
  rw [gradeClass_of_lt h', (principalComponentMk_eq_zero_iff α c h').mpr h, map_zero]

/-- For `c ∈ J_{ω^(α+1)}`, the class of `c` in grade `α` vanishes exactly when `c ∈ J_{ω^α}`. -/
theorem gradeClass_eq_zero_iff {α : NatOrdinal} {c : Series K} (h : ordinalValue c < ω^ (α + 1)) :
    gradeClass α c = 0 ↔ ordinalValue c < ω^ α := by
  rw [gradeClass_of_lt h]
  constructor
  · intro hzero
    exact (principalComponentMk_eq_zero_iff α c h).mp
      (DirectSum.of_injective α (by simpa using hzero))
  · intro hlt
    rw [(principalComponentMk_eq_zero_iff α c h).mpr hlt, map_zero]

/-- At ordinal value exactly `ω^α`, the grade-`α` class is `rv_J`. -/
theorem rvJ_eq_gradeClass {α : NatOrdinal} {c : Series K} (h : ordinalValue c = ω^ α) :
    rvJ c = gradeClass α c := by
  rw [rvJ_eq_homogeneousMk h,
    gradeClass_eq_homogeneousMk (h ▸ NatOrdinal.wpow_lt_wpow.mpr (lt_add_one α))]

/-- At ordinal value exactly `ω^α`, the class `rv_J(c)` is nonzero. -/
theorem rvJ_ne_zero_of_eq {α : NatOrdinal} {c : Series K} (h : ordinalValue c = ω^ α) :
    rvJ c ≠ 0 := by
  rw [rvJ_eq_gradeClass h, Ne, gradeClass_eq_zero_iff (h ▸ NatOrdinal.wpow_lt_wpow.mpr
    (lt_add_one α)), h]
  exact lt_irrefl _

/-- For `c ∈ J_{ω^(α+1)}` the grade-`α` class is nonzero exactly when `v_J(c) = ω^α`. -/
theorem ordinalValue_eq_of_gradeClass_ne_zero {α : NatOrdinal} {c : Series K}
    (h : ordinalValue c < ω^ (α + 1)) (hne : gradeClass α c ≠ 0) :
    ordinalValue c = ω^ α := by
  have hnot : ¬ ordinalValue c < ω^ α := fun hlt ↦ hne (gradeClass_eq_zero_of_lt hlt)
  rcases ordinalValue_eq_zero_or_isAdditivelyPrincipal c with hzero | hprin
  · exact absurd (hzero ▸ NatOrdinal.wpow_pos α) hnot
  · have hxi := Ordinal.natOrdinal_of_eq_wpow_log hprin
    rw [NatOrdinal.of_val] at hxi
    rw [hxi] at hnot h ⊢
    congr 1
    exact le_antisymm (Order.lt_add_one_iff.mp (NatOrdinal.wpow_lt_wpow.mp h))
      (le_of_not_gt fun hlt ↦ hnot (NatOrdinal.wpow_lt_wpow.mpr hlt))

/-- A series of `J_{ω^(α+1)}` has ordinal value `ω^α` or lies in `J_{ω^α}`. -/
theorem ordinalValue_eq_or_lt_of_lt_wpow_add_one {α : NatOrdinal} {c : Series K}
    (h : ordinalValue c < ω^ (α + 1)) :
    ordinalValue c = ω^ α ∨ ordinalValue c < ω^ α := by
  by_cases hne : gradeClass α c = 0
  · exact Or.inr ((gradeClass_eq_zero_iff h).mp hne)
  · exact Or.inl (ordinalValue_eq_of_gradeClass_ne_zero h hne)

/-- The grade-`α` class is additive on `J_{ω^(α+1)}`. -/
theorem gradeClass_add {α : NatOrdinal} {b c : Series K}
    (hb : ordinalValue b < ω^ (α + 1)) (hc : ordinalValue c < ω^ (α + 1)) :
    gradeClass α (b + c) = gradeClass α b + gradeClass α c := by
  have hbc : ordinalValue (b + c) < ω^ (α + 1) :=
    (ordinalValue_add_le_max b c).trans_lt (max_lt hb hc)
  rw [gradeClass_eq_homogeneousMk hb, gradeClass_eq_homogeneousMk hc,
    gradeClass_eq_homogeneousMk hbc, ← map_add]
  rfl

/-- The grade-`α` class of a constant multiple is the scalar multiple of the class. -/
theorem gradeClass_C_mul {α : NatOrdinal} (k : K) {c : Series K}
    (hc : ordinalValue c < ω^ (α + 1)) :
    gradeClass α ((HahnSeries.Nonpositive.C : K →+* Series K) k * c) = k • gradeClass α c := by
  have hkc : ordinalValue ((HahnSeries.Nonpositive.C : K →+* Series K) k * c) < ω^ (α + 1) := by
    simpa only [zero_add] using
      ordinalValue_mul_lt_wpow_add_one (ordinalValue_C_lt_wpow_one k) hc
  rw [gradeClass_of_lt hkc, gradeClass_of_lt hc, ← DirectSum.of_smul, smul_principalComponentMk]

/-- A finite sum of series of `J_{ω^(α+1)}` lies in `J_{ω^(α+1)}`. -/
theorem ordinalValue_sum_lt_wpow_add_one {α : NatOrdinal} {ι : Type*} (s : Finset ι)
    (f : ι → Series K) (hf : ∀ i ∈ s, ordinalValue (f i) < ω^ (α + 1)) :
    ordinalValue (∑ i ∈ s, f i) < ω^ (α + 1) := by
  rw [← ordinalValueDegree_le_coe_iff, ← ordinalValueDegreeValuation_apply]
  refine MaxAddDegree.map_sum_le_of_forall_le (ordinalValueDegreeValuation K) s f _
    fun i hi ↦ ?_
  rw [ordinalValueDegreeValuation_apply, ordinalValueDegree_le_coe_iff]
  exact hf i hi

/-- The grade-`α` class of a finite sum of series in `J_{ω^(α+1)}`. -/
theorem gradeClass_sum {α : NatOrdinal} {ι : Type*} (s : Finset ι) (f : ι → Series K)
    (hf : ∀ i ∈ s, ordinalValue (f i) < ω^ (α + 1)) :
    gradeClass α (∑ i ∈ s, f i) = ∑ i ∈ s, gradeClass α (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact gradeClass_eq_zero_of_lt (by rw [ordinalValue_zero]; exact NatOrdinal.wpow_pos α)
  | insert a s ha ih =>
      have hsum : ordinalValue (∑ i ∈ s, f i) < ω^ (α + 1) :=
        ordinalValue_sum_lt_wpow_add_one s f fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        gradeClass_add (hf a (Finset.mem_insert_self a s)) hsum,
        ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

/-- The grade-`α` class of a difference of series in `J_{ω^(α+1)}`. -/
theorem gradeClass_sub {α : NatOrdinal} {b c : Series K}
    (hb : ordinalValue b < ω^ (α + 1)) (hc : ordinalValue c < ω^ (α + 1)) :
    gradeClass α (b - c) = gradeClass α b - gradeClass α c := by
  have hbc : ordinalValue (b - c) < ω^ (α + 1) := by
    rw [sub_eq_add_neg]
    exact (ordinalValue_add_le_max b (-c)).trans_lt (max_lt hb (by rwa [ordinalValue_neg]))
  rw [eq_sub_iff_add_eq, ← gradeClass_add hbc hc, sub_add_cancel]

/-- The grade-`(α + β)` class of a product is the product of the grade classes. -/
theorem gradeClass_mul {α β : NatOrdinal} {b c : Series K}
    (hb : ordinalValue b < ω^ (α + 1)) (hc : ordinalValue c < ω^ (β + 1)) :
    gradeClass (α + β) (b * c) = gradeClass α b * gradeClass β c := by
  rw [gradeClass_of_lt (ordinalValue_mul_lt_wpow_add_one hb hc), gradeClass_of_lt hb,
    gradeClass_of_lt hc, ← principalComponentMul_mk, principalComponentMul_eq_componentMul,
    DirectSum.of_mul_of]
  rfl

/-- Series of `J_{ω^(α+1)}` congruent modulo `J_{ω^α}` have the same grade-`α` class. -/
theorem gradeClass_eq_of_sub_lt {α : NatOrdinal} {b c : Series K}
    (hb : ordinalValue b < ω^ (α + 1)) (hc : ordinalValue c < ω^ (α + 1))
    (h : ordinalValue (b - c) < ω^ α) :
    gradeClass α b = gradeClass α c := by
  rw [gradeClass_of_lt hb, gradeClass_of_lt hc, (principalComponentMk_eq_iff α b c hb hc).mpr h]

/-- The grade-`α` class lives in grade `α`: it is the inclusion of its `α`-component. -/
theorem gradeClass_eq_of_apply (α : NatOrdinal) (c : Series K) :
    gradeClass α c = DirectSum.of (PrincipalComponent K) α (gradeClass α c α) := by
  by_cases h : ordinalValue c < ω^ (α + 1)
  · rw [gradeClass_of_lt h, DirectSum.of_eq_same]
  · rw [gradeClass, dite_eq_right h, DirectSum.zero_apply, map_zero]

/-! ### The reducible span -/

variable (K) in
/-- FLLM24, Definition 4.1, in `P̂`: the `K`-span `D_α` of the products of two homogeneous
classes of positive grades `β, γ` with `β + γ = α`. It is the image `rv_J(R_α)`'s span, and
`c ∈ J_{ω^(α+1)}` lies in `A_α = J_α + Span_K(R_α)` exactly when its grade-`α` class lies in
`D_α`. -/
def decomposableSpan (α : NatOrdinal) : Submodule K (PrincipalSubring K) :=
  Submodule.span K
    {z | ∃ (β γ : NatOrdinal) (x : PrincipalComponent K β) (y : PrincipalComponent K γ),
      0 < β ∧ 0 < γ ∧ β + γ = α ∧
        z = DirectSum.of (PrincipalComponent K) β x *
          DirectSum.of (PrincipalComponent K) γ y}

theorem of_mul_of_mem_decomposableSpan {β γ : NatOrdinal} (hβ : 0 < β) (hγ : 0 < γ)
    (x : PrincipalComponent K β) (y : PrincipalComponent K γ) :
    DirectSum.of (PrincipalComponent K) β x * DirectSum.of (PrincipalComponent K) γ y ∈
      decomposableSpan K (β + γ) :=
  Submodule.subset_span ⟨β, γ, x, y, hβ, hγ, rfl, rfl⟩

/-- The grade class of a product of series of positive degrees `β, γ` lies in `D_{β+γ}`. -/
theorem gradeClass_mul_mem_decomposableSpan {β γ : NatOrdinal} (hβ : 0 < β) (hγ : 0 < γ)
    {b c : Series K} (hb : ordinalValue b < ω^ (β + 1)) (hc : ordinalValue c < ω^ (γ + 1)) :
    gradeClass (β + γ) (b * c) ∈ decomposableSpan K (β + γ) := by
  rw [gradeClass_mul hb hc, gradeClass_of_lt hb, gradeClass_of_lt hc]
  exact of_mul_of_mem_decomposableSpan hβ hγ _ _

/-- Every element of `D_α` is a finite combination of grade-`α` classes of products `u v` of
series of positive ordinal-value degrees `β, γ` with `β + γ = α`. -/
theorem exists_sum_of_mem_decomposableSpan {α : NatOrdinal} {z : PrincipalSubring K}
    (hz : z ∈ decomposableSpan K α) :
    ∃ (m : ℕ) (μ : Fin m → K) (β γ : Fin m → NatOrdinal) (u w : Fin m → Series K),
      (∀ k, 0 < β k ∧ 0 < γ k ∧ β k + γ k = α ∧
        ordinalValue (u k) < ω^ (β k + 1) ∧ ordinalValue (w k) < ω^ (γ k + 1)) ∧
      z = ∑ k, μ k • gradeClass α (u k * w k) := by
  rw [decomposableSpan, Submodule.mem_span_set'] at hz
  obtain ⟨m, μ, g, hsum⟩ := hz
  have hrep : ∀ k : Fin m, ∃ (β γ : NatOrdinal) (u w : Series K),
      0 < β ∧ 0 < γ ∧ β + γ = α ∧ ordinalValue u < ω^ (β + 1) ∧ ordinalValue w < ω^ (γ + 1) ∧
        (g k : PrincipalSubring K) = gradeClass α (u * w) := by
    intro k
    obtain ⟨β, γ, x, y, hβ, hγ, hβγ, hz⟩ := (g k).2
    obtain ⟨u, hu, rfl⟩ := exists_principalComponentMk β x
    obtain ⟨w, hw, rfl⟩ := exists_principalComponentMk γ y
    refine ⟨β, γ, u, w, hβ, hγ, hβγ, hu, hw, ?_⟩
    rw [hz, ← gradeClass_of_lt hu, ← gradeClass_of_lt hw, ← gradeClass_mul hu hw, hβγ]
  choose β γ u w hβ hγ hβγ hu hw hg using hrep
  refine ⟨m, μ, β, γ, u, w, fun k ↦ ⟨hβ k, hγ k, hβγ k, hu k, hw k⟩, ?_⟩
  rw [← hsum]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [hg k]

/-- No product of two positive grades is `1`: `D_1 = 0`, FLLM24, Remark 4.2. -/
theorem decomposableSpan_one : decomposableSpan K 1 = ⊥ := by
  rw [decomposableSpan, Submodule.span_eq_bot]
  rintro z ⟨β, γ, x, y, hβ, hγ, hβγ, rfl⟩
  exfalso
  have h1 : (1 : NatOrdinal) ≤ β := Order.one_le_iff_pos.mpr hβ
  have h2 : (1 : NatOrdinal) ≤ γ := Order.one_le_iff_pos.mpr hγ
  have h12 : (1 : NatOrdinal) + 1 ≤ β + γ := add_le_add h1 h2
  rw [hβγ] at h12
  exact absurd h12 (not_le.mpr (lt_add_one 1))

/-! ### The property `(*)_α` -/

variable (K) in
/-- FLLM24, § 4, property `(*)_α` at a finite degree `n`: every hereditarily `rv_J`-independent
family `b` of series with `v_J(b i) = ω^n` has classes `rv_J(b i)` that are `K`-linearly
independent modulo `D_n`, which is the source's "`K`-linearly independent over `A_n`". -/
def IndependentModuloDecomposable (n : ℕ) : Prop :=
  ∀ {ι : Type} (b : ι → Series K), HereditarilyRVIndependent n b →
    LinearIndependent K (fun i ↦ (decomposableSpan K (n : NatOrdinal)).mkQ (rvJ (b i)))

/-- Introduction rule for `(*)_n`. -/
theorem IndependentModuloDecomposable.of {n : ℕ}
    (h : ∀ {ι : Type} (b : ι → Series K), HereditarilyRVIndependent n b →
      LinearIndependent K (fun i ↦ (decomposableSpan K (n : NatOrdinal)).mkQ (rvJ (b i)))) :
    IndependentModuloDecomposable K n :=
  h

/-- Elimination rule for `(*)_n`. -/
theorem IndependentModuloDecomposable.linearIndependent {n : ℕ}
    (h : IndependentModuloDecomposable K n) {ι : Type} {b : ι → Series K}
    (hb : HereditarilyRVIndependent n b) :
    LinearIndependent K (fun i ↦ (decomposableSpan K (n : NatOrdinal)).mkQ (rvJ (b i))) :=
  h b hb

/-- FLLM24, Proposition 4.3, for `β = 0`: `(*)_1` holds, because `A_1 = J_1` and hereditary
`rv_J`-independence at degree `1` is linear independence of the classes. -/
theorem independentModuloDecomposable_one : IndependentModuloDecomposable K 1 := by
  intro ι b hb
  have hlin := hb.linearIndependent
  refine hlin.map' (decomposableSpan K ((1 : ℕ) : NatOrdinal)).mkQ ?_
  rw [Submodule.ker_mkQ, Nat.cast_one, decomposableSpan_one]

/-- Under `(*)_n`, the class of a single hereditarily `rv_J`-independent series of degree `n`
lies outside `D_n`. -/
theorem rvJ_notMem_decomposableSpan {n : ℕ} (hstar : IndependentModuloDecomposable K n)
    {b : Series K} (hb : HereditarilyRVIndependent n (fun _ : Unit ↦ b)) :
    rvJ b ∉ decomposableSpan K (n : NatOrdinal) := by
  intro hmem
  have hlin := hstar (fun _ : Unit ↦ b) hb
  have hne := hlin.ne_zero ()
  apply hne
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hmem

end FLLM24

end
