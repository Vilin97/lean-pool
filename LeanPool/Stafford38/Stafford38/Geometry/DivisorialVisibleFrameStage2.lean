/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.FiniteType
import LeanPool.Stafford38.Stafford38.Geometry.NormalizationHeightOne

open IsLocalRing
open scoped nonZeroDivisors

noncomputable section
universe u

namespace Stafford38.Geometry.DivisorialVisibleFrameStage2

section Chart
variable {K : Type u} [Field K]

private lemma chart_of_valuation
    {r : ℕ} (Y : Fin (r + 1) → K) (W : ValuationSubring K) (hY : Y 0 = 1) :
    ∃ (j : Fin (r + 1)) (s : K), s ≠ 0 ∧ Y j * s = 1 ∧
      ∀ a, Y a * s ∈ W.toSubring := by
  classical
  let S : Set (Fin (r + 1)) := {a | Y a ≠ 0}
  have hS : S.Nonempty := ⟨0, by simp [S, hY]⟩
  letI : LE (Fin (r + 1)) :=
    ⟨fun a b => Y b ≠ 0 ∧ Y a / Y b ∈ W.toSubring⟩
  have htrans : IsTrans (Fin (r + 1)) LE.le := by
    constructor
    intro a b c hab hbc
    rcases hab with ⟨hb, hab⟩
    rcases hbc with ⟨hc, hbc⟩
    refine ⟨hc, ?_⟩
    have := W.toSubring.mul_mem hab hbc
    rw [div_eq_mul_inv] at hab hbc ⊢
    simpa [div_eq_mul_inv, mul_assoc, hb] using this
  letI : IsTrans (Fin (r + 1)) LE.le := htrans
  obtain ⟨j, hjS, hjmax⟩ := S.toFinite.exists_maximalFor id S hS
  have hj0 : Y j ≠ 0 := hjS
  let s := (Y j)⁻¹
  refine ⟨j, s, inv_ne_zero hj0, ?_, ?_⟩
  · simp [s, hj0]
  · intro a
    by_cases ha : Y a = 0
    · rw [ha, zero_mul]
      exact W.zero_mem
    have haS : a ∈ S := ha
    rcases W.mem_or_inv_mem (Y a / Y j) with h | h
    · simpa [s, div_eq_mul_inv, mul_comm] using h
    · have h' : Y a / Y j ∈ W.toSubring := by
        apply (hjmax haS ⟨ha, ?_⟩).2
        simpa [div_eq_mul_inv, mul_comm] using h
      simpa [s, div_eq_mul_inv, mul_comm] using h'

end Chart

section Generation
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private lemma normalized_generates_top
    {r : ℕ} (y : Fin r → K) (i : Fin r) (s : K) (hs : s ≠ 0)
    (hgen : IntermediateField.adjoin k (Set.range y) = ⊤) :
    IntermediateField.adjoin k
        (Set.range (fun a : Fin (r + 1) => (Fin.cases 1 y a : K) * s) ∪ {y i}) = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply IntermediateField.adjoin_le_iff.2
  intro a ha
  rcases ha with ⟨a, rfl⟩
  apply IntermediateField.mem_adjoin_iff_div.mpr
  refine ⟨(Fin.cases 1 y (Fin.succ a) : K) * s, ?_, s, ?_, ?_⟩
  · exact Algebra.subset_adjoin (R := k) (A := K)
      (Set.mem_union_left _ (Set.mem_range_self _))
  · have h0 : (Fin.cases 1 y (0 : Fin (r + 1)) : K) * s ∈
        Algebra.adjoin k
          (Set.range (fun a : Fin (r + 1) => (Fin.cases 1 y a : K) * s) ∪ {y i}) :=
      Algebra.subset_adjoin (R := k) (A := K)
        (Set.mem_union_left _ (Set.mem_range_self (0 : Fin (r + 1))))
    simpa only [Fin.cases_zero, one_mul] using h0
  · simp only [Fin.cases_succ]
    exact (eq_div_iff hs).2 rfl

end Generation

section Pivot

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem exists_valuationSubring_of_transcendental
    (x : K) (hx : Transcendental k x) :
    ∃ W : ValuationSubring K, (∀ c : k, algebraMap k K c ∈ W) ∧ x ∈ W ∧ x⁻¹ ∉ W := by
  classical
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  let R : Subring K := (Algebra.adjoin k ({x} : Set K)).toSubring
  have hxR : x ∈ R := Algebra.subset_adjoin (Set.mem_singleton x)
  let I : Ideal R := Ideal.span {⟨x, hxR⟩}
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ I := htop ▸ Submodule.mem_top
    rw [Ideal.mem_span_singleton'] at h1
    obtain ⟨g, hg⟩ := h1
    have hg' : (g : K) * x = 1 := by
      have := congrArg Subtype.val hg
      simpa using this
    obtain ⟨q, hq⟩ : ∃ q : Polynomial k, Polynomial.aeval x q = (g : K) := by
      have hmem : (g : K) ∈ Algebra.adjoin k ({x} : Set K) := g.2
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
      exact (AlgHom.mem_range _).1 hmem
    apply hx
    refine ⟨q * Polynomial.X - 1, ?_, ?_⟩
    · intro h0
      have hc := congrArg (fun p : Polynomial k => p.coeff 0) h0
      simp [Polynomial.mul_coeff_zero] at hc
    · simp [map_sub, map_mul, hq, hg']
  obtain ⟨W, hRW, hIW⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hxW : x ∈ W := hRW hxR
  refine ⟨W, fun c => hRW (Subalgebra.algebraMap_mem _ c), hxW, ?_⟩
  intro hinv
  have hxn : x ∈ W.nonunits := hIW ⟨⟨x, hxR⟩, Ideal.mem_span_singleton_self _, rfl⟩
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hxn
  obtain ⟨hxW', hxm⟩ := hxn
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hxm
  exact hxm (isUnit_iff_exists_inv.2
    ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩)

end Pivot

open Stafford38.Geometry.NormalizationHeightOne

theorem stage2_exists_chart_normalization
    {k K : Type u} [Field k] [CharZero k] [Field K] [Algebra k K]
    {r : ℕ} (y : Fin r → K) (i : Fin r)
    (hgen : IntermediateField.adjoin k (Set.range y) = ⊤) (hx : Transcendental k (y i)) :
    ∃ (j : Fin (r + 1)) (s : K) (A : Subalgebra k K),
      s ≠ 0 ∧ (Fin.cases 1 y j : K) * s = 1 ∧
      (∀ a, (Fin.cases 1 y a : K) * s ∈ A) ∧ y i ∈ A ∧
      Algebra.FiniteType k A ∧ IsIntegrallyClosedIn A K ∧ IsFractionRing A K ∧
      (∀ a : A, IsIntegral (Algebra.adjoin k
        (Set.range (fun a : Fin (r + 1) => (Fin.cases 1 y a : K) * s) ∪ {y i})) (a : K)) ∧
      (y i)⁻¹ ∉ A := by
  classical
  obtain ⟨W, hkW, hxiW, hxiInvW⟩ := exists_valuationSubring_of_transcendental (y i) hx
  let Y : Fin (r + 1) → K := Fin.cases 1 y
  obtain ⟨j, s, hs, hjs, hYsW⟩ := chart_of_valuation Y W (by simp [Y])
  let C₀ : Subalgebra k K :=
    Algebra.adjoin k (Set.range (fun a : Fin (r + 1) => Y a * s) ∪ {y i})
  let SW : Subalgebra k K :=
    { W.toSubring with algebraMap_mem' := hkW }
  have hC₀W : C₀ ≤ SW := by
    apply Algebra.adjoin_le
    rintro z (⟨a, rfl⟩ | rfl)
    · exact hYsW a
    · exact hxiW
  have htop : IntermediateField.adjoin k
      (Set.range (fun a : Fin (r + 1) => Y a * s) ∪ {y i}) = ⊤ :=
    normalized_generates_top y i s hs hgen
  letI hC₀fr : IsFractionRing C₀ K := IsFractionRing.of_field C₀ K fun z => by
    have hz : z ∈ IntermediateField.adjoin k
        (Set.range (fun a : Fin (r + 1) => Y a * s) ∪ {y i}) := by
      rw [htop]
      exact Set.mem_univ z
    rw [IntermediateField.mem_adjoin_iff_div] at hz
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
  let A₀ : Subalgebra C₀ K := integralClosure C₀ K
  let A : Subalgebra k K := A₀.restrictScalars k
  have hC₀A : C₀ ≤ A := fun z hz => A₀.algebraMap_mem ⟨z, hz⟩
  letI : IsIntegrallyClosedIn W.toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn W K)
  have hA₀W : A₀.toSubring ≤ W.toSubring := by
    change (integralClosure C₀ K).toSubring ≤ W.toSubring
    apply (Subring.integralClosure_subring_le_iff (S := C₀) (T := W.toSubring)).2
    exact hC₀W
  have hyA : y i ∈ A := by
    exact A₀.algebraMap_mem ⟨y i, Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))⟩
  have hnormA : ∀ a, Y a * s ∈ A := by
    intro a
    exact A₀.algebraMap_mem
      ⟨Y a * s, Algebra.subset_adjoin (Set.mem_union_left _ (Set.mem_range_self a))⟩
  have hinvA : (y i)⁻¹ ∉ A := fun h => hxiInvW (hA₀W h)
  haveI hC₀ft : Algebra.FiniteType k C₀ := Algebra.FiniteType.adjoin_of_finite
    (Set.Finite.union (Set.finite_range _) (Set.finite_singleton _))
  let D : Subalgebra C₀ (FractionRing C₀) := integralClosure C₀ (FractionRing C₀)
  haveI hDfin : Module.Finite C₀ D :=
    finite_normalization_of_fg_domain k C₀ D
  let e : FractionRing C₀ ≃ₐ[C₀] K :=
    IsLocalization.algEquiv C₀⁰ (FractionRing C₀) K
  haveI hA₀fin : Module.Finite C₀ A₀ :=
    Module.Finite.equiv e.mapIntegralClosure.toLinearEquiv
  have hsub : A.toSubring = A₀.toSubring := rfl
  let er : A ≃+* A₀ := RingEquiv.subringCongr hsub
  letI : Algebra C₀ A :=
    (er.symm.toRingHom.comp (algebraMap C₀ A₀)).toAlgebra
  let ea : A₀ ≃ₐ[C₀] A := AlgEquiv.ofRingEquiv (f := er.symm) (fun _ => rfl)
  letI : IsScalarTower k C₀ A := IsScalarTower.of_algebraMap_eq fun _ => by
    apply Subtype.ext
    rfl
  letI : IsScalarTower C₀ A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hAfin : Module.Finite C₀ A := Module.Finite.equiv ea.toLinearEquiv
  have hAft : Algebra.FiniteType k A :=
    Algebra.FiniteType.trans hC₀ft (inferInstance : Algebra.FiniteType C₀ A)
  have hAic : IsIntegrallyClosedIn A K := by
    apply Subring.isIntegrallyClosedIn_iff.mpr
    intro x hx
    change x ∈ integralClosure C₀ K
    exact isIntegral_trans (R := C₀) (A := A) x hx
  have hAfr : IsFractionRing A K := IsFractionRing.of_field A K fun z => by
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective C₀ z
    refine ⟨⟨a, hC₀A a.2⟩, ⟨b, hC₀A b.2⟩, ?_⟩
    change z = (a : K) / (b : K)
    exact hab.symm
  refine ⟨j, s, A, hs, hjs, hnormA, hyA, hAft, hAic, hAfr, ?_, hinvA⟩
  intro a
  exact a.2


end Stafford38.Geometry.DivisorialVisibleFrameStage2
