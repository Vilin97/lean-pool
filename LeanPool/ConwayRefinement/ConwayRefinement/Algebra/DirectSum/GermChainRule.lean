/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.OrdinalGenerators
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermPolynomial
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.OrdinalDerivation

/-!
# The chain rule for ordinal-graded filter-germ lowering derivations

This file isolates the successor-degree chain rule from the real-line filter used by the
principal-subring development.
-/

universe u v w z q

open Filter GermPolynomial MvPolynomial

public noncomputable section

namespace OrdinalGraded

variable {K : Type u} {R : Type v} {T : Type q}
variable [Field K] [CommRing R] [Algebra K R]
variable {l : Filter T}
variable (A : NatOrdinal.{z} → Submodule K R) [GradedAlgebra A]
variable {ι : Type w} {wt : ι → NatOrdinal.{z}} {x : ι → R}

/-- Polynomial representatives of the derivatives of homogeneous coordinates. -/
structure DerivativeRep (wt : ι → NatOrdinal.{z}) (x : ι → R)
    (Δ : Derivation K R (Germ l R)) (g : ι → T → MvPolynomial ι K) : Prop where
  /-- In successor degree, the representative has the preceding degree. -/
  homogeneous : ∀ i t, 0 < (wt i).constantCoeff →
    IsWeightedHomogeneous wt (g i t) ((wt i).removeNat 1)
  /-- When the degree is zero or a limit ordinal, the representative is zero. -/
  eq_zero : ∀ i t, (wt i).constantCoeff = 0 → g i t = 0
  /-- Evaluation of the representatives gives the derivative germ. -/
  map_coordinate : ∀ i, Δ (x i) = ((fun t ↦ aeval x (g i t)) : Germ l R)

namespace IsMinimalSystem

variable {A} (hx : OrdinalGraded.IsMinimalSystem A wt x)
variable {Δ : Derivation K R (Germ l R)} (hΔ : GermPolynomial.IsLoweringDerivation A Δ)
include hx hΔ

omit [GradedAlgebra A] in
/-- Derivative representatives exist for every ordinal minimal system. -/
theorem exists_derivativeRep (h0 : GradeZeroScalars A) :
    ∃ g : ι → T → MvPolynomial ι K, DerivativeRep wt x Δ g := by
  classical
  have hrep : ∀ i, ∃ g : T → MvPolynomial ι K,
      (0 < (wt i).constantCoeff →
        ∀ t, IsWeightedHomogeneous wt (g t) ((wt i).removeNat 1)) ∧
      ((wt i).constantCoeff = 0 → ∀ t, g t = 0) ∧
      Δ (x i) = ((fun t ↦ aeval x (g t)) : Germ l R) := by
    intro i
    by_cases hi : 0 < (wt i).constantCoeff
    · obtain ⟨f, hf, hfΔ⟩ := exists_rep_of_mem_germSubmodule _
        (GermPolynomial.IsLoweringDerivation.mem_lower hΔ hi (hx.mem i))
      have hpoly : ∀ t, ∃ p : MvPolynomial ι K,
          IsWeightedHomogeneous wt p ((wt i).removeNat 1) ∧ aeval x p = f t := fun t ↦
        OrdinalGraded.IsMinimalSystem.exists_aeval_eq hx h0 _ (f t) (hf t)
      choose g hg hgf using hpoly
      refine ⟨g, fun _ t ↦ hg t, fun hzero ↦ absurd hzero hi.ne', ?_⟩
      rw [hfΔ]
      congr 1
      funext t
      exact (hgf t).symm
    · refine ⟨fun _ ↦ 0, fun hpos ↦ absurd hpos hi, fun _ _ ↦ rfl, ?_⟩
      rw [GermPolynomial.IsLoweringDerivation.eq_zero hΔ
        (Nat.eq_zero_of_not_pos hi) (hx.mem i)]
      simp only [map_zero]
      rfl
  choose g hg hg0 hgΔ using hrep
  exact ⟨g, fun i t hi ↦ hg i hi t, fun i t hi ↦ hg0 i hi t, hgΔ⟩

end IsMinimalSystem

namespace DerivativeRep

variable {A : NatOrdinal.{z} → Submodule K R}
variable [GradedAlgebra A]
variable {Δ : Derivation K R (Germ l R)}
variable {g : ι → T → MvPolynomial ι K}
variable (hg : DerivativeRep (l := l) wt x Δ g)
variable (hΔ : GermPolynomial.IsLoweringDerivation A Δ)
include hg hΔ

/-- The chain rule for evaluation along homogeneous coordinates. -/
theorem map_aeval (F : MvPolynomial ι K) :
    Δ (aeval x F) =
      ((fun t ↦ aeval x (mkDerivation K (fun i ↦ g i t) F)) : Germ l R) :=
  GermPolynomial.IsHomogeneousCoordinates.map_aeval hΔ g hg.map_coordinate F

omit hΔ in
/-- Pointwise polynomial derivation lowers every successor degree by one. -/
theorem mkDerivation_isWeightedHomogeneous (t : T) {F : MvPolynomial ι K}
    {δ : NatOrdinal.{z}} (hF : IsWeightedHomogeneous wt F δ) :
    IsWeightedHomogeneous wt (mkDerivation K (fun i ↦ g i t) F) (δ.removeNat 1) :=
  mkDerivation_isWeightedHomogeneous_removeNat wt _ (fun i hi ↦ hg.homogeneous i t hi)
    (fun i hi ↦ hg.eq_zero i t hi) hF

omit hΔ in
/-- A variable occurring in a derivative representative has lower weight than its source. -/
theorem wt_lt_of_pderiv_ne_zero {i j : ι} {t : T}
    (h : pderiv j (g i t) ≠ 0) :
    wt j < wt i := by
  by_cases hi : 0 < (wt i).constantCoeff
  · have hj : j ∈ (g i t).vars := by
      by_contra hj
      exact h (pderiv_eq_zero_of_notMem_vars hj)
    refine ((hg.homogeneous i t hi).wt_le_of_mem_vars wt hj).trans_lt ?_
    have hsucc := NatOrdinal.removeNat_add_natCast (a := wt i) (n := 1) hi
    rw [Nat.cast_one] at hsucc
    exact lt_of_lt_of_eq (lt_add_one _) hsucc
  · exact absurd (by rw [hg.eq_zero i t (Nat.eq_zero_of_not_pos hi), map_zero]) h

/-- The pointwise derivative of a homogeneous relation of successor degree vanishes eventually. -/
theorem eventually_mkDerivation_eq_zero {δ : NatOrdinal.{z}}
    (hinj : ∀ β < δ, InjectiveAt K wt x β) (hδ : 0 < δ.constantCoeff)
    {F : MvPolynomial ι K} (hF : IsWeightedHomogeneous wt F δ) (hF0 : aeval x F = 0) :
    ∀ᶠ t in l, mkDerivation K (fun i ↦ g i t) F = 0 := by
  have h := hg.map_aeval hΔ F
  rw [hF0, map_zero, eq_comm] at h
  change ((fun t ↦ aeval x (mkDerivation K (fun i ↦ g i t) F)) : Germ l R) =
    ((fun _ : T ↦ (0 : R)) : Germ l R) at h
  rw [Germ.coe_eq] at h
  have hlt : δ.removeNat 1 < δ := by
    have hsucc := NatOrdinal.removeNat_add_natCast (a := δ) (n := 1) hδ
    rw [Nat.cast_one] at hsucc
    exact lt_of_lt_of_eq (lt_add_one _) hsucc
  exact h.mono fun t ht ↦
    (injectiveAt_iff _).mp (hinj _ hlt) _ (hg.mkDerivation_isWeightedHomogeneous t hF) ht

/-- Differentiating the eventually vanishing pointwise derivative of a relation. -/
theorem eventually_mkDerivation_pderiv_eq {δ : NatOrdinal.{z}}
    (hinj : ∀ β < δ, InjectiveAt K wt x β) (hδ : 0 < δ.constantCoeff)
    {F : MvPolynomial ι K} (hF : IsWeightedHomogeneous wt F δ) (hF0 : aeval x F = 0)
    (j : ι) :
    ∀ᶠ t in l, mkDerivation K (fun i ↦ g i t) (pderiv j F) =
      -mkDerivation K (fun i ↦ pderiv j (g i t)) F := by
  filter_upwards [hg.eventually_mkDerivation_eq_zero hΔ hinj hδ hF hF0] with t ht
  have h := pderiv_mkDerivation (fun i ↦ g i t) j F
  rw [ht, map_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

end DerivativeRep

end OrdinalGraded
