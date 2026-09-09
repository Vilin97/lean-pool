/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldGramGevrey
public import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardCoefficientGevrey
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets

@[expose] public section

/-!
# The actual source forward generator in uniform space-time coefficient norm

The Gram inverse is constructed in the bounded-field Banach algebra. This
produces the literal source coefficient -2(Q*Q)⁻¹Q*Q₁ and the projected-forcing
coefficient (Q*Q)⁻¹Q*. Spatial translation covariance and coefficient estimates
are proved for these actual fields.
-/

noncomputable section

namespace EulerBoundedFieldForwardGenerator

open Set ContinuousLinearMap EulerBoundedFieldCalculus EulerBoundedFieldGramInverse
  EulerTransverseGramInverse EulerOperatorGevreyCalculus EulerGevrey EulerTimeLpGramGevrey
  EulerTransverseForwardCoefficientGevrey EulerSmoothLimit EulerMeanCoefficients
open scoped BoundedContinuousFunction ContDiff

variable {α K U E : Type*} [TopologicalSpace α] [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private local instance : NormedAddCommGroup (U →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (U →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup (E →L[ℝ] U) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] U) := inferInstance
private local instance : NormedAddCommGroup (U →L[ℝ] U) := inferInstance
private local instance : NormedSpace ℝ (U →L[ℝ] U) := inferInstance
private local instance : NormedAddCommGroup (α →ᵇ U →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (α →ᵇ U →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup (α →ᵇ E →L[ℝ] U) := inferInstance
private local instance : NormedSpace ℝ (α →ᵇ E →L[ℝ] U) := inferInstance
private local instance : NormedAddCommGroup (α →ᵇ U →L[ℝ] U) := inferInstance
private local instance : NormedSpace ℝ (α →ᵇ U →L[ℝ] U) := inferInstance
private local instance : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E)) := inferInstance
private local instance : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E)) := inferInstance
private local instance : NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] U)) := inferInstance
private local instance : NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] U)) := inferInstance
private local instance : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] U)) := inferInstance
private local instance : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] U)) := inferInstance

/-- The actual projected-forcing coefficient field. -/
def leftInversePath (c : ℝ) (hc : 0 < c) (Q : C(K,α →ᵇ U →L[ℝ] E))
    (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q t x v‖^2) : C(K,α →ᵇ E →L[ℝ] U) :=
  pathCompositionMap (inversePath c hc Q hQ) (pathAdjointMap Q)

/-- The actual ordinary coefficient in source equation (12). -/
def generatorPath (c : ℝ) (hc : 0 < c) (Q Q₁ : C(K,α →ᵇ U →L[ℝ] E))
    (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q t x v‖^2) : C(K,α →ᵇ U →L[ℝ] U) :=
  (-2 : ℝ) • pathCompositionMap (leftInversePath c hc Q hQ) Q₁

@[simp] theorem leftInversePath_apply (c : ℝ) (hc : 0 < c) (Q : C(K,α →ᵇ U →L[ℝ] E))
    (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q t x v‖^2) (t : K) (x : α) :
    leftInversePath c hc Q hQ t x = (gramInverse (Q t x) c hc (hQ t x)).comp (Q t x).adjoint := rfl

@[simp] theorem generatorPath_apply (c : ℝ) (hc : 0 < c) (Q Q₁ : C(K,α →ᵇ U →L[ℝ] E))
    (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q t x v‖^2) (t : K) (x : α) :
    generatorPath c hc Q Q₁ hQ t x =
      (-2 : ℝ) • (gramInverse (Q t x) c hc (hQ t x)).comp ((Q t x).adjoint.comp (Q₁ t x)) := rfl

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Genuine parameter regularity of the actual projected-forcing coefficient. -/
theorem leftInversePath_contDiff (c : ℝ) (hc : 0 < c) (Q : P → C(K,α →ᵇ U →L[ℝ] E))
    (hQ : ∀ y t x v, c*‖v‖^2 ≤ ‖Q y t x v‖^2) {n : ℕ∞ω} (hQr : ContDiff ℝ n Q) :
    ContDiff ℝ n (fun y => leftInversePath c hc (Q y) (hQ y)) :=
  pathComposition_contDiff _ _ (inversePath_contDiff c hc Q hQ hQr) ((pathAdjointMap (α := α) (K :=
    K) (U := U) (E := E)).contDiff.comp hQr)

/-- Genuine parameter regularity of the actual source generator. -/
theorem generatorPath_contDiff (c : ℝ) (hc : 0 < c) (Q Q₁ : P → C(K,α →ᵇ U →L[ℝ] E))
    (hQ : ∀ y t x v, c*‖v‖^2 ≤ ‖Q y t x v‖^2) {n : ℕ∞ω}
    (hQr : ContDiff ℝ n Q) (hQ₁r : ContDiff ℝ n Q₁) :
    ContDiff ℝ n (fun y => generatorPath c hc (Q y) (Q₁ y) (hQ y)) :=
  (pathComposition_contDiff _ Q₁ (leftInversePath_contDiff c hc Q hQ hQr) hQ₁r).const_smul (-2 : ℝ)

variable (Q Q₁ : P → C(K,α →ᵇ U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ y t x v, c*‖v‖^2 ≤ ‖Q y t x v‖^2)
  (hQr : ContDiff ℝ ∞ Q) (hQ₁r : ContDiff ℝ ∞ Q₁)
  (Rc C₀ C₁ Ri : ℝ) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
  (hRi : 2*gramCost c C₀ 1*(Rc+1) ≤ Ri)
  (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀*majorant Rc 0 n)
  (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁*majorant Rc 0 n)

include hQr hRc hC₀ hRi hbQ in
/-- The projected-forcing coefficient has a polynomial shift-zero amplitude. -/
theorem leftInversePath_bound (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => leftInversePath c hc (Q y) (hQ y)) x‖ ≤
      (3*Ri*C₀)*majorant (4*Ri) 0 n := by
  obtain ⟨hi,hbase⟩ := inverseRadius_bounds c C₀ Rc Ri hc hRc hRi
  have hrad : 0 ≤ 4*Ri := by positivity
  have hbQ' (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j Q y‖ ≤ C₀*majorant (4*Ri) 0 j :=
    (hbQ j y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc (4*Ri) hRc hbase 0 j) hC₀)
  have hbAdj := contraction_bound (pathAdjointMap (α := α) (K := K) (U := U) (E := E))
    pathAdjointMap_norm Q hQr (4*Ri) C₀ hrad hC₀ 0 hbQ'
  exact pathComposition_bound (fun y => inversePath c hc (Q y) (hQ y))
    (fun y => pathAdjointMap (Q y)) (inversePath_contDiff c hc Q hQ hQr)
    ((pathAdjointMap (α := α) (K := K) (U := U) (E := E)).contDiff.comp hQr) (4*Ri) Ri C₀ hrad hi
      hC₀ 0 0
    (EulerBoundedFieldGramInverse.inversePath_coefficient_bound Q c hc hQ hQr Rc C₀ hRc hC₀ hbQ Ri
      hi hRi)
    hbAdj n x

include hQr hQ₁r hRc hC₀ hC₁ hRi hbQ hbQ₁ in
/-- The literal generator in (12) satisfies the source's polynomial coefficient bound. -/
theorem generatorPath_bound (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => generatorPath c hc (Q y) (Q₁ y) (hQ y)) x‖ ≤
      (18*Ri*C₀*C₁)*majorant (4*Ri) 0 n := by
  obtain ⟨hi,hbase⟩ := inverseRadius_bounds c C₀ Rc Ri hc hRc hRi
  have hrad : 0 ≤ 4*Ri := by positivity
  have hbQ₁' (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j Q₁ y‖ ≤ C₁*majorant (4*Ri) 0 j :=
    (hbQ₁ j y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc (4*Ri) hRc hbase 0 j) hC₁)
  let A := fun y => pathCompositionMap (leftInversePath c hc (Q y) (hQ y)) (Q₁ y)
  have hAr : ContDiff ℝ ∞ A := pathComposition_contDiff _ Q₁
    (leftInversePath_contDiff c hc Q hQ hQr) hQ₁r
  have hAb : ‖iteratedFDeriv ℝ n A x‖ ≤ (3*(3*Ri*C₀)*C₁)*majorant (4*Ri) 0 n :=
    pathComposition_bound _ Q₁ (leftInversePath_contDiff c hc Q hQ hQr) hQ₁r
      (4*Ri) (3*Ri*C₀) C₁ hrad (by positivity) hC₁ 0 0
      (leftInversePath_bound Q c hc hQ hQr Rc C₀ Ri hRc hC₀ hRi hbQ) hbQ₁' n x
  change ‖iteratedFDeriv ℝ n (fun y => (-2 : ℝ) • A y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hAr.contDiffAt.of_le (by simp)),norm_smul]
  norm_num only [norm_neg,Real.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left hAb (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

end EulerBoundedFieldForwardGenerator
