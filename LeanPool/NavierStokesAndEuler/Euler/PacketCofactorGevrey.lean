/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCofactorOperator
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Polynomial Gevrey bounds for the actual inverse, strain and curvature
recovered from a determinant-one deformation and its first two time jets. -/

@[expose] public section


noncomputable section

namespace EulerPacketCofactor

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerPacketPiola
  EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup EndSpace` instance to shorten typeclass synthesis. -/
local instance instPacketCofactorGevrey1 : NormedAddCommGroup EndSpace := inferInstance
/-- Cache the standard `NormedSpace ℝ EndSpace` instance to shorten typeclass synthesis. -/
local instance instPacketCofactorGevrey2 : NormedSpace ℝ EndSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (EndSpace →L[ℝ] EndSpace)` instance to shorten
typeclass synthesis. -/
local instance instPacketCofactorGevrey3 : NormedAddCommGroup (EndSpace →L[ℝ] EndSpace) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (EndSpace →L[ℝ] EndSpace)` instance to shorten typeclass
synthesis. -/
local instance instPacketCofactorGevrey4 : NormedSpace ℝ (EndSpace →L[ℝ] EndSpace) := inferInstance
/-- Cache the standard `NormedAddCommGroup (EndSpace →L[ℝ] EndSpace →L[ℝ] EndSpace)` instance to
shorten typeclass synthesis. -/
local instance instPacketCofactorGevrey5 : NormedAddCommGroup (EndSpace →L[ℝ] EndSpace →L[ℝ]
    EndSpace) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (EndSpace →L[ℝ] EndSpace →L[ℝ] EndSpace)` instance to
shorten typeclass synthesis. -/
local instance instPacketCofactorGevrey6 : NormedSpace ℝ (EndSpace →L[ℝ] EndSpace →L[ℝ] EndSpace)
    := inferInstance

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem adjugate_contDiff (F : P → EndSpace) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => adjugate (F x)) :=
  (cofactorBilinear.contDiff.comp hF).clm_apply hF

theorem adjugate_bound (F : P → EndSpace) (hF : ContDiff ℝ ∞ F)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hFb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ C * majorant R 0 n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => adjugate (F y)) x‖ ≤ (9*C^2)*majorant R 0 n := by
  have hp := sequence_product_majorant R C C hR hC hC 0 0
    (fun k => ‖iteratedFDeriv ℝ k F x‖) (fun k => ‖iteratedFDeriv ℝ k F x‖)
    (fun k => by simpa only [abs_norm] using hFb k x)
    (fun k => by simpa only [abs_norm] using hFb k x) n
  have hs : (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i F x‖*‖iteratedFDeriv ℝ (n-i) F x‖) ≤
      (3*C*C)*majorant R 0 n := (le_abs_self _).trans (by simpa only [zero_add] using hp)
  calc
    _ ≤ ‖cofactorBilinear‖*(∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i F x‖*‖iteratedFDeriv ℝ (n-i) F x‖) :=
      cofactorBilinear.norm_iteratedFDeriv_le_of_bilinear hF hF x (by simp)
    _ ≤ ‖cofactorBilinear‖*((3*C*C)*majorant R 0 n) :=
      mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ ≤ 3*((3*C*C)*majorant R 0 n) :=
      mul_le_mul_of_nonneg_right cofactorBilinear_norm
        (mul_nonneg (by positivity) (majorant_nonneg R hR 0 n))
    _ = (9*C^2)*majorant R 0 n := by ring

theorem inverse_contDiff (F I : P → EndSpace) (hF : ContDiff ℝ ∞ F)
    (hdet : ∀ x, (operatorMatrix (F x)).det = 1)
    (hI : ∀ x v, I x (F x v) = v) : ContDiff ℝ ∞ I := by
  have he : I = fun x => adjugate (F x) :=
    funext (fun x => inverse_eq_adjugate (F x) (I x) (hdet x) (hI x))
  rw [he]
  exact adjugate_contDiff F hF

theorem inverse_bound (F I : P → EndSpace) (hF : ContDiff ℝ ∞ F)
    (hdet : ∀ x, (operatorMatrix (F x)).det = 1)
    (hI : ∀ x v, I x (F x v) = v)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hFb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ C * majorant R 0 n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n I x‖ ≤ (9*C^2)*majorant R 0 n := by
  have he : I = fun x => adjugate (F x) :=
    funext (fun x => inverse_eq_adjugate (F x) (I x) (hdet x) (hI x))
  rw [he]
  exact adjugate_bound F hF R C hR hC hFb n x

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem recovered_strain_eq (F F₁ M : P → EndSpace)
    (hdet : ∀ x, (operatorMatrix (F x)).det = 1)
    (h₁ : ∀ x v, F₁ x v = M x (F x v)) :
    M = fun x => (F₁ x).comp (adjugate (F x)) := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  have hv : F x (adjugate (F x) v) = v :=
    congrArg (fun L : EndSpace => L v) (comp_adjugate (F x) (hdet x))
  change M x v = F₁ x (adjugate (F x) v)
  rw [h₁,hv]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem recovered_curvature_eq (F F₂ H : P → EndSpace)
    (hdet : ∀ x, (operatorMatrix (F x)).det = 1)
    (h₂ : ∀ x v, F₂ x v = -(H x (F x v))) :
    H = fun x => -((F₂ x).comp (adjugate (F x))) := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  have hv : F x (adjugate (F x) v) = v :=
    congrArg (fun L : EndSpace => L v) (comp_adjugate (F x) (hdet x))
  change H x v = -(F₂ x (adjugate (F x) v))
  rw [h₂,hv,neg_neg]

theorem strain_bound (F F₁ M : P → EndSpace)
    (hF : ContDiff ℝ ∞ F) (hF₁ : ContDiff ℝ ∞ F₁)
    (hdet : ∀ x, (operatorMatrix (F x)).det = 1)
    (h₁ : ∀ x v, F₁ x v = M x (F x v))
    (R C C₁ : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hFb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ C * majorant R 0 n)
    (hF₁b : ∀ n x, ‖iteratedFDeriv ℝ n F₁ x‖ ≤ C₁ * majorant R 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n M x‖ ≤ (27*C^2*C₁)*majorant R 0 n := by
  rw [recovered_strain_eq F F₁ M hdet h₁]
  have h := clm_comp_bound F₁ (fun y => adjugate (F y)) hF₁ (adjugate_contDiff F hF)
    R C₁ (9*C^2) hR hC₁ (by positivity) 0 0 hF₁b
    (adjugate_bound F hF R C hR hC hFb) n x
  exact h.trans_eq (by rw [zero_add]; ring)

theorem curvature_bound (F F₂ H : P → EndSpace)
    (hF : ContDiff ℝ ∞ F) (hF₂ : ContDiff ℝ ∞ F₂)
    (hdet : ∀ x, (operatorMatrix (F x)).det = 1)
    (h₂ : ∀ x v, F₂ x v = -(H x (F x v)))
    (R C C₂ : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂)
    (hFb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ C * majorant R 0 n)
    (hF₂b : ∀ n x, ‖iteratedFDeriv ℝ n F₂ x‖ ≤ C₂ * majorant R 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n H x‖ ≤ (27*C^2*C₂)*majorant R 0 n := by
  rw [recovered_curvature_eq F F₂ H hdet h₂]
  have h := neg_bound (fun y => (F₂ y).comp (adjugate (F y))) R (3*C₂*(9*C^2)) 0
    (fun n x => by
      simpa only [zero_add] using clm_comp_bound F₂ (fun y => adjugate (F y))
        hF₂ (adjugate_contDiff F hF) R C₂ (9*C^2) hR hC₂ (by positivity) 0 0 hF₂b
        (adjugate_bound F hF R C hR hC hFb) n x) n x
  exact h.trans_eq (by ring)

end EulerPacketCofactor
