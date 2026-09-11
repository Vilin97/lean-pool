/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCofactorOperator
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! The actual parent deformation supplies inverse and strain bounds with
polynomial constants.  Determinant one removes any inverse-derivative input. -/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCofactor

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerPacketPiola
  EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup EndSpace` instance to shorten typeclass synthesis. -/
local instance instPacketParentCoefficientBounds1 : NormedAddCommGroup EndSpace := inferInstance
/-- Cache the standard `NormedSpace ℝ EndSpace` instance to shorten typeclass synthesis. -/
local instance instPacketParentCoefficientBounds2 : NormedSpace ℝ EndSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ EndSpace)` instance to shorten typeclass
synthesis. -/
local instance instPacketParentCoefficientBounds3 : NormedAddCommGroup (Space →ᵇ EndSpace) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ EndSpace)` instance to shorten typeclass
synthesis. -/
local instance instPacketParentCoefficientBounds4 : NormedSpace ℝ (Space →ᵇ EndSpace) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,Space →ᵇ EndSpace)` instance to shorten typeclass
synthesis. -/
local instance instPacketParentCoefficientBounds5 : NormedAddCommGroup C(K,Space →ᵇ EndSpace) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,Space →ᵇ EndSpace)` instance to shorten typeclass
synthesis. -/
local instance instPacketParentCoefficientBounds6 : NormedSpace ℝ C(K,Space →ᵇ EndSpace) :=
    inferInstance

theorem coefficientPath_norm_le (F : SmoothCoefficientPath K EndSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀ t x, ‖F.field t x‖ ≤ C) : ‖F.field‖ ≤ C :=
  (ContinuousMap.norm_le F.field hC).2 (fun t => (BoundedContinuousFunction.norm_le hC).2 (hF t))

theorem coefficientPath_norm_le_of_gevrey (F : SmoothCoefficientPath K EndSpace)
    (R C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → EndSpace) x‖ ≤ C * majorant R 0 n) :
    ‖F.field‖ ≤ C := by
  apply coefficientPath_norm_le F C hC
  intro t x
  simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
    Nat.cast_one,pow_zero,mul_one,one_pow] using hF 0 t x

theorem coefficientInverse_norm_le (F : SmoothCoefficientPath K EndSpace)
    (I : C(K, Space →ᵇ EndSpace))
    (hdet : ∀ t x, (operatorMatrix (F.field t x)).det = 1)
    (hI : ∀ t x v, I t x (F.field t x v) = v)
    (C : ℝ) (_hC : 0 ≤ C) (hF : ∀ t x, ‖F.field t x‖ ≤ C) :
    ‖I‖ ≤ 3*C^2 := by
  apply (ContinuousMap.norm_le I (by positivity)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro x
  rw [inverse_eq_adjugate (F.field t x) (I t x) (hdet t x) (hI t x)]
  exact (adjugate_norm _).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hF t x) 2) (by norm_num))

theorem coefficientInverse_bound (F : SmoothCoefficientPath K EndSpace)
    (I : C(K, Space →ᵇ EndSpace))
    (hdet : ∀ t x, (operatorMatrix (F.field t x)).det = 1)
    (hI : ∀ t x v, I t x (F.field t x v) = v)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → EndSpace) x‖ ≤ C * majorant R 0 n)
    (n : ℕ) (t : K) (x : Space) :
    ‖iteratedFDeriv ℝ n (I t : Space → EndSpace) x‖ ≤ (9*C^2)*majorant R 0 n :=
  inverse_bound (F.field t) (I t) (F.smooth t) (hdet t) (hI t)
    R C hR hC (fun n x => hF n t x) n x

theorem coefficientStrain_bound (F F₁ M : SmoothCoefficientPath K EndSpace)
    (hdet : ∀ t x, (operatorMatrix (F.field t x)).det = 1)
    (h₁ : ∀ t x v, F₁.field t x v = M.field t x (F.field t x v))
    (R C C₁ : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → EndSpace) x‖ ≤ C * majorant R 0 n)
    (hF₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (F₁.field t : Space → EndSpace) x‖ ≤ C₁ * majorant R 0 n)
    (n : ℕ) (t : K) (x : Space) :
    ‖iteratedFDeriv ℝ n (M.field t : Space → EndSpace) x‖ ≤ (27*C^2*C₁)*majorant R 0 n :=
  strain_bound (F.field t) (F₁.field t) (M.field t) (F.smooth t) (F₁.smooth t)
    (hdet t) (h₁ t) R C C₁ hR hC hC₁ (fun n x => hF n t x) (fun n x => hF₁ n t x) n x

theorem coefficientCurvature_bound (F F₂ H : SmoothCoefficientPath K EndSpace)
    (hdet : ∀ t x, (operatorMatrix (F.field t x)).det = 1)
    (h₂ : ∀ t x v, F₂.field t x v = -(H.field t x (F.field t x v)))
    (R C C₂ : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂)
    (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → EndSpace) x‖ ≤ C * majorant R 0 n)
    (hF₂ : ∀ n t x, ‖iteratedFDeriv ℝ n (F₂.field t : Space → EndSpace) x‖ ≤ C₂ * majorant R 0 n)
    (n : ℕ) (t : K) (x : Space) :
    ‖iteratedFDeriv ℝ n (H.field t : Space → EndSpace) x‖ ≤ (27*C^2*C₂)*majorant R 0 n :=
  curvature_bound (F.field t) (F₂.field t) (H.field t) (F.smooth t) (F₂.smooth t)
    (hdet t) (h₂ t) R C C₂ hR hC hC₂ (fun n x => hF n t x) (fun n x => hF₂ n t x) n x

end EulerPacketCofactor

namespace EulerTransversePacketProvider.Data

open Set EulerSmoothLimit EulerPacketCofactor EulerPacketPiola
open scoped BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

theorem inverseBound_le_of_frame (C : ℝ) (hC : 0 ≤ C)
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
    (hF : ∀ t x, ‖D.F.field t x‖ ≤ C) : D.inverseBound ≤ 1+3*C^2 := by
  change 1+‖D.FInv.field‖ ≤ 1+3*C^2
  exact add_le_add le_rfl (coefficientInverse_norm_le D.F D.FInv.field hdet D.inverse_left C hC hF)

theorem frameBound_le_of_frame (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ t x, ‖D.F.field t x‖ ≤ C) : D.frameBound ≤ 1+C := by
  change 1+‖D.F.field‖ ≤ 1+C
  exact add_le_add le_rfl (coefficientPath_norm_le D.F C hC hF)

theorem frameLower_inv_le_of_frame (C : ℝ) (hC : 0 ≤ C)
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
    (hF : ∀ t x, ‖D.F.field t x‖ ≤ C) : D.frameLower⁻¹ ≤ (1+3*C^2)^2 := by
  change (D.inverseBound⁻¹^2)⁻¹ ≤ _
  rw [← inv_pow,inv_inv]
  exact pow_le_pow_left₀ D.inverseBound_pos.le (D.inverseBound_le_of_frame C hC hdet hF) 2

theorem normalLower_inv_le_of_frame (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ t x, ‖D.F.field t x‖ ≤ C) : D.normalLower⁻¹ ≤ (1+C)^2 := by
  change (D.frameBound⁻¹^2)⁻¹ ≤ _
  rw [← inv_pow,inv_inv]
  exact pow_le_pow_left₀ D.frameBound_pos.le (D.frameBound_le_of_frame C hC hF) 2

end EulerTransversePacketProvider.Data
