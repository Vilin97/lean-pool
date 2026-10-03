/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.BarNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Seminorm

/-! A coordinate-seminorm bridge for the paper `barNorm`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.FaaDiBruno

theorem BarNormBridge.orderedPartial_eq_barCoordinate {n : ℕ} {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ n f) (x : Vec 2) (I : Fin n → Fin 2) :
    orderedPartial n f x I =
      iteratedFDeriv ℝ n f x (fun j => basisVec (I j)) := by
  change iteratedFDeriv ℝ n
      (fun z : VecOne 2 => f (WithLp.ofLp z)) (WithLp.toLp 1 x)
        (fun j => coordinateVectorOne 2 (I j)) = _
  have h := (vecOneEquiv 2).toContinuousLinearMap.iteratedFDeriv_comp_right
    (f := f) hf (WithLp.toLp 1 x) (i := n) le_rfl
  have h' := congrArg (fun T => T (fun j => coordinateVectorOne 2 (I j))) h
  simpa [Function.comp_def, coordinateVectorOne, basisVec,
    vecOneEquiv, PiLp.coe_continuousLinearEquiv] using h'

theorem BarNormBridge.derivativeSup_eq_barCoordinates {n : ℕ} {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ n f) :
    derivativeSup n f = ⨆ I : Fin n → Fin 2,
      eLpNorm (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (I j))) ⊤ volume := by
  unfold derivativeSup
  apply iSup_congr
  intro I
  unfold partialSup
  rw [eLpNorm_exponent_top]
  · congr 1
    funext x
    exact BarNormBridge.orderedPartial_eq_barCoordinate hf x I
  · have hEval : Continuous (fun T :
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) ℝ =>
          T (fun j => basisVec (I j))) := by fun_prop
    exact (hEval.comp (hf.continuous_iteratedFDeriv le_rfl)).aestronglyMeasurable

/-- The §1 paper seminorm is exactly the ordered-coordinate seminorm
used by the Appendix B composition and transport estimates. -/
theorem barNorm_eq_snorm {n : ℕ} {R : ℝ} {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ n f) :
    AVenhance.barNorm n R f = AVenhance.FaaDiBruno.snorm f n R := by
  unfold AVenhance.barNorm AVenhance.FaaDiBruno.snorm
  rw [BarNormBridge.derivativeSup_eq_barCoordinates hf]

end AVenhance.FaaDiBruno

end
