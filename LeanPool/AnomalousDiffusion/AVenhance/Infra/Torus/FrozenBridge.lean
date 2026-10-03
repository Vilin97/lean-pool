/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.GradNormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad

/-! Real-valued d = 2 corollaries in the paper carriers. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

namespace AVenhance.Infra.Torus

/-- Regard a real-valued Euclidean function as complex-valued. -/
def realToComplex (f : Vec 2 → ℝ) : Vec 2 → ℂ := Complex.ofRealCLM ∘ f

/-- The complex coordinate derivative of the real cast is the cast of the
classical gradient. -/
theorem coordDeriv_realToComplex {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin 2) (x : Vec 2) :
    coordDeriv i (realToComplex f) x = (AVenhance.spaceGrad f x i : ℂ) := by
  let z := i.removeNth x
  have hx : i.insertNth (x i) z = x := by
    exact Fin.insertNth_self_removeNth i x
  have hcast : ContDiff ℝ 1 (realToComplex f) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hcomplex :=
    (hcast.differentiable (by simp) (i.insertNth (x i) z)).hasFDerivAt
      |>.comp_hasDerivAt (x i) (Homogenization.hasDerivAt_insertNth i z (x i))
  have hreal :=
    (hf.differentiable (by simp) (i.insertNth (x i) z)).hasFDerivAt
      |>.comp_hasDerivAt (x i) (Homogenization.hasDerivAt_insertNth i z (x i))
  have hrealCast := hreal.ofReal_comp
  have hderiv :
      fderiv ℝ (realToComplex f) (i.insertNth (x i) z) (basisVec i) =
        (fderiv ℝ f (i.insertNth (x i) z) (basisVec i) : ℂ) := by
    calc
      _ = deriv (fun t => realToComplex f (i.insertNth t z)) (x i) := hcomplex.deriv.symm
      _ = (fderiv ℝ f (i.insertNth (x i) z) (basisVec i) : ℂ) := hrealCast.deriv
  rw [hx] at hderiv
  simpa [coordDeriv, AVenhance.spaceGrad, realToComplex] using hderiv

theorem FrozenBridge.realToComplex_periodic {f : Vec 2 → ℝ}
    (hperiodic : AVenhance.IsZ2Periodic f) : IsZdPeriodic (realToComplex f) := by
  intro n x
  have h := (isZdPeriodic_iff_frozen f).2 hperiodic n x
  exact congrArg (fun y : ℝ => (y : ℂ)) h

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def FrozenBridge.closedUnitSquare : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem FrozenBridge.real_integrableOn_unitCell {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f (unitCell 2) := by
  have hcompact : IsCompact FrozenBridge.closedUnitSquare := by
    simpa [FrozenBridge.closedUnitSquare] using
      (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)
  have hsubset : unitCell 2 ⊆ FrozenBridge.closedUnitSquare := by
    intro x hx
    simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
    simp only [FrozenBridge.closedUnitSquare, Set.mem_pi]
    intro i _hi
    exact ⟨le_of_lt (hx i).1, (hx i).2⟩
  exact (hf.continuousOn.integrableOn_compact hcompact).mono_set hsubset

theorem FrozenBridge.realToComplex_meanZero {f : Vec 2 → ℝ} (hf : Continuous f)
    (hmean : ∫ x in AVenhance.unitCube, f x = 0) :
    ∫ x in unitCell 2, realToComplex f x = 0 := by
  have hcell : ∫ x in unitCell 2, f x = 0 := by
    rw [integral_unitCell_eq_unitCube]
    exact hmean
  have hmap : ∫ x in unitCell 2, (f x : ℂ) =
      (∫ x in unitCell 2, f x : ℝ) := by
    simpa using (Complex.ofRealCLM.integral_comp_comm
      (μ := (volume : Measure (Vec 2)).restrict (unitCell 2))
      (FrozenBridge.real_integrableOn_unitCell hf))
  exact hmap.trans (congrArg (fun y : ℝ => (y : ℂ)) hcell)

theorem FrozenBridge.realToComplex_energy {f : Vec 2 → ℝ} :
    (∫ x in unitCell 2, ‖realToComplex f x‖ ^ 2) = AVenhance.l2NormSq f := by
  calc
    (∫ x in unitCell 2, ‖realToComplex f x‖ ^ 2) =
        ∫ x in unitCell 2, f x ^ 2 := by
      apply setIntegral_congr_ae (measurableSet_unitCell 2)
      filter_upwards with x _hx
      simp [realToComplex]
    _ = ∫ x in AVenhance.unitCube, f x ^ 2 := integral_unitCell_eq_unitCube _
    _ = AVenhance.l2NormSq f := rfl

theorem FrozenBridge.realToComplex_gradient_energy {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) :
    (∫ x in unitCell 2,
      ∑ i : Fin 2, ‖coordDeriv i (realToComplex f) x‖ ^ 2) =
      AVenhance.gradNormSq (AVenhance.spaceGrad f) := by
  calc
    (∫ x in unitCell 2,
      ∑ i : Fin 2, ‖coordDeriv i (realToComplex f) x‖ ^ 2) =
        ∫ x in unitCell 2, Homogenization.vecNormSq (AVenhance.spaceGrad f x) := by
      apply setIntegral_congr_ae (measurableSet_unitCell 2)
      filter_upwards with x _hx
      simp [Homogenization.vecNormSq, Homogenization.vecDot,
        coordDeriv_realToComplex hf, pow_two]
    _ = ∫ x in AVenhance.unitCube, Homogenization.vecNormSq (AVenhance.spaceGrad f x) :=
      integral_unitCell_eq_unitCube _
    _ = AVenhance.gradNormSq (AVenhance.spaceGrad f) := rfl

/-- The real d = 2 scalar Parseval identity in the `l2NormSq` carrier. -/
theorem hasSum_sq_realToComplexFourierCoeff {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) :
    HasSum (fun k : Fin 2 → ℤ => ‖smoothFourierCoeff (realToComplex f) k‖ ^ 2)
      (AVenhance.l2NormSq f) := by
  rw [← FrozenBridge.realToComplex_energy]
  exact hasSum_sq_smoothFourierCoeff
    (Complex.ofRealCLM.contDiff.comp hf).continuous

/-- The real d = 2 gradient Parseval identity in the `gradNormSq` carrier. -/
theorem hasSum_sq_realToComplexGradientFourierCoeff {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) :
    HasSum
      (fun k : Fin 2 → ℤ =>
        ∑ i : Fin 2, ‖smoothFourierCoeff (coordDeriv i (realToComplex f)) k‖ ^ 2)
      (AVenhance.gradNormSq (AVenhance.spaceGrad f)) := by
  rw [← FrozenBridge.realToComplex_gradient_energy hf]
  convert hasSum_sq_smoothGradientFourierCoeff
    (f := realToComplex f) (Complex.ofRealCLM.contDiff.comp hf) using 1
  simpa [realToComplex] using (integral_unitCell_gradSq_eq_sum_coord
    (Complex.ofRealCLM.contDiff.comp hf)).symm

/-- Fourier multiplier formula for each component of the real gradient. -/
theorem smoothFourierCoeff_spaceGrad {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hperiodic : AVenhance.IsZ2Periodic f)
    (i : Fin 2) (k : Fin 2 → ℤ) :
    smoothFourierCoeff (fun x => (AVenhance.spaceGrad f x i : ℂ)) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) * smoothFourierCoeff (realToComplex f) k := by
  have hderiv : coordDeriv i (realToComplex f) =
      fun x => (AVenhance.spaceGrad f x i : ℂ) := by
    funext x
    exact coordDeriv_realToComplex hf i x
  rw [← hderiv]
  exact smoothFourierCoeff_coordDeriv i (Complex.ofRealCLM.contDiff.comp hf)
    (FrozenBridge.realToComplex_periodic hperiodic) k

/-- Mean-zero Poincare inequality in the d = 2 carriers. -/
theorem l2NormSq_le_fourierPoincare {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hperiodic : AVenhance.IsZ2Periodic f)
    (hmean : ∫ x in AVenhance.unitCube, f x = 0) :
    AVenhance.l2NormSq f ≤ (4 * Real.pi ^ 2)⁻¹ *
      AVenhance.gradNormSq (AVenhance.spaceGrad f) := by
  rw [← FrozenBridge.realToComplex_energy, ← FrozenBridge.realToComplex_gradient_energy hf]
  exact meanZero_smoothPeriodic_poincare
    (Complex.ofRealCLM.contDiff.comp hf) (FrozenBridge.realToComplex_periodic hperiodic)
    (FrozenBridge.realToComplex_meanZero hf.continuous hmean)

end AVenhance.Infra.Torus
