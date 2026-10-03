/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.IndyStepDownPartI
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectCoefficient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.KappaProduct

/-! The first-order instance of the initial trace estimate: the coordinate trace bound gives
the gradient input of the initial-layer estimate. The trace bound itself is proved in
`TraceInstanceContract`. No undifferentiated temperature norm enters the corrector bound. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section5.RelativeError
open AVenhance AVenhance.Infra.Section5.Integration AVenhance.Infra.Section5.LeftToShow

/-- Coordinate n=1 trace implies the vector-gradient input of the initial-layer estimate. -/
theorem relative_initial_gradient_of_trace {g : Vec 2 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {C r S : ℝ}
    (hr : 0 < r) (hS : 0 ≤ S)
    (hTraceOne : ∀ i : Fin 2, Real.sqrt (l2NormSq (fun x => spaceGrad g x i)) ≤
      C * ((1 : ℕ).factorial : ℝ) * (C / r) ^ (1 : ℕ) * S) :
    Real.sqrt (gradNormSq (spaceGrad g)) ≤ (2 * C ^ 2) * S / r := by
  let G := C ^ 2 * S / r
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hb (i : Fin 2) : Real.sqrt (l2NormSq (fun x => spaceGrad g x i)) ≤ G := by
    convert hTraceOne i using 1
    simp only [Nat.factorial_one, Nat.cast_one, mul_one, pow_one]
    dsimp [G]
    ring
  have hi (i : Fin 2) : IntegrableOn (fun x => (spaceGrad g x i) ^ 2) unitCube :=
    integrableOn_unitCube_of_continuous
      (((hg.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2)
  have he : gradNormSq (spaceGrad g) =
      l2NormSq (fun x => spaceGrad g x 0) + l2NormSq (fun x => spaceGrad g x 1) := by
    unfold gradNormSq vecNormSq vecDot l2NormSq
    simp only [Fin.sum_univ_two, ← pow_two]
    exact integral_add (hi 0) (hi 1)
  have hnonneg (i : Fin 2) : 0 ≤ l2NormSq (fun x => spaceGrad g x i) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hs (i : Fin 2) : l2NormSq (fun x => spaceGrad g x i) ≤ G ^ 2 := by
    have hh := sq_le_sq₀ (Real.sqrt_nonneg _) hG |>.mpr (hb i)
    rwa [Real.sq_sqrt (hnonneg i)] at hh
  have hsum : gradNormSq (spaceGrad g) ≤ (2 * G) ^ 2 := by
    rw [he]
    nlinarith only [hs 0, hs 1, sq_nonneg G]
  have hh := Real.sqrt_le_sqrt hsum
  rw [Real.sqrt_sq (by positivity : 0 ≤ 2 * G)] at hh
  convert hh using 1
  dsimp [G]
  ring

end AVenhance.Infra.Section5.RelativeError
