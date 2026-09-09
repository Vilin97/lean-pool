/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSmoothRepresentative
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet
import LeanPool.NavierStokesAndEuler.Euler.MeanGradientTestSpace

/-! Strong ordinary L² spatial derivatives are the classical derivatives of the reconstructed field.
-/

@[expose] public section


noncomputable section


namespace EulerMeanSmoothRepresentative

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerVectorCalculus
  EulerMeanGradientTest
open scoped ContDiff

theorem representative_pointwise_translation_hasDerivAt (u : EulerMeanSolenoidal.L2)
    (hu : SmoothOrbit u) (v x : Space) :
    HasDerivAt (fun t : ℝ => representative u hu (x+t•v))
      (fderiv ℝ (representative u hu) x v) 0 := by
  have H := ((representative_smooth u hu).differentiable (by simp) x).hasFDerivAt
  have ht : HasDerivAt (fun t : ℝ => x+t•v) v 0 := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
  simpa only [Function.comp_def] using H.comp_hasDerivAt_of_eq (0 : ℝ) ht (by simp)

/-- No prior L² integrability of the classical derivative is assumed. -/
theorem orbitDerivative_ae_fderiv (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (v : Space) :
    (orbitDerivative u v : Space → Space) =ᵐ[volume]
      fun x => fderiv ℝ (representative u hu) x v := by
  apply EulerStrongSmoothJet.lp_derivative_ae volume
    (fun t => EulerMeanSolenoidal.translation (t•v) u) (orbitDerivative u v)
    (fun t x => representative u hu (x+t•v))
    (fun x => fderiv ℝ (representative u hu) x v)
    _ (orbitDerivative_hasDerivAt u hu v) (representative_pointwise_translation_hasDerivAt u hu v)
  intro t
  filter_upwards [EulerMeanSolenoidal.translation_ae (t•v) u,
    (measurePreserving_add_right (volume : Measure Space) (t•v)).quasiMeasurePreserving.ae
      (representative_ae u hu)] with x h₁ h₂
  exact h₁.trans h₂

/-- The classical directional derivative is exactly the reconstructed strong derivative. -/
theorem fderiv_representative_apply (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (v x : Space)
    :
    fderiv ℝ (representative u hu) x v =
      representative (orbitDerivative u v) (orbitDerivative_smooth u hu v) x := by
  have H := representative_unique (orbitDerivative u v) (orbitDerivative_smooth u hu v)
    (fun y => fderiv ℝ (representative u hu) y v)
    (((representative_smooth u hu).fderiv_right (m := ∞) (by
        simp)).continuous.clm_apply continuous_const)
    (orbitDerivative_ae_fderiv u hu v)
  exact (congrFun H x).symm

theorem representative_directional_memLp (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (v :
    Space) :
    MemLp (fun x => fderiv ℝ (representative u hu) x v) 2 (volume : Measure Space) :=
  (Lp.memLp (orbitDerivative u v)).ae_eq (orbitDerivative_ae_fderiv u hu v)

/-- The full classical first derivative is genuinely square-integrable. -/
theorem representative_fderiv_memLp (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) :
    MemLp (fderiv ℝ (representative u hu)) 2 (volume : Measure Space) := by
  let f (i : Fin 3) (x : Space) := ‖fderiv ℝ (representative u hu) x (EuclideanSpace.single i 1)‖
  have hf (i : Fin 3) : MemLp (f i) 2 (volume : Measure Space) :=
    (representative_directional_memLp u hu (EuclideanSpace.single i 1)).norm
  have hs : MemLp (∑ i : Fin 3, f i) 2 (volume : Measure Space) :=
    memLp_finsetSum' Finset.univ (fun i _ => hf i)
  apply hs.mono'
    ((representative_smooth u hu).fderiv_right (m := ∞) (by simp)).continuous.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simpa only [Finset.sum_apply, f] using opNorm_le_sum_columns (fderiv ℝ (representative u hu) x)

end EulerMeanSmoothRepresentative
