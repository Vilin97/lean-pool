/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceForceEnvelope
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserTimeBounds

/-!
# Time integrability of the harmonic force envelope

The fixed-radius force contribution in `eq:pressure-gradient-morrey` has a
measurable, finite, locally time-integrable norm envelope from `def:sws`.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- The fixed-radius Newtonian coefficients are finite. -/
theorem origin_newtonian_coefficients_lt_top {R : ℝ} (hR : 0 < R) :
    originNewtonianCoefficient R < ⊤ ∧
      ∀ i : Fin 3, originNewtonianDerivativeCoefficient R i < ⊤ := by
  have hvol : volume (closedBall (0 : Vec3) R) ^ (1 / 6 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (isCompact_closedBall (0 : Vec3) R).measure_lt_top.ne
  constructor
  · exact ENNReal.add_lt_top.mpr ⟨
      (truncatedNewtonianPotentialKernel_memLp (by positivity : 0 < R + 2 * R)
        (by norm_num : (0 : ℝ) < 6 / 5) (by norm_num)).eLpNorm_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol⟩
  · intro i
    exact ENNReal.add_lt_top.mpr ⟨
      (truncatedNewtonianDerivative_memLp (by positivity : 0 < R + 2 * R) i).eLpNorm_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol⟩

/-- Suitability gives the force envelope's measurability, a.e. finiteness,
and time integrability on any interior origin ball-times-window box. -/
theorem origin_force_envelope_obligations_on_local_box
    {Ω : Set Vec3} {I J : Set ℝ} {q R : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hR : 0 < R)
    (hbox : localBox Ω I (vec3Ball 0 R) J) :
    AEMeasurable (originForceGrowthEnvelope R f) (volume.restrict J) ∧
      (∀ᵐ s ∂volume.restrict J, originForceGrowthEnvelope R f s ≠ ⊤) ∧
      Integrable (fun s => (originForceGrowthEnvelope R f s).toReal) (volume.restrict J) := by
  let N := fun (j : Fin 3) s => eLpNorm (fun y => f (y, s) j)
    (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball 0 R))
  let A := fun j => originNewtonianDerivativeCoefficient R j +
    ENNReal.ofReal (cutoffGradientConstant / R) * originNewtonianCoefficient R
  have hNm (j : Fin 3) : AEMeasurable (N j) (volume.restrict J) := by
    have hf := (hsol.2.2.2.2.1 (vec3Ball 0 R) J hbox j).aestronglyMeasurable
    exact origin_time_slice_norm_aemeasurable (by norm_num) hf.aemeasurable
  have hNint (j : Fin 3) : (∫⁻ s in J, N j s) < ⊤ :=
    lintegral_force_slice_eLpNorm_lt_top_of_sws hsol hbox j
  have hA (j : Fin 3) : A j < ⊤ := ENNReal.add_lt_top.mpr
    ⟨(origin_newtonian_coefficients_lt_top hR).2 j,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (origin_newtonian_coefficients_lt_top hR).1⟩
  have hjm (j : Fin 3) : AEMeasurable (fun s => A j * N j s) (volume.restrict J) :=
    aemeasurable_const.mul (hNm j)
  have hsm : AEMeasurable (fun s => ∑ j : Fin 3, A j * N j s) (volume.restrict J) := by
    simpa only [Finset.sum_fn] using Finset.aemeasurable_sum Finset.univ (fun j _ => hjm j)
  have hm : AEMeasurable (originForceGrowthEnvelope R f) (volume.restrict J) :=
    aemeasurable_const.mul hsm
  have hfin : (∫⁻ s in J, originForceGrowthEnvelope R f s) < ⊤ := by
    change (∫⁻ s in J, ENNReal.ofReal (1 + R) * ∑ j : Fin 3, A j * N j s) < ⊤
    rw [lintegral_const_mul'' _ hsm, lintegral_finsetSum' _ (fun j _ => hjm j)]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    apply ENNReal.sum_lt_top.mpr
    intro j _
    rw [lintegral_const_mul'' _ (hNm j)]
    exact ENNReal.mul_lt_top (hA j) (hNint j)
  exact ⟨hm, (ae_lt_top' hm hfin.ne).mono (fun _ h => h.ne),
    integrable_toReal_of_lintegral_ne_top hm hfin.ne⟩

end CKN.Core.Step4
