/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceForceEnvelope
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserTimeBounds

/-!
# Measurability of time-dependent force potentials

Spatial integration against a measurable kernel preserves measurability
of the potential norm in time. This applies to the force-growth constants
in `eq:pressure-gradient-morrey` without assuming temporal regularity.
-/

@[expose] public section

section

/-!
# The harmonic force bound on interior time boxes

The force term in `eq:pressure-gradient-morrey` is controlled almost
everywhere by its measurable fixed-radius envelope on any local time box.
-/

section

/-!
# Time integrability of the harmonic force envelope

The fixed-radius force contribution in `eq:pressure-gradient-morrey` has a
measurable, finite, locally time-integrable norm envelope from `def:sws`.
-/

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
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (isCompact_closedBall (0 : Vec3)
      R).measure_lt_top.ne
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
end

end

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The force components lie in spatial `L^{6/5}` almost everywhere on an
arbitrary suitable-solution local box. -/
theorem origin_force_components_memLp_ae_on_local_box
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hbox : localBox Ω I B J) :
    ∀ᵐ s ∂volume.restrict J, ∀ j : Fin 3,
      MemLp (fun y => f (y, s) j) (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) := by
  apply ae_all_iff.mpr
  intro j
  have hm := origin_time_slice_norm_aemeasurable (by norm_num : (0 : ℝ) < 6 / 5)
    (hsol.2.2.2.2.1 B J hbox j).aestronglyMeasurable.aemeasurable
  have ht := lintegral_force_slice_eLpNorm_lt_top_of_sws hsol hbox j
  filter_upwards [ae_lt_top' hm ht.ne] with s hs
  exact memLp_iff.mpr hs

/-- The actual harmonic force constant is bounded a.e. by the force envelope
on any interior origin ball-times-window box. -/
theorem origin_harmonic_force_le_envelope_on_local_box
    {Ω : Set Vec3} {I J : Set ℝ} {q R : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hR : 0 < R)
    (hbox : localBox Ω I (vec3Ball 0 R) J) :
    ∀ᵐ s ∂volume.restrict J,
      ENNReal.ofReal (harmonicRemainderForceBound ((0 : Vec3), 0) hR f s) ≤
        originForceGrowthEnvelope R f s := by
  filter_upwards [origin_force_components_memLp_ae_on_local_box hsol hbox] with s hs
  exact origin_harmonic_force_le_envelope hR s hs

end CKN.Core.Step4
end

end

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- The spatial norm of a time-dependent convolution is measurable in time. -/
theorem origin_convolution_norm_time_aemeasurable
    {G : Vec3 × ℝ → ℝ} {J : Set ℝ} {k : Vec3 → ℝ}
    (hG : AEStronglyMeasurable G ((volume : Measure Vec3).prod (volume.restrict J)))
    (hk : Measurable k) {P : ℝ} (hP : 0 < P) (B : Set Vec3) :
    AEMeasurable (fun s => eLpNorm (fun x => ∫ y, k (x - y) * G (y, s))
      (ENNReal.ofReal P) (volume.restrict B)) (volume.restrict J) := by
  let G' := hG.mk G
  have hG'm : Measurable G' := hG.stronglyMeasurable_mk.measurable
  have hpot : Measurable (fun w : Vec3 × ℝ => ∫ y, k (w.1 - y) * G' (y, w.2)) := by
    have hm : Measurable (fun v : (Vec3 × ℝ) × Vec3 =>
        k (v.1.1 - v.2) * G' (v.2, v.1.2)) :=
      (hk.comp (measurable_fst.fst.sub measurable_snd)).mul
        (hG'm.comp (measurable_snd.prodMk measurable_fst.snd))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hn := origin_time_slice_norm_aemeasurable hP hpot.aemeasurable.restrict (E := B) (J := J)
  apply hn.congr
  filter_upwards [ae_ae_of_ae_prod_snd hG.ae_eq_mk] with s hs
  apply eLpNorm_congr_ae
  exact Eventually.of_forall fun x => integral_congr_ae
    (hs.mono fun y hy => congrArg (fun a => k (x - y) * a) hy.symm)

/-- Both Newtonian force-growth constants are measurable functions of time
for a jointly measurable source supported on the full spatial space. -/
theorem origin_force_growth_constants_time_aemeasurable
    {G : Vec3 × ℝ → ℝ} {J : Set ℝ}
    (hG : AEStronglyMeasurable G ((volume : Measure Vec3).prod (volume.restrict J)))
    (R : ℝ) :
    AEMeasurable (fun s => newtonianPotentialGrowthConstant (fun y => G (y, s)) R)
      (volume.restrict J) ∧
      ∀ i : Fin 3, AEMeasurable
        (fun s => newtonianDerivativePotentialGrowthConstant i (fun y => G (y, s)) R)
        (volume.restrict J) := by
  have hmass : AEMeasurable (fun s => ∫ y, |G (y, s)|) (volume.restrict J) :=
    hG.norm.prod_swap.integral_prod_right'.aemeasurable
  have hk : Measurable (fun x : Vec3 => -newtonianKernel x) := by
    unfold newtonianKernel vec3EuclideanNorm
    fun_prop
  have hd (i : Fin 3) : Measurable (spatialDeriv newtonianKernel i) :=
    measurable_fderiv_apply_const ℝ newtonianKernel (basisVec i)
  have hp := origin_convolution_norm_time_aemeasurable hG hk (by norm_num : (0 : ℝ) < 3 / 2)
    (ball (0 : Vec3) (2 * R))
  have hdp (i : Fin 3) := origin_convolution_norm_time_aemeasurable hG (hd i)
    (by norm_num : (0 : ℝ) < 3 / 2) (ball (0 : Vec3) (2 * R))
  constructor
  · unfold newtonianPotentialGrowthConstant invNormGrowthConstant
    simp_rw [← toReal_eLpNorm]
    exact hp.ennreal_toReal.add ((aemeasurable_const.mul hmass).mul_const _)
  · intro i
    unfold newtonianDerivativePotentialGrowthConstant invNormGrowthConstant
    simp_rw [← toReal_eLpNorm]
    exact (hdp i).ennreal_toReal.add (((aemeasurable_const.mul hmass).div_const _).mul_const _)

end CKN.Core.Step4
