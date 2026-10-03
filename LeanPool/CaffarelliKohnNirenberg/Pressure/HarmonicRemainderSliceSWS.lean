/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicRemainderSlice
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicRemainderForceTerms

/-!
# Harmonic Remainder Slice SWS

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
open CKN.Foundation.Euclidean

noncomputable section

namespace CKN

private theorem harmonic_remainder_vec3_norm_add_le (v w : Vec3) :
    vec3EuclideanNorm (v + w) ≤ vec3EuclideanNorm v + vec3EuclideanNorm w := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

/-- Nonnegative growth coefficient for the forcing part of the harmonic pressure remainder. -/
@[expose]
def harmonicRemainderForceBound (z : ParabolicPoint) {ρ : ℝ}
    (hρ : 0 < ρ) (f : ParabolicPoint → Vec3) (s : ℝ) : ℝ :=
  max
    ((pressureP7GrowthConstant (mollifiedBallCutoff z.1 hρ) f s
        (vec3EuclideanNorm z.1 + ρ) +
      pressureP8GrowthConstant (mollifiedBallCutoff z.1 hρ) f s
        (vec3EuclideanNorm z.1 + ρ)) *
      (1 + vec3EuclideanNorm z.1 + ρ)) 0

private theorem harmonic_remainder_inner_ball_subset_origin
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ) :
    euclideanBall z.1 (13 * ρ / 20) ⊆
      euclideanBall (0 : Vec3) (vec3EuclideanNorm z.1 + ρ) := by
  intro x hx
  have hR : 0 < vec3EuclideanNorm z.1 + ρ := by
    linarith only [vec3EuclideanNorm_nonneg z.1, hρ]
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
  have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  have hx'' : vec3EuclideanNorm (x - z.1) < 13 * ρ / 20 := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      using hx'
  have htri : vec3EuclideanNorm x ≤
      vec3EuclideanNorm (x - z.1) + vec3EuclideanNorm z.1 := by
    calc
      vec3EuclideanNorm x = vec3EuclideanNorm ((x - z.1) + z.1) := by
        congr 1
        abel
      _ ≤ vec3EuclideanNorm (x - z.1) + vec3EuclideanNorm z.1 :=
        harmonic_remainder_vec3_norm_add_le _ _
  have hnorm0 : vecEuclideanNorm (x - 0) = vec3EuclideanNorm x := by
    simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
  rw [hnorm0]
  exact htri.trans_lt (by linarith only [hx'', hρ])

private theorem harmonic_remainder_force_bound_nonneg_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      0 ≤ harmonicRemainderForceBound z hρ f s := by
  have hproducer := pressure_force_memLp_and_lpNorm_growth_ae_of_sws
    hsol hρ hsub
  filter_upwards [hproducer] with s hs
  exact le_max_right _ _

/- The force producer supplies the exact inner-ball hypothesis consumed by the
gradient estimate; the radius in the bound is the origin-ball radius used by
the Liouville growth estimate. -/
theorem pressure_force_inner_memLp_and_lpNorm_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ∧
      0 ≤ harmonicRemainderForceBound z hρ f s ∧
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤
        harmonicRemainderForceBound z hρ f s := by
  have hproducer := pressure_force_memLp_and_lpNorm_growth_ae_of_sws
    hsol hρ hsub
  have hnonneg := harmonic_remainder_force_bound_nonneg_ae_of_sws
    hsol hρ hsub
  filter_upwards [hproducer, hnonneg] with s hs hsnonneg
  have hR : 0 < vec3EuclideanNorm z.1 + ρ := by
    linarith only [vec3EuclideanNorm_nonneg z.1, hρ]
  have hinner := harmonic_remainder_inner_ball_subset_origin (z := z) hρ
  have hmem := hs.1 (vec3EuclideanNorm z.1 + ρ) hR
  have hmem' := hmem.mono_measure
    (Measure.restrict_mono_set volume hinner)
  have hnorm : lpNorm
      (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3)
        (vec3EuclideanNorm z.1 + ρ))) := by
    rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
    exact ENNReal.toReal_mono hmem.eLpNorm_lt_top.ne
      (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hinner))
  refine ⟨hmem', hsnonneg, ?_⟩
  calc
    lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3)
          (vec3EuclideanNorm z.1 + ρ))) := hnorm
    _ ≤ (pressureP7GrowthConstant (mollifiedBallCutoff z.1 hρ) f s
          (vec3EuclideanNorm z.1 + ρ) +
        pressureP8GrowthConstant (mollifiedBallCutoff z.1 hρ) f s
          (vec3EuclideanNorm z.1 + ρ)) *
        (1 + vec3EuclideanNorm z.1 + ρ) := by
      simpa only [add_assoc] using hs.2.2 (vec3EuclideanNorm z.1 + ρ) hR
    _ ≤ harmonicRemainderForceBound z hρ f s := by
      exact le_max_left _ _

end CKN
