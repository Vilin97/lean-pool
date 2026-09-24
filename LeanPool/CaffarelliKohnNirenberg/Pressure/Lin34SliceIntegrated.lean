/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceForceLp
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceQuantities

/-!
# Lin34 Slice Integrated

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

/-!
# `eq:lin34-pointwise` for a suitable weak solution, and its time integral

This file discharges, for a suitable weak solution, every hypothesis of the
integrated estimate `eq:lin35-force` of `prop:lin34`(ii-b) in `paper/ckn.tex`
except the Calderón--Zygmund bound `ext:CZ` for the centred first potential,
which stays named as `hCZ_p1`.
-/

private lemma lin34_euclideanBall_eq_vec3Ball_int {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

/-- **`eq:lin34-pointwise` at solution level.**  For a suitable weak solution
and a.e.\ time in `J_ρ`, the normalised inner pressure mass is controlled by the
velocity oscillation, the outer pressure mass, and the force group.  The only
named analytic input is `hCZ_p1`. -/
theorem lin34_slice_pointwise_bound_ae_of_sws
    (C₁₁ : ℝ) (hC₁₁ : 0 ≤ C₁₁)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (lin34CentredP1 u p f z.1 ρ hρ s)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
        lpNorm (lin34CentredP1 u p f z.1 ρ hρ s)
            (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
          C₁₁ * lin34VelocitySlice u z ρ s ^ (2 / 3 : ℝ)) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      r⁻¹ ^ 2 * lin34PressureSlice p z r s ≤
        lin34PointwiseConstant C₁₁ *
          ((ρ / r) ^ (2 : ℕ) * lin34G u z ρ s + (r / ρ) * lin34H p z ρ s +
            r⁻¹ ^ 2 * lin34ForceSliceIntegral f z ρ r hρ s) := by
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hpslices := sws_pressure_memLp_slice_ae hsol hρ hsub
  have hslices := ae_restrict_of_ae_restrict_of_subset htime
    (slice_memLp_ae_of_sws hsol hbox)
  have hVae := lin34_slice_integrableOn_ball_ae
    (lin34_integrableOn_meanFree_cube (u := u) (x := z.1) (t := z.2) (r := ρ)
      hρ (tsai_integrable_velocity_on_cylinder hsol hρ hsub)
      (tsai_integrable_velocity_cube_on_cylinder hsol hρ hsub))
  have hforceae := lin34_force_slice_memLp_ae hsol hρ hsub
  filter_upwards [hpslices, hslices, hVae, hforceae, hCZ_p1] with s hps hus
    hVs hfs hCZs
  have hu : MemLp (fun y : Vec3 => u (y, s)) 2
      (volume.restrict (vec3Ball z.1 ρ)) :=
    hus.1.mono_measure (Measure.restrict_mono_set volume hball)
  have humeas : AEMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball z.1 ρ)) := hu.aestronglyMeasurable.aemeasurable
  have hforce : MemLp (lin34ForcePart f z.1 ρ hρ s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball z.1 r)) := by
    have h := hfs z.1 r hr
    rwa [lin34_euclideanBall_eq_vec3Ball_int hr] at h
  exact lin34_slice_pointwise_bound hρ hr hhalf hC₁₁ hps hu humeas hVs hforce
    hCZs.1 hCZs.2

/-- The exponent constant `C₁₃` that makes the constant of `eq:lin35-force`
dominate the pointwise constant of `eq:lin34-pointwise`. -/
def lin34ForceExponent (C₁₁ : ℝ) : ℝ :=
  lin34PointwiseConstant C₁₁ ^ (2 / 3 : ℝ)

theorem lin34ForceExponent_nonneg {C₁₁ : ℝ} (hC₁₁ : 0 ≤ C₁₁) :
    0 ≤ lin34ForceExponent C₁₁ :=
  Real.rpow_nonneg (lin34PointwiseConstant_nonneg hC₁₁) _

theorem lin34_pointwiseConstant_le_forceConstant {C₁₁ : ℝ} (hC₁₁ : 0 ≤ C₁₁) :
    lin34PointwiseConstant C₁₁ ≤
      lin34ForceConstant (lin34ForceExponent C₁₁) := by
  have hP : 0 ≤ lin34PointwiseConstant C₁₁ := lin34PointwiseConstant_nonneg hC₁₁
  have hpow : lin34ForceExponent C₁₁ ^ (3 / 2 : ℝ) =
      lin34PointwiseConstant C₁₁ := by
    unfold lin34ForceExponent
    rw [← Real.rpow_mul hP]
    norm_num
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
    rwa [Real.sqrt_one] at h
  unfold lin34ForceConstant
  rw [hpow]
  calc
    lin34PointwiseConstant C₁₁ ≤ 1 * (1 + lin34PointwiseConstant C₁₁) := by
      linarith only [hP]
    _ ≤ Real.sqrt 2 * (1 + lin34PointwiseConstant C₁₁) :=
      mul_le_mul_of_nonneg_right hsqrt (by linarith only [hP])

private lemma lin34G_nonneg {u : ParabolicPoint → Vec3} {z : ParabolicPoint}
    {ρ : ℝ} (s : ℝ) : 0 ≤ lin34G u z ρ s := by
  refine mul_nonneg (by positivity) ?_
  exact integral_nonneg (fun y => pow_nonneg (vec3EuclideanNorm_nonneg _) 3)

private lemma lin34H_nonneg {p : ParabolicPoint → ℝ} {z : ParabolicPoint}
    {ρ : ℝ} (s : ℝ) : 0 ≤ lin34H p z ρ s := by
  refine mul_nonneg (by positivity) ?_
  exact integral_nonneg (fun y => by positivity)

private lemma lin34_force_slice_nonneg {f : ParabolicPoint → Vec3}
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    0 ≤ lin34ForceSliceIntegral f z ρ r hρ s :=
  integral_nonneg (fun x => by positivity)

/-- **The pointwise hypothesis of `eq:lin35-force`.**  The four time functions
`F, G, H, J` satisfy the pointwise inequality that the integrated estimate
consumes, for a.e. time in `J_ρ`. -/
theorem lin34_pointwise_bound_ae_of_sws
    (C₁₁ : ℝ) (hC₁₁ : 0 ≤ C₁₁)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (lin34CentredP1 u p f z.1 ρ hρ s)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
        lpNorm (lin34CentredP1 u p f z.1 ρ hρ s)
            (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
          C₁₁ * lin34VelocitySlice u z ρ s ^ (2 / 3 : ℝ)) :
    ∀ᵐ t ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      lin34F p z r t ≤ lin34ForceConstant (lin34ForceExponent C₁₁) *
        ((ρ / r) ^ 2 * lin34G u z ρ t + (r / ρ) * lin34H p z ρ t +
          lin34J f z ρ r hρ t) := by
  have hCle := lin34_pointwiseConstant_le_forceConstant hC₁₁
  have hC0 : 0 ≤ lin34ForceConstant (lin34ForceExponent C₁₁) :=
    le_trans (lin34PointwiseConstant_nonneg hC₁₁) hCle
  have hbase := lin34_slice_pointwise_bound_ae_of_sws C₁₁ hC₁₁ hsol hρ hr hhalf
    hsub hCZ_p1
  filter_upwards [hbase] with t ht
  have hG0 : 0 ≤ lin34G u z ρ t := lin34G_nonneg t
  have hH0 : 0 ≤ lin34H p z ρ t := lin34H_nonneg t
  have hX0 : 0 ≤ (ρ / r) ^ 2 * lin34G u z ρ t :=
    mul_nonneg (by positivity) hG0
  have hY0 : 0 ≤ (r / ρ) * lin34H p z ρ t :=
    mul_nonneg (by positivity) hH0
  by_cases hmem : t ∈ Ioc (z.2 - r ^ 2) z.2
  · have hZ0 : 0 ≤ r⁻¹ ^ 2 * lin34ForceSliceIntegral f z ρ r hρ t :=
      mul_nonneg (by positivity) (lin34_force_slice_nonneg hρ t)
    rw [lin34F, Set.indicator_of_mem hmem, lin34J, Set.indicator_of_mem hmem]
    refine ht.trans (mul_le_mul_of_nonneg_right hCle ?_)
    linarith only [hX0, hY0, hZ0]
  · rw [lin34F, Set.indicator_of_notMem hmem, lin34J,
      Set.indicator_of_notMem hmem]
    have hsum : 0 ≤ (ρ / r) ^ 2 * lin34G u z ρ t +
        (r / ρ) * lin34H p z ρ t + 0 := by
      linarith only [hX0, hY0]
    exact mul_nonneg hC0 hsum

/-- **The force hypothesis of `eq:lin35-force`.**  The time integral of the
force quantity carries the factor `(r/ρ)^{3/2}` of `prop:lin34`(ii-b). -/
theorem lin34J_integral_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    (∫ t, lin34J f z ρ r hρ t
        ∂(volume.restrict (Ioc (z.2 - ρ ^ 2) z.2))) ≤
      (r / ρ) ^ (3 / 2 : ℝ) *
        (lin34ForceCylinderConstant q * lambda q f z ρ) ^ (3 / 2 : ℝ) := by
  have hrρ : r ≤ ρ := by linarith only [hhalf, hρ]
  have hcyl := lin34_force_integrableOn_cylinder hsol hρ hr hhalf hsub
  have hlam : 0 ≤ lambda q f z ρ := by
    unfold lambda
    positivity
  have hCq : 0 ≤ lin34ForceCylinderConstant q :=
    lin34ForceCylinderConstant_nonneg q hsol.2.2.2.1
  have hCl : 0 ≤ lin34ForceCylinderConstant q * lambda q f z ρ :=
    mul_nonneg hCq hlam
  have hind : (∫ t, lin34J f z ρ r hρ t
      ∂(volume.restrict (Ioc (z.2 - ρ ^ 2) z.2))) =
      ∫ t in Ioc (z.2 - r ^ 2) z.2,
        r⁻¹ ^ 2 * lin34ForceSliceIntegral f z ρ r hρ t :=
    lin34_integral_indicator_subinterval (lin34_time_subset hr hrρ) _
  have hEq : (∫ t in Ioc (z.2 - r ^ 2) z.2,
      lin34ForceSliceIntegral f z ρ r hρ t) =
      ∫ w in parabolicCylinder z.1 z.2 r,
        |pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1| ^ (3 / 2 : ℝ) := by
    rw [integral_parabolicCylinder hcyl]
    rfl
  have hbnd := lin34_force_cylinder_integral_bound hsol hρ hr hhalf hsub
  rw [hind, integral_const_mul, hEq]
  calc
    r⁻¹ ^ 2 * ∫ w in parabolicCylinder z.1 z.2 r,
        |pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1| ^ (3 / 2 : ℝ) ≤
        r⁻¹ ^ 2 * (r ^ 2 * (lin34ForceCylinderConstant q *
          ((r / ρ) * lambda q f z ρ)) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ = (lin34ForceCylinderConstant q *
          ((r / ρ) * lambda q f z ρ)) ^ (3 / 2 : ℝ) := by
      field_simp
    _ = ((r / ρ) * (lin34ForceCylinderConstant q * lambda q f z ρ)) ^
          (3 / 2 : ℝ) := by ring_nf
    _ = (r / ρ) ^ (3 / 2 : ℝ) *
          (lin34ForceCylinderConstant q * lambda q f z ρ) ^ (3 / 2 : ℝ) :=
      Real.mul_rpow (by positivity) hCl

/-- **`eq:lin35-force` of `prop:lin34`(ii-b) for a suitable weak solution.**

The pressure quantity `D(z₀,r)` is bounded by the velocity oscillation
`C_hat(z₀,ρ)` with the factor `(ρ/r)²`, the pressure quantity `D(z₀,ρ)` with the
factor `r/ρ`, and the force quantity `λ(z₀,ρ)^{3/2}` with the factor
`(r/ρ)^{3/2}`.  The only named analytic input is the Calderón--Zygmund bound
`ext:CZ` for the centred first potential. -/
theorem pressure_lin34_force_of_sws
    (C₁₁ : ℝ) (hC₁₁ : 0 ≤ C₁₁)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (lin34CentredP1 u p f z.1 ρ hρ s)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
        lpNorm (lin34CentredP1 u p f z.1 ρ hρ s)
            (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
          C₁₁ * lin34VelocitySlice u z ρ s ^ (2 / 3 : ℝ)) :
    pressureD p z r ≤ lin34ForceConstant (lin34ForceExponent C₁₁) *
      ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ + (r / ρ) * pressureD p z ρ +
        (r / ρ) ^ (3 / 2 : ℝ) *
          (lin34ForceCylinderConstant q * lambda q f z ρ) ^ (3 / 2 : ℝ)) := by
  have hrρ : r ≤ ρ := by linarith only [hhalf, hρ]
  exact pressure_lin34_integrated_force
    (lin34ForceExponent_nonneg hC₁₁)
    (lin34F_integrable hsol hρ hr hrρ hsub)
    (lin34G_integrable hsol hρ hsub)
    (lin34H_integrable hsol hρ hsub)
    (lin34J_integrable hsol hρ hr hhalf hsub)
    (lin34_pointwise_bound_ae_of_sws C₁₁ hC₁₁ hsol hρ hr hhalf hsub hCZ_p1)
    (lin34J_integral_bound hsol hρ hr hhalf hsub)
    (lin34_pressureD_inner_eq_integral hsol hρ hr hrρ hsub)
    (lin34_pressureD_eq_integral hsol hρ hsub)
    (lin34_pressureChat_eq_integral hsol hρ hsub)

/-- The constant `C₃₂(q)` of `eq:lin35-force` in `paper/ckn.tex`, expressed
through the exponent that `lin34ForceConstant` consumes. -/
def lin34SolutionForceExponent (C₁₁ q : ℝ) : ℝ :=
  (lin34ForceConstant (lin34ForceExponent C₁₁) *
    (1 + lin34ForceCylinderConstant q ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ)

/-- **`eq:lin35-force` in the shape consumed by the scale iteration.**  The
force enters through `λ(z₀,ρ)^{3/2}` alone, the constant `C₁₃(q)` of
`lem:pk-bounds`(d)--(e) having been absorbed into `C₃₂`. -/
theorem pressure_lin34_force_lambda_of_sws
    (C₁₁ : ℝ) (hC₁₁ : 0 ≤ C₁₁)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (lin34CentredP1 u p f z.1 ρ hρ s)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
        lpNorm (lin34CentredP1 u p f z.1 ρ hρ s)
            (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
          C₁₁ * lin34VelocitySlice u z ρ s ^ (2 / 3 : ℝ)) :
    pressureD p z r ≤
      lin34ForceConstant (lin34SolutionForceExponent C₁₁ q) *
        ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ + (r / ρ) * pressureD p z ρ +
          (r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ)) := by
  have hbase := pressure_lin34_force_of_sws C₁₁ hC₁₁ hsol hρ hr hhalf hsub
    hCZ_p1
  have hE0 : 0 ≤ lin34ForceConstant (lin34ForceExponent C₁₁) :=
    le_trans (lin34PointwiseConstant_nonneg hC₁₁)
      (lin34_pointwiseConstant_le_forceConstant hC₁₁)
  have hCq : 0 ≤ lin34ForceCylinderConstant q :=
    lin34ForceCylinderConstant_nonneg q hsol.2.2.2.1
  have hCpow : 0 ≤ lin34ForceCylinderConstant q ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hCq _
  have hlam : 0 ≤ lambda q f z ρ := by
    unfold lambda
    positivity
  have hlampow : 0 ≤ lambda q f z ρ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlam _
  set M : ℝ := lin34ForceConstant (lin34ForceExponent C₁₁) *
    (1 + lin34ForceCylinderConstant q ^ (3 / 2 : ℝ)) with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg hE0 (by linarith only [hCpow])
  have hMforce : M ≤ lin34ForceConstant (lin34SolutionForceExponent C₁₁ q) := by
    have hpow : lin34SolutionForceExponent C₁₁ q ^ (3 / 2 : ℝ) = M := by
      rw [hMdef]
      unfold lin34SolutionForceExponent
      rw [← Real.rpow_mul (by rw [← hMdef]; exact hM0)]
      norm_num
    have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
      have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
      rwa [Real.sqrt_one] at h
    unfold lin34ForceConstant
    rw [hpow]
    calc
      M ≤ 1 * (1 + M) := by linarith only [hM0]
      _ ≤ Real.sqrt 2 * (1 + M) :=
        mul_le_mul_of_nonneg_right hsqrt (by linarith only [hM0])
  have hChat0 : 0 ≤ pressureChat u z ρ := by
    unfold pressureChat
    refine mul_nonneg (by positivity) ?_
    exact integral_nonneg (fun w => pow_nonneg (vec3EuclideanNorm_nonneg _) 3)
  have hD0 : 0 ≤ pressureD p z ρ := by
    unfold pressureD
    refine mul_nonneg (by positivity) ?_
    exact integral_nonneg (fun w => by positivity)
  have hX0 : 0 ≤ (ρ / r) ^ (2 : ℕ) * pressureChat u z ρ :=
    mul_nonneg (by positivity) hChat0
  have hY0 : 0 ≤ (r / ρ) * pressureD p z ρ :=
    mul_nonneg (by positivity) hD0
  have hZ0 : 0 ≤ (r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) hlampow
  have hsplit : (lin34ForceCylinderConstant q * lambda q f z ρ) ^ (3 / 2 : ℝ) =
      lin34ForceCylinderConstant q ^ (3 / 2 : ℝ) *
        lambda q f z ρ ^ (3 / 2 : ℝ) := Real.mul_rpow hCq hlam
  refine hbase.trans ?_
  rw [hsplit]
  have hstep : lin34ForceConstant (lin34ForceExponent C₁₁) *
      ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ + (r / ρ) * pressureD p z ρ +
        (r / ρ) ^ (3 / 2 : ℝ) *
          (lin34ForceCylinderConstant q ^ (3 / 2 : ℝ) *
            lambda q f z ρ ^ (3 / 2 : ℝ))) ≤
      M * ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ +
        (r / ρ) * pressureD p z ρ +
        (r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ)) := by
    have hEX : lin34ForceConstant (lin34ForceExponent C₁₁) ≤ M := by
      rw [hMdef]
      calc
        lin34ForceConstant (lin34ForceExponent C₁₁) =
            lin34ForceConstant (lin34ForceExponent C₁₁) * 1 := by ring
        _ ≤ lin34ForceConstant (lin34ForceExponent C₁₁) *
            (1 + lin34ForceCylinderConstant q ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hCpow]) hE0
    have hEZ : lin34ForceConstant (lin34ForceExponent C₁₁) *
        lin34ForceCylinderConstant q ^ (3 / 2 : ℝ) ≤ M := by
      rw [hMdef]
      exact mul_le_mul_of_nonneg_left (by linarith only [])
        hE0
    have hterm₁ := mul_le_mul_of_nonneg_right hEX hX0
    have hterm₂ := mul_le_mul_of_nonneg_right hEX hY0
    have hterm₃ := mul_le_mul_of_nonneg_right hEZ hZ0
    calc
      _ = lin34ForceConstant (lin34ForceExponent C₁₁) *
            ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ) +
          lin34ForceConstant (lin34ForceExponent C₁₁) *
            ((r / ρ) * pressureD p z ρ) +
          (lin34ForceConstant (lin34ForceExponent C₁₁) *
            lin34ForceCylinderConstant q ^ (3 / 2 : ℝ)) *
            ((r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ)) := by
        ring
      _ ≤ M * ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ) +
          M * ((r / ρ) * pressureD p z ρ) +
          M * ((r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ)) :=
        add_le_add (add_le_add hterm₁ hterm₂) hterm₃
      _ = _ := by ring
  refine hstep.trans ?_
  refine mul_le_mul_of_nonneg_right hMforce ?_
  linarith only [hX0, hY0, hZ0]

end CKN
