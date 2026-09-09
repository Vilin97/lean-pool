/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.RadialHeatProfile
public import LeanPool.NavierStokesAndEuler.NavierStokes.BorelExtension
public import LeanPool.NavierStokesAndEuler.NavierStokes.EndpointExtension

@[expose] public section

/-!
# A genuine smooth extension of the radial heat profile

For each fixed `a > 1`, the actual gamma-integral derivative kernels prescribe
all right jets at zero. A constructed Taylor--Borel series realizes precisely
these jets on the negative side. Gluing the two branches preserves the actual
heat profile on the entire nonnegative half-line and gives a globally smooth
function. No kernel formula at a negative argument is used.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.HeatProfileExtension

open RadialHeatProfile

/-- The actual right endpoint jets, as derived from the integral kernels. -/
noncomputable def endpointJet (a : ℝ) (n : ℕ) : ℝ := profileJet a n 0

theorem endpointJet_eq_gamma {a : ℝ} (ha : 1 < a) (n : ℕ) :
    endpointJet a n =
      (Real.Gamma a)⁻¹ * derivativeCoeff a n * Real.Gamma (a + (n : ℝ)) := by
  rw [endpointJet, profileJet, moment_zero ha]

theorem endpointJet_eq_right_derivative {a : ℝ} (ha : 1 < a) (n : ℕ) :
    endpointJet a n = iteratedDerivWithin n (profile a) (Ici 0) 0 :=
  (iteratedDerivWithin_profile ha n le_rfl).symm

theorem profileJet_continuousOn {a : ℝ} (ha : 1 < a) (n : ℕ) :
    ContinuousOn (profileJet a n) (Ici 0) :=
  continuousOn_const.mul (moment_continuousOn ha n)

/-- The negative branch is the actual compactly supported Borel series. -/
noncomputable def leftBranch (a : ℝ) : ℝ → ℝ := BorelExtension.extension (endpointJet a)

theorem leftBranch_contDiff (a : ℝ) : ContDiff ℝ ∞ (leftBranch a) :=
  BorelExtension.extension_contDiff (endpointJet a)

theorem leftBranch_jets (a : ℝ) (n : ℕ) :
    iteratedDeriv n (leftBranch a) 0 = endpointJet a n :=
  BorelExtension.extension_jets (endpointJet a) n

theorem leftBranch_left_jets (a : ℝ) (n : ℕ) :
    iteratedDerivWithin n (leftBranch a) (Iic 0) 0 = endpointJet a n := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Iic 0)
      ((leftBranch_contDiff a).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt (mem_Iic.mpr le_rfl)]
  exact leftBranch_jets a n

theorem leftBranch_zero (a : ℝ) : leftBranch a 0 = profile a 0 := by
  have h := leftBranch_jets a 0
  simpa only [iteratedDeriv_zero, endpointJet, profileJet, derivativeCoeff,
    mul_one, profile] using h

theorem matching_jets {a : ℝ} (ha : 1 < a) (n : ℕ) :
    iteratedDerivWithin n (leftBranch a) (Iic 0) 0 =
      iteratedDerivWithin n (profile a) (Ici 0) 0 := by
  rw [leftBranch_left_jets, ← endpointJet_eq_right_derivative ha]

/-- The globally defined extension. The original profile is used at every
positive argument, and matching zeroth jets preserve it at zero as well. -/
noncomputable def extension (a : ℝ) : ℝ → ℝ :=
  EndpointExtension.glue 0 (leftBranch a) (profile a)

theorem extension_contDiff {a : ℝ} (ha : 1 < a) : ContDiff ℝ ∞ (extension a) :=
  EndpointExtension.contDiff_glue (leftBranch_contDiff a).contDiffOn
    (profile_contDiffOn ha) (matching_jets ha)

theorem extension_eq_profile (a : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    extension a z = profile a z :=
  EndpointExtension.glue_eqOn_right (leftBranch_zero a) hz

theorem extension_eq_leftBranch (a : ℝ) {z : ℝ} (hz : z ≤ 0) :
    extension a z = leftBranch a z := EndpointExtension.glue_eq_left hz

theorem extension_zero {a : ℝ} (ha : 1 < a) : extension a 0 = 1 := by
  rw [extension_eq_profile a le_rfl, profile_zero ha]

/-- Ordinary derivatives of the smooth extension preserve every actual
one-sided profile derivative throughout the closed nonnegative half-line. -/
theorem iteratedDeriv_extension_eq_profileJet {a : ℝ} (ha : 1 < a)
    (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    iteratedDeriv n (extension a) z = profileJet a n z := by
  rw [extension, EndpointExtension.iteratedDeriv_glue
    (leftBranch_contDiff a).contDiffOn (profile_contDiffOn ha) (matching_jets ha)]
  exact (EndpointExtension.glue_eqOn_right (matching_jets ha n) hz).trans
    (iteratedDerivWithin_profile ha n hz)

theorem iteratedDeriv_extension_zero {a : ℝ} (ha : 1 < a) (n : ℕ) :
    iteratedDeriv n (extension a) 0 = endpointJet a n :=
  iteratedDeriv_extension_eq_profileJet ha n le_rfl

theorem extension_preserves_right_jets {a : ℝ} (ha : 1 < a) (n : ℕ) :
    iteratedDeriv n (extension a) 0 =
      iteratedDerivWithin n (profile a) (Ici 0) 0 :=
  (iteratedDeriv_extension_zero ha n).trans (endpointJet_eq_right_derivative ha n)

theorem extension_pos {a z : ℝ} (ha : 1 < a) (hz : 0 ≤ z) :
    0 < extension a z := by
  rw [extension_eq_profile a hz]
  exact profile_pos ha hz

theorem extension_zero_of_le_neg_one (a : ℝ) {z : ℝ} (hz : z ≤ -1) :
    extension a z = 0 := by
  rw [extension_eq_leftBranch a (by linarith)]
  exact BorelExtension.extension_zero_of_one_le_abs (endpointJet a)
    ((by linarith : (1 : ℝ) ≤ -z).trans (neg_le_abs z))

/-! ## Global fixed-order derivative bounds -/

/-- The convergent majorant from the actual Borel construction. -/
noncomputable def leftBound (a : ℝ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, BorelExtension.majorant (endpointJet a) n j

theorem leftBranch_derivative_bound (a : ℝ) (n : ℕ) (z : ℝ) :
    ‖iteratedDeriv n (leftBranch a) z‖ ≤ leftBound a n := by
  rw [leftBranch, BorelExtension.iteratedDeriv_extension]
  exact tsum_of_norm_bounded (BorelExtension.majorant_summable (endpointJet a) n).hasSum
    (fun j => BorelExtension.norm_iteratedDeriv_term_le_majorant (endpointJet a) n j z)

theorem leftBound_nonneg (a : ℝ) (n : ℕ) : 0 ≤ leftBound a n :=
  (norm_nonneg _).trans (leftBranch_derivative_bound a n 0)

/-- A finite bound at every fixed order, uniform over the entire real line. -/
noncomputable def derivativeBound (a : ℝ) (n : ℕ) : ℝ :=
  max (leftBound a n)
    (|(Real.Gamma a)⁻¹ * derivativeCoeff a n| * Real.Gamma (a + (n : ℝ)))

theorem derivativeBound_nonneg (a : ℝ) (n : ℕ) : 0 ≤ derivativeBound a n :=
  (leftBound_nonneg a n).trans (le_max_left _ _)

theorem extension_derivative_bound {a : ℝ} (ha : 1 < a) (n : ℕ) (z : ℝ) :
    ‖iteratedDeriv n (extension a) z‖ ≤ derivativeBound a n := by
  by_cases hz : 0 ≤ z
  · rw [iteratedDeriv_extension_eq_profileJet ha n hz,
      ← iteratedDerivWithin_profile ha n hz, Real.norm_eq_abs]
    exact (profile_derivative_bound ha n hz).trans (le_max_right _ _)
  · have hz' : z < 0 := lt_of_not_ge hz
    have heq : extension a =ᶠ[𝓝 z] leftBranch a := by
      filter_upwards [Iio_mem_nhds hz'] with y hy
      exact extension_eq_leftBranch a (show y < 0 from hy).le
    rw [heq.iteratedDeriv_eq]
    exact (leftBranch_derivative_bound a n z).trans (le_max_left _ _)

/-- The first-order error has a global linear bound, including negative
arguments. It is useful for domination of the extended tail integrals. -/
theorem extension_sub_one_bound {a : ℝ} (ha : 1 < a) (z : ℝ) :
    |extension a z - 1| ≤ derivativeBound a 1 * |z| := by
  have hc := (extension_contDiff ha).differentiable (by simp)
  have hb (y : ℝ) (_hy : y ∈ (univ : Set ℝ)) :
      ‖deriv (extension a) y‖ ≤ derivativeBound a 1 := by
    simpa only [iteratedDeriv_one] using extension_derivative_bound ha 1 y
  have hm := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun y _ => hc y) hb (mem_univ (0 : ℝ)) (mem_univ z)
  simpa only [extension_zero ha, sub_zero, Real.norm_eq_abs] using hm

/-- Positivity persists on a genuine two-sided neighborhood of the origin. -/
theorem extension_positive_near_zero {a : ℝ} (ha : 1 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, |z| < δ →
      (1 / 2 : ℝ) < extension a z ∧ extension a z < 3 / 2 := by
  have hev : ∀ᶠ z in 𝓝 (0 : ℝ), (1 / 2 : ℝ) < extension a z ∧ extension a z < 3 / 2 :=
    ((extension_contDiff ha).continuous.continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds (by rw [extension_zero ha]; norm_num)
        (by rw [extension_zero ha]; norm_num)))
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun z hz => hnear ?_⟩
  simpa only [Real.dist_eq, sub_zero] using hz

theorem extension_positive_on_collar {a : ℝ} (ha : 1 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, -δ < z → 0 < extension a z := by
  obtain ⟨δ, hδ, hnear⟩ := extension_positive_near_zero ha
  refine ⟨δ, hδ, fun z hz => ?_⟩
  by_cases hnonneg : 0 ≤ z
  · exact extension_pos ha hnonneg
  · have hz0 : z < 0 := lt_of_not_ge hnonneg
    have hsmall : |z| < δ := by rw [abs_of_neg hz0]; linarith
    exact lt_trans (by norm_num) (hnear z hsmall).1

/-! ## Physical parameter composition -/

/-- Diffusion-parametrized profile; negative diffusion uses only the Borel
extension, never the original gamma-integral expression. -/
noncomputable def scaledProfile (a X ν : ℝ) : ℝ := extension a (2 * ν / X)

theorem scaledProfile_contDiffOn {a : ℝ} (ha : 1 < a) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => scaledProfile a p.1 p.2)
      (Ioi 0 ×ˢ (univ : Set ℝ)) := by
  exact (extension_contDiff ha).comp_contDiffOn
    ((contDiffOn_const.mul contDiffOn_snd).div contDiffOn_fst
      (fun p hp => (show 0 < p.1 from hp.1).ne'))

theorem scaledProfile_eq_profile (a : ℝ) {X ν : ℝ} (hX : 0 < X) (hν : 0 ≤ ν) :
    scaledProfile a X ν = profile a (2 * ν / X) :=
  extension_eq_profile a (by positivity)

/-- Every ordinary diffusion derivative is an actual derivative of the
constructed smooth extension, including at and below zero diffusion. -/
theorem iteratedDeriv_scaledProfile {a : ℝ} (ha : 1 < a) (n : ℕ) (X ν : ℝ) :
    iteratedDeriv n (scaledProfile a X) ν =
      (2 / X) ^ n * iteratedDeriv n (extension a) (2 * ν / X) := by
  have heq : scaledProfile a X = fun u : ℝ => extension a ((2 / X) * u) := by
    funext u
    unfold scaledProfile
    congr 1
    ring
  rw [heq]
  have h := congrFun (iteratedDeriv_comp_const_mul
    ((extension_contDiff ha).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)) (2 / X)) ν
  simpa only [show 2 / X * ν = 2 * ν / X by ring] using h

theorem scaledProfile_derivative_bound {a X : ℝ} (ha : 1 < a) (hX : 0 < X)
    (n : ℕ) (ν : ℝ) :
    |iteratedDeriv n (scaledProfile a X) ν| ≤ (2 / X) ^ n * derivativeBound a n := by
  rw [iteratedDeriv_scaledProfile ha, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 / X) ^ n)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs] using extension_derivative_bound ha n (2 * ν / X))
    (by positivity)

/-- On a bounded diffusion set this supplies a uniform inverse-radius
majorant on either side of zero diffusion. -/
theorem scaledProfile_sub_one_bound {a : ℝ} (ha : 1 < a) {X : ℝ} (hX : 0 < X)
    (ν : ℝ) :
    |scaledProfile a X ν - 1| ≤ 2 * derivativeBound a 1 * |ν| / X := by
  calc
    _ ≤ derivativeBound a 1 * |2 * ν / X| := extension_sub_one_bound ha (2 * ν / X)
    _ = _ := by
      rw [abs_div, abs_mul, abs_of_pos hX, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring

noncomputable def physicalProfile (a X η : ℝ) : ℝ := scaledProfile a X (1 - η ^ 2)

/-- The physical profile now has an ordinary smooth neighborhood beyond
both endpoints `eta = ±1`, for every positive radius coordinate. -/
theorem physicalProfile_contDiffOn {a : ℝ} (ha : 1 < a) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => physicalProfile a p.1 p.2)
      (Ioi 0 ×ˢ (univ : Set ℝ)) := by
  exact (extension_contDiff ha).comp_contDiffOn
    ((contDiffOn_const.mul (contDiffOn_const.sub (contDiffOn_snd.pow 2))).div contDiffOn_fst
      (fun p hp => (show 0 < p.1 from hp.1).ne'))

theorem physicalProfile_eq_profile (a : ℝ) {X η : ℝ} (hX : 0 < X)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    physicalProfile a X η = profile a (2 * (1 - η ^ 2) / X) := by
  apply scaledProfile_eq_profile a hX
  have hp : 0 ≤ (η + 1) * (1 - η) := mul_nonneg (by linarith [hη.1]) (by linarith [hη.2])
  nlinarith

end NavierStokes.HeatProfileExtension
