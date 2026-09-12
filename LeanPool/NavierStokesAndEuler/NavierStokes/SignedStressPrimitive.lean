/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.IntegratedMeanBalances
import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricKernelBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformCone
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The actual compact signed-stress primitive

A positive normalized bump is constructed in a chosen interior slow patch.
Subtracting its exact weighted moment makes the negative radial primitive
compact. The physical construction is normalized by the physical scale.
-/

@[expose] public section


noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokes.SignedStressPrimitive

private theorem nat_le_smooth (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

/-- Patch data, collecting `a`, `b`, `left`, `right`, `a_pos`, `a_lt_left` and their
compatibility conditions. -/
structure Patch where
  /-- A of `Patch`, of type `ℝ`. -/
  a : ℝ
  /-- B of `Patch`, of type `ℝ`. -/
  b : ℝ
  /-- Left of `Patch`, of type `ℝ`. -/
  left : ℝ
  /-- Right of `Patch`, of type `ℝ`. -/
  right : ℝ
  a_pos : 0 < a
  a_lt_left : a < left
  left_lt_right : left < right
  right_lt_b : right < b

theorem Patch.a_lt_b (P : Patch) : P.a < P.b :=
  P.a_lt_left.trans (P.left_lt_right.trans P.right_lt_b)

theorem Patch.left_pos (P : Patch) : 0 < P.left := P.a_pos.trans P.a_lt_left

/-- Density, given by `PressureStream.rho P.left P.right P.left_lt_right`. -/
noncomputable def density (P : Patch) : ℝ → ℝ :=
  PressureStream.rho P.left P.right P.left_lt_right

theorem density_contDiff (P : Patch) : ContDiff ℝ ∞ (density P) :=
  PressureStream.rho_contDiff _ _ _

theorem density_support (P : Patch) : support (density P) ⊆ Icc P.left P.right :=
  PressureStream.rho_support _ _ _

theorem density_integral (P : Patch) : (∫ r, density P r) = 1 := PressureStream.rho_integral _ _ _

theorem density_nonneg (P : Patch) (r : ℝ) : 0 ≤ density P r := PressureStream.rho_nonneg _ _ _ r

/-- Density lift, given by `density P z.1`. -/
noncomputable def densityLift (P : Patch) (z : ℝ × ℝ) : ℝ := density P z.1

theorem densityLift_contDiff (P : Patch) : ContDiff ℝ ∞ (densityLift P) :=
  (density_contDiff P).comp contDiff_fst

theorem densityLift_supported (P : Patch) :
    RadialAlias.RadiallySupported P.left P.right (densityLift P) :=
  fun _ h => density_support P h

/-- Cutoff, given by `TransportPrimitive.pastIntegral 0 (0 : ℝ) (densityLift P) (r, 0)`. -/
noncomputable def cutoff (P : Patch) (r : ℝ) : ℝ :=
  TransportPrimitive.pastIntegral 0 (0 : ℝ) (densityLift P) (r, 0)

theorem cutoff_contDiff (P : Patch) : ContDiff ℝ ∞ (cutoff P) :=
  (TransportPrimitive.pastIntegral_contDiff (densityLift_contDiff P) (densityLift_supported P)).comp
    (contDiff_id.prodMk contDiff_const)

theorem cutoff_total (P : Patch) (r : ℝ) :
    TransportPrimitive.totalIntegral 0 (0 : ℝ) (densityLift P) (r, 0) = 1 := by
  rw [TransportPrimitive.totalIntegral_eq_radialInterval
    (densityLift_contDiff P).continuous (densityLift_supported P)]
  simp only [densityLift]
  have h := IntegratedMeanBalances.radialMoment_eq_interval
    (densityLift_contDiff P).continuous (densityLift_supported P) 0 0
  simp only [IntegratedMeanBalances.radialMoment, IntegratedMeanBalances.moment,
    densityLift, pow_zero, one_mul, density_integral] at h
  exact h.symm

theorem cutoff_zero (P : Patch) {r : ℝ} (hr : r ≤ P.left) : cutoff P r = 0 :=
  TransportPrimitive.pastIntegral_eq_zero_of_le
    (densityLift_contDiff P).continuous (densityLift_supported P) (r, 0) hr

theorem cutoff_one (P : Patch) {r : ℝ} (hr : P.right ≤ r) : cutoff P r = 1 := by
  change TransportPrimitive.pastIntegral 0 (0 : ℝ) (densityLift P) (r, 0) = 1
  rw [TransportPrimitive.pastIntegral_eq_total_of_ge (densityLift_supported P) (r, 0) hr,
    cutoff_total]

theorem cutoff_hasDerivAt (P : Patch) (r : ℝ) : HasDerivAt (cutoff P) (density P r) r := by
  have hs := TransportPrimitive.pastIntegral_contDiff (M := 0) (v := (0 : ℝ))
    (densityLift_contDiff P) (densityLift_supported P)
  have hd := ((hs.differentiable (by simp)) (r, 0)).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r (0 : ℝ)))
  have ht := TransportPrimitive.transport_pastIntegral (M := 0) (v := (0 : ℝ))
    (densityLift_contDiff P) (densityLift_supported P) (r, 0)
  simp only [TransportPrimitive.fixedDeriv, zero_smul, densityLift] at ht
  unfold cutoff
  simpa only [ht, Function.comp_def, id_eq] using hd

theorem cutoff_deriv (P : Patch) (r : ℝ) : deriv (cutoff P) r = density P r :=
  (cutoff_hasDerivAt P r).deriv

/-- Inverse power, given by `((RadialPullback.positiveRadius (P.a / 4) r) ^ e)⁻¹`. -/
noncomputable def inversePower (P : Patch) (e : ℕ) (r : ℝ) : ℝ :=
  ((RadialPullback.positiveRadius (P.a / 4) r) ^ e)⁻¹

theorem inversePower_contDiff (P : Patch) (e : ℕ) : ContDiff ℝ ∞ (inversePower P e) :=
  ((RadialPullback.positiveRadius_contDiff _).pow e).inv
    (fun r => pow_ne_zero _ (RadialPullback.positiveRadius_pos (by linarith [P.a_pos]) r).ne')

theorem inversePower_nonneg (P : Patch) (e : ℕ) (r : ℝ) : 0 ≤ inversePower P e r :=
  inv_nonneg.mpr (pow_nonneg (RadialPullback.positiveRadius_pos (by linarith [P.a_pos]) r).le e)

theorem inversePower_eq (P : Patch) (e : ℕ) {r : ℝ} (hr : P.a ≤ r) :
    inversePower P e r = (r ^ e)⁻¹ := by
  unfold inversePower
  rw [RadialPullback.positiveRadius_eq_self (by linarith [P.a_pos]) (by linarith [P.a_pos])]

/-- Moment density, given by `inversePower P e r * density P r`. -/
noncomputable def momentDensity (P : Patch) (e : ℕ) (r : ℝ) : ℝ := inversePower P e r * density P r

theorem momentDensity_contDiff (P : Patch) (e : ℕ) : ContDiff ℝ ∞ (momentDensity P e) :=
  (inversePower_contDiff P e).mul (density_contDiff P)

theorem momentDensity_nonneg (P : Patch) (e : ℕ) (r : ℝ) : 0 ≤ momentDensity P e r :=
  mul_nonneg (inversePower_nonneg P e r) (density_nonneg P r)

theorem momentDensity_support (P : Patch) (e : ℕ) : support (momentDensity P e) ⊆ Icc P.left
    P.right :=
  fun _ h => density_support P (right_ne_zero_of_mul h)

theorem weighted_momentDensity (P : Patch) (e : ℕ) (r : ℝ) :
    r ^ e * momentDensity P e r = density P r := by
  by_cases h : density P r = 0
  · simp [momentDensity, h]
  have hr := density_support P h
  have hr0 : 0 < r := P.left_pos.trans_le hr.1
  rw [momentDensity, inversePower_eq P e (P.a_lt_left.le.trans hr.1)]
  field_simp [hr0.ne']

theorem momentDensity_moment (P : Patch) (e : ℕ) : (∫ r, r ^ e * momentDensity P e r) = 1 := by
  simp_rw [weighted_momentDensity]
  exact density_integral P

theorem momentDensity_positive_moment (P : Patch) (e : ℕ) :
    (∫ r in Ioi (0 : ℝ), r ^ e * momentDensity P e r) = 1 := by
  rw [IntegratedMeanBalances.positive_integral_eq_integral P.left_pos]
  · exact momentDensity_moment P e
  · intro r hr
    exact momentDensity_support P e (right_ne_zero_of_mul hr)

theorem momentDensity_tsupport (P : Patch) (e : ℕ) : tsupport (momentDensity P e) ⊆ Ioo P.a P.b :=
    by
  intro r hr
  have h := closure_minimal (momentDensity_support P e) isClosed_Icc hr
  exact ⟨P.a_lt_left.trans_le h.1, h.2.trans_lt P.right_lt_b⟩

section Primitive

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weighted source, given by `z.1 ^ e * F z`. -/
noncomputable def weightedSource (e : ℕ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ := z.1 ^ e * F z
/-- Mass, given by `IntegratedMeanBalances.radialMoment e F`. -/
noncomputable def mass (e : ℕ) (F : ℝ × E → ℝ) : E → ℝ := IntegratedMeanBalances.radialMoment e F
/-- Bump correction, given by `momentDensity P e z.1 * mass e F z.2`. -/
noncomputable def bumpCorrection (P : Patch) (e : ℕ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  momentDensity P e z.1 * mass e F z.2
/-- Adjusted, given by `F z - bumpCorrection P e F z`. -/
noncomputable def adjusted (P : Patch) (e : ℕ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  F z - bumpCorrection P e F z
/-- Primitive, given by `TransportPrimitive.compactIntegral (cutoff P) 0 0 (weightedSource e
F)`. -/
noncomputable def primitive (P : Patch) (e : ℕ) (F : ℝ × E → ℝ) : ℝ × E → ℝ :=
  TransportPrimitive.compactIntegral (cutoff P) 0 0 (weightedSource e F)
/-- Sigma, given by `-inversePower P e z.1 * primitive P e F z`. -/
noncomputable def sigma (P : Patch) (e : ℕ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  -inversePower P e z.1 * primitive P e F z

theorem weightedSource_contDiff (e : ℕ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (weightedSource e F) := (contDiff_fst.pow e).mul hF

omit [NormedSpace ℝ E] in
theorem weightedSource_continuous (e : ℕ) {F : ℝ × E → ℝ} (hF : Continuous F) :
    Continuous (weightedSource e F) := (continuous_fst.pow e).mul hF

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weightedSource_supported (e : ℕ) {P : Patch} {F : ℝ × E → ℝ}
    (hF : RadialAlias.RadiallySupported P.a P.b F) :
    RadialAlias.RadiallySupported P.a P.b (weightedSource e F) :=
  fun _ h => hF (right_ne_zero_of_mul h)

theorem mass_contDiff {P : Patch} (e : ℕ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) : ContDiff ℝ ∞ (mass e F) :=
  IntegratedMeanBalances.radialMoment_smooth hF hs e

theorem bumpCorrection_contDiff (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) : ContDiff ℝ ∞ (bumpCorrection P e F) :=
  ((momentDensity_contDiff P e).comp contDiff_fst).mul ((mass_contDiff e hF hs).comp contDiff_snd)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem bumpCorrection_supported (P : Patch) (e : ℕ) (F : ℝ × E → ℝ) :
    RadialAlias.RadiallySupported P.left P.right (bumpCorrection P e F) :=
  fun _ h => momentDensity_support P e (left_ne_zero_of_mul h)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem bumpCorrection_moment (P : Patch) (e : ℕ) (F : ℝ × E → ℝ) (p : E) :
    mass e (bumpCorrection P e F) p = mass e F p := by
  change (∫ r, r ^ e * (momentDensity P e r * mass e F p)) = _
  simp_rw [← mul_assoc]
  rw [integral_mul_const, momentDensity_moment, one_mul]

theorem adjusted_contDiff (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) : ContDiff ℝ ∞ (adjusted P e F) :=
  hF.sub (bumpCorrection_contDiff P e hF hs)

theorem primitive_contDiff (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) : ContDiff ℝ ∞ (primitive P e F) :=
  TransportPrimitive.compactIntegral_contDiff (cutoff_contDiff P)
    (weightedSource_contDiff e hF) (weightedSource_supported e hs)

theorem primitive_supported (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : Continuous F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) :
    RadialAlias.RadiallySupported P.a P.b (primitive P e F) :=
  TransportPrimitive.compactIntegral_supported ((continuous_fst.pow e).mul hF)
    (weightedSource_supported e hs)
    (fun _ hr => cutoff_zero P (hr.trans P.a_lt_left.le))
    (fun _ hr => cutoff_one P (P.right_lt_b.le.trans hr))

theorem sigma_contDiff (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) : ContDiff ℝ ∞ (sigma P e F) :=
  (((inversePower_contDiff P e).comp contDiff_fst).neg).mul (primitive_contDiff P e hF hs)

theorem sigma_supported (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : Continuous F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) :
    RadialAlias.RadiallySupported P.a P.b (sigma P e F) :=
  fun _ h => primitive_supported P e hF hs (right_ne_zero_of_mul h)

theorem total_weightedSource (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : Continuous F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) (z : ℝ × E) :
    TransportPrimitive.totalIntegral 0 (0 : E) (weightedSource e F) z = mass e F z.2 := by
  rw [TransportPrimitive.totalIntegral_eq_radialInterval
    (weightedSource_continuous e hF) (weightedSource_supported e hs)]
  simp only [zero_mul, zero_smul, add_zero, weightedSource]
  exact (IntegratedMeanBalances.radialMoment_eq_interval hF hs e z.2).symm

theorem past_zero_eq_integral {a b : ℝ} (ha : 0 ≤ a) {F : ℝ × E → ℝ} (hF : Continuous F)
    (hs : RadialAlias.RadiallySupported a b F) (z : ℝ × E) :
    TransportPrimitive.pastIntegral 0 (0 : E) F z = ∫ r in (0 : ℝ)..z.1, F (r, z.2) := by
  have hs0 : RadialAlias.RadiallySupported 0 b F := fun y hy => ⟨ha.trans (hs hy).1, (hs hy).2⟩
  simpa only [zero_mul, zero_smul, add_zero] using
    TransportPrimitive.pastIntegral_eq_radialInterval (M := 0) (v := (0 : E)) hF hs0 z

theorem cutoff_eq_integral (P : Patch) (r : ℝ) : cutoff P r = ∫ s in (0 : ℝ)..r, density P s :=
  past_zero_eq_integral P.left_pos.le (densityLift_contDiff P).continuous (densityLift_supported P)
      (r, 0)

theorem primitive_eq_integral (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) (z : ℝ × E) :
    primitive P e F z = ∫ r in (0 : ℝ)..z.1, r ^ e * adjusted P e F (r, z.2) := by
  have hiF : IntervalIntegrable (fun r => r ^ e * F (r, z.2)) volume 0 z.1 :=
    ((continuous_id.pow e).mul (hF.continuous.comp (continuous_id.prodMk
        continuous_const))).intervalIntegrable _ _
  have hiD : IntervalIntegrable (fun r => density P r * mass e F z.2) volume 0 z.1 :=
    ((density_contDiff P).continuous.mul continuous_const).intervalIntegrable _ _
  have heq : (fun r => r ^ e * adjusted P e F (r, z.2)) =
      fun r => r ^ e * F (r, z.2) - density P r * mass e F z.2 := by
    funext r
    dsimp [adjusted, bumpCorrection]
    rw [mul_sub, ← mul_assoc, weighted_momentDensity]
  rw [heq, intervalIntegral.integral_sub hiF hiD, intervalIntegral.integral_mul_const]
  unfold primitive TransportPrimitive.compactIntegral
  rw [past_zero_eq_integral P.a_pos.le (weightedSource_continuous e hF.continuous)
    (weightedSource_supported e hs), total_weightedSource P e hF.continuous hs, cutoff_eq_integral]
  rfl

theorem weighted_sigma_eq (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : Continuous F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) (z : ℝ × E) :
    z.1 ^ e * sigma P e F z = -primitive P e F z := by
  by_cases h : primitive P e F z = 0
  · simp [sigma, h]
  have hr := primitive_supported P e hF hs h
  have hz0 : z.1 ≠ 0 := (P.a_pos.trans_le hr.1).ne'
  rw [sigma, inversePower_eq P e hr.1]
  field_simp

theorem sigma_eq_negative_primitive (P : Patch) (e : ℕ) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : RadialAlias.RadiallySupported P.a P.b F) (z : ℝ × E) :
    sigma P e F z = -(∫ r in (0 : ℝ)..z.1, r ^ e * adjusted P e F (r, z.2)) / z.1 ^ e := by
  rw [← primitive_eq_integral P e hF hs]
  by_cases h : primitive P e F z = 0
  · simp [sigma, h]
  rw [sigma, inversePower_eq P e (primitive_supported P e hF.continuous hs h).1]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem adjusted_supported (P : Patch) (e : ℕ) {F : ℝ × E → ℝ}
    (hs : RadialAlias.RadiallySupported P.a P.b F) :
    RadialAlias.RadiallySupported P.a P.b (adjusted P e F) := by
  intro z hz
  by_contra hn
  have hF : F z = 0 := by
    by_contra h
    exact hn (hs h)
  have hB : bumpCorrection P e F z = 0 := by
    by_contra h
    have hp := bumpCorrection_supported P e F h
    exact hn ⟨P.a_lt_left.le.trans hp.1, hp.2.trans P.right_lt_b.le⟩
  exact hz (by simp [adjusted, hF, hB])

theorem adjusted_moment_zero (P : Patch) (e : ℕ) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : RadialAlias.RadiallySupported P.a P.b F) (p : E) :
    mass e (adjusted P e F) p = 0 := by
  have hiF := IntegratedMeanBalances.weighted_integrable
    (IntegratedMeanBalances.radial_slice_smooth hF p).continuous
    (IntegratedMeanBalances.radial_slice_compact hs p) e
  have hiB := IntegratedMeanBalances.weighted_integrable
    (IntegratedMeanBalances.radial_slice_smooth (bumpCorrection_contDiff P e hF hs) p).continuous
    (IntegratedMeanBalances.radial_slice_compact (bumpCorrection_supported P e F) p) e
  change IntegratedMeanBalances.moment e
    (fun r => F (r, p) - bumpCorrection P e F (r, p)) = 0
  rw [IntegratedMeanBalances.moment_sub e hiF hiB]
  change mass e F p - mass e (bumpCorrection P e F) p = 0
  rw [bumpCorrection_moment, sub_self]

theorem adjusted_positive_moment_zero (P : Patch) (e : ℕ) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : RadialAlias.RadiallySupported P.a P.b F) (p : E) :
    (∫ r in Ioi (0 : ℝ), r ^ e * adjusted P e F (r, p)) = 0 := by
  rw [IntegratedMeanBalances.positive_integral_eq_integral P.a_pos]
  · exact adjusted_moment_zero P e hF hs p
  · intro r hr
    exact adjusted_supported P e hs (right_ne_zero_of_mul hr)

theorem primitive_hasDerivAt (P : Patch) (e : ℕ) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : RadialAlias.RadiallySupported P.a P.b F) (p : E) (r : ℝ) :
    HasDerivAt (fun t => primitive P e F (t, p)) (r ^ e * adjusted P e F (r, p)) r := by
  have hp := primitive_contDiff P e hF hs
  have hd := ((hp.differentiable (by simp)) (r, p)).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r p))
  have ht := TransportPrimitive.transport_compactIntegral (M := 0) (v := (0 : E))
    (cutoff_contDiff P) (weightedSource_contDiff e hF) (weightedSource_supported e hs) (r, p)
  simp only [TransportPrimitive.fixedDeriv, zero_smul, cutoff_deriv,
    total_weightedSource P e hF.continuous hs, smul_eq_mul] at ht
  have he : weightedSource e F (r, p) - density P r * mass e F p =
      r ^ e * adjusted P e F (r, p) := by
    dsimp [weightedSource, adjusted, bumpCorrection]
    rw [mul_sub, ← mul_assoc, weighted_momentDensity]
  rw [he] at ht
  change fderiv ℝ (primitive P e F) (r, p) (1, 0) = _ at ht
  simpa only [ht, Function.comp_def, id_eq] using hd

/-- The sign is the one required to cancel the adjusted residual by divergence. -/
theorem weighted_sigma_hasDerivAt (P : Patch) (e : ℕ) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : RadialAlias.RadiallySupported P.a P.b F) (p : E) (r : ℝ) :
    HasDerivAt (fun t => t ^ e * sigma P e F (t, p)) (-r ^ e * adjusted P e F (r, p)) r := by
  have he : (fun t => t ^ e * sigma P e F (t, p)) =
      fun t => -primitive P e F (t, p) := funext (fun t => weighted_sigma_eq P e hF.continuous hs
          (t, p))
  rw [he]
  convert! (primitive_hasDerivAt P e hF hs p r).neg using 1
  ring

theorem sigma_slice_compact (P : Patch) (e : ℕ) {F : ℝ × E → ℝ}
    (hF : Continuous F) (hs : RadialAlias.RadiallySupported P.a P.b F) (p : E) :
    HasCompactSupport (fun r => sigma P e F (r, p)) :=
  IntegratedMeanBalances.radial_slice_compact (sigma_supported P e hF hs) p

theorem angular_divergence (P : Patch) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : RadialAlias.RadiallySupported P.a P.b F) (p : E) {r : ℝ} (hr : 0 <
        r) :
    IntegratedMeanBalances.radialDivergence 2 (fun t => sigma P 2 F (t, p)) r =
      -adjusted P 2 F (r, p) := by
  have hsD := ((IntegratedMeanBalances.radial_slice_smooth (sigma_contDiff P 2 hF hs)
      p).differentiable (by
      simp) r).hasDerivAt
  have he := ((hasDerivAt_pow 2 r).mul hsD).unique (weighted_sigma_hasDerivAt P 2 hF hs p r)
  norm_num at he
  apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
  dsimp [IntegratedMeanBalances.radialDivergence]
  calc
    _ = 2 * r * sigma P 2 F (r, p) + r ^ 2 * deriv (fun t => sigma P 2 F (t, p)) r := by
      field_simp; ring
    _ = _ := by nlinarith [he]

theorem axial_divergence (P : Patch) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : RadialAlias.RadiallySupported P.a P.b F) (p : E) {r : ℝ} (hr : 0 <
        r) :
    IntegratedMeanBalances.radialDivergence 1 (fun t => sigma P 1 F (t, p)) r =
      -adjusted P 1 F (r, p) := by
  have hsD := ((IntegratedMeanBalances.radial_slice_smooth (sigma_contDiff P 1 hF hs)
      p).differentiable (by
      simp) r).hasDerivAt
  have he := ((hasDerivAt_pow 1 r).mul hsD).unique (weighted_sigma_hasDerivAt P 1 hF hs p r)
  norm_num at he
  apply mul_left_cancel₀ hr.ne'
  dsimp [IntegratedMeanBalances.radialDivergence]
  calc
    _ = sigma P 1 F (r, p) + r * deriv (fun t => sigma P 1 F (t, p)) r := by
      field_simp; ring
    _ = _ := by nlinarith [he]

/-- All fixed-order constants come from the proved weighted integral estimate
and bounded radial multipliers on a fixed positive annulus. -/
theorem sigma_finiteJets_uniform (P : Patch) (e : ℕ) {cL cR : ℝ}
    (hcL : 0 < cL) (hcR : 0 < cR) (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F : ℝ × E → ℝ, ContDiff ℝ ∞ F →
      RadialAlias.RadiallySupported P.a P.b F → ∀ A : ℝ, 0 ≤ A →
      (∀ i ≤ m, ∀ r ∈ Ioo P.a P.b, ∀ y : E,
        ‖iteratedFDeriv ℝ i F (r, y)‖ ≤ A * WeightedRadialPrimitive.logWeight cL cR P.a P.b p r) →
      ∀ z : ℝ × E, z.1 ∈ Ioo P.a P.b → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (sigma P e F) z‖ ≤
          K * A * WeightedRadialPrimitive.logWeight cL cR P.a P.b p z.1 := by
  obtain ⟨K1, hK1, h1⟩ := RadialPullback.radial_multiplier_finiteJets_uniform
    (E := E) (V := ℝ) P.a P.b (contDiff_id.pow e) m
  obtain ⟨K2, hK2, h2⟩ := WeightedRadialPrimitive.transport_compact_finiteJets_uniform
    (E := E) (V := ℝ) P.a_pos P.a_lt_left P.left_lt_right P.right_lt_b hcL hcR p m
    (cutoff P) (cutoff_contDiff P) (fun _ h => cutoff_zero P h) (fun _ h => cutoff_one P h)
  obtain ⟨K3, hK3, h3⟩ := RadialPullback.radial_multiplier_finiteJets_uniform
    (E := E) (V := ℝ) P.a P.b (inversePower_contDiff P e).neg m
  refine ⟨K3 * K2 * K1, by positivity, ?_⟩
  intro F hF hs A hA hFbound z hz j hj
  have hweight (r : ℝ) (hr : r ∈ Ioo P.a P.b) :
      0 ≤ WeightedRadialPrimitive.logWeight cL cR P.a P.b p r :=
    (WeightedRadialPrimitive.weight_pos cL cR p (WeightedRadialPrimitive.logPosition_mem P.a_pos
        hr)).le
  have hweighted : ∀ i ≤ m, ∀ r ∈ Ioo P.a P.b, ∀ y : E,
      ‖iteratedFDeriv ℝ i (weightedSource e F) (r, y)‖ ≤
        (K1 * A) * WeightedRadialPrimitive.logWeight cL cR P.a P.b p r := by
    intro i hi r hr y
    have h := h1 F hF (r, y) ⟨hr.1.le, hr.2.le⟩
      (A * WeightedRadialPrimitive.logWeight cL cR P.a P.b p r) (mul_nonneg hA (hweight r hr))
      (fun k hk => hFbound k hk r hr y) i hi
    simp only [smul_eq_mul, mul_assoc, id_eq] at h ⊢
    exact h
  have hprimitive (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i (primitive P e F) z‖ ≤
        (K2 * (K1 * A)) * WeightedRadialPrimitive.logWeight cL cR P.a P.b p z.1 :=
    h2 0 0 (weightedSource e F) (weightedSource_contDiff e hF) (weightedSource_supported e hs)
      (K1 * A) (mul_nonneg hK1 hA) hweighted z hz i hi
  have h := h3 (primitive P e F) (primitive_contDiff P e hF hs) z ⟨hz.1.le, hz.2.le⟩
    ((K2 * (K1 * A)) * WeightedRadialPrimitive.logWeight cL cR P.a P.b p z.1)
    (mul_nonneg (mul_nonneg hK2 (mul_nonneg hK1 hA)) (hweight z.1 hz)) hprimitive j hj
  simp only [smul_eq_mul, mul_assoc] at h ⊢
  exact h

theorem meanClass_sigma (P : Patch) (e : ℕ) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε slow : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hslow : ∀ n, 1 ≤ slow n)
    (α : ℝ) (F : ℕ → ℝ × E → ℝ) (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hs : ∀ n, RadialAlias.RadiallySupported P.a P.b (F n))
    (hclass : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow) α F)
          :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow) α
      (fun n => sigma P e (F n)) := by
  refine ⟨hclass.weight_nonneg, fun n => (sigma_contDiff P e (hF n) (hs n)).contDiffOn, ?_⟩
  intro m
  obtain ⟨C, hC, p, hsource⟩ := hclass.bounds m
  obtain ⟨K, hK, hbound⟩ := sigma_finiteJets_uniform (E := E) P e hcL hcR p m
  refine ⟨K * C, mul_nonneg hK hC, p, ?_⟩
  intro n z hz j hj
  change z.1 ∈ Ioo P.a P.b at hz
  have hA : 0 ≤ C * (ε n) ^ α * (slow n) ^ p :=
    mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hslow n)) p)
  have hinput : ∀ i ≤ m, ∀ r ∈ Ioo P.a P.b, ∀ y : E,
      ‖iteratedFDeriv ℝ i (F n) (r, y)‖ ≤
        (C * (ε n) ^ α * (slow n) ^ p) * WeightedRadialPrimitive.logWeight cL cR P.a P.b p r := by
    intro i hi r hr y
    have h := hsource n (r, y) hr i hi
    rw [WeightedRadialPrimitive.logStrip_majorant_eq P.a_pos hcL hcR ε slow hε hε1 hslow
      α C p n (r, y) hr] at h
    exact h
  have h := hbound (F n) (hF n) (hs n) _ hA hinput z hz j hj
  rw [WeightedRadialPrimitive.logStrip_majorant_eq P.a_pos hcL hcR ε slow hε hε1 hslow
    α (K * C) p n z hz]
  simpa only [mul_assoc] using h

/-- The constructed interior bump carries the full edge weight, because its
support lies in a fixed compact subset of the active annulus. -/
theorem momentDensity_meanClass (P : Patch) (e : ℕ) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε slow : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hslow : ∀ n, 1 ≤ slow n) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      0 (fun _ (z : ℝ × E) => momentDensity P e z.1) := by
  let s := WeightedRadialPrimitive.logStripData (E := E) P.a P.b cL cR P.a_pos hcL hcR ε slow hε
      hε1 hslow
  have hmem : ∀ r ∈ Icc P.left P.right, (r, (0 : E)) ∈ s.domain := by
    intro r hr
    exact ⟨P.a_lt_left.trans_le hr.1, hr.2.trans_lt P.right_lt_b⟩
  have hc : ContinuousOn (fun r => s.zeta (r, (0 : E))) (Icc P.left P.right) :=
    s.zeta_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmem
  have hp : ∀ r ∈ Icc P.left P.right, 0 < s.zeta (r, (0 : E)) := by
    intro r hr
    exact WeightedRadialPrimitive.zeta_pos cL cR
      (WeightedRadialPrimitive.logPosition_mem P.a_pos (hmem r hr))
  obtain ⟨D, hD, hDb⟩ := UniformCone.positive_uniform_margin isCompact_Icc hc hp
  have hs : RadialAlias.RadiallySupported P.left P.right (fun z : ℝ × E => momentDensity P e z.1) :=
    fun z hz => momentDensity_support P e hz
  refine ⟨fun _ z hz => s.zeta_nonneg z hz,
    fun _ => ((momentDensity_contDiff P e).comp contDiff_fst).contDiffOn, ?_⟩
  intro m
  obtain ⟨C, hC, hCb⟩ := WeightedRadialPrimitive.cutoff_finiteJet_bound (E := E)
    P.a P.b (momentDensity P e) (momentDensity_contDiff P e) m
  refine ⟨C / D, div_nonneg hC hD.le, 0, ?_⟩
  intro n z hz j hj
  change ‖iteratedFDeriv ℝ j (fun z : ℝ × E => momentDensity P e z.1) z‖ ≤
    WeightedClasses.majorant s (fun _ y => s.zeta y) 0 (C / D) 0 n z
  simp only [WeightedClasses.majorant, Real.rpow_zero, pow_zero, mul_one]
  by_cases hi : z.1 ∈ Icc P.left P.right
  · have hd : D ≤ s.zeta z := hDb z.1 hi
    calc
      _ ≤ C := hCb j hj z ⟨hz.1.le, hz.2.le⟩
      _ = (C / D) * D := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (div_nonneg hC hD.le)
  · have hzj : iteratedFDeriv ℝ j (fun z : ℝ × E => momentDensity P e z.1) z = 0 := by
      by_contra hn
      exact hi (TransportPrimitive.iteratedFDeriv_supported hs j hn)
    rw [hzj, norm_zero]
    exact mul_nonneg (div_nonneg hC hD.le) (s.zeta_nonneg z hz)

theorem fderiv_lift (D : E → ℝ) (hD : ContDiff ℝ ∞ D) (z : ℝ × E) (v : E) :
    fderiv ℝ (fun y : ℝ × E => D y.2) z (0, v) = fderiv ℝ D z.2 v := by
  have h := ((hD.differentiable (by simp)) z.2).hasFDerivAt.comp z hasFDerivAt_snd
  change fderiv ℝ (D ∘ Prod.snd) z (0, v) = _
  rw [h.fderiv]
  simp

/-- The improved bump order follows from a proved residual-moment identity:
one slow derivative comes with one additional factor of epsilon. -/
theorem bump_improvedClass_of_moment_identity (P : Patch) (e : ℕ) {cL cR : ℝ}
    (hcL : 0 < cL) (hcR : 0 < cR) (ε slow : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hslow : ∀ n, 1 ≤ slow n)
    (α : ℝ) (F : ℕ → ℝ × E → ℝ) (D : ℕ → E → ℝ) (v : E)
    (hD : ∀ n, ContDiff ℝ ∞ (D n))
    (hclass : WeightedClasses.UnweightedClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      α (fun n (z : ℝ × E) => D n z.2))
    (hmoment : ∀ n p, mass e (F n) p = ε n * fderiv ℝ (D n) p v) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      (α + 1) (fun n => bumpCorrection P e (F n)) := by
  let s := WeightedRadialPrimitive.logStripData (E := E) P.a P.b cL cR P.a_pos hcL hcR ε slow hε
      hε1 hslow
  have hd := hclass.directional ((0 : ℝ), v)
  have hb := (momentDensity_meanClass (E := E) P e hcL hcR ε slow hε hε1 hslow).mul hd
  have hmean : WeightedClasses.MeanClass s α (fun n (z : ℝ × E) =>
      momentDensity P e z.1 * fderiv ℝ (D n) z.2 v) := by
    simpa only [WeightedClasses.MeanClass, zero_add, mul_one, fderiv_lift _ (hD _)] using hb
  have hh := hmean.band_smul (WeightedClasses.bandBound_rpow s 1)
  have heq : (fun n (z : ℝ × E) => s.epsilon n ^ (1 : ℝ) •
      (momentDensity P e z.1 * fderiv ℝ (D n) z.2 v)) = fun n => bumpCorrection P e (F n) := by
    funext n z
    simp only [Real.rpow_one, smul_eq_mul, bumpCorrection, hmoment]
    change ε n * (momentDensity P e z.1 * _) = momentDensity P e z.1 * (ε n * _)
    ring
  rwa [heq] at hh

/-- Bar sigma, given by `sigma P e (PressureStream.torusAverage F)`. -/
noncomputable def barSigma (P : Patch) (e : ℕ) (F : PressureStream.Lift E → ℝ) : ℝ × E → ℝ :=
  sigma P e (PressureStream.torusAverage F)

theorem barSigma_contDiff (P : Patch) (e : ℕ) {F : PressureStream.Lift E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : RadialAlias.RadiallySupported P.a P.b F) :
    ContDiff ℝ ∞ (barSigma P e F) :=
  sigma_contDiff P e (PressureStream.torusAverage_contDiff hF)
      (PressureStream.torusAverage_supported hs)

theorem barSigma_eq_primitive (P : Patch) (e : ℕ) {F : PressureStream.Lift E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : RadialAlias.RadiallySupported P.a P.b F) (z : ℝ × E) :
    barSigma P e F z = -(∫ r in (0 : ℝ)..z.1,
      r ^ e * adjusted P e (PressureStream.torusAverage F) (r, z.2)) / z.1 ^ e :=
  sigma_eq_negative_primitive P e (PressureStream.torusAverage_contDiff hF)
    (PressureStream.torusAverage_supported hs) z

/-- Slow coefficients are constant along the ordinary radial integration. -/
theorem sigma_slow_mul (P : Patch) (e : ℕ) (k : E → ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) :
    sigma P e (fun y => k y.2 * F y) z = k z.2 * sigma P e F z := by
  have hp : TransportPrimitive.pastIntegral 0 (0 : E) (weightedSource e (fun y => k y.2 * F y)) z =
      k z.2 * TransportPrimitive.pastIntegral 0 (0 : E) (weightedSource e F) z := by
    unfold TransportPrimitive.pastIntegral
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => by
        simp [weightedSource, TransportPrimitive.shift]; ring)
  have ht : TransportPrimitive.totalIntegral 0 (0 : E) (weightedSource e (fun y => k y.2 * F y)) z =
      k z.2 * TransportPrimitive.totalIntegral 0 (0 : E) (weightedSource e F) z := by
    unfold TransportPrimitive.totalIntegral
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => by
        simp [weightedSource, TransportPrimitive.shift]; ring)
  unfold sigma primitive TransportPrimitive.compactIntegral
  rw [hp, ht]
  simp only [smul_eq_mul]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem mass_slow_mul (e : ℕ) (k : E → ℝ) (F : ℝ × E → ℝ) (p : E) :
    mass e (fun y => k y.2 * F y) p = k p * mass e F p := by
  change (∫ r, r ^ e * (k p * F (r, p))) = k p * ∫ r, r ^ e * F (r, p)
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => by ring)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem bump_slow_mul (P : Patch) (e : ℕ) (k : E → ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) :
    bumpCorrection P e (fun y => k y.2 * F y) z = k z.2 * bumpCorrection P e F z := by
  simp only [bumpCorrection, mass_slow_mul]
  ring

end Primitive

section Physical

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The physical radial length is sqrt q, as in the chart R = r / sqrt Q. -/
noncomputable def lengthScale (q : E → ℝ) (p : E) : ℝ := Real.sqrt (q p)
/-- Native source, given by `F (lengthScale q z.2 * z.1, z.2)`. -/
noncomputable def nativeSource (q : E → ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  F (lengthScale q z.2 * z.1, z.2)
/-- Physical density, given by `momentDensity P e (z.1 / lengthScale q z.2) / lengthScale q z.2
^ (e + 1)`. -/
noncomputable def physicalDensity (P : Patch) (e : ℕ) (q : E → ℝ) (z : ℝ × E) : ℝ :=
  momentDensity P e (z.1 / lengthScale q z.2) / lengthScale q z.2 ^ (e + 1)
/-- Physical bump, given by `physicalDensity P e q z * mass e F z.2`. -/
noncomputable def physicalBump (P : Patch) (e : ℕ) (q : E → ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  physicalDensity P e q z * mass e F z.2
/-- Physical adjusted, given by `F z - physicalBump P e q F z`. -/
noncomputable def physicalAdjusted (P : Patch) (e : ℕ) (q : E → ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ
    :=
  F z - physicalBump P e q F z
/-- Physical sigma, given by `lengthScale q z.2 * sigma P e (nativeSource q F) (z.1 /
lengthScale q z.2, z.2)`. -/
noncomputable def physicalSigma (P : Patch) (e : ℕ) (q : E → ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  lengthScale q z.2 * sigma P e (nativeSource q F) (z.1 / lengthScale q z.2, z.2)

/-- Radial support stated directly using the physical q, with no band index. -/
def PhysicalSupport (P : Patch) (q : E → ℝ) (F : ℝ × E → ℝ) : Prop :=
  ∀ z, F z ≠ 0 → z.1 / lengthScale q z.2 ∈ Icc P.a P.b

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem lengthScale_pos {q : E → ℝ} (hq : ∀ p, 0 < q p) (p : E) : 0 < lengthScale q p :=
  Real.sqrt_pos.mpr (hq p)

theorem lengthScale_contDiff {q : E → ℝ} (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) :
    ContDiff ℝ ∞ (lengthScale q) := hq.sqrt (fun p => (hpos p).ne')

theorem nativeSource_contDiff {q : E → ℝ} (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p)
    {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (nativeSource q F) :=
  hF.comp ((((lengthScale_contDiff hq hpos).comp contDiff_snd).mul contDiff_fst).prodMk
      contDiff_snd)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem nativeSource_supported (P : Patch) {q : E → ℝ} (hq : ∀ p, 0 < q p)
    {F : ℝ × E → ℝ} (hs : PhysicalSupport P q F) :
    RadialAlias.RadiallySupported P.a P.b (nativeSource q F) := by
  intro z hz
  have h := hs (lengthScale q z.2 * z.1, z.2) hz
  simp only [mul_div_cancel_left₀ _ (lengthScale_pos hq z.2).ne'] at h
  exact h

theorem integral_dilate_weighted (e : ℕ) (f : ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ r, r ^ e * f (s * r)) = (∫ r, r ^ e * f r) / s ^ (e + 1) := by
  have he : (fun r => r ^ e * f (s * r)) =
      fun r => (s ^ e)⁻¹ * ((s * r) ^ e * f (s * r)) := by
    funext r
    rw [mul_pow]
    field_simp [hs.ne']
  rw [he, integral_const_mul, Measure.integral_comp_mul_left (fun r => r ^ e * f r) s]
  rw [abs_of_pos (inv_pos.mpr hs), smul_eq_mul, pow_succ]
  field_simp [hs.ne']

theorem interval_dilate_weighted (e : ℕ) (f : ℝ → ℝ) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (∫ r in (0 : ℝ)..x, r ^ e * f (s * r)) =
      (∫ r in (0 : ℝ)..(s * x), r ^ e * f r) / s ^ (e + 1) := by
  have he : (fun r => r ^ e * f (s * r)) =
      fun r => (s ^ e)⁻¹ * ((s * r) ^ e * f (s * r)) := by
    funext r
    rw [mul_pow]
    field_simp [hs.ne']
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun r => r ^ e * f r) hs.ne']
  rw [mul_zero, smul_eq_mul, pow_succ]
  field_simp [hs.ne']

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem nativeSource_mass (e : ℕ) {q : E → ℝ} (hq : ∀ p, 0 < q p)
    (F : ℝ × E → ℝ) (p : E) :
    mass e (nativeSource q F) p = mass e F p / lengthScale q p ^ (e + 1) :=
  integral_dilate_weighted e (fun r => F (r, p)) (lengthScale_pos hq p)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem physicalDensity_moment (P : Patch) (e : ℕ) {q : E → ℝ} (hq : ∀ p, 0 < q p) (p : E) :
    (∫ r, r ^ e * physicalDensity P e q (r, p)) = 1 := by
  let s := lengthScale q p
  have hs : 0 < s := lengthScale_pos hq p
  have h := integral_dilate_weighted e (momentDensity P e) (inv_pos.mpr hs)
  simp only [momentDensity_moment] at h
  have he : (fun r => r ^ e * physicalDensity P e q (r, p)) =
      fun r => (r ^ e * momentDensity P e (s⁻¹ * r)) / s ^ (e + 1) := by
    funext r
    simp [physicalDensity, s, div_eq_mul_inv, mul_comm, mul_left_comm]
  rw [he, integral_div, h, inv_pow]
  field_simp [hs.ne']

theorem physicalDensity_contDiff (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) : ContDiff ℝ ∞ (physicalDensity P e q) := by
  have hs := (lengthScale_contDiff hq hpos).comp (contDiff_snd (E := ℝ))
  exact ((momentDensity_contDiff P e).comp
    (contDiff_fst.div hs (fun z => (lengthScale_pos hpos z.2).ne'))).div (hs.pow (e + 1))
      (fun z => pow_ne_zero _ (lengthScale_pos hpos z.2).ne')

theorem physical_mass_contDiff (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) : ContDiff ℝ ∞ (mass e F) := by
  have hn := mass_contDiff e (nativeSource_contDiff hq hpos hF) (nativeSource_supported P hpos hs)
  have he : mass e F = fun p => lengthScale q p ^ (e + 1) * mass e (nativeSource q F) p := by
    funext p
    rw [nativeSource_mass e hpos]
    field_simp [(lengthScale_pos hpos p).ne']
  rw [he]
  exact ((lengthScale_contDiff hq hpos).pow (e + 1)).mul hn

theorem physicalBump_contDiff (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) : ContDiff ℝ ∞ (physicalBump P e q F) :=
  (physicalDensity_contDiff P e hq hpos).mul ((physical_mass_contDiff P e hq hpos hF hs).comp
      contDiff_snd)

theorem physicalSigma_contDiff (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) : ContDiff ℝ ∞ (physicalSigma P e q F) := by
  have hl : ContDiff ℝ ∞ (fun z : ℝ × E => lengthScale q z.2) :=
    (lengthScale_contDiff hq hpos).comp contDiff_snd
  exact hl.mul ((sigma_contDiff P e (nativeSource_contDiff hq hpos hF)
    (nativeSource_supported P hpos hs)).comp
      ((contDiff_fst.div hl (fun z => (lengthScale_pos hpos z.2).ne')).prodMk contDiff_snd))

theorem physicalSigma_supported (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) : PhysicalSupport P q (physicalSigma P e q
        F) := by
  intro z hz
  exact sigma_supported P e (nativeSource_contDiff hq hpos hF).continuous
    (nativeSource_supported P hpos hs) (right_ne_zero_of_mul hz)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem native_adjusted_eq (P : Patch) (e : ℕ) {q : E → ℝ} (hq : ∀ p, 0 < q p)
    (F : ℝ × E → ℝ) (z : ℝ × E) :
    adjusted P e (nativeSource q F) z =
      physicalAdjusted P e q F (lengthScale q z.2 * z.1, z.2) := by
  simp only [adjusted, bumpCorrection, nativeSource, physicalAdjusted, physicalBump,
      physicalDensity,
    nativeSource_mass e hq, mul_div_cancel_left₀ _ (lengthScale_pos hq z.2).ne']
  ring

/-- The physical sigma is exactly the requested negative primitive from zero.
No fixed-Q chart enters this definition or identity. -/
theorem physicalSigma_eq_negative_primitive (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) (z : ℝ × E) :
    physicalSigma P e q F z =
      -(∫ r in (0 : ℝ)..z.1, r ^ e * physicalAdjusted P e q F (r, z.2)) / z.1 ^ e := by
  have hl := lengthScale_pos hpos z.2
  unfold physicalSigma
  rw [sigma_eq_negative_primitive P e (nativeSource_contDiff hq hpos hF) (nativeSource_supported P
      hpos hs)]
  simp_rw [native_adjusted_eq P e hpos]
  rw [interval_dilate_weighted e (fun r => physicalAdjusted P e q F (r, z.2)) hl,
    mul_div_cancel₀ z.1 hl.ne']
  rw [div_pow, pow_succ]
  by_cases hr : z.1 = 0
  · simp [hr]
  · field_simp [hl.ne', hr]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem physicalDensity_support (P : Patch) (e : ℕ) {q : E → ℝ} (hq : ∀ p, 0 < q p) (p : E) :
    support (fun r => physicalDensity P e q (r, p)) ⊆
      Icc (lengthScale q p * P.left) (lengthScale q p * P.right) := by
  intro r hr
  have hmd : momentDensity P e (r / lengthScale q p) ≠ 0 := by
    intro h
    apply hr
    simp [physicalDensity, h]
  have h := momentDensity_support P e hmd
  exact ⟨by simpa only [mul_comm] using (le_div_iff₀ (lengthScale_pos hq p)).mp h.1,
    by simpa only [mul_comm] using (div_le_iff₀ (lengthScale_pos hq p)).mp h.2⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem physicalDensity_positive_moment (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ∀ p, 0 < q p) (p : E) :
    (∫ r in Ioi (0 : ℝ), r ^ e * physicalDensity P e q (r, p)) = 1 := by
  rw [IntegratedMeanBalances.positive_integral_eq_integral (mul_pos (lengthScale_pos hq p)
      P.left_pos)]
  · exact physicalDensity_moment P e hq p
  · intro r hr
    exact physicalDensity_support P e hq p (right_ne_zero_of_mul hr)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem physicalBump_moment (P : Patch) (e : ℕ) {q : E → ℝ} (hq : ∀ p, 0 < q p)
    (F : ℝ × E → ℝ) (p : E) : mass e (physicalBump P e q F) p = mass e F p := by
  change (∫ r, r ^ e * (physicalDensity P e q (r, p) * mass e F p)) = _
  simp_rw [← mul_assoc]
  rw [integral_mul_const, physicalDensity_moment P e hq p, one_mul]

theorem physicalAdjusted_moment_zero (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) (p : E) :
    mass e (physicalAdjusted P e q F) p = 0 := by
  have he : nativeSource q (physicalAdjusted P e q F) = adjusted P e (nativeSource q F) :=
    funext fun z => (native_adjusted_eq P e hpos F z).symm
  have hz := adjusted_moment_zero P e (nativeSource_contDiff hq hpos hF)
    (nativeSource_supported P hpos hs) p
  have hh := nativeSource_mass e hpos (physicalAdjusted P e q F) p
  rw [he, hz] at hh
  have hm := congrArg (fun t => t * lengthScale q p ^ (e + 1)) hh
  simpa only [zero_mul, div_mul_cancel₀ _ (pow_ne_zero _ (lengthScale_pos hpos p).ne')] using
      hm.symm

theorem physicalSigma_slice_compact (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) (p : E) :
    HasCompactSupport (fun r => physicalSigma P e q F (r, p)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := lengthScale q p * P.a) (b := lengthScale q p * P.b))
  intro r hr
  have h := physicalSigma_supported P e hq hpos hF hs (r, p) hr
  exact ⟨by simpa only [mul_comm] using (le_div_iff₀ (lengthScale_pos hpos p)).mp h.1,
    by simpa only [mul_comm] using (div_le_iff₀ (lengthScale_pos hpos p)).mp h.2⟩

theorem physicalAdjusted_contDiff (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) :
    ContDiff ℝ ∞ (physicalAdjusted P e q F) := hF.sub (physicalBump_contDiff P e hq hpos hF hs)

theorem physical_weighted_sigma_eq (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) (p : E) (r : ℝ) :
    r ^ e * physicalSigma P e q F (r, p) =
      -(∫ t in (0 : ℝ)..r, t ^ e * physicalAdjusted P e q F (t, p)) := by
  rw [physicalSigma_eq_negative_primitive P e hq hpos hF hs]
  by_cases hr : r = 0
  · subst r
    simp
  · field_simp

theorem physical_weighted_sigma_hasDerivAt (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) (p : E) (r : ℝ) :
    HasDerivAt (fun t => t ^ e * physicalSigma P e q F (t, p))
      (-r ^ e * physicalAdjusted P e q F (r, p)) r := by
  have hc : Continuous (fun t => t ^ e * physicalAdjusted P e q F (t, p)) :=
    (continuous_id.pow e).mul ((physicalAdjusted_contDiff P e hq hpos hF hs).continuous.comp
      (continuous_id.prodMk continuous_const))
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).neg
  have he : (fun t => t ^ e * physicalSigma P e q F (t, p)) =
      fun t => -(∫ u in (0 : ℝ)..t, u ^ e * physicalAdjusted P e q F (u, p)) :=
    funext (physical_weighted_sigma_eq P e hq hpos hF hs p)
  rw [he]
  convert! hd using 1
  ring

theorem physical_angular_divergence (P : Patch) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) (p : E) {r : ℝ} (hr : 0 < r) :
    IntegratedMeanBalances.radialDivergence 2 (fun t => physicalSigma P 2 q F (t, p)) r =
      -physicalAdjusted P 2 q F (r, p) := by
  have hd := ((IntegratedMeanBalances.radial_slice_smooth (physicalSigma_contDiff P 2 hq hpos hF
      hs) p).differentiable
    (by simp) r).hasDerivAt
  have he := ((hasDerivAt_pow 2 r).mul hd).unique
    (physical_weighted_sigma_hasDerivAt P 2 hq hpos hF hs p r)
  norm_num at he
  apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
  dsimp [IntegratedMeanBalances.radialDivergence]
  calc
    _ = 2 * r * physicalSigma P 2 q F (r, p) +
        r ^ 2 * deriv (fun t => physicalSigma P 2 q F (t, p)) r := by field_simp; ring
    _ = _ := by nlinarith [he]

theorem physical_axial_divergence (P : Patch) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) (p : E) {r : ℝ} (hr : 0 < r) :
    IntegratedMeanBalances.radialDivergence 1 (fun t => physicalSigma P 1 q F (t, p)) r =
      -physicalAdjusted P 1 q F (r, p) := by
  have hd := ((IntegratedMeanBalances.radial_slice_smooth (physicalSigma_contDiff P 1 hq hpos hF
      hs) p).differentiable
    (by simp) r).hasDerivAt
  have he := ((hasDerivAt_pow 1 r).mul hd).unique
    (physical_weighted_sigma_hasDerivAt P 1 hq hpos hF hs p r)
  norm_num at he
  apply mul_left_cancel₀ hr.ne'
  dsimp [IntegratedMeanBalances.radialDivergence]
  calc
    _ = physicalSigma P 1 q F (r, p) + r * deriv (fun t => physicalSigma P 1 q F (t, p)) r := by
      field_simp; ring
    _ = _ := by nlinarith [he]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Taking the torus bar preserves support described by the physical q. -/
theorem physical_torusAverage_supported (P : Patch) {q : E → ℝ}
    {F : PressureStream.Lift E → ℝ}
    (hs : PhysicalSupport P (fun p => q p.1) F) :
    PhysicalSupport P q (PressureStream.torusAverage F) := by
  intro z hz
  by_contra hn
  apply hz
  apply PressureStream.torusAverage_zero_of_forall
  intro Y
  by_contra hF
  exact hn (hs (z.1, (z.2, Y)) hF)

/-- Physical bar sigma, given by `physicalSigma P e q (PressureStream.torusAverage F)`. -/
noncomputable def physicalBarSigma (P : Patch) (e : ℕ) (q : E → ℝ)
    (F : PressureStream.Lift E → ℝ) : ℝ × E → ℝ :=
  physicalSigma P e q (PressureStream.torusAverage F)

theorem physicalBarSigma_contDiff (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : PressureStream.Lift E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P (fun p => q p.1) F) :
    ContDiff ℝ ∞ (physicalBarSigma P e q F) :=
  physicalSigma_contDiff P e hq hpos (PressureStream.torusAverage_contDiff hF)
    (physical_torusAverage_supported P hs)

theorem physicalBarSigma_eq_negative_primitive (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : PressureStream.Lift E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P (fun p => q p.1) F) (z : ℝ × E) :
    physicalBarSigma P e q F z = -(∫ r in (0 : ℝ)..z.1,
      r ^ e * physicalAdjusted P e q (PressureStream.torusAverage F) (r, z.2)) / z.1 ^ e :=
  physicalSigma_eq_negative_primitive P e hq hpos (PressureStream.torusAverage_contDiff hF)
    (physical_torusAverage_supported P hs) z

/-- Residual units in the q-chart: q^(2A+1/2) times the physical residual. -/
noncomputable def normalizedResidual (q : E → ℝ) (A : ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  q z.2 ^ (2 * A + 1 / 2) * nativeSource q F z

/-- Q chart tensor, given by `q z.2 ^ (2 * A) * physicalSigma P e q F (lengthScale q z.2 * z.1,
z.2)`. -/
noncomputable def qChartTensor (P : Patch) (e : ℕ) (q : E → ℝ) (A : ℝ)
    (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  q z.2 ^ (2 * A) * physicalSigma P e q F (lengthScale q z.2 * z.1, z.2)

/-- Q chart bump, given by `q z.2 ^ (2 * A + 1 / 2) * physicalBump P e q F (lengthScale q z.2 *
z.1, z.2)`. -/
noncomputable def qChartBump (P : Patch) (e : ℕ) (q : E → ℝ) (A : ℝ)
    (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  q z.2 ^ (2 * A + 1 / 2) * physicalBump P e q F (lengthScale q z.2 * z.1, z.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem qChartBump_eq (P : Patch) (e : ℕ) {q : E → ℝ} (hq : ∀ p, 0 < q p)
    (A : ℝ) (F : ℝ × E → ℝ) : qChartBump P e q A F = bumpCorrection P e (normalizedResidual q A F)
        := by
  funext z
  unfold qChartBump normalizedResidual
  rw [bump_slow_mul P e (fun p => q p ^ (2 * A + 1 / 2)) (nativeSource q F)]
  simp only [physicalBump, physicalDensity, bumpCorrection, nativeSource_mass e hq,
    mul_div_cancel_left₀ _ (lengthScale_pos hq z.2).ne']
  ring

theorem tensor_units_identity (P : Patch) (e : ℕ) {q : E → ℝ} (hq : ∀ p, 0 < q p)
    (A : ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) :
    q z.2 ^ (2 * A) * physicalSigma P e q F z =
      sigma P e (normalizedResidual q A F) (z.1 / lengthScale q z.2, z.2) := by
  unfold normalizedResidual
  rw [sigma_slow_mul P e (fun p => q p ^ (2 * A + 1 / 2)) (nativeSource q F)]
  unfold physicalSigma lengthScale
  rw [← mul_assoc, Real.sqrt_eq_rpow, ← Real.rpow_add (hq z.2)]

/-- Exact chart tensor units, with no preferred band in the physical definition. -/
theorem qChartTensor_eq (P : Patch) (e : ℕ) {q : E → ℝ} (hq : ∀ p, 0 < q p)
    (A : ℝ) (F : ℝ × E → ℝ) : qChartTensor P e q A F = sigma P e (normalizedResidual q A F) := by
  funext z
  rw [qChartTensor, tensor_units_identity P e hq A F (lengthScale q z.2 * z.1, z.2)]
  simp only [mul_div_cancel_left₀ _ (lengthScale_pos hq z.2).ne']

theorem normalizedResidual_contDiff {q : E → ℝ} (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p)
    (A : ℝ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (normalizedResidual q A F) := by
  have hp : ContDiff ℝ ∞ (fun z : ℝ × E => q z.2 ^ (2 * A + 1 / 2)) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (hq.comp contDiff_snd).contDiffAt.rpow_const_of_ne (hpos z.2).ne'
  exact hp.mul (nativeSource_contDiff hq hpos hF)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem normalizedResidual_supported (P : Patch) {q : E → ℝ} (hq : ∀ p, 0 < q p)
    (A : ℝ) {F : ℝ × E → ℝ} (hs : PhysicalSupport P q F) :
    RadialAlias.RadiallySupported P.a P.b (normalizedResidual q A F) :=
  fun _ h => nativeSource_supported P hq hs (right_ne_zero_of_mul h)

/-- The actual physical stress has the claimed all-jet tensor class after
conversion to q-chart units, directly from the normalized residual class. -/
theorem meanClass_qChartTensor (P : Patch) (e : ℕ) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε slow : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hslow : ∀ n, 1 ≤ slow n)
    {q : E → ℝ} (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) (A α : ℝ)
    (F : ℕ → ℝ × E → ℝ) (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hs : ∀ n, PhysicalSupport P q (F n))
    (hclass : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      α (fun n => normalizedResidual q A (F n))) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      α (fun n => qChartTensor P e q A (F n)) := by
  simp_rw [qChartTensor_eq P e hpos A]
  exact meanClass_sigma P e hcL hcR ε slow hε hε1 hslow α _
    (fun n => normalizedResidual_contDiff hq hpos A (hF n))
    (fun n => normalizedResidual_supported P hpos A (hs n)) hclass

/-- A fixed-Q chart is an exact reparametrization of the physical-q stress;
the physical stress itself was defined without Q. -/
theorem fixedQ_tensor_identity (P : Patch) (e : ℕ) {q : E → ℝ} (hq : ∀ p, 0 < q p)
    {Q : ℝ} (hQ : 0 < Q) (A : ℝ) (F : ℝ × E → ℝ) (R : ℝ) (p : E) :
    Q ^ (2 * A) * physicalSigma P e q F (Real.sqrt Q * R, p) =
      (Q / q p) ^ (2 * A) * sigma P e (normalizedResidual q A F)
        ((Real.sqrt Q / Real.sqrt (q p)) * R, p) := by
  have hcoord : (Real.sqrt Q / Real.sqrt (q p)) * R = (Real.sqrt Q * R) / lengthScale q p := by
    unfold lengthScale
    ring
  rw [hcoord, ← tensor_units_identity P e hq A F (Real.sqrt Q * R, p),
    Real.div_rpow hQ.le (hq p).le]
  field_simp [(Real.rpow_pos_of_pos (hq p) (2 * A)).ne']

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem fixedQ_density_identity (P : Patch) (e : ℕ) (q : E → ℝ)
    (Q R : ℝ) (p : E) :
    Real.sqrt Q ^ (e + 1) * physicalDensity P e q (Real.sqrt Q * R, p) =
      (Real.sqrt Q / Real.sqrt (q p)) ^ (e + 1) *
        momentDensity P e ((Real.sqrt Q / Real.sqrt (q p)) * R) := by
  unfold physicalDensity lengthScale
  rw [div_pow]
  have hc : (Real.sqrt Q * R) / Real.sqrt (q p) = (Real.sqrt Q / Real.sqrt (q p)) * R := by ring
  rw [hc]
  ring

end Physical

section IntegratedBalances

open IntegratedMeanBalances

/-- The removed angular moment is the actual defect derivative in (34). -/
theorem angular_bump_identity (P : Patch) (ε : ℝ)
    {v radialFlux axialFlux virtualFlux : MeanField}
    (hv : SmoothShell P.a P.b v) (hr : SmoothShell P.a P.b radialFlux)
    (hz : SmoothShell P.a P.b axialFlux) (hT : SmoothShell P.a P.b virtualFlux)
    (hmass : radialMoment 2 v = 0) (z : MeanPoint) :
    bumpCorrection P 2 (angularBalance ε v radialFlux axialFlux virtualFlux) z =
      momentDensity P 2 z.1 * (ε * fderiv ℝ (radialMoment 2 axialFlux) z.2 (0, 1)) := by
  unfold bumpCorrection mass
  rw [integrated_angular_balance ε hv hr hz hT hmass]

/-- Axial moment potential, given by `axialDefect axialFlux gr p + pressureCoefficient ρ p *
pressureTotal gr p`. -/
noncomputable def axialMomentPotential (axialFlux gr ρ : MeanField) (p : MeanParameter) : ℝ :=
  axialDefect axialFlux gr p + pressureCoefficient ρ p * pressureTotal gr p

theorem axialMomentPotential_contDiff (P : Patch) {axialFlux gr ρ : MeanField}
    (hz : SmoothShell P.a P.b axialFlux) (hg : SmoothShell P.a P.b gr)
    (hρ : SmoothShell P.a P.b ρ) : ContDiff ℝ ∞ (axialMomentPotential axialFlux gr ρ) := by
  have h1 := radialMoment_smooth hz.smooth hz.supported 1
  have h2 := radialMoment_smooth hg.smooth hg.supported 2
  have h3 := radialMoment_smooth hρ.smooth hρ.supported 2
  have h4 := radialMoment_smooth hg.smooth hg.supported 0
  exact (h1.sub (contDiff_const.mul h2)).add ((h3.div_const 2).mul h4)

/-- The pressure coefficient remains inside the actual slow derivative. -/
theorem axial_bump_identity (P : Patch) (ε : ℝ)
    {γ radialFlux axialFlux pressure virtualFlux gr ρ : MeanField}
    (hγ : SmoothShell P.a P.b γ) (hr : SmoothShell P.a P.b radialFlux)
    (hz : SmoothShell P.a P.b axialFlux) (hp : SmoothShell P.a P.b pressure)
    (hT : SmoothShell P.a P.b virtualFlux) (hg : SmoothShell P.a P.b gr)
    (hρ : SmoothShell P.a P.b ρ) (hmass : radialMoment 1 γ = 0)
    (hderiv : ∀ r p, deriv (fun s => pressure (s, p)) r =
      gr (r, p) - ρ (r, p) * pressureTotal gr p) (z : MeanPoint) :
    bumpCorrection P 1 (axialBalance ε γ radialFlux axialFlux pressure virtualFlux) z =
      momentDensity P 1 z.1 * (ε * fderiv ℝ (axialMomentPotential axialFlux gr ρ) z.2 (0, 1)) := by
  unfold bumpCorrection mass
  rw [integrated_axial_reconstructed ε hγ hr hz hp hT hg hρ hmass hderiv]
  rfl

/-- The axial bump identity with pressure supplied by the actual torus-averaged
compact pressure constructor, so no pressure moment or derivative is assumed. -/
theorem axial_bump_constructed_pressure_identity (P : Patch) {d M : ℝ}
    (hd : 0 < d) (ε : ℝ) (v : ℝ × ℝ)
    {f : PressureStream.Lift MeanParameter → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported P.a P.b f) (hper : PressureStream.TorusPeriodicLift f)
    {γ radialFlux axialFlux virtualFlux : MeanField}
    (hγ : SmoothShell P.a P.b γ) (hr : SmoothShell P.a P.b radialFlux)
    (hz : SmoothShell P.a P.b axialFlux) (hT : SmoothShell P.a P.b virtualFlux)
    (hmass : radialMoment 1 γ = 0) (z : MeanPoint) :
    bumpCorrection P 1 (axialBalance ε γ radialFlux axialFlux
      (reconstructedMeanPressure d P.a P.b M P.a_lt_b v f) virtualFlux) z =
      momentDensity P 1 z.1 * (ε * fderiv ℝ (axialMomentPotential axialFlux
        (averagedRadialSource f) (normalizedMeanDensity P.a P.b P.a_lt_b)) z.2 (0, 1)) :=
  axial_bump_identity P ε hγ hr hz
    (reconstructedMeanPressure_shell P.a_pos P.a_lt_b hd v hf hs) hT
    (averagedRadialSource_shell hf hs) (normalizedMeanDensity_shell P.a P.b P.a_lt_b)
    hmass (constructed_pressure_deriv P.a_pos P.a_lt_b hd v hf hs hper) z

theorem angular_bump_improvedClass (P : Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε slow : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hslow : ∀ n, 1 ≤ slow n)
    (α : ℝ) (v radialFlux axialFlux virtualFlux : ℕ → MeanField)
    (hv : ∀ n, SmoothShell P.a P.b (v n)) (hr : ∀ n, SmoothShell P.a P.b (radialFlux n))
    (hz : ∀ n, SmoothShell P.a P.b (axialFlux n)) (hT : ∀ n, SmoothShell P.a P.b (virtualFlux n))
    (hmass : ∀ n, radialMoment 2 (v n) = 0)
    (hclass : WeightedClasses.UnweightedClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      α (fun n (z : MeanPoint) => radialMoment 2 (axialFlux n) z.2)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      (α + 1) (fun n => bumpCorrection P 2
        (angularBalance (ε n) (v n) (radialFlux n) (axialFlux n) (virtualFlux n))) := by
  apply bump_improvedClass_of_moment_identity P 2 hcL hcR ε slow hε hε1 hslow α
    (fun n => angularBalance (ε n) (v n) (radialFlux n) (axialFlux n) (virtualFlux n))
    (fun n => radialMoment 2 (axialFlux n)) (0, 1)
    (fun n => radialMoment_smooth (hz n).smooth (hz n).supported 2) hclass
  exact fun n p => integrated_angular_balance (ε n) (hv n) (hr n) (hz n) (hT n) (hmass n) p

theorem axial_bump_improvedClass (P : Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε slow : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hslow : ∀ n, 1 ≤ slow n)
    (α : ℝ) (γ radialFlux axialFlux pressure virtualFlux gr ρ : ℕ → MeanField)
    (hγ : ∀ n, SmoothShell P.a P.b (γ n)) (hr : ∀ n, SmoothShell P.a P.b (radialFlux n))
    (hz : ∀ n, SmoothShell P.a P.b (axialFlux n)) (hp : ∀ n, SmoothShell P.a P.b (pressure n))
    (hT : ∀ n, SmoothShell P.a P.b (virtualFlux n)) (hg : ∀ n, SmoothShell P.a P.b (gr n))
    (hρ : ∀ n, SmoothShell P.a P.b (ρ n)) (hmass : ∀ n, radialMoment 1 (γ n) = 0)
    (hderiv : ∀ n r p, deriv (fun s => pressure n (s, p)) r =
      gr n (r, p) - ρ n (r, p) * pressureTotal (gr n) p)
    (hclass : WeightedClasses.UnweightedClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      α (fun n (z : MeanPoint) => axialMomentPotential (axialFlux n) (gr n) (ρ n) z.2)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      (α + 1) (fun n => bumpCorrection P 1
        (axialBalance (ε n) (γ n) (radialFlux n) (axialFlux n) (pressure n) (virtualFlux n))) := by
  apply bump_improvedClass_of_moment_identity P 1 hcL hcR ε slow hε hε1 hslow α
    (fun n => axialBalance (ε n) (γ n) (radialFlux n) (axialFlux n) (pressure n) (virtualFlux n))
    (fun n => axialMomentPotential (axialFlux n) (gr n) (ρ n)) (0, 1)
    (fun n => axialMomentPotential_contDiff P (hz n) (hg n) (hρ n)) hclass
  exact fun n p => integrated_axial_reconstructed (ε n) (hγ n) (hr n) (hz n) (hp n)
    (hT n) (hg n) (hρ n) (hmass n) (hderiv n) p

end IntegratedBalances

section ChartComparison

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_jet_bounds {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {K : Set X} (hK : IsCompact K)
    {f : X → Y} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (nat_le_smooth j)).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩
  choose C hC hbound using hb
  refine ⟨1 + ∑ j ∈ Finset.range (m + 1), C j, ?_, ?_⟩
  · have h := Finset.sum_nonneg (s := Finset.range (m + 1)) (fun j _ => hC j)
    linarith
  · intro j hj x hx
    have h := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    exact (hbound j x hx).trans (by linarith)

/-- Smooth coordinate changes and multipliers have actual finite-jet operator
bounds on compact sets; the bound is uniform over every input function. -/
theorem compact_change_jet_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Set X} (hK : IsCompact K) {a : X → ℝ} (ha : ContDiff ℝ ∞ a)
    {φ : X → X} (hφ : ContDiff ℝ ∞ φ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : X → ℝ, ContDiff ℝ ∞ f → ∀ x ∈ K, ∀ B : ℝ, 0 ≤ B →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (φ x)‖ ≤ B) → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (fun y => a y * f (φ y)) x‖ ≤ C * B := by
  obtain ⟨A, hA, haB⟩ := compact_jet_bounds hK ha m
  obtain ⟨L, hL, hφB⟩ := compact_jet_bounds hK hφ m
  let D : ℝ := (m.factorial : ℝ) * L ^ m
  have hD : 0 < D := mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) (pow_pos
      (zero_lt_one.trans_le hL) m)
  refine ⟨(2 : ℝ) ^ m * A * D, by positivity, ?_⟩
  intro f hf x hx B hB hfb j hj
  have hcomp : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f ∘ φ) x‖ ≤ D * B := by
    intro i hi
    have h := norm_iteratedFDeriv_comp_le hf hφ (nat_le_smooth i) x
      (fun k hk => hfb k (hk.trans hi)) (D := L)
      (fun k hk hki => (hφB k (hki.trans hi) x hx).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hL hk))
    apply h.trans
    have hfac : (i.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hi
    calc
      _ ≤ (m.factorial : ℝ) * B * L ^ m := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hfac hB) (pow_le_pow_right₀ hL hi)
          (pow_nonneg (zero_le_one.trans hL) _) (mul_nonneg (Nat.cast_nonneg _) hB)
      _ = D * B := by dsimp [D]; ring
  have h := ParametricKernelBounds.norm_iteratedFDeriv_mul_le_of_bounds ha (hf.comp hφ) j x
    (zero_le_one.trans hA) (mul_nonneg hD.le hB)
    (fun i hi => haB i (hi.trans hj) x hx) (fun i hi => hcomp i (hi.trans hj))
  have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  rw [hsum] at h
  apply h.trans
  calc
    _ ≤ (2 : ℝ) ^ m * A * (D * B) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (zero_le_one.trans hA))
        (mul_nonneg hD.le hB)
    _ = _ := by ring

/-- Change chart, given by `ρ z.2 ^ (-2 * A) * F (z.1 / Real.sqrt (ρ z.2), z.2)`. -/
noncomputable def changeChart (ρ : E → ℝ) (A : ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  ρ z.2 ^ (-2 * A) * F (z.1 / Real.sqrt (ρ z.2), z.2)
/-- Inverse change chart, given by `ρ z.2 ^ (2 * A) * F (Real.sqrt (ρ z.2) * z.1, z.2)`. -/
noncomputable def inverseChangeChart (ρ : E → ℝ) (A : ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  ρ z.2 ^ (2 * A) * F (Real.sqrt (ρ z.2) * z.1, z.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem changeChart_inverse {ρ : E → ℝ} (hρ : ∀ p, 0 < ρ p) (A : ℝ) (F : ℝ × E → ℝ) :
    changeChart ρ A (inverseChangeChart ρ A F) = F ∧
      inverseChangeChart ρ A (changeChart ρ A F) = F := by
  constructor
  · funext z
    simp only [changeChart, inverseChangeChart,
      mul_div_cancel₀ z.1 (Real.sqrt_pos.mpr (hρ z.2)).ne']
    rw [← mul_assoc, ← Real.rpow_add (hρ z.2)]
    simp []
  · funext z
    simp only [changeChart, inverseChangeChart,
      mul_div_cancel_left₀ z.1 (Real.sqrt_pos.mpr (hρ z.2)).ne']
    rw [← mul_assoc, ← Real.rpow_add (hρ z.2)]
    simp []

/-- Both directions of the q/Q chart comparison have uniform finite-jet
operator bounds. The positive ratio and all its derivatives are bounded by
compactness, rather than postulated bounds on the transformed stress. -/
theorem chart_change_finiteJets {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ p, 0 < ρ p)
    (A : ℝ) {K : Set (ℝ × E)} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : ℝ × E → ℝ, ContDiff ℝ ∞ F → ∀ z ∈ K, ∀ B : ℝ, 0 ≤ B →
      ((∀ i ≤ m, ‖iteratedFDeriv ℝ i F (z.1 / Real.sqrt (ρ z.2), z.2)‖ ≤ B) →
        ∀ j ≤ m, ‖iteratedFDeriv ℝ j (changeChart ρ A F) z‖ ≤ C * B) ∧
      ((∀ i ≤ m, ‖iteratedFDeriv ℝ i F (Real.sqrt (ρ z.2) * z.1, z.2)‖ ≤ B) →
        ∀ j ≤ m, ‖iteratedFDeriv ℝ j (inverseChangeChart ρ A F) z‖ ≤ C * B) := by
  have hs : ContDiff ℝ ∞ (fun z : ℝ × E => Real.sqrt (ρ z.2)) :=
    (hρ.comp contDiff_snd).sqrt (fun z => (hpos z.2).ne')
  have ha : ContDiff ℝ ∞ (fun z : ℝ × E => ρ z.2 ^ (-2 * A)) :=
    (hρ.comp contDiff_snd).rpow_const_of_ne (fun z => (hpos z.2).ne')
  have hb : ContDiff ℝ ∞ (fun z : ℝ × E => ρ z.2 ^ (2 * A)) :=
    (hρ.comp contDiff_snd).rpow_const_of_ne (fun z => (hpos z.2).ne')
  have hφ : ContDiff ℝ ∞ (fun z : ℝ × E => (z.1 / Real.sqrt (ρ z.2), z.2)) :=
    (contDiff_fst.div hs (fun z => (Real.sqrt_pos.mpr (hpos z.2)).ne')).prodMk contDiff_snd
  have hψ : ContDiff ℝ ∞ (fun z : ℝ × E => (Real.sqrt (ρ z.2) * z.1, z.2)) :=
    (hs.mul contDiff_fst).prodMk contDiff_snd
  obtain ⟨C1, hC1, h1⟩ := compact_change_jet_bound hK ha hφ m
  obtain ⟨C2, hC2, h2⟩ := compact_change_jet_bound hK hb hψ m
  refine ⟨C1 + C2, add_pos hC1 hC2, ?_⟩
  intro F hF z hz B hB
  constructor
  · intro hfb j hj
    exact (h1 F hF z hz B hB hfb j hj).trans (mul_le_mul_of_nonneg_right (by linarith) hB)
  · intro hfb j hj
    exact (h2 F hF z hz B hB hfb j hj).trans (mul_le_mul_of_nonneg_right (by linarith) hB)

theorem fixedQ_tensor_common_ratio (P : Patch) (e : ℕ) {ρ : E → ℝ} (hρ : ∀ p, 0 < ρ p)
    {Q : ℝ} (hQ : 0 < Q) (A : ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) :
    Q ^ (2 * A) * physicalSigma P e (fun p => Q * ρ p) F (Real.sqrt Q * z.1, z.2) =
      changeChart ρ A (sigma P e (normalizedResidual (fun p => Q * ρ p) A F)) z := by
  rw [fixedQ_tensor_identity P e (fun p => mul_pos hQ (hρ p)) hQ A F z.1 z.2]
  have hr : Q / (Q * ρ z.2) = (ρ z.2)⁻¹ := by field_simp [hQ.ne', (hρ z.2).ne']
  have hs : Real.sqrt Q / Real.sqrt (Q * ρ z.2) = (Real.sqrt (ρ z.2))⁻¹ := by
    rw [Real.sqrt_mul hQ.le]
    field_simp [(Real.sqrt_pos.mpr hQ).ne', (Real.sqrt_pos.mpr (hρ z.2)).ne']
  rw [hr, hs, Real.inv_rpow (hρ z.2).le, ← Real.rpow_neg (hρ z.2).le]
  unfold changeChart
  congr 2
  · ring
  · ring_nf

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem fixedQ_density_common_ratio (P : Patch) (e : ℕ) {ρ : E → ℝ}
    (hρ : ∀ p, 0 < ρ p) {Q : ℝ} (hQ : 0 < Q) (z : ℝ × E) :
    Real.sqrt Q ^ (e + 1) *
      physicalDensity P e (fun p => Q * ρ p) (Real.sqrt Q * z.1, z.2) =
      physicalDensity P e ρ z := by
  rw [fixedQ_density_identity]
  have hs : Real.sqrt Q / Real.sqrt (Q * ρ z.2) = (Real.sqrt (ρ z.2))⁻¹ := by
    rw [Real.sqrt_mul hQ.le]
    field_simp [(Real.sqrt_pos.mpr hQ).ne', (Real.sqrt_pos.mpr (hρ z.2)).ne']
  rw [hs, inv_pow]
  simp only [physicalDensity, lengthScale, div_eq_mul_inv, mul_comm]

/-- For a fixed smooth positive ratio q/Q, every derivative of the
length-normalized physical bump is bounded independently of the band Q. -/
theorem fixedQ_density_finiteJets (P : Patch) (e : ℕ) {ρ : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ p, 0 < ρ p)
    {K : Set (ℝ × E)} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 0 < Q → ∀ i ≤ m, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ i (fun y : ℝ × E => Real.sqrt Q ^ (e + 1) *
        physicalDensity P e (fun p => Q * ρ p) (Real.sqrt Q * y.1, y.2)) z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_jet_bounds hK (physicalDensity_contDiff P e hρ hpos) m
  refine ⟨C, zero_lt_one.trans_le hC, ?_⟩
  intro Q hQ i hi z hz
  have he : (fun y : ℝ × E => Real.sqrt Q ^ (e + 1) *
      physicalDensity P e (fun p => Q * ρ p) (Real.sqrt Q * y.1, y.2)) =
      physicalDensity P e ρ := by
    funext y
    exact fixedQ_density_common_ratio P e hpos hQ y
  rw [he]
  exact hb i hi z hz

end ChartComparison

end NavierStokes.SignedStressPrimitive
