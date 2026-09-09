/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AssembledSlowBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.LeadingStress

@[expose] public section

/-!
# The canonical zeroth stress is the explicit leading stress

The weighted stresses have regular primitives through the axis. Their actual
derivatives are the negative weighted residuals, so the lower integration
endpoint fixes the constant and identifies the constructed stress.
-/

noncomputable section

namespace NavierStokes.ZerothStressIdentity

open Set Filter MeasureTheory ProfileHistories
open SimilarityProfile (InnerPoint InnerProfile partialX partialEta T Z)
open SlowExpansionResidual
open scoped Topology ContDiff BigOperators


variable {Ω : RadialDomain} (P : Profiles Ω)

noncomputable def leadingProfiles (h C : ℝ) : SlowProfiles where
  phi := NaturalCoefficientBridge.zeroSequence (fun w => C * P.f w)
  axial := NaturalCoefficientBridge.zeroSequence P.U
  flux := NaturalCoefficientBridge.zeroSequence (SlowDivergence.radialFlux h 0 P.U)
  pressure := NaturalCoefficientBridge.zeroSequence P.pressure

theorem T_const_mul (h b C : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f w) : T h b (fun p => C * f p) w = C * T h b f w := by
  simp only [T, CoordinateAlgebra.timeCoeff,
    NaturalCoefficientBridge.partialX_const_mul C hf,
    NaturalCoefficientBridge.partialEta_const_mul C hf]
  ring

theorem Z_const_mul (h b C : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f w) : Z h b (fun p => C * f p) w = C * Z h b f w := by
  simp only [Z, CoordinateAlgebra.axialCoeff,
    NaturalCoefficientBridge.partialX_const_mul C hf,
    NaturalCoefficientBridge.partialEta_const_mul C hf]
  ring

theorem leading_angular_coefficient (h C : ℝ) {w : InnerPoint} (hw : w ∈ Ω.carrier)
    (hX : w.1 ≠ 0) (hf : P.f w ≠ 0) (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    angularCoefficient h (leadingProfiles P h C) 0 w =
      C * (-P.f w * LeadingStress.sourceTheta P h w / CoordinateAlgebra.L h w.2 -
        2 * (w.1 * partialX (partialX P.f) w + 2 * partialX P.f w)) := by
  have hs := P.f_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)
  have hd := hs.differentiableAt (by simp)
  rw [NaturalCoefficientBridge.angular_zero_formula]
  simp only [leadingProfiles, NaturalCoefficientBridge.zeroSequence, ↓reduceIte,
    T_const_mul h (angularExponent h) C hd, Z_const_mul h (angularExponent h) C hd,
    NaturalCoefficientBridge.partialX_const_mul C hd, NaturalCoefficientBridge.secondX_const_mul C
      hs]
  have he := LeadingStress.theta_transport_coefficient P h hw hX hf hL
  simp only [angularExponent] at ⊢
  linear_combination C * he

theorem leading_axial_coefficient (h C : ℝ) {w : InnerPoint} (hw : w ∈ Ω.carrier)
    (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    axialCoefficient h (leadingProfiles P h C) 0 w =
      -LeadingStress.sourceAxial P h w / CoordinateAlgebra.L h w.2 -
        2 * (w.1 * partialX (partialX P.U) w + partialX P.U w) := by
  rw [NaturalCoefficientBridge.axial_zero_formula]
  simp only [leadingProfiles, NaturalCoefficientBridge.zeroSequence, ↓reduceIte]
  have he := LeadingStress.axial_transport_coefficient P h hw hL
  simp only [axialExponent, pressureExponent] at ⊢
  linear_combination he

/-- Regular formula for R² times the angular stress, with no inverse X. -/
noncomputable def weightedTheta (h R eta : ℝ) : ℝ :=
  primitive (P.angularSource h) (R ^ 2 / 2, eta) / CoordinateAlgebra.L h eta +
    R ^ 4 * partialX P.f (R ^ 2 / 2, eta)

/-- Regular formula for R times the axial stress. -/
noncomputable def weightedAxial (h R eta : ℝ) : ℝ :=
  primitive (P.axialSource h) (R ^ 2 / 2, eta) / CoordinateAlgebra.L h eta +
    R ^ 2 * partialX P.U (R ^ 2 / 2, eta)

@[simp] theorem weightedTheta_zero (h eta : ℝ) : weightedTheta P h 0 eta = 0 := by
  simp [weightedTheta, primitive_at_axis]

@[simp] theorem weightedAxial_zero (h eta : ℝ) : weightedAxial P h 0 eta = 0 := by
  simp [weightedAxial, primitive_at_axis]

theorem square_half_hasDerivAt (R : ℝ) : HasDerivAt (fun r : ℝ => r ^ 2 / 2) R R := by
  convert! ((hasDerivAt_id R).pow 2).div_const 2 using 1
  simp only [id_eq]
  ring

theorem weightedTheta_hasDerivAt (h : ℝ) {R eta : ℝ}
    (hw : (R ^ 2 / 2, eta) ∈ Ω.carrier) :
    HasDerivAt (fun r => weightedTheta P h r eta)
      (R * P.angularSource h (R ^ 2 / 2, eta) / CoordinateAlgebra.L h eta +
        4 * R ^ 3 * partialX P.f (R ^ 2 / 2, eta) +
        R ^ 5 * partialX (partialX P.f) (R ^ 2 / 2, eta)) R := by
  have hprim := (primitive_hasDerivAt Ω (P.angularSource_smooth h) hw).comp R
    (square_half_hasDerivAt R)
  have hfx := (LeadingStress.partialX_hasDerivAt
    (((radialPartial_smooth Ω P.f_smooth).contDiffAt (Ω.isOpen.mem_nhds hw)).differentiableAt (by
      simp))).comp R
      (square_half_hasDerivAt R)
  change HasDerivAt ((fun x => partialX P.f (x, eta)) ∘ fun r => r ^ 2 / 2)
    (partialX (partialX P.f) (R ^ 2 / 2, eta) * R) R at hfx
  have hd := (hprim.div_const (CoordinateAlgebra.L h eta)).add (((hasDerivAt_id R).pow 4).mul hfx)
  convert! hd using 1
  dsimp [weightedTheta, Function.comp_def]
  ring

theorem weightedAxial_hasDerivAt (h : ℝ) {R eta : ℝ}
    (hw : (R ^ 2 / 2, eta) ∈ Ω.carrier) :
    HasDerivAt (fun r => weightedAxial P h r eta)
      (R * P.axialSource h (R ^ 2 / 2, eta) / CoordinateAlgebra.L h eta +
        2 * R * partialX P.U (R ^ 2 / 2, eta) +
        R ^ 3 * partialX (partialX P.U) (R ^ 2 / 2, eta)) R := by
  have hprim := (primitive_hasDerivAt Ω (P.axialSource_smooth h) hw).comp R (square_half_hasDerivAt
    R)
  have hux := (LeadingStress.partialX_hasDerivAt
    (((radialPartial_smooth Ω P.U_smooth).contDiffAt (Ω.isOpen.mem_nhds hw)).differentiableAt (by
      simp))).comp R
      (square_half_hasDerivAt R)
  change HasDerivAt ((fun x => partialX P.U (x, eta)) ∘ fun r => r ^ 2 / 2)
    (partialX (partialX P.U) (R ^ 2 / 2, eta) * R) R at hux
  have hd := (hprim.div_const (CoordinateAlgebra.L h eta)).add (((hasDerivAt_id R).pow 2).mul hux)
  convert! hd using 1
  dsimp [weightedAxial, Function.comp_def]
  ring

theorem weightedTheta_eq (h : ℝ) {R eta : ℝ} (hR : 0 < R)
    (hf : P.f (R ^ 2 / 2, eta) ≠ 0) (hL : CoordinateAlgebra.L h eta ≠ 0) :
    weightedTheta P h R eta = R ^ 2 * LeadingStress.theta P h (R ^ 2 / 2, eta) := by
  unfold weightedTheta LeadingStress.theta Profiles.angularLag Profiles.H
  dsimp only
  field_simp

theorem weightedAxial_eq (h : ℝ) {R eta : ℝ} (hR : 0 < R)
    (hL : CoordinateAlgebra.L h eta ≠ 0) :
    weightedAxial P h R eta = R * LeadingStress.axial P h (R ^ 2 / 2, eta) := by
  unfold weightedAxial LeadingStress.axial Profiles.axialLag
  dsimp only
  rw [show 2 * (R ^ 2 / 2) = R ^ 2 by ring, Real.sqrt_sq hR.le]
  field_simp ; ring

theorem leading_thetaDensity (h C : ℝ) (hC : C ≠ 0) {R eta : ℝ} (hR : 0 < R)
    (hw : (R ^ 2 / 2, eta) ∈ Ω.carrier) (hf : P.f (R ^ 2 / 2, eta) ≠ 0)
    (hL : CoordinateAlgebra.L h eta ≠ 0) :
    SlowResidualMatching.thetaDensity h C (leadingProfiles P h C) 0 (R, eta) =
      -(R * P.angularSource h (R ^ 2 / 2, eta) / CoordinateAlgebra.L h eta +
        4 * R ^ 3 * partialX P.f (R ^ 2 / 2, eta) +
        R ^ 5 * partialX (partialX P.f) (R ^ 2 / 2, eta)) := by
  unfold SlowResidualMatching.thetaDensity SlowResidualMatching.radiusPoint
  rw [leading_angular_coefficient P h C hw (by positivity) hf hL]
  unfold LeadingStress.sourceTheta Profiles.H
  dsimp only
  field_simp ; ring

theorem leading_zDensity (h C : ℝ) {R eta : ℝ}
    (hw : (R ^ 2 / 2, eta) ∈ Ω.carrier) (hL : CoordinateAlgebra.L h eta ≠ 0) :
    SlowResidualMatching.zDensity h (leadingProfiles P h C) 0 (R, eta) =
      -(R * P.axialSource h (R ^ 2 / 2, eta) / CoordinateAlgebra.L h eta +
        2 * R * partialX P.U (R ^ 2 / 2, eta) +
        R ^ 3 * partialX (partialX P.U) (R ^ 2 / 2, eta)) := by
  unfold SlowResidualMatching.zDensity SlowResidualMatching.radiusPoint
  rw [leading_axial_coefficient P h C hw hL]
  unfold LeadingStress.sourceAxial
  dsimp only
  ring

/-- FTC determines the constant of the canonical negative primitive from
the actual zero-axis value of the weighted potential. -/
theorem stress_eq_of_weighted_derivative (m : ℕ) (F : InnerProfile) (G : ℝ → ℝ)
    {R eta : ℝ} (hR : 0 < R) (hG : ContinuousOn G (Icc 0 R)) (hG0 : G 0 = 0)
    (hD : ∀ r ∈ Ioo 0 R, HasDerivAt G (-F (r, eta)) r)
    (hF : IntervalIntegrable (fun r => F (r, eta)) volume 0 R) :
    SlowStressSupport.stress m F (R, eta) = G R / R ^ m := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le hG hD hF.neg
  rw [intervalIntegral.integral_neg, hG0, sub_zero] at hi
  rw [SlowStressSupport.stress_of_pos m F hR]
  change -(∫ r in (0 : ℝ)..R, F (r, eta)) / R ^ m = _
  rw [hi]

theorem weightedTheta_continuous (h : ℝ) {eta : ℝ}
    (hD : ∀ X, 0 ≤ X → (X, eta) ∈ Ω.carrier) :
    Continuous (fun R => weightedTheta P h R eta) := by
  apply continuous_iff_continuousAt.mpr
  intro R
  exact (weightedTheta_hasDerivAt P h (hD (R ^ 2 / 2) (by positivity))).continuousAt

theorem weightedAxial_continuous (h : ℝ) {eta : ℝ}
    (hD : ∀ X, 0 ≤ X → (X, eta) ∈ Ω.carrier) :
    Continuous (fun R => weightedAxial P h R eta) := by
  apply continuous_iff_continuousAt.mpr
  intro R
  exact (weightedAxial_hasDerivAt P h (hD (R ^ 2 / 2) (by positivity))).continuousAt

/-! ## A scheme whose actual order-zero fields come from P -/

theorem scheme_leading_germs {S : Set ℝ} {h C : ℝ}
    (s : GlobalSlowProfiles.Scheme S h C)
    (hD : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ Ω.carrier)
    (hbase : s.base = AssembledSlowBase.baseFields s.domain C P hD)
    {p : InnerPoint} (hX : 0 < p.1) (heta : p.2 ∈ S) :
    (GlobalSlowProfiles.asSlowProfiles s).phi 0 =ᶠ[𝓝 p] (leadingProfiles P h C).phi 0 ∧
    (GlobalSlowProfiles.asSlowProfiles s).axial 0 =ᶠ[𝓝 p] (leadingProfiles P h C).axial 0 ∧
    (GlobalSlowProfiles.asSlowProfiles s).flux 0 =ᶠ[𝓝 p] (leadingProfiles P h C).flux 0 ∧
    (GlobalSlowProfiles.asSlowProfiles s).pressure 0 =ᶠ[𝓝 p] (leadingProfiles P h C).pressure 0 :=
      by
  have hn := (isOpen_Ioi.prod s.domain.isOpen).mem_nhds (show p ∈ Ioi 0 ×ˢ S from ⟨hX, heta⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hn] with q hq
    change GlobalSlowProfiles.xProfile (GlobalSlowProfiles.profiles s 0).phi q = C * P.f q
    rw [GlobalSlowProfiles.profiles_zero, hbase]
    exact AssembledSlowBase.baseFields_phi s.domain C P hD hq.1.le
  · filter_upwards [hn] with q hq
    change GlobalSlowProfiles.xProfile (GlobalSlowProfiles.profiles s 0).axial q = P.U q
    rw [GlobalSlowProfiles.profiles_zero, hbase]
    exact AssembledSlowBase.baseFields_axial s.domain C P hD hq.1.le
  · filter_upwards [hn] with q hq
    change q.1 * GlobalSlowProfiles.xProfile (GlobalSlowProfiles.profiles s 0).beta q =
      SlowDivergence.radialFlux h 0 P.U q
    rw [GlobalSlowProfiles.profiles_zero, hbase,
      AssembledSlowBase.baseFields_beta_value s.domain C P hD hq.1 hq.2]
    have hqX : 0 < q.1 := hq.1
    field_simp [hqX.ne']
  · filter_upwards [hn] with q hq
    change GlobalSlowProfiles.xProfile (GlobalSlowProfiles.profiles s 0).pressure q = P.pressure q
    rw [GlobalSlowProfiles.profiles_zero, hbase]
    exact AssembledSlowBase.baseFields_pressure s.domain C P hD hq.1.le

theorem scheme_zero_coefficients_eq {S : Set ℝ} {h C : ℝ}
    (s : GlobalSlowProfiles.Scheme S h C)
    (hD : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ Ω.carrier)
    (hbase : s.base = AssembledSlowBase.baseFields s.domain C P hD)
    {p : InnerPoint} (hX : 0 < p.1) (heta : p.2 ∈ S) :
    angularCoefficient h (GlobalSlowProfiles.asSlowProfiles s) 0 p =
        angularCoefficient h (leadingProfiles P h C) 0 p ∧
    axialCoefficient h (GlobalSlowProfiles.asSlowProfiles s) 0 p =
        axialCoefficient h (leadingProfiles P h C) 0 p := by
  have he := scheme_leading_germs P s hD hbase hX heta
  have hphi : ∀ j ≤ 0, (GlobalSlowProfiles.asSlowProfiles s).phi j =ᶠ[𝓝 p]
      (leadingProfiles P h C).phi j := by
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    simpa only [hj0] using he.1
  have hu : ∀ j ≤ 0, (GlobalSlowProfiles.asSlowProfiles s).axial j =ᶠ[𝓝 p]
      (leadingProfiles P h C).axial j := by
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    simpa only [hj0] using he.2.1
  have hv : ∀ j ≤ 0, (GlobalSlowProfiles.asSlowProfiles s).flux j =ᶠ[𝓝 p]
      (leadingProfiles P h C).flux j := by
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    simpa only [hj0] using he.2.2.1
  exact ⟨SlowResidualMatching.angularCoefficient_congr_germ h 0 hv hu hphi,
    SlowResidualMatching.axialCoefficient_congr_germ h 0 hv hu he.2.2.2⟩

theorem scheme_zero_densities_eq {S : Set ℝ} {h C : ℝ}
    (s : GlobalSlowProfiles.Scheme S h C)
    (hD : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ Ω.carrier)
    (hbase : s.base = AssembledSlowBase.baseFields s.domain C P hD)
    (R : ℝ) {eta : ℝ} (heta : eta ∈ S) :
    SlowResidualMatching.thetaDensity h C (GlobalSlowProfiles.asSlowProfiles s) 0 (R, eta) =
        SlowResidualMatching.thetaDensity h C (leadingProfiles P h C) 0 (R, eta) ∧
    SlowResidualMatching.zDensity h (GlobalSlowProfiles.asSlowProfiles s) 0 (R, eta) =
        SlowResidualMatching.zDensity h (leadingProfiles P h C) 0 (R, eta) := by
  by_cases hR : R = 0
  · subst R
    simp [SlowResidualMatching.thetaDensity, SlowResidualMatching.zDensity]
  have he := scheme_zero_coefficients_eq P s hD hbase (p := (R ^ 2 / 2, eta))
    (div_pos (sq_pos_of_ne_zero hR) (by norm_num)) heta
  simp only [SlowResidualMatching.thetaDensity, SlowResidualMatching.zDensity,
    SlowResidualMatching.radiusPoint, he.1, he.2, and_self]

section Canonical

variable {S : Set ℝ} {h C rho core : ℝ} {U : Set ℂ}
  {base : Fin 5 → InnerProfile} {s : GlobalSlowProfiles.Scheme S h C}
  {A : SlowRecursion.LocalHierarchy rho U h C base}
  (L : GlobalSlowProfiles.Localization s A core)
  (B0 : GlobalSlowProfiles.BaseAgreement s A core)
  (Z0 : AssembledSlowBase.ZeroOrderSolved s core)

include L B0 Z0

theorem raw_stresses_eq
    (hD : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ Ω.carrier)
    (hbase : s.base = AssembledSlowBase.baseFields s.domain C P hD)
    {R eta : ℝ} (hR : 0 < R) (heta : eta ∈ S)
    (hf : ∀ X, 0 < X → X ≤ R ^ 2 / 2 → P.f (X, eta) ≠ 0) :
    SlowStressSupport.stress 2
        (SlowResidualMatching.thetaDensity h C (GlobalSlowProfiles.asSlowProfiles s) 0) (R, eta) =
      LeadingStress.theta P h (R ^ 2 / 2, eta) ∧
    SlowStressSupport.stress 1
        (SlowResidualMatching.zDensity h (GlobalSlowProfiles.asSlowProfiles s) 0) (R, eta) =
      LeadingStress.axial P h (R ^ 2 / 2, eta) := by
  have hL : CoordinateAlgebra.L h eta ≠ 0 := s.domain.denominator eta heta
  have hslice : ∀ X, 0 ≤ X → (X, eta) ∈ Ω.carrier := fun X hX => hD X hX eta heta
  constructor
  · have hd : ∀ r ∈ Ioo 0 R, HasDerivAt (fun t => weightedTheta P h t eta)
        (-SlowResidualMatching.thetaDensity h C (GlobalSlowProfiles.asSlowProfiles s) 0 (r, eta)) r
          := by
      intro r hr
      have hrpos : 0 < r := hr.1
      have hxr : r ^ 2 / 2 ≤ R ^ 2 / 2 :=
        div_le_div_of_nonneg_right ((sq_le_sq₀ hr.1.le hR.le).2 hr.2.le) (by norm_num)
      have hden := (scheme_zero_densities_eq P s hD hbase r heta).1.trans
        (leading_thetaDensity P h C s.nonzero_scale hr.1
          (hslice _ (by positivity)) (hf _ (by positivity) hxr) hL)
      rw [hden, neg_neg]
      exact weightedTheta_hasDerivAt P h (hslice _ (by positivity))
    have he := stress_eq_of_weighted_derivative 2
      (SlowResidualMatching.thetaDensity h C (GlobalSlowProfiles.asSlowProfiles s) 0)
      (fun r => weightedTheta P h r eta) hR
      (weightedTheta_continuous P h hslice).continuousOn (weightedTheta_zero P h eta) hd
      ((SlowStressSupport.slice_smooth (AssembledSlowBase.thetaDensity_smooth L B0 Z0 0)
        heta).continuous.intervalIntegrable 0 R)
    rw [he]
    change weightedTheta P h R eta / R ^ 2 = _
    rw [weightedTheta_eq P h hR (hf _ (by positivity) le_rfl) hL]
    field_simp
  · have hd : ∀ r ∈ Ioo 0 R, HasDerivAt (fun t => weightedAxial P h t eta)
        (-SlowResidualMatching.zDensity h (GlobalSlowProfiles.asSlowProfiles s) 0 (r, eta)) r := by
      intro r hr
      have hden := (scheme_zero_densities_eq P s hD hbase r heta).2.trans
        (leading_zDensity P h C (hslice _ (by positivity)) hL)
      rw [hden, neg_neg]
      exact weightedAxial_hasDerivAt P h (hslice _ (by positivity))
    have he := stress_eq_of_weighted_derivative 1
      (SlowResidualMatching.zDensity h (GlobalSlowProfiles.asSlowProfiles s) 0)
      (fun r => weightedAxial P h r eta) hR
      (weightedAxial_continuous P h hslice).continuousOn (weightedAxial_zero P h eta) hd
      ((SlowStressSupport.slice_smooth (AssembledSlowBase.zDensity_smooth L B0 Z0 0)
        heta).continuous.intervalIntegrable 0 R)
    rw [he]
    change weightedAxial P h R eta / R ^ 1 = _
    rw [weightedAxial_eq P h hR hL]
    field_simp

/-- The actual extended stress slots equal the literal leading stress pair.
The only nonvanishing condition is on the fixed radial slice being evaluated. -/
theorem coefficients_stress_zero_eq (hI : Icc (-1 : ℝ) 1 ⊆ S)
    (hD : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ Ω.carrier)
    (hbase : s.base = AssembledSlowBase.baseFields s.domain C P hD)
    {p : InnerPoint} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1)
    (hf : ∀ X, 0 < X → X ≤ p.1 → P.f (X, p.2) ≠ 0) :
    (AssembledSlowBase.coefficients L B0 Z0 hI).stressTheta 0 p = LeadingStress.theta P h p ∧
      (AssembledSlowBase.coefficients L B0 Z0 hI).stressAxial 0 p = LeadingStress.axial P h p := by
  have hc := AssembledSlowBase.coefficients_stress_eq L B0 Z0 hI 0 hX heta
  rcases p with ⟨X, eta⟩
  dsimp only at hX heta hf hc ⊢
  by_cases hzero : X = 0
  · subst X
    constructor
    · rw [hc.1]
      simp [SlowResidualMatching.thetaStress, SlowResidualMatching.fromRadius,
        SlowStressSupport.stress, LeadingStress.theta]
    · rw [hc.2]
      simp [SlowResidualMatching.zStress, SlowResidualMatching.fromRadius,
        SlowStressSupport.stress, LeadingStress.axial]
  have hXp : 0 < X := lt_of_le_of_ne hX (Ne.symm hzero)
  let R := Real.sqrt (2 * X)
  have hR : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hR2 : R ^ 2 / 2 = X := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hs := raw_stresses_eq P L B0 Z0 hD hbase hR (hI (abs_le.mp heta))
    (fun Y hY hYX => hf Y hY (by simpa only [hR2] using hYX))
  constructor
  · rw [hc.1]
    change SlowStressSupport.stress 2 _ (R, eta) = _
    simpa only [hR2] using hs.1
  · rw [hc.2]
    change SlowStressSupport.stress 1 _ (R, eta) = _
    simpa only [hR2] using hs.2

end Canonical

end NavierStokes.ZerothStressIdentity
