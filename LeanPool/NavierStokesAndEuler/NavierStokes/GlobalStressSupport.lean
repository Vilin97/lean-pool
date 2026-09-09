/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AssembledSlowBase

@[expose] public section

/-!
# Stress confinement for the coherent repaired slow sequence

The five rows constructed by `GlobalSlowProfiles` imply the two actual
conservative residual integrals vanish.  Their negative radial primitives
therefore vanish past the same outer radius, uniformly over positive orders
`n ≥ 2`.  The preceding angular coefficient then has an ordinary repaired
moment; no renormalized order-zero moment is used in this module.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokes.GlobalStressSupport

open GlobalSlowProfiles

/-- The actual axial coefficients pulled back from `X` to signed radius. -/
noncomputable def axialHistory {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) : Field :=
  SlowResidualMatching.toRadius ((asSlowProfiles s).axial n)

/-- The actual angular velocity coefficients in signed radius. -/
noncomputable def angularHistory {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) : Field :=
  SlowResidualMatching.swirlRadius C ((asSlowProfiles s).phi n)

/-- The divergence variable is `V = X β = R² β/2`. -/
noncomputable def fluxHistory {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) : Field :=
  SlowResidualMatching.toRadius ((asSlowProfiles s).flux n)

noncomputable def pressureField {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) : Field :=
  SlowResidualMatching.toRadius ((asSlowProfiles s).pressure n)

/-- The full preceding radial residual, including both viscous terms. -/
noncomputable def previousOmega {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    (w : ℝ × ℝ) : ℝ :=
  w.1 ^ 2 / 2 * previousOmegaDivX s.domain
    (fun j => (profiles s j).axial) (fun j => (profiles s j).beta) n w

theorem toRadius_xProfile {S : Set ℝ} (f : EvenProfile S) {w : ℝ × ℝ}
    (hw : w.2 ∈ S) : SlowResidualMatching.toRadius (xProfile f) w = f w := by
  change f (Real.sqrt (2 * (w.1 ^ 2 / 2)), w.2) = f (w.1, w.2)
  rw [show 2 * (w.1 ^ 2 / 2) = w.1 ^ 2 by ring, Real.sqrt_sq_eq_abs]
  rcases le_total 0 w.1 with hp | hn
  · rw [abs_of_nonneg hp]
  · rw [abs_of_nonpos hn, f.even hw]

theorem axialHistory_eq {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) : axialHistory s n w = (profiles s n).axial w :=
  toRadius_xProfile _ hw

theorem angularHistory_eq {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) : angularHistory s n w = angularField C (profiles s n).phi w := by
  change w.1 / C * SlowResidualMatching.toRadius (xProfile (profiles s n).phi) w = _
  rw [toRadius_xProfile _ hw]
  rfl

theorem fluxHistory_eq {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) : fluxHistory s n w = w.1 ^ 2 / 2 * (profiles s n).beta w := by
  change w.1 ^ 2 / 2 * SlowResidualMatching.toRadius (xProfile (profiles s n).beta) w = _
  rw [toRadius_xProfile _ hw]

theorem pressureField_eq {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) : pressureField s n w = (profiles s n).pressure w :=
  toRadius_xProfile _ hw

theorem axialHistory_smooth {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    Smooth S (axialHistory s n) :=
  (profiles s n).axial.smooth.congr (fun _ hw => axialHistory_eq s n hw.2)

theorem angularHistory_smooth {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    Smooth S (angularHistory s n) :=
  (angularField_smooth C (profiles s n).phi).congr
    (fun _ hw => angularHistory_eq s n hw.2)

theorem fluxHistory_smooth {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    Smooth S (fluxHistory s n) :=
  (((contDiffOn_fst.pow 2).div_const 2).mul (profiles s n).beta.smooth).congr
    (fun _ hw => fluxHistory_eq s n hw.2)

theorem pressureField_smooth {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    Smooth S (pressureField s n) :=
  (profiles s n).pressure.smooth.congr (fun _ hw => pressureField_eq s n hw.2)

theorem axialHistory_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    SlowStressSupport.exterior s.B S (axialHistory s n) := by
  intro eta heta R hR
  rw [axialHistory_eq s n heta]
  exact profiles_axial_exterior s n eta heta R hR

theorem angularHistory_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 0 < n) : SlowStressSupport.exterior s.B S (angularHistory s n) := by
  intro eta heta R hR
  rw [angularHistory_eq s n heta]
  simp only [angularField, profiles_phi_exterior s hn eta heta R hR, mul_zero]

theorem fluxHistory_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    SlowStressSupport.exterior s.B S (fluxHistory s n) := by
  intro eta heta R hR
  rw [fluxHistory_eq s n heta, profiles_beta_exterior s n eta heta R hR, mul_zero]

theorem pressureField_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 0 < n) : SlowStressSupport.exterior s.B S (pressureField s n) := by
  intro eta heta R hR
  rw [pressureField_eq s n heta]
  exact profiles_pressure_exterior s hn eta heta R hR

theorem previousOmega_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    SlowStressSupport.exterior s.B S (previousOmega s n) := by
  intro eta heta R hR
  have hz := exterior_previousOmegaDivX s.domain
    (fun j => (profiles s j).axial) (fun j => (profiles s j).beta) n s.B_pos
    (fun j _ => profiles_beta_exterior s j) eta heta R hR
  simp only [previousOmega, hz, mul_zero]

theorem pressureGradient_eq {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    PositiveOrderMoments.jointPressureGradient n (angularHistory s) (previousOmega s n) w =
      PositiveOrderMoments.jointPressureGradient n
        (fun j => angularField C (profiles s j).phi) (previousOmega s n) w := by
  simp only [PositiveOrderMoments.jointPressureGradient, PositiveOrderMoments.pressureGradient,
    PositiveOrderMoments.cauchy, PositiveAxisSystem.convolution, PositiveOrderMoments.slice,
    angularHistory_eq s _ hw]

theorem pressureGradient_smooth {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    Smooth S (PositiveOrderMoments.jointPressureGradient n (angularHistory s) (previousOmega s n))
      :=
  (actual_pressureGradient_smooth C (fun j => (profiles s j).phi)
    (previousOmegaDivX s.domain (fun j => (profiles s j).axial) (fun j => (profiles s j).beta) n)
      n).congr
      (fun _ hw => pressureGradient_eq s n hw.2)

theorem pressureField_eq_primitive {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 0 < n) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    pressureField s n w = PositiveOrderMoments.pressureHistory n (angularHistory s) (previousOmega
      s n) w := by
  rw [pressureField_eq s n hw]
  have he := congrFun (profiles_pressureHistory s hn) w
  rw [he]
  apply intervalIntegral.integral_congr
  intro R _
  exact (pressureGradient_eq s n (w := (R, w.2)) hw).symm

/-- These are the five rows of the constructed sequence, with its actual
preceding radial residual. -/
theorem moments_zero {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ}
    (hn : 0 < n) {eta : ℝ} (heta : eta ∈ S) :
    PositiveOrderMoments.moments n (PositiveOrderMoments.slice (axialHistory s) eta)
      (PositiveOrderMoments.slice (angularHistory s) eta) (fun R => previousOmega s n (R, eta)) = 0
        := by
  rw [← profiles_moments s hn heta]
  apply moments_congr_positive
  · intro R _ j
    exact axialHistory_eq s j heta
  · intro R _ j
    exact angularHistory_eq s j heta
  · intro R _
    rfl

theorem rowDensity_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ}
    (hn : 0 < n) {eta : ℝ} (heta : eta ∈ S) {R : ℝ} (hR : s.B ≤ R) :
    PositiveOrderMoments.jointRowDensity n (axialHistory s) (angularHistory s)
      (previousOmega s n) (R, eta) = 0 :=
  PositiveOrderMoments.jointRowDensity_exterior hn _ _ _ _
    (fun j _ => axialHistory_exterior s j eta heta R hR)
    (fun _ hj _ => angularHistory_exterior s hj eta heta R hR)
    (previousOmega_exterior s n eta heta R hR)

/-- In particular, pressure integration by parts converts the fifth repaired
row into the actual axial pressure/transport flux moment. -/
theorem conservative_moments_zero {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ}
    (hn : 0 < n) {eta : ℝ} (heta : eta ∈ S) :
    SlowStressSupport.moment s.B 1 (axialHistory s n) eta = 0 ∧
    SlowStressSupport.moment s.B 2 (angularHistory s n) eta = 0 ∧
    SlowStressSupport.moment s.B 2 (SlowStressSupport.conv n (axialHistory s) (angularHistory s))
      eta = 0 ∧
    SlowStressSupport.moment s.B 1
      (fun w => SlowStressSupport.conv n (axialHistory s) (axialHistory s) w + pressureField s n w)
        eta = 0 := by
  have hm := SlowStressSupport.repaired_moment_data s.domain.isOpen
    (fun j _ => axialHistory_smooth s j) (pressureGradient_smooth s n) s.B_pos.le
    (fun _ he _ hr => rowDensity_exterior s hn he hr)
    (fun _ he => moments_zero s hn he) heta
  refine ⟨hm.1, hm.2.1, hm.2.2.1, ?_⟩
  rw [← hm.2.2.2]
  apply intervalIntegral.integral_congr
  intro R _
  dsimp only
  rw [pressureField_eq_primitive s hn (w := (R, eta)) heta]

theorem fluxHistory_axis {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    {eta : ℝ} (heta : eta ∈ S) : fluxHistory s n (0, eta) = 0 := by
  rw [fluxHistory_eq s n (w := (0, eta)) heta]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul]

/-- The angular conservative residual has zero actual radial integral.
Differentiation of the zero moments and radial integration by parts are
performed by the imported balance theorem. -/
theorem angularDensity_moment_zero {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 2 ≤ n) {eta : ℝ} (heta : eta ∈ S) :
    SlowStressSupport.moment s.B 0
      (SlowStressSupport.angularDensity h n (fluxHistory s) (axialHistory s) (angularHistory s))
        eta = 0 := by
  have hn0 : 0 < n := by omega
  have hprev : 0 < n - 1 := by omega
  exact SlowStressSupport.angular_integral_zero s.domain.isOpen
    (fun j _ => fluxHistory_smooth s j) (fun j _ => axialHistory_smooth s j)
    (fun j _ => angularHistory_smooth s j) h s.B s.domain.denominator
    (angularHistory_exterior s hn0) (fun j _ => fluxHistory_exterior s j)
    (fun _ he => (conservative_moments_zero s hn0 he).2.1)
    (fun _ he => (conservative_moments_zero s hn0 he).2.2.1)
    (SlowStressSupport.exterior_conv_left (fun j _ => axialHistory_exterior s j))
    (angularHistory_exterior s hprev)
    (fun _ he => (conservative_moments_zero s hprev he).2.1) heta

theorem axialDensity_moment_zero {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 2 ≤ n) {eta : ℝ} (heta : eta ∈ S) :
    SlowStressSupport.moment s.B 0
      (SlowStressSupport.axialDensity h n (fluxHistory s) (axialHistory s) (pressureField s n)) eta
        = 0 := by
  have hn0 : 0 < n := by omega
  have hprev : 0 < n - 1 := by omega
  apply SlowStressSupport.axial_integral_zero s.domain.isOpen
    (fun j _ => fluxHistory_smooth s j) (fun j _ => axialHistory_smooth s j)
    (pressureField_smooth s n) h s.B s.domain.denominator
    (axialHistory_exterior s n) (fun j _ => fluxHistory_exterior s j)
  · intro z hz
    simp only [SlowStressSupport.conv, fluxHistory_axis s _ hz, zero_mul, Finset.sum_const_zero]
  · exact fun _ he => (conservative_moments_zero s hn0 he).1
  · exact fun _ he => (conservative_moments_zero s hn0 he).2.2.2
  · intro z hz
    rw [SlowStressSupport.exterior_conv_left (fun j _ => axialHistory_exterior s j) z hz s.B le_rfl,
      pressureField_exterior s hn0 z hz s.B le_rfl, zero_add]
  · exact axialHistory_exterior s (n - 1)
  · exact fun _ he => (conservative_moments_zero s hprev he).1
  · exact heta

theorem angularDensity_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 2 ≤ n) :
    SlowStressSupport.exterior s.B S
      (SlowStressSupport.angularDensity h n (fluxHistory s) (axialHistory s) (angularHistory s)) :=
        by
  have hn0 : 0 < n := by omega
  have hprev : 0 < n - 1 := by omega
  exact SlowStressSupport.exterior_angularDensity s.domain.isOpen
    (fun j _ => fluxHistory_smooth s j) (fun j _ => axialHistory_smooth s j)
    (fun j _ => angularHistory_smooth s j) h s.B
    (fun j _ => fluxHistory_exterior s j) (fun j _ => axialHistory_exterior s j)
    (angularHistory_exterior s hn0)
    (SlowStressSupport.exterior_axialOp2 s.domain.isOpen (angularHistory_smooth s (n - 1))
      (angularHistory_exterior s hprev) h _ s.domain.denominator)

theorem axialDensity_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 2 ≤ n) :
    SlowStressSupport.exterior s.B S
      (SlowStressSupport.axialDensity h n (fluxHistory s) (axialHistory s) (pressureField s n)) :=
        by
  have hn0 : 0 < n := by omega
  exact SlowStressSupport.exterior_axialDensity s.domain.isOpen
    (fun j _ => fluxHistory_smooth s j) (fun j _ => axialHistory_smooth s j)
    (pressureField_smooth s n) h s.B
    (fun j _ => fluxHistory_exterior s j) (fun j _ => axialHistory_exterior s j)
    (pressureField_exterior s hn0)
    (SlowStressSupport.exterior_axialOp2 s.domain.isOpen (axialHistory_smooth s (n - 1))
      (axialHistory_exterior s (n - 1)) h _ s.domain.denominator)

/-- At order zero the same divergence reconstruction is the only additional
generic input.  At every positive order it is part of the proved recursion. -/
theorem radial_divergence {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) (n : ℕ)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    SlowStressSupport.dr (fluxHistory s n) w =
      -w.1 * SlowStressSupport.axialOp h (SlowStressSupport.orderExponent h n) (axialHistory s n) w
        := by
  have hb : (profiles s n).beta =
      betaFromU s.domain (AxisSourceRegularity.slowOrder h n) (profiles s n).axial := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa only [profiles_zero, AxisSourceRegularity.slowOrder, Nat.cast_zero, mul_zero, zero_mul]
        using hbase
    · exact profiles_beta_eq s hn
  have hd := reconstructed_flux_derivative s.domain (AxisSourceRegularity.slowOrder h n)
    (profiles s n).axial (R := w.1) hw
  rw [← hb] at hd
  have hg := SlowStressSupport.radial_hasDerivAt s.domain.isOpen (fluxHistory_smooth s n) hw
  have he : (fun R => fluxHistory s n (R, w.2)) =
      fun R => R ^ 2 / 2 * (profiles s n).beta (R, w.2) :=
    funext (fun R => fluxHistory_eq s n (w := (R, w.2)) hw)
  rw [he] at hg
  rw [hg.unique hd]
  have hu : axialHistory s n =ᶠ[𝓝 w] ((profiles s n).axial : Field) := by
    filter_upwards [(isOpen_univ.prod s.domain.isOpen).mem_nhds ⟨mem_univ _, hw⟩] with p hp
    exact axialHistory_eq s n hp.2
  rw [SlowResidualMatching.axialOp_congr_germ h _ hu]
  rfl

theorem thetaDensity_eq {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 0 < n) :
    EqOn (SlowResidualMatching.thetaDensity h C (asSlowProfiles s) n)
      (SlowStressSupport.angularDensity h n (fluxHistory s) (axialHistory s) (angularHistory s))
      (region S) := by
  apply SlowResidualMatching.thetaDensity_eq_angularDensity s.domain.isOpen h C s.nonzero_scale
    (asSlowProfiles s) hn
  · exact fun j _ => fluxHistory_smooth s j
  · exact fun j _ => axialHistory_smooth s j
  · exact fun j _ => angularHistory_smooth s j
  · intro w hw hR j _
    exact (xProfile_contDiffAt s.domain.isOpen (profiles s j).phi (w :=
      SlowResidualMatching.radiusPoint w)
      (div_pos (sq_pos_of_ne_zero hR) (by norm_num)) hw).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  · exact s.domain.denominator
  · exact fun _ hw j _ => radial_divergence s hbase j hw

theorem zDensity_eq {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 0 < n) :
    EqOn (SlowResidualMatching.zDensity h (asSlowProfiles s) n)
      (SlowStressSupport.axialDensity h n (fluxHistory s) (axialHistory s) (pressureField s n))
      (region S) := by
  apply SlowResidualMatching.zDensity_eq_axialDensity s.domain.isOpen h (asSlowProfiles s) hn
  · exact fun j _ => fluxHistory_smooth s j
  · exact fun j _ => axialHistory_smooth s j
  · exact pressureField_smooth s n
  · intro w hw hR j _
    exact (xProfile_contDiffAt s.domain.isOpen (profiles s j).axial (w :=
      SlowResidualMatching.radiusPoint w)
      (div_pos (sq_pos_of_ne_zero hR) (by norm_num)) hw).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  · intro w hw hR
    exact (xProfile_contDiffAt s.domain.isOpen (profiles s n).pressure (w :=
      SlowResidualMatching.radiusPoint w)
      (div_pos (sq_pos_of_ne_zero hR) (by norm_num)) hw).differentiableAt (by simp)
  · exact s.domain.denominator
  · exact fun _ hw j _ => radial_divergence s hbase j hw

theorem thetaDensity_smooth {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 0 < n) :
    Smooth S (SlowResidualMatching.thetaDensity h C (asSlowProfiles s) n) :=
  (SlowStressSupport.smooth_angularDensity s.domain.isOpen
    (fun j _ => fluxHistory_smooth s j) (fun j _ => axialHistory_smooth s j)
    (fun j _ => angularHistory_smooth s j) h s.domain.denominator).congr (thetaDensity_eq s hbase
      hn)

theorem zDensity_smooth {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 0 < n) :
    Smooth S (SlowResidualMatching.zDensity h (asSlowProfiles s) n) :=
  (SlowStressSupport.smooth_axialDensity s.domain.isOpen
    (fun j _ => fluxHistory_smooth s j) (fun j _ => axialHistory_smooth s j)
    (pressureField_smooth s n) h s.domain.denominator).congr (zDensity_eq s hbase hn)

/-- Cancellation of the actual coefficient density, not an assumed moment
of an abstract source. -/
theorem thetaDensity_moment_zero {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 2 ≤ n)
    {eta : ℝ} (heta : eta ∈ S) :
    SlowStressSupport.moment s.B 0 (SlowResidualMatching.thetaDensity h C (asSlowProfiles s) n) eta
      = 0 := by
  rw [← angularDensity_moment_zero s hn heta]
  apply intervalIntegral.integral_congr
  intro R _
  dsimp only
  rw [thetaDensity_eq s hbase (by omega : 0 < n) ⟨mem_univ R, heta⟩]

theorem zDensity_moment_zero {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 2 ≤ n)
    {eta : ℝ} (heta : eta ∈ S) :
    SlowStressSupport.moment s.B 0 (SlowResidualMatching.zDensity h (asSlowProfiles s) n) eta = 0
      := by
  rw [← axialDensity_moment_zero s hn heta]
  apply intervalIntegral.integral_congr
  intro R _
  dsimp only
  rw [zDensity_eq s hbase (by omega : 0 < n) ⟨mem_univ R, heta⟩]

theorem thetaDensity_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 2 ≤ n) :
    SlowStressSupport.exterior s.B S (SlowResidualMatching.thetaDensity h C (asSlowProfiles s) n)
      := by
  intro eta heta R hR
  rw [thetaDensity_eq s hbase (by omega : 0 < n) ⟨mem_univ R, heta⟩]
  exact angularDensity_exterior s hn eta heta R hR

theorem zDensity_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 2 ≤ n) :
    SlowStressSupport.exterior s.B S (SlowResidualMatching.zDensity h (asSlowProfiles s) n) := by
  intro eta heta R hR
  rw [zDensity_eq s hbase (by omega : 0 < n) ⟨mem_univ R, heta⟩]
  exact axialDensity_exterior s hn eta heta R hR

theorem thetaDensity_integrableOn {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 2 ≤ n)
    {eta : ℝ} (heta : eta ∈ S) :
    IntegrableOn (fun R => SlowResidualMatching.thetaDensity h C (asSlowProfiles s) n (R, eta))
      (Ioi 0) :=
  PositiveOrderMoments.positive_integrableOn_of_compact
    (SlowStressSupport.slice_smooth (thetaDensity_smooth s hbase (by omega : 0 < n))
      heta).continuous.continuousOn
    (thetaDensity_exterior s hbase hn eta heta)

theorem zDensity_integrableOn {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 2 ≤ n)
    {eta : ℝ} (heta : eta ∈ S) :
    IntegrableOn (fun R => SlowResidualMatching.zDensity h (asSlowProfiles s) n (R, eta)) (Ioi 0) :=
  PositiveOrderMoments.positive_integrableOn_of_compact
    (SlowStressSupport.slice_smooth (zDensity_smooth s hbase (by omega : 0 < n))
      heta).continuous.continuousOn
    (zDensity_exterior s hbase hn eta heta)

theorem thetaDensity_positive_integral_zero {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 2 ≤ n)
    {eta : ℝ} (heta : eta ∈ S) :
    (∫ R in Ioi (0 : ℝ), SlowResidualMatching.thetaDensity h C (asSlowProfiles s) n (R, eta)) = 0
      := by
  have he := SlowStressSupport.moment_eq_positive s.B_pos.le (thetaDensity_exterior s hbase hn)
    heta 0
  simp only [pow_zero, one_mul, thetaDensity_moment_zero s hbase hn heta] at he
  exact he.symm

theorem zDensity_positive_integral_zero {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 2 ≤ n)
    {eta : ℝ} (heta : eta ∈ S) :
    (∫ R in Ioi (0 : ℝ), SlowResidualMatching.zDensity h (asSlowProfiles s) n (R, eta)) = 0 := by
  have he := SlowStressSupport.moment_eq_positive s.B_pos.le (zDensity_exterior s hbase hn) heta 0
  simp only [pow_zero, one_mul, zDensity_moment_zero s hbase hn heta] at he
  exact he.symm

/-- Both canonical negative radial primitives have the same exterior
radius for all `n ≥ 2`.  There is no output-support hypothesis. -/
theorem raw_stresses_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {n : ℕ} (hn : 2 ≤ n) :
    Exterior s.B S (SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity h C
      (asSlowProfiles s) n)) ∧
    Exterior s.B S (SlowStressSupport.stress 1 (SlowResidualMatching.zDensity h (asSlowProfiles s)
      n)) := by
  constructor
  · intro eta heta R hR
    exact SlowStressSupport.stress_exterior 2 s.B_pos.le (thetaDensity_exterior s hbase hn)
      (fun _ he => thetaDensity_moment_zero s hbase hn he) hR heta
  · intro eta heta R hR
    exact SlowStressSupport.stress_exterior 1 s.B_pos.le (zDensity_exterior s hbase hn)
      (fun _ he => zDensity_moment_zero s hbase hn he) hR heta

section Nominal

open AssembledSlowBase

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

/-- The nominal scheme uses the actual mass reconstruction already at
order zero, so the generic extra input is discharged definitionally. -/
theorem nominal_base_beta : (nominalScheme W).base.beta =
    betaFromU (nominalScheme W).domain 0 (nominalScheme W).base.axial := rfl

theorem nominal_stresses_exterior {n : ℕ} (hn : 2 ≤ n) :
    Exterior (nominalOuterRadius W) (nominalParameters W)
      (SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity F.data.h W.axis.normalization
        (asSlowProfiles (nominalScheme W)) n)) ∧
    Exterior (nominalOuterRadius W) (nominalParameters W)
      (SlowStressSupport.stress 1 (SlowResidualMatching.zDensity F.data.h
        (asSlowProfiles (nominalScheme W)) n)) :=
  raw_stresses_exterior (nominalScheme W) (nominal_base_beta W) hn

theorem nominal_density_integrals_zero {n : ℕ} (hn : 2 ≤ n)
    {eta : ℝ} (heta : eta ∈ nominalParameters W) :
    (∫ R in Ioi (0 : ℝ), SlowResidualMatching.thetaDensity F.data.h W.axis.normalization
      (asSlowProfiles (nominalScheme W)) n (R, eta)) = 0 ∧
    (∫ R in Ioi (0 : ℝ), SlowResidualMatching.zDensity F.data.h
      (asSlowProfiles (nominalScheme W)) n (R, eta)) = 0 :=
  ⟨thetaDensity_positive_integral_zero (nominalScheme W) (nominal_base_beta W) hn heta,
   zDensity_positive_integral_zero (nominalScheme W) (nominal_base_beta W) hn heta⟩

/-- The actual globally smooth coefficients vanish outside the fixed outer
radius for every parameter, including outside the physical parameter strip. -/
theorem nominalCoefficients_stress_zero_right {n : ℕ} (hn : 2 ≤ n)
    {p : ℝ × ℝ} (hX : nominalOuterX W ≤ p.1) :
    (nominalCoefficients W).stressTheta n p = 0 ∧ (nominalCoefficients W).stressAxial n p = 0 := by
  have hs := nominal_stresses_exterior W hn
  apply coefficients_stress_zero_right (nominalLocalization W) (nominalBaseAgreement W)
    (nominalZeroOrder W) (nominalParameters_contains W) n (nominalOuterRadius_pos W).le hs.1 hs.2
  simpa only [nominalOuterRadius_square] using hX

/-- One compact rectangle contains both stress supports for the entire
higher-order family.  Its radial lower edge is strictly positive. -/
theorem nominalCoefficients_stress_support {n : ℕ} (hn : 2 ≤ n) :
    tsupport (fun p => ((nominalCoefficients W).stressTheta n p,
        (nominalCoefficients W).stressAxial n p)) ⊆
      Icc (nominalInner W / 8) (nominalOuterX W) ×ˢ
        Icc (-(commonWindow (nominalScheme W) (nominalParameters_contains W)).outer)
          (commonWindow (nominalScheme W) (nominalParameters_contains W)).outer := by
  have hs := nominal_stresses_exterior W hn
  have h := coefficients_stress_support (nominalLocalization W) (nominalBaseAgreement W)
    (nominalZeroOrder W) (nominalParameters_contains W) n (nominalOuterRadius_pos W).le hs.1 hs.2
  simp only [nominalOuterRadius_square] at h
  exact h

theorem nominalCoefficients_stress_compactSupport {n : ℕ} (hn : 2 ≤ n) :
    HasCompactSupport (fun p => ((nominalCoefficients W).stressTheta n p,
      (nominalCoefficients W).stressAxial n p)) :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_closure
    (nominalCoefficients_stress_support W hn)

end Nominal

end NavierStokes.GlobalStressSupport
