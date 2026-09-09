/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryCovarianceBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryRepresentatives

/-!
# Base estimates imply the actual pulse geometry

The inputs concern normalized base fields and frozen representative data.
Normal, damping, and moving-basis errors are conclusions. The dyadic cutoff
is chosen after all fixed constants and before the band or slow point.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.BasePhaseGeometry

open Set Filter
open scoped Topology ContDiff InnerProductSpace

/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow
/-- Plane: an abbreviation for `MovingFrameODE.Plane`. -/
abbrev Plane := MovingFrameODE.Plane
/-- Space: an abbreviation for `MovingFrameODE.Space`. -/
abbrev Space := MovingFrameODE.Space

/-- The normalized base error `Q^(2h)` is exactly the squared native small
parameter used by the phase estimates. -/
theorem epsilon_squared (h : ℝ) (n : ℕ) :
    ChartScales.epsilon h n ^ 2 = ChartScales.Q n ^ (2 * h) := by
  symm
  simpa only [ChartScales.epsilon, Nat.cast_ofNat, mul_comm] using
    Real.rpow_mul_natCast (ChartScales.Q_pos n).le h 2

/-- Damping denominator, given by `(1 + u ^ 2) * Real.sqrt (1 + u ^ 2)`. -/
noncomputable def dampingDenominator (u : ℝ) : ℝ :=
  (1 + u ^ 2) * Real.sqrt (1 + u ^ 2)

/-- Reference scale, given by `Real.sqrt (lam / (viscosity * dampingDenominator u))`. -/
noncomputable def referenceScale (lam viscosity u : ℝ) : ℝ :=
  Real.sqrt (lam / (viscosity * dampingDenominator u))

theorem dampingDenominator_pos (u : ℝ) : 0 < dampingDenominator u :=
  PulseGrowth.dampingDenominator_pos u

theorem dampingDenominator_one_le (u : ℝ) : 1 ≤ dampingDenominator u := by
  have hs : 1 ≤ Real.sqrt (1 + u ^ 2) := (PhaseJetBounds.radius_bounds u).1
  unfold dampingDenominator
  nlinarith [sq_nonneg u, Real.sqrt_nonneg (1 + u ^ 2)]

theorem referenceScale_pos {lam viscosity u : ℝ} (hlam : 0 < lam) (hv : 0 < viscosity) :
    0 < referenceScale lam viscosity u :=
  Real.sqrt_pos.mpr (div_pos hlam (mul_pos hv (dampingDenominator_pos u)))

theorem referenceScale_normalization {lam viscosity u : ℝ}
    (hlam : 0 < lam) (hv : 0 < viscosity) :
    viscosity * referenceScale lam viscosity u ^ 2 = lam / dampingDenominator u := by
  have hD := dampingDenominator_pos u
  rw [referenceScale, Real.sq_sqrt (div_nonneg hlam.le (mul_nonneg hv.le hD.le))]
  field_simp [hv.ne', hD.ne']

/-- Uniform scale bounds are derived from the actual rounded viscosity
factor, rather than imposed on the chosen phase normal. -/
theorem referenceScale_bounds {lam l M viscosity u : ℝ}
    (hl : 0 < l) (hlam : l ≤ lam) (hM : lam ≤ M)
    (hvlo : 1 ≤ viscosity) (hvhi : viscosity ≤ 4) :
    Real.sqrt (l / (4 * dampingDenominator u)) ≤ referenceScale lam viscosity u ∧
      referenceScale lam viscosity u ≤ Real.sqrt M := by
  have hv : 0 < viscosity := zero_lt_one.trans_le hvlo
  have hD := dampingDenominator_pos u
  have hlampos := hl.trans_le hlam
  constructor
  · apply Real.sqrt_le_sqrt
    exact (div_le_div_of_nonneg_right hlam (by positivity : 0 ≤ 4 * dampingDenominator u)).trans
      (div_le_div_of_nonneg_left hlampos.le (mul_pos hv hD)
        (mul_le_mul_of_nonneg_right hvhi hD.le))
  · apply Real.sqrt_le_sqrt
    apply (div_le_iff₀ (mul_pos hv hD)).mpr
    have hVD : 1 ≤ viscosity * dampingDenominator u :=
      one_le_mul_of_one_le_of_one_le hvlo (dampingDenominator_one_le u)
    exact hM.trans (le_mul_of_one_le_right (hlampos.le.trans hM) hVD)

theorem dyadic_referenceScale_normalization (h u : ℝ) {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    (ChartScales.epsilon h n * (ChartScales.carrier h n : ℝ) ^ 2) *
      referenceScale lam (ChartScales.epsilon h n * (ChartScales.carrier h n : ℝ) ^ 2) u ^ 2 =
        lam / dampingDenominator u := by
  apply referenceScale_normalization hlam
  have hk : 0 < (ChartScales.carrier h n : ℝ) :=
    Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h n)
  exact mul_pos (ChartScales.epsilon_pos h n) (pow_pos hk 2)

theorem localBase_mono {F G F0 G0 : Slow → ℝ} {U : Set Slow} {M T ε : ℝ}
    (h : PhaseEstimates.LocalBaseBounds F G F0 G0 U M ε) (hMT : M ≤ T) :
    PhaseEstimates.LocalBaseBounds F G F0 G0 U T ε where
  convex := h.convex
  actualF := h.actualF
  actualG := h.actualG
  referenceF := h.referenceF
  referenceG := h.referenceG
  secondF := h.secondF
  secondG := h.secondG
  secondF_bound x hx := (h.secondF_bound x hx).trans hMT
  secondG_bound x hx := (h.secondG_bound x hx).trans hMT
  firstF_bound x hx := (h.firstF_bound x hx).trans hMT
  valueF_error x hx := (h.valueF_error x hx).trans (mul_le_mul_of_nonneg_right hMT (sq_nonneg ε))
  firstF_error x hx := (h.firstF_error x hx).trans (mul_le_mul_of_nonneg_right hMT (sq_nonneg ε))
  firstG_error x hx := (h.firstG_error x hx).trans (mul_le_mul_of_nonneg_right hMT (sq_nonneg ε))
  radialF_bound x hx := (h.radialF_bound x hx).trans hMT
  axialF_bound x hx := (h.axialF_bound x hx).trans hMT
  axialG_bound x hx := (h.axialG_bound x hx).trans hMT

/-- The norm of an actual base derivative is bounded by the reference
derivative and the normalized C1 error. -/
theorem derivative_norm_of_error {F F0 : Slow → ℝ} {q : Slow} {M ε : ℝ}
    (hM : 0 ≤ M) (hε : ε ^ 2 ≤ 1)
    (href : ‖fderiv ℝ F0 q‖ ≤ M)
    (herr : ‖fderiv ℝ F q - fderiv ℝ F0 q‖ ≤ M * ε ^ 2) :
    ‖fderiv ℝ F q‖ ≤ 2 * M := by
  have hnorm := norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ F q) (fderiv ℝ F0 q) 0
  simp only [sub_zero] at hnorm
  have he := mul_le_mul_of_nonneg_left hε hM
  nlinarith

/-- Primitive normalized-base C1 errors and fixed reference C2 bounds give
all local hypotheses used by the phase estimate. -/
theorem localBase_of_normalized_error
    {F G F0 G0 : Slow → ℝ} {U : Set Slow} {M ε : ℝ}
    (hM : 0 ≤ M) (hε : ε ^ 2 ≤ 1) (hU : Convex ℝ U)
    (hF : ∀ x ∈ U, DifferentiableAt ℝ F x) (hG : ∀ x ∈ U, DifferentiableAt ℝ G x)
    (hF0 : ∀ x ∈ U, DifferentiableAt ℝ F0 x) (hG0 : ∀ x ∈ U, DifferentiableAt ℝ G0 x)
    (hF02 : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ F0) x)
    (hG02 : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ G0) x)
    (hDF0 : ∀ x ∈ U, ‖fderiv ℝ F0 x‖ ≤ M)
    (hDG0 : ∀ x ∈ U, ‖fderiv ℝ G0 x‖ ≤ M)
    (hDDF0 : ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ F0) x‖ ≤ M)
    (hDDG0 : ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ G0) x‖ ≤ M)
    (hvalue : ∀ x ∈ U, |F x - F0 x| ≤ M * ε ^ 2)
    (hDF : ∀ x ∈ U, ‖fderiv ℝ F x - fderiv ℝ F0 x‖ ≤ M * ε ^ 2)
    (hDG : ∀ x ∈ U, ‖fderiv ℝ G x - fderiv ℝ G0 x‖ ≤ M * ε ^ 2) :
    PhaseEstimates.LocalBaseBounds F G F0 G0 U (2 * M) ε := by
  have hgradF x hx := derivative_norm_of_error hM hε (hDF0 x hx) (hDF x hx)
  have hgradG x hx := derivative_norm_of_error hM hε (hDG0 x hx) (hDG x hx)
  have hM2 : M ≤ 2 * M := by linarith
  have hdir (f : Slow → ℝ) (x : Slow) (e : Slow) (he : ‖e‖ ≤ 1)
      (hf : ‖fderiv ℝ f x‖ ≤ 2 * M) : |fderiv ℝ f x e| ≤ 2 * M := by
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul hf he (norm_nonneg _) (by positivity)).trans_eq (mul_one _))
  refine ⟨hU, hF, hG, hF0, hG0, hF02, hG02,
    fun x hx => (hDDF0 x hx).trans hM2, fun x hx => (hDDG0 x hx).trans hM2,
    fun x hx => (hDF0 x hx).trans hM2,
    fun x hx => (hvalue x hx).trans (mul_le_mul_of_nonneg_right hM2 (sq_nonneg ε)),
    fun x hx => (hDF x hx).trans (mul_le_mul_of_nonneg_right hM2 (sq_nonneg ε)),
    fun x hx => (hDG x hx).trans (mul_le_mul_of_nonneg_right hM2 (sq_nonneg ε)), ?_, ?_, ?_⟩
  · intro x hx
    exact hdir F x (1, (0, 0)) (by norm_num) (hgradF x hx)
  · intro x hx
    exact hdir F x (0, (1, 0)) (by norm_num) (hgradF x hx)
  · intro x hx
    exact hdir G x (0, (1, 0)) (by norm_num) (hgradG x hx)

theorem scaled_div_mono {a A δ b B : ℝ} (hδ : 0 ≤ δ) (hb : 0 < b)
    (hbB : b ≤ B) (ha : 0 ≤ a) (haA : a ≤ A) : a * δ / B ≤ A * δ / b := by
  have hB : 0 < B := hb.trans_le hbB
  have hd := div_le_div_of_nonneg_left hδ hb hbB
  simpa only [mul_div_assoc] using mul_le_mul haA hd (div_nonneg hδ hB.le) (ha.trans haA)

/-- Normal comparison and base comparison imply the three geometric
coefficient errors. All changing-frame terms are included. -/
theorem frame_errors_of_normal_close
    {n nDot : Space} {K g g0 : Plane} {F F0 B s b M A δ η : ℝ}
    (hb : 0 < b) (hbB : b ≤ B) (hK : ‖K‖ = 1)
    (hsmall : δ ≤ B / 2)
    (hn : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ)
    (hnd : ‖nDot‖ ≤ δ)
    (hM : 1 ≤ M) (hA : 0 ≤ A) (hs : |s| ≤ A)
    (hF0 : |F0| ≤ M) (hg0 : ‖g0‖ ≤ M) (horth : ⟪K, g0⟫_ℝ = 0)
    (hη : 0 ≤ η) (hF : |F - F0| ≤ η) (hg : ‖g - g0‖ ≤ η) :
    let G := M + 2 + 2 * A
    let E := η + 8 * (1 + A) * δ / b
    let R := PrimaryODE.localFrame n
    let r := MovingFrameODE.radialSlope n
    let rd := PhaseEstimates.slopeDerivative n nDot
    let rot := PhaseEstimates.angularVelocity n nDot
    |MovingFrameODE.coeff11 r rd ⟪R 0, g⟫_ℝ| ≤ 16 * G ^ 2 * (1 + G) * E ∧
    |MovingFrameODE.coeff12 F (R 1 0) r rot - 2 * F0 * (MovingFrameODE.quarterTurn K) 0 / (1 + s ^
        2)| ≤
      16 * G ^ 2 * (1 + G) * E ∧
    |MovingFrameODE.coeff21 F (R 1 0) ⟪R 1, g⟫_ℝ r rot -
        (-(2 * F0 * (MovingFrameODE.quarterTurn K) 0 + ⟪MovingFrameODE.quarterTurn K, g0⟫_ℝ))| ≤
      16 * G ^ 2 * (1 + G) * E := by
  dsimp only
  have hB : 0 < B := hb.trans_le hbB
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hn
  obtain ⟨hlow, _, hne, _⟩ := PhaseEstimates.normal_lower_bounds hB hK hsmall hn
  have hr := PhaseEstimates.radialSlope_uniform_bound hB hK hsmall hn hs
  let E := η + 8 * (1 + A) * δ / b
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hηE : η ≤ E := by
    have : 0 ≤ 8 * (1 + A) * δ / b := by positivity
    dsimp [E]
    linarith
  have hfac : 8 * (1 + A) * δ / b ≤ E := by dsimp [E]; linarith
  have h0 : PrimaryODE.localFrame n 0 = MovingFrameODE.normalDirection n := by
    rw [PrimaryODE.localFrame_eq hne, MovingFrameODE.normalFrame_zero]
  have h1 : PrimaryODE.localFrame n 1 = MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection
      n) := by
    rw [PrimaryODE.localFrame_eq hne, MovingFrameODE.normalFrame_one]
  have hKerr : ‖PrimaryODE.localFrame n 0 - K‖ ≤ E := by
    rw [h0]
    exact (PhaseEstimates.normalDirection_close hB hK hsmall hn).trans
      ((scaled_div_mono hδ hb hbB (by norm_num : (0 : ℝ) ≤ 4) (by nlinarith)).trans hfac)
  have hNerr : ‖PrimaryODE.localFrame n 1 - MovingFrameODE.quarterTurn K‖ ≤ E := by
    rw [h1]
    exact (PhaseEstimates.transverseDirection_close hB hK hsmall hn).trans
      ((scaled_div_mono hδ hb hbB (by norm_num : (0 : ℝ) ≤ 4) (by nlinarith)).trans hfac)
  have hrerr : |MovingFrameODE.radialSlope n - s| ≤ E :=
    (PhaseEstimates.radialSlope_close hB hK hsmall hn).trans
      ((scaled_div_mono hδ hb hbB (by positivity) (by nlinarith [abs_nonneg s])).trans hfac)
  have hrderr : |PhaseEstimates.slopeDerivative n nDot| ≤ E :=
    (PhaseEstimates.slopeDerivative_bound hB hlow hnd).trans
      ((scaled_div_mono hδ hb hbB (by positivity)
        (by nlinarith [abs_nonneg (MovingFrameODE.radialSlope n)])).trans hfac)
  have hωerr : |PhaseEstimates.angularVelocity n nDot| ≤ E :=
    (PhaseEstimates.angularVelocity_bound hB hlow hnd).trans
      ((scaled_div_mono hδ hb hbB (by norm_num : (0 : ℝ) ≤ 4) (by nlinarith)).trans hfac)
  have h := MovingFrameODE.frame_coefficients_close
    (B := PrimaryODE.localFrame n) (B0 := MovingFrameODE.frameOfUnit K hK)
    (g := g) (g0 := g0) (F := F) (F0 := F0) (ρ := MovingFrameODE.radialSlope n)
    (s := s) (ρ' := PhaseEstimates.slopeDerivative n nDot)
    (rot := PhaseEstimates.angularVelocity n nDot) (M := M + 2 + 2 * A) (η := E)
    (by linarith) hE (hr.trans (by linarith)) (hs.trans (by linarith))
    (hF0.trans (by linarith)) (hg0.trans (by linarith)) (by simpa using horth)
    (hF.trans hηE) (hg.trans hηE) (by simpa using hKerr) (by simpa using hNerr) hrerr hrderr hωerr
  simpa only [MovingFrameODE.frameOfUnit_one, E] using h

theorem norm_pack_sq (x : ℝ) (w : Plane) :
    ‖MovingFrameODE.pack x w‖ ^ 2 = x ^ 2 + ‖w‖ ^ 2 := by
  rw [PhaseCalculus.vec3_norm_sq, ViscousPropagator.plane_norm_sq]
  change x ^ 2 + w 0 ^ 2 + w 1 ^ 2 = x ^ 2 + (w 0 ^ 2 + w 1 ^ 2)
  ring

theorem reference_normal_sq {K : Plane} (hK : ‖K‖ = 1) (B s : ℝ) :
    ‖MovingFrameODE.pack (B * s) (B • K)‖ ^ 2 = B ^ 2 * (1 + s ^ 2) := by
  rw [norm_pack_sq, norm_smul, hK, mul_one, Real.norm_eq_abs, sq_abs]
  ring

theorem reference_normal_bound {K : Plane} {B s A : ℝ}
    (hK : ‖K‖ = 1) (hB : 0 ≤ B) (hs : |s| ≤ A) :
    ‖MovingFrameODE.pack (B * s) (B • K)‖ ≤ B * (A + 2) := by
  have hc (i : Fin 2) : |K i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hK] using PiLp.norm_apply_le K i
  have hn := PhaseEstimates.vec3_norm_le_sum (MovingFrameODE.pack (B * s) (B • K))
  change ‖MovingFrameODE.pack (B * s) (B • K)‖ ≤ |B * s| + |B * K 0| + |B * K 1| at hn
  simp only [abs_mul, abs_of_nonneg hB] at hn
  nlinarith [mul_le_mul_of_nonneg_left hs hB,
    mul_le_mul_of_nonneg_left (hc 0) hB, mul_le_mul_of_nonneg_left (hc 1) hB]

/-- The damping error is two-sided. It follows from normal comparison and
the actual bounded viscosity coefficient, including all high harmonics. -/
theorem damping_error_of_normal_close
    {n : Space} {K : Plane} {B s A M δ ν : ℝ}
    (hK : ‖K‖ = 1) (hB : 0 < B) (hBM : B ≤ M) (hs : |s| ≤ A)
    (hsmall : δ ≤ B / 2)
    (hn : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ)
    (hν0 : 0 ≤ ν) (hν4 : ν ≤ 4) :
    |ν * ‖n‖ ^ 2 - ν * B ^ 2 * (1 + s ^ 2)| ≤ 4 * M * (2 * A + 5) * δ := by
  let r := MovingFrameODE.pack (B * s) (B • K)
  have hA : 0 ≤ A := (abs_nonneg s).trans hs
  have hM : 0 ≤ M := hB.le.trans hBM
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hn
  have hr : ‖r‖ ≤ M * (A + 2) :=
    (reference_normal_bound hK hB.le hs).trans (mul_le_mul_of_nonneg_right hBM (by positivity))
  have hn' : ‖n‖ ≤ M * (A + 3) := by
    have hh := norm_sub_le_norm_sub_add_norm_sub n r 0
    simp only [sub_zero] at hh
    nlinarith
  have hdiff : |‖n‖ - ‖r‖| ≤ δ := (abs_norm_sub_norm_le n r).trans hn
  have hsq : |‖n‖ ^ 2 - ‖r‖ ^ 2| ≤ δ * (M * (2 * A + 5)) := by
    calc
      _ = |‖n‖ - ‖r‖| * (‖n‖ + ‖r‖) := by
        rw [← abs_of_nonneg (add_nonneg (norm_nonneg n) (norm_nonneg r)), ← abs_mul]
        congr 1
        ring
      _ ≤ δ * (M * (2 * A + 5)) := mul_le_mul hdiff (by nlinarith)
        (add_nonneg (norm_nonneg n) (norm_nonneg r)) hδ
  calc
    _ = ν * |‖n‖ ^ 2 - ‖r‖ ^ 2| := by
      rw [show ν * ‖n‖ ^ 2 - ν * B ^ 2 * (1 + s ^ 2) = ν * (‖n‖ ^ 2 - ‖r‖ ^ 2) by
        dsimp [r]; rw [reference_normal_sq hK]; ring, abs_mul, abs_of_nonneg hν0]
    _ ≤ 4 * (δ * (M * (2 * A + 5))) := mul_le_mul hν4 hsq (abs_nonneg _) (by norm_num)
    _ = _ := by ring

/-- Normal constant, given by `8 * PhaseEstimates.phaseConstant (2 * M)`. -/
noncomputable def normalConstant (M : ℝ) : ℝ :=
  8 * PhaseEstimates.phaseConstant (2 * M)

theorem normalConstant_pos {M : ℝ} (hM : 1 ≤ M) : 0 < normalConstant M := by
  have : 0 < M := zero_lt_one.trans_le hM
  unfold normalConstant PhaseEstimates.phaseConstant
  positivity

/-- The actual two-mesh enlargement has diameter three mesh units.  Using
the phase estimate at half the scale retains a fixed, band-independent
constant and does not strengthen this geometric input. -/
theorem phase_errors_on_mesh
    {F G F0 G0 : Slow → ℝ} {U : Set Slow} {q q0 : Slow}
    {ε target pz v θ B sigma u L M S k : ℝ} {K : Plane}
    (hbase : PhaseEstimates.LocalBaseBounds F G F0 G0 U M ε)
    (hq : q ∈ U) (hq0 : q0 ∈ U) (hdiameter : ‖q - q0‖ ≤ 3 / S ^ 3)
    (hR : q.1 ≠ 0) (hR0 : q0.1 ≠ 0)
    (hg : PhaseEstimates.shearVector F0 G0 q0 ≠ 0)
    (horth : ⟪K, PhaseEstimates.shearVector F0 G0 q0⟫_ℝ = 0)
    (hfreq : (!₂[target / q0.1, pz] : Plane) =
      PhaseEstimates.representativeFrequency B sigma u L K (PhaseEstimates.shearVector F0 G0 q0))
    (hM : 1 ≤ M) (hS : 2 ≤ S) (hk : 1 ≤ k) (hε : 0 < ε)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M) (hB : |B| ≤ M)
    (hsigma : |sigma| = 1) (hu : |u| ≤ M)
    (hgi : 1 / ‖PhaseEstimates.shearVector F0 G0 q0‖ ≤ M)
    (hL : 1 / |L| ≤ M / S) (hv : |v| ≤ M * S)
    (hRi : |1 / q.1| ≤ M) (hR0i : |1 / q0.1| ≤ M)
    (hε2 : S ^ 2 * ε ^ 2 ≤ 1) (hk2 : S ^ 2 / k ≤ 1)
    (hε1 : ε * S ^ 2 ≤ 1) :
    ‖PhaseCalculus.phaseNormal ε (PhaseEstimates.roundedFrequency k target) pz
        (sigma * B * u / 2) F G (q, (θ, v)) -
      PhaseEstimates.referenceNormal B sigma u L v K‖ ≤ normalConstant M / S ∧
    ‖PhaseCalculus.normalSlotDerivative ε (PhaseEstimates.roundedFrequency k target) pz F G q‖ ≤
      normalConstant M / S := by
  have hS0 : 0 < S := by linarith
  have hk0 : 0 < k := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hM2 : M ≤ 2 * M := by linarith
  have hd : ‖q - q0‖ ≤ 1 / (S / 2) ^ 3 := hdiameter.trans (by
    apply (div_le_div_iff₀ (pow_pos hS0 3) (pow_pos (half_pos hS0) 3)).2
    nlinarith [pow_pos hS0 3])
  have hL' : 1 / |L| ≤ (2 * M) / (S / 2) := hL.trans (by
    apply (div_le_div_iff₀ hS0 (half_pos hS0)).2
    nlinarith)
  have he := PhaseEstimates.actual_phase_estimates
    (v := v) (θ := θ) (localBase_mono hbase hM2) hq hq0 hd hR hR0 hg horth hfreq
    (by linarith) (by linarith) hk hε (htarget.trans hM2) (hpz.trans hM2) (hB.trans hM2)
    hsigma (hu.trans hM2) (hgi.trans hM2) hL' (by nlinarith [hv])
    (hRi.trans hM2) (hR0i.trans hM2)
  have hband := PhaseEstimates.phaseError_le_four_div (S := S / 2) (ε := ε) (k := k)
    (half_pos hS0) (by nlinarith [sq_nonneg (S * ε)])
    ((div_le_iff₀ hk0).2 (by
      have h := (div_le_iff₀ hk0).1 hk2
      nlinarith [sq_nonneg S]))
    (by nlinarith [mul_nonneg hε.le (sq_nonneg S)])
  have hc : 0 ≤ PhaseEstimates.phaseConstant (2 * M) := by
    unfold PhaseEstimates.phaseConstant
    positivity
  have hbound : PhaseEstimates.phaseConstant (2 * M) *
      PhaseEstimates.phaseError (S / 2) ε k ≤ normalConstant M / S := by
    calc
      _ ≤ PhaseEstimates.phaseConstant (2 * M) * (4 / (S / 2)) :=
        mul_le_mul_of_nonneg_left hband hc
      _ = _ := by unfold normalConstant; field_simp ; ring
  exact ⟨he.1.trans hbound, he.2.trans hbound⟩

theorem signedSlot_sq {sigma : ℝ} (hsigma : |sigma| = 1) (u L v : ℝ) :
    PhaseEstimates.signedSlot sigma u L v ^ 2 = PulseGrowth.slotMagnitude u L v ^ 2 := by
  have hh : sigma ^ 2 = 1 := by nlinarith [sq_abs sigma]
  simp only [PhaseEstimates.signedSlot, PulseGrowth.slotMagnitude, mul_pow, hh, one_mul]

/-- Exact reference diagonalization; its scalar identities are supplied by
the representative eigenpair construction. -/
theorem reference_off_diagonal {lam c0 u L v s a b : ℝ}
    (hc : c0 ≠ 0) (hs : s ^ 2 = PulseGrowth.slotMagnitude u L v ^ 2)
    (ha : lam / c0 = a) (hb : lam * c0 = b) :
    ViscousPropagator.referenceEigenvalue lam u L v / PrimaryODE.referenceProfile c0 u L v =
        a / (1 + s ^ 2) ∧
    ViscousPropagator.referenceEigenvalue lam u L v * PrimaryODE.referenceProfile c0 u L v = b := by
  let r := Real.sqrt (1 + PulseGrowth.slotMagnitude u L v ^ 2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr2 : r ^ 2 = 1 + s ^ 2 := by
    dsimp [r]
    rw [Real.sq_sqrt (by positivity), hs]
  change (lam / r) / (c0 * r) = a / (1 + s ^ 2) ∧ (lam / r) * (c0 * r) = b
  constructor
  · rw [← ha, ← hr2]
    field_simp [hc, hr.ne']
  · calc
      _ = lam * c0 := by field_simp [hr.ne']
      _ = b := hb

theorem reference_profile_bounds {c0 u L v c M A : ℝ}
    (hc : 0 < c) (hcl : c ≤ |c0|) (hch : |c0| ≤ M)
    (hs : |PulseGrowth.slotMagnitude u L v| ≤ A) :
    |PrimaryODE.referenceProfile c0 u L v| ≤ M * (1 + A) ∧
    |1 / PrimaryODE.referenceProfile c0 u L v| ≤ 1 / c := by
  have hb := PhaseJetBounds.radius_bounds (PulseGrowth.slotMagnitude u L v)
  have hM : 0 ≤ M := (abs_nonneg _).trans hch
  have hr : 0 < Real.sqrt (1 + PulseGrowth.slotMagnitude u L v ^ 2) := by positivity
  have hlow : c ≤ |c0| * Real.sqrt (1 + PulseGrowth.slotMagnitude u L v ^ 2) :=
    hcl.trans (le_mul_of_one_le_right (abs_nonneg _) hb.1)
  constructor
  · simpa only [PrimaryODE.referenceProfile, abs_mul, abs_of_pos hr] using
      mul_le_mul hch (hb.2.trans (by linarith)) (Real.sqrt_nonneg _) hM
  · rw [abs_div, abs_one, PrimaryODE.referenceProfile, abs_mul, abs_of_pos hr]
    exact one_div_le_one_div_of_le hc hlow

theorem reference_profile_rate_bound {u L v A M S : ℝ}
    (hA : 0 ≤ A) (_hM : 0 ≤ M) (_hS : 0 < S)
    (hs : |PulseGrowth.slotMagnitude u L v| ≤ A)
    (huL : |u / L| ≤ M / S) :
    |PrimaryODE.referenceProfileRate u L v| ≤ A * M / S := by
  have hden : 1 ≤ 1 + PulseGrowth.slotMagnitude u L v ^ 2 := by
      nlinarith [sq_nonneg (PulseGrowth.slotMagnitude u L v)]
  have hdenpos : 0 < 1 + PulseGrowth.slotMagnitude u L v ^ 2 := by positivity
  rw [PrimaryODE.referenceProfileRate, abs_div, abs_mul, abs_of_pos hdenpos]
  calc
    _ ≤ |PulseGrowth.slotMagnitude u L v| * |u / L| :=
      div_le_self (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hden
    _ ≤ A * (M / S) := mul_le_mul hs huL (abs_nonneg _) hA
    _ = _ := by ring

/-- Frequency bound, given by `M + M * (M + M ^ 4) + (M + M ^ 4) + M ^ 2 + 4`. -/
noncomputable def frequencyBound (M : ℝ) : ℝ := M + M * (M + M ^ 4) + (M + M ^ 4) + M ^ 2 + 4

theorem frequencyBound_bounds {M : ℝ} (hM : 1 ≤ M) :
    M ≤ frequencyBound M ∧ M * (M + M ^ 4) + 1 ≤ frequencyBound M ∧
    M + M ^ 4 ≤ frequencyBound M ∧ M ^ 2 ≤ frequencyBound M ∧ 4 ≤ frequencyBound M := by
  have h0 : 0 ≤ M := by linarith
  have h4 : 0 ≤ M ^ 4 := pow_nonneg h0 _
  have hprod : 0 ≤ M * (M + M ^ 4) := mul_nonneg h0 (add_nonneg h0 h4)
  unfold frequencyBound
  constructor
  · nlinarith [sq_nonneg M]
  constructor
  · nlinarith [sq_nonneg M]
  constructor
  · nlinarith [sq_nonneg M]
  constructor <;> nlinarith [sq_nonneg M]

/-- Normal lower, given by `Real.sqrt ((1 / M) / (4 * dampingDenominator u))`. -/
noncomputable def normalLower (M u : ℝ) : ℝ :=
  Real.sqrt ((1 / M) / (4 * dampingDenominator u))

theorem normalLower_pos {M u : ℝ} (hM : 1 ≤ M) : 0 < normalLower M u := by
  apply Real.sqrt_pos.mpr
  exact div_pos (one_div_pos.mpr (zero_lt_one.trans_le hM))
    (mul_pos (by norm_num) (dampingDenominator_pos u))

/-- Phase constant, given by `normalConstant (frequencyBound M)`. -/
noncomputable def phaseConstant (M : ℝ) : ℝ := normalConstant (frequencyBound M)

theorem phaseConstant_pos {M : ℝ} (hM : 1 ≤ M) : 0 < phaseConstant M :=
  normalConstant_pos (hM.trans (frequencyBound_bounds hM).1)

/-- Coordinate constant, given by `16 * (M + 2 + 2 * (3 * M)) ^ 2 * (1 + (M + 2 + 2 * (3 * M)))
* (16 * M ^ 2 + 8 * (1 + 3 * M) * phaseConstant M / normalLower M u)`. -/
noncomputable def coordinateConstant (M u : ℝ) : ℝ :=
  16 * (M + 2 + 2 * (3 * M)) ^ 2 * (1 + (M + 2 + 2 * (3 * M))) *
    (16 * M ^ 2 + 8 * (1 + 3 * M) * phaseConstant M / normalLower M u)

/-- Eigen bound, given by `M * (2 + 3 * M)`. -/
noncomputable def eigenBound (M : ℝ) : ℝ := M * (2 + 3 * M)

/-- Modal constant, given by `(1 + 2 * eigenBound M) * coordinateConstant M u + 3 * M ^ 3`. -/
noncomputable def modalConstant (M u : ℝ) : ℝ :=
  (1 + 2 * eigenBound M) * coordinateConstant M u + 3 * M ^ 3

/-- Damping constant, given by `4 * M * (6 * M + 5) * phaseConstant M`. -/
noncomputable def dampingConstant (M : ℝ) : ℝ :=
  4 * M * (6 * M + 5) * phaseConstant M

theorem error_constants_nonneg {M u : ℝ} (hM : 1 ≤ M) :
    0 ≤ coordinateConstant M u ∧ 0 ≤ modalConstant M u ∧ 0 ≤ dampingConstant M := by
  have hM0 : 0 ≤ M := by linarith
  have hD := (phaseConstant_pos hM).le
  have hb := (normalLower_pos (u := u) hM).le
  have hc : 0 ≤ coordinateConstant M u := by unfold coordinateConstant; positivity
  exact ⟨hc, by unfold modalConstant eigenBound; positivity,
    by unfold dampingConstant; positivity⟩

/-- Only numerical scale conditions occur here.  In particular, no normal,
coefficient, solution, or covariance estimate is assumed. -/
structure LargeBand (h M u : ℝ) (n : ℕ) : Prop where
  four_le : 4 ≤ n
  two_le_scale : 2 ≤ ChartScales.S n
  epsilon_square : ChartScales.S n ^ 2 * ChartScales.epsilon h n ^ 2 ≤ 1
  carrier : ChartScales.S n ^ 2 / (ChartScales.carrier h n : ℝ) ≤ 1
  epsilon : ChartScales.epsilon h n * ChartScales.S n ^ 2 ≤ 1
  small : phaseConstant M / ChartScales.S n ≤ normalLower M u / 2

/-- All constants are fixed before this threshold.  An arbitrary previous
band cutoff and arbitrary additional slow-scale requirement are allowed. -/
theorem exists_large_band (h M u T : ℝ) (hh : 0 < h) (hM : 1 ≤ M) (N0 : ℕ) :
    ∃ N ≥ N0, ∀ n ≥ N, LargeBand h M u n ∧ T ≤ ChartScales.S n := by
  have hb := normalLower_pos (u := u) hM
  have hD := phaseConstant_pos hM
  have hs := PhaseEstimates.chart_S_tendsto_atTop.eventually
    (eventually_ge_atTop (max T (max 2 (2 * phaseConstant M / normalLower M u))))
  have hall : ∀ᶠ n : ℕ in atTop, LargeBand h M u n ∧ T ≤ ChartScales.S n := by
    filter_upwards [PhaseEstimates.eventually_band_conditions h hh, hs,
      (eventually_ge_atTop (4 : ℕ))] with n hn hscale hn4
    have hS2 : 2 ≤ ChartScales.S n := (le_max_left _ _).trans ((le_max_right _ _).trans hscale)
    have hS0 : 0 < ChartScales.S n := by linarith
    have hcut : 2 * phaseConstant M / normalLower M u ≤ ChartScales.S n :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hscale)
    refine ⟨⟨hn4, hS2, hn.2.1, hn.2.2.1, hn.2.2.2, ?_⟩, (le_max_left _ _).trans hscale⟩
    apply (div_le_iff₀ hS0).2
    have ht := (div_le_iff₀ hb).1 hcut
    nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hall
  exact ⟨max N N0, le_max_right _ _, fun n hn => hN n ((le_max_left _ _).trans hn)⟩

theorem base_error_on_mesh {S ε M : ℝ} (hS : 1 ≤ S) (hM : 1 ≤ M)
    (hε : S ^ 2 * ε ^ 2 ≤ 1) :
    M * (3 / S ^ 3 + ε ^ 2) ≤ 16 * M ^ 2 / S ∧
    4 * M ^ 2 * (3 / S ^ 3 + ε ^ 2) ≤ 16 * M ^ 2 / S := by
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  have hM0 : 0 ≤ M := by linarith
  have he : ε ^ 2 ≤ 1 / S := by
    apply (le_div_iff₀ hS0).2
    have hsq : S ≤ S ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg ε)
    nlinarith
  have hcube := (PhaseEstimates.inverse_cube_bounds hS).1
  have hsum : 3 / S ^ 3 + ε ^ 2 ≤ 4 / S := by
    calc
      _ = 3 * (1 / S ^ 3) + ε ^ 2 := by ring
      _ ≤ 3 * (1 / S) + 1 / S := add_le_add
        (mul_le_mul_of_nonneg_left hcube (by norm_num)) he
      _ = _ := by ring
  have h4 : 4 * M ^ 2 * (3 / S ^ 3 + ε ^ 2) ≤ 16 * M ^ 2 / S := by
    calc
      _ ≤ 4 * M ^ 2 * (4 / S) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  refine ⟨?_, h4⟩
  exact (mul_le_mul_of_nonneg_right (by nlinarith : M ≤ 4 * M ^ 2)
    (by positivity : 0 ≤ 3 / S ^ 3 + ε ^ 2)).trans h4

/-- Fixed normalized-base data and frozen representative data.  The
representative point is selected separately from the actual enlarged
mesh; the equality and distance fields are the interface to that proof.
All phase quantities below are constructed from this record. -/
structure FamilyData {ι : Type*} (D : PhaseJetBounds.Domain ι Slow)
    (h r0 u M : ℝ) where
  /-- Band of `FamilyData`, of type `ι → ℕ`. -/
  band : ι → ℕ
  scale_eq : ∀ i, D.scale i = ChartScales.S (band i)
  /-- F of `FamilyData`, of type `ι → Slow → ℝ`. -/
  F : ι → Slow → ℝ
  /-- Geometric data of `FamilyData`, of type `ι → Slow → ℝ`. -/
  G : ι → Slow → ℝ
  /-- F0 of `FamilyData`, of type `ι → Slow → ℝ`. -/
  F0 : ι → Slow → ℝ
  /-- G0 of `FamilyData`, of type `ι → Slow → ℝ`. -/
  G0 : ι → Slow → ℝ
  /-- U of `FamilyData`, of type `ι → Set Slow`. -/
  U : ι → Set Slow
  /-- Q0 of `FamilyData`, of type `ι → Slow`. -/
  q0 : ι → Slow
  /-- K of `FamilyData`, of type `ι → Plane`. -/
  K : ι → Plane
  /-- Lam of `FamilyData`, of type `ι → ℝ`. -/
  lam : ι → ℝ
  /-- C0 of `FamilyData`, of type `ι → ℝ`. -/
  c0 : ι → ℝ
  /-- Sigma of `FamilyData`, of type `ι → ℝ`. -/
  sigma : ι → ℝ
  /-- Theta of `FamilyData`, of type `ι → ℝ`. -/
  theta : ι → ℝ
  base : ∀ i, PhaseEstimates.LocalBaseBounds (F i) (G i) (F0 i) (G0 i) (U i) M
    (ChartScales.epsilon h (band i))
  baseF : PhaseJetBounds.PolynomialJets D F
  baseG : PhaseJetBounds.PolynomialJets D G
  inside : ∀ i, D.carrier i ⊆ U i
  representative_inside : ∀ i, q0 i ∈ U i
  distance : ∀ i q, q ∈ D.carrier i → ‖q - q0 i‖ ≤ 3 / D.scale i ^ 3
  radius : ∀ i q, q ∈ D.carrier i → 1 / M ≤ |q.1| ∧ |q.1| ≤ M
  representative_radius : ∀ i, 1 / M ≤ |(q0 i).1| ∧ |(q0 i).1| ≤ M
  unit : ∀ i, ‖K i‖ = 1
  orthogonal : ∀ i, ⟪K i, PhaseEstimates.shearVector (F0 i) (G0 i) (q0 i)⟫_ℝ = 0
  frequency_bound : ∀ i, |F0 i (q0 i)| ≤ M
  shear_bound : ∀ i, ‖PhaseEstimates.shearVector (F0 i) (G0 i) (q0 i)‖ ≤ M
  shear_inv : ∀ i, 1 / M ≤ ‖PhaseEstimates.shearVector (F0 i) (G0 i) (q0 i)‖
  lambda_bound : ∀ i, 1 / M ≤ lam i ∧ lam i ≤ M
  ratio_bound : ∀ i, 1 / M ≤ |c0 i| ∧ |c0 i| ≤ M
  eigen12 : ∀ i, lam i / c0 i = 2 * F0 i (q0 i) * (MovingFrameODE.quarterTurn (K i)) 0
  eigen21 : ∀ i, lam i * c0 i =
    -(2 * F0 i (q0 i) * (MovingFrameODE.quarterTurn (K i)) 0 +
      ⟪MovingFrameODE.quarterTurn (K i), PhaseEstimates.shearVector (F0 i) (G0 i) (q0 i)⟫_ℝ)
  sign : ∀ i, |sigma i| = 1

namespace FamilyData

variable {ι : Type*} {D : PhaseJetBounds.Domain ι Slow} {h r0 u M : ℝ}
variable (a : FamilyData D h r0 u M)

/-- Length, given by `ChartScales.slotLength r0 h (a.band i)`. -/
noncomputable def length (i : ι) : ℝ := ChartScales.slotLength r0 h (a.band i)
/-- Viscosity, given by `ChartScales.epsilon h (a.band i) * (ChartScales.carrier h (a.band i) :
ℝ) ^ 2`. -/
noncomputable def viscosity (i : ι) : ℝ :=
  ChartScales.epsilon h (a.band i) * (ChartScales.carrier h (a.band i) : ℝ) ^ 2
/-- B, given by `referenceScale (a.lam i) (a.viscosity i) u`. -/
noncomputable def B (i : ι) : ℝ := referenceScale (a.lam i) (a.viscosity i) u
/-- Frequency, constructed using `PhaseEstimates.representativeFrequency`. -/
noncomputable def frequency (i : ι) : Plane :=
  PhaseEstimates.representativeFrequency (a.B i) (a.sigma i) u (a.length i) (a.K i)
    (PhaseEstimates.shearVector (a.F0 i) (a.G0 i) (a.q0 i))
/-- Target, given by `(a.q0 i).1 * a.frequency i 0`. -/
noncomputable def target (i : ι) : ℝ := (a.q0 i).1 * a.frequency i 0
/-- Phase, bundling `epsilon`, `p`, `pz`, `x0` and the required compatibility proofs. -/
noncomputable def phase : PhaseJetBounds.PhaseFamily ι where
  epsilon i := ChartScales.epsilon h (a.band i)
  p i := PhaseEstimates.roundedFrequency (ChartScales.carrier h (a.band i)) (a.target i)
  pz i := a.frequency i 1
  x0 i := a.sigma i * a.B i * u / 2
  theta := a.theta
  F := a.F
  G := a.G
/-- Frame, given by `a.phase.frameData a.lam a.c0 (fun _ => u) a.length a.viscosity i`. -/
noncomputable def frame (i : ι) : PrimaryODE.FrameData Slow :=
  a.phase.frameData a.lam a.c0 (fun _ => u) a.length a.viscosity i
/-- Slot, given by `Ioo (-(a.length i)) (2 * a.length i)`. -/
noncomputable def slot (i : ι) : Set ℝ := Ioo (-(a.length i)) (2 * a.length i)
/-- Slope, given by `PhaseEstimates.signedSlot (a.sigma i) u (a.length i) z.2`. -/
noncomputable def slope (i : ι) (z : Slow × ℝ) : ℝ :=
  PhaseEstimates.signedSlot (a.sigma i) u (a.length i) z.2

/-- The actual angular carrier is a nonzero integer, including the
zero-floor case, which is replaced by the integer one. -/
noncomputable def angularMode (i : ι) : ℤ :=
  PhaseEstimates.nonzeroRound ((ChartScales.carrier h (a.band i) : ℝ) * a.target i)

theorem angularMode_ne_zero (i : ι) : a.angularMode i ≠ 0 :=
  PhaseEstimates.nonzeroRound_ne_zero _

theorem carrier_mul_angular_frequency (i : ι) :
    (ChartScales.carrier h (a.band i) : ℝ) * a.phase.p i = (a.angularMode i : ℝ) :=
  PhaseEstimates.roundedFrequency_integer
    (zero_lt_one.trans_le (PhaseEstimates.chart_carrier_ge_one h (a.band i))).ne' _

theorem angular_rounding_error (i : ι) :
    |a.phase.p i - a.target i| ≤ 1 / (ChartScales.carrier h (a.band i) : ℝ) :=
  PhaseEstimates.roundedFrequency_error
    (zero_lt_one.trans_le (PhaseEstimates.chart_carrier_ge_one h (a.band i))) _

theorem lambda_pos (hM : 1 ≤ M) (i : ι) : 0 < a.lam i :=
  (one_div_pos.mpr (zero_lt_one.trans_le hM)).trans_le (a.lambda_bound i).1

theorem ratio_ne (hM : 1 ≤ M) (i : ι) : a.c0 i ≠ 0 :=
  abs_pos.mp ((one_div_pos.mpr (zero_lt_one.trans_le hM)).trans_le (a.ratio_bound i).1)

theorem B_bounds (hh : 0 ≤ h) (hM : 1 ≤ M) (i : ι) :
    normalLower M u ≤ a.B i ∧ a.B i ≤ M := by
  have hv := ChartScales.carrier_viscosity_bounds h hh (a.band i)
  have hb := referenceScale_bounds (u := u)
    (one_div_pos.mpr (zero_lt_one.trans_le hM)) (a.lambda_bound i).1 (a.lambda_bound i).2 hv.1 hv.2
  refine ⟨hb.1, hb.2.trans ?_⟩
  calc
    Real.sqrt M ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = M := Real.sqrt_sq (by linarith)

theorem B_pos (hh : 0 ≤ h) (hM : 1 ≤ M) (i : ι) : 0 < a.B i :=
  (normalLower_pos hM).trans_le (a.B_bounds hh hM i).1

theorem length_pos (hr : 0 < r0) (i : ι) : 0 < a.length i :=
  div_pos (mul_pos (by norm_num) hr) (ChartScales.timeCoefficient_pos h (a.band i))

theorem reciprocal_bound {x : ℝ} (hM : 1 ≤ M) (hx : 1 / M ≤ x) : 1 / x ≤ M := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hx0 := (one_div_pos.mpr hM0).trans_le hx
  apply (div_le_iff₀ hx0).2
  have hi := (div_le_iff₀ hM0).1 hx
  nlinarith

theorem length_inverse (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 / (2 * r0) ≤ M)
    (i : ι) (hn : 4 ≤ a.band i) : 1 / |a.length i| ≤ M / D.scale i := by
  have hS : 0 < D.scale i := zero_lt_one.trans_le (D.one_le_scale i)
  have hl := (ChartScales.slotLength_bounds r0 h hr.le hh hn).1
  rw [← a.scale_eq i] at hl
  rw [abs_of_pos (a.length_pos hr i)]
  calc
    _ ≤ 1 / (2 * r0 * D.scale i) :=
      one_div_le_one_div_of_le (by positivity) hl
    _ = (1 / (2 * r0)) / D.scale i := by ring
    _ ≤ M / D.scale i := div_le_div_of_nonneg_right hM hS.le

theorem slot_abs (hr : 0 < r0) {i : ι} {v : ℝ} (hv : v ∈ a.slot i) :
    |v| ≤ 2 * a.length i := by
  have hL := a.length_pos hr i
  exact abs_le.mpr ⟨by dsimp [slot] at hv; linarith [hv.1], le_of_lt hv.2⟩

theorem slot_bound (hh : 0 ≤ h) (hr : 0 < r0) (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    {i : ι} (hn : 4 ≤ a.band i) {v : ℝ} (hv : v ∈ a.slot i) :
    |v| ≤ M * D.scale i := by
  have hl := (ChartScales.slotLength_bounds r0 h hr.le hh hn).2
  rw [← a.scale_eq i] at hl
  change a.length i ≤ 2 * r0 * ChartScales.Tg * D.scale i at hl
  have hS : 0 ≤ D.scale i := (zero_lt_one.trans_le (D.one_le_scale i)).le
  have hm := mul_le_mul_of_nonneg_right hslot hS
  nlinarith [a.slot_abs hr hv]

theorem magnitude_bound (hr : 0 < r0) (hu : 0 ≤ u) (huM : u ≤ M)
    {i : ι} {v : ℝ} (hv : v ∈ a.slot i) :
    |PulseGrowth.slotMagnitude u (a.length i) v| ≤ 3 * M := by
  have hL := a.length_pos hr i
  have hv' := a.slot_abs hr hv
  have hmul : |u * v / a.length i| ≤ 2 * u := by
    rw [abs_div, abs_mul, abs_of_nonneg hu, abs_of_pos hL]
    apply (div_le_iff₀ hL).2
    nlinarith [mul_le_mul_of_nonneg_left hv' hu]
  have ha := abs_add_le (u / 2) (u * v / a.length i)
  rw [abs_div, abs_of_nonneg hu] at ha
  norm_num at ha
  dsimp [PulseGrowth.slotMagnitude]
  linarith

theorem slope_bound (hr : 0 < r0) (hu : 0 ≤ u) (huM : u ≤ M)
    {i : ι} {q : Slow} {v : ℝ} (hv : v ∈ a.slot i) : |a.slope i (q, v)| ≤ 3 * M := by
  simpa only [slope, PhaseEstimates.signedSlot, PulseGrowth.slotMagnitude, abs_mul, a.sign i,
      one_mul] using
    a.magnitude_bound hr hu huM hv

theorem frequency_identity (hM : 1 ≤ M) (i : ι) :
    (!₂[a.target i / (a.q0 i).1, a.frequency i 1] : Plane) = a.frequency i := by
  have hr : (a.q0 i).1 ≠ 0 := abs_pos.mp
    ((one_div_pos.mpr (zero_lt_one.trans_le hM)).trans_le (a.representative_radius i).1)
  ext j
  fin_cases j
  · change (a.q0 i).1 * a.frequency i 0 / (a.q0 i).1 = a.frequency i 0
    field_simp
  · rfl

theorem frequencies_bounded (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : |u| ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (i : ι) (hn : 4 ≤ a.band i) :
    |a.target i| ≤ M * (M + M ^ 4) ∧ |a.frequency i 1| ≤ M + M ^ 4 := by
  have hr0 : (a.q0 i).1 ≠ 0 := abs_pos.mp
    ((one_div_pos.mpr (zero_lt_one.trans_le hM)).trans_le (a.representative_radius i).1)
  exact PhaseEstimates.representative_uniform_frequency_bounds hr0 (by linarith)
    (D.one_le_scale i) (by simpa only [abs_of_pos (a.B_pos hh hM i)] using (a.B_bounds hh hM i).2)
    (a.sign i) hu (reciprocal_bound hM (a.shear_inv i))
    (a.length_inverse hh hr hL i hn) (a.unit i) (a.representative_radius i).2
    (a.frequency_identity hM i)

theorem frozen_constants (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : |u| ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (i : ι) (hn : 4 ≤ a.band i) :
    |a.phase.epsilon i| ≤ frequencyBound M ∧ |a.phase.p i| ≤ frequencyBound M ∧
    |a.phase.pz i| ≤ frequencyBound M ∧ |a.phase.x0 i| ≤ frequencyBound M := by
  have hb := frequencyBound_bounds hM
  have hf := a.frequencies_bounded hh hr hM hu hL i hn
  have hk := PhaseEstimates.chart_carrier_ge_one h (a.band i)
  have hround := PhaseEstimates.roundedFrequency_error (zero_lt_one.trans_le hk) (a.target i)
  have hinv : 1 / (ChartScales.carrier h (a.band i) : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hk
  refine ⟨?_, ?_, hf.2.trans hb.2.2.1, ?_⟩
  · have he := ChartScales.epsilon_le_one h hh (a.band i)
    simpa only [phase, abs_of_pos (ChartScales.epsilon_pos h (a.band i))] using
      he.trans (hM.trans hb.1)
  · have htri := abs_sub_le (PhaseEstimates.roundedFrequency (ChartScales.carrier h (a.band i))
      (a.target i)) (a.target i) 0
    simp only [sub_zero] at htri
    change |PhaseEstimates.roundedFrequency (ChartScales.carrier h (a.band i)) (a.target i)| ≤ _
    linarith [hb.2.1]
  · change |a.sigma i * a.B i * u / 2| ≤ _
    rw [abs_div, abs_mul, abs_mul, a.sign i, one_mul, abs_of_pos (a.B_pos hh hM i)]
    norm_num
    have hm := mul_le_mul (a.B_bounds hh hM i).2 hu (abs_nonneg u) (by linarith : 0 ≤ M)
    nlinarith [hb.2.2.2.1, sq_nonneg M]

/-- Actual phase-normal and normal-motion estimates for every enlarged
slot point.  These follow from the normalized base error and rounding. -/
theorem phase_estimates (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : |u| ≤ M) (hL : 1 / (2 * r0) ≤ M) (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (i : ι) (hn : LargeBand h M u (a.band i)) {q : Slow} (hq : q ∈ D.carrier i)
    {v : ℝ} (hv : v ∈ a.slot i) :
    ‖a.phase.normal i (q, v) - MovingFrameODE.pack (a.B i * a.slope i (q, v)) (a.B i • a.K i)‖ ≤
      phaseConstant M / D.scale i ∧
    ‖a.phase.velocity i (q, v)‖ ≤ phaseConstant M / D.scale i := by
  have hb := frequencyBound_bounds hM
  have hf := a.frequencies_bounded hh hr hM hu hL i hn.four_le
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hR : q.1 ≠ 0 := abs_pos.mp ((one_div_pos.mpr hM0).trans_le (a.radius i q hq).1)
  have hR0 : (a.q0 i).1 ≠ 0 := abs_pos.mp
    ((one_div_pos.mpr hM0).trans_le (a.representative_radius i).1)
  have hg : PhaseEstimates.shearVector (a.F0 i) (a.G0 i) (a.q0 i) ≠ 0 :=
    norm_pos_iff.mp ((one_div_pos.mpr hM0).trans_le (a.shear_inv i))
  have hinvR : |1 / q.1| ≤ M := by
    simpa only [abs_div, abs_one] using reciprocal_bound hM (a.radius i q hq).1
  have hinvR0 : |1 / (a.q0 i).1| ≤ M := by
    simpa only [abs_div, abs_one] using reciprocal_bound hM (a.representative_radius i).1
  have hS0 : 0 ≤ D.scale i := (zero_lt_one.trans_le (D.one_le_scale i)).le
  have he := phase_errors_on_mesh (θ := a.theta i) (v := v)
    (localBase_mono (a.base i) hb.1) (a.inside i hq) (a.representative_inside i)
    (a.distance i q hq) hR hR0 hg (a.orthogonal i) (a.frequency_identity hM i)
    (hM.trans hb.1) (by simpa only [a.scale_eq i] using hn.two_le_scale)
    (PhaseEstimates.chart_carrier_ge_one h (a.band i)) (ChartScales.epsilon_pos h (a.band i))
    (hf.1.trans (by linarith [hb.2.1])) (hf.2.trans hb.2.2.1)
    (by simpa only [abs_of_pos (a.B_pos hh hM i)] using (a.B_bounds hh hM i).2.trans hb.1)
    (a.sign i) (hu.trans hb.1) ((reciprocal_bound hM (a.shear_inv i)).trans hb.1)
    ((a.length_inverse hh hr hL i hn.four_le).trans (div_le_div_of_nonneg_right hb.1 hS0))
    ((a.slot_bound hh hr hslot hn.four_le hv).trans (mul_le_mul_of_nonneg_right hb.1 hS0))
    (hinvR.trans hb.1) (hinvR0.trans hb.1)
    (by simpa only [a.scale_eq i] using hn.epsilon_square)
    (by simpa only [a.scale_eq i] using hn.carrier)
    (by simpa only [a.scale_eq i] using hn.epsilon)
  exact he

theorem base_estimates (hM : 1 ≤ M) (i : ι) (hn : LargeBand h M u (a.band i))
    {q : Slow} (hq : q ∈ D.carrier i) :
    |a.F i q - a.F0 i (a.q0 i)| ≤ 16 * M ^ 2 / D.scale i ∧
    ‖PhaseEstimates.shearVector (a.F i) (a.G i) q -
      PhaseEstimates.shearVector (a.F0 i) (a.G0 i) (a.q0 i)‖ ≤ 16 * M ^ 2 / D.scale i := by
  have hb := base_error_on_mesh (D.one_le_scale i) hM
    (by simpa only [a.scale_eq i] using hn.epsilon_square)
  exact ⟨(PhaseEstimates.localBase_value_error (a.base i) (by linarith)
    (a.inside i hq) (a.representative_inside i) (a.distance i q hq)).trans hb.1,
    (PhaseEstimates.localBase_shear_error (a.base i) hM (a.inside i hq)
      (a.representative_inside i) (a.distance i q hq) (a.representative_radius i).2).trans hb.2⟩

theorem phase_error_small (hh : 0 ≤ h) (hM : 1 ≤ M) (i : ι)
    (hn : LargeBand h M u (a.band i)) : phaseConstant M / D.scale i ≤ a.B i / 2 := by
  have hs : phaseConstant M / D.scale i ≤ normalLower M u / 2 := by
    simpa only [a.scale_eq i] using hn.small
  exact hs.trans (div_le_div_of_nonneg_right (a.B_bounds hh hM i).1 (by norm_num))

theorem quotient_rate_bound (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : |u| ≤ M) (hL : 1 / (2 * r0) ≤ M) (i : ι) (hn : 4 ≤ a.band i) :
    |u / a.length i| ≤ M ^ 2 / D.scale i := by
  have hi := a.length_inverse hh hr hL i hn
  calc
    _ = |u| * (1 / |a.length i|) := by rw [abs_div]; ring
    _ ≤ M * (M / D.scale i) := mul_le_mul hu hi
      (one_div_nonneg.mpr (abs_nonneg _)) (by linarith)
    _ = _ := by ring

/-- The three coordinate errors of the actual constructed tangent frame
are estimated before changing to the moving eigenbasis. -/
theorem coordinate_errors (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (i : ι) (hn : LargeBand h M u (a.band i)) {q : Slow} (hq : q ∈ D.carrier i)
    {v : ℝ} (hv : v ∈ a.slot i) :
    |(a.frame i).errorA (q, v)| ≤ coordinateConstant M u / D.scale i ∧
    |(a.frame i).errorB (q, v)| ≤ coordinateConstant M u / D.scale i ∧
    |(a.frame i).errorC (q, v)| ≤ coordinateConstant M u / D.scale i := by
  have hS : 0 < D.scale i := zero_lt_one.trans_le (D.one_le_scale i)
  have hM0 : 0 ≤ M := by linarith
  have he := a.phase_estimates hh hr hM (by simpa only [abs_of_pos hu] using huM)
    hL hslot i hn hq hv
  have hb := a.base_estimates hM i hn hq
  have hs := a.slope_bound hr hu.le huM (q := q) hv
  have hc := frame_errors_of_normal_close (normalLower_pos hM) (a.B_bounds hh hM i).1
    (a.unit i) (a.phase_error_small hh hM i hn) he.1 he.2 hM
    (by positivity : 0 ≤ 3 * M) hs (a.frequency_bound i) (a.shear_bound i) (a.orthogonal i)
    (by positivity : 0 ≤ 16 * M ^ 2 / D.scale i) hb.1 hb.2
  have heq : 16 * (M + 2 + 2 * (3 * M)) ^ 2 * (1 + (M + 2 + 2 * (3 * M))) *
      (16 * M ^ 2 / D.scale i + 8 * (1 + 3 * M) * (phaseConstant M / D.scale i) / normalLower M u) =
      coordinateConstant M u / D.scale i := by unfold coordinateConstant; ring
  dsimp only at hc
  rw [heq] at hc
  have href := reference_off_diagonal (u := u) (L := a.length i) (v := v)
    (s := a.slope i (q, v)) (a.ratio_ne hM i) (signedSlot_sq (a.sign i) u (a.length i) v)
    (a.eigen12 i) (a.eigen21 i)
  refine ⟨hc.1, ?_, ?_⟩
  · change |MovingFrameODE.coeff12 (a.F i q) (PrimaryODE.localFrame (a.phase.normal i (q, v)) 1 0)
      (MovingFrameODE.radialSlope (a.phase.normal i (q, v)))
      (PhaseEstimates.angularVelocity (a.phase.normal i (q, v)) (a.phase.velocity i (q, v))) -
      ViscousPropagator.referenceEigenvalue (a.lam i) u (a.length i) v /
        PrimaryODE.referenceProfile (a.c0 i) u (a.length i) v| ≤ _
    rw [href.1]
    exact hc.2.1
  · change |MovingFrameODE.coeff21 (a.F i q) (PrimaryODE.localFrame (a.phase.normal i (q, v)) 1 0)
      ⟪PrimaryODE.localFrame (a.phase.normal i (q, v)) 1,
        PhaseEstimates.shearVector (a.F i) (a.G i) q⟫_ℝ
      (MovingFrameODE.radialSlope (a.phase.normal i (q, v)))
      (PhaseEstimates.angularVelocity (a.phase.normal i (q, v)) (a.phase.velocity i (q, v))) -
      ViscousPropagator.referenceEigenvalue (a.lam i) u (a.length i) v *
        PrimaryODE.referenceProfile (a.c0 i) u (a.length i) v| ≤ _
    rw [href.2]
    exact hc.2.2

theorem modal_errors (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (i : ι) (hn : LargeBand h M u (a.band i)) {q : Slow} (hq : q ∈ D.carrier i)
    {v : ℝ} (hv : v ∈ a.slot i) :
    |(a.frame i).error11 (q, v)| ≤ modalConstant M u / D.scale i ∧
    |(a.frame i).error12 (q, v)| ≤ modalConstant M u / D.scale i ∧
    |(a.frame i).error21 (q, v)| ≤ modalConstant M u / D.scale i ∧
    |(a.frame i).error22 (q, v)| ≤ modalConstant M u / D.scale i := by
  have hM0 : 0 ≤ M := by linarith
  have hS : 0 < D.scale i := zero_lt_one.trans_le (D.one_le_scale i)
  have hc := a.coordinate_errors hh hr hM hu huM hL hslot i hn hq hv
  have hmag := a.magnitude_bound hr hu.le huM hv
  have hprof := reference_profile_bounds (one_div_pos.mpr (zero_lt_one.trans_le hM))
    (a.ratio_bound i).1 (a.ratio_bound i).2 hmag
  have hrate := reference_profile_rate_bound (by positivity : 0 ≤ 3 * M)
    (sq_nonneg M) hS hmag (a.quotient_rate_bound hh hr hM
      (by simpa only [abs_of_pos hu] using huM) hL i hn.four_le)
  have hH : 0 ≤ eigenBound M := by unfold eigenBound; positivity
  have hH1 : M * (1 + 3 * M) ≤ eigenBound M := by unfold eigenBound; nlinarith
  have hH2 : M ≤ eigenBound M := by unfold eigenBound; nlinarith
  have hhi : |1 / PrimaryODE.referenceProfile (a.c0 i) u (a.length i) v| ≤ eigenBound M := by
    simpa only [one_div_one_div] using hprof.2.trans (by simpa only [one_div_one_div] using hH2)
  have hout := MovingFrameODE.modal_errors_le hH hc.1 hc.2.1 hc.2.2
    (hprof.1.trans hH1) hhi hrate
  have heq : (1 + 2 * eigenBound M) * (coordinateConstant M u / D.scale i) +
      (3 * M) * M ^ 2 / D.scale i = modalConstant M u / D.scale i := by
    unfold modalConstant
    ring
  rw [heq] at hout
  exact hout

/-- Two-sided comparison with the Gaussian reference viscosity. -/
theorem damping_error (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (i : ι) (hn : LargeBand h M u (a.band i)) {q : Slow} (hq : q ∈ D.carrier i)
    {v : ℝ} (hv : v ∈ a.slot i) :
    |(a.frame i).viscosity (q, v) -
      ViscousPropagator.referenceViscosity (a.lam i) u (a.length i) v| ≤ dampingConstant M /
          D.scale i := by
  have hvb := ChartScales.carrier_viscosity_bounds h hh (a.band i)
  have hν : 0 < a.viscosity i := zero_lt_one.trans_le hvb.1
  have he := (a.phase_estimates hh hr hM (by simpa only [abs_of_pos hu] using huM)
    hL hslot i hn hq hv).1
  have hout := damping_error_of_normal_close (a.unit i) (a.B_pos hh hM i)
    (a.B_bounds hh hM i).2 (a.slope_bound hr hu.le huM (q := q) hv)
    (a.phase_error_small hh hM i hn) he hν.le hvb.2
  have hB : a.viscosity i * a.B i ^ 2 = a.lam i / dampingDenominator u :=
    referenceScale_normalization (a.lambda_pos hM i) hν
  have href : a.viscosity i * a.B i ^ 2 * (1 + a.slope i (q, v) ^ 2) =
      ViscousPropagator.referenceViscosity (a.lam i) u (a.length i) v := by
    rw [hB, show a.slope i (q, v) ^ 2 = PulseGrowth.slotMagnitude u (a.length i) v ^ 2 from
      signedSlot_sq (a.sign i) u (a.length i) v]
    unfold ViscousPropagator.referenceViscosity dampingDenominator
    ring
  rw [href] at hout
  convert! hout using 1
  unfold dampingConstant
  ring

theorem interval_subset_slot (hr : 0 < r0) (i : ι) : Icc 0 (a.length i) ⊆ a.slot i := by
  intro v hv
  have hL := a.length_pos hr i
  exact ⟨by linarith [hv.1], by linarith [hv.2]⟩

theorem normal_nonzero (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : |u| ≤ M) (hL : 1 / (2 * r0) ≤ M) (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (i : ι) (hn : LargeBand h M u (a.band i)) {q : Slow} (hq : q ∈ D.carrier i)
    {v : ℝ} (hv : v ∈ a.slot i) :
    normalLower M u / 2 ≤ MovingFrameODE.normalScale (a.phase.normal i (q, v)) ∧
    MovingFrameODE.tail (a.phase.normal i (q, v)) ≠ 0 := by
  have hn' := PhaseEstimates.normal_lower_bounds (a.B_pos hh hM i) (a.unit i)
    (a.phase_error_small hh hM i hn) (a.phase_estimates hh hr hM hu hL hslot i hn hq hv).1
  exact ⟨(div_le_div_of_nonneg_right (a.B_bounds hh hM i).1 (by norm_num)).trans hn'.1,
    hn'.2.2.1⟩

theorem kinematics (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : |u| ≤ M) (hL : 1 / (2 * r0) ≤ M) (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (i : ι) (hn : LargeBand h M u (a.band i)) {q : Slow} (hq : q ∈ D.carrier i) :
    (a.frame i).Kinematics q (Icc 0 (a.length i)) := by
  apply PrimaryODE.FrameData.ofNormalLocal_kinematics
  · intro v _
    exact PhaseCalculus.hasDerivAt_phaseNormal_slot _ _ _ _ _ _ _ _ _
      (ChartScales.epsilon_pos h (a.band i)).ne' ((a.base i).actualF q (a.inside i hq))
      ((a.base i).actualG q (a.inside i hq))
  · intro v hv
    exact (a.normal_nonzero hh hr hM hu hL hslot i hn hq (a.interval_subset_slot hr i hv)).2
  · intro v _
    exact mul_ne_zero (a.ratio_ne hM i) (by
        positivity : Real.sqrt (1 + PulseGrowth.slotMagnitude u (a.length i) v ^ 2) ≠ 0)
  · intro v _
    exact PrimaryODE.hasDerivAt_referenceProfile (a.c0 i) u (a.length i) v

theorem coefficientControl (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (i : ι) (hn : LargeBand h M u (a.band i)) {q : Slow} (hq : q ∈ D.carrier i) :
    PrimaryCovarianceBounds.CoefficientControl (a.frame i) (a.lam i) u (a.length i)
      (D.scale i) (modalConstant M u) (dampingConstant M) q where
  eigenvalue _ _ := rfl
  errors _ hv := a.modal_errors hh hr hM hu huM hL hslot i hn hq (a.interval_subset_slot hr i hv)
  viscosity _ hv := a.damping_error hh hr hM hu huM hL hslot i hn hq (a.interval_subset_slot hr i
      hv)

/-- The actual modal energy bound holds with the same constants for every
nonzero harmonic.  The damping discrepancy is not multiplied by `j²`. -/
theorem energy_bound (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (i : ι) (hn : LargeBand h M u (a.band i)) {q : Slow} (hq : q ∈ D.carrier i)
    {v : ℝ} (hv : v ∈ a.slot i) {j : ℤ} (hj : j ≠ 0) (w : Plane) :
    ⟪w, (a.frame i).coefficient j (q, v) w⟫_ℝ ≤
      (ViscousPropagator.referenceEigenvalue (a.lam i) u (a.length i) v -
        ViscousPropagator.referenceViscosity (a.lam i) u (a.length i) v +
        (dampingConstant M + 4 * modalConstant M u) / D.scale i) * ‖w‖ ^ 2 := by
  have hν : 0 ≤ (a.frame i).viscosity (q, v) := by
    change 0 ≤ a.viscosity i * ‖a.phase.normal i (q, v)‖ ^ 2
    exact mul_nonneg (zero_le_one.trans (ChartScales.carrier_viscosity_bounds h hh (a.band i)).1)
      (sq_nonneg _)
  have hl : 0 ≤ (a.frame i).eigenvalue (q, v) := by
    change 0 ≤ a.lam i / Real.sqrt (1 + PulseGrowth.slotMagnitude u (a.length i) v ^ 2)
    exact div_nonneg (a.lambda_pos hM i).le (Real.sqrt_nonneg _)
  have hd := a.damping_error hh hr hM hu huM hL hslot i hn hq hv
  apply (a.frame i).energy_bound (q, v) hj hl hν
  · linarith [(abs_le.mp hd).1]
  · exact a.modal_errors hh hr hM hu huM hL hslot i hn hq hv

/-- Output bound, given by `frequencyBound M + 3 * M + M ^ 2 + 4`. -/
noncomputable def outputBound (M : ℝ) : ℝ := frequencyBound M + 3 * M + M ^ 2 + 4
/-- Output lower, given by `min (normalLower M u / 2) (1 / M)`. -/
noncomputable def outputLower (M u : ℝ) : ℝ := min (normalLower M u / 2) (1 / M)

theorem outputBound_bounds (hM : 1 ≤ M) :
    frequencyBound M ≤ outputBound M ∧ 3 * M ≤ outputBound M ∧
    M ^ 2 ≤ outputBound M ∧ 4 ≤ outputBound M ∧ M ≤ outputBound M := by
  have hb := frequencyBound_bounds hM
  have hM0 : 0 ≤ M := by linarith
  unfold outputBound
  exact ⟨by nlinarith [sq_nonneg M], by nlinarith [sq_nonneg M],
    by nlinarith, by nlinarith [sq_nonneg M], by nlinarith [sq_nonneg M]⟩

theorem outputLower_pos (hM : 1 ≤ M) : 0 < outputLower M u :=
  lt_min (half_pos (normalLower_pos hM)) (one_div_pos.mpr (zero_lt_one.trans_le hM))

/-- The actual phase family satisfies every order-zero input of the
previous primary-pulse theorem.  Its normal comparison, modal errors,
and damping comparison are proved here from the base and mesh data. -/
noncomputable def construction (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M)
    (hlarge : ∀ i, LargeBand h M u (a.band i)) : PrimaryPulseBounds.PhaseConstruction D := by
  have hb := outputBound_bounds hM
  have he := error_constants_nonneg (u := u) hM
  have huabs : |u| ≤ M := by simpa only [abs_of_pos hu] using huM
  refine {
    phase := a.phase
    V := a.slot
    openV := fun _ => isOpen_Ioo
    lam := a.lam
    c0 := a.c0
    u := fun _ => u
    L := a.length
    viscosity := a.viscosity
    B := a.B
    K := a.K
    slope := a.slope
    error := fun i _ => phaseConstant M / D.scale i
    r := 1 / M
    b := outputLower M u
    M := outputBound M
    C := modalConstant M u
    E := dampingConstant M
    r_pos := one_div_pos.mpr (zero_lt_one.trans_le hM)
    b_pos := outputLower_pos hM
    one_le_M := hM.trans hb.2.2.2.2
    C_nonneg := he.2.1
    E_nonneg := he.2.2
    baseF := a.baseF
    baseG := a.baseG
    constants := ?_
    epsilon_ne := fun i => (ChartScales.epsilon_pos h (a.band i)).ne'
    radius := fun i q hq => ⟨(a.radius i q hq).1, (a.radius i q hq).2.trans hb.2.2.2.2⟩
    slot := fun i v hv => (a.slot_bound hh hr hslot (hlarge i).four_le hv).trans
      (mul_le_mul_of_nonneg_right hb.2.2.2.2 (by linarith [D.one_le_scale i]))
    lam_bound := ?_
    c0_bound := ?_
    u_bound := fun _ => huabs.trans hb.2.2.2.2
    rate_bound := ?_
    viscosity_bound := ?_
    B_bound := ?_
    K_unit := a.unit
    slope_bound := fun _ _ hz => (a.slope_bound hr hu.le huM hz.2).trans hb.2.1
    error_small := fun i _ _ => a.phase_error_small hh hM i (hlarge i)
    normal_close := fun i _ hz => (a.phase_estimates hh hr hM huabs hL hslot i (hlarge i) hz.1
        hz.2).1
    lam_pos := a.lambda_pos hM
    u_pos := fun _ => hu
    L_pos := a.length_pos hr
    interval := a.interval_subset_slot hr
    viscosity_nonneg := fun i => zero_le_one.trans (ChartScales.carrier_viscosity_bounds h hh
        (a.band i)).1
    damping_error := ?_
    modal_errors := fun i q hq v hv =>
      a.modal_errors hh hr hM hu huM hL hslot i (hlarge i) hq (a.interval_subset_slot hr i hv) }
  · intro i
    have hc := a.frozen_constants hh hr hM huabs hL i (hlarge i).four_le
    exact ⟨hc.1.trans hb.1, hc.2.1.trans hb.1, hc.2.2.1.trans hb.1, hc.2.2.2.trans hb.1⟩
  · intro i
    simpa only [abs_of_pos (a.lambda_pos hM i)] using (a.lambda_bound i).2.trans hb.2.2.2.2
  · intro i
    exact ⟨(min_le_right _ _).trans (a.ratio_bound i).1, (a.ratio_bound i).2.trans hb.2.2.2.2⟩
  · intro i
    have hi := a.quotient_rate_bound hh hr hM huabs hL i (hlarge i).four_le
    exact ((le_div_iff₀ (zero_lt_one.trans_le (D.one_le_scale i))).1 hi).trans hb.2.2.1
  · intro i
    have hv := ChartScales.carrier_viscosity_bounds h hh (a.band i)
    simpa only [viscosity, abs_of_nonneg (zero_le_one.trans hv.1)] using hv.2.trans hb.2.2.2.1
  · intro i
    have hlo : outputLower M u ≤ normalLower M u / 2 := min_le_left _ _
    exact ⟨(by linarith [(a.B_bounds hh hM i).1]), (a.B_bounds hh hM i).2.trans hb.2.2.2.2⟩
  · intro i q hq v hv
    have hd := a.damping_error hh hr hM hu huM hL hslot i (hlarge i) hq (a.interval_subset_slot hr
        i hv)
    change ViscousPropagator.referenceViscosity (a.lam i) u (a.length i) v -
      dampingConstant M / D.scale i ≤ (a.frame i).viscosity (q, v)
    linarith [(abs_le.mp hd).1]

theorem construction_frame (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M) (hlarge : ∀ i, LargeBand h M u (a.band i)) :
    (a.construction hh hr hM hu huM hL hslot hlarge).frame = a.frame := rfl

/-- Every fixed derivative of the actual coefficient is controlled after
the derived zeroth-order geometry is inserted. -/
theorem frame_jets (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M) (hlarge : ∀ i, LargeBand h M u (a.band i)) :
    PhaseJetBounds.FrameJets (D.slot a.slot (fun _ => isOpen_Ioo)) a.frame := by
  let p := a.construction hh hr hM hu huM hL hslot hlarge
  exact p.phase.frameData_jets_of_phase_comparison D p.V p.openV p.lam p.c0 p.u p.L
    p.viscosity p.B p.K p.slope p.error p.baseF p.baseG p.r_pos p.b_pos p.one_le_M
    p.constants p.epsilon_ne p.radius p.slot p.lam_bound p.c0_bound p.u_bound p.rate_bound
    p.viscosity_bound p.B_bound p.K_unit p.slope_bound p.error_small p.normal_close

theorem pulse_jets (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M) (hlarge : ∀ i, LargeBand h M u (a.band i)) :
    PrimaryPulseBounds.EnvelopeJets
      (PrimaryPulseBounds.productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
      (fun i z => PrimaryPulseBounds.referenceP (a.lam i) u (a.length i) (a.length i * z.2))
      (fun i => PrimaryPulseBounds.normalizedPulse (a.frame i) (a.lam i) u (a.length i)) :=
  (a.construction hh hr hM hu huM hL hslot hlarge).pulse_jets

theorem coefficient_jets (hh : 0 ≤ h) (hr : 0 < r0) (hM : 1 ≤ M)
    (hu : 0 < u) (huM : u ≤ M) (hL : 1 / (2 * r0) ≤ M)
    (hslot : 4 * r0 * ChartScales.Tg ≤ M) (hlarge : ∀ i, LargeBand h M u (a.band i)) (j : ℤ) :
    PhaseJetBounds.PolynomialJets (D.slot a.slot (fun _ => isOpen_Ioo))
      (fun i => (a.frame i).coefficient j) :=
  (a.frame_jets hh hr hM hu huM hL hslot hlarge).coefficient j

end FamilyData

namespace Representatives

open PrimaryRepresentatives

theorem normal_inner_shear {g : Plane} (hg : g ≠ 0) :
    ⟪normalDirection g, g⟫_ℝ = ‖g‖ := by
  calc
    _ = ⟪normalDirection g, ‖g‖ • normalDirection g⟫_ℝ := by
      rw [norm_smul_normalDirection hg]
    _ = ‖g‖ := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, normalDirection_unit hg]
      ring

/-- A compact fixed reference profile chooses every uniform constant
before the band threshold.  `A` may include all prescribed base-chart,
derivative, and radial-annulus constants. -/
theorem ordered_constants {K : Set Slow} (hK : IsCompact K)
    {F0 G0 : Slow → ℝ}
    (hF : ContinuousOn F0 K) (hg : ContinuousOn (PhaseEstimates.shearVector F0 G0) K)
    (hR : ∀ q ∈ K, 0 < q.1)
    (hc : ∀ q ∈ K, ReferenceCone (F0 q) (PhaseEstimates.shearVector F0 G0 q))
    (h r0 u A T : ℝ) (hh : 0 < h) (N0 : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ A ≤ M ∧ |u| ≤ M ∧ 1 / (2 * r0) ≤ M ∧
      4 * r0 * ChartScales.Tg ≤ M ∧
      (∀ q ∈ K, ParameterBounds M q.1 (F0 q) (PhaseEstimates.shearVector F0 G0 q)) ∧
      ∃ N ≥ N0, ∀ n ≥ N, LargeBand h M u n ∧ T ≤ ChartScales.S n := by
  obtain ⟨M0, hM0, hp⟩ := compact_parameter_bounds hK hF hg hR hc
  let M := max M0 (max A (max |u| (max (1 / (2 * r0)) (4 * r0 * ChartScales.Tg))))
  have h0 : M0 ≤ M := le_max_left _ _
  have hM : 1 ≤ M := hM0.trans h0
  refine ⟨M, hM, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _
        _))),
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _
        _))),
    fun q hq => (hp q hq).mono h0, ?_⟩
  exact exists_large_band h M u T hh hM N0

/-- One target-cone choice, one compact parameter constant, and then one
band threshold.  Both the mixed-point target margin and all analytic
phase estimates hold after that same threshold. -/
theorem ordered_target_constants {K : Set Slow} (hK : IsCompact K)
    {F0 G0 : Slow → ℝ} {T0 : Slow → Plane}
    (hF : ContinuousOn F0 K) (hg : ContinuousOn (PhaseEstimates.shearVector F0 G0) K)
    (hT : ContinuousOn T0 K) (hR : ∀ q ∈ K, 0 < q.1)
    (hc : ∀ q ∈ K, ReferenceCone (F0 q) (PhaseEstimates.shearVector F0 G0 q))
    (ht : ∀ q ∈ K, TargetCone (F0 q) (PhaseEstimates.shearVector F0 G0 q) (T0 q))
    (h r0 A Tmin : ℝ) (hh : 0 < h) (N0 : ℕ) :
    ∃ u η M : ℝ, 0 < u ∧ 0 < η ∧ 1 ≤ M ∧ A ≤ M ∧ u ≤ M ∧
      1 / (2 * r0) ≤ M ∧ 4 * r0 * ChartScales.Tg ≤ M ∧
      (∀ q ∈ K, ParameterBounds M q.1 (F0 q) (PhaseEstimates.shearVector F0 G0 q)) ∧
      ∃ N ≥ N0, (∀ n ≥ N, LargeBand h M u n ∧ Tmin ≤ ChartScales.S n) ∧
        ∀ L : ActiveLabel K, N ≤ L.val.1 → ∀ q ∈ K, q ∈ gridBox L.val.1 L.val.2 2 →
          ⟪T0 q, normalDirection (PhaseEstimates.shearVector F0 G0 (representative K L))⟫_ℝ ≤ -η ∧
          |c0 (F0 (representative K L)) (PhaseEstimates.shearVector F0 G0 (representative K L)) *
            ⟪T0 q, transverseDirection (PhaseEstimates.shearVector F0 G0 (representative K L))⟫_ℝ /
            ⟪T0 q, normalDirection (PhaseEstimates.shearVector F0 G0 (representative K L))⟫_ℝ| + η ≤
              slopeRatio u := by
  obtain ⟨u, η, hu, hη, N1, htarget⟩ := representative_target_margin hK hF hg hT hc ht
  obtain ⟨M, hM, hA, huM, hL, hslot, hp, N, hN, hlarge⟩ :=
    ordered_constants hK hF hg hR hc h r0 u A Tmin hh (max N0 N1)
  refine ⟨u, η, M, hu, hη, hM, hA, ?_, hL, hslot, hp, N,
    (le_max_left _ _).trans hN, hlarge, ?_⟩
  · simpa only [abs_of_pos hu] using huM
  · intro L hLN q hq hbox
    exact htarget L ((le_max_right _ _).trans (hN.trans hLN)) q hq hbox

/-- The actual selected mesh representatives and their derived compact
eigenpairs instantiate the analytic phase data.  In particular, neither
representative closeness nor eigenpair bounds are fields of the resulting
construction that the caller must postulate independently. -/
noncomputable def family {ι : Type*} (D : PhaseJetBounds.Domain ι Slow)
    {K : Set Slow} (label : ι → ActiveLabel K) (U : Set Slow)
    (F G : ι → Slow → ℝ) (F0 G0 : Slow → ℝ)
    (h r0 u M : ℝ) (sigma theta : ι → ℝ) (hM : 1 ≤ M)
    (hscale : ∀ i, D.scale i = ChartScales.S (label i).val.1)
    (hgrid : ∀ i, D.carrier i ⊆ gridBox (label i).val.1 (label i).val.2 2)
    (hinside : ∀ i, D.carrier i ⊆ U) (hKU : K ⊆ U)
    (hbase : ∀ i, PhaseEstimates.LocalBaseBounds (F i) (G i) F0 G0 U M
      (ChartScales.epsilon h (label i).val.1))
    (hF : PhaseJetBounds.PolynomialJets D F) (hG : PhaseJetBounds.PolynomialJets D G)
    (hradius : ∀ q ∈ U, 1 / M ≤ |q.1| ∧ |q.1| ≤ M)
    (hR : ∀ q ∈ K, 0 < q.1)
    (hc : ∀ q ∈ K, ReferenceCone (F0 q) (PhaseEstimates.shearVector F0 G0 q))
    (hp : ∀ q ∈ K, ParameterBounds M q.1 (F0 q) (PhaseEstimates.shearVector F0 G0 q))
    (hsigma : ∀ i, |sigma i| = 1) : FamilyData D h r0 u M := by
  have hq i := representative_mem K (label i)
  have hlow i := (hp _ (hq i)).positive_lower hM (hR _ (hq i)) (hc _ (hq i))
  refine {
    band := fun i => (label i).val.1
    scale_eq := hscale
    F := F
    G := G
    F0 := fun _ => F0
    G0 := fun _ => G0
    U := fun _ => U
    q0 := fun i => representative K (label i)
    K := fun i => transverseDirection (PhaseEstimates.shearVector F0 G0 (representative K (label
        i)))
    lam := fun i => lambda0 (F0 (representative K (label i)))
      (PhaseEstimates.shearVector F0 G0 (representative K (label i)))
    c0 := fun i => c0 (F0 (representative K (label i)))
      (PhaseEstimates.shearVector F0 G0 (representative K (label i)))
    sigma := sigma
    theta := theta
    base := hbase
    baseF := hF
    baseG := hG
    inside := hinside
    representative_inside := fun i => hKU (hq i)
    distance := ?_
    radius := fun i q hq => hradius q (hinside i hq)
    representative_radius := fun i => hradius _ (hKU (hq i))
    unit := fun i => transverseDirection_unit (hc _ (hq i)).shear_ne_zero
    orthogonal := fun _ => transverseDirection_inner_shear _
    frequency_bound := fun i => (hp _ (hq i)).frequency
    shear_bound := fun i => (hp _ (hq i)).shear
    shear_inv := fun i => by simpa only [one_div] using (hlow i).2.1
    lambda_bound := fun i => ⟨by simpa only [one_div] using (hlow i).2.2.1, (hp _ (hq i)).lambda⟩
    ratio_bound := fun i => ⟨by simpa only [one_div] using (hlow i).2.2.2, (hp _ (hq i)).ratio⟩
    eigen12 := ?_
    eigen21 := ?_
    sign := hsigma }
  · intro i q hqi
    simpa only [hscale i] using representative_enlarged_distance K (label i) (hgrid i hqi)
  · intro i
    simpa only [quarterTurn_transverseDirection] using (hc _ (hq i)).lambda0_div_c0
  · intro i
    simpa only [quarterTurn_transverseDirection, normal_inner_shear (hc _ (hq i)).shear_ne_zero]
      using (hc _ (hq i)).lambda0_mul_c0

end Representatives

end NavierStokes.BasePhaseGeometry
