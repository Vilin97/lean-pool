/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveOrderMoments
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowExpansionResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedRadialPrimitive
public import Mathlib.Analysis.Calculus.Deriv.Support

@[expose] public section

/-!
# Positive slow-order tangential stress support

The moments are actual positive-radius integrals. All radial and parameter
operators use the actual Frechet derivatives. Compact stress support is a
consequence of the repaired moments and the differential equations.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokes.SlowStressSupport

abbrev Field := ℝ × ℝ → ℝ
abbrev History := ℕ → Field
noncomputable def dr := ProfileHistories.radialPartial
noncomputable def de := ProfileHistories.parameterPartial
abbrev region (S : Set ℝ) := (univ : Set ℝ) ×ˢ S
abbrev Smooth (S : Set ℝ) (f : Field) := ContDiffOn ℝ ∞ f (region S)

noncomputable def exterior (B : ℝ) (S : Set ℝ) (f : Field) : Prop :=
  ∀ eta ∈ S, ∀ R, B ≤ R → f (R, eta) = 0

noncomputable def weighted (m : ℕ) (f : Field) (w : ℝ × ℝ) : ℝ := w.1 ^ m * f w

noncomputable def moment (B : ℝ) (m : ℕ) (f : Field) (eta : ℝ) : ℝ :=
  ∫ R in (0 : ℝ)..B, R ^ m * f (R, eta)

noncomputable def timeOp (h b : ℝ) (f : Field) (w : ℝ × ℝ) : ℝ :=
  (-b * f w + PositiveAxisSystem.dScale h * w.2 * de f w + w.1 / 2 * dr f w) /
    PositiveAxisSystem.ell h w.2

noncomputable def axialOp (h b : ℝ) (f : Field) (w : ℝ × ℝ) : ℝ :=
  (2 * w.2 * b * f w + PositiveAxisSystem.edge w.2 * de f w - w.2 * w.1 * dr f w) /
    PositiveAxisSystem.ell h w.2

noncomputable def axialOp2 (h b : ℝ) (f : Field) : Field :=
  axialOp h (b - PositiveAxisSystem.dScale h) (axialOp h b f)

theorem smooth_dr {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f) :
    Smooth S (dr f) :=
  ProfileHistories.radialPartial_smooth (PositiveOrderMoments.parameterDomain S hS) hf

theorem smooth_de {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f) :
    Smooth S (de f) :=
  ProfileHistories.parameterPartial_smooth (PositiveOrderMoments.parameterDomain S hS) hf

theorem smooth_weighted {S : Set ℝ} {f : Field} (hf : Smooth S f) (m : ℕ) :
    Smooth S (weighted m f) := (contDiffOn_fst.pow m).mul hf

theorem slice_smooth {S : Set ℝ} {f : Field} (hf : Smooth S f)
    {eta : ℝ} (heta : eta ∈ S) : ContDiff ℝ ∞ (fun R => f (R, eta)) := by
  apply contDiffOn_univ.mp
  exact hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ _ => ⟨mem_univ _, heta⟩)

theorem radial_hasDerivAt {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) : HasDerivAt (fun R => f (R, w.2)) (dr f w) w.1 :=
  ProfileHistories.radialPartial_hasDerivAt (PositiveOrderMoments.parameterDomain S hS)
    hf (p := w) ⟨mem_univ _, hw⟩

theorem parameter_hasDerivAt {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) : HasDerivAt (fun eta => f (w.1, eta)) (de f w) w.2 :=
  ProfileHistories.parameterPartial_hasDerivAt (PositiveOrderMoments.parameterDomain S hS)
    hf (p := w) ⟨mem_univ _, hw⟩

theorem dr_mul {S : Set ℝ} (hS : IsOpen S) {f g : Field}
    (hf : Smooth S f) (hg : Smooth S g) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    dr (fun p => f p * g p) w = dr f w * g w + f w * dr g w :=
  (radial_hasDerivAt hS (hf.mul hg) hw).unique
    ((radial_hasDerivAt hS hf hw).mul (radial_hasDerivAt hS hg hw))

theorem de_mul {S : Set ℝ} (hS : IsOpen S) {f g : Field}
    (hf : Smooth S f) (hg : Smooth S g) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    de (fun p => f p * g p) w = de f w * g w + f w * de g w :=
  (parameter_hasDerivAt hS (hf.mul hg) hw).unique
    ((parameter_hasDerivAt hS hf hw).mul (parameter_hasDerivAt hS hg hw))

theorem de_weighted {S : Set ℝ} (hS : IsOpen S) {f : Field}
    (hf : Smooth S f) (m : ℕ) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    de (weighted m f) w = w.1 ^ m * de f w :=
  (parameter_hasDerivAt hS (smooth_weighted hf m) hw).unique
    ((parameter_hasDerivAt hS hf hw).const_mul (w.1 ^ m))

theorem exterior_partial {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {B : ℝ} (hs : exterior B S f) (v : ℝ × ℝ) :
    exterior B S (fun w => fderiv ℝ f w v) := by
  intro eta heta R hR
  have hg : Smooth S (fun w => fderiv ℝ f w v) :=
    (hf.fderiv_of_isOpen (isOpen_univ.prod hS) (by simp)).clm_apply contDiffOn_const
  have hz : EqOn (fun r => fderiv ℝ f (r, eta) v) (fun _ => 0) (Ioi B) := by
    intro r hr
    have he : f =ᶠ[𝓝 (r, eta)] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_Ioi.prod hS).mem_nhds ⟨hr, heta⟩] with w hw
      exact hs w.2 hw.2 w.1 hw.1.le
    change fderiv ℝ f (r, eta) v = 0
    rw [he.fderiv_eq (𝕜 := ℝ)]
    simp
  have hc := hz.closure (slice_smooth hg heta).continuous continuous_const
  rw [closure_Ioi] at hc
  exact hc hR

theorem exterior_dr {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {B : ℝ} (hs : exterior B S f) : exterior B S (dr f) := exterior_partial hS hf hs (1, 0)

theorem exterior_de {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {B : ℝ} (hs : exterior B S f) : exterior B S (de f) := exterior_partial hS hf hs (0, 1)

theorem moment_eq_positive {S : Set ℝ} {f : Field} {B : ℝ} (hB : 0 ≤ B)
    (hs : exterior B S f) {eta : ℝ} (heta : eta ∈ S) (m : ℕ) :
    moment B m f eta = PositiveOrderMoments.positiveIntegral (fun R => R ^ m * f (R, eta)) := by
  symm
  exact PositiveOrderMoments.positiveIntegral_eq_primitive hB le_rfl
    (fun R hR => by rw [hs eta heta R hR, mul_zero])

theorem moment_hasDerivAt {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    HasDerivAt (moment B m f) (moment B m (de f) eta) eta := by
  let D := PositiveOrderMoments.parameterDomain S hS
  have hp := parameter_hasDerivAt hS
    (ProfileHistories.primitive_smooth D (smooth_weighted hf m))
    (w := (B, eta)) heta
  change HasDerivAt (fun z => ProfileHistories.primitive (weighted m f) (B, z))
    (ProfileHistories.parameterPartial (ProfileHistories.primitive (weighted m f)) (B, eta)) eta at
      hp
  rw [ProfileHistories.parameterPartial_primitive D (smooth_weighted hf m)
    (p := (B, eta)) ⟨mem_univ _, heta⟩] at hp
  have hi : ProfileHistories.primitive (de (weighted m f)) (B, eta) =
      moment B m (de f) eta := by
    apply intervalIntegral.integral_congr
    intro R hR
    exact de_weighted hS hf m (w := (R, eta)) heta
  change ProfileHistories.primitive (ProfileHistories.parameterPartial (weighted m f)) (B, eta) =
    moment B m (de f) eta at hi
  rw [hi] at hp
  exact hp

theorem moment_de_zero {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (B : ℝ) (m : ℕ) (hm : ∀ eta ∈ S, moment B m f eta = 0)
    {eta : ℝ} (heta : eta ∈ S) : moment B m (de f) eta = 0 := by
  have he : moment B m f =ᶠ[𝓝 eta] fun _ => (0 : ℝ) := by
    filter_upwards [hS.mem_nhds heta] with z hz using hm z hz
  exact (moment_hasDerivAt hS hf B m heta).unique
    ((hasDerivAt_const eta 0).congr_of_eventuallyEq he)

/-- Radial integration by parts includes the genuine boundary at the axis. -/
theorem moment_dr {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    moment B (m + 1) (dr f) eta = B ^ (m + 1) * f (B, eta) -
      ((m + 1 : ℕ) : ℝ) * moment B m f eta := by
  have hp : ∀ R : ℝ, HasDerivAt (fun r : ℝ => r ^ (m + 1))
      (((m + 1 : ℕ) : ℝ) * R ^ m) R := by
    intro R
    simpa using (hasDerivAt_id R).fun_pow (m + 1)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := B) (u := fun R : ℝ => R ^ (m + 1))
    (u' := fun R => ((m + 1 : ℕ) : ℝ) * R ^ m)
    (v := fun R => f (R, eta)) (v' := fun R => dr f (R, eta))
    (continuous_id.pow (m + 1)).continuousOn (slice_smooth hf heta).continuous.continuousOn
    (fun R _ => hp R) (fun R _ => radial_hasDerivAt hS hf (w := (R, eta)) heta)
    ((continuous_const.mul (continuous_id.pow m)).intervalIntegrable 0 B)
    ((slice_smooth (smooth_dr hS hf) heta).continuous.intervalIntegrable (μ := volume) 0 B)
  simpa only [moment, zero_pow (Nat.succ_ne_zero m), zero_mul, sub_zero,
    mul_assoc, intervalIntegral.integral_const_mul] using hi

theorem moment_add {S : Set ℝ} {f g : Field} (hf : Smooth S f) (hg : Smooth S g)
    (B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (fun w => f w + g w) eta = moment B m f eta + moment B m g eta := by
  simp only [moment, mul_add]
  exact intervalIntegral.integral_add
    ((slice_smooth (smooth_weighted hf m) heta).continuous.intervalIntegrable (μ := volume) 0 B)
    ((slice_smooth (smooth_weighted hg m) heta).continuous.intervalIntegrable (μ := volume) 0 B)

theorem moment_sub {S : Set ℝ} {f g : Field} (hf : Smooth S f) (hg : Smooth S g)
    (B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (fun w => f w - g w) eta = moment B m f eta - moment B m g eta := by
  simp only [moment, mul_sub]
  exact intervalIntegral.integral_sub
    ((slice_smooth (smooth_weighted hf m) heta).continuous.intervalIntegrable (μ := volume) 0 B)
    ((slice_smooth (smooth_weighted hg m) heta).continuous.intervalIntegrable (μ := volume) 0 B)

theorem smooth_axialOp {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) :
    Smooth S (axialOp h b f) := by
  have hl : Smooth S (fun w => PositiveAxisSystem.ell h w.2) :=
    contDiffOn_const.sub (contDiffOn_const.mul (contDiffOn_snd.pow 2))
  have he : Smooth S (fun w => PositiveAxisSystem.edge w.2) :=
    contDiffOn_const.sub (contDiffOn_snd.pow 2)
  exact (((((contDiffOn_const.mul contDiffOn_snd).mul contDiffOn_const).mul hf).add
    (he.mul (smooth_de hS hf))).sub ((contDiffOn_snd.mul contDiffOn_fst).mul (smooth_dr hS hf))).div
      hl (fun w hw => hell w.2 hw.2)

theorem exterior_axialOp {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {B : ℝ} (hs : exterior B S f) (h b : ℝ) : exterior B S (axialOp h b f) := by
  intro eta heta R hR
  simp [axialOp, hs eta heta R hR, exterior_dr hS hf hs eta heta R hR,
    exterior_de hS hf hs eta heta R hR]

theorem axialOp_mul {S : Set ℝ} (hS : IsOpen S) {f g : Field}
    (hf : Smooth S f) (hg : Smooth S g) (h b c : ℝ)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    axialOp h (b + c) (fun p => f p * g p) w =
      axialOp h b f w * g w + f w * axialOp h c g w := by
  simp only [axialOp, de_mul hS hf hg hw, dr_mul hS hf hg hw]
  ring

/-- The weighted axial derivative is the actual derivative of the weighted
moment, with its exact scaling coefficient and radial boundary term. -/
theorem moment_axialOp {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (axialOp h b f) eta =
      (2 * eta * b * moment B m f eta + PositiveAxisSystem.edge eta * moment B m (de f) eta -
        eta * (B ^ (m + 1) * f (B, eta) - ((m + 1 : ℕ) : ℝ) * moment B m f eta)) /
        PositiveAxisSystem.ell h eta := by
  have h0 := ((slice_smooth (smooth_weighted hf m) heta).continuous.intervalIntegrable (μ :=
    volume) 0 B)
  have h1 := ((slice_smooth (smooth_weighted (smooth_de hS hf) m)
    heta).continuous.intervalIntegrable (μ := volume) 0 B)
  have h2 := ((slice_smooth (smooth_weighted (smooth_dr hS hf) (m + 1))
    heta).continuous.intervalIntegrable (μ := volume) 0 B)
  dsimp only [weighted] at h0 h1 h2
  have he : (fun R => R ^ m * axialOp h b f (R, eta)) =
      (fun R => (2 * eta * b * (R ^ m * f (R, eta)) +
        PositiveAxisSystem.edge eta * (R ^ m * de f (R, eta)) -
        eta * (R ^ (m + 1) * dr f (R, eta))) / PositiveAxisSystem.ell h eta) := by
    funext R
    simp only [axialOp, pow_succ]
    ring
  unfold moment
  rw [he, intervalIntegral.integral_div,
    intervalIntegral.integral_sub ((h0.const_mul _).add (h1.const_mul _)) (h2.const_mul _),
    intervalIntegral.integral_add (h0.const_mul _) (h1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  change (_ + _ - eta * moment B (m + 1) (dr f) eta) / _ = _
  rw [moment_dr hS hf B m heta]
  rfl

theorem moment_timeOp {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (timeOp h b f) eta =
      (-b * moment B m f eta + PositiveAxisSystem.dScale h * eta * moment B m (de f) eta +
        (B ^ (m + 1) * f (B, eta) - ((m + 1 : ℕ) : ℝ) * moment B m f eta) / 2) /
        PositiveAxisSystem.ell h eta := by
  have h0 := ((slice_smooth (smooth_weighted hf m) heta).continuous.intervalIntegrable (μ :=
    volume) 0 B)
  have h1 := ((slice_smooth (smooth_weighted (smooth_de hS hf) m)
    heta).continuous.intervalIntegrable (μ := volume) 0 B)
  have h2 := ((slice_smooth (smooth_weighted (smooth_dr hS hf) (m + 1))
    heta).continuous.intervalIntegrable (μ := volume) 0 B)
  dsimp only [weighted] at h0 h1 h2
  have he : (fun R => R ^ m * timeOp h b f (R, eta)) =
      (fun R => (-b * (R ^ m * f (R, eta)) +
        PositiveAxisSystem.dScale h * eta * (R ^ m * de f (R, eta)) +
        (1 / 2 : ℝ) * (R ^ (m + 1) * dr f (R, eta))) / PositiveAxisSystem.ell h eta) := by
    funext R
    simp only [timeOp, pow_succ]
    ring
  unfold moment
  rw [he, intervalIntegral.integral_div,
    intervalIntegral.integral_add ((h0.const_mul _).add (h1.const_mul _)) (h2.const_mul _),
    intervalIntegral.integral_add (h0.const_mul _) (h1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  change (_ + _ + (1 / 2 : ℝ) * moment B (m + 1) (dr f) eta) / _ = _
  rw [moment_dr hS hf B m heta]
  unfold moment
  ring

theorem moment_axialOp_zero {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b B : ℝ) (m : ℕ) (hb : ∀ eta ∈ S, f (B, eta) = 0)
    (hm : ∀ eta ∈ S, moment B m f eta = 0) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (axialOp h b f) eta = 0 := by
  rw [moment_axialOp hS hf h b B m heta, hb eta heta, hm eta heta,
    moment_de_zero hS hf B m hm heta]
  ring

theorem moment_timeOp_zero {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b B : ℝ) (m : ℕ) (hb : ∀ eta ∈ S, f (B, eta) = 0)
    (hm : ∀ eta ∈ S, moment B m f eta = 0) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (timeOp h b f) eta = 0 := by
  rw [moment_timeOp hS hf h b B m heta, hb eta heta, hm eta heta,
    moment_de_zero hS hf B m hm heta]
  ring

theorem moment_axialOp2_zero {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b B : ℝ) (m : ℕ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hs : exterior B S f) (hm : ∀ eta ∈ S, moment B m f eta = 0)
    {eta : ℝ} (heta : eta ∈ S) : moment B m (axialOp2 h b f) eta = 0 := by
  exact moment_axialOp_zero hS (smooth_axialOp hS hf h b hell)
    h (b - PositiveAxisSystem.dScale h) B m
    (fun z hz => exterior_axialOp hS hf hs h b z hz B le_rfl)
    (fun z hz => moment_axialOp_zero hS hf h b B m
      (fun z hz => hs z hz B le_rfl) hm hz) heta

noncomputable def orderExponent (h : ℝ) (n : ℕ) : ℝ :=
  -PositiveAxisSystem.a h + SlowExpansionResidual.slowOrder h n

noncomputable def pressureExponent (h : ℝ) (n : ℕ) : ℝ :=
  -2 * PositiveAxisSystem.a h + SlowExpansionResidual.slowOrder h n

theorem orderExponent_pair (h : ℝ) {i j n : ℕ} (hij : i + j = n) :
    orderExponent h i + orderExponent h j = pressureExponent h n := by
  unfold orderExponent pressureExponent
  rw [← hij, SlowExpansionResidual.slowOrder_add]
  ring

/-- At a fixed convolution order the physical power is independent of the split. -/
theorem physical_product_power {q : ℝ} (hq : 0 < q) (h b c : ℝ)
    {i j n : ℕ} (hij : i + j = n) :
    q ^ (b + SlowExpansionResidual.slowOrder h i) * q ^ (c + SlowExpansionResidual.slowOrder h j) =
      q ^ (b + c + SlowExpansionResidual.slowOrder h n) := by
  rw [SlowExpansionResidual.rpow_product_order hq, hij]

noncomputable def conv (n : ℕ) (u v : History) (w : ℝ × ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), u i w * v (n - i) w

theorem conv_eq_actual (n : ℕ) (u v : History) (w : ℝ × ℝ) :
    conv n u v w = PositiveOrderMoments.cauchy n (PositiveOrderMoments.slice u w.2)
      (PositiveOrderMoments.slice v w.2) w.1 := rfl

theorem conv_eq_antidiagonal (n : ℕ) (u v : History) (w : ℝ × ℝ) :
    conv n u v w = SlowExpansionResidual.convolution (fun i j => u i w * v j w) n := by
  symm
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => u i w * v j w) n

theorem smooth_conv {S : Set ℝ} {n : ℕ} {u v : History}
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hv : ∀ j, j ≤ n → Smooth S (v j)) :
    Smooth S (conv n u v) := by
  apply ContDiffOn.sum
  intro j hj
  exact (hu j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).mul (hv (n - j) (Nat.sub_le _ _))

theorem dr_conv {S : Set ℝ} (hS : IsOpen S) {n : ℕ} {u v : History}
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hv : ∀ j, j ≤ n → Smooth S (v j))
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    dr (conv n u v) w = ∑ j ∈ Finset.range (n + 1),
      (dr (u j) w * v (n - j) w + u j w * dr (v (n - j)) w) := by
  apply (radial_hasDerivAt hS (smooth_conv hu hv) hw).unique
  apply HasDerivAt.fun_sum
  intro j hj
  exact (radial_hasDerivAt hS (hu j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) hw).mul
    (radial_hasDerivAt hS (hv (n - j) (Nat.sub_le _ _)) hw)

theorem de_conv {S : Set ℝ} (hS : IsOpen S) {n : ℕ} {u v : History}
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hv : ∀ j, j ≤ n → Smooth S (v j))
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    de (conv n u v) w = ∑ j ∈ Finset.range (n + 1),
      (de (u j) w * v (n - j) w + u j w * de (v (n - j)) w) := by
  apply (parameter_hasDerivAt hS (smooth_conv hu hv) hw).unique
  apply HasDerivAt.fun_sum
  intro j hj
  exact (parameter_hasDerivAt hS (hu j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) hw).mul
    (parameter_hasDerivAt hS (hv (n - j) (Nat.sub_le _ _)) hw)

theorem axialOp_conv {S : Set ℝ} (hS : IsOpen S) {n : ℕ} {u v : History}
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hv : ∀ j, j ≤ n → Smooth S (v j))
    (h : ℝ) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    axialOp h (pressureExponent h n) (conv n u v) w =
      ∑ j ∈ Finset.range (n + 1),
        (axialOp h (orderExponent h j) (u j) w * v (n - j) w +
          u j w * axialOp h (orderExponent h (n - j)) (v (n - j)) w) := by
  unfold axialOp
  rw [de_conv hS hu hv hw, dr_conv hS hu hv hw]
  unfold conv
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have he := orderExponent_pair h (i := j) (j := n - j) (n := n)
    (Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  rw [← he]
  ring

theorem dr_weighted {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (m : ℕ) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    dr (weighted m f) w = (m : ℝ) * w.1 ^ (m - 1) * f w + w.1 ^ m * dr f w := by
  simpa only [id_eq, mul_one, Prod.eta] using
    (radial_hasDerivAt hS (smooth_weighted hf m) hw).unique
      (((hasDerivAt_id w.1).fun_pow m).fun_mul (radial_hasDerivAt hS hf hw))

theorem dr_sub {S : Set ℝ} (hS : IsOpen S) {f g : Field}
    (hf : Smooth S f) (hg : Smooth S g) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    dr (fun p => f p - g p) w = dr f w - dr g w :=
  (radial_hasDerivAt hS (hf.sub hg) hw).unique
    ((radial_hasDerivAt hS hf hw).sub (radial_hasDerivAt hS hg hw))

theorem axialOp_add {S : Set ℝ} (hS : IsOpen S) {f g : Field}
    (hf : Smooth S f) (hg : Smooth S g) (h b : ℝ)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    axialOp h b (fun p => f p + g p) w = axialOp h b f w + axialOp h b g w := by
  have hr := (radial_hasDerivAt hS (hf.add hg) hw).unique
    ((radial_hasDerivAt hS hf hw).add (radial_hasDerivAt hS hg hw))
  have he := (parameter_hasDerivAt hS (hf.add hg) hw).unique
    ((parameter_hasDerivAt hS hf hw).add (parameter_hasDerivAt hS hg hw))
  simp only [axialOp, hr, he]
  ring

noncomputable def angularViscousFlux (e : Field) (w : ℝ × ℝ) : ℝ :=
  w.1 ^ 2 * dr e w - w.1 * e w

noncomputable def axialViscousFlux (u : Field) (w : ℝ × ℝ) : ℝ := w.1 * dr u w

theorem dr_angularViscousFlux {S : Set ℝ} (hS : IsOpen S) {e : Field} (he : Smooth S e)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    dr (angularViscousFlux e) w = w.1 ^ 2 * dr (dr e) w + w.1 * dr e w - e w := by
  have hfun : angularViscousFlux e = fun p => weighted 2 (dr e) p - weighted 1 e p := by
    funext p
    simp [angularViscousFlux, weighted]
  rw [hfun]
  rw [dr_sub hS (smooth_weighted (smooth_dr hS he) 2) (smooth_weighted he 1) hw,
    dr_weighted hS (smooth_dr hS he) 2 hw, dr_weighted hS he 1 hw]
  norm_num
  ring

theorem dr_axialViscousFlux {S : Set ℝ} (hS : IsOpen S) {u : Field} (hu : Smooth S u)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    dr (axialViscousFlux u) w = w.1 * dr (dr u) w + dr u w := by
  have hfun : axialViscousFlux u = weighted 1 (dr u) := by
    funext p
    simp [axialViscousFlux, weighted]
  rw [hfun]
  rw [dr_weighted hS (smooth_dr hS hu) 1 hw]
  norm_num
  ring

noncomputable def angularWeighted (h : ℝ) (n : ℕ) (v u e : History) (w : ℝ × ℝ) : ℝ :=
  w.1 ^ 2 * timeOp h (orderExponent h n) (e n) w +
    (∑ j ∈ Finset.range (n + 1),
      (w.1 * v j w * dr (e (n - j)) w + v j w * e (n - j) w +
        w.1 ^ 2 * u j w * axialOp h (orderExponent h (n - j)) (e (n - j)) w)) -
    (w.1 ^ 2 * dr (dr (e n)) w + w.1 * dr (e n) w - e n w) -
    w.1 ^ 2 * axialOp2 h (orderExponent h (n - 1)) (e (n - 1)) w

noncomputable def axialWeighted (h : ℝ) (n : ℕ) (v u : History) (p : Field) (w : ℝ × ℝ) : ℝ :=
  w.1 * timeOp h (orderExponent h n) (u n) w +
    (∑ j ∈ Finset.range (n + 1),
      (v j w * dr (u (n - j)) w +
        w.1 * u j w * axialOp h (orderExponent h (n - j)) (u (n - j)) w)) +
    w.1 * axialOp h (pressureExponent h n) p w -
    (w.1 * dr (dr (u n)) w + dr (u n) w) -
    w.1 * axialOp2 h (orderExponent h (n - 1)) (u (n - 1)) w

noncomputable def angularDensity (h : ℝ) (n : ℕ) (v u e : History) (w : ℝ × ℝ) : ℝ :=
  w.1 ^ 2 * timeOp h (orderExponent h n) (e n) w +
    dr (weighted 1 (conv n v e)) w +
    w.1 ^ 2 * axialOp h (pressureExponent h n) (conv n u e) w -
    dr (angularViscousFlux (e n)) w -
    w.1 ^ 2 * axialOp2 h (orderExponent h (n - 1)) (e (n - 1)) w

noncomputable def axialDensity (h : ℝ) (n : ℕ) (v u : History) (p : Field) (w : ℝ × ℝ) : ℝ :=
  w.1 * timeOp h (orderExponent h n) (u n) w + dr (conv n v u) w +
    w.1 * axialOp h (pressureExponent h n) (fun p' => conv n u u p' + p p') w -
    dr (axialViscousFlux (u n)) w -
    w.1 * axialOp2 h (orderExponent h (n - 1)) (u (n - 1)) w

/-- Incompressibility converts the actual angular advection terms to
conservative form; the convolution exponents are checked, not assumed. -/
theorem angularWeighted_eq_density {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u e : History} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (he : ∀ j, j ≤ n → Smooth S (e j))
    (h : ℝ) {w : ℝ × ℝ} (hw : w.2 ∈ S)
    (hdiv : ∀ j, j ≤ n → dr (v j) w = -w.1 * axialOp h (orderExponent h j) (u j) w) :
    angularWeighted h n v u e w = angularDensity h n v u e w := by
  unfold angularDensity angularWeighted
  rw [dr_weighted hS (smooth_conv hv he) 1 hw, dr_conv hS hv he hw,
    axialOp_conv hS hu he h hw, dr_angularViscousFlux hS (he n le_rfl) hw]
  norm_num only [Nat.cast_one, pow_zero, pow_one, one_mul, Nat.sub_self]
  unfold conv
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 2
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hdiv j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  ring

theorem axialWeighted_eq_density {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h : ℝ) {w : ℝ × ℝ} (hw : w.2 ∈ S)
    (hdiv : ∀ j, j ≤ n → dr (v j) w = -w.1 * axialOp h (orderExponent h j) (u j) w) :
    axialWeighted h n v u p w = axialDensity h n v u p w := by
  unfold axialDensity axialWeighted
  rw [dr_conv hS hv hu hw, axialOp_add hS (smooth_conv hu hu) hp h _ hw,
    axialOp_conv hS hu hu h hw, dr_axialViscousFlux hS (hu n le_rfl) hw]
  have hs : (∑ j ∈ Finset.range (n + 1),
      (v j w * dr (u (n - j)) w + w.1 * u j w * axialOp h (orderExponent h (n - j)) (u (n - j)) w))
        =
      (∑ j ∈ Finset.range (n + 1), (dr (v j) w * u (n - j) w + v j w * dr (u (n - j)) w)) +
      w.1 * ∑ j ∈ Finset.range (n + 1),
        (axialOp h (orderExponent h j) (u j) w * u (n - j) w +
          u j w * axialOp h (orderExponent h (n - j)) (u (n - j)) w) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hdiv j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    ring
  rw [hs]
  ring

theorem smooth_timeOp {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) : Smooth S (timeOp h b f) := by
  have hl : Smooth S (fun w => PositiveAxisSystem.ell h w.2) :=
    contDiffOn_const.sub (contDiffOn_const.mul (contDiffOn_snd.pow 2))
  exact (((contDiffOn_const.mul hf).add
    ((contDiffOn_const.mul contDiffOn_snd).mul (smooth_de hS hf))).add
      ((contDiffOn_fst.div_const 2).mul (smooth_dr hS hf))).div hl
      (fun w hw => hell w.2 hw.2)

theorem smooth_axialOp2 {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) : Smooth S (axialOp2 h b f) :=
  smooth_axialOp hS (smooth_axialOp hS hf h b hell) h _ hell

theorem smooth_angularViscousFlux {S : Set ℝ} (hS : IsOpen S) {e : Field} (he : Smooth S e) :
    Smooth S (angularViscousFlux e) :=
  ((contDiffOn_fst.pow 2).mul (smooth_dr hS he)).sub (contDiffOn_fst.mul he)

theorem smooth_axialViscousFlux {S : Set ℝ} (hS : IsOpen S) {u : Field} (hu : Smooth S u) :
    Smooth S (axialViscousFlux u) := contDiffOn_fst.mul (smooth_dr hS hu)

theorem moment_weighted_zero (B : ℝ) (m : ℕ) (f : Field) (eta : ℝ) :
    moment B 0 (weighted m f) eta = moment B m f eta := by simp [moment, weighted]

theorem moment_dr_boundary {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (B : ℝ) {eta : ℝ} (heta : eta ∈ S) :
    moment B 0 (dr f) eta = f (B, eta) - f (0, eta) := by
  simp only [moment, pow_zero, one_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun R => f (R, eta))
    (fun R _ => radial_hasDerivAt hS hf (w := (R, eta)) heta)
    ((slice_smooth (smooth_dr hS hf) heta).continuous.intervalIntegrable 0 B)

theorem moment_five {S : Set ℝ} {f g k l p : Field}
    (hf : Smooth S f) (hg : Smooth S g) (hk : Smooth S k) (hl : Smooth S l) (hp : Smooth S p)
    (B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (fun w => f w + g w + k w - l w - p w) eta =
      moment B m f eta + moment B m g eta + moment B m k eta - moment B m l eta - moment B m p eta
        := by
  rw [moment_sub (((hf.add hg).add hk).sub hl) hp B m heta,
    moment_sub ((hf.add hg).add hk) hl B m heta,
    moment_add (hf.add hg) hk B m heta, moment_add hf hg B m heta]

theorem exterior_conv_left {S : Set ℝ} {B : ℝ} {n : ℕ} {u v : History}
    (hu : ∀ j, j ≤ n → exterior B S (u j)) : exterior B S (conv n u v) := by
  intro eta heta R hR
  unfold conv
  apply Finset.sum_eq_zero
  intro j hj
  rw [hu j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) eta heta R hR, zero_mul]

/-- The integrated angular equation, with the previous axial-viscosity term
still displayed. The other four terms cancel by the repaired moments and
the actual radial boundary terms. -/
theorem angular_integral_balance {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u e : History} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (he : ∀ j, j ≤ n → Smooth S (e j))
    (h B : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hev : exterior B S (e n)) (hvv : ∀ j, j ≤ n → exterior B S (v j))
    (hem : ∀ eta ∈ S, moment B 2 (e n) eta = 0)
    (hum : ∀ eta ∈ S, moment B 2 (conv n u e) eta = 0)
    (hug : exterior B S (conv n u e)) {eta : ℝ} (heta : eta ∈ S) :
    moment B 0 (angularDensity h n v u e) eta =
      -moment B 2 (axialOp2 h (orderExponent h (n - 1)) (e (n - 1))) eta := by
  have ht := smooth_weighted (smooth_timeOp hS (he n le_rfl) h (orderExponent h n) hell) 2
  have hr := smooth_weighted (smooth_conv hv he) 1
  have hz := smooth_weighted (smooth_axialOp hS (smooth_conv hu he) h (pressureExponent h n) hell) 2
  have hk := smooth_angularViscousFlux hS (he n le_rfl)
  have hp := smooth_weighted (smooth_axialOp2 hS (he (n - 1) (Nat.sub_le _ _)) h
    (orderExponent h (n - 1)) hell) 2
  have hd : angularDensity h n v u e = fun w =>
      weighted 2 (timeOp h (orderExponent h n) (e n)) w +
      dr (weighted 1 (conv n v e)) w +
      weighted 2 (axialOp h (pressureExponent h n) (conv n u e)) w -
      dr (angularViscousFlux (e n)) w -
      weighted 2 (axialOp2 h (orderExponent h (n - 1)) (e (n - 1))) w := by
    funext w
    rfl
  rw [hd, moment_five ht (smooth_dr hS hr) hz (smooth_dr hS hk) hp B 0 heta,
    moment_weighted_zero, moment_weighted_zero, moment_weighted_zero,
    moment_dr_boundary hS hr B heta, moment_dr_boundary hS hk B heta,
    moment_timeOp_zero hS (he n le_rfl) h _ B 2 (fun z hz => hev z hz B le_rfl) hem heta,
    moment_axialOp_zero hS (smooth_conv hu he) h _ B 2
      (fun z hz => hug z hz B le_rfl) hum heta]
  simp [weighted, angularViscousFlux, exterior_conv_left hvv eta heta B le_rfl,
    hev eta heta B le_rfl, exterior_dr hS (he n le_rfl) hev eta heta B le_rfl]

theorem axial_integral_balance {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h B : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (huv : exterior B S (u n)) (hvv : ∀ j, j ≤ n → exterior B S (v j))
    (haxis : ∀ eta ∈ S, conv n v u (0, eta) = 0)
    (hum : ∀ eta ∈ S, moment B 1 (u n) eta = 0)
    (hflux : ∀ eta ∈ S, moment B 1 (fun w => conv n u u w + p w) eta = 0)
    (hfluxB : ∀ eta ∈ S, conv n u u (B, eta) + p (B, eta) = 0)
    {eta : ℝ} (heta : eta ∈ S) :
    moment B 0 (axialDensity h n v u p) eta =
      -moment B 1 (axialOp2 h (orderExponent h (n - 1)) (u (n - 1))) eta := by
  have ht := smooth_weighted (smooth_timeOp hS (hu n le_rfl) h (orderExponent h n) hell) 1
  have hr := smooth_conv hv hu
  have hz := smooth_weighted (smooth_axialOp hS ((smooth_conv hu hu).add hp) h (pressureExponent h
    n) hell) 1
  have hk := smooth_axialViscousFlux hS (hu n le_rfl)
  have hl := smooth_weighted (smooth_axialOp2 hS (hu (n - 1) (Nat.sub_le _ _)) h
    (orderExponent h (n - 1)) hell) 1
  have hd : axialDensity h n v u p = fun w =>
      weighted 1 (timeOp h (orderExponent h n) (u n)) w + dr (conv n v u) w +
      weighted 1 (axialOp h (pressureExponent h n) (fun w => conv n u u w + p w)) w -
      dr (axialViscousFlux (u n)) w -
      weighted 1 (axialOp2 h (orderExponent h (n - 1)) (u (n - 1))) w := by
    funext w
    simp [axialDensity, weighted]
  rw [hd, moment_five ht (smooth_dr hS hr) hz (smooth_dr hS hk) hl B 0 heta,
    moment_weighted_zero, moment_weighted_zero, moment_weighted_zero,
    moment_dr_boundary hS hr B heta, moment_dr_boundary hS hk B heta,
    moment_timeOp_zero hS (hu n le_rfl) h _ B 1 (fun z hz => huv z hz B le_rfl) hum heta,
    moment_axialOp_zero hS ((smooth_conv hu hu).add hp) h _ B 1 hfluxB hflux heta]
  simp [axialViscousFlux, exterior_conv_left hvv eta heta B le_rfl,
    haxis eta heta, exterior_dr hS (hu n le_rfl) huv eta heta B le_rfl]

/-- Pressure integration by parts turns the fifth repaired row into the
zero total axial momentum flux. The pressure derivative is an actual one. -/
theorem axial_flux_moment_from_fifth {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {u : History} {p : Field} (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (B : ℝ) (hpB : ∀ eta ∈ S, p (B, eta) = 0)
    (hrow : ∀ eta ∈ S, moment B 1 (conv n u u) eta - (1 / 2 : ℝ) * moment B 2 (dr p) eta = 0)
    {eta : ℝ} (heta : eta ∈ S) :
    moment B 1 (fun w => conv n u u w + p w) eta = 0 := by
  have hibp := moment_dr hS hp B 1 heta
  rw [hpB eta heta] at hibp
  norm_num at hibp
  rw [moment_add (smooth_conv hu hu) hp B 1 heta]
  linarith [hrow eta heta]

theorem actual_row_integral_zero {n : ℕ} {u e : History} {omega : Field}
    {S : Set ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ eta ∈ S, ∀ R, B ≤ R → PositiveOrderMoments.jointRowDensity n u e omega (R, eta) = 0)
    (hm : ∀ eta ∈ S, PositiveOrderMoments.moments n (PositiveOrderMoments.slice u eta)
      (PositiveOrderMoments.slice e eta) (fun R => omega (R, eta)) = 0)
    {eta : ℝ} (heta : eta ∈ S) (i : Fin 5) :
    (∫ R in (0 : ℝ)..B, PositiveOrderMoments.jointRowDensity n u e omega (R, eta) i) = 0 := by
  rw [← PositiveOrderMoments.positiveIntegral_eq_primitive hB le_rfl
    (fun R hR => congrFun (hs eta heta R hR) i)]
  exact congrFun (hm eta heta) i

/-- All moment hypotheses used in the integrated balances follow from the
five repaired rows. Pressure is the actual forward primitive of its source. -/
theorem repaired_moment_data {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {u e : History} {omega : Field} (hu : ∀ j, j ≤ n → Smooth S (u j))
    (hq : Smooth S (PositiveOrderMoments.jointPressureGradient n e omega))
    {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ eta ∈ S, ∀ R, B ≤ R → PositiveOrderMoments.jointRowDensity n u e omega (R, eta) = 0)
    (hm : ∀ eta ∈ S, PositiveOrderMoments.moments n (PositiveOrderMoments.slice u eta)
      (PositiveOrderMoments.slice e eta) (fun R => omega (R, eta)) = 0)
    {eta : ℝ} (heta : eta ∈ S) :
    moment B 1 (u n) eta = 0 ∧ moment B 2 (e n) eta = 0 ∧
      moment B 2 (conv n u e) eta = 0 ∧
      moment B 1 (fun w => conv n u u w + PositiveOrderMoments.pressureHistory n e omega w) eta = 0
        := by
  have hP := PositiveOrderMoments.pressureHistory_contDiffOn hS hq
  have hdP : ∀ w : ℝ × ℝ, w.2 ∈ S →
      dr (PositiveOrderMoments.pressureHistory n e omega) w =
        PositiveOrderMoments.jointPressureGradient n e omega w := by
    intro w hw
    exact ProfileHistories.radialPartial_primitive (PositiveOrderMoments.parameterDomain S hS)
      hq (p := w) ⟨mem_univ _, hw⟩
  have hPB : ∀ z ∈ S, PositiveOrderMoments.pressureHistory n e omega (B, z) = 0 := by
    intro z hz
    exact PositiveOrderMoments.pressureHistory_exterior_on hB
      (fun z hz R hR => congrFun (hs z hz R hR) 2) hm le_rfl hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := actual_row_integral_zero hB hs hm heta 0
    change (∫ R in (0 : ℝ)..B, R * u n (R, eta)) = 0 at hh
    simpa [moment] using hh
  · exact actual_row_integral_zero hB hs hm heta 1
  · exact actual_row_integral_zero hB hs hm heta 3
  · apply axial_flux_moment_from_fifth hS hu hP B hPB _ heta
    intro z hz
    have hh := actual_row_integral_zero hB hs hm hz 4
    have hfun : (fun R => PositiveOrderMoments.jointRowDensity n u e omega (R, z) 4) =
        (fun R => R * conv n u u (R, z) - (1 / 2 : ℝ) *
          (R ^ 2 * dr (PositiveOrderMoments.pressureHistory n e omega) (R, z))) := by
      funext R
      rw [hdP (R, z) hz]
      change R * conv n u u (R, z) - R ^ 2 / 2 *
        PositiveOrderMoments.jointPressureGradient n e omega (R, z) = _
      ring
    have hi0 := (slice_smooth (smooth_weighted (smooth_conv hu hu) 1)
      hz).continuous.intervalIntegrable
      (μ := volume) 0 B
    have hi1 := (slice_smooth (smooth_weighted (smooth_dr hS hP) 2)
      hz).continuous.intervalIntegrable
      (μ := volume) 0 B
    simp only [weighted, pow_one] at hi0 hi1
    rw [hfun, intervalIntegral.integral_sub hi0 (hi1.const_mul (1 / 2)),
      intervalIntegral.integral_const_mul] at hh
    simpa only [moment, pow_one] using hh

theorem angular_integral_zero {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u e : History} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (he : ∀ j, j ≤ n → Smooth S (e j))
    (h B : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hev : exterior B S (e n)) (hvv : ∀ j, j ≤ n → exterior B S (v j))
    (hem : ∀ eta ∈ S, moment B 2 (e n) eta = 0)
    (hum : ∀ eta ∈ S, moment B 2 (conv n u e) eta = 0)
    (hug : exterior B S (conv n u e))
    (heprev : exterior B S (e (n - 1)))
    (hmprev : ∀ eta ∈ S, moment B 2 (e (n - 1)) eta = 0)
    {eta : ℝ} (heta : eta ∈ S) : moment B 0 (angularDensity h n v u e) eta = 0 := by
  rw [angular_integral_balance hS hv hu he h B hell hev hvv hem hum hug heta,
    moment_axialOp2_zero hS (he (n - 1) (Nat.sub_le _ _)) h _ B 2 hell heprev hmprev heta,
    neg_zero]

theorem axial_integral_zero {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h B : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (huv : exterior B S (u n)) (hvv : ∀ j, j ≤ n → exterior B S (v j))
    (haxis : ∀ eta ∈ S, conv n v u (0, eta) = 0)
    (hum : ∀ eta ∈ S, moment B 1 (u n) eta = 0)
    (hflux : ∀ eta ∈ S, moment B 1 (fun w => conv n u u w + p w) eta = 0)
    (hfluxB : ∀ eta ∈ S, conv n u u (B, eta) + p (B, eta) = 0)
    (huprev : exterior B S (u (n - 1)))
    (hmprev : ∀ eta ∈ S, moment B 1 (u (n - 1)) eta = 0)
    {eta : ℝ} (heta : eta ∈ S) : moment B 0 (axialDensity h n v u p) eta = 0 := by
  rw [axial_integral_balance hS hv hu hp h B hell huv hvv haxis hum hflux hfluxB heta,
    moment_axialOp2_zero hS (hu (n - 1) (Nat.sub_le _ _)) h _ B 1 hell huprev hmprev heta,
    neg_zero]

/-- The negative weighted radial primitive. The definition is zero on
nonpositive radii; vanishing of the source near the axis makes this smooth. -/
noncomputable def stress (m : ℕ) (F : Field) (w : ℝ × ℝ) : ℝ :=
  if 0 < w.1 then -ProfileHistories.primitive F w / w.1 ^ m else 0

theorem stress_of_pos (m : ℕ) (F : Field) {w : ℝ × ℝ} (hw : 0 < w.1) :
    stress m F w = -ProfileHistories.primitive F w / w.1 ^ m := ite_eq_left hw

theorem stress_inner (m : ℕ) {F : Field} {S : Set ℝ} {a : ℝ}
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, F (R, eta) = 0)
    {R eta : ℝ} (hR : R ≤ a) (heta : eta ∈ S) : stress m F (R, eta) = 0 := by
  by_cases hp : 0 < R
  · rw [stress_of_pos m F hp]
    have hi : ProfileHistories.primitive F (R, eta) = 0 := by
      change (∫ r in (0 : ℝ)..R, F (r, eta)) = 0
      have heq : EqOn (fun r => F (r, eta)) (fun _ => (0 : ℝ)) (uIcc 0 R) := by
        intro r hr
        rw [uIcc_of_le hp.le] at hr
        exact hinner eta heta r ⟨hr.1, hr.2.trans hR⟩
      rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]
    simp [hi]
  · simp [stress, hp]

theorem stress_exterior (m : ℕ) {F : Field} {S : Set ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hs : exterior B S F) (hm : ∀ eta ∈ S, moment B 0 F eta = 0)
    {R eta : ℝ} (hR : B ≤ R) (heta : eta ∈ S) : stress m F (R, eta) = 0 := by
  by_cases hp : 0 < R
  · rw [stress_of_pos m F hp]
    have hi : ProfileHistories.primitive F (R, eta) = 0 := by
      change (∫ r in (0 : ℝ)..R, F (r, eta)) = 0
      rw [← PositiveOrderMoments.positiveIntegral_eq_primitive hB hR (hs eta heta)]
      have hh := moment_eq_positive hB hs heta 0
      simpa only [pow_zero, one_mul, hm eta heta] using hh.symm
    simp [hi]
  · simp [stress, hp]

theorem stress_smooth {S : Set ℝ} (hS : IsOpen S) {F : Field} (hF : Smooth S F)
    (m : ℕ) {a : ℝ} (ha : 0 < a)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, F (R, eta) = 0) : Smooth S (stress m F) := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  by_cases hR : 0 < w.1
  · have hP := (ProfileHistories.primitive_smooth
      (PositiveOrderMoments.parameterDomain S hS) hF).contDiffAt
        ((isOpen_univ.prod hS).mem_nhds hw)
    have ht : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => -ProfileHistories.primitive F p / p.1 ^ m) w :=
      hP.neg.div (contDiffAt_fst.pow m) (pow_ne_zero m hR.ne')
    apply ht.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt (Ioi_mem_nhds hR)] with p hp
    exact stress_of_pos m F hp
  · have hRa : w.1 < a := (le_of_not_gt hR).trans_lt ha
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isOpen_Iio.prod hS).mem_nhds ⟨hRa, hw.2⟩] with p hp
    exact stress_inner m hinner hp.1.le hp.2

/-- The defining primitive has the exact negative weighted derivative. -/
theorem stress_weighted_hasDerivAt {S : Set ℝ} (hS : IsOpen S) {F : Field} (hF : Smooth S F)
    (m : ℕ) {R eta : ℝ} (hR : 0 < R) (heta : eta ∈ S) :
    HasDerivAt (fun r => r ^ m * stress m F (r, eta)) (-F (R, eta)) R := by
  have hp := (ProfileHistories.primitive_hasDerivAt
    (PositiveOrderMoments.parameterDomain S hS) hF (p := (R, eta)) ⟨mem_univ _, heta⟩).fun_neg
  apply hp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hR] with r hr
  rw [stress_of_pos m F (w := (r, eta)) hr]
  field_simp [pow_ne_zero m (ne_of_gt (show 0 < r from hr))]

theorem stress_radial_identity {S : Set ℝ} (hS : IsOpen S) {F : Field} (hF : Smooth S F)
    (m : ℕ) {a : ℝ} (ha : 0 < a)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, F (R, eta) = 0)
    {w : ℝ × ℝ} (hR : 0 < w.1) (heta : w.2 ∈ S) :
    (m : ℝ) * w.1 ^ (m - 1) * stress m F w + w.1 ^ m * dr (stress m F) w = -F w := by
  have ht := stress_smooth hS hF m ha hinner
  have hd := (radial_hasDerivAt hS (smooth_weighted ht m) heta).unique
    (stress_weighted_hasDerivAt hS hF m hR heta)
  rw [dr_weighted hS ht m heta] at hd
  exact hd

theorem stress_slice_support (m : ℕ) {F : Field} {S : Set ℝ} {a B : ℝ} (hB : 0 ≤ B)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, F (R, eta) = 0)
    (hs : exterior B S F) (hm : ∀ eta ∈ S, moment B 0 F eta = 0)
    {eta : ℝ} (heta : eta ∈ S) : support (fun R => stress m F (R, eta)) ⊆ Icc a B := by
  intro R hR
  constructor
  · by_contra hh
    exact hR (stress_inner m hinner (le_of_not_ge hh) heta)
  · by_contra hh
    exact hR (stress_exterior m hB hs hm (le_of_not_ge hh) heta)

noncomputable def radialSupport (S : Set ℝ) (a b : ℝ) (f : Field) : Prop :=
  ∀ eta ∈ S, ∀ R, R ∉ Icc a b → f (R, eta) = 0

theorem support_eventually_zero {S : Set ℝ} (hS : IsOpen S) {a b : ℝ} {f : Field}
    (hs : radialSupport S a b f) {w : ℝ × ℝ} (hw : w.2 ∈ S) (hR : w.1 ∉ Icc a b) :
    f =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [(isClosed_Icc.isOpen_compl.prod hS).mem_nhds ⟨hR, hw⟩] with p hp
  exact hs p.2 hp.2 p.1 hp.1

theorem jet_eq_zero_of_eventually {f : Field} {w : ℝ × ℝ}
    (hf : f =ᶠ[𝓝 w] fun _ => 0) (k : ℕ) : iteratedFDeriv ℝ k f w = 0 := by
  have hh : f =ᶠ[𝓝[univ] w] fun _ => (0 : ℝ) := by simpa only [nhdsWithin_univ] using hf
  have he := hh.iteratedFDerivWithin_eq (𝕜 := ℝ) hf.self_of_nhds k
  simpa only [iteratedFDerivWithin_univ, iteratedFDeriv_fun_zero, Pi.zero_apply] using he

theorem interior_quotient_smooth {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {a b l r : ℝ} (hs : radialSupport S a b f) (hab : Icc a b ⊆ Ioo l r)
    {zeta : ℝ → ℝ} (hz : ContDiffOn ℝ ∞ zeta (Ioo l r))
    (hz0 : ∀ R ∈ Ioo l r, zeta R ≠ 0) :
    Smooth S (fun w => f w / zeta w.1) := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  by_cases hR : w.1 ∈ Ioo l r
  · exact (hf.contDiffAt ((isOpen_univ.prod hS).mem_nhds hw)).div
      ((hz.contDiffAt (isOpen_Ioo.mem_nhds hR)).comp w contDiffAt_fst) (hz0 w.1 hR)
  · have ho : w.1 ∉ Icc a b := fun hm => hR (hab hm)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [support_eventually_zero hS hs hw.2 ho] with p hp
    simp [hp]

/-- Every actual derivative tensor has a weighted bound because its support
lies in one fixed compact subinterval of the positive-weight region. No
stress norm bound is an input. The constant may depend on the derivative order. -/
theorem interior_weighted_jets {S K : Set ℝ} (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    {f : Field} (hf : Smooth S f) {a b l r : ℝ}
    (hs : radialSupport S a b f) (hab : Icc a b ⊆ Ioo l r)
    {zeta : ℝ → ℝ} (hz : ContinuousOn zeta (Ioo l r))
    (hz0 : ∀ R ∈ Ioo l r, 0 < zeta R) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R ∈ Ioo l r, ∀ eta ∈ K,
      ‖iteratedFDeriv ℝ k f (R, eta)‖ ≤ C * zeta R := by
  have hcj : ContinuousOn (iteratedFDeriv ℝ k f) (Icc a b ×ˢ K) := by
    intro w hw
    have hh := hf.contDiffAt ((isOpen_univ.prod hS).mem_nhds ⟨mem_univ _, hKS hw.2⟩)
    exact (hh.iteratedFDeriv_right (m := 0) (by
      simp only [zero_add]
      exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).continuousAt.continuousWithinAt
  have hcz : ContinuousOn (fun w : ℝ × ℝ => zeta w.1) (Icc a b ×ˢ K) :=
    hz.comp continuous_fst.continuousOn (fun w hw => hab hw.1)
  have hc : ContinuousOn (fun w : ℝ × ℝ => ‖iteratedFDeriv ℝ k f w‖ / zeta w.1)
      (Icc a b ×ˢ K) := hcj.norm.div hcz (fun w hw => (hz0 w.1 (hab hw.1)).ne')
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro R hR eta heta
  by_cases hi : R ∈ Icc a b
  · apply (div_le_iff₀ (hz0 R hR)).mp
    exact (le_abs_self _).trans ((hC (R, eta) ⟨hi, heta⟩).trans (le_max_left _ _))
  · have hj := jet_eq_zero_of_eventually (support_eventually_zero hS hs (w := (R, eta)) (hKS heta)
    hi) k
    rw [hj, norm_zero]
    exact mul_nonneg (le_max_right _ _) (hz0 R hR).le

theorem stress_radialSupport (m : ℕ) {F : Field} {S : Set ℝ} {a B : ℝ} (hB : 0 ≤ B)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, F (R, eta) = 0)
    (hs : exterior B S F) (hm : ∀ eta ∈ S, moment B 0 F eta = 0) :
    radialSupport S a B (stress m F) := by
  intro eta heta R hR
  by_contra hn
  exact hR (stress_slice_support m hB hinner hs hm heta hn)

/-- A fixed interior support interval gives all weighted stress jets on
every compact parameter subinterval, as well as a smooth normalized stress. -/
theorem stress_weighted_jets {S K : Set ℝ} (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    {F : Field} (hF : Smooth S F) (m : ℕ) {a B l r : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    (hab : Icc a B ⊆ Ioo l r)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, F (R, eta) = 0)
    (hs : exterior B S F) (hm : ∀ eta ∈ S, moment B 0 F eta = 0)
    {zeta : ℝ → ℝ} (hz : ContDiffOn ℝ ∞ zeta (Ioo l r))
    (hz0 : ∀ R ∈ Ioo l r, 0 < zeta R) :
    Smooth S (fun w => stress m F w / zeta w.1) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ R ∈ Ioo l r, ∀ eta ∈ K,
        ‖iteratedFDeriv ℝ k (stress m F) (R, eta)‖ ≤ C * zeta R := by
  have ht := stress_smooth hS hF m ha hinner
  have hts := stress_radialSupport m hB hinner hs hm
  exact ⟨interior_quotient_smooth hS ht hts hab hz (fun R hR => (hz0 R hR).ne'),
    interior_weighted_jets hS hK hKS ht hts hab hz.continuousOn hz0⟩

theorem smooth_angularDensity {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u e : History} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (he : ∀ j, j ≤ n → Smooth S (e j))
    (h : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) :
    Smooth S (angularDensity h n v u e) :=
  (((((contDiffOn_fst.pow 2).mul (smooth_timeOp hS (he n le_rfl) h _ hell)).add
    (smooth_dr hS (smooth_weighted (smooth_conv hv he) 1))).add
      ((contDiffOn_fst.pow 2).mul (smooth_axialOp hS (smooth_conv hu he) h _ hell))).sub
        (smooth_dr hS (smooth_angularViscousFlux hS (he n le_rfl)))).sub
          ((contDiffOn_fst.pow 2).mul (smooth_axialOp2 hS (he (n - 1) (Nat.sub_le _ _)) h _ hell))

theorem smooth_axialDensity {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) :
    Smooth S (axialDensity h n v u p) :=
  ((((contDiffOn_fst.mul (smooth_timeOp hS (hu n le_rfl) h _ hell)).add
    (smooth_dr hS (smooth_conv hv hu))).add
      (contDiffOn_fst.mul (smooth_axialOp hS ((smooth_conv hu hu).add hp) h _ hell))).sub
        (smooth_dr hS (smooth_axialViscousFlux hS (hu n le_rfl)))).sub
          (contDiffOn_fst.mul (smooth_axialOp2 hS (hu (n - 1) (Nat.sub_le _ _)) h _ hell))

theorem exterior_weighted {S : Set ℝ} {B : ℝ} {f : Field} (hf : exterior B S f) (m : ℕ) :
    exterior B S (weighted m f) := by
  intro eta heta R hR
  simp [weighted, hf eta heta R hR]

theorem exterior_timeOp {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {B : ℝ} (hs : exterior B S f) (h b : ℝ) : exterior B S (timeOp h b f) := by
  intro eta heta R hR
  simp [timeOp, hs eta heta R hR, exterior_dr hS hf hs eta heta R hR,
    exterior_de hS hf hs eta heta R hR]

theorem exterior_axialOp2 {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {B : ℝ} (hs : exterior B S f) (h b : ℝ)
    (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) : exterior B S (axialOp2 h b f) :=
  exterior_axialOp hS (smooth_axialOp hS hf h b hell) (exterior_axialOp hS hf hs h b) h _

theorem exterior_angularDensity {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u e : History} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (he : ∀ j, j ≤ n → Smooth S (e j))
    (h B : ℝ) (hV : ∀ j, j ≤ n → exterior B S (v j))
    (hU : ∀ j, j ≤ n → exterior B S (u j)) (hE : exterior B S (e n))
    (hprev : exterior B S (axialOp2 h (orderExponent h (n - 1)) (e (n - 1)))) :
    exterior B S (angularDensity h n v u e) := by
  have hr := exterior_dr hS (smooth_weighted (smooth_conv hv he) 1)
    (exterior_weighted (exterior_conv_left hV) 1)
  have hz := exterior_axialOp hS (smooth_conv hu he) (exterior_conv_left hU) h (pressureExponent h
    n)
  have hvf : exterior B S (angularViscousFlux (e n)) := by
    intro eta heta R hR
    simp [angularViscousFlux, hE eta heta R hR, exterior_dr hS (he n le_rfl) hE eta heta R hR]
  have hk := exterior_dr hS (smooth_angularViscousFlux hS (he n le_rfl)) hvf
  intro eta heta R hR
  simp [angularDensity, exterior_timeOp hS (he n le_rfl) hE h (orderExponent h n) eta heta R hR,
    hr eta heta R hR, hz eta heta R hR, hk eta heta R hR, hprev eta heta R hR]

theorem exterior_axialDensity {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h B : ℝ) (hV : ∀ j, j ≤ n → exterior B S (v j))
    (hU : ∀ j, j ≤ n → exterior B S (u j)) (hP : exterior B S p)
    (hprev : exterior B S (axialOp2 h (orderExponent h (n - 1)) (u (n - 1)))) :
    exterior B S (axialDensity h n v u p) := by
  have hr := exterior_dr hS (smooth_conv hv hu) (exterior_conv_left hV)
  have hcp : exterior B S (fun w => conv n u u w + p w) := by
    intro eta heta R hR
    change conv n u u (R, eta) + p (R, eta) = 0
    rw [exterior_conv_left hU eta heta R hR, hP eta heta R hR, add_zero]
  have hz := exterior_axialOp hS ((smooth_conv hu hu).add hp) hcp h (pressureExponent h n)
  have hvf : exterior B S (axialViscousFlux (u n)) := by
    intro eta heta R hR
    simp [axialViscousFlux, exterior_dr hS (hu n le_rfl) (hU n le_rfl) eta heta R hR]
  have hk := exterior_dr hS (smooth_axialViscousFlux hS (hu n le_rfl)) hvf
  intro eta heta R hR
  simp [axialDensity, exterior_timeOp hS (hu n le_rfl) (hU n le_rfl) h (orderExponent h n) eta heta
    R hR,
    hr eta heta R hR, hz eta heta R hR, hk eta heta R hR, hprev eta heta R hR]

noncomputable def angularStress (h : ℝ) (n : ℕ) (v u e : History) : Field :=
  stress 2 (angularDensity h n v u e)

noncomputable def axialStress (h : ℝ) (n : ℕ) (v u : History) (p : Field) : Field :=
  stress 1 (axialDensity h n v u p)

/-- For n≥2 all the angular hypotheses below are supplied by ordinary
positive-order moments and compact positive-order profiles. -/
theorem angular_stress_support {S : Set ℝ} (hS : IsOpen S) {n : ℕ} (hn : 2 ≤ n)
    {v u e : History} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (he : ∀ j, j ≤ n → Smooth S (e j))
    (h a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hV : ∀ j, j ≤ n → exterior B S (v j)) (hU : ∀ j, j ≤ n → exterior B S (u j))
    (hE : ∀ j, 0 < j → j ≤ n → exterior B S (e j))
    (hem : ∀ eta ∈ S, moment B 2 (e n) eta = 0)
    (hum : ∀ eta ∈ S, moment B 2 (conv n u e) eta = 0)
    (hprev : ∀ eta ∈ S, moment B 2 (e (n - 1)) eta = 0)
    (hdiv : ∀ w : ℝ × ℝ, w.2 ∈ S → ∀ j, j ≤ n →
      dr (v j) w = -w.1 * axialOp h (orderExponent h j) (u j) w)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, angularWeighted h n v u e (R, eta) = 0) :
    Smooth S (angularStress h n v u e) ∧ radialSupport S a B (angularStress h n v u e) ∧
      ∀ eta ∈ S, ∀ R, 0 < R → HasDerivAt (fun r => r ^ 2 * angularStress h n v u e (r, eta))
        (-angularWeighted h n v u e (R, eta)) R := by
  have hen := hE n (by omega) le_rfl
  have hep := hE (n - 1) (by omega) (Nat.sub_le _ _)
  have hsm := smooth_angularDensity hS hv hu he h hell
  have htotal : ∀ eta ∈ S, moment B 0 (angularDensity h n v u e) eta = 0 :=
    fun eta heta => angular_integral_zero hS hv hu he h B hell hen hV hem hum
      (exterior_conv_left hU) hep hprev heta
  have hout := exterior_angularDensity hS hv hu he h B hV hU hen
    (exterior_axialOp2 hS (he (n - 1) (Nat.sub_le _ _)) hep h _ hell)
  have hin : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, angularDensity h n v u e (R, eta) = 0 := by
    intro eta heta R hR
    rw [← angularWeighted_eq_density hS hv hu he h heta (hdiv _ heta)]
    exact hinner eta heta R hR
  refine ⟨stress_smooth hS hsm 2 ha hin, stress_radialSupport 2 hB hin hout htotal, ?_⟩
  intro eta heta R hR
  rw [angularWeighted_eq_density hS hv hu he h heta (hdiv _ heta)]
  exact stress_weighted_hasDerivAt hS hsm 2 hR heta

theorem axial_stress_support {S : Set ℝ} (hS : IsOpen S) {n : ℕ} (hn : 0 < n)
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hV : ∀ j, j ≤ n → exterior B S (v j)) (hU : ∀ j, j ≤ n → exterior B S (u j))
    (hP : exterior B S p) (haxis : ∀ eta ∈ S, ∀ j, j ≤ n → v j (0, eta) = 0)
    (hum : ∀ eta ∈ S, moment B 1 (u n) eta = 0)
    (hflux : ∀ eta ∈ S, moment B 1 (fun w => conv n u u w + p w) eta = 0)
    (hprev : ∀ eta ∈ S, moment B 1 (u (n - 1)) eta = 0)
    (hdiv : ∀ w : ℝ × ℝ, w.2 ∈ S → ∀ j, j ≤ n →
      dr (v j) w = -w.1 * axialOp h (orderExponent h j) (u j) w)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, axialWeighted h n v u p (R, eta) = 0) :
    Smooth S (axialStress h n v u p) ∧ radialSupport S a B (axialStress h n v u p) ∧
      ∀ eta ∈ S, ∀ R, 0 < R → HasDerivAt (fun r => r * axialStress h n v u p (r, eta))
        (-axialWeighted h n v u p (R, eta)) R := by
  have hprev_le : n - 1 ≤ n := (Nat.sub_lt hn (by decide : 0 < 1)).le
  have hsm := smooth_axialDensity hS hv hu hp h hell
  have hax : ∀ eta ∈ S, conv n v u (0, eta) = 0 := by
    intro eta heta
    unfold conv
    apply Finset.sum_eq_zero
    intro j hj
    rw [haxis eta heta j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), zero_mul]
  have hfB : ∀ eta ∈ S, conv n u u (B, eta) + p (B, eta) = 0 := by
    intro eta heta
    rw [exterior_conv_left hU eta heta B le_rfl, hP eta heta B le_rfl, add_zero]
  have htotal : ∀ eta ∈ S, moment B 0 (axialDensity h n v u p) eta = 0 :=
    fun eta heta => axial_integral_zero hS hv hu hp h B hell (hU n le_rfl) hV hax hum hflux hfB
      (hU (n - 1) hprev_le) hprev heta
  have hout := exterior_axialDensity hS hv hu hp h B hV hU hP
    (exterior_axialOp2 hS (hu (n - 1) (Nat.sub_le _ _)) (hU (n - 1) (Nat.sub_le _ _)) h _ hell)
  have hin : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, axialDensity h n v u p (R, eta) = 0 := by
    intro eta heta R hR
    rw [← axialWeighted_eq_density hS hv hu hp h heta (hdiv _ heta)]
    exact hinner eta heta R hR
  refine ⟨stress_smooth hS hsm 1 ha hin, stress_radialSupport 1 hB hin hout htotal, ?_⟩
  intro eta heta R hR
  rw [axialWeighted_eq_density hS hv hu hp h heta (hdiv _ heta)]
  unfold axialStress
  simpa only [pow_one] using stress_weighted_hasDerivAt hS hsm 1 hR heta

/-- The order-one angular input is a moment of the actual axial viscosity,
not a condition on the total residual. It is supplied by differentiating
the restored renormalized order-zero physical angular moment. -/
noncomputable def LowerAngularViscosityMoment (S : Set ℝ) (B h : ℝ) (e₀ : Field) : Prop :=
  ∀ eta ∈ S, moment B 2 (axialOp2 h (orderExponent h 0) e₀) eta = 0

theorem order_one_angular_stress_support {S : Set ℝ} (hS : IsOpen S)
    {v u e : History} (hv : ∀ j, j ≤ 1 → Smooth S (v j))
    (hu : ∀ j, j ≤ 1 → Smooth S (u j)) (he : ∀ j, j ≤ 1 → Smooth S (e j))
    (h a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hV : ∀ j, j ≤ 1 → exterior B S (v j)) (hU : ∀ j, j ≤ 1 → exterior B S (u j))
    (hE : exterior B S (e 1))
    (hem : ∀ eta ∈ S, moment B 2 (e 1) eta = 0)
    (hum : ∀ eta ∈ S, moment B 2 (conv 1 u e) eta = 0)
    (hvisc : LowerAngularViscosityMoment S B h (e 0))
    (hviscExterior : exterior B S (axialOp2 h (orderExponent h 0) (e 0)))
    (hdiv : ∀ w : ℝ × ℝ, w.2 ∈ S → ∀ j, j ≤ 1 →
      dr (v j) w = -w.1 * axialOp h (orderExponent h j) (u j) w)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, angularWeighted h 1 v u e (R, eta) = 0) :
    Smooth S (angularStress h 1 v u e) ∧ radialSupport S a B (angularStress h 1 v u e) ∧
      ∀ eta ∈ S, ∀ R, 0 < R → HasDerivAt (fun r => r ^ 2 * angularStress h 1 v u e (r, eta))
        (-angularWeighted h 1 v u e (R, eta)) R := by
  have hsm := smooth_angularDensity hS hv hu he h hell
  have htotal : ∀ eta ∈ S, moment B 0 (angularDensity h 1 v u e) eta = 0 := by
    intro eta heta
    rw [angular_integral_balance hS hv hu he h B hell hE hV hem hum (exterior_conv_left hU) heta]
    simp only [Nat.sub_self, hvisc eta heta, neg_zero]
  have hout := exterior_angularDensity hS hv hu he h B hV hU hE hviscExterior
  have hin : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, angularDensity h 1 v u e (R, eta) = 0 := by
    intro eta heta R hR
    rw [← angularWeighted_eq_density hS hv hu he h heta (hdiv _ heta)]
    exact hinner eta heta R hR
  refine ⟨stress_smooth hS hsm 2 ha hin, stress_radialSupport 2 hB hin hout htotal, ?_⟩
  intro eta heta R hR
  rw [angularWeighted_eq_density hS hv hu he h heta (hdiv _ heta)]
  exact stress_weighted_hasDerivAt hS hsm 2 hR heta

/-- A concrete two-edge weight of the form prescribed in (20). -/
noncomputable def logFlatWeight (l r cL cR R : ℝ) : ℝ :=
  if R ∈ Ioo l r then
    FlatCutoff.edge cL (Real.log (R / l)) * FlatCutoff.edge cR (Real.log (r / R))
  else 0

theorem logFlatWeight_pos {l r : ℝ} (hl : 0 < l) (cL cR : ℝ)
    {R : ℝ} (hR : R ∈ Ioo l r) : 0 < logFlatWeight l r cL cR R := by
  rw [logFlatWeight, ite_eq_left hR]
  apply mul_pos
  · exact FlatCutoff.edge_pos cL (Real.log_pos ((one_lt_div hl).mpr hR.1))
  · exact FlatCutoff.edge_pos cR (Real.log_pos ((one_lt_div (hl.trans hR.1)).mpr hR.2))

theorem logFlatWeight_contDiffOn {l r cL cR : ℝ} (hl : 0 < l)
    (hcL : 0 < cL) (hcR : 0 < cR) :
    ContDiffOn ℝ ∞ (logFlatWeight l r cL cR) (Ioo l r) := by
  intro R hR
  apply ContDiffAt.contDiffWithinAt
  have hp := hl.trans hR.1
  have hr := hp.trans hR.2
  have hleft : ContDiffAt ℝ ∞ (fun x : ℝ => Real.log (x / l)) R :=
    (contDiffAt_id.div_const l).log (div_ne_zero hp.ne' hl.ne')
  have hright : ContDiffAt ℝ ∞ (fun x : ℝ => Real.log (r / x)) R :=
    (contDiffAt_const.div contDiffAt_id hp.ne').log (div_ne_zero hr.ne' hp.ne')
  have hs : ContDiffAt ℝ ∞ (fun x =>
      FlatCutoff.edge cL (Real.log (x / l)) * FlatCutoff.edge cR (Real.log (r / x))) R :=
    ((FlatCutoff.edge_contDiff hcL).contDiffAt.comp R hleft).mul
      ((FlatCutoff.edge_contDiff hcR).contDiffAt.comp R hright)
  apply hs.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hR] with x hx
  exact ite_eq_left hx

/-- In particular the prescribed logarithmic Gaussian weight controls every
jet, with inverse-edge loss zero, for a field supported strictly inside both
fixed edges. The constants are obtained from compactness. -/
theorem logarithmic_weighted_jets {S K : Set ℝ} (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    {f : Field} (hf : Smooth S f) {a b l r cL cR : ℝ}
    (hs : radialSupport S a b f) (hab : Icc a b ⊆ Ioo l r)
    (hl : 0 < l) (hcL : 0 < cL) (hcR : 0 < cR) :
    Smooth S (fun w => f w / logFlatWeight l r cL cR w.1) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ R ∈ Ioo l r, ∀ eta ∈ K,
        ‖iteratedFDeriv ℝ k f (R, eta)‖ ≤ C * logFlatWeight l r cL cR R := by
  have hz := logFlatWeight_contDiffOn (r := r) hl hcL hcR
  have hp : ∀ R ∈ Ioo l r, 0 < logFlatWeight l r cL cR R :=
    fun R hR => logFlatWeight_pos hl cL cR hR
  exact ⟨interior_quotient_smooth hS hf hs hab hz (fun R hR => (hp R hR).ne'),
    interior_weighted_jets hS hK hKS hf hs hab hz.continuousOn hp⟩

end NavierStokes.SlowStressSupport
