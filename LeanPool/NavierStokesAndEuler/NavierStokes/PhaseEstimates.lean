/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MovingFrameODE
public import LeanPool.NavierStokesAndEuler.NavierStokes.ChartScales
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Quantitative estimates for the actual pulse normal

The rounded frequency is used consistently throughout the actual phase.  The
estimates below start from representative data and local base derivative bounds,
rather than assuming that the normal is close to its reference value.
-/

@[expose] public section


namespace NavierStokes.PhaseEstimates

open Set Filter
open scoped Topology InnerProductSpace

/-- Plane: an abbreviation for `MovingFrameODE.Plane`. -/
abbrev Plane := MovingFrameODE.Plane
/-- Space: an abbreviation for `MovingFrameODE.Space`. -/
abbrev Space := MovingFrameODE.Space
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow

/-- Rounding in the punctured integer lattice.  The zero floor is replaced by
one; the distance to the input is still at most one. -/
noncomputable def nonzeroRound (x : ℝ) : ℤ := if Int.floor x = 0 then 1 else Int.floor x

theorem nonzeroRound_ne_zero (x : ℝ) : nonzeroRound x ≠ 0 := by
  unfold nonzeroRound
  split_ifs with h
  · norm_num
  · exact h

theorem nonzeroRound_error (x : ℝ) : |(nonzeroRound x : ℝ) - x| ≤ 1 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  unfold nonzeroRound
  split_ifs with h
  · rw [h] at hlo hhi
    norm_num at hlo hhi ⊢
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Rounded frequency, given by `(nonzeroRound (k * target) : ℝ) / k`. -/
noncomputable def roundedFrequency (k target : ℝ) : ℝ := (nonzeroRound (k * target) : ℝ) / k

theorem roundedFrequency_integer {k : ℝ} (hk : k ≠ 0) (target : ℝ) :
    k * roundedFrequency k target = (nonzeroRound (k * target) : ℝ) := by
  unfold roundedFrequency
  field_simp

theorem roundedFrequency_nonzero {k : ℝ} (hk : k ≠ 0) (target : ℝ) :
    ∃ m : ℤ, m ≠ 0 ∧ k * roundedFrequency k target = (m : ℝ) :=
  ⟨nonzeroRound (k * target), nonzeroRound_ne_zero _, roundedFrequency_integer hk target⟩

theorem roundedFrequency_ne_zero {k : ℝ} (hk : k ≠ 0) (target : ℝ) :
    roundedFrequency k target ≠ 0 := by
  apply div_ne_zero _ hk
  exact_mod_cast nonzeroRound_ne_zero (k * target)

theorem roundedFrequency_error {k : ℝ} (hk : 0 < k) (target : ℝ) :
    |roundedFrequency k target - target| ≤ 1 / k := by
  have heq : roundedFrequency k target - target =
      ((nonzeroRound (k * target) : ℝ) - k * target) / k := by
    unfold roundedFrequency
    field_simp
  rw [heq, abs_div, abs_of_pos hk]
  exact div_le_div_of_nonneg_right (nonzeroRound_error _) hk.le

/-- The fixed representative frequency in its two tangential components. -/
noncomputable def representativeFrequency (B sigma u L : ℝ) (K g : Plane) : Plane :=
  B • (K - (sigma * u / (L * ‖g‖ ^ 2)) • g)

theorem representative_slope (B sigma u L : ℝ) (K g : Plane)
    (hg : g ≠ 0) (horth : ⟪K, g⟫_ℝ = 0) :
    ⟪representativeFrequency B sigma u L K g, g⟫_ℝ = -sigma * B * u / L := by
  have hnorm : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  simp only [representativeFrequency, real_inner_smul_left, inner_sub_left,
    real_inner_self_eq_norm_sq, horth]
  by_cases hL : L = 0
  · simp [hL]
  · field_simp
    ring

theorem representative_tilt (B sigma u L : ℝ) (K g : Plane) :
    ‖representativeFrequency B sigma u L K g - B • K‖ =
      |B| * |sigma| * |u| / (|L| * ‖g‖) := by
  by_cases hg : g = 0
  · simp [representativeFrequency, hg]
  have hnorm : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have heq : representativeFrequency B sigma u L K g - B • K =
      -(B * (sigma * u / (L * ‖g‖ ^ 2))) • g := by
    unfold representativeFrequency
    module
  rw [heq, norm_smul]
  simp only [norm_neg, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_norm]
  by_cases hL : L = 0
  · simp [hL]
  · have habsL : |L| ≠ 0 := abs_ne_zero.mpr hL
    field_simp

/-- A bound on the fixed representative frequency follows from its explicit
tilt; its angular component is later multiplied by the representative radius. -/
theorem representative_frequency_bound (B sigma u L : ℝ) (K g : Plane)
    (hK : ‖K‖ = 1) :
    ‖representativeFrequency B sigma u L K g‖ ≤
      |B| + |B| * |sigma| * |u| / (|L| * ‖g‖) := by
  have h := norm_add_le (representativeFrequency B sigma u L K g - B • K) (B • K)
  rw [sub_add_cancel, representative_tilt, norm_smul, Real.norm_eq_abs, hK, mul_one] at h
  linarith only [h]

/-- Signed slot, given by `sigma * (u / 2 + u * v / L)`. -/
noncomputable def signedSlot (sigma u L v : ℝ) : ℝ := sigma * (u / 2 + u * v / L)

/-- The cancellation producing the intended radial slope is exact for the
unrounded representative data. -/
theorem radial_reference_identity (B sigma u L v : ℝ) :
    sigma * B * u / 2 - v * (-sigma * B * u / L) = B * signedSlot sigma u L v := by
  unfold signedSlot
  ring

/-! ## Local C2 control implies the derivative comparison at the representative -/

section LocalBase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second derivative controls variation of the first derivative across
a convex chart.  The actual base differs in C1 by the independently supplied
`baseError`, and the chart diameter is `diameter`. -/
theorem local_first_derivative_close {F F0 : E → ℝ} {U : Set E} {q q0 : E}
    {M diameter baseError : ℝ} (hM : 0 ≤ M) (hU : Convex ℝ U)
    (hq : q ∈ U) (hq0 : q0 ∈ U)
    (hC2 : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ F0) x)
    (hsecond : ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ F0) x‖ ≤ M)
    (hdiameter : ‖q - q0‖ ≤ diameter)
    (hbase : ‖fderiv ℝ F q - fderiv ℝ F0 q‖ ≤ baseError) :
    ‖fderiv ℝ F q - fderiv ℝ F0 q0‖ ≤ M * diameter + baseError := by
  have hlocal := hU.norm_image_sub_le_of_norm_fderiv_le hC2 hsecond hq0 hq
  calc
    _ ≤ ‖fderiv ℝ F q - fderiv ℝ F0 q‖ + ‖fderiv ℝ F0 q - fderiv ℝ F0 q0‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ baseError + M * diameter := add_le_add hbase
      (hlocal.trans (mul_le_mul_of_nonneg_left hdiameter hM))
    _ = _ := by ring

theorem local_directional_derivative_close {F F0 : E → ℝ} {U : Set E} {q q0 e : E}
    {M diameter baseError : ℝ} (hM : 0 ≤ M) (hU : Convex ℝ U)
    (hq : q ∈ U) (hq0 : q0 ∈ U)
    (hC2 : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ F0) x)
    (hsecond : ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ F0) x‖ ≤ M)
    (hdiameter : ‖q - q0‖ ≤ diameter)
    (hbase : ‖fderiv ℝ F q - fderiv ℝ F0 q‖ ≤ baseError) (he : ‖e‖ ≤ 1) :
    |fderiv ℝ F q e - fderiv ℝ F0 q0 e| ≤ M * diameter + baseError := by
  have hop := local_first_derivative_close hM hU hq hq0 hC2 hsecond hdiameter hbase
  have hbound : 0 ≤ M * diameter + baseError := (norm_nonneg _).trans hop
  calc
    _ = ‖(fderiv ℝ F q - fderiv ℝ F0 q0) e‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ F q - fderiv ℝ F0 q0‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (M * diameter + baseError) * 1 := mul_le_mul hop he (norm_nonneg _) hbound
    _ = _ := mul_one _

end LocalBase

/-! ## Pointwise error estimates before choosing the band scale -/

theorem radial_frequency_error {p target pz a a0 b b0 M rounding base : ℝ}
    (hp : |p - target| ≤ rounding) (ha : |a| ≤ M)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M)
    (ha0 : |a - a0| ≤ base) (hb0 : |b - b0| ≤ base) :
    |(p * a + pz * b) - (target * a0 + pz * b0)| ≤ M * rounding + 2 * M * base := by
  have hM : 0 ≤ M := (abs_nonneg _).trans ha
  have hr : 0 ≤ rounding := (abs_nonneg _).trans hp
  have hbase : 0 ≤ base := (abs_nonneg _).trans ha0
  calc
    _ = |(p - target) * a + target * (a - a0) + pz * (b - b0)| := by congr 1; ring
    _ ≤ |(p - target) * a + target * (a - a0)| + |pz * (b - b0)| := abs_add_le _ _
    _ ≤ (|(p - target) * a| + |target * (a - a0)|) + |pz * (b - b0)| :=
      add_le_add_left (abs_add_le _ _) _
    _ = (|p - target| * |a| + |target| * |a - a0|) + |pz| * |b - b0| := by
      rw [abs_mul, abs_mul, abs_mul]
    _ ≤ (rounding * M + M * base) + M * base := add_le_add
      (add_le_add (mul_le_mul hp ha (abs_nonneg _) hr)
        (mul_le_mul htarget ha0 (abs_nonneg _) hM))
      (mul_le_mul hpz hb0 (abs_nonneg _) hM)
    _ = _ := by ring

theorem angular_frequency_error {p target R R0 M rounding diameter : ℝ}
    (hR : R ≠ 0) (hR0 : R0 ≠ 0)
    (hp : |p - target| ≤ rounding) (htarget : |target| ≤ M)
    (hRi : |1 / R| ≤ M) (hR0i : |1 / R0| ≤ M) (hRd : |R - R0| ≤ diameter) :
    |p / R - target / R0| ≤ M * rounding + M ^ 3 * diameter := by
  have hM : 0 ≤ M := (abs_nonneg _).trans htarget
  have hr : 0 ≤ rounding := (abs_nonneg _).trans hp
  have hd : 0 ≤ diameter := (abs_nonneg _).trans hRd
  have htriple : |target * (1 / R) * (1 / R0)| ≤ M ^ 3 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (M * M) * M := mul_le_mul
        (mul_le_mul htarget hRi (abs_nonneg _) hM) hR0i (abs_nonneg _) (mul_nonneg hM hM)
      _ = _ := by ring
  have heq : p / R - target / R0 =
      (p - target) * (1 / R) + (target * (1 / R) * (1 / R0)) * (R0 - R) := by
    field_simp; ring
  rw [heq]
  calc
    _ ≤ |(p - target) * (1 / R)| + |(target * (1 / R) * (1 / R0)) * (R0 - R)| := abs_add_le _ _
    _ = |p - target| * |1 / R| + |target * (1 / R) * (1 / R0)| * |R0 - R| := by
      rw [abs_mul, abs_mul]
    _ ≤ rounding * M + M ^ 3 * diameter := add_le_add
      (mul_le_mul hp hRi (abs_nonneg _) hr)
      (mul_le_mul htriple (by simpa only [abs_sub_comm] using hRd) (abs_nonneg _) (pow_nonneg hM _))
    _ = _ := by ring

theorem axial_frequency_bound {p target pz a b M rounding : ℝ}
    (hM : 1 ≤ M) (hr : rounding ≤ 1) (hp : |p - target| ≤ rounding)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |p * a + pz * b| ≤ 3 * M ^ 2 := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hpp : |p| ≤ 2 * M := by
    have h := (abs_add_le (p - target) target)
    rw [sub_add_cancel] at h
    linarith only [h, hp, hr, htarget, hM]
  calc
    _ ≤ |p * a| + |pz * b| := abs_add_le _ _
    _ = |p| * |a| + |pz| * |b| := by rw [abs_mul, abs_mul]
    _ ≤ (2 * M) * M + M * M := add_le_add
      (mul_le_mul hpp ha (abs_nonneg _) (by positivity))
      (mul_le_mul hpz hb (abs_nonneg _) hM0)
    _ = _ := by ring

/-- Explicit normal, given by `!₂[x0 - v * (p * FR + pz * GR), p / R, pz - ε * v * (p * FZ + pz
* GZ)]`. -/
noncomputable def explicitNormal (ε p pz x0 R v FR GR FZ GZ : ℝ) : Space :=
  !₂[x0 - v * (p * FR + pz * GR), p / R, pz - ε * v * (p * FZ + pz * GZ)]

/-- Reference normal, given by `MovingFrameODE.pack (B * signedSlot sigma u L v) (B • K)`. -/
noncomputable def referenceNormal (B sigma u L v : ℝ) (K : Plane) : Space :=
  MovingFrameODE.pack (B * signedSlot sigma u L v) (B • K)

theorem vec3_norm_le_sum (w : Space) : ‖w‖ ≤ |w 0| + |w 1| + |w 2| := by
  have hs := PhaseCalculus.vec3_norm_sq w
  nlinarith only [hs, norm_nonneg w, sq_abs (w 0), sq_abs (w 1), sq_abs (w 2),
    abs_nonneg (w 0), abs_nonneg (w 1), abs_nonneg (w 2),
    mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 1)),
    mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 2)),
    mul_nonneg (abs_nonneg (w 1)) (abs_nonneg (w 2))]

/-- Assembly of the actual normal error from its three independently derived
coefficient errors.  Slot length multiplies only the radial and axial defects. -/
theorem normal_error_from_components
    {ε p pz R v FR GR FZ GZ B sigma u L radial angular axial shear : ℝ} {K : Plane}
    (hRadial : |p * FR + pz * GR - (-sigma * B * u / L)| ≤ radial)
    (hAngular : |p / R - B * K 0| ≤ angular)
    (hAxial : |pz - B * K 1| ≤ axial)
    (hShear : |p * FZ + pz * GZ| ≤ shear) :
    ‖explicitNormal ε p pz (sigma * B * u / 2) R v FR GR FZ GZ -
      referenceNormal B sigma u L v K‖ ≤
      |v| * radial + angular + axial + |ε| * |v| * shear := by
  have hrad : |sigma * B * u / 2 - v * (p * FR + pz * GR) - B * signedSlot sigma u L v| ≤
      |v| * radial := by
    have heq : sigma * B * u / 2 - v * (p * FR + pz * GR) - B * signedSlot sigma u L v =
        -v * (p * FR + pz * GR - (-sigma * B * u / L)) := by
      unfold signedSlot
      ring
    rw [heq, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hRadial (abs_nonneg _)
  have hz : |pz - ε * v * (p * FZ + pz * GZ) - B * K 1| ≤ axial + |ε| * |v| * shear := by
    calc
      _ = |(pz - B * K 1) - ε * v * (p * FZ + pz * GZ)| := by congr 1; ring
      _ ≤ |pz - B * K 1| + |ε * v * (p * FZ + pz * GZ)| := abs_sub _ _
      _ = |pz - B * K 1| + |ε| * |v| * |p * FZ + pz * GZ| := by rw [abs_mul, abs_mul]
      _ ≤ axial + |ε| * |v| * shear := add_le_add hAxial
        (mul_le_mul_of_nonneg_left hShear (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  have h := vec3_norm_le_sum (explicitNormal ε p pz (sigma * B * u / 2) R v FR GR FZ GZ -
    referenceNormal B sigma u L v K)
  change ‖explicitNormal ε p pz (sigma * B * u / 2) R v FR GR FZ GZ -
      referenceNormal B sigma u L v K‖ ≤
    |sigma * B * u / 2 - v * (p * FR + pz * GR) - B * signedSlot sigma u L v| +
    |p / R - B * K 0| + |pz - ε * v * (p * FZ + pz * GZ) - B * K 1| at h
  linarith only [h, hrad, hAngular, hz]

theorem representative_slope_coordinates
    {B sigma u L R0 target pz FR0 GR0 : ℝ} {K g : Plane}
    (hR0 : R0 ≠ 0) (hg : g ≠ 0) (horth : ⟪K, g⟫_ℝ = 0)
    (hgdef : g = !₂[R0 * FR0, GR0])
    (hfreq : (!₂[target / R0, pz] : Plane) = representativeFrequency B sigma u L K g) :
    target * FR0 + pz * GR0 = -sigma * B * u / L := by
  have h := representative_slope B sigma u L K g hg horth
  rw [← hfreq, hgdef] at h
  have hi : ⟪(!₂[target / R0, pz] : Plane), (!₂[R0 * FR0, GR0] : Plane)⟫_ℝ =
      target * FR0 + pz * GR0 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    field_simp
  rwa [hi] at h

theorem representative_coordinate_errors
    {B sigma u L R0 target pz : ℝ} {K g : Plane}
    (hfreq : (!₂[target / R0, pz] : Plane) = representativeFrequency B sigma u L K g) :
    |target / R0 - B * K 0| ≤ |B| * |sigma| * |u| / (|L| * ‖g‖) ∧
    |pz - B * K 1| ≤ |B| * |sigma| * |u| / (|L| * ‖g‖) := by
  have h (i : Fin 2) := PiLp.norm_apply_le (representativeFrequency B sigma u L K g - B • K) i
  rw [representative_tilt, ← hfreq] at h
  constructor
  · simpa using h 0
  · simpa using h 1

/-- The complete finite estimate starts from the chosen representative and
the local derivatives of the actual base. -/
theorem explicit_normal_estimate
    {ε p target pz R R0 v FR GR FZ GZ FR0 GR0 B sigma u L M rounding diameter base : ℝ}
    {K g : Plane}
    (hR : R ≠ 0) (hR0 : R0 ≠ 0) (hg : g ≠ 0) (horth : ⟪K, g⟫_ℝ = 0)
    (hgdef : g = !₂[R0 * FR0, GR0])
    (hfreq : (!₂[target / R0, pz] : Plane) = representativeFrequency B sigma u L K g)
    (hM : 1 ≤ M) (hround : rounding ≤ 1) (hp : |p - target| ≤ rounding)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M)
    (hRi : |1 / R| ≤ M) (hR0i : |1 / R0| ≤ M) (hRd : |R - R0| ≤ diameter)
    (hFR : |FR| ≤ M) (hFZ : |FZ| ≤ M) (hGZ : |GZ| ≤ M)
    (hFR0 : |FR - FR0| ≤ base) (hGR0 : |GR - GR0| ≤ base) :
    ‖explicitNormal ε p pz (sigma * B * u / 2) R v FR GR FZ GZ -
      referenceNormal B sigma u L v K‖ ≤
      |v| * (M * rounding + 2 * M * base) + M * rounding + M ^ 3 * diameter +
      2 * (|B| * |sigma| * |u| / (|L| * ‖g‖)) + |ε| * |v| * (3 * M ^ 2) := by
  have hslope := representative_slope_coordinates hR0 hg horth hgdef hfreq
  have hrad := radial_frequency_error hp hFR htarget hpz hFR0 hGR0
  rw [hslope] at hrad
  have hangle := angular_frequency_error hR hR0 hp htarget hRi hR0i hRd
  obtain ⟨hc0, hc1⟩ := representative_coordinate_errors hfreq
  have hangular : |p / R - B * K 0| ≤ M * rounding + M ^ 3 * diameter +
      |B| * |sigma| * |u| / (|L| * ‖g‖) := by
    calc
      _ ≤ |p / R - target / R0| + |target / R0 - B * K 0| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hangle hc0
  have hshear := axial_frequency_bound hM hround hp htarget hpz hFZ hGZ
  have h := normal_error_from_components (ε := ε) (v := v) hrad hangular hc1 hshear
  linarith only [h]

theorem phaseNormal_eq_explicit (ε p pz x0 : ℝ) (F G : Slow → ℝ)
    (q : PhaseCalculus.Slot) (hε : ε ≠ 0)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    PhaseCalculus.phaseNormal ε p pz x0 F G q =
      explicitNormal ε p pz x0 q.1.1 q.2.2
        (PhaseCalculus.slowR F q.1) (PhaseCalculus.slowR G q.1)
        (PhaseCalculus.slowZ F q.1) (PhaseCalculus.slowZ G q.1) :=
  PhaseCalculus.phaseNormal_formula ε p pz x0 F G q hε hF hG

/-- Phase error, given by `1 / S + S * ε ^ 2 + S / k + ε * S`. -/
noncomputable def phaseError (S ε k : ℝ) : ℝ := 1 / S + S * ε ^ 2 + S / k + ε * S
/-- Phase constant, given by `8 * M ^ 3 + 2 * M ^ 4`. -/
noncomputable def phaseConstant (M : ℝ) : ℝ := 8 * M ^ 3 + 2 * M ^ 4

theorem inverse_cube_bounds {S : ℝ} (hS : 1 ≤ S) :
    1 / S ^ 3 ≤ 1 / S ∧ S * (1 / S ^ 3) ≤ 1 / S := by
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have h2 : S ≤ S ^ 2 := by nlinarith only [hS]
  have h3 : S ^ 2 ≤ S ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hS (sq_nonneg S)
    nlinarith only [h]
  constructor
  · exact one_div_le_one_div_of_le hS0 (h2.trans h3)
  · have heq : S * (1 / S ^ 3) = 1 / S ^ 2 := by field_simp
    rw [heq]
    exact one_div_le_one_div_of_le hS0 h2

theorem representative_tilt_scaled {B sigma u L M S : ℝ} {g : Plane}
    (hM : 0 ≤ M) (hB : |B| ≤ M) (hsigma : |sigma| = 1)
    (hu : |u| ≤ M) (hg : 1 / ‖g‖ ≤ M) (hL : 1 / |L| ≤ M / S) :
    |B| * |sigma| * |u| / (|L| * ‖g‖) ≤ M ^ 4 / S := by
  rw [hsigma, mul_one]
  have hbu : |B| * |u| ≤ M * M := mul_le_mul hB hu (abs_nonneg _) hM
  calc
    _ = (|B| * |u|) * (1 / ‖g‖) * (1 / |L|) := by ring
    _ ≤ (M * M) * M * (M / S) := mul_le_mul
      (mul_le_mul hbu hg (one_div_nonneg.mpr (norm_nonneg _)) (mul_nonneg hM hM)) hL
      (one_div_nonneg.mpr (abs_nonneg _)) (by positivity)
    _ = _ := by ring

/-- A single algebraic estimate displays every long-slot loss. -/
theorem assembled_error_scaled {M S ε k v tilt : ℝ}
    (hM : 1 ≤ M) (hS : 1 ≤ S) (hk : 0 < k) (hε : 0 ≤ ε)
    (hv : |v| ≤ M * S) (htilt : tilt ≤ M ^ 4 / S) :
    |v| * (M * (1 / k) + 2 * M * (M * (1 / S ^ 3 + ε ^ 2))) +
      M * (1 / k) + M ^ 3 * (1 / S ^ 3) + 2 * tilt + |ε| * |v| * (3 * M ^ 2) ≤
      phaseConstant M * phaseError S ε k := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have he0 : 0 ≤ 1 / S := (one_div_pos.mpr hS0).le
  have he1 : 0 ≤ S * ε ^ 2 := mul_nonneg hS0.le (sq_nonneg _)
  have he2 : 0 ≤ S / k := (div_pos hS0 hk).le
  have he3 : 0 ≤ ε * S := mul_nonneg hε hS0.le
  have hE : 0 ≤ phaseError S ε k := by unfold phaseError; positivity
  have hE0 : 1 / S ≤ phaseError S ε k := by unfold phaseError; linarith only [he1, he2, he3]
  have hE01 : 1 / S + S * ε ^ 2 ≤ phaseError S ε k := by unfold phaseError; linarith only [he2, he3]
  have hE2 : S / k ≤ phaseError S ε k := by unfold phaseError; linarith only [he0, he1, he3]
  have hE3 : ε * S ≤ phaseError S ε k := by unfold phaseError; linarith only [he0, he1, he2]
  have hcubes := inverse_cube_bounds hS
  have hround : |v| * (M * (1 / k)) ≤ M ^ 2 * phaseError S ε k := by
    calc
      _ ≤ (M * S) * (M * (1 / k)) := mul_le_mul_of_nonneg_right hv (by positivity)
      _ = M ^ 2 * (S / k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE2 (sq_nonneg M)
  have hbase : |v| * (2 * M * (M * (1 / S ^ 3 + ε ^ 2))) ≤ 2 * M ^ 3 * phaseError S ε k := by
    calc
      _ ≤ (M * S) * (2 * M * (M * (1 / S ^ 3 + ε ^ 2))) := mul_le_mul_of_nonneg_right hv (by
          positivity)
      _ = 2 * M ^ 3 * (S * (1 / S ^ 3) + S * ε ^ 2) := by ring
      _ ≤ 2 * M ^ 3 * (1 / S + S * ε ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hcubes.2 _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hE01 (by positivity)
  have hangle : M * (1 / k) ≤ M * phaseError S ε k := by
    apply mul_le_mul_of_nonneg_left _ hM0
    exact (div_le_div_of_nonneg_right hS hk.le).trans hE2
  have hdiam : M ^ 3 * (1 / S ^ 3) ≤ M ^ 3 * phaseError S ε k :=
    mul_le_mul_of_nonneg_left (hcubes.1.trans hE0) (pow_nonneg hM0 _)
  have htilt' : 2 * tilt ≤ 2 * M ^ 4 * phaseError S ε k := by
    calc
      _ ≤ 2 * (M ^ 4 / S) := mul_le_mul_of_nonneg_left htilt (by norm_num)
      _ = (2 * M ^ 4) * (1 / S) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE0 (by positivity)
  have haxial : |ε| * |v| * (3 * M ^ 2) ≤ 3 * M ^ 3 * phaseError S ε k := by
    rw [abs_of_nonneg hε]
    calc
      _ ≤ ε * (M * S) * (3 * M ^ 2) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv hε) (by positivity)
      _ = 3 * M ^ 3 * (ε * S) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE3 (by positivity)
  have h2 : M ≤ M ^ 2 := by nlinarith only [hM]
  have h3 : M ^ 2 ≤ M ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hM (sq_nonneg M)
    nlinarith only [h]
  have hcoeff : M ^ 2 + M ≤ 2 * M ^ 3 := by linarith only [h2, h3]
  have hlast := mul_le_mul_of_nonneg_right hcoeff hE
  unfold phaseConstant
  nlinarith only [hround, hbase, hangle, hdiam, htilt', haxial, hlast]

theorem phaseError_le_four_div {S ε k : ℝ} (hS : 0 < S)
    (hε2 : S ^ 2 * ε ^ 2 ≤ 1) (hk2 : S ^ 2 / k ≤ 1) (hε1 : ε * S ^ 2 ≤ 1) :
    phaseError S ε k ≤ 4 / S := by
  have h1 : S * ε ^ 2 ≤ 1 / S := (le_div_iff₀ hS).2 (by nlinarith only [hε2])
  have h2 : S / k ≤ 1 / S := (le_div_iff₀ hS).2 (by
    have heq : S / k * S = S ^ 2 / k := by ring
    rwa [heq])
  have h3 : ε * S ≤ 1 / S := (le_div_iff₀ hS).2 (by nlinarith only [hε1])
  unfold phaseError
  rw [show 4 / S = 4 * (1 / S) by ring]
  linarith only [h1, h2, h3]

/-- Normal velocity, given by `!₂[-(p * FR + pz * GR), 0, -ε * (p * FZ + pz * GZ)]`. -/
noncomputable def normalVelocity (ε p pz FR GR FZ GZ : ℝ) : Space :=
  !₂[-(p * FR + pz * GR), 0, -ε * (p * FZ + pz * GZ)]

/-- The slot derivative is estimated from its exact formula, independently of
the estimate for the normal itself. -/
theorem normalVelocity_bound {ε p pz FR GR FZ GZ slope error shear : ℝ}
    (herror : |p * FR + pz * GR - slope| ≤ error)
    (hshear : |p * FZ + pz * GZ| ≤ shear) :
    ‖normalVelocity ε p pz FR GR FZ GZ‖ ≤ |slope| + error + |ε| * shear := by
  have h := vec3_norm_le_sum (normalVelocity ε p pz FR GR FZ GZ)
  change ‖normalVelocity ε p pz FR GR FZ GZ‖ ≤
    |-(p * FR + pz * GR)| + |(0 : ℝ)| + |-ε * (p * FZ + pz * GZ)| at h
  simp only [abs_neg, abs_zero, add_zero, abs_mul] at h
  have hs : |p * FR + pz * GR| ≤ |slope| + error := by
    have ht := abs_add_le (p * FR + pz * GR - slope) slope
    rw [sub_add_cancel] at ht
    linarith only [ht, herror]
  have hz := mul_le_mul_of_nonneg_left hshear (abs_nonneg ε)
  linarith only [h, hs, hz]

theorem representative_slope_scaled {B sigma u L M S : ℝ}
    (hM : 0 ≤ M) (hB : |B| ≤ M) (hsigma : |sigma| = 1)
    (hu : |u| ≤ M) (hL : 1 / |L| ≤ M / S) :
    |-sigma * B * u / L| ≤ M ^ 3 / S := by
  rw [abs_div, abs_mul, abs_mul, abs_neg, hsigma, one_mul]
  calc
    _ = (|B| * |u|) * (1 / |L|) := by ring
    _ ≤ (M * M) * (M / S) := mul_le_mul
      (mul_le_mul hB hu (abs_nonneg _) hM) hL (one_div_nonneg.mpr (abs_nonneg _))
      (mul_nonneg hM hM)
    _ = _ := by ring

theorem velocity_error_scaled {M S ε k : ℝ}
    (hM : 1 ≤ M) (hS : 1 ≤ S) (hk : 0 < k) (hε : 0 ≤ ε) :
    M ^ 3 / S + (M * (1 / k) + 2 * M * (M * (1 / S ^ 3 + ε ^ 2))) +
      |ε| * (3 * M ^ 2) ≤ phaseConstant M * phaseError S ε k := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hE : 0 ≤ phaseError S ε k := by unfold phaseError; positivity
  have h0 : 1 / S ≤ phaseError S ε k := by
    unfold phaseError
    linarith only [mul_nonneg hS0.le (sq_nonneg ε), div_nonneg hS0.le hk.le, mul_nonneg hε hS0.le]
  have h1 : 1 / S + S * ε ^ 2 ≤ phaseError S ε k := by
    unfold phaseError
    linarith only [div_nonneg hS0.le hk.le, mul_nonneg hε hS0.le]
  have h2 : S / k ≤ phaseError S ε k := by
    unfold phaseError
    linarith only [one_div_nonneg.mpr hS0.le, mul_nonneg hS0.le (sq_nonneg ε), mul_nonneg hε hS0.le]
  have h3 : ε * S ≤ phaseError S ε k := by
    unfold phaseError
    linarith only [one_div_nonneg.mpr hS0.le, mul_nonneg hS0.le (sq_nonneg ε), div_nonneg hS0.le
        hk.le]
  have ha : M ^ 3 / S ≤ M ^ 3 * phaseError S ε k := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h0 (pow_nonneg hM0 3)
  have hb : M * (1 / k) ≤ M * phaseError S ε k :=
    mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right hS hk.le).trans h2) hM0
  have hc : 2 * M * (M * (1 / S ^ 3 + ε ^ 2)) ≤ 2 * M ^ 2 * phaseError S ε k := by
    have hh : 1 / S ^ 3 + ε ^ 2 ≤ phaseError S ε k :=
      (add_le_add (inverse_cube_bounds hS).1
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hS (sq_nonneg ε))).trans h1
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * M ^ 2 by positivity)
    nlinarith only [hh']
  have hd : |ε| * (3 * M ^ 2) ≤ 3 * M ^ 2 * phaseError S ε k := by
    rw [abs_of_nonneg hε]
    have hεle : ε ≤ ε * S := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hS hε
    have hh : ε ≤ phaseError S ε k := hεle.trans h3
    nlinarith only [mul_le_mul_of_nonneg_left hh (show 0 ≤ 3 * M ^ 2 by positivity)]
  have hm2 : M ≤ M ^ 2 := by nlinarith only [hM]
  have hm3 : M ^ 2 ≤ M ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_left hM (sq_nonneg M)]
  have hm4 : 0 ≤ M ^ 4 := pow_nonneg hM0 _
  have hcoeff : M ^ 3 + M + 5 * M ^ 2 ≤ phaseConstant M := by
    unfold phaseConstant
    linarith only [hm2, hm3, hm4, pow_nonneg hM0 3]
  nlinarith only [ha, hb, hc, hd, mul_le_mul_of_nonneg_right hcoeff hE]

/-- Quantitative estimates for the actual rounded phase.  The C2 comparison
lemma above supplies the two `M (S⁻³ + ε²)` derivative hypotheses. -/
theorem rounded_normal_estimates
    {ε target pz R R0 v FR GR FZ GZ FR0 GR0 B sigma u L M S k : ℝ} {K g : Plane}
    (hR : R ≠ 0) (hR0 : R0 ≠ 0) (hg : g ≠ 0) (horth : ⟪K, g⟫_ℝ = 0)
    (hgdef : g = !₂[R0 * FR0, GR0])
    (hfreq : (!₂[target / R0, pz] : Plane) = representativeFrequency B sigma u L K g)
    (hM : 1 ≤ M) (hS : 1 ≤ S) (hk : 1 ≤ k) (hε : 0 ≤ ε)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M) (hB : |B| ≤ M)
    (hsigma : |sigma| = 1) (hu : |u| ≤ M) (hgi : 1 / ‖g‖ ≤ M)
    (hL : 1 / |L| ≤ M / S) (hv : |v| ≤ M * S)
    (hRi : |1 / R| ≤ M) (hR0i : |1 / R0| ≤ M) (hRd : |R - R0| ≤ 1 / S ^ 3)
    (hFR : |FR| ≤ M) (hFZ : |FZ| ≤ M) (hGZ : |GZ| ≤ M)
    (hFR0 : |FR - FR0| ≤ M * (1 / S ^ 3 + ε ^ 2))
    (hGR0 : |GR - GR0| ≤ M * (1 / S ^ 3 + ε ^ 2)) :
    ‖explicitNormal ε (roundedFrequency k target) pz (sigma * B * u / 2) R v FR GR FZ GZ -
      referenceNormal B sigma u L v K‖ ≤ phaseConstant M * phaseError S ε k ∧
    ‖normalVelocity ε (roundedFrequency k target) pz FR GR FZ GZ‖ ≤
      phaseConstant M * phaseError S ε k := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hp := roundedFrequency_error hk0 target
  have hround : 1 / k ≤ 1 := (one_div_le_one_div_of_le zero_lt_one hk).trans_eq (one_div_one)
  have h := explicit_normal_estimate (ε := ε) (v := v) hR hR0 hg horth hgdef hfreq hM hround hp
    htarget hpz hRi hR0i hRd hFR hFZ hGZ hFR0 hGR0
  constructor
  · exact h.trans (assembled_error_scaled hM hS hk0 hε hv
      (representative_tilt_scaled hM0 hB hsigma hu hgi hL))
  · have hslope := representative_slope_coordinates hR0 hg horth hgdef hfreq
    have hrad := radial_frequency_error hp hFR htarget hpz hFR0 hGR0
    rw [hslope] at hrad
    have hz := axial_frequency_bound hM hround hp htarget hpz hFZ hGZ
    have hn := normalVelocity_bound (ε := ε) hrad hz
    have href := representative_slope_scaled hM0 hB hsigma hu hL
    exact (hn.trans (add_le_add_left (add_le_add_left href _) _)).trans
      (velocity_error_scaled hM hS hk0 hε)

/-! ## Quantitative lower bounds and the actual normalized frame -/

theorem tail_norm_le (n : Space) : ‖MovingFrameODE.tail n‖ ≤ ‖n‖ := by
  have h2 := ViscousPropagator.plane_norm_sq (MovingFrameODE.tail n)
  have h3 := PhaseCalculus.vec3_norm_sq n
  change ‖MovingFrameODE.tail n‖ ^ 2 = (n 1) ^ 2 + (n 2) ^ 2 at h2
  nlinarith only [h2, h3, sq_nonneg (n 0), norm_nonneg (MovingFrameODE.tail n), norm_nonneg n]

theorem normalScale_close {n : Space} {K : Plane} {B s δ : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1)
    (hclose : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ) :
    |MovingFrameODE.normalScale n - B| ≤ δ := by
  have ht := (tail_norm_le (n - MovingFrameODE.pack (B * s) (B • K))).trans hclose
  rw [MovingFrameODE.tail_sub, MovingFrameODE.tail_pack] at ht
  have h := (abs_norm_sub_norm_le (MovingFrameODE.tail n) (B • K)).trans ht
  simpa only [MovingFrameODE.normalScale, norm_smul, Real.norm_eq_abs,
    abs_of_pos hB, hK, mul_one] using h

/-- Closeness derived above controls the tangential normal as well as the full
normal; the weaker full-normal lower bound alone would not build the frame. -/
theorem normal_lower_bounds {n : Space} {K : Plane} {B s δ : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1) (hδ : δ ≤ B / 2)
    (hclose : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ) :
    B / 2 ≤ MovingFrameODE.normalScale n ∧ B / 2 ≤ ‖n‖ ∧
      MovingFrameODE.tail n ≠ 0 ∧ n ≠ 0 := by
  have hc := (abs_le.mp (normalScale_close hB hK hclose)).1
  have hlow : B / 2 ≤ MovingFrameODE.normalScale n := by linarith only [hc, hδ]
  have hnlow : B / 2 ≤ ‖n‖ := hlow.trans (tail_norm_le n)
  refine ⟨hlow, hnlow, ?_, ?_⟩
  · apply norm_pos_iff.mp
    exact lt_of_lt_of_le (half_pos hB) hlow
  · exact norm_pos_iff.mp (lt_of_lt_of_le (half_pos hB) hnlow)

theorem radialSlope_close {n : Space} {K : Plane} {B s δ : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1) (hδ : δ ≤ B / 2)
    (hclose : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ) :
    |MovingFrameODE.radialSlope n - s| ≤ 2 * (1 + |s|) * δ / B := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hclose
  obtain ⟨hlow, _, hne, _⟩ := normal_lower_bounds hB hK hδ hclose
  have hβ : 0 < MovingFrameODE.normalScale n := MovingFrameODE.normalScale_pos hne
  have hscale := normalScale_close hB hK hclose
  have hr := (PiLp.norm_apply_le (n - MovingFrameODE.pack (B * s) (B • K)) 0).trans hclose
  change |n 0 - B * s| ≤ δ at hr
  have heq : MovingFrameODE.radialSlope n - s =
      ((n 0 - B * s) + s * (B - MovingFrameODE.normalScale n)) / MovingFrameODE.normalScale n := by
    unfold MovingFrameODE.radialSlope
    field_simp; ring
  rw [heq, abs_div, abs_of_pos hβ]
  have hnum : |(n 0 - B * s) + s * (B - MovingFrameODE.normalScale n)| ≤ δ + |s| * δ := by
    calc
      _ ≤ |n 0 - B * s| + |s * (B - MovingFrameODE.normalScale n)| := abs_add_le _ _
      _ = |n 0 - B * s| + |s| * |MovingFrameODE.normalScale n - B| := by
        rw [abs_mul, abs_sub_comm B]
      _ ≤ _ := add_le_add hr (mul_le_mul_of_nonneg_left hscale (abs_nonneg _))
  calc
    _ ≤ (δ + |s| * δ) / MovingFrameODE.normalScale n := div_le_div_of_nonneg_right hnum hβ.le
    _ ≤ (δ + |s| * δ) / (B / 2) := div_le_div_of_nonneg_left (by positivity) (half_pos hB) hlow
    _ = _ := by ring

theorem normalDirection_close {n : Space} {K : Plane} {B s δ : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1) (hδ : δ ≤ B / 2)
    (hclose : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ) :
    ‖MovingFrameODE.normalDirection n - K‖ ≤ 4 * δ / B := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hclose
  obtain ⟨hlow, _, hne, _⟩ := normal_lower_bounds hB hK hδ hclose
  have hβ : 0 < MovingFrameODE.normalScale n := MovingFrameODE.normalScale_pos hne
  have ht := (tail_norm_le (n - MovingFrameODE.pack (B * s) (B • K))).trans hclose
  rw [MovingFrameODE.tail_sub, MovingFrameODE.tail_pack] at ht
  have hc := normalScale_close hB hK hclose
  have heq : MovingFrameODE.normalDirection n - K =
      (MovingFrameODE.normalScale n)⁻¹ • (MovingFrameODE.tail n - B • K) +
      ((B - MovingFrameODE.normalScale n) / MovingFrameODE.normalScale n) • K := by
    unfold MovingFrameODE.normalDirection
    ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp; ring
  rw [heq]
  have hn := norm_add_le ((MovingFrameODE.normalScale n)⁻¹ • (MovingFrameODE.tail n - B • K))
    (((B - MovingFrameODE.normalScale n) / MovingFrameODE.normalScale n) • K)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hβ), hK, mul_one, abs_div, abs_of_pos hβ,
    abs_sub_comm B] at hn
  have h1 := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hβ.le)
  have h2 := div_le_div_of_nonneg_right hc hβ.le
  have hsum : ‖(MovingFrameODE.normalScale n)⁻¹ • (MovingFrameODE.tail n - B • K) +
      ((B - MovingFrameODE.normalScale n) / MovingFrameODE.normalScale n) • K‖ ≤
      2 * δ / MovingFrameODE.normalScale n := by
    calc
      _ ≤ (MovingFrameODE.normalScale n)⁻¹ * δ + δ / MovingFrameODE.normalScale n :=
        hn.trans (add_le_add h1 h2)
      _ = _ := by ring
  calc
    _ ≤ 2 * δ / MovingFrameODE.normalScale n := hsum
    _ ≤ 2 * δ / (B / 2) := div_le_div_of_nonneg_left (by positivity) (half_pos hB) hlow
    _ = _ := by ring

theorem quarterTurn_norm (w : Plane) : ‖MovingFrameODE.quarterTurn w‖ = ‖w‖ := by
  have h := MovingFrameODE.quarterTurn_inner w w
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith only [h, norm_nonneg w, norm_nonneg (MovingFrameODE.quarterTurn w)]

theorem transverseDirection_close {n : Space} {K : Plane} {B s δ : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1) (hδ : δ ≤ B / 2)
    (hclose : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ) :
    ‖MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection n) - MovingFrameODE.quarterTurn K‖ ≤
      4 * δ / B := by
  rw [← map_sub, quarterTurn_norm]
  exact normalDirection_close hB hK hδ hclose

/-- Scale derivative, given by `⟪MovingFrameODE.tail n, MovingFrameODE.tail n'⟫_ℝ /
MovingFrameODE.normalScale n`. -/
noncomputable def scaleDerivative (n n' : Space) : ℝ :=
  ⟪MovingFrameODE.tail n, MovingFrameODE.tail n'⟫_ℝ / MovingFrameODE.normalScale n

/-- Slope derivative, given by `(n' 0 - MovingFrameODE.radialSlope n * scaleDerivative n n') /
MovingFrameODE.normalScale n`. -/
noncomputable def slopeDerivative (n n' : Space) : ℝ :=
  (n' 0 - MovingFrameODE.radialSlope n * scaleDerivative n n') / MovingFrameODE.normalScale n

/-- Direction derivative, given by `(MovingFrameODE.normalScale n)⁻¹ • (MovingFrameODE.tail n' -
scaleDerivative n n' • MovingFrameODE.normalDirection n)`. -/
noncomputable def directionDerivative (n n' : Space) : Plane :=
  (MovingFrameODE.normalScale n)⁻¹ •
    (MovingFrameODE.tail n' - scaleDerivative n n' • MovingFrameODE.normalDirection n)

/-- Angular velocity, given by `⟪MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection n),
directionDerivative n n'⟫_ℝ`. -/
noncomputable def angularVelocity (n n' : Space) : ℝ :=
  ⟪MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection n), directionDerivative n n'⟫_ℝ

theorem hasDerivAt_normalScale {n : ℝ → Space} {n' : Space} {v : ℝ}
    (hn : HasDerivAt n n' v) (hne : MovingFrameODE.tail (n v) ≠ 0) :
    HasDerivAt (fun s => MovingFrameODE.normalScale (n s)) (scaleDerivative (n v) n') v := by
  have ht : HasDerivAt (fun s => MovingFrameODE.tail (n s)) (MovingFrameODE.tail n') v :=
    MovingFrameODE.tailCLM.hasFDerivAt.comp_hasDerivAt v hn
  have h := ht.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  simpa only [MovingFrameODE.normalScale, scaleDerivative, Real.sqrt_sq_eq_abs, abs_norm,
    mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)] using h

theorem hasDerivAt_radialSlope {n : ℝ → Space} {n' : Space} {v : ℝ}
    (hn : HasDerivAt n n' v) (hne : MovingFrameODE.tail (n v) ≠ 0) :
    HasDerivAt (fun s => MovingFrameODE.radialSlope (n s)) (slopeDerivative (n v) n') v := by
  have hβ := MovingFrameODE.normalScale_pos hne
  let pr : Space →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0
  have hr : HasDerivAt (fun s => (n s) 0) (n' 0) v :=
    pr.hasFDerivAt.comp_hasDerivAt v hn
  have heq : slopeDerivative (n v) n' =
      (n' 0 * MovingFrameODE.normalScale (n v) - (n v) 0 * scaleDerivative (n v) n') /
        MovingFrameODE.normalScale (n v) ^ 2 := by
    unfold slopeDerivative MovingFrameODE.radialSlope
    field_simp [hβ.ne']
  rw [heq]
  exact hr.div (hasDerivAt_normalScale hn hne) hβ.ne'

theorem hasDerivAt_normalDirection {n : ℝ → Space} {n' : Space} {v : ℝ}
    (hn : HasDerivAt n n' v) (hne : MovingFrameODE.tail (n v) ≠ 0) :
    HasDerivAt (fun s => MovingFrameODE.normalDirection (n s)) (directionDerivative (n v) n') v :=
        by
  have hβ := MovingFrameODE.normalScale_pos hne
  have ht : HasDerivAt (fun s => MovingFrameODE.tail (n s)) (MovingFrameODE.tail n') v :=
    MovingFrameODE.tailCLM.hasFDerivAt.comp_hasDerivAt v hn
  convert! ((hasDerivAt_normalScale hn hne).fun_inv hβ.ne').smul ht using 1
  unfold directionDerivative MovingFrameODE.normalDirection
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hβ.ne']; ring

/-- The angular speed is computed from the actual normal derivative. -/
theorem hasDerivAt_actual_frame {n : ℝ → Space} {n' : Space} {v : ℝ}
    (hn : HasDerivAt n n' v) (hne : MovingFrameODE.tail (n v) ≠ 0) :
    HasDerivAt (fun s => MovingFrameODE.normalDirection (n s))
      (angularVelocity (n v) n' • MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (n
          v))) v ∧
    HasDerivAt (fun s => MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (n s)))
      (-angularVelocity (n v) n' • MovingFrameODE.normalDirection (n v)) v := by
  have ht : HasDerivAt (fun s => MovingFrameODE.tail (n s)) (MovingFrameODE.tail n') v :=
    MovingFrameODE.tailCLM.hasFDerivAt.comp_hasDerivAt v hn
  have hunit : ∀ᶠ s in nhds v, ‖MovingFrameODE.normalDirection (n s)‖ = 1 := by
    have he : ∀ᶠ s in nhds v, MovingFrameODE.tail (n s) ≠ 0 := ht.continuousAt.eventually_ne hne
    filter_upwards [he] with s hs
    exact MovingFrameODE.normalDirection_unit hs
  have hd := hasDerivAt_normalDirection hn hne
  have hrot := MovingFrameODE.unit_curve_rotation hd hunit
  have hk : HasDerivAt (fun s => MovingFrameODE.normalDirection (n s))
      (angularVelocity (n v) n' • MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (n
          v))) v :=
    hrot ▸ hd
  exact ⟨hk, MovingFrameODE.hasDerivAt_quarterTurn_of_rotation hk⟩

theorem scaleDerivative_bound {n n' : Space} (hne : MovingFrameODE.tail n ≠ 0) :
    |scaleDerivative n n'| ≤ ‖n'‖ := by
  have hβ := MovingFrameODE.normalScale_pos hne
  unfold scaleDerivative
  rw [abs_div, abs_of_pos hβ]
  calc
    _ ≤ (‖MovingFrameODE.tail n‖ * ‖MovingFrameODE.tail n'‖) / MovingFrameODE.normalScale n :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) hβ.le
    _ = ‖MovingFrameODE.tail n'‖ := by
      change (MovingFrameODE.normalScale n * ‖MovingFrameODE.tail n'‖) / MovingFrameODE.normalScale
          n = _
      exact mul_div_cancel_left₀ _ hβ.ne'
    _ ≤ ‖n'‖ := tail_norm_le n'

theorem slopeDerivative_bound {n n' : Space} {B η : ℝ}
    (hB : 0 < B) (hlow : B / 2 ≤ MovingFrameODE.normalScale n) (hn' : ‖n'‖ ≤ η) :
    |slopeDerivative n n'| ≤ 2 * (1 + |MovingFrameODE.radialSlope n|) * η / B := by
  have hβ : 0 < MovingFrameODE.normalScale n := lt_of_lt_of_le (half_pos hB) hlow
  have hne : MovingFrameODE.tail n ≠ 0 := norm_pos_iff.mp hβ
  have hη : 0 ≤ η := (norm_nonneg _).trans hn'
  have hr : |n' 0| ≤ η := by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le n' 0).trans hn'
  have hb : |scaleDerivative n n'| ≤ η := (scaleDerivative_bound hne).trans hn'
  unfold slopeDerivative
  rw [abs_div, abs_of_pos hβ]
  calc
    _ ≤ (|n' 0| + |MovingFrameODE.radialSlope n * scaleDerivative n n'|) /
        MovingFrameODE.normalScale n :=
      div_le_div_of_nonneg_right (abs_sub _ _) hβ.le
    _ ≤ (η + |MovingFrameODE.radialSlope n| * η) / MovingFrameODE.normalScale n := by
      rw [abs_mul]
      exact div_le_div_of_nonneg_right
        (add_le_add hr (mul_le_mul_of_nonneg_left hb (abs_nonneg _))) hβ.le
    _ ≤ (η + |MovingFrameODE.radialSlope n| * η) / (B / 2) :=
      div_le_div_of_nonneg_left (by positivity) (half_pos hB) hlow
    _ = _ := by ring

theorem directionDerivative_bound {n n' : Space} {B η : ℝ}
    (hB : 0 < B) (hlow : B / 2 ≤ MovingFrameODE.normalScale n) (hn' : ‖n'‖ ≤ η) :
    ‖directionDerivative n n'‖ ≤ 4 * η / B := by
  have hβ : 0 < MovingFrameODE.normalScale n := lt_of_lt_of_le (half_pos hB) hlow
  have hne : MovingFrameODE.tail n ≠ 0 := norm_pos_iff.mp hβ
  have hη : 0 ≤ η := (norm_nonneg _).trans hn'
  have hb : |scaleDerivative n n'| ≤ η := (scaleDerivative_bound hne).trans hn'
  have ht : ‖MovingFrameODE.tail n'‖ ≤ η := (tail_norm_le n').trans hn'
  have hs : ‖MovingFrameODE.tail n' - scaleDerivative n n' • MovingFrameODE.normalDirection n‖ ≤ 2
      * η := by
    have h := norm_sub_le (MovingFrameODE.tail n') (scaleDerivative n n' •
        MovingFrameODE.normalDirection n)
    rw [norm_smul, Real.norm_eq_abs, MovingFrameODE.normalDirection_unit hne, mul_one] at h
    linarith only [h, hb, ht]
  unfold directionDerivative
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ)]
  calc
    _ ≤ (MovingFrameODE.normalScale n)⁻¹ * (2 * η) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr
        hβ.le)
    _ = 2 * η / MovingFrameODE.normalScale n := by ring
    _ ≤ 2 * η / (B / 2) := div_le_div_of_nonneg_left (by positivity) (half_pos hB) hlow
    _ = _ := by ring

theorem angularVelocity_bound {n n' : Space} {B η : ℝ}
    (hB : 0 < B) (hlow : B / 2 ≤ MovingFrameODE.normalScale n) (hn' : ‖n'‖ ≤ η) :
    |angularVelocity n n'| ≤ 4 * η / B := by
  have hβ : 0 < MovingFrameODE.normalScale n := lt_of_lt_of_le (half_pos hB) hlow
  have hne : MovingFrameODE.tail n ≠ 0 := norm_pos_iff.mp hβ
  unfold angularVelocity
  have h := abs_real_inner_le_norm
    (MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection n)) (directionDerivative n n')
  rw [quarterTurn_norm, MovingFrameODE.normalDirection_unit hne, one_mul] at h
  exact h.trans (directionDerivative_bound hB hlow hn')

/-! ## The actual local base hypotheses -/

/-- Local C1/C2 bounds on the given base and its order-zero limit.  These are
derivative bounds on actual functions, not a normal-comparison hypothesis. -/
structure LocalBaseBounds (F G F0 G0 : Slow → ℝ) (U : Set Slow) (M ε : ℝ) : Prop where
  convex : Convex ℝ U
  actualF : ∀ x ∈ U, DifferentiableAt ℝ F x
  actualG : ∀ x ∈ U, DifferentiableAt ℝ G x
  referenceF : ∀ x ∈ U, DifferentiableAt ℝ F0 x
  referenceG : ∀ x ∈ U, DifferentiableAt ℝ G0 x
  secondF : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ F0) x
  secondG : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ G0) x
  secondF_bound : ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ F0) x‖ ≤ M
  secondG_bound : ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ G0) x‖ ≤ M
  firstF_bound : ∀ x ∈ U, ‖fderiv ℝ F0 x‖ ≤ M
  valueF_error : ∀ x ∈ U, |F x - F0 x| ≤ M * ε ^ 2
  firstF_error : ∀ x ∈ U, ‖fderiv ℝ F x - fderiv ℝ F0 x‖ ≤ M * ε ^ 2
  firstG_error : ∀ x ∈ U, ‖fderiv ℝ G x - fderiv ℝ G0 x‖ ≤ M * ε ^ 2
  radialF_bound : ∀ x ∈ U, |PhaseCalculus.slowR F x| ≤ M
  axialF_bound : ∀ x ∈ U, |PhaseCalculus.slowZ F x| ≤ M
  axialG_bound : ∀ x ∈ U, |PhaseCalculus.slowZ G x| ≤ M

theorem localBase_derivative_errors {F G F0 G0 : Slow → ℝ} {U : Set Slow}
    {M ε diameter : ℝ} {q q0 : Slow} (h : LocalBaseBounds F G F0 G0 U M ε)
    (hM : 0 ≤ M) (hq : q ∈ U) (hq0 : q0 ∈ U) (hd : ‖q - q0‖ ≤ diameter) :
    |PhaseCalculus.slowR F q - PhaseCalculus.slowR F0 q0| ≤ M * (diameter + ε ^ 2) ∧
    |PhaseCalculus.slowR G q - PhaseCalculus.slowR G0 q0| ≤ M * (diameter + ε ^ 2) := by
  have he : ‖((1, (0, 0)) : Slow)‖ ≤ 1 := by norm_num
  have hF := local_directional_derivative_close hM h.convex hq hq0 h.secondF h.secondF_bound
    hd (h.firstF_error q hq) he
  have hG := local_directional_derivative_close hM h.convex hq hq0 h.secondG h.secondG_bound
    hd (h.firstG_error q hq) he
  simpa only [PhaseCalculus.slowR, mul_add] using And.intro hF hG

theorem localBase_value_error {F G F0 G0 : Slow → ℝ} {U : Set Slow}
    {M ε diameter : ℝ} {q q0 : Slow} (h : LocalBaseBounds F G F0 G0 U M ε)
    (hM : 0 ≤ M) (hq : q ∈ U) (hq0 : q0 ∈ U) (hd : ‖q - q0‖ ≤ diameter) :
    |F q - F0 q0| ≤ M * (diameter + ε ^ 2) := by
  have hlocal := h.convex.norm_image_sub_le_of_norm_fderiv_le h.referenceF h.firstF_bound hq0 hq
  have hloc : |F0 q - F0 q0| ≤ M * diameter := by
    simpa only [Real.norm_eq_abs] using hlocal.trans (mul_le_mul_of_nonneg_left hd hM)
  calc
    _ ≤ |F q - F0 q| + |F0 q - F0 q0| := abs_sub_le _ _ _
    _ ≤ M * ε ^ 2 + M * diameter := add_le_add (h.valueF_error q hq) hloc
    _ = _ := by ring

theorem radius_difference_le {q q0 : Slow} {diameter : ℝ} (hd : ‖q - q0‖ ≤ diameter) :
    |q.1 - q0.1| ≤ diameter := by
  simpa only [Prod.fst_sub, Real.norm_eq_abs] using (norm_fst_le (q - q0)).trans hd

/-- Shear vector, given by `!₂[q.1 * PhaseCalculus.slowR F q, PhaseCalculus.slowR G q]`. -/
noncomputable def shearVector (F G : Slow → ℝ) (q : Slow) : Plane :=
  !₂[q.1 * PhaseCalculus.slowR F q, PhaseCalculus.slowR G q]

theorem localBase_shear_error {F G F0 G0 : Slow → ℝ} {U : Set Slow}
    {M ε diameter : ℝ} {q q0 : Slow} (h : LocalBaseBounds F G F0 G0 U M ε)
    (hM : 1 ≤ M) (hq : q ∈ U) (hq0 : q0 ∈ U) (hd : ‖q - q0‖ ≤ diameter)
    (hR0 : |q0.1| ≤ M) :
    ‖shearVector F G q - shearVector F0 G0 q0‖ ≤ 4 * M ^ 2 * (diameter + ε ^ 2) := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hd0 : 0 ≤ diameter := (norm_nonneg _).trans hd
  obtain ⟨hF, hG⟩ := localBase_derivative_errors h hM0 hq hq0 hd
  have hR := radius_difference_le hd
  have ha : |q.1 * PhaseCalculus.slowR F q - q0.1 * PhaseCalculus.slowR F0 q0| ≤
      M * diameter + M ^ 2 * (diameter + ε ^ 2) := by
    calc
      _ = |(q.1 - q0.1) * PhaseCalculus.slowR F q +
          q0.1 * (PhaseCalculus.slowR F q - PhaseCalculus.slowR F0 q0)| := by congr 1; ring
      _ ≤ |(q.1 - q0.1) * PhaseCalculus.slowR F q| +
          |q0.1 * (PhaseCalculus.slowR F q - PhaseCalculus.slowR F0 q0)| := abs_add_le _ _
      _ = |q.1 - q0.1| * |PhaseCalculus.slowR F q| +
          |q0.1| * |PhaseCalculus.slowR F q - PhaseCalculus.slowR F0 q0| := by rw [abs_mul, abs_mul]
      _ ≤ diameter * M + M * (M * (diameter + ε ^ 2)) := add_le_add
        (mul_le_mul hR (h.radialF_bound q hq) (abs_nonneg _) hd0)
        (mul_le_mul hR0 hF (abs_nonneg _) hM0)
      _ = _ := by ring
  have hn := MovingFrameODE.plane_norm_le_coordinate_sum (shearVector F G q - shearVector F0 G0 q0)
  change ‖shearVector F G q - shearVector F0 G0 q0‖ ≤
    |q.1 * PhaseCalculus.slowR F q - q0.1 * PhaseCalculus.slowR F0 q0| +
    |PhaseCalculus.slowR G q - PhaseCalculus.slowR G0 q0| at hn
  have hm2 : M ≤ M ^ 2 := by nlinarith only [hM]
  have he0 : 0 ≤ diameter + ε ^ 2 := add_nonneg hd0 (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hm2 he0
  have hd' : M * diameter ≤ M * (diameter + ε ^ 2) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) hM0
  nlinarith only [hn, ha, hG, hh, hd', mul_nonneg (sq_nonneg M) he0]

/-- The principal estimate stated for the actual PhaseCalculus normal, with
local C1/C2 hypotheses and the actual punctured-lattice rounded frequency. -/
theorem actual_phase_estimates
    {F G F0 G0 : Slow → ℝ} {U : Set Slow} {q q0 : Slow}
    {ε target pz v θ B sigma u L M S k : ℝ} {K : Plane}
    (hbase : LocalBaseBounds F G F0 G0 U M ε)
    (hq : q ∈ U) (hq0 : q0 ∈ U) (hdiameter : ‖q - q0‖ ≤ 1 / S ^ 3)
    (hR : q.1 ≠ 0) (hR0 : q0.1 ≠ 0)
    (hg : shearVector F0 G0 q0 ≠ 0) (horth : ⟪K, shearVector F0 G0 q0⟫_ℝ = 0)
    (hfreq : (!₂[target / q0.1, pz] : Plane) =
      representativeFrequency B sigma u L K (shearVector F0 G0 q0))
    (hM : 1 ≤ M) (hS : 1 ≤ S) (hk : 1 ≤ k) (hε : 0 < ε)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M) (hB : |B| ≤ M)
    (hsigma : |sigma| = 1) (hu : |u| ≤ M) (hgi : 1 / ‖shearVector F0 G0 q0‖ ≤ M)
    (hL : 1 / |L| ≤ M / S) (hv : |v| ≤ M * S)
    (hRi : |1 / q.1| ≤ M) (hR0i : |1 / q0.1| ≤ M) :
    ‖PhaseCalculus.phaseNormal ε (roundedFrequency k target) pz (sigma * B * u / 2) F G (q, (θ, v))
        -
      referenceNormal B sigma u L v K‖ ≤ phaseConstant M * phaseError S ε k ∧
    ‖PhaseCalculus.normalSlotDerivative ε (roundedFrequency k target) pz F G q‖ ≤
      phaseConstant M * phaseError S ε k := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  obtain ⟨hFR, hGR⟩ := localBase_derivative_errors hbase hM0 hq hq0 hdiameter
  have h := rounded_normal_estimates hR hR0 hg horth (rfl : shearVector F0 G0 q0 = _)
    hfreq hM hS hk hε.le htarget hpz hB hsigma hu hgi hL hv hRi hR0i
    (radius_difference_le hdiameter) (hbase.radialF_bound q hq) (hbase.axialF_bound q hq)
    (hbase.axialG_bound q hq) hFR hGR
  rw [phaseNormal_eq_explicit ε (roundedFrequency k target) pz (sigma * B * u / 2)
    F G (q, (θ, v)) hε.ne' (hbase.actualF q hq) (hbase.actualG q hq)]
  exact h

/-- Punctured-lattice rounding itself already excludes exact zeros of the
tangential normal; the comparison estimate supplies the uniform lower bound. -/
theorem phase_normal_nonvanishing {ε k target pz x0 : ℝ} {F G : Slow → ℝ}
    {q : PhaseCalculus.Slot} (hε : ε ≠ 0) (hk : k ≠ 0) (hR : q.1.1 ≠ 0)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    MovingFrameODE.tail (PhaseCalculus.phaseNormal ε (roundedFrequency k target) pz x0 F G q) ≠ 0 ∧
    PhaseCalculus.phaseNormal ε (roundedFrequency k target) pz x0 F G q ≠ 0 := by
  rw [phaseNormal_eq_explicit ε (roundedFrequency k target) pz x0 F G q hε hF hG]
  have hp := div_ne_zero (roundedFrequency_ne_zero hk target) hR
  constructor
  · intro hz
    have h := congrArg (fun w : Plane => w 0) hz
    exact hp h
  · intro hz
    have h := congrArg (fun w : Space => w 1) hz
    exact hp h

/-- The phase's actual derivative, uniform lower bounds and every changing
frame quantity needed in `MovingFrameODE`, from local base and band data. -/
theorem actual_phase_geometry
    {F G F0 G0 : Slow → ℝ} {U : Set Slow} {q q0 : Slow}
    {ε target pz v θ B sigma u L M S k : ℝ} {K : Plane}
    (hbase : LocalBaseBounds F G F0 G0 U M ε)
    (hq : q ∈ U) (hq0 : q0 ∈ U) (hdiameter : ‖q - q0‖ ≤ 1 / S ^ 3)
    (hR : q.1 ≠ 0) (hR0 : q0.1 ≠ 0)
    (hg : shearVector F0 G0 q0 ≠ 0) (horth : ⟪K, shearVector F0 G0 q0⟫_ℝ = 0)
    (hfreq : (!₂[target / q0.1, pz] : Plane) =
      representativeFrequency B sigma u L K (shearVector F0 G0 q0))
    (hM : 1 ≤ M) (hS : 1 ≤ S) (hk : 1 ≤ k) (hε : 0 < ε)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M) (hB : |B| ≤ M)
    (hsigma : |sigma| = 1) (hu : |u| ≤ M) (hgi : 1 / ‖shearVector F0 G0 q0‖ ≤ M)
    (hL : 1 / |L| ≤ M / S) (hv : |v| ≤ M * S)
    (hRi : |1 / q.1| ≤ M) (hR0i : |1 / q0.1| ≤ M)
    (hBpos : 0 < B) (hK : ‖K‖ = 1)
    (hsmall : phaseConstant M * phaseError S ε k ≤ B / 2) :
    let N : ℝ → Space := fun w => PhaseCalculus.phaseNormal ε (roundedFrequency k target) pz
      (sigma * B * u / 2) F G (q, (θ, w))
    let n' := PhaseCalculus.normalSlotDerivative ε (roundedFrequency k target) pz F G q
    let δ := phaseConstant M * phaseError S ε k
    HasDerivAt N n' v ∧
    B / 2 ≤ MovingFrameODE.normalScale (N v) ∧ B / 2 ≤ ‖N v‖ ∧
    MovingFrameODE.tail (N v) ≠ 0 ∧ N v ≠ 0 ∧
    |MovingFrameODE.radialSlope (N v) - signedSlot sigma u L v| ≤
      2 * (1 + |signedSlot sigma u L v|) * δ / B ∧
    ‖MovingFrameODE.normalDirection (N v) - K‖ ≤ 4 * δ / B ∧
    ‖MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (N v)) - MovingFrameODE.quarterTurn
        K‖ ≤
      4 * δ / B ∧
    |slopeDerivative (N v) n'| ≤ 2 * (1 + |MovingFrameODE.radialSlope (N v)|) * δ / B ∧
    |angularVelocity (N v) n'| ≤ 4 * δ / B := by
  dsimp only
  obtain ⟨hc, hd⟩ := actual_phase_estimates (v := v) (θ := θ) hbase hq hq0 hdiameter
    hR hR0 hg horth hfreq hM hS hk hε htarget hpz hB hsigma hu hgi hL hv hRi hR0i
  have hl := normal_lower_bounds (s := signedSlot sigma u L v) hBpos hK hsmall hc
  refine ⟨?_, hl.1, hl.2.1, hl.2.2.1, hl.2.2.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact PhaseCalculus.hasDerivAt_phaseNormal_slot ε (roundedFrequency k target) pz
      (sigma * B * u / 2) θ v F G q hε.ne' (hbase.actualF q hq) (hbase.actualG q hq)
  · exact radialSlope_close hBpos hK hsmall hc
  · exact normalDirection_close hBpos hK hsmall hc
  · exact transverseDirection_close hBpos hK hsmall hc
  · exact slopeDerivative_bound hBpos hl.1 hd
  · exact angularVelocity_bound hBpos hl.1 hd

theorem signedSlot_bound {sigma u L v : ℝ}
    (hsigma : |sigma| = 1) (hu : 0 ≤ u) (hL : 0 < L) (hv : 0 ≤ v) (hvL : v ≤ L) :
    |signedSlot sigma u L v| ≤ 3 * u / 2 := by
  have hvdiv : v / L ≤ 1 := (div_le_one hL).2 hvL
  have hnonneg : 0 ≤ u / 2 + u * v / L := by positivity
  unfold signedSlot
  rw [abs_mul, hsigma, one_mul, abs_of_nonneg hnonneg]
  have h := mul_le_mul_of_nonneg_left hvdiv hu
  simp only [mul_one] at h
  rw [mul_div_assoc]
  nlinarith only [h]

theorem radialSlope_uniform_bound {n : Space} {K : Plane} {B s δ A : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1) (hδ : δ ≤ B / 2)
    (hclose : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ) (hs : |s| ≤ A) :
    |MovingFrameODE.radialSlope n| ≤ 1 + 2 * A := by
  have hc := radialSlope_close hB hK hδ hclose
  have hscale : 2 * (1 + |s|) * δ / B ≤ 1 + |s| := by
    apply (div_le_iff₀ hB).2
    have h := mul_le_mul_of_nonneg_left hδ (show 0 ≤ 2 * (1 + |s|) by positivity)
    nlinarith only [h]
  have h := abs_add_le (MovingFrameODE.radialSlope n - s) s
  rw [sub_add_cancel] at h
  linarith only [hc, hscale, h, hs]

/-- The representative frequencies are bounded uniformly before rounding;
the bound follows from the specified frequency formula. -/
theorem representative_uniform_frequency_bounds
    {B sigma u L M S R0 target pz : ℝ} {K g : Plane}
    (hR0 : R0 ≠ 0) (hM : 0 ≤ M) (hS : 1 ≤ S)
    (hB : |B| ≤ M) (hsigma : |sigma| = 1) (hu : |u| ≤ M)
    (hg : 1 / ‖g‖ ≤ M) (hL : 1 / |L| ≤ M / S) (hK : ‖K‖ = 1)
    (hRbound : |R0| ≤ M)
    (hfreq : (!₂[target / R0, pz] : Plane) = representativeFrequency B sigma u L K g) :
    |target| ≤ M * (M + M ^ 4) ∧ |pz| ≤ M + M ^ 4 := by
  have htilt := representative_tilt_scaled hM hB hsigma hu hg hL
  have hinv : M ^ 4 / S ≤ M ^ 4 :=
    (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hS)).2 (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hS (pow_nonneg hM 4))
  have hf : ‖representativeFrequency B sigma u L K g‖ ≤ M + M ^ 4 := by
    exact (representative_frequency_bound B sigma u L K g hK).trans
      (add_le_add hB (htilt.trans hinv))
  have h0 := (PiLp.norm_apply_le (representativeFrequency B sigma u L K g) 0).trans hf
  have h1 := (PiLp.norm_apply_le (representativeFrequency B sigma u L K g) 1).trans hf
  rw [← hfreq] at h0 h1
  have htarget : |target / R0| ≤ M + M ^ 4 := by simpa [abs_div] using h0
  constructor
  · have heq : target = R0 * (target / R0) := by field_simp
    calc
      |target| = |R0| * |target / R0| := by nth_rw 1 [heq]; rw [abs_mul]
      _ ≤ M * (M + M ^ 4) := mul_le_mul hRbound htarget (abs_nonneg _) hM
  · simpa using h1

theorem chart_carrier_ge_one (h : ℝ) (n : ℕ) : 1 ≤ (ChartScales.carrier h n : ℝ) := by
  have hk : 0 < (ChartScales.carrier h n : ℝ) :=
    Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h n)
  have hn : 0 < ChartScales.carrier h n := by exact_mod_cast hk
  exact_mod_cast Nat.succ_le_of_lt hn

theorem chart_S_tendsto_atTop : Tendsto ChartScales.S atTop atTop := by
  exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The band conditions used in the finite estimate hold on the actual
dyadic scale and actual ceiling-rounded carrier. -/
theorem eventually_band_conditions (h : ℝ) (hh : 0 < h) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ ChartScales.S n ∧
      ChartScales.S n ^ 2 * ChartScales.epsilon h n ^ 2 ≤ 1 ∧
      ChartScales.S n ^ 2 / (ChartScales.carrier h n : ℝ) ≤ 1 ∧
      ChartScales.epsilon h n * ChartScales.S n ^ 2 ≤ 1 := by
  have hS := chart_S_tendsto_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have h2 := ChartScales.eventually_slow_power_epsilon_lt h hh 2 2 1 (by norm_num) (by norm_num)
  have h1 := ChartScales.eventually_slow_power_epsilon_lt h hh 2 1 1 (by norm_num) (by norm_num)
  have hk := (tendsto_order.1 (ChartScales.slow_power_div_carrier_tendsto_zero h hh 2)).2 1 (by
      norm_num)
  filter_upwards [hS, h2, hk, h1] with n hn hn2 hnk hn1
  refine ⟨hn, ?_, ?_, ?_⟩
  · simpa only [Real.rpow_two] using hn2.le
  · simpa only [Real.rpow_two] using hnk.le
  · simpa only [Real.rpow_two, Real.rpow_one, mul_comm] using hn1.le

theorem eventually_phaseError_le (h : ℝ) (hh : 0 < h) :
    ∀ᶠ n : ℕ in atTop,
      phaseError (ChartScales.S n) (ChartScales.epsilon h n) (ChartScales.carrier h n) ≤
        4 / ChartScales.S n := by
  filter_upwards [eventually_band_conditions h hh] with n hn
  exact phaseError_le_four_div (lt_of_lt_of_le zero_lt_one hn.1) hn.2.1 hn.2.2.1 hn.2.2.2

/-- Any fixed positive representative lower bound eventually dominates the
derived normal error.  This is a cutoff conclusion, not an assumed comparison. -/
theorem eventually_error_small (h : ℝ) (hh : 0 < h) {C B : ℝ} (hC : 0 ≤ C) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop,
      C * phaseError (ChartScales.S n) (ChartScales.epsilon h n) (ChartScales.carrier h n) ≤ B / 2
          := by
  have hS := chart_S_tendsto_atTop.eventually (eventually_ge_atTop (max 1 (8 * C / B)))
  filter_upwards [hS, eventually_phaseError_le h hh] with n hn he
  have hS1 : 1 ≤ ChartScales.S n := (le_max_left _ _).trans hn
  have hS0 : 0 < ChartScales.S n := lt_of_lt_of_le zero_lt_one hS1
  have hthreshold : 8 * C / B ≤ ChartScales.S n := (le_max_right _ _).trans hn
  have hb := (div_le_iff₀ hB).mp hthreshold
  calc
    _ ≤ C * (4 / ChartScales.S n) := mul_le_mul_of_nonneg_left he hC
    _ = (4 * C) / ChartScales.S n := by ring
    _ ≤ B / 2 := (div_le_iff₀ hS0).mpr (by nlinarith only [hb])

end NavierStokes.PhaseEstimates
