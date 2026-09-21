/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries.Annulus
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.RemovableSingularity.Cauchy

/-!
# Circle coefficients for analytic Laurent series

Laurent coefficients on a circle satisfy Cauchy bounds and depend holomorphically on holomorphic
parameters. Cauchy's formula on an annulus proves the Laurent expansion, independence of radius,
and vanishing of negative coefficients on a disc. These results are independent of the
multivariable Laurent expansion.

## Main results

`circleLaurentCoeff` is the coefficient of `z ^ k` on the circle of radius `r`.
`circleLaurentCoeff_eq_of_connected` is independence of radius on a connected set of admissible
radii. `circleLaurentCoeff_neg_eq_zero` is vanishing of negative coefficients on a disc.
`circleLaurent_expansion` is the two-sided series on an annulus.
-/

public noncomputable section

open Complex Set Filter Metric
open scoped Topology

namespace SeveralComplexVariables

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The coefficient of exponent `k` obtained by integrating on the circle of radius `r`. -/
@[expose] def circleLaurentCoeff (f : ℂ → F) (r : ℝ) (k : ℤ) : F :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∮ w in C(0, r), w ^ (-k - 1) • f w

omit [CompleteSpace F] in
/-- Cauchy's bound for an arbitrary integer Laurent coefficient. No analyticity assumption is needed
for this integral estimate. -/
theorem norm_circleLaurentCoeff_le {f : ℂ → F} {r M : ℝ} (hr : 0 < r)
    (hM : ∀ w ∈ sphere (0 : ℂ) r, ‖f w‖ ≤ M) (k : ℤ) :
    ‖circleLaurentCoeff f r k‖ ≤ M * r ^ (-k) := by
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le
    (C := r ^ (-k - 1) * M) (f := fun w => w ^ (-k - 1) • f w) (by
      intro w hw
      have hn : ‖w‖ = r := mem_sphere_zero_iff_norm.mp hw
      rw [norm_smul, norm_zpow, hn]
      exact mul_le_mul_of_nonneg_left (hM w hw) (zpow_nonneg hr.le _))
  apply h.trans_eq
  have he : r * r ^ (-k - 1) = r ^ (-k) := by
    calc
      r * r ^ (-k - 1) = r ^ (1 : ℤ) * r ^ (-k - 1) := by rw [zpow_one]
      _ = r ^ (-k) := by rw [← zpow_add₀ hr.ne']; congr 1; omega
  rw [mul_comm (r ^ (-k - 1)) M, ← mul_assoc, mul_comm r M, mul_assoc,
    he]

/-- A fixed-circle Laurent coefficient is analytic in any finite-dimensional complex parameter on
which the integrand depends holomorphically. -/
theorem analyticOnNhd_circleLaurentCoeff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {V : Set E} (hV : IsOpen V)
    {U : Set (E × ℂ)} {f : E × ℂ → F} (hf : AnalyticOnNhd ℂ f U)
    {r : ℝ} (hr : 0 < r) (hsub : ∀ z ∈ V, ∀ w ∈ sphere (0 : ℂ) r, (z, w) ∈ U)
    (k : ℤ) : AnalyticOnNhd ℂ (fun z => circleLaurentCoeff (fun w => f (z, w)) r k) V := by
  let W := U ∩ {p : E × ℂ | p.2 ≠ 0}
  have hH : AnalyticOnNhd ℂ (fun p : E × ℂ => p.2 ^ (-k - 1) • f p) W := by
    intro p hp
    exact (analyticAt_snd.zpow (n := -k - 1) hp.2).smul (hf p hp.1)
  apply (analyticOnNhd_circleIntegral_kernel hV hH hr.le ?_).const_smul
  intro z hz w hw
  refine ⟨hsub z hz w hw, ?_⟩
  exact norm_pos_iff.mp (by rw [mem_sphere_zero_iff_norm.mp hw]; exact hr)

omit [CompleteSpace F] in
/-- The nonnegative Laurent terms admit a geometric bound inside the coefficient circle. -/
theorem norm_circleLaurentTerm_nat_le {f : ℂ → F} {R M t : ℝ} (hR : 0 < R)
    (hbound : ∀ w ∈ sphere (0 : ℂ) R, ‖f w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ t) (n : ℕ) :
    ‖z ^ (n : ℤ) • circleLaurentCoeff f R n‖ ≤ M * (t / R) ^ n := by
  have hc := norm_circleLaurentCoeff_le hR hbound (n : ℤ)
  have ht : 0 ≤ t := (norm_nonneg z).trans hz
  rw [zpow_neg, zpow_natCast] at hc
  rw [norm_smul, norm_zpow, zpow_natCast]
  calc
    ‖z‖ ^ n * ‖circleLaurentCoeff f R n‖ ≤ t ^ n * (M * (R ^ n)⁻¹) := by
      gcongr
    _ = M * (t / R) ^ n := by simp only [div_eq_mul_inv]; ring

omit [CompleteSpace F] in
/-- The negative Laurent terms admit a geometric bound outside the coefficient circle. -/
theorem norm_circleLaurentTerm_negSucc_le {f : ℂ → F} {r M t : ℝ} (hr : 0 < r)
    (ht : 0 < t) (hbound : ∀ w ∈ sphere (0 : ℂ) r, ‖f w‖ ≤ M)
    {z : ℂ} (hz : t ≤ ‖z‖) (n : ℕ) :
    ‖z ^ (Int.negSucc n) • circleLaurentCoeff f r (Int.negSucc n)‖ ≤
      M * (r / t) ^ (n + 1) := by
  have hc := norm_circleLaurentCoeff_le hr hbound (Int.negSucc n)
  simp only [Int.neg_negSucc, zpow_natCast] at hc
  rw [norm_smul, norm_zpow, zpow_negSucc]
  calc
    (‖z‖ ^ (n + 1))⁻¹ * ‖circleLaurentCoeff f r (Int.negSucc n)‖ ≤
        (t ^ (n + 1))⁻¹ * (M * r ^ (n + 1)) := by
      gcongr
    _ = M * (r / t) ^ (n + 1) := by simp only [div_eq_mul_inv]; ring

/-- A connected rotation-invariant set contains all intermediate radii. -/
private theorem mem_of_norm_between {V : Set ℂ} (hc : IsConnected V)
    (hrot : ∀ z ∈ V, ∀ w : ℂ, ‖w‖ = ‖z‖ → w ∈ V)
    {a b w : ℂ} (ha : a ∈ V) (hb : b ∈ V)
    (haw : ‖a‖ ≤ ‖w‖) (hwb : ‖w‖ ≤ ‖b‖) : w ∈ V := by
  obtain ⟨v, hv, he⟩ := (hc.isPreconnected.image norm continuous_norm.continuousOn).Icc_subset
    (mem_image_of_mem _ ha) (mem_image_of_mem _ hb) ⟨haw, hwb⟩
  exact hrot v hv w he.symm

omit [CompleteSpace F] in
/-- Laurent coefficients are unchanged between two circles in an analytic annulus. -/
theorem circleLaurentCoeff_eq_of_analyticOnNhd_annulus {f : ℂ → F} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R \ ball 0 r)) :
    circleLaurentCoeff f R = circleLaurentCoeff f r := by
  funext k
  have ha : AnalyticOnNhd ℂ (fun w => w ^ (-k - 1) • f w)
      (closedBall 0 R \ ball 0 r) := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro he
      subst w
      exact hw.2 (mem_ball_self hr)
    exact (analyticAt_id.zpow hw0).smul (hf w hw)
  unfold circleLaurentCoeff
  congr 1
  exact circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR countable_empty
    ha.continuousOn (fun w hw => (ha w ⟨ball_subset_closedBall hw.1.1,
      fun hb => hw.1.2 (ball_subset_closedBall hb)⟩).differentiableAt)

omit [CompleteSpace F] in
/-- On a connected rotation-invariant set, the Laurent coefficients do not depend on radius. -/
theorem circleLaurentCoeff_eq_of_connected {V : Set ℂ} (hc : IsConnected V)
    (hrot : ∀ z ∈ V, ∀ w : ℂ, ‖w‖ = ‖z‖ → w ∈ V)
    {f : ℂ → F} (hf : AnalyticOnNhd ℂ f V) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrV : (r : ℂ) ∈ V) (hsV : (s : ℂ) ∈ V) :
    circleLaurentCoeff f s = circleLaurentCoeff f r := by
  have hordered {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
      (haV : (a : ℂ) ∈ V) (hbV : (b : ℂ) ∈ V) :
      circleLaurentCoeff f b = circleLaurentCoeff f a := by
    apply circleLaurentCoeff_eq_of_analyticOnNhd_annulus ha hab (hf.mono ?_)
    intro w hw
    apply mem_of_norm_between hc hrot haV hbV
    · simpa [abs_of_pos ha] using (not_lt.mp (mem_ball_zero_iff.not.mp hw.2))
    · simpa [abs_of_pos (ha.trans_le hab)] using mem_closedBall_zero_iff.mp hw.1
  rcases le_total r s with h | h
  · exact hordered hr h hrV hsV
  · exact (hordered hs h hsV hrV).symm

omit [CompleteSpace F] in
/-- Negative Laurent coefficients vanish if the coefficient circle bounds an analytic disc. -/
theorem circleLaurentCoeff_neg_eq_zero {f : ℂ → F} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) {k : ℤ} (hk : k < 0) :
    circleLaurentCoeff f r k = 0 := by
  have he : -k - 1 = ((-k - 1).toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  have ha : AnalyticOnNhd ℂ (fun w => w ^ (-k - 1) • f w) (closedBall 0 r) := by
    have ha' : AnalyticOnNhd ℂ (fun w => w ^ (-k - 1).toNat • f w) (closedBall 0 r) :=
      fun w hw => (analyticAt_id.pow _).smul (hf w hw)
    convert ha' using 1
    funext w
    rw [he, zpow_natCast, Int.toNat_natCast]
  rw [circleLaurentCoeff,
    (ha.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero
      hr,
    smul_zero]

omit [CompleteSpace F] in
/-- The nonnegative Laurent terms sum to the outer Cauchy integral. -/
theorem hasSum_circleLaurentCoeff_nat {f : ℂ → F} {R : ℝ}
    (hf : CircleIntegrable f 0 R) {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun n : ℕ => z ^ (n : ℤ) • circleLaurentCoeff f R n)
      ((2 * Real.pi * I : ℂ)⁻¹ • ∮ w in C(0, R), (w - z)⁻¹ • f w) := by
  have hR : 0 < R := (norm_nonneg z).trans_lt hz
  have hs := (hasSum_two_pi_I_cauchyPowerSeries_integral hf hz).const_smul
    (2 * Real.pi * I : ℂ)⁻¹
  simp only [zero_add, sub_zero] at hs
  apply hs.congr_fun
  intro n
  rw [circleLaurentCoeff, smul_comm (z ^ (n : ℤ)), ← circleIntegral.integral_smul]
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro w _
  dsimp only
  rw [show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by omega, zpow_neg,
    zpow_natCast, zpow_natCast, smul_smul, smul_smul]
  congr 1
  simp [div_eq_mul_inv, mul_pow, pow_succ, mul_left_comm, mul_comm]

omit [CompleteSpace F] in
/-- The negative Laurent terms sum to the inner Cauchy integral with reversed kernel. -/
theorem hasSum_circleLaurentCoeff_negSucc {f : ℂ → F} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (sphere (0 : ℂ) r)) {z : ℂ} (hz : r < ‖z‖) :
    HasSum (fun n : ℕ => z ^ (Int.negSucc n) • circleLaurentCoeff f r (Int.negSucc n))
      ((2 * Real.pi * I : ℂ)⁻¹ • ∮ w in C(0, r), (z - w)⁻¹ • f w) := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans_lt hz)
  have hs := (hasSum_circleIntegral_geometric hr (hf.const_smul z⁻¹)
    (g := fun w => w / z) (continuousOn_id.div_const z)
    (div_nonneg hr (norm_nonneg z)) ((div_lt_one (hr.trans_lt hz)).mpr hz) (by
      intro w hw
      simp [mem_sphere_zero_iff_norm.mp hw])).const_smul (2 * Real.pi * I : ℂ)⁻¹
  have he : (∮ w in C(0, r), (1 - w / z)⁻¹ • z⁻¹ • f w) =
      ∮ w in C(0, r), (z - w)⁻¹ • f w := by
    apply circleIntegral.integral_congr hr
    intro w _
    dsimp only
    rw [smul_smul]
    congr 1
    rw [← mul_inv, sub_mul, one_mul, div_mul_cancel₀ _ hz0]
  simp only [Pi.smul_apply] at hs
  rw [he] at hs
  apply hs.congr_fun
  intro n
  rw [circleLaurentCoeff, smul_comm (z ^ (Int.negSucc n)),
    ← circleIntegral.integral_smul]
  congr 1
  apply circleIntegral.integral_congr hr
  intro w _
  dsimp only
  rw [show -(Int.negSucc n) - 1 = (n : ℤ) by omega, zpow_natCast,
    zpow_negSucc, smul_smul, smul_smul]
  congr 1
  simp [div_eq_mul_inv, mul_pow, pow_succ, mul_left_comm, mul_comm]

/-- Laurent expansion at a point strictly between two analytic coefficient circles. -/
theorem hasSum_circleLaurentCoeff_annulus {f : ℂ → F} {r R : ℝ}
    (hr : 0 < r) {z : ℂ} (hzr : r < ‖z‖) (hzR : ‖z‖ < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R \ ball 0 r)) :
    HasSum (fun k : ℤ => z ^ k • circleLaurentCoeff f r k) (f z) := by
  have hs (t : ℝ) (ht : t = r ∨ t = R) : sphere (0 : ℂ) t ⊆ closedBall 0 R \ ball 0 r := by
    intro w hw
    have hw' := mem_sphere_zero_iff_norm.mp hw
    simp only [Set.mem_sdiff, mem_closedBall_zero_iff, mem_ball_zero_iff, not_lt, hw']
    rcases ht with rfl | rfl <;> constructor <;> linarith
  have hp := hasSum_circleLaurentCoeff_nat
    ((hf.continuousOn.mono (hs R (Or.inr rfl))).circleIntegrable (hr.trans (hzr.trans hzR)).le) hzR
  rw [circleLaurentCoeff_eq_of_analyticOnNhd_annulus hr (hzr.trans hzR).le hf] at hp
  have hn := hasSum_circleLaurentCoeff_negSucc hr.le (hf.continuousOn.mono (hs r (Or.inl rfl))) hzr
  have hi : (∮ w in C(0, r), (z - w)⁻¹ • f w) =
      -(∮ w in C(0, r), (w - z)⁻¹ • f w) := by
    calc
      _ = ∮ w in C(0, r), -((w - z)⁻¹ • f w) := by
        congr 1
        funext w
        rw [← neg_sub w z, inv_neg, neg_smul]
      _ = _ := by simp only [circleIntegral, smul_neg, intervalIntegral.integral_neg]
  have hsum := hp.int_rec hn
  rw [hi, ← smul_add, ← sub_eq_add_neg,
    circleIntegral_sub_inv_smul_sub_of_analyticOnNhd_annulus hr hzr hzR hf,
    inv_smul_smul₀ two_pi_I_ne_zero] at hsum
  exact hsum.congr_fun fun k => by cases k <;> rfl

/-- One-variable Laurent expansion on a connected rotation-invariant open set, including
independence of radius and vanishing of negative coefficients at zero. -/
theorem circleLaurent_expansion {V : Set ℂ} (hV : IsOpen V) (hc : IsConnected V)
    (hrot : ∀ z ∈ V, ∀ w : ℂ, ‖w‖ = ‖z‖ → w ∈ V)
    {f : ℂ → F} (hf : AnalyticOnNhd ℂ f V) {r : ℝ} (hr : 0 < r) (hrV : (r : ℂ) ∈ V) :
    (∀ z ∈ V, HasSum (fun k : ℤ => z ^ k • circleLaurentCoeff f r k) (f z)) ∧
    (∀ s : ℝ, 0 < s → (s : ℂ) ∈ V → circleLaurentCoeff f s = circleLaurentCoeff f r) ∧
    (0 ∈ V → ∀ k : ℤ, k < 0 → circleLaurentCoeff f r k = 0) := by
  have hind (s : ℝ) (hs : 0 < s) (hsV : (s : ℂ) ∈ V) :
      circleLaurentCoeff f s = circleLaurentCoeff f r :=
    circleLaurentCoeff_eq_of_connected hc hrot hf hr hs hrV hsV
  have hdisc (h0 : 0 ∈ V) : AnalyticOnNhd ℂ f (closedBall 0 r) := by
    apply hf.mono
    intro w hw
    apply mem_of_norm_between hc hrot h0 hrV
    · simp
    · simpa [abs_of_pos hr] using mem_closedBall_zero_iff.mp hw
  refine ⟨?_, hind, fun h0 k hk => circleLaurentCoeff_neg_eq_zero hr.le (hdisc h0) hk⟩
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    have he : circleLaurentCoeff f r 0 = f 0 := by
      have hdc := ((hdisc hz).differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
      simpa [circleLaurentCoeff] using
        hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (mem_ball_self hr)
    simpa [he] using (hasSum_single (0 : ℤ)
      (f := fun k : ℤ => (0 : ℂ) ^ k • circleLaurentCoeff f r k) (by
        intro k hk
        simp [zero_zpow k hk]))
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hzV : (‖z‖ : ℂ) ∈ V := hrot z hz _ (by simp)
    obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      ((hV.preimage continuous_ofReal).mem_nhds hzV)
    obtain ⟨s, hs₁, hs₂⟩ := exists_between (max_lt hn hab.1)
    obtain ⟨R, hR₁, hR₂⟩ := exists_between hab.2
    have hs : 0 < s := (le_max_left _ _).trans_lt hs₁
    have hsV : (s : ℂ) ∈ V := hsub ⟨(le_max_right _ _).trans_lt hs₁, hs₂.trans hab.2⟩
    have hRV : (R : ℂ) ∈ V := hsub ⟨hab.1.trans hR₁, hR₂⟩
    have ha : AnalyticOnNhd ℂ f (closedBall 0 R \ ball 0 s) := by
      apply hf.mono
      intro w hw
      apply mem_of_norm_between hc hrot hsV hRV
      · simpa [abs_of_pos hs] using (not_lt.mp (mem_ball_zero_iff.not.mp hw.2))
      · simpa [abs_of_pos (hn.trans hR₁)] using mem_closedBall_zero_iff.mp hw.1
    simpa only [hind s hs hsV] using hasSum_circleLaurentCoeff_annulus hs hs₂ hR₁ ha

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
