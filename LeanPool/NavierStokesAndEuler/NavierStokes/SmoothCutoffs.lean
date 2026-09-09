/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Constructed smooth cutoffs for the diagonal sum and time switch

The fixed cutoff is an actual Mathlib `ContDiffBump`, centered at zero, with
inner radius `1/2` and outer radius `1`. Smoothness below is `C^∞`, written `∞`;
no analyticity assertion is made. The scaled cutoff and time switch are explicit
functions obtained from that bump. No convergence or PDE claim is encoded here.
-/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace NavierStokes.SmoothCutoffs

def cutoffBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoff : ℝ → ℝ := cutoffBump

theorem cutoff_contDiff : ContDiff ℝ ∞ cutoff := cutoffBump.contDiff

theorem cutoff_mem_Icc (x : ℝ) : cutoff x ∈ Icc (0 : ℝ) 1 :=
  ⟨cutoffBump.nonneg, cutoffBump.le_one⟩

theorem cutoff_one_of_abs_le {x : ℝ} (hx : |x| ≤ 1 / 2) : cutoff x = 1 := by
  apply cutoffBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, cutoffBump] using hx

theorem cutoff_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : cutoff x = 0 := by
  apply cutoffBump.zero_of_le_dist
  simpa [Real.dist_eq, cutoffBump] using hx

theorem cutoff_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : cutoff x = 0 :=
  cutoff_zero_of_one_le_abs (hx.trans (le_abs_self x))

theorem cutoff_support : support cutoff = Ioo (-1 : ℝ) 1 := by
  change support (cutoffBump : ℝ → ℝ) = _
  rw [cutoffBump.support_eq]
  ext x
  simp [Metric.mem_ball, cutoffBump, abs_lt]

theorem cutoff_tsupport : tsupport cutoff = Icc (-1 : ℝ) 1 := by
  change tsupport (cutoffBump : ℝ → ℝ) = _
  rw [cutoffBump.tsupport_eq]
  ext x
  simp [Metric.mem_closedBall, cutoffBump, abs_le]

theorem cutoff_hasCompactSupport : HasCompactSupport cutoff :=
  cutoffBump.hasCompactSupport

theorem cutoff_eventually_one {x : ℝ} (hx : |x| < 1 / 2) :
    cutoff =ᶠ[𝓝 x] (fun _ => 1) := by
  apply cutoffBump.eventuallyEq_one_of_mem_ball
  simpa [Metric.mem_ball, cutoffBump] using hx

theorem cutoff_eventually_zero {x : ℝ} (hx : 1 < |x|) :
    cutoff =ᶠ[𝓝 x] (fun _ => 0) := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  rw [cutoff_tsupport]
  intro hmem
  exact (not_le_of_gt hx) (abs_le.mpr hmem)

theorem cutoff_eventually_one_at_zero : cutoff =ᶠ[𝓝 0] (fun _ => 1) :=
  cutoff_eventually_one (by norm_num)

theorem iteratedDeriv_const_succ (n : ℕ) (c : ℝ) :
    iteratedDeriv (n + 1) (fun _ : ℝ => c) = (fun _ => 0) := by
  induction n with
  | zero =>
      ext x
      simp [iteratedDeriv_succ]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      ext x
      simp

theorem cutoff_iteratedDeriv_zero_inside (n : ℕ) {x : ℝ} (hx : |x| < 1 / 2) :
    iteratedDeriv (n + 1) cutoff x = 0 := by
  rw [(cutoff_eventually_one hx).iteratedDeriv_eq (n + 1), iteratedDeriv_const_succ]

theorem cutoff_iteratedDeriv_zero_outside (n : ℕ) {x : ℝ} (hx : 1 < |x|) :
    iteratedDeriv (n + 1) cutoff x = 0 := by
  rw [(cutoff_eventually_zero hx).iteratedDeriv_eq (n + 1), iteratedDeriv_const_succ]

/-- Every positive-order derivative is supported in a fixed collar away from zero. -/
theorem cutoff_iteratedDeriv_support (n : ℕ) :
    support (iteratedDeriv (n + 1) cutoff) ⊆ {x : ℝ | 1 / 2 ≤ |x| ∧ |x| ≤ 1} := by
  intro x hx
  change iteratedDeriv (n + 1) cutoff x ≠ 0 at hx
  constructor
  · by_contra h
    exact hx (cutoff_iteratedDeriv_zero_inside n (lt_of_not_ge h))
  · by_contra h
    exact hx (cutoff_iteratedDeriv_zero_outside n (lt_of_not_ge h))

theorem cutoff_iteratedDeriv_tsupport (n : ℕ) :
    tsupport (iteratedDeriv (n + 1) cutoff) ⊆ {x : ℝ | 1 / 2 ≤ |x| ∧ |x| ≤ 1} := by
  apply closure_minimal (cutoff_iteratedDeriv_support n)
  exact (isClosed_le continuous_const continuous_abs).inter
    (isClosed_le continuous_abs continuous_const)

theorem cutoff_iteratedDeriv_hasCompactSupport (n : ℕ) :
    HasCompactSupport (iteratedDeriv n cutoff) := by
  induction n with
  | zero => simpa using cutoff_hasCompactSupport
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

theorem cutoff_iteratedDeriv_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv n cutoff x| ≤ C := by
  obtain ⟨C, hC⟩ := (cutoff_iteratedDeriv_hasCompactSupport n).exists_bound_of_continuous
    (cutoff_contDiff.continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx : |iteratedDeriv n cutoff x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x
  exact hx.trans (le_max_left _ _)

def scaledCutoff (a : ℝ) : ℝ → ℝ := fun q => cutoff (a * q)

theorem scaledCutoff_contDiff (a : ℝ) : ContDiff ℝ ∞ (scaledCutoff a) :=
  cutoff_contDiff.comp (contDiff_const.mul contDiff_id)

theorem scaledCutoff_mem_Icc (a q : ℝ) : scaledCutoff a q ∈ Icc (0 : ℝ) 1 :=
  cutoff_mem_Icc (a * q)

theorem scaledCutoff_one_of_abs_le {a q : ℝ} (hq : |a * q| ≤ 1 / 2) :
    scaledCutoff a q = 1 := cutoff_one_of_abs_le hq

theorem scaledCutoff_zero_of_one_le_abs {a q : ℝ} (hq : 1 ≤ |a * q|) :
    scaledCutoff a q = 0 := cutoff_zero_of_one_le_abs hq

theorem scaledCutoff_zero_of_inv_le {a q : ℝ} (ha : 0 < a) (hq : 1 / a ≤ q) :
    scaledCutoff a q = 0 := by
  apply cutoff_zero_of_one_le
  have hprod := (div_le_iff₀ ha).mp hq
  nlinarith

theorem scaledCutoff_hasCompactSupport {a : ℝ} (ha : a ≠ 0) :
    HasCompactSupport (scaledCutoff a) := by
  change HasCompactSupport (fun x => cutoff (a * x))
  have hc : HasCompactSupport (fun x : ℝ => cutoff (a • x)) :=
    cutoff_hasCompactSupport.comp_smul (G₀ := ℝ) (c := a) ha
  simpa only [smul_eq_mul] using hc

theorem scaledCutoff_eventually_one {a q : ℝ} (hq : |a * q| < 1 / 2) :
    scaledCutoff a =ᶠ[𝓝 q] (fun _ => 1) :=
  (cutoff_eventually_one hq).comp_tendsto
    (continuous_const.mul continuous_id).continuousAt

theorem scaledCutoff_eventually_zero {a q : ℝ} (hq : 1 < |a * q|) :
    scaledCutoff a =ᶠ[𝓝 q] (fun _ => 0) :=
  (cutoff_eventually_zero hq).comp_tendsto
    (continuous_const.mul continuous_id).continuousAt

theorem scaledCutoff_eventually_one_at_zero (a : ℝ) :
    scaledCutoff a =ᶠ[𝓝 0] (fun _ => 1) :=
  scaledCutoff_eventually_one (by simp)

/-- Every finite list of stage cutoffs has a common plateau around zero. -/
theorem finite_scaledCutoffs_eventually_one {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ∀ᶠ q in 𝓝 0, ∀ i ∈ s, scaledCutoff (a i) q = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      filter_upwards [ih, scaledCutoff_eventually_one_at_zero (a i)] with q hq hqi
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hqi
      · exact hq j hj

/-- If the scales diverge, a common neighborhood of each positive `q₀` meets
only finitely many stage cutoffs. The neighborhood is explicitly `q > q₀/2`. -/
theorem scaledCutoffs_zero_on_common_neighborhood (a : ℕ → ℝ)
    (ha : Tendsto a atTop atTop) {q₀ : ℝ} (hq₀ : 0 < q₀) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℝ, q₀ / 2 < q → scaledCutoff (a n) q = 0 := by
  have htail : ∀ᶠ n in atTop, (2 / q₀ : ℝ) ≤ a n :=
    ha.eventually (eventually_ge_atTop (2 / q₀))
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  refine ⟨N, fun n hn q hq => ?_⟩
  have ha' : 0 < a n := lt_of_lt_of_le (div_pos (by norm_num) hq₀) (hN n hn)
  apply cutoff_zero_of_one_le
  calc
    (1 : ℝ) = (2 / q₀) * (q₀ / 2) := by field_simp
    _ ≤ a n * q := mul_le_mul (hN n hn) hq.le (half_pos hq₀).le ha'.le

/-- The exact all-order chain rule for the scale used in Sections 7 and 11. -/
theorem scaledCutoff_iteratedDeriv (a : ℝ) (n : ℕ) :
    iteratedDeriv n (scaledCutoff a) =
      fun q => a ^ n * iteratedDeriv n cutoff (a * q) :=
  iteratedDeriv_comp_const_mul
    (cutoff_contDiff.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) a

theorem scaledCutoff_iteratedDeriv_support (a : ℝ) (n : ℕ) :
    support (iteratedDeriv (n + 1) (scaledCutoff a)) ⊆
      {q : ℝ | 1 / 2 ≤ |a * q| ∧ |a * q| ≤ 1} := by
  intro q hq
  change iteratedDeriv (n + 1) (scaledCutoff a) q ≠ 0 at hq
  rw [scaledCutoff_iteratedDeriv] at hq
  apply cutoff_iteratedDeriv_support n
  change iteratedDeriv (n + 1) cutoff (a * q) ≠ 0
  intro hz
  exact hq (by simp [hz])

/-- Powers of the scale on derivative support are bounded by powers of `q⁻¹`. -/
theorem scale_power_bound {a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q) (n b : ℕ)
    (hs : iteratedDeriv (n + 1) (scaledCutoff a) q ≠ 0) :
    a ^ b ≤ (1 / q) ^ b := by
  have hup := (scaledCutoff_iteratedDeriv_support a n hs).2
  rw [abs_of_nonneg (mul_nonneg ha hq.le)] at hup
  exact pow_le_pow_left₀ ha ((le_div_iff₀ hq).mpr hup) b

/-- Uniform scale-independent derivative loss used by the diagonal cutoff argument. -/
theorem scaledCutoff_iteratedDeriv_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a q : ℝ, 0 ≤ a → 0 < q →
      |iteratedDeriv (n + 1) (scaledCutoff a) q| ≤ C * (1 / q) ^ (n + 1) := by
  obtain ⟨C, hC, hbound⟩ := cutoff_iteratedDeriv_bounded (n + 1)
  refine ⟨C, hC, fun a q ha hq => ?_⟩
  by_cases hz : iteratedDeriv (n + 1) (scaledCutoff a) q = 0
  · rw [hz, abs_zero]
    positivity
  · have hpow := scale_power_bound ha hq n (n + 1) hz
    rw [scaledCutoff_iteratedDeriv, abs_mul, abs_of_nonneg (pow_nonneg ha _)]
    calc
      _ ≤ a ^ (n + 1) * C := mul_le_mul_of_nonneg_left (hbound (a * q)) (pow_nonneg ha _)
      _ ≤ (1 / q) ^ (n + 1) * C := mul_le_mul_of_nonneg_right hpow hC
      _ = _ := mul_comm _ _

/-- Zero near time zero, and one for every time at least `3/4`. -/
def timeSwitch (t : ℝ) : ℝ := 1 - scaledCutoff (4 / 3) t

theorem timeSwitch_contDiff : ContDiff ℝ ∞ timeSwitch :=
  contDiff_const.sub (scaledCutoff_contDiff (4 / 3))

theorem timeSwitch_mem_Icc (t : ℝ) : timeSwitch t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hlo, hhi⟩ := scaledCutoff_mem_Icc (4 / 3) t
  unfold timeSwitch
  constructor <;> linarith

theorem timeSwitch_zero_of_abs_le {t : ℝ} (ht : |t| ≤ 3 / 8) : timeSwitch t = 0 := by
  have hs : |(4 / 3 : ℝ) * t| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
    linarith
  simp [timeSwitch, scaledCutoff_one_of_abs_le hs]

theorem timeSwitch_one_of_three_quarters_le {t : ℝ} (ht : 3 / 4 ≤ t) :
    timeSwitch t = 1 := by
  have hs : (1 : ℝ) ≤ (4 / 3) * t := by linarith
  simp [timeSwitch, scaledCutoff, cutoff_zero_of_one_le hs]

theorem timeSwitch_eventually_zero : timeSwitch =ᶠ[𝓝 0] (fun _ => 0) := by
  filter_upwards [scaledCutoff_eventually_one_at_zero (4 / 3)] with t ht
  simp [timeSwitch, ht]

theorem timeSwitch_eventually_one {t : ℝ} (ht : 3 / 4 < t) :
    timeSwitch =ᶠ[𝓝 t] (fun _ => 1) := by
  have hs : (1 : ℝ) < |(4 / 3) * t| := by
    have hprod : (1 : ℝ) < (4 / 3) * t := by linarith
    exact hprod.trans_le (le_abs_self _)
  filter_upwards [scaledCutoff_eventually_zero hs] with s hs
  simp [timeSwitch, hs]

theorem timeSwitch_iteratedDeriv_at_zero (n : ℕ) :
    iteratedDeriv (n + 1) timeSwitch 0 = 0 := by
  rw [timeSwitch_eventually_zero.iteratedDeriv_eq (n + 1), iteratedDeriv_const_succ]

theorem timeSwitch_iteratedDeriv_late (n : ℕ) {t : ℝ} (ht : 3 / 4 < t) :
    iteratedDeriv (n + 1) timeSwitch t = 0 := by
  rw [(timeSwitch_eventually_one ht).iteratedDeriv_eq (n + 1), iteratedDeriv_const_succ]

theorem timeSwitch_iteratedDeriv_formula (n : ℕ) (t : ℝ) :
    iteratedDeriv (n + 1) timeSwitch t =
      -((4 / 3 : ℝ) ^ (n + 1) * iteratedDeriv (n + 1) cutoff ((4 / 3) * t)) := by
  unfold timeSwitch
  rw [iteratedDeriv_const_sub (Nat.succ_pos n) (1 : ℝ)]
  change iteratedDeriv (n + 1) (fun s => -(scaledCutoff (4 / 3) s)) t = _
  rw [iteratedDeriv_fun_neg, scaledCutoff_iteratedDeriv]

/-- On the physical half-line, all nonzero positive derivatives lie in `[3/8,3/4]`. -/
theorem timeSwitch_iteratedDeriv_support_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hs : iteratedDeriv (n + 1) timeSwitch t ≠ 0) :
    3 / 8 ≤ t ∧ t ≤ 3 / 4 := by
  have hcut : iteratedDeriv (n + 1) cutoff ((4 / 3) * t) ≠ 0 := by
    intro hz
    apply hs
    rw [timeSwitch_iteratedDeriv_formula, hz]
    simp
  have hb := cutoff_iteratedDeriv_support n hcut
  change 1 / 2 ≤ |(4 / 3 : ℝ) * t| ∧ |(4 / 3 : ℝ) * t| ≤ 1 at hb
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 / 3) * t)] at hb
  constructor <;> linarith [hb.1, hb.2]

end NavierStokes.SmoothCutoffs
