/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: residue-calculus. The circle-integral / residue bridge.
-/
import LeanPool.JacobianDiffgeo.ResidueCalculus.Residue
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The circle-integral bridge (residue-calculus)

The one honest integration atom this unit budgets for: `∮_{C(z₀,R)} f = 2πi · resAt f z₀`, for
`f` meromorphic at `z₀` and differentiable on the punctured closed disk. A small-radius
(`∀ᶠ` in the radius) convenience form is also provided for consumers who only know meromorphy.

Main exports: `RS.circleIntegral_eq_two_pi_I_mul_resAt`,
`RS.MeromorphicAt.eventually_circleIntegral_eq_two_pi_I_mul_resAt`.
-/

open Filter Topology Metric Function Real Complex

namespace RS

variable {f : ℂ → ℂ} {z₀ : ℂ}

open Real Complex in
/-- Fixed-radius residue formula: if `f` is meromorphic at `z₀` and differentiable on the
punctured closed disk, the circle integral computes the residue. -/
theorem circleIntegral_eq_two_pi_I_mul_resAt {R : ℝ} (hR : 0 < R) (hf : MeromorphicAt f z₀)
    (hd : ∀ z ∈ closedBall z₀ R \ {z₀}, DifferentiableAt ℂ f z) :
    (∮ z in C(z₀, R), f z) = (2 * π * I) * resAt f z₀ := by
  obtain ⟨h, hh, _, hdecomp⟩ := MeromorphicAt.exists_principalPart_add_analyticAt hf
  set a := (meromorphicOrderAt f z₀).untop₀ with hadef
  -- Extract a punctured ball on which the decomposition holds.
  obtain ⟨r₂, hr₂pos, hr₂⟩ :
      ∃ r₂ > 0, ∀ z ∈ ball z₀ r₂ \ {z₀}, f z = principalPartAt f z₀ z + h z := by
    obtain ⟨r₂, hr₂pos, hr₂⟩ := eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hdecomp)
    exact ⟨r₂, hr₂pos, fun z hz => hr₂ z hz.1 hz.2⟩
  -- Extract a ball on which `h` is analytic.
  obtain ⟨r₁, hr₁pos, hr₁raw⟩ := eventually_nhds_iff_ball.mp hh.eventually_analyticAt
  have hr₁ : AnalyticOnNhd ℂ h (ball z₀ r₁) := hr₁raw
  -- Pick a small radius `r` strictly inside both, and `≤ R`.
  set r := min R (min r₁ r₂) / 2 with hrdef
  have hm : (0:ℝ) < min R (min r₁ r₂) := lt_min hR (lt_min hr₁pos hr₂pos)
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrR : r ≤ R := by
    have h1 : min R (min r₁ r₂) ≤ R := min_le_left R (min r₁ r₂)
    rw [hrdef]; linarith
  have hrr1 : r < r₁ := by
    have h1 : min R (min r₁ r₂) ≤ r₁ := (min_le_right R (min r₁ r₂)).trans (min_le_left r₁ r₂)
    rw [hrdef]; linarith
  have hrr2 : r < r₂ := by
    have h1 : min R (min r₁ r₂) ≤ r₂ := (min_le_right R (min r₁ r₂)).trans (min_le_right r₁ r₂)
    rw [hrdef]; linarith
  -- Step 1: deform the big circle to the small one; the annulus avoids `z₀`.
  have hdeform : (∮ z in C(z₀, R), f z) = ∮ z in C(z₀, r), f z := by
    apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hrpos hrR
      (Set.countable_empty)
    · intro z hz
      have hzne : z ≠ z₀ := by
        intro hcon
        apply hz.2
        rw [hcon]; exact mem_ball_self hrpos
      exact (hd z ⟨hz.1, hzne⟩).continuousAt.continuousWithinAt
    · intro z hz
      have hzne : z ≠ z₀ := by
        intro hcon
        apply hz.1.2
        rw [hcon, mem_closedBall, dist_self]
        exact hrpos.le
      exact hd z ⟨(ball_subset_closedBall hz.1.1), hzne⟩
  rw [hdeform]
  -- Step 2: split the small circle integral into principal part + analytic remainder.
  have hsphere_sub_ball2 : sphere z₀ r ⊆ ball z₀ r₂ \ {z₀} := by
    intro z hz
    rw [mem_sphere] at hz
    refine ⟨?_, ?_⟩
    · rw [mem_ball, hz]; exact hrr2
    · simp only [Set.mem_singleton_iff]
      intro hcon
      rw [hcon, dist_self] at hz
      exact hrpos.ne' hz.symm
  have heqOn : Set.EqOn f (fun z => principalPartAt f z₀ z + h z) (sphere z₀ r) :=
    fun z hz => hr₂ z (hsphere_sub_ball2 hz)
  rw [circleIntegral.integral_congr hrpos.le heqOn]
  have hPintegrable : CircleIntegrable (principalPartAt f z₀) z₀ r := by
    unfold principalPartAt
    apply CircleIntegrable.fun_sum
    intro k _
    have hzsphere : z₀ ∉ sphere z₀ |r| := by
      rw [mem_sphere, dist_self, abs_of_pos hrpos]
      exact hrpos.ne
    exact CircleIntegrable.const_fun_smul
      (circleIntegrable_sub_zpow_iff.mpr (Or.inr (Or.inr hzsphere)))
  have hhintegrable : CircleIntegrable h z₀ r := by
    apply ContinuousOn.circleIntegrable hrpos.le
    exact (hr₁.continuousOn.mono (closedBall_subset_ball hrr1)).mono sphere_subset_closedBall
  rw [circleIntegral.integral_add hPintegrable hhintegrable]
  -- Step 3: the analytic remainder integrates to `0`.
  have hharm : (∮ z in C(z₀, r), h z) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hrpos.le
      (Set.countable_empty)
    · exact hr₁.continuousOn.mono (closedBall_subset_ball hrr1)
    · exact fun z hz => (hr₁ z ((ball_subset_ball hrr1.le) hz.1)).differentiableAt
  rw [hharm, add_zero]
  -- Step 4: the principal part integrates termwise, picking out the `k = -1` coefficient.
  unfold principalPartAt
  have hterm : ∀ k ∈ Finset.Icc a (-1),
      CircleIntegrable (fun z => laurentCoeffAt f z₀ k * (z - z₀) ^ k) z₀ r := by
    intro k _
    have hzsphere : z₀ ∉ sphere z₀ |r| := by
      rw [mem_sphere, dist_self, abs_of_pos hrpos]
      exact hrpos.ne
    exact CircleIntegrable.const_fun_smul
      (circleIntegrable_sub_zpow_iff.mpr (Or.inr (Or.inr hzsphere)))
  rw [circleIntegral.integral_fun_sum hterm]
  have hval : ∀ k ∈ Finset.Icc a (-1),
      (∮ z in C(z₀, r), laurentCoeffAt f z₀ k * (z - z₀) ^ k)
        = laurentCoeffAt f z₀ k * (if k = -1 then 2 * π * I else 0) := by
    intro k _
    rw [circleIntegral.integral_const_mul]
    congr 1
    split_ifs with hk1
    · subst hk1
      simp only [zpow_neg_one]
      exact circleIntegral.integral_sub_center_inv z₀ hrpos.ne'
    · exact circleIntegral.integral_sub_zpow_of_ne hk1 z₀ z₀ r
  rw [Finset.sum_congr rfl hval]
  by_cases ha : a ≤ -1
  · rw [Finset.sum_eq_single (-1)
      (fun k _ hkne => by rw [ite_eq_right hkne, mul_zero])
      (fun hnmem => absurd (Finset.mem_Icc.mpr ⟨ha, le_refl _⟩) hnmem)]
    rw [ite_eq_left rfl]
    change laurentCoeffAt f z₀ (-1) * (2 * π * I) = 2 * π * I * resAt f z₀
    rw [resAt]; ring
  · push Not at ha
    have hempty : Finset.Icc a (-1) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    have h0a : (0 : ℤ) ≤ a := by omega
    rw [hadef] at h0a
    rw [resAt_of_order_nonneg (WithTop.untop₀_nonneg.mp h0a), mul_zero]

open Real Complex in
/-- Small-radius form for consumers that only know meromorphy (they pick their own `ρ`). -/
theorem MeromorphicAt.eventually_circleIntegral_eq_two_pi_I_mul_resAt
    (hf : MeromorphicAt f z₀) :
    ∀ᶠ R in 𝓝[>] (0 : ℝ), (∮ z in C(z₀, R), f z) = (2 * π * I) * resAt f z₀ := by
  obtain ⟨N, hN⟩ := hf
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ := eventually_nhds_iff_ball.mp hN.eventually_analyticAt
  have hd : ∀ z ∈ ball z₀ ρ₀ \ {z₀}, DifferentiableAt ℂ f z := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hzne : z ≠ z₀ := hz2
    have hzsub : z - z₀ ≠ 0 := sub_ne_zero.2 hzne
    have hanalytic : AnalyticAt ℂ (fun w => (w - z₀) ^ N • f w) z := hρ₀ z hz1
    have heq : f =ᶠ[𝓝 z] fun w => (w - z₀) ^ (-(N : ℤ)) * ((w - z₀) ^ N • f w) := by
      have hopen : {z₀}ᶜ ∈ 𝓝 z := IsOpen.mem_nhds isOpen_compl_singleton hzne
      filter_upwards [hopen] with w hw
      have hwsub : w - z₀ ≠ 0 := sub_ne_zero.2 hw
      rw [smul_eq_mul, ← mul_assoc, ← zpow_natCast (w - z₀) N, ← zpow_add₀ hwsub]
      simp
    have hdiffRHS : DifferentiableAt ℂ
        (fun w => (w - z₀) ^ (-(N : ℤ)) * ((w - z₀) ^ N • f w)) z := by
      have h1 : DifferentiableAt ℂ (fun w : ℂ => (w - z₀) ^ (-(N : ℤ))) z :=
        (show DifferentiableAt ℂ (fun w : ℂ => w - z₀) z by fun_prop).zpow (Or.inl hzsub)
      have h2 : DifferentiableAt ℂ (fun w => (w - z₀) ^ N • f w) z := hanalytic.differentiableAt
      exact h1.mul (by simpa using h2)
    exact hdiffRHS.congr_of_eventuallyEq heq
  have hd' : ∀ R : ℝ, R < ρ₀ → ∀ z ∈ closedBall z₀ R \ {z₀}, DifferentiableAt ℂ f z := by
    intro R hR z hz
    obtain ⟨hz1, hz2⟩ := hz
    exact hd z ⟨by rw [mem_ball]; exact lt_of_le_of_lt hz1 hR, hz2⟩
  filter_upwards [Ioo_mem_nhdsGT hρ₀pos] with R hR
  exact circleIntegral_eq_two_pi_I_mul_resAt hR.1 (⟨N, hN⟩ : MeromorphicAt f z₀) (hd' R hR.2)

end RS
