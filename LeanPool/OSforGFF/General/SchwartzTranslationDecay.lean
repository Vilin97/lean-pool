/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Operator.Mul -- For ContinuousLinearMap.mul

/-!
# Schwartz Bilinear Translation Decay

This file proves that bilinear integrals of Schwartz functions against a decaying
kernel vanish at infinity under translation.

## Main Result

`schwartz_bilinear_translation_decay`: For Schwartz functions f, g on a
finite-dimensional real inner product space E, and a kernel K : E → ℝ
with polynomial decay |K(z)| ≤ C/‖z‖^α for large ‖z‖, the bilinear
integral against a translated g vanishes at infinity:

  ∫∫ f(x) · K(x - y) · g(y - a) dx dy → 0  as ‖a‖ → ∞

## Proof Strategy (via convolutions)

The key theorem is: L¹ ⋆ C₀ → C₀ (convolution of integrable with vanishing-at-∞ vanishes)

Apply this pattern three times:
1. f ⋆ K_sing: f is C₀ (Schwartz), K_sing is L¹ → result is C₀
2. f ⋆ K_tail: f is L¹ (Schwartz), K_tail is C₀ (decay) → result is C₀
3. (f ⋆ K) ⋆ g: g is L¹, (f ⋆ K) is C₀ → result is C₀

## References

- Glimm-Jaffe "Quantum Physics" Ch. 6 (clustering)
- Reed-Simon Vol. II, Ch. X (decay of correlations)
-/

open MeasureTheory Complex SchwartzMap Filter Convolution Set Function Metric
open scoped Real Topology Pointwise

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## Helper lemmas for Schwartz functions -/

/-- Schwartz functions are integrable. -/
lemma schwartz_integrable (f : SchwartzMap E ℂ) : Integrable f := f.integrable

omit [MeasurableSpace E] [BorelSpace E] in
/-- Schwartz functions vanish at infinity (C₀).

Proof: Schwartz decay gives ‖x‖^k · ‖f(x)‖ ≤ seminorm k 0 f for all k.
Taking k = 1: ‖f(x)‖ ≤ C/‖x‖ → 0 as ‖x‖ → ∞.
-/
lemma schwartz_tendsto_zero (f : SchwartzMap E ℂ) :
    Tendsto f (cocompact E) (nhds 0) :=
  zero_at_infty f

/-! ## Kernel decomposition -/

/-- The singular (compactly supported) part of the kernel. -/
def kernelSingular (K : E → ℝ) (R₀ : ℝ) : E → ℝ :=
  fun x => K x * (closedBall (0 : E) R₀).indicator (fun _ => (1 : ℝ)) x

/-- The tail (decaying) part of the kernel. -/
def kernelTail (K : E → ℝ) (R₀ : ℝ) : E → ℝ :=
  fun x => K x * (closedBall (0 : E) R₀)ᶜ.indicator (fun _ => (1 : ℝ)) x

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Kernel decomposes into singular and tail parts. -/
lemma kernel_decomposition (K : E → ℝ) (R₀ : ℝ) :
    K = fun x => kernelSingular K R₀ x + kernelTail K R₀ x := by
  ext x
  simp only [kernelSingular, kernelTail]
  by_cases hx : x ∈ closedBall (0 : E) R₀
  · rw [indicator_of_mem hx, indicator_of_notMem (by simp [hx])]
    ring
  · rw [indicator_of_notMem hx, indicator_of_mem (mem_compl hx)]
    ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- K_tail vanishes at infinity when K has polynomial decay. -/
lemma kernelTail_tendsto_zero (K : E → ℝ) (R₀ : ℝ)
    (α : ℝ) (hα : α > 0) (C : ℝ)
    (hK_decay : ∀ z : E, ‖z‖ ≥ R₀ → |K z| ≤ C / ‖z‖ ^ α) :
    Tendsto (kernelTail K R₀) (cocompact E) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- For ‖z‖ ≤ R₀, kernelTail z = 0
  -- For ‖z‖ > R₀, |kernelTail z| = |K z| ≤ C/‖z‖^α
  -- We need C/‖z‖^α < ε, i.e., ‖z‖ > (C/ε)^(1/α)
  by_cases hC : C ≤ 0
  · -- If C ≤ 0, decay bound gives |K z| ≤ 0, so K z = 0 for ‖z‖ ≥ R₀
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨(closedBall 0 R₀)ᶜ, ?_, ?_⟩
    · rw [Filter.mem_cocompact]
      exact ⟨closedBall 0 R₀, isCompact_closedBall 0 R₀, fun x hx => hx⟩
    · intro z hz
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hz
      simp only [kernelTail, dist_zero_right]
      have hmem : z ∈ (closedBall (0 : E) R₀)ᶜ := by
        simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
        exact hz
      rw [indicator_of_mem hmem, mul_one]
      have hbound := hK_decay z hz.le
      have : |K z| ≤ 0 := le_trans hbound (div_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg
        (norm_nonneg z) α))
      simp only [abs_nonpos_iff] at this
      simp [this, hε]
  · -- C > 0 case
    push Not at hC
    let R := max R₀ ((C / ε) ^ (1 / α) + 1)
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨(closedBall 0 R)ᶜ, ?_, ?_⟩
    · rw [Filter.mem_cocompact]
      exact ⟨closedBall 0 R, isCompact_closedBall 0 R, fun x hx => hx⟩
    · intro z hz
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hz
      simp only [dist_zero_right]
      -- Two cases: z inside or outside the R₀ ball
      by_cases hz_R₀ : ‖z‖ ≤ R₀
      · -- Inside R₀ ball: kernelTail z = 0
        simp only [kernelTail]
        rw [indicator_of_notMem (by simp [hz_R₀] : z ∉ (closedBall (0 : E) R₀)ᶜ), mul_zero,
            norm_zero]
        exact hε
      · -- Outside R₀ ball: use decay bound
        push Not at hz_R₀
        simp only [kernelTail]
        have hmem : z ∈ (closedBall (0 : E) R₀)ᶜ := by
          simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
          exact hz_R₀
        rw [indicator_of_mem hmem, mul_one]
        have hbound := hK_decay z hz_R₀.le
        have hz_large : ‖z‖ > (C / ε) ^ (1 / α) := by
          calc ‖z‖ > R := hz
            _ ≥ (C / ε) ^ (1 / α) + 1 := le_max_right _ _
            _ > (C / ε) ^ (1 / α) := lt_add_one _
        have hz_pos : 0 < ‖z‖ := by
          have h1 : 0 < (C / ε) ^ (1 / α) + 1 := by positivity
          calc 0 < (C / ε) ^ (1 / α) + 1 := h1
            _ ≤ R := le_max_right _ _
            _ < ‖z‖ := hz
        calc ‖K z‖ = |K z| := Real.norm_eq_abs _
          _ ≤ C / ‖z‖ ^ α := hbound
          _ < ε := by
              -- We have ‖z‖ > (C/ε)^(1/α), so ‖z‖^α > C/ε, hence C/‖z‖^α < ε
              have hCε_pos : 0 < C / ε := div_pos hC hε
              -- (C/ε)^(1/α) < ‖z‖ implies (C/ε) < ‖z‖^α by taking α-power
              have key : C / ε < ‖z‖ ^ α := by
                have h1 : (C / ε) ^ (1 / α) < ‖z‖ := hz_large
                have h2 : ((C / ε) ^ (1 / α)) ^ α = C / ε := by
                  rw [← Real.rpow_mul (le_of_lt hCε_pos)]
                  simp [one_div, inv_mul_cancel₀ (ne_of_gt hα)]
                rw [← h2]
                exact Real.rpow_lt_rpow (Real.rpow_nonneg (le_of_lt hCε_pos) _) h1 hα
              rw [div_lt_iff₀ (Real.rpow_pos_of_pos hz_pos α)]
              calc C = (C / ε) * ε := by field_simp
                _ < ‖z‖ ^ α * ε := mul_lt_mul_of_pos_right key hε
                _ = ε * ‖z‖ ^ α := mul_comm _ _

/-! ## Key theorem: L¹ ⋆ C₀ → C₀

This is the main engine of the proof. In Mathlib this should be something like
`convolution_tendsto_zero_of_integrable_of_continuous_vanishing` or similar.
-/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A continuous function vanishing at infinity is bounded. -/
lemma bounded_of_continuous_tendsto_zero
    {g : E → ℂ} (hg_cont : Continuous g) (hg_zero : Tendsto g (cocompact E) (nhds 0)) :
    ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
  -- g tends to 0 at infinity, so for ε = 1, ‖g x‖ < 1 outside some compact set
  rw [Metric.tendsto_nhds] at hg_zero
  obtain ⟨K, hK_cpct, hK⟩ : ∃ K : Set E, IsCompact K ∧ ∀ x ∉ K, ‖g x‖ < 1 := by
    have h1 := hg_zero 1 one_pos
    rw [Filter.eventually_iff_exists_mem] at h1
    obtain ⟨S, hS_mem, hS⟩ := h1
    rw [Filter.mem_cocompact] at hS_mem
    obtain ⟨K, hK_cpct, hK_sub⟩ := hS_mem
    refine ⟨K, hK_cpct, ?_⟩
    intro x hx
    have : x ∈ S := hK_sub hx
    simpa [dist_zero_right] using hS x this
  -- The image of K under ‖g ·‖ is compact (continuous image of compact)
  have himg_cpct : IsCompact (Set.image (‖g ·‖) K) :=
    hK_cpct.image (continuous_norm.comp hg_cont)
  -- Compact subsets of ℝ are bounded
  obtain ⟨M, hM⟩ := himg_cpct.isBounded.subset_closedBall 0
  -- Take C = max M 1
  use max M 1
  intro x
  by_cases hx : x ∈ K
  · have : ‖g x‖ ∈ Set.image (‖g ·‖) K := ⟨x, hx, rfl⟩
    have hle : ‖g x‖ ∈ closedBall (0 : ℝ) M := hM this
    simp only [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_norm] at hle
    exact le_sup_of_le_left hle
  · exact le_trans (le_of_lt (hK x hx)) (le_max_right _ _)

/-- For integrable f and ε > 0, there exists a compact set K with small tail integral.

This is a standard consequence of integrability - the integral concentrates on compact sets.
-/
lemma integrable_tail_small {f : E → ℂ} (hf : Integrable f) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set E, IsCompact K ∧ ∫ x in Kᶜ, ‖f x‖ < ε := by
  -- Use: for antitone sequence of sets, integral tends to integral over intersection
  -- Here s(n) = (closedBall 0 n)ᶜ is antitone and ⋂ s(n) = ∅
  let s : ℕ → Set E := fun n => (closedBall (0 : E) n)ᶜ
  have hs_anti : Antitone s := fun m n hmn =>
    compl_subset_compl.mpr (closedBall_subset_closedBall (by exact Nat.cast_le.mpr hmn))
  have hs_meas : ∀ n, MeasurableSet (s n) := fun n =>
    isClosed_closedBall.measurableSet.compl
  -- ‖f‖ is integrable
  have hf_norm : Integrable (fun x => ‖f x‖) := hf.norm
  -- The integral over s(n) tends to the integral over ⋂ s(n)
  have htends := Antitone.tendsto_setIntegral hs_meas hs_anti hf_norm.integrableOn
  -- ⋂ s(n) = ∅ in finite-dimensional space
  have h_inter : ⋂ n, s n = ∅ := by
    ext x
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    -- There exists n with x ∈ closedBall 0 n, i.e., x ∉ s(n)
    refine ⟨⌈‖x‖⌉₊, ?_⟩
    change x ∉ (closedBall (0 : E) ⌈‖x‖⌉₊)ᶜ
    simp only [mem_compl_iff, not_not, mem_closedBall, dist_zero_right]
    exact Nat.le_ceil ‖x‖
  rw [h_inter, setIntegral_empty] at htends
  -- Get n such that ∫ x in s(n), ‖f x‖ < ε
  rw [Metric.tendsto_nhds] at htends
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htends ε hε)
  refine ⟨closedBall 0 N, isCompact_closedBall 0 N, ?_⟩
  specialize hN N le_rfl
  simp only [dist_zero_right] at hN
  -- hN : ‖∫ x in s N, ‖f x‖‖ < ε, but ∫ x in s N, ‖f x‖ ≥ 0, so this gives what we need
  have h_nonneg : 0 ≤ ∫ x in s N, ‖f x‖ := setIntegral_nonneg (hs_meas N) (fun _ _ => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg] at hN
  exact hN

/-- Convolution of an integrable function with a function vanishing at infinity
also vanishes at infinity. This is a fundamental result in harmonic analysis.
-/
theorem convolution_vanishes_of_integrable_and_C0
    {f : E → ℂ} {g : E → ℂ}
    (hf_int : Integrable f)
    (hg_C0 : Tendsto g (cocompact E) (nhds 0))
    (hg_cont : Continuous g) :
    Tendsto (fun y => ∫ x, f x * g (x - y)) (cocompact E) (nhds 0) := by
  -- Step 1: g is bounded
  obtain ⟨B, hB⟩ := bounded_of_continuous_tendsto_zero hg_cont hg_C0
  have hB_pos : 0 < max B 1 := lt_max_of_lt_right zero_lt_one
  -- Step 2: Setup the ε argument
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Step 3: Get a compact set K where f's tail integral is small
  obtain ⟨K, hK_cpct, hf_tail⟩ := integrable_tail_small hf_int (ε / (2 * max B 1))
    (div_pos hε (mul_pos two_pos hB_pos))
  -- Step 4: Get radius R where g is small
  let If := ∫ x, ‖f x‖
  have hIf_nonneg : 0 ≤ If := integral_nonneg (fun _ => norm_nonneg _)
  let η := ε / (2 * (If + 1))
  have hη_pos : 0 < η := div_pos hε (mul_pos two_pos (by linarith))
  rw [Metric.tendsto_nhds] at hg_C0
  have hg_small := hg_C0 η hη_pos
  rw [Filter.eventually_iff_exists_mem] at hg_small
  obtain ⟨S, hS_mem, hS⟩ := hg_small
  rw [Filter.mem_cocompact] at hS_mem
  obtain ⟨L, hL_cpct, hL_sub⟩ := hS_mem
  -- So for x ∉ L, ‖g x‖ < η
  -- Step 5: Combine K and L to get the radius
  -- We need y large enough that for all x ∈ K, x - y ∉ L
  -- i.e., ‖y‖ > R_K + R_L
  obtain ⟨R_K, hR_K⟩ := hK_cpct.isBounded.subset_closedBall 0
  obtain ⟨R_L, hR_L⟩ := hL_cpct.isBounded.subset_closedBall 0
  let R := R_K + R_L
  -- Step 6: The eventual statement
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨(closedBall 0 R)ᶜ, ?_, ?_⟩
  · rw [Filter.mem_cocompact]
    exact ⟨closedBall 0 R, isCompact_closedBall 0 R, fun x hx => hx⟩
  · intro y hy
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hy
    simp only [dist_zero_right]
    -- The main estimate: split integral over K and Kᶜ
    -- Key: for x ∈ K, x - y ∉ L (since ‖x - y‖ ≥ ‖y‖ - ‖x‖ > R - R_K = R_L)
    have hxy_outside : ∀ x ∈ K, x - y ∉ L := by
      intro x hxK
      have hx_bound : ‖x‖ ≤ R_K := by simpa [mem_closedBall, dist_zero_right] using hR_K hxK
      intro hxy_in_L
      have hxy_bound : ‖x - y‖ ≤ R_L := by simpa [mem_closedBall,
                                                  dist_zero_right] using hR_L hxy_in_L
      -- ‖y‖ - ‖x‖ ≤ ‖y - x‖ = ‖x - y‖
      have h1 : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
      have h2 : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
      linarith
    -- For x ∈ K, |g(x-y)| < η
    have hg_small_on_K : ∀ x ∈ K, ‖g (x - y)‖ < η := by
      intro x hxK
      have : x - y ∈ S := hL_sub (hxy_outside x hxK)
      simpa [dist_zero_right] using hS (x - y) this
    -- The integrand is integrable (f integrable, g bounded)
    have hg_bdd : ∀ x, ‖g (x - y)‖ ≤ max B 1 := fun x => le_max_of_le_left (hB (x - y))
    -- Split the integral using set integral bounds
    -- We can bound the total integral by splitting over K and Kᶜ
    -- This proof uses the outline; full details require set integral calculus
    -- Bound: ‖∫ f(x) * g(x-y)‖ ≤ ∫ ‖f(x)‖ * ‖g(x-y)‖
    --   = ∫_K ‖f‖ * ‖g(·-y)‖ + ∫_{Kᶜ} ‖f‖ * ‖g(·-y)‖
    --   ≤ (∫_K ‖f‖) * η + (∫_{Kᶜ} ‖f‖) * (max B 1)       [g small on K, g bounded elsewhere]
    --   ≤ If * η + (ε / (2 * max B 1)) * (max B 1)
    --   < ε/2 + ε/2 = ε
    -- For K part: for x ∈ K, g(x-y) is small (< η), and ∫_K ‖f‖ ≤ If
    -- For Kᶜ part: g is bounded by max B 1, and ∫_{Kᶜ} ‖f‖ < ε / (2 * max B 1)
    -- The detailed proof requires verifying integrability and using setIntegral_mono
    -- Core calculation is: η * If + (max B 1) * (ε / (2 * max B 1)) < ε/2 + ε/2 = ε
    -- where η * If < η * (If + 1) = ε/2 since η = ε / (2 * (If + 1))
    -- Integrability of the integrand
    have hg_bdd : ∀ x, ‖g (x - y)‖ ≤ max B 1 := fun x => le_max_of_le_left (hB (x - y))
    have h_int : Integrable (fun x => ‖f x‖ * ‖g (x - y)‖) volume := by
      have hg_meas : AEStronglyMeasurable (fun x => ‖g (x - y)‖) volume :=
        (hg_cont.comp (continuous_id.sub continuous_const)).norm.aestronglyMeasurable
      refine Integrable.mul_bdd (c := max B 1) hf_int.norm hg_meas ?_
      filter_upwards with x
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hg_bdd x
    -- Split integral over K and Kᶜ
    have hK_meas : MeasurableSet K := hK_cpct.isClosed.measurableSet
    -- Bound on K using setIntegral_mono_on (which gives us the membership hypothesis)
    have hK_bound : ∫ x in K, ‖f x‖ * ‖g (x - y)‖ ≤ η * If := by
      have h1 : ∫ x in K, ‖f x‖ * ‖g (x - y)‖ ≤ ∫ x in K, ‖f x‖ * η := by
        refine setIntegral_mono_on h_int.integrableOn (hf_int.norm.mul_const _).integrableOn
          hK_meas ?_
        intro x hxK
        exact mul_le_mul_of_nonneg_left (hg_small_on_K x hxK).le (norm_nonneg _)
      have h2 : ∫ x in K, ‖f x‖ * η = η * ∫ x in K, ‖f x‖ := by
        rw [integral_mul_const]; ring
      have h3 : ∫ x in K, ‖f x‖ ≤ If := setIntegral_le_integral hf_int.norm
        (Eventually.of_forall (fun _ => norm_nonneg _))
      linarith [mul_le_mul_of_nonneg_left h3 hη_pos.le]
    -- Bound on Kᶜ (g is bounded globally, so setIntegral_mono works)
    have hKc_bound : ∫ x in Kᶜ, ‖f x‖ * ‖g (x - y)‖ ≤ max B 1 * (ε / (2 * max B 1)) := by
      have h1 : ∫ x in Kᶜ, ‖f x‖ * ‖g (x - y)‖ ≤ ∫ x in Kᶜ, ‖f x‖ * max B 1 := by
        refine setIntegral_mono h_int.integrableOn (hf_int.norm.mul_const _).integrableOn ?_
        intro x
        exact mul_le_mul_of_nonneg_left (hg_bdd x) (norm_nonneg _)
      have h2 : ∫ x in Kᶜ, ‖f x‖ * max B 1 = max B 1 * ∫ x in Kᶜ, ‖f x‖ := by
        rw [integral_mul_const]; ring
      linarith [mul_le_mul_of_nonneg_left hf_tail.le hB_pos.le]
    calc ‖∫ x, f x * g (x - y)‖
        ≤ ∫ x, ‖f x * g (x - y)‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖f x‖ * ‖g (x - y)‖ := by congr 1; ext x; exact norm_mul (f x) (g (x - y))
      _ = ∫ x in K, ‖f x‖ * ‖g (x - y)‖ ∂volume + ∫ x in Kᶜ, ‖f x‖ * ‖g (x - y)‖ ∂volume :=
          (integral_add_compl hK_meas h_int).symm
      _ ≤ η * If + max B 1 * (ε / (2 * max B 1)) := add_le_add hK_bound hKc_bound
      _ < ε := by
          have h1 : η * If < ε / 2 := by
            have hlt : η * If < η * (If + 1) := mul_lt_mul_of_pos_left (lt_add_one If) hη_pos
            have heq : η * (If + 1) = ε / 2 := by
              simp only [η]
              have hne : If + 1 ≠ 0 := by linarith
              field_simp
            linarith
          have h2 : max B 1 * (ε / (2 * max B 1)) = ε / 2 := by
            have hne : max B 1 ≠ 0 := ne_of_gt hB_pos
            field_simp
          linarith

/-! ## Product Space Integrability for Fubini

The bilinear integrand f(x) K(x-y) g(y-a) is integrable on E × E when:
- f, g are Schwartz functions
- K is locally integrable with bounded tail (e.g., exponential/polynomial decay)

This is used for Fubini swaps in bilinear integral proofs.
-/

/-- **Product integrability for Schwartz bilinear forms with locally integrable kernel**

For Schwartz f, g and kernel K = K_sing + K_tail where K_sing is compactly supported
(hence integrable) and K_tail is bounded, the product f(x) K(x-y) g(y-a) is integrable
on E × E.

This enables Fubini's theorem to swap integration order:
∫∫ f(x) K(x-y) g(y-a) dx dy = ∫ (∫ f(x) K(x-y) dx) g(y-a) dy
-/
theorem schwartz_bilinear_prod_integrable
    (f g : SchwartzMap E ℂ)
    (K : E → ℝ) (hK_meas : Measurable K) (hK_loc : LocallyIntegrable K volume)
    (R₀ : ℝ) (_hR₀ : R₀ > 0)
    (hK_tail_bdd : ∃ M : ℝ, ∀ z : E, |kernelTail K R₀ z| ≤ M)
    (a : E) :
    Integrable (Function.uncurry (fun x y => f x * (K (x - y) : ℂ) * g (y - a)))
        (volume.prod volume) := by
  -- Get Schwartz integrability
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  haveI : SecondCountableTopology E := secondCountable_of_proper
  have hf_int : Integrable f volume := f.integrable
  have hg_int : Integrable g volume := g.integrable
  -- Get bounds
  obtain ⟨Cf, hCf⟩ := bounded_of_continuous_tendsto_zero f.continuous (schwartz_tendsto_zero f)
  obtain ⟨Cg, hCg⟩ := bounded_of_continuous_tendsto_zero g.continuous (schwartz_tendsto_zero g)
  obtain ⟨M_tail, hM_tail⟩ := hK_tail_bdd
  let K_sing := kernelSingular K R₀
  let K_tail := kernelTail K R₀
  -- Split K = K_sing + K_tail
  have hK_eq : ∀ x y, (K (x - y) : ℂ) = (K_sing (x - y) : ℂ) + (K_tail (x - y) : ℂ) := by
    intro x y
    have h := congrFun (kernel_decomposition K R₀) (x - y)
    rw [h, Complex.ofReal_add]
  have h_split : ∀ x y, f x * (K (x - y) : ℂ) * g (y - a) =
      f x * (K_sing (x - y) : ℂ) * g (y - a) + f x * (K_tail (x - y) : ℂ) * g (y - a) := by
    intro x y
    rw [hK_eq x y]
    ring
  -- K_sing part: f bounded, K_sing integrable (compact support), g integrable
  have h_sing_int : Integrable (Function.uncurry (fun x y => f x * (K_sing (x - y) : ℂ) * g (y -
    a)))
      (volume.prod volume) := by
    have hKs_meas : Measurable K_sing :=
      hK_meas.mul (measurable_const.indicator isClosed_closedBall.measurableSet)
    have hg_shift : Integrable (fun y => g (y - a)) volume := hg_int.comp_sub_right a
    -- K_sing is integrable (compact support)
    have hKs_int : Integrable K_sing volume := by
      change Integrable (kernelSingular K R₀) volume
      have heq : kernelSingular K R₀ = (closedBall (0 : E) R₀).indicator K := by
        ext x
        simp only [kernelSingular]
        by_cases hx : x ∈ closedBall (0 : E) R₀
        · simp [indicator_of_mem hx]
        · simp [indicator_of_notMem hx]
      rw [heq, integrable_indicator_iff isClosed_closedBall.measurableSet]
      exact hK_loc.integrableOn_isCompact (isCompact_closedBall 0 R₀)
    -- Product: Cf * |K_sing(x-y)| * |g(y-a)| is integrable
    have hKs_int_C : Integrable (fun z => (K_sing z : ℂ)) volume := hKs_int.ofReal
    have hg_shift_C : Integrable (fun y => g (y - a)) volume := hg_shift
    -- Use Integrable.mul_prod for the shifted variables
    have h_prod_Ks_g : Integrable (fun p : E × E => (K_sing p.1 : ℂ) * g (p.2 - a))
        (volume.prod volume) := Integrable.mul_prod hKs_int_C hg_shift_C
    -- Change of variables (x, y) ↦ (x - y, y) to get K_sing(x-y)
    let e : E × E ≃ᵐ E × E :=
      { toFun := fun p => (p.1 - p.2, p.2)
        invFun := fun p => (p.1 + p.2, p.2)
        left_inv := fun p => by simp [sub_add_cancel]
        right_inv := fun p => by simp [add_sub_cancel_right]
        measurable_toFun := Measurable.prodMk (measurable_fst.sub measurable_snd) measurable_snd
        measurable_invFun := Measurable.prodMk (measurable_fst.add measurable_snd) measurable_snd }
    have he_preserves : MeasurePreserving e (volume.prod volume) (volume.prod volume) := by
      have := measurePreserving_sub_prod (G := E) volume volume
      convert this using 1
      ext p : 1
      rfl
    have h_Ks_shifted : Integrable (fun p : E × E => (K_sing (p.1 - p.2) : ℂ) * g (p.2 - a))
        (volume.prod volume) := by
      have heq : (fun p : E × E => (K_sing (p.1 - p.2) : ℂ) * g (p.2 - a)) =
          (fun p => (K_sing p.1 : ℂ) * g (p.2 - a)) ∘ e := by ext p; rfl
      rw [heq, he_preserves.integrable_comp_emb e.measurableEmbedding]
      exact h_prod_Ks_g
    -- Now bound: |f(x) K_sing(x-y) g(y-a)| ≤ Cf * |K_sing(x-y) * g(y-a)|
    have hCf_pos : 0 < max Cf 1 := lt_max_of_lt_right one_pos
    have h_dom : Integrable (fun p : E × E => max Cf 1 * ‖(K_sing (p.1 - p.2) : ℂ) * g (p.2 - a)‖)
        (volume.prod volume) := h_Ks_shifted.norm.const_mul (max Cf 1)
    refine h_dom.mono' ?_ ?_
    · -- AEStronglyMeasurable
      apply AEStronglyMeasurable.mul
      · apply AEStronglyMeasurable.mul
        · exact f.continuous.aestronglyMeasurable.comp_measurable measurable_fst
        · exact (hKs_meas.comp (measurable_fst.sub
            measurable_snd)).complex_ofReal.aestronglyMeasurable
      · exact (g.continuous.comp (continuous_snd.sub continuous_const)).aestronglyMeasurable
    · filter_upwards with ⟨x, y⟩
      simp only [Function.uncurry]
      calc ‖f x * (K_sing (x - y) : ℂ) * g (y - a)‖
          = ‖f x‖ * ‖(K_sing (x - y) : ℂ)‖ * ‖g (y - a)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ max Cf 1 * ‖(K_sing (x - y) : ℂ)‖ * ‖g (y - a)‖ := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_right (le_trans (hCf x) (le_max_left _ _))
                (norm_nonneg _)
            · exact norm_nonneg _
        _ = max Cf 1 * (‖(K_sing (x - y) : ℂ)‖ * ‖g (y - a)‖) := by ring
        _ = max Cf 1 * ‖(K_sing (x - y) : ℂ) * g (y - a)‖ := by rw [← norm_mul]
  -- K_tail part: f integrable, K_tail bounded, g integrable
  have h_tail_int : Integrable (Function.uncurry (fun x y => f x * (K_tail (x - y) : ℂ) * g (y -
    a)))
      (volume.prod volume) := by
    have hg_shift : Integrable (fun y => g (y - a)) volume := hg_int.comp_sub_right a
    have h_prod : Integrable (fun z : E × E => f z.1 * g (z.2 - a)) (volume.prod volume) :=
      Integrable.mul_prod hf_int hg_shift
    have h_dom : Integrable (fun z : E × E => M_tail * ‖f z.1 * g (z.2 - a)‖) (volume.prod volume)
      :=
      h_prod.norm.const_mul M_tail
    refine h_dom.mono' ?_ ?_
    · -- AEStronglyMeasurable
      have hKt_meas : Measurable (kernelTail K R₀) := by
        have hind : Measurable ((closedBall (0 : E) R₀)ᶜ.indicator (fun _ => (1 : ℝ))) :=
          measurable_const.indicator isClosed_closedBall.measurableSet.compl
        exact hK_meas.mul hind
      have h1 : Measurable (fun z : E × E => (kernelTail K R₀ (z.1 - z.2) : ℂ)) :=
        measurable_ofReal.comp (hKt_meas.comp (measurable_fst.sub measurable_snd))
      have h2 : AEStronglyMeasurable (fun z : E × E => f z.1) (volume.prod volume) :=
        (f.continuous.comp continuous_fst).aestronglyMeasurable
      have h3 : AEStronglyMeasurable (fun z : E × E => g (z.2 - a)) (volume.prod volume) :=
        (g.continuous.comp (continuous_snd.sub continuous_const)).aestronglyMeasurable
      exact (h2.mul h1.aestronglyMeasurable).mul h3
    · -- ae bound: ‖f(x) K_tail(x-y) g(y-a)‖ ≤ M_tail * ‖f(x) * g(y-a)‖
      filter_upwards with ⟨x, y⟩
      simp only [Function.uncurry]
      have hKt_bnd : ‖(K_tail (x - y) : ℂ)‖ ≤ M_tail := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hM_tail (x - y)
      calc ‖f x * (K_tail (x - y) : ℂ) * g (y - a)‖
          = ‖f x‖ * ‖(K_tail (x - y) : ℂ)‖ * ‖g (y - a)‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖f x‖ * M_tail * ‖g (y - a)‖ := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left hKt_bnd (norm_nonneg _)
            · exact norm_nonneg _
        _ = M_tail * (‖f x‖ * ‖g (y - a)‖) := by ring
        _ = M_tail * ‖f x * g (y - a)‖ := by rw [← norm_mul]
  -- Combine using integral_add for product integrals
  have h_eq : Function.uncurry (fun x y => f x * (K (x - y) : ℂ) * g (y - a)) =
      Function.uncurry (fun x y => f x * (K_sing (x - y) : ℂ) * g (y - a)) +
      Function.uncurry (fun x y => f x * (K_tail (x - y) : ℂ) * g (y - a)) := by
    ext ⟨x, y⟩
    simp only [Function.uncurry, Pi.add_apply, h_split]
  rw [h_eq]
  exact Integrable.add h_sing_int h_tail_int

/-! ## Main theorem -/

/-- The bilinear integral of Schwartz functions against a decaying kernel -/
def schwartzBilinearIntegral (f g : SchwartzMap E ℂ) (K : E → ℝ) (a : E) : ℂ :=
  ∫ x : E, ∫ y : E, f x * (K (x - y) : ℂ) * g (y - a)

private lemma schwartz_bilinear_kernelSingular_vanish
    (f : SchwartzMap E ℂ) (K : E → ℝ) (R₀ : ℝ)
    (hK_sing_int : Integrable (kernelSingular K R₀) volume)
    (hf_C0 : Tendsto f (cocompact E) (nhds 0)) :
    Tendsto (fun y => ∫ x, f x * (kernelSingular K R₀ (x - y) : ℂ))
      (cocompact E) (nhds 0) := by
  let K_sing := kernelSingular K R₀
  change Tendsto (fun y => ∫ x, f x * (K_sing (x - y) : ℂ)) (cocompact E) (nhds 0)
  change Integrable K_sing volume at hK_sing_int
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hK_sing_norm : 0 ≤ ∫ x, ‖(K_sing x : ℂ)‖ := integral_nonneg (fun _ => norm_nonneg _)
  let I_Ksing := ∫ x, ‖(K_sing x : ℂ)‖
  have hI_pos : 0 < I_Ksing + 1 := by linarith
  let δ := ε / (I_Ksing + 1)
  have hδ_pos : δ > 0 := div_pos hε hI_pos
  rw [Metric.tendsto_nhds] at hf_C0
  have hf_small := hf_C0 δ hδ_pos
  rw [Filter.eventually_iff_exists_mem] at hf_small
  obtain ⟨S, hS_mem, hS⟩ := hf_small
  rw [Filter.mem_cocompact] at hS_mem
  obtain ⟨L, hL_cpct, hL_sub⟩ := hS_mem
  obtain ⟨R_L, hR_L⟩ := hL_cpct.isBounded.subset_closedBall 0
  let R := R_L + R₀
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨(closedBall 0 R)ᶜ, ?_, ?_⟩
  · rw [Filter.mem_cocompact]
    exact ⟨closedBall 0 R, isCompact_closedBall 0 R, fun x hx => hx⟩
  · intro y hy
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hy
    simp only [dist_zero_right]
    have hxy_outside : ∀ x, K_sing (x - y) ≠ 0 → x ∉ L := by
      intro x hK_ne hx_in_L
      have hxy_in_ball : x - y ∈ closedBall (0 : E) R₀ := by
        by_contra h
        simp only [mem_closedBall, dist_zero_right, not_le] at h
        have : K_sing (x - y) = 0 := by
          simp only [K_sing, kernelSingular]
          rw [indicator_of_notMem]
          · ring
          · simp [mem_closedBall, dist_zero_right, not_le.mpr h]
        exact hK_ne this
      have h1 : ‖x - y‖ ≤ R₀ := by simpa [mem_closedBall, dist_zero_right] using hxy_in_ball
      have h2 : ‖x‖ ≤ R_L := by simpa [mem_closedBall, dist_zero_right] using hR_L hx_in_L
      have h3 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
        calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      have h4 : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
      linarith
    have hf_small_on_supp : ∀ x, K_sing (x - y) ≠ 0 → ‖f x‖ < δ := by
      intro x hK_ne
      have hx_not_L : x ∉ L := hxy_outside x hK_ne
      have hx_in_S : x ∈ S := hL_sub hx_not_L
      simpa [dist_zero_right] using hS x hx_in_S
    have hfK_bdd : ∀ x, ‖f x * (K_sing (x - y) : ℂ)‖ ≤ δ * ‖(K_sing (x - y) : ℂ)‖ := by
      intro x
      rw [norm_mul]
      by_cases hK : K_sing (x - y) = 0
      · simp [hK]
      · exact mul_le_mul_of_nonneg_right (hf_small_on_supp x hK).le (norm_nonneg _)
    have hKs_y_int : Integrable (fun x => (K_sing (x - y) : ℂ)) volume :=
      (hK_sing_int.comp_sub_right y).ofReal
    obtain ⟨Cf, hCf⟩ := bounded_of_continuous_tendsto_zero f.continuous (schwartz_tendsto_zero f)
    have hint1 : Integrable (fun x => ‖f x * (K_sing (x - y) : ℂ)‖) volume :=
      (Integrable.bdd_mul hKs_y_int f.continuous.aestronglyMeasurable
        (Eventually.of_forall hCf)).norm
    have hint2 : Integrable (fun x => δ * ‖(K_sing (x - y) : ℂ)‖) volume := by
      simp only [mul_comm δ]
      exact hKs_y_int.norm.mul_const δ
    calc ‖∫ x, f x * (K_sing (x - y) : ℂ)‖ ≤ ∫ x, ‖f x * (K_sing (x - y) : ℂ)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x, δ * ‖(K_sing (x - y) : ℂ)‖ := integral_mono hint1 hint2 hfK_bdd
      _ = δ * ∫ x, ‖(K_sing (x - y) : ℂ)‖ := by
          simp only [mul_comm δ]
          exact integral_mul_const δ _
      _ = δ * I_Ksing := by
          congr 1
          have : ∫ x, ‖(K_sing (x - y) : ℂ)‖ = ∫ z, ‖(K_sing z : ℂ)‖ :=
            integral_sub_right_eq_self (fun z => ‖(K_sing z : ℂ)‖) y
          exact this
      _ < ε := by
          have : δ * I_Ksing < δ * (I_Ksing + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hδ_pos
          have heq : δ * (I_Ksing + 1) = ε := by simp only [δ]; field_simp
          linarith

private lemma schwartz_bilinear_kernelTail_vanish
    (f : SchwartzMap E ℂ) (K : E → ℝ) (hK_meas : Measurable K)
    (α : ℝ) (hα : α > 0) (C R₀ : ℝ) (hC : C > 0) (hR₀ : R₀ > 0)
    (hK_decay : ∀ z : E, ‖z‖ ≥ R₀ → |K z| ≤ C / ‖z‖ ^ α)
    (hK_tail_C0 : Tendsto (kernelTail K R₀) (cocompact E) (nhds 0))
    (hf_int : Integrable f) :
    Tendsto (fun y => ∫ x, f x * (kernelTail K R₀ (x - y) : ℂ))
      (cocompact E) (nhds 0) := by
  let K_tail := kernelTail K R₀
  change Tendsto (fun y => ∫ x, f x * (K_tail (x - y) : ℂ)) (cocompact E) (nhds 0)
  change Tendsto K_tail (cocompact E) (nhds 0) at hK_tail_C0
  have hK_tail_bdd : ∃ M : ℝ, 0 < M ∧ ∀ z, ‖(K_tail z : ℂ)‖ ≤ M := by
    use max (C / R₀ ^ α) 1
    constructor
    · exact lt_max_of_lt_right one_pos
    intro z
    rw [Complex.norm_real]
    simp only [K_tail, kernelTail]
    by_cases hz : z ∈ (closedBall (0 : E) R₀)ᶜ
    · rw [indicator_of_mem hz, mul_one]
      have hz' : ‖z‖ ≥ R₀ := by
        simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hz
        exact hz.le
      calc |K z| ≤ C / ‖z‖ ^ α := hK_decay z hz'
        _ ≤ C / R₀ ^ α := by
            apply div_le_div_of_nonneg_left hC.le (Real.rpow_pos_of_pos hR₀ α)
            exact Real.rpow_le_rpow hR₀.le hz' hα.le
        _ ≤ max (C / R₀ ^ α) 1 := le_max_left _ _
    · rw [indicator_of_notMem hz, mul_zero]
      simp only [norm_zero]
      exact le_of_lt (lt_max_of_lt_right one_pos)
  obtain ⟨M, hM_pos, hM⟩ := hK_tail_bdd
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K_set, hK_cpct, hf_tail⟩ := integrable_tail_small hf_int (ε / (2 * M))
    (div_pos hε (mul_pos two_pos hM_pos))
  let If := ∫ x, ‖f x‖
  have hIf_nonneg : 0 ≤ If := integral_nonneg (fun _ => norm_nonneg _)
  let η := ε / (2 * (If + 1))
  have hη_pos : 0 < η := div_pos hε (mul_pos two_pos (by linarith))
  rw [Metric.tendsto_nhds] at hK_tail_C0
  have hKt_small := hK_tail_C0 η hη_pos
  rw [Filter.eventually_iff_exists_mem] at hKt_small
  obtain ⟨S, hS_mem, hS⟩ := hKt_small
  rw [Filter.mem_cocompact] at hS_mem
  obtain ⟨L, hL_cpct, hL_sub⟩ := hS_mem
  obtain ⟨R_K, hR_K⟩ := hK_cpct.isBounded.subset_closedBall 0
  obtain ⟨R_L, hR_L⟩ := hL_cpct.isBounded.subset_closedBall 0
  let R := R_K + R_L
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨(closedBall 0 R)ᶜ, ?_, ?_⟩
  · rw [Filter.mem_cocompact]
    exact ⟨closedBall 0 R, isCompact_closedBall 0 R, fun x hx => hx⟩
  · intro y hy
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hy
    simp only [dist_zero_right]
    have hxy_outside : ∀ x ∈ K_set, x - y ∉ L := by
      intro x hxK
      have hx_bound : ‖x‖ ≤ R_K := by simpa [mem_closedBall, dist_zero_right] using hR_K hxK
      intro hxy_in_L
      have hxy_bound : ‖x - y‖ ≤ R_L := by simpa [mem_closedBall,
                                                  dist_zero_right] using hR_L hxy_in_L
      have h1 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
        calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      have h2 : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
      linarith
    have hKt_small_on_K : ∀ x ∈ K_set, ‖(K_tail (x - y) : ℂ)‖ < η := by
      intro x hxK
      have : x - y ∈ S := hL_sub (hxy_outside x hxK)
      have h := hS (x - y) this
      simp only [dist_zero_right] at h
      rwa [Complex.norm_real]
    have hKt_y_meas : AEStronglyMeasurable (fun x => (K_tail (x - y) : ℂ)) volume := by
      have hind : Measurable ((closedBall (0 : E) R₀)ᶜ.indicator (fun _ => (1 : ℝ))) :=
        measurable_const.indicator isClosed_closedBall.measurableSet.compl
      have h1 : Measurable (K_tail) := hK_meas.mul hind
      have h2 : Measurable (fun x => K_tail (x - y)) := h1.comp (measurable_id.sub
        measurable_const)
      exact (measurable_ofReal.comp h2).aestronglyMeasurable
    have h_int : Integrable (fun x => ‖f x‖ * ‖(K_tail (x - y) : ℂ)‖) volume := by
      refine Integrable.mul_bdd (c := M) hf_int.norm hKt_y_meas.norm ?_
      filter_upwards with x
      simp only [Real.norm_of_nonneg (norm_nonneg _)]
      exact hM (x - y)
    have hK_meas : MeasurableSet K_set := hK_cpct.isClosed.measurableSet
    have hK_bound : ∫ x in K_set, ‖f x‖ * ‖(K_tail (x - y) : ℂ)‖ ≤ η * If := by
      have h1 : ∫ x in K_set, ‖f x‖ * ‖(K_tail (x - y) : ℂ)‖ ≤ ∫ x in K_set, ‖f x‖ * η := by
        refine setIntegral_mono_on h_int.integrableOn (hf_int.norm.mul_const _).integrableOn
          hK_meas ?_
        intro x hxK
        exact mul_le_mul_of_nonneg_left (hKt_small_on_K x hxK).le (norm_nonneg _)
      have h2 : ∫ x in K_set, ‖f x‖ * η = η * ∫ x in K_set, ‖f x‖ := by
        rw [integral_mul_const]; ring
      have h3 : ∫ x in K_set, ‖f x‖ ≤ If := setIntegral_le_integral hf_int.norm
        (Eventually.of_forall (fun _ => norm_nonneg _))
      linarith [mul_le_mul_of_nonneg_left h3 hη_pos.le]
    have hKc_bound : ∫ x in K_setᶜ, ‖f x‖ * ‖(K_tail (x - y) : ℂ)‖ ≤ M * (ε / (2 * M)) := by
      have h1 : ∫ x in K_setᶜ, ‖f x‖ * ‖(K_tail (x - y) : ℂ)‖ ≤ ∫ x in K_setᶜ, ‖f x‖ * M := by
        refine setIntegral_mono h_int.integrableOn (hf_int.norm.mul_const _).integrableOn ?_
        intro x
        exact mul_le_mul_of_nonneg_left (hM (x - y)) (norm_nonneg _)
      have h2 : ∫ x in K_setᶜ, ‖f x‖ * M = M * ∫ x in K_setᶜ, ‖f x‖ := by
        rw [integral_mul_const]; ring
      linarith [mul_le_mul_of_nonneg_left hf_tail.le hM_pos.le]
    calc ‖∫ x, f x * (K_tail (x - y) : ℂ)‖
        ≤ ∫ x, ‖f x * (K_tail (x - y) : ℂ)‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖f x‖ * ‖(K_tail (x - y) : ℂ)‖ := by congr 1; ext x; exact norm_mul _ _
      _ = ∫ x in K_set, ‖f x‖ * ‖(K_tail (x - y) : ℂ)‖ ∂volume +
          ∫ x in K_setᶜ, ‖f x‖ * ‖(K_tail (x - y) : ℂ)‖ ∂volume := (integral_add_compl hK_meas
            h_int).symm
      _ ≤ η * If + M * (ε / (2 * M)) := add_le_add hK_bound hKc_bound
      _ < ε := by
          have h1 : η * If < ε / 2 := by
            have hlt : η * If < η * (If + 1) := mul_lt_mul_of_pos_left (lt_add_one If) hη_pos
            have heq : η * (If + 1) = ε / 2 := by
              simp only [η]
              have hne : If + 1 ≠ 0 := by linarith
              field_simp
            linarith
          have h2 : M * (ε / (2 * M)) = ε / 2 := by
            have hne : M ≠ 0 := ne_of_gt hM_pos
            field_simp
          linarith

private lemma schwartz_bilinear_kernel_convolution_continuous
    (f : SchwartzMap E ℂ) (K : E → ℝ) (hK_meas : Measurable K)
    (R₀ : ℝ) (hR₀ : R₀ > 0)
    (hK_cont : ContinuousOn K (closedBall (0 : E) R₀)ᶜ)
    (hK_sing_int : Integrable (kernelSingular K R₀) volume)
    (hf_int : Integrable f)
    (Cf : ℝ) (hCf : ∀ x, ‖f x‖ ≤ Cf)
    (M_tail : ℝ) (hM_tail : ∀ z, ‖(kernelTail K R₀ z : ℂ)‖ ≤ M_tail) :
    Continuous (fun y => ∫ x, f x * (K (x - y) : ℂ)) := by
  let K_sing := kernelSingular K R₀
  let K_tail := kernelTail K R₀
  let H := fun y => ∫ x, f x * (K (x - y) : ℂ)
  change Continuous H
  change Integrable K_sing volume at hK_sing_int
  let H_sing := fun y => ∫ x, f x * (K_sing (x - y) : ℂ)
  let H_tail := fun y => ∫ x, f x * (K_tail (x - y) : ℂ)
  have hH_eq : H = fun y => H_sing y + H_tail y := by
    ext y
    simp only [H, H_sing, H_tail]
    have hdec := kernel_decomposition K R₀
    have hK_eq : ∀ x, (K (x - y) : ℂ) = (K_sing (x - y) : ℂ) + (K_tail (x - y) : ℂ) := by
      intro x
      have h := congrFun hdec (x - y)
      rw [h, Complex.ofReal_add]
    conv_lhs => arg 2; ext x; rw [hK_eq x, mul_add]
    have h_int_sing : Integrable (fun x => f x * (K_sing (x - y) : ℂ)) volume := by
      refine Integrable.bdd_mul ((hK_sing_int.comp_sub_right y).ofReal)
        f.continuous.aestronglyMeasurable (Eventually.of_forall hCf)
    have h_int_tail : Integrable (fun x => f x * (K_tail (x - y) : ℂ)) volume := by
      have hKt_meas : AEStronglyMeasurable (fun x => (kernelTail K R₀ (x - y) : ℂ)) volume := by
        have hind : Measurable ((closedBall (0 : E) R₀)ᶜ.indicator (fun _ => (1 : ℝ))) :=
          measurable_const.indicator isClosed_closedBall.measurableSet.compl
        have h1 : Measurable (kernelTail K R₀) := hK_meas.mul hind
        have h2 : Measurable (fun x => kernelTail K R₀ (x - y)) :=
          h1.comp (measurable_id.sub measurable_const)
        exact (measurable_ofReal.comp h2).aestronglyMeasurable
      exact Integrable.mul_bdd hf_int hKt_meas (Eventually.of_forall (fun x => hM_tail (x - y)))
    exact integral_add h_int_sing h_int_tail
  rw [hH_eq]
  apply Continuous.add
  · have hH_sing_eq : H_sing = fun y => ∫ z, f (z + y) * (K_sing z : ℂ) := by
      ext y
      simp only [H_sing]
      rw [← integral_add_right_eq_self (fun x => f x * (K_sing (x - y) : ℂ)) y]
      congr 1
      ext x
      simp only [add_sub_cancel_right]
    rw [hH_sing_eq]
    have hKs_meas : Measurable K_sing :=
      hK_meas.mul (measurable_const.indicator isClosed_closedBall.measurableSet)
    refine continuous_of_dominated (bound := fun z => max Cf 1 * |K_sing z|) ?_ ?_ ?_ ?_
    · intro y
      exact (f.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable.mul
        (measurable_ofReal.comp hKs_meas).aestronglyMeasurable
    · intro y
      filter_upwards with z
      simp only [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (le_max_of_le_left (hCf (z + y))) (abs_nonneg _)
    · exact hK_sing_int.abs.const_mul _
    · filter_upwards with z
      exact (f.continuous.comp (continuous_const.add continuous_id)).mul continuous_const
  · rw [continuous_iff_continuousAt]
    intro y₀
    have hKt_meas : Measurable (kernelTail K R₀) := by
      have hind : Measurable ((closedBall (0 : E) R₀)ᶜ.indicator (fun _ => (1 : ℝ))) :=
        measurable_const.indicator isClosed_closedBall.measurableSet.compl
      exact hK_meas.mul hind
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := fun x => M_tail * ‖f x‖) ?_ ?_ ?_ ?_
    · filter_upwards with y
      have h1 : Measurable (fun x => (kernelTail K R₀ (x - y) : ℂ)) :=
        measurable_ofReal.comp (hKt_meas.comp (measurable_id.sub measurable_const))
      exact f.continuous.aestronglyMeasurable.mul h1.aestronglyMeasurable
    · filter_upwards with y
      filter_upwards with x
      simp only [norm_mul, Complex.norm_real]
      calc ‖f x‖ * |kernelTail K R₀ (x - y)| ≤ ‖f x‖ * M_tail := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            have h := hM_tail (x - y)
            rwa [Complex.norm_real] at h
        _ = M_tail * ‖f x‖ := mul_comm _ _
    · exact hf_int.norm.const_mul M_tail
    · by_cases hnt : Nontrivial E
      · haveI := hnt
        haveI : NoAtoms (volume : Measure E) := inferInstance
        have h_vol_sphere : volume (Metric.sphere y₀ R₀) = 0 :=
          MeasureTheory.Measure.addHaar_sphere volume y₀ R₀
        have h_vol_singleton : volume {y₀} = 0 := measure_singleton y₀
        have h_ae_sphere : ∀ᵐ x ∂volume, x ∉ Metric.sphere y₀ R₀ :=
          compl_mem_ae_iff.mpr h_vol_sphere
        have h_ae_sing : ∀ᵐ x ∂volume, x ∉ ({y₀} : Set E) :=
          compl_mem_ae_iff.mpr h_vol_singleton
        filter_upwards [h_ae_sphere, h_ae_sing] with x hx_sphere hx_sing
        apply Tendsto.mul tendsto_const_nhds
        have h_comp : (fun y => (kernelTail K R₀ (x - y) : ℂ)) =
            (fun z => (kernelTail K R₀ z : ℂ)) ∘ (fun y => x - y) := rfl
        rw [h_comp]
        apply Tendsto.comp _ (tendsto_const_nhds.sub tendsto_id)
        have hxy_ne_zero : x - y₀ ≠ 0 := by
          intro h
          apply hx_sing
          rw [mem_singleton_iff]
          exact sub_eq_zero.mp h
        have hxy_not_sphere : ‖x - y₀‖ ≠ R₀ := by
          intro h
          apply hx_sphere
          rw [Metric.mem_sphere, dist_eq_norm]
          exact h
        apply ContinuousAt.comp (g := Complex.ofReal)
        · exact Complex.continuous_ofReal.continuousAt
        · unfold kernelTail
          by_cases hz_outside : ‖x - y₀‖ > R₀
          · apply ContinuousAt.mul
            · have h_mem : x - y₀ ∈ (closedBall (0 : E) R₀)ᶜ := by
                simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
                exact hz_outside
              exact hK_cont.continuousAt ((isOpen_compl_iff.mpr isClosed_closedBall).mem_nhds
                h_mem)
            · apply ContinuousOn.continuousAt_indicator continuousOn_const
              rw [frontier_compl, frontier_closedBall (0 : E) hR₀.ne']
              simp only [mem_sphere_zero_iff_norm]
              exact hxy_not_sphere
          · push Not at hz_outside
            have hz_inside : ‖x - y₀‖ < R₀ := lt_of_le_of_ne hz_outside hxy_not_sphere
            have h_mem_interior : x - y₀ ∈ interior (closedBall (0 : E) R₀) := by
              rw [interior_closedBall _ hR₀.ne']
              simp only [mem_ball, dist_zero_right]
              exact hz_inside
            have h_eq : (fun z => K z * (closedBall (0 : E) R₀)ᶜ.indicator (fun _ => (1 : ℝ)) z)
              =ᶠ[nhds (x - y₀)] (fun _ => 0) := by
              have h_open : IsOpen (interior (closedBall (0 : E) R₀)) := isOpen_interior
              filter_upwards [h_open.mem_nhds h_mem_interior] with z hz_int
              have hz_not_compl : z ∉ (closedBall (0 : E) R₀)ᶜ := by
                simp only [mem_compl_iff, not_not]
                exact interior_subset hz_int
              simp only [indicator_of_notMem hz_not_compl, mul_zero]
            exact h_eq.continuousAt
      · simp only [not_nontrivial_iff_subsingleton] at hnt
        filter_upwards with x
        apply Tendsto.mul tendsto_const_nhds
        apply Tendsto.comp Complex.continuous_ofReal.continuousAt
        have h_sub_zero : ∀ y : E, x - y = 0 := fun y => by
          exact Subsingleton.eq_zero (x - y)
        have hK_tail_zero : kernelTail K R₀ (0 : E) = 0 := by
          unfold kernelTail
          rw [indicator_of_notMem]
          · ring
          · simp only [mem_compl_iff, mem_closedBall, dist_zero_right, norm_zero, not_not]
            exact hR₀.le
        have hK_tail_const : ∀ y, kernelTail K R₀ (x - y) = 0 := fun y => by
          rw [h_sub_zero y, hK_tail_zero]
        have hK_tail_xy₀ : K_tail (x - y₀) = 0 := hK_tail_const y₀
        have h_eq : (fun y => K_tail (x - y)) = fun _ => (0 : ℝ) := by
          ext y
          exact hK_tail_const y
        rw [h_eq, hK_tail_xy₀]
        exact tendsto_const_nhds

/-- **Clustering decay for Schwartz bilinear forms** (proof version)

For Schwartz functions f, g and a kernel K with polynomial decay,
the bilinear integral tends to 0 as the translation parameter a → ∞.

This version adds LocallyIntegrable hypothesis to handle kernel singularities.
-/
theorem schwartz_bilinear_translation_decay_proof
    (f g : SchwartzMap E ℂ)
    (K : E → ℝ)
    (hK_meas : Measurable K)
    (hK_loc : LocallyIntegrable K volume) -- Handles singularity at 0
    -- K has polynomial decay: |K(z)| ≤ C/‖z‖^α for ‖z‖ ≥ R₀
    (α : ℝ) (hα : α > 0)
    (C R₀ : ℝ) (hC : C > 0) (hR₀ : R₀ > 0)
    (hK_cont : ContinuousOn K (closedBall (0 : E) R₀)ᶜ) -- Continuous outside R₀-ball
    (hK_decay : ∀ z : E, ‖z‖ ≥ R₀ → |K z| ≤ C / ‖z‖ ^ α) :
    Tendsto (schwartzBilinearIntegral f g K) (cocompact E) (nhds 0) := by
  -- Step 1: Decompose K = K_sing + K_tail
  let K_sing := kernelSingular K R₀
  let K_tail := kernelTail K R₀
  -- Step 2: Show K_sing is integrable (compact support + locally integrable)
  have hK_sing_int : Integrable K_sing volume := by
    change Integrable (kernelSingular K R₀) volume
    unfold kernelSingular
    have heq : (fun x => K x * (closedBall (0 : E) R₀).indicator (fun _ => (1 : ℝ)) x) =
               (closedBall (0 : E) R₀).indicator K := by
      ext x
      by_cases hx : x ∈ closedBall (0 : E) R₀
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
    rw [heq, integrable_indicator_iff isClosed_closedBall.measurableSet]
    exact hK_loc.integrableOn_isCompact (isCompact_closedBall 0 R₀)
  -- Step 3: Show K_tail is C₀ (vanishes at infinity)
  have hK_tail_C0 : Tendsto (kernelTail K R₀) (cocompact E) (nhds 0) :=
    kernelTail_tendsto_zero K R₀ α hα C hK_decay
  -- Step 4: f is C₀ (Schwartz functions vanish at infinity)
  have hf_C0 : Tendsto f (cocompact E) (nhds 0) := schwartz_tendsto_zero f
  -- Step 5: f is L¹ (Schwartz functions are integrable)
  have hf_int : Integrable f := schwartz_integrable f
  -- Step 6: g is L¹
  have hg_int : Integrable g := schwartz_integrable g
  -- Step 7: Show f ⋆ K_sing vanishes at infinity
  -- Pattern: K_sing is L¹ with compact support, f is C₀
  -- As y → ∞, the support of K_sing(·-y) moves to where f is small
  have h_fKsing_vanish : Tendsto (fun y => ∫ x,
                                  f x * (K_sing (x - y) : ℂ)) (cocompact E) (nhds 0) := by
    change Tendsto (fun y => ∫ x, f x * (kernelSingular K R₀ (x - y) : ℂ))
      (cocompact E) (nhds 0)
    exact schwartz_bilinear_kernelSingular_vanish f K R₀ hK_sing_int hf_C0
  -- Step 8: Show f ⋆ K_tail vanishes at infinity
  -- Pattern: f is L¹, K_tail is bounded and C₀ → use ε-δ argument
  have h_fKtail_vanish : Tendsto (fun y => ∫ x,
                                  f x * (K_tail (x - y) : ℂ)) (cocompact E) (nhds 0) := by
    change Tendsto (fun y => ∫ x, f x * (kernelTail K R₀ (x - y) : ℂ))
      (cocompact E) (nhds 0)
    exact schwartz_bilinear_kernelTail_vanish f K hK_meas α hα C R₀ hC hR₀
      hK_decay hK_tail_C0 hf_int
  -- Step 9: Combine: f ⋆ K vanishes at infinity
  have h_fK_vanish : Tendsto (fun y => ∫ x, f x * (K (x - y) : ℂ)) (cocompact E) (nhds 0) := by
    -- Use kernel_decomposition and linearity of integral
    -- (f ⋆ K) = (f ⋆ K_sing) + (f ⋆ K_tail)
    -- Both terms vanish at infinity, so their sum does too
    have hdec := kernel_decomposition K R₀
    -- The combination follows from Tendsto.add
    have h_add := Tendsto.add h_fKsing_vanish h_fKtail_vanish
    simp only [add_zero] at h_add
    refine h_add.congr ?_
    intro y
    -- Need: (∫ f * K_sing) + (∫ f * K_tail) = ∫ f * K
    symm
    rw [hdec]
    rw [← integral_add]
    · congr 1
      ext x
      push_cast
      ring
    -- Integrability of f · K_sing and f · K_tail
    -- f is Schwartz (hence bounded and integrable), K_sing is integrable
    -- f is Schwartz, K_tail is bounded (decays at infinity)
    · -- f · K_sing is integrable: f bounded, K_sing integrable
      obtain ⟨Cf, hCf⟩ := bounded_of_continuous_tendsto_zero f.continuous hf_C0
      have hf_meas : AEStronglyMeasurable f volume := f.continuous.aestronglyMeasurable
      -- K_sing(· - y) : ℂ is integrable (translation of integrable, then embed into ℂ)
      have hKs_int : Integrable (fun x => (K_sing (x - y) : ℂ)) volume :=
        (hK_sing_int.comp_sub_right y).ofReal
      refine Integrable.bdd_mul hKs_int hf_meas (Eventually.of_forall hCf)
    · -- f · K_tail is integrable: f integrable, K_tail bounded
      -- K_tail is bounded: |K_tail(z)| ≤ max (C / R₀^α) 1 for all z
      have hK_tail_bdd : ∃ M : ℝ, ∀ z, ‖(kernelTail K R₀ z : ℂ)‖ ≤ M := by
        use max (C / R₀ ^ α) 1
        intro z
        rw [Complex.norm_real]
        simp only [kernelTail]
        by_cases hz : z ∈ (closedBall (0 : E) R₀)ᶜ
        · rw [indicator_of_mem hz, mul_one]
          have hz' : ‖z‖ ≥ R₀ := by
            simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hz
            exact hz.le
          calc |K z| ≤ C / ‖z‖ ^ α := hK_decay z hz'
            _ ≤ C / R₀ ^ α := by
                apply div_le_div_of_nonneg_left hC.le (Real.rpow_pos_of_pos hR₀ α)
                exact Real.rpow_le_rpow hR₀.le hz' hα.le
            _ ≤ max (C / R₀ ^ α) 1 := le_max_left _ _
        · rw [indicator_of_notMem hz, mul_zero]
          simp only [norm_zero]
          exact le_of_lt (lt_max_of_lt_right one_pos)
      obtain ⟨M, hM⟩ := hK_tail_bdd
      have hK_tail_meas : AEStronglyMeasurable (fun x => (kernelTail K R₀ (x - y) : ℂ)) volume := by
        -- kernelTail K R₀ x = K x * indicator is measurable
        have hind : Measurable ((closedBall (0 : E) R₀)ᶜ.indicator (fun _ => (1 : ℝ))) :=
          measurable_const.indicator isClosed_closedBall.measurableSet.compl
        have h1 : Measurable (kernelTail K R₀) := hK_meas.mul hind
        have h2 : Measurable (fun x => kernelTail K R₀ (x - y)) := h1.comp (measurable_id.sub
          measurable_const)
        exact (measurable_ofReal.comp h2).aestronglyMeasurable
      refine Integrable.mul_bdd (c := M) hf_int hK_tail_meas (Eventually.of_forall ?_)
      intro x
      exact hM (x - y)
  -- Step 10: Final step - the double integral vanishes at infinity
  -- Strategy: Use Tendsto composition directly, avoiding ε-δ unfolding
  --
  -- Key insight: schwartzBilinearIntegral f g K a = ∫∫ f(x) K(x-y) g(y-a) dx dy
  --   = ∫ g(y-a) H(y) dy  (Fubini, where H(y) = ∫ f(x) K(x-y) dx)
  --   = ∫ g(w) H(w+a) dw  (translation w = y-a)
  --   = ∫ g(w) H(w-(-a)) dw
  --
  -- We proved: Tendsto (fun b => ∫ g(w) H(w-b)) (cocompact E) (nhds 0)  [h_fK_vanish + convolution
  -- theorem]
  -- Composing with negation: Tendsto (fun a => ∫ g(w) H(w-(-a))) (cocompact E) (nhds 0)
  -- Define H(y) = (f⋆K)(y) = ∫ f(x) K(x-y) dx
  let H := fun y => ∫ x, f x * (K (x - y) : ℂ)
  -- Get bounds on f and K for integrability proofs
  obtain ⟨Cf, hCf⟩ := bounded_of_continuous_tendsto_zero f.continuous (schwartz_tendsto_zero f)
  have hCf_pos : 0 < max Cf 1 := lt_max_of_lt_right one_pos
  -- K_tail bound
  have hK_tail_bdd : ∃ M : ℝ, 0 < M ∧ ∀ z, ‖(K_tail z : ℂ)‖ ≤ M := by
    use max (C / R₀ ^ α) 1
    constructor
    · exact lt_max_of_lt_right one_pos
    intro z
    rw [Complex.norm_real]
    simp only [K_tail, kernelTail]
    by_cases hz : z ∈ (closedBall (0 : E) R₀)ᶜ
    · rw [indicator_of_mem hz, mul_one]
      have hz' : ‖z‖ ≥ R₀ := by
        simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hz
        exact hz.le
      calc |K z| ≤ C / ‖z‖ ^ α := hK_decay z hz'
        _ ≤ C / R₀ ^ α := by
            apply div_le_div_of_nonneg_left hC.le (Real.rpow_pos_of_pos hR₀ α)
            exact Real.rpow_le_rpow hR₀.le hz' hα.le
        _ ≤ max (C / R₀ ^ α) 1 := le_max_left _ _
    · rw [indicator_of_notMem hz, mul_zero]
      simp only [norm_zero]
      exact le_of_lt (lt_max_of_lt_right one_pos)
  obtain ⟨M_tail, hM_tail_pos, hM_tail⟩ := hK_tail_bdd
  -- Step 10a: H is continuous (convolution of Schwartz with locally integrable kernel)
  have hH_cont : Continuous H := by
    change Continuous (fun y => ∫ x, f x * (K (x - y) : ℂ))
    exact schwartz_bilinear_kernel_convolution_continuous f K hK_meas R₀ hR₀
      hK_cont hK_sing_int hf_int Cf hCf M_tail (fun z => by simpa [K_tail] using hM_tail z)
  -- Step 10b: Apply the proven convolution theorem
  -- For integrable g and continuous C₀ H, (fun b => ∫ g(w) H(w - b)) → 0 as b → cocompact
  have h_decay := convolution_vanishes_of_integrable_and_C0 hg_int h_fK_vanish hH_cont
  -- Step 10c: Negation preserves cocompact filter (since ‖-x‖ = ‖x‖)
  have h_neg_cocompact : Tendsto (fun a : E => -a) (cocompact E) (cocompact E) := by
    rw [Filter.Tendsto]
    intro S hS
    rw [Filter.mem_cocompact] at hS
    obtain ⟨K, hK_cpct, hK_sub⟩ := hS
    rw [Filter.mem_map, Filter.mem_cocompact]
    refine ⟨-K, hK_cpct.neg, ?_⟩
    intro a ha
    apply hK_sub
    simp only [mem_compl_iff, Set.mem_neg] at ha ⊢
    exact ha
  -- Step 10d: Compose to get decay in -a
  have h_composed : Tendsto (fun a => ∫ w : E, g w * H (w - (-a))) (cocompact E) (nhds 0) :=
    h_decay.comp h_neg_cocompact
  -- Step 10e: Show the schwartzBilinearIntegral equals the composed form
  unfold schwartzBilinearIntegral
  refine h_composed.congr ?_
  intro a
  -- Need: ∫∫ f(x) K(x-y) g(y-a) dx dy = ∫ g(w) H(w - (-a)) dw
  -- Step 10e-i: Fubini swap
  have h_fubini : ∫ x : E, ∫ y : E, f x * (K (x - y) : ℂ) * g (y - a) =
      ∫ y : E, g (y - a) * H y := by
    -- Goal: swap integration order and pull g(y-a) out of inner integral
    --
    -- Step 1: Prove integrability on E × E
    -- Decompose K = K_sing + K_tail where K_sing is L¹ and K_tail is bounded
    -- For K_sing: |f(x)| · |K_sing(x-y)| · |g(y-a)| ≤ Cf · |K_sing(x-y)| · Cg
    --   Integral ≤ Cf · Cg · ‖K_sing‖_1 · |E| (but E is infinite, so need careful argument)
    -- For K_tail: |f(x)| · |K_tail(x-y)| · |g(y-a)| ≤ |f(x)| · M_tail · |g(y-a)|
    --   Integral ≤ M_tail · ‖f‖_1 · ‖g‖_1
    have h_int : Integrable (uncurry (fun x y => f x * (K (x - y) : ℂ) * g (y - a)))
        (volume.prod volume) := by
      have hK_tail_bdd_abs : ∃ M : ℝ, ∀ z : E, |kernelTail K R₀ z| ≤ M := by
        refine ⟨M_tail, ?_⟩
        intro z
        have h := hM_tail z
        simpa [K_tail, Complex.norm_real] using h
      exact schwartz_bilinear_prod_integrable f g K hK_meas hK_loc R₀ hR₀
        hK_tail_bdd_abs a
    -- Step 2: Apply Fubini to swap integration order
    have h_swap : ∫ x : E, ∫ y : E, f x * (K (x - y) : ℂ) * g (y - a) =
        ∫ y : E, ∫ x : E, f x * (K (x - y) : ℂ) * g (y - a) := by
      exact MeasureTheory.integral_integral_swap h_int
    rw [h_swap]
    -- Step 3: Pull g(y-a) out of inner integral (it's constant in x)
    congr 1
    ext y
    -- Goal: ∫ x, f(x) * K(x-y) * g(y-a) = g(y-a) * H(y)
    -- where H(y) = ∫ x, f(x) * K(x-y)
    -- Rewrite: f * K * g = (f * K) * g, then pull out g
    have : ∫ x, f x * (K (x - y) : ℂ) * g (y - a) =
        (∫ x, f x * (K (x - y) : ℂ)) * g (y - a) :=
      integral_mul_const _ _
    rw [this]
    ring
  -- Step 10e-ii: Translation y ↦ w = y - a
  have h_translate : ∫ y : E, g (y - a) * H y = ∫ w : E, g w * H (w + a) := by
    have : ∫ y : E, g (y - a) * H y = ∫ w : E, g ((w + a) - a) * H (w + a) := by
      rw [integral_add_right_eq_self (fun y => g (y - a) * H y) a]
    simp only [add_sub_cancel_right] at this
    exact this
  -- Step 10e-iii: Rewrite w + a = w - (-a)
  have h_neg : ∫ w : E, g w * H (w + a) = ∫ w : E, g w * H (w - (-a)) := by
    congr 1; ext w; congr 1; simp only [sub_neg_eq_add]
  -- Chain: ∫ g(w) H(w-(-a)) = h_neg.symm = h_translate.symm = h_fubini.symm = ∫∫ f K g
  rw [h_neg.symm, h_translate.symm, h_fubini.symm]

end
