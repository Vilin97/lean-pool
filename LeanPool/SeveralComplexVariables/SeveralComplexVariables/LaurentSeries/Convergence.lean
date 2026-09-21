/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries.Coefficients
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LocallyUniform

/-!
# Normal convergence of Laurent coefficient families

Inner and outer coefficient tori bound the two halves of each coordinate series by geometric
sequences. Their finite products give summable local majorants.

## Main results

`exists_local_laurent_majorant` produces a geometric bound from inner and outer tori.
`summable_norm_multivariableLaurent` is absolute summability of the terms.
`hasSumLocallyUniformlyOn_multivariableLaurent_of_pointwise` upgrades a pointwise summable
expansion to locally uniform convergence.
-/

public noncomputable section

open Complex Set Metric Filter
open scoped Real Topology

namespace SeveralComplexVariables

/-- A finite product of nonnegative summable families is summable over all tuples. -/
private theorem summable_fin_prod_of_nonneg {n : ℕ} (b : Fin n → ℤ → ℝ)
    (hb : ∀ i, Summable (b i)) (hb₀ : ∀ i k, 0 ≤ b i k) :
    Summable (fun m : Fin n → ℤ => ∏ i, b i (m i)) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    have h := (hb 0).mul_of_nonneg (ih (fun i => b i.succ) (fun i => hb i.succ)
      (fun i => hb₀ i.succ)) (hb₀ 0) (fun m => Finset.prod_nonneg (fun i _ => hb₀ i.succ (m i)))
    apply (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).summable_iff.mp
    simpa [Fin.consEquiv, Fin.prod_univ_succ, Function.comp_def] using h

/-- Positive and negative geometric tails give a summable integer-indexed family. -/
private theorem summable_two_sided_geometric {p q : ℝ}
    (hp₀ : 0 ≤ p) (hp : p < 1) (hq₀ : 0 ≤ q) (hq : q < 1) :
    Summable (Int.rec (fun n => p ^ n) (fun n => q ^ (n + 1))) := by
  apply (summable_geometric_of_lt_one hp₀ hp).int_rec
  simpa only [pow_succ] using (summable_geometric_of_lt_one hq₀ hq).mul_right q

/-- A scalar Laurent factor is controlled by its inner or outer geometric ratio. -/
private theorem zpow_mul_corner_le {a b t T u : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hu : 0 ≤ u)
    (huT : u ≤ T) (k : ℤ) (htu : k < 0 → t ≤ u) :
    u ^ k * (if k < 0 then a else b) ^ (-k) ≤
      Int.rec (fun n => (T / b) ^ n) (fun n => (a / t) ^ (n + 1)) k := by
  cases k with
  | ofNat n =>
    simp only [zpow_neg]
    calc
      u ^ n * (b ^ n)⁻¹ ≤ T ^ n * (b ^ n)⁻¹ := by gcongr
      _ = (T / b) ^ n := by simp [div_eq_mul_inv, mul_pow]
  | negSucc n =>
    have htu' := htu (by omega)
    simp only [Int.negSucc_lt_zero, ite_true, Int.neg_negSucc, zpow_natCast, zpow_negSucc]
    calc
      (u ^ (n + 1))⁻¹ * a ^ (n + 1) ≤ (t ^ (n + 1))⁻¹ * a ^ (n + 1) := by gcongr
      _ = (a / t) ^ (n + 1) := by simp only [div_eq_mul_inv]; ring

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Corner coefficient bounds give a product geometric bound for every Laurent term. -/
private theorem norm_laurentTerm_le_geometric {c : (Fin n → ℤ) → F}
    {a b t T : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (ht : ∀ i, 0 < t i) (hT : ∀ i, 0 ≤ T i) {M : ℝ} (hM : 0 ≤ M)
    {z w : Fin n → ℂ} (hwT : ∀ i, ‖w i‖ ≤ T i)
    (htw : ∀ i, z i ≠ 0 → t i ≤ ‖w i‖) (m : Fin n → ℤ)
    (hzero : ∀ i, z i = 0 → m i < 0 → c m = 0)
    (hc : ‖c m‖ ≤ M * ∏ i, (if m i < 0 then a i else b i) ^ (-m i)) :
    ‖multivariableLaurentTerm c m w‖ ≤
      M * ∏ i, Int.rec (fun n => (T i / b i) ^ n) (fun n => (a i / t i) ^ (n + 1)) (m i) := by
  have hgeom (i : Fin n) :
      (0 : ℝ) ≤ Int.rec (fun n => (T i / b i) ^ n) (fun n => (a i / t i) ^ (n + 1)) (m i) := by
    cases m i with
    | ofNat k => exact pow_nonneg (div_nonneg (hT i) (hb i).le) _
    | negSucc k => exact pow_nonneg (div_nonneg (ha i).le (ht i).le) _
  by_cases hbad : ∃ i, z i = 0 ∧ m i < 0
  · obtain ⟨i, hi, hm⟩ := hbad
    rw [multivariableLaurentTerm, hzero i hi hm, smul_zero, norm_zero]
    exact mul_nonneg hM (Finset.prod_nonneg fun i _ => hgeom i)
  · rw [multivariableLaurentTerm, norm_smul, norm_prod]
    simp only [norm_zpow]
    calc
      (∏ i, ‖w i‖ ^ m i) * ‖c m‖ ≤
          (∏ i, ‖w i‖ ^ m i) * (M * ∏ i, (if m i < 0 then a i else b i) ^ (-m i)) :=
        mul_le_mul_of_nonneg_left hc (Finset.prod_nonneg fun i _ => zpow_nonneg (norm_nonneg _) _)
      _ = M * ∏ i, ‖w i‖ ^ m i * (if m i < 0 then a i else b i) ^ (-m i) := by
        rw [Finset.prod_mul_distrib]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hM
        apply Finset.prod_le_prod₀
        · intro i _
          apply mul_nonneg (zpow_nonneg (norm_nonneg _) _)
          apply zpow_nonneg
          split_ifs
          · exact (ha i).le
          · exact (hb i).le
        · intro i _
          exact zpow_mul_corner_le (ha i) (hb i) (ht i) (norm_nonneg _) (hwT i) (m i)
            (fun hm => htw i (fun hi => hbad ⟨i, hi, hm⟩))

omit [NormedSpace ℂ F] in
/-- The finitely many corner tori of a circular product share a bound for a continuous function. -/
private theorem exists_bound_torus_corners {V : Fin n → Set ℂ}
    (hrot : ∀ i, ∀ v ∈ V i, ∀ w : ℂ, ‖w‖ = ‖v‖ → w ∈ V i)
    {a b : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (haV : ∀ i, (a i : ℂ) ∈ V i) (hbV : ∀ i, (b i : ℂ) ∈ V i)
    {f : (Fin n → ℂ) → F} (hf : ContinuousOn f (Set.pi univ V)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : Fin n → Bool, ∀ θ,
      ‖f (torusMap 0 (fun i => if p i then a i else b i) θ)‖ ≤ M := by
  let r (p : Fin n → Bool) (i : Fin n) := if p i then a i else b i
  have hr (p : Fin n → Bool) (i : Fin n) : 0 < r p i := by
    dsimp [r]; split_ifs <;> [exact ha i; exact hb i]
  have hrV (p : Fin n → Bool) (i : Fin n) : (r p i : ℂ) ∈ V i := by
    dsimp [r]; split_ifs <;> [exact haV i; exact hbV i]
  let K (p : Fin n → Bool) := {w : Fin n → ℂ | ∀ i, w i ∈ sphere 0 (r p i)}
  have hKV (p : Fin n → Bool) : K p ⊆ Set.pi univ V := by
    intro w hw i _
    apply hrot i _ (hrV p i) _
    simpa [abs_of_pos (hr p i)] using hw i
  have hbound (p : Fin n → Bool) : ∃ M : ℝ, ∀ w ∈ K p, ‖f w‖ ≤ M :=
    (isCompact_pi_infinite fun i => isCompact_sphere (0 : ℂ) (r p i)).exists_bound_of_continuousOn
      (hf.mono (hKV p))
  choose M hM using hbound
  refine ⟨∑ p, max (M p) 0, Finset.sum_nonneg (fun p _ => le_max_right _ _), ?_⟩
  intro p θ
  apply (hM p _ (fun i => by
    change torusMap 0 (r p) θ i ∈ sphere 0 (r p i)
    simp [torusMap, abs_of_pos (hr p i)])).trans
  exact (le_max_left _ _).trans (Finset.single_le_sum
    (fun q _ => le_max_right (M q) 0) (Finset.mem_univ p))

variable [CompleteSpace F]

/-- Every point has a neighborhood on which the Laurent terms admit a summable majorant. -/
theorem exists_local_laurent_majorant {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsPreconnected U) (hR : IsReinhardt U)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U)
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrU : (fun i => (r i : ℂ)) ∈ U)
    {z : Fin n → ℂ} (hz : z ∈ U) :
    ∃ N : Set (Fin n → ℂ), N ∈ 𝓝 z ∧ N ⊆ U ∧
      ∃ B : (Fin n → ℤ) → ℝ, Summable B ∧ ∀ m, ∀ w ∈ N,
        ‖multivariableLaurentTerm (multivariableLaurentCoeff f r) m w‖ ≤ B m := by
  obtain ⟨V, hVo, hVc, hVr, hzV, hVU⟩ := hR.exists_circular_product_neighborhood ho hz
  choose a b t T ha hat hT hTb haV hbV hzT htz using
    fun i => exists_circular_radii_bounds (hVo i) (hVr i) (hzV i (mem_univ _))
  have hb (i) : 0 < b i := (hT i).trans (hTb i)
  have ht (i) : 0 < t i := (ha i).trans (hat i)
  obtain ⟨M, hM, hcorner⟩ := exists_bound_torus_corners hVr ha hb haV hbV (hf.continuousOn.mono hVU)
  let W : Fin n → Set ℂ := fun i => {w | ‖w‖ < T i ∧ (z i ≠ 0 → t i < ‖w‖)}
  have hWo (i) : IsOpen (W i) := by
    by_cases hzi : z i = 0
    · simpa [W, hzi] using isOpen_lt (f := fun w : ℂ => ‖w‖) continuous_norm
        (g := fun _ => T i) continuous_const
    · simp only [W, hzi, ne_eq, not_false_eq_true, true_implies]
      exact (isOpen_lt (f := fun w : ℂ => ‖w‖) continuous_norm
        (g := fun _ => T i) continuous_const).inter
        (isOpen_lt (f := fun _ : ℂ => t i) continuous_const continuous_norm)
  let B (m : Fin n → ℤ) :=
    M * ∏ i, Int.rec (fun k => (T i / b i) ^ k) (fun k => (a i / t i) ^ (k + 1)) (m i)
  have hB : Summable B := by
    apply Summable.mul_left M
    apply summable_fin_prod_of_nonneg
    · intro i
      exact summable_two_sided_geometric (div_nonneg (hT i).le (hb i).le)
        ((div_lt_one (hb i)).mpr (hTb i)) (div_nonneg (ha i).le (ht i).le)
        ((div_lt_one (ht i)).mpr (hat i))
    · intro i k
      cases k with
      | ofNat k => exact pow_nonneg (div_nonneg (hT i).le (hb i).le) _
      | negSucc k => exact pow_nonneg (div_nonneg (ha i).le (ht i).le) _
  refine ⟨Set.pi univ W ∩ U,
    ((isOpen_set_pi finite_univ (fun i _ => hWo i)).inter ho).mem_nhds
      ⟨fun i _ => ⟨hzT i, htz i⟩, hz⟩, inter_subset_right, B, hB, ?_⟩
  intro m w hw
  apply norm_laurentTerm_le_geometric ha hb ht (fun i => (hT i).le) hM
    (fun i => (hw.1 i (mem_univ _)).1.le)
    (fun i hi => ((hw.1 i (mem_univ _)).2 hi).le) m
  · intro i hzi hmi
    exact multivariableLaurentCoeff_neg_eq_zero ho hc hR hf hr hrU m i ⟨z, hz, hzi⟩ hmi
  · let q (i : Fin n) := if m i < 0 then a i else b i
    have hq (i) : 0 < q i := by dsimp [q]; split_ifs <;> [exact ha i; exact hb i]
    have hqV : (fun i => (q i : ℂ)) ∈ Set.pi univ V := by
      intro i _; dsimp [q]; split_ifs <;> [exact haV i; exact hbV i]
    rw [← multivariableLaurentCoeff_eq_of_radii ho hc hR hf hr hq hrU (hVU hqV)]
    apply norm_multivariableLaurentCoeff_le hq
    intro θ
    simpa [q] using hcorner (fun i => decide (m i < 0)) θ

/-- The Laurent expansion family is absolutely summable at every point of the domain. -/
theorem summable_norm_multivariableLaurent {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsPreconnected U) (hR : IsReinhardt U)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U)
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrU : (fun i => (r i : ℂ)) ∈ U)
    {z : Fin n → ℂ} (hz : z ∈ U) :
    Summable (fun m => ‖multivariableLaurentTerm (multivariableLaurentCoeff f r) m z‖) := by
  obtain ⟨N, hN, _, B, hB, hb⟩ := exists_local_laurent_majorant ho hc hR hf hr hrU hz
  exact hB.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => hb m z (mem_of_mem_nhds hN))

/-- Pointwise Laurent expansion with torus coefficients automatically converges locally
uniformly. -/
theorem hasSumLocallyUniformlyOn_multivariableLaurent_of_pointwise {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsPreconnected U) (hR : IsReinhardt U)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U)
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrU : (fun i => (r i : ℂ)) ∈ U)
    (hsum : ∀ z ∈ U, HasSum (fun m => multivariableLaurentTerm (multivariableLaurentCoeff f r) m
      z) (f z)) :
    HasSumLocallyUniformlyOn (multivariableLaurentTerm (multivariableLaurentCoeff f r)) f U := by
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z hz
  obtain ⟨N, hN, hNU, B, hB, hb⟩ := exists_local_laurent_majorant ho hc hR hf hr hrU hz
  refine ⟨N, mem_nhdsWithin_of_mem_nhds hN, ?_⟩
  apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
  exact (tendstoUniformlyOn_tsum hB hb).congr_right (fun w hw => (hsum w (hNU hw)).tsum_eq)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
