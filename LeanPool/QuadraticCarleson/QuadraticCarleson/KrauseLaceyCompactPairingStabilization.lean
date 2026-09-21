/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyFullDyadicSparseTransfer

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson.KrauseLaceyCompactPairingStabilization

open KrauseLaceyFullDyadicReflection KrauseLaceyFullDyadicSparseTransfer
open KrauseLaceySharpSmoothAdapter KrauseLaceySparseReflection


/-- One finite scale cutoff works on the entire compact testing support,
for every modulation. -/
theorem exists_uniform_zero_fullDyadic_integrands
    (j : ℤ) (f g : L0Infinity) :
    ∃ N : ℕ, ∀ (lam : ℝ) (x : ℝ), x ∈ tsupport g →
      ∀ r : ℕ, N ≤ r → ∀ y : ℝ,
        annularQuadraticKernel (fun t ↦ (dyadicPsi (j + (r : ℤ)) t : ℂ))
          lam (x - y) * f y = 0 := by
  obtain ⟨Rf, _, hRf⟩ := f.hasCompactSupport_toFun.isBounded.exists_pos_norm_le
  obtain ⟨Rg, _, hRg⟩ := g.hasCompactSupport_toFun.isBounded.exists_pos_norm_le
  have hp : Tendsto (fun r : ℕ ↦ (2 : ℝ) ^ r) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hc : 0 < (2 : ℝ) ^ (j - 3) := zpow_pos (by norm_num) _
  have hscale : Tendsto (fun r : ℕ ↦ (2 : ℝ) ^ (j + (r : ℤ) - 3)) atTop atTop := by
    convert hp.const_mul_atTop hc using 1
    funext r
    rw [show j + (r : ℤ) - 3 = (j - 3) + (r : ℤ) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hscale.eventually_gt_atTop (Rg + Rf))
  refine ⟨N, fun lam x hx r hr y ↦ ?_⟩
  by_cases hy : f y = 0
  · simp [hy]
  have hx' : |x| ≤ Rg := by simpa only [Real.norm_eq_abs] using hRg x hx
  have hy' : |y| ≤ Rf := by
    simpa only [Real.norm_eq_abs] using hRf y (subset_tsupport f hy)
  have hxy := (abs_sub x y).trans (add_le_add hx' hy')
  have hz := dyadicPsi_eq_zero_of_abs_le (hxy.trans (hN r hr).le)
  simp [annularQuadraticKernel, hz]

theorem exists_uniform_zero_fullDyadicConvolution (j : ℤ) (f g : L0Infinity) :
    ∃ N : ℕ, ∀ (lam : ℝ) (x : ℝ), x ∈ tsupport g →
      ∀ r : ℕ, N ≤ r → fullDyadicConvolution lam (j + (r : ℤ)) f x = 0 := by
  obtain ⟨N, hN⟩ := exists_uniform_zero_fullDyadic_integrands j f g
  refine ⟨N, fun lam x hx r hr ↦ ?_⟩
  unfold fullDyadicConvolution
  simp only [hN lam x hx r hr, integral_zero]

theorem finiteFullDyadicTail_stable {lam : ℝ} {j : ℤ} {f : ℝ → ℂ} {x : ℝ} {N n : ℕ}
    (hz : ∀ r : ℕ, N ≤ r → fullDyadicConvolution lam (j + (r : ℤ)) f x = 0)
    (hn : N ≤ n) : finiteFullDyadicTail lam j n f x = finiteFullDyadicTail lam j N f x := by
  unfold finiteFullDyadicTail
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro r hr hrN
  exact hz r (by simpa only [Finset.mem_range, not_lt] using hrN)

theorem smoothHighPass_eq_finiteFullDyadicTail_of_zero
    (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) {N : ℕ}
    (hz : ∀ r : ℕ, N ≤ r → fullDyadicConvolution lam (j + (r : ℤ)) f x = 0) :
    smoothQuadraticHighPass lam ((2 : ℝ) ^ (j - 3)) f x = finiteFullDyadicTail lam j N f x := by
  have hs : HasSum (fun r : ℕ ↦ fullDyadicConvolution lam (j + (r : ℤ)) f x)
      (finiteFullDyadicTail lam j N f x) :=
    hasSum_sum_of_ne_finset_zero (s := Finset.range N) fun r hr ↦
      hz r (by simpa only [Finset.mem_range, not_lt] using hr)
  exact (hasSum_fullDyadicConvolution_add_nat lam j f x).unique hs

/-- The actual high-pass and every sufficiently long finite tail coincide
pointwise on the entire testing support, with a modulation-independent cutoff. -/
theorem exists_uniform_smoothHighPass_eq_finiteFullDyadicTail (j : ℤ) (f g : L0Infinity) :
    ∃ N : ℕ, ∀ (lam : ℝ) (x : ℝ), x ∈ tsupport g → ∀ n : ℕ, N ≤ n →
      smoothQuadraticHighPass lam ((2 : ℝ) ^ (j - 3)) f x = finiteFullDyadicTail lam j n f x := by
  obtain ⟨N, hN⟩ := exists_uniform_zero_fullDyadicConvolution j f g
  refine ⟨N, fun lam x hx n hn ↦ ?_⟩
  rw [finiteFullDyadicTail_stable (hN lam x hx) hn]
  exact smoothHighPass_eq_finiteFullDyadicTail_of_zero lam j f x (hN lam x hx)

noncomputable def finiteFullDyadicTailOperator (lam : ℝ) (j : ℤ) (N : ℕ) : TestOperator :=
  fun f x ↦ finiteFullDyadicTail lam j N f x

theorem exists_operatorPairing_smoothHighPass_eq_finiteTail (j : ℤ) (f g : L0Infinity) :
    ∃ N : ℕ, ∀ lam : ℝ, ∀ n : ℕ, N ≤ n →
      operatorPairing (smoothQuadraticHighPassTestOperator lam ((2 : ℝ) ^ (j - 3))) f g =
        operatorPairing (finiteFullDyadicTailOperator lam j n) f g := by
  obtain ⟨N, hN⟩ := exists_uniform_smoothHighPass_eq_finiteFullDyadicTail j f g
  refine ⟨N, fun lam n hn ↦ ?_⟩
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport g
  · change smoothQuadraticHighPass _ _ _ x * star (g x) = _
    rw [hN lam x hx n hn]
    rfl
  · have hg := image_eq_zero_of_notMem_tsupport hx
    simp [hg]

theorem hasSparseOnePBound_smoothHighPass_of_uniform_finiteTail
    (lam : ℝ) (j : ℤ) {C p : ℝ}
    (hfinite : ∀ N : ℕ, HasSparseOnePBound C p (finiteFullDyadicTailOperator lam j N)) :
    HasSparseOnePBound C p (smoothQuadraticHighPassTestOperator lam ((2 : ℝ) ^ (j - 3))) := by
  intro f g
  obtain ⟨N, hN⟩ := exists_operatorPairing_smoothHighPass_eq_finiteTail j f g
  obtain ⟨S, hS, hb⟩ := hfinite N f g
  refine ⟨S, hS, ?_⟩
  rw [hN lam N le_rfl]
  exact hb

theorem nnnorm_finiteFullDyadicTail_le_max (lam : ℝ) (j : ℤ) (f : ℝ → ℂ) (x : ℝ)
    {n N : ℕ} (hn : n ≤ N) :
    ‖finiteFullDyadicTail lam j n f x‖₊ ≤ finiteFullDyadicTailMaxNNNorm lam j N f x :=
  Finset.le_sup (f := fun r ↦ ‖finiteFullDyadicTail lam j r f x‖₊)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

theorem fullDyadicTailSupEnorm_eq_finiteMax_of_zero
    (lam : ℝ) (j : ℤ) (f : ℝ → ℂ) (x : ℝ) {N : ℕ}
    (hz : ∀ r : ℕ, N ≤ r → fullDyadicConvolution lam (j + (r : ℤ)) f x = 0) :
    fullDyadicTailSupEnorm lam j f x = (finiteFullDyadicTailMaxNNNorm lam j N f x : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro n
    change (‖finiteFullDyadicTail lam j n f x‖₊ : ℝ≥0∞) ≤ _
    apply ENNReal.coe_le_coe.mpr
    by_cases hn : n ≤ N
    · exact nnnorm_finiteFullDyadicTail_le_max lam j f x hn
    · rw [finiteFullDyadicTail_stable hz (le_of_not_ge hn)]
      exact nnnorm_finiteFullDyadicTail_le_max lam j f x le_rfl
  · unfold finiteFullDyadicTailMaxNNNorm
    rw [ENNReal.coe_finset_sup]
    apply Finset.sup_le
    intro n hn
    exact le_iSup (fun r : ℕ ↦ ‖finiteFullDyadicTail lam j r f x‖ₑ) n

noncomputable def fullDyadicTailSupTestOperator (lam : ℝ) (j : ℤ) : TestOperator :=
  fun f x ↦ ((fullDyadicTailSupEnorm lam j f x).toReal : ℂ)

/-- The maximal-tail representative is finite at every point on the actual
test domain; its real conversion never hides an infinite value. -/
theorem fullDyadicTailSupEnorm_lt_top (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) :
    fullDyadicTailSupEnorm lam j f x < ∞ := by
  obtain ⟨N, hN⟩ := exists_eventually_zero_dyadicTail_integrands lam j f x
  have hz : ∀ r : ℕ, N ≤ r → fullDyadicConvolution lam (j + (r : ℤ)) f x = 0 := by
    intro r hr
    unfold fullDyadicConvolution
    simp only [annularQuadraticKernel, hN r hr, integral_zero]
  rw [fullDyadicTailSupEnorm_eq_finiteMax_of_zero lam j f x hz]
  exact ENNReal.coe_lt_top

theorem enorm_fullDyadicTailSupTestOperator (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) :
    ‖fullDyadicTailSupTestOperator lam j f x‖ₑ = fullDyadicTailSupEnorm lam j f x := by
  rw [← ofReal_norm, fullDyadicTailSupTestOperator, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (fullDyadicTailSupEnorm_lt_top lam j f x).ne]

/-- On any compact pairing support, the supremum over every finite tail is
already attained by one fixed finite maximal approximant. -/
theorem exists_fullDyadicTailSup_eq_finiteMax (j : ℤ) (f g : L0Infinity) :
    ∃ N : ℕ, ∀ (lam : ℝ) (x : ℝ), x ∈ tsupport g →
      fullDyadicTailSupTestOperator lam j f x = finiteFullDyadicTailMaxOperator lam j N f x := by
  obtain ⟨N, hN⟩ := exists_uniform_zero_fullDyadicConvolution j f g
  refine ⟨N, fun lam x hx ↦ ?_⟩
  unfold fullDyadicTailSupTestOperator finiteFullDyadicTailMaxOperator
  rw [fullDyadicTailSupEnorm_eq_finiteMax_of_zero lam j f x (hN lam x hx)]
  rfl

theorem exists_operatorPairing_fullDyadicTailSup_eq_finiteMax (j : ℤ) (f g : L0Infinity) :
    ∃ N : ℕ, ∀ lam : ℝ,
      operatorPairing (fullDyadicTailSupTestOperator lam j) f g =
        operatorPairing (finiteFullDyadicTailMaxOperator lam j N) f g := by
  obtain ⟨N, hN⟩ := exists_fullDyadicTailSup_eq_finiteMax j f g
  refine ⟨N, fun lam ↦ ?_⟩
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport g
  · rw [hN lam x hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem hasSparseOnePBound_fullDyadicTailSup_of_uniform_finiteMax
    (lam : ℝ) (j : ℤ) {C p : ℝ}
    (hfinite : ∀ N : ℕ, HasSparseOnePBound C p (finiteFullDyadicTailMaxOperator lam j N)) :
    HasSparseOnePBound C p (fullDyadicTailSupTestOperator lam j) := by
  intro f g
  obtain ⟨N, hN⟩ := exists_operatorPairing_fullDyadicTailSup_eq_finiteMax j f g
  obtain ⟨S, hS, hb⟩ := hfinite N f g
  refine ⟨S, hS, ?_⟩
  rw [hN lam]
  exact hb

/-- Compact-test domination by one finite maximal approximant is enough to
transfer a uniform sparse estimate. Its cutoff may depend on both tests. -/
theorem hasSparseOnePBound_of_compact_finiteMax_domination
    (lam : ℝ) (j : ℤ) {C p : ℝ} {U : TestOperator}
    (hfinite : ∀ N : ℕ, HasSparseOnePBound C p (finiteFullDyadicTailMaxOperator lam j N))
    (hdom : ∀ f g : L0Infinity, ∃ N : ℕ, ∀ x ∈ tsupport g,
      ‖U f x‖ ≤ ‖finiteFullDyadicTailMaxOperator lam j N f x‖) :
    HasSparseOnePBound C p U := by
  intro f g
  obtain ⟨N, hN⟩ := hdom f g
  let T := finiteFullDyadicTailMaxOperator lam j N
  obtain ⟨S, hS, hb⟩ := hfinite N f (normInput g)
  have habs : absoluteValueOperator T = T := by
    funext f x
    simp [T, absoluteValueOperator, finiteFullDyadicTailMaxOperator]
  have hp : ‖operatorPairing T f (normInput g)‖ = ∫ x, ‖T f x‖ * ‖g x‖ := by
    simpa only [habs] using norm_operatorPairing_absolute_normInput T f g
  change ENNReal.ofReal ‖operatorPairing T f (normInput g)‖ ≤ _ at hb
  rw [hp, sparseForm_normInput] at hb
  have hi : Integrable (fun x ↦ ‖T f x‖ * ‖g x‖) := by
    have hpair := integrable_pairing_of_locallyIntegrable
      (locallyIntegrable_finiteFullDyadicTailMaxOperator lam j N f) g
    simpa only [norm_mul, norm_star] using hpair.norm
  have hnorm : ‖operatorPairing U f g‖ ≤ ∫ x, ‖T f x‖ * ‖g x‖ := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards with x
    rw [norm_mul, norm_star]
    by_cases hx : x ∈ tsupport g
    · exact mul_le_mul_of_nonneg_right (hN x hx) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  exact ⟨S, hS, (ENNReal.ofReal_le_ofReal hnorm).trans hb⟩

theorem hasSparseOnePBound_smoothHighPass_of_uniform_finiteMax
    (lam : ℝ) (j : ℤ) {C p : ℝ}
    (hfinite : ∀ N : ℕ, HasSparseOnePBound C p (finiteFullDyadicTailMaxOperator lam j N)) :
    HasSparseOnePBound C p (smoothQuadraticHighPassTestOperator lam ((2 : ℝ) ^ (j - 3))) := by
  apply hasSparseOnePBound_of_compact_finiteMax_domination lam j hfinite
  intro f g
  obtain ⟨N, hN⟩ := exists_uniform_smoothHighPass_eq_finiteFullDyadicTail j f g
  refine ⟨N, fun x hx ↦ ?_⟩
  change ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (j - 3)) f x‖ ≤ _
  rw [hN lam x hx N le_rfl]
  simpa only [finiteFullDyadicTailMaxOperator, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (NNReal.coe_nonneg _), coe_nnnorm] using
    (show (‖finiteFullDyadicTail lam j N f x‖₊ : ℝ) ≤
      (finiteFullDyadicTailMaxNNNorm lam j N f x : ℝ) from
        NNReal.coe_le_coe.mpr (nnnorm_finiteFullDyadicTail_le_max lam j f x le_rfl))

theorem hasSparseOnePBound_absolute_smoothHighPass_of_uniform_finiteMax
    (lam : ℝ) (j : ℤ) {C p : ℝ}
    (hfinite : ∀ N : ℕ, HasSparseOnePBound C p (finiteFullDyadicTailMaxOperator lam j N)) :
    HasSparseOnePBound C p
      (absoluteValueOperator (smoothQuadraticHighPassTestOperator lam ((2 : ℝ) ^ (j - 3)))) := by
  apply hasSparseOnePBound_of_compact_finiteMax_domination lam j hfinite
  intro f g
  obtain ⟨N, hN⟩ := exists_uniform_smoothHighPass_eq_finiteFullDyadicTail j f g
  refine ⟨N, fun x hx ↦ ?_⟩
  simp only [absoluteValueOperator, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), smoothQuadraticHighPassTestOperator]
  rw [hN lam x hx N le_rfl]
  simpa only [finiteFullDyadicTailMaxOperator, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (NNReal.coe_nonneg _), coe_nnnorm] using
    (show (‖finiteFullDyadicTail lam j N f x‖₊ : ℝ) ≤
      (finiteFullDyadicTailMaxNNNorm lam j N f x : ℝ) from
        NNReal.coe_le_coe.mpr (nnnorm_finiteFullDyadicTail_le_max lam j f x le_rfl))

/-- Composing positive-half sparse domination, reflection, and compact
stabilization reaches the genuine absolute smooth high-pass with factor two. -/
theorem hasSparseOnePBound_absolute_smoothHighPass_of_uniform_positive_finiteMax
    (lam : ℝ) (j : ℤ) {C p : ℝ} (hC : 0 ≤ C)
    (hpositive : ∀ N : ℕ, HasSparseOnePBound C p (finitePositiveDyadicTailMaxOperator lam j N)) :
    HasSparseOnePBound (2 * C) p
      (absoluteValueOperator (smoothQuadraticHighPassTestOperator lam ((2 : ℝ) ^ (j - 3)))) :=
  hasSparseOnePBound_absolute_smoothHighPass_of_uniform_finiteMax lam j
    (fun N ↦ hasSparseOnePBound_fullDyadicTailMax lam j N hC (hpositive N))




/-! The KL-oriented bridge: the lower cutoff moves and the upper cutoff
is fixed. Prefix-maximal statements above are auxiliary only. -/

theorem smoothHighPass_eq_finiteSuffix_of_zero
    (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) {N : ℕ}
    (hz : ∀ r : ℕ, N ≤ r → fullDyadicConvolution lam (j + (r : ℤ)) f x = 0)
    (m : ℕ) : smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (m : ℤ) - 3)) f x =
      finiteFullDyadicSuffix lam j N m f x := by
  apply smoothHighPass_eq_finiteFullDyadicTail_of_zero
  intro r hr
  have hmr : N ≤ m + r := by omega
  simpa only [Nat.cast_add, add_assoc] using hz (m + r) hmr

noncomputable def dyadicSmoothHighPassMaxEnorm
    (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) : ℝ≥0∞ :=
  ⨆ m : ℕ, ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (m : ℤ) - 3)) f x‖ₑ

noncomputable def dyadicSmoothHighPassMaxOperator (lam : ℝ) (j : ℤ) : TestOperator :=
  fun f x ↦ ((dyadicSmoothHighPassMaxEnorm lam j f x).toReal : ℂ)

theorem dyadicSmoothHighPassMaxEnorm_eq_finiteSuffixMax_of_zero
    (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) {N : ℕ}
    (hz : ∀ r : ℕ, N ≤ r → fullDyadicConvolution lam (j + (r : ℤ)) f x = 0) :
    dyadicSmoothHighPassMaxEnorm lam j f x =
      (finiteFullDyadicSuffixMaxNNNorm lam j N f x : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro m
    rw [smoothHighPass_eq_finiteSuffix_of_zero lam j f x hz m]
    by_cases hm : m ≤ N
    · apply ENNReal.coe_le_coe.mpr
      exact Finset.le_sup (f := fun r ↦ ‖finiteFullDyadicSuffix lam j N r f x‖₊)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    · simp [finiteFullDyadicSuffix, Nat.sub_eq_zero_of_le (le_of_not_ge hm), finiteFullDyadicTail]
  · unfold finiteFullDyadicSuffixMaxNNNorm
    rw [ENNReal.coe_finset_sup]
    apply Finset.sup_le
    intro m hm
    change ‖finiteFullDyadicSuffix lam j N m f x‖ₑ ≤ _
    rw [← smoothHighPass_eq_finiteSuffix_of_zero lam j f x hz m]
    exact le_iSup (fun r : ℕ ↦
      ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (r : ℤ) - 3)) f x‖ₑ) m

theorem dyadicSmoothHighPassMaxEnorm_lt_top (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) :
    dyadicSmoothHighPassMaxEnorm lam j f x < ∞ := by
  obtain ⟨N, hN⟩ := exists_eventually_zero_dyadicTail_integrands lam j f x
  have hz : ∀ r : ℕ, N ≤ r → fullDyadicConvolution lam (j + (r : ℤ)) f x = 0 := by
    intro r hr
    unfold fullDyadicConvolution
    simp only [annularQuadraticKernel, hN r hr, integral_zero]
  rw [dyadicSmoothHighPassMaxEnorm_eq_finiteSuffixMax_of_zero lam j f x hz]
  exact ENNReal.coe_lt_top

theorem enorm_dyadicSmoothHighPassMaxOperator (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) :
    ‖dyadicSmoothHighPassMaxOperator lam j f x‖ₑ = dyadicSmoothHighPassMaxEnorm lam j f x := by
  rw [← ofReal_norm, dyadicSmoothHighPassMaxOperator, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (dyadicSmoothHighPassMaxEnorm_lt_top lam j f x).ne]

/-- The genuine supremum over every moving lower cutoff agrees exactly,
on the entire compact testing support, with one finite suffix maximum. -/
theorem exists_dyadicSmoothHighPassMax_eq_finiteSuffixMax (j : ℤ) (f g : L0Infinity) :
    ∃ N : ℕ, ∀ (lam : ℝ) (x : ℝ), x ∈ tsupport g →
      dyadicSmoothHighPassMaxOperator lam j f x =
        finiteFullDyadicSuffixMaxOperator lam j N f x := by
  obtain ⟨N, hN⟩ := exists_uniform_zero_fullDyadicConvolution j f g
  refine ⟨N, fun lam x hx ↦ ?_⟩
  unfold dyadicSmoothHighPassMaxOperator finiteFullDyadicSuffixMaxOperator
  rw [dyadicSmoothHighPassMaxEnorm_eq_finiteSuffixMax_of_zero lam j f x (hN lam x hx)]
  rfl

theorem exists_operatorPairing_dyadicSmoothHighPassMax_eq_finiteSuffixMax
    (j : ℤ) (f g : L0Infinity) :
    ∃ N : ℕ, ∀ lam : ℝ,
      operatorPairing (dyadicSmoothHighPassMaxOperator lam j) f g =
        operatorPairing (finiteFullDyadicSuffixMaxOperator lam j N) f g := by
  obtain ⟨N, hN⟩ := exists_dyadicSmoothHighPassMax_eq_finiteSuffixMax j f g
  refine ⟨N, fun lam ↦ ?_⟩
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport g
  · rw [hN lam x hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- Uniform KL-oriented finite suffix bounds pass to the genuine smooth
high-pass maximum without a sparse-family limit and without constant loss. -/
theorem hasSparseOnePBound_dyadicSmoothHighPassMax_of_uniform_finiteSuffixMax
    (lam : ℝ) (j : ℤ) {C p : ℝ}
    (hfinite : ∀ N : ℕ, HasSparseOnePBound C p (finiteFullDyadicSuffixMaxOperator lam j N)) :
    HasSparseOnePBound C p (dyadicSmoothHighPassMaxOperator lam j) := by
  intro f g
  obtain ⟨N, hN⟩ := exists_operatorPairing_dyadicSmoothHighPassMax_eq_finiteSuffixMax j f g
  obtain ⟨S, hS, hb⟩ := hfinite N f g
  refine ⟨S, hS, ?_⟩
  rw [hN lam]
  exact hb

/-- Final positive-half-to-genuine-high-pass transfer in the source's
moving-lower-cutoff orientation. Only reflection costs the factor two. -/
theorem hasSparseOnePBound_dyadicSmoothHighPassMax_of_uniform_positive_finiteSuffixMax
    (lam : ℝ) (j : ℤ) {C p : ℝ} (hC : 0 ≤ C)
    (hpositive : ∀ N : ℕ, HasSparseOnePBound C p (finitePositiveDyadicSuffixMaxOperator lam j N)) :
    HasSparseOnePBound (2 * C) p (dyadicSmoothHighPassMaxOperator lam j) :=
  hasSparseOnePBound_dyadicSmoothHighPassMax_of_uniform_finiteSuffixMax lam j
    (fun N ↦ hasSparseOnePBound_fullDyadicSuffixMax lam j N hC (hpositive N))


end QuadraticCarleson.KrauseLaceyCompactPairingStabilization
