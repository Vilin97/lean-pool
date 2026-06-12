/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # AnnulusLocalEstimate.lean
  Uniform local estimate on annuli (combining circle + band estimates).
  Scaffolding notes: AnnulusLocalEstimate/annulus_local.md

  Dependencies: BlockDecomposition, LocalCircleEstimate, HighFreqBandEstimate

  Public API:
  - `annulus_local_estimate` (Theorem 6.1)
-/
import LeanPool.PhaseRetrieval.Constant.Internal.BlockDecomposition
import LeanPool.PhaseRetrieval.Constant.Internal.LocalCircleEstimate
import LeanPool.PhaseRetrieval.Constant.Internal.HighFreqBandEstimate

/-! # AnnulusLocalEstimate -/


open MeasureTheory Complex Real Finset

noncomputable section

namespace FockSPR

/-! ## Auxiliary lemmas for frequency block analysis -/

/-- `(r * fourier 1 t)^n = r^n * fourier n t`. -/
private lemma mul_fourier_pow (r : ℝ) (t : AddCircle T) (n : ℕ) :
    ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ n =
    (↑r : ℂ) ^ n * fourier (n : ℤ) t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]; push_cast [Nat.cast_succ]; rw [fourier_add]; ring

/-- Frequency blocks are pairwise disjoint. -/
private lemma freqBlock_pairwiseDisjoint :
    ∀ (S : Finset ℕ), (S : Set ℕ).PairwiseDisjoint freqBlock := by
  intro S ℓ₁ _ ℓ₂ _ hne
  simp only [Function.onFun, freqBlock, Finset.disjoint_left, Finset.mem_Icc]
  intro n hn₁ hn₂
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (ℓ₁ + 1) ^ 2 ≤ ℓ₂ ^ 2 := by nlinarith
    have := Nat.pos_of_ne_zero (show (ℓ₁ + 1) ^ 2 ≠ 0 by positivity)
    omega
  · have : (ℓ₂ + 1) ^ 2 ≤ ℓ₁ ^ 2 := by nlinarith
    have := Nat.pos_of_ne_zero (show (ℓ₂ + 1) ^ 2 ≠ 0 by positivity)
    omega

/-- Collapse inner sum over blocks to membership in biUnion. -/
private lemma sum_ite_mem_biUnion (S : Finset ℕ) (n : ℕ) (c : ℂ) :
    ∑ ℓ ∈ S, (if n ∈ freqBlock ℓ then c else 0) =
    if n ∈ S.biUnion freqBlock then c else 0 := by
  split_ifs with h
  · obtain ⟨ℓ, hℓS, hℓn⟩ := Finset.mem_biUnion.mp h
    rw [Finset.sum_eq_single ℓ (fun ℓ' hℓ'S hne => by
      rw [if_neg]; intro h'
      exact Finset.disjoint_left.mp
        ((freqBlock_pairwiseDisjoint S) (Finset.mem_coe.mpr hℓ'S)
          (Finset.mem_coe.mpr hℓS) hne) h' hℓn)
      (fun habs => absurd hℓS habs)]
    simp only [hℓn, ite_true]
  · exact Finset.sum_eq_zero (fun ℓ hℓ => if_neg (fun h' =>
      h (Finset.mem_biUnion.mpr ⟨ℓ, hℓ, h'⟩)))

/-- Sum of `2ℓ+1` over `Icc a b` plus `a²` equals `(b+1)²`. -/
private lemma sum_odd_sq (a b : ℕ) (h : a ≤ b) :
    ∑ ℓ ∈ Finset.Icc a b, (2 * ℓ + 1) + a ^ 2 = (b + 1) ^ 2 := by
  induction b with
  | zero => interval_cases a; simp
  | succ n ih =>
    by_cases ha' : a ≤ n
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have := ih ha'
      nlinarith [show (n + 2) ^ 2 = (n + 1) ^ 2 + 2 * (n + 1) + 1 from by ring]
    · have : a = n + 1 := by omega
      subst this; simp; ring

/-- Cardinality of biUnion of frequency blocks. -/
private lemma card_biUnion_freqBlock (a b : ℕ) (h : a ≤ b) :
    ((Finset.Icc a b).biUnion freqBlock).card = (b + 1) ^ 2 - a ^ 2 := by
  rw [Finset.card_biUnion (freqBlock_pairwiseDisjoint _)]
  simp_rw [FockSPR.freqBlock_card]
  have h1 : a ^ 2 ≤ (b + 1) ^ 2 := by nlinarith
  have h2 := sum_odd_sq a b h
  omega

/-! ## Private Lemma 6.1a: Monotonicity of `f(j) = 11(2j+1)/(j-5)^2` -/

private lemma freq_ratio_decreasing {j₁ j₂ : ℕ} (hj₁ : 6 ≤ j₁) (hj₂ : 6 ≤ j₂)
    (h : j₁ ≤ j₂) :
    (11 * (2 * j₂ + 1) : ℝ) / ((j₂ - 5 : ℤ) : ℝ) ^ 2 ≤
    (11 * (2 * j₁ + 1) : ℝ) / ((j₁ - 5 : ℤ) : ℝ) ^ 2 := by
  have hj₁_sub : (j₁ - 5 : ℤ) = (j₁ : ℤ) - 5 := by omega
  have hj₂_sub : (j₂ - 5 : ℤ) = (j₂ : ℤ) - 5 := by omega
  rw [hj₁_sub, hj₂_sub]
  have hd₁ : (0 : ℝ) < (((j₁ : ℤ) - 5 : ℤ) : ℝ) := by
    exact_mod_cast (show (0 : ℤ) < (j₁ : ℤ) - 5 by omega)
  have hd₂ : (0 : ℝ) < (((j₂ : ℤ) - 5 : ℤ) : ℝ) := by
    exact_mod_cast (show (0 : ℤ) < (j₂ : ℤ) - 5 by omega)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have cast₁ : (((j₁ : ℤ) - 5 : ℤ) : ℝ) = (j₁ : ℝ) - 5 := by push_cast; ring
  have cast₂ : (((j₂ : ℤ) - 5 : ℤ) : ℝ) = (j₂ : ℝ) - 5 := by push_cast; ring
  rw [cast₁, cast₂]
  nlinarith [sq_nonneg ((j₂ : ℝ) - j₁),
    mul_nonneg (sub_nonneg.mpr (show (j₁ : ℝ) ≤ j₂ from by exact_mod_cast h))
      (mul_nonneg (by linarith : (0 : ℝ) ≤ (j₁ : ℝ) - 5)
        (by linarith : (0 : ℝ) ≤ (j₂ : ℝ) - 5))]

/-! ## Private Lemma 6.1b: Numerical verification at j = 818 -/

private lemma numerical_check_818 : 1343 * (11 * 1637) ^ 2 ≤ 813 ^ 4 := by
  norm_num

/-! ## Structural matching: localPoly as a Fourier sum -/

/-- The frequency support of `localPoly a 5 j`, restricted to indices `≤ D`. -/
private def activeFreqSet (D j : ℕ) : Finset ℕ :=
  ((Finset.Icc (max 1 (j - 5))
    (min (maxBlockIndex D) (j + 5))).biUnion freqBlock).filter (· ≤ D)

/-- Fourier coefficients for `localPoly` at radius `r`, incorporating the frequency
    support check so that coefficients are zero outside the active frequency set. -/
private def localFourierCoeff {D : ℕ} (a : Fin D → ℂ) (j : ℕ) (r : ℝ) : ℕ → ℂ :=
  fun n =>
    if h : n ∈ (Finset.Icc (max 1 (j - 5))
        (min (maxBlockIndex D) (j + 5))).biUnion freqBlock ∧
        1 ≤ n ∧ n ≤ D then
      a ⟨n - 1, by omega⟩ * (↑r : ℂ) ^ n
    else 0

/-- All elements of `activeFreqSet` are `≥ 1`. -/
private lemma activeFreqSet_pos {D j n : ℕ} (hn : n ∈ activeFreqSet D j) :
    1 ≤ n := by
  simp only [activeFreqSet, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_Icc] at hn
  obtain ⟨⟨ℓ, hℓ, hn_block⟩, _⟩ := hn
  simp only [freqBlock, Finset.mem_Icc] at hn_block
  nlinarith [sq_nonneg ℓ, show 1 ≤ ℓ by omega]

/-- `localPoly a 5 j (r * fourier 1 t)` equals a Fourier sum over `activeFreqSet`.
    This is a mechanical reindexing of the `Fin D` sum into a `Finset ℕ` sum. -/
private lemma localPoly_eq_fourierSum {D : ℕ} (_hD : 1 ≤ D) (a : Fin D → ℂ)
    (j : ℕ) (r : ℝ) :
    (fun t : AddCircle T => localPoly a 5 j (↑r * (fourier 1 t : ℂ))) =
    fun t => ∑ n ∈ activeFreqSet D j,
      localFourierCoeff a j r n * fourier (n : ℤ) t := by
  ext t
  -- Unfold localPoly and blockPoly
  unfold localPoly blockPoly
  simp_rw [mul_fourier_pow]
  rw [Finset.sum_comm]
  -- Factor out fourier from each term
  simp_rw [show ∀ (k : Fin D) (ℓ : ℕ),
    (if (k.val + 1) ∈ freqBlock ℓ then
      a k * ((↑r : ℂ) ^ (k.val + 1) * fourier ((k.val + 1 : ℕ) : ℤ) t) else 0) =
    (if (k.val + 1) ∈ freqBlock ℓ then
      a k * (↑r : ℂ) ^ (k.val + 1) else 0) * fourier ((k.val + 1 : ℕ) : ℤ) t
    from fun k ℓ => by split_ifs <;> ring]
  simp_rw [← Finset.sum_mul, sum_ite_mem_biUnion]
  -- Now: ∑ k : Fin D, (if (k+1) ∈ E then a k * r^(k+1) else 0) * fourier(k+1) t
  -- = ∑ n ∈ activeFreqSet, localFourierCoeff(n) * fourier(n) t
  -- Step 1: Replace each term with localFourierCoeff(k+1)
  simp_rw [show ∀ k : Fin D,
    (if (k.val + 1) ∈ (Finset.Icc (max 1 (j - 5))
      (min (maxBlockIndex D) (j + 5))).biUnion freqBlock then
      a k * (↑r : ℂ) ^ (k.val + 1) else 0) = localFourierCoeff a j r (k.val + 1)
    from fun k => by
      unfold localFourierCoeff
      split_ifs with h1 h2 h2
      · congr 1
      · exact absurd ⟨h1, by omega, by omega⟩ h2
      · exact absurd h2.1 h1
      · rfl]
  -- Step 2: Reindex from Fin D to activeFreqSet via Icc 1 D
  set f : ℕ → ℂ := fun n =>
    localFourierCoeff a j r n * fourier (n : ℤ) t
  change ∑ k : Fin D, f (k.val + 1) = ∑ n ∈ activeFreqSet D j, f n
  -- Convert Fin D sum to Icc 1 D sum
  conv_lhs =>
    rw [show (fun k : Fin D => f (k.val + 1)) =
      (fun k : Fin D => (f ∘ (· + 1)) k.val) from rfl]
  rw [Fin.sum_univ_eq_sum_range]
  have hmap : Finset.Icc 1 D =
      (Finset.range D).map ⟨(· + 1), Nat.succ_injective⟩ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range,
      Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨n - 1, by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩; omega
  rw [show ∑ i ∈ Finset.range D, (f ∘ (· + 1)) i =
    ∑ n ∈ Finset.Icc 1 D, f n from by rw [hmap, Finset.sum_map]; rfl]
  -- Now both sides are sums of f: one over Icc 1 D, one over activeFreqSet
  -- activeFreqSet ⊆ Icc 1 D and f(n) = 0 for n ∈ Icc 1 D \ activeFreqSet
  symm
  apply Finset.sum_subset
  · -- activeFreqSet ⊆ Icc 1 D
    intro n hn
    simp only [activeFreqSet, Finset.mem_filter, Finset.mem_biUnion,
      Finset.mem_Icc] at hn
    obtain ⟨⟨ℓ, hℓ, hn_block⟩, hn_le⟩ := hn
    simp only [freqBlock, Finset.mem_Icc] at hn_block
    exact Finset.mem_Icc.mpr
      ⟨by nlinarith [sq_nonneg ℓ, show 1 ≤ ℓ by omega], hn_le⟩
  · -- f(n) = 0 for n ∉ activeFreqSet
    intro n hn hn_not
    change localFourierCoeff a j r n * fourier (n : ℤ) t = 0
    simp only [localFourierCoeff]
    rw [dif_neg]
    · simp
    · intro ⟨h_mem, _, _⟩
      exact hn_not (Finset.mem_filter.mpr
        ⟨h_mem, (Finset.mem_Icc.mp hn).2⟩)

/-- For `j ≤ 817`, the active frequency set has `≤ 17985` elements. -/
private lemma activeFreqSet_card_le {D : ℕ} (_hD : 1 ≤ D) {j : ℕ} (hj : j ≤ 817) :
    (activeFreqSet D j).card ≤ 17985 := by
  apply le_trans (Finset.card_filter_le _ _)
  by_cases hrange : max 1 (j - 5) ≤ min (maxBlockIndex D) (j + 5)
  · rw [card_biUnion_freqBlock _ _ hrange]
    by_cases hj6 : 6 ≤ j
    · -- j ≥ 6: max(1,j-5) = j-5
      have hmax : max 1 (j - 5) = j - 5 := by omega
      rw [hmax]
      -- (min(Λ,j+5)+1)^2 - (j-5)^2 ≤ (j+6)^2 - (j-5)^2 = 11*(2j+1) ≤ 17985
      have h_ub : min (maxBlockIndex D) (j + 5) + 1 ≤ j + 6 := by omega
      have h_sq : (min (maxBlockIndex D) (j + 5) + 1) ^ 2 ≤ (j + 6) ^ 2 := by
        nlinarith
      suffices (j + 6) ^ 2 - (j - 5) ^ 2 ≤ 17985 by omega
      suffices (j + 6) ^ 2 = (j - 5) ^ 2 + 11 * (2 * j + 1) by omega
      nlinarith [sq_nonneg (j - 5), Nat.sub_add_cancel (show 5 ≤ j by omega)]
    · -- j < 6: max(1,j-5) = 1
      have hmax : max 1 (j - 5) = 1 := by omega
      rw [hmax]
      have h_ub : min (maxBlockIndex D) (j + 5) + 1 ≤ j + 6 := by omega
      have h_sq : (min (maxBlockIndex D) (j + 5) + 1) ^ 2 ≤ (j + 6) ^ 2 := by
        nlinarith
      have h_jsm : (j + 6) ^ 2 ≤ 11 ^ 2 := by nlinarith
      omega
  · -- Empty range
    have : Finset.Icc (max 1 (j - 5)) (min (maxBlockIndex D) (j + 5)) = ∅ :=
      Finset.Icc_eq_empty (by omega)
    rw [this, Finset.biUnion_empty]; simp

/-! ## Theorem 6.1: Uniform local estimate on annuli -/

/-- Case 1 (j ≤ 817): Apply `local_circle_estimate` with `L ≤ 17985`. -/
private lemma annulus_low_freq {D : ℕ} (hD : 1 ≤ D) (a : Fin D → ℂ)
    (j : ℕ) (hj : j ≤ 817) {r : ℝ} (_hr : 0 ≤ r) :
    circleNormSq (fun t => localPoly a 5 j (↑r * (fourier 1 t : ℂ))) ≤
      1620 ^ 2 *
        (∫ t : AddCircle T,
          (rho (localPoly a 5 j (↑r * (fourier 1 t : ℂ)))) ^ 2
          ∂AddCircle.haarAddCircle) := by
  set P := fun t : AddCircle T => localPoly a 5 j (↑r * (fourier 1 t : ℂ))
  set E := activeFreqSet D j
  set b := localFourierCoeff a j r
  set L := E.card
  have hP_eq := localPoly_eq_fourierSum hD a j r
  by_cases hL_pos : 1 ≤ L
  · -- Nontrivial case: apply local_circle_estimate
    have hE_pos : ∀ n ∈ E, 1 ≤ n := fun n hn => activeFreqSet_pos hn
    have h_est := local_circle_estimate hL_pos rfl hE_pos b P hP_eq
    have hL_bound : L ≤ 17985 := activeFreqSet_card_le hD hj
    calc circleNormSq P
        ≤ 144 * ↑L * ∫ t, (rho (P t)) ^ 2 ∂AddCircle.haarAddCircle := h_est
      _ ≤ 1620 ^ 2 * ∫ t, (rho (P t)) ^ 2 ∂AddCircle.haarAddCircle := by
          apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun t => sq_nonneg _))
          calc (144 : ℝ) * ↑L
              ≤ 144 * 17985 := by
                apply mul_le_mul_of_nonneg_left (by exact_mod_cast hL_bound) (by norm_num)
            _ ≤ 1620 ^ 2 := by norm_num
  · -- Trivial case: L = 0 means P = 0
    push Not at hL_pos
    have hL_zero : L = 0 := by omega
    have hE_empty : E = ∅ := Finset.card_eq_zero.mp hL_zero
    -- P = 0 since the Fourier sum has no terms
    have hP_zero : P = fun _ => 0 := by
      show P = fun _ => 0
      conv_lhs => rw [show P = fun t =>
        localPoly a 5 j (↑r * (fourier 1 t : ℂ)) from rfl, hP_eq]
      ext t
      show ∑ n ∈ activeFreqSet D j, _ = 0
      rw [show activeFreqSet D j = E from rfl, hE_empty]
      simp
    simp only [hP_zero, circleNormSq, norm_zero, zero_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, integral_zero]
    apply mul_nonneg (by norm_num) (integral_nonneg (fun t => sq_nonneg _))

/-- The high-frequency NL condition: `1343 * (11(2j+1))² ≤ ((j-5)²)²` for `j ≥ 818`. -/
private lemma high_freq_NL_condition (j : ℕ) (hj : 818 ≤ j) :
    1343 * (11 * (2 * j + 1)) ^ 2 ≤ ((j - 5) ^ 2) ^ 2 := by
  zify [show 5 ≤ j by omega]
  set k := (j : ℤ) - 818
  have hk : 0 ≤ k := by omega
  rw [show (j : ℤ) - 5 = k + 813 from by omega,
      show 2 * (j : ℤ) + 1 = 2 * k + 1637 from by omega]
  nlinarith [sq_nonneg k, sq_nonneg (k * k),
    sq_nonneg (k * (k + 813)), hk]

/-- `activeFreqSet` is contained in `Icc (j-5)² ((j+6)²-1)` for `j ≥ 6`. -/
private lemma activeFreqSet_subset_Icc {D j : ℕ} (hj6 : 6 ≤ j) :
    activeFreqSet D j ⊆
      Finset.Icc ((j - 5) ^ 2) ((j + 6) ^ 2 - 1) := by
  intro n hn
  simp only [activeFreqSet, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_Icc] at hn
  obtain ⟨⟨ℓ, hℓ_range, hn_block⟩, _⟩ := hn
  simp only [freqBlock, Finset.mem_Icc] at hn_block hℓ_range
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · have : j - 5 ≤ ℓ := by omega
    nlinarith
  · have : ℓ + 1 ≤ j + 6 := by omega
    have : (ℓ + 1) ^ 2 ≤ (j + 6) ^ 2 :=
      Nat.pow_le_pow_left this 2
    omega

/-- `localFourierCoeff` vanishes outside `activeFreqSet`. -/
private lemma localFourierCoeff_zero_outside {D : ℕ} (a : Fin D → ℂ)
    (j : ℕ) (r : ℝ) {n : ℕ} (hn : n ∉ activeFreqSet D j) :
    localFourierCoeff a j r n = 0 := by
  unfold localFourierCoeff
  rw [dif_neg]
  intro ⟨h_mem, h1, hD⟩
  exact hn (Finset.mem_filter.mpr ⟨h_mem, hD⟩)

/-- The Fourier sum over `activeFreqSet` equals the sum over `Icc N (N+L-1)`, since
    `localFourierCoeff` is zero outside the active set. -/
private lemma fourierSum_extend_to_Icc {D : ℕ} (a : Fin D → ℂ) (j : ℕ)
    (r : ℝ) (hj6 : 6 ≤ j) (t : AddCircle T) :
    ∑ n ∈ activeFreqSet D j,
      localFourierCoeff a j r n * fourier (n : ℤ) t =
    ∑ n ∈ Finset.Icc ((j - 5) ^ 2) ((j + 6) ^ 2 - 1),
      localFourierCoeff a j r n * fourier (n : ℤ) t := by
  apply Finset.sum_subset (activeFreqSet_subset_Icc hj6)
  intro n _ hn_not
  simp [localFourierCoeff_zero_outside a j r hn_not]

-- to_mathlib: Mathlib/Algebra/BigOperators/Intervals
/-- Reindex a sum over `Icc N (N+L-1)` to `Fin L`. -/
private lemma sum_Icc_eq_sum_Fin {α : Type*} [AddCommMonoid α]
    (N L : ℕ) (hL : 1 ≤ L) (f : ℕ → α) :
    ∑ n ∈ Finset.Icc N (N + L - 1), f n =
    ∑ m : Fin L, f (N + m.val) := by
  symm
  apply Finset.sum_nbij (fun (m : Fin L) => N + m.val)
  · intro ⟨m, hm⟩ _
    exact Finset.mem_Icc.mpr
      ⟨Nat.le_add_right N m, by omega⟩
  · intro a _ b _ (h : N + a.val = N + b.val)
    exact Fin.ext (by omega)
  · intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    exact ⟨⟨n - N, by omega⟩, Finset.mem_univ _,
      by change N + (n - N) = n; omega⟩
  · intro _ _; rfl

/-- `(j+6)^2 - 1 = (j-5)^2 + (11*(2*j+1)) - 1` for `j ≥ 5`. -/
private lemma freq_range_eq (j : ℕ) (hj : 5 ≤ j) :
    (j + 6) ^ 2 - 1 = (j - 5) ^ 2 + (11 * (2 * j + 1)) - 1 := by
  zify [show (j - 5) ^ 2 + (11 * (2 * j + 1)) ≥ 1 from by nlinarith,
        show (j + 6) ^ 2 ≥ 1 from by nlinarith, show 5 ≤ j from hj]
  ring

/-- Case 2 (j ≥ 818): Apply `high_freq_band_estimate`. The high-frequency condition
    `1342 * L^2 ≤ N^2` is verified via monotonicity and the numerical check at j = 818. -/
private lemma annulus_high_freq {D : ℕ} (hD : 1 ≤ D) (a : Fin D → ℂ)
    (j : ℕ) (hj : 818 ≤ j) {r : ℝ} (_hr : 0 ≤ r) :
    circleNormSq (fun t => localPoly a 5 j (↑r * (fourier 1 t : ℂ))) ≤
      1620 ^ 2 *
        (∫ t : AddCircle T,
          (rho (localPoly a 5 j (↑r * (fourier 1 t : ℂ)))) ^ 2
          ∂AddCircle.haarAddCircle) := by
  set P := fun t : AddCircle T =>
    localPoly a 5 j (↑r * (fourier 1 t : ℂ))
  -- Parameters for high_freq_band_estimate
  set N := (j - 5) ^ 2
  set L := 11 * (2 * j + 1)
  -- Coefficients for the reindexed sum
  set b : Fin L → ℂ := fun m => localFourierCoeff a j r (N + m.val)
  -- Key range identity
  have hj5 : 5 ≤ j := by omega
  have hj6 : 6 ≤ j := by omega
  have hL_pos : 1 ≤ L := by omega
  have hN_pos : 1 ≤ N := Nat.one_le_pow 2 _ (by omega)
  -- The NL condition
  have hNL : 1343 * L ^ 2 ≤ N ^ 2 :=
    high_freq_NL_condition j hj
  -- Express P as a high-frequency Fourier sum
  have hP_eq : P = fun t =>
      ∑ m : Fin L, b m * fourier ((N + m.val : ℕ) : ℤ) t := by
    ext t
    -- P(t) = ∑ n ∈ activeFreqSet, localFourierCoeff * fourier n t
    have h1 := localPoly_eq_fourierSum hD a j r
    -- = ∑ n ∈ Icc N (N+L-1), localFourierCoeff * fourier n t
    have h2 := fourierSum_extend_to_Icc a j r hj6 t
    -- = ∑ m : Fin L, b m * fourier (N+m) t
    have hrange : (j + 6) ^ 2 - 1 =
        (j - 5) ^ 2 + (11 * (2 * j + 1)) - 1 :=
      freq_range_eq j hj5
    change P t = ∑ m : Fin L,
      b m * fourier ((N + m.val : ℕ) : ℤ) t
    -- P t = localPoly ... = ∑ activeFreqSet = ∑ Icc = ∑ Fin L
    have hPt : P t = ∑ n ∈ activeFreqSet D j,
        localFourierCoeff a j r n * fourier (n : ℤ) t :=
      congr_fun h1 t
    rw [hPt, h2, hrange]
    exact sum_Icc_eq_sum_Fin N L hL_pos _
  -- Apply high_freq_band_estimate
  have hband := high_freq_band_estimate hN_pos hL_pos hNL b P hP_eq
  -- Scale: 32 ≤ 1620²
  calc circleNormSq P
      ≤ 32 * (∫ t, (rho (P t)) ^ 2
          ∂AddCircle.haarAddCircle) := hband
    _ ≤ 1620 ^ 2 * (∫ t, (rho (P t)) ^ 2
          ∂AddCircle.haarAddCircle) := by
        apply mul_le_mul_of_nonneg_right _ (integral_nonneg
          (fun t => sq_nonneg _))
        norm_num

theorem annulus_local_estimate {D : ℕ} (hD : 1 ≤ D) (a : Fin D → ℂ)
    (j : ℕ) {r : ℝ} (hr_nn : 0 ≤ r) (_hr_lo : (j : ℝ) ≤ r)
    (_hr_hi : r ≤ (j : ℝ) + 1) :
    circleNormSq (fun t => localPoly a 5 j (↑r * (fourier 1 t : ℂ))) ≤
      1620 ^ 2 *
        (∫ t : AddCircle T,
          (rho (localPoly a 5 j (↑r * (fourier 1 t : ℂ)))) ^ 2
          ∂AddCircle.haarAddCircle) := by
  by_cases hj : j ≤ 817
  · exact annulus_low_freq hD a j hj hr_nn
  · exact annulus_high_freq hD a j (by omega) hr_nn

end FockSPR
