/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStoppingRecursion
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Log

/-!
# Finite signed-sum and dyadic prefix estimates for Rademacher--Menshov

The signed-sum hypothesis used in KL18 (2.8) is kept explicit. In particular,
no orthogonality of the actual oscillatory pieces is silently assumed.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyRademacherMenshov


/-- For finitely many Hilbert-space vectors, some choice of signs has
squared norm at least the sum of their squared norms. This is the finite
random-sign argument, proved deterministically from the parallelogram law. -/
theorem exists_signs_sum_norm_sq_le
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (v : ι → E) :
    ∃ c : ι → ℝ, (∀ i, c i = 1 ∨ c i = -1) ∧
      (∑ i ∈ s, ‖v i‖ ^ 2) ≤ ‖∑ i ∈ s, c i • v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ ↦ 1, fun _ ↦ Or.inl rfl, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨c, hc, hsum⟩ := ih
    let w := ∑ i ∈ s, c i • v i
    have hpar := parallelogram_law_with_norm ℝ (v a) w
    have hupdate (r : ℝ) :
        (∑ i ∈ insert a s, Function.update c a r i • v i) = r • v a + w := by
      rw [Finset.sum_insert ha, Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
    by_cases hplus : ‖v a‖ ^ 2 + ‖w‖ ^ 2 ≤ ‖v a + w‖ ^ 2
    · refine ⟨Function.update c a 1, ?_, ?_⟩
      · intro i
        by_cases hi : i = a
        · simp [hi]
        · simpa only [Function.update_of_ne hi] using hc i
      · rw [hupdate, one_smul, Finset.sum_insert ha]
        exact (add_le_add (le_refl _) hsum).trans hplus
    · refine ⟨Function.update c a (-1), ?_, ?_⟩
      · intro i
        by_cases hi : i = a
        · simp [hi]
        · simpa only [Function.update_of_ne hi] using hc i
      · rw [hupdate, neg_one_smul, Finset.sum_insert ha]
        have heq : ‖-v a + w‖ = ‖v a - w‖ := by
          rw [show -v a + w = -(v a - w) by abel, norm_neg]
        rw [heq]
        change (∑ i ∈ s, ‖v i‖ ^ 2) ≤ ‖w‖ ^ 2 at hsum
        linarith

/-- The exact finite signed-sum condition of KL18 (2.8), in squared form.
The signs are constant coefficients, not functions of the spatial variable. -/
def HasSignedSumSquareBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (v : ℕ → E) (B : ℝ) : Prop :=
  ∀ c : ℕ → ℝ, (∀ i < N, c i = 0 ∨ c i = 1 ∨ c i = -1) →
    ‖∑ i ∈ Finset.range N, c i • v i‖ ^ 2 ≤ B

/-- A dyadic block is defined by the quotient index, with the original
finite sequence length retained. The last block is automatically truncated. -/
noncomputable def dyadicBlock (N l q : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun i ↦ i / 2 ^ l = q

/-- The sum of the sequence over one truncated dyadic block. -/
noncomputable def blockSum {E : Type*} [AddCommMonoid E]
    (N l q : ℕ) (v : ℕ → E) : E := ∑ i ∈ dyadicBlock N l q, v i

/-- Signed block sums are genuine signed sums of the original sequence;
quotient-index blocks partition the finite index set exactly. -/
theorem sum_signed_blocks_eq
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (N l : ℕ) (c : ℕ → ℝ) (v : ℕ → E) :
    (∑ q ∈ Finset.range (N + 1), c q • blockSum N l q v) =
      ∑ i ∈ Finset.range N, c (i / 2 ^ l) • v i := by
  classical
  simp only [blockSum, dyadicBlock, Finset.sum_filter, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hq : i / 2 ^ l < N + 1 :=
    (Nat.div_le_self i _).trans_lt (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))
  simp [Finset.mem_range.mpr hq]

/-- A single dyadic generation has square energy bounded by the same
signed-sum constant, with no loss in the number of blocks. -/
theorem sum_norm_sq_blocks_le_signedBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N l : ℕ) (v : ℕ → E) {B : ℝ} (hB : HasSignedSumSquareBound N v B) :
    (∑ q ∈ Finset.range (N + 1), ‖blockSum N l q v‖ ^ 2) ≤ B := by
  obtain ⟨c, hc, henergy⟩ := exists_signs_sum_norm_sq_le (Finset.range (N + 1))
    (fun q ↦ blockSum N l q v)
  rw [sum_signed_blocks_eq] at henergy
  exact henergy.trans (hB (fun i ↦ c (i / 2 ^ l)) fun i _ ↦
    (hc (i / 2 ^ l)).elim (fun h ↦ Or.inr (Or.inl h)) (fun h ↦ Or.inr (Or.inr h)))

/-- The indices below the dyadic block containing the prefix endpoint. -/
noncomputable def coarsePrefix (N n l : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun i ↦ i / 2 ^ l < n / 2 ^ l

theorem div_pow_succ (n l : ℕ) : n / 2 ^ (l + 1) = (n / 2 ^ l) / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

theorem coarsePrefix_succ_subset (N n l : ℕ) :
    coarsePrefix N n (l + 1) ⊆ coarsePrefix N n l := by
  intro i hi
  have h := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨h.1, ?_⟩
  simp only [div_pow_succ] at h
  omega

/-- Each adjacent pair of coarse prefixes differs by either no indices or
exactly one dyadic block. This is the finite binary-prefix decomposition. -/
theorem coarsePrefix_sdiff_eq
    (N n l : ℕ) :
    coarsePrefix N n l \ coarsePrefix N n (l + 1) =
      if (n / 2 ^ l) % 2 = 0 then ∅ else dyadicBlock N l (n / 2 ^ l - 1) := by
  classical
  have harith (a b : ℕ) :
      a < b ∧ ¬a / 2 < b / 2 ↔ b % 2 ≠ 0 ∧ a = b - 1 := by omega
  ext i
  simp only [Finset.mem_sdiff, coarsePrefix, dyadicBlock, Finset.mem_filter, div_pow_succ]
  have h := harith (i / 2 ^ l) (n / 2 ^ l)
  split_ifs with hn
  · simp only [Finset.notMem_empty]
    tauto
  · simp only [Finset.mem_filter]
    tauto

/-- The prefix sums telescope over their binary quotient scales. -/
theorem prefixSum_eq_sum_differences
    {E : Type*} [AddCommGroup E] (N n d : ℕ) (hn : n ≤ N) (hd : n < 2 ^ (d + 1))
    (v : ℕ → E) :
    (∑ i ∈ Finset.range n, v i) =
      ∑ l ∈ Finset.range (d + 1),
        ((∑ i ∈ coarsePrefix N n l, v i) -
          ∑ i ∈ coarsePrefix N n (l + 1), v i) := by
  have hzero : coarsePrefix N n 0 = Finset.range n := by
    ext i
    simp only [coarsePrefix, pow_zero, Nat.div_one, Finset.mem_filter, Finset.mem_range]
    omega
  have hlast : coarsePrefix N n (d + 1) = ∅ := by
    simp [coarsePrefix, Nat.div_eq_of_lt hd]
  rw [Finset.sum_range_sub', hzero, hlast, Finset.sum_empty, sub_zero]

/-- The energy of one binary-prefix increment is bounded by the energy
of its whole generation. -/
theorem norm_sq_prefix_difference_le
    {E : Type*} [NormedAddCommGroup E] (N n l : ℕ) (hn : n ≤ N) (v : ℕ → E) :
    ‖(∑ i ∈ coarsePrefix N n l, v i) -
      ∑ i ∈ coarsePrefix N n (l + 1), v i‖ ^ 2 ≤
      ∑ q ∈ Finset.range (N + 1), ‖blockSum N l q v‖ ^ 2 := by
  classical
  rw [← Finset.sum_sdiff (coarsePrefix_succ_subset N n l), add_sub_cancel_right,
    coarsePrefix_sdiff_eq]
  split_ifs with h
  · simp only [Finset.sum_empty, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  · have hq : n / 2 ^ l - 1 < N + 1 := by
      have := Nat.div_le_self n (2 ^ l)
      omega
    exact Finset.single_le_sum (fun q _ ↦ sq_nonneg ‖blockSum N l q v‖)
      (Finset.mem_range.mpr hq)

/-- The pointwise binary-prefix estimate: only `d + 1` generations are
needed, so Cauchy--Schwarz costs exactly `d + 1`. -/
theorem norm_sq_prefix_le_dyadicEnergy
    {E : Type*} [NormedAddCommGroup E]
    (N n d : ℕ) (hn : n ≤ N) (hd : n < 2 ^ (d + 1)) (v : ℕ → E) :
    ‖∑ i ∈ Finset.range n, v i‖ ^ 2 ≤
      (d + 1 : ℝ) * ∑ l ∈ Finset.range (d + 1),
        ∑ q ∈ Finset.range (N + 1), ‖blockSum N l q v‖ ^ 2 := by
  rw [prefixSum_eq_sum_differences N n d hn hd]
  calc
    _ ≤ (∑ l ∈ Finset.range (d + 1),
        ‖(∑ i ∈ coarsePrefix N n l, v i) -
          ∑ i ∈ coarsePrefix N n (l + 1), v i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (d + 1 : ℝ) * ∑ l ∈ Finset.range (d + 1),
        ‖(∑ i ∈ coarsePrefix N n l, v i) -
          ∑ i ∈ coarsePrefix N n (l + 1), v i‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq
        (s := Finset.range (d + 1))
        (f := fun l ↦ ‖(∑ i ∈ coarsePrefix N n l, v i) -
          ∑ i ∈ coarsePrefix N n (l + 1), v i‖)
    _ ≤ _ := by
      gcongr with l hl
      exact norm_sq_prefix_difference_le N n l hn v

section L2

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The actual finite maximal partial sum, including the empty prefix. -/
noncomputable def finitePrefixMaximal (N : ℕ) (v : ℕ → Lp ℂ 2 μ) (x : X) : ℝ :=
  ⨆ n : Fin (N + 1), ‖∑ i ∈ Finset.range n.val, v i x‖

theorem finitePrefixMaximal_nonneg (N : ℕ) (v : ℕ → Lp ℂ 2 μ) (x : X) :
    0 ≤ finitePrefixMaximal N v x := by
  have h := le_ciSup (Set.finite_range
    (fun n : Fin (N + 1) ↦ ‖∑ i ∈ Finset.range n.val, v i x‖)).bddAbove
    (0 : Fin (N + 1))
  simpa [finitePrefixMaximal] using h

theorem integral_sq_norm_Lp (u : Lp ℂ 2 μ) :
    (∫ x, ‖u x‖ ^ 2 ∂μ) = ‖u‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) u u).symm

theorem integrable_sq_norm_blockSum (N l q : ℕ) (v : ℕ → Lp ℂ 2 μ) :
    Integrable (fun x ↦ ‖blockSum N l q (fun i ↦ v i x)‖ ^ 2) μ := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable
    (blockSum N l q v))).mp (Lp.memLp _)
  apply h.congr
  filter_upwards [Lp.coeFn_finsetSum (dyadicBlock N l q) v] with x hx
  simp only [blockSum] at *
  simp only [hx, Finset.sum_apply]

theorem integral_sq_norm_blockSum (N l q : ℕ) (v : ℕ → Lp ℂ 2 μ) :
    (∫ x, ‖blockSum N l q (fun i ↦ v i x)‖ ^ 2 ∂μ) = ‖blockSum N l q v‖ ^ 2 := by
  rw [← integral_sq_norm_Lp]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_finsetSum (dyadicBlock N l q) v] with x hx
  simp only [blockSum] at *
  simp only [hx, Finset.sum_apply]

theorem aemeasurable_finitePrefixMaximal (N : ℕ) (v : ℕ → Lp ℂ 2 μ) :
    AEMeasurable (finitePrefixMaximal N v) μ := by
  apply AEMeasurable.iSup
  intro n
  exact ((Finset.range n.val).aestronglyMeasurable_fun_sum
    (fun i _ ↦ Lp.aestronglyMeasurable (v i))).norm.aemeasurable

/-- All prefix maxima are controlled by one common finite square-energy
majorant, so no choice of a spatially varying sign sequence is used. -/
theorem finitePrefixMaximal_sq_le (N d : ℕ) (hd : N < 2 ^ (d + 1))
    (v : ℕ → Lp ℂ 2 μ) (x : X) :
    finitePrefixMaximal N v x ^ 2 ≤
      (d + 1 : ℝ) * ∑ l ∈ Finset.range (d + 1),
        ∑ q ∈ Finset.range (N + 1), ‖blockSum N l q (fun i ↦ v i x)‖ ^ 2 := by
  obtain ⟨n, hn⟩ := exists_eq_ciSup_of_finite
    (f := fun n : Fin (N + 1) ↦ ‖∑ i ∈ Finset.range n.val, v i x‖)
  change _ = finitePrefixMaximal N v x at hn
  rw [← hn]
  exact norm_sq_prefix_le_dyadicEnergy N n.val d (by omega)
    ((show n.val ≤ N by omega).trans_lt hd) (fun i ↦ v i x)

/-- Integrability of the square of the actual finite maximal partial sum. -/
theorem integrable_finitePrefixMaximal_sq (N d : ℕ) (hd : N < 2 ^ (d + 1))
    (v : ℕ → Lp ℂ 2 μ) :
    Integrable (fun x ↦ finitePrefixMaximal N v x ^ 2) μ := by
  have hmajor := (integrable_finsetSum (Finset.range (d + 1)) fun l _ ↦
    integrable_finsetSum (Finset.range (N + 1)) fun q _ ↦
      integrable_sq_norm_blockSum N l q v).const_mul (d + 1 : ℝ)
  apply hmajor.mono_nonneg
    ((aemeasurable_finitePrefixMaximal N v).pow_const 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ sq_nonneg _
  · exact Filter.Eventually.of_forall (finitePrefixMaximal_sq_le N d hd v)

/-- Finite Rademacher--Menshov with an explicit constant and explicit
prefix order. A bound `B` on every constant signed sum gives squared maximal
`L²` norm at most `(d + 1)² B` whenever `N < 2^(d+1)`. -/
theorem integral_finitePrefixMaximal_sq_le
    (N d : ℕ) (hd : N < 2 ^ (d + 1)) (v : ℕ → Lp ℂ 2 μ)
    {B : ℝ} (hB : HasSignedSumSquareBound N v B) :
    (∫ x, finitePrefixMaximal N v x ^ 2 ∂μ) ≤ (d + 1 : ℝ) ^ 2 * B := by
  have hblocks (l : ℕ) := integrable_finsetSum (Finset.range (N + 1))
    (fun q _ ↦ integrable_sq_norm_blockSum N l q v)
  have hmajor := (integrable_finsetSum (Finset.range (d + 1))
    (fun l _ ↦ hblocks l)).const_mul (d + 1 : ℝ)
  calc
    _ ≤ ∫ x, (d + 1 : ℝ) * ∑ l ∈ Finset.range (d + 1),
        ∑ q ∈ Finset.range (N + 1), ‖blockSum N l q (fun i ↦ v i x)‖ ^ 2 ∂μ :=
      integral_mono (integrable_finitePrefixMaximal_sq N d hd v) hmajor
        (finitePrefixMaximal_sq_le N d hd v)
    _ = (d + 1 : ℝ) * ∑ l ∈ Finset.range (d + 1),
        ∑ q ∈ Finset.range (N + 1), ‖blockSum N l q v‖ ^ 2 := by
      rw [integral_const_mul, integral_finsetSum _ (fun l _ ↦ hblocks l)]
      congr 1
      apply Finset.sum_congr rfl
      intro l hl
      rw [integral_finsetSum _ (fun q _ ↦ integrable_sq_norm_blockSum N l q v)]
      simp_rw [integral_sq_norm_blockSum]
    _ ≤ (d + 1 : ℝ) * ∑ _l ∈ Finset.range (d + 1), B := by
      gcongr with l hl
      exact sum_norm_sq_blocks_le_signedBound N l v hB
    _ = _ := by simp; ring

/-- The finite Rademacher--Menshov estimate with its logarithmic loss
written using the binary logarithm, including `N = 0`. -/
theorem integral_finitePrefixMaximal_sq_le_log2
    (N : ℕ) (v : ℕ → Lp ℂ 2 μ)
    {B : ℝ} (hB : HasSignedSumSquareBound N v B) :
    (∫ x, finitePrefixMaximal N v x ^ 2 ∂μ) ≤ (Nat.log2 N + 1 : ℝ) ^ 2 * B := by
  apply integral_finitePrefixMaximal_sq_le N (Nat.log2 N) _ v hB
  simpa only [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) N

theorem memLp_finitePrefixMaximal (N : ℕ) (v : ℕ → Lp ℂ 2 μ) :
    MemLp (finitePrefixMaximal N v) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (aemeasurable_finitePrefixMaximal N v).aestronglyMeasurable).mpr
  apply integrable_finitePrefixMaximal_sq N (Nat.log2 N) _ v
  simpa only [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) N

/-- An extended-norm version of the same squared estimate. -/
theorem eLpNorm_finitePrefixMaximal_sq_le_log2
    (N : ℕ) (v : ℕ → Lp ℂ 2 μ)
    {B : ℝ} (hB : HasSignedSumSquareBound N v B) :
    eLpNorm (finitePrefixMaximal N v) 2 μ ^ 2 ≤
      ENNReal.ofReal ((Nat.log2 N + 1 : ℝ) ^ 2 * B) := by
  have heq : eLpNorm (finitePrefixMaximal N v) 2 μ ^ 2 =
      ∫⁻ x, ‖finitePrefixMaximal N v x‖ₑ ^ 2 ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (aemeasurable_finitePrefixMaximal N v).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [← ENNReal.rpow_mul_natCast]
    norm_num
  rw [heq]
  have hreal := ofReal_integral_eq_lintegral_ofReal
    (memLp_finitePrefixMaximal N v).integrable_sq
    (Filter.Eventually.of_forall fun x ↦ sq_nonneg (finitePrefixMaximal N v x))
  have heq' : (∫⁻ x, ‖finitePrefixMaximal N v x‖ₑ ^ 2 ∂μ) =
      ENNReal.ofReal (∫ x, finitePrefixMaximal N v x ^ 2 ∂μ) := by
    rw [hreal]
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
    simp
  rw [heq']
  exact ENNReal.ofReal_le_ofReal (integral_finitePrefixMaximal_sq_le_log2 N v hB)

/-- The norm form of KL18's finite Rademacher--Menshov lemma, with the
universal constant equal to one for the binary-logarithm normalization. -/
theorem eLpNorm_finitePrefixMaximal_le_log2
    (N : ℕ) (v : ℕ → Lp ℂ 2 μ)
    {A : ℝ} (hA : 0 ≤ A) (hB : HasSignedSumSquareBound N v (A ^ 2)) :
    eLpNorm (finitePrefixMaximal N v) 2 μ ≤
      ENNReal.ofReal ((Nat.log2 N + 1 : ℝ) * A) := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [ENNReal.rpow_two, ENNReal.rpow_two,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ (Nat.log2 N + 1 : ℝ) * A), mul_pow]
  exact eLpNorm_finitePrefixMaximal_sq_le_log2 N v hB

end L2


end KrauseLaceyRademacherMenshov
end QuadraticCarleson
