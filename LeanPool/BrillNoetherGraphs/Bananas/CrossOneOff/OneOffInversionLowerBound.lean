/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.OneOffPeriodBound
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointCardinality

/-!
# The immediate one-off inversion bound

This formalizes the unnamed proposition immediately following Lemma 4.23.
The selected positive-residue rows form a strictly decreasing subsequence of
length `(n-2) * floor(g/(n-1))`, hence contribute the corresponding binomial
number of distinct `k`-inversions.
-/

namespace Bananas

open Utilities

/-- Increasing enumeration of the positive residues in blocks of width
`n`: two residue classes (`0` and `n-1`) are skipped per block. -/
def oneOffPositiveIndex (n t : ℕ) : ℕ :=
  t + 2 * (t / (n - 2)) + 1

theorem oneOffPositiveIndex_strictMono {n : ℕ} (_hn : 2 < n) :
    StrictMono (oneOffPositiveIndex n) := by
  apply strictMono_nat_of_lt_succ
  intro t
  unfold oneOffPositiveIndex
  have hDiv : t / (n - 2) ≤ (t + 1) / (n - 2) :=
    Nat.div_le_div_right (by omega)
  omega

noncomputable def indexedPairEmbedding (index : ℕ → ℕ) (length : ℕ) :
    Sym2 (Fin length) → ℤ × ℤ :=
  Sym2.lift ⟨(fun a b =>
    ((index (min a.val b.val) : ℕ),
      (index (max a.val b.val + 1) : ℕ))), by
        intro a b
        simp [min_comm, max_comm]⟩

theorem indexedPairEmbedding_injective
    {index : ℕ → ℕ} (hIndex : Function.Injective index) (length : ℕ) :
    Function.Injective (indexedPairEmbedding index length) := by
  intro x y hxy
  induction x using Sym2.ind with
  | _ a b =>
    induction y using Sym2.ind with
    | _ c d =>
      simp only [indexedPairEmbedding, Sym2.lift_mk, Prod.mk.injEq] at hxy
      have hMin : min a.val b.val = min c.val d.val := by
        apply hIndex
        exact_mod_cast hxy.1
      have hMax : max a.val b.val + 1 = max c.val d.val + 1 := by
        apply hIndex
        exact_mod_cast hxy.2
      apply endpointPairEmbedding_injective length
      simp only [endpointPairEmbedding, Sym2.lift_mk, Prod.mk.injEq]
      exact ⟨by exact_mod_cast hMin, by exact_mod_cast hMax⟩

/-- A decreasing sequence sampled at arbitrary strictly increasing natural
indices contributes all of its pairwise inversions.  The bound on possible
first coordinates is stated only for `i < length`; the last sampled point
can occur only as a second coordinate. -/
theorem indexed_decreasing_inversion_lower_bound
    {length value k : ℕ} {index : ℕ → ℕ} {tau : ℤ → ℤ}
    (hIndex : StrictMono index) (hValue : length ≤ value)
    (hFirst : ∀ i : ℕ, i < length → index i < k)
    (hBlock : ∀ i : ℕ, i ≤ length → tau (index i) = (value - i : ℕ))
    (hfinite : (kInversions k tau).Finite) :
    Nat.choose (length + 1) 2 ≤ kInversionCount k tau := by
  have hmap : ∀ x : Sym2 (Fin length), x ∈ Set.univ →
      indexedPairEmbedding index length x ∈ kInversions k tau := by
    intro x _
    induction x using Sym2.ind with
    | _ a b =>
      simp only [indexedPairEmbedding, Sym2.lift_mk, kInversions,
        Set.mem_ofPred_eq]
      let m := min a.val b.val
      let n := max a.val b.val + 1
      have hmn : m < n := by
        dsimp [m, n]
        omega
      have hnle : n ≤ length := by
        dsimp [n]
        exact Nat.succ_le_of_lt (max_lt a.isLt b.isLt)
      have hmLt : m < length := hmn.trans_le hnle
      have hmle : m ≤ length := hmLt.le
      have htm := hBlock m hmle
      have htn := hBlock n hnle
      change (index m : ℤ) < index n ∧ tau (index m) > tau (index n) ∧
        0 ≤ (index m : ℤ) ∧ (index m : ℤ) < k
      rw [htm, htn]
      refine ⟨by exact_mod_cast hIndex hmn, ?_, by positivity, ?_⟩
      · have hnValue : n ≤ value := hnle.trans hValue
        exact_mod_cast (show value - n < value - m by omega)
      · exact_mod_cast hFirst m hmLt
  have hle := Set.ncard_le_ncard_of_injOn
    (s := (Set.univ : Set (Sym2 (Fin length))))
    (t := kInversions k tau) (indexedPairEmbedding index length)
    hmap (indexedPairEmbedding_injective hIndex.injective length).injOn hfinite
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hle
  change (Finset.univ : Finset (Sym2 (Fin length))).card ≤ _ at hle
  rw [← Finset.sym2_univ, Finset.card_sym2, Finset.card_univ] at hle
  simpa [kInversionCount] using hle

private theorem oneOffPositiveIndex_data
    {g n t : ℕ} (hn : 2 < n)
    (ht : t < (n - 2) * (g / (n - 1))) :
    let q := t / (n - 2)
    let r := t % (n - 2) + 1
    oneOffPositiveIndex n t = q * n + r ∧
      1 ≤ r ∧ r + 1 < n ∧
      oneOffPositiveIndex n t ≤ g + q ∧
      oneOffPositiveIndex n t < crossOneOffCutoff g n := by
  let q := t / (n - 2)
  let s := t % (n - 2)
  let r := s + 1
  have hdPos : 0 < n - 2 := by omega
  have hsLt : s < n - 2 := by
    dsimp [s]
    exact Nat.mod_lt t hdPos
  have htDecompose : t = q * (n - 2) + s := by
    dsimp [q, s]
    simpa [Nat.mul_comm] using (Nat.div_add_mod t (n - 2)).symm
  have hqLt : q < g / (n - 1) := by
    apply (Nat.div_lt_iff_lt_mul hdPos).2
    simpa [Nat.mul_comm] using ht
  have hqMul : (g / (n - 1)) * (n - 1) ≤ g := by
    exact Nat.div_mul_le_self g (n - 1)
  have hIndex : oneOffPositiveIndex n t = q * n + r := by
    unfold oneOffPositiveIndex
    change t + 2 * q + 1 = q * n + r
    rw [htDecompose]
    dsimp [r]
    have hnEq : n = (n - 2) + 2 := by omega
    have hqn : q * n = q * (n - 2) + 2 * q := by
      calc
        q * n = q * ((n - 2) + 2) := congrArg (q * ·) hnEq
        _ = q * (n - 2) + 2 * q := by
          rw [Nat.mul_add]
          exact congrArg (q * (n - 2) + ·) (Nat.mul_comm q 2)
    rw [hqn]
    omega
  have hResidual : q * (n - 1) + r ≤ g := by
    have hqSucc : q + 1 ≤ g / (n - 1) := by omega
    have hrLe : r ≤ n - 2 := by
      dsimp [r]
      omega
    have hBlockLe : q * (n - 1) + r ≤ (q + 1) * (n - 1) := by
      rw [Nat.add_mul, one_mul]
      omega
    have hMul : (q + 1) * (n - 1) ≤ (g / (n - 1)) * (n - 1) :=
      Nat.mul_le_mul_right (n - 1) hqSucc
    exact hBlockLe.trans (hMul.trans hqMul)
  have hBound : oneOffPositiveIndex n t ≤ g + q := by
    rw [hIndex]
    have hnEq : n = (n - 1) + 1 := by omega
    rw [hnEq, Nat.mul_add, Nat.mul_one]
    omega
  have hrLo : 1 ≤ r := by
    dsimp [r]
    omega
  have hrHi : r + 1 < n := by
    dsimp [r]
    omega
  refine ⟨hIndex, hrLo, hrHi, hBound, ?_⟩
  · unfold crossOneOffCutoff
    omega

/-- The corrected form of the immediate inversion lower bound following
Lemma 4.23. -/
theorem oneOff_inversion_lower_bound
    {g k : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (tau : ℤ → ℤ) (hg : 2 ≤ g) (hk : 0 < k)
    (hLength : 1 < B.length alpha)
    (hTau : IsTransmissionPermutation
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (g • one_chip (rightEndpoint B)) tau)
    (hAffine : IsKAffine k tau)
    (hfinite : (kInversions k tau).Finite) :
    Nat.choose
      ((B.length alpha - 2) * (g / (B.length alpha - 1))) 2 ≤
        kInversionCount k tau := by
  let n := B.length alpha
  let f := g / (n - 1)
  let total := (n - 2) * f
  by_cases hnTwo : n = 2
  · have hLenTwo : B.length alpha = 2 := by simpa [n] using hnTwo
    rw [hLenTwo]
    simp
  have hn : 2 < n := by
    have : 1 < n := by simpa [n] using hLength
    omega
  by_cases hfZero : f = 0
  · have hfZero' : g / (B.length alpha - 1) = 0 := by
      simpa [f, n] using hfZero
    rw [hfZero']
    simp
  have hTotalPos : 0 < total := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hfZero)
  have hPeriod := oneOff_affine_period_gt_cutoff B alpha tau hg hk hLength
    hTau hAffine
  have hIndex := oneOffPositiveIndex_strictMono hn
  have hBlock : ∀ i : ℕ, i ≤ total - 1 →
      tau (oneOffPositiveIndex n i) = (g - i : ℕ) := by
    intro i hi
    have hiTotal : i < total := by omega
    obtain ⟨hDecompose, hrLo, hrHi, hBound, _⟩ :=
      oneOffPositiveIndex_data (g := g) (n := n) hn (by simpa [total, f] using hiTotal)
    let q := i / (n - 2)
    let r := i % (n - 2) + 1
    have hRow := transmission_oneOff_positive_residue B alpha
      (oneOffPositiveIndex n i) q r tau hg hLength
      (by simpa [q, r] using hDecompose) hrLo hrHi hBound hTau
    have hIndexFormula : oneOffPositiveIndex n i = i + 2 * q + 1 := rfl
    rw [hRow]
    dsimp [q]
    rw [hIndexFormula]
    omega
  have hFirst : ∀ i : ℕ, i < total - 1 → oneOffPositiveIndex n i < k := by
    intro i hi
    have hiTotal : i < total := by omega
    have hData := oneOffPositiveIndex_data (g := g) (n := n) hn
      (by simpa [total, f] using hiTotal)
    exact hData.2.2.2.2.trans hPeriod
  have hValue : total - 1 ≤ g := by
    have hFactor : n - 2 ≤ n - 1 := by omega
    have hTotalLeMul : (n - 2) * f ≤ (n - 1) * f :=
      Nat.mul_le_mul_right f hFactor
    have hMul : (n - 1) * f ≤ g := by
      simpa [f, Nat.mul_comm] using Nat.div_mul_le_self g (n - 1)
    have hTotalLe : total ≤ g := by
      simpa [total] using hTotalLeMul.trans hMul
    omega
  have hCount := indexed_decreasing_inversion_lower_bound
    (length := total - 1) (value := g) (k := k)
    (index := oneOffPositiveIndex n) (tau := tau)
    hIndex hValue hFirst hBlock hfinite
  have hLengthCount : total - 1 + 1 = total := Nat.sub_add_cancel hTotalPos
  rw [hLengthCount] at hCount
  simpa [total, f, n] using hCount

end Bananas
