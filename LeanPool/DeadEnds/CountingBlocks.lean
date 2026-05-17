/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/

import LeanPool.DeadEnds.CRT

/-!
Complete and partial residue blocks used to count finite prime-square conditions.
-/

namespace LeanPool.DeadEnds

/-- The `k`-th complete block of positive integers of length `M`. -/
def completeBlock (M k : ℕ) : Finset ℕ := Finset.Icc (k * M + 1) ((k + 1) * M)

lemma primeSquareProduct_pos (S : Finset Nat.Primes) : 0 < primeSquareProduct S := by
  have h₁ : ∀ p : Nat.Primes, 0 < (p : ℕ) ^ 2 := by
    intro p
    have h₂ : (p : ℕ) ≥ 2 := by
      exact Nat.Prime.two_le p.prop
    have h₄ : 0 < (p : ℕ) ^ 2 := by positivity
    exact h₄
  have h₂ : 0 < ∏ p ∈ S, (p : ℕ) ^ 2 := by
    apply Finset.prod_pos
    intro p _
    exact h₁ p
  exact h₂

lemma completeBlocks_subset_Icc (M X : ℕ) (hM : 0 < M) (k : ℕ) (hk : k < X / M) :
    completeBlock M k ⊆ Finset.Icc 1 X := by
  have h₁ : completeBlock M k = Finset.Icc (k * M + 1) ((k + 1) * M) := rfl
  rw [h₁]
  have h₂ : (k + 1) * M ≤ X := by
    have h₄ : (k + 1) * M ≤ X := by
      have h₅ : (X / M) * M ≤ X := by
        apply Nat.div_mul_le_self
      calc
        (k + 1) * M ≤ (X / M) * M := by
          nlinarith
        _ ≤ X := h₅
    exact h₄
  have h₃ : 1 ≤ k * M + 1 := by
    have h₄ : 0 ≤ k * M := by positivity
    omega
  have h₄ : (k + 1) * M ≤ X := h₂
  have h₆ : Finset.Icc (k * M + 1) ((k + 1) * M) ⊆ Finset.Icc 1 X := by
    apply Finset.Icc_subset_Icc
    · omega
    · omega
  exact h₆

lemma completeBlock_card (M k : ℕ) (hM : 0 < M) : (completeBlock M k).card = M := by
  have h₁ : (completeBlock M k) = Finset.Icc (k * M + 1) ((k + 1) * M) := rfl
  rw [h₁]
  have h₂ : (k * M + 1) ≤ ((k + 1) * M) := by
    have h₄ : (k * M + 1) ≤ ((k + 1) * M) := by
      ring_nf at *
      nlinarith
    exact h₄
  rw [Finset.card_eq_sum_ones]
  simp; ring_nf at *; simp_all

lemma completeBlock_mapsTo (M k : ℕ) (hM : 0 < M) :
    Set.MapsTo (· % M) (completeBlock M k : Set ℕ) (Finset.range M : Set ℕ) := by
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_range, completeBlock] at hx ⊢
  have h₄ : x % M < M := Nat.mod_lt x hM
  simp_all

/-- For any x, y in the complete block [kM+1, (k+1)M], we have |y - x| < M.

    This follows because:
    - The block has width (k+1)M - (kM+1) = M - 1
    - So the maximum absolute difference between any two elements is M - 1 < M
    In integers: max(y) - min(x) = (k+1)M - (kM+1) = M - 1
    and min(y) - max(x) = (kM+1) - (k+1)M = 1 - M
    So |y - x| ≤ M - 1 < M.
    Mathlib coverage: This uses `abs_sub_lt_iff` and basic interval arithmetic.
-/
lemma abs_sub_lt_of_mem_completeBlock (M k x y : ℕ) (_hM : 0 < M)
    (hx : x ∈ completeBlock M k) (hy : y ∈ completeBlock M k) :
    |(y : ℤ) - (x : ℤ)| < (M : ℤ) := by
  obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hx
  obtain ⟨hy1, hy2⟩ := Finset.mem_Icc.mp hy
  rw [show (k + 1) * M = k * M + M from by ring] at hx2 hy2
  rw [abs_sub_lt_iff]
  omega

/-- The function N ↦ N % M is injective on the complete block.
    Two numbers in [kM+1, (k+1)M] with the same residue mod M must be equal,
    since they are within distance M of each other.
    The proof uses the fact that if x, y are in [kM+1, (k+1)M], then |x - y| < M.
    If x % M = y % M and |x - y| < M, then x = y (since the only multiple of M
    in (-M, M) is 0). -/
lemma completeBlock_injOn (M k : ℕ) (hM : 0 < M) :
    Set.InjOn (· % M) (completeBlock M k : Set ℕ) := by
  intro x hx y hy hmod
  apply Nat.ModEq.eq_of_abs_lt
  · rw [Nat.ModEq.eq_1]
    exact hmod
  · exact abs_sub_lt_of_mem_completeBlock M k x y hM hx hy

lemma completeBlock_surjOn (M k : ℕ) (hM : 0 < M) :
    Set.SurjOn (· % M) (completeBlock M k : Set ℕ) (Finset.range M : Set ℕ) := by
  have h₁ : ∀ r ∈ (Finset.range M : Set ℕ), ∃ N ∈ (completeBlock M k : Set ℕ), N % M = r := by
    intro r hr
    have h₂ : r < M := Finset.mem_range.mp hr
    have h₃ : r ≤ M := by linarith
    by_cases h₄ : r = 0
    · have h₅ : ((k + 1) * M : ℕ) ∈ (completeBlock M k : Set ℕ) := by
        simp only [completeBlock, Finset.mem_coe, Finset.mem_Icc]
        constructor <;>
        (try norm_num);
        (try ring_nf);
        (try nlinarith)
      refine ⟨(k + 1) * M, h₅, ?_⟩
      have h₆ : ((k + 1) * M : ℕ) % M = 0 := by
        simp
      rw [h₄] at *
      omega
    · have h₅ : (k * M + r : ℕ) ∈ (completeBlock M k : Set ℕ) := by
        simp only [completeBlock, Finset.mem_coe, Finset.mem_Icc]
        constructor
        · have h₆ : 1 ≤ r := by
            by_contra h₆
            have h₇ : r = 0 := by
              omega
            contradiction
          nlinarith
        · nlinarith
      refine ⟨(k * M + r : ℕ), h₅, ?_⟩
      have h₆ : (k * M + r : ℕ) % M = r % M := by
        have h₇ : (k * M + r : ℕ) % M = r % M := by
          simp [Nat.add_mod]
        exact h₇
      have h₇ : r % M = r := by
        have h₈ : r < M := by
          exact h₂
        have h₉ : r % M = r := Nat.mod_eq_of_lt h₈
        exact h₉
      omega
  intro r hr
  have h₂ : r ∈ (Finset.range M : Set ℕ) := hr
  have h₃ : ∃ N ∈ (completeBlock M k : Set ℕ), N % M = r := h₁ r h₂
  obtain ⟨N, hN, hN'⟩ := h₃
  refine ⟨N, hN, ?_⟩; simp_all

/-- For N in the k-th complete block, N mod M takes each residue below M exactly once.
    This is because N ranges from kM+1 through (k+1)M, and:
    - (kM+j) mod M = j for 1 ≤ j < M
    - (k+1)M mod M = 0
    More precisely: the map N ↦ N % M is a bijection from B_k to `Finset.range M`. -/
lemma completeBlock_residues_bijective (M k : ℕ) (hM : 0 < M) :
    Set.BijOn (· % M) (completeBlock M k : Set ℕ) (Finset.range M : Set ℕ) := by
  exact Set.BijOn.mk (completeBlock_mapsTo M k hM) (completeBlock_injOn M k hM) (
      completeBlock_surjOn M k hM)

lemma filter_mapsTo (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (k : ℕ) :
    let M := primeSquareProduct S
    let P := fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
    Set.MapsTo (· % M) ((completeBlock M k).filter P : Set ℕ) ((Finset.range M).filter P : Set ℕ) :=
        by
  intro M P N hN
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hN ⊢
  obtain ⟨hNblock, hPN⟩ := hN
  constructor
  · have hM : 0 < M := primeSquareProduct_pos S
    exact (completeBlock_residues_bijective M k hM).mapsTo hNblock
  · have hM : 0 < M := primeSquareProduct_pos S
    have hmodlt : N % M < M := Nat.mod_lt N hM
    have hmod : N % M % M = N % M := Nat.mod_eq_of_lt hmodlt
    exact (condition_mod_invariant b T S N (N % M) hmod.symm).mp hPN

/-- Filtering a complete block preserves injectivity of the residue map. -/
lemma filter_injOn (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (k : ℕ) :
    let M := primeSquareProduct S
    let P := fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
    Set.InjOn (· % M) ((completeBlock M k).filter P : Set ℕ) := by
  intro M P
  have hM : 0 < M := primeSquareProduct_pos S
  have h_injOn := completeBlock_injOn M k hM
  have h_subset : ((completeBlock M k).filter P : Set ℕ) ⊆ (completeBlock M k : Set ℕ) :=
    Finset.filter_subset P (completeBlock M k)
  exact h_injOn.mono h_subset

/-- Filtering a complete block preserves surjectivity of the residue map onto valid residues. -/
lemma filter_surjOn (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (k : ℕ) :
    let M := primeSquareProduct S
    let P := fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
    Set.SurjOn (· % M) ((completeBlock M k).filter P : Set ℕ) ((Finset.range M).filter P : Set ℕ) :=
        by
  intro M P r hr
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hr
  obtain ⟨hr_range, hr_P⟩ := hr
  have hM : 0 < M := primeSquareProduct_pos S
  have hsurj := completeBlock_surjOn M k hM
  rw [Set.SurjOn] at hsurj
  have hr_range' : r ∈ (Finset.range M : Set ℕ) := hr_range
  obtain ⟨N, hN_block, hN_mod⟩ := hsurj hr_range'
  have hr_lt : r < M := Finset.mem_range.mp hr_range
  have hr_mod : r % M = r := Nat.mod_eq_of_lt hr_lt
  have hmod_eq : N % M = r % M := by simp only [hN_mod, hr_mod]
  have hP_equiv := condition_mod_invariant b T S N r hmod_eq
  have hN_P : P N := hP_equiv.mpr hr_P
  use N
  constructor
  · simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨hN_block, hN_P⟩
  · exact hN_mod

lemma filter_card_eq_of_bijOn_filter (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (k : ℕ) :
    let M := primeSquareProduct S
    let P := fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
    Set.BijOn (· % M)
      ((completeBlock M k).filter P : Set ℕ)
      ((Finset.range M).filter P : Set ℕ) := by
  intro M P
  exact ⟨filter_mapsTo b T S k, filter_injOn b T S k, filter_surjOn b T S k⟩

/-- Each complete block B_k contributes exactly |A| valid integers.

    Since the map N ↦ N % M is a bijection from B_k to `Finset.range M`, and by
    condition_mod_invariant validity depends only on N % M, the count of valid N in B_k
    equals the count of valid residues in `Finset.range M`, which is |A|.
    Uses: condition_mod_invariant, completeBlock_residues_bijective -/
lemma completeBlock_valid_count (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (k : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    ((completeBlock M k).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card = A.card := by
  intro M A
  have hbij := filter_card_eq_of_bijOn_filter b T S k
  exact Set.BijOn.finsetCard_eq _ hbij

lemma completeBlock_disjoint (M : ℕ) (_hM : 0 < M) (i j : ℕ) (hij : i < j) :
    Disjoint (completeBlock M i) (completeBlock M j) := by
  have h₁ : (i + 1) * M < j * M + 1 := by
    have h₃ : (i + 1) * M ≤ j * M := by
      nlinarith
    have h₄ : (i + 1) * M < j * M + 1 := by
      nlinarith
    exact h₄
  have h₂ : ((completeBlock M i) : Set ℕ) ∩ ((completeBlock M j) : Set ℕ) = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    simp only [Set.mem_inter_iff, completeBlock] at hx
    have h₃ : x ∈ (Finset.Icc (i * M + 1) ((i + 1) * M) : Finset ℕ) := hx.1
    have h₄ : x ∈ (Finset.Icc (j * M + 1) ((j + 1) * M) : Finset ℕ) := hx.2
    simp only [Finset.mem_Icc] at h₃ h₄
    linarith
  rw [Finset.disjoint_iff_inter_eq_empty]
  exact_mod_cast h₂

/-- The complete blocks indexed by `Finset.range q` are pairwise disjoint.
    Block B_i = [iM+1, (i+1)M] and B_j = [jM+1, (j+1)M] are disjoint for i ≠ j
    because their ranges don't overlap.
    Uses: For i < j, (i+1)M < jM+1 so the intervals are disjoint. -/
lemma completeBlocks_pairwise_disjoint (M : ℕ) (hM : 0 < M) :
    (Set.univ : Set ℕ).PairwiseDisjoint (fun k => (completeBlock M k : Set ℕ)) := by
  intro i _ j _ hij
  rcases hij.lt_or_gt with h | h
  · exact Finset.disjoint_coe.mpr (completeBlock_disjoint M hM i j h)
  · exact (Finset.disjoint_coe.mpr (completeBlock_disjoint M hM j i h)).symm

/-- The sum of valid elements from all complete blocks ≤ count.

    Since blocks are disjoint and contained in [1,X], the union of filtered blocks
    is a subset of the filtered [1,X], so the sum of cardinalities is at most count.
    Uses: completeBlocks_pairwise_disjoint, completeBlocks_subset_Icc, Finset.card_biUnion -/
lemma sum_valid_from_blocks_le_count (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    (Finset.range (X / M)).sum (fun k =>
        ((completeBlock M k).filter fun N =>
          ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card) ≤ count := by
  intro M count
  have hM : 0 < M := primeSquareProduct_pos S
  let P := fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
  have hdisj : (↑(Finset.range (X / M)) : Set ℕ).PairwiseDisjoint
      (fun k => (completeBlock M k).filter P) := by
    intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_iff_ne]
    intro x hxi y hyj
    have hblocks := completeBlocks_pairwise_disjoint M hM
    have hdisj_ij : Disjoint (completeBlock M i : Set ℕ) (completeBlock M j : Set ℕ) :=
      hblocks (Set.mem_univ i) (Set.mem_univ j) hij
    have hxi' : x ∈ completeBlock M i := Finset.mem_of_mem_filter x hxi
    have hyj' : y ∈ completeBlock M j := Finset.mem_of_mem_filter y hyj
    intro heq
    rw [heq] at hxi'
    rw [Set.disjoint_iff] at hdisj_ij
    exact hdisj_ij ⟨hxi', hyj'⟩
  have hsum : (Finset.range (X / M)).sum (fun k => ((completeBlock M k).filter P).card)
      = ((Finset.range (X / M)).biUnion (fun k => (completeBlock M k).filter P)).card := by
    rw [Finset.card_biUnion]
    · exact hdisj
  rw [hsum]
  have hsub : (Finset.range (X / M)).biUnion (fun k => (completeBlock M k).filter P)
      ⊆ (Finset.Icc 1 X).filter P := by
    rw [Finset.biUnion_subset]
    intro k hk
    apply Finset.filter_subset_filter
    exact completeBlocks_subset_Icc M X hM k (Finset.mem_range.mp hk)
  exact Finset.card_le_card hsub

lemma count_lower_bound (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    (X / M) * A.card ≤ count := by
  intro M A count
  have blocks_eq : (Finset.range (X / M)).sum (fun k =>
      ((completeBlock M k).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card) =
      (X / M) * A.card := by
    have h : ∀ k ∈ Finset.range (X / M),
        ((completeBlock M k).filter fun N =>
          ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card = A.card :=
      fun k _ => completeBlock_valid_count b T S k
    rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul]
  calc (X / M) * A.card = (Finset.range (X / M)).sum (fun k =>
        ((completeBlock M k).filter fun N =>
          ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card) := blocks_eq.symm
    _ ≤ count := sum_valid_from_blocks_le_count b T S X

/-- The partial block consists of the remaining integers from `q * M + 1` through `X`,
where `q = X / M`. -/
def partialBlock (M X : ℕ) : Finset ℕ := Finset.Icc (X / M * M + 1) X

lemma partialBlock_subset_Icc (M X : ℕ) (_hM : 0 < M) :
    partialBlock M X ⊆ Finset.Icc 1 X := by
  dsimp [partialBlock]
  apply Finset.Icc_subset_Icc
  <;>
  (try norm_num)

lemma partialBlock_subset_Ico (M X : ℕ) (hM : 0 < M) :
    (partialBlock M X : Set ℕ) ⊆ ↑(Finset.Ico (X / M * M) (X / M * M + M)) := by
  unfold partialBlock
  rw [Finset.coe_Icc, Finset.coe_Ico]
  intro n hn
  simp only [Set.mem_Icc] at hn
  simp only [Set.mem_Ico]
  constructor
  · omega
  · calc n ≤ X := hn.2
      _ < X / M * M + M := Nat.lt_div_mul_add hM

/-- The residue map N ↦ N % M is injective on the partial block from `q * M + 1` through `X`.
    This is because for any N in the partial block, N = q*M + k where 1 ≤ k ≤ r < M
    (where r = X % M), so N % M = k. Different elements have different k values.
    The key insight is that all elements lie within a single period of M:
    they are all in [q*M+1, q*M+r] where r < M.
    Uses: `Set.InjOn : ∀ {α : Type u_1} {β : Type u_2}, (α → β) → Set α → Prop`
    which states f is injective on s iff ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y. -/
lemma partialBlock_injOn_mod (M X : ℕ) :
    Set.InjOn (fun x => x % M) ↑(partialBlock M X) := by
  rcases eq_or_lt_of_le (Nat.zero_le M) with rfl | hM
  · intro x _ y _ hxy
    simp only [Nat.mod_zero] at hxy
    exact hxy
  · exact (Nat.mod_injOn_Ico (X / M * M) M).mono (partialBlock_subset_Ico M X hM)

lemma partialBlock_valid_mapsTo (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    let validBlock := (partialBlock M X).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
    Set.MapsTo (fun x => x % M) ↑validBlock ↑A := by
  intro M A validBlock N hN
  rw [Finset.mem_coe] at hN ⊢
  rw [Finset.mem_filter] at hN
  obtain ⟨_, hvalid⟩ := hN
  simp only at *
  change N % M ∈ validResiduesMod b T S
  rw [validResiduesMod, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact Nat.mod_lt N (primeSquareProduct_pos S)
  · have hmodEq : (N % M) ≡ N [MOD M] := Nat.mod_modEq N M
    have hmod : N % M = (N % M) % M := (Nat.ModEq.eq_1 M (N % M) N ▸ hmodEq).symm
    rw [← condition_mod_invariant b T S N (N % M) hmod]
    exact hvalid

lemma partialBlock_valid_count_le (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    ((partialBlock M X).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card ≤ A.card := by
  intro M A
  let validBlock := (partialBlock M X).filter fun N =>
    ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
  apply Finset.card_le_card_of_injOn (fun x => x % M)
  · exact partialBlock_valid_mapsTo b T S X
  · intro x hx y hy hxy
    have hx' : x ∈ partialBlock M X := Finset.mem_filter.mp hx |>.1
    have hy' : y ∈ partialBlock M X := Finset.mem_filter.mp hy |>.1
    exact partialBlock_injOn_mod M X hx' hy' hxy

lemma completeBlock_disjoint_partialBlock (M X : ℕ) (_hM : 0 < M) (k : ℕ) (hk : k < X / M) :
    Disjoint (completeBlock M k) (partialBlock M X) := by
  have h₁ : (completeBlock M k) ∩ (partialBlock M X) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro n hn
    simp only [completeBlock, partialBlock, Finset.mem_inter, Finset.mem_Icc] at hn
    have h₈ : (k + 1) * M ≤ (X / M) * M := by
      have h₁₁ : (k + 1) * M ≤ (X / M) * M := by
        nlinarith
      exact h₁₁
    have h₁₁ : n ≤ (X / M) * M := by
      linarith
    omega
  exact Finset.disjoint_iff_inter_eq_empty.mpr h₁

lemma biUnion_completeBlocks_disjoint_partialBlock (M X : ℕ) (_hM : 0 < M) :
    Disjoint ((Finset.range (X / M)).biUnion (completeBlock M)) (partialBlock M X) := by
  have h_main : Disjoint ((Finset.range (X / M)).biUnion (completeBlock M)) (partialBlock M X) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have h₁ : ∃ k, k ∈ Finset.range (X / M) ∧ x ∈ completeBlock M k := by
      simpa [Finset.mem_biUnion] using hx₁
    obtain ⟨k, hk₁, hk₂⟩ := h₁
    have h₂ : x ∉ partialBlock M X := by
      have h₃ : k < X / M := Finset.mem_range.mp hk₁
      have h₄ : x ∈ completeBlock M k := hk₂
      have h₅ : x ∈ Finset.Icc (k * M + 1) ((k + 1) * M) := by
        simpa [completeBlock] using h₄
      have h₇ : x ≤ (k + 1) * M := Finset.mem_Icc.mp h₅ |>.2
      have h₈ : x ∉ partialBlock M X := by
        intro h₉
        have h₁₀ : x ∈ Finset.Icc (X / M * M + 1) X := by
          simpa [partialBlock] using h₉
        have h₁₁ : (X / M * M + 1 : ℕ) ≤ x := Finset.mem_Icc.mp h₁₀ |>.1
        have h₁₄ : (k + 1 : ℕ) ≤ X / M := by
          omega
        have h₁₅ : (k + 1) * M ≤ X / M * M := by
          have h₁₆ : (k + 1 : ℕ) ≤ X / M := h₁₄
          have h₁₇ : (k + 1 : ℕ) * M ≤ (X / M) * M := by
            exact Nat.mul_le_mul_right M h₁₆
          exact h₁₇
        have h₁₈ : (X / M * M + 1 : ℕ) ≤ (k + 1) * M := by
          omega
        omega
      exact h₈
    exact h₂ hx₂
  exact h_main

lemma mem_completeBlock_of_div_lt (M X n : ℕ) (hM : 0 < M) (hn_pos : 1 ≤ n) (hn_le : n ≤ X)
    (hk : (n - 1) / M < X / M) : n ∈ completeBlock M ((n - 1) / M) := by
  have h₁ : n - 1 < (n - 1) / M * M + M := by
    have h₂ : (n - 1) % M < M := Nat.mod_lt (n - 1) hM
    have h₃ : (n - 1) = (n - 1) / M * M + (n - 1) % M := by
      have h₄ := Nat.div_add_mod (n - 1) M
      linarith
    linarith
  have h₂ : (n - 1) / M * M + 1 ≤ n := by
    have h₃ : n - 1 ≥ (n - 1) / M * M := by
      have h₄ : (n - 1) / M * M ≤ n - 1 := by
        have h₅ : (n - 1) / M * M ≤ n - 1 := by
          have h₆ := Nat.div_mul_le_self (n - 1) M
          linarith
        exact h₅
      omega
    have h₄ : (n - 1) / M * M + 1 ≤ n := by
      have h₅ : n ≥ 1 := by omega
      have h₆ : (n - 1) / M * M + 1 ≤ n := by
        cases n with
        | zero => omega
        | succ n =>
          cases n with
          | zero => omega
          | succ n =>
            simp at h₃ ⊢; ring_nf at h₃ ⊢; omega
      exact h₆
    exact h₄
  have h₃ : n ≤ ((n - 1) / M + 1) * M := by
    have h₄ : n ≤ ((n - 1) / M + 1) * M := by
      by_cases h₅ : M = 0
      · exfalso
        linarith
      · have h₇ : (n - 1) < ((n - 1) / M + 1) * M := by
          have h₈ : (n - 1) < ((n - 1) / M + 1) * M := by
            linarith
          exact h₈
        have h₈ : n ≤ ((n - 1) / M + 1) * M := by
          have h₁₀ : n ≤ ((n - 1) / M + 1) * M := by
            by_cases h₁₁ : n - 1 + 1 ≤ ((n - 1) / M + 1) * M
            · have h₁₂ : n = n - 1 + 1 := by
                omega
              omega
            · omega
          exact h₁₀
        exact h₈
    exact h₄
  have h₄ : n ∈ Finset.Icc ((n - 1) / M * M + 1) (((n - 1) / M + 1) * M) := by
    rw [Finset.mem_Icc]
    constructor <;>
    (try omega)
  simp only [completeBlock] at *
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add, Nat.add_mul] using h₄

lemma mem_partialBlock_of_div_eq (M X n : ℕ) (_hM : 0 < M) (hn_pos : 1 ≤ n) (hn_le : n ≤ X)
    (hk : (n - 1) / M = X / M) : n ∈ partialBlock M X := by
  have h₁ : X / M * M + 1 ≤ n := by
    have h₂ : (n - 1) / M = X / M := hk
    have h₃ : (n - 1) / M * M ≤ n - 1 := by
      have h₄ : (n - 1) / M * M ≤ n - 1 := by
        have h₅ : (n - 1) / M * M ≤ n - 1 := by
          apply Nat.div_mul_le_self
        exact h₅
      exact h₄
    have h₄ : X / M * M ≤ n - 1 := by
      calc
        X / M * M = (n - 1) / M * M := by rw [h₂]
        _ ≤ n - 1 := h₃
    have h₅ : X / M * M + 1 ≤ n := by
      have h₈ : X / M * M + 1 ≤ n := by
        have h₁₀ : n - 1 + 1 = n := by
          have h₁₂ : n - 1 + 1 = n := by
            omega
          exact h₁₂
        omega
      exact h₈
    exact h₅
  have h₂ : n ≤ X := hn_le
  have h₃ : n ∈ Finset.Icc (X / M * M + 1) X := by
    apply Finset.mem_Icc.mpr
    constructor
    · exact h₁
    · exact h₂
  have h₄ : partialBlock M X = Finset.Icc (X / M * M + 1) X := rfl
  rw [h₄] at *
  exact h₃

lemma div_sub_one_le_div (M X n : ℕ) (hn_pos : 1 ≤ n) (hn_le : n ≤ X) :
    (n - 1) / M ≤ X / M := by
  have h : n - 1 ≤ X := by
    omega
  have h₁ : (n - 1) / M ≤ X / M := by
    apply Nat.div_le_div_right; omega
  exact h₁

/-- The interval [1,X] equals the disjoint union of complete blocks indexed by `Finset.range q` and
    the partial block V from `qM + 1` through `X`.
    Every n ∈ [1,X] falls into exactly one of:
    - Complete block B_k where k = (n-1)/M for k < q
    - Partial block V if (n-1)/M ≥ q
    Conversely, all elements in the blocks are in [1,X] by completeBlocks_subset_Icc
    and partialBlock_subset_Icc.
    Uses the division algorithm: n = (n-1)/M * M + (n-1)%M + 1. -/
theorem Icc_eq_biUnion_union_partialBlock (M X : ℕ) (hM : 0 < M) :
    Finset.Icc 1 X = ((Finset.range (X / M)).biUnion (completeBlock M)) ∪ partialBlock M X := by
  ext n
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_range]
  constructor
  · intro ⟨hn_pos, hn_le⟩
    have hk_le : (n - 1) / M ≤ X / M := div_sub_one_le_div M X n hn_pos hn_le
    rcases Nat.lt_or_eq_of_le hk_le with hk_lt | hk_eq
    · left
      exact ⟨(n - 1) / M, hk_lt, mem_completeBlock_of_div_lt M X n hM hn_pos hn_le hk_lt⟩
    · right
      exact mem_partialBlock_of_div_eq M X n hM hn_pos hn_le hk_eq
  · intro h
    rcases h with ⟨k, hk, hn_block⟩ | hn_partial
    · exact Finset.mem_Icc.mp (completeBlocks_subset_Icc M X hM k hk hn_block)
    · exact Finset.mem_Icc.mp (partialBlock_subset_Icc M X hM hn_partial)

lemma filtered_biUnion_disjoint_filtered_partialBlock (M X : ℕ) (_hM : 0 < M)
    (P : ℕ → Prop) [DecidablePred P] :
    Disjoint (((Finset.range (X / M)).biUnion (completeBlock M)).filter P)
             ((partialBlock M X).filter P) := by
  have h_disjoint_unfiltered : Disjoint ((Finset.range (X / M)).biUnion (completeBlock M)) (
      partialBlock M X) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [Finset.mem_biUnion, Finset.mem_range, completeBlock, partialBlock,
        Finset.mem_Icc] at hx₁ hx₂
    obtain ⟨k, hk₁, hk₂⟩ := hx₁
    have h₈ : (k + 1) * M ≤ (X / M) * M := by
      have h₈₂ : (k + 1) * M ≤ (X / M) * M := by
        nlinarith
      exact h₈₂
    have h₉ : x ≤ (X / M) * M := by
      nlinarith
    omega
  have h_main : Disjoint (((Finset.range (X / M)).biUnion (completeBlock M)).filter P) (
      (partialBlock M X).filter P) := by
    apply Finset.disjoint_filter_filter h_disjoint_unfiltered
  exact h_main

/-- Filtering preserves pairwise disjointness of Finsets: if the original Finsets are
    pairwise disjoint, then their filtered versions are too.
    Mathlib has `Finset.pairwiseDisjoint_filter : ∀ {α β : Type*} {s : Finset α} {f : α → Finset β},
      (↑s).PairwiseDisjoint f → ∀ (p : β → Prop), (↑s).PairwiseDisjoint (fun a => Finset.filter p (f
      a))`
    but this only works for Finsets `s`, not arbitrary sets.
    This follows from `Set.PairwiseDisjoint.mono :
      ∀ {s : Set ι} {f g : ι → α}, s.PairwiseDisjoint f → g ≤ f → s.PairwiseDisjoint g`
    combined with `Finset.filter_subset : ∀ (p : α → Prop) [DecidablePred p] (s : Finset α),
      Finset.filter p s ⊆ s` to show that filtering decreases each set.
    Since `(f k).filter P ⊆ f k` for all k, and disjointness is preserved under taking subsets,
    the filtered family inherits pairwise disjointness from the original family. -/
lemma pairwiseDisjoint_filter_of_pairwiseDisjoint {ι : Type*} (s : Set ι)
    (f : ι → Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hpwd : s.PairwiseDisjoint f) :
    s.PairwiseDisjoint (fun k => (f k).filter P) := by
  intro i hi j hj hij
  exact Disjoint.mono (Finset.filter_subset P (f i)) (Finset.filter_subset P (f j)) (hpwd hi hj hij)

lemma filtered_completeBlocks_pairwiseDisjoint (M : ℕ) (hM : 0 < M)
    (P : ℕ → Prop) [DecidablePred P] (s : Finset ℕ) :
    (↑s : Set ℕ).PairwiseDisjoint (fun k => (completeBlock M k).filter P) := by
  apply pairwiseDisjoint_filter_of_pairwiseDisjoint _ _ P
  have h := completeBlocks_pairwise_disjoint M hM
  rw [Finset.pairwiseDisjoint_coe] at h
  exact Set.PairwiseDisjoint.subset h (Set.subset_univ _)

lemma count_eq_sum_blocks (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    let blockCounts := ∑ k ∈ Finset.range (X / M), ((completeBlock M k).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    let partialCount := ((partialBlock M X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    count = blockCounts + partialCount := by
  intro M count blockCounts partialCount
  set P := fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d) with hP
  have hM : 0 < M := primeSquareProduct_pos S
  have h_partition := Icc_eq_biUnion_union_partialBlock M X hM
  calc count
      = ((Finset.Icc 1 X).filter P).card := rfl
    _ = ((((Finset.range (X / M)).biUnion (completeBlock M)) ∪ partialBlock M X).filter P).card :=
        by
        rw [h_partition]
    _ = (((Finset.range (X / M)).biUnion (completeBlock M)).filter P ∪
         (partialBlock M X).filter P).card := by
        rw [Finset.filter_union]
    _ = (((Finset.range (X / M)).biUnion (completeBlock M)).filter P).card +
        ((partialBlock M X).filter P).card := by
        apply Finset.card_union_of_disjoint
        exact filtered_biUnion_disjoint_filtered_partialBlock M X hM P
    _ = ((Finset.range (X / M)).biUnion (fun k => (completeBlock M k).filter P)).card +
        partialCount := by
        rw [Finset.filter_biUnion]
    _ = (∑ k ∈ Finset.range (X / M), ((completeBlock M k).filter P).card) + partialCount := by
        congr 1
        apply Finset.card_biUnion
        exact filtered_completeBlocks_pairwiseDisjoint M hM P (Finset.range (X / M))
    _ = blockCounts + partialCount := rfl

end LeanPool.DeadEnds
