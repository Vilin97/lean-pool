/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.ColourWord

/-!
# Word sign depends only on the word's permutation

We show that `wordSign w c` depends on `w` only through `wordPerm w`,
by identifying it as `(-1) ^ oddInversions (wordPerm w) c`, where
`oddInversions σ c` counts inversions of `σ` at odd-coloured positions.
-/

namespace RS

open Finset

variable {k ℓ : ℕ}

/-- Count of inversions of `σ` restricted to odd-coloured positions:
pairs `(a, b)` with `a < b`, `σ a > σ b`, and both `c (σ a)` and
`c (σ b)` odd-coloured. -/
def oddInversions {k ℓ n : ℕ} (σ : _root_.Equiv.Perm (Fin n))
    (c : MixedColouring k ℓ n) : ℕ :=
  (univ.filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ σ p.1 > σ p.2 ∧
    (c (σ p.1)).isRight ∧ (c (σ p.2)).isRight)).card

private theorem oddInversions_one {n : ℕ}
    (c : MixedColouring k ℓ n) :
    oddInversions (1 : _root_.Equiv.Perm (Fin n)) c = 0 := by
  simp only [oddInversions, _root_.Equiv.Perm.one_apply, gt_iff_lt,
    Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Finset.mem_univ, forall_true_left]
  intro ⟨_, _⟩
  rintro ⟨hlt, hgt, _⟩
  exact absurd (lt_trans hlt hgt) (lt_irrefl _)

private theorem swap_adj_gt_iff {m : ℕ} {a b : Fin m}
    (hadj : b.val = a.val + 1) {x y : Fin m}
    (hne : ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) :
    (_root_.Equiv.swap a b x > _root_.Equiv.swap a b y) ↔
      (x > y) := by
  simp only [gt_iff_lt, _root_.Equiv.swap_apply_def, Fin.lt_def]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

/-- In the ¬both-odd case the two inversion filter sets are equal:
the critical pair fails the `isRight` check, and non-critical pairs
have their ordering preserved by the adjacent swap. -/
private theorem filter_eq_of_not_bothOdd {n : ℕ}
    {a b : Fin (n + 1)} (hadj : b.val = a.val + 1)
    (τ : _root_.Equiv.Perm (Fin (n + 1)))
    (c : MixedColouring k ℓ (n + 1))
    (hno : ¬ ((c a).isRight ∧ (c b).isRight)) :
    (univ.filter (fun p : Fin (n+1) × Fin (n+1) =>
      p.1 < p.2 ∧ _root_.Equiv.swap a b (τ p.1) > _root_.Equiv.swap a b (τ p.2)
        ∧
      (c (_root_.Equiv.swap a b (τ p.1))).isRight ∧
      (c (_root_.Equiv.swap a b (τ p.2))).isRight)) =
    (univ.filter (fun p : Fin (n+1) × Fin (n+1) =>
      p.1 < p.2 ∧ τ p.1 > τ p.2 ∧
      (c (_root_.Equiv.swap a b (τ p.1))).isRight ∧
      (c (_root_.Equiv.swap a b (τ p.2))).isRight)) := by
  ext ⟨p₁, p₂⟩
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hlt, hord, hr1, hr2⟩
    refine ⟨hlt, ?_, hr1, hr2⟩
    by_cases hcrit : (τ p₁ = a ∧ τ p₂ = b) ∨ (τ p₁ = b ∧ τ p₂ = a)
    · rcases hcrit with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · rw [ha, _root_.Equiv.swap_apply_left] at hr1
        rw [hb, _root_.Equiv.swap_apply_right] at hr2
        exact absurd ⟨hr2, hr1⟩ hno
      · rw [hb, _root_.Equiv.swap_apply_right] at hr1
        rw [ha, _root_.Equiv.swap_apply_left] at hr2
        exact absurd ⟨hr1, hr2⟩ hno
    · exact (swap_adj_gt_iff hadj hcrit).mp hord
  · rintro ⟨hlt, hord, hr1, hr2⟩
    refine ⟨hlt, ?_, hr1, hr2⟩
    by_cases hcrit : (τ p₁ = a ∧ τ p₂ = b) ∨ (τ p₁ = b ∧ τ p₂ = a)
    · rcases hcrit with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · rw [ha, _root_.Equiv.swap_apply_left] at hr1
        rw [hb, _root_.Equiv.swap_apply_right] at hr2
        exact absurd ⟨hr2, hr1⟩ hno
      · rw [hb, _root_.Equiv.swap_apply_right] at hr1
        rw [ha, _root_.Equiv.swap_apply_left] at hr2
        exact absurd ⟨hr1, hr2⟩ hno
    · exact (swap_adj_gt_iff hadj hcrit).mpr hord

/-- In the both-odd case with `τ⁻¹ a < τ⁻¹ b`, the swap-side
inversion set is the insert of the critical pair into the
plain-ordering set. -/
private theorem filter_insert_of_bothOdd_fwd {n : ℕ}
    {a b : Fin (n + 1)} (hadj : b.val = a.val + 1)
    (τ : _root_.Equiv.Perm (Fin (n + 1)))
    (c : MixedColouring k ℓ (n + 1))
    (hboth : (c a).isRight ∧ (c b).isRight)
    (hord : τ.symm a < τ.symm b) :
    (univ.filter (fun p : Fin (n+1) × Fin (n+1) =>
      p.1 < p.2 ∧ _root_.Equiv.swap a b (τ p.1) > _root_.Equiv.swap a b (τ p.2)
        ∧
      (c (_root_.Equiv.swap a b (τ p.1))).isRight ∧
      (c (_root_.Equiv.swap a b (τ p.2))).isRight)) =
    insert (τ.symm a, τ.symm b)
      (univ.filter (fun p : Fin (n+1) × Fin (n+1) =>
        p.1 < p.2 ∧ τ p.1 > τ p.2 ∧
        (c (_root_.Equiv.swap a b (τ p.1))).isRight ∧
        (c (_root_.Equiv.swap a b (τ p.2))).isRight)) := by
  ext ⟨p₁, p₂⟩
  simp only [mem_filter, mem_univ, true_and, mem_insert, Prod.mk.injEq]
  constructor
  · rintro ⟨hlt, hord_s, hr1, hr2⟩
    by_cases hcrit : (τ p₁ = a ∧ τ p₂ = b) ∨ (τ p₁ = b ∧ τ p₂ = a)
    · rcases hcrit with ⟨ha, hb⟩ | ⟨hb', ha'⟩
      · left
        exact ⟨by rw [← ha]; simp [_root_.Equiv.symm_apply_apply],
               by rw [← hb]; simp [_root_.Equiv.symm_apply_apply]⟩
      · rw [hb', ha'] at hord_s
        simp only [_root_.Equiv.swap_apply_right,
          _root_.Equiv.swap_apply_left] at hord_s
        exact absurd hord_s (by
          simp only [gt_iff_lt, not_lt, Fin.le_def]; omega)
    · right
      exact ⟨hlt, (swap_adj_gt_iff hadj hcrit).mp hord_s, hr1, hr2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hlt, hord_t, hr1, hr2⟩)
    · refine ⟨hord, ?_, ?_, ?_⟩
      · simp only [_root_.Equiv.apply_symm_apply,
          _root_.Equiv.swap_apply_left,
          _root_.Equiv.swap_apply_right, gt_iff_lt, Fin.lt_def]
        omega
      · simp only [_root_.Equiv.apply_symm_apply,
          _root_.Equiv.swap_apply_left]
        exact hboth.2
      · simp only [_root_.Equiv.apply_symm_apply,
          _root_.Equiv.swap_apply_right]
        exact hboth.1
    · refine ⟨hlt, ?_, hr1, hr2⟩
      by_cases hcrit : (τ p₁ = a ∧ τ p₂ = b) ∨ (τ p₁ = b ∧ τ p₂ = a)
      · rcases hcrit with ⟨ha, hb⟩ | ⟨hb', ha'⟩
        · rw [ha, hb] at hord_t
          exact absurd hord_t (by
            simp only [gt_iff_lt, not_lt, Fin.le_def]; omega)
        · have h1 : p₁ = τ.symm b := by
            rw [← hb']; simp [_root_.Equiv.symm_apply_apply]
          have h2 : p₂ = τ.symm a := by
            rw [← ha']; simp [_root_.Equiv.symm_apply_apply]
          rw [h1, h2] at hlt
          exact absurd hlt (not_lt.mpr (le_of_lt hord))
      · exact (swap_adj_gt_iff hadj hcrit).mpr hord_t

/-- In the both-odd case with `τ⁻¹ b < τ⁻¹ a`, the
plain-ordering inversion set is the insert of the critical pair
into the swap-side set. -/
private theorem filter_insert_of_bothOdd_rev {n : ℕ}
    {a b : Fin (n + 1)} (hadj : b.val = a.val + 1)
    (τ : _root_.Equiv.Perm (Fin (n + 1)))
    (c : MixedColouring k ℓ (n + 1))
    (hboth : (c a).isRight ∧ (c b).isRight)
    (hord : τ.symm b < τ.symm a) :
    (univ.filter (fun p : Fin (n+1) × Fin (n+1) =>
      p.1 < p.2 ∧ τ p.1 > τ p.2 ∧
      (c (_root_.Equiv.swap a b (τ p.1))).isRight ∧
      (c (_root_.Equiv.swap a b (τ p.2))).isRight)) =
    insert (τ.symm b, τ.symm a)
      (univ.filter (fun p : Fin (n+1) × Fin (n+1) =>
        p.1 < p.2 ∧ _root_.Equiv.swap a b (τ p.1) > _root_.Equiv.swap a b (τ
          p.2) ∧
        (c (_root_.Equiv.swap a b (τ p.1))).isRight ∧
        (c (_root_.Equiv.swap a b (τ p.2))).isRight)) := by
  ext ⟨p₁, p₂⟩
  simp only [mem_filter, mem_univ, true_and, mem_insert, Prod.mk.injEq]
  constructor
  · rintro ⟨hlt, hord_t, hr1, hr2⟩
    by_cases hcrit : (τ p₁ = a ∧ τ p₂ = b) ∨ (τ p₁ = b ∧ τ p₂ = a)
    · rcases hcrit with ⟨ha, hb⟩ | ⟨hb', ha'⟩
      · have h1 : p₁ = τ.symm a := by
          rw [← ha]; simp [_root_.Equiv.symm_apply_apply]
        have h2 : p₂ = τ.symm b := by
          rw [← hb]; simp [_root_.Equiv.symm_apply_apply]
        rw [h1, h2] at hlt
        exact absurd hlt (not_lt.mpr (le_of_lt hord))
      · left
        exact ⟨by rw [← hb']; simp [_root_.Equiv.symm_apply_apply],
               by rw [← ha']; simp [_root_.Equiv.symm_apply_apply]⟩
    · right
      exact ⟨hlt, (swap_adj_gt_iff hadj hcrit).mpr hord_t, hr1, hr2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hlt, hord_s, hr1, hr2⟩)
    · refine ⟨hord, ?_, ?_, ?_⟩
      · simp only [_root_.Equiv.apply_symm_apply, gt_iff_lt, Fin.lt_def]
        omega
      · simp only [_root_.Equiv.apply_symm_apply,
          _root_.Equiv.swap_apply_right]
        exact hboth.1
      · simp only [_root_.Equiv.apply_symm_apply,
          _root_.Equiv.swap_apply_left]
        exact hboth.2
    · refine ⟨hlt, ?_, hr1, hr2⟩
      by_cases hcrit : (τ p₁ = a ∧ τ p₂ = b) ∨ (τ p₁ = b ∧ τ p₂ = a)
      · rcases hcrit with ⟨ha, hb⟩ | ⟨hb', ha'⟩
        · have h1 : p₁ = τ.symm a := by
            rw [← ha]; simp [_root_.Equiv.symm_apply_apply]
          have h2 : p₂ = τ.symm b := by
            rw [← hb]; simp [_root_.Equiv.symm_apply_apply]
          rw [h1, h2] at hlt
          exact absurd hlt (not_lt.mpr (le_of_lt hord))
        · rw [hb', ha'] at hord_s
          simp only [_root_.Equiv.swap_apply_right,
            _root_.Equiv.swap_apply_left] at hord_s
          exact absurd hord_s (by
            simp only [gt_iff_lt, not_lt, Fin.le_def]; omega)
      · exact (swap_adj_gt_iff hadj hcrit).mp hord_s

/-- The adjacent-swap cocycle: the sign of a swap-composed
permutation absorbs the `adjSign` factor. -/
private theorem neg_one_pow_oddInversions_swap_mul {n : ℕ}
    (a b : Fin (n + 1)) (hadj : b.val = a.val + 1)
    (τ : _root_.Equiv.Perm (Fin (n + 1)))
    (c : MixedColouring k ℓ (n + 1)) :
    adjSign c a b *
      (-1 : ℂ) ^ oddInversions τ (c ∘ _root_.Equiv.swap a b) =
    (-1 : ℂ) ^ oddInversions (_root_.Equiv.swap a b * τ) c := by
  -- The key observation: oddInversions (swap * τ) c and oddInversions τ (c ∘
  --   swap)
  -- share the same isRight conditions but differ in the ordering condition.
  -- We rewrite oddInversions (swap * τ) c to expose swap ∘ τ.
  have hS₁_eq : oddInversions (_root_.Equiv.swap a b * τ) c =
      (univ.filter (fun p : Fin (n+1) × Fin (n+1) =>
        p.1 < p.2 ∧
        _root_.Equiv.swap a b (τ p.1) > _root_.Equiv.swap a b (τ p.2) ∧
        (c (_root_.Equiv.swap a b (τ p.1))).isRight ∧
        (c (_root_.Equiv.swap a b (τ p.2))).isRight)).card := by
    unfold oddInversions; congr 1
  have hS₂_eq : oddInversions τ (c ∘ _root_.Equiv.swap a b) =
      (univ.filter (fun p : Fin (n+1) × Fin (n+1) =>
        p.1 < p.2 ∧ τ p.1 > τ p.2 ∧
        (c (_root_.Equiv.swap a b (τ p.1))).isRight ∧
        (c (_root_.Equiv.swap a b (τ p.2))).isRight)).card := by
    unfold oddInversions; congr 1
  rw [hS₁_eq, hS₂_eq]
  -- Now case-split on whether both positions are odd-coloured.
  by_cases hbo : (c a).isRight ∧ (c b).isRight
  · -- Both odd: the critical pair causes a difference of 1 in cardinality.
    have hab : a ≠ b := by intro h; rw [h] at hadj; omega
    have hlt_or_gt : τ.symm a < τ.symm b ∨ τ.symm b < τ.symm a := by
      rcases lt_or_gt_of_ne (show τ.symm a ≠ τ.symm b from
        fun h => hab (τ.symm.injective h)) with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hlt_or_gt with hfwd | hrev
    · -- τ⁻¹ a < τ⁻¹ b: S₁ = insert (τ⁻¹ a, τ⁻¹ b) S₂, so |S₁| = |S₂| + 1
      have hins := filter_insert_of_bothOdd_fwd hadj τ c hbo hfwd
      have hnotmem : (τ.symm a, τ.symm b) ∉
          univ.filter (fun p : Fin (n+1) × Fin (n+1) =>
            p.1 < p.2 ∧ τ p.1 > τ p.2 ∧
            (c (_root_.Equiv.swap a b (τ p.1))).isRight ∧
            (c (_root_.Equiv.swap a b (τ p.2))).isRight) := by
        simp only [mem_filter, mem_univ, true_and, not_and,
          _root_.Equiv.apply_symm_apply]
        intro _hlt hgt
        exact absurd hgt (by
          simp only [gt_iff_lt, not_lt, Fin.le_def]; omega)
      rw [hins, Finset.card_insert_of_notMem hnotmem]
      show adjSign c a b * (-1 : ℂ) ^ _ = (-1 : ℂ) ^ (_ + 1)
      rw [adjSign, if_pos hbo, pow_succ]
      ring
    · -- τ⁻¹ b < τ⁻¹ a: S₂ = insert (τ⁻¹ b, τ⁻¹ a) S₁, so |S₂| = |S₁| + 1
      have hins := filter_insert_of_bothOdd_rev hadj τ c hbo hrev
      have hnotmem : (τ.symm b, τ.symm a) ∉
          univ.filter (fun p : Fin (n+1) × Fin (n+1) =>
            p.1 < p.2 ∧
            _root_.Equiv.swap a b (τ p.1) > _root_.Equiv.swap a b (τ p.2) ∧
            (c (_root_.Equiv.swap a b (τ p.1))).isRight ∧
            (c (_root_.Equiv.swap a b (τ p.2))).isRight) := by
        simp only [mem_filter, mem_univ, true_and, not_and,
          _root_.Equiv.apply_symm_apply,
          _root_.Equiv.swap_apply_right, _root_.Equiv.swap_apply_left]
        intro _hlt hgt
        exact absurd hgt (by
          simp only [gt_iff_lt, not_lt, Fin.le_def]; omega)
      rw [hins, Finset.card_insert_of_notMem hnotmem]
      show adjSign c a b * (-1 : ℂ) ^ (_ + 1) = (-1 : ℂ) ^ _
      rw [adjSign, if_pos hbo, pow_succ]
      ring
  · -- Not both odd: the two filter sets are equal.
    have heq := filter_eq_of_not_bothOdd hadj τ c hbo
    rw [heq]
    show adjSign c a b * (-1 : ℂ) ^ _ = (-1 : ℂ) ^ _
    rw [adjSign, if_neg hbo, one_mul]

/-- **The word sign is an inversion count**: it is `(−1)` to the
number of inversions of the word's permutation at odd positions. -/
theorem wordSign_eq_oddInversions {n : ℕ} (w : List (Fin n))
    (c : MixedColouring k ℓ (n + 1)) :
    wordSign w c =
      (-1 : ℂ) ^ oddInversions (wordPerm w) c := by
  induction w generalizing c with
  | nil =>
    simp only [wordSign, wordPerm, oddInversions_one, pow_zero]
  | cons i w ih =>
    show adjSign c ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ *
        wordSign w (c ∘ _root_.Equiv.swap
          (⟨i.val, by omega⟩ : Fin (n + 1))
          ⟨i.val + 1, by omega⟩) =
      (-1 : ℂ) ^ oddInversions
        (_root_.Equiv.swap (⟨i.val, by omega⟩ : Fin (n + 1))
          ⟨i.val + 1, by omega⟩ * wordPerm w) c
    rw [ih]
    exact neg_one_pow_oddInversions_swap_mul
      ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ rfl
      (wordPerm w) c

end RS
