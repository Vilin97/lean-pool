/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import LeanPool.BollobasNikiforov.TN.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Sort
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Instances.Matrix

/-!
# Truncated and unrestricted square kernels

This file records the elementary algebraic facts about the kernels
`(t - a)²` and `(t - a)₊²` used for total nonnegativity. The positive
part is `max · 0`.
-/

@[expose] public section

namespace BollobasNikiforov

open Matrix

variable {ι κ : Type*}

/-- The unrestricted square kernel `(i, j) ↦ (t j - a i)²`. -/
def unrestrictedSquare (a : ι → ℝ) (t : κ → ℝ) : Matrix ι κ ℝ :=
  fun i j => (t j - a i) ^ 2

/-- The truncated square kernel `(i, j) ↦ (t j - a i)₊²`. -/
def truncatedSquare (a : ι → ℝ) (t : κ → ℝ) : Matrix ι κ ℝ :=
  fun i j => (max (t j - a i) 0) ^ 2

@[simp] lemma unrestrictedSquare_apply (a : ι → ℝ) (t : κ → ℝ) (i : ι) (j : κ) :
    unrestrictedSquare a t i j = (t j - a i) ^ 2 :=
  rfl

@[simp] lemma truncatedSquare_apply (a : ι → ℝ) (t : κ → ℝ) (i : ι) (j : κ) :
    truncatedSquare a t i j = (max (t j - a i) 0) ^ 2 :=
  rfl

/-- Row factor with columns `(1, a, a²)`. -/
def unrestrictedSquareLeft (a : ι → ℝ) : Matrix ι (Fin 3) ℝ :=
  fun i => ![1, a i, a i ^ 2]

/-- Column factor with rows `(t², -2 t, 1)`. -/
def unrestrictedSquareRight (t : κ → ℝ) : Matrix (Fin 3) κ ℝ :=
  fun k j => ![t j ^ 2, -2 * t j, 1] k

/-- TN05. The identity `(t - a)² = t² + a² - 2 t a` as a three-term
rank-one expansion. -/
lemma unrestrictedSquare_eq_sum_vecMulVec (a : ι → ℝ) (t : κ → ℝ) :
    unrestrictedSquare a t =
      vecMulVec (fun i => a i ^ 2) (fun _ => (1 : ℝ)) +
      vecMulVec (fun _ => (1 : ℝ)) (fun j => t j ^ 2) +
      (-2 : ℝ) • vecMulVec a t := by
  ext i j
  simp [vecMulVec_apply]
  ring

/-- TN05. Factorization against `(1, a, a²)` and `(t², -2 t, 1)`. -/
lemma unrestrictedSquare_eq_mul (a : ι → ℝ) (t : κ → ℝ) :
    unrestrictedSquare a t = unrestrictedSquareLeft a * unrestrictedSquareRight t := by
  ext i j
  simp [unrestrictedSquareLeft, unrestrictedSquareRight, mul_apply, Fin.sum_univ_three,
    cons_val_zero, cons_val_one, cons_val_two, vecHead, vecTail]
  ring

/-- TN05. The unrestricted square matrix has rank at most three. -/
lemma unrestrictedSquare_rank_le [Fintype κ] (a : ι → ℝ) (t : κ → ℝ) :
    (unrestrictedSquare a t).rank ≤ 3 := by
  rw [unrestrictedSquare_eq_mul]
  refine (rank_mul_le_left (unrestrictedSquareLeft a) _).trans ?_
  exact (rank_le_card_width (unrestrictedSquareLeft a)).trans_eq (Fintype.card_fin 3)

lemma unrestrictedSquare_submatrix_eq_mul (a : ι → ℝ) (t : κ → ℝ)
    {r c : Type*} (I : r → ι) (J : c → κ) :
    (unrestrictedSquare a t).submatrix I J =
      (unrestrictedSquareLeft a).submatrix I id *
        (unrestrictedSquareRight t).submatrix id J := by
  rw [unrestrictedSquare_eq_mul]
  exact submatrix_mul _ _ I id J Function.bijective_id

/-- TN06. Every `r × r` minor of unrestricted squares with `r ≥ 4` vanishes. -/
lemma unrestrictedSquare_submatrix_det_eq_zero {r : ℕ} (hr : 4 ≤ r)
    (a : ι → ℝ) (t : κ → ℝ) (I : Fin r → ι) (J : Fin r → κ) :
    ((unrestrictedSquare a t).submatrix I J).det = 0 := by
  rw [unrestrictedSquare_submatrix_eq_mul]
  set P := (unrestrictedSquareLeft a).submatrix I (id : Fin 3 → Fin 3)
  set Q := (unrestrictedSquareRight t).submatrix (id : Fin 3 → Fin 3) J
  have hrank : (P * Q).rank ≤ 3 :=
    (rank_mul_le_left P Q).trans <|
      (rank_le_card_width P).trans_eq (Fintype.card_fin 3)
  by_contra hdet
  have hunit : IsUnit (P * Q) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hcard : (P * Q).rank = r := by
    simpa using rank_of_isUnit (P * Q) hunit
  omega

/-- Algebraic factorization of the 2×2 minor of unrestricted squares (TN07). -/
lemma unrestricted_sq_two_eq (a b t u : ℝ) :
    (t - a) ^ 2 * (u - b) ^ 2 - (u - a) ^ 2 * (t - b) ^ 2 =
      (t - u) * (a - b) * ((t - a) * (u - b) + (u - a) * (t - b)) := by
  ring

/-- TN07. In the unrestricted chamber `a ≤ b ≤ t ≤ u`, the 2×2 minor is
nonnegative. The remaining factor `(t-a)(u-b)+(u-a)(t-b)` is a sum of
nonnegative terms in this chamber. -/
lemma unrestricted_sq_two_nonneg {a b t u : ℝ}
    (hab : a ≤ b) (hbt : b ≤ t) (htu : t ≤ u) :
    0 ≤ (t - a) ^ 2 * (u - b) ^ 2 - (u - a) ^ 2 * (t - b) ^ 2 := by
  rw [unrestricted_sq_two_eq]
  have hfac : 0 ≤ (t - u) * (a - b) :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr htu) (sub_nonpos.mpr hab)
  have hrest : 0 ≤ (t - a) * (u - b) + (u - a) * (t - b) := by nlinarith
  nlinarith

lemma unrestrictedSquare_det_two {a t : Fin 2 → ℝ}
    (ha : a 0 ≤ a 1) (ht : t 0 ≤ t 1) (hbt : a 1 ≤ t 0) :
    0 ≤ (unrestrictedSquare a t).det := by
  rw [det_fin_two]
  simpa using unrestricted_sq_two_nonneg ha hbt ht

/-- Closed form for the 3×3 minor of unrestricted squares. -/
lemma unrestrictedSquare_det_fin_three (a t : Fin 3 → ℝ) :
    (unrestrictedSquare a t).det =
      2 * (a 1 - a 0) * (a 2 - a 1) * (a 2 - a 0) *
        (t 1 - t 0) * (t 2 - t 1) * (t 2 - t 0) := by
  simp [det_fin_three]
  ring

/-- TN08. The 3×3 minor of unrestricted squares is nonnegative on
nondecreasing arguments. -/
lemma unrestrictedSquare_det_fin_three_nonneg {a t : Fin 3 → ℝ}
    (ha : Monotone a) (ht : Monotone t) :
    0 ≤ (unrestrictedSquare a t).det := by
  rw [unrestrictedSquare_det_fin_three]
  have h01a : 0 ≤ a 1 - a 0 := sub_nonneg.mpr (ha (by decide : (0 : Fin 3) ≤ 1))
  have h12a : 0 ≤ a 2 - a 1 := sub_nonneg.mpr (ha (by decide : (1 : Fin 3) ≤ 2))
  have h02a : 0 ≤ a 2 - a 0 := sub_nonneg.mpr (ha (by decide : (0 : Fin 3) ≤ 2))
  have h01t : 0 ≤ t 1 - t 0 := sub_nonneg.mpr (ht (by decide : (0 : Fin 3) ≤ 1))
  have h12t : 0 ≤ t 2 - t 1 := sub_nonneg.mpr (ht (by decide : (1 : Fin 3) ≤ 2))
  have h02t : 0 ≤ t 2 - t 0 := sub_nonneg.mpr (ht (by decide : (0 : Fin 3) ≤ 2))
  positivity

/-- TN09. Two-by-two minor of truncated squares. -/
lemma truncated_sq_two_nonneg {a b t u : ℝ} (hab : a ≤ b) (htu : t ≤ u) :
    0 ≤ (max (t - a) 0) ^ 2 * (max (u - b) 0) ^ 2 -
      (max (u - a) 0) ^ 2 * (max (t - b) 0) ^ 2 := by
  rcases le_or_gt t a with hta | _hat
  · have htb : t ≤ b := hta.trans hab
    have hta0 : max (t - a) 0 = 0 := max_eq_right (sub_nonpos.mpr hta)
    have htb0 : max (t - b) 0 = 0 := max_eq_right (sub_nonpos.mpr htb)
    simp [hta0, htb0]
  · rcases le_or_gt t b with htb | hbt
    · rcases le_or_gt u b with hub | _hbu
      · have hub0 : max (u - b) 0 = 0 := max_eq_right (sub_nonpos.mpr hub)
        have htb0 : max (t - b) 0 = 0 := max_eq_right (sub_nonpos.mpr htb)
        simp [hub0, htb0]
      · have htb0 : max (t - b) 0 = 0 := max_eq_right (sub_nonpos.mpr htb)
        rw [htb0, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · have hta' : max (t - a) 0 = t - a :=
        max_eq_left (sub_nonneg.mpr (hab.trans hbt.le))
      have hub' : max (u - b) 0 = u - b :=
        max_eq_left (sub_nonneg.mpr (hbt.le.trans htu))
      have hua' : max (u - a) 0 = u - a :=
        max_eq_left (sub_nonneg.mpr (hab.trans (hbt.le.trans htu)))
      have htb' : max (t - b) 0 = t - b :=
        max_eq_left (sub_nonneg.mpr hbt.le)
      rw [hta', hub', hua', htb']
      exact unrestricted_sq_two_nonneg hab hbt.le htu

lemma truncatedSquare_det_two {a t : Fin 2 → ℝ} (ha : a 0 ≤ a 1) (ht : t 0 ≤ t 1) :
    0 ≤ (truncatedSquare a t).det := by
  rw [det_fin_two]
  simpa using truncated_sq_two_nonneg ha ht

/-- TN10. If `t 0 < a 0` and `a` is nondecreasing, every truncated entry in
column `0` vanishes. -/
lemma truncated_sq_col_zero {k : ℕ} [NeZero k] {a t : Fin k → ℝ}
    (ha : Monotone a) (h : t 0 < a 0) (i : Fin k) :
    max (t 0 - a i) 0 = 0 := by
  have hai : a 0 ≤ a i := ha (Fin.zero_le i)
  exact max_eq_right (sub_nonpos.mpr (le_of_lt (h.trans_le hai)))

lemma truncatedSquare_column_zero {k : ℕ} [NeZero k] {a t : Fin k → ℝ}
    (ha : Monotone a) (h : t 0 < a 0) (i : Fin k) :
    truncatedSquare a t i 0 = 0 := by
  rw [truncatedSquare_apply, truncated_sq_col_zero ha h, zero_pow (by decide : (2 : ℕ) ≠ 0)]

/-- TN10. Every square minor that includes column `0` vanishes. -/
lemma truncatedSquare_det_eq_zero_of_first_col {k r : ℕ} [NeZero k] [NeZero r]
    {a t : Fin k → ℝ} (ha : Monotone a) (h : t 0 < a 0)
    (I : Fin r → Fin k) (J : Fin r → Fin k) (hJ : J 0 = 0) :
    ((truncatedSquare a t).submatrix I J).det = 0 := by
  refine det_eq_zero_of_column_eq_zero 0 fun i => ?_
  rw [submatrix_apply, hJ, truncatedSquare_column_zero ha h]

lemma truncatedSquare_eq_zero_of_le {a t : ℝ} (h : t ≤ a) :
    (max (t - a) 0) ^ 2 = 0 := by
  rw [max_eq_right (sub_nonpos.mpr h), zero_pow (by decide : (2 : ℕ) ≠ 0)]

lemma truncatedSquare_eq_unrestricted_of_le {a t : ℝ} (h : a ≤ t) :
    (max (t - a) 0) ^ 2 = (t - a) ^ 2 := by
  rw [max_eq_left (sub_nonneg.mpr h)]

/-- The last index of a nonempty `Fin k`. -/
def finLast (k : ℕ) [NeZero k] : Fin k :=
  ⟨k - 1, Nat.sub_one_lt (NeZero.ne k)⟩

lemma le_finLast {k : ℕ} [NeZero k] (i : Fin k) : i ≤ finLast k := by
  exact Nat.le_pred_of_lt i.isLt

/-- TN11. In the unrestricted chamber every truncated entry is unrestricted. -/
lemma truncatedSquare_eq_unrestrictedSquare {k : ℕ} [NeZero k] {a t : Fin k → ℝ}
    (ha : Monotone a) (ht : Monotone t) (h : a (finLast k) ≤ t 0) :
    truncatedSquare a t = unrestrictedSquare a t := by
  ext i j
  refine truncatedSquare_eq_unrestricted_of_le ?_
  exact (ha (le_finLast i)).trans (h.trans (ht (Fin.zero_le j)))

lemma truncatedSquare_submatrix_eq {r c n m : ℕ}
    (a : Fin r → ℝ) (t : Fin c → ℝ) (I : Fin n → Fin r) (J : Fin m → Fin c) :
    (truncatedSquare a t).submatrix I J = truncatedSquare (a ∘ I) (t ∘ J) :=
  rfl

lemma unrestrictedSquare_submatrix_eq {r c n m : ℕ}
    (a : Fin r → ℝ) (t : Fin c → ℝ) (I : Fin n → Fin r) (J : Fin m → Fin c) :
    (unrestrictedSquare a t).submatrix I J = unrestrictedSquare (a ∘ I) (t ∘ J) :=
  rfl

lemma monotone_comp_of_monotone {α β γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
    {f : β → γ} {g : α → β} (hf : Monotone f) (hg : Monotone g) :
    Monotone (f ∘ g) :=
  hf.comp hg

lemma monotone_of_strictMono {α β : Type*} [LinearOrder α] [Preorder β]
    {f : α → β} (hf : StrictMono f) : Monotone f :=
  hf.monotone

/-- Size-one minors are squares of nonnegative numbers. -/
lemma truncatedSquare_det_one {a t : Fin 1 → ℝ} :
    0 ≤ (truncatedSquare a t).det := by
  rw [det_fin_one]
  exact sq_nonneg _

lemma unrestrictedSquare_det_one {a t : Fin 1 → ℝ} :
    0 ≤ (unrestrictedSquare a t).det := by
  rw [det_fin_one]
  exact sq_nonneg _

/-- Unrestricted dets in the chamber `a last ≤ t 0`. -/
lemma unrestrictedSquare_det_nonneg_chamber {n : ℕ} {a t : Fin n → ℝ}
    (ha : Monotone a) (ht : Monotone t)
    (hch : n = 0 ∨ ∃ _ : NeZero n, a (finLast n) ≤ t 0) :
    0 ≤ (unrestrictedSquare a t).det := by
  rcases n with _ | n
  · simp [det_eq_one_of_card_eq_zero (Fintype.card_fin 0)]
  have hlast : a (finLast (n + 1)) ≤ t 0 := by
    rcases hch with h | ⟨_, h⟩
    · cases h
    · exact h
  rcases n with _ | n
  · exact unrestrictedSquare_det_one
  rcases n with _ | n
  · exact unrestrictedSquare_det_two (ha (Fin.zero_le 1)) (ht (Fin.zero_le 1)) hlast
  rcases n with _ | n
  · exact unrestrictedSquare_det_fin_three_nonneg ha ht
  · exact (unrestrictedSquare_submatrix_det_eq_zero (by omega : 4 ≤ n + 4) a t id id).symm.le

/-- TN11. Increasing minors of a truncated matrix in the unrestricted chamber. -/
lemma truncatedSquare_unrestricted_chamber_minor_nonneg {k n : ℕ} [NeZero k]
    {a t : Fin k → ℝ} (ha : Monotone a) (ht : Monotone t)
    (h : a (finLast k) ≤ t 0) (I J : Fin n → Fin k)
    (hI : Monotone I) (hJ : Monotone J) :
    0 ≤ ((truncatedSquare a t).submatrix I J).det := by
  rw [truncatedSquare_eq_unrestrictedSquare ha ht h, unrestrictedSquare_submatrix_eq]
  refine unrestrictedSquare_det_nonneg_chamber (ha.comp hI) (ht.comp hJ) ?_
  rcases n with _ | n
  · exact Or.inl rfl
  · refine Or.inr ⟨inferInstance, ?_⟩
    have hIlast : I (finLast (n + 1)) ≤ finLast k := le_finLast _
    have hJ0 : (0 : Fin k) ≤ J 0 := Fin.zero_le _
    exact (ha hIlast).trans (h.trans (ht hJ0))

/-- TN12. A truncated entry vanishes on and below the diagonal of the staircase. -/
lemma truncatedSquare_block_zero {k : ℕ} {a t : Fin k → ℝ}
    (ha : Monotone a) (ht : Monotone t) {s j0 i j : Fin k}
    (hj0 : t j0 < a s) (hi : s ≤ i) (hj : j ≤ j0) :
    truncatedSquare a t i j = 0 := by
  have : t j ≤ a i :=
    (ht hj).trans (hj0.le.trans (ha hi))
  simpa [truncatedSquare_apply] using truncatedSquare_eq_zero_of_le this

lemma truncatedSquare_block_zero_of_le {k : ℕ} {a t : Fin k → ℝ}
    (ha : Monotone a) (ht : Monotone t) {s j0 i j : Fin k}
    (hj0 : t j0 ≤ a s) (hi : s ≤ i) (hj : j ≤ j0) :
    truncatedSquare a t i j = 0 := by
  have : t j ≤ a i := (ht hj).trans (hj0.trans (ha hi))
  simpa [truncatedSquare_apply] using truncatedSquare_eq_zero_of_le this

/-- Block-triangular determinant after splitting `Fin (m + n)` as `Fin m ⊕ Fin n`. -/
lemma det_block_triangular_add {m n : ℕ}
    (M : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)
    (hz : ∀ (i : Fin n) (j : Fin m), M (Fin.natAdd m i) (Fin.castAdd n j) = 0) :
    M.det =
      (M.submatrix (Fin.castAdd n) (Fin.castAdd n)).det *
        (M.submatrix (Fin.natAdd m) (Fin.natAdd m)).det := by
  let e : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  have hdet : (M.submatrix e e).det = M.det := det_submatrix_equiv_self e M
  let A : Matrix (Fin m) (Fin m) ℝ := M.submatrix (Fin.castAdd n) (Fin.castAdd n)
  let B : Matrix (Fin m) (Fin n) ℝ := M.submatrix (Fin.castAdd n) (Fin.natAdd m)
  let D : Matrix (Fin n) (Fin n) ℝ := M.submatrix (Fin.natAdd m) (Fin.natAdd m)
  have hM : M.submatrix e e = fromBlocks A B 0 D := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [A, e, submatrix_apply]
      | inr j => simp [B, e, submatrix_apply]
    | inr i =>
      cases j with
      | inl j => simp [e, submatrix_apply, hz]
      | inr j => simp [D, e, submatrix_apply]
  rw [← hdet, hM, det_fromBlocks_zero₂₁]

lemma truncatedSquare_det_eq_zero_of_le_first {n : ℕ} [NeZero n] {a t : Fin n → ℝ}
    (ha : Monotone a) (h : t 0 ≤ a 0) :
    (truncatedSquare a t).det = 0 := by
  refine det_eq_zero_of_column_eq_zero 0 fun i => ?_
  have : t 0 ≤ a i := h.trans (ha (Fin.zero_le i))
  simpa [truncatedSquare_apply] using truncatedSquare_eq_zero_of_le this

/-- Mixed 3×3 staircase `a 0 ≤ a 1 ≤ t 0 ≤ a 2 ≤ t 1 ≤ t 2`. -/
lemma truncatedSquare_det_three_mixed {a t : Fin 3 → ℝ}
    (h01a : a 0 ≤ a 1) (h1t : a 1 ≤ t 0) (ht0a2 : t 0 ≤ a 2)
    (ha2t1 : a 2 ≤ t 1) (ht01 : t 0 ≤ t 1) (ht12 : t 1 ≤ t 2) :
    0 ≤ (truncatedSquare a t).det := by
  let x := a 1 - a 0
  let u := t 0 - a 1
  let v := a 2 - t 0
  let r := t 1 - a 2
  let q := t 2 - t 1
  have hx : 0 ≤ x := sub_nonneg.mpr h01a
  have hu : 0 ≤ u := sub_nonneg.mpr h1t
  have hv : 0 ≤ v := sub_nonneg.mpr ht0a2
  have hr : 0 ≤ r := sub_nonneg.mpr ha2t1
  have hq : 0 ≤ q := sub_nonneg.mpr ht12
  have h00 : truncatedSquare a t 0 0 = (x + u) ^ 2 := by
    change (max (t 0 - a 0) 0) ^ 2 = (x + u) ^ 2
    rw [truncatedSquare_eq_unrestricted_of_le (h01a.trans h1t)]
    simp [x, u]
  have h01 : truncatedSquare a t 0 1 = (x + u + v + r) ^ 2 := by
    have : a 0 ≤ t 1 := h01a.trans (h1t.trans ht01)
    change (max (t 1 - a 0) 0) ^ 2 = (x + u + v + r) ^ 2
    rw [truncatedSquare_eq_unrestricted_of_le this]
    simp [x, u, v, r]
  have h02 : truncatedSquare a t 0 2 = (x + u + v + r + q) ^ 2 := by
    have : a 0 ≤ t 2 := h01a.trans (h1t.trans (ht01.trans ht12))
    change (max (t 2 - a 0) 0) ^ 2 = (x + u + v + r + q) ^ 2
    rw [truncatedSquare_eq_unrestricted_of_le this]
    simp [x, u, v, r, q]
  have h10 : truncatedSquare a t 1 0 = u ^ 2 := by
    change (max (t 0 - a 1) 0) ^ 2 = u ^ 2
    rw [truncatedSquare_eq_unrestricted_of_le h1t]
  have h11 : truncatedSquare a t 1 1 = (u + v + r) ^ 2 := by
    have : a 1 ≤ t 1 := h1t.trans ht01
    change (max (t 1 - a 1) 0) ^ 2 = (u + v + r) ^ 2
    rw [truncatedSquare_eq_unrestricted_of_le this]
    simp [u, v, r]
  have h12 : truncatedSquare a t 1 2 = (u + v + r + q) ^ 2 := by
    have : a 1 ≤ t 2 := h1t.trans (ht01.trans ht12)
    change (max (t 2 - a 1) 0) ^ 2 = (u + v + r + q) ^ 2
    rw [truncatedSquare_eq_unrestricted_of_le this]
    simp [u, v, r, q]
  have h20 : truncatedSquare a t 2 0 = 0 :=
    truncatedSquare_eq_zero_of_le ht0a2
  have h21 : truncatedSquare a t 2 1 = r ^ 2 := by
    change (max (t 1 - a 2) 0) ^ 2 = r ^ 2
    rw [truncatedSquare_eq_unrestricted_of_le ha2t1]
  have h22 : truncatedSquare a t 2 2 = (r + q) ^ 2 := by
    have : a 2 ≤ t 2 := ha2t1.trans ht12
    change (max (t 2 - a 2) 0) ^ 2 = (r + q) ^ 2
    rw [truncatedSquare_eq_unrestricted_of_le this]
    simp [r, q]
  have hpoly :
      (truncatedSquare a t).det =
        q * x * (2 * q * r * u ^ 2 + 4 * q * r * u * v + 2 * q * r * u * x + 2 * q * r * v * x +
          2 * q * u ^ 2 * v + 2 * q * u * v ^ 2 + 2 * q * u * v * x + q * v ^ 2 * x +
          2 * r ^ 2 * u ^ 2 + 4 * r ^ 2 * u * v + 2 * r ^ 2 * u * x + 2 * r ^ 2 * v * x +
          4 * r * u ^ 2 * v + 4 * r * u * v ^ 2 + 4 * r * u * v * x + 2 * r * v ^ 2 * x) := by
    rw [det_fin_three]
    simp only [h00, h01, h02, h10, h11, h12, h20, h21, h22]
    ring
  rw [hpoly]
  exact mul_nonneg (mul_nonneg hq hx) (by positivity)

lemma truncatedSquare_det_three {a t : Fin 3 → ℝ} (ha : Monotone a) (ht : Monotone t) :
    0 ≤ (truncatedSquare a t).det := by
  have h01a : a 0 ≤ a 1 := ha (by decide : (0 : Fin 3) ≤ 1)
  have h12a : a 1 ≤ a 2 := ha (by decide : (1 : Fin 3) ≤ 2)
  have h02a : a 0 ≤ a 2 := ha (by decide : (0 : Fin 3) ≤ 2)
  have h01t : t 0 ≤ t 1 := ht (by decide : (0 : Fin 3) ≤ 1)
  have h12t : t 1 ≤ t 2 := ht (by decide : (1 : Fin 3) ≤ 2)
  have h02t : t 0 ≤ t 2 := ht (by decide : (0 : Fin 3) ≤ 2)
  rcases le_or_gt (t 0) (a 0) with ht0 | h0t
  · exact (truncatedSquare_det_eq_zero_of_le_first ha ht0).symm.le
  rcases le_or_gt (a 2) (t 0) with ha2 | ht0a2
  · rw [truncatedSquare_eq_unrestrictedSquare ha ht ha2]
    exact unrestrictedSquare_det_fin_three_nonneg ha ht
  -- a 0 < t 0 < a 2, so s = 1 or s = 2
  rcases le_or_gt (a 1) (t 0) with h1t | ht01a
  · -- s = 2: a 0 ≤ a 1 ≤ t 0 < a 2
    rcases le_or_gt (t 1) (a 2) with ht1a2 | ha2t1
    · -- p ≥ 2: columns 0,1 vanish on the last row, and col 0,1 have support in 2 rows
      -- t 1 ≤ a 2, so j0 ≥ 1, p ≥ 2 = s. If t 1 < a 2 then p > 2 or p = 2 with extra zeros.
      have h20 : truncatedSquare a t 2 0 = 0 := by
        simpa [truncatedSquare] using truncatedSquare_eq_zero_of_le ht0a2.le
      have h21 : truncatedSquare a t 2 1 = 0 := by
        simpa [truncatedSquare] using truncatedSquare_eq_zero_of_le ht1a2
      -- last row is [0, 0, *]; if also t 2 ≤ a 2 the row is 0
      rcases le_or_gt (t 2) (a 2) with ht2a2 | ha2t2
      · exact (det_eq_zero_of_row_eq_zero (2 : Fin 3) (by
          intro j
          fin_cases j
          · exact h20
          · exact h21
          · simpa [truncatedSquare] using truncatedSquare_eq_zero_of_le ht2a2)).symm.le
      · -- last row [0, 0, *]; det = A22 * (A00 A11 - A01 A10)
        have hdet :
            (truncatedSquare a t).det =
              truncatedSquare a t 2 2 *
                (truncatedSquare a t 0 0 * truncatedSquare a t 1 1 -
                  truncatedSquare a t 0 1 * truncatedSquare a t 1 0) := by
          rw [det_fin_three]
          simp only [h20, h21, mul_zero, add_zero, sub_zero]
          ring
        rw [hdet]
        exact mul_nonneg (sq_nonneg _) (truncated_sq_two_nonneg h01a h01t)
    · exact truncatedSquare_det_three_mixed h01a h1t ht0a2.le ha2t1.le h01t h12t
  · -- s = 1: a 0 < t 0 < a 1 ≤ a 2, column 0 vanishes on rows 1,2
    have h10 : truncatedSquare a t 1 0 = 0 :=
      truncatedSquare_eq_zero_of_le ht01a.le
    have h20 : truncatedSquare a t 2 0 = 0 :=
      truncatedSquare_eq_zero_of_le (ht01a.le.trans h12a)
    have hdet :
        (truncatedSquare a t).det =
          truncatedSquare a t 0 0 *
            (truncatedSquare a t 1 1 * truncatedSquare a t 2 2 -
              truncatedSquare a t 1 2 * truncatedSquare a t 2 1) := by
      rw [det_fin_three]
      simp only [h10, h20, mul_zero, zero_mul, add_zero, sub_zero]
      ring
    rw [hdet]
    exact mul_nonneg (sq_nonneg _) (truncated_sq_two_nonneg h12a h12t)

/-! ### TN13: truncated squares are totally nonnegative -/

/-- Square truncated determinants of size at most three, plus the two vanishing
chambers of size at least four. -/
lemma truncatedSquare_det_nonneg_of_small_or_chamber {n : ℕ}
    {a t : Fin n → ℝ} (ha : Monotone a) (ht : Monotone t)
    (h : n ≤ 3 ∨ (∃ _ : NeZero n, t 0 ≤ a 0) ∨
      (∃ _ : NeZero n, a (finLast n) ≤ t 0)) :
    0 ≤ (truncatedSquare a t).det := by
  rcases h with hn | ⟨_, hcol⟩ | ⟨_, hch⟩
  · match n with
    | 0 => simp [det_eq_one_of_card_eq_zero (Fintype.card_fin 0)]
    | 1 => exact truncatedSquare_det_one
    | 2 => exact truncatedSquare_det_two (ha (Fin.zero_le 1)) (ht (Fin.zero_le 1))
    | 3 => exact truncatedSquare_det_three ha ht
    | n + 4 => omega
  · exact (truncatedSquare_det_eq_zero_of_le_first ha hcol).symm.le
  · rw [truncatedSquare_eq_unrestrictedSquare ha ht hch]
    rcases n with _ | n
    · simp [det_eq_one_of_card_eq_zero (Fintype.card_fin 0)]
    exact unrestrictedSquare_det_nonneg_chamber ha ht (Or.inr ⟨inferInstance, hch⟩)

/-- TN13 for increasing selections of length at most three, and for every
length in the first-column or unrestricted chambers. -/
lemma truncatedSquare_minor_nonneg_of_small_or_chamber {r c k : ℕ}
    {a : Fin r → ℝ} {t : Fin c → ℝ} (ha : Monotone a) (ht : Monotone t)
    (I : Fin k → Fin r) (J : Fin k → Fin c)
    (hI : Monotone I) (hJ : Monotone J)
    (h : k ≤ 3 ∨ (∃ _ : NeZero k, t (J 0) ≤ a (I 0)) ∨
      (∃ _ : NeZero k, a (I (finLast k)) ≤ t (J 0))) :
    0 ≤ ((truncatedSquare a t).submatrix I J).det := by
  rw [truncatedSquare_submatrix_eq]
  refine truncatedSquare_det_nonneg_of_small_or_chamber (ha.comp hI) (ht.comp hJ) ?_
  rcases h with hn | ⟨_, hcol⟩ | ⟨_, hch⟩
  · exact Or.inl hn
  · exact Or.inr (Or.inl ⟨inferInstance, hcol⟩)
  · exact Or.inr (Or.inr ⟨inferInstance, hch⟩)

lemma truncatedSquare_isTotallyNonnegative_of_small {r c : ℕ}
    {a : Fin r → ℝ} {t : Fin c → ℝ} (ha : Monotone a) (ht : Monotone t) :
    ∀ _k ≤ 3, ∀ I : Fin _k → Fin r, ∀ J : Fin _k → Fin c,
      StrictMono I → StrictMono J →
        0 ≤ ((truncatedSquare a t).submatrix I J).det :=
  fun _k hk I J hI hJ =>
    truncatedSquare_minor_nonneg_of_small_or_chamber ha ht I J
      hI.monotone hJ.monotone (Or.inl hk)

/-! ### Step kernel, Cauchy–Binet, and the discrete-to-continuous limit (TN13) -/

open Finset Filter Metric

noncomputable section

/-- Indicator kernel `H(a,t) = 1_{a ≤ t}`. -/
def stepKernel (a : ι → ℝ) (t : κ → ℝ) : Matrix ι κ ℝ :=
  fun i j => if a i ≤ t j then (1 : ℝ) else 0

lemma stepKernel_apply (a : ι → ℝ) (t : κ → ℝ) (i : ι) (j : κ) :
    stepKernel a t i j = if a i ≤ t j then (1 : ℝ) else 0 :=
  rfl

lemma stepKernel_submatrix_eq {r c n m : ℕ}
    (a : Fin r → ℝ) (t : Fin c → ℝ) (I : Fin n → Fin r) (J : Fin m → Fin c) :
    (stepKernel a t).submatrix I J = stepKernel (a ∘ I) (t ∘ J) :=
  rfl

/-- Columns where the `i`-th step-row is one. -/
def stepSupport {n : ℕ} (a t : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  univ.filter (fun j => a i ≤ t j)

/-- First column index where `a i ≤ t j`, or `n` if the row is zero. -/
def stepCutoff {n : ℕ} (a t : Fin n → ℝ) (i : Fin n) : ℕ :=
  if h : (stepSupport a t i).Nonempty then ((stepSupport a t i).min' h : ℕ) else n

lemma stepSupport_anti {n : ℕ} {a t : Fin n → ℝ} (ha : Monotone a)
    {i i' : Fin n} (h : i ≤ i') :
    stepSupport a t i' ⊆ stepSupport a t i := by
  intro j hj
  simp only [stepSupport, mem_filter, mem_univ, true_and] at hj ⊢
  exact (ha h).trans hj

lemma stepCutoff_mono {n : ℕ} {a t : Fin n → ℝ} (ha : Monotone a) :
    Monotone (stepCutoff a t) := by
  intro i i' hii
  simp only [stepCutoff]
  by_cases hi' : (stepSupport a t i').Nonempty
  · have hi : (stepSupport a t i).Nonempty := hi'.mono (stepSupport_anti ha hii)
    simp only [hi, hi', ↓reduceDIte]
    exact (stepSupport a t i).min'_le _ ((stepSupport_anti ha hii) (min'_mem _ hi'))
  · simp only [hi', ↓reduceDIte]
    split_ifs <;> omega

lemma stepKernel_eq_of_cutoff {n : ℕ} {a t : Fin n → ℝ} (ht : Monotone t)
    (i j : Fin n) :
    stepKernel a t i j = if stepCutoff a t i ≤ (j : ℕ) then (1 : ℝ) else 0 := by
  simp only [stepKernel, stepCutoff]
  by_cases hne : (stepSupport a t i).Nonempty
  · simp only [hne, ↓reduceDIte]
    have hmem : (j ∈ stepSupport a t i) ↔ a i ≤ t j := by
      simp [stepSupport]
    have hmin : ((stepSupport a t i).min' hne : ℕ) ≤ (j : ℕ) ↔ j ∈ stepSupport a t i := by
      constructor
      · intro hj
        have hj' : (stepSupport a t i).min' hne ≤ j := Nat.cast_le.mp hj
        have hminmem := min'_mem (stepSupport a t i) hne
        simp only [stepSupport, mem_filter, mem_univ, true_and] at hminmem
        have : a i ≤ t j := hminmem.trans (ht hj')
        simpa [stepSupport] using this
      · intro hj
        exact Nat.cast_le.mpr ((stepSupport a t i).min'_le j hj)
    by_cases haij : a i ≤ t j
    · simp [haij, hmin, hmem]
    · simp [haij, hmin, hmem]
  · simp only [hne, ↓reduceDIte]
    have : ¬ a i ≤ t j := by
      intro hij
      exact hne ⟨j, by simp [stepSupport, hij]⟩
    have : ¬ n ≤ (j : ℕ) := not_le.mpr j.isLt
    simp [this, ‹¬ a i ≤ t j›]

lemma det_ones_of_le (n : ℕ) :
    (Matrix.of fun i j : Fin n => if i ≤ j then (1 : ℝ) else 0).det = 1 := by
  rw [det_of_isUpperTriangular]
  · simp
  · intro i j hij
    have : ¬ i ≤ j := not_le.mpr hij
    simp [this]

lemma strictMono_fin_to_nat_ge {n : ℕ} {c : Fin n → ℕ} (hc : StrictMono c) (i : Fin n) :
    (i : ℕ) ≤ c i := by
  have h : ∀ k : ℕ, ∀ hk : k < n, k ≤ c ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < n := Nat.lt_of_succ_lt hk
      have hlt : c ⟨k, hk'⟩ < c ⟨k + 1, hk⟩ := by
        refine hc ?_
        rw [Fin.lt_def]
        exact Nat.lt_succ_self k
      have := ih hk'
      omega
  exact h i.val i.isLt

lemma strictMono_fin_to_nat_walk {n : ℕ} {c : Fin (n + 1) → ℕ} (hc : StrictMono c)
    (i : Fin (n + 1)) (d : ℕ) (hd : (i : ℕ) + d < n + 1) :
    c i + d ≤ c ⟨(i : ℕ) + d, hd⟩ := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hd' : (i : ℕ) + d < n + 1 := Nat.lt_of_succ_lt hd
    have heq : (⟨(i : ℕ) + d + 1, hd⟩ : Fin (n + 1)) = ⟨(i : ℕ) + (d + 1), hd⟩ := by
      ext; simp [Nat.add_assoc]
    have hlt : c ⟨(i : ℕ) + d, hd'⟩ < c ⟨(i : ℕ) + d + 1, hd⟩ := by
      refine hc ?_
      rw [Fin.lt_def]
      exact Nat.lt_succ_self _
    have := ih hd'
    rw [heq] at hlt
    omega

lemma strictMono_fin_to_nat_eq {n : ℕ} {c : Fin (n + 1) → ℕ}
    (hc : StrictMono c) (hbnd : ∀ i, c i < n + 1) (i : Fin (n + 1)) :
    c i = (i : ℕ) := by
  have hge := strictMono_fin_to_nat_ge hc i
  refine le_antisymm ?_ hge
  have hlast : c (Fin.last n) = n := by
    have hge' : (Fin.last n : ℕ) ≤ c (Fin.last n) :=
      strictMono_fin_to_nat_ge hc (Fin.last n)
    have hb : c (Fin.last n) < n + 1 := hbnd _
    simp [Fin.val_last] at hge'
    omega
  have hd : (i : ℕ) + (n - (i : ℕ)) < n + 1 := by
    have : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    omega
  have hwalk := strictMono_fin_to_nat_walk hc i (n - (i : ℕ)) hd
  have : (⟨(i : ℕ) + (n - (i : ℕ)), hd⟩ : Fin (n + 1)) = Fin.last n := by
    ext
    have : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    simp [Fin.last, this]
  rw [this, hlast] at hwalk
  have : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  omega

lemma stepKernel_det_nonneg {n : ℕ} {a t : Fin n → ℝ}
    (ha : Monotone a) (ht : Monotone t) :
    0 ≤ (stepKernel a t).det := by
  cases n with
  | zero =>
    simp [det_eq_one_of_card_eq_zero (Fintype.card_fin 0)]
  | succ n =>
    let c := stepCutoff a t
    have hcmono : Monotone c := stepCutoff_mono ha
    have hent : ∀ i j, stepKernel a t i j = if c i ≤ (j : ℕ) then (1 : ℝ) else 0 :=
      fun i j => stepKernel_eq_of_cutoff ht i j
    by_cases hzero : ∃ i, c i = n + 1
    · obtain ⟨i, hi⟩ := hzero
      refine (det_eq_zero_of_row_eq_zero i ?_).symm.le
      intro j
      have : ¬ c i ≤ (j : ℕ) := by
        have : (j : ℕ) < n + 1 := j.isLt
        omega
      simp [hent, this]
    by_cases hdup : ∃ i i' : Fin (n + 1), i ≠ i' ∧ c i = c i'
    · obtain ⟨i, i', hne, heq⟩ := hdup
      refine (det_zero_of_row_eq hne ?_).symm.le
      ext j
      simp [hent, heq]
    have hbnd : ∀ i, c i < n + 1 := by
      intro i
      have hne : c i ≠ n + 1 := fun h => hzero ⟨i, h⟩
      have hle : c i ≤ n + 1 := by
        simp only [c, stepCutoff]
        split_ifs with h
        · exact le_of_lt ((stepSupport a t i).min' h).isLt
        · exact le_rfl
      omega
    have hinj : Function.Injective c := by
      intro i i' h
      by_contra hne
      exact hdup ⟨i, i', hne, h⟩
    have hstrict : StrictMono c := hcmono.strictMono_of_injective hinj
    have hci : ∀ i, c i = (i : ℕ) := strictMono_fin_to_nat_eq hstrict hbnd
    have : stepKernel a t =
        Matrix.of fun i j => if i ≤ j then (1 : ℝ) else 0 := by
      ext i j
      rw [hent, hci, Matrix.of_apply]
      exact if_congr Fin.val_fin_le.symm rfl rfl
    rw [this, det_ones_of_le]
    exact zero_le_one

lemma stepKernel_isTotallyNonneg {r c : ℕ} {a : Fin r → ℝ} {t : Fin c → ℝ}
    (ha : Monotone a) (ht : Monotone t) :
    IsTotallyNonneg (stepKernel a t) := by
  intro k I J hI hJ
  rw [stepKernel_submatrix_eq]
  exact stepKernel_det_nonneg (ha.comp hI.monotone) (ht.comp hJ.monotone)

lemma diagonal_isTotallyNonneg {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    IsTotallyNonneg (diagonal d) := by
  intro k I J hI hJ
  by_cases hIJ : I = J
  · subst hIJ
    have hdiag : (diagonal d).submatrix I I = diagonal (d ∘ I) := by
      ext i j
      simp only [submatrix_apply, diagonal]
      by_cases hij : i = j
      · simp [hij]
      · have : I i ≠ I j := hI.injective.ne hij
        simp [hij, this]
    rw [hdiag, det_diagonal]
    exact prod_nonneg fun i _ => hd _
  · have himg : univ.image I ≠ univ.image J := by
      intro h
      have hc : (univ.image I).card = k := by
        rw [card_image_of_injective _ hI.injective, card_univ, Fintype.card_fin]
      have hIunq := orderEmbOfFin_unique hc
        (fun i => mem_image_of_mem _ (mem_univ _)) hI
      have hJunq := orderEmbOfFin_unique (h ▸ hc)
        (fun i => show J i ∈ univ.image I from h ▸ mem_image_of_mem _ (mem_univ _)) hJ
      exact hIJ (hIunq.trans hJunq.symm)
    have hss : ¬ univ.image I ⊆ univ.image J ∨ ¬ univ.image J ⊆ univ.image I :=
      not_and_or.mp fun h => himg (Subset.antisymm h.1 h.2)
    rcases hss with hsub | hsub
    · obtain ⟨x, hxI, hxJ⟩ := not_subset.mp hsub
      obtain ⟨i, _, rfl⟩ := mem_image.mp hxI
      refine (det_eq_zero_of_row_eq_zero i ?_).symm.le
      intro j
      have : I i ≠ J j := by
        intro h
        exact hxJ (mem_image.mpr ⟨j, mem_univ _, h.symm⟩)
      simp [submatrix_apply, diagonal, this]
    · obtain ⟨x, hxJ, hxI⟩ := not_subset.mp hsub
      obtain ⟨j, _, rfl⟩ := mem_image.mp hxJ
      refine (det_eq_zero_of_column_eq_zero j ?_).symm.le
      intro i
      have : I i ≠ J j := by
        intro h
        exact hxI (mem_image.mpr ⟨i, mem_univ _, h⟩)
      simp [submatrix_apply, diagonal, this]

/-- Strictly increasing maps `Fin k → Fin m`. -/
abbrev StrictMonoFin (k m : ℕ) := {f : Fin k → Fin m // StrictMono f}

noncomputable instance decidablePredStrictMonoFin (k m : ℕ) :
    DecidablePred fun f : Fin k → Fin m => StrictMono f :=
  Classical.decPred _

noncomputable instance (k m : ℕ) : Fintype (StrictMonoFin k m) :=
  Subtype.fintype _

/-- The strictly increasing enumeration of the image of an injection `u : Fin k → Fin m`. -/
noncomputable def injRearrange {k m : ℕ} {u : Fin k → Fin m} (hu : Function.Injective u) :
    StrictMonoFin k m :=
  ⟨(univ.image u).orderEmbOfFin (by
      rw [card_image_of_injective _ hu, card_univ, Fintype.card_fin]),
    ((univ.image u).orderEmbOfFin _).strictMono⟩

lemma injRearrange_mem {k m : ℕ} {u : Fin k → Fin m} (hu : Function.Injective u) (i : Fin k) :
    ∃ j, (injRearrange hu).1 j = u i := by
  have : u i ∈ Set.range (injRearrange hu).1 := by
    change u i ∈ Set.range ((univ.image u).orderEmbOfFin _)
    rw [range_orderEmbOfFin]
    exact mem_image_of_mem _ (mem_univ _)
  exact this

/-- The permutation of `Fin k` through which an injection `u` factors as `injRearrange hu ∘ injPerm
hu`. -/
noncomputable def injPerm {k m : ℕ} {u : Fin k → Fin m} (hu : Function.Injective u) :
    Equiv.Perm (Fin k) :=
  Equiv.ofBijective (fun i => Classical.choose (injRearrange_mem hu i)) <| by
    have hspec : ∀ i, (injRearrange hu).1 (Classical.choose (injRearrange_mem hu i)) = u i :=
      fun i => Classical.choose_spec (injRearrange_mem hu i)
    have hinj : Function.Injective fun i => Classical.choose (injRearrange_mem hu i) := by
      intro i i' h
      apply hu
      have := congrArg (injRearrange hu).1 h
      rw [hspec i, hspec i'] at this
      exact this
    exact ⟨hinj, Finite.surjective_of_injective hinj⟩

lemma inj_eq_rearrange_comp {k m : ℕ} {u : Fin k → Fin m} (hu : Function.Injective u) :
    u = (injRearrange hu).1 ∘ injPerm hu := by
  funext i
  have hπ : injPerm hu i = Classical.choose (injRearrange_mem hu i) := rfl
  rw [Function.comp_apply, hπ]
  exact (Classical.choose_spec (injRearrange_mem hu i)).symm

lemma image_comp_perm {k m : ℕ} (S : Fin k → Fin m) (π : Equiv.Perm (Fin k)) :
    univ.image (S ∘ π) = univ.image S := by
  ext x
  simp only [mem_image, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨π i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨π.symm i, by simp⟩

lemma injRearrange_comp {k m : ℕ} (S : StrictMonoFin k m) (π : Equiv.Perm (Fin k)) :
    injRearrange (S.2.injective.comp π.injective) = S := by
  have hu : Function.Injective (S.1 ∘ π) := S.2.injective.comp π.injective
  apply Subtype.ext
  refine (StrictMono.range_inj (injRearrange hu).2 S.2).1 ?_
  have h1 : Set.range (injRearrange hu).1 = ((univ.image (S.1 ∘ π) : Finset _) : Set _) := by
    simp only [injRearrange]
    exact range_orderEmbOfFin _ _
  have h2 : Set.range S.1 = ((univ.image S.1 : Finset _) : Set _) := by
    ext x; simp [Set.mem_range]
  rw [h1, h2, image_comp_perm]

lemma injPerm_comp {k m : ℕ} (S : StrictMonoFin k m) (π : Equiv.Perm (Fin k)) :
    injPerm (S.2.injective.comp π.injective) = π := by
  have hu : Function.Injective (S.1 ∘ π) := S.2.injective.comp π.injective
  have hS : (injRearrange hu).1 = S.1 := congrArg Subtype.val (injRearrange_comp S π)
  refine Equiv.ext fun i => ?_
  apply S.2.injective
  calc S.1 (injPerm hu i)
      = (injRearrange hu).1 (injPerm hu i) := by rw [hS]
    _ = (S.1 ∘ π) i := (congrFun (inj_eq_rearrange_comp hu) i).symm
    _ = S.1 (π i) := rfl

/-- Injections `Fin k → Fin m` correspond to pairs of a strictly increasing map and a permutation of
`Fin k`. -/
noncomputable def equivInjOfStrictMono (k m : ℕ) :
    StrictMonoFin k m × Equiv.Perm (Fin k) ≃
      {u : Fin k → Fin m // Function.Injective u} where
  toFun := fun p => ⟨p.1.1 ∘ p.2, p.1.2.injective.comp p.2.injective⟩
  invFun := fun u => (injRearrange u.2, injPerm u.2)
  left_inv := fun p =>
    Prod.ext (injRearrange_comp p.1 p.2) (injPerm_comp p.1 p.2)
  right_inv := fun u => Subtype.ext (inj_eq_rearrange_comp u.2).symm

lemma det_mul_eq_sum_comp {k m : ℕ}
    (P : Matrix (Fin k) (Fin m) ℝ) (Q : Matrix (Fin m) (Fin k) ℝ) :
    (P * Q).det =
      ∑ p : Fin k → Fin m, (P.submatrix id p).det * ∏ i, Q (p i) i := by
  calc (P * Q).det
      = ∑ p : Fin k → Fin m, ∑ σ : Equiv.Perm (Fin k),
          Equiv.Perm.sign σ * ∏ i, P (σ i) (p i) * Q (p i) i := by
        simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
        rw [sum_comm]
    _ = ∑ p : Fin k → Fin m, (P.submatrix id p).det * ∏ i, Q (p i) i := by
        refine sum_congr rfl fun p _ => ?_
        have hprod :
            (∑ σ : Equiv.Perm (Fin k),
                Equiv.Perm.sign σ * ∏ i, P (σ i) (p i) * Q (p i) i) =
              (∑ σ : Equiv.Perm (Fin k),
                Equiv.Perm.sign σ * ∏ i, P (σ i) (p i)) * ∏ i, Q (p i) i := by
          simp only [prod_mul_distrib]
          calc ∑ σ : Equiv.Perm (Fin k),
                Equiv.Perm.sign σ * ((∏ i, P (σ i) (p i)) * ∏ i, Q (p i) i)
              = ∑ σ : Equiv.Perm (Fin k),
                  (∏ i, Q (p i) i) * (Equiv.Perm.sign σ * ∏ i, P (σ i) (p i)) := by
                refine sum_congr rfl fun σ _ => ?_
                ring
            _ = (∏ i, Q (p i) i) *
                  ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ * ∏ i, P (σ i) (p i) := by
                rw [← mul_sum]
            _ = (∑ σ : Equiv.Perm (Fin k),
                  Equiv.Perm.sign σ * ∏ i, P (σ i) (p i)) * ∏ i, Q (p i) i := by
                ring
        rw [hprod]
        congr 1
        simp [det_apply', submatrix_apply]

lemma det_mul_eq_sum_strictMono {k m : ℕ}
    (P : Matrix (Fin k) (Fin m) ℝ) (Q : Matrix (Fin m) (Fin k) ℝ) :
    (P * Q).det =
      ∑ S : StrictMonoFin k m,
        (P.submatrix id S.1).det * (Q.submatrix S.1 id).det := by
  classical
  rw [det_mul_eq_sum_comp]
  have hzero :
      ∑ p : Fin k → Fin m, (P.submatrix id p).det * ∏ i, Q (p i) i =
        ∑ p : {u : Fin k → Fin m // Function.Injective u},
          (P.submatrix id p.1).det * ∏ i, Q (p.1 i) i := by
    have hfilter :
        ∑ p ∈ univ.filter Function.Injective,
            (P.submatrix id p).det * ∏ i, Q (p i) i =
          ∑ p : Fin k → Fin m, (P.submatrix id p).det * ∏ i, Q (p i) i := by
      refine sum_subset (filter_subset _ _) ?_
      intro p _ hp
      have : ¬ Function.Injective p := by simpa using hp
      simp [det_submatrix_eq_zero_of_not_injective P (Or.inr this)]
    rw [← hfilter]
    exact sum_subtype (univ.filter Function.Injective)
      (fun p => by simp [mem_filter])
      (fun p => (P.submatrix id p).det * ∏ i, Q (p i) i)
  rw [hzero, ← Equiv.sum_comp (equivInjOfStrictMono k m)]
  simp only [equivInjOfStrictMono, Equiv.coe_fn_mk, Fintype.sum_prod_type]
  refine sum_congr rfl fun S _ => ?_
  have hπ : ∀ π : Equiv.Perm (Fin k),
      (P.submatrix id (S.1 ∘ π)).det * ∏ i, Q (S.1 (π i)) i =
        Equiv.Perm.sign π * (P.submatrix id S.1).det * ∏ i, Q (S.1 (π i)) i := by
    intro π
    have hsub : P.submatrix id (S.1 ∘ π) = (P.submatrix id S.1).submatrix id π := by
      ext; simp
    rw [hsub, det_permute']
  refine Eq.trans (sum_congr rfl fun π _ => hπ π) ?_
  have hfactor :
      ∑ π : Equiv.Perm (Fin k),
          Equiv.Perm.sign π * (P.submatrix id S.1).det * ∏ i, Q (S.1 (π i)) i =
        (P.submatrix id S.1).det *
          ∑ π : Equiv.Perm (Fin k), Equiv.Perm.sign π * ∏ i, Q (S.1 (π i)) i := by
    have hπmul : ∀ π : Equiv.Perm (Fin k),
        Equiv.Perm.sign π * (P.submatrix id S.1).det * ∏ i, Q (S.1 (π i)) i =
          (P.submatrix id S.1).det *
            (Equiv.Perm.sign π * ∏ i, Q (S.1 (π i)) i) := fun π => by ring
    exact (sum_congr rfl fun π _ => hπmul π).trans
      (mul_sum (univ : Finset (Equiv.Perm (Fin k)))
        (fun π => Equiv.Perm.sign π * ∏ i, Q (S.1 (π i)) i)
        (P.submatrix id S.1).det).symm
  exact hfactor.trans <| by
    congr 1
    simp [det_apply', submatrix_apply]

lemma IsTotallyNonneg.mul {l m n : Type*}
    [LinearOrder l] [LinearOrder m] [LinearOrder n]
    [Fintype m]
    {A : Matrix l m ℝ} {B : Matrix m n ℝ}
    (hA : IsTotallyNonneg A) (hB : IsTotallyNonneg B) :
    IsTotallyNonneg (A * B) := by
  intro k I J hI hJ
  let e : Fin (Fintype.card m) ≃o m := monoEquivOfFin m rfl
  have hre : (A * B).submatrix I J =
      A.submatrix I e * B.submatrix (e : Fin (Fintype.card m) → m) J := by
    ext i j
    simp only [submatrix_apply, mul_apply]
    exact (e.toEquiv.sum_comp fun x => A (I i) x * B x (J j)).symm
  rw [hre, det_mul_eq_sum_strictMono]
  refine sum_nonneg fun S _ =>
    mul_nonneg (hA k I (e ∘ S.1) hI (e.strictMono.comp S.2))
      (hB k (e ∘ S.1) J (e.strictMono.comp S.2) hJ)

/-! ### Uniform grid composition -/

/-- The finite set of all values `a i` and `t j`. -/
noncomputable def valuesFinset {r c : ℕ} (a : Fin r → ℝ) (t : Fin c → ℝ) : Finset ℝ :=
  univ.image a ∪ univ.image t

lemma valuesFinset_nonempty {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) :
    (valuesFinset a t).Nonempty :=
  ⟨a ⟨0, hr⟩, mem_union_left _ (mem_image_of_mem _ (mem_univ _))⟩

/-- One less than the smallest of the values `a i` and `t j`. -/
noncomputable def gridXMin {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) : ℝ :=
  (valuesFinset a t).min' (valuesFinset_nonempty hr a t) - 1

/-- One more than the largest of the values `a i` and `t j`. -/
noncomputable def gridXMax {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) : ℝ :=
  (valuesFinset a t).max' (valuesFinset_nonempty hr a t) + 1

lemma gridXMin_lt_a {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) (i : Fin r) :
    gridXMin hr a t < a i := by
  have : (valuesFinset a t).min' (valuesFinset_nonempty hr a t) ≤ a i :=
    (valuesFinset a t).min'_le _ (mem_union_left _ (mem_image_of_mem _ (mem_univ _)))
  simp [gridXMin]; linarith

lemma gridXMax_gt_t {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) (j : Fin c) :
    t j < gridXMax hr a t := by
  have : t j ≤ (valuesFinset a t).max' (valuesFinset_nonempty hr a t) :=
    (valuesFinset a t).le_max' _ (mem_union_right _ (mem_image_of_mem _ (mem_univ _)))
  simp [gridXMax]; linarith

lemma gridXMax_gt_a {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) (i : Fin r) :
    a i < gridXMax hr a t := by
  have : a i ≤ (valuesFinset a t).max' (valuesFinset_nonempty hr a t) :=
    (valuesFinset a t).le_max' _ (mem_union_left _ (mem_image_of_mem _ (mem_univ _)))
  simp [gridXMax]; linarith

lemma grid_span_pos {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) :
    0 < gridXMax hr a t - gridXMin hr a t := by
  have := gridXMin_lt_a hr a t ⟨0, hr⟩
  have := gridXMax_gt_a hr a t ⟨0, hr⟩
  linarith

/-- The mesh of the uniform grid with `N` steps from `gridXMin` to `gridXMax`. -/
noncomputable def gridDelta {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) (N : ℕ) : ℝ :=
  (gridXMax hr a t - gridXMin hr a t) / N

lemma gridDelta_nonneg {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) (N : ℕ) :
    0 ≤ gridDelta hr a t N :=
  div_nonneg (le_of_lt (grid_span_pos hr a t)) (Nat.cast_nonneg _)

lemma gridDelta_pos {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) {N : ℕ}
    (hN : 0 < N) :
    0 < gridDelta hr a t N :=
  div_pos (grid_span_pos hr a t) (Nat.cast_pos.mpr hN)

/-- The `k`-th point of the uniform grid: `gridXMin + k * gridDelta`. -/
noncomputable def gridPt {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    (N : ℕ) (k : Fin (N + 1)) : ℝ :=
  gridXMin hr a t + k.val * gridDelta hr a t N

lemma gridPt_mono {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) (N : ℕ) :
    Monotone (gridPt hr a t N) := by
  intro k ℓ hkl
  simp only [gridPt]
  gcongr
  · exact gridDelta_nonneg hr a t N
  · exact Nat.cast_le.mpr (Fin.val_le_of_le hkl)

lemma gridPt_strictMono {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    {N : ℕ} (hN : 0 < N) :
    StrictMono (gridPt hr a t N) := by
  intro k ℓ hkl
  simp only [gridPt]
  have hkv : (k.val : ℝ) < ℓ.val := Nat.cast_lt.mpr (show k.val < ℓ.val by omega)
  nlinarith [gridDelta_pos hr a t hN]

lemma gridPt_zero {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) (N : ℕ) :
    gridPt hr a t N 0 = gridXMin hr a t := by
  simp [gridPt]

lemma gridPt_last {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) {N : ℕ}
    (hN : 0 < N) :
    gridPt hr a t N (Fin.last N) = gridXMax hr a t := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp [gridPt, gridDelta, Fin.last, mul_div_cancel₀ _ hN0]

/-- The step kernel from the row parameters `a` to the grid points. -/
noncomputable def gridH1 {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) (N : ℕ) :
    Matrix (Fin r) (Fin (N + 1)) ℝ :=
  stepKernel a (gridPt hr a t N)

/-- The step kernel between grid indices, compared through their values. -/
noncomputable def gridH2 (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  stepKernel (fun k : Fin (N + 1) => (k.val : ℝ)) (fun ℓ => (ℓ.val : ℝ))

/-- The step kernel from the grid points to the column parameters `t`. -/
noncomputable def gridH3 {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin c) ℝ :=
  stepKernel (gridPt hr a t N) t

/-- The scalar matrix `gridDelta • 1` on grid indices. -/
noncomputable def gridD {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  diagonal fun _ => gridDelta hr a t N

/-- The product `H₁ D H₂ D H₃` of the grid kernels. -/
noncomputable def gridK {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) (N : ℕ) :
    Matrix (Fin r) (Fin c) ℝ :=
  gridH1 hr a t N * gridD hr a t N * gridH2 N * gridD hr a t N * gridH3 hr a t N

lemma gridH2_isTotallyNonneg (N : ℕ) : IsTotallyNonneg (gridH2 N) := by
  refine stepKernel_isTotallyNonneg ?_ ?_
  · intro k ℓ hkl
    exact Nat.cast_le.mpr (Fin.val_le_of_le hkl)
  · intro k ℓ hkl
    exact Nat.cast_le.mpr (Fin.val_le_of_le hkl)

lemma gridK_isTotallyNonneg {r c : ℕ} (hr : 0 < r)
    {a : Fin r → ℝ} {t : Fin c → ℝ} (ha : Monotone a) (ht : Monotone t) (N : ℕ) :
    IsTotallyNonneg (gridK hr a t N) :=
  ((((stepKernel_isTotallyNonneg ha (gridPt_mono hr a t N)).mul
        (diagonal_isTotallyNonneg _ fun _ => gridDelta_nonneg hr a t N)).mul
      (gridH2_isTotallyNonneg N)).mul
    (diagonal_isTotallyNonneg _ fun _ => gridDelta_nonneg hr a t N)).mul
    (stepKernel_isTotallyNonneg (gridPt_mono hr a t N) ht)

lemma gridH2_apply (N : ℕ) (k ℓ : Fin (N + 1)) :
    gridH2 N k ℓ = if k ≤ ℓ then (1 : ℝ) else 0 := by
  simp [gridH2, stepKernel, Nat.cast_le, Fin.val_fin_le]

lemma gridK_apply {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    (N : ℕ) (i : Fin r) (j : Fin c) :
    gridK hr a t N i j =
      gridDelta hr a t N ^ 2 *
        ∑ ℓ : Fin (N + 1), ∑ k : Fin (N + 1),
          if a i ≤ gridPt hr a t N k ∧ k ≤ ℓ ∧ gridPt hr a t N ℓ ≤ t j then
            (1 : ℝ) else 0 := by
  set δ := gridDelta hr a t N
  have hD : ∀ p q : Fin (N + 1), gridD hr a t N p q = if p = q then δ else 0 := by
    intro p q; simp [gridD, diagonal, δ]
  have h1 : ∀ k,
      (gridH1 hr a t N * gridD hr a t N) i k = gridH1 hr a t N i k * δ := by
    intro k
    simp only [mul_apply, hD, mul_ite, mul_zero]
    trans ∑ x : Fin (N + 1), if x = k then gridH1 hr a t N i k * δ else 0
    · refine sum_congr rfl fun x _ => ?_
      split_ifs with hx <;> simp [hx]
    · simp
  have h2 : ∀ p,
      (gridH1 hr a t N * gridD hr a t N * gridH2 N) i p =
        δ * ∑ k : Fin (N + 1), gridH1 hr a t N i k * gridH2 N k p := by
    intro p
    change ∑ k, (gridH1 hr a t N * gridD hr a t N) i k * gridH2 N k p = _
    simp_rw [h1]
    have hk : ∀ k, gridH1 hr a t N i k * δ * gridH2 N k p =
        δ * (gridH1 hr a t N i k * gridH2 N k p) := fun k => by ring
    simp_rw [hk]
    exact (mul_sum univ (fun k => gridH1 hr a t N i k * gridH2 N k p) δ).symm
  have h3 : ∀ q,
      (gridH1 hr a t N * gridD hr a t N * gridH2 N * gridD hr a t N) i q =
        δ ^ 2 * ∑ k : Fin (N + 1), gridH1 hr a t N i k * gridH2 N k q := by
    intro q
    change ∑ p, (gridH1 hr a t N * gridD hr a t N * gridH2 N) i p * gridD hr a t N p q = _
    simp_rw [h2, hD]
    have hite : ∀ p,
        (δ * ∑ k : Fin (N + 1), gridH1 hr a t N i k * gridH2 N k p) *
            (if p = q then δ else 0) =
          if p = q then
            (δ * ∑ k : Fin (N + 1), gridH1 hr a t N i k * gridH2 N k q) * δ
          else 0 := by
      intro p
      split_ifs with hp <;> simp [hp]
    simp_rw [hite]
    have : ∑ p ∈ (univ : Finset (Fin (N + 1))),
        ite (p = q) ((δ * ∑ k : Fin (N + 1), gridH1 hr a t N i k * gridH2 N k q) * δ) 0 =
        (δ * ∑ k : Fin (N + 1), gridH1 hr a t N i k * gridH2 N k q) * δ := by
      simp
    rw [this]
    ring
  change ∑ q, (gridH1 hr a t N * gridD hr a t N * gridH2 N * gridD hr a t N) i q *
      gridH3 hr a t N q j = _
  simp_rw [h3]
  have hswap :
      ∑ q : Fin (N + 1),
          (δ ^ 2 * ∑ k : Fin (N + 1), gridH1 hr a t N i k * gridH2 N k q) *
            gridH3 hr a t N q j =
        δ ^ 2 * ∑ q : Fin (N + 1), ∑ k : Fin (N + 1),
          gridH1 hr a t N i k * gridH2 N k q * gridH3 hr a t N q j := by
    have hq : ∀ q,
        (δ ^ 2 * ∑ k : Fin (N + 1), gridH1 hr a t N i k * gridH2 N k q) *
            gridH3 hr a t N q j =
          δ ^ 2 * ∑ k : Fin (N + 1),
            gridH1 hr a t N i k * gridH2 N k q * gridH3 hr a t N q j := by
      intro q
      rw [mul_assoc, sum_mul]
    simp_rw [hq, ← mul_sum]
  rw [hswap]
  refine congrArg (fun t => δ ^ 2 * t) ?_
  refine sum_congr rfl fun ℓ _ => sum_congr rfl fun k _ => ?_
  by_cases hak : a i ≤ gridPt hr a t N k
  · by_cases hkl : k ≤ ℓ
    · by_cases hℓt : gridPt hr a t N ℓ ≤ t j
      · simp [gridH1, gridH3, stepKernel, gridH2_apply, hak, hkl, hℓt]
      · simp [gridH1, gridH3, stepKernel, gridH2_apply, hak, hkl, hℓt]
    · simp [gridH1, gridH3, stepKernel, gridH2_apply, hak, hkl]
  · simp [gridH1, gridH3, stepKernel, gridH2_apply, hak]

lemma sum_ite_le_real (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, if i ≤ j then (1 : ℝ) else 0) =
      (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [@Fin.sum_univ_succ ℝ _ n]
    have h0 : ∑ j : Fin (n + 1), (if (0 : Fin (n + 1)) ≤ j then (1 : ℝ) else 0) =
        (n + 1 : ℝ) := by
      simp
    have hrest :
        ∑ i : Fin n, ∑ j : Fin (n + 1), (if i.succ ≤ j then (1 : ℝ) else 0) =
          ∑ i : Fin n, ∑ j : Fin n, (if i ≤ j then (1 : ℝ) else 0) := by
      refine sum_congr rfl fun i _ => ?_
      rw [@Fin.sum_univ_succ ℝ _ n]
      have : ¬ i.succ ≤ (0 : Fin (n + 1)) :=
        not_le.mpr (Fin.succ_pos i)
      simp [this, Fin.succ_le_succ_iff]
    rw [h0, hrest, ih]
    push_cast
    ring

lemma sum_ite_le_finset {n : ℕ} (s : Finset (Fin n)) :
    ∑ x ∈ s, ∑ y ∈ s, (if x ≤ y then (1 : ℝ) else 0) =
      (s.card : ℝ) * (s.card + 1) / 2 := by
  let e := s.orderEmbOfFin rfl
  have hs : map e.toEmbedding univ = s := map_orderEmbOfFin_univ s rfl
  rw [← hs, sum_map]
  refine (sum_congr rfl fun _ _ => sum_map _ _ _).trans ?_
  refine (sum_congr rfl fun i _ => sum_congr rfl fun j _ =>
    if_congr e.map_rel_iff rfl rfl).trans ?_
  rw [sum_ite_le_real s.card]
  simp [hs]

/-- The grid indices `k` with `a i ≤ gridPt k ≤ t j`. -/
noncomputable def gridSupport {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    (N : ℕ) (i : Fin r) (j : Fin c) : Finset (Fin (N + 1)) :=
  univ.filter (fun k => a i ≤ gridPt hr a t N k ∧ gridPt hr a t N k ≤ t j)

lemma grid_pair_sum_eq {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    (N : ℕ) (i : Fin r) (j : Fin c) :
    (∑ ℓ : Fin (N + 1), ∑ k : Fin (N + 1),
        (if a i ≤ gridPt hr a t N k ∧ k ≤ ℓ ∧ gridPt hr a t N ℓ ≤ t j then
          (1 : ℝ) else 0)) =
      ∑ ℓ ∈ gridSupport hr a t N i j, ∑ k ∈ gridSupport hr a t N i j,
        (if k ≤ ℓ then (1 : ℝ) else 0) := by
  have hx : Monotone (gridPt hr a t N) := gridPt_mono hr a t N
  have hiff : ∀ k ℓ : Fin (N + 1),
      (a i ≤ gridPt hr a t N k ∧ k ≤ ℓ ∧ gridPt hr a t N ℓ ≤ t j) ↔
        (k ∈ gridSupport hr a t N i j ∧ ℓ ∈ gridSupport hr a t N i j ∧ k ≤ ℓ) := by
    intro k ℓ
    simp only [gridSupport, mem_filter, mem_univ, true_and]
    constructor
    · intro ⟨hak, hkl, hℓt⟩
      exact ⟨⟨hak, le_trans (hx hkl) hℓt⟩, ⟨le_trans hak (hx hkl), hℓt⟩, hkl⟩
    · intro ⟨⟨hak, _⟩, ⟨_, hℓt⟩, hkl⟩
      exact ⟨hak, hkl, hℓt⟩
  have hinner :
      (∑ ℓ : Fin (N + 1), ∑ k : Fin (N + 1),
          (if a i ≤ gridPt hr a t N k ∧ k ≤ ℓ ∧ gridPt hr a t N ℓ ≤ t j then
            (1 : ℝ) else 0)) =
        ∑ ℓ : Fin (N + 1), ∑ k : Fin (N + 1),
          (if k ∈ gridSupport hr a t N i j ∧ ℓ ∈ gridSupport hr a t N i j ∧ k ≤ ℓ then
            (1 : ℝ) else 0) := by
    refine sum_congr rfl fun ℓ _ => sum_congr rfl fun k _ => ?_
    simp [hiff]
  rw [hinner]
  have hsplit :
      ∀ ℓ, (∑ k : Fin (N + 1),
          (if k ∈ gridSupport hr a t N i j ∧ ℓ ∈ gridSupport hr a t N i j ∧ k ≤ ℓ then
            (1 : ℝ) else 0)) =
        if ℓ ∈ gridSupport hr a t N i j then
          ∑ k : Fin (N + 1),
            (if k ∈ gridSupport hr a t N i j ∧ k ≤ ℓ then (1 : ℝ) else 0)
        else 0 := by
    intro ℓ
    split_ifs with hℓ <;> simp [hℓ]
  simp_rw [hsplit]
  rw [← sum_filter, filter_univ_mem]
  refine sum_congr rfl fun ℓ _ => ?_
  have ksplit :
      ∀ k, (if k ∈ gridSupport hr a t N i j ∧ k ≤ ℓ then (1 : ℝ) else 0) =
        if k ∈ gridSupport hr a t N i j then
          (if k ≤ ℓ then (1 : ℝ) else 0) else 0 :=
    fun k => ite_and _ _ _ _
  simp_rw [ksplit]
  rw [← sum_filter, filter_univ_mem]

lemma gridK_apply_count {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    (N : ℕ) (i : Fin r) (j : Fin c) :
    gridK hr a t N i j =
      gridDelta hr a t N ^ 2 *
        ((gridSupport hr a t N i j).card : ℝ) *
          (((gridSupport hr a t N i j).card : ℝ) + 1) / 2 := by
  rw [gridK_apply, grid_pair_sum_eq]
  have hswap :
      ∑ ℓ ∈ gridSupport hr a t N i j, ∑ k ∈ gridSupport hr a t N i j,
          (if k ≤ ℓ then (1 : ℝ) else 0) =
        ∑ k ∈ gridSupport hr a t N i j, ∑ ℓ ∈ gridSupport hr a t N i j,
          (if k ≤ ℓ then (1 : ℝ) else 0) :=
    Finset.sum_comm
  rw [hswap, sum_ite_le_finset]
  ring

lemma gridSupport_interval {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    {N : ℕ} (_hN : 0 < N) (i : Fin r) (j : Fin c)
    (hne : (gridSupport hr a t N i j).Nonempty) :
    gridSupport hr a t N i j =
      Icc (min' (gridSupport hr a t N i j) hne) (max' (gridSupport hr a t N i j) hne) := by
  ext k
  simp only [gridSupport, mem_filter, mem_univ, true_and, mem_Icc]
  constructor
  · intro hk
    exact ⟨(gridSupport hr a t N i j).min'_le _ (by simpa [gridSupport] using hk),
      (gridSupport hr a t N i j).le_max' _ (by simpa [gridSupport] using hk)⟩
  · intro ⟨hkmin, hkmax⟩
    have hmin := min'_mem (gridSupport hr a t N i j) hne
    have hmax := max'_mem (gridSupport hr a t N i j) hne
    simp only [gridSupport, mem_filter, mem_univ, true_and] at hmin hmax
    have hx := gridPt_mono hr a t N
    exact ⟨le_trans hmin.1 (hx hkmin), le_trans (hx hkmax) hmax.2⟩

lemma gridPt_succ {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    (N : ℕ) (k : Fin (N + 1)) (hk : k.val + 1 < N + 1) :
    gridPt hr a t N ⟨k.val + 1, hk⟩ =
      gridPt hr a t N k + gridDelta hr a t N := by
  unfold gridPt
  have hcast : ((k.val + 1 : ℕ) : ℝ) = (k.val : ℝ) + 1 := Nat.cast_succ k.val
  rw [hcast, add_mul, one_mul, add_assoc]

lemma gridPt_sub_eq {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    (N : ℕ) {k ℓ : Fin (N + 1)} (hkl : k ≤ ℓ) :
    gridPt hr a t N ℓ - gridPt hr a t N k =
      ((ℓ.val - k.val : ℕ) : ℝ) * gridDelta hr a t N := by
  unfold gridPt
  have hle : k.val ≤ ℓ.val := Fin.val_le_of_le hkl
  have hcast : (ℓ.val : ℝ) - k.val = ((ℓ.val - k.val : ℕ) : ℝ) := (Nat.cast_sub hle).symm
  calc gridXMin hr a t + (ℓ.val : ℝ) * gridDelta hr a t N -
        (gridXMin hr a t + (k.val : ℝ) * gridDelta hr a t N)
      = ((ℓ.val : ℝ) - k.val) * gridDelta hr a t N := by ring
    _ = ((ℓ.val - k.val : ℕ) : ℝ) * gridDelta hr a t N := by rw [hcast]

lemma not_mem_gridSupport_zero {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    (N : ℕ) (i : Fin r) (j : Fin c) :
    (0 : Fin (N + 1)) ∉ gridSupport hr a t N i j := by
  intro h
  have hai : a i ≤ gridPt hr a t N 0 := (mem_filter.mp h).2.1
  rw [gridPt_zero] at hai
  exact (not_le_of_gt (gridXMin_lt_a hr a t i)) hai

lemma not_mem_gridSupport_last {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    {N : ℕ} (hN : 0 < N) (i : Fin r) (j : Fin c) :
    Fin.last N ∉ gridSupport hr a t N i j := by
  intro h
  have htj : gridPt hr a t N (Fin.last N) ≤ t j := (mem_filter.mp h).2.2
  rw [gridPt_last hr a t hN] at htj
  exact (not_le_of_gt (gridXMax_gt_t hr a t j)) htj

lemma mem_gridSupport_iff {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    (N : ℕ) (i : Fin r) (j : Fin c) (k : Fin (N + 1)) :
    k ∈ gridSupport hr a t N i j ↔
      a i ≤ gridPt hr a t N k ∧ gridPt hr a t N k ≤ t j := by
  simp [gridSupport]

lemma gridSupport_card_mul_delta_sub_le {r c : ℕ} (hr : 0 < r)
    (a : Fin r → ℝ) (t : Fin c → ℝ) {N : ℕ} (hN : 0 < N)
    (i : Fin r) (j : Fin c) :
    |((gridSupport hr a t N i j).card : ℝ) * gridDelta hr a t N -
        max (t j - a i) 0| ≤ 2 * gridDelta hr a t N := by
  set S := gridSupport hr a t N i j
  set δ := gridDelta hr a t N
  set L := max (t j - a i) 0
  have h0nS : (0 : Fin (N + 1)) ∉ S := not_mem_gridSupport_zero hr a t N i j
  have hlastnS : Fin.last N ∉ S := not_mem_gridSupport_last hr a t hN i j
  by_cases hne : S.Nonempty
  · have hinter := gridSupport_interval hr a t hN i j hne
    set kmin := S.min' hne
    set ℓmax := S.max' hne
    have hkminS : kmin ∈ S := min'_mem S hne
    have hℓmaxS : ℓmax ∈ S := max'_mem S hne
    have hkmin0 : kmin ≠ 0 := fun h => h0nS (h ▸ hkminS)
    have hℓmaxN : ℓmax ≠ Fin.last N := fun h => hlastnS (h ▸ hℓmaxS)
    have hkminpos : 0 < kmin.val :=
      Nat.pos_of_ne_zero fun hv => hkmin0 (Fin.ext hv)
    have hℓmaxltFin : ℓmax < Fin.last N :=
      lt_of_le_of_ne (Fin.le_last ℓmax) hℓmaxN
    have hℓmaxlt : ℓmax.val < N := by
      simpa [Fin.lt_def, Fin.val_last] using hℓmaxltFin
    have hpred : kmin.val - 1 < N + 1 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) kmin.isLt
    have hsucc : ℓmax.val + 1 < N + 1 := Nat.succ_lt_succ hℓmaxlt
    let kpred : Fin (N + 1) := ⟨kmin.val - 1, hpred⟩
    let ℓsucc : Fin (N + 1) := ⟨ℓmax.val + 1, hsucc⟩
    have hkpred_val : kpred.val = kmin.val - 1 := rfl
    have hℓsucc_val : ℓsucc.val = ℓmax.val + 1 := rfl
    have hkpred_lt : kpred < kmin := by
      refine Fin.lt_def.mpr ?_
      rw [hkpred_val]
      exact Nat.sub_lt hkminpos (by norm_num)
    have hℓsucc_gt : ℓmax < ℓsucc := by
      refine Fin.lt_def.mpr ?_
      rw [hℓsucc_val]
      exact Nat.lt_succ_self _
    have hkpred_nS : kpred ∉ S :=
      fun hk => (not_lt_of_ge (S.min'_le kpred hk)) hkpred_lt
    have hℓsucc_nS : ℓsucc ∉ S :=
      fun hk => (not_lt_of_ge (S.le_max' ℓsucc hk)) hℓsucc_gt
    have hxkmin : a i ≤ gridPt hr a t N kmin ∧ gridPt hr a t N kmin ≤ t j :=
      (mem_gridSupport_iff hr a t N i j kmin).mp hkminS
    have hxℓmax : a i ≤ gridPt hr a t N ℓmax ∧ gridPt hr a t N ℓmax ≤ t j :=
      (mem_gridSupport_iff hr a t N i j ℓmax).mp hℓmaxS
    have hxkpred : gridPt hr a t N kpred < a i := by
      have : ¬ (a i ≤ gridPt hr a t N kpred ∧ gridPt hr a t N kpred ≤ t j) := by
        rw [← mem_gridSupport_iff hr a t N i j kpred]
        simpa [S] using hkpred_nS
      rcases not_and_or.mp this with h | h
      · exact lt_of_not_ge h
      · have hlt : gridPt hr a t N kpred < gridPt hr a t N kmin :=
          gridPt_strictMono hr a t hN hkpred_lt
        linarith [hxkmin.1]
    have hxℓsucc : t j < gridPt hr a t N ℓsucc := by
      have : ¬ (a i ≤ gridPt hr a t N ℓsucc ∧ gridPt hr a t N ℓsucc ≤ t j) := by
        rw [← mem_gridSupport_iff hr a t N i j ℓsucc]
        simpa [S] using hℓsucc_nS
      rcases not_and_or.mp this with h | h
      · have hlt : gridPt hr a t N ℓmax < gridPt hr a t N ℓsucc :=
          gridPt_strictMono hr a t hN hℓsucc_gt
        linarith [hxℓmax.2]
      · exact lt_of_not_ge h
    have hle_kl : kmin ≤ ℓmax := S.min'_le ℓmax hℓmaxS
    have hdiff := gridPt_sub_eq hr a t N hle_kl
    have hcard : S.card = ℓmax.val + 1 - kmin.val := by
      rw [show S = Icc kmin ℓmax from hinter, Fin.card_Icc]
    have hcast_card : (ℓmax.val + 1 - kmin.val : ℕ) = ℓmax.val - kmin.val + 1 := by
      have : kmin.val ≤ ℓmax.val := Fin.val_le_of_le hle_kl
      omega
    have hmd : (S.card : ℝ) * δ =
        (gridPt hr a t N ℓmax - gridPt hr a t N kmin) + δ := by
      rw [hcard, hcast_card, Nat.cast_add, Nat.cast_one, add_mul, one_mul, hdiff]
    have hL : L = t j - a i :=
      max_eq_left (sub_nonneg.mpr (hxkmin.1.trans hxkmin.2))
    have hxkmin_eq : gridPt hr a t N kmin = gridPt hr a t N kpred + δ := by
      have hk : kpred.val + 1 < N + 1 := by
        have : kpred.val + 1 = kmin.val := by
          rw [hkpred_val]
          exact Nat.succ_pred_eq_of_pos hkminpos
        rw [this]
        exact kmin.isLt
      have heq : (⟨kpred.val + 1, hk⟩ : Fin (N + 1)) = kmin := by
        apply Fin.ext
        change kpred.val + 1 = kmin.val
        rw [hkpred_val]
        exact Nat.succ_pred_eq_of_pos hkminpos
      have hpt := gridPt_succ hr a t N kpred hk
      rw [heq] at hpt
      exact hpt
    have hxℓmax_eq : gridPt hr a t N ℓsucc = gridPt hr a t N ℓmax + δ :=
      gridPt_succ hr a t N ℓmax hsucc
    have hup : (S.card : ℝ) * δ - L ≤ δ := by
      rw [hmd, hL]
      linarith [hxℓmax.2, hxkmin.1]
    have hlow : L - (S.card : ℝ) * δ ≤ 2 * δ := by
      rw [hmd, hL]
      linarith [hxkpred, hxℓsucc, hxkmin_eq, hxℓmax_eq]
    rw [abs_le]
    constructor <;> linarith
  · have hm0 : S.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hne)
    have hLnn : 0 ≤ L := le_max_right _ _
    rw [hm0, Nat.cast_zero, zero_mul, zero_sub, abs_neg, abs_of_nonneg hLnn]
    by_cases hta : t j ≤ a i
    · have hL : L = 0 := max_eq_right (sub_nonpos.mpr hta)
      rw [hL]
      exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (gridDelta_nonneg hr a t N)
    · have hlt : a i < t j := not_le.mp hta
      have hL : L = t j - a i := max_eq_left (le_of_lt (sub_pos.mpr hlt))
      let sL : Finset (Fin (N + 1)) :=
        univ.filter (fun k => gridPt hr a t N k < a i)
      have hsLne : sL.Nonempty := ⟨0, by
        simp only [mem_filter, mem_univ, true_and, sL]
        rw [gridPt_zero]
        exact gridXMin_lt_a hr a t i⟩
      have hlastnL : Fin.last N ∉ sL := by
        intro h
        have : gridPt hr a t N (Fin.last N) < a i := (mem_filter.mp h).2
        rw [gridPt_last hr a t hN] at this
        exact (not_lt_of_ge (le_of_lt (hlt.trans (gridXMax_gt_t hr a t j)))) this
      set kstar := sL.max' hsLne
      have hkstar : gridPt hr a t N kstar < a i :=
        (mem_filter.mp (max'_mem sL hsLne)).2
      have hkstarN : kstar ≠ Fin.last N :=
        fun h => hlastnL (h ▸ max'_mem sL hsLne)
      have hkstarltFin : kstar < Fin.last N :=
        lt_of_le_of_ne (Fin.le_last kstar) hkstarN
      have hkstarlt : kstar.val < N := by
        simpa [Fin.lt_def, Fin.val_last] using hkstarltFin
      have hsucc : kstar.val + 1 < N + 1 := Nat.succ_lt_succ hkstarlt
      let knext : Fin (N + 1) := ⟨kstar.val + 1, hsucc⟩
      have hknext_gt : kstar < knext :=
        Fin.lt_def.mpr (by simp [knext])
      have hknext_nL : knext ∉ sL :=
        fun hk => (not_lt_of_ge (sL.le_max' knext hk)) hknext_gt
      have hai_le : a i ≤ gridPt hr a t N knext := by
        have : ¬ gridPt hr a t N knext < a i := by
          simpa [sL, mem_filter] using hknext_nL
        exact le_of_not_gt this
      have hknext_nS : knext ∉ S := fun hk => hne ⟨knext, hk⟩
      have htj_lt : t j < gridPt hr a t N knext := by
        have : ¬ (a i ≤ gridPt hr a t N knext ∧ gridPt hr a t N knext ≤ t j) := by
          rw [← mem_gridSupport_iff hr a t N i j knext]
          simpa [S] using hknext_nS
        rcases not_and_or.mp this with h | h
        · exact (h hai_le).elim
        · exact lt_of_not_ge h
      have hxeq : gridPt hr a t N knext = gridPt hr a t N kstar + δ :=
        gridPt_succ hr a t N kstar hsucc
      rw [hL]
      nlinarith [hkstar, htj_lt, hxeq, gridDelta_nonneg hr a t N]

lemma gridDelta_tendsto {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ) :
    Tendsto (fun n : ℕ => gridDelta hr a t (n + 1)) atTop (nhds 0) :=
  (tendsto_const_div_atTop_nhds_zero_nat (gridXMax hr a t - gridXMin hr a t)).comp
    (tendsto_add_atTop_nat 1)

lemma gridSupport_mul_delta_tendsto {r c : ℕ} (hr : 0 < r)
    (a : Fin r → ℝ) (t : Fin c → ℝ) (i : Fin r) (j : Fin c) :
    Tendsto
      (fun n : ℕ =>
        (gridSupport hr a t (n + 1) i j).card * gridDelta hr a t (n + 1))
      atTop (nhds (max (t j - a i) 0)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have h2δ : Tendsto (fun n : ℕ => (2 : ℝ) * gridDelta hr a t (n + 1)) atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds (x := (2 : ℝ))).mul (gridDelta_tendsto hr a t)
  filter_upwards [Metric.tendsto_nhds.mp h2δ ε hε] with n hn
  have hN : 0 < n + 1 := Nat.succ_pos _
  have hbound := gridSupport_card_mul_delta_sub_le hr a t hN i j
  have hδnn : 0 ≤ gridDelta hr a t (n + 1) := gridDelta_nonneg hr a t (n + 1)
  have hle : dist
      (((gridSupport hr a t (n + 1) i j).card : ℝ) * gridDelta hr a t (n + 1))
      (max (t j - a i) 0) ≤ 2 * gridDelta hr a t (n + 1) := by
    simpa [Real.dist_eq] using hbound
  have hlt : 2 * gridDelta hr a t (n + 1) < ε := by
    simpa [Real.dist_eq, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδnn)] using hn
  exact hle.trans_lt hlt

lemma gridK_tendsto {r c : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (t : Fin c → ℝ)
    (i : Fin r) (j : Fin c) :
    Tendsto (fun n : ℕ => gridK hr a t (n + 1) i j) atTop
      (nhds (2⁻¹ * truncatedSquare a t i j)) := by
  have hδ := gridDelta_tendsto hr a t
  have hm := gridSupport_mul_delta_tendsto hr a t i j
  have hform : ∀ n : ℕ,
      gridK hr a t (n + 1) i j =
        2⁻¹ * ((gridSupport hr a t (n + 1) i j).card * gridDelta hr a t (n + 1)) *
          ((gridSupport hr a t (n + 1) i j).card * gridDelta hr a t (n + 1) +
            gridDelta hr a t (n + 1)) := by
    intro n
    rw [gridK_apply_count]
    ring
  have hlim :
      Tendsto (fun n : ℕ =>
        2⁻¹ * ((gridSupport hr a t (n + 1) i j).card * gridDelta hr a t (n + 1)) *
          ((gridSupport hr a t (n + 1) i j).card * gridDelta hr a t (n + 1) +
            gridDelta hr a t (n + 1)))
        atTop (nhds (2⁻¹ * max (t j - a i) 0 * (max (t j - a i) 0 + 0))) :=
    (tendsto_const_nhds.mul hm).mul (hm.add hδ)
  have heq : 2⁻¹ * max (t j - a i) 0 * (max (t j - a i) 0 + 0) =
      2⁻¹ * truncatedSquare a t i j := by
    simp [truncatedSquare, pow_two]
    ring
  rw [← heq]
  exact hlim.congr fun n => (hform n).symm

lemma isTotallyNonneg_truncatedSquare {r c : ℕ}
    {a : Fin r → ℝ} {t : Fin c → ℝ} (ha : Monotone a) (ht : Monotone t) :
    IsTotallyNonneg (truncatedSquare a t) := by
  intro k I J hI hJ
  cases k with
  | zero =>
    exact (det_eq_one_of_card_eq_zero
      (A := (truncatedSquare a t).submatrix I J) (Fintype.card_fin 0)) ▸
      (zero_le_one : (0 : ℝ) ≤ 1)
  | succ k =>
    have hr : 0 < r := Fin.pos_iff_nonempty.mpr ⟨I 0⟩
    have hK : ∀ n : ℕ, 0 ≤ ((gridK hr a t (n + 1)).submatrix I J).det :=
      fun n => (gridK_isTotallyNonneg hr ha ht (n + 1)) _ I J hI hJ
    have hmat : Tendsto (fun n : ℕ => (gridK hr a t (n + 1)).submatrix I J)
        atTop (nhds ((2⁻¹ : ℝ) • (truncatedSquare a t).submatrix I J)) := by
      refine (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_)
      simpa [submatrix_apply, Pi.smul_apply, smul_eq_mul] using
        gridK_tendsto hr a t (I i) (J j)
    have hdet :
        Tendsto (fun n : ℕ => ((gridK hr a t (n + 1)).submatrix I J).det)
          atTop (nhds (((2⁻¹ : ℝ) • (truncatedSquare a t).submatrix I J).det)) :=
      ((continuous_id (X := Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)).matrix_det.tendsto _).comp
        hmat
    have hlim : 0 ≤ ((2⁻¹ : ℝ) • (truncatedSquare a t).submatrix I J).det :=
      ge_of_tendsto hdet (Eventually.of_forall hK)
    have hpow : 0 < (2⁻¹ : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
    rw [det_smul, Fintype.card_fin] at hlim
    exact (mul_nonneg_iff_of_pos_left hpow).mp hlim

end

end BollobasNikiforov
