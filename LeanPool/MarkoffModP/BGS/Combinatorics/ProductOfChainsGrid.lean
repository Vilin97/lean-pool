/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.Tactic

/-!
# Symmetric chains in a rectangle

This is the explicit de Bruijn--Tengbergen--Kruyswijk rectangle decomposition
used in the product-of-chains proof.  A point `(x,y)` in
`[0,m] × [0,n]` is encoded by a chain key and a position on that chain.
The decoder is inverse to the encoder, preserves rank, and is monotone along
each chain.
-/

@[expose] public section

namespace BGS.Combinatorics

/-- Key of the L-shaped symmetric chain containing `(x,y)`. -/
def gridKey (m n x y : ℕ) : ℕ :=
  if m ≤ n then min y (m - x) else min x (n - y)

/-- Position of `(x,y)` along its rectangle chain. -/
def gridPosition (m n x y : ℕ) : ℕ :=
  x + y - gridKey m n x y

/-- First coordinate of the point at position `t` on chain `k`. -/
def gridDecodeX (m n k t : ℕ) : ℕ :=
  if m ≤ n then
    if t ≤ m - k then t else m - k
  else
    if t ≤ n - k then k else t + 2 * k - n

/-- Second coordinate of the point at position `t` on chain `k`. -/
def gridDecodeY (m n k t : ℕ) : ℕ :=
  if m ≤ n then
    if t ≤ m - k then k else t + 2 * k - m
  else
    if t ≤ n - k then t else n - k

theorem gridKey_le_min
    {m n x y : ℕ} (hx : x ≤ m) (hy : y ≤ n) :
    gridKey m n x y ≤ min m n := by
  by_cases hmn : m ≤ n
  · rw [gridKey, ite_eq_left hmn]
    apply le_min
    · exact (min_le_right _ _).trans (Nat.sub_le _ _)
    · exact (min_le_left _ _).trans hy
  · rw [gridKey, ite_eq_right hmn]
    apply le_min
    · exact (min_le_left _ _).trans hx
    · exact (min_le_right _ _).trans (Nat.sub_le _ _)

theorem gridPosition_le
    {m n x y : ℕ} (hx : x ≤ m) (hy : y ≤ n) :
    gridPosition m n x y ≤
      m + n - 2 * gridKey m n x y := by
  by_cases hmn : m ≤ n
  · by_cases hshort : y ≤ m - x
    · simp [gridPosition, gridKey, hmn, min_eq_left hshort]
      omega
    · have hreverse : m - x ≤ y := Nat.le_of_not_ge hshort
      simp [gridPosition, gridKey, hmn, min_eq_right hreverse]
      omega
  · have hnm : n ≤ m := Nat.le_of_not_ge hmn
    by_cases hshort : x ≤ n - y
    · simp [gridPosition, gridKey, hmn, min_eq_left hshort]
      omega
    · have hreverse : n - y ≤ x := Nat.le_of_not_ge hshort
      simp [gridPosition, gridKey, hmn, min_eq_right hreverse]
      omega

theorem gridDecodeX_le
    {m n k t : ℕ} (hk : k ≤ min m n)
    (ht : t ≤ m + n - 2 * k) :
    gridDecodeX m n k t ≤ m := by
  have hkm : k ≤ m := hk.trans (min_le_left _ _)
  have hkn : k ≤ n := hk.trans (min_le_right _ _)
  by_cases hmn : m ≤ n
  · by_cases hpos : t ≤ m - k
    · simp [gridDecodeX, hmn, hpos]
      omega
    · simp [gridDecodeX, hmn, hpos]
  · by_cases hpos : t ≤ n - k
    · simp [gridDecodeX, hmn, hpos]
      omega
    · simp [gridDecodeX, hmn, hpos]
      omega

theorem gridDecodeY_le
    {m n k t : ℕ} (hk : k ≤ min m n)
    (ht : t ≤ m + n - 2 * k) :
    gridDecodeY m n k t ≤ n := by
  have hkm : k ≤ m := hk.trans (min_le_left _ _)
  have hkn : k ≤ n := hk.trans (min_le_right _ _)
  by_cases hmn : m ≤ n
  · by_cases hpos : t ≤ m - k
    · simp [gridDecodeY, hmn, hpos]
      omega
    · simp [gridDecodeY, hmn, hpos]
      omega
  · by_cases hpos : t ≤ n - k
    · simp [gridDecodeY, hmn, hpos]
      omega
    · simp [gridDecodeY, hmn, hpos]

theorem gridKey_decode
    {m n k t : ℕ} (hk : k ≤ min m n)
    (_ht : t ≤ m + n - 2 * k) :
    gridKey m n (gridDecodeX m n k t)
        (gridDecodeY m n k t) = k := by
  have hkm : k ≤ m := hk.trans (min_le_left _ _)
  have hkn : k ≤ n := hk.trans (min_le_right _ _)
  by_cases hmn : m ≤ n
  · by_cases hpos : t ≤ m - k
    · have hkSub : k ≤ m - t := by omega
      simp [gridKey, gridDecodeX, gridDecodeY, hmn, hpos,
        min_eq_left hkSub]
    · have hkY : k ≤ t + 2 * k - m := by omega
      simp [gridKey, gridDecodeX, gridDecodeY, hmn, hpos,
        Nat.sub_sub_self hkm, min_eq_right hkY]
  · by_cases hpos : t ≤ n - k
    · have hkSub : k ≤ n - t := by omega
      simp [gridKey, gridDecodeX, gridDecodeY, hmn, hpos,
        min_eq_left hkSub]
    · have hkX : k ≤ t + 2 * k - n := by omega
      simp [gridKey, gridDecodeX, gridDecodeY, hmn, hpos,
        Nat.sub_sub_self hkn, min_eq_right hkX]

theorem gridDecode_rank
    {m n k t : ℕ} (hk : k ≤ min m n)
    (_ht : t ≤ m + n - 2 * k) :
    gridDecodeX m n k t + gridDecodeY m n k t = k + t := by
  have hkm : k ≤ m := hk.trans (min_le_left _ _)
  have hkn : k ≤ n := hk.trans (min_le_right _ _)
  by_cases hmn : m ≤ n
  · by_cases hpos : t ≤ m - k
    · simp [gridDecodeX, gridDecodeY, hmn, hpos]
      omega
    · simp [gridDecodeX, gridDecodeY, hmn, hpos]
      omega
  · by_cases hpos : t ≤ n - k
    · simp [gridDecodeX, gridDecodeY, hmn, hpos]
    · simp [gridDecodeX, gridDecodeY, hmn, hpos]
      omega

theorem gridPosition_decode
    {m n k t : ℕ} (hk : k ≤ min m n)
    (ht : t ≤ m + n - 2 * k) :
    gridPosition m n (gridDecodeX m n k t)
        (gridDecodeY m n k t) = t := by
  rw [gridPosition, gridKey_decode hk ht, gridDecode_rank hk ht]
  omega

theorem gridDecode_encode_x
    {m n x y : ℕ} (hx : x ≤ m) (hy : y ≤ n) :
    gridDecodeX m n (gridKey m n x y)
      (gridPosition m n x y) = x := by
  by_cases hmn : m ≤ n
  · by_cases hshort : y ≤ m - x
    · have hdecode : x ≤ m - y := by omega
      simp [gridDecodeX, gridPosition, gridKey, hmn,
        min_eq_left hshort, hdecode]
    · have hreverse : m - x ≤ y := Nat.le_of_not_ge hshort
      have hdecode :
          ¬x + y - (m - x) ≤ m - (m - x) := by
        rw [Nat.sub_sub_self hx]
        omega
      simp [gridDecodeX, gridPosition, gridKey, hmn, hshort,
        min_eq_right hreverse,  Nat.sub_sub_self hx]
  · by_cases hshort : x ≤ n - y
    · have hdecode : y ≤ n - x := by omega
      simp [gridDecodeX, gridPosition, gridKey, hmn,
        min_eq_left hshort, hdecode]
    · have hreverse : n - y ≤ x := Nat.le_of_not_ge hshort
      have hdecode :
          ¬x + y - (n - y) ≤ n - (n - y) := by
        rw [Nat.sub_sub_self hy]
        omega
      have hsum : ¬x + y ≤ y + (n - y) := by omega
      simp [gridDecodeX, gridPosition, gridKey, hmn,
        min_eq_right hreverse,  hsum, Nat.sub_sub_self hy]
      omega

theorem gridDecode_encode_y
    {m n x y : ℕ} (hx : x ≤ m) (hy : y ≤ n) :
    gridDecodeY m n (gridKey m n x y)
      (gridPosition m n x y) = y := by
  by_cases hmn : m ≤ n
  · by_cases hshort : y ≤ m - x
    · have hdecode : x ≤ m - y := by omega
      simp [gridDecodeY, gridPosition, gridKey, hmn,
        min_eq_left hshort, hdecode]
    · have hreverse : m - x ≤ y := Nat.le_of_not_ge hshort
      have hdecode :
          ¬x + y - (m - x) ≤ m - (m - x) := by
        rw [Nat.sub_sub_self hx]
        omega
      simp [gridDecodeY, gridPosition, gridKey, hmn, hshort,
        min_eq_right hreverse,  Nat.sub_sub_self hx]
      omega
  · by_cases hshort : x ≤ n - y
    · have hdecode : y ≤ n - x := by omega
      simp [gridDecodeY, gridPosition, gridKey, hmn,
        min_eq_left hshort, hdecode]
    · have hreverse : n - y ≤ x := Nat.le_of_not_ge hshort
      have hdecode :
          ¬x + y - (n - y) ≤ n - (n - y) := by
        rw [Nat.sub_sub_self hy]
        omega
      simp [gridDecodeY, gridPosition, gridKey, hmn,
        min_eq_right hreverse,  Nat.sub_sub_self hy]
      omega

theorem gridDecode_mono
    {m n k t₁ t₂ : ℕ} (_hk : k ≤ min m n)
    (_ht₁ : t₁ ≤ m + n - 2 * k)
    (_ht₂ : t₂ ≤ m + n - 2 * k)
    (h : t₁ ≤ t₂) :
    gridDecodeX m n k t₁ ≤ gridDecodeX m n k t₂ ∧
      gridDecodeY m n k t₁ ≤ gridDecodeY m n k t₂ := by
  by_cases hmn : m ≤ n
  · by_cases hpos₁ : t₁ ≤ m - k <;>
      by_cases hpos₂ : t₂ ≤ m - k <;>
        simp [gridDecodeX, gridDecodeY, hmn, hpos₁, hpos₂] <;>
        omega
  · by_cases hpos₁ : t₁ ≤ n - k <;>
      by_cases hpos₂ : t₂ ≤ n - k <;>
        simp [gridDecodeX, gridDecodeY, hmn, hpos₁, hpos₂] <;>
        omega

end BGS.Combinatorics
