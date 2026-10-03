/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Profiles

/-! The pieces of `psiL` and `phiL` (the proof notes, §8.5).

In the variable `u = 1/x` (for a prime, `u = n/p`), the relaxed range `(1/20, 7/3]` of `x` is
the range
`[3/7, 20)` of `u`, cut at the points `m + α` (`m ∈ ℕ`, `α ∈ {0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5,
2/3, 3/4, 4/5}`)
into 196 half-open pieces `[ub i, ub (i+1))`. On the piece with `⌊u⌋ = m` and `{u}` in the
`k`-th cell,
`psiL x = cellA k m + cellB k m · x − 25/(4x)` (the ten parametric formulas, proved once for all
`m`).
The outer range `(7/3, 5]` of `x` is `[1/5, 3/7)` in `u`, four pieces on which `phiL` is linear.
The tail `x ≤ 1/20` is handled by the global bound `psiL x ≤ 33/5 + (121/100) x`. -/

public section

namespace Zeta32.ArithSum
noncomputable section

/-! ### The cells of `[0,1]` and the ten formulas -/

/-- Breakpoints of the cells of `[0, 1]` (partition by `j/3, j/4, j/5`). -/
@[expose]
def alphaQ : ℕ → ℚ
  | 0 => 0 | 1 => 1/5 | 2 => 1/4 | 3 => 1/3 | 4 => 2/5 | 5 => 1/2 | 6 => 3/5 | 7 => 2/3
  | 8 => 3/4 | 9 => 4/5 | _ => 1

/-- Constant coefficient on cell `k` (with `m = ⌊1/x⌋`). -/
@[expose]
def cellA : ℕ → ℚ → ℚ
  | 0, m => (62*m+49)/4 | 1, m => (62*m+7)/4 | 2, m => (62*m+39)/4 | 3, m => (62*m+63)/4
  | 4, m => (62*m+21)/4 | 5, m => (62*m+53)/4 | 6, m => (62*m+11)/4 | 7, m => (62*m+35)/4
  | 8, m => (62*m+67)/4 | _, m => (62*m+25)/4

/-- Coefficient of `x` on cell `k`. -/
@[expose]
def cellB : ℕ → ℚ → ℚ
  | 0, m => -(m*(37*m+25))/4 | 1, m => -(37*m^2-5*m-6)/4 | 2, m => -(37*m^2+27*m+2)/4
  | 3, m => -(37*m^2+51*m+10)/4 | 4, m => -(37*m^2+21*m-2)/4 | 5, m => -(37*m^2+53*m+14)/4
  | 6, m => -(37*m^2+23*m-4)/4 | 7, m => -(37*m^2+47*m+12)/4 | 8, m => -(37*m^2+79*m+36)/4
  | _, m => -((m+1)*(37*m+12))/4

lemma fract_eq_sub (y : ℝ) (z : ℤ) (h1 : (z : ℝ) ≤ y) (h2 : y < z + 1) :
    Int.fract y = y - z := by
  rw [Int.fract_eq_iff]
  exact ⟨by linarith, by linarith, z, by ring⟩

/-- `psiL` in terms of the three fractional parts (definitional unfolding). -/
lemma psiL_eq (x : ℝ) : psiL x =
    6 + x * Int.fract (3/x) * (1 - Int.fract (3/x)) - 3 * (4 * Int.fract (1/x) - Int.fract (5/x)) +
      x / 4 * (16 * Int.fract (1/x) + Int.fract (5/x) - 8 * min (Int.fract (1/x)) (Int.fract
        (5/x)) -
        (4 * Int.fract (1/x) - Int.fract (5/x)) ^ 2) := rfl

/-- The ten parametric formulas: on the cell `k` of the unit interval, shifted by `m`. -/
theorem psiL_cell (k : ℕ) (hk : k < 10) (m : ℕ) {x : ℝ} (hx : 0 < x)
    (h1 : (m : ℝ) + (alphaQ k : ℝ) ≤ 1 / x) (h2 : 1 / x < (m : ℝ) + (alphaQ (k + 1) : ℝ)) :
    psiL x = (cellA k m : ℝ) + (cellB k m : ℝ) * x - 25 / (4 * x) := by
  have h5 : 5 / x = 5 * (1 / x) := by ring
  have h3 : 3 / x = 3 * (1 / x) := by ring
  rw [psiL_eq, h5, h3]
  interval_cases k <;> simp only [alphaQ, Nat.reduceAdd] at h1 h2 <;> push_cast at h1 h2
  · -- cell 0: α ∈ [0, 1/5)
    rw [fract_eq_sub (1 / x) (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * (1 / x)) (5 * m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * (1 / x)) (3 * m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_left (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    field_simp
    ring
  · -- cell 1: α ∈ [1/5, 1/4)
    rw [fract_eq_sub (1 / x) (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * (1 / x)) (5 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * (1 / x)) (3 * m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_right (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    field_simp
    ring
  · -- cell 2: α ∈ [1/4, 1/3)
    rw [fract_eq_sub (1 / x) (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * (1 / x)) (5 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * (1 / x)) (3 * m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_left (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    field_simp
    ring
  · -- cell 3: α ∈ [1/3, 2/5)
    rw [fract_eq_sub (1 / x) (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * (1 / x)) (5 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * (1 / x)) (3 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_left (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    field_simp
    ring
  · -- cell 4: α ∈ [2/5, 1/2)
    rw [fract_eq_sub (1 / x) (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * (1 / x)) (5 * m + 2 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * (1 / x)) (3 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_right (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    field_simp
    ring
  · -- cell 5: α ∈ [1/2, 3/5)
    rw [fract_eq_sub (1 / x) (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * (1 / x)) (5 * m + 2 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * (1 / x)) (3 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_left (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    field_simp
    ring
  · -- cell 6: α ∈ [3/5, 2/3)
    rw [fract_eq_sub (1 / x) (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * (1 / x)) (5 * m + 3 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * (1 / x)) (3 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_right (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    field_simp
    ring
  · -- cell 7: α ∈ [2/3, 3/4)
    rw [fract_eq_sub (1 / x) (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * (1 / x)) (5 * m + 3 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * (1 / x)) (3 * m + 2 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_right (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    field_simp
    ring
  · -- cell 8: α ∈ [3/4, 4/5)
    rw [fract_eq_sub (1 / x) (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * (1 / x)) (5 * m + 3 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * (1 / x)) (3 * m + 2 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_left (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    field_simp
    ring
  · -- cell 9: α ∈ [4/5, 1)
    rw [fract_eq_sub (1 / x) (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * (1 / x)) (5 * m + 4 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * (1 / x)) (3 * m + 2 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_right (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    field_simp
    ring

/-! ### The 196 pieces of the relaxed range, indexed flatly -/

/-- Integer part `m` of piece `i` (pieces `0..5` have `m = 0`, cells `4..9`). -/
@[expose]
def pm (i : ℕ) : ℕ := if i < 6 then 0 else (i - 6) / 10 + 1
/-- Cell `k` of piece `i`. -/
@[expose]
def pk (i : ℕ) : ℕ := if i < 6 then i + 4 else (i - 6) % 10
/-- Left endpoint (in `u = 1/x`) of piece `i`; piece `0` starts at `3/7` inside cell `4`. -/
@[expose]
def ub (i : ℕ) : ℚ := if i = 0 then 3/7 else (pm i : ℚ) + alphaQ (pk i)
/-- Coefficients of piece `i`: `psiL x = pa i + pb i · x − 25/(4x)`. -/
@[expose]
def pa (i : ℕ) : ℚ := cellA (pk i) (pm i)
/-- Constant term of the affine arithmetic-profile cell selected by `i`. -/
@[expose]
def pb (i : ℕ) : ℚ := cellB (pk i) (pm i)

lemma pk_lt (i : ℕ) : pk i < 10 := by
  unfold pk; split_ifs <;> omega

lemma pm_pk_succ (i : ℕ) :
    (pk i < 9 ∧ pm (i + 1) = pm i ∧ pk (i + 1) = pk i + 1) ∨
      (pk i = 9 ∧ pm (i + 1) = pm i + 1 ∧ pk (i + 1) = 0) := by
  unfold pm pk
  split_ifs <;> omega

lemma ub_succ (i : ℕ) : ub (i + 1) = (pm i : ℚ) + alphaQ (pk i + 1) := by
  simp only [ub, Nat.add_one_ne_zero, ↓reduceIte]
  rcases pm_pk_succ i with ⟨_, h1, h2⟩ | ⟨h0, h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, h0]
    simp only [alphaQ]
    push_cast
    ring

lemma ub_ge (i : ℕ) : (pm i : ℚ) + alphaQ (pk i) ≤ ub i := by
  unfold ub
  split_ifs with h
  · subst h; simp [pm, pk, alphaQ]; norm_num
  · exact le_rfl

lemma alphaQ_lt (k : ℕ) (hk : k < 10) : alphaQ k < alphaQ (k + 1) := by
  interval_cases k <;> simp only [alphaQ] <;> norm_num

lemma ub_lt_succ (i : ℕ) : ub i < ub (i + 1) := by
  rw [ub_succ]
  have h := alphaQ_lt (pk i) (pk_lt i)
  unfold ub
  split_ifs with h0
  · subst h0; simp only [pm, pk, alphaQ]; norm_num
  · linarith

lemma ub_zero : ub 0 = 3/7 := rfl

lemma ub_196 : ub 196 = 20 := by
  simp only [ub, pm, pk, alphaQ]; norm_num

lemma ub_pos (i : ℕ) : 0 < ub i := by
  induction i with
  | zero => rw [ub_zero]; norm_num
  | succ i ih => exact ih.trans (ub_lt_succ i)

/-- On piece `i` (for every `i`, in particular the 196 pieces of `[3/7, 20)`), `psiL` is given by
the formula of its cell. -/
theorem psiL_piece (i : ℕ) {x : ℝ} (hx : 0 < x) (h1 : (ub i : ℝ) ≤ 1 / x)
    (h2 : 1 / x < (ub (i + 1) : ℝ)) :
    psiL x = (pa i : ℝ) + (pb i : ℝ) * x - 25 / (4 * x) := by
  have hge : ((pm i : ℚ) + alphaQ (pk i) : ℚ) ≤ ub i := ub_ge i
  have hge' : ((pm i : ℝ) + (alphaQ (pk i) : ℝ)) ≤ (ub i : ℝ) := by exact_mod_cast hge
  have hs : ((ub (i + 1) : ℚ) : ℝ) = (pm i : ℝ) + (alphaQ (pk i + 1) : ℝ) := by
    rw [ub_succ]; push_cast; ring
  rw [hs] at h2
  unfold pa pb
  exact psiL_cell (pk i) (pk_lt i) (pm i) hx (hge'.trans h1) h2

/-! ### The four pieces of the outer range (`7/3 < x ≤ 5`, i.e. `1/5 ≤ u < 3/7`) -/

/-- Rational breakpoints for the reciprocal outer-prime profile. -/
@[expose]
def vb : ℕ → ℚ
  | 0 => 1/5 | 1 => 1/4 | 2 => 1/3 | 3 => 2/5 | _ => 3/7
/-- Constant terms of the affine pieces of the reciprocal outer-prime profile. -/
@[expose]
def vc : ℕ → ℚ
  | 0 => 2 | 1 => 18 | 2 => 24 | _ => 6
/-- Slopes of the affine pieces of the reciprocal outer-prime profile. -/
@[expose]
def vd : ℕ → ℚ
  | 0 => -1 | 1 => -5 | 2 => -7 | _ => -1

lemma vb_lt_succ (i : ℕ) (hi : i < 4) : vb i < vb (i + 1) := by
  interval_cases i <;> simp only [vb] <;> norm_num

theorem phiL_piece (i : ℕ) (hi : i < 4) {x : ℝ} (hx : 0 < x) (h1 : (vb i : ℝ) ≤ 1 / x)
    (h2 : 1 / x < (vb (i + 1) : ℝ)) :
    phiL x = (vc i : ℝ) + (vd i : ℝ) * x := by
  have key : ∀ c : ℝ, 0 < c → (c ≤ 1 / x ↔ x ≤ 1 / c) := fun c hc => by
    rw [le_div_iff₀ hx, le_div_iff₀ hc, mul_comm]
  have key2 : ∀ c : ℝ, 0 < c → (1 / x < c ↔ 1 / c < x) := fun c hc => by
    rw [div_lt_iff₀ hx, div_lt_iff₀ hc, mul_comm]
  unfold phiL
  interval_cases i <;> simp only [vb, vc, vd, Nat.reduceAdd] at h1 h2 ⊢ <;> push_cast at h1 h2 ⊢
  · rw [key _ (by norm_num)] at h1; rw [key2 _ (by norm_num)] at h2
    norm_num at h1 h2
    split_ifs <;> first | (exfalso; linarith) | ring1
  · rw [key _ (by norm_num)] at h1; rw [key2 _ (by norm_num)] at h2
    norm_num at h1 h2
    split_ifs <;> first | (exfalso; linarith) | ring1
  · rw [key _ (by norm_num)] at h1; rw [key2 _ (by norm_num)] at h2
    norm_num at h1 h2
    split_ifs <;> first | (exfalso; linarith) | ring1
  · rw [key _ (by norm_num)] at h1; rw [key2 _ (by norm_num)] at h2
    norm_num at h1 h2
    split_ifs <;> first | (exfalso; linarith) | ring1

/-! ### The tail bound -/

lemma quad_bound (a b : ℝ) (j : ℤ) (hj : 5 * a - b = j) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    16 * a + b - 8 * min a b - (4 * a - b) ^ 2 ≤ 96 / 25 ∧ -3 * (4 * a - b) ≤ 3 / 5 := by
  have hj0 : (-1 : ℝ) < j := by rw [← hj]; linarith
  have hj5 : (j : ℝ) < 5 := by rw [← hj]; linarith
  have hj0' : -1 < j := by exact_mod_cast hj0
  have hj5' : j < 5 := by exact_mod_cast hj5
  have hb : b = 5 * a - j := by linarith
  subst hb
  interval_cases j <;> push_cast at hb0 hb1 ⊢ <;>
    rcases le_total a (5 * a - _) with hab | hab <;>
    first
    | (rw [min_eq_left hab]; constructor <;> nlinarith)
    | (rw [min_eq_right hab]; constructor <;> nlinarith)

/-- `psiL x ≤ 33/5 + (121/100) x` for every `x > 0` (used for `x ≤ 1/20`). -/
theorem psiL_le_tail {x : ℝ} (hx : 0 < x) : psiL x ≤ 33 / 5 + 121 / 100 * x := by
  rw [psiL_eq]
  set a := Int.fract (1 / x) with ha
  set b := Int.fract (5 / x) with hb
  set g := Int.fract (3 / x) with hg
  have hj : 5 * a - b = ((⌊5 / x⌋ - 5 * ⌊1 / x⌋ : ℤ) : ℝ) := by
    rw [ha, hb, Int.fract, Int.fract]
    push_cast
    have : 5 / x = 5 * (1 / x) := by ring
    rw [this]; ring
  obtain ⟨h1, h2⟩ := quad_bound a b _ hj (Int.fract_nonneg _) (Int.fract_lt_one _)
    (Int.fract_nonneg _) (Int.fract_lt_one _)
  have hg1 : g * (1 - g) ≤ 1 / 4 := by nlinarith [sq_nonneg (g - 1 / 2)]
  have hsum : g * (1 - g) + (16 * a + b - 8 * min a b - (4 * a - b) ^ 2) / 4 ≤ 121 / 100 := by
    linarith
  have := mul_le_mul_of_nonneg_left hsum hx.le
  nlinarith [this]

end
end Zeta32.ArithSum

end
