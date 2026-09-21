/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import LeanPool.GranvilleMoore.CoefficientAnalysis
public import LeanPool.GranvilleMoore.Defs.TheMooreDeterminant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The reduction ladder

The determinant half of the argument about the Moore determinant: the ladder
`L 0, L 1, …, L (d-1)` of `ladderMatrix` starts at the Moore matrix, each rung costs one
power `p ^ C(d - i, 2)` of `p`, and the total cost is `p ^ C(d + 1, 3)`.

## Main results

* `GranvilleMoore.iteratedFermatQuot_sub_iteratedFermatQuot`: the row difference identity
  `F⁽ᵃ⁾_(b+1)(x) - F⁽ᵃ⁾_b(x) = p^(b+1) F⁽ᵃ⁺¹⁾_b(x)`.
* `GranvilleMoore.ladderMatrix_zero`: `L 0` is the Moore matrix, viewed over `ℚ`.
* `GranvilleMoore.ladderMatrix_last_apply`: every row of `L (d-1)` sits at subscript `0`.
* `GranvilleMoore.det_ladderMatrix_step`: one rung, `det (L i) = p^C(d-i,2) det (L (i+1))`.
* `GranvilleMoore.det_mooreMatrix_eq_pow_mul_det_ladderMatrix`: the factorisation
  `det M = p^C(d+1,3) det (L (d-1))`.

## Implementation notes

The row operations of one rung run for `b = d-2-i` down to `0`, so that each row is modified only
after it has served as the subtrahend. The bookkeeping is carried here by
`GranvilleMoore.ladderStep p x i m`, the matrix in which exactly the rows at index `≥ m + i + 1`
have already been replaced; `ladderStep p x i (d-1-i)` is `L i`, one determinant-preserving row
operation takes `ladderStep p x i (m+1)` to `ladderStep p x i m`, and `ladderStep p x i 0` is a row
rescaling of `L (i+1)`. Making the *set* of finished rows explicit is what removes the need to
reason about the order of the operations at all: each single step is a `Matrix.updateRow` whose
subtrahend row is visibly untouched.

The `d - 1 - i` scalars are extracted in one go with `Matrix.det_mul_column` (which scales
rows, despite the name) rather than by `Matrix.det_updateRow_smul` once per row.

None of the results below needs the bounds `d ≥ 2` and `i ≤ d - 2`: for `d ≤ i + 1` the ladder has
stabilised, `L i = L (i+1)`, and `C(d-i,2) = 0`, so one rung is an identity there too. Only `p ≠ 0`
is genuinely needed, to divide in the recursion for `iteratedFermatQuot`.

## References

* A. Granville, *The p-divisibility of the integer Moore determinant and iterated
  Fermat quotients*.
-/

@[expose] public section

open Finset Matrix

namespace GranvilleMoore

variable {d : ℕ}

/-! ### The row difference identity -/

/-- **The row difference identity** (`lem_row_difference`): the recursion defining
`iteratedFermatQuot`, cleared of its denominator. Raising the subscript by one changes
`F⁽ᵃ⁾` by `p^(b+1)` times the next `F⁽ᵃ⁺¹⁾`. -/
theorem iteratedFermatQuot_sub_iteratedFermatQuot {p : ℕ} (hp : p ≠ 0) (a b : ℕ) (x : ℤ) :
    iteratedFermatQuot p a (b + 1) x - iteratedFermatQuot p a b x
      = (p : ℚ) ^ (b + 1) * iteratedFermatQuot p (a + 1) b x := by
  have hp' : (p : ℚ) ^ (b + 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp)
  rw [iteratedFermatQuot_succ, mul_div_cancel₀ _ hp']

/-! ### The two ends of the ladder -/

/-- **The ladder starts at the Moore matrix** (`lem_ladder_start`): the rows of `L 0` are
`F⁽⁰⁾_0, …, F⁽⁰⁾_(d-1)`, and `F⁽⁰⁾_k(x) = x^(p^k)` is the Moore matrix entry. The
comparison is stated over `ℚ`, where the ladder lives, so the integer Moore matrix appears
through its entrywise image. -/
theorem ladderMatrix_zero (p : ℕ) (x : Fin d → ℤ) :
    ladderMatrix p x 0 = (mooreMatrix p x).map (fun z : ℤ => (z : ℚ)) := by
  ext r j
  simp

/-- **Entries of the last ladder matrix** (`lem_ladder_last_entries`): at the last rung the
trailing block of growing subscripts is empty, so the row at index `r` of `L (d-1)` is
`F⁽ʳ⁾_0`. -/
theorem ladderMatrix_last_apply (p : ℕ) (x : Fin d → ℤ) (r j : Fin d) :
    ladderMatrix p x (d - 1) r j = iteratedFermatQuot p (r : ℕ) 0 (x j) := by
  have hr : (r : ℕ) ≤ d - 1 := by have := r.isLt; omega
  rw [ladderMatrix_apply, min_eq_left hr, Nat.sub_eq_zero_of_le hr]

/-! ### The row operations of one rung -/

/-- The matrix interpolating between `ladderMatrix p x i` and its rescaled successor: the
rows at index `r ≥ m + i + 1` have already been replaced by `p^(r-i) • F⁽ⁱ⁺¹⁾_(r-i-1)` by
the row operations of one rung, and the remaining rows are still those of `L i`.

Recording the finished rows by a *threshold* `m` is what makes that decreasing-`b` order automatic:
in `ladderStep p x i (m+1)` the two rows involved in the next operation, at indices `m + i` and
`m + i + 1`, are both still original. -/
private def ladderStep (p : ℕ) (x : Fin d → ℤ) (i m : ℕ) : Matrix (Fin d) (Fin d) ℚ :=
  Matrix.of fun r j =>
    if m + i + 1 ≤ (r : ℕ) then
      (p : ℚ) ^ ((r : ℕ) - i) * iteratedFermatQuot p (i + 1) ((r : ℕ) - i - 1) (x j)
    else ladderMatrix p x i r j

private theorem ladderStep_apply (p : ℕ) (x : Fin d → ℤ) (i m : ℕ) (r j : Fin d) :
    ladderStep p x i m r j =
      if m + i + 1 ≤ (r : ℕ) then
        (p : ℚ) ^ ((r : ℕ) - i) * iteratedFermatQuot p (i + 1) ((r : ℕ) - i - 1) (x j)
      else ladderMatrix p x i r j :=
  rfl

/-- At the threshold `m = d - 1 - i` no row has been touched: this is `L i` itself. -/
private theorem ladderStep_top (p : ℕ) (x : Fin d → ℤ) (i : ℕ) :
    ladderStep p x i (d - 1 - i) = ladderMatrix p x i := by
  ext r j
  have := r.isLt
  rw [ladderStep_apply, ite_eq_right (by omega)]

/-- One row operation, with the two row indices supplied abstractly: subtracting the row at
index `m + i` from the row at index `m + i + 1` lowers the threshold from `m + 1` to `m`
and leaves the determinant unchanged. -/
private theorem det_ladderStep_succ_aux {p : ℕ} (hp : p ≠ 0) (x : Fin d → ℤ) (i m : ℕ)
    (r₀ r₁ : Fin d) (h₀ : (r₀ : ℕ) = m + i + 1) (h₁ : (r₁ : ℕ) = m + i) :
    (ladderStep p x i m).det = (ladderStep p x i (m + 1)).det := by
  have hne : r₀ ≠ r₁ := by
    intro hh
    rw [hh, h₁] at h₀
    omega
  have key : ladderStep p x i m
      = Matrix.updateRow (ladderStep p x i (m + 1)) r₀
          (ladderStep p x i (m + 1) r₀ + (-1 : ℚ) • ladderStep p x i (m + 1) r₁) := by
    ext r j
    by_cases hr : r = r₀
    · rw [hr, Matrix.updateRow_self]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ladderStep_apply,
        ladderMatrix_apply]
      rw [ite_eq_left (show m + i + 1 ≤ (r₀ : ℕ) by omega),
        ite_eq_right (show ¬m + 1 + i + 1 ≤ (r₀ : ℕ) by omega),
        ite_eq_right (show ¬m + 1 + i + 1 ≤ (r₁ : ℕ) by omega),
        min_eq_right (show i ≤ (r₀ : ℕ) by omega),
        min_eq_right (show i ≤ (r₁ : ℕ) by omega),
        show (r₀ : ℕ) - i - 1 = m by omega, show (r₀ : ℕ) - i = m + 1 by omega,
        show (r₁ : ℕ) - i = m by omega]
      linear_combination -iteratedFermatQuot_sub_iteratedFermatQuot hp i m (x j)
    · have hrv : (r : ℕ) ≠ m + i + 1 := fun hh => hr (Fin.val_injective (by omega))
      rw [Matrix.updateRow_ne hr]
      simp only [ladderStep_apply]
      exact if_congr (by omega) rfl rfl
  rw [key]
  exact Matrix.det_updateRow_add_smul_self _ hne _

/-- One row operation: lowering the threshold by one leaves the determinant unchanged. -/
private theorem det_ladderStep_succ {p : ℕ} (hp : p ≠ 0) (x : Fin d → ℤ) (i m : ℕ)
    (h : m + i + 2 ≤ d) :
    (ladderStep p x i m).det = (ladderStep p x i (m + 1)).det :=
  det_ladderStep_succ_aux hp x i m ⟨m + i + 1, by omega⟩ ⟨m + i, by omega⟩ rfl rfl

/-- All the row operations of one rung together: every threshold up to `d - 1 - i` gives
the same determinant as the fully reduced matrix. -/
private theorem det_ladderStep_zero {p : ℕ} (hp : p ≠ 0) (x : Fin d → ℤ) (i m : ℕ)
    (hm : m ≤ d - 1 - i) :
    (ladderStep p x i 0).det = (ladderStep p x i m).det := by
  induction m with
  | zero => rfl
  | succ n ih => rw [ih (by omega), det_ladderStep_succ hp x i n (by omega)]

/-! ### The scalars extracted from one rung -/

/-- The product of the scalars `p^(r-i)` extracted from the rows `r ≥ i + 1`. The exponent
`∑_{r=i+1}^{n-1} (r - i) = ∑_{c=1}^{n-1-i} c` is `C(n-i, 2)`. -/
private theorem prod_range_ite_pow (p i n : ℕ) :
    ∏ r ∈ range n, (if i + 1 ≤ r then (p : ℚ) ^ (r - i) else 1)
      = (p : ℚ) ^ Nat.choose (n - i) 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    by_cases hn : i + 1 ≤ n
    · have he : Nat.choose (n + 1 - i) 2 = (n - i) + Nat.choose (n - i) 2 := by
        rw [show n + 1 - i = (n - i) + 1 by omega, Nat.choose_succ_succ (n - i) 1,
          Nat.choose_one_right]
      rw [ite_eq_left hn, he, pow_add, mul_comm]
    · have he : Nat.choose (n + 1 - i) 2 = Nat.choose (n - i) 2 := by
        rw [Nat.choose_eq_zero_of_lt (show n + 1 - i < 2 by omega),
          Nat.choose_eq_zero_of_lt (show n - i < 2 by omega)]
      rw [ite_eq_right hn, mul_one, he]

/-- The fully reduced matrix of one rung is `L (i+1)` with its last `d - 1 - i` rows scaled
by `p^(r-i)`, so its determinant is `p^C(d-i,2)` times that of `L (i+1)`. -/
private theorem det_ladderStep_zero_eq (p : ℕ) (x : Fin d → ℤ) (i : ℕ) :
    (ladderStep p x i 0).det
      = (p : ℚ) ^ Nat.choose (d - i) 2 * (ladderMatrix p x (i + 1)).det := by
  have key : ladderStep p x i 0
      = Matrix.of fun (r j : Fin d) =>
          (if i + 1 ≤ (r : ℕ) then (p : ℚ) ^ ((r : ℕ) - i) else 1)
            * ladderMatrix p x (i + 1) r j := by
    ext r j
    simp only [ladderStep_apply, Matrix.of_apply, ladderMatrix_apply, Nat.zero_add]
    by_cases hr : i + 1 ≤ (r : ℕ)
    · rw [ite_eq_left hr, ite_eq_left hr, min_eq_right hr, Nat.sub_sub]
    · rw [ite_eq_right hr, ite_eq_right hr, one_mul,
        min_eq_left (show (r : ℕ) ≤ i by omega),
        min_eq_left (show (r : ℕ) ≤ i + 1 by omega),
        Nat.sub_eq_zero_of_le (show (r : ℕ) ≤ i by omega),
        Nat.sub_eq_zero_of_le (show (r : ℕ) ≤ i + 1 by omega)]
  rw [key, Matrix.det_mul_column, ← Finset.prod_range
    (fun r => if i + 1 ≤ r then (p : ℚ) ^ (r - i) else 1), prod_range_ite_pow]

/-! ### One rung of the ladder -/

/-- **One rung of the ladder** (`lem_ladder_step`): passing from `L i` to `L (i+1)` costs
exactly `p^C(d-i,2)`.

This is usually stated for `d ≥ 2` and `i ≤ d - 2`; no such bound is needed, since for
`d ≤ i + 1` both sides read `det (L i) = det (L i)`. -/
theorem det_ladderMatrix_step {p : ℕ} (hp : p ≠ 0) (x : Fin d → ℤ) (i : ℕ) :
    (ladderMatrix p x i).det
      = (p : ℚ) ^ Nat.choose (d - i) 2 * (ladderMatrix p x (i + 1)).det := by
  rw [← ladderStep_top p x i, ← det_ladderStep_zero hp x i (d - 1 - i) le_rfl,
    det_ladderStep_zero_eq]

/-! ### Factoring the Moore determinant -/

/-- Iterating one rung: `det (L 0) = p^(∑_{i<n} C(d-i,2)) det (L n)`. -/
private theorem det_ladderMatrix_zero_eq {p : ℕ} (hp : p ≠ 0) (x : Fin d → ℤ) (n : ℕ) :
    (ladderMatrix p x 0).det
      = (p : ℚ) ^ (∑ i ∈ range n, Nat.choose (d - i) 2) * (ladderMatrix p x n).det := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, det_ladderMatrix_step hp x n, Finset.sum_range_succ, pow_add]
    ring

/-- **The ladder exponent** (`lem_ladder_exponent`): `∑_{i<n-1} C(n-i,2) = C(n+1,3)`.

This is the total power of `p` that the ladder extracts: rung `i` contributes `C(n-i,2)`. It
follows from the hockey stick `GranvilleMoore.sum_range_choose_two` by the re-indexing `c = n - i`;
the two terms `C(1,2)` and `C(0,2)` that the reflected range adds both vanish. -/
theorem sum_range_sub_choose_two (n : ℕ) :
    ∑ i ∈ range (n - 1), Nat.choose (n - i) 2 = Nat.choose (n + 1) 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
    have hflip := Finset.sum_flip (n := t + 1) fun c => Nat.choose c 2
    rw [sum_range_choose_two] at hflip
    have e1 : t + 1 - t = 1 := by omega
    have e2 : t + 1 - (t + 1) = 0 := by omega
    have c1 : Nat.choose 1 2 = 0 := rfl
    have c0 : Nat.choose 0 2 = 0 := rfl
    rw [Finset.sum_range_succ, Finset.sum_range_succ, e1, e2, c1, c0] at hflip
    simpa using hflip

/-- **Factoring the Moore determinant** (`lem_det_factor`): the Moore determinant is
`p^C(d+1,3)` times the determinant of the last matrix of the ladder.

`ladderMatrix_zero` identifies `L 0` with the Moore matrix over `ℚ`, `det_ladderMatrix_step`
supplies the `d - 1` rungs, and the exponents add up to `C(d+1,3)` by
`sum_range_choose_two`. For `d = 0` and `d = 1` there are no rungs and the exponent is `0`,
so the identity is an equality of the two ends. -/
theorem det_mooreMatrix_eq_pow_mul_det_ladderMatrix {p : ℕ} (hp : p ≠ 0) (x : Fin d → ℤ) :
    ((mooreMatrix p x).det : ℚ)
      = (p : ℚ) ^ Nat.choose (d + 1) 3 * (ladderMatrix p x (d - 1)).det := by
  have hmap : ((mooreMatrix p x).det : ℚ) = (ladderMatrix p x 0).det := by
    rw [ladderMatrix_zero]
    simpa [RingHom.mapMatrix_apply] using RingHom.map_det (Int.castRingHom ℚ) (mooreMatrix p x)
  rw [hmap, det_ladderMatrix_zero_eq hp x (d - 1), sum_range_sub_choose_two]

end GranvilleMoore
