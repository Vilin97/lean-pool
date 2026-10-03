/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Outer.Raw

/-! Bookkeeping for the proof notes section 8.2: the exact valuation of the normalizer
`S_n^{3n}/F_n`
(Legendre with one level, `5n < p²`), the row product `∏ rowScale = p^{5n+1-p}`, and the sum of
the class
bounds over all classes. `normScale_val` and the floor sums are adapted from
dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/
DecayMediumClosed.lean and MediumFloorSum.lean (layout `2n, 4n, 3` there, `3n, 5n, 4` here). -/

public section

open Zeta32.Arith.Local

open Polynomial
open scoped BigOperators
namespace Zeta32.Outer
noncomputable section

/-! ## The normalizer -/

-- adapted from Li2Unified/Modular/Base/DecayMediumClosed.lean
lemma padicValRat_prod_range (p : ℕ) [Fact p.Prime] (f : ℕ → ℚ) (hf : ∀ i, f i ≠ 0) (N : ℕ) :
    padicValRat p (∏ i ∈ Finset.range N, f i) = ∑ i ∈ Finset.range N, padicValRat p (f i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ,
      padicValRat.mul (Finset.prod_ne_zero_iff.mpr fun i _ => hf i) (hf N), ih]

/-- Prime-valuation normalization term for the scaled determinant. -/
def normVal (p n : ℕ) : ℚ :=
  3 * (n:ℚ) * (((5*n)/p : ℕ) - 4 * ((n/p : ℕ) : ℚ)) -
    2 * ∑ i ∈ Finset.range (3*n), ((i/p : ℕ) : ℚ)

-- adapted from Li2Unified/Modular/Base/DecayMediumClosed.lean (`normScale_val`)
theorem scale_val (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (hK : 5 * n < p ^ 2) :
    padicValRat p (scale n) = normVal p n := by
  have hf : ∀ m : ℕ, (m.factorial : ℚ) ≠ 0 := fun m => by positivity
  have hS : Sn n ≠ 0 := (Sn_pos n).ne'
  have hF : Fn n ≠ 0 := (Fn_pos n).ne'
  rw [scale, padicValRat.div (pow_ne_zero _ hS) hF, padicValRat.pow, Sn,
    padicValRat.div (hf _) (pow_ne_zero _ (hf _)), padicValRat.pow,
    padicValRat_factorial_small hK, padicValRat_factorial_small (by omega : n < p^2)]
  have hFv : padicValRat p (Fn n) = 2 * ∑ i ∈ Finset.range (3*n), ((i/p : ℕ) : ℤ) := by
    unfold Fn
    rw [padicValRat_prod_range p _ (fun i => pow_ne_zero _ (hf i)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [padicValRat.pow, padicValRat_factorial_small (by
      have := Finset.mem_range.mp hi; omega)]
    ring
  rw [hFv, normVal]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Int.cast_sum,
    Nat.cast_mul, Nat.cast_ofNat]

lemma scale_VG (p : ℕ) [Fact p.Prime] {n : ℕ} (hK : 5 * n < p ^ 2) :
    VG p (scale n) (normVal p n) :=
  VG.of_eq _ fun _ => by rw [scale_val p hK]

/-- For `3n < 2p` the floor sum `Σ_{i<3n} ⌊i/p⌋` is `(3n - p)₊`. -/
lemma floor_sum_small {p n : ℕ} (hp : 0 < p) (h : 3 * n < 2 * p) :
    ∑ i ∈ Finset.range (3*n), ((i/p : ℕ) : ℚ) = ((3*n - p : ℕ) : ℚ) := by
  by_cases h1 : 3*n ≤ p
  · rw [Nat.sub_eq_zero_of_le h1, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro i hi
    have := Finset.mem_range.mp hi
    rw [Nat.div_eq_of_lt (by omega), Nat.cast_zero]
  · rw [show 3*n = p + (3*n - p) by omega, Finset.sum_range_add]
    have e1 : ∑ i ∈ Finset.range p, ((i/p : ℕ) : ℚ) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Nat.div_eq_of_lt (Finset.mem_range.mp hi), Nat.cast_zero]
    have e2 : ∑ i ∈ Finset.range (3*n - p), (((p + i)/p : ℕ) : ℚ) = ((3*n - p : ℕ) : ℚ) := by
      rw [show ((3*n - p : ℕ) : ℚ) = ∑ _i ∈ Finset.range (3*n - p), (1:ℚ) by simp]
      apply Finset.sum_congr rfl
      intro i hi
      have := Finset.mem_range.mp hi
      rw [show p + i = i + p*1 by ring, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega)]
      norm_num
    rw [e1, e2, zero_add, show p + (3*n - p) - p = 3*n - p by omega]

/-! ## The row product -/

lemma rowScale_prod {n p : ℕ} (h1 : 2 * n + 1 ≤ p) (h2 : p ≤ 5 * n + 1) :
    ∏ a : Fin (3*n), rowScale n p a = (p:ℚ)^(5*n + 1 - p) := by
  rw [Fin.prod_univ_eq_prod_range (fun a => rowScale n p a),
    ← Finset.prod_range_mul_prod_Ico _ (show p - 2*n - 1 ≤ 3*n by omega)]
  have e1 : ∏ a ∈ Finset.range (p - 2*n - 1), rowScale n p a = 1 := by
    apply Finset.prod_eq_one
    intro a ha
    have := Finset.mem_range.mp ha
    unfold rowScale
    rw [ite_eq_left (by omega)]
  have e2 : ∏ a ∈ Finset.Ico (p - 2*n - 1) (3*n), rowScale n p a = (p:ℚ)^(5*n + 1 - p) := by
    rw [Finset.prod_congr rfl (g := fun _ => (p:ℚ)), Finset.prod_const, Nat.card_Ico]
    · congr 1; omega
    · intro a ha
      have := (Finset.mem_Ico.mp ha).1
      unfold rowScale
      rw [ite_eq_right (by omega)]
  rw [e1, e2, one_mul]

/-! ## Summing the class bounds -/

lemma sum_range_ite_lt (N r : ℕ) :
    ∑ c ∈ Finset.range N, (if c < r then (1:ℚ) else 0) = ((min N r : ℕ) : ℚ) := by
  rw [Finset.sum_boole]
  congr 1
  have : (Finset.range N).filter (fun c => c < r) = Finset.range (min N r) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

/-- The per-class lower bound of `Classes.lean`. -/
def gcl (n p c : ℕ) : ℚ :=
  if c + 1 = p then -4 else if c < n then -(if c < 5*n - 2*p then 1 else 0)
  else -4 * (if c < 5*n - p then 1 else 0)

lemma Scl_ge_gcl {n p c : ℕ} (h73 : 7 * n < 3 * p) (hp5 : p ≤ 5 * n) (hc : c < p) :
    gcl n p c ≤ Scl n p c := by
  unfold gcl
  by_cases h1 : c + 1 = p
  · rw [ite_eq_left h1]; exact Scl_zero h73 hp5 h1
  · rw [ite_eq_right h1]
    by_cases h2 : c < n
    · rw [ite_eq_left h2]; exact Scl_low h73 (by omega)
    · rw [ite_eq_right h2]; exact Scl_high h73 hp5 (by omega) (by omega)

lemma sum_gcl {n p : ℕ} (h73 : 7 * n < 3 * p) (hp5 : p ≤ 5 * n) :
    ∑ c : Fin p, gcl n p c =
      -4 - ((5*n - 2*p : ℕ) : ℚ) - 4 * ((min (p - 1 - n) (5*n - p - n) : ℕ) : ℚ) := by
  rw [Fin.sum_univ_eq_sum_range (fun c => gcl n p c)]
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  rw [Finset.sum_range_succ, show p' = n + (p' - n) by omega, Finset.sum_range_add]
  have e0 : gcl n (n + (p' - n) + 1) (n + (p' - n)) = -4 := by
    unfold gcl; rw [ite_eq_left rfl]
  have e1 : ∑ c ∈ Finset.range n, gcl n (n + (p' - n) + 1) c =
      -((5*n - 2*(n + (p' - n) + 1) : ℕ) : ℚ) := by
    rw [Finset.sum_congr rfl (g := fun c => -(if c < 5*n - 2*(n + (p' - n) + 1) then (1:ℚ) else 0)),
      Finset.sum_neg_distrib, sum_range_ite_lt, show min n (5*n - 2*(n + (p' - n) + 1)) =
        5*n - 2*(n + (p' - n) + 1) by omega]
    intro c hc
    have := Finset.mem_range.mp hc
    unfold gcl
    rw [ite_eq_right (by omega), ite_eq_left this]
  have e2 : ∑ i ∈ Finset.range (p' - n), gcl n (n + (p' - n) + 1) (n + i) =
      -4 * ((min (n + (p' - n) + 1 - 1 - n) (5*n - (n + (p' - n) + 1) - n) : ℕ) : ℚ) := by
    rw [Finset.sum_congr rfl (g := fun i => -4 * (if i < 5*n - (n + (p' - n) + 1) - n then (1:ℚ)
      else 0)),
      ← Finset.mul_sum, sum_range_ite_lt, show n + (p' - n) + 1 - 1 - n = p' - n by omega]
    intro i hi
    have := Finset.mem_range.mp hi
    unfold gcl
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    congr 1
    by_cases h : i < 5*n - (n + (p' - n) + 1) - n
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]
  rw [e0, e1, e2]
  ring

end
end Zeta32.Outer

end
