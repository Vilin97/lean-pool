/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.BasisChange
public import LeanPool.Zeta5Irrational.Arith.BinomBasis
public import LeanPool.Zeta5Irrational.Arith.Val
import LeanPool.Zeta5Irrational.Arith.SmallPrime
import LeanPool.Zeta5Irrational.Arith.SmallPrimeTau
import LeanPool.Zeta5Irrational.PartialFractions
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Small primes: the bound (3.12)

`v_p^G(F_K) ≥ -6h ⌊log_p (5K)⌋ - h v_p(24)` for every prime `p` (`small_prime_bound`), via the
basis `q_0 = 1`, `q_i(t) = (-1)^i 2t D_{i-1}(t)/(2i)!` with `q_i(-z²) = C(z+i, 2i) + C(z+i-1, 2i)`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

/-- The basis `q_a`. -/
noncomputable def qP (a : ℕ) : ℚ[X] :=
  if a = 0 then 1 else C ((-1 : ℚ) ^ a * 2 / ((2 * a).factorial : ℚ)) * (X * D (a - 1))

/-- Its leading coefficient. -/
noncomputable def qlead (a : ℕ) : ℚ :=
  if a = 0 then 1 else (-1 : ℚ) ^ a * 2 / ((2 * a).factorial : ℚ)

lemma qlead_ne_zero (a : ℕ) : qlead a ≠ 0 := by
  unfold qlead; split_ifs
  · norm_num
  · have : ((2 * a).factorial : ℚ) ≠ 0 := by positivity
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num)) this

lemma qP_eq (a : ℕ) : qP a = C (qlead a) * (if a = 0 then 1 else X * D (a - 1)) := by
  unfold qP qlead; split_ifs <;> simp

lemma monic_qbase (a : ℕ) : (if a = 0 then (1 : ℚ[X]) else X * D (a - 1)).Monic := by
  split_ifs
  · exact monic_one
  · exact monic_X.mul (D_monic _)

lemma natDegree_qbase (a : ℕ) : (if a = 0 then (1 : ℚ[X]) else X * D (a - 1)).natDegree = a := by
  split_ifs with h
  · simp [h]
  · rw [natDegree_mul X_ne_zero (D_monic _).ne_zero, natDegree_X, natDegree_D]; omega

lemma natDegree_qP (a : ℕ) : (qP a).natDegree = a := by
  rw [qP_eq, natDegree_C_mul (qlead_ne_zero a), natDegree_qbase]

lemma coeff_qP_self (a : ℕ) : (qP a).coeff a = qlead a := by
  rw [qP_eq, coeff_C_mul]
  have := (monic_qbase a).coeff_natDegree
  rw [natDegree_qbase] at this
  rw [this, mul_one]

/-! ### Integer values -/

lemma prod_Icc_eq_prod_range (N : ℕ) (g : ℕ → ℚ) :
    ∏ j ∈ Icc 1 N, g j = ∏ i ∈ range N, g (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

lemma bin_eval_eq (k : ℕ) (y : ℚ) :
    (bin k).eval y = (∏ i ∈ range k, (y - i)) / (k.factorial : ℚ) := by
  unfold bin
  rw [eval_mul, eval_C, descPochhammer_eval_eq_prod_range]
  ring

/-- `∏_{i < 2c+1} (z + c - i) = z ∏_{j ≤ c} (z² - j²)`. -/
lemma prod_window (z : ℚ) (c : ℕ) :
    ∏ i ∈ range (2 * c + 1), (z + c - i) = z * ∏ j ∈ Icc 1 c, (z ^ 2 - (j : ℚ) ^ 2) := by
  induction c with
  | zero => simp
  | succ c
    ih =>
    rw [show 2 * (c + 1) + 1 = (2 * c + 1) + 1 + 1 by ring, Finset.prod_range_succ',
      Finset.prod_range_succ]
    have e :
      ∏ i ∈ range (2 * c + 1), (z + ((c + 1 : ℕ) : ℚ) - ((i + 1 : ℕ) : ℚ)) =
        ∏ i ∈ range (2 * c + 1), (z + c - i) :=
      by refine Finset.prod_congr rfl fun i _ => ?_; push_cast; ring
    rw [e, ih, Finset.prod_Icc_succ_top (by omega)]
    push_cast; ring

/-- `q_a(-z²) = C(z+a, 2a) + C(z+a-1, 2a)` for `a ≥ 1`. -/
lemma qP_eval_neg_sq {a : ℕ} (ha : 1 ≤ a) (z : ℚ) :
    (qP a).eval (-z ^ 2) = (bin (2 * a)).eval (z + a) + (bin (2 * a)).eval (z + a - 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  rw [qP, ite_eq_right (by omega), bin_eval_eq, bin_eval_eq, show c + 1 - 1 = c by omega]
  rw [eval_mul, eval_C, eval_mul, eval_X]
  unfold D
  rw [eval_prod]
  simp only [eval_add, eval_X, eval_C]
  have h1 :
    ∏ i ∈ range (2 * (c + 1)), (z + ((c + 1 : ℕ) : ℚ) - i) =
      (z + ((c + 1 : ℕ) : ℚ)) * (z * ∏ j ∈ Icc 1 c, (z ^ 2 - (j : ℚ) ^ 2)) := by
    rw [show 2 * (c + 1) = (2 * c + 1) + 1 by ring, Finset.prod_range_succ']
    have e :
      ∏ i ∈ range (2 * c + 1), (z + ((c + 1 : ℕ) : ℚ) - ((i + 1 : ℕ) : ℚ)) =
        ∏ i ∈ range (2 * c + 1), (z + c - i) :=
      by refine Finset.prod_congr rfl fun i _ => ?_; push_cast; ring
    rw [e, prod_window]; push_cast; ring
  have h2 :
    ∏ i ∈ range (2 * (c + 1)), (z + ((c + 1 : ℕ) : ℚ) - 1 - i) =
      (z * ∏ j ∈ Icc 1 c, (z ^ 2 - (j : ℚ) ^ 2)) * (z - ((c + 1 : ℕ) : ℚ)) := by
    rw [show 2 * (c + 1) = (2 * c + 1) + 1 by ring, Finset.prod_range_succ]
    have e :
      ∏ i ∈ range (2 * c + 1), (z + ((c + 1 : ℕ) : ℚ) - 1 - (i : ℚ)) =
        ∏ i ∈ range (2 * c + 1), (z + c - i) :=
      by refine Finset.prod_congr rfl fun i _ => ?_; push_cast; ring
    rw [e, prod_window]; push_cast; ring
  rw [h1, h2]
  have h3 :
    ∏ j ∈ Icc 1 c, (-z ^ 2 + (j : ℚ) ^ 2) = (-1) ^ c * ∏ j ∈ Icc 1 c, (z ^ 2 - (j : ℚ) ^ 2) := by
    rw [show ((-1 : ℚ) ^ c) = ∏ _j ∈ Icc 1 c, (-1 : ℚ) by
        rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel],
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_; ring
  rw [h3]
  have hf : ((2 * (c + 1)).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  have hc : (-1 : ℚ) ^ (c * 2) = 1 := Even.neg_one_pow ⟨c, by ring⟩
  linear_combination (2 * z ^ 2 * ∏ j ∈ Icc 1 c, (z ^ 2 - (j : ℚ) ^ 2)) * hc

lemma VG_qP_eval (a : ℕ) (z : ℤ) : VG p ((qP a).eval (-(z : ℚ) ^ 2)) 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [qP, ↓reduceIte, eval_one]; exact VG.one
  · rw [qP_eval_neg_sq ha]
    refine VG.add ?_ ?_
    · have := VG_bin_eval_int (p := p) (2 * a) (z + a); push_cast at this; exact this
    · have := VG_bin_eval_int (p := p) (2 * a) (z + a - 1); push_cast at this; exact this

/-- `D_N(-z²) = (N!)² C(N+z, N) C(N-z, N)`. -/
lemma D_eval_neg_sq (N : ℕ) (z : ℚ) :
    (D N).eval (-z ^ 2) = (N.factorial : ℚ) ^ 2 * ((bin N).eval (N + z) * (bin N).eval (N - z)) :=
  by
  rw [bin_eval_eq, bin_eval_eq]
  unfold D
  rw [eval_prod]
  simp only [eval_add, eval_X, eval_C]
  have hf : (N.factorial : ℚ) ≠ 0 := by positivity
  have r1 : ∏ i ∈ range N, ((N : ℚ) + z - i) = ∏ i ∈ range N, (z + ((i + 1 : ℕ) : ℚ)) := by
    rw [← Finset.prod_range_reflect (fun i => z + ((i + 1 : ℕ) : ℚ)) N]
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    push_cast [show i ≤ N - 1 by omega, show 1 ≤ N by omega]; ring
  have r2 : ∏ i ∈ range N, ((N : ℚ) - z - i) = ∏ i ∈ range N, (((i + 1 : ℕ) : ℚ) - z) := by
    rw [← Finset.prod_range_reflect (fun i => ((i + 1 : ℕ) : ℚ) - z) N]
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    push_cast [show i ≤ N - 1 by omega, show 1 ≤ N by omega]; ring
  rw [r1, r2, prod_Icc_eq_prod_range N (fun j => -z ^ 2 + (j : ℚ) ^ 2)]
  field_simp
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

lemma VG_D_eval (N : ℕ) (z : ℤ) : VG p ((D N).eval (-(z : ℚ) ^ 2) / (N.factorial : ℚ) ^ 2) 0 := by
  have hf : (N.factorial : ℚ) ≠ 0 := by positivity
  rw [D_eval_neg_sq, mul_div_cancel_left₀ _ (pow_ne_zero _ hf)]
  have h1 := VG_bin_eval_int (p := p) N (N + z)
  have h2 := VG_bin_eval_int (p := p) N (N - z)
  push_cast at h1 h2
  simpa using h1.mul h2

/-! ### Assembly -/

lemma det_coeffMat_qP (h : ℕ) : (coeffMat (fun a : Fin h => qP a)).det = ∏ a : Fin h, qlead a := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_congr rfl fun a _ => ?_
    simp only [coeffMat, Matrix.of_apply]
    exact coeff_qP_self a
  · intro i j hij
    simp only [coeffMat, Matrix.of_apply]
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_qP]
    exact hij

lemma qlead_sq {a : ℕ} (ha : 1 ≤ a) : qlead a ^ 2 = 4 / (((2 * a).factorial : ℚ) ^ 2) := by
  unfold qlead
  rw [ite_eq_right (by omega), div_pow, mul_pow, ← pow_mul, show a * 2 = 2 * a by ring, pow_mul]
  norm_num

lemma prod_qlead_sq (h : ℕ) (hh : 1 ≤ h) :
    (∏ a : Fin h, qlead a) ^ 2 =
      4 ^ (h - 1) / ∏ i ∈ Icc 1 (h - 1), (((2 * i).factorial : ℚ) ^ 2) := by
  rw [← Finset.prod_pow, Fin.prod_univ_eq_prod_range (fun a => qlead a ^ 2) h]
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  rw [Finset.prod_range_succ', show qlead 0 = 1 by simp [qlead], one_pow, mul_one, ←
    prod_Icc_eq_prod_range h' (fun a => qlead a ^ 2), Nat.add_sub_cancel]
  rw [Finset.prod_congr rfl (fun i hi => qlead_sq (Finset.mem_Icc.mp hi).1),
    Finset.prod_div_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]

/-- `S_K = ((K!)²/(N!)¹²)^h det(C)²`. -/
lemma S_eq_qlead (n : ℕ) (hn : 1 ≤ n) :
    S n =
      (((40 * n).factorial : ℚ) ^ 2 / ((3 * n).factorial : ℚ) ^ 12) ^ (37 * n) *
        (∏ a : Fin (37 * n), qlead a) ^ 2 := by
  rw [prod_qlead_sq _ (by omega)]
  unfold S
  have h1 : ((3 * n).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ∏ i ∈ Icc 1 (37 * n - 1), (((2 * i).factorial : ℚ) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
  rw [div_pow, ← pow_mul, ← pow_mul, show 12 * (37 * n) = 12 * (37 * n) by rfl]
  field_simp

/-- **The bound (3.12)** at every prime. -/
theorem small_prime_bound {n : ℕ} (hn : 1 ≤ n) :
    GV p (F n)
      (-(6 * (37 * n : ℕ) * (Nat.log p (200 * n) : ℚ) + (37 * n : ℕ) * padicValNat p 24)) := by
  set h := 37 * n with hh
  set K := 40 * n with hK
  set N := 3 * n with hN
  set E : Fin h → ℚ[X] := fun a => qP a with hE
  have hEdeg : ∀ a, (E a).natDegree < h := fun a => by
    rw [hE]; simp only; rw [natDegree_qP];
    exact a.isLt
  have hbc := det_basis_change n E hEdeg
  set c : ℚ := (K.factorial : ℚ) ^ 2 / (N.factorial : ℚ) ^ 12 with hc
  set M := Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b) with hM
  have hF : F n = ((C c) • M).det := by
    rw [Matrix.det_smul, hbc, Fintype.card_fin, F, S_eq_qlead n hn, det_coeffMat_qP]
    simp only [map_mul, map_pow]
    ring
  rw [hF]
  set d := 5 + 12 * N + 4 * (h - 1) with hd
  set Λ : ℚ := (Nat.log p (200 * n) : ℚ) with hΛ
  have hd1 : d + 1 ≤ 200 * n := by omega
  have hdK : 2 * K ≤ d := by omega
  have hentry :
    ∀ a b : Fin h,
      GV p (((C c) • M) a b)
        ((-3 * Λ - padicValNat p 24 / 2) + (-3 * Λ - padicValNat p 24 / 2)) := by
    intro a b
    rw [Matrix.smul_apply, hM, Matrix.of_apply, smul_eq_mul, ← μX_C_mul, μX_eq_tauX]
    set Q := D (3 * n) ^ 6 * E a * E b with hQ
    set A : ℚ[X] := C ((-1 : ℚ) ^ K / (N.factorial : ℚ) ^ 12) * X ^ 5 * Q.comp (-X ^ 2) with hA
    have hpull : pull (40 * n) (C c * Q) = C ((K.factorial : ℚ) ^ 2) * A := by
      have e1 : C c = C ((K.factorial : ℚ) ^ 2) * C (1 / (N.factorial : ℚ) ^ 12) := by
        rw [← C_mul]; congr 1; rw [hc]; ring
      have e2 :
        C ((-1 : ℚ) ^ K / (N.factorial : ℚ) ^ 12) =
          C ((-1 : ℚ) ^ (40 * n)) * C (1 / (N.factorial : ℚ) ^ 12) :=
        by rw [← C_mul]; congr 1; rw [hK]; ring
      rw [pull, hA, mul_comp, C_comp, e1, e2]; ring
    rw [hpull]
    have hQdeg : Q.natDegree ≤ 6 * N + 2 * (h - 1) := by
      rw [hQ]
      refine (natDegree_mul_le).trans ?_
      have h1 : (D (3 * n) ^ 6 * E a).natDegree ≤ 6 * N + a := by
        refine (natDegree_mul_le).trans ?_
        rw [natDegree_pow, natDegree_D, hE]; simp only; rw [natDegree_qP]
      have h2 : (E b).natDegree ≤ b := by rw [hE]; simp only; rw [natDegree_qP]
      have := a.isLt; have := b.isLt
      omega
    have hAdeg : A.natDegree ≤ d := by
      rw [hA]
      refine (natDegree_mul_le).trans ?_
      have h1 : (C ((-1 : ℚ) ^ K / (N.factorial : ℚ) ^ 12) * X ^ 5 : ℚ[X]).natDegree ≤ 5 :=
        (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow])
      have h2 : (Q.comp (-X ^ 2 : ℚ[X])).natDegree ≤ 2 * (6 * N + 2 * (h - 1)) := by
        rw [natDegree_comp]
        have : (-X ^ 2 : ℚ[X]).natDegree = 2 := by rw [natDegree_neg, natDegree_X_pow]
        rw [this]; linarith
      omega
    have hAint : ∀ z : ℤ, VG p (A.eval (z : ℚ)) 0 := by
      intro z
      have e :
        A.eval (z : ℚ) =
          (-1 : ℚ) ^ K * (z : ℚ) ^ 5 * ((D N).eval (-(z : ℚ) ^ 2) / (N.factorial : ℚ) ^ 2) ^ 6 *
              (qP a).eval (-(z : ℚ) ^ 2) *
            (qP b).eval (-(z : ℚ) ^ 2) := by
        rw [hA, hQ, hE]
        simp only [eval_mul, eval_C, eval_pow, eval_X, eval_comp, eval_neg]
        have : (N.factorial : ℚ) ≠ 0 := by positivity
        field_simp
        rw [hN]; ring
      rw [e]
      have hs : VG p ((-1 : ℚ) ^ K) 0 := by
        rcases neg_one_pow_eq_or ℚ K with h | h <;> rw [h]
        · exact VG.one
        · exact VG.one.neg
      have hz : VG p ((z : ℚ) ^ 5) 0 := by simpa using (VG.intCast (p := p) z).pow 5
      have :=
        (((hs.mul hz).mul ((VG_D_eval (p := p) N z).pow 6)).mul (VG_qP_eval (p := p) a z)).mul
          (VG_qP_eval (p := p) b z)
      simpa using this
    have hb := crude_tauX (p := p) (K := K) (d := d) (by omega) hdK A hAdeg hAint
    refine hb.mono ?_
    have : (Nat.log p (d + 1) : ℚ) ≤ Λ := log_mono hd1
    linarith
  have hdet :=
    det_GV _ (fun _ => -3 * Λ - padicValNat p 24 / 2) (fun _ => -3 * Λ - padicValNat p 24 / 2)
      hentry
  refine hdet.mono ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

end Zeta5Irrational
