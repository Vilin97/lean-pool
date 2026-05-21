/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FinCases

variable {R : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

noncomputable def ofVec (v : Fin m → R) : R[X] :=
  ∑ i, C (v i) * X^(i : ℕ)

@[simp] lemma coeff_ofVec (v : Fin m → R) (i : ℕ) :
    (ofVec v).coeff i = if hi : i < m then v ⟨i, hi⟩ else 0 := by
  simp only [ofVec, finset_sum_coeff]
  split_ifs with hi
  · simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single ⟨i, hi⟩, if_pos rfl]
    · intro b _ hb
      exact if_neg (fun hi => hb (by simp [hi]))
    · simp
  · simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    convert Finset.sum_const_zero
    rw [if_neg]
    rintro rfl
    exact hi (Fin.prop _)

@[simp] lemma ofVec_one {v : Fin 1 → R} : ofVec v = C (v 0) := by
  ext i
  cases i
  · simp
  · simp

@[simp] lemma natDegree_ofVec {v : Fin (m + 1) → R} (h : v (Fin.last _) ≠ 0) :
    natDegree (ofVec v) = m := by
  by_cases hm : m = 0
  · subst hm
    simp
  rw [ofVec, Fin.sum_univ_castSucc, natDegree_add_eq_right_of_natDegree_lt, natDegree_C_mul_X_pow,
      Fin.val_last]
  · assumption
  · refine (natDegree_sum_le _ _).trans_lt ?_
    rw [natDegree_C_mul_X_pow _ _ h, Fin.val_last, Finset.fold_max_lt]
    refine ⟨Nat.pos_iff_ne_zero.mpr hm, fun i _ => (natDegree_C_mul_X_pow_le _ _).trans_lt ?_⟩
    exact i.prop

@[simp] lemma ofVec_smul (v : Fin m → R) (x : R) : ofVec (x • v) = x • ofVec v := by
  ext i
  rw [coeff_ofVec, coeff_smul, coeff_ofVec]
  split_ifs <;> simp

@[simp] lemma ofVec_const_mul (v : Fin m → R) (x : R) : ofVec (fun i => x * v i) =
    C x * ofVec v := by
  ext i
  rw [coeff_ofVec, coeff_C_mul, coeff_ofVec]
  split_ifs <;> simp

def toVec (n : ℕ) (P : R[X]) : Fin n → R
  | ⟨i, _⟩ => P.coeff i

@[simp] lemma toVec_mk (P : R[X]) (i : ℕ) (hi : i < n) :
  P.toVec n ⟨i, hi⟩ = P.coeff i := rfl

@[simp] lemma toVec_C' [NeZero n] (x : R) : toVec n (C x) = fun i => if i.1 = 0 then x else 0 := by
  ext ⟨i, _⟩
  simp [toVec_mk, coeff_C]

lemma toVec_C (x : R) : toVec 1 (C x) = fun _ => x := by
  ext ⟨i, hi⟩
  rcases hi with (_ | ⟨⟨⟩⟩)
  rw [toVec_mk, coeff_C_zero]

@[simp] lemma toVec_X : toVec 2 (X : R[X]) = ![0, 1] := by
  ext ⟨i, hi⟩
  rcases hi with (_ | ⟨_ | ⟨⟨⟩⟩⟩)
  · simp [toVec]
  · rw [toVec_mk, coeff_X_zero]
    simp

@[simp] lemma toVec_add (p q : R[X]) : toVec n (p + q) = toVec n p + toVec n q := by
  ext
  simp [toVec]

@[simp] lemma toVec_X_add_C (x : R) : toVec 2 (X + C x) = ![x, 1] := by
  rw [toVec_add, toVec_X, toVec_C']
  ext i
  fin_cases i <;> simp

@[simp] lemma toVec_C_mul [NoZeroDivisors R] (x : R) (P : R[X]) :
    toVec n (C x * P) = (x • toVec n P) := by
  ext ⟨_, _⟩
  simp

@[simp] lemma ofVec_toVec (f : R[X]) :
    ofVec (toVec (f.natDegree + 1) f) = f := by
  ext i
  simp only [coeff_ofVec]
  split_ifs with h
  · simp
  · rw [coeff_eq_zero_of_natDegree_lt (not_lt.mp h)]

@[simp] lemma toVec_map {S : Type*} [CommRing S] (φ : R →+* S) (f : R[X]) :
    toVec n (map φ f) = φ ∘ toVec n f := by
  ext i
  simp [toVec]

@[simp] lemma toVec_last (f : R[X]) :
    toVec (f.natDegree + 1) f (Fin.last _) = f.leadingCoeff := by
  simp [toVec]

@[simp] lemma toVec_ofVec (v : Fin (m + 1) → R) (h : v (Fin.last m) ≠ 0) :
    toVec _ (ofVec v) = v ∘ Fin.cast (congr_arg (· + 1) (natDegree_ofVec h)) := by
  ext ⟨i, hi⟩
  rw [natDegree_ofVec h] at hi
  simp [toVec, hi]

@[simp] lemma toVec_ofVec' (v : Fin (m + 1) → R) : toVec _ (ofVec v) = v := by
  ext ⟨i, hi⟩
  simp [toVec, hi]

@[simp] lemma toVec_X_pow : toVec (n + 1) (X ^ n : R[X]) = Pi.single (Fin.last _) 1 := by
  ext i
  simp only [toVec, coeff_X_pow]
  split_ifs with hi
  · rw [show i = Fin.last _ by ext; simp [hi], Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne]
    rintro rfl
    simp at hi

end Semiring

section Ring

variable [Ring R]

@[simp] lemma toVec_X_sub_one_pow {m n : ℕ} :
    toVec m ((X - 1) ^ n : R[X]) = fun (i : Fin _) => ((-1) ^ (n - i) * (n.choose i : R)) := by
  ext ⟨i, hi⟩
  simp only [toVec]
  rw [sub_eq_add_neg X, ← _root_.map_one C, ← _root_.map_neg C (1 : R), coeff_X_add_C_pow]

end Ring
