/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Defs

import LeanPool.RingOfIntegersProject.PolynomialAsVec

variable {R : Type*} {m n : ℕ}

open Matrix

/-- Rotate a vector by moving the entries `i` steps to the right. -/
def vecRotate (P : Fin n → R) (i : Fin n) : Fin n → R := fun j ↦ P (j - i)

example : vecRotate ![1, 2, 3] 1 = ![3, 1, 2] := by decide

@[simp]
theorem vecRotate_map {S : Type*} (φ : R → S) (f : Fin n → R) (i) (j) :
    vecRotate (φ ∘ f) i j = φ (vecRotate f i j) := by
  simp [vecRotate]

/-- Resize a vector, adding `x` to the end if it needs to be longer, or cutting of the final
entries if it needs to be shorter. -/
def Fin.pad (P : Fin n → R) (x : R) : Fin m → R
  | ⟨i, _⟩ => if h : i < n then P ⟨i, h⟩ else x

lemma Fin.pad_of_lt (P : Fin n → R) (x : R) (i : Fin m)
    (h : (i : ℕ) < n) : Fin.pad P x i = P ⟨i, h⟩ := by
  simp [pad, h]

lemma Fin.pad_of_ge (P : Fin n → R) (x : R) (i : Fin m)
    (h : n ≤ (i : ℕ)) : Fin.pad P x i = x := by
  simp [pad, not_lt_of_ge h]

@[simp] lemma Fin.pad_cast {a} (P : Fin a → R) (h : n = a) :
    Fin.pad (m := m) (P ∘ Fin.cast h) = Fin.pad P := by
  subst h
  simp

@[simp] lemma Fin.pad_finCongr {a} (P : Fin a → R) (h : n = a) :
    Fin.pad (m := m) (P ∘ finCongr h) = Fin.pad P := by
  subst h
  simp

@[simp]
theorem Fin.pad_map {S : Type*} (φ : R → S) (f : Fin (n + 1) → R) (x : R) (y : S)
    (h : φ x = y) :
    Fin.pad (m := m) (φ ∘ f) y = φ ∘ (Fin.pad f x) := by
  ext i
  simp [Fin.pad, ← h]
  split_ifs <;> rfl

section Zero

variable [Zero R]

/-- `sylvesterVec P i` is the vector `P` with `i` zeros appended to the left and `m - i` zeros to the right. -/
def sylvesterVec (P : Fin (n + 1) → R) (i : Fin m) : Fin (n + m) → R :=
  vecRotate (Fin.pad P 0) ((i.castAdd _).cast (add_comm _ _))

lemma sylvesterVec_apply (P : Fin (n + 1) → R) (i : Fin m) (j : Fin (n + m)) :
    sylvesterVec P i j = Fin.pad P 0 (j - ((i.castAdd _).cast (add_comm _ _))) :=
  rfl

@[simp] theorem Fin.castAdd_zero_right [NeZero m] [NeZero (m + n)] :
    (castAdd n 0 : Fin (m + n)) = 0 := rfl

@[simp]
lemma sylvesterVec_zero [NeZero m] (P : Fin (n + 1) → R) (j : Fin (n + m)) :
    sylvesterVec P 0 j = Fin.pad P 0 j := by
  have : NeZero (m + n) := ⟨(Nat.add_pos_left (NeZero.pos _) _).ne'⟩
  have : NeZero (n + m) := ⟨(Nat.add_pos_right _ (NeZero.pos _)).ne'⟩
  rw [sylvesterVec_apply, Fin.castAdd_zero_right, Fin.cast_zero, sub_zero j]

lemma sylvesterVec_cast {a} (P : Fin (a + 1) → R) (i : Fin m) (j : Fin (n + m))
    (h : n + 1 = a + 1) :
    sylvesterVec (P ∘ Fin.cast h) i j = sylvesterVec P i (j.cast (by simpa using h)) := by
  have : n = a := Nat.succ_injective h
  subst this
  simp

lemma sylvesterVec_of_lt (P : Fin (n + 1) → R) (i : Fin m) (j : Fin (n + m))
    (h : (j : ℕ) < i) : sylvesterVec P i j = 0 := by
  rw [sylvesterVec_apply, Fin.pad_of_ge]
  · rw [Nat.succ_le, Fin.coe_sub_iff_lt.mpr h, Fin.coe_cast, Fin.coe_castAdd, add_right_comm _ m,
        Nat.add_sub_assoc i.prop.le, add_assoc]
    simp

lemma sylvesterVec_of_ge_of_le (P : Fin (n + 1) → R) (i : Fin m) (j : Fin (n + m))
    (h₁ : (i : ℕ) ≤ j) (h₂ : (j : ℕ) - i ≤ n) :
    sylvesterVec P i j = P ⟨(j : ℕ) - i, Nat.lt_succ.mpr h₂⟩ := by
  rw [sylvesterVec_apply, Fin.pad_of_lt]
  · congr
    rw [Fin.coe_sub_iff_le.mpr h₁, Fin.coe_cast, Fin.coe_castAdd]
  · rwa [Nat.lt_succ, Fin.coe_sub_iff_le.mpr h₁, Fin.coe_cast, Fin.coe_castAdd]

lemma sylvesterVec_of_ge_of_gt (P : Fin (n + 1) → R) (i : Fin m) (j : Fin (n + m))
    (h₁ : (i : ℕ) ≤ j) (h₂ : n < (j : ℕ) - i) : sylvesterVec P i j = 0 := by
  rw [sylvesterVec_apply, Fin.pad_of_ge]
  · rwa [Nat.succ_le, Fin.coe_sub_iff_le.mpr h₁, Fin.coe_cast, Fin.coe_castAdd]

lemma sylvesterVec_def (P : Fin (n + 1) → R) (i : Fin m) (j : Fin (n + m)) :
  sylvesterVec P i j =
    if i ≤ (j : ℕ) then
      if h₂ : (j : ℕ) - i ≤ n then P ⟨(j : ℕ) - i, Nat.lt_succ.mpr h₂⟩
        else 0
      else 0 := by
  split_ifs with h₁ h₂
  · exact sylvesterVec_of_ge_of_le P i j h₁ h₂
  · exact sylvesterVec_of_ge_of_gt P i j h₁ (not_le.mp h₂)
  · exact sylvesterVec_of_lt P i j (not_le.mp h₁)

lemma sylvesterVec_cases (P : R → Prop) (h0 : P 0) {f : Fin (n + 1) → R} (hf : ∀ i, P (f i)) :
    ∀ i (j : Fin (n + m)), P (sylvesterVec f i j) := by
  intro i j
  cases lt_or_ge (j : ℕ) i
  case inl h =>
    rwa [sylvesterVec_of_lt _ _ _ h]
  case inr h₁ =>
    cases le_or_gt ((j : ℕ) - i) n
    case inl h₂ =>
      rw [sylvesterVec_of_ge_of_le _ _ _ h₁ h₂]
      apply hf
    case inr h₂ =>
      rwa [sylvesterVec_of_ge_of_gt _ _ _ h₁ h₂]

example : sylvesterVec (m := 3) ![1, 2, 3] 1 = ![0, 1, 2, 3, 0] := by decide
example : sylvesterVec (m := 3) ![1, 2, 3] 2 = ![0, 0, 1, 2, 3] := by decide

end Zero

variable [CommRing R] 

@[simp] lemma vecRotate_smul (a : R) (P : Fin n → R) (i) :
    vecRotate (a • P) i = a • vecRotate P i := by
  ext j
  simp [vecRotate]

@[simp] lemma Fin.pad_smul {a : R} (P : Fin n → R) (x : R) :
    Fin.pad (m := m) (a • P) (a * x) = a • Fin.pad P x := by
  ext ⟨i, hi⟩
  simp only [Fin.pad, Pi.smul_apply]
  split_ifs <;> simp

@[simp] lemma Fin.pad_smul_zero {a : R} (P : Fin n → R) :
    Fin.pad (m := m) (a • P) 0 = a • Fin.pad P 0 := by
  rw [← Fin.pad_smul, mul_zero]

lemma sylvesterVec_smul (a : R) (P : Fin (n + 1) → R) :
    sylvesterVec (m := m) (n := n) (a • P) = a • sylvesterVec P := by
  ext i j
  simp only [sylvesterVec, Pi.smul_apply, Fin.pad_smul_zero, vecRotate_smul]

def sylvesterMatrixVec (P : Fin (n + 1) → R) (Q : Fin (m + 1) → R) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  (Matrix.of (Fin.addCases (fun i j ↦ sylvesterVec P i (j.cast (add_comm _ _))) (sylvesterVec Q)))ᵀ

@[simp]
lemma sylvesterMatrixVec_zero (P Q : Fin 1 → R) :
    sylvesterMatrixVec P Q = !![] := by ext i; apply finZeroElim i

@[simp]
lemma sylvesterMatrixVec_one (P Q : Fin 2 → R) :
    sylvesterMatrixVec P Q = !![P 0, Q 0; P 1, Q 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] lemma sylvesterMatrixVec_comp_cast (a b) (P : Fin (a + 1) → R) (Q : Fin (b + 1) → R)
    (h₁ : n + 1 = a + 1) (h₂ : m + 1 = b + 1) (h : b + a = m + n := by simp) :
    sylvesterMatrixVec (P ∘ Fin.cast h₁) (Q ∘ Fin.cast h₂) =
      Matrix.reindex (finCongr h) (finCongr h) (sylvesterMatrixVec P Q) := by
  have := Nat.succ_injective h₁
  subst this
  have := Nat.succ_injective h₂
  subst this
  simp

@[simp] lemma Fin.cast_castAdd (m n n' : ℕ) (h : m + n = n') (i : Fin m) :
    Fin.cast h (Fin.castAdd n i) = Fin.castLE (Nat.le.intro h) i := by
  ext
  rfl

@[simp] lemma finAddFlip_symm {m n : ℕ} :
  (finAddFlip (m := m) (n := n)).symm = finAddFlip := by ext i; simp [finAddFlip]

def sylvesterMatrixVec_swap (P : Fin (n + 1) → R) (Q : Fin (m + 1) → R) :
    sylvesterMatrixVec P Q =
      Matrix.reindex (finCongr (add_comm _ _)) finAddFlip (sylvesterMatrixVec Q P) := by
  ext i j
  rw [sylvesterMatrixVec, transpose_apply, of_apply, sylvesterMatrixVec, reindex_apply,
      submatrix_apply, transpose_apply, of_apply]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.addCases_left, finAddFlip_symm, finAddFlip_apply_castAdd, Fin.addCases_right,
        finCongr_symm, finCongr_apply]
  · rw [Fin.addCases_right, finAddFlip_symm, finAddFlip_apply_natAdd, Fin.addCases_left,
        finCongr_symm, finCongr_apply, Fin.cast_trans, Fin.cast_eq_self]

@[simp]
lemma sylvesterMatrixVec_smul (a : R) (P : Fin (n + 1) → R) (Q : Fin (m + 1) → R) :
    sylvesterMatrixVec P (a • Q) = Matrix.of (fun (i j : Fin (m + n)) =>
      (Fin.addCases (fun _ => 1) (fun _ => a) j) * sylvesterMatrixVec P Q i j) := by
  ext i j
  induction j using Fin.addCases <;>
    simp only [sylvesterMatrixVec, Matrix.transpose_apply, Matrix.of_apply, Fin.addCases_left,
      Fin.addCases_right, Pi.natCast_def, one_mul, sylvesterVec_smul, Pi.smul_apply, smul_eq_mul]

@[simp]
lemma smul_sylvesterMatrixVec (a : R) (P : Fin (n + 1) → R) (Q : Fin (m + 1) → R) :
    sylvesterMatrixVec (a • P) Q = Matrix.of (fun (i j : Fin (m + n)) =>
      (Fin.addCases (fun _ => a) (fun _ => 1) j) * sylvesterMatrixVec P Q i j) := by
  ext i j
  induction j using Fin.addCases <;>
    simp only [sylvesterMatrixVec, Matrix.transpose_apply, Matrix.of_apply, Fin.addCases_left,
      Fin.addCases_right, Pi.natCast_def, one_mul, sylvesterVec_smul, Pi.smul_apply, smul_eq_mul]

@[simp]
lemma sylvesterMatrixVec_zero_left (P : Fin 1 → R) (Q : Fin (n + 1) → R) :
    sylvesterMatrixVec P Q =
      Matrix.reindex (finCongr (add_comm _ _)) (finCongr (add_zero n).symm)
        (Matrix.of (sylvesterVec P))ᵀ := by
  ext i j
  refine Fin.addCases (fun j => ?_) (fun j => by apply finZeroElim j) j
  rw [sylvesterMatrixVec, Matrix.transpose_apply, Matrix.of_apply, Fin.addCases_left]
  rfl

@[simp]
lemma sylvesterMatrixVec_zero_right (P : Fin (m + 1) → R) (Q : Fin 1 → R) :
    sylvesterMatrixVec P Q =
      Matrix.reindex (finCongr rfl) (finCongr (zero_add m).symm) (Matrix.of (sylvesterVec Q))ᵀ := by
  ext i j
  refine Fin.addCases (fun j => by apply finZeroElim j) (fun j => ?_) j
  rw [sylvesterMatrixVec, Matrix.transpose_apply, Matrix.of_apply, Fin.addCases_right,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.of_apply,
    finCongr_symm, finCongr_apply, Fin.cast_natAdd]
  rfl

@[simp]
theorem sylvesterVec_map {S : Type*} [CommRing S] (φ : R →+* S) (f : Fin (n + 1) → R) (i : Fin m) (j) :
    sylvesterVec (φ ∘ f) i j = φ (sylvesterVec f i j) := by
  rw [sylvesterVec, Fin.pad_map φ f 0 0 (map_zero φ), vecRotate_map, sylvesterVec]

@[simp]
theorem sylvesterMatrixVec_map {S : Type*} [CommRing S] (φ : R →+* S) (f : Fin (n + 1) → R) (g : Fin (m + 1) → R) :
    sylvesterMatrixVec (φ ∘ f) (φ ∘ g) = (sylvesterMatrixVec f g).map φ := by
  ext i j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [sylvesterMatrixVec]
  · simp [sylvesterMatrixVec]

namespace Polynomial

/--
We define the sylvester matrix for polynomials P and Q and natural numbers n and m as the
Sylvester matrix for the lists [P.coeff 0, P.coeff 1, ... , P.coeff n] and
[Q.coeff 0, Q.coeff 1, ... , Q.coeff m].

Note that this is slightly different from the standard definition: the highest coefficients
end up with the highest indices. This allows for easier working with the `sylvesterMap`,
since the `i`th coefficient ends up at index `i + j` for some `j`.
-/
def sylvesterMatrixAux (m n : ℕ) (P Q : R[X]) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  sylvesterMatrixVec (Q.toVec (n + 1)) (P.toVec (m + 1))

/--
We define the sylvester matrix for polynomials P and Q of degree n and m respectively as the
Sylvester matrix for the lists [P.coeff 0, P.coeff 1, ... , P.coeff n] and
[Q.coeff 0, Q.coeff 1, ... , Q.coeff m]
-/
def sylvesterMatrix (P Q : R[X]) :
    Matrix (Fin (P.natDegree + Q.natDegree)) (Fin (P.natDegree + Q.natDegree)) R :=
  sylvesterMatrixAux _ _ P Q

lemma sylvesterMatrix_C (P : Polynomial R) (x : R) :
    P.sylvesterMatrix (C x) = diagonal (fun _ => x) := by
  ext i j
  rw [sylvesterMatrix, sylvesterMatrixAux, sylvesterMatrixVec, diagonal, of_apply, transpose_apply,
      of_apply]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  swap
  · rw [natDegree_C] at j
    rcases j with ⟨_, ⟨⟩⟩
  rw [Fin.addCases_left]
  split_ifs with h
  · simp [h, sylvesterVec_of_ge_of_le]
  · obtain (h | h) := lt_or_gt_of_ne h
    · rw [sylvesterVec_of_lt _ _ _ h]
    · rw [sylvesterVec_of_ge_of_gt _ _ _ h.le]
      simpa using h

lemma C_sylvesterMatrix (x : R) (Q : Polynomial R) :
    (C x).sylvesterMatrix Q = diagonal (fun _ => x) := by
  ext i j
  rw [sylvesterMatrix, sylvesterMatrixAux, sylvesterMatrixVec, diagonal, of_apply, transpose_apply,
      of_apply]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [natDegree_C] at j
    rcases j with ⟨_, ⟨⟩⟩
  rw [Fin.addCases_right]
  split_ifs with h
  · simp [h, sylvesterVec_of_ge_of_le]
  · obtain (h | h) := lt_or_gt_of_ne h <;>
      simp only [Fin.lt_def, Fin.coe_natAdd, natDegree_C, zero_add] at h
    · rw [sylvesterVec_of_lt _ _ _ h]
    · rw [sylvesterVec_of_ge_of_gt _ _ _ h.le]
      simpa using h

end Polynomial
