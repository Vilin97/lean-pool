/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.LinearCombination

/-!
# Ordinary Wronskians over differential fields

Corvaja--Zannier's positive-characteristic argument uses an ordinary Wronskian over the
subfield of constants of a derivation. This file proves the required algebraic criterion:
a finite family is linearly independent over the exact constant field if and only if its
Wronskian determinant is nonzero.

The reverse implication is the difficult direction. Its proof normalizes a nonzero kernel
vector, differentiates the resulting row relations, deletes the normalized coordinate, and
applies induction to the smaller Wronskian.
-/

namespace BGS.Algebra

noncomputable section

open scoped Matrix

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- The ordinary Wronskian matrix of a finite family with respect to a derivation. -/
def derivationWronskian (D : Derivation C L L) {n : ℕ} (f : Fin n → L) :
    Matrix (Fin n) (Fin n) L :=
  fun i j ↦ (D.toLinearMap ^ (i : ℕ)) (f j)

private lemma derivation_iterate_succ (D : Derivation C L L) (n : ℕ) (x : L) :
    D ((D.toLinearMap ^ n) x) = (D.toLinearMap ^ (n + 1)) x := by
  rw [pow_succ', Module.End.mul_apply]
  rfl

/-- If every element killed by `D` comes from `C`, then a family linearly independent over
`C` has nonzero ordinary Wronskian. -/
theorem derivationWronskian_det_ne_zero_of_linearIndependent
    (D : Derivation C L L)
    (constants : ∀ x : L, D x = 0 → ∃ c : C, algebraMap C L c = x) :
    ∀ (n : ℕ) (f : Fin n → L), LinearIndependent C f →
      (derivationWronskian D f).det ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro f hf
      simp
  | succ n ih =>
      intro f hf hdet
      let W : Matrix (Fin (n + 1)) (Fin (n + 1)) L := derivationWronskian D f
      have hWdet : W.det = 0 := by simpa [W] using hdet
      obtain ⟨a, ha_ne, haW⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hWdet
      obtain ⟨k, hak⟩ : ∃ k, a k ≠ 0 := by
        simpa [Function.ne_iff] using ha_ne
      let c : Fin (n + 1) → L := fun j ↦ (a k)⁻¹ * a j
      have hck : c k = 1 := by simp [c, hak]
      have hcW : W *ᵥ c = 0 := by
        funext i
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
        calc
          ∑ j, W i j * c j = (a k)⁻¹ * ∑ j, W i j * a j := by
            simp only [c]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = 0 := by
            rw [show ∑ j, W i j * a j = 0 by
              simpa [Matrix.mulVec, dotProduct] using congr_fun haW i, mul_zero]
      have hc_relation (i : Fin (n + 1)) :
          ∑ j, (D.toLinearMap ^ (i : ℕ)) (f j) * c j = 0 := by
        simpa [W, derivationWronskian, Matrix.mulVec, dotProduct] using congr_fun hcW i
      have hDck : D (c k) = 0 := by simp [hck]
      let g : Fin n → L := fun j ↦ f (k.succAbove j)
      have hg : LinearIndependent C g :=
        hf.comp k.succAbove k.succAbove_right_injective
      have hWgdet : (derivationWronskian D g).det ≠ 0 := ih g hg
      let b : Fin n → L := fun j ↦ D (c (k.succAbove j))
      have hfull (i : Fin n) :
          ∑ j : Fin (n + 1),
              (D.toLinearMap ^ (i : ℕ)) (f j) * D (c j) = 0 := by
        have hderiv := congrArg D (hc_relation i.castSucc)
        have hnext := hc_relation i.succ
        simp only [map_zero, map_sum, D.leibniz, smul_eq_mul,
          derivation_iterate_succ] at hderiv
        have hindex (j : Fin (n + 1)) :
            (D.toLinearMap ^ (((i.castSucc : Fin (n + 1)) : ℕ) + 1)) (f j) =
              (D.toLinearMap ^ ((i.succ : Fin (n + 1)) : ℕ)) (f j) := by
          simp
        simp_rw [hindex] at hderiv
        have hnext' :
            ∑ j : Fin (n + 1),
                c j * (D.toLinearMap ^ ((i.succ : Fin (n + 1)) : ℕ)) (f j) = 0 := by
          simpa [mul_comm] using hnext
        rw [Finset.sum_add_distrib] at hderiv
        have hderiv' :
            (∑ j : Fin (n + 1), (D.toLinearMap ^ (i : ℕ)) (f j) * D (c j)) +
              ∑ j : Fin (n + 1),
                c j * (D.toLinearMap ^ ((i.succ : Fin (n + 1)) : ℕ)) (f j) = 0 := by
          simpa using hderiv
        linear_combination hderiv' - hnext'
      have hWgb : derivationWronskian D g *ᵥ b = 0 := by
        funext i
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, b, g,
          derivationWronskian]
        have hi := hfull i
        rw [Fin.sum_univ_succAbove (fun j : Fin (n + 1) ↦
          (D.toLinearMap ^ (i : ℕ)) (f j) * D (c j)) k] at hi
        simpa [hDck] using hi
      have hbzero : b = 0 := Matrix.eq_zero_of_mulVec_eq_zero hWgdet hWgb
      have hDc (j : Fin (n + 1)) : D (c j) = 0 := by
        by_cases hj : j = k
        · simpa [hj] using hDck
        · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hj
          have := congr_fun hbzero r
          simpa [b, hr] using this
      choose coeff hcoeff using fun j ↦ constants (c j) (hDc j)
      have hcoeff_relation : ∑ j, coeff j • f j = 0 := by
        have hzero := hc_relation 0
        simpa [hcoeff, Algebra.smul_def, mul_comm] using hzero
      have hcoeff_zero : ∀ j, coeff j = 0 :=
        (Fintype.linearIndependent_iff.mp hf) coeff hcoeff_relation
      have : (1 : L) = 0 := by
        rw [← hck, ← hcoeff k, hcoeff_zero k, map_zero]
      exact one_ne_zero this

/-- A nonzero Wronskian determinant implies linear independence over the derivation's
scalar field. -/
theorem linearIndependent_of_derivationWronskian_det_ne_zero
    (D : Derivation C L L) {n : ℕ} (f : Fin n → L)
    (hdet : (derivationWronskian D f).det ≠ 0) :
    LinearIndependent C f := by
  let W := derivationWronskian D f
  have hcols : LinearIndependent L W.col :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  let gL : Fin n → L := fun i ↦ algebraMap C L (g i)
  have hcomb : ∑ i, gL i • W.col i = 0 := by
    funext r
    have hrow := congrArg (fun x ↦ (D.toLinearMap ^ (r : ℕ)) x) hg
    simp only [map_sum, LinearMap.map_smul] at hrow
    simpa [W, gL, derivationWronskian, Algebra.smul_def] using hrow
  have hgj : gL j = 0 := Fintype.linearIndependent_iff.mp hcols gL hcomb j
  exact (algebraMap C L).injective (by simpa [gL] using hgj)

/-- The ordinary Wronskian criterion when `C` is exactly the field of constants of `D`. -/
theorem derivationWronskian_det_ne_zero_iff_linearIndependent
    (D : Derivation C L L)
    (constants : ∀ x : L, D x = 0 → ∃ c : C, algebraMap C L c = x)
    {n : ℕ} (f : Fin n → L) :
    (derivationWronskian D f).det ≠ 0 ↔ LinearIndependent C f := by
  exact ⟨linearIndependent_of_derivationWronskian_det_ne_zero D f,
    derivationWronskian_det_ne_zero_of_linearIndependent D constants n f⟩

end

end BGS.Algebra
