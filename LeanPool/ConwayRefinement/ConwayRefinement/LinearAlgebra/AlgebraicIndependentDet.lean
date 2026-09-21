/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Determinants of matrices of algebraically independent entries

A square matrix whose entries are either `0` or members of an algebraically independent family,
with no member used twice and every diagonal entry a member, has nonzero determinant. The
determinant is the image of the determinant of the symbolic matrix, which is a nonzero
polynomial: specializing the diagonal variables to `1` and all others to `0` evaluates it to
`det 1 = 1`.

The zero pattern is recorded by a function `v : n → n → Option V`; the entry at `(i, j)` is
`f w` when `v i j = some w` and `0` when `v i j = none`.
-/

universe u v w

public section

namespace Matrix

variable {R : Type u} {A : Type v} [CommRing R] [Nontrivial R] [CommRing A] [Algebra R A]

/-- A matrix of distinct algebraically independent entries and zeros, with a full diagonal of
entries, has nonzero determinant. -/
theorem det_ne_zero_of_algebraicIndependent {V : Type w} {f : V → A}
    (hf : AlgebraicIndependent R f) {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → n → Option V) (M : Matrix n n A) (hM : ∀ i j, M i j = (v i j).elim 0 f)
    (hdiag : ∀ i, (v i i).isSome)
    (hdistinct : ∀ i j i' j' w, v i j = some w → v i' j' = some w → i = i' ∧ j = j') :
    M.det ≠ 0 := by
  classical
  intro hdet
  let Msym : Matrix n n (MvPolynomial V R) := Matrix.of fun i j ↦ (v i j).elim 0 MvPolynomial.X
  have hmap : (MvPolynomial.aeval f).mapMatrix Msym = M := by
    ext i j
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, hM i j]
    simp only [Msym, Matrix.of_apply]
    cases v i j <;> simp
  have hdetSym : MvPolynomial.aeval f Msym.det = 0 := by
    rw [AlgHom.map_det, hmap, hdet]
  have hzero : Msym.det = 0 := hf.eq_zero_of_aeval_eq_zero _ hdetSym
  let e : V → R := fun w ↦ if ∃ i, v i i = some w then 1 else 0
  have heval : (MvPolynomial.eval e).mapMatrix Msym = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
    simp only [Msym, Matrix.of_apply]
    by_cases hij : i = j
    · subst hij
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hdiag i)
      rw [hw, if_pos rfl]
      simp only [Option.elim, MvPolynomial.eval_X, e]
      rw [if_pos ⟨i, hw⟩]
    · rw [if_neg hij]
      cases hv : v i j with
      | none => simp
      | some w =>
        simp only [Option.elim, MvPolynomial.eval_X, e]
        rw [if_neg]
        rintro ⟨i', hi'⟩
        obtain ⟨h1, h2⟩ := hdistinct i j i' i' w hv hi'
        exact hij (h1.trans h2.symm)
  have hone : MvPolynomial.eval e Msym.det = 1 := by
    rw [RingHom.map_det, heval, Matrix.det_one]
  rw [hzero, map_zero] at hone
  exact zero_ne_one hone

end Matrix

end
