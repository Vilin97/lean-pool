/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.LinearAction
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous symbols and prospective monic charts

Over a characteristic-zero field, a nonzero homogeneous phase-space symbol
has a nonvanishing point over the original field. Linear substitution evaluates
the transformed symbol along a coordinate axis at the corresponding matrix
column. Axis restriction to one variable identifies this value with the exact
pure-power coefficient. The remaining chart-existence obligation is to place
the chosen nonzero vector into a prescribed column of a symplectic matrix.
-/

namespace Stafford38.CharacteristicHomogeneousChart

open Stafford38.Characteristic
open Stafford38.CharacteristicLinearAction

noncomputable section
universe u
variable (k : Type u) [Field k]

theorem exists_eval_ne_zero_of_homogeneous [CharZero k]
    {n N : ℕ} {P : SymbolRing k n}
    (hP : P.IsHomogeneous N) (hne : P ≠ 0) :
    ∃ v : PhaseVar n → k, MvPolynomial.eval v P ≠ 0 := by
  by_contra h
  push_neg at h
  exact hne (hP.eq_zero_of_forall_eval_eq_zero h)

theorem eval_symbolLinearAlgHom {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (v : PhaseVar n → k) (P : SymbolRing k n) :
    MvPolynomial.eval v (symbolLinearAlgHom k M P) =
      MvPolynomial.eval (fun i => ∑ j, M i j * v j) P := by
  rw [symbolLinearAlgHom]
  change MvPolynomial.aeval v
      (MvPolynomial.aeval (symbolLinearCombination k M) P) =
    MvPolynomial.aeval (fun i => ∑ j, M i j * v j) P
  rw [MvPolynomial.comp_aeval_apply]
  congr 2
  funext i
  simp [symbolLinearCombination]

theorem homogeneous_unit_eq_monomial {N : ℕ}
    (P : MvPolynomial Unit k) (hP : P.IsHomogeneous N) :
    P = MvPolynomial.monomial (Finsupp.single () N)
      (P.coeff (Finsupp.single () N)) := by
  ext d
  by_cases hd : d = Finsupp.single () N
  · subst d
    simp
  · have hdegree : d.degree ≠ N := by
      intro hdeg
      apply hd
      have hdform : d = Finsupp.single () (d ()) := by
        apply Finsupp.ext
        intro i
        rcases i with ⟨⟩
        simp
      rw [hdform, Finsupp.degree_single] at hdeg
      rw [hdform, hdeg]
    rw [hP.coeff_eq_zero hdegree]
    rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hd)]

def axisPoint {n : ℕ} (t : PhaseVar n) : PhaseVar n → k :=
  fun i => if i = t then 1 else 0

def axisPolynomial {n : ℕ} (t : PhaseVar n) :
    SymbolRing k n →ₐ[k] MvPolynomial Unit k :=
  MvPolynomial.aeval (fun i => if i = t then MvPolynomial.X () else 0)

theorem axisPolynomial_isHomogeneous {n N : ℕ}
    (t : PhaseVar n) {P : SymbolRing k n} (hP : P.IsHomogeneous N) :
    (axisPolynomial k t P).IsHomogeneous N := by
  simpa [axisPolynomial, ← MvPolynomial.aeval_eq_bind₁] using hP.aeval (n := 1)
    (fun i => if i = t then MvPolynomial.X () else 0)
    (fun i => by
      by_cases hi : i = t
      · simp [hi, MvPolynomial.isHomogeneous_X]
      · simp [hi, MvPolynomial.isHomogeneous_zero])

theorem eval_axis_eq_eval_axisPolynomial_one {n : ℕ}
    (t : PhaseVar n) (P : SymbolRing k n) :
    MvPolynomial.eval (axisPoint k t) P =
      MvPolynomial.eval (fun _ : Unit => (1 : k)) (axisPolynomial k t P) := by
  change MvPolynomial.aeval (axisPoint k t) P =
    MvPolynomial.aeval (fun _ : Unit => (1 : k))
      (MvPolynomial.aeval
        (fun i => if i = t then MvPolynomial.X () else 0) P)
  rw [MvPolynomial.comp_aeval_apply]
  congr 2
  funext i
  by_cases hi : i = t
  · simp [axisPoint, hi]
  · simp [axisPoint, hi]

theorem eval_axis_eq_pureCoefficient {n N : ℕ}
    (t : PhaseVar n) {P : SymbolRing k n} (hP : P.IsHomogeneous N) :
    MvPolynomial.eval (axisPoint k t) P =
      (axisPolynomial k t P).coeff (Finsupp.single () N) := by
  rw [eval_axis_eq_eval_axisPolynomial_one]
  rw [homogeneous_unit_eq_monomial k (axisPolynomial k t P)
    (axisPolynomial_isHomogeneous k t hP)]
  simp [MvPolynomial.eval_monomial]

theorem symbolLinearCombination_isHomogeneous {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) (i : PhaseVar n) :
    (symbolLinearCombination k M i).IsHomogeneous 1 := by
  rw [symbolLinearCombination]
  apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
  intro j hj
  simpa using (MvPolynomial.isHomogeneous_C (PhaseVar n) (M i j)).mul
    (MvPolynomial.isHomogeneous_X (R := k) j)

theorem symbolLinearAlgHom_isHomogeneous {n N : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    {P : SymbolRing k n} (hP : P.IsHomogeneous N) :
    (symbolLinearAlgHom k M P).IsHomogeneous N := by
  simpa [symbolLinearAlgHom] using hP.aeval (n := 1)
    (symbolLinearCombination k M)
    (symbolLinearCombination_isHomogeneous k M)

theorem eval_symbolLinearAlgHom_axis {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (t : PhaseVar n) (P : SymbolRing k n) :
    MvPolynomial.eval (axisPoint k t) (symbolLinearAlgHom k M P) =
      MvPolynomial.eval (fun i => M i t) P := by
  rw [eval_symbolLinearAlgHom]
  congr 2
  funext i
  simp [axisPoint]

theorem pureCoefficient_symbolLinearAlgHom {n N : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (t : PhaseVar n) {P : SymbolRing k n} (hP : P.IsHomogeneous N) :
    (axisPolynomial k t (symbolLinearAlgHom k M P)).coeff (Finsupp.single () N) =
      MvPolynomial.eval (fun i => M i t) P := by
  rw [← eval_axis_eq_pureCoefficient k t
    (symbolLinearAlgHom_isHomogeneous k M hP)]
  exact eval_symbolLinearAlgHom_axis k M t P

/- Exact statement pins for original-field nonvanishing and column detection. -/
example [CharZero k] {n N : ℕ} {P : SymbolRing k n}
    (hP : P.IsHomogeneous N) (hne : P ≠ 0) :
    ∃ v : PhaseVar n → k, MvPolynomial.eval v P ≠ 0 :=
  exists_eval_ne_zero_of_homogeneous k hP hne

example {n N : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (t : PhaseVar n) {P : SymbolRing k n} (hP : P.IsHomogeneous N) :
    (axisPolynomial k t (symbolLinearAlgHom k M P)).coeff (Finsupp.single () N) =
      MvPolynomial.eval (fun i => M i t) P :=
  pureCoefficient_symbolLinearAlgHom k M t hP


end
end Stafford38.CharacteristicHomogeneousChart
