/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import LeanPool.Koethe.MultiProjective
public import LeanPool.Koethe.Pencil
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Coefficientwise multihomogeneity for matrix words

The central parameter is a univariate polynomial variable.  Its coefficient
ring is a multivariate polynomial ring whose variables are grouped into
independent triples.  The zero polynomial is homogeneous of every degree.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open KoetheMultiProjective

namespace KoetheCounterexample.Mortality

/-- The polynomial ring in `N` blocks of three hole variables. -/
abbrev HoleRing (k : Type*) [CommSemiring k] (N : ℕ) :=
  MvPolynomial (Fin N × Fin 3) k

/-- The multidegree contributed by one occurrence of block `b`. -/
def blockUnit {N : ℕ} (b : Fin N) : Fin N → ℕ := fun c => if c = b then 1 else 0

section Homogeneity

variable {k : Type*} [CommRing k] {N : ℕ}

/-- The coefficients in the central parameter are all multihomogeneous of
one and the same specified multidegree. -/
def CoeffHom (p : Polynomial (HoleRing k N)) (e : Fin N → ℕ) : Prop :=
  ∀ j, IsMultiHomogeneous (p.coeff j) e

theorem multiHom_sum {ι : Type*} (s : Finset ι) (f : ι → HoleRing k N)
    {e : Fin N → ℕ} (hf : ∀ i ∈ s, IsMultiHomogeneous (f i) e) :
    IsMultiHomogeneous (∑ i ∈ s, f i) e := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro hf
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem multiHom_C (a : k) :
    IsMultiHomogeneous (MvPolynomial.C a : HoleRing k N) 0 := by
  exact isMultiHomogeneous_monomial (fun _ => blockDegree_zero _) a

theorem multiHom_X (b : Fin N) (j : Fin 3) :
    IsMultiHomogeneous (MvPolynomial.X (b, j) : HoleRing k N) (blockUnit b) := by
  apply isMultiHomogeneous_monomial
  intro c
  by_cases h : c = b
  · subst c
    simp [blockDegree, blockUnit, Finsupp.single_apply]
  · simp [blockDegree, blockUnit, h]

@[simp] theorem coeffHom_zero (e : Fin N → ℕ) :
    CoeffHom (0 : Polynomial (HoleRing k N)) e := by
  intro j
  simp

theorem coeffHom_C {a : HoleRing k N} {e : Fin N → ℕ}
    (ha : IsMultiHomogeneous a e) : CoeffHom (Polynomial.C a) e := by
  intro j
  by_cases h : j = 0
  · simpa only [Polynomial.coeff_C, ite_eq_left h] using ha
  · simp only [Polynomial.coeff_C, ite_eq_right h, isMultiHomogeneous_zero]

@[simp] theorem coeffHom_one : CoeffHom (1 : Polynomial (HoleRing k N)) 0 := by
  simpa only [map_one] using coeffHom_C (multiHom_C (N := N) (1 : k))

theorem coeffHom_intCast (z : ℤ) :
    CoeffHom (z : Polynomial (HoleRing k N)) 0 := by
  simpa only [map_intCast] using coeffHom_C (multiHom_C (N := N) (z : k))

theorem coeffHom_X : CoeffHom (Polynomial.X : Polynomial (HoleRing k N)) 0 := by
  intro j
  by_cases h : 1 = j
  · simpa only [Polynomial.coeff_X, ite_eq_left h, map_one] using
      multiHom_C (N := N) (1 : k)
  · simp only [Polynomial.coeff_X, ite_eq_right h, isMultiHomogeneous_zero]

theorem CoeffHom.add {p q : Polynomial (HoleRing k N)} {e : Fin N → ℕ}
    (hp : CoeffHom p e) (hq : CoeffHom q e) : CoeffHom (p + q) e := by
  intro j
  simpa only [Polynomial.coeff_add] using (hp j).add (hq j)

theorem CoeffHom.sum {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (HoleRing k N)) {e : Fin N → ℕ}
    (hf : ∀ i ∈ s, CoeffHom (f i) e) : CoeffHom (∑ i ∈ s, f i) e := by
  intro j
  rw [Polynomial.finsetSum_coeff]
  exact multiHom_sum s _ (fun i hi => hf i hi j)

theorem CoeffHom.mul {p q : Polynomial (HoleRing k N)} {e f : Fin N → ℕ}
    (hp : CoeffHom p e) (hq : CoeffHom q f) : CoeffHom (p * q) (e + f) := by
  intro j
  rw [Polynomial.coeff_mul]
  exact multiHom_sum _ _ (fun i _ => (hp i.1).mul (hq i.2))

theorem CoeffHom.prod {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (HoleRing k N)) (e : ι → Fin N → ℕ)
    (hf : ∀ i ∈ s, CoeffHom (f i) (e i)) :
    CoeffHom (∏ i ∈ s, f i) (∑ i ∈ s, e i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro hf
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- The common multidegree of every coefficient of every matrix entry. -/
def MatrixCoeffHom {m n : Type*} (A : Matrix m n (Polynomial (HoleRing k N)))
    (e : Fin N → ℕ) : Prop := ∀ i j, CoeffHom (A i j) e

theorem matrixCoeffHom_one {n : Type*} [DecidableEq n] :
    MatrixCoeffHom (1 : Matrix n n (Polynomial (HoleRing k N))) 0 := by
  intro i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h, coeffHom_one, coeffHom_zero]

theorem MatrixCoeffHom.mul {m n o : Type*} [Fintype n]
    {A : Matrix m n (Polynomial (HoleRing k N))}
    {B : Matrix n o (Polynomial (HoleRing k N))} {e f : Fin N → ℕ}
    (hA : MatrixCoeffHom A e) (hB : MatrixCoeffHom B f) :
    MatrixCoeffHom (A * B) (e + f) := by
  intro i j
  rw [Matrix.mul_apply]
  exact CoeffHom.sum _ _ (fun x _ => (hA i x).mul (hB x j))

theorem MatrixCoeffHom.det {r : ℕ}
    {A : Matrix (Fin r) (Fin r) (Polynomial (HoleRing k N))} {e : Fin N → ℕ}
    (hA : MatrixCoeffHom A e) : CoeffHom A.det (fun b => r * e b) := by
  classical
  rw [Matrix.det_apply']
  apply CoeffHom.sum
  intro σ _
  have hp := CoeffHom.prod Finset.univ (fun i => A (σ i) i) (fun _ => e)
    (fun i _ => hA (σ i) i)
  convert (coeffHom_intCast (N := N) (k := k) (Equiv.Perm.sign σ : ℤ)).mul hp using 1
  ext b
  simp

theorem matrixCoeffHom_prod {n α : Type*} [Fintype n] [DecidableEq n]
    (w : List α) (L : α → Matrix n n (Polynomial (HoleRing k N)))
    (e : α → Fin N → ℕ) (hw : ∀ a ∈ w, MatrixCoeffHom (L a) (e a)) :
    MatrixCoeffHom (w.map L).prod (w.map e).sum := by
  revert hw
  induction w with
  | nil =>
    intro _
    simpa using (matrixCoeffHom_one (n := n) (N := N) (k := k))
  | cons a w ih =>
    intro hw
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact (hw a (List.mem_cons_self ..)).mul
      (ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)))

end Homogeneity

section Lift

variable {k : Type*} [Field k] {N d : ℕ}

theorem lift_coeffHom (P : Pencil k d) (a : Fin 3 → HoleRing k N)
    (e : Fin N → ℕ) (ha : ∀ i, IsMultiHomogeneous (a i) e) :
    MatrixCoeffHom (P.lift a) e := by
  intro row col
  unfold Pencil.lift
  rw [MvPolynomial.algebraMap_eq]
  apply CoeffHom.add
  · apply coeffHom_C
    apply multiHom_sum
    intro i _
    simpa only [zero_add] using (multiHom_C (P.scalar i row col)).mul (ha i)
  · have hlin : CoeffHom
        (Polynomial.C (∑ i : Fin 3, MvPolynomial.C (P.linear i row col) * a i)) e := by
      apply coeffHom_C
      apply multiHom_sum
      intro i _
      simpa only [zero_add] using (multiHom_C (P.linear i row col)).mul (ha i)
    simpa only [zero_add] using coeffHom_X.mul hlin

end Lift

end KoetheCounterexample.Mortality

end
