/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib
import LeanPool.Stafford38.AlgebraicAnalysis.Commutator

/-!
# The linear symplectic layer of the A₂ reduction

This file isolates the part of the generic-monic reduction which is purely
linear algebra.  A Weyl presentation is encoded by a finite family `z` whose
pairwise commutators are the entries of a fixed skew matrix.  A matrix `M`
preserving that form gives a new family by linear combination, and the new
family has exactly the same Weyl commutators.

The result is deliberately stated for an arbitrary finite index type and an
arbitrary symplectic form.  The A₂ instance is obtained with
`ι = Fin 2 ⊕ Fin 2` and `Matrix.J (Fin 2) k`, so this is not a list of
hand-picked coordinate changes.

This is the algebraic prerequisite for applying Stafford's
ring-equivalence transport to a Weyl change of generators.  The final section
also descends a form-preserving change to a homomorphism of the presented
quotient and proves the A₂ symplectic change is invertible using the inverse
matrix and generator-extensionality. The PBW identification and generic monic
normalization belong to the downstream Weyl modules, outside this module's
linear-algebra scope. Reusable commutator identities are imported from
AlgebraicAnalysis.
-/

namespace Stafford

variable {k A ι : Type*} [Field k] [Ring A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]

/-- Historical namespace for the shared ring commutator. -/
def commutator (u v : A) : A := AlgebraicAnalysis.ringCommutator u v

@[simp] theorem commutator_eq_shared (u v : A) :
    commutator u v = AlgebraicAnalysis.ringCommutator u v := rfl

/-- The linear combination of a family of generators specified by a matrix. -/
def linearCombination (M : Matrix ι ι k) (z : ι → A) (i : ι) : A :=
  ∑ j, algebraMap k A (M i j) * z j

lemma commutator_sum_left (u : ι → A) (v : A) :
    commutator (∑ i, u i) v = ∑ i, commutator (u i) v := by
  simp [commutator, Finset.sum_mul, Finset.mul_sum]

lemma commutator_sum_right (u : A) (v : ι → A) :
    commutator u (∑ i, v i) = ∑ i, commutator u (v i) := by
  simp [commutator, Finset.sum_mul, Finset.mul_sum]

lemma commutator_smul_smul (a b : k) (u v : A) :
    commutator (algebraMap k A a * u) (algebraMap k A b * v) =
      algebraMap k A (a * b) * commutator u v := by
  have hub : u * algebraMap k A b = algebraMap k A b * u :=
    (Algebra.commutes b u).symm
  have hva : v * algebraMap k A a = algebraMap k A a * v :=
    (Algebra.commutes a v).symm
  simp only [commutator]
  calc
    algebraMap k A a * u * (algebraMap k A b * v) -
        algebraMap k A b * v * (algebraMap k A a * u) =
      (algebraMap k A a * algebraMap k A b) * (u * v) -
        (algebraMap k A b * algebraMap k A a) * (v * u) := by
          rw [show algebraMap k A a * u * (algebraMap k A b * v) =
              (algebraMap k A a * algebraMap k A b) * (u * v) by
                calc
                  algebraMap k A a * u * (algebraMap k A b * v) =
                      algebraMap k A a * (u * algebraMap k A b) * v := by
                        noncomm_ring
                  _ = algebraMap k A a * (algebraMap k A b * u) * v := by
                        rw [hub]
                  _ = (algebraMap k A a * algebraMap k A b) * (u * v) := by
                        noncomm_ring,
            show algebraMap k A b * v * (algebraMap k A a * u) =
              (algebraMap k A b * algebraMap k A a) * (v * u) by
                calc
                  algebraMap k A b * v * (algebraMap k A a * u) =
                      algebraMap k A b * (v * algebraMap k A a) * u := by
                        noncomm_ring
                  _ = algebraMap k A b * (algebraMap k A a * v) * u := by
                        rw [hva]
                  _ = (algebraMap k A b * algebraMap k A a) * (v * u) := by
                        noncomm_ring]
    _ = algebraMap k A (a * b) * (u * v) -
        algebraMap k A (b * a) * (v * u) := by
          rw [_root_.map_mul, _root_.map_mul]
    _ = algebraMap k A (a * b) * (u * v - v * u) := by
          rw [mul_comm b a, mul_sub]

lemma commutator_linearCombination
    (M : Matrix ι ι k) (z : ι → A) (omega : Matrix ι ι k) (i l : ι)
    (hcomm : ∀ j n, commutator (z j) (z n) =
      algebraMap k A (omega j n)) :
    commutator (linearCombination M z i) (linearCombination M z l) =
      algebraMap k A (∑ j, ∑ n, M i j * omega j n * M l n) := by
  rw [linearCombination, linearCombination, commutator_sum_left]
  simp_rw [commutator_sum_right, commutator_smul_smul, hcomm]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  congr 2
  funext j
  congr 1
  funext n
  calc
    algebraMap k A (M i j) * algebraMap k A (M l n) *
          algebraMap k A (omega j n) =
        algebraMap k A (M i j) *
          (algebraMap k A (M l n) * algebraMap k A (omega j n)) := by
            rw [mul_assoc]
    _ = algebraMap k A (M i j) *
          (algebraMap k A (omega j n) * algebraMap k A (M l n)) := by
            congr 1
            rw [← _root_.map_mul, ← _root_.map_mul]
            congr 1
            ring
    _ = algebraMap k A (M i j) * algebraMap k A (omega j n) *
          algebraMap k A (M l n) := by
            rw [← mul_assoc]

/-- A matrix preserving `omega` preserves all Weyl commutators. -/
theorem symplectic_linear_change_preserves_commutator
    (M : Matrix ι ι k) (z : ι → A) (omega : Matrix ι ι k)
    (hcomm : ∀ j n, commutator (z j) (z n) =
      algebraMap k A (omega j n))
    (hM : M * omega * Matrix.transpose M = omega) :
    ∀ i l, commutator (linearCombination M z i) (linearCombination M z l) =
      algebraMap k A (omega i l) := by
  intro i l
  rw [commutator_linearCombination M z omega i l hcomm]
  have hentry : (∑ j, ∑ n, M i j * omega j n * M l n) = omega i l := by
    calc
      (∑ j, ∑ n, M i j * omega j n * M l n) =
          (M * omega * Matrix.transpose M) i l := by
            simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
            rw [Finset.sum_comm]
      _ = omega i l := by rw [hM]
  rw [hentry]

/-! ### The standard A₂ specialization -/

abbrev A2Index := Fin 2 ⊕ Fin 2

abbrev A2SymplecticForm (k : Type*) [CommRing k] :
    Matrix A2Index A2Index k := Matrix.J (Fin 2) k

theorem a2_symplectic_linear_change_preserves_weyl
    (M : Matrix A2Index A2Index k) (z : A2Index → A)
    (hcomm : ∀ j n, commutator (z j) (z n) =
      algebraMap k A (A2SymplecticForm k j n))
    (hM : M * A2SymplecticForm k * Matrix.transpose M = A2SymplecticForm k) :
    ∀ i l, commutator (linearCombination M z i) (linearCombination M z l) =
      algebraMap k A (A2SymplecticForm k i l) := by
  exact symplectic_linear_change_preserves_commutator M z (A2SymplecticForm k)
    hcomm hM

theorem a2_symplectic_group_change_preserves_weyl
    (M : Matrix.symplecticGroup (Fin 2) k) (z : A2Index → A)
    (hcomm : ∀ j n, commutator (z j) (z n) =
      algebraMap k A (A2SymplecticForm k j n)) :
    ∀ i l, commutator (linearCombination (M : Matrix A2Index A2Index k) z i)
        (linearCombination (M : Matrix A2Index A2Index k) z l) =
      algebraMap k A (A2SymplecticForm k i l) := by
  exact a2_symplectic_linear_change_preserves_weyl (M : Matrix A2Index A2Index k)
    z hcomm (SymplecticGroup.mem_iff.mp M.property)

/-! ### Descent to the presented Weyl algebra

`RingQuot` is Mathlib's universal quotient for a possibly noncommutative ring.
The following definitions use it to make the universal-property step
explicit.  This is still presentation-level algebra: identifying the
quotient with a PBW Weyl algebra remains separate, while the inverse-matrix
argument below proves the form-preserving A₂ map is an automorphism. -/

def freeWeylRelation (omega : Matrix ι ι k)
    (a b : FreeAlgebra k ι) : Prop :=
  ∃ i j,
    a = FreeAlgebra.ι k i * FreeAlgebra.ι k j -
      FreeAlgebra.ι k j * FreeAlgebra.ι k i ∧
    b = algebraMap k (FreeAlgebra k ι) (omega i j)

abbrev FreeWeyl (k : Type*) [Field k] (ι : Type*)
    (omega : Matrix ι ι k) := RingQuot (freeWeylRelation omega)

def freeWeylGenerator (omega : Matrix ι ι k) (i : ι) : FreeWeyl k ι omega :=
  RingQuot.mkAlgHom k (freeWeylRelation omega) (FreeAlgebra.ι k i)

theorem freeWeylGenerator_commutator
    (omega : Matrix ι ι k) (i j : ι) :
    commutator (freeWeylGenerator omega i) (freeWeylGenerator omega j) =
      algebraMap k (FreeWeyl k ι omega) (omega i j) := by
  have h := RingQuot.mkAlgHom_rel k
    (show freeWeylRelation omega
      (FreeAlgebra.ι k i * FreeAlgebra.ι k j -
        FreeAlgebra.ι k j * FreeAlgebra.ι k i)
      (algebraMap k (FreeAlgebra k ι) (omega i j)) from ⟨i, j, rfl, rfl⟩)
  simp only [freeWeylGenerator, commutator, RingQuot.mkAlgHom_coe]
  calc
    RingQuot.mkAlgHom k (freeWeylRelation omega) (FreeAlgebra.ι k i) *
          RingQuot.mkAlgHom k (freeWeylRelation omega) (FreeAlgebra.ι k j) -
        RingQuot.mkAlgHom k (freeWeylRelation omega) (FreeAlgebra.ι k j) *
          RingQuot.mkAlgHom k (freeWeylRelation omega) (FreeAlgebra.ι k i) =
      RingQuot.mkAlgHom k (freeWeylRelation omega)
        (FreeAlgebra.ι k i * FreeAlgebra.ι k j -
          FreeAlgebra.ι k j * FreeAlgebra.ι k i) := by
            rw [← map_mul, ← map_mul, ← map_sub]
    _ = RingQuot.mkAlgHom k (freeWeylRelation omega)
        ((algebraMap k (FreeAlgebra k ι)) (omega i j)) := h
    _ = algebraMap k (FreeWeyl k ι omega) (omega i j) := by
      have hmap : algebraMap k (FreeWeyl k ι omega) =
          (RingQuot.mkAlgHom k (freeWeylRelation omega)).toRingHom.comp
            (algebraMap k (FreeAlgebra k ι)) := by
        apply RingHom.ext
        intro c
        change algebraMap k (FreeWeyl k ι omega) c =
          RingQuot.mkAlgHom k (freeWeylRelation omega)
            (algebraMap k (FreeAlgebra k ι) c)
        exact (RingQuot.mkAlgHom k (freeWeylRelation omega)).commutes c |>.symm
      rw [hmap]
      rfl

def freeWeylLinearCombination
    (M : Matrix ι ι k) (z : ι → FreeWeyl k ι omega) (i : ι) :
    FreeWeyl k ι omega :=
  ∑ j, algebraMap k (FreeWeyl k ι omega) (M i j) * z j

def freeWeylMap (M : Matrix ι ι k) (omega : Matrix ι ι k) :
    FreeAlgebra k ι →ₐ[k] FreeWeyl k ι omega :=
  FreeAlgebra.lift k (fun i => freeWeylLinearCombination M
    (freeWeylGenerator omega) i)

def freeWeylMapRespects (M : Matrix ι ι k) (omega : Matrix ι ι k)
    (hpres : ∀ i j,
      commutator (freeWeylLinearCombination M (freeWeylGenerator omega) i)
          (freeWeylLinearCombination M (freeWeylGenerator omega) j) =
        algebraMap k (FreeWeyl k ι omega) (omega i j)) :
    ∀ ⦃a b : FreeAlgebra k ι⦄,
      freeWeylRelation omega a b → freeWeylMap M omega a = freeWeylMap M omega b
  | _, _, ⟨i, j, rfl, rfl⟩ => by
      simp only [freeWeylMap, FreeAlgebra.lift_ι_apply, map_sub, map_mul,
        freeWeylLinearCombination, AlgHom.commutes]
      exact hpres i j

def freeWeylSymplecticAlgHom (M : Matrix ι ι k) (omega : Matrix ι ι k)
    (hpres : ∀ i j,
      commutator (freeWeylLinearCombination M (freeWeylGenerator omega) i)
          (freeWeylLinearCombination M (freeWeylGenerator omega) j) =
        algebraMap k (FreeWeyl k ι omega) (omega i j)) :
    FreeWeyl k ι omega →ₐ[k] FreeWeyl k ι omega :=
  RingQuot.liftAlgHom k
    ⟨freeWeylMap M omega, freeWeylMapRespects M omega hpres⟩

theorem freeWeylSymplecticAlgHom_generator
    (M : Matrix ι ι k) (omega : Matrix ι ι k)
    (hpres : ∀ i j,
      commutator (freeWeylLinearCombination M (freeWeylGenerator omega) i)
          (freeWeylLinearCombination M (freeWeylGenerator omega) j) =
        algebraMap k (FreeWeyl k ι omega) (omega i j)) (i : ι) :
    freeWeylSymplecticAlgHom M omega hpres (freeWeylGenerator omega i) =
      freeWeylLinearCombination M (freeWeylGenerator omega) i := by
  simpa [freeWeylSymplecticAlgHom, freeWeylGenerator, freeWeylMap,
    FreeAlgebra.lift_ι_apply] using
    (RingQuot.liftAlgHom_mkAlgHom_apply k (freeWeylMap M omega)
      (freeWeylMapRespects M omega hpres) (FreeAlgebra.ι k i))

theorem freeWeylSymplecticAlgHom_map_linearCombination
    (M N : Matrix ι ι k) (omega : Matrix ι ι k)
    (hpres : ∀ i j,
      commutator (freeWeylLinearCombination M (freeWeylGenerator omega) i)
          (freeWeylLinearCombination M (freeWeylGenerator omega) j) =
        algebraMap k (FreeWeyl k ι omega) (omega i j)) (i : ι) :
    freeWeylSymplecticAlgHom M omega hpres
        (freeWeylLinearCombination N (freeWeylGenerator omega) i) =
      freeWeylLinearCombination (N * M) (freeWeylGenerator omega) i := by
  rw [freeWeylLinearCombination, map_sum]
  simp_rw [map_mul, AlgHom.commutes,
    freeWeylSymplecticAlgHom_generator M omega hpres]
  simp_rw [freeWeylLinearCombination]
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  rw [mul_assoc]

lemma freeWeylLinearCombination_one
    (omega : Matrix ι ι k) (i : ι) :
    freeWeylLinearCombination (1 : Matrix ι ι k)
        (freeWeylGenerator omega) i = freeWeylGenerator omega i := by
  simp [freeWeylLinearCombination, Matrix.one_apply]

theorem freeWeylSymplecticAlgHom_comp_generator
    (M N : Matrix ι ι k) (omega : Matrix ι ι k)
    (hM : ∀ i j,
      commutator (freeWeylLinearCombination M (freeWeylGenerator omega) i)
          (freeWeylLinearCombination M (freeWeylGenerator omega) j) =
        algebraMap k (FreeWeyl k ι omega) (omega i j))
    (hN : ∀ i j,
      commutator (freeWeylLinearCombination N (freeWeylGenerator omega) i)
          (freeWeylLinearCombination N (freeWeylGenerator omega) j) =
        algebraMap k (FreeWeyl k ι omega) (omega i j)) (i : ι) :
    freeWeylSymplecticAlgHom M omega hM
      (freeWeylSymplecticAlgHom N omega hN (freeWeylGenerator omega i)) =
      freeWeylLinearCombination (N * M) (freeWeylGenerator omega) i := by
  rw [freeWeylSymplecticAlgHom_generator N omega hN]
  exact freeWeylSymplecticAlgHom_map_linearCombination M N omega hM i

def a2_freeWeyl_symplectic_hpres
    (M : Matrix A2Index A2Index k)
    (hM : M * A2SymplecticForm k * Matrix.transpose M = A2SymplecticForm k) :
    ∀ i l,
      commutator
          (freeWeylLinearCombination M
            (freeWeylGenerator (A2SymplecticForm k)) i)
          (freeWeylLinearCombination M
            (freeWeylGenerator (A2SymplecticForm k)) l) =
        algebraMap k (FreeWeyl k A2Index (A2SymplecticForm k))
          (A2SymplecticForm k i l) := by
  let z : A2Index → FreeWeyl k A2Index (A2SymplecticForm k) :=
    freeWeylGenerator (A2SymplecticForm k)
  intro i l
  change commutator (freeWeylLinearCombination M z i)
      (freeWeylLinearCombination M z l) = _
  exact symplectic_linear_change_preserves_commutator M z
    (A2SymplecticForm k)
    (fun j n => freeWeylGenerator_commutator (A2SymplecticForm k) j n)
    hM i l

def a2_freeWeyl_symplectic_hom
    (M : Matrix A2Index A2Index k)
    (hM : M * A2SymplecticForm k * Matrix.transpose M = A2SymplecticForm k) :
    FreeWeyl k A2Index (A2SymplecticForm k) →ₐ[k]
      FreeWeyl k A2Index (A2SymplecticForm k) :=
  freeWeylSymplecticAlgHom M (A2SymplecticForm k)
    (a2_freeWeyl_symplectic_hpres M hM)

theorem a2_freeWeyl_symplectic_hom_generator
    (M : Matrix A2Index A2Index k)
    (hM : M * A2SymplecticForm k * Matrix.transpose M = A2SymplecticForm k)
    (i : A2Index) :
    a2_freeWeyl_symplectic_hom M hM
        (freeWeylGenerator (A2SymplecticForm k) i) =
      freeWeylLinearCombination M
        (freeWeylGenerator (A2SymplecticForm k)) i := by
  exact freeWeylSymplecticAlgHom_generator M (A2SymplecticForm k)
    (a2_freeWeyl_symplectic_hpres M hM) i

theorem a2_freeWeyl_symplectic_hom_comp_generator
    (M N : Matrix A2Index A2Index k)
    (hM : M * A2SymplecticForm k * Matrix.transpose M = A2SymplecticForm k)
    (hN : N * A2SymplecticForm k * Matrix.transpose N = A2SymplecticForm k)
    (i : A2Index) :
    a2_freeWeyl_symplectic_hom M hM
        (a2_freeWeyl_symplectic_hom N hN
          (freeWeylGenerator (A2SymplecticForm k) i)) =
      freeWeylLinearCombination (N * M)
        (freeWeylGenerator (A2SymplecticForm k)) i := by
  exact freeWeylSymplecticAlgHom_comp_generator M N
    (A2SymplecticForm k)
    (a2_freeWeyl_symplectic_hpres M hM)
    (a2_freeWeyl_symplectic_hpres N hN) i

theorem a2_freeWeyl_symplectic_hom_comp_eq_id
    (M N : Matrix A2Index A2Index k)
    (hM : M * A2SymplecticForm k * Matrix.transpose M = A2SymplecticForm k)
    (hN : N * A2SymplecticForm k * Matrix.transpose N = A2SymplecticForm k)
    (hNM : N * M = 1) :
    (a2_freeWeyl_symplectic_hom M hM).comp
        (a2_freeWeyl_symplectic_hom N hN) =
      AlgHom.id k (FreeWeyl k A2Index (A2SymplecticForm k)) := by
  apply RingQuot.ringQuot_ext' k
  apply FreeAlgebra.hom_ext
  funext i
  change a2_freeWeyl_symplectic_hom M hM
      (a2_freeWeyl_symplectic_hom N hN
        (freeWeylGenerator (A2SymplecticForm k) i)) =
    freeWeylGenerator (A2SymplecticForm k) i
  rw [a2_freeWeyl_symplectic_hom_comp_generator M N hM hN i, hNM]
  exact freeWeylLinearCombination_one (A2SymplecticForm k) i

def a2_freeWeyl_symplectic_equiv
    (M : Matrix.symplecticGroup (Fin 2) k) :
    FreeWeyl k A2Index (A2SymplecticForm k) ≃+*
      FreeWeyl k A2Index (A2SymplecticForm k) := by
  let hM : (M : Matrix A2Index A2Index k) * A2SymplecticForm k *
      Matrix.transpose (M : Matrix A2Index A2Index k) = A2SymplecticForm k :=
    SymplecticGroup.mem_iff.mp M.property
  let hMi : ((M⁻¹ : Matrix.symplecticGroup (Fin 2) k) :
      Matrix A2Index A2Index k) * A2SymplecticForm k *
      Matrix.transpose ((M⁻¹ : Matrix.symplecticGroup (Fin 2) k) :
        Matrix A2Index A2Index k) = A2SymplecticForm k :=
    SymplecticGroup.mem_iff.mp (M⁻¹).property
  let f := a2_freeWeyl_symplectic_hom
    (M : Matrix A2Index A2Index k) hM
  let g := a2_freeWeyl_symplectic_hom
    ((M⁻¹ : Matrix.symplecticGroup (Fin 2) k) : Matrix A2Index A2Index k) hMi
  have hfg : f.comp g =
      AlgHom.id k (FreeWeyl k A2Index (A2SymplecticForm k)) := by
    exact a2_freeWeyl_symplectic_hom_comp_eq_id
      (M : Matrix A2Index A2Index k)
      ((M⁻¹ : Matrix.symplecticGroup (Fin 2) k) : Matrix A2Index A2Index k)
      hM hMi (by
        exact congrArg (fun X : Matrix.symplecticGroup (Fin 2) k =>
          (X : Matrix A2Index A2Index k)) (inv_mul_cancel M))
  have hgf : g.comp f =
      AlgHom.id k (FreeWeyl k A2Index (A2SymplecticForm k)) := by
    exact a2_freeWeyl_symplectic_hom_comp_eq_id
      ((M⁻¹ : Matrix.symplecticGroup (Fin 2) k) : Matrix A2Index A2Index k)
      (M : Matrix A2Index A2Index k) hMi hM (by
        exact congrArg (fun X : Matrix.symplecticGroup (Fin 2) k =>
          (X : Matrix A2Index A2Index k)) (mul_inv_cancel M))
  exact
    { toFun := f
      invFun := g
      left_inv := fun a => congrArg (fun h => h a) hgf
      right_inv := fun a => congrArg (fun h => h a) hfg
      map_mul' := f.map_mul
      map_add' := f.map_add }

end Stafford
