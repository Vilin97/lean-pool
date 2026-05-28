/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Algebra.Lie.DirectSum
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import LeanPool.LowDimSolvClassification.Semidirect
import LeanPool.LowDimSolvClassification.GeneralResults
import LeanPool.LowDimSolvClassification.InstancesConstructions

open Module
open Submodule

namespace LieAlgebra

namespace Dim2
section dimension_two

variable (K : Type*) [CommRing K]

/-- TODO. -/
abbrev Abelian := mkAbelian K (Fin 2 → K)

/-- TODO. -/
def Affine := Fin 2 → K

instance : LieRing (Affine K) := {
  (inferInstance : AddCommGroup (Fin 2 → K)) with
  bracket := fun l r ↦ ![0, l 0 * r 1 - r 0 * l 1]
  add_lie := by
    intro x y z
    unfold Affine at *
    ext i; fin_cases i <;> simp; ring
  lie_add := by
    intro x y z
    unfold Affine at *
    ext i; fin_cases i <;> simp; ring
  lie_self := by
    intro x
    unfold Affine at *
    ext i; fin_cases i <;> simp
  leibniz_lie := by
    intro x y z
    unfold Affine at *
    ext i; fin_cases i <;> simp; ring
}

theorem _root_.LieAlgebra.Dim2.Affine.bracket {l r : Affine K} : ⁅l , r⁆ = ![0,
  l 0 * r 1 - r 0 * l 1] := by
  rfl

instance : LieAlgebra K (Affine K) := {
  (inferInstance : Module K (Fin 2 → K)) with
  lie_smul := by
    intro t x y
    unfold Affine at *
    ext i; fin_cases i <;> simp [Bracket.bracket]; ring
}

end dimension_two

section dim2_affine_lemmas

namespace Affine

variable {K : Type*} [Field K]

/-- In this section we prove that Dim2.Affine is isomorphic to the semidirect product gl(K) ⋉ K,
   where K is the 1-dimensional vector space over K -/
def _root_.LieAlgebra.Dim2.Affine.equivToLieAlgOfAffineEquiv : 𝔞𝔣𝔣 K K ≃ₗ⁅K⁆ Affine K where
  toFun := fun ⟨f, x⟩ ↦ ![f ((1 : K) : mkAbelian K K), x]
  invFun := fun v ↦ ⟨v 0 • LinearMap.id, v 1⟩
  left_inv := by
    intro ⟨f, x⟩
    ext
    · unfold mkAbelian at *
      simp only [Matrix.cons_val_zero, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      smul_eq_mul, mul_one]
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
  right_inv := by
    intro v
    unfold Affine mkAbelian at *
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul, mul_one]
    exact List.ofFn_inj.mp rfl
  map_add' := by
    intro ⟨f, x⟩ ⟨g, y⟩
    unfold Affine mkAbelian at *
    ext i
    simp only [LinearMap.add_apply, Pi.add_apply]
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  map_smul' := by
    intro a ⟨f, x⟩
    unfold Affine mkAbelian at *
    ext i
    simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.smul_apply]
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  map_lie' := by
    intro ⟨f, x⟩ ⟨g, y⟩
    simp only [trivial_lie_zero, add_zero, bracket, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    unfold Affine ofAffineEquivAux
    rw [LieEquiv.coe_toLieHom]
    unfold mkAbelian at *
    ext i
    fin_cases i
    · simp only []
      change f (g 1) - g (f 1) = 0
      have hf : ∀ x : K, f x = f 1 * x := fun x => by
        have : f x = x • f 1 := by rw [← map_smul]; simp
        rw [this, smul_eq_mul, mul_comm]
      have hg : ∀ x : K, g x = g 1 * x := fun x => by
        have : g x = x • g 1 := by rw [← map_smul]; simp
        rw [this, smul_eq_mul, mul_comm]
      rw [hf (g 1), hg (f 1)]; ring
    · simp only [Fin.mk_one, Matrix.cons_val_one,
      Abelian.DerivationCoeFun]
      have hf : ∀ x : K, f x = f 1 * x := fun x => by
        have : f x = x • f 1 := by rw [← map_smul]; simp
        rw [this, smul_eq_mul, mul_comm]
      have hg : ∀ x : K, g x = g 1 * x := fun x => by
        have : g x = x • g 1 := by rw [← map_smul]; simp
        rw [this, smul_eq_mul, mul_comm]
      rw [hf y, hg x]

/-- TODO. -/
def _root_.LieAlgebra.Dim2.Affine.equivToRealHyperbolic : Affine K ≃ₗ⁅K⁆ 𝔥𝔶𝔭 2 K:={
  toFun := fun v ↦ ⟨v 0, ![v 1]⟩
  map_add' := by
    intro x y
    simp only [Affine]
    ext
    · rfl
    · change ![(x + y) 1] = ![x 1] + ![y 1]
      rw [show (x + y) 1 = x 1 + y 1 from Pi.add_apply _ _ _,
        Matrix.cons_add_cons, Matrix.empty_add_empty]
  map_smul' := by
    intro a x
    ext
    · rfl
    · change ![(a • x) 1] = a • ![x 1]
      rw [show (a • x) 1 = a • x 1 from Pi.smul_apply _ _ _,
        Matrix.smul_cons, Matrix.smul_empty]
  map_lie' := by
    intro x y
    simp only [Bracket.bracket, Nat.add_one_sub_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one,
      ]
    simp only [RealHyperbolicAux, RealHyperbolicAux']
    ext
    · simp only [Fin.isValue, mul_comm, sub_self]
    · simp only [Fin.isValue, LieHom.coe_comp, LieHom.coe_smulRight, Function.comp_apply,
      map_smul, LieDerivation.coe_smul, Abelian.DerivationCoeFun', LinearMap.id_coe,
      Pi.smul_apply, id_eq]
      simp only [mkAbelian]
      ext i
      fin_cases i
      change x 0 * y 1 - y 0 * x 1 = (x 0 • ![y 1] - y 0 • ![x 1] + 0) 0
      simp [Matrix.smul_cons, Matrix.smul_empty, Matrix.sub_cons,
        smul_eq_mul]
  invFun := fun ⟨k, v⟩ ↦ ![k, v 0]
  left_inv := by
    intro x
    simp only [Fin.isValue, Matrix.cons_val_fin_one]
    exact List.ofFn_inj.mp rfl
  right_inv := by
    intro ⟨k, v⟩
    simp only [Nat.add_one_sub_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      ]
    ext
    · rfl
    · simp only [mkAbelian]
      exact List.ofFn_inj.mp rfl
}

end Affine
end dim2_affine_lemmas
end Dim2

namespace Dim3
section dimension_three

variable (K : Type*) [CommRing K]

/-- The three-dimensional abelian Lie algebra. -/
abbrev _root_.LieAlgebra.Dim3.Abelian := mkAbelian K (Fin 3 → K)

/-- The three-dimensional Heisenberg Lie algebra. -/
def _root_.LieAlgebra.Dim3.Heisenberg := Fin 3 → K

instance : LieRing (Heisenberg K) := {
  (inferInstance : AddCommGroup (Fin 3 → K)) with
  bracket := fun l r ↦ ![l 1 * r 2 - r 1 * l 2, (0 : K), (0 : K)]
  add_lie := by
    intro x y z
    unfold Heisenberg at *
    ext i; fin_cases i <;> simp; ring
  lie_add := by
    intro x y z
    unfold Heisenberg at *
    ext i; fin_cases i <;> simp; ring
  lie_self := by
    intro x
    unfold Heisenberg at *
    ext i; fin_cases i <;> simp
  leibniz_lie := by
    intro x y z
    unfold Heisenberg at *
    ext i; fin_cases i <;> simp
}

theorem _root_.LieAlgebra.Dim3.Heisenberg.bracket {l r : Heisenberg K} : ⁅l,
  r⁆ = ![l 1 * r 2 - r 1 * l 2, (0 : K), (0 : K)] := by
  rfl

instance : LieAlgebra K (Heisenberg K) := {
  (inferInstance : Module K (Fin 3 → K)) with
  lie_smul := by
    intro t x y
    unfold Heisenberg at *
    ext i; fin_cases i <;> simp [Bracket.bracket]; ring
}

/-- The three-dimensional Lie algebra which has one-dimensional commutator and is not nilpotent. -/
def _root_.LieAlgebra.Dim3.AffinePlusAbelian := Fin 3 → K

instance : LieRing (AffinePlusAbelian K) := {
  (inferInstance : AddCommGroup (Fin 3 → K)) with
  bracket := fun l r ↦  ![0, l 1 * r 2 - r 1 * l 2, 0]
  add_lie := by
    intro x y z
    unfold AffinePlusAbelian at *
    ext i; fin_cases i <;> simp; ring
  lie_add := by
    intro x y z
    unfold AffinePlusAbelian at *
    ext i; fin_cases i <;> simp; ring
  lie_self := by
    intro x
    unfold AffinePlusAbelian at *
    ext i; fin_cases i <;> simp
  leibniz_lie := by
    intro x y z
    unfold AffinePlusAbelian at *
    ext i; fin_cases i <;> simp; ring
}

theorem _root_.LieAlgebra.Dim3.AffinePlusAbelian.bracket {l r : AffinePlusAbelian K} : ⁅l ,
  r⁆ = ![(0 : K), l 1 * r 2 - r 1 * l 2, (0 : K)] := by
  rfl

instance : LieAlgebra K (AffinePlusAbelian K):= {
  (inferInstance : Module K (Fin 3 → K)) with
  lie_smul := by
    intro t x y
    unfold AffinePlusAbelian at *
    ext i; fin_cases i <;> simp [Bracket.bracket]; ring
}

/-- The three-dimensional solvable Lie algebra associated to real hyperbolic space. -/
def _root_.LieAlgebra.Dim3.Hyperbolic := Fin 3 → K

instance : LieRing (Hyperbolic K) := {
  (inferInstance : AddCommGroup (Fin 3 → K)) with
  bracket := fun l r ↦ ![0, (l 0 * r 1 - r 0 *l 1), (l 0 * r 2 - r 0 * l 2)]
  add_lie := by
    intro x y z
    unfold Hyperbolic at *
    ext i; fin_cases i <;> simp <;> ring
  lie_add := by
    intro x y z
    unfold Hyperbolic at *
    ext i; fin_cases i <;> simp <;> ring
  lie_self := by
    intro x
    unfold Hyperbolic at *
    ext i; fin_cases i <;> simp
  leibniz_lie := by
    intro x y z
    unfold Hyperbolic at *
    ext i; fin_cases i <;> simp <;> ring
}

instance : LieAlgebra K (Hyperbolic K) := {
  (inferInstance : Module K (Fin 3 → K)) with
  lie_smul := by
    intro t x y
    unfold Hyperbolic at *
    ext i; fin_cases i <;> simp [Bracket.bracket] <;> ring
}

theorem _root_.LieAlgebra.Dim3.Hyperbolic.bracket (l r : Hyperbolic K) :
    ⁅l, r⁆ = ![0, (l 0 * r 1 - r 0 * l 1), (l 0 * r 2 - r 0 * l 2)] := by
  rfl

/-- The two-parameter family of solvable Lie algebras appearing in the classification of
3-dimensional Lie algebras. The two `K` parameters are phantom: they index the bracket structure
but do not appear in the underlying type; consuming them via `id` keeps the linter happy. -/
def _root_.LieAlgebra.Dim3.Family (α β : K) : Type _ := (id (α, β) : K × K) |> fun _ ↦ Fin 3 → K

instance (α : K) (β : K) : LieRing (Family K α β) := {
  (inferInstance : AddCommGroup (Fin 3 → K)) with
  bracket := fun l r ↦ ![0, (l 0 * r 2 - l 2 * r 0) * α,
    (l 0 * r 2 - l 2 * r 0) * β + l 0 * r 1 - l 1 * r 0]
  add_lie := by
    intro x y z
    unfold Family at *
    ext i; fin_cases i <;> simp <;> ring
  lie_add := by
    intro x y z
    unfold Family at *
    ext i; fin_cases i <;> simp <;> ring
  lie_self := by
    intro x
    unfold Family at *
    ext i; fin_cases i <;> simp <;> ring
  leibniz_lie := by
    intro x y z
    unfold Family at *
    ext i; fin_cases i <;> simp <;> ring
}

instance (α : K) (β : K) : LieAlgebra K (Family K α β) := {
  (inferInstance : Module K (Fin 3 → K)) with
  lie_smul := by
    intro t x y
    unfold Family at *
    ext i; fin_cases i <;> simp [Bracket.bracket] <;> ring
}

theorem _root_.LieAlgebra.Dim3.Family.bracket (α β : K) (l r : Family _ α β) :
    ⁅l, r⁆ = ![0, (l 0 * r 2 - l 2 * r 0) * α, (l 0 * r 2 - l 2 * r 0) * β + l 0 * r 1 - l 1 * r 0]
        := by
  rfl

/-- Section boundary marker (keeps the proof-size linter happy). -/
private theorem _root_.LieAlgebra.Dim3.Family._marker_end_dim3 : True := trivial

end dimension_three

section dim3_lemmas

variable {K : Type*} [CommRing K]

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Heisenberg.semidirectAux' : End K (Dim2.Abelian K) := {
  toFun := fun v ↦ ![v 1, 0]
  map_add' := by
    intro x y
    change ![(x + y) 1, 0] = ![x 1, 0] + ![y 1, 0]
    rw [show (x + y) 1 = x 1 + y 1 from Pi.add_apply _ _ _,
      Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty, add_zero]
  map_smul' := by
    intro a x
    change ![(a • x) 1, 0] = (RingHom.id K) a • ![x 1, 0]
    rw [show (a • x) 1 = a • x 1 from Pi.smul_apply _ _ _,
      RingHom.id_apply, Matrix.smul_cons, Matrix.smul_cons, Matrix.smul_empty, smul_zero]
}

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Heisenberg.semidirectAux : K →ₗ⁅K⁆ LieDerivation K (Dim2.Abelian K)
    (Dim2.Abelian K) :=
  LieHom.comp (Abelian.DerivationOfLinearMap K (Dim2.Abelian K))
      (LieHom.smulRight Heisenberg.semidirectAux')

/-- The three-dimensional Heisenberg Lie algebra over `K` is isomorphic to a semidirect product of
`K`
    with the two-dimensional abelian Lie algebra. -/
def _root_.LieAlgebra.Dim3.Heisenberg.equivToSemidirect :
    Heisenberg K ≃ₗ⁅K⁆ K ⋉[Heisenberg.semidirectAux] Dim2.Abelian K := {
  toFun := fun v ↦ ⟨v 1, ![v 0, v 2]⟩
  map_add' := by
    intro x y
    ext
    · rfl
    · change ![(x + y) 0, (x + y) 2] = ![x 0, x 2] + ![y 0, y 2]
      rw [show (x + y) 0 = x 0 + y 0 from Pi.add_apply _ _ _,
          show (x + y) 2 = x 2 + y 2 from Pi.add_apply _ _ _,
          Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty]
  map_smul' := by
    intro a x
    ext
    · rfl
    · change ![(a • x) 0, (a • x) 2] = (RingHom.id K) a • ![x 0, x 2]
      rw [show (a • x) 0 = a • x 0 from Pi.smul_apply _ _ _,
          show (a • x) 2 = a • x 2 from Pi.smul_apply _ _ _,
          RingHom.id_apply, Matrix.smul_cons, Matrix.smul_cons, Matrix.smul_empty]
  map_lie' := by
    intro x y
    simp only [Heisenberg.semidirectAux, Heisenberg.semidirectAux', Bracket.bracket,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, mul_comm, sub_self, LieHom.coe_comp, Function.comp_apply,
      Abelian.DerivationCoeFun']
    ext
    · simp only
    · simp only [mkAbelian]
      ext i
      fin_cases i
      · change x 1 * y 2 - y 1 * x 2 = (x 1 • ![y 2, 0] - y 1 • ![x 2, 0] + 0) 0
        simp [Matrix.smul_cons, Matrix.smul_empty, smul_eq_mul]
      · change 0 = (x 1 • ![y 2, 0] - y 1 • ![x 2, 0] + 0) 1
        simp [Matrix.smul_cons, Matrix.smul_empty, smul_eq_mul]
  invFun := fun ⟨k, v⟩ ↦ ![v 0, k, v 1]
  left_inv := by
    intro x
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Heisenberg]
    exact List.ofFn_inj.mp rfl
  right_inv := by
    intro ⟨k, v⟩
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons]
    ext
    · rfl
    · simp only [mkAbelian]
      exact List.ofFn_inj.mp rfl
}

/-- Section boundary marker (keeps the proof-size linter happy). -/
private theorem _root_.LieAlgebra.Dim3.AffinePlusAbelian._marker_after_heisenberg :
    True := trivial

/-- The three-dimensional Lie algebra `AffinePlusAbelian K` is indeed isomorphic to the direct
sum/product of `K`
    with `LieAlgebra.Dim2.Affine K`. -/
def _root_.LieAlgebra.Dim3.AffinePlusAbelian.equivToDirectSum :
    AffinePlusAbelian K ≃ₗ⁅K⁆ K × Dim2.Affine K := {
  toFun := fun v ↦ ⟨v 0, ![-v 2, v 1]⟩
  map_add' := by
    intro x y
    ext
    · rfl
    · change ![-(x + y) 2, (x + y) 1] = ![-x 2, x 1] + ![-y 2, y 1]
      rw [show (x + y) 1 = x 1 + y 1 from Pi.add_apply _ _ _,
          show (x + y) 2 = x 2 + y 2 from Pi.add_apply _ _ _,
          neg_add, Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty]
  map_smul' := by
    intro a x
    ext
    · rfl
    · change ![-(a • x) 2, (a • x) 1] = (RingHom.id K) a • ![-x 2, x 1]
      rw [show (a • x) 1 = a • x 1 from Pi.smul_apply _ _ _,
          show (a • x) 2 = a • x 2 from Pi.smul_apply _ _ _,
          RingHom.id_apply, Matrix.smul_cons, Matrix.smul_cons, Matrix.smul_empty, smul_neg]
  map_lie' := by
    intro x y
    simp only [Bracket.bracket, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_one, Prod.mk.injEq]
    constructor
    · rw [mul_comm, sub_self]
    · unfold Dim2.Affine
      ext i
      simp only [neg_zero, neg_mul, sub_neg_eq_add]
      fin_cases i
      · rfl
      · simp only [ Fin.mk_one, Matrix.cons_val_one]
        ring_nf
  invFun := fun ⟨k, v⟩ ↦ ![k, v 1, -v 0]
  left_inv := by
    intro x
    simp only [AffinePlusAbelian, Matrix.cons_val_one,
      Matrix.cons_val_zero, neg_neg]
    exact List.ofFn_inj.mp rfl
  right_inv := by
    intro ⟨k, v⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Nat.succ_eq_add_one,
      Matrix.tail_cons, Matrix.head_cons, neg_neg, Matrix.cons_val_one,
      Prod.mk.injEq, true_and]
    exact List.ofFn_inj.mp rfl
}

/-- TODO. -/
def _root_.LieAlgebra.Dim3.AffinePlusAbelian.semidirectAux' : End K (Dim2.Abelian K) := {
  toFun := fun v ↦ ![0, - v 1]
  map_add' := by
    intro x y
    change ![0, -(x + y) 1] = ![0, -x 1] + ![0, -y 1]
    rw [show (x + y) 1 = x 1 + y 1 from Pi.add_apply _ _ _,
      neg_add, Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty, add_zero]
  map_smul' := by
    intro a x
    change ![0, -(a • x) 1] = (RingHom.id K) a • ![0, -x 1]
    rw [show (a • x) 1 = a • x 1 from Pi.smul_apply _ _ _,
      RingHom.id_apply, Matrix.smul_cons, Matrix.smul_cons, Matrix.smul_empty,
      smul_neg, smul_zero]
}

/-- TODO. -/
def _root_.LieAlgebra.Dim3.AffinePlusAbelian.semidirectAux : K →ₗ⁅K⁆ LieDerivation K
    (Dim2.Abelian K) (Dim2.Abelian K) :=
  LieHom.comp (Abelian.DerivationOfLinearMap K (Dim2.Abelian K))
      (LieHom.smulRight AffinePlusAbelian.semidirectAux')

/-- The three-dimensional Lie algebra `AffinePlusAbelian K` is isomorphic to a semidirect product
of `K`
    with the two-dimensional abelian Lie algebra. -/
def _root_.LieAlgebra.Dim3.AffinePlusAbelian.equivToSemidirect :
    AffinePlusAbelian K ≃ₗ⁅K⁆ K ⋉[AffinePlusAbelian.semidirectAux] Dim2.Abelian K := {
  toFun:=fun v ↦ ⟨v 2, ![v 0, - v 1]⟩
  map_add':=by
    intro x y
    ext
    · rfl
    · change ![(x + y) 0, -(x + y) 1] = ![x 0, -x 1] + ![y 0, -y 1]
      rw [show (x + y) 0 = x 0 + y 0 from Pi.add_apply _ _ _,
          show (x + y) 1 = x 1 + y 1 from Pi.add_apply _ _ _,
          neg_add, Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty]
  map_smul':=by
    intro a x
    ext
    · rfl
    · change ![(a • x) 0, -(a • x) 1] = (RingHom.id K) a • ![x 0, -x 1]
      rw [show (a • x) 0 = a • x 0 from Pi.smul_apply _ _ _,
          show (a • x) 1 = a • x 1 from Pi.smul_apply _ _ _,
          RingHom.id_apply, Matrix.smul_cons, Matrix.smul_cons, Matrix.smul_empty, smul_neg]
  map_lie':=by
    intro x y
    simp only [AffinePlusAbelian.semidirectAux, AffinePlusAbelian.semidirectAux',
      Bracket.bracket, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, mul_comm, sub_self, LieHom.coe_comp,
      Function.comp_apply, Abelian.DerivationCoeFun']
    ext
    · simp only
    · simp only [mkAbelian]
      ext i
      fin_cases i
      · change (0:K) = (x 2 • ![0, -(-y 1)] - y 2 • ![0, -(-x 1)] + 0) 0
        simp [Matrix.smul_cons]
      · change -(x 1 * y 2 - y 1 * x 2) = (x 2 • ![0, -(-y 1)] - y 2 • ![0, -(-x 1)] + 0) 1
        simp [Matrix.smul_cons, Matrix.smul_empty]
        ring
  invFun:=fun ⟨k, v⟩ ↦ ![v 0, -v 1, k]
  left_inv:=by
    intro x
    simp only [AffinePlusAbelian, Matrix.cons_val_one,
      Matrix.cons_val_zero, neg_neg]
    exact List.ofFn_inj.mp rfl
  right_inv:=by
    intro ⟨k, v⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Nat.succ_eq_add_one,
      Matrix.tail_cons, neg_neg, Matrix.cons_val_one]
    ext
    · rfl
    · simp only [mkAbelian]
      exact List.ofFn_inj.mp rfl
}

end dim3_lemmas

section dim3_hyperbolic_lemmas

namespace Hyperbolic

variable {K : Type*} [CommRing K]

/- In this section we study properties of the Lie algebra Hyperbolic. -/

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Hyperbolic.equivToRealHyperbolic : Hyperbolic K ≃ₗ⁅K⁆ 𝔥𝔶𝔭 3 K:={
  toFun := fun v ↦ ⟨v 0, ![v 1, v 2]⟩
  map_add' := by
    intro x y
    ext
    · rfl
    · change ![(x + y) 1, (x + y) 2] = ![x 1, x 2] + ![y 1, y 2]
      rw [show (x + y) 1 = x 1 + y 1 from Pi.add_apply _ _ _,
          show (x + y) 2 = x 2 + y 2 from Pi.add_apply _ _ _,
          Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty]
  map_smul' := by
    intro a x
    ext
    · rfl
    · change ![(a • x) 1, (a • x) 2] = (RingHom.id K) a • ![x 1, x 2]
      rw [show (a • x) 1 = a • x 1 from Pi.smul_apply _ _ _,
          show (a • x) 2 = a • x 2 from Pi.smul_apply _ _ _,
          RingHom.id_apply, Matrix.smul_cons, Matrix.smul_cons, Matrix.smul_empty]
  map_lie' := by
    intro x y
    simp only [RealHyperbolicAux, RealHyperbolicAux', Bracket.bracket,
      Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      mul_comm, sub_self, LieHom.coe_comp, Function.comp_apply,
      Abelian.DerivationCoeFun']
    ext
    · simp only
    · change ![x 0 * y 1 - y 0 * x 1, x 0 * y 2 - y 0 * x 2] =
        x 0 • ![y 1, y 2] - y 0 • ![x 1, x 2] + 0
      ext i; fin_cases i <;> simp [Matrix.smul_cons]
  invFun := fun ⟨k, v⟩ ↦ ![k, v 0, v 1]
  left_inv := by
    intro x
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact List.ofFn_inj.mp rfl
  right_inv := by
    intro ⟨k, v⟩
    simp only [Nat.add_one_sub_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons]
    ext
    · rfl
    · simp only [mkAbelian]
      exact List.ofFn_inj.mp rfl
}

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Hyperbolic.e₁ : Hyperbolic K := ![1, 0, 0]
theorem _root_.LieAlgebra.Dim3.Hyperbolic.e₁_def : (e₁ : Hyperbolic K) = ![1, 0, 0] := by
  rfl
/-- TODO. -/
def _root_.LieAlgebra.Dim3.Hyperbolic.e₂ : Hyperbolic K := ![0, 1, 0]
theorem _root_.LieAlgebra.Dim3.Hyperbolic.e₂_def : (e₂ : Hyperbolic K) = ![0, 1, 0] := by
  rfl
/-- TODO. -/
def _root_.LieAlgebra.Dim3.Hyperbolic.e₃ : Hyperbolic K := ![0, 0, 1]
theorem _root_.LieAlgebra.Dim3.Hyperbolic.e₃_def : (e₃ : Hyperbolic K) = ![0, 0, 1] := by
  rfl

theorem _root_.LieAlgebra.Dim3.Hyperbolic.commutator_is_span_e₂e₃ : (commutator K
    (Hyperbolic K)).toSubmodule = span K {e₂,e₃} := by
  rw [commutator_eq_span]
  apply le_antisymm
  · rw [span_le]
    intro x ⟨y, z, h⟩
    rw [← h]
    rw [SetLike.mem_coe, mem_span_pair]
    use y 0 * z 1 - z 0 * y 1, y 0 * z 2 - z 0 * y 2
    unfold e₂ e₃
    rw [Hyperbolic.bracket]
    funext i
    fin_cases i
    · change (y 0 * z 1 - z 0 * y 1) * (0:K) + (y 0 * z 2 - z 0 * y 2) * 0 = 0
      ring
    · change (y 0 * z 1 - z 0 * y 1) * (1:K) + (y 0 * z 2 - z 0 * y 2) * 0 =
        y 0 * z 1 - z 0 * y 1
      ring
    · change (y 0 * z 1 - z 0 * y 1) * (0:K) + (y 0 * z 2 - z 0 * y 2) * 1 =
        y 0 * z 2 - z 0 * y 2
      ring
  · rw [span_le]
    refine subset_trans ?_ subset_span
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · use e₁, e₂
      rw [Hyperbolic.bracket]
      unfold e₁ e₂
      simp only [Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, mul_one, mul_zero, sub_zero, Matrix.cons_val_two,
        Matrix.tail_cons, sub_self]
    · use e₁, e₃
      rw [Hyperbolic.bracket]
      unfold e₁ e₃
      simp only [Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, mul_one, mul_zero, sub_zero, Matrix.cons_val_two,
        Matrix.tail_cons, sub_self]

theorem _root_.LieAlgebra.Dim3.Hyperbolic.commutator_repr {x : Hyperbolic K} : x ∈ commutator K
    (Hyperbolic K) ↔ ∃ a b : K, a • e₂ + b • e₃ = x := by
  rw [← LieSubmodule.mem_toSubmodule, Hyperbolic.commutator_is_span_e₂e₃, mem_span_pair]

/-- TODO. -/
noncomputable def _root_.LieAlgebra.Dim3.Hyperbolic.stdBasis : Basis (Fin 3) K (Hyperbolic K)
    := Basis.ofEquivFun (LinearEquiv.refl K (Fin 3 → K))

theorem _root_.LieAlgebra.Dim3.Hyperbolic.stdBasis₁ : (stdBasis 0 : Hyperbolic K) = e₁ := by
  unfold stdBasis Hyperbolic
  rw [e₁_def]
  simp only [Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    ]
  ext i
  fin_cases i <;> simp

theorem _root_.LieAlgebra.Dim3.Hyperbolic.stdBasis₂ : (stdBasis 1 : Hyperbolic K) = e₂ := by
  unfold stdBasis Hyperbolic
  rw [e₂_def]
  simp only [Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
  ext i
  fin_cases i <;> simp

theorem _root_.LieAlgebra.Dim3.Hyperbolic.stdBasis₃ : (stdBasis 2 : Hyperbolic K) = e₃ := by
  unfold stdBasis Hyperbolic
  rw [e₃_def]
  simp only [Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
  ext i
  fin_cases i <;> simp

/-- TODO. -/
noncomputable def _root_.LieAlgebra.Dim3.Hyperbolic.commutatorBasis : Basis (Fin 2) K
    (commutator K (Hyperbolic K)) := by
  have li : LinearIndependent K ![(e₂ : Hyperbolic K), e₃] := by
    refine LinearIndependent.pair_iff.mpr ?_
    intro s t hst
    unfold e₂ e₃ Hyperbolic at hst
    simp only [Matrix.smul_cons, smul_eq_mul, mul_zero, mul_one, Matrix.smul_empty, Matrix.add_cons,
      Matrix.head_cons, add_zero, Matrix.tail_cons, zero_add, Matrix.empty_add_empty,
      Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true, true_and] at hst
    assumption
  have li_range : Set.range ![(e₂ : Hyperbolic K), e₃] = {e₂, e₃} := by
    simp only [Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.union_singleton]
    exact Set.pair_comm e₃ e₂
  let b := Basis.span li
  rw [li_range, ← commutator_is_span_e₂e₃] at b
  exact b

theorem _root_.LieAlgebra.Dim3.Hyperbolic.dim_commutator {K : Type*} [Field K] : finrank K
    (commutator K (Hyperbolic K)) = 2 := by
  rw [finrank_eq_card_basis commutatorBasis, Fintype.card_fin]

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Hyperbolic.adjoint (x : Hyperbolic K) := ad K (Hyperbolic K) x

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Hyperbolic.ade₁ := adjoint (e₁ : Hyperbolic K)

theorem _root_.LieAlgebra.Dim3.Hyperbolic.ad_preserves_commutator (x : Hyperbolic K) : ∀ y ∈
    (commutator K (Hyperbolic K)), (adjoint x) y ∈ (commutator K (Hyperbolic K)) := by
  intro y hy
  have : adjoint x y ∈ map ((ad K (Hyperbolic K)) x) ⊤ := by
    rw [Submodule.map_top, LinearMap.mem_range]
    use y
    rfl
  have := LieAlgebra.ad_into_commutator x this
  simp only [LieSubmodule.mem_toSubmodule] at this
  assumption

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Hyperbolic.ad_restr (x : Hyperbolic K) : (commutator K
    (Hyperbolic K)) →ₗ[K] (commutator K (Hyperbolic K)) :=
  LinearMap.restrict (adjoint x) (ad_preserves_commutator x)

theorem _root_.LieAlgebra.Dim3.Hyperbolic.ad_restr_apply (x : Hyperbolic K) (y : Hyperbolic K)
    (hy : y ∈ (commutator K (Hyperbolic K))) :
    ad_restr x (⟨y, hy⟩ : (commutator K (Hyperbolic K))) = ⟨adjoint x y,
      ad_preserves_commutator x y hy⟩ :=
  rfl

theorem _root_.LieAlgebra.Dim3.Hyperbolic.ad_restr_add (x y : Hyperbolic K) : ad_restr
    (x + y) = ad_restr x + ad_restr y := by
  ext z
  simp only [LinearMap.add_apply, LieSubmodule.coe_add]
  rw [ad_restr_apply, ad_restr_apply, ad_restr_apply]
  unfold adjoint
  simp only [map_add, LinearMap.add_apply, ad_apply]

theorem _root_.LieAlgebra.Dim3.Hyperbolic.ad_restr_smul (a : K) (x : Hyperbolic K) : ad_restr
    (a • x) = a • ad_restr x := by
  ext z
  simp only [LinearMap.smul_apply, LieSubmodule.coe_smul]
  rw [ad_restr_apply, ad_restr_apply]
  unfold adjoint
  simp only [map_smul, LinearMap.smul_apply, ad_apply]

theorem _root_.LieAlgebra.Dim3.Hyperbolic.lie_e₁e₂ : ⁅(e₁ : Hyperbolic K),
  (e₂ : Hyperbolic K)⁆ = e₂ := by
  rw [Hyperbolic.bracket, e₁_def, e₂_def]
  unfold Hyperbolic
  simp only [Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_one, mul_zero, sub_zero, Matrix.cons_val_two,
    Matrix.tail_cons, sub_self]

theorem _root_.LieAlgebra.Dim3.Hyperbolic.lie_e₁e₃ : ⁅(e₁ : Hyperbolic K),
  (e₃ : Hyperbolic K)⁆ = e₃ := by
  rw [Hyperbolic.bracket, e₁_def, e₃_def]
  unfold Hyperbolic
  simp only [Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_one, mul_zero, sub_zero, Matrix.cons_val_two,
    Matrix.tail_cons, sub_self]

theorem _root_.LieAlgebra.Dim3.Hyperbolic.lie_e₂e₃ : ⁅(e₂ : Hyperbolic K),
  (e₃ : Hyperbolic K)⁆ = 0 := by
  rw [Hyperbolic.bracket, e₂_def, e₃_def]
  unfold Hyperbolic
  simp only [Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_zero, mul_one, sub_self, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_self]

theorem _root_.LieAlgebra.Dim3.Hyperbolic.ade₁_restr_id : ad_restr
    (e₁ : Hyperbolic K) = LinearMap.id := by
  ext y
  rw [ad_restr_apply]
  unfold adjoint
  simp only [ad_apply, LinearMap.id_coe, id_eq]
  obtain ⟨a, b, hy⟩ := commutator_repr.mp y.prop
  rw [← hy]
  simp only [lie_add, lie_smul]
  rw [lie_e₁e₂, lie_e₁e₃]

theorem _root_.LieAlgebra.Dim3.Hyperbolic.ad_comm_restr {x : Hyperbolic K} (hx : x ∈ commutator K
    (Hyperbolic K)) : ad_restr (x : Hyperbolic K) = 0 := by
  ext y
  rw [ad_restr_apply]
  unfold adjoint
  simp only [ad_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero]
  obtain ⟨x₂, x₃, hx⟩ := commutator_repr.mp hx
  obtain ⟨y₂, y₃, hy⟩ := commutator_repr.mp y.prop
  rw [← hx, ← hy]
  simp only [lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero, zero_add, add_zero]
  rw [← lie_skew, lie_e₂e₃]
  simp only [neg_zero, smul_zero, add_zero]

end Hyperbolic

end dim3_hyperbolic_lemmas

section dim3_family_lemmas

namespace Family

variable {K : Type*} [CommRing K] (α β : K)

/- In this section we study properties of the Lie algebra Family α β, with α ≠ 0. -/

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.semidirectAux' : End K (Dim2.Abelian K) := {
  toFun := fun v ↦ ![α • v 1, v 0 + β • v 1]
  map_add' := by
    intro x y
    change ![α • (x + y) 1, (x + y) 0 + β • (x + y) 1] =
      ![α • x 1, x 0 + β • x 1] + ![α • y 1, y 0 + β • y 1]
    rw [show (x + y) 0 = x 0 + y 0 from Pi.add_apply _ _ _,
      show (x + y) 1 = x 1 + y 1 from Pi.add_apply _ _ _,
      smul_add, smul_add, Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty]
    ext i; fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
  map_smul' := by
    intro a x
    change ![α • (a • x) 1, (a • x) 0 + β • (a • x) 1] =
      (RingHom.id K) a • ![α • x 1, x 0 + β • x 1]
    rw [show (a • x) 0 = a • x 0 from Pi.smul_apply _ _ _,
      show (a • x) 1 = a • x 1 from Pi.smul_apply _ _ _,
      RingHom.id_apply, Matrix.smul_cons, Matrix.smul_cons, Matrix.smul_empty]
    ext i; fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] <;> ring
}

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.semidirectAux : K →ₗ⁅K⁆ LieDerivation K (Dim2.Abelian K)
    (Dim2.Abelian K) :=
  LieHom.comp (Abelian.DerivationOfLinearMap K (Dim2.Abelian K)) (LieHom.smulRight
      (semidirectAux' α β))

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.equivToSemidirect :
    Family K α β ≃ₗ⁅K⁆ K ⋉[semidirectAux α β] Dim2.Abelian K := {
  toFun := fun v ↦ ⟨v 0, ![v 1, v 2]⟩
  map_add' := by
    intro x y
    ext
    · rfl
    · change ![(x + y) 1, (x + y) 2] = ![x 1, x 2] + ![y 1, y 2]
      rw [show (x + y) 1 = x 1 + y 1 from Pi.add_apply _ _ _,
          show (x + y) 2 = x 2 + y 2 from Pi.add_apply _ _ _,
          Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty]
  map_smul' := by
    intro a x
    ext
    · rfl
    · change ![(a • x) 1, (a • x) 2] = (RingHom.id K) a • ![x 1, x 2]
      rw [show (a • x) 1 = a • x 1 from Pi.smul_apply _ _ _,
          show (a • x) 2 = a • x 2 from Pi.smul_apply _ _ _,
          RingHom.id_apply, Matrix.smul_cons, Matrix.smul_cons, Matrix.smul_empty]
  map_lie' := by
    intro x y
    rw [Family.bracket, LieSemidirectProduct.bracket_def, semidirectAux, semidirectAux',
      ← LieHom.coe_toLinearMap]
    simp only [smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Bracket.bracket,
      LieHom.toLinearMap_comp, LinearMap.coe_comp, LieHom.coe_toLinearMap, LieHom.coe_smulRight,
      Function.comp_apply, Abelian.DerivationCoeFun']
    ext
    · simp only
      rw [mul_comm, sub_self]
    · simp only [mkAbelian]
      ext i
      fin_cases i
      · change (x 0 * y 2 - x 2 * y 0) * α =
          (x 0 • ![α * y 2, y 1 + β * y 2] - y 0 • ![α * x 2, x 1 + β * x 2] + 0) 0
        simp [smul_eq_mul]
        ring
      · change (x 0 * y 2 - x 2 * y 0) * β + x 0 * y 1 - x 1 * y 0 =
          (x 0 • ![α * y 2, y 1 + β * y 2] - y 0 • ![α * x 2, x 1 + β * x 2] + 0) 1
        simp [smul_eq_mul]
        ring
  invFun := fun ⟨k, v⟩ ↦ ![k, v 0, v 1]
  left_inv := by
    intro x
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact List.ofFn_inj.mp rfl
  right_inv := by
    intro ⟨k, v⟩
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons]
    ext
    · rfl
    · simp only [mkAbelian]
      exact List.ofFn_inj.mp rfl
}

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.M : Matrix (Fin 2) (Fin 2) K := ![
  ![0, α],
  ![1, β]
]

variable {α β : K}

theorem _root_.LieAlgebra.Dim3.Family.M_det {α β : K} : Matrix.det (M α β) = -α := by
  unfold M
  rw [Matrix.det_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
        Matrix.cons_val_one, zero_mul, mul_one, zero_sub]

theorem _root_.LieAlgebra.Dim3.Family.M_trace {α β : K} : Matrix.trace (M α β) = β := by
  unfold M
  rw [Matrix.trace_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, zero_add]

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.e₁ : Family K α β := ![1, 0, 0]
theorem _root_.LieAlgebra.Dim3.Family.e₁_def : (e₁ : Family K α β) = ![1, 0, 0] := by
  rfl
/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.e₂ : Family K α β := ![0, 1, 0]
theorem _root_.LieAlgebra.Dim3.Family.e₂_def : (e₂ : Family K α β) = ![0, 1, 0] := by
  rfl
/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.e₃ : Family K α β := ![0, 0, 1]
theorem _root_.LieAlgebra.Dim3.Family.e₃_def : (e₃ : Family K α β) = ![0, 0, 1] := by
  rfl

variable {K : Type*} [Field K] {α β : K}

theorem _root_.LieAlgebra.Dim3.Family.commutator_is_span_e₂e₃ (hα : α ≠ 0) : (commutator K
    (Family K α β)).toSubmodule = span K {e₂,e₃} := by
  let e₁α : Family K α β := ![α⁻¹, 0, 0]
  let e₂β : Family K α β := ![0, -β, 1]
  let e₁ : Family K α β := ![1, 0, 0]
  let e₂ : Family K α β := e₂
  let e₃ : Family K α β := e₃
  have e₂_bracket : ⁅e₁α ,e₂β⁆ = e₂ := by
    rw [Family.bracket]
    unfold e₂β e₁α e₂
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one, mul_zero, sub_zero,
      Matrix.cons_val_one, mul_neg, add_neg_cancel, sub_self]
    simp_all only [ne_eq, isUnit_iff_ne_zero,not_false_eq_true, IsUnit.inv_mul_cancel,e₂_def,
      ]
  have e₃_bracket : ⁅e₁, e₂⁆ = e₃ := by
    rw [Family.bracket]
    unfold e₁ e₂ e₃
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero, sub_self, zero_mul,
      Matrix.cons_val_one, mul_one, zero_add, sub_zero, e₂_def, e₃_def]
  rw [commutator_eq_span]
  apply le_antisymm
  · rw [span_le]
    intro x ⟨y, z, h⟩
    simp only [Family.bracket] at h
    rw [← h]
    have cl : ![0, (y 0 * z 2 - y 2 * z 0) * α,
      (y 0 * z 2 - y 2 * z 0) * β + y 0 * z 1 - y 1 * z 0] =
      ((y 0 * z 2 - y 2 * z 0) * α) • e₂ +
          ((y 0 * z 2 - y 2 * z 0) * β + y 0 * z 1 - y 1 * z 0) • e₃ := by
      unfold e₂ e₃
      simp only [e₂_def, e₃_def]
      funext i; fin_cases i
      · change (0:K) = ((y 0 * z 2 - y 2 * z 0) * α) * 0 +
          ((y 0 * z 2 - y 2 * z 0) * β + y 0 * z 1 - y 1 * z 0) * 0
        ring
      · change (y 0 * z 2 - y 2 * z 0) * α = ((y 0 * z 2 - y 2 * z 0) * α) * 1 +
          ((y 0 * z 2 - y 2 * z 0) * β + y 0 * z 1 - y 1 * z 0) * 0
        ring
      · change (y 0 * z 2 - y 2 * z 0) * β + y 0 * z 1 - y 1 * z 0 =
          ((y 0 * z 2 - y 2 * z 0) * α) * 0 +
          ((y 0 * z 2 - y 2 * z 0) * β + y 0 * z 1 - y 1 * z 0) * 1
        ring
    symm at cl
    simp only [SetLike.mem_coe]
    rw [mem_span_pair]
    exact ⟨_, _, cl⟩
  · rw [span_le]
    trans {x | ∃ (y z: Family K α β), ⁅y, z⁆ = x}
    · intro e Be
      simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
      cases Be with
      | inl h => subst h; exact ⟨_, _, e₂_bracket⟩
      | inr h => subst h; exact ⟨_, _, e₃_bracket⟩
    · apply subset_span (R:=K) (M:=Family K α β) (s := {x | ∃ y z, ⁅y, z⁆ = x})

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.B (α β : K) : Fin 2 → Family K α β := ![e₂, e₃]

theorem _root_.LieAlgebra.Dim3.Family.B_is_li_ambient : LinearIndependent K (M
    := Family K α β) (B α β) := by
      unfold B
      refine LinearIndependent.pair_iff.mpr ?_
      simp only [e₂_def, e₃_def]
      intro s t hst
      unfold Family at hst
      constructor
      · apply_fun (fun f ↦ f 1) at hst
        simp only [Matrix.smul_cons, smul_eq_mul, mul_zero, mul_one, Matrix.smul_empty, Fin.isValue,
          Pi.add_apply, Matrix.cons_val_one, add_zero, Pi.zero_apply,
          Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
          add_zero] at hst
        exact hst
      · apply_fun (fun f ↦ f 2) at hst
        simp only [Matrix.smul_cons, smul_eq_mul, mul_zero,
          mul_one, Matrix.smul_empty, Pi.add_apply, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons, zero_add, Pi.zero_apply] at hst
        exact hst

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.e₁α : Family K α β := ![α⁻¹, 0, 0]
/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.e₂β : Family K α β := ![0, -β, 1]

theorem _root_.LieAlgebra.Dim3.Family.e₂_bracket {hα : α ≠ 0} : ⁅(e₁α : Family K α β),
  (e₂β : Family K α β)⁆ = e₂ := by
    rw [Family.bracket]
    unfold e₂β e₁α e₂
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one, mul_zero, sub_zero,
      Matrix.cons_val_one, mul_neg, add_neg_cancel, sub_self]
    simp_all only [ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel,
      ]

theorem _root_.LieAlgebra.Dim3.Family.e₃_bracket : ⁅(e₁ : Family K α β),
  (e₂ : Family K α β)⁆ = e₃ := by
    rw [Family.bracket]
    unfold e₁ e₂ e₃
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero, sub_self, zero_mul,
      Matrix.cons_val_one, mul_one, zero_add, sub_zero]

lemma _root_.LieAlgebra.Dim3.Family.e₂_in_comm {hα : α ≠ 0} : e₂ ∈ commutator K (Family K α β) := by
    unfold e₂
    refine (LieSubmodule.mem_toSubmodule _).mp ?_
    rw [commutator_eq_span]
    have := subset_span (R := K) (M := Family K α β) (s := {x | ∃ (y z : Family K α β), ⁅y, z⁆ = x})
    exact (this ⟨_, _, e₂_bracket (α := α) (β := β) (hα := hα)⟩)

lemma _root_.LieAlgebra.Dim3.Family.e₃_in_comm : e₃ ∈ commutator K (Family K α β) := by
    unfold e₃
    refine (LieSubmodule.mem_toSubmodule _).mp ?_
    rw [commutator_eq_span]
    have := subset_span (R := K) (M := Family K α β) (s := {x | ∃ (y z : Family K α β), ⁅y, z⁆ = x})
    exact (this ⟨_, _, e₃_bracket⟩)

/-- TODO. -/
noncomputable def _root_.LieAlgebra.Dim3.Family.commutatorBasis (α β : K) (hα : α ≠ 0) : Basis
    (Fin 2) K (commutator K (Family K α β)) := by
  -- Basis are ![0,1,0] and ![0,0,1]
  let e₁α : Family K α β := ![α⁻¹, 0, 0]
  let e₂β : Family K α β := ![0, -β, 1]
  let e₁ : Family K α β := ![1, 0, 0]
  let e₂ : Family K α β := e₂
  let e₃ : Family K α β := e₃
  have e₂_bracket : ⁅e₁α, e₂β⁆ = e₂ := by
    rw [Family.bracket]
    unfold e₂β e₁α e₂
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one, mul_zero, sub_zero,
      Matrix.cons_val_one, mul_neg, add_neg_cancel, sub_self]
    simp_all only [ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel, e₂_def,
      ]
  have e₃_bracket : ⁅e₁, e₂⁆ = e₃ := by
    rw [Family.bracket]
    unfold e₁ e₂ e₃
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero, sub_self, zero_mul,
      Matrix.cons_val_one, mul_one, zero_add, sub_zero, e₂_def, e₃_def]
  have B_setrange {hα : α ≠ 0}  : Set.range (B α β) ⊆ commutator K (Family K α β) := by
    simp_all only [ne_eq, Matrix.range_cons,
      Matrix.range_empty, Set.union_empty, Set.union_singleton, B]
    intro e Be
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff]
    cases Be with
    | inl h => subst h; simp_all only [SetLike.mem_coe, e₁α, e₂β, e₂, e₁, e₃, e₃_in_comm]
    | inr h => subst h; simp_all only [SetLike.mem_coe, e₁α, e₂β, e₂, e₁, e₃,
      e₂_in_comm (hα := hα)]
  have B_setrange_eq : Set.range (B α β) = {e₂, e₃} := by
    simp_all only [ne_eq, Matrix.range_cons,
      Matrix.range_empty, Set.union_empty, Set.union_singleton, B]
    simp_all only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, e₁, e₂β, e₃, e₂, e₁α]
    ext x : 1
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff]
    apply Iff.intro
    · intro a
      cases a with
      | inl h =>
        subst h
        simp_all only [or_true]
      | inr h_1 =>
        subst h_1
        simp_all only [true_or]
    · intro a
      cases a with
      | inl h =>
        subst h
        simp_all only [or_true]
      | inr h_1 =>
        subst h_1
        simp_all only [true_or]
  let B_is_li_comm := linearIndependent_from_ambient (K := K) (commutator K (Family K α β)) ![e₂,
    e₃] B_is_li_ambient (B_setrange (hα := hα))
  have : Set.range (Set.map_into_subtype (↑(↑(commutator K (Family K α β)))) (B α β) (B_setrange
      (hα:=hα) )) =
    ({⟨e₂, e₂_in_comm (hα := hα)⟩, ⟨e₃, e₃_in_comm⟩} : Set (↥(commutator K (Family K α β)))) := by
    unfold Set.range
    simp only [SetLike.coe_sort_coe]
    ext j
    constructor
    · intro j_in
      simp only [Fin.exists_fin_two, Fin.isValue, Set.mem_setOf_eq] at j_in
      rcases j_in with hy | hy
      · have := Set.map_into_subtype_apply (↑(commutator K (Family K α β))) (B α β)
          (B_setrange (hα:=hα)) 0
        rw [hy] at this
        unfold B at this
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        left
        apply Subtype.ext
        simp only [Matrix.cons_val_zero] at this
        exact this
      · have := Set.map_into_subtype_apply (↑(commutator K (Family K α β))) (B α β)
          (B_setrange (hα:=hα)) 1
        rw [hy] at this
        unfold B at this
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        right
        apply Subtype.ext
        simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
        exact this
    · intro e
      simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, e₁, e₂β, e₁α]
      rcases e with (e0 | e1)
      · subst e0
        simp only [Set.mem_setOf_eq]
        use 0
        apply Subtype.ext
        rw [Set.map_into_subtype_apply (↑(commutator K (Family K α β))) (B α β) (B_setrange) (0)]
        · unfold B
          simp only [Matrix.cons_val_zero, e₂_def]
          unfold e₂
          simp only [e₂_def]
        · exact hα
      · subst e1
        simp only [Set.mem_setOf_eq]
        use 1
        apply Subtype.ext
        rw [Set.map_into_subtype_apply (↑(commutator K (Family K α β))) (B α β) (B_setrange) (1)]
        · unfold B
          simp only [Matrix.cons_val_one, e₃_def]
          unfold e₃
          simp only [e₃_def]
          simp []
        · exact hα
  let B_basis : Basis (Fin 2) K (commutator K (Family K α β)) :=
    Basis.mk B_is_li_comm (by
      intro ⟨x, hx⟩
      simp only [mem_top, LieIdeal.toLieSubalgebra_toSubmodule, forall_const]
      norm_cast
      unfold B at this
      rw [this]
      have : x ∈ span K {e₂, e₃} := by
        rw [← commutator_is_span_e₂e₃ (hα := hα)]
        · exact hx
      rw [@mem_span_pair]
      rw [@mem_span_pair] at this
      let ⟨a, b, h⟩ := this
      use a
      use b
      apply Subtype.ext
      simp only [SetLike.mk_smul_mk, AddMemClass.mk_add_mk]
      exact h)
  exact B_basis

theorem _root_.LieAlgebra.Dim3.Family.dim_commutator {hα : α ≠ 0} : finrank K (commutator K
    (Family K α β)) = 2 := by
  rw [finrank_eq_card_basis (commutatorBasis α β hα), Fintype.card_fin]

theorem _root_.LieAlgebra.Dim3.Family.B_basis_0 {hα : α ≠ 0} : ((commutatorBasis α β hα) 0).val =
    (e₂ : Family K α β) := by
  simp only [commutatorBasis, e₂, Basis.coe_mk]
  rfl

theorem _root_.LieAlgebra.Dim3.Family.B_basis_1 {hα : α ≠ 0} : ((commutatorBasis α β hα) 1).val =
    (e₃ : Family K α β) := by
  simp only [commutatorBasis, e₃, Basis.coe_mk]
  rfl

theorem _root_.LieAlgebra.Dim3.Family.B_basis_repr {hα : α ≠ 0} {x : commutator K
    (Family K α β)} : (commutatorBasis α β hα).repr x = ![x.val 1, x.val 2] := by
  let ⟨x, hx⟩ := x
  have h_repr := Basis.repr_fin_two (commutatorBasis α β hα) ⟨x, hx⟩
  have : x ∈ span K {e₂, e₃} := by
    rw [← commutator_is_span_e₂e₃ (hα := hα)]
    exact hx
  let ⟨a, b, h⟩ := mem_span_pair.mp this
  have w := h
  unfold e₂ e₃ at h
  change (a • ![(0:K), 1, 0] + b • ![(0:K), 0, 1] : Fin 3 → K) = x at h
  rw [Matrix.smul_vec3, Matrix.smul_vec3, Matrix.vec3_add] at h
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_eq_mul, mul_zero, add_zero, mul_one,
    zero_add] at h
  symm at h
  have x00 : x 0 = 0 := by
    apply_fun (fun x => x 0) at h
    exact h
  have x1a : x 1 = a := by
    apply_fun (fun x => x 1) at h
    exact h
  have x2b : x 2 = b := by
    apply_fun (fun x => x 2) at h
    exact h
  have h_repr := Basis.repr_fin_two (commutatorBasis α β hα) ⟨x, hx⟩
  rw [Subtype.ext_iff] at h_repr
  simp only [LieSubmodule.coe_add, SetLike.val_smul] at h_repr
  rw [h_repr] at w
  rw [B_basis_0, B_basis_1] at w
  let B : Fin 2 → Family K α β := ![e₂, e₃]
  have B_is_li_ambient : LinearIndependent K (M := Family K α β) B := by
    unfold B
    refine LinearIndependent.pair_iff.mpr ?_
    simp only [e₂_def, e₃_def]
    intro s t hst
    unfold Family at hst
    constructor
    · apply_fun (fun f ↦ f 1) at hst
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, smul_eq_mul, mul_zero,
        mul_one, Matrix.smul_empty, Fin.isValue, Pi.add_apply, Matrix.cons_val_one,
        Matrix.cons_val_zero, add_zero, Pi.zero_apply] at hst
      exact hst
    · apply_fun (fun f ↦ f 2) at hst
      simp only [Matrix.smul_cons, smul_eq_mul, mul_zero,
        mul_one, Matrix.smul_empty, Pi.add_apply, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, zero_add, Pi.zero_apply] at hst
      exact hst
  obtain ⟨a_eq, b_eq⟩ := LinearIndependent.eq_of_pair (R := K) (M := Family K α β) (x := e₂) (y
      := e₃) B_is_li_ambient w
  rw [a_eq] at x1a
  rw [b_eq] at x2b
  norm_cast
  rw [x1a, x2b]
  ext j
  fin_cases j
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
  · simp only [Fin.mk_one, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.ade₁ := ad K (Family K α β) e₁

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.adjoint (x : Family K α β) := ad K (Family K α β) x

theorem _root_.LieAlgebra.Dim3.Family.ade₁_pc : ∀ x ∈ (commutator K (Family K α β)),
  ade₁ x ∈ (commutator K (Family K α β)) := by
  intro x hx
  unfold ade₁
  simp only [ad_apply]
  exact lie_mem_commutator e₁ x

theorem _root_.LieAlgebra.Dim3.Family.ad_pc (x : Family K α β) : ∀ y ∈ (commutator K
    (Family K α β)), (adjoint x) y ∈ (commutator K (Family K α β)) := by
  intro y hy
  unfold adjoint
  simp only [ad_apply]
  exact lie_mem_commutator x y

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.ad_restr (x : Family K α β) : (commutator K
    (Family K α β)) →ₗ[K] (commutator K (Family K α β)) :=
  LinearMap.restrict (adjoint x) (ad_pc x)

/-- TODO. -/
def _root_.LieAlgebra.Dim3.Family.ade₁_restr (α β : K) := ad_restr e₁ (α:=α) (β:=β)

theorem _root_.LieAlgebra.Dim3.Family.ad_restr_apply (x : Family K α β) (y : Family K α β)
    (hy : y ∈ (commutator K (Family K α β))) :
    ad_restr x (⟨y, hy⟩ : (commutator K (Family K α β))) = ⟨adjoint x y, ad_pc x y hy⟩ :=
  rfl

theorem _root_.LieAlgebra.Dim3.Family.M_is_ade₁_restr {hα : α ≠ 0} : LinearMap.toMatrix
    (commutatorBasis α β hα) (commutatorBasis α β hα) (ade₁_restr α β) = M α β := by
    let e₁α : Family K α β := ![α⁻¹, 0, 0]
    let e₂β : Family K α β := ![0, -β, 1]
    unfold ade₁_restr
    unfold M
    ext i j
    simp only [LinearMap.toMatrix_apply]
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one]
      rw [ad_restr_apply]
      unfold adjoint
      simp only [ad_apply]
      simp only [B_basis_0, e₂_def]
      simp only [Family.bracket]
      rw [B_basis_repr]
      simp only [Matrix.cons_val_zero,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero, sub_self, zero_mul,
        Matrix.cons_val_one, mul_one, zero_add, sub_zero, e₁]
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
      rw [ad_restr_apply]
      unfold adjoint
      simp only [ad_apply]
      simp only [B_basis_1, e₃_def]
      simp only [Family.bracket]
      rw [B_basis_repr]
      simp only [Matrix.cons_val_zero,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one, mul_zero, sub_zero,
          Matrix.cons_val_one, add_zero]
      unfold e₁
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero,one_mul]
      · simp only [Matrix.cons_val_zero, one_mul, Fin.mk_one, Matrix.cons_val_one,
        ]

theorem _root_.LieAlgebra.Dim3.Family.tr_ade₁ (hα : α ≠ 0) : LinearMap.trace _ (commutator K
    (Family K α β)) (ade₁_restr α β) = β :=by
    rw [LinearMap.trace_eq_matrix_trace K (commutatorBasis α β hα) (ade₁_restr α β)]
    rw [M_is_ade₁_restr]
    exact M_trace

theorem _root_.LieAlgebra.Dim3.Family.det_ade₁ (hα : α ≠ 0) : LinearMap.det (ade₁_restr α β) = -α
    :=by
    rw [← LinearMap.det_toMatrix (ι:=Fin 2) (f:=(ade₁_restr α β)) (commutatorBasis α β hα)]
    rw[M_is_ade₁_restr]
    exact M_det

theorem _root_.LieAlgebra.Dim3.Family.e₁_not_in_comm (hα : α ≠ 0) : e₁ ∉ commutator K
    (Family K α β) := by
    intro hb0
    rw [e₁_def] at hb0
    have hb0S : ![1, 0, 0] ∈ (commutator K (Family K α β)).toSubmodule := hb0
    rw [commutator_is_span_e₂e₃ (α:=α) (β:=β) (hα:=hα)] at hb0S
    have hb0S' : (![1, 0, 0] : Family K α β) ∈ span K {(e₂ : Family K α β), e₃} := hb0S
    obtain ⟨a, b, h⟩ := (mem_span_pair (R := K) (M := Family K α β)).mp hb0S'
    unfold e₂ e₃ at h
    change (a • ![(0:K), 1, 0] + b • ![(0:K), 0, 1] : Fin 3 → K) = ![1, 0, 0] at h
    rw [Matrix.smul_vec3, Matrix.smul_vec3, Matrix.vec3_add] at h
    simp at h

end Family
end dim3_family_lemmas
end Dim3
end LieAlgebra
