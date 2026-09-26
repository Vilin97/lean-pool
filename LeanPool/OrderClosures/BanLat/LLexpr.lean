/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination


/-!
# Formal lattice-linear expressions

This file defines formal lattice-linear expressions in finitely many variables
and their evaluation in an arbitrary real vector lattice. It also develops a
normal-form API: every expression is converted to a signed difference of finite
suprema of real linear combinations, with evaluation preserved in every vector
lattice.

The main application is the Yudin theorem: a lattice-linear identity between
formal expressions holds in every vector lattice as soon as it holds on `ℝ`.
-/

@[expose] public section

/-- A formal lattice-linear expression in `n` variables, built from the
variables by addition, real scalar multiplication, and the binary lattice
operations `⊔` and `⊓`. -/
inductive LLexpr (n : ℕ) where
  | zero : LLexpr n
  | var : Fin n → LLexpr n
  | add : LLexpr n → LLexpr n → LLexpr n
  | smul : ℝ → LLexpr n → LLexpr n
  | sup : LLexpr n → LLexpr n → LLexpr n
  | inf : LLexpr n → LLexpr n → LLexpr n

namespace LLexpr

open scoped BigOperators

variable {n : ℕ}

/-- Evaluation of a formal lattice-linear expression at an `n`-tuple of vectors
in a vector lattice. -/
def eval {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] (x : Fin n → X) : LLexpr n → X
  | .zero => 0
  | .var i => x i
  | .add e₁ e₂ => eval x e₁ + eval x e₂
  | .smul r e => r • eval x e
  | .sup e₁ e₂ => eval x e₁ ⊔ eval x e₂
  | .inf e₁ e₂ => eval x e₁ ⊓ eval x e₂

/-- Rename the variables of an expression along `f`.

This is used when two expressions depending on different finite tuples are
viewed as expressions in one concatenated tuple, and when a tuple is compressed
to the distinct elements in its range. -/
def reindexExpr {m n : ℕ} (f : Fin n → Fin m) : LLexpr n → LLexpr m
  | .zero => .zero
  | .var i => .var (f i)
  | .add e₁ e₂ => .add (reindexExpr f e₁) (reindexExpr f e₂)
  | .smul r e => .smul r (reindexExpr f e)
  | .sup e₁ e₂ => .sup (reindexExpr f e₁) (reindexExpr f e₂)
  | .inf e₁ e₂ => .inf (reindexExpr f e₁) (reindexExpr f e₂)

section Evaluation

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

@[simp] theorem eval_zero (x : Fin n → X) : eval x .zero = 0 := rfl

@[simp] theorem eval_var (x : Fin n → X) (i : Fin n) : eval x (.var i) = x i :=
  rfl

@[simp] theorem eval_add (x : Fin n → X) (e₁ e₂ : LLexpr n) :
    eval x (.add e₁ e₂) = eval x e₁ + eval x e₂ := rfl

@[simp] theorem eval_smul (x : Fin n → X) (r : ℝ) (e : LLexpr n) :
    eval x (.smul r e) = r • eval x e := rfl

@[simp] theorem eval_sup (x : Fin n → X) (e₁ e₂ : LLexpr n) :
    eval x (.sup e₁ e₂) = eval x e₁ ⊔ eval x e₂ := rfl

@[simp] theorem eval_inf (x : Fin n → X) (e₁ e₂ : LLexpr n) :
    eval x (.inf e₁ e₂) = eval x e₁ ⊓ eval x e₂ := rfl

@[simp]
theorem eval_reindexExpr {m n : ℕ} (x : Fin m → X)
    (f : Fin n → Fin m) (e : LLexpr n) :
    eval x (reindexExpr f e) = eval (fun i => x (f i)) e := by
  induction e <;> simp [reindexExpr, *]

/-- Any finite family factors through an injective finite family listing its range.

The map `f` records, for each original index, the corresponding index in the
range listing. This is useful when reducing an arbitrary finite tuple to a
tuple of distinct entries. -/
theorem exists_injective_reindex {ι : Type*} {n : ℕ} (a : Fin n → ι) :
    ∃ (m : ℕ) (b : Fin m → ι) (_ : Function.Injective b) (f : Fin n → Fin m),
      ∀ i, b (f i) = a i := by
  classical
  let s : Set ι := Set.range a
  have hs : s.Finite := Set.finite_range a
  let : Fintype s := hs.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨Fintype.card s, fun j => (e.symm j).1, ?_, fun i => e ⟨a i, ⟨i, rfl⟩⟩, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro i
    simp

end Evaluation

/-! ### Lattice-linear combinations of a tuple -/

section Combinations

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- The set of lattice-linear combinations of a tuple `x : Fin n → X`, i.e. the
image of `LLexpr n` under evaluation at `x`. -/
def combinations (x : Fin n → X) : Set X :=
  Set.range (eval x)

end Combinations

/-! ### Yudin's theorem -/

/-- A formal lattice-linear expression *vanishes* on a vector lattice `X` if its
evaluation is zero for every substitution by vectors of `X`. -/
def Vanishes (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] (e : LLexpr n) : Prop :=
  ∀ x : Fin n → X, eval x e = 0

private theorem sup'_add_right {ι X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] (s : Finset ι) (hs : s.Nonempty) (f : ι → X) (a : X) :
    s.sup' hs f + a = s.sup' hs (fun i => f i + a) :=
  map_finset_sup' (OrderIso.addRight a) hs f

private theorem add_left_sup' {ι X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] (s : Finset ι) (hs : s.Nonempty) (f : ι → X) (a : X) :
    a + s.sup' hs f = s.sup' hs (fun i => a + f i) :=
  map_finset_sup' (OrderIso.addLeft a) hs f

/-- Non-negative scalar multiplication as a `SupHom`. This packages
`nonneg_smul_sup` so finite suprema can be mapped through scalar
multiplication by `map_finset_sup'`. -/
private def smulSupHom {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (r : ℝ) (hr : 0 ≤ r) : SupHom X X where
  toFun := fun z => r • z
  map_sup' := fun a b => nonneg_smul_sup a b r hr

/-- A finite nonempty supremum of real linear combinations in `n` variables.

A value `A : SupLinearCombination n` stores a finite nonempty set of coefficient
vectors. Evaluating it at `x : Fin n → X` gives the supremum of the corresponding
linear combinations of the entries of `x`. -/
structure SupLinearCombination (n : ℕ) where
  /-- The finite set of coefficient vectors. -/
  coeffs : Finset (Fin n → ℝ)
  /-- Nonemptiness of the coefficient set, avoiding any ambient completeness assumption. -/
  nonempty : coeffs.Nonempty

namespace SupLinearCombination

/-- Evaluate a finite supremum of linear combinations at a tuple in a vector lattice. -/
noncomputable def eval {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (A : SupLinearCombination n)
    (x : Fin n → X) : X :=
  A.coeffs.sup' A.nonempty (Fintype.linearCombination ℝ x)

@[simp] private theorem linearCombination_zero_coeff {X : Type*} [AddCommGroup X]
    [Module ℝ X] (x : Fin n → X) :
    Fintype.linearCombination ℝ x (fun _ : Fin n => 0) = 0 := by
  change Fintype.linearCombination ℝ x (0 : Fin n → ℝ) = 0
  exact map_zero (Fintype.linearCombination ℝ x)

/-- The supremum consisting of a single linear combination with coefficient vector `a`. -/
noncomputable def singleton (a : Fin n → ℝ) : SupLinearCombination n :=
  { coeffs := {a}
    nonempty := Finset.singleton_nonempty a }

/-- Evaluating a singleton supremum gives the corresponding linear combination. -/
@[simp] theorem eval_singleton {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (a : Fin n → ℝ) (x : Fin n → X) :
    (singleton a).eval x = Fintype.linearCombination ℝ x a := by
  simp [eval, singleton]

/-- Add two finite suprema by adding each coefficient vector from the first to
each coefficient vector from the second. -/
noncomputable def add (A B : SupLinearCombination n) : SupLinearCombination n := by
  classical
  exact
    { coeffs := A.coeffs.image₂ (fun a b => a + b) B.coeffs
      nonempty := A.nonempty.image₂ B.nonempty }

/-- Evaluation turns addition of finite suprema into addition in the vector lattice. -/
@[simp] theorem eval_add {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (A B : SupLinearCombination n)
    (x : Fin n → X) :
    (A.add B).eval x = A.eval x + B.eval x := by
  classical
  unfold eval add
  rw [Finset.sup'_image₂_left]
  simp only [map_add]
  simp_rw [← add_left_sup' B.coeffs B.nonempty (fun b => Fintype.linearCombination ℝ x b)]
  rw [← sup'_add_right A.coeffs A.nonempty (fun a => Fintype.linearCombination ℝ x a)]

/-- The pointwise supremum of two finite suprema, obtained by taking the union
of their coefficient sets. -/
noncomputable def sup (A B : SupLinearCombination n) : SupLinearCombination n :=
  { coeffs := A.coeffs ∪ B.coeffs
    nonempty := A.nonempty.mono Finset.subset_union_left }

/-- Evaluation turns `SupLinearCombination.sup` into lattice supremum. -/
@[simp] theorem eval_sup {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (A B : SupLinearCombination n)
    (x : Fin n → X) :
    (A.sup B).eval x = A.eval x ⊔ B.eval x := by
  classical
  unfold eval sup
  rw [Finset.sup'_union]

/-- Scale every coefficient vector in a finite supremum by the scalar `r`. -/
noncomputable def smul (r : ℝ) (A : SupLinearCombination n) :
    SupLinearCombination n := by
  classical
  exact
    { coeffs := A.coeffs.image fun a => r • a
      nonempty := A.nonempty.image _ }

/-- For non-negative scalars, evaluation turns coefficient scaling into scalar multiplication. -/
@[simp] theorem eval_smul {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] {r : ℝ} (hr : 0 ≤ r)
    (A : SupLinearCombination n) (x : Fin n → X) :
    (A.smul r).eval x = r • A.eval x := by
  classical
  unfold eval smul
  rw [Finset.sup'_image]
  change A.coeffs.sup' A.nonempty (fun a => Fintype.linearCombination ℝ x (r • a)) =
    r • A.coeffs.sup' A.nonempty (fun a => Fintype.linearCombination ℝ x a)
  simp_rw [map_smul]
  exact (map_finset_sup' (smulSupHom r hr) A.nonempty
    (fun a => Fintype.linearCombination ℝ x a)).symm

private theorem continuousLinearMap_apply_eq_linearCombination (f : StrongDual ℝ (Fin n → ℝ))
    (a : Fin n → ℝ) :
    f a = Fintype.linearCombination ℝ
      (fun i => f (Pi.single i (1 : ℝ) : Fin n → ℝ)) a := by
  classical
  have ha : a = ∑ i, a i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    funext j
    simp [Pi.single_apply, Finset.sum_apply]
  calc
    f a = f (∑ i, a i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by rw [← ha]
    _ = ∑ i, f (a i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by rw [map_sum]
    _ = ∑ i, a i * f (Pi.single i (1 : ℝ) : Fin n → ℝ) := by simp
    _ = Fintype.linearCombination ℝ
        (fun i => f (Pi.single i (1 : ℝ) : Fin n → ℝ)) a := by
      simp [Fintype.linearCombination_apply, smul_eq_mul]

/-- A finite-dimensional support-function criterion for membership in the
convex hull of `S`.

If every real linear functional takes value on `p` no larger than its supremum
over `S`, then `p` belongs to the convex hull of `S`. -/
private theorem mem_convexHull_of_forall_le_sup (p : Fin n → ℝ)
    (S : Finset (Fin n → ℝ)) (hS : S.Nonempty)
    (h : ∀ r : Fin n → ℝ,
      Fintype.linearCombination ℝ r p ≤ S.sup' hS (Fintype.linearCombination ℝ r)) :
    p ∈ convexHull ℝ (S : Set (Fin n → ℝ)) := by
  classical
  by_contra hp
  obtain ⟨f, u, hfp, hsep⟩ := _root_.geometric_hahn_banach_point_closed
    (E := Fin n → ℝ)
    (convex_convexHull ℝ (S : Set (Fin n → ℝ))) (S.finite_toSet.isClosed_convexHull ℝ) hp
  let c : Fin n → ℝ := fun i => f (Pi.single i (1 : ℝ) : Fin n → ℝ)
  let r : Fin n → ℝ := fun i => -c i
  have hf_eval : ∀ a : Fin n → ℝ, f a = Fintype.linearCombination ℝ c a := fun a =>
    continuousLinearMap_apply_eq_linearCombination f a
  have hsup_lt :
      S.sup' hS (Fintype.linearCombination ℝ r) < Fintype.linearCombination ℝ r p := by
    rw [Finset.sup'_lt_iff]
    intro q hq
    have hqconv : q ∈ convexHull ℝ (S : Set (Fin n → ℝ)) :=
      subset_convexHull ℝ (S : Set (Fin n → ℝ)) hq
    have hqsep := hsep q hqconv
    have : -f q < -f p := by
      simpa using neg_lt_neg (hfp.trans hqsep)
    have hq_eval : Fintype.linearCombination ℝ r q = -f q := by
      rw [hf_eval q]
      simp [Fintype.linearCombination_apply, r, c, Finset.sum_neg_distrib, smul_eq_mul]
    have hp_eval : Fintype.linearCombination ℝ r p = -f p := by
      rw [hf_eval p]
      simp [Fintype.linearCombination_apply, r, c, Finset.sum_neg_distrib, smul_eq_mul]
    simpa [hq_eval, hp_eval] using this
  exact (not_lt_of_ge (h r)) hsup_lt

/-- If the coefficient vector `p` is a convex combination of the coefficient
vectors in `B`, then its linear evaluation is bounded by the supremum `B.eval`.

This is the vector-lattice step: the scalar convex-combination coefficients are
non-negative, so the pointwise order bound can be summed. -/
private theorem linearCombination_le_eval_of_mem_convexHull {X : Type*} [AddCommGroup X]
    [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X] (B : SupLinearCombination n)
    {p : Fin n → ℝ} (hp : p ∈ convexHull ℝ (B.coeffs : Set (Fin n → ℝ)))
    (x : Fin n → X) :
    Fintype.linearCombination ℝ x p ≤ B.eval x := by
  classical
  rw [Finset.mem_convexHull'] at hp
  obtain ⟨w, hw_nonneg, hw_sum, hw_eq⟩ := hp
  calc
    Fintype.linearCombination ℝ x p =
        Fintype.linearCombination ℝ x (∑ q ∈ B.coeffs, w q • q) := by
      rw [hw_eq]
    _ = ∑ q ∈ B.coeffs, w q • Fintype.linearCombination ℝ x q := by
      simp
    _ ≤ ∑ q ∈ B.coeffs, w q • B.eval x := by
      refine Finset.sum_le_sum fun q hq => ?_
      exact smul_le_smul_of_nonneg_left
        (Finset.le_sup' (Fintype.linearCombination ℝ x) hq) (hw_nonneg q hq)
    _ = B.eval x := by
      rw [← Finset.sum_smul, hw_sum, one_smul]

/-- If one finite supremum of linear combinations is pointwise below another on
`ℝ^n`, then the same inequality holds after evaluation in any vector lattice. -/
theorem eval_le_of_forall_real_le {X : Type*} [AddCommGroup X]
    [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X] (A B : SupLinearCombination n)
    (h : ∀ r : Fin n → ℝ, A.eval r ≤ B.eval r) (x : Fin n → X) :
    A.eval x ≤ B.eval x := by
  classical
  unfold eval
  refine Finset.sup'_le A.nonempty (Fintype.linearCombination ℝ x) fun p hp => ?_
  exact linearCombination_le_eval_of_mem_convexHull B
    (mem_convexHull_of_forall_le_sup p B.coeffs B.nonempty fun r =>
      (Finset.le_sup' (Fintype.linearCombination ℝ r) hp).trans (h r)) x

/-- If two finite suprema of linear combinations agree pointwise on `ℝ^n`, then
they agree after evaluation in any vector lattice. -/
theorem eval_eq_of_forall_real_eq {X : Type*} [AddCommGroup X]
    [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X] (A B : SupLinearCombination n)
    (h : ∀ r : Fin n → ℝ, A.eval r = B.eval r) (x : Fin n → X) :
    A.eval x = B.eval x :=
  le_antisymm (eval_le_of_forall_real_le A B (fun r => (h r).le) x)
    (eval_le_of_forall_real_le B A (fun r => (h r).ge) x)

end SupLinearCombination

/-- A signed normal form `pos - neg`, where both sides are finite suprema of
linear combinations. -/
structure NormalForm (n : ℕ) where
  /-- The positive finite supremum in the signed representation. -/
  pos : SupLinearCombination n
  /-- The negative finite supremum in the signed representation. -/
  neg : SupLinearCombination n

namespace NormalForm

/-- Evaluate a signed normal form at a tuple in a vector lattice. -/
noncomputable def eval {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (N : NormalForm n) (x : Fin n → X) : X :=
  N.pos.eval x - N.neg.eval x

/-- The zero normal form. -/
noncomputable def zero : NormalForm n :=
  { pos := SupLinearCombination.singleton (fun _ : Fin n => 0)
    neg := SupLinearCombination.singleton (fun _ : Fin n => 0) }

/-- The normal form for the `i`-th variable. -/
noncomputable def var (i : Fin n) : NormalForm n :=
  { pos := SupLinearCombination.singleton (Pi.single i (1 : ℝ) : Fin n → ℝ)
    neg := SupLinearCombination.singleton (fun _ : Fin n => 0) }

/-- Add two signed normal forms. -/
noncomputable def add (N M : NormalForm n) : NormalForm n :=
  { pos := N.pos.add M.pos
    neg := N.neg.add M.neg }

/-- Negate a signed normal form by swapping its positive and negative parts. -/
noncomputable def negate (N : NormalForm n) : NormalForm n :=
  { pos := N.neg
    neg := N.pos }

/-- Scalar multiplication of signed normal forms. -/
noncomputable def smul (r : ℝ) (N : NormalForm n) : NormalForm n :=
  if 0 ≤ r then
    { pos := N.pos.smul r
      neg := N.neg.smul r }
  else
    { pos := N.neg.smul (-r)
      neg := N.pos.smul (-r) }

/-- The lattice supremum of two signed normal forms. -/
noncomputable def sup (N M : NormalForm n) : NormalForm n :=
  { pos := (N.pos.add M.neg).sup (M.pos.add N.neg)
    neg := N.neg.add M.neg }

/-- The lattice infimum of two signed normal forms. -/
noncomputable def inf (N M : NormalForm n) : NormalForm n :=
  negate (sup (negate N) (negate M))

private theorem sup_sub_identity {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] (a b c d : X) :
    ((a + d) ⊔ (b + c)) - (c + d) = (a - c) ⊔ (b - d) := by
  have h : ((a - c) ⊔ (b - d)) + (c + d) = (a + d) ⊔ (b + c) := by
    rw [sup_add]
    congr 1 <;> abel
  rw [← h]
  abel

/-- Evaluating the zero normal form gives zero. -/
@[simp] theorem eval_zero {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (x : Fin n → X) :
    (zero : NormalForm n).eval x = 0 := by
  simp [eval, zero]

/-- Evaluating a variable normal form gives the corresponding tuple entry. -/
@[simp] theorem eval_var {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (i : Fin n) (x : Fin n → X) :
    (var i).eval x = x i := by
  simp [eval, var]

/-- Evaluation turns addition of normal forms into addition. -/
@[simp] theorem eval_add {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (N M : NormalForm n) (x : Fin n → X) :
    (add N M).eval x = N.eval x + M.eval x := by
  simp [eval, add]
  abel

/-- Evaluation turns negation of normal forms into negation. -/
@[simp] theorem eval_negate {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (N : NormalForm n)
    (x : Fin n → X) :
    (negate N).eval x = -N.eval x := by
  simp [eval, negate]

/-- Evaluation turns scalar multiplication of normal forms into scalar multiplication. -/
@[simp] theorem eval_smul {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (r : ℝ) (N : NormalForm n)
    (x : Fin n → X) :
    (smul r N).eval x = r • N.eval x := by
  by_cases hr : 0 ≤ r
  · simp [smul, hr, eval, smul_sub]
  · have hneg : 0 ≤ -r := by linarith
    simp [smul, hr, hneg, eval, smul_sub]
    abel

/-- Evaluation turns supremum of normal forms into lattice supremum. -/
@[simp] theorem eval_sup {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (N M : NormalForm n) (x : Fin n → X) :
    (sup N M).eval x = N.eval x ⊔ M.eval x := by
  simp [eval, sup, sup_sub_identity]

/-- Evaluation turns infimum of normal forms into lattice infimum. -/
@[simp] theorem eval_inf {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (N M : NormalForm n) (x : Fin n → X) :
    (inf N M).eval x = N.eval x ⊓ M.eval x := by
  simp [inf, neg_sup]

end NormalForm

/-- Convert an arbitrary lattice-linear expression into a signed supremum of
linear combinations, preserving evaluation in every vector lattice. -/
noncomputable def normalize : LLexpr n → NormalForm n
  | .zero => NormalForm.zero
  | .var i => NormalForm.var i
  | .add e₁ e₂ => NormalForm.add (normalize e₁) (normalize e₂)
  | .smul r e => NormalForm.smul r (normalize e)
  | .sup e₁ e₂ => NormalForm.sup (normalize e₁) (normalize e₂)
  | .inf e₁ e₂ => NormalForm.inf (normalize e₁) (normalize e₂)

/-- The normal form of an expression has the same evaluation as the expression. -/
@[simp] theorem normalize_eval {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (x : Fin n → X) (e : LLexpr n) :
    (normalize e).eval x = eval x e := by
  induction e <;> simp [normalize, *]

/-- Yudin's theorem: a formal lattice-linear expression that vanishes on `ℝ`
vanishes on every vector lattice. -/
theorem vanishes_of_vanishes_real (e : LLexpr n) (h : Vanishes ℝ e)
    (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] : Vanishes X e := by
  intro x
  have hreal : ∀ r : Fin n → ℝ, (normalize e).pos.eval r = (normalize e).neg.eval r := by
    intro r
    have hr := h r
    rw [← normalize_eval r e, NormalForm.eval] at hr
    exact sub_eq_zero.mp hr
  have hx :=
    SupLinearCombination.eval_eq_of_forall_real_eq (normalize e).pos (normalize e).neg hreal x
  rw [← normalize_eval x e, NormalForm.eval, hx, sub_self]

/-- If the difference of two formal expressions vanishes on the reals, their
evaluations agree in every vector lattice. -/
theorem eval_eq_of_vanishes_real {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (x : Fin n → X) (e₁ e₂ : LLexpr n)
    (h : Vanishes ℝ (add e₁ (smul (-1) e₂))) :
    eval x e₁ = eval x e₂ := by
  have hX : eval x e₁ + (-1 : ℝ) • eval x e₂ = 0 :=
    (vanishes_of_vanishes_real (add e₁ (smul (-1) e₂)) h X) x
  apply sub_eq_zero.mp
  simpa [sub_eq_add_neg] using hX

end LLexpr
