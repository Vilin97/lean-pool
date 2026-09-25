/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
/-!
# Compatible families in inverse systems

The elementary inverse limits used in the local-field structure development are subobjects of
  dependent
products: their elements are precisely the families preserved by every
transition map.  Keeping this construction at the level of `Subring` and
`Subgroup` lets Lean inherit the ambient algebraic structure instead of
rebuilding the same pointwise instances for each inverse system.
-/

namespace LubinTate

/-- Families in a preorder-indexed system of rings that are preserved by all
transition maps.  No coherence hypotheses on `transition` are needed merely
to form this subring; concrete inverse systems supply them separately when
they are used. -/
def compatibleRingFamilies
    {ι : Type*} [Preorder ι] (R : ι → Type*) [∀ i, Ring (R i)]
    (transition : ∀ {i j : ι}, i ≤ j → R j →+* R i) :
    Subring (∀ i, R i) where
  carrier :=
    {x | ∀ {i j : ι} (hij : i ≤ j), transition hij (x j) = x i}
  zero_mem' := by
    intro i j hij
    exact map_zero (transition hij)
  one_mem' := by
    intro i j hij
    exact map_one (transition hij)
  add_mem' hx hy := by
    intro i j hij
    simpa using congrArg₂ (· + ·) (hx hij) (hy hij)
  mul_mem' hx hy := by
    intro i j hij
    simpa using congrArg₂ (· * ·) (hx hij) (hy hij)
  neg_mem' hx := by
    intro i j hij
    simpa using congrArg Neg.neg (hx hij)

/-- Families in a preorder-indexed system of groups that are preserved by all
transition maps.  The resulting subtype inherits its group structure from
the dependent product. -/
def compatibleGroupFamilies
    {ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i) :
    Subgroup (∀ i, G i) where
  carrier :=
    {x | ∀ {i j : ι} (hij : i ≤ j), transition hij (x j) = x i}
  one_mem' := by
    intro i j hij
    exact map_one (transition hij)
  mul_mem' hx hy := by
    intro i j hij
    simpa using congrArg₂ (· * ·) (hx hij) (hy hij)
  inv_mem' hx := by
    intro i j hij
    simpa using congrArg Inv.inv (hx hij)

/-- The group structure transported from the concrete compatible-family
subgroup.  Declaring it explicitly keeps clients independent of reducibility
of `compatibleGroupFamilies`. -/
instance compatibleGroupFamiliesGroup
    {ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i) :
    Group (compatibleGroupFamilies G transition) := by
  unfold compatibleGroupFamilies
  infer_instance

/-- Coordinatewise commutativity descends to the compatible-family inverse
limit. -/
instance compatibleGroupFamiliesCommGroup
    {ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, CommGroup (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i) :
    CommGroup (compatibleGroupFamilies G transition) :=
  { (compatibleGroupFamiliesGroup G transition) with
    mul_comm := fun x y => by
      apply Subtype.ext
      funext i
      exact mul_comm (x.1 i) (y.1 i) }

/-- Evaluation of a compatible family at one coordinate. -/
def compatibleGroupFamiliesEval
    {ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i) (i : ι) :
    compatibleGroupFamilies G transition →* G i :=
  (Pi.evalMonoidHom G i).comp (compatibleGroupFamilies G transition).subtype

/-- Evaluation of a compatible group family returns its component at the chosen index. -/
@[simp]
theorem compatibleGroupFamiliesEval_apply
    {ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i)
    (i : ι) (x : compatibleGroupFamilies G transition) :
    compatibleGroupFamiliesEval G transition i x = x.1 i :=
  rfl

/-- The named compatibility law for an inverse-limit family. -/
theorem compatibleGroupFamilies_transition
    {ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i)
    (x : compatibleGroupFamilies G transition) {i j : ι} (hij : i ≤ j) :
    transition hij (compatibleGroupFamiliesEval G transition j x) =
      compatibleGroupFamiliesEval G transition i x :=
  x.2 hij

/-- Compatible families are equal when all named coordinate evaluations
agree. -/
@[ext]
theorem compatibleGroupFamilies_ext
    {ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i)
    {x y : compatibleGroupFamilies G transition}
    (h : ∀ i, compatibleGroupFamiliesEval G transition i x =
      compatibleGroupFamiliesEval G transition i y) : x = y := by
  apply Subtype.ext
  funext i
  exact h i

/-- Stagewise multiplicative equivalences induce an equivalence of compatible
families when they commute with every transition map.  This is the reusable
inverse-limit boundary behind the quotient-unit comparisons between finite quotient systems. -/
def compatibleGroupFamiliesMulEquiv
    {ι : Type*} [Preorder ι]
    (G H : ι → Type*) [∀ i, Group (G i)] [∀ i, Group (H i)]
    (transitionG : ∀ {i j : ι}, i ≤ j → G j →* G i)
    (transitionH : ∀ {i j : ι}, i ≤ j → H j →* H i)
    (e : ∀ i, G i ≃* H i)
    (hcomm : ∀ {i j : ι} (hij : i ≤ j) (x : G j),
      transitionH hij (e j x) = e i (transitionG hij x)) :
    compatibleGroupFamilies G transitionG ≃*
      compatibleGroupFamilies H transitionH where
  toFun x :=
    ⟨fun i => e i (x.1 i), by
      intro i j hij
      rw [hcomm hij, x.2 hij]⟩
  invFun y :=
    ⟨fun i => (e i).symm (y.1 i), by
      intro i j hij
      apply (e i).injective
      calc
        e i (transitionG hij ((e j).symm (y.1 j))) =
            transitionH hij (e j ((e j).symm (y.1 j))) :=
          (hcomm hij ((e j).symm (y.1 j))).symm
        _ = transitionH hij (y.1 j) := by rw [(e j).apply_symm_apply]
        _ = y.1 i := y.2 hij
        _ = e i ((e i).symm (y.1 i)) := by rw [(e i).apply_symm_apply]
      ⟩
  left_inv x := by
    ext i
    exact (e i).symm_apply_apply (x.1 i)
  right_inv y := by
    ext i
    exact (e i).apply_symm_apply (y.1 i)
  map_mul' x y := by
    ext i
    exact (e i).map_mul (x.1 i) (y.1 i)

end LubinTate
