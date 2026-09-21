/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Convex.AffineLattice
import Mathlib.Order.Fin.Basic

/-!
# Convex flags

This file formalizes Definitions 3.1, 3.4, 3.5, and 3.6 of the paper.
Nodes form a finite nonempty upper semilattice.  Fibre coordinates are real,
and each fibre carries its own affine lattice.  Transitions preserve both
the polytope and the chosen lattice.

The base of a point is retained as data.  This is intentional: points with
the same coordinate at an upper node but different domains are distinct (the
`0` versus `0'` phenomenon in the examples following Proposition 3.11).
-/

open scoped BigOperators

namespace EGZ

universe u

/-- A convex flag in affine-lattice coordinates.

The transition attached to `x ≤ y` goes from the fibre at `x` to the fibre
at `y`; it is the paper's map `ψ_{y,x}`. -/
structure ConvexFlag where
  Node : Type u
  [nodeFintype : Fintype Node]
  [nodeSemilatticeSup : SemilatticeSup Node]
  [nodeOrderTop : OrderTop Node]
  rank : Node → ℕ
  polytope : (x : Node) → RationalPolytope (rank x)
  lattice : (x : Node) → AffineLattice (rank x)
  transition : {x y : Node} → x ≤ y → IntegralAffineMap (rank x) (rank y)
  transition_mem : ∀ {x y : Node} (h : x ≤ y) {q},
    q ∈ (polytope x).carrier → (transition h).real q ∈ (polytope y).carrier
  transition_lattice : ∀ {x y : Node} (h : x ≤ y) {q},
    q ∈ lattice x → (transition h).real q ∈ lattice y
  transition_refl : ∀ x, transition (le_refl x) = IntegralAffineMap.id (rank x)
  transition_trans : ∀ {x y z : Node} (hxy : x ≤ y) (hyz : y ≤ z),
    transition (hxy.trans hyz) = (transition hyz).comp (transition hxy)

namespace ConvexFlag

attribute [instance] nodeFintype nodeSemilatticeSup nodeOrderTop

/-- The points of a flag are dependent pairs of a base and a point of that
base polytope. -/
structure Point (F : ConvexFlag) where
  base : F.Node
  val : RealCoord (F.rank base)
  val_mem : val ∈ (F.polytope base).carrier

namespace Point

/-- The upper-set domain of a flag point. -/
def domain {F : ConvexFlag} (q : F.Point) : Set F.Node := {x | q.base ≤ x}

@[simp]
theorem mem_domain {F : ConvexFlag} (q : F.Point) (x : F.Node) :
    x ∈ q.domain ↔ q.base ≤ x := Iff.rfl

/-- Coordinate of a point at a node in its domain. -/
def coord {F : ConvexFlag} (q : F.Point) {x : F.Node} (h : q.base ≤ x) :
    RealCoord (F.rank x) :=
  (F.transition h).real q.val

theorem coord_mem {F : ConvexFlag} (q : F.Point) {x : F.Node} (h : q.base ≤ x) :
    q.coord h ∈ (F.polytope x).carrier :=
  F.transition_mem h q.val_mem

@[simp]
theorem coord_base {F : ConvexFlag} (q : F.Point) : q.coord (le_refl q.base) = q.val := by
  rw [coord, F.transition_refl]
  rfl

/-- A point is integral if its coordinate at its base is in that fibre's
distinguished affine lattice. -/
def IsIntegral {F : ConvexFlag} (q : F.Point) : Prop := q.val ∈ F.lattice q.base

theorem isIntegral_coord {F : ConvexFlag} {q : F.Point} (hq : q.IsIntegral)
    {x : F.Node} (h : q.base ≤ x) : q.coord h ∈ F.lattice x :=
  F.transition_lattice h hq

/-- `q` is a projection of `q'` when `q'` has the larger domain and they agree
on the domain of `q`.  By the cocycle law it is enough to compare at `q.base`.
-/
def IsProjectionOf {F : ConvexFlag} (q q' : F.Point) : Prop :=
  ∃ h : q'.base ≤ q.base, q.val = q'.coord h

theorem domain_subset_of_projection {F : ConvexFlag} {q q' : F.Point}
    (h : q.IsProjectionOf q') : q.domain ⊆ q'.domain := by
  obtain ⟨hbase, _⟩ := h
  intro x hx
  exact hbase.trans hx

theorem coord_eq_of_projection {F : ConvexFlag} {q q' : F.Point}
    (hbase : q'.base ≤ q.base) (hval : q.val = q'.coord hbase)
    {x : F.Node} (hx : q.base ≤ x) :
    q.coord hx = q'.coord (hbase.trans hx) := by
  unfold coord
  rw [hval, F.transition_trans hbase hx]
  rfl

end Point

/-- A "linear function" in the paper: an affine functional based at one
node, with constant terms allowed. -/
structure LinearFunction (F : ConvexFlag) where
  base : F.Node
  toAffine : RealCoord (F.rank base) →ᵃ[ℝ] ℝ

namespace LinearFunction

/-- The lower-set domain of a flag linear function. -/
def domain {F : ConvexFlag} (xi : F.LinearFunction) : Set F.Node := {x | x ≤ xi.base}

@[simp]
theorem mem_domain {F : ConvexFlag} (xi : F.LinearFunction) (x : F.Node) :
    x ∈ xi.domain ↔ x ≤ xi.base := Iff.rfl

/-- A function can be evaluated at a point exactly when their domains meet. -/
def EvaluableAt {F : ConvexFlag} (xi : F.LinearFunction) (q : F.Point) : Prop :=
  q.base ≤ xi.base

theorem evaluableAt_iff_domains_inter {F : ConvexFlag} (xi : F.LinearFunction)
    (q : F.Point) : xi.EvaluableAt q ↔ (xi.domain ∩ q.domain).Nonempty := by
  constructor
  · intro h
    exact ⟨xi.base, le_rfl, h⟩
  · rintro ⟨x, hx, hq⟩
    exact hq.trans hx

/-- Evaluation, using the function's base. -/
def eval {F : ConvexFlag} (xi : F.LinearFunction) (q : F.Point)
    (h : xi.EvaluableAt q) : ℝ :=
  xi.toAffine (q.coord h)

end LinearFunction

/-- Data witnessing one finite convex combination of flag points.  Only
strictly positive coefficients constrain the result's base; this is crucial
in Proposition 7.1 and avoids zero coefficients shrinking the domain. -/
structure ConvexCombination {F : ConvexFlag} {I : Type*} [Fintype I]
    (points : I → F.Point) (weight : I → ℝ) (result : F.Point) : Prop where
  nonnegative : ∀ i, 0 ≤ weight i
  sum_eq_one : (∑ i, weight i) = 1
  base_isLUB : IsLeast {x : F.Node | ∀ i, 0 < weight i → (points i).base ≤ x} result.base
  val_eq : result.val = ∑ i : {i // 0 < weight i},
    weight i • (points i).coord (base_isLUB.1 i i.property)

namespace ConvexCombination

/-- The weights on the strictly positive support still sum to one. -/
theorem sum_active {F : ConvexFlag} {I : Type*} [Fintype I]
    {points : I → F.Point} {weight : I → ℝ} {result : F.Point}
    (c : ConvexCombination points weight result) :
    (∑ i : {i // 0 < weight i}, weight i) = 1 := by
  classical
  have hactive :
      (∑ i : {i : I // 0 < weight i}, weight i) = ∑ i, weight i := by
    calc
      (∑ i : {i : I // 0 < weight i}, weight i) =
          (∑ i : {i : I // 0 < weight i}, weight i) +
            ∑ i : {i : I // ¬ 0 < weight i}, weight i := by
              have hinactive :
                  (∑ i : {i : I // ¬ 0 < weight i}, weight i) = 0 := by
                apply Finset.sum_eq_zero
                intro i _
                exact le_antisymm (le_of_not_gt i.property) (c.nonnegative i)
              rw [hinactive, add_zero]
      _ = ∑ i, weight i := Fintype.sum_subtype_add_sum_subtype _ _
  exact hactive.trans c.sum_eq_one

/-- Equation `convc` at an arbitrary upper node.  This is the API form used
as equation `comb2` in Proposition 7.1. -/
theorem coord_eq {F : ConvexFlag} {I : Type*} [Fintype I]
    {points : I → F.Point} {weight : I → ℝ} {result : F.Point}
    (c : ConvexCombination points weight result) {y : F.Node}
    (hy : result.base ≤ y) :
    result.coord hy = ∑ i : {i // 0 < weight i},
      weight i • (points i).coord ((c.base_isLUB.1 i i.property).trans hy) := by
  classical
  let A := {i : I // 0 < weight i}
  let z : A → RealCoord (F.rank result.base) := fun i ↦
    (points i).coord (c.base_isLUB.1 i i.property)
  have hs : (∑ i : A, weight i) = 1 := by
    simpa [A] using c.sum_active
  calc
    result.coord hy = (F.transition hy).real result.val := rfl
    _ = (F.transition hy).real (∑ i : A, weight i • z i) := by
      rw [c.val_eq]
    _ = (F.transition hy).real
        ((Finset.univ : Finset A).affineCombination ℝ z (fun i ↦ weight i)) := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hs)]
    _ = (Finset.univ : Finset A).affineCombination ℝ
        ((F.transition hy).real ∘ z) (fun i ↦ weight i) :=
      (Finset.univ : Finset A).map_affineCombination z (fun i ↦ weight i) hs
        (F.transition hy).real
    _ = ∑ i : A, weight i • (F.transition hy).real (z i) := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hs)]
      rfl
    _ = ∑ i : {i // 0 < weight i},
        weight i • (points i).coord ((c.base_isLUB.1 i i.property).trans hy) := by
      apply Fintype.sum_congr
      intro i
      congr 1
      unfold z Point.coord
      rw [F.transition_trans (c.base_isLUB.1 i i.property) hy]
      rfl

end ConvexCombination

/-- Convex combinations exist.  This theorem is the implementation-level
counterpart of equation `convc`: the base is the supremum of the positive
support and convexity of the target fibre supplies membership. -/
theorem exists_convexCombination {F : ConvexFlag} {I : Type*} [Fintype I]
    (points : I → F.Point) (weight : I → ℝ)
    (hnonneg : ∀ i, 0 ≤ weight i) (hsum : (∑ i, weight i) = 1) :
    ∃ result, ConvexCombination points weight result := by
  classical
  have hpos : ∃ i, 0 < weight i := by
    by_contra h
    have hz : ∀ i, weight i = 0 := fun i ↦
      le_antisymm (le_of_not_gt (fun hi ↦ h ⟨i, hi⟩)) (hnonneg i)
    simp [hz] at hsum
  let A := {i : I // 0 < weight i}
  let _ : Nonempty A := ⟨⟨hpos.choose, hpos.choose_spec⟩⟩
  let b : F.Node := (Finset.univ : Finset A).sup' Finset.univ_nonempty
    (fun i ↦ (points i).base)
  have hib (i : A) : (points i).base ≤ b := by
    exact Finset.le_sup' (fun j : A ↦ (points j).base) (Finset.mem_univ i)
  have hsumA : (∑ i : A, weight i) = 1 := by
    have hactive :
        (∑ i : {i : I // 0 < weight i}, weight i) = ∑ i, weight i := by
      calc
        (∑ i : {i : I // 0 < weight i}, weight i) =
            (∑ i : {i : I // 0 < weight i}, weight i) +
              ∑ i : {i : I // ¬ 0 < weight i}, weight i := by
                have hinactive :
                    (∑ i : {i : I // ¬ 0 < weight i}, weight i) = 0 := by
                  apply Finset.sum_eq_zero
                  intro i _
                  exact le_antisymm (le_of_not_gt i.property) (hnonneg i)
                rw [hinactive, add_zero]
        _ = ∑ i, weight i := Fintype.sum_subtype_add_sum_subtype _ _
    simpa [A, hsum] using hactive
  let value : RealCoord (F.rank b) :=
    ∑ i : A, weight i • (points i).coord (hib i)
  have hvalue : value ∈ (F.polytope b).carrier := by
    apply (F.polytope b).convex.sum_mem (t := Finset.univ)
        (w := fun i : A ↦ weight i) (z := fun i : A ↦ (points i).coord (hib i))
    · intro i _
      exact hnonneg i
    · simpa using hsumA
    · intro i _
      exact (points i).coord_mem (hib i)
  let result : F.Point := ⟨b, value, hvalue⟩
  refine ⟨result, hnonneg, hsum, ?_, rfl⟩
  constructor
  · intro i hi
    exact hib ⟨i, hi⟩
  · intro x hx
    exact Finset.sup'_le Finset.univ_nonempty (fun i : A ↦ (points i).base)
      (fun i _ ↦ hx i i.property)

/-- The flag-convex hull from Definition 3.5. -/
def convexHull (F : ConvexFlag) (S : Set F.Point) : Set F.Point :=
  {result | ∃ (n : ℕ) (points : Fin n → F.Point) (weight : Fin n → ℝ),
    (∀ i, points i ∈ S) ∧ ConvexCombination points weight result}

/-- A designated set of proper points: it is closed under flag convex
combinations. -/
structure ProperPointSet (F : ConvexFlag) where
  carrier : Set F.Point
  convex_closed : F.convexHull carrier ⊆ carrier

namespace ProperPointSet

instance {F : ConvexFlag} : Membership F.Point (ProperPointSet F) :=
  ⟨fun Ω q ↦ q ∈ Ω.carrier⟩

end ProperPointSet

end ConvexFlag

end EGZ
