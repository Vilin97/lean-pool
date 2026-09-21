/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Coordinates on the standard simplex and its affine hull

This file develops algebraic and ordered coordinate constructions for `Convexity.StdSimplex R ι`.
The affine coordinate chart is available over a commutative ring, while statements involving
simplex inequalities use a compatible partial order. The final section gives the topological
properties of these coordinate charts over `ℝ`.

For a finite index type `ι` and a chosen coordinate `i : ι`, the affine hyperplane
`∑ j, u j = 1` is parametrized by the remaining `card ι - 1` coordinates, with the omitted
coordinate reconstructed as `1 - ∑ j, u j`.

The ambient coordinate declarations remain in the root namespace. Declarations whose target is
Mathlib's intrinsic simplex are placed in `Convexity.StdSimplex`. None of this material belongs
to a measure-theory namespace.

## Main definitions and results

* `stdSimplexAffineSet`: the affine hyperplane `∑ j, u j = 1`.
* `stdSimplexAffineBasis`: the standard vertices as an affine basis of that hyperplane.
* `stdSimplexCoordEquiv`: its parametrization by `card ι - 1` free coordinates.
* `stdSimplexFreeCoords`: the filled simplex in free coordinates.
* `Convexity.StdSimplex.equivFreeCoords`: the corresponding parametrization of Mathlib's
  intrinsic standard simplex.

The affine hyperplane is identified with Mathlib's `fintypeAffineCoords`.  The standard
vertices form an affine basis of this hyperplane, and its barycentric coordinates are the
ordinary ambient coordinates.  We nevertheless retain the explicit omitted-coordinate chart:
its computational formulas are used by the measure and integral theory.
-/

@[expose] public noncomputable section StdSimplexCoordinates

/- Defining the standard index set as a `Type*`. -/
variable {ι : Type*} [Fintype ι]
variable {R : Type*}

open scoped Classical
open Convexity

section Ring

variable [CommRing R]

/-- The affine hyperplane `{x | ∑ j, x j = 1}` (the affine hull of the standard simplex),
viewed as a plain set.  This is the carrier of Mathlib's `fintypeAffineCoords`. -/
abbrev stdSimplexAffineSet : Set (ι → R) :=
  fintypeAffineCoords ι R

/-- Compatibility name for `Fintype.sum_eq_add_sum_subtype_ne`. -/
theorem sum_eq_apply_add_sum_ne (u : ι → R) (i : ι) :
    ∑ j, u j = u i + ∑ j : {j : ι // j ≠ i}, u j := by
  classical
  exact Fintype.sum_eq_add_sum_subtype_ne u i

/-- The affine hyperplane `{x | ∑ j, x j = 1}` as an `AffineSubspace`. -/
abbrev stdSimplexAffineSubspace : AffineSubspace R (ι → R) :=
  fintypeAffineCoords ι R

/-- The elements of the affine subspace are exactly the elements of the affine set. -/
@[simp] theorem mem_stdSimplexAffineSubspace_iff (x : ι → R) :
    x ∈ stdSimplexAffineSubspace (R := R) ↔ x ∈ stdSimplexAffineSet := by
  rfl

section StandardAffineBasis

variable [Nonempty ι]

/-- The standard vertex indexed by `i`, regarded as a point of the affine coordinate
hyperplane. -/
def stdSimplexAffineVertex (i : ι) : fintypeAffineCoords ι R :=
  ⟨Pi.single i 1, mem_fintypeAffineCoords_iff_sum.mpr (by simp)⟩

omit [Nonempty ι] in
/-- The ambient coordinate of a standard affine vertex is a Kronecker delta. -/
@[simp] theorem stdSimplexAffineVertex_apply (i j : ι) :
    (stdSimplexAffineVertex (R := R) i : ι → R) j = if i = j then 1 else 0 := by
  change Pi.single i 1 j = _
  simp [Pi.single_apply, eq_comm]

local instance : Nonempty (fintypeAffineCoords ι R) :=
  ⟨stdSimplexAffineVertex (Classical.choice ‹Nonempty ι›)⟩

/-- Applying the inclusion of the affine coordinate hyperplane to a standard vertex gives
the corresponding Kronecker-delta function. -/
@[simp] theorem stdSimplexAffineVertex_subtype_apply (i j : ι) :
    (fintypeAffineCoords ι R).subtype (stdSimplexAffineVertex (R := R) i) j =
      if i = j then 1 else 0 :=
  stdSimplexAffineVertex_apply i j

/-- The standard vertices are affinely independent in the affine coordinate hyperplane. -/
theorem affineIndependent_stdSimplexAffineVertex :
    AffineIndependent R (V := (fintypeAffineCoords ι R).direction)
      (stdSimplexAffineVertex (ι := ι) (R := R)) := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro w₁ w₂ hw₁ hw₂ h
  apply funext
  intro j
  have hmap := congrArg (fintypeAffineCoords ι R).subtype h
  rw [Finset.univ.map_affineCombination _ _ hw₁,
    Finset.univ.map_affineCombination _ _ hw₂] at hmap
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hw₁),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hw₂)] at hmap
  have hj := congrFun hmap j
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
    stdSimplexAffineVertex_subtype_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using hj

/-- Every point of the affine coordinate hyperplane is the affine combination of the standard
vertices with weights given by its ambient coordinates. -/
theorem affineCombination_stdSimplexAffineVertex (u : fintypeAffineCoords ι R) :
    Finset.univ.affineCombination R (stdSimplexAffineVertex (ι := ι) (R := R)) u.1 = u := by
  have hu : ∑ i, u.1 i = 1 := mem_fintypeAffineCoords_iff_sum.mp u.2
  apply Subtype.ext
  change (fintypeAffineCoords ι R).subtype
    (Finset.univ.affineCombination R stdSimplexAffineVertex u.1) = u.1
  rw [Finset.univ.map_affineCombination _ _ hu]
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hu)]
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
    stdSimplexAffineVertex_subtype_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The standard vertices affinely span the affine coordinate hyperplane. -/
theorem affineSpan_stdSimplexAffineVertex :
    affineSpan R (V := (fintypeAffineCoords ι R).direction)
      (Set.range (stdSimplexAffineVertex (ι := ι) (R := R))) = ⊤ := by
  apply le_antisymm le_top
  intro u _
  have hu : ∑ i, u.1 i = 1 := mem_fintypeAffineCoords_iff_sum.mp u.2
  rw [← affineCombination_stdSimplexAffineVertex u]
  exact affineCombination_mem_affineSpan_of_nonempty hu _

/-- The standard vertices form an affine basis of Mathlib's affine coordinate hyperplane. -/
def stdSimplexAffineBasis : AffineBasis ι R (fintypeAffineCoords ι R) :=
  ⟨stdSimplexAffineVertex, affineIndependent_stdSimplexAffineVertex,
    affineSpan_stdSimplexAffineVertex⟩

/-- The points of `stdSimplexAffineBasis` are the standard affine vertices. -/
@[simp] theorem stdSimplexAffineBasis_apply (i : ι) :
    stdSimplexAffineBasis (R := R) i = stdSimplexAffineVertex i :=
  rfl

/-- Barycentric coordinates for the standard affine basis are the ordinary ambient
coordinates. -/
@[simp] theorem stdSimplexAffineBasis_coord (i : ι) (u : fintypeAffineCoords ι R) :
    (stdSimplexAffineBasis (R := R)).coord i u = u.1 i := by
  calc
    (stdSimplexAffineBasis (R := R)).coord i u =
        (stdSimplexAffineBasis (R := R)).coord i
          (Finset.univ.affineCombination R stdSimplexAffineBasis u.1) := by
      rw [show Finset.univ.affineCombination R stdSimplexAffineBasis u.1 = u by
        change Finset.univ.affineCombination R stdSimplexAffineVertex u.1 = u
        exact affineCombination_stdSimplexAffineVertex u]
    _ = u.1 i := by
      exact (stdSimplexAffineBasis (R := R)).coord_apply_combination_of_mem
        (Finset.mem_univ i) (mem_fintypeAffineCoords_iff_sum.mp u.2)

end StandardAffineBasis

/-- The coordinate projection that eliminates coordinate `i`. -/
def stdSimplexCoordProj (i : ι) (u : ι → R) :
    {j : ι // j ≠ i} → R :=
  fun j => u j

/-- Map from the free-coordinate space that omits coordinate `i` to `stdSimplexAffineSet`,
constructed by pairing the recovered dependent coordinate with `x`, then applying the inverse of
`Equiv.funSplitAt i R`. -/
def stdSimplexCoordMap (i : ι) (x : {j : ι // j ≠ i} → R) : ι → R :=
  (Equiv.funSplitAt i R).symm (1 - ∑ j, x j, x)

/-- The value of the dependent coordinate `i` is `1 - ∑ j, x j`. -/
@[simp] theorem stdSimplexCoordMap_apply_self (i : ι) (x : {j : ι // j ≠ i} → R) :
    stdSimplexCoordMap i x i = 1 - ∑ j, x j := by
  simp [stdSimplexCoordMap]

/-- The value of a free coordinate `j ≠ i` remains unchanged under the coordinate map. -/
@[simp] theorem stdSimplexCoordMap_apply_of_ne (i j : ι) (h : j ≠ i)
    (x : {j : ι // j ≠ i} → R) :
    stdSimplexCoordMap i x j = x ⟨j, h⟩ := by
  simp [stdSimplexCoordMap, h]

/-- The coordinate map maps to `stdSimplexAffineSet`. -/
@[simp] theorem sum_stdSimplexCoordMap (i : ι) (x : {j : ι // j ≠ i} → R) :
    ∑ j, stdSimplexCoordMap i x j = 1 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i,
    stdSimplexCoordMap_apply_self]
  have h : (∑ j : {j : ι // j ≠ i}, stdSimplexCoordMap i x j) = ∑ j, x j := by
    apply Finset.sum_congr rfl
    intro j _
    exact stdSimplexCoordMap_apply_of_ne i j j.property x
  rw [h]
  ring

/-- Projecting after applying the coordinate map recovers the free coordinates. -/
@[simp] theorem stdSimplexCoordProj_coordMap
    (i : ι) (x : {j : ι // j ≠ i} → R) :
    stdSimplexCoordProj i (stdSimplexCoordMap i x) = x := by
  ext ⟨j, hj⟩
  simp [stdSimplexCoordProj, stdSimplexCoordMap, hj]

/-- Applying the coordinate map after projecting recovers the vector on
`stdSimplexAffineSet`. -/
theorem stdSimplexCoordMap_coordProj
    (i : ι) {u : ι → R}
    (hu : u ∈ stdSimplexAffineSet) :
    stdSimplexCoordMap i (stdSimplexCoordProj i u) = u := by
  change u ∈ fintypeAffineCoords ι R at hu
  funext j
  by_cases hji : j = i
  · subst j
    rw [stdSimplexCoordMap_apply_self]
    change 1 - ∑ j : {j : ι // j ≠ i}, u j = u i
    have hsum := Fintype.sum_eq_add_sum_subtype_ne u i
    rw [mem_fintypeAffineCoords_iff_sum] at hu
    rw [hu] at hsum
    rw [hsum]
    ring
  · simp [stdSimplexCoordMap_apply_of_ne,
      stdSimplexCoordProj, hji]

/-- The range of `stdSimplexCoordMap` is the affine hyperplane `stdSimplexAffineSet`. -/
theorem range_stdSimplexCoordMap (i : ι) :
    Set.range (stdSimplexCoordMap (R := R) i) = stdSimplexAffineSet := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    exact mem_fintypeAffineCoords_iff_sum.mpr (sum_stdSimplexCoordMap i x)
  · intro hu
    refine ⟨stdSimplexCoordProj i u, ?_⟩
    exact stdSimplexCoordMap_coordProj i hu

/-- The coordinate map relates stdSimplexCoordMap (σ i) composed with σ to
stdSimplexCoordMap i applied to the permuted free coordinates. -/
theorem stdSimplexCoordMap_comp_perm (i : ι) (σ : Equiv.Perm ι)
    (x : {j : ι // j ≠ σ i} → R) :
  stdSimplexCoordMap (σ i) x ∘ σ =
    stdSimplexCoordMap i (fun ⟨j, hj⟩ ↦
      x ⟨σ j, fun h ↦ hj (σ.injective h)⟩) := by
  have hu : stdSimplexCoordMap (σ i) x ∘ σ ∈ stdSimplexAffineSet := by
    change stdSimplexCoordMap (σ i) x ∘ σ ∈ fintypeAffineCoords ι R
    rw [mem_fintypeAffineCoords_iff_sum]
    have hsum : ∑ q, stdSimplexCoordMap (σ i) x q = 1 :=
      sum_stdSimplexCoordMap (σ i) x
    rw [← hsum]
    exact Equiv.sum_comp σ (stdSimplexCoordMap (σ i) x)
  symm
  rw [← stdSimplexCoordMap_coordProj i hu]
  congr 1
  funext ⟨j, hj⟩
  change x ⟨σ j, _⟩ = stdSimplexCoordMap (σ i) x (σ j)
  rw [stdSimplexCoordMap_apply_of_ne (σ i) (σ j) (fun h => hj (σ.injective h))]

/-- The linear part of the change of free coordinates induced by swapping the omitted
coordinate `i` with a different coordinate `j`. -/
def stdSimplexFreeCoordSwapLinear (i j : ι) (hij : i ≠ j) :
    ({q : ι // q ≠ i} → R) →ₗ[R] ({q : ι // q ≠ i} → R) :=
  let ji : {q : ι // q ≠ i} := ⟨j, Ne.symm hij⟩
  { toFun := fun x q => if q = ji then - ∑ r, x r else x q
    map_add' := by
      intro x y
      funext q
      by_cases hq : q = ji
      · simp [hq, Finset.sum_add_distrib]
        ring
      · simp [hq]
    map_smul' := by
      intro c x
      funext q
      by_cases hq : q = ji
      · simp [hq, Finset.mul_sum]
      · simp [hq] }

/-- The sum of the coordinates after applying `stdSimplexFreeCoordSwapLinear` is the
negative of the coordinate belonging to `j`. -/
theorem sum_stdSimplexFreeCoordSwapLinear (i j : ι) (hij : i ≠ j)
    (x : {q : ι // q ≠ i} → R) :
    ∑ q, stdSimplexFreeCoordSwapLinear i j hij x q = -x ⟨j, Ne.symm hij⟩ := by
  let ji : {q : ι // q ≠ i} := ⟨j, Ne.symm hij⟩
  let L := stdSimplexFreeCoordSwapLinear (R := R) i j hij
  calc
    ∑ q, L x q = (∑ q ∈ Finset.univ.erase ji, L x q) + L x ji :=
      (Finset.sum_erase_add Finset.univ (fun q => L x q) (Finset.mem_univ ji)).symm
    _ = (∑ q ∈ Finset.univ.erase ji, x q) + (-∑ q, x q) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro q hq
        simp [L, stdSimplexFreeCoordSwapLinear, ji, Finset.ne_of_mem_erase hq]
      · simp [L, stdSimplexFreeCoordSwapLinear, ji]
    _ = -x ji := by
      have hx := Finset.sum_erase_add Finset.univ x (Finset.mem_univ ji)
      rw [← hx]
      abel

/-- The affine change of free coordinates induced by swapping `i` and `j` in the ambient
coordinate space. -/
def stdSimplexFreeCoordSwap (i j : ι) (hij : i ≠ j)
    (x : {q : ι // q ≠ i} → R) : {q : ι // q ≠ i} → R :=
  let ji : {q : ι // q ≠ i} := ⟨j, Ne.symm hij⟩
  (fun q => if q = ji then 1 else 0) + stdSimplexFreeCoordSwapLinear i j hij x

/-- At the free coordinate corresponding to `j`, the coordinate swap stores the dependent
coordinate recovered from `x`. -/
@[simp] theorem stdSimplexFreeCoordSwap_apply_ji (i j : ι) (hij : i ≠ j)
    (x : {q : ι // q ≠ i} → R) :
    stdSimplexFreeCoordSwap i j hij x ⟨j, Ne.symm hij⟩ = 1 - ∑ q, x q := by
  simp [stdSimplexFreeCoordSwap, stdSimplexFreeCoordSwapLinear]
  ring

/-- A free coordinate other than the one corresponding to `j` is unchanged by the coordinate
swap. -/
@[simp] theorem stdSimplexFreeCoordSwap_apply_of_ne (i j : ι) (hij : i ≠ j)
    {x : {q : ι // q ≠ i} → R} {q : {q : ι // q ≠ i}} (hq : q ≠ ⟨j, Ne.symm hij⟩) :
    stdSimplexFreeCoordSwap i j hij x q = x q := by
  simp [stdSimplexFreeCoordSwap, stdSimplexFreeCoordSwapLinear, hq]

/-- The sum of the coordinates after applying `stdSimplexFreeCoordSwap`. -/
@[simp] theorem sum_stdSimplexFreeCoordSwap (i j : ι) (hij : i ≠ j)
    (x : {q : ι // q ≠ i} → R) :
    ∑ q, stdSimplexFreeCoordSwap i j hij x q = 1 - x ⟨j, Ne.symm hij⟩ := by
  simp_rw [stdSimplexFreeCoordSwap, Pi.add_apply]
  rw [Finset.sum_add_distrib, sum_stdSimplexFreeCoordSwapLinear]
  have hc : (∑ q : {q : ι // q ≠ i}, if q = (⟨j, Ne.symm hij⟩ : {q : ι // q ≠ i})
      then (1 : R) else 0) = 1 := by
    simpa using Finset.sum_ite_eq' Finset.univ (⟨j, Ne.symm hij⟩ : {q : ι // q ≠ i})
      (fun _ => (1 : R))
  rw [hc]
  ring

/-- Swapping `i` and `j` in ambient coordinates corresponds to
`stdSimplexFreeCoordSwap` in the chart omitting `i`. -/
theorem stdSimplexCoordMap_comp_freeCoordSwap (i j : ι) (hij : i ≠ j) :
    (fun u : ι → R => u ∘ Equiv.swap i j) ∘ stdSimplexCoordMap i =
      stdSimplexCoordMap i ∘ stdSimplexFreeCoordSwap i j hij := by
  funext x q
  by_cases hqi : q = i
  · subst q
    simp only [Function.comp_apply, Equiv.swap_apply_left]
    rw [stdSimplexCoordMap_apply_of_ne i j (Ne.symm hij), stdSimplexCoordMap_apply_self,
      sum_stdSimplexFreeCoordSwap]
    ring
  · by_cases hqj : q = j
    · subst q
      simp only [Function.comp_apply, Equiv.swap_apply_right, stdSimplexCoordMap_apply_self]
      rw [stdSimplexCoordMap_apply_of_ne i j (Ne.symm hij),
        stdSimplexFreeCoordSwap_apply_ji]
    · rw [Function.comp_apply, Function.comp_apply,
        Equiv.swap_apply_of_ne_of_ne hqi hqj,
        stdSimplexCoordMap_apply_of_ne i q hqi]
      change x ⟨q, hqi⟩ =
        stdSimplexCoordMap i (stdSimplexFreeCoordSwap i j hij x) q
      rw [stdSimplexCoordMap_apply_of_ne i q hqi]
      symm
      apply stdSimplexFreeCoordSwap_apply_of_ne
      intro h
      exact hqj (congrArg Subtype.val h)

/-- The free coordinates obtained by omitting `i` are equivalent to
`stdSimplexAffineSet`. -/
def stdSimplexCoordEquiv (i : ι) :
    ({j : ι // j ≠ i} → R) ≃ stdSimplexAffineSet (R := R) (ι := ι) where
  toFun x :=
    ⟨stdSimplexCoordMap i x,
      mem_fintypeAffineCoords_iff_sum.mpr (sum_stdSimplexCoordMap i x)⟩
  invFun u :=
    stdSimplexCoordProj i u.1
  left_inv x := by
    simp
  right_inv u := by
    apply Subtype.ext
    exact stdSimplexCoordMap_coordProj i u.property

/-- The coordinate map is injective. -/
theorem injective_stdSimplexCoordMap (i : ι) :
    Function.Injective (stdSimplexCoordMap (R := R) i) := by
  intro x y hxy
  have h := congrArg (stdSimplexCoordProj i) hxy
  simpa using h

end Ring

section OrderedRing

variable [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- The filled `(card ι - 1)`-dimensional simplex of free coordinates corresponding to
points of `Convexity.StdSimplex.coordinateSet R ι`. (Not to be confused with `Convexity.StdSimplex.coordinateSet R {j // j ≠ i}`.) -/
def stdSimplexFreeCoords (i : ι) :
    Set ({j : ι // j ≠ i} → R) :=
  {x | (∀ j, 0 ≤ x j) ∧ ∑ j, x j ≤ 1}

end OrderedRing

namespace Convexity.StdSimplex

section OrderedRing

variable [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- Omitted-coordinate parametrization of Mathlib's intrinsic standard simplex.

The forward map stores the reconstructed coordinates as finitely supported `weights`; the
inverse map drops coordinate `i`. This is the algebraic precursor of the corresponding
homeomorphism. -/
def equivFreeCoords (i : ι) :
    stdSimplexFreeCoords (R := R) i ≃ StdSimplex R ι where
  toFun x :=
    { weights := Finsupp.equivFunOnFinite.symm (stdSimplexCoordMap i x.1)
      nonneg := by
        intro j
        change 0 ≤ stdSimplexCoordMap i x.1 j
        by_cases hji : j = i
        · subst j
          rw [stdSimplexCoordMap_apply_self]
          exact sub_nonneg.mpr x.2.2
        · rw [stdSimplexCoordMap_apply_of_ne i j hji]
          exact x.2.1 ⟨j, hji⟩
      total := by
        simp [Finsupp.sum_fintype, sum_stdSimplexCoordMap] }
  invFun s :=
    ⟨stdSimplexCoordProj i (fun j ↦ s.weights j), by
      refine ⟨fun j ↦ s.nonneg j, ?_⟩
      have hs : ∑ j, s.weights j = 1 := by
        simpa [Finsupp.sum_fintype] using s.total
      rw [← hs, Fintype.sum_eq_add_sum_subtype_ne (fun j ↦ s.weights j) i]
      exact le_add_of_nonneg_left (s.nonneg i)⟩
  left_inv x := by
    apply Subtype.ext
    exact stdSimplexCoordProj_coordMap i x.1
  right_inv s := by
    apply StdSimplex.ext
    apply Finsupp.ext
    intro j
    change stdSimplexCoordMap i (stdSimplexCoordProj i (fun q ↦ s.weights q)) j = s.weights j
    exact congrFun (stdSimplexCoordMap_coordProj i <|
      mem_fintypeAffineCoords_iff_sum.mpr <| by
        simpa [Finsupp.sum_fintype] using s.total) j

/-- The weights of the intrinsic simplex point associated to free coordinates are the
coordinates reconstructed by `stdSimplexCoordMap`. -/
@[simp] theorem weights_equivFreeCoords_apply (i : ι)
    (x : stdSimplexFreeCoords (R := R) i) (j : ι) :
    (equivFreeCoords i x).weights j = stdSimplexCoordMap i x.1 j :=
  rfl

/-- The inverse of `equivFreeCoords` drops the chosen coordinate from the weight function. -/
@[simp] theorem coe_equivFreeCoords_symm_apply (i : ι) (s : StdSimplex R ι) :
    ((equivFreeCoords i).symm s : {j : ι // j ≠ i} → R) =
      stdSimplexCoordProj i (fun j ↦ s.weights j) :=
  rfl

end OrderedRing

end Convexity.StdSimplex

section RealTopology

/-- `stdSimplexAffineSet` is closed over the reals. -/
theorem isClosed_stdSimplexAffineSet :
    IsClosed (stdSimplexAffineSet (R := ℝ) (ι := ι)) := by
  have heq : stdSimplexAffineSet (R := ℝ) (ι := ι) =
      (fun x : ι → ℝ ↦ ∑ i, x i) ⁻¹' {1} := by
    ext x
    change x ∈ fintypeAffineCoords ι ℝ ↔ _
    simp only [Set.mem_preimage, Set.mem_singleton_iff, mem_fintypeAffineCoords_iff_sum]
  rw [heq]
  exact isClosed_singleton.preimage
    (continuous_finsetSum _ (fun i _ ↦ continuous_apply i))

/-- The free-coordinate swap is continuous over the reals. -/
theorem continuous_stdSimplexFreeCoordSwap (i j : ι) (hij : i ≠ j) :
    Continuous (stdSimplexFreeCoordSwap (R := ℝ) i j hij) := by
  apply continuous_pi
  intro q
  unfold stdSimplexFreeCoordSwap stdSimplexFreeCoordSwapLinear
  dsimp
  split_ifs <;> fun_prop

/-- The real coordinate map is continuous. -/
theorem continuous_stdSimplexCoordMap (i : ι) :
    Continuous (stdSimplexCoordMap (R := ℝ) i) := by
  unfold stdSimplexCoordMap
  exact (Homeomorph.funSplitAt ℝ i).symm.continuous.comp
    (continuous_const.sub (continuous_finsetSum _ (fun j _ => continuous_apply j))
      |>.prodMk continuous_id)

omit [Fintype ι] in
/-- The real coordinate projection is continuous. -/
theorem continuous_stdSimplexCoordProj (i : ι) :
    Continuous (stdSimplexCoordProj (R := ℝ) i) := by
  exact continuous_pi (fun j => continuous_apply j.val)

/-- The real free-coordinate equivalence with `stdSimplexAffineSet` is a homeomorphism. -/
def stdSimplexCoordHomeomorph (i : ι) :
    ({j : ι // j ≠ i} → ℝ) ≃ₜ stdSimplexAffineSet (R := ℝ) (ι := ι) where
  toEquiv := stdSimplexCoordEquiv (R := ℝ) i
  continuous_toFun :=
    (continuous_stdSimplexCoordMap i).subtype_mk _
  continuous_invFun :=
    (continuous_stdSimplexCoordProj i).comp continuous_subtype_val

/-- The real coordinate map gives a closed embedding. -/
theorem isClosedEmbedding_stdSimplexCoordMap (i : ι) :
    Topology.IsClosedEmbedding (stdSimplexCoordMap (R := ℝ) i) :=
  (isClosed_stdSimplexAffineSet (ι := ι)).isClosedEmbedding_subtypeVal.comp
    (stdSimplexCoordHomeomorph i).isClosedEmbedding

end RealTopology

end StdSimplexCoordinates
