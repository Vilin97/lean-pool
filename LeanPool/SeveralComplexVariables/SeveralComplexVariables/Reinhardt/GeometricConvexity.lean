/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Homeomorph.Lemmas
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt

/-!
# Geometric convexity including zero coordinates

Geometric combinations of nonnegative radius vectors include coordinate hyperplanes. Weights are
nonnegative and sum to one, as in `Convex`. Mathlib's convention `0 ^ 0 = 1` gives the expected
endpoints. The old logarithmic-image predicate remains unchanged. Reinhardt symmetry, openness,
and completeness are separate assumptions. Positive geometric interpolation is an open map,
including on coordinate hyperplanes. Consequently, interiors preserve geometric convexity and
geometric convex hulls preserve openness.

Reference: [Korevaar–Wiegerinck][KorevaarWiegerinck2017] (2017), §2.2, Definition 2.2.3.

## Main definitions

* `geometricCombination`: Coordinatewise weighted geometric combination of nonnegative radii.
* `IsGeometricallyConvex`: Closure under geometric combinations, including zero coordinates and
  endpoint weights.
* `geometricConvexHull`: The geometric convex hull, with zero coordinates included.
* `modulusTrace`: The modulus trace of a complex coordinate set, with values in nonnegative radii.
* `HasGeometricallyConvexModuli`: Logarithmic convexity including zero coordinates is geometric
  convexity of the trace.

## Main results

* `isGeometricallyConvex_geometricConvexHull`: The geometric convex hull is geometrically convex.
* `geometricConvexHull_min`: Minimality of the geometric convex hull.
* `isOpenMap_geometricCombination`: Positive weighted geometric interpolation is an open map on
  pairs of radius vectors.
* `IsGeometricallyConvex.interior`: The interior of a geometrically convex set of radii is
  geometrically convex.
* `isOpen_geometricConvexHull`: The geometric convex hull of an open set of nonnegative radii is
  open.
* `HasGeometricallyConvexModuli.isLogarithmicallyConvex`: Strong logarithmic convexity implies
  convexity of the positive logarithmic image.

## References

* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
-/

public noncomputable section

open Set Filter
open scoped NNReal Topology

namespace SeveralComplexVariables

variable {ι : Type*}

/-- Coordinatewise weighted geometric combination of nonnegative radii. -/
@[expose] def geometricCombination (a b : ℝ) (r s : ι → ℝ≥0) : ι → ℝ≥0 :=
  fun i => r i ^ a * s i ^ b

/-- Closure under geometric combinations, including zero coordinates and endpoint weights. -/
@[expose] def IsGeometricallyConvex (S : Set (ι → ℝ≥0)) : Prop :=
  ∀ ⦃r⦄, r ∈ S → ∀ ⦃s⦄, s ∈ S → ∀ ⦃a b : ℝ⦄,
    0 ≤ a → 0 ≤ b → a + b = 1 → geometricCombination a b r s ∈ S

/-- The left endpoint of geometric interpolation. -/
@[simp] theorem geometricCombination_one_zero (r s : ι → ℝ≥0) :
    geometricCombination 1 0 r s = r := by ext i; simp [geometricCombination]

/-- The right endpoint of geometric interpolation. -/
@[simp] theorem geometricCombination_zero_one (r s : ι → ℝ≥0) :
    geometricCombination 0 1 r s = s := by ext i; simp [geometricCombination]

/-- Interpolating a radius vector with itself fixes it, including its zero coordinates. -/
theorem geometricCombination_self (r : ι → ℝ≥0) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : geometricCombination a b r r = r := by
  ext i
  simp only [geometricCombination, ← NNReal.rpow_add_of_nonneg (r i) ha hb, hab, NNReal.rpow_one]

/-- Positive interpolation weights preserve a zero from either input coordinate. -/
theorem geometricCombination_eq_zero {r s : ι → ℝ≥0} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {i : ι} (h : r i = 0 ∨ s i = 0) :
    geometricCombination a b r s i = 0 := by
  rcases h with h | h <;> simp [geometricCombination, h, ha.ne', hb.ne']

/-- A singleton of radii is geometrically convex, including when some radii are zero. -/
theorem isGeometricallyConvex_singleton (r : ι → ℝ≥0) : IsGeometricallyConvex {r} := by
  intro x hx y hy a b ha hb hab
  rw [mem_singleton_iff] at hx hy ⊢
  rw [hx, hy]
  exact geometricCombination_self r ha hb hab

/-- The empty set is geometrically convex. -/
@[simp] theorem isGeometricallyConvex_empty : IsGeometricallyConvex (∅ : Set (ι → ℝ≥0)) :=
  fun _ h => h.elim

/-- The whole space of nonnegative radii is geometrically convex. -/
@[simp] theorem isGeometricallyConvex_univ : IsGeometricallyConvex (univ : Set (ι → ℝ≥0)) :=
  fun _ _ _ _ _ _ _ _ _ => mem_univ _

/-- Arbitrary intersections preserve geometric convexity. -/
theorem isGeometricallyConvex_sInter {A : Set (Set (ι → ℝ≥0))}
    (hA : ∀ S ∈ A, IsGeometricallyConvex S) : IsGeometricallyConvex (⋂₀ A) := by
  intro r hr s hs a b ha hb hab
  exact mem_sInter.mpr fun S hS => hA S hS (mem_sInter.mp hr S hS)
    (mem_sInter.mp hs S hS) ha hb hab

/-- The geometric convex hull, with zero coordinates included. -/
@[expose] def geometricConvexHull (S : Set (ι → ℝ≥0)) : Set (ι → ℝ≥0) :=
  ⋂₀ {T | S ⊆ T ∧ IsGeometricallyConvex T}

/-- Every set is contained in its geometric convex hull. -/
theorem subset_geometricConvexHull (S : Set (ι → ℝ≥0)) : S ⊆ geometricConvexHull S :=
  fun _ hr => mem_sInter.mpr fun _ hT => hT.1 hr

/-- The geometric convex hull is geometrically convex. -/
theorem isGeometricallyConvex_geometricConvexHull (S : Set (ι → ℝ≥0)) :
    IsGeometricallyConvex (geometricConvexHull S) :=
  isGeometricallyConvex_sInter fun _ h => h.2

/-- Minimality of the geometric convex hull. -/
theorem geometricConvexHull_min {S T : Set (ι → ℝ≥0)} (hST : S ⊆ T)
    (hT : IsGeometricallyConvex T) : geometricConvexHull S ⊆ T :=
  fun _ h => mem_sInter.mp h T ⟨hST, hT⟩

/-- Taking the geometric convex hull is monotone. -/
theorem geometricConvexHull_mono {S T : Set (ι → ℝ≥0)} (h : S ⊆ T) :
    geometricConvexHull S ⊆ geometricConvexHull T :=
  geometricConvexHull_min (h.trans (subset_geometricConvexHull T))
    (isGeometricallyConvex_geometricConvexHull T)

/-- A geometrically convex set equals its hull. -/
theorem IsGeometricallyConvex.geometricConvexHull_eq {S : Set (ι → ℝ≥0)}
    (h : IsGeometricallyConvex S) : geometricConvexHull S = S :=
  Subset.antisymm (geometricConvexHull_min Subset.rfl h) (subset_geometricConvexHull S)

/-- Multiplication of nonnegative radii is open, including at the pair of zero radii. -/
private theorem isOpenMap_nnreal_mul : IsOpenMap (fun p : ℝ≥0 × ℝ≥0 => p.1 * p.2) := by
  intro S hS
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨⟨r, s⟩, hrs, rfl⟩
  by_cases hr : r = 0
  · subst r
    by_cases hs : s = 0
    · subst s
      have h : Tendsto (fun t : ℝ≥0 => (NNReal.sqrt t, NNReal.sqrt t))
          (𝓝 (0 * 0)) (𝓝 (0, 0)) := by
        simpa using (NNReal.continuous_sqrt.prodMk NNReal.continuous_sqrt).tendsto 0
      filter_upwards [h.eventually (hS.mem_nhds hrs)] with t ht
      exact ⟨(NNReal.sqrt t, NNReal.sqrt t), ht, NNReal.mul_self_sqrt t⟩
    · have h : Tendsto (fun t : ℝ≥0 => (t / s, s)) (𝓝 (0 * s)) (𝓝 (0, s)) := by
        simpa using ((continuous_id.div_const s).prodMk continuous_const).tendsto 0
      filter_upwards [h.eventually (hS.mem_nhds hrs)] with t ht
      exact ⟨(t / s, s), ht, div_mul_cancel₀ t hs⟩
  · have h : Tendsto (fun t : ℝ≥0 => (r, t / r)) (𝓝 (r * s)) (𝓝 (r, s)) := by
      simpa [mul_div_cancel_left₀ s hr] using
        (continuous_const.prodMk (continuous_id.div_const r)).tendsto (r * s)
    filter_upwards [h.eventually (hS.mem_nhds hrs)] with t ht
    exact ⟨(r, t / r), ht, mul_div_cancel₀ t hr⟩

/-- Positive weighted geometric interpolation is an open map on pairs of radius vectors. -/
theorem isOpenMap_geometricCombination {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsOpenMap (fun p : (ι → ℝ≥0) × (ι → ℝ≥0) => geometricCombination a b p.1 p.2) := by
  have hscalar : IsOpenMap (fun p : ℝ≥0 × ℝ≥0 => p.1 ^ a * p.2 ^ b) :=
    isOpenMap_nnreal_mul.comp
      ((NNReal.orderIsoRpow a ha).toHomeomorph.isOpenMap.prodMap
        (NNReal.orderIsoRpow b hb).toHomeomorph.isOpenMap)
  have hsurj : Function.Surjective (fun p : ℝ≥0 × ℝ≥0 => p.1 ^ a * p.2 ^ b) := by
    intro t
    obtain ⟨r, hr⟩ := NNReal.rpow_left_surjective ha.ne' t
    exact ⟨(r, 1), by simp [hr]⟩
  let e : ((ι → ℝ≥0) × (ι → ℝ≥0)) ≃ₜ (ι → ℝ≥0 × ℝ≥0) :=
    { toFun := fun p i => (p.1 i, p.2 i)
      invFun := fun p => (fun i => (p i).1, fun i => (p i).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact (IsOpenMap.piMap (fun _ : ι => hscalar) (.of_forall fun _ => hsurj)).comp e.isOpenMap

/-- The interior of a geometrically convex set of radii is geometrically convex. -/
theorem IsGeometricallyConvex.interior {S : Set (ι → ℝ≥0)}
    (hS : IsGeometricallyConvex S) : IsGeometricallyConvex (interior S) := by
  intro r hr s hs a b ha hb hab
  rcases ha.eq_or_lt with ha | ha
  · have hb : b = 1 := by linarith
    simpa [← ha, hb] using hs
  rcases hb.eq_or_lt with hb | hb
  · have ha : a = 1 := by linarith
    simpa [ha, ← hb] using hr
  let g := fun p : (ι → ℝ≥0) × (ι → ℝ≥0) => geometricCombination a b p.1 p.2
  have ho : IsOpen (g '' (_root_.interior S ×ˢ _root_.interior S)) :=
    isOpenMap_geometricCombination ha hb _ (isOpen_interior.prod isOpen_interior)
  have hsub : g '' (_root_.interior S ×ˢ _root_.interior S) ⊆ S := by
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact hS (interior_subset hx) (interior_subset hy) ha.le hb.le hab
  exact (ho.subset_interior_iff.mpr hsub) ⟨(r, s), ⟨hr, hs⟩, rfl⟩

/-- The geometric convex hull of an open set of nonnegative radii is open. -/
theorem isOpen_geometricConvexHull {S : Set (ι → ℝ≥0)} (hS : IsOpen S) :
    IsOpen (geometricConvexHull S) :=
  subset_interior_iff_isOpen.mp (geometricConvexHull_min
    (hS.subset_interior_iff.mpr (subset_geometricConvexHull S))
    (isGeometricallyConvex_geometricConvexHull S).interior)

/-- Taking a geometric convex hull twice has no further effect. -/
@[simp] theorem geometricConvexHull_idem (S : Set (ι → ℝ≥0)) :
    geometricConvexHull (geometricConvexHull S) = geometricConvexHull S :=
  (isGeometricallyConvex_geometricConvexHull S).geometricConvexHull_eq

/-- The empty set has empty geometric convex hull. -/
@[simp] theorem geometricConvexHull_empty : geometricConvexHull (∅ : Set (ι → ℝ≥0)) = ∅ :=
  isGeometricallyConvex_empty.geometricConvexHull_eq

/-- A singleton is fixed by the geometric convex hull. -/
@[simp] theorem geometricConvexHull_singleton (r : ι → ℝ≥0) : geometricConvexHull {r} = {r} :=
  (isGeometricallyConvex_singleton r).geometricConvexHull_eq

/-- The modulus trace of a complex coordinate set, with values in nonnegative radii. -/
@[expose] def modulusTrace (U : Set (ι → ℂ)) : Set (ι → ℝ≥0) :=
  (fun z i => ‖z i‖₊) '' U

/-- Logarithmic convexity including zero coordinates is geometric convexity of the trace. This does
not impose Reinhardt symmetry, openness, or completeness. -/
@[expose] def HasGeometricallyConvexModuli (U : Set (ι → ℂ)) : Prop :=
  IsGeometricallyConvex (modulusTrace U)

/-- For a Reinhardt set, a radius vector belongs to the trace exactly when its positive real
representative belongs to the set. -/
theorem IsReinhardt.mem_modulusTrace_iff {U : Set (ι → ℂ)} (hU : IsReinhardt U)
    {r : ι → ℝ≥0} : r ∈ modulusTrace U ↔ (fun i => (r i : ℂ)) ∈ U := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hU hz (fun i => by simp)
  · intro h
    refine ⟨_, h, ?_⟩
    ext i
    simp

/-- Strong logarithmic convexity implies convexity of the positive logarithmic image. -/
theorem HasGeometricallyConvexModuli.isLogarithmicallyConvex {U : Set (ι → ℂ)}
    (h : HasGeometricallyConvexModuli U) (hU : IsReinhardt U) : IsLogarithmicallyConvex U := by
  intro x hx y hy a b ha hb hab
  let r : ι → ℝ≥0 := fun i => ⟨Real.exp (x i), (Real.exp_pos _).le⟩
  let s : ι → ℝ≥0 := fun i => ⟨Real.exp (y i), (Real.exp_pos _).le⟩
  have hr : r ∈ modulusTrace U := hU.mem_modulusTrace_iff.mpr hx
  have hs : s ∈ modulusTrace U := hU.mem_modulusTrace_iff.mpr hy
  have hm := hU.mem_modulusTrace_iff.mp (h hr hs ha hb hab)
  have he : (fun i => (Real.exp ((a • x + b • y) i) : ℂ)) =
      (fun i => (geometricCombination a b r s i : ℂ)) := by
    ext i
    apply congrArg Complex.ofReal
    change Real.exp (a * x i + b * y i) = ((r i ^ a * s i ^ b : ℝ≥0) : ℝ)
    rw [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_rpow]
    change Real.exp (a * x i + b * y i) = Real.exp (x i) ^ a * Real.exp (y i) ^ b
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  change (fun i => (Real.exp ((a • x + b • y) i) : ℂ)) ∈ U
  rw [he]
  exact hm

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
