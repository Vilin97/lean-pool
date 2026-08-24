/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.Brouwer
import LeanPool.ClassificationOfSurfaces.Surface

/-!
# Boundary invariance for C0 surface charts

This file discharges the `ChartBoundaryInvariant` interface for topological surface charts.
The plane has invariance of domain by `Moise.instBrouwerFixedPointPlane` and the general
invariance-of-domain theorem.  Steven Sivek's chart-independence argument then shows that a
manifold-boundary point is sent to the frontier of the model range by every chart containing it.
The frontier of the chart's extended target follows because its interior is contained in the
interior of the model range.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open InvarianceOfDomain Set

/-- C0 invariance of the boundary stratum for surface charts, derived from planar invariance of
domain. -/
instance chartBoundaryInvariant_of_invarianceOfDomain
    (S : Type*) [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S] :
    ChartBoundaryInvariant S where
  chartAt_extend_mem_frontier_target_of_boundary := by
    intro x y hySource hyBoundary
    let I := modelWithCornersEuclideanHalfSpace 2
    let f := chartAt (EuclideanHalfSpace 2) x
    change f.extend I y ∈ frontier (f.extend I).target
    have hyFrontierRange : f.extend I y ∈ frontier (Set.range I) := by
      exact (isBoundaryPoint_iff_any_chart I (f := f) hySource).mp hyBoundary
    have hyTarget : f.extend I y ∈ (f.extend I).target := by
      apply (f.extend I).map_source
      rwa [f.extend_source]
    apply (mem_frontier_iff_notMem_interior hyTarget).2
    intro hyInterior
    have hyNotInteriorRange : f.extend I y ∉ interior (Set.range I) :=
      (mem_frontier_iff_notMem_interior (Set.mem_range_self (f y))).1 hyFrontierRange
    exact hyNotInteriorRange (f.interior_extend_target_subset_interior_range hyInterior)

/-- Reflection in the boundary line of the Euclidean half-plane. -/
def reflectAcrossHalfPlaneBoundary (p : Moise.Plane) : Moise.Plane :=
  WithLp.toLp 2 (fun i => if i = 0 then -p i else p i)

/-- Fold the plane onto the Euclidean half-plane by taking the absolute value of its normal
coordinate. -/
def foldPlaneToHalfSpace (p : Moise.Plane) : EuclideanHalfSpace 2 :=
  ⟨WithLp.toLp 2 (fun i => if i = 0 then |p i| else p i), by simp⟩

/-- Reflection across the boundary line is continuous. -/
theorem continuous_reflectAcrossHalfPlaneBoundary :
    Continuous reflectAcrossHalfPlaneBoundary := by
  unfold reflectAcrossHalfPlaneBoundary
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, one_ne_zero] <;>
    fun_prop

/-- Folding the plane onto the Euclidean half-plane is continuous. -/
theorem continuous_foldPlaneToHalfSpace :
    Continuous foldPlaneToHalfSpace := by
  unfold foldPlaneToHalfSpace
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, one_ne_zero] <;>
    fun_prop

/-- Reflection across the boundary line is injective. -/
theorem injective_reflectAcrossHalfPlaneBoundary :
    Function.Injective reflectAcrossHalfPlaneBoundary := by
  intro p q hpq
  have h := congrArg reflectAcrossHalfPlaneBoundary hpq
  apply PiLp.ext
  intro i
  have hi := congrArg (fun z : Moise.Plane => z i) h
  fin_cases i <;> simpa [reflectAcrossHalfPlaneBoundary] using hi

/-- Reflection across the boundary line is an involution. -/
@[simp] theorem reflectAcrossHalfPlaneBoundary_involutive (p : Moise.Plane) :
    reflectAcrossHalfPlaneBoundary (reflectAcrossHalfPlaneBoundary p) = p := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [reflectAcrossHalfPlaneBoundary]

/-- Folding fixes points on the nonnegative side of the boundary line. -/
theorem foldPlaneToHalfSpace_val_of_nonneg (p : Moise.Plane) (hp : 0 ≤ p 0) :
    (foldPlaneToHalfSpace p).1 = p := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [foldPlaneToHalfSpace, abs_of_nonneg hp]

/-- Folding a point on the negative side agrees with reflection. -/
theorem foldPlaneToHalfSpace_val_of_neg (p : Moise.Plane) (hp : p 0 < 0) :
    (foldPlaneToHalfSpace p).1 = reflectAcrossHalfPlaneBoundary p := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [foldPlaneToHalfSpace, reflectAcrossHalfPlaneBoundary, abs_of_neg hp]

/-- Reflection across the boundary line preserves the Euclidean norm. -/
theorem norm_reflectAcrossHalfPlaneBoundary (p : Moise.Plane) :
    ‖reflectAcrossHalfPlaneBoundary p‖ = ‖p‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;> simp [reflectAcrossHalfPlaneBoundary]

/-- Folding onto the half-plane preserves the Euclidean norm. -/
theorem norm_foldPlaneToHalfSpace (p : Moise.Plane) :
    ‖(foldPlaneToHalfSpace p).1‖ = ‖p‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;> simp [foldPlaneToHalfSpace]

/-- Relative invariance of domain for the Euclidean half-plane.

An embedding of an open subset of the half-plane has open image provided it carries the
boundary line exactly to the boundary line.  The boundary hypothesis is necessary: without it,
an embedding may bend a boundary arc into the interior.  The proof doubles the source and map
across the boundary line, applies planar invariance of domain, and then restricts the resulting
open image back to the half-plane. -/
theorem isOpen_range_halfSpace_of_isOpen_of_isEmbedding_of_boundary
    {U : Set (EuclideanHalfSpace 2)} (hU : IsOpen U)
    (f : U → EuclideanHalfSpace 2)
    (hf : _root_.Topology.IsEmbedding f)
    (hboundary : ∀ x : U, (f x).1 0 = 0 ↔ x.1.1 0 = 0) :
    IsOpen (Set.range f) := by
  let D : Set Moise.Plane := foldPlaneToHalfSpace ⁻¹' U
  have hfoldContinuous := continuous_foldPlaneToHalfSpace
  have hreflectContinuous := continuous_reflectAcrossHalfPlaneBoundary
  have hreflectInj := injective_reflectAcrossHalfPlaneBoundary
  have hfold_nonneg := foldPlaneToHalfSpace_val_of_nonneg
  have hfold_neg := foldPlaneToHalfSpace_val_of_neg
  have hDopen : IsOpen D := hU.preimage hfoldContinuous
  let toU : D → U := fun p => ⟨foldPlaneToHalfSpace p.1, p.2⟩
  have htoU : Continuous toU :=
    Continuous.subtype_mk
      (hfoldContinuous.comp continuous_subtype_val) _
  let base : D → Moise.Plane := fun p => (f (toU p)).1
  have hbase : Continuous base :=
    continuous_subtype_val.comp (hf.continuous.comp htoU)
  let doubled : D → Moise.Plane := fun p =>
    if 0 ≤ p.1 0 then base p else reflectAcrossHalfPlaneBoundary (base p)
  have hdoubledContinuous : Continuous doubled := by
    dsimp only [doubled]
    apply Continuous.if_le
    · exact hbase
    · exact hreflectContinuous.comp hbase
    · exact continuous_const
    · exact
        (PiLp.continuous_apply (p := 2)
          (β := fun _ : Fin 2 => ℝ) 0).comp continuous_subtype_val
    · intro p hp
      have hinput : (toU p).1.1 0 = 0 := by
        simp [toU, foldPlaneToHalfSpace, hp]
      have houtput : base p 0 = 0 := by
        exact (hboundary (toU p)).mpr hinput
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [reflectAcrossHalfPlaneBoundary, houtput]
  have hdoubledInj : Function.Injective doubled := by
    intro p q hpq
    by_cases hp : 0 ≤ p.1 0
    · by_cases hq : 0 ≤ q.1 0
      · have hb : base p = base q := by
          simpa only [doubled, ite_eq_left hp, ite_eq_left hq] using hpq
        have hfu : f (toU p) = f (toU q) := Subtype.ext hb
        have hu : toU p = toU q := hf.injective hfu
        have hfold :
            (foldPlaneToHalfSpace p.1).1 = (foldPlaneToHalfSpace q.1).1 :=
          congrArg (fun z : U => z.1.1) hu
        rw [hfold_nonneg p.1 hp, hfold_nonneg q.1 hq] at hfold
        exact Subtype.ext hfold
      · have hqneg : q.1 0 < 0 := lt_of_not_ge hq
        have hb :
            base p = reflectAcrossHalfPlaneBoundary (base q) := by
          simpa only [doubled, ite_eq_left hp, ite_eq_right hq] using hpq
        have hcoord := congrArg (fun z : Moise.Plane => z 0) hb
        have hpbase : 0 ≤ base p 0 := (f (toU p)).2
        have hqbase : 0 ≤ base q 0 := (f (toU q)).2
        have hqzero : base q 0 = 0 := by
          simp [reflectAcrossHalfPlaneBoundary] at hcoord
          linarith
        have hinput : (toU q).1.1 0 = 0 :=
          (hboundary (toU q)).mp hqzero
        have habs : |q.1 0| = 0 := by
          simpa [toU, foldPlaneToHalfSpace] using hinput
        exact False.elim (by
          have : q.1 0 = 0 := abs_eq_zero.mp habs
          linarith)
    · have hpneg : p.1 0 < 0 := lt_of_not_ge hp
      by_cases hq : 0 ≤ q.1 0
      · have hb :
            reflectAcrossHalfPlaneBoundary (base p) = base q := by
          simpa only [doubled, ite_eq_right hp, ite_eq_left hq] using hpq
        have hcoord := congrArg (fun z : Moise.Plane => z 0) hb
        have hpbase : 0 ≤ base p 0 := (f (toU p)).2
        have hqbase : 0 ≤ base q 0 := (f (toU q)).2
        have hpzero : base p 0 = 0 := by
          simp [reflectAcrossHalfPlaneBoundary] at hcoord
          linarith
        have hinput : (toU p).1.1 0 = 0 :=
          (hboundary (toU p)).mp hpzero
        have habs : |p.1 0| = 0 := by
          simpa [toU, foldPlaneToHalfSpace] using hinput
        exact False.elim (by
          have : p.1 0 = 0 := abs_eq_zero.mp habs
          linarith)
      · have hqneg : q.1 0 < 0 := lt_of_not_ge hq
        have hr :
            reflectAcrossHalfPlaneBoundary (base p) =
              reflectAcrossHalfPlaneBoundary (base q) := by
          simpa only [doubled, ite_eq_right hp, ite_eq_right hq] using hpq
        have hb : base p = base q := hreflectInj hr
        have hfu : f (toU p) = f (toU q) := Subtype.ext hb
        have hu : toU p = toU q := hf.injective hfu
        have hfold :
            (foldPlaneToHalfSpace p.1).1 = (foldPlaneToHalfSpace q.1).1 :=
          congrArg (fun z : U => z.1.1) hu
        rw [hfold_neg p.1 hpneg, hfold_neg q.1 hqneg] at hfold
        exact Subtype.ext (hreflectInj hfold)
  have hdoubledOpen : IsOpen (Set.range doubled) :=
    isOpen_range_of_isOpen_of_continuous_injective
      (modelWithCornersSelf ℝ Moise.Plane) hDopen doubled
        hdoubledContinuous hdoubledInj
  have hrange :
      Set.range f = Subtype.val ⁻¹' Set.range doubled := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      let p : D := ⟨x.1.1, by
        change foldPlaneToHalfSpace x.1.1 ∈ U
        have hval : (foldPlaneToHalfSpace x.1.1).1 = x.1.1 :=
          hfold_nonneg x.1.1 x.1.2
        have heq : foldPlaneToHalfSpace x.1.1 = x.1 :=
          EuclideanHalfSpace.ext _ _ hval
        simpa only [heq] using x.2⟩
      refine ⟨p, ?_⟩
      have hp : 0 ≤ p.1 0 := x.1.2
      simp only [doubled, ite_eq_left hp, base]
      rw [show toU p = x by
        apply Subtype.ext
        exact Subtype.ext (hfold_nonneg x.1.1 x.1.2)]
      exact congrArg Subtype.val hx
    · rintro ⟨p, hp⟩
      by_cases hsign : 0 ≤ p.1 0
      · refine ⟨toU p, ?_⟩
        have : base p = z.1 := by
          simpa only [doubled, ite_eq_left hsign] using hp
        exact Subtype.ext this
      · have hpneg : p.1 0 < 0 := lt_of_not_ge hsign
        have hreflect :
            reflectAcrossHalfPlaneBoundary (base p) = z.1 := by
          simpa only [doubled, ite_eq_right hsign] using hp
        have hcoord := congrArg (fun w : Moise.Plane => w 0) hreflect
        have hbaseNonneg : 0 ≤ base p 0 := (f (toU p)).2
        have hzNonneg : 0 ≤ z.1 0 := z.2
        have hbaseZero : base p 0 = 0 := by
          simp [reflectAcrossHalfPlaneBoundary] at hcoord
          linarith
        have hinputZero : (toU p).1.1 0 = 0 :=
          (hboundary (toU p)).mp hbaseZero
        have habs : |p.1 0| = 0 := by
          simpa [toU, foldPlaneToHalfSpace] using hinputZero
        exfalso
        have : p.1 0 = 0 := abs_eq_zero.mp habs
        linarith
  rw [hrange]
  exact hdoubledOpen.preimage continuous_subtype_val

/-- A boundary-preserving re-embedding of a fixed source carries every old interior sheet to
an interior sheet of its new half-plane image.

Unlike pointwise physical coverage, this statement compares corresponding source points.  It
is the local relative-invariance-of-domain input used when two polyhedral pieces are identified
along a boundary-preserving seam. -/
theorem mem_interior_range_halfSpace_of_isEmbedding_of_boundary
    {X : Type*} [TopologicalSpace X]
    {f g : X → EuclideanHalfSpace 2}
    (hf : _root_.Topology.IsEmbedding f)
    (hg : _root_.Topology.IsEmbedding g)
    (hboundary : ∀ x : X, (g x).1 0 = 0 ↔ (f x).1 0 = 0)
    {x : X} (hx : f x ∈ interior (Set.range f)) :
    g x ∈ interior (Set.range g) := by
  let U : Set (EuclideanHalfSpace 2) := interior (Set.range f)
  let intoOldRange : U → Set.range f :=
    Set.inclusion interior_subset
  let source : U → X :=
    hf.toHomeomorph.symm ∘ intoOldRange
  have hsourceEmbedding : _root_.Topology.IsEmbedding source := by
    exact hf.toHomeomorph.symm.isEmbedding.comp
      (_root_.Topology.IsEmbedding.inclusion interior_subset)
  let localMap : U → EuclideanHalfSpace 2 := g ∘ source
  have hlocalEmbedding : _root_.Topology.IsEmbedding localMap :=
    hg.comp hsourceEmbedding
  have hlocalBoundary :
      ∀ z : U, (localMap z).1 0 = 0 ↔ z.1.1 0 = 0 := by
    intro z
    have hsourceValue : f (source z) = z.1 := by
      exact congrArg Subtype.val
        (hf.toHomeomorph.apply_symm_apply (intoOldRange z))
    rw [show localMap z = g (source z) by rfl,
      hboundary (source z), hsourceValue]
  have hlocalOpen : IsOpen (Set.range localMap) :=
    isOpen_range_halfSpace_of_isOpen_of_isEmbedding_of_boundary
      isOpen_interior localMap hlocalEmbedding hlocalBoundary
  let z : U := ⟨f x, hx⟩
  have hsourceZ : source z = x := by
    apply hf.injective
    exact congrArg Subtype.val
      (hf.toHomeomorph.apply_symm_apply (intoOldRange z))
  have hmemLocal : g x ∈ Set.range localMap := by
    refine ⟨z, ?_⟩
    change g (source z) = g x
    rw [hsourceZ]
  have hmemInteriorLocal : g x ∈ interior (Set.range localMap) := by
    rwa [hlocalOpen.interior_eq]
  apply interior_mono ?_ hmemInteriorLocal
  rintro y ⟨u, rfl⟩
  exact ⟨source u, rfl⟩

end ClassificationOfSurfaces
end Topology
end LeanEval
