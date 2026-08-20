/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.AdaptiveTriangulation

/-!
# Adaptive triangulations subordinate to an open cover

The adaptive fan construction only needs a hereditary, locally attainable notion of a safe
midpoint face.  This file instantiates that interface with containment in one member of an open
cover.  In particular, the resulting locally finite triangulation has every closed triangle in
one prescribed control neighborhood.  Quantitative chart approximation can therefore choose
the neighborhoods first and reuse the conforming triangulation unchanged.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)

/-- An open cover of `U` by subsets which remain inside `U`. -/
structure AdaptiveOpenCover where
  /-- The `Index` declaration. -/
  Index : Type
  /-- The `set` declaration. -/
  set : Index → Set K.realization
  isOpen : ∀ i, IsOpen (set i)
  subset : ∀ i, set i ⊆ U
  covers : ∀ {p : K.realization}, p ∈ U → ∃ i, p ∈ set i

namespace AdaptiveOpenCover

variable (C : K.AdaptiveOpenCover U)

/-- A level face is cover-safe when its complete carrier lies in one cover member. -/
@[reducible]
def safety : K.AdaptiveSafety U where
  safe t := ∃ i, K.levelFaceCarrier t ⊆ C.set i
  carrier_subset := by
    rintro n t ⟨i, hi⟩
    exact hi.trans (C.subset i)
  hereditary := by
    rintro n m s t hts ⟨i, hi⟩
    exact ⟨i, hts.trans hi⟩

/-- Subordination to an open cover is locally attainable under repeated midpoint subdivision. -/
theorem safety_isAdmissible :
    @AdaptiveSafety.IsAdmissible K U C.safety := by
  letI : K.AdaptiveSafety U := C.safety
  refine { exists_safe := ?_, locally_parent_safe := ?_ }
  · intro _ p hp
    obtain ⟨i, hpi⟩ := C.covers hp
    letI : K.AdaptiveSafety (C.set i) := K.defaultAdaptiveSafety (C.set i)
    letI : AdaptiveSafety.IsAdmissible (K := K) (U := C.set i) :=
      K.defaultAdaptiveSafety_admissible (C.set i)
    obtain ⟨n, t, ht, hpt⟩ :=
      K.exists_safeLevelFace_containing (C.set i) (C.isOpen i) hpi
    refine ⟨n, t, ⟨i, ?_⟩, hpt⟩
    exact AdaptiveSafety.carrier_subset (K := K) (U := C.set i) ht
  · intro _ p
    obtain ⟨i, hpi⟩ := C.covers p.2
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (C.isOpen i) p.1 hpi
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε2
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨ε, hε, N, ?_⟩
    intro n hNn t hinter
    refine ⟨i, ?_⟩
    obtain ⟨z, hzFace, hzBall⟩ := hinter
    have hzParent : z ∈ K.levelFaceCarrier (K.levelParentFace n t) :=
      K.levelFaceCarrier_subset_parent n t hzFace
    have hpow : (1 / 2 : ℝ) ^ n < ε / 2 :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hNn).trans_lt hN
    intro y hy
    apply hball
    rw [Metric.mem_ball]
    calc
      dist y p.1 ≤ dist y z + dist z p.1 := dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) ^ n + dist z p.1 := by
        gcongr
        exact K.dist_le_pow_of_mem_levelFaceCarrier
          (K.levelParentFace n t) hy hzParent
      _ < ε / 2 + ε / 2 := add_lt_add hpow hzBall
      _ = ε := by ring

/-- The conforming adaptive triangle complex subordinate to `C`. -/
noncomputable abbrev locallyFiniteTriangleComplex (hU : IsOpen U) :
    LocallyFiniteTriangleComplex U := by
  letI : K.AdaptiveSafety U := C.safety
  letI : AdaptiveSafety.IsAdmissible (K := K) (U := U) := C.safety_isAdmissible
  exact K.adaptiveLocallyFiniteTriangleComplex U hU

/-- The cover-subordinate adaptive complex covers all of `U`. -/
theorem locallyFiniteTriangleComplex_support (hU : IsOpen U) :
    (locallyFiniteTriangleComplex K U C hU).support = Set.univ := by
  letI : K.AdaptiveSafety U := C.safety
  letI : AdaptiveSafety.IsAdmissible (K := K) (U := U) := C.safety_isAdmissible
  exact K.adaptiveLocallyFiniteTriangleComplex_support U hU

/-- Distinct faces of the cover-subordinate adaptive complex carry distinct vertex triples. -/
theorem faceVertices_injective (hU : IsOpen U) :
    Function.Injective (locallyFiniteTriangleComplex K U C hU).faceVertices := by
  letI : K.AdaptiveSafety U := C.safety
  letI : AdaptiveSafety.IsAdmissible (K := K) (U := U) := C.safety_isAdmissible
  exact K.adaptiveGlobalFanFaceVertices_injective U hU

/-- Every adaptive tile selected by `C` lies in one member of the cover. -/
theorem exists_cover_set_of_adaptiveFace
    (t : @IntrinsicTwoComplex.AdaptiveFace K U C.safety) :
    ∃ i, @IntrinsicTwoComplex.adaptiveFaceCarrier K U C.safety t ⊆ C.set i := by
  letI : K.AdaptiveSafety U := C.safety
  rcases t with ⟨(_ | n), t⟩
  · exact t.2
  · exact t.2.1

/-- Every closed triangle of the conforming fan triangulation lies in one cover member. -/
theorem exists_cover_set_of_complex_face (hU : IsOpen U)
    (f : (locallyFiniteTriangleComplex K U C hU).Face) :
    ∃ i, Subtype.val ''
        ((locallyFiniteTriangleComplex K U C hU).faceCarrier f) ⊆ C.set i := by
  letI : K.AdaptiveSafety U := C.safety
  letI : AdaptiveSafety.IsAdmissible (K := K) (U := U) := C.safety_isAdmissible
  obtain ⟨i, hi⟩ := exists_cover_set_of_adaptiveFace K U C f.1
  refine ⟨i, ?_⟩
  rintro p ⟨q, hq, rfl⟩
  change q ∈ Set.range (K.adaptiveGlobalFanFaceMap U hU f) at hq
  rw [K.range_adaptiveGlobalFanFaceMap U hU] at hq
  exact hi (K.range_adaptiveFanFaceMap_subset_tile U hU f hq)

end AdaptiveOpenCover
end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
