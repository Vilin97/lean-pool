/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicGraphModel

/-!
# Arbitrarily close intrinsic graph approximation

The first simultaneous intrinsic graph replacement polygonalizes the abstract one-skeleton but
does not, by itself, give arbitrary pointwise control along a large edge.  Its conforming plane
model turns that replacement into an ordinary finite plane graph.  Transferring the original
embedding to this model and applying the plane graph approximation theorem gives the required
arbitrarily close second replacement.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}

/-- The original intrinsic embedding, transferred to the conforming plane graph model.  Values
off the graph support are irrelevant. -/
noncomputable def replacementGraphOriginalMap (p : Plane) : Plane := by
  classical
  let G := K.replacementGraphComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  let e := K.replacementGraphHomeomorph
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  exact if hp : p ∈ G.support then h (e.symm ⟨p, hp⟩).1 else 0

@[simp] theorem replacementGraphOriginalMap_apply
    (p : (K.replacementGraphComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support) :
    K.replacementGraphOriginalMap
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) p.1 =
      h ((K.replacementGraphHomeomorph
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).symm p).1 := by
  simp [replacementGraphOriginalMap, p.2]

theorem continuousOn_replacementGraphOriginalMap :
    ContinuousOn
      (K.replacementGraphOriginalMap
        (hcont := hcont) (hinj := hinj) (D := D) (C := C))
      (K.replacementGraphComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support := by
  rw [continuousOn_iff_continuous_restrict]
  let e := K.replacementGraphHomeomorph
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  have hc : Continuous (fun p : (K.replacementGraphComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support ↦
      h (e.symm p).1) :=
    hcont.comp (continuous_subtype_val.comp e.symm.continuous)
  convert hc using 1
  funext p
  exact K.replacementGraphOriginalMap_apply p

theorem replacementGraphOriginalMap_injOn :
    Set.InjOn
      (K.replacementGraphOriginalMap
        (hcont := hcont) (hinj := hinj) (D := D) (C := C))
      (K.replacementGraphComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support := by
  intro p hp q hq hpq
  let e := K.replacementGraphHomeomorph
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  have heq : h (e.symm ⟨p, hp⟩).1 = h (e.symm ⟨q, hq⟩).1 := by
    rw [← K.replacementGraphOriginalMap_apply ⟨p, hp⟩,
      ← K.replacementGraphOriginalMap_apply ⟨q, hq⟩]
    exact hpq
  have hsource : (e.symm ⟨p, hp⟩).1 = (e.symm ⟨q, hq⟩).1 := hinj heq
  have hsubtype : e.symm ⟨p, hp⟩ = e.symm ⟨q, hq⟩ := Subtype.ext hsource
  exact congrArg Subtype.val (e.symm.injective hsubtype)

/-- Certified output of the intrinsic one-skeleton approximation.  `planeMap` acts on the first
polygonal graph model; composing it with `graphReplacementMap` is the final intrinsic graph
embedding. -/
structure CloseGraphApproximation (ε : ℝ) where
  /-- The `planeMap` declaration. -/
  planeMap : Plane → Plane
  isPLOnModel : IsPLOn
    (K.replacementGraphComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) planeMap
  injOnModel : Set.InjOn planeMap
    (K.replacementGraphComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support
  close : ∀ x ∈ K.oneSkeleton,
    dist (planeMap (K.graphReplacementMap hcont hinj D C x)) (h x) < ε
  facewisePL : ∀ t : K.Face,
    IsPLOnSet
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier planeMap

namespace CloseGraphApproximation

/-- The final graph map on the intrinsic realization. -/
noncomputable def intrinsicMap {ε : ℝ} (A : K.CloseGraphApproximation
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) ε) :
    K.realization → Plane :=
  A.planeMap ∘ K.graphReplacementMap hcont hinj D C

theorem continuousOn_intrinsicMap {ε : ℝ} (A : K.CloseGraphApproximation
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) ε) :
    ContinuousOn A.intrinsicMap K.oneSkeleton := by
  apply A.isPLOnModel.continuousOn.comp
    (K.continuousOn_graphReplacementMap_oneSkeleton hcont hinj D C)
  intro x hx
  rw [K.replacementGraphComplex_support_eq_image]
  exact ⟨x, hx, rfl⟩

theorem injOn_intrinsicMap {ε : ℝ} (A : K.CloseGraphApproximation
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) ε) :
    Set.InjOn A.intrinsicMap K.oneSkeleton := by
  intro x hx y hy hxy
  apply K.graphReplacementMap_injectiveOn_oneSkeleton hcont hinj D C hx hy
  apply A.injOnModel
  · rw [K.replacementGraphComplex_support_eq_image]
    exact ⟨x, hx, rfl⟩
  · rw [K.replacementGraphComplex_support_eq_image]
    exact ⟨y, hy, rfl⟩
  · exact hxy

end CloseGraphApproximation

/-- Moise Ch. 6, Thm. 2 for an intrinsic finite one-skeleton: after one auxiliary
polygonalization, the graph admits an arbitrarily close PL embedding, simultaneously PL on all
three-edge face cycles. -/
theorem exists_closeGraphApproximation {ε : ℝ} (hε : 0 < ε) :
    Nonempty (K.CloseGraphApproximation
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) ε) := by
  let G := K.replacementGraphComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  let q := K.replacementGraphOriginalMap
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  obtain ⟨f, hpl, hfinj, -, hfclose, -, hfacewise⟩ :=
    G.exists_graph_PL_approximation_facewise
      (K.replacementGraphBaseComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).oneSkeleton_isGraph
      K.continuousOn_replacementGraphOriginalMap
      K.replacementGraphOriginalMap_injOn hε
  refine ⟨{
    planeMap := f
    isPLOnModel := hpl
    injOnModel := hfinj
    close := ?_
    facewisePL := ?_ }⟩
  · intro x hx
    let z : K.oneSkeleton := ⟨x, hx⟩
    let e := K.replacementGraphHomeomorph
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)
    have heVal : (e z).1 = K.graphReplacementMap hcont hinj D C x := by
      exact K.replacementGraphHomeomorph_coe z
    have hclose := hfclose (e z).1 (e z).2
    have hq : K.replacementGraphOriginalMap
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) (e z).1 = h x := by
      rw [K.replacementGraphOriginalMap_apply (e z), e.symm_apply_apply]
    rw [hq] at hclose
    rw [heVal] at hclose
    exact hclose
  · intro t
    exact hfacewise _ (K.facePolygonalCircle_locallyCoveredBy_replacementGraphComplex t)

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
