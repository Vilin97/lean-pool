/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.PlaneComplex
import Mathlib.Topology.Piecewise

/-!
# Extending a homeomorphism of a closed planar patch

Moise's elementary free-triangle move is first constructed on a finite polygonal patch.  Since
the move fixes the patch frontier, it extends to an ambient homeomorphism by the identity.  This
file proves that pasting step independently of the particular triangulated patch.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Changing only the proof that a point belongs to an equal set does not change the point. -/
theorem coe_setCongr_apply {X : Type*} [TopologicalSpace X] {s t : Set X}
    (h : s = t) (z : s) : ((Homeomorph.setCongr h z : t) : X) = z := by
  subst t
  rfl

namespace TriangleMesh

variable (M : TriangleMesh)

/-- Repositioning a fixed abstract triangle mesh gives a canonical homeomorphism between the old
and new geometric supports, obtained by preserving barycentric coordinates. -/
noncomputable def repositionHomeomorph (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex))) :
    M.toPlaneComplex.support ≃ₜ
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.support :=
  (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm.trans
    ((M.reposition position' hposition_injective haffineIndependent
      htriangle_inter).toPlaneComplex.realizationHomeomorph
        (M.reposition position' hposition_injective haffineIndependent
          htriangle_inter).toPlaneComplex_isPure2)

@[simp] theorem repositionHomeomorph_apply_realization (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (x : GeometricRealization M.toPlaneComplex.Vertex M.toPlaneComplex.cells) :
    M.repositionHomeomorph position' hposition_injective haffineIndependent htriangle_inter
        (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2 x) =
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.realizationHomeomorph
          (M.reposition position' hposition_injective haffineIndependent
            htriangle_inter).toPlaneComplex_isPure2 x := by
  unfold repositionHomeomorph Homeomorph.trans Equiv.trans Function.comp
  simp
  rfl

theorem coe_repositionHomeomorph_apply_realization (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (x : GeometricRealization M.toPlaneComplex.Vertex M.toPlaneComplex.cells) :
    (M.repositionHomeomorph position' hposition_injective haffineIndependent htriangle_inter
        (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2 x) : Plane) =
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.baryEval x.1 := by
  exact congrArg Subtype.val (M.repositionHomeomorph_apply_realization position'
    hposition_injective haffineIndependent htriangle_inter x)

theorem coe_repositionHomeomorph_apply (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (z : M.toPlaneComplex.support) :
    (M.repositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter z : Plane) =
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.baryEval
          ((M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm z).1 := by
  let x := (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm z
  have hz : z = M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2 x := by
    exact
      (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).apply_symm_apply z |>.symm
  change (M.repositionHomeomorph position' hposition_injective haffineIndependent
      htriangle_inter z : Plane) =
    (M.reposition position' hposition_injective haffineIndependent
      htriangle_inter).toPlaneComplex.baryEval x.1
  rw [hz, repositionHomeomorph_apply_realization]
  rfl

theorem coe_repositionHomeomorph_trans_setCongr_apply
    (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.support = M.toPlaneComplex.support)
    (z : M.toPlaneComplex.support) :
    (((M.repositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter).trans (Homeomorph.setCongr hsupport)) z : Plane) =
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.baryEval
          ((M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm z).1 := by
  exact M.coe_repositionHomeomorph_apply position' hposition_injective haffineIndependent
    htriangle_inter z

end TriangleMesh

/-- Extend a homeomorphism of a closed planar patch by the identity outside the patch. -/
noncomputable def extendHomeomorphByIdentity {P : Set Plane} (hP : IsClosed P)
    (e : P ≃ₜ P)
    (hfrontier : ∀ x (hx : x ∈ frontier P), (e ⟨x, hP.frontier_subset hx⟩).1 = x) :
    Plane ≃ₜ Plane := by
  classical
  let f : Plane → Plane := fun x => if hx : x ∈ P then (e ⟨x, hx⟩).1 else x
  let g : Plane → Plane := fun x => if hx : x ∈ P then (e.symm ⟨x, hx⟩).1 else x
  have hgf : Function.LeftInverse g f := by
    intro x
    by_cases hx : x ∈ P
    · simp [f, g, hx]
    · simp [f, g, hx]
  have hfg : Function.RightInverse g f := by
    intro x
    by_cases hx : x ∈ P
    · simp [f, g, hx]
    · simp [f, g, hx]
  have hfrontierSymm :
      ∀ x (hx : x ∈ frontier P), (e.symm ⟨x, hP.frontier_subset hx⟩).1 = x := by
    intro x hx
    have he : e ⟨x, hP.frontier_subset hx⟩ = ⟨x, hP.frontier_subset hx⟩ := by
      apply Subtype.ext
      exact hfrontier x hx
    have := congrArg Subtype.val (e.symm_apply_eq.mpr he.symm)
    exact this
  have hfContinuousOn : ContinuousOn f P := by
    rw [continuousOn_iff_continuous_restrict]
    have hcont : Continuous fun x : P => (e x).1 :=
      continuous_subtype_val.comp e.continuous
    convert hcont using 1
    funext x
    simp [Set.restrict, f, x.property]
  have hgContinuousOn : ContinuousOn g P := by
    rw [continuousOn_iff_continuous_restrict]
    have hcont : Continuous fun x : P => (e.symm x).1 :=
      continuous_subtype_val.comp e.symm.continuous
    convert hcont using 1
    funext x
    simp [Set.restrict, g, x.property]
  have hfContinuous : Continuous f := by
    have hpaste : Set.piecewise P f id = f := by
      funext x
      by_cases hx : x ∈ P <;> simp [Set.piecewise, f, hx]
    rw [← hpaste]
    apply continuous_piecewise
    · intro x hx
      have hxP := hP.frontier_subset hx
      simp [f, hxP, hfrontier x hx]
    · simpa [hP.closure_eq] using hfContinuousOn
    · exact continuous_id.continuousOn
  have hgContinuous : Continuous g := by
    have hpaste : Set.piecewise P g id = g := by
      funext x
      by_cases hx : x ∈ P <;> simp [Set.piecewise, g, hx]
    rw [← hpaste]
    apply continuous_piecewise
    · intro x hx
      have hxP := hP.frontier_subset hx
      simp [g, hxP, hfrontierSymm x hx]
    · simpa [hP.closure_eq] using hgContinuousOn
    · exact continuous_id.continuousOn
  exact
    { toEquiv := Equiv.mk f g hgf hfg
      continuous_toFun := hfContinuous
      continuous_invFun := hgContinuous }

theorem extendHomeomorphByIdentity_apply_mem {P : Set Plane} (hP : IsClosed P)
    (e : P ≃ₜ P)
    (hfrontier : ∀ x (hx : x ∈ frontier P), (e ⟨x, hP.frontier_subset hx⟩).1 = x)
    {x : Plane} (hx : x ∈ P) :
    extendHomeomorphByIdentity hP e hfrontier x = (e ⟨x, hx⟩).1 := by
  classical
  simp [extendHomeomorphByIdentity, hx]

theorem extendHomeomorphByIdentity_apply_not_mem {P : Set Plane} (hP : IsClosed P)
    (e : P ≃ₜ P)
    (hfrontier : ∀ x (hx : x ∈ frontier P), (e ⟨x, hP.frontier_subset hx⟩).1 = x)
    {x : Plane} (hx : x ∉ P) :
    extendHomeomorphByIdentity hP e hfrontier x = x := by
  classical
  simp [extendHomeomorphByIdentity, hx]

namespace TriangleMesh

variable (M : TriangleMesh)

/-- A repositioning with unchanged support and fixed support frontier extends to an ambient plane
homeomorphism. -/
noncomputable def ambientRepositionHomeomorph (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.support = M.toPlaneComplex.support)
    (hfrontier : ∀ x (hx : x ∈ frontier M.toPlaneComplex.support),
      (((M.repositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter).trans (Homeomorph.setCongr hsupport))
          ⟨x, M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hx⟩).1 = x) :
    Plane ≃ₜ Plane :=
  extendHomeomorphByIdentity M.toPlaneComplex.isCompact_support.isClosed
    ((M.repositionHomeomorph position' hposition_injective haffineIndependent
      htriangle_inter).trans (Homeomorph.setCongr hsupport)) hfrontier

theorem ambientRepositionHomeomorph_eqOn_compl (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.support = M.toPlaneComplex.support)
    (hfrontier : ∀ x (hx : x ∈ frontier M.toPlaneComplex.support),
      (((M.repositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter).trans (Homeomorph.setCongr hsupport))
          ⟨x, M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hx⟩).1 = x) :
    Set.EqOn
      (M.ambientRepositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter hsupport hfrontier)
      id M.toPlaneComplex.supportᶜ := by
  intro x hx
  exact extendHomeomorphByIdentity_apply_not_mem _ _ _ hx

end TriangleMesh

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
