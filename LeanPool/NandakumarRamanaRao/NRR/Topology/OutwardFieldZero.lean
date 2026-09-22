/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.DegreePositiveIntegration
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SphereOrientationPosFromMV
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.BallBoundaryLES
/-!
# A zero theorem for outward-pointing Euclidean vector fields

This is the finite-dimensional topological input used by the equal-area power-weight
existence proof.  A continuous vector field on Euclidean space that points strictly
outward along the unit sphere must vanish in the closed unit ball.

The proof uses the project's unconditional integral degree of positive-dimensional
spheres.  Under the contrary assumption, radial normalization gives a map from the
closed ball to its boundary.  Its restriction to the boundary is both nullhomotopic
(because it extends over the contractible ball) and homotopic to the identity (by the
strictly outward scalar-product condition), contradicting degree.
-/

noncomputable section

open Metric RealInnerProductSpace

namespace NRR
namespace Topology

open SphereOddDegree

variable {d : Nat}

private abbrev Ambient (d : Nat) := EuclideanSpace Real (Fin (d + 1))

/-- Radial normalization of a nonzero vector. -/
private def radialNormalize {d : Nat} (x : Ambient d) (hx : x ≠ 0) : Sphere d :=
  ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx]⟩

private lemma radialNormalize_val {d : Nat} (x : Ambient d) (hx : x ≠ 0) :
    (radialNormalize x hx : Ambient d) = ‖x‖⁻¹ • x := rfl

/-- Continuous radial normalization of a continuous nowhere-zero vector-valued map. -/
private noncomputable def radialNormalizeMap
    {X : Type*} [TopologicalSpace X] {d : Nat}
    (G : X → Ambient d) (hG : Continuous G) (hne : ∀ x, G x ≠ 0) :
    C(X, Sphere d) :=
  ⟨fun x => radialNormalize (G x) (hne x), by
    exact Continuous.subtype_mk
      (((continuous_norm.comp hG).inv₀
        (fun x => norm_ne_zero_iff.mpr (hne x))).smul hG) _⟩

/-- A continuous vector field that is strictly outward on the unit sphere has a zero
in the closed unit ball.  The positive-dimensional assumption is exactly what is
needed by the integral sphere-degree API. -/
theorem exists_zero_closedBall_of_inner_pos_on_sphere
    (hd : 1 ≤ d)
    (F : Ambient d → Ambient d)
    (hF : Continuous F)
    (hout : ∀ x : Ambient d, ‖x‖ = 1 → 0 < inner Real x (F x)) :
    ∃ x : Ambient d, x ∈ closedBall 0 1 ∧ F x = 0 := by
  by_contra hzero
  push Not at hzero
  have hFne : ∀ x : SphereOddDegree.Disk d, F x.1 ≠ 0 := by
    intro x hx
    exact hzero x.1 x.2 hx
  let r : C(SphereOddDegree.Disk d, Sphere d) :=
    radialNormalizeMap (fun x => F x.1)
      (hF.comp continuous_subtype_val) hFne
  let incl : C(Sphere d, SphereOddDegree.Disk d) :=
    ⟨fun x => ⟨x.1, by
        have hxnorm : ‖(x.1 : Ambient d)‖ = 1 := by
          simp
        simp⟩,
      Continuous.subtype_mk continuous_subtype_val (by
        intro x
        have hxnorm : ‖(x.1 : Ambient d)‖ = 1 := by
          simp
        simp)⟩
  let boundaryMap : C(Sphere d, Sphere d) := r.comp incl
  obtain ⟨yDisk, hyDisk⟩ :
      ∃ y : SphereOddDegree.Disk d,
        ContinuousMap.Homotopic (ContinuousMap.id (SphereOddDegree.Disk d))
          (ContinuousMap.const (SphereOddDegree.Disk d) y) := by
    exact id_nullhomotopic (SphereOddDegree.Disk d)
  have hincl_null : ContinuousMap.Homotopic incl
      (ContinuousMap.const (Sphere d) yDisk) := by
    simpa using hyDisk.comp (ContinuousMap.Homotopic.refl incl)
  have hboundary_null : ContinuousMap.Homotopic boundaryMap
      (ContinuousMap.const (Sphere d) (r yDisk)) := by
    simpa [boundaryMap] using (ContinuousMap.Homotopic.refl r).comp hincl_null
  have hboundary_id : ContinuousMap.Homotopic boundaryMap
      (ContinuousMap.id (Sphere d)) := by
    have hcomb_ne : ∀ p : unitInterval × Sphere d,
        (1 - (p.1 : Real)) • F p.2.1 + (p.1 : Real) • p.2.1 ≠ 0 := by
      intro p hEq
      have ht1 : (p.1 : Real) ≤ 1 := p.1.2.2
      have hp_norm : ‖(p.2.1 : Ambient d)‖ = 1 := by
        simp
      have hout' : 0 < inner Real p.2.1 (F p.2.1) := hout p.2.1 hp_norm
      have hinner : 0 < inner Real p.2.1
          ((1 - (p.1 : Real)) • F p.2.1 + (p.1 : Real) • p.2.1) := by
        rw [inner_add_right, inner_smul_right, inner_smul_right,
          real_inner_self_eq_norm_sq, hp_norm]
        norm_num
        have ht0 : 0 ≤ (p.1 : Real) := p.1.2.1
        by_cases ht : (p.1 : Real) = 1
        · rw [ht]
          norm_num
        · have hlt : (p.1 : Real) < 1 := lt_of_le_of_ne ht1 ht
          nlinarith
      rw [hEq, inner_zero_right] at hinner
      exact lt_irrefl 0 hinner
    let V : unitInterval × Sphere d → Ambient d := fun p =>
      (1 - (p.1 : Real)) • F p.2.1 + (p.1 : Real) • p.2.1
    have hV : Continuous V := by
      fun_prop
    let Hmap : C(unitInterval × Sphere d, Sphere d) :=
      radialNormalizeMap V hV hcomb_ne
    refine ⟨⟨Hmap, ?_, ?_⟩⟩
    · intro x
      apply Subtype.ext
      simp [Hmap, V, radialNormalizeMap, boundaryMap, incl, r,
        radialNormalize]
    · intro x
      apply Subtype.ext
      simp [Hmap, V, radialNormalizeMap, radialNormalize]
  let o : SphereOrientationPos := sphereOrientationPosUnconditional
  have hdeg_id : degreePos o hd boundaryMap = 1 := by
    rw [degreePos_homotopy o hd hboundary_id]
    exact degreePos_id o hd
  have hdeg_zero : degreePos o hd boundaryMap = 0 := by
    rw [degreePos_homotopy o hd hboundary_null]
    exact degreePos_const o hd _
  omega

end Topology
end NRR
