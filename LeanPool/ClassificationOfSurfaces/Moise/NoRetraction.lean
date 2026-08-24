/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.ConeExtension
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting

/-!
# The disk has no retraction onto its boundary

This is Moise, Chapter 4, Problem 2 (proved as Theorem 10.10 later in the book).  We use the
covering map `Circle.exp : ℝ → S¹`: a map from the contractible closed disk to the circle
lifts to `ℝ`, whereas its restriction to the boundary cannot be the identity because the
standard boundary loop has lifts whose endpoints differ by `2π`.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open scoped Pointwise unitInterval

/-- The complex closed unit disk, used only as the standard model for the no-retraction
argument. -/
abbrev ClosedUnitDisk := Metric.closedBall (0 : ℂ) 1

/-- The boundary circle included in the closed unit disk. -/
def circleToClosedUnitDisk (z : Circle) : ClosedUnitDisk :=
  ⟨z, by
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Circle.norm_coe]⟩

@[simp] theorem circleToClosedUnitDisk_coe (z : Circle) :
    (circleToClosedUnitDisk z : ℂ) = z :=
  rfl

theorem continuous_circleToClosedUnitDisk : Continuous circleToClosedUnitDisk := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

/-- The closed disk does not retract continuously onto its boundary circle. -/
theorem no_retraction_closedUnitDisk :
    ¬ ∃ r : ClosedUnitDisk → Circle,
      Continuous r ∧ ∀ z : Circle, r (circleToClosedUnitDisk z) = z := by
  rintro ⟨r, hr, hretract⟩
  let : ContractibleSpace ClosedUnitDisk :=
    (convex_closedBall (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩
  let : LocallyPathConnectedSpace ClosedUnitDisk :=
    (convex_closedBall (0 : ℂ) 1).locallyPathConnectedSpace
  let f : C(ClosedUnitDisk, Circle) := ⟨r, hr⟩
  let center : ClosedUnitDisk := ⟨0, by simp⟩
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (f center)
  obtain ⟨F, hF, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f center e₀ he₀
  have hFlifts : Circle.exp ∘ F = f := hF.2
  let γ : C(I, Circle) :=
    ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩
  let Γ : C(I, ℝ) :=
    ⟨fun t => F (circleToClosedUnitDisk (γ t)),
      F.continuous.comp (continuous_circleToClosedUnitDisk.comp γ.continuous)⟩
  let Λ : C(I, ℝ) :=
    ⟨fun t => Γ 0 + 2 * Real.pi * (t : ℝ), by fun_prop⟩
  have hΓlift : Circle.exp ∘ Γ = γ := by
    funext t
    change Circle.exp (F (circleToClosedUnitDisk (γ t))) = γ t
    rw [show Circle.exp (F (circleToClosedUnitDisk (γ t))) =
      f (circleToClosedUnitDisk (γ t)) by exact congrFun hFlifts _]
    exact hretract (γ t)
  have hΛlift : Circle.exp ∘ Λ = γ := by
    funext t
    change Circle.exp (Γ 0 + 2 * Real.pi * (t : ℝ)) =
      Circle.exp (2 * Real.pi * (t : ℝ))
    rw [Circle.exp_add]
    have hΓ0 : Circle.exp (Γ 0) = 1 := by
      have h := congrFun hΓlift 0
      simpa [γ] using h
    rw [hΓ0, one_mul]
  have hΓ0 : Γ 0 = Λ 0 := by simp [Λ]
  have hΓeq : Γ = Circle.isCoveringMap_exp.liftPath γ (Γ 0) (by
      simpa using (congrFun hΓlift 0).symm) :=
    (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
      simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΓlift, rfl⟩
  have hΛeq : Λ = Circle.isCoveringMap_exp.liftPath γ (Γ 0) (by
      simpa using (congrFun hΓlift 0).symm) :=
    (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
      simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΛlift, hΓ0.symm⟩
  have hend : Γ 1 = Λ 1 := by rw [hΓeq, hΛeq]
  have hloop : Γ 1 = Γ 0 := by
    change F (circleToClosedUnitDisk (γ 1)) = F (circleToClosedUnitDisk (γ 0))
    congr 2
    apply Subtype.ext
    simp [γ]
  rw [hloop] at hend
  have hend' : Γ 0 = Γ 0 + 2 * Real.pi := by simp [Λ] at hend
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  apply hpi
  linarith

/-- The Euclidean plane and the complex plane are linearly isometric, using the orthonormal
basis `(1, I)` of `ℂ` over `ℝ`. -/
noncomputable abbrev planeComplexIsometry : Plane ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- A complex unit direction, transported to the Euclidean plane, lies in the plane unit ball. -/
noncomputable def circleToPlaneClosedUnitBall (z : Circle) : Metric.closedBall (0 : Plane) 1 :=
  ⟨planeComplexIsometry.symm z, by
    rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩

/-- A point on the Euclidean unit sphere, transported to `ℂ`, is a point of `Circle`. -/
noncomputable def planeUnitSphereToCircle (x : Metric.sphere (0 : Plane) 1) : Circle :=
  ⟨planeComplexIsometry x, by
    exact show planeComplexIsometry (x : Plane) ∈ Metric.sphere (0 : ℂ) 1 from
      mem_sphere_zero_iff_norm.mpr (by
        rw [LinearIsometryEquiv.norm_map]
        exact mem_sphere_zero_iff_norm.mp x.2)⟩

@[simp] theorem planeUnitSphereToCircle_circleToPlaneClosedUnitBall (z : Circle) :
    planeUnitSphereToCircle
      ⟨(circleToPlaneClosedUnitBall z : Plane), by
        rw [mem_sphere_zero_iff_norm]
        change ‖planeComplexIsometry.symm (z : ℂ)‖ = 1
        rw [LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩ = z := by
  apply Subtype.ext
  exact planeComplexIsometry.apply_symm_apply z

theorem continuous_circleToPlaneClosedUnitBall : Continuous circleToPlaneClosedUnitBall := by
  apply Continuous.subtype_mk
  exact planeComplexIsometry.symm.continuous.comp continuous_subtype_val

theorem continuous_planeUnitSphereToCircle : Continuous planeUnitSphereToCircle := by
  apply Continuous.subtype_mk
  exact planeComplexIsometry.continuous.comp continuous_subtype_val

/-- The linear isometry sends the complex unit disk to the plane unit ball. -/
noncomputable def complexDiskToPlaneClosedUnitBall
    (z : ClosedUnitDisk) : Metric.closedBall (0 : Plane) 1 :=
  ⟨planeComplexIsometry.symm z.1, by
    rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
    simpa [dist_zero_right] using Metric.mem_closedBall.mp z.2⟩

theorem continuous_complexDiskToPlaneClosedUnitBall :
    Continuous complexDiskToPlaneClosedUnitBall := by
  apply Continuous.subtype_mk
  exact planeComplexIsometry.symm.continuous.comp continuous_subtype_val

/-- The closed unit ball in the project's Euclidean plane does not retract onto its sphere. -/
theorem no_retraction_planeClosedUnitBall :
    ¬ ∃ r : Metric.closedBall (0 : Plane) 1 → Metric.sphere (0 : Plane) 1,
      Continuous r ∧
        ∀ z : Metric.sphere (0 : Plane) 1,
          r ⟨z.1, Metric.mem_closedBall.mpr z.2.le⟩ = z := by
  rintro ⟨r, hr, hretract⟩
  apply no_retraction_closedUnitDisk
  let r' : ClosedUnitDisk → Circle := fun z =>
    planeUnitSphereToCircle (r (complexDiskToPlaneClosedUnitBall z))
  refine ⟨r', ?_, ?_⟩
  · exact continuous_planeUnitSphereToCircle.comp
      (hr.comp continuous_complexDiskToPlaneClosedUnitBall)
  · intro z
    let zp : Metric.sphere (0 : Plane) 1 :=
      ⟨planeComplexIsometry.symm z, by
        rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩
    change planeUnitSphereToCircle (r ⟨zp.1, Metric.mem_closedBall.mpr zp.2.le⟩) = z
    rw [hretract zp]
    exact planeUnitSphereToCircle_circleToPlaneClosedUnitBall z

/-- Retractions are invariant under an ambient homeomorphism carrying both the disk and its
boundary to the target disk and boundary. -/
theorem no_retraction_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} {A' B' : Set Y} (e : X ≃ₜ Y)
    (hA : e '' A = A') (hB : e '' B = B') (hBA : B ⊆ A) (hB'A' : B' ⊆ A')
    (hno : ¬ ∃ r : A' → B', Continuous r ∧
      ∀ z : B', r ⟨z.1, hB'A' z.2⟩ = z) :
    ¬ ∃ r : A → B, Continuous r ∧
      ∀ z : B, r ⟨z.1, hBA z.2⟩ = z := by
  rintro ⟨r, hr, hretract⟩
  apply hno
  have hApre : A = e ⁻¹' A' := by
    ext x
    constructor
    · intro hx
      exact hA ▸ ⟨x, hx, rfl⟩
    · intro hx
      have hex : e x ∈ e '' A := hA.symm ▸ hx
      obtain ⟨y, hy, hey⟩ := hex
      exact e.injective hey ▸ hy
  have hBpre : B = e ⁻¹' B' := by
    ext x
    constructor
    · intro hx
      exact hB ▸ ⟨x, hx, rfl⟩
    · intro hx
      have hex : e x ∈ e '' B := hB.symm ▸ hx
      obtain ⟨y, hy, hey⟩ := hex
      exact e.injective hey ▸ hy
  let eA : A ≃ₜ A' := e.sets hApre
  let eB : B ≃ₜ B' := e.sets hBpre
  let r' : A' → B' := fun x => eB (r (eA.symm x))
  refine ⟨r', eB.continuous.comp (hr.comp eA.symm.continuous), ?_⟩
  intro z
  apply Subtype.ext
  have hzB : e.symm z.1 ∈ B := by
    rw [hBpre]
    change e (e.symm z.1) ∈ B'
    rw [e.apply_symm_apply]
    exact z.2
  have hzA : e.symm z.1 ∈ A := hBA hzB
  change e (r ⟨e.symm z.1, hzA⟩).1 = z.1
  rw [show (r ⟨e.symm z.1, hzA⟩).1 = e.symm z.1 from
    congrArg Subtype.val (hretract ⟨e.symm z.1, hzB⟩)]
  exact e.apply_symm_apply z.1

/-- A nondegenerate closed plane triangle has no continuous retraction onto its frontier. -/
theorem IsTriangle.no_retraction {C : Set Plane} (hC : IsTriangle C) :
    ¬ ∃ r : C → frontier C,
      Continuous r ∧ ∀ z : frontier C,
        r ⟨z.1, hC.isCompact.isClosed.frontier_subset z.2⟩ = z := by
  obtain ⟨e, -, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hC.convex
      hC.infinite_interior.nonempty hC.isCompact.isBounded
  have hclosed : IsClosed C := hC.isCompact.isClosed
  have hCimage : e '' C = Metric.closedBall (0 : Plane) 1 := by
    rw [← hclosed.closure_eq]
    exact hclosure
  exact no_retraction_of_homeomorph e hCimage hfrontier
    hC.isCompact.isClosed.frontier_subset Metric.sphere_subset_closedBall
    no_retraction_planeClosedUnitBall

/-- Radial projection from an interior point of a bounded convex plane set retracts the
punctured plane onto the set's frontier.  The Minkowski gauge supplies the distance to the
frontier along each ray. -/
theorem exists_radial_retraction_to_frontier {C : Set Plane}
    (hconvex : Convex ℝ C) (hbounded : Bornology.IsBounded C)
    {q : Plane} (hq : q ∈ interior C) :
    ∃ R : {x : Plane // x ≠ q} → frontier C,
      Continuous R ∧
        ∀ x : frontier C, R ⟨x.1, fun h =>
          Set.disjoint_left.mp disjoint_interior_frontier hq (h ▸ x.2)⟩ = x := by
  let S : Set Plane := -q +ᵥ C
  have hSconvex : Convex ℝ S := by
    simpa only [S] using hconvex.vadd (-q)
  have hSnhds : S ∈ nhds (0 : Plane) := by
    rw [← mem_interior_iff_mem_nhds]
    change (0 : Plane) ∈ interior (-q +ᵥ C)
    rw [interior_vadd]
    exact ⟨q, hq, by simp [vadd_eq_add]⟩
  have hSbounded : Bornology.IsVonNBounded ℝ S :=
    NormedSpace.isVonNBounded_of_isBounded ℝ (hbounded.vadd (-q))
  have hSabsorbent : Absorbent ℝ S := absorbent_nhds_zero hSnhds
  have hgaugePos (x : {x : Plane // x ≠ q}) :
      0 < gauge S (x.1 - q) := by
    rw [gauge_pos hSabsorbent hSbounded]
    exact sub_ne_zero.mpr x.2
  let radial (x : {x : Plane // x ≠ q}) : Plane :=
    q + (gauge S (x.1 - q))⁻¹ • (x.1 - q)
  have hradialFrontier (x : {x : Plane // x ≠ q}) : radial x ∈ frontier C := by
    have hgauge : gauge S ((gauge S (x.1 - q))⁻¹ • (x.1 - q)) = 1 := by
      rw [gauge_smul_of_nonneg (inv_nonneg.mpr (hgaugePos x).le), smul_eq_mul,
        inv_mul_cancel₀ (hgaugePos x).ne']
    have hfrontierS : (gauge S (x.1 - q))⁻¹ • (x.1 - q) ∈ frontier S :=
      (gauge_eq_one_iff_mem_frontier hSconvex hSnhds).mp hgauge
    let w := (gauge S (x.1 - q))⁻¹ • (x.1 - q)
    have hwFrontier : w ∈ frontier (-q +ᵥ C) := hfrontierS
    rw [frontier, closure_vadd, interior_vadd] at hwFrontier
    rw [frontier]
    constructor
    · rcases hwFrontier.1 with ⟨y, hy, heq⟩
      change q + w ∈ closure C
      have hqy : q + w = y := by
        rw [← heq]
        simp [vadd_eq_add]
      exact hqy ▸ hy
    · intro hqwin
      change q + w ∈ interior C at hqwin
      apply hwFrontier.2
      exact ⟨q + w, hqwin, by simp [vadd_eq_add]⟩
  let R : {x : Plane // x ≠ q} → frontier C :=
    fun x => ⟨radial x, hradialFrontier x⟩
  refine ⟨R, ?_, ?_⟩
  · apply Continuous.subtype_mk
    have hgauge : Continuous fun x : {x : Plane // x ≠ q} => gauge S (x.1 - q) :=
      (continuous_gauge hSconvex hSnhds).comp
        (continuous_subtype_val.sub continuous_const)
    have hginv : Continuous fun x : {x : Plane // x ≠ q} => (gauge S (x.1 - q))⁻¹ :=
      hgauge.inv₀ fun x => (hgaugePos x).ne'
    exact continuous_const.add (hginv.smul (continuous_subtype_val.sub continuous_const))
  · intro x
    apply Subtype.ext
    have hxS : x.1 - q ∈ frontier S := by
      change x.1 - q ∈ frontier (-q +ᵥ C)
      rw [frontier, closure_vadd, interior_vadd]
      constructor
      · exact ⟨x.1, x.2.1, by simp [vadd_eq_add, sub_eq_add_neg, add_comm]⟩
      · rintro ⟨y, hy, heq⟩
        apply x.2.2
        have hyx : y = x.1 := by
          apply_fun (fun z : Plane => q + z) at heq
          simpa [vadd_eq_add, sub_eq_add_neg, add_assoc] using heq
        rwa [← hyx]
    have hgauge : gauge S (x.1 - q) = 1 :=
      (gauge_eq_one_iff_mem_frontier hSconvex hSnhds).mpr hxS
    change radial ⟨x.1, _⟩ = x.1
    simp [radial, hgauge]

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
