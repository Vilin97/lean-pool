/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Hurewicz.SixthHurewicz
public import LeanPool.HopfProblem.Recognition.Smale12
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology2
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology3
import all LeanPool.HopfProblem.MainTheorem.SixSphereCube1
import all LeanPool.HopfProblem.MainTheorem.SixSphereCube2
import all LeanPool.HopfProblem.Recognition.Smale12
import all LeanPool.HopfProblem.Hurewicz.SixthHurewicz

/-!
# Hopf problem: main theorem · six sphere cube 3

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private abbrev SixSphere :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1

private def SixSphereHomology.homologyZeroEquiv :
    SingularMayerVietoris.SingularHomology SixSphere 0 ≃ₗ[ℤ] ℤ :=
  SphereHomology.unitSphereHomologyZeroEquiv 5

private def SixSphereHomology.homologySixEquiv :
    SingularMayerVietoris.SingularHomology SixSphere 6 ≃ₗ[ℤ] ℤ :=
  SphereHomology.unitSphereHomologyTopEquiv 5

private theorem SixSphereHomology.homology_subsingleton (k : ℕ) (hk : k ≠ 0) (hk6 : k ≠ 6) :
    Subsingleton (SingularMayerVietoris.SingularHomology SixSphere k) :=
  SphereHomology.unitSphere_homology_subsingleton 5 k hk hk6

private def
    SixSphereCube.collapseLift {K X : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace X] (F : Set K) (hF : IsClosed F) (hne : F.Nonempty) (f : C(K, X)) (x : X)
    (hf : ∀ a ∈ F, f a = x) : C(OnePoint ↥Fᶜ, X) :=
  Topology.IsQuotientMap.lift (f := collapseMap F hF) (isQuotientMap_collapse F hF hne) f
    (by
      intro a b h
      rcases (collapse_eq_iff F a b).mp h with rfl | ⟨ha, hb⟩
      · rfl
      · exact (hf a ha).trans (hf b hb).symm)

@[simp]
private theorem SixSphereCube.collapseLift_comp {K X : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [TopologicalSpace X] (F : Set K) (hF : IsClosed F) (hne : F.Nonempty)
    (f : C(K, X)) (x : X) (hf : ∀ a ∈ F, f a = x) :
    (collapseLift F hF hne f x hf).comp (collapseMap F hF) = f :=
  Topology.IsQuotientMap.lift_comp (f := collapseMap F hF) (isQuotientMap_collapse F hF hne) f _

@[simp]
private theorem SixSphereCube.collapseLift_apply {K X : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [TopologicalSpace X] (F : Set K) (hF : IsClosed F) (hne : F.Nonempty)
    (f : C(K, X)) (x : X) (hf : ∀ a ∈ F, f a = x) (a : K) :
    collapseLift F hF hne f x hf (collapse F a) = f a :=
  ContinuousMap.congr_fun (collapseLift_comp F hF hne f x hf) a

private abbrev SixSphereCube.OpenUnitInterval :=
  Set.Ioo (0 : ℝ) 1

private def SixSphereCube.openUnitIntervalAffineOrderIso : OpenUnitInterval ≃o Set.Ioo (-1 : ℝ) 1
    where
  toFun t := ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.1, t.property.2]⟩
  invFun t := ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
  left_inv
    t := by
    apply Subtype.ext
    change (2 * (t : ℝ) - 1 + 1) / 2 = (t : ℝ)
    ring
  right_inv
    t := by
    apply Subtype.ext
    change 2 * (((t : ℝ) + 1) / 2) - 1 = (t : ℝ)
    ring
  map_rel_iff' := by
    intro t s
    change 2 * (t : ℝ) - 1 ≤ 2 * (s : ℝ) - 1 ↔ (t : ℝ) ≤ (s : ℝ)
    constructor <;> intro h <;> linarith

private def SixSphereCube.openUnitIntervalHomeomorph : OpenUnitInterval ≃ₜ ℝ :=
  openUnitIntervalAffineOrderIso.toHomeomorph.trans (orderIsoIooNegOneOne ℝ).toHomeomorph.symm

private abbrev SixSphereCube.CubeInteriorN (n : ℕ) :=
  { u : Fin n → (unitInterval) // u ∉ Cube.boundary (Fin n) }

private theorem SixSphereCube.not_mem_cubeBoundary_iff {n : ℕ} (u : Fin n → (unitInterval)) :
    u ∉ Cube.boundary (Fin n) ↔ ∀ i, 0 < (u i : ℝ) ∧ (u i : ℝ) < 1 := by
  simp only [Cube.boundary, Set.mem_ofPred_eq, not_exists, not_or, unitInterval.coe_pos,
    unitInterval.coe_lt_one, unitInterval.pos_iff_ne_zero, unitInterval.lt_one_iff_ne_one]

private theorem SixSphereCube.cubeBoundary_eq_iUnion (n : ℕ) :
    Cube.boundary (Fin n) =
      ⋃ i : Fin n,
        {u : Fin n → (unitInterval) | u i = 0} ∪ {u : Fin n → (unitInterval) | u i = 1} := by
  ext u
  simp only [Cube.boundary, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union]

private theorem
    SixSphereCube.isClosed_cubeBoundaryN (n : ℕ) : IsClosed (Cube.boundary (Fin n)) := by
  rw [cubeBoundary_eq_iUnion]
  exact
    isClosed_iUnion_of_finite fun i =>
      (isClosed_eq (continuous_apply i) continuous_const).union
        (isClosed_eq (continuous_apply i) continuous_const)

private def
    SixSphereCube.cubeInteriorCoordinates (n : ℕ) : CubeInteriorN n ≃ₜ (Fin n → OpenUnitInterval)
    where
  toFun u i := ⟨(u.val i : ℝ), (not_mem_cubeBoundary_iff u.val).mp u.property i⟩
  invFun
    v :=
    ⟨fun i => ⟨(v i : ℝ), ⟨(v i).property.1.le, (v i).property.2.le⟩⟩,
      (not_mem_cubeBoundary_iff _).mpr fun i => (v i).property⟩
  left_inv
    u := by
    apply Subtype.ext
    funext i
    exact Subtype.ext rfl
  right_inv
    v := by
    funext i
    exact Subtype.ext rfl
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    have hi : Continuous (fun u : CubeInteriorN n => u.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact (continuous_subtype_val.comp hi).subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun i => ?_
    have hi : Continuous (fun v : Fin n → OpenUnitInterval => v i) := continuous_apply i
    exact (continuous_subtype_val.comp hi).subtype_mk _

private def SixSphereCube.cubeInteriorEuclideanHomeomorph (n : ℕ) :
    CubeInteriorN n ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (cubeInteriorCoordinates n).trans
    ((Homeomorph.piCongrRight fun _ : Fin n => openUnitIntervalHomeomorph).trans
      (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm)

private abbrev SixSphereCube.CubeInterior :=
  CubeInteriorN 6

private theorem SixSphereCube.isClosed_cubeBoundary : IsClosed (Cube.boundary (Fin 6)) :=
  isClosed_cubeBoundaryN 6

private abbrev SixSphereCube.cubeInteriorHomeomorph : CubeInterior ≃ₜ EuclideanSpace ℝ (Fin 6) :=
  cubeInteriorEuclideanHomeomorph 6

@[simp]
public
theorem SixSphereCube.zero_mem_cubeBoundary :
    (0 : Fin 6 → (unitInterval)) ∈ Cube.boundary (Fin 6) :=
  ⟨0, Or.inl rfl⟩

private theorem SixSphereCube.cubeBoundary_nonempty : (Cube.boundary (Fin 6)).Nonempty :=
  ⟨0, zero_mem_cubeBoundary⟩

private def SixSphereCube.cubeInteriorSphereHomeomorph : OnePoint CubeInterior ≃ₜ StandardSphere :=
  cubeInteriorHomeomorph.onePointCongr.trans euclideanOnePointSphereHomeomorph

@[simp]
private theorem SixSphereCube.cubeInteriorSphereHomeomorph_infty :
    cubeInteriorSphereHomeomorph (OnePoint.infty) = sphereBasePoint :=
  rfl

private def SixSphereCube.cubeSphereMap : C(Fin 6 → (unitInterval), StandardSphere) :=
  (cubeInteriorSphereHomeomorph : C(OnePoint CubeInterior, StandardSphere)).comp
    (collapseMap (Cube.boundary (Fin 6)) isClosed_cubeBoundary)

@[simp]
private theorem SixSphereCube.cubeSphereMap_apply (u : Fin 6 → (unitInterval)) :
    cubeSphereMap u = cubeInteriorSphereHomeomorph (collapse (Cube.boundary (Fin 6)) u) :=
  rfl

private theorem SixSphereCube.cubeSphereMap_boundary (u : Fin 6 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 6)) : cubeSphereMap u = sphereBasePoint := by
  rw [cubeSphereMap_apply, SixSphereCube.collapse_of_mem _ hu, cubeInteriorSphereHomeomorph_infty]

private theorem SixSphereCube.cubeSphereMap_eq_iff (u v : Fin 6 → (unitInterval)) :
    cubeSphereMap u = cubeSphereMap v ↔
      u = v ∨ u ∈ Cube.boundary (Fin 6) ∧ v ∈ Cube.boundary (Fin 6) := by
  change
    cubeInteriorSphereHomeomorph (collapse (Cube.boundary (Fin 6)) u) =
        cubeInteriorSphereHomeomorph (collapse (Cube.boundary (Fin 6)) v) ↔
      _
  rw [cubeInteriorSphereHomeomorph.injective.eq_iff, collapse_eq_iff]

private theorem SixSphereCube.cubeSphereMap_surjective : Function.Surjective cubeSphereMap :=
  cubeInteriorSphereHomeomorph.surjective.comp
    (collapse_surjective (Cube.boundary (Fin 6)) cubeBoundary_nonempty)

private def SixSphereCube.cubeSphereLoop : GenLoop (Fin 6) StandardSphere sphereBasePoint :=
  ⟨cubeSphereMap, cubeSphereMap_boundary⟩

@[simp]
private theorem SixSphereCube.cubeSphereLoop_val : cubeSphereLoop.val = cubeSphereMap :=
  rfl

private def
    SixSphereCube.factorMap {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    C(StandardSphere, X) :=
  (collapseLift (Cube.boundary (Fin 6)) isClosed_cubeBoundary cubeBoundary_nonempty p.val x
        (fun u hu => p.property u hu)).comp
    (cubeInteriorSphereHomeomorph.symm : C(StandardSphere, OnePoint CubeInterior))

private theorem SixSphereCube.factorMap_cubeSphereMap {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) (u : Fin 6 → (unitInterval)) :
    factorMap p (cubeSphereMap u) = p u := by
  change
    collapseLift (Cube.boundary (Fin 6)) isClosed_cubeBoundary cubeBoundary_nonempty p.val x
        (fun v hv => p.property v hv)
        (cubeInteriorSphereHomeomorph.symm
          (cubeInteriorSphereHomeomorph (collapse (Cube.boundary (Fin 6)) u))) =
      p u
  rw [cubeInteriorSphereHomeomorph.symm_apply_apply]
  exact
    collapseLift_apply (Cube.boundary (Fin 6)) isClosed_cubeBoundary cubeBoundary_nonempty p.val x
      (fun v hv => p.property v hv) u

@[simp]
private theorem SixSphereCube.factorMap_comp_cubeSphereMap {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) : (factorMap p).comp cubeSphereMap = p.val := by
  ext u
  exact factorMap_cubeSphereMap p u

private theorem SixSphereCube.factorMap_unique {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) (f : C(StandardSphere, X)) (hf : f.comp cubeSphereMap = p.val) :
    f = factorMap p := by
  ext z
  obtain ⟨u, rfl⟩ := cubeSphereMap_surjective z
  exact (ContinuousMap.congr_fun hf u).trans (factorMap_cubeSphereMap p u).symm

private theorem SixSphereCube.factor_cubeChain {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    FirstHurewicz.inducedChain (factorMap p) 6 (SixthHurewicz.cubeChain cubeSphereLoop) =
      SixthHurewicz.cubeChain p := by
  calc
    _ =
        FirstHurewicz.inducedChain ((factorMap p).comp cubeSphereMap) 6
          SixthHurewicz.fundamentalCubeChain := by
      rw [SixthHurewicz.cubeChain_eq_induced, cubeSphereLoop_val, FirstHurewicz.inducedChain_comp,
        LinearMap.comp_apply]
    _ = _ := by rw [factorMap_comp_cubeSphereMap, SixthHurewicz.cubeChain_eq_induced]

private theorem SixSphereCube.factor_cubeCycle {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.ModuleHomology.mapCycles (FirstHurewicz.singularChainMap (factorMap p))
        6 (SixthHurewicz.cubeCycle cubeSphereLoop) =
      SixthHurewicz.cubeCycle p := by
  apply Subtype.ext
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, SixthHurewicz.cubeCycle_val,
    SixthHurewicz.cubeCycle_val]
  exact factor_cubeChain p

private theorem SixSphereCube.factor_cubeHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.singularHomologyMap (factorMap p) 6
        (SixthHurewicz.cubeHomologyClass cubeSphereLoop) =
      SixthHurewicz.cubeHomologyClass p := by
  change
    (HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap (factorMap p)) 6).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (FirstHurewicz.singularComplex StandardSphere) 6
          (SixthHurewicz.cubeCycle cubeSphereLoop)) =
      _
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, factor_cubeCycle]
  rfl

end Mathoverflow1973

end
