/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.MainTheorem.SixSphereCube3
public import LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology4
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1
import all LeanPool.HopfProblem.Hurewicz.SecondHurewicz
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Threefold.SpecialPeriods11
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology3
import all LeanPool.HopfProblem.Hurewicz.HigherHurewicz1
import all LeanPool.HopfProblem.Hurewicz.HigherHurewicz2
import all LeanPool.HopfProblem.MainTheorem.SixSphereCube2
import all LeanPool.HopfProblem.Hurewicz.SixthHurewicz
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology4
import all LeanPool.HopfProblem.MainTheorem.SixSphereCube3

/-!
# Hopf problem: threefold · special periods 12

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

private theorem SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton
    (x : SpecialPeriods.Threefold.Space) : Subsingleton (π_ 2 SpecialPeriods.Threefold.Space x) :=
  by
  have := SpecialPeriods.Threefold.space_simplyConnected
  have := ThreefoldHomology.SecondDegree.homologyTwo_subsingleton
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton

private theorem SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton
    (x : SpecialPeriods.Threefold.Space) : Subsingleton (π_ 3 SpecialPeriods.Threefold.Space x) :=
  by
  have := SpecialPeriods.Threefold.space_simplyConnected
  have := SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton x
  have := ThreefoldHomology.ThirdDegree.homologyThree_subsingleton
  exact (ThirdHurewicz.hurewiczPi3Equiv x).injective.subsingleton

private theorem SpecialPeriods.Threefold.HomotopyFour.piFour_subsingleton
    (x : SpecialPeriods.Threefold.Space) : Subsingleton (π_ 4 SpecialPeriods.Threefold.Space x) :=
  by
  have := SpecialPeriods.Threefold.space_simplyConnected
  have := SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton x
  have := SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton x
  have := ThreefoldHomology.FourthDegree.homologyFour_subsingleton
  exact (FourthHurewicz.hurewiczPi4Equiv x).injective.subsingleton

private theorem SpecialPeriods.Threefold.HomotopyFive.piFive_subsingleton
    (x : SpecialPeriods.Threefold.Space) : Subsingleton (π_ 5 SpecialPeriods.Threefold.Space x) :=
  by
  have := SpecialPeriods.Threefold.space_simplyConnected
  have := SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton x
  have := SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton x
  have := SpecialPeriods.Threefold.HomotopyFour.piFour_subsingleton x
  have := ThreefoldHomology.FifthDegree.homologyFive_subsingleton
  exact (FifthHurewicz.hurewiczPi5Equiv x).injective.subsingleton

private def
    SpecialPeriods.Threefold.HomotopySix.hurewiczEquiv (x : SpecialPeriods.Threefold.Space) :
    Additive (π_ 6 SpecialPeriods.Threefold.Space x) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6 := by
  letI := SpecialPeriods.Threefold.space_simplyConnected
  letI := SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton x
  letI := SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton x
  letI := SpecialPeriods.Threefold.HomotopyFour.piFour_subsingleton x
  letI := SpecialPeriods.Threefold.HomotopyFive.piFive_subsingleton x
  exact SixthHurewicz.hurewiczLinearEquiv x

@[simp]
private theorem
    SpecialPeriods.Threefold.HomotopySix.hurewiczEquiv_mk (x : SpecialPeriods.Threefold.Space)
    (p : GenLoop (Fin 6) SpecialPeriods.Threefold.Space x) :
    hurewiczEquiv x (Additive.ofMul (⟦p⟧ : π_ 6 SpecialPeriods.Threefold.Space x)) =
      SixthHurewicz.cubeHomologyClass p :=
  rfl

private def SpecialPeriods.Threefold.HomotopySix.piSixEquiv (x : SpecialPeriods.Threefold.Space) :
    Additive (π_ 6 SpecialPeriods.Threefold.Space x) ≃ₗ[ℤ] ℤ :=
  (hurewiczEquiv x).trans ThreefoldHomology.TopDegree.homologySixEquiv

private def SpecialPeriods.Threefold.HomotopySix.generator (x : SpecialPeriods.Threefold.Space) :
    Additive (π_ 6 SpecialPeriods.Threefold.Space x) :=
  (hurewiczEquiv x).symm ThreefoldHomology.TopDegree.topClass

@[simp]
private theorem SpecialPeriods.Threefold.HomotopySix.hurewiczEquiv_generator
    (x : SpecialPeriods.Threefold.Space) :
    hurewiczEquiv x (generator x) = ThreefoldHomology.TopDegree.topClass :=
  (hurewiczEquiv x).apply_symm_apply _

private theorem SpecialPeriods.Threefold.HomotopySix.exists_cube_topClass
    (x : SpecialPeriods.Threefold.Space) :
    ∃ p : GenLoop (Fin 6) SpecialPeriods.Threefold.Space x,
      SixthHurewicz.cubeHomologyClass p = ThreefoldHomology.TopDegree.topClass := by
  obtain ⟨p, hp⟩ := Quotient.exists_rep (Additive.toMul (generator x))
  have hclass : Additive.ofMul (⟦p⟧ : π_ 6 SpecialPeriods.Threefold.Space x) = generator x :=
    congrArg Additive.ofMul hp
  exact
    ⟨p,
      (hurewiczEquiv_mk x p).symm.trans
        ((congrArg (hurewiczEquiv x) hclass).trans (hurewiczEquiv_generator x))⟩

private def
    SpecialPeriods.Threefold.HomotopySix.generatingCube (x : SpecialPeriods.Threefold.Space) :
    GenLoop (Fin 6) SpecialPeriods.Threefold.Space x :=
  Classical.choose (exists_cube_topClass x)

@[simp]
private theorem SpecialPeriods.Threefold.HomotopySix.generatingCube_homologyClass
    (x : SpecialPeriods.Threefold.Space) :
    SixthHurewicz.cubeHomologyClass (generatingCube x) = ThreefoldHomology.TopDegree.topClass :=
  Classical.choose_spec (exists_cube_topClass x)

@[instance_reducible]
private def ManifoldAtlasTransport.chartedSpace {H M N : Type*} [TopologicalSpace H] [Nonempty H]
    [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace H M] (h : M ≃ₜ N) : ChartedSpace H N
    where
  atlas :=
    (fun e : OpenPartialHomeomorph M H => e.lift_openEmbedding h.isOpenEmbedding) '' atlas H M
  chartAt y := (chartAt H (h.symm y)).lift_openEmbedding h.isOpenEmbedding
  mem_chart_source y := ⟨h.symm y, mem_chart_source H (h.symm y), h.apply_symm_apply y⟩
  chart_mem_atlas y := ⟨chartAt H (h.symm y), chart_mem_atlas H (h.symm y), rfl⟩

public
theorem
    ManifoldAtlasTransport.transition_eq {H M N : Type*} [TopologicalSpace H] [Nonempty H]
    [TopologicalSpace M] [TopologicalSpace N] (h : M ≃ₜ N) (e e' : OpenPartialHomeomorph M H) :
    (e.lift_openEmbedding h.isOpenEmbedding).symm.trans
        (e'.lift_openEmbedding h.isOpenEmbedding) =
      e.symm.trans e' :=
  e.lift_openEmbedding_trans e' h.isOpenEmbedding

private theorem ManifoldAtlasTransport.isManifold {H M N : Type*} [TopologicalSpace H] [Nonempty H]
    [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace H M] {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (h : M ≃ₜ N) [IsManifold I n M] :
    letI := chartedSpace (H := H) h
    IsManifold I n N := by
  let := chartedSpace (H := H) h
  refine { compatible := ?_ }
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  rw [transition_eq]
  exact (contDiffGroupoid n I).compatible he he'

private theorem SpecialPeriods.Threefold.HomologySphere.homology_subsingleton (n : ℕ) (hn0 : n ≠ 0)
    (hn6 : n ≠ 6) :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space n) := by
  by_cases hn : 6 < n
  · exact ThreefoldHomology.Finiteness.homology_subsingleton_of_lt hn
  have hn' : n ≤ 6 := Nat.le_of_not_gt hn
  interval_cases n
  · exact (hn0 rfl).elim
  · exact SpecialPeriods.Threefold.LowDegrees.singularH1_subsingleton
  · exact ThreefoldHomology.SecondDegree.homologyTwo_subsingleton
  · exact ThreefoldHomology.ThirdDegree.homologyThree_subsingleton
  · exact ThreefoldHomology.FourthDegree.homologyFour_subsingleton
  · exact ThreefoldHomology.FifthDegree.homologyFive_subsingleton
  · exact (hn6 rfl).elim


private def SpecialPeriods.Threefold.HomologySphere.homologySixEquivSixSphere :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SixSphere 6 :=
  ThreefoldHomology.TopDegree.homologySixEquiv.trans SixSphereHomology.homologySixEquiv.symm

private theorem SpecialPeriods.Threefold.SphereHomologyMap.six_surjective_of_topClass_preimage
    (f : C(SixSphere, SpecialPeriods.Threefold.Space))
    (a : SingularMayerVietoris.SingularHomology SixSphere 6)
    (ha :
      SingularMayerVietoris.singularHomologyMap f 6 a = ThreefoldHomology.TopDegree.topClass) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap f 6) := by
  intro b
  refine ⟨ThreefoldHomology.TopDegree.homologySixEquiv b • a, ?_⟩
  rw [map_zsmul, ha]
  exact (ThreefoldHomology.TopDegree.eq_smul_topClass b).symm

private theorem SpecialPeriods.Threefold.SphereHomologyMap.six_bijective_of_topClass_preimage
    (f : C(SixSphere, SpecialPeriods.Threefold.Space))
    (a : SingularMayerVietoris.SingularHomology SixSphere 6)
    (ha :
      SingularMayerVietoris.singularHomologyMap f 6 a = ThreefoldHomology.TopDegree.topClass) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap f 6) := by
  let :
    IsNoetherian ℤ (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6) :=
    isNoetherian_of_injective ThreefoldHomology.TopDegree.homologySixEquiv.toLinearMap
      ThreefoldHomology.TopDegree.homologySixEquiv.injective
  have hsurj := six_surjective_of_topClass_preimage f a ha
  refine ⟨?_, hsurj⟩
  exact
    IsNoetherian.injective_of_surjective_of_injective
      SpecialPeriods.Threefold.HomologySphere.homologySixEquivSixSphere.symm.toLinearMap
      (SingularMayerVietoris.singularHomologyMap f 6)
      SpecialPeriods.Threefold.HomologySphere.homologySixEquivSixSphere.symm.injective hsurj

private theorem
    SpecialPeriods.Threefold.SphereHomologyMap.homologyMap_bijective_of_topClass_preimage
    (f : C(SixSphere, SpecialPeriods.Threefold.Space))
    (a : SingularMayerVietoris.SingularHomology SixSphere 6)
    (ha : SingularMayerVietoris.singularHomologyMap f 6 a = ThreefoldHomology.TopDegree.topClass)
    (n : ℕ) : Function.Bijective (SingularMayerVietoris.singularHomologyMap f n) := by
  by_cases hn0 : n = 0
  · subst n
    let := SpecialPeriods.Threefold.space_pathConnected
    exact SphereHomology.singularHomologyMap_zero_bijective f
  by_cases hn6 : n = 6
  · subst n
    exact six_bijective_of_topClass_preimage f a ha
  let := SpecialPeriods.Threefold.HomologySphere.homology_subsingleton n hn0 hn6
  let := SixSphereHomology.homology_subsingleton n hn0 hn6
  exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩

private def SpecialPeriods.Threefold.SphereHomologyMap.homologyEquivOfTopClassPreimage
    (f : C(SixSphere, SpecialPeriods.Threefold.Space))
    (a : SingularMayerVietoris.SingularHomology SixSphere 6)
    (ha : SingularMayerVietoris.singularHomologyMap f 6 a = ThreefoldHomology.TopDegree.topClass)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology SixSphere n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space n :=
  LinearEquiv.ofBijective (SingularMayerVietoris.singularHomologyMap f n)
    (homologyMap_bijective_of_topClass_preimage f a ha n)

private def SpecialPeriods.Threefold.SphereHomologyEquivalence.sourceCubeClass :
    SingularMayerVietoris.SingularHomology SixSphere 6 :=
  SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop

private def SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap
    (x : SpecialPeriods.Threefold.Space) : C(SixSphere, SpecialPeriods.Threefold.Space) :=
  SixSphereCube.factorMap (SpecialPeriods.Threefold.HomotopySix.generatingCube x)

@[simp]
private theorem SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap_sourceCubeClass
    (x : SpecialPeriods.Threefold.Space) :
    SingularMayerVietoris.singularHomologyMap (sphereMap x) 6 sourceCubeClass =
      ThreefoldHomology.TopDegree.topClass :=
  (SixSphereCube.factor_cubeHomologyClass
        (SpecialPeriods.Threefold.HomotopySix.generatingCube x)).trans
    (SpecialPeriods.Threefold.HomotopySix.generatingCube_homologyClass x)

private theorem SpecialPeriods.Threefold.SphereHomologyEquivalence.homologyMap_bijective
    (x : SpecialPeriods.Threefold.Space) (n : ℕ) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap (sphereMap x) n) :=
  SpecialPeriods.Threefold.SphereHomologyMap.homologyMap_bijective_of_topClass_preimage
    (sphereMap x) sourceCubeClass (sphereMap_sourceCubeClass x) n

private def SpecialPeriods.Threefold.SphereHomologyEquivalence.homologyEquiv
    (x : SpecialPeriods.Threefold.Space) (n : ℕ) :
    SingularMayerVietoris.SingularHomology SixSphere n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space n :=
  SpecialPeriods.Threefold.SphereHomologyMap.homologyEquivOfTopClassPreimage (sphereMap x)
    sourceCubeClass (sphereMap_sourceCubeClass x) n

end Mathoverflow1973

end
