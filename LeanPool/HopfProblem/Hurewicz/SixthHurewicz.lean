/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.CuspFibre.CuspNegation
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.Hurewicz.SecondHurewicz
import all LeanPool.HopfProblem.Hurewicz.ThirdHurewicz
import all LeanPool.HopfProblem.Hurewicz.HigherHurewicz1
import all LeanPool.HopfProblem.Hurewicz.HigherHurewicz2
import all LeanPool.HopfProblem.CuspFibre.CuspNegation

/-!
# Hopf problem: hurewicz · sixth hurewicz

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

private def SixthHurewicz.lowerSevenSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 7) :
    C((unitInterval) × FirstHurewicz.Simplex 7, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (FifthHurewicz.normalizationSixSimplexHomotopy x)
    (FifthHurewicz.normalizationSixHomotopy_face x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x) smp

@[simp]
private theorem SixthHurewicz.lowerSevenSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 7)
    (s : FirstHurewicz.Simplex 7) : lowerSevenSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem SixthHurewicz.lowerSevenSimplexHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 6
      (FifthHurewicz.normalizationSixSimplexHomotopy x) (lowerSevenSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (FifthHurewicz.normalizationSixSimplexHomotopy x)
    (FifthHurewicz.normalizationSixHomotopy_face x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x)

private def SixthHurewicz.fiveSixSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 6) :
    C((unitInterval) × FirstHurewicz.Simplex 6, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 4)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x) smp

@[simp]
private theorem SixthHurewicz.fiveSixSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 6)
    (s : FirstHurewicz.Simplex 6) : fiveSixSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem SixthHurewicz.fiveSixSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 5 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 5
      (HigherHurewicz.simplexStraighteningHomotopy 5 x) (fiveSixSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 4)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x)

private def SixthHurewicz.fiveSevenSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 7) :
    C((unitInterval) × FirstHurewicz.Simplex 7, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (HigherHurewicz.simplexStraighteningHomotopy 5 x) (fiveSixSimplexHomotopy x)
    (fiveSixSimplexHomotopy_face x) (fiveSixSimplexHomotopy_zero x) smp

@[simp]
private theorem SixthHurewicz.fiveSevenSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 7)
    (s : FirstHurewicz.Simplex 7) : fiveSevenSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem SixthHurewicz.fiveSevenSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 5 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 6 (fiveSixSimplexHomotopy x)
      (fiveSevenSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (HigherHurewicz.simplexStraighteningHomotopy 5 x) (fiveSixSimplexHomotopy x)
    (fiveSixSimplexHomotopy_face x) (fiveSixSimplexHomotopy_zero x)

private def SixthHurewicz.normalizationFiveSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    FirstHurewicz.SingularSimplex X 5 → C((unitInterval) × FirstHurewicz.Simplex 5, X) :=
  ThirdHurewicz.composeSimplexHomotopies (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (FifthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x)

private def SixthHurewicz.normalizationSixSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    FirstHurewicz.SingularSimplex X 6 → C((unitInterval) × FirstHurewicz.Simplex 6, X) :=
  ThirdHurewicz.composeSimplexHomotopies (FifthHurewicz.normalizationSixSimplexHomotopy x)
    (fiveSixSimplexHomotopy x) (FifthHurewicz.normalizationSixSimplexHomotopy_zero x)
    (fiveSixSimplexHomotopy_zero x)

private def SixthHurewicz.normalizationSevenSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    FirstHurewicz.SingularSimplex X 7 → C((unitInterval) × FirstHurewicz.Simplex 7, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerSevenSimplexHomotopy x)
    (fiveSevenSimplexHomotopy x) (lowerSevenSimplexHomotopy_zero x)
    (fiveSevenSimplexHomotopy_zero x)

@[simp]
private theorem SixthHurewicz.normalizationSixSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 6)
    (s : FirstHurewicz.Simplex 6) : normalizationSixSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

private theorem SixthHurewicz.normalizationHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 5 (normalizationFiveSimplexHomotopy x)
      (normalizationSixSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (FifthHurewicz.normalizationSixSimplexHomotopy x) (fiveSixSimplexHomotopy x)
    (FifthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x) (fiveSixSimplexHomotopy_zero x)
    (FifthHurewicz.normalizationSixHomotopy_face x) (fiveSixSimplexHomotopy_face x)

private theorem SixthHurewicz.normalizationSevenHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 6 (normalizationSixSimplexHomotopy x)
      (normalizationSevenSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (FifthHurewicz.normalizationSixSimplexHomotopy x)
    (fiveSixSimplexHomotopy x) (lowerSevenSimplexHomotopy x) (fiveSevenSimplexHomotopy x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x) (fiveSixSimplexHomotopy_zero x)
    (lowerSevenSimplexHomotopy_zero x) (fiveSevenSimplexHomotopy_zero x)
    (lowerSevenSimplexHomotopy_face x) (fiveSevenSimplexHomotopy_face x)

@[simp]
private theorem SixthHurewicz.normalizationFiveSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    normalizationFiveSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 5) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 5) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (FifthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x) x
    (FifthHurewicz.normalizationFiveSimplexHomotopy_const x)
    (HigherHurewicz.simplexStraighteningHomotopy_const 5 x)

@[simp]
private theorem
    SixthHurewicz.normalizationFiveSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) :
    SecondHurewicz.SimplyConnected.timeSlice (normalizationFiveSimplexHomotopy x smp) 1 =
      ContinuousMap.const (FirstHurewicz.Simplex 5) x := by
  rw [normalizationFiveSimplexHomotopy, ThirdHurewicz.timeSlice_composeSimplexHomotopies_one,
    FifthHurewicz.normalizationFiveSimplexHomotopy_endpoint]
  ext s
  exact
    HigherHurewicz.simplexStraighteningHomotopy_one 5 x
      (FifthHurewicz.normalizedFiveSimplex x smp).val
      (FifthHurewicz.normalizedFiveSimplex x smp).property s

private abbrev SixthHurewicz.sixSimplexBoundary : Set (FirstHurewicz.Simplex 6) :=
  SecondHurewicz.SimplyConnected.simplexBoundary 6

private abbrev SixthHurewicz.BasedSixSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplex 6 x

private abbrev SixthHurewicz.basedSixSimplexLoop {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) : GenLoop (Fin 6) X x :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoop τ

private abbrev SixthHurewicz.basedSixSimplexClass {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) : Additive (π_ 6 X x) :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass τ

private theorem SixthHurewicz.basedSixSimplex_face {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) (i : Fin 7) :
    τ.val.comp (FirstHurewicz.simplexFace 5 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 5) x :=
  HigherHurewicz.SimplexGeometry.basedSimplex_face τ i

private def
    SixthHurewicz.normalizedSixSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 6) : BasedSixSimplex x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (normalizationSixSimplexHomotopy x smp) 1,
    HigherHurewicz.simplexEndpoint_boundary (normalizationFiveSimplexHomotopy x)
      (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x) x
      (normalizationFiveSimplexHomotopy_endpoint x) smp⟩

private def SixthHurewicz.normalizedSevenSimplexMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (smp : FirstHurewicz.SingularSimplex X 7) : FirstHurewicz.SingularSimplex X 7 :=
  SecondHurewicz.SimplyConnected.timeSlice (normalizationSevenSimplexHomotopy x smp) 1

private theorem SixthHurewicz.normalizedSevenSimplexMap_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 7)
    (i : Fin 8) :
    (normalizedSevenSimplexMap x smp).comp (FirstHurewicz.simplexFace 6 i) =
      (normalizedSixSimplex x (smp.comp (FirstHurewicz.simplexFace 6 i))).val :=
  SecondHurewicz.SimplyConnected.timeSlice_face (normalizationSevenHomotopy_face x) smp i 1

private theorem
    SixthHurewicz.normalizedSevenSimplexMap_face_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 7)
    (i : Fin 8) (s : FirstHurewicz.Simplex 6) (hs : s ∈ sixSimplexBoundary) :
    normalizedSevenSimplexMap x smp (FirstHurewicz.simplexFace 6 i s) = x := by
  have hf :=
    congrArg (fun f : C(FirstHurewicz.Simplex 6, X) => f s)
      (normalizedSevenSimplexMap_face x smp i)
  exact
    hf.trans ((normalizedSixSimplex x (smp.comp (FirstHurewicz.simplexFace 6 i))).property s hs)

private def
    SixthHurewicz.sixSimplexClassOperator {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] : FirstHurewicz.Chains X 6 →ₗ[ℤ] Additive (π_ 6 X x) :=
  FirstHurewicz.chainLift X 6 fun smp => basedSixSimplexClass (normalizedSixSimplex x smp)

@[simp]
private theorem SixthHurewicz.sixSimplexClassOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (smp : FirstHurewicz.SingularSimplex X 6) :
    sixSimplexClassOperator x (FirstHurewicz.simplexChain X 6 smp) =
      basedSixSimplexClass (normalizedSixSimplex x smp) :=
  FirstHurewicz.chainLift_simplex X 6 _ smp

private abbrev SixthHurewicz.BasedSevenSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplexBoundary 7 x

private abbrev SixthHurewicz.basedSevenSimplexFace {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSevenSimplex x) (i : Fin 8) : BasedSixSimplex x :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundaryFace τ i

private def SixthHurewicz.BasedSevenSimplex.ofFaces {X : Type*} [TopologicalSpace X] {x : X}
    (τ : C(FirstHurewicz.Simplex 7, X))
    (h :
      ∀ i : Fin 8,
        ∀ s ∈ SixthHurewicz.sixSimplexBoundary, (τ.comp (FirstHurewicz.simplexFace 6 i)) s = x) :
    SixthHurewicz.BasedSevenSimplex x :=
  HigherHurewicz.SimplexGeometry.BasedSimplexBoundary.ofFaces τ h

private theorem
    SixthHurewicz.basedSevenSimplex_signed_relation {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSevenSimplex x) :
    (∑ i : Fin 8, (-1 : ℤ) ^ i.val • basedSixSimplexClass (basedSevenSimplexFace τ i)) = 0 :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation (n := 4) τ

private def
    SixthHurewicz.normalizedSevenSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 7) : BasedSevenSimplex x :=
  BasedSevenSimplex.ofFaces (normalizedSevenSimplexMap x smp)
    (normalizedSevenSimplexMap_face_boundary x smp)

@[simp]
private theorem SixthHurewicz.normalizedSevenSimplex_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 7)
    (i : Fin 8) :
    basedSevenSimplexFace (normalizedSevenSimplex x smp) i =
      normalizedSixSimplex x (smp.comp (FirstHurewicz.simplexFace 6 i)) := by
  apply Subtype.ext
  exact normalizedSevenSimplexMap_face x smp i

private theorem SixthHurewicz.normalizedSixSimplex_boundary_relation {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (smp : FirstHurewicz.SingularSimplex X 7) :
    ∑ i : Fin 8,
        (-1 : ℤ) ^ i.val •
          basedSixSimplexClass
            (normalizedSixSimplex x (smp.comp (FirstHurewicz.simplexFace 6 i))) =
      0 := by
  simpa only [normalizedSevenSimplex_face] using
    basedSevenSimplex_signed_relation (normalizedSevenSimplex x smp)

private theorem SixthHurewicz.sixSimplexClassOperator_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (b : FirstHurewicz.Chains X 7) :
    sixSimplexClassOperator x (((FirstHurewicz.singularComplex X).d 7 6).hom b) = 0 := by
  have h : (sixSimplexClassOperator x).comp ((FirstHurewicz.singularComplex X).d 7 6).hom = 0 := by
    apply FirstHurewicz.chainMap_ext X 7
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundary_simplex, map_sum, map_zsmul,
      sixSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedSixSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

private def
    SixthHurewicz.normalizedCube {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x) : GenLoop (Fin 6) X x :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint (normalizationFiveSimplexHomotopy x)
    (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFiveSimplexHomotopy_const x) p

private theorem
    SixthHurewicz.normalizedCube_cell {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x) (e : Equiv.Perm (Fin 6)) :
    (normalizedCube x p).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e) =
      (normalizedSixSimplex x
          (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))).val :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint_cell (normalizationFiveSimplexHomotopy x)
    (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFiveSimplexHomotopy_const x) p e

private def SixthHurewicz.normalizationCubeHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 6)) :=
  HigherHurewicz.CubeGluing.coherentCubeHomotopy (normalizationFiveSimplexHomotopy x)
    (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFiveSimplexHomotopy_const x) (normalizationSixSimplexHomotopy_zero x) p

private theorem SixthHurewicz.normalizedCube_internalBased {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x)
    (u : Fin 6 → (unitInterval)) (i j : Fin 6) (hij : i ≠ j) (hu : u i = u j) :
    normalizedCube x p u = x :=
  HigherHurewicz.coherentCubeEndpoint_internalBased (normalizationFiveSimplexHomotopy x)
    (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFiveSimplexHomotopy_const x) (normalizationFiveSimplexHomotopy_endpoint x) p u i
    j hij hu

private theorem SixthHurewicz.normalizedCube_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x)
    (e : Equiv.Perm (Fin 6)) :
    HigherHurewicz.NativeSubdivision.nativeBasedCubeSimplex (normalizedCube x p)
        (normalizedCube_internalBased x p) e =
      normalizedSixSimplex x (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

private abbrev SixthHurewicz.Remaining :=
  { j : Fin 6 // j ≠ 0 }

private def
    SixthHurewicz.remainingCoordinates : C(Fin 5 → (unitInterval), Remaining → (unitInterval))
    where
  toFun u j := u (j.val.pred j.property)
  continuous_toFun := by fun_prop

@[simp]
private theorem SixthHurewicz.remainingCoordinates_succ (u : Fin 5 → (unitInterval)) (i : Fin 5) :
    remainingCoordinates u ⟨i.succ, Fin.succ_ne_zero i⟩ = u i := by simp [remainingCoordinates]

private theorem SixthHurewicz.remainingCoordinates_boundary {u : Fin 5 → (unitInterval)}
    (h : u ∈ Cube.boundary (Fin 5)) : remainingCoordinates u ∈ Cube.boundary Remaining := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simpa using hi⟩

private abbrev SixthHurewicz.BasedLoopSpace {X : Type} [TopologicalSpace X] (x : X) :=
  GenLoop Remaining X x

private def SixthHurewicz.evaluation {X : Type} [TopologicalSpace X] (x : X) :
    C(BasedLoopSpace x × (Fin 5 → (unitInterval)), X)
    where
  toFun z := z.1 (remainingCoordinates z.2)
  continuous_toFun := by fun_prop

private theorem SixthHurewicz.evaluation_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) (u : Fin 5 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 5)) :
    evaluation x (p, u) = x :=
  GenLoop.boundary p _ (remainingCoordinates_boundary hu)

private theorem SixthHurewicz.evaluation_comp_boundary {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (x : X) (f : C(A, Fin 5 → (unitInterval)))
    (hf : ∀ a, f a ∈ Cube.boundary (Fin 5)) :
    (evaluation x).comp ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) =
      ContinuousMap.const (BasedLoopSpace x × A) x := by
  ext z
  exact evaluation_boundary x z.1 (f z.2) (hf z.2)

private def SixthHurewicz.cubeCoordinates :
    C((unitInterval) × (Fin 5 → (unitInterval)), Fin 6 → (unitInterval))
    where
  toFun z := Cube.insertAt (0 : Fin 6) (z.1, remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp]
private theorem SixthHurewicz.cubeCoordinates_zero (z : (unitInterval) × (Fin 5 → (unitInterval))) :
    cubeCoordinates z 0 = z.1 := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp]
private theorem SixthHurewicz.cubeCoordinates_succ (z : (unitInterval) × (Fin 5 → (unitInterval)))
    (i : Fin 5) : cubeCoordinates z i.succ = z.2 i := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply, remainingCoordinates]

private def
    SixthHurewicz.cubeMap {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    C((unitInterval) × (Fin 5 → (unitInterval)), X) :=
  p.val.comp cubeCoordinates

private theorem SixthHurewicz.evaluation_comp_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 6) p).toContinuousMap.prodMap
          (ContinuousMap.id (Fin 5 → (unitInterval)))) =
      cubeMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SixthHurewicz.remainingCubeSideFirst (t : (unitInterval)) :
    C(Fin 4 → (unitInterval), Fin 5 → (unitInterval)) :=
  FifthHurewicz.cubeCoordinates.comp (PeriodTorusHigherHomology.crossInsertLeft t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SixthHurewicz.remainingCubeSide {A : Type} [TopologicalSpace A]
    (f : C(A, Fin 4 → (unitInterval))) : C((unitInterval) × A, Fin 5 → (unitInterval)) :=
  FifthHurewicz.cubeCoordinates.comp ((ContinuousMap.id (unitInterval)).prodMap f)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SixthHurewicz.remainingCubeSideFirst_boundary (t : (unitInterval)) (ht : t = 0 ∨ t = 1)
    (u : Fin 4 → (unitInterval)) : remainingCubeSideFirst t u ∈ Cube.boundary (Fin 5) := by
  refine ⟨0, ?_⟩
  change FifthHurewicz.cubeCoordinates (t, u) 0 = 0 ∨ FifthHurewicz.cubeCoordinates (t, u) 0 = 1
  simpa only [FifthHurewicz.cubeCoordinates_zero] using ht

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.remainingCubeSide_boundary {A : Type} [TopologicalSpace A]
    (f : C(A, Fin 4 → (unitInterval))) (hf : ∀ a, f a ∈ Cube.boundary (Fin 4))
    (z : (unitInterval) × A) : remainingCubeSide f z ∈ Cube.boundary (Fin 5) := by
  obtain ⟨i, hi⟩ := hf z.2
  refine ⟨i.succ, ?_⟩
  change
    FifthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 0 ∨
      FifthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 1
  simpa only [FifthHurewicz.cubeCoordinates_succ] using hi

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.remainingCubeSide_chain {A : Type} [TopologicalSpace A] (k : ℕ)
    (f : C(A, Fin 4 → (unitInterval))) (b : FirstHurewicz.Chains A k) :
    FirstHurewicz.inducedChain FifthHurewicz.cubeCoordinates (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 4 → (unitInterval)) k
          SecondHurewicz.intervalChain (FirstHurewicz.inducedChain f k b)) =
      FirstHurewicz.inducedChain (remainingCubeSide f) (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) A k
          SecondHurewicz.intervalChain b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval)) f k
      SecondHurewicz.intervalChain b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain FifthHurewicz.cubeCoordinates (k + 1)).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (unitInterval)).prodMap f) (k + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SixthHurewicz.productTwoIntervalSquareChain :
    FirstHurewicz.Chains ((unitInterval) × ((unitInterval) × (Fin 2 → (unitInterval)))) 4 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval)
    ((unitInterval) × (Fin 2 → (unitInterval))) 3 SecondHurewicz.intervalChain
    ThirdHurewicz.productCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SixthHurewicz.productFourIntervalChain :
    FirstHurewicz.Chains ((unitInterval) × ((unitInterval) × ((unitInterval) × (unitInterval))))
      4 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval)
    ((unitInterval) × ((unitInterval) × (unitInterval))) 3 SecondHurewicz.intervalChain
    FifthHurewicz.productThreeIntervalChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.remainingCubeChain_boundary :
    ((FirstHurewicz.singularComplex (Fin 5 → (unitInterval))).d 5 4).hom
        FifthHurewicz.fundamentalCubeChain =
      FirstHurewicz.inducedChain (remainingCubeSideFirst 1) 4
            FourthHurewicz.fundamentalCubeChain -
          FirstHurewicz.inducedChain (remainingCubeSideFirst 0) 4
            FourthHurewicz.fundamentalCubeChain -
        (FirstHurewicz.inducedChain (remainingCubeSide (FifthHurewicz.remainingCubeSideFirst 1)) 4
              FourthHurewicz.productCubeChain -
            FirstHurewicz.inducedChain
              (remainingCubeSide (FifthHurewicz.remainingCubeSideFirst 0)) 4
              FourthHurewicz.productCubeChain -
          (FirstHurewicz.inducedChain
                (remainingCubeSide
                  (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst 1)))
                4 productTwoIntervalSquareChain -
              FirstHurewicz.inducedChain
                (remainingCubeSide
                  (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst 0)))
                4 productTwoIntervalSquareChain -
            (FirstHurewicz.inducedChain
                  (remainingCubeSide
                    (FifthHurewicz.remainingCubeSide
                      (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft 1))))
                  4 productFourIntervalChain -
                FirstHurewicz.inducedChain
                  (remainingCubeSide
                    (FifthHurewicz.remainingCubeSide
                      (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft 0))))
                  4 productFourIntervalChain -
              (FirstHurewicz.inducedChain
                  (remainingCubeSide
                    (FifthHurewicz.remainingCubeSide
                      (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight 1))))
                  4 productFourIntervalChain -
                FirstHurewicz.inducedChain
                  (remainingCubeSide
                    (FifthHurewicz.remainingCubeSide
                      (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight 0))))
                  4 productFourIntervalChain)))) := by
  have hpoint (t : (unitInterval)) :
    PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (Fin 4 → (unitInterval)) 4
        (FirstHurewicz.pointChain t) FourthHurewicz.fundamentalCubeChain =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) 4
        FourthHurewicz.fundamentalCubeChain := by
    rw [FirstHurewicz.pointChain, PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left]
    rfl
  have hfirst (t : (unitInterval)) :
    FirstHurewicz.inducedChain FifthHurewicz.cubeCoordinates 4
        (FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) 4
          FourthHurewicz.fundamentalCubeChain) =
      FirstHurewicz.inducedChain (remainingCubeSideFirst t) 4
        FourthHurewicz.fundamentalCubeChain := by
    rw [remainingCubeSideFirst, FirstHurewicz.inducedChain_comp]
    rfl
  rw [FifthHurewicz.fundamentalCubeChain, ← FirstHurewicz.inducedChain_boundary]
  change
    FirstHurewicz.inducedChain FifthHurewicz.cubeCoordinates 4
        (((FirstHurewicz.singularComplex ((unitInterval) × (Fin 4 → (unitInterval)))).d 5 4).hom
          (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 4 → (unitInterval)) 4
            SecondHurewicz.intervalChain FourthHurewicz.fundamentalCubeChain)) =
      _
  rw [PeriodTorusHigherHomology.crossProductEdge_boundary 3]
  change
    FirstHurewicz.inducedChain FifthHurewicz.cubeCoordinates 4
        (PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (Fin 4 → (unitInterval)) 4
            (FirstHurewicz.boundaryOne (unitInterval) SecondHurewicz.intervalChain)
            FourthHurewicz.fundamentalCubeChain -
          PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 4 → (unitInterval)) 3
            SecondHurewicz.intervalChain
            (((FirstHurewicz.singularComplex (Fin 4 → (unitInterval))).d 4 3).hom
              FourthHurewicz.fundamentalCubeChain)) =
      _
  rw [SecondHurewicz.intervalChain_boundary, FifthHurewicz.remainingCubeChain_boundary]
  simp only [map_sub, LinearMap.sub_apply, hpoint, hfirst, remainingCubeSide_chain]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.evaluated_edge_boundaryMap {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) (k : ℕ)
    (b : FirstHurewicz.Chains A k) (f : C(A, Fin 5 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 5)) :
    FirstHurewicz.inducedChain (evaluation x) (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 5 → (unitInterval)) k
          a (FirstHurewicz.inducedChain f k b)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) A k a b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (BasedLoopSpace x)) f k a
      b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) (k + 1)).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) (k + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.evaluated_triangle_boundaryMap {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) (k : ℕ)
    (b : FirstHurewicz.Chains A k) (f : C(A, Fin 5 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 5)) :
    FirstHurewicz.inducedChain (evaluation x) (k + 2)
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 5 → (unitInterval)) k a (FirstHurewicz.inducedChain f k b)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) (k + 2)
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) A k a b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f
      k a b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) (k + 2)).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) (k + 2)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SixthHurewicz.evaluated_edge_cubeBoundary_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    FirstHurewicz.inducedChain (evaluation x) 5
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 5 → (unitInterval)) 4
          a
          (((FirstHurewicz.singularComplex (Fin 5 → (unitInterval))).d 5 4).hom
            FifthHurewicz.fundamentalCubeChain)) =
      0 := by
  have hF (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 FourthHurewicz.fundamentalCubeChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hS (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 FourthHurewicz.productCubeChain
      (remainingCubeSide (FifthHurewicz.remainingCubeSideFirst t))
      (remainingCubeSide_boundary _ (FifthHurewicz.remainingCubeSideFirst_boundary t ht))
  have hT (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 productTwoIntervalSquareChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t)))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSideFirst_boundary t ht)))
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 productFourIntervalChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide
          (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t))))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSide_boundary _
            (ThirdHurewicz.squareSideLeft_boundary t ht))))
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 productFourIntervalChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide
          (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t))))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSide_boundary _
            (ThirdHurewicz.squareSideRight_boundary t ht))))
  simp only [remainingCubeChain_boundary, map_sub, hF 1 (Or.inr rfl), hF 0 (Or.inl rfl),
    hS 1 (Or.inr rfl), hS 0 (Or.inl rfl), hT 1 (Or.inr rfl), hT 0 (Or.inl rfl), hL 1 (Or.inr rfl),
    hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.evaluated_triangle_cubeBoundary_cancel {X : Type} [TopologicalSpace X]
    (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    FirstHurewicz.inducedChain (evaluation x) 6
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 5 → (unitInterval)) 4 a
          (((FirstHurewicz.singularComplex (Fin 5 → (unitInterval))).d 5 4).hom
            FifthHurewicz.fundamentalCubeChain)) =
      0 := by
  have hF (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 FourthHurewicz.fundamentalCubeChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hS (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 FourthHurewicz.productCubeChain
      (remainingCubeSide (FifthHurewicz.remainingCubeSideFirst t))
      (remainingCubeSide_boundary _ (FifthHurewicz.remainingCubeSideFirst_boundary t ht))
  have hT (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 productTwoIntervalSquareChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t)))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSideFirst_boundary t ht)))
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 productFourIntervalChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide
          (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t))))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSide_boundary _
            (ThirdHurewicz.squareSideLeft_boundary t ht))))
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 productFourIntervalChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide
          (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t))))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSide_boundary _
            (ThirdHurewicz.squareSideRight_boundary t ht))))
  simp only [remainingCubeChain_boundary, map_sub, hF 1 (Or.inr rfl), hF 0 (Or.inl rfl),
    hS 1 (Or.inr rfl), hS 0 (Or.inl rfl), hT 1 (Or.inr rfl), hT 0 (Or.inl rfl), hL 1 (Or.inr rfl),
    hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SixthHurewicz.suspensionOne {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 1 →ₗ[ℤ] FirstHurewicz.Chains X 6 :=
  (FirstHurewicz.inducedChain (evaluation x) 6).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 5 → (unitInterval)) 5)
      FifthHurewicz.fundamentalCubeChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem SixthHurewicz.suspensionOne_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    suspensionOne x a =
      FirstHurewicz.inducedChain (evaluation x) 6
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 5 → (unitInterval)) 5
          a FifthHurewicz.fundamentalCubeChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SixthHurewicz.suspensionTwo {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 2 →ₗ[ℤ] FirstHurewicz.Chains X 7 :=
  (FirstHurewicz.inducedChain (evaluation x) 7).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (Fin 5 → (unitInterval))
        5)
      FifthHurewicz.fundamentalCubeChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem SixthHurewicz.suspensionTwo_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a =
      FirstHurewicz.inducedChain (evaluation x) 7
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 5 → (unitInterval)) 5 a FifthHurewicz.fundamentalCubeChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SixthHurewicz.boundarySix_suspensionOne_of_cycle {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (ha : FirstHurewicz.boundaryOne (BasedLoopSpace x) a = 0) :
    ((FirstHurewicz.singularComplex X).d 6 5).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary 4]
  change
    FirstHurewicz.inducedChain (evaluation x) 5
        (PeriodTorusHigherHomology.crossProductZeroLeft (BasedLoopSpace x)
            (Fin 5 → (unitInterval)) 5 (FirstHurewicz.boundaryOne (BasedLoopSpace x) a)
            FifthHurewicz.fundamentalCubeChain -
          PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 5 → (unitInterval)) 4
            a
            (((FirstHurewicz.singularComplex (Fin 5 → (unitInterval))).d 5 4).hom
              FifthHurewicz.fundamentalCubeChain)) =
      0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg, evaluated_edge_cubeBoundary_cancel,
    neg_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.boundarySeven_suspensionTwo {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    ((FirstHurewicz.singularComplex X).d 7 6).hom (suspensionTwo x a) =
      suspensionOne x (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductTriangle_boundary 4]
  change
    FirstHurewicz.inducedChain (evaluation x) 6
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 5 → (unitInterval)) 5
            (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) FifthHurewicz.fundamentalCubeChain +
          PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
            (Fin 5 → (unitInterval)) 4 a
            (((FirstHurewicz.singularComplex (Fin 5 → (unitInterval))).d 5 4).hom
              FifthHurewicz.fundamentalCubeChain)) =
      _
  rw [map_add, evaluated_triangle_cubeBoundary_cancel, add_zero]
  rfl

private def SixthHurewicz.pathCubeCycle {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 6
    (suspensionOne x (FirstHurewicz.pathChain p))
    (boundarySix_suspensionOne_of_cycle x (FirstHurewicz.pathChain p)
      (FirstHurewicz.boundaryOne_loop p))

@[simp]
private theorem SixthHurewicz.pathCubeCycle_val {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathCubeCycle x p).1 = suspensionOne x (FirstHurewicz.pathChain p) :=
  rfl

private def SixthHurewicz.pathCubeClass {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.SingularHomology X 6 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
    (pathCubeCycle x p)

private theorem SixthHurewicz.pathCube_homotopy_boundary {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((FirstHurewicz.singularComplex X).d 7 6).hom
        (suspensionTwo x (FirstHurewicz.homotopyChain H)) =
      (pathCubeCycle x p).1 - (pathCubeCycle x q).1 := by
  rw [boundarySeven_suspensionTwo, FirstHurewicz.boundaryTwo_loopHomotopy, map_sub]
  rfl

private theorem SixthHurewicz.pathCubeClass_homotopy {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathCubeClass x p = pathCubeClass x q :=
  (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 6 _
        _).mpr
    ⟨suspensionTwo x (FirstHurewicz.homotopyChain H), pathCube_homotopy_boundary x H⟩

private theorem SixthHurewicz.pathCubeClass_homotopic {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathCubeClass x p = pathCubeClass x q := by
  obtain ⟨H⟩ := h
  exact pathCubeClass_homotopy x H

@[simp]
private theorem SixthHurewicz.pathCubeClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathCubeClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        6 _).mpr
  refine
    ⟨suspensionTwo x (FirstHurewicz.constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundarySeven_suspensionTwo, FirstHurewicz.boundaryTwo_constantTriangleChain]
  rfl

private theorem SixthHurewicz.pathCube_concat_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((FirstHurewicz.singularComplex X).d 7 6).hom
        (-suspensionTwo x (FirstHurewicz.concatChain p q)) =
      (pathCubeCycle x (p.trans q)).1 - ((pathCubeCycle x p).1 + (pathCubeCycle x q).1) := by
  rw [map_neg, boundarySeven_suspensionTwo, FirstHurewicz.boundaryTwo_concatChain, map_add,
    map_sub]
  simp only [pathCubeCycle_val]
  abel

private theorem SixthHurewicz.pathCubeClass_trans {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathCubeClass x (p.trans q) = pathCubeClass x p + pathCubeClass x q := by
  unfold pathCubeClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 6 _
        _).mpr
  exact ⟨-suspensionTwo x (FirstHurewicz.concatChain p q), pathCube_concat_boundary x p q⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SixthHurewicz.productCubeChain :
    FirstHurewicz.Chains ((unitInterval) × (Fin 5 → (unitInterval))) 6 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 5 → (unitInterval)) 5
    SecondHurewicz.intervalChain FifthHurewicz.fundamentalCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SixthHurewicz.fundamentalCubeChain : FirstHurewicz.Chains (Fin 6 → (unitInterval)) 6 :=
  FirstHurewicz.inducedChain cubeCoordinates 6 productCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.suspensionOne_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 6) p)) =
      FirstHurewicz.inducedChain (cubeMap p) 6 productCubeChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural
      (GenLoop.toLoop (0 : Fin 6) p).toContinuousMap (ContinuousMap.id (Fin 5 → (unitInterval))) 5
      SecondHurewicz.intervalChain FifthHurewicz.fundamentalCubeChain
  rw [SecondHurewicz.induced_intervalChain, FirstHurewicz.inducedChain_id,
    LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 6).comp
          (FirstHurewicz.inducedChain
            ((GenLoop.toLoop (0 : Fin 6) p).toContinuousMap.prodMap
              (ContinuousMap.id (Fin 5 → (unitInterval))))
            6))
        productCubeChain =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_toLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    SixthHurewicz.cubeChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    FirstHurewicz.Chains X 6 :=
  suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 6) p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.cubeChain_eq_induced {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    cubeChain p = FirstHurewicz.inducedChain p.val 6 fundamentalCubeChain := by
  rw [cubeChain, suspensionOne_toLoop]
  change
    FirstHurewicz.inducedChain (p.val.comp cubeCoordinates) 6 productCubeChain =
      ((FirstHurewicz.inducedChain p.val 6).comp (FirstHurewicz.inducedChain cubeCoordinates 6))
        productCubeChain
  rw [FirstHurewicz.inducedChain_comp]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    SixthHurewicz.cubeCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6 :=
  pathCubeCycle x (GenLoop.toLoop (0 : Fin 6) p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem SixthHurewicz.cubeCycle_val {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) : (cubeCycle p).1 = cubeChain p :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SixthHurewicz.cubeHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) : SingularMayerVietoris.SingularHomology X 6 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
    (cubeCycle p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SixthHurewicz.cubeHomologyClass_eq_pathCubeClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    cubeHomologyClass p = pathCubeClass x (GenLoop.toLoop (0 : Fin 6) p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.cubeHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 6) X x} (h : GenLoop.Homotopic p q) :
    cubeHomologyClass p = cubeHomologyClass q :=
  pathCubeClass_homotopic x (GenLoop.homotopicTo (0 : Fin 6) h)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.toLoop_const {X : Type} [TopologicalSpace X] {x : X} :
    GenLoop.toLoop (0 : Fin 6) (GenLoop.const : GenLoop (Fin 6) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem SixthHurewicz.cubeHomologyClass_const {X : Type} [TopologicalSpace X] {x : X} :
    cubeHomologyClass (GenLoop.const : GenLoop (Fin 6) X x) = 0 := by
  rw [cubeHomologyClass_eq_pathCubeClass, toLoop_const, pathCubeClass_refl]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
public
theorem SixthHurewicz.toLoop_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 6) X x) :
    GenLoop.toLoop (0 : Fin 6) (GenLoop.transAt (0 : Fin 6) p q) =
      (GenLoop.toLoop (0 : Fin 6) p).trans (GenLoop.toLoop (0 : Fin 6) q) := by
  have h :=
    congrArg (GenLoop.toLoop (0 : Fin 6))
      (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 6)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.cubeHomologyClass_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 6) X x) :
    cubeHomologyClass (GenLoop.transAt (0 : Fin 6) p q) =
      cubeHomologyClass p + cubeHomologyClass q := by
  simp only [cubeHomologyClass_eq_pathCubeClass, toLoop_transAt, pathCubeClass_trans]

private theorem SixthHurewicz.CubeSubdivision.cubeCoordinates_boundary_right (s : (unitInterval))
    {u : Fin 5 → (unitInterval)} (hu : u ∈ Cube.boundary (Fin 5)) :
    SixthHurewicz.cubeCoordinates (s, u) ∈ Cube.boundary (Fin 6) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨i.succ, by simpa only [SixthHurewicz.cubeCoordinates_succ] using hi⟩

private def SixthHurewicz.CubeSubdivision.curryLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    GenLoop (Fin 5) C((unitInterval), X) (ContinuousMap.const (unitInterval) x) :=
  ⟨((SixthHurewicz.cubeMap p).comp ContinuousMap.prodSwap).curry,
    by
    intro u hu
    apply ContinuousMap.ext
    intro s
    exact GenLoop.boundary p _ (cubeCoordinates_boundary_right s hu)⟩

private theorem
    SixthHurewicz.CubeSubdivision.evalLeft_comp_curryLoop {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 6) X x) :
    (FourthHurewicz.CubeSubdivision.evalLeft X).comp
        ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) =
      SixthHurewicz.cubeMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.CubeSubdivision.evalLeft_crossProductEdge_curryLoop {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) (n : ℕ)
    (b : FirstHurewicz.Chains (Fin 5 → (unitInterval)) n) :
    FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) n
          SecondHurewicz.intervalChain (FirstHurewicz.inducedChain (curryLoop p).val n b)) =
      FirstHurewicz.inducedChain (SixthHurewicz.cubeMap p) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 5 → (unitInterval)) n
          SecondHurewicz.intervalChain b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval))
      (curryLoop p).val n SecondHurewicz.intervalChain b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) (n + 1)).comp
          (FirstHurewicz.inducedChain
            ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) (n + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evalLeft_comp_curryLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.CubeSubdivision.cubeChain_eq_curriedCrossProduct {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    SixthHurewicz.cubeChain p =
      FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) 6
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) 5
          SecondHurewicz.intervalChain (FifthHurewicz.cubeChain (curryLoop p))) := by
  rw [FifthHurewicz.cubeChain_eq_induced, evalLeft_crossProductEdge_curryLoop,
    SixthHurewicz.cubeChain_eq_induced, SixthHurewicz.fundamentalCubeChain]
  change
    (FirstHurewicz.inducedChain p.val 6)
        ((FirstHurewicz.inducedChain SixthHurewicz.cubeCoordinates 6)
          SixthHurewicz.productCubeChain) =
      (FirstHurewicz.inducedChain (p.val.comp SixthHurewicz.cubeCoordinates) 6)
        SixthHurewicz.productCubeChain
  rw [FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    SixthHurewicz.CubeSubdivision.intervalFiveSimplexChain {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) (e : Equiv.Perm (Fin 5)) : FirstHurewicz.Chains X 6 :=
  FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) 6
    (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) 5
      SecondHurewicz.intervalChain
      (FirstHurewicz.simplexChain C((unitInterval), X) 5
        ((curryLoop p).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.CubeSubdivision.intervalFiveSimplexChain_eq_original {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) (e : Equiv.Perm (Fin 5)) :
    intervalFiveSimplexChain p e =
      FirstHurewicz.inducedChain (SixthHurewicz.cubeMap p) 6
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 5 → (unitInterval)) 5
          SecondHurewicz.intervalChain
          (FirstHurewicz.simplexChain (Fin 5 → (unitInterval)) 5
            (HigherHurewicz.CubeTriangulation.cubeSimplex e))) := by
  rw [intervalFiveSimplexChain, ← FirstHurewicz.inducedChain_simplex,
    evalLeft_crossProductEdge_curryLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SixthHurewicz.CubeSubdivision.cubeChain_eq_sum_prisms {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 6) X x) :
    SixthHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 5),
        HigherHurewicz.CubeTriangulation.cubeOrientation e • intervalFiveSimplexChain p e := by
  rw [cubeChain_eq_curriedCrossProduct, FifthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices]
  simp only [map_sum, map_zsmul, intervalFiveSimplexChain]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SixthHurewicz.CubeSubdivision.prismCubeMap_five (e : Equiv.Perm (Fin 5)) :
    SixthHurewicz.cubeCoordinates.comp
        ((FirstHurewicz.pathSimplex Path.id).prodMap
          (HigherHurewicz.CubeTriangulation.cubeSimplex e)) =
      FourthHurewicz.CubeSubdivision.prismCubeMap e := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact SixthHurewicz.cubeCoordinates_zero _
  · change
      SixthHurewicz.cubeCoordinates
          (FirstHurewicz.pathSimplex Path.id z.1,
            HigherHurewicz.CubeTriangulation.cubeSimplex e z.2)
          j.succ =
        _
    rw [SixthHurewicz.cubeCoordinates_succ]
    rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SixthHurewicz.CubeSubdivision.intervalFiveSimplexChain_eq_prismCubeRealization {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) (e : Equiv.Perm (Fin 5)) :
    intervalFiveSimplexChain p e =
      FourthHurewicz.CubeSubdivision.prismCubeRealization p.val e 6
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 5
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 6 => j))) := by
  rw [intervalFiveSimplexChain_eq_original, SecondHurewicz.intervalChain, FirstHurewicz.pathChain,
    PeriodTorusHigherHomology.crossProductEdge_simplex,
    FourthHurewicz.CubeSubdivision.prismCubeRealization_edgeCrossProduct]
  change
    ((FirstHurewicz.inducedChain (SixthHurewicz.cubeMap p) 6).comp
          (FirstHurewicz.inducedChain
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))
            6))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  change
    FirstHurewicz.inducedChain
        (p.val.comp
          (SixthHurewicz.cubeCoordinates.comp
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))))
        6 _ =
      _
  rw [prismCubeMap_five]

private theorem SixthHurewicz.CubeSubdivision.cubeChain_eq_orientedPrismRealization {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    SixthHurewicz.cubeChain p =
      FourthHurewicz.CubeSubdivision.orientedPrismRealization p.val 6
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 5
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 6 => j))) := by
  rw [cubeChain_eq_sum_prisms, FourthHurewicz.CubeSubdivision.orientedPrismRealization_eq_sum]
  simp only [intervalFiveSimplexChain_eq_prismCubeRealization]

private theorem
    SixthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 6) X x) :
    SixthHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 6),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 6
            (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  rw [cubeChain_eq_orientedPrismRealization,
    FourthHurewicz.CubeSubdivision.orientedPrismRealization_edge_eq_standard (n := 3) p,
    FourthHurewicz.CubeSubdivision.orientedPrismRealization_standardPrism]

private theorem SixthHurewicz.sixSimplexClassOperator_cubeChain_sum {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x) :
    sixSimplexClassOperator x (cubeChain p) =
      ∑ e : Equiv.Perm (Fin 6),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          basedSixSimplexClass
            (normalizedSixSimplex x
              (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_zsmul, sixSimplexClassOperator_simplex]

private theorem SixthHurewicz.sixSimplexClassOperator_cubeChain {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x) :
    sixSimplexClassOperator x (cubeChain p) = Additive.ofMul (⟦p⟧ : π_ 6 X x) := by
  rw [sixSimplexClassOperator_cubeChain_sum]
  calc
    _ = Additive.ofMul (⟦normalizedCube x p⟧ : π_ 6 X x) := by
      simpa only [normalizedCube_simplex, basedSixSimplexClass] using
        (HigherHurewicz.NativeSubdivision.nativeCubeSubdivision_class (normalizedCube x p)
            (normalizedCube_internalBased x p)).symm
    _ = _ :=
      congrArg Additive.ofMul
        (Quotient.sound
          (show GenLoop.Homotopic (normalizedCube x p) p from
            ⟨(normalizationCubeHomotopy x p).symm⟩))

private def SixthHurewicz.basedSixSimplexChain {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) : FirstHurewicz.Chains X 6 :=
  HigherHurewicz.correctedSimplexChain 6 x τ.val

private def SixthHurewicz.basedSixSimplexCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6 :=
  HigherHurewicz.correctedSimplexCycle 5 x τ.val (basedSixSimplex_face τ)

private theorem
    SixthHurewicz.basedSixSimplex_simplexChain_sum {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) :
    (∑ e : Equiv.Perm (Fin 6),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 6
            ((basedSixSimplexLoop τ).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) =
      basedSixSimplexChain τ :=
  HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum (n := 4) τ

private def SixthHurewicz.normalizedSixSimplexCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    FirstHurewicz.Chains X 6 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6 :=
  HigherHurewicz.normalizedCycleAssignment 5 x (normalizedSixSimplex x)

@[simp]
private theorem
    SixthHurewicz.normalizedSixSimplexCycleOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (smp : FirstHurewicz.SingularSimplex X 6) :
    normalizedSixSimplexCycleOperator x (FirstHurewicz.simplexChain X 6 smp) =
      basedSixSimplexCycle (normalizedSixSimplex x smp) :=
  HigherHurewicz.normalizedCycleAssignment_simplex 5 x (normalizedSixSimplex x) smp

private theorem
    SixthHurewicz.normalizedSixSimplexCycleOperator_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
        (normalizedSixSimplexCycleOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6 c := by
  apply
    HigherHurewicz.normalizedCycleAssignment_class 5 x (normalizedSixSimplex x)
      (normalizationFiveSimplexHomotopy x) (normalizationSixSimplexHomotopy x)
      (normalizationHomotopy_face x) _ (fun _ => rfl) c
  intro smp
  ext s
  exact normalizationSixSimplexHomotopy_zero x smp s

private def
    SixthHurewicz.homotopyMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (x : X) : π_ 6 X x →* π_ 6 Y (f x)
    where
  toFun :=
    Quotient.map (SecondHurewicz.mapGenLoop f x)
      (fun _ _ h => SecondHurewicz.mapGenLoop_homotopic f x h)
  map_one' := by
    change (⟦SecondHurewicz.mapGenLoop f x GenLoop.const⟧ : π_ 6 Y (f x)) = ⟦GenLoop.const⟧
    rw [SecondHurewicz.mapGenLoop_const]
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    exact
      (congrArg
            (Quotient.map (SecondHurewicz.mapGenLoop f x)
              (fun _ _ h => SecondHurewicz.mapGenLoop_homotopic f x h))
            (HomotopyGroup.mul_spec (i := (0 : Fin 6)) (p := p) (q := q))).trans
        ((congrArg (fun r : GenLoop (Fin 6) Y (f x) => (⟦r⟧ : π_ 6 Y (f x)))
              (SecondHurewicz.mapGenLoop_transAt f x (0 : Fin 6) q p)).trans
          (HomotopyGroup.mul_spec (i := (0 : Fin 6)) (p := SecondHurewicz.mapGenLoop f x p) (q :=
              SecondHurewicz.mapGenLoop f x q)).symm)

private def SixthHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 6 X x → SingularMayerVietoris.SingularHomology X 6 :=
  Quotient.lift cubeHomologyClass (fun _ _ h => cubeHomologyClass_homotopic h)

private def SixthHurewicz.hurewiczPi6 {X : Type} [TopologicalSpace X] (x : X) :
    π_ 6 X x →* Multiplicative (SingularMayerVietoris.SingularHomology X 6)
    where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (cubeHomologyClass_const (x := x))
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ 6 X x => Multiplicative.ofAdd (hurewiczFunction x c))
            (HomotopyGroup.mul_spec (i := (0 : Fin 6)) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd (cubeHomologyClass (GenLoop.transAt (0 : Fin 6) q p)) =
        Multiplicative.ofAdd (cubeHomologyClass p + cubeHomologyClass q)
    rw [cubeHomologyClass_transAt, add_comm]

private def SixthHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 6 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 6
    where
  toFun := (hurewiczPi6 x).toAdditiveLeft
  map_add' := (hurewiczPi6 x).toAdditiveLeft.map_add
  map_smul' n a := by simpa using map_intCast_smul (hurewiczPi6 x).toAdditiveLeft ℤ ℤ n a

private theorem SixthHurewicz.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 6) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 6 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
        (cubeCycle p) :=
  rfl

private theorem SixthHurewicz.cubeChain_basedSixSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) : cubeChain (basedSixSimplexLoop τ) = basedSixSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, basedSixSimplex_simplexChain_sum]

private theorem SixthHurewicz.cubeCycle_basedSixSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) : cubeCycle (basedSixSimplexLoop τ) = basedSixSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedSixSimplexLoop τ

private theorem SixthHurewicz.hurewicz_basedSixSimplexClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) :
    hurewiczMap x (basedSixSimplexClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
        (basedSixSimplexCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
        (cubeCycle (basedSixSimplexLoop τ)) =
      _
  rw [cubeCycle_basedSixSimplexLoop]

private theorem
    SixthHurewicz.hurewiczMap_comp_sixSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    (hurewiczMap x).comp (sixSimplexClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6).comp
        (normalizedSixSimplexCycleOperator x) := by
  apply FirstHurewicz.chainMap_ext X 6
  intro smp
  simp only [LinearMap.comp_apply, sixSimplexClassOperator_simplex,
    normalizedSixSimplexCycleOperator_simplex]
  exact hurewicz_basedSixSimplexClass (normalizedSixSimplex x smp)

private theorem
    SixthHurewicz.hurewiczMap_sixSimplexClassOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6) :
    hurewiczMap x (sixSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_sixSimplexClassOperator x) c.val
  change
    hurewiczMap x (sixSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
        (normalizedSixSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedSixSimplexCycleOperator_class x c)

private def
    SixthHurewicz.hurewiczInverse {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] :
    SingularMayerVietoris.SingularHomology X 6 →ₗ[ℤ] Additive (π_ 6 X x) :=
  HigherHurewicz.singularHomologyDesc 6 (sixSimplexClassOperator x)
    (sixSimplexClassOperator_boundary x)

@[simp]
private theorem SixthHurewicz.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6 c) =
      sixSimplexClassOperator x c.val :=
  HigherHurewicz.singularHomologyDesc_cycleClass 6 _ _ c

private theorem SixthHurewicz.hurewiczMap_comp_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    (hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  HigherHurewicz.comp_singularHomologyDesc_eq_id 6 (sixSimplexClassOperator x)
    (sixSimplexClassOperator_boundary x) (hurewiczMap x)
    (hurewiczMap_sixSimplexClassOperator_cycle x)

@[simp]
private theorem SixthHurewicz.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (c : SingularMayerVietoris.SingularHomology X 6) : hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

private theorem SixthHurewicz.hurewiczInverse_hurewiczMap_mk {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x) :
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 6 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 6 X x) := by
  rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact sixSimplexClassOperator_cubeChain x p

@[simp]
private theorem SixthHurewicz.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (a : Additive (π_ 6 X x)) :
    hurewiczInverse x (hurewiczMap x a) = a := by
  change
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

private theorem SixthHurewicz.hurewiczInverse_comp_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    (hurewiczInverse x).comp (hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a

private def
    SixthHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] :
    Additive (π_ 6 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 6 :=
  LinearEquiv.ofLinearMap (hurewiczMap x) (hurewiczInverse x) (hurewiczMap_comp_hurewiczInverse x)
    (hurewiczInverse_comp_hurewiczMap x)

private def SixthHurewicz.hurewiczPi6Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] :
    π_ 6 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 6)
    where
  __ := hurewiczPi6 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv
    c := congrArg Multiplicative.ofAdd (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

private theorem
    SixthHurewicz.cubeChain_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop (Fin 6) X x) :
    FirstHurewicz.inducedChain f 6 (cubeChain p) = cubeChain (SecondHurewicz.mapGenLoop f x p) := by
  rw [cubeChain_eq_induced, cubeChain_eq_induced, SecondHurewicz.mapGenLoop_val,
    FirstHurewicz.inducedChain_comp, LinearMap.comp_apply]

private theorem
    SixthHurewicz.cubeCycle_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.ModuleHomology.mapCycles (FirstHurewicz.singularChainMap f) 6
        (cubeCycle p) =
      cubeCycle (SecondHurewicz.mapGenLoop f x p) := by
  apply Subtype.ext
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, cubeCycle_val, cubeCycle_val]
  exact cubeChain_natural f x p

private theorem SixthHurewicz.cubeHomologyClass_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.singularHomologyMap f 6 (cubeHomologyClass p) =
      cubeHomologyClass (SecondHurewicz.mapGenLoop f x p) := by
  change
    (HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap f) 6).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
          (cubeCycle p)) =
      _
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, cubeCycle_natural]
  rfl

private theorem SixthHurewicz.hurewiczFunction_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (a : π_ 6 X x) :
    SingularMayerVietoris.singularHomologyMap f 6 (hurewiczFunction x a) =
      hurewiczFunction (f x) (homotopyMap f x a) := by
  refine Quotient.inductionOn a fun p => ?_
  exact cubeHomologyClass_natural f x p

private theorem
    SixthHurewicz.hurewiczMap_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (a : Additive (π_ 6 X x)) :
    SingularMayerVietoris.singularHomologyMap f 6 (hurewiczMap x a) =
      hurewiczMap (f x) ((homotopyMap f x).toAdditive a) :=
  hurewiczFunction_natural f x a.toMul

private theorem SixthHurewicz.hurewiczLinearEquiv_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (f : C(X, Y)) (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 2 Y (f x))] [Subsingleton (π_ 3 Y (f x))]
    [Subsingleton (π_ 4 Y (f x))] [Subsingleton (π_ 5 Y (f x))] (a : Additive (π_ 6 X x)) :
    SingularMayerVietoris.singularHomologyMap f 6 (hurewiczLinearEquiv x a) =
      hurewiczLinearEquiv (f x) ((homotopyMap f x).toAdditive a) :=
  hurewiczMap_natural f x a

end Mathoverflow1973

end
