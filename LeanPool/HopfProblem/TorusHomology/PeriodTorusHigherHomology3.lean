/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1

/-!
# Hopf problem: torus homology · period torus higher homology 3

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

private theorem PeriodTorusHigherHomology.connectingMap_cycleClass
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) (c : SingularMayerVietoris.ModuleHomology.Cycle S.X₃ (n + 1)) (z₂ : S.X₂.X (n + 1))
    (hz₂ : (S.g.f (n + 1)).hom z₂ = c.1) (z₁ : SingularMayerVietoris.ModuleHomology.Cycle S.X₁ n)
    (hz₁ : (S.f.f n).hom z₁.1 = (S.X₂.d (n + 1) n).hom z₂) :
    SingularMayerVietoris.connectingMap hS n
        (SingularMayerVietoris.ModuleHomology.cycleClass S.X₃ (n + 1) c) =
      SingularMayerVietoris.ModuleHomology.cycleClass S.X₁ n z₁ := by
  have hc : (S.X₃.d (n + 1) n).hom c.1 = 0 := by
    have h := SingularMayerVietoris.ModuleHomology.cycle_condition S.X₃ (n + 1) c
    rw [Nat.add_sub_cancel] at h
    exact h
  have hnext : (ComplexShape.down ℕ).next (n + 1) = n := (ComplexShape.down ℕ).next_eq' (by simp)
  have h₃ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_eq_homologyClassOfCycle_of_next S.X₃ (n + 1) c
      n hnext hc
  have hδ := SingularMayerVietoris.connectingMap_homologyClassOfCycle hS n c.1 hc z₂ hz₂ z₁.1 hz₁
  have h₁ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_eq_homologyClassOfCycle_of_next S.X₁ n z₁
      ((ComplexShape.down ℕ).next n) rfl
      (SingularMayerVietoris.connectingMap_lift_is_cycle hS n z₂ z₁.1 hz₁ _)
  exact (congrArg (SingularMayerVietoris.connectingMap hS n) h₃).trans (hδ.trans h₁.symm)

private theorem
    PeriodTorusHigherHomology.smallConnectingMap_cycleClass {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ)
    (c :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularMayerVietoris.smallComplex U V) (n + 1))
    (z₂ : (SingularMayerVietoris.middleComplex U V).X (n + 1))
    (hz₂ : ((SingularMayerVietoris.rightMap U V).f (n + 1)).hom z₂ = c.1)
    (z₁ :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (hz₁ :
      ((SingularMayerVietoris.leftMap U V).f n).hom z₁.1 =
        ((SingularMayerVietoris.middleComplex U V).d (n + 1) n).hom z₂) :
    SingularMayerVietoris.smallConnectingMap U V n
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularMayerVietoris.smallComplex U V)
          (n + 1) c) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex (U ∩ V : Set X)) n z₁ :=
  connectingMap_cycleClass (SingularMayerVietoris.chainSequence_shortExact U V) n c z₂ hz₂ z₁ hz₁

private theorem PeriodTorusHigherHomology.connectingHomomorphism_cycleClass {X : Type}
    [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ)
    (c :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularMayerVietoris.smallComplex U V) (n + 1))
    (z₂ : (SingularMayerVietoris.middleComplex U V).X (n + 1))
    (hz₂ : ((SingularMayerVietoris.rightMap U V).f (n + 1)).hom z₂ = c.1)
    (z₁ :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (hz₁ :
      ((SingularMayerVietoris.leftMap U V).f n).hom z₁.1 =
        ((SingularMayerVietoris.middleComplex U V).d (n + 1) n).hom z₂) :
    SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) (n + 1)
          (SingularMayerVietoris.ModuleHomology.mapCycles
            (SingularMayerVietoris.smallInclusion U V) (n + 1) c)) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex (U ∩ V : Set X)) n z₁ := by
  rw [← SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  change
    SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n
        (SingularMayerVietoris.smallHomologyComparison U V (n + 1)
          (SingularMayerVietoris.ModuleHomology.cycleClass
            (SingularMayerVietoris.smallComplex U V) (n + 1) c)) =
      _
  rw [SingularMayerVietoris.connectingHomomorphism_comparison]
  exact smallConnectingMap_cycleClass U V n c z₂ hz₂ z₁ hz₁

private def PeriodTorusHigherHomology.pointCycle {X : Type} [TopologicalSpace X] (x : X) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 0 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 0
    (FirstHurewicz.simplexChain X 0 (ContinuousMap.const (FirstHurewicz.Simplex 0) x))
    (by
      have h := (FirstHurewicz.singularComplex X).shape 0 0 (by simp)
      exact
        congrArg
          (fun f =>
            f.hom
              (FirstHurewicz.simplexChain X 0 (ContinuousMap.const (FirstHurewicz.Simplex 0) x)))
          h)

@[simp]
private theorem PeriodTorusHigherHomology.pointCycle_val {X : Type} [TopologicalSpace X] (x : X) :
    (pointCycle x).1 =
      FirstHurewicz.simplexChain X 0 (ContinuousMap.const (FirstHurewicz.Simplex 0) x) :=
  rfl

private def PeriodTorusHigherHomology.pointClass {X : Type} [TopologicalSpace X] (x : X) :
    SingularMayerVietoris.SingularHomology X 0 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 0
    (pointCycle x)

@[simp]
private theorem PeriodTorusHigherHomology.mapCycles_pointCycle {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    SingularMayerVietoris.ModuleHomology.mapCycles (FirstHurewicz.singularChainMap f) 0
        (pointCycle x) =
      pointCycle (f x) := by
  apply Subtype.ext
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, pointCycle_val, pointCycle_val]
  change
    FirstHurewicz.inducedChain f 0
        (FirstHurewicz.simplexChain X 0 (ContinuousMap.const (FirstHurewicz.Simplex 0) x)) =
      _
  rw [FirstHurewicz.inducedChain_simplex]
  apply congrArg (FirstHurewicz.simplexChain Y 0)
  apply ContinuousMap.ext
  intro t
  rfl

@[simp]
private theorem
    PeriodTorusHigherHomology.singularHomologyMap_pointClass {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    SingularMayerVietoris.singularHomologyMap f 0 (pointClass x) = pointClass (f x) := by
  change
    (HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap f) 0).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 0
          (pointCycle x)) =
      _
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, mapCycles_pointCycle]
  rfl

private def PeriodTorusHigherHomology.pointCycleLift_mo1973_4686 {X : Type} [TopologicalSpace X]
    (x : X) : ModuleCat.of ℤ ℤ ⟶ (FirstHurewicz.singularComplex X).cycles 0 :=
  (FirstHurewicz.singularComplex X).liftCycles
    ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      (FirstHurewicz.simplexIndex X 0 (ContinuousMap.const (FirstHurewicz.Simplex 0) x)))
    0 (by simp) (by simp)

private theorem PeriodTorusHigherHomology.pointClass_eq_pointCycleLift_mo1973_4687 {X : Type}
    [TopologicalSpace X] (x : X) :
    pointClass x =
      (FirstHurewicz.singularComplex X).homologyπ 0 ((pointCycleLift_mo1973_4686 x).hom 1) := by
  rw [pointClass, SingularMayerVietoris.ModuleHomology.cycleClass_eq_homologyClassOfCycle,
    SingularMayerVietoris.homologyClassOfCycle]
  apply congrArg ((FirstHurewicz.singularComplex X).homologyπ 0).hom
  apply
    (ModuleCat.mono_iff_injective ((FirstHurewicz.singularComplex X).iCycles 0)).mp inferInstance
  have h₁ :=
    (FirstHurewicz.singularComplex X).i_cyclesMk (pointCycle x).1 (0 - 1)
      (SingularMayerVietoris.ModuleHomology.next_nat 0)
      (SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 0
        (pointCycle x))
  have h₂ :=
    congrArg (fun f => f.hom 1)
      ((FirstHurewicz.singularComplex X).liftCycles_i
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (FirstHurewicz.simplexIndex X 0 (ContinuousMap.const (FirstHurewicz.Simplex 0) x)))
        0 (by simp) (by simp))
  exact h₁.trans h₂.symm

@[simp]
private theorem PeriodTorusHigherHomology.pointClass_augmentation {X : Type} [TopologicalSpace X]
    (x : X) : ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ)).hom (pointClass x) = 1 := by
  rw [pointClass_eq_pointCycleLift_mo1973_4687]
  exact
    congrArg (fun f => f.hom 1)
      ((TopCat.toSSet.obj (TopCat.of X)).liftCycles_ιChainComplex_homologyπ_homology₀ε
        (ModuleCat.of ℤ ℤ)
        (FirstHurewicz.simplexIndex X 0 (ContinuousMap.const (FirstHurewicz.Simplex 0) x)))

@[simp]
private theorem PeriodTorusHigherHomology.connectedHomologyZeroEquiv_pointClass {X : Type}
    [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    connectedHomologyZeroEquiv X (pointClass x) = 1 :=
  pointClass_augmentation x

private theorem PeriodTorusHigherHomology.eq_zsmul_pointClass {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (a : SingularMayerVietoris.SingularHomology X 0) :
    a = connectedHomologyZeroEquiv X a • pointClass x := by
  apply (connectedHomologyZeroEquiv X).injective
  rw [map_zsmul, connectedHomologyZeroEquiv_pointClass, zsmul_eq_mul, mul_one]
  simp

private theorem PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) (a : SingularMayerVietoris.SingularHomology X 0) :
    connectedHomologyZeroEquiv Y (SingularMayerVietoris.singularHomologyMap f 0 a) =
      connectedHomologyZeroEquiv X a := by
  let x : X := Classical.arbitrary X
  calc
    connectedHomologyZeroEquiv Y (SingularMayerVietoris.singularHomologyMap f 0 a) =
        connectedHomologyZeroEquiv Y
          (SingularMayerVietoris.singularHomologyMap f 0
            (connectedHomologyZeroEquiv X a • pointClass x)) :=
      congrArg
        (fun b => connectedHomologyZeroEquiv Y (SingularMayerVietoris.singularHomologyMap f 0 b))
        (eq_zsmul_pointClass x a)
    _ = connectedHomologyZeroEquiv X a := by
      rw [map_zsmul, map_zsmul, singularHomologyMap_pointClass,
        connectedHomologyZeroEquiv_pointClass, zsmul_eq_mul, mul_one]
      simp

private def PeriodTorusHigherHomology.trivialFirstEquiv_mo1973_4693 (A B : Type*) [AddCommGroup A]
    [AddCommGroup B] [Module ℤ B] [Subsingleton A] : (A × B) ≃ₗ[ℤ] B :=
  ({    toFun a := a.2
        invFun b := (0, b)
        left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
        right_inv _ := rfl
        map_add' _ _ := rfl } : (A × B) ≃+ B).toIntLinearEquiv

/-- The canonical linear equivalence from first homology of the circle to the integers. -/
public
def PeriodTorusHigherHomology.circleHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.CircleTopology.Circle)
        1 ≃ₗ[ℤ]
      ℤ := by
  letI := point_homology_subsingleton 1 (by decide)
  exact
    ((homeomorphHomologyEquiv
              (Homeomorph.prodUnique (PeriodTorusHigherHomology.CircleTopology.Circle) Unit).symm
              1).trans
          (circleProductHomologyEquiv Unit 0)).trans
      ((trivialFirstEquiv_mo1973_4693 (SingularMayerVietoris.SingularHomology Unit 1)
            (SingularMayerVietoris.SingularHomology Unit 0)).trans
        pointHomologyZeroEquiv)

private theorem PeriodTorusHigherHomology.circleHomologyOneEquiv_apply
    (a :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.CircleTopology.Circle)
        1) :
    circleHomologyOneEquiv a =
      pointHomologyZeroEquiv
        (circleBoundary Unit 0
          (homeomorphHomologyEquiv
            (Homeomorph.prodUnique (PeriodTorusHigherHomology.CircleTopology.Circle) Unit).symm 1
            a)) :=
  rfl

private theorem PeriodTorusHigherHomology.circle_homology_subsingleton (n : ℕ) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.CircleTopology.Circle)
        (n + 2)) := by
  let := point_homology_subsingleton (n + 2) (Nat.succ_ne_zero _)
  let := point_homology_subsingleton (n + 1) (Nat.succ_ne_zero _)
  exact
    ((homeomorphHomologyEquiv
            (Homeomorph.prodUnique (PeriodTorusHigherHomology.CircleTopology.Circle) Unit).symm
            (n + 2)).trans
        (circleProductHomologyEquiv Unit (n + 1))).injective.subsingleton

end Mathoverflow1973

end
