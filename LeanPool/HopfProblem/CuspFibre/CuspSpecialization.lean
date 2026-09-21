/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.CuspFibre.CuspCentralHomology3
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.Foundations.InvariantSubsetQuotient
import all LeanPool.HopfProblem.Toric.ToricSpace2
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.CuspFibre.CuspPositiveRetraction
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Toric.CuspHoneycombHexagon
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology3

/-!
# Hopf problem: cusp fibre · cusp specialization

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

private def
    CuspControlledRetraction.Concatenation.connectingHomotopy {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P K : C(unitInterval × X, Y)) (hjoin : ∀ x, K (0, x) = P (1, x)) :
    (slice P 1).Homotopy (slice K 1)
    where
  toContinuousMap := K
  map_zero_left := hjoin
  map_one_left _ := rfl

private def CuspControlledRetraction.Concatenation.map {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P K : C(unitInterval × X, Y)) (hjoin : ∀ x, K (0, x) = P (1, x)) :
    C(unitInterval × X, Y) :=
  ((asHomotopy P).trans (connectingHomotopy P K hjoin)).toContinuousMap

@[simp]
private theorem CuspControlledRetraction.Concatenation.map_zero {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P K : C(unitInterval × X, Y)) (hjoin : ∀ x, K (0, x) = P (1, x))
    (x : X) : CuspControlledRetraction.Concatenation.map P K hjoin (0, x) = P (0, x) :=
  ContinuousMap.Homotopy.apply_zero _ x

@[simp]
private theorem CuspControlledRetraction.Concatenation.map_one {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P K : C(unitInterval × X, Y)) (hjoin : ∀ x, K (0, x) = P (1, x))
    (x : X) : CuspControlledRetraction.Concatenation.map P K hjoin (1, x) = K (1, x) :=
  ContinuousMap.Homotopy.apply_one _ x

private theorem
    CuspControlledRetraction.Concatenation.map_property {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P K : C(unitInterval × X, Y)) (hjoin : ∀ x, K (0, x) = P (1, x))
    (R : C(X, Y) → Prop) (hP : ∀ s, R (slice P s)) (hK : ∀ s, R (slice K s)) (s : unitInterval) :
    R (slice (CuspControlledRetraction.Concatenation.map P K hjoin) s) := by
  let F : (slice P 0).HomotopyWith (slice P 1) R :=
    { toHomotopy := asHomotopy P
      prop' := hP }
  let G : (slice P 1).HomotopyWith (slice K 1) R :=
    { toHomotopy := connectingHomotopy P K hjoin
      prop' := hK }
  exact (F.trans G).prop s

private theorem
    CuspControlledRetraction.exists_positive_modification (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (hηε : η < ε) (hη : 0 ≤ η) (ρ : ℝ) (hρ : 0 < ρ)
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hzero : ∀ q, P (0, q) = q)
    (hfix :
      ∀ s (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (hequiv :
      ∀ s v q,
        P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
          CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (hmono : ∀ s q, positiveHeight (P (s, q)) ≤ positiveHeight q) :
    ∃ Q : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η),
      (∀ q, Q (0, q) = q) ∧
        (∀ s (q : ToricSpace.ClosedPositiveTube η),
            ToricSpace.time (q.1 : ToricSpace.Space) = 0 → Q (s, q) = q) ∧
          (∀ q : ToricSpace.ClosedPositiveTube η,
              ToricSpace.time ((Q (1, q)).1 : ToricSpace.Space) = 0) ∧
            (∀ s v q,
                Q (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
                  CuspPositive.closedPositiveTranslate C₀ η v (Q (s, q))) ∧
              (∀ s q, positiveHeight (Q (s, q)) ≤ positiveHeight q) ∧
                (∀ q,
                    positiveHeight q = ρ →
                      Q (1, q) =
                        CuspPositiveRetraction.positiveCentralInclusion η hη
                          (CuspHoneycomb.honeycombHomeomorph C₀
                            (normalizedPosition C₀ (q.1 : ToricSpace.Space)))) ∧
                  (∀ q, positiveHeight q ≤ ρ / 2 → Q (1, q) = P (1, q)) := by
  let K := centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ
  have hjoin : ∀ q, K (0, q) = P (1, q) := centralInterpolation_zero P hone C₀ hε1 hR hηε hη ρ hρ
  let Q := Concatenation.map P K hjoin
  let R : C(ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η) → Prop := fun f =>
    (∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → f q = q) ∧
      (∀ v q,
          f (CuspPositive.closedPositiveTranslate C₀ η v q) =
            CuspPositive.closedPositiveTranslate C₀ η v (f q)) ∧
        (∀ q, positiveHeight (f q) ≤ positiveHeight q)
  have hQP (s : unitInterval) : R (Concatenation.slice Q s) := by
    apply Concatenation.map_property P K hjoin R
    · intro t
      exact ⟨hfix t, hequiv t, hmono t⟩
    · intro t
      exact
        ⟨centralInterpolation_fixed P hone C₀ hε1 hR hηε hη ρ hρ hfix t,
          centralInterpolation_equivariant P hone C₀ hε1 hR hηε hη ρ hρ hequiv t,
          centralInterpolation_nonincreasing P hone C₀ hε1 hR hηε hη ρ hρ t⟩
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    exact (Concatenation.map_zero P K hjoin q).trans (hzero q)
  · intro s q hq
    exact (hQP s).1 q hq
  · intro q
    change ToricSpace.time (((Concatenation.map P K hjoin) (1, q)).1 : ToricSpace.Space) = 0
    rw [Concatenation.map_one]
    exact centralInterpolation_central P hone C₀ hε1 hR hηε hη ρ hρ 1 q
  · intro s v q
    exact (hQP s).2.1 v q
  · intro s q
    exact (hQP s).2.2 q
  · intro q hq
    exact
      (Concatenation.map_one P K hjoin q).trans
        (centralInterpolation_one_of_height_eq P hone C₀ hε1 hR hηε hη ρ hρ q hq)
  · intro q hq
    exact
      (Concatenation.map_one P K hjoin q).trans
        (centralInterpolation_eq_endpoint_of_height_le_half P hone C₀ hε1 hR hηε hη ρ hρ 1 q hq)

private theorem CuspControlledRetraction.exists_positive_controlled_deformation_below
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < ε ∧
          ∀ (η : ℝ) (hη : 0 < η),
            η ≤ η₀ →
              ∀ ρ : ℝ,
                0 < ρ →
                  ρ ≤ η →
                    ∃ P :
                      C(unitInterval × ToricSpace.ClosedPositiveTube η,
                        ToricSpace.ClosedPositiveTube η),
                      (∀ q, P (0, q) = q) ∧
                        (∀ s (q : ToricSpace.ClosedPositiveTube η),
                            ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q) ∧
                          (∀ q : ToricSpace.ClosedPositiveTube η,
                              ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0) ∧
                            (∀ s v q,
                                P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
                                  CuspPositive.closedPositiveTranslate C₀ η v (P (s, q))) ∧
                              (∀ s q,
                                  ‖ToricSpace.time ((P (s, q)).1 : ToricSpace.Space)‖ ≤
                                    ‖ToricSpace.time (q.1 : ToricSpace.Space)‖) ∧
                                (∀ q,
                                  ‖ToricSpace.time (q.1 : ToricSpace.Space)‖ = ρ →
                                    P (1, q) =
                                      CuspPositiveRetraction.positiveCentralInclusion η hη.le
                                        (CuspHoneycomb.honeycombHomeomorph C₀
                                          (normalizedPosition C₀ (q.1 : ToricSpace.Space)))) := by
  obtain ⟨η₀, hη₀, hη₀ε, hP⟩ :=
    CuspPositiveRetraction.exists_positive_closed_deformation_below C₀ ε hε hε1 hR
  refine ⟨η₀, hη₀, hη₀ε, ?_⟩
  intro η hη hηη₀ ρ hρ _hρη
  obtain ⟨P, hzero, hfix, hone, hequiv, hmono⟩ := hP η hη hηη₀
  obtain ⟨Q, hQzero, hQfix, hQone, hQequiv, hQmono, hQend, _hQnear⟩ :=
    exists_positive_modification C₀ hε1 hR (hηη₀.trans_lt hη₀ε) hη.le ρ hρ P hzero hfix hone
      hequiv hmono
  exact ⟨Q, hQzero, hQfix, hQone, hQequiv, hQmono, hQend⟩

private def CuspControlledRetraction.polarDeformation {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q) :
    C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η) :=
  ⟨fun p => CuspRetraction.polarSpread P p.1 p.2, CuspRetraction.polarSpread_continuous P hfix⟩

private theorem CuspControlledRetraction.polarDeformation_closedPolarMap {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (φ : ToricSpace.CompactTorus) (q : ToricSpace.ClosedPositiveTube η) :
    polarDeformation P hfix (s, ToricSpace.closedPolarMap η (φ, q)) =
      ToricSpace.closedPolarMap η (φ, P (s, q)) :=
  CuspRetraction.polarSpread_closedPolarMap P hfix s (φ, q)

private theorem CuspControlledRetraction.polarDeformation_properties (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (hzero : ∀ q : ToricSpace.ClosedPositiveTube η, P (0, q) = q)
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (hequiv :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η),
        P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
          CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (hmono :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ‖ToricSpace.time ((P (s, q)).1 : ToricSpace.Space)‖ ≤
          ‖ToricSpace.time (q.1 : ToricSpace.Space)‖) :
    (∀ x, polarDeformation P hfix (0, x) = x) ∧
      (∀ s (x : CuspRetraction.ClosedTube η),
          ToricSpace.time (x : ToricSpace.Space) = 0 → polarDeformation P hfix (s, x) = x) ∧
        (∀ x, ToricSpace.time (polarDeformation P hfix (1, x) : ToricSpace.Space) = 0) ∧
          (∀ s v x,
              polarDeformation P hfix (s, CuspRetraction.closedTranslate (fun _ => C₀) η v x) =
                CuspRetraction.closedTranslate (fun _ => C₀) η v
                  (polarDeformation P hfix (s, x))) ∧
            (∀ s φ x,
                polarDeformation P hfix (s, CuspRetraction.closedCompactAction η φ x) =
                  CuspRetraction.closedCompactAction η φ (polarDeformation P hfix (s, x))) ∧
              (∀ s (u : Fin 2 → ℂˣ),
                  (∀ i, ‖(u i : ℂ)‖ = 1) →
                    ∀ x,
                      polarDeformation P hfix (s, CuspRetraction.closedFibreAction η u x) =
                        CuspRetraction.closedFibreAction η u (polarDeformation P hfix (s, x))) ∧
                (∀ s x,
                  ‖ToricSpace.time (polarDeformation P hfix (s, x) : ToricSpace.Space)‖ ≤
                    ‖ToricSpace.time (x : ToricSpace.Space)‖) :=
  ⟨CuspRetraction.polarSpread_zero P hfix hzero, CuspRetraction.polarSpread_fixed P hfix,
    CuspRetraction.polarSpread_one_central P hfix hone,
    CuspRetraction.polarSpread_frozen_equivariant C₀ P hfix hequiv,
    CuspRetraction.polarSpread_compactTorus_equivariant P hfix,
    CuspRetraction.polarSpread_fibre_torus_equivariant P hfix,
    CuspRetraction.polarSpread_norm_time_le P hfix hmono⟩

private abbrev CuspControlledRetraction.PuncturedPositiveTube (η : ℝ) :=
  { q : ToricSpace.ClosedPositiveTube η // ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0 }

private abbrev CuspControlledRetraction.PuncturedClosedTube (η : ℝ) :=
  { x : CuspRetraction.ClosedTube η // ToricSpace.time (x : ToricSpace.Space) ≠ 0 }

private theorem CuspControlledRetraction.puncturedPolarMap_mem_iff (η : ℝ)
    (p : ToricSpace.CompactTorus × ToricSpace.ClosedPositiveTube η) :
    ToricSpace.closedPolarMap η p ∈
        {x : CuspRetraction.ClosedTube η | ToricSpace.time (x : ToricSpace.Space) ≠ 0} ↔
      p.2 ∈
        {q : ToricSpace.ClosedPositiveTube η | ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0} := by
  change
    ToricSpace.time (ToricSpace.compactTorusAction p.1 (p.2.1 : ToricSpace.Space)) ≠ 0 ↔
      ToricSpace.time (p.2.1 : ToricSpace.Space) ≠ 0
  rw [← norm_ne_zero_iff, ToricSpace.norm_time_compactTorusAction, norm_ne_zero_iff]

private def CuspControlledRetraction.puncturedPolarMap (η : ℝ) :
    ToricSpace.CompactTorus × PuncturedPositiveTube η → PuncturedClosedTube η :=
  ProductRestriction.productRestriction (ToricSpace.closedPolarMap η)
    {q : ToricSpace.ClosedPositiveTube η | ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0}
    {x : CuspRetraction.ClosedTube η | ToricSpace.time (x : ToricSpace.Space) ≠ 0}
    (puncturedPolarMap_mem_iff η)

@[simp]
private theorem CuspControlledRetraction.puncturedPolarMap_closed_coe (η : ℝ)
    (p : ToricSpace.CompactTorus × PuncturedPositiveTube η) :
    (puncturedPolarMap η p : CuspRetraction.ClosedTube η) =
      ToricSpace.closedPolarMap η (p.1, p.2.1) :=
  rfl

private theorem CuspControlledRetraction.norm_time_puncturedPolarMap (η : ℝ)
    (p : ToricSpace.CompactTorus × PuncturedPositiveTube η) :
    ‖ToricSpace.time ((puncturedPolarMap η p).1 : ToricSpace.Space)‖ =
      ‖ToricSpace.time (p.2.1.1 : ToricSpace.Space)‖ :=
  ToricSpace.norm_time_compactTorusAction p.1 (p.2.1.1 : ToricSpace.Space)

private theorem CuspControlledRetraction.puncturedPolarMap_continuous (η : ℝ) :
    Continuous (puncturedPolarMap η) :=
  ProductRestriction.productRestriction_continuous _ _ _ _
    (ToricSpace.closedPolarMap_continuous η)

private theorem CuspControlledRetraction.puncturedPolarMap_isClosedMap (η : ℝ) :
    IsClosedMap (puncturedPolarMap η) :=
  ProductRestriction.productRestriction_isClosedMap _ _ _ _
    (ToricSpace.closedPolarMap_isClosedMap η)

private theorem CuspControlledRetraction.puncturedPolarMap_surjective (η : ℝ) :
    Function.Surjective (puncturedPolarMap η) :=
  ProductRestriction.productRestriction_surjective _ _ _ _
    (ToricSpace.closedPolarMap_surjective η)

private theorem CuspControlledRetraction.puncturedPolarMap_injective (η : ℝ) :
    Function.Injective (puncturedPolarMap η) := by
  rintro ⟨u, q⟩ ⟨v, r⟩ h
  have hclosed : ToricSpace.closedPolarMap η (u, q.1) = ToricSpace.closedPolarMap η (v, r.1) :=
    congrArg Subtype.val h
  have hqr : q = r := by
    apply Subtype.ext
    simpa only [ToricSpace.closedModulusRetraction_closedPolarMap] using
      congrArg (ToricSpace.closedModulusRetraction η) hclosed
  subst r
  have huv : u = v :=
    ToricSpace.compactTorusAction_injective_of_time_ne_zero q.property
      (congrArg (fun x : CuspRetraction.ClosedTube η => (x : ToricSpace.Space)) hclosed)
  exact Prod.ext huv rfl

private theorem CuspControlledRetraction.puncturedPolarMap_bijective (η : ℝ) :
    Function.Bijective (puncturedPolarMap η) :=
  ⟨puncturedPolarMap_injective η, puncturedPolarMap_surjective η⟩

private def CuspControlledRetraction.puncturedPolarHomeomorph (η : ℝ) :
    (ToricSpace.CompactTorus × PuncturedPositiveTube η) ≃ₜ PuncturedClosedTube η :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (puncturedPolarMap η) (puncturedPolarMap_bijective η))
    (puncturedPolarMap_continuous η) (puncturedPolarMap_isClosedMap η)

@[simp]
private theorem CuspControlledRetraction.puncturedPolarHomeomorph_symm_map (η : ℝ)
    (p : ToricSpace.CompactTorus × PuncturedPositiveTube η) :
    (puncturedPolarHomeomorph η).symm (puncturedPolarMap η p) = p :=
  (puncturedPolarHomeomorph η).symm_apply_apply p

@[simp]
private theorem
    CuspControlledRetraction.puncturedPolarMap_symm (η : ℝ) (x : PuncturedClosedTube η) :
    puncturedPolarMap η ((puncturedPolarHomeomorph η).symm x) = x :=
  (puncturedPolarHomeomorph η).apply_symm_apply x

@[simp]
private theorem CuspControlledRetraction.puncturedPolarHomeomorph_symm_positive_coe (η : ℝ)
    (x : PuncturedClosedTube η) :
    ((puncturedPolarHomeomorph η).symm x).2.1 = ToricSpace.closedModulusRetraction η x.1 := by
  have h :=
    congrArg (fun y : PuncturedClosedTube η => ToricSpace.closedModulusRetraction η y.1)
      (puncturedPolarMap_symm η x)
  simpa only [puncturedPolarMap_closed_coe,
    ToricSpace.closedModulusRetraction_closedPolarMap] using h

private def CuspControlledRetraction.centralCompactPolar
    (p : ToricSpace.CompactTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    CuspRetraction.CentralFibre :=
  ⟨ToricSpace.compactTorusAction p.1 (p.2.1 : ToricSpace.Space), by
    simp only [ToricSpace.compactTorusAction, ToricSpace.time_torusAction, p.2.2,
      MulZeroClass.mul_zero]⟩

private theorem CuspControlledRetraction.centralCompactPolar_continuous :
    Continuous centralCompactPolar :=
  (ToricSpace.compactTorusAction_continuous.comp
        (continuous_fst.prodMk
          ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd))).subtype_mk
    _

@[simp]
private theorem CuspControlledRetraction.centralModulus_centralCompactPolar
    (p : ToricSpace.CompactTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    CuspCollapse.centralModulus (centralCompactPolar p) = p.2 := by
  apply Subtype.ext
  apply Subtype.ext
  change
    ToricSpace.modulus (ToricSpace.compactTorusAction p.1 (p.2.1 : ToricSpace.Space)) =
      (p.2.1 : ToricSpace.Space)
  rw [ToricSpace.modulus_compactTorusAction]
  exact p.2.1.2

private def
    CuspControlledRetraction.prescribedPositiveCollapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (q : PuncturedPositiveTube η) : CuspPositiveRetraction.PositiveCentralFibre :=
  CuspHoneycomb.honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1.1 : ToricSpace.Space))

private def CuspControlledRetraction.prescribedPolarCollapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (p : ToricSpace.CompactTorus × PuncturedPositiveTube η) : CuspRetraction.CentralFibre :=
  centralCompactPolar (p.1, prescribedPositiveCollapse C₀ η p.2)

private def CuspControlledRetraction.prescribedCollapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (x : PuncturedClosedTube η) : CuspRetraction.CentralFibre :=
  prescribedPolarCollapse C₀ η ((puncturedPolarHomeomorph η).symm x)

@[simp]
private theorem CuspControlledRetraction.prescribedCollapse_puncturedPolarMap
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (p : ToricSpace.CompactTorus × PuncturedPositiveTube η) :
    prescribedCollapse C₀ η (puncturedPolarMap η p) = prescribedPolarCollapse C₀ η p := by
  unfold prescribedCollapse
  rw [puncturedPolarHomeomorph_symm_map]

private theorem
    CuspControlledRetraction.prescribedCollapse_polar (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (u : ToricSpace.CompactTorus) (q : PuncturedPositiveTube η) :
    (prescribedCollapse C₀ η (puncturedPolarMap η (u, q)) : ToricSpace.Space) =
      ToricSpace.compactTorusAction u
        ((CuspHoneycomb.honeycombHomeomorph C₀
              (normalizedPosition C₀ (q.1.1 : ToricSpace.Space))).1 :
          ToricSpace.Space) := by
  rw [prescribedCollapse_puncturedPolarMap]
  rfl

@[simp]
private theorem CuspControlledRetraction.prescribedCollapse_modulus (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (x : PuncturedClosedTube η) :
    CuspCollapse.centralModulus (prescribedCollapse C₀ η x) =
      prescribedPositiveCollapse C₀ η ((puncturedPolarHomeomorph η).symm x).2 :=
  centralModulus_centralCompactPolar _

private theorem CuspControlledRetraction.normalizedPosition_puncturedPositive_continuous
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) :
    Continuous
      (fun q : PuncturedPositiveTube η => normalizedPosition C₀ (q.1.1 : ToricSpace.Space)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  exact
    (normalizedPosition_closedPositive_continuousAt C₀ hε1 hR hηε q.2).comp
      continuous_subtype_val.continuousAt

private theorem CuspControlledRetraction.prescribedPositiveCollapse_continuous
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) :
    Continuous (prescribedPositiveCollapse C₀ η) :=
  (CuspHoneycomb.honeycombHomeomorph C₀).continuous.comp
    (normalizedPosition_puncturedPositive_continuous C₀ hε1 hR hηε)

private theorem CuspControlledRetraction.prescribedPolarCollapse_continuous
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) :
    Continuous (prescribedPolarCollapse C₀ η) :=
  centralCompactPolar_continuous.comp
    (continuous_fst.prodMk
      ((prescribedPositiveCollapse_continuous C₀ hε1 hR hηε).comp continuous_snd))

private theorem
    CuspControlledRetraction.prescribedCollapse_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (hηε : η < ε) : Continuous (prescribedCollapse C₀ η) :=
  (prescribedPolarCollapse_continuous C₀ hε1 hR hηε).comp
    (puncturedPolarHomeomorph η).symm.continuous

private theorem CuspControlledRetraction.polarDeformation_prescribedCollapse_of_puncturedEndpoint
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (ρ : ℝ) (hη : 0 ≤ η)
    (hEnd :
      ∀ q : PuncturedPositiveTube η,
        ‖ToricSpace.time (q.1.1 : ToricSpace.Space)‖ = ρ →
          P (1, q.1) =
            CuspPositiveRetraction.positiveCentralInclusion η hη
              (prescribedPositiveCollapse C₀ η q))
    (x : PuncturedClosedTube η) (hx : ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ) :
    polarDeformation P hfix (1, x.1) =
      CuspRetraction.centralIntoClosedTube η hη (prescribedCollapse C₀ η x) := by
  obtain ⟨⟨φ, q⟩, rfl⟩ := puncturedPolarMap_surjective η x
  have hq : ‖ToricSpace.time (q.1.1 : ToricSpace.Space)‖ = ρ := by
    simpa only [norm_time_puncturedPolarMap] using hx
  apply Subtype.ext
  change
    (polarDeformation P hfix (1, ToricSpace.closedPolarMap η (φ, q.1)) : ToricSpace.Space) =
      (prescribedCollapse C₀ η (puncturedPolarMap η (φ, q)) : ToricSpace.Space)
  rw [polarDeformation_closedPolarMap, hEnd q hq, prescribedCollapse_polar]
  rfl

private theorem CuspControlledRetraction.polarDeformation_prescribedCollapse
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (ρ : ℝ) (hη : 0 ≤ η)
    (hEnd :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ‖ToricSpace.time (q.1 : ToricSpace.Space)‖ = ρ →
          P (1, q) =
            CuspPositiveRetraction.positiveCentralInclusion η hη
              (CuspHoneycomb.honeycombHomeomorph C₀
                (normalizedPosition C₀ (q.1 : ToricSpace.Space))))
    (x : PuncturedClosedTube η) (hx : ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ) :
    polarDeformation P hfix (1, x.1) =
      CuspRetraction.centralIntoClosedTube η hη (prescribedCollapse C₀ η x) :=
  polarDeformation_prescribedCollapse_of_puncturedEndpoint C₀ P hfix ρ hη
    (fun q hq => hEnd q.1 hq) x hx

private theorem CuspControlledRetraction.exists_frozen_controlled_deformation_below
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < ε ∧
          ∀ (η : ℝ) (hη : 0 < η),
            η ≤ η₀ →
              ∀ ρ : ℝ,
                0 < ρ →
                  ρ ≤ η →
                    ∃ H :
                      C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η),
                      (∀ x, H (0, x) = x) ∧
                        (∀ s (x : CuspRetraction.ClosedTube η),
                            ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x) ∧
                          (∀ x, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) ∧
                            (∀ s v x,
                                H (s, CuspRetraction.closedTranslate (fun _ => C₀) η v x) =
                                  CuspRetraction.closedTranslate (fun _ => C₀) η v (H (s, x))) ∧
                              (∀ s φ x,
                                  H (s, CuspRetraction.closedCompactAction η φ x) =
                                    CuspRetraction.closedCompactAction η φ (H (s, x))) ∧
                                (∀ s (u : Fin 2 → ℂˣ),
                                    (∀ i, ‖(u i : ℂ)‖ = 1) →
                                      ∀ x,
                                        H (s, CuspRetraction.closedFibreAction η u x) =
                                          CuspRetraction.closedFibreAction η u (H (s, x))) ∧
                                  (∀ s x,
                                      ‖ToricSpace.time (H (s, x) : ToricSpace.Space)‖ ≤
                                        ‖ToricSpace.time (x : ToricSpace.Space)‖) ∧
                                    (∀ x : PuncturedClosedTube η,
                                      ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ →
                                        H (1, x.1) =
                                          CuspRetraction.centralIntoClosedTube η hη.le
                                            (prescribedCollapse C₀ η x)) := by
  obtain ⟨η₀, hη₀, hη₀ε, hP⟩ := exists_positive_controlled_deformation_below C₀ ε hε hε1 hR
  refine ⟨η₀, hη₀, hη₀ε, ?_⟩
  intro η hη hηη₀ ρ hρ hρη
  obtain ⟨P, hzero, hfix, hone, hequiv, hmono, hEnd⟩ := hP η hη hηη₀ ρ hρ hρη
  obtain ⟨hHzero, hHfix, hHone, hHequiv, hHcompact, hHfibre, hHmono⟩ :=
    polarDeformation_properties C₀ P hfix hzero hone hequiv hmono
  refine ⟨polarDeformation P hfix, hHzero, hHfix, hHone, hHequiv, hHcompact, hHfibre, hHmono, ?_⟩
  exact polarDeformation_prescribedCollapse C₀ P hfix ρ hη.le hEnd

private theorem CuspControlledRetraction.closedHomotopyDescentRetraction_endpoint_of_eq
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε)
    (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hHequiv :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : CuspRetraction.ClosedTube η),
        H (s, CuspRetraction.closedTranslate C η v x) =
          CuspRetraction.closedTranslate C η v (H (s, x)))
    (hCanalytic : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hone : ∀ x : CuspRetraction.ClosedTube η, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0)
    (hη : 0 ≤ η) (x : CuspRetraction.ClosedTube η) (y : CuspRetraction.CentralFibre)
    (hEndx : H (1, x) = CuspRetraction.centralIntoClosedTube η hη y) :
    (CuspRetraction.closedHomotopyDescentRetraction C hηε H hHequiv hCanalytic hone
          (CuspRetraction.closedQuotientMap C hηε x) :
        CuspQuotient.QuotientSpace C ε) =
      (CuspRetraction.closedQuotientMap C hηε (CuspRetraction.centralIntoClosedTube η hη y) :
        CuspQuotient.QuotientSpace C ε) := by
  change
    (CuspRetraction.closedHomotopyDescent C hηε H 1 (CuspRetraction.closedQuotientMap C hηε x) :
        CuspQuotient.QuotientSpace C ε) =
      _
  rw [CuspRetraction.closedHomotopyDescent_closedQuotientMap C hηε H hHequiv, hEndx]

private theorem CuspControlledRetraction.closedFrozenStraightening_symm_fixed
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hCcont : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (x : CuspRetraction.ClosedTube η)
    (hx : ToricSpace.time (x : ToricSpace.Space) = 0) :
    ((CuspPositiveRetraction.closedFrozenStraightening C hε hε1 hCcont hRC hRD hηε)).symm x = x :=
  by
  apply ((CuspPositiveRetraction.closedFrozenStraightening C hε hε1 hCcont hRC hRD hηε)).injective
  rw [((CuspPositiveRetraction.closedFrozenStraightening C hε hε1 hCcont hRC hRD
        hηε)).apply_symm_apply,
    CuspPositiveRetraction.closedFrozenStraightening_fixed C hε hε1 hCcont hRC hRD hηε x hx]

private theorem CuspControlledRetraction.straightenedHomotopy_endpoint_of_eq
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hCcont : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hη : 0 ≤ η) (x : CuspRetraction.ClosedTube η) (y : CuspRetraction.CentralFibre)
    (he :
      H (1, (CuspPositiveRetraction.closedFrozenStraightening C hε hε1 hCcont hRC hRD hηε) x) =
        CuspRetraction.centralIntoClosedTube η hη y) :
    (CuspPositiveRetraction.straightenedHomotopy C hε hε1 hCcont hRC hRD hηε H) (1, x) =
      CuspRetraction.centralIntoClosedTube η hη y := by
  rw [CuspPositiveRetraction.straightenedHomotopy_apply, he]
  exact
    closedFrozenStraightening_symm_fixed C hε hε1 hCcont hRC hRD hηε
      (CuspRetraction.centralIntoClosedTube η hη y) y.2

private def
    CuspControlledRetraction.puncturedStraightening (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (x : PuncturedClosedTube η) : PuncturedClosedTube η :=
  ⟨CuspRetraction.closedTubeChangeTwist C (CuspRetraction.frozen C) η x.1,
    by
    change
      ToricSpace.time
          (CuspRetraction.changeTwist C (CuspRetraction.frozen C) (x.1 : ToricSpace.Space)) ≠
        0
    rw [CuspRetraction.time_changeTwist]
    exact x.2⟩

private theorem
    CuspControlledRetraction.puncturedStraightening_base (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (x : PuncturedClosedTube η) :
    ToricSpace.time ((puncturedStraightening C η x).1 : ToricSpace.Space) =
      ToricSpace.time (x.1 : ToricSpace.Space) :=
  CuspRetraction.time_changeTwist C (CuspRetraction.frozen C) (x.1 : ToricSpace.Space)

private def
    CuspControlledRetraction.straightenedPrescribedCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) : PuncturedClosedTube η → CuspRetraction.CentralFibre :=
  prescribedCollapse (C 0) η ∘ puncturedStraightening C η

private theorem CuspControlledRetraction.puncturedStraightening_continuous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hηε : η < ε) : Continuous (puncturedStraightening C η) := by
  apply Continuous.subtype_mk
  exact
    (CuspRetraction.closedTubeChangeTwist_continuous C (CuspRetraction.frozen C) hε hε1 hC
          (fun _ _ => continuousOn_const) rfl hRC hηε).comp
      continuous_subtype_val

private theorem CuspControlledRetraction.straightenedPrescribedCollapse_continuous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) : Continuous (straightenedPrescribedCollapse C η) :=
  (prescribedCollapse_continuous (C 0) hε1 (CuspPositive.smallDrift_positiveTwist (C 0) hRD)
        hηε).comp
    (puncturedStraightening_continuous C hε hε1 hC hRC hηε)

private theorem CuspControlledRetraction.straightenedHomotopy_prescribed_endpoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hη : 0 ≤ η) {ρ : ℝ}
    (hEnd :
      ∀ x : PuncturedClosedTube η,
        ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ →
          H (1, x.1) = CuspRetraction.centralIntoClosedTube η hη (prescribedCollapse (C 0) η x))
    (x : PuncturedClosedTube η) (hx : ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ) :
    CuspPositiveRetraction.straightenedHomotopy C hε hε1 hC hRC hRD hηε H (1, x.1) =
      CuspRetraction.centralIntoClosedTube η hη (straightenedPrescribedCollapse C η x) := by
  apply
    straightenedHomotopy_endpoint_of_eq C hε hε1 hC hRC hRD hηε H hη x.1
      (straightenedPrescribedCollapse C η x)
  exact
    hEnd (puncturedStraightening C η x)
      ((congrArg Norm.norm (puncturedStraightening_base C η x)).trans hx)

private theorem CuspControlledRetraction.exists_closed_tube_controlled_deformation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ (η : ℝ) (hη : 0 < η),
              η ≤ η₀ →
                ∀ ρ : ℝ,
                  0 < ρ →
                    ρ ≤ η →
                      ∃ H :
                        C(unitInterval × CuspRetraction.ClosedTube η,
                          CuspRetraction.ClosedTube η),
                        (∀ x, H (0, x) = x) ∧
                          (∀ s (x : CuspRetraction.ClosedTube η),
                              ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x) ∧
                            (∀ x, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) ∧
                              (∀ s v x,
                                  H (s, CuspRetraction.closedTranslate C η v x) =
                                    CuspRetraction.closedTranslate C η v (H (s, x))) ∧
                                (∀ s (u : Fin 2 → ℂˣ),
                                    (∀ i, ‖(u i : ℂ)‖ = 1) →
                                      ∀ x,
                                        H (s, CuspRetraction.closedFibreAction η u x) =
                                          CuspRetraction.closedFibreAction η u (H (s, x))) ∧
                                  (∀ s x,
                                      ‖ToricSpace.time (H (s, x) : ToricSpace.Space)‖ ≤
                                        ‖ToricSpace.time (x : ToricSpace.Space)‖) ∧
                                    (∀ x : PuncturedClosedTube η,
                                      ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ →
                                        H (1, x.1) =
                                          CuspRetraction.centralIntoClosedTube η hη.le
                                            (straightenedPrescribedCollapse C η x)) := by
  obtain ⟨ε, hε, hεr, hε1, hRC, hRD⟩ := CuspRetraction.exists_common_frozen_radius C hr hC
  have hCε : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε) := fun i j =>
    (hC i j).mono (Metric.ball_subset_ball hεr.le)
  have hRP : ToricSpace.SmallDrift (CuspPositive.positiveTwist (C 0)) ε :=
    CuspPositive.smallDrift_positiveTwist (C 0) hRD
  obtain ⟨η₀, hη₀, hη₀ε, hH⟩ := exists_frozen_controlled_deformation_below (C 0) ε hε hε1 hRP
  refine ⟨η₀, hη₀, hη₀ε.trans hεr, hη₀ε.trans hε1, ?_⟩
  intro η hη hηη₀ ρ hρ hρη
  have hηε : η < ε := hηη₀.trans_lt hη₀ε
  obtain ⟨H, hzero, hfix, hone, hequiv, _hcompact, hfibre, hmono, hEnd⟩ := hH η hη hηη₀ ρ hρ hρη
  refine
    ⟨CuspPositiveRetraction.straightenedHomotopy C hε hε1 hCε hRC hRD hηε H,
      CuspPositiveRetraction.straightenedHomotopy_zero C hε hε1 hCε hRC hRD hηε H hzero,
      CuspPositiveRetraction.straightenedHomotopy_fixed C hε hε1 hCε hRC hRD hηε H hfix,
      CuspPositiveRetraction.straightenedHomotopy_one_central C hε hε1 hCε hRC hRD hηε H hone,
      CuspPositiveRetraction.straightenedHomotopy_equivariant C hε hε1 hCε hRC hRD hηε H hequiv,
      CuspPositiveRetraction.straightenedHomotopy_fibre_torus_equivariant C hε hε1 hCε hRC hRD hηε
        H hfibre,
      CuspPositiveRetraction.straightenedHomotopy_norm_time_le C hε hε1 hCε hRC hRD hηε H hmono,
      ?_⟩
  exact straightenedHomotopy_prescribed_endpoint C hε hε1 hCε hRC hRD hηε H hη.le hEnd

private theorem
    CuspControlledRetraction.exists_closed_quotient_controlled_strongDeformationRetraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ (η : ℝ) (hη : 0 < η),
              η ≤ η₀ →
                ∀ ρ : ℝ,
                  0 < ρ →
                    ρ ≤ η →
                      ∃ R :
                        C(CuspRetraction.ClosedQuotient C r η,
                          CuspRetraction.QuotientCentralFibre C r),
                        R.comp (CuspRetraction.quotientCentralIntoClosed C r η hη.le) =
                            ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r) ∧
                          ∃ H :
                            (ContinuousMap.id (CuspRetraction.ClosedQuotient C r η)).HomotopyRel
                              ((CuspRetraction.quotientCentralIntoClosed C r η hη.le).comp R)
                              {q : CuspRetraction.ClosedQuotient C r η |
                                CuspQuotient.projection C r q = 0},
                            (∀ s q,
                                ‖CuspQuotient.projection C r (H (s, q))‖ ≤
                                  ‖CuspQuotient.projection C r q‖) ∧
                              (∀ (hηr : η < r) (x : PuncturedClosedTube η),
                                ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ →
                                  R (CuspRetraction.closedQuotientMap C hηr x.1) =
                                    CuspCollapse.centralProject C r hr
                                      (straightenedPrescribedCollapse C η x)) := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hH⟩ :=
    exists_closed_tube_controlled_deformation C hr (fun i j => (hC i j).continuousOn)
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀ ρ hρ hρη
  have hηr : η < r := hηη₀.trans_lt hη₀r
  obtain ⟨H, hzero, hfix, hone, hequiv, _hfibre, hmono, hEnd⟩ := hH η hη hηη₀ ρ hρ hρη
  refine
    ⟨CuspRetraction.closedHomotopyDescentRetraction C hηr H hequiv hC hone,
      CuspRetraction.closedHomotopyDescentRetraction_comp_inclusion C hηr H hequiv hC hfix hone
        hη.le,
      CuspRetraction.closedHomotopyDescentHomotopyRel C hηr H hequiv hC hzero hfix hone hη.le,
      CuspRetraction.closedHomotopyDescent_norm_nonincrease C hηr H hequiv hmono, ?_⟩
  intro hηr' x hx
  apply Subtype.ext
  exact
    closedHomotopyDescentRetraction_endpoint_of_eq C hηr H hequiv hC hone hη.le x.1
      (straightenedPrescribedCollapse C η x) (hEnd x hx)

private abbrev CuspControlledRetraction.ToricLevel (η : ℝ) (t : ℂ) :=
  { x : CuspRetraction.ClosedTube η // ToricSpace.time (x : ToricSpace.Space) = t }

private abbrev CuspControlledRetraction.QuotientLevel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r η : ℝ)
    (t : ℂ) :=
  { q : CuspRetraction.ClosedQuotient C r η // CuspQuotient.projection C r q = t }

private noncomputable def
    CuspControlledRetraction.levelProjection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} (hηr : η < r) (t : ℂ) (x : ToricLevel η t) : QuotientLevel C r η t :=
  ⟨CuspRetraction.closedQuotientMap C hηr x.1, x.2⟩

private theorem
    CuspControlledRetraction.levelProjection_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} (hηr : η < r) (t : ℂ) : Function.Surjective (levelProjection C hηr t) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := CuspRetraction.closedQuotientMap_surjective C hηr q
  exact ⟨⟨x, hq⟩, rfl⟩

private theorem CuspControlledRetraction.levelProjection_isOpenQuotientMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r η : ℝ} (hηr : η < r) (t : ℂ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    IsOpenQuotientMap (levelProjection C hηr t) :=
  (CuspRetraction.closedQuotientMap_isOpenQuotientMap C hηr hC).restrictPreimage
    {q : CuspRetraction.ClosedQuotient C r η | CuspQuotient.projection C r q = t}

private theorem
    CuspControlledRetraction.levelProjection_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} (hηr : η < r) (t : ℂ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Topology.IsQuotientMap (levelProjection C hηr t) :=
  (levelProjection_isOpenQuotientMap C hηr t hC).isQuotientMap

private noncomputable def CuspControlledRetraction.levelTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (t : ℂ) (v : Fin 2 → ℤ) (x : ToricLevel η t) : ToricLevel η t :=
  ⟨CuspRetraction.closedTranslate C η v x.1,
    by
    change ToricSpace.time (ToricSpace.twistedTranslate C v (x.1 : ToricSpace.Space)) = t
    rw [ToricSpace.time_twistedTranslate]
    exact x.2⟩

private theorem CuspControlledRetraction.levelProjection_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} (hηr : η < r) (t : ℂ) (x y : ToricLevel η t) :
    levelProjection C hηr t x = levelProjection C hηr t y ↔
      ∃ v : Fin 2 → ℤ, CuspRetraction.closedTranslate C η v y.1 = x.1 := by
  constructor
  · intro hxy
    have hq :=
      congrArg (fun q : QuotientLevel C r η t => (q : CuspRetraction.ClosedQuotient C r η)) hxy
    obtain ⟨v, hv⟩ := (CuspRetraction.closedQuotientMap_eq_iff C hηr x.1 y.1).mp hq
    exact ⟨v, Subtype.ext hv⟩
  · rintro ⟨v, hv⟩
    apply Subtype.ext
    apply (CuspRetraction.closedQuotientMap_eq_iff C hηr x.1 y.1).mpr
    exact ⟨v, congrArg (fun z : CuspRetraction.ClosedTube η => (z : ToricSpace.Space)) hv⟩

private theorem CuspControlledRetraction.levelProjection_eq_iff_levelTranslate
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r η : ℝ} (hηr : η < r) (t : ℂ) (x y : ToricLevel η t) :
    levelProjection C hηr t x = levelProjection C hηr t y ↔
      ∃ v : Fin 2 → ℤ, levelTranslate C η t v y = x := by
  constructor
  · intro hxy
    obtain ⟨v, hv⟩ := (levelProjection_eq_iff C hηr t x y).mp hxy
    exact ⟨v, Subtype.ext hv⟩
  · rintro ⟨v, hv⟩
    apply (levelProjection_eq_iff C hηr t x y).mpr
    exact ⟨v, congrArg (fun z : ToricLevel η t => (z : CuspRetraction.ClosedTube η)) hv⟩

private theorem CuspControlledRetraction.levelProjection_fibre_compatible_of_invariant
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r η : ℝ} {Z : Type*} (hηr : η < r) (t : ℂ)
    (f : ToricLevel η t → Z)
    (hinv : ∀ (v : Fin 2 → ℤ) (x : ToricLevel η t), f (levelTranslate C η t v x) = f x) :
    ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y := by
  intro x y hxy
  obtain ⟨v, hv⟩ := (levelProjection_eq_iff_levelTranslate C hηr t x y).mp hxy
  rw [← hv]
  exact hinv v y

private noncomputable def CuspControlledRetraction.levelDescend (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} {Z : Type*} (hηr : η < r) (t : ℂ) (f : ToricLevel η t → Z) :
    QuotientLevel C r η t → Z :=
  CuspHoneycombHexagon.CommonFibres.descend (levelProjection C hηr t) f
    (levelProjection_surjective C hηr t)

private theorem
    CuspControlledRetraction.levelDescend_levelProjection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} {Z : Type*} (hηr : η < r) (t : ℂ) (f : ToricLevel η t → Z)
    (hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y)
    (x : ToricLevel η t) : levelDescend C hηr t f (levelProjection C hηr t x) = f x :=
  CuspHoneycombHexagon.CommonFibres.descend_apply (levelProjection C hηr t) f
    (levelProjection_surjective C hηr t) hcompat x

private theorem
    CuspControlledRetraction.levelDescend_unique (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r η : ℝ}
    {Z : Type*} (hηr : η < r) (t : ℂ) (f : ToricLevel η t → Z)
    (hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y)
    (g : QuotientLevel C r η t → Z) (hg : ∀ x, g (levelProjection C hηr t x) = f x) :
    g = levelDescend C hηr t f := by
  funext q
  obtain ⟨x, rfl⟩ := levelProjection_surjective C hηr t q
  rw [hg, levelDescend_levelProjection C hηr t f hcompat]

private theorem CuspControlledRetraction.levelDescend_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} {Z : Type*} [TopologicalSpace Z] (hηr : η < r) (t : ℂ) (f : ToricLevel η t → Z)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hf : Continuous f)
    (hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y) :
    Continuous (levelDescend C hηr t f) :=
  CuspHoneycombHexagon.CommonFibres.descend_continuous (levelProjection C hηr t) f
    (levelProjection_surjective C hηr t) (levelProjection_isQuotientMap C hηr t hC) hf hcompat

private abbrev
    CuspControlledRetraction.ActualQuotientFibre (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (t : ℂ) :=
  { q : CuspQuotient.QuotientSpace C r // CuspQuotient.projection C r q = t }

private def CuspControlledRetraction.quotientLevelFibreHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r η : ℝ) (t : ℂ) (htη : ‖t‖ ≤ η) : QuotientLevel C r η t ≃ₜ ActualQuotientFibre C r t
    where
  toFun q := ⟨q.1.1, q.2⟩
  invFun q := ⟨⟨q.1, by rw [q.2]; exact htη⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk _

private def
    CuspControlledRetraction.levelToPunctured (η : ℝ) (t : ℂ) (ht : t ≠ 0) (x : ToricLevel η t) :
    PuncturedClosedTube η :=
  ⟨x.1, fun hx => ht (x.2.symm.trans hx)⟩

private def
    CuspControlledRetraction.prescribedFibreUpstairs (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (η : ℝ) (t : ℂ) (ht : t ≠ 0) (x : ToricLevel η t) :
    CuspRetraction.QuotientCentralFibre C r :=
  CuspCollapse.centralProject C r hr
    (straightenedPrescribedCollapse C η (levelToPunctured η t ht x))

private def
    CuspControlledRetraction.prescribedFibreCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) {η : ℝ} (hηr : η < r) (t : ℂ) (ht : t ≠ 0) :
    QuotientLevel C r η t → CuspRetraction.QuotientCentralFibre C r :=
  levelDescend C hηr t (prescribedFibreUpstairs C r hr η t ht)

private def
    CuspControlledRetraction.prescribedActualFibreCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) {η : ℝ} (hηr : η < r) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η) :
    ActualQuotientFibre C r t → CuspRetraction.QuotientCentralFibre C r :=
  prescribedFibreCollapse C r hr hηr t ht ∘ (quotientLevelFibreHomeomorph C r η t htη).symm

private theorem CuspControlledRetraction.prescribedFibreCollapse_eq_of_endpoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) {η : ℝ} (hηr : η < r) (t : ℂ)
    (ht : t ≠ 0)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (hEnd :
      ∀ x : PuncturedClosedTube η,
        ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ‖t‖ →
          R (CuspRetraction.closedQuotientMap C hηr x.1) =
            CuspCollapse.centralProject C r hr (straightenedPrescribedCollapse C η x)) :
    (fun q : QuotientLevel C r η t => R q.1) = prescribedFibreCollapse C r hr hηr t ht := by
  let f := prescribedFibreUpstairs C r hr η t ht
  let g := fun q : QuotientLevel C r η t => R q.1
  have hg (x : ToricLevel η t) : g (levelProjection C hηr t x) = f x :=
    hEnd (levelToPunctured η t ht x) (congrArg Norm.norm x.2)
  have hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y := by
    intro x y hxy
    exact (hg x).symm.trans ((congrArg g hxy).trans (hg y))
  exact levelDescend_unique C hηr t f hcompat g hg

private theorem CuspControlledRetraction.prescribedFibreCollapse_levelProjection_of_endpoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) {η : ℝ} (hηr : η < r) (t : ℂ)
    (ht : t ≠ 0)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (hEnd :
      ∀ x : PuncturedClosedTube η,
        ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ‖t‖ →
          R (CuspRetraction.closedQuotientMap C hηr x.1) =
            CuspCollapse.centralProject C r hr (straightenedPrescribedCollapse C η x))
    (x : ToricLevel η t) :
    prescribedFibreCollapse C r hr hηr t ht (levelProjection C hηr t x) =
      prescribedFibreUpstairs C r hr η t ht x := by
  rw [← prescribedFibreCollapse_eq_of_endpoint C r hr hηr t ht R hEnd]
  exact hEnd (levelToPunctured η t ht x) (congrArg Norm.norm x.2)

private theorem CuspControlledRetraction.exists_controlled_actual_fibre_retraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ (η : ℝ) (hη : 0 < η),
              η ≤ η₀ →
                ∀ (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η),
                  ∃ R :
                    C(CuspRetraction.ClosedQuotient C r η,
                      CuspRetraction.QuotientCentralFibre C r),
                    R.comp (CuspRetraction.quotientCentralIntoClosed C r η hη.le) =
                        ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r) ∧
                      ∃ H :
                        (ContinuousMap.id (CuspRetraction.ClosedQuotient C r η)).HomotopyRel
                          ((CuspRetraction.quotientCentralIntoClosed C r η hη.le).comp R)
                          {q : CuspRetraction.ClosedQuotient C r η |
                            CuspQuotient.projection C r q = 0},
                        (∀ s q,
                            ‖CuspQuotient.projection C r (H (s, q))‖ ≤
                              ‖CuspQuotient.projection C r q‖) ∧
                          ∀ hηr : η < r,
                            Continuous (prescribedActualFibreCollapse C r hr hηr t ht htη) ∧
                              (∀ q : ActualQuotientFibre C r t,
                                  R ((quotientLevelFibreHomeomorph C r η t htη).symm q).1 =
                                    prescribedActualFibreCollapse C r hr hηr t ht htη q) ∧
                                (∀ x : ToricLevel η t,
                                  prescribedFibreCollapse C r hr hηr t ht
                                      (levelProjection C hηr t x) =
                                    prescribedFibreUpstairs C r hr η t ht x) := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hR⟩ :=
    exists_closed_quotient_controlled_strongDeformationRetraction C hr hC
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀ t ht htη
  obtain ⟨R, hRinc, H, hmono, hEnd⟩ := hR η hη hηη₀ ‖t‖ (norm_pos_iff.mpr ht) htη
  refine ⟨R, hRinc, H, hmono, ?_⟩
  intro hηr
  have he := prescribedFibreCollapse_eq_of_endpoint C r hr hηr t ht R (hEnd hηr)
  refine ⟨?_, ?_, ?_⟩
  · unfold prescribedActualFibreCollapse
    rw [← he]
    exact
      (R.continuous.comp continuous_subtype_val).comp
        (quotientLevelFibreHomeomorph C r η t htη).symm.continuous
  · intro q
    exact congrFun he ((quotientLevelFibreHomeomorph C r η t htη).symm q)
  · exact prescribedFibreCollapse_levelProjection_of_endpoint C r hr hηr t ht R (hEnd hηr)

private def CuspCentralHomology.fibreIntoOpen (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (t : ℂ)
    (htδ : ‖t‖ < δ) : C(CuspControlledRetraction.ActualQuotientFibre C r t, OpenQuotient C r δ)
    where
  toFun q := ⟨q.1, by rw [q.2]; exact htδ⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

private def
    CuspCentralHomology.openLevelFibreHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ)
    (t : ℂ) (htδ : ‖t‖ < δ) :
    { q : OpenQuotient C r δ // CuspQuotient.projection C r q = t } ≃ₜ
      CuspControlledRetraction.ActualQuotientFibre C r t
    where
  toFun q := ⟨q.1.1, q.2⟩
  invFun q := ⟨fibreIntoOpen C r δ t htδ q, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (fibreIntoOpen C r δ t htδ).continuous

private def
    CuspCentralHomology.fibreRadiusHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (t : ℂ)
    (hδr : δ ≤ r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (htδ : ‖t‖ < δ) :
    CuspControlledRetraction.ActualQuotientFibre C δ t ≃ₜ
      CuspControlledRetraction.ActualQuotientFibre C r t :=
  ((openQuotientRadiusHomeomorph C hδr hC).subtype (p := fun q =>
        CuspQuotient.projection C δ q = t) (q := fun q : OpenQuotient C r δ =>
        CuspQuotient.projection C r q = t)
        (fun q => by rw [openQuotientRadiusHomeomorph_projection])).trans
    (openLevelFibreHomeomorph C r δ t htδ)

private def CuspCentralHomology.centralRadiusHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ)
    (hδr : δ ≤ r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ) :
    CuspRetraction.QuotientCentralFibre C δ ≃ₜ CuspRetraction.QuotientCentralFibre C r :=
  fibreRadiusHomeomorph C r δ 0 hδr hC (by simpa only [norm_zero] using hδ)

private def CuspCentralHomology.centralSingularH2Equiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2 ≃ₗ[ℤ]
      (Fin 4 → ℤ) := by
  let δ : ℝ := Classical.choose (CuspQuotient.exists_admissible_radius C hr hC)
  have hs :
    0 < δ ∧
      δ < r ∧
        δ < 1 ∧
          ToricSpace.SmallDrift C δ ∧
            ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    Classical.choose_spec (CuspQuotient.exists_admissible_radius C hr hC)
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (centralRadiusHomeomorph C r δ hs.2.1.le hC hs.1).symm 2).trans
      (centralSingularH2Equiv_of_admissible C δ hs.1 hs.2.2.1 hs.2.2.2.2 hs.2.2.2.1)

private def CuspCentralHomology.centralSingularH3Equiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 3 ≃ₗ[ℤ]
      (Fin 2 → ℤ) := by
  let δ : ℝ := Classical.choose (CuspQuotient.exists_admissible_radius C hr hC)
  have hs :
    0 < δ ∧
      δ < r ∧
        δ < 1 ∧
          ToricSpace.SmallDrift C δ ∧
            ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    Classical.choose_spec (CuspQuotient.exists_admissible_radius C hr hC)
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (centralRadiusHomeomorph C r δ hs.2.1.le hC hs.1).symm 3).trans
      (centralSingularH3Equiv_of_admissible C δ hs.1 hs.2.2.1 hs.2.2.2.2 hs.2.2.2.1)

private theorem
    CuspCentralHomology.centralSingularH2_free (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2) :=
  Module.Free.of_equiv (centralSingularH2Equiv C r hr hC).symm

private theorem
    CuspCentralHomology.centralSingularH3_free (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 3) :=
  Module.Free.of_equiv (centralSingularH3Equiv C r hr hC).symm

private theorem
    CuspCentralHomology.centralSingularH2_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2) :=
  Module.Finite.of_surjective (centralSingularH2Equiv C r hr hC).symm.toLinearMap
    (centralSingularH2Equiv C r hr hC).symm.surjective

private theorem
    CuspCentralHomology.centralSingularH3_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 3) :=
  Module.Finite.of_surjective (centralSingularH3Equiv C r hr hC).symm.toLinearMap
    (centralSingularH3Equiv C r hr hC).symm.surjective

private theorem
    CuspCentralHomology.centralSingularH2_finrank (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2) =
      4 := by
  rw [(centralSingularH2Equiv C r hr hC).finrank_eq]
  exact Module.finrank_fin_fun ℤ

private theorem
    CuspCentralHomology.centralSingularH3_finrank (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 3) =
      2 := by
  rw [(centralSingularH3Equiv C r hr hC).finrank_eq]
  exact Module.finrank_fin_fun ℤ

private def
    CuspCentralHomology.centralSingularH4Equiv_of_admissible (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε) 4 ≃ₗ[ℤ] ℤ := by
  letI := outerRegion_homology_subsingleton C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num) 1
  letI := innerRegion_homology_subsingleton C ε hε hε1 hC hR 1
  letI := outerRegion_homology_subsingleton C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num) 0
  letI := innerRegion_homology_subsingleton C ε hε hε1 hC hR 0
  exact
    (coverConnectingEquivOfVanishing (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε)
          (outerRegion_isOpen C ε hε hε1 hC hR (1 / 2)) (innerRegion_isOpen C ε hε hε1 hC hR)
          (outerRegion_union_innerRegion C ε hε (1 / 2) (by norm_num)) 3).trans
      (overlapRegionHomologyThreeEquiv C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num))

private theorem CuspCentralHomology.centralSingularHomology_subsingleton_of_admissible
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε)
        (n + 5)) := by
  let :=
    outerRegion_homology_subsingleton C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num) (n + 2)
  let := innerRegion_homology_subsingleton C ε hε hε1 hC hR (n + 2)
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        ((outerRegion C ε hε (1 / 2)) ∩ (innerRegion C ε hε) :
          Set (CuspRetraction.QuotientCentralFibre C ε))
        (n + 4)) :=
    overlapRegion_homology_subsingleton C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num) n
  exact
    coverHomology_subsingleton_of_vanishing (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε)
      (outerRegion_isOpen C ε hε hε1 hC hR (1 / 2)) (innerRegion_isOpen C ε hε hε1 hC hR)
      (outerRegion_union_innerRegion C ε hε (1 / 2) (by norm_num)) (n + 4)

private def CuspCentralHomology.centralSingularH4Equiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 4 ≃ₗ[ℤ] ℤ := by
  let δ : ℝ := Classical.choose (CuspQuotient.exists_admissible_radius C hr hC)
  have hs :
    0 < δ ∧
      δ < r ∧
        δ < 1 ∧
          ToricSpace.SmallDrift C δ ∧
            ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    Classical.choose_spec (CuspQuotient.exists_admissible_radius C hr hC)
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (centralRadiusHomeomorph C r δ hs.2.1.le hC hs.1).symm 4).trans
      (centralSingularH4Equiv_of_admissible C δ hs.1 hs.2.2.1 hs.2.2.2.2 hs.2.2.2.1)

private theorem CuspCentralHomology.centralSingularHomology_subsingleton
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r)
        (n + 5)) := by
  obtain ⟨δ, hδ, hδr, hδ1, hR, hCδ⟩ := CuspQuotient.exists_admissible_radius C hr hC
  let := centralSingularHomology_subsingleton_of_admissible C δ hδ hδ1 hCδ hR n
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (centralRadiusHomeomorph C r δ hδr.le hC hδ).symm (n + 5)).injective.subsingleton

private theorem CuspCentralHomology.centralSingularHomology_subsingleton_of_four_lt
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) {n : ℕ} (hn : 4 < n) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n) := by
  have he : (n - 5) + 5 = n := Nat.sub_add_cancel (by omega)
  rw [← he]
  exact centralSingularHomology_subsingleton C r hr hC (n - 5)

private def
    CuspCentralHomology.centralSingularHomologyHigherEquivZero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) (n + 5) ≃ₗ[ℤ]
      (Fin 0 → ℤ) := by
  letI := centralSingularHomology_subsingleton C r hr hC n
  exact LinearEquiv.ofSubsingleton _ _

private theorem
    CuspCentralHomology.centralSingularH4_free (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 4) :=
  Module.Free.of_equiv (centralSingularH4Equiv C r hr hC).symm

private theorem
    CuspCentralHomology.centralSingularH4_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 4) :=
  Module.Finite.of_surjective (centralSingularH4Equiv C r hr hC).symm.toLinearMap
    (centralSingularH4Equiv C r hr hC).symm.surjective

private theorem
    CuspCentralHomology.centralSingularH4_finrank (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 4) =
      1 := by
  rw [(centralSingularH4Equiv C r hr hC).finrank_eq]
  simp

private def CuspCentralHomology.centralBetti : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 2
  | 4 => 1
  | _ => 0

private def
    CuspCentralHomology.centralSingularHomologyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n ≃ₗ[ℤ]
      (Fin (centralBetti n) → ℤ) :=
  match n with
  | 0 => (centralSingularH0Equiv C r hr).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | 1 => centralSingularH1Equiv C r hr hC
  | 2 => centralSingularH2Equiv C r hr hC
  | 3 => centralSingularH3Equiv C r hr hC
  | 4 => (centralSingularH4Equiv C r hr hC).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | n + 5 => centralSingularHomologyHigherEquivZero C r hr hC n

private theorem CuspCentralHomology.centralSingularHomology_free (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n) :=
  Module.Free.of_equiv (centralSingularHomologyEquiv C r hr hC n).symm


private theorem
    CuspCentralHomology.centralSingularHomology_finrank (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n) =
      centralBetti n := by
  rw [(centralSingularHomologyEquiv C r hr hC n).finrank_eq]
  exact Module.finrank_fin_fun ℤ


private def
    CuspCentralHomology.centralSingularEulerCharacteristic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) : ℤ :=
  ∑ i : Fin 5,
    (-1 : ℤ) ^ (i : ℕ) *
      (Module.finrank ℤ
          (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) i) :
        ℤ)


private abbrev CuspSpecialization.ToricFibre (t : ℂ) :=
  { x : ToricSpace.Space // ToricSpace.time x = t }

private abbrev CuspSpecialization.PositiveFibre (ρ : ℝ) :=
  { q : ToricSpace.PositivePart // ToricSpace.time (q : ToricSpace.Space) = (ρ : ℂ) }

@[simp]
private theorem CuspSpecialization.time_positiveFibre (ρ : ℝ) (q : PositiveFibre ρ) :
    ToricSpace.time (q.1 : ToricSpace.Space) = (ρ : ℂ) :=
  q.2

private theorem
    CuspSpecialization.norm_time_positiveFibre (ρ : ℝ) (hρ : 0 ≤ ρ) (q : PositiveFibre ρ) :
    ‖ToricSpace.time (q.1 : ToricSpace.Space)‖ = ρ := by rw [q.2, Complex.norm_of_nonneg hρ]

private def
    CuspSpecialization.positiveFibreInclusion (ρ : ℝ) : C(PositiveFibre ρ, ToricSpace.Space) :=
  ⟨fun q => (q.1 : ToricSpace.Space), continuous_subtype_val.comp continuous_subtype_val⟩

private def CuspSpecialization.toricFibreLevelHomeomorph (η : ℝ) (t : ℂ) (htη : ‖t‖ ≤ η) :
    ToricFibre t ≃ₜ CuspControlledRetraction.ToricLevel η t
    where
  toFun x := ⟨⟨(x : ToricSpace.Space), by rw [x.2]; exact htη⟩, x.2⟩
  invFun x := ⟨(x.1 : ToricSpace.Space), x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private theorem CuspSpecialization.positiveFibre_isClosed (ρ : ℝ) :
    IsClosed {q : ToricSpace.PositivePart | ToricSpace.time (q : ToricSpace.Space) = (ρ : ℂ)} :=
  isClosed_eq (ToricSpace.time_holomorphic.continuous.comp continuous_subtype_val)
    continuous_const

private theorem CuspSpecialization.positiveFibreVal_isClosedEmbedding (ρ : ℝ) :
    Topology.IsClosedEmbedding (fun q : PositiveFibre ρ => (q.1 : ToricSpace.Space)) :=
  ToricSpace.positivePart_isClosed.isClosedEmbedding_subtypeVal.comp
    (positiveFibre_isClosed ρ).isClosedEmbedding_subtypeVal

private def CuspSpecialization.positiveFibrePolarMap (ρ : ℝ)
    (p : ToricSpace.CompactFibreTorus × PositiveFibre ρ) : ToricFibre (ρ : ℂ) :=
  ⟨ToricSpace.compactFibreAction p.1 (p.2.1 : ToricSpace.Space), by
    rw [ToricSpace.time_compactFibreAction, p.2.2]⟩

@[simp]
private theorem CuspSpecialization.positiveFibrePolarMap_coe (ρ : ℝ)
    (p : ToricSpace.CompactFibreTorus × PositiveFibre ρ) :
    (positiveFibrePolarMap ρ p : ToricSpace.Space) =
      ToricSpace.compactFibreAction p.1 (p.2.1 : ToricSpace.Space) :=
  rfl

private theorem CuspSpecialization.positiveFibrePolarMap_continuous (ρ : ℝ) :
    Continuous (positiveFibrePolarMap ρ) :=
  (ToricSpace.compactFibreAction_continuous.comp
        (continuous_fst.prodMk
          ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd))).subtype_mk
    _

private theorem CuspSpecialization.modulus_positiveFibrePolarMap (ρ : ℝ)
    (p : ToricSpace.CompactFibreTorus × PositiveFibre ρ) :
    ToricSpace.modulus (positiveFibrePolarMap ρ p : ToricSpace.Space) =
      (p.2.1 : ToricSpace.Space) := by
  rw [positiveFibrePolarMap_coe, ToricSpace.modulus_compactFibreAction]
  exact p.2.1.2

private def CuspSpecialization.positiveFibreModulus (ρ : ℝ) (hρ : 0 ≤ ρ) (x : ToricFibre (ρ : ℂ)) :
    PositiveFibre ρ :=
  ⟨ToricSpace.modulusRetraction (x : ToricSpace.Space), by
    rw [ToricSpace.modulusRetraction_coe, ToricSpace.time_modulus, x.2,
      Complex.norm_of_nonneg hρ]⟩

@[simp]
private theorem CuspSpecialization.positiveFibreModulus_polarMap (ρ : ℝ) (hρ : 0 ≤ ρ)
    (p : ToricSpace.CompactFibreTorus × PositiveFibre ρ) :
    positiveFibreModulus ρ hρ (positiveFibrePolarMap ρ p) = p.2 :=
  Subtype.ext (Subtype.ext (modulus_positiveFibrePolarMap ρ p))

private theorem CuspSpecialization.compactFibrePhase_injective :
    Function.Injective ToricSpace.compactFibrePhase := by
  intro u v huv
  funext i
  fin_cases i
  · exact congrFun huv 0
  · exact congrFun huv 1

private theorem
    CuspSpecialization.compactFibreAction_injective_of_time_ne_zero {x : ToricSpace.Space}
    (hx : ToricSpace.time x ≠ 0) :
    Function.Injective
      (fun u : ToricSpace.CompactFibreTorus => ToricSpace.compactFibreAction u x) := by
  intro u v huv
  apply compactFibrePhase_injective
  apply ToricSpace.compactTorusAction_injective_of_time_ne_zero hx
  simpa only [← ToricSpace.compactFibreAction_eq_compact] using huv

private theorem CuspSpecialization.positiveFibrePolarMap_injective (ρ : ℝ) (hρ : 0 < ρ) :
    Function.Injective (positiveFibrePolarMap ρ) := by
  rintro ⟨u, x⟩ ⟨v, y⟩ h
  have hxy : x = y := by
    have hm := congrArg (positiveFibreModulus ρ hρ.le) h
    simpa only [positiveFibreModulus_polarMap] using hm
  subst y
  have hx : ToricSpace.time (x.1 : ToricSpace.Space) ≠ 0 := by
    rw [x.2]
    exact Complex.ofReal_ne_zero.mpr hρ.ne'
  have huv : u = v := compactFibreAction_injective_of_time_ne_zero hx (congrArg Subtype.val h)
  exact Prod.ext huv rfl

private theorem
    CuspSpecialization.compactTorusPhase_two_eq_one_of_positive_time (ρ : ℝ) (hρ : 0 < ρ)
    {x : ToricSpace.Space} (hx : ToricSpace.time x = (ρ : ℂ)) (u : ToricSpace.CompactTorus)
    (hu : ToricSpace.compactTorusAction u (ToricSpace.modulus x) = x) : u 2 = 1 := by
  have hm : ToricSpace.time (ToricSpace.modulus x) = (ρ : ℂ) := by
    rw [ToricSpace.time_modulus, hx, Complex.norm_of_nonneg hρ.le]
  have ht := congrArg ToricSpace.time hu
  rw [ToricSpace.compactTorusAction, ToricSpace.time_torusAction,
    ToricSpace.compactTorusUnits_apply, hm, hx] at ht
  apply Circle.ext
  apply mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hρ.ne')
  simpa only [Circle.coe_one, one_mul] using ht

private theorem
    CuspSpecialization.exists_compactFibreAction_modulus_of_positive_time (ρ : ℝ) (hρ : 0 < ρ)
    {x : ToricSpace.Space} (hx : ToricSpace.time x = (ρ : ℂ)) :
    ∃ u : ToricSpace.CompactFibreTorus,
      ToricSpace.compactFibreAction u (ToricSpace.modulus x) = x := by
  obtain ⟨u, hu⟩ := ToricSpace.exists_compactTorusAction_modulus x
  have hu2 := compactTorusPhase_two_eq_one_of_positive_time ρ hρ hx u hu
  let uf : ToricSpace.CompactFibreTorus := ![u 0, u 1]
  have hf : ToricSpace.compactFibrePhase uf = u := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact hu2.symm
  refine ⟨uf, ?_⟩
  rw [ToricSpace.compactFibreAction_eq_compact, hf]
  exact hu

private theorem CuspSpecialization.positiveFibrePolarMap_surjective (ρ : ℝ) (hρ : 0 < ρ) :
    Function.Surjective (positiveFibrePolarMap ρ) := by
  intro x
  obtain ⟨u, hu⟩ := exists_compactFibreAction_modulus_of_positive_time ρ hρ x.2
  exact ⟨(u, positiveFibreModulus ρ hρ.le x), Subtype.ext hu⟩

private theorem CuspSpecialization.positiveFibrePolarMap_isProperMap (ρ : ℝ) :
    IsProperMap (positiveFibrePolarMap ρ) := by
  have hinc :
    IsProperMap
      (fun p : ToricSpace.CompactFibreTorus × PositiveFibre ρ =>
        (p.1, (p.2.1 : ToricSpace.Space))) :=
    ((Homeomorph.refl ToricSpace.CompactFibreTorus).isClosedEmbedding.prodMap
        (positiveFibreVal_isClosedEmbedding ρ)).isProperMap
  have hcomp :
    IsProperMap
      ((Subtype.val : ToricFibre (ρ : ℂ) → ToricSpace.Space) ∘ positiveFibrePolarMap ρ) :=
    ToricSpace.compactFibreAction_isProperMap.comp hinc
  exact
    isProperMap_of_comp_of_inj (positiveFibrePolarMap_continuous ρ) continuous_subtype_val hcomp
      Subtype.val_injective

private theorem CuspSpecialization.positiveFibrePolarMap_isClosedMap (ρ : ℝ) :
    IsClosedMap (positiveFibrePolarMap ρ) :=
  (positiveFibrePolarMap_isProperMap ρ).isClosedMap

private def CuspSpecialization.positiveFibrePolarHomeomorph (ρ : ℝ) (hρ : 0 < ρ) :
    (ToricSpace.CompactFibreTorus × PositiveFibre ρ) ≃ₜ ToricFibre (ρ : ℂ) :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (positiveFibrePolarMap ρ)
      ⟨positiveFibrePolarMap_injective ρ hρ, positiveFibrePolarMap_surjective ρ hρ⟩)
    (positiveFibrePolarMap_continuous ρ) (positiveFibrePolarMap_isClosedMap ρ)

@[simp]
private theorem CuspSpecialization.modulus_torusPoint (w : ToricCharts.CoordinateSpace 3) :
    ToricSpace.modulus (CuspUniformization.torusPoint w) =
      CuspUniformization.torusPoint (ToricCharts.coordinateModulus w) := by
  simp only [CuspUniformization.torusPoint, ToricSpace.modulus_inclusion,
    ToricCharts.monomial_coordinateModulus]

private theorem CuspSpecialization.torusCoordinates_modulus {x : ToricSpace.Space}
    (hx : x ∈ ToricSpace.openTorus) :
    ToricSpace.torusCoordinates (ToricSpace.modulus x) =
      ToricCharts.coordinateModulus (ToricSpace.torusCoordinates x) := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [ToricSpace.modulus_inclusion,
    ToricSpace.torusCoordinates_inclusion _
      ((ToricCharts.coordinateModulus_mem_torus_iff z).mpr hz),
    ToricSpace.torusCoordinates_inclusion _ hz, ToricCharts.monomial_coordinateModulus]

private theorem
    CuspSpecialization.positivePart_torusCoordinates_eq_norm (q : ToricSpace.PositivePart)
    (ht : ToricSpace.time (q : ToricSpace.Space) ≠ 0) (i : Fin 3) :
    ToricSpace.torusCoordinates (q : ToricSpace.Space) i =
      (‖ToricSpace.torusCoordinates (q : ToricSpace.Space) i‖ : ℂ) := by
  have hx : (q : ToricSpace.Space) ∈ ToricSpace.openTorus :=
    (ToricSpace.mem_openTorus_iff _).mpr ht
  have hq : ToricSpace.modulus (q : ToricSpace.Space) = (q : ToricSpace.Space) := q.2
  simpa only [hq, ToricCharts.coordinateModulus_apply] using
    congrFun (torusCoordinates_modulus hx) i

private theorem
    CuspSpecialization.positivePart_torusCoordinates_norm_pos (q : ToricSpace.PositivePart)
    (ht : ToricSpace.time (q : ToricSpace.Space) ≠ 0) (i : Fin 3) :
    0 < ‖ToricSpace.torusCoordinates (q : ToricSpace.Space) i‖ :=
  norm_pos_iff.mpr
    (ToricSpace.torusCoordinates_nonzero ((ToricSpace.mem_openTorus_iff _).mpr ht) i)

private theorem
    CuspSpecialization.positiveFibre_time_ne_zero (ρ : ℝ) (hρ : 0 < ρ) (q : PositiveFibre ρ) :
    ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0 := by
  rw [q.2]
  exact Complex.ofReal_ne_zero.mpr hρ.ne'

private def CuspSpecialization.positiveLogCoordinates (ρ : ℝ) (r : (CuspHoneycombTiling.Plane)) :
    ToricCharts.CoordinateSpace 3 :=
  ![(Real.exp (Real.log ρ * r 0) : ℂ), (Real.exp (Real.log ρ * r 1) : ℂ), (ρ : ℂ)]

private theorem CuspSpecialization.positiveLogCoordinates_mem {ρ : ℝ} (hρ : 0 < ρ)
    (r : (CuspHoneycombTiling.Plane)) : positiveLogCoordinates ρ r ∈ ToricCharts.torus := by
  intro i
  fin_cases i
  · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  · exact Complex.ofReal_ne_zero.mpr hρ.ne'

private theorem CuspSpecialization.torusCoordinates_positiveLogPoint {ρ : ℝ} (hρ : 0 < ρ)
    (r : (CuspHoneycombTiling.Plane)) :
    ToricSpace.torusCoordinates (CuspUniformization.torusPoint (positiveLogCoordinates ρ r)) =
      positiveLogCoordinates ρ r :=
  CuspUniformization.torusCoordinates_torusPoint (positiveLogCoordinates_mem hρ r)

private theorem CuspSpecialization.time_positiveLogPoint {ρ : ℝ} (hρ : 0 < ρ)
    (r : (CuspHoneycombTiling.Plane)) :
    ToricSpace.time (CuspUniformization.torusPoint (positiveLogCoordinates ρ r)) = (ρ : ℂ) := by
  simpa [positiveLogCoordinates] using congrFun (torusCoordinates_positiveLogPoint hρ r) 2

private theorem
    CuspSpecialization.position_positiveLogPoint {ρ : ℝ} (hρ : 0 < ρ) (hlog : Real.log ρ ≠ 0)
    (r : (CuspHoneycombTiling.Plane)) :
    ToricSpace.position (CuspUniformization.torusPoint (positiveLogCoordinates ρ r)) = r := by
  funext i
  rw [ToricSpace.position, ToricSpace.logCoordinates, torusCoordinates_positiveLogPoint hρ r,
    time_positiveLogPoint hρ r, Complex.norm_of_nonneg hρ.le]
  fin_cases i
  · change Real.log ‖(Real.exp (Real.log ρ * r 0) : ℂ)‖ / Real.log ρ = r 0
    rw [Complex.norm_of_nonneg (Real.exp_nonneg _), Real.log_exp]
    exact mul_div_cancel_left₀ _ hlog
  · change Real.log ‖(Real.exp (Real.log ρ * r 1) : ℂ)‖ / Real.log ρ = r 1
    rw [Complex.norm_of_nonneg (Real.exp_nonneg _), Real.log_exp]
    exact mul_div_cancel_left₀ _ hlog

private theorem CuspSpecialization.positiveLogCoordinates_continuous (ρ : ℝ) :
    Continuous (positiveLogCoordinates ρ) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact
      Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul (continuous_apply 0)))
  · exact
      Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul (continuous_apply 1)))
  · exact continuous_const

private theorem CuspSpecialization.positiveLogPoint_continuous {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous
      (fun r : (CuspHoneycombTiling.Plane) =>
        CuspUniformization.torusPoint (positiveLogCoordinates ρ r)) :=
  CuspUniformization.torusChart.symm.continuousOn.comp_continuous
    (positiveLogCoordinates_continuous ρ) (fun r => positiveLogCoordinates_mem hρ r)

private theorem CuspSpecialization.positiveLogPoint_mem_positivePart {ρ : ℝ} (hρ : 0 < ρ)
    (r : (CuspHoneycombTiling.Plane)) :
    CuspUniformization.torusPoint (positiveLogCoordinates ρ r) ∈ ToricSpace.positivePart := by
  change ToricSpace.modulus (CuspUniformization.torusPoint (positiveLogCoordinates ρ r)) = _
  rw [modulus_torusPoint]
  apply congrArg CuspUniformization.torusPoint
  funext i
  fin_cases i
  · change (‖(Real.exp (Real.log ρ * r 0) : ℂ)‖ : ℂ) = (Real.exp (Real.log ρ * r 0) : ℂ)
    rw [Complex.norm_of_nonneg (Real.exp_nonneg _)]
  · change (‖(Real.exp (Real.log ρ * r 1) : ℂ)‖ : ℂ) = (Real.exp (Real.log ρ * r 1) : ℂ)
    rw [Complex.norm_of_nonneg (Real.exp_nonneg _)]
  · change (‖(ρ : ℂ)‖ : ℂ) = (ρ : ℂ)
    rw [Complex.norm_of_nonneg hρ.le]

private def CuspSpecialization.positivePositionPoint (ρ : ℝ) (hρ : 0 < ρ)
    (r : (CuspHoneycombTiling.Plane)) : PositiveFibre ρ :=
  ⟨⟨CuspUniformization.torusPoint (positiveLogCoordinates ρ r),
      positiveLogPoint_mem_positivePart hρ r⟩,
    time_positiveLogPoint hρ r⟩

@[simp]
private theorem CuspSpecialization.position_positivePositionPoint (ρ : ℝ) (hρ : 0 < ρ)
    (hlog : Real.log ρ ≠ 0) (r : (CuspHoneycombTiling.Plane)) :
    ToricSpace.position ((positivePositionPoint ρ hρ r).1 : ToricSpace.Space) = r :=
  position_positiveLogPoint hρ hlog r

private theorem CuspSpecialization.positivePositionPoint_continuous (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (positivePositionPoint ρ hρ) := by
  apply Continuous.subtype_mk
  exact (positiveLogPoint_continuous hρ).subtype_mk _

private theorem CuspSpecialization.position_positiveFibre_injective (ρ : ℝ) (hρ : 0 < ρ)
    (hlog : Real.log ρ ≠ 0) :
    Function.Injective
      (fun q : PositiveFibre ρ => ToricSpace.position (q.1 : ToricSpace.Space)) := by
  intro q r he
  have hq := positiveFibre_time_ne_zero ρ hρ q
  have hr := positiveFibre_time_ne_zero ρ hρ r
  have hcoord (i : Fin 2) :
    ToricSpace.torusCoordinates (q.1 : ToricSpace.Space) i.castSucc =
      ToricSpace.torusCoordinates (r.1 : ToricSpace.Space) i.castSucc := by
    have hl :
      Real.log ‖ToricSpace.torusCoordinates (q.1 : ToricSpace.Space) i.castSucc‖ =
        Real.log ‖ToricSpace.torusCoordinates (r.1 : ToricSpace.Space) i.castSucc‖ := by
      have hi := congrFun he i
      change
        Real.log ‖ToricSpace.torusCoordinates (q.1 : ToricSpace.Space) i.castSucc‖ /
            Real.log ‖ToricSpace.time (q.1 : ToricSpace.Space)‖ =
          Real.log ‖ToricSpace.torusCoordinates (r.1 : ToricSpace.Space) i.castSucc‖ /
            Real.log ‖ToricSpace.time (r.1 : ToricSpace.Space)‖ at hi
      rw [norm_time_positiveFibre ρ hρ.le q, norm_time_positiveFibre ρ hρ.le r] at hi
      have hm := congrArg (fun z : ℝ => z * Real.log ρ) hi
      simpa only [div_mul_cancel₀ _ hlog] using hm
    have hn := congrArg Real.exp hl
    rw [Real.exp_log (positivePart_torusCoordinates_norm_pos q.1 hq i.castSucc),
      Real.exp_log (positivePart_torusCoordinates_norm_pos r.1 hr i.castSucc)] at hn
    rw [positivePart_torusCoordinates_eq_norm q.1 hq i.castSucc,
      positivePart_torusCoordinates_eq_norm r.1 hr i.castSucc, hn]
  apply Subtype.ext
  apply Subtype.ext
  apply
    CuspUniformization.torusCoordinates_injective ((ToricSpace.mem_openTorus_iff _).mpr hq)
      ((ToricSpace.mem_openTorus_iff _).mpr hr)
  funext i
  fin_cases i
  · exact hcoord 0
  · exact hcoord 1
  · change
      ToricSpace.torusCoordinates (q.1 : ToricSpace.Space) 2 =
        ToricSpace.torusCoordinates (r.1 : ToricSpace.Space) 2
    rw [ToricSpace.torusCoordinates_time, ToricSpace.torusCoordinates_time, q.2, r.2]

private theorem
    CuspSpecialization.realCuspVector_neg_realCuspVector (y : (CuspHoneycombTiling.Plane)) :
    ToricSpace.realCuspVector (-ToricSpace.realCuspVector y) = y := by
  ext i
  fin_cases i <;> simp [ToricSpace.realCuspVector]

private theorem
    CuspSpecialization.neg_realCuspVector_realCuspVector (y : (CuspHoneycombTiling.Plane)) :
    -ToricSpace.realCuspVector (ToricSpace.realCuspVector y) = y := by
  rw [← map_neg, realCuspVector_neg_realCuspVector]

private def CuspSpecialization.normalizedPositivePoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (y : (CuspHoneycombTiling.Plane)) : PositiveFibre ρ :=
  positivePositionPoint ρ hρ
    (ToricSpace.displacement (CuspPositive.positiveTwist C₀) (ρ : ℂ)
      (-ToricSpace.realCuspVector y))

private theorem
    CuspSpecialization.normalizedPositivePoint_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) : Continuous (normalizedPositivePoint C₀ ρ hρ) :=
  (positivePositionPoint_continuous ρ hρ).comp
    ((ToricSpace.displacement (CuspPositive.positiveTwist C₀)
          (ρ : ℂ)).continuous_of_finiteDimensional.comp
      CuspControlledRetraction.realCuspVector_continuous.neg)

private theorem CuspSpecialization.position_normalizedPositivePoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (hlog : Real.log ρ ≠ 0) (y : (CuspHoneycombTiling.Plane)) :
    ToricSpace.position ((normalizedPositivePoint C₀ ρ hρ y).1 : ToricSpace.Space) =
      ToricSpace.displacement (CuspPositive.positiveTwist C₀) (ρ : ℂ)
        (-ToricSpace.realCuspVector y) :=
  position_positivePositionPoint ρ hρ hlog _

private theorem CuspSpecialization.normalizedPosition_normalizedPositivePoint
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (y : (CuspHoneycombTiling.Plane)) :
    CuspControlledRetraction.normalizedPosition C₀
        ((normalizedPositivePoint C₀ ρ hρ y).1 : ToricSpace.Space) =
      y := by
  have hlog : Real.log ρ < 0 := Real.log_neg hρ (hρε.trans hε1)
  have hlogC : Real.log ‖(ρ : ℂ)‖ < 0 := by simpa only [Complex.norm_of_nonneg hρ.le] using hlog
  rw [CuspControlledRetraction.normalizedPosition, time_positiveFibre,
    position_normalizedPositivePoint C₀ ρ hρ hlog.ne,
    ToricSpace.inverseDisplacement_displacement (CuspPositive.positiveTwist C₀) hlogC
      (hR _ (by simpa only [Complex.norm_of_nonneg hρ.le] using hρ)
        (by simpa only [Complex.norm_of_nonneg hρ.le] using hρε))]
  exact realCuspVector_neg_realCuspVector y

private theorem CuspSpecialization.normalizedPositivePoint_normalizedPosition
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (q : PositiveFibre ρ) :
    normalizedPositivePoint C₀ ρ hρ
        (CuspControlledRetraction.normalizedPosition C₀ (q.1 : ToricSpace.Space)) =
      q := by
  have hlog : Real.log ρ < 0 := Real.log_neg hρ (hρε.trans hε1)
  have hlogC : Real.log ‖(ρ : ℂ)‖ < 0 := by simpa only [Complex.norm_of_nonneg hρ.le] using hlog
  apply position_positiveFibre_injective ρ hρ hlog.ne
  change
    ToricSpace.position
        ((normalizedPositivePoint C₀ ρ hρ
              (CuspControlledRetraction.normalizedPosition C₀ (q.1 : ToricSpace.Space))).1 :
          ToricSpace.Space) =
      ToricSpace.position (q.1 : ToricSpace.Space)
  rw [position_normalizedPositivePoint C₀ ρ hρ hlog.ne,
    CuspControlledRetraction.normalizedPosition, q.2, neg_realCuspVector_realCuspVector]
  exact
    ToricSpace.displacement_inverseDisplacement (CuspPositive.positiveTwist C₀) hlogC
      (hR _ (by simpa only [Complex.norm_of_nonneg hρ.le] using hρ)
        (by simpa only [Complex.norm_of_nonneg hρ.le] using hρε))
      _

private theorem CuspSpecialization.normalizedPosition_positiveFibre_continuous
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    Continuous
      (fun q : PositiveFibre ρ =>
        CuspControlledRetraction.normalizedPosition C₀ (q.1 : ToricSpace.Space)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have ht : ‖ToricSpace.time (q.1 : ToricSpace.Space)‖ < ε := by
    rw [norm_time_positiveFibre ρ hρ.le q]
    exact hρε
  exact
    ContinuousAt.comp (f := fun r : PositiveFibre ρ => (r.1 : ToricSpace.Space)) (g :=
      CuspControlledRetraction.normalizedPosition C₀)
      (CuspControlledRetraction.normalizedPosition_continuousAt C₀ hε1 hR
        (positiveFibre_time_ne_zero ρ hρ q) ht)
      (positiveFibreInclusion ρ).continuous.continuousAt

private def CuspSpecialization.normalizedPositiveHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    (CuspHoneycombTiling.Plane) ≃ₜ PositiveFibre ρ
    where
  toFun := normalizedPositivePoint C₀ ρ hρ
  invFun q := CuspControlledRetraction.normalizedPosition C₀ (q.1 : ToricSpace.Space)
  left_inv := normalizedPosition_normalizedPositivePoint C₀ ρ hρ ε hε1 hρε hR
  right_inv := normalizedPositivePoint_normalizedPosition C₀ ρ hρ ε hε1 hρε hR
  continuous_toFun := normalizedPositivePoint_continuous C₀ ρ hρ
  continuous_invFun := normalizedPosition_positiveFibre_continuous C₀ ρ hρ ε hε1 hρε hR

@[simp]
private theorem
    CuspSpecialization.normalizedPositiveHomeomorph_apply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (y : (CuspHoneycombTiling.Plane)) :
    normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR y = normalizedPositivePoint C₀ ρ hρ y :=
  rfl

@[simp]
private theorem
    CuspSpecialization.normalizedPositiveHomeomorph_symm_apply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (q : PositiveFibre ρ) :
    (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm q =
      CuspControlledRetraction.normalizedPosition C₀ (q.1 : ToricSpace.Space) :=
  rfl

private def CuspSpecialization.positiveFibreTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (v : Fin 2 → ℤ) (q : PositiveFibre ρ) : PositiveFibre ρ :=
  ⟨⟨ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v (q.1 : ToricSpace.Space),
      CuspPositive.twistedTranslate_positiveTwist_preserves_positivePart C₀ v q.1.2⟩,
    by rw [ToricSpace.time_twistedTranslate, q.2]⟩

@[simp]
private theorem
    CuspSpecialization.positiveFibreTranslate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (v : Fin 2 → ℤ) (q : PositiveFibre ρ) :
    ((positiveFibreTranslate C₀ ρ v q).1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v (q.1 : ToricSpace.Space) :=
  rfl

private theorem CuspSpecialization.normalizedPosition_positiveFibreTranslate
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (v : Fin 2 → ℤ)
    (q : PositiveFibre ρ) :
    CuspControlledRetraction.normalizedPosition C₀
        ((positiveFibreTranslate C₀ ρ v q).1 : ToricSpace.Space) =
      CuspControlledRetraction.normalizedPosition C₀ (q.1 : ToricSpace.Space) +
        CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) := by
  have hq : ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0 := by
    rw [q.2]
    exact Complex.ofReal_ne_zero.mpr hρ.ne'
  have ht : ‖ToricSpace.time (q.1 : ToricSpace.Space)‖ < ε := by
    rw [norm_time_positiveFibre ρ hρ.le q]
    exact hρε
  exact CuspControlledRetraction.normalizedPosition_twistedTranslate C₀ hε1 hR v hq ht

private theorem CuspSpecialization.normalizedPositiveHomeomorph_equivariant
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (v : Fin 2 → ℤ)
    (y : (CuspHoneycombTiling.Plane)) :
    normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR
        (y + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      positiveFibreTranslate C₀ ρ v (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR y) := by
  apply (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm.injective
  rw [Homeomorph.symm_apply_apply, normalizedPositiveHomeomorph_symm_apply,
    normalizedPosition_positiveFibreTranslate C₀ ρ hρ ε hε1 hρε hR]
  have hy := (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm_apply_apply y
  rw [normalizedPositiveHomeomorph_symm_apply] at hy
  rw [hy]

private theorem
    CuspSpecialization.normalizedPositivePoint_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (v : Fin 2 → ℤ)
    (y : (CuspHoneycombTiling.Plane)) :
    normalizedPositivePoint C₀ ρ hρ
        (y + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      positiveFibreTranslate C₀ ρ v (normalizedPositivePoint C₀ ρ hρ y) := by
  simpa only [normalizedPositiveHomeomorph_apply] using
    normalizedPositiveHomeomorph_equivariant C₀ ρ hρ ε hε1 hρε hR v y

private def
    CuspSpecialization.frozenPhaseHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    CuspHoneycomb.PhasePlane ≃ₜ ToricFibre (ρ : ℂ) :=
  ((Homeomorph.refl ToricSpace.CompactFibreTorus).prodCongr
        (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR)).trans
    (positiveFibrePolarHomeomorph ρ hρ)

private theorem
    CuspSpecialization.frozenPhaseHomeomorph_coe_homeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (p : CuspHoneycomb.PhasePlane) :
    (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p : ToricSpace.Space) =
      ToricSpace.compactFibreAction p.1
        ((normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR p.2).1 : ToricSpace.Space) :=
  rfl

@[simp]
private theorem CuspSpecialization.frozenPhaseHomeomorph_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (p : CuspHoneycomb.PhasePlane) :
    (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p : ToricSpace.Space) =
      ToricSpace.compactFibreAction p.1
        ((normalizedPositivePoint C₀ ρ hρ p.2).1 : ToricSpace.Space) := by
  rw [frozenPhaseHomeomorph_coe_homeomorph, normalizedPositiveHomeomorph_apply]

@[simp]
private theorem CuspSpecialization.sourceDeck_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CuspHoneycomb.PhasePlane) : CuspHoneycomb.honeycombDeckMap C₀ 0 p = p := by
  simp only [CuspHoneycomb.honeycombDeckMap, CuspCollapse.deckFibrePhase_zero, one_mul,
    ToricSpace.cuspVector_zero, CuspHoneycombTiling.latticePoint_zero, add_zero, Prod.eta]

private theorem CuspSpecialization.sourceDeck_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v w : Fin 2 → ℤ)
    (p : CuspHoneycomb.PhasePlane) :
    CuspHoneycomb.honeycombDeckMap C₀ v (CuspHoneycomb.honeycombDeckMap C₀ w p) =
      CuspHoneycomb.honeycombDeckMap C₀ (v + w) p := by
  apply Prod.ext
  · change
      CuspCollapse.deckFibrePhase C₀ v * (CuspCollapse.deckFibrePhase C₀ w * p.1) =
        CuspCollapse.deckFibrePhase C₀ (v + w) * p.1
    rw [CuspCollapse.deckFibrePhase_add, mul_assoc]
  · change
      (p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector w)) +
          CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) =
        p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector (v + w))
    rw [ToricSpace.cuspVector_add, CuspHoneycombTiling.latticePoint_add]
    abel

private def CuspSpecialization.sourceDeckSetoid (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Setoid CuspHoneycomb.PhasePlane
    where
  r p q := ∃ v : Fin 2 → ℤ, CuspHoneycomb.honeycombDeckMap C₀ v q = p
  iseqv :=
    { refl := fun p => ⟨0, sourceDeck_zero C₀ p⟩
      symm := by
        rintro p q ⟨v, hv⟩
        refine ⟨-v, ?_⟩
        rw [← hv, sourceDeck_add, neg_add_cancel, sourceDeck_zero]
      trans := by
        rintro p q r ⟨v, hv⟩ ⟨w, hw⟩
        refine ⟨v + w, ?_⟩
        rw [← sourceDeck_add, hw, hv] }

private abbrev CuspSpecialization.SourceModel (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :=
  Quotient (sourceDeckSetoid C₀)

private def CuspSpecialization.sourceProjection (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    CuspHoneycomb.PhasePlane → SourceModel C₀ :=
  Quotient.mk (sourceDeckSetoid C₀)

private theorem CuspSpecialization.sourceProjection_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (sourceProjection C₀) :=
  continuous_quotient_mk'

private theorem CuspSpecialization.sourceProjection_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Surjective (sourceProjection C₀) :=
  Quotient.mk_surjective

private theorem CuspSpecialization.sourceProjection_isQuotientMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Topology.IsQuotientMap (sourceProjection C₀) :=
  isQuotientMap_quotient_mk'

private theorem CuspSpecialization.sourceProjection_eq_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p q : CuspHoneycomb.PhasePlane) :
    sourceProjection C₀ p = sourceProjection C₀ q ↔
      ∃ v : Fin 2 → ℤ, CuspHoneycomb.honeycombDeckMap C₀ v q = p :=
  ⟨Quotient.exact, fun h => @Quotient.sound CuspHoneycomb.PhasePlane (sourceDeckSetoid C₀) p q h⟩

private theorem
    CuspSpecialization.honeycombCollapseMap_sourceDeck (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (v : Fin 2 → ℤ) (p : CuspHoneycomb.PhasePlane) :
    CuspHoneycomb.honeycombCollapseMap C ε hε (CuspHoneycomb.honeycombDeckMap (C 0) v p) =
      CuspHoneycomb.honeycombCollapseMap C ε hε p := by
  apply (CuspHoneycomb.honeycombCollapseMap_eq_iff C ε hε _ p).mpr
  refine ⟨v, rfl, ?_⟩
  change
    (CuspCollapse.deckFibrePhase (C 0) v * p.1)⁻¹ * (CuspCollapse.deckFibrePhase (C 0) v * p.1) ∈
      _
  rw [inv_mul_cancel]
  exact Subgroup.one_mem _

private def
    CuspSpecialization.sourceCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    C(SourceModel (C 0), CuspRetraction.QuotientCentralFibre C ε)
    where
  toFun :=
    Quotient.lift (CuspHoneycomb.honeycombCollapseMap C ε hε)
      (by
        rintro p q ⟨v, hv⟩
        rw [← hv]
        exact honeycombCollapseMap_sourceDeck C ε hε v q)
  continuous_toFun := (CuspHoneycomb.honeycombCollapseMap_continuous C ε hε).quotient_lift _

@[simp]
private theorem
    CuspSpecialization.sourceCollapse_projection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : CuspHoneycomb.PhasePlane) :
    sourceCollapse C ε hε (sourceProjection (C 0) p) =
      CuspHoneycomb.honeycombCollapseMap C ε hε p :=
  rfl

private theorem CuspSpecialization.circle_exp_two_pi : Circle.exp (2 * Real.pi) = 1 := by
  apply Circle.ext
  simpa only [Circle.coe_exp, Circle.coe_one, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    Complex.exp_two_pi_mul_I

private def CuspSpecialization.planarPhase (y : (CuspHoneycombTiling.Plane)) :
    ToricSpace.CompactFibreTorus := fun i => Circle.exp (2 * Real.pi * y i)

private theorem CuspSpecialization.planarPhase_continuous : Continuous planarPhase := by
  apply continuous_pi
  intro i
  exact Circle.exp.continuous.comp (continuous_const.mul (continuous_apply i))

private theorem CuspSpecialization.circle_exp_add_integer (a y : ℝ) (n : ℤ) :
    Circle.exp (a * (y + n)) = Circle.exp (a * y) * Circle.exp a ^ n := by
  rw [mul_add, Circle.exp_add]
  congr 1
  rw [mul_comm, Circle.exp_intCast_mul]

private theorem CuspSpecialization.planarPhase_add_latticePoint (y : (CuspHoneycombTiling.Plane))
    (v : Fin 2 → ℤ) : planarPhase (y + CuspHoneycombTiling.latticePoint v) = planarPhase y := by
  funext i
  change Circle.exp (2 * Real.pi * (y i + (v i : ℝ))) = _
  rw [circle_exp_add_integer, circle_exp_two_pi, one_zpow, mul_one]
  rfl

private def CuspSpecialization.compensatingPhase (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    ToricSpace.CompactTorus :=
  ![p.1 0 * Circle.exp (2 * Real.pi * r * p.2 0), p.1 1 * Circle.exp (2 * Real.pi * r * p.2 1),
    Circle.exp (2 * Real.pi * r)]

private theorem CuspSpecialization.compensatingPhase_continuous :
    Continuous (fun p : ℝ × CuspHoneycomb.PhasePlane => compensatingPhase p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [compensatingPhase] <;> fun_prop

@[simp]
private theorem CuspSpecialization.compensatingPhase_zero (p : CuspHoneycomb.PhasePlane) :
    compensatingPhase 0 p = ToricSpace.compactFibrePhase p.1 := by
  funext i
  fin_cases i <;> simp [compensatingPhase, ToricSpace.compactFibrePhase]

@[simp]
private theorem CuspSpecialization.compensatingPhase_one (p : CuspHoneycomb.PhasePlane) :
    compensatingPhase 1 p = ToricSpace.compactFibrePhase (p.1 * planarPhase p.2) := by
  funext i
  fin_cases i <;> simp [compensatingPhase, ToricSpace.compactFibrePhase, planarPhase]

private theorem
    CuspSpecialization.compensatingPhase_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    compensatingPhase r (CuspHoneycomb.honeycombDeckMap C₀ v p) =
      CuspPositive.phaseTransform C₀ v (compensatingPhase r p) := by
  funext i
  fin_cases i
  · change
      (CuspCollapse.deckFibrePhase C₀ v 0 * p.1 0) *
          Circle.exp (2 * Real.pi * r * (p.2 0 + (ToricSpace.cuspVector v 0 : ℝ))) =
        CuspPositive.frozenPhaseCoordinate C₀ v 0 *
          ((p.1 0 * Circle.exp (2 * Real.pi * r * p.2 0)) *
            Circle.exp (2 * Real.pi * r) ^ ToricSpace.cuspVector v 0)
    rw [circle_exp_add_integer]
    simp only [CuspCollapse.deckFibrePhase, mul_assoc]
  · change
      (CuspCollapse.deckFibrePhase C₀ v 1 * p.1 1) *
          Circle.exp (2 * Real.pi * r * (p.2 1 + (ToricSpace.cuspVector v 1 : ℝ))) =
        CuspPositive.frozenPhaseCoordinate C₀ v 1 *
          ((p.1 1 * Circle.exp (2 * Real.pi * r * p.2 1)) *
            Circle.exp (2 * Real.pi * r) ^ ToricSpace.cuspVector v 1)
    rw [circle_exp_add_integer]
    simp only [CuspCollapse.deckFibrePhase, mul_assoc]
  · simp [compensatingPhase, CuspPositive.phaseTransform, CuspPositive.frozenPhase,
      ToricSpace.phaseShear]

private def CuspSpecialization.rotatedLevel (ρ r : ℝ) : ℂ :=
  (Circle.exp (2 * Real.pi * r) : ℂ) * (ρ : ℂ)

@[simp]
private theorem
    CuspSpecialization.norm_rotatedLevel (ρ r : ℝ) (hρ : 0 ≤ ρ) : ‖rotatedLevel ρ r‖ = ρ := by
  rw [rotatedLevel, norm_mul, Circle.norm_coe, one_mul, Complex.norm_of_nonneg hρ]

private theorem
    CuspSpecialization.rotatedLevel_ne_zero (ρ r : ℝ) (hρ : 0 < ρ) : rotatedLevel ρ r ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_rotatedLevel ρ r hρ.le]
  exact hρ.ne'

private theorem
    CuspSpecialization.rotatedLevel_norm_lt (ρ r : ℝ) (hρ : 0 ≤ ρ) (ε : ℝ) (hρε : ρ < ε) :
    ‖rotatedLevel ρ r‖ < ε := by rwa [norm_rotatedLevel ρ r hρ]

private theorem
    CuspSpecialization.rotatedLevel_norm_le (ρ r : ℝ) (hρ : 0 ≤ ρ) (η : ℝ) (hρη : ρ ≤ η) :
    ‖rotatedLevel ρ r‖ ≤ η := by rwa [norm_rotatedLevel ρ r hρ]

private def CuspSpecialization.baseRotationPhase (r : ℝ) : ToricSpace.CompactTorus :=
  ![1, 1, Circle.exp (2 * Real.pi * r)]

private def CuspSpecialization.baseRotationMap (ρ r : ℝ) (x : ToricFibre (ρ : ℂ)) :
    ToricFibre (rotatedLevel ρ r) :=
  ⟨ToricSpace.compactTorusAction (baseRotationPhase r) x,
    by
    rw [ToricSpace.compactTorusAction, ToricSpace.time_torusAction,
      ToricSpace.compactTorusUnits_apply, x.2]
    rfl⟩

private def
    CuspSpecialization.baseInverseRotationMap (ρ r : ℝ) (x : ToricFibre (rotatedLevel ρ r)) :
    ToricFibre (ρ : ℂ) :=
  ⟨ToricSpace.compactTorusAction (baseRotationPhase r)⁻¹ x,
    by
    rw [ToricSpace.compactTorusAction, ToricSpace.time_torusAction,
      ToricSpace.compactTorusUnits_apply, x.2]
    change
      ((Circle.exp (2 * Real.pi * r))⁻¹ : Circle) *
          ((Circle.exp (2 * Real.pi * r) : ℂ) * (ρ : ℂ)) =
        (ρ : ℂ)
    rw [Circle.coe_inv, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]⟩

private theorem CuspSpecialization.baseRotationMap_continuous (ρ r : ℝ) :
    Continuous (baseRotationMap ρ r) := by
  have h :
    Continuous
      (fun x : ToricFibre (ρ : ℂ) =>
        ToricSpace.compactTorusAction (baseRotationPhase r) (x : ToricSpace.Space)) := by
    change Continuous (fun x : ToricFibre (ρ : ℂ) => baseRotationPhase r • (x : ToricSpace.Space))
    exact
      (continuous_const : Continuous (fun _ : ToricFibre (ρ : ℂ) => baseRotationPhase r)).smul
        (continuous_subtype_val :
          Continuous (fun x : ToricFibre (ρ : ℂ) => (x : ToricSpace.Space)))
  exact h.subtype_mk _

private theorem CuspSpecialization.baseInverseRotationMap_continuous (ρ r : ℝ) :
    Continuous (baseInverseRotationMap ρ r) := by
  have h :
    Continuous
      (fun x : ToricFibre (rotatedLevel ρ r) =>
        ToricSpace.compactTorusAction (baseRotationPhase r)⁻¹ (x : ToricSpace.Space)) := by
    change
      Continuous
        (fun x : ToricFibre (rotatedLevel ρ r) =>
          (baseRotationPhase r)⁻¹ • (x : ToricSpace.Space))
    exact
      (continuous_const :
            Continuous (fun _ : ToricFibre (rotatedLevel ρ r) => (baseRotationPhase r)⁻¹)).smul
        (continuous_subtype_val :
          Continuous (fun x : ToricFibre (rotatedLevel ρ r) => (x : ToricSpace.Space)))
  exact h.subtype_mk _

private def CuspSpecialization.baseRotationHomeomorph (ρ r : ℝ) :
    ToricFibre (ρ : ℂ) ≃ₜ ToricFibre (rotatedLevel ρ r)
    where
  toFun := baseRotationMap ρ r
  invFun := baseInverseRotationMap ρ r
  left_inv
    x := by
    apply Subtype.ext
    change
      ToricSpace.compactTorusAction (baseRotationPhase r)⁻¹
          (ToricSpace.compactTorusAction (baseRotationPhase r) (x : ToricSpace.Space)) =
        (x : ToricSpace.Space)
    rw [ToricSpace.compactTorusAction_mul, inv_mul_cancel, ToricSpace.compactTorusAction_one]
  right_inv
    x := by
    apply Subtype.ext
    change
      ToricSpace.compactTorusAction (baseRotationPhase r)
          (ToricSpace.compactTorusAction (baseRotationPhase r)⁻¹ (x : ToricSpace.Space)) =
        (x : ToricSpace.Space)
    rw [ToricSpace.compactTorusAction_mul, mul_inv_cancel, ToricSpace.compactTorusAction_one]
  continuous_toFun := baseRotationMap_continuous ρ r
  continuous_invFun := baseInverseRotationMap_continuous ρ r

private def CuspSpecialization.partialPlanarPhase (r : ℝ) (y : (CuspHoneycombTiling.Plane)) :
    ToricSpace.CompactFibreTorus := fun i => Circle.exp (2 * Real.pi * r * y i)

private theorem CuspSpecialization.partialPlanarPhase_continuous (r : ℝ) :
    Continuous (partialPlanarPhase r) := by
  apply continuous_pi
  intro i
  exact Circle.exp.continuous.comp (continuous_const.mul (continuous_apply i))

private def CuspSpecialization.partialPhaseHomeomorph (r : ℝ) :
    CuspHoneycomb.PhasePlane ≃ₜ CuspHoneycomb.PhasePlane
    where
  toFun p := (p.1 * partialPlanarPhase r p.2, p.2)
  invFun p := (p.1 * (partialPlanarPhase r p.2)⁻¹, p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun :=
    (continuous_fst.mul ((partialPlanarPhase_continuous r).comp continuous_snd)).prodMk
      continuous_snd
  continuous_invFun :=
    (continuous_fst.mul (((partialPlanarPhase_continuous r).comp continuous_snd).inv)).prodMk
      continuous_snd

private theorem CuspSpecialization.baseRotationPhase_mul_partialPhase (r : ℝ)
    (p : CuspHoneycomb.PhasePlane) :
    baseRotationPhase r * ToricSpace.compactFibrePhase (p.1 * partialPlanarPhase r p.2) =
      compensatingPhase r p := by
  funext i
  fin_cases i <;>
    simp [baseRotationPhase, ToricSpace.compactFibrePhase, partialPlanarPhase, compensatingPhase]

private def
    CuspSpecialization.complexPhaseHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (r : ℝ) :
    CuspHoneycomb.PhasePlane ≃ₜ ToricFibre (rotatedLevel ρ r) :=
  ((partialPhaseHomeomorph r).trans (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR)).trans
    (baseRotationHomeomorph ρ r)

@[simp]
private theorem
    CuspSpecialization.complexPhaseHomeomorph_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (r : ℝ)
    (p : CuspHoneycomb.PhasePlane) :
    (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p : ToricSpace.Space) =
      ToricSpace.compactTorusAction (compensatingPhase r p)
        ((normalizedPositivePoint C₀ ρ hρ p.2).1 : ToricSpace.Space) := by
  change
    ToricSpace.compactTorusAction (baseRotationPhase r)
        (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR (partialPhaseHomeomorph r p) :
          ToricSpace.Space) =
      _
  rw [frozenPhaseHomeomorph_coe, ToricSpace.compactFibreAction_eq_compact,
    ToricSpace.compactTorusAction_mul]
  change
    ToricSpace.compactTorusAction
        (baseRotationPhase r * ToricSpace.compactFibrePhase (p.1 * partialPlanarPhase r p.2))
        ((normalizedPositivePoint C₀ ρ hρ p.2).1 : ToricSpace.Space) =
      _
  rw [baseRotationPhase_mul_partialPhase]

private theorem
    CuspSpecialization.complexPhaseHomeomorph_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (r : ℝ) (v : Fin 2 → ℤ)
    (p : CuspHoneycomb.PhasePlane) :
    (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r (CuspHoneycomb.honeycombDeckMap C₀ v p) :
        ToricSpace.Space) =
      ToricSpace.twistedTranslate (fun _ => C₀) v
        (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p : ToricSpace.Space) := by
  rw [complexPhaseHomeomorph_coe, complexPhaseHomeomorph_coe, compensatingPhase_deck]
  change
    ToricSpace.compactTorusAction (CuspPositive.phaseTransform C₀ v (compensatingPhase r p))
        ((normalizedPositivePoint C₀ ρ hρ
              (p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v))).1 :
          ToricSpace.Space) =
      _
  rw [normalizedPositivePoint_equivariant C₀ ρ hρ ε hε1 hρε hR, positiveFibreTranslate_coe,
    CuspPositive.twistedTranslate_constant_polar]

private def CuspSpecialization.toricFibrePunctured (η : ℝ) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η)
    (x : ToricFibre t) : CuspControlledRetraction.PuncturedClosedTube η :=
  CuspControlledRetraction.levelToPunctured η t ht (toricFibreLevelHomeomorph η t htη x)

private def CuspSpecialization.positiveFibrePunctured (ρ : ℝ) (hρ : 0 < ρ) (η : ℝ) (hρη : ρ ≤ η)
    (q : PositiveFibre ρ) : CuspControlledRetraction.PuncturedPositiveTube η :=
  ⟨⟨q.1, by rw [q.2, Complex.norm_of_nonneg hρ.le]; exact hρη⟩, by
    rw [q.2]
    exact Complex.ofReal_ne_zero.mpr hρ.ne'⟩

private def CuspSpecialization.phasePlaneShear (p : CuspHoneycomb.PhasePlane) :
    CuspHoneycomb.PhasePlane :=
  (p.1 * planarPhase p.2, p.2)

private theorem CuspSpecialization.phasePlaneShear_continuous : Continuous phasePlaneShear :=
  (continuous_fst.mul (planarPhase_continuous.comp continuous_snd)).prodMk continuous_snd

private theorem
    CuspSpecialization.phasePlaneShear_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (p : CuspHoneycomb.PhasePlane) :
    phasePlaneShear (CuspHoneycomb.honeycombDeckMap C₀ v p) =
      CuspHoneycomb.honeycombDeckMap C₀ v (phasePlaneShear p) := by
  apply Prod.ext
  · change
      (CuspCollapse.deckFibrePhase C₀ v * p.1) *
          planarPhase (p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
        CuspCollapse.deckFibrePhase C₀ v * (p.1 * planarPhase p.2)
    rw [planarPhase_add_latticePoint, mul_assoc]
  · rfl

private def CuspSpecialization.sourceShear (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    C(SourceModel C₀, SourceModel C₀)
    where
  toFun :=
    Quotient.map phasePlaneShear
      (by
        rintro p q ⟨v, hv⟩
        refine ⟨v, ?_⟩
        rw [← phasePlaneShear_deck, hv])
  continuous_toFun :=
    ((sourceProjection_continuous C₀).comp phasePlaneShear_continuous).quotient_lift _

@[simp]
private theorem CuspSpecialization.sourceShear_projection (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CuspHoneycomb.PhasePlane) :
    sourceShear C₀ (sourceProjection C₀ p) = sourceProjection C₀ (phasePlaneShear p) :=
  rfl

private def CuspSpecialization.rotatingCentralPoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (p : CuspHoneycomb.PhasePlane) : CuspRetraction.CentralFibre :=
  ⟨ToricSpace.compactTorusAction (compensatingPhase r p)
      ((CuspHoneycomb.honeycombHomeomorph C₀ p.2).1 : ToricSpace.Space),
    by
    apply norm_eq_zero.mp
    rw [ToricSpace.norm_time_compactTorusAction, (CuspHoneycomb.honeycombHomeomorph C₀ p.2).2,
      norm_zero]⟩

private theorem CuspSpecialization.rotatingCentralPoint_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (fun p : ℝ × CuspHoneycomb.PhasePlane => rotatingCentralPoint C₀ p.1 p.2) := by
  have hθ :
    Continuous
      (fun p : ℝ × CuspHoneycomb.PhasePlane => CuspHoneycomb.honeycombHomeomorph C₀ p.2.2) :=
    (CuspHoneycomb.honeycombHomeomorph C₀).continuous.comp (continuous_snd.comp continuous_snd)
  have hθp :
    Continuous
      (fun p : ℝ × CuspHoneycomb.PhasePlane => (CuspHoneycomb.honeycombHomeomorph C₀ p.2.2).1) :=
    continuous_subtype_val.comp hθ
  have hθx :
    Continuous
      (fun p : ℝ × CuspHoneycomb.PhasePlane =>
        ((CuspHoneycomb.honeycombHomeomorph C₀ p.2.2).1 : ToricSpace.Space)) :=
    continuous_subtype_val.comp hθp
  apply Continuous.subtype_mk
  change
    Continuous
      (fun p : ℝ × CuspHoneycomb.PhasePlane =>
        compensatingPhase p.1 p.2 •
          ((CuspHoneycomb.honeycombHomeomorph C₀ p.2.2).1 : ToricSpace.Space))
  exact compensatingPhase_continuous.smul hθx

@[simp]
private theorem CuspSpecialization.rotatingCentralPoint_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CuspHoneycomb.PhasePlane) :
    rotatingCentralPoint C₀ 0 p = CuspHoneycomb.honeycombPolarMap C₀ p := by
  apply Subtype.ext
  change ToricSpace.compactTorusAction (compensatingPhase 0 p) _ = _
  rw [compensatingPhase_zero]
  rfl

@[simp]
private theorem CuspSpecialization.rotatingCentralPoint_one (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CuspHoneycomb.PhasePlane) :
    rotatingCentralPoint C₀ 1 p = CuspHoneycomb.honeycombPolarMap C₀ (phasePlaneShear p) := by
  apply Subtype.ext
  change ToricSpace.compactTorusAction (compensatingPhase 1 p) _ = _
  rw [compensatingPhase_one]
  rfl

private theorem CuspSpecialization.rotatingCentralPoint_deck (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    (rotatingCentralPoint (C 0) r (CuspHoneycomb.honeycombDeckMap (C 0) v p) : ToricSpace.Space) =
      ToricSpace.twistedTranslate C v (rotatingCentralPoint (C 0) r p : ToricSpace.Space) := by
  rw [CuspCollapse.twistedTranslate_central_eq_constant C v (rotatingCentralPoint (C 0) r p).2]
  change
    ToricSpace.compactTorusAction (compensatingPhase r (CuspHoneycomb.honeycombDeckMap (C 0) v p))
        ((CuspHoneycomb.honeycombHomeomorph (C 0)
              (p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v))).1 :
          ToricSpace.Space) =
      ToricSpace.twistedTranslate (fun _ => C 0) v
        (ToricSpace.compactTorusAction (compensatingPhase r p)
          ((CuspHoneycomb.honeycombHomeomorph (C 0) p.2).1 : ToricSpace.Space))
  rw [compensatingPhase_deck, CuspHoneycomb.honeycombHomeomorph_equivariant,
    CuspCollapse.positiveCentralTranslate_coe, CuspPositive.twistedTranslate_constant_polar]

private theorem CuspSpecialization.toricFibrePunctured_complexPhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (r : ℝ) (η : ℝ) (hρη : ρ ≤ η)
    (p : CuspHoneycomb.PhasePlane) :
    toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
        (rotatedLevel_norm_le ρ r hρ.le η hρη) (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p) =
      CuspControlledRetraction.puncturedPolarMap η
        (compensatingPhase r p,
          positiveFibrePunctured ρ hρ η hρη (normalizedPositivePoint C₀ ρ hρ p.2)) := by
  apply Subtype.ext
  apply Subtype.ext
  exact complexPhaseHomeomorph_coe C₀ ρ hρ ε hε1 hρε hR r p

private theorem
    CuspSpecialization.prescribedCollapse_complexPhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (r : ℝ) (η : ℝ) (hρη : ρ ≤ η)
    (p : CuspHoneycomb.PhasePlane) :
    CuspControlledRetraction.prescribedCollapse C₀ η
        (toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
          (rotatedLevel_norm_le ρ r hρ.le η hρη)
          (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p)) =
      rotatingCentralPoint C₀ r p := by
  apply Subtype.ext
  rw [toricFibrePunctured_complexPhase C₀ ρ hρ ε hε1 hρε hR r η hρη p,
    CuspControlledRetraction.prescribedCollapse_polar]
  change
    ToricSpace.compactTorusAction (compensatingPhase r p)
        ((CuspHoneycomb.honeycombHomeomorph C₀
              (CuspControlledRetraction.normalizedPosition C₀
                ((normalizedPositivePoint C₀ ρ hρ p.2).1 : ToricSpace.Space))).1 :
          ToricSpace.Space) =
      ToricSpace.compactTorusAction (compensatingPhase r p)
        ((CuspHoneycomb.honeycombHomeomorph C₀ p.2).1 : ToricSpace.Space)
  have hy := (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm_apply_apply p.2
  rw [normalizedPositiveHomeomorph_symm_apply, normalizedPositiveHomeomorph_apply] at hy
  rw [hy]

private def CuspSpecialization.fibreProjection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (t : ℂ)
    (htε : ‖t‖ < ε) : ToricFibre t → CuspControlledRetraction.ActualQuotientFibre C ε t :=
  CuspControlledRetraction.quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl ∘
    CuspControlledRetraction.levelProjection C htε t ∘ toricFibreLevelHomeomorph ‖t‖ t le_rfl

@[simp]
private theorem
    CuspSpecialization.fibreProjection_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (t : ℂ)
    (htε : ‖t‖ < ε) (x : ToricFibre t) :
    (fibreProjection C ε t htε x : CuspQuotient.QuotientSpace C ε) =
      CuspQuotient.quotientMap C ε
        ⟨(x : ToricSpace.Space),
          by
          change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
          rw [x.2]
          simpa only [Metric.mem_ball, dist_zero_right] using htε⟩ :=
  rfl

private theorem
    CuspSpecialization.fibreProjection_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (t : ℂ) (htε : ‖t‖ < ε) : Function.Surjective (fibreProjection C ε t htε) :=
  (CuspControlledRetraction.quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl).surjective.comp
    ((CuspControlledRetraction.levelProjection_surjective C htε t).comp
      (toricFibreLevelHomeomorph ‖t‖ t le_rfl).surjective)

private theorem
    CuspSpecialization.fibreProjection_isOpenQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (t : ℂ) (htε : ‖t‖ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    IsOpenQuotientMap (fibreProjection C ε t htε) :=
  (CuspControlledRetraction.quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl).isOpenQuotientMap.comp
    ((CuspControlledRetraction.levelProjection_isOpenQuotientMap C htε t hC).comp
      (toricFibreLevelHomeomorph ‖t‖ t le_rfl).isOpenQuotientMap)

private theorem CuspSpecialization.fibreProjection_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (t : ℂ) (htε : ‖t‖ < ε) (x y : ToricFibre t) :
    fibreProjection C ε t htε x = fibreProjection C ε t htε y ↔
      ∃ v : Fin 2 → ℤ,
        ToricSpace.twistedTranslate C v (y : ToricSpace.Space) = (x : ToricSpace.Space) := by
  change
    CuspControlledRetraction.quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl
          (CuspControlledRetraction.levelProjection C htε t
            (toricFibreLevelHomeomorph ‖t‖ t le_rfl x)) =
        CuspControlledRetraction.quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl
          (CuspControlledRetraction.levelProjection C htε t
            (toricFibreLevelHomeomorph ‖t‖ t le_rfl y)) ↔
      _
  rw [(CuspControlledRetraction.quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl).injective.eq_iff,
    CuspControlledRetraction.levelProjection_eq_iff]
  apply exists_congr
  intro v
  exact
    ⟨fun h => congrArg (fun z : CuspRetraction.ClosedTube ‖t‖ => (z : ToricSpace.Space)) h,
      fun h => Subtype.ext h⟩

private theorem
    CuspSpecialization.fibreProjection_eq_levelProjection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (t : ℂ) (htε : ‖t‖ < ε) (η : ℝ) (hηε : η < ε) (htη : ‖t‖ ≤ η) (x : ToricFibre t) :
    fibreProjection C ε t htε x =
      CuspControlledRetraction.quotientLevelFibreHomeomorph C ε η t htη
        (CuspControlledRetraction.levelProjection C hηε t
          (toricFibreLevelHomeomorph η t htη x)) :=
  rfl

private def CuspSpecialization.toricFibreChangeTwist (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ)
    (x : ToricFibre t) : ToricFibre t :=
  ⟨CuspRetraction.changeTwist C D x, (CuspRetraction.time_changeTwist C D x).trans x.2⟩

private def CuspSpecialization.toricFibreChangeTwistHomeomorph (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContDiffOn ℂ ω (fun z => D z i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) (t : ℂ) (htε : ‖t‖ < ε) :
    ToricFibre t ≃ₜ ToricFibre t
    where
  toFun := toricFibreChangeTwist C D t
  invFun := toricFibreChangeTwist D C t
  left_inv
    x :=
    Subtype.ext
      (CuspRetraction.changeTwist_inverse_on_disc C D hε1 hRC hRD
        (by
          rw [x.2]
          exact htε))
  right_inv
    x :=
    Subtype.ext
      (CuspRetraction.changeTwist_inverse_on_disc D C hε1 hRD hRC
        (by
          rw [x.2]
          exact htε))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      (CuspRetraction.changeTwist_continuousOn C D hε hε1 (fun i j => (hC i j).continuousOn)
            (fun i j => (hD i j).continuousOn) hzero hRC).comp_continuous
        continuous_subtype_val
        (fun x => by
          change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
          rw [x.2]
          simpa only [Metric.mem_ball, dist_zero_right] using htε)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact
      (CuspRetraction.changeTwist_continuousOn D C hε hε1 (fun i j => (hD i j).continuousOn)
            (fun i j => (hC i j).continuousOn) hzero.symm hRD).comp_continuous
        continuous_subtype_val
        (fun x => by
          change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
          rw [x.2]
          simpa only [Metric.mem_ball, dist_zero_right] using htε)

private theorem
    CuspSpecialization.centralRotation_sourceDeck (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (r : ℝ) (v : Fin 2 → ℤ) (p : CuspHoneycomb.PhasePlane) :
    CuspCollapse.centralProject C ε hε
        (rotatingCentralPoint (C 0) r (CuspHoneycomb.honeycombDeckMap (C 0) v p)) =
      CuspCollapse.centralProject C ε hε (rotatingCentralPoint (C 0) r p) := by
  apply (CuspCollapse.centralProject_eq_iff C ε hε _ _).mpr
  exact ⟨v, (rotatingCentralPoint_deck C v r p).symm⟩

private def
    CuspSpecialization.sourceRotation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (r : ℝ) : C(SourceModel (C 0), CuspRetraction.QuotientCentralFibre C ε)
    where
  toFun :=
    Quotient.lift
      (fun p : CuspHoneycomb.PhasePlane =>
        CuspCollapse.centralProject C ε hε (rotatingCentralPoint (C 0) r p))
      (by
        rintro p q ⟨v, hv⟩
        rw [← hv]
        exact centralRotation_sourceDeck C ε hε r v q)
  continuous_toFun :=
    ((CuspCollapse.centralProject_continuous C ε hε).comp
          ((rotatingCentralPoint_continuous (C 0)).comp
            (continuous_const.prodMk continuous_id))).quotient_lift
      _

@[simp]
private theorem
    CuspSpecialization.sourceRotation_projection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    sourceRotation C ε hε r (sourceProjection (C 0) p) =
      CuspCollapse.centralProject C ε hε (rotatingCentralPoint (C 0) r p) :=
  rfl

private theorem
    CuspSpecialization.sourceRotation_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Continuous (fun p : ℝ × SourceModel (C 0) => sourceRotation C ε hε p.1 p.2) := by
  apply (sourceProjection_isQuotientMap (C 0)).continuous_lift_prod_right
  simpa only [Function.comp_def, sourceRotation_projection] using
    (CuspCollapse.centralProject_continuous C ε hε).comp (rotatingCentralPoint_continuous (C 0))

@[simp]
private theorem CuspSpecialization.sourceRotation_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : sourceRotation C ε hε 0 = sourceCollapse C ε hε := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := sourceProjection_surjective (C 0) q
  rw [sourceRotation_projection, rotatingCentralPoint_zero]
  rfl

@[simp]
private theorem CuspSpecialization.sourceRotation_one (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : sourceRotation C ε hε 1 = (sourceCollapse C ε hε).comp (sourceShear (C 0)) := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := sourceProjection_surjective (C 0) q
  rw [sourceRotation_projection, rotatingCentralPoint_one]
  rfl

private def CuspSpecialization.sourceRotationHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (r : ℝ) : (sourceCollapse C ε hε).Homotopy (sourceRotation C ε hε r)
    where
  toFun p := sourceRotation C ε hε ((p.1 : ℝ) * r) p.2
  continuous_toFun := by
    have hs : Continuous (fun p : unitInterval × SourceModel (C 0) => ((p.1 : ℝ) * r, p.2)) :=
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd
    simpa only [Function.comp_def] using (sourceRotation_continuous C ε hε).comp hs
  map_zero_left
    q := by
    change sourceRotation C ε hε (0 * r) q = sourceCollapse C ε hε q
    rw [MulZeroClass.zero_mul, sourceRotation_zero]
  map_one_left
    q := by
    change sourceRotation C ε hε (1 * r) q = sourceRotation C ε hε r q
    rw [one_mul]

private def
    CuspSpecialization.varyingComplexPhaseHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) : CuspHoneycomb.PhasePlane ≃ₜ ToricFibre (rotatedLevel ρ r) :=
  (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε (CuspPositive.smallDrift_positiveTwist (C 0) hRD)
        r).trans
    (toricFibreChangeTwistHomeomorph C (CuspRetraction.frozen C) ε hε hε1 hC
        (fun _ _ => contDiffOn_const) rfl hRC hRD (rotatedLevel ρ r)
        (rotatedLevel_norm_lt ρ r hρ.le ε hρε)).symm

@[simp]
private theorem
    CuspSpecialization.varyingComplexPhaseHomeomorph_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p : ToricSpace.Space) =
      CuspRetraction.changeTwist (CuspRetraction.frozen C) C
        (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
            (CuspPositive.smallDrift_positiveTwist (C 0) hRD) r p :
          ToricSpace.Space) :=
  rfl

private theorem CuspSpecialization.varyingComplexPhaseHomeomorph_straightened
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    CuspRetraction.changeTwist C (CuspRetraction.frozen C)
        (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p : ToricSpace.Space) =
      (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
          (CuspPositive.smallDrift_positiveTwist (C 0) hRD) r p :
        ToricSpace.Space) := by
  rw [varyingComplexPhaseHomeomorph_coe]
  apply CuspRetraction.changeTwist_inverse_on_disc (CuspRetraction.frozen C) C hε1 hRD hRC
  rw [(complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
        (CuspPositive.smallDrift_positiveTwist (C 0) hRD) r p).2]
  exact rotatedLevel_norm_lt ρ r hρ.le ε hρε

private theorem
    CuspSpecialization.varyingComplexPhaseHomeomorph_deck (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (v : Fin 2 → ℤ) (p : CuspHoneycomb.PhasePlane) :
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r
          (CuspHoneycomb.honeycombDeckMap (C 0) v p) :
        ToricSpace.Space) =
      ToricSpace.twistedTranslate C v
        (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p : ToricSpace.Space) := by
  rw [varyingComplexPhaseHomeomorph_coe, varyingComplexPhaseHomeomorph_coe,
    complexPhaseHomeomorph_deck]
  apply CuspRetraction.changeTwist_equivariant_on_disc (CuspRetraction.frozen C) C rfl hε1 hRD
  rw [(complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
        (CuspPositive.smallDrift_positiveTwist (C 0) hRD) r p).2]
  exact rotatedLevel_norm_lt ρ r hρ.le ε hρε

private def CuspSpecialization.varyingComplexFibreMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) :
    CuspHoneycomb.PhasePlane →
      CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r) :=
  fibreProjection C ε (rotatedLevel ρ r) (rotatedLevel_norm_lt ρ r hρ.le ε hρε) ∘
    varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r

private theorem CuspSpecialization.varyingComplexFibreMap_isOpenQuotientMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) : IsOpenQuotientMap (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r) :=
  (fibreProjection_isOpenQuotientMap C ε (rotatedLevel ρ r) (rotatedLevel_norm_lt ρ r hρ.le ε hρε)
        hC).comp
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).isOpenQuotientMap

private theorem
    CuspSpecialization.varyingComplexFibreMap_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) : Topology.IsQuotientMap (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r) :=
  (varyingComplexFibreMap_isOpenQuotientMap C ρ hρ ε hε hε1 hρε hC hRC hRD r).isQuotientMap

private theorem CuspSpecialization.varyingComplexFibreMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (p q : CuspHoneycomb.PhasePlane) :
    varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p =
        varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r q ↔
      ∃ v : Fin 2 → ℤ, CuspHoneycomb.honeycombDeckMap (C 0) v q = p := by
  change
    fibreProjection C ε (rotatedLevel ρ r) _
          (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p) =
        fibreProjection C ε (rotatedLevel ρ r) _
          (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r q) ↔
      _
  rw [fibreProjection_eq_iff]
  apply exists_congr
  intro v
  rw [← varyingComplexPhaseHomeomorph_deck C ρ hρ ε hε hε1 hρε hC hRC hRD r v q]
  exact
    ⟨fun h =>
      (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).injective (Subtype.ext h),
      fun h =>
      congrArg
        (fun z : CuspHoneycomb.PhasePlane =>
          (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r z : ToricSpace.Space))
        h⟩

private def
    CuspSpecialization.varyingComplexSourceHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) :
    SourceModel (C 0) ≃ₜ CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r) :=
  CuspHoneycombClosedCover.quotientHomeomorph (sourceProjection (C 0))
    (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r)
    (sourceProjection_isQuotientMap (C 0))
    (varyingComplexFibreMap_isQuotientMap C ρ hρ ε hε hε1 hρε hC hRC hRD r)
    (fun p q =>
      (sourceProjection_eq_iff (C 0) p q).trans
        (varyingComplexFibreMap_eq_iff C ρ hρ ε hε hε1 hρε hC hRC hRD r p q).symm)

@[simp]
private theorem CuspSpecialization.varyingComplexSourceHomeomorph_projection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r (sourceProjection (C 0) p) =
      varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p :=
  CuspHoneycombClosedCover.quotientHomeomorph_apply _ _ _ _ _ p

private def CuspSpecialization.varyingComplexPhaseLevelHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) :
    CuspHoneycomb.PhasePlane ≃ₜ CuspControlledRetraction.ToricLevel η (rotatedLevel ρ r) :=
  (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).trans
    (toricFibreLevelHomeomorph η (rotatedLevel ρ r) (rotatedLevel_norm_le ρ r hρ.le η hρη))

private theorem CuspSpecialization.varyingComplexFibreMap_eq_levelProjection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (p : CuspHoneycomb.PhasePlane) :
    varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p =
      CuspControlledRetraction.quotientLevelFibreHomeomorph C ε η (rotatedLevel ρ r)
        (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (CuspControlledRetraction.levelProjection C hηε (rotatedLevel ρ r)
          (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p)) :=
  fibreProjection_eq_levelProjection C ε (rotatedLevel ρ r) (rotatedLevel_norm_lt ρ r hρ.le ε hρε)
    η hηε (rotatedLevel_norm_le ρ r hρ.le η hρη)
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p)

private theorem CuspSpecialization.puncturedStraightening_varyingComplexPhase
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (p : CuspHoneycomb.PhasePlane) :
    CuspControlledRetraction.puncturedStraightening C η
        (toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
          (rotatedLevel_norm_le ρ r hρ.le η hρη)
          (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p)) =
      toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
        (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
          (CuspPositive.smallDrift_positiveTwist (C 0) hRD) r p) := by
  apply Subtype.ext
  apply Subtype.ext
  exact varyingComplexPhaseHomeomorph_straightened C ρ hρ ε hε hε1 hρε hC hRC hRD r p

private theorem CuspSpecialization.prescribedFibreUpstairs_varyingComplexPhaseLevel
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (p : CuspHoneycomb.PhasePlane) :
    CuspControlledRetraction.prescribedFibreUpstairs C ε hε η (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ)
        (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p) =
      CuspCollapse.centralProject C ε hε (rotatingCentralPoint (C 0) r p) := by
  change
    CuspCollapse.centralProject C ε hε
        (CuspControlledRetraction.prescribedCollapse (C 0) η
          (CuspControlledRetraction.puncturedStraightening C η
            (toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
              (rotatedLevel_norm_le ρ r hρ.le η hρη)
              (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p)))) =
      _
  rw [puncturedStraightening_varyingComplexPhase C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p,
    prescribedCollapse_complexPhase (C 0) ρ hρ ε hε1 hρε
      (CuspPositive.smallDrift_positiveTwist (C 0) hRD) r η hρη p]

private theorem CuspSpecialization.prescribedFibreUpstairs_varyingComplex_compatible
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε)
    (x y : CuspControlledRetraction.ToricLevel η (rotatedLevel ρ r))
    (hxy :
      CuspControlledRetraction.levelProjection C hηε (rotatedLevel ρ r) x =
        CuspControlledRetraction.levelProjection C hηε (rotatedLevel ρ r) y) :
    CuspControlledRetraction.prescribedFibreUpstairs C ε hε η (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) x =
      CuspControlledRetraction.prescribedFibreUpstairs C ε hε η (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) y := by
  obtain ⟨p, rfl⟩ :=
    (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη).surjective x
  obtain ⟨q, rfl⟩ :=
    (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη).surjective y
  have hf :
    varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p =
      varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r q := by
    rw [varyingComplexFibreMap_eq_levelProjection C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε p,
      varyingComplexFibreMap_eq_levelProjection C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε q, hxy]
  obtain ⟨v, hv⟩ := (varyingComplexFibreMap_eq_iff C ρ hρ ε hε hε1 hρε hC hRC hRD r p q).mp hf
  rw [prescribedFibreUpstairs_varyingComplexPhaseLevel,
    prescribedFibreUpstairs_varyingComplexPhaseLevel, ← hv, centralRotation_sourceDeck]

private theorem CuspSpecialization.prescribedActualFibreCollapse_varyingComplexFibreMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (p : CuspHoneycomb.PhasePlane) :
    CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p) =
      CuspCollapse.centralProject C ε hε (rotatingCentralPoint (C 0) r p) := by
  rw [CuspControlledRetraction.prescribedActualFibreCollapse, Function.comp_apply,
    varyingComplexFibreMap_eq_levelProjection C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε p,
    Homeomorph.symm_apply_apply]
  change
    CuspControlledRetraction.levelDescend C hηε (rotatedLevel ρ r)
        (CuspControlledRetraction.prescribedFibreUpstairs C ε hε η (rotatedLevel ρ r)
          (rotatedLevel_ne_zero ρ r hρ))
        (CuspControlledRetraction.levelProjection C hηε (rotatedLevel ρ r)
          (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p)) =
      _
  rw [CuspControlledRetraction.levelDescend_levelProjection C hηε (rotatedLevel ρ r) _
      (prescribedFibreUpstairs_varyingComplex_compatible C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη
        hηε)]
  exact prescribedFibreUpstairs_varyingComplexPhaseLevel C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p

private theorem CuspSpecialization.prescribedActualFibreCollapse_varyingComplexSourceHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (q : SourceModel (C 0)) :
    CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r q) =
      sourceRotation C ε hε r q := by
  obtain ⟨p, rfl⟩ := sourceProjection_surjective (C 0) q
  rw [varyingComplexSourceHomeomorph_projection, sourceRotation_projection]
  exact
    prescribedActualFibreCollapse_varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη
      hηε p

private theorem CuspSpecialization.prescribedActualFibreCollapse_varyingComplex_continuous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    Continuous
      (CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)) := by
  apply
    (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
          r).isQuotientMap |>.continuous_iff.mpr
  have he :
    CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
          (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη) ∘
        varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r =
      sourceRotation C ε hε r :=
    funext
      (prescribedActualFibreCollapse_varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
        r η hρη hηε)
  rw [he]
  exact (sourceRotation C ε hε r).continuous

private def CuspSpecialization.varyingComplexCollapseMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    C(CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r),
      CuspRetraction.QuotientCentralFibre C ε)
    where
  toFun :=
    CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
      (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
  continuous_toFun :=
    prescribedActualFibreCollapse_varyingComplex_continuous C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη
      hηε

private def CuspSpecialization.sourcePhaseArgument (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y : (CuspHoneycombTiling.Plane)) : (CuspHoneycombTiling.Plane) :=
  (fun i j => (C₀ i j).re) *ᵥ (-ToricSpace.realCuspVector y)

private theorem CuspSpecialization.sourcePhaseArgument_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y z : (CuspHoneycombTiling.Plane)) :
    sourcePhaseArgument C₀ (y + z) = sourcePhaseArgument C₀ y + sourcePhaseArgument C₀ z := by
  funext i
  simp [sourcePhaseArgument, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    ToricSpace.realCuspVector, mul_add, add_comm, add_left_comm, add_assoc]

@[simp]
private theorem CuspSpecialization.sourcePhaseArgument_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    sourcePhaseArgument C₀ 0 = 0 := by
  funext i
  simp [sourcePhaseArgument, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    ToricSpace.realCuspVector]

private theorem CuspSpecialization.sourcePhaseArgument_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (sourcePhaseArgument C₀) := by
  unfold sourcePhaseArgument
  simp only [ToricSpace.realCuspVector]
  fun_prop

private theorem
    CuspSpecialization.sourcePhaseArgument_lattice_cuspVector (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (i : Fin 2) :
    sourcePhaseArgument C₀ (CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) i =
      ((C₀ *ᵥ (fun j => (v j : ℂ))) i).re := by
  simp [sourcePhaseArgument, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    ToricSpace.realCuspVector, CuspHoneycombTiling.latticePoint, ToricSpace.cuspVector,
    Complex.mul_re, add_comm]

private def CuspSpecialization.sourcePhaseCharacter (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y : (CuspHoneycombTiling.Plane)) : ToricSpace.CompactFibreTorus := fun i =>
  Circle.exp (2 * Real.pi * sourcePhaseArgument C₀ y i)

private theorem CuspSpecialization.sourcePhaseCharacter_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (sourcePhaseCharacter C₀) := by
  apply continuous_pi
  intro i
  exact
    Circle.exp.continuous.comp
      (continuous_const.mul ((continuous_apply i).comp (sourcePhaseArgument_continuous C₀)))

@[simp]
private theorem CuspSpecialization.sourcePhaseCharacter_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    sourcePhaseCharacter C₀ 0 = 1 := by
  funext i
  simp [sourcePhaseCharacter]

private theorem CuspSpecialization.sourcePhaseCharacter_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y z : (CuspHoneycombTiling.Plane)) :
    sourcePhaseCharacter C₀ (y + z) = sourcePhaseCharacter C₀ y * sourcePhaseCharacter C₀ z := by
  funext i
  simp only [sourcePhaseCharacter, sourcePhaseArgument_add, Pi.add_apply, mul_add, Circle.exp_add,
    Pi.mul_apply]

@[simp]
private theorem
    CuspSpecialization.sourcePhaseCharacter_lattice_cuspVector (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) :
    sourcePhaseCharacter C₀ (CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      CuspCollapse.deckFibrePhase C₀ v := by
  funext i
  rw [sourcePhaseCharacter, sourcePhaseArgument_lattice_cuspVector, CuspCollapse.deckFibrePhase,
    CuspPositive.frozenPhaseCoordinate_eq_exp]

private theorem CuspSpecialization.sourcePhaseCharacter_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (y : (CuspHoneycombTiling.Plane)) :
    sourcePhaseCharacter C₀ (y + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      CuspCollapse.deckFibrePhase C₀ v * sourcePhaseCharacter C₀ y := by
  rw [sourcePhaseCharacter_add, sourcePhaseCharacter_lattice_cuspVector, mul_comm]

private def CuspSpecialization.sourcePhaseShear (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    CuspHoneycomb.PhasePlane ≃ₜ CuspHoneycomb.PhasePlane
    where
  toFun p := (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹, p.2)
  invFun p := (p.1 * sourcePhaseCharacter C₀ p.2, p.2)
  left_inv p := by simp only [mul_assoc, inv_mul_cancel, mul_one, Prod.eta]
  right_inv p := by simp only [mul_inv_cancel_right, Prod.eta]
  continuous_toFun :=
    (continuous_fst.mul ((sourcePhaseCharacter_continuous C₀).comp continuous_snd).inv).prodMk
      continuous_snd
  continuous_invFun :=
    (continuous_fst.mul ((sourcePhaseCharacter_continuous C₀).comp continuous_snd)).prodMk
      continuous_snd

@[simp]
private theorem CuspSpecialization.sourcePhaseShear_apply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CuspHoneycomb.PhasePlane) :
    sourcePhaseShear C₀ p = (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹, p.2) :=
  rfl

private theorem
    CuspSpecialization.sourcePhaseShear_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (p : CuspHoneycomb.PhasePlane) :
    sourcePhaseShear C₀ (CuspHoneycomb.honeycombDeckMap C₀ v p) =
      ((sourcePhaseShear C₀ p).1,
        p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) := by
  simp only [sourcePhaseShear_apply, CuspHoneycomb.honeycombDeckMap, sourcePhaseCharacter_deck]
  apply Prod.ext
  · simp only [mul_inv_rev]
    calc
      (CuspCollapse.deckFibrePhase C₀ v * p.1) *
            ((sourcePhaseCharacter C₀ p.2)⁻¹ * (CuspCollapse.deckFibrePhase C₀ v)⁻¹) =
          (CuspCollapse.deckFibrePhase C₀ v * (CuspCollapse.deckFibrePhase C₀ v)⁻¹) *
            (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹) := by ac_rfl
      _ = p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹ := by rw [mul_inv_cancel, one_mul]
  · rfl

private def CuspSpecialization.sourceBaseMarking :
    (CuspHoneycombTiling.Plane) ≃ₜ (CuspHoneycombTiling.Plane)
    where
  toFun y := -ToricSpace.realCuspVector y
  invFun y := ToricSpace.realCuspVector y
  left_inv
    y := by
    funext i
    fin_cases i <;> simp [ToricSpace.realCuspVector]
  right_inv
    y := by
    funext i
    fin_cases i <;> simp [ToricSpace.realCuspVector]
  continuous_toFun := by simp only [ToricSpace.realCuspVector]; fun_prop
  continuous_invFun := by simp only [ToricSpace.realCuspVector]; fun_prop

@[simp]
private theorem CuspSpecialization.sourceBaseMarking_apply (y : (CuspHoneycombTiling.Plane)) :
    sourceBaseMarking y = -ToricSpace.realCuspVector y :=
  rfl

private theorem CuspSpecialization.sourceBaseMarking_add (y z : (CuspHoneycombTiling.Plane)) :
    sourceBaseMarking (y + z) = sourceBaseMarking y + sourceBaseMarking z := by
  simp only [sourceBaseMarking_apply, map_add, neg_add]

private theorem CuspSpecialization.sourceBaseMarking_lattice_cuspVector (v : Fin 2 → ℤ) :
    sourceBaseMarking (CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      CuspHoneycombTiling.latticePoint v := by
  funext i
  fin_cases i <;>
    simp [sourceBaseMarking_apply, ToricSpace.realCuspVector, CuspHoneycombTiling.latticePoint,
      ToricSpace.cuspVector]

private theorem CuspSpecialization.sourceBaseMarking_deck (v : Fin 2 → ℤ)
    (y : (CuspHoneycombTiling.Plane)) :
    sourceBaseMarking (y + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      sourceBaseMarking y + CuspHoneycombTiling.latticePoint v := by
  rw [sourceBaseMarking_add, sourceBaseMarking_lattice_cuspVector]

private def CuspSpecialization.sourceMarkedShear (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    CuspHoneycomb.PhasePlane ≃ₜ CuspHoneycomb.PhasePlane :=
  (sourcePhaseShear C₀).trans
    ((Homeomorph.refl ToricSpace.CompactFibreTorus).prodCongr sourceBaseMarking)

private theorem
    CuspSpecialization.sourceMarkedShear_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (p : CuspHoneycomb.PhasePlane) :
    sourceMarkedShear C₀ (CuspHoneycomb.honeycombDeckMap C₀ v p) =
      ((sourceMarkedShear C₀ p).1,
        (sourceMarkedShear C₀ p).2 + CuspHoneycombTiling.latticePoint v) := by
  change
    ((sourcePhaseShear C₀ (CuspHoneycomb.honeycombDeckMap C₀ v p)).1,
        sourceBaseMarking (CuspHoneycomb.honeycombDeckMap C₀ v p).2) =
      _
  rw [sourcePhaseShear_deck]
  change
    ((sourceMarkedShear C₀ p).1,
        sourceBaseMarking (p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v))) =
      _
  rw [sourceBaseMarking_deck]
  rfl

public
theorem CuspSpecialization.sourceCoordinateProjection_isOpenQuotientMap :
    IsOpenQuotientMap (PeriodTorusHigherHomology.coordinateProjection 2) := by
  exact
    IsOpenQuotientMap.piMap
      (fun _ : Fin 2 =>
        (QuotientAddGroup.isOpenQuotientMap_mk : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ))))

private theorem
    CuspSpecialization.sourceCoordinateProjection_eq_iff (y z : (CuspHoneycombTiling.Plane)) :
    PeriodTorusHigherHomology.coordinateProjection 2 y =
        PeriodTorusHigherHomology.coordinateProjection 2 z ↔
      ∃ v : Fin 2 → ℤ, y = z + CuspHoneycombTiling.latticePoint v := by
  constructor
  · intro h
    have hz : PeriodTorusHigherHomology.coordinateProjection 2 (y - z) = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨v, hv⟩ := (PeriodTorusHigherHomology.coordinateProjection_eq_zero_iff 2 _).mp hz
    refine ⟨v, ?_⟩
    change y - z = CuspHoneycombTiling.latticePoint v at hv
    calc
      y = (y - z) + z := (sub_add_cancel y z).symm
      _ = z + CuspHoneycombTiling.latticePoint v := by rw [hv, add_comm]
  · rintro ⟨v, rfl⟩
    have hz :
      PeriodTorusHigherHomology.coordinateProjection 2 (CuspHoneycombTiling.latticePoint v) = 0 :=
      (PeriodTorusHigherHomology.coordinateProjection_eq_zero_iff 2
            (CuspHoneycombTiling.latticePoint v)).mpr
        ⟨v, rfl⟩
    rw [map_add, hz, add_zero]

private def CuspSpecialization.sourceProductCoordinates (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    CuspHoneycomb.PhasePlane →
      ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2 :=
  Prod.map id (PeriodTorusHigherHomology.coordinateProjection 2) ∘ sourceMarkedShear C₀

private theorem CuspSpecialization.sourceProductCoordinates_isOpenQuotientMap
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) : IsOpenQuotientMap (sourceProductCoordinates C₀) :=
  (IsOpenQuotientMap.id.prodMap sourceCoordinateProjection_isOpenQuotientMap).comp
    (sourceMarkedShear C₀).isOpenQuotientMap

private theorem
    CuspSpecialization.sourceProductCoordinates_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Surjective (sourceProductCoordinates C₀) :=
  (sourceProductCoordinates_isOpenQuotientMap C₀).surjective

private theorem CuspSpecialization.sourceProductCoordinates_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (p : CuspHoneycomb.PhasePlane) :
    sourceProductCoordinates C₀ (CuspHoneycomb.honeycombDeckMap C₀ v p) =
      sourceProductCoordinates C₀ p := by
  change
    Prod.map id (PeriodTorusHigherHomology.coordinateProjection 2)
        (sourceMarkedShear C₀ (CuspHoneycomb.honeycombDeckMap C₀ v p)) =
      _
  rw [sourceMarkedShear_deck]
  apply Prod.ext
  · rfl
  · change
      PeriodTorusHigherHomology.coordinateProjection 2
          ((sourceMarkedShear C₀ p).2 + CuspHoneycombTiling.latticePoint v) =
        PeriodTorusHigherHomology.coordinateProjection 2 (sourceMarkedShear C₀ p).2
    exact (sourceCoordinateProjection_eq_iff _ _).mpr ⟨v, rfl⟩

private theorem CuspSpecialization.sourceProductCoordinates_eq_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p q : CuspHoneycomb.PhasePlane) :
    sourceProductCoordinates C₀ p = sourceProductCoordinates C₀ q ↔
      ∃ v : Fin 2 → ℤ, CuspHoneycomb.honeycombDeckMap C₀ v q = p := by
  constructor
  · intro h
    have hphase : (sourceMarkedShear C₀ p).1 = (sourceMarkedShear C₀ q).1 :=
      congrArg
        (fun x : ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2 => x.1) h
    have hbase :
      PeriodTorusHigherHomology.coordinateProjection 2 (sourceMarkedShear C₀ p).2 =
        PeriodTorusHigherHomology.coordinateProjection 2 (sourceMarkedShear C₀ q).2 :=
      congrArg
        (fun x : ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2 => x.2) h
    obtain ⟨v, hv⟩ := (sourceCoordinateProjection_eq_iff _ _).mp hbase
    refine ⟨v, (sourceMarkedShear C₀).injective ?_⟩
    rw [sourceMarkedShear_deck]
    apply Prod.ext
    · exact hphase.symm
    · exact hv.symm
  · rintro ⟨v, hv⟩
    rw [← hv, sourceProductCoordinates_deck]

private def CuspSpecialization.sourceProductMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    SourceModel C₀ → ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2 :=
  Quotient.lift (sourceProductCoordinates C₀)
    (by
      rintro p q ⟨v, hv⟩
      rw [← hv]
      exact sourceProductCoordinates_deck C₀ v q)

private theorem CuspSpecialization.sourceProductMap_injective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Injective (sourceProductMap C₀) := by
  intro x y h
  obtain ⟨p, rfl⟩ := sourceProjection_surjective C₀ x
  obtain ⟨q, rfl⟩ := sourceProjection_surjective C₀ y
  exact (sourceProjection_eq_iff C₀ p q).mpr ((sourceProductCoordinates_eq_iff C₀ p q).mp h)

private theorem CuspSpecialization.sourceProductMap_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Surjective (sourceProductMap C₀) := by
  intro x
  obtain ⟨p, hp⟩ := sourceProductCoordinates_surjective C₀ x
  exact ⟨sourceProjection C₀ p, hp⟩

private theorem CuspSpecialization.sourceProductMap_isQuotientMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Topology.IsQuotientMap (sourceProductMap C₀) :=
  (sourceProjection_isQuotientMap C₀).of_comp_isQuotientMap
    (sourceProductCoordinates_isOpenQuotientMap C₀).isQuotientMap

private def CuspSpecialization.sourceProductHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    SourceModel C₀ ≃ₜ ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2 :=
  (Equiv.ofBijective (sourceProductMap C₀)
        ⟨sourceProductMap_injective C₀, sourceProductMap_surjective C₀⟩).toHomeomorph
    (fun _ => (sourceProductMap_isQuotientMap C₀).isOpen_preimage)

@[simp]
private theorem
    CuspSpecialization.sourceProductHomeomorph_projection (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CuspHoneycomb.PhasePlane) :
    sourceProductHomeomorph C₀ (sourceProjection C₀ p) =
      (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹,
        PeriodTorusHigherHomology.coordinateProjection 2 (-ToricSpace.realCuspVector p.2)) :=
  rfl

private theorem CuspSpecialization.sourceProductHomeomorph_symm_coordinateProjection
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (u : ToricSpace.CompactFibreTorus)
    (y : (CuspHoneycombTiling.Plane)) :
    (sourceProductHomeomorph C₀).symm (u, PeriodTorusHigherHomology.coordinateProjection 2 y) =
      sourceProjection C₀
        (u * sourcePhaseCharacter C₀ (ToricSpace.realCuspVector y),
          ToricSpace.realCuspVector y) := by
  apply (sourceProductHomeomorph C₀).injective
  rw [Homeomorph.apply_symm_apply]
  change
    (u, PeriodTorusHigherHomology.coordinateProjection 2 y) =
      sourceProductCoordinates C₀ ((sourceMarkedShear C₀).symm (u, y))
  unfold sourceProductCoordinates
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  rfl

private def
    CuspSpecialization.productCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
      CuspRetraction.QuotientCentralFibre C ε) :=
  (sourceCollapse C ε hε).comp
    ((sourceProductHomeomorph (C 0)).symm :
      C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
        SourceModel (C 0)))

private theorem
    CuspSpecialization.productCollapse_coordinateProjection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (y : (CuspHoneycombTiling.Plane)) :
    productCollapse C ε hε (u, PeriodTorusHigherHomology.coordinateProjection 2 y) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (u * sourcePhaseCharacter (C 0) (ToricSpace.realCuspVector y),
          ToricSpace.realCuspVector y) := by
  change
    sourceCollapse C ε hε
        ((sourceProductHomeomorph (C 0)).symm
          (u, PeriodTorusHigherHomology.coordinateProjection 2 y)) =
      _
  rw [sourceProductHomeomorph_symm_coordinateProjection, sourceCollapse_projection]

private def
    CuspSpecialization.productRotation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (r : ℝ) :
    C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
      CuspRetraction.QuotientCentralFibre C ε) :=
  (sourceRotation C ε hε r).comp
    ((sourceProductHomeomorph (C 0)).symm :
      C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
        SourceModel (C 0)))

private def CuspSpecialization.productRotationHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (r : ℝ) : (productCollapse C ε hε).Homotopy (productRotation C ε hε r) :=
  (sourceRotationHomotopy C ε hε r).compContinuousMap
    ((sourceProductHomeomorph (C 0)).symm :
      C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
        SourceModel (C 0)))

private theorem
    CuspSpecialization.productRotation_homologyMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (r : ℝ) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (productRotation C ε hε r) n =
      SingularMayerVietoris.singularHomologyMap (productCollapse C ε hε) n :=
  (PeriodTorusHigherHomology.homotopy_homologyMap (productRotationHomotopy C ε hε r) n).symm

private def
    CuspSpecialization.varyingComplexProductFibreHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) :
    (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
      CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r) :=
  (sourceProductHomeomorph (C 0)).symm.trans
    (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r)

private theorem
    CuspSpecialization.prescribedActualFibreCollapse_varyingComplexProductFibreHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε)
    (p : ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :
    CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r p) =
      productRotation C ε hε r p :=
  prescribedActualFibreCollapse_varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η
    hρη hηε ((sourceProductHomeomorph (C 0)).symm p)

private theorem CuspSpecialization.varyingComplexCollapseMap_comp_product
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    (varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε).comp
        (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r :
          C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
            CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r))) =
      productRotation C ε hε r :=
  ContinuousMap.ext
    (prescribedActualFibreCollapse_varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC
      hRD r η hρη hηε)

private def
    CuspSpecialization.varyingComplexProductCollapseHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    (productCollapse C ε hε).Homotopy
      ((varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε).comp
        (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r :
          C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
            CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r)))) := by
  rw [varyingComplexCollapseMap_comp_product]
  exact productRotationHomotopy C ε hε r

private theorem CuspSpecialization.varyingComplexProductCollapseMap_homology
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) n) :
    SingularMayerVietoris.singularHomologyMap
        (varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε) n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r) n a) =
      SingularMayerVietoris.singularHomologyMap (productCollapse C ε hε) n a := by
  change
    (SingularMayerVietoris.singularHomologyMap
            (varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε) n).comp
        (SingularMayerVietoris.singularHomologyMap
          (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r :
            C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
              CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r)))
          n)
        a =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp,
    varyingComplexCollapseMap_comp_product, productRotation_homologyMap]

private def CuspSpecialization.argumentTurns (t : ℂ) : ℝ :=
  t.arg / (2 * Real.pi)

private theorem CuspSpecialization.rotatedLevel_norm_argumentTurns (t : ℂ) :
    rotatedLevel ‖t‖ (argumentTurns t) = t := by
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have he : 2 * Real.pi * (t.arg / (2 * Real.pi)) = t.arg := mul_div_cancel₀ t.arg hπ
  rw [rotatedLevel, argumentTurns, he, Circle.coe_exp, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I t

private def CuspSpecialization.IsPrescribedProductModel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (t : ℂ) (ht : t ≠ 0)
    (e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C ε t) :
    Prop :=
  ∀ (η : ℝ) (htη : ‖t‖ ≤ η) (hηε : η < ε),
    ∃ hc :
      Continuous (CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε t ht htη),
      (productCollapse C ε hε).Homotopic
          ((⟨CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε t ht htη, hc⟩ :
                C(CuspControlledRetraction.ActualQuotientFibre C ε t,
                  CuspRetraction.QuotientCentralFibre C ε)).comp
            (e :
              C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
                CuspControlledRetraction.ActualQuotientFibre C ε t))) ∧
        ∀ (n : ℕ)
          (a :
            SingularMayerVietoris.SingularHomology
              (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) n),
          SingularMayerVietoris.singularHomologyMap
              (⟨CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε t ht htη, hc⟩ :
                C(CuspControlledRetraction.ActualQuotientFibre C ε t,
                  CuspRetraction.QuotientCentralFibre C ε))
              n (PeriodTorusHigherHomology.homeomorphHomologyEquiv e n a) =
            SingularMayerVietoris.singularHomologyMap (productCollapse C ε hε) n a

private theorem CuspSpecialization.varyingComplexProductFibreHomeomorph_isPrescribedProductModel
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ < ε) (r : ℝ) :
    IsPrescribedProductModel C ε hε (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
      (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r) := by
  intro η htη hηε
  have hρη : ρ ≤ η := by rwa [norm_rotatedLevel ρ r hρ.le] at htη
  refine
    ⟨prescribedActualFibreCollapse_varyingComplex_continuous C ρ hρ ε hε hε1 hρε hC hRC hRD r η
        hρη hηε,
      ?_, ?_⟩
  · exact ⟨varyingComplexProductCollapseHomotopy C ε hε ρ hρ hε1 hρε hC hRC hRD r η hρη hηε⟩
  · intro n a
    exact varyingComplexProductCollapseMap_homology C ε hε ρ hρ hε1 hρε hC hRC hRD r η hρη hηε n a

private theorem CuspSpecialization.exists_product_model_at_nonzero_level
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (t : ℂ) (ht : t ≠ 0) (htε : ‖t‖ < ε) :
    ∃ e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C ε t,
      IsPrescribedProductModel C ε hε t ht e := by
  have hρ : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hm :
    ∃ e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ‖t‖ (argumentTurns t)),
      IsPrescribedProductModel C ε hε (rotatedLevel ‖t‖ (argumentTurns t))
        (rotatedLevel_ne_zero ‖t‖ (argumentTurns t) hρ) e :=
    ⟨varyingComplexProductFibreHomeomorph C ε hε ‖t‖ hρ hε1 htε hC hRC hRD (argumentTurns t),
      varyingComplexProductFibreHomeomorph_isPrescribedProductModel C ε hε hε1 hC hRC hRD ‖t‖ hρ
        htε (argumentTurns t)⟩
  have transfer (u : ℂ) (hu : u ≠ 0) (hut : u = t)
    (huModel :
      ∃ e :
        (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
          CuspControlledRetraction.ActualQuotientFibre C ε u,
        IsPrescribedProductModel C ε hε u hu e) :
    ∃ e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C ε t,
      IsPrescribedProductModel C ε hε t ht e := by
    subst u
    exact huModel
  exact transfer _ _ (rotatedLevel_norm_argumentTurns t) hm

@[simp]
private theorem CuspCentralHomology.fibreRadiusHomeomorph_fibreProjection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (t : ℂ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (htδ : ‖t‖ < δ)
    (x : CuspSpecialization.ToricFibre t) :
    fibreRadiusHomeomorph C r δ t hδr hC htδ (CuspSpecialization.fibreProjection C δ t htδ x) =
      CuspSpecialization.fibreProjection C r t (htδ.trans_le hδr) x := by
  apply Subtype.ext
  change
    (openQuotientRadiusHomeomorph C hδr hC (CuspSpecialization.fibreProjection C δ t htδ x).1).1 =
      (CuspSpecialization.fibreProjection C r t (htδ.trans_le hδr) x).1
  simp only [CuspSpecialization.fibreProjection_coe, openQuotientRadiusHomeomorph_quotientMap,
    openQuotientMap]

@[simp]
private theorem CuspCentralHomology.centralRadiusHomeomorph_centralProject
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ)
    (x : CuspRetraction.CentralFibre) :
    centralRadiusHomeomorph C r δ hδr hC hδ (CuspCollapse.centralProject C δ hδ x) =
      CuspCollapse.centralProject C r (hδ.trans_le hδr) x := by
  apply Subtype.ext
  change
    (openQuotientRadiusHomeomorph C hδr hC (CuspCollapse.centralProject C δ hδ x).1).1 =
      (CuspCollapse.centralProject C r (hδ.trans_le hδr) x).1
  simp only [CuspCollapse.centralProject, openQuotientRadiusHomeomorph_quotientMap,
    openQuotientMap]

@[simp]
private theorem CuspCentralHomology.centralRadiusHomeomorph_centralCollapseMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ)
    (p : CuspCollapse.PhasePositiveSpace) :
    centralRadiusHomeomorph C r δ hδr hC hδ (CuspCollapse.centralCollapseMap C δ hδ p) =
      CuspCollapse.centralCollapseMap C r (hδ.trans_le hδr) p :=
  centralRadiusHomeomorph_centralProject C r δ hδr hC hδ (CuspCollapse.centralPolarMap p)

@[simp]
private theorem CuspCentralHomology.centralRadiusHomeomorph_honeycombCollapseMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ)
    (p : CuspHoneycomb.PhasePlane) :
    centralRadiusHomeomorph C r δ hδr hC hδ (CuspHoneycomb.honeycombCollapseMap C δ hδ p) =
      CuspHoneycomb.honeycombCollapseMap C r (hδ.trans_le hδr) p :=
  centralRadiusHomeomorph_centralCollapseMap C r δ hδr hC hδ
    (CuspHoneycomb.phaseCoordinatesHomeomorph (C 0) p)

@[simp]
private theorem CuspCentralHomology.centralRadiusHomeomorph_sourceCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ)
    (q : CuspSpecialization.SourceModel (C 0)) :
    centralRadiusHomeomorph C r δ hδr hC hδ (CuspSpecialization.sourceCollapse C δ hδ q) =
      CuspSpecialization.sourceCollapse C r (hδ.trans_le hδr) q := by
  induction q using Quotient.inductionOn with
  | h p => exact centralRadiusHomeomorph_honeycombCollapseMap C r δ hδr hC hδ p

@[simp]
private theorem CuspCentralHomology.centralRadiusHomeomorph_productCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ)
    (p : ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :
    centralRadiusHomeomorph C r δ hδr hC hδ (CuspSpecialization.productCollapse C δ hδ p) =
      CuspSpecialization.productCollapse C r (hδ.trans_le hδr) p :=
  centralRadiusHomeomorph_sourceCollapse C r δ hδr hC hδ
    ((CuspSpecialization.sourceProductHomeomorph (C 0)).symm p)

private theorem CuspCentralHomology.centralRadiusHomeomorph_comp_productCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ) :
    (centralRadiusHomeomorph C r δ hδr hC hδ :
            C(CuspRetraction.QuotientCentralFibre C δ,
              CuspRetraction.QuotientCentralFibre C r)).comp
        (CuspSpecialization.productCollapse C δ hδ) =
      CuspSpecialization.productCollapse C r (hδ.trans_le hδr) := by
  apply ContinuousMap.ext
  intro p
  exact centralRadiusHomeomorph_productCollapse C r δ hδr hC hδ p

private def
    CuspControlledRetraction.puncturedPositiveTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (q : PuncturedPositiveTube η) : PuncturedPositiveTube η :=
  ⟨CuspPositive.closedPositiveTranslate C₀ η v q.1,
    by
    change
      ToricSpace.time
          (ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v
            (q.1.1 : ToricSpace.Space)) ≠
        0
    rw [ToricSpace.time_twistedTranslate]
    exact q.2⟩

private def
    CuspControlledRetraction.puncturedFrozenTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (x : PuncturedClosedTube η) : PuncturedClosedTube η :=
  ⟨CuspRetraction.closedTranslate (fun _ => C₀) η v x.1,
    by
    change
      ToricSpace.time (ToricSpace.twistedTranslate (fun _ => C₀) v (x.1 : ToricSpace.Space)) ≠ 0
    rw [ToricSpace.time_twistedTranslate]
    exact x.2⟩

private theorem
    CuspControlledRetraction.puncturedFrozenTranslate_polar (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (v : Fin 2 → ℤ) (u : ToricSpace.CompactTorus) (q : PuncturedPositiveTube η) :
    puncturedFrozenTranslate C₀ η v (puncturedPolarMap η (u, q)) =
      puncturedPolarMap η
        (CuspPositive.phaseTransform C₀ v u, puncturedPositiveTranslate C₀ η v q) :=
  Subtype.ext
    (Subtype.ext (CuspPositive.twistedTranslate_constant_polar C₀ v u (q.1.1 : ToricSpace.Space)))

private theorem CuspControlledRetraction.prescribedPositiveCollapse_equivariant
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (v : Fin 2 → ℤ)
    (q : PuncturedPositiveTube η) :
    prescribedPositiveCollapse C₀ η (puncturedPositiveTranslate C₀ η v q) =
      CuspCollapse.positiveCentralTranslate C₀ v (prescribedPositiveCollapse C₀ η q) := by
  change
    CuspHoneycomb.honeycombHomeomorph C₀
        (normalizedPosition C₀
          ((CuspPositive.closedPositiveTranslate C₀ η v q.1).1 : ToricSpace.Space)) =
      CuspCollapse.positiveCentralTranslate C₀ v
        (CuspHoneycomb.honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1.1 : ToricSpace.Space)))
  rw [normalizedPosition_closedPositive_twistedTranslate C₀ hε1 hR hηε v q.2,
    CuspHoneycomb.honeycombHomeomorph_equivariant]

private theorem CuspControlledRetraction.prescribedCollapse_frozen_equivariant
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (v : Fin 2 → ℤ)
    (x : PuncturedClosedTube η) :
    (prescribedCollapse C₀ η (puncturedFrozenTranslate C₀ η v x) : ToricSpace.Space) =
      ToricSpace.twistedTranslate (fun _ => C₀) v
        (prescribedCollapse C₀ η x : ToricSpace.Space) := by
  obtain ⟨⟨u, q⟩, rfl⟩ := puncturedPolarMap_surjective η x
  rw [puncturedFrozenTranslate_polar, prescribedCollapse_puncturedPolarMap,
    prescribedCollapse_puncturedPolarMap]
  change
    ToricSpace.compactTorusAction (CuspPositive.phaseTransform C₀ v u)
        ((prescribedPositiveCollapse C₀ η (puncturedPositiveTranslate C₀ η v q)).1 :
          ToricSpace.Space) =
      ToricSpace.twistedTranslate (fun _ => C₀) v
        (ToricSpace.compactTorusAction u
          ((prescribedPositiveCollapse C₀ η q).1 : ToricSpace.Space))
  rw [prescribedPositiveCollapse_equivariant C₀ hε1 hR hηε]
  exact
    (CuspPositive.twistedTranslate_constant_polar C₀ v u
        ((prescribedPositiveCollapse C₀ η q).1 : ToricSpace.Space)).symm

private def CuspSpecialization.puncturedTwistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (x : CuspControlledRetraction.PuncturedClosedTube η) :
    CuspControlledRetraction.PuncturedClosedTube η :=
  ⟨CuspRetraction.closedTranslate C η v x.1,
    by
    change ToricSpace.time (ToricSpace.twistedTranslate C v (x.1 : ToricSpace.Space)) ≠ 0
    rw [ToricSpace.time_twistedTranslate]
    exact x.2⟩

private theorem CuspSpecialization.puncturedStraightening_twistedTranslate
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1) (hRC : ToricSpace.SmallDrift C ε)
    (hηε : η < ε) (v : Fin 2 → ℤ) (x : CuspControlledRetraction.PuncturedClosedTube η) :
    CuspControlledRetraction.puncturedStraightening C η (puncturedTwistedTranslate C η v x) =
      CuspControlledRetraction.puncturedFrozenTranslate (C 0) η v
        (CuspControlledRetraction.puncturedStraightening C η x) := by
  apply Subtype.ext
  apply Subtype.ext
  exact CuspRetraction.changeTwist_frozen_equivariant C hε1 hRC v (x.1.2.trans_lt hηε)

private theorem
    CuspSpecialization.twistedTranslate_frozen_central (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : CuspRetraction.CentralFibre) :
    ToricSpace.twistedTranslate (CuspRetraction.frozen C) v (x : ToricSpace.Space) =
      ToricSpace.twistedTranslate C v (x : ToricSpace.Space) := by
  rw [CuspRetraction.twistedTranslate_eq_expFibreAction,
    CuspRetraction.twistedTranslate_eq_expFibreAction, x.2]
  rfl

@[simp]
private theorem
    CuspSpecialization.levelToPunctured_levelTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (t : ℂ) (ht : t ≠ 0) (v : Fin 2 → ℤ) (x : CuspControlledRetraction.ToricLevel η t) :
    CuspControlledRetraction.levelToPunctured η t ht
        (CuspControlledRetraction.levelTranslate C η t v x) =
      puncturedTwistedTranslate C η v (CuspControlledRetraction.levelToPunctured η t ht x) :=
  rfl

private theorem CuspSpecialization.straightenedPrescribedCollapse_equivariant
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1) (hRC : ToricSpace.SmallDrift C ε)
    (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε) (hηε : η < ε) (v : Fin 2 → ℤ)
    (x : CuspControlledRetraction.PuncturedClosedTube η) :
    (CuspControlledRetraction.straightenedPrescribedCollapse C η
          (puncturedTwistedTranslate C η v x) :
        ToricSpace.Space) =
      ToricSpace.twistedTranslate C v
        (CuspControlledRetraction.straightenedPrescribedCollapse C η x : ToricSpace.Space) := by
  change
    (CuspControlledRetraction.prescribedCollapse (C 0) η
          (CuspControlledRetraction.puncturedStraightening C η
            (puncturedTwistedTranslate C η v x)) :
        ToricSpace.Space) =
      ToricSpace.twistedTranslate C v
        (CuspControlledRetraction.prescribedCollapse (C 0) η
            (CuspControlledRetraction.puncturedStraightening C η x) :
          ToricSpace.Space)
  rw [puncturedStraightening_twistedTranslate C hε1 hRC hηε,
    CuspControlledRetraction.prescribedCollapse_frozen_equivariant (C 0) hε1
      (CuspPositive.smallDrift_positiveTwist (C 0) hRD) hηε]
  exact
    twistedTranslate_frozen_central C v
      (CuspControlledRetraction.prescribedCollapse (C 0) η
        (CuspControlledRetraction.puncturedStraightening C η x))

private theorem
    CuspSpecialization.prescribedFibreUpstairs_invariant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε1 : ε < 1) (hRC : ToricSpace.SmallDrift C ε)
    (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε) (hηε : η < ε) (r : ℝ) (hr : 0 < r)
    (t : ℂ) (ht : t ≠ 0) (v : Fin 2 → ℤ) (x : CuspControlledRetraction.ToricLevel η t) :
    CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht
        (CuspControlledRetraction.levelTranslate C η t v x) =
      CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht x := by
  unfold CuspControlledRetraction.prescribedFibreUpstairs
  rw [levelToPunctured_levelTranslate]
  apply (CuspCollapse.centralProject_eq_iff C r hr _ _).mpr
  exact
    ⟨v,
      (straightenedPrescribedCollapse_equivariant C hε1 hRC hRD hηε v
          (CuspControlledRetraction.levelToPunctured η t ht x)).symm⟩

private theorem
    CuspSpecialization.prescribedFibreUpstairs_compatible (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε1 : ε < 1) (hRC : ToricSpace.SmallDrift C ε)
    (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε) (hηε : η < ε) (r : ℝ) (hr : 0 < r)
    (hηr : η < r) (t : ℂ) (ht : t ≠ 0) :
    ∀ x y : CuspControlledRetraction.ToricLevel η t,
      CuspControlledRetraction.levelProjection C hηr t x =
          CuspControlledRetraction.levelProjection C hηr t y →
        CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht x =
          CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht y :=
  CuspControlledRetraction.levelProjection_fibre_compatible_of_invariant C hηr t
    (CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht)
    (prescribedFibreUpstairs_invariant C hε1 hRC hRD hηε r hr t ht)

private theorem CuspSpecialization.prescribedFibreCollapse_levelProjection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1) (hRC : ToricSpace.SmallDrift C ε)
    (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε) (hηε : η < ε) (r : ℝ) (hr : 0 < r)
    (hηr : η < r) (t : ℂ) (ht : t ≠ 0) (x : CuspControlledRetraction.ToricLevel η t) :
    CuspControlledRetraction.prescribedFibreCollapse C r hr hηr t ht
        (CuspControlledRetraction.levelProjection C hηr t x) =
      CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht x :=
  CuspControlledRetraction.levelDescend_levelProjection C hηr t
    (CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht)
    (prescribedFibreUpstairs_compatible C hε1 hRC hRD hηε r hr hηr t ht) x

private theorem CuspSpecialization.prescribedActualFibreCollapse_fibreProjection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1) (hRC : ToricSpace.SmallDrift C ε)
    (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε) (hηε : η < ε) (r : ℝ) (hr : 0 < r)
    (hηr : η < r) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η) (x : ToricFibre t) :
    CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht htη
        (fibreProjection C r t (htη.trans_lt hηr) x) =
      CuspCollapse.centralProject C r hr
        (CuspControlledRetraction.straightenedPrescribedCollapse C η
          (toricFibrePunctured η t ht htη x)) := by
  rw [fibreProjection_eq_levelProjection C r t (htη.trans_lt hηr) η hηr htη x]
  change
    CuspControlledRetraction.prescribedFibreCollapse C r hr hηr t ht
        ((CuspControlledRetraction.quotientLevelFibreHomeomorph C r η t htη).symm
          (CuspControlledRetraction.quotientLevelFibreHomeomorph C r η t htη
            (CuspControlledRetraction.levelProjection C hηr t
              (toricFibreLevelHomeomorph η t htη x)))) =
      _
  rw [Homeomorph.symm_apply_apply]
  exact
    prescribedFibreCollapse_levelProjection C hε1 hRC hRD hηε r hr hηr t ht
      (toricFibreLevelHomeomorph η t htη x)

private theorem CuspCentralHomology.prescribedActualFibreCollapse_radius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (η : ℝ) (hηδ : η < δ) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η)
    (q : CuspControlledRetraction.ActualQuotientFibre C δ t) :
    CuspControlledRetraction.prescribedActualFibreCollapse C r hr (hηδ.trans_le hδr) t ht htη
        (fibreRadiusHomeomorph C r δ t hδr hC (htη.trans_lt hηδ) q) =
      centralRadiusHomeomorph C r δ hδr hC hδ
        (CuspControlledRetraction.prescribedActualFibreCollapse C δ hδ hηδ t ht htη q) := by
  obtain ⟨x, rfl⟩ := CuspSpecialization.fibreProjection_surjective C δ t (htη.trans_lt hηδ) q
  rw [fibreRadiusHomeomorph_fibreProjection,
    CuspSpecialization.prescribedActualFibreCollapse_fibreProjection C hδ1 hRC hRF hηδ r hr
      (hηδ.trans_le hδr) t ht htη,
    CuspSpecialization.prescribedActualFibreCollapse_fibreProjection C hδ1 hRC hRF hηδ δ hδ hηδ t
      ht htη,
    centralRadiusHomeomorph_centralProject]

private theorem CuspCentralHomology.levelToPunctured_continuous (η : ℝ) (t : ℂ) (ht : t ≠ 0) :
    Continuous (CuspControlledRetraction.levelToPunctured η t ht) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

private theorem CuspCentralHomology.prescribedFibreUpstairs_continuous_of_smallRadius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hCδ : ∀ i j, ContinuousOn (fun z => C z i j) (Metric.ball 0 δ))
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (hηδ : η < δ) (t : ℂ) (ht : t ≠ 0) :
    Continuous (CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht) := by
  change
    Continuous
      (CuspCollapse.centralProject C r hr ∘
        (CuspControlledRetraction.straightenedPrescribedCollapse C η ∘
          CuspControlledRetraction.levelToPunctured η t ht))
  have hc : Continuous (CuspControlledRetraction.straightenedPrescribedCollapse C η) :=
    CuspControlledRetraction.straightenedPrescribedCollapse_continuous C hδ hδ1 hCδ hRC hRF hηδ
  have hp : Continuous (CuspControlledRetraction.levelToPunctured η t ht) :=
    levelToPunctured_continuous η t ht
  have hi :
    Continuous
      (CuspControlledRetraction.straightenedPrescribedCollapse C η ∘
        CuspControlledRetraction.levelToPunctured η t ht) :=
    Continuous.comp (f := CuspControlledRetraction.levelToPunctured η t ht) (g :=
      CuspControlledRetraction.straightenedPrescribedCollapse C η) hc hp
  exact
    Continuous.comp (f :=
      CuspControlledRetraction.straightenedPrescribedCollapse C η ∘
        CuspControlledRetraction.levelToPunctured η t ht)
      (g := CuspCollapse.centralProject C r hr) (CuspCollapse.centralProject_continuous C r hr) hi

private theorem CuspCentralHomology.prescribedFibreCollapse_continuous_of_smallRadius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (η : ℝ) (hηδ : η < δ) (t : ℂ) (ht : t ≠ 0) :
    Continuous
      (CuspControlledRetraction.prescribedFibreCollapse C r hr (hηδ.trans_le hδr) t ht) := by
  have hCδ (i j) : ContinuousOn (fun z => C z i j) (Metric.ball 0 δ) :=
    ((hC i j).mono (Metric.ball_subset_ball hδr)).continuousOn
  have hf : Continuous (CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht) :=
    prescribedFibreUpstairs_continuous_of_smallRadius C r hr hδ hδ1 hCδ hRC hRF hηδ t ht
  exact
    CuspControlledRetraction.levelDescend_continuous C (hηδ.trans_le hδr) t
      (CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht) hC hf
      (CuspSpecialization.prescribedFibreUpstairs_compatible C hδ1 hRC hRF hηδ r hr
        (hηδ.trans_le hδr) t ht)

private theorem CuspCentralHomology.prescribedActualFibreCollapse_continuous_of_smallRadius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (η : ℝ) (hηδ : η < δ) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η) :
    Continuous
      (CuspControlledRetraction.prescribedActualFibreCollapse C r hr (hηδ.trans_le hδr) t ht
        htη) := by
  change
    Continuous
      (CuspControlledRetraction.prescribedFibreCollapse C r hr (hηδ.trans_le hδr) t ht ∘
        (CuspControlledRetraction.quotientLevelFibreHomeomorph C r η t htη).symm)
  exact
    (prescribedFibreCollapse_continuous_of_smallRadius C r δ hr hδ hδr hC hδ1 hRC hRF η hηδ t
          ht).comp
      (CuspControlledRetraction.quotientLevelFibreHomeomorph C r η t htη).symm.continuous

private def CuspCentralHomology.smallRadiusActualFibreCollapseMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (η : ℝ) (hηδ : η < δ) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η) :
    C(CuspControlledRetraction.ActualQuotientFibre C r t, CuspRetraction.QuotientCentralFibre C r)
    where
  toFun :=
    CuspControlledRetraction.prescribedActualFibreCollapse C r hr (hηδ.trans_le hδr) t ht htη
  continuous_toFun :=
    prescribedActualFibreCollapse_continuous_of_smallRadius C r δ hr hδ hδr hC hδ1 hRC hRF η hηδ t
      ht htη

private def CuspSpecialization.sourceProductCoordinateHomeomorph :
    (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
      PeriodTorusHigherHomology.ProductTorus 4 :=
  ((Homeomorph.prodComm ToricSpace.CompactFibreTorus
            (PeriodTorusHigherHomology.ProductTorus 2)).trans
        ((Homeomorph.refl (PeriodTorusHigherHomology.ProductTorus 2)).prodCongr
          CuspCentralHomology.compactFibreTorusHomeomorph)).trans
    (Fin.appendHomeomorph 2 2)

@[simp]
private theorem CuspSpecialization.sourceProductCoordinateHomeomorph_apply
    (p : ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :
    sourceProductCoordinateHomeomorph p =
      ![p.2 0, p.2 1, CuspCentralHomology.compactFibreTorusHomeomorph p.1 0,
        CuspCentralHomology.compactFibreTorusHomeomorph p.1 1] := by
  funext i
  fin_cases i <;> rfl

private def CuspSpecialization.sourceCoordinateTorusHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    SourceModel C₀ ≃ₜ PeriodTorusHigherHomology.ProductTorus 4 :=
  (sourceProductHomeomorph C₀).trans sourceProductCoordinateHomeomorph

@[simp]
private theorem CuspSpecialization.sourceCoordinateTorusHomeomorph_projection
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (p : CuspHoneycomb.PhasePlane) :
    sourceCoordinateTorusHomeomorph C₀ (sourceProjection C₀ p) =
      ![((-p.2 1 : ℝ) : AddCircle (1 : ℝ)), (p.2 0 : AddCircle (1 : ℝ)),
        CuspCentralHomology.compactFibreTorusHomeomorph (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹) 0,
        CuspCentralHomology.compactFibreTorusHomeomorph (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹)
          1] := by
  rw [sourceCoordinateTorusHomeomorph, Homeomorph.trans_apply, sourceProductHomeomorph_projection,
    sourceProductCoordinateHomeomorph_apply]
  simp [ToricSpace.realCuspVector]

private theorem CuspSpecialization.compactFibreTorusHomeomorph_planarPhase
    (y : (CuspHoneycombTiling.Plane)) :
    CuspCentralHomology.compactFibreTorusHomeomorph (planarPhase y) =
      PeriodTorusHigherHomology.coordinateProjection 2 y :=
  CuspCentralHomology.compactFibreTorusHomeomorph_exp y

private theorem CuspSpecialization.sourceTorusMatrix_M₀_apply
    (x : PeriodTorusHigherHomology.ProductTorus 4) :
    PeriodTorusHigherHomology.torusMatrixMap M₀ x = ![x 0, x 1, x 1 + x 2, -x 0 + x 3] := by
  funext i
  fin_cases i <;> simp [PeriodTorusHigherHomology.torusMatrixMap_apply, M₀, Fin.sum_univ_four]

private theorem
    CuspSpecialization.sourceCoordinateTorusHomeomorph_shear (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (x : SourceModel C₀) :
    sourceCoordinateTorusHomeomorph C₀ (sourceShear C₀ x) =
      PeriodTorusHigherHomology.torusMatrixMap M₀ (sourceCoordinateTorusHomeomorph C₀ x) := by
  obtain ⟨p, rfl⟩ := sourceProjection_surjective C₀ x
  rw [sourceShear_projection, sourceCoordinateTorusHomeomorph_projection,
    sourceCoordinateTorusHomeomorph_projection, sourceTorusMatrix_M₀_apply]
  have hp :
    (p.1 * planarPhase p.2) * (sourcePhaseCharacter C₀ p.2)⁻¹ =
      (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹) * planarPhase p.2 := by ac_rfl
  simp only [phasePlaneShear, hp, CuspCentralHomology.compactFibreTorusHomeomorph_mul,
    compactFibreTorusHomeomorph_planarPhase]
  funext i
  fin_cases i <;>
    simp [PeriodTorusHigherHomology.coordinateProjection_apply, QuotientAddGroup.mk_neg, add_comm]

private def
    CuspSpecialization.markedCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    C(PeriodTorusHigherHomology.ProductTorus 4, CuspRetraction.QuotientCentralFibre C ε) :=
  (sourceCollapse C ε hε).comp
    ((sourceCoordinateTorusHomeomorph (C 0)).symm :
      C(PeriodTorusHigherHomology.ProductTorus 4, SourceModel (C 0)))

private theorem
    CuspSpecialization.markedCollapse_eq_product (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    markedCollapse C ε hε =
      (productCollapse C ε hε).comp
        (sourceProductCoordinateHomeomorph.symm :
          C(PeriodTorusHigherHomology.ProductTorus 4,
            ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2)) :=
  rfl

private theorem CuspSpecialization.markedCollapse_comp_productCoordinates
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    (markedCollapse C ε hε).comp
        (sourceProductCoordinateHomeomorph :
          C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
            PeriodTorusHigherHomology.ProductTorus 4)) =
      productCollapse C ε hε := by
  rw [markedCollapse_eq_product]
  apply ContinuousMap.ext
  intro x
  change
    productCollapse C ε hε
        (sourceProductCoordinateHomeomorph.symm (sourceProductCoordinateHomeomorph x)) =
      _
  rw [Homeomorph.symm_apply_apply]

private theorem CuspSpecialization.sourceCoordinateTorusHomeomorph_symm_matrix
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (x : PeriodTorusHigherHomology.ProductTorus 4) :
    (sourceCoordinateTorusHomeomorph (C 0)).symm (PeriodTorusHigherHomology.torusMatrixMap M₀ x) =
      sourceShear (C 0) ((sourceCoordinateTorusHomeomorph (C 0)).symm x) := by
  apply (sourceCoordinateTorusHomeomorph (C 0)).injective
  rw [Homeomorph.apply_symm_apply, sourceCoordinateTorusHomeomorph_shear,
    Homeomorph.apply_symm_apply]

private theorem
    CuspSpecialization.markedCollapse_comp_matrix (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    (markedCollapse C ε hε).comp (PeriodTorusHigherHomology.torusMatrixMap M₀) =
      ((sourceCollapse C ε hε).comp (sourceShear (C 0))).comp
        ((sourceCoordinateTorusHomeomorph (C 0)).symm :
          C(PeriodTorusHigherHomology.ProductTorus 4, SourceModel (C 0))) := by
  apply ContinuousMap.ext
  intro x
  change
    sourceCollapse C ε hε
        ((sourceCoordinateTorusHomeomorph (C 0)).symm
          (PeriodTorusHigherHomology.torusMatrixMap M₀ x)) =
      _
  rw [sourceCoordinateTorusHomeomorph_symm_matrix]
  rfl

private def
    CuspSpecialization.markedCollapseMonodromyHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    (markedCollapse C ε hε).Homotopy
      ((markedCollapse C ε hε).comp (PeriodTorusHigherHomology.torusMatrixMap M₀)) := by
  rw [markedCollapse_comp_matrix]
  have h :=
    (sourceRotationHomotopy C ε hε 1).compContinuousMap
      ((sourceCoordinateTorusHomeomorph (C 0)).symm :
        C(PeriodTorusHigherHomology.ProductTorus 4, SourceModel (C 0)))
  simpa only [sourceRotation_one, markedCollapse] using h

private theorem
    CuspSpecialization.markedCollapse_homology_comp_matrix (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n).comp
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
          n) =
      SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact
    (PeriodTorusHigherHomology.homotopy_homologyMap (markedCollapseMonodromyHomotopy C ε hε)
        n).symm

private theorem
    CuspSpecialization.markedCollapse_homology_invariant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n) :
    SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) n
          a) =
      SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n a :=
  LinearMap.congr_fun (markedCollapse_homology_comp_matrix C ε hε n) a

private theorem CuspSpecialization.markedCollapse_homology_range_variation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            n -
          LinearMap.id) ≤
      LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n) := by
  rintro a ⟨b, rfl⟩
  change
    SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) n
            b -
          b) =
      0
  rw [map_sub, markedCollapse_homology_invariant, sub_self]

private theorem
    CuspSpecialization.markedCollapse_homology_product (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) n) :
    SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv sourceProductCoordinateHomeomorph n
          a) =
      SingularMayerVietoris.singularHomologyMap (productCollapse C ε hε) n a := by
  have h :=
    congrArg (fun f => SingularMayerVietoris.singularHomologyMap f n)
      (markedCollapse_comp_productCoordinates C ε hε)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

private theorem CuspSpecialization.markedCollapse_homology_surjective_of_product
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hf :
      Function.Surjective
        (SingularMayerVietoris.singularHomologyMap (productCollapse C ε hε) n)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n) := by
  intro x
  obtain ⟨a, rfl⟩ := hf x
  exact
    ⟨PeriodTorusHigherHomology.homeomorphHomologyEquiv sourceProductCoordinateHomeomorph n a,
      markedCollapse_homology_product C ε hε n a⟩

private def
    CuspSpecialization.radiusMarkedHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (t : ℂ)
    (hδr : δ ≤ r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (htδ : ‖t‖ < δ)
    (e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C δ t) :
    PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ
      CuspControlledRetraction.ActualQuotientFibre C r t :=
  sourceProductCoordinateHomeomorph.symm.trans
    (e.trans (CuspCentralHomology.fibreRadiusHomeomorph C r δ t hδr hC htδ))

private theorem
    CuspSpecialization.radiusMarkedHomeomorph_homotopic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (t : ℂ) (ht : t ≠ 0) (htδ : ‖t‖ < δ)
    (e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C δ t)
    (he : IsPrescribedProductModel C δ hδ t ht e) (η : ℝ) (hηδ : η < δ) (htη : ‖t‖ ≤ η) :
    (markedCollapse C r hr).Homotopic
      ((CuspCentralHomology.smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF η hηδ
            t ht htη).comp
        (radiusMarkedHomeomorph C r δ t hδr hC htδ e :
          C(PeriodTorusHigherHomology.ProductTorus 4,
            CuspControlledRetraction.ActualQuotientFibre C r t))) := by
  obtain ⟨hc, hh, _⟩ := he η htη hηδ
  let f :
    C(CuspControlledRetraction.ActualQuotientFibre C δ t,
      CuspRetraction.QuotientCentralFibre C δ) :=
    ⟨CuspControlledRetraction.prescribedActualFibreCollapse C δ hδ hηδ t ht htη, hc⟩
  let g :=
    CuspCentralHomology.smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF η hηδ t
      ht htη
  let eW : C(CuspRetraction.QuotientCentralFibre C δ, CuspRetraction.QuotientCentralFibre C r) :=
    (CuspCentralHomology.centralRadiusHomeomorph C r δ hδr hC hδ :
      C(CuspRetraction.QuotientCentralFibre C δ, CuspRetraction.QuotientCentralFibre C r))
  let eF := CuspCentralHomology.fibreRadiusHomeomorph C r δ t hδr hC htδ
  let eP :
    (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
      CuspControlledRetraction.ActualQuotientFibre C r t :=
    e.trans eF
  have hleft : eW.comp (productCollapse C δ hδ) = productCollapse C r hr :=
    CuspCentralHomology.centralRadiusHomeomorph_comp_productCollapse C r δ hδr hC hδ
  have hright :
    eW.comp
        (f.comp
          (e :
            C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
              CuspControlledRetraction.ActualQuotientFibre C δ t))) =
      g.comp
        (eP :
          C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
            CuspControlledRetraction.ActualQuotientFibre C r t)) := by
    apply ContinuousMap.ext
    intro x
    exact
      (CuspCentralHomology.prescribedActualFibreCollapse_radius C r δ hr hδ hδr hC hδ1 hRC hRF η
          hηδ t ht htη (e x)).symm
  have hp :
    (productCollapse C r hr).Homotopic
      (g.comp
        (eP :
          C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
            CuspControlledRetraction.ActualQuotientFibre C r t))) := by
    have h := (ContinuousMap.Homotopic.refl eW).comp hh
    change
      (eW.comp (productCollapse C δ hδ)).Homotopic
        (eW.comp
          (f.comp
            (e :
              C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
                CuspControlledRetraction.ActualQuotientFibre C δ t)))) at h
    rwa [hleft, hright] at h
  have h :=
    hp.comp
      (ContinuousMap.Homotopic.refl
        (sourceProductCoordinateHomeomorph.symm :
          C(PeriodTorusHigherHomology.ProductTorus 4,
            ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2)))
  have hmarked :
    (productCollapse C r hr).comp
        (sourceProductCoordinateHomeomorph.symm :
          C(PeriodTorusHigherHomology.ProductTorus 4,
            ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2)) =
      markedCollapse C r hr :=
    (markedCollapse_eq_product C r hr).symm
  have hend :
    (g.comp
            (eP :
              C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
                CuspControlledRetraction.ActualQuotientFibre C r t))).comp
        (sourceProductCoordinateHomeomorph.symm :
          C(PeriodTorusHigherHomology.ProductTorus 4,
            ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2)) =
      g.comp
        (radiusMarkedHomeomorph C r δ t hδr hC htδ e :
          C(PeriodTorusHigherHomology.ProductTorus 4,
            CuspControlledRetraction.ActualQuotientFibre C r t)) := by
    apply ContinuousMap.ext
    intro x
    rfl
  rwa [hmarked, hend] at h

private theorem
    CuspSpecialization.radiusMarkedHomeomorph_homology (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (t : ℂ) (ht : t ≠ 0) (htδ : ‖t‖ < δ)
    (e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C δ t)
    (he : IsPrescribedProductModel C δ hδ t ht e) (η : ℝ) (hηδ : η < δ) (htη : ‖t‖ ≤ η) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n) :
    SingularMayerVietoris.singularHomologyMap
        (CuspCentralHomology.smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF η
          hηδ t ht htη)
        n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (radiusMarkedHomeomorph C r δ t hδr hC htδ e) n a) =
      SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n a := by
  have h :=
    PeriodTorusHigherHomology.homotopic_homologyMap
      (radiusMarkedHomeomorph_homotopic C r δ hr hδ hδr hC hδ1 hRC hRF t ht htδ e he η hηδ htη) n
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  exact (LinearMap.congr_fun h a).symm

private theorem CuspSpecialization.exists_original_marked_model_of_smallRadius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (t : ℂ) (ht : t ≠ 0) (htδ : ‖t‖ < δ) :
    ∃ E :
      PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C r t,
      ∀ (η : ℝ) (hηδ : η < δ) (htη : ‖t‖ ≤ η),
        (markedCollapse C r hr).Homotopic
            ((CuspCentralHomology.smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
                  η hηδ t ht htη).comp
              (E :
                C(PeriodTorusHigherHomology.ProductTorus 4,
                  CuspControlledRetraction.ActualQuotientFibre C r t))) ∧
          ∀ (n : ℕ)
            (a :
              SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4)
                n),
            SingularMayerVietoris.singularHomologyMap
                (CuspCentralHomology.smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC
                  hRF η hηδ t ht htη)
                n (PeriodTorusHigherHomology.homeomorphHomologyEquiv E n a) =
              SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n a := by
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hC i j).mono (Metric.ball_subset_ball hδr)
  obtain ⟨e, he⟩ := exists_product_model_at_nonzero_level C δ hδ hδ1 hCδ hRC hRF t ht htδ
  refine ⟨radiusMarkedHomeomorph C r δ t hδr hC htδ e, ?_⟩
  intro η hηδ htη
  exact
    ⟨radiusMarkedHomeomorph_homotopic C r δ hr hδ hδr hC hδ1 hRC hRF t ht htδ e he η hηδ htη,
      radiusMarkedHomeomorph_homology C r δ hr hδ hδr hC hδ1 hRC hRF t ht htδ e he η hηδ htη⟩

private theorem CuspSpecialization.exists_original_marked_specialization_models
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ (η₀ : ℝ) (_hη₀ : 0 < η₀),
      η₀ < r ∧
        η₀ < 1 ∧
          ∀ (t : ℂ) (ht : t ≠ 0),
            ‖t‖ ≤ η₀ →
              ∃ E :
                PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ
                  CuspControlledRetraction.ActualQuotientFibre C r t,
                ∀ (η : ℝ) (_hη : η ≤ η₀) (htη : ‖t‖ ≤ η) (hηr : η < r),
                  ∃ hc :
                    Continuous
                      (CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht
                        htη),
                    (markedCollapse C r hr).Homotopic
                        ((⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht
                                  htη,
                                hc⟩ :
                              C(CuspControlledRetraction.ActualQuotientFibre C r t,
                                CuspRetraction.QuotientCentralFibre C r)).comp
                          (E :
                            C(PeriodTorusHigherHomology.ProductTorus 4,
                              CuspControlledRetraction.ActualQuotientFibre C r t))) ∧
                      ∀ (n : ℕ)
                        (a :
                          SingularMayerVietoris.SingularHomology
                            (PeriodTorusHigherHomology.ProductTorus 4) n),
                        SingularMayerVietoris.singularHomologyMap
                            (⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t
                                  ht htη,
                                hc⟩ :
                              C(CuspControlledRetraction.ActualQuotientFibre C r t,
                                CuspRetraction.QuotientCentralFibre C r))
                            n (PeriodTorusHigherHomology.homeomorphHomologyEquiv E n a) =
                          SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n a :=
  by
  obtain ⟨δ, hδ, hδr, hδ1, hRC, hRF⟩ :=
    CuspRetraction.exists_common_frozen_radius C hr (fun i j => (hC i j).continuousOn)
  let η₀ : ℝ := δ / 2
  have hη₀ : 0 < η₀ := half_pos hδ
  have hη₀δ : η₀ < δ := half_lt_self hδ
  refine ⟨η₀, hη₀, hη₀δ.trans hδr, hη₀δ.trans hδ1, ?_⟩
  intro t ht ht₀
  have htδ : ‖t‖ < δ := ht₀.trans_lt hη₀δ
  obtain ⟨E, hE⟩ :=
    exists_original_marked_model_of_smallRadius C r δ hr hδ hδr.le hC hδ1 hRC hRF t ht htδ
  refine ⟨E, ?_⟩
  intro η hη htη hηr
  have hηδ : η < δ := hη.trans_lt hη₀δ
  let f :=
    CuspCentralHomology.smallRadiusActualFibreCollapseMap C r δ hr hδ hδr.le hC hδ1 hRC hRF η hηδ
      t ht htη
  refine ⟨f.continuous, ?_, ?_⟩
  · exact (hE η hηδ htη).1
  · exact (hE η hηδ htη).2

private def CuspSpecialization.coordinateTorusH1Coordinates :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 1 ≃ₗ[ℤ]
      (Fin 4 → ℤ) :=
  (PeriodTorusHigherHomology.coordinateH1FourEquiv (Elliptic.examplePeriod .four)).symm

@[simp]
private theorem CuspSpecialization.coordinateTorusH1Coordinates_coordinateH1 (v : Fin 4 → ℤ) :
    coordinateTorusH1Coordinates (PeriodTorusHigherHomology.coordinateH1 4 v) = v :=
  (PeriodTorusHigherHomology.coordinateH1FourEquiv
        (Elliptic.examplePeriod .four)).symm_apply_apply
    v

private theorem CuspSpecialization.coordinateTorusH1Coordinates_matrix (A : LatticeMatrix)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 1) :
    coordinateTorusH1Coordinates
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A) 1
          a) =
      A *ᵥ coordinateTorusH1Coordinates a := by
  obtain ⟨v, hv⟩ :=
    (PeriodTorusHigherHomology.coordinateH1FourEquiv (Elliptic.examplePeriod .four)).surjective a
  change PeriodTorusHigherHomology.coordinateH1 4 v = a at hv
  rw [← hv, SingularMayerVietoris.singularHomologyMap_one,
    PeriodTorusHigherHomology.coordinateH1_matrix_natural (Elliptic.examplePeriod .four),
    coordinateTorusH1Coordinates_coordinateH1, coordinateTorusH1Coordinates_coordinateH1]

end Mathoverflow1973

end
