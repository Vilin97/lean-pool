/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedJointDifferentiability
import LeanPool.NavierStokesAndEuler.Euler.CommonPressureRepresentative
import LeanPool.NavierStokesAndEuler.Euler.GraphDivergence

/-! The actual total pressure of an exact lifted packet has a canonically
normalized scalar pressure on the oscillating graph. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderDriftCorrection.ExactLiftedPacket

open Set InnerProductSpace EulerLiftedGradientSpace EulerAllOrderCorrectionData
  EulerGraphPressurePotential EulerCanonicalGraphPotential
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 < T} {A : Data P T} {B : Budget P hT A}
  (S : ExactLiftedPacket P hT A B)

/-- Graph pressure, given by `A.κ • S.pressure.pointField t (cylinderGraph P k A.direction x)`. -/
def graphPressure (k : ℝ) (t : Icc (0 : ℝ) T) (x : Vector3) : Vector3 :=
  A.κ • S.pressure.pointField t (cylinderGraph P k A.direction x)

theorem graphPressure_joint_continuous (k : ℝ) :
    Continuous (S.graphPressure k).uncurry :=
  (S.pressure.pointField_joint_continuous.comp
    (continuous_fst.prodMk ((EulerCommonPressureRepresentative.cylinderGraph_continuous
      P k A.direction).comp continuous_snd))).const_smul A.κ

theorem graphPressure_has_potential (k : ℝ) (hk : k * A.κ = 1) (t : Icc (0 : ℝ) T) :
    ∃ q : Vector3 → ℝ, ContDiff ℝ ∞ q ∧
      ∀ x, _root_.gradient q x = S.graphPressure k t x :=
  gradientSpace_has_graph_potential P A.κ k hk A.direction
    (S.pressure.field t) (S.gradient t) (S.pressure.pointField t)
    (S.pressure.pointField_ae t) (S.pressure.pointField_smooth t)

/-- Graph potential, given by `radialPotential (S.graphPressure k t)`. -/
def graphPotential (k : ℝ) (t : Icc (0 : ℝ) T) : Vector3 → ℝ :=
  radialPotential (S.graphPressure k t)

theorem graphPotential_zero (k : ℝ) (t : Icc (0 : ℝ) T) :
    S.graphPotential k t 0 = 0 := radialPotential_zero _

theorem graphPotential_joint_continuous (k : ℝ) :
    Continuous (S.graphPotential k).uncurry :=
  radialPotential_joint_continuous _ (S.graphPressure_joint_continuous k)

theorem graphPotential_smooth (k : ℝ) (hk : k * A.κ = 1) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (S.graphPotential k t) := by
  obtain ⟨q,hq,hgrad⟩ := S.graphPressure_has_potential k hk t
  exact radialPotential_smooth _
    (Continuous.uncurry_left t (S.graphPressure_joint_continuous k)) q hq hgrad

theorem graphPotential_gradient (k : ℝ) (hk : k * A.κ = 1)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    _root_.gradient (S.graphPotential k t) x =
      A.κ • S.pressure.pointField t (cylinderGraph P k A.direction x) := by
  obtain ⟨q,hq,hgrad⟩ := S.graphPressure_has_potential k hk t
  exact radialPotential_gradient _
    (Continuous.uncurry_left t (S.graphPressure_joint_continuous k)) q hq hgrad x

/-- Raw graph potential, given by `S.graphPotential k (projIcc 0 T hT.le q.1) q.2`. -/
def rawGraphPotential (k : ℝ) (q : ℝ × Vector3) : ℝ :=
  S.graphPotential k (projIcc 0 T hT.le q.1) q.2

theorem rawGraphPotential_smooth (k : ℝ) (hk : k * A.κ = 1) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => S.rawGraphPotential k (t,x)) := by
  change ContDiff ℝ ∞ (S.graphPotential k (projIcc 0 T hT.le t))
  exact S.graphPotential_smooth k hk (projIcc 0 T hT.le t)

theorem rawGraphPotential_gradient (k : ℝ) (hk : k * A.κ = 1) (t : ℝ) (x : Vector3) :
    _root_.gradient (fun y => S.rawGraphPotential k (t,y)) x =
      A.κ • S.rawPressure (t,(x,k*⟪A.direction,x⟫_ℝ)) := by
  change _root_.gradient (S.graphPotential k (projIcc 0 T hT.le t)) x =
    A.κ • S.pressure.pointField (projIcc 0 T hT.le t) (cylinderGraph P k A.direction x)
  exact S.graphPotential_gradient k hk (projIcc 0 T hT.le t) x

theorem graphVelocity_divergence (k : ℝ) (hk : k * A.κ = 1)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    (∑ i : Fin 3, (fderiv ℝ (fun y =>
      S.velocity.pointField t (cylinderGraph P k A.direction y)) x
        (EuclideanSpace.single i 1)) i) = 0 :=
  EulerGraphDivergence.divergenceFree_graph P A.κ k hk A.direction
    (S.velocity.field t) (S.divergence t) (S.velocity.pointField t)
    (S.velocity.pointField_ae t) (S.velocity.pointField_smooth t) x

end EulerAllOrderDriftCorrection.ExactLiftedPacket
