/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevNonlinearCompatibility
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionTime

@[expose] public section

/-! Exact restriction and time continuity of the actual order-zero correction source. -/

noncomputable section

namespace EulerSobolevCorrectionCompatibility

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerSobolevNonlinearCompatibility
  EulerSobolevL2Product EulerGevreyOrderZero EulerAsymmetricTransport EulerVectorCylinder
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

local instance correctionCompatGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
  inferInstance
local instance correctionCompatSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
  inferInstance

/-- The actual derivative-free Euler term restricts to the same lower-order field. -/
theorem restrict_algebraicAt {p q : ℕ} (hp : 6 ≤ p) (hq : 6 ≤ q) (hqp : q ≤ p)
    (A : Fin 3 → SmoothCoefficient period)
    (KP : ∀ i, CoefficientJet period standardDirection p (A i))
    (KQ : ∀ i, CoefficientJet period standardDirection q (A i)) (u v : SobolevSpace period p) :
    restrictOperator period hqp (algebraicAt period hp (fun i => coefficientSobolevOperator period
      (KP i)) u v) =
      algebraicAt period hq (fun i => coefficientSobolevOperator period (KQ i))
        (restrictOperator period hqp u) (restrictOperator period hqp v) := by
  simp only [algebraicAt, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [restrict_coefficient period hqp (KP i) (KQ i),
    restrict_productHq period hp hq hqp (coordinate 3 i) (coordinate_norm_le 3 i)]

/-- Background transport has precisely the same value on every compatible Sobolev level. -/
theorem restrict_backgroundDrift {p q : ℕ} (hp : 6 ≤ p) (hq : 6 ≤ q) (hqp : q ≤ p)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (z : SobolevSpace period (p+1)) (e : SobolevSpace period p) :
    restrictOperator period hqp (backgroundDrift period hp L hL z e) =
      backgroundDrift period hq L hL (restrictOperator period (Nat.succ_le_succ hqp) z)
        (restrictOperator period hqp e) := by
  exact restrict_asymmetricTransport period hp hq hqp L hL e z

/-- The full actual order-zero source agrees exactly with its lower-order construction. -/
theorem restrict_orderZeroSource {p q : ℕ} (hp : 6 ≤ p) (hq : 6 ≤ q) (hqp : q ≤ p)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (A0 : SmoothCoefficient period) (KP0 : CoefficientJet period standardDirection p A0)
    (KQ0 : CoefficientJet period standardDirection q A0) (A : Fin 3 → SmoothCoefficient period)
    (KP : ∀ i, CoefficientJet period standardDirection p (A i))
    (KQ : ∀ i, CoefficientJet period standardDirection q (A i))
    (z : SobolevSpace period (p+1)) (r e : SobolevSpace period p) :
    restrictOperator period hqp (orderZeroSource period hp L hL (coefficientSobolevOperator period
      KP0)
      (fun i => coefficientSobolevOperator period (KP i)) z r e) =
      orderZeroSource period hq L hL (coefficientSobolevOperator period KQ0)
        (fun i => coefficientSobolevOperator period (KQ i))
        (restrictOperator period (Nat.succ_le_succ hqp) z) (restrictOperator period hqp r)
          (restrictOperator period hqp e) := by
  simp only [orderZeroSource, map_add, restrict_backgroundDrift period hp hq hqp L hL,
    restrict_coefficient period hqp KP0 KQ0, restrict_algebraicAt period hp hq hqp A KP KQ,
    restrictOperator_truncate, truncate_restrictOperator]

/-- A continuous coefficient and two continuous energy-order paths give a continuous actual algebraic term. -/
theorem algebraicAt_continuous {s : ℕ} (hs : 6 ≤ s) {T : Type*} [TopologicalSpace T]
    (C : T → Fin 3 → SobolevSpace period s →L[ℝ] SobolevSpace period s)
    (hC : ∀ i, Continuous (fun t => C t i)) (u v : T → SobolevSpace period s)
    (hu : Continuous u) (hv : Continuous v) : Continuous (fun t => algebraicAt period hs (C t) (u
      t) (v t)) := by
  apply continuous_finsetSum
  intro i _
  exact (hC i).clm_apply (((productHqBilinear period hs (coordinate 3 i) (coordinate_norm_le 3
    i)).continuous.comp hu).clm_apply hv)

/-- The actual order-zero source is continuous at the energy Sobolev level, without an additional error derivative. -/
theorem orderZeroSource_continuous {s : ℕ} (hs : 6 ≤ s) {T : Type*} [TopologicalSpace T]
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : T → SobolevSpace period s →L[ℝ] SobolevSpace period s) (hC0 : Continuous C0)
    (C : T → Fin 3 → SobolevSpace period s →L[ℝ] SobolevSpace period s)
    (hC : ∀ i, Continuous (fun t => C t i))
    (z : T → SobolevSpace period (s+1)) (r e : T → SobolevSpace period s)
    (hz : Continuous z) (hr : Continuous r) (he : Continuous e) :
    Continuous (fun t => orderZeroSource period hs L hL (C0 t) (C t) (z t) (r t) (e t)) := by
  have hd : Continuous (fun t => backgroundDrift period hs L hL (z t) (e t)) :=
    ((asymmetricTransport period hs L hL).continuous.comp he).clm_apply hz
  have hzt := (truncateOperator period s).continuous.comp hz
  exact ((((hr.add hd).add (hC0.clm_apply he)).add
    (algebraicAt_continuous period hs C hC _ e hzt he)).add
    (algebraicAt_continuous period hs C hC e _ he hzt)).add
    (algebraicAt_continuous period hs C hC e e he he)

end EulerSobolevCorrectionCompatibility
