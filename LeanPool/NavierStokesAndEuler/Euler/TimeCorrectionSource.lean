/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionLocal
import LeanPool.NavierStokesAndEuler.Euler.SobolevNonlinearCompatibility
public import LeanPool.NavierStokesAndEuler.Euler.AsymmetricTransport
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.HeatRegularizedPaths
import LeanPool.NavierStokesAndEuler.Euler.TimeLpStrongOperators
public import LeanPool.NavierStokesAndEuler.Euler.GevreyOrderZero

/-! Actual energy-order Bochner representatives of the nonlinear correction source and pressure. -/

section

/-! Exact restriction and time continuity of the actual order-zero correction source. -/

@[expose] public section

noncomputable section

namespace EulerSobolevCorrectionCompatibility

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerSobolevNonlinearCompatibility
  EulerSobolevL2Product EulerGevreyOrderZero EulerAsymmetricTransport EulerVectorCylinder
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance correctionCompatGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
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
    (z : SobolevSpace period (p + 1)) (e : SobolevSpace period p) :
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
    (z : SobolevSpace period (p + 1)) (r e : SobolevSpace period p) :
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

/-- A continuous coefficient and two continuous energy-order paths give a continuous actual
algebraic term. -/
theorem algebraicAt_continuous {s : ℕ} (hs : 6 ≤ s) {T : Type*} [TopologicalSpace T]
    (C : T → Fin 3 → SobolevSpace period s →L[ℝ] SobolevSpace period s)
    (hC : ∀ i, Continuous (fun t => C t i)) (u v : T → SobolevSpace period s)
    (hu : Continuous u) (hv : Continuous v) : Continuous (fun t => algebraicAt period hs (C t) (u
        t) (v t)) := by
  apply continuous_finsetSum
  intro i _
  exact (hC i).clm_apply (((productHqBilinear period hs (coordinate 3 i) (coordinate_norm_le 3
      i)).continuous.comp hu).clm_apply hv)

/-- The actual order-zero source is continuous at the energy Sobolev level, without an additional
error derivative. -/
theorem orderZeroSource_continuous {s : ℕ} (hs : 6 ≤ s) {T : Type*} [TopologicalSpace T]
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : T → SobolevSpace period s →L[ℝ] SobolevSpace period s) (hC0 : Continuous C0)
    (C : T → Fin 3 → SobolevSpace period s →L[ℝ] SobolevSpace period s)
    (hC : ∀ i, Continuous (fun t => C t i))
    (z : T → SobolevSpace period (s + 1)) (r e : T → SobolevSpace period s)
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

end
end

end

section

/-! Strong actual heat approximation and time-dependent operator commutators in Bochner Sobolev
spaces. -/

@[expose] public section

noncomputable section

namespace EulerSobolevTimeRegularization

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerHeatRegularizedPaths EulerTimeLp
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine Sobolev heat regularizations converge strongly on every Bochner L² time field. -/
theorem heat_timeLp_tendsto (q : ℕ) (T : ℝ) (u : TimeLp T (SobolevSpace period q)) :
    Filter.Tendsto (fun n => (heatOperator period q (regularizerVariance n)).compLpL 2 (timeMeasure
        T) u)
      Filter.atTop (𝓝 u) := by
  apply strong_operator_timeLp_tendsto T (fun n => heatOperator period q (regularizerVariance n)) 1
  · intro n x
    simpa only [one_mul] using heatOperator_bound period (regularizerVariance n) x
  · intro x
    have h := (heatOperator_continuous period x).continuousAt.tendsto.comp
        regularizerVariance_tendsto
    simpa only [heatOperator_zero, Function.comp_def] using h

/-- Actual heat approximation commutes asymptotically with every continuous bounded time-dependent
Sobolev operator. -/
theorem heat_time_commutator_tendsto (p q : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period q →L[ℝ] SobolevSpace period p))
    (u : TimeLp T (SobolevSpace period q)) :
    Filter.Tendsto (fun n =>
      timeMultiplier T hT A ((heatOperator period q (regularizerVariance n)).compLpL 2 (timeMeasure
          T) u) -
        (heatOperator period p (regularizerVariance n)).compLpL 2 (timeMeasure T) (timeMultiplier T
            hT A u))
      Filter.atTop (𝓝 0) := by
  have hA := (timeMultiplier T hT A).continuous.continuousAt.tendsto.comp (heat_timeLp_tendsto
      period q T u)
  have hB := heat_timeLp_tendsto period p T (timeMultiplier T hT A u)
  simpa only [sub_self, Function.comp_def] using hA.sub hB

/-- The actual heat commutator vanishes in the full L² time norm. -/
theorem heat_time_commutator_norm_tendsto (p q : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period q →L[ℝ] SobolevSpace period p))
    (u : TimeLp T (SobolevSpace period q)) :
    Filter.Tendsto (fun n => ‖
      timeMultiplier T hT A ((heatOperator period q (regularizerVariance n)).compLpL 2 (timeMeasure
          T) u) -
        (heatOperator period p (regularizerVariance n)).compLpL 2 (timeMeasure T) (timeMultiplier T
            hT A u)‖)
      Filter.atTop (𝓝 (0 : ℝ)) := by
  simpa only [norm_zero] using (heat_time_commutator_tendsto period p q T hT A u).norm

end EulerSobolevTimeRegularization

end
end

end

section

/-! Actual derivative-losing transport on continuous coefficients and square-integrable higher
Sobolev states. -/

@[expose] public section

noncomputable section

namespace EulerTimeSobolevTransport

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAsymmetricTransport
  EulerTimeLp EulerVolterraConvolution EulerSobolevTimeRegularization EulerHeatRegularizedPaths
  EulerSobolevHeat
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A named local normed-group instance for the actual Sobolev scale. -/
local instance transportTimeGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance

/-- A named local real normed-space instance for the actual Sobolev scale. -/
local instance transportTimeSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- A continuous actual velocity path gives a continuous path of asymmetric transport operators. -/
def transportPath {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s)) :
    C(Icc (0 : ℝ) T, SobolevSpace period (s+1) →L[ℝ] SobolevSpace period s) :=
  (asymmetricTransport period hs L hL).compLeftContinuous ℝ (Icc (0 : ℝ) T) u

/-- Actual nonlinear transport of a higher Sobolev time field belongs to the full energy-order
Bochner space. -/
def transportTime {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (v : TimeLp T (SobolevSpace period (s + 1))) : TimeLp T (SobolevSpace period s) :=
  timeMultiplier T hT (transportPath period hs L hL T u) v

/-- The actual Bochner transport is literal asymmetric Sobolev transport almost everywhere in time.
-/
theorem transportTime_ae {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (v : TimeLp T (SobolevSpace period (s + 1))) :
    (transportTime period hs L hL T hT u v : ℝ → SobolevSpace period s) =ᵐ[timeMeasure T]
      fun t => asymmetricTransport period hs L hL (extendPath T hT u t) (v t) :=
  timeMultiplier_ae T hT (transportPath period hs L hL T u) v

/-- Genuine heat smoothing and actual transport commute asymptotically in the energy-order L² time
space. -/
theorem transport_regularization_commutator {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (v : TimeLp T (SobolevSpace period (s + 1))) :
    Filter.Tendsto (fun n =>
      transportTime period hs L hL T hT u
        ((heatOperator period (s+1) (regularizerVariance n)).compLpL 2 (timeMeasure T) v) -
      (heatOperator period s (regularizerVariance n)).compLpL 2 (timeMeasure T)
        (transportTime period hs L hL T hT u v)) Filter.atTop (𝓝 0) :=
  heat_time_commutator_tendsto period s (s+1) T hT (transportPath period hs L hL T u) v

end EulerTimeSobolevTransport

end
end

end

@[expose] public section

noncomputable section

namespace EulerTimeCorrectionSource

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerSobolevNonlinearCompatibility
  EulerSobolevCorrectionCompatibility EulerGevreyOrderZero EulerAsymmetricTransport
      EulerSobolevTransport
  EulerTimeLp EulerTimeSobolevTransport EulerVolterraConvolution EulerCorrectionOperators
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance timeCorrectionGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance timeCorrectionSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- Cache pointwise addition for the Sobolev paths used in correction sources. -/
local instance timeCorrectionPathAdd (T : ℝ) (q : ℕ) :
    Add C(Icc (0 : ℝ) T, SobolevSpace period q) := inferInstance

/-- The actual order-zero source is a continuous path on the energy Sobolev level. -/
def orderZeroPath {s : ℕ} (hs : 6 ≤ s) (T : ℝ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (C : Fin 3 → C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (z : C(Icc (0 : ℝ) T, SobolevSpace period (s + 1)))
    (r e : C(Icc (0 : ℝ) T, SobolevSpace period s)) : C(Icc (0 : ℝ) T, SobolevSpace period s) :=
  ⟨fun t => orderZeroSource period hs L hL (C0 t) (fun i => C i t) (z t) (r t) (e t),
    orderZeroSource_continuous period hs L hL C0 C0.continuous (fun t i => C i t) (fun i => (C
        i).continuous)
      z r e z.continuous r.continuous e.continuous⟩

/-- The genuine energy-order raw correction source uses the constructed higher derivative only in
its top transport. -/
def rawSourceTime {s : ℕ} (hs : 6 ≤ s) (T : ℝ) (hT : 0 ≤ T)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (C : Fin 3 → C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (z : C(Icc (0 : ℝ) T, SobolevSpace period (s + 1)))
    (r e : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (U : TimeLp T (SobolevSpace period (s + 1))) : TimeLp T (SobolevSpace period s) :=
  transportTime period hs L hL T hT
    ((truncateOperator period s).compLeftContinuous ℝ (Icc (0 : ℝ) T) z + e) U +
      pathLp T hT (orderZeroPath period hs T L hL C0 C z r e)

/-- The Bochner raw source has exactly the actual transport-plus-order-zero representative. -/
theorem rawSourceTime_ae {s : ℕ} (hs : 6 ≤ s) (T : ℝ) (hT : 0 ≤ T)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (C : Fin 3 → C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (z : C(Icc (0 : ℝ) T, SobolevSpace period (s + 1)))
    (r e : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (U : TimeLp T (SobolevSpace period (s + 1))) :
    (rawSourceTime period hs T hT L hL C0 C z r e U : ℝ → SobolevSpace period s) =ᵐ[timeMeasure T]
      fun t => asymmetricTransport period hs L hL
        (truncateOperator period s (extendPath T hT z t) + extendPath T hT e t) (U t) +
          extendPath T hT (orderZeroPath period hs T L hL C0 C z r e) t := by
  let b := (truncateOperator period s).compLeftContinuous ℝ (Icc (0 : ℝ) T) z + e
  let F := orderZeroPath period hs T L hL C0 C z r e
  filter_upwards [Lp.coeFn_add (transportTime period hs L hL T hT b U) (pathLp T hT F),
    transportTime_ae period hs L hL T hT b U, pathLp_ae T hT F] with t h1 h2 h3
  simp only [Pi.add_apply] at h1
  exact h1.trans (congrArg₂ (fun x y : SobolevSpace period s => x+y) h2 h3)

/-- Restricting genuine asymmetric transport and its constructed state recovers the original
lower-level nonlinearity. -/
theorem restrict_transport_state {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (b e : SobolevSpace period (q + 1)) (U : SobolevSpace period ((q + 1) + 1))
    (hU : truncateOperator period (q + 1) U = e) :
    truncateOperator period q (asymmetricTransport period (by omega : 6 ≤ q+1) L hL b U) =
      transportBilinear period hq L hL b e := by
  have hb : restrictOperator period (by omega : q ≤ q+1) b = truncateOperator period q b := by
    apply value_injective period
    rfl
  have hUr : restrictOperator period (by omega : q+1 ≤ (q+1)+1) U = e := by
    exact hU
  have h := restrict_asymmetricTransport period (by
      omega : 6 ≤ q+1) hq (by omega : q ≤ q+1) L hL b U
  have he := congrArg₂ (fun x : SobolevSpace period q => fun y : SobolevSpace period (q+1) =>
    asymmetricTransport period hq L hL x y) hb hUr
  exact h.trans (he.trans (asymmetricTransport_eq period hq L hL b e))

/-- The upgraded raw source restricts to the literal lower-order correction equation. -/
theorem restrict_raw_source {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (A0 : SmoothCoefficient period) (KP0 : CoefficientJet period standardDirection (q + 1) A0)
    (KQ0 : CoefficientJet period standardDirection q A0) (A : Fin 3 → SmoothCoefficient period)
    (KP : ∀ i, CoefficientJet period standardDirection (q + 1) (A i))
    (KQ : ∀ i, CoefficientJet period standardDirection q (A i))
    (z : SobolevSpace period ((q + 1) + 1)) (r e : SobolevSpace period (q + 1))
    (U : SobolevSpace period ((q + 1) + 1)) (hU : truncateOperator period (q + 1) U = e) :
    truncateOperator period q
      (asymmetricTransport period (by omega : 6 ≤ q+1) L hL (truncateOperator period (q+1) z+e) U +
        orderZeroSource period (by omega : 6 ≤ q+1) L hL (coefficientSobolevOperator period KP0)
          (fun i => coefficientSobolevOperator period (KP i)) z r e) =
      transportBilinear period hq L hL (truncateOperator period (q+1) z+e) e +
        orderZeroSource period hq L hL (coefficientSobolevOperator period KQ0)
          (fun i => coefficientSobolevOperator period (KQ i))
          (truncateOperator period (q+1) z) (truncateOperator period q r) (truncateOperator period
              q e) := by
  exact (map_add (truncateOperator period q) _ _).trans
    (congrArg₂ (fun x y : SobolevSpace period q => x+y)
      (restrict_transport_state period hq L hL _ e U hU)
      (restrict_orderZeroSource period (by omega : 6 ≤ q+1) hq (by omega : q ≤ q+1)
        L hL A0 KP0 KQ0 A KP KQ z r e))

/-- The actual positive coercive pressure operator is a continuous energy-order time path. -/
def positivePressurePath {s : ℕ} (T : ℝ) (G : CoefficientPath period s (Icc (0 : ℝ) T))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪(G.coefficient t).coefficient x v, v⟫_ℝ) :
    C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s) :=
  ⟨fun t => pressureSobolevOperator period (G.jet t) κ m c hc (hpos t),
    continuous_iff_continuousAt.mpr (fun t => pressureSobolev_continuousAt period G.coefficient
        G.jet κ m c hc hpos t G.continuous.continuousAt)⟩

/-- The actual signed PDE pressure belongs to the full energy-order Bochner space. -/
def pressureTime {s : ℕ} (T : ℝ) (hT : 0 ≤ T) (G : CoefficientPath period s (Icc (0 : ℝ) T))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪(G.coefficient t).coefficient x v, v⟫_ℝ)
    (F : TimeLp T (SobolevSpace period s)) : TimeLp T (SobolevSpace period s) :=
  -(timeMultiplier T hT (positivePressurePath period T G κ m c hc hpos) F)

/-- The actual projected mild forcing belongs to the full energy-order Bochner space. -/
def projectedTime {s : ℕ} (T : ℝ) (hT : 0 ≤ T) (G : CoefficientPath period s (Icc (0 : ℝ) T))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪(G.coefficient t).coefficient x v, v⟫_ℝ)
    (F : TimeLp T (SobolevSpace period s)) : TimeLp T (SobolevSpace period s) :=
  -(timeMultiplier T hT (pressureProjectionPath period G.coefficient G.jet κ m c hc hpos
      G.continuous) F)

/-- The signed pressure time field is the literal unique coercive pressure solve almost everywhere.
-/
theorem pressureTime_ae {s : ℕ} (T : ℝ) (hT : 0 ≤ T) (G : CoefficientPath period s (Icc (0 : ℝ) T))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪(G.coefficient t).coefficient x v, v⟫_ℝ)
    (F : TimeLp T (SobolevSpace period s)) :
    (pressureTime period T hT G κ m c hc hpos F : ℝ → SobolevSpace period s) =ᵐ[timeMeasure T]
      fun t => -(pressureSobolevOperator period (G.jet (projIcc 0 T hT t)) κ m c hc (hpos _) (F t))
          := by
  filter_upwards [Lp.coeFn_neg (timeMultiplier T hT (positivePressurePath period T G κ m c hc hpos)
      F),
    timeMultiplier_ae T hT (positivePressurePath period T G κ m c hc hpos) F] with t h1 h2
  simp only [Pi.neg_apply] at h1
  exact h1.trans (congrArg (fun x : SobolevSpace period s => -x) h2)

/-- The projected time field is exactly the pressure-projected nonlinear mild forcing almost
everywhere. -/
theorem projectedTime_ae {s : ℕ} (T : ℝ) (hT : 0 ≤ T) (G : CoefficientPath period s (Icc (0 : ℝ) T))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪(G.coefficient t).coefficient x v, v⟫_ℝ)
    (F : TimeLp T (SobolevSpace period s)) :
    (projectedTime period T hT G κ m c hc hpos F : ℝ → SobolevSpace period s) =ᵐ[timeMeasure T]
      fun t => -(projectedSourceOperator period (G.jet (projIcc 0 T hT t)) κ m c hc (hpos _) (F t))
          := by
  filter_upwards [Lp.coeFn_neg (timeMultiplier T hT (pressureProjectionPath period G.coefficient
      G.jet κ m c hc hpos G.continuous) F),
    timeMultiplier_ae T hT (pressureProjectionPath period G.coefficient G.jet κ m c hc hpos
        G.continuous) F] with t h1 h2
  simp only [Pi.neg_apply] at h1
  exact h1.trans (congrArg (fun x : SobolevSpace period s => -x) h2)

end EulerTimeCorrectionSource
