/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordValueIdentity
public import LeanPool.NavierStokesAndEuler.Euler.RegularizedMetricPaths
public import LeanPool.NavierStokesAndEuler.Euler.EnergyWordCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionForcing
public import LeanPool.NavierStokesAndEuler.Euler.TimeCorrectionSource
public import LeanPool.NavierStokesAndEuler.Euler.TransportL2Time
public import LeanPool.NavierStokesAndEuler.Euler.RegularizedEnergyFamily
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
import LeanPool.NavierStokesAndEuler.Euler.EnergyForcingIdentity

/-! Constructed nonlinear time fields and their exact full-order metric forcing for the Euler
correction. -/

section

/-! Exact energy forcing from the literal raw, projected, and signed-pressure field identities. -/

section

/-! Actual coercive projected sources have precisely the signed energy forcing required by the
differentiated equation. -/

@[expose] public section

noncomputable section

namespace EulerProjectedEnergyForcing

open InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
    EulerSpatialSobolevInverse
  EulerSobolevCoefficientPressure EulerSobolevTransport EulerEnergyWordCoordinates
      EulerEnergyForcingIdentity
  EulerGevreyCorrectionForcing EulerGevreyDifferentiatedEquation EulerGevreyMetricComparison
      EulerBaseWordMetric
  EulerMildTopWord

variable (period : ℝ) [Fact (0 < period)]

/-- The actual pressure-projected negative source splits into its two positive pressure solves with
the literal PDE signs. -/
theorem projected_negative_split {s : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection s A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (T F : SobolevSpace period s) :
    -(projectedSourceOperator period K κ m c hc hpos (T+F)) =
      -(T+F-coefficientSobolevOperator period K (pressureSobolevOperator period K κ m c hc hpos F) -
        coefficientSobolevOperator period K (pressureSobolevOperator period K κ m c hc hpos T)) :=
            by
  let P := pressureSobolevOperator period K κ m c hc hpos
  let G := coefficientSobolevOperator period K
  change -(T+F-G (P (T+F))) = -(T+F-G (P F)-G (P T))
  rw [map_add P T F, map_add G (P T) (P F)]
  abel

/-- The signed actual pressure is the negative sum of the two genuine component pressure solves. -/
theorem pressure_negative_split {s : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection s A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (T F : SobolevSpace period s) :
    -(pressureSobolevOperator period K κ m c hc hpos (T+F)) =
      -(pressureSobolevOperator period K κ m c hc hpos F + pressureSobolevOperator period K κ m c
          hc hpos T) := by
  rw [map_add]
  exact congrArg (fun x : SobolevSpace period s => -x) (add_comm _ _)

/-- The actual coercive projected source and actual signed pressure give exactly the seven
differentiated correction terms. -/
theorem projected_forcing_word {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection s A) (K0 : CoefficientJet period standardDirection
        6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hL : ∀ i, ‖velocityComponents κ m i‖ ≤ 1)
    (z : SobolevSpace period s) (u v : SobolevSpace period (s + 1)) (hzu : value period z = value
        period u)
    (f : SobolevSpace period s) (I : ExternalWord N) (a : BaseWord 6) :
    word period (-(projectedSourceOperator period K κ m c hc hpos
      (transportBilinear period hs (velocityComponents κ m) hL u v+f)))
      (energyLength_le hN I a) (energyWord I a) +
      EulerSobolevMetricTransport.transportOperator period (by omega : 3 ≤ s) κ m z
        (boundedWordBlock period 1 (energyLength I a) (by
            have := energyLength_le hN I a; omega) (energyWord I a) v) +
      A.operator (word period (-(pressureSobolevOperator period K κ m c hc hpos
        (transportBilinear period hs (velocityComponents κ m) hL u v+f)))
        (energyLength_le hN I a) (energyWord I a)) =
      correctionForcing period hs K K0 N hN (velocityComponents κ m) hL u v f
        (pressureSobolevOperator period K κ m c hc hpos f)
        (pressureSobolevOperator period K κ m c hc hpos
          (transportBilinear period hs (velocityComponents κ m) hL u v)) I a := by
  let TV := transportBilinear period hs (velocityComponents κ m) hL u v
  let D := wordOperator period (⟨⟨energyLength I a, Nat.lt_succ_of_le (energyLength_le hN I
      a)⟩,energyWord I a⟩ : SobolevWord s)
  let Tr := EulerSobolevMetricTransport.transportOperator period (by omega : 3 ≤ s) κ m z
    (boundedWordBlock period 1 (energyLength I a) (by
        have := energyLength_le hN I a; omega) (energyWord I a) v)
  have hf := projected_negative_split period K κ m c hc hpos TV f
  have hp := pressure_negative_split period K κ m c hc hpos TV f
  have he := forcing_word_telescope period hs K K0 N hN κ m hL z u v hzu f
    (pressureSobolevOperator period K κ m c hc hpos f)
    (pressureSobolevOperator period K κ m c hc hpos TV) I a
  have hh := congrArg₂ (fun x y : LiftL2 period => x+Tr+A.operator y) (congrArg D hf) (congrArg D
      hp)
  exact hh.trans he

end EulerProjectedEnergyForcing

end
end

end

@[expose] public section

noncomputable section

namespace EulerProjectedForcingFields

open InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerSobolevTransport EulerMildTopWord
  EulerEnergyWordCoordinates EulerSobolevWordValueIdentity EulerProjectedEnergyForcing
  EulerGevreyCorrectionForcing EulerGevreyMetricComparison EulerBaseWordMetric
      EulerSobolevMetricTransport

variable (period : ℝ) [Fact (0 < period)]

/-- Actual raw-source and pressure identities determine the complete differentiated forcing,
independently of the chosen equivalent higher representative. -/
theorem forcing_word_of_actual_fields {s r : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection s A) (K0 : CoefficientJet period standardDirection
        6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hL : ∀ i, ‖velocityComponents κ m i‖ ≤ 1)
    (z : SobolevSpace period s) (u v : SobolevSpace period (s + 1)) (V : SobolevSpace period r)
    (hzu : value period z = value period u) (hV : value period V = value period v)
    (f raw F P : SobolevSpace period s)
    (hraw : raw = transportBilinear period hs (velocityComponents κ m) hL u v + f)
    (hF : F = -(projectedSourceOperator period K κ m c hc hpos raw))
    (hP : P = -(pressureSobolevOperator period K κ m c hc hpos raw))
    (I : ExternalWord N) (a : BaseWord 6) (horder : 1 + energyLength I a ≤ r) :
    word period F (energyLength_le hN I a) (energyWord I a) +
      transportOperator period (by omega : 3 ≤ s) κ m z
        (boundedWordBlock period 1 (energyLength I a) horder (energyWord I a) V) +
      A.operator (word period P (energyLength_le hN I a) (energyWord I a)) =
      correctionForcing period hs K K0 N hN (velocityComponents κ m) hL u v f
        (pressureSobolevOperator period K κ m c hc hpos f)
        (pressureSobolevOperator period K κ m c hc hpos
          (transportBilinear period hs (velocityComponents κ m) hL u v)) I a := by
  let D := wordOperator period (⟨⟨energyLength I a,Nat.lt_succ_of_le (energyLength_le hN I
      a)⟩,energyWord I a⟩ : SobolevWord s)
  let Tr := transportOperator period (by omega : 3 ≤ s) κ m z
  have hf' := hF.trans (congrArg (fun x : SobolevSpace period s => -(projectedSourceOperator period
      K κ m c hc hpos x)) hraw)
  have hp' := hP.trans (congrArg (fun x : SobolevSpace period s => -(pressureSobolevOperator period
      K κ m c hc hpos x)) hraw)
  have hblock := boundedWordBlock_of_value_eq period V v hV horder
    (by have := energyLength_le hN I a; omega : 1+energyLength I a ≤ s+1) (energyWord I a)
  have he := congrArg₂ (fun x y : SobolevSpace period s => D x +
    Tr (boundedWordBlock period 1 (energyLength I a) horder (energyWord I a) V)+A.operator (D y))
        hf' hp'
  have ht := congrArg (fun b : SobolevSpace period 1 =>
    D (-(projectedSourceOperator period K κ m c hc hpos
      (transportBilinear period hs (velocityComponents κ m) hL u v+f)))+Tr b +
    A.operator (D (-(pressureSobolevOperator period K κ m c hc hpos
      (transportBilinear period hs (velocityComponents κ m) hL u v+f))))) hblock
  exact he.trans (ht.trans (projected_forcing_word period hs K K0 N hN κ m c hc hpos hL z u v hzu f
      I a))

end EulerProjectedForcingFields

end
end

end

section

/-! Literal almost-everywhere representatives of the limiting actual word forcing. -/

section

/-! Actual representatives of linear source, transport, and pressure combinations in Bochner time
spaces. -/

@[expose] public section

noncomputable section

namespace EulerTimeLp

open MeasureTheory Set EulerVolterraConvolution

variable {E V W H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A genuine sum of fixed spatial and time-dependent operator actions has its literal pointwise
representative. -/
theorem timeLinearForcing_ae (T : ℝ) (hT : 0 ≤ T) (D : E →L[ℝ] H) (B : V →L[ℝ] W)
    (A : C(Icc (0 : ℝ) T, W →L[ℝ] H)) (G : C(Icc (0 : ℝ) T, H →L[ℝ] H))
    (U : TimeLp T V) (F P : TimeLp T E) :
    (((D.compLpL 2 (timeMeasure T) F + timeMultiplier T hT A (B.compLpL 2 (timeMeasure T) U) +
      timeMultiplier T hT G (D.compLpL 2 (timeMeasure T) P)) : TimeLp T H) : ℝ → H) =ᵐ[timeMeasure
          T]
      fun t => D (F t) + A (projIcc 0 T hT t) (B (U t)) + G (projIcc 0 T hT t) (D (P t)) := by
  let DF := D.compLpL 2 (timeMeasure T) F
  let BU := B.compLpL 2 (timeMeasure T) U
  let DP := D.compLpL 2 (timeMeasure T) P
  let AB := timeMultiplier T hT A BU
  let GP := timeMultiplier T hT G DP
  filter_upwards [Lp.coeFn_add (DF+AB) GP, Lp.coeFn_add DF AB,
    D.coeFn_compLpL F, B.coeFn_compLpL U, D.coeFn_compLpL P,
    timeMultiplier_ae T hT A BU, timeMultiplier_ae T hT G DP] with t h1 h2 h3 h4 h5 h6 h7
  change (DF+AB+GP) t = _
  simp only [Pi.add_apply] at h1 h2
  rw [h1,h2,h3,h6,h7,h4,h5]
  rfl

end EulerTimeLp

end
end

end

@[expose] public section

noncomputable section

namespace EulerRegularizedForcingRepresentative

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerMildTopWord
  EulerRegularizedForcingWord EulerRegularizedEnergyFamily EulerTimeFamily EulerTimeLp
  EulerVolterraConvolution EulerWeightedForcingTime EulerFiniteMetricEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The limiting word forcing has exactly the differentiated-source plus transport plus pressure
representative. -/
theorem forcingWordTime_ae {q m : ℕ} (hm : m ≤ q + 1) (w : Fin m → Fin 4) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2 + q))) (F P : TimeLp T (SobolevSpace period (q + 1))) :
    (forcingWordTime period hm w T hT A G U F P : ℝ → LiftL2 period) =ᵐ[timeMeasure T]
      fun t => word period (F t) hm w + A (projIcc 0 T hT t)
        (boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w (U t)) +
        G (projIcc 0 T hT t) (word period (P t) hm w) := by
  exact timeLinearForcing_ae T hT
    (wordOperator period (⟨⟨m,Nat.lt_succ_of_le hm⟩,w⟩ : SobolevWord (q+1)))
    (boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w) A G U F P

/-- The limiting finite family has its literal actual word forcing at every component almost
everywhere. -/
theorem forcingFamilyTime_ae {α β : Type*} [Fintype β] {q : ℕ}
    (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4) (hd : ∀ i j, d i j ≤ q + 1)
    (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2 + q))) (F P : TimeLp T (SobolevSpace period (q + 1))) (i
        : α)
        :
    (forcingFamilyTime period d w hd T hT A G U F P i : ℝ → β → LiftL2 period) =ᵐ[timeMeasure T]
      fun t j => word period (F t) (hd i j) (w i j) + A (projIcc 0 T hT t)
        (boundedWordBlock period 1 (d i j) (by
            have := hd i j; omega : 1+d i j ≤ 2+q) (w i j) (U t)) +
        G (projIcc 0 T hT t) (word period (P t) (hd i j) (w i j)) := by
  filter_upwards [familyTime_ae T (fun j => forcingWordTime period (hd i j) (w i j) T hT A G U F P),
    ae_all_iff.mpr (fun j => forcingWordTime_ae period (hd i j) (w i j) T hT A G U F P)] with t h1
        h2
  change familyTime T _ t = _
  rw [h1]
  exact funext h2

/-- The limiting weighted forcing is the genuine finite sum of norms of the literal differentiated
PDE forcing. -/
theorem weighted_forcing_ae {α β : Type*} [Fintype α] [Fintype β] {q : ℕ}
    (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4) (hd : ∀ i j, d i j ≤ q + 1)
    (T : ℝ) (hT : 0 ≤ T) (weights : α → C(Icc (0 : ℝ) T, ℝ))
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2 + q))) (F P : TimeLp T (SobolevSpace period (q + 1))) :
    (weightedForcingTime T hT weights (forcingFamilyTime period d w hd T hT A G U F P) : ℝ → ℝ)
        =ᵐ[timeMeasure T]
      fun t => ∑ i, extendPath T hT (weights i) t * familyNorm (fun j =>
        word period (F t) (hd i j) (w i j) + A (projIcc 0 T hT t)
          (boundedWordBlock period 1 (d i j) (by
              have := hd i j; omega : 1+d i j ≤ 2+q) (w i j) (U t)) +
          G (projIcc 0 T hT t) (word period (P t) (hd i j) (w i j))) := by
  filter_upwards [weightedForcingTime_ae T hT weights (forcingFamilyTime period d w hd T hT A G U F
      P),
    ae_all_iff.mpr (fun i => forcingFamilyTime_ae period d w hd T hT A G U F P i)] with t h1 h2
  rw [h1]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun v : β → LiftL2 period =>
    extendPath T hT (weights i) t * familyNorm v) (h2 i))

end EulerRegularizedForcingRepresentative

end
end

end

section

/-! The constructed Bochner correction source is literally the higher-order nonlinear correction
almost everywhere. -/

@[expose] public section

noncomputable section

namespace EulerTimeCorrectionStrongIdentity

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAsymmetricTransport
  EulerSobolevTransport EulerTimeLp EulerVolterraConvolution EulerTimeCorrectionSource
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine raw source is the literal transport of the actual higher-order representative plus
the prescribed lower-order terms. -/
theorem rawSourceTime_transport_ae {s : ℕ} (hs : 6 ≤ s) (T : ℝ) (hT : 0 ≤ T)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (C : Fin 3 → C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (z : C(Icc (0 : ℝ) T, SobolevSpace period (s + 1)))
    (r e : C(Icc (0 : ℝ) T, SobolevSpace period s)) (U : TimeLp T (SobolevSpace period (s + 1)))
    (hU : (fun t => truncateOperator period s (U t)) =ᵐ[timeMeasure T] extendPath T hT e) :
    (rawSourceTime period hs T hT L hL C0 C z r e U : ℝ → SobolevSpace period s) =ᵐ[timeMeasure T]
      fun t => transportBilinear period hs L hL (extendPath T hT z t + U t) (U t) +
        extendPath T hT (orderZeroPath period hs T L hL C0 C z r e) t := by
  filter_upwards [rawSourceTime_ae period hs T hT L hL C0 C z r e U, hU] with t hraw hu
  have ht := asymmetricTransport_eq period hs L hL (extendPath T hT z t + U t) (U t)
  have hv : truncateOperator period s (extendPath T hT z t + U t) =
      truncateOperator period s (extendPath T hT z t) + extendPath T hT e t :=
    (map_add (truncateOperator period s) (extendPath T hT z t) (U t)).trans
      (congrArg (fun x : SobolevSpace period s => truncateOperator period s (extendPath T hT z
          t)+x) hu)
  have ht' := (congrArg (fun x : SobolevSpace period s => asymmetricTransport period hs L hL x (U
      t)) hv).symm.trans ht
  exact hraw.trans (congrArg (fun v : SobolevSpace period s => v +
    extendPath T hT (orderZeroPath period hs T L hL C0 C z r e) t) ht')

/-- The continuous transport velocity and its higher Sobolev representative have the same actual L²
value almost everywhere. -/
theorem transport_velocity_value_ae {s : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (z : C(Icc (0 : ℝ) T, SobolevSpace period (s + 1))) (e : C(Icc (0 : ℝ) T, SobolevSpace period
        s))
    (U : TimeLp T (SobolevSpace period (s + 1)))
    (hU : (fun t => truncateOperator period s (U t)) =ᵐ[timeMeasure T] extendPath T hT e) :
    (fun t => value period (truncateOperator period s (extendPath T hT z t) + extendPath T hT e t))
        =ᵐ[timeMeasure T]
      fun t => value period (extendPath T hT z t + U t) := by
  filter_upwards [hU] with t ht
  rw [← ht]
  exact congrArg (value period) (map_add (truncateOperator period s) (extendPath T hT z t) (U
      t)).symm

end EulerTimeCorrectionStrongIdentity

end
end

end

@[expose] public section

noncomputable section

namespace EulerCorrectionEnergyTime

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSpatialSobolevInverse EulerCorrectionOperators EulerTimeCorrectionSource
  EulerTimeCorrectionStrongIdentity EulerSobolevWordValueIdentity EulerTimeLp
      EulerVolterraConvolution
  EulerRegularizedEnergyFamily EulerRegularizedForcingRepresentative EulerRegularizedMetricPaths
  EulerRegularizedTopBlocks EulerTransportL2Time EulerWeightedForcingTime EulerSobolevEnergyPaths
  EulerEnergyWordCoordinates  EulerGevreyCorrectionForcing
  EulerGevreyMetricComparison EulerBaseWordMetric EulerSobolevTransport
      EulerSobolevCoefficientPressure
  EulerMildTopWord EulerFiniteMetricEnergy EulerWeightedCylinderEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A local concrete normed-group instance for the actual cylinder Sobolev scale. -/
local instance correctionTimeGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance

/-- A local concrete real normed-space instance for the actual cylinder Sobolev scale. -/
local instance correctionTimeSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual continuous background-plus-error velocity at the energy level. -/
def velocityPath {q : ℕ} {T : ℝ} (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, SobolevSpace period
        (q+1))
        :=
  (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) D.approximation + e

/-- The actual continuous order-zero source along the original energy-level solution. -/
def lowerOrderPath {q : ℕ} (hq : 6 ≤ q + 1) {T : ℝ} (D : CorrectionData period (q + 1) (Icc (0 : ℝ)
    T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, SobolevSpace period
        (q+1))
        :=
  orderZeroPath period hq T (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    D.linear.operatorPath (fun i => (D.quadratic i).operatorPath) D.approximation D.residual e

/-- The genuine full energy-order nonlinear raw time field, constructed using maximal regularity. -/
def rawTime {q : ℕ} (hq : 6 ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 +
        q))) :
    TimeLp T (SobolevSpace period (q+1)) :=
  rawSourceTime period hq T hT (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    D.linear.operatorPath (fun i => (D.quadratic i).operatorPath) D.approximation D.residual e
    (reindexMaximalTime period q T U)

/-- The actual full energy-order projected nonlinear forcing belongs to Bochner L² time. -/
def sourceTime {q : ℕ} (hq : 6 ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 +
        q))) :
    TimeLp T (SobolevSpace period (q+1)) :=
  projectedTime period T hT D.metric D.κ D.direction D.coercivity D.coercivity_pos D.metric_pos
    (rawTime period hq T hT D e U)

/-- The actual signed coercive pressure has full energy-order Bochner regularity. -/
def signedPressureTime {q : ℕ} (hq : 6 ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 +
        q))) :
    TimeLp T (SobolevSpace period (q+1)) :=
  pressureTime period T hT D.metric D.κ D.direction D.coercivity D.coercivity_pos D.metric_pos
    (rawTime period hq T hT D e U)

/-- The actual limiting weighted word forcing constructed from the genuine correction time fields.
-/
def weightedCorrectionForcing {q : ℕ} (hq : 6 ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (R : C(Icc (0 : ℝ) T, ℝ))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 +
        q))) :
        TimeLp T ℝ :=
  weightedForcingTime T hT (fun I : ExternalWord N => gevreyWeightPath T R I.1.val)
    (forcingFamilyTime period energyLength energyWord (energyLength_le hN) T hT
      (transportL2Path period (by omega : 3 ≤ q+1) D.κ D.direction T (velocityPath period D e))
      (metricOperatorPath period T D.metric.coefficient hG) U
      (sourceTime period hq T hT D e U) (signedPressureTime period hq T hT D e U))

/-- The seven literal spatial correction terms evaluated on an actual higher Sobolev representative.
-/
def correctionArray {q : ℕ} (hq : 6 ≤ q + 1) {T : ℝ}
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (K6 : ∀ t, CoefficientJet period standardDirection 6 (D.metric.coefficient t))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (V : SobolevSpace period ((q + 1) + 1)) (τ : Icc (0 : ℝ) T) : ExternalWord N → BaseWord 6 →
        LiftL2
        period :=
  let f := lowerOrderPath period hq D e τ
  correctionForcing period hq (D.metric.jet τ) (K6 τ) N hN (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    (D.approximation τ+V) V f
    (pressureSobolevOperator period (D.metric.jet τ) D.κ D.direction D.coercivity D.coercivity_pos
        (D.metric_pos τ) f)
    (pressureSobolevOperator period (D.metric.jet τ) D.κ D.direction D.coercivity D.coercivity_pos
        (D.metric_pos τ)
      (transportBilinear period hq (velocityComponents D.κ D.direction)
        (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) (D.approximation
            τ+V) V))

/-- The constructed actual weighted time forcing is exactly the seven genuine correction terms
almost everywhere. -/
theorem weightedCorrectionForcing_ae {q : ℕ} (hq : 6 ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (K6 : ∀ t, CoefficientJet period standardDirection 6 (D.metric.coefficient t))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (R : C(Icc (0 : ℝ) T, ℝ))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e)) Filter.atTop
        (𝓝 U)) :
    (weightedCorrectionForcing period hq T hT D hG N hN R e U : ℝ → ℝ) =ᵐ[timeMeasure T]
      fun t => weightedForcingSum (R (projIcc 0 T hT t)) (fun I : ExternalWord N => I.1.val)
        (correctionArray period hq D K6 N hN e (reindexMaximalTime period q T U t) (projIcc 0 T hT
            t)) := by
  let V := reindexMaximalTime period q T U
  let A := transportL2Path period (by omega : 3 ≤ q+1) D.κ D.direction T (velocityPath period D e)
  let G := metricOperatorPath period T D.metric.coefficient hG
  let F := sourceTime period hq T hT D e U
  let P := signedPressureTime period hq T hT D e U
  let raw := rawTime period hq T hT D e U
  have hV := reindexMaximalTime_restriction period T hT e U hU
  have hr := rawSourceTime_transport_ae period hq T hT (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    D.linear.operatorPath (fun i => (D.quadratic i).operatorPath) D.approximation D.residual e V hV
  have hv := transport_velocity_value_ae period T hT D.approximation e V hV
  filter_upwards [weighted_forcing_ae period energyLength energyWord (energyLength_le hN) T hT
      (fun I : ExternalWord N => gevreyWeightPath T R I.1.val) A G U F P,
    hr, hv, reindexMaximalTime_value period q T U,
    projectedTime_ae period T hT D.metric D.κ D.direction D.coercivity D.coercivity_pos
        D.metric_pos raw,
    pressureTime_ae period T hT D.metric D.κ D.direction D.coercivity D.coercivity_pos D.metric_pos
        raw]
    with t hweight hraw hvel hVU hF hP
  change weightedForcingTime T hT _ (forcingFamilyTime period energyLength energyWord
      (energyLength_le hN) T hT A G U F P) t = _
  rw [hweight]
  apply Finset.sum_congr rfl
  intro I _
  apply congrArg (fun v : BaseWord 6 → LiftL2 period => EulerPacketWeights.weight (R (projIcc 0 T
      hT t)) I.1.val * familyNorm v)
  funext a
  let τ := projIcc 0 T hT t
  change word period (F t) (energyLength_le hN I a) (energyWord I a) +
    transportL2Path period (by omega : 3 ≤ q+1) D.κ D.direction T (velocityPath period D e) τ
      (boundedWordBlock period 1 (energyLength I a) (by
          have := energyLength_le hN I a; omega) (energyWord I a) (U t)) +
    (D.metric.coefficient τ).operator (word period (P t) (energyLength_le hN I a) (energyWord I a))
        = _
  rw [transportL2Path_apply]
  exact EulerProjectedForcingFields.forcing_word_of_actual_fields period hq (D.metric.jet τ) (K6 τ)
      N hN
    D.κ D.direction D.coercivity D.coercivity_pos (D.metric_pos τ)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    (velocityPath period D e τ) (D.approximation τ+V t) (V t) (U t) hvel hVU.symm
    (lowerOrderPath period hq D e τ) (raw t) (F t) (P t) hraw hF hP I a
    (by have := energyLength_le hN I a; omega)

end EulerCorrectionEnergyTime
