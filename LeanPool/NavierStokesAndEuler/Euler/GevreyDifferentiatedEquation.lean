/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionForcing
public import LeanPool.NavierStokesAndEuler.Euler.SobolevNonlinearCompatibility

@[expose] public section

/-! Exact spatial differentiation of the actual nonlinear correction equation. -/

noncomputable section

namespace EulerGevreyDifferentiatedEquation

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerBaseWordMetric EulerGevreyMetricComparison
  EulerSobolevWordLevel EulerSobolevTransport EulerSobolevTransportCommutator
  EulerSobolevBaseCommutator EulerTransportL2Bilinear EulerGevreyBaseTransport
  EulerGevreyForcingComponents EulerGevreyCorrectionForcing EulerSobolevCoefficientPressure

variable (period : ℝ) [Fact (0 < period)]

local instance diffEqGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance diffEqSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual continuous linear map taking one external and one base derivative word. -/
def energyWordOperator {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (I : ExternalWord N) (a : BaseWord q) :
    SobolevSpace period s →L[ℝ] LiftL2 period :=
  ((valueOperator period 0).comp
    (wordAtLevel period (s := q) 0 a.1.val a.2 (by have := a.1.isLt; omega))).comp
    (wordAtLevel period (s := s) q I.1.val I.2 (by have := I.1.isLt; omega))

/-- This continuous operator is exactly the genuine jet word in the metric energy. -/
theorem energyWordOperator_apply {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (I : ExternalWord N) (a :
  BaseWord q)
    (u : SobolevSpace period s) :
    energyWordOperator period q N hN I a u = energyValues period q N hN u I a := by
  change value period (wordAtLevel period 0 a.1.val a.2 (by have := a.1.isLt; omega)
    (wordAtLevel period q I.1.val I.2 (by have := I.1.isLt; omega) u)) = _
  rw [wordAtLevel_value]
  exact EulerPressureJetIdentities.SpatialJet.word_unique
    (toJet period (wordAtLevel period q I.1.val I.2 (by have := I.1.isLt; omega) u))
    (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet period u) I.2 (by have := I.1.isLt;
      omega))
    (wordAtLevel_value period q I.1.val I.2 (by have := I.1.isLt; omega) u)
    (by have := a.1.isLt; omega) (by have := a.1.isLt; omega) a.2

/-- Genuine energy words are linear in the differentiated field. -/
theorem energyValues_add {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (u v : SobolevSpace period s) :
    energyValues period q N hN (u+v) = energyValues period q N hN u + energyValues period q N hN v
      := by
  funext I a
  simp only [← energyWordOperator_apply, map_add, Pi.add_apply]

/-- Genuine energy words commute with subtraction. -/
theorem energyValues_sub {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (u v : SobolevSpace period s) :
    energyValues period q N hN (u-v) = energyValues period q N hN u - energyValues period q N hN v
      := by
  funext I a
  simp only [← energyWordOperator_apply, map_sub, Pi.sub_apply]

/-- The literal undifferentiated transport acting on the final external/base derivative. -/
def topTransport {s : ℕ} (N : ℕ) (hN : N+6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (u v : SobolevSpace period (s+1)) :
    ExternalWord N → BaseWord 6 → LiftL2 period := fun I a =>
  transportL2Bilinear period (by norm_num : 3 ≤ 7) L
    (restrictOperator period (by omega : 7 ≤ s+1) u)
    (wordAtLevel period 1 a.1.val a.2 (by have := a.1.isLt; omega)
      (wordAtLevel period 7 I.1.val I.2 (by have := I.1.isLt; omega) v))

/-- External and base transport commutators telescope to the exact differentiated transport. -/
theorem transport_telescope {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N+6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) :
    externalTransportForcing period hs N hN L hL u v + baseTransportForcing period N hN L hL u v =
      energyValues period 6 N hN (transportBilinear period hs L hL u v) - topTransport period N hN
        L u v := by
  funext I a
  let D := (valueOperator period 0).comp
    (wordAtLevel period 0 a.1.val a.2 (by have := a.1.isLt; omega : a.1.val+0 ≤ 6))
  let X := wordAtLevel period 6 I.1.val I.2 (by have := I.1.isLt; omega) (transportBilinear period
    hs L hL u v)
  let Y := transportBilinear period (by norm_num : 6 ≤ 6) L hL
    (restrictOperator period (by omega : 7 ≤ s+1) u)
    (wordAtLevel period 7 I.1.val I.2 (by have := I.1.isLt; omega) v)
  let Z := topTransport period N hN L u v I a
  have he : externalTransportForcing period hs N hN L hL u v I a =
      D (externalCommutator period hs I.1.val I.2 (by have := I.1.isLt; omega) L hL u v) := by
    symm
    exact wordAtLevel_value period 0 a.1.val a.2 (by have := a.1.isLt; omega) _
  have hext : externalCommutator period hs I.1.val I.2 (by have := I.1.isLt; omega) L hL u v = X-Y
    :=
    externalCommutator_apply period hs I.1.val I.2 (by have := I.1.isLt; omega) L hL u v
  have he' : externalTransportForcing period hs N hN L hL u v I a = D X-D Y :=
    he.trans ((congrArg D hext).trans (map_sub D X Y))
  have hb : baseTransportForcing period N hN L hL u v I a = D Y-Z :=
    baseCommutator_apply period a.1.val (by have := a.1.isLt; omega) a.2 L hL
      (restrictOperator period (by omega : 7 ≤ s+1) u)
      (wordAtLevel period 7 I.1.val I.2 (by have := I.1.isLt; omega) v)
  have hx : energyValues period 6 N hN (transportBilinear period hs L hL u v) I a = D X :=
    (energyWordOperator_apply period 6 N hN I a (transportBilinear period hs L hL u v)).symm
  change externalTransportForcing period hs N hN L hL u v I a +
    baseTransportForcing period N hN L hL u v I a =
      energyValues period 6 N hN (transportBilinear period hs L hL u v) I a-Z
  calc
    _ = (D X-D Y)+(D Y-Z) := congrArg₂ (fun x y : LiftL2 period => x+y) he' hb
    _ = D X-Z := by abel
    _ = _ := congrArg (fun x : LiftL2 period => x-Z) hx.symm

/-- Taking a word of the actual coefficient operator gives the word of its genuine product jet. -/
theorem coefficient_word {s n : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (p : SobolevSpace period s) (hn : n ≤ s) (w : Fin n → Fin 4) :
    (toJet period (coefficientSobolevOperator period K p)).word w =
      (EulerSpatialSobolevInverse.SpatialJet.multiply K (toJet period p)).word w :=
  EulerPressureJetIdentities.SpatialJet.word_unique _ _ (coefficientSobolevOperator_value period K
    p) hn hn w

/-- The external pressure commutator is the actual difference of two Sobolev coefficient products. -/
theorem externalPressure_as_difference {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N+6 ≤ s) (p : SobolevSpace period s) (I : ExternalWord N) (a : BaseWord 6) :
    externalPressureForcing period K N hN p I a =
      value period (wordAtLevel period 0 a.1.val a.2 (by have := a.1.isLt; omega)
        (wordAtLevel period 6 I.1.val I.2 (by have := I.1.isLt; omega) (coefficientSobolevOperator
          period K p) -
          coefficientSobolevOperator period K0 (wordAtLevel period 6 I.1.val I.2 (by have :=
            I.1.isLt; omega) p))) := by
  rw [wordAtLevel_value]
  apply EulerPressureJetIdentities.SpatialJet.word_unique _ _ _ (by have := a.1.isLt; omega)
    (by have := a.1.isLt; omega) a.2
  change _ = valueOperator period 6 (_ - _)
  rw [map_sub]
  change _ = value period (wordAtLevel period 6 I.1.val I.2 (by have := I.1.isLt; omega)
    (coefficientSobolevOperator period K p)) - value period
      (coefficientSobolevOperator period K0 (wordAtLevel period 6 I.1.val I.2 (by have := I.1.isLt;
        omega) p))
  apply congrArg₂ (fun x y : LiftL2 period => x-y)
  · symm
    exact (wordAtLevel_value period 6 I.1.val I.2 (by have := I.1.isLt; omega)
      (coefficientSobolevOperator period K p)).trans (coefficient_word period K p (by have :=
        I.1.isLt; omega) I.2)
  · symm
    exact (coefficientSobolevOperator_value period K0
      (wordAtLevel period 6 I.1.val I.2 (by have := I.1.isLt; omega) p)).trans
      (congrArg A.operator (wordAtLevel_value period 6 I.1.val I.2 (by have := I.1.isLt; omega) p))

/-- The base pressure commutator is the actual differentiated product minus its top coefficient action. -/
theorem basePressure_as_difference {s : ℕ} {A : SmoothCoefficient period}
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N+6 ≤ s) (p : SobolevSpace period s) (I : ExternalWord N) (a : BaseWord 6) :
    basePressureForcing period K0 N hN p I a =
      value period (wordAtLevel period 0 a.1.val a.2 (by have := a.1.isLt; omega)
        (coefficientSobolevOperator period K0 (wordAtLevel period 6 I.1.val I.2 (by have :=
          I.1.isLt; omega) p))) -
          A.operator (energyValues period 6 N hN p I a) := by
  rw [wordAtLevel_value]
  apply congrArg (fun z => z - A.operator (energyValues period 6 N hN p I a))
  apply EulerPressureJetIdentities.SpatialJet.word_unique _ _ _ (by have := a.1.isLt; omega)
    (by have := a.1.isLt; omega) a.2
  rw [coefficientSobolevOperator_value, wordAtLevel_value]

/-- External and base coefficient commutators telescope to the exact differentiated pressure term. -/
theorem pressure_telescope {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N+6 ≤ s) (p : SobolevSpace period s) :
    externalPressureForcing period K N hN p + basePressureForcing period K0 N hN p =
      energyValues period 6 N hN (coefficientSobolevOperator period K p) -
        (fun I a => A.operator (energyValues period 6 N hN p I a)) := by
  funext I a
  change externalPressureForcing period K N hN p I a + basePressureForcing period K0 N hN p I a =
    energyValues period 6 N hN (coefficientSobolevOperator period K p) I a - A.operator
      (energyValues period 6 N hN p I a)
  rw [externalPressure_as_difference period K K0 N hN p I a,
    basePressure_as_difference period K0 N hN p I a]
  rw [← energyWordOperator_apply period 6 N hN I a (coefficientSobolevOperator period K p)]
  let D := (valueOperator period 0).comp
    (wordAtLevel period 0 a.1.val a.2 (by have := a.1.isLt; omega : a.1.val+0 ≤ 6))
  let X := wordAtLevel period 6 I.1.val I.2 (by have := I.1.isLt; omega)
    (coefficientSobolevOperator period K p)
  let Y := coefficientSobolevOperator period K0 (wordAtLevel period 6 I.1.val I.2 (by have :=
    I.1.isLt; omega) p)
  let Z := A.operator (energyValues period 6 N hN p I a)
  change D (X-Y) + (D Y-Z) = D X-Z
  rw [map_sub]
  abel

/-- The seven bounded forcing terms are exactly the remainder in the differentiated actual correction equation. -/
theorem correction_differentiated_identity {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N+6 ≤ s) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (f p0 p1 : SobolevSpace period s) :
    energyValues period 6 N hN (transportBilinear period hs L hL u v + f -
      coefficientSobolevOperator period K p0 - coefficientSobolevOperator period K p1) =
      topTransport period N hN L u v - (fun I a => A.operator (energyValues period 6 N hN (p0+p1) I
        a)) -
        correctionForcing period hs K K0 N hN L hL u v f p0 p1 := by
  have ht := transport_telescope period hs N hN L hL u v
  have hp0 := pressure_telescope period K K0 N hN p0
  have hp1 := pressure_telescope period K K0 N hN p1
  simp only [energyValues_sub, energyValues_add]
  funext I a
  have ht' := congrFun (congrFun ht I) a
  have hp0' := congrFun (congrFun hp0 I) a
  have hp1' := congrFun (congrFun hp1 I) a
  simp only [Pi.add_apply, Pi.sub_apply] at ht' hp0' hp1'
  simp only [correctionForcing, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, map_add]
  rw [eq_sub_iff_add_eq] at ht' hp0' hp1'
  rw [← ht', ← hp0', ← hp1']
  abel

end EulerGevreyDifferentiatedEquation
