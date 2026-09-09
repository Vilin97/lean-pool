/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyOrderZero
public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionEquation

/-! Exact transport/order-zero splitting of the constructed correction source and its actual
pressure. -/

@[expose] public section


noncomputable section

namespace EulerGevreyOrderZero

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevL2Product EulerH6Nonlinear EulerH6Pressure
      EulerJetProductBounds
  EulerPacketWeights EulerSobolevGevreyOperators EulerSobolevCoefficientPressure EulerVectorCylinder
  EulerCorrectionOperators EulerSobolevTransport
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance splitGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance splitSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance
/-- Cache the standard `SeminormedAddCommGroup (SobolevSpace period (q+1) →L[ℝ] SobolevSpace
period (q+1) →L[ℝ] SobolevSpace period q)` instance to shorten typeclass synthesis. -/
local instance splitBilinearGroup (q : ℕ) : SeminormedAddCommGroup
    (SobolevSpace period (q+1) →L[ℝ] SobolevSpace period (q+1) →L[ℝ] SobolevSpace period q) :=
        inferInstance

/-- The fixed-level algebraic expression is exactly the algebraic term used in the mild solver. -/
theorem algebraicAt_eq {s : ℕ} (hs : 6 ≤ s)
    (C : Fin 3 → SobolevSpace period s →L[ℝ] SobolevSpace period s)
    (u v : SobolevSpace period (s + 1)) :
    algebraicAt period hs C (truncateOperator period s u) (truncateOperator period s v) =
      algebraicBilinear period hs C u v := by
  rw [algebraicBilinear_apply]
  rfl

/-- The order-zero background transport is exactly e·D z_a in the mild solver. -/
theorem backgroundDrift_eq {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u background : SobolevSpace period (s + 1)) :
    backgroundDrift period hs L hL background (truncateOperator period s u) =
      transportBilinear period hs L hL u background := by
  rw [transportBilinear_apply]
  rfl

/-- Exact splitting of the actual nonlinear increment into top transport plus the order-zero source.
-/
theorem correction_split_identity {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : SobolevSpace period s →L[ℝ] SobolevSpace period s)
    (C : Fin 3 → SobolevSpace period s →L[ℝ] SobolevSpace period s)
    (background e : SobolevSpace period (s + 1)) (r : SobolevSpace period s) :
    r + linearize (eulerBilinear period hs L hL C) (C0.comp (truncateOperator period s)) background
        e +
      eulerBilinear period hs L hL C e e =
      transportBilinear period hs L hL (background+e) e +
        orderZeroSource period hs L hL C0 C background r (truncateOperator period s e) := by
  have hzero : orderZeroSource period hs L hL C0 C background r (truncateOperator period s e) =
      r + transportBilinear period hs L hL e background + C0 (truncateOperator period s e) +
        algebraicBilinear period hs C background e + algebraicBilinear period hs C e background +
          algebraicBilinear period hs C e e := by
    simp only [orderZeroSource, backgroundDrift, algebraicAt, transportBilinear_apply,
      algebraicBilinear_apply, coordinateProduct_apply]
  have halg : r + linearize (eulerBilinear period hs L hL C) (C0.comp (truncateOperator period s))
      background e +
      eulerBilinear period hs L hL C e e =
      transportBilinear period hs L hL (background+e) e +
        (r + transportBilinear period hs L hL e background + C0 (truncateOperator period s e) +
          algebraicBilinear period hs C background e + algebraicBilinear period hs C e background +
            algebraicBilinear period hs C e e) := by
    simp only [linearize_apply, eulerBilinear, add_apply, map_add, ContinuousLinearMap.comp_apply]
    abel
  exact halg.trans (congrArg (fun a => transportBilinear period hs L hL (background+e) e + a)
      hzero.symm)

/-- Actual finite weighted Sobolev norms are invariant under sign. -/
theorem weightedNorm_neg {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (u : SobolevSpace period s) :
    weightedNorm period q N ρ (-u) = weightedNorm period q N ρ u := by
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  unfold blockNorm
  apply Finset.sum_congr rfl
  intro r hr
  rw [levelNorm_eq_words, levelNorm_eq_words]
  apply Finset.sum_congr rfl
  intro w _
  have hnr : n+r ≤ s := by have := Finset.mem_range.mp hn; have := Finset.mem_range.mp hr; omega
  rw [toJet_word period (-u) hnr, toJet_word period u hnr]
  change ‖-u.val ⟨⟨n+r, by omega⟩,w⟩‖ = ‖u.val ⟨⟨n+r, by omega⟩,w⟩‖
  exact norm_neg _

/-- The actual order-zero pressure bound follows from the genuine projected inverse and the derived
nonlinear estimate. -/
theorem orderZeroPressure_bound {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (G : SmoothCoefficient period) (KG : EulerSpatialSobolevInverse.CoefficientJet period
        standardDirection s G)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪G.coefficient x v, v⟫_ℝ)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict KG 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period KG 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : SmoothCoefficient period) (K0 : EulerSpatialSobolevInverse.CoefficientJet period
        standardDirection s C0)
    (C : Fin 3 → SmoothCoefficient period)
    (K : ∀ i, EulerSpatialSobolevInverse.CoefficientJet period standardDirection s (C i))
    (background : SobolevSpace period (s + 1)) (r e : SobolevSpace period s) :
    weightedNorm period 6 N ρ (-(pressureSobolevOperator period KG κ m c hc hpos
      (orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
        (fun i => coefficientSobolevOperator period (K i)) background r e))) ≤
      2*M*(weightedNorm period 6 N ρ r +
      (productConstant period 3 * (∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator
          period s i background)) +
        weightedCoefficient period K0 6 N ρ +
        2 * (∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ) * productConstant period 3 *
          weightedNorm period 6 N ρ (truncateOperator period s background)) * weightedNorm period 6
              N ρ e +
      (∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ) * productConstant period 3 *
          (weightedNorm period 6 N ρ e)^2) := by
  rw [weightedNorm_neg period 6 N hN]
  exact (weightedNorm_pressure period KG κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase hsmall hcoeff
      _).trans
    (mul_le_mul_of_nonneg_left (orderZeroSource_bound period hs N hN ρ hρ L hL C0 K0 C K background
        r e)
      (by linarith : 0 ≤ 2*M))

/-- The solver's actual raw source has exactly the transport/order-zero decomposition used by the
energy estimate. -/
theorem correctionData_rawSource_split {s : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period s T) (hs : 6 ≤ s) (t : T) (e : SobolevSpace period (s + 1)) :
    D.rawSource period hs t e =
      transportBilinear period hs (velocityComponents D.κ D.direction)
        (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) (D.approximation
            t+e) e +
      orderZeroSource period hs (velocityComponents D.κ D.direction)
        (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
        (coefficientSobolevOperator period (D.linear.jet t))
        (fun i => coefficientSobolevOperator period ((D.quadratic i).jet t))
        (D.approximation t) (D.residual t) (truncateOperator period s e) :=
  correction_split_identity period hs _ _ _ _ _ _ _

/-- The actual signed correction pressure is the sum of its order-zero and transport pressure
solves. -/
theorem correctionData_pressure_split {s : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period s T) (hs : 6 ≤ s) (t : T) (e : SobolevSpace period (s + 1)) :
    D.pressure period hs t e =
      -(pressureSobolevOperator period (D.metric.jet t) D.κ D.direction D.coercivity
          D.coercivity_pos (D.metric_pos t)
        (transportBilinear period hs (velocityComponents D.κ D.direction)
          (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
              (D.approximation t+e) e)) +
      -(pressureSobolevOperator period (D.metric.jet t) D.κ D.direction D.coercivity
          D.coercivity_pos (D.metric_pos t)
        (orderZeroSource period hs (velocityComponents D.κ D.direction)
          (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
          (coefficientSobolevOperator period (D.linear.jet t))
          (fun i => coefficientSobolevOperator period ((D.quadratic i).jet t))
          (D.approximation t) (D.residual t) (truncateOperator period s e))) := by
  unfold CorrectionData.pressure
  simp only [correctionData_rawSource_split period D hs t e, map_add, neg_add]

end EulerGevreyOrderZero
