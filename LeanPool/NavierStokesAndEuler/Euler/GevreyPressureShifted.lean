/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyPressureTransport

@[expose] public section

/-! Cutoff-independent nonlinear pressure bounds for actual finite-Sobolev transport sources. -/

noncomputable section

namespace EulerGevreyPressureTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerH6Pressure EulerPacketWeights
  EulerSobolevGevreyOperators EulerSobolevTransport EulerSobolevL2Product EulerFunctionalVelocity
  EulerH6Nonlinear EulerVectorCylinder EulerSobolevTransportCommutator
    EulerSobolevCoefficientPressure
  EulerSobolevGevreyProduct EulerSobolevHeat
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

local instance shiftedTransportGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
  inferInstance
local instance shiftedTransportSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
  inferInstance

/-- The shifted actual H⁶ pressure sum stops one derivative below the velocity cutoff. -/
def shiftedPressureNorm {s : ℕ} (N : ℕ) (ρ : ℝ) (p : SobolevSpace period s) : ℝ :=
  ∑ n ∈ Finset.range (N+1), ((n+1 : ℕ) : ℝ)*weight ρ (n+1)*blockNorm period (toJet period p) 6 n

/-- Continuity on the genuine Sobolev domain of the shifted pressure norm. -/
theorem continuous_shiftedPressureNorm {s : ℕ} (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ) :
    Continuous (shiftedPressureNorm period (s := s) N ρ) := by
  apply continuous_finsetSum
  intro n hn
  exact (continuous_blockNorm period (by have := Finset.mem_range.mp hn; omega : n+6 ≤
    s)).const_mul _

/-- The actual shifted H⁶ nonlinear pressure estimate on smooth Sobolev representatives. -/
theorem transportPressure_shifted_smooth {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ)
    (N : ℕ) (hN : N+6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4*M*(ρ*Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (hgL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
      period)) :
    shiftedPressureNorm period N ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (16*M*productConstant period 3)*weightedNorm period 6 (N+1) ρ u*weightedLoss period 6 (N+1) ρ
        v := by
  let b := velocityMap L ∘ f
  have hb := postcomp_smooth period (velocityMap L) f hf
  have hbL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w b) 2 (liftMeasure
    period) :=
    fun j w => postcomp_word_memLp period (le_refl j) (velocityMap L) f hf (fun r _ a => hfL r a) w
  have hp := nonlinear_pressure_shifted_bound period K (toJet period (transportBilinear period hs L
    hL u v))
    κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase hsmall hcoeff b g hb hg hbL hgL
    (transport_ae_velocityMap period hs L hL u v f g hu hv hg)
  have heq : shiftedPressureNorm period N ρ (transportPressure period hs K κ m c hc hpos L hL u v) =
      ∑ n ∈ Finset.range (N+1), ((n+1 : ℕ) : ℝ) * weight ρ (n+1) * blockNorm period
        ((toJet period (transportBilinear period hs L hL u v)).solvePressure K κ m c hc hpos) 6 n
          := by
    apply Finset.sum_congr rfl
    intro n hn
    exact congrArg (fun a : ℝ => ((n+1 : ℕ) : ℝ)*weight ρ (n+1)*a)
      (pressure_block_eq period (q := 6) (n := n) K κ m c hc hpos (transportBilinear period hs L hL
        u v)
        (by have := Finset.mem_range.mp hn; omega : n+6 ≤ s))
  rw [heq]
  conv_rhs => rw [weightedNorm_eq_classical period 6 (N+1) (by omega) ρ u f hu hf,
    weightedLoss_eq_classical period 6 (N+1) (by omega) ρ v g hv hg]
  have hcoef : 0 ≤ 4*M*productConstant period 3 := mul_nonneg (by linarith) (productConstant_nonneg
    period 3)
  have hv0 : 0 ≤ ∑ j ∈ Finset.range (N+2), (j : ℝ)*weight ρ j * wordSobolevNorm period 6 j g :=
    Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (weight_pos hρ j).le)
      (wordSobolevNorm_nonneg period 6 j g)
  exact hp.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (velocityMap_weighted_bound period 6 (N+1) ρ hρ L hL f hf hfL) hcoef) hv0).trans_eq (by ring))

/-- The shifted nonlinear pressure estimate holds for the actual finite-Sobolev fields used by the solver. -/
theorem transportPressure_shifted {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ)
    (N : ℕ) (hN : N+6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4*M*(ρ*Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) :
    shiftedPressureNorm period N ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (16*M*productConstant period 3)*weightedNorm period 6 (N+1) ρ u*weightedLoss period 6 (N+1) ρ
        v := by
  let U : ℕ → SobolevSpace period (s+1) := fun n => restrictOperator period (by omega : s+1 ≤
    s+1+3) (smoothApprox period (s+1) n u)
  let V : ℕ → SobolevSpace period (s+1) := fun n => restrictOperator period (by omega : s+1 ≤
    s+1+3) (smoothApprox period (s+1) n v)
  have hU : Filter.Tendsto U Filter.atTop (𝓝 u) := smoothApprox_tendsto period u
  have hV : Filter.Tendsto V Filter.atTop (𝓝 v) := smoothApprox_tendsto period v
  have hpairs : Filter.Tendsto (fun n => (U n,V n)) Filter.atTop (𝓝 (u,v)) := hU.prodMk_nhds hV
  have hP : Filter.Tendsto
      (fun p : SobolevSpace period (s+1) × SobolevSpace period (s+1) => transportPressure period hs
        K κ m c hc hpos L hL p.1 p.2)
      (𝓝 (u,v)) (𝓝 (transportPressure period hs K κ m c hc hpos L hL u v)) :=
    (transportPressure_continuous period hs K κ m c hc hpos L hL).tendsto (u,v)
  have hpress := hP.comp hpairs
  have hW5 : Continuous (shiftedPressureNorm period (s := s) N ρ) := continuous_shiftedPressureNorm
    period N hN ρ
  have hleft := (hW5.tendsto _).comp hpress
  have hW : Continuous (weightedNorm period (s := s+1) 6 (N+1) ρ) := continuous_weighted_blockNorm
    period (N+1) (by omega) ρ
  have hY : Continuous (weightedLoss period (s := s+1) 6 (N+1) ρ) := continuous_weightedLoss period
    6 (N+1) (by omega) ρ
  have hright : Filter.Tendsto (fun n => (16*M*productConstant period 3)*weightedNorm period 6
    (N+1) ρ (U n)*weightedLoss period 6 (N+1) ρ (V n))
      Filter.atTop (𝓝 ((16*M*productConstant period 3)*weightedNorm period 6 (N+1) ρ u*weightedLoss
        period 6 (N+1) ρ v)) :=
    ((hW.tendsto u |>.comp hU).const_mul (16*M*productConstant period 3)).mul (hY.tendsto v |>.comp
      hV)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨f,hf,hfs,hfL⟩ := smoothApprox_representative_all period n u
  obtain ⟨g,hg,hgs,hgL⟩ := smoothApprox_representative_all period n v
  exact transportPressure_shifted_smooth period hs K κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase
    hsmall hcoeff
    L hL (U n) (V n) f g hf hg hfs hgs hfL hgL


end EulerGevreyPressureTransport
