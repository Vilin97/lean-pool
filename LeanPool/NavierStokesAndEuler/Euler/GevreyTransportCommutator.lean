/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevTransportCommutator

@[expose] public section

/-! The actual finite-Sobolev external transport commutator satisfies the Gevrey radius-loss bound.
  -/

noncomputable section

namespace EulerSobolevTransportCommutator

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerH6Pressure EulerPacketWeights
  EulerSobolevGevreyOperators EulerSobolevWordLevel EulerSobolevTransport EulerSobolevL2Product
  EulerFunctionalVelocity EulerH6Nonlinear EulerVectorCylinder EulerExternalTransportCommutator
  EulerSobolevGevreyProduct EulerSobolevHeat
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

local instance weightedCommGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
  inferInstance
local instance weightedCommSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual finite weighted derivative-loss norm. -/
def weightedLoss {s : ℕ} (q N : ℕ) (ρ : ℝ) (u : SobolevSpace period s) : ℝ :=
  ∑ n ∈ Finset.range (N+1), (n : ℝ)*weight ρ n*blockNorm period (toJet period u) q n

theorem weightedLoss_nonneg {s : ℕ} (q N : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (u : SobolevSpace period s) :
    0 ≤ weightedLoss period q N ρ u :=
  Finset.sum_nonneg fun n _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (weight_pos hρ n).le)
    (blockNorm_nonneg _)

/-- Continuity of the actual finite loss norm. -/
theorem continuous_weightedLoss {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ) :
    Continuous (weightedLoss period (s := s) q N ρ) := by
  apply continuous_finsetSum
  intro n hn
  exact (continuous_blockNorm period (by have := Finset.mem_range.mp hn; omega : n+q ≤
    s)).const_mul _

/-- Exact identification of weighted complete-Sobolev blocks with classical representative norms. -/
theorem weightedNorm_eq_classical {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ)
    (u : SobolevSpace period s) (f : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    weightedNorm period q N ρ u = ∑ n ∈ Finset.range (N+1), weight ρ n*wordSobolevNorm period q n f
      := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [blockNorm_eq_classical period (toJet period u) (by have := Finset.mem_range.mp hn; omega) f
    hu hf]

/-- The same exact identification for the derivative-loss norm. -/
theorem weightedLoss_eq_classical {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ)
    (u : SobolevSpace period s) (f : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    weightedLoss period q N ρ u = ∑ n ∈ Finset.range (N+1), (n : ℝ)*weight ρ n*wordSobolevNorm
      period q n f := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [blockNorm_eq_classical period (toJet period u) (by have := Finset.mem_range.mp hn; omega) f
    hu hf]

/-- Weighted sum of the genuine H⁶ external transport commutators. -/
def weightedCommutatorNorm {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) : ℝ :=
  ∑ n : Fin (N+1), weight ρ n.val * ∑ w : Fin n.val → Fin 4,
    sumNorm period (externalCommutator period hs n.val w (by have := n.isLt; omega) L hL u v)

/-- The weighted commutator expression is continuous in its actual finite-Sobolev inputs. -/
theorem continuous_weightedCommutatorNorm {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) :
    Continuous (fun p : SobolevSpace period (s+1) × SobolevSpace period (s+1) =>
      weightedCommutatorNorm period hs N hN ρ L hL p.1 p.2) := by
  apply continuous_finsetSum
  intro n _
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro w _
  exact (continuous_sumNorm period 6).comp
    (externalCommutator period hs n.val w (by have := n.isLt; omega) L hL).continuous₂

/-- The external commutator bound for actual smooth representatives depends only on derivatives inside the energy cutoff. -/
theorem weightedCommutator_smooth_bound {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N+6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (hgL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
      period)) :
    weightedCommutatorNorm period hs N hN ρ L hL u v ≤
      (4*productConstant period 3)*ρ⁻¹*weightedNorm period 6 N ρ u*weightedLoss period 6 N ρ v := by
  let b := velocityMap L ∘ f
  have hb := postcomp_smooth period (velocityMap L) f hf
  have hbL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w b) 2 (liftMeasure
    period) :=
    fun j w => postcomp_word_memLp period (le_refl j) (velocityMap L) f hf (fun r _ a => hfL r a) w
  have heq : weightedCommutatorNorm period hs N hN ρ L hL u v =
      ∑ n ∈ Finset.range (N+1), weight ρ n*transportCommutatorNorm period n b g := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    exact externalCommutator_sumNorm period hs n.val w (by have := n.isLt; omega) L hL u v f g hu
      hv hf hg
  rw [heq, weightedNorm_eq_classical period 6 N (by omega) ρ u f hu hf,
    weightedLoss_eq_classical period 6 N (by omega) ρ v g hv hg]
  have ht := transportCommutator_weighted_bound period N ρ hρ b g hb hg hbL hgL
  have hbnd : (∑ n ∈ Finset.range (N+1), weight ρ n*wordSobolevNorm period 6 n b) ≤
      4 * ∑ n ∈ Finset.range (N+1), weight ρ n*wordSobolevNorm period 6 n f := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ =>
      (mul_le_mul_of_nonneg_left (velocityMap_word_bound period 6 n L hL f hf hfL) (weight_pos hρ
        n).le).trans_eq (by ring)
  have hz : 0 ≤ ∑ n ∈ Finset.range (N+1), (n : ℝ)*weight ρ n*wordSobolevNorm period 6 n g :=
    Finset.sum_nonneg fun n _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (weight_pos hρ n).le)
      (wordSobolevNorm_nonneg period 6 n g)
  have hcoef : 0 ≤ productConstant period 3*ρ⁻¹ := mul_nonneg (productConstant_nonneg period 3)
    (inv_nonneg.mpr hρ.le)
  exact ht.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbnd hcoef) hz).trans_eq
    (by ring))

/-- The genuine finite-Sobolev external transport commutator has the cutoff-independent radius-loss bound.
One additional derivative is used only to define the individual terms; it does not occur in the
  bound. -/
theorem weightedCommutator_bound {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N+6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) :
    weightedCommutatorNorm period hs N hN ρ L hL u v ≤
      (4*productConstant period 3)*ρ⁻¹*weightedNorm period 6 N ρ u*weightedLoss period 6 N ρ v := by
  let U : ℕ → SobolevSpace period (s+1) := fun n => restrictOperator period (by omega : s+1 ≤
    s+1+3) (smoothApprox period (s+1) n u)
  let V : ℕ → SobolevSpace period (s+1) := fun n => restrictOperator period (by omega : s+1 ≤
    s+1+3) (smoothApprox period (s+1) n v)
  have hU : Filter.Tendsto U Filter.atTop (𝓝 u) := smoothApprox_tendsto period u
  have hV : Filter.Tendsto V Filter.atTop (𝓝 v) := smoothApprox_tendsto period v
  have hpairs : Filter.Tendsto (fun n => (U n,V n)) Filter.atTop (𝓝 (u,v)) := hU.prodMk_nhds hV
  have hC : Filter.Tendsto
      (fun p : SobolevSpace period (s+1) × SobolevSpace period (s+1) => weightedCommutatorNorm
        period hs N hN ρ L hL p.1 p.2)
      (𝓝 (u,v)) (𝓝 (weightedCommutatorNorm period hs N hN ρ L hL u v)) :=
    (continuous_weightedCommutatorNorm period hs N hN ρ L hL).tendsto (u,v)
  have hleft := hC.comp hpairs
  have hW : Continuous (weightedNorm period (s := s+1) 6 N ρ) := continuous_weighted_blockNorm
    period N (by omega) ρ
  have hY : Continuous (weightedLoss period (s := s+1) 6 N ρ) := continuous_weightedLoss period 6 N
    (by omega) ρ
  have hright : Filter.Tendsto (fun n => (4*productConstant period 3)*ρ⁻¹*weightedNorm period 6 N ρ
    (U n)*weightedLoss period 6 N ρ (V n))
      Filter.atTop (𝓝 ((4*productConstant period 3)*ρ⁻¹*weightedNorm period 6 N ρ u*weightedLoss
        period 6 N ρ v)) :=
    ((hW.tendsto u |>.comp hU).const_mul ((4*productConstant period 3)*ρ⁻¹)).mul (hY.tendsto v
      |>.comp hV)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨f,hf,hfs,hfL⟩ := smoothApprox_representative_all period n u
  obtain ⟨g,hg,hgs,hgL⟩ := smoothApprox_representative_all period n v
  exact weightedCommutator_smooth_bound period hs N hN ρ hρ L hL (U n) (V n) f g hf hg hfs hgs hfL
    hgL

end EulerSobolevTransportCommutator
