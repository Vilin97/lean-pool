/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FunctionalVelocity
public import LeanPool.NavierStokesAndEuler.Euler.SobolevGevreyOperators
import LeanPool.NavierStokesAndEuler.Euler.Foundations.RealCylinder
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SobolevDerivativeNorm
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet

/-! Genuine finite-Sobolev norms of the small four-component transport drift. -/

@[expose] public section


noncomputable section

namespace EulerSobolevDriftNorm

open MeasureTheory Filter EulerSobolev EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSpatialSobolevInverse EulerMetricTransport EulerH6Pressure
  EulerH6Nonlinear EulerJetProductBounds EulerSobolevGevreyOperators
  EulerFunctionalVelocity EulerStrongSmoothJet EulerVectorCylinder EulerRealCylinder
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Postcomposition of an actual derivative coordinate with the fixed drift map. -/
def driftWordOperator {s : ℕ} (L : Vector3 →L[ℝ] Domain 4) (w : SobolevWord s) :
    SobolevSpace period s →L[ℝ] Lp (Domain 4) 2 (liftMeasure period) :=
  (L.compLpL 2 (liftMeasure period)).comp (wordOperator period w)

/-- The exact sum of L² norms of drift derivatives at one total derivative order. -/
def driftLevelNorm {s : ℕ} (n : ℕ) (L : Vector3 →L[ℝ] Domain 4)
    (u : SobolevSpace period s) : ℝ :=
  ∑ w : Fin n → Fin 4, ‖L.compLpL 2 (liftMeasure period) ((toJet period u).word w)‖

/-- The drift norm at one external order, including all derivatives in the fixed base Sobolev block.
-/
def driftBlockNorm {s : ℕ} (q n : ℕ) (L : Vector3 →L[ℝ] Domain 4)
    (u : SobolevSpace period s) : ℝ :=
  ∑ r ∈ Finset.range (q+1), driftLevelNorm period (n+r) L u

/-- The weighted genuine drift norm, retaining cancellations in the fixed velocity map. -/
def weightedDriftNorm {s : ℕ} (q N : ℕ) (ρ : ℝ) (L : Vector3 →L[ℝ] Domain 4)
    (u : SobolevSpace period s) : ℝ :=
  ∑ n ∈ Finset.range (N+1), EulerPacketWeights.weight ρ n * driftBlockNorm period q n L u

theorem driftWordOperator_eq {s n : ℕ} (hn : n ≤ s) (L : Vector3 →L[ℝ] Domain 4)
    (w : Fin n → Fin 4) (u : SobolevSpace period s) :
    L.compLpL 2 (liftMeasure period) ((toJet period u).word w) =
      driftWordOperator period L ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩ u := by
  rw [toJet_word period u hn]
  rfl

theorem driftLevelNorm_nonneg {s : ℕ} (n : ℕ) (L : Vector3 →L[ℝ] Domain 4)
    (u : SobolevSpace period s) : 0 ≤ driftLevelNorm period n L u :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem driftBlockNorm_nonneg {s : ℕ} (q n : ℕ) (L : Vector3 →L[ℝ] Domain 4)
    (u : SobolevSpace period s) : 0 ≤ driftBlockNorm period q n L u :=
  Finset.sum_nonneg fun _ _ => driftLevelNorm_nonneg period _ L u

theorem weightedDriftNorm_nonneg {s : ℕ} (q N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (L : Vector3 →L[ℝ] Domain 4) (u : SobolevSpace period s) :
    0 ≤ weightedDriftNorm period q N ρ L u :=
  Finset.sum_nonneg fun n _ => mul_nonneg (EulerPacketWeights.weight_pos hρ n).le
    (driftBlockNorm_nonneg period q n L u)

/-- Valid drift coordinates are continuous on the complete finite Sobolev space. -/
theorem continuous_driftLevelNorm {s n : ℕ} (hn : n ≤ s) (L : Vector3 →L[ℝ] Domain 4) :
    Continuous (driftLevelNorm period (s := s) n L) := by
  unfold driftLevelNorm
  apply continuous_finsetSum
  intro w _
  simp_rw [driftWordOperator_eq period hn]
  exact (driftWordOperator period L ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩).continuous.norm

theorem continuous_driftBlockNorm {s q n : ℕ} (h : n + q ≤ s) (L : Vector3 →L[ℝ] Domain 4) :
    Continuous (driftBlockNorm period (s := s) q n L) := by
  apply continuous_finsetSum
  intro r hr
  exact continuous_driftLevelNorm period (by have := Finset.mem_range.mp hr; omega) L

/-- Joint continuity in radius and field follows directly from finite sums of continuous linear
coordinates. -/
theorem continuous_weightedDriftNorm_pair {s : ℕ} (q N : ℕ) (hN : N + q ≤ s)
    (L : Vector3 →L[ℝ] Domain 4) :
    Continuous (fun p : ℝ × SobolevSpace period s => weightedDriftNorm period q N p.1 L p.2) := by
  apply continuous_finsetSum
  intro n hn
  have hw : Continuous (fun p : ℝ × SobolevSpace period s => EulerPacketWeights.weight p.1 n) := by
    unfold EulerPacketWeights.weight
    fun_prop
  exact hw.mul ((continuous_driftBlockNorm period
    (by have := Finset.mem_range.mp hn; omega : n+q ≤ s) L).comp continuous_snd)

theorem continuous_weightedDriftNorm {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ)
    (L : Vector3 →L[ℝ] Domain 4) : Continuous (weightedDriftNorm period (s := s) q N ρ L) :=
  (continuous_weightedDriftNorm_pair period q N hN L).comp (continuous_const.prodMk continuous_id)

/-- The drift norm is subadditive without discarding its directional cancellations. -/
theorem driftLevelNorm_add_le {s n : ℕ} (hn : n ≤ s) (L : Vector3 →L[ℝ] Domain 4)
    (u v : SobolevSpace period s) :
    driftLevelNorm period n L (u+v) ≤ driftLevelNorm period n L u + driftLevelNorm period n L v :=
        by
  unfold driftLevelNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  simp_rw [driftWordOperator_eq period hn]
  rw [map_add]
  exact norm_add_le _ _

theorem weightedDriftNorm_add_le {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (L : Vector3 →L[ℝ] Domain 4) (u v : SobolevSpace period s) :
    weightedDriftNorm period q N ρ L (u+v) ≤
      weightedDriftNorm period q N ρ L u + weightedDriftNorm period q N ρ L v := by
  unfold weightedDriftNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (EulerPacketWeights.weight_pos hρ n).le
  unfold driftBlockNorm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun r hr => driftLevelNorm_add_le period
    (by have := Finset.mem_range.mp hn; have := Finset.mem_range.mp hr; omega) L u v

/-- The coarse comparison is used for the correction field, not for the prescribed drift. -/
theorem driftLevelNorm_le {s : ℕ} (n : ℕ) (L : Vector3 →L[ℝ] Domain 4)
    (u : SobolevSpace period s) :
    driftLevelNorm period n L u ≤ ‖L‖ * levelNorm period (toJet period u) n := by
  rw [levelNorm_eq_words, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ =>
    ((L.compLpL 2 (liftMeasure period)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right L.norm_compLpL_le (norm_nonneg _))

theorem weightedDriftNorm_le_weightedNorm {s : ℕ} (q N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (L : Vector3 →L[ℝ] Domain 4) (u : SobolevSpace period s) :
    weightedDriftNorm period q N ρ L u ≤ ‖L‖ * weightedNorm period q N ρ u := by
  unfold weightedDriftNorm weightedNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have h : driftBlockNorm period q n L u ≤ ‖L‖ * blockNorm period (toJet period u) q n := by
    unfold driftBlockNorm blockNorm
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun r _ => driftLevelNorm_le period (n+r) L u
  exact (mul_le_mul_of_nonneg_left h (EulerPacketWeights.weight_pos hρ n).le).trans_eq (by ring)

omit [Fact (0 < period)] in
/-- Four contractive coordinate functionals assemble into a map of norm at most four. -/
theorem velocityMap_norm_le_four (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) :
    ‖velocityMap L‖ ≤ 4 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  calc
    ‖velocityMap L z‖ ≤ ∑ i : Fin 4, ‖velocityMap L z i‖ :=
        EulerSobolevDerivativeNorm.norm_le_sum_coordinates 4 _
    _ ≤ ∑ _i : Fin 4, ‖z‖ := Finset.sum_le_sum fun i _ =>
      ((L i).le_opNorm z).trans (by simpa using mul_le_mul_of_nonneg_right (hL i) (norm_nonneg z))
    _ = _ := by simp

theorem weightedDriftNorm_velocityMap_le {s : ℕ} (q N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (u : SobolevSpace period s) :
    weightedDriftNorm period q N ρ (velocityMap L) u ≤ 4 * weightedNorm period q N ρ u :=
  (weightedDriftNorm_le_weightedNorm period q N ρ hρ (velocityMap L) u).trans
    (mul_le_mul_of_nonneg_right (velocityMap_norm_le_four L hL) (weightedNorm_nonneg period q N ρ
        hρ u))

section Classical

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- External-word Sobolev blocks equal the sum over the corresponding total derivative orders. -/
theorem wordSobolevNorm_eq_total (q n : ℕ) (f : LiftDomain period → F) :
    wordSobolevNorm period q n f = ∑ r ∈ Finset.range (q+1),
      ∑ w : Fin (n+r) → Fin 4, (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure
          period)).toReal := by
  induction n generalizing f with
  | zero =>
    simp only [wordSobolevNorm_zero, liftSobolevNorm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Nat.zero_add]
  | succ n ih =>
    rw [wordSobolevNorm_succ]
    simp_rw [ih]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [show n+1+r = (n+r)+1 by omega, ← Fintype.sum_prod_type']
    symm
    exact Fintype.sum_equiv (EulerSpatialSobolevInverse.SpatialJet.wordSnocEquiv (n+r))
      (fun w => (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal)
      (fun v => (eLpNorm (iteratedFieldDerivative period v.2
        (EulerTransportDerivatives.fieldDerivative period (standardDirection v.1) f)) 2
            (liftMeasure period)).toReal)
      (fun w => by
        change (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal =
          (eLpNorm (iteratedFieldDerivative period (Fin.init w)
            (EulerTransportDerivatives.fieldDerivative period (standardDirection (w (Fin.last
                (n+r)))) f)) 2
              (liftMeasure period)).toReal
        rw [word_init_last period w f])

end Classical

/-- Each postcomposed strong word agrees almost everywhere with the actual classical drift
derivative. -/
theorem driftWord_ae {s n : ℕ} (hn : n ≤ s) (L : Vector3 →L[ℝ] Domain 4)
    (w : Fin n → Fin 4) (u : SobolevSpace period s) (f : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    (L.compLpL 2 (liftMeasure period) ((toJet period u).word w) : LiftDomain period → Domain 4)
      =ᵐ[liftMeasure period] iteratedFieldDerivative period w (L ∘ f) := by
  rw [iteratedFieldDerivative_postcomp period L w f hf]
  filter_upwards [L.coeFn_compLpL ((toJet period u).word w),
    jet_word_ae period hn (value period u) (toJet period u) w f hu hf] with x hx hy
  rw [hx, hy]
  rfl

theorem driftLevelNorm_eq_classical {s n : ℕ} (hn : n ≤ s) (L : Vector3 →L[ℝ] Domain 4)
    (u : SobolevSpace period s) (f : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    driftLevelNorm period n L u = ∑ w : Fin n → Fin 4,
      (eLpNorm (iteratedFieldDerivative period w (L ∘ f)) 2 (liftMeasure period)).toReal := by
  apply Finset.sum_congr rfl
  intro w _
  rw [Lp.norm_def]
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae (driftWord_ae period hn L w u f hu hf))

/-- The rough drift block is exactly the classical external-word Sobolev norm on every smooth
representative. -/
theorem driftBlockNorm_eq_classical {s q n : ℕ} (h : n + q ≤ s) (L : Vector3 →L[ℝ] Domain 4)
    (u : SobolevSpace period s) (f : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    driftBlockNorm period q n L u = wordSobolevNorm period q n (L ∘ f) := by
  rw [wordSobolevNorm_eq_total]
  apply Finset.sum_congr rfl
  intro r hr
  exact driftLevelNorm_eq_classical period (by have := Finset.mem_range.mp hr; omega) L u f hu hf

/-- Exact representative identity for the finite weighted drift norm. -/
theorem weightedDriftNorm_eq_classical {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ)
    (L : Vector3 →L[ℝ] Domain 4) (u : SobolevSpace period s) (f : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    weightedDriftNorm period q N ρ L u =
      ∑ n ∈ Finset.range (N+1), EulerPacketWeights.weight ρ n * wordSobolevNorm period q n (L ∘ f)
          := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [driftBlockNorm_eq_classical period (by have := Finset.mem_range.mp hn; omega) L u f hu hf]

/-- Restriction of the finite Sobolev ambient space preserves each retained drift coordinate. -/
theorem driftLevelNorm_restrict {s t n : ℕ} (h : t ≤ s) (hn : n ≤ t)
    (L : Vector3 →L[ℝ] Domain 4) (u : SobolevSpace period s) :
    driftLevelNorm period n L (restrictOperator period h u) = driftLevelNorm period n L u := by
  apply Finset.sum_congr rfl
  intro w _
  rw [toJet_word period (restrictOperator period h u) hn, toJet_word period u (hn.trans h)]
  rfl

theorem weightedDriftNorm_restrict {s t : ℕ} (h : t ≤ s) (q N : ℕ) (hN : N + q ≤ t)
    (ρ : ℝ) (L : Vector3 →L[ℝ] Domain 4) (u : SobolevSpace period s) :
    weightedDriftNorm period q N ρ L (restrictOperator period h u) = weightedDriftNorm period q N ρ
        L u := by
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  exact driftLevelNorm_restrict period h
    (by have := Finset.mem_range.mp hn; have := Finset.mem_range.mp hr; omega) L u

theorem weightedDriftNorm_truncate {s : ℕ} (q N : ℕ) (hN : N + q ≤ s)
    (ρ : ℝ) (L : Vector3 →L[ℝ] Domain 4) (u : SobolevSpace period (s + 1)) :
    weightedDriftNorm period q N ρ L (truncateOperator period s u) = weightedDriftNorm period q N ρ
        L u := by
  have he : truncateOperator period s u = restrictOperator period (Nat.le_succ s) u := by
    apply value_injective period
    rfl
  rw [he]
  exact weightedDriftNorm_restrict period (Nat.le_succ s) q N hN ρ L u

/-- Actual smooth approximations converge in the drift norm at every retained weighted cutoff. -/
theorem weightedDriftNorm_smoothApprox_tendsto {s : ℕ} (q N : ℕ) (hN : N + q ≤ s)
    (ρ : ℝ) (L : Vector3 →L[ℝ] Domain 4) (u : SobolevSpace period s) :
    Tendsto (fun n => weightedDriftNorm period q N ρ L
      (restrictOperator period (by omega : s ≤ s+3) (smoothApprox period s n u))) atTop
        (𝓝 (weightedDriftNorm period q N ρ L u)) :=
  ((continuous_weightedDriftNorm period q N hN ρ L).tendsto u).comp (smoothApprox_tendsto period u)

/-- A zero field has zero drift at every valid weighted cutoff. -/
theorem weightedDriftNorm_zero {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ)
    (L : Vector3 →L[ℝ] Domain 4) : weightedDriftNorm period q N ρ L (0 : SobolevSpace period s) = 0
        := by
  apply Finset.sum_eq_zero
  intro n hn
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro w _
  rw [driftWordOperator_eq period
    (by
        have := Finset.mem_range.mp hn; have := Finset.mem_range.mp hr; omega : n+r ≤ s), map_zero,
            norm_zero]

/-- Smoothing errors themselves tend to zero in the genuine drift norm. -/
theorem weightedDriftNorm_smoothApprox_sub_tendsto {s : ℕ} (q N : ℕ) (hN : N + q ≤ s)
    (ρ : ℝ) (L : Vector3 →L[ℝ] Domain 4) (u : SobolevSpace period s) :
    Tendsto (fun n => weightedDriftNorm period q N ρ L
      (restrictOperator period (by
          omega : s ≤ s+3) (smoothApprox period s n u) - u)) atTop (𝓝 0) := by
  have h := ((continuous_weightedDriftNorm period q N hN ρ L).tendsto (0 : SobolevSpace period
      s)).comp
    (by
        simpa only [sub_self] using (smoothApprox_tendsto period u).sub (tendsto_const_nhds (x :=
            u)))
  simpa only [Function.comp_def, weightedDriftNorm_zero period q N hN ρ L] using h

end EulerSobolevDriftNorm
