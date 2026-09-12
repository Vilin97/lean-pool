/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EnergyMetricPaths
public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricEstimate
import Mathlib.Algebra.Order.Star.Real
import LeanPool.NavierStokesAndEuler.Euler.EnergyWordCoordinates
import LeanPool.NavierStokesAndEuler.ForMathlib.FiniteSum
import LeanPool.NavierStokesAndEuler.Euler.GevreyDifferentiatedEquation
import LeanPool.NavierStokesAndEuler.Euler.GevreyRestriction
import LeanPool.NavierStokesAndEuler.Euler.MetricPathConvergence
public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionLocal
import LeanPool.NavierStokesAndEuler.Euler.DivergenceFreeHeat
public import LeanPool.NavierStokesAndEuler.Euler.QuadraticHeatLocal
import LeanPool.NavierStokesAndEuler.Euler.QuadraticMildPasting
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyData
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
import LeanPool.NavierStokesAndEuler.Euler.CorrectionFamilyCompactness
import LeanPool.NavierStokesAndEuler.Euler.GevreyStabilityBudget

/-! Related estimates used together by the same construction modules. -/

section

/-! A genuine metric Gevrey bound supplies the uniform Banach norm used in actual continuation. -/

section

/-! Actual complete-Sobolev control from a positive-radius finite Gevrey bound, for parabolic
continuation. -/

@[expose] public section

noncomputable section

namespace EulerGevreyContinuationNorm

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
    EulerSpatialSobolevInverse
  EulerJetProductBounds EulerH6Pressure EulerSobolevGevreyOperators EulerPacketWeights
      EulerGevreyMetricEstimate

/-- At every retained derivative order, the Gevrey weight is bounded below by one positive
fixed-cutoff weight. -/
theorem weight_lower (ρ δ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hδ1 : δ ≤ 1)
    (n N : ℕ) (hn : n ≤ N) : weight δ N ≤ weight ρ n := by
  have hρ : 0 ≤ ρ := hδ.le.trans hδρ
  have hp : δ^N ≤ ρ^n := (pow_le_pow_of_le_one hδ.le hδ1 hn).trans (pow_le_pow_left₀ hδ.le hδρ n)
  have hf : (n.factorial : ℝ) ≤ (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hn
  have hsq : (n.factorial : ℝ)^2 ≤ (N.factorial : ℝ)^2 := by
    nlinarith [show (0 : ℝ) ≤ (n.factorial : ℝ) from Nat.cast_nonneg _]
  exact div_le_div₀ (pow_nonneg hρ n) hp (by positivity) hsq

variable (period : ℝ) [Fact (0 < period)]

/-- Each actual derivative coordinate is bounded by its genuine homogeneous derivative-sum norm. -/
theorem word_le_level {s : ℕ} (u : SobolevSpace period s) (w : SobolevWord s) :
    ‖u.val w‖ ≤ levelNorm period (toJet period u) w.1.val := by
  rw [levelNorm_eq_words]
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin w.1.val → Fin 4)))
    (fun v _ => norm_nonneg ((toJet period u).word v)) (Finset.mem_univ w.2)
  rw [toJet_word period u (by have := w.1.isLt; omega) w.2] at h
  exact h

/-- Every derivative coordinate through the full energy order is contained in one retained
external/base block. -/
theorem level_le_block {s : ℕ} (u : SobolevSpace period s) (N m : ℕ) (hm : m ≤ N + 6) :
    levelNorm period (toJet period u) m ≤ blockNorm period (toJet period u) 6 (min m N) := by
  let n := min m N
  have hn : n ≤ m := Nat.min_le_left m N
  have hr : m-n ≤ 6 := by dsimp [n]; omega
  have he : n+(m-n) = m := Nat.add_sub_of_le hn
  have h := Finset.single_le_sum (s := Finset.range 7)
    (fun r _ => (levelNorm_nonneg (toJet period u) : 0 ≤ levelNorm period (toJet period u) (n+r)))
    (show m-n ∈ Finset.range 7 by exact Finset.mem_range.mpr (by omega))
  rw [he] at h
  exact h

/-- A finite actual Gevrey bound controls the complete energy-order Sobolev norm on every
positive-radius interval. -/
theorem norm_le_weighted {s : ℕ} (N : ℕ) (hS : s ≤ N + 6) (ρ δ : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hδ1 : δ ≤ 1) (u : SobolevSpace period s) :
    ‖u‖ ≤ weightedNorm period 6 N ρ u / weight δ N := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hw : 0 < weight δ N := weight_pos hδ N
  change ‖u.val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (weightedNorm_nonneg period 6 N ρ hρ u) hw.le)).mpr
  intro w
  have hm : w.1.val ≤ N+6 := (Nat.le_of_lt_succ w.1.isLt).trans hS
  let n := min w.1.val N
  have hn : n ≤ N := Nat.min_le_right w.1.val N
  have hc := (word_le_level period u w).trans (level_le_block period u N w.1.val hm)
  have hh := Finset.single_le_sum (s := Finset.range (N+1))
    (fun i _ => mul_nonneg (weight_pos hρ i).le (show 0 ≤ blockNorm period (toJet period u) 6 i
        from blockNorm_nonneg _))
    (show n ∈ Finset.range (N+1) by exact Finset.mem_range.mpr (by omega))
  have hle : weight δ N*‖u.val w‖ ≤ weightedNorm period 6 N ρ u := by
    calc
      _ ≤ weight ρ n*‖u.val w‖ := mul_le_mul_of_nonneg_right (weight_lower ρ δ hδ hδρ hδ1 n N hn)
          (norm_nonneg _)
      _ ≤ weight ρ n*blockNorm period (toJet period u) 6 n := mul_le_mul_of_nonneg_left hc
          (weight_pos hρ n).le
      _ ≤ _ := hh
  exact (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using hle)

/-- A metric Gevrey bound gives the actual finite-Sobolev state bound needed by the uniform local
restart theorem. -/
theorem norm_le_metric {s : ℕ} (N : ℕ) (hN : N + 6 ≤ s) (hS : s ≤ N + 6) (ρ δ : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hδ1 : δ ≤ 1)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) (c : ℝ) (hc : 0 < c)
    (hK : ∀ v, c ^ 2 * ‖v‖ ^ 2 ≤ inner ℝ (K v) v) :
    ‖u‖ ≤ metricAmplification c*energyNorm period N hN ρ K u / weight δ N := by
  exact (norm_le_weighted period N hS ρ δ hδ hδρ hδ1 u).trans
    (div_le_div_of_nonneg_right (weightedNorm_le_energy period N hN ρ (hδ.trans_le hδρ) K u c hc
        hK) (weight_pos hδ N).le)

end EulerGevreyContinuationNorm

end
end

end

@[expose] public section

noncomputable section

namespace EulerGevreyPathNorm

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGevreyMetricEstimate
  EulerGevreyContinuationNorm EulerEnergyMetricPaths EulerPacketWeights
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A uniform metric-energy bound controls the actual continuous Sobolev path norm. -/
theorem norm_le_of_energy_bound {q : ℕ} (N : ℕ) (hN : N + 6 ≤ q + 1) (hS : q + 1 ≤ N + 6)
    (T : ℝ) (R : C(Icc (0 : ℝ) T, ℝ))
    (K : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (c δ E : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hE : 0 ≤ E)
    (hR : ∀ t, δ ≤ R t) (hK : ∀ t v, c ^ 2 * ‖v‖ ^ 2 ≤ inner ℝ (K t v) v)
    (he : ∀ t, energyPath period N hN T R K e t ≤ E) :
    ‖e‖ ≤ metricAmplification c*E/weight δ N := by
  have ha : 0 ≤ metricAmplification c := (by
      norm_num : (0 : ℝ) ≤ 1).trans (metricAmplification_one_le hc)
  have hw := weight_pos hδ N
  apply (ContinuousMap.norm_le e (div_nonneg (mul_nonneg ha hE) hw.le)).mpr
  intro t
  have h := norm_le_metric period N hN hS (R t) δ hδ (hR t) hδ1 (K t) (e t) c hc (hK t)
  have he' : energyNorm period N hN (R t) (K t) (e t) ≤ E := by
    simpa only [energyPath_apply] using he t
  exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he' ha) hw.le)

end EulerGevreyPathNorm

end
end

end

section

/-! Quantitative finite Gevrey bounds survive the actual strong time-path limit. -/

section

/-! The actual finite Gevrey metric energy passes to strong Sobolev limits. -/

@[expose] public section

noncomputable section

namespace EulerGevreyEnergyLimit

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGevreyMetricComparison
  EulerGevreyDifferentiatedEquation EulerGevreyMetricEstimate EulerGevreyRestriction
  EulerMetricPathConvergence EulerWeightedCylinderEnergy EulerFiniteMetricEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual energy coordinates depend continuously on the Sobolev field. -/
theorem energyValues_continuous {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) :
    Continuous (energyValues period q N hN) := by
  apply continuous_pi
  intro I
  apply continuous_pi
  intro a
  exact (energyWordOperator period q N hN I a).continuous.congr
    (fun u => energyWordOperator_apply period q N hN I a u)

/-- The actual finite Gevrey metric energy is continuous in its Sobolev field, including zero
energy. -/
theorem energyNorm_continuous {s : ℕ} (N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) :
    Continuous (energyNorm period N hN ρ K) := by
  unfold energyNorm weightedMetricSum
  apply continuous_finsetSum
  intro I _
  apply Continuous.const_mul
  exact familyMetricNorm_continuous.comp
    (continuous_const.prodMk ((continuous_apply I).comp (energyValues_continuous period 6 N hN)))

/-- Restriction preserving the derivative cutoff leaves the actual Gevrey energy unchanged. -/
theorem energyNorm_restrict {p q : ℕ} (hqp : q ≤ p) (N : ℕ) (hN : N + 6 ≤ q) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period p) :
    energyNorm period N hN ρ K (restrictOperator period hqp u) =
      energyNorm period N (hN.trans hqp) ρ K u := by
  unfold energyNorm
  rw [energyValues_restrict]

/-- A genuine strong lower-order limit retains every finite metric-energy bound whose derivative
cutoff is retained. -/
theorem energyNorm_limit_bound {p q : ℕ} (hqp : q ≤ p) (N : ℕ) (hN : N + 6 ≤ q) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : ℕ → SobolevSpace period p) (e : SobolevSpace
        period q)
    (h : Filter.Tendsto (fun n => restrictOperator period hqp (u n)) Filter.atTop (𝓝 e))
    (M : ℝ) (hb : ∀ n, energyNorm period N (hN.trans hqp) ρ K (u n) ≤ M) :
    energyNorm period N hN ρ K e ≤ M := by
  apply le_of_tendsto ((energyNorm_continuous period N hN ρ K).continuousAt.tendsto.comp h)
  exact Filter.Eventually.of_forall (fun n => by
    change energyNorm period N hN ρ K (restrictOperator period hqp (u n)) ≤ M
    rw [energyNorm_restrict]
    exact hb n)

end EulerGevreyEnergyLimit

end
end

end

section

/-! Monotonicity of the actual finite Gevrey metric energy in the external cutoff. -/

@[expose] public section

noncomputable section

namespace EulerGevreyEnergyCutoff

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGevreyMetricComparison
  EulerGevreyMetricEstimate  EulerEnergyWordCoordinates
  EulerWeightedCylinderEnergy EulerFiniteMetricEnergy EulerPacketWeights EulerBaseWordMetric

/-- The literal inclusion of external words into a larger cutoff. -/
def externalWordInclusion {N M : ℕ} (hNM : N ≤ M) (I : ExternalWord N) : ExternalWord M :=
  ⟨Fin.castLE (Nat.succ_le_succ hNM) I.1,I.2⟩

/-- Increasing the cutoff does not identify distinct derivative words. -/
theorem externalWordInclusion_injective {N M : ℕ} (hNM : N ≤ M) :
    Function.Injective (externalWordInclusion hNM) := by
  intro I J h
  obtain ⟨i,w⟩ := I
  obtain ⟨j,v⟩ := J
  have h1 := congrArg Sigma.fst h
  have hij : i=j := Fin.castLE_injective (Nat.succ_le_succ hNM) h1
  subst j
  have hw : w=v := by
    have hh := (Sigma.mk.inj h).2
    exact eq_of_heq hh
  subst v
  rfl

variable (period : ℝ) [Fact (0 < period)]

/-- The retained energy coordinates are identical in a larger cutoff. -/
theorem energyValues_inclusion {s N M q : ℕ} (hNM : N ≤ M) (hM : M + q ≤ s)
    (u : SobolevSpace period s) (I : ExternalWord N) :
    energyValues period q M hM u (externalWordInclusion hNM I) =
      energyValues period q N (by omega) u I := by
  funext a
  rw [energyValues_eq_word,energyValues_eq_word]
  rfl

/-- The literal finite Gevrey metric energy increases with its external derivative cutoff. -/
theorem energyNorm_cutoff_mono {s N M : ℕ} (hNM : N ≤ M) (hM : M + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) :
    energyNorm period N (by omega) ρ K u ≤ energyNorm period M hM ρ K u := by
  unfold energyNorm weightedMetricSum
  apply NavierStokesAndEuler.sum_le_sum_of_injOn (externalWordInclusion hNM)
    (externalWordInclusion_injective hNM).injOn (Finset.subset_univ _)
  · intro I _
    rw [energyValues_inclusion]
    exact le_refl _
  · intro I _ _
    exact mul_nonneg (weight_pos hρ I.1.val).le (Real.sqrt_nonneg _)

end EulerGevreyEnergyCutoff

end
end

end

@[expose] public section

noncomputable section

namespace EulerGevreyEnergyPathLimit

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGevreyMetricEstimate
  EulerGevreyEnergyLimit EulerGevreyEnergyCutoff
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every retained Gevrey cutoff of the actual strong path limit keeps the genuine uniform
approximation bound. -/
theorem energyNorm_path_limit_bound {p q N : ℕ} (hqp : q ≤ p) (hN : N + 6 ≤ p) (T : ℝ)
    (ρ : Icc (0 : ℝ) T → ℝ) (hρ : ∀ t, 0 < ρ t)
    (K : Icc (0 : ℝ) T → LiftL2 period →L[ℝ] LiftL2 period)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period p))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (hconv : Filter.Tendsto (fun n => (restrictOperator period hqp).compLeftContinuous ℝ (Icc (0 :
        ℝ) T) (u n))
      Filter.atTop (𝓝 e))
    (B : Icc (0 : ℝ) T → ℝ)
    (hb : ∀ n t, energyNorm period N hN (ρ t) (K t) (u n t) ≤ B t)
    (P : ℕ) (hPN : P ≤ N) (hP : P + 6 ≤ q) :
    ∀ t, energyNorm period P hP (ρ t) (K t) (e t) ≤ B t := by
  intro t
  have ht := (ContinuousMap.evalCLM ℝ t).continuous.tendsto e |>.comp hconv
  apply energyNorm_limit_bound period hqp P hP (ρ t) (K t) (fun n => u n t) (e t) ht (B t)
  intro n
  exact (energyNorm_cutoff_mono period hPN hN (ρ t) (hρ t) (K t) (u n t)).trans (hb n t)

end EulerGevreyEnergyPathLimit

end
end

end

section

/-! Actual divergence-free continuation of the concrete viscous correction equation. -/

section

/-! Genuine finite-time continuation of actual viscous mild solutions from an a priori Sobolev
bound. -/

@[expose] public section

noncomputable section

namespace EulerBoundedMildContinuation

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerVolterraConvolution
  EulerUniformHeatLocal EulerQuadraticSource EulerTimePathGluing EulerQuadraticMildPasting
open scoped Topology

/-- The next actual time window ends at the smaller of one full step and the terminal time. -/
theorem advance_time_eq (a δ S : ℝ) : a+min δ (S-a) = min (a+δ) S := by
  by_cases h : δ ≤ S-a
  · rw [min_eq_left h, min_eq_left (by linarith : a+δ ≤ S)]
  · rw [min_eq_right (le_of_not_ge h), min_eq_right (by linarith : S ≤ a+δ)]
    ring

/-- Repeated genuine local windows reach each successive point of a fixed finite time grid. -/
theorem advance_grid (S δ a : ℝ) (hδ : 0 ≤ δ) (n : ℕ)
    (hgrid : min ((n : ℝ) * δ) S ≤ a) :
    min (((n+1 : ℕ) : ℝ)*δ) S ≤ a+min δ (S-a) := by
  rw [advance_time_eq]
  apply le_min
  · by_cases hn : (n : ℝ)*δ ≤ S
    · have hna : (n : ℝ)*δ ≤ a := by simpa only [min_eq_left hn] using hgrid
      apply (min_le_left _ _).trans
      push_cast
      nlinarith only [hna]
    · have hSa : S ≤ a := by simpa only [min_eq_right (le_of_not_ge hn)] using hgrid
      exact (min_le_right _ _).trans (by linarith)
  · exact min_le_right _ _

variable (period : ℝ) [Fact (0 < period)]

/-- An actual uniform Sobolev bound on partial solutions yields a genuine solution on the whole
prescribed interval.
The continuation is constructed by finitely many actual local heat solves and exact nonlinear
pasting. -/
theorem exists_global_mild_of_bound (q : ℕ) (ν : ℝ) (hν : 0 < ν) (S : ℝ) (hS : 0 < S)
    (R : ℝ) (hR : 0 ≤ R) (u₀ : SobolevSpace period (q + 1)) (hu₀ : ‖u₀‖ ≤ R)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q + 1)) (SobolevSpace period q))
    (hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
      (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))),
      (∀ t, u t = quadraticDuhamel period ν hν hT hTS C u₀ u t) → ‖u‖ ≤ R) :
    ∃ u : C(Icc (0 : ℝ) S, SobolevSpace period (q+1)),
      ‖u‖ ≤ R ∧ u ⟨0,le_rfl,hS.le⟩ = u₀ ∧
        ∀ t, u t = quadraticDuhamel period ν hν hS.le le_rfl C u₀ u t := by
  obtain ⟨δ,hδ,_,hlocal⟩ := exists_uniform_restart_time period q ν hν S hS R hR C
  have hind : ∀ n : ℕ, ∃ (a : ℝ) (ha : 0 ≤ a) (haS : a ≤ S),
      min ((n : ℝ)*δ) S ≤ a ∧
      ∃ u : C(Icc (0 : ℝ) a, SobolevSpace period (q+1)),
        ∀ t, u t = quadraticDuhamel period ν hν ha haS C u₀ u t := by
    intro n
    induction n with
    | zero =>
      obtain ⟨u,_,_,hsol⟩ := hlocal 0 0 le_rfl le_rfl (by linarith) hδ.le u₀ hu₀
      refine ⟨0,le_rfl,hS.le,?_,u,?_⟩
      · simpa only [Nat.cast_zero,zero_mul] using min_le_left (0 : ℝ) S
      · apply (quadratic_mild_window_iff period ν hν le_rfl hS.le C u₀ u).mpr
        exact hsol
    | succ n ih =>
      obtain ⟨a,ha,haS,hgrid,u,hsolu⟩ := ih
      let b := min δ (S-a)
      have hb : 0 ≤ b := le_min hδ.le (sub_nonneg.mpr haS)
      have hbδ : b ≤ δ := min_le_left _ _
      have habS : a+b ≤ S := by have h := min_le_right δ (S-a); dsimp [b]; linarith
      have hu : ‖u ⟨a,ha,le_rfl⟩‖ ≤ R :=
        (u.norm_coe_le_norm _).trans (hbound a ha haS u hsolu)
      obtain ⟨v,_,hv0,hsolv⟩ := hlocal a b ha hb habS hbδ (u ⟨a,ha,le_rfl⟩) hu
      let w := gluePath a b ha hb u v hv0.symm
      have hw := glue_quadratic_mild period ν hν C a b ha hb haS habS u v hv0.symm u₀ hsolu hsolv
      exact ⟨a+b,add_nonneg ha hb,habS,advance_grid S δ a hδ.le n hgrid,w,hw⟩
  obtain ⟨n,hn⟩ := exists_nat_ge (S/δ)
  have hN : S ≤ (n : ℝ)*δ := (div_le_iff₀ hδ).mp hn
  obtain ⟨a,ha,haS,hgrid,u,hsol⟩ := hind n
  have hSa : S ≤ a := by simpa only [min_eq_right hN] using hgrid
  have he : a = S := le_antisymm haS hSa
  subst a
  refine ⟨u,hbound S ha haS u hsol,?_,hsol⟩
  have hz := hsol ⟨0,le_rfl,hS.le⟩
  simpa only [quadraticDuhamel, mul_zero, Real.toNNReal_zero, heatOperator_zero,
      intervalIntegral.integral_same, add_zero] using hz

end EulerBoundedMildContinuation

end
end

end

@[expose] public section

noncomputable section

namespace EulerCorrectionContinuation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerQuadraticSource EulerDivergenceFreeHeat EulerBoundedMildContinuation
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every actual partial zero-initial correction solution preserves the lifted divergence
constraint. -/
theorem correction_mild_divergenceFree {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) (hν : 0 < ν)
    {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : CorrectionData period q (Icc (0 : ℝ) S))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t, e t = quadraticDuhamel period ν hν hT hTS (D.coefficients period hq) 0 e t) :
    ∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction := by
  let F := ((D.coefficients period hq).comp (timeInclusion hTS)).apply
  have hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q+1) => F p.1 p.2) :=
    ((D.coefficients period hq).comp (timeInclusion hTS)).continuous
  have hz := mild_solution_preserves_gradient_zero period D.κ D.direction ν hν T hT 0
    (map_zero _) F hF (fun t u => D.source_gradient_zero period hq (timeInclusion hTS t) u) e hsol
  intro t
  exact (gradientEvaluation_zero_iff period D.κ D.direction (e t)).mp (hz t)

/-- A genuine a-priori Sobolev bound continues the actual zero-initial viscous Euler correction
across the prescribed interval. -/
theorem exists_global_correction_of_bound {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (S : ℝ) (hS : 0 < S) (R : ℝ) (hR : 0 ≤ R)
    (D : CorrectionData period q (Icc (0 : ℝ) S))
    (hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
      (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))),
      (∀ t, e t = quadraticDuhamel period ν hν hT hTS (D.coefficients period hq) 0 e t) → ‖e‖ ≤ R) :
    ∃ e : C(Icc (0 : ℝ) S, SobolevSpace period (q+1)),
      ‖e‖ ≤ R ∧ e ⟨0,le_rfl,hS.le⟩ = 0 ∧
      (∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
      ∀ t, e t = quadraticDuhamel period ν hν hS.le le_rfl (D.coefficients period hq) 0 e t := by
  obtain ⟨e,he,hi,hsol⟩ := exists_global_mild_of_bound period q ν hν S hS R hR 0
    (by simpa only [norm_zero] using hR) (D.coefficients period hq) hbound
  exact ⟨e,he,hi,correction_mild_divergenceFree period hq ν hν hS.le le_rfl D e hsol,hsol⟩

end EulerCorrectionContinuation

end
end

end

section

/-! Applying the concrete Gevrey budgets to a genuinely bounded viscous correction family. -/

@[expose] public section

noncomputable section

namespace EulerGevreyFamilyCompactness

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionEnergyData EulerQuadraticSource EulerGevreyStabilityBudget
      EulerCorrectionFamilyCompactness
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Concrete Gevrey and inverse-metric budgets turn a genuinely bounded correction family into its
actual strong lower-order limit. -/
theorem exists_limit_of_gevrey_family {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hGq : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hLq : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQq : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (N : ℕ) (R : C(Icc (0 : ℝ) T, ℝ))
    (B : SpatialBudget period (by omega : 6 ≤ q + 1) D N R) (K : MetricBudget period T hT D)
    (ν : ℕ → ℝ) (hν : ∀ n, 0 < ν n) (hν1 : ∀ n, ν n ≤ 1) (hνc : CauchySeq ν)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (M : ℝ)
    (huM : ∀ n, ‖u n‖ ≤ M) (hu0 : ∀ n, u n ⟨0, le_rfl, hT⟩ = 0)
    (hu : ∀ n t, u n t = quadraticDuhamel period (ν n) (hν n) hT le_rfl
      ((lowerData period D KG KL KQ hGq hLq hQq).coefficients period hq) 0 (u n) t)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : ∀ n t, value period (u n t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∃ e : C(Icc (0 : ℝ) T,SobolevSpace period q),
      Filter.Tendsto (fun n => (truncateOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u
          n))
        Filter.atTop (𝓝 e) ∧
      e ⟨0,le_rfl,hT⟩=0 ∧ (∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
          ‖e‖ ≤ M := by
  let Dlow := lowerData period D KG KL KQ hGq hLq hQq
  let Bstable := stabilityBudgetLower period hT D KG KL KQ hGq hLq hQq N R (by omega) B K
  have hcz : ∀ t, value period (Dlow.approximation t) ∈ divergenceFreeSpace period Dlow.κ
      Dlow.direction := by
    intro t
    exact hz t
  exact exists_correction_family_limit period hq T hT Dlow Bstable ν hν hν1 hνc u M huM hu0 hu hcz
      hud

end EulerGevreyFamilyCompactness

end
end

end
