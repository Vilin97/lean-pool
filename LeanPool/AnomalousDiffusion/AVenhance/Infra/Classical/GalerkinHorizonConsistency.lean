/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothHorizon
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothCoefficients
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.LimitRegularity

/-! Finite Galerkin time-change identities for nested physical horizons. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance galerkinHorizonConsistencyMeasureSpaceUnitAddCircle :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance galerkinHorizonConsistencyMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance galerkinHorizonConsistencyProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance galerkinHorizonConsistencyProbabilityTorus :
    IsProbabilityMeasure (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.Classical

/-- Continuous linear Galerkin generator at a given time and frequency cutoff. -/
def GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM
    (φ : ℝ → Vec 2 → ℝ) (κ : ℝ) (K : ℕ) (t : ℝ) :
    Coefficients (RealFourierDimension K) →L[ℝ]
      Coefficients (RealFourierDimension K) :=
  matrixCoefficientCLM (fun i j => weakFormMatrixEntry
    (fun r x => AVenhance.Infra.Torus.periodicToTorus (AVenhance.streamVel φ r) x)
    κ (realFourierModeFin K) (realFourierModeGradFin K) t i j)

theorem GalerkinHorizonConsistency.classicalGalerkinWeakEntry_horizon_eq (H K : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (s : ℝ) (i j : Fin (RealFourierDimension K)) :
    weakFormMatrixEntry
        (fun r x => AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.streamVel (classicalGalerkinHorizonStream H φ) r) x)
        ((H : ℝ) * κ) (realFourierModeFin K) (realFourierModeGradFin K) s i j =
      (H : ℝ) * weakFormMatrixEntry
        (fun r x => AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.streamVel φ r) x)
        κ (realFourierModeFin K) (realFourierModeGradFin K) ((H : ℝ) * s) i j := by
  unfold weakFormMatrixEntry
  have hvel (x : Torus) :
      AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.streamVel (classicalGalerkinHorizonStream H φ) s) x =
        (H : ℝ) • AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.streamVel φ ((H : ℝ) * s)) x := by
    simpa [AVenhance.Infra.Torus.periodicToTorus] using
      classicalGalerkinHorizonStreamVel_eq H φ hφ s
        (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)
  have hpoint (x : Torus) :
      AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
          (AVenhance.Infra.Torus.periodicToTorus
            (AVenhance.streamVel (classicalGalerkinHorizonStream H φ) s) x)
          (realFourierModeGradFin K j x) * realFourierModeFin K i x =
        (H : ℝ) * (AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
          (AVenhance.Infra.Torus.periodicToTorus (AVenhance.streamVel φ ((H : ℝ) * s)) x)
          (realFourierModeGradFin K j x) * realFourierModeFin K i x) := by
    rw [hvel x]
    simp [AVenhance.Infra.Parabolic.FourierGalerkin.vecDot, Pi.smul_apply]
    ring
  have hdrift :
      (∫ x, AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
          (AVenhance.Infra.Torus.periodicToTorus
            (AVenhance.streamVel (classicalGalerkinHorizonStream H φ) s) x)
          (realFourierModeGradFin K j x) * realFourierModeFin K i x) =
        (H : ℝ) * ∫ x, AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
          (AVenhance.Infra.Torus.periodicToTorus
            (AVenhance.streamVel φ ((H : ℝ) * s)) x)
          (realFourierModeGradFin K j x) * realFourierModeFin K i x := by
    calc
      _ = ∫ x, (H : ℝ) * (AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
          (AVenhance.Infra.Torus.periodicToTorus
            (AVenhance.streamVel φ ((H : ℝ) * s)) x)
          (realFourierModeGradFin K j x) * realFourierModeFin K i x) := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpoint x
      _ = _ := integral_const_mul _ _
  rw [hdrift]
  ring

theorem GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM_horizon_eq (H K : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (s : ℝ) :
    GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM (classicalGalerkinHorizonStream H φ)
        ((H : ℝ) * κ) K s =
      (H : ℝ) • GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM φ κ K ((H : ℝ) * s) := by
  ext c i
  simp only [GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM, matrixCoefficientCLM_apply]
  change (∑ j : Fin (RealFourierDimension K),
      weakFormMatrixEntry
        (fun r x => AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.streamVel (classicalGalerkinHorizonStream H φ) r) x)
        ((H : ℝ) * κ) (realFourierModeFin K) (realFourierModeGradFin K) s i j *
          c.ofLp j) =
    ((H : ℝ) • GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM φ κ K ((H : ℝ) * s)
        c).ofLp i
  have hright :
      ((H : ℝ) • GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM φ κ K ((H : ℝ) * s)
          c).ofLp i =
        (H : ℝ) * ∑ j : Fin (RealFourierDimension K),
          weakFormMatrixEntry
            (fun r x => AVenhance.Infra.Torus.periodicToTorus
              (AVenhance.streamVel φ r) x)
            κ (realFourierModeFin K) (realFourierModeGradFin K)
            ((H : ℝ) * s) i j * c.ofLp j := by
    rw [PiLp.smul_apply, GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM,
        matrixCoefficientCLM_apply]
    simp only [smul_eq_mul]
  rw [hright, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [GalerkinHorizonConsistency.classicalGalerkinWeakEntry_horizon_eq H K φ hφ κ s i j]
  ring

theorem classicalForcingCoefficients_horizon_eq (H K : ℕ)
    (F : ℝ → Vec 2 → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    classicalForcingCoefficients K (classicalGalerkinHorizonForcing H F) s =
      (H : ℝ) • classicalForcingCoefficients K F ((H : ℝ) * s) := by
  have hHs : 0 ≤ (H : ℝ) * s := mul_nonneg (Nat.cast_nonneg H) hs
  ext i
  dsimp [classicalForcingCoefficients, modeProjectionCoefficients]
  simp only [max_eq_left hs, max_eq_left hHs]
  unfold classicalGalerkinHorizonForcing
  have hfun : (fun x : Torus =>
      AVenhance.Infra.Torus.periodicToTorus
        (fun y => (H : ℝ) * F ((H : ℝ) * s) y) x * realFourierModeFin K i x) =
      fun x => (H : ℝ) * (AVenhance.Infra.Torus.periodicToTorus
        (F ((H : ℝ) * s)) x * realFourierModeFin K i x) := by
    funext x
    simp [AVenhance.Infra.Torus.periodicToTorus]
    ring
  rw [hfun, integral_const_mul]

/-- The finite ODE data obtained by running the Galerkin construction on a physical
integer horizon. -/
noncomputable def classicalGalerkinHorizonODEData
    (H : ℕ) (hH : 0 < H)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (K : ℕ) :
    AVenhance.Infra.ODE.LinearODEData
      (E := Coefficients (RealFourierDimension K)) 0 1 (by norm_num) :=
  (classicalForcedGalerkinData
    (classicalGalerkinHorizonStream H φ)
    (classicalGalerkinHorizonStream_admissible H φ hφ)
    ((H : ℝ) * κ) (mul_pos (Nat.cast_pos.mpr hH) hκ)
    (classicalGalerkinHorizonForcing H F)
    (classicalGalerkinHorizonForcing_smooth H F hF)
    θ₀ hθ₀ K).ode

theorem GalerkinHorizonConsistency.classicalGalerkinHorizonODEData_A_eq_generator
    (H : ℕ) (hH : 0 < H)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (K : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (classicalGalerkinHorizonODEData H hH φ hφ κ hκ F hF θ₀ hθ₀ K).A t =
      GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM (classicalGalerkinHorizonStream H φ)
        ((H : ℝ) * κ) K t := by
  change (classicalForcedGalerkinData
      (classicalGalerkinHorizonStream H φ)
      (classicalGalerkinHorizonStream_admissible H φ hφ)
      ((H : ℝ) * κ) (mul_pos (Nat.cast_pos.mpr hH) hκ)
      (classicalGalerkinHorizonForcing H F)
      (classicalGalerkinHorizonForcing_smooth H F hF)
      θ₀ hθ₀ K).weak.coefficient t = _
  change frozenWeakFormCoefficient
      (AVenhance.streamVel (classicalGalerkinHorizonStream H φ))
      ((H : ℝ) * κ) (realFourierModeFin K) (realFourierModeGradFin K) t = _
  simp [frozenWeakFormCoefficient, ht, GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM]

theorem GalerkinHorizonConsistency.classicalGalerkinHorizonODEData_f_eq_forcing
    (H : ℕ) (hH : 0 < H)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (K : ℕ) (t : ℝ) :
    (classicalGalerkinHorizonODEData H hH φ hφ κ hκ F hF θ₀ hθ₀ K).f t =
      classicalForcingCoefficients K (classicalGalerkinHorizonForcing H F) t := rfl

/-- The horizon-rescaled weak operators satisfy the `hA` identity required by finite-path
uniqueness on nested horizons. -/
theorem classicalGalerkinHorizonOperator_rescale
    (T S K : ℕ) (hT : 0 < T) (hTS : T ≤ S)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (classicalGalerkinHorizonODEData T hT φ hφ κ hκ F hF θ₀ hθ₀ K).A t =
      ((T : ℝ) / (S : ℝ)) •
        (classicalGalerkinHorizonODEData S (lt_of_lt_of_le hT hTS)
          φ hφ κ hκ F hF θ₀ hθ₀ K).A (((T : ℝ) / (S : ℝ)) * t) := by
  let q : ℝ := (T : ℝ) / (S : ℝ)
  have hS : 0 < (S : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hT hTS)
  have hq : 0 < q := div_pos (Nat.cast_pos.mpr hT) hS
  have hqle : q ≤ 1 := by
    dsimp [q]
    rw [div_le_one hS]
    exact_mod_cast hTS
  have hqt : q * t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hq.le ht.1
    · calc
        q * t ≤ 1 * t := mul_le_mul_of_nonneg_right hqle ht.1
        _ = t := one_mul _
        _ ≤ 1 := ht.2
  have hqS : q * (S : ℝ) = (T : ℝ) := by
    dsimp [q]
    field_simp [ne_of_gt hS]
  have htime : (S : ℝ) * (q * t) = (T : ℝ) * t := by
    calc
      (S : ℝ) * (q * t) = (q * (S : ℝ)) * t := by ring
      _ = (T : ℝ) * t := by rw [hqS]
  rw [GalerkinHorizonConsistency.classicalGalerkinHorizonODEData_A_eq_generator T hT φ hφ κ hκ F
      hF θ₀ hθ₀ K ht,
    GalerkinHorizonConsistency.classicalGalerkinHorizonODEData_A_eq_generator S (lt_of_lt_of_le hT
        hTS)
      φ hφ κ hκ F hF θ₀ hθ₀ K hqt]
  rw [GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM_horizon_eq T K φ hφ κ t,
    GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM_horizon_eq S K φ hφ κ (q * t)]
  calc
    (T : ℝ) • GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM φ κ K ((T : ℝ) * t) =
        (q * (S : ℝ)) • GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM φ κ K
          ((S : ℝ) * (q * t)) := by rw [hqS, htime]
    _ = q • ((S : ℝ) • GalerkinHorizonConsistency.classicalGalerkinGeneratorCLM φ κ K
          ((S : ℝ) * (q * t))) := by rw [smul_smul]

/-- The horizon-rescaled forcing vectors satisfy the `hf` identity required by finite-path
uniqueness on nested horizons. -/
theorem classicalGalerkinHorizonForcing_rescale
    (T S K : ℕ) (hT : 0 < T) (hTS : T ≤ S)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (classicalGalerkinHorizonODEData T hT φ hφ κ hκ F hF θ₀ hθ₀ K).f t =
      ((T : ℝ) / (S : ℝ)) •
        (classicalGalerkinHorizonODEData S (lt_of_lt_of_le hT hTS)
          φ hφ κ hκ F hF θ₀ hθ₀ K).f (((T : ℝ) / (S : ℝ)) * t) := by
  let q : ℝ := (T : ℝ) / (S : ℝ)
  have hS : 0 < (S : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hT hTS)
  have hq : 0 < q := div_pos (Nat.cast_pos.mpr hT) hS
  have hqle : q ≤ 1 := by
    dsimp [q]
    rw [div_le_one hS]
    exact_mod_cast hTS
  have hqt : q * t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hq.le ht.1
    · calc
        q * t ≤ 1 * t := mul_le_mul_of_nonneg_right hqle ht.1
        _ = t := one_mul _
        _ ≤ 1 := ht.2
  have hqS : q * (S : ℝ) = (T : ℝ) := by
    dsimp [q]
    field_simp [ne_of_gt hS]
  have htime : (S : ℝ) * (q * t) = (T : ℝ) * t := by
    calc
      (S : ℝ) * (q * t) = (q * (S : ℝ)) * t := by ring
      _ = (T : ℝ) * t := by rw [hqS]
  rw [GalerkinHorizonConsistency.classicalGalerkinHorizonODEData_f_eq_forcing T hT φ hφ κ hκ F hF
      θ₀ hθ₀ K t,
    GalerkinHorizonConsistency.classicalGalerkinHorizonODEData_f_eq_forcing S (lt_of_lt_of_le hT
        hTS)
      φ hφ κ hκ F hF θ₀ hθ₀ K (q * t)]
  rw [classicalForcingCoefficients_horizon_eq T K F ht.1,
    classicalForcingCoefficients_horizon_eq S K F hqt.1]
  calc
    (T : ℝ) • classicalForcingCoefficients K F ((T : ℝ) * t) =
        (q * (S : ℝ)) • classicalForcingCoefficients K F
          ((S : ℝ) * (q * t)) := by rw [hqS, htime]
    _ = q • ((S : ℝ) • classicalForcingCoefficients K F
          ((S : ℝ) * (q * t))) := by rw [smul_smul]

theorem GalerkinHorizonConsistency.classicalGalerkinHorizonODEData_y₀_eq_projection
    (H : ℕ) (hH : 0 < H)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (K : ℕ) :
    (classicalGalerkinHorizonODEData H hH φ hφ κ hκ F hF θ₀ hθ₀ K).y₀ =
      modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus θ₀) := by
  change (classicalForcedGalerkinData
      (classicalGalerkinHorizonStream H φ)
      (classicalGalerkinHorizonStream_admissible H φ hφ)
      ((H : ℝ) * κ) (mul_pos (Nat.cast_pos.mpr hH) hκ)
      (classicalGalerkinHorizonForcing H F)
      (classicalGalerkinHorizonForcing_smooth H F hF)
      θ₀ hθ₀ K).initial = _
  change ((classicalFrozenDriftProblem
      (classicalGalerkinHorizonStream H φ)
      (classicalGalerkinHorizonStream_admissible H φ hφ)
      ((H : ℝ) * κ) (mul_pos (Nat.cast_pos.mpr hH) hκ)
      θ₀ hθ₀).galerkinData K).initial = _
  rfl

/-- The base `L²` Galerkin limits on nested integer horizons agree under physical-time
restriction. This is the sequence-level consistency needed to patch the smooth representatives. -/
theorem classicalGalerkinHorizonLimitL2_consistent
    (T S : ℕ) (hT : 0 < T) (hTS : T ≤ S)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    ∀ s : Icc (0 : ℝ) 1,
      classicalGalerkinWordScalarPathLimit
        (classicalGalerkinHorizonStream T φ)
        (classicalGalerkinHorizonStream_admissible T φ hφ)
        ((T : ℝ) * κ) (mul_pos (Nat.cast_pos.mpr hT) hκ)
        (classicalGalerkinHorizonForcing T F)
        (classicalGalerkinHorizonForcing_smooth T F hF)
        (classicalGalerkinHorizonForcing_periodic T F hFper)
        θ₀ hθ₀ hθ₀per [] s =
      classicalGalerkinWordScalarPathLimit
        (classicalGalerkinHorizonStream S φ)
        (classicalGalerkinHorizonStream_admissible S φ hφ)
        ((S : ℝ) * κ)
        (mul_pos (Nat.cast_pos.mpr (lt_of_lt_of_le hT hTS)) hκ)
        (classicalGalerkinHorizonForcing S F)
        (classicalGalerkinHorizonForcing_smooth S F hF)
        (classicalGalerkinHorizonForcing_periodic S F hFper)
        θ₀ hθ₀ hθ₀per []
        (classicalGalerkinNestedTimeMap (T : ℝ) (S : ℝ)
          (Nat.cast_pos.mpr hT) (by exact_mod_cast hTS) s) := by
  let φT := classicalGalerkinHorizonStream T φ
  let hφT := classicalGalerkinHorizonStream_admissible T φ hφ
  let κT := (T : ℝ) * κ
  have hκT : 0 < κT := mul_pos (Nat.cast_pos.mpr hT) hκ
  let FT := classicalGalerkinHorizonForcing T F
  let hFT := classicalGalerkinHorizonForcing_smooth T F hF
  let hFTper := classicalGalerkinHorizonForcing_periodic T F hFper
  let φS := classicalGalerkinHorizonStream S φ
  let hφS := classicalGalerkinHorizonStream_admissible S φ hφ
  let κS := (S : ℝ) * κ
  have hκS : 0 < κS := mul_pos (Nat.cast_pos.mpr (lt_of_lt_of_le hT hTS)) hκ
  let FS := classicalGalerkinHorizonForcing S F
  let hFS := classicalGalerkinHorizonForcing_smooth S F hF
  let hFSper := classicalGalerkinHorizonForcing_periodic S F hFper
  let DT : (K : ℕ) → AVenhance.Infra.ODE.LinearODEData
      (E := Coefficients (RealFourierDimension K)) 0 1 (by norm_num) := fun K =>
    classicalGalerkinHorizonODEData T hT φ hφ κ hκ F hF θ₀ hθ₀ K
  let DS : (K : ℕ) → AVenhance.Infra.ODE.LinearODEData
      (E := Coefficients (RealFourierDimension K)) 0 1 (by norm_num) := fun K =>
    classicalGalerkinHorizonODEData S (lt_of_lt_of_le hT hTS)
      φ hφ κ hκ F hF θ₀ hθ₀ K
  let uT : (K : ℕ) → C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension K)) := fun K =>
    classicalGalerkinCoefficientPath φT hφT κT hκT FT hFT θ₀ hθ₀ K
  let uS : (K : ℕ) → C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension K)) := fun K =>
    classicalGalerkinCoefficientPath φS hφS κS hκS FS hFS θ₀ hθ₀ K
  let uTlim := classicalGalerkinWordScalarPathLimit
    φT hφT κT hκT FT hFT hFTper θ₀ hθ₀ hθ₀per []
  let uSlim := classicalGalerkinWordScalarPathLimit
    φS hφS κS hκS FS hFS hFSper θ₀ hθ₀ hθ₀per []
  have hsolT : ∀ K, (DT K).IsSolution (uT K) := by
    intro K
    exact classicalGalerkinCoefficientPath_isSolution φT hφT κT hκT FT hFT θ₀ hθ₀ K
  have hsolS : ∀ K, (DS K).IsSolution (uS K) := by
    intro K
    exact classicalGalerkinCoefficientPath_isSolution φS hφS κS hκS FS hFS θ₀ hθ₀ K
  have hy₀ : ∀ K, (DT K).y₀ = (DS K).y₀ := by
    intro K
    exact (GalerkinHorizonConsistency.classicalGalerkinHorizonODEData_y₀_eq_projection T hT φ hφ κ
        hκ F hF θ₀ hθ₀ K).trans
      (GalerkinHorizonConsistency.classicalGalerkinHorizonODEData_y₀_eq_projection S
          (lt_of_lt_of_le hT hTS)
        φ hφ κ hκ F hF θ₀ hθ₀ K).symm
  have hA : ∀ K t, t ∈ Icc (0 : ℝ) 1 →
      (DT K).A t = ((T : ℝ) / (S : ℝ)) •
        (DS K).A (((T : ℝ) / (S : ℝ)) * t) := by
    intro K t ht
    exact classicalGalerkinHorizonOperator_rescale T S K hT hTS φ hφ κ hκ F hF θ₀ hθ₀ ht
  have hf : ∀ K t, t ∈ Icc (0 : ℝ) 1 →
      (DT K).f t = ((T : ℝ) / (S : ℝ)) •
        (DS K).f (((T : ℝ) / (S : ℝ)) * t) := by
    intro K t ht
    exact classicalGalerkinHorizonForcing_rescale T S K hT hTS φ hφ κ hκ F hF θ₀ hθ₀ ht
  have hTlim : Tendsto
      (fun K => classicalGalerkinCoefficientScalarPath K (uT K))
      atTop (𝓝 uTlim) := by
    simpa [uT, uTlim, classicalGalerkinCoefficientScalarPath,
      classicalGalerkinWordScalarPath, realFourierWordDerivativeMap] using
      classicalGalerkinWordScalarPathLimit_tendsto
        φT hφT κT hκT FT hFT hFTper θ₀ hθ₀ hθ₀per []
  have hSlim : Tendsto
      (fun K => classicalGalerkinCoefficientScalarPath K (uS K))
      atTop (𝓝 uSlim) := by
    simpa [uS, uSlim, classicalGalerkinCoefficientScalarPath,
      classicalGalerkinWordScalarPath, realFourierWordDerivativeMap] using
      classicalGalerkinWordScalarPathLimit_tendsto
        φS hφS κS hκS FS hFS hFSper θ₀ hθ₀ hθ₀per []
  have hlimit := classicalGalerkinIncreasingHorizon_consistent_of_finiteODE
    (T : ℝ) (S : ℝ) (Nat.cast_pos.mpr hT) (by exact_mod_cast hTS)
    DT DS uT uS hsolT hsolS hy₀ hA hf uTlim uSlim hTlim hSlim
  intro s
  exact hlimit s

theorem GalerkinHorizonConsistency.classicalRealToComplexTorusCLM_injective :
    Function.Injective classicalRealToComplexTorusCLM := by
  intro u v huv
  let R := Complex.reCLM.compLpL (2 : ENNReal) (volume : Measure Torus)
  have hleft (w : ScalarTorusL2) : R (classicalRealToComplexTorusCLM w) = w := by
    apply Lp.ext
    filter_upwards [Complex.reCLM.coeFn_compLpL
        (classicalRealToComplexTorusCLM w),
      Complex.ofRealCLM.coeFn_compLpL w] with x hre hreal
    rw [hre]
    change Complex.reCLM
      (Complex.ofRealCLM.compLpL (2 : ENNReal) (volume : Measure Torus) w x) = _
    rw [hreal]
    simp only [Complex.reCLM_apply, Complex.ofRealCLM_apply, Complex.ofReal_re]
  calc
    u = R (classicalRealToComplexTorusCLM u) := (hleft u).symm
    _ = R (classicalRealToComplexTorusCLM v) := congrArg R huv
    _ = v := hleft v

theorem GalerkinHorizonConsistency.classicalPeriodicRealFunctions_eq_of_L2_eq
    (u v : Vec 2 → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hup : AVenhance.IsZ2Periodic u) (hvp : AVenhance.IsZ2Periodic v)
    (hL2 : (memLp_periodicToTorus_real hu hup).toLp
        (AVenhance.Infra.Torus.periodicToTorus u) =
      (memLp_periodicToTorus_real hv hvp).toLp
        (AVenhance.Infra.Torus.periodicToTorus v)) : u = v := by
  have huTor : AVenhance.Infra.Torus.IsZdPeriodic u :=
    (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen u).2 hup
  have hvTor : AVenhance.Infra.Torus.IsZdPeriodic v :=
    (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen v).2 hvp
  have huComplex : AVenhance.Infra.Torus.IsZdPeriodic
      (AVenhance.Infra.Torus.realToComplex u) := by
    apply (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen _).2
    intro z x
    exact congrArg (fun y : ℝ => (y : ℂ)) (hup z x)
  have hvComplex : AVenhance.Infra.Torus.IsZdPeriodic
      (AVenhance.Infra.Torus.realToComplex v) := by
    apply (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen _).2
    intro z x
    exact congrArg (fun y : ℝ => (y : ℂ)) (hvp z x)
  have hcontu : Continuous (AVenhance.Infra.Torus.periodicToTorus
      (AVenhance.Infra.Torus.realToComplex u)) :=
    AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
      (Complex.ofRealCLM.continuous.comp hu) huComplex
  have hcontv : Continuous (AVenhance.Infra.Torus.periodicToTorus
      (AVenhance.Infra.Torus.realToComplex v)) :=
    AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
      (Complex.ofRealCLM.continuous.comp hv) hvComplex
  let zu : C(Torus, ℂ) := ⟨AVenhance.Infra.Torus.periodicToTorus
    (AVenhance.Infra.Torus.realToComplex u), hcontu⟩
  let zv : C(Torus, ℂ) := ⟨AVenhance.Infra.Torus.periodicToTorus
    (AVenhance.Infra.Torus.realToComplex v), hcontv⟩
  have hcucont : Continuous (fun x => (zu x).re) := by
    change Continuous (fun x => Complex.reCLM (zu x))
    exact Complex.reCLM.continuous.comp zu.continuous
  have hcvcont : Continuous (fun x => (zv x).re) := by
    change Continuous (fun x => Complex.reCLM (zv x))
    exact Complex.reCLM.continuous.comp zv.continuous
  let cu : C(Torus, ℝ) := ⟨fun x => (zu x).re, hcucont⟩
  let cv : C(Torus, ℝ) := ⟨fun x => (zv x).re, hcvcont⟩
  have hurep (x : Torus) : cu x = AVenhance.Infra.Torus.periodicToTorus u x := by
    simp [cu, zu, AVenhance.Infra.Torus.realToComplex,
      AVenhance.Infra.Torus.periodicToTorus, Complex.ofReal_re]
  have hvrep (x : Torus) : cv x = AVenhance.Infra.Torus.periodicToTorus v x := by
    simp [cv, zv, AVenhance.Infra.Torus.realToComplex,
      AVenhance.Infra.Torus.periodicToTorus, Complex.ofReal_re]
  have hcu : ContinuousMap.toLp 2 (volume : Measure Torus) ℝ cu =
      (memLp_periodicToTorus_real hu hup).toLp
        (AVenhance.Infra.Torus.periodicToTorus u) := by
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
        (μ := (volume : Measure Torus)) (𝕜 := ℝ) cu,
      (memLp_periodicToTorus_real hu hup).coeFn_toLp] with x hcu hmem
    rw [hcu, hmem]
    exact hurep x
  have hcv : ContinuousMap.toLp 2 (volume : Measure Torus) ℝ cv =
      (memLp_periodicToTorus_real hv hvp).toLp
        (AVenhance.Infra.Torus.periodicToTorus v) := by
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
        (μ := (volume : Measure Torus)) (𝕜 := ℝ) cv,
      (memLp_periodicToTorus_real hv hvp).coeFn_toLp] with x hcv hmem
    rw [hcv, hmem]
    exact hvrep x
  have heq : ContinuousMap.toLp 2 (volume : Measure Torus) ℝ cu =
      ContinuousMap.toLp 2 (volume : Measure Torus) ℝ cv := by
    rw [hcu, hL2, hcv]
  have hfun : cu = cv :=
    (ContinuousMap.toLp_injective (p := (2 : ENNReal))
      (μ := (volume : Measure Torus)) (𝕜 := ℝ)) heq
  funext x
  calc
    u x = cu (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
      rw [hurep]
      have h := congrFun
        (AVenhance.Infra.Torus.fromUnitTorus_periodicToTorus huTor) x
      change AVenhance.Infra.Torus.periodicToTorus u
        (AVenhance.Infra.Torus.toUnitTorus 2 x) = u x at h
      exact h.symm
    _ = cv (AVenhance.Infra.Torus.toUnitTorus 2 x) :=
      congrArg (fun f : C(Torus, ℝ) => f
        (AVenhance.Infra.Torus.toUnitTorus 2 x)) hfun
    _ = v x := by
      rw [hvrep]
      have h := congrFun
        (AVenhance.Infra.Torus.fromUnitTorus_periodicToTorus hvTor) x
      change AVenhance.Infra.Torus.periodicToTorus v
        (AVenhance.Infra.Torus.toUnitTorus 2 x) = v x at h
      exact h

/-- The smooth unit-slab representative associated with a positive physical integer horizon. -/
@[irreducible]
noncomputable def classicalGalerkinHorizonSmoothSlice
    (H : ℕ) (hH : 0 < H)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (s : Icc (0 : ℝ) 1) : Vec 2 → ℝ :=
  classicalGalerkinHorizonLimit H hH φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per
    ((H : ℝ) * (s : ℝ))

/-- The smooth unit-slab representatives themselves agree on nested integer horizons. -/
theorem classicalGalerkinHorizonSmoothLimit_consistent
    (T S : ℕ) (hT : 0 < T) (hTS : T ≤ S)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (s : Icc (0 : ℝ) 1) :
    classicalGalerkinHorizonSmoothSlice T hT φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per s =
      classicalGalerkinHorizonSmoothSlice S (lt_of_lt_of_le hT hTS)
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per
        (classicalGalerkinNestedTimeMap (T : ℝ) (S : ℝ)
          (Nat.cast_pos.mpr hT) (by exact_mod_cast hTS) s) := by
  let φT := classicalGalerkinHorizonStream T φ
  let hφT := classicalGalerkinHorizonStream_admissible T φ hφ
  let κT := (T : ℝ) * κ
  have hκT : 0 < κT := mul_pos (Nat.cast_pos.mpr hT) hκ
  let FT := classicalGalerkinHorizonForcing T F
  let hFT := classicalGalerkinHorizonForcing_smooth T F hF
  let hFTper := classicalGalerkinHorizonForcing_periodic T F hFper
  let φS := classicalGalerkinHorizonStream S φ
  let hφS := classicalGalerkinHorizonStream_admissible S φ hφ
  let κS := (S : ℝ) * κ
  have hκS : 0 < κS := mul_pos (Nat.cast_pos.mpr (lt_of_lt_of_le hT hTS)) hκ
  let FS := classicalGalerkinHorizonForcing S F
  let hFS := classicalGalerkinHorizonForcing_smooth S F hF
  let hFSper := classicalGalerkinHorizonForcing_periodic S F hFper
  let σ := classicalGalerkinNestedTimeMap (T : ℝ) (S : ℝ)
    (Nat.cast_pos.mpr hT) (by exact_mod_cast hTS)
  unfold classicalGalerkinHorizonSmoothSlice at ⊢
  have hTcast : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hScast : 0 < (S : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hT hTS)
  have hTquot : (T : ℝ) * (s : ℝ) / (T : ℝ) = (s : ℝ) := by
    field_simp [ne_of_gt hTcast]
  have hSquot : (S : ℝ) * (σ s : ℝ) / (S : ℝ) = (σ s : ℝ) := by
    field_simp [ne_of_gt hScast]
  have hclT : classicalGalerkinUnitSlabClamp
      ((T : ℝ) * (s : ℝ) / (T : ℝ)) = s := by
    apply Subtype.ext
    simp [classicalGalerkinUnitSlabClamp, hTquot,
      max_eq_right s.property.1, min_eq_right s.property.2]
  have hclS : classicalGalerkinUnitSlabClamp
      ((S : ℝ) * (σ s : ℝ) / (S : ℝ)) = σ s := by
    apply Subtype.ext
    simp [classicalGalerkinUnitSlabClamp, hSquot,
      max_eq_right (σ s).property.1, min_eq_right (σ s).property.2]
  change classicalGalerkinRealSmoothLift φT hφT κT hκT FT hFT hFTper
      θ₀ hθ₀ hθ₀per
      (classicalGalerkinUnitSlabClamp ((T : ℝ) * (s : ℝ) / (T : ℝ))) =
    classicalGalerkinRealSmoothLift φS hφS κS hκS FS hFS hFSper θ₀ hθ₀ hθ₀per
      (classicalGalerkinUnitSlabClamp ((S : ℝ) * (σ s : ℝ) / (S : ℝ)))
  rw [hclT, hclS]
  let limitT := classicalGalerkinWordScalarPathLimit
    φT hφT κT hκT FT hFT hFTper θ₀ hθ₀ hθ₀per []
  let limitS := classicalGalerkinWordScalarPathLimit
    φS hφS κS hκS FS hFS hFSper θ₀ hθ₀ hθ₀per []
  let smoothT := classicalGalerkinRealSmoothDerivativeL2
    φT hφT κT hκT FT hFT hFTper θ₀ hθ₀ hθ₀per [] s
  let smoothS := classicalGalerkinRealSmoothDerivativeL2
    φS hφS κS hκS FS hFS hFSper θ₀ hθ₀ hθ₀per [] (σ s)
  have hL2 := classicalGalerkinHorizonLimitL2_consistent
    T S hT hTS φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per s
  have hcomplexT : classicalRealToComplexTorusCLM (limitT s) =
      classicalRealToComplexTorusCLM smoothT := by
    exact classicalGalerkinWordScalarPathLimit_eq_smoothDerivative
      φT hφT κT hκT FT hFT hFTper θ₀ hθ₀ hθ₀per [] s
  have hcomplexS : classicalRealToComplexTorusCLM (limitS (σ s)) =
      classicalRealToComplexTorusCLM smoothS := by
    exact classicalGalerkinWordScalarPathLimit_eq_smoothDerivative
      φS hφS κS hκS FS hFS hFSper θ₀ hθ₀ hθ₀per [] (σ s)
  have hlimit : limitT s = limitS (σ s) := hL2
  have hcomplex : classicalRealToComplexTorusCLM smoothT =
      classicalRealToComplexTorusCLM smoothS := by
    calc
      _ = classicalRealToComplexTorusCLM (limitT s) := hcomplexT.symm
      _ = classicalRealToComplexTorusCLM (limitS (σ s)) :=
        congrArg classicalRealToComplexTorusCLM hlimit
      _ = _ := hcomplexS
  have hrealL2 : smoothT = smoothS :=
    GalerkinHorizonConsistency.classicalRealToComplexTorusCLM_injective hcomplex
  let u := classicalGalerkinRealSmoothLift φT hφT κT hκT FT hFT hFTper
    θ₀ hθ₀ hθ₀per s
  let v := classicalGalerkinRealSmoothLift φS hφS κS hκS FS hFS hFSper
    θ₀ hθ₀ hθ₀per (σ s)
  have hucont : Continuous u := by
    exact (classicalGalerkinRealSmoothLift_contDiff
      φT hφT κT hκT FT hFT hFTper θ₀ hθ₀ hθ₀per s).continuous
  have hvcont : Continuous v := by
    exact (classicalGalerkinRealSmoothLift_contDiff
      φS hφS κS hκS FS hFS hFSper θ₀ hθ₀ hθ₀per (σ s)).continuous
  have huper : AVenhance.IsZ2Periodic u :=
    classicalGalerkinRealSmoothLift_periodic
      φT hφT κT hκT FT hFT hFTper θ₀ hθ₀ hθ₀per s
  have hvper : AVenhance.IsZ2Periodic v :=
    classicalGalerkinRealSmoothLift_periodic
      φS hφS κS hκS FS hFS hFSper θ₀ hθ₀ hθ₀per (σ s)
  have hderivL2T : smoothT =
      (memLp_periodicToTorus_real hucont huper).toLp
        (AVenhance.Infra.Torus.periodicToTorus u) := by
    simp [smoothT, classicalGalerkinRealSmoothDerivativeL2, u, classicalWordDerivative]
  have hderivL2S : smoothS =
      (memLp_periodicToTorus_real hvcont hvper).toLp
        (AVenhance.Infra.Torus.periodicToTorus v) := by
    simp [smoothS, classicalGalerkinRealSmoothDerivativeL2, v, classicalWordDerivative]
  have hrealL2' : (memLp_periodicToTorus_real hucont huper).toLp
      (AVenhance.Infra.Torus.periodicToTorus u) =
    (memLp_periodicToTorus_real hvcont hvper).toLp
      (AVenhance.Infra.Torus.periodicToTorus v) := by
    calc
      _ = smoothT := hderivL2T.symm
      _ = smoothS := hrealL2
      _ = _ := hderivL2S
  exact GalerkinHorizonConsistency.classicalPeriodicRealFunctions_eq_of_L2_eq
    u v hucont hvcont huper hvper hrealL2'

/-- Physical-time smooth limits from a shorter integer horizon agree pointwise with those from a
longer horizon throughout the shorter closed interval. -/
theorem classicalGalerkinHorizonLimit_consistent_on_overlap
    (T S : ℕ) (hT : 0 < T) (hTS : T ≤ S)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) :
    classicalGalerkinHorizonLimit T hT φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t =
    classicalGalerkinHorizonLimit S (lt_of_lt_of_le hT hTS) φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t := by
  have hTpos : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hSpos : 0 < (S : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hT hTS)
  let s : Icc (0 : ℝ) 1 := ⟨t / (T : ℝ),
    ⟨div_nonneg ht.1 hTpos.le, (div_le_one hTpos).2 ht.2⟩⟩
  have hTtime : (T : ℝ) * (s : ℝ) = t := by
    change (T : ℝ) * (t / (T : ℝ)) = t
    field_simp [ne_of_gt hTpos]
  let σ := classicalGalerkinNestedTimeMap (T : ℝ) (S : ℝ) hTpos
    (by exact_mod_cast hTS)
  have hStime : (S : ℝ) * (σ s : ℝ) = t := by
    calc
      (S : ℝ) * (σ s : ℝ) = (T : ℝ) * (s : ℝ) :=
        classicalGalerkinNestedTimeMap_physicalTime
          (T : ℝ) (S : ℝ) hTpos (by exact_mod_cast hTS) s
      _ = t := hTtime
  have hleft : classicalGalerkinHorizonLimit T hT φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t =
    classicalGalerkinHorizonSmoothSlice T hT φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per s := by
    unfold classicalGalerkinHorizonSmoothSlice
    rw [hTtime]
  have hright : classicalGalerkinHorizonLimit S (lt_of_lt_of_le hT hTS)
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t =
    classicalGalerkinHorizonSmoothSlice S (lt_of_lt_of_le hT hTS)
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per (σ s) := by
    unfold classicalGalerkinHorizonSmoothSlice
    rw [hStime]
  rw [hleft, hright]
  exact classicalGalerkinHorizonSmoothLimit_consistent T S hT hTS
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per s

/-- Use horizon `N+1` at family index `N`, so every member has a positive horizon. -/
@[irreducible]
noncomputable def classicalGalerkinIntegerHorizonFamily
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) : ℕ → ℝ → Vec 2 → ℝ :=
  fun N => classicalGalerkinHorizonLimit (Nat.succ N) (Nat.succ_pos N)
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per

theorem classicalGalerkinIntegerHorizonFamily_periodic
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    ∀ N t, 0 ≤ t → AVenhance.IsZ2Periodic
      (classicalGalerkinIntegerHorizonFamily φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per N t) := by
  intro N t ht
  unfold classicalGalerkinIntegerHorizonFamily
  exact classicalGalerkinHorizonLimit_periodic
    (Nat.succ N) (Nat.succ_pos N) φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t

theorem classicalGalerkinIntegerHorizonFamily_initial
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    ∀ N x, classicalGalerkinIntegerHorizonFamily φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per N 0 x = θ₀ x := by
  intro N x
  unfold classicalGalerkinIntegerHorizonFamily
  exact classicalGalerkinHorizonLimit_initial
    (Nat.succ N) (Nat.succ_pos N) φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per x

theorem classicalGalerkinIntegerHorizonFamily_advDiffOp
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    ∀ n, ∀ t, t ∈ Ioo (0 : ℝ) (Nat.succ n : ℝ) → ∀ x,
      AVenhance.advDiffOp (AVenhance.streamVel φ) κ
        (classicalGalerkinIntegerHorizonFamily φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per n) t x = F t x := by
  intro n t ht x
  unfold classicalGalerkinIntegerHorizonFamily
  exact classicalGalerkinHorizonLimit_advDiffOp
    (Nat.succ n) (Nat.succ_pos n) φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per ht x

theorem classicalGalerkinIntegerHorizonFamily_consistent
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    ∀ (M N : ℕ), M ≤ N → ∀ t, t ∈ Icc (0 : ℝ) (M : ℝ) →
      classicalGalerkinIntegerHorizonFamily φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per M t =
      classicalGalerkinIntegerHorizonFamily φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per N t := by
  intro M N hMN t ht
  unfold classicalGalerkinIntegerHorizonFamily
  apply classicalGalerkinHorizonLimit_consistent_on_overlap
    (Nat.succ M) (Nat.succ N) (Nat.succ_pos M) (Nat.succ_le_succ hMN)
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per
  exact ⟨ht.1, ht.2.trans (by exact_mod_cast Nat.le_succ M)⟩

end AVenhance.Infra.Classical

end
