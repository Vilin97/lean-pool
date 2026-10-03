/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.Density
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Existence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Fourier and time-rescaling adapters for the classical Galerkin limit paths.

The strong limit constructed in `Infra/Classical/GalerkinSmoothLimit` has type
`C(Icc (0 : ℝ) 1, ScalarTorusL2)`. These lemmas identify such limits from their Fourier cutoffs
and compare them on nested physical-time intervals. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open AVenhance.Infra.Parabolic.FourierGalerkin

namespace AVenhance.Infra.Classical

/-- Limits of finite Galerkin paths preserve equality under a continuous time reparameterization.
This is the comparison step used when two scaled unit-slab constructions describe the same
physical times. -/
theorem classicalGalerkinLimitPath_eq_under_timeMap
    (a b : ℕ → C(Icc (0 : ℝ) 1, ScalarTorusL2))
    (u v : C(Icc (0 : ℝ) 1, ScalarTorusL2))
    (ha : Tendsto a atTop (𝓝 u)) (hb : Tendsto b atTop (𝓝 v))
    (σ : C(Icc (0 : ℝ) 1, Icc (0 : ℝ) 1))
    (hfinite : ∀ N s, a N s = b N (σ s)) :
    ∀ s, u s = v (σ s) := by
  intro s
  have hA : Tendsto (fun N => a N s) atTop (𝓝 (u s)) := by
    have heval :=
      ((ContinuousMap.evalCLM (R := ℝ) s).continuous.continuousAt.tendsto).comp ha
    have hseq : (⇑(ContinuousMap.evalCLM (R := ℝ) s) ∘ a) =
        fun N => a N s := by
      funext N
      rfl
    rw [hseq] at heval
    simpa using heval
  have hB : Tendsto (fun N => b N (σ s)) atTop (𝓝 (v (σ s))) := by
    have heval :=
      ((ContinuousMap.evalCLM (R := ℝ) (σ s)).continuous.continuousAt.tendsto).comp hb
    have hseq : (⇑(ContinuousMap.evalCLM (R := ℝ) (σ s)) ∘ b) =
        fun N => b N (σ s) := by
      funext N
      rfl
    rw [hseq] at heval
    simpa using heval
  have hseq : (fun N => a N s) = fun N => b N (σ s) := by
    funext N
    exact hfinite N s
  rw [hseq] at hA
  exact tendsto_nhds_unique hA hB

/-- Rescale the shorter unit slab into a longer unit slab: equal normalized points represent the
same physical time when the first construction has horizon `T` and the second horizon `S`. -/
noncomputable def classicalGalerkinNestedTimeMap (T S : ℝ)
    (hT : 0 < T) (hTS : T ≤ S) :
    C(Icc (0 : ℝ) 1, Icc (0 : ℝ) 1) := by
  have hS : 0 < S := lt_of_lt_of_le hT hTS
  have hscale0 : 0 ≤ T / S := (div_pos hT hS).le
  have hscale1 : T / S ≤ 1 := (div_le_iff₀ hS).2 (by simpa using hTS)
  have hmem (s : Icc (0 : ℝ) 1) : (T / S) * (s : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hscale0 s.property.1
    · calc
        (T / S) * (s : ℝ) ≤ 1 * (s : ℝ) :=
          mul_le_mul_of_nonneg_right hscale1 s.property.1
        _ = s := one_mul _
        _ ≤ 1 := s.property.2
  refine ⟨fun s => ⟨(T / S) * (s : ℝ), hmem s⟩, ?_⟩
  exact Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) hmem

/-- The nested unit-slab map preserves physical time. -/
theorem classicalGalerkinNestedTimeMap_physicalTime (T S : ℝ)
    (hT : 0 < T) (hTS : T ≤ S) (s : Icc (0 : ℝ) 1) :
    S * ((classicalGalerkinNestedTimeMap T S hT hTS s : ℝ)) = T * (s : ℝ) := by
  change S * ((T / S) * (s : ℝ)) = T * (s : ℝ)
  field_simp [ne_of_gt (lt_of_lt_of_le hT hTS)]

/-- Finite-dimensional linear Galerkin paths agree on a nested interval when their operators and
forcings are related by the physical-time rescaling. This discharges the finite-path premise in
`classicalGalerkinIncreasingHorizon_consistent` for the horizon-rescaled Galerkin systems. -/
theorem classicalGalerkinFiniteODEPath_rescale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T S : ℝ) (hT : 0 < T) (hTS : T ≤ S)
    (DT DS : AVenhance.Infra.ODE.LinearODEData (E := E) 0 1 (by norm_num))
    (uT uS : C(Icc (0 : ℝ) 1, E))
    (huT : DT.IsSolution uT) (huS : DS.IsSolution uS)
    (hy₀ : DT.y₀ = DS.y₀)
    (hA : ∀ t, t ∈ Icc (0 : ℝ) 1 →
      DT.A t = (T / S) • DS.A ((T / S) * t))
    (hf : ∀ t, t ∈ Icc (0 : ℝ) 1 →
      DT.f t = (T / S) • DS.f ((T / S) * t)) :
    ∀ s, uT s = uS (classicalGalerkinNestedTimeMap T S hT hTS s) := by
  let c : ℝ := T / S
  let σ := classicalGalerkinNestedTimeMap T S hT hTS
  let v : C(Icc (0 : ℝ) 1, E) := uS.comp σ
  have hSpos : 0 < S := lt_of_lt_of_le hT hTS
  have hc : 0 < c := div_pos hT hSpos
  have hc1 : c ≤ 1 := by
    dsimp [c]
    rw [div_le_iff₀ hSpos]
    simpa using hTS
  have hσ (s : Icc (0 : ℝ) 1) : (σ s : ℝ) = c * (s : ℝ) := rfl
  have hv : DT.IsSolution v := by
    apply (DT.isSolution_iff_integralSolution v).2
    intro t ht
    let q : Icc (0 : ℝ) 1 := ⟨t, ht⟩
    let g : ℝ → E := fun r =>
      AVenhance.Infra.ODE.linearRhs DS.A DS.f
        (AVenhance.Infra.ODE.extendCurve (by norm_num) uS) r
    have hSIntegral := (huS.integralSolution DS) (σ q) (σ q).property
    have hscale (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
        AVenhance.Infra.ODE.linearRhs DT.A DT.f
          (AVenhance.Infra.ODE.extendCurve (by norm_num) v) r =
          c • g (c * r) := by
      have hσq : σ ⟨r, hr.1, hr.2⟩ = ⟨c * r, by
          constructor
          · exact mul_nonneg hc.le hr.1
          · change c * r ≤ 1
            calc
              c * r ≤ 1 * r := mul_le_mul_of_nonneg_right hc1 hr.1
              _ = r := one_mul _
              _ ≤ 1 := hr.2⟩ := by
        apply Subtype.ext
        rfl
      have hvs : v ⟨r, hr.1, hr.2⟩ =
          AVenhance.Infra.ODE.extendCurve (by norm_num) uS (c * r) := by
        change uS (σ ⟨r, hr.1, hr.2⟩) = _
        rw [hσq,
          AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) uS
            (by
              exact (σ ⟨r, hr.1, hr.2⟩).property)]
      change DT.A r (AVenhance.Infra.ODE.extendCurve (by norm_num) v r) + DT.f r = _
      rw [AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) v hr]
      rw [hvs, hA r hr, hf r hr]
      change c • DS.A (c * r)
          (AVenhance.Infra.ODE.extendCurve (by norm_num) uS (c * r)) +
            c • DS.f (c * r) =
        c • (DS.A (c * r)
            (AVenhance.Infra.ODE.extendCurve (by norm_num) uS (c * r)) +
          DS.f (c * r))
      rw [← smul_add]
    have hInt :
        (∫ r in (0 : ℝ)..t,
          AVenhance.Infra.ODE.linearRhs DT.A DT.f
            (AVenhance.Infra.ODE.extendCurve (by norm_num) v) r) =
        ∫ r in (0 : ℝ)..(c * t), g r := by
      calc
        _ = ∫ r in (0 : ℝ)..t, c • g (c * r) := by
          apply intervalIntegral.integral_congr
          intro r hr
          have hr' : r ∈ Icc (0 : ℝ) 1 := by
            have hrt : r ∈ Icc (0 : ℝ) t := by
              simpa only [uIcc_of_le ht.1] using hr
            exact ⟨hrt.1, hrt.2.trans ht.2⟩
          exact hscale r hr'
        _ = c • ∫ r in (0 : ℝ)..t, g (c * r) := by
          rw [intervalIntegral.integral_smul]
        _ = ∫ r in (0 : ℝ)..(c * t), g r := by
          simpa only [mul_zero] using
            (intervalIntegral.smul_integral_comp_mul_left
              (a := (0 : ℝ)) (b := t) g c)
    have hSValue :
        uS (σ q) = DS.y₀ + ∫ r in (0 : ℝ)..(c * t), g r := by
      have h := hSIntegral
      rw [AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) uS
        (σ q).property] at h
      have hval := hσ q
      change uS (σ q) = DS.y₀ + ∫ r in (0 : ℝ)..(σ q : ℝ), g r at h
      rw [hval] at h
      simpa [g] using h
    calc
      AVenhance.Infra.ODE.extendCurve (by norm_num) v t = uS (σ q) := by
        rw [AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) v ht]
        rfl
      _ = DS.y₀ + ∫ r in (0 : ℝ)..(c * t), g r := hSValue
      _ = DT.y₀ + ∫ r in (0 : ℝ)..t,
            AVenhance.Infra.ODE.linearRhs DT.A DT.f
              (AVenhance.Infra.ODE.extendCurve (by norm_num) v) r := by
        rw [hy₀, ← hInt]
  obtain ⟨w, hw, huniq⟩ := DT.existsUnique_solution
  have huT' : uT = w := huniq uT huT
  have hv' : v = w := huniq v hv
  intro s
  calc
    uT s = w s := congrArg (fun p : C(Icc (0 : ℝ) 1, E) => p s) huT'
    _ = v s := congrArg (fun p : C(Icc (0 : ℝ) 1, E) => p s) hv'.symm
    _ = uS (σ s) := rfl

/-- View a finite real-Fourier coefficient path as a continuous scalar torus `L²` path. -/
noncomputable def classicalGalerkinCoefficientScalarPath (N : ℕ)
    (u : C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension N))) :
    C(Icc (0 : ℝ) 1, ScalarTorusL2) :=
  ⟨fun t => realFourierScalarMap N (u t),
    (realFourierScalarMap N).continuous.comp u.continuous⟩

/-- Increasing-horizon consistency for the exact real-Fourier Galerkin coefficient paths.
The finite-path equality is derived from uniqueness of each rescaled coefficient ODE, so only the
physical-time scaling identities for its operator and forcing remain as source-specific inputs. -/
theorem classicalGalerkinIncreasingHorizon_consistent_of_finiteODE
    (T S : ℝ) (hT : 0 < T) (hTS : T ≤ S)
    (DT DS : (N : ℕ) →
      AVenhance.Infra.ODE.LinearODEData
        (E := Coefficients (RealFourierDimension N)) 0 1 (by norm_num))
    (uT uS : (N : ℕ) →
      C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension N)))
    (hsolT : ∀ N, (DT N).IsSolution (uT N))
    (hsolS : ∀ N, (DS N).IsSolution (uS N))
    (hy₀ : ∀ N, (DT N).y₀ = (DS N).y₀)
    (hA : ∀ N t, t ∈ Icc (0 : ℝ) 1 →
      (DT N).A t = (T / S) • (DS N).A ((T / S) * t))
    (hf : ∀ N t, t ∈ Icc (0 : ℝ) 1 →
      (DT N).f t = (T / S) • (DS N).f ((T / S) * t))
    (uTlim uSlim : C(Icc (0 : ℝ) 1, ScalarTorusL2))
    (hTlim : Tendsto
      (fun N => classicalGalerkinCoefficientScalarPath N (uT N))
      atTop (𝓝 uTlim))
    (hSlim : Tendsto
      (fun N => classicalGalerkinCoefficientScalarPath N (uS N))
      atTop (𝓝 uSlim)) :
    ∀ s, uTlim s =
      uSlim (classicalGalerkinNestedTimeMap T S hT hTS s) := by
  apply classicalGalerkinLimitPath_eq_under_timeMap
    (fun N => classicalGalerkinCoefficientScalarPath N (uT N))
    (fun N => classicalGalerkinCoefficientScalarPath N (uS N))
    uTlim uSlim hTlim hSlim (classicalGalerkinNestedTimeMap T S hT hTS)
  intro N s
  have hpath := classicalGalerkinFiniteODEPath_rescale T S hT hTS
    (DT N) (DS N) (uT N) (uS N) (hsolT N) (hsolS N) (hy₀ N)
    (hA N) (hf N) s
  change realFourierScalarMap N (uT N s) =
    realFourierScalarMap N
      (uS N (classicalGalerkinNestedTimeMap T S hT hTS s))
  exact congrArg (realFourierScalarMap N) hpath

/-- Increasing-horizon consistency follows once the finite Galerkin paths agree after restriction.
The limit and approximant types match the word-derivative paths used by the smooth Fourier
construction, so this theorem applies separately to every spatial derivative word. -/
theorem classicalGalerkinIncreasingHorizon_consistent
    (T S : ℝ) (hT : 0 < T) (hTS : T ≤ S)
    (a b : ℕ → C(Icc (0 : ℝ) 1, ScalarTorusL2))
    (uT uS : C(Icc (0 : ℝ) 1, ScalarTorusL2))
    (ha : Tendsto a atTop (𝓝 uT)) (hb : Tendsto b atTop (𝓝 uS))
    (hfinite : ∀ N s,
      a N s = b N (classicalGalerkinNestedTimeMap T S hT hTS s)) :
    ∀ s, uT s = uS (classicalGalerkinNestedTimeMap T S hT hTS s) := by
  exact classicalGalerkinLimitPath_eq_under_timeMap a b uT uS ha hb
    (classicalGalerkinNestedTimeMap T S hT hTS) hfinite

end AVenhance.Infra.Classical

end
