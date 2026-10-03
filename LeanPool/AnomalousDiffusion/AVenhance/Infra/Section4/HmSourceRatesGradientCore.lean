/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebraDefs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsL2Ioi
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HmBaseFluxIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordDiffusion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.DmPulledGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.AppB2Smoothness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2JointInduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46FluxFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialPrimitive
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFlowSupport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsPointwise

/-! Pointwise calculus for the spacetime gradient of the averaged pulled
temperature gradient. -/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff
namespace AVenhance.Infra.Section4

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.RelativeError

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- A convex average of the differentiated pulled gradients is controlled by
the Hessian and gradient of the temperature, provided the active flow
Jacobians and their first spatial derivatives have the indicated bounds. -/
theorem gradMatrix_Gbar_entry_abs_le_of_active_flow_bounds
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ ∞ (T t))
    {E : ℝ} (hE : 0 < E)
    (hFlow : ∀ l : ℤ, I.hatXiML m l t ≠ 0 → ∀ x i j,
      |I.flowGrad hΦ m l t x i j| ≤ 2)
    (hInv : ∀ l : ℤ, I.hatXiML m l t ≠ 0 → ∀ x i j,
      |gradMatrix (fun y => I.xFlowInv hΦ m l t y) x i j| ≤ 2)
    (hHess : ∀ l : ℤ, I.hatXiML m l t ≠ 0 → ∀ x p j q,
      |xFlowHess I hΦ m l t x p j q| ≤ 2 ^ 16 / E)
    (x : Vec 2) (i j : Fin 2) :
    |gradMatrix (Gbar I hΦ m T t) x i j| ≤
      4 * (Real.sqrt (vecNormSq
          (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x)) +
        Real.sqrt (vecNormSq
          (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x))) +
      2 ^ 19 / E * Real.sqrt (vecNormSq (spaceGrad (T t) x)) := by
  classical
  let S := (I.hatXiML_support_finite hm t).toFinset
  have hbar (y : Vec 2) : Gbar I hΦ m T t y =
      ∑ l ∈ S, I.hatXiML m l t • G I hΦ m T l t y :=
    Gbar_eq_finite_support I hΦ m hm T t y
  have hweightSum : (∑ l ∈ S, I.hatXiML m l t) = 1 := by
    have hfinite : (∑ l ∈ S, I.hatXiML m l t) = ∑' l : ℤ, I.hatXiML m l t := by
      symm
      apply tsum_eq_sum
      intro l hl
      have hz : I.hatXiML m l t = 0 := by
        by_contra hn
        exact hl ((I.hatXiML_support_finite hm t).mem_toFinset.mpr hn)
      simp [hz]
    rw [hfinite]
    exact Infra.Ingredients.hatXiML_partition I hm t
  have hweightNonneg (l : ℤ) (hl : l ∈ S) : 0 ≤ I.hatXiML m l t :=
    (Infra.Ingredients.hatXiML_mem_Icc I hm l t).1
  have hG (l : ℤ) : ContDiff ℝ ∞ (G I hΦ m T l t) :=
    contDiff_G I hΦ m T l hTt
  have hGbarFun : (fun y : Vec 2 => Gbar I hΦ m T t y j) =
      fun y => ∑ l ∈ S, I.hatXiML m l t * G I hΦ m T l t y j := by
    funext y
    rw [hbar]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hGderiv (l : ℤ) : HasFDerivAt
      (fun y : Vec 2 => G I hΦ m T l t y j)
      (fderiv ℝ (fun y : Vec 2 => G I hΦ m T l t y j) x) x :=
    ((contDiff_apply ℝ ℝ j).comp (hG l)).differentiable (by simp) x |>.hasFDerivAt
  have hsumDeriv : HasFDerivAt
      (fun y : Vec 2 => ∑ l ∈ S, I.hatXiML m l t * G I hΦ m T l t y j)
      (∑ l ∈ S, I.hatXiML m l t •
        fderiv ℝ (fun y : Vec 2 => G I hΦ m T l t y j) x) x := by
    have hsum : HasFDerivAt
        (∑ l ∈ S, (fun y : Vec 2 => I.hatXiML m l t * G I hΦ m T l t y j))
        (∑ l ∈ S, I.hatXiML m l t •
          fderiv ℝ (fun y : Vec 2 => G I hΦ m T l t y j) x) x :=
      HasFDerivAt.sum fun l hl =>
        (hGderiv l).const_mul (I.hatXiML m l t)
    convert hsum using 1
    · funext y
      simp
  have hgradbar : gradMatrix (Gbar I hΦ m T t) x i j =
      ∑ l ∈ S, I.hatXiML m l t *
        spaceGrad (fun y => G I hΦ m T l t y j) x i := by
    change spaceGrad (fun y => Gbar I hΦ m T t y j) x i = _
    rw [hGbarFun, spaceGrad]
    rw [hsumDeriv.fderiv]
    rw [sum_apply]
    apply Finset.sum_congr rfl
    intro l hl
    change I.hatXiML m l t *
      fderiv ℝ (fun y => G I hΦ m T l t y j) x (basisVec i) = _
    rw [spaceGrad]
  have hterm (l : ℤ) (hl : l ∈ S) :
      |spaceGrad (fun y => G I hΦ m T l t y j) x i| ≤
        4 * (Real.sqrt (vecNormSq
            (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x)) +
          Real.sqrt (vecNormSq
            (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x))) +
        2 ^ 19 / E * Real.sqrt (vecNormSq (spaceGrad (T t) x)) := by
    have hactive : I.hatXiML m l t ≠ 0 :=
      (I.hatXiML_support_finite hm t).mem_toFinset.mp hl
    rw [spaceGrad_G_component I hΦ m T l hTt x i j]
    have hFlow' := hFlow l hactive x
    have hInv' := hInv l hactive x
    have hHess' := hHess l hactive (I.xFlowInv hΦ m l t x)
    have hgrad (p : Fin 2) :
        |spaceGrad (T t) x p| ≤ Real.sqrt (vecNormSq (spaceGrad (T t) x)) :=
      abs_apply_le_sqrt_vecNormSq _ p
    have hhess (p : Fin 2) :
        |spaceHess (T t) x i p| ≤ Real.sqrt (vecNormSq
          (spaceGrad (Infra.Section4.iterateSpatialWord [p] (T t)) x)) := by
      exact abs_apply_le_sqrt_vecNormSq
        (spaceGrad (Infra.Section4.iterateSpatialWord [p] (T t)) x) i
    have hsumAbs :
        |∑ p : Fin 2,
          (I.flowGrad hΦ m l t x j p * spaceHess (T t) x i p +
            (∑ q : Fin 2,
              gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
                xFlowHess I hΦ m l t
                  (I.xFlowInv hΦ m l t x) p j q) * spaceGrad (T t) x p)| ≤
          4 * (Real.sqrt (vecNormSq
              (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x)) +
            Real.sqrt (vecNormSq
              (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x))) +
          2 ^ 19 / E * Real.sqrt (vecNormSq (spaceGrad (T t) x)) := by
      calc
        _ ≤ ∑ p : Fin 2,
            (|I.flowGrad hΦ m l t x j p * spaceHess (T t) x i p| +
              |(∑ q : Fin 2,
                gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
                  xFlowHess I hΦ m l t
                    (I.xFlowInv hΦ m l t x) p j q) * spaceGrad (T t) x p|) := by
          calc
            _ ≤ ∑ p : Fin 2,
                |I.flowGrad hΦ m l t x j p * spaceHess (T t) x i p +
                  (∑ q : Fin 2,
                    gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
                      xFlowHess I hΦ m l t
                        (I.xFlowInv hΦ m l t x) p j q) * spaceGrad (T t) x p| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ _ := Finset.sum_le_sum fun p _ => abs_add_le _ _
        _ ≤ ∑ p : Fin 2,
              (2 * Real.sqrt (vecNormSq
                (spaceGrad (Infra.Section4.iterateSpatialWord [p] (T t)) x)) +
                (2 ^ 18 / E) * Real.sqrt (vecNormSq (spaceGrad (T t) x))) := by
          apply Finset.sum_le_sum
          intro p hp
          have hfirst :
              |I.flowGrad hΦ m l t x j p * spaceHess (T t) x i p| ≤
                2 * Real.sqrt (vecNormSq
                  (spaceGrad (Infra.Section4.iterateSpatialWord [p] (T t)) x)) := by
            calc
              _ = |I.flowGrad hΦ m l t x j p| * |spaceHess (T t) x i p| := abs_mul _ _
              _ ≤ 2 * Real.sqrt (vecNormSq
                    (spaceGrad (Infra.Section4.iterateSpatialWord [p] (T t)) x)) :=
                mul_le_mul (hFlow' j p) (hhess p) (abs_nonneg _) (by positivity)
          have hinner :
              |∑ q : Fin 2,
                  gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
                    xFlowHess I hΦ m l t
                      (I.xFlowInv hΦ m l t x) p j q| ≤ 2 ^ 18 / E := by
            calc
              _ ≤ ∑ q : Fin 2,
                  |gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
                    xFlowHess I hΦ m l t
                      (I.xFlowInv hΦ m l t x) p j q| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ _q : Fin 2, 2 * (2 ^ 16 / E) := by
                apply Finset.sum_le_sum
                intro q hq
                rw [abs_mul]
                exact mul_le_mul (hInv' i q) (hHess' p j q)
                  (abs_nonneg _) (by positivity)
              _ = _ := by simp only [Fin.sum_univ_two]; ring
          have hsecond :
              |(∑ q : Fin 2,
                gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
                  xFlowHess I hΦ m l t
                    (I.xFlowInv hΦ m l t x) p j q) * spaceGrad (T t) x p| ≤
                (2 ^ 18 / E) * Real.sqrt (vecNormSq (spaceGrad (T t) x)) := by
            rw [abs_mul]
            exact mul_le_mul hinner (hgrad p) (abs_nonneg _) (by positivity)
          linarith
        _ = 2 * (Real.sqrt (vecNormSq
              (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x)) +
            Real.sqrt (vecNormSq
              (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x))) +
              2 * ((2 ^ 18 / E) * Real.sqrt (vecNormSq (spaceGrad (T t) x))) := by
          simp only [Fin.sum_univ_two]
          ring
        _ ≤ _ := by
          have h0 := Real.sqrt_nonneg (vecNormSq
            (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x))
          have h1 := Real.sqrt_nonneg (vecNormSq
            (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x))
          calc
            _ = 2 * (Real.sqrt (vecNormSq
                  (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x)) +
                Real.sqrt (vecNormSq
                  (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x))) +
                (2 ^ 19 / E) * Real.sqrt (vecNormSq (spaceGrad (T t) x)) := by ring
            _ ≤ _ := by nlinarith
    exact hsumAbs
  rw [hgradbar]
  calc
    |∑ l ∈ S, I.hatXiML m l t *
        spaceGrad (fun y => G I hΦ m T l t y j) x i| ≤
      ∑ l ∈ S, |I.hatXiML m l t *
        spaceGrad (fun y => G I hΦ m T l t y j) x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ S, I.hatXiML m l t *
        (4 * (Real.sqrt (vecNormSq
            (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T t)) x)) +
          Real.sqrt (vecNormSq
            (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T t)) x))) +
          2 ^ 19 / E * Real.sqrt (vecNormSq (spaceGrad (T t) x))) := by
      apply Finset.sum_le_sum
      intro l hl
      rw [abs_mul, abs_of_nonneg (hweightNonneg l hl)]
      exact mul_le_mul_of_nonneg_left (hterm l hl) (hweightNonneg l hl)
    _ = _ := by rw [← Finset.sum_mul, hweightSum, one_mul]

/-- The quantitative limit-field regularity package controls every flow factor on the support of
the large cutoff used in `Gbar`. -/
theorem HmSourceRatesGradientCore.iteratedFDeriv_component {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : Vec 2)
    (J : Fin n → Fin 2) (i : Fin 2) :
    iteratedFDeriv ℝ n (fun y : Vec 2 => f y i) x
        (fun k => basisVec (J k)) =
      iteratedFDeriv ℝ n f x (fun k => basisVec (J k)) i := by
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hcomp := P.iteratedFDeriv_comp_left
    (f := f) (x := x) hfN.contDiffAt (i := n) le_rfl
  change iteratedFDeriv ℝ n (P ∘ f) x
    (fun k => basisVec (J k)) = _
  rw [hcomp]
  rfl

theorem hm_Gbar_active_flow_bounds
    {Cmat Creg : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (hflow : FlowBoundsData I Φ hΦ Cmat)
    (hreg : StreamRegularityBounds Creg I Φ)
    {m : ℕ} (hm : 2 ≤ m) {t : ℝ}
    (l : ℤ) (hactive : I.hatXiML m l t ≠ 0) :
    (∀ x i j, |I.flowGrad hΦ m l t x i j| ≤ 2) ∧
    (∀ x i j,
      |gradMatrix (fun y => I.xFlowInv hΦ m l t y) x i j| ≤ 2) ∧
    (∀ x p j q, |xFlowHess I hΦ m l t x p j q| ≤
      2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹) := by
  have hm1 : 1 ≤ m := by omega
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he1 : epsilon β I.Λ (m - 1) ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hepow : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 :=
    Real.rpow_le_one he.le he1 (by positivity)
  have hwindow : |t - (l : ℝ) * tauPP β I.Λ m| ≤ tauPP β I.Λ m :=
    hatXiML_time_distance_le_tauPP I m hm1 l t hactive
  refine ⟨?_, ?_, ?_⟩
  · intro x i j
    have hc := flowGrad_entry_close_on_tauPP_window I Cmat hΦ hflow m hm l t x
      hwindow i j
    have hecpow : 0 ≤ (1 / 4 : ℝ) * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
      positivity
    by_cases hij : i = j
    · subst j
      have hc' : |I.flowGrad hΦ m l t x i i - 1| ≤
          (1 / 4 : ℝ) * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
        simpa [Matrix.sub_apply, Matrix.one_apply] using hc
      calc
            |I.flowGrad hΦ m l t x i i| =
            |(I.flowGrad hΦ m l t x i i - 1) + 1| := by congr 1; ring
        _ ≤ |I.flowGrad hΦ m l t x i i - 1| + 1 := by
          simpa using abs_add_le (I.flowGrad hΦ m l t x i i - 1) (1 : ℝ)
        _ ≤ (1 / 4 : ℝ) * epsilon β I.Λ (m - 1) ^ (2 * delta β) + 1 := by
          nlinarith only [hc']
        _ ≤ 2 := by nlinarith [hepow]
    · have hc' : |I.flowGrad hΦ m l t x i j| ≤
          (1 / 4 : ℝ) * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
        simpa [Matrix.sub_apply, Matrix.one_apply, hij] using hc
      exact hc'.trans (by nlinarith [hepow])
  · intro x i j
    have htime := Infra.Section4.hatXiML_active_time_window I hm1 l t hactive
    have hInv := amnr_xFlowInv_fderiv_norm_le_two_of_A3 I hΦ hreg hm1 l t x htime
    have hdiff : DifferentiableAt ℝ (I.xFlowInv hΦ m l t) x :=
      (xFlowInv_spatial_contDiff_two I hΦ m l t).differentiable (by norm_num) x
    have hentry :
        gradMatrix (fun y => I.xFlowInv hΦ m l t y) x i j =
          fderiv ℝ (I.xFlowInv hΦ m l t) x (basisVec i) j := by
      simp [gradMatrix, spaceGrad, fderiv_apply hdiff j]
    rw [hentry]
    calc
      |fderiv ℝ (I.xFlowInv hΦ m l t) x (basisVec i) j| ≤
          ‖fderiv ℝ (I.xFlowInv hΦ m l t) x (basisVec i)‖ := by
            calc
              _ = ‖fderiv ℝ (I.xFlowInv hΦ m l t) x (basisVec i) j‖ :=
                (Real.norm_eq_abs _).symm
              _ ≤ ‖fderiv ℝ (I.xFlowInv hΦ m l t) x (basisVec i)‖ := norm_le_pi_norm _ j
      _ ≤ ‖fderiv ℝ (I.xFlowInv hΦ m l t) x‖ * ‖basisVec i‖ :=
        (fderiv ℝ (I.xFlowInv hΦ m l t) x).le_opNorm _
      _ = ‖fderiv ℝ (I.xFlowInv hΦ m l t) x‖ := by simp [basisVec, Pi.norm_single]
      _ ≤ 2 := hInv
  · intro x p j q
    let s : ℝ := (l : ℝ) * tauPP β I.Λ m
    have hwindow' := iterate_hatXi_section2_window I hm1 hactive
    have hhigh := hflow.flow_higher_derivative (m - 1) (by omega) s (t - s)
      (by simpa [s] using hwindow') 2 (by norm_num) x ![q, j]
    have hX : (fun y => I.xFlow hΦ m l t y) = fun y =>
        constructionFlow hΦ (m - 1) (s + (t - s)) y s := by
      funext y
      change constructionFlow hΦ (m - 1) t y s =
        constructionFlow hΦ (m - 1) (s + (t - s)) y s
      ring_nf
    rw [← hX] at hhigh
    have hcoord :
        |iteratedFDeriv ℝ 2 (fun y => I.xFlow hΦ m l t y p) x
          (fun k => basisVec (![q, j] k))| ≤
          2 * (Nat.factorial 2 : ℝ) *
            (2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹) ^ (2 - 1) := by
      have hfun : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => I.xFlow hΦ m l t y) :=
        contDiff_xFlow_slice I hΦ m l t
      rw [HmSourceRatesGradientCore.iteratedFDeriv_component hfun 2 x (fun k => ![q, j] k) p]
      calc
        |((iteratedFDeriv ℝ 2 (fun y => I.xFlow hΦ m l t y) x
            (fun k => basisVec (![q, j] k))) p)| =
            ‖(iteratedFDeriv ℝ 2 (fun y => I.xFlow hΦ m l t y) x
              (fun k => basisVec (![q, j] k))) p‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖iteratedFDeriv ℝ 2 (fun y => I.xFlow hΦ m l t y) x
            (fun k => basisVec (![q, j] k))‖ := norm_le_pi_norm _ p
        _ ≤ _ := hhigh
    have h2 :
        2 * (Nat.factorial 2 : ℝ) *
          (2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹) ^ (2 - 1) =
          2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹ := by
      norm_num [Nat.factorial]
      ring
    have hxe := xFlowHess_eq_iteratedFDeriv hΦ m l t x p j q
    have hxe' : xFlowHess I hΦ m l t x p j q =
        iteratedFDeriv ℝ 2 (fun y => I.xFlow hΦ m l t y p) x
          (fun k => basisVec (![q, j] k)) := by
      rw [hxe]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hxe', ← h2]
    exact hcoord

end AVenhance.Infra.Section4

end
