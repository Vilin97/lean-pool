/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSolution.Definitions

/-! # Gradient Estimates

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff NNReal Topology

noncomputable section

namespace AVenhance.FaaDiBruno

/-- Along a flow characteristic, the spatial derivative of a smooth transport
solution solves the differentiated transport equation as a linear-map ODE. -/
theorem transportSolution_spatialGradient_hasDerivAt_alongFlow
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) :
    HasDerivAt
      (fun r => spatialDerivativeCLM (Function.uncurry Y) r (X r x s))
      (spatialDerivativeCLM (Function.uncurry g) t (X t x s) -
        (spatialDerivativeCLM (Function.uncurry Y) t (X t x s)).comp
          (spatialDerivativeCLM (Function.uncurry b) t (X t x s))) t := by
  let F : ℝ × Vec 2 → Vec 2 := Function.uncurry Y
  let G : ℝ × Vec 2 → Vec 2 := Function.uncurry g
  let B : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  let L : Vec 2 →L[ℝ] ℝ × Vec 2 := ContinuousLinearMap.inr ℝ ℝ (Vec 2)
  let ψ : ((ℝ × Vec 2) →L[ℝ] Vec 2) →L[ℝ] (Vec 2 →L[ℝ] Vec 2) :=
    (ContinuousLinearMap.compL ℝ (Vec 2) (ℝ × Vec 2) (Vec 2)).flip L
  let DF : ℝ × Vec 2 → (ℝ × Vec 2) →L[ℝ] Vec 2 := fun q => fderiv ℝ F q
  let A : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun q => (DF q).comp L
  let γ : ℝ → ℝ × Vec 2 := fun r => (r, X r x s)
  have hDF : ContDiff ℝ ∞ DF := by
    dsimp [DF, F]
    exact hY.smooth.fderiv_right (by simp)
  have hA : ContDiff ℝ ∞ A := by
    simpa [A, DF, ψ] using hDF.continuousLinearMap_comp ψ
  have hAderiv : HasFDerivAt A (ψ.comp (fderiv ℝ DF (t, X t x s)))
      (t, X t x s) := by
    have hψ : HasFDerivAt ψ ψ (DF (t, X t x s)) := ψ.hasFDerivAt
    have hDF' := (hDF.differentiable (by simp) (t, X t x s)).hasFDerivAt
    simpa [A, DF, ψ, Function.comp_def] using hψ.comp (t, X t x s) hDF'
  have hγ : HasDerivAt γ (1, b t (X t x s)) t := by
    exact (hasDerivAt_id t).prodMk (hX.2 x s t)
  have hchain := hAderiv.comp t hγ
  have hderiv_eq : fderiv ℝ A (t, X t x s) (1, b t (X t x s)) =
      spatialDerivativeCLM G t (X t x s) -
        (spatialDerivativeCLM F t (X t x s)).comp
          (spatialDerivativeCLM B t (X t x s)) := by
    apply ContinuousLinearMap.ext
    intro v
    have htransport := transportSolution_spatialDerivative_equation hY hb
      t (X t x s) v
    have hEval : (fderiv ℝ DF (t, X t x s) (1, b t (X t x s))) (0, v) =
        fderiv ℝ (fun q => DF q (0, v)) (t, X t x s)
          (1, b t (X t x s)) := by
      rw [fderiv_clm_apply
        (hDF.differentiable (by simp) (t, X t x s))
        (differentiableAt_const (0, v))]
      simp [fderiv_const_apply]
    rw [hAderiv.fderiv]
    change (ψ.comp (fderiv ℝ DF (t, X t x s)))
        (1, b t (X t x s)) v = _
    rw [show (ψ.comp (fderiv ℝ DF (t, X t x s)))
        (1, b t (X t x s)) v =
          (fderiv ℝ DF (t, X t x s) (1, b t (X t x s))) (0, v) by
            simp [ψ, L, ContinuousLinearMap.compL_apply]]
    rw [hEval]
    simpa [spatialDerivativeCLM, F, G, B, Function.uncurry,
      ContinuousLinearMap.comp_apply] using htransport
  have hpath : (fun r => spatialDerivativeCLM F r (X r x s)) = A ∘ γ := by
    funext r
    rfl
  have hderiv : HasDerivAt (A ∘ γ)
      (fderiv ℝ A (t, X t x s) (1, b t (X t x s))) t := by
    have h := hchain.hasDerivAt
    convert h using 1
    rw [hAderiv.fderiv]
    simp [ψ, L, ContinuousLinearMap.compL_apply]
  rw [hderiv_eq] at hderiv
  simpa [hpath, Function.comp_def, γ, F, G, B] using hderiv

/-- Grönwall bound for the differentiated transport solution along the
characteristic ending at an arbitrary point at time `t`. -/
theorem transportSolution_spatialGradient_norm_le_forward
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hLip : ∃ L : ℝ, ∀ r x z, ‖b r x - b r z‖ ≤ L * ‖x - z‖)
    {Lf Lg : ℝ}
    (hbD : ∀ r x, ‖spatialDerivativeCLM (Function.uncurry b) r x‖ ≤ Lf)
    (hgD : ∀ r x, ‖spatialDerivativeCLM (Function.uncurry g) r x‖ ≤ Lg)
    {t : ℝ} (ht : 0 ≤ t) (y : Vec 2) :
    ‖spatialDerivativeCLM (Function.uncurry Y) t y‖ ≤
      gronwallBound 0 Lf Lg t := by
  let x : Vec 2 := X 0 y t
  let J : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => spatialDerivativeCLM (Function.uncurry Y) r (X r x 0)
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => spatialDerivativeCLM (Function.uncurry b) r (X r x 0)
  let G : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => spatialDerivativeCLM (Function.uncurry g) r (X r x 0)
  have hJderiv (r : ℝ) : HasDerivAt J (G r - (J r).comp (A r)) r := by
    simpa [J, A, G] using
      transportSolution_spatialGradient_hasDerivAt_alongFlow hY hb hX x 0 r
  have hJcont : ContinuousOn J (Set.Icc 0 t) :=
    HasDerivAt.continuousOn (fun r _ => hJderiv r)
  have hJwithin : ∀ r ∈ Set.Ico 0 t,
      HasDerivWithinAt J (G r - (J r).comp (A r)) (Set.Ici r) r := by
    intro r hr
    exact (hJderiv r).hasDerivWithinAt
  have hinitial : J 0 = 0 := by
    dsimp [J]
    rw [spatialDerivativeCLM_eq_slice
      (hY.smooth.of_le (by norm_num : (1 : ℕ) ≤ ∞))]
    have hzero : (fun z : Vec 2 => Y 0 z) = fun _ => (0 : Vec 2) := by
      funext z
      exact hY.initial z
    change fderiv ℝ (fun z : Vec 2 => Y 0 z) (X 0 x 0) = 0
    rw [hzero]
    simp
  have hbound : ∀ r ∈ Set.Ico 0 t,
      ‖G r - (J r).comp (A r)‖ ≤ Lf * ‖J r‖ + Lg := by
    intro r hr
    calc
      ‖G r - (J r).comp (A r)‖ ≤ ‖G r‖ + ‖(J r).comp (A r)‖ := norm_sub_le _ _
      _ ≤ Lg + ‖J r‖ * Lf := by
        apply add_le_add (hgD r (X r x 0))
        exact (ContinuousLinearMap.opNorm_comp_le (J r) (A r)).trans
          (mul_le_mul_of_nonneg_left (hbD r (X r x 0)) (norm_nonneg _))
      _ = Lf * ‖J r‖ + Lg := by ring
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le
    (δ := 0) (K := Lf) (ε := Lg) (a := 0) (b := t)
    hJcont hJwithin (by rw [hinitial]; simp) hbound
  have hendpoint : X t (X 0 y t) 0 = y := by
    calc
      X t (X 0 y t) 0 = X t y t :=
        AVenhance.Infra.Flow.flow_group_law b hLip hX y t 0 t
      _ = y := hX.1 y t
  have hJt : J t = spatialDerivativeCLM (Function.uncurry Y) t y := by
    simp [J, x, hendpoint]
  simpa [hJt] using hgron t ⟨ht, le_rfl⟩

/-- The same endpoint derivative estimate for a characteristic traversed
backward from time zero. -/
theorem transportSolution_spatialGradient_norm_le_backward
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hLip : ∃ L : ℝ, ∀ r x z, ‖b r x - b r z‖ ≤ L * ‖x - z‖)
    {Lf Lg : ℝ}
    (hbD : ∀ r x, ‖spatialDerivativeCLM (Function.uncurry b) r x‖ ≤ Lf)
    (hgD : ∀ r x, ‖spatialDerivativeCLM (Function.uncurry g) r x‖ ≤ Lg)
    {t : ℝ} (ht : t ≤ 0) (y : Vec 2) :
    ‖spatialDerivativeCLM (Function.uncurry Y) t y‖ ≤
      gronwallBound 0 Lf Lg (-t) := by
  let x : Vec 2 := X 0 y t
  let τ : ℝ := -t
  let J : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => spatialDerivativeCLM (Function.uncurry Y) (-r) (X (-r) x 0)
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => spatialDerivativeCLM (Function.uncurry b) (-r) (X (-r) x 0)
  let G : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => spatialDerivativeCLM (Function.uncurry g) (-r) (X (-r) x 0)
  have hJderiv (r : ℝ) : HasDerivAt J (-(G r - (J r).comp (A r))) r := by
    have hbase := transportSolution_spatialGradient_hasDerivAt_alongFlow
      hY hb hX x 0 (0 - r)
    have hreverse := hbase.comp_const_sub 0 r
    simpa [J, A, G, Function.comp_def, zero_sub] using hreverse
  have hJcont : ContinuousOn J (Set.Icc 0 τ) :=
    HasDerivAt.continuousOn (fun r _ => hJderiv r)
  have hJwithin : ∀ r ∈ Set.Ico 0 τ,
      HasDerivWithinAt J (-(G r - (J r).comp (A r))) (Set.Ici r) r := by
    intro r hr
    exact (hJderiv r).hasDerivWithinAt
  have hinitial : J 0 = 0 := by
    dsimp [J]
    rw [spatialDerivativeCLM_eq_slice
      (hY.smooth.of_le (by norm_num : (1 : ℕ) ≤ ∞))]
    have hzero : (fun z : Vec 2 => Y 0 z) = fun _ => (0 : Vec 2) := by
      funext z
      exact hY.initial z
    simp only [neg_zero]
    change fderiv ℝ (fun z : Vec 2 => Y 0 z) (X 0 x 0) = 0
    rw [hzero]
    simp
  have hbound : ∀ r ∈ Set.Ico 0 τ,
      ‖-(G r - (J r).comp (A r))‖ ≤ Lf * ‖J r‖ + Lg := by
    intro r hr
    rw [norm_neg]
    calc
      ‖G r - (J r).comp (A r)‖ ≤ ‖G r‖ + ‖(J r).comp (A r)‖ := norm_sub_le _ _
      _ ≤ Lg + ‖J r‖ * Lf := by
        apply add_le_add (hgD (-r) (X (-r) x 0))
        exact (ContinuousLinearMap.opNorm_comp_le (J r) (A r)).trans
          (mul_le_mul_of_nonneg_left (hbD (-r) (X (-r) x 0)) (norm_nonneg _))
      _ = Lf * ‖J r‖ + Lg := by ring
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le
    (δ := 0) (K := Lf) (ε := Lg) (a := 0) (b := τ)
    hJcont hJwithin (by rw [hinitial]; simp) hbound
  have hendpoint : X t (X 0 y t) 0 = y := by
    calc
      X t (X 0 y t) 0 = X t y t :=
        AVenhance.Infra.Flow.flow_group_law b hLip hX y t 0 t
      _ = y := hX.1 y t
  have hJτ : J τ = spatialDerivativeCLM (Function.uncurry Y) t y := by
    simp [J, τ, x, hendpoint]
  have hτnonneg : 0 ≤ τ := by dsimp [τ]; linarith
  simpa [hJτ, τ] using hgron τ ⟨hτnonneg, le_rfl⟩

theorem GradientEstimates.gronwallBound_zero_le_two_mul_of_small
    {K ε t : ℝ} (hK : 0 < K) (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hsmall : K * t ≤ 1) :
    gronwallBound 0 K ε t ≤ 2 * ε * t := by
  have hz : 0 ≤ K * t := mul_nonneg hK.le ht
  have hzabs : |K * t| ≤ 1 := by
    rw [abs_of_nonneg hz]
    exact hsmall
  have hexp := Real.abs_exp_sub_one_le hzabs
  have hexpNonneg : 0 ≤ Real.exp (K * t) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp hz)
  have hdiff : Real.exp (K * t) - 1 ≤ 2 * (K * t) := by
    calc
      Real.exp (K * t) - 1 ≤ |Real.exp (K * t) - 1| := le_abs_self _
      _ ≤ 2 * |K * t| := hexp
      _ = 2 * (K * t) := by rw [abs_of_nonneg hz]
  rw [gronwallBound_of_K_ne_0 hK.ne']
  simp only [zero_mul, zero_add]
  have hratio : 0 ≤ ε / K := div_nonneg hε hK.le
  calc
    ε / K * (Real.exp (K * t) - 1) ≤ ε / K * (2 * (K * t)) :=
      mul_le_mul_of_nonneg_left hdiff hratio
    _ = 2 * ε * t := by field_simp [ne_of_gt hK]

theorem GradientEstimates.exists_spatial_lipschitz_of_fderiv_bound
    {b : ℝ → Vec 2 → Vec 2}
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ t x, ‖fderiv ℝ (b t) x‖ ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t x y, ‖b t x - b t y‖ ≤ K * ‖x - y‖ := by
  let K : ℝ≥0 := ⟨L, hL⟩
  have hFdiff : Differentiable ℝ (Function.uncurry b) :=
    hb.differentiable (by norm_num)
  have hsliceDiff (t : ℝ) : Differentiable ℝ (b t) := by
    have hpair : Differentiable ℝ (fun x : Vec 2 => (t, x)) := by fun_prop
    exact hFdiff.comp hpair
  have hD' (t : ℝ) (x : Vec 2) : ‖fderiv ℝ (b t) x‖₊ ≤ K := by
    exact_mod_cast hD t x
  have hLip (t : ℝ) : LipschitzWith K (b t) :=
    lipschitzWith_of_nnnorm_fderiv_le (hsliceDiff t) (hD' t)
  refine ⟨L, hL, ?_⟩
  intro t x y
  have h := (hLip t).dist_le_mul x y
  change dist (b t x) (b t y) ≤ (K : ℝ) * dist x y at h
  have hK : (K : ℝ) = L := rfl
  rw [hK] at h
  simpa [dist_eq_norm] using h

/-- The source seminorm at order one supplies the pointwise spatial
derivative bound used by the characteristic estimate. -/
theorem GradientEstimates.transportField_spatialDerivative_bound
    {b : ℝ → Vec 2 → Vec 2}
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    {C R : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hB : ∀ t, snorm (b t) 1 R ≤ ENNReal.ofReal C) :
    ∀ t x, ‖spatialDerivativeCLM (Function.uncurry b) t x‖ ≤ 2 * C * R / 4 := by
  intro t x
  rw [spatialDerivativeCLM_eq_slice (hb.of_le (by norm_num : (1 : ℕ) ≤ ∞))]
  have hslice : ContDiff ℝ 1 (b t) := by
    have hpair : ContDiff ℝ 1 (fun x : Vec 2 => (t, x)) := by fun_prop
    simpa [Function.uncurry, Function.comp_def] using
      (hb.of_le (by norm_num : (1 : ℕ) ≤ ∞)).comp hpair
  exact fderiv_norm_le_of_snorm_one_le (b t) hslice hR hC (hB t) x

/-- Equal-radius, order-one transport estimate for either sign of time. -/
theorem transportSolution_snorm_one_equalRadius
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {C_f C_g R : ℝ} (hCf : 0 < C_f) (hCg : 0 ≤ C_g) (hR : 0 < R)
    (hB : ∀ t, snorm (b t) 1 R ≤ ENNReal.ofReal C_f)
    (hG : ∀ t, snorm (g t) 1 R ≤ ENNReal.ofReal C_g)
    {t : ℝ} (hT : |t| ≤ 1 / (8 * C_f * R)) :
    snorm (Y t) 1 (R * (1 + 8 * |t| * C_f * R)) ≤
      ENNReal.ofReal (16 * C_g * |t|) := by
  let Lf : ℝ := 2 * C_f * R / 4
  let Lg : ℝ := 2 * C_g * R / 4
  have hLf : 0 < Lf := by dsimp [Lf]; positivity
  have hLg : 0 ≤ Lg := by dsimp [Lg]; positivity
  have hbD : ∀ r x, ‖spatialDerivativeCLM (Function.uncurry b) r x‖ ≤ Lf := by
    intro r x
    simpa [Lf] using
      GradientEstimates.transportField_spatialDerivative_bound hb hR hCf.le hB r x
  have hgD : ∀ r x, ‖spatialDerivativeCLM (Function.uncurry g) r x‖ ≤ Lg := by
    intro r x
    simpa [Lg] using
      GradientEstimates.transportField_spatialDerivative_bound hg hR hCg hG r x
  have hsliceD : ∀ r x, ‖fderiv ℝ (b r) x‖ ≤ Lf := by
    intro r x
    rw [← spatialDerivativeCLM_eq_slice
      (hb.of_le (by norm_num : (1 : ℕ) ≤ ∞))]
    exact hbD r x
  obtain ⟨K, hK, hLip⟩ :=
    GradientEstimates.exists_spatial_lipschitz_of_fderiv_bound hb hLf.le hsliceD
  have hsmall : Lf * |t| ≤ 1 := by
    have hprod : |t| * (8 * C_f * R) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 8 * C_f * R)).mp hT
    calc
      Lf * |t| = (1 / 16) * (|t| * (8 * C_f * R)) := by dsimp [Lf]; ring
      _ ≤ 1 / 16 := by
        simpa using mul_le_mul_of_nonneg_left hprod
          (by norm_num : 0 ≤ (1 / 16 : ℝ))
      _ ≤ 1 := by norm_num
  have hgrad : ∀ y,
      ‖spatialDerivativeCLM (Function.uncurry Y) t y‖ ≤ 2 * Lg * |t| := by
    intro y
    by_cases hsign : 0 ≤ t
    · have hchar := transportSolution_spatialGradient_norm_le_forward
        hY hb hX ⟨K, hLip⟩ hbD hgD (Lf := Lf) (Lg := Lg) hsign y
      have htime : |t| = t := abs_of_nonneg hsign
      rw [htime] at hsmall ⊢
      exact hchar.trans
        (GradientEstimates.gronwallBound_zero_le_two_mul_of_small hLf hLg hsign hsmall)
    · have hsign' : t ≤ 0 := le_of_not_ge hsign
      have hchar := transportSolution_spatialGradient_norm_le_backward
        hY hb hX ⟨K, hLip⟩ hbD hgD (Lf := Lf) (Lg := Lg) hsign' y
      have htime : |t| = -t := abs_of_nonpos hsign'
      rw [htime] at hsmall ⊢
      exact hchar.trans
        (GradientEstimates.gronwallBound_zero_le_two_mul_of_small hLf hLg (by linarith) hsmall)
  have hsliceY : ContDiff ℝ 1 (Y t) := by
    have hpair : ContDiff ℝ 1 (fun y : Vec 2 => (t, y)) := by fun_prop
    simpa [Function.uncurry, Function.comp_def] using
      (hY.smooth.of_le (by norm_num : (1 : ℕ) ≤ ∞)).comp hpair
  have hDslice : ∀ y, ‖fderiv ℝ (Y t) y‖ ≤ 2 * Lg * |t| := by
    intro y
    rw [← spatialDerivativeCLM_eq_slice
      (hY.smooth.of_le (by norm_num : (1 : ℕ) ≤ ∞))]
    exact hgrad y
  have hDsup := derivativeSup_one_le_of_fderiv_norm_le (Y t) hsliceY hDslice
  let RY : ℝ := R * (1 + 8 * |t| * C_f * R)
  have hRY : 0 < RY := by dsimp [RY]; positivity
  have hsnorm := snorm_one_le_of_derivativeSup_le (Y t) hRY hDsup
  have hfactor : 1 ≤ 1 + 8 * |t| * C_f * R := by
    have hnonneg : 0 ≤ |t| * C_f * R := by positivity
    nlinarith [hnonneg]
  have hRYlower : R ≤ RY := by
    dsimp [RY]
    calc
      R = R * 1 := by ring
      _ ≤ R * (1 + 8 * |t| * C_f * R) :=
        mul_le_mul_of_nonneg_left hfactor hR.le
  have hLgEq : 2 * Lg = C_g * R := by dsimp [Lg]; ring
  have hfinal : 4 * (2 * Lg * |t|) / RY ≤ 16 * C_g * |t| := by
    rw [div_le_iff₀ hRY]
    rw [hLgEq]
    have hprod : (C_g * |t|) * R ≤ (C_g * |t|) * RY :=
      mul_le_mul_of_nonneg_left hRYlower (mul_nonneg hCg (abs_nonneg t))
    nlinarith [hprod]
  calc
    snorm (Y t) 1 RY ≤ ENNReal.ofReal (4 * (2 * Lg * |t|) / RY) := hsnorm
    _ ≤ ENNReal.ofReal (16 * C_g * |t|) := ENNReal.ofReal_le_ofReal hfinal

end AVenhance.FaaDiBruno

end
