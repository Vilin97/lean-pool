/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.HigherVariation3.Multilinear

/-! # Growth

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

theorem Growth.gronwallBound_zero_scale_third (L a c d : ℝ) :
    gronwallBound 0 L (c * a) d = c * gronwallBound 0 L a d := by
  by_cases hL : L = 0
  · simp [gronwallBound, hL]
    ring
  · simp [gronwallBound, hL]
    ring

/-- The uniform growth constant for the third variation on `[s,t]`. -/
noncomputable def flowThirdVariationGrowthConstant
    (M C₂ C₃ s t : ℝ) : ℝ :=
  let d := t - s
  let E := Real.exp (M * d)
  let K₂ := gronwallBound 0 M (C₂ * E * E) d
  let Cforce := C₃ * E * E * E + C₂ * K₂ * E +
    C₂ * K₂ * E + C₂ * K₂ * E
  gronwallBound 0 M Cforce d

/-- The third variation has a uniform trilinear growth bound on forward
compact time intervals. -/
theorem flowThirdVariation_bound_all_times_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s t : ℝ) (hst : s ≤ t)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (M C₂ C₃ : ℝ) (hM₀ : 0 ≤ M) (hM : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    (hC₂₀ : 0 ≤ C₂)
    (hC₂ : ∀ t x h k, ‖spatialSecondDerivativeEval b t x h k‖ ≤ C₂ * ‖h‖ * ‖k‖)
    (hC₃₀ : 0 ≤ C₃)
    (hC₃ : ∀ t x h k l,
      ‖spatialThirdDerivativeEval b t x h k l‖ ≤ C₃ * ‖h‖ * ‖k‖ * ‖l‖) :
    ∃ K : ℝ, 0 ≤ K ∧ K = flowThirdVariationGrowthConstant M C₂ C₃ s t ∧
      ∀ h k l q, q ∈ Icc s t →
      ‖flowThirdVariation hb hX x s hV h k l q 0 s‖ ≤
        K * ‖h‖ * ‖k‖ * ‖l‖ := by
  obtain ⟨K₂, hK₂₀, hK₂Formula, hW₂⟩ := flowSecondVariation_bound_all_times_of_le
    hb hX M C₂ hM₀ hM hC₂₀ hC₂ x s t hst hV
  let d : ℝ := t - s
  let E : ℝ := Real.exp (M * d)
  let Cforce : ℝ := C₃ * E * E * E + C₂ * K₂ * E +
    C₂ * K₂ * E + C₂ * K₂ * E
  let K : ℝ := gronwallBound 0 M Cforce d
  have hd₀ : 0 ≤ d := by dsimp [d]; linarith
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hCforce₀ : 0 ≤ Cforce := by dsimp [Cforce]; positivity
  have hK₀ : 0 ≤ K := by
    have hmono := gronwallBound_mono
      (show 0 ≤ (0 : ℝ) by norm_num) hCforce₀ hM₀
    simpa [K, gronwallBound_x0] using hmono hd₀
  refine ⟨K, hK₀, ?_, ?_⟩
  · dsimp [K, flowThirdVariationGrowthConstant, Cforce, E, d]
    rw [hK₂Formula]
  intro h k l q hq
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun q => jointSpatialFDeriv b q (X q x s)
  have hAL : ∀ q u v, ‖A q u - A q v‖ ≤ M * ‖u - v‖ := by
    intro q u v
    calc
      ‖A q u - A q v‖ = ‖A q (u - v)‖ := by rw [map_sub]
      _ ≤ ‖A q‖ * ‖u - v‖ := (A q).le_opNorm _
      _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right
        (hM q (X q x s)) (norm_nonneg _)
  have hVzero (q : ℝ) : V q 0 s = 0 := linearSystemFlow_zero A M hAL hV s q
  have hVbound (v : Vec 2) (q : ℝ) (hq : q ∈ Ico s t) :
      ‖V q v s‖ ≤ E * ‖v‖ := by
    have hgr := flow_spatial_gronwall (fun r z => A r z) hAL hV v 0 s q
    have hexp : Real.exp (M * |q - s|) ≤ E := by
      apply Real.exp_le_exp.mpr
      calc
        M * |q - s| = M * (q - s) := by
          rw [abs_of_nonneg (sub_nonneg.mpr hq.1)]
        _ ≤ M * d := mul_le_mul_of_nonneg_left (by dsimp [d]; linarith [hq.2]) hM₀
    calc
      ‖V q v s‖ = ‖V q v s - V q 0 s‖ := by rw [hVzero q, sub_zero]
      _ ≤ Real.exp (M * |q - s|) * ‖v - 0‖ := hgr
      _ = Real.exp (M * |q - s|) * ‖v‖ := by simp
      _ ≤ E * ‖v‖ := mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  let W₂hk := flowSecondVariation hb hX x s hV h k
  let W₂hl := flowSecondVariation hb hX x s hV h l
  let W₂kl := flowSecondVariation hb hX x s hV k l
  have hW₂bound (u v : Vec 2) (q : ℝ) (hq : q ∈ Icc s t) :
      ‖flowSecondVariation hb hX x s hV u v q 0 s‖ ≤ K₂ * ‖u‖ * ‖v‖ :=
    hW₂ q hq u v
  let F : ℝ → Vec 2 := fun q =>
    spatialThirdDerivativeEval b q (X q x s) (V q h s) (V q k s) (V q l s) +
      spatialSecondDerivativeEval b q (X q x s) (W₂hk q 0 s) (V q l s) +
      spatialSecondDerivativeEval b q (X q x s) (W₂hl q 0 s) (V q k s) +
      spatialSecondDerivativeEval b q (X q x s) (W₂kl q 0 s) (V q h s)
  let P : ℝ := ‖h‖ * ‖k‖ * ‖l‖
  let ε : ℝ := Cforce * P
  have hFbound (q : ℝ) (hq : q ∈ Ico s t) : ‖F q‖ ≤ ε := by
    let a := spatialThirdDerivativeEval b q (X q x s)
      (V q h s) (V q k s) (V q l s)
    let c := spatialSecondDerivativeEval b q (X q x s) (W₂hk q 0 s) (V q l s)
    let e := spatialSecondDerivativeEval b q (X q x s) (W₂hl q 0 s) (V q k s)
    let g := spatialSecondDerivativeEval b q (X q x s) (W₂kl q 0 s) (V q h s)
    have ha : ‖a‖ ≤ C₃ * E * E * E * P := by
      calc
        ‖a‖ ≤ C₃ * ‖V q h s‖ * ‖V q k s‖ * ‖V q l s‖ :=
          hC₃ q (X q x s) (V q h s) (V q k s) (V q l s)
        _ ≤ C₃ * (E * ‖h‖) * (E * ‖k‖) * (E * ‖l‖) := by
          have h1 := mul_le_mul_of_nonneg_left (hVbound h q hq) hC₃₀
          calc
            _ ≤ (C₃ * (E * ‖h‖)) * ‖V q k s‖ * ‖V q l s‖ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) (norm_nonneg _)
            _ ≤ (C₃ * (E * ‖h‖)) * (E * ‖k‖) * ‖V q l s‖ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hVbound k q hq)
                  (mul_nonneg hC₃₀ (mul_nonneg hE₀ (norm_nonneg _))))
                (norm_nonneg _)
            _ ≤ C₃ * (E * ‖h‖) * (E * ‖k‖) * (E * ‖l‖) := by
              exact mul_le_mul_of_nonneg_left (hVbound l q hq)
                (mul_nonneg
                  (mul_nonneg hC₃₀ (mul_nonneg hE₀ (norm_nonneg _)))
                  (mul_nonneg hE₀ (norm_nonneg _)))
        _ = C₃ * E * E * E * P := by dsimp [P]; ring
    have hc : ‖c‖ ≤ C₂ * K₂ * E * P := by
      calc
        ‖c‖ ≤ C₂ * ‖W₂hk q 0 s‖ * ‖V q l s‖ :=
          hC₂ q (X q x s) (W₂hk q 0 s) (V q l s)
        _ ≤ C₂ * (K₂ * ‖h‖ * ‖k‖) * (E * ‖l‖) := by
          have hWscaled := mul_le_mul_of_nonneg_left
            (hW₂bound h k q ⟨hq.1, le_of_lt hq.2⟩) hC₂₀
          calc
            _ ≤ C₂ * (K₂ * ‖h‖ * ‖k‖) * ‖V q l s‖ :=
              mul_le_mul_of_nonneg_right hWscaled (norm_nonneg _)
            _ ≤ C₂ * (K₂ * ‖h‖ * ‖k‖) * (E * ‖l‖) :=
              mul_le_mul_of_nonneg_left (hVbound l q hq)
                (mul_nonneg hC₂₀
                  (mul_nonneg (mul_nonneg hK₂₀ (norm_nonneg h)) (norm_nonneg k)))
        _ = C₂ * K₂ * E * P := by dsimp [P]; ring
    have he : ‖e‖ ≤ C₂ * K₂ * E * P := by
      calc
        ‖e‖ ≤ C₂ * ‖W₂hl q 0 s‖ * ‖V q k s‖ :=
          hC₂ q (X q x s) (W₂hl q 0 s) (V q k s)
        _ ≤ C₂ * (K₂ * ‖h‖ * ‖l‖) * (E * ‖k‖) := by
          have hWscaled := mul_le_mul_of_nonneg_left
            (hW₂bound h l q ⟨hq.1, le_of_lt hq.2⟩) hC₂₀
          calc
            _ ≤ C₂ * (K₂ * ‖h‖ * ‖l‖) * ‖V q k s‖ :=
              mul_le_mul_of_nonneg_right hWscaled (norm_nonneg _)
            _ ≤ C₂ * (K₂ * ‖h‖ * ‖l‖) * (E * ‖k‖) :=
              mul_le_mul_of_nonneg_left (hVbound k q hq)
                (mul_nonneg hC₂₀
                  (mul_nonneg (mul_nonneg hK₂₀ (norm_nonneg h)) (norm_nonneg l)))
        _ = C₂ * K₂ * E * P := by dsimp [P]; ring
    have hg : ‖g‖ ≤ C₂ * K₂ * E * P := by
      calc
        ‖g‖ ≤ C₂ * ‖W₂kl q 0 s‖ * ‖V q h s‖ :=
          hC₂ q (X q x s) (W₂kl q 0 s) (V q h s)
        _ ≤ C₂ * (K₂ * ‖k‖ * ‖l‖) * (E * ‖h‖) := by
          have hWscaled := mul_le_mul_of_nonneg_left
            (hW₂bound k l q ⟨hq.1, le_of_lt hq.2⟩) hC₂₀
          calc
            _ ≤ C₂ * (K₂ * ‖k‖ * ‖l‖) * ‖V q h s‖ :=
              mul_le_mul_of_nonneg_right hWscaled (norm_nonneg _)
            _ ≤ C₂ * (K₂ * ‖k‖ * ‖l‖) * (E * ‖h‖) :=
              mul_le_mul_of_nonneg_left (hVbound h q hq)
                (mul_nonneg hC₂₀
                  (mul_nonneg (mul_nonneg hK₂₀ (norm_nonneg k)) (norm_nonneg l)))
        _ = C₂ * K₂ * E * P := by dsimp [P]; ring
    have hsum3 : ‖a + c + e‖ ≤ ‖a‖ + ‖c‖ + ‖e‖ := by
      calc
        ‖(a + c) + e‖ ≤ ‖a + c‖ + ‖e‖ := norm_add_le _ _
        _ ≤ (‖a‖ + ‖c‖) + ‖e‖ := add_le_add (norm_add_le _ _) (le_rfl)
    calc
      ‖F q‖ = ‖a + c + e + g‖ := by rfl
      _ ≤ ‖a + c + e‖ + ‖g‖ := norm_add_le _ _
      _ ≤ ‖a‖ + ‖c‖ + ‖e‖ + ‖g‖ := add_le_add hsum3 (le_rfl)
      _ ≤ Cforce * P := by dsimp [Cforce]; linarith [ha, hc, he, hg]
      _ = ε := by rfl
  let W₃ := flowThirdVariation hb hX x s hV h k l
  have hW₃ := flowThirdVariation_isFlow hb hX x s hV h k l
  let f : ℝ → Vec 2 := fun _ => 0
  let g : ℝ → Vec 2 := fun q => W₃ q 0 s
  have hfderiv (q : ℝ) : HasDerivAt f (A q (f q)) q := by
    simpa [f] using (hasDerivAt_const q (0 : Vec 2))
  have hgderiv (q : ℝ) : HasDerivAt g (A q (g q) + F q) q := by
    simpa [g, W₃, F, A, W₂hk, W₂hl, W₂kl, add_assoc] using hW₃.2 0 s q
  have hfcont : ContinuousOn f (Icc s t) := continuousOn_const
  have hgcont : ContinuousOn g (Icc s t) :=
    HasDerivAt.continuousOn (fun q _ => hgderiv q)
  have hfwithin : ∀ q ∈ Ico s t,
      HasDerivWithinAt f (A q (f q)) (Ici q) q :=
    fun q _ => (hfderiv q).hasDerivWithinAt
  have hgwithin : ∀ q ∈ Ico s t,
      HasDerivWithinAt g (A q (g q) + F q) (Ici q) q :=
    fun q _ => (hgderiv q).hasDerivWithinAt
  have hfapprox : ∀ q ∈ Ico s t,
      dist (A q (f q)) (A q (f q)) ≤ (0 : ℝ) := by
    intro q hq
    simp
  have hgapprox : ∀ q ∈ Ico s t,
      dist (A q (g q) + F q) (A q (g q)) ≤ ε := by
    intro q hq
    rw [dist_eq_norm, add_sub_cancel_left]
    exact hFbound q hq
  let KN : ℝ≥0 := ⟨M, hM₀⟩
  have hAlip : ∀ q, LipschitzWith KN (fun z => A q z) := by
    intro q
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, dist_eq_norm]
    exact hAL q u v
  have hstart : dist (f s) (g s) ≤ (0 : ℝ) := by
    simp [f, g, W₃, hW₃.1]
  have hcomp := dist_le_of_approx_trajectories_ODE
    (K := KN) (v := fun q z => A q z) (a := s) (b := t)
    (εf := 0) (εg := ε) (δ := 0)
    hAlip hfcont hfwithin hfapprox hgcont hgwithin hgapprox hstart
  have hKcast : (KN : ℝ) = M := rfl
  have hmono := gronwallBound_mono
    (show 0 ≤ (0 : ℝ) by norm_num) hCforce₀ hM₀
  have hP₀ : 0 ≤ P := by dsimp [P]; positivity
  have hdist : ‖W₃ q 0 s‖ ≤ gronwallBound 0 M ε (q - s) := by
    have h := hcomp q hq
    simpa [f, g, dist_eq_norm, hKcast, zero_add, zero_sub, norm_neg] using h
  have htime : q - s ≤ d := by dsimp [d]; linarith [hq.2]
  have hscale : gronwallBound 0 M ε (q - s) =
      P * gronwallBound 0 M Cforce (q - s) := by
    rw [show ε = P * Cforce by dsimp [ε, P]; ring]
    rw [Growth.gronwallBound_zero_scale_third M Cforce P (q - s)]
  have hKbound : gronwallBound 0 M Cforce (q - s) ≤ K := by
    dsimp [K]
    exact hmono htime
  calc
    ‖flowThirdVariation hb hX x s hV h k l q 0 s‖ ≤
        gronwallBound 0 M ε (q - s) := by
          simpa [W₃] using hdist
    _ = P * gronwallBound 0 M Cforce (q - s) := hscale
    _ ≤ P * K := mul_le_mul_of_nonneg_left hKbound hP₀
    _ = K * ‖h‖ * ‖k‖ * ‖l‖ := by dsimp [P]; ring

/-- On a forward compact time interval, fixing the second and third
directions makes the third variation a continuous linear map in its
differentiating direction. -/
theorem exists_flowThirdVariationContinuousLinear_left_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s t : ℝ) (hst : s ≤ t)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
  (k l : Vec 2) :
    ∃ L : Vec 2 →L[ℝ] Vec 2, ∀ h,
      L h = flowThirdVariation hb hX x s hV h k l t 0 s := by
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨C₂, hC₂₀, hC₂⟩ := exists_global_spatialSecondDerivativeEval_bound hb
  obtain ⟨C₃, hC₃₀, hC₃⟩ := exists_global_spatialThirdDerivativeEval_bound hb
  obtain ⟨K, hK₀, _, hK⟩ := flowThirdVariation_bound_all_times_of_le
    hb hX x s t hst hV M C₂ C₃ hM₀ hM hC₂₀ hC₂ hC₃₀ hC₃
  let L : Vec 2 →ₗ[ℝ] Vec 2 :=
    { toFun := fun h => flowThirdVariation hb hX x s hV h k l t 0 s
      map_add' := by
        intro h₁ h₂
        exact flowThirdVariation_add_left hb hX x s hV h₁ h₂ k l t
      map_smul' := by
        intro c h
        exact flowThirdVariation_smul_left hb hX x s c hV h k l t }
  let C : ℝ := K * ‖k‖ * ‖l‖
  have hbound (h : Vec 2) : ‖L h‖ ≤ C * ‖h‖ := by
    calc
      ‖L h‖ = ‖flowThirdVariation hb hX x s hV h k l t 0 s‖ := by rfl
      _ ≤ K * ‖h‖ * ‖k‖ * ‖l‖ := hK h k l t ⟨hst, le_rfl⟩
      _ = C * ‖h‖ := by dsimp [C]; ring
  refine ⟨L.mkContinuous C hbound, ?_⟩
  intro h
  rfl

/-- On a forward compact time interval, the third variation is represented by
a continuous trilinear map in all three directions. -/
theorem exists_flowThirdVariationContinuousTrilinear_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s t : ℝ) (hst : s ≤ t)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V) :
    ∃ B : Vec 2 →L[ℝ] (Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2)), ∀ h k l,
      B h k l = flowThirdVariation hb hX x s hV h k l t 0 s := by
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨C₂, hC₂₀, hC₂⟩ := exists_global_spatialSecondDerivativeEval_bound hb
  obtain ⟨C₃, hC₃₀, hC₃⟩ := exists_global_spatialThirdDerivativeEval_bound hb
  obtain ⟨K, hK₀, _, hK⟩ := flowThirdVariation_bound_all_times_of_le
    hb hX x s t hst hV M C₂ C₃ hM₀ hM hC₂₀ hC₂ hC₃₀ hC₃
  let innerLinear (h k : Vec 2) : Vec 2 →ₗ[ℝ] Vec 2 :=
    { toFun := fun l => flowThirdVariation hb hX x s hV h k l t 0 s
      map_add' := by
        intro l₁ l₂
        exact flowThirdVariation_add_right hb hX x s hV h k l₁ l₂ t
      map_smul' := by
        intro c l
        exact flowThirdVariation_smul_right hb hX x s c hV h k l t }
  let innerContinuous (h k : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
    (innerLinear h k).mkContinuous (K * ‖h‖ * ‖k‖) (fun l => by
      change ‖flowThirdVariation hb hX x s hV h k l t 0 s‖ ≤
        (K * ‖h‖ * ‖k‖) * ‖l‖
      calc
        _ ≤ K * ‖h‖ * ‖k‖ * ‖l‖ := hK h k l t ⟨hst, le_rfl⟩
        _ = (K * ‖h‖ * ‖k‖) * ‖l‖ := by ring)
  let middleLinear (h : Vec 2) : Vec 2 →ₗ[ℝ] Vec 2 →L[ℝ] Vec 2 :=
    { toFun := innerContinuous h
      map_add' := by
        intro k₁ k₂
        ext l i
        exact congrArg (fun z : Vec 2 => z i)
          (flowThirdVariation_add_middle hb hX x s hV h k₁ k₂ l t)
      map_smul' := by
        intro c k
        ext l i
        exact congrArg (fun z : Vec 2 => z i)
          (flowThirdVariation_smul_middle hb hX x s c hV h k l t) }
  have hmiddleBound (h k : Vec 2) :
      ‖middleLinear h k‖ ≤ (K * ‖h‖) * ‖k‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg hK₀ (norm_nonneg h)) (norm_nonneg k))
    intro l
    calc
      ‖innerContinuous h k l‖ ≤ K * ‖h‖ * ‖k‖ * ‖l‖ := by
        change ‖flowThirdVariation hb hX x s hV h k l t 0 s‖ ≤ _
        exact hK h k l t ⟨hst, le_rfl⟩
      _ = (K * ‖h‖) * ‖k‖ * ‖l‖ := by ring
  let middleContinuous (h : Vec 2) : Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 :=
    (middleLinear h).mkContinuous (K * ‖h‖) (fun k => hmiddleBound h k)
  let outerLinear : Vec 2 →ₗ[ℝ] (Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2)) :=
    { toFun := middleContinuous
      map_add' := by
        intro h₁ h₂
        ext k l i
        exact congrArg (fun z : Vec 2 => z i)
          (flowThirdVariation_add_left hb hX x s hV h₁ h₂ k l t)
      map_smul' := by
        intro c h
        ext k l i
        exact congrArg (fun z : Vec 2 => z i)
          (flowThirdVariation_smul_left hb hX x s c hV h k l t) }
  have houterBound (h : Vec 2) : ‖outerLinear h‖ ≤ K * ‖h‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK₀ (norm_nonneg h))
    intro k
    change ‖middleContinuous h k‖ ≤ K * ‖h‖ * ‖k‖
    exact hmiddleBound h k
  let B : Vec 2 →L[ℝ] (Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2)) :=
    @LinearMap.mkContinuous ℝ ℝ (Vec 2)
      (Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (RingHom.id ℝ) outerLinear K houterBound
  refine ⟨B, ?_⟩
  intro h k l
  rfl

end AVenhance.Infra.Flow
