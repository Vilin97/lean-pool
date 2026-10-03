/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.ThirdSpatialRemainder
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.ThirdVariationContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialRegularity
public import Mathlib.Analysis.Asymptotics.Basic

/-! Spatial C³ regularity of a smooth periodic flow. -/

@[expose] public section

open Homogenization
open Asymptotics
open Filter
open Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

/-- Continuous bilinear maps with values in the flow state space. -/
abbrev SpatialC3.FlowCML2 (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => E) E

/-- Continuous trilinear maps with values in the flow state space. -/
abbrev SpatialC3.FlowCML3 (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin 3 => E) E

/-- Bilinear maps represented as nested continuous linear maps. -/
abbrev SpatialC3.FlowNestedBilinear (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :=
  E →L[𝕜] (E →L[𝕜] E)

/-- The normed bilinear-map space, written as nested continuous linear maps in the
second-variation API. -/
noncomputable def SpatialC3.flowCML2NestedEquiv {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] :
    SpatialC3.FlowCML2 𝕜 E ≃L[𝕜] SpatialC3.FlowNestedBilinear 𝕜 E :=
  (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin 2 => E) E).toContinuousLinearEquiv.trans
    ((ContinuousLinearEquiv.refl 𝕜 E).arrowCongr
      (continuousMultilinearCurryFin1 𝕜 E E).toContinuousLinearEquiv)

theorem SpatialC3.flowCML2NestedEquiv_apply {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (A : SpatialC3.FlowCML2 𝕜 E) (h k : E) :
    SpatialC3.flowCML2NestedEquiv E A h k = A ![h, k] := by
  simp [SpatialC3.flowCML2NestedEquiv, continuousMultilinearCurryLeftEquiv_apply,
    continuousMultilinearCurryFin1_apply]

private theorem flow_spatial_contDiff_three_of_le_Bderiv1 :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b) {X : ℝ → Vec (2 : ℕ) → ℝ →
      Vec (2 : ℕ)}
    (hX : IsFlow b X) (s t : ℝ) (hst : s ≤ t),
    let f : Vec 2 → Vec 2 := fun x => X t x s;
    let J : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun x => fderiv ℝ f x;
    let B : Vec 2 → SpatialC3.FlowCML2 ℝ (Vec 2) :=
      fun x => (SpatialC3.flowCML2NestedEquiv (𝕜 := ℝ) (E := Vec 2)).symm (fderiv ℝ J x);
    let VAt : Vec 2 → ℝ → Vec 2 → ℝ → Vec 2 := fun x =>
      Classical.choose (existsUnique_flow_variationalEquation hb hX x s);
    ∀ (hVAt : ∀ (x : Vec (2 : ℕ)), IsFlow (linearizedFieldAlongFlow b X x s) (VAt x)),
      let Tnested : Vec 2 → Vec 2 →L[ℝ] SpatialC3.FlowNestedBilinear ℝ (Vec 2) := fun x =>
        Classical.choose (exists_flowThirdVariationContinuousTrilinear_of_le
          hb hX (V := VAt x) x s t hst (hVAt x));
      let T : Vec 2 → SpatialC3.FlowCML3 ℝ (Vec 2) := fun x =>
        ((SpatialC3.flowCML2NestedEquiv (𝕜 := ℝ) (E := Vec 2)).symm.toContinuousLinearMap.comp
          (Tnested x)).uncurryLeft;
      let C : Vec 2 → ℝ := fun x => Classical.choose
        (exists_flow_secondVariation_quadratic_remainder_all_times_of_le hb hX x s t hst);
      (∀ (x : Vec (2 : ℕ)), (0 : ℝ) ≤ C x) →
        (∀ (x u : Vec (2 : ℕ)),
            ‖B (x + u) - B x -
                  (ContinuousMultilinearMap.curryLeft (T x) : Vec (2 : ℕ) → Vec (2 : ℕ) [×(2 :
                      ℕ)]→L[ℝ] Vec (2 : ℕ)) u‖ ≤
              C x * ‖u‖ * ‖u‖) →
          ∀ (x : Vec (2 : ℕ)), HasFDerivAt B (ContinuousMultilinearMap.curryLeft (T x)) x
    := by
  intro b hb X hX s t hst f J B VAt hVAt Tnested T C hC₀ hBrem x
  have hnormLittle :
      (fun u : Vec 2 => ‖B (x + u) - B x - (T x).curryLeft u‖) =o[𝓝 0]
        fun u => ‖u‖ := by
    rw [isLittleO_iff]
    intro c hc
    have hcball : Metric.ball (0 : Vec 2) (c / (C x + 1)) ∈ 𝓝 (0 : Vec 2) :=
      Metric.ball_mem_nhds _ (div_pos hc (by linarith [hC₀ x]))
    filter_upwards [hcball] with u hu
    have hu' : ‖u‖ < c / (C x + 1) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hscaled' : ‖u‖ * (C x + 1) < c :=
      (lt_div_iff₀ (by linarith [hC₀ x])).mp hu'
    have hscaled : (C x + 1) * ‖u‖ ≤ c :=
      le_of_lt (by simpa [mul_comm] using hscaled')
    have hbnd : ‖B (x + u) - B x - (T x).curryLeft u‖ ≤ c * ‖u‖ := by
      calc
        ‖B (x + u) - B x - (T x).curryLeft u‖ ≤
            C x * ‖u‖ * ‖u‖ := hBrem x u
        _ ≤ c * ‖u‖ := by
          have hC : C x ≤ C x + 1 := by linarith [hC₀ x]
          calc
            C x * ‖u‖ * ‖u‖ = C x * (‖u‖ * ‖u‖) := by ring
            _ ≤ (C x + 1) * (‖u‖ * ‖u‖) :=
              mul_le_mul_of_nonneg_right hC
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            _ = ((C x + 1) * ‖u‖) * ‖u‖ := by ring
            _ ≤ c * ‖u‖ := mul_le_mul_of_nonneg_right hscaled (norm_nonneg _)
    change |‖B (x + u) - B x - (T x).curryLeft u‖| ≤ c * |‖u‖|
    simpa only [abs_of_nonneg (norm_nonneg _)] using hbnd
  have hLittle :
      (fun u : Vec 2 => B (x + u) - B x - (T x).curryLeft u) =o[𝓝 0]
      fun u => u := isLittleO_norm_norm.mp hnormLittle
  apply (hasFDerivAt_iff_isLittleO_nhds_zero).2
  exact hLittle

/-- On a forward interval, the selected third variation is the derivative of
the second spatial derivative, and the fixed-time flow is spatially C³. -/
theorem flow_spatial_contDiff_three_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) (hst : s ≤ t) :
    ContDiff ℝ 3 (fun x => X t x s) := by
  let f : Vec 2 → Vec 2 := fun x => X t x s
  let J : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun x => fderiv ℝ f x
  let B : Vec 2 → SpatialC3.FlowCML2 ℝ (Vec 2) :=
    fun x => (SpatialC3.flowCML2NestedEquiv (𝕜 := ℝ) (E := Vec 2)).symm (fderiv ℝ J x)
  let VAt : Vec 2 → ℝ → Vec 2 → ℝ → Vec 2 := fun x =>
    Classical.choose (existsUnique_flow_variationalEquation hb hX x s)
  have hVAt (x : Vec 2) :
      AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) (VAt x) :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
  let Tnested : Vec 2 → Vec 2 →L[ℝ] SpatialC3.FlowNestedBilinear ℝ (Vec 2) := fun x =>
    Classical.choose (exists_flowThirdVariationContinuousTrilinear_of_le
      hb hX (V := VAt x) x s t hst (hVAt x))
  let T : Vec 2 → SpatialC3.FlowCML3 ℝ (Vec 2) := fun x =>
    ((SpatialC3.flowCML2NestedEquiv (𝕜 := ℝ) (E := Vec 2)).symm.toContinuousLinearMap.comp
      (Tnested x)).uncurryLeft
  have hTnestedSpec (x u h k : Vec 2) :
      Tnested x u h k = flowThirdVariation hb hX x s (hVAt x) u h k t 0 s :=
    Classical.choose_spec (exists_flowThirdVariationContinuousTrilinear_of_le
      hb hX (V := VAt x) x s t hst (hVAt x)) u h k
  have hTspec (x u h k : Vec 2) :
      T x ![u, h, k] = flowThirdVariation hb hX x s (hVAt x) u h k t 0 s := by
    dsimp [T]
    rw [← SpatialC3.flowCML2NestedEquiv_apply (𝕜 := ℝ) (E := Vec 2)
      ((SpatialC3.flowCML2NestedEquiv (𝕜 := ℝ) (E := Vec 2)).symm (Tnested x u)) h k]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    exact hTnestedSpec x u h k
  let C : Vec 2 → ℝ := fun x => Classical.choose
    (exists_flow_secondVariation_quadratic_remainder_all_times_of_le hb hX x s t hst)
  have hC₀ (x : Vec 2) : 0 ≤ C x :=
    (Classical.choose_spec
      (exists_flow_secondVariation_quadratic_remainder_all_times_of_le hb hX x s t hst)).1
  have hTaylor (x u h k : Vec 2) (q : ℝ) (hq : q ∈ Icc s t) :
      ‖flowSecondVariation hb hX (x + u) s
          (Classical.choose_spec
            (existsUnique_flow_variationalEquation hb hX (x + u) s)).1 h k q 0 s -
        flowSecondVariation hb hX x s
          (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
          h k q 0 s -
        flowThirdVariation hb hX x s
          (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
          u h k q 0 s‖ ≤ C x * ‖u‖ * ‖u‖ * ‖h‖ * ‖k‖ :=
    (Classical.choose_spec
      (exists_flow_secondVariation_quadratic_remainder_all_times_of_le hb hX x s t hst)).2
      u h k q hq
  have hBeval (x h k : Vec 2) :
      B x ![h, k] = flowSecondVariation hb hX x s (hVAt x) h k t 0 s := by
    obtain ⟨_, _, Bx, hBx, hD⟩ :=
      exists_flow_spatialFDeriv_hasFDerivAt_of_le hb hX x s t hst
    have hEq : SpatialC3.flowCML2NestedEquiv (𝕜 := ℝ) (E := Vec 2) (B x) = Bx := by
      dsimp [B, J, f]
      rw [hD.fderiv]
      exact (SpatialC3.flowCML2NestedEquiv (𝕜 := ℝ) (E := Vec 2)).apply_symm_apply Bx
    calc
      B x ![h, k] = SpatialC3.flowCML2NestedEquiv (𝕜 := ℝ) (E := Vec 2) (B x) h k := by
        symm
        exact SpatialC3.flowCML2NestedEquiv_apply (𝕜 := ℝ) (E := Vec 2) (B x) h k
      _ = Bx h k := by rw [hEq]
      _ = flowSecondVariation hb hX x s (hVAt x) h k t 0 s := by
        have hVeq :
            (Classical.choose (existsUnique_flow_variationalEquation hb hX x s)) = VAt x := rfl
        simpa [hVeq] using hBx h k
  have hBrem (x u : Vec 2) :
      ‖B (x + u) - B x - (T x).curryLeft u‖ ≤ C x * ‖u‖ * ‖u‖ := by
    refine ContinuousMultilinearMap.opNorm_le_bound
      (f := B (x + u) - B x - (T x).curryLeft u)
      (M := C x * ‖u‖ * ‖u‖)
      (mul_nonneg (mul_nonneg (hC₀ x) (norm_nonneg u)) (norm_nonneg u)) ?_
    intro m
    let h := m 0
    let k := m 1
    have hm : m = ![h, k] := by
      ext i
      fin_cases i <;> simp [h, k]
    rw [hm]
    have hpoint := hTaylor x u h k t ⟨hst, le_rfl⟩
    have hpoint' :
        ‖B (x + u) ![h, k] - B x ![h, k] - T x ![u, h, k]‖ ≤
          C x * ‖u‖ * ‖u‖ * ‖h‖ * ‖k‖ := by
      rw [hBeval (x + u) h k, hBeval x h k, hTspec x u h k]
      exact hpoint
    calc
      ‖(B (x + u) - B x - (T x).curryLeft u) ![h, k]‖ =
          ‖B (x + u) ![h, k] - B x ![h, k] - T x ![u, h, k]‖ := by
            simp [ContinuousMultilinearMap.curryLeft_apply]
      _ ≤ C x * ‖u‖ * ‖u‖ * ‖h‖ * ‖k‖ := hpoint'
      _ = (C x * ‖u‖ * ‖u‖) * ∏ i : Fin 2, ‖![h, k] i‖ := by
        simp [Fin.prod_univ_succ]
        ring
  have hBderiv (x : Vec 2) : HasFDerivAt B ((T x).curryLeft) x := by
    exact @flow_spatial_contDiff_three_of_le_Bderiv1 b hb X hX s t hst hVAt hC₀ hBrem x
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨Cjac, hCjac₀, hCjac⟩ := exists_global_spatialFDeriv_lipschitz hb
  obtain ⟨C₂, hC₂₀, hC₂⟩ := exists_global_spatialSecondDerivativeEval_bound hb
  obtain ⟨C₂lip, hC₂lip₀, hC₂lip⟩ :=
    exists_global_spatialSecondDerivativeEval_lipschitz hb
  obtain ⟨C₃, hC₃₀, hC₃⟩ := exists_global_spatialThirdDerivativeEval_bound hb
  obtain ⟨C₄, hC₄₀, hC₄lip⟩ :=
    exists_global_spatialThirdDerivativeEval_lipschitz hb
  let K : ℝ := flowThirdVariationLipschitzConstant
    L M Cjac C₂ C₂lip C₃ C₄ s t
  have hK₀ : 0 ≤ K := by
    obtain ⟨Cxy, hCxy₀, hCxyEq, _⟩ :=
      exists_flow_thirdVariation_lipschitz_all_times_of_le hb hX
        L M Cjac C₂ C₂lip C₃ C₄
        hL₀ hM₀ hCjac₀ hC₂₀ hC₂lip₀ hC₃₀ hC₄₀
        hL hM hCjac hC₂ hC₂lip hC₃ hC₄lip 0 0 s t hst 0 0 0
    dsimp [K]
    rw [← hCxyEq]
    exact hCxy₀
  have hTlip (x y : Vec 2) : ‖T y - T x‖ ≤ K * ‖x - y‖ := by
    refine ContinuousMultilinearMap.opNorm_le_bound
      (f := T y - T x) (M := K * ‖x - y‖)
      (mul_nonneg hK₀ (norm_nonneg (x - y))) ?_
    intro m
    let u := m 0
    let h := m 1
    let k := m 2
    have hm : m = ![u, h, k] := by
      ext i
      fin_cases i <;> simp [u, h, k]
    obtain ⟨Cxy, _, hCxyEq, hpoint⟩ :=
      exists_flow_thirdVariation_lipschitz_all_times_of_le hb hX
        L M Cjac C₂ C₂lip C₃ C₄
        hL₀ hM₀ hCjac₀ hC₂₀ hC₂lip₀ hC₃₀ hC₄₀
        hL hM hCjac hC₂ hC₂lip hC₃ hC₄lip x y s t hst u h k
    have hpoint' := hpoint t ⟨hst, le_rfl⟩
    rw [hCxyEq] at hpoint'
    calc
      ‖(T y - T x) ![u, h, k]‖ =
          ‖flowThirdVariation hb hX y s (hVAt y) u h k t 0 s -
            flowThirdVariation hb hX x s (hVAt x) u h k t 0 s‖ := by
              change ‖T y ![u, h, k] - T x ![u, h, k]‖ = _
              rw [hTspec y u h k, hTspec x u h k]
      _ ≤ K * ‖x - y‖ * ‖u‖ * ‖h‖ * ‖k‖ := by
        simpa [K] using hpoint'
      _ = K * ‖x - y‖ * ∏ i : Fin 3, ‖![u, h, k] i‖ := by
        simp [Fin.prod_univ_succ]
        ring
  let KN : ℝ≥0 := ⟨K, hK₀⟩
  have hTLip : LipschitzWith KN T := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖T x - T y‖ = ‖T y - T x‖ := norm_sub_rev _ _
      _ ≤ K * ‖x - y‖ := hTlip x y
  have hTcont : Continuous T := hTLip.continuous
  have hTderivCont : Continuous (fun x => (T x).curryLeft) := by
    change Continuous
      (fun x => continuousMultilinearCurryLeftEquiv
        ℝ (fun _ : Fin 3 => Vec 2) (Vec 2) (T x))
    exact (continuousMultilinearCurryLeftEquiv
      ℝ (fun _ : Fin 3 => Vec 2) (Vec 2)).continuous.comp hTcont
  have hBcontDiff : ContDiff ℝ 1 B := by
    rw [contDiff_one_iff_hasFDerivAt]
    exact ⟨fun x => (T x).curryLeft, hTderivCont, hBderiv⟩
  let K : Vec 2 → SpatialC3.FlowNestedBilinear ℝ (Vec 2) :=
    fun x => SpatialC3.flowCML2NestedEquiv (𝕜 := ℝ) (E := Vec 2) (B x)
  have hKcontDiff : ContDiff ℝ 1 K := by
    exact (SpatialC3.flowCML2NestedEquiv (𝕜 := ℝ) (E := Vec 2)).contDiff.comp hBcontDiff
  have hJderiv (x : Vec 2) : HasFDerivAt J (K x) x := by
    obtain ⟨_, _, Bx, _, hD⟩ :=
      exists_flow_spatialFDeriv_hasFDerivAt_of_le hb hX x s t hst
    have hEq : K x = Bx := by
      dsimp [K, B, J, f]
      rw [hD.fderiv]
      exact (SpatialC3.flowCML2NestedEquiv (𝕜 := ℝ) (E := Vec 2)).apply_symm_apply Bx
    rw [hEq]
    simpa [J, f] using hD
  have hJcontDiff : ContDiff ℝ 2 J := by
    rw [show (2 : ℕ∞ω) = (1 : ℕ) + 1 by norm_num,
      contDiff_succ_iff_hasFDerivAt]
    exact ⟨K, hKcontDiff, hJderiv⟩
  have hfderiv (x : Vec 2) : HasFDerivAt f (J x) x := by
    obtain ⟨_, Jx, _, _, hD⟩ :=
      exists_flow_hasFDerivAt_spatial_of_le hb hX x s t hst
    have hEq : J x = Jx := by
      dsimp [J, f]
      exact hD.fderiv
    rw [hEq]
    exact hD
  rw [show (3 : ℕ∞ω) = (2 : ℕ) + 1 by norm_num,
    contDiff_succ_iff_hasFDerivAt]
  exact ⟨J, hJcontDiff, hfderiv⟩

/-- Every fixed-time map of a smooth flow is spatially C³. -/
theorem flow_spatial_contDiff_three
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) :
    ContDiff ℝ 3 (fun x => X t x s) := by
  by_cases hst : s ≤ t
  · exact flow_spatial_contDiff_three_of_le hb hX s t hst
  · have hts : t ≤ s := le_of_not_ge hst
    let br := regularityReverseTimeField b
    let Xr := regularityReverseTimeFlow X
    have hbr : SmoothPeriodicField br := smoothPeriodicField_regularityReverseTime hb
    have hXr : AVenhance.IsFlow br Xr := isFlow_regularityReverseTime hX
    have hforward : -s ≤ -t := by linarith
    have hC3 := flow_spatial_contDiff_three_of_le hbr hXr (-s) (-t) hforward
    simpa [Xr, regularityReverseTimeFlow] using hC3

end AVenhance.Infra.Flow
