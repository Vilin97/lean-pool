/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowTimeGevrey

@[expose] public section

/-! Frequency arithmetic for the genuine graph-flow estimates. Fixed
source constants affect only the frequency threshold. The power losses
can be made arbitrarily small, independently of any truncation order. -/

noncomputable section


namespace EulerPacketGraphFlowFrequency

open Filter Real EulerSmoothFlowGevrey

def inputExponent (ε : ℝ) : ℝ := min (ε/6) (1/4)

theorem inputExponent_pos (ε : ℝ) (hε : 0 < ε) : 0 < inputExponent ε := by
  unfold inputExponent
  positivity

theorem inputExponent_le_quarter (ε : ℝ) : inputExponent ε ≤ 1/4 := min_le_right _ _

theorem six_inputExponent_le (ε : ℝ) : 6*inputExponent ε ≤ ε := by
  have h := min_le_left (ε/6) (1/4 : ℝ)
  dsimp [inputExponent]
  linarith

private theorem flow_radius_polynomial (B R T w : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hT : 0 ≤ T) (hw : 71 ≤ w)
    (hRw : R ≤ w) (hTw : T ≤ w) (hsmall : B*w ≤ 1) :
    1+flowRadius B R T R ≤ w^3 ∧ 1+flowRadius B R T (6*R) ≤ w^3 := by
  have hw0 : 0 ≤ w := by linarith
  have hBT : B*T ≤ 1 := (mul_le_mul_of_nonneg_left hTw hB).trans hsmall
  have hleft : 4*R+1 ≤ 5*w := by linarith
  have hright : (1+B*T)*(6*R)+2 ≤ 14*w := by
    have h := mul_le_mul_of_nonneg_right (show 1+B*T ≤ 2 by linarith) (by positivity : 0 ≤ 6*R)
    nlinarith
  have hlarge : flowRadius B R T (6*R) ≤ 70*w^2 := by
    have h := mul_le_mul hleft hright (by positivity : 0 ≤ (1+B*T)*(6*R)+2) (by positivity : 0 ≤
      5*w)
    simpa only [flowRadius] using h.trans_eq (by ring)
  have hsmallR : flowRadius B R T R ≤ flowRadius B R T (6*R) := by
    unfold flowRadius
    gcongr
    nlinarith
  have hsq : 1 ≤ w^2 := by nlinarith
  have h71 : 71*w^2 ≤ w^3 := by
    have h := mul_le_mul_of_nonneg_right hw (sq_nonneg w)
    nlinarith
  have hb : 1+flowRadius B R T (6*R) ≤ w^3 := by nlinarith
  exact ⟨(add_le_add le_rfl hsmallR).trans hb,hb⟩

private theorem physical_polynomial_bounds (K B R T C1 k ell w : ℝ)
    (_hK : 0 ≤ K) (hB : 0 ≤ B) (hR : 0 ≤ R) (hT : 0 ≤ T) (hC1 : 0 ≤ C1)
    (hk : 1 ≤ k) (hell : 0 < ell) (hw : 71 ≤ w)
    (hKw : K ≤ w) (hRw : R ≤ w) (hTw : T ≤ w) (hCw : C1 ≤ w)
    (hsmall : B*w ≤ 1) :
    K*(T*B)*(1+flowRadius B R T R) ≤ B*w^5 ∧
    K*B*(1+flowRadius B R T R) ≤ B*w^5 ∧
    K*(C1+3*B^2*R)*(1+flowRadius B R T (6*R)) ≤ w^6 ∧
    ell⁻¹*(4*flowRadius B R T R*(1+k)) ≤ ell⁻¹*k*w^4 ∧
    ell⁻¹*(4*flowRadius B R T (6*R)*(1+k)) ≤ ell⁻¹*k*w^4 := by
  have hw0 : 0 ≤ w := by linarith
  have hB1 : B ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ w by linarith) hB
    nlinarith
  have hBT : 0 ≤ T*B := mul_nonneg hT hB
  obtain ⟨hv,ha⟩ := flow_radius_polynomial B R T w hB hR hT hw hRw hTw hsmall
  have hVr : 0 ≤ flowRadius B R T R := by unfold flowRadius; positivity
  have hAr : 0 ≤ flowRadius B R T (6*R) := by unfold flowRadius; positivity
  have hd : K*(T*B)*(1+flowRadius B R T R) ≤ B*w^5 := by
    calc
      _ ≤ w*(w*B)*w^3 := by gcongr
      _ = _ := by ring
  have hvb : K*B*(1+flowRadius B R T R) ≤ B*w^5 := by
    calc
      _ ≤ w*B*w^3 := by gcongr
      _ ≤ (w*B*w^3)*w := le_mul_of_one_le_right (by positivity) (by linarith)
      _ = _ := by ring
  have hb2 : B^2 ≤ 1 := by nlinarith
  have hac : C1+3*B^2*R ≤ 4*w := by
    have h := mul_le_mul_of_nonneg_right hb2 hR
    nlinarith
  have hab : K*(C1+3*B^2*R)*(1+flowRadius B R T (6*R)) ≤ w^6 := by
    calc
      _ ≤ w*(4*w)*w^3 := by gcongr
      _ = 4*w^5 := by ring
      _ ≤ w*w^5 := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hw0 5)
      _ = _ := by ring
  have hradius (r : ℝ) (hr : 0 ≤ r) (hrw : 1+r ≤ w^3) :
      ell⁻¹*(4*r*(1+k)) ≤ ell⁻¹*k*w^4 := by
    have hk0 : 0 ≤ k := by linarith
    have hi : 0 ≤ ell⁻¹ := inv_nonneg.mpr hell.le
    have hrw' : r ≤ w^3 := by linarith
    calc
      _ ≤ ell⁻¹*(4*w^3*(2*k)) := by gcongr; linarith
      _ = ell⁻¹*k*(8*w^3) := by ring
      _ ≤ ell⁻¹*k*(w*w^3) := by gcongr; linarith
      _ = _ := by ring
  exact ⟨hd,hvb,hab,hradius _ hVr hv,hradius _ hAr ha⟩

theorem physical_bounds_of_power (ε η K k B R T C1 ell : ℝ)
    (hη : 0 < η) (_hηq : η ≤ 1/4) (hηε : 6*η ≤ ε)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hR : 0 ≤ R) (hT : 0 ≤ T) (hC1 : 0 ≤ C1)
    (hk : 1 ≤ k) (hell : 0 < ell)
    (hw : 71 ≤ k^η) (hKw : K ≤ k^η) (hRw : R ≤ k^η)
    (hTw : T ≤ k^η) (hCw : C1 ≤ k^η)
    (hroot : 2 ≤ k^(1/2-η)) (hsmall : B ≤ 2*k^(-(1/2 : ℝ))) :
    K*(T*B)*(1+flowRadius B R T R) ≤ k^(-(1/2 : ℝ)+ε) ∧
    K*B*(1+flowRadius B R T R) ≤ k^(-(1/2 : ℝ)+ε) ∧
    K*(C1+3*B^2*R)*(1+flowRadius B R T (6*R)) ≤ k^ε ∧
    ell⁻¹*(4*flowRadius B R T R*(1+k)) ≤ ell⁻¹*k^(1+ε) ∧
    ell⁻¹*(4*flowRadius B R T (6*R)*(1+k)) ≤ ell⁻¹*k^(1+ε) := by
  have hk0 : 0 < k := by linarith
  have hw0 : 0 ≤ k^η := Real.rpow_nonneg hk0.le _
  have hBw : B*k^η ≤ 1 := by
    have hp : 0 < k^(1/2-η) := Real.rpow_pos_of_pos hk0 _
    calc
      _ ≤ (2*k^(-(1/2 : ℝ)))*k^η := mul_le_mul_of_nonneg_right hsmall hw0
      _ = 2/k^(1/2-η) := by
        rw [mul_assoc, ← Real.rpow_add hk0]
        have he : -(1/2 : ℝ)+η = -(1/2-η) := by ring
        rw [he, Real.rpow_neg hk0.le]
        ring
      _ ≤ 1 := (div_le_one hp).mpr hroot
  obtain ⟨hd,hv,ha,hr,hr1⟩ := physical_polynomial_bounds K B R T C1 k ell (k^η)
    hK hB hR hT hC1 hk hell hw hKw hRw hTw hCw hBw
  have h6 : (k^η)^6 ≤ k^ε := by
    rw [← Real.rpow_mul_natCast hk0.le]
    exact Real.rpow_le_rpow_of_exponent_le hk (by norm_num; nlinarith)
  have hdisp : B*(k^η)^5 ≤ k^(-(1/2 : ℝ)+ε) := by
    calc
      _ ≤ (2*k^(-(1/2 : ℝ)))*(k^η)^5 :=
        mul_le_mul_of_nonneg_right hsmall (pow_nonneg hw0 5)
      _ ≤ (k^η*k^(-(1/2 : ℝ)))*(k^η)^5 := by gcongr; linarith
      _ = k^(-(1/2 : ℝ))*(k^η)^6 := by ring
      _ ≤ k^(-(1/2 : ℝ))*k^ε := mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg hk0.le _)
      _ = _ := (Real.rpow_add hk0 _ _).symm
  have hrad : ell⁻¹*k*(k^η)^4 ≤ ell⁻¹*k^(1+ε) := by
    have h4 : (k^η)^4 ≤ k^ε := by
      rw [← Real.rpow_mul_natCast hk0.le]
      exact Real.rpow_le_rpow_of_exponent_le hk (by norm_num; nlinarith)
    calc
      _ ≤ ell⁻¹*k*k^ε := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = ell⁻¹*(k^(1 : ℝ)*k^ε) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hk0]
  exact ⟨hd.trans hdisp,hv.trans hdisp,ha.trans h6,hr.trans hrad,hr1.trans hrad⟩

theorem physical_bounds_eventually (ε K : ℝ) (hε : 0 < ε) (hK : 0 ≤ K) :
    ∀ᶠ k : ℝ in atTop, ∀ B R T C1 ell : ℝ,
      0 ≤ B → 0 ≤ R → 0 ≤ T → 0 ≤ C1 → 0 < ell →
      R ≤ k^(inputExponent ε) → T ≤ k^(inputExponent ε) → C1 ≤ k^(inputExponent ε) →
      B ≤ 2*k^(-(1/2 : ℝ)) →
      K*(T*B)*(1+flowRadius B R T R) ≤ k^(-(1/2 : ℝ)+ε) ∧
      K*B*(1+flowRadius B R T R) ≤ k^(-(1/2 : ℝ)+ε) ∧
      K*(C1+3*B^2*R)*(1+flowRadius B R T (6*R)) ≤ k^ε ∧
      ell⁻¹*(4*flowRadius B R T R*(1+k)) ≤ ell⁻¹*k^(1+ε) ∧
      ell⁻¹*(4*flowRadius B R T (6*R)*(1+k)) ≤ ell⁻¹*k^(1+ε) := by
  have hη := inputExponent_pos ε hε
  have hηq := inputExponent_le_quarter ε
  have hroot : 0 < 1/2-inputExponent ε := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (_root_.tendsto_rpow_atTop hη).eventually_ge_atTop 71,
    (_root_.tendsto_rpow_atTop hη).eventually_ge_atTop K,
    (_root_.tendsto_rpow_atTop hroot).eventually_ge_atTop 2] with k hk hw hKw hr
  intro B R T C1 ell hB hR hT hC1 hell hRw hTw hCw hsmall
  exact physical_bounds_of_power ε (inputExponent ε) K k B R T C1 ell
    hη hηq (six_inputExponent_le ε) hK hB hR hT hC1 hk hell hw hKw hRw hTw hCw hr hsmall

end EulerPacketGraphFlowFrequency
