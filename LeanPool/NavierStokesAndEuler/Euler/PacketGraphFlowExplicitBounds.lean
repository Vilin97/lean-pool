/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceFrequency
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphFlowBounds
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyMargin
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowCoefficientPaths
import Mathlib.Analysis.Normed.Operator.Prod
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowTimeGevrey
import Mathlib.Algebra.Order.Star.Real

/-! The quarter-power physical-flow bounds follow from the same tiny-power
source comparison and one parent-independent numerical margin. -/

section

/-! Frequency arithmetic for the genuine graph-flow estimates. Fixed
source constants affect only the frequency threshold. The power losses
can be made arbitrarily small, independently of any truncation order. -/

@[expose] public section

noncomputable section

namespace EulerPacketGraphFlowFrequency

open Filter Real EulerSmoothFlowGevrey

/-- Input exponent, given by `min (ε/6) (1/4)`. -/
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
    (hRw : R ≤ w) (hTw : T ≤ w) (hsmall : B * w ≤ 1) :
    1+flowRadius B R T R ≤ w^3 ∧ 1+flowRadius B R T (6*R) ≤ w^3 := by
  have hw0 : 0 ≤ w := by linarith
  have hBT : B*T ≤ 1 := (mul_le_mul_of_nonneg_left hTw hB).trans hsmall
  have hleft : 4*R+1 ≤ 5*w := by linarith
  have hright : (1+B*T)*(6*R)+2 ≤ 14*w := by
    have h := mul_le_mul_of_nonneg_right (show 1+B*T ≤ 2 by linarith) (by positivity : 0 ≤ 6*R)
    nlinarith
  have hlarge : flowRadius B R T (6*R) ≤ 70*w^2 := by
    have h := mul_le_mul hleft hright (by
        positivity : 0 ≤ (1+B*T)*(6*R)+2) (by positivity : 0 ≤ 5*w)
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
    (hsmall : B * w ≤ 1) :
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
    (hη : 0 < η) (_hηq : η ≤ 1 / 4) (hηε : 6 * η ≤ ε)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hR : 0 ≤ R) (hT : 0 ≤ T) (hC1 : 0 ≤ C1)
    (hk : 1 ≤ k) (hell : 0 < ell)
    (hw : 71 ≤ k ^ η) (hKw : K ≤ k ^ η) (hRw : R ≤ k ^ η)
    (hTw : T ≤ k ^ η) (hCw : C1 ≤ k ^ η)
    (hroot : 2 ≤ k ^ (1 / 2 - η)) (hsmall : B ≤ 2 * k ^ (-(1 / 2 : ℝ))) :
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

end
end

end

section

/-! Uniform bounds needed for composition with the physical graph flow.
The small lifted displacement controls positive derivatives of the
physical coordinate change without a physical-frequency Grönwall bound. -/

@[expose] public section

noncomputable section

namespace EulerPhysicalGraphFlowBounds.Data

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerSmoothBanachFlow
  EulerSmoothFlowGevrey EulerGraphInvariantFlow EulerPhysicalGraphGevrey
  EulerCylinderGraphGevrey EulerGevrey
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (G : Data P T)

theorem displacement_sup_bound (k : ℝ) (m : Vector3) (ell : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (t : Icc (0 : ℝ) T) :
    HasSupBound (G.displacementField k m ell hell t).field (G.B*T)
      (ell⁻¹*(4*G.R*graphFactor k m)) := by
  intro n x
  apply physicalField_sup_bound P _ _ _ k m (T*G.C) G.velocityRadius
    (mul_nonneg G.time_nonneg G.C_nonneg) G.velocityRadius_nonneg _ _ ell hell hell1
    (fst ℝ Vector3 ℝ) (norm_fst_le ..) (G.B*T) (4*G.R)
  intro j z
  have he : (fun y => displacementFamily T G.time_nonneg G.A y t) =
      displacement T G.time_nonneg G.A t := by
    funext y
    simp only [displacement,EulerVolterraConvolution.extendPath,projIcc_of_mem G.time_nonneg
        t.property]
  rw [← he]
  exact displacementFamily_jet_bound T G.time_nonneg G.A G.B G.R G.B_nonneg G.R_pos G.small
    G.sup_bound j t z

theorem velocity_sup_bound (k : ℝ) (m : Vector3) (ell : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (t : Icc (0 : ℝ) T) :
    HasSupBound (G.velocityField k m ell hell t).field G.B
      (ell⁻¹*(flowRadius G.B G.R T G.R*graphFactor k m)) := by
  intro n x
  apply physicalField_sup_bound P _ _ _ k m G.C G.velocityRadius
    G.C_nonneg G.velocityRadius_nonneg _ _ ell hell hell1
    (fst ℝ Vector3 ℝ) (norm_fst_le ..) G.B (flowRadius G.B G.R T G.R)
  exact fun j z => materialVelocity_bound T G.time_nonneg G.A G.B G.R
    G.B_nonneg G.R_pos G.small G.sup_bound j t z

variable (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)

include hgraph in
theorem physical_positive_bound (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) (n : ℕ) (hn : 0 < n) (x : Vector3) :
    ‖iteratedFDeriv ℝ n ((flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t)
        x‖ ≤
      (1+G.B*T)*(1+ell⁻¹*(4*G.R*graphFactor k m))^n*(n.factorial : ℝ)^2 := by
  have he : (flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t =
      fun y => y+(G.displacementField k m ell hell t).field y := by
    funext y
    rw [G.displacementField_eq k m hgraph,displacement_eq]
    abel
  rw [he]
  exact positive_id_add_bound _ (G.displacementField k m ell hell t).smooth
    (G.B*T) (ell⁻¹*(4*G.R*graphFactor k m)) (mul_nonneg G.B_nonneg G.time_nonneg)
    (mul_nonneg (inv_nonneg.mpr hell.le)
      (mul_nonneg (by linarith [G.R_pos]) (graphFactor_nonneg k m)))
    (G.displacement_sup_bound k m ell hell hell1 t) n hn x

end EulerPhysicalGraphFlowBounds.Data

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketGraphFlowFrequency

open Real EulerSmoothFlowGevrey EulerPacketSourceFrequency

theorem physical_bounds_of_costs (K B R T C1 k ell : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hR : 0 ≤ R) (hT : 0 ≤ T) (hC1 : 0 ≤ C1)
    (hk : 1 ≤ k) (hell : 0 < ell)
    (hw : max 71 K ≤ k ^ (1 / 24 : ℝ)) (hroot : 16 ≤ k ^ (1 / 4 : ℝ))
    (hRk : R ≤ smallPower k) (hTk : T ≤ smallPower k) (hCk : C1 ≤ smallPower k)
    (hsmall : B ≤ 2 * k ^ (-(1 / 2 : ℝ))) :
    K*(T*B)*(1+flowRadius B R T R) ≤ k^(-(1/4 : ℝ)) ∧
    K*B*(1+flowRadius B R T R) ≤ k^(-(1/4 : ℝ)) ∧
    K*(C1+3*B^2*R)*(1+flowRadius B R T (6*R)) ≤ k^(1/4 : ℝ) ∧
    ell⁻¹*(4*flowRadius B R T R*(1+k)) ≤ ell⁻¹*k^(5/4 : ℝ) ∧
    ell⁻¹*(4*flowRadius B R T (6*R)*(1+k)) ≤ ell⁻¹*k^(5/4 : ℝ) := by
  have hs := smallPower_le_power k (1/24) hk (by norm_num [theta])
  have hr : 2 ≤ k^(1/2-(1/24 : ℝ)) :=
    (show 2 ≤ k^(1/4 : ℝ) by linarith).trans
      (Real.rpow_le_rpow_of_exponent_le hk (by norm_num))
  simpa only [show -(1/2 : ℝ)+1/4=-(1/4) by norm_num,
    show (1 : ℝ)+1/4=5/4 by norm_num] using
    physical_bounds_of_power (1/4) (1/24) K k B R T C1 ell
      (by norm_num) (by norm_num) (by norm_num) hK hB hR hT hC1 hk hell
      ((le_max_left _ _).trans hw) ((le_max_right _ _).trans hw)
      (hRk.trans hs) (hTk.trans hs) (hCk.trans hs) hr hsmall

end EulerPacketGraphFlowFrequency

namespace EulerPhysicalGraphFlowBounds

open Set Real EulerLiftedGradientSpace EulerSmoothFlowGevrey
  EulerPacketGraphFlowFrequency EulerPacketSourceFrequency EulerCylinderGraphGevrey
  EulerLpTranslation.SmoothL2Field EulerGevrey

variable (P T : ℝ) [Fact (0 < P)]

theorem data_field_bounds_explicit (G : Data P T) (k : ℝ)
    (hC : G.C = G.B) (hS : G.S = G.R) (hS1 : G.S₁ = G.R)
    (hk : 1 ≤ k) (hw : max 71 (Real.sqrt (2 / P + 2 * P)) ≤ k ^ (1 / 24 : ℝ))
    (hroot : 16 ≤ k ^ (1 / 4 : ℝ)) (hB : G.B ≤ 2 * k ^ (-(1 / 2 : ℝ)))
    (hR : G.R ≤ smallPower k) (hC1 : G.C₁ ≤ smallPower k) (hT : T ≤ smallPower k)
    (m : Vector3) (hm : ‖m‖ = 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) :
    (G.displacementField k m ell hell t).HasJetBound (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) ∧
    (G.velocityField k m ell hell t).HasJetBound (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) ∧
    (G.accelerationFieldL2 k m ell hell t).HasJetBound (k^(1/4 : ℝ)) (ell⁻¹*k^(5/4 : ℝ)) := by
  have hn := physical_bounds_of_costs (Real.sqrt (2/P+2*P)) G.B G.R T G.C₁ k ell
    (Real.sqrt_nonneg _) G.B_nonneg G.R_pos.le G.time_nonneg G.C₁_nonneg hk hell
    hw hroot hR hT hC1 hB
  have hvr : G.velocityRadius=flowRadius G.B G.R T G.R := by rw [Data.velocityRadius,hS]
  have har : G.accelerationRadius=flowRadius G.B G.R T (6*G.R) := by
    rw [Data.accelerationRadius,hS,hS1]
    congr 1
    ring
  have haa : G.accelerationAmplitude=G.C₁+3*G.B^2*G.R := by rw [Data.accelerationAmplitude,hC]; ring
  have hgf : graphFactor k m=1+k := by
    rw [graphFactor,hm,abs_of_nonneg (zero_le_one.trans hk),mul_one]
  have hv0 := G.velocityRadius_nonneg
  have ha0 := G.accelerationRadius_nonneg
  have hc0 := G.C_nonneg
  have ht0 := G.time_nonneg
  have hac0 := G.accelerationAmplitude_nonneg
  have hg0 := graphFactor_nonneg k m
  refine ⟨?_,?_,?_⟩
  · apply (G.displacementField_bound k m ell hell hell1 t).mono
    · positivity
    · positivity
    · simpa only [hC,hvr] using hn.1
    · simpa only [hvr,hgf] using hn.2.2.2.1
  · apply (G.velocityField_bound k m ell hell hell1 t).mono
    · positivity
    · positivity
    · simpa only [hC,hvr] using hn.2.1
    · simpa only [hvr,hgf] using hn.2.2.2.1
  · apply (G.accelerationField_bound k m ell hell hell1 t).mono
    · positivity
    · positivity
    · simpa only [haa,har] using hn.2.2.1
    · simpa only [har,hgf] using hn.2.2.2.2

theorem data_sup_bounds_explicit (G : Data P T) (k : ℝ)
    (hk : 1 ≤ k) (hw : 71 ≤ k ^ (1 / 24 : ℝ)) (hroot : 16 ≤ k ^ (1 / 4 : ℝ))
    (hB : G.B ≤ 2 * k ^ (-(1 / 2 : ℝ))) (hR : G.R ≤ smallPower k) (hT : T ≤ smallPower k)
    (m : Vector3) (hm : ‖m‖ = 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) :
    HasSupBound (G.displacementField k m ell hell t).field (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) ∧
    HasSupBound (G.velocityField k m ell hell t).field (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) := by
  have hk0 := zero_le_one.trans hk
  have hn := physical_bounds_of_costs 1 G.B G.R T 0 k ell zero_le_one
    G.B_nonneg G.R_pos.le G.time_nonneg le_rfl hk hell
    (by simpa only [max_eq_left (by norm_num : (1 : ℝ) ≤ 71)] using hw)
    hroot hR hT (Real.rpow_nonneg hk0 _) hB
  have hgf : graphFactor k m=1+k := by rw [graphFactor,hm,abs_of_nonneg hk0,mul_one]
  have hB0 := G.B_nonneg
  have hT0 := G.time_nonneg
  have hR0 := G.R_pos.le
  have hf0 : 0 ≤ flowRadius G.B G.R T G.R := by unfold flowRadius; positivity
  have hrad := hn.2.2.2.1
  have hg0 := graphFactor_nonneg k m
  have hdisp : G.B*T ≤ k^(-(1/4 : ℝ)) := by
    apply (show G.B*T ≤ T*G.B*(1+flowRadius G.B G.R T G.R) by
      nlinarith [mul_nonneg (mul_nonneg hB0 hT0) hf0]).trans
    simpa only [one_mul] using hn.1
  have hvel : G.B ≤ k^(-(1/4 : ℝ)) := by
    apply (show G.B ≤ G.B*(1+flowRadius G.B G.R T G.R) by nlinarith [mul_nonneg hB0 hf0]).trans
    simpa only [one_mul] using hn.2.1
  have hRflow : G.R ≤ flowRadius G.B G.R T G.R := by
    have hleft : (1 : ℝ) ≤ 4*G.R+1 := by linarith
    have hright : G.R ≤ (1+G.B*T)*G.R+2 := by nlinarith [mul_nonneg (mul_nonneg hB0 hT0) hR0]
    have h := mul_le_mul hleft hright hR0 (by positivity : 0 ≤ 4*G.R+1)
    simpa only [one_mul,flowRadius] using h
  constructor
  · apply (G.displacement_sup_bound k m ell hell hell1 t).mono (mul_nonneg hB0 hT0) (by
      positivity) hdisp
    rw [hgf]
    apply le_trans _ hrad
    gcongr
  · apply (G.velocity_sup_bound k m ell hell hell1 t).mono hB0 (by positivity) hvel
    rw [hgf]
    apply le_trans _ hrad
    gcongr
    nlinarith

end EulerPhysicalGraphFlowBounds
