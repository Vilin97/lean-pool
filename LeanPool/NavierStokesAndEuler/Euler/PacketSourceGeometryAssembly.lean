/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryData
import LeanPool.NavierStokesAndEuler.Euler.PacketCoefficientLipschitz
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryDynamics
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalSize
public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationLipschitz
public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationRay
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryUncut
public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
public import LeanPool.NavierStokesAndEuler.Euler.TransverseHistoryBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialGeometry
import LeanPool.NavierStokesAndEuler.Euler.TransverseHistoryLipschitz

/-! The actual source ray and selected primary satisfy every analytic
field of `PhysicalGeometryData`.  Neighbor errors follow from the source
coefficient derivatives and the genuine stationary-history estimate. -/

section

/-! The actual source normal and the same selected terminal coordinate
give the scaled neighboring-label initial errors.  Their constants only
involve coefficient norms, the terminal size, and the stated scaling. -/

section

/-!
The actual fixed-terminal history estimate controls the scaled neighbor
initial velocity.  The loss `ε⁻¹` comes from the specified coordinate
rescaling and is independent of the oscillation frequency.
-/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerVolterraConvolution EulerTimeH1FrameTransport
  EulerTransverseEndpointCoordinates EulerTransverseHistoryBounds

theorem frame_pair_difference_le {p q x y : Space} {ε D : ℝ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hxy : ‖x - y‖ ≤ D) :
    |⟪p,x⟫_ℝ/ε-⟪p,y⟫_ℝ/ε|+|⟪q,x⟫_ℝ-⟪q,y⟫_ℝ| ≤ 2*D/ε := by
  have hp' : |⟪p,x-y⟫_ℝ| ≤ ‖x-y‖ := by
    simpa only [hp, one_mul] using abs_real_inner_le_norm p (x-y)
  have hq' : |⟪q,x-y⟫_ℝ| ≤ ‖x-y‖ := by
    simpa only [hq, one_mul] using abs_real_inner_le_norm q (x-y)
  have hU : |⟪p,x⟫_ℝ/ε-⟪p,y⟫_ℝ/ε| ≤ ‖x-y‖/ε := by
    rw [← sub_div, ← inner_sub_right, abs_div, abs_of_pos hε]
    exact div_le_div_of_nonneg_right hp' hε.le
  have hV : |⟪q,x⟫_ℝ-⟪q,y⟫_ℝ| ≤ ‖x-y‖/ε := by
    rw [← inner_sub_right]
    apply hq'.trans
    apply (le_div_iff₀ hε).mpr
    exact mul_le_of_le_one_right (norm_nonneg _) hε1
  have hD := div_le_div_of_nonneg_right hxy hε.le
  calc
    _ ≤ D/ε+D/ε := add_le_add (hU.trans hD) (hV.trans hD)
    _ = 2*D/ε := by ring

theorem scaledVelocity_initial_difference_le {m v x y : ℝ → Space}
    {t₀ a ε D : ℝ} (hm0 : m t₀ ≠ 0) (hv0 : v t₀ ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hxy : ‖x t₀ - y t₀‖ ≤ D) :
    |scaledVelocity m v x t₀ a ε 0 0-scaledVelocity m v y t₀ a ε 0 0| +
      |scaledVelocity m v x t₀ a ε 0 1-scaledVelocity m v y t₀ a ε 0 1| ≤ 2*D/ε := by
  simpa [scaledVelocity, movingVelocity, physicalTime, normalizedFrame, frame,
    velocityScale, Fin.ext_iff] using
      frame_pair_difference_le (unit_norm hm0) (unit_norm hv0) hε hε1 hxy

theorem scaled_inner_difference_le {p x y : Space} {b D : ℝ}
    (hp : ‖p‖ = 1) (hb : 0 < b) (hxy : ‖x - y‖ ≤ D) :
    |⟪p,x⟫_ℝ/b-⟪p,y⟫_ℝ/b| ≤ D/b := by
  rw [← sub_div, ← inner_sub_right, abs_div, abs_of_pos hb]
  apply div_le_div_of_nonneg_right _ hb.le
  exact ((abs_real_inner_le_norm p (x-y)).trans_eq (by rw [hp, one_mul])).trans hxy

theorem scaledRay_initial_difference_le {m v x y : ℝ → Space} {s₀ t₀ a ε D : ℝ}
    (hs₀ : 0 < s₀) (hm0 : m t₀ ≠ 0) (hv0 : v t₀ ≠ 0) (hmv : ⟪m t₀, v t₀⟫_ℝ = 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hxy : ‖x t₀ - y t₀‖ ≤ D) :
    norm3 (scaledRay m v x s₀ t₀ a ε 0 0-scaledRay m v y s₀ t₀ a ε 0 0)
      (scaledRay m v x s₀ t₀ a ε 0 1-scaledRay m v y s₀ t₀ a ε 0 1)
      (scaledRay m v x s₀ t₀ a ε 0 2-scaledRay m v y s₀ t₀ a ε 0 2) ≤
        3*D/(s₀*ε) := by
  have hn := (frame_orthonormal (unit (m t₀)) (unit (v t₀))
    (unit_inner_self hm0) (unit_inner_self hv0) (unit_inner_zero hmv)).norm_eq_one 2
  have hpn := scaled_inner_difference_le (unit_norm hm0) hs₀ hxy
  have hqn := scaled_inner_difference_le (unit_norm hv0) (mul_pos hs₀ hε) hxy
  have hnn := scaled_inner_difference_le hn hs₀ hxy
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hxy
  have hden : D/s₀ ≤ D/(s₀*ε) := div_le_div_of_nonneg_left hD0 (mul_pos hs₀ hε)
    (mul_le_of_le_one_right hs₀.le hε1)
  have hall := add_le_add (add_le_add (hpn.trans hden) hqn) (hnn.trans hden)
  have hthree : D/(s₀*ε)+D/(s₀*ε)+D/(s₀*ε) = 3*D/(s₀*ε) := by ring
  rw [hthree] at hall
  simpa [norm3, scaledRay, movingRay, physicalTime, normalizedFrame, frame, rayScale,
    Fin.ext_iff] using hall

/-- A physical initial-ray error around the chosen normal becomes the
source's scaled ray error with the fixed factor `(s₀ ε)⁻¹`. -/
theorem scaledRay_initial_error {m v r : ℝ → Space} {s₀ t₀ a ε D : ℝ}
    (hs₀ : 0 < s₀) (hm0 : m t₀ ≠ 0) (hv0 : v t₀ ≠ 0) (hmv : ⟪m t₀, v t₀⟫_ℝ = 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hr : ‖r t₀ - s₀ • EulerPacketCrossProduct.cross (unit (m t₀)) (unit (v t₀))‖ ≤ D) :
    norm3 (scaledRay m v r s₀ t₀ a ε 0 0) (scaledRay m v r s₀ t₀ a ε 0 1)
      (scaledRay m v r s₀ t₀ a ε 0 2-1) ≤ 3*D/(s₀*ε) := by
  let r₀ : ℝ → Space := fun _ => s₀ • EulerPacketCrossProduct.cross (unit (m t₀)) (unit (v t₀))
  have hi : scaledRay m v r₀ s₀ t₀ a ε 0 = ![0,0,1] :=
    scaledRay_initial (ne_of_gt hs₀) hm0 hv0 hmv rfl
  have h := scaledRay_initial_difference_le (a := a) hs₀ hm0 hv0 hmv hε hε1 (y := r₀) hr
  simpa [hi] using h

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

omit [CompleteSpace U] in
theorem frame_pair_operator_difference_le {T ε D : ℝ}
    (A B : U →L[ℝ] C(Icc (0 : ℝ) T, Space)) (ξ : U) (t : Icc (0 : ℝ) T)
    {p q : Space} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hAB : ‖A - B‖ ≤ D) :
    |⟪p,A ξ t⟫_ℝ/ε-⟪p,B ξ t⟫_ℝ/ε|+|⟪q,A ξ t⟫_ℝ-⟪q,B ξ t⟫_ℝ| ≤
      2*D*‖ξ‖/ε := by
  have hn : ‖A ξ t-B ξ t‖ ≤ D*‖ξ‖ := by
    exact (((A-B) ξ).norm_coe_le_norm t).trans (((A-B).le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right hAB (norm_nonneg ξ)))
  simpa only [mul_assoc] using frame_pair_difference_le hp hq hε hε1 hn

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] Space))
  (H : C(Icc (0 : ℝ) T, Space →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t ξ, c * ‖ξ‖ ^ 2 ≤ ‖Q t ξ‖ ^ 2)
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K * ‖z‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
  (P P₁ : C(Icc (0 : ℝ) T, U →L[ℝ] Space))
  (G : C(Icc (0 : ℝ) T, Space →L[ℝ] Space))
  (hP : ∀ t ξ, c * ‖ξ‖ ^ 2 ≤ ‖P t ξ‖ ^ 2)
  (hp : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT P) (P₁ t) (Icc (0 : ℝ) T) t)
  (hG : ∀ t z, ⟪G t z, z⟫_ℝ ≤ K * ‖z‖ ^ 2)

/-- The two actual stationary histories use the same terminal coordinate
`ξ`; physical coefficient differences give the scaled initial error. -/
theorem history_scaled_pair_difference_le (hTpos : 0 < T) (q q₁ d a r : ℝ)
    (hQn : ‖Q‖ ≤ q) (hPn : ‖P‖ ≤ q) (hQ₁n : ‖Q₁‖ ≤ q₁) (hP₁n : ‖P₁‖ ≤ q₁)
    (hD : T * ‖Q₁‖ + ‖Q‖ ≤ d) (hD' : T * ‖P₁‖ + ‖P‖ ≤ d)
    (hA : 1 + T ^ 2 * ‖H‖ ≤ a) (hA' : 1 + T ^ 2 * ‖G‖ ≤ a)
    (hr : transportCost T Q Q₁ c ≤ r) (hr' : transportCost T P P₁ c ≤ r)
    (L₀ L₁ LH s : ℝ) (h₀ : ‖Q - P‖ ≤ L₀ * s) (h₁ : ‖Q₁ - P₁‖ ≤ L₁ * s) (hHdiff : ‖H - G‖ ≤ LH * s)
    (ξ : U) (t : Icc (0 : ℝ) T) {p₀ q₀ : Space} (hp₀ : ‖p₀‖ = 1) (hq₀ : ‖q₀‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let u := historyVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ t
    let v := historyVelocity T hT P P₁ G c hc hP hp K hK hG hsmall ξ t
    |⟪p₀,u⟫_ℝ/ε-⟪p₀,v⟫_ℝ/ε|+|⟪q₀,u⟫_ℝ-⟪q₀,v⟫_ℝ| ≤
      2*historyDifferenceCost T c q q₁ d a r L₀ L₁ LH*s*‖ξ‖/ε := by
  have hh := historyVelocity_sub_norm_le_of_coefficient_bounds T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    P P₁ G hP hp hG hTpos q q₁ d a r hQn hPn hQ₁n hP₁n hD hD' hA hA' hr hr'
    L₀ L₁ LH s h₀ h₁ hHdiff
  have h := frame_pair_operator_difference_le
    (historyVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall)
    (historyVelocity T hT P P₁ G c hc hP hp K hK hG hsmall) ξ t hp₀ hq₀ hε hε1 hh
  simpa only [mul_assoc] using h

end EulerPacketMovingFrame

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketCrossProduct
  EulerPacketPrimaryFactorization EulerPacketRay

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))

theorem uncutVelocity_activation_difference (ξ : U) (x y : Space) :
    ‖uncutVelocity τ hτ hτT B ξ τ x-uncutVelocity τ hτ hτT B ξ τ y‖ ≤
      historyLabelDifferenceCost B*‖x-y‖*‖ξ‖ := by
  have hx := uncutVelocity_history τ hτ hτT B ξ ⟨τ,hτ.le,le_rfl⟩ x
  have hy := uncutVelocity_history τ hτ hτT B ξ ⟨τ,hτ.le,le_rfl⟩ y
  change uncutVelocity τ hτ hτT B ξ τ x = _ at hx
  change uncutVelocity τ hτ hτT B ξ τ y = _ at hy
  rw [hx,hy]
  exact labelVelocity_point_difference B x y ξ ⟨τ,hτ.le,le_rfl⟩

theorem actual_scaled_velocity_initial_error
    (m v : ℝ → Space) (hm : m τ ≠ 0) (hv : v τ ≠ 0)
    (ξ : U) (a ε lam : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : scaledVelocity m v (fun s => uncutVelocity τ hτ hτT B ξ s 0) τ a ε 0 0 = -lam)
    (hw : scaledVelocity m v (fun s => uncutVelocity τ hτ hτT B ξ s 0) τ a ε 0 1 = 1)
    (x : Space) :
    |scaledVelocity m v (fun s => uncutVelocity τ hτ hτT B ξ s x) τ a ε 0 1-1| +
      |scaledVelocity m v (fun s => uncutVelocity τ hτ hτT B ξ s x) τ a ε 0 0+lam| ≤
      2*historyLabelDifferenceCost B*‖x‖*‖ξ‖/ε := by
  have hd := uncutVelocity_activation_difference τ hτ hτT B ξ x 0
  rw [sub_zero] at hd
  have he := scaledVelocity_initial_difference_le (m := m) (v := v)
    (x := fun s => uncutVelocity τ hτ hτT B ξ s x)
    (y := fun s => uncutVelocity τ hτ hτT B ξ s 0) (t₀ := τ) (a := a) (ε := ε)
    hm hv hε hε1 hd
  rw [hu,hw,sub_neg_eq_add] at he
  convert! he using 1 <;> ring

omit [CompleteSpace U] in
theorem actual_scaled_ray_initial_error
    (m v : ℝ → Space) (hm : m τ ≠ 0) (hv : v τ ≠ 0) (hmv : ⟪m τ, v τ⟫_ℝ = 0)
    (hchoice : D.m₀ = activationDirection (D.deformationEquiv ⟨τ, hτ.le, hτT.le⟩ 0)
      (cross (unit (m τ)) (unit (v τ))))
    (a ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (x : Space) :
    let s₀ := activationRayScale (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
      (cross (unit (m τ)) (unit (v τ)))
    norm3 (scaledRay m v (fun s => D.normal.field (D.clamp s) x) s₀ τ a ε 0 0)
      (scaledRay m v (fun s => D.normal.field (D.clamp s) x) s₀ τ a ε 0 1)
      (scaledRay m v (fun s => D.normal.field (D.clamp s) x) s₀ τ a ε 0 2-1) ≤
      3*‖D.normal.derivative.field‖*‖x‖/(s₀*ε) := by
  dsimp only
  have hs := actual_activation_scaled_ray D m v ⟨τ,hτ.le,hτT.le⟩ a ε hm hv hmv hchoice
  have hn := actual_normal_of_activation_choice D ⟨τ,hτ.le,hτT.le⟩ 0 _ hchoice
  have hd := coefficient_difference D.normal ⟨τ,hτ.le,hτT.le⟩ x 0
  rw [sub_zero,hn] at hd
  have hclamp : D.clamp τ = ⟨τ,hτ.le,hτT.le⟩ := Data.clamp_coe D ⟨τ,hτ.le,hτT.le⟩
  have hd' : ‖D.normal.field (D.clamp τ) x -
      activationRayScale (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
        (cross (unit (m τ)) (unit (v τ))) • cross (unit (m τ)) (unit (v τ))‖ ≤
      ‖D.normal.derivative.field‖*‖x‖ := by rw [hclamp]; exact hd
  convert! scaledRay_initial_error (m := m) (v := v)
    (r := fun s => D.normal.field (D.clamp s) x) (t₀ := τ) (a := a) (ε := ε)
    hs.1 hm hv hmv hε hε1 hd' using 1
  ring

end EulerPacketActivationHistory

end
end

end

section

/-! Exact scale normalization from the actual parent frame and shear.
The physical interval ends at the chosen scaled horizon; no extension
beyond the source time interval is required. -/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerPacketNormalizedPrimary EulerPacketCrossProduct

theorem activation_coupling_match (B : ℝ → Space →L[ℝ] Space)
    (m v : ℝ → Space) (t₀ ε : ℝ) :
    let a := normalizedCoupling (B t₀) (m t₀) (v t₀)
    rescaledFrame B m v t₀ a ε 0 0 1 = a := by
  simp [rescaledFrame,physicalTime,frameMatrix,frame,normalizedCoupling]

theorem activation_tilt_match (B : ℝ → Space →L[ℝ] Space)
    (m v : ℝ → Space) (t₀ ε : ℝ)
    (ha : normalizedCoupling (B t₀) (m t₀) (v t₀) ≠ 0)
    (hβ : 0 ≤ normalizedTilt (B t₀) (m t₀) (v t₀)) :
    let a := normalizedCoupling (B t₀) (m t₀) (v t₀)
    let σ := Real.sqrt (normalizedTilt (B t₀) (m t₀) (v t₀))
    rescaledFrame B m v t₀ a ε 0 2 1 = a*σ^2 := by
  dsimp only
  rw [Real.sq_sqrt hβ]
  simp only [rescaledFrame,physicalTime,mul_zero,add_zero,frameMatrix,frame,
    Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero,normalizedTilt]
  exact (mul_div_cancel₀ _ ha).symm

theorem activation_shear_match (c : ℝ) (m v : ℝ → Space) (t₀ a : ℝ)
    (ha : 0 < a) (hh : 0 < primaryShear c m v t₀) :
    let ε := Real.sqrt (a/primaryShear c m v t₀)
    0 < ε ∧ rescaledShear c m v t₀ a ε 0 = a/ε^2 := by
  dsimp only
  have hratio := div_pos ha hh
  refine ⟨Real.sqrt_pos.mpr hratio,?_⟩
  rw [Real.sq_sqrt hratio.le]
  simp only [rescaledShear,physicalTime,mul_zero,add_zero]
  field_simp

theorem activation_horizon_exact (t₀ T a ε : ℝ) (ha : a ≠ 0) (hε : ε ≠ 0) :
    physicalTime t₀ a ε (a*(T-t₀)/ε) = T := by
  unfold physicalTime
  field_simp
  ring

theorem activation_horizon_maps (t₀ T a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    MapsTo (physicalTime t₀ a ε) (Icc 0 (a*(T-t₀)/ε)) (Icc t₀ T) := by
  intro s hs
  constructor
  · change t₀ ≤ t₀+(ε/a)*s
    exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hε.le ha.le) hs.1)
  · calc
      physicalTime t₀ a ε s ≤ physicalTime t₀ a ε (a*(T-t₀)/ε) := by
        unfold physicalTime
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs.2 (div_nonneg hε.le ha.le))
      _ = T := activation_horizon_exact t₀ T a ε ha.ne' hε.ne'

end EulerPacketMovingFrame

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketSourceGeometry

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerPacketMovingFrame EulerPacketNormalizedPrimary
  EulerPacketCrossProduct EulerPacketActivationHistory EulerTransverseActivationSelection
  EulerPacketPrimaryFactorization EulerPacketRay EulerVolterraConvolution
  EulerTransverseSourceCoefficientPath

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Source matrix, given by `D.M.field (D.clamp t) x`. -/
def sourceMatrix (D : Data U) (x : Space) (t : ℝ) : Space →L[ℝ] Space := D.M.field (D.clamp t) x
/-- Source ray, given by `D.normal.field (D.clamp t) x`. -/
def sourceRay (D : Data U) (x : Space) (t : ℝ) : Space := D.normal.field (D.clamp t) x

theorem sourceMatrix_continuous (D : Data U) (x : Space) : Continuous (sourceMatrix D x) :=
  extendPath_continuous D.T D.T_pos.le (pathEvaluation x D.M.field)

variable [CompleteSpace U] {D : Data U} {τ : ℝ}
  {hτ : 0 < τ} {hτT : τ < D.T} {P : ParentFrame D τ}
  {H : HistoryData (D.initial τ hτ hτT.le)}

/-- Source error, given by `sourceMatrix D x t-P.B t-primaryShear P.c P.m P.v t • rankOne ℝ
(unit (P.v t)) (unit (P.m t))`. -/
def ParentFrame.sourceError (x : Space) (t : ℝ) : Space →L[ℝ] Space :=
  sourceMatrix D x t-P.B t-primaryShear P.c P.m P.v t • rankOne ℝ (unit (P.v t)) (unit (P.m t))

namespace Guards

variable (A : Guards hτ hτT P H)

/-- Source velocity, given by `uncutVelocity τ hτ hτT H A.terminal t x`. -/
def sourceVelocity (x : Space) (t : ℝ) : Space := uncutVelocity τ hτ hτT H A.terminal t x

omit [CompleteSpace U] in
include hτ in
theorem sourceRay_equation (x : Space) (t : ℝ) (ht : t ∈ Icc τ D.T) :
    HasDerivWithinAt (sourceRay D x) (-(sourceMatrix D x t).adjoint (sourceRay D x t))
      (Icc τ D.T) t := by
  have hsub : Icc τ D.T ⊆ Icc (0 : ℝ) D.T := fun _ hs => ⟨hτ.le.trans hs.1,hs.2⟩
  have hclamp : D.clamp t=⟨t,hsub ht⟩ := Data.clamp_coe D ⟨t,hsub ht⟩
  change HasDerivWithinAt (fun s => D.normal.field (D.clamp s) x)
    (-(D.M.field (D.clamp t) x).adjoint (D.normal.field (D.clamp t) x)) (Icc τ D.T) t
  rw [hclamp]
  exact (canonicalNormal_equation (D := D) ⟨t,hsub ht⟩ x).mono hsub

theorem sourceVelocity_equation (x : Space) (t : ℝ) (ht : t ∈ Icc τ D.T) :
    HasDerivWithinAt (A.sourceVelocity x)
      (-(sourceMatrix D x t) (A.sourceVelocity x t) +
        (2*⟪sourceRay D x t,(sourceMatrix D x t) (A.sourceVelocity x t)⟫_ℝ/
          ‖sourceRay D x t‖^2) • sourceRay D x t) (Icc τ D.T) t := by
  have hsub : Icc τ D.T ⊆ Icc (0 : ℝ) D.T := fun _ hs => ⟨hτ.le.trans hs.1,hs.2⟩
  have hclamp : D.clamp t=⟨t,hsub ht⟩ := Data.clamp_coe D ⟨t,hsub ht⟩
  unfold sourceVelocity sourceRay sourceMatrix
  rw [hclamp]
  have he := (uncutVelocity_equation τ hτ hτT H A.terminal ⟨t,hsub ht⟩ x).mono hsub
  rw [EulerPacketPrimaryFactorization.physicalGenerator_apply] at he
  exact he

theorem source_initial_tangent (x : Space) : ⟪sourceRay D x τ,A.sourceVelocity x τ⟫_ℝ=0 := by
  have hclamp : D.clamp τ=⟨τ,hτ.le,hτT.le⟩ := Data.clamp_coe D ⟨τ,hτ.le,hτT.le⟩
  simpa only [sourceRay,sourceVelocity,hclamp] using
    uncutVelocity_tangent τ hτ hτT H A.terminal ⟨τ,hτ.le,hτT.le⟩ x

theorem sourceVelocity_ne_zero (x : Space) (t : Icc (0 : ℝ) D.T) : A.sourceVelocity x t ≠ 0 :=
  uncutVelocity_ne_zero τ hτ hτT H A.terminal A.terminal_properties.1 t x

omit [CompleteSpace U] in
theorem neighbor_components :
    ‖D.M.derivative.field‖ ≤ P.neighborCost hτ hτT H A.CM A.CH ∧
      3*‖D.normal.derivative.field‖/(P.rayScale hτ hτT*P.epsilon) ≤
        P.neighborCost hτ hτT H A.CM A.CH ∧
      2*historyLabelDifferenceCost H*P.terminalBound A.CM A.CH/P.epsilon ≤
        P.neighborCost hτ hτT H A.CM A.CH := by
  have hs := rayScale_pos hτ hτT P
  have he := A.epsilon_pos
  have ht := A.terminalBound_nonneg
  have hc := historyLabelDifferenceCost_nonneg H
  have hn := norm_nonneg (D.M.derivative.field)
  have hr : 0 ≤ 3*‖D.normal.derivative.field‖/(P.rayScale hτ hτT*P.epsilon) := by positivity
  have hv : 0 ≤ 2*historyLabelDifferenceCost H*P.terminalBound A.CM A.CH/P.epsilon := by positivity
  unfold ParentFrame.neighborCost
  constructor
  · linarith only [hr,hv]
  constructor <;> linarith only [hn,hr,hv]

omit [CompleteSpace U] in
theorem radius_cost_le_error : P.neighborCost hτ hτT H A.CM A.CH*A.radius ≤
    P.totalError hτ hτT H A.CM A.CH A.radius := by
  change _ ≤ P.error+_
  linarith only [P.error_nonneg]

omit [CompleteSpace U] in
theorem sourceError_bound (x : Space) (hx : ‖x‖ ≤ A.radius) (t : ℝ) (ht : t ∈ Icc τ D.T) :
    ‖P.sourceError x t‖ ≤ P.totalError hτ hτT H A.CM A.CH A.radius := by
  have hd := coefficient_difference D.M (D.clamp t) x 0
  rw [sub_zero] at hd
  have hr := P.remainder_bound t ht
  have hm := mul_le_mul A.neighbor_components.1 hx (norm_nonneg x) A.neighborCost_nonneg
  calc
    ‖P.sourceError x t‖ = ‖(sourceMatrix D x t-sourceMatrix D 0 t)+P.sourceError 0 t‖ := by
      congr 1
      unfold ParentFrame.sourceError
      module
    _ ≤ ‖sourceMatrix D x t-sourceMatrix D 0 t‖+‖P.sourceError 0 t‖ := norm_add_le _ _
    _ ≤ ‖D.M.derivative.field‖*‖x‖+P.error := add_le_add hd hr
    _ ≤ P.neighborCost hτ hτT H A.CM A.CH*A.radius+P.error := add_le_add hm le_rfl
    _ = P.totalError hτ hτT H A.CM A.CH A.radius := by unfold ParentFrame.totalError; ring

theorem source_velocity_initial_error (x : Space) (hx : ‖x‖ ≤ A.radius) :
    |scaledVelocity P.m P.v (A.sourceVelocity x) τ P.a P.epsilon 0 1-1| +
      |scaledVelocity P.m P.v (A.sourceVelocity x) τ P.a P.epsilon 0 0+A.slope| ≤
      P.totalError hτ hτT H A.CM A.CH A.radius := by
  have hp := A.terminal_properties
  have he := actual_scaled_velocity_initial_error τ hτ hτT H P.m P.v
    (P.ray_nonzero τ ⟨le_rfl,hτT.le⟩) (P.velocity_nonzero τ ⟨le_rfl,hτT.le⟩)
    A.terminal P.a P.epsilon A.slope A.epsilon_pos A.epsilon_small hp.2.2.2.2.1 hp.2.2.2.2.2 x
  apply he.trans
  have hc := historyLabelDifferenceCost_nonneg H
  calc
    2*historyLabelDifferenceCost H*‖x‖*‖A.terminal‖/P.epsilon ≤
        2*historyLabelDifferenceCost H*‖x‖*P.terminalBound A.CM A.CH/P.epsilon := by
      apply div_le_div_of_nonneg_right _ A.epsilon_pos.le
      exact mul_le_mul_of_nonneg_left hp.2.2.2.1 (by positivity)
    _ = (2*historyLabelDifferenceCost H*P.terminalBound A.CM A.CH/P.epsilon)*‖x‖ := by ring
    _ ≤ P.neighborCost hτ hτT H A.CM A.CH*A.radius :=
      mul_le_mul A.neighbor_components.2.2 hx (norm_nonneg x) A.neighborCost_nonneg
    _ ≤ P.totalError hτ hτT H A.CM A.CH A.radius := A.radius_cost_le_error

omit [CompleteSpace U] in
theorem source_ray_initial_error (x : Space) (hx : ‖x‖ ≤ A.radius) :
    norm3 (scaledRay P.m P.v (sourceRay D x) (P.rayScale hτ hτT) τ P.a P.epsilon 0 0)
      (scaledRay P.m P.v (sourceRay D x) (P.rayScale hτ hτT) τ P.a P.epsilon 0 1)
      (scaledRay P.m P.v (sourceRay D x) (P.rayScale hτ hτT) τ P.a P.epsilon 0 2-1) ≤
      P.totalError hτ hτT H A.CM A.CH A.radius := by
  have he := actual_scaled_ray_initial_error (D := D) τ hτ hτT P.m P.v
    (P.ray_nonzero τ ⟨le_rfl,hτT.le⟩) (P.velocity_nonzero τ ⟨le_rfl,hτT.le⟩)
    (P.tangent τ ⟨le_rfl,hτT.le⟩) A.normal_choice P.a P.epsilon A.epsilon_pos A.epsilon_small x
  apply he.trans
  calc
    3*‖D.normal.derivative.field‖*‖x‖/(P.rayScale hτ hτT*P.epsilon) =
      (3*‖D.normal.derivative.field‖/(P.rayScale hτ hτT*P.epsilon))*‖x‖ := by ring
    _ ≤ P.neighborCost hτ hτT H A.CM A.CH*A.radius :=
      mul_le_mul A.neighbor_components.2.1 hx (norm_nonneg x) A.neighborCost_nonneg
    _ ≤ P.totalError hτ hτT H A.CM A.CH A.radius := A.radius_cost_le_error

omit [CompleteSpace U] in
theorem error_le_scaled_error : P.totalError hτ hτT H A.CM A.CH A.radius ≤
    16*(P.epsilon*P.horizon*(4*P.G)^2+P.totalError hτ hτT H A.CM A.CH A.radius) := by
  have he := A.totalError_nonneg
  have hbase : 0 ≤ P.epsilon*P.horizon*(4*P.G)^2 :=
    mul_nonneg (mul_nonneg A.epsilon_pos.le (zero_le_one.trans A.horizon_lower)) (sq_nonneg _)
  linarith only [he,hbase]

/-- Every new analytic component is the actual source field or the
selected stationary/forward primary.  The parent input and scalar guard
record contain none of this record's new-field conclusions. -/
def geometryData (Ω : Set Space) (h0 : 0 ∈ Ω) (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ A.radius) :
    PhysicalGeometryData {x : Space // x ∈ Ω} where
  center := ⟨0,h0⟩
  B := P.B
  B₁ := P.B₁
  M := fun x => sourceMatrix D x
  E := fun x => P.sourceError x
  m := P.m
  v := P.v
  r := fun x => sourceRay D x
  w := fun x => A.sourceVelocity x
  c := P.c
  s₀ := P.rayScale hτ hτT
  t₀ := τ
  a := P.a
  ε := P.epsilon
  σ := P.sigma
  y := A.y
  Θ := P.horizon
  H := P.horizon
  G := P.G
  d := P.totalError hτ hτT H A.CM A.CH A.radius
  lam := A.slope
  δ := A.δ
  hchild := A.hchild
  S := Icc τ D.T
  sigma_pos := A.sigma_pos
  sigma_small := A.sigma_small
  y_pos := A.y_pos
  y_small := A.y_small
  target_le_horizon := A.target_le_horizon
  horizon_le_Theta := le_rfl
  short_extension := A.short_extension
  a_lower := A.coupling_lower
  epsilon_pos := A.epsilon_pos
  Theta_lower := A.horizon_lower
  G_lower := P.G_lower
  d_nonneg := A.totalError_nonneg
  ray_scale_pos := rayScale_pos hτ hτT P
  slope_nonneg := A.terminal_properties.2.1
  delta_nonneg := A.delta_nonneg
  child_nonneg := A.child_nonneg
  small := A.small
  compression_guard := A.compression_guard
  time_maps := activation_horizon_maps τ D.T P.a P.epsilon A.a_pos A.epsilon_pos
  M_continuous := fun x => (sourceMatrix_continuous D x).continuousOn
  B_derivative := P.B_derivative
  old_ray_equation := P.ray_equation
  old_velocity_equation := P.velocity_equation
  ray_equation := fun x t ht => sourceRay_equation (hτ := hτ) x t ht
  velocity_equation := fun x t ht => A.sourceVelocity_equation x t ht
  old_ray_nonzero := P.ray_nonzero
  old_velocity_nonzero := P.velocity_nonzero
  old_tangent := P.tangent
  initial_tangent := fun x => A.source_initial_tangent x
  B_bound := P.B_bound
  B_derivative_bound := P.B₁_bound
  E_bound := fun x t ht => A.sourceError_bound x (hΩ x x.property) t ht
  parent_decomposition := by
    intro x t _
    unfold ParentFrame.sourceError
    module
  initial_coupling := activation_coupling_match P.B P.m P.v τ P.epsilon
  initial_tilt := activation_tilt_match P.B P.m P.v τ P.epsilon A.a_pos.ne'
    (Real.sqrt_pos.mp A.sigma_pos).le
  initial_shear := (activation_shear_match P.c P.m P.v τ P.a A.a_pos A.shear_pos).2
  initial_ray_error := fun x => (A.source_ray_initial_error x (hΩ x x.property)).trans
      A.error_le_scaled_error
  initial_velocity_error := fun x =>
    (A.source_velocity_initial_error x (hΩ x x.property)).trans A.error_le_scaled_error

theorem geometryData_matrix (Ω : Set Space) (h0 : 0 ∈ Ω) (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ A.radius)
    (x : {x : Space // x ∈ Ω}) (t : ℝ) :
    (A.geometryData Ω h0 hΩ).M x t=D.M.field (D.clamp t) x := rfl

theorem geometryData_ray (Ω : Set Space) (h0 : 0 ∈ Ω) (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ A.radius)
    (x : {x : Space // x ∈ Ω}) (t : ℝ) :
    (A.geometryData Ω h0 hΩ).r x t=D.normal.field (D.clamp t) x := rfl

theorem geometryData_velocity (Ω : Set Space) (h0 : 0 ∈ Ω) (hΩ : ∀ x ∈ Ω, ‖x‖ ≤ A.radius)
    (x : {x : Space // x ∈ Ω}) (t : ℝ) :
    (A.geometryData Ω h0 hΩ).w x t=uncutVelocity τ hτ hτT H A.terminal t x := rfl

end Guards
end EulerPacketSourceGeometry
