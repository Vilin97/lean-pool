/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialGeometry
public import LeanPool.NavierStokesAndEuler.Euler.TransverseHistoryLipschitz

@[expose] public section

/-!
The actual fixed-terminal history estimate controls the scaled neighbor
initial velocity.  The loss `ε⁻¹` comes from the specified coordinate
rescaling and is independent of the oscillation frequency.
-/

noncomputable section


namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerVolterraConvolution EulerTimeH1FrameTransport
  EulerTransverseEndpointCoordinates EulerTransverseHistoryBounds

theorem frame_pair_difference_le {p q x y : Space} {ε D : ℝ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hxy : ‖x-y‖ ≤ D) :
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
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hxy : ‖x t₀-y t₀‖ ≤ D) :
    |scaledVelocity m v x t₀ a ε 0 0-scaledVelocity m v y t₀ a ε 0 0|+
      |scaledVelocity m v x t₀ a ε 0 1-scaledVelocity m v y t₀ a ε 0 1| ≤ 2*D/ε := by
  simpa [scaledVelocity, movingVelocity, physicalTime, normalizedFrame, frame,
    velocityScale, Fin.ext_iff] using
      frame_pair_difference_le (unit_norm hm0) (unit_norm hv0) hε hε1 hxy

theorem scaled_inner_difference_le {p x y : Space} {b D : ℝ}
    (hp : ‖p‖ = 1) (hb : 0 < b) (hxy : ‖x-y‖ ≤ D) :
    |⟪p,x⟫_ℝ/b-⟪p,y⟫_ℝ/b| ≤ D/b := by
  rw [← sub_div, ← inner_sub_right, abs_div, abs_of_pos hb]
  apply div_le_div_of_nonneg_right _ hb.le
  exact ((abs_real_inner_le_norm p (x-y)).trans_eq (by rw [hp, one_mul])).trans hxy

theorem scaledRay_initial_difference_le {m v x y : ℝ → Space} {s₀ t₀ a ε D : ℝ}
    (hs₀ : 0 < s₀) (hm0 : m t₀ ≠ 0) (hv0 : v t₀ ≠ 0) (hmv : ⟪m t₀,v t₀⟫_ℝ = 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hxy : ‖x t₀-y t₀‖ ≤ D) :
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
    (hs₀ : 0 < s₀) (hm0 : m t₀ ≠ 0) (hv0 : v t₀ ≠ 0) (hmv : ⟪m t₀,v t₀⟫_ℝ = 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hr : ‖r t₀-s₀ • EulerPacketCrossProduct.cross (unit (m t₀)) (unit (v t₀))‖ ≤ D) :
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
    (A B : U →L[ℝ] C(Icc (0:ℝ) T, Space)) (ξ : U) (t : Icc (0:ℝ) T)
    {p q : Space} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hAB : ‖A-B‖ ≤ D) :
    |⟪p,A ξ t⟫_ℝ/ε-⟪p,B ξ t⟫_ℝ/ε|+|⟪q,A ξ t⟫_ℝ-⟪q,B ξ t⟫_ℝ| ≤
      2*D*‖ξ‖/ε := by
  have hn : ‖A ξ t-B ξ t‖ ≤ D*‖ξ‖ := by
    exact (((A-B) ξ).norm_coe_le_norm t).trans (((A-B).le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right hAB (norm_nonneg ξ)))
  simpa only [mul_assoc] using frame_pair_difference_le hp hq hε hε1 hn

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] Space))
  (H : C(Icc (0 : ℝ) T, Space →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t ξ, c*‖ξ‖^2 ≤ ‖Q t ξ‖^2)
  (hd : ∀ t : Icc (0:ℝ) T, HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0:ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t z, ⟪H t z,z⟫_ℝ ≤ K*‖z‖^2)
  (hsmall : K*(T^2/2) ≤ 1/2)
  (P P₁ : C(Icc (0:ℝ) T, U →L[ℝ] Space))
  (G : C(Icc (0:ℝ) T, Space →L[ℝ] Space))
  (hP : ∀ t ξ, c*‖ξ‖^2 ≤ ‖P t ξ‖^2)
  (hp : ∀ t : Icc (0:ℝ) T, HasDerivWithinAt (extendPath T hT P) (P₁ t) (Icc (0:ℝ) T) t)
  (hG : ∀ t z, ⟪G t z,z⟫_ℝ ≤ K*‖z‖^2)

/-- The two actual stationary histories use the same terminal coordinate
`ξ`; physical coefficient differences give the scaled initial error. -/
theorem history_scaled_pair_difference_le (hTpos : 0 < T) (q q₁ d a r : ℝ)
    (hQn : ‖Q‖ ≤ q) (hPn : ‖P‖ ≤ q) (hQ₁n : ‖Q₁‖ ≤ q₁) (hP₁n : ‖P₁‖ ≤ q₁)
    (hD : T*‖Q₁‖+‖Q‖ ≤ d) (hD' : T*‖P₁‖+‖P‖ ≤ d)
    (hA : 1+T^2*‖H‖ ≤ a) (hA' : 1+T^2*‖G‖ ≤ a)
    (hr : transportCost T Q Q₁ c ≤ r) (hr' : transportCost T P P₁ c ≤ r)
    (L₀ L₁ LH s : ℝ) (h₀ : ‖Q-P‖ ≤ L₀*s) (h₁ : ‖Q₁-P₁‖ ≤ L₁*s) (hHdiff : ‖H-G‖ ≤ LH*s)
    (ξ : U) (t : Icc (0:ℝ) T) {p₀ q₀ : Space} (hp₀ : ‖p₀‖ = 1) (hq₀ : ‖q₀‖ = 1)
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
