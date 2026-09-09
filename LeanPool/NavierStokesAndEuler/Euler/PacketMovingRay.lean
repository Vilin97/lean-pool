/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketMovingFrame

@[expose] public section

/-! The physical ray ODE in the actual normalized moving frame. -/

noncomputable section


namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary InnerProductSpace ContinuousLinearMap

theorem frame_inner_expand (p q : Space)
    (hp : ⟪p,p⟫_ℝ = 1) (hq : ⟪q,q⟫_ℝ = 1) (hpq : ⟪p,q⟫_ℝ = 0) (x y : Space) :
    (∑ j : Fin 3, ⟪frame p q j,x⟫_ℝ * ⟪frame p q j,y⟫_ℝ) = ⟪x,y⟫_ℝ := by
  have hb := (frameBasis p q hp hq hpq).sum_inner_mul_inner x y
  simp only [frameBasis_apply] at hb
  calc
    (∑ j : Fin 3, ⟪frame p q j,x⟫_ℝ * ⟪frame p q j,y⟫_ℝ) =
        ∑ j : Fin 3, ⟪x,frame p q j⟫_ℝ * ⟪frame p q j,y⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_comm x (frame p q j)]
    _ = _ := hb

theorem movingRayRate_identity (B M : Space →L[ℝ] Space) (p q x : Space)
    (hp : ⟪p,p⟫_ℝ = 1) (hq : ⟪q,q⟫_ℝ = 1) (hpq : ⟪p,q⟫_ℝ = 0) (i : Fin 3) :
    -⟪M (frame p q i),x⟫_ℝ + ⟪frameRate B p q i,x⟫_ℝ =
      -(∑ j : Fin 3, (frameMatrix M p q j i -
        EulerPacketRay.frameSkew (frameMatrix B p q) j i) * ⟪frame p q j,x⟫_ℝ) := by
  have hsk (j : Fin 3) : EulerPacketRay.frameSkew (frameMatrix B p q) j i =
      ⟪frame p q j,frameRate B p q i⟫_ℝ := (frameRate_skew B p q hp hq hpq j i).symm
  simp_rw [hsk, frameMatrix, sub_mul, Finset.sum_sub_distrib]
  rw [frame_inner_expand p q hp hq hpq, frame_inner_expand p q hp hq hpq]
  ring

def movingRay (m v r : ℝ → Space) (t : ℝ) (i : Fin 3) : ℝ :=
  ⟪normalizedFrame m v t i,r t⟫_ℝ

/-- The actual moving-coordinate ray obeys `-(M-S)ᵀ`, with the skew
matrix already derived from the older primary ODE. -/
theorem movingRay_hasDerivAt (B M : Space →L[ℝ] Space)
    {m v r : ℝ → Space} {t : ℝ}
    (hm : HasDerivAt m (-B.adjoint (m t)) t)
    (hv : HasDerivAt v (-B (v t) + (2*⟪m t,B (v t)⟫_ℝ / ‖m t‖^2) • m t) t)
    (hr : HasDerivAt r (-M.adjoint (r t)) t)
    (hm0 : m t ≠ 0) (hv0 : v t ≠ 0) (hmv : ⟪m t,v t⟫_ℝ = 0) (i : Fin 3) :
    HasDerivAt (fun s => movingRay m v r s i)
      (-(∑ j : Fin 3, (frameMatrix M (unit (m t)) (unit (v t)) j i -
        EulerPacketRay.frameSkew (frameMatrix B (unit (m t)) (unit (v t))) j i) *
          movingRay m v r t j)) t := by
  have h := (normalizedFrame_hasDerivAt B hm hv hm0 hv0 hmv i).inner ℝ hr
  have he := movingRayRate_identity B M (unit (m t)) (unit (v t)) (r t)
    (unit_inner_self hm0) (unit_inner_self hv0) (unit_inner_zero hmv) i
  simpa only [movingRay, normalizedFrame, inner_neg_right, adjoint_inner_right, he] using h

/-- The same physical coordinate equation holds with one-sided endpoint derivatives. -/
theorem movingRay_hasDerivWithinAt (B M : Space →L[ℝ] Space)
    {m v r : ℝ → Space} {t : ℝ} {S : Set ℝ}
    (hm : HasDerivWithinAt m (-B.adjoint (m t)) S t)
    (hv : HasDerivWithinAt v (-B (v t) + (2*⟪m t,B (v t)⟫_ℝ / ‖m t‖^2) • m t) S t)
    (hr : HasDerivWithinAt r (-M.adjoint (r t)) S t)
    (hm0 : m t ≠ 0) (hv0 : v t ≠ 0) (hmv : ⟪m t,v t⟫_ℝ = 0) (i : Fin 3) :
    HasDerivWithinAt (fun s => movingRay m v r s i)
      (-(∑ j : Fin 3, (frameMatrix M (unit (m t)) (unit (v t)) j i -
        EulerPacketRay.frameSkew (frameMatrix B (unit (m t)) (unit (v t))) j i) *
          movingRay m v r t j)) S t := by
  have h := (normalizedFrame_hasDerivWithinAt B hm hv hm0 hv0 hmv i).inner ℝ hr
  have he := movingRayRate_identity B M (unit (m t)) (unit (v t)) (r t)
    (unit_inner_self hm0) (unit_inner_self hv0) (unit_inner_zero hmv) i
  simpa only [movingRay, normalizedFrame, inner_neg_right, adjoint_inner_right, he] using h

end EulerPacketMovingFrame
