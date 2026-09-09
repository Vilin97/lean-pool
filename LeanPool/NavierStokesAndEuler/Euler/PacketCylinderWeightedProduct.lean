/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldWeight
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique

/-! Products of actual normalized fields use only the pointwise ratio of their time profiles. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderPathProduct EulerPacketProfileRecursion
open scoped ContDiff

/-- Product profile ratio, given by `⟨fun t => g t*h t/b t,(g.continuous.mul h.continuous).div
b.continuous (fun t => (hb t).ne')⟩`. -/
def productProfileRatio {K : Type*} [TopologicalSpace K]
    (g h b : C(K, ℝ)) (hb : ∀ t, 0 < b t) : C(K,ℝ) :=
  ⟨fun t => g t*h t/b t,(g.continuous.mul h.continuous).div b.continuous (fun t => (hb t).ne')⟩

@[simp] theorem productProfileRatio_apply {K : Type*} [TopologicalSpace K]
    (g h b : C(K, ℝ)) (hb : ∀ t, 0 < b t) (t : K) :
    productProfileRatio g h b hb t = g t*h t/b t := rfl

theorem productProfileRatio_abs_le {K : Type*} [TopologicalSpace K]
    (g h b : C(K, ℝ)) (hg : ∀ t, 0 ≤ g t) (hh : ∀ t, 0 ≤ h t)
    (hb : ∀ t, 0 < b t) (C : ℝ) (hC : ∀ t, g t * h t ≤ C * b t) (t : K) :
    |productProfileRatio g h b hb t| ≤ C := by
  rw [productProfileRatio_apply,abs_of_nonneg (div_nonneg (mul_nonneg (hg t) (hh t)) (hb t).le)]
  exact (div_le_iff₀ (hb t)).mpr (hC t)

namespace Field

variable {P T : ℝ} [Fact (0 < P)] {raw raw' : VectorField}
  (G : Field P T raw) (H : Field P T raw') (hT : 0 ≤ T)
  (g h b : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t) (hh : ∀ t, 0 < h t) (hb : ∀ t, 0 < b t)

theorem normalized_bilinear_path (L : Space →L[ℝ] Space →L[ℝ] Space) :
    ((G.bilinear H L).normalized hT b hb).path =
      (((G.normalized hT g hg).bilinear (H.normalized hT h hh) L).weighted hT
        (productProfileRatio g h b hb)).path := by
  apply path_eq_of_raw_eq
  intro t x θ
  change productProfileRatio g h b hb (projIcc 0 T hT t) •
    L ((g (projIcc 0 T hT t))⁻¹ • raw (t,(x,θ))) ((h (projIcc 0 T hT t))⁻¹ • raw' (t,(x,θ))) =
      (b (projIcc 0 T hT t))⁻¹ • L (raw (t,(x,θ))) (raw' (t,(x,θ)))
  rw [projIcc_of_mem hT t.property]
  simp only [productProfileRatio_apply,map_smul,smul_apply,smul_smul]
  congr 1
  field_simp [(hg t).ne',(hh t).ne',(hb t).ne']

theorem normalized_scalarProduct_path (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    ((G.scalarProduct H L hL).normalized hT b hb).path =
      (((G.normalized hT g hg).scalarProduct (H.normalized hT h hh) L hL).weighted hT
        (productProfileRatio g h b hb)).path := by
  apply path_eq_of_raw_eq
  intro t x θ
  change productProfileRatio g h b hb (projIcc 0 T hT t) •
    (L ((g (projIcc 0 T hT t))⁻¹ • raw (t,(x,θ))) • ((h (projIcc 0 T hT t))⁻¹ • raw' (t,(x,θ)))) =
      (b (projIcc 0 T hT t))⁻¹ • (L (raw (t,(x,θ))) • raw' (t,(x,θ)))
  rw [projIcc_of_mem hT t.property]
  simp only [productProfileRatio_apply,map_smul,smul_eq_mul,smul_smul]
  congr 1
  field_simp [(hg t).ne',(hh t).ne',(hb t).ne']

theorem normalized_spatialTransport_path :
    ((G.spatialTransport H).normalized hT b hb).path =
      (((G.normalized hT g hg).spatialTransport (H.normalized hT h hh)).weighted hT
        (productProfileRatio g h b hb)).path := by
  apply path_eq_of_raw_eq
  intro t x θ
  have hd : fderiv ℝ
      (fun y : LiftTangent => (h (projIcc 0 T hT t))⁻¹ • raw' (t,y)) (x,θ) =
        (h t)⁻¹ • fderiv ℝ (fun y : LiftTangent => raw' (t,y)) (x,θ) := by
    rw [projIcc_of_mem hT t.property]
    exact (((H.raw_smooth t).differentiable (by simp) (x,θ)).hasFDerivAt.const_smul (h t)⁻¹).fderiv
  change productProfileRatio g h b hb (projIcc 0 T hT t) •
    fderiv ℝ (fun y : LiftTangent => (h (projIcc 0 T hT t))⁻¹ • raw' (t,y)) (x,θ)
      ((g (projIcc 0 T hT t))⁻¹ • raw (t,(x,θ)),0) =
        (b (projIcc 0 T hT t))⁻¹ • fderiv ℝ (fun y : LiftTangent => raw' (t,y)) (x,θ) (raw
            (t,(x,θ)),0)
  rw [hd,projIcc_of_mem hT t.property]
  have ha : ((g t)⁻¹ • raw (t,(x,θ)),(0 : ℝ)) = (g t)⁻¹ • (raw (t,(x,θ)),(0 : ℝ)) := by simp
  rw [ha]
  simp only [productProfileRatio_apply,smul_apply,map_smul,smul_smul]
  congr 1
  field_simp [(hg t).ne',(hh t).ne',(hb t).ne']

variable {G H g h b hg hh hb}

theorem WordBound.normalized_bilinear {R A B : ℝ} {d e : ℕ}
    (hG : (G.normalized hT g hg).WordBound 6 R A d)
    (hH : (H.normalized hT h hh).WordBound 6 R B e)
    (L : Space →L[ℝ] Space →L[ℝ] Space) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (C : ℝ) (hC : 0 ≤ C) (hprofile : ∀ t, |productProfileRatio g h b hb t| ≤ C) :
    ((G.bilinear H L).normalized hT b hb).WordBound 6 R
      (C*(9*productBlockConstant P*‖L‖*A*B)) (d+e) := by
  have hbound := (hG.bilinear hH L hR hA hB).weighted hT (productProfileRatio g h b hb) C hC
      hprofile
  unfold WordBound at *
  rw [G.normalized_bilinear_path H hT g h b hg hh hb L]
  exact hbound

theorem WordBound.normalized_scalarProduct {R A B : ℝ} {d e : ℕ}
    (hG : (G.normalized hT g hg).WordBound 6 R A d)
    (hH : (H.normalized hT h hh).WordBound 6 R B e)
    (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (C : ℝ) (hC : 0 ≤ C) (hprofile : ∀ t, |productProfileRatio g h b hb t| ≤ C) :
    ((G.scalarProduct H L hL).normalized hT b hb).WordBound 6 R
      (C*(3*productBlockConstant P*A*B)) (d+e) := by
  have hbound := (hG.scalarProduct hH L hL hR hA hB).weighted hT (productProfileRatio g h b hb) C
      hC hprofile
  unfold WordBound at *
  rw [G.normalized_scalarProduct_path H hT g h b hg hh hb L hL]
  exact hbound

theorem WordBound.normalized_spatialTransport {R A B : ℝ} {d e : ℕ}
    (hG : (G.normalized hT g hg).WordBound 6 R A d)
    (hH : (H.normalized hT h hh).WordBound 6 R B e)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (C : ℝ) (hC : 0 ≤ C) (hprofile : ∀ t, |productProfileRatio g h b hb t| ≤ C) :
    ((G.spatialTransport H).normalized hT b hb).WordBound 6 R
      (C*(9*productBlockConstant P*A*B)) (d+e+1) := by
  have hbound := (hG.spatialTransport hH hR hA hB).weighted hT (productProfileRatio g h b hb) C hC
      hprofile
  unfold WordBound at *
  rw [G.normalized_spatialTransport_path H hT g h b hg hh hb]
  exact hbound

end Field
end EulerPacketCylinderField
