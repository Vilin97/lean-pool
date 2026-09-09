/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerGraphDerivative
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerTimeRestriction

@[expose] public section

/-! Canonical graph restrictions need no additional representative or
regularity assumptions beyond the actual all-order tower. -/

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerMetricTransport EulerVolterraConvolution
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)]
  (A : EulerAllOrderCorrectionData.FieldTower P T)
  (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

def canonicalGraphWordPath (n : ℕ) (w : Fin n → Fin 4) :
    C(Icc (0 : ℝ) T,Lp Vector3 2 (volume : Measure Vector3)) :=
  A.graphWordPath A.pointField A.pointField_smooth A.pointField_ae θ hθ n w

theorem canonicalGraphWordPath_ae (n : ℕ) (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    (A.canonicalGraphWordPath θ hθ n w t : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w (A.pointField t) (x,θ x) :=
  A.graphWordPath_ae A.pointField A.pointField_smooth A.pointField_ae θ hθ n w t

theorem canonicalGraphWordPath_norm_sq_le (n : ℕ) (w : Fin n → Fin 4)
    (t : Icc (0 : ℝ) T) :
    ‖A.canonicalGraphWordPath θ hθ n w t‖^2 ≤
      (2/P+2*P)*‖A.realization (n+1) t‖^2 :=
  A.graphWordPath_norm_sq_le A.pointField A.pointField_smooth A.pointField_ae θ hθ n w t

theorem canonicalGraphWordPath_norm_sq_le_high (n : ℕ) (w : Fin n → Fin 4)
    (q : ℕ) (hq : n+1 ≤ q) (t : Icc (0 : ℝ) T) :
    ‖A.canonicalGraphWordPath θ hθ n w t‖^2 ≤
      (2/P+2*P)*‖A.realization q t‖^2 := by
  have hn := restrictOperator_bound P hq (A.realization q t)
  rw [A.restrict_realization] at hn
  have hP : 0 < P := Fact.out
  exact (A.canonicalGraphWordPath_norm_sq_le θ hθ n w t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) (by positivity))

theorem canonicalGraphWordPath_hasDerivAt (B : EulerAllOrderCorrectionData.FieldTower P T)
    (hT : 0 ≤ T) (n : ℕ) (w : Fin n → Fin 4) (q : ℕ) (hq : n+1 ≤ q)
    (t : ℝ) (ht : t ∈ Ioo 0 T)
    (hd : HasDerivAt (extendPath T hT (A.realization q))
      (B.realization q ⟨t,ht.1.le,ht.2.le⟩) t) :
    HasDerivAt (extendPath T hT (A.canonicalGraphWordPath θ hθ n w))
      (B.canonicalGraphWordPath θ hθ n w ⟨t,ht.1.le,ht.2.le⟩) t :=
  A.graphWordPath_hasDerivAt B A.pointField B.pointField A.pointField_smooth B.pointField_smooth
    A.pointField_ae B.pointField_ae θ hθ hT n w t ht
    (A.realization_hasDerivAt_of_le B hq hT ⟨t,ht.1.le,ht.2.le⟩ hd)

end EulerAllOrderCorrectionData.FieldTower
