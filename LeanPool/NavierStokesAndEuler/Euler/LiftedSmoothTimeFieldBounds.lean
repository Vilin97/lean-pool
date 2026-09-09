/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LiftedSmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldAlgebra

@[expose] public section

/-! The true lifted coefficient of an approximation plus correction has
a small amplitude controlled by the scaled spatial field, the actual
normal component, and the correction size. -/

noncomputable section


namespace EulerLiftedSmoothTimeField

open EulerSmoothLimit EulerLiftedGradientSpace EulerPacketCylinderField
open scoped ContDiff BoundedContinuousFunction

variable {K E : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] LiftTangent) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] LiftTangent) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] Space)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] Space)) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] LiftTangent)) :=
  inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] LiftTangent)) := inferInstance

theorem lift_add_jet_norm_le (A B : SmoothTimeField K E Space)
    (κ : ℝ) (m : Space) (n : ℕ) :
    ‖(lift (A.add B) κ m).jet n‖ ≤
      |κ| * ‖A.jet n‖ + ‖(A.map (normalComponentMap m)).jet n‖ +
        (|κ| + ‖m‖)*‖B.jet n‖ := by
  have he : (lift (A.add B) κ m).jet n = ((lift A κ m).add (lift B κ m)).jet n := by
    apply SmoothTimeField.jet_eq_of_field_eq
    intro t x
    change EulerLiftedTransportTrace.transportLinear κ m (A.field t x+B.field t x) = _
    exact (EulerLiftedTransportTrace.transportLinear κ m).map_add _ _
  rw [he]
  exact (((lift A κ m).add_jet_norm_le (lift B κ m) n).trans
    (add_le_add (lift_jet_norm_le A κ m n) (lift_jet_norm_le_full B κ m n)))

theorem lift_add_jet_bound (A B : SmoothTimeField K E Space)
    (κ : ℝ) (m : Space) (R C0 Cn Ce : ℝ)
    (hA : ∀ n, ‖A.jet n‖ ≤ C0*R^n*(n.factorial : ℝ)^2)
    (hN : ∀ n, ‖(A.map (normalComponentMap m)).jet n‖ ≤ Cn*R^n*(n.factorial : ℝ)^2)
    (hE : ∀ n, ‖B.jet n‖ ≤ Ce*R^n*(n.factorial : ℝ)^2) (n : ℕ) :
    ‖(lift (A.add B) κ m).jet n‖ ≤
      (|κ| * C0+Cn+(|κ| + ‖m‖)*Ce)*R^n*(n.factorial : ℝ)^2 := by
  apply (lift_add_jet_norm_le A B κ m n).trans
  calc
    _ ≤ |κ| * (C0*R^n*(n.factorial : ℝ)^2) + Cn*R^n*(n.factorial : ℝ)^2 +
        (|κ| + ‖m‖)*(Ce*R^n*(n.factorial : ℝ)^2) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hA n) (abs_nonneg κ)) (hN n))
        (mul_le_mul_of_nonneg_left (hE n) (add_nonneg (abs_nonneg κ) (norm_nonneg m)))
    _ = _ := by ring

theorem lift_add_inverse_scale_bound (A B : SmoothTimeField K E Space)
    (k : ℝ) (hk : 1 ≤ k) (m : Space) (hm : ‖m‖ ≤ 1)
    (R C0 Cn Ce : ℝ) (hR : 0 ≤ R) (hCe : 0 ≤ Ce)
    (hA : ∀ n, ‖A.jet n‖ ≤ C0*R^n*(n.factorial : ℝ)^2)
    (hN : ∀ n, ‖(A.map (normalComponentMap m)).jet n‖ ≤ (Cn/k)*R^n*(n.factorial : ℝ)^2)
    (hE : ∀ n, ‖B.jet n‖ ≤ Ce*R^n*(n.factorial : ℝ)^2) (n : ℕ) :
    ‖(lift (A.add B) k⁻¹ m).jet n‖ ≤
      ((C0+Cn)/k+2*Ce)*R^n*(n.factorial : ℝ)^2 := by
  have hk0 : 0 < k := by linarith
  have hki : |k⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hk0)]
    exact inv_le_one_of_one_le₀ hk
  have hc : |k⁻¹| * C0+Cn/k+(|k⁻¹| + ‖m‖)*Ce ≤ (C0+Cn)/k+2*Ce := by
    rw [abs_of_pos (inv_pos.mpr hk0)]
    have he := mul_le_mul_of_nonneg_right (add_le_add hki hm) hCe
    rw [abs_of_pos (inv_pos.mpr hk0)] at he
    calc
      _ ≤ k⁻¹*C0+Cn/k+(1+1)*Ce := add_le_add le_rfl he
      _ = _ := by ring
  exact (lift_add_jet_bound A B k⁻¹ m R C0 (Cn/k) Ce hA hN hE n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (pow_nonneg hR n))
      (sq_nonneg (n.factorial : ℝ)))

end EulerLiftedSmoothTimeField
