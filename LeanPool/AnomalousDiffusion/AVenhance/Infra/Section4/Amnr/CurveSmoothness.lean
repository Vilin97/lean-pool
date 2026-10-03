/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StateDerivatives

/-! Arbitrary smoothness of primitive fields acting on continuous curves. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

universe u
variable {K E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Evaluate a joint primitive field along the prescribed time curve and a
state trajectory. This is the actual substitution in the integral equation. -/
def amnrCurveJointCompose (f : ℝ × E → F) (hf : Continuous f) (η : C(K, ℝ)) :
    C(K, E) → C(K, F) :=
  amnrCurveCompose (fun t x => f (η t, x))
    (hf.comp ((η.continuous.comp continuous_fst).prodMk continuous_snd))

/-- The actual joint field induces its actual curve-space derivative from
a primitive second derivative bound. -/
theorem amnrCurveJointCompose_hasFDerivAt {f : ℝ × E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ C) (η : C(K, ℝ)) (u : C(K, E)) :
    HasFDerivAt (amnrCurveJointCompose f hf.continuous η)
      (amnrCurveOperator (amnrCurveJointCompose (amnrStateDerivative f)
        (amnrStateDerivative_contDiff hf).continuous η u)) u := by
  have hD := (amnrStateDerivative_contDiff hf).continuous
  exact amnrCurveCompose_hasFDerivAt (fun t x => f (η t, x))
    (hf.continuous.comp ((η.continuous.comp continuous_fst).prodMk continuous_snd))
    (fun t x => amnrStateDerivative f (η t, x))
    (hD.comp ((η.continuous.comp continuous_fst).prodMk continuous_snd)) hC
    (fun t x h => amnr_joint_field_state_quadratic_remainder hf hC hbound (η t) x h) u

/-- Primitive bounds at every derivative order prove every finite order of
smoothness of the substitution operator. The assumptions are actual field
bounds, not regularity or bounds of the flow being constructed. -/
theorem amnrCurveJointCompose_contDiff_nat (n : ℕ) {f : ℝ × E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤ C)
    (η : C(K, ℝ)) : ContDiff ℝ n (amnrCurveJointCompose f hf.continuous η) := by
  induction n generalizing F with
  | zero =>
    apply contDiff_zero.mpr
    apply Differentiable.continuous (𝕜 := ℝ)
    intro u
    obtain ⟨C, hC, hCb⟩ := hbound 2
    exact (amnrCurveJointCompose_hasFDerivAt hf hC hCb η u).differentiableAt
  | succ n ih =>
    have hD := amnrStateDerivative_contDiff hf
    have hDb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ z, ‖iteratedFDeriv ℝ j (amnrStateDerivative f) z‖ ≤ C := by
      intro j
      obtain ⟨C, hC, hCb⟩ := hbound (j + 1)
      exact ⟨C, hC, amnrStateDerivative_iteratedFDeriv_norm_le hf j hCb⟩
    have hcurve := ih hD hDb
    have hderiv : ContDiff ℝ n (fun u => amnrCurveOperator
        (amnrCurveJointCompose (amnrStateDerivative f) hD.continuous η u)) := by
      convert (amnrCurveOperatorMap (K := K) (E := E) (F := F)).contDiff.comp hcurve using 1
      rfl
    apply (contDiff_succ_iff_hasFDerivAt (n := n)).mpr
    refine ⟨_, hderiv, ?_⟩
    intro u
    obtain ⟨C, hC, hCb⟩ := hbound 2
    exact amnrCurveJointCompose_hasFDerivAt hf hC hCb η u

/-- All-order primitive estimates give actual smooth substitution on the
continuous-trajectory Banach space. -/
theorem amnrCurveJointCompose_contDiff_infty {f : ℝ × E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤ C)
    (η : C(K, ℝ)) : ContDiff ℝ (⊤ : ℕ∞) (amnrCurveJointCompose f hf.continuous η) := by
  rw [contDiff_infty]
  exact fun n => amnrCurveJointCompose_contDiff_nat n hf hbound η

end AVenhance.Infra.Section4
