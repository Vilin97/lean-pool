/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCrossProduct
public import LeanPool.NavierStokesAndEuler.Euler.AngleMeanZeroPrimitive

/-! The vector potential Q of a tangent, mean-zero, periodic high coefficient. -/

section

/-! Uniform bounds for the actual mean-zero angular primitive. -/

@[expose] public section

noncomputable section

namespace EulerAngleMeanZeroPrimitive

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem rawPrimitive_bound (P M : ℝ) (hM : 0 ≤ M) (f : ℝ → E)
    (hf : ∀ θ ∈ Icc 0 P, ‖f θ‖ ≤ M) (θ : ℝ) (hθ : θ ∈ Icc 0 P) :
    ‖rawPrimitive f θ‖ ≤ M*P := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := θ) (f := f) (C := M) (fun x hx => hf x (by
      rw [uIoc_of_le hθ.1] at hx
      exact ⟨hx.1.le, hx.2.trans hθ.2⟩))
  simp only [sub_zero, abs_of_nonneg hθ.1] at h
  exact h.trans (mul_le_mul_of_nonneg_left hθ.2 hM)

omit [CompleteSpace E] in
theorem primitive_bound (P M : ℝ) (hP : 0 < P) (hM : 0 ≤ M) (f : ℝ → E)
    (hf : ∀ θ ∈ Icc 0 P, ‖f θ‖ ≤ M) (θ : ℝ) (hθ : θ ∈ Icc 0 P) :
    ‖primitive P f θ‖ ≤ 2*P*M := by
  have hraw := rawPrimitive_bound P M hM f hf
  have hint : ‖∫ s in 0..P, rawPrimitive f s‖ ≤ (M*P)*P := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := P) (f := rawPrimitive f) (C := M*P) (fun x hx => hraw x (by
        rw [uIoc_of_le hP.le] at hx
        exact ⟨hx.1.le, hx.2⟩))
    simpa only [sub_zero, abs_of_pos hP] using h
  have hmean : ‖P⁻¹ • (∫ s in 0..P, rawPrimitive f s)‖ ≤ M*P := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hP)]
    calc
      _ ≤ P⁻¹*((M*P)*P) := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hP.le)
      _ = M*P := by field_simp
  exact (norm_sub_le _ _).trans (by linarith [hraw θ hθ, hmean])

end EulerAngleMeanZeroPrimitive

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketAngularPotential

open EulerSmoothLimit EulerPacketCrossProduct EulerAngleMeanZeroPrimitive
  MeasureTheory Set InnerProductSpace

/-- Potential, given by `primitive P (fun θ => potentialMultiplier m (A θ))`. -/
def potential (P : ℝ) (m : Space) (A : ℝ → Space) : ℝ → Space :=
  primitive P (fun θ => potentialMultiplier m (A θ))

theorem potential_hasDerivAt (P : ℝ) (m : Space) (A : ℝ → Space)
    (hA : Continuous A) (θ : ℝ) :
    HasDerivAt (potential P m A) (potentialMultiplier m (A θ)) θ :=
  primitive_hasDerivAt P _ ((potentialMultiplier m).continuous.comp hA) θ

/-- The actual angular derivative recovers A after crossing with m. -/
theorem cross_deriv_potential (P : ℝ) (m : Space) (hm : m ≠ 0) (A : ℝ → Space)
    (hA : Continuous A) (htan : ∀ θ, ⟪m, A θ⟫_ℝ = 0) (θ : ℝ) :
    cross m (deriv (potential P m A) θ)=A θ := by
  rw [(potential_hasDerivAt P m A hA θ).deriv]
  exact cross_potentialMultiplier m (A θ) hm (htan θ)

theorem potential_periodic (P : ℝ) (m : Space) (A : ℝ → Space)
    (hA : Continuous A) (hper : Function.Periodic A P)
    (hmean : ∫ θ in 0..P, A θ = 0) : Function.Periodic (potential P m A) P := by
  apply primitive_periodic P _ ((potentialMultiplier m).continuous.comp hA)
  · intro θ
    exact congrArg (potentialMultiplier m) (hper θ)
  · simp only [Function.comp_def]
    rw [(potentialMultiplier m).intervalIntegral_comp_comm (hA.intervalIntegrable 0 P),
      hmean, map_zero]

theorem potential_mean_zero (P : ℝ) (hP : P ≠ 0) (m : Space) (A : ℝ → Space)
    (hA : Continuous A) : (∫ θ in 0..P, potential P m A θ)=0 :=
  primitive_mean_zero P hP _ ((potentialMultiplier m).continuous.comp hA)

theorem potential_zero (P : ℝ) (m : Space) :
    potential P m (fun _ => 0)=fun _ => 0 := by
  funext θ
  simp [potential, primitive, rawPrimitive]

/-- The angular construction creates no values at labels where the whole input vanishes. -/
theorem potential_vanishes (P : ℝ) (m : Space) (A : ℝ → Space) (hA : ∀ θ, A θ = 0) :
    ∀ θ, potential P m A θ=0 := by
  have h : A=fun _ => 0 := funext hA
  rw [h, potential_zero]
  exact fun _ => rfl

theorem potential_bound (P M : ℝ) (hP : 0 < P) (hM : 0 ≤ M) (m : Space)
    (A : ℝ → Space) (hA : ∀ θ ∈ Icc 0 P, ‖A θ‖ ≤ M) (θ : ℝ) (hθ : θ ∈ Icc 0 P) :
    ‖potential P m A θ‖ ≤ 2*P*(‖potentialMultiplier m‖*M) := by
  apply primitive_bound P (‖potentialMultiplier m‖*M) hP
    (mul_nonneg (norm_nonneg _) hM) _ _ θ hθ
  intro s hs
  exact ((potentialMultiplier m).le_opNorm (A s)).trans
    (mul_le_mul_of_nonneg_left (hA s hs) (norm_nonneg _))

end EulerPacketAngularPotential
