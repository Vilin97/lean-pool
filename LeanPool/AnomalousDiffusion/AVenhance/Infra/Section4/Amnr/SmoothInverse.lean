/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowJointSmoothness

/-! Smoothness of actual inverses from proved C¹ inverse identities. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- A C¹ inverse of a locally smooth map is locally smooth. Invertibility
of the derivative is obtained by differentiating the actual two inverse
identities, rather than supplied as an additional premise. -/
theorem amnr_contDiffAt_inverse_of_differentiable_inverses {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P Q : E → E} {x : E}
    (hP : ContDiffAt ℝ (⊤ : ℕ∞) P (Q x)) (hQ : DifferentiableAt ℝ Q x)
    (hleft : ∀ y, Q (P y) = y) (hright : ∀ y, P (Q y) = y) :
    ContDiffAt ℝ (⊤ : ℕ∞) Q x := by
  let A := fderiv ℝ P (Q x)
  let B := fderiv ℝ Q x
  have hP' := (hP.differentiableAt (by simp)).hasFDerivAt
  have hQ' := hQ.hasFDerivAt
  have hPQ : A.comp B = ContinuousLinearMap.id ℝ E := by
    have hh := hP'.comp x hQ'
    have he : P ∘ Q = id := funext hright
    rw [he] at hh
    exact hh.unique (hasFDerivAt_id x)
  have hQP : B.comp A = ContinuousLinearMap.id ℝ E := by
    have hQ'' : HasFDerivAt Q B (P (Q x)) := by rw [hright]; exact hQ'
    have hh := hQ''.comp (Q x) hP'
    have he : Q ∘ P = id := funext hleft
    rw [he] at hh
    exact hh.unique (hasFDerivAt_id (Q x))
  have hbij : Function.Bijective A := by
    constructor
    · intro y z h
      have hh := congrArg B h
      change (B.comp A) y = (B.comp A) z at hh
      rwa [hQP] at hh
    · intro y
      refine ⟨B y, ?_⟩
      change (A.comp B) y = y
      rw [hPQ]
      rfl
  let e := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hbij.1)
    (LinearMap.range_eq_top.mpr hbij.2)
  have he : (e : E →L[ℝ] E) = A := rfl
  have hd : HasFDerivAt P (e : E →L[ℝ] E) (Q x) := by rw [he]; exact hP'
  exact amnr_contDiffAt_of_invertible_left_equation hQ.continuousAt hP e hd
    contDiffAt_id hright

/-- The actual inverse flow is jointly smooth wherever the actual forward
flow is smooth on the short interval. Its C¹ inverse identities are already
proved from the characterized ODE. -/
theorem amnr_flow_inverse_contDiffAt_joint_of_short {b : ℝ → Vec 2 → Vec 2}
    (hb : AVenhance.Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {M : ℝ} (hM : 0 ≤ M)
    (hstate : ∀ t x, ‖AVenhance.Infra.Flow.jointSpatialFDeriv b t x‖ ≤ M)
    (s t : ℝ) (x : Vec 2) (hshort : |t - s| * M ≤ 1 / 4) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => X s z.2 z.1) (t, x) := by
  let P := fun z : ℝ × Vec 2 => (z.1, X z.1 z.2 s)
  let Q := fun z : ℝ × Vec 2 => (z.1, X s z.2 z.1)
  have hP : ContDiffAt ℝ (⊤ : ℕ∞) P (Q (t, x)) :=
    contDiffAt_fst.prodMk (amnr_flow_contDiffAt_joint_of_short hb hX hM hstate s t (X s x t) hshort)
  have hQi : ContDiff ℝ 1 (fun z : ℝ × Vec 2 => X s z.2 z.1) :=
    (AVenhance.Infra.Flow.flow_joint_contDiff_one hb hX).comp
      (by fun_prop : ContDiff ℝ 1 (fun z : ℝ × Vec 2 => (s, z.2, z.1)))
  have hQ : DifferentiableAt ℝ Q (t, x) :=
    (contDiff_fst.prodMk hQi).differentiable (by norm_num) _
  have hl : ∀ z, Q (P z) = z := by
    intro z
    have hh := (AVenhance.Infra.Flow.flow_fixed_time_maps_are_C1_inverses hb hX s z.1).2.2.1 z.2
    exact Prod.ext rfl hh
  have hr : ∀ z, P (Q z) = z := by
    intro z
    have hh := (AVenhance.Infra.Flow.flow_fixed_time_maps_are_C1_inverses hb hX s z.1).2.2.2 z.2
    exact Prod.ext rfl hh
  have hh := amnr_contDiffAt_inverse_of_differentiable_inverses hP hQ hl hr
  exact contDiffAt_snd.comp (t, x) hh

end AVenhance.Infra.Section4
