/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointVelocity
public import LeanPool.NavierStokesAndEuler.Euler.TransverseActivationTrial

@[expose] public section

/-!
Source (26) for the actual stationary transverse solution.  The endpoint
matrix is the constructed Dirichlet-to-Neumann operator and its norm is
derived from the explicit moving-projection trial.  The selected velocity is
the genuine derivative η_t minus Mη, not a separately prescribed matrix output.
-/

noncomputable section


namespace EulerTransverseActivationSelection

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerInitialTimePrimitive EulerVolterraConvolution
  EulerTransverseEndpointEnergy EulerTransverseEndpointVelocity
  EulerTransverseActivationTrial EulerDNSelection

variable {U E V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def activationConstant (CM CH : ℝ) : ℝ := 4 + 64 * CM ^ 2 + 2 * CH

/-- The actual terminal matrix after subtracting the prescribed shear. -/
def terminalPerturbation (T : ℝ) (hT : 0 ≤ T) (R : V →ₗᵢ[ℝ] E)
    (M : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (p q : V) (h : ℝ) : V →L[ℝ] V :=
  R.toContinuousLinearMap.adjoint.comp
    ((M ⟨T, hT, le_rfl⟩).comp R.toContinuousLinearMap) - h • rankOne ℝ q p

/-- Differentiating the actual moving tangency constraint makes η_t−Mη tangent. -/
theorem corrected_velocity_tangent (T : ℝ) (hT : 0 < T)
    (m m₁ : C(Icc (0 : ℝ) T, E))
    (M : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hdm : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT.le m) (m₁ t) (Icc (0 : ℝ) T) t)
    (hRay : ∀ t, m₁ t = -(M t).adjoint (m t))
    (η v : ℝ → E)
    (hdη : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt η (v t) (Icc (0 : ℝ) T) t)
    (htan : ∀ t : Icc (0 : ℝ) T, ⟪m t, η t⟫_ℝ = 0)
    (t : Icc (0 : ℝ) T) : ⟪m t, v t - M t (η t)⟫_ℝ = 0 := by
  have hd := (hdm t).inner ℝ (hdη t)
  have hz : HasDerivWithinAt (fun s => ⟪extendPath T hT.le m s, η s⟫_ℝ)
      (0 : ℝ) (Icc (0 : ℝ) T) t := by
    apply (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) (0 : ℝ)).congr_of_mem _ t.property
    intro s hs
    simpa only [extendPath, projIcc_of_mem hT.le hs] using htan ⟨s, hs⟩
  have he := (hd.derivWithin ((uniqueDiffOn_Icc hT) t t.property)).symm.trans
    (hz.derivWithin ((uniqueDiffOn_Icc hT) t t.property))
  simp only [extendPath, projIcc_of_mem hT.le t.property, hRay,
    inner_neg_left, adjoint_inner_left, inner_sub_right] at he ⊢
  linarith only [he]

/-- The activation choice is attached to the actual weak inverse, its continuous
physical derivative, and the derived endpoint energy bound. -/
theorem select_actual_activation
    (T : ℝ) (hT : 0 < T)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)
    (hdQ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT.le Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (m m₁ : C(Icc (0 : ℝ) T, E)) (hne : ∀ t, m t ≠ 0)
    (hdm : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT.le m) (m₁ t) (Icc (0 : ℝ) T) t)
    (hm : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (R : V →ₗᵢ[ℝ] E) (hR : ∀ Y, ⟪m ⟨T, hT.le, le_rfl⟩, R Y⟫_ℝ = 0)
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (hHs : ∀ t, (H t).IsSymmetric)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
    (M : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hRay : ∀ t, m₁ t = -(M t).adjoint (m t))
    (h CM CH ε : ℝ) (hh : 0 < h) (hLayer : 1 ≤ h * T)
    (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hε : 0 ≤ ε)
    (hM : ∀ t, ‖M t‖ ≤ CM * h) (hHnorm : ‖H‖ ≤ CH * h ^ 2)
    (p q : V) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫_ℝ = 0)
    (hεsmall : 16 * (activationConstant CM CH + 1) * ε ≤ 1)
    (hB : ‖terminalPerturbation T hT.le R M p q h‖ ≤ ε * h)
    (hBpp : ⟪terminalPerturbation T hT.le R M p q h p, p⟫_ℝ < 0) :
    ∃ Y : V,
      let L := activationTrial T hT.le m m₁ hne R.toContinuousLinearMap h
      let u := endpointDerivative T hT.le (fun t => m t) H K hK hH hsmall L Y
      let η := initialRealPrimitive T u
      let v := physicalVelocityPath T hT.le Q Q₁ c hc hQ H u
      let w := fun t => v t - extendPath T hT.le M t (η t)
      η 0 = 0 ∧ η T = R Y ∧ Continuous v ∧
      (∀ t : Icc (0 : ℝ) T, HasDerivWithinAt η (v t) (Icc (0 : ℝ) T) t) ∧
      (∀ t : Icc (0 : ℝ) T, ⟪m t, w t⟫_ℝ = 0) ∧
      ⟪w T, R q⟫_ℝ = 1 ∧
      -8 * (activationConstant CM CH + 1) ≤ ⟪w T, R p⟫_ℝ ∧
      ⟪w T, R p⟫_ℝ ≤ 0 ∧
      ‖Y‖ ≤ 8 * (activationConstant CM CH + 1) / h := by
  let L := activationTrial T hT.le m m₁ hne R.toContinuousLinearMap h
  let Λ := dirichletToNeumann T hT.le (fun t => m t) H K hK hH hsmall L
  let B := terminalPerturbation T hT.le R M p q h
  have hΛ : Λ.IsPositive :=
    dirichletToNeumann_positive T hT.le (fun t => m t) H K hK hH hsmall hHs L
  have hΛnorm : ‖Λ‖ ≤ activationConstant CM CH * h :=
    activation_endpoint_norm T hT.le m m₁ hne R.toContinuousLinearMap hdm h hh hLayer
      R.norm_toContinuousLinearMap_le CM CH hCM hCH M hRay hM H hHs hHnorm K hK hH hsmall
  have hC : 1 ≤ activationConstant CM CH := by
    unfold activationConstant
    nlinarith only [sq_nonneg CM, hCH]
  obtain ⟨yp, yq, hwq, hwpl, hwpu, hY⟩ :=
    select_endpoint_hilbert Λ B p q (activationConstant CM CH) ε h hΛ hp hq hpq
      hC hε hh hεsmall hΛnorm hB hBpp
  let Y := yp • p + yq • q
  let u := endpointDerivative T hT.le (fun t => m t) H K hK hH hsmall L Y
  let η := initialRealPrimitive T u
  let v := physicalVelocityPath T hT.le Q Q₁ c hc hQ H u
  let w := fun t => v t - extendPath T hT.le M t (η t)
  have hLt : ∀ Z t, ⟪m t, initialPrimitive T hT.le (L Z) t⟫_ℝ = 0 :=
    activationTrial_tangent T hT.le m m₁ hne R.toContinuousLinearMap hdm h
  have hLT : ∀ Z, initialPrimitive T hT.le (L Z) ⟨T, hT.le, le_rfl⟩ = R Z :=
    activationTrial_terminal T hT.le m m₁ hne R.toContinuousLinearMap hdm h hLayer hR
  have hηT : η T = R Y :=
    (endpointDisplacement_terminal T hT.le (fun t => m t) H K hK hH hsmall L Y).trans (hLT Y)
  have hdη : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt η (v t) (Icc (0 : ℝ) T) t :=
    endpointDisplacement_hasDerivWithinAt T hT.le Q Q₁ c hc hQ H hdQ hT
      (fun t => m t) hm hRange K hK hH hsmall L hLt Y
  have hηtan : ∀ t : Icc (0 : ℝ) T, ⟪m t, η t⟫_ℝ = 0 :=
    endpointDisplacement_tangent T hT.le (fun t => m t) H K hK hH hsmall L hLt Y
  have hvt : R.toContinuousLinearMap.adjoint (v T) = Λ Y :=
    (dirichletToNeumann_eq_terminal_velocity T hT.le Q Q₁ c hc hQ H hdQ hT
      (fun t => m t) hm hRange K hK hH hsmall L R.toContinuousLinearMap hLt hLT Y).symm
  have hwt : R.toContinuousLinearMap.adjoint (w T) =
      Λ Y - B Y - (h * ⟪p, Y⟫_ℝ) • q := by
    dsimp only [w]
    rw [map_sub, hvt, hηT]
    simp only [B, terminalPerturbation, sub_apply, comp_apply, smul_apply, rankOne_apply,
      smul_smul, extendPath, projIcc_of_mem hT.le (show T ∈ Icc (0 : ℝ) T from ⟨hT.le, le_rfl⟩)]
    abel
  have hwcoord (z : V) : ⟪w T, R z⟫_ℝ =
      ⟪Λ Y - B Y - (h * ⟪p, Y⟫_ℝ) • q, z⟫_ℝ := by
    change ⟪w T, R.toContinuousLinearMap z⟫_ℝ = _
    rw [← R.toContinuousLinearMap.adjoint_inner_left, hwt]
  refine ⟨Y, initialRealPrimitive_initial T u, hηT,
    physicalVelocityPath_continuous T hT.le Q Q₁ c hc hQ H u, hdη, ?_, ?_, ?_, ?_, hY⟩
  · intro t
    simpa only [w, extendPath, projIcc_of_mem hT.le t.property] using
      corrected_velocity_tangent T hT m m₁ M hdm hRay η v hdη hηtan t
  · exact (hwcoord q).trans hwq
  · exact (hwcoord p).symm ▸ hwpl
  · exact (hwcoord p).symm ▸ hwpu

end EulerTransverseActivationSelection
