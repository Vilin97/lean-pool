/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTimeWordGluing

@[expose] public section

/-! The actual affine time shift used by the forward transverse solve. -/

noncomputable section

namespace EulerPacketTimePathGluing

open Set EulerParameterWordGevrey
open scoped ContDiff

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] compactInterval

def elapsedTime (S τ : ℝ) : C(Icc τ S, Icc (0 : ℝ) (S-τ)) :=
  ⟨fun t => ⟨(t:ℝ)-τ, sub_nonneg.mpr t.property.1, sub_le_sub_right t.property.2 τ⟩,
    (continuous_subtype_val.sub continuous_const).subtype_mk _⟩

def shiftPath (S τ : ℝ) : C(Icc (0 : ℝ) (S-τ), E) →L[ℝ] C(Icc τ S,E) :=
  ContinuousMap.compCLM ℝ E (elapsedTime S τ)

theorem shiftPath_apply (S τ : ℝ) (u : C(Icc (0 : ℝ) (S-τ), E)) (t : Icc τ S) :
    shiftPath S τ u t = u ⟨(t:ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2 τ⟩ :=
      rfl

theorem shiftPath_norm_le_one (S τ : ℝ) : ‖shiftPath (E := E) S τ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).2
  intro t
  exact u.norm_coe_le_norm _

theorem shiftPath_initial (S τ : ℝ) (hτS : τ ≤ S) (u : C(Icc (0 : ℝ) (S-τ), E)) :
    shiftPath S τ u ⟨τ,le_rfl,hτS⟩ = u ⟨0,le_rfl,sub_nonneg.mpr hτS⟩ := by
  simp only [shiftPath_apply, sub_self]

/-- Literal elapsed-time paths retain the same fixed-Sobolev word bound. -/
theorem shiftPath_block_bound [Fintype ι] (S τ : ℝ) (directions : ι → X) (q : ℕ)
    (f : X → C(Icc (0 : ℝ) (S-τ), E)) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    block directions q (fun y => shiftPath S τ (f y)) n x ≤ block directions q f n x := by
  have h := block_comp_clm_le directions q (shiftPath S τ) f hf n x
  exact h.trans ((mul_le_mul_of_nonneg_right (shiftPath_norm_le_one S τ)
    (block_nonneg directions q f n x)).trans_eq (one_mul _))

end EulerPacketTimePathGluing
