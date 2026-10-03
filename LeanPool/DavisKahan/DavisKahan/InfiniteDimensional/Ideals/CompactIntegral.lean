/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Ideals.Symmetric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bochner integration of compact-operator-valued functions

Compact continuous linear maps form a norm-closed linear subspace of the
bounded rectangular operator space.  Therefore the Bochner integral of an
integrable, almost-everywhere compact-valued function is compact.  This is the
closure fact needed by the Fourier Sylvester inverse.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open MeasureTheory Filter

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F]

/-- Compact rectangular operators as a linear subspace. -/
def compactOperatorSubmodule : Submodule ℂ (E →L[ℂ] F) where
  carrier := {T | IsCompactOperator T}
  zero_mem' := isCompactOperator_zero
  add_mem' := fun hS hT => hS.add hT
  smul_mem' := fun c _T hT => hT.smul c

omit [CompleteSpace E] in
/-- The compact-operator submodule is operator-norm closed. -/
theorem isClosed_compactOperatorSubmodule :
    IsClosed (compactOperatorSubmodule (E := E) (F := F) : Set (E →L[ℂ] F)) := by
  exact isClosed_setOfPred_isCompactOperator

omit [CompleteSpace E] in
/-- Bochner integration preserves compactness. -/
theorem isCompactOperator_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → E →L[ℂ] F}
    (hf : Integrable f μ)
    (hcompact : ∀ᵐ a ∂μ, IsCompactOperator (f a)) :
    IsCompactOperator (∫ a, f a ∂μ : E →L[ℂ] F) := by
  have hKcl : IsClosed
      ((compactOperatorSubmodule (E := E) (F := F)) : Set (E →L[ℂ] F)) :=
    isClosed_compactOperatorSubmodule
  let π := (compactOperatorSubmodule (E := E) (F := F)).mkQL
  have hπ : ∀ x, π x = Submodule.Quotient.mk x := fun _ => rfl
  have hπ0 : π (∫ a, f a ∂μ) = 0 := by
    have hcomm := ContinuousLinearMap.integral_comp_comm (𝕜 := ℂ)
      (E := E →L[ℂ] F)
      (Fₗ := (E →L[ℂ] F) ⧸ compactOperatorSubmodule (E := E) (F := F)) π hf
    rw [← hcomm]
    have hzero : (fun a => π (f a)) =ᵐ[μ] fun _ =>
        (0 : (E →L[ℂ] F) ⧸ compactOperatorSubmodule (E := E) (F := F)) := by
      filter_upwards [hcompact] with a ha
      rw [hπ]
      exact (Submodule.Quotient.mk_eq_zero
        (compactOperatorSubmodule (E := E) (F := F))).mpr ha
    rw [integral_congr_ae hzero, integral_zero]
  exact (Submodule.Quotient.mk_eq_zero
    (compactOperatorSubmodule (E := E) (F := F))).mp
    ((hπ (∫ a, f a ∂μ)).symm.trans hπ0)

end

end DavisKahanExt
end TauCeti
