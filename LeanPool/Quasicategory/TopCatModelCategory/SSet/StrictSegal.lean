/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import LeanPool.Quasicategory.TopCatModelCategory.Fin
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

universe u

open CategoryTheory Opposite Simplicial

@[simp]
lemma SimplexCategory.mkOfSucc_zero :
    mkOfSucc (0 : Fin 1) = 𝟙 _ := by
  ext i
  fin_cases i <;> rfl

namespace SSet

variable {X Y : SSet.{u}} (f : X ⟶ Y)

lemma σ_injective {n : ℕ} (i : Fin (n + 1)) : Function.Injective (X.σ i) := fun x₁ x₂ h ↦ by
  rw [← δ_comp_σ_self_apply i x₁, ← δ_comp_σ_self_apply i x₂, h]

lemma mono_iff_of_strictSegal [IsStrictSegal X] :
    Mono f ↔ Function.Injective (f.app (op (.mk 1))) := by
  have sx := StrictSegal.ofIsStrictSegal X
  rw [NatTrans.mono_iff_mono_app]
  simp only [mono_iff_injective]
  refine ⟨fun hf ↦ hf _, fun hf ⟨k⟩ ↦ ?_⟩
  induction k using SimplexCategory.rec with | _ k => ?_
  obtain _ | k := k
  · intro x y h
    apply σ_injective 0
    apply sx.spineInjective
    ext i
    fin_cases i
    apply hf
    dsimp [StrictSegal.spineEquiv]
    simp only [Fin.isValue, SimplexCategory.mkOfSucc_zero, op_id, Functor.map_id_apply,
      σ_naturality_apply, h]
  · intro x y h
    apply sx.spineInjective
    ext i
    apply hf
    dsimp [StrictSegal.spineEquiv]
    simp only [NatTrans.naturality_apply, h]

end SSet
