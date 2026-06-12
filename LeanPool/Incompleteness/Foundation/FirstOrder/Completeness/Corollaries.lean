/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.Completeness

/-! # Corollaries -/


namespace LO
namespace FirstOrder

namespace ModelsTheory

variable {L : Language.{u}} (M : Type w) [Nonempty M] [Structure L M] (T U V : Theory L)

lemma of_provably_subtheory [T wkn U] (h : M ⊧ₘ* U) : M ⊧ₘ* T := ⟨by
  intro φ hp
  have : U ⊢! φ := (inferInstance : T wkn U).pbl (Entailment.by_axm _ hp)
  exact consequence_iff'.{u, w}.mp (sound! this) M⟩

lemma of_provably_subtheory' [T wkn U] [M ⊧ₘ* U] :
    M ⊧ₘ* T :=
  of_provably_subtheory M T U inferInstance

lemma of_add_left [M ⊧ₘ* T + U] :
    M ⊧ₘ* T :=
  of_ss inferInstance (show T ⊆ T + U from by simp [Theory.add_def])

lemma of_add_right [M ⊧ₘ* T + U] :
    M ⊧ₘ* U :=
  of_ss inferInstance (show U ⊆ T + U from by simp [Theory.add_def])

lemma of_add_left_left [M ⊧ₘ* T + U + V] :
    M ⊧ₘ* T :=
  @of_add_left _ M _ _ T U (of_add_left M (T + U) V)

lemma of_add_left_right [M ⊧ₘ* T + U + V] :
    M ⊧ₘ* U :=
  @of_add_right _ M _ _ T U (of_add_left M (T + U) V)

end ModelsTheory

variable {L : Language.{u}} [L.Eq] {T : Theory L} [𝐄𝐐 wkn T]

lemma _root_.LO.FirstOrder.EQ.provOf (φ : SyntacticFormula L)
  (H : ∀ (M : Type (max u w))
         [Nonempty M]
         [Structure L M] [Structure.Eq L M]
         [M ⊧ₘ* T],
         M ⊧ₘ φ) :
    T ⊨ φ := consequence_iff_consequence.{u, w}.mp <| consequence_iff_eq.mpr fun M _ _ _ hT =>
  letI : (Structure.Model L M) ⊧ₘ* T :=
    ((Structure.ElementaryEquiv.modelsTheory (Structure.Model.elementaryEquiv L M)).mp hT)
  (Structure.ElementaryEquiv.models (Structure.Model.elementaryEquiv L M)).mpr (H (Structure.Model
    L M))

end FirstOrder
end LO
