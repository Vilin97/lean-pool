/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.GodelLoeb.Modal.Kripke

/-!
# Kripke soundness bridge

This file bundles the semantic soundness statements for K, T, 4, and
5 and keeps the concrete one-world K4 frame.
-/

namespace ModalLogic.GoedelLoeb

namespace KripkeFrame

universe u

/-- On a reflexive, transitive, Euclidean frame, K, T, 4, and 5 are sound. -/
theorem basicModalAxiomsSound {F : KripkeFrame}
    (hRefl : ∀ w, F.accessible w w)
    (hTrans : ∀ w₁ w₂ w₃, F.accessible w₁ w₂ → F.accessible w₂ w₃ →
      F.accessible w₁ w₃)
    (hEucl : ∀ w₁ w₂ w₃, F.accessible w₁ w₂ → F.accessible w₁ w₃ →
      F.accessible w₂ w₃)
    {P Q : F.World → Prop} {w : F.World}
    (hImp : F.necessarily (fun v => P v → Q v) w)
    (hBoxP : F.necessarily P w)
    (hPossP : F.possibly P w) :
    F.necessarily Q w ∧
      P w ∧
        F.necessarily (fun u => F.necessarily P u) w ∧
          F.necessarily (fun u => F.possibly P u) w := by
  exact ⟨distrib_K hImp hBoxP, refl_T hRefl hBoxP, four hTrans hBoxP, five hEucl hPossP⟩

/-- The one-world frame with universal accessibility. -/
def trivialK4Frame : KripkeFrame where
  World := Unit
  accessible _ _ := True

/-- The one-world frame is reflexive. -/
lemma trivialK4Frame_reflexive :
    ∀ w : trivialK4Frame.World, trivialK4Frame.accessible w w := by
  intro w
  trivial

/-- The one-world frame is transitive. -/
lemma trivialK4Frame_transitive :
    ∀ w₁ w₂ w₃ : trivialK4Frame.World,
      trivialK4Frame.accessible w₁ w₂ →
        trivialK4Frame.accessible w₂ w₃ →
          trivialK4Frame.accessible w₁ w₃ := by
  intro w₁ w₂ w₃ _h₁₂ _h₂₃
  trivial

/-- The one-world frame is Euclidean. -/
lemma trivialK4Frame_euclidean :
    ∀ w₁ w₂ w₃ : trivialK4Frame.World,
      trivialK4Frame.accessible w₁ w₂ →
        trivialK4Frame.accessible w₁ w₃ →
          trivialK4Frame.accessible w₂ w₃ := by
  intro w₁ w₂ w₃ _h₁₂ _h₁₃
  trivial

/-- The bundled modal-axiom soundness theorem fires on the concrete frame. -/
lemma trivialK4Frame_basicModalAxiomsSound
    {P Q : trivialK4Frame.World → Prop} {w : trivialK4Frame.World}
    (hImp : trivialK4Frame.necessarily (fun v => P v → Q v) w)
    (hBoxP : trivialK4Frame.necessarily P w)
    (hPossP : trivialK4Frame.possibly P w) :
    trivialK4Frame.necessarily Q w ∧
      P w ∧
        trivialK4Frame.necessarily (fun u => trivialK4Frame.necessarily P u) w ∧
          trivialK4Frame.necessarily (fun u => trivialK4Frame.possibly P u) w :=
  basicModalAxiomsSound trivialK4Frame_reflexive trivialK4Frame_transitive
    trivialK4Frame_euclidean hImp hBoxP hPossP

/-- The `Provable` forcing theorem also fires on the concrete one-world frame. -/
lemma trivialK4Frame_provable_forces {α : Type u}
    {val : α → trivialK4Frame.World → Prop}
    (hProp : PropTautSound (F := trivialK4Frame) val)
    {phi : ModalFormula α} (h : Provable phi) :
    ∀ w : trivialK4Frame.World, Forces (F := trivialK4Frame) val w phi :=
  provable_forces trivialK4Frame_transitive hProp h

end KripkeFrame

end ModalLogic.GoedelLoeb
