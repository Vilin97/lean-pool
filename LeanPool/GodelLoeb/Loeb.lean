/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.GodelLoeb.Diagonal

/-!
# Modal-axiomatic Loeb theorem

This file derives Loeb's theorem in the K4 substrate and the
non-vacuous Kreisel diagonal interface.
-/

namespace ModalLogic.GoedelLoeb

open ModalFormula

universe u

/-- Loeb's theorem in the modal-axiomatic K4 substrate. -/
theorem loeb {α : Type u} [DecidableEq α] [Diagonalisable α] {phi : ModalFormula α}
    (h : Provable (□ₛphi ⟶ phi)) : Provable phi := by
  let psi := Diagonalisable.fixedpoint phi
  let hStructuralEvidence := Diagonalisable.structural (α := α)
  have hStructural :
      Provable (psi ⟷ (□ₛ(Substitution.code (hStructuralEvidence.template phi)) ⟶
        phi)) := by
    dsimp [psi, hStructuralEvidence]
    exact Provable.of_prop_taut
      (ModalFormula.fixedpoint_structural_prop_taut Diagonalisable.fixedpoint
        Diagonalisable.distinguishedAtom phi Diagonalisable.structural)
  have hCodeTemplate :
      Provable (□ₛ(Substitution.code (hStructuralEvidence.template phi)) ⟷ □ₛpsi) := by
    dsimp [psi, hStructuralEvidence]
    exact Provable.of_prop_taut (Diagonalisable.structural.box_code_fixedpoint phi)
  have hImpBridge :
      Provable (((□ₛ(Substitution.code (hStructuralEvidence.template phi))) ⟶ phi) ⟷
        (□ₛpsi ⟶ phi)) :=
    Provable.imp_congr hCodeTemplate (Provable.iff_intro (Provable.imp_refl phi)
      (Provable.imp_refl phi))
  have hForward : Provable (psi ⟶ (□ₛpsi ⟶ phi)) :=
    Provable.imp_trans (Provable.iff_left hStructural) (Provable.iff_left hImpBridge)
  have hBackward : Provable ((□ₛpsi ⟶ phi) ⟶ psi) :=
    Provable.imp_trans (Provable.iff_right hImpBridge) (Provable.iff_right hStructural)
  have hDiag : Provable (psi ⟷ (□ₛpsi ⟶ phi)) := by
    exact Provable.iff_intro hForward hBackward
  have hUnfold : Provable (psi ⟶ (□ₛpsi ⟶ phi)) :=
    Provable.iff_left hDiag
  have hBoxUnfold : Provable (□ₛ(psi ⟶ (□ₛpsi ⟶ phi))) :=
    Provable.nec hUnfold
  have hD2Unfold :
      Provable (□ₛ(psi ⟶ (□ₛpsi ⟶ phi)) ⟶
        (□ₛpsi ⟶ □ₛ(□ₛpsi ⟶ phi))) :=
    Provable.k psi (□ₛpsi ⟶ phi)
  have hBoxImp : Provable (□ₛpsi ⟶ □ₛ(□ₛpsi ⟶ phi)) :=
    Provable.mp hD2Unfold hBoxUnfold
  have hD2Target :
      Provable (□ₛ(□ₛpsi ⟶ phi) ⟶ (□ₛ□ₛpsi ⟶ □ₛphi)) :=
    Provable.k (□ₛpsi) phi
  have hD3Psi : Provable (□ₛpsi ⟶ □ₛ□ₛpsi) :=
    Provable.four psi
  have hBoxToBoxTarget : Provable (□ₛpsi ⟶ □ₛphi) :=
    Provable.imp_box_combine hBoxImp hD3Psi hD2Target
  have hBoxToTarget : Provable (□ₛpsi ⟶ phi) :=
    Provable.imp_trans hBoxToBoxTarget h
  have hFold : Provable ((□ₛpsi ⟶ phi) ⟶ psi) :=
    Provable.iff_right hDiag
  have hPsi : Provable psi :=
    Provable.mp hFold hBoxToTarget
  have hBoxPsi : Provable (□ₛpsi) :=
    Provable.nec hPsi
  exact Provable.mp hBoxToTarget hBoxPsi

end ModalLogic.GoedelLoeb
