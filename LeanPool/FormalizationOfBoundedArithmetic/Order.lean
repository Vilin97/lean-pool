/-
Copyright (c) 2026 Mary Jane. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mary Jane
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Order
import Mathlib.Tactic.FinCases

import LeanPool.FormalizationOfBoundedArithmetic.DisplayedVariables
import LeanPool.FormalizationOfBoundedArithmetic.Syntax
import LeanPool.FormalizationOfBoundedArithmetic.LanguageZambella

namespace FirstOrder.Language.Formula

open Language BoundedFormula

section IsOrdered
universe u
variable {L : Language} [IsOrdered L] {α : Type u}

variable {n r} (a b : L.BoundedFormula n r)


def iBdEx' {α n} (bdTerm : L.Term (α ⊕ Fin 0)) (φ : L.Formula (α ⊕ (Vars1 n))) : L.Formula α :=
  let bd := (var (.inl (Sum.inr (.fv1)))).le $ bdTerm.relabel (Sum.map .inl id)
  iExs' $ bd ⊓ φ

def iBdAll' {α n} (bdTerm : L.Term (α ⊕ Fin 0)) (φ : L.Formula (α ⊕ (Vars1 n))) : L.Formula α :=
  let bd := (var (.inl (Sum.inr (.fv1)))).le $ bdTerm.relabel (Sum.map .inl id)
  iAlls' $ bd ⟹ φ

-- TODO: there should only be Lt constructors in Complexity
-- and iBd should be an alias to iBdLt with term + 1
def iBdAllLt' {α n} (bdTerm : L.Term (α ⊕ Fin 0)) (φ : L.Formula (α ⊕ (Vars1 n))) : L.Formula α :=
  let bd := (var (.inl (Sum.inr (.fv1)))).lt $ bdTerm.relabel (Sum.map .inl id)
  iAlls' $ bd ⟹ φ

def iBdExNum'
  {α n}
  (bdTerm : zambella.Term (α ⊕ Fin 0))
  (φ : zambella.Formula (α ⊕ (Vars1 n)))
  : zambella.Formula α :=
  iBdEx' bdTerm $ (var $ Sum.inl $ Sum.inr $ .fv1).IsNum ⊓ φ

def iBdExStr'
  {α n}
  (bdTerm : zambella.Term (α ⊕ Fin 0))
  (φ : zambella.Formula (α ⊕ (Vars1 n)))
  : zambella.Formula α :=
  iBdEx' bdTerm $ (var $ Sum.inl $ Sum.inr $ .fv1).IsStr ⊓ φ

def iBdAllNum'
  {α n}
  (bdTerm : zambella.Term (α ⊕ Fin 0))
  (φ : zambella.Formula (α ⊕ (Vars1 n)))
  : zambella.Formula α :=
  iBdAll' bdTerm $ (var $ Sum.inl $ Sum.inr $ .fv1).IsNum ⟹ φ

def iBdAllNumLt'
  {α n}
  (bdTerm : zambella.Term (α ⊕ Fin 0))
  (φ : zambella.Formula (α ⊕ (Vars1 n)))
  : zambella.Formula α :=
  iBdAllLt' bdTerm $ (var $ Sum.inl $ Sum.inr $ .fv1).IsNum ⟹ φ



open Lean Elab Tactic

theorem iBdEx'.relabelEquiv
  {α β n} (bdTerm : L.Term (α ⊕ Fin 0)) (φ : L.Formula (α ⊕ (Vars1 n)))
  (f : α ≃ β)
  : relabelEquiv f (iBdEx' bdTerm φ)
    = iBdEx'
        (Term.relabelEquiv (f.sumCongr (_root_.Equiv.refl (Fin 0))) bdTerm)
        (relabelEquiv (f.sumCongr (_root_.Equiv.refl (Vars1 n))) φ) :=
by
  unfold iBdEx'
  rw [relabelEquiv.iExs']
  congr
  rw [relabelEquiv.inf]
  congr
  · unfold Term.le Relations.boundedFormula₂ Relations.boundedFormula
    rw [relabelEquiv.rel]
    congr
    funext x
    simp only [Term.relabelEquiv_apply, Term.relabel_relabel]
    fin_cases x
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Term.relabel.eq_1, Sum.map_inl,
      Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inr, id_eq]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Term.relabel_relabel, Sum.map_comp_map, Function.comp_id]
      congr 1
      funext y
      cases y <;> rfl

theorem iBdAll'.relabelEquiv
  {α β n} (bdTerm : L.Term (α ⊕ Fin 0)) (φ : L.Formula (α ⊕ (Vars1 n)))
  (f : α ≃ β)
  : relabelEquiv f (iBdAll' bdTerm φ)
    = iBdAll'
        (Term.relabelEquiv (f.sumCongr (_root_.Equiv.refl (Fin 0))) bdTerm)
        (relabelEquiv (f.sumCongr (_root_.Equiv.refl (Vars1 n))) φ) :=
by
  unfold iBdAll'
  rw [relabelEquiv.iAlls']
  congr
  rw [relabelEquiv.imp]
  congr
  · unfold Term.le Relations.boundedFormula₂ Relations.boundedFormula
    rw [relabelEquiv.rel]
    congr
    funext x
    simp only [Term.relabelEquiv_apply, Term.relabel_relabel]
    fin_cases x
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Term.relabel.eq_1, Sum.map_inl,
      Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inr, id_eq]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Term.relabel_relabel, Sum.map_comp_map, Function.comp_id]
      congr 1
      funext y
      cases y <;> rfl


end IsOrdered

end FirstOrder.Language.Formula
