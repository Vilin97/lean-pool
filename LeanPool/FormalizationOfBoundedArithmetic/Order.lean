/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Order
import Mathlib.Tactic.FinCases

import LeanPool.FormalizationOfBoundedArithmetic.DisplayedVariables
import LeanPool.FormalizationOfBoundedArithmetic.Syntax
import LeanPool.FormalizationOfBoundedArithmetic.LanguageZambella

/-!
# LeanPool.FormalizationOfBoundedArithmetic.Order
-/

namespace FirstOrder.Language.Formula

open Language BoundedFormula

section IsOrdered
universe u
variable {L : Language} [IsOrdered L] {α : Type u}

variable {n r} (a b : L.BoundedFormula n r)


/-- Existential quantification bounded by a term. -/
def iBdEx' {α n} (bdTerm : L.Term (α ⊕ Fin 0))
    (φ : L.Formula (α ⊕ (Vars1 n))) : L.Formula α :=
  let bd := (var (.inl (Sum.inr (.fv1)))).le <| bdTerm.relabel (Sum.map .inl id)
  iExs' <| bd ⊓ φ

/-- Universal quantification bounded by a term. -/
def iBdAll' {α n} (bdTerm : L.Term (α ⊕ Fin 0))
    (φ : L.Formula (α ⊕ (Vars1 n))) : L.Formula α :=
  let bd := (var (.inl (Sum.inr (.fv1)))).le <| bdTerm.relabel (Sum.map .inl id)
  iAlls' <| bd ⟹ φ

-- TODO: there should only be Lt constructors in Complexity
-- and iBd should be an alias to iBdLt with term + 1
/-- Universal quantification bounded strictly by a term. -/
def iBdAllLt' {α n} (bdTerm : L.Term (α ⊕ Fin 0))
    (φ : L.Formula (α ⊕ (Vars1 n))) : L.Formula α :=
  let bd := (var (.inl (Sum.inr (.fv1)))).lt <| bdTerm.relabel (Sum.map .inl id)
  iAlls' <| bd ⟹ φ

/-- Existential quantification bounded by a term and guarded as numeric. -/
def iBdExNum'
  {α n}
  (bdTerm : zambella.Term (α ⊕ Fin 0))
  (φ : zambella.Formula (α ⊕ (Vars1 n)))
  : zambella.Formula α :=
  iBdEx' bdTerm <| (var <| Sum.inl <| Sum.inr <| .fv1).IsNum ⊓ φ

/-- Existential quantification bounded by a term and guarded as a string. -/
def iBdExStr'
  {α n}
  (bdTerm : zambella.Term (α ⊕ Fin 0))
  (φ : zambella.Formula (α ⊕ (Vars1 n)))
  : zambella.Formula α :=
  iBdEx' bdTerm <| (var <| Sum.inl <| Sum.inr <| .fv1).IsStr ⊓ φ

/-- Universal quantification bounded by a term and guarded as numeric. -/
def iBdAllNum'
  {α n}
  (bdTerm : zambella.Term (α ⊕ Fin 0))
  (φ : zambella.Formula (α ⊕ (Vars1 n)))
  : zambella.Formula α :=
  iBdAll' bdTerm <| (var <| Sum.inl <| Sum.inr <| .fv1).IsNum ⟹ φ

/-- Universal quantification strictly bounded by a term and guarded as numeric. -/
def iBdAllNumLt'
  {α n}
  (bdTerm : zambella.Term (α ⊕ Fin 0))
  (φ : zambella.Formula (α ⊕ (Vars1 n)))
  : zambella.Formula α :=
  iBdAllLt' bdTerm <| (var <| Sum.inl <| Sum.inr <| .fv1).IsNum ⟹ φ



open Lean Elab Tactic

namespace iBdEx'

theorem relabelEquiv
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
    · simp [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Term.relabel_relabel, Sum.map_comp_map, Function.comp_id, Equiv.sumCongr]
      congr 1

end iBdEx'

namespace iBdAll'

theorem relabelEquiv
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
    · simp [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Term.relabel_relabel, Sum.map_comp_map, Function.comp_id, Equiv.sumCongr]
      congr 1

end iBdAll'

namespace iBdAllLt'

theorem relabelEquiv
  {α β n} (bdTerm : L.Term (α ⊕ Fin 0)) (φ : L.Formula (α ⊕ (Vars1 n)))
  (f : α ≃ β)
  : relabelEquiv f (iBdAllLt' bdTerm φ)
    = iBdAllLt'
        (Term.relabelEquiv (f.sumCongr (_root_.Equiv.refl (Fin 0))) bdTerm)
        (relabelEquiv (f.sumCongr (_root_.Equiv.refl (Vars1 n))) φ) :=
by
  unfold iBdAllLt'
  rw [relabelEquiv.iAlls']
  congr
  rw [relabelEquiv.imp]
  congr
  · unfold Term.lt
    rw [BoundedFormula.relabelEquiv.inf]
    congr
    · unfold Term.le Relations.boundedFormula₂ Relations.boundedFormula
      rw [BoundedFormula.relabelEquiv.rel]
      congr
      funext x
      simp only [Term.relabelEquiv_apply, Term.relabel_relabel]
      fin_cases x <;> simp [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero, Term.relabel_relabel, Sum.map_comp_map,
        Function.comp_id, Equiv.sumCongr]
      congr 1
    · rw [BoundedFormula.relabelEquiv.not]
      congr
      unfold Term.le Relations.boundedFormula₂ Relations.boundedFormula
      rw [BoundedFormula.relabelEquiv.rel]
      congr
      funext x
      simp only [Term.relabelEquiv_apply, Term.relabel_relabel]
      fin_cases x <;> simp [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero, Term.relabel_relabel, Sum.map_comp_map,
        Function.comp_id, Equiv.sumCongr]
      congr 1

end iBdAllLt'

end IsOrdered

end FirstOrder.Language.Formula
