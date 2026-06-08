/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

import Mathlib.ModelTheory.Syntax

import LeanPool.FormalizationOfBoundedArithmetic.IsEnum

/-!
# LeanPool.FormalizationOfBoundedArithmetic.Syntax
-/

namespace FirstOrder
namespace Language

universe u
variable {L : Language}
variable {α β : Type u} {n : Nat}

namespace BoundedFormula

/-- Computable finite supremum over an explicitly enumerated type. -/
def iSup' [enum : IsEnum β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  (enum.toList.map f).foldr (· ⊔ ·) ⊥

/-- Computable finite infimum over an explicitly enumerated type. -/
def iInf' [enum : IsEnum β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  (enum.toList.map f).foldr (· ⊓ ·) ⊤

end BoundedFormula

namespace Formula

/-- Computable finite universal closure over an explicitly enumerated type. -/
def iAlls' [enum : IsEnum β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  (BoundedFormula.relabel (fun a => Sum.map id enum.toIdx a) φ).alls

/-- Computable finite existential closure over an explicitly enumerated type. -/
def iExs' [enum : IsEnum β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  (BoundedFormula.relabel (fun a => Sum.map id enum.toIdx a) φ).exs

/-- Computable finite unique-existence formula over an explicitly enumerated type. -/
def iExsUnique' [enum : IsEnum β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  iExs' <| φ ⊓ iAlls'
    ((φ.relabel (fun a => Sum.elim (.inl ∘ .inl) .inr a)).imp <|
      .iInf' fun g => Term.equal (var (.inr g)) (var (.inl (.inr g))))

/-- Computable finite supremum for formulas over an explicitly enumerated type. -/
def iSup' [enum : IsEnum α] (f : α → L.Formula β) : L.Formula β :=
  BoundedFormula.iSup' f

/-- Computable finite infimum for formulas over an explicitly enumerated type. -/
def iInf' [enum : IsEnum α] (f : α → L.Formula β) : L.Formula β :=
  BoundedFormula.iInf' f

end Formula


namespace BoundedFormula


namespace relabelEquiv

@[simp]
theorem falsum {α β} (g : α ≃ β) {k} :
    (falsum : L.BoundedFormula α k).relabelEquiv g = falsum :=
  rfl

@[simp]
theorem imp {α β} (g : α ≃ β) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabelEquiv g = (φ.relabelEquiv g).imp (ψ.relabelEquiv g) :=
  rfl

@[simp]
theorem not {α β} (g : α ≃ β) {k} (φ : L.BoundedFormula α k) :
    φ.not.relabelEquiv g = (φ.relabelEquiv g).not :=
  rfl

@[simp]
theorem nf {α β} (g : α ≃ β) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊓ ψ).relabelEquiv g = (φ.relabelEquiv g) ⊓ (ψ.relabelEquiv g) :=
  rfl

@[simp]
theorem sup {α β} (g : α ≃ β) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊔ ψ).relabelEquiv g = (φ.relabelEquiv g) ⊔ (ψ.relabelEquiv g) :=
  rfl

@[simp]
theorem rel {L : Language} {a b} {n} (g : a ≃ b) {k} {R : L.Relations k}
    {ts : Fin k -> L.Term (a ⊕ Fin n)} :
    ((BoundedFormula.rel R ts).relabelEquiv g : L.BoundedFormula b n) =
      (BoundedFormula.rel R (fun i =>
        (ts i).relabel (Sum.map g id : a ⊕ Fin n -> b ⊕ Fin n)) :
          L.BoundedFormula b n) :=
by
  rfl

@[simp]
theorem eq {L : Language} {a b} {n} (g : a ≃ b) {t1 t2 : L.Term (a ⊕ Fin n)}
  : ((t1 =' t2).relabelEquiv g : L.BoundedFormula b n)
    =
      (
        (t1.relabel (Sum.map g id : a ⊕ Fin n -> b ⊕ Fin n)
        =' t2.relabel (Sum.map g id : a ⊕ Fin n -> b ⊕ Fin n)
        ) : L.BoundedFormula b n
      ) :=
by
  rfl

theorem bdEqual {L : Language} {a b} {n} (g : a ≃ b) {t1 t2 : L.Term (a ⊕ Fin n)}
  : ((t1 =' t2).relabelEquiv g)
    =
    (t1.relabel (Sum.map g id)) =' (t2.relabel (Sum.map g id)) :=
by
  rfl

-- TODO: this was very hard to prove. simp sets of Equiv and of mapTermRel are bad.
theorem comp_inv {L : Language} {α β} {m} {φ : L.BoundedFormula α m} (f : α ≃ β)
  : (relabelEquiv f.symm ((relabelEquiv f) φ)) = φ :=
by
  unfold relabelEquiv mapTermRelEquiv
  dsimp only [Equiv.coe_refl, Equiv.coe_fn_mk]
  rw [mapTermRel_mapTermRel]
  unfold Function.comp
  unfold Equiv.sumCongr
  simp only [Equiv.coe_refl, _root_.Equiv.symm_symm, Equiv.refl_symm, Term.relabelEquiv_apply,
    Equiv.coe_fn_mk, Term.relabel_relabel, Sum.map_comp_map, _root_.Equiv.symm_comp_self,
    Function.comp_id, Sum.map_id_id, Term.relabel_id_eq_id, id_eq]
  apply mapTermRel_id_id_id

end relabelEquiv

namespace relabel

@[simp]
theorem sup {L : Language} {α β} {n} (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊔ ψ).relabel g = (φ.relabel g) ⊔ (ψ.relabel g) :=
  rfl

@[simp]
theorem inf {L : Language} {α β} {n} (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊓ ψ).relabel g = (φ.relabel g) ⊓ (ψ.relabel g) :=
  rfl

end relabel

namespace relabelEquiv

@[simp]
theorem all {α β} (g : α ≃ β) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.all.relabelEquiv g = (φ.relabelEquiv g).all := by
  rw [relabelEquiv]
  rw [mapTermRelEquiv]
  rw [relabelEquiv]
  rw [mapTermRelEquiv]
  simp only [Equiv.coe_refl, Equiv.refl_symm, Equiv.coe_fn_mk]
  conv => lhs; unfold mapTermRel
  simp

@[simp]
theorem ex {α β} (g : α ≃ β) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.ex.relabelEquiv g = (φ.relabelEquiv g).ex := by
  simp only [BoundedFormula.ex, BoundedFormula.not]
  simp only [relabelEquiv.imp, all, imp.injEq, all.injEq, true_and, Bot.bot]
  constructor
  · simp only [relabelEquiv.falsum]
  · simp only [relabelEquiv.falsum]


@[simp]
theorem alls {α β} (g : α ≃ β) {k} (φ : L.BoundedFormula α k) :
    φ.alls.relabelEquiv g = (φ.relabelEquiv g).alls := by
  induction k with
  | zero =>
    unfold BoundedFormula.alls
    simp only
  | succ m ih =>
    apply ih


@[simp]
theorem exs {α β} (g : α ≃ β) {k} (φ : L.BoundedFormula α k) :
    φ.exs.relabelEquiv g = (φ.relabelEquiv g).exs := by
  induction k with
  | zero =>
    unfold BoundedFormula.exs
    simp only
  | succ m ih =>
    apply ih

theorem relabelAux_sumCongr [enum : IsEnum β] (g : α ≃ γ) (k : ℕ) :
    ∀ x : (α ⊕ β) ⊕ Fin k,
      (g.sumCongr (_root_.Equiv.refl (Fin (enum.size + k))))
          (BoundedFormula.relabelAux (fun a : α ⊕ β => Sum.map id enum.toIdx a) k x)
        = BoundedFormula.relabelAux (fun a : γ ⊕ β => Sum.map id enum.toIdx a) k
          (((g.sumCongr (_root_.Equiv.refl β)).sumCongr (_root_.Equiv.refl (Fin k))) x) := by
  intro x
  cases x with
  | inl ab =>
      cases ab with
      | inl a =>
          simp [BoundedFormula.relabelAux, Equiv.sumCongr, Equiv.sumAssoc]
      | inr b =>
          simp [BoundedFormula.relabelAux, Equiv.sumCongr, Equiv.sumAssoc]
  | inr i =>
      simp [BoundedFormula.relabelAux, Equiv.sumCongr, Equiv.sumAssoc]

theorem relabel_relabelSum [enum : IsEnum β] (g : α ≃ γ) :
    ∀ {k} (φ : L.BoundedFormula (α ⊕ β) k),
      BoundedFormula.relabelEquiv g
          (BoundedFormula.relabel (fun a : α ⊕ β => Sum.map id enum.toIdx a) φ)
        = BoundedFormula.relabel (fun a : γ ⊕ β => Sum.map id enum.toIdx a)
          (BoundedFormula.relabelEquiv (Equiv.sumCongr g (_root_.Equiv.refl β)) φ) := by
  intro k φ
  have hterm :
      ∀ {n} (t : L.Term ((α ⊕ β) ⊕ Fin n)),
        (Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl (Fin (enum.size + n)))))
            (Term.relabel (BoundedFormula.relabelAux
              (fun a : α ⊕ β => Sum.map id enum.toIdx a) n) t)
          =
        Term.relabel (BoundedFormula.relabelAux
            (fun a : γ ⊕ β => Sum.map id enum.toIdx a) n)
            ((Term.relabelEquiv
              ((g.sumCongr (_root_.Equiv.refl β)).sumCongr (_root_.Equiv.refl (Fin n)))) t) := by
    intro n t
    have hfun :
        ((g.sumCongr (_root_.Equiv.refl (Fin (enum.size + n)))) ∘
            BoundedFormula.relabelAux (fun a : α ⊕ β => Sum.map id enum.toIdx a) n)
          =
        (BoundedFormula.relabelAux (fun a : γ ⊕ β => Sum.map id enum.toIdx a) n ∘
          ((g.sumCongr (_root_.Equiv.refl β)).sumCongr (_root_.Equiv.refl (Fin n)))) := by
      funext x
      exact relabelAux_sumCongr g n x
    simpa only [Term.relabelEquiv_apply, Term.relabel_relabel] using
      congrArg (fun h => Term.relabel h t) hfun
  induction φ with
  | falsum => rfl
  | equal t1 t2 =>
      dsimp [BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv,
        BoundedFormula.relabel, BoundedFormula.mapTermRel, Term.relabelEquiv_apply,
        Term.relabel_relabel]
      congr 1
      · exact hterm t1
      · exact hterm t2
  | rel R ts =>
      dsimp [BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv,
        BoundedFormula.relabel, BoundedFormula.mapTermRel, Term.relabelEquiv_apply,
        Term.relabel_relabel]
      congr 1
      funext i
      exact hterm (ts i)
  | imp φ ψ ihφ ihψ =>
      simp only [relabel_imp, imp, imp.injEq]
      exact ⟨ihφ, ihψ⟩
  | all φ ih =>
      simp only [relabel_all, Nat.add_eq, all, all.injEq]
      exact ih

@[simp]
theorem iExs' {α β γ} [henum : IsEnum β] (g : α ≃ γ)
    (φ : L.Formula (α ⊕ β)) :
    BoundedFormula.relabelEquiv g (φ.iExs')
    = Formula.iExs' (φ.relabelEquiv (Equiv.sumCongr g (_root_.Equiv.refl β))) :=
by
  unfold Formula.iExs'
  rw [exs]
  congr
  exact relabel_relabelSum g φ

@[simp]
theorem iAlls' {α β γ} [henum : IsEnum β] (g : α ≃ γ)
    (φ : L.Formula (α ⊕ β)) :
    BoundedFormula.relabelEquiv g (φ.iAlls')
    = Formula.iAlls' (φ.relabelEquiv (Equiv.sumCongr g (_root_.Equiv.refl β))) :=
by
  unfold Formula.iAlls'
  rw [alls]
  congr
  exact relabel_relabelSum g φ

@[simp]
theorem inf {L : Language} {α β} (g : α ≃ β) {k} (φ ψ : L.BoundedFormula α k) :
    (φ ⊓ ψ).relabelEquiv g = (φ.relabelEquiv g) ⊓ (ψ.relabelEquiv g) :=
  rfl


end relabelEquiv

end BoundedFormula
end Language
end FirstOrder
