/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Syntax

import LeanPool.FormalizationOfBoundedArithmetic.DisplayedVariables
import LeanPool.FormalizationOfBoundedArithmetic.Order
import LeanPool.FormalizationOfBoundedArithmetic.LanguagePeano
import LeanPool.FormalizationOfBoundedArithmetic.LanguageZambella
import LeanPool.FormalizationOfBoundedArithmetic.Register

/-!
# LeanPool.FormalizationOfBoundedArithmetic.Complexity
-/

open FirstOrder Language

universe u
variable {L : Language} {α β : Type u} {n : Nat}

namespace FirstOrder.Language

namespace BoundedFormula.IsAtomic
variable {φ : L.BoundedFormula α n}

namespace relabelEquiv

theorem mpr {f : α ≃ β} (h : φ.IsAtomic)
  : (φ.relabelEquiv f).IsAtomic
:=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

theorem mp {f : α ≃ β} (h : (φ.relabelEquiv f).IsAtomic)
  : φ.IsAtomic :=
by
  cases φ <;> (try cases h) <;> constructor

end relabelEquiv

@[delta0_simps]
theorem relabelEquiv {f : α ≃ β} :
  (φ.relabelEquiv f).IsAtomic <-> φ.IsAtomic :=
  ⟨relabelEquiv.mp, relabelEquiv.mpr⟩
end BoundedFormula.IsAtomic

namespace Formula.IsAtomic
open BoundedFormula

@[delta0_simps]
theorem display1 {n1} {phi : L.Formula (Vars1 n1)} :
  phi.display1.IsAtomic <-> phi.IsAtomic :=
by
  unfold Formula.display1
  rw [IsAtomic.relabelEquiv]

@[delta0_simps]
theorem display2 {n1 n2} {phi : L.Formula (Vars2 n1 n2)} :
  phi.display2.IsAtomic <-> phi.IsAtomic :=
by
  unfold Formula.display2
  rw [IsAtomic.relabelEquiv]

@[delta0_simps]
theorem display3 {n1 n2 n3} {phi : L.Formula (Vars3 n1 n2 n3)} :
  phi.display3.IsAtomic <-> phi.IsAtomic :=
by
  unfold Formula.display3
  rw [IsAtomic.relabelEquiv]

end Formula.IsAtomic

namespace BoundedFormula.IsQF

namespace imp

@[delta0_simps]
theorem mpr {L : Language} {α} {m} {φ ψ : L.BoundedFormula α m} :
  (φ.imp ψ).IsQF <-> (φ.IsQF ∧ ψ.IsQF) :=
by
  constructor
  · intro h
    constructor
    · cases h with
      | of_isAtomic h' => cases h'
      | imp pre post => exact pre
    · cases h with
      | of_isAtomic h' => cases h'
      | imp pre post => exact post
  · intro h
    apply IsQF.imp h.left h.right

end imp

namespace relabelEquiv

@[delta0_simps]
theorem mp {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m}
  (f : α ≃ β)
  (h : φ.IsQF)
  : (φ.relabelEquiv f).IsQF :=
by
  induction φ with
  | falsum =>
    constructor
  | equal lhs rhs =>
    simp only [relabelEquiv, mapTermRelEquiv, Equiv.coe_refl, Equiv.refl_symm, Equiv.coe_fn_mk,
      mapTermRel, Term.relabelEquiv_apply]
    constructor; constructor
  | rel R ts =>
    simp only [relabelEquiv, mapTermRelEquiv, Equiv.coe_refl, Equiv.refl_symm, Equiv.coe_fn_mk,
      mapTermRel, Term.relabelEquiv_apply]
    constructor; constructor
  | imp pre post hind_pre hind_post =>
    cases h with
    | of_isAtomic hh => cases hh
    | imp hpre hpost =>
      rw [relabelEquiv.imp]
      apply IsQF.imp
      · exact hind_pre hpre
      · exact hind_post hpost
  | all f f_ih =>
    cases h with
    | of_isAtomic h' => cases h'

@[delta0_simps]
theorem mpr {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β)
  (h : (φ.relabelEquiv f).IsQF)
  : φ.IsQF :=
by
  have h' : relabelEquiv f.symm ((relabelEquiv f) φ) = φ := relabelEquiv.comp_inv f
  rw [<- h']
  apply relabelEquiv.mp
  exact h

end relabelEquiv

@[delta0_simps]
theorem relabelEquiv {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) :
  (φ.relabelEquiv f).IsQF <-> φ.IsQF := ⟨IsQF.relabelEquiv.mpr f, IsQF.relabelEquiv.mp f⟩


end BoundedFormula.IsQF




-- Definition 3.7, page 36 of draft (47 of pdf)
namespace BoundedFormula

/-- Open formulas are quantifier-free bounded formulas. -/
abbrev IsOpen (formula : L.BoundedFormula α n)
  := IsQF formula
namespace IsOpen
variable {phi : L.BoundedFormula α n}

@[delta0_simps]
theorem equal (t1 t2 : L.Term (α ⊕ Fin n))
  : (t1.bdEqual t2).IsOpen :=
by
  constructor
  apply IsAtomic.equal

namespace imp
namespace mpr

@[delta0_simps]
theorem left {psi : _}
  : (phi.imp psi).IsOpen -> phi.IsOpen :=
by
  intro h
  -- TODO: order of constructors in IsQF should be reversed,
  -- so that `constructor` here works!
  cases h with
  | of_isAtomic h => cases h
  | imp p q => exact p

@[delta0_simps]
theorem right {psi : _}
  : (phi.imp psi).IsOpen -> psi.IsOpen :=
by
  intro h
  cases h with
  | of_isAtomic h => cases h
  | imp p q => exact q

end mpr
end imp

@[delta0_simps]
theorem not
  : phi.not.IsOpen <-> phi.IsOpen :=
by
  constructor <;> (unfold BoundedFormula.not; intro h)
  · exact imp.mpr.left h
  · apply IsQF.imp
    · assumption
    · exact isQF_bot

@[delta0_simps]
theorem relabelEquiv {f : α ≃ β}
  : (phi.relabelEquiv f).IsOpen <-> phi.IsOpen :=
by
  apply IsQF.relabelEquiv

end IsOpen
end BoundedFormula

namespace Formula.IsOpen
open BoundedFormula.IsOpen

@[delta0_simps]
theorem display1 {n1} {phi : L.Formula (Vars1 n1)} :
    phi.display1.IsOpen <-> phi.IsOpen := by
  unfold Formula.display1
  rw [relabelEquiv]

@[delta0_simps]
theorem display2 {n1 n2} {phi : L.Formula (Vars2 n1 n2)} :
    phi.display2.IsOpen <-> phi.IsOpen := by
  unfold Formula.display2
  rw [relabelEquiv]

@[delta0_simps]
theorem display3 {n1 n2 n3} {phi : L.Formula (Vars3 n1 n2 n3)} :
    phi.display3.IsOpen <-> phi.IsOpen := by
  unfold Formula.display3
  rw [relabelEquiv]

end Formula.IsOpen



variable {L : Language} [IsOrdered L] {a : Type u}
open BoundedFormula Formula

-- Definition 3.7, page 36 of draft (47 of pdf)
-- + Definition 3.6, page 35 of draft (46 of pdf)
-- fix level of `a` to 0, because level of `Vars` was fixed to 0!
namespace BoundedFormula

/-- Delta-zero formulas, built from quantifier-free formulas and bounded number quantifiers. -/
inductive IsDelta0 :
    ∀ {a : Type} {n : Nat}, L.BoundedFormula a n -> Prop
| bdEx {a : Type} {n : FvName}
  {phi : L.Formula (a ⊕ (Vars1 n))}
  (t : L.Term (a ⊕ Fin 0))
  : IsDelta0 phi -> (IsDelta0 <| iBdEx' t phi)
| bdAll {a : Type} {n : FvName}
  {phi : L.Formula (a ⊕ (Vars1 n))}
  (t : L.Term (a ⊕ Fin 0))
  : IsDelta0 phi -> (IsDelta0 <| iBdAll' t phi)
| imp {a : Type} {n : Nat} {phi1 phi2 : L.BoundedFormula a n}
  : IsDelta0 phi1 -> IsDelta0 phi2 -> IsDelta0 (phi1.imp phi2)
| of_isQF {a : Type} {n : Nat} {phi : L.BoundedFormula a n}
  : BoundedFormula.IsQF phi -> IsDelta0 phi

end BoundedFormula

namespace IsDelta0

@[delta0_simps]
theorem bot {a n} : (⊥ : L.BoundedFormula a n).IsDelta0  := by
  constructor
  exact isQF_bot

@[delta0_simps]
theorem equal {a n} (t1 t2 : L.Term (a ⊕ Fin n))
  : (t1.bdEqual t2).IsDelta0 :=
by
  constructor
  constructor
  apply IsAtomic.equal

namespace of_open

theorem imp {a n} {phi psi : L.BoundedFormula a n} (h : phi.IsOpen)
  : (phi.imp psi).IsDelta0 <-> (phi.IsDelta0 ∧ psi.IsDelta0) :=
by
  constructor
  · intro h
    cases h with
    | imp p q =>
      exact ⟨p, q⟩
    | of_isQF q =>
      rw [IsQF.imp.mpr] at q
      constructor <;>
        apply IsDelta0.of_isQF
      · exact q.left
      · exact q.right
    | bdEx phi t =>
      cases h with
      | of_isAtomic h' =>
        cases h' with
  · intro h
    exact IsDelta0.imp h.left h.right

end of_open

namespace of_notfalsum

theorem imp {a n} {phi psi : L.BoundedFormula a n} (h : psi ≠ falsum)
  : (phi.imp psi).IsDelta0 <-> (phi.IsDelta0 ∧ psi.IsDelta0) :=
by
  constructor
  · intro h'
    cases h' with
    | imp p q =>
      exact ⟨p, q⟩
    | of_isQF q =>
      rw [IsQF.imp.mpr] at q
      constructor <;>
        apply IsDelta0.of_isQF
      · exact q.left
      · exact q.right
    | bdEx phi t =>
      simp only [Bot.bot, ne_eq, not_true_eq_false] at h
  · intro h
    exact IsDelta0.imp h.left h.right

end of_notfalsum


@[delta0_simps]
theorem neq {a n} (t1 t2 : L.Term (a ⊕ Fin n))
  : (t1 ≠' t2).IsDelta0 :=
by
  constructor
  · apply equal
  · apply bot

namespace of_open

theorem not {a n} {phi : L.BoundedFormula a n} (h : phi.IsOpen)
  : phi.not.IsDelta0 <-> phi.IsDelta0 :=
by
  unfold BoundedFormula.not
  rw [of_open.imp h]
  exact ⟨fun h => h.left, fun h => ⟨h, IsDelta0.bot⟩⟩

end of_open

namespace relabelEquiv

theorem mpAux {a b n} {phi : peano.BoundedFormula a n}
  (g : a ≃ b)
  (h : phi.IsDelta0)
  : (phi.relabelEquiv g).IsDelta0 :=
by
  induction h generalizing b with
  | bdEx t hphi ih =>
    rw [iBdEx'.relabelEquiv]
    constructor
    exact ih (g.sumCongr (_root_.Equiv.refl _))
  | bdAll t hphi ih =>
    rw [iBdAll'.relabelEquiv]
    constructor
    exact ih (g.sumCongr (_root_.Equiv.refl _))
  | imp pre post ihpre ihpost =>
    rw [relabelEquiv.imp]
    constructor
    · exact ihpre g
    · exact ihpost g
  | of_isQF f =>
    exact IsDelta0.of_isQF (BoundedFormula.IsQF.relabelEquiv.mp g f)

theorem gSumCongr
  {a b c}
  {phi : peano.Formula (a ⊕ c)}
  (g : a ≃ b)
  (h : phi.IsDelta0)
  : ((relabelEquiv (g.sumCongr (_root_.Equiv.refl c))) phi).IsDelta0 :=
  relabelEquiv.mpAux (g.sumCongr (_root_.Equiv.refl c)) h


@[delta0_simps]
theorem mp {a b} {phi : peano.Formula a}
  (g : a ≃ b)
  (h : phi.IsDelta0)
  : (phi.relabelEquiv g).IsDelta0 :=
  relabelEquiv.mpAux g h


@[delta0_simps]
theorem mpr {α β} {φ : peano.Formula α} (f : α ≃ β)
  (h : (φ.relabelEquiv f).IsDelta0)
  : φ.IsDelta0 :=
by
  have h' : relabelEquiv f.symm ((relabelEquiv f) φ) = φ := relabelEquiv.comp_inv f
  rw [<- h']
  apply relabelEquiv.mp
  exact h

end relabelEquiv

@[delta0_simps]
theorem relabelEquiv {α β} (φ : peano.Formula α) {f : α ≃ β} :
  (φ.relabelEquiv f).IsDelta0 <-> φ.IsDelta0 :=
  ⟨IsDelta0.relabelEquiv.mpr f, IsDelta0.relabelEquiv.mp f⟩


@[delta0_simps]
theorem display1 {n} (phi : peano.Formula (Vars1 n)) :
  phi.display1.IsDelta0 <-> phi.IsDelta0 :=
  IsDelta0.relabelEquiv phi

@[delta0_simps]
theorem display2 {n1 n2} (phi : peano.Formula (Vars2 n1 n2)) :
  phi.display2.IsDelta0 <-> phi.IsDelta0 :=
  IsDelta0.relabelEquiv phi

@[delta0_simps]
theorem display3 {n1 n2 n3} (phi : peano.Formula (Vars3 n1 n2 n3)) :
  phi.display3.IsDelta0 <-> phi.IsDelta0 :=
  IsDelta0.relabelEquiv phi

@[delta0_simps]
theorem flip {a b} (phi : peano.Formula (a ⊕ b)) :
  phi.flip.IsDelta0 <-> phi.IsDelta0 :=
  IsDelta0.relabelEquiv phi

end IsDelta0




-- only bounded number quantifiers allowed. and free string vars.
-- p. 82 of pdf of Logical Foundatoin release
namespace BoundedFormula

/-- Sigma-zero-B formulas in the two-sorted Zambella language. -/
inductive IsSigma0B {a : Type} :
    {n : Nat} -> zambella.BoundedFormula a n -> Prop
| imp {phi1 phi2} (h1 : IsSigma0B phi1) (h2 : IsSigma0B phi2)
  : IsSigma0B (phi1.imp phi2)
| bdEx
  {n : FvName}
  (phi : zambella.Formula (a ⊕ (Vars1 n)))
  (t : zambella.Term (a ⊕ Fin 0))
  : IsSigma0B <| iBdEx' t
      ((rel ZambellaRel.isnum ![var <| Sum.inl <| Sum.inr <| .fv1]) ⊓ phi)
-- TODO: WHICH ONE IS REDUNDANT?
| bdAll
  {n : FvName}
  (phi : zambella.Formula (a ⊕ (Vars1 n)))
  (t : zambella.Term (a ⊕ Fin 0))
  : IsSigma0B <| iBdAllNum' t phi
| bdAllLt
  {n : FvName}
  (phi : zambella.Formula (a ⊕ (Vars1 n)))
  (t : zambella.Term (a ⊕ Fin 0))
  : IsSigma0B <| iBdAllLt' t
      ((rel ZambellaRel.isnum ![var <| Sum.inl <| Sum.inr <| .fv1]) ⊓ phi)
| of_isQF {phi} (h : IsQF phi) : IsSigma0B phi

end BoundedFormula

namespace Sigma0B

namespace relabelEquiv

theorem mpAux {a b n} {phi : zambella.BoundedFormula a n}
  (g : a ≃ b)
  (h : phi.IsSigma0B)
  : (phi.relabelEquiv g).IsSigma0B :=
by
  induction h generalizing b with
  | imp h1 h2 ih1 ih2 =>
    rw [relabelEquiv.imp]
    exact BoundedFormula.IsSigma0B.imp (ih1 g) (ih2 g)
  | bdEx phi t =>
    rw [iBdEx'.relabelEquiv]
    convert BoundedFormula.IsSigma0B.bdEx
      (phi.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
      (Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)) t) using 1
    simp only [Term.relabelEquiv_apply, relabelEquiv.nf, relabelEquiv.rel,
      Matrix.cons_val_fin_one, Term.relabel.eq_1, Sum.map_inl, Equiv.sumCongr_apply,
      Equiv.coe_refl, Sum.map_inr, id_eq]
    congr
    funext i
    fin_cases i
    rfl
  | bdAll phi t =>
    unfold iBdAllNum'
    rw [iBdAll'.relabelEquiv]
    convert BoundedFormula.IsSigma0B.bdAll
      (phi.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
      (Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)) t) using 1
    unfold Term.IsNum Relations.boundedFormula₁ Relations.boundedFormula
    rw [relabelEquiv.imp]
    congr
    rw [relabelEquiv.rel]
    congr
    funext i
    fin_cases i
    rfl
  | bdAllLt phi t =>
    rw [iBdAllLt'.relabelEquiv]
    convert BoundedFormula.IsSigma0B.bdAllLt
      (phi.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
      (Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)) t) using 1
    simp only [Term.relabelEquiv_apply, relabelEquiv.nf, relabelEquiv.rel,
      Matrix.cons_val_fin_one, Term.relabel.eq_1, Sum.map_inl, Equiv.sumCongr_apply,
      Equiv.coe_refl, Sum.map_inr, id_eq]
    congr
    funext i
    fin_cases i
    rfl
  | of_isQF h =>
    exact BoundedFormula.IsSigma0B.of_isQF (BoundedFormula.IsQF.relabelEquiv.mp g h)

theorem mprAux {a b n} {phi : zambella.BoundedFormula a n}
  (g : a ≃ b)
  (h : (phi.relabelEquiv g).IsSigma0B)
  : phi.IsSigma0B :=
by
  have h' : relabelEquiv g.symm ((relabelEquiv g) phi) = phi := relabelEquiv.comp_inv g
  rw [<- h']
  exact relabelEquiv.mpAux g.symm h

end relabelEquiv

@[delta0_simps]
theorem relabelEquiv {a b} {g : a ≃ b} (phi : zambella.Formula a) :
  (phi.relabelEquiv g).IsSigma0B <-> phi.IsSigma0B :=
  ⟨relabelEquiv.mprAux g, relabelEquiv.mpAux g⟩

/-- Discharge a `Sigma0B` closure lemma for a `Formula.*` reshaping. -/
macro "sigma0bViaRelabel " target:ident : tactic =>
  `(tactic| (unfold $target; apply relabelEquiv))

@[delta0_simps]
nonrec theorem display1 {n1 : FvName}
  (phi : zambella.Formula (Vars1 n1))
  :
  phi.display1.IsSigma0B <-> phi.IsSigma0B :=
by
  sigma0bViaRelabel display1

@[delta0_simps]
nonrec theorem display2 {n1 n2 : FvName}
  (phi : zambella.Formula (Vars2 n1 n2))
  :
  phi.display2.IsSigma0B <-> phi.IsSigma0B :=
by
  sigma0bViaRelabel display2

@[delta0_simps]
nonrec theorem display3 {n1 n2 n3 : FvName}
  (phi : zambella.Formula (Vars3 n1 n2 n3))
  :
  phi.display3.IsSigma0B <-> phi.IsSigma0B :=
by
  sigma0bViaRelabel display3

@[delta0_simps]
nonrec theorem display4 {n1 n2 n3 n4 : FvName}
  (phi : zambella.Formula (Vars4 n1 n2 n3 n4))
  :
  phi.display4.IsSigma0B <-> phi.IsSigma0B :=
by
  sigma0bViaRelabel display4

@[delta0_simps]
nonrec theorem displaySwapleft {n1 n2 n3 : FvName}
  (phi : zambella.Formula (Vars1 n1 ⊕ Vars2 n2 n3))
  :
  phi.displaySwapleft.IsSigma0B <-> phi.IsSigma0B :=
by
  sigma0bViaRelabel displaySwapleft

@[delta0_simps]
nonrec theorem displaySwapleft' {n1 n2 n3 : FvName}
  (phi : zambella.Formula (Vars1 n1 ⊕ Vars2 n2 n3))
  :
  phi.displaySwapleft'.IsSigma0B <-> phi.IsSigma0B :=
by
  sigma0bViaRelabel displaySwapleft'

@[delta0_simps]
nonrec theorem rotate21 {n1 n2 : FvName}
  (phi : zambella.Formula (Vars2 n1 n2))
  :
  phi.rotate21.IsSigma0B <-> phi.IsSigma0B :=
by
  sigma0bViaRelabel rotate21

@[delta0_simps]
nonrec theorem rotate213 {n1 n2 n3 : FvName}
  (phi : zambella.Formula (Vars3 n1 n2 n3))
  :
  phi.rotate213.IsSigma0B <-> phi.IsSigma0B :=
by
  sigma0bViaRelabel rotate213

@[delta0_simps]
nonrec theorem rotate231 {n1 n2 n3 : FvName}
  (phi : zambella.Formula (Vars3 n1 n2 n3))
  :
  phi.rotate231.IsSigma0B <-> phi.IsSigma0B :=
by
  sigma0bViaRelabel rotate231

@[delta0_simps]
nonrec theorem flip {a b}
  (phi : zambella.Formula (a ⊕ b))
  :
  phi.flip.IsSigma0B <-> phi.IsSigma0B :=
by
  sigma0bViaRelabel Formula.flip

end Sigma0B

/-- Simplify complexity side conditions in a hypothesis. -/
syntax (name := simpComplexity) "simpComplexity" " at " (ppSpace ident)? : tactic

macro_rules
| `(tactic| simpComplexity at $h:ident) =>
  `(tactic|
  conv at $h =>
    conv =>
      lhs
      simp only [delta0_simps]
    -- this has to work! the `IsOpen` goal has to reduce to `True`.
    rw [forall_const]
  )


end FirstOrder.Language
