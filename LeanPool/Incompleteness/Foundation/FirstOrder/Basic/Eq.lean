/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.BinderNotation
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Semantics.Elementary
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Soundness

/-! # Eq -/


namespace Matrix

variable {α : Type*}

/-- Imported declaration from the Incompleteness formalization. -/
def iget [Inhabited α] (v : Fin k → α) (x : ℕ) : α := if h : x < k then v ⟨x, h⟩ else default

end Matrix

namespace LO

namespace FirstOrder

variable {L : Language} {μ : Type*} [Semiformula.Operator.Eq L]

namespace Theory

/-- Imported declaration from the Incompleteness formalization. -/
class Sub (T U : Theory L) where
  sub : T ⊆ U

section «lp_section_1»

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Eq.refl : SyntacticFormula L := “x | x = x”

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Eq.symm : SyntacticFormula L := “x y | x = y → y = x”

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Eq.trans : SyntacticFormula L := “x y z | x = y → y = z → x = z”

variable {L}

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Eq.funcExt {k} (f : L.Func k) : SyntacticFormula L :=
  (Matrix.conjVec fun i : Fin k ↦ “&i =
    &(k + i)”) ==> op(=).operator ![Semiterm.func f (fun i ↦ &i),
      Semiterm.func f (fun i ↦ &(k + i))]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Eq.relExt {k} (r : L.Rel k) : SyntacticFormula L :=
  (Matrix.conjVec fun i : Fin k ↦ “&i =
    &(k + i)”) ==> Semiformula.rel r (fun i ↦ &i) ==> Semiformula.rel r (fun i ↦ &(k + i))

/-- Imported declaration from the Incompleteness formalization. -/
inductive eqAxiom : Theory L
  | refl : eqAxiom (Eq.refl L)
  | symm : eqAxiom (Eq.symm L)
  | trans : eqAxiom (Eq.trans L)
  | funcExt {k} (f : L.Func k) : eqAxiom (Eq.funcExt f)
  | relExt {k} (r : L.Rel k) : eqAxiom (Eq.relExt r)

/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐄𝐐" => eqAxiom

lemma _root_.LO.FirstOrder.Theory.Eq.defeq :
    𝐄𝐐 = {Eq.refl L, Eq.symm L, Eq.trans L}
      ∪ Set.range (fun f : (k : ℕ) × L.Func k ↦ Eq.funcExt f.2)
      ∪ Set.range (fun f : (k : ℕ) × L.Rel k ↦ Eq.relExt f.2) := by
  ext φ; constructor
  · rintro ⟨⟩
    case refl => simp
    case symm => simp
    case trans => simp
    case funcExt k f =>
      left; right; exact ⟨⟨k, f⟩, rfl⟩
    case relExt k r =>
      right; exact ⟨⟨k, r⟩, rfl⟩
  · rintro (((rfl | rfl | rfl) | ⟨f, rfl⟩) | ⟨r, rfl⟩)
    · exact eqAxiom.refl
    · exact eqAxiom.symm
    · exact eqAxiom.trans
    · exact eqAxiom.funcExt _
    · exact eqAxiom.relExt _

@[simp] lemma _root_.LO.FirstOrder.Theory.EqAxiom.finite [L.Finite] : Set.Finite (𝐄𝐐 :
    Theory L) := by
  haveI : Fintype ((k : ℕ) × L.Func k) := Language.Finite.func
  haveI : Fintype ((k : ℕ) × L.Rel k) := Language.Finite.rel
  rw [Eq.defeq]
  simp [Set.finite_range]

end «lp_section_1»

end Theory

namespace Structure

namespace Eq

@[simp] lemma models_eqAxiom {M : Type u} [Nonempty M] [Structure L M] [Structure.Eq L M] :
    M ⊧ₘ* (𝐄𝐐 :
    Theory L) :=
  ⟨by
  intro σ h
  cases h <;> try { simp [models_def, Semiterm.val_func, Semiformula.eval_rel, *]; try simp_all }⟩

variable (L)

instance models_eqAxiom' (M : Type u) [Nonempty M] [Structure L M] [Structure.Eq L M] : M ⊧ₘ* (𝐄𝐐 :
    Theory L) := Structure.Eq.models_eqAxiom

variable {M : Type u} [Nonempty M] [Structure L M]

/-- Imported declaration from the Incompleteness formalization. -/
def eqv (a b : M) : Prop := (@Semiformula.Operator.Eq.eq L _).val ![a, b]

variable {L}

variable [H : M ⊧ₘ* (𝐄𝐐 : Theory L)]

open Semiterm Theory Semiformula

lemma eqv_refl (a : M) : eqv L a a := by
  have : M ⊧ₘ “x | x = x” := H.realize _ (Theory.eqAxiom.refl (L := L))
  simpa [eqv, models_def] using this (fun _ ↦ a)

lemma eqv_symm {a b : M} : eqv L a b → eqv L b a := by
  have : M ⊧ₘ “x y | x = y → y = x” := H.realize _ (Theory.eqAxiom.symm (L := L))
  simpa [eqv, models_def] using this (a :>ₙ fun _ ↦ b)

lemma eqv_trans {a b c : M} : eqv L a b → eqv L b c → eqv L a c := by
  have : M ⊧ₘ “x y z | x = y → y = z → x = z” := H.realize _ (Theory.eqAxiom.trans (L := L))
  simpa [eqv, models_def] using  this (a :>ₙ b :>ₙ fun _ ↦ c)

lemma eqv_funcExt {k} (f : L.Func k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    eqv L (func f v) (func f w) := by
  haveI : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  have :=
    H.realize _ (eqAxiom.funcExt f (L := L)) (fun x ↦ Matrix.iget (Matrix.vecAppend rfl v w) x)
  have : (∀ i, op(=).val ![v i, w i]) → op(=).val ![func f v, func f w] := by {
    simpa [models_def, Matrix.vecAppend_eq_ite, Semiterm.val_func, Matrix.iget,
      show ∀ i : Fin k, i < k + k from fun i ↦ lt_of_lt_of_le i.prop (by simp)] using
      H.realize _ (eqAxiom.funcExt f (L := L)) (fun x ↦ Matrix.iget (Matrix.vecAppend rfl v w) x) }
  exact this h

lemma eqv_relExt_aux {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v → rel r w := by
  haveI : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  have : (∀ i, op(=).val ![v i, w i]) → rel r v → rel r w := by {
    simpa [models_def, Matrix.vecAppend_eq_ite, Semiterm.val_func, eval_rel (r := r), Matrix.iget,
      show ∀ i : Fin k, i < k + k from fun i ↦ lt_of_lt_of_le i.prop (by simp)] using
      H.realize _ (eqAxiom.relExt r (L := L)) (fun x ↦ Matrix.iget (Matrix.vecAppend rfl v w) x) }
  exact this h

lemma eqv_relExt {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v = rel r w := by
  simp only [eq_iff_iff]; constructor
  · exact eqv_relExt_aux r h
  · exact eqv_relExt_aux r (fun i => eqv_symm (h i))

lemma eqv_equivalence : Equivalence (eqv L (M := M)) where
  refl := eqv_refl
  symm := eqv_symm
  trans := eqv_trans

variable (L M)

/-- Imported declaration from the Incompleteness formalization. -/
def eqvSetoid : Setoid M := Setoid.mk (eqv L) eqv_equivalence

/-- Imported declaration from the Incompleteness formalization. -/
def QuotEq := Quotient (eqvSetoid L M)

variable {L M}

instance _root_.LO.FirstOrder.Structure.Eq.QuotEq.inhabited :
    Nonempty (QuotEq L M) := Nonempty.map (⟦·⟧) inferInstance

lemma of_eq_of {a b : M} : (⟦a⟧ : QuotEq L M) = ⟦b⟧ ↔ eqv L a b := Quotient.eq (r := eqvSetoid L M)

namespace QuotEq

/-- Imported declaration from the Incompleteness formalization. -/
def func ⦃k⦄ (f : L.Func k) (v : Fin k → QuotEq L M) : QuotEq L M :=
  Quotient.liftVec (s := eqvSetoid L M) (⟦Structure.func f ·⟧) (fun _ _ hvw =>
    of_eq_of.mpr (eqv_funcExt f hvw)) v

/-- Imported declaration from the Incompleteness formalization. -/
def rel ⦃k⦄ (r : L.Rel k) (v : Fin k → QuotEq L M) : Prop :=
  Quotient.liftVec (s := eqvSetoid L M) (Structure.rel r) (fun _ _ hvw => eqv_relExt r hvw) v

instance struc : Structure L (QuotEq L M) where
  func := QuotEq.func
  rel := QuotEq.rel

lemma funk_mk {k} (f : L.Func k) (v : Fin k → M) :
    Structure.func (M :=
  QuotEq L M) f (fun i => ⟦v i⟧) = ⟦Structure.func f v⟧ :=
  Quotient.liftVec_mk (s := eqvSetoid L M) _ _ _

lemma rel_mk {k} (r : L.Rel k) (v : Fin k → M) :
    Structure.rel (M :=
  QuotEq L M) r (fun i => ⟦v i⟧) ↔ Structure.rel r v :=
  of_eq <| Quotient.liftVec_mk (s := eqvSetoid L M) _ _ _

lemma val_mk {e} {ε} (t : Semiterm L μ n) :
    Semiterm.valm (QuotEq L M) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) t = ⟦Semiterm.valm M e ε t⟧ :=
  by induction t <;> simp [*, funk_mk, Semiterm.val_func]

lemma eval_mk {e} {ε} {φ : Semiformula L μ n} :
    Semiformula.Evalm (QuotEq L M) (fun i =>
      ⟦e i⟧) (fun i => ⟦ε i⟧) φ ↔ Semiformula.Evalm M e ε φ := by
  induction φ using Semiformula.rec'
  case hverum =>
    simp only [LogicalConnective.HomClass.map_top, «Prop».top_eq_true]
  case hfalsum =>
    simp only [LogicalConnective.HomClass.map_bot, «Prop».bot_eq_false]
  case hrel =>
    simp only [Semiformula.eval_rel, val_mk, rel_mk]
  case hnrel =>
    simp only [Semiformula.eval_nrel, val_mk, rel_mk]
  case hand =>
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, *]
  case hor =>
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq, *]
  case hall n φ ih =>
    simp only [Semiformula.eval_all, Nat.succ_eq_add_one]
    constructor
    · intro h a
      exact (ih (e := a :> e)).mp (by simp only [Matrix.comp_vecCons] at h ⊢; exact h ⟦a⟧)
    · intro h a;
      induction a using Quotient.ind with
      | _ a =>
        have := ih.mpr (h a); simp only [Matrix.comp_vecCons] at this ⊢; exact this
  case hex n φ ih =>
    simp only [Semiformula.eval_ex, Nat.succ_eq_add_one]
    constructor
    · intro ⟨a, h⟩
      induction a using Quotient.ind with
      | _ a =>
        exact ⟨a, (ih (e := a :> e)).mp (by simp only [Matrix.comp_vecCons] at h ⊢; exact h)⟩
    · intro ⟨a, h⟩
      exact ⟨⟦a⟧, by have := ih.mpr h; simp only [Matrix.comp_vecCons] at this ⊢; exact this⟩

lemma eval_mk₀ {ε} {φ : Formula L ξ} :
    Semiformula.Evalfm (QuotEq L M) (fun i => ⟦ε i⟧) φ ↔ Semiformula.Evalfm (L := L) M ε φ := by
  have h := eval_mk (H := H) (e := ![]) (ε := ε) (φ := φ)
  simp only [Matrix.empty_eq] at h
  exact h

lemma models_iff {φ : SyntacticFormula L} : QuotEq L M ⊧ₘ φ ↔ M ⊧ₘ φ := by
  constructor
  · intro h f; exact eval_mk₀.mp (h (fun x ↦ ⟦f x⟧))
  · intro h f
    induction f using Quotient.induction_on_pi with
    | _ f => exact eval_mk₀.mpr (h f)

variable (L M)

lemma elementaryEquiv : QuotEq L M ≡ₑ[L] M := fun _ => models_iff

variable {L M}

lemma rel_eq (a b : QuotEq L M) :
    (@Semiformula.Operator.Eq.eq L _).val (M := QuotEq L M) ![a, b] ↔ a = b := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      have hEval :
          (@Semiformula.Operator.Eq.eq L _).val (M := QuotEq L M) ![⟦a⟧, ⟦b⟧] ↔
            eqv L a b := by
        have h := eval_mk (H := H) (e := ![a, b]) (ε := Empty.elim)
          (φ := Semiformula.Operator.Eq.eq.sentence)
        simp only [Semiformula.Operator.val, eqv, Matrix.fun_eq_vec₂, Matrix.cons_val_zero,
          Matrix.cons_val_one, Empty.eq_elim] at h ⊢
        exact h
      exact hEval.trans (of_eq_of (L := L) (M := M) (a := a) (b := b)).symm

instance structureEq : Structure.Eq L (QuotEq L M) := ⟨rel_eq⟩

end QuotEq

end Eq

end Structure

lemma consequence_iff_eq {T : Theory L} [𝐄𝐐 wkn T] {φ : SyntacticFormula L} :
    T ⊨[Struc.{v, u} L] φ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M],
        M ⊧ₘ* T → M ⊧ₘ φ) := by
  simp only [consequence_iff, Nonempty.forall]; constructor
  · intro h M x s _ hM; exact h M x hM
  · intro h M x s hM
    haveI : Nonempty M := ⟨x⟩
    have H : M ⊧ₘ* (𝐄𝐐 : Theory L) := models_of_subtheory hM
    have e : Structure.Eq.QuotEq L M ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv L M
    exact e.models.mp <| h (Structure.Eq.QuotEq L M) ⟦x⟧ (e.modelsTheory.mpr hM)

lemma consequence_iff_eq' {T : Theory L} [𝐄𝐐 wkn T] {φ : SyntacticFormula L} :
    T ⊨[Struc.{v, u} L] φ ↔ (∀ (M :
        Type v) [Nonempty M] [Structure L M] [Structure.Eq L M] [M ⊧ₘ* T], M ⊧ₘ φ) := by
  rw [consequence_iff_eq]

lemma satisfiable_iff_eq {T : Theory L} [𝐄𝐐 wkn T] :
    Semantics.Satisfiable (Struc.{v, u} L) T ↔
        (∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M) (_ : Structure.Eq L M), M ⊧ₘ* T) := by
  simp only [satisfiable_iff, exists_prop, Nonempty.exists]; constructor
  · intro ⟨M, x, s, hM⟩;
    haveI : Nonempty M := ⟨x⟩
    have H : M ⊧ₘ* (𝐄𝐐 : Theory L) := models_of_subtheory hM
    have e : Structure.Eq.QuotEq L M ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv L M
    exact ⟨Structure.Eq.QuotEq L M, ⟦x⟧, inferInstance, inferInstance, e.modelsTheory.mpr hM⟩
  · intro ⟨M, i, s, _, hM⟩; exact ⟨M, i, s, hM⟩

instance {T : Theory L} [𝐄𝐐 wkn T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T) :
    ModelOfSat sat ⊧ₘ* (𝐄𝐐 : Theory L) := models_of_subtheory (ModelOfSat.models sat)

/-- Imported declaration from the Incompleteness formalization. -/
def ModelOfSatEq {T : Theory L} [𝐄𝐐 wkn T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T) :
    Type _ := Structure.Eq.QuotEq L (ModelOfSat sat)

namespace ModelOfSatEq

variable {T : Theory L} [𝐄𝐐 wkn T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T)

noncomputable instance : Nonempty (ModelOfSatEq sat) := Structure.Eq.QuotEq.inhabited

noncomputable instance struc : Structure L (ModelOfSatEq sat) := Structure.Eq.QuotEq.struc

noncomputable instance : Structure.Eq L (ModelOfSatEq sat) := Structure.Eq.QuotEq.structureEq

lemma models : ModelOfSatEq sat ⊧ₘ* T :=
  have e : ModelOfSatEq sat ≡ₑ[L] ModelOfSat sat :=
    Structure.Eq.QuotEq.elementaryEquiv L (ModelOfSat sat)
  e.modelsTheory.mpr (ModelOfSat.models _)

instance mod : ModelOfSatEq sat ⊧ₘ* T := models sat

open Semiterm Semiformula

noncomputable instance [Operator.Zero L] :
    Zero (ModelOfSatEq sat) :=
  ⟨(@Operator.Zero.zero L _).val ![]⟩

instance strucZero [Operator.Zero L] : Structure.Zero L (ModelOfSatEq sat) := ⟨rfl⟩

noncomputable instance [Operator.One L] :
    One (ModelOfSatEq sat) :=
  ⟨(@Operator.One.one L _).val ![]⟩

instance [Operator.One L] : Structure.One L (ModelOfSatEq sat) := ⟨rfl⟩

noncomputable instance [Operator.Add L] : Add (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.Add.add L _).val ![x, y]⟩

instance [Operator.Add L] : Structure.Add L (ModelOfSatEq sat) := ⟨fun _ _ => rfl⟩

noncomputable instance [Operator.Mul L] : Mul (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.Mul.mul L _).val ![x, y]⟩

instance [Operator.Mul L] : Structure.Mul L (ModelOfSatEq sat) := ⟨fun _ _ => rfl⟩

instance [Operator.LT L] : LT (ModelOfSatEq sat) := ⟨fun x y => (@Operator.LT.lt L _).val ![x, y]⟩

instance [Operator.LT L] : Structure.LT L (ModelOfSatEq sat) := ⟨fun _ _ => iff_of_eq rfl⟩

instance [Operator.Mem L] : Membership (ModelOfSatEq sat) (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.Mem.mem L _).val ![y, x]⟩

instance [Operator.Mem L] : Structure.Mem L (ModelOfSatEq sat) := ⟨fun _ _ => iff_of_eq rfl⟩

end ModelOfSatEq

namespace Semiformula

/-- Imported declaration from the Incompleteness formalization. -/
def existsUnique {ξ} (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  “∃ y, !φ y ⋯ ∧ ∀ z, !φ z ⋯ → z = y”

/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∃'! " => existsUnique

variable {M : Type*} [s : Structure L M] [Structure.Eq L M]

@[simp] lemma eval_existsUnique {e ε} {φ : Semiformula L ξ (n + 1)} :
    Eval s e ε (∃'! φ) ↔ ∃! x, Eval s (x :> e) ε φ := by
  simp [existsUnique, Semiformula.eval_substs, Matrix.comp_vecCons', ExistsUnique]

end Semiformula

namespace BinderNotation

open Lean PrettyPrinter Delaborator SubExpr

/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃! " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃! " ident ", " firstOrderFormula:0 : firstOrderFormula

macro_rules
  | `(foFormula[ $binders* | $fbinders* | ∃! $φ:firstOrderFormula ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃'! foFormula[ $binders'* | $fbinders* | $φ])
  | `(foFormula[ $binders* | $fbinders* | ∃! $x, $φ ])                 => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(∃'! foFormula[ $binders'* | $fbinders* | $φ ])

end BinderNotation

end FirstOrder

end LO
