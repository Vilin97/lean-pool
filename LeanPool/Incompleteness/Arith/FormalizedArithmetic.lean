/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Metamath

/-!

# Formalized Theory $\mathsf{R_0}$

-/

noncomputable section «lp_nc_section_1»

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

/-- Local classical decidable equality instance used by imported proofs. -/
local instance instDecidableEqOfClassical (α : Sort _) : DecidableEq α := Classical.decEq α

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

namespace Formalized

variable (V)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Arith.Formalized.LOR.Theory := @Language.Theory V _ ⌜ℒₒᵣ⌝ (Language.lDef ℒₒᵣ) _

variable {V}

/-- TODO: move -/
@[simp] lemma two_lt_three : (2 : V) < (1 + 1 + 1 : V) := by simp [←one_add_one_eq_two]
@[simp] lemma two_lt_four : (2 : V) < (1 + 1 + 1 + 1 : V) := by simp [←one_add_one_eq_two]
@[simp] lemma three_lt_four : (3 : V) < (1 + 1 + 1 + 1 :
    V) := by
  simp [←two_add_one_eq_three, ←one_add_one_eq_two]
@[simp] lemma two_sub_one_eq_one : (2 : V) - 1 = 1 := by simp [←one_add_one_eq_two]
@[simp] lemma three_sub_one_eq_two : (3 : V) - 1 = 2 := by simp [←two_add_one_eq_three]

/-- Imported declaration from the Incompleteness formalization. -/
class R₀Theory (T : LOR.TTheory (V := V)) where
  /-- Imported declaration from the Incompleteness formalization. -/
  refl : T ⊢ (#'0 =' #'0).all
  /-- Imported declaration from the Incompleteness formalization. -/
  replace (φ :
      ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) : T ⊢ (#'1 =' #'0 ==> φ^/[(#'1).sing] ==> φ^/[(#'0).sing]).all.all
  /-- Imported declaration from the Incompleteness formalization. -/
  add (n m : V) : T ⊢ (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m)
  /-- Imported declaration from the Incompleteness formalization. -/
  mul (n m : V) : T ⊢ (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m)
  /-- Imported declaration from the Incompleteness formalization. -/
  ne {n m : V} : n ≠ m → T ⊢ ↑n ≠' ↑m
  /-- Imported declaration from the Incompleteness formalization. -/
  ltNumeral (n : V) : T ⊢ (#'0 <' ↑n <=> (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all

/-- Imported declaration from the Incompleteness formalization. -/
abbrev oneAbbrev {n} : ⌜ℒₒᵣ⌝[V].Semiterm n := (1 : V)

/-- Imported declaration from the Incompleteness formalization. -/
scoped notation "^1" => oneAbbrev

/-
section «lp_nc_section_2»

def _root_.LO.FirstOrder.Arith.eqTheory : Sg1.Semisentence 0 := .mkSigma
  “(∃ b0, !qqBvarDef b0 0 ∧ !qqAllDef )” (by simp)

end «lp_nc_section_2»
-/

variable (T : LOR.TTheory (V := V))

namespace TProof

open Language.Theory.TProof Entailment Entailment.FiniteContext

section «lp_section_1»

variable [R₀Theory T]

/-- Imported declaration from the Incompleteness formalization. -/
def eqRefl (t : ⌜ℒₒᵣ⌝.Term) : T ⊢ t =' t := by
  have : T ⊢ (#'0 =' #'0).all := R₀Theory.refl
  simpa [Language.Semiformula.substs₁] using specialize this t

lemma «eq_refl!» (t : ⌜ℒₒᵣ⌝.Term) : T ⊢! t =' t := ⟨eqRefl T t⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def replace (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t =' u ==> φ^/[t.sing] ==> φ^/[u.sing] := by
  have : T ⊢ (#'1 =' #'0 ==> φ^/[(#'1).sing] ==> φ^/[(#'0).sing]).all.all := R₀Theory.replace φ
  have := by simpa using specialize this t
  simpa [Language.SemitermVec.q_of_pos, Language.Semiformula.substs₁,
    Language.TSemifromula.substs_substs] using specialize this u

lemma «replace!» (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.Term) :
    T ⊢! t =' u ==> φ^/[t.sing] ==> φ^/[u.sing] :=
  ⟨replace T φ t u⟩

/-- Imported declaration from the Incompleteness formalization. -/
def eqSymm (t₁ t₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢ t₁ =' t₂ ==> t₂ =' t₁ := by
  apply deduct'
  let Γ := [t₁ =' t₂]
  have e₁ : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm (by simp [Γ])
  have e₂ : Γ ⊢[T] t₁ =' t₁ := of <| eqRefl T t₁
  have : Γ ⊢[T] t₁ =' t₂ ==> t₁ =' t₁ ==> t₂ =' t₁ := of <| by
    simpa using replace T (#'0 =' t₁.bShift) t₁ t₂
  exact this ⨀ e₁ ⨀ e₂

lemma «eq_symm!» (t₁ t₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢! t₁ =' t₂ ==> t₂ =' t₁ := ⟨eqSymm T t₁ t₂⟩

lemma «eq_symm'!» {t₁ t₂ : ⌜ℒₒᵣ⌝.Term} (h : T ⊢! t₁ =' t₂) : T ⊢! t₂ =' t₁ := eq_symm! T t₁ t₂ ⨀ h

/-- Imported declaration from the Incompleteness formalization. -/
def eqTrans (t₁ t₂ t₃ : ⌜ℒₒᵣ⌝.Term) : T ⊢ t₁ =' t₂ ==> t₂ =' t₃ ==> t₁ =' t₃ := by
  apply deduct'
  apply deduct
  let Γ := [t₂ =' t₃, t₁ =' t₂]
  have e₁ : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm (by simp [Γ])
  have e₂ : Γ ⊢[T] t₂ =' t₃ := FiniteContext.byAxm (by simp [Γ])
  have : Γ ⊢[T] t₂ =' t₃ ==> t₁ =' t₂ ==> t₁ =' t₃ := of <| by
    simpa using replace T (t₁.bShift =' #'0) t₂ t₃
  exact this ⨀ e₂ ⨀ e₁

lemma «eq_trans!» (t₁ t₂ t₃ : ⌜ℒₒᵣ⌝.Term) :
    T ⊢! t₁ =' t₂ ==> t₂ =' t₃ ==> t₁ =' t₃ :=
  ⟨eqTrans T t₁ t₂ t₃⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def addExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t₁ =' t₂ ==> u₁ =' u₂ ==> (t₁ + u₁) =' (t₂ + u₂) := by
  apply deduct'
  apply deduct
  let Γ := [u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ==> (t₁ + u₁) =' (t₁ + u₁) ==> (t₁ + u₁) =' (t₂ + u₁) := by
    have := replace T ((t₁.bShift + u₁.bShift) =' (#'0 + u₁.bShift)) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] (t₁ + u₁) =' (t₂ + u₁) := of (Γ := Γ) this ⨀ bt ⨀ of (eqRefl _ _)
  have : T ⊢ u₁ =' u₂ ==> (t₁ + u₁) =' (t₂ + u₁) ==> (t₁ + u₁) =' (t₂ + u₂) := by
    have := replace T ((t₁.bShift + u₁.bShift) =' (t₂.bShift + #'0)) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma «add_ext!» (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) :
    T ⊢! t₁ =' t₂ ==> u₁ =' u₂ ==> (t₁ + u₁) =' (t₂ + u₂) :=
  ⟨addExt T t₁ t₂ u₁ u₂⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def mulExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t₁ =' t₂ ==> u₁ =' u₂ ==> (t₁ * u₁) =' (t₂ * u₂) := by
  apply deduct'
  apply deduct
  let Γ := [u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ==> (t₁ * u₁) =' (t₁ * u₁) ==> (t₁ * u₁) =' (t₂ * u₁) := by
    have := replace T ((t₁.bShift * u₁.bShift) =' (#'0 * u₁.bShift)) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] (t₁ * u₁) =' (t₂ * u₁) := of (Γ := Γ) this ⨀ bt ⨀ of (eqRefl _ _)
  have : T ⊢ u₁ =' u₂ ==> (t₁ * u₁) =' (t₂ * u₁) ==> (t₁ * u₁) =' (t₂ * u₂) := by
    have := replace T ((t₁.bShift * u₁.bShift) =' (t₂.bShift * #'0)) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma «mul_ext!» (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) :
    T ⊢! t₁ =' t₂ ==> u₁ =' u₂ ==> (t₁ * u₁) =' (t₂ * u₂) :=
  ⟨mulExt T t₁ t₂ u₁ u₂⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def eqExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t₁ =' t₂ ==> u₁ =' u₂ ==> t₁ =' u₁ ==> t₂ =' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ =' u₁, u₁ =' u₂, t₁ =' t₂]
  have e1 : Γ ⊢[T] t₂ =' t₁ := by
    refine (of <| eqSymm T t₁ t₂) ⨀ FiniteContext.byAxm (by simp [Γ])
  have e2 : Γ ⊢[T] t₁ =' u₁ := FiniteContext.byAxm (by simp [Γ])
  have e3 : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm (by simp [Γ])
  exact (of <| eqTrans T t₂ u₁ u₂) ⨀ ((of <| eqTrans T t₂ t₁ u₁) ⨀ e1 ⨀ e2) ⨀ e3

lemma eq_ext (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢! t₁ =' t₂ ==> u₁ =' u₂ ==> t₁ =' u₁ ==> t₂ =' u₂ :=
  ⟨eqExt T t₁ t₂ u₁ u₂⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def neExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t₁ =' t₂ ==> u₁ =' u₂ ==> t₁ ≠' u₁ ==> t₂ ≠' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ ≠' u₁, u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have bl : Γ ⊢[T] t₁ ≠' u₁ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ==> t₁ ≠' u₁ ==> t₂ ≠' u₁ := by
    have := replace T (#'0 ≠' u₁.bShift) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] t₂ ≠' u₁ := of (Γ := Γ) this ⨀ bt ⨀ bl
  have : T ⊢ u₁ =' u₂ ==> t₂ ≠' u₁ ==> t₂ ≠' u₂ := by
    simpa using replace T (t₂.bShift ≠' #'0) u₁ u₂
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma ne_ext (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢! t₁ =' t₂ ==> u₁ =' u₂ ==> t₁ ≠' u₁ ==> t₂ ≠' u₂ :=
  ⟨neExt T t₁ t₂ u₁ u₂⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def ltExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t₁ =' t₂ ==> u₁ =' u₂ ==> t₁ <' u₁ ==> t₂ <' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ <' u₁, u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have bl : Γ ⊢[T] t₁ <' u₁ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ==> t₁ <' u₁ ==> t₂ <' u₁ := by
    have := replace T (#'0 <' u₁.bShift) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] t₂ <' u₁ := of (Γ := Γ) this ⨀ bt ⨀ bl
  have : T ⊢ u₁ =' u₂ ==> t₂ <' u₁ ==> t₂ <' u₂ := by
    have := replace T (t₂.bShift <' #'0) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma «lt_ext!» (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) :
    T ⊢! t₁ =' t₂ ==> u₁ =' u₂ ==> t₁ <' u₁ ==> t₂ <' u₂ :=
  ⟨ltExt T t₁ t₂ u₁ u₂⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def nltExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t₁ =' t₂ ==> u₁ =' u₂ ==> t₁ </' u₁ ==> t₂ </' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ </' u₁, u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have bl : Γ ⊢[T] t₁ </' u₁ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ==> t₁ </' u₁ ==> t₂ </' u₁ := by
    have := replace T (#'0 </' u₁.bShift) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] t₂ </' u₁ := of (Γ := Γ) this ⨀ bt ⨀ bl
  have : T ⊢ u₁ =' u₂ ==> t₂ </' u₁ ==> t₂ </' u₂ := by
    have := replace T (t₂.bShift </' #'0) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma nlt_ext (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) :
    T ⊢! t₁ =' t₂ ==> u₁ =' u₂ ==> t₁ </' u₁ ==> t₂ </' u₂ :=
  ⟨nltExt T t₁ t₂ u₁ u₂⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def ballReplace (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t =' u ==> φ.ball t ==> φ.ball u := by
  simpa [Language.TSemifromula.substs_substs] using replace T ((φ^/[(#'0).sing]).ball #'0) t u

lemma «ball_replace!» (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.Term) :
    T ⊢! t =' u ==> φ.ball t ==> φ.ball u := ⟨ballReplace T φ t u⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def bexReplace (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t =' u ==> φ.bex t ==> φ.bex u := by
  simpa [Language.TSemifromula.substs_substs] using replace T ((φ^/[(#'0).sing]).bex #'0) t u

lemma «bex_replace!» (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.Term) :
    T ⊢! t =' u ==> φ.bex t ==> φ.bex u := ⟨bexReplace T φ t u⟩

/-- Imported declaration from the Incompleteness formalization. -/
def eqComplete {n m : V} (h : n = m) : T ⊢ ↑n =' ↑m := by
  rcases h; exact eqRefl T _

lemma «eq_complete!» {n m : V} (h : n = m) : T ⊢! ↑n =' ↑m := ⟨eqComplete T h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def addComplete (n m : V) : T ⊢ (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m) := R₀Theory.add n m

lemma «add_complete!» (n m : V) : T ⊢! (n + m :
    ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m) :=
  ⟨addComplete T n m⟩

/-- Imported declaration from the Incompleteness formalization. -/
def mulComplete (n m : V) : T ⊢ (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m) := R₀Theory.mul n m

lemma «mul_complete!» (n m : V) : T ⊢! (n * m :
    ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m) :=
  ⟨mulComplete T n m⟩

/-- Imported declaration from the Incompleteness formalization. -/
def neComplete {n m : V} (h : n ≠ m) : T ⊢ ↑n ≠' ↑m := R₀Theory.ne h

lemma «ne_complete!» {n m : V} (h : n ≠ m) : T ⊢! ↑n ≠' ↑m := ⟨neComplete T h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def ltNumeral (t : ⌜ℒₒᵣ⌝.Term) (n : V) :
    T ⊢ t <' ↑n <=> (tSubstItr t.sing (#'1 =' #'0) n).disj := by
  have : T ⊢ (#'0 <' ↑n <=> (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all := R₀Theory.ltNumeral n
  simpa [Language.SemitermVec.q_of_pos, Language.Semiformula.substs₁] using specialize this t

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def nltNumeral (t : ⌜ℒₒᵣ⌝.Term) (n : V) :
    T ⊢ t </' ↑n <=> (tSubstItr t.sing (#'1 ≠' #'0) n).conj := by
  simpa using negReplaceIff' <| ltNumeral T t n

/-- Imported declaration from the Incompleteness formalization. -/
def ltComplete {n m : V} (h : n < m) : T ⊢ ↑n <' ↑m := by
  have : T ⊢ ↑n <' ↑m <=> _ := ltNumeral T n m
  apply andRight this ⨀ ?_
  apply disj (i := m - (n + 1)) _ (by simpa using sub_succ_lt_self h)
  simpa [nth_tSubstItr', h] using eqRefl T ↑n

lemma «lt_complete!» {n m : V} (h : n < m) : T ⊢! ↑n <' ↑m := ⟨ltComplete T h⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def nltComplete {n m : V} (h : m ≤ n) : T ⊢ ↑n </' ↑m := by
  have : T ⊢ ↑n </' ↑m <=> (tSubstItr (↑n : ⌜ℒₒᵣ⌝.Term).sing (#'1 ≠' #'0) m).conj := by
    simpa using negReplaceIff' <| ltNumeral T n m
  refine andRight this ⨀ ?_
  apply conj'
  intro i hi
  have hi : i < m := by simpa using hi
  have : n ≠ i := Ne.symm <| ne_of_lt <| lt_of_lt_of_le hi h
  simpa [nth_tSubstItr', hi] using neComplete T this

lemma nlt_complete {n m : V} (h : m ≤ n) : T ⊢! ↑n </' ↑m := ⟨nltComplete T h⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def ballIntro (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (n : V)
    (bs : ∀ i < n, T ⊢ φ^/[(i : ⌜ℒₒᵣ⌝.Term).sing]) :
    T ⊢ φ.ball ↑n := by
  apply all
  suffices T ⊢ &'0 </' ↑n ⋎ φ.shift^/[(&'0).sing] by
    simpa [Language.Semiformula.free, Language.Semiformula.substs₁]
  have : T ⊢ (tSubstItr (&'0).sing (#'1 ≠' #'0) n).conj ⋎ φ.shift^/[(&'0).sing] := by
    apply conjOr'
    intro i hi
    have hi : i < n := by simpa using hi
    let Γ := [&'0 =' typedNumeral 0 i]
    suffices Γ ⊢[T] φ.shift^/[(&'0).sing] by
      simpa [nth_tSubstItr', hi, Language.Semiformula.imp_def] using deduct' this
    have e : Γ ⊢[T] ↑i =' &'0 := of (eqSymm T &'0 ↑i) ⨀ (FiniteContext.byAxm <| by simp [Γ])
    have : T ⊢ φ.shift^/[(i : ⌜ℒₒᵣ⌝.Term).sing] := by
      simpa [Language.TSemifromula.shift_substs] using shift (bs i hi)
    exact of (replace T φ.shift ↑i &'0) ⨀ e ⨀ of this
  exact orReplaceLeft' this (andRight (nltNumeral T (&'0) n))

lemma «ball_intro!» (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (n : V)
    (bs : ∀ i < n, T ⊢! φ ^/[(i : ⌜ℒₒᵣ⌝.Term).sing]) :
    T ⊢! φ.ball ↑n := ⟨ballIntro T φ n fun i hi ↦ (bs i hi).get⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def bexIntro (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (n : V) {i}
    (hi : i < n) (b : T ⊢ φ^/[(i : ⌜ℒₒᵣ⌝.Term).sing]) :
    T ⊢ φ.bex ↑n := by
  apply ex i
  suffices T ⊢ i <' n ⋏ φ^/[(i : ⌜ℒₒᵣ⌝.Term).sing] by simpa
  exact Entailment.andIntro (ltComplete T hi) b

lemma «bex_intro!» (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (n : V) {i}
    (hi : i < n) (b : T ⊢! φ ^/[(i : ⌜ℒₒᵣ⌝.Term).sing]) :
    T ⊢! φ.bex ↑n := ⟨bexIntro T φ n hi b.get⟩

end «lp_section_1»

end TProof

end Formalized

end Arith
end LO

end «lp_nc_section_1»
