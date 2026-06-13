/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Metamath.Formula.Typed
import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Metamath.Proof.Derivation
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental

/-!

# Typed Formalized Tait-Calculus

-/

noncomputable section «lp_nc_section_1»

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Arith.Language.Semiformula.substs₁ (p : L.Semiformula (0 + 1)) (t : L.Term) :
    L.Formula :=
  p.substs t.sing

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Arith.Language.Semiformula.free (p : L.Semiformula (0 + 1)) :
    L.Formula :=
  p.shift.substs₁ (L.fvar 0)

@[simp 1100] lemma _root_.LO.Arith.Language.Semiformula.val_substs₁ (p : L.Semiformula (0 + 1)) (t :
    L.Term) :
    (p.substs₁ t).val = L.substs ?[t.val] p.val := by
  simp [Language.Semiformula.substs₁, Language.Semiformula.substs]

lemma _root_.LO.Arith.Language.Semiformula.val_free (p : L.Semiformula (0 + 1)) :
    p.free.val = L.substs ?[^&0] (L.shift p.val) := by
  simp [Language.Semiformula.free, Language.Semiformula.substs₁, Language.Semiformula.substs,
    Language.Semiformula.shift, Language.fvar]

@[simp 1100] lemma substs₁_neg (p : L.Semiformula (0 + 1)) (t : L.Term) :
    (∼p).substs₁ t = ∼(p.substs₁ t) := by simp [Language.Semiformula.substs₁]

@[simp 1100] lemma substs₁_all (p : L.Semiformula (0 + 1 + 1)) (t : L.Term) :
    p.all.substs₁ t = (p.substs t.sing.q).all := by simp [Language.Semiformula.substs₁]

@[simp 1100] lemma substs₁_ex (p : L.Semiformula (0 + 1 + 1)) (t : L.Term) :
    p.ex.substs₁ t = (p.substs t.sing.q).ex := by simp [Language.Semiformula.substs₁]

end «lp_section_1»

section «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Arith.Language.Theory.tmem (p : L.Formula) (T : L.Theory) : Prop := p.val ∈ T

/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:50 " ∈' " => Language.Theory.tmem

end «lp_section_2»

section «lp_section_3»

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.Arith.Language.Sequent where
  /-- Imported declaration from the Incompleteness formalization. -/
  val : V
  val_formulaSet : L.IsFormulaSet val

attribute [simp] Language.Sequent.val_formulaSet

variable {L}

instance : EmptyCollection L.Sequent := ⟨⟨∅, by simp⟩⟩

instance : Singleton L.Formula L.Sequent := ⟨fun p ↦ ⟨{p.val}, by simp⟩⟩

instance : Insert L.Formula L.Sequent := ⟨fun p Γ ↦ ⟨insert p.val Γ.val, by simp⟩⟩

instance : Union L.Sequent := ⟨fun Γ Δ ↦ ⟨Γ.val ∪ Δ.val, by simp⟩⟩

instance : Membership L.Formula L.Sequent := ⟨fun Γ p ↦ (p.val ∈ Γ.val)⟩

instance : HasSubset L.Sequent := ⟨(·.val ⊆ ·.val)⟩

/-- Imported declaration from the Incompleteness formalization. -/
scoped infixr:50 " :+> " => Insert.insert

namespace Language
namespace Sequent

variable {Γ Δ : L.Sequent} {p q : L.Formula}

lemma mem_iff : p ∈ Γ ↔ p.val ∈ Γ.val := iff_of_eq rfl

lemma subset_iff : Γ ⊆ Δ ↔ Γ.val ⊆ Δ.val := iff_of_eq rfl

@[simp] lemma val_empty : (∅ : L.Sequent).val = ∅ := rfl

@[simp] lemma val_singleton (p : L.Formula) : ({p} : L.Sequent).val = {p.val} := rfl

@[simp] lemma val_insert (p : L.Formula) (Γ : L.Sequent) :
    (insert p Γ).val = insert p.val Γ.val :=
  rfl

@[simp] lemma val_union (Γ Δ : L.Sequent) : (Γ ∪ Δ).val = Γ.val ∪ Δ.val := rfl

@[simp] lemma not_mem_empty (p : L.Formula) : p ∉ (∅ : L.Sequent) := by simp [mem_iff]

@[simp] lemma mem_singleton_iff : p ∈ ({q} :
    L.Sequent) ↔ p = q := by simp [mem_iff, Language.Semiformula.val_inj]

@[simp] lemma mem_insert_iff :
    p ∈ insert q Γ ↔ p = q ∨ p ∈ Γ := by simp [mem_iff, Language.Semiformula.val_inj]

@[simp] lemma mem_union_iff :
    p ∈ Γ ∪ Δ ↔ p ∈ Γ ∨ p ∈ Δ := by simp [mem_iff]

@[ext] lemma ext (h : ∀ x, x ∈ Γ ↔ x ∈ Δ) : Γ = Δ := by
  rcases Γ with ⟨Γ, hΓ⟩; rcases Δ with ⟨Δ, hΔ⟩; simp only [mk.injEq]
  apply mem_ext; intro x
  constructor
  · intro hx; simpa using mem_iff.mp <| (h ⟨x, hΓ x hx⟩ |>.1 (by simp [mem_iff, hx]))
  · intro hx; simpa using mem_iff.mp <| (h ⟨x, hΔ x hx⟩ |>.2 (by simp [mem_iff, hx]))

lemma ext' (h : Γ.val = Δ.val) : Γ = Δ := by rcases Γ; rcases Δ; simpa using h

/-- Imported declaration from the Incompleteness formalization. -/
def shift (s : L.Sequent) : L.Sequent := ⟨L.setShift s.val, by simp⟩

@[simp] lemma shift_empty : (∅ : L.Sequent).shift = ∅ := ext' <| by simp [shift]

@[simp] lemma shift_insert : (insert p Γ).shift = insert p.shift Γ.shift := ext' <| by simp [shift]

end Sequent
end Language

end «lp_section_3»

section «lp_section_4»

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.Arith.Language.TTheory where
  /-- Imported declaration from the Incompleteness formalization. -/
  thy : L.Theory
  /-- Imported declaration from the Incompleteness formalization. -/
  pthy : pL.TDef
  [defined : thy.Defined pthy]

instance (T : Language.TTheory L) : T.thy.Defined T.pthy := T.defined

variable {L}

/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.Arith.Language.Theory.TDerivation (T : Language.TTheory L) (Γ : L.Sequent) where
  /-- Imported declaration from the Incompleteness formalization. -/
  derivation : V
  derivationOf : T.thy.DerivationOf derivation Γ.val

/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:45 " ⊢¹ " => Language.Theory.TDerivation

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Language.Theory.TProof (T : Language.TTheory L) (p :
    L.Formula) :=
  T ⊢¹ insert p ∅

instance : Entailment L.Formula L.TTheory := ⟨Language.Theory.TProof⟩

instance : HasSubset L.TTheory := ⟨fun T U ↦ T.thy ⊆ U.thy⟩

variable {T U : L.TTheory}

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Language.Theory.Derivable.toTDerivation (Γ : L.Sequent) (h :
    T.thy.Derivable Γ.val) :
    T ⊢¹ Γ := by
  choose a ha using h; choose d hd using ha.2
  exact ⟨a, ha.1, d, hd⟩

lemma _root_.LO.Arith.Language.Theory.TDerivation.toDerivable {Γ : L.Sequent} (d : T ⊢¹ Γ) :
    T.thy.Derivable Γ.val :=
  ⟨d.derivation, d.derivationOf⟩

lemma _root_.LO.Arith.Language.Theory.TProvable.iff_provable {σ : L.Formula} :
    T ⊢! σ ↔ T.thy.Provable σ.val := by
  constructor
  · intro b
    unfold Language.Theory.Provable
    simpa [←singleton_eq_insert] using Language.Theory.TDerivation.toDerivable b.get
  · intro h
    refine ⟨Language.Theory.Derivable.toTDerivation _ ?_⟩
    unfold Language.Theory.Provable at h
    simpa [←singleton_eq_insert] using h

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Language.Theory.TDerivation.toTProof {p} (d : T ⊢¹ insert p ∅) : T ⊢ p := d

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Language.Theory.TProof.toTDerivation {p} (d : T ⊢ p) : T ⊢¹ insert p ∅ := d

namespace Language
namespace Theory
namespace TDerivation

variable {Γ Δ : L.Sequent} {p q p₀ p₁ p₂ p₃ p₄ : L.Formula}

/-- Imported declaration from the Incompleteness formalization. -/
def byAxm (p) (h : p ∈' T.thy) (hΓ : p ∈ Γ) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| Language.Theory.Derivable.by_axm (by simp) _ hΓ h

/-- Imported declaration from the Incompleteness formalization. -/
def em (p) (h : p ∈ Γ := by simp) (hn : ∼p ∈ Γ := by simp) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| Language.Theory.Derivable.em (by simp) p.val (Language.Sequent.mem_iff.mp h) (by
      simpa using Language.Sequent.mem_iff.mp hn)

/-- Imported declaration from the Incompleteness formalization. -/
def verum (h : ⊤ ∈ Γ := by simp) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| Language.Theory.Derivable.verum (by simp) (by simpa using Language.Sequent.mem_iff.mp h)

/-- Imported declaration from the Incompleteness formalization. -/
def and (dp : T ⊢¹ insert p Γ) (dq : T ⊢¹ insert q Γ) : T ⊢¹ insert (p ⋏ q) Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| by
      simpa using Language.Theory.Derivable.and
        (by simpa using dp.toDerivable) (by simpa using dq.toDerivable)

/-- Imported declaration from the Incompleteness formalization. -/
def or (dpq : T ⊢¹ insert p (insert q Γ)) : T ⊢¹ insert (p ⋎ q) Γ :=
  Language.Theory.Derivable.toTDerivation _ <|
      by simpa using Language.Theory.Derivable.or (by simpa using dpq.toDerivable)

/-- Imported declaration from the Incompleteness formalization. -/
def all {p : L.Semiformula (0 + 1)} (dp : T ⊢¹ insert p.free Γ.shift) : T ⊢¹ insert p.all Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.all (by simpa using p.prop) dp.toDerivable

/-- Imported declaration from the Incompleteness formalization. -/
def ex {p : L.Semiformula (0 + 1)} (t : L.Term) (dp : T ⊢¹ insert (p.substs₁ t) Γ) :
    T ⊢¹ insert p.ex Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.ex (by simpa using p.prop) t.prop dp.toDerivable

/-- Imported declaration from the Incompleteness formalization. -/
def wk (d : T ⊢¹ Δ) (h : Δ ⊆ Γ) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.wk (by simp) (Language.Sequent.subset_iff.mp h) (by simpa
      using d.toDerivable)

/-- Imported declaration from the Incompleteness formalization. -/
def shift (d : T ⊢¹ Γ) : T ⊢¹ Γ.shift :=
  Language.Theory.Derivable.toTDerivation _ <| by
    exact Language.Theory.Derivable.shift d.toDerivable

/-- Imported declaration from the Incompleteness formalization. -/
def cut (d₁ : T ⊢¹ insert p Γ) (d₂ : T ⊢¹ insert (∼p) Γ) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.cut p.val (by simpa using d₁.toDerivable) (by simpa using
      d₂.toDerivable)

/-- Imported declaration from the Incompleteness formalization. -/
def ofSubset (h : T ⊆ U) (d : T ⊢¹ Γ) : U ⊢¹ Γ where
  derivation := d.derivation
  derivationOf := ⟨d.derivationOf.1, d.derivationOf.2.of_ss h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def cut' (d₁ : T ⊢¹ insert p Γ) (d₂ : T ⊢¹ insert (∼p) Δ) : T ⊢¹ Γ ∪ Δ :=
  cut (p := p) (d₁.wk (by intro x; simp; tauto)) (d₂.wk (by intro x; simp; tauto))

/-- Imported declaration from the Incompleteness formalization. -/
def conj (ps : L.SemiformulaVec 0) (ds : ∀ i, (hi : i < len ps.val) → T ⊢¹ insert (ps.nth i hi) Γ) :
    T ⊢¹ insert ps.conj Γ := by
  have : ∀ i < len ps.val, T.thy.Derivable (insert (ps.val.[i]) Γ.val) := by
    intro i hi; simpa using (ds i hi).toDerivable
  have : T.thy.Derivable (insert (^⋀ ps.val) Γ.val) :=
    Language.Theory.Derivable.conj ps.val (by simp) this
  exact Language.Theory.Derivable.toTDerivation _ (by simpa using this)

/-- Imported declaration from the Incompleteness formalization. -/
def disj (ps : L.SemiformulaVec 0) {i} (hi : i < len ps.val)
    (d : T ⊢¹ insert (ps.nth i hi) Γ) : T ⊢¹ insert ps.disj Γ := by
  have : T.thy.Derivable (insert (^⋁ ps.val) Γ.val) :=
    Language.Theory.Derivable.disj ps.val Γ.val ps.prop hi (by simpa using d.toDerivable)
  apply Language.Theory.Derivable.toTDerivation _ (by simpa using this)

/-- Imported declaration from the Incompleteness formalization. -/
def modusPonens (dpq : T ⊢¹ insert (p ==> q) Γ) (dp : T ⊢¹ insert p Γ) : T ⊢¹ insert q Γ := by
  let d : T ⊢¹ insert (p ==> q) (insert q Γ) := dpq.wk (insert_subset_insert_of_subset _ <| by simp)
  let b : T ⊢¹ insert (∼(p ==> q)) (insert q Γ) := by
    simp only [Semiformula.imp_def, Semiformula.neg_or, Semiformula.neg_neg]
    exact and (dp.wk (insert_subset_insert_of_subset _ <| by simp))
      (em q (by simp) (by simp))
  exact cut d b

/-- Imported declaration from the Incompleteness formalization. -/
def ofEq (d : T ⊢¹ Γ) (h : Γ = Δ) : T ⊢¹ Δ := h ▸ d

/-- Imported declaration from the Incompleteness formalization. -/
def rotate₁ (d : T ⊢¹ p₀ :+> p₁ :+> Γ) : T ⊢¹ p₁ :+> p₀ :+> Γ :=
  ofEq d (by ext x; simp; tauto)

/-- Imported declaration from the Incompleteness formalization. -/
def rotate₂ (d : T ⊢¹ p₀ :+> p₁ :+> p₂ :+> Γ) : T ⊢¹ p₂ :+> p₁ :+> p₀ :+> Γ :=
  ofEq d (by ext x; simp; tauto)

/-- Imported declaration from the Incompleteness formalization. -/
def rotate₃ (d : T ⊢¹ p₀ :+> p₁ :+> p₂ :+> p₃ :+> Γ) : T ⊢¹ p₃ :+> p₁ :+> p₂ :+> p₀ :+> Γ :=
  ofEq d (by ext x; simp; tauto)

/-- Imported declaration from the Incompleteness formalization. -/
def orInv (d : T ⊢¹ p ⋎ q :+> Γ) : T ⊢¹ p :+> q :+> Γ := by
  have b : T ⊢¹ p ⋎ q :+> p :+> q :+> Γ := wk d (by intro x; simp; tauto)
  have : T ⊢¹ ∼(p ⋎ q) :+> p :+> q :+> Γ := by
    simp only [Semiformula.neg_or]
    apply and (em p) (em q)
  exact cut b this

/-- Imported declaration from the Incompleteness formalization. -/
def specialize {p : L.Semiformula (0 + 1)} (b : T ⊢¹ p.all :+> Γ) (t : L.Term) :
    T ⊢¹ p.substs₁ t :+> Γ := by
  apply TDerivation.cut (p := p.all)
  · exact (TDerivation.wk b <| by intro x; simp; tauto)
  · rw [Semiformula.neg_all]
    apply TDerivation.ex t
    apply TDerivation.em (p.substs₁ t)

end TDerivation
end Theory
end Language

namespace Language
namespace Theory
namespace TProof

variable {T U : L.TTheory} {p q : L.Formula}

/-- Condition D2 -/
def modusPonens (d : T ⊢ p ==> q) (b : T ⊢ p) : T ⊢ q := TDerivation.modusPonens d b

/-- Imported declaration from the Incompleteness formalization. -/
def byAxm {p : L.Formula} (h : p ∈' T.thy) : T ⊢ p := TDerivation.byAxm p h (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def ofSubset (h : T ⊆ U) {p : L.Formula} : T ⊢ p → U ⊢ p := TDerivation.ofSubset h

lemma of_subset (h : T ⊆ U) {p : L.Formula} : T ⊢! p → U ⊢! p := by rintro ⟨b⟩; exact ⟨ofSubset h b⟩

instance : Entailment.ModusPonens T := ⟨modusPonens⟩

instance : Entailment.NegationEquiv T where
  negEquiv p := by
    simp only [Axioms.NegEquiv, LogicalConnective.iff, Semiformula.imp_def,
      Semiformula.neg_neg, Semiformula.neg_or, Semiformula.neg_falsum]
    apply TDerivation.and
    · apply TDerivation.or
      apply TDerivation.rotate₁
      apply TDerivation.or
      exact TDerivation.em p
    · apply TDerivation.or
      apply TDerivation.and
      · exact TDerivation.em p
      · exact TDerivation.verum

instance : Entailment.Minimal T where
  verum := TDerivation.toTProof <| TDerivation.verum
  imply₁ (p q) := by
    simp only [Axioms.Imply₁, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em p
  imply₂ (p q r) := by
    simp only [Axioms.Imply₂, Semiformula.imp_def, Semiformula.neg_or, Semiformula.neg_neg]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₂
    apply TDerivation.and
    · exact TDerivation.em p
    · apply TDerivation.rotate₃
      apply TDerivation.and
      · exact TDerivation.em p
      · apply TDerivation.and
        · exact TDerivation.em q
        · exact TDerivation.em r
  and₁ (p q) := by
    simp only [Axioms.AndElim₁, Semiformula.imp_def, Semiformula.neg_and]
    apply TDerivation.or
    apply TDerivation.or
    exact TDerivation.em p
  and₂ (p q) := by
    simp only [Axioms.AndElim₂, Semiformula.imp_def, Semiformula.neg_and]
    apply TDerivation.or
    apply TDerivation.or
    exact TDerivation.em q
  and₃ (p q) := by
    simp only [Axioms.AndInst, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.and
    · exact TDerivation.em p
    · exact TDerivation.em q
  or₁ (p q) := by
    simp only [Axioms.OrInst₁, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em p
  or₂ (p q) := by
    simp only [Axioms.OrInst₂, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em q
  or₃ (p q r) := by
    simp only [Axioms.OrElim, Semiformula.imp_def, Semiformula.neg_or, Semiformula.neg_neg]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.and
    · apply TDerivation.rotate₃
      apply TDerivation.and
      · exact TDerivation.em p
      · exact TDerivation.em r
    · apply TDerivation.rotate₂
      apply TDerivation.and
      · exact TDerivation.em q
      · exact TDerivation.em r

instance : Entailment.Classical T where
  dne p := by
    simp only [Axioms.DNE, Semiformula.neg_neg, Semiformula.imp_def]
    apply TDerivation.or
    exact TDerivation.em p

/-- Imported declaration from the Incompleteness formalization. -/
def exIntro (p : L.Semiformula (0 + 1)) (t : L.Term) (b : T ⊢ p.substs₁ t) :
    T ⊢ p.ex :=
  TDerivation.ex t b

lemma «ex_intro!» (p : L.Semiformula (0 + 1)) (t : L.Term) (b : T ⊢! p.substs₁ t) :
    T ⊢! p.ex :=
  ⟨exIntro _ t b.get⟩

/-- Imported declaration from the Incompleteness formalization. -/
def specialize {p : L.Semiformula (0 + 1)} (b : T ⊢ p.all) (t : L.Term) :
    T ⊢ p.substs₁ t :=
  TDerivation.specialize b t

lemma «specialize!» {p : L.Semiformula (0 + 1)} (b : T ⊢! p.all) (t : L.Term) :
    T ⊢! p.substs₁ t :=
  ⟨TDerivation.specialize b.get t⟩

/-- Imported declaration from the Incompleteness formalization. -/
def conj (ps : L.SemiformulaVec 0) (ds : ∀ i, (hi : i < len ps.val) → T ⊢ ps.nth i hi) :
    T ⊢ ps.conj :=
  TDerivation.conj ps ds

lemma «conj!» (ps : L.SemiformulaVec 0) (ds : ∀ i, (hi : i < len ps.val) → T ⊢! ps.nth i hi) :
    T ⊢! ps.conj :=
  ⟨conj ps fun i hi ↦ (ds i hi).get⟩

/-- Imported declaration from the Incompleteness formalization. -/
def conj' (ps : L.SemiformulaVec 0) (ds : ∀ i, (hi :
    i < len ps.val) → T ⊢ ps.nth (len ps.val - (i + 1)) (sub_succ_lt_self hi)) :
    T ⊢ ps.conj :=
  TDerivation.conj ps <| fun i hi ↦ by
    have h := ds (len ps.val - (i + 1)) (by simp [tsub_lt_iff_left (succ_le_iff_lt.mpr hi)])
    simp only [sub_succ_lt_selfs hi] at h
    exact h

/-- Imported declaration from the Incompleteness formalization. -/
def conjOr' (ps : L.SemiformulaVec 0) (q) (ds : ∀ i, (hi :
    i < len ps.val) → T ⊢ ps.nth (len ps.val - (i + 1)) (sub_succ_lt_self hi) ⋎ q) :
    T ⊢ ps.conj ⋎ q :=
  TDerivation.or <| TDerivation.conj ps <| fun i hi ↦ by
    simpa [sub_succ_lt_selfs hi] using TDerivation.orInv (ds (len ps.val - (i + 1)) (by simp
      [tsub_lt_iff_left (succ_le_iff_lt.mpr hi)]))

/-- Imported declaration from the Incompleteness formalization. -/
def disj (ps : L.SemiformulaVec 0) {i} (hi : i < len ps.val) (d : T ⊢ ps.nth i hi) : T ⊢ ps.disj :=
  TDerivation.disj ps hi d

/-- Imported declaration from the Incompleteness formalization. -/
def shift {p : L.Formula} (d : T ⊢ p) : T ⊢ p.shift := by
  have h := TDerivation.shift d
  simp only [Language.Sequent.shift_insert, Language.Sequent.shift_empty] at h
  exact h

lemma «shift!» {p : L.Formula} (d : T ⊢! p) :
    T ⊢! p.shift :=
  ⟨by
    have h := TDerivation.shift d.get
    simp only [Language.Sequent.shift_insert, Language.Sequent.shift_empty] at h
    exact h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def all {p : L.Semiformula (0 + 1)} (dp : T ⊢ p.free) :
    T ⊢ p.all :=
  TDerivation.all (by rw [Language.Sequent.shift_empty]; exact dp)

lemma «all!» {p : L.Semiformula (0 + 1)} (dp : T ⊢! p.free) : T ⊢! p.all := ⟨all dp.get⟩

/-- Imported declaration from the Incompleteness formalization. -/
def generalizeAux {C : L.Formula} {p : L.Semiformula (0 + 1)} (dp : T ⊢ C.shift ==> p.free) :
    T ⊢ C ==> p.all := by
  rw [Semiformula.imp_def] at dp ⊢
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.all
  exact TDerivation.wk (TDerivation.orInv dp) (by intro x; simp; tauto)

lemma conj_shift (Γ : List L.Formula) : (⋀Γ).shift = ⋀(Γ.map .shift) := by
    induction Γ using List.induction_with_singleton
    case hnil => simp
    case hsingle => simp [List.conj₂]
    case hcons p ps hps ih => simp [hps, ih]

/-- Imported declaration from the Incompleteness formalization. -/
def generalize {Γ} {p : L.Semiformula (0 + 1)} (d : Γ.map .shift ⊢[T] p.free) : Γ ⊢[T] p.all := by
  apply Entailment.FiniteContext.ofDef
  apply generalizeAux
  simpa [conj_shift] using Entailment.FiniteContext.toDef d

lemma «generalize!» {Γ} {p : L.Semiformula (0 + 1)} (d : Γ.map .shift ⊢[T]! p.free) :
    Γ ⊢[T]! p.all :=
  ⟨generalize d.get⟩

/-- Imported declaration from the Incompleteness formalization. -/
def specializeWithCtxAux {C : L.Formula} {p : L.Semiformula (0 + 1)} (d : T ⊢ C ==> p.all) (t :
    L.Term) :
    T ⊢ C ==> p.substs₁ t := by
  rw [Semiformula.imp_def] at d ⊢
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.specialize
  exact TDerivation.wk (TDerivation.orInv d) (by intro x; simp; tauto)

/-- Imported declaration from the Incompleteness formalization. -/
def specializeWithCtx {Γ} {p : L.Semiformula (0 + 1)} (d : Γ ⊢[T] p.all) (t) :
    Γ ⊢[T] p.substs₁ t :=
  specializeWithCtxAux d t

lemma «specialize_with_ctx!» {Γ} {p : L.Semiformula (0 + 1)} (d : Γ ⊢[T]! p.all) (t) :
    Γ ⊢[T]! p.substs₁ t :=
  ⟨specializeWithCtx d.get t⟩

/-- Imported declaration from the Incompleteness formalization. -/
def ex {p : L.Semiformula (0 + 1)} (t) (dp : T ⊢ p.substs₁ t) :
    T ⊢ p.ex :=
  TDerivation.ex t (by exact dp)

lemma «ex!» {p : L.Semiformula (0 + 1)} (t) (dp : T ⊢! p.substs₁ t) : T ⊢! p.ex := ⟨ex t dp.get⟩

end TProof
end Theory
end Language

end «lp_section_4»
end Arith
end LO
