/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.FirstOrder.Basic

/-! # SubLanguage -/


namespace LO

namespace FirstOrder

variable {L : Language.{u}} {L₁ : Language.{u}} {L₂ : Language.{u}}

namespace Language

/-- Imported declaration from the Incompleteness formalization. -/
def subLanguage (L : Language) (pfunc : ∀ k, L.Func k → Prop) (prel : ∀ k, L.Rel k → Prop) :
    Language where
  Func := fun k => Subtype (pfunc k)
  Rel  := fun k => Subtype (prel k)

section «lp_section_1»

variable (L)

variable {pf : (k : ℕ) → L.Func k → Prop} {pr : (k : ℕ) → L.Rel k → Prop}

/-- Imported declaration from the Incompleteness formalization. -/
def ofSubLanguage : subLanguage L pf pr →ᵥ L where
  func := Subtype.val
  rel  := Subtype.val

@[simp] lemma ofSubLanguage_onFunc :
    L.ofSubLanguage.func φ = φ.val := rfl

@[simp] lemma ofSubLanguage_onRel :
    L.ofSubLanguage.rel φ = φ.val := rfl

end «lp_section_1»

end Language

namespace Semiterm

open Language
variable [∀ k, DecidableEq (L.Func k)]

/-- Imported declaration from the Incompleteness formalization. -/
def lang : Semiterm L μ n → Finset (Σ k, L.Func k)
  | #_       => ∅
  | &_       => ∅
  | func f v => insert ⟨_, f⟩ <| Finset.biUnion Finset.univ (fun i => lang (v i))

@[simp] lemma lang_func {k} (f : L.Func k) (v : Fin k → Semiterm L μ n) :
    ⟨k, f⟩ ∈ (func f v).lang := by simp[lang]

lemma lang_func_ss {k} (f : L.Func k) (v : Fin k → Semiterm L μ n) (i) :
    (v i).lang ⊆ (func f v).lang :=
  by
    intro x h
    simp only [lang, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨i, h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def toSubLanguage' (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop) : ∀ t : Semiterm L μ n,
    (∀ k f, ⟨k, f⟩ ∈ t.lang → pf k f) → Semiterm (subLanguage L pf pr) μ n
  | #x,                    _ => #x
  | &x,                    _ => &x
  | func (arity := k) f v, h => func ⟨f, h k f (by simp)⟩
      (fun i => toSubLanguage' pf pr (v i) (fun k' f' h' => h k' f' (lang_func_ss f v i h')))

@[simp] lemma lMap_toSubLanguage' (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop)
  (t : Semiterm L μ n) (h : ∀ k f, ⟨k, f⟩ ∈ t.lang → pf k f) :
    (t.toSubLanguage' pf pr h).lMap L.ofSubLanguage = t :=
  by induction t <;> simp[*, toSubLanguage', lMap_func]

end Semiterm

namespace Semiformula

variable [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)]

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def langFunc : ∀ {n}, Semiformula L μ n → Finset (Σ k, L.Func k)
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, rel  _ v => Finset.biUnion Finset.univ (fun i => (v i).lang)
  | _, nrel _ v => Finset.biUnion Finset.univ (fun i => (v i).lang)
  | _, φ ⋏ ψ    => langFunc φ ∪ langFunc ψ
  | _, φ ⋎ ψ    => langFunc φ ∪ langFunc ψ
  | _, ∀' φ     => langFunc φ
  | _, ∃' φ     => langFunc φ

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def langRel : ∀ {n}, Semiformula L μ n → Finset (Σ k, L.Rel k)
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, rel  r _ => {⟨_, r⟩}
  | _, nrel r _ => {⟨_, r⟩}
  | _, φ ⋏ ψ    => langRel φ ∪ langRel ψ
  | _, φ ⋎ ψ    => langRel φ ∪ langRel ψ
  | _, ∀' φ     => langRel φ
  | _, ∃' φ     => langRel φ

omit [∀ k, DecidableEq (L.Rel k)] in
lemma langFunc_rel_ss {k} (r : L.Rel k) (v : Fin k → Semiterm L μ n) (i) :
    (v i).lang ⊆ (rel r v).langFunc :=
  by
    intro x h
    simp only [langFunc, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def toSubLanguage' (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop) : ∀ {n} (φ :
    Semiformula L μ n),
    (∀ k f, ⟨k, f⟩ ∈ φ.langFunc → pf k f) →
    (∀ k r, ⟨k, r⟩ ∈ φ.langRel → pr k r) →
    Semiformula (L.subLanguage pf pr) μ n
  | _, ⊤,        _,  _  => ⊤
  | _, ⊥,        _,  _  => ⊥
  | _, rel r v,  hf, hr =>
      rel ⟨r, hr _ r (by simp[langRel])⟩
        (fun i => (v i).toSubLanguage' pf pr (fun k f h => hf k f (langFunc_rel_ss r v i h)))
  | _, nrel r v, hf, hr =>
      nrel ⟨r, hr _ r (by simp[langRel])⟩
        (fun i => (v i).toSubLanguage' pf pr (fun k f h => hf k f (langFunc_rel_ss r v i h)))
  | _, φ ⋏ ψ,    hf, hr =>
      toSubLanguage' pf pr φ (fun k f h =>
        hf k f (Finset.mem_union_left _ h)) (fun k r h => hr k r (Finset.mem_union_left _ h)) ⋏
      toSubLanguage' pf pr ψ (fun k f h =>
        hf k f (Finset.mem_union_right _ h)) (fun k r h => hr k r (Finset.mem_union_right _ h))
  | _, φ ⋎ ψ,    hf, hr =>
      toSubLanguage' pf pr φ (fun k f h =>
        hf k f (Finset.mem_union_left _ h)) (fun k r h => hr k r (Finset.mem_union_left _ h)) ⋎
      toSubLanguage' pf pr ψ (fun k f h =>
        hf k f (Finset.mem_union_right _ h)) (fun k r h => hr k r (Finset.mem_union_right _ h))
  | _, ∀' φ,     hf, hr => ∀' toSubLanguage' pf pr φ hf hr
  | _, ∃' φ,     hf, hr => ∃' toSubLanguage' pf pr φ hf hr

@[simp] lemma lMap_toSubLanguage'
  (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop) {n} (φ : Semiformula L μ n)
  (hf : ∀ k f, ⟨k, f⟩ ∈ φ.langFunc → pf k f) (hr : ∀ k r, ⟨k, r⟩ ∈ φ.langRel → pr k r) :
    lMap L.ofSubLanguage (φ.toSubLanguage' pf pr hf hr) = φ := by
  induction φ using rec' <;> simp[*, toSubLanguage', lMap_rel, lMap_nrel]

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def languageFuncIndexed (φ : Semiformula L μ n) (k) : Finset (L.Func k) :=
  Finset.preimage (langFunc φ) (Sigma.mk k) (Set.injOn_of_injective sigma_mk_injective)

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def languageRelIndexed (φ : Semiformula L μ n) (k) : Finset (L.Rel k) :=
  Finset.preimage (langRel φ) (Sigma.mk k) (Set.injOn_of_injective sigma_mk_injective)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev languageFinset (Γ : Finset (Semiformula L μ n)) : Language :=
  Language.subLanguage L (fun k f =>
    ∃ φ ∈ Γ, ⟨k, f⟩ ∈ langFunc φ) (fun k r => ∃ φ ∈ Γ, ⟨k, r⟩ ∈ langRel φ)

noncomputable instance (Γ : Finset (Semiformula L μ n)) (k) : Fintype ((languageFinset Γ).Func k) :=
  Fintype.subtype (Γ.biUnion (languageFuncIndexed · k)) (by simp[languageFuncIndexed])

noncomputable instance (Γ : Finset (Semiformula L μ n)) (k) : Fintype ((languageFinset Γ).Rel k) :=
  Fintype.subtype (Γ.biUnion (languageRelIndexed · k)) (by simp[languageRelIndexed])

/-- Imported declaration from the Incompleteness formalization. -/
def toSubLanguageFinsetSelf {Γ : Finset (Semiformula L μ n)} {φ} (h : φ ∈ Γ) :
    Semiformula (languageFinset Γ) μ n :=
  φ.toSubLanguage' _ _ (fun _ _ hf => ⟨φ, h, hf⟩) (fun _ _ hr => ⟨φ, h, hr⟩)

@[simp] lemma lMap_toSubLanguageFinsetSelf {Γ : Finset (Semiformula L μ n)} {φ} (h : φ ∈ Γ) :
    lMap L.ofSubLanguage (toSubLanguageFinsetSelf h) = φ :=
  lMap_toSubLanguage' _ _ _ _ _

end Semiformula

namespace Structure

instance subLanguageStructure {pf : ∀ k, L.Func k → Prop} {pr : ∀ k, L.Rel k → Prop}
  {M : Type w} [s : Structure L M] : Structure (Language.subLanguage L pf pr) M :=
  s.lMap (Language.ofSubLanguage L)

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
noncomputable def extendStructure (Φ : L₁ →ᵥ L₂) {M : Type w} [Nonempty M] (s : Structure L₁ M) :
    Structure L₂ M where
  func := fun {k} f₂ v =>
    Classical.epsilon (fun y => ∃ f₁ : L₁.Func k, Φ.func f₁ = f₂ ∧ y = s.func f₁ v)
  rel  := fun {k} r₂ v => ∃ r₁ : L₁.Rel k, Φ.rel r₁ = r₂ ∧ s.rel r₁ v

namespace extendStructure

variable {M : Type u} [Nonempty M] (s₁ : Structure L₁ M)

protected lemma func
    (Φ : L₁ →ᵥ L₂)
    {k} (injf : Function.Injective (Φ.func : L₁.Func k →
      L₂.Func k)) (f₁ : L₁.Func k) (v : Fin k → M) :
    (s₁.extendStructure Φ).func (Φ.func f₁) v = s₁.func f₁ v := by
  change
    Classical.epsilon
      (fun y => ∃ f₁' : L₁.Func k, Φ.func f₁' = Φ.func f₁ ∧ y = s₁.func f₁' v) =
        s₁.func f₁ v
  have : ∃ y, ∃ f₁' : L₁.Func k, Φ.func f₁' = Φ.func f₁ ∧ y = s₁.func f₁' v :=
    ⟨s₁.func f₁ v, f₁, rfl, rfl⟩
  rcases Classical.epsilon_spec this with ⟨f', f'eq, h⟩
  rcases injf f'eq with rfl; exact h

protected lemma rel
    (Φ : L₁ →ᵥ L₂)
    {k} (injr : Function.Injective (Φ.rel : L₁.Rel k → L₂.Rel k))
    (r₁ : L₁.Rel k) (v : Fin k → M) :
    (s₁.extendStructure Φ).rel (Φ.rel r₁) v ↔ s₁.rel r₁ v := by
  change (∃ r₁' : L₁.Rel k, Φ.rel r₁' = Φ.rel r₁ ∧ s₁.rel r₁' v) ↔ s₁.rel r₁ v
  refine ⟨by intros h; rcases h with ⟨r₁', e, h⟩; rcases injr e; exact h,
    by intros h; refine ⟨r₁, rfl, h⟩⟩

lemma val_lMap
    (Φ : L₁ →ᵥ L₂)
    (injf : ∀ k, Function.Injective (Φ.func : L₁.Func k → L₂.Func k))
      {n} (e : Fin n → M) (ε : μ → M)
      (t : Semiterm L₁ μ n) :
      Semiterm.val (s₁.extendStructure Φ) e ε (t.lMap Φ) = Semiterm.val s₁ e ε t := by
    induction t with
    | bvar =>
      simp only [Semiterm.lMap_bvar, Semiterm.val_bvar]
    | fvar =>
      simp only [Semiterm.lMap_fvar, Semiterm.val_fvar]
    | func f v ih =>
      simp only [Semiterm.lMap_func, Semiterm.val_func, ih]
      exact extendStructure.func s₁ Φ (injf _) f fun i ↦ Semiterm.val s₁ e ε (v i)

open Semiformula

lemma eval_lMap
    (Φ : L₁ →ᵥ L₂)
    (injf : ∀ k, Function.Injective (Φ.func : L₁.Func k → L₂.Func k))
    (injr : ∀ k, Function.Injective (Φ.rel : L₁.Rel k → L₂.Rel k))
    {n} (e : Fin n → M) (ε : μ → M)
    {φ : Semiformula L₁ μ n} :
      Eval (s₁.extendStructure Φ) e ε (lMap Φ φ) ↔ Eval s₁ e ε φ := by
    induction φ using Semiformula.rec' with
    | hverum =>
      simp only [LogicalConnective.HomClass.map_top, «Prop».top_eq_true]
    | hfalsum =>
      simp only [LogicalConnective.HomClass.map_bot, «Prop».bot_eq_false]
    | hrel r v =>
      simp only [Semiformula.lMap_rel, eval_rel, val_lMap s₁ Φ injf e ε]
      exact extendStructure.rel s₁ Φ (injr _) r (fun i => Semiterm.val s₁ e ε (v i))
    | hnrel r v =>
      simp only [Semiformula.lMap_nrel, eval_nrel, val_lMap s₁ Φ injf e ε]
      simpa[not_iff_not] using
        extendStructure.rel s₁ Φ (injr _) r (fun i => Semiterm.val s₁ e ε (v i))
    | hand _ _ ihφ ihψ =>
      simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, ihφ, ihψ]
    | hor _ _ ihφ ihψ =>
      simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq, ihφ, ihψ]
    | hall _ ih =>
      simp only [Semiformula.lMap_all, Semiformula.eval_all, Nat.succ_eq_add_one, ih]
    | hex _ ih =>
      simp only [Semiformula.lMap_ex, Semiformula.eval_ex, Nat.succ_eq_add_one, ih]

lemma models_lMap
    (Φ : L₁ →ᵥ L₂)
    (injf : ∀ k, Function.Injective (Φ.func : L₁.Func k → L₂.Func k))
    (injr : ∀ k, Function.Injective (Φ.rel : L₁.Rel k → L₂.Rel k))
    (φ : SyntacticFormula L₁) :
    Semantics.Realize (s₁.extendStructure Φ).toStruc (Semiformula.lMap Φ φ) ↔
        Semantics.Realize s₁.toStruc φ := by
  simp [Semantics.Realize, Evalf, eval_lMap s₁ Φ injf injr]

end extendStructure

end Structure

section «lp_section_2»

lemma lMap_models_lMap_iff
    (Φ : L₁ →ᵥ L₂)
    (injf : ∀ k, Function.Injective (Φ.func : L₁.Func k → L₂.Func k))
    (injr : ∀ k, Function.Injective (Φ.rel : L₁.Rel k → L₂.Rel k))
    {T : Theory L₁} {φ : SyntacticFormula L₁} :
    Theory.lMap Φ T ⊨ Semiformula.lMap Φ φ ↔ T ⊨ φ := by
  constructor
  · intro h s₁ hs₁
    exact (Structure.extendStructure.models_lMap s₁.struc Φ injf injr φ).mp <| h
        (by simp only [Semantics.models, Theory.lMap, Semantics.realizeSet_iff, Set.mem_image,
            forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Set.mem_setOf_eq]
            intro φ hp
            exact (Structure.extendStructure.models_lMap s₁.struc Φ injf injr φ).mpr
              (hs₁.realize _ hp))
  · exact lMap_models_lMap

lemma satisfiable_lMap
    (Φ : L₁ →ᵥ L₂)
    (injf : ∀ k, Function.Injective (Φ.func : L₁.Func k → L₂.Func k))
    (injr : ∀ k, Function.Injective (Φ.rel : L₁.Rel k → L₂.Rel k))
    {T : Theory L₁} (s : Satisfiable T) :
    Satisfiable (Semiformula.lMap Φ '' T) := by
  rcases s with ⟨⟨M, i, s⟩, hM⟩
  exact ⟨⟨M, i, s.extendStructure Φ⟩, by
    simp only [Semantics.RealizeSet.image_iff]
    intro φ hp
    exact (Structure.extendStructure.models_lMap s Φ injf injr φ).mpr (hM.realize _ hp)⟩

end «lp_section_2»

end FirstOrder

end LO
