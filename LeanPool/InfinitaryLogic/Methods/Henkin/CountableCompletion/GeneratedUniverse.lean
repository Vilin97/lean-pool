/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.ConstantInstances
/-!
# The generated enumeration universe `U` (issue #8 tranche 2, commit 1)

`GenU r₁ r₂` is the countable domain the fair Henkin enumeration runs through: the two roots
`r₁, r₂`, all constant equalities, and all atomic relation instances over constants, closed
under the **unary** `C0`–`C4`/quantifier decomposition targets. Per the audit (§6b, §8) it is
NOT closed under forming new infinitary conjunctions/disjunctions — only components of existing
ones.

**Design.** The binary atomic closures (equality symmetry/transitivity, relation
one-coordinate replacement) are handled by *seeding*: all constant equalities and all constant
atomic relation instances are put in the seed (countably many, using `[Countable (Σ l,
L.Relations l)]`), so those closure *targets* already lie in `U`. Only the unary connective /
quantifier rules need reachability closure, which admits the component-path countability
argument of `Fragment.generated_countable`.

Acceptance gate (this commit): both roots ∈ `U`; closure under every `C0`–`C4` decomposition
target and under `instConst`; all constant reflexivity/symmetry/transitivity equalities and
atomic relation replacements present; `Countable ↥U`; every member has finite constant support.
The relational-core collapse lemma `exists_eq_constTerm` (every closed term is a constant) is
included — it drives the later term-model plumbing.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-! ## The relational-core collapse lemma -/

/-- **Collapse** (relational core): over a relational base, every closed `L[[ℕ]]`-term is a
constant. -/
theorem exists_eq_constTerm [L.IsRelational] (t : L[[ℕ]].Term Empty) :
    ∃ c : ℕ, t = constTerm c := by
  cases t with
  | var x => exact x.elim
  | @func l f ts =>
    rcases f with f | c
    · have : IsEmpty (L.Functions l) := ‹L.IsRelational› l
      exact isEmptyElim f
    · match l, c with
      | 0, c => exact ⟨c, congrArg _ (funext fun i => i.elim0)⟩
      | (l + 1), c => exact isEmptyElim c

/-! ## Seeds -/

/-- A constant as a term inside a sentence (`Empty ⊕ Fin 0` variable context). -/
def constTermS (c : ℕ) : L[[ℕ]].Term (Empty ⊕ Fin 0) :=
  Term.func (Sum.inr c : L[[ℕ]].Functions 0) Fin.elim0

/-- The closed constant `constTerm a`, relabeled into the sentence-term context, is
`constTermS a`. -/
theorem constTerm_relabel_inl (a : ℕ) :
    (constTerm (L' := L) (J := ℕ) a).relabel (Sum.inl : Empty → Empty ⊕ Fin 0) =
      constTermS a := by
  simp only [constTerm, constTermS, Term.relabel]
  congr 1
  funext i
  exact i.elim0

/-- The constant equality `c_a = c_b`. -/
def constEq (a b : ℕ) : L[[ℕ]].Sentenceω :=
  BoundedFormulaω.equal (constTermS a) (constTermS b)

/-- The atomic relation instance `R(c_{g 0}, …)`. -/
def relInst {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ) : L[[ℕ]].Sentenceω :=
  BoundedFormulaω.rel (Sum.inl R : L[[ℕ]].Relations l) (fun i => constTermS (g i))

/-- The seed: the two roots, all constant equalities, all constant atomic relation instances. -/
def seed (r₁ r₂ : L[[ℕ]].Sentenceω) : Set L[[ℕ]].Sentenceω :=
  {r₁, r₂}
  ∪ Set.range (fun p : ℕ × ℕ => constEq p.1 p.2)
  ∪ {χ | ∃ (l : ℕ) (R : L.Relations l) (g : Fin l → ℕ), χ = relInst R g}

/-! ## Reachability under the unary decomposition rules -/

/-- One-step reachability under the unary `C0`–`C4`/quantifier decomposition targets. -/
inductive ReachFrom (S : Set L[[ℕ]].Sentenceω) : L[[ℕ]].Sentenceω → Prop
  | base {p : L[[ℕ]].Sentenceω} : p ∈ S → ReachFrom S p
  | imp_negleft {φ ψ : L[[ℕ]].Sentenceω} : ReachFrom S (φ.imp ψ) → ReachFrom S φ.not
  | imp_right {φ ψ : L[[ℕ]].Sentenceω} : ReachFrom S (φ.imp ψ) → ReachFrom S ψ
  | negimp_left {φ ψ : L[[ℕ]].Sentenceω} : ReachFrom S (φ.imp ψ).not → ReachFrom S φ
  | negimp_right {φ ψ : L[[ℕ]].Sentenceω} : ReachFrom S (φ.imp ψ).not → ReachFrom S ψ.not
  | iInf_comp {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ) :
      ReachFrom S (BoundedFormulaω.iInf φs) → ReachFrom S (φs k)
  | negiInf_comp {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ) :
      ReachFrom S (BoundedFormulaω.iInf φs).not → ReachFrom S (φs k).not
  | iSup_comp {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ) :
      ReachFrom S (BoundedFormulaω.iSup φs) → ReachFrom S (φs k)
  | negiSup_comp {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ) :
      ReachFrom S (BoundedFormulaω.iSup φs).not → ReachFrom S (φs k).not
  | all_inst {φ : L[[ℕ]].BoundedFormulaω Empty 1} (c : ℕ) :
      ReachFrom S φ.all → ReachFrom S (instConst c φ)
  | negall_inst {φ : L[[ℕ]].BoundedFormulaω Empty 1} (c : ℕ) :
      ReachFrom S φ.all.not → ReachFrom S (instConst c φ).not

/-- **The generated universe**. -/
def GenU (r₁ r₂ : L[[ℕ]].Sentenceω) : Set L[[ℕ]].Sentenceω :=
  {p | ReachFrom (seed r₁ r₂) p}

variable {r₁ r₂ : L[[ℕ]].Sentenceω}

theorem seed_subset_genU : seed r₁ r₂ ⊆ GenU r₁ r₂ := fun _ h => .base h

theorem root₁_mem : r₁ ∈ GenU r₁ r₂ :=
  .base (Or.inl (Or.inl (Set.mem_insert _ _)))

theorem root₂_mem : r₂ ∈ GenU r₁ r₂ :=
  .base (Or.inl (Or.inl (Set.mem_insert_of_mem _ rfl)))

theorem constEq_mem (a b : ℕ) : constEq a b ∈ GenU r₁ r₂ :=
  .base (Or.inl (Or.inr ⟨(a, b), rfl⟩))

theorem eqRefl_mem (c : ℕ) : constEq c c ∈ GenU r₁ r₂ := constEq_mem c c

theorem relInst_mem {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ) :
    relInst R g ∈ GenU r₁ r₂ :=
  .base (Or.inr ⟨l, R, g, rfl⟩)

/-! ## Closure under the decomposition targets -/

theorem imp_negleft_mem {φ ψ : L[[ℕ]].Sentenceω} (h : φ.imp ψ ∈ GenU r₁ r₂) :
    φ.not ∈ GenU r₁ r₂ := h.imp_negleft
theorem imp_right_mem {φ ψ : L[[ℕ]].Sentenceω} (h : φ.imp ψ ∈ GenU r₁ r₂) :
    ψ ∈ GenU r₁ r₂ := h.imp_right
theorem negimp_left_mem {φ ψ : L[[ℕ]].Sentenceω} (h : (φ.imp ψ).not ∈ GenU r₁ r₂) :
    φ ∈ GenU r₁ r₂ := h.negimp_left
theorem negimp_right_mem {φ ψ : L[[ℕ]].Sentenceω} (h : (φ.imp ψ).not ∈ GenU r₁ r₂) :
    ψ.not ∈ GenU r₁ r₂ := h.negimp_right
theorem iInf_comp_mem {φs : ℕ → L[[ℕ]].Sentenceω} (k) (h : BoundedFormulaω.iInf φs ∈ GenU r₁ r₂) :
    φs k ∈ GenU r₁ r₂ := h.iInf_comp k
theorem negiInf_comp_mem {φs : ℕ → L[[ℕ]].Sentenceω} (k)
    (h : (BoundedFormulaω.iInf φs).not ∈ GenU r₁ r₂) : (φs k).not ∈ GenU r₁ r₂ := h.negiInf_comp k
theorem iSup_comp_mem {φs : ℕ → L[[ℕ]].Sentenceω} (k) (h : BoundedFormulaω.iSup φs ∈ GenU r₁ r₂) :
    φs k ∈ GenU r₁ r₂ := h.iSup_comp k
theorem negiSup_comp_mem {φs : ℕ → L[[ℕ]].Sentenceω} (k)
    (h : (BoundedFormulaω.iSup φs).not ∈ GenU r₁ r₂) : (φs k).not ∈ GenU r₁ r₂ := h.negiSup_comp k
theorem all_inst_mem {φ : L[[ℕ]].BoundedFormulaω Empty 1} (c) (h : φ.all ∈ GenU r₁ r₂) :
    instConst c φ ∈ GenU r₁ r₂ := h.all_inst c
theorem negall_inst_mem {φ : L[[ℕ]].BoundedFormulaω Empty 1} (c) (h : φ.all.not ∈ GenU r₁ r₂) :
    (instConst c φ).not ∈ GenU r₁ r₂ := h.negall_inst c

/-! ## Countability of the seed -/

theorem countable_relations_each [Countable (Σ l, L.Relations l)] (l : ℕ) :
    Countable (L.Relations l) :=
  Function.Injective.countable (f := fun r => (⟨l, r⟩ : Σ l, L.Relations l))
    (fun _ _ h => by simpa using h)

theorem seed_countable [Countable (Σ l, L.Relations l)] : (seed r₁ r₂).Countable := by
  refine Set.Countable.union (Set.Countable.union ?_ ?_) ?_
  · exact Set.countable_insert.mpr (Set.countable_singleton _)
  · exact Set.countable_range _
  · have : ∀ l, Countable (L.Relations l) := countable_relations_each
    have : {χ : L[[ℕ]].Sentenceω | ∃ (l : ℕ) (R : L.Relations l) (g : Fin l → ℕ), χ = relInst R g}
        = Set.range (fun p : Σ l, L.Relations l × (Fin l → ℕ) => relInst p.2.1 p.2.2) := by
      ext χ
      constructor
      · rintro ⟨l, R, g, rfl⟩; exact ⟨⟨l, R, g⟩, rfl⟩
      · rintro ⟨⟨l, R, g⟩, rfl⟩; exact ⟨l, R, g, rfl⟩
    rw [this]
    exact Set.countable_range _

/-! ## Countability of the generated universe (component-path encoding) -/

/-- One decomposition step, coded by `(tag, index)`. Matching on the tag first keeps the step
reducible on concrete members (the sentence discriminant is inspected only after the tag has
already selected the intended rule). -/
def uStep (p : L[[ℕ]].Sentenceω) (c : ℕ × ℕ) : Option L[[ℕ]].Sentenceω :=
  match c.1, p with
  | 0, .imp φ _ => some φ.not
  | 1, .imp _ ψ => some ψ
  | 2, .imp (.imp φ _) .falsum => some φ
  | 3, .imp (.imp _ ψ) .falsum => some ψ.not
  | 4, .iInf φs => some (φs c.2)
  | 5, .imp (.iInf φs) .falsum => some (φs c.2).not
  | 6, .iSup φs => some (φs c.2)
  | 7, .imp (.iSup φs) .falsum => some (φs c.2).not
  | 8, .all φ => some (instConst c.2 φ)
  | 9, .imp (.all φ) .falsum => some (instConst c.2 φ).not
  | _, _ => none

/-- Iterated steps along a list of codes. -/
def uPath (p : L[[ℕ]].Sentenceω) :
    List (ℕ × ℕ) → Option L[[ℕ]].Sentenceω
  | [] => some p
  | c :: l => (uStep p c).bind (uPath · l)

theorem uPath_append (p : L[[ℕ]].Sentenceω) (l₁ l₂ : List (ℕ × ℕ)) :
    uPath p (l₁ ++ l₂) = (uPath p l₁).bind (uPath · l₂) := by
  induction l₁ generalizing p with
  | nil => rfl
  | cons c l ih =>
    show (uStep p c).bind (uPath · (l ++ l₂))
      = ((uStep p c).bind (uPath · l)).bind (uPath · l₂)
    cases uStep p c with
    | none => rfl
    | some q => exact ih q

/-- A single coded step lands inside the reachability set. -/
theorem ReachFrom.of_uStep {S : Set L[[ℕ]].Sentenceω} {q p : L[[ℕ]].Sentenceω} {c : ℕ × ℕ}
    (hq : ReachFrom S q) (h : uStep q c = some p) : ReachFrom S p := by
  unfold uStep at h
  split at h
  · exact Option.some_injective _ h ▸ hq.imp_negleft
  · exact Option.some_injective _ h ▸ hq.imp_right
  · exact Option.some_injective _ h ▸ hq.negimp_left
  · exact Option.some_injective _ h ▸ hq.negimp_right
  · exact Option.some_injective _ h ▸ hq.iInf_comp _
  · exact Option.some_injective _ h ▸ hq.negiInf_comp _
  · exact Option.some_injective _ h ▸ hq.iSup_comp _
  · exact Option.some_injective _ h ▸ hq.negiSup_comp _
  · exact Option.some_injective _ h ▸ hq.all_inst _
  · exact Option.some_injective _ h ▸ hq.negall_inst _
  · exact absurd h (by simp)

/-- **The path characterization**: `ReachFrom S` is exactly what is reachable from `S` by
finitely many coded steps. -/
theorem reachFrom_iff_path {S : Set L[[ℕ]].Sentenceω} {p : L[[ℕ]].Sentenceω} :
    ReachFrom S p ↔ ∃ s ∈ S, ∃ l : List (ℕ × ℕ), uPath s l = some p := by
  constructor
  · intro hp
    induction hp with
    | base h => exact ⟨_, h, [], rfl⟩
    | @imp_negleft φ ψ _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(0, 0)], by rw [uPath_append, hl]; rfl⟩
    | @imp_right φ ψ _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(1, 0)], by rw [uPath_append, hl]; rfl⟩
    | @negimp_left φ ψ _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(2, 0)], by rw [uPath_append, hl]; rfl⟩
    | @negimp_right φ ψ _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(3, 0)], by rw [uPath_append, hl]; rfl⟩
    | @iInf_comp φs k _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(4, k)], by rw [uPath_append, hl]; rfl⟩
    | @negiInf_comp φs k _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(5, k)], by rw [uPath_append, hl]; rfl⟩
    | @iSup_comp φs k _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(6, k)], by rw [uPath_append, hl]; rfl⟩
    | @negiSup_comp φs k _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(7, k)], by rw [uPath_append, hl]; rfl⟩
    | @all_inst φ c _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(8, c)], by rw [uPath_append, hl]; rfl⟩
    | @negall_inst φ c _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(9, c)], by rw [uPath_append, hl]; rfl⟩
  · rintro ⟨s, hs, l, hl⟩
    have hgen : ∀ (l : List (ℕ × ℕ)) (q : L[[ℕ]].Sentenceω),
        ReachFrom S q → uPath q l = some p → ReachFrom S p := by
      intro l
      induction l with
      | nil => exact fun q hq hl => Option.some_injective _ hl ▸ hq
      | cons c l ih =>
        intro q hq hl
        rw [show uPath q (c :: l) = (uStep q c).bind (uPath · l) from rfl] at hl
        cases hstep : uStep q c with
        | none => rw [hstep] at hl; exact absurd hl (by simp)
        | some r => rw [hstep] at hl; exact ih r (hq.of_uStep hstep) hl
    exact hgen l s (.base hs) hl

/-- **Countability of `U`**. -/
theorem genU_countable [Countable (Σ l, L.Relations l)] : (GenU r₁ r₂).Countable := by
  have hchar : GenU r₁ r₂
      = ⋃ s ∈ seed r₁ r₂, Option.some ⁻¹' Set.range (fun l : List (ℕ × ℕ) => uPath s l) := by
    ext p
    simp only [GenU, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_range,
      exists_prop]
    exact reachFrom_iff_path
  rw [hchar]
  exact Set.Countable.biUnion seed_countable fun s _ =>
    (Set.countable_range _).preimage (Option.some_injective _)

/-! ## Finite constant support -/

theorem sentenceJConsts_all (φ : L[[ℕ]].BoundedFormulaω Empty 1) :
    sentenceJConsts (L' := L) (J := ℕ) φ.all = sentenceJConsts (L' := L) (J := ℕ) φ := rfl

theorem sentenceJConsts_instConst_subset (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1) :
    sentenceJConsts (L' := L) (J := ℕ) (instConst c φ)
      ⊆ sentenceJConsts (L' := L) (J := ℕ) φ.all ∪ {c} := by
  rw [instConst, sentenceJConsts_all]
  refine (sentenceJConsts_subst_constTerm (L' := L) φ.openBounds c).trans ?_
  rw [sentenceJConsts_openBounds]

theorem constTermS_jConsts (c : ℕ) :
    Term.jConsts (L' := L) (constTermS (L := L) c) ⊆ {c} := by
  intro k hk
  simp only [constTermS, Term.jConsts, Term.functionsIn, Set.iUnion_of_empty,
    Set.mem_insert_iff, Set.mem_empty_iff_false, or_false, Set.mem_ofPred_eq] at hk
  exact Set.mem_singleton_iff.mpr (Sum.inr.inj (eq_of_heq (Sigma.mk.inj_iff.mp hk).2))

/-- **Finite constant support**: assuming the roots have finite constant support, every member
of `U` does. -/
theorem genU_finite_support (hr₁ : (sentenceJConsts (L' := L) (J := ℕ) r₁).Finite)
    (hr₂ : (sentenceJConsts (L' := L) (J := ℕ) r₂).Finite) :
    ∀ p ∈ GenU r₁ r₂, (sentenceJConsts (L' := L) (J := ℕ) p).Finite := by
  intro p hp
  induction hp with
  | @base q hq =>
    rcases hq with (hq | ⟨⟨a, b⟩, rfl⟩) | ⟨l, R, g, rfl⟩
    · rcases hq with rfl | hq
      · exact hr₁
      · rw [Set.mem_singleton_iff] at hq; exact hq ▸ hr₂
    · refine Set.Finite.subset (Set.finite_singleton a |>.union (Set.finite_singleton b)) ?_
      intro k hk
      rcases hk with hk | hk
      · exact Or.inl (constTermS_jConsts a hk)
      · exact Or.inr (constTermS_jConsts b hk)
    · refine Set.Finite.subset (Set.finite_range g) ?_
      intro k hk
      obtain ⟨_, ⟨i, rfl⟩, hmem⟩ := hk
      exact ⟨i, (constTermS_jConsts (g i) hmem).symm ▸ rfl⟩
  | imp_negleft _ ih => rw [sentenceJConsts_not]; exact ih.subset (sentenceJConsts_imp_left _ _)
  | imp_right _ ih => exact ih.subset (sentenceJConsts_imp_right _ _)
  | negimp_left _ ih => rw [sentenceJConsts_not] at ih; exact ih.subset (sentenceJConsts_imp_left _ _)
  | negimp_right _ ih =>
    rw [sentenceJConsts_not] at ih ⊢
    exact ih.subset (sentenceJConsts_imp_right _ _)
  | iInf_comp k _ ih => exact ih.subset (sentenceJConsts_component_iInf _ k)
  | negiInf_comp k _ ih =>
    rw [sentenceJConsts_not] at ih ⊢
    exact ih.subset (sentenceJConsts_component_iInf _ k)
  | iSup_comp k _ ih => exact ih.subset (sentenceJConsts_component_iSup _ k)
  | negiSup_comp k _ ih =>
    rw [sentenceJConsts_not] at ih ⊢
    exact ih.subset (sentenceJConsts_component_iSup _ k)
  | all_inst c _ ih =>
    exact (ih.union (Set.finite_singleton c)).subset (sentenceJConsts_instConst_subset c _)
  | negall_inst c _ ih =>
    rw [sentenceJConsts_not] at ih ⊢
    exact (ih.union (Set.finite_singleton c)).subset (sentenceJConsts_instConst_subset c _)

/-! ## Minimality

`GenU` is the smallest set containing the seed and closed under the unary rules: the generic
induction principle for the generated universe. (The current paired construction carries its
side-membership bound as an explicit invariant instead of instantiating this principle, so
`genU_le` presently has no in-tree consumer; it is the library-level minimality statement.) -/
theorem genU_le {P : Set L[[ℕ]].Sentenceω} (hseed : seed r₁ r₂ ⊆ P)
    (himp_negleft : ∀ {φ ψ : L[[ℕ]].Sentenceω}, φ.imp ψ ∈ P → φ.not ∈ P)
    (himp_right : ∀ {φ ψ : L[[ℕ]].Sentenceω}, φ.imp ψ ∈ P → ψ ∈ P)
    (hnegimp_left : ∀ {φ ψ : L[[ℕ]].Sentenceω}, (φ.imp ψ).not ∈ P → φ ∈ P)
    (hnegimp_right : ∀ {φ ψ : L[[ℕ]].Sentenceω}, (φ.imp ψ).not ∈ P → ψ.not ∈ P)
    (hiInf : ∀ {φs : ℕ → L[[ℕ]].Sentenceω} (k), BoundedFormulaω.iInf φs ∈ P → φs k ∈ P)
    (hnegiInf : ∀ {φs : ℕ → L[[ℕ]].Sentenceω} (k),
      (BoundedFormulaω.iInf φs).not ∈ P → (φs k).not ∈ P)
    (hiSup : ∀ {φs : ℕ → L[[ℕ]].Sentenceω} (k), BoundedFormulaω.iSup φs ∈ P → φs k ∈ P)
    (hnegiSup : ∀ {φs : ℕ → L[[ℕ]].Sentenceω} (k),
      (BoundedFormulaω.iSup φs).not ∈ P → (φs k).not ∈ P)
    (hall : ∀ {φ : L[[ℕ]].BoundedFormulaω Empty 1} (c), φ.all ∈ P → instConst c φ ∈ P)
    (hnegall : ∀ {φ : L[[ℕ]].BoundedFormulaω Empty 1} (c),
      φ.all.not ∈ P → (instConst c φ).not ∈ P) :
    GenU r₁ r₂ ⊆ P := by
  intro p hp
  induction hp with
  | base h => exact hseed h
  | imp_negleft _ ih => exact himp_negleft ih
  | imp_right _ ih => exact himp_right ih
  | negimp_left _ ih => exact hnegimp_left ih
  | negimp_right _ ih => exact hnegimp_right ih
  | iInf_comp k _ ih => exact hiInf k ih
  | negiInf_comp k _ ih => exact hnegiInf k ih
  | iSup_comp k _ ih => exact hiSup k ih
  | negiSup_comp k _ ih => exact hnegiSup k ih
  | all_inst c _ ih => exact hall c ih
  | negall_inst c _ ih => exact hnegall c ih

end FirstOrder.Language
