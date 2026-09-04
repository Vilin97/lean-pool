/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Semantics
/-!
# Fragments of `L_{ω₁ω}`

The foundational fragment interface of issue #13, per the frozen audit
(`docs/fragments-audit.md`): a fragment is an arity-indexed set of formulas over `Empty` free
variables (parameters enter semantically, through tuples), closed under CONSTRUCTOR COMPONENTS
only — the direction every induction (A-elementarity, Tarski–Vaught, Löwenheim–Skolem, chain
unions) consumes. Deliberately absent, per the audit: atomic-formula membership (would force
countable fragments to have countable languages), formation closure under countable
connectives (destroys countability), syntactic substitution closure (subsumed by semantic
parameters), and formal-negation closure (an NNF concern, #14).
-/

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

/-- **A fragment**: an arity-indexed set of `L_{ω₁ω}`-formulas closed under constructor
components. -/
structure Fragment (L : Language.{u, v}) where
  /-- The member formulas, tagged by arity. -/
  toSet : Set (Σ n, L.BoundedFormulaω Empty n)
  /-- Component closure: the antecedent of a member implication. -/
  imp_left_mem : ∀ {n : ℕ} {φ ψ : L.BoundedFormulaω Empty n},
    (⟨n, φ.imp ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet → ⟨n, φ⟩ ∈ toSet
  /-- Component closure: the consequent of a member implication. -/
  imp_right_mem : ∀ {n : ℕ} {φ ψ : L.BoundedFormulaω Empty n},
    (⟨n, φ.imp ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet → ⟨n, ψ⟩ ∈ toSet
  /-- Component closure: the body of a member universal. -/
  all_mem : ∀ {n : ℕ} {φ : L.BoundedFormulaω Empty (n + 1)},
    (⟨n, φ.all⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet → ⟨n + 1, φ⟩ ∈ toSet
  /-- Component closure: every component of a member countable conjunction. -/
  iInf_mem : ∀ {n : ℕ} {φs : ℕ → L.BoundedFormulaω Empty n},
    (⟨n, BoundedFormulaω.iInf φs⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet →
      ∀ k, ⟨n, φs k⟩ ∈ toSet
  /-- Component closure: every component of a member countable disjunction. -/
  iSup_mem : ∀ {n : ℕ} {φs : ℕ → L.BoundedFormulaω Empty n},
    (⟨n, BoundedFormulaω.iSup φs⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet →
      ∀ k, ⟨n, φs k⟩ ∈ toSet

namespace Fragment

instance : Membership (Σ n, L.BoundedFormulaω Empty n) (Fragment L) :=
  ⟨fun A p => p ∈ A.toSet⟩

theorem mem_def {A : Fragment L} {p : Σ n, L.BoundedFormulaω Empty n} :
    p ∈ A ↔ p ∈ A.toSet :=
  Iff.rfl

/-- The full fragment: every formula. -/
def top : Fragment L where
  toSet := Set.univ
  imp_left_mem _ := Set.mem_univ _
  imp_right_mem _ := Set.mem_univ _
  all_mem _ := Set.mem_univ _
  iInf_mem _ _ := Set.mem_univ _
  iSup_mem _ _ := Set.mem_univ _

/-- Fragments are closed under intersection. -/
def inter (A B : Fragment L) : Fragment L where
  toSet := A.toSet ∩ B.toSet
  imp_left_mem h := ⟨A.imp_left_mem h.1, B.imp_left_mem h.2⟩
  imp_right_mem h := ⟨A.imp_right_mem h.1, B.imp_right_mem h.2⟩
  all_mem h := ⟨A.all_mem h.1, B.all_mem h.2⟩
  iInf_mem h k := ⟨A.iInf_mem h.1 k, B.iInf_mem h.2 k⟩
  iSup_mem h k := ⟨A.iSup_mem h.1 k, B.iSup_mem h.2 k⟩

/-! ## Generated fragments -/

/-- The component-closure of a set of formulas, as an inductive reachability predicate. -/
inductive GeneratedFrom (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (Σ n, L.BoundedFormulaω Empty n) → Prop
  | base {p} (h : p ∈ S) : GeneratedFrom S p
  | imp_left {n : ℕ} {φ ψ : L.BoundedFormulaω Empty n} :
      GeneratedFrom S ⟨n, φ.imp ψ⟩ → GeneratedFrom S ⟨n, φ⟩
  | imp_right {n : ℕ} {φ ψ : L.BoundedFormulaω Empty n} :
      GeneratedFrom S ⟨n, φ.imp ψ⟩ → GeneratedFrom S ⟨n, ψ⟩
  | all_body {n : ℕ} {φ : L.BoundedFormulaω Empty (n + 1)} :
      GeneratedFrom S ⟨n, φ.all⟩ → GeneratedFrom S ⟨n + 1, φ⟩
  | iInf_comp {n : ℕ} {φs : ℕ → L.BoundedFormulaω Empty n} (k : ℕ) :
      GeneratedFrom S ⟨n, BoundedFormulaω.iInf φs⟩ → GeneratedFrom S ⟨n, φs k⟩
  | iSup_comp {n : ℕ} {φs : ℕ → L.BoundedFormulaω Empty n} (k : ℕ) :
      GeneratedFrom S ⟨n, BoundedFormulaω.iSup φs⟩ → GeneratedFrom S ⟨n, φs k⟩

/-- **The generated fragment**: the smallest fragment containing `S`. -/
def generated (S : Set (Σ n, L.BoundedFormulaω Empty n)) : Fragment L where
  toSet := {p | GeneratedFrom S p}
  imp_left_mem h := .imp_left h
  imp_right_mem h := .imp_right h
  all_mem h := .all_body h
  iInf_mem h k := .iInf_comp k h
  iSup_mem h k := .iSup_comp k h

theorem subset_generated (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    S ⊆ (generated S).toSet := fun _ h => .base h

/-! ### Set and order API

Minimal by design: `SetLike`, extensionality, and the order the `generated`/`inter`/`top`
constructions already induce.  **Not** a complete lattice — no consumer needs arbitrary suprema, and
a speculative one would have to justify closure of unions, which fails. -/

instance : SetLike (Fragment L) (Σ n, L.BoundedFormulaω Empty n) where
  coe A := A.toSet
  coe_injective := by
    rintro ⟨s, _, _, _, _, _⟩ ⟨t, _, _, _, _, _⟩ h
    congr

@[ext] theorem ext {A B : Fragment L} (h : ∀ p, p ∈ A ↔ p ∈ B) : A = B := SetLike.ext h

@[simp] theorem coe_toSet (A : Fragment L) : ((A : Set (Σ n, L.BoundedFormulaω Empty n))) = A.toSet :=
  rfl

instance : LE (Fragment L) := ⟨fun A B => A.toSet ⊆ B.toSet⟩

theorem le_def {A B : Fragment L} : A ≤ B ↔ ∀ p, p ∈ A → p ∈ B := Iff.rfl

instance : Top (Fragment L) := ⟨top⟩

@[simp] theorem mem_top (p : Σ n, L.BoundedFormulaω Empty n) : p ∈ (⊤ : Fragment L) :=
  Set.mem_univ p

instance : Min (Fragment L) := ⟨inter⟩

@[simp] theorem mem_inf {A B : Fragment L} {p : Σ n, L.BoundedFormulaω Empty n} :
    p ∈ A ⊓ B ↔ p ∈ A ∧ p ∈ B := Iff.rfl


/-- The generated fragment is the smallest one containing `S`. -/
theorem generated_le {S : Set (Σ n, L.BoundedFormulaω Empty n)} {A : Fragment L}
    (hSA : S ⊆ A.toSet) : (generated S).toSet ⊆ A.toSet := by
  intro p hp
  induction hp with
  | base h => exact hSA h
  | imp_left _ ih => exact A.imp_left_mem ih
  | imp_right _ ih => exact A.imp_right_mem ih
  | all_body _ ih => exact A.all_mem ih
  | iInf_comp k _ ih => exact A.iInf_mem ih k
  | iSup_comp k _ ih => exact A.iSup_mem ih k

/-- **The Galois-style characterization**: `generated` is left adjoint to the forgetful map to sets.
This is the form consumers want — it replaces `subset_generated`/`generated_le` pairs at call
sites. -/
theorem generated_le_iff {S : Set (Σ n, L.BoundedFormulaω Empty n)} {A : Fragment L} :
    generated S ≤ A ↔ S ⊆ A :=
  ⟨fun h _ hp => h (subset_generated S hp), fun h _ hp => generated_le h hp⟩

/-! ### Countability of generated fragments: the component-path encoding -/

/-- One component step, coded by a pair (tag, index). -/
def componentStep : (Σ n, L.BoundedFormulaω Empty n) → ℕ × ℕ →
    Option (Σ n, L.BoundedFormulaω Empty n)
  | ⟨n, .imp φ _⟩, (0, _) => some ⟨n, φ⟩
  | ⟨n, .imp _ ψ⟩, (1, _) => some ⟨n, ψ⟩
  | ⟨n, .all φ⟩, (2, _) => some ⟨n + 1, φ⟩
  | ⟨n, .iInf φs⟩, (3, k) => some ⟨n, φs k⟩
  | ⟨n, .iSup φs⟩, (4, k) => some ⟨n, φs k⟩
  | _, _ => none

/-- Iterated component steps along a list of codes. -/
def componentPath (p : Σ n, L.BoundedFormulaω Empty n) :
    List (ℕ × ℕ) → Option (Σ n, L.BoundedFormulaω Empty n)
  | [] => some p
  | c :: l => (componentStep p c).bind (componentPath · l)

theorem componentPath_append (p : Σ n, L.BoundedFormulaω Empty n) (l₁ l₂ : List (ℕ × ℕ)) :
    componentPath p (l₁ ++ l₂) = (componentPath p l₁).bind (componentPath · l₂) := by
  induction l₁ generalizing p with
  | nil => rfl
  | cons c l ih =>
    show (componentStep p c).bind (componentPath · (l ++ l₂))
      = ((componentStep p c).bind (componentPath · l)).bind (componentPath · l₂)
    cases componentStep p c with
    | none => rfl
    | some q => exact ih q

/-- A single step lands inside the generated set. -/
theorem GeneratedFrom.of_componentStep {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    {q p : Σ n, L.BoundedFormulaω Empty n} {c : ℕ × ℕ}
    (hq : GeneratedFrom S q) (h : componentStep q c = some p) : GeneratedFrom S p := by
  unfold componentStep at h
  split at h
  · exact Option.some_injective _ h ▸ hq.imp_left
  · exact Option.some_injective _ h ▸ hq.imp_right
  · exact Option.some_injective _ h ▸ hq.all_body
  · exact Option.some_injective _ h ▸ hq.iInf_comp _
  · exact Option.some_injective _ h ▸ hq.iSup_comp _
  · simp at h

/-- **The path characterization**: the generated fragment is exactly what is reachable from
`S` by finitely many coded component steps. -/
theorem generatedFrom_iff_path {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    {p : Σ n, L.BoundedFormulaω Empty n} :
    GeneratedFrom S p ↔ ∃ s ∈ S, ∃ l : List (ℕ × ℕ), componentPath s l = some p := by
  constructor
  · intro hp
    induction hp with
    | base h => exact ⟨_, h, [], rfl⟩
    | @imp_left n φ ψ _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(0, 0)], by rw [componentPath_append, hl]; rfl⟩
    | @imp_right n φ ψ _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(1, 0)], by rw [componentPath_append, hl]; rfl⟩
    | @all_body n φ _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(2, 0)], by rw [componentPath_append, hl]; rfl⟩
    | @iInf_comp n φs k _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(3, k)], by rw [componentPath_append, hl]; rfl⟩
    | @iSup_comp n φs k _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(4, k)], by rw [componentPath_append, hl]; rfl⟩
  · rintro ⟨s, hs, l, hl⟩
    have hgen : ∀ (l : List (ℕ × ℕ)) (q : Σ n, L.BoundedFormulaω Empty n),
        GeneratedFrom S q → componentPath q l = some p → GeneratedFrom S p := by
      intro l
      induction l with
      | nil => exact fun q hq hl => Option.some_injective _ hl ▸ hq
      | cons c l ih =>
        intro q hq hl
        show GeneratedFrom S p
        rw [show componentPath q (c :: l) = (componentStep q c).bind (componentPath · l)
          from rfl] at hl
        cases hstep : componentStep q c with
        | none => rw [hstep] at hl; exact absurd hl (by simp)
        | some r =>
          rw [hstep] at hl
          exact ih r (hq.of_componentStep hstep) hl
    exact hgen l s (.base hs) hl

/-- **Countability**: the fragment generated by a countable set is countable. -/
theorem generated_countable {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    (hS : S.Countable) : (generated S).toSet.Countable := by
  have hchar : (generated S).toSet
      = ⋃ s ∈ S, Option.some ⁻¹' Set.range (fun l : List (ℕ × ℕ) => componentPath s l) := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_range]
    exact generatedFrom_iff_path.trans (by
      constructor
      · rintro ⟨s, hs, l, hl⟩; exact ⟨s, hs, l, hl⟩
      · rintro ⟨s, hs, l, hl⟩; exact ⟨s, hs, l, hl⟩)
  rw [hchar]
  exact Set.Countable.biUnion hS fun s _ =>
    (Set.countable_range _).preimage (Option.some_injective _)

/-- The generated fragment of a single sentence — countable, no hypotheses. -/
def generatedSentence (φ : L.Sentenceω) : Fragment L :=
  generated {⟨0, φ⟩}

theorem generatedSentence_countable (φ : L.Sentenceω) :
    (generatedSentence φ).toSet.Countable :=
  generated_countable (Set.countable_singleton _)

theorem mem_generatedSentence (φ : L.Sentenceω) :
    (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ (generatedSentence φ).toSet :=
  subset_generated _ rfl

/-- The generated fragment of a COUNTABLE theory (the sentence case is automatic; theory
countability is an assumption, per the audit). -/
def generatedTheory (T : Set L.Sentenceω) : Fragment L :=
  generated ((fun φ => (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n)) '' T)

theorem generatedTheory_countable {T : Set L.Sentenceω} (hT : T.Countable) :
    (generatedTheory T).toSet.Countable :=
  generated_countable (hT.image _)

theorem mem_generatedTheory {T : Set L.Sentenceω} {φ : L.Sentenceω} (h : φ ∈ T) :
    (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ (generatedTheory T).toSet :=
  subset_generated _ ⟨φ, h, rfl⟩

end Fragment

end Language

end FirstOrder
