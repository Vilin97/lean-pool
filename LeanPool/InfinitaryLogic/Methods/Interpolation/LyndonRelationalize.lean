/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.PolarityCalculus
import LeanPool.InfinitaryLogic.Methods.Interpolation.Relationalize
import LeanPool.InfinitaryLogic.Methods.Interpolation.GraphAxioms
import LeanPool.InfinitaryLogic.Methods.Interpolation.BackTranslate
/-!
# Signed occurrences through the relationalization layer (issue #14, Unit 6 — the D6 gate)

The polarity bookkeeping of the graph translation, in three gates.

**Gate 1 — the atomic calculus.**  Term graphs are *positive-only*: `termGraphAux` is built from
graph atoms by conjunction, `einf`, and existential blocks — all sign-preserving — so its negative
set is empty and its positive set is the whole `graphRelSym`-image.  The graph axioms, by contrast,
do use their graph relations in **both** signs (functionality has one in an antecedent); what
matters is that they contribute **no base-relation occurrence in either sign**
(`relationsInSigned_graphAxioms_inter_base`), which is why the identities below are insensitive to
whether the axioms sit in a conjunction or an antecedent.

**Gate 2 — base-polarity preservation (the stop/go equation).**

```
relationsInSigned s (relationalizeFormula φ) ∩ Set.range (baseRelSym L)
  = baseRelSym L '' relationsInSigned s φ
```

Relationalization preserves base-relation polarity *on the nose*, in the audit's exact
image/intersection form, with `positiveRelationsIn`/`negativeRelationsIn` corollaries and
preimage-shaped consumer lemmas.

**Gate 3 — back-translation.**

```
relationsInSigned s (backTranslateFormula θ) = baseRelSym L ⁻¹' relationsInSigned s θ
```

Here the key acceptance fact lands: a **graph** atom back-translates to an *equality*, whose signed
sets are empty in both signs.  So graph relations may carry arbitrary polarity in the graph world
and still disappear harmlessly.  Composing the two gates gives the exact base-polarity identities
for Craig's graph antecedent `(graphAxioms F).and (relationalizeFormula r)` and consequent
`(graphAxioms F).imp (relationalizeFormula r)`.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}} {α β : Type}

/-! ## Symbol-range disjointness -/

/-! ## Gate 1: the atomic calculus — term graphs are positive-only -/

/-- **The term-graph signed identity**, both signs at once (the recursion needs both): positive
occurrences are the whole `graphRelSym`-image, negative occurrences are empty — term graphs are
built from graph atoms by conjunction, `einf`, and existential blocks, all sign-preserving. -/
private theorem relationsInSigned_termGraphAux :
    ∀ {m : ℕ} (t : L.Term β) (ρ : β → (graphLanguage L).Term (α ⊕ Fin m))
      (y : (graphLanguage L).Term (α ⊕ Fin m)),
      relationsInSigned true (termGraphAux t ρ y) = graphRelSym L '' t.functionsIn ∧
        relationsInSigned false (termGraphAux t ρ y) = ∅
  | _, .var z, ρ, y => by
    refine ⟨?_, rfl⟩
    change relationsInSigned true (BoundedFormulaω.equal (ρ z) y) = _
    rw [relationsInSigned_equal, Term.functionsIn, Set.image_empty]
  | m, .func f ts, ρ, y => by
    constructor
    · change relationsInSigned true (BoundedFormulaω.existsBlock _) = _
      rw [relationsInSigned_existsBlock, relationsInSigned_and, relationsInSigned_einf,
        Set.iUnion_congr fun i => (relationsInSigned_termGraphAux (ts i) _ _).1]
      change (⋃ i, graphRelSym L '' (ts i).functionsIn) ∪ {graphRelSym L ⟨_, f⟩} = _
      rw [← Set.image_iUnion, Set.union_singleton, ← Set.image_insert_eq]
      rfl
    · change relationsInSigned false (BoundedFormulaω.existsBlock _) = _
      rw [relationsInSigned_existsBlock, relationsInSigned_and, relationsInSigned_einf,
        Set.iUnion_congr fun i => (relationsInSigned_termGraphAux (ts i) _ _).2]
      change (⋃ _i : Fin _, (∅ : Set (Σ n, GraphRelation L n))) ∪ ∅ = ∅
      rw [Set.iUnion_empty, Set.union_empty]

/-- **The equality atom's translation is positive-only**, with exactly the two terms' graph
relations. -/
private theorem relationsInSigned_equalGraph {n : ℕ} (t u : L.Term (α ⊕ Fin n)) :
    relationsInSigned true (equalGraph t u) =
        graphRelSym L '' (t.functionsIn ∪ u.functionsIn) ∧
      relationsInSigned false (equalGraph t u) = ∅ := by
  constructor
  · change relationsInSigned true (BoundedFormulaω.existsBlock _) = _
    rw [relationsInSigned_existsBlock, relationsInSigned_and,
      (relationsInSigned_termGraphAux t _ _).1, (relationsInSigned_termGraphAux u _ _).1,
      Set.image_union]
  · change relationsInSigned false (BoundedFormulaω.existsBlock _) = _
    rw [relationsInSigned_existsBlock, relationsInSigned_and,
      (relationsInSigned_termGraphAux t _ _).2, (relationsInSigned_termGraphAux u _ _).2,
      Set.union_self]

/-- **The relation atom's translation is positive-only**: the arguments' graph relations *and* the
base symbol itself, all positive; nothing negative. -/
private theorem relationsInSigned_relGraph {n k : ℕ} (R : L.Relations k)
    (ts : Fin k → L.Term (α ⊕ Fin n)) :
    relationsInSigned true (relGraph R ts) =
        graphRelSym L '' (⋃ i, (ts i).functionsIn) ∪ {baseRelSym L ⟨k, R⟩} ∧
      relationsInSigned false (relGraph R ts) = ∅ := by
  constructor
  · change relationsInSigned true (BoundedFormulaω.existsBlock _) = _
    rw [relationsInSigned_existsBlock, relationsInSigned_and, relationsInSigned_einf,
      Set.iUnion_congr fun i => (relationsInSigned_termGraphAux (ts i) _ _).1,
      relationsInSigned_rel, Set.image_iUnion, ite_eq_left rfl]
    rfl
  · change relationsInSigned false (BoundedFormulaω.existsBlock _) = _
    rw [relationsInSigned_existsBlock, relationsInSigned_and, relationsInSigned_einf,
      Set.iUnion_congr fun i => (relationsInSigned_termGraphAux (ts i) _ _).2,
      relationsInSigned_rel]
    change (⋃ _i : Fin _, (∅ : Set (Σ n, GraphRelation L n))) ∪
      (if false then {(⟨k, GraphRelation.base R⟩ : Σ l, GraphRelation L l)} else ∅) = ∅
    rw [Set.iUnion_empty, ite_eq_right (by simp), Set.union_empty]

/-- Preimage form of range-disjointness: no base symbol pulls back from a graph image. -/
private theorem preimage_baseRelSym_graphRelSym_image (X : Set (Σ n, L.Functions n)) :
    baseRelSym L ⁻¹' (graphRelSym L '' X) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro p ⟨q, -, hq⟩
  exact baseRelSym_ne_graphRelSym p q hq.symm

/-- The graph axioms have **no base-relation occurrence in either sign** — the fact that makes the
base-polarity identities insensitive to which side the axioms sit on. -/
private theorem preimage_baseRelSym_relationsInSigned_graphAxioms (s : Bool)
    (F : Set (Σ n, L.Functions n)) [Countable ↥F] :
    baseRelSym L ⁻¹' relationsInSigned s (graphAxioms F) = ∅ := by
  refine Set.eq_empty_of_subset_empty ?_
  intro p hp
  have hmem : baseRelSym L p ∈ graphRelSym L '' F := by
    rw [← relationsIn_graphAxioms F]
    exact relationsInSigned_subset_relationsIn s _ hp
  exact absurd (Set.mem_preimage.mpr hmem)
    (by rw [preimage_baseRelSym_graphRelSym_image F]; exact Set.notMem_empty p)

/-! ## Gate 2: base-polarity preservation (the stop/go equation) -/

/-- **The D6 stop/go equation, membership form** — the workhorse.  A base symbol occurs with sign
`s` in the relationalization exactly when it occurs with sign `s` in the original.  Phrased as a
membership equivalence so the induction never touches set operations at the two (definitionally
equal but syntactically distinct) relation-symbol types. -/
private theorem mem_relationsInSigned_relationalizeFormula (s : Bool) (p : Σ n, L.Relations n) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n),
      baseRelSym L p ∈ relationsInSigned s (relationalizeFormula φ) ↔
        p ∈ relationsInSigned s φ
  | _, .falsum => by
    rw [relationalizeFormula_falsum, relationsInSigned_falsum, relationsInSigned_falsum]
    exact iff_of_false (Set.notMem_empty _) (Set.notMem_empty _)
  | _, .equal t u => by
    rw [relationalizeFormula_equal, relationsInSigned_equal]
    cases s with
    | true =>
      rw [(relationsInSigned_equalGraph t u).1]
      refine iff_of_false ?_ (Set.notMem_empty _)
      rintro ⟨q, -, hq⟩
      exact baseRelSym_ne_graphRelSym p q hq.symm
    | false =>
      rw [(relationsInSigned_equalGraph t u).2]
      exact iff_of_false (Set.notMem_empty _) (Set.notMem_empty _)
  | _, .rel R ts => by
    rw [relationalizeFormula_rel, relationsInSigned_rel]
    cases s with
    | true =>
      rw [(relationsInSigned_relGraph R ts).1, ite_eq_left rfl]
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro (⟨q, -, hq⟩ | hq)
        · exact absurd hq.symm (baseRelSym_ne_graphRelSym p q)
        · exact baseRelSym_injective hq
      · rintro rfl
        exact Or.inr rfl
    | false =>
      rw [(relationsInSigned_relGraph R ts).2, ite_eq_right (by simp)]
      exact iff_of_false (Set.notMem_empty _) (Set.notMem_empty _)
  | _, .imp φ ψ => by
    rw [relationalizeFormula_imp, relationsInSigned_imp, relationsInSigned_imp]
    constructor
    · rintro (h | h)
      · exact Or.inl ((mem_relationsInSigned_relationalizeFormula (!s) p φ).mp h)
      · exact Or.inr ((mem_relationsInSigned_relationalizeFormula s p ψ).mp h)
    · rintro (h | h)
      · exact Or.inl ((mem_relationsInSigned_relationalizeFormula (!s) p φ).mpr h)
      · exact Or.inr ((mem_relationsInSigned_relationalizeFormula s p ψ).mpr h)
  | _, .all φ => by
    rw [relationalizeFormula_all, relationsInSigned_all, relationsInSigned_all]
    exact mem_relationsInSigned_relationalizeFormula s p φ
  | _, .iSup φs => by
    rw [relationalizeFormula_iSup, relationsInSigned_iSup, relationsInSigned_iSup]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, (mem_relationsInSigned_relationalizeFormula s p (φs i)).mp hi⟩
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, (mem_relationsInSigned_relationalizeFormula s p (φs i)).mpr hi⟩
  | _, .iInf φs => by
    rw [relationalizeFormula_iInf, relationsInSigned_iInf, relationsInSigned_iInf]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, (mem_relationsInSigned_relationalizeFormula s p (φs i)).mp hi⟩
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, (mem_relationsInSigned_relationalizeFormula s p (φs i)).mpr hi⟩

/-! ## Gate 3: back-translation -/

/-- **The back-translation signed identity, membership form**: a base symbol occurs with sign `s`
in the back-translation exactly when its graph image occurs with sign `s` upstream.  The `graph`
atom case is the acceptance fact: it back-translates to an *equality*, contributing to neither
sign, so graph relations may carry arbitrary polarity upstream and still vanish. -/
private theorem mem_relationsInSigned_backTranslateFormula (s : Bool) (p : Σ n, L.Relations n) :
    ∀ {n : ℕ} (θ : (graphLanguage L).BoundedFormulaω α n),
      p ∈ relationsInSigned s (backTranslateFormula θ) ↔
        baseRelSym L p ∈ relationsInSigned s θ
  | _, .falsum => by
    change p ∈ relationsInSigned s (BoundedFormulaω.falsum : L.BoundedFormulaω α _) ↔ _
    rw [relationsInSigned_falsum, relationsInSigned_falsum]
    exact iff_of_false (Set.notMem_empty _) (Set.notMem_empty _)
  | _, .equal t u => by
    change p ∈ relationsInSigned s (BoundedFormulaω.equal (ungraphTerm t) (ungraphTerm u)) ↔ _
    rw [relationsInSigned_equal, relationsInSigned_equal]
    exact iff_of_false (Set.notMem_empty _) (Set.notMem_empty _)
  | _, .rel (GraphRelation.base R₀) ts => by
    change p ∈ relationsInSigned s (BoundedFormulaω.rel R₀ fun i => ungraphTerm (ts i)) ↔ _
    rw [relationsInSigned_rel, relationsInSigned_rel]
    cases s with
    | true =>
      rw [ite_eq_left rfl, ite_eq_left rfl]
      constructor
      · rintro rfl; exact rfl
      · intro h; exact baseRelSym_injective (Set.mem_singleton_iff.mp h)
    | false =>
      rw [ite_eq_right (by simp), ite_eq_right (by simp)]
      exact iff_of_false (Set.notMem_empty _) (Set.notMem_empty _)
  | _, .rel (GraphRelation.graph f) ts => by
    -- the graph atom back-translates to an equality: empty in both signs
    change p ∈ relationsInSigned s (BoundedFormulaω.equal _ _) ↔ _
    rw [relationsInSigned_equal, relationsInSigned_rel]
    cases s with
    | true =>
      rw [ite_eq_left rfl]
      refine iff_of_false (Set.notMem_empty _) ?_
      intro h
      exact baseRelSym_ne_graphRelSym p ⟨_, f⟩ (Set.mem_singleton_iff.mp h)
    | false =>
      rw [ite_eq_right (by simp)]
      exact iff_of_false (Set.notMem_empty _) (Set.notMem_empty _)
  | _, .imp φ ψ => by
    change p ∈ relationsInSigned s ((backTranslateFormula φ).imp (backTranslateFormula ψ)) ↔ _
    rw [relationsInSigned_imp, relationsInSigned_imp]
    constructor
    · rintro (h | h)
      · exact Or.inl ((mem_relationsInSigned_backTranslateFormula (!s) p φ).mp h)
      · exact Or.inr ((mem_relationsInSigned_backTranslateFormula s p ψ).mp h)
    · rintro (h | h)
      · exact Or.inl ((mem_relationsInSigned_backTranslateFormula (!s) p φ).mpr h)
      · exact Or.inr ((mem_relationsInSigned_backTranslateFormula s p ψ).mpr h)
  | _, .all φ => by
    change p ∈ relationsInSigned s (backTranslateFormula φ).all ↔ _
    rw [relationsInSigned_all, relationsInSigned_all]
    exact mem_relationsInSigned_backTranslateFormula s p φ
  | _, .iSup φs => by
    change p ∈ relationsInSigned s (BoundedFormulaω.iSup fun i => backTranslateFormula (φs i)) ↔ _
    rw [relationsInSigned_iSup, relationsInSigned_iSup]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, (mem_relationsInSigned_backTranslateFormula s p (φs i)).mp hi⟩
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, (mem_relationsInSigned_backTranslateFormula s p (φs i)).mpr hi⟩
  | _, .iInf φs => by
    change p ∈ relationsInSigned s (BoundedFormulaω.iInf fun i => backTranslateFormula (φs i)) ↔ _
    rw [relationsInSigned_iInf, relationsInSigned_iInf]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, (mem_relationsInSigned_backTranslateFormula s p (φs i)).mp hi⟩
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, (mem_relationsInSigned_backTranslateFormula s p (φs i)).mpr hi⟩

/-- **Gate 3**: the signed occurrences of a back-translation are the base-embedding preimage of the
graph formula's signed occurrences. -/
private theorem relationsInSigned_backTranslateFormula (s : Bool) {n : ℕ}
    (θ : (graphLanguage L).BoundedFormulaω α n) :
    relationsInSigned s (backTranslateFormula θ) = baseRelSym L ⁻¹' relationsInSigned s θ := by
  ext p
  exact mem_relationsInSigned_backTranslateFormula s p θ

/-- Gate 3, positive corollary. -/
theorem positiveRelationsIn_backTranslateFormula {n : ℕ}
    (θ : (graphLanguage L).BoundedFormulaω α n) :
    (backTranslateFormula θ).positiveRelationsIn = baseRelSym L ⁻¹' θ.positiveRelationsIn :=
  relationsInSigned_backTranslateFormula true θ

/-- Gate 3, negative corollary. -/
theorem negativeRelationsIn_backTranslateFormula {n : ℕ}
    (θ : (graphLanguage L).BoundedFormulaω α n) :
    (backTranslateFormula θ).negativeRelationsIn = baseRelSym L ⁻¹' θ.negativeRelationsIn :=
  relationsInSigned_backTranslateFormula false θ

/-! ## The base-polarity identities for Craig's graph roots -/

/-- Preimage form of the graph-antecedent identity — the shape the endpoint consumes, so that no
`Sigma`/definitional-equality friction leaks into the assembly. -/
theorem preimage_baseRelSym_graphAnd (s : Bool) (F : Set (Σ n, L.Functions n)) [Countable ↥F]
    (φ : L.Sentenceω) :
    baseRelSym L ⁻¹' relationsInSigned s ((graphAxioms F).and (relationalizeFormula φ)) =
      relationsInSigned s φ := by
  rw [relationsInSigned_and]
  ext p
  constructor
  · rintro (h | h)
    · have h1 : p ∈ baseRelSym L ⁻¹' relationsInSigned s (graphAxioms F) := h
      rw [preimage_baseRelSym_relationsInSigned_graphAxioms s F] at h1
      exact absurd h1 (Set.notMem_empty p)
    · exact (mem_relationsInSigned_relationalizeFormula s p φ).mp h
  · intro hp
    exact Or.inr ((mem_relationsInSigned_relationalizeFormula s p φ).mpr hp)

/-- Preimage form of the graph-consequent identity: the axioms sit in an antecedent, so the
implication flips their sign — and they still contribute nothing to the base part. -/
theorem preimage_baseRelSym_graphImp (s : Bool) (F : Set (Σ n, L.Functions n)) [Countable ↥F]
    (φ : L.Sentenceω) :
    baseRelSym L ⁻¹' relationsInSigned s ((graphAxioms F).imp (relationalizeFormula φ)) =
      relationsInSigned s φ := by
  rw [relationsInSigned_imp]
  ext p
  constructor
  · rintro (h | h)
    · have h1 : p ∈ baseRelSym L ⁻¹' relationsInSigned (!s) (graphAxioms F) := h
      rw [preimage_baseRelSym_relationsInSigned_graphAxioms (!s) F] at h1
      exact absurd h1 (Set.notMem_empty p)
    · exact (mem_relationsInSigned_relationalizeFormula s p φ).mp h
  · intro hp
    exact Or.inr ((mem_relationsInSigned_relationalizeFormula s p φ).mpr hp)

end FirstOrder.Language
