/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.GraphLanguage
import LeanPool.InfinitaryLogic.Methods.ConstantSupport
/-!
# Graph axioms: totality and functionality (Craig Layer 3, Unit 5a)

The sentences asserting that the graph relations of a symbol set `F` really are function
graphs: for each `f ∈ F`, **totality** `∀ x⃗ ∃ y, G_f(x⃗, y)` and **functionality**
`∀ x⃗ y z, G_f(x⃗,y) → G_f(x⃗,z) → y = z`, bundled as `graphAxioms F` — the countable
conjunction over `F` (hence `[Countable ↥F]`; the sentence does not depend on a choice of proof
of countability, and `F = ∅` correctly produces a tautology).

Quantifier blocks are `forallBlock`/`existsBlock` with the output variable **last**, matching
the graph-relation convention `funMap f args = output`.

## Main Results

* `realize_graphTotality` / `realize_graphFunctionality` — the per-symbol semantic gates.
* `realize_graphAxioms_iff` — realizing the bundle is exactly realizing both gates for every
  `f ∈ F`; `realize_graphAxioms_union` — the semantic union lemma.
* `graphExpansion_realizes_graphAxioms` — the graph expansion of an actual `L`-structure
  satisfies the axioms for every `F`.
* `relationsIn_graphAxioms = graphRelSym L '' F` (and `functionsIn_graphAxioms = ∅`) — the
  exact occurrence identities.

Unit 5b consumes these to reconstruct an `L`-structure from any model of `graphAxioms F`.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-! ## The axiom sentences -/

/-- **Totality** of the graph relation of `f`: `∀ x⃗, ∃ y, G_f(x⃗, y)` — output variable last. -/
def graphTotality {n : ℕ} (f : L.Functions n) : (graphLanguage L).Sentenceω :=
  .forallBlock (k := n) (.existsBlock (k := 1)
    (.rel (GraphRelation.graph f)
      (Fin.snoc (fun j => Term.var (Sum.inr (Fin.castAdd 1 (Fin.natAdd 0 j))))
        (Term.var (Sum.inr (Fin.natAdd (0 + n) 0))))))

/-- **Functionality** of the graph relation of `f`:
`∀ x⃗ y z, G_f(x⃗, y) → G_f(x⃗, z) → y = z` — one universal block of `n + 2` variables, the two
output candidates last. -/
def graphFunctionality {n : ℕ} (f : L.Functions n) : (graphLanguage L).Sentenceω :=
  .forallBlock (k := n + 2)
    ((BoundedFormulaω.rel (GraphRelation.graph f)
        (Fin.snoc (fun j => Term.var (Sum.inr (Fin.natAdd 0 (Fin.castAdd 2 j))))
          (Term.var (Sum.inr (Fin.natAdd 0 (Fin.natAdd n 0)))))).imp
      ((BoundedFormulaω.rel (GraphRelation.graph f)
          (Fin.snoc (fun j => Term.var (Sum.inr (Fin.natAdd 0 (Fin.castAdd 2 j))))
            (Term.var (Sum.inr (Fin.natAdd 0 (Fin.natAdd n 1)))))).imp
        (.equal (Term.var (Sum.inr (Fin.natAdd 0 (Fin.natAdd n 0))))
          (Term.var (Sum.inr (Fin.natAdd 0 (Fin.natAdd n 1)))))))

/-- **The graph axioms** of a symbol set `F`: totality and functionality of `G_f` for every
`f ∈ F`, as one countable conjunction. `F = ∅` produces a tautology. -/
noncomputable def graphAxioms (F : Set (Σ n, L.Functions n)) [Countable ↥F] :
    (graphLanguage L).Sentenceω :=
  letI : Encodable ↥F := Encodable.ofCountable _
  BoundedFormulaω.einf fun p : ↥F => (graphTotality p.1.2).and (graphFunctionality p.1.2)

/-! ## Semantic gates -/

section Semantics

variable {M : Type} [(graphLanguage L).Structure M]

/-- Totality realizes to: every argument tuple has an output related by `G_f`. -/
theorem realize_graphTotality {n : ℕ} (f : L.Functions n) :
    Sentenceω.Realize (graphTotality f) M ↔
      ∀ ws : Fin n → M, ∃ y : M, RelMap (L := graphLanguage L) (GraphRelation.graph f) (Fin.snoc ws y) := by
  have htuple : ∀ (ws : Fin n → M) (ys : Fin 1 → M),
      (fun i => Term.realize
          -- the sentence semantics supplies the empty tuple as `default`; it is definitionally
          -- `Fin.elim0`, but the statement has to be in the shape the goal actually carries
          (Sum.elim (Empty.elim : Empty → M) (Fin.append (Fin.append default ws) ys))
          ((Fin.snoc (fun j => Term.var (Sum.inr (Fin.castAdd 1 (Fin.natAdd 0 j))))
            (Term.var (Sum.inr (Fin.natAdd (0 + n) 0))) :
            Fin (n + 1) → (graphLanguage L).Term (Empty ⊕ Fin (0 + n + 1))) i)) =
        Fin.snoc ws (ys 0) := by
    intro ws ys
    funext i
    cases i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, Fin.snoc_last]
      exact Fin.append_right _ _ 0
    | cast j =>
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      show Fin.append (Fin.append Fin.elim0 ws) ys (Fin.castAdd 1 (Fin.natAdd 0 j)) = ws j
      rw [Fin.append_left, Fin.append_right]
  show BoundedFormulaω.Realize _ _ _ ↔ _
  rw [graphTotality, BoundedFormulaω.realize_forallBlock]
  refine forall_congr' fun ws => ?_
  rw [BoundedFormulaω.realize_existsBlock]
  constructor
  · rintro ⟨ys, hy⟩
    rw [BoundedFormulaω.realize_rel, htuple ws ys] at hy
    exact ⟨ys 0, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨fun _ => y, ?_⟩
    rw [BoundedFormulaω.realize_rel, htuple ws fun _ => y]
    exact hy

/-- Functionality realizes to: `G_f` relates each argument tuple to at most one output. -/
theorem realize_graphFunctionality {n : ℕ} (f : L.Functions n) :
    Sentenceω.Realize (graphFunctionality f) M ↔
      ∀ (ws : Fin n → M) (y z : M),
        RelMap (L := graphLanguage L) (GraphRelation.graph f) (Fin.snoc ws y) →
        RelMap (L := graphLanguage L) (GraphRelation.graph f) (Fin.snoc ws z) → y = z := by
  have htuple : ∀ (us : Fin (n + 2) → M) (b : Fin 2),
      (fun i => Term.realize
          -- `default`, not `Fin.elim0`: see the note in `realize_graphTotality`
          (Sum.elim (Empty.elim : Empty → M) (Fin.append default us))
          ((Fin.snoc (fun j => Term.var (Sum.inr (Fin.natAdd 0 (Fin.castAdd 2 j))))
            (Term.var (Sum.inr (Fin.natAdd 0 (Fin.natAdd n b)))) :
            Fin (n + 1) → (graphLanguage L).Term (Empty ⊕ Fin (0 + (n + 2)))) i)) =
        Fin.snoc (fun j => us (Fin.castAdd 2 j)) (us (Fin.natAdd n b)) := by
    intro us b
    funext i
    cases i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, Fin.snoc_last]
      show Fin.append Fin.elim0 us (Fin.natAdd 0 (Fin.natAdd n b)) = us (Fin.natAdd n b)
      exact Fin.append_right _ _ _
    | cast j =>
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      show Fin.append Fin.elim0 us (Fin.natAdd 0 (Fin.castAdd 2 j)) = us (Fin.castAdd 2 j)
      exact Fin.append_right _ _ _
  have hvar : ∀ (us : Fin (n + 2) → M) (b : Fin 2),
      Term.realize (Sum.elim (Empty.elim : Empty → M) (Fin.append default us))
        (Term.var (Sum.inr (Fin.natAdd 0 (Fin.natAdd n b))) :
          (graphLanguage L).Term (Empty ⊕ Fin (0 + (n + 2)))) = us (Fin.natAdd n b) := by
    intro us b
    show Fin.append Fin.elim0 us (Fin.natAdd 0 (Fin.natAdd n b)) = us (Fin.natAdd n b)
    exact Fin.append_right _ _ _
  show BoundedFormulaω.Realize _ _ _ ↔ _
  rw [graphFunctionality, BoundedFormulaω.realize_forallBlock]
  constructor
  · intro h ws y z hy hz
    have hu := h (Fin.append ws ![y, z])
    rw [BoundedFormulaω.realize_imp, BoundedFormulaω.realize_imp,
      BoundedFormulaω.realize_rel, BoundedFormulaω.realize_rel, BoundedFormulaω.realize_equal,
      htuple _ 0, htuple _ 1, hvar, hvar] at hu
    have hws : (fun j => Fin.append ws ![y, z] (Fin.castAdd 2 j)) = ws :=
      funext fun j => Fin.append_left ws ![y, z] j
    have hy' : Fin.append ws ![y, z] (Fin.natAdd n 0) = y := Fin.append_right ws ![y, z] 0
    have hz' : Fin.append ws ![y, z] (Fin.natAdd n 1) = z := Fin.append_right ws ![y, z] 1
    rw [hws, hy', hz'] at hu
    exact hu hy hz
  · intro h us
    rw [BoundedFormulaω.realize_imp, BoundedFormulaω.realize_imp,
      BoundedFormulaω.realize_rel, BoundedFormulaω.realize_rel, BoundedFormulaω.realize_equal,
      htuple _ 0, htuple _ 1, hvar, hvar]
    exact h _ _ _

/-- The bundle realizes iff both gates realize for every symbol of `F`. -/
theorem realize_graphAxioms_iff (F : Set (Σ n, L.Functions n)) [Countable ↥F] :
    Sentenceω.Realize (graphAxioms F) M ↔
      ∀ p : ↥F, Sentenceω.Realize (graphTotality p.1.2) M ∧ Sentenceω.Realize (graphFunctionality p.1.2) M := by
  let : Encodable ↥F := Encodable.ofCountable _
  show BoundedFormulaω.Realize _ _ _ ↔ _
  rw [graphAxioms, BoundedFormulaω.realize_einf]
  exact forall_congr' fun p => BoundedFormulaω.realize_and _ _

/-- The semantic union lemma: the axioms of a union are the conjunction of the axioms. -/
theorem realize_graphAxioms_union (F₁ F₂ : Set (Σ n, L.Functions n))
    [Countable ↥F₁] [Countable ↥F₂] :
    haveI : Countable ↥(F₁ ∪ F₂) :=
      ((Set.countable_coe_iff.mp ‹_›).union (Set.countable_coe_iff.mp ‹_›)).to_subtype
    (Sentenceω.Realize (graphAxioms (F₁ ∪ F₂)) M ↔
      Sentenceω.Realize (graphAxioms F₁) M ∧ Sentenceω.Realize (graphAxioms F₂) M) := by
  have : Countable ↥(F₁ ∪ F₂) :=
    ((Set.countable_coe_iff.mp ‹_›).union (Set.countable_coe_iff.mp ‹_›)).to_subtype
  rw [realize_graphAxioms_iff, realize_graphAxioms_iff, realize_graphAxioms_iff]
  constructor
  · intro h
    exact ⟨fun p => h ⟨p.1, Or.inl p.2⟩, fun p => h ⟨p.1, Or.inr p.2⟩⟩
  · rintro ⟨h₁, h₂⟩ ⟨p, hp | hp⟩
    exacts [h₁ ⟨p, hp⟩, h₂ ⟨p, hp⟩]

end Semantics

/-- The graph expansion of an `L`-structure satisfies the graph axioms of every symbol set. -/
theorem graphExpansion_realizes_graphAxioms (F : Set (Σ n, L.Functions n)) [Countable ↥F]
    (M : Type) [L.Structure M] :
    letI := graphExpansion L M
    Sentenceω.Realize (graphAxioms F) M := by
  let := graphExpansion L M
  rw [realize_graphAxioms_iff]
  intro p
  constructor
  · rw [realize_graphTotality]
    intro ws
    refine ⟨funMap p.1.2 ws, ?_⟩
    rw [graphExpansion_relMap_graph, Fin.init_snoc, Fin.snoc_last]
  · rw [realize_graphFunctionality]
    intro ws y z hy hz
    rw [graphExpansion_relMap_graph, Fin.init_snoc, Fin.snoc_last] at hy hz
    exact hy.symm.trans hz

/-! ## Occurrence identities -/

private theorem relationsIn_graphTotality {n : ℕ} (f : L.Functions n) :
    (graphTotality f).relationsIn = {⟨n + 1, GraphRelation.graph f⟩} := by
  rw [graphTotality, BoundedFormulaω.relationsIn_forallBlock,
    BoundedFormulaω.relationsIn_existsBlock]
  rfl

private theorem relationsIn_graphFunctionality {n : ℕ} (f : L.Functions n) :
    (graphFunctionality f).relationsIn = {⟨n + 1, GraphRelation.graph f⟩} := by
  rw [graphFunctionality, BoundedFormulaω.relationsIn_forallBlock]
  show ({⟨n + 1, GraphRelation.graph f⟩} ∪ ({⟨n + 1, GraphRelation.graph f⟩} ∪ ∅) :
    Set (Σ k, (graphLanguage L).Relations k)) = {⟨n + 1, GraphRelation.graph f⟩}
  rw [Set.union_empty, Set.union_self]

/-- **The exact occurrence identity**: the graph axioms of `F` mention exactly the graph
relations of `F`. -/
theorem relationsIn_graphAxioms (F : Set (Σ n, L.Functions n)) [Countable ↥F] :
    (graphAxioms F).relationsIn = graphRelSym L '' F := by
  let : Encodable ↥F := Encodable.ofCountable _
  have hpt : ∀ p : ↥F,
      ((graphTotality p.1.2).and (graphFunctionality p.1.2)).relationsIn =
        {(⟨p.1.1 + 1, GraphRelation.graph p.1.2⟩ : Σ k, (graphLanguage L).Relations k)} := by
    intro p
    rw [BoundedFormulaω.relationsIn_and, relationsIn_graphTotality,
      relationsIn_graphFunctionality, Set.union_self]
  rw [graphAxioms, BoundedFormulaω.relationsIn_einf, Set.iUnion_congr hpt]
  ext q
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩

/-- No function symbol occurs in the graph axioms (the graph language is relational). -/
private theorem functionsIn_graphAxioms (F : Set (Σ n, L.Functions n)) [Countable ↥F] :
    (graphAxioms F).functionsIn = ∅ :=
  BoundedFormulaω.functionsIn_of_isRelational _

end FirstOrder.Language
