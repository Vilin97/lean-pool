/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.GraphAxioms
import LeanPool.InfinitaryLogic.Methods.Interpolation.Relationalize
/-!
# Reconstructing functions from a model of the graph axioms (Craig Layer 3, Unit 5b)

From any nonempty `graphLanguage L`-structure satisfying `graphAxioms F`, a full (noncomputable)
`L.Structure`: for `f ∈ F` the function value is the totality witness (unique by
functionality), outside `F` an arbitrary element; every base relation is copied directly.

The results are deliberately **localized to `F`** — global round-trip structure identities are
false outside `F`, and nothing downstream needs them. The choice outside `F` is completely
irrelevant to every consumer:

* reconstructing a graph expansion preserves all base relations (definitionally) and `funMap`
  on every symbol of `F` (`reconstruct_graphExpansion_funMap`);
* graph-expanding a reconstruction preserves base relations (definitionally) and the graph
  relations of `F` (`graphExpansion_reconstruct_relMap_graph`);
* therefore formulas whose function support lies in `F` have identical semantics — the
  consumer-shaped capstone `realize_relationalize_reconstruct`, proved from the
  occurrence-aware congruence `realize_congr_symbolsIn`, the exact occurrence identity
  `relationsIn_relationalizeFormula`, and Unit 4's `realize_relationalizeFormula`.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

section Reconstruct

variable {M : Type} [Nonempty M] [(graphLanguage L).Structure M]
variable {F : Set (Σ n, L.Functions n)} [Countable ↥F]

/-- The function value extracted from a model of the graph axioms: the totality witness for
`f ∈ F` (unique by functionality), an arbitrary element outside `F`. -/
private noncomputable def graphValue (hAx : Sentenceω.Realize (graphAxioms F) M) {n : ℕ}
    (f : L.Functions n) (xs : Fin n → M) : M :=
  letI := Classical.dec ((⟨n, f⟩ : Σ n, L.Functions n) ∈ F)
  if h : (⟨n, f⟩ : Σ n, L.Functions n) ∈ F then
    Classical.choose
      ((realize_graphTotality f).mp ((realize_graphAxioms_iff F).mp hAx ⟨⟨n, f⟩, h⟩).1 xs)
  else Classical.arbitrary M

/-- The extracted value satisfies the graph relation. -/
private theorem graphValue_spec (hAx : Sentenceω.Realize (graphAxioms F) M) {n : ℕ}
    (f : L.Functions n) (h : (⟨n, f⟩ : Σ n, L.Functions n) ∈ F) (xs : Fin n → M) :
    RelMap (L := graphLanguage L) (GraphRelation.graph f)
      (Fin.snoc xs (graphValue hAx f xs)) := by
  rw [graphValue, dite_eq_left h]
  exact Classical.choose_spec
    ((realize_graphTotality f).mp ((realize_graphAxioms_iff F).mp hAx ⟨⟨n, f⟩, h⟩).1 xs)

/-- Uniqueness from functionality: anything the graph relation relates to `xs` is the
extracted value. -/
private theorem graphValue_unique (hAx : Sentenceω.Realize (graphAxioms F) M) {n : ℕ}
    (f : L.Functions n) (h : (⟨n, f⟩ : Σ n, L.Functions n) ∈ F) (xs : Fin n → M) (y : M)
    (hy : RelMap (L := graphLanguage L) (GraphRelation.graph f) (Fin.snoc xs y)) :
    y = graphValue hAx f xs :=
  (realize_graphFunctionality f).mp ((realize_graphAxioms_iff F).mp hAx ⟨⟨n, f⟩, h⟩).2
    xs y (graphValue hAx f xs) hy (graphValue_spec hAx f h xs)

/-- **The reconstructed `L`-structure**: functions from `graphValue`, base relations copied. -/
@[reducible] noncomputable def reconstructStructure (F : Set (Σ n, L.Functions n)) [Countable ↥F]
    (hAx : Sentenceω.Realize (graphAxioms F) M) : L.Structure M where
  funMap f xs := graphValue hAx f xs
  RelMap R xs := RelMap (L := graphLanguage L) (GraphRelation.base R) xs

/-- Base relations are copied directly — definitionally. -/
theorem reconstruct_relMap_base (hAx : Sentenceω.Realize (graphAxioms F) M) {n : ℕ}
    (R : L.Relations n) (v : Fin n → M) :
    (reconstructStructure F hAx).RelMap R v ↔
      RelMap (L := graphLanguage L) (GraphRelation.base R) v :=
  Iff.rfl



/-- Graph-expanding a reconstruction preserves the graph relations of `F`. -/
private theorem graphExpansion_reconstruct_relMap_graph (hAx : Sentenceω.Realize (graphAxioms F) M)
    {n : ℕ} (f : L.Functions n) (h : (⟨n, f⟩ : Σ n, L.Functions n) ∈ F)
    (v : Fin (n + 1) → M) :
    (@graphExpansion L M (reconstructStructure F hAx)).RelMap (GraphRelation.graph f) v ↔
      RelMap (L := graphLanguage L) (GraphRelation.graph f) v := by
  rw [graphExpansion_relMap_graph]
  constructor
  · intro h'
    have hspec := graphValue_spec hAx f h (Fin.init v)
    rw [show graphValue hAx f (Fin.init v) = v (Fin.last n) from h'] at hspec
    rwa [Fin.snoc_init_self] at hspec
  · intro hR
    exact (graphValue_unique hAx f h (Fin.init v) (v (Fin.last n))
      (by rwa [Fin.snoc_init_self])).symm

/-- **The capstone** (consumer-shaped): for formulas whose function support lies in `F`, the
relationalized formula in the ambient graph structure realizes exactly as the original formula
in the reconstruction. The choice outside `F` never enters. -/
theorem realize_relationalize_reconstruct {α : Type}
    (hAx : Sentenceω.Realize (graphAxioms F) M) {n : ℕ} (φ : L.BoundedFormulaω α n)
    (hφ : φ.functionsIn ⊆ F) (v : α → M) (xs : Fin n → M) :
    (relationalizeFormula φ).Realize v xs ↔
      @BoundedFormulaω.Realize L M (reconstructStructure F hAx) α n φ v xs := by
  have hf : ∀ p ∈ (relationalizeFormula φ).functionsIn, ∀ x : Fin p.1 → M,
      @Structure.funMap (graphLanguage L) M ‹_› p.1 p.2 x =
        @Structure.funMap (graphLanguage L) M
          (@graphExpansion L M (reconstructStructure F hAx)) p.1 p.2 x := by
    intro p hp
    rw [functionsIn_relationalizeFormula] at hp
    exact absurd hp (Set.notMem_empty p)
  have hr : ∀ p ∈ (relationalizeFormula φ).relationsIn, ∀ x : Fin p.1 → M,
      (@Structure.RelMap (graphLanguage L) M ‹_› p.1 p.2 x ↔
        @Structure.RelMap (graphLanguage L) M
          (@graphExpansion L M (reconstructStructure F hAx)) p.1 p.2 x) := by
    intro p hp x
    rw [relationsIn_relationalizeFormula] at hp
    rcases hp with ⟨q, _, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Iff.rfl
    · exact (graphExpansion_reconstruct_relMap_graph hAx q.2 (hφ hq) x).symm
  exact (BoundedFormulaω.realize_congr_symbolsIn _ _ (relationalizeFormula φ) hf hr v xs).trans
    (@realize_relationalizeFormula L α M (reconstructStructure F hAx) n φ v xs)

end Reconstruct

/-! ## Localized round-trip: reconstructing a graph expansion -/

section RoundTrip

variable {M : Type} [Nonempty M] [L.Structure M]
variable (F : Set (Σ n, L.Functions n)) [Countable ↥F]



/-- Reconstructing the graph expansion recovers `funMap` on every symbol of `F`. -/
private theorem reconstruct_graphExpansion_funMap {n : ℕ} (f : L.Functions n)
    (h : (⟨n, f⟩ : Σ n, L.Functions n) ∈ F) (v : Fin n → M) :
    letI := graphExpansion L M
    ((reconstructStructure F (graphExpansion_realizes_graphAxioms F M)).funMap f v =
      funMap f v) := by
  let := graphExpansion L M
  refine (graphValue_unique (graphExpansion_realizes_graphAxioms F M) f h v (funMap f v)
    ?_).symm
  rw [graphExpansion_relMap_graph, Fin.init_snoc, Fin.snoc_last]

end RoundTrip

end FirstOrder.Language
