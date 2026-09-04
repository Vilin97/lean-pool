/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Scott.Height.Defs
/-!
# Canonical Scott Sentence

The canonical Scott sentence of a structure M is the Scott formula at Scott
height level for the empty tuple. It is the "optimal" Scott sentence whose
quantifier rank is minimized among Scott formulas.

## Main Definitions

- `canonicalScottSentence`: The Scott formula at Scott height for the empty tuple.

## Main Results

- `canonicalScottSentence_iff_potentialIso`: Characterizes potential isomorphism.
- `canonicalScottSentence_characterizes`: For countable structures, characterizes isomorphism.
- `canonicalScottSentence_equiv_scottSentence`: Semantically equivalent to the standard Scott sentence.
- `canonicalScottSentence_qrank`: Quantifier rank bounded by scottHeight + ω.
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal

/-- The canonical Scott sentence of a structure M, defined as the Scott formula at Scott
height level for the empty tuple.

This is the "optimal" Scott sentence in the sense that its quantifier rank is minimized
(among Scott formulas). It characterizes the structure up to potential isomorphism,
and for countable structures, up to isomorphism. -/
noncomputable def canonicalScottSentence (M : Type w) [L.Structure M] [Countable M] :
    L.Formulaω (Fin 0) :=
  scottFormula (L := L) (M := M) Fin.elim0 (scottHeight (L := L) M)

/-- The canonical Scott sentence realizes in N iff BFEquiv at scottHeight. -/
private theorem canonicalScottSentence_iff_BFEquiv0
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w'} [L.Structure N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    BFEquiv (L := L) (scottHeight (L := L) M) 0
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  unfold canonicalScottSentence Formulaω.realize_as_sentence
  exact realize_scottFormula_iff_BFEquiv _ _ _ (scottHeight_lt_omega1_of hcount M)

/-- Conditional variant of `canonicalScottSentence_iff_potentialIso`. -/
theorem canonicalScottSentence_iff_potentialIso_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    Nonempty (PotentialIso L M N) := by
  constructor
  · intro h
    rw [canonicalScottSentence_iff_BFEquiv0 hcount] at h
    have hstab := scottHeight_stabilizesCompletely_of hcount M
    exact ⟨{
      family := { p | BFEquiv (L := L) (scottHeight (L := L) M) p.1 p.2.1 p.2.2 }
      empty_mem := h
      compatible := fun p hp =>
        (BFEquiv.zero p.2.1 p.2.2).mp (BFEquiv.monotone bot_le hp)
      forth := fun ⟨k, a, b⟩ hp m => by
        simp only [Set.mem_ofPred_eq] at hp ⊢
        exact BFEquiv.forth ((hstab k N a b).mp hp) m
      back := fun ⟨k, a, b⟩ hp n' => by
        simp only [Set.mem_ofPred_eq] at hp ⊢
        exact BFEquiv.back ((hstab k N a b).mp hp) n'
    }⟩
  · intro ⟨P⟩
    rw [canonicalScottSentence_iff_BFEquiv0 hcount]
    exact P.implies_BFEquiv_all (scottHeight (L := L) M)

/-- Conditional variant of `canonicalScottSentence_characterizes`. -/
theorem canonicalScottSentence_characterizes_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    Nonempty (M ≃[L] N) := by
  rw [canonicalScottSentence_iff_BFEquiv0 hcount]
  constructor
  · exact BFEquiv_stabilization_implies_equiv (scottHeight_stabilizesCompletely_of hcount M)
  · intro ⟨e⟩
    rw [← comp_fin_elim0 e]
    exact equiv_implies_BFEquiv e _ 0 Fin.elim0

/-- Conditional variant of `canonicalScottSentence_equiv_scottSentence`. -/
theorem canonicalScottSentence_equiv_scottSentence_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    (scottSentence (L := L) M).realize_as_sentence N := by
  rw [canonicalScottSentence_characterizes_of hcount, scottSentence_characterizes_of hcount]

/-- Conditional variant of `canonicalScottSentence_qrank`. -/
theorem canonicalScottSentence_qrank_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    (canonicalScottSentence (L := L) M).qrank ≤
    scottHeight (L := L) M + Ordinal.omega0 :=
  le_trans
    (scottFormula_qrank_le Fin.elim0 _ (scottHeight_lt_omega1_of hcount M))
    le_self_add

/-- The canonical Scott sentence characterizes potential isomorphism. -/
theorem canonicalScottSentence_iff_potentialIso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    Nonempty (PotentialIso L M N) :=
  canonicalScottSentence_iff_potentialIso_of countableRefinementHypothesis

/-- For countable structures, the canonical Scott sentence characterizes isomorphism. -/
theorem canonicalScottSentence_characterizes
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    Nonempty (M ≃[L] N) :=
  canonicalScottSentence_characterizes_of countableRefinementHypothesis

/-- The canonical Scott sentence is semantically equivalent to the standard Scott sentence. -/
theorem canonicalScottSentence_equiv_scottSentence
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    (scottSentence (L := L) M).realize_as_sentence N :=
  canonicalScottSentence_equiv_scottSentence_of countableRefinementHypothesis

/-- The quantifier rank of the canonical Scott sentence is bounded. -/
theorem canonicalScottSentence_qrank
    (M : Type w) [L.Structure M] [Countable M] :
    (canonicalScottSentence (L := L) M).qrank ≤
    scottHeight (L := L) M + Ordinal.omega0 :=
  canonicalScottSentence_qrank_of countableRefinementHypothesis M

end Language

end FirstOrder
