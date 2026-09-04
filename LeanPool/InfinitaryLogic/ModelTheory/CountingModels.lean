/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Theory
import LeanPool.InfinitaryLogic.Scott.Height
import LeanPool.InfinitaryLogic.Scott.RefinementCount
/-!
# Counting Models

This file states model-counting results for Lω₁ω, connecting Scott rank bounds
to the structure of the isomorphism relation.

## Main Results

- `bounded_scottHeight_iso_eq_BFEquiv`: When all models of a sentence have Scott height
  bounded by α, isomorphism equals BF-equivalence at level α.
- `morley_counting_dichotomy`: Placeholder for the full Morley counting theorem.
  The conditional bounded-height version is in `Descriptive/CountingDichotomy.lean`
  as `counting_coded_models_dichotomy`.

## References

- [Mar16]
- [KK04]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Cardinal Ordinal

omit [Countable (Σ l, L.Relations l)] in
/-- When a structure has `StabilizesCompletely M α` (with α < ω₁) and BFEquiv α holds,
the structures are isomorphic. Unconditional (no `CountableRefinementHypothesis` needed).

This decouples the isomorphism conclusion from scottRank entirely, taking
`StabilizesCompletely` as a direct hypothesis. -/
theorem stabilization_bound_iso_eq_BFEquiv
    {M N : Type w} [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    {α : Ordinal.{0}} (_hα : α < Ordinal.omega 1)
    (hstab : StabilizesCompletely (L := L) M α)
    (hBF : BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  have hAll : ∀ γ < (Ordinal.omega 1 : Ordinal.{0}),
      BFEquiv (L := L) γ 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
    intro γ _
    rcases le_or_gt γ α with hγα | hαγ
    · exact BFEquiv.monotone hγα hBF
    · exact BFEquiv_upgrade_at_stabilization hstab hBF γ hαγ.le
  exact BFEquiv_below_omega1_implies_iso hAll

/-- When all countable models of a sentence have Scott height bounded by α (with α < ω₁),
isomorphism between countable models is equivalent to BF-equivalence at level α.
Conditional on `CountableRefinementHypothesis`.

This uses `scottHeight` (which has a clean conditional relationship to
`StabilizesCompletely`) rather than `scottRank`. -/
private theorem bounded_scottHeight_iso_eq_BFEquiv_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {φ : L.Sentenceω} {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type w) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottHeight (L := L) M ≤ α)
    {M N : Type w} [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    (hM : Sentenceω.Realize φ M) (_hN : Sentenceω.Realize φ N) :
    Nonempty (M ≃[L] N) ↔
    BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  constructor
  · intro ⟨e⟩
    rw [← comp_fin_elim0 e]
    exact equiv_implies_BFEquiv e α 0 Fin.elim0
  · intro hBF
    have hstabM := scottHeight_le_implies_stabilizesCompletely_of hcount M (hbound M hM)
    exact stabilization_bound_iso_eq_BFEquiv hα hstabM hBF

/-! ### Unconditional Wrapper (via CRH) -/

/-- When all countable models of a sentence have Scott height bounded by α (with α < ω₁),
isomorphism between countable models is equivalent to BF-equivalence at level α. -/
theorem bounded_scottHeight_iso_eq_BFEquiv
    {φ : L.Sentenceω} {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type w) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottHeight (L := L) M ≤ α)
    {M N : Type w} [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    (hM : Sentenceω.Realize φ M) (hN : Sentenceω.Realize φ N) :
    Nonempty (M ≃[L] N) ↔
    BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
  bounded_scottHeight_iso_eq_BFEquiv_of countableRefinementHypothesis hα hbound hM hN

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Placeholder for the full Morley counting theorem (the number of isomorphism
classes of countable models of an Lω₁ω sentence is either at most ℵ₁ or exactly 2^ℵ₀).

The conditional version is proved as `FirstOrder.Language.morley_counting`
(in `ModelTheory/MorleyCounting.lean`). -/
private theorem morley_counting_dichotomy
    (_φ : L.Sentenceω) :
    True := by  -- Schematic: see docstring for the actual mathematical content
  trivial

end Language

end FirstOrder
