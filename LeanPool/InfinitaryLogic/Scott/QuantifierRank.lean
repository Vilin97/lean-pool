/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Scott.Formula
import LeanPool.InfinitaryLogic.Lomega1omega.QuantifierRank
import LeanPool.InfinitaryLogic.Karp.CarrierTheorem
/-!
# Quantifier Rank of Scott Formulas

This file proves bounds on the quantifier rank of Scott formulas and connects
BF-equivalence to agreement on Lω₁ω formulas of bounded quantifier rank.

## Main Results

- `scottFormula_qrank_le`: The Scott formula at level α has quantifier rank ≤ α.
- `BFEquiv_iff_EquivQRω_formulas`: BF-equivalence at level α between tuples is
  equivalent to agreement on all Lω₁ω formulas of quantifier rank ≤ α (for α < ω₁).

## References

- [Mar16]
- [KK04]
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal BoundedFormulaω

-- Derive Encodable from Countable for use in einf/esup
attribute [local instance] Encodable.ofCountable

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Each atomic formula has qrank 0. -/
private theorem atomicFormulaω_qrank (idx : L.AtomicIdx n) :
    (atomicFormulaω idx).qrank = 0 := by
  cases idx with
  | eq i j => rfl
  | rel R f => rfl

omit [L.IsRelational] in
/-- The atomic diagram has quantifier rank 0. -/
theorem atomicDiagram_qrank_eq_zero {M : Type w} [L.Structure M]
    {n : ℕ} (a : Fin n → M) :
    (atomicDiagram (L := L) a).qrank = 0 := by
  classical
  simp only [atomicDiagram, Formulaω.qrank, qrank_einf]
  apply le_antisymm
  · apply Ordinal.iSup_le; intro idx
    split_ifs with h
    · exact le_of_eq (atomicFormulaω_qrank idx)
    · simp only [qrank_not]; exact le_of_eq (atomicFormulaω_qrank idx)
  · exact bot_le

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- `existsLastVar` adds 1 to quantifier rank. -/
theorem qrank_existsLastVar {n : ℕ} (φ : L.Formulaω (Fin (n + 1))) :
    (existsLastVar φ).qrank = φ.qrank + 1 := by
  simp only [existsLastVar, BoundedFormulaω.qrank_ex, BoundedFormulaω.qrank_relabel]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- `forallLastVar` adds 1 to quantifier rank. -/
theorem qrank_forallLastVar {n : ℕ} (φ : L.Formulaω (Fin (n + 1))) :
    (forallLastVar φ).qrank = φ.qrank + 1 := by
  simp only [forallLastVar, BoundedFormulaω.qrank_all, BoundedFormulaω.qrank_relabel]

omit [L.IsRelational] in
/-- The Scott formula at level α has quantifier rank ≤ α.

This is proved by ordinal induction:
- At level 0: the atomic diagram has rank 0.
- At successor α + 1: the formula at α has rank ≤ α, and the forth/back
  conditions add one quantifier, giving rank ≤ α + 1.
- At limit λ: the conjunction over β < λ has rank ≤ λ. -/
theorem scottFormula_qrank_le {M : Type w} [L.Structure M] [Countable M]
    {n : ℕ} (a : Fin n → M) (α : Ordinal) (hα : α < Ordinal.omega 1) :
    (scottFormula (L := L) a α).qrank ≤ α := by
  induction α using Ordinal.limitRecOn generalizing n a with
  | zero =>
    rw [scottFormula_zero, atomicDiagram_qrank_eq_zero]
  | add_one β ih =>
    rw [← Order.succ_eq_add_one] at hα ⊢
    have hβ : β < Ordinal.omega 1 := lt_of_lt_of_le (Order.lt_succ β) (le_of_lt hα)
    rw [scottFormula_succ]
    -- Goal: ((scottFormula a β ⊓ einf ...) ⊓ forallLastVar ...).qrank ≤ Order.succ β
    -- `⊓` is `Min.min` = `BoundedFormulaω.and`, unfold and use qrank_and
    show (BoundedFormulaω.and _ _).qrank ≤ _
    rw [qrank_and]
    apply max_le
    · -- (scottFormula a β ⊓ einf (fun m => existsLastVar ...)).qrank ≤ succ β
      show (BoundedFormulaω.and _ _).qrank ≤ _
      rw [qrank_and]
      apply max_le
      · -- scottFormula a β has qrank ≤ β ≤ succ β
        exact le_trans (ih a hβ) (Order.le_succ β)
      · -- einf (fun m => existsLastVar (scottFormula (snoc a m) β))
        -- qrank = sup_m (qrank(scottFormula(snoc a m) β) + 1)
        simp only [qrank_einf, qrank_existsLastVar]
        rw [Order.succ_eq_add_one]
        apply Ordinal.iSup_le; intro m
        exact add_le_add_left (ih (Fin.snoc a m) hβ) 1
    · -- forallLastVar (esup (fun m => scottFormula (snoc a m) β))
      -- qrank = qrank(esup ...) + 1 = (sup_m qrank(scottFormula(snoc a m) β)) + 1
      simp only [qrank_forallLastVar, qrank_esup]
      rw [Order.succ_eq_add_one]
      exact add_le_add_left (Ordinal.iSup_le fun m => ih (Fin.snoc a m) hβ) 1
  | limit β hβlimit ih =>
    unfold scottFormula
    rw [Ordinal.limitRecOn_limit _ _ _ _ hβlimit]
    simp only [hα, dite_true]
    simp only [Formulaω.qrank, qrank_einf]
    apply Ordinal.iSup_le; intro ⟨γ, hγ⟩
    exact le_trans (ih γ hγ a (lt_trans hγ hα)) (le_of_lt hγ)

omit [Countable (Σ l, L.Relations l)] in
/-- BF-equivalence at level α implies agreement on Lω₁ω formulas of quantifier rank ≤ α.

This is the carrier-`ℕ` case of the forward direction of the Karp lemma
(`BFEquiv_implies_agreeQR`). There is no embedding step: `L.Formulaω` *is*
`L.BoundedFormulaInf ℕ` and the ω rank *is* the carrier-generic rank, so specializing the
carrier is the whole proof. -/
theorem BFEquiv_implies_agree_formulas_omega {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (α : Ordinal) (_hα : α < Ordinal.omega 1) :
    BFEquiv (L := L) α n a b →
    ∀ (φ : L.Formulaω (Fin n)), φ.qrank ≤ α →
      (Formulaω.Realize φ a ↔ Formulaω.Realize φ b) := by
  intro hBF φ hφ
  exact BFEquiv_implies_agreeQR α a b hBF φ hφ

omit [L.IsRelational] in
/-- Agreement on all Lω₁ω formulas of quantifier rank ≤ α implies BF-equivalence.

This direction uses the Scott formula: if all rank-≤-α formulas agree, then in particular
the Scott formula at level α agrees, which by `realize_scottFormula_iff_BFEquiv` gives
BFEquiv at level α. -/
theorem agree_formulas_omega_implies_BFEquiv {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (α : Ordinal) (hα : α < Ordinal.omega 1) :
    (∀ (φ : L.Formulaω (Fin n)), φ.qrank ≤ α →
      (Formulaω.Realize φ a ↔ Formulaω.Realize φ b)) →
    BFEquiv (L := L) α n a b := by
  intro hAgree
  -- The Scott formula at level α has qrank ≤ α
  have hqr := scottFormula_qrank_le (L := L) a α hα
  -- M satisfies its own Scott formula (by BFEquiv.refl)
  have hRealize : Formulaω.Realize (scottFormula (L := L) a α) a :=
    (realize_scottFormula_iff_BFEquiv a a α hα).mpr (BFEquiv.refl α a)
  -- By hypothesis, b also satisfies the Scott formula
  have hRealize' := (hAgree _ hqr).mp hRealize
  -- By the fundamental correspondence, this gives BFEquiv
  exact (realize_scottFormula_iff_BFEquiv a b α hα).mp hRealize'

/-- BF-equivalence at level α between tuples is equivalent to agreement on all
Lω₁ω formulas of quantifier rank ≤ α (for α < ω₁).

This is the Lω₁ω version of the Karp lemma. -/
theorem BFEquiv_iff_agree_formulas_omega {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (α : Ordinal) (hα : α < Ordinal.omega 1) :
    BFEquiv (L := L) α n a b ↔
    ∀ (φ : L.Formulaω (Fin n)), φ.qrank ≤ α →
      (Formulaω.Realize φ a ↔ Formulaω.Realize φ b) := by
  exact ⟨BFEquiv_implies_agree_formulas_omega a b α hα,
         agree_formulas_omega_implies_BFEquiv a b α hα⟩

end Language

end FirstOrder
