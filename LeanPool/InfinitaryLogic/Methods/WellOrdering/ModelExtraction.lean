/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.WOConsistency
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.QuotientTruthLemma
/-!
# Model extraction from the completed well-ordering set (issue #12, step 5)

The completion endpoint hands step 5 a Henkin-complete `S` containing the base diagram
`Bφ = {φ̂} ∪ {d_q < d_r : q < r}` opaquely; the quotient term model of the forward truth
lemma then realizes every member of `S`, hence every member of `Bφ`.

This file is the **relational/countable** extraction: `[L.IsRelational]` is consumed by the
quotient term model (the relational-core collapse of closed terms to constants), and
`[Countable (Σ l, L.Relations l)]` by the fair enumeration.  Removing both restrictions is
the later transport step, not done here.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} (φ : L.Sentenceω) (lt : L.Relations 2)

/-- **Model extraction** (relational/countable form): under the well-ordered-chains
hypothesis, some nonempty `L[[ℕ]]`-structure realizes every member of the base diagram —
the lifted root and the full positive rational diagram.  Composition of the completion
endpoint with the forward-truth-lemma model existence theorem; the Henkin-complete set is
consumed opaquely. -/
private theorem exists_model_baseDiagram [L.IsRelational] [Countable (Σ l, L.Relations l)]
    (h : HasWellOrderedChains φ lt) :
    ∃ (M : Type) (_ : L[[ℕ]].Structure M) (_ : Nonempty M),
      ∀ χ ∈ baseDiagram φ lt, Sentenceω.Realize χ M := by
  obtain ⟨S, hsub, hcomp⟩ := exists_henkinComplete_baseDiagram φ lt h
  obtain ⟨M, instM, hne, hpos, -⟩ := exists_model_of_henkinComplete hcomp
  exact ⟨M, instM, hne, fun χ hχ => hpos χ (hsub hχ)⟩

/-! ## The rational map through the interpreted constants -/

/-- **The rational map** of an `L[[ℕ]]`-structure: `q ↦ d_q^M`, the interpretation of the
rational constant.  Step 5's `f : ℚ → M`. -/
private def ratConstMap (M : Type) [L[[ℕ]].Structure M] (q : ℚ) : M :=
  (ratConstTerm (L := L) q).realize (Empty.elim : Empty → M)

/-- The sentence-context constant term realizes to the interpretation of the closed
constant, under any (vacuous) assignment. -/
private theorem realize_constTermS_eq_constTerm {M : Type} [L[[ℕ]].Structure M] (c : ℕ)
    (v : Empty ⊕ Fin 0 → M) :
    Term.realize v (constTermS (L := L) c) =
      Term.realize (Empty.elim : Empty → M) (constTerm (L' := L) (J := ℕ) c) := by
  simp only [constTermS, constTerm]
  -- `congr 1` now also splits the variable-type index, leaving `(Empty ⊕ Fin 0) = Empty`.
  exact congrArg _ (funext fun i => i.elim0)

/-- A positive diagram atom realizes as the expansion relation at the mapped rationals. -/
private theorem realize_ratLtAtom {M : Type} [inst : L[[ℕ]].Structure M] (q r : ℚ) :
    Sentenceω.Realize (ratLtAtom lt q r) M ↔
      @RelMap L[[ℕ]] M inst 2 (Sum.inl lt)
        ![ratConstMap (L := L) M q, ratConstMap (L := L) M r] := by
  have hfun : (fun i => Term.realize (Sum.elim (Empty.elim : Empty → M) (Fin.elim0 : Fin 0 → M))
        (constTermS (L := L) (![ratConstIdx q, ratConstIdx r] i)))
      = ![ratConstMap (L := L) M q, ratConstMap (L := L) M r] := by
    funext i
    rw [realize_constTermS_eq_constTerm]
    induction i using Fin.cases <;>
      simp [ratConstMap, ratConstTerm, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one]
  show @RelMap L[[ℕ]] M inst 2 (Sum.inl lt)
      (fun i => Term.realize (Sum.elim (Empty.elim : Empty → M) (Fin.elim0 : Fin 0 → M))
        (constTermS (![ratConstIdx q, ratConstIdx r] i))) ↔ _
  rw [hfun]

/-! ## The step-5 endpoint (relational/countable form) -/

/-- **Step 5 endpoint, relational/countable form** (Marker, Theorem 4.26 at a relational
language with countable relational core): under the well-ordered-chains hypothesis, some
nonempty model of `φ` carries a relation-preserving map `f : ℚ → M` — the rational map of
the extracted expansion, through its reduct `L`-structure.  The raw positive conclusion
(D2): no injectivity, no order-embedding packaging; those are derived corollaries tracked
for subsequent commits, and the arbitrary-language form is the later transport step. -/
theorem exists_model_relPreserving_relational [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (h : HasWellOrderedChains φ lt) :
    ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M) (f : ℚ → M),
      Sentenceω.Realize φ M ∧ RelPreserving lt f := by
  obtain ⟨M, instM, hne, hall⟩ := exists_model_baseDiagram φ lt h
  let instL : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  have : (L.lhomWithConstants ℕ).IsExpansionOn M := LHom.isExpansionOn_reduct _ _
  refine ⟨M, instL, hne, ratConstMap (L := L) M, ?_, fun q r hqr => ?_⟩
  · exact (BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) φ
      (Empty.elim : Empty → M) Fin.elim0).mp (hall _ (mapLanguage_mem_baseDiagram φ lt))
  · exact (realize_ratLtAtom lt q r).mp (hall _ (ratLtAtom_mem_baseDiagram φ lt hqr))

end FirstOrder.Language
