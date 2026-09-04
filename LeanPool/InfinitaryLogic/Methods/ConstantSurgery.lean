/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.QuantifierRoundTrip
import LeanPool.InfinitaryLogic.Methods.Interpolation.BaseOccurrenceProjections
import LeanPool.InfinitaryLogic.Lomega1omega.QuantifierOccurrence
/-!
# Constant surgery: substituting one constant for another

The neutral constant-surgery layer.  `substConst b a ρ` replaces the constant `c_b` by `c_a`
throughout `ρ`, built from the existing abstraction/instantiation pair, together with its
realization, symbol, constant-support and quantifier-occurrence laws.

Nothing here is specific to interpolation: this is the reusable operation tracked by issue #39
(neutral `L_ω₁ω` syntax-analysis and constant-surgery API), extracted early because the cross-label
equality/relation transfer of the Malitz arc is its first consumer.  The decisive law is
`hasQuantSigned_substConst`: substitution moves **no** quantifier occurrence, which is what lets a
consumer replace a constant in a separator without spending a quantifier permission.

The `instConst` dependency is why this file currently sits under `Methods` beside the interpolation
machinery rather than in the syntax layer; #39's consolidation is where that is resolved.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}} {M : Type}

/-! ## Constant-for-constant substitution

The machinery the **cross-label** equality/relation transfers need, and the reason they are the
riskiest gate: when the relation atom and the equality atom sit on *different* labels, the derived
atom is entailed by neither side alone, and the separator of the extended pair may legitimately
mention a constant that only the *other* side carries.  Feferman's condition (iii) then forces that
constant out of the separator — and the operation that does it is substitution of the shared
partner,
not quantification.

`substConst b a ρ` replaces the constant `c_b` by `c_a` throughout `ρ`, built from the existing
abstraction/instantiation pair. -/

/-- Replace the constant `c_b` by `c_a`: abstract `b` into the free variable, then instantiate at
`a`. -/
noncomputable def substConst (b a : ℕ) (ρ : L[[ℕ]].Sentenceω) : L[[ℕ]].Sentenceω :=
  instConst a ((ρ.abstractConst b).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1))

/-- Realizing the substitution is realizing the original with `b` reinterpreted at `a`'s value. -/
theorem realize_substConst (base : L.Structure M) (h : ℕ → M) (b a : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 (substConst b a ρ) Empty.elim Fin.elim0
      ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h b (h a))) Empty 0 ρ
          Empty.elim Fin.elim0 := by
  let : L[[ℕ]].Structure M := wc base h
  rw [substConst, realize_instConst base h a _,
    BoundedFormulaω.realize_relabel_sumInr_zero (ρ.abstractConst b) (fun _ : Fin 1 => h a)]
  exact BoundedFormulaω.realize_abstractConst base h b (h a) ρ Fin.elim0

theorem baseFunctionsIn_substConst_subset (b a : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (substConst b a ρ).baseFunctionsIn ⊆ ρ.baseFunctionsIn := by
  refine (baseFunctionsIn_instConst_subset a _).trans ?_
  intro s hs
  simp only [BoundedFormulaω.baseFunctionsIn, Set.mem_ofPred_eq] at hs ⊢
  rw [show (BoundedFormulaω.all ((ρ.abstractConst b).relabel
      (Sum.inr : Fin 1 → Empty ⊕ Fin 1))).functionsIn
    = ((ρ.abstractConst b).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).functionsIn from rfl,
    BoundedFormulaω.functionsIn_relabel] at hs
  exact BoundedFormulaω.functionsIn_abstractConst_subset b ρ hs

theorem baseRelationsIn_substConst (b a : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (substConst b a ρ).baseRelationsIn ⊆ ρ.baseRelationsIn := by
  refine (baseRelationsIn_instConst_subset a _).trans ?_
  intro s hs
  simp only [BoundedFormulaω.baseRelationsIn, Set.mem_ofPred_eq] at hs ⊢
  rw [show (BoundedFormulaω.all ((ρ.abstractConst b).relabel
      (Sum.inr : Fin 1 → Empty ⊕ Fin 1))).relationsIn
    = ((ρ.abstractConst b).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).relationsIn from rfl,
    BoundedFormulaω.relationsIn_relabel, BoundedFormulaω.relationsIn_abstractConst] at hs
  exact hs

theorem sentenceJConsts_substConst_subset (b a : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    sentenceJConsts (L' := L) (J := ℕ) (substConst b a ρ)
      ⊆ sentenceJConsts (L' := L) (J := ℕ) ρ ∪ {a} := by
  refine (sentenceJConsts_instConst_subset a _).trans ?_
  refine Set.union_subset_union_left _ ?_
  intro k hk
  unfold sentenceJConsts at hk ⊢
  rw [show (BoundedFormulaω.all ((ρ.abstractConst b).relabel
      (Sum.inr : Fin 1 → Empty ⊕ Fin 1))).functionsIn
    = ((ρ.abstractConst b).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).functionsIn from rfl,
    BoundedFormulaω.functionsIn_relabel] at hk
  exact BoundedFormulaω.functionsIn_abstractConst_subset b ρ hk

/-- The substituted constant is gone, provided it was not the substitute. -/
theorem notMem_sentenceJConsts_substConst (b a : ℕ) (hne : b ≠ a) (ρ : L[[ℕ]].Sentenceω) :
    b ∉ sentenceJConsts (L' := L) (J := ℕ) (substConst b a ρ) := by
  intro hk
  rcases sentenceJConsts_instConst_subset a _ hk with hk | hk
  · unfold sentenceJConsts at hk
    rw [show (BoundedFormulaω.all ((ρ.abstractConst b).relabel
        (Sum.inr : Fin 1 → Empty ⊕ Fin 1))).functionsIn
      = ((ρ.abstractConst b).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).functionsIn from rfl,
      BoundedFormulaω.functionsIn_relabel] at hk
    exact BoundedFormulaω.notMem_sentenceJConsts_abstractConst b ρ hk
  · exact hne (Set.mem_singleton_iff.mp hk)

/-- Constant abstraction does not move the signed quantifier occurrences. -/
private theorem hasQuantSigned_abstractConst (j : ℕ) (s : Bool) :
    ∀ {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n),
      hasQuantSigned s (BoundedFormulaω.abstractConst j φ) ↔ hasQuantSigned s φ := by
  intro n φ
  induction φ generalizing s with
  | falsum => exact Iff.rfl
  | equal t u => exact Iff.rfl
  | rel R ts => exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    -- induction-bound receivers carry the inductive type, so they need the qualified name
    change hasQuantSigned (!s) (BoundedFormulaω.abstractConst j φ) ∨
        hasQuantSigned s (BoundedFormulaω.abstractConst j ψ) ↔ _
    exact or_congr (ihφ (!s)) (ihψ s)
  | all φ ih =>
    change s = true ∨ hasQuantSigned s (BoundedFormulaω.abstractConst j φ) ↔ _
    exact or_congr_right (ih s)
  | iSup φs ih =>
    change (∃ i, hasQuantSigned s (BoundedFormulaω.abstractConst j (φs i))) ↔ _
    exact exists_congr fun i => ih i s
  | iInf φs ih =>
    change (∃ i, hasQuantSigned s (BoundedFormulaω.abstractConst j (φs i))) ↔ _
    exact exists_congr fun i => ih i s

/-- Substitution does not move the signed quantifier occurrences: the budgets are untouched. -/
theorem hasQuantSigned_substConst (b a : ℕ) (s : Bool) (ρ : L[[ℕ]].Sentenceω) :
    hasQuantSigned s (substConst b a ρ) ↔ hasQuantSigned s ρ := by
  rw [substConst, instConst,
    show ∀ ψ : L[[ℕ]].BoundedFormulaω Empty 1,
      hasQuantSigned s ((ψ.openBounds).subst (fun _ => constTerm a))
        ↔ hasQuantSigned s ψ from fun ψ => by
      rw [hasQuantSigned_subst, hasQuantSigned_openBounds],
    hasQuantSigned_relabel, hasQuantSigned_abstractConst]

end FirstOrder.Language
