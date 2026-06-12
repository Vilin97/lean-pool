/-
Copyright (c) 2026 György Kurucz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: György Kurucz
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Insert
import Mathlib.Order.SetNotation

import LeanPool.LeanModelChecking.LTLNBWStatement

/-!
# Negation normal form for Linear Temporal Logic

We define negation normal form (NNF) formulas, their language, and a translation
`LTL.toNNF` from `LTL` formulas to equivalent NNF formulas. The main result
`LTL.exists_equiv_nnf` shows every `LTL` formula has an equivalent NNF formula.
-/

namespace LeanModelChecking

/-- Linear temporal logic formulas in negation normal form over atomic
propositions `AP`: negation is pushed to the atoms (`atom`/`not_atom`), and the
temporal operators are `next`, `until`, and the dual `release`. -/
inductive NNF (AP : Type) where
| atom (p : AP)
| not_atom (p : AP)
| and (f g : NNF AP)
| or (f g : NNF AP)
| next (f : NNF AP)
| until (f g : NNF AP)
| release (f g : NNF AP)
deriving DecidableEq

/-- The language of an NNF formula: the predicate on infinite words `w` that holds
exactly when `w` satisfies `f` at position `0`. -/
def NNF.language {AP} (f : NNF AP) (w : Nat → Letter AP) : Prop :=
  match f with
  | .atom p => p ∈ w 0
  | .not_atom p => p ∉ w 0
  | .and f g => NNF.language f w ∧ NNF.language g w
  | .or f g => NNF.language f w ∨ NNF.language g w
  | .next f => NNF.language f (fun j => w (j + 1))
  | .until f g =>
    ∃ i, NNF.language g (fun j => w (j + i)) ∧ ∀ k < i, NNF.language f (fun j => w (j + k))
  | .release f g =>
    ∀ i, NNF.language g (fun j => w (j + i)) ∨ ∃ k < i, NNF.language f (fun j => w (j + k))

-- Code below here mostly written by GPT-5-Codex

lemma not_exists_until_iff_forall {P Q : Nat → Prop} :
    (¬ ∃ i, Q i ∧ ∀ k < i, P k) ↔ ∀ i, ¬ Q i ∨ ∃ k < i, ¬ P k := by
  constructor
  · intro h i
    cases Classical.em (Q i) with
    | inl hQi =>
        refine Or.inr ?_
        have hforall : ¬ ∀ k < i, P k := by
          intro hPi
          exact h ⟨i, hQi, hPi⟩
        obtain ⟨k, hk⟩ := Classical.not_forall.mp hforall
        have hklt : k < i := by
          by_contra hnot
          exact hk (fun hlt => (hnot hlt).elim)
        have hnotPk : ¬ P k := by
          intro hPk
          exact hk (fun _ => hPk)
        exact ⟨k, hklt, hnotPk⟩
    | inr hQi =>
        exact Or.inl hQi
  · intro h
    rintro ⟨i, hQi, hPi⟩
    have hi := h i
    cases hi with
    | inl hneg => exact hneg hQi
    | inr hcounter =>
        rcases hcounter with ⟨k, hk, hk'⟩
        exact hk' (hPi k hk)

namespace LTL

/-- Translate an `LTL` formula to an NNF formula, optionally negated: the Boolean
flag, when `true`, requests the NNF of the negation of the formula, allowing
negation to be pushed down to the atoms recursively. -/
def toNNFCore {AP} : Bool → LTL AP → NNF AP
  | false, .atom p => .atom p
  | true, .atom p => .not_atom p
  | false, .not f => toNNFCore true f
  | true, .not f => toNNFCore false f
  | false, .or f g => .or (toNNFCore false f) (toNNFCore false g)
  | true, .or f g => .and (toNNFCore true f) (toNNFCore true g)
  | false, .next f => .next (toNNFCore false f)
  | true, .next f => .next (toNNFCore true f)
  | false, .until f g => .until (toNNFCore false f) (toNNFCore false g)
  | true, .until f g => .release (toNNFCore true f) (toNNFCore true g)

/-- The NNF formula equivalent to the `LTL` formula `f`. -/
def toNNF {AP} (f : LTL AP) : NNF AP := toNNFCore false f

/-- The NNF formula equivalent to the negation of the `LTL` formula `f`. -/
def toNNFNeg {AP} (f : LTL AP) : NNF AP := toNNFCore true f

lemma toNNFCore_sound {AP} (f : LTL AP) :
    (∀ w, LTL.language f w ↔ NNF.language (toNNF f) w) ∧
      (∀ w, ¬ LTL.language f w ↔ NNF.language (toNNFNeg f) w) := by
  induction f with
  | atom p => simp [toNNF, toNNFNeg, toNNFCore, LTL.language, NNF.language]
  | not f ih =>
    refine ⟨?_, ?_⟩
    · simpa [toNNF, toNNFNeg, toNNFCore, LTL.language] using ih.2
    · simpa [toNNF, toNNFNeg, toNNFCore, LTL.language] using ih.1
  | or f g ihf ihg =>
    refine ⟨?_, ?_⟩
    · simp [toNNF, toNNFCore, LTL.language, NNF.language, ihf.1, ihg.1]
    · simp [toNNFNeg, toNNFCore, LTL.language, NNF.language, ihf.2, ihg.2]
  | next f ih =>
    refine ⟨?_, ?_⟩
    · simp [toNNF, toNNFCore, LTL.language, NNF.language, ih.1]
    · simp [toNNFNeg, toNNFCore, LTL.language, NNF.language, ih.2]
  | «until» f g ihf ihg =>
    refine ⟨?_, ?_⟩
    · intro w
      constructor
      · intro h
        rcases h with ⟨i, hgi, hfi⟩
        refine ⟨i, ?_, ?_⟩
        · exact (ihg.1 _).mp hgi
        · intro k hk
          exact (ihf.1 _).mp (hfi k hk)
      · intro h
        rcases h with ⟨i, hgi, hfi⟩
        refine ⟨i, ?_, ?_⟩
        · exact (ihg.1 _).mpr hgi
        · intro k hk
          exact (ihf.1 _).mpr (hfi k hk)
    · intro w
      have hf : ∀ k,
          ¬ LTL.language f (fun j => w (j + k)) ↔
            NNF.language (toNNFNeg f) (fun j => w (j + k)) := by
        intro k
        simpa using ihf.2 (fun j => w (j + k))
      have hg : ∀ k,
          ¬ LTL.language g (fun j => w (j + k)) ↔
            NNF.language (toNNFNeg g) (fun j => w (j + k)) := by
        intro k
        simpa using ihg.2 (fun j => w (j + k))
      have hlogic :=
        not_exists_until_iff_forall
          (P := fun k => LTL.language f (fun j => w (j + k)))
          (Q := fun i => LTL.language g (fun j => w (j + i)))
      simp [toNNFNeg, toNNFCore, LTL.language, NNF.language, hf, hg, hlogic]

end LTL

-- Theorem statement written by hand
theorem LTL.exists_equiv_nnf {AP} (ψ : LTL AP) :
    ∃ (nnf : NNF AP), ψ.language = nnf.language := by
  refine ⟨LTL.toNNF ψ, funext ?_⟩
  simpa using (toNNFCore_sound ψ).1

end LeanModelChecking
