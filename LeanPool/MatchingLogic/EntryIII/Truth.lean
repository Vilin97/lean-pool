/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
The conditional canonical Truth Lemma (source Lemma 81).

The n-ary Existence Lemma is isolated as an explicit proposition.  The proof
is otherwise complete and proceeds by strong induction on the name-insensitive
pattern complexity, which is essential because total capture-avoiding
substitution preserves that complexity without being a structural subterm.
-/
import LeanPool.MatchingLogic.EntryIII.Completion
import LeanPool.MatchingLogic.EntryIII.CanonicalExistence
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# MatchingLogic.EntryIII.Truth
-/

namespace MatchingLogic

open Set
open scoped BigOperators

variable {S : Signature}

noncomputable section

/-- Local decidable equality used by the truth lemma. -/
local instance instDecidableEqPatternNatTruth : DecidableEq (Pattern S Nat) :=
  Classical.decEq _

private theorem completed_truth_at_complexity
    (hExist : CanonicalExistenceProperty S) (root : CanonicalCarrier S) :
    ∀ n : Nat, ∀ p : Pattern S Nat, p.complexity = n →
      ∀ world : GeneratedCarrier root,
        p ∈ world.val.val ↔
          completedEmbed root world ∈
            (completedModel root).denote (completedValuation root) p := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p hcomplexity world
      cases p with
      | var x =>
          simpa [denote_var, eq_comm] using
            (completedValuation_eq_embed_iff root x world).symm
      | bot =>
          simp [denote_bot, GeneratedCarrier.isMCS world |>.bot_not_mem]
      | imp p q =>
          have hpLt : p.complexity < n := by
            rw [← hcomplexity]
            simp only [Pattern.complexity]
            omega
          have hqLt : q.complexity < n := by
            rw [← hcomplexity]
            simp only [Pattern.complexity]
            omega
          have hp := ih p.complexity hpLt p rfl world
          have hq := ih q.complexity hqLt q rfl world
          have hbool := (GeneratedCarrier.isMCS world).imp_mem_iff p q
          rw [denote_imp]
          simp only [Set.mem_union, Set.mem_compl_iff]
          exact hbool.trans (or_congr (not_congr hp) hq)
      | app sigma args =>
          have hargLe : ∀ i : Fin (S.arity sigma),
              (args i).complexity ≤ ∑ j, (args j).complexity := by
            intro i
            exact Finset.single_le_sum
              (f := fun j : Fin (S.arity sigma) => (args j).complexity)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          have hargLt : ∀ i : Fin (S.arity sigma),
              (args i).complexity < n := by
            intro i
            have hle := hargLe i
            rw [← hcomplexity]
            simp only [Pattern.complexity]
            omega
          constructor
          · intro happ
            obtain ⟨components, hargs, hinterp⟩ :=
              hExist world.val sigma args happ
            have hgenerated : ∀ i, Generated root (components i) := by
              intro i
              exact world.property.tail
                ((canonicalStep_iff world.val (components i)).mpr
                  ⟨sigma, components, i, hinterp, rfl⟩)
            let generatedComponents : Fin (S.arity sigma) → GeneratedCarrier root :=
              fun i => ⟨components i, hgenerated i⟩
            have hdenArgs : ∀ i,
                completedEmbed root (generatedComponents i) ∈
                  (completedModel root).denote (completedValuation root) (args i) := by
              intro i
              exact (ih (args i).complexity (hargLt i) (args i) rfl
                (generatedComponents i)).mp (hargs i)
            have hgeneratedInterp : world ∈
                generatedInterp root sigma generatedComponents := by
              change world.val ∈ canonicalInterp sigma
                (fun i => (generatedComponents i).val)
              simpa [generatedComponents] using hinterp
            rw [denote_app]
            refine ⟨fun i => completedEmbed root (generatedComponents i), hdenArgs, ?_⟩
            exact (completedEmbed_mem_completedInterp_iff
              root generatedComponents world).mpr hgeneratedInterp
          · intro hden
            rw [denote_app] at hden
            rcases hden with ⟨inputs, hdenArgs, hout⟩
            change completedEmbed root world ∈
              completedInterp root sigma inputs at hout
            rcases hout with ⟨components, hinputs, hreal | hstar⟩
            · rcases hreal with ⟨output, houtput, hinterp⟩
              have hworld : world = output :=
                completedEmbed_injective root houtput
              subst output
              apply (mem_generatedInterp.mp hinterp) args
              intro i
              apply (ih (args i).complexity (hargLt i) (args i) rfl
                (components i)).mpr
              rw [← hinputs i]
              exact hdenArgs i
            · have himpossible : (completedEmbed root world).val = none := hstar.1
              simp [completedEmbed] at himpossible
      | ex x p =>
          have hpLt : p.complexity < n := by
            rw [← hcomplexity]
            simp [Pattern.complexity]
          constructor
          · intro hex
            obtain ⟨y, himp⟩ := (GeneratedCarrier.witnessed world) hex
            let q := Pattern.captureAvoidingSubst x y p
            have hqComplexity : q.complexity < n := by
              rw [Pattern.complexity_captureAvoidingSubst]
              exact hpLt
            have hq : q ∈ world.val.val :=
              (GeneratedCarrier.isMCS world).mp_mem hex himp
            have hqDenote :=
              (ih q.complexity hqComplexity q rfl world).mp hq
            have hupdated : completedEmbed root world ∈
                (completedModel root).denote
                  (Function.update (completedValuation root) x
                    (completedValuation root y)) p := by
              rw [← Model.denote_captureAvoidingSubst]
              exact hqDenote
            rw [denote_ex]
            exact Set.mem_iUnion.mpr ⟨completedValuation root y, hupdated⟩
          · intro hden
            rw [denote_ex] at hden
            rcases Set.mem_iUnion.mp hden with ⟨point, hpoint⟩
            obtain ⟨z, rfl⟩ := completedValuation_surjective root point
            let q := Pattern.captureAvoidingSubst x z p
            have hqComplexity : q.complexity < n := by
              rw [Pattern.complexity_captureAvoidingSubst]
              exact hpLt
            have hqDenote : completedEmbed root world ∈
                (completedModel root).denote (completedValuation root) q := by
              rw [Model.denote_captureAvoidingSubst]
              exact hpoint
            have hq : q ∈ world.val.val :=
              (ih q.complexity hqComplexity q rfl world).mpr hqDenote
            exact (GeneratedCarrier.isMCS world).mem_of_provable_imp hq
              (Provable.captureAvoidingExQuant x z p)

/-- Source Lemma 81, conditional only on the separately isolated canonical
Existence Lemma. -/
theorem completed_truth (hExist : CanonicalExistenceProperty S)
    (root : CanonicalCarrier S) (world : GeneratedCarrier root)
    (p : Pattern S Nat) :
    p ∈ world.val.val ↔
      completedEmbed root world ∈
        (completedModel root).denote (completedValuation root) p :=
  completed_truth_at_complexity hExist root p.complexity p rfl world

end

end MatchingLogic
