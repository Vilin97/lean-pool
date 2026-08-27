/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Conditional pointed-model existence and completeness compositions for entry
point (iii).

The only remaining mathematical premise is the separately isolated canonical
Existence Lemma.  All model construction, completion, valuation, and Truth
Lemma steps are discharged below without strengthening that premise.
-/
import LeanPool.MatchingLogic.EntryIII.Truth
import LeanPool.MatchingLogic.EntryIII.Countertheory

/-!
# MatchingLogic.EntryIII.ModelExistence
-/

namespace MatchingLogic

open Set

variable {S : Signature}

noncomputable section

/-- Local decidable equality used by the finite-model construction. -/
local instance instDecidableEqPatternNatModelExistence : DecidableEq (Pattern S Nat) :=
  Classical.decEq _

/-- Conditional finite pointed-model existence, obtained from a fresh-witnessed
MCS root and the completed canonical Truth Lemma. -/
theorem finiteLocalModelExistence_of_canonicalExistence
    [Countable (Pattern S Nat)] (hExist : CanonicalExistenceProperty S) :
    FiniteLocalModelExistence S Nat := by
  intro l hconsistent
  obtain ⟨Delta, hbase, hM, hW⟩ :=
    finite_locConsistent_extend_freshWitnessed_isMCS l hconsistent
  let root : CanonicalCarrier S := ⟨Delta, hM, hW⟩
  let world : GeneratedCarrier root := generatedRoot root
  refine ⟨completedModel root, completedValuation root,
    completedEmbed root world, ?_⟩
  simp only [Model.denoteSet, Set.mem_iInter]
  intro delta hdelta
  apply (completed_truth hExist root world delta).mp
  exact hbase hdelta

/-- Conditional finite-list local completeness. -/
theorem finiteLocalCompleteness_of_canonicalExistence
    [Countable (Pattern S Nat)] (hExist : CanonicalExistenceProperty S) :
    FiniteLocalCompleteness S Nat :=
  finiteLocalCompleteness_of_finiteLocalModelExistence
    (finiteLocalModelExistence_of_canonicalExistence hExist)

/-- Conditional strong local completeness over the source variable type
`Nat`, using semantic compactness after the finite-list result. -/
theorem strongLocalCompleteness_nat_of_canonicalExistence
    [Countable (Pattern S Nat)] (hExist : CanonicalExistenceProperty S) :
    StrongLocalCompleteness S Nat :=
  strongLocalCompleteness_of_finiteLocalCompleteness
    (finiteLocalCompleteness_of_canonicalExistence hExist)

end

end MatchingLogic
