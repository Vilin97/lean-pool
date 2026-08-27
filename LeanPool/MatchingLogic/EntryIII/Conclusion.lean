/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
The final source-scoped composition for entry point (iii).

The canonical construction is used only on the finite sub-signature generated
by a finite countertheory.  This avoids a countability assumption on the
ambient symbol type.  The result over `Nat` is then transported to every
countably infinite element-variable type.
-/
import LeanPool.MatchingLogic.EntryIII.CanonicalConstruction
import LeanPool.MatchingLogic.EntryIII.ModelExistence
import LeanPool.MatchingLogic.EntryIII.SignatureReduction
import LeanPool.MatchingLogic.EntryIII.Renaming
import LeanPool.MatchingLogic.EntryPoints

/-!
# MatchingLogic.EntryIII.Conclusion
-/

namespace MatchingLogic

variable {S : Signature}

/-- Every locally consistent finite list over an arbitrary ambient signature
has a pointed model.  Only its finite symbol restriction enters the canonical
construction. -/
theorem finiteLocalModelExistence : FiniteLocalModelExistence S Nat := by
  classical
  apply finiteLocalModelExistence_of_restricted
  intro F
  have : Countable (Pattern (S.restrict F) Nat) :=
    restrictedPatternNatCountable F
  exact finiteLocalModelExistence_of_canonicalExistence canonicalExistence

/-- Unconditional finite-list local completeness over the source variable
type `Nat`. -/
theorem finiteLocalCompleteness : FiniteLocalCompleteness S Nat :=
  finiteLocalCompleteness_of_finiteLocalModelExistence finiteLocalModelExistence

/-- Unconditional strong local completeness over `Nat`. -/
theorem strongLocalCompleteness_nat : StrongLocalCompleteness S Nat :=
  strongLocalCompleteness_of_finiteLocalCompleteness finiteLocalCompleteness

/-- Entry point (iii), at the source-faithful scope of a countably infinite
element-variable type. -/
theorem strongLocalCompleteness {Var : Type}
    [DecidableEq Var] [Denumerable Var] :
    StrongLocalCompleteness S Var :=
  (strongLocalCompleteness_iff_nat (S := S) (Var := Var)).mpr
    strongLocalCompleteness_nat

/-- Corollary 15 with both soundness and strong local completeness supplied by
the development.  Only the paper's closedness premises remain. -/
theorem global_completeness_entryIII {Var : Type}
    [DecidableEq Var] [Denumerable Var]
    {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (hGamma : ∀ gamma ∈ Gamma, Closed gamma) (hphi : Closed phi) :
    GlobalCons Gamma phi ↔ Provable Gamma phi :=
  global_completeness_of_localCompleteness strongLocalCompleteness hGamma hphi

end MatchingLogic
