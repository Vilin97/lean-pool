/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Where the mechanization actually stands against the paper's challenge.

`global_completeness` (in `Completeness.lean`) is entry point (ii) verbatim:
Corollary 15 with (L) and (S) assumed. But (S) is not an assumption in this
development -- `soundness` (in `Soundness.lean`) proves it -- so it can be
supplied rather than hypothesised. That is what this file records.
-/
import LeanPool.MatchingLogic.Soundness
import LeanPool.MatchingLogic.Completeness

/-!
# MatchingLogic.EntryPoints
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-- **Corollary 15 with (S) discharged.**

Entry point (ii) of the paper's challenge is Corollary 15 *with (L) and (S)
assumed*, which is `global_completeness` above. But (S) is not an assumption
here — `soundness` proves it — so it can be supplied rather than hypothesised,
leaving (L) as the only remaining black box.

This is entry point (ii) in full, plus (S) discharged -- which (ii) permitted
us to assume, so it is beyond (ii) rather than part of (iii). Entry point (iii)
asks for (L) to be discharged as well; that is done in `MatchingLogic/EntryIII/`
(see `strongLocalCompleteness` and `global_completeness_entryIII` in
`EntryIII/Conclusion.lean`), via Theorem 73, Lemmas 80--81, and strong local
completeness Theorem 83 of Chen and Roșu, *Matching μ-Logic*, 2019 technical
report (https://hdl.handle.net/2142/102281), the paper's reference [5].
The theorem below deliberately keeps
(L) as a hypothesis: it holds at an *arbitrary* element-variable type, whereas
the (iii) discharge is at the paper's scope `[Denumerable Var]`. -/
theorem global_completeness_of_localCompleteness
    (hL : StrongLocalCompleteness S Var)
    {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) :
    GlobalCons Γ φ ↔ Provable Γ φ :=
  global_completeness hL soundness hΓ hφ

end MatchingLogic
