/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Ordinary Lindenbaum extension for the local proof relation.

This is the Zorn step behind the first half of the source's Extension Lemma:
every locally consistent set lies in a maximal locally consistent set.  It does
not claim witnessedness, which is the genuinely fresh-variable-dependent part
of TR Lemma 71.
-/
import LeanPool.MatchingLogic.EntryIII.LocalTheory
import Mathlib.Order.Zorn

/-!
# MatchingLogic.EntryIII.Lindenbaum
-/

namespace MatchingLogic

open Set

variable {S : Signature} {Var : Type} [DecidableEq Var]

omit [DecidableEq Var] in
private theorem chain_covers_list
    {c : Set (Set (Pattern S Var))}
    (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (l : List (Pattern S Var)) (hl : ∀ phi ∈ l, phi ∈ ⋃₀ c) :
    ∃ Delta ∈ c, ∀ phi ∈ l, phi ∈ Delta := by
  induction l with
  | nil =>
      rcases hne with ⟨Delta, hDelta⟩
      exact ⟨Delta, hDelta, by simp⟩
  | cons phi l ih =>
      obtain ⟨D, hDc, hphiD⟩ := Set.mem_sUnion.mp (hl phi (by simp))
      obtain ⟨E, hEc, hE⟩ := ih (by
        intro psi hpsi
        exact hl psi (by simp [hpsi]))
      rcases hc.total hDc hEc with hDE | hED
      · refine ⟨E, hEc, ?_⟩
        intro psi hpsi
        rcases List.mem_cons.mp hpsi with rfl | hpsi
        · exact hDE hphiD
        · exact hE psi hpsi
      · refine ⟨D, hDc, ?_⟩
        intro psi hpsi
        rcases List.mem_cons.mp hpsi with rfl | hpsi
        · exact hphiD
        · exact hED (hE psi hpsi)

private theorem chain_sUnion_locConsistent
    {Gamma : Set (Pattern S Var)} {c : Set (Set (Pattern S Var))}
    (hcandidates : ∀ Delta ∈ c, Gamma ⊆ Delta ∧ LocConsistent Delta)
    (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    LocConsistent (⋃₀ c) := by
  intro hbot
  rcases hbot with ⟨l, hl, hp⟩
  obtain ⟨Delta, hDelta, hcover⟩ := chain_covers_list hchain hne l hl
  exact (hcandidates Delta hDelta).2 ⟨l, hcover, hp⟩

/-- Every locally consistent pattern set is included in a maximal locally
consistent set.  This is the non-witnessed Zorn part of the source's
Lindenbaum construction. -/
theorem locConsistent_extend_isMCS {Gamma : Set (Pattern S Var)}
    (hGamma : LocConsistent Gamma) :
    ∃ Delta : Set (Pattern S Var), Gamma ⊆ Delta ∧ IsMCS Delta := by
  let candidates : Set (Set (Pattern S Var)) :=
    { Delta | Gamma ⊆ Delta ∧ LocConsistent Delta }
  obtain ⟨Delta, hGammaDelta, hmax⟩ := zorn_subset_nonempty candidates (by
    intro c hc hchain hne
    refine ⟨⋃₀ c, ?_, fun D hD => Set.subset_sUnion_of_mem hD⟩
    constructor
    · rcases hne with ⟨D, hDc⟩
      exact (hc hDc).1.trans (Set.subset_sUnion_of_mem hDc)
    · exact chain_sUnion_locConsistent hc hchain hne) Gamma ⟨Set.Subset.rfl, hGamma⟩
  refine ⟨Delta, hGammaDelta, hmax.1.2, ?_⟩
  intro Theta hstrict hTheta
  have hcandidate : Theta ∈ candidates := ⟨hmax.1.1.trans hstrict.1, hTheta⟩
  exact hstrict.2 (hmax.2 hcandidate hstrict.1)

end MatchingLogic
