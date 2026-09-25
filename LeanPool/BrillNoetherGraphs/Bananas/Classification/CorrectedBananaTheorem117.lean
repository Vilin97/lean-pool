/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Classification.CorrectedBananaTorsion
public import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionSixBananaCorollary

/-!
# The corrected torsion classification and Theorem 1.17

This module records the two concise public consequences of the completed
high-genus banana analysis.  The first is the corrected form of Proposition
4.19 needed in the proof of Theorem 1.17: the published exceptional family
must allow one marked midpoint strand to have arbitrary even length, provided
the other has length two.  The second is Theorem 1.17 itself.

The stronger dichotomy in `CorrectedBananaTorsion` also proves that the
exceptional branch has exact torsion order two.  The corrected Section 6
assembly then combines the remaining `g ≤ k` branch with the banana
Brill--Noether obstruction.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Corrected Proposition 4.19, in the precise form used by Theorem 1.17.

For a banana of genus at least three, an all-submodular marking of exact
torsion order `k` either belongs to the corrected distinct-strand midpoint
family (with at least one marked strand of length two), or satisfies
`g ≤ k`.  The source theorem proves the stronger conclusion `k = 2` in
the midpoint branch. -/
theorem corrected_banana_torsion_classification
    {g k : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hTO : IsTorsionOrder
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k)
    (hSub : AllSubmodular
      (mark B.graph (strandVertex B α i) (strandVertex B β j))) :
    CorrectedMidpointException B α β i j ∨ g ≤ k := by
  rcases corrected_banana_torsion_dichotomy hg B α β i j hTO hSub with
    hExceptional | hLarge
  · exact Or.inl hExceptional.1
  · exact Or.inr hLarge

/-- Corrected Theorem 1.17 (`thm:bananas`).

A banana graph of genus at least three, marked at any two vertices expressed
in strand coordinates, does not have `k`-general transmission for `k ≥ 3`.
The two coordinates are not assumed distinct: diagonal markings are already
excluded by the stronger corrected classification of general-transmission
markings. -/
theorem corrected_highGenus_banana_not_kGeneral
    {g k : ℕ} (hg : 3 ≤ g) (hk : 3 ≤ k) (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β) :
    ¬ KGeneralTransmission
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k := by
  intro hK
  have hExceptional :=
    (corrected_banana_kGeneral_iff hg B α β i j).mp hK
  omega

end Bananas
