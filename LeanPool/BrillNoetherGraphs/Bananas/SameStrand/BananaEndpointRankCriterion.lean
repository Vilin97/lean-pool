/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.Semibreak

/-!
# The endpoint rank-one criterion for banana graphs

The paper proves `lem-BananaRDS` by invoking Luo's characterization of a
rank-determining set: it is enough to show that a divisor has rank at least
one whenever subtracting either member of the proposed set leaves a winnable
divisor.  The imported chip-firing library does not currently define
rank-determining sets or contain Luo's characterization.  This file proves
the complete banana-specific input to that characterization.

The proof uses the already formalized endpoint/semibreak normal form.  The
left endpoint test forces the unrestricted left coefficient to be positive.
If the Riemann--Roch term does not already give rank one, the right endpoint
test forces the bounded right coefficient to be positive as well.
-/

namespace Bananas

open Utilities

open Utilities Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

section Generic

private theorem linearEquiv_sub_same_right {G : CFGraph}
    {D N C : CFDiv G} (h : linearEquiv G D N) :
    linearEquiv G (D - C) (N - C) := by
  unfold linearEquiv at h ⊢
  have hDifference : (N - C) - (D - C) = N - D := by
    abel
  rw [hDifference]
  exact h

private theorem endpointNormalForm_sub_left {G : CFGraph}
    (L R E : CFDiv G) (a b : ℤ) :
    (a • L + b • R + E) - L = (a - 1) • L + b • R + E := by
  module

private theorem endpointNormalForm_sub_right {G : CFGraph}
    (L R E : CFDiv G) (a b : ℤ) :
    (a • L + b • R + E) - R = a • L + (b - 1) • R + E := by
  module

end Generic

private theorem bananaNormalForm_sub_leftEndpoint {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) :
    bananaNormalForm B a b E - oneChip (leftEndpoint B) =
      bananaNormalForm B (a - 1) b E := by
  exact endpointNormalForm_sub_left
    (oneChip (leftEndpoint B)) (oneChip (rightEndpoint B)) E a b

private theorem bananaNormalForm_sub_rightEndpoint {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) :
    bananaNormalForm B a b E - oneChip (rightEndpoint B) =
      bananaNormalForm B a (b - 1) E := by
  exact endpointNormalForm_sub_right
    (oneChip (leftEndpoint B)) (oneChip (rightEndpoint B)) E a b

/-- TeX label: `lem-BananaRDS` (Lemma 2.21), banana-specific rank-one
criterion used with Luo's rank-determining-set characterization.

If subtracting either multivalent endpoint from a divisor leaves nonnegative
rank, then the original divisor has rank at least one.  This is exactly the
graph-specific assertion proved in the paper after the reduction to rank one;
packaging it as the full rank-determining-set statement only requires the
currently absent generic definition and Luo equivalence. -/
theorem banana_rank_one_of_endpoint_residuals {g : ℕ} (B : Banana g)
    (D : CFDiv B.graph)
    (hLeft : 0 ≤ rank B.graph (D - oneChip (leftEndpoint B)))
    (hRight : 0 ≤ rank B.graph (D - oneChip (rightEndpoint B))) :
    1 ≤ rank B.graph D := by
  obtain ⟨a, b, E, hE, hb, hBound, hDN⟩ :=
    exists_linearly_equiv_bananaNormalForm B D
  let N : CFDiv B.graph := bananaNormalForm B a b E
  have hLeftEquiv : linearEquiv B.graph
      (D - oneChip (leftEndpoint B))
      (N - oneChip (leftEndpoint B)) :=
    linearEquiv_sub_same_right hDN
  have hRightEquiv : linearEquiv B.graph
      (D - oneChip (rightEndpoint B))
      (N - oneChip (rightEndpoint B)) :=
    linearEquiv_sub_same_right hDN
  have hLeftN : 0 ≤ rank B.graph
      (bananaNormalForm B (a - 1) b E) := by
    rw [← bananaNormalForm_sub_leftEndpoint]
    rw [← rank_eq_of_linear_equiv B.graph hLeftEquiv]
    exact hLeft
  have ha : 1 ≤ a := by
    by_contra haNot
    have hNeg : rank B.graph (bananaNormalForm B (a - 1) b E) = -1 :=
      (rank_bananaNormalForm_neg_iff B (a - 1) b E hE hb hBound).2
        (by omega)
    rw [hNeg] at hLeftN
    omega
  have hRankN := rank_bananaNormalForm B a b E hE (by omega) hb hBound
  have hRankD : rank B.graph D =
      max (min a b) (a + b + deg E - (g : ℤ)) := by
    rw [rank_eq_of_linear_equiv B.graph hDN]
    exact hRankN
  by_cases hLarge : (g : ℤ) < a + deg E
  · rw [hRankD]
    omega
  · have haBound : a + deg E ≤ (g : ℤ) := by omega
    have hRightN : 0 ≤ rank B.graph
        (bananaNormalForm B a (b - 1) E) := by
      rw [← bananaNormalForm_sub_rightEndpoint]
      rw [← rank_eq_of_linear_equiv B.graph hRightEquiv]
      exact hRight
    have hbOne : 1 ≤ b := by
      by_contra hbNot
      have hbZero : b = 0 := by omega
      have hReduced := q_reduced_bananaNormalForm_right B a (b - 1) E hE
        (by omega) haBound
      have hNeg : rank B.graph (bananaNormalForm B a (b - 1) E) = -1 := by
        apply rank_eq_neg_one_of_qReduced_debt B.graph (rightEndpoint B)
          (bananaNormalForm B a (b - 1) E) hReduced
        rw [bananaNormalForm_rightEndpoint B a (b - 1) E hE]
        omega
      rw [hNeg] at hRightN
      omega
    rw [hRankD]
    omega

end Bananas
