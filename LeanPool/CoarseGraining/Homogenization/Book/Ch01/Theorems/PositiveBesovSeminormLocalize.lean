/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.PositiveBesovLocalize

/-! # Positive Besov Seminorm Localize -/

namespace Homogenization
namespace Book
namespace Ch01

noncomputable section

open scoped BigOperators ENNReal

/-!
# Legacy positive Besov seminorm localization

This file keeps the seminorm-only companions for the legacy disjoint,
finite-truncation/real-`sSup` compatibility lane.  These are not statements
about the manuscript's exact overlapping `ENNReal` definitions.
-/

namespace Legacy

theorem positiveBesovPartialSeminormTwo_le_seminormTwo_of_bddAbove {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialSeminormTwo Q s N u)) (N : ℕ) :
    positiveBesovPartialSeminormTwo Q s N u ≤
      positiveBesovSeminormTwo Q s u := by
  change positiveBesovPartialSeminormTwo Q s N u ≤
    sSup (Set.range fun N : ℕ => positiveBesovPartialSeminormTwo Q s N u)
  exact le_csSup hBdd ⟨N, rfl⟩

theorem positiveBesovSeminormTwo_nonneg_of_bddAbove {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialSeminormTwo Q s N u)) :
    0 ≤ positiveBesovSeminormTwo Q s u := by
  exact (positiveBesovPartialSeminormTwo_nonneg Q s 0 u).trans
    (positiveBesovPartialSeminormTwo_le_seminormTwo_of_bddAbove Q s u hBdd 0)

theorem positiveBesovPartialSeminormTwo_bddAbove_of_parent_bddAbove {d : ℕ}
    {Q R : Cube d} {j : ℕ} (s : ℝ) (u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hParentBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialSeminormTwo Q s N u)) :
    BddAbove (Set.range fun N : ℕ =>
      positiveBesovPartialSeminormTwo R s N u) := by
  classical
  rcases hParentBdd with ⟨B, hB⟩
  have hB_nonneg : 0 ≤ B := by
    have hB0 : positiveBesovPartialSeminormTwo Q s 0 u ≤ B :=
      hB ⟨0, rfl⟩
    exact (positiveBesovPartialSeminormTwo_nonneg Q s 0 u).trans hB0
  let D : Finset (Cube d) := descendantsAtDepth Q j
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  have hcard_pos : 0 < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD_nonempty
  have hcard_nonneg : 0 ≤ (D.card : ℝ) := le_of_lt hcard_pos
  refine ⟨Real.sqrt ((D.card : ℝ) * B ^ 2), ?_⟩
  rintro x ⟨N, rfl⟩
  have hparent_le :
      positiveBesovPartialSeminormTwo Q s (j + N) u ≤ B :=
    hB ⟨j + N, rfl⟩
  have hparent_nonneg :
      0 ≤ positiveBesovPartialSeminormTwo Q s (j + N) u :=
    positiveBesovPartialSeminormTwo_nonneg Q s (j + N) u
  have hparent_sq_le :
      (positiveBesovPartialSeminormTwo Q s (j + N) u) ^ 2 ≤ B ^ 2 := by
    nlinarith
  let F : Cube d → ℝ := fun S =>
    (positiveBesovPartialSeminormTwo S s N u) ^ 2
  have havg_le_parent :
      descendantsAverage Q j F ≤
        (positiveBesovPartialSeminormTwo Q s (j + N) u) ^ 2 := by
    dsimp [F]
    exact descendantsAverage_sq_positiveBesovPartialSeminormTwo_le Q s u j N
  have havg_le_Bsq : descendantsAverage Q j F ≤ B ^ 2 :=
    havg_le_parent.trans hparent_sq_le
  have hsum_le : (∑ S ∈ D, F S) ≤ (D.card : ℝ) * B ^ 2 := by
    have hmul :
        (D.card : ℝ) * descendantsAverage Q j F ≤ (D.card : ℝ) * B ^ 2 :=
      mul_le_mul_of_nonneg_left havg_le_Bsq hcard_nonneg
    have hdesc : (D.card : ℝ) * descendantsAverage Q j F = ∑ S ∈ D, F S := by
      dsimp [descendantsAverage, D]
      field_simp [ne_of_gt hcard_pos]
    rwa [hdesc] at hmul
  have hterm_le_sum : F R ≤ ∑ S ∈ D, F S := by
    exact Finset.single_le_sum
      (fun S _hS => sq_nonneg (positiveBesovPartialSeminormTwo S s N u))
      (by simpa [D] using hR)
  have hterm_sq_le :
      (positiveBesovPartialSeminormTwo R s N u) ^ 2 ≤
        (D.card : ℝ) * B ^ 2 :=
    hterm_le_sum.trans hsum_le
  exact Real.le_sqrt_of_sq_le hterm_sq_le

theorem tendsto_positiveBesovPartialSeminormTwo_atTop {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialSeminormTwo Q s N u)) :
    Filter.Tendsto
      (fun N : ℕ => positiveBesovPartialSeminormTwo Q s N u)
      Filter.atTop
      (nhds (positiveBesovSeminormTwo Q s u)) := by
  change Filter.Tendsto
    (fun N : ℕ => positiveBesovPartialSeminormTwo Q s N u)
    Filter.atTop
    (nhds (sSup (Set.range fun N : ℕ =>
      positiveBesovPartialSeminormTwo Q s N u)))
  exact
    tendsto_atTop_ciSup
      (monotone_nat_of_le_succ
        (fun N => positiveBesovPartialSeminormTwo_le_succ Q s u N))
      hBdd

theorem tendsto_sq_positiveBesovPartialSeminormTwo_atTop {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialSeminormTwo Q s N u)) :
    Filter.Tendsto
      (fun N : ℕ => (positiveBesovPartialSeminormTwo Q s N u) ^ 2)
      Filter.atTop
      (nhds ((positiveBesovSeminormTwo Q s u) ^ 2)) := by
  exact (tendsto_positiveBesovPartialSeminormTwo_atTop Q s u hBdd).pow 2

theorem tendsto_descendantsAverage_sq_positiveBesovPartialSeminormTwo_atTop {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j : ℕ)
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          positiveBesovPartialSeminormTwo R s N u)) :
    Filter.Tendsto
      (fun N : ℕ =>
        descendantsAverage Q j
          (fun R => (positiveBesovPartialSeminormTwo R s N u) ^ 2))
      Filter.atTop
      (nhds
        (descendantsAverage Q j
          (fun R => (positiveBesovSeminormTwo R s u) ^ 2))) := by
  unfold descendantsAverage
  exact
    Filter.Tendsto.const_mul ((descendantsAtDepth Q j).card : ℝ)⁻¹
      (tendsto_finsetSum (descendantsAtDepth Q j)
        (fun R hR =>
          tendsto_sq_positiveBesovPartialSeminormTwo_atTop
            R s u (hLocalBdd R hR)))

/-- In the legacy real-`sSup` lane, infinite-depth scalar `q = 2` positive
Besov seminorms localize over descendants, provided the parent and local
`sSup`s are bounded above. -/
theorem descendantsAverage_sq_positiveBesovSeminormTwo_le {d : ℕ}
    (Q : Cube d) (s : ℝ) (u : Vec d → ℝ) (j : ℕ)
    (hParentBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialSeminormTwo Q s N u))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          positiveBesovPartialSeminormTwo R s N u)) :
    descendantsAverage Q j
        (fun R => (positiveBesovSeminormTwo R s u) ^ 2) ≤
      (positiveBesovSeminormTwo Q s u) ^ 2 := by
  have hparent_nonneg :
      0 ≤ positiveBesovSeminormTwo Q s u :=
    positiveBesovSeminormTwo_nonneg_of_bddAbove Q s u hParentBdd
  have hbound :
      ∀ N : ℕ,
        descendantsAverage Q j
            (fun R => (positiveBesovPartialSeminormTwo R s N u) ^ 2) ≤
          (positiveBesovSeminormTwo Q s u) ^ 2 := by
    intro N
    have hpartial :=
      descendantsAverage_sq_positiveBesovPartialSeminormTwo_le Q s u j N
    have hpartial_le_full :
        positiveBesovPartialSeminormTwo Q s (j + N) u ≤
          positiveBesovSeminormTwo Q s u :=
      positiveBesovPartialSeminormTwo_le_seminormTwo_of_bddAbove
        Q s u hParentBdd (j + N)
    have hpartial_nonneg :
        0 ≤ positiveBesovPartialSeminormTwo Q s (j + N) u :=
      positiveBesovPartialSeminormTwo_nonneg Q s (j + N) u
    have hpartial_sq :
        (positiveBesovPartialSeminormTwo Q s (j + N) u) ^ 2 ≤
          (positiveBesovSeminormTwo Q s u) ^ 2 := by
      nlinarith
    exact hpartial.trans hpartial_sq
  have hlim :=
    tendsto_descendantsAverage_sq_positiveBesovPartialSeminormTwo_atTop
      Q s u j hLocalBdd
  exact le_of_tendsto' hlim hbound

end Legacy

end

end Ch01
end Book
end Homogenization
