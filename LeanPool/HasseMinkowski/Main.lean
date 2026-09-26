/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.RankFour
public import LeanPool.HasseMinkowski.RankTwo
public import LeanPool.HasseMinkowski.Legendre
public import LeanPool.HasseMinkowski.HighRank

/-!
# Assembly of the Hasse–Minkowski principle over `ℚ` (WP6)

This file assembles the local–global principle for quadratic forms over `ℚ` from the
rank-by-rank inputs proved in the earlier layers:

* `isotropic_of_rank_one` / `isotropic_of_rank_two` (`RankTwo.lean`),
* `isotropic_of_rank_three'` (`Legendre.lean`),
* `rankFourDiagonalHM` (`RankFour.lean`, the diagonal rank-four case),
* `RankFiveLeDiagonalHM` (`HighRank.lean`, diagonal rank `≥ 5`).

The two diagonal ingredients `RankFourDiagonalHM` (`RankFour.lean`) and
`RankFiveLeDiagonalHM` (the WP5.3 induction, `HighRank.lean`) enter as explicit hypotheses
of the conditional `hasseMinkowski_of` and `meyer_of`; the unconditional `hasseMinkowski`
and `meyer` below specialise them with `rankFourDiagonalHM` and
`rankFiveLeDiagonalHM rankFourDiagonalHM`.

## Main results

* `isotropic_of_radical_ne_bot` (WP6.1): a form with nonzero radical is isotropic, because
  a radical vector `x` has `associated Q x x = 0` and `associated Q x x = 2 * Q x`.
* `hasseMinkowski_of` (WP6.2): `Isotropic Q ↔ EverywhereLocallyIsotropic Q`.
* `meyer_of` (WP6.3): an indefinite form of rank `≥ 5` over `ℚ` is isotropic.
-/

public section

open Module QuadraticMap

namespace HasseMinkowski

/-! ### WP6.1 — a degenerate form is isotropic

In characteristic different from `2` a nonzero vector of the radical satisfies
`Q x = 0` (it is orthogonal to itself, and `associated Q x x = 2 * Q x`).  This is the
"degenerate `Q`" case of the Hasse–Minkowski principle. -/

-- Theorem (WP6.1): a quadratic form with nonzero radical is isotropic.
theorem isotropic_of_radical_ne_bot {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    (h : Q.radical ≠ ⊥) : Isotropic Q := by
  obtain ⟨x, hxmem, hxne⟩ := (Submodule.ne_bot_iff Q.radical).mp h
  exact ⟨x, hxne, (QuadraticMap.mem_radical_iff'.mp hxmem).1⟩

/-! ### WP6.2 — the rank-by-rank dispatch on the diagonalized form

A nondegenerate form is equivalent to a weighted sum of squares `⟨w₀, …, w_{n-1}⟩` with
nonzero rational weights.  The local hypotheses of `h4` and `h5` are exactly the isotropy of
this diagonal form at every place, so we dispatch on `n = finrank ℚ V`: ranks `0`, `1`, `2`,
`3` are the proved layer results, rank `4` is `h4`, and rank `≥ 5` is `h5`. -/

section DiagonalDispatch

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

-- Theorem: diagonal Hasse–Minkowski for an arbitrary rank, conditional on the rank-4 and
-- rank-`≥ 5` diagonal statements.  The local hypotheses `hp`, `hR` are the raw `p`-adic and
-- real isotropy of the diagonal form.
private theorem isotropic_wss_of (h4 : RankFourDiagonalHM) (h5 : RankFiveLeDiagonalHM)
    {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, w i ≠ 0)
    (hp : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (weightedSumSquares ℚ_[p] (fun i => (w i : ℚ_[p]))).Isotropic)
    (hR : (weightedSumSquares ℝ (fun i => (w i : ℝ))).Isotropic) :
    (weightedSumSquares ℚ w).Isotropic := by
  have hW' : EverywhereLocallyIsotropic (weightedSumSquares ℚ w) := by
    constructor
    · intro p hpinst
      have heq := baseChange_weightedSumSquares (R := ℚ) (A := ℚ_[p]) (w := w)
      have hfun : (fun i => algebraMap ℚ ℚ_[p] (w i)) = (fun i => (w i : ℚ_[p])) := by
        funext i
        simp
      rw [hfun] at heq
      exact (heq.isotropic_iff).mpr (hp p)
    · have heq := baseChange_weightedSumSquares (R := ℚ) (A := ℝ) (w := w)
      have hfun : (fun i => algebraMap ℚ ℝ (w i)) = (fun i => (w i : ℝ)) := by
        funext i
        simp
      rw [hfun] at heq
      exact (heq.isotropic_iff).mpr hR
  rcases n with _ | _ | _ | _ | _ | m
  · exact absurd hR (not_isotropic_of_rank_zero
      (weightedSumSquares ℝ (fun i => (w i : ℝ))) (by rw [Module.finrank_fin_fun]))
  · exact isotropic_of_rank_one (weightedSumSquares ℚ w)
      (Module.finrank_fin_fun (R := ℚ)) hW'
  · exact isotropic_of_rank_two (weightedSumSquares ℚ w)
      (Module.finrank_fin_fun (R := ℚ)) (nondegenerate_wss_of_ne hw) hW'
  · exact isotropic_of_rank_three' (weightedSumSquares ℚ w)
      (Module.finrank_fin_fun (R := ℚ)) (nondegenerate_wss_of_ne hw) hW'
  · exact h4 w hw hp hR
  · exact h5 (by omega) w hw hp hR

-- Theorem (WP6.2): Hasse–Minkowski for a general quadratic form over `ℚ`, conditional on the
-- rank-4 and rank-`≥ 5` diagonal statements.
theorem hasseMinkowski_of (h4 : RankFourDiagonalHM) (h5 : RankFiveLeDiagonalHM)
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (Q : QuadraticForm ℚ V) : Isotropic Q ↔ EverywhereLocallyIsotropic Q := by
  refine ⟨isotropic_everywhereLocallyIsotropic, fun hQ' => ?_⟩
  by_cases hrad : Q.radical = ⊥
  · have hQ : Q.Nondegenerate := (QuadraticMap.nondegenerate_iff_radical_eq_bot).mpr hrad
    have hsep : (QuadraticMap.associated (R := ℚ) Q).SeparatingLeft :=
      (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
    obtain ⟨w₀, hw₀⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hsep
    let wq : Fin (finrank ℚ V) → ℚ := fun i => (w₀ i : ℚ)
    have hw' : Q.Equivalent (weightedSumSquares ℚ wq) := hw₀
    have hwq : ∀ i, wq i ≠ 0 := fun i => by simp [wq]
    obtain ⟨hQ'f, hQ'R⟩ := hQ'
    have hp (p : ℕ) [Fact (Nat.Prime p)] :
        (weightedSumSquares ℚ_[p] (fun i => (wq i : ℚ_[p]))).Isotropic := by
      have heq : (Q.baseChange ℚ_[p]).Equivalent
          (weightedSumSquares ℚ_[p] (fun i => algebraMap ℚ ℚ_[p] (wq i))) :=
        (hw'.baseChange (A := ℚ_[p])).trans
          (baseChange_weightedSumSquares (R := ℚ) (A := ℚ_[p]) (w := wq))
      have hfun : (fun i => algebraMap ℚ ℚ_[p] (wq i)) =
          (fun i => (wq i : ℚ_[p])) := by
        funext i
        simp
      rw [hfun] at heq
      exact (heq.isotropic_iff).mp (hQ'f p)
    have hR : (weightedSumSquares ℝ (fun i => (wq i : ℝ))).Isotropic := by
      have heq : (Q.baseChange ℝ).Equivalent
          (weightedSumSquares ℝ (fun i => algebraMap ℚ ℝ (wq i))) :=
        (hw'.baseChange (A := ℝ)).trans
          (baseChange_weightedSumSquares (R := ℚ) (A := ℝ) (w := wq))
      have hfun : (fun i => algebraMap ℚ ℝ (wq i)) = (fun i => (wq i : ℝ)) := by
        funext i
        simp
      rw [hfun] at heq
      exact (heq.isotropic_iff).mp hQ'R
    have hWiso : Isotropic (weightedSumSquares ℚ wq) :=
      isotropic_wss_of h4 h5 wq hwq hp hR
    exact (hw'.isotropic_iff).mpr hWiso
  · exact isotropic_of_radical_ne_bot Q hrad

end DiagonalDispatch

/-! ### WP6.3 — Meyer's theorem

An indefinite real form of rank `≥ 5` is isotropic over `ℝ`; over each `ℚ_[p]` every form in
at least five variables is isotropic (`isotropic_weightedSumSquares_of_five_le`), and these
local data feed WP6.2. -/

-- Theorem (WP6.3): an indefinite form over `ℚ` in at least five variables is isotropic.
theorem meyer_of (h4 : RankFourDiagonalHM) (h5 : RankFiveLeDiagonalHM)
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (Q : QuadraticForm ℚ V) (hrank : 5 ≤ finrank ℚ V)
    (hind : Indefinite (QuadraticForm.baseChange ℝ Q)) : Isotropic Q := by
  by_cases hrad : Q.radical = ⊥
  · have hQ : Q.Nondegenerate := (QuadraticMap.nondegenerate_iff_radical_eq_bot).mpr hrad
    have hsep : (QuadraticMap.associated (R := ℚ) Q).SeparatingLeft :=
      (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
    obtain ⟨w₀, hw₀⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hsep
    let wq : Fin (finrank ℚ V) → ℚ := fun i => (w₀ i : ℚ)
    have hw' : Q.Equivalent (weightedSumSquares ℚ wq) := hw₀
    have hwq : ∀ i, wq i ≠ 0 := fun i => by simp [wq]
    have hlocf (p : ℕ) [Fact (Nat.Prime p)] :
        (weightedSumSquares ℚ_[p] (fun i => (wq i : ℚ_[p]))).Isotropic := by
      have hcard : 5 ≤ Fintype.card (Fin (finrank ℚ V)) := by
        rw [Fintype.card_fin]
        exact hrank
      exact isotropic_weightedSumSquares_of_five_le p
        (fun i => Rat.cast_ne_zero.mpr (hwq i)) hcard
    have hQ' : EverywhereLocallyIsotropic Q := by
      constructor
      · intro p hpinst
        have heq : (Q.baseChange ℚ_[p]).Equivalent
            (weightedSumSquares ℚ_[p] (fun i => (wq i : ℚ_[p]))) := by
          have h := baseChange_weightedSumSquares (R := ℚ) (A := ℚ_[p]) (w := wq)
          have hfun : (fun i => algebraMap ℚ ℚ_[p] (wq i)) =
              (fun i => (wq i : ℚ_[p])) := by
            funext i
            simp
          rw [hfun] at h
          exact (hw'.baseChange (A := ℚ_[p])).trans h
        exact (heq.isotropic_iff).mpr (hlocf p)
      · exact hind.isotropic
    exact (hasseMinkowski_of h4 h5 Q).mpr hQ'
  · exact isotropic_of_radical_ne_bot Q hrad

/-! ### The unconditional theorems

With `RankFourDiagonalHM` proved in `RankFour.lean` and its rank-`≥ 5` counterpart in
`HighRank.lean`, the conditional theorems above specialise to the targets: -/

-- Theorem: Hasse–Minkowski over `ℚ` (isotropy form).
theorem hasseMinkowski {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (Q : QuadraticForm ℚ V) : Isotropic Q ↔ EverywhereLocallyIsotropic Q :=
  hasseMinkowski_of rankFourDiagonalHM (rankFiveLeDiagonalHM rankFourDiagonalHM) Q

-- Theorem (Meyer): an indefinite form over `ℚ` in at least five variables is isotropic.
theorem meyer {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (Q : QuadraticForm ℚ V) (h : 5 ≤ finrank ℚ V)
    (hind : Indefinite (QuadraticForm.baseChange ℝ Q)) : Isotropic Q :=
  meyer_of rankFourDiagonalHM (rankFiveLeDiagonalHM rankFourDiagonalHM) Q h hind

end HasseMinkowski
