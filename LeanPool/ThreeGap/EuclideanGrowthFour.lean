/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/
import LeanPool.ThreeGap.FiveDistanceHM

/-!
# The sharp Euclidean growth inequality `2 qₙ ≤ qₙ₊₄` (`K = 4`) via Haynes–Marklof Theorem 8

This sharpens `euclidean_growth_five` (`2 qₙ ≤ qₙ₊₅`, the planar packing count) to the sharp
`2 qₙ ≤ qₙ₊₄`, the input to the sharp Euclidean five-distance theorem `g₂ ≤ 5`. The five-vector
configuration `r(qₙ), …, r(qₙ₊₄)` is admissible for the bare packing count (5 vectors pairwise `>
π/3`
*do* fit), so the extra structure of Haynes–Marklof Theorem 8 (`FiveDistance.hm_theorem8`) is used:
the
shortest record `r(qₙ₊₄)` cannot lie in the open cone of two others, because that would force
`‖r(qₙ₊₄) − vⱼ − vₖ‖ < ‖vₖ‖` (`FiveDistanceHM.cone_exclusion`) while the best-approximation property
(`hbest`, the index difference lies in `(0, qₖ)`) forces `‖r(qₙ₊₄) − vⱼ − vₖ‖ > ‖vₖ‖`. Axiom-clean.
-/

namespace ThreeGap.SimApprox

open scoped Real
open ThreeGap.EuclideanPacking

variable {n : ℕ}

/-- **The sharp Euclidean growth inequality, `K = 4` (Haynes–Marklof Theorem 8).** For a
best-`L²`-approximation sequence `(q, p)` of `α : Fin 2 → ℝ` with the record/monotonicity
hypotheses,
the denominators at least double every **four** steps: `2 qₙ ≤ qₙ₊₄`. -/
theorem euclidean_growth_four (α : Fin 2 → ℝ) (q : ℕ → ℤ) (p : ℕ → Fin 2 → ℤ)
    (hmono : StrictMono q)
    (hattain : ∀ k, euclNorm 2 (rem α (q k) (p k)) ≤ deltaN (euclNorm 2) α (q k))
    (hdec : ∀ i j, i ≤ j → deltaN (euclNorm 2) α (q j) ≤ deltaN (euclNorm 2) α (q i))
    (hdecstrict : ∀ k, deltaN (euclNorm 2) α (q (k + 1)) < deltaN (euclNorm 2) α (q k))
    (hbest : ∀ (k : ℕ) (m : ℤ), 0 < m → m < q k →
      deltaN (euclNorm 2) α (q k) < deltaN (euclNorm 2) α m)
    (hpos : ∀ k, 0 < deltaN (euclNorm 2) α (q k))
    (N : ℕ) : 2 * q N ≤ q (N + 4) := by
  by_contra hcon
  rw [not_le] at hcon
  have hnorm_eq : ∀ k, euclNorm 2 (rem α (q k) (p k)) = deltaN (euclNorm 2) α (q k) := fun k =>
    le_antisymm (hattain k) (deltaN_le (euclNorm 2) euclNorm_nonneg α (q k) (p k))
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨finrank_euclideanSpace_fin⟩
  -- the five remainder vectors, in natural denominator order: w 0 longest (= δ_N), w 4 shortest
  set w : Fin 5 → EuclideanSpace ℝ (Fin 2) :=
    fun i => (EuclideanSpace.equiv (Fin 2) ℝ).symm (rem α (q (N + i.val)) (p (N + i.val))) with hw
  have hnorm_w : ∀ i : Fin 5, ‖w i‖ = deltaN (euclNorm 2) α (q (N + i.val)) := by
    intro i; simp only [hw]; exact hnorm_eq _
  have hwne : ∀ i : Fin 5, w i ≠ 0 := by
    intro i hi
    have h0 : ‖w i‖ = 0 := by rw [hi, norm_zero]
    rw [hnorm_w i] at h0; linarith [hpos (N + i.val)]
  have hlb : ∀ i : Fin 5, q N ≤ q (N + i.val) := fun i => hmono.monotone (by omega)
  have hub : ∀ i : Fin 5, q (N + i.val) < 2 * q N := by
    intro i
    exact lt_of_le_of_lt (hmono.monotone (show N + i.val ≤ N + 4 by omega)) hcon
  -- defects strictly decrease along the index: `i < j → ‖w j‖ < ‖w i‖`
  have hnorm_lt : ∀ i j : Fin 5, i < j → ‖w j‖ < ‖w i‖ := by
    intro i j hij
    rw [hnorm_w, hnorm_w]
    have hjv : i.val + 1 ≤ j.val := hij
    calc deltaN (euclNorm 2) α (q (N + j.val))
        ≤ deltaN (euclNorm 2) α (q (N + (i.val + 1))) := hdec _ _ (by omega)
      _ < deltaN (euclNorm 2) α (q (N + i.val)) := by
          rw [show N + (i.val + 1) = (N + i.val) + 1 by ring]; exact hdecstrict _
  -- pairwise angle `> π/3` (the metric→angle crux), identical to the K=5 argument
  have hwsep : ∀ i j : Fin 5, i ≠ j → π / 3 < InnerProductGeometry.angle (w i) (w j) := by
    intro i j hij
    have hwi : 0 < ‖w i‖ := by rw [hnorm_w]; exact hpos _
    have hwj : 0 < ‖w j‖ := by rw [hnorm_w]; exact hpos _
    have hui : ‖w i‖ ≤ deltaN (euclNorm 2) α (q N) := by
      rw [hnorm_w]; exact hdec N (N + i.val) (by omega)
    have huj : ‖w j‖ ≤ deltaN (euclNorm 2) α (q N) := by
      rw [hnorm_w]; exact hdec N (N + j.val) (by omega)
    have hsep : deltaN (euclNorm 2) α (q N) ≤ ‖w i - w j‖ := by
      have hwij : ‖w i - w j‖
          = euclNorm 2 (rem α (q (N + i.val) - q (N + j.val)) (p (N + i.val) - p (N + j.val))) := by
        simp only [hw]; rw [← map_sub, rem_sub]; rfl
      rw [hwij]
      set m : ℤ := q (N + i.val) - q (N + j.val) with hm
      have hmne : m ≠ 0 := by
        rw [hm, sub_ne_zero]; exact fun h => hij (by
          have := hmono.injective h; exact Fin.ext (by omega))
      have habs_pos : 0 < |m| := abs_pos.mpr hmne
      have habs_lt : |m| < q N := by
        rw [hm, abs_sub_lt_iff]
        constructor <;> [linarith [hub i, hlb j]; linarith [hub j, hlb i]]
      have hdN_abs : deltaN (euclNorm 2) α (q N) < deltaN (euclNorm 2) α |m| :=
        hbest N |m| habs_pos habs_lt
      have hsym : deltaN (euclNorm 2) α |m| = deltaN (euclNorm 2) α m := by
        rcases abs_choice m with h | h
        · rw [h]
        · rw [h, deltaN_neg (euclNorm 2) euclNorm_nonneg euclNorm_neg]
      have hle : deltaN (euclNorm 2) α m
          ≤ euclNorm 2 (rem α m (p (N + i.val) - p (N + j.val))) :=
        deltaN_le (euclNorm 2) euclNorm_nonneg α m _
      rw [hsym] at hdN_abs; linarith [hdN_abs, hle]
    have hstrict : ‖w i‖ < deltaN (euclNorm 2) α (q N) ∨ ‖w j‖ < deltaN (euclNorm 2) α (q N) := by
      rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
      · right
        rw [hnorm_w]
        have hj1 : 1 ≤ j.val := by
          rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
          · exact absurd (Fin.ext (by omega) : i = j) hij
          · exact hjpos
        exact lt_of_le_of_lt (hdec (N + 1) (N + j.val) (by omega)) (hdecstrict N)
      · left
        rw [hnorm_w]
        exact lt_of_le_of_lt (hdec (N + 1) (N + i.val) (by omega)) (hdecstrict N)
    exact EuclideanAngle.angle_gt_pi_div_three hwi hwj hui huj hsep hstrict
  -- the (5.3) record bound: `‖w 4 − w a − w b‖ > ‖w a‖` for `a, b ≠ 4`
  have h53 : ∀ a b : Fin 5, a ≠ 4 → b ≠ 4 → a ≠ b → ‖w a‖ < ‖w 4 - w a - w b‖ := by
    intro a b ha hb hab
    have hav : a.val < 4 := by have : a.val ≠ 4 := fun h => ha (Fin.ext h); omega
    have hbv : b.val < 4 := by have : b.val ≠ 4 := fun h => hb (Fin.ext h); omega
    have hwabc : ‖w 4 - w a - w b‖
        = euclNorm 2 (rem α (q (N + 4) - q (N + a.val) - q (N + b.val))
            (p (N + 4) - p (N + a.val) - p (N + b.val))) := by
      simp only [hw, ← map_sub]; rw [rem_sub, rem_sub]; rfl
    rw [hwabc, hnorm_w a]
    set m : ℤ := q (N + 4) - q (N + a.val) - q (N + b.val) with hm
    have hqa : q N ≤ q (N + a.val) := hlb a
    have hqb : q N ≤ q (N + b.val) := hlb b
    have hqb4 : q (N + b.val) < q (N + 4) := hmono (by omega)
    have hmneg : m < 0 := by rw [hm]; linarith
    have hmpos : 0 < |m| := by rw [abs_of_neg hmneg, hm]; linarith
    have hmlt : |m| < q (N + a.val) := by rw [abs_of_neg hmneg, hm]; linarith
    have hda := hbest (N + a.val) |m| hmpos hmlt
    have hsym : deltaN (euclNorm 2) α |m| = deltaN (euclNorm 2) α m := by
      rcases abs_choice m with h | h
      · rw [h]
      · rw [h, deltaN_neg (euclNorm 2) euclNorm_nonneg euclNorm_neg]
    have hle : deltaN (euclNorm 2) α m
        ≤ euclNorm 2 (rem α m (p (N + 4) - p (N + a.val) - p (N + b.val))) :=
      deltaN_le (euclNorm 2) euclNorm_nonneg α m _
    rw [hsym] at hda; linarith
  -- the cone property for the shortest vector `w 4`
  have hconeW : ∀ a b : Fin 5, a ≠ 4 → b ≠ 4 → a ≠ b →
      ¬ ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ w 4 = s • w a + t • w b := by
    intro a b ha hb hab ⟨s, t, hs, ht, heq⟩
    have ha4 : a < (4 : Fin 5) := by
      have : a.val ≠ 4 := fun h => ha (Fin.ext h); omega
    have hb4 : b < (4 : Fin 5) := by
      have : b.val ≠ 4 := fun h => hb (Fin.ext h); omega
    have hla : ‖w 4‖ < ‖w a‖ := hnorm_lt a 4 ha4
    have hlb' : ‖w 4‖ < ‖w b‖ := hnorm_lt b 4 hb4
    have hβa : π / 3 < InnerProductGeometry.angle (w 4) (w a) := hwsep 4 a (Ne.symm ha)
    have hβb : π / 3 < InnerProductGeometry.angle (w 4) (w b) := hwsep 4 b (Ne.symm hb)
    have hcomm : w 4 - w b - w a = w 4 - w a - w b := by abel
    have hnorm_ne : ‖w a‖ ≠ ‖w b‖ := by
      rcases lt_trichotomy a b with h | h | h
      · exact ne_of_gt (hnorm_lt a b h)
      · exact absurd h hab
      · exact ne_of_lt (hnorm_lt b a h)
    rcases lt_or_gt_of_ne hnorm_ne with hnab | hnab
    · -- ‖w a‖ < ‖w b‖: cone edges (w a, w b)
      have hexcl := FiveDistanceHM.cone_exclusion (hwne a) (hwne b) (hwne 4)
        hs.le ht.le heq hla hnab hβa hβb
      have h := h53 b a hb ha (Ne.symm hab)
      rw [hcomm] at h
      linarith
    · -- ‖w b‖ < ‖w a‖: cone edges (w b, w a)
      have heq' : w 4 = t • w b + s • w a := by rw [heq]; abel
      have hexcl := FiveDistanceHM.cone_exclusion (hwne b) (hwne a) (hwne 4)
        ht.le hs.le heq' hlb' hnab hβb hβa
      rw [hcomm] at hexcl
      linarith [h53 a b ha hb hab]
  -- apply Haynes–Marklof Theorem 8 to the reindexed tuple `v i = w (rev i)` (so `v 0 = w 4`)
  refine FiveDistance.hm_theorem8 (v := fun i => w i.rev) (fun i => hwne _) ?_ ?_
  · intro i j hij
    exact hwsep _ _ (fun h => hij (Fin.rev_injective h))
  · intro j k hj hk hjk
    have hj4 : j.rev ≠ 4 := by
      intro h; rw [Fin.rev_eq_iff, show (4 : Fin 5).rev = 0 by decide] at h
      exact absurd h (ne_of_gt hj)
    have hk4 : k.rev ≠ 4 := by
      intro h; rw [Fin.rev_eq_iff, show (4 : Fin 5).rev = 0 by decide] at h
      exact absurd h (ne_of_gt hk)
    exact hconeW j.rev k.rev hj4 hk4 (fun h => hjk (Fin.rev_injective h))

end ThreeGap.SimApprox
