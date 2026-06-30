/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import LeanPool.ThreeGap.ChevallierCount
import LeanPool.ThreeGap.SupNormGrowth

/-!
# The sup-norm defect cost: growth of its record denominators is *unconditional*

This file instantiates the abstract Chevallier machinery with the **actual** sup-norm approximation
defect as the cost function:

  `r q = delta α q = inf_{p ∈ ℤᵈ} ‖q • α − p‖_∞`   (the torus distance of `q • α` to the origin).

The payoff: the growth hypothesis fed to `ChevallierCount.chevallier_gap_count_le` — that the record
denominators at least double every `2^d` steps — **holds automatically**, with no extra hypothesis
beyond `RecordsContinue` (irrationality). The two ingredients:

* **`delta_attained`.** For the sup norm the defect is *attained* by coordinatewise rounding:
  `delta α q = ‖q • α − round(q • α)‖`. (Each coordinate is minimised independently — `round_le`.)
  This supplies the `hattain` hypothesis of `SupNormGrowth.supNorm_growth_doubling`.
* **The record structure of `bestDenom`** supplies `hdec` (`bestDenom_cost_antitone`) and the full
  best-approximation property `hbsad` (`bestDenom_strict_floor`: `q_k` strictly beats *every*
  smaller
  positive denominator).

Combining the two, `supNorm_growth_doubling` gives `2 q_k ≤ q_{k+2^d}` for `q_k = bestDenom (delta
α)`,
which is exactly the growth input of `chevallier_gap_count_le`. Hence the **combinatorial bound**
`g_∞ ≤ 2^d + 1` holds for the sup-norm defect cost given only `RecordsContinue` — the growth
geometry
is now entirely discharged (orthant pigeonhole, already proven). The only remaining input to the
*geometric* three-distance statement is the isometry identification (`gapVal = ` nearest-neighbour
distance), handled separately.

Axiom-clean.
-/

namespace ThreeGap.DeltaCost

open ThreeGap.SimApprox ThreeGap.Chevallier

variable {d : ℕ}

/-- **Coordinatewise nearest integer vector** to `q • α`: `round` of each coordinate. For the sup
norm this is the closest lattice point, so it *attains* the defect `delta α q`. -/
noncomputable def nearestInt (α : Fin d → ℝ) (q : ℤ) : Fin d → ℤ :=
  fun k => round ((q : ℝ) * α k)

/-- The remainder against the nearest integer vector, coordinatewise. -/
theorem rem_nearestInt_apply (α : Fin d → ℝ) (q : ℤ) (k : Fin d) :
    rem α q (nearestInt α q) k = (q : ℝ) * α k - round ((q : ℝ) * α k) := by
  simp only [rem, nearestInt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- **The defect is attained by rounding (sup norm).** `delta α q = ‖q • α − round(q • α)‖`. Each
coordinate `|qα_k − round(qα_k)| ≤ |qα_k − p_k|` (`round_le`), so the rounded vector minimises the
sup norm over all integer translates. This is the `hattain` hypothesis of the growth lemma. -/
theorem delta_attained (α : Fin d → ℝ) (q : ℤ) :
    ‖rem α q (nearestInt α q)‖ = delta α q := by
  refine le_antisymm ?_ (delta_le α q (nearestInt α q))
  refine le_ciInf (fun p => ?_)
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun k => ?_)
  rw [rem_nearestInt_apply, Real.norm_eq_abs]
  calc |(q : ℝ) * α k - round ((q : ℝ) * α k)|
      ≤ |(q : ℝ) * α k - (p k : ℝ)| := round_le _ _
    _ = ‖rem α q p k‖ := by rw [Real.norm_eq_abs, rem]; simp [Pi.smul_apply, smul_eq_mul]
    _ ≤ ‖rem α q p‖ := norm_le_pi_norm _ k

/-- **The defect cost** as a function of a natural-number denominator: `r q = delta α q`. -/
noncomputable def deltaCost (α : Fin d → ℝ) : ℕ → ℝ := fun q => delta α (q : ℤ)

/-- `hattain` for the record denominators: at each `q_k = bestDenom`, the defect is attained by the
nearest integer vector. -/
theorem bestDenom_hattain (α : Fin d → ℝ) (hr : RecordsContinue (deltaCost α)) (k : ℕ) :
    ‖rem α ((bestDenom (deltaCost α) hr k : ℤ)) (nearestInt α (bestDenom (deltaCost α) hr k))‖
      = delta α ((bestDenom (deltaCost α) hr k : ℤ)) :=
  delta_attained α _

/-- `hdec` for the record denominators: the defects `delta α q_i` are non-increasing in `i`. -/
theorem bestDenom_hdec (α : Fin d → ℝ) (hr : RecordsContinue (deltaCost α)) {i j : ℕ}
    (h : i ≤ j) :
    delta α ((bestDenom (deltaCost α) hr j : ℤ)) ≤ delta α ((bestDenom (deltaCost α) hr i : ℤ)) :=
  bestDenom_cost_antitone (deltaCost α) hr h

/-- `hbsad` for the record denominators: each `q_k` is a **strict** record minimum over *all*
smaller
positive denominators — `delta α q_k < delta α m` for `0 < m < q_k`. -/
theorem bestDenom_hbsad (α : Fin d → ℝ) (hr : RecordsContinue (deltaCost α)) (k : ℕ) (m : ℤ)
    (hpos : 0 < m) (hlt : m < (bestDenom (deltaCost α) hr k : ℤ)) :
    delta α ((bestDenom (deltaCost α) hr k : ℤ)) < delta α m := by
  have hmnat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hpos.le
  have hj1 : 1 ≤ m.toNat := by omega
  have hj2 : m.toNat < bestDenom (deltaCost α) hr k := by
    have : (m.toNat : ℤ) < (bestDenom (deltaCost α) hr k : ℤ) := by rw [hmnat]; exact hlt
    exact_mod_cast this
  have := bestDenom_strict_floor (deltaCost α) hr k hj1 hj2
  simp only [deltaCost] at this
  rw [← hmnat]
  exact this

/-- **The sup-norm growth inequality for the defect record denominators (unconditional).** With the
defect cost `r q = delta α q` and `RecordsContinue` (irrationality), the record denominators
`q_k = bestDenom (delta α)` at least double every `2^d` steps:

  `2 q_k ≤ q_{k + 2^d}`.

This discharges the growth hypothesis of `ChevallierCount.chevallier_gap_count_le` **with no extra
input** — `hattain` comes from rounding (`delta_attained`), `hdec`/`hbsad` from the record structure
(`bestDenom_*`), and the doubling itself from the orthant pigeonhole (`supNorm_growth_doubling`). -/
theorem bestDenom_supNorm_growth (α : Fin d → ℝ) (hr : RecordsContinue (deltaCost α)) (k : ℕ) :
    2 * bestDenom (deltaCost α) hr k ≤ bestDenom (deltaCost α) hr (k + 2 ^ d) := by
  have hint : 2 * (bestDenom (deltaCost α) hr k : ℤ)
      ≤ (bestDenom (deltaCost α) hr (k + 2 ^ d) : ℤ) :=
    supNorm_growth_doubling α (fun n => (bestDenom (deltaCost α) hr n : ℤ))
      (fun n => nearestInt α (bestDenom (deltaCost α) hr n))
      (bestDenom_int_strictMono (deltaCost α) hr)
      (fun n => bestDenom_hattain α hr n)
      (fun i j h => bestDenom_hdec α hr h)
      (fun n m hpos hlt => bestDenom_hbsad α hr n m hpos hlt)
      k
  exact_mod_cast hint

/-- **`g_∞ ≤ 2^d + 1` for the sup-norm defect cost (combinatorial form, unconditional growth).**
For every `N ≥ 2`, the number of distinct values of the abstract nearest-neighbour distance
`gapVal (delta α) N q` (`q ∈ [0,N]`) is at most `2^d + 1`. The growth is now fully discharged: the
*only* hypothesis is `RecordsContinue` (the best approximations of `α` improve without bound, i.e.
the
appropriate irrationality of `α`). The remaining step to the geometric three-distance statement is
the
isometry identification of `gapVal` with the actual torus nearest-neighbour distance. -/
theorem gap_count_supNorm_le (α : Fin d → ℝ) (hr : RecordsContinue (deltaCost α))
    {N : ℕ} (hN : 2 ≤ N) :
    ((Finset.range (N + 1)).image (gapVal (deltaCost α) N)).card ≤ 2 ^ d + 1 :=
  chevallier_gap_count_le (deltaCost α) hr (2 ^ d) (bestDenom_supNorm_growth α hr) hN

end ThreeGap.DeltaCost
