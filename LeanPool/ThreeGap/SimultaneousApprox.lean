/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Simultaneous Diophantine approximation: the remainder-vector difference inequality

The separation lemma behind the higher-dimensional growth inequality (Lagarias 1980, Ermakov
arXiv:1002.2713) splits into an **elementary algebraic core** and a **convex-geometry completion**.
This file formalizes the algebraic core, faithfully.

For `α : Fin n → ℝ` and an integer `q`, the *approximation defect* is

  `δ_q = inf over p ∈ ℤⁿ of ‖q • α − p‖`,

with `r(q) = q • α − p(q)` the *remainder vector* (`‖r(q)‖ = δ_q`). The crucial elementary fact,
used throughout Ermakov's Lemma 2 (*"`r(qᵢ) − r(qⱼ)` is the remainder vector for `qᵢ − qⱼ`"*): the
difference of two remainder vectors is itself an approximation remainder for the difference of the
denominators, hence its norm is `≥ δ_{qᵢ − qⱼ}`:

  `‖r(qᵢ) − r(qⱼ)‖ ≥ δ_{qᵢ − qⱼ}`.

This is `delta_diff_le`. It is the algebraic input that makes the remainder vectors *spread out*;
the
remaining geometric step (their direction angles exceed `π/3`, so at most `K` = contact-number many
fit) is Ermakov's Lemmas 1–2, the cited geometric completion. Norm-agnostic: holds for every norm
(here the sup norm on `Fin n → ℝ`).

Axiom-clean; elementary.
-/

namespace ThreeGap.SimApprox

variable {n : ℕ}

/-- The integer-vector translate of `q • α` by `p`, as an element of `Fin n → ℝ`. Its norm over all
`p ∈ ℤⁿ` is minimised at the best approximation; here we only need the value and its lower bound. -/
noncomputable def rem (α : Fin n → ℝ) (q : ℤ) (p : Fin n → ℤ) : Fin n → ℝ :=
  (q : ℝ) • α - (fun k => (p k : ℝ))

/-- The **approximation defect** `δ_q = inf_{p ∈ ℤⁿ} ‖q • α − p‖`. -/
noncomputable def delta (α : Fin n → ℝ) (q : ℤ) : ℝ :=
  ⨅ p : Fin n → ℤ, ‖rem α q p‖

/-- The **approximation defect for an arbitrary norm `N`**: `δ^N_q = inf_{p ∈ ℤⁿ} N (q • α − p)`.
(`delta` is the `N = ‖·‖` sup-norm case.) -/
noncomputable def deltaN (N : (Fin n → ℝ) → ℝ) (α : Fin n → ℝ) (q : ℤ) : ℝ :=
  ⨅ p : Fin n → ℤ, N (rem α q p)

/-- For a nonnegative `N`, the defect `δ^N_q` is a lower bound on every concrete approximation. -/
theorem deltaN_le (N : (Fin n → ℝ) → ℝ) (hN : ∀ x, 0 ≤ N x) (α : Fin n → ℝ) (q : ℤ)
    (p : Fin n → ℤ) : deltaN N α q ≤ N (rem α q p) :=
  ciInf_le ⟨0, by rintro _ ⟨p, rfl⟩; exact hN _⟩ p

/-- The range of `p ↦ ‖rem α q p‖` is bounded below (by `0`), so the infimum is genuine. -/
theorem bddBelow_rem (α : Fin n → ℝ) (q : ℤ) :
    BddBelow (Set.range fun p : Fin n → ℤ => ‖rem α q p‖) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact norm_nonneg _⟩

/-- `δ_q` is a lower bound for every concrete approximation: `δ_q ≤ ‖q • α − p‖` for all `p ∈ ℤⁿ`.
-/
theorem delta_le (α : Fin n → ℝ) (q : ℤ) (p : Fin n → ℤ) : delta α q ≤ ‖rem α q p‖ :=
  ciInf_le (bddBelow_rem α q) p

/-- `δ_q ≥ 0`. -/
theorem delta_nonneg (α : Fin n → ℝ) (q : ℤ) : 0 ≤ delta α q :=
  le_ciInf fun _p => norm_nonneg _

/-- **The remainder-vector difference is an approximation remainder for the difference of
denominators.** Algebraically, `(qᵢ • α − pᵢ) − (qⱼ • α − pⱼ) = (qᵢ − qⱼ) • α − (pᵢ − pⱼ)`. -/
theorem rem_sub (α : Fin n → ℝ) (qi qj : ℤ) (pi pj : Fin n → ℤ) :
    rem α qi pi - rem α qj pj = rem α (qi - qj) (pi - pj) := by
  funext k
  simp only [rem, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **Halving homogeneity.** `r(2q, 2p) = 2 · r(q, p)` — doubling both the denominator and the
integer translate doubles the remainder vector. Used in the mod-2 pigeonhole growth argument, where
two best approximations agreeing mod 2 produce a half-integer combination. -/
theorem rem_two_smul (α : Fin n → ℝ) (q : ℤ) (p : Fin n → ℤ) :
    rem α (2 * q) (fun k => 2 * p k) = (2 : ℝ) • rem α q p := by
  funext k
  simp only [rem, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **The separation core (Ermakov Lemma 2, algebraic part).** The distance between two remainder
vectors is at least the approximation defect of the difference of their denominators:

  `δ_{qᵢ − qⱼ} ≤ ‖r(qᵢ) − r(qⱼ)‖`.

Combined with the best-approximation property (every nonzero denominator below `qₖ₊₁` has defect
`≥ δ_{qₖ}`), this makes the remainder vectors `r(qₖ), …, r(qₖ₊ₖ)` pairwise `≥ δ_{qₖ}` apart — the
input to the convex-geometry/contact-number count that yields the growth inequality. -/
theorem delta_diff_le (α : Fin n → ℝ) (qi qj : ℤ) (pi pj : Fin n → ℤ) :
    delta α (qi - qj) ≤ ‖rem α qi pi - rem α qj pj‖ := by
  rw [rem_sub]
  exact delta_le α (qi - qj) (pi - pj)

/-- **Window separation (the fully-proven elementary half of Ermakov's separation lemma).** Let `q`
be strictly increasing with the best-approximation property `hbest` (every positive denominator
below `q (k+1)` has defect `≥ δ_{q k}`). In a *doubling window* `q (k+K) < q (k+1) + q k`, any two
of
the remainder vectors `r(q k), …, r(q (k+K))` are at least `δ_{q k}` apart:

  `δ_{q k} ≤ ‖r(qᵢ) − r(qⱼ)‖`   for `k ≤ j < i ≤ k+K`.

Proof: `0 < qᵢ − qⱼ < q (k+1)` (the window keeps the index gap below `q (k+1)`), so `hbest` gives
`δ_{q k} ≤ δ_{qᵢ − qⱼ}`, and `delta_diff_le` gives `δ_{qᵢ − qⱼ} ≤ ‖r(qᵢ) − r(qⱼ)‖`.

Since the remainder lengths `‖r(q i)‖ = δ_{q i}` decrease, these are `K+1` vectors of norm `≤ δ_{q
k}`
that are pairwise `≥ δ_{q k}` apart. The *geometric* completion — their normalised directions are
pairwise `> π/3`, so at most `K` = contact-number many exist — is Ermakov's Lemmas 1–2, the one
remaining cited input (`ThreeGap.growth_of_separation`'s hypothesis). -/
theorem window_separation (α : Fin n → ℝ) (q : ℕ → ℤ) (p : ℕ → Fin n → ℤ)
    (hmono : StrictMono q)
    (hbest : ∀ k (m : ℤ), 0 < m → m < q (k + 1) → delta α (q k) ≤ delta α m)
    {K k i j : ℕ} (hk : k ≤ j) (hj : j < i) (hi : i ≤ k + K)
    (hwin : q (k + K) < q (k + 1) + q k) :
    delta α (q k) ≤ ‖rem α (q i) (p i) - rem α (q j) (p j)‖ := by
  have hji : q j < q i := hmono hj
  have hik : q i ≤ q (k + K) := hmono.monotone (by omega)
  have hkj : q k ≤ q j := hmono.monotone hk
  have hpos : (0 : ℤ) < q i - q j := by omega
  have hub : q i - q j < q (k + 1) := by omega
  calc delta α (q k) ≤ delta α (q i - q j) := hbest k (q i - q j) hpos hub
    _ ≤ ‖rem α (q i) (p i) - rem α (q j) (p j)‖ := delta_diff_le α (q i) (q j) (p i) (p j)

end ThreeGap.SimApprox
