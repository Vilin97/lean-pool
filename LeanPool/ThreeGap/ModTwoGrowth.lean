/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import LeanPool.ThreeGap.SimultaneousApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators

/-!
# The any-norm growth inequality via the mod-2 pigeonhole (Lagarias II, Theorem 6)

The canonical growth inequality for best simultaneous Diophantine approximations, valid for **every
norm** on `ℝ^d` (Lagarias, *Best simultaneous Diophantine approximations II*, Pacific J. Math. 102
(1982), Thm 6; restated in the Chevallier survey 2011, p. 5):

  `q_{n + 2^{d+1}} ≥ 2 q_{n+1} + q_n`.

The proof is a **mod-2 pigeonhole**: among the `2^{d+1} + 1` best-approximation vectors
`(P_{n+k}, q_{n+k})`, two agree mod 2 (there are only `2^{d+1}` parity classes in `(ℤ/2)^{d+1}`);
their half-difference `(P, q)` is an integer vector with `0 < q < q_{n+1}` and remainder norm
`≤ ½(δ_{q_{n+1}} + δ_{q_n}) < δ_{q_n}`, contradicting the best-approximation/record property.

To get genuine **any-norm** generality we abstract the norm as a function `N` with the three norm
properties (`hN_nonneg`, `hN_tri`, `hN_smul`) and the approximation defect as `δ` (a lower bound on
`N (rem …)`, with the best-approximation record structure). The norm-free remainder algebra
(`SimApprox.rem`, `rem_sub`, `rem_two_smul`) is reused verbatim. Instantiating `N` at the Euclidean
norm gives the Euclidean growth inequality (`q_{n+8} ≥ 2q_{n+1}+q_n` for `d = 2`), the input for the
five-distance theorem.

Axiom-clean.
-/

namespace ThreeGap.SimApprox

/-- **The any-norm growth inequality (mod-2 pigeonhole).** For an abstract norm `N` and a
best-approximation sequence `(q, p)` with defect `δ` (record minima), the denominators satisfy
`2 q_{n+1} + q_n ≤ q_{n + 2^{d+1}}`. Hypotheses: `N` is a norm (`nonneg`, triangle `tri`,
homogeneity `smul`); `δ m ≤ N (rem α m P)` for every integer translate (`hδ_le`); the chosen
remainders nearly attain the defect (`hattain`); defects strictly decrease along the sequence
(`hdec`); and each `q k` is a record (`hbest`: every positive denominator below `q (k+1)` has defect
`≥ δ (q k)`). -/
theorem growth_additive_modTwo {d : ℕ}
    (N : (Fin d → ℝ) → ℝ)
    (hN_tri : ∀ x y, N (x + y) ≤ N x + N y)
    (hN_smul : ∀ (c : ℝ) (x : Fin d → ℝ), N (c • x) = |c| * N x)
    (α : Fin d → ℝ) (q : ℕ → ℤ) (p : ℕ → Fin d → ℤ) (δ : ℤ → ℝ)
    (hmono : StrictMono q)
    (hδ_le : ∀ (m : ℤ) (P : Fin d → ℤ), δ m ≤ N (rem α m P))
    (hattain : ∀ k, N (rem α (q k) (p k)) ≤ δ (q k))
    (hdec : ∀ k, δ (q (k + 1)) < δ (q k))
    (hbest : ∀ (k : ℕ) (m : ℤ), 0 < m → m < q (k + 1) → δ (q k) ≤ δ m)
    (n : ℕ) :
    2 * q (n + 1) + q n ≤ q (n + 2 ^ (d + 1)) := by
  have hanti : ∀ i j, i ≤ j → δ (q j) ≤ δ (q i) :=
    fun i j hij => (strictAnti_nat_of_succ_lt (f := fun k => δ (q k)) hdec).antitone hij
  by_contra hcon
  rw [not_le] at hcon
  set sig : ℕ → (Fin d → Bool) × Bool :=
    fun k => (fun i => decide (Even (p (n + k) i)), decide (Even (q (n + k)))) with hsig
  -- core contradiction for an ordered same-parity pair
  have key : ∀ i0 j0 : ℕ, i0 < j0 → j0 ≤ 2 ^ (d + 1) → sig i0 = sig j0 → False := by
    intro i0 j0 hlt hle hse
    have hqpar : Even (q (n + j0)) ↔ Even (q (n + i0)) := by
      have h := congrArg Prod.snd hse
      simp only [hsig, decide_eq_decide] at h
      exact h.symm
    have hppar : ∀ k, Even (p (n + j0) k) ↔ Even (p (n + i0) k) := by
      intro k
      have h := congrFun (congrArg Prod.fst hse) k
      simp only [hsig, decide_eq_decide] at h
      exact h.symm
    have hqeven : Even (q (n + j0) - q (n + i0)) := Int.even_sub.mpr hqpar
    have hpeven : ∀ k, Even (p (n + j0) k - p (n + i0) k) := fun k => Int.even_sub.mpr (hppar k)
    set a2 : ℤ := q (n + j0) - q (n + i0) with ha2
    set Pd : Fin d → ℤ := fun k => p (n + j0) k - p (n + i0) k with hPd
    set Q : ℤ := a2 / 2 with hQ
    set Pv : Fin d → ℤ := fun k => Pd k / 2 with hPv
    have h2Q : 2 * Q = a2 := by rw [hQ, mul_comm]; exact Int.ediv_mul_cancel hqeven.two_dvd
    have h2Pv : ∀ k, 2 * Pv k = Pd k := fun k => by
      rw [hPv, mul_comm]; exact Int.ediv_mul_cancel (hpeven k).two_dvd
    have hqlt : q (n + i0) < q (n + j0) := hmono (by omega)
    have ha2pos : 0 < a2 := by rw [ha2]; omega
    have hQpos : 0 < Q := by omega
    -- a2 < 2 q_{n+1}, hence Q < q_{n+1}
    have hjub : q (n + j0) ≤ q (n + 2 ^ (d + 1)) := hmono.monotone (by omega)
    have hilb : q n ≤ q (n + i0) := hmono.monotone (by omega)
    have hQlt : Q < q (n + 1) := by omega
    -- the half-difference vector equals (ε_j - ε_i), so its norm is small
    have hsubeq : rem α a2 Pd
        = rem α (q (n + j0)) (p (n + j0)) - rem α (q (n + i0)) (p (n + i0)) := by
      rw [ha2, show Pd = p (n + j0) - p (n + i0) from rfl]
      exact (rem_sub α _ _ _ _).symm
    have hrt : rem α a2 Pd = (2 : ℝ) • rem α Q Pv := by
      rw [show a2 = 2 * Q from h2Q.symm, show Pd = (fun k => 2 * Pv k) from
        funext fun k => (h2Pv k).symm]
      exact rem_two_smul α Q Pv
    have hdouble : N (rem α a2 Pd) = 2 * N (rem α Q Pv) := by
      rw [hrt, hN_smul]; norm_num
    have hbound : N (rem α a2 Pd) ≤ δ (q (n + 1)) + δ (q n) := by
      rw [hsubeq]
      have hnb : N (-(rem α (q (n + i0)) (p (n + i0))))
          = N (rem α (q (n + i0)) (p (n + i0))) := by
        rw [← neg_one_smul ℝ, hN_smul]; norm_num
      have hstep1 : N (rem α (q (n + j0)) (p (n + j0)) - rem α (q (n + i0)) (p (n + i0)))
          ≤ N (rem α (q (n + j0)) (p (n + j0))) + N (rem α (q (n + i0)) (p (n + i0))) := by
        rw [sub_eq_add_neg]
        exact le_trans (hN_tri _ _) (by rw [hnb])
      have hatt_j : N (rem α (q (n + j0)) (p (n + j0))) ≤ δ (q (n + 1)) :=
        le_trans (hattain (n + j0)) (hanti (n + 1) (n + j0) (by omega))
      have hatt_i : N (rem α (q (n + i0)) (p (n + i0))) ≤ δ (q n) :=
        le_trans (hattain (n + i0)) (hanti n (n + i0) (by omega))
      linarith [hstep1, hatt_j, hatt_i]
    -- assemble the contradiction
    have hQle : δ (q n) ≤ δ Q := hbest n Q hQpos hQlt
    have hδQ : δ Q ≤ N (rem α Q Pv) := hδ_le Q Pv
    have hdn : δ (q (n + 1)) < δ (q n) := hdec n
    linarith [hQle, hδQ, hdouble, hbound, hdn]
  -- pigeonhole over the 2^{d+1}+1 indices
  have hcard : Fintype.card ((Fin d → Bool) × Bool) < Fintype.card (Fin (2 ^ (d + 1) + 1)) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin,
      pow_succ]
    omega
  obtain ⟨a, b, hab, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (2 ^ (d + 1) + 1) => sig k.val) hcard
  have hne : a.val ≠ b.val := fun h => hab (Fin.val_injective h)
  have hale : a.val ≤ 2 ^ (d + 1) := Nat.lt_succ_iff.mp a.isLt
  have hble : b.val ≤ 2 ^ (d + 1) := Nat.lt_succ_iff.mp b.isLt
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a.val b.val h hble heq
  · exact key b.val a.val h hale heq.symm

/-- **The sup-norm additive growth inequality** as the concrete instance of the abstract mod-2
theorem at the sup norm `‖·‖` on `Fin d → ℝ` (with `δ = SimApprox.delta`): `2 q_{n+1} + q_n ≤
q_{n + 2^{d+1}}`. This is the additive (Lagarias II Thm 6) form; the `supNorm_growth_doubling`
companion gives the doubling form with the better constant `2^d` via the orthant pigeonhole. -/
theorem supNorm_growth_additive {d : ℕ} (α : Fin d → ℝ) (q : ℕ → ℤ) (p : ℕ → Fin d → ℤ)
    (hmono : StrictMono q)
    (hattain : ∀ k, ‖rem α (q k) (p k)‖ ≤ delta α (q k))
    (hdec : ∀ k, delta α (q (k + 1)) < delta α (q k))
    (hbest : ∀ (k : ℕ) (m : ℤ), 0 < m → m < q (k + 1) → delta α (q k) ≤ delta α m)
    (n : ℕ) : 2 * q (n + 1) + q n ≤ q (n + 2 ^ (d + 1)) :=
  growth_additive_modTwo (fun x => ‖x‖) (fun x y => norm_add_le x y)
    (fun c x => by show ‖c • x‖ = |c| * ‖x‖; rw [norm_smul, Real.norm_eq_abs]) α q p (delta α) hmono
    (fun m P => delta_le α m P) hattain hdec hbest n

end ThreeGap.SimApprox
