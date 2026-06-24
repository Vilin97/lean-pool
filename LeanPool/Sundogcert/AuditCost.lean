/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
  Audit-asymmetry certificate  (Lean 4 / mathlib v4.30.0) — HS7, prereg frozen at `37d3306`.

  ONE FINITE SETTING.  Populations are `u : Fin n → ℚ`; the observation channel is the pair
  `(report, pooledMean u)`; empirical statistics are finite sums.  No `Measure ℝ` anywhere — the
  audit half and the blindness half live on literally the same interface (the banked ShadowDecay
  tower states its determine/resist law in `Measure ℝ`; this module is its finite, certificate-
  grade sibling, not a restatement).

  WHAT IS PROVED.
    (i)  An audit game sound against an ADVERSARIAL REPORTER: over reporter strategies
         `σ : (Fin n → ℚ) → ℚ`, no false report accepts (`audit_sound`, `dishonest_caught`) and
         the honest report always accepts (`audit_complete`, `honest_accepts`) — with a faithful
         per-audit op-count `auditCost n ≤ 3·n + 2` (`auditCost_le`), exact value `2n + 1`
         (`auditCost_eq`), in the CheckCost.lean trust-surface style.
    (ii) CHANNEL-LEVEL BLINDNESS QUANTIFIED OVER ALL VERIFIERS (`pooled_channel_blind`): for EVERY
         decidable `A : ℚ × ℚ → Bool` seeing only `(report, pooledMean u)`, every coordinate `i`,
         and every prescribed `δ`, an EXPLICIT fiber pair (`bump`) has equal pooled mean, per-unit
         difference exactly `δ`, and identical verdicts for every report.  Impossibility form
         (`no_verifier_checks_perUnit`): no channel verifier is sound-and-complete for ANY
         per-unit claim `u i = v`.
    (iii) NON-VACUITY: at `n = 1` the channel DETERMINES the unit (`n1_channel_determines`) — the
         blindness genuinely needs `n ≥ 2`; and the same fiber pair every channel verifier misses
         is SEPARATED by the second-moment statistic (`secondMoment_separates`) — the hidden
         information sits one statistic above the mean; it is the channel that is blind, not the
         pair that is identical.
    HEADLINE (`audit_asymmetry`): full per-unit access decides every report at linear cost, while
    every pooled-channel verifier is per-unit blind — one statement, one setting.

  TRUST SURFACE (audited by a human, exactly as in CheckCost.lean).  The COST MODEL: the audit's
  dominant path folds the `n` per-unit values into the running sum (`n` term-reads counted by
  `sumReadCost`, `n − 1` additions), then one division by `n`, one equality test against the
  report.  Nothing forces this correspondence mechanically — it is asserted, then audited.  Given
  the audited model, `auditCost_le` is a THEOREM (kernel-checked, axiom-clean, no `native_decide`).

  HONEST SCOPE.
    • The blindness certifies the POOLED OBSERVABLE.  A reporter that itself has per-unit access
      can still encode per-unit facts in the report; the theorem says no verifier can CHECK such a
      claim against the pooled observable (`no_verifier_checks_perUnit`) — not that reports carry
      no information.
    • A finite rational-mean channel — the certified template for audit-asymmetry claims; NOT a
      claim about trained systems, and NOT "introspection".
    • The blindness PROOF is short: data processing is short (verdict equality is congruence from
      pooled-mean equality).  The content is the STATEMENT — what is quantified over (`∀` verifier)
      and what is constructed (the prescribed-δ fiber pair) — adjudicated by the prereg's K2
      structure audit against the banked-statement list.
-/

namespace Sundog.AuditCost

/-! ### The channel -/

/-- The pooled mean — the lossy shadow of the population that the channel exposes. -/
def pooledMean {n : ℕ} (u : Fin n → ℚ) : ℚ := (∑ i, u i) / n

/-- At `n = 1` the channel DETERMINES the unit: `pooledMean u = u 0`.  Blindness below genuinely
    requires `n ≥ 2` — it is a statement about pooling, not a generic artifact. -/
theorem n1_channel_determines (u : Fin 1 → ℚ) : pooledMean u = u 0 := by
  simp [pooledMean]

/-! ### The audit game (full per-unit access, adversarial reporter) -/

/-- A reporter strategy: sees the full population, emits a report. Adversarial = arbitrary. -/
def ReporterStrategy (n : ℕ) : Type := (Fin n → ℚ) → ℚ

/-- The honest strategy reports the pooled mean itself. -/
def Honest {n : ℕ} (σ : ReporterStrategy n) : Prop := ∀ u, σ u = pooledMean u

/-- The full-access audit: recompute the pooled mean from the per-unit values, compare. -/
def auditAccept {n : ℕ} (u : Fin n → ℚ) (r : ℚ) : Bool := decide (r = pooledMean u)

/-- **Audit soundness** — no false report accepts. -/
theorem audit_sound {n : ℕ} (u : Fin n → ℚ) (r : ℚ) :
    auditAccept u r = true → r = pooledMean u := fun h => of_decide_eq_true h

/-- **Audit completeness** — the honest report always accepts. -/
theorem audit_complete {n : ℕ} (u : Fin n → ℚ) : auditAccept u (pooledMean u) = true :=
  decide_eq_true rfl

/-- Game form of completeness: every honest strategy passes every audit. -/
theorem honest_accepts {n : ℕ} (σ : ReporterStrategy n) (hσ : Honest σ) (u : Fin n → ℚ) :
    auditAccept u (σ u) = true := by
  rw [hσ u]; exact audit_complete u

/-- Game form of soundness: every dishonest move is caught, whatever the strategy. -/
theorem dishonest_caught {n : ℕ} (σ : ReporterStrategy n) (u : Fin n → ℚ)
    (h : σ u ≠ pooledMean u) : auditAccept u (σ u) = false := decide_eq_false h

/-! ### The cost model (TRUST SURFACE — see header) -/

/-- Structural term-read count for folding the `n` per-unit values: one `(1 : ℕ)` per term. -/
def sumReadCost (n : ℕ) : ℕ := ∑ _i : Fin n, 1

/-- The structural read-count equals `n`. -/
theorem sumReadCost_eq (n : ℕ) : sumReadCost n = n := by
  simp [sumReadCost]

/-- **Per-audit cost** on the dominant path:
    `sumReadCost n` term-reads + `n − 1` additions + `1` division + `1` equality test. -/
def auditCost (n : ℕ) : ℕ := sumReadCost n + (n - 1) + 2

/-- Exact value of the cost model: `n + (n − 1) + 2` (= `2n + 1` for `n ≥ 1`) — stated so the
    headroom under the headline bound is visible, not hidden. -/
theorem auditCost_eq (n : ℕ) : auditCost n = n + (n - 1) + 2 := by
  rw [auditCost, sumReadCost_eq]

/-- **THE COST THEOREM** — auditing is linear: `auditCost n ≤ 3·n + 2`. -/
theorem auditCost_le (n : ℕ) : auditCost n ≤ 3 * n + 2 := by
  rw [auditCost_eq]; omega

/-! ### The fiber-pair construction -/

/-- Move coordinate `i` up by `δ` and coordinate `j` down by `δ`: the pooled mean is unchanged
    while `u i` shifts by exactly the prescribed amount (when `i ≠ j`). -/
def bump {n : ℕ} (u : Fin n → ℚ) (i j : Fin n) (δ : ℚ) : Fin n → ℚ :=
  fun k => u k + (if k = i then δ else 0) - (if k = j then δ else 0)

/-- The bump is invisible to the pooled mean: the `+δ` and `−δ` cancel in the sum. -/
theorem pooledMean_bump {n : ℕ} (u : Fin n → ℚ) (i j : Fin n) (δ : ℚ) :
    pooledMean (bump u i j δ) = pooledMean u := by
  unfold pooledMean bump
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp

/-- The bump hits coordinate `i` by exactly the prescribed `δ`. -/
theorem bump_apply {n : ℕ} (u : Fin n → ℚ) (i j : Fin n) (δ : ℚ) (hij : i ≠ j) :
    bump u i j δ i = u i + δ := by
  simp [bump, hij]

/-- `Fin n` has two distinct elements once `2 ≤ n` (explicit witnesses `0` and `1`). -/
theorem fin_nontrivial {n : ℕ} (hn : 2 ≤ n) : Nontrivial (Fin n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, fun h => ?_⟩
  have hval := congrArg Fin.val h
  simp at hval

/-! ### THE BLINDNESS THEOREMS — quantified over ALL verifiers -/

/-- **∀-verifier per-unit blindness of the pooled channel.**  For EVERY decidable verifier
    `A : ℚ × ℚ → Bool` on the channel `(report, pooledMean u)`, every population `u`, every
    coordinate `i`, and every prescribed difference `δ`, there is an explicit population `u'`
    with the same pooled mean, `u' i = u i + δ`, and `A`'s verdict identical on both for every
    report.  Finite data processing, with the fiber pair exhibited (`bump`). -/
theorem pooled_channel_blind {n : ℕ} (hn : 2 ≤ n) (A : ℚ × ℚ → Bool)
    (u : Fin n → ℚ) (i : Fin n) (δ : ℚ) :
    ∃ u' : Fin n → ℚ,
      pooledMean u' = pooledMean u ∧ u' i = u i + δ ∧
      ∀ r : ℚ, A (r, pooledMean u') = A (r, pooledMean u) := by
  haveI := fin_nontrivial hn
  obtain ⟨j, hj⟩ := exists_ne i
  exact ⟨bump u i j δ, pooledMean_bump u i j δ, bump_apply u i j δ (Ne.symm hj),
    fun r => by rw [pooledMean_bump]⟩

/-- A pooled-mean fiber pair on which `P` differs rules out every sound-and-complete channel
    verifier for `P`: the impossibility engine behind `no_verifier_checks_perUnit`. -/
theorem no_channel_verifier_decides {n : ℕ} (P : (Fin n → ℚ) → Prop)
    (hfib : ∃ u u' : Fin n → ℚ, pooledMean u' = pooledMean u ∧ P u ∧ ¬P u') :
    ¬∃ A : ℚ × ℚ → Bool, ∀ (u : Fin n → ℚ) (r : ℚ), A (r, pooledMean u) = true ↔ P u := by
  rintro ⟨A, hA⟩
  obtain ⟨u, u', hm, hPu, hPu'⟩ := hfib
  have h1 := hA u 0
  have h2 := hA u' 0
  rw [hm] at h2
  exact hPu' (h2.mp (h1.mpr hPu))

/-- **No channel verifier checks any per-unit claim.**  For every coordinate `i`, claimed value
    `v`, and any nonzero `δ`, NO decidable verifier on `(report, pooledMean u)` is
    sound-and-complete for the claim `u i = v` — the witnessing fiber pair differs by `δ` at `i`
    yet is indistinguishable through the channel. -/
theorem no_verifier_checks_perUnit {n : ℕ} (hn : 2 ≤ n) (i : Fin n) (v δ : ℚ) (hδ : δ ≠ 0) :
    ¬∃ A : ℚ × ℚ → Bool,
      ∀ (u : Fin n → ℚ) (r : ℚ), A (r, pooledMean u) = true ↔ u i = v := by
  haveI := fin_nontrivial hn
  obtain ⟨j, hj⟩ := exists_ne i
  apply no_channel_verifier_decides (P := fun u => u i = v)
  refine ⟨fun _ => v, bump (fun _ => v) i j δ, pooledMean_bump _ i j δ, rfl, ?_⟩
  rw [bump_apply _ i j δ (Ne.symm hj)]
  intro h
  exact hδ (by linarith)

/-! ### Non-vacuity: the information is one statistic up, not gone -/

/-- An empirical finite-sum statistic of the population — the channel only exposes the `g = id`
    member of this family (the pooled mean). -/
def empStat {n : ℕ} (g : ℚ → ℚ) (u : Fin n → ℚ) : ℚ := (∑ i, g (u i)) / n

/-- **The fiber pair is separated one statistic up.**  The same explicit pair that every channel
    verifier misses is distinguished by the second moment `x ↦ x²` — the per-unit information is
    present in the population; the pooled-mean channel is what is blind to it. -/
theorem secondMoment_separates {n : ℕ} (hn : 2 ≤ n) (i : Fin n) (δ : ℚ) (hδ : δ ≠ 0) :
    ∃ u u' : Fin n → ℚ,
      pooledMean u' = pooledMean u ∧ u' i = u i + δ ∧
      empStat (fun x => x ^ 2) u' ≠ empStat (fun x => x ^ 2) u := by
  haveI := fin_nontrivial hn
  obtain ⟨j, hj⟩ := exists_ne i
  refine ⟨fun _ => 0, bump (fun _ => 0) i j δ, pooledMean_bump _ i j δ, ?_, ?_⟩
  · rw [bump_apply _ i j δ (Ne.symm hj)]
  · have hsq : ∀ k, (bump (fun _ => (0 : ℚ)) i j δ k) ^ 2
        = (if k = i then δ ^ 2 else 0) + (if k = j then δ ^ 2 else 0) := by
      intro k
      simp only [bump]
      split_ifs with h1 h2
      · exact absurd (h1.symm.trans h2) (Ne.symm hj)
      · ring
      · ring
      · ring
    have hsum : (∑ k, (bump (fun _ => (0 : ℚ)) i j δ k) ^ 2) = δ ^ 2 + δ ^ 2 := by
      rw [Finset.sum_congr rfl fun k _ => hsq k, Finset.sum_add_distrib]
      simp
    have hzero : empStat (fun x => x ^ 2) (fun _ : Fin n => (0 : ℚ)) = 0 := by
      simp [empStat]
    rw [hzero]
    unfold empStat
    rw [hsum]
    have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnum : δ ^ 2 + δ ^ 2 ≠ 0 := by
      have hsqz := pow_ne_zero 2 hδ
      intro h
      exact hsqz (by linarith)
    exact div_ne_zero hnum hn0

/-! ### THE HEADLINE — the audit asymmetry in one statement -/

/-- **Audit asymmetry.**  In one finite setting: (1) the full-access audit DECIDES every report —
    accept iff the report is the true pooled mean — sound and complete against any adversarial
    reporter; (2) at linear cost `≤ 3n + 2`; while (3) EVERY decidable verifier seeing only the
    pooled channel is per-unit blind — for any coordinate and any prescribed difference `δ` there
    is an explicit same-mean population on which its verdict is identical for every report.
    Quantifier shape: `∀ verifier, ∃ fiber pair` — present in no banked statement of this repo
    (prereg K2 list). -/
theorem audit_asymmetry {n : ℕ} (hn : 2 ≤ n) :
    (∀ (u : Fin n → ℚ) (r : ℚ), auditAccept u r = true ↔ r = pooledMean u) ∧
    auditCost n ≤ 3 * n + 2 ∧
    ∀ (A : ℚ × ℚ → Bool) (u : Fin n → ℚ) (i : Fin n) (δ : ℚ),
      ∃ u' : Fin n → ℚ,
        pooledMean u' = pooledMean u ∧ u' i = u i + δ ∧
        ∀ r : ℚ, A (r, pooledMean u') = A (r, pooledMean u) := by
  refine ⟨fun u r => ⟨audit_sound u r, fun h => ?_⟩, auditCost_le n,
    fun A u i δ => pooled_channel_blind hn A u i δ⟩
  rw [h]; exact audit_complete u

/-! ### Concrete toy instance (n = 8) — illustration, not a kill surface.
    Kernel `decide` gets stuck reducing `ℚ` arithmetic, so the toy is checked by `norm_num`
    (pre-authorized by the prereg §3 carve-out; no axioms beyond the foundational triple). -/

/-- A concrete population of 8 units (sum 31, pooled mean 31/8). -/
def u₈ : Fin 8 → ℚ := ![3, 1, 4, 1, 5, 9, 2, 6]

example : auditAccept u₈ (31 / 8) = true := by
  norm_num [auditAccept, pooledMean, u₈, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, decide_eq_true_eq]

example : auditAccept u₈ 4 = false := by
  norm_num [auditAccept, pooledMean, u₈, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, decide_eq_false_iff_not]

end Sundog.AuditCost
