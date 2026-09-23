/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound
import LeanPool.AsymptoticTrianglePacking.Internal.CeilingOracle
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.LossVariance

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the tight-band assembly: from one sharp round to the
LeanPool.AsymptoticTrianglePacking.Internal theorem

This file performs the ASSEMBLY of the LeanPool.AsymptoticTrianglePacking.Internal out of the
iterable single round
`LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundHyp`
(`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound`):

* `LeanPool.AsymptoticTrianglePacking.Internal.TightParams` — the schedule: the round rate `γ`, the
  relative tolerance `ε`, the per-round
  exceptional fraction `θ`, the initial exceptional fraction `η`, the number of rounds `T`, the
  degree band `[d·lo k, d·hi k]` after `k` rounds and the exceptional budget `sig k`, together with
  every inequality the iteration consumes.
* `LeanPool.AsymptoticTrianglePacking.Internal.roundOracle_of_sharpRound_params` — one round of the
  schedule: the tight-band invariant is
  re-established (band, global ceiling, codegree, exceptional budget) and a `γ/(16r)` fraction of
  the
  uncovered vertices is covered; iterated by
  `LeanPool.AsymptoticTrianglePacking.Internal.hasRoundOracle_of_scheduled_invariant`.
* `LeanPool.AsymptoticTrianglePacking.Internal.exists_tightParams` — the schedule exists for every
  `r ≥ 2` and `β ∈ (0,1)`.
* `LeanPool.AsymptoticTrianglePacking.Internal.roundOracleExistsCeil_of_sharpRound`,
  `LeanPool.AsymptoticTrianglePacking.Internal.nibbleTheoremMostCeil_of_sharpRound`,
  `LeanPool.AsymptoticTrianglePacking.Internal.nibbleTheoremMostCeilSized_of_sharpRound`,
  `LeanPool.AsymptoticTrianglePacking.Internal.nibbleTheorem_of_sharpRound` — the
  packaged conclusions.

The three mechanisms of the assembly are:

* **the band step** — the floor falls by at most `((r−1)/r)γΔ + εγΔ` and the ceiling by at least
  `((r−1)/r)γ(δ−lost)δ(1−γ)/Δ − εγΔ`, so a band of relative width `n` widens to `n(1 + 8((r−1)/r)γ)`
  while both ends fall by the factor `1 − ((r−1)/r)γ`;
* **the exceptional bookkeeping** — the vertices that leave the band (`B`), the vertices with too
  many edges into the exceptional set (`heavy`), the vertices that break the new ceiling (`Hi`,
  contained in `E ∪ B ∪ heavy`) and the vertices damaged by pruning `Hi` (`Dam`) are all counted by
  the deterministic estimate `LeanPool.AsymptoticTrianglePacking.Internal.card_heavyLoss_le`; the
  exceptional set therefore grows by a
  bounded factor `(2 + r/(εγ))²` per round, which the choice of `θ` absorbs;
* **the covering count** — the round covers a `γ/(8r)` fraction of the live set, which is at least
  half of the uncovered set as long as the exceptional set stays below `β|V|/2`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-! ## The schedule -/

/-- **The tight-band schedule.** All parameters of the `T`-round
LeanPool.AsymptoticTrianglePacking.Internal at uniformity `r` and target
`β`, with the inequalities the iteration consumes.  `lo k`, `hi k` are the degree band after `k`
rounds RELATIVE to the regular degree `d`, and `sig k` is the exceptional budget as a fraction of
`|V|`. -/
structure TightParams (r : ℕ) (β : ℝ) where
  /-- round rate -/
  gam : ℝ
  /-- relative band tolerance -/
  eps : ℝ
  /-- per-round exceptional fraction -/
  exc : ℝ
  /-- initial exceptional fraction -/
  eta : ℝ
  /-- initial relative band width -/
  wid : ℝ
  /-- a positive lower bound for the relative band floor -/
  lomin : ℝ
  /-- the number of rounds -/
  T : ℕ
  /-- relative degree floor after `k` rounds -/
  lo : ℕ → ℝ
  /-- relative degree ceiling after `k` rounds -/
  hi : ℕ → ℝ
  /-- exceptional budget after `k` rounds -/
  sig : ℕ → ℝ
  gam_pos : 0 < gam
  gam_le : gam ≤ 1 / 2
  eps_pos : 0 < eps
  eps_le : eps ≤ 1
  /-- the tolerance is at least twice the round rate; this is the regime in which the sharp round
  `LeanPool.AsymptoticTrianglePacking.Internal.sharpRoundFor_of_two_gamma_le_eps` is proved -/
  two_gam_le_eps : 2 * gam ≤ eps
  exc_pos : 0 < exc
  exc_le : exc ≤ 1
  eta_pos : 0 < eta
  wid_pos : 0 < wid
  lomin_pos : 0 < lomin
  lomin_le : ∀ k, k ≤ T → lomin ≤ lo k
  hi_le_two_lo : ∀ k, k ≤ T → hi k ≤ 2 * lo k
  lo_le_hi : ∀ k, k ≤ T → lo k ≤ hi k
  init_lo : lo 0 ≤ 1 - wid
  init_hi : 1 + wid ≤ hi 0
  step_lo : ∀ k, k < T →
    lo (k + 1) ≤ lo k - ((r : ℝ) - 1) / r * gam * hi k - 2 * eps * gam * hi k
  step_hi : ∀ k, k < T →
    hi k - ((r : ℝ) - 1) / r * gam * (lo k - eps * gam * hi k) * lo k * (1 - gam) / hi k
      + eps * gam * hi k ≤ hi (k + 1)
  sig_init : eta ≤ sig 0
  sig_step : ∀ k, k < T → (2 + (r : ℝ) / (eps * gam)) ^ 2 * (sig k + exc) ≤ sig (k + 1)
  sig_le : ∀ k, k ≤ T → sig k ≤ β / 2
  decay : (1 - gam / (16 * r)) ^ T ≤ β

/-! ## Elementary hypergraph bricks used by the step -/

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Pruning kills the degree of the pruned vertices. -/
theorem degree_prune_eq_zero {K : Finset (Finset V)} {B : Finset V} {v : V} (hv : v ∈ B) :
    degree (prune K B) v = 0 := by
  classical
  rw [degree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hve
  rw [prune, Finset.mem_filter] at he
  exact (Finset.disjoint_left.mp he.2 hve) hv

omit [Fintype V] in
/-- Degrees are monotone in the hypergraph. -/
theorem degree_mono {K K' : Finset (Finset V)} (h : K' ⊆ K) (v : V) :
    degree K' v ≤ degree K v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

omit [Fintype V] in
/-- Codegrees are monotone in the hypergraph. -/
theorem codegree_mono {K K' : Finset (Finset V)} (h : K' ⊆ K) (x y : V) :
    codegree K' x y ≤ codegree K x y :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

omit [Fintype V] in
/-- Only the part of the deleted set that the edges actually meet matters. -/
theorem lostDegree_union_of_disjoint {K : Finset (Finset V)} {S E : Finset V}
    (hS : ∀ e ∈ K, Disjoint e S) (v : V) :
    lostDegree K (S ∪ E) v = lostDegree K E v := by
  classical
  unfold lostDegree
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro e he
  constructor
  · rintro ⟨hve, hne⟩
    refine ⟨hve, fun hd => hne ?_⟩
    rw [Finset.disjoint_union_right]
    exact ⟨hS e he, hd⟩
  · rintro ⟨hve, hne⟩
    refine ⟨hve, fun hd => hne ?_⟩
    exact (Finset.disjoint_union_right.mp hd).2

omit [Fintype V] in
/-- A vertex in an edge-avoided set has degree zero. -/
theorem degree_eq_zero_of_disjoint {K : Finset (Finset V)} {S : Finset V}
    (hS : ∀ e ∈ K, Disjoint e S) {v : V} (hv : v ∈ S) : degree K v = 0 := by
  classical
  rw [degree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hve
  exact (Finset.disjoint_left.mp (hS e he) hve) hv

omit [Fintype V] in
/-- The number of edges meeting `B`, bounded by the degree sum over `B`. -/
theorem card_edges_meeting_le_sum {K : Finset (Finset V)} (B : Finset V) :
    (K.filter (fun e => ¬ Disjoint e B)).card ≤ ∑ x ∈ B, degree K x := by
  exact Hypergraph.edges_meeting_le_of_not_disjoint K B

/-- The total loss equals the size of the edges meeting `B`. -/
theorem sum_lostDegree_eq {K : Finset (Finset V)} (B : Finset V) :
    ∑ v : V, lostDegree K B v = ∑ e ∈ K.filter (fun e => ¬ Disjoint e B), e.card := by
  classical
  have h1 : ∀ v : V, lostDegree K B v
      = ∑ e ∈ K, (if v ∈ e ∧ ¬ Disjoint e B then 1 else 0) := by
    intro v; unfold lostDegree; rw [Finset.card_filter]
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases hd : Disjoint e B
  · simp [hd]
  · simp [hd, Finset.sum_ite_mem]

/-- **Few vertices lose many edges (real form).**  At most `r·|B|·Δ/ζ` vertices lose more than `ζ`
edges when the edges meeting `B` are deleted. -/
theorem card_heavyLoss_le_real {K : Finset (Finset V)} {r : ℕ} (hr : IsUniform K r) {Δ : ℝ}
    (hΔ : ∀ x : V, (degree K x : ℝ) ≤ Δ) (B : Finset V) (ζ : ℝ) :
    (((Finset.univ : Finset V).filter (fun v => ζ < (lostDegree K B v : ℝ))).card : ℝ) * ζ
      ≤ (r : ℝ) * ((B.card : ℝ) * Δ) := by
  classical
  set T := (Finset.univ : Finset V).filter (fun v => ζ < (lostDegree K B v : ℝ)) with hT
  have hstep1 : (T.card : ℝ) * ζ ≤ ∑ v ∈ T, (lostDegree K B v : ℝ) := by
    calc (T.card : ℝ) * ζ = ∑ _v ∈ T, ζ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ T, (lostDegree K B v : ℝ) :=
        Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2.le)
  have hstep2 : ∑ v ∈ T, (lostDegree K B v : ℝ) ≤ ∑ v : V, (lostDegree K B v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => Nat.cast_nonneg _)
  have hstep3 : (∑ v : V, (lostDegree K B v : ℝ))
      = ((∑ e ∈ K.filter (fun e => ¬ Disjoint e B), e.card : ℕ) : ℝ) := by
    rw [← sum_lostDegree_eq]
    push_cast
    rfl
  have hstep4 : ((∑ e ∈ K.filter (fun e => ¬ Disjoint e B), e.card : ℕ) : ℝ)
      = (r : ℝ) * ((K.filter (fun e => ¬ Disjoint e B)).card : ℝ) := by
    have : ∑ e ∈ K.filter (fun e => ¬ Disjoint e B), e.card
        = (K.filter (fun e => ¬ Disjoint e B)).card * r := by
      rw [Finset.sum_congr rfl (fun e he => hr e (Finset.mem_of_mem_filter e he)),
        Finset.sum_const, smul_eq_mul]
    rw [this]; push_cast; ring
  have hstep5 : ((K.filter (fun e => ¬ Disjoint e B)).card : ℝ) ≤ (B.card : ℝ) * Δ := by
    have h1 : ((K.filter (fun e => ¬ Disjoint e B)).card : ℝ) ≤
        ((∑ x ∈ B, degree K x : ℕ) : ℝ) := by
      exact_mod_cast card_edges_meeting_le_sum B
    have h2 : ((∑ x ∈ B, degree K x : ℕ) : ℝ) ≤ (B.card : ℝ) * Δ := by
      push_cast
      calc ∑ x ∈ B, (degree K x : ℝ) ≤ ∑ _x ∈ B, Δ := Finset.sum_le_sum (fun x _ => hΔ x)
        _ = (B.card : ℝ) * Δ := by rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  calc (T.card : ℝ) * ζ ≤ ∑ v : V, (lostDegree K B v : ℝ) := le_trans hstep1 hstep2
    _ = (r : ℝ) * ((K.filter (fun e => ¬ Disjoint e B)).card : ℝ) := by rw [hstep3, hstep4]
    _ ≤ (r : ℝ) * ((B.card : ℝ) * Δ) := mul_le_mul_of_nonneg_left hstep5 hr0

/-- **Few vertices lose many edges (ratio form).**  If `r·Δ = psi·ζ` then at most `psi·|B|` vertices
lose more than `ζ` edges when the edges meeting `B` are deleted. -/
theorem card_heavyLoss_le_ratio {K : Finset (Finset V)} {r : ℕ} (hr : IsUniform K r) {Δ ζ psi : ℝ}
    (hΔ : ∀ x : V, (degree K x : ℝ) ≤ Δ) (hζ : 0 < ζ) (hratio : (r : ℝ) * Δ = psi * ζ)
    (B : Finset V) :
    ((((Finset.univ : Finset V).filter (fun v => ζ < (lostDegree K B v : ℝ))).card : ℝ))
      ≤ psi * (B.card : ℝ) := by
  refine le_of_mul_le_mul_right ?_ hζ
  refine le_trans (card_heavyLoss_le_real hr hΔ B ζ) (le_of_eq ?_)
  rw [show (r : ℝ) * ((B.card : ℝ) * Δ) = ((r : ℝ) * Δ) * (B.card : ℝ) by ring, hratio]
  ring

omit [Fintype V] in
/-- The cardinality of a five-fold union, in real form. -/
theorem card_union_five_le (A B C D E : Finset V) :
    (((A ∪ B ∪ C ∪ D ∪ E).card : ℝ))
      ≤ (A.card : ℝ) + (B.card : ℝ) + (C.card : ℝ) + (D.card : ℝ) + (E.card : ℝ) := by
  have hn : (A ∪ B ∪ C ∪ D ∪ E).card ≤ A.card + B.card + C.card + D.card + E.card := by
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
    exact Finset.card_union_le _ _
  exact_mod_cast hn

/-- The complement of `S ∪ E` is at least as large as `|V| − |S| − |E|`. -/
theorem card_compl_union_ge (S E : Finset V) :
    (Fintype.card V : ℝ) - (S.card : ℝ) - (E.card : ℝ) ≤ (((S ∪ E)ᶜ).card : ℝ) := by
  classical
  have hle : (S ∪ E).card ≤ Fintype.card V := Finset.card_le_univ _
  have hunion : ((S ∪ E).card : ℝ) ≤ (S.card : ℝ) + (E.card : ℝ) := by
    exact_mod_cast Finset.card_union_le S E
  have hcompl : (((S ∪ E)ᶜ).card : ℝ) = (Fintype.card V : ℝ) - ((S ∪ E).card : ℝ) := by
    rw [Finset.card_compl]
    push_cast [Nat.cast_sub hle]
    ring
  rw [hcompl]
  linarith

/-- **The ceiling of the next round.** The drop requested by
`LeanPool.AsymptoticTrianglePacking.Internal.TightParams.step_hi`, at the
absolute scale `d` and with an actual loss `l` below the tolerance `εγ·d·hi`, still lands below
`d·hi₁`. -/
theorem tight_ceiling_step_bound {a gam eps lo hi hi1 d l : ℝ}
    (hd : 0 < d) (hhi0 : 0 < hi) (ha0 : 0 ≤ a) (hgam0 : 0 ≤ gam) (hg1 : 0 ≤ 1 - gam)
    (hlo0 : 0 ≤ lo) (hl : l ≤ eps * gam * (d * hi))
    (hstep : hi - a * gam * (lo - eps * gam * hi) * lo * (1 - gam) / hi + eps * gam * hi ≤ hi1) :
    d * hi - a * gam * (d * lo - l) * (d * lo) * (1 - gam) / (d * hi) + eps * gam * (d * hi)
      ≤ d * hi1 := by
  have hDhi : (0 : ℝ) < d * hi := mul_pos hd hhi0
  have hfac : (0 : ℝ) ≤ a * gam * (d * lo) * (1 - gam) / (d * hi) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha0 hgam0) (mul_nonneg hd.le hlo0)) hg1)
      hDhi.le
  have hmono : a * gam * (d * lo - eps * gam * (d * hi)) * (d * lo) * (1 - gam) / (d * hi)
      ≤ a * gam * (d * lo - l) * (d * lo) * (1 - gam) / (d * hi) := by
    have e1 : a * gam * (d * lo - eps * gam * (d * hi)) * (d * lo) * (1 - gam) / (d * hi)
        = (a * gam * (d * lo) * (1 - gam) / (d * hi)) * (d * lo - eps * gam * (d * hi)) := by
      ring
    have e2 : a * gam * (d * lo - l) * (d * lo) * (1 - gam) / (d * hi)
        = (a * gam * (d * lo) * (1 - gam) / (d * hi)) * (d * lo - l) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (by linarith) hfac
  have heq : a * gam * (d * lo - eps * gam * (d * hi)) * (d * lo) * (1 - gam) / (d * hi)
      = d * (a * gam * (lo - eps * gam * hi) * lo * (1 - gam) / hi) := by
    field_simp
  have hsd : d * (hi - a * gam * (lo - eps * gam * hi) * lo * (1 - gam) / hi + eps * gam * hi)
      ≤ d * hi1 := mul_le_mul_of_nonneg_left hstep hd.le
  linarith only [hmono, heq, hsd]

/-- **Vertex count from the codegree bound.**  A vertex of degree `D` forces
`(r−1)·D ≤ (|V| − 1)·κ`. -/
theorem card_ge_of_codegree {K : Finset (Finset V)} {r : ℕ} (hr : IsUniform K r) (hr1 : 1 ≤ r)
    {κ : ℝ} (hκ : ∀ x y : V, x ≠ y → (codegree K x y : ℝ) ≤ κ) (v : V) :
    ((r : ℝ) - 1) * (degree K v : ℝ) ≤ ((Fintype.card V : ℝ) - 1) * κ := by
  classical
  have hsum : ∑ u ∈ (Finset.univ : Finset V).erase v, codegree K v u = (r - 1) * degree K v :=
    sum_codegree_erase_eq hr v
  have hsumR : ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree K v u : ℝ)
      = ((r : ℝ) - 1) * (degree K v : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hsum
    push_cast [Nat.cast_sub hr1] at h
    simpa using h
  have hle : ∀ u ∈ (Finset.univ : Finset V).erase v, (codegree K v u : ℝ) ≤ κ := by
    intro u hu
    exact hκ v u (fun h => (Finset.mem_erase.mp hu).1 h.symm)
  have hcardV : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hcard : (((Finset.univ : Finset V).erase v).card : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
    push_cast [Nat.cast_sub hcardV]
    ring
  calc ((r : ℝ) - 1) * (degree K v : ℝ)
      = ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree K v u : ℝ) := hsumR.symm
    _ ≤ ∑ _u ∈ (Finset.univ : Finset V).erase v, κ := Finset.sum_le_sum hle
    _ = (((Finset.univ : Finset V).erase v).card : ℝ) * κ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Fintype.card V : ℝ) - 1) * κ := by rw [hcard]

/-- The arithmetic of the exceptional budget: the new exceptional set is the old one (`e`) plus the
vertices that left the band (`b`), plus those heavily damaged by the old exceptional set (`h`), plus
those breaking the new ceiling (`hh ≤ e + b + h`), plus those damaged by pruning the latter
(`dm ≤ psi·hh`); the total is at most `(2 + psi)²(e + b)`. -/
theorem budget_arith {e b h hh dm tot psi sigj exc sig1 N : ℝ}
    (hpsi0 : 0 ≤ psi) (he : 0 ≤ e) (hb : 0 ≤ b)
    (htot : tot ≤ e + b + h + hh + dm)
    (h1 : h ≤ psi * e) (h2 : hh ≤ e + b + h) (h3 : dm ≤ psi * hh)
    (hEB : e + b ≤ (sigj + exc) * N) (hN : 0 ≤ N)
    (hstep : (2 + psi) ^ 2 * (sigj + exc) ≤ sig1) :
    tot ≤ sig1 * N := by
  have hs : (0 : ℝ) ≤ e + b := by linarith
  have hps : (0 : ℝ) ≤ psi * (e + b) := mul_nonneg hpsi0 hs
  have g1 : h ≤ psi * (e + b) := by nlinarith [mul_nonneg hpsi0 hb]
  have g2 : hh ≤ (1 + psi) * (e + b) := by nlinarith
  have g3 : dm ≤ psi * ((1 + psi) * (e + b)) := by nlinarith
  have g4 : tot ≤ (2 + psi) ^ 2 * (e + b) := by nlinarith
  have g5 : (2 + psi) ^ 2 * (e + b) ≤ (2 + psi) ^ 2 * ((sigj + exc) * N) :=
    mul_le_mul_of_nonneg_left hEB (sq_nonneg _)
  nlinarith only [g4, g5, hstep, hN]

/-! ## One round of the schedule -/

/-- **One round of the tight-band schedule.**  From the invariant at stage `j` — an `r`-uniform
sub-hypergraph `K` avoiding the covered set `S`, with global degree ceiling `d·hi j`, degree floor
`d·lo j` off the exceptional set `E`, codegrees `≤ κ` and `|E| ≤ sig j·|V|` — one sharp round
produces a retained set covering a `γ/(16r)` fraction of the uncovered vertices and re-establishes
the invariant at stage `j+1`. -/
theorem tight_round_step {r : ℕ} (hr : 2 ≤ r) {β : ℝ} (Pm : TightParams r β)
    {D₀ c₀ : ℝ} (hc₀ : 0 ≤ c₀) (hround : SharpRoundFor r Pm.gam Pm.eps Pm.exc (β / 2) D₀ c₀)
    {W : Type} [Fintype W] [DecidableEq W]
    {d κ : ℝ} (hd : 0 < d) (hκ0 : 0 ≤ κ)
    (hDlo : D₀ ≤ d * Pm.lomin) (hcodsmall : κ ≤ c₀ * (d * Pm.lomin))
    (hNbig : D₀ ≤ (Fintype.card W : ℝ))
    {j : ℕ} (hj : j < Pm.T)
    {K : Finset (Finset W)} {S E : Finset W}
    (huni : IsUniform K r)
    (hSdisj : ∀ e ∈ K, Disjoint e S)
    (hhi : ∀ v : W, (degree K v : ℝ) ≤ d * Pm.hi j)
    (hlo : ∀ v : W, v ∉ S → v ∉ E → d * Pm.lo j ≤ (degree K v : ℝ))
    (hcodeg : ∀ x y : W, x ≠ y → (codegree K x y : ℝ) ≤ κ)
    (hE : (E.card : ℝ) ≤ Pm.sig j * (Fintype.card W : ℝ))
    (huncov : β * (Fintype.card W : ℝ) < (Fintype.card W : ℝ) - (S.card : ℝ)) :
    ∃ R' : Finset (Finset W), R' ⊆ K ∧
      Pm.gam / (16 * r) * ((Fintype.card W : ℝ) - (S.card : ℝ)) ≤ ((covered R').card : ℝ) ∧
      ∃ (K' : Finset (Finset W)) (E' : Finset W),
        K' ⊆ Hypergraph.residual K R' ∧ IsUniform K' r ∧
        (∀ e ∈ K', Disjoint e (S ∪ covered R')) ∧
        (∀ v : W, (degree K' v : ℝ) ≤ d * Pm.hi (j + 1)) ∧
        (∀ v : W, v ∉ S ∪ covered R' → v ∉ E' → d * Pm.lo (j + 1) ≤ (degree K' v : ℝ)) ∧
        (∀ x y : W, x ≠ y → (codegree K' x y : ℝ) ≤ κ) ∧
        (E'.card : ℝ) ≤ Pm.sig (j + 1) * (Fintype.card W : ℝ) := by
  classical
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hjT : j ≤ Pm.T := le_of_lt hj
  have hj1T : j + 1 ≤ Pm.T := hj
  have hlo_pos : 0 < Pm.lo j := lt_of_lt_of_le Pm.lomin_pos (Pm.lomin_le j hjT)
  have hhi_pos : 0 < Pm.hi j := lt_of_lt_of_le hlo_pos (Pm.lo_le_hi j hjT)
  have hlo1_pos : 0 < Pm.lo (j + 1) := lt_of_lt_of_le Pm.lomin_pos (Pm.lomin_le (j + 1) hj1T)
  have hhi1_pos : 0 < Pm.hi (j + 1) := lt_of_lt_of_le hlo1_pos (Pm.lo_le_hi (j + 1) hj1T)
  have hgam := Pm.gam_pos
  have heps := Pm.eps_pos
  set N : ℝ := (Fintype.card W : ℝ) with hNdef
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  set A : Finset W := (S ∪ E)ᶜ with hAdef
  -- the live set is large
  have hAcard : N - (S.card : ℝ) - (E.card : ℝ) ≤ (A.card : ℝ) := card_compl_union_ge S E
  have hsigj : Pm.sig j ≤ β / 2 := Pm.sig_le j hjT
  have hEsmall : (E.card : ℝ) ≤ β / 2 * N := by
    refine le_trans hE ?_
    exact mul_le_mul_of_nonneg_right hsigj hN0
  have hAhalf : ((Fintype.card W : ℝ) - (S.card : ℝ)) / 2 ≤ (A.card : ℝ) := by linarith
  have hAbig : β / 2 * N ≤ (A.card : ℝ) := by linarith
  -- apply the sharp round
  have hlo' : ∀ v ∈ A, d * Pm.lo j ≤ (degree K v : ℝ) := by
    intro v hv
    rw [hAdef, Finset.mem_compl, Finset.mem_union] at hv
    push Not at hv
    exact hlo v hv.1 hv.2
  have hlomin_le_hi : Pm.lomin ≤ Pm.hi j := le_trans (Pm.lomin_le j hjT) (Pm.lo_le_hi j hjT)
  have hDΔ : D₀ ≤ d * Pm.hi j :=
    le_trans hDlo (mul_le_mul_of_nonneg_left hlomin_le_hi hd.le)
  have hcκ : κ ≤ c₀ * (d * Pm.hi j) :=
    le_trans hcodsmall (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hlomin_le_hi hd.le) hc₀)
  have h2δ : d * Pm.hi j ≤ 2 * (d * Pm.lo j) := by
    have hh2 := Pm.hi_le_two_lo j hjT
    linarith only [mul_le_mul_of_nonneg_left hh2 hd.le]
  obtain ⟨R', hR'K, B, hBcard, hband, hcov⟩ :=
    hround K A (d * Pm.lo j) (d * Pm.hi j) κ huni hhi hlo' hcodeg hκ0 hcκ hDΔ h2δ hNbig hAbig
  refine ⟨R', hR'K, ?_, ?_⟩
  · -- the covering bound
    have hfrac : 0 ≤ Pm.gam / (8 * (r : ℝ)) := by positivity
    have h1 : Pm.gam / (8 * (r : ℝ)) * (((Fintype.card W : ℝ) - (S.card : ℝ)) / 2)
        ≤ Pm.gam / (8 * (r : ℝ)) * (A.card : ℝ) := mul_le_mul_of_nonneg_left hAhalf hfrac
    have h2 : Pm.gam / (16 * (r : ℝ)) * ((Fintype.card W : ℝ) - (S.card : ℝ))
        = Pm.gam / (8 * (r : ℝ)) * (((Fintype.card W : ℝ) - (S.card : ℝ)) / 2) := by
      field_simp
      ring
    rw [h2]
    linarith [hcov]
  -- the new invariant
  set ζ : ℝ := Pm.eps * Pm.gam * (d * Pm.hi j) with hζdef
  have hζpos : 0 < ζ := by rw [hζdef]; positivity
  set Kres : Finset (Finset W) := Hypergraph.residual K R' with hKresdef
  have hKresK : Kres ⊆ K := Hypergraph.residual_subset K R'
  have hKreshi : ∀ v : W, (degree Kres v : ℝ) ≤ d * Pm.hi j := by
    intro v
    exact le_trans (by exact_mod_cast degree_mono hKresK v) (hhi v)
  set heavy : Finset W :=
    (Finset.univ : Finset W).filter (fun v => ζ < (lostDegree K E v : ℝ)) with hheavydef
  set Hi : Finset W :=
    (Finset.univ : Finset W).filter (fun v => d * Pm.hi (j + 1) < (degree Kres v : ℝ)) with hHidef
  set K' : Finset (Finset W) := prune Kres Hi with hK'def
  set Dam : Finset W :=
    (Finset.univ : Finset W).filter (fun v => ζ < (lostDegree Kres Hi v : ℝ)) with hDamdef
  have hDhi : (0 : ℝ) < d * Pm.hi j := by positivity
  have hr1' : (0 : ℝ) ≤ (r : ℝ) - 1 := by linarith
  have hg1 : (0 : ℝ) ≤ 1 - Pm.gam := by linarith only [Pm.gam_le]
  have hKres0 : ∀ v : W, v ∈ S ∪ covered R' → degree Kres v = 0 := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · have h0 : degree K v = 0 := degree_eq_zero_of_disjoint hSdisj h
      have := degree_mono hKresK v
      omega
    · exact degree_eq_zero_of_disjoint
        (fun e he => Hypergraph.residual_disjoint_covered he) h
  -- every vertex breaking the new ceiling is exceptional, badly-banded, or heavily damaged
  have hHisub : Hi ⊆ E ∪ B ∪ heavy := by
    intro v hvHi
    have hdeg : d * Pm.hi (j + 1) < (degree Kres v : ℝ) := (Finset.mem_filter.mp hvHi).2
    have hpos1 : (0 : ℝ) < d * Pm.hi (j + 1) := by positivity
    by_contra hc
    simp only [Finset.mem_union, not_or] at hc
    obtain ⟨⟨hvE, hvB⟩, hvheavy⟩ := hc
    have hvS : v ∉ S := by
      intro h
      rw [hKres0 v (Finset.mem_union_left _ h)] at hdeg
      simp only [Nat.cast_zero] at hdeg
      linarith
    have hvcov : v ∉ covered R' := by
      intro h
      rw [hKres0 v (Finset.mem_union_right _ h)] at hdeg
      simp only [Nat.cast_zero] at hdeg
      linarith
    have hvA : v ∈ A := by
      rw [hAdef, Finset.mem_compl, Finset.mem_union]
      push Not
      exact ⟨hvS, hvE⟩
    obtain ⟨_, hup⟩ := hband v hvA hvB hvcov
    have hlostA : (lostDegree K Aᶜ v : ℝ) = (lostDegree K E v : ℝ) := by
      rw [hAdef, compl_compl, lostDegree_union_of_disjoint hSdisj]
    rw [hlostA] at hup
    have hlostle : (lostDegree K E v : ℝ) ≤ Pm.eps * Pm.gam * (d * Pm.hi j) := by
      by_contra hcc
      push Not at hcc
      exact hvheavy (Finset.mem_filter.mpr ⟨Finset.mem_univ v, by rw [hζdef]; exact hcc⟩)
    have hbound := tight_ceiling_step_bound (a := ((r : ℝ) - 1) / r) hd hhi_pos
      (div_nonneg hr1' hrpos.le) hgam.le hg1 hlo_pos.le hlostle (Pm.step_hi j hj)
    linarith only [hdeg, hup, hbound]
  refine ⟨K', E ∪ B ∪ heavy ∪ Hi ∪ Dam, Finset.filter_subset _ _,
    fun e he => huni e (hKresK (Finset.mem_of_mem_filter e he)), ?_, ?_, ?_, ?_, ?_⟩
  · -- edges avoid the new covered set
    intro e he
    have heK : e ∈ Kres := Finset.mem_of_mem_filter e he
    rw [Finset.disjoint_union_right]
    exact ⟨hSdisj e (hKresK heK), Hypergraph.residual_disjoint_covered heK⟩
  · -- the new ceiling
    intro v
    by_cases hv : v ∈ Hi
    · rw [hK'def, degree_prune_eq_zero hv]
      push_cast
      positivity
    · have h1 : (degree K' v : ℝ) ≤ (degree Kres v : ℝ) := by
        exact_mod_cast degree_mono (Finset.filter_subset _ _) v
      have h2 : ¬ (d * Pm.hi (j + 1) < (degree Kres v : ℝ)) := by
        intro hlt
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hlt⟩)
      push Not at h2
      linarith
  · -- the new floor
    intro v hvS hvE'
    simp only [Finset.mem_union, not_or] at hvS hvE'
    obtain ⟨⟨⟨⟨hvE, hvB⟩, hvheavy⟩, _hvHi⟩, hvDam⟩ := hvE'
    have hvA : v ∈ A := by
      rw [hAdef, Finset.mem_compl, Finset.mem_union]
      push Not
      exact ⟨hvS.1, hvE⟩
    obtain ⟨hlow, _⟩ := hband v hvA hvB hvS.2
    have hdrop : (degree Kres v : ℝ) ≤ (degree K' v : ℝ) + (lostDegree Kres Hi v : ℝ) := by
      exact_mod_cast degree_prune_ge Hi v
    have hlost : (lostDegree Kres Hi v : ℝ) ≤ ζ := by
      by_contra hc
      push Not at hc
      exact hvDam (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
    have hstep := Pm.step_lo j hj
    have hkey : d * Pm.lo (j + 1)
        ≤ d * Pm.lo j - ((r : ℝ) - 1) / r * Pm.gam * (d * Pm.hi j)
          - Pm.eps * Pm.gam * (d * Pm.hi j) - ζ := by
      rw [hζdef]
      linarith only [mul_le_mul_of_nonneg_left hstep hd.le]
    linarith
  · -- codegrees only decrease
    intro x y hxy
    refine le_trans ?_ (hcodeg x y hxy)
    exact_mod_cast codegree_mono
      (Finset.Subset.trans (Finset.filter_subset _ _) hKresK) x y
  · -- the exceptional budget
    obtain ⟨psi, hpsidef⟩ : ∃ p : ℝ, p = (r : ℝ) / (Pm.eps * Pm.gam) := ⟨_, rfl⟩
    have hpsi0 : (0 : ℝ) ≤ psi := by rw [hpsidef]; positivity
    have hratio : (r : ℝ) * (d * Pm.hi j) = psi * ζ := by
      rw [hpsidef, hζdef]; field_simp
    have hheavy_le : (heavy.card : ℝ) ≤ psi * (E.card : ℝ) :=
      card_heavyLoss_le_ratio huni hhi hζpos hratio E
    have hDam_le : (Dam.card : ℝ) ≤ psi * (Hi.card : ℝ) :=
      card_heavyLoss_le_ratio (fun e he => huni e (hKresK he)) hKreshi hζpos hratio Hi
    have hHi_le : (Hi.card : ℝ) ≤ (E.card : ℝ) + (B.card : ℝ) + (heavy.card : ℝ) := by
      have h1 : Hi.card ≤ (E ∪ B ∪ heavy).card := Finset.card_le_card hHisub
      have h2 : (E ∪ B ∪ heavy).card ≤ E.card + B.card + heavy.card :=
        le_trans (Finset.card_union_le _ _)
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      have : Hi.card ≤ E.card + B.card + heavy.card := le_trans h1 h2
      exact_mod_cast this
    have hunion : ((E ∪ B ∪ heavy ∪ Hi ∪ Dam).card : ℝ)
        ≤ (E.card : ℝ) + (B.card : ℝ) + (heavy.card : ℝ) + (Hi.card : ℝ) + (Dam.card : ℝ) :=
      card_union_five_le E B heavy Hi Dam
    -- the total is at most `(2 + psi)^2` times the fresh exceptional mass
    have hEB : (E.card : ℝ) + (B.card : ℝ) ≤ (Pm.sig j + Pm.exc) * N := by
      have hb : (B.card : ℝ) ≤ Pm.exc * N := hBcard
      linarith only [hE, hb]
    have hEnn : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg _
    have hBnn : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
    have hstepsig : (2 + psi) ^ 2 * (Pm.sig j + Pm.exc) ≤ Pm.sig (j + 1) := by
      rw [hpsidef]; exact Pm.sig_step j hj
    exact budget_arith hpsi0 hEnn hBnn hunion hheavy_le hHi_le hDam_le hEB hN0 hstepsig

end LeanPool.AsymptoticTrianglePacking.Internal
