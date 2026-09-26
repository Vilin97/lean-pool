/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.AHL.AHLAmGm

/-!
# The SUM (vertex-ball) Moore refutation — the band-discharge spine (B1–B3)

This file lands the SUM (vertex-ball) sharpening of the Alon–Hoory–Linial irregular Moore bound
(nodes B1–B3 of the band discharge), the spine of the `hStarved55` discharge on `64 ≤ n ≤ 387`.
It composes the landed AM–GM walk-count lower bound (`nb_amgm_lambda`,
`lambda_ge`) with a new *ball* injectivity: at girth `> 2ℓ` the endpoints of all non-backtracking
walks of length `1..ℓ` from a fixed start are pairwise distinct and differ from the start.  Writing
`n = Fintype.card V` and `D = ∑ v, G.degree v`, the ball form
`D · Σ_{k<ℓ} (D − n)^k n^(ℓ−1−k) ≤ n^ℓ (n − 1)` keeps the whole Moore ball (not just the top level),
buying the extra half-level over the pair form `ahl_irregular_moore`.

## Contents

* **`nb_walk_isPath_of_girth_sharp`** (B1) — the *sharp* NB-path lemma: girth `> r` (not `2r + 1`)
  already forces every non-backtracking walk of length `≤ r` to be a path.  The landed induction
  only ever closes a cycle of length `≤ r`, so the weaker hypothesis suffices.
* **`nb_ball_injectivity`** (B2) — the vertex-ball injectivity: at girth `> 2ℓ`,
  `Σ_{k ∈ Icc 1 ℓ} nbTotalWalks G k ≤ n·(n − 1)`.  Per start `x`, the endpoint map on all NB walks
  of length `1..ℓ` is injective into `univ.erase x`.
* **`ahl_ball_moore`** (B3) — the SUM Moore bound
  `D · Σ_{k<ℓ} (D − n)^k n^(ℓ−1−k) ≤ n^ℓ (n − 1)`; and its girth-side contrapositive
  **`ahl_ball_girth_bound`** (`n^ℓ(n − 1) < D · Σ … ⟹ ∃ cycle ≤ 2ℓ`), the form the band
  arithmetic instantiates at the extremal `V₉/2`-core.
-/

public section

namespace ACMax

open SimpleGraph Finset

/-- **B1 — the sharp non-backtracking path lemma.**  In a graph with no cycle of length `≤ r`, every
non-backtracking walk of length `≤ r` is a path.  This sharpens the landed
`nb_walk_isPath_of_girth` (which demands girth `> 2r + 1`): peeling the first edge, the tail is a
non-backtracking walk of length `≤ r`, hence a path by induction; a revisit of the start supplies
two distinct paths closing a cycle of length `≤ r`, contradicting the hypothesis. -/
theorem nb_walk_isPath_of_girth_sharp {V : Type*} (G : SimpleGraph V) {r : ℕ}
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → r < c.length) :
    ∀ {x y : V} (w : G.Walk x y), IsNonBacktracking w → w.length ≤ r → w.IsPath := by
  classical
  intro x y w
  induction w with
  | nil => intro _ _; exact Walk.IsPath.nil
  | @cons a b c h p ih =>
    intro hnb hlen
    have hnbp : IsNonBacktracking p := by
      intro i hi
      rw [← Walk.getVert_cons_succ p h (n := i + 2), ← Walk.getVert_cons_succ p h (n := i)]
      exact hnb (i + 1) (by rw [Walk.length_cons]; omega)
    have hlenp : p.length ≤ r := by rw [Walk.length_cons] at hlen; omega
    have hp : p.IsPath := ih hnbp hlenp
    rw [Walk.cons_isPath_iff]
    refine ⟨hp, ?_⟩
    intro hx
    set Q := p.takeUntil a hx with hQdef
    have hQ : Q.IsPath := hp.takeUntil hx
    have hQle : Q.length ≤ p.length := p.length_takeUntil_le_length hx
    have hQlen_ne : Q.length ≠ 1 := by
      intro hQ1
      have hple : (1 : ℕ) ≤ p.length := by omega
      have hval : p.getVert Q.length = a := p.getVert_length_takeUntil hx
      rw [hQ1] at hval
      have hnb0 := hnb 0 (by rw [Walk.length_cons]; omega)
      rw [Walk.getVert_zero] at hnb0
      apply hnb0
      rw [show (0 : ℕ) + 2 = 1 + 1 by rfl, Walk.getVert_cons_succ, hval]
    set E := Walk.cons h.symm Walk.nil with hEdef
    have hE : E.IsPath := by
      rw [hEdef, Walk.cons_isPath_iff]
      exact ⟨Walk.IsPath.nil, by simp [h.symm.ne]⟩
    have hElen : E.length = 1 := by rw [hEdef]; simp
    have hne : Q ≠ E := by
      intro heq
      apply hQlen_ne
      rw [heq, hElen]
    obtain ⟨w', -, -, c, hc, hcl⟩ := hQ.exists_isCycle_length_le_add_of_ne hE hne
    have hgc := hg w' c hc
    rw [hElen] at hcl
    rw [Walk.length_cons] at hlen
    omega

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
  {ℓ : ℕ}

/-- **B2 — the vertex-ball injectivity.**  If there is no cycle of length `≤ 2ℓ`, then the total
number of non-backtracking walks of length `1..ℓ` is at most `n·(n − 1)`.  For each start `x`, the
endpoint map on the disjoint union of `nbWalksFrom G x k` (`k ∈ Icc 1 ℓ`) is injective into
`univ.erase x`: two walks with a common endpoint `v` are paths (B1), and if distinct they close a
cycle of length `≤ 2ℓ`; a walk returning to `x` would be a positive-length closed path,
impossible. -/
theorem nb_ball_injectivity
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * ℓ < c.length) :
    ∑ k ∈ Finset.Icc 1 ℓ, nbTotalWalks G k ≤ Fintype.card V * (Fintype.card V - 1) := by
  have hnt : ∀ k, nbTotalWalks G k = ∑ x : V, (nbWalksFrom G x k).card := fun k => by
    rw [nbTotalWalks]; exact Finset.sum_congr rfl fun x _ => (card_nbWalksFrom x k).symm
  have hLHS : ∑ k ∈ Finset.Icc 1 ℓ, nbTotalWalks G k
      = ∑ x : V, ∑ k ∈ Finset.Icc 1 ℓ, (nbWalksFrom G x k).card := by
    rw [Finset.sum_congr rfl (fun k _ => hnt k), Finset.sum_comm]
  rw [hLHS]
  have hball : ∀ x : V, (∑ k ∈ Finset.Icc 1 ℓ, (nbWalksFrom G x k).card)
      ≤ Fintype.card V - 1 := by
    intro x
    have hdisj : (↑(Finset.Icc 1 ℓ) : Set ℕ).PairwiseDisjoint (fun k => nbWalksFrom G x k) := by
      intro j _ k _ hjk
      refine Finset.disjoint_left.mpr fun s hsj hsk => ?_
      rw [mem_nbWalksFrom] at hsj hsk
      exact hjk (hsj.1.symm.trans hsk.1)
    have hcardU : ((Finset.Icc 1 ℓ).biUnion (fun k => nbWalksFrom G x k)).card
        = ∑ k ∈ Finset.Icc 1 ℓ, (nbWalksFrom G x k).card := Finset.card_biUnion hdisj
    rw [← hcardU]
    have hmaps : ∀ s ∈ (Finset.Icc 1 ℓ).biUnion (fun k => nbWalksFrom G x k),
        (fun s : Σ v : V, G.Walk x v => s.1) s ∈ Finset.univ.erase x := by
      intro s hs
      rw [Finset.mem_biUnion] at hs
      obtain ⟨k, hk, hsk⟩ := hs
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      rw [mem_nbWalksFrom] at hsk
      obtain ⟨hswl, hswnb⟩ := hsk
      change s.1 ∈ Finset.univ.erase x
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro hvx
      have hpath : s.2.IsPath :=
        nb_walk_isPath_of_girth_sharp (r := s.2.length) G
          (fun u c hc => by have := hg u c hc; omega) s.2 hswnb le_rfl
      have h0 : s.2.getVert 0 = x := s.2.getVert_zero
      have hLv : s.2.getVert s.2.length = s.1 := s.2.getVert_length
      have hcontra : (0 : ℕ) = s.2.length :=
        hpath.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; omega) (by rw [h0, hLv, hvx])
      omega
    have hinj : Set.InjOn (fun s : Σ v : V, G.Walk x v => s.1)
        ↑((Finset.Icc 1 ℓ).biUnion (fun k => nbWalksFrom G x k)) := by
      intro s hs t ht hst
      rw [Finset.mem_coe, Finset.mem_biUnion] at hs ht
      obtain ⟨j, hj, hsj⟩ := hs
      obtain ⟨k, hk, htk⟩ := ht
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      rw [mem_nbWalksFrom] at hsj htk
      obtain ⟨hswl, hswnb⟩ := hsj
      obtain ⟨htwl, htwnb⟩ := htk
      obtain ⟨sv, sw⟩ := s
      obtain ⟨tv, tw⟩ := t
      change sw.length = j at hswl
      change IsNonBacktracking sw at hswnb
      change tw.length = k at htwl
      change IsNonBacktracking tw at htwnb
      change sv = tv at hst
      subst hst
      have hpsw : sw.IsPath :=
        nb_walk_isPath_of_girth_sharp (r := sw.length) G
          (fun u c hc => by have := hg u c hc; omega) sw hswnb le_rfl
      have hptw : tw.IsPath :=
        nb_walk_isPath_of_girth_sharp (r := tw.length) G
          (fun u c hc => by have := hg u c hc; omega) tw htwnb le_rfl
      have hsweq : sw = tw := by
        by_contra hne
        obtain ⟨u, -, -, c, hc, hcl⟩ := hpsw.exists_isCycle_length_le_add_of_ne hptw hne
        have := hg u c hc
        omega
      rw [hsweq]
    calc ((Finset.Icc 1 ℓ).biUnion (fun k => nbWalksFrom G x k)).card
        ≤ (Finset.univ.erase x).card :=
          Finset.card_le_card_of_injOn (fun s : Σ v : V, G.Walk x v => s.1) hmaps hinj
      _ = Fintype.card V - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
  calc ∑ x : V, ∑ k ∈ Finset.Icc 1 ℓ, (nbWalksFrom G x k).card
      ≤ ∑ _x : V, (Fintype.card V - 1) := Finset.sum_le_sum fun x _ => hball x
    _ = Fintype.card V * (Fintype.card V - 1) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [DecidableEq V] in
/-- **B3 — the SUM Moore bound.**  Under `δ ≥ 2` (and `V` nonempty) with no cycle of length `≤ 2ℓ`
and `1 ≤ ℓ`, the whole Moore ball is captured:
`D · Σ_{k<ℓ} (D − n)^k n^(ℓ−1−k) ≤ n^ℓ (n − 1)`.  Per level `k`, the AM–GM lower bound
`D·((D − n)/n)^k ≤ m_{k+1}` (`lambda_ge`, `nb_amgm_lambda`) is scaled by `n^(ℓ−1)`; summing and
capping `Σ m_k ≤ n(n − 1)` (`nb_ball_injectivity`) gives the ℝ inequality, cast back to ℕ via
`n ≤ D`.  This keeps the lower Moore terms the pair form `ahl_irregular_moore` discards. -/
theorem ahl_ball_moore (hδ2 : ∀ v, 2 ≤ G.degree v) [Nonempty V] (hℓ : 1 ≤ ℓ)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * ℓ < c.length) :
    (∑ v, G.degree v) * ∑ k ∈ Finset.range ℓ,
        ((∑ v, G.degree v) - Fintype.card V) ^ k * (Fintype.card V) ^ (ℓ - 1 - k)
      ≤ (Fintype.card V) ^ ℓ * (Fintype.card V - 1) := by
  classical
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hn' : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hnn0 : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt hn'
  have hn1 : 1 ≤ Fintype.card V := hn
  have hnD : Fintype.card V ≤ ∑ v, G.degree v := by
    have h : ∑ _v : V, 1 ≤ ∑ v, G.degree v :=
      Finset.sum_le_sum fun v _ => by have := hδ2 v; omega
    simpa using h
  have hDge : (2 * Fintype.card V : ℝ) ≤ ∑ v, (G.degree v : ℝ) := by
    have h : ∑ _v : V, (2 : ℝ) ≤ ∑ v, (G.degree v : ℝ) :=
      Finset.sum_le_sum fun v _ => by exact_mod_cast hδ2 v
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using h
  have hDpos : 0 < ∑ v, (G.degree v : ℝ) := by linarith
  have hnpow : (Fintype.card V : ℝ) ^ ℓ
      = (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ (ℓ - 1) := by
    conv_lhs => rw [show ℓ = (ℓ - 1) + 1 from by omega]
    rw [pow_succ']
  have hcap : (∑ k ∈ Finset.range ℓ, (nbTotalWalks G (k + 1) : ℝ))
      ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
    have hb2 := nb_ball_injectivity (G := G) (ℓ := ℓ) hg
    have hreindex : (∑ k ∈ Finset.range ℓ, nbTotalWalks G (k + 1))
        = ∑ k ∈ Finset.Icc 1 ℓ, nbTotalWalks G k := by
      have hh : ∀ m, ∑ k ∈ Finset.Icc 1 m, nbTotalWalks G k
          = ∑ k ∈ Finset.range m, nbTotalWalks G (k + 1) := by
        intro m
        induction m with
        | zero => simp
        | succ p ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
      exact (hh ℓ).symm
    calc (∑ k ∈ Finset.range ℓ, (nbTotalWalks G (k + 1) : ℝ))
        = ((∑ k ∈ Finset.range ℓ, nbTotalWalks G (k + 1) : ℕ) : ℝ) := by push_cast; ring
      _ = ((∑ k ∈ Finset.Icc 1 ℓ, nbTotalWalks G k : ℕ) : ℝ) := by rw [hreindex]
      _ ≤ ((Fintype.card V * (Fintype.card V - 1) : ℕ) : ℝ) := by exact_mod_cast hb2
      _ = (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub hn1]; push_cast; ring
  have key : (∑ v, (G.degree v : ℝ)) *
      (∑ k ∈ Finset.range ℓ, ((∑ v, (G.degree v : ℝ)) - (Fintype.card V : ℝ)) ^ k
          * (Fintype.card V : ℝ) ^ (ℓ - 1 - k))
      ≤ (Fintype.card V : ℝ) ^ ℓ * ((Fintype.card V : ℝ) - 1) := by
    have hterm : ∀ k ∈ Finset.range ℓ,
        (∑ v, (G.degree v : ℝ)) * (((∑ v, (G.degree v : ℝ)) - (Fintype.card V : ℝ)) ^ k
            * (Fintype.card V : ℝ) ^ (ℓ - 1 - k))
        ≤ (nbTotalWalks G (k + 1) : ℝ) * (Fintype.card V : ℝ) ^ (ℓ - 1) := by
      intro k hk
      have hklt : k < ℓ := Finset.mem_range.mp hk
      have hbase : (0 : ℝ)
          ≤ ((∑ v, (G.degree v : ℝ)) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ) :=
        div_nonneg (by linarith) (le_of_lt hn')
      have hpow : (((∑ v, (G.degree v : ℝ)) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ)) ^ k
          ≤ (Lambda G) ^ k := pow_le_pow_left₀ hbase (lambda_ge hδ2 hn) k
      have hlam := nb_amgm_lambda (G := G) hδ2 (show 1 ≤ k + 1 by omega)
      rw [show ((↑(k + 1) : ℝ) - 1) = (↑k : ℝ) by push_cast; ring, Real.rpow_natCast] at hlam
      have h1 : (∑ v, (G.degree v : ℝ))
          * (((∑ v, (G.degree v : ℝ)) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ)) ^ k
          ≤ (nbTotalWalks G (k + 1) : ℝ) := by
        calc (∑ v, (G.degree v : ℝ))
              * (((∑ v, (G.degree v : ℝ)) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ)) ^ k
            ≤ (∑ v, (G.degree v : ℝ)) * (Lambda G) ^ k :=
                mul_le_mul_of_nonneg_left hpow (le_of_lt hDpos)
          _ ≤ (nbTotalWalks G (k + 1) : ℝ) := hlam
      have h2 := mul_le_mul_of_nonneg_right h1
        (show (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ (ℓ - 1) by positivity)
      have hrw : (∑ v, (G.degree v : ℝ))
            * (((∑ v, (G.degree v : ℝ)) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ)) ^ k
            * (Fintype.card V : ℝ) ^ (ℓ - 1)
          = (∑ v, (G.degree v : ℝ))
            * (((∑ v, (G.degree v : ℝ)) - (Fintype.card V : ℝ)) ^ k
              * (Fintype.card V : ℝ) ^ (ℓ - 1 - k)) := by
        have hsplit : (Fintype.card V : ℝ) ^ (ℓ - 1)
            = (Fintype.card V : ℝ) ^ k * (Fintype.card V : ℝ) ^ (ℓ - 1 - k) := by
          rw [← pow_add]; congr 1; omega
        rw [hsplit, div_pow]; field_simp
      rw [hrw] at h2
      exact h2
    calc (∑ v, (G.degree v : ℝ))
          * (∑ k ∈ Finset.range ℓ, ((∑ v, (G.degree v : ℝ)) - (Fintype.card V : ℝ)) ^ k
              * (Fintype.card V : ℝ) ^ (ℓ - 1 - k))
        = ∑ k ∈ Finset.range ℓ, (∑ v, (G.degree v : ℝ))
            * (((∑ v, (G.degree v : ℝ)) - (Fintype.card V : ℝ)) ^ k
              * (Fintype.card V : ℝ) ^ (ℓ - 1 - k)) := by rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range ℓ, (nbTotalWalks G (k + 1) : ℝ) * (Fintype.card V : ℝ) ^ (ℓ - 1) :=
          Finset.sum_le_sum hterm
      _ = (∑ k ∈ Finset.range ℓ, (nbTotalWalks G (k + 1) : ℝ)) * (Fintype.card V : ℝ) ^ (ℓ - 1) :=
        by
          rw [Finset.sum_mul]
      _ ≤ ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) * (Fintype.card V : ℝ) ^ (ℓ - 1) :=
          mul_le_mul_of_nonneg_right hcap (by positivity)
      _ = (Fintype.card V : ℝ) ^ ℓ * ((Fintype.card V : ℝ) - 1) := by rw [hnpow]; ring
  rw [show ((∑ v, (G.degree v : ℝ)) - (Fintype.card V : ℝ))
        = (((∑ v, G.degree v) - Fintype.card V : ℕ) : ℝ) from by
      rw [Nat.cast_sub hnD]; push_cast; ring] at key
  rw [show ((Fintype.card V : ℝ) - 1) = ((Fintype.card V - 1 : ℕ) : ℝ) from by
      rw [Nat.cast_sub hn1]; push_cast; ring] at key
  exact_mod_cast key

omit [DecidableEq V] in
/-- **B3 (contrapositive) — the SUM girth bound.**  Under `δ ≥ 2` (and `V` nonempty) with `1 ≤ ℓ`,
if `n^ℓ(n − 1) < D · Σ_{k<ℓ} (D − n)^k n^(ℓ−1−k)` then `G` contains a cycle of length `≤ 2ℓ`.  This
is the SUM refutation the band arithmetic instantiates: a failing ball inequality forces a short
cycle. -/
theorem ahl_ball_girth_bound (hδ2 : ∀ v, 2 ≤ G.degree v) [Nonempty V] (hℓ : 1 ≤ ℓ)
    (hbig : (Fintype.card V) ^ ℓ * (Fintype.card V - 1)
        < (∑ v, G.degree v) * ∑ k ∈ Finset.range ℓ,
            ((∑ v, G.degree v) - Fintype.card V) ^ k * (Fintype.card V) ^ (ℓ - 1 - k)) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length ≤ 2 * ℓ := by
  classical
  by_contra h
  have hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * ℓ < c.length := by
    intro v c hc
    by_contra hlen
    exact h ⟨v, c, hc, not_lt.mp hlen⟩
  exact absurd (ahl_ball_moore hδ2 hℓ hg) (not_le.mpr hbig)

end ACMax
