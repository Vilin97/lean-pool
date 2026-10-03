/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.ACMax.Counting.Moats
public import LeanPool.ACMax.Counting.ResidualInterface
public import LeanPool.ACMax.Counting.XBoundAssembly
public import LeanPool.ACMax.Reduction.Residual

/-!
# The starved-world census and the owner-choke rows

The pure-counting census of the *starved world* — the `e(M) = 0` stratum: a
never-firing graph on `Fin n` with `2(n−2)` edges, minimum degree `≥ 3`, and no
degree-3–degree-3 edge. Its degree-3 vertices are *twins* (all `M`-isolated), the
degree-4 vertices the *sea*, the degree-`≥ 4` vertices the *hubs*. The
contrapositive of the star-moat law caps twin-hoarding (`starved_cap`), and
feeding the caps into the twin-incidence total against the degree-excess ledger
`Σ_h(deg − 3) = n − 8` produces the census rows.

## Main results

* `starved_cap`, `hoarding_law`, `slots_law` — the cap and the two aggregate rows;
  the hoarding row gives the giant census `n_g ≤ 1` at `n ≤ 49`.
* `starved_owner_choke_35_49` — with the owner-choke `7·t₄ + 3X ≤ 4n − 32`, the
  `35 ≤ n ≤ 49` band dies by pure counting.
* `slots_law_sharp` — the per-`p` sharpened slots row `24 + 2X ≤ t₄ + p + h₆₊ + 4n_g`
  split along the honest per-heavy caps (`p` = saturated degree-5 hubs).
* `choke_count`, `p_choke_count`, `p_choke_row` — the owner-choke and its per-`p`
  sharpening `7·t₄ + 8·p + 3X + 32 ≤ 4n`, with the independence rows
  `owner_independence`, `owner_sat_independence`.
* `deco_edge_shared_twin_fires`, `sat_sat_independence`,
  `p_choke_row_unconditional` — the shared-twin decorated-edge moat (fires at
  `9·(deg u + deg v) ≤ n + 56`) discharging the last moat-provenance hypothesis.
-/

public section

namespace ACMax

open Finset

open Classical in
/-- **The starved cap** (contrapositive of `star_moat_fires`).  In a never-firing census world
(`m = 2(n−2)`, `δ ≥ 3`) a hub `h` under the cap horizon `9·deg h ≤ n + 15` owns at most
`deg h − 3` `M`-isolated twins: if it owned `deg h − 2`, that twin star would fire. -/
theorem starved_cap {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2) (h : Fin n) (hfire : 9 * G.degree h ≤ n + 15) :
    (G.neighborFinset h ∩ isoTwins G).card ≤ G.degree h - 3 := by
  by_contra hlt
  -- extract a twin star of the exact firing size `deg h − 2`
  have hge : G.degree h - 2 ≤ (G.neighborFinset h ∩ isoTwins G).card := by omega
  obtain ⟨K, hKsub, hKcard⟩ := Finset.exists_subset_card_eq hge
  apply hnf
  refine star_moat_fires G hm h3 h K ?_ ?_ hKcard hfire
  · exact fun x hx => (Finset.mem_inter.mp (hKsub hx)).1
  · exact fun t ht => (mem_isoTwins.mp (Finset.mem_inter.mp (hKsub ht)).2).1

open Classical in
/-- **The cap ledger.**  Over any hub set `S`, the total twin ownership is bounded by the
degree excess plus a `3`-per-*giant* credit: a capped hub (`9·deg ≤ n + 15`) owns
`≤ deg − 3` twins (`starved_cap`), while a giant contributes the trivial `≤ deg = (deg − 3) + 3`.
-/
theorem cap_sum_le {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2) (S : Finset (Fin n)) (hS : S ⊆ hubSet G) :
    ∑ h ∈ S, (G.neighborFinset h ∩ isoTwins G).card
      ≤ (∑ h ∈ S, (G.degree h - 3))
        + 3 * (S.filter (fun h => n + 15 < 9 * G.degree h)).card := by
  have hpt : ∀ h ∈ S, (G.neighborFinset h ∩ isoTwins G).card
      ≤ (G.degree h - 3) + 3 * (if n + 15 < 9 * G.degree h then 1 else 0) := by
    intro h hh
    have hdeg4 : 4 ≤ G.degree h := mem_hubSet.mp (hS hh)
    by_cases hg : n + 15 < 9 * G.degree h
    · simp only [hg, ite_true]
      have hle : (G.neighborFinset h ∩ isoTwins G).card ≤ G.degree h := by
        calc (G.neighborFinset h ∩ isoTwins G).card
            ≤ (G.neighborFinset h).card := Finset.card_le_card (Finset.inter_subset_left)
          _ = G.degree h := G.card_neighborFinset_eq_degree h
      omega
    · simp only [hg, ite_false]
      have hcap := starved_cap G hm h3 hnf h (by omega)
      omega
  calc ∑ h ∈ S, (G.neighborFinset h ∩ isoTwins G).card
      ≤ ∑ h ∈ S, ((G.degree h - 3) + 3 * (if n + 15 < 9 * G.degree h then 1 else 0)) :=
        Finset.sum_le_sum hpt
    _ = (∑ h ∈ S, (G.degree h - 3))
          + 3 * ∑ h ∈ S, (if n + 15 < 9 * G.degree h then 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ h ∈ S, (G.degree h - 3))
          + 3 * (S.filter (fun h => n + 15 < 9 * G.degree h)).card := by
        rw [Finset.card_filter]

open Classical in
/-- **The twin total.**  Under `hs0` (`e(M) = 0`) the degree-`3` set is the `M`-isolated twin
set, so the hub-to-twin incidence sum is `3·(8 + X) = 24 + 3X`. -/
theorem twin_total_eq {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 2 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    ∑ h ∈ hubSet G, (G.neighborFinset h ∩ isoTwins G).card = 24 + 3 * excessX n G := by
  have h1 := twin_incidence_total G h3
  have h2 : (isoTwins G).card = 8 + excessX n G := by
    rw [← deg3_eq_isoTwins_of_s0 G hs0, deg3_card_eq_eight_add_excess n G hn hm h3]
  have hbridge : ∑ h ∈ hubSet G, (G.neighborFinset h ∩ isoTwins G).card
      = 3 * (isoTwins G).card := by
    rw [← h1]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    congr 1
    apply Finset.ext
    intro x
    simp only [Finset.mem_inter]
  rw [hbridge, h2]; ring

open Classical in
/-- **The hub excess ledger.**  The degree excess is carried entirely by the hubs:
`Σ_{h ∈ Hub}(deg h − 3) = n − 8`, since every non-hub is a degree-`3` twin (`total_excess_eq`). -/
theorem hub_deg_excess_eq {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 8 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    ∑ h ∈ hubSet G, (G.degree h - 3) = n - 8 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun v => 4 ≤ G.degree v) (fun v => G.degree v - 3)
  have htot : ∑ v : Fin n, (G.degree v - 3) = n - 8 := total_excess_eq hn G hm h3
  have hzero : ∑ v ∈ Finset.univ.filter (fun v => ¬ 4 ≤ G.degree v), (G.degree v - 3) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [Finset.mem_filter] at hv
    have := h3 v
    omega
  have hhub : hubSet G = Finset.univ.filter (fun v => 4 ≤ G.degree v) := rfl
  rw [hhub]
  omega

open Classical in
/-- **The hoarding law** (SW §S2).  Twin-slot supply meets capacity: the `24 + 3X` twin
incidences are hosted by the hubs, capped at `deg − 3` apart from the `3`-per-giant credit, so
`3X + 32 ≤ n + 3·n_g` where `n_g` is the number of giants (hubs above the cap horizon
`9·deg ≤ n + 15`). -/
theorem hoarding_law {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) (hn : 8 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    3 * excessX n G + 32
      ≤ n + 3 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card := by
  have htot := twin_total_eq G (by omega) hm h3 hs0
  have hcap := cap_sum_le G hm h3 hnf (hubSet G) (Finset.Subset.refl _)
  have hexc := hub_deg_excess_eq G hn hm h3
  rw [htot, hexc] at hcap
  omega

open Classical in
/-- **The slots row** (SW §S2 / §4 slots).  Splitting the twin total by degree class: the
deg-`≥ 5` hubs absorb at most `X + h` slots (`h` = number of heavies), plus the `3`-per-giant
credit, so the deg-`4` owner-slot total `t₄` is forced up to `24 + 2X ≤ t₄ + h + 3·n_g`. -/
theorem slots_law {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) (hn : 8 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    24 + 2 * excessX n G
      ≤ (∑ h ∈ (hubSet G).filter (fun h => G.degree h = 4),
            (G.neighborFinset h ∩ isoTwins G).card)
        + (Finset.univ.filter (fun h => 5 ≤ G.degree h)).card
        + 3 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card := by
  have htot := twin_total_eq G (by omega) hm h3 hs0
  have hsplit := Finset.sum_filter_add_sum_filter_not (hubSet G)
    (fun h => G.degree h = 4) (fun h => (G.neighborFinset h ∩ isoTwins G).card)
  have hcap := cap_sum_le G hm h3 hnf ((hubSet G).filter (fun h => ¬ G.degree h = 4))
    (Finset.filter_subset _ _)
  have hDn4 : (hubSet G).filter (fun h => ¬ G.degree h = 4)
      = Finset.univ.filter (fun h => 5 ≤ G.degree h) := by
    ext x
    simp only [Finset.mem_filter, mem_hubSet, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hh, hne⟩; omega
    · intro h5; exact ⟨by omega, by omega⟩
  have hdeg : ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4), (G.degree h - 3)
      = excessX n G + (Finset.univ.filter (fun h => 5 ≤ G.degree h)).card := by
    rw [hDn4]
    have hpt : ∀ h ∈ Finset.univ.filter (fun h => 5 ≤ G.degree h),
        G.degree h - 3 = (G.degree h - 4) + 1 := by
      intro h hh; rw [Finset.mem_filter] at hh; omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    rfl
  have hgle : (((hubSet G).filter (fun h => ¬ G.degree h = 4)).filter
        (fun h => n + 15 < 9 * G.degree h)).card
      ≤ ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1.1, hx.2⟩
  rw [hdeg] at hcap
  omega

open Classical in
/-- **The giant census bound** (SW §S2).  A giant `h` (`n + 15 < 9·deg h`) has
`9·(deg h − 4) ≥ n − 20`, and every giant is a heavy, so summing gives
`n_g·(n − 20) ≤ 9·X`.  With hoarding this pins `n_g ≤ 2` at `n ≤ 49`. -/
theorem giant_excess_bound {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 30 ≤ n) :
    ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card * (n - 20)
      ≤ 9 * excessX n G := by
  set Gi := (hubSet G).filter (fun h => n + 15 < 9 * G.degree h) with hGidef
  have hptB : ∀ h ∈ Gi, n - 20 ≤ 9 * (G.degree h - 4) := by
    intro h hh
    rw [hGidef, Finset.mem_filter] at hh
    have hdeg := mem_hubSet.mp hh.1
    omega
  have hB : Gi.card * (n - 20) ≤ 9 * ∑ h ∈ Gi, (G.degree h - 4) := by
    have e1 : Gi.card * (n - 20) = ∑ _h ∈ Gi, (n - 20) := by
      rw [Finset.sum_const, smul_eq_mul]
    have e2 : 9 * ∑ h ∈ Gi, (G.degree h - 4) = ∑ h ∈ Gi, 9 * (G.degree h - 4) := by
      rw [Finset.mul_sum]
    rw [e1, e2]
    exact Finset.sum_le_sum hptB
  have hsub : Gi ⊆ Finset.univ.filter (fun v => 5 ≤ G.degree v) := by
    intro x hx
    rw [hGidef, Finset.mem_filter] at hx
    rw [Finset.mem_filter]
    have hdeg := mem_hubSet.mp hx.1
    exact ⟨Finset.mem_univ x, by omega⟩
  have hA : ∑ h ∈ Gi, (G.degree h - 4) ≤ excessX n G :=
    Finset.sum_le_sum_of_subset hsub
  calc Gi.card * (n - 20) ≤ 9 * ∑ h ∈ Gi, (G.degree h - 4) := hB
    _ ≤ 9 * excessX n G := by gcongr

open Classical in
/-- **Heavies are bounded by the excess.**  The number of heavies (`deg ≥ 5`) is at most the
total excess `X`, since each heavy contributes `deg − 4 ≥ 1`. -/
theorem heavy_le_excess {n : ℕ} (G : SimpleGraph (Fin n)) :
    (Finset.univ.filter (fun h => 5 ≤ G.degree h)).card ≤ excessX n G := by
  have hcard : (Finset.univ.filter (fun h => 5 ≤ G.degree h)).card
      = ∑ _h ∈ Finset.univ.filter (fun h => 5 ≤ G.degree h), 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one]
  rw [hcard]
  change ∑ _h ∈ Finset.univ.filter (fun h => 5 ≤ G.degree h), 1
      ≤ ∑ h ∈ Finset.univ.filter (fun v => 5 ≤ G.degree v), (G.degree h - 4)
  apply Finset.sum_le_sum
  intro h hh
  rw [Finset.mem_filter] at hh
  omega

/-! ## The per-`p` sharpened slots row (D1)

Sharpens `slots_law` by splitting the deg-`≥ 5` twin demand along the per-heavy
caps `starved_cap` (no independence law). The twin total `24 + 3X` splits into the
deg-4 owner slots `t₄` and a deg-`≥ 5` remainder `≤ X + p + h₆₊ + 4n_g`, giving the
sharpened row `24 + 2X ≤ t₄ + p + h₆₊ + 4n_g` (`p` = saturated deg-5 hubs,
`h₆₊` = non-giant deg-`≥ 6` hubs, `n_g` = giants). -/

open Classical in
/-- **D1 — the per-`p` sharpened slots row.**  In a never-firing starved census (`m = 2(n−2)`,
`δ ≥ 3`, `hs0`) the twin total `24 + 3X` splits along the honest per-heavy caps into
`24 + 2X ≤ t₄ + p + h₆₊ + 4·n_g`, where `t₄ = ∑_{deg-4 hubs} |N(h) ∩ Iso|`, `p` is the count of
saturated deg-`5` hubs (deg `5`, owning exactly `2` `M`-isolated twins), `h₆₊` the count of
non-giant deg-`≥ 6` hubs (`6 ≤ deg`, `9·deg ≤ n + 15`) and `n_g` the number of giants
(`n + 15 < 9·deg`).  Each deg-`≥ 5` hub contributes at most `(deg − 4)` plus one of the class
credits, so the deg-`≥ 5` remainder is `≤ X + p + h₆₊ + 4·n_g`; the star-moat cap `starved_cap`
supplies the non-giant per-hub bounds. -/
theorem slots_p_row {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) (hn : 8 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    24 + 2 * excessX n G
      ≤ (∑ h ∈ (hubSet G).filter (fun h => G.degree h = 4),
            (G.neighborFinset h ∩ isoTwins G).card)
        + ((hubSet G).filter (fun h => G.degree h = 5 ∧
            (G.neighborFinset h ∩ isoTwins G).card = 2)).card
        + ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧
            ¬ (n + 15 < 9 * G.degree h))).card
        + 4 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card := by
  have htot := twin_total_eq G (by omega) hm h3 hs0
  have hsplit := Finset.sum_filter_add_sum_filter_not (hubSet G)
    (fun h => G.degree h = 4) (fun h => (G.neighborFinset h ∩ isoTwins G).card)
  -- the set of deg-`≥ 5` hubs, and its identification with `univ.filter (5 ≤ deg)`
  have hDn4 : (hubSet G).filter (fun h => ¬ G.degree h = 4)
      = Finset.univ.filter (fun h => 5 ≤ G.degree h) := by
    ext x
    simp only [Finset.mem_filter, mem_hubSet, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hh, hne⟩; omega
    · intro h5; exact ⟨by omega, by omega⟩
  -- the sharpened deg-`≥ 5` cap: the remainder is `≤ X + p + h₆₊ + 4·n_g`
  have hcapP : ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
      (G.neighborFinset h ∩ isoTwins G).card
      ≤ excessX n G
        + ((hubSet G).filter (fun h => G.degree h = 5 ∧
            (G.neighborFinset h ∩ isoTwins G).card = 2)).card
        + ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧
            ¬ (n + 15 < 9 * G.degree h))).card
        + 4 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card := by
    have hpt : ∀ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
        (G.neighborFinset h ∩ isoTwins G).card
        ≤ (G.degree h - 4)
          + (if G.degree h = 5 ∧ (G.neighborFinset h ∩ isoTwins G).card = 2 then 1 else 0)
          + (if 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h) then 1 else 0)
          + 4 * (if n + 15 < 9 * G.degree h then 1 else 0) := by
      intro h hh
      rw [Finset.mem_filter] at hh
      obtain ⟨hhub, hne4⟩ := hh
      have hdeg4 : 4 ≤ G.degree h := mem_hubSet.mp hhub
      have hcardle : (G.neighborFinset h ∩ isoTwins G).card ≤ G.degree h :=
        le_of_le_of_eq (Finset.card_le_card Finset.inter_subset_left)
          (G.card_neighborFinset_eq_degree h)
      by_cases hg : n + 15 < 9 * G.degree h
      · split_ifs <;> omega
      · have hcap := starved_cap G hm h3 hnf h (by omega)
        split_ifs <;> omega
    calc ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
            (G.neighborFinset h ∩ isoTwins G).card
        ≤ ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
            ((G.degree h - 4)
              + (if G.degree h = 5 ∧ (G.neighborFinset h ∩ isoTwins G).card = 2 then 1 else 0)
              + (if 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h) then 1 else 0)
              + 4 * (if n + 15 < 9 * G.degree h then 1 else 0)) := Finset.sum_le_sum hpt
      _ ≤ excessX n G
            + ((hubSet G).filter (fun h => G.degree h = 5 ∧
                (G.neighborFinset h ∩ isoTwins G).card = 2)).card
            + ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧
                ¬ (n + 15 < 9 * G.degree h))).card
            + 4 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
          have hA : ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4), (G.degree h - 4)
              = excessX n G := by rw [hDn4]; rfl
          have hB : ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
              (if G.degree h = 5 ∧ (G.neighborFinset h ∩ isoTwins G).card = 2 then 1 else 0)
              ≤ ((hubSet G).filter (fun h => G.degree h = 5 ∧
                  (G.neighborFinset h ∩ isoTwins G).card = 2)).card := by
            rw [← Finset.card_filter]
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_filter, mem_hubSet] at hx ⊢
            exact ⟨hx.1.1, hx.2⟩
          have hC : ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
              (if 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h) then 1 else 0)
              ≤ ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧
                  ¬ (n + 15 < 9 * G.degree h))).card := by
            rw [← Finset.card_filter]
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_filter, mem_hubSet] at hx ⊢
            exact ⟨hx.1.1, hx.2⟩
          have hD : ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
              4 * (if n + 15 < 9 * G.degree h then 1 else 0)
              ≤ 4 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card := by
            rw [← Finset.mul_sum, ← Finset.card_filter]
            gcongr
            exact Finset.filter_subset _ _
          omega
  omega

/-! ## Independence and triangle helpers -/

open Classical in
/-- Triangle test. -/
theorem tri_deg445_fires {n : ℕ} [Nonempty (Fin n)] (hn : 16 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (a b t : Fin n)
    (hab : G.Adj a b) (hat : G.Adj a t) (hbt : G.Adj b t)
    (hda : G.degree a = 4) (hdb : G.degree b = 4) (hdt : G.degree t = 3) :
    algConn G ≤ 2 := by
  have hne_ab : a ≠ b := G.ne_of_adj hab
  have hne_at : a ≠ t := by intro h; rw [h, hdt] at hda; omega
  have hne_bt : b ≠ t := by intro h; rw [h, hdt] at hdb; omega
  have e0 : (![a, b, t] : Fin 3 → Fin n) 0 = a := rfl
  have e1 : (![a, b, t] : Fin 3 → Fin n) 1 = b := rfl
  have e2 : (![a, b, t] : Fin 3 → Fin n) 2 = t := rfl
  refine master_cycle_fires (k := 3) (by norm_num) G hm h3 ![a, b, t] ?_ ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> rfl
  · intro i
    fin_cases i
    · change G.Adj a b; exact hab
    · change G.Adj b t; exact hbt
    · change G.Adj t a; exact hat.symm
  · have hsplit : (∑ i : ZMod 3, G.degree (![a, b, t] i))
        = G.degree a + G.degree b + G.degree t := by
      have h := Fin.sum_univ_three (fun i : Fin 3 => G.degree (![a, b, t] i))
      rw [e0, e1, e2] at h
      exact h
    rw [hsplit, hda, hdb, hdt]; omega
  · have hsplit : (∑ i : ZMod 3, (G.degree (![a, b, t] i) - 1))
        = (G.degree a - 1) + (G.degree b - 1) + (G.degree t - 1) := by
      have h := Fin.sum_univ_three (fun i : Fin 3 => G.degree (![a, b, t] i) - 1)
      rw [e0, e1, e2] at h
      exact h
    rw [hsplit, hda, hdb, hdt]
    omega

open Classical in
/-- **Owner independence.**  In a never-firing starved census (`m = 2(n−2)`, `δ ≥ 3`) at
`n ≥ 30`, any two *distinct* degree-`4` vertices `o₁, o₂`, each carrying a degree-`3` neighbour
(`t₁` resp. `t₂`), are non-adjacent.  If they were adjacent: distinct twins (`t₁ ≠ t₂`) fire the
`(4,4)` decorated edge `z4c_fires`; a shared twin (`t₁ = t₂`) makes `{o₁, o₂, t₁}` a
degree-`(4,4,3)` triangle which fires the master cycle `tri_deg445_fires` — either way
contradicting `¬ algConn G ≤ 2`. -/
theorem owner_independence {n : ℕ} [Nonempty (Fin n)] (hn : 30 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (o₁ o₂ t₁ t₂ : Fin n) (ho1 : G.degree o₁ = 4) (ho2 : G.degree o₂ = 4)
    (ht1 : G.Adj o₁ t₁) (hdt1 : G.degree t₁ = 3)
    (ht2 : G.Adj o₂ t₂) (hdt2 : G.degree t₂ = 3) :
    ¬ G.Adj o₁ o₂ := by
  intro hadj
  apply hnf
  by_cases htw : t₁ = t₂
  · subst htw
    exact tri_deg445_fires (by omega) G hm h3 o₁ o₂ t₁ hadj ht1 ht2 ho1 ho2 hdt1
  · have hutv : o₁ ≠ t₂ := by intro h; rw [h, hdt2] at ho1; omega
    have hvtu : o₂ ≠ t₁ := by intro h; rw [h, hdt1] at ho2; omega
    exact z4c_fires hn G hm h3 o₁ o₂ t₁ t₂ hadj ho1 ho2 ht1 ht2 hdt1 hdt2 htw hutv hvtu

open Classical in
/-- **The owner-choke count.**  In a starved census (`m = 2(n−2)`, `δ ≥ 3`, `hs0`), under the
starved degree-`4` twin cap (`hcap`: each degree-`4` hub owns `≤ 1` twin) and owner independence
(`hindep`: distinct twin-carrying degree-`4` hubs are non-adjacent), the degree-`4` owner-slot
total `t₄ = ∑_{deg 4 hubs} |N(h) ∩ Iso|` satisfies the choke `7·t₄ + 3X + 32 ≤ 4n`.

Each owner `o` (degree-`4` hub with its unique twin) spends `1` edge on that twin and, by
independence, `0` on other owners, so its remaining `3` edges land on non-owner hubs
(`|N(o) ∩ NH| = 3`).  The bipartite double count `cross_count` transposes `∑_{o} |N(o) ∩ NH| =
3·t₄` into `∑_{w ∈ NH} |N(w) ∩ O| ≤ ∑_{w ∈ NH} deg w`, and the hub degree total
`∑_{Hub} deg + 3X + 32 = 4n` splits as `∑_{NH} deg + 4·t₄`; combining gives the choke. -/
theorem choke_count {n : ℕ} (hn : 8 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (hcap : ∀ h : Fin n, G.degree h = 4 → (G.neighborFinset h ∩ isoTwins G).card ≤ 1)
    (hindep : ∀ o₁ o₂ : Fin n, G.degree o₁ = 4 → G.degree o₂ = 4 →
        (G.neighborFinset o₁ ∩ isoTwins G).Nonempty →
        (G.neighborFinset o₂ ∩ isoTwins G).Nonempty → o₁ ≠ o₂ → ¬ G.Adj o₁ o₂) :
    7 * (∑ h ∈ (hubSet G).filter (fun h => G.degree h = 4),
            (G.neighborFinset h ∩ isoTwins G).card)
        + 3 * excessX n G + 32 ≤ 4 * n := by
  classical
  -- the hub degree total `∑_{Hub} deg + 3X + 32 = 4n`
  have hhand : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  have hcard3 : (deg3Set G).card = 8 + excessX n G :=
    deg3_card_eq_eight_add_excess n G (by omega) hm h3
  have hdisj : Disjoint (hubSet G) (deg3Set G) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    rw [mem_hubSet] at hv
    rw [mem_deg3Set] at hv'
    omega
  have hunion : hubSet G ∪ deg3Set G = Finset.univ := by
    ext v
    simp only [Finset.mem_union, mem_hubSet, mem_deg3Set, Finset.mem_univ, iff_true]
    have := h3 v
    omega
  have hd3sum : ∑ t ∈ deg3Set G, G.degree t = 3 * (deg3Set G).card := by
    have hc : ∑ t ∈ deg3Set G, G.degree t = ∑ _t ∈ deg3Set G, 3 :=
      Finset.sum_congr rfl (fun t ht => mem_deg3Set.mp ht)
    rw [hc, Finset.sum_const, smul_eq_mul, mul_comm]
  have hpart : ∑ h ∈ hubSet G, G.degree h + ∑ t ∈ deg3Set G, G.degree t
      = ∑ v : Fin n, G.degree v := by
    rw [← Finset.sum_union hdisj, hunion]
  have hHubsum : ∑ h ∈ hubSet G, G.degree h + 3 * excessX n G + 32 = 4 * n := by
    omega
  -- the owner set and the non-owner hubs
  set D4 := (hubSet G).filter (fun h => G.degree h = 4) with hD4def
  set O := D4.filter (fun h => (G.neighborFinset h ∩ isoTwins G).Nonempty) with hOdef
  set NH := hubSet G \ O with hNHdef
  have hOsubD4 : O ⊆ D4 := Finset.filter_subset _ _
  have hD4subHub : D4 ⊆ hubSet G := Finset.filter_subset _ _
  have hOsubHub : O ⊆ hubSet G := hOsubD4.trans hD4subHub
  -- `t₄ = |O|`
  have ht4 : ∑ h ∈ D4, (G.neighborFinset h ∩ isoTwins G).card = O.card := by
    rw [hOdef, Finset.card_filter]
    refine Finset.sum_congr rfl (fun h hh => ?_)
    rw [hD4def, Finset.mem_filter] at hh
    by_cases hne : (G.neighborFinset h ∩ isoTwins G).Nonempty
    · rw [ite_eq_left hne]
      have hle := hcap h hh.2
      have hge := Finset.card_pos.mpr hne
      omega
    · rw [ite_eq_right hne]
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
  -- each owner has exactly three non-owner-hub neighbours
  have hslice : ∀ o ∈ O, (G.neighborFinset o ∩ NH).card = 3 := by
    intro o ho
    have hoD4 : o ∈ D4 := hOsubD4 ho
    rw [hOdef, Finset.mem_filter] at ho
    obtain ⟨_, hoNE⟩ := ho
    rw [hD4def, Finset.mem_filter] at hoD4
    obtain ⟨_, hodeg⟩ := hoD4
    have hiso1 : (G.neighborFinset o ∩ isoTwins G).card = 1 := by
      have hle := hcap o hodeg
      have hge := Finset.card_pos.mpr hoNE
      omega
    have hseteq : G.neighborFinset o ∩ NH = G.neighborFinset o \ isoTwins G := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_inter] at hx
        obtain ⟨hxN, hxNH⟩ := hx
        rw [hNHdef, Finset.mem_sdiff] at hxNH
        obtain ⟨hxHub, _⟩ := hxNH
        rw [Finset.mem_sdiff]
        refine ⟨hxN, ?_⟩
        intro hxIso
        have hd3 : G.degree x = 3 := (mem_isoTwins.mp hxIso).1
        rw [mem_hubSet] at hxHub
        omega
      · intro hx
        rw [Finset.mem_sdiff] at hx
        obtain ⟨hxN, hxIso⟩ := hx
        have hAdj : G.Adj o x := (G.mem_neighborFinset o x).mp hxN
        have hdeg_x_ne3 : G.degree x ≠ 3 := by
          intro h3x
          apply hxIso
          have hmem : x ∈ deg3Set G := mem_deg3Set.mpr h3x
          rwa [deg3_eq_isoTwins_of_s0 G hs0] at hmem
        have hxHub : x ∈ hubSet G := by
          rw [mem_hubSet]; have := h3 x; omega
        have hxO : x ∉ O := by
          intro hxOmem
          have hxD4 : x ∈ D4 := hOsubD4 hxOmem
          rw [hOdef, Finset.mem_filter] at hxOmem
          obtain ⟨_, hxNE⟩ := hxOmem
          rw [hD4def, Finset.mem_filter] at hxD4
          obtain ⟨_, hxdeg⟩ := hxD4
          exact hindep o x hodeg hxdeg hoNE hxNE (G.ne_of_adj hAdj) hAdj
        rw [Finset.mem_inter, hNHdef, Finset.mem_sdiff]
        exact ⟨hxN, hxHub, hxO⟩
    rw [hseteq]
    have hsum := Finset.card_inter_add_card_sdiff (G.neighborFinset o) (isoTwins G)
    rw [hiso1, G.card_neighborFinset_eq_degree, hodeg] at hsum
    omega
  -- assemble the cross count
  have hslicesum : ∑ o ∈ O, (G.neighborFinset o ∩ NH).card = 3 * O.card := by
    rw [Finset.sum_congr rfl hslice, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcc := cross_count G O NH
  have hcap2 : ∑ w ∈ NH, (G.neighborFinset w ∩ O).card ≤ ∑ w ∈ NH, G.degree w := by
    refine Finset.sum_le_sum (fun w _ => ?_)
    calc (G.neighborFinset w ∩ O).card ≤ (G.neighborFinset w).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree w := G.card_neighborFinset_eq_degree w
  have hOdeg : ∑ o ∈ O, G.degree o = 4 * O.card := by
    have hpt : ∀ o ∈ O, G.degree o = 4 := by
      intro o ho
      have hoD4 : o ∈ D4 := hOsubD4 ho
      rw [hD4def, Finset.mem_filter] at hoD4
      exact hoD4.2
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, mul_comm]
  have hNHsum : ∑ w ∈ NH, G.degree w + ∑ o ∈ O, G.degree o = ∑ h ∈ hubSet G, G.degree h := by
    rw [hNHdef]
    exact Finset.sum_sdiff hOsubHub
  rw [ht4]
  omega

/-! ## The per-`p` sharpened owner-choke

Sharpens the owner-choke `choke_count` (`7·t₄ + 3X + 32 ≤ 4n`) by `8·p`, where `p`
counts saturated degree-5 hubs (owning exactly two twins). A saturated degree-5
hub spends 2 edges on its twins and, by the decorated-edge law, 0 on owners and 0
on other saturated hubs, so its remaining 3 edges land on non-owner
non-saturated hubs; the transposed slice count gives `p_choke_count` /
`p_choke_row` (`7·t₄ + 8·p + 3X + 32 ≤ 4n`). The `(4,5)` independence is
`owner_sat_independence`; the `(5,5)` independence is threaded as `hindep55`. -/

open Classical in
private theorem p_choke_count_hsliceO : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (_ : ∀ (v : Fin n), 3
  ≤ G.degree v)
  (_ : ∀ (v w : Fin n), G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
  (_ : ∀ (h : Fin n), G.degree h = 4 → #(G.neighborFinset h ∩ isoTwins G) ≤ 1)
  (_ :
    ∀ (o₁ o₂ : Fin n),
      G.degree o₁ = 4 →
        G.degree o₂ = 4 →
          (G.neighborFinset o₁ ∩ isoTwins G).Nonempty →
            (G.neighborFinset o₂ ∩ isoTwins G).Nonempty → o₁ ≠ o₂ → ¬G.Adj o₁ o₂)
  (_ :
    ∀ (o s : Fin n),
      G.degree o = 4 →
        (G.neighborFinset o ∩ isoTwins G).Nonempty →
          G.degree s = 5 → #(G.neighborFinset s ∩ isoTwins G) = 2 → ¬G.Adj o s)
  (D4 : Finset (Fin n)) (_ : D4 = {h ∈ hubSet G | G.degree h = 4}),
  let O := {h ∈ D4 | (G.neighborFinset h ∩ isoTwins G).Nonempty};
  ∀ (_ : O = {h ∈ D4 | (G.neighborFinset h ∩ isoTwins G).Nonempty}),
    let P := {h ∈ hubSet G | G.degree h = 5 ∧ #(G.neighborFinset h ∩ isoTwins G) = 2};
    ∀ (_ : P = {h ∈ hubSet G | G.degree h = 5 ∧ #(G.neighborFinset h ∩ isoTwins G) = 2}),
      let SP := O ∪ P;
      ∀ (_ : SP = O ∪ P),
        let NH := hubSet G \ SP;
        ∀ (_ : NH = hubSet G \ SP) (_ : O ⊆ D4), ∀ o ∈ O, #(G.neighborFinset o ∩ NH) =
          3 := by
  classical
  intro n G h3 hs0 hcap4 hindep44 hindep45 D4 hD4def O hOdef P hPdef SP hSPdef NH hNHdef hOsubD4 o
    ho
  have hoD4 : o ∈ D4 := hOsubD4 ho
  rw [hOdef, Finset.mem_filter] at ho
  obtain ⟨_, hoNE⟩ := ho
  rw [hD4def, Finset.mem_filter] at hoD4
  obtain ⟨_, hodeg⟩ := hoD4
  have hiso1 : (G.neighborFinset o ∩ isoTwins G).card = 1 := by
    have hle := hcap4 o hodeg
    have hge := Finset.card_pos.mpr hoNE
    omega
  have hseteq : G.neighborFinset o ∩ NH = G.neighborFinset o \ isoTwins G := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_inter] at hx
      obtain ⟨hxN, hxNH⟩ := hx
      rw [hNHdef, Finset.mem_sdiff] at hxNH
      obtain ⟨hxHub, _⟩ := hxNH
      rw [Finset.mem_sdiff]
      refine ⟨hxN, ?_⟩
      intro hxIso
      have hd3 : G.degree x = 3 := (mem_isoTwins.mp hxIso).1
      rw [mem_hubSet] at hxHub
      omega
    · intro hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hxN, hxIso⟩ := hx
      have hAdj : G.Adj o x := (G.mem_neighborFinset o x).mp hxN
      have hdeg_x_ne3 : G.degree x ≠ 3 := by
        intro h3x
        apply hxIso
        have hmem : x ∈ deg3Set G := mem_deg3Set.mpr h3x
        rwa [deg3_eq_isoTwins_of_s0 G hs0] at hmem
      have hxHub : x ∈ hubSet G := by
        rw [mem_hubSet]; have := h3 x; omega
      have hxSP : x ∉ SP := by
        rw [hSPdef, Finset.mem_union, not_or]
        refine ⟨?_, ?_⟩
        · intro hxO
          have hxD4 : x ∈ D4 := hOsubD4 hxO
          rw [hOdef, Finset.mem_filter] at hxO
          obtain ⟨_, hxNE⟩ := hxO
          rw [hD4def, Finset.mem_filter] at hxD4
          obtain ⟨_, hxdeg⟩ := hxD4
          exact hindep44 o x hodeg hxdeg hoNE hxNE (G.ne_of_adj hAdj) hAdj
        · intro hxP
          rw [hPdef, Finset.mem_filter] at hxP
          obtain ⟨_, hx5, hx2⟩ := hxP
          exact hindep45 o x hodeg hoNE hx5 hx2 hAdj
      rw [Finset.mem_inter, hNHdef, Finset.mem_sdiff]
      exact ⟨hxN, hxHub, hxSP⟩
  rw [hseteq]
  have hsum := Finset.card_inter_add_card_sdiff (G.neighborFinset o) (isoTwins G)
  rw [hiso1, G.card_neighborFinset_eq_degree, hodeg] at hsum
  omega

open Classical in
/-- **N5 — the per-`p` sharpened owner-choke (counting core).**  In a starved census
(`m = 2(n−2)`, `δ ≥ 3`, `hs0`) under the degree-`4` twin cap (`hcap4`) and the three independence
rows — degree-`4` owners pairwise non-adjacent (`hindep44`), owner–saturated non-adjacent
(`hindep45`), saturated–saturated non-adjacent (`hindep55`) — the degree-`4` owner-slot total
`t₄ = ∑_{deg 4 hubs} |N(h) ∩ Iso|` and the saturated degree-`5` count `p` satisfy the sharpened
choke `7·t₄ + 8·p + 3·X + 32 ≤ 4n`.

Owners `O` (degree-`4`, one twin) each spend `3` edges on non-owner non-saturated hubs `NH`;
saturated degree-`5`s `P` (two twins) each spend `3` edges on `NH` (the `2` twin edges and the
`0` owner/saturated edges being excluded by independence).  The bipartite double count
`cross_count` transposes `∑_{O ∪ P} |N(·) ∩ NH| = 3·t₄ + 3·p` into
`∑_{NH} |N(w) ∩ (O ∪ P)| ≤ ∑_{NH} deg w`, and the hub degree total
`∑_{Hub} deg + 3X + 32 = 4n` splits as `∑_{NH} deg + 4·t₄ + 5·p`; combining gives the choke. -/
theorem p_choke_count {n : ℕ} (hn : 8 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (hcap4 : ∀ h : Fin n, G.degree h = 4 → (G.neighborFinset h ∩ isoTwins G).card ≤ 1)
    (hindep44 : ∀ o₁ o₂ : Fin n, G.degree o₁ = 4 → G.degree o₂ = 4 →
        (G.neighborFinset o₁ ∩ isoTwins G).Nonempty →
        (G.neighborFinset o₂ ∩ isoTwins G).Nonempty → o₁ ≠ o₂ → ¬ G.Adj o₁ o₂)
    (hindep45 : ∀ o s : Fin n, G.degree o = 4 →
        (G.neighborFinset o ∩ isoTwins G).Nonempty → G.degree s = 5 →
        (G.neighborFinset s ∩ isoTwins G).card = 2 → ¬ G.Adj o s)
    (hindep55 : ∀ s₁ s₂ : Fin n, G.degree s₁ = 5 →
        (G.neighborFinset s₁ ∩ isoTwins G).card = 2 → G.degree s₂ = 5 →
        (G.neighborFinset s₂ ∩ isoTwins G).card = 2 → s₁ ≠ s₂ → ¬ G.Adj s₁ s₂) :
    7 * (∑ h ∈ (hubSet G).filter (fun h => G.degree h = 4),
            (G.neighborFinset h ∩ isoTwins G).card)
        + 8 * ((hubSet G).filter (fun h => G.degree h = 5 ∧
            (G.neighborFinset h ∩ isoTwins G).card = 2)).card
        + 3 * excessX n G + 32 ≤ 4 * n := by
  classical
  -- the hub degree total `∑_{Hub} deg + 3X + 32 = 4n`
  have hhand : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  have hcard3 : (deg3Set G).card = 8 + excessX n G :=
    deg3_card_eq_eight_add_excess n G (by omega) hm h3
  have hdisj : Disjoint (hubSet G) (deg3Set G) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    rw [mem_hubSet] at hv
    rw [mem_deg3Set] at hv'
    omega
  have hunion : hubSet G ∪ deg3Set G = Finset.univ := by
    ext v
    simp only [Finset.mem_union, mem_hubSet, mem_deg3Set, Finset.mem_univ, iff_true]
    have := h3 v
    omega
  have hd3sum : ∑ t ∈ deg3Set G, G.degree t = 3 * (deg3Set G).card := by
    have hc : ∑ t ∈ deg3Set G, G.degree t = ∑ _t ∈ deg3Set G, 3 :=
      Finset.sum_congr rfl (fun t ht => mem_deg3Set.mp ht)
    rw [hc, Finset.sum_const, smul_eq_mul, mul_comm]
  have hpart : ∑ h ∈ hubSet G, G.degree h + ∑ t ∈ deg3Set G, G.degree t
      = ∑ v : Fin n, G.degree v := by
    rw [← Finset.sum_union hdisj, hunion]
  have hHubsum : ∑ h ∈ hubSet G, G.degree h + 3 * excessX n G + 32 = 4 * n := by
    omega
  -- the owner set, the saturated degree-`5` set, and the non-owner non-saturated hubs
  set D4 := (hubSet G).filter (fun h => G.degree h = 4) with hD4def
  set O := D4.filter (fun h => (G.neighborFinset h ∩ isoTwins G).Nonempty) with hOdef
  set P := (hubSet G).filter (fun h => G.degree h = 5 ∧
    (G.neighborFinset h ∩ isoTwins G).card = 2) with hPdef
  set SP := O ∪ P with hSPdef
  set NH := hubSet G \ SP with hNHdef
  have hOsubD4 : O ⊆ D4 := Finset.filter_subset _ _
  have hD4subHub : D4 ⊆ hubSet G := Finset.filter_subset _ _
  have hOsubHub : O ⊆ hubSet G := hOsubD4.trans hD4subHub
  have hPsubHub : P ⊆ hubSet G := Finset.filter_subset _ _
  have hSPsubHub : SP ⊆ hubSet G := by
    rw [hSPdef]; exact Finset.union_subset hOsubHub hPsubHub
  have hOPdisj : Disjoint O P := by
    rw [Finset.disjoint_left]
    intro x hxO hxP
    have hx4 : G.degree x = 4 := by
      have hxD4 := hOsubD4 hxO
      rw [hD4def, Finset.mem_filter] at hxD4
      exact hxD4.2
    have hx5 : G.degree x = 5 := by
      rw [hPdef, Finset.mem_filter] at hxP
      exact hxP.2.1
    omega
  -- `t₄ = |O|` via the degree-`4` twin cap
  have ht4 : ∑ h ∈ D4, (G.neighborFinset h ∩ isoTwins G).card = O.card := by
    rw [hOdef, Finset.card_filter]
    refine Finset.sum_congr rfl (fun h hh => ?_)
    rw [hD4def, Finset.mem_filter] at hh
    by_cases hne : (G.neighborFinset h ∩ isoTwins G).Nonempty
    · rw [ite_eq_left hne]
      have hle := hcap4 h hh.2
      have hge := Finset.card_pos.mpr hne
      omega
    · rw [ite_eq_right hne]
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
  -- each owner has exactly three non-owner non-saturated hub neighbours
  have hsliceO := p_choke_count_hsliceO (n := n) (G := G) (h3) (hs0) (hcap4)
      (hindep44) (hindep45) (D4 := D4) (hD4def) (hOdef)
      (hPdef) (hSPdef) (hNHdef) (hOsubD4)
  -- each saturated degree-`5` has exactly three non-owner non-saturated hub neighbours
  have hsliceP : ∀ s ∈ P, (G.neighborFinset s ∩ NH).card = 3 := by
    intro s hs
    rw [hPdef, Finset.mem_filter] at hs
    obtain ⟨_, hs5, hs2⟩ := hs
    have hseteq : G.neighborFinset s ∩ NH = G.neighborFinset s \ isoTwins G := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_inter] at hx
        obtain ⟨hxN, hxNH⟩ := hx
        rw [hNHdef, Finset.mem_sdiff] at hxNH
        obtain ⟨hxHub, _⟩ := hxNH
        rw [Finset.mem_sdiff]
        refine ⟨hxN, ?_⟩
        intro hxIso
        have hd3 : G.degree x = 3 := (mem_isoTwins.mp hxIso).1
        rw [mem_hubSet] at hxHub
        omega
      · intro hx
        rw [Finset.mem_sdiff] at hx
        obtain ⟨hxN, hxIso⟩ := hx
        have hAdj : G.Adj s x := (G.mem_neighborFinset s x).mp hxN
        have hdeg_x_ne3 : G.degree x ≠ 3 := by
          intro h3x
          apply hxIso
          have hmem : x ∈ deg3Set G := mem_deg3Set.mpr h3x
          rwa [deg3_eq_isoTwins_of_s0 G hs0] at hmem
        have hxHub : x ∈ hubSet G := by
          rw [mem_hubSet]; have := h3 x; omega
        have hxSP : x ∉ SP := by
          rw [hSPdef, Finset.mem_union, not_or]
          refine ⟨?_, ?_⟩
          · intro hxO
            have hxD4 : x ∈ D4 := hOsubD4 hxO
            rw [hOdef, Finset.mem_filter] at hxO
            obtain ⟨_, hxNE⟩ := hxO
            rw [hD4def, Finset.mem_filter] at hxD4
            obtain ⟨_, hxdeg⟩ := hxD4
            exact hindep45 x s hxdeg hxNE hs5 hs2 hAdj.symm
          · intro hxP
            rw [hPdef, Finset.mem_filter] at hxP
            obtain ⟨_, hx5, hx2⟩ := hxP
            exact hindep55 s x hs5 hs2 hx5 hx2 (G.ne_of_adj hAdj) hAdj
        rw [Finset.mem_inter, hNHdef, Finset.mem_sdiff]
        exact ⟨hxN, hxHub, hxSP⟩
    rw [hseteq]
    have hsum := Finset.card_inter_add_card_sdiff (G.neighborFinset s) (isoTwins G)
    rw [hs2, G.card_neighborFinset_eq_degree, hs5] at hsum
    omega
  -- the joint slice count `∑_{O ∪ P} |N(·) ∩ NH| = 3·|O| + 3·|P|`
  have hslicesum : ∑ v ∈ SP, (G.neighborFinset v ∩ NH).card = 3 * O.card + 3 * P.card := by
    have e1 : ∑ v ∈ O, (G.neighborFinset v ∩ NH).card = 3 * O.card := by
      rw [Finset.sum_congr rfl hsliceO, Finset.sum_const, smul_eq_mul, mul_comm]
    have e2 : ∑ v ∈ P, (G.neighborFinset v ∩ NH).card = 3 * P.card := by
      rw [Finset.sum_congr rfl hsliceP, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hSPdef, Finset.sum_union hOPdisj, e1, e2]
  -- transpose the count and cap it by the non-owner-non-saturated hub degree total
  have hcc := cross_count G SP NH
  have hcap2 : ∑ w ∈ NH, (G.neighborFinset w ∩ SP).card ≤ ∑ w ∈ NH, G.degree w := by
    refine Finset.sum_le_sum (fun w _ => ?_)
    calc (G.neighborFinset w ∩ SP).card ≤ (G.neighborFinset w).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree w := G.card_neighborFinset_eq_degree w
  have hOdeg : ∑ o ∈ O, G.degree o = 4 * O.card := by
    have hpt : ∀ o ∈ O, G.degree o = 4 := by
      intro o ho
      have hoD4 : o ∈ D4 := hOsubD4 ho
      rw [hD4def, Finset.mem_filter] at hoD4
      exact hoD4.2
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, mul_comm]
  have hPdeg : ∑ s ∈ P, G.degree s = 5 * P.card := by
    have hpt : ∀ s ∈ P, G.degree s = 5 := by
      intro s hs
      rw [hPdef, Finset.mem_filter] at hs
      exact hs.2.1
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, mul_comm]
  have hSPdeg : ∑ v ∈ SP, G.degree v = 4 * O.card + 5 * P.card := by
    rw [hSPdef, Finset.sum_union hOPdisj, hOdeg, hPdeg]
  have hNHsum : ∑ w ∈ NH, G.degree w + ∑ v ∈ SP, G.degree v
      = ∑ h ∈ hubSet G, G.degree h := by
    rw [hNHdef]
    exact Finset.sum_sdiff hSPsubHub
  rw [ht4]
  omega

open Classical in
/-- **The `(4,5)` decorated-edge independence.**  In a never-firing starved census
(`m = 2(n−2)`, `δ ≥ 3`) at `n ≥ 39`, a degree-`4` owner `o` (carrying a twin) and a saturated
degree-`5` hub `s` (owning exactly `2` twins) are non-adjacent.  If they were adjacent: a shared
twin makes `{o, s, t}` a degree-`(4,5,3)` triangle (`Σdeg = 12 = 4·3`) firing `master_cycle_fires`
(`n ≥ 19`); distinct twins fire the `(4,5)` decorated edge `deco_edge_moat_fires`
(`9·(4 + 5) = 81 ≤ n + 42`, i.e. `n ≥ 39`) — either way contradicting `¬ algConn G ≤ 2`. -/
theorem owner_sat_independence {n : ℕ} [Nonempty (Fin n)] (hn : 39 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (o s : Fin n) (hdo : G.degree o = 4) (hds : G.degree s = 5)
    (hoNE : (G.neighborFinset o ∩ isoTwins G).Nonempty)
    (hscard : (G.neighborFinset s ∩ isoTwins G).card = 2) :
    ¬ G.Adj o s := by
  classical
  intro hadj
  apply hnf
  obtain ⟨t, ht⟩ := hoNE
  rw [Finset.mem_inter] at ht
  obtain ⟨htN, htIso⟩ := ht
  have hot : G.Adj o t := (G.mem_neighborFinset o t).mp htN
  have hdt : G.degree t = 3 := (mem_isoTwins.mp htIso).1
  have hne_st : s ≠ t := by intro h; rw [h, hdt] at hds; omega
  set Ks := G.neighborFinset s ∩ isoTwins G with hKsdef
  by_cases htin : t ∈ Ks
  · have hst : G.Adj s t := by
      rw [hKsdef, Finset.mem_inter] at htin
      exact (G.mem_neighborFinset s t).mp htin.1
    have hne_os : o ≠ s := by intro h; rw [h, hds] at hdo; omega
    have hne_ot : o ≠ t := by intro h; rw [h, hdt] at hdo; omega
    have e0 : (![o, s, t] : Fin 3 → Fin n) 0 = o := rfl
    have e1 : (![o, s, t] : Fin 3 → Fin n) 1 = s := rfl
    have e2 : (![o, s, t] : Fin 3 → Fin n) 2 = t := rfl
    refine master_cycle_fires (k := 3) (by norm_num) G hm h3 ![o, s, t] ?_ ?_ ?_ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> rfl
    · intro i
      fin_cases i
      · change G.Adj o s; exact hadj
      · change G.Adj s t; exact hst
      · change G.Adj t o; exact hot.symm
    · have hsplit : (∑ i : ZMod 3, G.degree (![o, s, t] i))
          = G.degree o + G.degree s + G.degree t := by
        have h := Fin.sum_univ_three (fun i : Fin 3 => G.degree (![o, s, t] i))
        rw [e0, e1, e2] at h
        exact h
      rw [hsplit, hdo, hds, hdt]
    · have hsplit : (∑ i : ZMod 3, (G.degree (![o, s, t] i) - 1))
          = (G.degree o - 1) + (G.degree s - 1) + (G.degree t - 1) := by
        have h := Fin.sum_univ_three (fun i : Fin 3 => G.degree (![o, s, t] i) - 1)
        rw [e0, e1, e2] at h
        exact h
      rw [hsplit, hdo, hds, hdt]; omega
  · refine deco_edge_moat_fires G hm h3 o s {t} Ks hadj ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      rw [G.mem_neighborFinset]; exact hot
    · intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx; exact hdt
    · rw [Finset.card_singleton, hdo]
    · rw [hKsdef]; exact Finset.inter_subset_left
    · intro x hx
      rw [hKsdef, Finset.mem_inter] at hx
      exact (mem_isoTwins.mp hx.2).1
    · rw [hscard, hds]
    · intro hoKs
      rw [hKsdef, Finset.mem_inter] at hoKs
      have := (mem_isoTwins.mp hoKs.2).1
      omega
    · rw [Finset.mem_singleton]; exact hne_st
    · rw [Finset.disjoint_singleton_left]; exact htin
    · rw [hdo, hds]; omega

open Classical in
/-- **N5 — the per-`p` sharpened owner-choke (assembled row).**  A never-firing starved census
(`m = 2(n−2)`, `δ ≥ 3`, `hs0`) on `n ≥ 48` satisfies the sharpened choke
`7·t₄ + 8·p + 3·X + 32 ≤ 4n`.  The degree-`4` twin cap is the contrapositive of the star moat
(`starved_cap` at `deg = 4`), the `(4,4)` independence is `owner_independence`, and the `(4,5)`
independence is `owner_sat_independence`; the `(5,5)` independence `hindep55` is threaded as the
single moat-provenance hypothesis (its shared-single-twin subcase requires a shared-twin
decorated-edge moat, a separate node — `scratchpad/ahl_import.md` §1.3/§4.4). -/
theorem p_choke_row {n : ℕ} [Nonempty (Fin n)] (hn : 48 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (hnf : ¬ algConn G ≤ 2)
    (hindep55 : ∀ s₁ s₂ : Fin n, G.degree s₁ = 5 →
        (G.neighborFinset s₁ ∩ isoTwins G).card = 2 → G.degree s₂ = 5 →
        (G.neighborFinset s₂ ∩ isoTwins G).card = 2 → s₁ ≠ s₂ → ¬ G.Adj s₁ s₂) :
    7 * (∑ h ∈ (hubSet G).filter (fun h => G.degree h = 4),
            (G.neighborFinset h ∩ isoTwins G).card)
        + 8 * ((hubSet G).filter (fun h => G.degree h = 5 ∧
            (G.neighborFinset h ∩ isoTwins G).card = 2)).card
        + 3 * excessX n G + 32 ≤ 4 * n := by
  have hcap4 : ∀ h : Fin n, G.degree h = 4 →
      (G.neighborFinset h ∩ isoTwins G).card ≤ 1 := by
    intro h hh
    have hc := starved_cap G hm h3 hnf h (by rw [hh]; omega)
    rw [hh] at hc
    omega
  have hindep44 : ∀ o₁ o₂ : Fin n, G.degree o₁ = 4 → G.degree o₂ = 4 →
      (G.neighborFinset o₁ ∩ isoTwins G).Nonempty →
      (G.neighborFinset o₂ ∩ isoTwins G).Nonempty → o₁ ≠ o₂ → ¬ G.Adj o₁ o₂ := by
    intro o₁ o₂ ho1 ho2 hn1 hn2 _hne
    obtain ⟨t₁, ht1⟩ := hn1
    obtain ⟨t₂, ht2⟩ := hn2
    rw [Finset.mem_inter, G.mem_neighborFinset] at ht1 ht2
    exact owner_independence (by omega) G hm h3 hnf o₁ o₂ t₁ t₂ ho1 ho2 ht1.1
      (mem_isoTwins.mp ht1.2).1 ht2.1 (mem_isoTwins.mp ht2.2).1
  have hindep45 : ∀ o s : Fin n, G.degree o = 4 →
      (G.neighborFinset o ∩ isoTwins G).Nonempty → G.degree s = 5 →
      (G.neighborFinset s ∩ isoTwins G).card = 2 → ¬ G.Adj o s := by
    intro o s ho hoNE hs hscard
    exact owner_sat_independence (by omega) G hm h3 hnf o s ho hs hoNE hscard
  exact p_choke_count (by omega) G hm h3 hs0 hcap4 hindep44 hindep45 hindep55

/-! ## The shared-twin decorated-edge moat and the unconditional row

Reworks the decorated-edge moat for the overlapping-twin case and discharges the
last hypothesis of the per-`p` owner-choke. `deco_edge_shared_twin_fires`: adjacent
hubs sharing exactly one twin fire at `9·(deg u + deg v) ≤ n + 56` (the shared
twin has external budget `1`, so the threshold is easier than the disjoint
`n + 42`). `sat_sat_independence`: two adjacent saturated degree-5 hubs are
non-adjacent at `n ≥ 48`. `p_choke_row_unconditional`: the census-only per-`p`
choke row, discharging `hindep55` via `sat_sat_independence`. -/

open Classical in
private theorem deco_edge_shared_twin_fires_hsliceU : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u v _
  : Fin n)
  (Ku Kv : Finset (Fin n)) (_ : G.Adj u v) (_ : Ku ⊆ G.neighborFinset u) (_ : #Ku =
    G.degree u - 3)
  (_ : #Kv = G.degree v - 3) (_ : v ∉ Ku),
  let _ := Classical.decEq (Fin n);
  ∀ (_ : 3 ≤ G.degree u) (_ : 3 ≤ G.degree v) (_ : u ≠ v) (_ : 1 ≤ #Ku) (_
    : 1 ≤ #Kv)
    (S₁ : Finset (Fin n)) (_ : S₁ = insert u (insert v (Ku ∪ Kv))), #(G.neighborFinset u \
      S₁) ≤ 2 := by
  classical
  intro n G u v t₀ Ku Kv huv hKusub hKucard hKvcard hvKu this hdeg3u hdeg3v huv' hKupos hKvpos S₁
    hS1def
  have hivku_nb : insert v Ku ⊆ G.neighborFinset u :=
    Finset.insert_subset ((G.mem_neighborFinset u v).mpr huv) hKusub
  have hivku_S1 : insert v Ku ⊆ S₁ := by
    refine Finset.insert_subset ?_ ?_
    · rw [hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _)
    · intro x hxKu
      rw [hS1def]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_union_left Kv hxKu))
  have hsub : G.neighborFinset u \ S₁ ⊆ G.neighborFinset u \ insert v Ku :=
    Finset.sdiff_subset_sdiff (le_refl _) hivku_S1
  calc (G.neighborFinset u \ S₁).card
      ≤ (G.neighborFinset u \ insert v Ku).card := Finset.card_le_card hsub
    _ = (G.neighborFinset u).card - (insert v Ku).card :=
        Finset.card_sdiff_of_subset hivku_nb
    _ = G.degree u - (insert v Ku).card := by rw [G.card_neighborFinset_eq_degree]
    _ = 2 := by rw [Finset.card_insert_of_notMem hvKu, hKucard]; omega

open Classical in
private theorem deco_edge_shared_twin_fires_hsliceV : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u v _
  : Fin n)
  (Ku Kv : Finset (Fin n)) (_ : G.Adj u v) (_ : #Ku = G.degree u - 3) (_ : Kv ⊆
    G.neighborFinset v)
  (_ : #Kv = G.degree v - 3) (_ : u ∉ Kv),
  let _ := Classical.decEq (Fin n);
  ∀ (_ : 3 ≤ G.degree u) (_ : 3 ≤ G.degree v) (_ : u ≠ v) (_ : 1 ≤ #Ku) (_
    : 1 ≤ #Kv)
    (S₁ : Finset (Fin n)) (_ : S₁ = insert u (insert v (Ku ∪ Kv))), #(G.neighborFinset v \
      S₁) ≤ 2 := by
  classical
  intro n G u v t₀ Ku Kv huv hKucard hKvsub hKvcard huKv this hdeg3u hdeg3v huv' hKupos hKvpos S₁
    hS1def
  have hiukv_nb : insert u Kv ⊆ G.neighborFinset v :=
    Finset.insert_subset ((G.mem_neighborFinset v u).mpr huv.symm) hKvsub
  have hiukv_S1 : insert u Kv ⊆ S₁ := by
    refine Finset.insert_subset ?_ ?_
    · rw [hS1def]; exact Finset.mem_insert_self u _
    · intro x hxKv
      rw [hS1def]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_union_right Ku hxKv))
  have hsub : G.neighborFinset v \ S₁ ⊆ G.neighborFinset v \ insert u Kv :=
    Finset.sdiff_subset_sdiff (le_refl _) hiukv_S1
  calc (G.neighborFinset v \ S₁).card
      ≤ (G.neighborFinset v \ insert u Kv).card := Finset.card_le_card hsub
    _ = (G.neighborFinset v).card - (insert u Kv).card :=
        Finset.card_sdiff_of_subset hiukv_nb
    _ = G.degree v - (insert u Kv).card := by rw [G.card_neighborFinset_eq_degree]
    _ = 2 := by rw [Finset.card_insert_of_notMem huKv, hKvcard]; omega

open Classical in
private theorem deco_edge_shared_twin_fires_hsliceTu : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u v :
  Fin n)
  (Ku Kv : Finset (Fin n)) (_ : Ku ⊆ G.neighborFinset u) (_ : ∀ t ∈ Ku, G.degree t = 3),
  let _ := Classical.decEq (Fin n);
  ∀ (S₁ : Finset (Fin n)) (_ : S₁ = insert u (insert v (Ku ∪ Kv))), ∀ t ∈ Ku,
    #(G.neighborFinset t \ S₁) ≤ 2 := by
  classical
  intro n G u v Ku Kv hKusub hKudeg this S₁ hS1def t htK
  have htNu : t ∈ G.neighborFinset u := hKusub htK
  have hut : G.Adj u t := (G.mem_neighborFinset u t).mp htNu
  have huNt : u ∈ G.neighborFinset t := (G.mem_neighborFinset t u).mpr hut.symm
  have hsub : G.neighborFinset t \ S₁ ⊆ (G.neighborFinset t).erase u := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_erase]
    refine ⟨fun hxu => hx.2 ?_, hx.1⟩
    rw [hS1def, hxu]
    exact Finset.mem_insert_self u _
  calc (G.neighborFinset t \ S₁).card
      ≤ ((G.neighborFinset t).erase u).card := Finset.card_le_card hsub
    _ = G.degree t - 1 := by
        rw [Finset.card_erase_of_mem huNt, G.card_neighborFinset_eq_degree]
    _ = 2 := by rw [hKudeg t htK]

open Classical in
private theorem deco_edge_shared_twin_fires_hsliceTv : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u v :
  Fin n)
  (Ku Kv : Finset (Fin n)) (_ : Kv ⊆ G.neighborFinset v) (_ : ∀ t ∈ Kv, G.degree t = 3),
  let _ := Classical.decEq (Fin n);
  ∀ (S₁ : Finset (Fin n)) (_ : S₁ = insert u (insert v (Ku ∪ Kv))), ∀ t ∈ Kv,
    #(G.neighborFinset t \ S₁) ≤ 2 := by
  classical
  intro n G u v Ku Kv hKvsub hKvdeg this S₁ hS1def t htK
  have htNv : t ∈ G.neighborFinset v := hKvsub htK
  have hvt : G.Adj v t := (G.mem_neighborFinset v t).mp htNv
  have hvNt : v ∈ G.neighborFinset t := (G.mem_neighborFinset t v).mpr hvt.symm
  have hsub : G.neighborFinset t \ S₁ ⊆ (G.neighborFinset t).erase v := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_erase]
    refine ⟨fun hxv => hx.2 ?_, hx.1⟩
    rw [hS1def, hxv]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _)
  calc (G.neighborFinset t \ S₁).card
      ≤ ((G.neighborFinset t).erase v).card := Finset.card_le_card hsub
    _ = G.degree t - 1 := by
        rw [Finset.card_erase_of_mem hvNt, G.card_neighborFinset_eq_degree]
    _ = 2 := by rw [hKvdeg t htK]

open Classical in
private theorem deco_edge_shared_twin_fires_hsliceT0 : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u v t₀
  : Fin n)
  (Ku Kv : Finset (Fin n)) (_ : G.Adj u v) (_ : Ku ⊆ G.neighborFinset u) (_ : #Ku =
    G.degree u - 3)
  (_ : Kv ⊆ G.neighborFinset v) (_ : #Kv = G.degree v - 3) (_ : u ∉ Kv) (_ : v ∉
    Ku)
  (_ : 9 * (G.degree u + G.degree v) ≤ n + 56) (_ : t₀ ∈ Ku) (_ : t₀ ∈ Kv),
  let _ := Classical.decEq (Fin n);
  ∀ (_ : 3 ≤ G.degree u) (_ : 3 ≤ G.degree v) (_ : u ≠ v) (_ : G.degree t₀ = 3)
    (_ : u ∉ Ku)
    (_ : v ∉ Kv) (S₁ : Finset (Fin n)) (_ : S₁ = insert u (insert v (Ku ∪ Kv))),
    let F := (S₁.biUnion fun x => G.neighborFinset x) \ S₁;
    ∀ (_ : F = (S₁.biUnion fun x => G.neighborFinset x) \ S₁),
      let S₂ := (S₁ ∪ F)ᶜ;
      ∀ (_ : S₂ = (S₁ ∪ F)ᶜ) (_ : u ∉ insert v (Ku ∪ Kv)) (_ : v ∉ Ku ∪ Kv)
        (_ : #S₁ = G.degree u + G.degree v - 5) (_ : S₁.Nonempty) (_ : u ∉ F) (_ : v
          ∉ F)
        (_ : Disjoint S₁ F) (_ : #S₂ = n - (#S₁ + #F)) (_ : #(G.neighborFinset
          u \ S₁) ≤ 2)
        (_ : #(G.neighborFinset v \ S₁) ≤ 2) (_ : ∀ t ∈ Ku, #(G.neighborFinset t \
          S₁) ≤ 2)
        (_ : ∀ t ∈ Kv, #(G.neighborFinset t \ S₁) ≤ 2) (_ : ∀ x ∈ S₁,
          #(G.neighborFinset x \ S₁) ≤ 2),
        #(G.neighborFinset t₀ \ S₁) ≤ 1 := by
  classical
  intro n G u v t₀ Ku Kv huv hKusub hKucard hKvsub hKvcard huKv hvKu hfire ht0Ku ht0Kv this hdeg3u
    hdeg3v huv' hdt0 huKu hvKv S₁ hS1def F hFdef S₂ hS2def hu_notin hv_notin hS1card hS1ne huF hvF
    hdisjS1F hS2card hsliceU hsliceV hsliceTu hsliceTv hslice
  have hut0 : G.Adj u t₀ := (G.mem_neighborFinset u t₀).mp (hKusub ht0Ku)
  have hvt0 : G.Adj v t₀ := (G.mem_neighborFinset v t₀).mp (hKvsub ht0Kv)
  have huNt0 : u ∈ G.neighborFinset t₀ := (G.mem_neighborFinset t₀ u).mpr hut0.symm
  have hvNt0 : v ∈ G.neighborFinset t₀ := (G.mem_neighborFinset t₀ v).mpr hvt0.symm
  have huvsub : ({u, v} : Finset (Fin n)) ⊆ G.neighborFinset t₀ := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact huNt0
    · exact hvNt0
  have huvS1 : ({u, v} : Finset (Fin n)) ⊆ S₁ := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxu | hxv
    · rw [hxu, hS1def]; exact Finset.mem_insert_self u _
    · rw [hxv, hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _)
  have hsub : G.neighborFinset t₀ \ S₁ ⊆ G.neighborFinset t₀ \ {u, v} :=
    Finset.sdiff_subset_sdiff (le_refl _) huvS1
  calc (G.neighborFinset t₀ \ S₁).card
      ≤ (G.neighborFinset t₀ \ {u, v}).card := Finset.card_le_card hsub
    _ = G.degree t₀ - 2 := by
        rw [Finset.card_sdiff_of_subset huvsub, G.card_neighborFinset_eq_degree,
          Finset.card_pair_eq_two_iff.mpr huv']
    _ = 1 := by rw [hdt0]

open Classical in
private theorem deco_edge_shared_twin_fires_he2 : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (_ : ∀ (w :
  Fin n), 3 ≤ G.degree w)
  (u v _ : Fin n) (Ku Kv : Finset (Fin n)) (_ : #Ku = G.degree u - 3) (_ : #Kv =
    G.degree v - 3)
  (_ : 9 * (G.degree u + G.degree v) ≤ n + 56),
  let _ := Classical.decEq (Fin n);
  ∀ (_ : 3 ≤ G.degree u) (_ : 3 ≤ G.degree v) (_ : u ≠ v) (_ : 1 ≤ #Ku) (_
    : 1 ≤ #Kv)
    (_ : 8 ≤ n),
    let S₁ := insert u (insert v (Ku ∪ Kv));
    ∀ (F : Finset (Fin n)) (_ : F = (S₁.biUnion fun x => G.neighborFinset x) \ S₁),
      let S₂ := (S₁ ∪ F)ᶜ;
      ∀ (_ : S₂ = (S₁ ∪ F)ᶜ) (_ : #S₁ = G.degree u + G.degree v - 5) (_ : #S₂ = n
        - (#S₁ + #F))
        (_ : ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = ∑ a ∈ A,
          #(G.neighborFinset a ∩ C))
        (_ : ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = #({q ∈ C ×ˢ A |
          G.Adj q.1 q.2}))
        (_ : ∑ x ∈ S₁, #(G.neighborFinset x \ S₁) + 1 ≤ 2 * #S₁) (_ : #F + 1 ≤ 2 * #S₁)
        (_ : ∑ w ∈ F, (G.degree w - 3) ≤ n - 8 - (G.degree u - 3) - (G.degree v - 3)),
        #({q ∈ S₂ ×ˢ F | G.Adj q.1 q.2}) ≤ 2 * #S₂ := by
  classical
  intro n G h3 u v t₀ Ku Kv hKucard hKvcard hfire this hdeg3u hdeg3v huv' hKupos hKvpos hn8 S₁ F
    hFdef S₂ hS2def hS1card hS2card hcnt htrans hsumbound hFcard hexc
  rw [htrans S₂ F, hcnt F S₂]
  have hbound : ∀ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 := by
    intro w hw
    obtain ⟨a, haS1, haw⟩ : ∃ a ∈ S₁, G.Adj a w := by
      have hwF := hw
      rw [hFdef, Finset.mem_sdiff, Finset.mem_biUnion] at hwF
      obtain ⟨⟨a, haS1, hwa⟩, _⟩ := hwF
      exact ⟨a, haS1, (G.mem_neighborFinset a w).mp hwa⟩
    have haNw : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
    have haS2 : a ∉ S₂ := by
      rw [hS2def, Finset.mem_compl, not_not]
      exact Finset.mem_union_left F haS1
    have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_erase]
      refine ⟨?_, hx.1⟩
      rintro rfl
      exact haS2 hx.2
    calc (G.neighborFinset w ∩ S₂).card
        ≤ ((G.neighborFinset w).erase a).card := Finset.card_le_card hsub
      _ = G.degree w - 1 := by
          rw [Finset.card_erase_of_mem haNw, G.card_neighborFinset_eq_degree]
  have hpt : ∀ w ∈ F, G.degree w - 1 = (G.degree w - 3) + 2 := by
    intro w _
    have := h3 w
    omega
  calc ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card
      ≤ ∑ w ∈ F, (G.degree w - 1) := Finset.sum_le_sum hbound
    _ = ∑ w ∈ F, (G.degree w - 3) + F.card * 2 := by
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
          smul_eq_mul]
    _ ≤ 2 * S₂.card := by omega

open Classical in
private theorem deco_edge_shared_twin_fires_hcnt_step1 : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (_ :
  Fin n),
  let _ : DecidableEq (Fin n) := Classical.decEq (Fin n);
  ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = ∑ a ∈ A, #(G.neighborFinset a ∩ C)
    := by
  classical
  intro n G v this A C
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hset : G.neighborFinset a ∩ C = C.filter (fun v => G.Adj a v) := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact and_comm
  rw [hset, Finset.card_filter]

open Classical in
private theorem deco_edge_shared_twin_fires_htrans_step1 : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (A
  C : Finset (Fin n)),
  #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = #({q ∈ C ×ˢ A | G.Adj q.1 q.2}) := by
  classical
  intro n G A C
  refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
    exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  · intro q _ r _ hqr
    exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
  · intro q hq
    refine ⟨(q.2, q.1), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
    exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩

open Classical in
private theorem deco_edge_shared_twin_fires_hsliceT0_step1 : ∀ {n : ℕ} (G : SimpleGraph (Fin n))
  (u v t₀ : Fin n)
  (Ku Kv : Finset (Fin n)) (_ : G.Adj u v) (_ : Ku ⊆ G.neighborFinset u) (_ : #Ku =
    G.degree u - (3 : ℕ))
  (_ : Kv ⊆ G.neighborFinset v) (_ : #Kv = G.degree v - (3 : ℕ)) (_ : u ∉ Kv) (_
    : v ∉ Ku)
  (_ : (9 : ℕ) * (G.degree u + G.degree v) ≤ n + (56 : ℕ)) (_ : t₀ ∈ Ku) (_ : t₀ ∈ Kv),
  let _ : DecidableEq (Fin n) := Classical.decEq (Fin n);
  ∀ (_ : (3 : ℕ) ≤ G.degree u) (_ : (3 : ℕ) ≤ G.degree v) (_ : u ≠ v) (_ :
    G.degree t₀ = (3 : ℕ))
    (_ : u ∉ Ku) (_ : v ∉ Kv) (S₁ : Finset (Fin n)) (_ : S₁ = insert u (insert v (Ku ∪
      Kv))),
    let F : Finset (Fin n) := (S₁.biUnion fun x => G.neighborFinset x) \ S₁;
    ∀ (_ : F = (S₁.biUnion fun x => G.neighborFinset x) \ S₁),
      let S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ;
      ∀ (_ : S₂ = (S₁ ∪ F)ᶜ) (_ : u ∉ insert v (Ku ∪ Kv)) (_ : v ∉ Ku ∪ Kv)
        (_ : #S₁ = G.degree u + G.degree v - (5 : ℕ)) (_ : S₁.Nonempty) (_ : u ∉ F)
          (_ : v ∉ F)
        (_ : Disjoint S₁ F) (_ : #S₂ = n - (#S₁ + #F)) (_ : #(G.neighborFinset
          u \ S₁) ≤ (2 : ℕ))
        (_ : #(G.neighborFinset v \ S₁) ≤ (2 : ℕ)) (_ : ∀ t ∈ Ku, #(G.neighborFinset
          t \ S₁) ≤ (2 : ℕ))
        (_ : ∀ t ∈ Kv, #(G.neighborFinset t \ S₁) ≤ (2 : ℕ))
        (_ : ∀ x ∈ S₁, #(G.neighborFinset x \ S₁) ≤ (2 : ℕ)), #(G.neighborFinset t₀ \ S₁) ≤
          (1 : ℕ) := by
  classical
  intro n G u v t₀ Ku Kv huv hKusub hKucard hKvsub hKvcard huKv hvKu hfire ht0Ku ht0Kv this hdeg3u
    hdeg3v huv' hdt0 huKu hvKv S₁ hS1def F hFdef S₂ hS2def hu_notin hv_notin hS1card hS1ne huF hvF
    hdisjS1F hS2card hsliceU hsliceV hsliceTu hsliceTv hslice
  exact deco_edge_shared_twin_fires_hsliceT0 (n := n) (G := G) (u := u) (v := v) (t₀ := t₀) (Ku
    := Ku) (Kv := Kv) (huv) (hKusub) (hKucard) (hKvsub)
    (hKvcard) (huKv) (hvKu) (hfire) (ht0Ku) (ht0Kv) (hdeg3u) (hdeg3v) (huv') (hdt0) (huKu)
    (hvKv) (S₁ := S₁) (hS1def) (hFdef) (hS2def) (hu_notin) (hv_notin) (hS1card) (hS1ne) (huF)
      (hvF) (hdisjS1F) (hS2card) (hsliceU) (hsliceV) (hsliceTu) (hsliceTv) (hslice)

open Classical in
private theorem deco_edge_shared_twin_fires_hterm_step1 : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u v
  : Fin n)
  (Ku Kv : Finset (Fin n)),
  let _ : DecidableEq (Fin n) := Classical.decEq (Fin n);
  let S₁ : Finset (Fin n) := insert u (insert v (Ku ∪ Kv));
  ∀ (F : Finset (Fin n)) (_ : F = (S₁.biUnion fun x => G.neighborFinset x) \ S₁)
    (_ : ∀ x ∈ S₁, #(G.neighborFinset x \ S₁) ≤ (2 : ℕ)), ∀ a ∈ S₁, #(G.neighborFinset a ∩ F)
      ≤ (2 : ℕ) := by
  classical
  intro n G u v Ku Kv this S₁ F hFdef hslice a ha
  have hsub : G.neighborFinset a ∩ F ⊆ G.neighborFinset a \ S₁ := by
    intro x hx
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_sdiff]
    refine ⟨hx.1, ?_⟩
    have hxF := hx.2
    rw [hFdef, Finset.mem_sdiff] at hxF
    exact hxF.2
  exact le_trans (Finset.card_le_card hsub) (hslice a ha)

open Classical in
private theorem deco_edge_shared_twin_fires_hsumbound_step1 : ∀ {n : ℕ} (G : SimpleGraph (Fin n))
  (u v t₀ : Fin n)
  (Ku Kv : Finset (Fin n)),
  let _ : DecidableEq (Fin n) := Classical.decEq (Fin n);
  let S₁ : Finset (Fin n) := insert u (insert v (Ku ∪ Kv));
  ∀ (_ : #S₁ = G.degree u + G.degree v - (5 : ℕ)) (_ : ∀ x ∈ S₁, #(G.neighborFinset x \
    S₁) ≤ (2 : ℕ))
    (_ : #(G.neighborFinset t₀ \ S₁) ≤ (1 : ℕ)) (_ : t₀ ∈ S₁),
    ∑ x ∈ S₁, #(G.neighborFinset x \ S₁) + (1 : ℕ) ≤ (2 : ℕ) * #S₁ := by
  classical
  intro n G u v t₀ Ku Kv this S₁ hS1card hslice hsliceT0 ht0S1
  have hsplit : (G.neighborFinset t₀ \ S₁).card
      + ∑ x ∈ S₁.erase t₀, (G.neighborFinset x \ S₁).card
      = ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card :=
    Finset.add_sum_erase S₁ (fun x => (G.neighborFinset x \ S₁).card) ht0S1
  have herase : ∑ x ∈ S₁.erase t₀, (G.neighborFinset x \ S₁).card
      ≤ 2 * (S₁.erase t₀).card := by
    calc ∑ x ∈ S₁.erase t₀, (G.neighborFinset x \ S₁).card
        ≤ ∑ _x ∈ S₁.erase t₀, 2 :=
          Finset.sum_le_sum (fun x hx => hslice x (Finset.mem_of_mem_erase hx))
      _ = 2 * (S₁.erase t₀).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hcarderase : (S₁.erase t₀).card = S₁.card - 1 := Finset.card_erase_of_mem ht0S1
  have hS1pos : 1 ≤ S₁.card := Finset.card_pos.mpr ⟨t₀, ht0S1⟩
  omega

open Classical in
private theorem deco_edge_shared_twin_fires_hFcard_step1 : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u
  v _ : Fin n)
  (Ku Kv : Finset (Fin n)),
  let _ : DecidableEq (Fin n) := Classical.decEq (Fin n);
  let S₁ : Finset (Fin n) := insert u (insert v (Ku ∪ Kv));
  ∀ (F : Finset (Fin n)) (_ : F = (S₁.biUnion fun x => G.neighborFinset x) \ S₁)
    (_ : #S₁ = G.degree u + G.degree v - (5 : ℕ))
    (_ : ∑ x ∈ S₁, #(G.neighborFinset x \ S₁) + (1 : ℕ) ≤ (2 : ℕ) * #S₁), #F + (1 : ℕ) ≤
      (2 : ℕ) * #S₁ := by
  classical
  intro n G u v t₀ Ku Kv this S₁ F hFdef hS1card hsumbound
  have hFsub2 : F ⊆ S₁.biUnion (fun x => G.neighborFinset x \ S₁) := by
    intro y hy
    rw [hFdef, Finset.mem_sdiff] at hy
    obtain ⟨hyNS, hyS1⟩ := hy
    rw [Finset.mem_biUnion] at hyNS ⊢
    obtain ⟨x, hxS1, hyx⟩ := hyNS
    exact ⟨x, hxS1, Finset.mem_sdiff.mpr ⟨hyx, hyS1⟩⟩
  have hFle : F.card ≤ ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card :=
    le_trans (Finset.card_le_card hFsub2) Finset.card_biUnion_le
  omega

open Classical in
private theorem deco_edge_shared_twin_fires_hexc_step1 : ∀ {n : ℕ} (G : SimpleGraph (Fin n))
  (_ : #G.edgeFinset = (2 : ℕ) * (n - (2 : ℕ))) (_ : ∀ (w : Fin n), (3 : ℕ) ≤ G.degree w) (u v
    _ : Fin n)
  (Ku Kv : Finset (Fin n)),
  let _ : DecidableEq (Fin n) := Classical.decEq (Fin n);
  ∀ (_ : u ≠ v) (_ : (8 : ℕ) ≤ n),
    let S₁ : Finset (Fin n) := insert u (insert v (Ku ∪ Kv));
    let F : Finset (Fin n) := (S₁.biUnion fun x => G.neighborFinset x) \ S₁;
    ∀ (_ : F ⊆ (univ.erase u).erase v),
      ∑ w ∈ F, (G.degree w - (3 : ℕ)) ≤ n - (8 : ℕ) - (G.degree u - (3 : ℕ)) - (G.degree v - (3 :
        ℕ)) := by
  classical
  intro n G hm h3 u v t₀ Ku Kv this huv' hn8 S₁ F hFsubErase
  have hle : ∑ w ∈ F, (G.degree w - 3)
      ≤ ∑ w ∈ (Finset.univ.erase u).erase v, (G.degree w - 3) :=
    Finset.sum_le_sum_of_subset hFsubErase
  have hsplit1 : (G.degree u - 3) + ∑ w ∈ Finset.univ.erase u, (G.degree w - 3)
      = ∑ w : Fin n, (G.degree w - 3) :=
    Finset.add_sum_erase _ (fun w => G.degree w - 3) (Finset.mem_univ u)
  have hsplit2 : (G.degree v - 3) + ∑ w ∈ (Finset.univ.erase u).erase v, (G.degree w - 3)
      = ∑ w ∈ Finset.univ.erase u, (G.degree w - 3) :=
    Finset.add_sum_erase _ (fun w => G.degree w - 3)
      (Finset.mem_erase.mpr ⟨huv'.symm, Finset.mem_univ v⟩)
  have htot : ∑ w : Fin n, (G.degree w - 3) = n - 8 := total_excess_eq hn8 G hm h3
  omega

open Classical in
private theorem deco_edge_shared_twin_fires_hnc_step1 : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u v :
  Fin n)
  (Ku Kv : Finset (Fin n)),
  let _ : DecidableEq (Fin n) := Classical.decEq (Fin n);
  let S₁ : Finset (Fin n) := insert u (insert v (Ku ∪ Kv));
  ∀ (F : Finset (Fin n)) (_ : F = (S₁.biUnion fun x => G.neighborFinset x) \ S₁),
    let S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ;
    ∀ (_ : S₂ = (S₁ ∪ F)ᶜ), ∀ a ∈ S₁, ∀ w ∈ S₂, ¬G.Adj a w := by
  classical
  intro n G u v Ku Kv this S₁ F hFdef S₂ hS2def a ha w hw hadj
  rw [hS2def, Finset.mem_compl] at hw
  have hwnotS1 : w ∉ S₁ := fun hh => hw (Finset.mem_union_left F hh)
  have hwnotF : w ∉ F := fun hh => hw (Finset.mem_union_right S₁ hh)
  apply hwnotF
  rw [hFdef, Finset.mem_sdiff]
  refine ⟨?_, hwnotS1⟩
  rw [Finset.mem_biUnion]
  exact ⟨a, ha, (G.mem_neighborFinset a w).mpr hadj⟩

open Classical in
private theorem deco_edge_shared_twin_fires_hFeq_step1 : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u v
  : Fin n)
  (Ku Kv : Finset (Fin n)),
  let _ : DecidableEq (Fin n) := Classical.decEq (Fin n);
  let S₁ : Finset (Fin n) := insert u (insert v (Ku ∪ Kv));
  let F : Finset (Fin n) := (S₁.biUnion fun x => G.neighborFinset x) \ S₁;
  ∀ (S₂ : Finset (Fin n)) (_ : S₂ = (S₁ ∪ F)ᶜ) (_ : Disjoint S₁ F), (S₁ ∪ S₂)ᶜ = F := by
  classical
  intro n G u v Ku Kv this S₁ F S₂ hS2def hdisjS1F
  ext w
  constructor
  · intro hw
    rw [Finset.mem_compl, Finset.mem_union, not_or] at hw
    obtain ⟨hwS1, hwS2⟩ := hw
    rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hwS2
    rcases hwS2 with hh | hh
    · exact absurd hh hwS1
    · exact hh
  · intro hw
    rw [Finset.mem_compl, Finset.mem_union, not_or]
    exact ⟨Finset.disjoint_right.mp hdisjS1F hw,
      by rw [hS2def, Finset.mem_compl, not_not]; exact Finset.mem_union_right S₁ hw⟩

open Classical in
/-- **The shared-twin decorated-edge moat certificate.**  A graph on `Fin n` with `2(n−2)` edges,
minimum degree `≥ 3`, adjacent hubs `u, v`, and twin sets `Ku ⊆ N(u)`, `Kv ⊆ N(v)` of degree-`3`
vertices with `|Ku| = deg u − 3`, `|Kv| = deg v − 3` (avoiding the opposite hub) sharing *exactly
one* common twin (`Ku ∩ Kv = {t₀}`) has `algConn G ≤ 2` whenever `9·(deg u + deg v) ≤ n + 56`.

Instantiate the two-cluster law with the tie-block `S₁ = {u, v} ∪ Ku ∪ Kv` (`|S₁| = deg u +
deg v − 5`) against the bulk `S₂ = (S₁ ∪ F)ᶜ`, `F = (⋃_{x ∈ S₁} N(x)) ∖ S₁` the moat: every hub
slice loses `deg − 2` internally (budget `2`) and every twin loses its hub (budget `2`), except the
shared twin `t₀` which loses *both* hubs (budget `1`), so `|F| + 1 ≤ 2·|S₁|`; the pair-credited
excess ledger then gives `∂₂ ≤ 2·|S₂|` and the Fiedler cut condition closes by `ring`. -/
theorem deco_edge_shared_twin_fires {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ w : Fin n, 3 ≤ G.degree w) (u v t₀ : Fin n) (Ku Kv : Finset (Fin n))
    (huv : G.Adj u v)
    (hKusub : Ku ⊆ G.neighborFinset u) (hKudeg : ∀ t ∈ Ku, G.degree t = 3)
    (hKucard : Ku.card = G.degree u - 3)
    (hKvsub : Kv ⊆ G.neighborFinset v) (hKvdeg : ∀ t ∈ Kv, G.degree t = 3)
    (hKvcard : Kv.card = G.degree v - 3)
    (huKv : u ∉ Kv) (hvKu : v ∉ Ku) (hshare : Ku ∩ Kv = {t₀})
    (hfire : 9 * (G.degree u + G.degree v) ≤ n + 56) :
    algConn G ≤ 2 := by
  classical
  -- process the overlap hypothesis in the canonical `Fin` instance, before switching to
  -- the classical instance the two-cluster law expects
  have ht0mem : t₀ ∈ Ku ∩ Kv := by rw [hshare]; exact Finset.mem_singleton_self t₀
  have ht0Ku : t₀ ∈ Ku := Finset.mem_of_mem_inter_left ht0mem
  have ht0Kv : t₀ ∈ Kv := Finset.mem_of_mem_inter_right ht0mem
  have huniq : ∀ a : Fin n, a ∈ Ku → a ∈ Kv → a = t₀ := by
    intro a ha hb
    have hmem : a ∈ Ku ∩ Kv := Finset.mem_inter.mpr ⟨ha, hb⟩
    rw [hshare] at hmem
    exact Finset.mem_singleton.mp hmem
  let : DecidableEq (Fin n) := Classical.decEq (Fin n)
  have hdeg3u : 3 ≤ G.degree u := h3 u
  have hdeg3v : 3 ≤ G.degree v := h3 v
  have huv' : u ≠ v := G.ne_of_adj huv
  have hdt0 : G.degree t₀ = 3 := hKudeg t₀ ht0Ku
  have hKupos : 1 ≤ Ku.card := Finset.card_pos.mpr ⟨t₀, ht0Ku⟩
  have hKvpos : 1 ≤ Kv.card := Finset.card_pos.mpr ⟨t₀, ht0Kv⟩
  have hn8 : 8 ≤ n := by omega
  have hshare' : Ku ∩ Kv = {t₀} := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, hb⟩
      exact huniq a ha hb
    · rintro rfl
      exact ⟨ht0Ku, ht0Kv⟩
  have huKu : u ∉ Ku := by
    intro hu
    have hmem := hKusub hu
    rw [G.mem_neighborFinset] at hmem
    exact (G.ne_of_adj hmem) rfl
  have hvKv : v ∉ Kv := by
    intro hv
    have hmem := hKvsub hv
    rw [G.mem_neighborFinset] at hmem
    exact (G.ne_of_adj hmem) rfl
  set S₁ : Finset (Fin n) := insert u (insert v (Ku ∪ Kv)) with hS1def
  set F : Finset (Fin n) := (S₁.biUnion (fun x => G.neighborFinset x)) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  have hu_notin : u ∉ insert v (Ku ∪ Kv) := by
    rw [Finset.mem_insert, Finset.mem_union]
    rintro (h | h | h)
    · exact huv' h
    · exact huKu h
    · exact huKv h
  have hv_notin : v ∉ Ku ∪ Kv := by
    rw [Finset.mem_union]
    rintro (h | h)
    · exact hvKu h
    · exact hvKv h
  have hunioncard : (Ku ∪ Kv).card = Ku.card + Kv.card - 1 := by
    have h := Finset.card_union_add_card_inter Ku Kv
    rw [hshare', Finset.card_singleton] at h
    omega
  have hS1card : S₁.card = G.degree u + G.degree v - 5 := by
    rw [hS1def, Finset.card_insert_of_notMem hu_notin,
      Finset.card_insert_of_notMem hv_notin, hunioncard, hKucard, hKvcard]
    omega
  have hS1ne : S₁.Nonempty := by rw [hS1def]; exact Finset.insert_nonempty u _
  have huF : u ∉ F := by
    rw [hFdef]
    intro hmem
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 (by rw [hS1def]; exact Finset.mem_insert_self u _)
  have hvF : v ∉ F := by
    rw [hFdef]
    intro hmem
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 (by rw [hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _))
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [hFdef, Finset.mem_sdiff] at haF
    exact haF.2 ha
  have hS2card : S₂.card = n - (S₁.card + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjS1F]
  have hcnt := deco_edge_shared_twin_fires_hcnt_step1 (n := n) (G := G) (v)
  have htrans := deco_edge_shared_twin_fires_htrans_step1 (n := n) (G := G)
  have hsliceU :=
      deco_edge_shared_twin_fires_hsliceU (n := n) (G := G) (u := u) (v := v) (t₀) (Ku
        := Ku) (Kv := Kv) (huv) (hKusub) (hKucard) (hKvcard)
        (hvKu) (hdeg3u) (hdeg3v) (huv') (hKupos)
        (hKvpos) (S₁ := S₁) (hS1def)
  have hsliceV :=
      deco_edge_shared_twin_fires_hsliceV (n := n) (G := G) (u := u) (v := v) (t₀) (Ku
        := Ku) (Kv := Kv) (huv) (hKucard) (hKvsub) (hKvcard)
        (huKv) (hdeg3u) (hdeg3v) (huv') (hKupos)
        (hKvpos) (S₁ := S₁) (hS1def)
  have hsliceTu :=
      deco_edge_shared_twin_fires_hsliceTu (n := n) (G := G) (u := u) (v := v) (Ku := Ku) (Kv
        := Kv) (hKusub) (hKudeg) (S₁ := S₁) (hS1def)
  have hsliceTv :=
      deco_edge_shared_twin_fires_hsliceTv (n := n) (G := G) (u := u) (v := v) (Ku := Ku) (Kv
        := Kv) (hKvsub) (hKvdeg) (S₁ := S₁) (hS1def)
  have hslice : ∀ x ∈ S₁, (G.neighborFinset x \ S₁).card ≤ 2 := by
    intro x hx
    rw [hS1def, Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hx
    rcases hx with rfl | rfl | hxKu | hxKv
    · exact hsliceU
    · exact hsliceV
    · exact hsliceTu x hxKu
    · exact hsliceTv x hxKv
  have hsliceT0 :=
      deco_edge_shared_twin_fires_hsliceT0_step1 (n := n) (G := G) (u := u) (v := v) (t₀ :=
        t₀) (Ku := Ku) (Kv := Kv) (huv) (hKusub) (hKucard) (hKvsub) (hKvcard) (huKv) (hvKu)
          (hfire) (ht0Ku)
        (ht0Kv) (hdeg3u) (hdeg3v) (huv') (hdt0) (huKu) (hvKv) (S₁ := S₁) (hS1def) (hFdef) (hS2def)
        (hu_notin) (hv_notin) (hS1card) (hS1ne) (huF) (hvF) (hdisjS1F) (hS2card) (hsliceU)
          (hsliceV) (hsliceTu) (hsliceTv) (hslice)
  have hterm :=
      deco_edge_shared_twin_fires_hterm_step1 (n := n) (G := G) (u := u) (v := v) (Ku := Ku)
        (Kv := Kv) (F := F) (hFdef) (hslice)
  have he1 : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₁.card := by
    rw [hcnt S₁ F]
    calc ∑ a ∈ S₁, (G.neighborFinset a ∩ F).card
        ≤ ∑ _a ∈ S₁, 2 := Finset.sum_le_sum hterm
      _ = 2 * S₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have ht0S1 : t₀ ∈ S₁ := by
    rw [hS1def]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_union_left Kv ht0Ku))
  have hsumbound : ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card + 1 ≤ 2 * S₁.card :=
      deco_edge_shared_twin_fires_hsumbound_step1 (n := n) (G := G) (u := u) (v := v) (t₀ :=
        t₀) (Ku := Ku) (Kv := Kv) (hS1card) (hslice) (hsliceT0)
        (ht0S1)
  have hFcard : F.card + 1 ≤ 2 * S₁.card :=
      deco_edge_shared_twin_fires_hFcard_step1 (n := n) (G := G) (u := u) (v := v) (t₀)
        (Ku := Ku) (Kv := Kv) (F := F) (hFdef) (hS1card) (hsumbound)
  have hFsubErase : F ⊆ (Finset.univ.erase u).erase v := by
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.mem_univ x⟩
    · rintro rfl; exact hvF hx
    · rintro rfl; exact huF hx
  have hexc : ∑ w ∈ F, (G.degree w - 3)
      ≤ (n - 8) - (G.degree u - 3) - (G.degree v - 3) :=
      deco_edge_shared_twin_fires_hexc_step1 (n := n) (G := G) (hm) (h3) (u := u)
        (v := v) (t₀) (Ku := Ku) (Kv := Kv) (huv') (hn8) (hFsubErase)
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos, hS2card]; omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS2def, Finset.mem_compl] at ha2
    exact ha2 (Finset.mem_union_left F ha1)
  have hnc :=
      deco_edge_shared_twin_fires_hnc_step1 (n := n) (G := G) (u := u) (v := v) (Ku := Ku) (Kv
        := Kv) (F := F) (hFdef) (hS2def)
  have hFeq :=
      deco_edge_shared_twin_fires_hFeq_step1 (n := n) (G := G) (u := u) (v := v) (Ku := Ku)
        (Kv := Kv) (S₂ := S₂) (hS2def) (hdisjS1F)
  have he2 :=
      deco_edge_shared_twin_fires_he2 (n := n) (G := G) (h3) (u := u) (v := v) (t₀) (Ku := Ku) (Kv
        := Kv) (hKucard) (hKvcard) (hfire) (hdeg3u) (hdeg3v) (huv') (hKupos) (hKvpos) (hn8) (F :=
        F) (hFdef) (hS2def) (hS1card) (hS2card)
        (hcnt) (htrans) (hsumbound) (hFcard) (hexc)
  refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
  rw [hFeq]
  have hbound1 := Nat.mul_le_mul he1 (le_refl (S₂.card ^ 2))
  have hbound2 := Nat.mul_le_mul he2 (le_refl (S₁.card ^ 2))
  refine le_trans (add_le_add hbound1 hbound2) (le_of_eq ?_)
  ring

open Classical in
/-- **The `(5,5)` saturated-pair independence.**  In a never-firing starved census
(`m = 2(n−2)`, `δ ≥ 3`) at `n ≥ 48`, two saturated degree-`5` hubs `s₁, s₂` — each owning exactly
`2` `M`-isolated twins — are non-adjacent.  If they were adjacent: disjoint twin sets fire the
disjoint decorated edge (`deco_edge_moat_fires`, `90 ≤ n + 42`); one shared twin fires the
shared-twin decorated edge (`deco_edge_shared_twin_fires`, `90 ≤ n + 56`); two shared twins form a
`(5,3,5,3)` `4`-cycle `s₁, t₁, s₂, t₂` firing `master_cycle_fires` (`Σdeg = 16 = 4·4`,
`3·12 = 36 ≤ n + 8`) — either way contradicting `¬ algConn G ≤ 2`. -/
theorem sat_sat_independence {n : ℕ} [Nonempty (Fin n)] (hn : 48 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (s₁ s₂ : Fin n) (hd1 : G.degree s₁ = 5) (hd2 : G.degree s₂ = 5)
    (hc1 : (G.neighborFinset s₁ ∩ isoTwins G).card = 2)
    (hc2 : (G.neighborFinset s₂ ∩ isoTwins G).card = 2) (hne : s₁ ≠ s₂) :
    ¬ G.Adj s₁ s₂ := by
  classical
  intro hadj
  apply hnf
  set K1 := G.neighborFinset s₁ ∩ isoTwins G with hK1def
  set K2 := G.neighborFinset s₂ ∩ isoTwins G with hK2def
  have hK1sub : K1 ⊆ G.neighborFinset s₁ := by rw [hK1def]; exact Finset.inter_subset_left
  have hK2sub : K2 ⊆ G.neighborFinset s₂ := by rw [hK2def]; exact Finset.inter_subset_left
  have hK1deg : ∀ t ∈ K1, G.degree t = 3 := by
    intro t ht; rw [hK1def, Finset.mem_inter] at ht; exact (mem_isoTwins.mp ht.2).1
  have hK2deg : ∀ t ∈ K2, G.degree t = 3 := by
    intro t ht; rw [hK2def, Finset.mem_inter] at ht; exact (mem_isoTwins.mp ht.2).1
  have hs1notK2 : s₁ ∉ K2 := by
    rw [hK2def, Finset.mem_inter]; rintro ⟨_, hiso⟩
    have := (mem_isoTwins.mp hiso).1; omega
  have hs2notK1 : s₂ ∉ K1 := by
    rw [hK1def, Finset.mem_inter]; rintro ⟨_, hiso⟩
    have := (mem_isoTwins.mp hiso).1; omega
  have hInterLe : (K1 ∩ K2).card ≤ 2 := by
    calc (K1 ∩ K2).card ≤ K1.card := Finset.card_le_card Finset.inter_subset_left
      _ = 2 := hc1
  have hcases : (K1 ∩ K2).card = 0 ∨ (K1 ∩ K2).card = 1 ∨ (K1 ∩ K2).card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hdisj : Disjoint K1 K2 :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0)
    exact deco_edge_moat_fires G hm h3 s₁ s₂ K1 K2 hadj hK1sub hK1deg
      (by rw [hc1, hd1]) hK2sub hK2deg (by rw [hc2, hd2]) hs1notK2 hs2notK1 hdisj
      (by rw [hd1, hd2]; omega)
  · obtain ⟨t₀, ht0⟩ := Finset.card_eq_one.mp h1
    exact deco_edge_shared_twin_fires G hm h3 s₁ s₂ t₀ K1 K2 hadj hK1sub hK1deg
      (by rw [hc1, hd1]) hK2sub hK2deg (by rw [hc2, hd2]) hs1notK2 hs2notK1 ht0
      (by rw [hd1, hd2]; omega)
  · obtain ⟨t₁, t₂, ht12ne, hK1eq⟩ := Finset.card_eq_two.mp hc1
    have ht1K1 : t₁ ∈ K1 := by rw [hK1eq]; exact Finset.mem_insert_self t₁ _
    have ht2K1 : t₂ ∈ K1 := by
      rw [hK1eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self t₂)
    have hInterEq : K1 ∩ K2 = K1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have ht1K2 : t₁ ∈ K2 := by
      have hmem : t₁ ∈ K1 ∩ K2 := by rw [hInterEq]; exact ht1K1
      exact (Finset.mem_inter.mp hmem).2
    have ht2K2 : t₂ ∈ K2 := by
      have hmem : t₂ ∈ K1 ∩ K2 := by rw [hInterEq]; exact ht2K1
      exact (Finset.mem_inter.mp hmem).2
    have hdt1 : G.degree t₁ = 3 := hK1deg t₁ ht1K1
    have hdt2 : G.degree t₂ = 3 := hK1deg t₂ ht2K1
    have has1t1 : G.Adj s₁ t₁ := (G.mem_neighborFinset s₁ t₁).mp (hK1sub ht1K1)
    have has1t2 : G.Adj s₁ t₂ := (G.mem_neighborFinset s₁ t₂).mp (hK1sub ht2K1)
    have has2t1 : G.Adj s₂ t₁ := (G.mem_neighborFinset s₂ t₁).mp (hK2sub ht1K2)
    have has2t2 : G.Adj s₂ t₂ := (G.mem_neighborFinset s₂ t₂).mp (hK2sub ht2K2)
    have hs1t1 : s₁ ≠ t₁ := by intro h; rw [h, hdt1] at hd1; omega
    have hs1t2 : s₁ ≠ t₂ := by intro h; rw [h, hdt2] at hd1; omega
    have hs2t1 : s₂ ≠ t₁ := by intro h; rw [h, hdt1] at hd2; omega
    have hs2t2 : s₂ ≠ t₂ := by intro h; rw [h, hdt2] at hd2; omega
    have e0 : (![s₁, t₁, s₂, t₂] : Fin 4 → Fin n) 0 = s₁ := rfl
    have e1 : (![s₁, t₁, s₂, t₂] : Fin 4 → Fin n) 1 = t₁ := rfl
    have e2 : (![s₁, t₁, s₂, t₂] : Fin 4 → Fin n) 2 = s₂ := rfl
    have e3 : (![s₁, t₁, s₂, t₂] : Fin 4 → Fin n) 3 = t₂ := rfl
    refine master_cycle_fires (k := 4) (by norm_num) G hm h3 ![s₁, t₁, s₂, t₂] ?_ ?_ ?_ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> rfl
    · intro i
      fin_cases i
      · change G.Adj s₁ t₁; exact has1t1
      · change G.Adj t₁ s₂; exact has2t1.symm
      · change G.Adj s₂ t₂; exact has2t2
      · change G.Adj t₂ s₁; exact has1t2.symm
    · have hsplit : (∑ i : ZMod 4, G.degree (![s₁, t₁, s₂, t₂] i))
          = G.degree s₁ + G.degree t₁ + G.degree s₂ + G.degree t₂ := by
        have h := Fin.sum_univ_four (fun i : Fin 4 => G.degree (![s₁, t₁, s₂, t₂] i))
        rw [e0, e1, e2, e3] at h
        exact h
      rw [hsplit, hd1, hdt1, hd2, hdt2]
    · have hsplit : (∑ i : ZMod 4, (G.degree (![s₁, t₁, s₂, t₂] i) - 1))
          = (G.degree s₁ - 1) + (G.degree t₁ - 1) + (G.degree s₂ - 1)
            + (G.degree t₂ - 1) := by
        have h := Fin.sum_univ_four (fun i : Fin 4 => G.degree (![s₁, t₁, s₂, t₂] i) - 1)
        rw [e0, e1, e2, e3] at h
        exact h
      rw [hsplit, hd1, hdt1, hd2, hdt2]; omega

open Classical in
/-- **The fully census-only per-`p` owner-choke row.**  A never-firing starved census
(`m = 2(n−2)`, `δ ≥ 3`, `hs0`) on `n ≥ 48` satisfies the sharpened choke
`7·t₄ + 8·p + 3·X + 32 ≤ 4n`, with the `(5,5)` saturated-pair independence discharged internally
by `sat_sat_independence` (no moat-provenance hypothesis remains). -/
theorem p_choke_row_unconditional {n : ℕ} [Nonempty (Fin n)] (hn : 48 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (hnf : ¬ algConn G ≤ 2) :
    7 * (∑ h ∈ (hubSet G).filter (fun h => G.degree h = 4),
            (G.neighborFinset h ∩ isoTwins G).card)
        + 8 * ((hubSet G).filter (fun h => G.degree h = 5 ∧
            (G.neighborFinset h ∩ isoTwins G).card = 2)).card
        + 3 * excessX n G + 32 ≤ 4 * n := by
  refine p_choke_row hn G hm h3 hs0 hnf ?_
  intro s₁ s₂ hd1 hc1 hd2 hc2 hne
  exact sat_sat_independence hn G hm h3 hnf s₁ s₂ hd1 hd2 hc1 hc2 hne

end ACMax
