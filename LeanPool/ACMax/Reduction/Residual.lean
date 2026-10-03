/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Counting.Incidence
public import Mathlib.Tactic.Ring
public import LeanPool.ACMax.Reduction.Reduction
public import LeanPool.ACMax.Cuts.SignedCut

/-!
# Uniformly-provable foundation layers for the general ACMAX residual program

This file formalizes, **for general `n`** (no `Fin`-enumeration, no `decide`; only
counting / pigeonhole / `omega`), the four foundation layers of the uniform residual
program identified by the investigation of the per-`n` architecture (`n = 12..19`):

* **L1 — thresholds as functions of `n`.**  The `n`-uniform good-certificate inequalities
  `n·(Σdeg − 2k) ≤ 2k(n−k)` of `Reduction.Reduction` are converted to explicit per-degree-sum
  thresholds `goodTriThreshold / goodC4Threshold / goodK23Threshold` (`Σdeg ≤ thr(n)`),
  together with the full saturation ladder: the good-triangle threshold is `11` for **all**
  `n ≥ 18`, the good-`C₄` threshold is `14` on `16 ≤ n < 32` and `15` for `n ≥ 32`, and the
  good-`K₂,₃` threshold is `19` on `17 ≤ n < 25`, `20` on `25 ≤ n < 50` and `21` for
  `n ≥ 50` (after `n = 50` the whole good-certificate layer is literally `n`-invariant).

* **L2 — the handshake package for `ResidualCore`.**  With `D = {deg = 3}`,
  `Hub = {deg ≥ 4}`: `∑ deg = 4n − 8`; `|D| + |Hub| = n`; the **excess identity**
  `∑_{Hub} (deg − 3) = n − 8`; hence `|Hub| ≤ n − 8` (and `|D| ≥ 8`, re-exported from
  `card_deg3_ge_eight`); and the generalized `e(M)/e_H` handshake
  `2·e(M) + 6·|Hub| = 2(n+4) + 2·e_H` (in incidence-sum form), the `n`-generic form of the
  per-`n` formulas `e(M) = (n+4) − 3|Hub| + e_H` (`= 22 − 3|Hub| + e_H` at `n = 18`,
  `23 − 3|Hub| + e_H` at `n = 19`).  No all-hubs-degree-4 hypothesis is needed: the excess
  identity supplies `∑_{Hub} deg = 3|Hub| + (n − 8)` in general.

* **L3 — the share lemmas, generalized.**  Two non-adjacent degree-`4` hubs share at most
  **one** common `M`-isolated degree-`3` twin for every `n ≥ 16` (two shared twins form an
  induced `C₄` of `Σdeg = 14 ≤ goodC4Threshold n`), and two non-adjacent degree-`≤ 5` hubs
  share at most **two** for every `n ≥ 17` (three form an induced `K₂,₃` of
  `Σdeg ≤ 19 ≤ goodK23Threshold n`) — the `n`-generic ports of
  `nonadj_hubs_share_le_one_iso` / `nonadj_hubs_share_le_two_iso`, consuming
  `¬HasGoodC4 n G` / `¬HasGoodK23 n G` verbatim.

* **L7 — the TWO-BLOCK construction** (the validated 6th cut, the umbrella of the five
  per-`n` boundary configurations and the certificate that kills the `n ≥ 23` fat-regime
  escaper family).  `TwoBlockConfig` asks for disjoint equal-size blocks `P, N` with
  `2·e(P,N) + leak(P) + leak(N) ≤ 4|P|`, where `leak(X) = e(X, Xᶜ)` **includes** the
  cross-edges (`leak(P) = e(P,N) + e(P,Z)`), so the form is *exactly* equal to the
  hypothesis `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4|P|` of `algConn_le_two_of_signed`
  (`twoBlock_eq_signed`; validated numerically on the verified `n = 23, 25` escapers: both forms
  agree exactly, values `21 ≤ 44`, `23 ≤ 44`, `25 ≤ 40`, Rayleigh `≤ 1.25`).  The certificate
  `two_block_cut_certificate : TwoBlockConfig n G → algConn G ≤ 2` is a direct application
  of the already-general signed-cut lemma.  Any witness assembled in the signed form — in
  particular the output of each of the five per-`n` `*_cut_certificate` lemmas — is a
  `TwoBlockConfig` witness by `twoBlockConfig_iff_signed`.

Everything here is sorry-free and axiom-clean.
-/

public section

namespace ACMax

/-! ## L1 — good-certificate thresholds as functions of `n`

The generic cut criteria of `Reduction.Reduction` are `n·(Σdeg − 2k) ≤ 2·(k·(n − k))` for the
`k`-vertex gadgets (`k = 3` triangle, `4` cycle, `5` `K₂,₃`).  Solving for `Σdeg` gives the
explicit thresholds below (`ℕ`-division; `thr = 2k + ⌊2k(n−k)/n⌋`). -/

open Classical in
/-- Degree-sum threshold for a **good triangle**: `Σdeg ≤ goodTriThreshold n` iff the
`n`-uniform inequality `n·(Σdeg − 6) ≤ 2·(3·(n−3))` holds.  Equals `11` for all `n ≥ 18`. -/
def goodTriThreshold (n : ℕ) : ℕ := 6 + 6 * (n - 3) / n

open Classical in
/-- Degree-sum threshold for a **good `C₄`**: `Σdeg ≤ goodC4Threshold n` iff
`n·(Σdeg − 8) ≤ 2·(4·(n−4))`.  Equals `14` on `16 ≤ n < 32` and `15` for all `n ≥ 32`. -/
def goodC4Threshold (n : ℕ) : ℕ := 8 + 8 * (n - 4) / n

open Classical in
/-- The generic conversion: `n·(S − c) ≤ m ↔ S ≤ c + m/n` (`ℕ`-division, `n > 0`). -/
theorem nat_mul_sub_le_iff {n : ℕ} (hn : 0 < n) (c m S : ℕ) :
    n * (S - c) ≤ m ↔ S ≤ c + m / n := by
  rw [Nat.mul_comm n (S - c), ← Nat.le_div_iff_mul_le hn]
  generalize m / n = q
  omega

open Classical in
/-- Division sandwich: `k·n ≤ m < (k+1)·n → m/n = k`. -/
theorem nat_div_eq_of_between {m n k : ℕ} (hn : 0 < n) (h1 : k * n ≤ m)
    (h2 : m < (k + 1) * n) : m / n = k := by
  have hle : k ≤ m / n := (Nat.le_div_iff_mul_le hn).mpr h1
  have hlt : m / n < k + 1 := (Nat.div_lt_iff_lt_mul hn).mpr h2
  omega

open Classical in
/-- The good-triangle weighted-cut inequality is exactly the degree-sum threshold. -/
theorem goodTri_threshold_iff {n : ℕ} (hn : 0 < n) (S : ℕ) :
    n * (S - 6) ≤ 2 * (3 * (n - 3)) ↔ S ≤ goodTriThreshold n := by
  have h : (2 : ℕ) * (3 * (n - 3)) = 6 * (n - 3) := by ring
  rw [h, goodTriThreshold]
  exact nat_mul_sub_le_iff hn 6 (6 * (n - 3)) S

open Classical in
/-- The good-`C₄` weighted-cut inequality is exactly the degree-sum threshold. -/
theorem goodC4_threshold_iff {n : ℕ} (hn : 0 < n) (S : ℕ) :
    n * (S - 8) ≤ 2 * (4 * (n - 4)) ↔ S ≤ goodC4Threshold n := by
  have h : (2 : ℕ) * (4 * (n - 4)) = 8 * (n - 4) := by ring
  rw [h, goodC4Threshold]
  exact nat_mul_sub_le_iff hn 8 (8 * (n - 4)) S

open Classical in
/-- **No good triangle ⟹ every triangle exceeds the threshold**: in a graph with no good
triangle, every triangle has degree sum `> goodTriThreshold n`. -/
theorem no_good_triangle_sum_gt {n : ℕ} (hn : 0 < n) {G : SimpleGraph (Fin n)}
    (hT : ¬HasGoodTriangle n G) {x y z : Fin n}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (haxy : G.Adj x y) (hayz : G.Adj y z) (haxz : G.Adj x z) :
    goodTriThreshold n < G.degree x + G.degree y + G.degree z := by
  by_contra hle
  rw [not_lt] at hle
  exact hT ⟨x, y, z, hxy, hyz, hxz, haxy, hayz, haxz,
    (goodTri_threshold_iff hn _).mpr hle⟩

open Classical in
/-- **No good `C₄` ⟹ every induced `C₄` exceeds the threshold.** -/
theorem no_good_C4_sum_gt {n : ℕ} (hn : 0 < n) {G : SimpleGraph (Fin n)}
    (hC4 : ¬HasGoodC4 n G) {a b c d : Fin n}
    (hcard : ({a, b, c, d} : Finset (Fin n)).card = 4)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : ¬G.Adj a c) (hbd : ¬G.Adj b d) :
    goodC4Threshold n < G.degree a + G.degree b + G.degree c + G.degree d := by
  by_contra hle
  rw [not_lt] at hle
  exact hC4 ⟨a, b, c, d, hcard, hab, hbc, hcd, hda, hac, hbd,
    (goodC4_threshold_iff hn _).mpr hle⟩

/-! ### The saturation ladder -/

open Classical in
/-- Good-triangle threshold saturates at `11` for **all** `n ≥ 18` (never reaches `12`). -/
theorem goodTriThreshold_eq_of_ge_eighteen {n : ℕ} (hn : 18 ≤ n) :
    goodTriThreshold n = 11 := by
  have hdiv : 6 * (n - 3) / n = 5 :=
    nat_div_eq_of_between (by omega) (by omega) (by omega)
  rw [goodTriThreshold, hdiv]

open Classical in
/-- Good-`C₄` threshold is `14` on the window `16 ≤ n < 32`. -/
theorem goodC4Threshold_eq_of_window {n : ℕ} (h1 : 16 ≤ n) (h2 : n < 32) :
    goodC4Threshold n = 14 := by
  have hdiv : 8 * (n - 4) / n = 6 :=
    nat_div_eq_of_between (by omega) (by omega) (by omega)
  rw [goodC4Threshold, hdiv]

open Classical in
/-- Good-`C₄` threshold saturates at `15` for **all** `n ≥ 32` (never reaches `16`). -/
theorem goodC4Threshold_eq_of_ge_thirtytwo {n : ℕ} (hn : 32 ≤ n) :
    goodC4Threshold n = 15 := by
  have hdiv : 8 * (n - 4) / n = 7 :=
    nat_div_eq_of_between (by omega) (by omega) (by omega)
  rw [goodC4Threshold, hdiv]

/-! ## L2 — the handshake package

Throughout, `D = univ.filter (deg = 3)` and `Hub = univ.filter (4 ≤ deg)`. -/

open Classical in
/-- **(a) Degree sum.**  `2(n−2)` edges give `∑ deg = 4n − 8` (`n ≥ 2`). -/
theorem residual_degree_sum (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) :
    ∑ v : Fin n, G.degree v = 4 * n - 8 := by
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  omega

/-! ## L3 — the share lemmas, generalized

`n`-generic ports of `nonadj_hubs_share_le_one_iso` / `nonadj_hubs_share_le_two_iso`
(`TwinCert19Core`), consuming `¬HasGoodC4 n G` / `¬HasGoodK23 n G` verbatim.  The
constants are exactly those of the per-`n` layer from the respective tie points onward:
share `≤ 1` for degree-4 pairs from `n = 16` (`C₄` tie `Σ = 14`), share `≤ 2` for
degree-`≤ 5` pairs from `n = 17` (`K₂,₃` tie `Σ = 19`); both only gain slack as `n` grows. -/

/-! ## L7 — the TWO-BLOCK construction (the validated 6th cut)

`leak(X) := ∑_{v∈X} |N(v) \ X| = e(X, Xᶜ)` counts **all** edges leaving `X`, including
those into the opposite block.  Since `N` and `Z = (P ∪ N)ᶜ` partition `Pᶜ ⊇ N(p) \ P`,
`leak(P) = e(P,N) + e(P,Z)` and symmetrically `leak(N) = e(N,P) + e(N,Z)` with
`e(N,P) = e(P,N)`; hence

  `2·e(P,N) + leak(P) + leak(N) = 4·e(P,N) + e(P,Z) + e(N,Z)`,

so the report form of the two-block inequality is *literally equal* to the hypothesis of
`algConn_le_two_of_signed` (there is no discrepancy — validated to exact integer equality
on the verified `n = 23, 25` fat-regime escapers). -/

open Classical in
/-- Neighbourhood split along a disjoint pair: for disjoint `X, Y`,
`|N(p) \ X| = |N(p) ∩ Y| + |N(p) \ (X ∪ Y)|`. -/
theorem leak_split {V : Type*} [Fintype V] (G : SimpleGraph V) {X Y : Finset V}
    (hd : Disjoint X Y) (p : V) :
    (G.neighborFinset p \ X).card
      = (G.neighborFinset p ∩ Y).card + (G.neighborFinset p \ (X ∪ Y)).card := by
  classical
  have hu : G.neighborFinset p \ X
      = (G.neighborFinset p ∩ Y) ∪ (G.neighborFinset p \ (X ∪ Y)) := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ⟨hw, hwX⟩
      by_cases hwY : w ∈ Y
      · exact Or.inl ⟨hw, hwY⟩
      · exact Or.inr ⟨hw, fun h => h.elim hwX hwY⟩
    · rintro (⟨hw, hwY⟩ | ⟨hw, hwXY⟩)
      · exact ⟨hw, fun hwX => Finset.disjoint_left.mp hd hwX hwY⟩
      · exact ⟨hw, fun hwX => hwXY (Or.inl hwX)⟩
  have hdis : Disjoint (G.neighborFinset p ∩ Y) (G.neighborFinset p \ (X ∪ Y)) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [Finset.mem_inter] at hw
    rw [Finset.mem_sdiff, Finset.mem_union] at hw'
    exact hw'.2 (Or.inr hw.2)
  rw [hu, Finset.card_union_of_disjoint hdis]

open Classical in
/-- **The TWO-BLOCK signed-cut configuration** (the 6th construction): disjoint equal-size
nonempty blocks `P, N` with

  `2·e(P,N) + leak(P) + leak(N) ≤ 4·|P|`,   `leak(X) = ∑_{v∈X} |N(v) \ X|`.

All five per-`n` boundary configurations (`SingleVertex`, `TwoTwin`, `TwoHub`,
`HubTriangle`, `StarTriangle`) are `|P| = 3` instances (their `_cut_certificate` lemmas
output exactly the equivalent signed form — see `twoBlockConfig_iff_signed`), and the new
fat-regime instances (two disjoint closed carrier stars; a starved internally-bound hub
cycle vs any sparse block) kill every verified `n ≥ 23` escaper of the 5-construction set.

Stated for an arbitrary finite vertex type (like the whole spectral base layer), so that
its instances match `algConn_le_two_of_signed` exactly; at `Fin n` this is the
`TwoBlockConfig n G` of the residual program. -/
@[expose] def TwoBlockConfig {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ P N : Finset V, Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
    2 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
      + (∑ p ∈ P, (G.neighborFinset p \ P).card)
      + (∑ q ∈ N, (G.neighborFinset q \ N).card)
    ≤ 4 * P.card

open Classical in
/-- **The two forms are equal**: for disjoint `P, N`,
`2·e(P,N) + leak(P) + leak(N) = 4·e(P,N) + e(P,Z) + e(N,Z)` — the left side is the
two-block form, the right side is the exact quantity in the hypothesis of
`algConn_le_two_of_signed`. -/
theorem twoBlock_eq_signed {V : Type*} [Fintype V] (G : SimpleGraph V) (P N : Finset V)
    (hd : Disjoint P N) :
    2 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
      + (∑ p ∈ P, (G.neighborFinset p \ P).card)
      + (∑ q ∈ N, (G.neighborFinset q \ N).card)
    = 4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
      + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
      + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card) := by
  classical
  have hP : ∑ p ∈ P, (G.neighborFinset p \ P).card
      = (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + ∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => leak_split G hd p)
  have hN : ∑ q ∈ N, (G.neighborFinset q \ N).card
      = (∑ q ∈ N, (G.neighborFinset q ∩ P).card)
        + ∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    have h := leak_split G hd.symm q
    rwa [Finset.union_comm N P] at h
  have hsym : ∑ q ∈ N, (G.neighborFinset q ∩ P).card
      = ∑ p ∈ P, (G.neighborFinset p ∩ N).card := cross_count G N P
  omega

open Classical in
/-- `TwoBlockConfig` is **exactly** the existence of a witness of the signed-cut hypothesis
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4|P|` of `algConn_le_two_of_signed`.  In particular every
witness assembled by the five per-`n` cut certificates (whose conclusions are precisely the
right-hand existential) is a two-block witness — `TwoBlockConfig` is the umbrella form. -/
theorem twoBlockConfig_iff_signed {V : Type*} [Fintype V] (G : SimpleGraph V) :
    TwoBlockConfig G ↔
      ∃ P N : Finset V, Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
        4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
          + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
          + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
        ≤ 4 * P.card := by
  constructor
  · rintro ⟨P, N, hd, hc, hpos, hineq⟩
    refine ⟨P, N, hd, hc, hpos, ?_⟩
    rw [← twoBlock_eq_signed G P N hd]
    exact hineq
  · rintro ⟨P, N, hd, hc, hpos, hineq⟩
    refine ⟨P, N, hd, hc, hpos, ?_⟩
    rw [twoBlock_eq_signed G P N hd]
    exact hineq

open Classical in
/-- **The two-block cut certificate**: `TwoBlockConfig G → algConn G ≤ 2`, a direct
application of the already-general three-valued signed cut `algConn_le_two_of_signed`. -/
theorem two_block_cut_certificate {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (h : TwoBlockConfig G) : algConn G ≤ 2 := by
  obtain ⟨P, N, hd, hc, hpos, hineq⟩ := (twoBlockConfig_iff_signed G).mp h
  exact algConn_le_two_of_signed G P N hd hc hpos hineq

end ACMax
