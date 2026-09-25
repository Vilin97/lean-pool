/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Grassmannian.OnceMarked
import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphContractionFibreTree
import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RiemannRoch

/-!
# From once-marked Brill--Noether existence to the gonality and Brill--Noether conjectures

`OnceMarkedBNExistence G u` (`Utilities/Grassmannian/OnceMarked.lean`) describes
the Young-diagram divisor census of a once-marked graph `(G, u)`.  This file relates it to
two standard statements, both
from the dependency `ChipFiringWithLean.RiemannRoch`:

* `gonalityConjecture h_conn : gonality h_conn ≤ (genus G + 3) / 2`
* `brillNoetherConjecture h_conn r d : 0 ≤ ρ → ∃ D, rank G D ≥ r ∧ deg D = d`

## The rectangular Young diagram

The row form `onceMarkedBNExists_iff_rank_rows` gives, for a normalized `D` (`deg D = g`)
and `i < lambda.rowLens.length`,

`rank G (D + (i - lambda.rowLens[i]) • oneChip u) ≥ i`.

The index `i` here is the *target rank*, not merely a label: to extract a rank-`≥ r`
conclusion one must plug in `i = r`, and `lambda.rowLens` is `0`-indexed with only
*positive* entries (Mathlib's `YoungDiagram.rowLens` never stores a zero row). A
single-row diagram therefore only ever supplies the row-`0` condition (`rank ≥ 0`,
trivial) — it cannot produce `rank ≥ 1`. To reach row index `r` at all, `lambda` needs
at least `r + 1` (positive-length) rows.

The right shape is the standard Brill--Noether rectangle: `r + 1` rows, each of length
`n := rectangleWidth G r d = genus G - d + r` (`Utilities/Foundations/
Parameters.lean`). Its row `r` is exactly the `n`-length row (`rowLens[r] = n`, since all
`r + 1` rows are equal), so the row-form condition at `i = r` reads

`rank G (D + (r - n) • oneChip u) ≥ r`,  of degree `g + r - n = d`.

The diagram's cardinality is `(r + 1) * n`, so `OnceMarkedBNExistence` supplies this
witness exactly when `(r + 1) * n ≤ g`, i.e. `bnNumber G r d ≥ 0` — the Brill--Noether
number `ρ`. This is *not* the `1 ≤ d` bound from the single-row guess; it is the sharp
`ρ ≥ 0` condition, and for `r = 1` its smallest solution in `d` is exactly
`(genus G + 3) / 2`, which is what makes `gonalityConjecture_of_onceMarkedBNExistence`
below go through with no slack.

When `n ≤ 0` (`d ≥ genus G + r`) the rectangle degenerates and no census input is needed
at all: `deg (d • oneChip u) = d ≥ genus G + r` makes Riemann's inequality
(`rank_ge_deg_sub_genus`) alone give `rank ≥ r`. `bnExists_of_onceMarkedBNExistence`
below case-splits exactly on this sign.
-/

namespace Utilities

section Rectangle

/-- The `(r + 1) x n` Brill--Noether rectangle: `r + 1` equal rows of length `n`. Only
used with `n > 0`; the case `n ≤ 0` never needs a Young diagram at all (see the module
docstring), so this definition is never asked about `n = 0` downstream, but it is defined
totally (as `⊥`) for that input so the surrounding construction stays a plain function. -/
def bnRectangle (r n : ℕ) : YoungDiagram :=
  if n = 0 then ⊥
  else YoungDiagram.ofRowLens (List.replicate (r + 1) n)
    (List.Pairwise.sortedGE (List.pairwise_replicate.mpr (Or.inr le_rfl)))

theorem bnRectangle_card (r n : ℕ) : (bnRectangle r n).card = (r + 1) * n := by
  unfold bnRectangle
  split_ifs with hn
  · simp [hn]
  · have hpos : ∀ x ∈ List.replicate (r + 1) n, 0 < x := by
      intro x hx
      rw [List.eq_of_mem_replicate hx]
      omega
    rw [← youngDiagram_rowLens_sum_eq_card,
      YoungDiagram.rowLens_ofRowLens_eq_self hpos, List.sum_const_nat]

theorem bnRectangle_rowLens_length_of_pos {r n : ℕ} (hn : 0 < n) :
    (bnRectangle r n).rowLens.length = r + 1 := by
  unfold bnRectangle
  rw [if_neg (by omega)]
  have hpos : ∀ x ∈ List.replicate (r + 1) n, 0 < x := by
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    exact hn
  rw [YoungDiagram.rowLens_ofRowLens_eq_self hpos, List.length_replicate]

theorem bnRectangle_getD_of_pos {r n : ℕ} (hn : 0 < n) :
    (bnRectangle r n).rowLens.getD r 0 = n := by
  unfold bnRectangle
  rw [if_neg (by omega)]
  have hpos : ∀ x ∈ List.replicate (r + 1) n, 0 < x := by
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    exact hn
  rw [YoungDiagram.rowLens_ofRowLens_eq_self hpos]
  exact List.getD_replicate n (Nat.lt_succ_self r)

end Rectangle

/-- The general bridging lemma: `OnceMarkedBNExistence` supplies a rank-`≥ r` divisor of
every degree `d` with `ρ(r, d) ≥ 0`, matching `brillNoetherConjecture`'s hypothesis
exactly (via `bnNumber`). No hypothesis on the sign of `rectangleWidth G r d` is needed:
the proof case-splits on it internally (see the module docstring). -/
theorem bnExists_of_onceMarkedBNExistence
    {G : CFGraph} (hG : graphConnected G) (u : G.V)
    (hCensus : OnceMarkedBNExistence G u) (r : ℕ) (d : ℤ)
    (hBN : 0 ≤ bnNumber G (r : ℤ) d) :
    BNExists G (r : ℤ) d := by
  rcases le_or_gt (rectangleWidth G (r : ℤ) d) 0 with hnle | hnpos
  · -- `d ≥ genus G + r`: Riemann's inequality alone gives rank `≥ r`, no census needed.
    refine ⟨d • oneChip u, ?_, ?_⟩
    · have hDeg : deg (d • oneChip u) = d := by rw [map_zsmul, deg_one_chip]; ring
      exact hDeg
    · have hDeg : deg (d • oneChip u) = d := by rw [map_zsmul, deg_one_chip]; ring
      have hRR := rank_ge_deg_sub_genus hG (d • oneChip u)
      rw [hDeg] at hRR
      unfold rectangleWidth at hnle
      linarith
  · -- `n := rectangleWidth G r d > 0`: build the `(r+1) x n` rectangle.
    set n : ℕ := (rectangleWidth G (r : ℤ) d).toNat with hn_def
    have hn_cast : (n : ℤ) = rectangleWidth G (r : ℤ) d :=
      Int.toNat_of_nonneg hnpos.le
    have hnpos' : 0 < n := by
      have : (0 : ℤ) < (n : ℤ) := by rw [hn_cast]; exact hnpos
      exact_mod_cast this
    have hCardLe : ((bnRectangle r n).card : ℤ) ≤ genus G := by
      rw [bnRectangle_card]
      push_cast
      rw [hn_cast]
      unfold bnNumber at hBN
      linarith
    obtain ⟨D, hDegree, hRows⟩ :=
      (onceMarkedBNExists_iff_rank_rows G u (bnRectangle r n)).mp (hCensus _ hCardLe)
    have hLen : r < (bnRectangle r n).rowLens.length := by
      rw [bnRectangle_rowLens_length_of_pos hnpos']
      omega
    have hgetD : (bnRectangle r n).rowLens.getD r 0 = n := bnRectangle_getD_of_pos hnpos'
    have hval : (bnRectangle r n).rowLens[r] = n := by
      have hge := (List.getD_eq_getElem (l := (bnRectangle r n).rowLens) (d := 0) hLen).symm
      rw [hgetD] at hge
      exact hge
    have hrow := hRows r hLen
    rw [hval] at hrow
    refine ⟨D + ((r : ℤ) - (n : ℤ)) • oneChip u, ?_, hrow⟩
    rw [deg.map_add, map_zsmul, deg_one_chip, hDegree, hn_cast]
    unfold rectangleWidth
    ring

/-- The `r = 1` specialization, phrased exactly as the reader-recognisable
`BNExists G 1 d` (`Utilities/Foundations/Parameters.lean`). -/
theorem bnExists_one_of_onceMarkedBNExistence
    {G : CFGraph} (hG : graphConnected G) (u : G.V)
    (hCensus : OnceMarkedBNExistence G u) (d : ℤ)
    (hBN : 0 ≤ bnNumber G (1 : ℤ) d) :
    BNExists G 1 d := by
  have h := bnExists_of_onceMarkedBNExistence hG u hCensus 1 d (by simpa using hBN)
  simpa using h

/-- A public replacement for the dependency's `private lemma gonality_le_genus_add_one`'s
proof pattern: any witness of `gonalityLeq G k` bounds the noncomputable `gonality`
above by `k`. The dependency does not export a lemma of this shape (its own version is
`private`), so this re-derives the two ingredients (`BddBelow` and `csInf_le`) from the
public `rank_geq_iff` / `rank_le_degree`. -/
theorem gonality_le_of_gonality_leq {G : CFGraph} (h_conn : graphConnected G) {k : ℤ}
    (hk : gonalityLeq G k) : gonality h_conn ≤ k := by
  unfold gonality
  refine csInf_le ?_ hk
  refine ⟨1, ?_⟩
  rintro l ⟨D, hRank, hDeg⟩
  have hRankGeq : rankGeq G D 1 := (rank_geq_iff G D 1).mpr hRank
  have hDegLower : (1 : ℤ) ≤ deg D := rank_le_degree G D 1 (by norm_num) hRankGeq
  simpa [hDeg] using hDegLower

/-- The gonality conjecture in this genus follows from once-marked Brill--Noether
existence: the minimal degree `d = (genus G + 3) / 2` with `ρ(1, d) ≥ 0` is a rank-`≥ 1`
divisor degree by `bnExists_one_of_onceMarkedBNExistence`, and `gonality_le_of_
gonalityLeq` transports that into a bound on the dependency's noncomputable
`gonality`. -/
theorem gonalityConjecture_of_onceMarkedBNExistence
    {G : CFGraph} (hG : graphConnected G) (u : G.V)
    (hCensus : OnceMarkedBNExistence G u) :
    gonalityConjecture hG := by
  have hgnn := genus_nonneg_of_graph_connected G hG
  set d : ℤ := (genus G + 3) / 2 with hd_def
  have hBN : 0 ≤ bnNumber G (1 : ℤ) d := by
    unfold bnNumber rectangleWidth
    omega
  obtain ⟨D, hDeg, hRank⟩ := bnExists_one_of_onceMarkedBNExistence hG u hCensus d hBN
  have hgle : gonalityLeq G d := ⟨D, hRank, hDeg⟩
  have hle := gonality_le_of_gonality_leq hG hgle
  show gonality hG ≤ (genus G + 3) / 2
  omega

/-- The Brill--Noether conjecture in this genus follows from once-marked Brill--Noether
existence, for every `r d : ℤ`. The `r ≥ 0` case is `bnExists_of_onceMarkedBNExistence`
after `lift`ing `r` to `ℕ`; the `r < 0` case is trivial, since `rank G D ≥ -1` always
(`rank_geq_neg_one`) and `r ≤ -1`. -/
theorem brillNoetherConjecture_of_onceMarkedBNExistence
    {G : CFGraph} (hG : graphConnected G) (u : G.V)
    (hCensus : OnceMarkedBNExistence G u) (r d : ℤ) :
    brillNoetherConjecture hG r d := by
  show 0 ≤ genus G - (r + 1) * (genus G - d + r) → ∃ D : CFDiv G, rank G D ≥ r ∧ deg D = d
  intro hrho
  rcases le_or_gt 0 r with hr0 | hrneg
  · lift r to ℕ using hr0 with rNat
    have hBN : 0 ≤ bnNumber G (rNat : ℤ) d := by
      unfold bnNumber rectangleWidth
      exact hrho
    obtain ⟨D, hDeg, hRank⟩ := bnExists_of_onceMarkedBNExistence hG u hCensus rNat d hBN
    exact ⟨D, hRank, hDeg⟩
  · refine ⟨d • oneChip u, ?_, ?_⟩
    · have hge : rank G (d • oneChip u) ≥ -1 := rank_geq_neg_one G (d • oneChip u)
      omega
    · rw [map_zsmul, deg_one_chip]; ring

end Utilities
