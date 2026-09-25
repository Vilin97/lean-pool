/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Duality
import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RRGHelpers

/-!
# Unwinnability at degree `g - 1` and acyclic orientations

For a connected graph `G` and a divisor `D` of degree `genus G - 1`, the main
result `unwinnable_iff_exists_acyclic_ordiv` identifies unwinnability with
linear equivalence to `ordiv G O` for an acyclic orientation `O`.

The proof assembles the following results from `chip-firing-with-lean`:

* `ordiv`, `isAcyclic`, `acyclicWithUniqueSource`, `orientationToConfig`
  (`Orientation.lean:402,221,357,431`) — the definitions.
* `ordiv_unwinnable` (`Orientation.lean:666`) — acyclic ⟹ `ordiv` unwinnable. This alone is
  the `⟸` direction, after transporting along `linearEquiv` with `winnable_equiv_winnable`
  (`Rank.lean:32`).
* `config_and_divisor_from_O` (`Orientation.lean:449`) and `div_of_config_of_div`
  (`Config.lean:161`) — together they give, for any acyclic `O` with unique source `q`,
  `(orientationToConfig G O q hO).chips - oneChip q = ordiv G O`
  (`orientation_config_sub_one_chip_eq_ordiv` below). This is the bridge from the
  configuration side back to the orientation divisor.
* `maximal_superstable_orientation` (`Orientation.lean:1186`) — every maximal superstable
  configuration comes from an acyclic orientation with unique source `q` (Dhar's algorithm,
  via `superstable_dhar` at `Orientation.lean:1118`).
* `maximal_unwinnable_char` (`RRGHelpers.lean:329`) — a divisor is maximal unwinnable iff its
  `q`-reduced representative has the shape `c - q` for `c` the (maximal superstable)
  `q`-reduced configuration.
* `winnable_of_deg_ge_genus` (`RRGHelpers.lean:223`) — an unwinnable divisor
  of degree `g - 1` is maximal unwinnable, since adding one chip gives degree
  `g` and therefore a winnable divisor.
* `unique_q_reduced` (`Basic.lean:1497`) — existence and uniqueness of the `q`-reduced
  representative, used to recover `linearEquiv G D (qReducedRep h_conn q D)` (the spec
  lemma for `qReducedRep` is `private` to `RRGHelpers.lean`, so it is re-derived here in one
  line from the public `unique_q_reduced`).

-/

namespace Utilities

/-- The canonical `q`-reduced representative of `D` is linearly equivalent to `D`.

This is the `private`-to-`RRGHelpers.lean` fact `qReducedRep_spec`'s first component,
re-derived here from the public `unique_q_reduced` since the original is not exported. -/
private lemma qReducedRep_linear_equiv {G : CFGraph} (h_conn : graphConnected G) (q : G.V)
    (D : CFDiv G) : linearEquiv G D (qReducedRep h_conn q D) :=
  (Classical.choose_spec (unique_q_reduced h_conn q D)).1.1

/-- For an acyclic orientation `O` with unique source `q`, the associated configuration minus
one chip at `q` recovers the orientation divisor `ordiv G O`.

This is the identity underlying `q_reduced_eq_chips_sub_one_chip` specialized to the
orientation-divisor case, proved the same way `moderator_of_unwinnable`
(`RRGHelpers.lean:443`) proves its `h_M_O` step: convert `orientationToConfig` to
`toConfig (orqed O hO)` via `config_and_divisor_from_O`, then use that `toDiv` at degree
`genus G - 1` of a configuration of degree `genus G` (`config_degree_from_O`) is exactly
`chips - oneChip q`. -/
private lemma orientation_config_sub_one_chip_eq_ordiv {G : CFGraph} (O : CFOrientation G)
    {q : G.V} (hO : acyclicWithUniqueSource G O q) :
    (orientationToConfig G O q hO).chips - oneChip q = ordiv G O := by
  have hDegOrqed : deg (orqed O hO).D = genus G - 1 := by
    simpa [orqed] using degree_ordiv O
  have hToDiv : toDiv (genus G - 1) (toConfig (orqed O hO)) = ordiv G O := by
    calc
      toDiv (genus G - 1) (toConfig (orqed O hO))
          = toDiv (deg (orqed O hO).D) (toConfig (orqed O hO)) := by rw [hDegOrqed]
      _ = (orqed O hO).D := div_of_config_of_div (orqed O hO)
      _ = ordiv G O := rfl
  have hCfgDeg : configDegree (toConfig (orqed O hO)) = genus G := by
    rw [← config_and_divisor_from_O O hO]
    exact config_degree_from_O O hO
  rw [← hToDiv, config_and_divisor_from_O O hO]
  dsimp only [toDiv]
  rw [show genus G - 1 - configDegree (toConfig (orqed O hO)) = -1 by rw [hCfgDeg]; ring]
  simp [sub_eq_add_neg]

/-- **The hard direction, assembled.** An unwinnable divisor of degree `genus G - 1` is
linearly equivalent to the orientation divisor of some acyclic orientation.

Chain: unwinnable of degree `g-1` is maximal unwinnable (`winnable_of_deg_ge_genus`, the one
new step); `maximal_unwinnable_char` reads off that the `q`-reduced representative is
`c - q` for `c` the maximal superstable `q`-reduced configuration;
`maximal_superstable_orientation` produces an acyclic `O` with unique source `q` realizing
`c`; `orientation_config_sub_one_chip_eq_ordiv` identifies `c - q` with `ordiv G O`. -/
theorem exists_acyclic_ordiv_of_unwinnable {G : CFGraph} (h_conn : graphConnected G)
    (D : CFDiv G) (hUnwin : ¬ winnable G D) (hDeg : deg D = genus G - 1) :
    ∃ O : CFOrientation G, isAcyclic G O ∧ linearEquiv G D (ordiv G O) := by
  set q : G.V := Classical.arbitrary G.V with hq
  -- Step 1: unwinnable of degree `g - 1` is maximal unwinnable.
  have hMax : maximalUnwinnable G D := by
    refine ⟨hUnwin, fun v => ?_⟩
    apply winnable_of_deg_ge_genus h_conn
    rw [deg.map_add, deg_one_chip, hDeg]
    linarith
  -- Step 2: the `q`-reduced configuration is maximal superstable, and `D`'s `q`-reduced
  -- representative has the canonical `c - q` shape.
  have hChar := (maximal_unwinnable_char h_conn q D).mp hMax
  -- Step 3: that maximal superstable configuration comes from an acyclic orientation.
  obtain ⟨O, hO, hOeq⟩ :=
    maximal_superstable_orientation G q (qReducedConfig h_conn q D) hChar.1
  -- Step 4: identify the `c - q` shape with `ordiv G O`.
  have hRep : qReducedRep h_conn q D = (orientationToConfig G O q hO).chips - oneChip q := by
    rw [hOeq]; exact hChar.2
  have hOrdivEq := orientation_config_sub_one_chip_eq_ordiv O hO
  refine ⟨O, hO.1, ?_⟩
  have hEquivRep := qReducedRep_linear_equiv h_conn q D
  rw [hRep, hOrdivEq] at hEquivRep
  exact hEquivRep

/-- **The easy direction.** If `D` is linearly equivalent to the orientation divisor of an
acyclic orientation, `D` is unwinnable. This is `ordiv_unwinnable`
(`Orientation.lean:666`) transported along `linearEquiv` by `winnable_equiv_winnable`
(`Rank.lean:32`). -/
theorem unwinnable_of_exists_acyclic_ordiv {G : CFGraph} (D : CFDiv G) (O : CFOrientation G)
    (hAcyc : isAcyclic G O) (hEquiv : linearEquiv G D (ordiv G O)) :
    ¬ winnable G D := by
  intro hWin
  exact ordiv_unwinnable G O hAcyc (winnable_equiv_winnable G D (ordiv G O) hWin hEquiv)

/-- **T3, combinatorial half.** For a connected graph `G` and a divisor `D` of degree
`genus G - 1`, `D` is unwinnable if and only if `D` is linearly equivalent to `ordiv G O`
for some acyclic orientation `O`.

Pairs with `Utilities.Certificate.ExplicitPotential.onFacet_flipPoint_iff_runsAgainst`
in `OrientationPoint.lean`, which reads the same equivalence off the geometric side: a
circuit is tight at the orientation's theta witness exactly when the orientation has a
directed cycle, i.e. is not acyclic. -/
theorem unwinnable_iff_exists_acyclic_ordiv {G : CFGraph} (h_conn : graphConnected G)
    (D : CFDiv G) (hDeg : deg D = genus G - 1) :
    ¬ winnable G D ↔ ∃ O : CFOrientation G, isAcyclic G O ∧ linearEquiv G D (ordiv G O) :=
  ⟨fun hUnwin => exists_acyclic_ordiv_of_unwinnable h_conn D hUnwin hDeg,
   fun ⟨O, hAcyc, hEquiv⟩ => unwinnable_of_exists_acyclic_ordiv D O hAcyc hEquiv⟩

end Utilities
