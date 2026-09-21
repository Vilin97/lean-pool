/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Duality

/-!
# Elementary Brill--Noether existence

The predicate `BNExists` is immediate in three parameter ranges: rank zero,
nonpositive rectangle width, and rectangle width one.  These arguments use
only effective divisors, the degree bound for winnability, and graph
Riemann--Roch.
-/

namespace Utilities

/-- The Brill--Noether inequality at rank zero just says that `d` is
nonnegative, so an effective divisor of degree `d` is a witness. -/
theorem BNExists_rank_zero
    {G : CFGraph} {d : ℤ} (hRho : 0 ≤ bnNumber G 0 d) :
    BNExists G 0 d := by
  have hd : 0 ≤ d := by
    unfold bnNumber rectangleWidth at hRho
    linarith
  let v : G.V := Classical.arbitrary G.V
  let D : CFDiv G := d.toNat • one_chip v
  have hEffective : effective D := by
    exact (Eff G).nsmul_mem (eff_one_chip v) d.toNat
  refine ⟨D, ?_, ?_⟩
  · dsimp [D]
    simpa [Int.toNat_of_nonneg hd] using
      (AddMonoidHom.map_nsmul deg d.toNat (one_chip v))
  · rw [← rank_geq_iff G D 0, rank_nonneg_iff_winnable]
    exact winnable_of_effective G D hEffective

/-- If the rectangle width is nonpositive, every rank test leaves degree at
least the genus and is therefore winnable. -/
theorem BNExists_of_width_nonpos
    {G : CFGraph} (hG : graph_connected G) {r d : ℤ}
    (hWidth : rectangleWidth G r d ≤ 0) :
    BNExists G r d := by
  let v : G.V := Classical.arbitrary G.V
  let D : CFDiv G := d • one_chip v
  have hDegree : deg D = d := by
    dsimp [D]
    rw [map_zsmul, deg_one_chip, zsmul_one]
    simp
  refine ⟨D, hDegree, ?_⟩
  rw [← rank_geq_iff G D r]
  intro E hE
  apply winnable_of_deg_ge_genus hG (D - E)
  rcases hE with ⟨_, hEDegree⟩
  rw [deg.map_sub, hDegree, hEDegree]
  unfold rectangleWidth at hWidth
  linarith

/-- At rectangle width one, subtract an effective divisor of degree `rho`
from the canonical divisor and apply Riemann--Roch. -/
theorem BNExists_of_width_one
    {G : CFGraph} (hG : graph_connected G) {r d : ℤ}
    (_hR : 0 ≤ r) (hWidth : rectangleWidth G r d = 1)
    (hRho : 0 ≤ bnNumber G r d) :
    BNExists G r d := by
  let v : G.V := Classical.arbitrary G.V
  let E : CFDiv G := (bnNumber G r d).toNat • one_chip v
  have hEffective : effective E := by
    exact (Eff G).nsmul_mem (eff_one_chip v) (bnNumber G r d).toNat
  have hEDegree : deg E = bnNumber G r d := by
    dsimp [E]
    simpa [Int.toNat_of_nonneg hRho] using
      (AddMonoidHom.map_nsmul deg (bnNumber G r d).toNat (one_chip v))
  let D : CFDiv G := canonical_divisor G - E
  have hDegree : deg D = d := by
    dsimp [D]
    rw [deg.map_sub, degree_of_canonical_divisor, hEDegree]
    unfold bnNumber
    rw [hWidth]
    unfold rectangleWidth at hWidth
    linarith
  have hERank : rank G E ≥ 0 := by
    rw [← rank_geq_iff G E 0, rank_nonneg_iff_winnable]
    exact winnable_of_effective G E hEffective
  refine ⟨D, hDegree, ?_⟩
  have hRR := riemann_roch_for_graphs hG D
  have hComplement : canonical_divisor G - D = E := by
    dsimp [D]
    abel
  rw [hComplement, hDegree] at hRR
  unfold rectangleWidth at hWidth
  linarith

/-- The complete elementary range: rank zero or rectangle width at most one. -/
theorem BNExists_elementary
    {G : CFGraph} (hG : graph_connected G) {r d : ℤ}
    (hR : 0 ≤ r) (hRho : 0 ≤ bnNumber G r d)
    (hEasy : r = 0 ∨ rectangleWidth G r d ≤ 1) :
    BNExists G r d := by
  rcases hEasy with hRankZero | hWidth
  · subst r
    exact BNExists_rank_zero hRho
  · by_cases hNonpos : rectangleWidth G r d ≤ 0
    · exact BNExists_of_width_nonpos hG hNonpos
    · have hOne : rectangleWidth G r d = 1 := by omega
      exact BNExists_of_width_one hG hR hOne hRho

end Utilities
