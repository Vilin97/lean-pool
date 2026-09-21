/-
Copyright (c) 2026 Dhyey Dharmendrakumar Mavani, Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyey Dharmendrakumar Mavani, Nathan Pflueger
-/
import LeanPool.ChipFiring.ChipFiringWithLean.RiemannRoch

namespace Propositions

private lemma rank_eq_rank (G : CFGraph) (D : CFDiv G) (r : ℤ)
    (h : rank_eq G D r) : rank G D = r := by
  change rank_geq G D r ∧ ¬rank_geq G D (r + 1) at h
  rw [rank_geq_iff, rank_geq_iff] at h
  omega

theorem riemann_roch {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
    ∀ r rdual : ℤ, rank_eq G D r → rank_eq G (canonical_divisor G - D) rdual →
      r - rdual = deg D + 1 - genus G := by
  intro r rdual h_rank h_rankdual
  have hr : rank G D = r := rank_eq_rank G D r h_rank
  have hrdual : rank G (canonical_divisor G - D) = rdual :=
    rank_eq_rank G (canonical_divisor G - D) rdual h_rankdual
  have h_rr := riemann_roch_for_graphs h_conn D
  rw [hr, hrdual] at h_rr
  linarith

theorem clifford {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
    ∀ r rdual : ℤ, rank_eq G D r → rank_eq G (canonical_divisor G - D) rdual →
      0 ≤ r → 0 ≤ rdual → (r : ℚ) ≤ (deg D : ℚ) / 2 := by
  intro r rdual h_rank h_rankdual hr_nonneg hrdual_nonneg
  have hr : rank G D = r := rank_eq_rank G D r h_rank
  have hrdual : rank G (canonical_divisor G - D) = rdual :=
    rank_eq_rank G (canonical_divisor G - D) rdual h_rankdual
  have h_clifford := clifford_theorem h_conn D (by simpa [hr] using hr_nonneg)
    (by simpa [hrdual] using hrdual_nonneg)
  rw [hr] at h_clifford
  exact h_clifford

end Propositions
