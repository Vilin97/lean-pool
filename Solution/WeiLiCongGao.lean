/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132WeiE2

/-!
# Solution: Six distances from the E2 diameter-heptagon pattern

Challenge: `diameter-heptagon-e2-six-distances` (`Challenge.WeiLiCongGao`)
Proves: `Challenge.WeiLiCongGao.e2_pattern_six_distances`
Solved by: Egor Lyfar
Pool project: `LeanPool.Erdos132WeiE2`

This module restates the challenge statement under its own name and proves it. It must not import
the challenge module: comparator exports both environments separately and checks that the statements
agree, which is what makes the verdict independent of the statement file.
-/

namespace Challenge.WeiLiCongGao

/-- The E2 diameter-heptagon pattern realizes at least six distinct pairwise distances. -/
theorem e2_pattern_six_distances
    (p : Fin 7 → EuclideanSpace ℝ (Fin 2))
    (hdiam : ∀ i : Fin 7, dist (p i) (p (i + 3)) = 1)
    (hshort : ∀ i j : Fin 7, i ≠ j → j ≠ i + 3 → i ≠ j + 3 → dist (p i) (p j) < 1)
    (hC : dist (p 0) (p 1) = dist (p 3) (p 4))
    (hB : dist (p 1) (p 2) = dist (p 2) (p 3))
    (hA₁ : dist (p 4) (p 5) = dist (p 5) (p 6))
    (hA₂ : dist (p 5) (p 6) = dist (p 6) (p 0))
    (hBA : dist (p 1) (p 2) < dist (p 4) (p 5))
    (hAC : dist (p 4) (p 5) < dist (p 0) (p 1)) :
    6 ≤ ((Finset.univ.filter fun q : Fin 7 × Fin 7 => q.1 ≠ q.2).image
      fun q => dist (p q.1) (p q.2)).card := by
  obtain ⟨A, B, C, hpar⟩ :=
    LeanPool.Erdos132WeiE2.Geometry.e2_angle_parametrization
      p hdiam hshort hC hB hA₁ hA₂ hBA hAC
  exact LeanPool.Erdos132WeiE2.Counting.six_distances_of_parametrization
    p (hdiam 0)
    (hshort 0 2 (by decide) (by decide) (by decide))
    (hshort 0 5 (by decide) (by decide) (by decide))
    (hshort 1 3 (by decide) (by decide) (by decide))
    hBA hAC A B C hpar.B_pos hpar.B_lt_A hpar.A_lt_C hpar.C_lt_pi_div_three
    hpar.angle_sum hpar.closure hpar.edgeC hpar.edgeB hpar.edgeA hpar.q_sq hpar.ra_sq hpar.rb_sq

end Challenge.WeiLiCongGao
