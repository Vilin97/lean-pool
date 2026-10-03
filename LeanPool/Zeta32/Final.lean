/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Assembly
public import LeanPool.Zeta32.LinearIndependence
public import LeanPool.Zeta32.Arith.Greedy
public import LeanPool.Zeta32.Arith.Node
public import LeanPool.Zeta32.Analytic.Heine
public import LeanPool.Zeta32.Analytic.Energy
public import LeanPool.Zeta32.Arith.Relaxed
public import LeanPool.Zeta32.Arith.SmallPrimes
public import LeanPool.Zeta32.Arith.Outer
public import LeanPool.Zeta32.Arith.LargePrimes
public import LeanPool.Zeta32.Fstar
public import LeanPool.Zeta32.FstarPointsW
public import LeanPool.Zeta32.FstarPointsRho

/-! Final assembly (§9 of the proof notes). The main theorem follows from three nodes:
the arithmetic bound on the primitive content (`arith_node`), the analytic bound on the Hankel
determinant
at `ζ(3) − r ζ(2)` (`analytic_node`), and the nonvanishing modulo primes (`prime_edge_node`); linear
independence then follows from the irrationality of `ζ(3) − r ζ(2)` for every rational `r` and
of `ζ(2)`. -/

public section

open Filter Polynomial

namespace Zeta32
/-- `FstarPoints`, from `Fstar.pointsW` and `Fstar.pointsRho`. -/
theorem fstarPoints : FstarPoints := by
  obtain ⟨hm1, hm2, hlog, hW⟩ := Fstar.pointsW
  obtain ⟨hell, hR⟩ := Fstar.pointsRho
  exact ⟨hm1, hm2, hell, hlog, fun k => ⟨hW k, hR k⟩⟩

theorem arith_node (r : ℚ) : ArithNode r :=
  Arith.arith_of_parts r (Arith.greedy_valuation_bound r) (Arith.Relaxed.relaxed_per_prime r)
    (Arith.outer_per_prime_bound r) (Arith.large_prime_integrality r)
      (Arith.small_prime_crude_bound r)

theorem analytic_node (r : ℚ) : AnalyticNode r :=
  Analytic.energy_bound_of_inputs r (Analytic.heine_bound r) (Fstar.fstarInput_of_points
    fstarPoints)

theorem prime_edge_node (r : ℚ) : PrimeEdgeNode r :=
  fun p _ hp hE hden => PrimeEdge.prime_edge r p hp hE hden

theorem zeta3_sub_rat_mul_zeta2_irrational (r : ℚ) :
    Irrational ((∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) - (r : ℝ) * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2) :=
  main_of_nodes r (arith_node r) (analytic_node r) (prime_edge_node r)

/-- The main theorem in its strong form. -/
theorem one_zeta_two_zeta_three_linearIndependent :
    LinearIndependent ℚ ![(1 : ℂ), riemannZeta 2, riemannZeta 3] :=
  LinearIndependence.linearIndependent_of_irrational zeta3_sub_rat_mul_zeta2_irrational

end Zeta32
end
