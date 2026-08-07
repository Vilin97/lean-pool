/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CechCount.Mul
import LeanPool.JacobianDiffgeo.CechCount.Surjective
import LeanPool.JacobianDiffgeo.CechCount.Count
import LeanPool.JacobianDiffgeo.CechCount.Final

/-!
# cechcount: the final gate — `dim H¹(𝒪_X) ≤ genus X` (namespace `RS` / `RS.Cech`)

The unit that closes the Buzzard Jacobian challenge. Forster §17.8-17.9's dimension count,
executed directly on the project's Čech colimit `RS.Cech.H1` (Hodge-free, duality-free):

* **`Mul.lean`**: multiplication by a global meromorphic function on Čech `H¹` —
  `RS.Cech.MulBound f D E` (pointwise order bound, `0`-friendly), the level tower
  `mulOn`/`mulC0`/`mulC1`/`mulZ1`/`mulH1Cover`, and **`RS.Cech.mulH1 f hf : H1 D →ₗ[ℂ] H1 E`**
  (`Module.DirectLimit.map`, mirroring `H1Incl`) with the algebra laws `mulH1_add`/`mulH1_smul`/
  `mulH1_mulH1`/`mulH1_one` (= `H1Incl`)/`mulH1_H1Incl`/`mulH1_congr`.
* **`Surjective.lean`**: **`RS.Cech.mulH1_surjective`** (Forster 17.8): multiplication by a
  nonzero function is onto, via the factorization through `E + divisor f` (`H1Incl_surjective`
  + the exact-bound multiplication with inverse `f⁻¹`).
* **`Count.lean`**: the χ-ledger constancy `h¹(nP) = h¹(0) - g` for `n > 2g-2` (Riemann–Roch +
  `linSys_eq_bot_of_degree_neg'` + `chi_eq_chi_zero_add_degree`) and the growth contradiction
  (Forster 17.9): a nonzero `ξ ∈ H¹(n₀P)` would be killed by some nonzero `f ∈ L(mP)` for
  dimension reasons, contradicting `mulH1_surjective` between equal finite dimensions. Yields
  **`RS.cechCount : Module.finrank ℂ (RS.Cech.H1 0) ≤ genus X`** (= `finrank_H1_zero_le_genus`).
* **`Final.lean`**: the ungated exports — `RS.tailToH1_zero_surjective`,
  `RS.finrank_H1_zero_eq_genus` (`dim H¹(X,𝒪_X) = genus X`),
  `RS.Abel.weakSolutionUpgrade_final`/`weakSolutionUpgradeFinset_final`,
  `RS.discretenessHyp_final : RS.DiscretenessHyp X`, the global instances
  `DiscreteTopology (RS.periodSubgroup X)`,
  `DiscreteTopology (RS.periodSubgroup X).topologicalClosure`,
  `IsZLattice ℝ (RS.periodSubgroup X).topologicalClosure.toIntSubmodule`,
  `RS.finrank_int_periodSubgroup_final` (`ℤ`-rank `2g`), and
  **`Jacobian.ofCurve_inj`** (the challenge's `ofCurve_inj`, hypothesis-free).
-/
