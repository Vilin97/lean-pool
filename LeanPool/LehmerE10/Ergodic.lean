/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/

import LeanPool.LehmerE10.Main
import LeanPool.LehmerE10.CyclotomicKill

/-!
# the E₁₀ Coxeter element as an ERGODIC toral automorphism.
A matrix `M ∈ GL(n, ℤ)` acts on the torus `Tⁿ = ℝⁿ/ℤⁿ` as a group automorphism.  By the
standard criterion (see Walters, *Ergodic Theory*), this automorphism is **ergodic** (with respect
to Haar measure) iff **no eigenvalue of `M` is a root of unity**, equivalently iff the
characteristic polynomial has **no cyclotomic factor**.
For `coxeterE10` the characteristic polynomial is Lehmer's polynomial `L` (`main_theorem`), and
`CyclotomicKill.no_cyclotomic_divisor` proves no cyclotomic polynomial divides `L`.  So the E₁₀
toral automorphism is ergodic — the *unique* ergodic member of the finite/affine E₆..E₉ + hyperbolic
Eₙ series, since E₆,E₇,E₈ (finite) and E₉ (affine) have all-cyclotomic characteristic polynomials.
ERGODIC-THEORY READING (context, not formalized here — the entropy theorem is not in Mathlib):
by Yuzvinskii / Lind–Schmidt–Ward the measure-theoretic entropy of this automorphism equals the
logarithmic Mahler measure `log M(L) = log μ` (`Mahler.lehmer_mahlerMeasure`), the smallest known
positive entropy of an ergodic compact-group automorphism.  Lind's dichotomy: the set of such
entropies is all of `(0,∞]` or countable according to Lehmer's problem (`Mahler.LehmerConjecture`);
via Ornstein's theorem (ergodic compact-group automorphism ≅ Bernoulli shift, classified by entropy)
the moduli space of these automorphisms is uncountable or countable by the same dichotomy.  This
lemma records the *ergodicity* half — provable now — not the entropy value.
-/

open Polynomial

namespace LehmerE10

/-- **The E₁₀ Coxeter toral automorphism is ergodic**: its characteristic polynomial has no
cyclotomic factor, i.e. `coxeterE10` has no root-of-unity eigenvalue.  Immediate from
`coxeter_charpoly_lehmer` (charpoly `= L`) and `no_cyclotomic_divisor` (no
cyclotomic polynomial divides `L`). -/
theorem coxeterE10_ergodic {k : ℕ} (hk : 1 ≤ k) :
    ¬ (cyclotomic k ℤ ∣ coxeterE10.charpoly) := by
  rw [coxeter_charpoly_lehmer]
  exact no_cyclotomic_divisor hk

end LehmerE10
