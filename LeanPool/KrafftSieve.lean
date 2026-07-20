/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import LeanPool.KrafftSieve.Defs
import LeanPool.KrafftSieve.Basic
import LeanPool.KrafftSieve.ThirdHarmonic
import LeanPool.KrafftSieve.Variance
import LeanPool.KrafftSieve.SelbergWeights
import LeanPool.KrafftSieve.OptimalWeights
import LeanPool.KrafftSieve.MainTheorem

/-!
# A Conditional Sieve Criterion for Twin Primes via Krafft Geometry

Source: doi:10.5281/zenodo.19763833
Authors: Fernando Portela
Status: verified
Main declarations: `KrafftSieve.mu_min_lt_one_implies_tpc`
Tags: analytic-number-theory, sieve-theory, twin-primes, optimization
MSC: 11N05, 11N35
-/

/-!
## Mathematical overview

This project implements a formalization of a weighted Turán Sieve approach to the
Twin Prime Conjecture, utilizing the Krafft Geometry.

### Main Results

This project's headline result is **conditional**: it reduces the Twin Prime Conjecture to a
spectral hypothesis on the Rayleigh quotient $\mu_{min}(n)$. The hypothesis $\mu_{min}(n) < 1$
is **not** established here for any $n$; indeed `resonance_lt_mainTerm` formalizes the
parity-barrier deficit showing the one-dimensional sieve cannot beat the main term. The value
of this formalization is in the verified sieve machinery, not a claim of progress on the
conjecture itself. The conditional results are captured by:
* `KrafftSieve.mu_min_lt_one_implies_tpc`: If there are infinitely many intervals where the
  multidimensional optimal weight achieves a ratio strictly less than 1, then there are
  infinitely many twin primes.
* `krafft_sieve_guarantee_with_mu_min`: The Krafft Sieve Guarantee holds if $\mu_{min}(n) < 1$.
* `Krafft_Sufficiency`: Defines the exact set of conditions for the sieve to be considered
  successful.

### Major Analytical Building Blocks

* `krafft_sieve_guarantee`: A generic formulation proving that the existence of a valid weight
  function satisfying the variance constraints guarantees the discovery of Twin Primes.

### Independent Analytical Results

The following independent results provide structural motivation and spectral analysis of the sieve:
* `resonance_lt_mainTerm`: Establishes the core inequality where the main term dominates the
  error/resonance terms.
* `third_harmonic_extraction`: Extracts the critical third harmonic frequency from the Fourier
  domain analysis of the weighted hit counts.
* `parseval_identity`: Links the variance of the survivor distribution strictly to the sum of
  the squared magnitudes of its non-zero Fourier coefficients.
* `W_truly_multi`: Constructs the multi-dimensional optimal weight function crucial for driving
  down the physical variance.
-/
