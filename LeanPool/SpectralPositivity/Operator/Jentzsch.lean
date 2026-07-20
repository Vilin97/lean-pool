/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.SpectralPositivity.Operator.JentzschProof

/-!
# Jentzsch's Theorem — Clean API

Re-exports the main results from JentzschProof.lean with clean
theorem names for downstream use.

The full proof (1082 lines, 7 phases, 0 sorries) is in JentzschProof.lean,
generalized from L²(ℝⁿ) to L²(Ω, volume) for any MeasureSpace Ω.

## Main results

- `jentzsch_theorem_proved` — the full theorem
- `abs_apply_le_apply_abs` — Phase 1: |Tf| ≤ T|f|
- `abs_inner_le_inner_abs` — Phase 2: |⟨f,Tf⟩| ≤ ⟨|f|,T|f|⟩
- `abs_eigenvector_of_top_eigenvector` — Phase 3: |f| is ground state
- `ground_state_strictly_positive` — Phase 4: ψ₀ > 0 a.e.
- `eigenvector_constant_sign` — Phase 5: ground states have constant sign
- `top_eigenvalue_simple` — Phase 6: λ₀ is simple
- `spectral_gap` — Phase 7: |λ| < λ₀

## References

- Reed-Simon IV, Theorems XIII.43–44
-/
