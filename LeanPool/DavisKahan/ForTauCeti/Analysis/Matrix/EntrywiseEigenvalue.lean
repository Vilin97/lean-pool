/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/

/-
Staged for Tau Ceti, roadmap topic T19.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
addition to `Mathlib/Analysis/Matrix/Spectrum.lean`
(eigenvalue perturbation from entrywise closeness).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]); golfed (collapse a
`have … := by rw [map_sub]; rw [hsub]` to a single `rw [← map_sub]`).
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CourantFischer
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Matrix.EntrywiseOpNorm
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Matrix.SpectralFunctionMeasurable


/-! # Eigenvalue perturbation from entrywise closeness

Weyl's inequality bounds the eigenvalue perturbation by the *operator* norm of the
difference.  Combined with the entrywise→operator-norm comparison
`‖toEuclideanLin A‖ ≤ n · (entrywise sup of A)`, this gives a directly usable
**entrywise** eigenvalue-perturbation bound: if two Hermitian `n × n`
matrices are entrywise `ε`-close, their sorted eigenvalues differ by at most
`n · ε`.

## Main result

* `TauCeti.Matrix.abs_eigenvalues₀_sub_le_of_entry_le`

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.Matrix.EntrywiseEigenvalue`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `2356fd0`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

@[expose] public section

open scoped Matrix
open Module

namespace TauCeti.Matrix

variable {n : ℕ}

/-- **Entrywise eigenvalue perturbation.**  If two Hermitian matrices `A`,
`Ahat` are entrywise `ε`-close, their `k`-th eigenvalues differ by at most
`n · ε` (Weyl's inequality through the entrywise → operator-norm comparison). -/
theorem abs_eigenvalues₀_sub_le_of_entry_le {𝕜 : Type*} [RCLike 𝕜]
    {A Ahat : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (hAhat : Ahat.IsHermitian)
    {ε : ℝ} (hentry : ∀ i j, ‖Ahat i j - A i j‖ ≤ ε)
    (k : Fin (Fintype.card (Fin n))) :
    |hAhat.eigenvalues₀ k - hA.eigenvalues₀ k| ≤ (n : ℝ) * ε := by
  -- Operator-norm bound on the difference, from the entrywise bound.
  have hop : ∀ x : EuclideanSpace 𝕜 (Fin n),
      ‖(Matrix.toEuclideanLin Ahat - Matrix.toEuclideanLin A) x‖ ≤ ((n : ℝ) * ε) * ‖x‖ := by
    intro x
    rw [← map_sub]
    have hentry' : ∀ i j, ‖(Ahat - A) i j‖ ≤ ε := by
      intro i j; simpa [Matrix.sub_apply] using hentry i j
    exact TauCeti.norm_toEuclideanLin_le_of_entry_le hentry' x
  -- Weyl on the symmetric operators.
  exact abs_eigenvalue_sub_eigenvalue_le (opSym hAhat) (opSym hA) finrank_euclideanSpace hop k

end TauCeti.Matrix
