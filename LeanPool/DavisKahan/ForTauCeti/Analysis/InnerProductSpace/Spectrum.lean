/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

Staged for Tau Ceti, roadmap topic T01.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum


/-! # Eigenvector cross-term identity for a perturbation

For symmetric operators `T`, `S` on a finite-dimensional inner product space,
with `u i` the `i`-th eigenvector of `T` (eigenvalue `λ i`) and `v j` the
`j`-th eigenvector of `S` (eigenvalue `μ j`),

`⟪u i, (S - T) (v j)⟫ = (μ j - λ i) * ⟪u i, v j⟫`.

This three-line identity is the seed of every Davis–Kahan-style subspace
perturbation bound: cross terms between well-separated parts of the spectra
are controlled by the perturbation `S - T` divided by the eigenvalue gap.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.Spectrum`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `56f7495`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/--
**Cross-term identity.** The matrix entry of the perturbation `S - T` between
the `i`-th eigenvector of `T` and the `j`-th eigenvector of `S` is the
eigenvalue difference times the overlap of the two eigenvectors.
-/
theorem inner_eigenvectorBasis_map_sub_eigenvectorBasis
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i j : Fin n) :
    ⟪hT.eigenvectorBasis hn i, (S - T) (hS.eigenvectorBasis hn j)⟫_𝕜
      = ((hS.eigenvalues hn j - hT.eigenvalues hn i : ℝ) : 𝕜)
          * ⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜 := by
  have hSterm : ⟪hT.eigenvectorBasis hn i, S (hS.eigenvectorBasis hn j)⟫_𝕜
      = ((hS.eigenvalues hn j : ℝ) : 𝕜)
          * ⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜 := by
    rw [hS.apply_eigenvectorBasis, inner_smul_right]
  have hTterm : ⟪hT.eigenvectorBasis hn i, T (hS.eigenvectorBasis hn j)⟫_𝕜
      = ((hT.eigenvalues hn i : ℝ) : 𝕜)
          * ⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜 := by
    rw [← hT (hT.eigenvectorBasis hn i) (hS.eigenvectorBasis hn j),
      hT.apply_eigenvectorBasis, inner_smul_left, RCLike.conj_ofReal]
  rw [LinearMap.sub_apply, inner_sub_right, hSterm, hTterm, RCLike.ofReal_sub]
  ring

end TauCeti
