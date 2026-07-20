/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactOperatorOrthonormal
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.Approximation
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.CutoffProjector
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.OpNormEigenvalue
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.SpectralFiniteness
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.SpectralTheorem
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.RayleighCompact
import LeanPool.CompactSpectral.Topology.WeakHilbertCompact

/-!
# Spectral theorem for compact self-adjoint operators

Source: doi:10.3792/euclid/9781429799911-2
Authors: Adam Benenson
Status: verified
Main declarations: `CompactSelfAdjoint.exists_hasEigenvector_iSup_or_iInf_of_isCompactOperator`
Tags: spectral-theory, functional-analysis, compact-operators
MSC: 47A75, 47B07
-/

/-!
# Compact self-adjoint spectral theory

This is the root import file for the `CompactSpectral` library. It re-exports every
module in the library so that downstream files can `import CompactSpectral` to obtain
the full spectral theorem for compact self-adjoint operators on Hilbert spaces.

## Overview

* **WeakHilbertCompact** — weak compactness of Hilbert closed balls
* **RayleighCompact** — Rayleigh quotient extrema for compact operators
* **CompactOperatorOrthonormal** — compact operators on orthonormal sequences
* **CompactSelfAdjoint** — compression/restriction helpers
* **SpectralFiniteness** — finiteness of large eigenvalues
* **CutoffProjector** — large-eigenspace cutoff projectors
* **Approximation** — finite-rank approximation in operator norm
* **OpNormEigenvalue** — eigenvalue at the operator norm
* **SpectralTheorem** — Hilbert basis of eigenvectors
-/
