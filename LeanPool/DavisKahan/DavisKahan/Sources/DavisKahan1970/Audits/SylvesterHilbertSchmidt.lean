/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.UnitaryInvariantNormInstances
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtPairwise

/-!
# Audit surface for the literal square-norm Sylvester theorem

This module is intentionally excluded from ordinary aggregates. Compile it
directly after repairing the new infrastructure, then inspect the trusted
assumptions of every declaration below.

Updated 2026-07-29: the uniqueness half of the chain no longer runs through
Spectra's generator-intertwiner, so auditing
`generatorIntertwiner_eq_zero_of_disjoint_spectrum`,
`spectralProjection_intertwines_of_generator` and `GeneratorIntertwines.group`
was auditing constants the theorem no longer depends on.  They are replaced by
the single native endpoint
`TauCeti.LinearPMap.eq_zero_of_intertwines_of_disjoint_spectrum`.  The remaining
`Spectra.HilbertSchmidtTensor.*` entries are SR-D's, and are still load-bearing.

Also 2026-07-29: the direct `Spectra.QuantumMechanics.BornRule.Joint.ProjectivePVM`
import was dropped.  Nothing in this file referenced a declaration from it — the

/-! # Sylvester Hilbert Schmidt -/
Born-rule module was reached anyway, transitively, through
`Sylvester.HilbertSchmidtPairwise`, so the explicit import bought nothing and
made this file look like an independent Spectra consumer when it is not.
-/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

end ExactSinTheta
end DavisKahan
end TauCeti
