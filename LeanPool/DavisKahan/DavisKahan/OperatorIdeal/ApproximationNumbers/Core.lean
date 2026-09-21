/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Core

/-!
# The paper library's spelling of the approximation-number foundation

**Every declaration here is a forwarding name.**  The mathematics lives in
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean` under the generic
namespace `TauCeti.ApproximationNumber`; this module re-exports it under
`TauCeti.DavisKahan.ExactSinTheta`, which is the name 339 references in this
library already use.

## Why the split

The module was lifted into `ForTauCeti` because its imports are `ForTauCeti` leaves and
Mathlib — it is generic approximation-number theory.  But it carried the enclosing
namespace `TauCeti.DavisKahan.ExactSinTheta` with it: **a paper's name and a
staging word, inside the library staged for Tau Ceti.**  A submission reviewer reads
`Experimental` as a warning.

Renaming the namespace outright is not available: it is *shared*, not owned — 283 of its
references across `DavisKahan` are `namespace`/`open`/`end` lines belonging to other
modules.  So the generic library gets the generic name and the paper library keeps its
spelling, which is the same division of labour as
`DavisKahan/BoundedOperator/Compat.lean`.

**Do not add mathematics to this file.**  A new approximation-number result belongs in
`ForTauCeti` under `TauCeti.ApproximationNumber`; if this library wants the shorter name,
add it to the `export` list below.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: this path held the mathematics itself until it moved to `ForTauCeti`.
* Extraction class: **not for extraction** — this is paper-library vocabulary.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

export TauCeti.ApproximationNumber (
  StronglyTendsto IsOrthogonalProjectionMap approximationSingularValue
  approximationSingularValue_nonneg approximationSingularValue_zero_map approximationSingularValue_zero
  approximationSingularValue_smul approximationSingularValue_neg approximationSingularValue_antitone
  approximationSingularValue_le_opNorm approximationSingularValue_add_le approximationSingularValue_adjoint
  approximationSingularValue_comp_le singularValues_le_approximationSingularValue approximationSingularValue_eq_singularValues
  IsOrthogonalProjectionMap.norm_apply_le IsOrthogonalProjectionMap.norm_le_one tendsto_opNorm_zero_of_finiteDimensional
  approximationSingularValue_comp_le_of_isOrthogonalProjection approximationSingularValue_comp_strongProjection_tendsto_of_minMax approximationSingularValue_comp_strongProjection_tendsto_complex
  kyFanApproximationGauge kyFanApproximationGauge_eq_kyFanGauge kyFanApproximationGauge_neg
  kyFanApproximationGauge_comp_strongProjection_tendsto_of_minMax
    kyFanApproximationGauge_comp_strongProjection_tendsto_complex
    kyFanSum_le_kyFanApproximationGauge
  kyFanSum_eq_kyFanApproximationGauge kyFanApproximationGauge_add_le_finiteDimensional
    approximationSingularValue_restrict_mono
  approximationSingularValue_orthogonalProjectionOnto_comp_eq kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq kyFanApproximationGauge_add_le_finiteSource
  kyFanApproximationGauge_add_le_of_minMax exists_finiteRestrictionApproximationNumber_add_gt kyFanApproximationGauge_add_le_complex
  kyFanApproximationGauge_zero kyFanApproximationGauge_zero_map kyFanApproximationGauge_one
  kyFanApproximationGauge_smul kyFanApproximationGauge_nonneg kyFanApproximationGauge_adjoint
  kyFanApproximationGauge_comp_le opNorm_le_kyFanApproximationGauge kyFanApproximationGauge_le_nat_mul_opNorm
)

end ExactSinTheta
end DavisKahan
end TauCeti
