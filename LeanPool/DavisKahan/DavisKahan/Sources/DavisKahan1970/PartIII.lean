/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Interval
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.Basic
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.SinTheta.TrialMap
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.TanTheta.RitzResidual
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.TanTheta.Vector
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DoubleAngle.SinTheta
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DoubleAngle.TanTheta

/-!
# Finite Davis--Kahan Part III specialization surface

This module is the stable source-facing import surface for the finite Part III
results that are currently proved in the library. It is a specialization and a
low-dependency proof surface, not the completion boundary for the 1970 paper.
The default project goal remains the source's Hilbert-space theory, including
the bounded main body, arbitrary unitary-invariant norm scope, and unbounded
passages.

The source package exposed here includes:

* the sharp ordered and interval/exterior Sylvester estimates for arbitrary
  rectangular unitarily invariant norms;
* the generalized `sin Theta` theorem for arbitrary trial maps, in the paper's
  lower-Gram-bound and equisingular-representative form;
* the ordinary perturbation `sin Theta` theorem for every unitarily invariant
  norm;
* the equal-rank and strict-lower-rank Ritz-residual `tan Theta` theorems for
  arbitrary rectangular unitarily invariant norms, with tangents directed from
  the trial subspace toward the exact invariant subspace;
* the `sin 2 Theta` perturbation theorem for every unitarily invariant norm;
* the sharp operator-norm `tan 2 Theta` theorem, including its strict
  quarter-turn conclusion;
* the sharp finite projector-difference companions.

The older per-vector tangent theorem remains available as a useful elementary
endpoint, but it is not the strongest source-facing tangent result.

This module does not claim that all numbered results of the 1970 paper are
represented.  In particular, the direct-rotation extremal theory, the exact
source form of the non-ordered Sylvester theorem, the unbounded appendix, the
canonical continuation and spectral-repulsion package, and the planar
sharpness/numerical examples require separate source modules and proof audits.
Those developments must not be inferred merely from the quartet aliases below.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

/-! ## Sections 3--4: direct rotation foundation -/

/-- The canonical finite direct rotation maps the first subspace onto the
second. -/
alias partIII_directRotation_map_eq :=
  directRotation_map_eq

/-- The canonical direct rotation intertwines the two orthogonal
projections. -/
alias partIII_directRotation_intertwines_projection :=
  directRotation_comp_projection

/-! ## Section 5: the Sylvester engine -/

/-- The sharp ordered-separation Sylvester estimate for every rectangular
unitarily invariant norm. -/
alias partIII_sylvester_ordered_uiNorm :=
  uiNorm_sylvester_le_of_orderedGap

/-- The sharp interval/exterior Sylvester estimate for every rectangular
unitarily invariant norm. -/
alias partIII_sylvester_interval_uiNorm :=
  uiNorm_sylvester_le_of_intervalGap

/-! ## Section 6: single-angle theorems -/

/-- The finite Part III `sin Theta` residual theorem for every rectangular
unitarily invariant norm. -/
alias partIII_sinTheta_residual_uiNorm :=
  sinTheta_residual_le

/-- The paper's generalized `sin Theta` theorem in its Gram-bound and arbitrary
representative form.

The trial map need not be an isometry.  The representative `sinTheta0` may be
any rectangular operator with the singular values of the canonical directed
sine block. -/
alias partIII_generalizedSinTheta_uiNorm :=
  generalizedSinTheta0_residual_le_of_gramLowerBound

/-- The finite Part III `sin Theta` perturbation theorem for every unitarily
invariant norm.

This is an exact canonical alias of
`UnitarilyInvariantSeminorm.apply_starProjection_comp_starProjection_le`.
Its proof is the ordered Sylvester argument followed by the ideal property of
the chosen unitarily invariant norm. -/
alias partIII_sinTheta_uiNorm :=
  UnitarilyInvariantSeminorm.apply_starProjection_comp_starProjection_le

/-- The full-space canonical sine-angle-operator form.  It records explicitly
the forward and reverse interval/exterior hypotheses needed for a
constant-one estimate in an arbitrary square unitarily invariant norm. -/
alias partIII_sinTheta_angleOperator_uiNorm :=
  sinAngleOperator_perturbation_le

/-- The equal-rank Ritz-residual `tan Theta` theorem for every rectangular
unitarily invariant norm.

The trial basis `X` is isometric, the coordinate operator is the Ritz
compression `X star A X`, and `tanTheta0` may be any rectangular operator with
the canonical directed principal-tangent singular values.  Transversality is a
consequence of the spectral hypotheses rather than a public premise. -/
alias partIII_tanTheta_ritzResidual_uiNorm :=
  davisKahan1970_tanTheta0_ritzResidual_le

/-- The strict-lower-rank generalized Ritz-residual `tan Theta` theorem for
every rectangular unitarily invariant norm. -/
alias partIII_generalizedTanTheta_ritzResidual_uiNorm :=
  davisKahan1970_generalizedTanTheta0_ritzResidual_le

/-- The strongest common tangent wrapper: it records both transversality and
the arbitrary-UI-norm residual inequality. -/
alias partIII_tanTheta_ritzResidual_uiNorm_and_isTransverse :=
  tanTheta0_ritzResidual_le_and_isTransverse

/-- The finite Part III `tan Theta` theorem in pole-free per-vector form.

This compatibility alias retains the elementary spectral-norm endpoint.  New
source-facing uses that need the paper's arbitrary-UI-norm conclusion should
prefer `partIII_tanTheta_ritzResidual_uiNorm`. -/
alias partIII_tanTheta_vector :=
  TauCeti.tan_theta_le

/-! ## Sections 7--8: double-angle theorems -/

/-- The finite Part III `sin 2 Theta` theorem for every unitarily invariant
norm.

This is an exact canonical alias of
`UnitarilyInvariantSeminorm.sin_two_theta_starProjection_le`.  The proof reflects
the reference operator through the perturbed reducing subspace, applies the
single-angle theorem to the reflected pair, and identifies the cross block
with one half of `sin 2 Theta`. -/
alias partIII_sinTwoTheta_uiNorm :=
  UnitarilyInvariantSeminorm.sin_two_theta_starProjection_le

/-- The same `sin 2 Theta` conclusion in the canonical full-space
angle-operator representation. -/
alias partIII_sinTwoTheta_angleOperator_uiNorm :=
  sinTwoTheta_perturbation_le

/-- The finite Part III `tan 2 Theta` theorem in its sharp operator-norm form.

This is an exact canonical alias of `TauCeti.tan_two_theta_norm_sub_le`.
Besides the sharp factor-two estimate, the conclusion proves that the maximal
angle is strictly below `pi / 4`, so the tangent remains on the acute branch. -/
alias partIII_tanTwoTheta_opNorm :=
  TauCeti.tan_two_theta_norm_sub_le

/-! ## Projector companions -/

/-- The sharp factor-one finite projector-difference theorem.

For symmetric `A, B` with reducing subspaces carrying two-sided spectral gaps,
`norm (P_U - P_W) <= epsilon / g`, with no rank hypothesis and no factor-two
loss. -/
alias projector_difference_opNorm :=
  opNorm_starProjection_sub_le

/-- The sharp projector-difference theorem for canonical spectral subspaces. -/
alias spectralProjector_difference_opNorm :=
  opNorm_pointSpectralSubspace_sub_le

end DavisKahan.FiniteDimensional
end TauCeti
