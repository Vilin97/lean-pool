/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.FormBoundedGap
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Specializations
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Real.Specializations
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.Real

/-!
# Davis--Kahan 1970 general sine-theta manuscript surface

The unqualified manuscript names use the complex scalar convention and cover
the complete 1970 gap disjunction: finite interval/exterior separation and both
ordered half-line orientations.  Parallel real problem records and result
aliases are exposed explicitly.  The complex and real routes share the same
legacy statement surface but use the direct genuine engine and exact finite
Ky Fan transport underneath.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970

/-- Complete generalized 1970 target, including ordered half-lines. -/
alias FormBoundedGeneralSinThetaProblem :=
  DavisKahan.ExactSinTheta.FormBoundedGeneralSinThetaProblem

/-- Completed genuine-spectrum finite interval/exterior problem. -/
alias FiniteIntervalGeneralSinThetaProblem :=
  DavisKahan.ExactSinTheta.FiniteIntervalGeneralSinThetaProblem

alias FormBoundedIsometricSinThetaProblem :=
  DavisKahan.ExactSinTheta.FormBoundedIsometricSinThetaProblem

/-- Real lower-frame version of the complete source-shaped problem. -/
alias RealGeneralSinThetaProblem :=
  DavisKahan.ExactSinTheta.RealGeneralSinThetaProblem

alias sinTheta_generalized_bundled_complex :=
  DavisKahan.ExactSinTheta.FormBoundedGeneralSinThetaProblem.result
alias sinTheta_generalized_complementaryBlock_complex :=
  DavisKahan.ExactSinTheta.FormBoundedGeneralSinThetaProblem.complementaryBlock_result

/-- Completed generalized finite interval/exterior theorem. -/
alias sinTheta_generalized_intervalExterior_bundled_complex :=
  DavisKahan.ExactSinTheta.FiniteIntervalGeneralSinThetaProblem.result

/-- Complementary-overlap form of the completed finite interval/exterior theorem. -/
alias sinTheta_generalized_intervalExterior_complementaryBlock_complex :=
  DavisKahan.ExactSinTheta.FiniteIntervalGeneralSinThetaProblem.complementaryBlock_result

/-- The bundled-problem entry point for the complex sine theorem: it takes a
`FormBoundedIsometricSinThetaProblem` record rather than an argument list.  The
direct-argument stronger API is
`TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_complex`; the short
SectionTwo API now uses the where-defined norm boundary.
For source-fidelity evidence, follow the result ledger rather than an alias name. -/
alias sinTheta_bundled_complex :=
  DavisKahan.ExactSinTheta.FormBoundedIsometricSinThetaProblem.result_complex

/-- Real source-facing isometric theorem. -/
alias sinTheta_bundled_real :=
  DavisKahan.ExactSinTheta.FormBoundedIsometricSinThetaProblem.result_real

/-- Real unbounded isometric theorem from a measurable exact spectral set. -/
alias sinTheta_unbounded_spectralSubspace_real :=
  DavisKahan.ExactSinTheta.sinTheta_unbounded_real_spectralSubspace

/-- Real source-facing generalized theorem. -/
alias sinTheta_generalized_bundled_real :=
  DavisKahan.ExactSinTheta.RealGeneralSinThetaProblem.result

/-- Real generalized unbounded theorem from a measurable exact spectral set. -/
alias sinTheta_generalized_unbounded_spectralSubspace_real :=
  DavisKahan.ExactSinTheta.generalizedSinTheta_unbounded_real_spectralSubspace

/-- Real complementary-overlap form of the generalized theorem. -/
alias sinTheta_generalized_complementaryBlock_real :=
  DavisKahan.ExactSinTheta.RealGeneralSinThetaProblem.complementaryBlock_result

/-- Bounded generalized problem, derived through the full-domain closed-operator
bridge rather than owning the canonical proof. -/
alias BoundedGeneralSinThetaProblem :=
  DavisKahan.ExactSinTheta.BoundedGeneralSinThetaProblem

/-- Bounded specialization derived from the canonical generalized theorem. -/
alias sinTheta_generalized_bounded_complex :=
  DavisKahan.ExactSinTheta.BoundedGeneralSinThetaProblem.result

/-- Bounded real lower-frame problem. -/
alias RealBoundedGeneralSinThetaProblem :=
  DavisKahan.ExactSinTheta.RealBoundedGeneralSinThetaProblem

/-- Bounded real generalized specialization. -/
alias sinTheta_generalized_bounded_real :=
  DavisKahan.ExactSinTheta.RealBoundedGeneralSinThetaProblem.result

end DavisKahan1970
end TauCeti
