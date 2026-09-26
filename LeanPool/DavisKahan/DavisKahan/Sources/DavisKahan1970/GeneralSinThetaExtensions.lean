/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.GeneralSinTheta
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.Reducing
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.Generalized
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.Bounded
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.GapConvenience
public import LeanPool.DavisKahan.DavisKahan.SinTheta.NaturalTwoSubspace

/-!
# Optional natural-input extensions to the general sine-theta surface

The compiler-accepted `GeneralSinTheta` facade remains unchanged.  This separate
module exposes reducing-subspace, bounded natural-input, generalized complex
spectral-subspace, gap-constructor, and symmetric two-direction conveniences.
After this leaf is compiler-accepted, its aliases can be folded into the main
source facade without changing the verified theorem chain.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970

/-- Complex isometric unbounded theorem from a measurable exact spectral set. -/
alias sinTheta_unbounded_spectralSubspace_complex :=
  DavisKahan.ExactSinTheta.sinTheta_unbounded_spectralSubspace_of_spectrumGap

/-- Complex generalized unbounded theorem from a measurable exact spectral set. -/
alias sinTheta_generalized_unbounded_spectralSubspace_complex :=
  DavisKahan.ExactSinTheta.generalizedSinTheta_unbounded_spectralSubspace_of_spectrumGap

/-- Scalar-generic natural isometric problem over a reducing exact subspace. -/
alias NaturalReducingIsometricSinThetaProblem :=
  DavisKahan.ExactSinTheta.NaturalReducingIsometricSinThetaProblem

/-- Scalar-generic natural lower-frame problem over a reducing exact subspace. -/
alias NaturalReducingGeneralSinThetaProblem :=
  DavisKahan.ExactSinTheta.NaturalReducingGeneralSinThetaProblem

/-- Complex natural theorem when the exact subspace is supplied as reducing. -/
alias sinTheta_unbounded_reducingSubspace_complex :=
  DavisKahan.ExactSinTheta.sinTheta_unbounded_complex_reducingSubspace

/-- Real natural theorem when the exact subspace is supplied as reducing. -/
alias sinTheta_unbounded_reducingSubspace_real :=
  DavisKahan.ExactSinTheta.sinTheta_unbounded_real_reducingSubspace

/-- Complex lower-frame theorem when the exact subspace is supplied as reducing. -/
alias sinTheta_generalized_unbounded_reducingSubspace_complex :=
  DavisKahan.ExactSinTheta.generalizedSinTheta_unbounded_complex_reducingSubspace

/-- Real lower-frame theorem when the exact subspace is supplied as reducing. -/
alias sinTheta_generalized_unbounded_reducingSubspace_real :=
  DavisKahan.ExactSinTheta.generalizedSinTheta_unbounded_real_reducingSubspace

/-- Bounded complex isometric theorem from a measurable exact spectral set. -/
alias sinTheta_bounded_spectralSubspace_complex :=
  DavisKahan.ExactSinTheta.sinTheta_bounded_spectralSubspace_of_spectrumGap

/-- Bounded complex generalized theorem from a measurable exact spectral set. -/
alias sinTheta_generalized_bounded_spectralSubspace_complex :=
  DavisKahan.ExactSinTheta.generalizedSinTheta_bounded_spectralSubspace_of_spectrumGap

/-- Bounded real isometric theorem from a measurable exact spectral set. -/
alias sinTheta_bounded_spectralSubspace_real :=
  DavisKahan.ExactSinTheta.sinTheta_bounded_spectralSubspace_real

/-- Bounded real generalized theorem from a measurable exact spectral set. -/
alias sinTheta_generalized_bounded_spectralSubspace_real :=
  DavisKahan.ExactSinTheta.sinTheta_generalized_bounded_spectralSubspace_real

end DavisKahan1970
end TauCeti
