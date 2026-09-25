/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.TanTheta.Spectrum
public import LeanPool.DavisKahan.DavisKahan.TanTheta.UnboundedGraphAngle
public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.TanTheta.RitzResidual
public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63FiniteSource
public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63InfiniteTrial
public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63Unbounded
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section2TanThetaPerturbation
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Section6Theorem63Presentation -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 6.3, presented by scope

Theorem 6.3 is proved at several scopes, in several modules, and this gives
each one its paper-facing name in one place: the finite strict-lower-rank and
equal-rank specializations, the bounded source-faithful statement, the
unbounded arbitrary-ideal statement, the operator-norm graph-angle companion,
the Ky Fan root, and the forms that construct the tangent representative
instead of assuming one.

Each docstring says which scope its target actually has, so a reader comparing
these names against the printed theorem can see what is a specialization and
what is the full statement.
-/

open scoped InnerProductSpace
open Set

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open DavisKahanExt

universe u v

section GeneralizedTangent

/-!
## Source-audit correction for Theorem 6.3

The previous frontier draft mistranscribed the paper.  Davis--Kahan Theorem 6.3
assumes a strict dimension inequality between the coordinate spaces and defines
`tan Θ₀` from the singular values of the directed cross block `E₀⋆ F₁`.  It does
not infer the symmetric relation `IsAcute Z V` from an abstract isometric
embedding of the smaller space into the larger one.

The bounded strict-dimension theorem is now proved at the paper's effective
scope: finite trial coordinates and an arbitrary complete ambient Hilbert
space.  This follows from the paper's global separability convention together
with its strict Hilbert-dimension inequality.  The equal-dimension tangent
theorem and the Appendix's full unbounded arbitrary-ideal extension remain
separate open endpoints.
-/

/-- Compiled finite-dimensional strict-lower-rank specialization of
Davis--Kahan 1970, Theorem 6.3.  This is intentionally not named as the full
source endpoint. -/
alias theorem6_3_finite_generalizedTanTheta_ideal :=
  DavisKahan.FiniteDimensional.davisKahan1970_generalizedTanTheta0_ritzResidual_le

/-- Compiled finite-dimensional equal-rank specialization of the Section 2
single-angle tangent theorem. -/
alias theorem6_3_equalRank_finite_tanTheta_ideal :=
  DavisKahan.FiniteDimensional.davisKahan1970_tanTheta0_ritzResidual_le

/-- Compiled unbounded graph-angle companion at operator norm.  This is useful
partial source coverage but does not discharge the paper's arbitrary
unitarily-invariant-norm statement. -/
alias theorem6_3_unbounded_graphAngle_opNorm_partial :=
  DavisKahan.TanTheta.tanTheta_unbounded_graphAngle_trialBlock

/-- The unbounded tangent theorem with an arbitrary tangent representative supplied. -/
alias theorem6_3_unbounded_tanTheta_ideal :=
  TanTheta.theorem6_3_unbounded_ideal

/-- Retained: the operator-norm graph-angle companion.  Useful partial coverage, and
**not** the arbitrary-unitarily-invariant-norm scope claim -- that is the alias above. -/
alias theorem6_3_unbounded_graphAngle_opNorm_companion :=
  DavisKahan.TanTheta.tanTheta_unbounded_graphAngle_trialBlock

/-- Completed finite-trial/arbitrary-ambient Ky Fan root of Theorem 6.3. -/
alias theorem6_3_all_kyFan_core :=
  TanTheta.theorem6_3_all_kyFan_core

/-- Completed bounded source-faithful Davis--Kahan Theorem 6.3. -/
alias theorem6_3_generalizedTanTheta_ideal :=
  TanTheta.theorem6_3_generalizedTanTheta_ideal

/-! ### Theorem 6.3 without a tangent-representative hypothesis

The two aliases above quantify over a `tanTheta0` satisfying
`HasTheorem63DirectedTangentApproximationNumbers`, and until 2026-08-05 nothing
in the repository constructed one — so the compiled Theorem 6.3 was a
conditional whose antecedent had no witness, which is weaker than what Davis and
Kahan assert.

`theorem63DirectedTangent` is the witness: diagonal in the right singular basis
of the sine block, with entries `tan (arcsin sᵢ)`.  Its finiteness needs
`sᵢ < 1`, and that is not a new hypothesis — `theorem63_singularValues_sine_lt_one`
derives it from the source gap the theorem already assumes.  The two aliases
below therefore carry exactly the printed hypotheses and nothing else. -/

/-- The directed tangent representative of Theorem 6.3, and the proof that it
has the approximation numbers the theorem asks for. -/
alias theorem6Point3DirectedTangent :=
  TanTheta.theorem63DirectedTangent

alias theorem6_3_directedTangent_approximationNumbers :=
  TanTheta.hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent

/-- Theorem 6.3's Ky Fan root with the representative supplied, not assumed. -/
alias theorem6_3_all_kyFan_core_unconditional :=
  TanTheta.theorem6_3_all_kyFan_core_directedTangent

/-- Theorem 6.3 at ideal-gauge scope with the representative supplied, not
assumed. -/
alias theorem6_3_generalizedTanTheta_ideal_unconditional :=
  TanTheta.theorem6_3_generalizedTanTheta_ideal_directedTangent

/-! ### The equal-rank tangent theorem

Section 2's tangent theorem is about a pair of subspaces of **equal** rank, so
it cannot be obtained by specialising a statement that assumes
`rank Z < rank V`.  It does not have to be: the printed `dim X(E₀) < dim X(F₀)`
does one job — under the paper's separability convention it forces the trial
coordinate space to be finite-dimensional — and here that is an explicit
instance hypothesis.  Lean had already recorded the redundancy, binding the
comparison as `_hStrictDimension` and never using it.

`theorem6_3_equalRank_tanTheta_ideal` is the residual half of the Section 2
tangent theorem at arbitrary unitarily invariant ideal-gauge scope, in an
arbitrary complete complex Hilbert space, with a finite-dimensional trial
space and no dimension comparison. -/

/-- The equal-rank tangent bound from form bounds. -/
alias theorem6_3_equalRank_tanTheta_formBounds :=
  TanTheta.theorem6_3_generalizedTanTheta_of_formBounds_equalRank

/-- The equal-rank tangent bound in the source's spectral-separation form. -/
alias theorem6_3_equalRank_tanTheta_ideal :=
  TanTheta.theorem6_3_generalizedTanTheta_equalRank_spectral

/-! ### The equal-dimensional infinite/noncompact tangent theorem

The two aliases above still assume a finite-dimensional trial space.  The paper's
Section 2 claims the theorem for arbitrary equal-dimensional pairs in an infinite
Hilbert space, and its Appendix supplies the missing case by the finite-projector
cutoff/Ky-Fan limiting argument.  That passage is formalized in
`DavisKahan/TanTheta/Theorem63InfiniteTrial.lean`: the trial subspace carries **no**
dimension hypothesis, the tangent representative is exhibited with the paper's
approximation numbers (`tan (arcsin sᵢ)` over the directed sine block's approximation
numbers), and the bound holds in every Fan-dominant unitarily invariant ideal gauge.

The residual half is stated in the source's spectral-separation form and in form-bound
form; the perturbation companion assumes invariance of the trial space under the
perturbed operator, exactly as in the finite case. -/

/-- Section 2 tangent theorem, residual half, at arbitrary trial dimension and
ideal-gauge scope, spectral-separation form. -/
alias theorem6_3_equalDimension_tanTheta_ideal_spectral :=
  TanTheta.theorem6_3_infiniteTrial_spectral_exists

/-- Section 2 tangent theorem, residual half, at arbitrary trial dimension and
ideal-gauge scope, form-bound form. -/
alias theorem6_3_equalDimension_tanTheta_ideal_formBounds :=
  TanTheta.theorem6_3_infiniteTrial_of_formBounds_exists

/-- Section 2 tangent theorem, perturbation half, at arbitrary trial dimension and
ideal-gauge scope. -/
alias theorem6_3_equalDimension_tanTheta_perturbation :=
  TauCeti.DavisKahan1970.theorem6_3_perturbation_infiniteTrial

end GeneralizedTangent
end DavisKahan1970
end TauCeti
