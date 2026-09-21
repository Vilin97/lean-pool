/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.PrincipalPlanes.Basic
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.PrincipalPlanes.Spectrum
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.PrincipalPlanes.Variational

/-!
# Principal planes of an acute pair

This file constructs the finite principal planes used in Davis--Kahan Section 4
without assuming a `FiniteTwoProjection` API.  The source vectors are the
nonzero right singular vectors of the directed sine block
`P_{V orthogonal} P_U`.  If `s_i` is the corresponding singular value, put
`c_i = sqrt (1-s_i^2)` and

`j_i = s_i^{-1} (R u_i - c_i u_i)`,

where `R` is the canonical direct rotation.  Acuteness gives `c_i > 0`, and the
polar identities give

`R u_i = c_i u_i + s_i j_i`,
`R j_i = -s_i u_i + c_i j_i`.

The family `(u_i,j_i)` is orthonormal, the `s_i` are decreasing, and the
singular values of `I-R` are the duplicated chord lengths
`d_i = sqrt (2(1-c_i))`.

This module is a thin re-export aggregate.  The material is split by topic into

* `PrincipalPlanes.Basic`: the principal-plane definitions and the `2 x 2`
  rotation block on each plane;
* `PrincipalPlanes.Spectrum`: the vanishing-direction descent lemmas and the
  spectrum of the direct displacement `I - R`;
* `PrincipalPlanes.Variational`: Davis's variational theorem for the restricted
  displacement.

## The sound Section 4 package

* `singularValues_directRotation_displacement`: the singular values of `I - R`
  are the principal chords, each occurring twice
  (`sigma_k (I-R) = 2 sin (theta_{k/2} / 2)`).
* `kyFanSum_directRotation_displacement_eq_principalChords`: closed Ky Fan
  formula for `I - R`.
* `principalPlaneChord_le_singularValues_restrictedDisplacement` (Davis 1958
  Theorem 7.2 / Davis--Kahan Proposition 4.1): for every unitary `W` carrying
  `U` onto `V`, the `k`-th singular value of the restricted displacement
  `(I - W) P_U` is at least the `k`-th principal chord.  Combined with the
  closed form `singularValues_restrictedDisplacement_directRotation`, the
  direct rotation minimizes every singular value of the restricted
  displacement pointwise — over any `RCLike` field, and with no largest-angle
  threshold (the standing `IsAcute` hypothesis is what makes the direct
  rotation exist, not a restriction on the conclusion).
* `kyFanSum_restrictedDisplacement_le` and
  `uiNorm_restrictedDisplacement_le` (Davis--Kahan Corollary 4.1): Ky Fan and
  unitarily-invariant-norm minimality of the restricted displacement.

## What is deliberately absent

The historical candidate for Proposition 4.4 — "if the largest principal angle
is at most `pi/3`, the direct rotation minimizes every UI norm of the full
displacement `I - W` over real scalars" — is **false**: rotating by `2 theta`
in a single plane spanned across two equal principal angles `theta` carries
`U` onto `V` with a strictly smaller trace norm than the direct rotation, for
every `theta` in `(0, pi/2)`.  See
`DavisKahan.FiniteDimensional.DirectRotation.ShortRotationCounterexample`.
The per-plane compression route sketched in the source-derived draft is
likewise unsound: a competitor may leak mass out of a principal plane, so the
compression of `I - W` to a principal plane need not dominate the chord.  Only
the restricted-displacement statements above survive, and they need no angle
hypothesis at all.
-/
