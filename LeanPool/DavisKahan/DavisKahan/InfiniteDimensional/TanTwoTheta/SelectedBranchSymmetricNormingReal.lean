/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.SelectedBranchSymmetricNorming
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleReal
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.FormTransport
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.ComplexificationGauge

/-!
# The selected-branch `tan 2Θ` theorem over a real Hilbert space

Standing assumption 1 of Davis--Kahan 1970 is that the Hilbert space is "real or
complex", and the paper says explicitly that "all four theorems are applicable
for infinite- as well as finite-dimensional spaces".  This module supplies the
real half of `tanTwoTheta_selectedBranch_symmetricNorming`.

## Scope: this is the selected-branch form, NOT the Section 2 theorem

Read this before citing the theorem below.

The printed Section 2 `tan 2θ` theorem assumes only `spectrum(A₀) ⊆ [β, α]`,
`spectrum(A₁) ⊆ [α + δ, ∞)` -- conditions on the blocks of the *unperturbed*
operator -- together with `H₀ = H₁ = 0`.  The reducing subspace `Q` of `A + H`
is **arbitrary**, and the conclusion is the norm inequality alone.

The theorem below, like its complex donor, additionally assumes ordered form
bounds on `A + H` restricted to `V` and `Vᗮ` (`hVlow`, `hVperpHigh`).  Those are
spectral placements of `Λ₀` and `Λ₁`, which the source does not assume, and they
are exactly what lets `IsQuarterAcute U V` be concluded.  So this is the
*selected-branch* theorem -- the configuration of Theorem 8.1 -- and it must not
be used to certify the unrestricted Section 2 row.

The paper is explicit that the difference is real, at the head of Section 8:
"The double-angle conclusions also allow angles close to `π/2`. … the
double-angle theorems imposed no special choice of the reducing subspace `QH` of
`A + H`."  A branch-free real `tan 2Θ` is still open; see the `S2-tan-two-theta`
census row.

The theorem is nonetheless the right real object for Section 8 and for
applications, where the branch *is* selected.

No perturbation theory is repeated.  The proof complexifies the entire real
configuration, applies the complex theorem verbatim, and pulls the conclusion
back.  Every step of that is a transport lemma that already exists or was added
alongside this file:

* hypotheses -- `complexify_isSelfAdjoint_iff`, `mapsTo_complexifySubmodule`,
  `le_re_inner_of_mem_complexifySubmodule`,
  `re_inner_le_of_mem_complexifySubmodule`,
  `mapsTo_orthogonal_complexifySubmodule`,
  `mapsTo_of_mem_orthogonal_complexifySubmodule`,
  `SymmetricNormingFunction.mem_complexify_iff`;
* conclusion -- `isQuarterAcute_complexifySubmodule_iff` and
  `SymmetricNormingFunction.gauge_complexify`.

Crucially the transport is *lossless*: the form constants `a` and `b` and the
gauge values are preserved exactly, so the real conclusion carries the same
sharp constant `b - a` as the complex one.

## What the angle operator is

The conclusion is phrased with `directedTanTwoAngleOperatorRC U V`, which is by
definition `directedTanTwoAngleOperatorC` of the two complexified subspaces.  That is the
faithful real object here rather than a workaround: the source theorem bounds a
unitarily-invariant norm, a unitarily-invariant norm sees only the approximation
singular values, and `approximationSingularValue_complexify` says those are
exactly the singular values of the real angle.  A genuinely `E →L[ℝ] E`-typed
angle operator can be extracted with `complexify_realPartOperator`; it would have
the same singular values and hence the same value under every `N`.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan.Angle.Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The SELECTED-BRANCH `tan 2Θ` theorem over a real Hilbert space, for every
source unitarily-invariant norm, in arbitrary dimension.**

Not the unrestricted Section 2 theorem: `hVlow` and `hVperpHigh` place the
spectrum of `Λ₀` and `Λ₁`, which the source does not assume, and which is what
makes `IsQuarterAcute U V` available.  See the scope section of the module
docstring.

Real form of `tanTwoTheta_selectedBranch_symmetricNorming`.  `A` is self-adjoint with `U`
invariant and the ordered form gap `b` on `U` against `a` on `Uᗮ`; `H` is
self-adjoint and fully off-diagonal for `U`; `V` is invariant for `A + H` with
the same ordered gap.  Then the pair is quarter-acute and

`(b - a) * N.gauge (tan 2Θ) ≤ 2 * N.gauge H`

with the sharp constant, for every `N`.

The quarter-acuteness is genuinely concluded here, not assumed: it comes back
from the complex theorem through `isQuarterAcute_complexifySubmodule_iff`. -/
theorem tanTwoTheta_selectedBranch_symmetricNorming_real
    (N : SymmetricNormingFunction) (A H : E →L[ℝ] E) (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hAHV : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUlow : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hUperpHigh : ∀ x ∈ Uᗮ, ⟪A x, x⟫_ℝ ≤ a * ‖x‖ ^ 2)
    (hVlow : ∀ x ∈ V, b * ‖x‖ ^ 2 ≤ ⟪(A + H) x, x⟫_ℝ)
    (hVperpHigh : ∀ x ∈ Vᗮ, ⟪(A + H) x, x⟫_ℝ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hHmem : N.Mem H) :
    ∃ hquarter : IsQuarterAcute U V,
      N.Mem (directedTanTwoAngleOperatorRC U V hquarter) ∧
        (b - a) * N.gauge (directedTanTwoAngleOperatorRC U V hquarter) ≤ 2 * N.gauge H := by
  have hsum : complexify (A + H) = complexify A + complexify H := complexify_add A H
  obtain ⟨hqc, hmemc, hboundc⟩ :=
    tanTwoTheta_selectedBranch_symmetricNorming N (complexify A) (complexify H)
      (complexifySubmodule U) (complexifySubmodule V)
      ((complexify_isSelfAdjoint_iff A).2 hA)
      ((complexify_isSelfAdjoint_iff H).2 hH)
      (fun z hz => mapsTo_complexifySubmodule hAU hz)
      (fun z hz => by
        rw [← hsum]; exact mapsTo_complexifySubmodule hAHV hz)
      hab
      (fun z hz => le_re_inner_of_mem_complexifySubmodule hUlow hz)
      (fun z hz => by
        rw [← complexifySubmodule_orthogonal U] at hz
        exact re_inner_le_of_mem_complexifySubmodule hUperpHigh hz)
      (fun z hz => by
        rw [← hsum]; exact le_re_inner_of_mem_complexifySubmodule hVlow hz)
      (fun z hz => by
        rw [← complexifySubmodule_orthogonal V] at hz
        rw [← hsum]
        exact re_inner_le_of_mem_complexifySubmodule hVperpHigh hz)
      (fun z hz => mapsTo_orthogonal_complexifySubmodule U hHU hz)
      (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule U hHUperp hz)
      ((SymmetricNormingFunction.mem_complexify_iff N H).2 hHmem)
  refine ⟨(isQuarterAcute_complexifySubmodule_iff U V).1 hqc, hmemc, ?_⟩
  rwa [SymmetricNormingFunction.gauge_complexify] at hboundc

end DavisKahan
end TauCeti
