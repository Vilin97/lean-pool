/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaBranchFree
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.FormTransport
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.ComplexificationGauge

/-!
# The branch-free `tan 2Θ` theorem over a real Hilbert space, arbitrary dimension

`DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFreeInfinite.lean` proves
the unrestricted Section 2 `tan 2Θ` theorem with an arbitrary trial subspace
over `ℂ`; the restriction to complex scalars there is not mathematical, it is
that the existence of approximate leading singular families is proved through
the complex projection-valued measure.

This module supplies the real case by complexification.  No perturbation theory
is repeated: the whole configuration is complexified, the complex theorem is
applied verbatim, and the conclusion is transported back.  The transport is
**lossless** -- the form constants `a` and `b`, the sharp factor two, and every
source gauge value are preserved exactly.

Nothing here weakens the conclusion:

* no branch is selected or assumed;
* no uniform separation from the `π/4` pole is assumed;
* no finite-dimensionality of `U` or of `E`.

The only genuinely new transport steps beyond
`DavisKahan/SpectralTheory/Complexification/FormTransport.lean` are for the
graph coordinate: that `T` still lands in the complement and still kills it, and
that the *graph-invariance* relation `hinv` transports.  Both are coordinatewise,
because a complexified operator acts coordinatewise and a complexified subspace
is characterised by its two real coordinates.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open TauCeti.DavisKahan.ExactSinTheta

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

section Transport

variable {T : E →L[ℝ] E} {U : Submodule ℝ E} [U.HasOrthogonalProjection]

omit [CompleteSpace E] [U.HasOrthogonalProjection] in
/-- The complexified graph coordinate still takes every vector into the
orthogonal complement of the complexified trial subspace. -/
theorem complexify_mapsTo_orthogonal (hTmem : ∀ x, T x ∈ Uᗮ)
    (z : RealComplexification E) :
    complexify T z ∈ (complexifySubmodule U)ᗮ := by
  rw [← complexifySubmodule_orthogonal U, mem_complexifySubmodule]
  exact ⟨hTmem _, hTmem _⟩

omit [CompleteSpace E] [U.HasOrthogonalProjection] in
/-- The complexified graph coordinate still annihilates the orthogonal
complement of the complexified trial subspace. -/
theorem complexify_eq_zero_of_mem_orthogonal (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    {z : RealComplexification E} (hz : z ∈ (complexifySubmodule U)ᗮ) :
    complexify T z = 0 := by
  rw [← complexifySubmodule_orthogonal U, mem_complexifySubmodule] at hz
  refine RealComplexification.ext ?_ ?_
  · simpa using hTzero _ hz.1
  · simpa using hTzero _ hz.2

omit [CompleteSpace E] [U.HasOrthogonalProjection] in
/-- **The graph-invariance relation transports coordinatewise.**  This is the
one hypothesis of the branch-free theorem that is not covered by the generic
form-transport layer: the witness `y` is assembled from the witnesses for the
two real coordinates. -/
theorem complexify_graph_invariant {A H : E →L[ℝ] E}
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    {z : RealComplexification E} (hz : z ∈ complexifySubmodule U) :
    ∃ y ∈ complexifySubmodule U,
      (complexify A + complexify H) (z + complexify T z) =
        y + complexify T y := by
  rw [mem_complexifySubmodule] at hz
  obtain ⟨y₁, hy₁U, hy₁⟩ := hinv _ hz.1
  obtain ⟨y₂, hy₂U, hy₂⟩ := hinv _ hz.2
  refine ⟨RealComplexification.mk y₁ y₂, ?_, ?_⟩
  · rw [mem_complexifySubmodule]
    simpa using ⟨hy₁U, hy₂U⟩
  · rw [← complexify_add]
    refine RealComplexification.ext ?_ ?_
    · simpa using hy₁
    · simpa using hy₂

end Transport

/-- **Davis--Kahan 1970, the unrestricted Section 2 `tan 2Θ` theorem over a
REAL Hilbert space of arbitrary dimension, with an arbitrary trial subspace,
for every source unitarily invariant norm.**

`(b - a) · N(tan 2Θ) ≤ 2 · N(H)` with the sharp constant two, where `tan 2Θ` is
any operator whose approximation numbers are a rearrangement of the branch-free
double-angle tangents `2 tⱼ / |1 - tⱼ²|`.

Absent from the hypotheses, and this is the point:

* no `[FiniteDimensional ℝ U]` and no `[FiniteDimensional ℝ E]`;
* no bound on the graph coordinate, no `IsQuarterAcute`, and no spectral
  placement on the blocks of `A + H` -- the perturbed invariant subspace is an
  arbitrary invariant graph over `U` and may make angles arbitrarily close to
  `π/2` with it;
* no uniform separation from the `π/4` pole; that is derived from the ordered
  gap inside the proof.

`[U.HasOrthogonalProjection]` is the formal encoding of the paper's "closed
subspace". -/
theorem tanTwoTheta_branchFree_bounded_symmetricNorming_real
    (N : SymmetricNormingFunction)
    {A H T : E →L[ℝ] E} {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hUa : ∀ x ∈ Uᗮ, ⟪A x, x⟫_ℝ ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (tanTwoTheta : E →L[ℝ] E) (π : ℕ ≃ ℕ)
    (htan : ∀ n, approximationSingularValue (π n) tanTwoTheta =
      DavisKahan.TanTwoTheta.absDoubleAngleTangent (approximationSingularValue n T))
    (hHmem : N.Mem H) :
    N.Mem tanTwoTheta ∧
      (b - a) * N.gauge tanTwoTheta ≤ 2 * N.gauge H := by
  obtain ⟨hmemC, hboundC⟩ :=
    tanTwoTheta_branchFree_bounded_symmetricNorming_complex N
      (A := complexify A) (H := complexify H) (T := complexify T)
      (U := complexifySubmodule U)
      ((complexify_isSelfAdjoint_iff A).2 hA)
      ((complexify_isSelfAdjoint_iff H).2 hH)
      (fun z hz => mapsTo_complexifySubmodule hAU hz)
      (fun z hz => mapsTo_orthogonal_complexifySubmodule U hHU hz)
      (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule U hHUperp hz)
      (fun z => complexify_mapsTo_orthogonal hTmem z)
      (fun _ hz => complexify_eq_zero_of_mem_orthogonal hTzero hz)
      hab
      (fun z hz => le_re_inner_of_mem_complexifySubmodule hUb hz)
      (fun z hz => by
        rw [← complexifySubmodule_orthogonal U] at hz
        exact re_inner_le_of_mem_complexifySubmodule hUa hz)
      (fun _ hz => complexify_graph_invariant hinv hz)
      (complexify tanTwoTheta) π
      (fun n => by
        rw [ComplexificationApproximation.approximationSingularValue_complexify,
          ComplexificationApproximation.approximationSingularValue_complexify]
        exact htan n)
      ((SymmetricNormingFunction.mem_complexify_iff N H).2 hHmem)
  refine ⟨(SymmetricNormingFunction.mem_complexify_iff N tanTwoTheta).1 hmemC, ?_⟩
  rwa [SymmetricNormingFunction.gauge_complexify,
    SymmetricNormingFunction.gauge_complexify] at hboundC

end

end DavisKahan1970
end TauCeti
