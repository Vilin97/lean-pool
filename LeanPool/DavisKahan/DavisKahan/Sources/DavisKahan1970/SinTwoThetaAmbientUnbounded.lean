/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Proposition61
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoTheta
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.AmbientReal
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ReflectionRestriction
import LeanPool.DavisKahan.DavisKahan.TanTheta.RitzPair
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.DoubleAngleFunctionalCalculus
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleGeneric
import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-! # Sin Two Theta Ambient Unbounded -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The ambient `sin 2Θ` conclusion at the source's unbounded scope

The Section 2 `sin 2Θ` theorem has two printed conclusions,

`δ ‖sin 2Θ₀‖ ≤ 2‖R‖`  and  `δ ‖sin 2Θ‖ ≤ 2‖H‖`,

the first directed and the second *ambient*.  The directed conclusion is proved
for an unbounded self-adjoint operator, a bounded self-adjoint perturbation and
an arbitrary `SymmetricNormingFunction` in
`DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean`.  The ambient conclusion was
available only for **bounded** ambient operators
(`sinTwoTheta_ambient_bounded_symmetricNorming_complex` and its real sibling), which is
a specialization of the printed theorem and not the printed theorem.  This module
proves the ambient conclusion at the same scope as the directed one.

## The route, and why it needs no new analysis

`directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub` says the ambient
`sin 2Θ` between `U` and `V` is the modulus of `P_{J U} − P_U`, where `J` is the
reflection through `V`.  So the ambient double angle between `U` and `V` *is* an
ambient single angle between `U` and its mirror image, and the theorem to apply
is Proposition 6.1 rather than a second double-angle argument.

Over `ℂ` the bounded proof does exactly this, with the bounded symmetric sine
theorem.  Its unbounded counterpart now exists — Proposition 6.1 on a common
dense domain, `proposition6_1_commonDomain_projectorDifference` — and the
reflected operator is `J A J`, which shares `dom A` because `J` preserves it.
The paper's bounded perturbation for the reflected pair is
`D = H − J H J`, whose gauge is at most `2 N(H)`: that is where the printed
factor `2` comes from, and it is the *only* place a constant enters.

What was missing was not analysis but transport.  Three facts had to cross the
reflection, and all three are now theorems rather than remarks:

* `TauCeti.LinearPMap.reducesSubspace_unitaryConj` — the mirror of a reducing
  subspace reduces the conjugated operator;
* `TauCeti.LinearPMap.reducingRestriction_unitaryConj` — the reducing
  restriction of the conjugate *is* the conjugate of the reducing restriction,
  as an equality of partial maps;
* `FormBoundedSylvesterGap.unitaryConj_left` / `.unitaryConj_right` — the source
  separation is invariant under unitary conjugation **in every constructor**,
  so the half-infinite configurations survive the reflection unchanged.

The bridge that makes them applicable is
`addBounded_reflectionPerturbation_eq_unitaryConj`: the two facts a reflection
argument establishes about `A + (H − J H J)` say exactly that it *equals*
`J A J` as a partial map.

## Main results

* `sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex`;
* `sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_real`.

Both take an unbounded self-adjoint `A`, a bounded self-adjoint `H`, arbitrary
measurable spectral selections, the full `FormBoundedSylvesterGap` — half-infinite
separating intervals included — and an arbitrary `SymmetricNormingFunction`, and
conclude ideal membership together with `δ N(sin 2Θ) ≤ 2 N(H)` on the genuine
ambient angle operator.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Section 2, third unnumbered
  theorem, second conclusion; Section 7, equation (7.5); the Appendix to
  Section 6 for the common-domain relaxation.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

noncomputable section

universe u v

/-- A subspace admitting an orthogonal projection inside a complete ambient space
is itself complete.  `local instance` does not propagate through imports, so it is
reinstalled here; every reducing restriction below lives in such a coordinate
space, and all three scalar sections need it, so its binders are written out
rather than taken from a `variable` block. -/
local instance instCompleteSpaceCoeAmbientUnbounded
    {𝕜 : Type u} [RCLike 𝕜]
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-! ## The reflected pair, scalar-generically -/

section Generic

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **The ambient sine estimate for a pair related by a unitary conjugation.**

`B` is the conjugate `W A W⁻¹` and `D` is the bounded operator representing
`B − A` on the common domain.  The conclusion is the paper's whole-space sine
between `U` and its image `W U`, read as the projector difference — the one
spelling available over both scalar fields.

The single separation hypothesis is the source's: a form-bounded gap between the
two reducing restrictions of the *unperturbed* operator.  Both of Proposition
6.1's crossed gaps are obtained from it by conjugating one block, which is why no
second separation assumption appears. -/
theorem sinTheta_ambient_unitaryConj_projectorDifference_symmetricNorming
    (N : SymmetricNormingFunction)
    {A B : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hUred : TauCeti.LinearPMap.ReducesSubspace A U)
    (W : H ≃ₗᵢ[𝕜] H)
    (hBeq : B = TauCeti.LinearPMap.unitaryConj W A)
    (D : H →L[𝕜] H)
    (hdomain : A.domain = B.domain)
    (hperturbation : ∀ (x : H) (hxA : x ∈ A.domain) (hxB : x ∈ B.domain),
      B ⟨x, hxB⟩ - A ⟨x, hxA⟩ = D x)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ)
    (hDmem : N.Mem D) :
    N.Mem ((U.map (W.toLinearEquiv : H →ₗ[𝕜] H)).starProjection - U.starProjection) ∧
      δ * N.gauge ((U.map (W.toLinearEquiv : H →ₗ[𝕜] H)).starProjection -
        U.starProjection) ≤ N.gauge D := by
  subst hBeq
  have hUrred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.unitaryConj W A)
      (U.map (W.toLinearEquiv : H →ₗ[𝕜] H)) :=
    TauCeti.LinearPMap.reducesSubspace_unitaryConj W A U hUred
  have hperp : (U.map (W.toLinearEquiv : H →ₗ[𝕜] H))ᗮ =
      Uᗮ.map (W.toLinearEquiv : H →ₗ[𝕜] H) :=
    (Submodule.map_orthogonal_equiv U W).symm
  -- the first crossed gap: conjugate the complementary block
  have hgapUV : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.unitaryConj W A)
        (U.map (W.toLinearEquiv : H →ₗ[𝕜] H))ᗮ hUrred.orthogonal) δ := by
    refine FormBoundedSylvesterGap.reducingRestriction_congr_right hperp.symm
      (TauCeti.LinearPMap.reducesSubspace_unitaryConj W A Uᗮ hUred.orthogonal)
      hUrred.orthogonal ?_
    rw [TauCeti.LinearPMap.reducingRestriction_unitaryConj W A Uᗮ hUred.orthogonal]
    exact hgap.unitaryConj_right (TauCeti.LinearPMap.submoduleMapIsometry W Uᗮ)
  -- the second crossed gap: conjugate the selected block
  have hgapVU : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.unitaryConj W A)
        (U.map (W.toLinearEquiv : H →ₗ[𝕜] H)) hUrred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ := by
    rw [TauCeti.LinearPMap.reducingRestriction_unitaryConj W A U hUred]
    exact hgap.unitaryConj_left (TauCeti.LinearPMap.submoduleMapIsometry W U)
  exact proposition6_1_commonDomain_projectorDifference N hA hB hUred hUrred
    D hdomain hperturbation hδ hgapUV hgapVU hDmem

/-- **The reflected perturbation costs at most a factor two in every source
norm.**

`D = H − J H J` with `J` unitary, so each Ky Fan gauge of `D` is at most twice
that of `H`; Fan dominance turns that into the same statement for an arbitrary
`SymmetricNormingFunction`.  This is where the printed constant `2` enters the
ambient conclusion, and it is the only constant in the proof. -/
theorem reflectionPerturbation_normingMem_and_gauge_le
    (N : SymmetricNormingFunction)
    (V : Submodule 𝕜 H) [V.HasOrthogonalProjection]
    (Eop : H →L[𝕜] H) (hEmem : N.Mem Eop) :
    N.Mem (DavisKahan.reflectionPerturbation V Eop) ∧
      N.gauge (DavisKahan.reflectionPerturbation V Eop) ≤ 2 * N.gauge Eop := by
  have htwo : ‖((2 : ℝ) : 𝕜)‖ = 2 := by
    rw [RCLike.norm_ofReal]; norm_num
  have hMem2 : N.Mem (((2 : ℝ) : 𝕜) • Eop) := by
    intro htop
    rw [N.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hEmem h
    · exact absurd h (by simp)
  have hkyFan : ∀ k : ℕ,
      (1 : ℝ) * kyFanApproximationGauge k (DavisKahan.reflectionPerturbation V Eop) ≤
        kyFanApproximationGauge k (((2 : ℝ) : 𝕜) • Eop) := by
    intro k
    rw [one_mul, kyFanApproximationGauge_smul, htwo]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
    · have h := DavisKahan.reflectionPerturbation_mem_and_gauge_le
        (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk).toSymmetricOperatorIdealFamily
        V Eop (KyFanDominantIdealFamily.kyFan_mem k hk Eop)
      rw [FanDominantIdealFamily.toSymmetric_gaugeReal,
        FanDominantIdealFamily.toSymmetric_gaugeReal,
        KyFanDominantIdealFamily.kyFan_gauge,
        KyFanDominantIdealFamily.kyFan_gauge] at h
      exact h.2
  obtain ⟨hmem, hle⟩ := N.mul_gauge_le_of_all_mul_kyFan_le one_pos hMem2 hkyFan
  refine ⟨hmem, ?_⟩
  rw [one_mul, N.gauge_smul _ hEmem, htwo] at hle
  exact hle

/-- The reflected pair produced by a bounded perturbation, in the form the source
theorems consume: `A` and `A + (H − J H J)`, with `J` the reflection through the
perturbed spectral subspace.

The two hypotheses are exactly what the spectral development supplies over each
field — `J` preserves `dom A`, and `(A + (H − J H J)) J = J A` there. -/
theorem sinTwoTheta_ambient_reflection_projectorDifference_symmetricNorming
    (N : SymmetricNormingFunction)
    {A : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A)
    (Eop : H →L[𝕜] H) (hEop : Eop.IsSymmetric)
    {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hmem : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hint : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A (DavisKahan.reflectionPerturbation V Eop))
          ⟨V.reflectionOperator (x : H), hmem x⟩ =
        V.reflectionOperator (A x))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ)
    (hEmem : N.Mem Eop) :
    N.Mem ((U.map (V.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection -
        U.starProjection) ∧
      δ * N.gauge ((U.map (V.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection -
        U.starProjection) ≤ 2 * N.gauge Eop := by
  set D : H →L[𝕜] H := DavisKahan.reflectionPerturbation V Eop with hD
  have hDsa : D.IsSymmetric :=
    DavisKahan.reflectionPerturbation_isSelfAdjoint V Eop hEop
  have hDideal := reflectionPerturbation_normingMem_and_gauge_le N V Eop hEmem
  have hBeq : TauCeti.LinearPMap.addBounded A D =
      TauCeti.LinearPMap.unitaryConj V.reflection A :=
    DavisKahan.addBounded_reflectionPerturbation_eq_unitaryConj V Eop hmem hint
  have hBsa : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A D) :=
    DavisKahan.addBounded_isSelfAdjoint A hA D hDsa
  obtain ⟨hmemD, hleD⟩ :=
    sinTheta_ambient_unitaryConj_projectorDifference_symmetricNorming N hA hBsa hUred
      V.reflection hBeq D rfl
      (by
        intro x hxA hxB
        change A ⟨x, hxB⟩ + D x - A ⟨x, hxA⟩ = D x
        have hxx : (⟨x, hxB⟩ : A.domain) = ⟨x, hxA⟩ := rfl
        rw [hxx, add_sub_cancel_left])
      hδ hgap hDideal.1
  exact ⟨hmemD, hleD.trans hDideal.2⟩

/-- **Davis--Kahan 1970, the ambient conclusion of the `sin 2Θ` theorem, at an arbitrary
`RCLike` field.**

`δ N(sin 2Θ) ≤ 2 N(H)` on the paper's ambient double-angle sine
`TauCeti.DavisKahan.Angle.sinTwoAngleOperator`, for an unbounded self-adjoint ambient operator
`A`, a bounded self-adjoint perturbation `Eop`, arbitrary Hilbert dimension, an arbitrary
`SymmetricNormingFunction`, and the full `FormBoundedSylvesterGap` -- so the separating
interval may be half-infinite.  Membership in the norm ideal is concluded, not assumed, and
the constant is exactly `2`.

The scalar field is arbitrary and the statement mentions no capability class: the real
functional calculus that names `sin 2Θ` is an instance at every `RCLike` field
(`ForTauCeti/Analysis/RCLike/ScalarTransportFunctionalCalculus.lean`).

The conclusion is on the mathematical angle operator, not on a proof representative.  What
converts the one into the other is `sinTwoAngleOperator_eq_modulus_starProjection_sub`, the
paper's own reflection identity: `sin 2Θ(U, V) = |P_{J_V U} - P_U|`, and a modulus does not
change approximation numbers, so no source norm can tell the two apart.

`sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex` and its real sibling are
the specializations in which `U` and `V` are the spectral subspaces the paper names; the
spectral selection is field-specific (the spectral measure is built over `ℂ` and descended to
`ℝ`), which is why the hypotheses here are the reducing-subspace and intertwining conditions
that the spectral development supplies over each field. -/
theorem sinTwoTheta_ambient_unbounded_reflectionPair_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    {A : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A)
    (Eop : H →L[𝕜] H) (hEop : Eop.IsSymmetric)
    {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hmem : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hint : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A (DavisKahan.reflectionPerturbation V Eop))
          ⟨V.reflectionOperator (x : H), hmem x⟩ =
        V.reflectionOperator (A x))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator U V) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator U V) ≤ 2 * N.gauge Eop := by
  obtain ⟨hmemX, hleX⟩ :=
    sinTwoTheta_ambient_reflection_projectorDifference_symmetricNorming N hA Eop hEop hUred
      hmem hint hδ hgap hEmem
  obtain ⟨hiff, hgauge⟩ :=
    SameApproximationSingularSequence.normingMem_iff_and_gauge_eq N
      (A := TauCeti.DavisKahan.Angle.sinTwoAngleOperator U V)
      (B := (U.map (V.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection - U.starProjection)
      (TauCeti.DavisKahan.Angle.sinTwoAngleOperator_hasSameApproximationNumbers U V)
  exact ⟨hiff.mpr hmemX, by rw [hgauge]; exact hleX⟩

/-! ## The printed hypothesis: an arbitrary reducing subspace of the perturbed operator

Printed Section 2 puts no spectral condition on the ambient subspaces: `P` reduces `A`
and `Q` reduces `A + H`, and that is all.  The endpoint above takes the reduction of
`A + H` in reflection form -- `V.reflectionOperator` preserves `dom A` and conjugates
`A` into `A + reflectionPerturbation V Eop` -- because that is the shape its proof
consumes.  The two are the same hypothesis: `ReflectionIntertwines.ofReducesSubspace`
turns "`V` reduces `A + Eop`" into the reflection form, and
`addBounded_reflectionPerturbation_intertwines_of_commutes` turns the commutation into
the intertwining equation.

The declaration below is therefore the printed statement with the printed hypothesis,
and it is what the Section 2 ambient clause is registered on. -/

section ReducingAmbient

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Davis--Kahan 1970, the ambient conclusion of the `sin 2Θ` theorem, at an arbitrary
reducing pair.**

`δ N(sin 2Θ(U, V)) ≤ 2 N(H)` where `U` is an arbitrary subspace reducing the unbounded
self-adjoint `A`, `V` is an arbitrary subspace reducing the perturbed operator `A + H`,
`H` is a bounded self-adjoint perturbation, the Hilbert dimension is arbitrary, the
separation is the whole `FormBoundedSylvesterGap` between the two blocks of `A`, and `N`
is an arbitrary source unitarily invariant norm.  Membership of `sin 2Θ` in the norm's
ideal is concluded, not assumed, and the constant is exactly `2`.

Neither subspace is required to be a spectral subspace.  That is the printed scope: the
Section 2 statement says only that the two subspaces reduce their operators, and the
spectral selection appears in the source as the way a reader *produces* such a pair, not
as a hypothesis of the theorem. -/
theorem sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    {A : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A)
    (Eop : H →L[𝕜] H) (hEop : Eop.IsSymmetric)
    {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hVred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Eop) V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator U V) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator U V) ≤
        2 * N.gauge Eop :=
  let hV := DavisKahan.ReflectionIntertwines.ofReducesSubspace hVred
  sinTwoTheta_ambient_unbounded_reflectionPair_symmetricNorming_rclike N hA Eop hEop hUred
    hV.mapsDomain
    (DavisKahan.addBounded_reflectionPerturbation_intertwines_of_commutes Eop V
      hV.mapsDomain hV.commutes)
    hδ hgap hEmem

/-- The complex fixed-field form of
`sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_rclike`. -/
theorem sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (N : SymmetricNormingFunction)
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Eop : Hc →L[ℂ] Hc) (hEop : Eop.IsSymmetric)
    {U V : Submodule ℂ Hc} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hVred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Eop) V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator U V) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator U V) ≤
        2 * N.gauge Eop :=
  sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_rclike N hA Eop hEop hUred hVred
    hδ hgap hEmem

/-! ### The printed operator roles

The source's Section 2 setup fixes which operator each hypothesis is about.  `P`
reduces the *unperturbed* `A`, with blocks `A₀, A₁`; `Q` reduces the *perturbed*
`A + H`, with blocks `Λ₀, Λ₁` (equations (1.2) and (1.3)).  The `sin 2Θ` theorem's
gap is on the perturbed blocks:

  spec(Λ₀) ⊆ [β, α],   spec(Λ₁) ∩ (β − δ, α + δ) = ∅.

The theorems above take the gap on the blocks of the *unperturbed* operator, which
is the other reading.  They are correct and reusable -- the ambient estimate is
symmetric in the pair, so neither reading is stronger -- but only one of them is
the printed hypothesis, and the source-facing name belongs to that one.

The bridge is a role reversal, and it is exact rather than approximate.  Applying
the theorem above to the data

  unperturbed := A + H,   perturbation := −H,   first subspace := Q,   second := P

makes its gap hypothesis the printed one, because the blocks of `A + H` on `Q` are
`Λ₀, Λ₁`; its perturbed operator is `(A + H) + (−H) = A`, which `P` reduces on the
nose by `addBounded_neg_cancel`; its conclusion bounds `sin 2Θ(Q, P) = sin 2Θ(P, Q)`
by `sinTwoAngleOperator_comm`; and its right-hand side is `2 N(−H) = 2 N(H)` by
`gauge_neg`. -/

/-- **Davis--Kahan 1970, Section 2, the ambient `sin 2Θ` theorem at the printed
operator roles.**

`P` reduces the unperturbed `A`; `Q` reduces the perturbed `A + H`; and the
spectral gap is between the two blocks of `A + H` relative to `Q` -- the source's
`Λ₀, Λ₁`, not the unperturbed `A₀, A₁`.  Unbounded self-adjoint `A`, bounded
self-adjoint perturbation, arbitrary `SymmetricNormingFunction`. -/
theorem sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    {A : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A)
    (Hop : H →L[𝕜] H) (hHop : Hop.IsSymmetric)
    {P Q : Submodule 𝕜 H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ)
    (hHmem : N.Mem Hop) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
        2 * N.gauge Hop := by
  -- The perturbed operator of the reversed problem is `A` itself, on the nose.
  have hcancel : TauCeti.LinearPMap.addBounded
      (TauCeti.LinearPMap.addBounded A Hop) (-Hop) = A :=
    TauCeti.LinearPMap.addBounded_neg_cancel A Hop
  have hAH : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    DavisKahan.addBounded_isSelfAdjoint A hA Hop hHop
  have hnegHop : (-Hop).IsSymmetric := by
    intro x y
    simpa using congrArg Neg.neg (hHop x y)
  have hPred' : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.addBounded A Hop) (-Hop)) P := by
    rw [hcancel]; exact hPred
  have hmemneg : N.Mem (-Hop) := SymmetricNormingFunction.mem_neg N |>.mpr hHmem
  obtain ⟨hmem, hle⟩ :=
    sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_rclike N hAH (-Hop) hnegHop
      hQred hPred' hδ hgap hmemneg
  rw [TauCeti.DavisKahan.Angle.sinTwoAngleOperator_comm] at hmem hle
  rw [SymmetricNormingFunction.gauge_neg] at hle
  exact ⟨hmem, hle⟩

/-- **Davis--Kahan 1970, Section 2, ambient `sin 2Theta` at the where-defined
unitarily invariant norm boundary, scalar-generic over `RCLike`.**

The analytic estimate is the scalar-generic symmetric-norming theorem above.  This
production wrapper uses the weaker normalized symmetric operator-ideal family selected by
source review and asserts the numerical inequality only when both displayed norms exist.
The factor two is handled by applying Fan dominance to the equivalent `δ / 2` estimate. -/
theorem sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike
    
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {A : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A)
    (Hop : H →L[𝕜] H) (hHop : Hop.IsSymmetric)
    {P Q : Submodule 𝕜 H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) →
    N.Mem Hop →
      δ * N.gaugeReal (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
        2 * N.gaugeReal Hop := by
  intro hAngle hHopMem
  have hhalf : N.ScaledGaugeLEWhereDefined (δ / 2)
      (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) Hop := by
    apply N.scaledGaugeLEWhereDefined_of_all_mul_kyFan_le
      (div_pos hδ (by norm_num : (0 : ℝ) < 2))
    intro k
    by_cases hk0 : k = 0
    · subst k
      simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge_zero_index]
    · have hk : 0 < k := Nat.pos_of_ne_zero hk0
      have hmain :=
        sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_rclike
          (𝕜 := 𝕜) (kyFanNormingFunction k hk) hA Hop hHop
          hPred hQred hδ hgap (kyFanNormingFunction_mem k hk Hop)
      have hky :
          δ * kyFanApproximationGauge k
              (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
            2 * kyFanApproximationGauge k Hop := by
        simpa only [kyFanNormingFunction_gauge] using hmain.2
      nlinarith
  have hle := hhalf hAngle hHopMem
  nlinarith

/-- The complex fixed-field form of
`sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_rclike`. -/
theorem sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (N : SymmetricNormingFunction)
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ)
    (hHmem : N.Mem Hop) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
        2 * N.gauge Hop :=
  sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_rclike N hA Hop hHop
    hPred hQred hδ hgap hHmem

/-- The real fixed-field form of
`sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_rclike`. -/
theorem sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    (N : SymmetricNormingFunction)
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Eop : Er →L[ℝ] Er) (hEop : Eop.IsSymmetric)
    {U V : Submodule ℝ Er} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hVred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Eop) V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator U V) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator U V) ≤
        2 * N.gauge Eop :=
  sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_rclike N hA Eop hEop hUred hVred
    hδ hgap hEmem

/-- The real fixed-field form of
`sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_rclike`: the gap is
on the blocks of the perturbed operator, as printed. -/
theorem sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    (N : SymmetricNormingFunction)
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ)
    (hHmem : N.Mem Hop) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
        2 * N.gauge Hop :=
  sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_rclike N hA Hop hHop
    hPred hQred hδ hgap hHmem

/-! ### Where-defined fixed-field wrappers

These declarations are convenience specializations of the scalar-generic production
boundary above.  Source fidelity is attested by the result ledger; neither theorem name
acts as a certificate. -/

/-- Complex specialization of
`sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike`. -/
theorem sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    [TopologicalSpace.SeparableSpace Hc]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) →
    N.Mem Hop →
      δ * N.gaugeReal (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
        2 * N.gaugeReal Hop :=
  sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike
    (𝕜 := ℂ) N hA Hop hHop hPred hQred hδ hgap

/-- Real specialization of
`sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike`. -/
theorem sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    [TopologicalSpace.SeparableSpace Er]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) →
    N.Mem Hop →
      δ * N.gaugeReal (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
        2 * N.gaugeReal Hop :=
  sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike
    (𝕜 := ℝ) N hA Hop hHop hPred hQred hδ hgap

/-! ### Stronger normalized-UIN fixed-field wrappers

The two declarations below retain the older membership-transfer API over
`NormalizedUnitaryInvariantNorm`.  They are useful stronger specializations, but the result
ledger now selects the where-defined `NormalizedSymmetricOperatorIdealFamily` boundary above.

Only the ambient space carries separability, which is all the source assumes. -/

/-- **Complex normalized-UIN specialization of the ambient `sin 2Θ` theorem.**

Separable ambient Hilbert space, normalized unitarily invariant norm, unbounded
self-adjoint `A`, bounded self-adjoint perturbation, and -- as Section 2 states
it -- the spectral gap between the two blocks of the *perturbed* operator
`A + H` relative to `Q`. -/
theorem sinTwoTheta_ambient_unbounded_perturbedGap_normalizedUIN_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ)
    (hHmem : N.Mem Hop) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
        2 * N.gauge Hop :=
  normalizedUnitaryInvariant_of_symmetricNorming_mul N hδ two_pos hHmem fun M hM =>
    sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_complex M hA Hop hHop
      hPred hQred hδ hgap hM

/-- **Real normalized-UIN specialization of the ambient `sin 2Θ` theorem.** -/
theorem sinTwoTheta_ambient_unbounded_perturbedGap_normalizedUIN_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ)
    (hHmem : N.Mem Hop) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
        2 * N.gauge Hop :=
  normalizedUnitaryInvariant_of_symmetricNorming_mul N hδ two_pos hHmem fun M hM =>
    sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_real M hA Hop hHop
      hPred hQred hδ hgap hM

end ReducingAmbient

end Generic

/-! ## The source theorem over `ℂ` -/

section Complex

variable {Hc : Type v}
  [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]

open DavisKahan in
/-- **Davis--Kahan 1970, the ambient conclusion of the `sin 2Θ` theorem, over
`ℂ`, at the source's unbounded scope and for every source unitarily invariant
norm.**

`δ N(sin 2Θ) ≤ 2 N(H)` on the paper's ambient double-angle sine
`sinTwoAngleOperatorC`, where `A` is an unbounded self-adjoint operator, `H`
a bounded self-adjoint perturbation, and the two subspaces are the genuine
spectral subspaces selected by `B` from `A` and by `S` from `A + H`.  The
separation is the full `FormBoundedSylvesterGap`, so the separating interval may
be half-infinite.

This is the printed second conclusion of the Section 2 `sin 2Θ` theorem;
`sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex` is the first.
`sinTwoTheta_ambient_bounded_symmetricNorming_complex` is this statement's bounded
specialization, kept as an alternative proof. -/
theorem sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : Hc →ₗ.[ℂ] Hc) (hA : IsSelfAdjoint A)
    (Eop : Hc →L[ℂ] Hc) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB)
      (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop := by
  have hUred := DavisKahan.selfAdjointSpectralSubspace_reducing A hA B hB
  have hcompl : DavisKahan.selfAdjointSpectralSubspace A hA Bᶜ hB.compl =
      (DavisKahan.selfAdjointSpectralSubspace A hA B hB)ᗮ :=
    DavisKahan.selfAdjointSpectralSubspace_compl_eq_orthogonal A hA B hB
  -- the source gap, read on reducing restrictions
  have hgap' : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB) hUred)
      (TauCeti.LinearPMap.reducingRestriction A
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)ᗮ hUred.orthogonal) δ := by
    rw [DavisKahan.selfAdjointSpectralRestriction_eq_reducingRestriction A hA B hB,
      DavisKahan.selfAdjointSpectralRestriction_eq_reducingRestriction A hA Bᶜ
        hB.compl] at hgap
    exact FormBoundedSylvesterGap.reducingRestriction_congr_right hcompl
      (DavisKahan.selfAdjointSpectralSubspace_reducing A hA Bᶜ hB.compl)
      hUred.orthogonal hgap
  obtain ⟨hmem, hle⟩ :=
    sinTwoTheta_ambient_reflection_projectorDifference_symmetricNorming
      (𝕜 := ℂ) (H := Hc) N hA Eop hEop
      (U := DavisKahan.selfAdjointSpectralSubspace A hA B hB)
      (V := DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
        (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)
      hUred
      (DavisKahan.perturbedSpectralReflection_mem_domain A hA Eop hEop S hS)
      (DavisKahan.add_reflectionPerturbation_intertwines A hA Eop hEop S hS)
      hδ hgap' hEmem
  set X : Hc →L[ℂ] Hc :=
    ((DavisKahan.selfAdjointSpectralSubspace A hA B hB).map
          ((DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
            (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S
            hS).reflection.toLinearEquiv : Hc →ₗ[ℂ] Hc)).starProjection -
      (DavisKahan.selfAdjointSpectralSubspace A hA B hB).starProjection with hX
  obtain ⟨hiff, hgauge⟩ :=
    SameApproximationSingularSequence.normingMem_iff_and_gauge_eq N
      (A := X.modulus) (B := X)
      (ContinuousLinearMap.modulus_hasSameApproximationNumbers X)
  rw [TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub]
  exact ⟨hiff.mpr hmem, by rw [hgauge]; exact hle⟩

end Complex

/-! ## The source theorem over `ℝ` -/

section Real

variable {Er : Type v}
  [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]

open DavisKahan TauCeti.RealComplexification
  TauCeti.DavisKahan.Foundation.RealComplexification in
/-- The real ambient double-angle sine and the projector difference between `U`
and its mirror image through `V` have the same complete singular data.

Both complexify to the two complex spellings of the same quantity: the left to
`sinTwoAngleOperatorC`, which is the *modulus* of the reflected projector
difference, and the right to that difference itself.  A modulus does not change
approximation numbers, so no source norm can tell them apart. -/
theorem sameSingular_sinTwoAngleOperatorR_reflectedProjectorDifference
    (U V : Submodule ℝ Er)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularSequence
      (complexify (TauCeti.DavisKahan.Angle.sinTwoAngleOperatorR U V))
      (complexify ((U.map (V.reflection.toLinearEquiv : Er →ₗ[ℝ] Er)).starProjection -
        U.starProjection)) := by
  have hleft : complexify (TauCeti.DavisKahan.Angle.sinTwoAngleOperatorR U V) =
      (((complexifySubmodule U).map
            ((complexifySubmodule V).reflection.toLinearEquiv :
              RealComplexification Er →ₗ[ℂ] RealComplexification Er)).starProjection -
          (complexifySubmodule U).starProjection).modulus := by
    rw [TauCeti.DavisKahan.Angle.complexify_sinTwoAngleOperatorR U V,
      TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub]
  have hright : complexify
        ((U.map (V.reflection.toLinearEquiv : Er →ₗ[ℝ] Er)).starProjection -
          U.starProjection) =
      ((complexifySubmodule U).map
          ((complexifySubmodule V).reflection.toLinearEquiv :
            RealComplexification Er →ₗ[ℂ] RealComplexification Er)).starProjection -
        (complexifySubmodule U).starProjection := by
    have hconj : ∀ T : Er →L[ℝ] Er,
        DavisKahan.boundedUnitaryConjugate V.reflection T =
          V.reflectionOperator ∘L T ∘L V.reflectionOperator :=
      fun _ => ContinuousLinearMap.ext fun _ => rfl
    have hconjC : ∀ T : RealComplexification Er →L[ℂ] RealComplexification Er,
        DavisKahan.boundedUnitaryConjugate (complexifySubmodule V).reflection T =
          (complexifySubmodule V).reflectionOperator ∘L T ∘L
            (complexifySubmodule V).reflectionOperator :=
      fun _ => ContinuousLinearMap.ext fun _ => rfl
    rw [DavisKahan.starProjection_map_unitary U V.reflection,
      DavisKahan.starProjection_map_unitary (complexifySubmodule U)
        (complexifySubmodule V).reflection,
      complexify_sub, hconj U.starProjection,
      hconjC (complexifySubmodule U).starProjection,
      complexify_comp, complexify_comp, complexify_reflectionOperator,
      starProjection_complexifySubmodule]
  rw [hleft, hright]
  exact ContinuousLinearMap.modulus_hasSameApproximationNumbers _

open DavisKahan DavisKahan.RealSpectralRestriction
  TauCeti.RealComplexification
  TauCeti.DavisKahan.Foundation.RealComplexification in
/-- **Davis--Kahan 1970, the ambient conclusion of the `sin 2Θ` theorem, over
`ℝ`, at the source's unbounded scope and for every source unitarily invariant
norm.**

The real sibling of
`sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex`, at exactly the
same strength: unbounded self-adjoint `A`, bounded self-adjoint `H`, arbitrary
real Hilbert dimension, genuine real spectral subspaces, the full
`FormBoundedSylvesterGap` including its half-infinite configurations, an
arbitrary `SymmetricNormingFunction`, and the exact factor `2`.

This stronger fixed-field theorem remains a useful API and implementation witness.
The result ledger now selects the scalar-generic where-defined UIN endpoint for the
ambient source clause.  The analytic content here is the scalar-generic reflected-pair
theorem at `ℝ`, not a complexification of the complex endpoint; complexification
enters only to name the real ambient angle operator, since `sinTwoAngleOperatorR` is
defined as the real part of the complex one. -/
theorem sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (A : Er →ₗ.[ℝ] Er) (hA : IsSelfAdjoint A)
    (Eop : Er →L[ℝ] Er) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperatorR
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperatorR
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop := by
  have hUred := realSelfAdjointSpectralSubspace_reducing A hA B hB
  have hcompl : realSelfAdjointSpectralSubspace A hA Bᶜ hB.compl =
      (realSelfAdjointSpectralSubspace A hA B hB)ᗮ :=
    realSelfAdjointSpectralSubspace_compl A hA B hB
  have hgap' : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A
        (realSelfAdjointSpectralSubspace A hA B hB) hUred)
      (TauCeti.LinearPMap.reducingRestriction A
        (realSelfAdjointSpectralSubspace A hA B hB)ᗮ hUred.orthogonal) δ :=
    FormBoundedSylvesterGap.reducingRestriction_congr_right hcompl
      (realSelfAdjointSpectralSubspace_reducing A hA Bᶜ hB.compl)
      hUred.orthogonal hgap
  obtain ⟨hmem, hle⟩ :=
    sinTwoTheta_ambient_reflection_projectorDifference_symmetricNorming
      (𝕜 := ℝ) (H := Er) N hA Eop hEop
      (U := realSelfAdjointSpectralSubspace A hA B hB)
      (V := realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
        (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)
      hUred
      (realPerturbedSpectralReflection_mem_domain A hA Eop hEop S hS)
      (real_add_reflectionPerturbation_intertwines A hA Eop hEop S hS)
      hδ hgap' hEmem
  obtain ⟨hiff, hgauge⟩ :=
    SameApproximationSingularSequence.normingMem_iff_and_gauge_eq N
      (sameSingular_sinTwoAngleOperatorR_reflectedProjectorDifference
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS))
  rw [SymmetricNormingFunction.mem_complexify_iff,
    SymmetricNormingFunction.mem_complexify_iff] at hiff
  rw [SymmetricNormingFunction.gauge_complexify,
    SymmetricNormingFunction.gauge_complexify] at hgauge
  exact ⟨hiff.mpr hmem, by rw [hgauge]; exact hle⟩

end Real

end

end DavisKahan1970
end TauCeti
