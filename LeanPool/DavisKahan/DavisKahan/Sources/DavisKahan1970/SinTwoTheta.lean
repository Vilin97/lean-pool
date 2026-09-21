/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Reflection
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdealFormGap
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.AngleTransport
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.RealAngleIdentification
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.RealUnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TangentTransport
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SingularValueTransport
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Sin Two Theta -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Literal Davis--Kahan 1970 Section 7 sine-double-angle surface

Source anchor: Section 7, equations (7.1)--(7.5), the reflection proof of the
`sin 2Θ` theorem, together with the Section 2 statement `DK-sin2`.

The proof package reflects the perturbed system through the perturbed spectral
subspace `V`: with `J_V = 2P_V - 1`, conjugation fixes `B = A + H` and carries
`A` to a second operator whose distance from `A` is the mirror defect, at most
`2‖H‖` in every source norm.  The cross block between the exact subspace `U`
and the reflected image `J_V U` realizes `sin 2Θ`, and the single-angle sine
theorem applied across the mirror yields the double-angle estimate with the
sharp factor two.

This facade exposes:

* the mirror-defect identities of the proof package (equations (7.1)--(7.3));
* the identification of the reflected cross block with `sin 2Θ`
  (equations (7.4)--(7.5));
* the unbounded bounded-perturbation theorem at operator-norm and
  arbitrary unitary-invariant ideal-gauge scope, in both reflection-residual
  and perturbation forms;
* literal-source forms with the paper's freedom in the choice of the
  `sin 2Θ₀` representative: any operator with the prescribed complete
  singular-value sequence.

The theorems are stated for unbounded self-adjoint closed operators with
genuine spectral subspaces, the paper's most general single-operator setting;
bounded operators are the special case of a bounded closed operator.  The
separate bounded genuine-spectrum modules under
`Experimental/InfiniteDimensional` are not part of the maintained build and
are deliberately not referenced here.

Every declaration below is an alias of, or a thin wrapper around, a compiled
theorem; no new mathematics is introduced in this facade.
-/

namespace TauCeti
namespace DavisKahan1970


open DavisKahan.ExactSinTheta
open DavisKahan

/-! ## The mirror proof package, equations (7.1)--(7.3)

`reflectionDefect V A = J_V A J_V - A` is the mirror defect.  When `V` reduces
the perturbed operator `B`, the defect of the unperturbed operator equals the
reflected perturbation defect and is bounded by twice the perturbation in
every source norm. -/

/-- Equation (7.1): the mirror defect of the exact operator through the
perturbed subspace. -/
alias sinTwoTheta_mirrorDefect := DavisKahan.reflectionDefect

/-- Equation (7.2): when `V` reduces the perturbed operator, the mirror defect
of `A` is the reflected perturbation defect. -/
alias sinTwoTheta_mirrorDefect_eq_perturbationDefect :=
  DavisKahan.reflectionDefect_eq_perturbationDefect

/-- The mirror defect vanishes on reducing subspaces; this is the anchor of
the mirror construction. -/
alias sinTwoTheta_mirrorDefect_eq_zero_of_reduces :=
  DavisKahan.reflectionDefect_eq_zero_of_reduces

/-- Equation (7.3), operator-norm form: the mirror defect costs at most twice
the perturbation. -/
alias sinTwoTheta_mirrorDefect_le_two_mul :=
  DavisKahan.norm_reflectionDefect_le_two_mul

/-- Ideal-gauge form of equation (7.3): the reflected perturbation stays in
every rectangular symmetric ideal with gauge cost at most two. -/
alias sinTwoTheta_mirrorPerturbation_mem_and_gauge_le :=
  DavisKahan.reflectionPerturbation_mem_and_gauge_le

/-! ## Identification of the double angle, equations (7.4)--(7.5)

The cross block between the exact subspace `U` and the reflected image of its
complement realizes exactly the norm of `sin 2Θ(U, V)`.  This is the geometric
identity that converts the mirrored single-angle estimate into the
double-angle conclusion. -/

/-- Equations (7.4)--(7.5), ambient form: the reflected complementary overlap
block has exactly the norm of `sin 2Θ`. -/
alias sinTwoTheta_reflectedOverlap_norm :=
  DavisKahan.norm_starProjection_reflectedComplementary_eq_sinTwoAngle

/-- The canonical reflected overlap block whose complete singular-value data
realizes the source's `sin 2Θ₀` in the unbounded ideal theorem. -/
alias sinTwoThetaBlock :=
  DavisKahan.sinTwoThetaIdealBlock

/-- The canonical block has operator norm exactly `‖sin 2Θ‖`. -/
alias norm_sinTwoThetaBlock_complex :=
  DavisKahan.norm_sinTwoThetaIdealBlock_complex

/-- Equations (7.4)--(7.5) over a **real** Hilbert space: the canonical block
has operator norm exactly `‖sin 2Θ‖` of the real pair. -/
alias norm_sinTwoThetaBlock_real :=
  DavisKahan.norm_sinTwoThetaIdealBlock_real

/-! ## Unbounded forms

`A` is an unbounded self-adjoint closed operator, `H` a bounded self-adjoint
perturbation, and the subspaces are genuine spectral subspaces of `A` and of
`A + H` for prescribed measurable spectral sets.  The spectral separation is
the source interval/exterior hypothesis. -/

/-- **Davis--Kahan 1970, `sin 2Θ` theorem, unbounded perturbation form at
operator norm.** -/
alias sinTwoTheta_unbounded_perturbation_opNorm_complex :=
  DavisKahan.sinTwoTheta_addBounded_of_spectrum_gap

/-- Set-localized interval/exterior form of the unbounded operator-norm
theorem. -/
alias sinTwoTheta_unbounded_perturbation_intervalExterior_opNorm_complex :=
  DavisKahan.sinTwoTheta_addBounded_of_intervalExterior

/-- **Reflection-residual form** of the unbounded operator-norm theorem: the
bounded operator `R` implements the mirrored system on the full domain and
controls `sin 2Θ` with constant one. -/
alias sinTwoTheta_unbounded_reflectionResidual_opNorm_complex :=
  DavisKahan.sinTwoTheta_reflectionResidual_of_spectrum_gap

/-- **Davis--Kahan 1970, `sin 2Θ` theorem, unbounded perturbation form for
every source unitary-invariant ideal family.** -/
alias sinTwoTheta_unbounded_perturbation_blockRepresentative_idealFamily_complex :=
  DavisKahan.sinTwoTheta_addBounded_unitaryInvariant_of_spectrum_gap

/-- Set-localized interval/exterior form at unitary-invariant ideal scope. -/
alias sinTwoTheta_unbounded_perturbation_intervalExterior_blockRepresentative_idealFamily_complex :=
  DavisKahan.sinTwoTheta_addBounded_unitaryInvariant_of_intervalExterior

/-- Reflection-residual form at rectangular symmetric ideal-gauge scope. -/
alias sinTwoTheta_unbounded_reflectionResidual_blockRepresentative_symmetricIdealFamily_complex :=
  DavisKahan.sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap

/-! ## Literal source forms with the paper's `sin 2Θ₀` freedom

The paper does not fix a codomain realization of `sin 2Θ₀`; any operator with
the prescribed complete singular-value sequence is admissible.  The theorems
below transport the canonical conclusions along that freedom, exactly as the
literal Theorem 6.1 surface does for the single angle. -/

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open DavisKahan in
/-- **Davis--Kahan 1970, `sin 2Θ` theorem, literal unbounded perturbation
form.**  The chosen `sin 2Θ₀` may be any operator with the complete
singular-value sequence of the canonical reflected overlap block. -/
theorem sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hEmem : N.Mem E)
    (sinTwoTheta₀ : SinThetaRepresentative
      (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS))) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤
        2 * N.gauge E := by
  have hcanonical := sinTwoTheta_addBounded_gauge_of_spectrum_gap
    N.toSymmetricOperatorIdealFamily A hA E hE B S hB hS
      hβα hδ hBlow hBhigh hBcomplSpec hEmem
  obtain ⟨hmem, hgauge⟩ := sinTwoTheta₀.mem_and_gauge_eq N hcanonical.1
  refine ⟨hmem, ?_⟩
  rw [hgauge]
  exact hcanonical.2

/-! ### The Section 8 unequal-dimension extension

The closing sentence of Section 8 says that the `sin 2Θ` theorem extends to
`dim X(E₀) < dim X(F₀)`, similarly to Theorems 6.1 and 6.3.  In that strict
inequality regime the paper's ambient Hermitian angle `Θ`, whose construction
uses the matched-dimension condition (1.5), is not available.  Thus the
extension is necessarily the directed `Θ₀` conclusion, exactly as in Theorems
6.1 and 6.3; it does not ask for an ambient `Θ₀`-to-`Θ` conversion.

The maintained directed theorem above is stronger than the announced
extension: it has no dimension comparison at all.  The corollaries below keep
the strict rank hypothesis explicitly so the final Section 8 sentence has a
literal source-facing declaration over both scalar fields. -/

open DavisKahan in
/-- **Davis--Kahan 1970, Section 8 closing unequal-dimension extension of the
directed `sin 2Θ₀` theorem, perturbation form.**

The source explicitly announces the extension when
`dim X(E₀) < dim X(F₀)`.  The maintained Section 7 theorem is actually stronger:
it has no dimension comparison at all.  This corollary records the printed
strict-dimension case explicitly at the literal representative / arbitrary
unitarily-invariant-ideal scope, so the source sentence has a declaration whose
signature contains the hypothesis it states. -/
theorem sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_unequalDimension_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hEmem : N.Mem E)
    (_hStrictDimension :
      Module.rank ℂ (selfAdjointSpectralSubspace A hA B hB) <
        Module.rank ℂ (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS))
    (sinTwoTheta₀ : SinThetaRepresentative
      (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS))) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤ 2 * N.gauge E := by
  exact sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_complex N A hA E hE B S hB hS
    hβα hδ hBlow hBhigh hBcomplSpec hEmem sinTwoTheta₀

open DavisKahan in
/-- **Davis--Kahan 1970, `sin 2Θ` theorem, literal reflection-residual
form.**  The bounded operator `R` implements the mirrored system on the full
domain; the chosen `sin 2Θ₀` may be any operator with the complete
singular-value sequence of the canonical reflected overlap block, and it is
controlled by the residual with constant one. -/
theorem sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (R : H →L[ℂ] H) (hR : R.IsSymmetric)
    (B : Set ℝ) (hB : MeasurableSet B)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : H), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R)
    (sinTwoTheta₀ : SinThetaRepresentative
      (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V)) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤
        N.gauge R := by
  have hcanonical := sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap
    N.toSymmetricOperatorIdealFamily A hA R hR B hB V
      hβα hδ hBlow hBhigh hBcomplSpec hJdom hJintertwines hRmem
  obtain ⟨hmem, hgauge⟩ := sinTwoTheta₀.mem_and_gauge_eq N hcanonical.1
  refine ⟨hmem, ?_⟩
  rw [hgauge]
  exact hcanonical.2

open DavisKahan in
/-- **Section 8 closing unequal-dimension extension of the directed
`sin 2Θ₀` theorem, reflection-residual form.**  The strict dimension comparison
is recorded exactly as printed; the proof is a
direct specialization of the stronger dimension-free Section 7 theorem. -/
theorem sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_unequalDimension_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (R : H →L[ℂ] H) (hR : R.IsSymmetric)
    (B : Set ℝ) (hB : MeasurableSet B)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : H), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R)
    (_hStrictDimension :
      Module.rank ℂ (selfAdjointSpectralSubspace A hA B hB) < Module.rank ℂ V)
    (sinTwoTheta₀ : SinThetaRepresentative
      (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V)) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤ N.gauge R := by
  exact sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_complex N A hA R hR B hB V
    hβα hδ hBlow hBhigh hBcomplSpec hJdom hJintertwines hRmem sinTwoTheta₀

/-! ## Real-scalar forms

Standing assumption 1 of the source says the Hilbert space is "real or
complex".  The two theorems below are the real-scalar counterparts of the two
directed statements above, at the same unbounded scope and with the same
`sin 2Θ₀` representative freedom.  The gap is carried by the scalar-generic
form-bounded Sylvester predicate between the two real spectral restrictions,
which is the weaker of this tree's two spellings of spectral separation; the
`ℂ`-only resolvent-set spelling used above has no real counterpart, since
`TauCeti.LinearPMap.spectrum` is defined over `ℂ`.

The ambient (whole-space) half `δ ‖sin 2Θ‖ ≤ 2‖H‖` over the reals is
`TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_symmetricNorming_real`. -/

variable {Er : Type v}
  [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]

open DavisKahan DavisKahan.RealSpectralRestriction in
/-- **Davis--Kahan 1970, `sin 2Θ` theorem, literal unbounded perturbation form
over a REAL Hilbert space.**  The chosen `sin 2Θ₀` may be any operator with the
complete singular-value sequence of the canonical reflected overlap block. -/
theorem sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : Er →ₗ.[ℝ] Er)
    (hA : IsSelfAdjoint A)
    (Eop : Er →L[ℝ] Er) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop)
    (sinTwoTheta₀ : SinThetaRepresentative
      (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS))) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤ 2 * N.gauge Eop := by
  have hcanonical := sinTwoTheta_addBounded_gauge_real
    A hA Eop hEop N B S hB hS hδ hgap hEmem
  obtain ⟨hmem, hgauge⟩ := sinTwoTheta₀.mem_and_gauge_eq N hcanonical.1
  refine ⟨hmem, ?_⟩
  rw [hgauge]
  exact hcanonical.2

open DavisKahan DavisKahan.RealSpectralRestriction in
/-- **Real-scalar Section 8 closing unequal-dimension extension of the
directed `sin 2Θ₀` theorem, perturbation form.**  As over `ℂ`, the underlying theorem is
dimension-free; this declaration records the printed strict-dimension case. -/
theorem sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_unequalDimension_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : Er →ₗ.[ℝ] Er)
    (hA : IsSelfAdjoint A)
    (Eop : Er →L[ℝ] Er) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop)
    (_hStrictDimension :
      Module.rank ℝ (realSelfAdjointSpectralSubspace A hA B hB) <
        Module.rank ℝ (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS))
    (sinTwoTheta₀ : SinThetaRepresentative
      (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS))) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤ 2 * N.gauge Eop := by
  exact sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_real N A hA Eop hEop B S hB hS
    hδ hgap hEmem sinTwoTheta₀

open DavisKahan DavisKahan.RealSpectralRestriction in
/-- **Davis--Kahan 1970, `sin 2Θ` theorem, literal reflection-residual form
over a REAL Hilbert space.**  The bounded operator `R` implements the mirrored
system on the full domain; the chosen `sin 2Θ₀` may be any operator with the
complete singular-value sequence of the canonical reflected overlap block, and
it is controlled by the residual with constant one. -/
theorem sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : Er →ₗ.[ℝ] Er)
    (hA : IsSelfAdjoint A)
    (R : Er →L[ℝ] Er) (hR : R.IsSymmetric)
    (B : Set ℝ) (hB : MeasurableSet B)
    (V : Submodule ℝ Er) [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : Er) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : Er), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R)
    (sinTwoTheta₀ : SinThetaRepresentative
      (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB) V)) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤ N.gauge R := by
  have hcanonical := sinTwoTheta_reflectionResidual_gauge_real
    A hA B hB N R hR V hδ hgap hJdom hJintertwines hRmem
  obtain ⟨hmem, hgauge⟩ := sinTwoTheta₀.mem_and_gauge_eq N hcanonical.1
  refine ⟨hmem, ?_⟩
  rw [hgauge]
  exact hcanonical.2

open DavisKahan DavisKahan.RealSpectralRestriction in
/-- **Real-scalar Section 8 closing unequal-dimension extension of the
directed `sin 2Θ₀` theorem, reflection-residual form.** -/
theorem sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_unequalDimension_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : Er →ₗ.[ℝ] Er)
    (hA : IsSelfAdjoint A)
    (R : Er →L[ℝ] Er) (hR : R.IsSymmetric)
    (B : Set ℝ) (hB : MeasurableSet B)
    (V : Submodule ℝ Er) [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : Er) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : Er), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R)
    (_hStrictDimension :
      Module.rank ℝ (realSelfAdjointSpectralSubspace A hA B hB) < Module.rank ℝ V)
    (sinTwoTheta₀ : SinThetaRepresentative
      (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB) V)) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤ N.gauge R := by
  exact sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_real
    N A hA R hR B hB V hδ hgap hJdom hJintertwines hRmem sinTwoTheta₀

/-! ### The real directed forms at the paper's own unitarily invariant norm

`SymmetricNormingFunction` is the source's symmetric-gauge presentation, and it
is the class the real ambient half `sinTwoTheta_ambient_bounded_symmetricNorming_real` is
stated over.  Reading the real Ky-Fan-dominant theorems at each finite Ky Fan
family and closing with Fan dominance puts the real directed half at the same
class, so both printed conclusions of the Section 2 `sin 2Θ` theorem are now
available over `ℝ` for the same notion of "every unitarily invariant norm". -/

omit [CompleteSpace Er] in
private theorem kyFanApproximationGauge_zero_real {Fr : Type v}
    [NormedAddCommGroup Fr] [InnerProductSpace ℝ Fr]
    (T : Er →L[ℝ] Fr) : kyFanApproximationGauge 0 T = 0 := by
  simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]

open DavisKahan DavisKahan.RealSpectralRestriction in
/-- **Davis--Kahan 1970, directed `sin 2Θ` theorem over a REAL Hilbert space,
reflection-residual form, for every source unitarily invariant norm**:
`δ ‖sin 2Θ₀‖ ≤ ‖R‖`. -/
theorem sinTwoTheta_directed_unboundedReflectionResidual_blockRepresentative_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (A : Er →ₗ.[ℝ] Er)
    (hA : IsSelfAdjoint A)
    (R : Er →L[ℝ] Er) (hR : R.IsSymmetric)
    (B : Set ℝ) (hB : MeasurableSet B)
    (V : Submodule ℝ Er) [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : Er) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : Er), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB) V) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB) V) ≤ N.gauge R := by
  refine N.mul_gauge_le_of_all_mul_kyFan_le hδ hRmem fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [kyFanApproximationGauge_zero_real, kyFanApproximationGauge_zero_real,
      mul_zero]
  · have h := sinTwoTheta_reflectionResidual_gauge_real A hA B hB
      (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hk) R hR V hδ hgap
      hJdom hJintertwines (KyFanDominantIdealFamily.kyFan_mem k hk R)
    rw [KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at h
    exact h.2

open DavisKahan DavisKahan.RealSpectralRestriction in
/-- **Davis--Kahan 1970, directed `sin 2Θ` theorem over a REAL Hilbert space,
bounded-perturbation form, for every source unitarily invariant norm**:
`δ ‖sin 2Θ₀‖ ≤ 2‖E‖`, with the paper's sharp factor two. -/
theorem sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (A : Er →ₗ.[ℝ] Er)
    (hA : IsSelfAdjoint A)
    (Eop : Er →L[ℝ] Er) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop := by
  have hhalf : 0 < δ / 2 := by linarith
  have hmain := N.mul_gauge_le_of_all_mul_kyFan_le hhalf hEmem
    (A := sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) (fun k => ?_)
  · exact ⟨hmain.1, by linarith [hmain.2]⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [kyFanApproximationGauge_zero_real, kyFanApproximationGauge_zero_real,
        mul_zero]
    · have h := sinTwoTheta_addBounded_gauge_real A hA Eop hEop
        (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hk) B S hB hS hδ hgap
        (KyFanDominantIdealFamily.kyFan_mem k hk Eop)
      rw [KyFanDominantIdealFamily.kyFan_gauge,
        KyFanDominantIdealFamily.kyFan_gauge] at h
      linarith [h.2]

open DavisKahan DavisKahan.RealSpectralRestriction in
/-- **Davis--Kahan 1970, `sin 2Θ` over a REAL Hilbert space, bounded-perturbation
form, stated on the angle operator itself.**

`sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_symmetricNorming_real` concludes about
`sinTwoThetaIdealBlock`, the overlap of the selected spectral subspace with the
reflected complement, which is the proof's vehicle rather than the paper's
object.  `DavisKahan.gauge_directedSinTwoAngleOperatorRC` moves it to `2 sin Θ cos Θ`
for the real pair: the two have the same approximation singular values
(`DavisKahan.approximationSingularValue_sinTwoThetaIdealBlock_real`), so every
source unitarily invariant norm sees them identically.

The real mirror of `sinTwoTheta_directed_unbounded_addBounded_spectrumGap_symmetricNorming_complex`.  The angle
is the *directed* double-angle sine of the real pair, read in the canonical
complexification, which is where this development keeps the real double-angle
operators; the ambient spelling `sinTwoAngleOperatorR` is a different
operator, carrying each principal angle twice where the block carries it once,
and no transport to it is claimed. -/
theorem sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (A : Er →ₗ.[ℝ] Er)
    (hA : IsSelfAdjoint A)
    (Eop : Er →L[ℝ] Er) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahan.Angle.Real.directedSinTwoAngleOperatorRC
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.Real.directedSinTwoAngleOperatorRC
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop := by
  obtain ⟨hmem, hle⟩ := sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_symmetricNorming_real N A hA Eop hEop
    B S hB hS hδ hgap hEmem
  refine ⟨(DavisKahan.mem_directedSinTwoAngleOperatorRC_iff _ _ N).mpr hmem, ?_⟩
  rwa [DavisKahan.gauge_directedSinTwoAngleOperatorRC]

open DavisKahan DavisKahan.RealSpectralRestriction in
/-- **Davis--Kahan 1970, the Section 8 unequal-dimension `sin 2Θ` extension, over
`ℝ`.**

The real sibling of
`sinTwoTheta_directed_unbounded_addBounded_unequalDimension_symmetricNorming_complex`,
with the same unused strict-dimension hypothesis and the same conclusion for an
arbitrary operator carrying the directed double-angle sine's singular-value
sequence. -/
theorem sinTwoTheta_directed_unbounded_addBounded_unequalDimension_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (A : Er →ₗ.[ℝ] Er)
    (hA : IsSelfAdjoint A)
    (Eop : Er →L[ℝ] Er) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop)
    (_hStrictDimension :
      Module.rank ℝ (realSelfAdjointSpectralSubspace A hA B hB) <
        Module.rank ℝ (realSelfAdjointSpectralSubspace
          (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS))
    (sinTwoTheta₀ : SinThetaRepresentative
      (TauCeti.DavisKahan.Angle.Real.directedSinTwoAngleOperatorRC
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS))) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤ 2 * N.gauge Eop := by
  obtain ⟨hmem, hle⟩ :=
    sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_real
      N A hA Eop hEop B S hB hS hδ hgap hEmem
  have hext := N.gauge_eq_of_sameApproximationSingularValues
    sinTwoTheta₀.same_singular_values
  refine ⟨?_, ?_⟩
  · change N.extendedGauge sinTwoTheta₀.operator ≠ ⊤
    rw [hext]
    exact hmem
  · have hgauge : N.gauge sinTwoTheta₀.operator
        = N.gauge (TauCeti.DavisKahan.Angle.Real.directedSinTwoAngleOperatorRC
            (realSelfAdjointSpectralSubspace A hA B hB)
            (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
              (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) := by
      unfold SymmetricNormingFunction.gauge
      rw [hext]
    rw [hgauge]
    exact hle

/-! ### The real directed forms at the operator norm, naming the real angle

The two theorems above conclude about the canonical reflected overlap block.
Reading the real Ky-Fan-dominant statements at the first Ky Fan family and
renaming the block through `norm_sinTwoThetaBlock_real` gives the printed
operator-norm conclusions with `sin 2Θ` itself, over a real Hilbert space. -/

/-- **Davis--Kahan 1970, `sin 2Θ` theorem over a REAL Hilbert space, unbounded
bounded-perturbation form at the operator norm**: `δ ‖sin 2Θ‖ ≤ 2‖E‖`. -/
alias sinTwoTheta_unbounded_perturbation_opNorm_real :=
  DavisKahan.sinTwoTheta_addBounded_opNorm_real

/-- **Davis--Kahan 1970, `sin 2Θ` theorem over a REAL Hilbert space, unbounded
reflection-residual form at the operator norm**: `δ ‖sin 2Θ‖ ≤ ‖R‖`. -/
alias sinTwoTheta_unbounded_reflectionResidual_opNorm_real :=
  DavisKahan.sinTwoTheta_reflectionResidual_opNorm_real

/-! ### The complex source norm, completing the pair

`sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_symmetricNorming_real` above states the bounded-perturbation
`sin 2Θ` theorem for a `SymmetricNormingFunction` over a real Hilbert space.
The complex counterpart was missing, even though the complex ideal-level theorem
`DavisKahan.sinTwoTheta_addBounded_unitaryInvariant_of_spectrum_gap` has been
available: only the adaptation from a Ky-Fan-dominant family to the source norm
was absent.

The two are not literal mirror images, and the difference is real rather than
cosmetic.  The real track reaches the ideal layer through
`FormBoundedSylvesterGap`; the complex track reaches it through the spectrum
gap -- semiboundedness of the selected spectral restriction together with the
complementary restriction's spectrum avoiding the open enlargement.  This
statement takes the hypotheses the complex proof actually has. -/

section ComplexPaperNorm

variable {Hc : Type v}
  [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]

open DavisKahan in
/-- **Davis--Kahan 1970, `sin 2Θ`, bounded perturbation of an unbounded
self-adjoint operator, in a source unitarily invariant norm, over `ℂ`.**

`δ · N(sin 2Θ block) ≤ 2 N(E)` for the spectral subspaces selected by `B` from
`A` and by `S` from `A + E`, under the spectrum gap: the restriction of `A` to
`B` is semibounded between `β` and `α`, and the restriction to `Bᶜ` has spectrum
avoiding `(β − δ, α + δ)`.

The complex counterpart of `sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_symmetricNorming_real`. -/
theorem sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_spectrumGap_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : Hc →ₗ.[ℂ] Hc) (hA : IsSelfAdjoint A)
    (Eop : Hc →L[ℂ] Hc) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hEmem : N.Mem Eop) :
    N.Mem (DavisKahan.sinTwoThetaIdealBlock
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (DavisKahan.sinTwoThetaIdealBlock
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop := by
  have hhalf : 0 < δ / 2 := by linarith
  have hmain := N.mul_gauge_le_of_all_mul_kyFan_le hhalf hEmem
    (A := DavisKahan.sinTwoThetaIdealBlock
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) (fun k => ?_)
  · exact ⟨hmain.1, by linarith [hmain.2]⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
    · have h := DavisKahan.sinTwoTheta_addBounded_unitaryInvariant_of_spectrum_gap
        (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hk) A hA Eop hEop B S hB hS
        hβα hδ hBlow hBhigh hBcomplSpec
        (KyFanDominantIdealFamily.kyFan_mem k hk Eop)
      rw [KyFanDominantIdealFamily.kyFan_gauge,
        KyFanDominantIdealFamily.kyFan_gauge] at h
      linarith [h.2]

open DavisKahan in
/-- **Davis--Kahan 1970, `sin 2Θ` for a bounded perturbation of an unbounded
self-adjoint operator, stated on the angle operator itself.**

`sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_spectrumGap_symmetricNorming_complex` above concludes about
`sinTwoThetaIdealBlock`, the overlap of the selected spectral subspace with the
reflected complement.  That block is the proof's vehicle, not the paper's object.
`DavisKahan.sinTwoThetaIdealBlock_hasSameApproximationNumbers` shows the two have
the same approximation numbers -- because
`directedSinAngleOperatorC U (reflectedU U V) = directedSinTwoAngleOperatorC U V` exactly,
as operators -- so every source unitarily invariant norm sees them identically,
and this statement is the same theorem read on `2 sin Θ cos Θ`.

Note that this is the *directed* double-angle operator.  The paper's ambient
spelling `sinTwoAngleOperatorC U V` is
`|R_V P_U R_V − P_U|` (`directedSinTwoAngleOperatorC_eq_modulus_reflect`), a
different operator: it agrees in operator norm
(`norm_sinTwoAngleOperatorC_eq_norm_directedSinTwoAngleOperatorC`) but its
approximation-number sequence is not identified with this one here, so the
transport below is not claimed for it. -/
theorem sinTwoTheta_directed_unbounded_addBounded_spectrumGap_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : Hc →ₗ.[ℂ] Hc) (hA : IsSelfAdjoint A)
    (Eop : Hc →L[ℂ] Hc) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop := by
  obtain ⟨hmem, hle⟩ := sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_spectrumGap_symmetricNorming_complex N A hA Eop hEop B S hB hS
    hβα hδ hBlow hBhigh hBcomplSpec hEmem
  refine ⟨(DavisKahan.mem_directedSinTwoAngleOperatorC_iff _ _ N).mpr hmem, ?_⟩
  rwa [DavisKahan.gauge_directedSinTwoAngleOperatorC]

/-! ### The complex source norm at the full source gap

The two statements above take the hypotheses the spectrum-gap proof has: a
*bounded* separating interval `[β, α]`, its exterior avoided by the
complementary restriction's spectrum.  Davis and Kahan allow the separating
interval to be half-infinite, so those two are a specialization of the printed
`sin 2Θ` theorem, not the theorem itself.

The two below are the printed scope over `ℂ`.  They take the same
`FormBoundedSylvesterGap` as the real endpoints, and so cover all three of the
source's separation configurations.  They are proved through
`DavisKahan.sinTwoTheta_addBounded_gauge_of_formGap`, which reaches the
single-angle estimate through `sinTheta_unbounded_complex` -- the complex
form-gap sine theorem -- rather than through the centre/radius engine the
spectrum-gap route uses.

The spectrum-gap statements are kept, and are *not* derived from these.  Their
hypothesis is not known to imply this one: `FormBoundedSylvesterGap.intervalExterior`
wants `LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α`, and the tree proves only the
converse direction (`DavisKahan.semiboundedBelow_of_spectrum_subset_Ici` and its
`Iic` partner).  The missing bridge is the `LinearPMap` analogue of
`DavisKahan.Foundation.realSpectrum_subset_Ici_of_le_re_inner_generic`, which
exists for bounded operators only. -/

open DavisKahan in
/-- **Davis--Kahan 1970, `sin 2Θ`, bounded perturbation of an unbounded
self-adjoint operator, in a source unitarily invariant norm, over `ℂ`, at the
full source gap.**

`δ · N(sin 2Θ block) ≤ 2 N(E)` for the spectral subspaces selected by `B` from
`A` and by `S` from `A + E`, under the form-bounded Sylvester gap between the
restriction of `A` to `B` and its restriction to `Bᶜ`.  The separating interval
may be half-infinite, which is the scope Davis and Kahan state.

The complex counterpart of
`sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_symmetricNorming_real`. -/
theorem sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : Hc →ₗ.[ℂ] Hc) (hA : IsSelfAdjoint A)
    (Eop : Hc →L[ℂ] Hc) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB)
      (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (DavisKahan.sinTwoThetaIdealBlock
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (DavisKahan.sinTwoThetaIdealBlock
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop := by
  have hhalf : 0 < δ / 2 := by linarith
  have hmain := N.mul_gauge_le_of_all_mul_kyFan_le hhalf hEmem
    (A := DavisKahan.sinTwoThetaIdealBlock
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) (fun k => ?_)
  · exact ⟨hmain.1, by linarith [hmain.2]⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
    · have h := DavisKahan.sinTwoTheta_addBounded_gauge_of_formGap
        (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hk) A hA Eop hEop B S hB hS
        hδ hgap (KyFanDominantIdealFamily.kyFan_mem k hk Eop)
      rw [KyFanDominantIdealFamily.kyFan_gauge,
        KyFanDominantIdealFamily.kyFan_gauge] at h
      linarith [h.2]

open DavisKahan in
/-- **Davis--Kahan 1970, `sin 2Θ` for a bounded perturbation of an unbounded
self-adjoint operator, stated on the angle operator itself, at the full source
gap.**

The block-representative statement above read on `2 sin Θ cos Θ`.
`DavisKahan.sinTwoThetaIdealBlock_hasSameApproximationNumbers` gives the two the
same approximation numbers, so every source unitarily invariant norm sees them
identically.

This is the *directed* double-angle operator; the paper's ambient spelling
`sinTwoAngleOperatorC U V` is a different operator, agreeing in operator
norm but with no approximation-number identification claimed here. -/
theorem sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : Hc →ₗ.[ℂ] Hc) (hA : IsSelfAdjoint A)
    (Eop : Hc →L[ℂ] Hc) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB)
      (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop := by
  obtain ⟨hmem, hle⟩ :=
    sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_symmetricNorming_complex
      N A hA Eop hEop B S hB hS hδ hgap hEmem
  refine ⟨(DavisKahan.mem_directedSinTwoAngleOperatorC_iff _ _ N).mpr hmem, ?_⟩
  rwa [DavisKahan.gauge_directedSinTwoAngleOperatorC]

/-! ### The Section 8 unequal-dimension extension, at this result's certified scope

The closing sentence of Section 8 states that the `sin 2Θ` theorem extends to
`dim X(E₀) < dim X(F₀)`, analogously to Theorems 6.1 and 6.3.  The repository
states it at the scope the counted Section 2 result is certified at: an
arbitrary `SymmetricNormingFunction` and the whole `FormBoundedSylvesterGap`.

`sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_unequalDimension_complex`
earlier in this file states the same extension, but only at a
`KyFanDominantIdealFamily` and the bounded-interval spectrum gap.

**This is a `result_adjacent_extension`, not an obligation of the counted
result.**  Davis and Kahan state the extension "analogously to Theorems 6.1
and 6.3" without proving it as a result of its own, so under the repository's
completion criterion it does not enlarge `S2-sin-two-theta`.  The declarations
below are stronger coverage held as supporting evidence, which is worth having
and is not something the certificate depends on.

The strict-dimension hypothesis is carried and **not used**, exactly as in that
earlier declaration: the underlying theorem imposes no comparison of dimensions
at all, so the extension is a restriction of a theorem already proved without it.
Carrying it makes the source sentence checkable against a Lean statement that
displays its hypothesis. -/

open DavisKahan in
/-- **Davis--Kahan 1970, the Section 8 unequal-dimension `sin 2Θ` extension, over
`ℂ`, at an arbitrary source unitarily invariant norm and the full source gap.**

`δ N(sin 2Θ₀) ≤ 2 N(E)` for any operator carrying the directed double-angle
sine's singular-value sequence, when the selected spectral subspace of `A` has
strictly smaller dimension than the selected spectral subspace of `A + E`. -/
theorem sinTwoTheta_directed_unbounded_addBounded_unequalDimension_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : Hc →ₗ.[ℂ] Hc) (hA : IsSelfAdjoint A)
    (Eop : Hc →L[ℂ] Hc) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB)
      (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop)
    (_hStrictDimension :
      Module.rank ℂ (DavisKahan.selfAdjointSpectralSubspace A hA B hB) <
        Module.rank ℂ (DavisKahan.selfAdjointSpectralSubspace
          (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS))
    (sinTwoTheta₀ : SinThetaRepresentative
      (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS))) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤ 2 * N.gauge Eop := by
  obtain ⟨hmem, hle⟩ :=
    sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex
      N A hA Eop hEop B S hB hS hδ hgap hEmem
  have hext := N.gauge_eq_of_sameApproximationSingularValues
    sinTwoTheta₀.same_singular_values
  refine ⟨?_, ?_⟩
  · change N.extendedGauge sinTwoTheta₀.operator ≠ ⊤
    rw [hext]; exact hmem
  · have hgauge : N.gauge sinTwoTheta₀.operator
        = N.gauge (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC
            (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
            (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
              (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) := by
      unfold SymmetricNormingFunction.gauge
      rw [hext]
    rw [hgauge]
    exact hle

end ComplexPaperNorm

end DavisKahan1970
end TauCeti
