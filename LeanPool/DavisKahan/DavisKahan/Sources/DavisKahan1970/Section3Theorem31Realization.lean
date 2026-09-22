/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/

import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.Realization
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.UnitaryEquivalence
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus
import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.SpectralMultiplicityEquiv
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Real.SpectralMultiplicityClassification

/-! # Section3Theorem31Realization -/

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

/-!
# Davis--Kahan 1970, Theorem 3.1, the realization half

The classification half of Theorem 3.1 -- `twoProjection_operator_classification`
in `Section3Classification.lean` -- says that the angle datum determines the
pair.  The paper's sentence (ii) is the converse of the *existence* kind: every
admissible angle datum is attained.  This module states that sentence, in two
shapes: from a packaged `HalmosAngleDatum`, and from the printed data -- two
Hermitian operators `Θ₀`, `Θ₁` confined to `[0, π/2]` and an intertwining
partial isometry `J`.

The construction is owned upstream by `Geometry/Halmos/Realization.lean`; every
statement here is grounded on it by `:=`, so there is a single source of truth
and no geometry is redone.

Everything is `RCLike`-generic, so the real case is an instantiation rather than a second
theorem; it is recorded at the end as an `example` that checks the real specialization.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan

universe u v w

section Realization

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Davis--Kahan 1970, Theorem 3.1, the realization half — the paper's sentence
(ii).**

The classification half (`twoProjection_operator_classification`, and
`TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_complex` in the paper's
multiplicity phrasing) says that the angle datum determines the pair.  This says the converse of the *existence* kind: every
admissible angle datum is *attained*.  Given `cos Θ₀, sin Θ₀` on `E`,
`cos Θ₁, sin Θ₁` on `F` and the intertwiner `J₀` that matches their spectral
multiplicities away from the angle `0`, the two subspaces

`U = E`-factor,  `V = W₀ E` with `W₀ x = (cos Θ₀ x, J₀ sin Θ₀ x)`

of `E ⊕₂ F` satisfy, in order:

1. the compression of `P_V` to `U` is `cos² Θ₀`;
2. the compression of `P_Vᗮ` to `Uᗮ` is `cos² Θ₁`;
3. `U ⊓ V` is the angle-`0` eigenspace on the `P`-side;
4. `Uᗮ ⊓ Vᗮ` is the angle-`0` eigenspace on the `Pᗮ`-side;
5. `U ⊓ Vᗮ` is the angle-`π/2` eigenspace on the `P`-side;
6. `Uᗮ ⊓ V` is the angle-`π/2` eigenspace on the `Pᗮ`-side;
7. the two crossed defects are isometric.

Items 3--7 are the mathematical content of the theorem's hypothesis: the
`π/2` multiplicities are *forced* to agree, because `J₀` restricts to a linear
isometric equivalence between them, while the `0` multiplicities are the two
kernels of `sin Θ₀` and `sin Θ₁`, which `J₀` never sees.  That the latter are
genuinely unconstrained is witnessed by
`theorem3_1_realization_zeroAngle_unconstrained`.

Grounded by `:=` on `Geometry/Halmos/Realization.lean`, so there is a single
source of truth.  The block matrix behind item 1 and item 2 is
`starProjection_targetSubspace_apply`, which reproduces equation (3.7) of the
source, both off-diagonal entries positive. -/
theorem theorem3_1_realization (d : HalmosAngleDatum 𝕜 E F) :
    (∀ x : E, (sourceSubspace 𝕜 E F).starProjection
        (d.targetSubspace.starProjection (modelInl 𝕜 E F x)) =
          modelInl 𝕜 E F (d.cos₀ (d.cos₀ x))) ∧
      (∀ y : F, (sourceSubspace 𝕜 E F)ᗮ.starProjection
        ((d.targetSubspace)ᗮ.starProjection (modelInr 𝕜 E F y)) =
          modelInr 𝕜 E F (d.cos₁ (d.cos₁ y))) ∧
      halmosCommonPart (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.sin₀ : E →ₗ[𝕜] E)) ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.sin₁ : F →ₗ[𝕜] F)) ∧
      halmosSourceDefect (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.cos₀ : E →ₗ[𝕜] E)) ∧
      halmosTargetDefect (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.cos₁ : F →ₗ[𝕜] F)) ∧
      Nonempty (↥(halmosSourceDefect (sourceSubspace 𝕜 E F) d.targetSubspace) ≃ₗᵢ[𝕜]
        ↥(halmosTargetDefect (sourceSubspace 𝕜 E F) d.targetSubspace)) :=
  ⟨d.compress_source_eq, d.compress_sourceOrthogonal_eq, d.halmosCommonPart_eq,
    d.halmosExteriorPart_eq, d.halmosSourceDefect_eq, d.halmosTargetDefect_eq,
    d.nonempty_halmosSourceDefect_equiv_targetDefect⟩
section OfAngles


/-- **Davis--Kahan 1970, Theorem 3.1, sentence (ii), in the printed shape: stated
from the angle operators rather than from a packaged datum.**

`theorem3_1_realization` consumes a `HalmosAngleDatum`, which carries
`cos Θ₀, sin Θ₀, cos Θ₁, sin Θ₁` and the intertwiner as five independent fields.
The paper does not.  It says "given such `Θⱼ` acting on spaces `Hⱼ`", where
"such" refers to the theorem's own sentence "these are arbitrary Hermitian
operators satisfying the following conditions: `0 ≤ Θⱼ ≤ π/2`; ... and the
spectral multiplicity functions of the `Θⱼ` are the same except for a possible
difference in the multiplicity of `{0}`", and then extracts from that last
condition "some isometry `J₀` of `closure (ran Θ₀)` onto `closure (ran Θ₁)` such
that `J₀ Θ₀ J₀⁻¹` agrees on its domain with `Θ₁`".  So the printed data are two
Hermitian operators and one intertwining partial isometry — and that is this
statement's hypothesis list.  The datum is built inside the proof by
`HalmosAngleDatum.ofIntertwinedAngles`, and each
`cos Θⱼ`, `sin Θⱼ` in the conclusion is the continuous functional calculus of
`Θⱼ` rather than an opaque field, so the seven conjuncts of
`theorem3_1_realization` are read here directly off `Θ₀`, `Θ₁` and `J`.

**The two partial-isometry hypotheses are the paper's, not an artifact.**
`hisom` and `hcoisom` say that `J` is isometric on `ran sin Θ₀` and co-isometric
onto `ran sin Θ₁`; that is the content of the printed `J₀`, and it is a
multiplicity statement, invisible to a functional calculus of one operator at a
time.  Everything else the datum needs is derived.

**On the spectral confinement.**  `_hspec₀` and `_hspec₁` are the printed
`0 ≤ Θⱼ ≤ π/2`.  They are taken as hypotheses here and are deliberately unused in
the proof, hence the underscores.  They belong here rather than on the
constructor: `HalmosAngleDatum` records no nonnegativity, and none of the ten
fields `ofIntertwinedAngles` derives needs one — `cos² + sin² = 1` and
`J f(Θ₀) = f(Θ₁) J` hold over all of `ℝ` — so assuming confinement there would
narrow the constructor for nothing.  What confinement buys is that the statement
*reads* as the printed sentence: on `[0, π/2]` one has `sin t = 0 ↔ t = 0` and
`cos t = 0 ↔ t = π/2`, so conjuncts 3--4 exhibit the two angle-`0` spaces and
conjuncts 5--6 the two angle-`π/2` spaces, which is what Davis and Kahan mean by
calling the `Θⱼ` angle operators.  Dropping the two hypotheses would leave the
same theorem with the same proof and a weaker reading; keeping them costs
nothing, so they are kept.

`RCLike`-generic.  The real case is therefore an instantiation and not a second
theorem: `theorem3_1_realization_ofAngles_real`. -/
theorem theorem3_1_realization_ofAngles
    {Θ₀ : E →L[𝕜] E} {Θ₁ : F →L[𝕜] F}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (_hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (_hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (J : E →L[𝕜] F) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
    (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
    (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁) :
    (∀ x : E, (sourceSubspace 𝕜 E F).starProjection
        ((HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace.starProjection (modelInl 𝕜 E F x)) =
          modelInl 𝕜 E F (cfc Real.cos Θ₀ (cfc Real.cos Θ₀ x))) ∧
      (∀ y : F, (sourceSubspace 𝕜 E F)ᗮ.starProjection
        (((HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace)ᗮ.starProjection (modelInr 𝕜 E F y)) =
          modelInr 𝕜 E F (cfc Real.cos Θ₁ (cfc Real.cos Θ₁ y))) ∧
      halmosCommonPart (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.sin Θ₀ : E →L[𝕜] E) : E →ₗ[𝕜] E)) ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.sin Θ₁ : F →L[𝕜] F) : F →ₗ[𝕜] F)) ∧
      halmosSourceDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.cos Θ₀ : E →L[𝕜] E) : E →ₗ[𝕜] E)) ∧
      halmosTargetDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.cos Θ₁ : F →L[𝕜] F) : F →ₗ[𝕜] F)) ∧
      Nonempty (↥(halmosSourceDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace) ≃ₗᵢ[𝕜]
        ↥(halmosTargetDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace)) :=
  theorem3_1_realization (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom)

end OfAngles
/-- **The multiplicity at angle `0` is genuinely unconstrained.**

The all-`0` datum over an arbitrary pair `(E, F)` of Hilbert spaces
realizes `U = V`, whose angle-`0` spaces are the whole of `E` on the `P`-side and
the whole of `F` on the `Pᗮ`-side.  `E` and `F` are unrelated, so no admissibility
condition at angle `0` can be imposed — in contrast to the angle `π/2`, where
item 7 of `theorem3_1_realization` forces the two multiplicities to agree.
Together the two statements are why Davis and Kahan's hypothesis is asymmetric
between `0` and `π/2`. -/
theorem theorem3_1_realization_zeroAngle_unconstrained
    (𝕜 : Type*) [RCLike 𝕜]
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (F : Type v) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    halmosCommonPart (sourceSubspace 𝕜 E F) (trivialHalmosAngleDatum 𝕜 E F).targetSubspace =
        sourceSubspace 𝕜 E F ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F)
          (trivialHalmosAngleDatum 𝕜 E F).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F)) ⊤ :=
  ⟨trivial_halmosCommonPart_eq 𝕜 E F, trivial_halmosExteriorPart_eq 𝕜 E F⟩
end Realization

/-! ## Theorem 3.1, sentence (ii), over a real Hilbert space

`theorem3_1_realization_ofAngles` is `RCLike`-generic, so its real form is an
instantiation rather than a separate theorem.  The example below checks that the local
operator functional calculus supplies the two real angle calculi in unrestricted dimension.
Two of the seven conjuncts are read off below: the
angle-`π/2` space on the `P`-side, and the isometry between the two crossed
defects that forces the two `π/2` multiplicities to agree. -/

section RealScalars

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [CompleteSpace H₂]

example {Θ₀ : H₁ →L[ℝ] H₁} {Θ₁ : H₂ →L[ℝ] H₂}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (J : H₁ →L[ℝ] H₂) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
    (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
    (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁) :
    halmosSourceDefect (sourceSubspace ℝ H₁ H₂)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
      Submodule.map (modelInl ℝ H₁ H₂ : H₁ →ₗ[ℝ] WithLp 2 (H₁ × H₂))
        (LinearMap.ker ((cfc Real.cos Θ₀ : H₁ →L[ℝ] H₁) : H₁ →ₗ[ℝ] H₁)) ∧
    Nonempty (↥(halmosSourceDefect (sourceSubspace ℝ H₁ H₂)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
          hcoisom).targetSubspace) ≃ₗᵢ[ℝ]
      ↥(halmosTargetDefect (sourceSubspace ℝ H₁ H₂)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
          hcoisom).targetSubspace)) :=
  ⟨(theorem3_1_realization_ofAngles hΘ₀ hΘ₁ hspec₀ hspec₁ J hJ hisom hcoisom).2.2.2.2.1,
    (theorem3_1_realization_ofAngles hΘ₀ hΘ₁ hspec₀ hspec₁ J hJ hisom hcoisom).2.2.2.2.2.2⟩
end RealScalars

/-! ## The intertwiner is reconstructed from the multiplicity data, not assumed

The printed converse of Theorem 3.1 gives arbitrary Hermitian `Θ₀, Θ₁` with `0 ≤ Θⱼ ≤ π/2`
whose spectral multiplicity functions agree, and then says: "the proof reconstructs the pair
from these angle data **and the corresponding partial isometry `J₀`**".  `J₀` is therefore
output of the proof, not input to the theorem.

`theorem3_1_realization_ofAngles` asks its caller for `J` and its two partial-isometry
identities.  Those are consequences of the multiplicity hypothesis; taking them as hypotheses
makes the Lean statement weaker than the printed one, which is a source-correspondence defect
even though every instance of it is true.  The theorem below closes that gap in the case where
the multiplicity functions agree everywhere -- the printed hypothesis allows them to differ at
the spectral point `0`, and that residual freedom is recorded below.  Over `ℂ` the
classification `TauCeti.operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex` supplies the
unitary directly. -/

section OfMultiplicity

variable {E₂ : Type u} [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [CompleteSpace E₂]
variable {F₂ : Type v} [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]

/-- **Davis--Kahan 1970, Theorem 3.1: the printed partial isometry `J₀`, constructed.**

From equality of the spectral multiplicity data of two self-adjoint operators, the intertwining
partial isometry the printed converse names is produced, together with the two identities
`theorem3_1_realization_ofAngles` asks for.  Nothing about `J` is hypothesised.

The two spectral confinements `0 ≤ Θⱼ ≤ π/2` are carried because they are printed, and are not
consumed: the construction is a fact about multiplicity data at any spectrum.

**Recorded narrowing.**  The printed hypothesis is that the multiplicity functions agree
*except possibly at `0`*.  `SameSpectralMultiplicity` is agreement everywhere, so this covers
the equal-null-space case.  The freedom at `0` is realized separately, and unconditionally, by
`corollary3_1_realization_zeroMultiplicity` in the compact setting; closing it here needs the
multiplicity comparison restricted to the closures of the ranges, which is not written. -/
theorem theorem3_1_intertwiner_of_sameSpectralMultiplicity_complex
    {Θ₀ : E₂ →L[ℂ] E₂} {Θ₁ : F₂ →L[ℂ] F₂}
    (_hΘ₀ : IsSelfAdjoint Θ₀) (_hΘ₁ : IsSelfAdjoint Θ₁)
    (_hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (_hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (hmult : TauCeti.SameSpectralMultiplicity Θ₀ Θ₁) :
    ∃ J : E₂ →L[ℂ] F₂, J ∘L Θ₀ = Θ₁ ∘L J ∧
      ContinuousLinearMap.adjoint J ∘L J = 1 ∧
      J ∘L ContinuousLinearMap.adjoint J = 1 := by
  obtain ⟨e, he⟩ := TauCeti.operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex Θ₀ Θ₁ hmult
  refine ⟨(e : E₂ →L[ℂ] F₂), ContinuousLinearMap.ext fun x => he x, ?_, ?_⟩
  · exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp e.norm_map
  · rw [e.adjoint_eq_symm]
    exact ContinuousLinearMap.ext fun y => by simp


attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal

/-- **Davis--Kahan 1970, Theorem 3.1, converse sentence, from the printed angle data alone.**

Two arbitrary self-adjoint operators with `0 ≤ Θⱼ ≤ π/2` and equal spectral multiplicity data,
and nothing else.  The intertwining partial isometry `J₀` the printed proof reconstructs is
produced here rather than demanded of the caller, and the pair it realizes has the printed
invariants: the two compressions are `cos²Θⱼ`, the two angle-`0` spaces are the kernels of
`sin Θⱼ`, the two angle-`π/2` spaces are the kernels of `cos Θⱼ`, and the two crossed defects
are isometrically equivalent.

`theorem3_1_realization_ofAngles` is the same conclusion with `J` as a hypothesis; it remains
as the lower-level surface, and this theorem is `..._ofAngles` composed with
`theorem3_1_intertwiner_of_sameSpectralMultiplicity_complex`.  The recorded narrowing at the
spectral point `0` is the one on that theorem. -/
theorem theorem3_1_realization_ofSpectralMultiplicity_complex
    {Θ₀ : E₂ →L[ℂ] E₂} {Θ₁ : F₂ →L[ℂ] F₂}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (hmult : TauCeti.SameSpectralMultiplicity Θ₀ Θ₁) :
    ∃ (J : E₂ →L[ℂ] F₂) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
      (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
      (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁),
      (∀ x : E₂, (sourceSubspace ℂ E₂ F₂).starProjection
          ((HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
              hcoisom).targetSubspace.starProjection (modelInl ℂ E₂ F₂ x)) =
            modelInl ℂ E₂ F₂ (cfc Real.cos Θ₀ (cfc Real.cos Θ₀ x))) ∧
        (∀ y : F₂, (sourceSubspace ℂ E₂ F₂)ᗮ.starProjection
          (((HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
              hcoisom).targetSubspace)ᗮ.starProjection (modelInr ℂ E₂ F₂ y)) =
            modelInr ℂ E₂ F₂ (cfc Real.cos Θ₁ (cfc Real.cos Θ₁ y))) ∧
        halmosCommonPart (sourceSubspace ℂ E₂ F₂)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInl ℂ E₂ F₂ : E₂ →ₗ[ℂ] WithLp 2 (E₂ × F₂))
            (LinearMap.ker ((cfc Real.sin Θ₀ : E₂ →L[ℂ] E₂) : E₂ →ₗ[ℂ] E₂)) ∧
        halmosExteriorPart (sourceSubspace ℂ E₂ F₂)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInr ℂ E₂ F₂ : F₂ →ₗ[ℂ] WithLp 2 (E₂ × F₂))
            (LinearMap.ker ((cfc Real.sin Θ₁ : F₂ →L[ℂ] F₂) : F₂ →ₗ[ℂ] F₂)) ∧
        halmosSourceDefect (sourceSubspace ℂ E₂ F₂)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInl ℂ E₂ F₂ : E₂ →ₗ[ℂ] WithLp 2 (E₂ × F₂))
            (LinearMap.ker ((cfc Real.cos Θ₀ : E₂ →L[ℂ] E₂) : E₂ →ₗ[ℂ] E₂)) ∧
        halmosTargetDefect (sourceSubspace ℂ E₂ F₂)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInr ℂ E₂ F₂ : F₂ →ₗ[ℂ] WithLp 2 (E₂ × F₂))
            (LinearMap.ker ((cfc Real.cos Θ₁ : F₂ →L[ℂ] F₂) : F₂ →ₗ[ℂ] F₂)) ∧
        Nonempty (↥(halmosSourceDefect (sourceSubspace ℂ E₂ F₂)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
              hcoisom).targetSubspace) ≃ₗᵢ[ℂ]
          ↥(halmosTargetDefect (sourceSubspace ℂ E₂ F₂)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
              hcoisom).targetSubspace)) := by
  obtain ⟨J, hJ, hadj, hcoadj⟩ :=
    theorem3_1_intertwiner_of_sameSpectralMultiplicity_complex hΘ₀ hΘ₁ hspec₀ hspec₁ hmult
  have hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀ := by
    rw [← ContinuousLinearMap.comp_assoc, hadj, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]
  have hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁ := by
    rw [← ContinuousLinearMap.comp_assoc, hcoadj, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]
  exact ⟨J, hJ, hisom, hcoisom,
    theorem3_1_realization_ofAngles hΘ₀ hΘ₁ hspec₀ hspec₁ J hJ hisom hcoisom⟩

/-! ### The multiplicity hypothesis at the printed strength

The printed converse lets the two multiplicity functions differ at the spectral point `0`.
`SameSpectralMultiplicity Θ₀ Θ₁` is agreement everywhere, so the theorems above establish only
the equal-null-space case.  What the source actually asks for is agreement on the *nonzero*
part: `J₀` is required only to carry `closure (Ran Θ₀)` onto `closure (Ran Θ₁)`, and the null
spaces are free.

`closure (Ran Θ)` is `(ker Θ)ᗮ`, and on the printed spectrum `[0, π/2]` the kernel of `Θ` is the
kernel of `sin Θ`, which is the operator the polar resolution `S₀ = J₀ sin Θ₀` actually uses.
Restricting to `(ker (sin Θ))ᗮ` is therefore the printed hypothesis, and it is also the form
that makes the two partial-isometry identities immediate: the range of a self-adjoint operator
lies in the orthogonal complement of its kernel. -/

section AwayFromZero

variable {𝕜' : Type*} [RCLike 𝕜']
variable {G₀ : Type u} [NormedAddCommGroup G₀] [InnerProductSpace 𝕜' G₀] [CompleteSpace G₀]
variable {G₁ : Type v} [NormedAddCommGroup G₁] [InnerProductSpace 𝕜' G₁] [CompleteSpace G₁]
variable {Θ₀ : G₀ →L[𝕜'] G₀} {Θ₁ : G₁ →L[𝕜'] G₁}

/-- The nonzero part of an angle operator: the orthogonal complement of the kernel of its sine,
which is `closure (Ran Θ)` on the printed spectrum. -/
noncomputable abbrev nonzeroPart (Θ : G₀ →L[𝕜'] G₀) : Submodule 𝕜' G₀ :=
  (LinearMap.ker ((cfc Real.sin Θ : G₀ →L[𝕜'] G₀) : G₀ →ₗ[𝕜'] G₀))ᗮ

/-- The nonzero part is invariant: `sin Θ` commutes with `Θ`, so its kernel is `Θ`-invariant,
and self-adjointness carries that to the orthogonal complement. -/
theorem invariantFor_nonzeroPart (hΘ : IsSelfAdjoint Θ₀) :
    ∀ x ∈ nonzeroPart Θ₀, Θ₀ x ∈ nonzeroPart Θ₀ := by
  intro x hx
  have hcomm : Commute (cfc Real.sin Θ₀) Θ₀ := (Commute.refl Θ₀).cfc_real Real.sin
  refine (Submodule.mem_orthogonal _ _).2 fun y hy => ?_
  have hky : cfc Real.sin Θ₀ y = 0 := by simpa using (LinearMap.mem_ker).1 hy
  have hy' : cfc Real.sin Θ₀ (Θ₀ y) = 0 := by
    have h := congrArg (fun T : G₀ →L[𝕜'] G₀ => T y) hcomm.eq
    simp only [mul_apply_eq_comp] at h
    rw [h, hky, map_zero]
  have hmem : Θ₀ y ∈ LinearMap.ker ((cfc Real.sin Θ₀ : G₀ →L[𝕜'] G₀) : G₀ →ₗ[𝕜'] G₀) := by
    simpa using hy'
  have hself : ContinuousLinearMap.adjoint Θ₀ = Θ₀ :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hΘ
  have hthis := (Submodule.mem_orthogonal _ _).1 hx (Θ₀ y) hmem
  rw [← ContinuousLinearMap.adjoint_inner_left, hself]
  exact hthis

/-- **The printed multiplicity hypothesis**: the two angle operators have the same spectral
multiplicity data on their nonzero parts, with the null spaces unconstrained. -/
def SameSpectralMultiplicityAwayFromZero
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁) : Prop :=
  TauCeti.SameSpectralMultiplicity
    (Θ₀.restrict (invariantFor_nonzeroPart hΘ₀))
    (Θ₁.restrict (invariantFor_nonzeroPart hΘ₁))

/-- The unitary equivalence of the two nonzero parts, which is what the multiplicity hypothesis
delivers.  Taking it as the hypothesis makes the construction below field-generic; the two
classifications that produce it are stated one field at a time. -/
def NonzeroPartsUnitaryEquiv (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁) : Prop :=
  TauCeti.OperatorUnitaryEquiv
    (Θ₀.restrict (invariantFor_nonzeroPart hΘ₀))
    (Θ₁.restrict (invariantFor_nonzeroPart hΘ₁))

/-- A self-adjoint operator maps into the orthogonal complement of its own kernel. -/
private theorem apply_mem_ker_orthogonal {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜' G] [CompleteSpace G] {S : G →L[𝕜'] G} (hS : IsSelfAdjoint S) (x : G) :
    S x ∈ (LinearMap.ker (S : G →ₗ[𝕜'] G))ᗮ := by
  refine (Submodule.mem_orthogonal _ _).2 fun y hy => ?_
  have hSy : S y = 0 := by simpa using (LinearMap.mem_ker).1 hy
  have hself : ContinuousLinearMap.adjoint S = S := ContinuousLinearMap.isSelfAdjoint_iff'.mp hS
  rw [← ContinuousLinearMap.adjoint_inner_left, hself, hSy, inner_zero_left]

/-- **Davis--Kahan 1970, Theorem 3.1: the printed partial isometry `J₀`, constructed from the
printed multiplicity hypothesis.**

The null spaces are unconstrained: only the nonzero parts are compared, which is the source's
"their spectral multiplicity functions agree except possibly at the eigenvalue `0`", and `J₀` is
built rather than assumed.  It is the unitary between the nonzero parts, extended by zero on the
null space -- the source's `J₀`, which "carries `closure (Ran Θ₀)` isometrically onto
`closure (Ran Θ₁)`".

The two partial-isometry identities come out as identities about the nonzero parts, and they
hold on the ranges of the sines because a self-adjoint operator maps into the orthogonal
complement of its own kernel. -/
theorem theorem3_1_intertwiner_of_nonzeroPartsUnitaryEquiv
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hmult : NonzeroPartsUnitaryEquiv hΘ₀ hΘ₁) :
    ∃ J : G₀ →L[𝕜'] G₁, J ∘L Θ₀ = Θ₁ ∘L J ∧
      ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀ ∧
      J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁ := by
  classical
  set K₀ : Submodule 𝕜' G₀ := nonzeroPart Θ₀ with hK₀
  set K₁ : Submodule 𝕜' G₁ := nonzeroPart Θ₁ with hK₁
  obtain ⟨e, he⟩ := hmult
  set J : G₀ →L[𝕜'] G₁ := K₁.subtypeL ∘L (e : K₀ →L[𝕜'] K₁) ∘L K₀.orthogonalProjectionOnto with hJ
  -- the adjoint, computed once
  have hadjJ : ContinuousLinearMap.adjoint J =
      K₀.subtypeL ∘L (e.symm : K₁ →L[𝕜'] K₀) ∘L K₁.orthogonalProjectionOnto := by
    rw [hJ, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      Submodule.adjoint_subtypeL, e.adjoint_eq_symm,
      Submodule.adjoint_orthogonalProjectionOnto]
    rfl
  -- the two projections, from the two triple cancellations
  have hp₀ : ∀ u : K₀, K₀.orthogonalProjectionOnto (K₀.subtypeL u) = u := fun u =>
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self u
  have hp₁ : ∀ u : K₁, K₁.orthogonalProjectionOnto (K₁.subtypeL u) = u := fun u =>
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self u
  have hJJ : ContinuousLinearMap.adjoint J ∘L J = K₀.starProjection := by
    ext x
    rw [hadjJ]
    change K₀.subtypeL ((e.symm : K₁ →L[𝕜'] K₀)
        (K₁.orthogonalProjectionOnto (J x))) = K₀.starProjection x
    have hJx : J x = K₁.subtypeL ((e : K₀ →L[𝕜'] K₁) (K₀.orthogonalProjectionOnto x)) := rfl
    rw [hJx, hp₁]
    change K₀.subtypeL (e.symm (e (K₀.orthogonalProjectionOnto x))) = _
    rw [e.symm_apply_apply]
    rfl
  have hJJ' : J ∘L ContinuousLinearMap.adjoint J = K₁.starProjection := by
    ext y
    rw [hadjJ]
    change K₁.subtypeL ((e : K₀ →L[𝕜'] K₁) (K₀.orthogonalProjectionOnto (K₀.subtypeL
      ((e.symm : K₁ →L[𝕜'] K₀) (K₁.orthogonalProjectionOnto y))))) = K₁.starProjection y
    rw [hp₀]
    change K₁.subtypeL (e (e.symm (K₁.orthogonalProjectionOnto y))) = _
    rw [e.apply_symm_apply]
    rfl
  refine ⟨J, ?_, ?_, ?_⟩
  · -- the intertwining, read on the two `Θ₀`-invariant summands
    -- `K₀ᗮ` is the kernel of `sin Θ₀`, which `Θ₀` preserves because the two commute
    have hperp : K₀ᗮ = LinearMap.ker ((cfc Real.sin Θ₀ : G₀ →L[𝕜'] G₀) : G₀ →ₗ[𝕜'] G₀) := by
      rw [hK₀]
      exact Submodule.orthogonal_orthogonal _
    have hcomm : Commute (cfc Real.sin Θ₀) Θ₀ := (Commute.refl Θ₀).cfc_real Real.sin
    have hinvperp : ∀ v ∈ K₀ᗮ, Θ₀ v ∈ K₀ᗮ := by
      intro v hv
      rw [hperp] at hv ⊢
      have hSv : cfc Real.sin Θ₀ v = 0 := by simpa using (LinearMap.mem_ker).1 hv
      have h := congrArg (fun T : G₀ →L[𝕜'] G₀ => T v) hcomm.eq
      simp only [mul_apply_eq_comp] at h
      simp [h, hSv]
    -- hence the projection onto `K₀` commutes with `Θ₀`
    have hPcomm : ∀ x : G₀, K₀.starProjection (Θ₀ x) = Θ₀ (K₀.starProjection x) := by
      intro x
      have hsplit : K₀.starProjection x + K₀ᗮ.starProjection x = x :=
        Submodule.starProjection_add_starProjection_orthogonal (K := K₀) x
      have hu : Θ₀ (K₀.starProjection x) ∈ K₀ :=
        invariantFor_nonzeroPart hΘ₀ _ (K₀.starProjection_apply_mem x)
      have hv : Θ₀ (K₀ᗮ.starProjection x) ∈ K₀ᗮ :=
        hinvperp _ (K₀ᗮ.starProjection_apply_mem x)
      calc K₀.starProjection (Θ₀ x)
          = K₀.starProjection (Θ₀ (K₀.starProjection x) + Θ₀ (K₀ᗮ.starProjection x)) := by
            rw [← map_add, hsplit]
        _ = Θ₀ (K₀.starProjection x) := by
            rw [map_add, Submodule.starProjection_eq_self_iff.mpr hu,
              show K₀.starProjection (Θ₀ (K₀ᗮ.starProjection x)) = 0 from by
                rw [Submodule.starProjection_apply, Submodule.coe_eq_zero]
                exact Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hv,
              add_zero]
    ext x
    change K₁.subtypeL ((e : K₀ →L[𝕜'] K₁) (K₀.orthogonalProjectionOnto (Θ₀ x))) =
      Θ₁ (K₁.subtypeL ((e : K₀ →L[𝕜'] K₁) (K₀.orthogonalProjectionOnto x)))
    -- the projection commutes, so the argument is the restriction applied to `P₀ x`
    have hrestr : K₀.orthogonalProjectionOnto (Θ₀ x)
        = Θ₀.restrict (invariantFor_nonzeroPart hΘ₀) (K₀.orthogonalProjectionOnto x) := by
      apply Subtype.ext
      exact hPcomm x
    calc K₁.subtypeL ((e : K₀ →L[𝕜'] K₁) (K₀.orthogonalProjectionOnto (Θ₀ x)))
        = K₁.subtypeL (e (Θ₀.restrict (invariantFor_nonzeroPart hΘ₀)
            (K₀.orthogonalProjectionOnto x))) := by rw [hrestr]; rfl
      _ = K₁.subtypeL (Θ₁.restrict (invariantFor_nonzeroPart hΘ₁)
            (e (K₀.orthogonalProjectionOnto x))) :=
          congrArg K₁.subtypeL (he (K₀.orthogonalProjectionOnto x))
      _ = Θ₁ (K₁.subtypeL ((e : K₀ →L[𝕜'] K₁) (K₀.orthogonalProjectionOnto x))) := rfl
  · rw [← ContinuousLinearMap.comp_assoc, hJJ]
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr
      (apply_mem_ker_orthogonal (S := cfc Real.sin Θ₀) (cfc_predicate _ _) x)
  · rw [← ContinuousLinearMap.comp_assoc, hJJ']
    ext y
    exact Submodule.starProjection_eq_self_iff.mpr
      (apply_mem_ker_orthogonal (S := cfc Real.sin Θ₁) (cfc_predicate _ _) y)

/-- **Davis--Kahan 1970, Theorem 3.1, converse sentence, at the printed hypotheses.**

Two arbitrary self-adjoint operators with `0 ≤ Θⱼ ≤ π/2` whose spectral multiplicity functions
agree *except possibly at `0`*, and nothing else.  The intertwining partial isometry `J₀` the
printed proof reconstructs is produced here, and the pair it realizes has the printed
invariants.

This is the printed converse.  `theorem3_1_realization_ofSpectralMultiplicity_complex` is the
special case in which the multiplicity functions also agree at `0`, and
`theorem3_1_realization_ofAngles` is the lower-level surface that takes `J₀` as a hypothesis. -/
theorem theorem3_1_realization_ofNonzeroPartsUnitaryEquiv
    {Θ₀ : G₀ →L[𝕜'] G₀} {Θ₁ : G₁ →L[𝕜'] G₁}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (hmult : NonzeroPartsUnitaryEquiv hΘ₀ hΘ₁) :
    ∃ (J : G₀ →L[𝕜'] G₁) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
      (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
      (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁),
      halmosCommonPart (sourceSubspace 𝕜' G₀ G₁)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl 𝕜' G₀ G₁ : G₀ →ₗ[𝕜'] WithLp 2 (G₀ × G₁))
          (LinearMap.ker ((cfc Real.sin Θ₀ : G₀ →L[𝕜'] G₀) : G₀ →ₗ[𝕜'] G₀)) ∧
        halmosExteriorPart (sourceSubspace 𝕜' G₀ G₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInr 𝕜' G₀ G₁ : G₁ →ₗ[𝕜'] WithLp 2 (G₀ × G₁))
            (LinearMap.ker ((cfc Real.sin Θ₁ : G₁ →L[𝕜'] G₁) : G₁ →ₗ[𝕜'] G₁)) ∧
        halmosSourceDefect (sourceSubspace 𝕜' G₀ G₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInl 𝕜' G₀ G₁ : G₀ →ₗ[𝕜'] WithLp 2 (G₀ × G₁))
            (LinearMap.ker ((cfc Real.cos Θ₀ : G₀ →L[𝕜'] G₀) : G₀ →ₗ[𝕜'] G₀)) ∧
        halmosTargetDefect (sourceSubspace 𝕜' G₀ G₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInr 𝕜' G₀ G₁ : G₁ →ₗ[𝕜'] WithLp 2 (G₀ × G₁))
            (LinearMap.ker ((cfc Real.cos Θ₁ : G₁ →L[𝕜'] G₁) : G₁ →ₗ[𝕜'] G₁)) := by
  obtain ⟨J, hJ, hisom, hcoisom⟩ :=
    theorem3_1_intertwiner_of_nonzeroPartsUnitaryEquiv hΘ₀ hΘ₁ hmult
  obtain ⟨-, -, h₃, h₄, h₅, h₆, -⟩ :=
    theorem3_1_realization_ofAngles hΘ₀ hΘ₁ hspec₀ hspec₁ J hJ hisom hcoisom
  exact ⟨J, hJ, hisom, hcoisom, h₃, h₄, h₅, h₆⟩

/-! ### The multiplicity classification, one field at a time

The construction above is field-generic once the unitary equivalence of the nonzero parts is in
hand.  Producing it from the printed multiplicity hypothesis is where the two fields separate,
because Hahn--Hellinger is stated one field at a time.  These two wrappers are the printed
converse over `ℂ` and over `ℝ`, which is the source's own scalar scope. -/

section Fields

/-- **Davis--Kahan 1970, Theorem 3.1, converse sentence over `ℂ`, at the printed hypotheses.**

Two arbitrary self-adjoint operators with `0 ≤ Θⱼ ≤ π/2` whose spectral multiplicity functions
agree *except possibly at `0`*, and nothing else.  `J₀` is constructed. -/
theorem theorem3_1_realization_ofSpectralMultiplicityAwayFromZero_complex
    {A₀ : Type u} [NormedAddCommGroup A₀] [InnerProductSpace ℂ A₀] [CompleteSpace A₀]
    {A₁ : Type v} [NormedAddCommGroup A₁] [InnerProductSpace ℂ A₁] [CompleteSpace A₁]
    {Θ₀ : A₀ →L[ℂ] A₀} {Θ₁ : A₁ →L[ℂ] A₁}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (hmult : SameSpectralMultiplicityAwayFromZero hΘ₀ hΘ₁) :
    ∃ (J : A₀ →L[ℂ] A₁) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
      (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
      (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁),
      halmosCommonPart (sourceSubspace ℂ A₀ A₁)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl ℂ A₀ A₁ : A₀ →ₗ[ℂ] WithLp 2 (A₀ × A₁))
          (LinearMap.ker ((cfc Real.sin Θ₀ : A₀ →L[ℂ] A₀) : A₀ →ₗ[ℂ] A₀)) ∧
        halmosExteriorPart (sourceSubspace ℂ A₀ A₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInr ℂ A₀ A₁ : A₁ →ₗ[ℂ] WithLp 2 (A₀ × A₁))
            (LinearMap.ker ((cfc Real.sin Θ₁ : A₁ →L[ℂ] A₁) : A₁ →ₗ[ℂ] A₁)) ∧
        halmosSourceDefect (sourceSubspace ℂ A₀ A₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInl ℂ A₀ A₁ : A₀ →ₗ[ℂ] WithLp 2 (A₀ × A₁))
            (LinearMap.ker ((cfc Real.cos Θ₀ : A₀ →L[ℂ] A₀) : A₀ →ₗ[ℂ] A₀)) ∧
        halmosTargetDefect (sourceSubspace ℂ A₀ A₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInr ℂ A₀ A₁ : A₁ →ₗ[ℂ] WithLp 2 (A₀ × A₁))
            (LinearMap.ker ((cfc Real.cos Θ₁ : A₁ →L[ℂ] A₁) : A₁ →ₗ[ℂ] A₁)) :=
  theorem3_1_realization_ofNonzeroPartsUnitaryEquiv hΘ₀ hΘ₁ hspec₀ hspec₁
    (TauCeti.operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex _ _ hmult)

/-- **Davis--Kahan 1970, Theorem 3.1, converse sentence over `ℝ`, at the printed hypotheses.**

The real sibling, at the same strength: no separability hypothesis on either space.

An earlier version of this docstring said `A₀` carries the source's separability.  It does not,
and the signature never did -- the 2026-09-05 hostile follow-up review caught the sentence.
Separability is needed for the *other* direction of the real multiplicity classification, where a
model has to be built from a countable cyclic decomposition
(`sameSpectralMultiplicity_of_unitaryEquiv_real`).  The direction used here,
`operatorUnitaryEquiv_of_sameSpectralMultiplicity_real`, consumes a model that the hypothesis
already supplies, so it needs none. -/
theorem theorem3_1_realization_ofSpectralMultiplicityAwayFromZero_real
    {A₀ : Type u} [NormedAddCommGroup A₀] [InnerProductSpace ℝ A₀] [CompleteSpace A₀]
    {A₁ : Type v} [NormedAddCommGroup A₁] [InnerProductSpace ℝ A₁] [CompleteSpace A₁]
    {Θ₀ : A₀ →L[ℝ] A₀} {Θ₁ : A₁ →L[ℝ] A₁}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (hmult : SameSpectralMultiplicityAwayFromZero hΘ₀ hΘ₁) :
    ∃ (J : A₀ →L[ℝ] A₁) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
      (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
      (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁),
      halmosCommonPart (sourceSubspace ℝ A₀ A₁)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl ℝ A₀ A₁ : A₀ →ₗ[ℝ] WithLp 2 (A₀ × A₁))
          (LinearMap.ker ((cfc Real.sin Θ₀ : A₀ →L[ℝ] A₀) : A₀ →ₗ[ℝ] A₀)) ∧
        halmosExteriorPart (sourceSubspace ℝ A₀ A₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInr ℝ A₀ A₁ : A₁ →ₗ[ℝ] WithLp 2 (A₀ × A₁))
            (LinearMap.ker ((cfc Real.sin Θ₁ : A₁ →L[ℝ] A₁) : A₁ →ₗ[ℝ] A₁)) ∧
        halmosSourceDefect (sourceSubspace ℝ A₀ A₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInl ℝ A₀ A₁ : A₀ →ₗ[ℝ] WithLp 2 (A₀ × A₁))
            (LinearMap.ker ((cfc Real.cos Θ₀ : A₀ →L[ℝ] A₀) : A₀ →ₗ[ℝ] A₀)) ∧
        halmosTargetDefect (sourceSubspace ℝ A₀ A₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInr ℝ A₀ A₁ : A₁ →ₗ[ℝ] WithLp 2 (A₀ × A₁))
            (LinearMap.ker ((cfc Real.cos Θ₁ : A₁ →L[ℝ] A₁) : A₁ →ₗ[ℝ] A₁)) :=
  theorem3_1_realization_ofNonzeroPartsUnitaryEquiv hΘ₀ hΘ₁ hspec₀ hspec₁
    (TauCeti.DavisKahan.RealSpectralRestriction.operatorUnitaryEquiv_of_sameSpectralMultiplicity_real
      _ _ hmult)

/-! ### The printed ambient-dimension clause

The printed converse reads: "the angle operators may be arbitrary Hermitian operators
satisfying `0 ≤ Θⱼ ≤ π/2`, **their domain dimensions sum to `dim H`**, and their spectral
multiplicity functions agree except possibly at the spectral point `0`".

The realizations above build the pair on `WithLp 2 (A₀ × A₁)`, the orthogonal direct sum of
the two angle-operator domains, so the dimension equation holds there by construction -- but
there is no ambient `H` in their signatures at all, and so nothing in their types answers the
printed clause.  The wrappers below put it back.

The dimension hypothesis is supplied constructively, as a linear isometry equivalence
`WithLp 2 (A₀ × A₁) ≃ₗᵢ[𝕜] H`.  That is the same hypothesis: two Hilbert spaces admit such an
equivalence exactly when their Hilbert dimensions agree
(`TauCeti.nonempty_linearIsometryEquiv_of_hilbertBasis`), and the Hilbert dimension of the
orthogonal direct sum is the sum of the two.  Supplying the equivalence rather than a cardinal
equation is the same choice the repository makes for condition (3.5), where the crossed-defect
identification is carried by an explicit isometry.

The realized pair inside `H` is the isometric image of the model pair, so
`PairOfSubspacesUnitaryEquivalent` holds between them and the four Halmos identities of the
model realization transfer along `e` -- which is exactly the sense in which Theorem 3.1
classifies pairs, namely up to isometric equivalence. -/

section AmbientDimension

/-- **Davis--Kahan 1970, Theorem 3.1, converse sentence over `ℂ`, with the printed ambient
space and its dimension clause.**

Given an ambient Hilbert space `H` whose dimension is the sum of the two angle-operator
domain dimensions -- supplied as the isometry `e` -- the realized pair lives in `H`: there are
subspaces `P, Q ≤ H` that are the isometric image of the model pair, and the model pair carries
the four Halmos identities the printed converse asserts.

`P` and `Q` are exhibited, not merely asserted to exist, so the conclusion also records that
`(P, Q)` is unitarily equivalent to the model pair as an ordered pair of subspaces. -/
theorem theorem3_1_realization_inAmbient_ofSpectralMultiplicityAwayFromZero_complex
    {A₀ : Type u} [NormedAddCommGroup A₀] [InnerProductSpace ℂ A₀] [CompleteSpace A₀]
    {A₁ : Type v} [NormedAddCommGroup A₁] [InnerProductSpace ℂ A₁] [CompleteSpace A₁]
    {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Θ₀ : A₀ →L[ℂ] A₀} {Θ₁ : A₁ →L[ℂ] A₁}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (hmult : SameSpectralMultiplicityAwayFromZero hΘ₀ hΘ₁)
    (e : WithLp 2 (A₀ × A₁) ≃ₗᵢ[ℂ] H) :
    ∃ (J : A₀ →L[ℂ] A₁) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
      (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
      (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁),
      TauCeti.DavisKahan.PairOfSubspacesUnitaryEquivalent
          (sourceSubspace ℂ A₀ A₁)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace
          (Submodule.map (e.toLinearEquiv : WithLp 2 (A₀ × A₁) →ₗ[ℂ] H)
            (sourceSubspace ℂ A₀ A₁))
          (Submodule.map (e.toLinearEquiv : WithLp 2 (A₀ × A₁) →ₗ[ℂ] H)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace) ∧
      halmosCommonPart (sourceSubspace ℂ A₀ A₁)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl ℂ A₀ A₁ : A₀ →ₗ[ℂ] WithLp 2 (A₀ × A₁))
          (LinearMap.ker ((cfc Real.sin Θ₀ : A₀ →L[ℂ] A₀) : A₀ →ₗ[ℂ] A₀)) ∧
        halmosExteriorPart (sourceSubspace ℂ A₀ A₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInr ℂ A₀ A₁ : A₁ →ₗ[ℂ] WithLp 2 (A₀ × A₁))
            (LinearMap.ker ((cfc Real.sin Θ₁ : A₁ →L[ℂ] A₁) : A₁ →ₗ[ℂ] A₁)) ∧
        halmosSourceDefect (sourceSubspace ℂ A₀ A₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInl ℂ A₀ A₁ : A₀ →ₗ[ℂ] WithLp 2 (A₀ × A₁))
            (LinearMap.ker ((cfc Real.cos Θ₀ : A₀ →L[ℂ] A₀) : A₀ →ₗ[ℂ] A₀)) ∧
        halmosTargetDefect (sourceSubspace ℂ A₀ A₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInr ℂ A₀ A₁ : A₁ →ₗ[ℂ] WithLp 2 (A₀ × A₁))
            (LinearMap.ker ((cfc Real.cos Θ₁ : A₁ →L[ℂ] A₁) : A₁ →ₗ[ℂ] A₁)) := by
  obtain ⟨J, hJ, hisom, hcoisom, h₃, h₄, h₅, h₆⟩ :=
    theorem3_1_realization_ofSpectralMultiplicityAwayFromZero_complex hΘ₀ hΘ₁ hspec₀ hspec₁ hmult
  exact ⟨J, hJ, hisom, hcoisom, ⟨e, rfl, rfl⟩, h₃, h₄, h₅, h₆⟩

/-- **Davis--Kahan 1970, Theorem 3.1, converse sentence over `ℝ`, with the printed ambient
space and its dimension clause.**  The real sibling of
`theorem3_1_realization_inAmbient_ofSpectralMultiplicityAwayFromZero_complex`. -/
theorem theorem3_1_realization_inAmbient_ofSpectralMultiplicityAwayFromZero_real
    {A₀ : Type u} [NormedAddCommGroup A₀] [InnerProductSpace ℝ A₀] [CompleteSpace A₀]
    {A₁ : Type v} [NormedAddCommGroup A₁] [InnerProductSpace ℝ A₁] [CompleteSpace A₁]
    {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {Θ₀ : A₀ →L[ℝ] A₀} {Θ₁ : A₁ →L[ℝ] A₁}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (hmult : SameSpectralMultiplicityAwayFromZero hΘ₀ hΘ₁)
    (e : WithLp 2 (A₀ × A₁) ≃ₗᵢ[ℝ] H) :
    ∃ (J : A₀ →L[ℝ] A₁) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
      (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
      (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁),
      TauCeti.DavisKahan.PairOfSubspacesUnitaryEquivalent
          (sourceSubspace ℝ A₀ A₁)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace
          (Submodule.map (e.toLinearEquiv : WithLp 2 (A₀ × A₁) →ₗ[ℝ] H)
            (sourceSubspace ℝ A₀ A₁))
          (Submodule.map (e.toLinearEquiv : WithLp 2 (A₀ × A₁) →ₗ[ℝ] H)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace) ∧
      halmosCommonPart (sourceSubspace ℝ A₀ A₁)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl ℝ A₀ A₁ : A₀ →ₗ[ℝ] WithLp 2 (A₀ × A₁))
          (LinearMap.ker ((cfc Real.sin Θ₀ : A₀ →L[ℝ] A₀) : A₀ →ₗ[ℝ] A₀)) ∧
        halmosExteriorPart (sourceSubspace ℝ A₀ A₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInr ℝ A₀ A₁ : A₁ →ₗ[ℝ] WithLp 2 (A₀ × A₁))
            (LinearMap.ker ((cfc Real.sin Θ₁ : A₁ →L[ℝ] A₁) : A₁ →ₗ[ℝ] A₁)) ∧
        halmosSourceDefect (sourceSubspace ℝ A₀ A₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInl ℝ A₀ A₁ : A₀ →ₗ[ℝ] WithLp 2 (A₀ × A₁))
            (LinearMap.ker ((cfc Real.cos Θ₀ : A₀ →L[ℝ] A₀) : A₀ →ₗ[ℝ] A₀)) ∧
        halmosTargetDefect (sourceSubspace ℝ A₀ A₁)
            (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
          Submodule.map (modelInr ℝ A₀ A₁ : A₁ →ₗ[ℝ] WithLp 2 (A₀ × A₁))
            (LinearMap.ker ((cfc Real.cos Θ₁ : A₁ →L[ℝ] A₁) : A₁ →ₗ[ℝ] A₁)) := by
  obtain ⟨J, hJ, hisom, hcoisom, h₃, h₄, h₅, h₆⟩ :=
    theorem3_1_realization_ofSpectralMultiplicityAwayFromZero_real hΘ₀ hΘ₁ hspec₀ hspec₁ hmult
  exact ⟨J, hJ, hisom, hcoisom, ⟨e, rfl, rfl⟩, h₃, h₄, h₅, h₆⟩

/-! ### The dimension clause as a proposition

The printed converse assumes `dim A₀ + dim A₁ = dim H`.  That is a *proposition*
about the three spaces, not a chosen isometric equivalence, and the two theorems
above take the equivalence as an explicit argument.  For Hilbert spaces the two
are interchangeable -- equality of Hilbert dimensions is exactly the existence of
a linear isometric equivalence -- but the source-facing statement should take the
proposition and produce the equivalence, not demand it from the caller.

`SameHilbertDimensionSum` is that proposition, and the two theorems below are the
printed converse: from the dimension clause they *produce* a realization inside
`H`, rather than asking which realization to use.  This is the same discipline
already applied to `J₀`: construction data follows from the source hypothesis and
so does not belong in the source-facing signature. -/

/-- **The source's ambient dimension clause**, `dim A₀ + dim A₁ = dim H`, as a
proposition about the three spaces.

For Hilbert spaces, equality of Hilbert dimensions is equivalent to the existence
of a linear isometric equivalence, and this is the form the realization consumes. -/
def SameHilbertDimensionSum (𝕜 : Type*) [RCLike 𝕜]
    (A₀ : Type u) [NormedAddCommGroup A₀] [InnerProductSpace 𝕜 A₀]
    (A₁ : Type v) [NormedAddCommGroup A₁] [InnerProductSpace 𝕜 A₁]
    (H : Type w) [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] : Prop :=
  Nonempty (WithLp 2 (A₀ × A₁) ≃ₗᵢ[𝕜] H)

/-- **Davis--Kahan 1970, Theorem 3.1, converse sentence over `ℂ`, taking the
printed dimension clause as a proposition.**

The realization inside the ambient `H` is produced, not supplied. -/
theorem theorem3_1_realization_inAmbient_ofSameHilbertDimension_complex
    {A₀ : Type u} [NormedAddCommGroup A₀] [InnerProductSpace ℂ A₀] [CompleteSpace A₀]
    {A₁ : Type v} [NormedAddCommGroup A₁] [InnerProductSpace ℂ A₁] [CompleteSpace A₁]
    {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Θ₀ : A₀ →L[ℂ] A₀} {Θ₁ : A₁ →L[ℂ] A₁}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (hmult : SameSpectralMultiplicityAwayFromZero hΘ₀ hΘ₁)
    (hdim : SameHilbertDimensionSum ℂ A₀ A₁ H) :
    ∃ (P Q : Submodule ℂ H) (J : A₀ →L[ℂ] A₁) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
      (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
      (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁),
      TauCeti.DavisKahan.PairOfSubspacesUnitaryEquivalent
        (sourceSubspace ℂ A₀ A₁)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace
        P Q := by
  obtain ⟨e⟩ := hdim
  obtain ⟨J, hJ, hisom, hcoisom, hpair, -, -, -, -⟩ :=
    theorem3_1_realization_inAmbient_ofSpectralMultiplicityAwayFromZero_complex
      hΘ₀ hΘ₁ hspec₀ hspec₁ hmult e
  exact ⟨_, _, J, hJ, hisom, hcoisom, hpair⟩

/-- **Davis--Kahan 1970, Theorem 3.1, converse sentence over `ℝ`, taking the
printed dimension clause as a proposition.** -/
theorem theorem3_1_realization_inAmbient_ofSameHilbertDimension_real
    {A₀ : Type u} [NormedAddCommGroup A₀] [InnerProductSpace ℝ A₀] [CompleteSpace A₀]
    {A₁ : Type v} [NormedAddCommGroup A₁] [InnerProductSpace ℝ A₁] [CompleteSpace A₁]
    {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {Θ₀ : A₀ →L[ℝ] A₀} {Θ₁ : A₁ →L[ℝ] A₁}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (hmult : SameSpectralMultiplicityAwayFromZero hΘ₀ hΘ₁)
    (hdim : SameHilbertDimensionSum ℝ A₀ A₁ H) :
    ∃ (P Q : Submodule ℝ H) (J : A₀ →L[ℝ] A₁) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
      (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
      (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁),
      TauCeti.DavisKahan.PairOfSubspacesUnitaryEquivalent
        (sourceSubspace ℝ A₀ A₁)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace
        P Q := by
  obtain ⟨e⟩ := hdim
  obtain ⟨J, hJ, hisom, hcoisom, hpair, -, -, -, -⟩ :=
    theorem3_1_realization_inAmbient_ofSpectralMultiplicityAwayFromZero_real
      hΘ₀ hΘ₁ hspec₀ hspec₁ hmult e
  exact ⟨_, _, J, hJ, hisom, hcoisom, hpair⟩

/-! ### The converse at the paper's own ambient scope

Davis and Kahan work throughout on a separable Hilbert space, and the converse
sentence reconstructs a pair *in that space*.  The two declarations below are the
converse at that scope, with the partial isometry `J₀` — which the source
introduces inside the *proof*, after the theorem's data have been specified —
existentially internal to the angle datum rather than exposed in the conclusion.

`theorem3_1_realization_inAmbient_ofSameHilbertDimension_*` above are the same
mathematics on an arbitrary ambient Hilbert space and with the datum's pieces
spelled out; they are the general form, not the printed one. -/

section SourceScope

variable {A₀ : Type u} [NormedAddCommGroup A₀] [CompleteSpace A₀]
variable {A₁ : Type v} [NormedAddCommGroup A₁] [CompleteSpace A₁]
variable {H : Type w} [NormedAddCommGroup H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **Davis--Kahan 1970, Theorem 3.1, converse sentence, at the printed source
scope over `ℂ`.**

Admissible angle data — Hermitian, spectrum in `[0, π/2]`, matching spectral
multiplicity away from `0`, domain dimensions summing to `dim H` — are realized
by a pair of subspaces of the paper's separable ambient space, up to isometric
equivalence with the model pair carrying exactly those angle data. -/
theorem theorem3_1_realization_sourceExact_complex
    [InnerProductSpace ℂ A₀] [InnerProductSpace ℂ A₁] [InnerProductSpace ℂ H]
    {Θ₀ : A₀ →L[ℂ] A₀} {Θ₁ : A₁ →L[ℂ] A₁}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (hmult : SameSpectralMultiplicityAwayFromZero hΘ₀ hΘ₁)
    (hdim : SameHilbertDimensionSum ℂ A₀ A₁ H) :
    ∃ (P Q : Submodule ℂ H) (d : TauCeti.DavisKahan.HalmosAngleDatum ℂ A₀ A₁),
      d.cos₀ = cfc Real.cos Θ₀ ∧ d.sin₀ = cfc Real.sin Θ₀ ∧
        d.cos₁ = cfc Real.cos Θ₁ ∧ d.sin₁ = cfc Real.sin Θ₁ ∧
        TauCeti.DavisKahan.PairOfSubspacesUnitaryEquivalent
          (sourceSubspace ℂ A₀ A₁) d.targetSubspace P Q := by
  obtain ⟨P, Q, J, hJ, hisom, hcoisom, hpair⟩ :=
    theorem3_1_realization_inAmbient_ofSameHilbertDimension_complex hΘ₀ hΘ₁ hspec₀
      hspec₁ hmult hdim
  exact ⟨P, Q, _, rfl, rfl, rfl, rfl, hpair⟩

omit [CompleteSpace H] in
/-- **Davis--Kahan 1970, Theorem 3.1, converse sentence, at the printed source
scope over `ℝ`.** -/
theorem theorem3_1_realization_sourceExact_real
    [InnerProductSpace ℝ A₀] [InnerProductSpace ℝ A₁] [InnerProductSpace ℝ H]
    {Θ₀ : A₀ →L[ℝ] A₀} {Θ₁ : A₁ →L[ℝ] A₁}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (hmult : SameSpectralMultiplicityAwayFromZero hΘ₀ hΘ₁)
    (hdim : SameHilbertDimensionSum ℝ A₀ A₁ H) :
    ∃ (P Q : Submodule ℝ H) (d : TauCeti.DavisKahan.HalmosAngleDatum ℝ A₀ A₁),
      d.cos₀ = cfc Real.cos Θ₀ ∧ d.sin₀ = cfc Real.sin Θ₀ ∧
        d.cos₁ = cfc Real.cos Θ₁ ∧ d.sin₁ = cfc Real.sin Θ₁ ∧
        TauCeti.DavisKahan.PairOfSubspacesUnitaryEquivalent
          (sourceSubspace ℝ A₀ A₁) d.targetSubspace P Q := by
  obtain ⟨P, Q, J, hJ, hisom, hcoisom, hpair⟩ :=
    theorem3_1_realization_inAmbient_ofSameHilbertDimension_real hΘ₀ hΘ₁ hspec₀
      hspec₁ hmult hdim
  exact ⟨P, Q, _, rfl, rfl, rfl, rfl, hpair⟩

end SourceScope

end AmbientDimension

end Fields

end AwayFromZero

end OfMultiplicity

end DavisKahan1970
end TauCeti
