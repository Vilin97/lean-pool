/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.StandardDescent
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberLocLift
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizationLiftContinuityBounded

/-!
# Relative descent infrastructure: the noetherian-free keystone

Phase 1 of the sheafy repair campaign (Kedlaya Lemma 1.6.8's relative mechanism,
noetherian-free). For a valid rational base `D₀` over `A` with section ring
`B := 𝒪(D₀) = presheafValue D₀`:

* **`B`-instances** (noetherian-free, any datum): `IsHuberRing`/`IsTateRing`/
  `NonarchimedeanRing`/right-uniformity-`CompleteSpace` on `presheafValue D` — so
  `HasLocLiftPowerBounded (presheafValue D)` synthesizes through the proven
  full-Huber instance (`hasLocLiftPowerBounded_huber_instance`), with **no**
  noetherian input.
* **`imgDatum`** — the image rational datum over `B` of a valid `A`-datum `E`
  (parameters `canonicalMap '' E.T` and `canonicalMap E.s`; `hopen` by the span
  constructor `genPieceDatum`), with `imgDatum_rationalOpen_subset`: an `A⁺`-level
  containment `R(E') ⊆ R(E)` transfers to the `B⁺`-level containment of the image
  opens, through the proven `Spa`-restriction
  (`comap_mem_spa`/`comap_canonicalMap_mem_rationalOpen`, HuberLocLift).
* **The keystone, noetherian-free** (Wedhorn Lemma 8.1 / Proposition 8.2(2) /
  Remark 8.4 — the universal property of `A⟨T/s⟩` and the identification of the
  iterated rational localization;
  replaces the strongly-noetherian-scoped `relativePiece_equiv` on the descent
  path): `keystoneHom`/`keystoneInv` between `𝒪_A(E)` and `𝒪_B(imgDatum D₀ E)`,
  mutually inverse (`keystone` as a `RingEquiv`), continuous both ways,
  intertwining the canonical maps (`keystoneHom_canonicalMap`) and the restriction
  maps on both sides (`keystone_restriction_square`). Universal-property route:
  both directions are `IsLocalization.Away.lift`s extended to the completions
  (`locTopology_continuous_lift` supplies continuity from power-boundedness of the
  `t/s`-lifts — the `HasLocLiftPowerBounded` package at reflexive containments);
  round-trips and squares by `IsLocalization.ringHom_ext` + density.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 8.1, Prop 8.2(2), Remark 8.4.
* [K. Kedlaya, AWS 2017], Lemma 1.6.8 ("every rational subspace of `X` is itself
  the spectrum of a Huber pair" — this file is that statement's section-ring level).
-/

noncomputable section

open TopologicalSpace

universe u

namespace ValuationSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-! ### Noetherian-free instances on the section rings -/

instance presheafValue.instIsHuberRing (D : RationalLocData A) :
    IsHuberRing (presheafValue D) :=
  ⟨⟨presheafValue_concretePair D⟩⟩

instance presheafValue.instIsTateRing [IsTateRing A] (D : RationalLocData A) :
    IsTateRing (presheafValue D) where
  exists_pairOfDefinition := ⟨presheafValue_concretePair D⟩
  exists_topologicallyNilpotent_unit := presheafValue_topNilUnit D

instance presheafValue.instNonarchimedeanRing (D : RationalLocData A) :
    NonarchimedeanRing (presheafValue D) :=
  { is_nonarchimedean := (D.nonarchimedeanAddGroup_presheafValue).is_nonarchimedean }

/-- Completeness for the right uniformity, as an instance keyed at the
right-uniformity form — this is exactly the binder shape of the proven full-Huber
`hasLocLiftPowerBounded_huber_instance`, so `HasLocLiftPowerBounded (presheafValue D)`
now synthesizes noetherian-free. -/
instance presheafValue.instCompleteSpaceRight (D : RationalLocData A) :
    @CompleteSpace (presheafValue D)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D)) :=
  presheafValue_completeSpace_rightUniformSpace D

example [IsRingOfIntegralElements (A⁺ : Subring A)] (D : RationalLocData A) :
    HasLocLiftPowerBounded (presheafValue D) := inferInstance

/-! ### Restriction/canonical compatibility (noetherian-free) -/

section RestrictionCanonical

variable [HasLocLiftPowerBounded A] (D₀ : RationalLocData A) {E : RationalLocData A}
  (hE : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)

/-- The restriction map intertwines the canonical maps (noetherian-free restatement
of `restrictionMapHom_canonicalMap`, via `extensionHom_coe`). -/
theorem restriction_canonicalMap' (a : A) :
    restrictionMapHom D₀ E hE (D₀.canonicalMap a) = E.canonicalMap a := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  have hcoe : restrictionMapHom D₀ E hE
      (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a)) =
      restrictionMapAlg D₀ E hE (algebraMap A (Localization.Away D₀.s) a) :=
    UniformSpace.Completion.extensionHom_coe _ _ _
  calc restrictionMapHom D₀ E hE (D₀.canonicalMap a)
      = restrictionMapAlg D₀ E hE (algebraMap A (Localization.Away D₀.s) a) := hcoe
    _ = E.canonicalMap a :=
        IsLocalization.Away.lift_eq D₀.s
          (HasLocLiftPowerBounded.isUnit_canonicalMap_s D₀ E hE) a

end RestrictionCanonical

/-! ### The image datum over the section ring -/

section ImgDatum

variable [DecidableEq A]

/-- The span of the image parameters is the unit ideal. -/
theorem imgSpan (D₀ : RationalLocData A) {E : RationalLocData A}
    [DecidableEq (presheafValue D₀)]
    (hspanE : Ideal.span (E.T : Set A) = ⊤) :
    Ideal.span ((E.T.image D₀.canonicalMap : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤ := by
  rw [Finset.coe_image, ← Ideal.map_span, hspanE]
  exact Ideal.map_top _

/-- **The image rational datum over `B = 𝒪(D₀)`** of a valid `A`-datum `E`
(Wedhorn Remark 8.4's `R_B(can T / can s)`): parameters the canonical images,
openness by the span constructor. -/
def imgDatum (D₀ : RationalLocData A) (E : RationalLocData A)
    [DecidableEq (presheafValue D₀)]
    (hspanE : Ideal.span (E.T : Set A) = ⊤) : RationalLocData (presheafValue D₀) :=
  genPieceDatum (presheafValue_concretePair D₀) (E.T.image D₀.canonicalMap)
    (D₀.canonicalMap E.s) (imgSpan D₀ hspanE)

@[simp] theorem imgDatum_T (D₀ E : RationalLocData A) [DecidableEq (presheafValue D₀)]
    (hspanE : Ideal.span (E.T : Set A) = ⊤) :
    (imgDatum D₀ E hspanE).T = E.T.image D₀.canonicalMap := rfl

@[simp] theorem imgDatum_s (D₀ E : RationalLocData A) [DecidableEq (presheafValue D₀)]
    (hspanE : Ideal.span (E.T : Set A) = ⊤) :
    (imgDatum D₀ E hspanE).s = D₀.canonicalMap E.s := rfl

theorem imgDatum_isRational (D₀ E : RationalLocData A) [DecidableEq (presheafValue D₀)]
    (hspanE : Ideal.span (E.T : Set A) = ⊤) :
    (imgDatum D₀ E hspanE).IsRational :=
  RationalLocData.isRational_of_span_eq_top (imgSpan D₀ hspanE)

variable [HasLocLiftPowerBounded A]

/-- **Containment transfer** (through `Spa`-restriction): an `A⁺`-level containment
of rational opens transfers to the `B⁺`-level containment of the image opens.
This is what makes the `B`-side restriction maps between image data available. -/
theorem imgDatum_rationalOpen_subset (D₀ : RationalLocData A)
    {E E' : RationalLocData A} [DecidableEq (presheafValue D₀)]
    (hspanE : Ideal.span (E.T : Set A) = ⊤)
    (hspanE' : Ideal.span (E'.T : Set A) = ⊤)
    (hE'E : rationalOpen E'.T E'.s ⊆ rationalOpen E.T E.s) :
    rationalOpen (imgDatum D₀ E' hspanE').T (imgDatum D₀ E' hspanE').s ⊆
      rationalOpen (imgDatum D₀ E hspanE).T (imgDatum D₀ E hspanE).s := by
  intro w hw
  obtain ⟨hwSpa, hwT, hws⟩ := hw
  -- the restriction of `w` along the canonical map
  set v : Spv A := comap D₀.canonicalMap w with hvdef
  have hvSpa : v ∈ Spa A A⁺ :=
    comap_mem_spa (canonicalMap_continuous D₀) D₀.canonicalMap_integral hwSpa
  have hvE' : v ∈ rationalOpen E'.T E'.s := by
    refine ⟨hvSpa, fun t ht => ?_, fun h0 => ?_⟩
    · show w.vle (D₀.canonicalMap t) (D₀.canonicalMap E'.s)
      exact hwT _ (by
        rw [imgDatum_T]
        exact Finset.mem_image_of_mem _ ht)
    · refine hws ?_
      show w.vle (imgDatum D₀ E' hspanE').s 0
      have h0' : w.vle (D₀.canonicalMap E'.s) (D₀.canonicalMap 0) := h0
      rw [map_zero] at h0'
      exact h0'
  have hvE : v ∈ rationalOpen E.T E.s := hE'E hvE'
  refine ⟨hwSpa, fun b hb => ?_, fun h0 => ?_⟩
  · rw [imgDatum_T] at hb
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
    show w.vle (D₀.canonicalMap t) (D₀.canonicalMap E.s)
    exact hvE.2.1 t ht
  · refine hvE.2.2 ?_
    show w.vle (D₀.canonicalMap E.s) (D₀.canonicalMap 0)
    rw [map_zero]
    exact h0

end ImgDatum

/-! ### The keystone: `𝒪_A(E) ≃ 𝒪_B(imgDatum D₀ E)` -/

section Keystone

variable [DecidableEq A] [HasLocLiftPowerBounded A]
  [IsRingOfIntegralElements (A⁺ : Subring A)]

variable (D₀ : RationalLocData A) {E : RationalLocData A}
  [DecidableEq (presheafValue D₀)]
  (hspanE : Ideal.span (E.T : Set A) = ⊤)

/-- The composed canonical map `A → 𝒪_B(imgDatum D₀ E)`. -/
def imgCanonical : A →+* presheafValue (imgDatum D₀ E hspanE) :=
  ((imgDatum D₀ E hspanE).canonicalMap).comp D₀.canonicalMap

/-- `E.s` becomes a unit in the doubly-localized completion (it is the image
datum's own denominator, a unit in its own section ring). -/
theorem imgCanonical_isUnit_s : IsUnit ((imgCanonical D₀ hspanE) E.s) := by
  have := isUnit_canonicalMap_s (A := presheafValue D₀)
    (imgDatum D₀ E hspanE) (imgDatum D₀ E hspanE) subset_rfl
  rw [imgDatum_s] at this
  exact this

/-- The forward lift on the localization: `Localization.Away E.s → 𝒪_B(img E)`. -/
def keystoneAlg : Localization.Away E.s →+* presheafValue (imgDatum D₀ E hspanE) :=
  IsLocalization.Away.lift E.s (imgCanonical_isUnit_s D₀ hspanE)

theorem keystoneAlg_algebraMap (a : A) :
    keystoneAlg D₀ hspanE (algebraMap A (Localization.Away E.s) a) =
      (imgDatum D₀ E hspanE).canonicalMap (D₀.canonicalMap a) :=
  IsLocalization.Away.lift_eq E.s (imgCanonical_isUnit_s D₀ hspanE) a

/-- The forward lift sends the `t/s`-generators to the image datum's own
`t/s`-lifts (uniqueness of division by the unit `can E.s`). -/
theorem keystoneAlg_divByS {t : A} (ht : t ∈ E.T) :
    keystoneAlg D₀ hspanE (divByS t E.s) =
      IsLocalization.Away.lift (imgDatum D₀ E hspanE).s
        (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
        (divByS (D₀.canonicalMap t) (imgDatum D₀ E hspanE).s) := by
  refine (imgCanonical_isUnit_s D₀ hspanE).mul_left_cancel ?_
  have hspec : algebraMap A (Localization.Away E.s) E.s * divByS t E.s =
      algebraMap A (Localization.Away E.s) t := by
    unfold divByS
    exact IsLocalization.mk'_spec' (Localization.Away E.s) t
      (⟨E.s, ⟨1, pow_one E.s⟩⟩ : Submonoid.powers E.s)
  have hL : (imgCanonical D₀ hspanE) E.s * keystoneAlg D₀ hspanE (divByS t E.s) =
      (imgDatum D₀ E hspanE).canonicalMap (D₀.canonicalMap t) := by
    calc (imgCanonical D₀ hspanE) E.s * keystoneAlg D₀ hspanE (divByS t E.s)
        = keystoneAlg D₀ hspanE (algebraMap A (Localization.Away E.s) E.s) *
            keystoneAlg D₀ hspanE (divByS t E.s) := by
          rw [keystoneAlg_algebraMap]
          rfl
      _ = keystoneAlg D₀ hspanE
            (algebraMap A (Localization.Away E.s) E.s * divByS t E.s) :=
          (map_mul _ _ _).symm
      _ = keystoneAlg D₀ hspanE (algebraMap A (Localization.Away E.s) t) := by
          rw [hspec]
      _ = (imgDatum D₀ E hspanE).canonicalMap (D₀.canonicalMap t) :=
          keystoneAlg_algebraMap D₀ hspanE t
  have hspecB : algebraMap (presheafValue D₀)
        (Localization.Away (imgDatum D₀ E hspanE).s) (imgDatum D₀ E hspanE).s *
        divByS (D₀.canonicalMap t) (imgDatum D₀ E hspanE).s =
      algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s)
        (D₀.canonicalMap t) := by
    unfold divByS
    exact IsLocalization.mk'_spec' (Localization.Away (imgDatum D₀ E hspanE).s)
      (D₀.canonicalMap t)
      (⟨(imgDatum D₀ E hspanE).s, ⟨1, pow_one _⟩⟩ :
        Submonoid.powers (imgDatum D₀ E hspanE).s)
  have hR : (imgCanonical D₀ hspanE) E.s *
      IsLocalization.Away.lift (imgDatum D₀ E hspanE).s
        (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
        (divByS (D₀.canonicalMap t) (imgDatum D₀ E hspanE).s) =
      (imgDatum D₀ E hspanE).canonicalMap (D₀.canonicalMap t) := by
    calc (imgCanonical D₀ hspanE) E.s *
        IsLocalization.Away.lift (imgDatum D₀ E hspanE).s
          (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
          (divByS (D₀.canonicalMap t) (imgDatum D₀ E hspanE).s)
        = IsLocalization.Away.lift (imgDatum D₀ E hspanE).s
            (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
            (algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s)
              (imgDatum D₀ E hspanE).s) *
          IsLocalization.Away.lift (imgDatum D₀ E hspanE).s
            (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
            (divByS (D₀.canonicalMap t) (imgDatum D₀ E hspanE).s) := by
          rw [IsLocalization.Away.lift_eq _ _ (imgDatum D₀ E hspanE).s]
          rfl
      _ = IsLocalization.Away.lift (imgDatum D₀ E hspanE).s
            (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
            (algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s)
              (imgDatum D₀ E hspanE).s *
              divByS (D₀.canonicalMap t) (imgDatum D₀ E hspanE).s) :=
          (map_mul _ _ _).symm
      _ = IsLocalization.Away.lift (imgDatum D₀ E hspanE).s
            (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
            (algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s)
              (D₀.canonicalMap t)) := by
          rw [hspecB]
      _ = (imgDatum D₀ E hspanE).canonicalMap (D₀.canonicalMap t) :=
          IsLocalization.Away.lift_eq _ _ _
  rw [hL, hR]

/-- Continuity of the forward lift for the `E`-localization topology (through the
general engine `locTopology_continuous_lift`: the composed canonical map is
continuous, and the `t/s`-lifts are power-bounded by the `B`-level
`HasLocLiftPowerBounded` package at the reflexive containment). -/
theorem keystoneAlg_continuous :
    @Continuous _ _ E.topology _ (keystoneAlg D₀ hspanE) := by
  refine locTopology_continuous_lift E.P E.T E.s E.hopen _ ?_ ?_
  · -- continuity of `lift ∘ algebraMap = imgCanonical`
    have h_eq : (keystoneAlg D₀ hspanE).comp (algebraMap A (Localization.Away E.s)) =
        imgCanonical D₀ hspanE := by
      ext a
      exact keystoneAlg_algebraMap D₀ hspanE a
    rw [show ⇑((keystoneAlg D₀ hspanE).comp (algebraMap A (Localization.Away E.s)))
        = ⇑(imgCanonical D₀ hspanE) from congrArg _ h_eq]
    exact (canonicalMap_continuous (imgDatum D₀ E hspanE)).comp
      (canonicalMap_continuous D₀)
  · -- power-boundedness of the `t/s`-images
    intro t ht
    rw [keystoneAlg_divByS D₀ hspanE ht]
    exact @HasLocLiftPowerBounded.locLift_divByS_isPowerBounded (presheafValue D₀)
      _ _ _ (presheafValue.instIsHuberRing D₀) _
      (imgDatum D₀ E hspanE) (imgDatum D₀ E hspanE) (fun _ hv => hv)
      (D₀.canonicalMap t) (by
        rw [imgDatum_T]
        exact Finset.mem_image_of_mem _ ht)

/-- **The keystone, forward**: `𝒪_A(E) →+* 𝒪_B(imgDatum D₀ E)`. -/
def keystoneHom : presheafValue E →+* presheafValue (imgDatum D₀ E hspanE) := by
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  letI : IsTopologicalRing (Localization.Away E.s) := E.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away E.s) := E.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (keystoneAlg D₀ hspanE)
    (keystoneAlg_continuous D₀ hspanE)

theorem keystoneHom_coe (x : Localization.Away E.s) :
    keystoneHom D₀ hspanE
      (@UniformSpace.Completion.coeRingHom _ _ E.uniformSpace
        E.isTopologicalRing E.isUniformAddGroup x) = keystoneAlg D₀ hspanE x := by
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  letI : IsTopologicalRing (Localization.Away E.s) := E.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away E.s) := E.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe _ _ x

theorem keystoneHom_continuous : Continuous (keystoneHom D₀ hspanE) := by
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-- The keystone intertwines the canonical maps. -/
theorem keystoneHom_canonicalMap (a : A) :
    keystoneHom D₀ hspanE (E.canonicalMap a) =
      (imgDatum D₀ E hspanE).canonicalMap (D₀.canonicalMap a) := by
  have := keystoneHom_coe D₀ hspanE (algebraMap A (Localization.Away E.s) a)
  rw [keystoneAlg_algebraMap] at this
  exact this

end Keystone

/-! ### The keystone, backward direction and round trips -/

section KeystoneInv

variable [DecidableEq A] [HasLocLiftPowerBounded A]
  [IsRingOfIntegralElements (A⁺ : Subring A)]

variable (D₀ : RationalLocData A) {E : RationalLocData A}
  [DecidableEq (presheafValue D₀)]
  (hspanE : Ideal.span (E.T : Set A) = ⊤)
  (hE : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)

/-- `imgDatum`'s denominator maps to a unit under the restriction map. -/
theorem restriction_isUnit_imgS :
    IsUnit ((restrictionMapHom D₀ E hE) (imgDatum D₀ E hspanE).s) := by
  rw [imgDatum_s, restriction_canonicalMap' D₀ hE]
  exact isUnit_canonicalMap_s E E (fun _ hv => hv)

/-- The backward lift on the `B`-localization. -/
def keystoneInvAlg :
    Localization.Away (imgDatum D₀ E hspanE).s →+* presheafValue E :=
  IsLocalization.Away.lift (imgDatum D₀ E hspanE).s
    (restriction_isUnit_imgS D₀ hspanE hE)

theorem keystoneInvAlg_algebraMap (b : presheafValue D₀) :
    keystoneInvAlg D₀ hspanE hE
      (algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s) b) =
      restrictionMapHom D₀ E hE b :=
  IsLocalization.Away.lift_eq (imgDatum D₀ E hspanE).s
    (restriction_isUnit_imgS D₀ hspanE hE) b

/-- The backward lift sends the image `t/s`-generators to the `A`-side `t/s`-lifts. -/
theorem keystoneInvAlg_divByS {t : A} (ht : t ∈ E.T) :
    keystoneInvAlg D₀ hspanE hE
      (divByS (D₀.canonicalMap t) (imgDatum D₀ E hspanE).s) =
      IsLocalization.Away.lift E.s
        (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
        (divByS t E.s) := by
  refine (restriction_isUnit_imgS D₀ hspanE hE).mul_left_cancel ?_
  have hspecB : algebraMap (presheafValue D₀)
        (Localization.Away (imgDatum D₀ E hspanE).s) (imgDatum D₀ E hspanE).s *
        divByS (D₀.canonicalMap t) (imgDatum D₀ E hspanE).s =
      algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s)
        (D₀.canonicalMap t) := by
    unfold divByS
    exact IsLocalization.mk'_spec' _ (D₀.canonicalMap t)
      (⟨(imgDatum D₀ E hspanE).s, ⟨1, pow_one _⟩⟩ :
        Submonoid.powers (imgDatum D₀ E hspanE).s)
  have hspecA : algebraMap A (Localization.Away E.s) E.s * divByS t E.s =
      algebraMap A (Localization.Away E.s) t := by
    unfold divByS
    exact IsLocalization.mk'_spec' (Localization.Away E.s) t
      (⟨E.s, ⟨1, pow_one E.s⟩⟩ : Submonoid.powers E.s)
  have hL : (restrictionMapHom D₀ E hE) (imgDatum D₀ E hspanE).s *
      keystoneInvAlg D₀ hspanE hE
        (divByS (D₀.canonicalMap t) (imgDatum D₀ E hspanE).s) =
      E.canonicalMap t := by
    calc (restrictionMapHom D₀ E hE) (imgDatum D₀ E hspanE).s *
        keystoneInvAlg D₀ hspanE hE
          (divByS (D₀.canonicalMap t) (imgDatum D₀ E hspanE).s)
        = keystoneInvAlg D₀ hspanE hE
            (algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s)
              (imgDatum D₀ E hspanE).s *
              divByS (D₀.canonicalMap t) (imgDatum D₀ E hspanE).s) := by
          rw [map_mul, keystoneInvAlg_algebraMap]
      _ = keystoneInvAlg D₀ hspanE hE
            (algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s)
              (D₀.canonicalMap t)) := by rw [hspecB]
      _ = restrictionMapHom D₀ E hE (D₀.canonicalMap t) :=
          keystoneInvAlg_algebraMap D₀ hspanE hE _
      _ = E.canonicalMap t := restriction_canonicalMap' D₀ hE t
  have hR : (restrictionMapHom D₀ E hE) (imgDatum D₀ E hspanE).s *
      IsLocalization.Away.lift E.s
        (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
        (divByS t E.s) =
      E.canonicalMap t := by
    have hs' : (restrictionMapHom D₀ E hE) (imgDatum D₀ E hspanE).s =
        E.canonicalMap E.s := by
      rw [imgDatum_s]
      exact restriction_canonicalMap' D₀ hE E.s
    calc (restrictionMapHom D₀ E hE) (imgDatum D₀ E hspanE).s *
        IsLocalization.Away.lift E.s
          (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
          (divByS t E.s)
        = IsLocalization.Away.lift E.s
            (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
            (algebraMap A (Localization.Away E.s) E.s) *
          IsLocalization.Away.lift E.s
            (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
            (divByS t E.s) := by
          rw [IsLocalization.Away.lift_eq, hs']
      _ = IsLocalization.Away.lift E.s
            (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
            (algebraMap A (Localization.Away E.s) E.s * divByS t E.s) :=
          (map_mul _ _ _).symm
      _ = IsLocalization.Away.lift E.s
            (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
            (algebraMap A (Localization.Away E.s) t) := by rw [hspecA]
      _ = E.canonicalMap t := IsLocalization.Away.lift_eq E.s _ t
  rw [hL, hR]

/-- Continuity of the backward lift for the image localization topology over `B`. -/
theorem keystoneInvAlg_continuous :
    @Continuous _ _ (imgDatum D₀ E hspanE).topology _ (keystoneInvAlg D₀ hspanE hE) := by
  refine locTopology_continuous_lift (imgDatum D₀ E hspanE).P (imgDatum D₀ E hspanE).T
    (imgDatum D₀ E hspanE).s (imgDatum D₀ E hspanE).hopen _ ?_ ?_
  · have h_eq : (keystoneInvAlg D₀ hspanE hE).comp
        (algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s)) =
        restrictionMapHom D₀ E hE := by
      ext b
      exact keystoneInvAlg_algebraMap D₀ hspanE hE b
    rw [show ⇑((keystoneInvAlg D₀ hspanE hE).comp
        (algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s)))
        = ⇑(restrictionMapHom D₀ E hE) from congrArg _ h_eq]
    exact restrictionMapHom_continuous D₀ E hE
  · intro b hb
    rw [imgDatum_T] at hb
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
    rw [keystoneInvAlg_divByS D₀ hspanE hE ht]
    exact @HasLocLiftPowerBounded.locLift_divByS_isPowerBounded A
      _ _ _ _ _ E E (fun _ hv => hv) t ht

/-- **The keystone, backward**: `𝒪_B(imgDatum D₀ E) →+* 𝒪_A(E)`. -/
def keystoneInv : presheafValue (imgDatum D₀ E hspanE) →+* presheafValue E := by
  letI : UniformSpace (Localization.Away (imgDatum D₀ E hspanE).s) :=
    (imgDatum D₀ E hspanE).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imgDatum D₀ E hspanE).s) :=
    (imgDatum D₀ E hspanE).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imgDatum D₀ E hspanE).s) :=
    (imgDatum D₀ E hspanE).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (keystoneInvAlg D₀ hspanE hE)
    (keystoneInvAlg_continuous D₀ hspanE hE)

theorem keystoneInv_coe (x : Localization.Away (imgDatum D₀ E hspanE).s) :
    keystoneInv D₀ hspanE hE
      (@UniformSpace.Completion.coeRingHom _ _ (imgDatum D₀ E hspanE).uniformSpace
        (imgDatum D₀ E hspanE).isTopologicalRing
        (imgDatum D₀ E hspanE).isUniformAddGroup x) =
      keystoneInvAlg D₀ hspanE hE x := by
  letI : UniformSpace (Localization.Away (imgDatum D₀ E hspanE).s) :=
    (imgDatum D₀ E hspanE).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imgDatum D₀ E hspanE).s) :=
    (imgDatum D₀ E hspanE).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imgDatum D₀ E hspanE).s) :=
    (imgDatum D₀ E hspanE).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe _ _ x

theorem keystoneInv_continuous : Continuous (keystoneInv D₀ hspanE hE) := by
  letI : UniformSpace (Localization.Away (imgDatum D₀ E hspanE).s) :=
    (imgDatum D₀ E hspanE).uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-- The backward keystone intertwines the `B`-canonical map with the restriction. -/
theorem keystoneInv_canonicalMap (b : presheafValue D₀) :
    keystoneInv D₀ hspanE hE ((imgDatum D₀ E hspanE).canonicalMap b) =
      restrictionMapHom D₀ E hE b := by
  have := keystoneInv_coe D₀ hspanE hE
    (algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s) b)
  rw [keystoneInvAlg_algebraMap] at this
  exact this

end KeystoneInv

/-! ### Round trips and the bundled keystone -/

section KeystoneRoundtrip

variable [DecidableEq A] [HasLocLiftPowerBounded A]
  [IsRingOfIntegralElements (A⁺ : Subring A)]

variable (D₀ : RationalLocData A) {E : RationalLocData A}
  [DecidableEq (presheafValue D₀)]
  (hspanE : Ideal.span (E.T : Set A) = ⊤)
  (hE : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)

/-- **The base square**: the forward keystone turns the `A`-side restriction map
into the `B`-side canonical map. (Two continuous maps out of `B`, agreeing on the
dense image of the `D₀`-localization, which in turn is checked on the image of `A`
by `IsLocalization.ringHom_ext`.) -/
theorem keystoneHom_restriction (b : presheafValue D₀) :
    keystoneHom D₀ hspanE (restrictionMapHom D₀ E hE b) =
      (imgDatum D₀ E hspanE).canonicalMap b := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  -- ring-hom equality on the `D₀`-localization
  have hloc : ((keystoneHom D₀ hspanE).comp (restrictionMapHom D₀ E hE)).comp
      D₀.coeRingHom =
      ((imgDatum D₀ E hspanE).canonicalMap).comp D₀.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D₀.s) ?_
    ext a
    have h₁ : restrictionMapHom D₀ E hE
        (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a)) =
        E.canonicalMap a := restriction_canonicalMap' D₀ hE a
    show keystoneHom D₀ hspanE (restrictionMapHom D₀ E hE
      (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a))) =
      (imgDatum D₀ E hspanE).canonicalMap
        (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a))
    rw [h₁, keystoneHom_canonicalMap]
    rfl
  -- extend by density and continuity
  have hdense : DenseRange (⇑(D₀.coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _ D₀.uniformSpace
  have hfun : ⇑(keystoneHom D₀ hspanE) ∘ ⇑(restrictionMapHom D₀ E hE) =
      ⇑((imgDatum D₀ E hspanE).canonicalMap) := by
    refine hdense.equalizer ?_ ?_ ?_
    · exact (keystoneHom_continuous D₀ hspanE).comp
        (restrictionMapHom_continuous D₀ E hE)
    · exact canonicalMap_continuous (imgDatum D₀ E hspanE)
    · funext x
      exact DFunLike.congr_fun hloc x
  exact congr_fun hfun b

/-- Round trip on `𝒪_A(E)`. -/
theorem keystoneInv_keystoneHom (x : presheafValue E) :
    keystoneInv D₀ hspanE hE (keystoneHom D₀ hspanE x) = x := by
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  letI : IsTopologicalRing (Localization.Away E.s) := E.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away E.s) := E.isUniformAddGroup
  have hloc : ((keystoneInv D₀ hspanE hE).comp (keystoneAlg D₀ hspanE)) =
      E.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers E.s) ?_
    ext a
    show keystoneInv D₀ hspanE hE
      (keystoneAlg D₀ hspanE (algebraMap A (Localization.Away E.s) a)) =
      E.coeRingHom (algebraMap A (Localization.Away E.s) a)
    rw [keystoneAlg_algebraMap, keystoneInv_canonicalMap,
      restriction_canonicalMap' D₀ hE]
    rfl
  have hdense : DenseRange (⇑(E.coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _ E.uniformSpace
  have hfun : ⇑(keystoneInv D₀ hspanE hE) ∘ ⇑(keystoneHom D₀ hspanE) =
      (id : presheafValue E → presheafValue E) := by
    refine hdense.equalizer ?_ continuous_id ?_
    · exact (keystoneInv_continuous D₀ hspanE hE).comp
        (keystoneHom_continuous D₀ hspanE)
    · funext l
      show keystoneInv D₀ hspanE hE (keystoneHom D₀ hspanE (E.coeRingHom l)) =
        E.coeRingHom l
      have h1 : keystoneHom D₀ hspanE (E.coeRingHom l) = keystoneAlg D₀ hspanE l :=
        keystoneHom_coe D₀ hspanE l
      rw [h1]
      exact DFunLike.congr_fun hloc l
  exact congr_fun hfun x

/-- Round trip on `𝒪_B(imgDatum D₀ E)`. -/
theorem keystoneHom_keystoneInv (y : presheafValue (imgDatum D₀ E hspanE)) :
    keystoneHom D₀ hspanE (keystoneInv D₀ hspanE hE y) = y := by
  letI : UniformSpace (Localization.Away (imgDatum D₀ E hspanE).s) :=
    (imgDatum D₀ E hspanE).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imgDatum D₀ E hspanE).s) :=
    (imgDatum D₀ E hspanE).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imgDatum D₀ E hspanE).s) :=
    (imgDatum D₀ E hspanE).isUniformAddGroup
  have hloc : ((keystoneHom D₀ hspanE).comp (keystoneInvAlg D₀ hspanE hE)) =
      (imgDatum D₀ E hspanE).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (imgDatum D₀ E hspanE).s) ?_
    ext b
    show keystoneHom D₀ hspanE (keystoneInvAlg D₀ hspanE hE
      (algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s) b)) =
      (imgDatum D₀ E hspanE).coeRingHom
        (algebraMap (presheafValue D₀) (Localization.Away (imgDatum D₀ E hspanE).s) b)
    rw [keystoneInvAlg_algebraMap, keystoneHom_restriction]
    rfl
  have hdense : DenseRange (⇑((imgDatum D₀ E hspanE).coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _ (imgDatum D₀ E hspanE).uniformSpace
  have hfun : ⇑(keystoneHom D₀ hspanE) ∘ ⇑(keystoneInv D₀ hspanE hE) =
      (id : presheafValue (imgDatum D₀ E hspanE) → presheafValue (imgDatum D₀ E hspanE)) := by
    refine hdense.equalizer ?_ continuous_id ?_
    · exact (keystoneHom_continuous D₀ hspanE).comp
        (keystoneInv_continuous D₀ hspanE hE)
    · funext l
      show keystoneHom D₀ hspanE (keystoneInv D₀ hspanE hE
        ((imgDatum D₀ E hspanE).coeRingHom l)) = (imgDatum D₀ E hspanE).coeRingHom l
      have h1 : keystoneInv D₀ hspanE hE ((imgDatum D₀ E hspanE).coeRingHom l) =
          keystoneInvAlg D₀ hspanE hE l := keystoneInv_coe D₀ hspanE hE l
      rw [h1]
      exact DFunLike.congr_fun hloc l
  exact congr_fun hfun y

/-- **The noetherian-free keystone** (Wedhorn Lemma 8.1 / Prop 8.2(2) / Remark 8.4): the section
ring of a rational piece over `A` is canonically the section ring of its image
datum over `B = 𝒪(D₀)`, as topological rings
(`keystoneHom_continuous`/`keystoneInv_continuous`), compatibly with the canonical
maps (`keystoneHom_canonicalMap`) and the restriction maps
(`keystoneHom_restriction`). -/
def keystone : presheafValue E ≃+* presheafValue (imgDatum D₀ E hspanE) where
  toFun := keystoneHom D₀ hspanE
  invFun := keystoneInv D₀ hspanE hE
  left_inv := keystoneInv_keystoneHom D₀ hspanE hE
  right_inv := keystoneHom_keystoneInv D₀ hspanE hE
  map_mul' := map_mul _
  map_add' := map_add _

end KeystoneRoundtrip

/-! ### The keystone restriction squares -/

section KeystoneSquares

variable [DecidableEq A] [HasLocLiftPowerBounded A]
  [IsRingOfIntegralElements (A⁺ : Subring A)]

variable (D₀ : RationalLocData A) {E E' : RationalLocData A}
  [DecidableEq (presheafValue D₀)]
  (hspanE : Ideal.span (E.T : Set A) = ⊤)
  (hspanE' : Ideal.span (E'.T : Set A) = ⊤)
  (hE'E : rationalOpen E'.T E'.s ⊆ rationalOpen E.T E.s)

/-- **The keystone square**: the forward keystones intertwine the `A`-side and
`B`-side restriction maps between pieces. (Both composites are continuous maps out
of `𝒪_A(E)`; they agree on the canonical image of `A`, hence on the dense image of
the `E`-localization, hence everywhere.) -/
theorem keystone_restriction_square (x : presheafValue E) :
    keystoneHom D₀ hspanE' (restrictionMap E E' hE'E x) =
      restrictionMap (imgDatum D₀ E hspanE) (imgDatum D₀ E' hspanE')
        (imgDatum_rationalOpen_subset D₀ hspanE hspanE' hE'E)
        (keystoneHom D₀ hspanE x) := by
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  letI : IsTopologicalRing (Localization.Away E.s) := E.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away E.s) := E.isUniformAddGroup
  -- ring-hom equality on the `E`-localization: both routes send `algebraMap a` to
  -- the doubly-canonical image of `a`
  have hloc : ((keystoneHom D₀ hspanE').comp (restrictionMapHom E E' hE'E)).comp
      E.coeRingHom =
      ((restrictionMapHom (imgDatum D₀ E hspanE) (imgDatum D₀ E' hspanE')
          (imgDatum_rationalOpen_subset D₀ hspanE hspanE' hE'E)).comp
        (keystoneHom D₀ hspanE)).comp E.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers E.s) ?_
    ext a
    have h₁ : restrictionMapHom E E' hE'E (E.canonicalMap a) = E'.canonicalMap a :=
      restriction_canonicalMap' E hE'E a
    have h₂ : restrictionMapHom (imgDatum D₀ E hspanE) (imgDatum D₀ E' hspanE')
        (imgDatum_rationalOpen_subset D₀ hspanE hspanE' hE'E)
        ((imgDatum D₀ E hspanE).canonicalMap (D₀.canonicalMap a)) =
        (imgDatum D₀ E' hspanE').canonicalMap (D₀.canonicalMap a) :=
      restriction_canonicalMap' (A := presheafValue D₀) (imgDatum D₀ E hspanE)
        (imgDatum_rationalOpen_subset D₀ hspanE hspanE' hE'E) (D₀.canonicalMap a)
    show keystoneHom D₀ hspanE' (restrictionMapHom E E' hE'E
        (E.coeRingHom (algebraMap A (Localization.Away E.s) a))) =
      restrictionMapHom (imgDatum D₀ E hspanE) (imgDatum D₀ E' hspanE')
        (imgDatum_rationalOpen_subset D₀ hspanE hspanE' hE'E)
        (keystoneHom D₀ hspanE
          (E.coeRingHom (algebraMap A (Localization.Away E.s) a)))
    have hcanE : E.coeRingHom (algebraMap A (Localization.Away E.s) a) =
        E.canonicalMap a := rfl
    rw [hcanE, h₁, keystoneHom_canonicalMap, keystoneHom_canonicalMap, h₂]
  have hdense : DenseRange (⇑(E.coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _ E.uniformSpace
  have hfun : ⇑(keystoneHom D₀ hspanE') ∘ ⇑(restrictionMapHom E E' hE'E) =
      ⇑(restrictionMapHom (imgDatum D₀ E hspanE) (imgDatum D₀ E' hspanE')
          (imgDatum_rationalOpen_subset D₀ hspanE hspanE' hE'E)) ∘
        ⇑(keystoneHom D₀ hspanE) := by
    refine hdense.equalizer ?_ ?_ ?_
    · exact (keystoneHom_continuous D₀ hspanE').comp
        (restrictionMapHom_continuous E E' hE'E)
    · exact (restrictionMapHom_continuous (imgDatum D₀ E hspanE)
        (imgDatum D₀ E' hspanE')
        (imgDatum_rationalOpen_subset D₀ hspanE hspanE' hE'E)).comp
        (keystoneHom_continuous D₀ hspanE)
    · funext l
      exact DFunLike.congr_fun hloc l
  exact congr_fun hfun x

end KeystoneSquares

end ValuationSpectrum
