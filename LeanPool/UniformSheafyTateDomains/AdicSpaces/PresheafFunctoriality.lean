/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf

/-!
# Covariant functoriality of the presheaf value along a continuous ring hom

For a continuous ring homomorphism `φ : R →+* S` and rational localization data
`D` of `R`, `D'` of `S` with matching denominator (`D'.s = φ D.s`) and numerator
containment (`φ '' D.T ⊆ D'.T`), the completed rational localization is covariantly
functorial:

* `locMapOfHom` — the localization-level map `Rₛ →+* S_{s'}` (`IsLocalization.map`);
* `pushMapAlg` — its composition into the completion `𝒪(D')`;
* `presheafValueMapOfHom : 𝒪(D) →+* 𝒪(D')` — the completed covariant map, with
  `_continuous`, `_coe`, and `_canonicalMap` (naturality on `R`).

This is the ring-hom generalization of the noetherian-free keystone
(`RelativeDescent.lean`, the same-ring image-datum case). It was previously
stranded inside `namespace FiniteJet` (`FJP/FiniteJetFunctoriality.lean`); it is
generic (no jet structure) and used here by the ring-equivalence presheaf
transport (`RingEquivPresheafTransport.lean`, PASS 2) and re-used by FJP.

## Reference

[FJP] Lemma 5.1; the localization-topology continuity engine
(`locTopology_continuous_lift`) and completion functoriality
(`UniformSpace.Completion.extensionHom`).
-/

noncomputable section

open Filter Topology

namespace ValuationSpectrum

/-- **Restriction fixes the canonical images** (Wedhorn Proposition 8.2(1),
naturality on `A`): `restrictionMapHom D D' h ∘ D.canonicalMap = D'.canonicalMap`.
Single-ring, minimal hypotheses (only `[HasLocLiftPowerBounded A]` beyond the Huber
structure); the previously-used copies (`IteratedRational.restrictionMapHom_canonicalMap`,
which was overscoped with `[IsTateRing]…[NonarchimedeanRing]`, and the private FJP
`restrictionMapHom_canonicalMap'`) route through this. -/
theorem restrictionMapHom_canonicalMap_generic {A : Type*} [CommRing A]
    [TopologicalSpace A] [PlusSubring A] [IsHuberRing A]
    [HasLocLiftPowerBounded A] (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) (a : A) :
    restrictionMapHom D D' h (D.canonicalMap a) = D'.canonicalMap a := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  have h_ext :
      restrictionMapHom D D' h
        (D.coeRingHom (algebraMap A (Localization.Away D.s) a)) =
      restrictionMapAlg D D' h (algebraMap A (Localization.Away D.s) a) :=
    UniformSpace.Completion.extensionHom_coe (restrictionMapAlg D D' h)
      (restrictionMapAlg_continuous D D' h)
      (algebraMap A (Localization.Away D.s) a)
  rw [show D.canonicalMap a =
    D.coeRingHom (algebraMap A (Localization.Away D.s) a) from rfl]
  rw [h_ext, restrictionMapAlg, IsLocalization.Away.lift_eq]

/-- **Transport along a datum equality is restriction** (the cast-elimination
identity; `subst`-provable because the target is free): rewriting a completed
section along `E₁ = E₂` agrees with the restriction map for the induced
(equality-derived) containment. Extracted from FJP (T0, 2026-07-21) — it is fully
generic and is the standard tool for eliminating `▸`-casts between
propositionally equal presheaf values. -/
theorem restrictionMap_cast {A : Type*} [CommRing A] [TopologicalSpace A]
    [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
    (E₁ E₂ : RationalLocData A) (heq : E₁ = E₂) (v : presheafValue E₁) :
    heq ▸ v = restrictionMap E₁ E₂ (by rw [heq]) v := by
  subst heq
  exact (congrFun (restrictionMap_id E₁) v).symm

section CovariantPush

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

/-- The localization-level covariant map of a pushed rational datum. -/
noncomputable def locMapOfHom (φ : R →+* S) (D : RationalLocData R)
    (D' : RationalLocData S) (hs : D'.s = φ D.s) :
    Localization.Away D.s →+* Localization.Away D'.s :=
  IsLocalization.map (Localization.Away D'.s) φ
    (show Submonoid.powers D.s ≤ (Submonoid.powers D'.s).comap φ from
      Submonoid.powers_le.mpr (show φ D.s ∈ Submonoid.powers D'.s from
        ⟨1, by show D'.s ^ 1 = φ D.s; rw [pow_one, hs]⟩))

theorem locMapOfHom_algebraMap (φ : R →+* S) (D : RationalLocData R)
    (D' : RationalLocData S) (hs : D'.s = φ D.s) (a : R) :
    locMapOfHom φ D D' hs (algebraMap R (Localization.Away D.s) a) =
      algebraMap S (Localization.Away D'.s) (φ a) := by
  unfold locMapOfHom
  rw [IsLocalization.map_eq]

theorem locMapOfHom_divByS (φ : R →+* S) (D : RationalLocData R)
    (D' : RationalLocData S) (hs : D'.s = φ D.s) (t : R) :
    locMapOfHom φ D D' hs (divByS t D.s) = divByS (φ t) D'.s := by
  rw [divByS, divByS, locMapOfHom, IsLocalization.map_mk']
  exact congrArg _ (Subtype.ext hs.symm)

/-- Continuity of the localization-level covariant map (universal property of the
localization topology; the pushed generators are in `locSubring D'`, hence
power-bounded). -/
theorem locMapOfHom_continuous (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) :
    @Continuous _ _ D.topology D'.topology (locMapOfHom φ D D' hs) := by
  letI := D'.topology
  haveI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  haveI : @NonarchimedeanRing _ _ D'.topology :=
    (locBasis D'.P D'.T D'.s D'.hopen).nonarchimedean
  have hf_alg : @Continuous _ _ _ D'.topology
      ((locMapOfHom φ D D' hs).comp (algebraMap R (Localization.Away D.s))) := by
    have h_eq : (locMapOfHom φ D D' hs).comp (algebraMap R (Localization.Away D.s)) =
        (algebraMap S (Localization.Away D'.s)).comp φ := by
      ext a; exact locMapOfHom_algebraMap φ D D' hs a
    rw [show ⇑((locMapOfHom φ D D' hs).comp (algebraMap R (Localization.Away D.s)))
        = ⇑((algebraMap S (Localization.Away D'.s)).comp φ) from congrArg _ h_eq,
      RingHom.coe_comp]
    refine Continuous.comp ?_ hφ
    -- `algebraMap S (Localization.Away D'.s)` is continuous into `D'.topology`
    -- (inlined from `algebraMap_continuous_loc`, avoiding its nonarchimedean variable).
    apply continuous_of_continuousAt_zero
      (algebraMap S (Localization.Away D'.s)).toAddMonoidHom
    rw [ContinuousAt, map_zero, Filter.tendsto_def]
    intro U hU
    obtain ⟨n, -, hn⟩ :=
      (locBasis D'.P D'.T D'.s D'.hopen).hasBasis_nhds_zero.mem_iff.mp hU
    apply Filter.mem_of_superset (D'.P.hasBasis_nhds_zero.mem_of_mem (i := n) trivial)
    intro a ha
    obtain ⟨⟨b, hb⟩, hbn, hab⟩ := ha
    rw [← hab]
    exact hn ⟨algebraMapD D'.P D'.T D'.s ⟨b, hb⟩,
      by rw [locIdeal, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hbn, rfl⟩
  refine locTopology_continuous_lift D.P D.T D.s D.hopen _ hf_alg fun t ht => ?_
  rw [locMapOfHom_divByS]
  exact (locSubring_isBounded_of_pair D'.P D'.T D'.s D'.hopen).isPowerBounded_of_mem
    (divByS_mem_locSubring D'.P D'.T D'.s (hT t ht))

/-- The covariant map into the completion (algebraic side). -/
noncomputable def pushMapAlg (φ : R →+* S) (D : RationalLocData R)
    (D' : RationalLocData S) (hs : D'.s = φ D.s) :
    Localization.Away D.s →+* presheafValue D' :=
  D'.coeRingHom.comp (locMapOfHom φ D D' hs)

theorem pushMapAlg_continuous (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) :
    @Continuous _ _ D.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      (pushMapAlg φ D D' hs) := by
  letI := D.topology
  letI := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  have hcoe : @Continuous _ _ D'.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      D'.coeRingHom :=
    @UniformSpace.Completion.continuous_coe _ D'.uniformSpace
  exact hcoe.comp (locMapOfHom_continuous φ hφ D D' hs hT)

/-- The covariant presheaf-value map `𝒪(D) →+* 𝒪(D')` along `φ` ([FJP] Lemma 5.1). -/
noncomputable def presheafValueMapOfHom (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) :
    presheafValue D →+* presheafValue D' := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (pushMapAlg φ D D' hs)
    (pushMapAlg_continuous φ hφ D D' hs hT)

theorem presheafValueMapOfHom_continuous (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) :
    Continuous (presheafValueMapOfHom φ hφ D D' hs hT) := by
  letI := D.uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-- The covariant map agrees with the algebraic map on the dense image. -/
theorem presheafValueMapOfHom_coe (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) (a : Localization.Away D.s) :
    presheafValueMapOfHom φ hφ D D' hs hT
      (@UniformSpace.Completion.coeRingHom _ _ D.uniformSpace
        D.isTopologicalRing D.isUniformAddGroup a) =
      pushMapAlg φ D D' hs a := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (pushMapAlg φ D D' hs)
    (pushMapAlg_continuous φ hφ D D' hs hT) a

/-- The covariant map intertwines the canonical maps ([FJP] Lemma 5.1 naturality on `A`). -/
theorem presheafValueMapOfHom_canonicalMap (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) (a : R) :
    presheafValueMapOfHom φ hφ D D' hs hT (D.canonicalMap a) =
      D'.canonicalMap (φ a) := by
  have h1 : presheafValueMapOfHom φ hφ D D' hs hT (D.canonicalMap a) =
      pushMapAlg φ D D' hs (algebraMap R (Localization.Away D.s) a) :=
    presheafValueMapOfHom_coe φ hφ D D' hs hT (algebraMap R (Localization.Away D.s) a)
  rw [h1]
  show D'.coeRingHom (locMapOfHom φ D D' hs (algebraMap R (Localization.Away D.s) a)) = _
  rw [locMapOfHom_algebraMap]
  rfl

end CovariantPush

/-- **Generic restriction-naturality of the covariant map** (Wedhorn Prop 8.2(1) /
[FJP] Lemma 4.6+5.1): the completed covariant map commutes with restriction. The
`R`- and `S`-side need `[HasLocLiftPowerBounded]` (so `restrictionMap` is defined);
no noetherian/T2 hypotheses. -/
theorem presheafValueMapOfHom_restriction
    {R S : Type*} [CommRing R] [TopologicalSpace R]
    [PlusSubring R] [IsHuberRing R] [HasLocLiftPowerBounded R]
    [CommRing S] [TopologicalSpace S]
    [PlusSubring S] [IsHuberRing S] [HasLocLiftPowerBounded S]
    (φ : R →+* S) (hφ : Continuous φ)
    (D D' : RationalLocData R) (E E' : RationalLocData S)
    (hs : E.s = φ D.s) (hT : ∀ t ∈ D.T, φ t ∈ E.T)
    (hs' : E'.s = φ D'.s) (hT' : ∀ t ∈ D'.T, φ t ∈ E'.T)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hpush : rationalOpen E'.T E'.s ⊆ rationalOpen E.T E.s) (x : presheafValue D) :
    presheafValueMapOfHom φ hφ D' E' hs' hT' (restrictionMap D D' h x) =
      restrictionMap E E' hpush (presheafValueMapOfHom φ hφ D E hs hT x) := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI : RegularSpace (presheafValue E') := UniformSpace.to_regularSpace
  have hcomp : ((presheafValueMapOfHom φ hφ D' E' hs' hT').comp
      (restrictionMapHom D D' h)).comp D.coeRingHom =
      ((restrictionMapHom E E' hpush).comp
        (presheafValueMapOfHom φ hφ D E hs hT)).comp D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [show D.coeRingHom (algebraMap R (Localization.Away D.s) a) =
        D.canonicalMap a from rfl,
      restrictionMapHom_canonicalMap_generic D D' h,
      presheafValueMapOfHom_canonicalMap φ hφ D' E' hs' hT' a,
      presheafValueMapOfHom_canonicalMap φ hφ D E hs hT a,
      restrictionMapHom_canonicalMap_generic E E' hpush]
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => presheafValueMapOfHom φ hφ D' E' hs' hT'
      (restrictionMapHom D D' h y)) =
      fun y => restrictionMapHom E E' hpush (presheafValueMapOfHom φ hφ D E hs hT y) :=
    hdense.equalizer
      ((presheafValueMapOfHom_continuous φ hφ D' E' hs' hT').comp
        (restrictionMapHom_continuous D D' h))
      ((restrictionMapHom_continuous _ _ hpush).comp
        (presheafValueMapOfHom_continuous φ hφ D E hs hT))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq x

/-- **Value-map composition along a commuting triangle of ring homs** ([FJP] (4.9),
generically): if `ψ ∘ φ = χ` at the ring level, then the completed covariant value
maps compose accordingly on any matching data. Both composites of a commuting
square of Huber rings therefore agree on sections — the generic `row_comm` engine
for Milnor-square instantiations. Dense-equalizer proof (the
`mapBD_mapB_eq_mapCD_mapC` pattern, made generic). -/
theorem presheafValueMapOfHom_comp
    {R S T : Type*} [CommRing R] [TopologicalSpace R]
    [PlusSubring R] [IsHuberRing R] [HasLocLiftPowerBounded R]
    [CommRing S] [TopologicalSpace S]
    [PlusSubring S] [IsHuberRing S] [HasLocLiftPowerBounded S]
    [CommRing T] [TopologicalSpace T]
    [PlusSubring T] [IsHuberRing T] [HasLocLiftPowerBounded T]
    (φ : R →+* S) (hφ : Continuous φ) (ψ : S →+* T) (hψ : Continuous ψ)
    (χ : R →+* T) (hχ : Continuous χ) (hcomm : ψ.comp φ = χ)
    (D : RationalLocData R) (E : RationalLocData S) (G : RationalLocData T)
    (hsE : E.s = φ D.s) (hTE : ∀ t ∈ D.T, φ t ∈ E.T)
    (hsG : G.s = ψ E.s) (hTG : ∀ t ∈ E.T, ψ t ∈ G.T)
    (hsG' : G.s = χ D.s) (hTG' : ∀ t ∈ D.T, χ t ∈ G.T)
    (x : presheafValue D) :
    presheafValueMapOfHom ψ hψ E G hsG hTG
        (presheafValueMapOfHom φ hφ D E hsE hTE x) =
      presheafValueMapOfHom χ hχ D G hsG' hTG' x := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI : RegularSpace (presheafValue G) := UniformSpace.to_regularSpace
  have hcompeq : ((presheafValueMapOfHom ψ hψ E G hsG hTG).comp
      (presheafValueMapOfHom φ hφ D E hsE hTE)).comp D.coeRingHom =
      (presheafValueMapOfHom χ hχ D G hsG' hTG').comp D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [show D.coeRingHom (algebraMap R (Localization.Away D.s) a) =
        D.canonicalMap a from rfl,
      presheafValueMapOfHom_canonicalMap φ hφ D E hsE hTE a,
      presheafValueMapOfHom_canonicalMap ψ hψ E G hsG hTG (φ a),
      presheafValueMapOfHom_canonicalMap χ hχ D G hsG' hTG' a,
      show ψ (φ a) = χ a from DFunLike.congr_fun hcomm a]
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => presheafValueMapOfHom ψ hψ E G hsG hTG
      (presheafValueMapOfHom φ hφ D E hsE hTE y)) =
      fun y => presheafValueMapOfHom χ hχ D G hsG' hTG' y :=
    hdense.equalizer
      ((presheafValueMapOfHom_continuous ψ hψ E G hsG hTG).comp
        (presheafValueMapOfHom_continuous φ hφ D E hsE hTE))
      (presheafValueMapOfHom_continuous χ hχ D G hsG' hTG')
      (by funext a; exact DFunLike.congr_fun hcompeq a)
  exact congrFun h_eq x

end ValuationSpectrum
