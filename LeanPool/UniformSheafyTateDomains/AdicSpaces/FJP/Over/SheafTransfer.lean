/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.Functoriality

/-!
# Sheafiness of 𝓐 over a CDVF base by Milnor transfer ([FJP] Lemma 5.2, Theorem 5.3)

Source: [FJP] Lemma 5.2 (topological sheaf transfer for a strictly localizing Milnor
square, verbatim conclusion): "If the Huber pairs `(B,B⁺), (C,C⁺), (D,D⁺)` are sheafy as
complete topological rings, then `(R,R⁺)` is sheafy as a complete topological ring." and
Theorem 5.3: "The structure presheaf on `X = Spa(𝒜, 𝒜°)` is a sheaf of complete topological
rings; equivalently, `(𝒜, 𝒜°)` is sheafy." Ported to the generic base stack of the CDVF
campaign (crosswalk D9) from `FiniteJetSheafTransfer.lean`; the vertex sheafiness inputs
are re-sourced from the layer-1 strong-noetherianity theorems of
`Over/StrictLocalization.lean` (`(ϖ : Uniformizer K)` + `hK₀ : IsNoetherianRing
(unitBall K)`) through the project's 828(b) discharger.

Retargeted at the project's `ValuationSpectrum.IsSheafy` (rational coverings; the paper's
arbitrary-opens upgrade (5.9) is not part of the project's class and is not formalised).

Gluing chain (paper's proof, p. 19–20): push the matching family to the vertices; matching
persists on pairwise intersections (`interDatum` + naturality); vertices' `IsSheafy.gluing`
produce `b ∈ B_U`, `c ∈ C_U`; their 𝓓-images agree after restriction to every piece, hence
agree by 𝓓-separatedness; exactness of the localized Milnor row ([FJP] Prop 4.5 via the
graph bridges) produces the unique `x ∈ 𝒪_𝓐(U)`; its restrictions are recovered by
injectivity of the localized rows on the pieces.

Embedding: the range of `productRestrictionSub` is the closed `sectionEqualizer` (project
generic), and the σ-compact-free Tate open mapping route applies once gluing and
injectivity are in hand ([FJP] Thm 5.3's "the Banach open mapping theorem makes the
continuous bijection onto that image a homeomorphism").
-/

@[expose] public section

open Filter Topology

namespace FiniteJetOver

open FiniteJet
open FiniteJet.RestrictedLaurent
open ValuationSpectrum
open FiniteJetOver.StrictLoc

open scoped Classical NormedField Valued

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable {K}
variable (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))

/-! ### The vertex sheafiness inputs

[FJP] Theorem 5.3 (input): "The three comparison rings are strongly noetherian. Huber's
direct sheaf theorem [4, Theorem 2.2] gives the rational-cover sheaf condition for their
structure presheaves." In the project's vocabulary this is
`isSheafy_of_stronglyNoetherian_828b`; the strong noetherianity comes from the layer-1 K2
chain (`StrictLoc.isStronglyNoetherian_JetB/C/D`), everything else in the 828(b)
hypothesis bundle is an instance (`Over/JetRings.lean` + the Huber/Tate instances of
`Over/Functoriality.lean`). -/

include ϖ hK₀ in
theorem isSheafy_JetB : ValuationSpectrum.IsSheafy (JetB K) := by
  haveI := isStronglyNoetherian_JetB K ϖ hK₀
  exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

include ϖ hK₀ in
theorem isSheafy_JetC : ValuationSpectrum.IsSheafy (JetC K) := by
  haveI := isStronglyNoetherian_JetC K ϖ hK₀
  exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

include ϖ hK₀ in
theorem isSheafy_JetD : ValuationSpectrum.IsSheafy (JetD K) := by
  haveI := isStronglyNoetherian_JetD K ϖ hK₀
  exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

/-! ### Ingredients of the gluing transfer -/

include ϖ hK₀ in
/-- Injectivity (separation) for 𝓐: the localized Milnor rows are jointly injective on
every rational piece ([FJP] Lemma 5.2: "It equals `J r_R`. Since `J` is itself an
embedding …"; algebraic part). -/
theorem productRestrictionSub_injective_JetA (C : RationalCoveringData (JetA K))
    (hC : C.IsRational) :
    Function.Injective (productRestrictionSub (JetA K) C) := by
  haveI : IsSheafy (JetB K) := isSheafy_JetB ϖ hK₀
  haveI : IsSheafy (JetC K) := isSheafy_JetC ϖ hK₀
  intro x y hxy
  set z := x - y with hz
  set e := datumEnum C.base with he
  -- all piece restrictions of `z` vanish
  have hres : ∀ (D : ↥C.covers),
      restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) z = 0 := by
    intro D
    have hDx := congrFun hxy D
    have hsub : restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) (x - y) =
        restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) x -
        restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) y :=
      RingHom.map_sub _ x y
    rw [hz, hsub,
      show restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) x =
        productRestrictionSub (JetA K) C x D from rfl,
      show restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) y =
        productRestrictionSub (JetA K) C y D from rfl, hDx, sub_self]
  -- the 𝓑-pushed global section vanishes (vertex separatedness on the pushed covering)
  have hBz : presheafValueMapB ϖ C.base hC.base z = 0 := by
    refine IsSheafy.separationSub (A := JetB K) (pushCoveringB ϖ C hC)
      (pushCoveringB_isRational ϖ hC) ?_
    funext D'
    obtain ⟨D₀, hD₀⟩ := D'
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD₀
    show restrictionMapHom (pushDatumB ϖ C.base hC.base) (pushDatumB ϖ d.1 (hC.piece d.2))
      ((pushCoveringB ϖ C hC).hsubset _ hD₀) (presheafValueMapB ϖ C.base hC.base z) =
      restrictionMapHom (pushDatumB ϖ C.base hC.base) (pushDatumB ϖ d.1 (hC.piece d.2))
        ((pushCoveringB ϖ C hC).hsubset _ hD₀) 0
    rw [RingHom.map_zero (restrictionMapHom (pushDatumB ϖ C.base hC.base)
      (pushDatumB ϖ d.1 (hC.piece d.2)) ((pushCoveringB ϖ C hC).hsubset _ hD₀))]
    show restrictionMap (pushDatumB ϖ C.base hC.base) (pushDatumB ϖ d.1 (hC.piece d.2))
      ((pushCoveringB ϖ C hC).hsubset _ hD₀) (presheafValueMapB ϖ C.base hC.base z) = 0
    rw [← presheafValueMapB_restriction ϖ C.base d.1 hC.base (hC.piece d.2)
        (C.hsubset d.1 d.2) ((pushCoveringB ϖ C hC).hsubset _ hD₀) z,
      show restrictionMap C.base d.1 (C.hsubset d.1 d.2) z =
        restrictionMapHom C.base d.1 (C.hsubset d.1 d.2) z from rfl,
      hres d, RingHom.map_zero (presheafValueMapB ϖ d.1 (hC.piece d.2))]
  -- the 𝓒-pushed global section vanishes
  have hCz : presheafValueMapC ϖ C.base hC.base z = 0 := by
    refine IsSheafy.separationSub (A := JetC K) (pushCoveringC ϖ C hC)
      (pushCoveringC_isRational ϖ hC) ?_
    funext D'
    obtain ⟨D₀, hD₀⟩ := D'
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD₀
    show restrictionMapHom (pushDatumC ϖ C.base hC.base) (pushDatumC ϖ d.1 (hC.piece d.2))
      ((pushCoveringC ϖ C hC).hsubset _ hD₀) (presheafValueMapC ϖ C.base hC.base z) =
      restrictionMapHom (pushDatumC ϖ C.base hC.base) (pushDatumC ϖ d.1 (hC.piece d.2))
        ((pushCoveringC ϖ C hC).hsubset _ hD₀) 0
    rw [RingHom.map_zero (restrictionMapHom (pushDatumC ϖ C.base hC.base)
      (pushDatumC ϖ d.1 (hC.piece d.2)) ((pushCoveringC ϖ C hC).hsubset _ hD₀))]
    show restrictionMap (pushDatumC ϖ C.base hC.base) (pushDatumC ϖ d.1 (hC.piece d.2))
      ((pushCoveringC ϖ C hC).hsubset _ hD₀) (presheafValueMapC ϖ C.base hC.base z) = 0
    rw [← presheafValueMapC_restriction ϖ C.base d.1 hC.base (hC.piece d.2)
        (C.hsubset d.1 d.2) ((pushCoveringC ϖ C hC).hsubset _ hD₀) z,
      show restrictionMap C.base d.1 (C.hsubset d.1 d.2) z =
        restrictionMapHom C.base d.1 (C.hsubset d.1 d.2) z from rfl,
      hres d, RingHom.map_zero (presheafValueMapC ϖ d.1 (hC.piece d.2))]
  -- through the base graph bridge: both localized-row images vanish
  have hbridge : graphBridgeA ϖ hK₀ C.base hC.base e z = 0 := by
    have hpair := loc_pair_injective K e.m C.base.s e.f ϖ hK₀
      (e.span_eq_top C.base hC.base)
    have hB0 : locJB K e.m C.base.s e.f (graphBridgeA ϖ hK₀ C.base hC.base e z) = 0 := by
      have hnat := DFunLike.congr_fun (graphBridge_natural_B ϖ hK₀ C.base hC.base e) z
      simp only [RingHom.comp_apply] at hnat
      rw [show (graphBridgeA ϖ hK₀ C.base hC.base e :
          presheafValue C.base →+* locA K e.m C.base.s e.f) z =
        graphBridgeA ϖ hK₀ C.base hC.base e z from rfl] at hnat
      rw [← hnat, hBz, RingHom.map_zero (bridgeFwdB ϖ hK₀ C.base e hC.base)]
    have hC0 : locIotaC K e.m C.base.s e.f
        (graphBridgeA ϖ hK₀ C.base hC.base e z) = 0 := by
      have hnat := DFunLike.congr_fun (graphBridge_natural_C ϖ hK₀ C.base hC.base e) z
      simp only [RingHom.comp_apply] at hnat
      rw [show (graphBridgeA ϖ hK₀ C.base hC.base e :
          presheafValue C.base →+* locA K e.m C.base.s e.f) z =
        graphBridgeA ϖ hK₀ C.base hC.base e z from rfl] at hnat
      rw [← hnat, hCz, RingHom.map_zero (bridgeFwdC ϖ hK₀ C.base e hC.base)]
    have h00 : (fun w : locA K e.m C.base.s e.f =>
        (locJB K e.m C.base.s e.f w, locIotaC K e.m C.base.s e.f w))
          (graphBridgeA ϖ hK₀ C.base hC.base e z) =
        (fun w : locA K e.m C.base.s e.f =>
          (locJB K e.m C.base.s e.f w, locIotaC K e.m C.base.s e.f w)) 0 := by
      simp only [hB0, hC0, RingHom.map_zero]
    exact hpair h00
  -- the bridge is injective, so `z = 0`
  have hz0 : z = 0 := by
    have := (graphBridgeA ϖ hK₀ C.base hC.base e).injective
      (a₁ := z) (a₂ := 0) (by rw [hbridge, map_zero])
    exact this
  rw [← sub_eq_zero]
  exact hz0

/-- Pushed opens of intersection data cut out the intersections of the pushed opens
(𝓑-side; [FJP] Lemma 5.2 `(U_{ij})_E = (U_i)_E ∩ (U_j)_E`). -/
theorem pushDatumB_interOpen (d₁ d₂ : RationalLocData (JetA K))
    (h₁ : d₁.IsRational) (h₂ : d₂.IsRational) :
    rationalOpen (pushDatumB ϖ (interDatum ϖ d₁ d₂ h₁ h₂)
        (interDatum_isRational ϖ h₁ h₂)).T
      (pushDatumB ϖ (interDatum ϖ d₁ d₂ h₁ h₂) (interDatum_isRational ϖ h₁ h₂)).s =
    rationalOpen (pushDatumB ϖ d₁ h₁).T (pushDatumB ϖ d₁ h₁).s ∩
      rationalOpen (pushDatumB ϖ d₂ h₂).T (pushDatumB ϖ d₂ h₂).s := by
  ext v
  constructor
  · intro hv
    have hvspa : v ∈ Spa (JetB K) (ringPlus (JetB K)) := hv.1
    have hmem := (mem_rationalOpen_pushDatumB_iff ϖ (interDatum ϖ d₁ d₂ h₁ h₂)
      (interDatum_isRational ϖ h₁ h₂) v hvspa).mp hv
    rw [rationalOpen_interDatum ϖ d₁ d₂ h₁ h₂] at hmem
    exact ⟨(mem_rationalOpen_pushDatumB_iff ϖ d₁ h₁ v hvspa).mpr hmem.1,
      (mem_rationalOpen_pushDatumB_iff ϖ d₂ h₂ v hvspa).mpr hmem.2⟩
  · rintro ⟨hv₁, hv₂⟩
    have hvspa : v ∈ Spa (JetB K) (ringPlus (JetB K)) := hv₁.1
    refine (mem_rationalOpen_pushDatumB_iff ϖ (interDatum ϖ d₁ d₂ h₁ h₂)
      (interDatum_isRational ϖ h₁ h₂) v hvspa).mpr ?_
    rw [rationalOpen_interDatum ϖ d₁ d₂ h₁ h₂]
    exact ⟨(mem_rationalOpen_pushDatumB_iff ϖ d₁ h₁ v hvspa).mp hv₁,
      (mem_rationalOpen_pushDatumB_iff ϖ d₂ h₂ v hvspa).mp hv₂⟩

/-- 𝓒-side analogue of `pushDatumB_interOpen`. -/
theorem pushDatumC_interOpen (d₁ d₂ : RationalLocData (JetA K))
    (h₁ : d₁.IsRational) (h₂ : d₂.IsRational) :
    rationalOpen (pushDatumC ϖ (interDatum ϖ d₁ d₂ h₁ h₂)
        (interDatum_isRational ϖ h₁ h₂)).T
      (pushDatumC ϖ (interDatum ϖ d₁ d₂ h₁ h₂) (interDatum_isRational ϖ h₁ h₂)).s =
    rationalOpen (pushDatumC ϖ d₁ h₁).T (pushDatumC ϖ d₁ h₁).s ∩
      rationalOpen (pushDatumC ϖ d₂ h₂).T (pushDatumC ϖ d₂ h₂).s := by
  ext v
  constructor
  · intro hv
    have hvspa : v ∈ Spa (JetC K) (ringPlus (JetC K)) := hv.1
    have hmem := (mem_rationalOpen_pushDatumC_iff ϖ (interDatum ϖ d₁ d₂ h₁ h₂)
      (interDatum_isRational ϖ h₁ h₂) v hvspa).mp hv
    rw [rationalOpen_interDatum ϖ d₁ d₂ h₁ h₂] at hmem
    exact ⟨(mem_rationalOpen_pushDatumC_iff ϖ d₁ h₁ v hvspa).mpr hmem.1,
      (mem_rationalOpen_pushDatumC_iff ϖ d₂ h₂ v hvspa).mpr hmem.2⟩
  · rintro ⟨hv₁, hv₂⟩
    have hvspa : v ∈ Spa (JetC K) (ringPlus (JetC K)) := hv₁.1
    refine (mem_rationalOpen_pushDatumC_iff ϖ (interDatum ϖ d₁ d₂ h₁ h₂)
      (interDatum_isRational ϖ h₁ h₂) v hvspa).mpr ?_
    rw [rationalOpen_interDatum ϖ d₁ d₂ h₁ h₂]
    exact ⟨(mem_rationalOpen_pushDatumC_iff ϖ d₁ h₁ v hvspa).mp hv₁,
      (mem_rationalOpen_pushDatumC_iff ϖ d₂ h₂ v hvspa).mp hv₂⟩

section Gluing

variable (C : RationalCoveringData (JetA K)) (hC : C.IsRational)
  (f : ∀ D : ↥C.covers, presheafValue D.1)
  (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData (JetA K))
    (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
    (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
    restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂))

include hcompat in
/-- Compatibility of the 𝓑-pushed family at an ARBITRARY vertex refinement
([FJP] Lemma 5.2: factor through the pushed intersection). -/
theorem pushedCompatB (d₁ d₂ : ↥C.covers) (D₃ : RationalLocData (JetB K))
    (h₃₁ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (pushDatumB ϖ d₁.1 (hC.piece d₁.2)).T
        (pushDatumB ϖ d₁.1 (hC.piece d₁.2)).s)
    (h₃₂ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (pushDatumB ϖ d₂.1 (hC.piece d₂.2)).T
        (pushDatumB ϖ d₂.1 (hC.piece d₂.2)).s) :
    restrictionMap (pushDatumB ϖ d₁.1 (hC.piece d₁.2)) D₃ h₃₁
      (presheafValueMapB ϖ d₁.1 (hC.piece d₁.2) (f d₁)) =
    restrictionMap (pushDatumB ϖ d₂.1 (hC.piece d₂.2)) D₃ h₃₂
      (presheafValueMapB ϖ d₂.1 (hC.piece d₂.2) (f d₂)) := by
  set hIrat := interDatum_isRational ϖ (hC.piece d₁.2) (hC.piece d₂.2) with hIratdef
  have hsub₁ : rationalOpen (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).T (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).s ⊆ rationalOpen d₁.1.T d₁.1.s := by
    rw [rationalOpen_interDatum]
    exact Set.inter_subset_left
  have hsub₂ : rationalOpen (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).T (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).s ⊆ rationalOpen d₂.1.T d₂.1.s := by
    rw [rationalOpen_interDatum]
    exact Set.inter_subset_right
  have hpush₁ : rationalOpen (pushDatumB ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).T (pushDatumB ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).s ⊆
      rationalOpen (pushDatumB ϖ d₁.1 (hC.piece d₁.2)).T
        (pushDatumB ϖ d₁.1 (hC.piece d₁.2)).s := by
    rw [pushDatumB_interOpen]
    exact Set.inter_subset_left
  have hpush₂ : rationalOpen (pushDatumB ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).T (pushDatumB ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).s ⊆
      rationalOpen (pushDatumB ϖ d₂.1 (hC.piece d₂.2)).T
        (pushDatumB ϖ d₂.1 (hC.piece d₂.2)).s := by
    rw [pushDatumB_interOpen]
    exact Set.inter_subset_right
  have h₃I : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (pushDatumB ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).T (pushDatumB ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).s := by
    rw [pushDatumB_interOpen]
    exact Set.subset_inter h₃₁ h₃₂
  have hpushed := congrArg (presheafValueMapB ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat) (hcompat d₁ d₂ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hsub₁ hsub₂)
  rw [presheafValueMapB_restriction ϖ d₁.1 (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) (hC.piece d₁.2) hIrat hsub₁ hpush₁ (f d₁),
    presheafValueMapB_restriction ϖ d₂.1 (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) (hC.piece d₂.2) hIrat hsub₂ hpush₂ (f d₂)]
    at hpushed
  have hfac₁ := congrFun (restrictionMap_comp (pushDatumB ϖ d₁.1 (hC.piece d₁.2))
    (pushDatumB ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat) D₃ hpush₁ h₃I) (presheafValueMapB ϖ d₁.1 (hC.piece d₁.2) (f d₁))
  have hfac₂ := congrFun (restrictionMap_comp (pushDatumB ϖ d₂.1 (hC.piece d₂.2))
    (pushDatumB ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat) D₃ hpush₂ h₃I) (presheafValueMapB ϖ d₂.1 (hC.piece d₂.2) (f d₂))
  simp only [Function.comp_apply] at hfac₁ hfac₂
  rw [← hfac₁, ← hfac₂, hpushed]

include hcompat in
/-- 𝓒-side analogue of `pushedCompatB`. -/
theorem pushedCompatC (d₁ d₂ : ↥C.covers) (D₃ : RationalLocData (JetC K))
    (h₃₁ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (pushDatumC ϖ d₁.1 (hC.piece d₁.2)).T
        (pushDatumC ϖ d₁.1 (hC.piece d₁.2)).s)
    (h₃₂ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (pushDatumC ϖ d₂.1 (hC.piece d₂.2)).T
        (pushDatumC ϖ d₂.1 (hC.piece d₂.2)).s) :
    restrictionMap (pushDatumC ϖ d₁.1 (hC.piece d₁.2)) D₃ h₃₁
      (presheafValueMapC ϖ d₁.1 (hC.piece d₁.2) (f d₁)) =
    restrictionMap (pushDatumC ϖ d₂.1 (hC.piece d₂.2)) D₃ h₃₂
      (presheafValueMapC ϖ d₂.1 (hC.piece d₂.2) (f d₂)) := by
  set hIrat := interDatum_isRational ϖ (hC.piece d₁.2) (hC.piece d₂.2) with hIratdef
  have hsub₁ : rationalOpen (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).T (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).s ⊆ rationalOpen d₁.1.T d₁.1.s := by
    rw [rationalOpen_interDatum]
    exact Set.inter_subset_left
  have hsub₂ : rationalOpen (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).T (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)).s ⊆ rationalOpen d₂.1.T d₂.1.s := by
    rw [rationalOpen_interDatum]
    exact Set.inter_subset_right
  have hpush₁ : rationalOpen (pushDatumC ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).T (pushDatumC ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).s ⊆
      rationalOpen (pushDatumC ϖ d₁.1 (hC.piece d₁.2)).T
        (pushDatumC ϖ d₁.1 (hC.piece d₁.2)).s := by
    rw [pushDatumC_interOpen]
    exact Set.inter_subset_left
  have hpush₂ : rationalOpen (pushDatumC ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).T (pushDatumC ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).s ⊆
      rationalOpen (pushDatumC ϖ d₂.1 (hC.piece d₂.2)).T
        (pushDatumC ϖ d₂.1 (hC.piece d₂.2)).s := by
    rw [pushDatumC_interOpen]
    exact Set.inter_subset_right
  have h₃I : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (pushDatumC ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).T (pushDatumC ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat).s := by
    rw [pushDatumC_interOpen]
    exact Set.subset_inter h₃₁ h₃₂
  have hpushed := congrArg (presheafValueMapC ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat) (hcompat d₁ d₂ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hsub₁ hsub₂)
  rw [presheafValueMapC_restriction ϖ d₁.1 (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) (hC.piece d₁.2) hIrat hsub₁ hpush₁ (f d₁),
    presheafValueMapC_restriction ϖ d₂.1 (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) (hC.piece d₂.2) hIrat hsub₂ hpush₂ (f d₂)]
    at hpushed
  have hfac₁ := congrFun (restrictionMap_comp (pushDatumC ϖ d₁.1 (hC.piece d₁.2))
    (pushDatumC ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat) D₃ hpush₁ h₃I) (presheafValueMapC ϖ d₁.1 (hC.piece d₁.2) (f d₁))
  have hfac₂ := congrFun (restrictionMap_comp (pushDatumC ϖ d₂.1 (hC.piece d₂.2))
    (pushDatumC ϖ (interDatum ϖ d₁.1 d₂.1 (hC.piece d₁.2) (hC.piece d₂.2)) hIrat) D₃ hpush₂ h₃I) (presheafValueMapC ϖ d₂.1 (hC.piece d₂.2) (f d₂))
  simp only [Function.comp_apply] at hfac₁ hfac₂
  rw [← hfac₁, ← hfac₂, hpushed]

include hK₀ in
/-- Joint injectivity of the vertex pushes at a single rational datum
([FJP] `j_{U_i}`-injectivity; the kernel chase at one datum). -/
theorem pairMapBC_injective (D : RationalLocData (JetA K)) (hD : D.IsRational)
    {u₁ u₂ : presheafValue D}
    (hB : presheafValueMapB ϖ D hD u₁ = presheafValueMapB ϖ D hD u₂)
    (hCeq : presheafValueMapC ϖ D hD u₁ = presheafValueMapC ϖ D hD u₂) : u₁ = u₂ := by
  set e := datumEnum D with he
  set z := u₁ - u₂ with hz
  have hBz : presheafValueMapB ϖ D hD z = 0 := by
    rw [hz]
    exact (RingHom.map_sub (presheafValueMapB ϖ D hD) u₁ u₂).trans
      (sub_eq_zero.mpr hB)
  have hCz : presheafValueMapC ϖ D hD z = 0 := by
    rw [hz]
    exact (RingHom.map_sub (presheafValueMapC ϖ D hD) u₁ u₂).trans
      (sub_eq_zero.mpr hCeq)
  have hbridge : graphBridgeA ϖ hK₀ D hD e z = 0 := by
    have hpair := loc_pair_injective K e.m D.s e.f ϖ hK₀ (e.span_eq_top D hD)
    have hB0 : locJB K e.m D.s e.f (graphBridgeA ϖ hK₀ D hD e z) = 0 := by
      have hnat := DFunLike.congr_fun (graphBridge_natural_B ϖ hK₀ D hD e) z
      simp only [RingHom.comp_apply] at hnat
      rw [show (graphBridgeA ϖ hK₀ D hD e :
          presheafValue D →+* locA K e.m D.s e.f) z =
        graphBridgeA ϖ hK₀ D hD e z from rfl] at hnat
      rw [← hnat, hBz, RingHom.map_zero (bridgeFwdB ϖ hK₀ D e hD)]
    have hC0 : locIotaC K e.m D.s e.f (graphBridgeA ϖ hK₀ D hD e z) = 0 := by
      have hnat := DFunLike.congr_fun (graphBridge_natural_C ϖ hK₀ D hD e) z
      simp only [RingHom.comp_apply] at hnat
      rw [show (graphBridgeA ϖ hK₀ D hD e :
          presheafValue D →+* locA K e.m D.s e.f) z =
        graphBridgeA ϖ hK₀ D hD e z from rfl] at hnat
      rw [← hnat, hCz, RingHom.map_zero (bridgeFwdC ϖ hK₀ D e hD)]
    have h00 : (fun w : locA K e.m D.s e.f =>
        (locJB K e.m D.s e.f w, locIotaC K e.m D.s e.f w)) (graphBridgeA ϖ hK₀ D hD e z) =
        (fun w : locA K e.m D.s e.f =>
          (locJB K e.m D.s e.f w, locIotaC K e.m D.s e.f w)) 0 := by
      simp only [hB0, hC0, RingHom.map_zero]
    exact hpair h00
  have hz0 : z = 0 := (graphBridgeA ϖ hK₀ D hD e).injective (by rw [hbridge, map_zero])
  rw [← sub_eq_zero]
  exact hz0

include ϖ hK₀ hC hcompat in
/-- The gluing transfer ([FJP] Lemma 5.2, gluing half). -/
theorem gluing_JetA :
    ∃ x : presheafValue C.base, ∀ D : ↥C.covers,
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by
  classical
  haveI : IsSheafy (JetB K) := isSheafy_JetB ϖ hK₀
  haveI : IsSheafy (JetC K) := isSheafy_JetC ϖ hK₀
  haveI : IsSheafy (JetD K) := isSheafy_JetD ϖ hK₀
  set e := datumEnum C.base with he
  -- the pushed families (choice-based; casts eliminated by `restrictionMap_cast`)
  set gB : ∀ D' : ↥(pushCoveringB ϖ C hC).covers, presheafValue D'.1 := fun D' =>
    (Finset.mem_image.mp D'.2).choose_spec.2 ▸
      presheafValueMapB ϖ (Finset.mem_image.mp D'.2).choose.1
        (hC.piece (Finset.mem_image.mp D'.2).choose.2)
        (f (Finset.mem_image.mp D'.2).choose) with hgB
  set gC : ∀ D' : ↥(pushCoveringC ϖ C hC).covers, presheafValue D'.1 := fun D' =>
    (Finset.mem_image.mp D'.2).choose_spec.2 ▸
      presheafValueMapC ϖ (Finset.mem_image.mp D'.2).choose.1
        (hC.piece (Finset.mem_image.mp D'.2).choose.2)
        (f (Finset.mem_image.mp D'.2).choose) with hgC
  -- restriction of a pushed-family value factors through the chosen piece
  have hgBres : ∀ (D' : ↥(pushCoveringB ϖ C hC).covers) (D₃ : RationalLocData (JetB K))
      (h₃ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D'.1.T D'.1.s),
      restrictionMap D'.1 D₃ h₃ (gB D') =
        restrictionMap (pushDatumB ϖ (Finset.mem_image.mp D'.2).choose.1
            (hC.piece (Finset.mem_image.mp D'.2).choose.2)) D₃
          (by rw [(Finset.mem_image.mp D'.2).choose_spec.2]; exact h₃)
          (presheafValueMapB ϖ (Finset.mem_image.mp D'.2).choose.1
            (hC.piece (Finset.mem_image.mp D'.2).choose.2)
            (f (Finset.mem_image.mp D'.2).choose)) := by
    intro D' D₃ h₃
    show restrictionMap D'.1 D₃ h₃
      ((Finset.mem_image.mp D'.2).choose_spec.2 ▸
        presheafValueMapB ϖ (Finset.mem_image.mp D'.2).choose.1
          (hC.piece (Finset.mem_image.mp D'.2).choose.2)
          (f (Finset.mem_image.mp D'.2).choose)) = _
    rw [restrictionMap_cast _ _ (Finset.mem_image.mp D'.2).choose_spec.2]
    have := congrFun (restrictionMap_comp
      (pushDatumB ϖ (Finset.mem_image.mp D'.2).choose.1
        (hC.piece (Finset.mem_image.mp D'.2).choose.2)) D'.1 D₃
      (by rw [(Finset.mem_image.mp D'.2).choose_spec.2]) h₃)
      (presheafValueMapB ϖ (Finset.mem_image.mp D'.2).choose.1
        (hC.piece (Finset.mem_image.mp D'.2).choose.2)
        (f (Finset.mem_image.mp D'.2).choose))
    simp only [Function.comp_apply] at this
    exact this
  have hgCres : ∀ (D' : ↥(pushCoveringC ϖ C hC).covers) (D₃ : RationalLocData (JetC K))
      (h₃ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D'.1.T D'.1.s),
      restrictionMap D'.1 D₃ h₃ (gC D') =
        restrictionMap (pushDatumC ϖ (Finset.mem_image.mp D'.2).choose.1
            (hC.piece (Finset.mem_image.mp D'.2).choose.2)) D₃
          (by rw [(Finset.mem_image.mp D'.2).choose_spec.2]; exact h₃)
          (presheafValueMapC ϖ (Finset.mem_image.mp D'.2).choose.1
            (hC.piece (Finset.mem_image.mp D'.2).choose.2)
            (f (Finset.mem_image.mp D'.2).choose)) := by
    intro D' D₃ h₃
    show restrictionMap D'.1 D₃ h₃
      ((Finset.mem_image.mp D'.2).choose_spec.2 ▸
        presheafValueMapC ϖ (Finset.mem_image.mp D'.2).choose.1
          (hC.piece (Finset.mem_image.mp D'.2).choose.2)
          (f (Finset.mem_image.mp D'.2).choose)) = _
    rw [restrictionMap_cast _ _ (Finset.mem_image.mp D'.2).choose_spec.2]
    have := congrFun (restrictionMap_comp
      (pushDatumC ϖ (Finset.mem_image.mp D'.2).choose.1
        (hC.piece (Finset.mem_image.mp D'.2).choose.2)) D'.1 D₃
      (by rw [(Finset.mem_image.mp D'.2).choose_spec.2]) h₃)
      (presheafValueMapC ϖ (Finset.mem_image.mp D'.2).choose.1
        (hC.piece (Finset.mem_image.mp D'.2).choose.2)
        (f (Finset.mem_image.mp D'.2).choose))
    simp only [Function.comp_apply] at this
    exact this
  -- the pushed-family value at the canonical piece element is the piece push
  have hgBd : ∀ d : ↥C.covers, gB ⟨pushDatumB ϖ d.1 (hC.piece d.2),
      Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ =
      presheafValueMapB ϖ d.1 (hC.piece d.2) (f d) := by
    intro d
    have hselfB := hgBres ⟨pushDatumB ϖ d.1 (hC.piece d.2),
        Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩
      (pushDatumB ϖ d.1 (hC.piece d.2)) (subset_refl _)
    rw [congrFun (restrictionMap_id (pushDatumB ϖ d.1 (hC.piece d.2))) _] at hselfB
    simp only [id_eq] at hselfB
    rw [hselfB,
      pushedCompatB ϖ C hC f hcompat
        (Finset.mem_image.mp (Finset.mem_image.mpr
          ⟨d, Finset.mem_attach _ _, rfl⟩ : pushDatumB ϖ d.1 (hC.piece d.2) ∈
            (pushCoveringB ϖ C hC).covers)).choose d
        (pushDatumB ϖ d.1 (hC.piece d.2)) _ (subset_refl _)]
    exact congrFun (restrictionMap_id (pushDatumB ϖ d.1 (hC.piece d.2))) _
  have hgCd : ∀ d : ↥C.covers, gC ⟨pushDatumC ϖ d.1 (hC.piece d.2),
      Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ =
      presheafValueMapC ϖ d.1 (hC.piece d.2) (f d) := by
    intro d
    have hselfC := hgCres ⟨pushDatumC ϖ d.1 (hC.piece d.2),
        Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩
      (pushDatumC ϖ d.1 (hC.piece d.2)) (subset_refl _)
    rw [congrFun (restrictionMap_id (pushDatumC ϖ d.1 (hC.piece d.2))) _] at hselfC
    simp only [id_eq] at hselfC
    rw [hselfC,
      pushedCompatC ϖ C hC f hcompat
        (Finset.mem_image.mp (Finset.mem_image.mpr
          ⟨d, Finset.mem_attach _ _, rfl⟩ : pushDatumC ϖ d.1 (hC.piece d.2) ∈
            (pushCoveringC ϖ C hC).covers)).choose d
        (pushDatumC ϖ d.1 (hC.piece d.2)) _ (subset_refl _)]
    exact congrFun (restrictionMap_id (pushDatumC ϖ d.1 (hC.piece d.2))) _
  -- vertex gluing at 𝓑
  obtain ⟨bB, hbB⟩ := IsSheafy.gluing (A := JetB K) (pushCoveringB ϖ C hC)
    (pushCoveringB_isRational ϖ hC) gB (by
      intro D₁' D₂' D₃ h₃₁ h₃₂
      rw [hgBres D₁' D₃ h₃₁, hgBres D₂' D₃ h₃₂]
      exact pushedCompatB ϖ C hC f hcompat _ _ D₃ _ _)
  -- vertex gluing at 𝓒
  obtain ⟨bC, hbC⟩ := IsSheafy.gluing (A := JetC K) (pushCoveringC ϖ C hC)
    (pushCoveringC_isRational ϖ hC) gC (by
      intro D₁' D₂' D₃ h₃₁ h₃₂
      rw [hgCres D₁' D₃ h₃₁, hgCres D₂' D₃ h₃₂]
      exact pushedCompatC ϖ C hC f hcompat _ _ D₃ _ _)
  -- 𝓓-matching by 𝓓-separation on the pushed covering
  have hDmatch : mapBD ϖ C.base hC.base bB = mapCD ϖ C.base hC.base bC := by
    refine IsSheafy.separationSub (A := JetD K) (pushCoveringD ϖ C hC)
      (pushCoveringD_isRational ϖ hC) ?_
    funext D'
    obtain ⟨DD, hDD⟩ := D'
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hDD
    show restrictionMapHom (pushDatumD ϖ C.base hC.base)
      (pushDatumD ϖ d.1 (hC.piece d.2))
      ((pushCoveringD ϖ C hC).hsubset _ hDD) (mapBD ϖ C.base hC.base bB) =
      restrictionMapHom (pushDatumD ϖ C.base hC.base) (pushDatumD ϖ d.1 (hC.piece d.2))
        ((pushCoveringD ϖ C hC).hsubset _ hDD) (mapCD ϖ C.base hC.base bC)
    have hpushB : rationalOpen (pushDatumB ϖ d.1 (hC.piece d.2)).T
        (pushDatumB ϖ d.1 (hC.piece d.2)).s ⊆
        rationalOpen (pushDatumB ϖ C.base hC.base).T (pushDatumB ϖ C.base hC.base).s :=
      (pushCoveringB ϖ C hC).hsubset _
        (Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩)
    have hpushC : rationalOpen (pushDatumC ϖ d.1 (hC.piece d.2)).T
        (pushDatumC ϖ d.1 (hC.piece d.2)).s ⊆
        rationalOpen (pushDatumC ϖ C.base hC.base).T (pushDatumC ϖ C.base hC.base).s :=
      (pushCoveringC ϖ C hC).hsubset _
        (Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩)
    -- restriction commutes with mapBD/mapCD (generic naturality at ρ)
    have hnatB : restrictionMap (pushDatumD ϖ C.base hC.base)
        (pushDatumD ϖ d.1 (hC.piece d.2)) ((pushCoveringD ϖ C hC).hsubset _ hDD)
        (mapBD ϖ C.base hC.base bB) =
        mapBD ϖ d.1 (hC.piece d.2) (restrictionMap (pushDatumB ϖ C.base hC.base)
          (pushDatumB ϖ d.1 (hC.piece d.2)) hpushB bB) :=
      (presheafValueMapOfHom_restriction (rhoB K) (continuous_rhoB)
        (pushDatumB ϖ C.base hC.base) (pushDatumB ϖ d.1 (hC.piece d.2))
        (pushDatumD ϖ C.base hC.base) (pushDatumD ϖ d.1 (hC.piece d.2))
        ((square_commutes K C.base.s).symm)
        (by
          intro t ht
          obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
          rw [square_commutes K t₀]
          exact Finset.mem_image_of_mem _ ht₀)
        ((square_commutes K d.1.s).symm)
        (by
          intro t ht
          obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
          rw [square_commutes K t₀]
          exact Finset.mem_image_of_mem _ ht₀)
        hpushB ((pushCoveringD ϖ C hC).hsubset _ hDD) bB).symm
    have hnatC : restrictionMap (pushDatumD ϖ C.base hC.base)
        (pushDatumD ϖ d.1 (hC.piece d.2)) ((pushCoveringD ϖ C hC).hsubset _ hDD)
        (mapCD ϖ C.base hC.base bC) =
        mapCD ϖ d.1 (hC.piece d.2) (restrictionMap (pushDatumC ϖ C.base hC.base)
          (pushDatumC ϖ d.1 (hC.piece d.2)) hpushC bC) :=
      (presheafValueMapOfHom_restriction (rhoC K) (continuous_rhoC)
        (pushDatumC ϖ C.base hC.base) (pushDatumC ϖ d.1 (hC.piece d.2))
        (pushDatumD ϖ C.base hC.base) (pushDatumD ϖ d.1 (hC.piece d.2))
        rfl
        (by
          intro t ht
          obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
          exact Finset.mem_image_of_mem _ ht₀)
        rfl
        (by
          intro t ht
          obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
          exact Finset.mem_image_of_mem _ ht₀)
        hpushC ((pushCoveringD ϖ C hC).hsubset _ hDD) bC).symm
    show restrictionMap (pushDatumD ϖ C.base hC.base) (pushDatumD ϖ d.1 (hC.piece d.2))
      ((pushCoveringD ϖ C hC).hsubset _ hDD) (mapBD ϖ C.base hC.base bB) =
      restrictionMap (pushDatumD ϖ C.base hC.base) (pushDatumD ϖ d.1 (hC.piece d.2))
        ((pushCoveringD ϖ C hC).hsubset _ hDD) (mapCD ϖ C.base hC.base bC)
    rw [hnatB, hnatC]
    -- restrictions of the glued sections are the pushed piece-values
    have hbBd := hbB ⟨pushDatumB ϖ d.1 (hC.piece d.2),
      Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩
    have hbCd := hbC ⟨pushDatumC ϖ d.1 (hC.piece d.2),
      Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩
    rw [show restrictionMap (pushDatumB ϖ C.base hC.base)
        (pushDatumB ϖ d.1 (hC.piece d.2)) hpushB bB =
        gB ⟨pushDatumB ϖ d.1 (hC.piece d.2),
          Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ from hbBd,
      show restrictionMap (pushDatumC ϖ C.base hC.base)
        (pushDatumC ϖ d.1 (hC.piece d.2)) hpushC bC =
        gC ⟨pushDatumC ϖ d.1 (hC.piece d.2),
          Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ from hbCd]
    -- both sides are the 𝓓-pushes of chosen 𝓐-sections; identify via self-restriction
    -- + pushed compatibility + the coherence square
    rw [hgBd d, hgCd d]
    -- finish with the 𝓓-coherence at the piece
    exact DFunLike.congr_fun (mapBD_mapB_eq_mapCD_mapC ϖ d.1 (hC.piece d.2)) (f d)
  -- transport through the base bridges: loc-level row exactness gives the pullback
  have hloc : locRhoB K e.m C.base.s e.f (bridgeFwdB ϖ hK₀ C.base e hC.base bB) =
      locRhoC K e.m C.base.s e.f (bridgeFwdC ϖ hK₀ C.base e hC.base bC) := by
    have hB : locRhoB K e.m C.base.s e.f (bridgeFwdB ϖ hK₀ C.base e hC.base bB) =
        bridgeFwdD ϖ hK₀ C.base e hC.base (mapBD ϖ C.base hC.base bB) :=
      DFunLike.congr_fun (locRhoB_bridgeFwdB ϖ hK₀ C.base e hC.base) bB
    have hCq : locRhoC K e.m C.base.s e.f (bridgeFwdC ϖ hK₀ C.base e hC.base bC) =
        bridgeFwdD ϖ hK₀ C.base e hC.base (mapCD ϖ C.base hC.base bC) :=
      DFunLike.congr_fun (locRhoC_bridgeFwdC ϖ hK₀ C.base e hC.base) bC
    rw [hB, hCq, hDmatch]
  obtain ⟨w, ⟨hwB, hwC⟩, -⟩ := loc_row_exact K e.m C.base.s e.f ϖ hK₀
    (e.span_eq_top C.base hC.base) (bridgeFwdB ϖ hK₀ C.base e hC.base bB)
    (bridgeFwdC ϖ hK₀ C.base e hC.base bC) hloc
  set x := (graphBridgeA ϖ hK₀ C.base hC.base e).symm w with hx
  have hAx : graphBridgeA ϖ hK₀ C.base hC.base e x = w :=
    (graphBridgeA ϖ hK₀ C.base hC.base e).apply_symm_apply w
  have hmapBx : presheafValueMapB ϖ C.base hC.base x = bB := by
    refine bridgeFwdB_injective ϖ hK₀ C.base e hC.base ?_
    have hnat : bridgeFwdB ϖ hK₀ C.base e hC.base
        (presheafValueMapB ϖ C.base hC.base x) =
        locJB K e.m C.base.s e.f (graphBridgeA ϖ hK₀ C.base hC.base e x) :=
      DFunLike.congr_fun (graphBridge_natural_B ϖ hK₀ C.base hC.base e) x
    rw [hnat, hAx, hwB]
  have hmapCx : presheafValueMapC ϖ C.base hC.base x = bC := by
    refine bridgeFwdC_injective ϖ hK₀ C.base e hC.base ?_
    have hnat : bridgeFwdC ϖ hK₀ C.base e hC.base
        (presheafValueMapC ϖ C.base hC.base x) =
        locIotaC K e.m C.base.s e.f (graphBridgeA ϖ hK₀ C.base hC.base e x) :=
      DFunLike.congr_fun (graphBridge_natural_C ϖ hK₀ C.base hC.base e) x
    rw [hnat, hAx, hwC]
  refine ⟨x, fun d => ?_⟩
  -- identify the restrictions piecewise via the joint vertex injectivity
  have hpushB : rationalOpen (pushDatumB ϖ d.1 (hC.piece d.2)).T
      (pushDatumB ϖ d.1 (hC.piece d.2)).s ⊆
      rationalOpen (pushDatumB ϖ C.base hC.base).T (pushDatumB ϖ C.base hC.base).s :=
    (pushCoveringB ϖ C hC).hsubset _
      (Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩)
  have hpushC : rationalOpen (pushDatumC ϖ d.1 (hC.piece d.2)).T
      (pushDatumC ϖ d.1 (hC.piece d.2)).s ⊆
      rationalOpen (pushDatumC ϖ C.base hC.base).T (pushDatumC ϖ C.base hC.base).s :=
    (pushCoveringC ϖ C hC).hsubset _
      (Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩)
  refine pairMapBC_injective ϖ hK₀ d.1 (hC.piece d.2) ?_ ?_
  · rw [presheafValueMapB_restriction ϖ C.base d.1 hC.base (hC.piece d.2)
      (C.hsubset d.1 d.2) hpushB x, hmapBx]
    have hbBd := hbB ⟨pushDatumB ϖ d.1 (hC.piece d.2),
      Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩
    rw [show restrictionMap (pushDatumB ϖ C.base hC.base)
        (pushDatumB ϖ d.1 (hC.piece d.2)) hpushB bB =
        gB ⟨pushDatumB ϖ d.1 (hC.piece d.2),
          Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ from hbBd]
    have hselfB := hgBres ⟨pushDatumB ϖ d.1 (hC.piece d.2),
        Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩
      (pushDatumB ϖ d.1 (hC.piece d.2)) (subset_refl _)
    rw [congrFun (restrictionMap_id (pushDatumB ϖ d.1 (hC.piece d.2))) _] at hselfB
    simp only [id_eq] at hselfB
    rw [hselfB,
      pushedCompatB ϖ C hC f hcompat
        (Finset.mem_image.mp (Finset.mem_image.mpr
          ⟨d, Finset.mem_attach _ _, rfl⟩ : pushDatumB ϖ d.1 (hC.piece d.2) ∈
            (pushCoveringB ϖ C hC).covers)).choose d
        (pushDatumB ϖ d.1 (hC.piece d.2)) _ (subset_refl _)]
    exact congrFun (restrictionMap_id (pushDatumB ϖ d.1 (hC.piece d.2))) _
  · rw [presheafValueMapC_restriction ϖ C.base d.1 hC.base (hC.piece d.2)
      (C.hsubset d.1 d.2) hpushC x, hmapCx]
    have hbCd := hbC ⟨pushDatumC ϖ d.1 (hC.piece d.2),
      Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩
    rw [show restrictionMap (pushDatumC ϖ C.base hC.base)
        (pushDatumC ϖ d.1 (hC.piece d.2)) hpushC bC =
        gC ⟨pushDatumC ϖ d.1 (hC.piece d.2),
          Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩ from hbCd]
    have hselfC := hgCres ⟨pushDatumC ϖ d.1 (hC.piece d.2),
        Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩⟩
      (pushDatumC ϖ d.1 (hC.piece d.2)) (subset_refl _)
    rw [congrFun (restrictionMap_id (pushDatumC ϖ d.1 (hC.piece d.2))) _] at hselfC
    simp only [id_eq] at hselfC
    rw [hselfC,
      pushedCompatC ϖ C hC f hcompat
        (Finset.mem_image.mp (Finset.mem_image.mpr
          ⟨d, Finset.mem_attach _ _, rfl⟩ : pushDatumC ϖ d.1 (hC.piece d.2) ∈
            (pushCoveringC ϖ C hC).covers)).choose d
        (pushDatumC ϖ d.1 (hC.piece d.2)) _ (subset_refl _)]
    exact congrFun (restrictionMap_id (pushDatumC ϖ d.1 (hC.piece d.2))) _

end Gluing

include ϖ hK₀ in
/-- The embedding transfer ([FJP] Lemma 5.2, topological half; Theorem 5.3's "the Banach
open mapping theorem makes the continuous bijection onto that image a homeomorphism" —
the σ-compact-free 828b-assembly mirrored at 𝓐). -/
theorem productRestrictionSub_isEmbedding_JetA (C : RationalCoveringData (JetA K))
    (hC : C.IsRational) :
    Topology.IsEmbedding (productRestrictionSub (JetA K) C) := by
  classical
  refine ⟨?_, productRestrictionSub_injective_JetA ϖ hK₀ C hC⟩
  letI instModPiD : ∀ D : ↥C.covers, Module (JetA K) (presheafValue D.1) :=
    fun D => RingHom.toModule (RationalLocData.canonicalMap D.1)
  letI instModBase : Module (JetA K) (presheafValue C.base) :=
    RingHom.toModule (RationalLocData.canonicalMap C.base)
  letI instModPi : Module (JetA K) (∀ D : ↥C.covers, presheafValue D.1) := Pi.module _ _ _
  let rho : presheafValue C.base →ₗ[JetA K] (∀ D : ↥C.covers, presheafValue D.1) :=
    { toFun := productRestrictionSub (JetA K) C
      map_add' := fun x y => by
        funext D
        exact map_add (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) x y
      map_smul' := fun a x => by
        funext D
        show restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)
            ((RationalLocData.canonicalMap C.base) a * x) =
          (RationalLocData.canonicalMap D.1) a *
            restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) x
        rw [map_mul]
        congr 1
        exact productRestriction_comp_canonicalMap (A := JetA K) C a D.1 D.2 }
  have hrange : (LinearMap.range rho : Set (∀ D : ↥C.covers, presheafValue D.1)) =
      sectionEqualizer (JetA K) C := by
    ext s
    constructor
    · rintro ⟨x, rfl⟩
      exact productRestrictionSub_mem_sectionEqualizer (JetA K) C x
    · intro hs
      obtain ⟨x, hx⟩ := gluing_JetA ϖ hK₀ C hC s hs
      exact ⟨x, funext fun D => hx D⟩
  have hclosed : IsClosed
      (LinearMap.range rho : Set (∀ D : ↥C.covers, presheafValue D.1)) := by
    rw [hrange]; exact sectionEqualizer_isClosed (JetA K) C
  haveI : (uniformity (presheafValue C.base)).IsCountablyGenerated :=
    presheafValue_uniformity_isCountablyGenerated (A := JetA K) C.base
  haveI : ∀ D : ↥C.covers, (uniformity (presheafValue D.1)).IsCountablyGenerated :=
    fun D => presheafValue_uniformity_isCountablyGenerated (A := JetA K) D.1
  haveI : ContinuousSMul (JetA K) (presheafValue C.base) :=
    ⟨continuous_mul.comp (((canonicalMap_continuous C.base).comp continuous_fst).prodMk
      continuous_snd)⟩
  haveI : ∀ D : ↥C.covers, ContinuousSMul (JetA K) (presheafValue D.1) :=
    fun D => ⟨continuous_mul.comp
      (((canonicalMap_continuous D.1).comp continuous_fst).prodMk continuous_snd)⟩
  haveI : ContinuousSMul (JetA K) (∀ D : ↥C.covers, presheafValue D.1) := inferInstance
  have hrho_cont : Continuous rho :=
    continuous_pi fun D => restrictionMapHom_continuous C.base D.1 (C.hsubset D.1 D.2)
  have hinj : Function.Injective (rho : presheafValue C.base → _) := fun x y h =>
    productRestrictionSub_injective_JetA ϖ hK₀ C hC h
  obtain ⟨u, hu⟩ := (inferInstance : IsTateRing (JetA K)).exists_topologicallyNilpotent_unit
  exact @isInducing_of_closedRange_of_topNilpUnit (JetA K) _ _
    (presheafValue C.base) _ instModBase _ _ _ _ _
    (∀ D : ↥C.covers, presheafValue D.1) _ instModPi _ _ _ _ _ _
    u hu u.isUnit rho hrho_cont hinj hclosed

variable (K)

include ϖ hK₀ in
/-- **The finite-jet pinching algebra over a CDVF base is sheafy**
([FJP] Theorem 5.3, layer-1 form: an explicit uniformizer `ϖ` and the noetherianity of
the base unit ball). This is the priority theorem of the campaign. -/
theorem isSheafy_JetA : ValuationSpectrum.IsSheafy (JetA K) where
  embedding := fun C hC => productRestrictionSub_isEmbedding_JetA ϖ hK₀ C hC
  gluing := fun C hC f hcompat => gluing_JetA ϖ hK₀ C hC f hcompat

/-- **Layer-2 form of `isSheafy_JetA`**: over a base whose valuation ring is a discrete
valuation ring, the uniformizer is chosen by `Uniformizer.ofDVR` and the unit-ball
noetherianity comes from `CDVFBase.isNoetherianRing_unitBall`. -/
theorem isSheafy_JetA_of_dvr [IsDiscreteValuationRing 𝒪[K]] :
    ValuationSpectrum.IsSheafy (JetA K) :=
  isSheafy_JetA K (Uniformizer.ofDVR K) (isNoetherianRing_unitBall K)

end FiniteJetOver
