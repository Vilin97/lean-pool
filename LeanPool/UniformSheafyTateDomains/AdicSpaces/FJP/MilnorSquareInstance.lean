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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetSheafTransfer
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.MilnorSheafTransfer

/-!
# The finite-jet square as a `MilnorSquareData` (campaign B, T620)

Instantiates the abstract strict-Milnor-descent criterion
(`isSheafy_of_milnorSquare`) at the finite-jet square
`𝓐 = 𝓑 ×_𝓓 𝓒` — the regression target re-deriving `isSheafy_JetA` through the
abstract criterion, and the template for the `⟨V₁,…,Vₙ⟩`-extended square.

The pushes are the rationality-gated `pushDatum*` constructors behind a
classical `dite` (the abstract laws only quantify over rational data, where
`dif_pos` collapses the gate). The value maps are definitionally the generic
`presheafValueMapOfHom` (that is how `presheafValueMap*` are defined).
-/

@[expose] public section

@[expose] public section

noncomputable section

namespace FiniteJet

open ValuationSpectrum TopologicalRing StrictLoc

variable (F : Type*) [Field F]

open Classical in
/-- The total `B`-push: `pushDatumB` on rational data, a trivial datum elsewhere. -/
noncomputable def jetPushB : RationalLocData (JetA F) → RationalLocData (JetB F) :=
  fun D => if h : D.IsRational then pushDatumB D h else trivialPlusDatum (JetB F) (podB F) 1

open Classical in
/-- The total `C`-push. -/
noncomputable def jetPushC : RationalLocData (JetA F) → RationalLocData (JetC F) :=
  fun D => if h : D.IsRational then pushDatumC D h else trivialPlusDatum (JetC F) (podC F) 1

open Classical in
/-- The total `D`-push. -/
noncomputable def jetPushD : RationalLocData (JetA F) → RationalLocData (JetD F) :=
  fun D => if h : D.IsRational then pushDatumD D h else trivialPlusDatum (JetD F) (podD F) 1

theorem jetPushB_eq {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    jetPushB F D = pushDatumB D hD := by
  simp [jetPushB, dif_pos hD]

theorem jetPushC_eq {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    jetPushC F D = pushDatumC D hD := by
  simp [jetPushC, dif_pos hD]

theorem jetPushD_eq {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    jetPushD F D = pushDatumD D hD := by
  simp [jetPushD, dif_pos hD]

/-! ### Subst-helpers: free-datum auxiliaries reducing the abstract fields to the
concrete `pushDatum*` lemmas (the target datum is a free variable so `subst`
lands the goal in `pushDatum*`-land, where proof-irrelevance makes the maps
definitionally the concrete `presheafValueMap*`). -/

private theorem rowInjectiveAux (U : RationalLocData (JetA F)) (hU : U.IsRational)
    {DB : RationalLocData (JetB F)} {DC : RationalLocData (JetC F)}
    (hDB : DB = pushDatumB U hU) (hDC : DC = pushDatumC U hU)
    (hsB : DB.s = jB F U.s) (hTB : ∀ t ∈ U.T, jB F t ∈ DB.T)
    (hsC : DC.s = iotaC F U.s) (hTC : ∀ t ∈ U.T, iotaC F t ∈ DC.T)
    (x y : presheafValue U)
    (hB : presheafValueMapOfHom (jB F) (continuous_jB) U DB hsB hTB x =
      presheafValueMapOfHom (jB F) (continuous_jB) U DB hsB hTB y)
    (hC : presheafValueMapOfHom (iotaC F) (continuous_iotaC) U DC hsC hTC x =
      presheafValueMapOfHom (iotaC F) (continuous_iotaC) U DC hsC hTC y) :
    x = y := by
  subst hDB; subst hDC
  have hB' : presheafValueMapB U hU x = presheafValueMapB U hU y := hB
  have hC' : presheafValueMapC U hU x = presheafValueMapC U hU y := hC
  exact pairMapBC_injective U hU hB' hC'

private theorem rowCommAux (U : RationalLocData (JetA F)) (hU : U.IsRational)
    {DB : RationalLocData (JetB F)} {DC : RationalLocData (JetC F)}
    {DD : RationalLocData (JetD F)}
    (hDB : DB = pushDatumB U hU) (hDC : DC = pushDatumC U hU)
    (hDD : DD = pushDatumD U hU)
    (hsB : DB.s = jB F U.s) (hTB : ∀ t ∈ U.T, jB F t ∈ DB.T)
    (hsC : DC.s = iotaC F U.s) (hTC : ∀ t ∈ U.T, iotaC F t ∈ DC.T)
    (hsBD : DD.s = rhoB F DB.s) (hTBD : ∀ t ∈ DB.T, rhoB F t ∈ DD.T)
    (hsCD : DD.s = rhoC F DC.s) (hTCD : ∀ t ∈ DC.T, rhoC F t ∈ DD.T)
    (x : presheafValue U) :
    presheafValueMapOfHom (rhoB F) (continuous_rhoB) DB DD hsBD hTBD
        (presheafValueMapOfHom (jB F) (continuous_jB) U DB hsB hTB x) =
      presheafValueMapOfHom (rhoC F) (continuous_rhoC) DC DD hsCD hTCD
        (presheafValueMapOfHom (iotaC F) (continuous_iotaC) U DC hsC hTC x) := by
  subst hDB; subst hDC; subst hDD
  exact DFunLike.congr_fun (mapBD_mapB_eq_mapCD_mapC U hU) x

private theorem rowGlueAux (U : RationalLocData (JetA F)) (hU : U.IsRational)
    {DB : RationalLocData (JetB F)} {DC : RationalLocData (JetC F)}
    {DD : RationalLocData (JetD F)}
    (hDB : DB = pushDatumB U hU) (hDC : DC = pushDatumC U hU)
    (hDD : DD = pushDatumD U hU)
    (hsB : DB.s = jB F U.s) (hTB : ∀ t ∈ U.T, jB F t ∈ DB.T)
    (hsC : DC.s = iotaC F U.s) (hTC : ∀ t ∈ U.T, iotaC F t ∈ DC.T)
    (hsBD : DD.s = rhoB F DB.s) (hTBD : ∀ t ∈ DB.T, rhoB F t ∈ DD.T)
    (hsCD : DD.s = rhoC F DC.s) (hTCD : ∀ t ∈ DC.T, rhoC F t ∈ DD.T)
    (b : presheafValue DB) (c : presheafValue DC)
    (h : presheafValueMapOfHom (rhoB F) (continuous_rhoB) DB DD hsBD hTBD b =
      presheafValueMapOfHom (rhoC F) (continuous_rhoC) DC DD hsCD hTCD c) :
    ∃ x : presheafValue U,
      presheafValueMapOfHom (jB F) (continuous_jB) U DB hsB hTB x = b ∧
      presheafValueMapOfHom (iotaC F) (continuous_iotaC) U DC hsC hTC x = c := by
  subst hDB; subst hDC; subst hDD
  have h' : mapBD U hU b = mapCD U hU c := h
  set e := datumEnum U with he
  have hloc : locRhoB F e.m U.s e.f (bridgeFwdB U e hU b) =
      locRhoC F e.m U.s e.f (bridgeFwdC U e hU c) := by
    have hB : locRhoB F e.m U.s e.f (bridgeFwdB U e hU b) =
        bridgeFwdD U e hU (mapBD U hU b) :=
      DFunLike.congr_fun (locRhoB_bridgeFwdB U e hU) b
    have hCq : locRhoC F e.m U.s e.f (bridgeFwdC U e hU c) =
        bridgeFwdD U e hU (mapCD U hU c) :=
      DFunLike.congr_fun (locRhoC_bridgeFwdC U e hU) c
    rw [hB, hCq, h']
  obtain ⟨w, ⟨hwB, hwC⟩, -⟩ := loc_row_exact F e.m U.s e.f (e.span_eq_top U hU)
    (bridgeFwdB U e hU b) (bridgeFwdC U e hU c) hloc
  refine ⟨(graphBridgeA U hU e).symm w, ?_, ?_⟩
  · show presheafValueMapB U hU ((graphBridgeA U hU e).symm w) = b
    refine bridgeFwdB_injective U e hU ?_
    have hnat : bridgeFwdB U e hU
        (presheafValueMapB U hU ((graphBridgeA U hU e).symm w)) =
        locJB F e.m U.s e.f (graphBridgeA U hU e ((graphBridgeA U hU e).symm w)) :=
      DFunLike.congr_fun (graphBridge_natural_B U hU e) ((graphBridgeA U hU e).symm w)
    rw [hnat, (graphBridgeA U hU e).apply_symm_apply, hwB]
  · show presheafValueMapC U hU ((graphBridgeA U hU e).symm w) = c
    refine bridgeFwdC_injective U e hU ?_
    have hnat : bridgeFwdC U e hU
        (presheafValueMapC U hU ((graphBridgeA U hU e).symm w)) =
        locIotaC F e.m U.s e.f (graphBridgeA U hU e ((graphBridgeA U hU e).symm w)) :=
      DFunLike.congr_fun (graphBridge_natural_C U hU e) ((graphBridgeA U hU e).symm w)
    rw [hnat, (graphBridgeA U hU e).apply_symm_apply, hwC]

private theorem rowEmbeddingAux (U : RationalLocData (JetA F)) (hU : U.IsRational)
    {DB : RationalLocData (JetB F)} {DC : RationalLocData (JetC F)}
    (hDB : DB = pushDatumB U hU) (hDC : DC = pushDatumC U hU)
    (hsB : DB.s = jB F U.s) (hTB : ∀ t ∈ U.T, jB F t ∈ DB.T)
    (hsC : DC.s = iotaC F U.s) (hTC : ∀ t ∈ U.T, iotaC F t ∈ DC.T) :
    Topology.IsEmbedding (fun x : presheafValue U =>
      (presheafValueMapOfHom (jB F) (continuous_jB) U DB hsB hTB x,
       presheafValueMapOfHom (iotaC F) (continuous_iotaC) U DC hsC hTC x)) := by
  subst hDB; subst hDC
  show Topology.IsEmbedding (fun x : presheafValue U =>
    (presheafValueMapB U hU x, presheafValueMapC U hU x))
  set e := datumEnum U with he
  have hbr : Topology.IsEmbedding ⇑(graphBridgeA U hU e) :=
    (Homeomorph.mk (graphBridgeA U hU e).toEquiv (graphBridgeA_continuous U hU e)
      (graphBridgeA_symm_continuous U hU e)).isEmbedding
  have hpair : Topology.IsEmbedding (fun w : locA F e.m U.s e.f =>
      (locJB F e.m U.s e.f w, locIotaC F e.m U.s e.f w)) :=
    loc_pair_isEmbedding F e.m U.s e.f (e.span_eq_top U hU)
  have hcomp : (fun p : presheafValue (pushDatumB U hU) ×
        presheafValue (pushDatumC U hU) =>
        (bridgeFwdB U e hU p.1, bridgeFwdC U e hU p.2)) ∘
      (fun x : presheafValue U =>
        (presheafValueMapB U hU x, presheafValueMapC U hU x)) =
      (fun w : locA F e.m U.s e.f =>
        (locJB F e.m U.s e.f w, locIotaC F e.m U.s e.f w)) ∘
        ⇑(graphBridgeA U hU e) := by
    funext x
    have hnB : bridgeFwdB U e hU (presheafValueMapB U hU x) =
        locJB F e.m U.s e.f (graphBridgeA U hU e x) :=
      DFunLike.congr_fun (graphBridge_natural_B U hU e) x
    have hnC : bridgeFwdC U e hU (presheafValueMapC U hU x) =
        locIotaC F e.m U.s e.f (graphBridgeA U hU e x) :=
      DFunLike.congr_fun (graphBridge_natural_C U hU e) x
    exact Prod.ext hnB hnC
  refine Topology.IsEmbedding.of_comp ?_ ?_ (by rw [hcomp]; exact hpair.comp hbr)
  · exact (presheafValueMapB_continuous U hU).prodMk (presheafValueMapC_continuous U hU)
  · exact ((bridgeFwdB_continuous U e hU).comp continuous_fst).prodMk
      ((bridgeFwdC_continuous U e hU).comp continuous_snd)

private theorem pushedCompatBAux (U₁ U₂ : RationalLocData (JetA F))
    (hU₁ : U₁.IsRational) (hU₂ : U₂.IsRational)
    {DB₁ DB₂ : RationalLocData (JetB F)}
    (hDB₁ : DB₁ = pushDatumB U₁ hU₁) (hDB₂ : DB₂ = pushDatumB U₂ hU₂)
    (hs₁ : DB₁.s = jB F U₁.s) (hT₁ : ∀ t ∈ U₁.T, jB F t ∈ DB₁.T)
    (hs₂ : DB₂.s = jB F U₂.s) (hT₂ : ∀ t ∈ U₂.T, jB F t ∈ DB₂.T)
    (x₁ : presheafValue U₁) (x₂ : presheafValue U₂)
    (hmatch : ∀ (D₃ : RationalLocData (JetA F))
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₁.T U₁.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₂.T U₂.s),
      restrictionMap U₁ D₃ h₃₁ x₁ = restrictionMap U₂ D₃ h₃₂ x₂)
    (E₃ : RationalLocData (JetB F))
    (hE₁ : rationalOpen E₃.T E₃.s ⊆ rationalOpen DB₁.T DB₁.s)
    (hE₂ : rationalOpen E₃.T E₃.s ⊆ rationalOpen DB₂.T DB₂.s) :
    restrictionMap DB₁ E₃ hE₁
        (presheafValueMapOfHom (jB F) (continuous_jB) U₁ DB₁ hs₁ hT₁ x₁) =
      restrictionMap DB₂ E₃ hE₂
        (presheafValueMapOfHom (jB F) (continuous_jB) U₂ DB₂ hs₂ hT₂ x₂) := by
  subst hDB₁; subst hDB₂
  show restrictionMap (pushDatumB U₁ hU₁) E₃ hE₁ (presheafValueMapB U₁ hU₁ x₁) =
    restrictionMap (pushDatumB U₂ hU₂) E₃ hE₂ (presheafValueMapB U₂ hU₂ x₂)
  set hIrat := interDatum_isRational hU₁ hU₂ with hIratdef
  have hsub₁ : rationalOpen (interDatum U₁ U₂ hU₁ hU₂).T
      (interDatum U₁ U₂ hU₁ hU₂).s ⊆ rationalOpen U₁.T U₁.s := by
    rw [rationalOpen_interDatum]
    exact Set.inter_subset_left
  have hsub₂ : rationalOpen (interDatum U₁ U₂ hU₁ hU₂).T
      (interDatum U₁ U₂ hU₁ hU₂).s ⊆ rationalOpen U₂.T U₂.s := by
    rw [rationalOpen_interDatum]
    exact Set.inter_subset_right
  have hpush₁ : rationalOpen (pushDatumB (interDatum U₁ U₂ hU₁ hU₂) hIrat).T
      (pushDatumB (interDatum U₁ U₂ hU₁ hU₂) hIrat).s ⊆
      rationalOpen (pushDatumB U₁ hU₁).T (pushDatumB U₁ hU₁).s := by
    rw [pushDatumB_interOpen]
    exact Set.inter_subset_left
  have hpush₂ : rationalOpen (pushDatumB (interDatum U₁ U₂ hU₁ hU₂) hIrat).T
      (pushDatumB (interDatum U₁ U₂ hU₁ hU₂) hIrat).s ⊆
      rationalOpen (pushDatumB U₂ hU₂).T (pushDatumB U₂ hU₂).s := by
    rw [pushDatumB_interOpen]
    exact Set.inter_subset_right
  have h₃I : rationalOpen E₃.T E₃.s ⊆
      rationalOpen (pushDatumB (interDatum U₁ U₂ hU₁ hU₂) hIrat).T
        (pushDatumB (interDatum U₁ U₂ hU₁ hU₂) hIrat).s := by
    rw [pushDatumB_interOpen]
    exact Set.subset_inter hE₁ hE₂
  have hpushed := congrArg
    (presheafValueMapB (interDatum U₁ U₂ hU₁ hU₂) hIrat)
    (hmatch (interDatum U₁ U₂ hU₁ hU₂) hsub₁ hsub₂)
  rw [presheafValueMapB_restriction U₁ (interDatum U₁ U₂ hU₁ hU₂) hU₁ hIrat
      hsub₁ hpush₁ x₁,
    presheafValueMapB_restriction U₂ (interDatum U₁ U₂ hU₁ hU₂) hU₂ hIrat
      hsub₂ hpush₂ x₂] at hpushed
  have hfac₁ := congrFun (restrictionMap_comp (pushDatumB U₁ hU₁)
    (pushDatumB (interDatum U₁ U₂ hU₁ hU₂) hIrat) E₃ hpush₁ h₃I)
    (presheafValueMapB U₁ hU₁ x₁)
  have hfac₂ := congrFun (restrictionMap_comp (pushDatumB U₂ hU₂)
    (pushDatumB (interDatum U₁ U₂ hU₁ hU₂) hIrat) E₃ hpush₂ h₃I)
    (presheafValueMapB U₂ hU₂ x₂)
  simp only [Function.comp_apply] at hfac₁ hfac₂
  rw [← hfac₁, ← hfac₂, hpushed]

private theorem pushedCompatCAux (U₁ U₂ : RationalLocData (JetA F))
    (hU₁ : U₁.IsRational) (hU₂ : U₂.IsRational)
    {DC₁ DC₂ : RationalLocData (JetC F)}
    (hDC₁ : DC₁ = pushDatumC U₁ hU₁) (hDC₂ : DC₂ = pushDatumC U₂ hU₂)
    (hs₁ : DC₁.s = iotaC F U₁.s) (hT₁ : ∀ t ∈ U₁.T, iotaC F t ∈ DC₁.T)
    (hs₂ : DC₂.s = iotaC F U₂.s) (hT₂ : ∀ t ∈ U₂.T, iotaC F t ∈ DC₂.T)
    (x₁ : presheafValue U₁) (x₂ : presheafValue U₂)
    (hmatch : ∀ (D₃ : RationalLocData (JetA F))
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₁.T U₁.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₂.T U₂.s),
      restrictionMap U₁ D₃ h₃₁ x₁ = restrictionMap U₂ D₃ h₃₂ x₂)
    (E₃ : RationalLocData (JetC F))
    (hE₁ : rationalOpen E₃.T E₃.s ⊆ rationalOpen DC₁.T DC₁.s)
    (hE₂ : rationalOpen E₃.T E₃.s ⊆ rationalOpen DC₂.T DC₂.s) :
    restrictionMap DC₁ E₃ hE₁
        (presheafValueMapOfHom (iotaC F) (continuous_iotaC) U₁ DC₁ hs₁ hT₁ x₁) =
      restrictionMap DC₂ E₃ hE₂
        (presheafValueMapOfHom (iotaC F) (continuous_iotaC) U₂ DC₂ hs₂ hT₂ x₂) := by
  subst hDC₁; subst hDC₂
  show restrictionMap (pushDatumC U₁ hU₁) E₃ hE₁ (presheafValueMapC U₁ hU₁ x₁) =
    restrictionMap (pushDatumC U₂ hU₂) E₃ hE₂ (presheafValueMapC U₂ hU₂ x₂)
  set hIrat := interDatum_isRational hU₁ hU₂ with hIratdef
  have hsub₁ : rationalOpen (interDatum U₁ U₂ hU₁ hU₂).T
      (interDatum U₁ U₂ hU₁ hU₂).s ⊆ rationalOpen U₁.T U₁.s := by
    rw [rationalOpen_interDatum]
    exact Set.inter_subset_left
  have hsub₂ : rationalOpen (interDatum U₁ U₂ hU₁ hU₂).T
      (interDatum U₁ U₂ hU₁ hU₂).s ⊆ rationalOpen U₂.T U₂.s := by
    rw [rationalOpen_interDatum]
    exact Set.inter_subset_right
  have hpush₁ : rationalOpen (pushDatumC (interDatum U₁ U₂ hU₁ hU₂) hIrat).T
      (pushDatumC (interDatum U₁ U₂ hU₁ hU₂) hIrat).s ⊆
      rationalOpen (pushDatumC U₁ hU₁).T (pushDatumC U₁ hU₁).s := by
    rw [pushDatumC_interOpen]
    exact Set.inter_subset_left
  have hpush₂ : rationalOpen (pushDatumC (interDatum U₁ U₂ hU₁ hU₂) hIrat).T
      (pushDatumC (interDatum U₁ U₂ hU₁ hU₂) hIrat).s ⊆
      rationalOpen (pushDatumC U₂ hU₂).T (pushDatumC U₂ hU₂).s := by
    rw [pushDatumC_interOpen]
    exact Set.inter_subset_right
  have h₃I : rationalOpen E₃.T E₃.s ⊆
      rationalOpen (pushDatumC (interDatum U₁ U₂ hU₁ hU₂) hIrat).T
        (pushDatumC (interDatum U₁ U₂ hU₁ hU₂) hIrat).s := by
    rw [pushDatumC_interOpen]
    exact Set.subset_inter hE₁ hE₂
  have hpushed := congrArg
    (presheafValueMapC (interDatum U₁ U₂ hU₁ hU₂) hIrat)
    (hmatch (interDatum U₁ U₂ hU₁ hU₂) hsub₁ hsub₂)
  rw [presheafValueMapC_restriction U₁ (interDatum U₁ U₂ hU₁ hU₂) hU₁ hIrat
      hsub₁ hpush₁ x₁,
    presheafValueMapC_restriction U₂ (interDatum U₁ U₂ hU₁ hU₂) hU₂ hIrat
      hsub₂ hpush₂ x₂] at hpushed
  have hfac₁ := congrFun (restrictionMap_comp (pushDatumC U₁ hU₁)
    (pushDatumC (interDatum U₁ U₂ hU₁ hU₂) hIrat) E₃ hpush₁ h₃I)
    (presheafValueMapC U₁ hU₁ x₁)
  have hfac₂ := congrFun (restrictionMap_comp (pushDatumC U₂ hU₂)
    (pushDatumC (interDatum U₁ U₂ hU₁ hU₂) hIrat) E₃ hpush₂ h₃I)
    (presheafValueMapC U₂ hU₂ x₂)
  simp only [Function.comp_apply] at hfac₁ hfac₂
  rw [← hfac₁, ← hfac₂, hpushed]

/-- **The finite-jet square as a strict Milnor square-with-rows.** -/
noncomputable def jetSquare :
    MilnorSquareData (jB F) (iotaC F) ((rhoC F).comp (iotaC F))
      (continuous_jB) (continuous_iotaC)
      (by rw [RingHom.coe_comp]; exact (continuous_rhoC).comp (continuous_iotaC)) where
  pushB := jetPushB F
  pushC := jetPushC F
  pushD := jetPushD F
  pushB_s := by
    intro U hU
    rw [jetPushB_eq F hU]
    rfl
  pushC_s := by
    intro U hU
    rw [jetPushC_eq F hU]
    rfl
  pushD_s := by
    intro U hU
    rw [jetPushD_eq F hU]
    rfl
  pushB_T := by
    classical
    intro U hU t ht
    rw [jetPushB_eq F hU]
    exact Finset.mem_image_of_mem _ ht
  pushC_T := by
    classical
    intro U hU t ht
    rw [jetPushC_eq F hU]
    exact Finset.mem_image_of_mem _ ht
  pushD_T := by
    classical
    intro U hU t ht
    rw [jetPushD_eq F hU]
    exact Finset.mem_image_of_mem _ ht
  pushB_isRational := by
    intro U hU
    rw [jetPushB_eq F hU]
    exact pushDatumB_isRational hU
  pushC_isRational := by
    intro U hU
    rw [jetPushC_eq F hU]
    exact pushDatumC_isRational hU
  pushD_isRational := by
    intro U hU
    rw [jetPushD_eq F hU]
    exact pushDatumD_isRational hU
  legB := rhoB F
  legC := rhoC F
  hlegB := continuous_rhoB
  hlegC := continuous_rhoC
  legB_s := by
    intro U hU
    rw [jetPushB_eq F hU, jetPushD_eq F hU]
    exact (square_commutes F U.s).symm
  legC_s := by
    intro U hU
    rw [jetPushC_eq F hU, jetPushD_eq F hU]
    rfl
  legB_T := by
    classical
    intro U hU t ht
    rw [jetPushB_eq F hU] at ht
    rw [jetPushD_eq F hU]
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    rw [square_commutes F u]
    exact Finset.mem_image_of_mem _ hu
  legC_T := by
    classical
    intro U hU t ht
    rw [jetPushC_eq F hU] at ht
    rw [jetPushD_eq F hU]
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_image_of_mem _ hu
  row_injective := by
    intro U hU x y hB hC
    exact rowInjectiveAux F U hU (jetPushB_eq F hU) (jetPushC_eq F hU)
      _ _ _ _ x y hB hC
  row_glue := by
    intro U hU b c h
    exact rowGlueAux F U hU (jetPushB_eq F hU) (jetPushC_eq F hU) (jetPushD_eq F hU)
      _ _ _ _ _ _ _ _ b c h
  row_embedding := by
    intro U hU
    exact rowEmbeddingAux F U hU (jetPushB_eq F hU) (jetPushC_eq F hU) _ _ _ _
  pushB_mono := by
    intro U U' hU hU' hsub v hv
    rw [jetPushB_eq F hU'] at hv
    rw [jetPushB_eq F hU]
    have hvspa := rationalOpen_subset_spa hv
    exact (mem_rationalOpen_pushDatumB_iff U hU v hvspa).mpr
      (hsub ((mem_rationalOpen_pushDatumB_iff U' hU' v hvspa).mp hv))
  pushC_mono := by
    intro U U' hU hU' hsub v hv
    rw [jetPushC_eq F hU'] at hv
    rw [jetPushC_eq F hU]
    have hvspa := rationalOpen_subset_spa hv
    exact (mem_rationalOpen_pushDatumC_iff U hU v hvspa).mpr
      (hsub ((mem_rationalOpen_pushDatumC_iff U' hU' v hvspa).mp hv))
  push_natural_B := by
    intro U U' hU hU' h x
    exact presheafValueMapOfHom_restriction (jB F) (continuous_jB) U U'
      (jetPushB F U) (jetPushB F U') _ _ _ _ h _ x
  push_natural_C := by
    intro U U' hU hU' h x
    exact presheafValueMapOfHom_restriction (iotaC F) (continuous_iotaC) U U'
      (jetPushC F U) (jetPushC F U') _ _ _ _ h _ x
  pushB_cover := by
    intro U S hU hS hcov w hw
    rw [jetPushB_eq F hU] at hw
    have hwspa := rationalOpen_subset_spa hw
    obtain ⟨W, hWS, hWmem⟩ := hcov (ValuationSpectrum.comap (jB F) w)
      ((mem_rationalOpen_pushDatumB_iff U hU w hwspa).mp hw)
    refine ⟨W, hWS, ?_⟩
    rw [jetPushB_eq F (hS W hWS)]
    exact (mem_rationalOpen_pushDatumB_iff W (hS W hWS) w hwspa).mpr hWmem
  pushC_cover := by
    intro U S hU hS hcov w hw
    rw [jetPushC_eq F hU] at hw
    have hwspa := rationalOpen_subset_spa hw
    obtain ⟨W, hWS, hWmem⟩ := hcov (ValuationSpectrum.comap (iotaC F) w)
      ((mem_rationalOpen_pushDatumC_iff U hU w hwspa).mp hw)
    refine ⟨W, hWS, ?_⟩
    rw [jetPushC_eq F (hS W hWS)]
    exact (mem_rationalOpen_pushDatumC_iff W (hS W hWS) w hwspa).mpr hWmem
  pushD_cover := by
    intro U S hU hS hcov w hw
    rw [jetPushD_eq F hU] at hw
    have hwspa := rationalOpen_subset_spa hw
    obtain ⟨W, hWS, hWmem⟩ := hcov
      (ValuationSpectrum.comap ((rhoC F).comp (iotaC F)) w)
      ((mem_rationalOpen_pushDatumD_iff U hU w hwspa).mp hw)
    refine ⟨W, hWS, ?_⟩
    rw [jetPushD_eq F (hS W hWS)]
    exact (mem_rationalOpen_pushDatumD_iff W (hS W hWS) w hwspa).mpr hWmem
  pushD_mono := by
    intro U U' hU hU' hsub v hv
    rw [jetPushD_eq F hU'] at hv
    rw [jetPushD_eq F hU]
    have hvspa := rationalOpen_subset_spa hv
    exact (mem_rationalOpen_pushDatumD_iff U hU v hvspa).mpr
      (hsub ((mem_rationalOpen_pushDatumD_iff U' hU' v hvspa).mp hv))
  leg_natural_B := by
    intro U U' hU hU' h b
    exact presheafValueMapOfHom_restriction (rhoB F) (continuous_rhoB)
      (jetPushB F U) (jetPushB F U') (jetPushD F U) (jetPushD F U') _ _ _ _ _ _ b
  leg_natural_C := by
    intro U U' hU hU' h c
    exact presheafValueMapOfHom_restriction (rhoC F) (continuous_rhoC)
      (jetPushC F U) (jetPushC F U') (jetPushD F U) (jetPushD F U') _ _ _ _ _ _ c
  row_comm := by
    intro U hU x
    exact rowCommAux F U hU (jetPushB_eq F hU) (jetPushC_eq F hU) (jetPushD_eq F hU)
      _ _ _ _ _ _ _ _ x
  pushedCompat_B := by
    intro U₁ U₂ hU₁ hU₂ x₁ x₂ hmatch E₃ hE₁ hE₂
    exact pushedCompatBAux F U₁ U₂ hU₁ hU₂ (jetPushB_eq F hU₁) (jetPushB_eq F hU₂)
      _ _ _ _ x₁ x₂ hmatch E₃ hE₁ hE₂
  pushedCompat_C := by
    intro U₁ U₂ hU₁ hU₂ x₁ x₂ hmatch E₃ hE₁ hE₂
    exact pushedCompatCAux F U₁ U₂ hU₁ hU₂ (jetPushC_eq F hU₁) (jetPushC_eq F hU₂)
      _ _ _ _ x₁ x₂ hmatch E₃ hE₁ hE₂

/-- **Regression (T620)**: the finite-jet headline re-derived through the abstract
strict-Milnor-descent criterion — `isSheafy_JetA` from `isSheafy_of_milnorSquare`
at `jetSquare`, consuming only the three vertex sheafinesses. -/
theorem isSheafy_JetA' : ValuationSpectrum.IsSheafy (JetA F) := by
  classical
  exact isSheafy_of_milnorSquare (jB F) (iotaC F) ((rhoC F).comp (iotaC F))
    (continuous_jB) (continuous_iotaC)
    (by rw [RingHom.coe_comp]; exact (continuous_rhoC).comp (continuous_iotaC))
    (jetSquare F) (isSheafy_JetB F) (isSheafy_JetC F) (isSheafy_JetD F)

end FiniteJet
