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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafFunctoriality
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.EmbeddingTopo

/-!
# Abstract Milnor descent for sheafiness (campaign B, AG1.d skeleton)

[WP-paper] lem:sheaf-transfer (l.576–583), verbatim hypothesis: "Suppose that for
every rational domain U ⊂ X_R the section rings satisfy a natural strict exact
sequence 0 → 𝒪_R(U) → 𝒪_B(U_B) ⊕ 𝒪_C(U_C) → 𝒪_D(U_D) → 0. If the Huber pairs
associated with B, C, D are sheafy as complete topological rings, then the Huber
pair associated with R is sheafy as a complete topological ring."

The abstract criterion (reviewer §4.1's "strict Milnor descent") over the generic
value-map machinery of `PresheafFunctoriality.lean`. The bundle `MilnorSquareData`
carries the datum-level pushes explicitly (there is no canonical pushed-datum
constructor in the core; the concrete instantiations — `pushDatumB` etc. in
`FiniteJetFunctoriality.lean`, and their `⟨V⟩`-extensions — supply them), together
with the exactness / strictness / naturality facts the transfer chase consumes.
Instantiations planned: the finite-jet square (regression: re-derive
`isSheafy_JetA`) and the `⟨V₁,…,Vₙ⟩`-extended square (campaign B headline).
-/

@[expose] public section

@[expose] public section

noncomputable section

namespace ValuationSpectrum

open TopologicalRing

universe u

variable {R B C D : Type u}
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [PlusSubring R]
  [IsHuberRing R] [T2Space R] [NonarchimedeanRing R]
  [letI : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R; CompleteSpace R]
  [IsRingOfIntegralElements (R⁺)]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [PlusSubring B]
  [IsHuberRing B] [T2Space B] [NonarchimedeanRing B]
  [letI : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B; CompleteSpace B]
  [IsRingOfIntegralElements (B⁺)]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [PlusSubring C]
  [IsHuberRing C] [T2Space C] [NonarchimedeanRing C]
  [letI : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C; CompleteSpace C]
  [IsRingOfIntegralElements (C⁺)]
  [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [PlusSubring D]
  [IsHuberRing D] [T2Space D] [NonarchimedeanRing D]
  [letI : UniformSpace D := IsTopologicalAddGroup.rightUniformSpace D; CompleteSpace D]
  [IsRingOfIntegralElements (D⁺)]

/-- **The strict Milnor square-with-rows data** ([WP-paper] eq:sheaf-transfer-row,
per rational datum, natural under refinement). Carries the three structural homs,
per-datum pushes to each vertex with their side conditions, and the
exactness/strictness/naturality of
`0 → 𝒪_R(U) → 𝒪_B(U_B) ⊕ 𝒪_C(U_C) → 𝒪_D(U_D) → 0`. -/
structure MilnorSquareData
    (φB : R →+* B) (φC : R →+* C) (φD : R →+* D)
    (hφB : Continuous φB) (hφC : Continuous φC) (hφD : Continuous φD) where
  /-- The pushed datum at each vertex. -/
  pushB : RationalLocData R → RationalLocData B
  pushC : RationalLocData R → RationalLocData C
  pushD : RationalLocData R → RationalLocData D
  pushB_s : ∀ U, U.IsRational → (pushB U).s = φB U.s
  pushC_s : ∀ U, U.IsRational → (pushC U).s = φC U.s
  pushD_s : ∀ U, U.IsRational → (pushD U).s = φD U.s
  pushB_T : ∀ U, U.IsRational → ∀ t ∈ U.T, φB t ∈ (pushB U).T
  pushC_T : ∀ U, U.IsRational → ∀ t ∈ U.T, φC t ∈ (pushC U).T
  pushD_T : ∀ U, U.IsRational → ∀ t ∈ U.T, φD t ∈ (pushD U).T
  /-- Pushes of rational data are rational. -/
  pushB_isRational : ∀ U, U.IsRational → (pushB U).IsRational
  pushC_isRational : ∀ U, U.IsRational → (pushC U).IsRational
  pushD_isRational : ∀ U, U.IsRational → (pushD U).IsRational
  /-- The `D`-vertex maps of the two legs, from the pushed `B`/`C` data. -/
  legB : B →+* D
  legC : C →+* D
  hlegB : Continuous legB
  hlegC : Continuous legC
  legB_s : ∀ U, U.IsRational → (pushD U).s = legB (pushB U).s
  legC_s : ∀ U, U.IsRational → (pushD U).s = legC (pushC U).s
  legB_T : ∀ U, U.IsRational → ∀ t ∈ (pushB U).T, legB t ∈ (pushD U).T
  legC_T : ∀ U, U.IsRational → ∀ t ∈ (pushC U).T, legC t ∈ (pushD U).T
  /-- Row exactness at the left: the pair of value pushes is jointly injective. -/
  row_injective : ∀ (U : RationalLocData R) (hU : U.IsRational),
    ∀ x y : presheafValue U,
      presheafValueMapOfHom φB hφB U (pushB U) (pushB_s U hU) (pushB_T U hU) x =
        presheafValueMapOfHom φB hφB U (pushB U) (pushB_s U hU) (pushB_T U hU) y →
      presheafValueMapOfHom φC hφC U (pushC U) (pushC_s U hU) (pushC_T U hU) x =
        presheafValueMapOfHom φC hφC U (pushC U) (pushC_s U hU) (pushC_T U hU) y →
      x = y
  /-- Row exactness in the middle: a `D`-matching pair comes from the base. -/
  row_glue : ∀ (U : RationalLocData R) (hU : U.IsRational),
    ∀ (b : presheafValue (pushB U)) (c : presheafValue (pushC U)),
      presheafValueMapOfHom legB hlegB (pushB U) (pushD U) (legB_s U hU)
          (legB_T U hU) b =
        presheafValueMapOfHom legC hlegC (pushC U) (pushD U) (legC_s U hU)
          (legC_T U hU) c →
      ∃ x : presheafValue U,
        presheafValueMapOfHom φB hφB U (pushB U) (pushB_s U hU) (pushB_T U hU) x = b ∧
        presheafValueMapOfHom φC hφC U (pushC U) (pushC_s U hU) (pushC_T U hU) x = c
  /-- Strictness at the left: the base embeds topologically in the product. -/
  row_embedding : ∀ (U : RationalLocData R) (hU : U.IsRational),
    Topology.IsEmbedding (fun x : presheafValue U =>
      (presheafValueMapOfHom φB hφB U (pushB U) (pushB_s U hU) (pushB_T U hU) x,
       presheafValueMapOfHom φC hφC U (pushC U) (pushC_s U hU) (pushC_T U hU) x))
  /-- Naturality under refinement: pushes commute with restriction maps, and the
  pushed datum of a refinement refines the pushed datum. -/
  pushB_mono : ∀ (U U' : RationalLocData R), U.IsRational → U'.IsRational →
    rationalOpen U'.T U'.s ⊆ rationalOpen U.T U.s →
    rationalOpen (pushB U').T (pushB U').s ⊆ rationalOpen (pushB U).T (pushB U).s
  pushC_mono : ∀ (U U' : RationalLocData R), U.IsRational → U'.IsRational →
    rationalOpen U'.T U'.s ⊆ rationalOpen U.T U.s →
    rationalOpen (pushC U').T (pushC U').s ⊆ rationalOpen (pushC U).T (pushC U).s
  push_natural_B : ∀ (U U' : RationalLocData R) (hU : U.IsRational)
    (hU' : U'.IsRational)
    (h : rationalOpen U'.T U'.s ⊆ rationalOpen U.T U.s) (x : presheafValue U),
    presheafValueMapOfHom φB hφB U' (pushB U') (pushB_s U' hU') (pushB_T U' hU')
        (restrictionMap U U' h x) =
      restrictionMap (pushB U) (pushB U') (pushB_mono U U' hU hU' h)
        (presheafValueMapOfHom φB hφB U (pushB U) (pushB_s U hU) (pushB_T U hU) x)
  push_natural_C : ∀ (U U' : RationalLocData R) (hU : U.IsRational)
    (hU' : U'.IsRational)
    (h : rationalOpen U'.T U'.s ⊆ rationalOpen U.T U.s) (x : presheafValue U),
    presheafValueMapOfHom φC hφC U' (pushC U') (pushC_s U' hU') (pushC_T U' hU')
        (restrictionMap U U' h x) =
      restrictionMap (pushC U) (pushC U') (pushC_mono U U' hU hU' h)
        (presheafValueMapOfHom φC hφC U (pushC U) (pushC_s U hU) (pushC_T U hU) x)
  /-- Covering transport: the pushes of the pieces of a rational cover of `U`
  cover the pushed base (the paper's `U_E = p_E⁻¹(U)` gets this for free;
  abstract pushes must carry it). -/
  pushB_cover : ∀ (U : RationalLocData R) (S : Finset (RationalLocData R)),
    U.IsRational → (∀ W ∈ S, RationalLocData.IsRational W) →
    (∀ v, v ∈ rationalOpen U.T U.s → ∃ W ∈ S, v ∈ rationalOpen W.T W.s) →
    ∀ w, w ∈ rationalOpen (pushB U).T (pushB U).s →
      ∃ W ∈ S, w ∈ rationalOpen (pushB W).T (pushB W).s
  pushC_cover : ∀ (U : RationalLocData R) (S : Finset (RationalLocData R)),
    U.IsRational → (∀ W ∈ S, RationalLocData.IsRational W) →
    (∀ v, v ∈ rationalOpen U.T U.s → ∃ W ∈ S, v ∈ rationalOpen W.T W.s) →
    ∀ w, w ∈ rationalOpen (pushC U).T (pushC U).s →
      ∃ W ∈ S, w ∈ rationalOpen (pushC W).T (pushC W).s
  pushD_cover : ∀ (U : RationalLocData R) (S : Finset (RationalLocData R)),
    U.IsRational → (∀ W ∈ S, RationalLocData.IsRational W) →
    (∀ v, v ∈ rationalOpen U.T U.s → ∃ W ∈ S, v ∈ rationalOpen W.T W.s) →
    ∀ w, w ∈ rationalOpen (pushD U).T (pushD U).s →
      ∃ W ∈ S, w ∈ rationalOpen (pushD W).T (pushD W).s
  /-- The pushed datum of a refinement refines at the `D`-vertex too. -/
  pushD_mono : ∀ (U U' : RationalLocData R), U.IsRational → U'.IsRational →
    rationalOpen U'.T U'.s ⊆ rationalOpen U.T U.s →
    rationalOpen (pushD U').T (pushD U').s ⊆ rationalOpen (pushD U).T (pushD U).s
  /-- Leg naturality: the `B → D` leg's value map commutes with restrictions of
  pushed data. -/
  leg_natural_B : ∀ (U U' : RationalLocData R) (hU : U.IsRational)
    (hU' : U'.IsRational)
    (h : rationalOpen U'.T U'.s ⊆ rationalOpen U.T U.s)
    (b : presheafValue (pushB U)),
    presheafValueMapOfHom legB hlegB (pushB U') (pushD U') (legB_s U' hU')
        (legB_T U' hU')
        (restrictionMap (pushB U) (pushB U') (pushB_mono U U' hU hU' h) b) =
      restrictionMap (pushD U) (pushD U') (pushD_mono U U' hU hU' h)
        (presheafValueMapOfHom legB hlegB (pushB U) (pushD U) (legB_s U hU)
          (legB_T U hU) b)
  leg_natural_C : ∀ (U U' : RationalLocData R) (hU : U.IsRational)
    (hU' : U'.IsRational)
    (h : rationalOpen U'.T U'.s ⊆ rationalOpen U.T U.s)
    (c : presheafValue (pushC U)),
    presheafValueMapOfHom legC hlegC (pushC U') (pushD U') (legC_s U' hU')
        (legC_T U' hU')
        (restrictionMap (pushC U) (pushC U') (pushC_mono U U' hU hU' h) c) =
      restrictionMap (pushD U) (pushD U') (pushD_mono U U' hU hU' h)
        (presheafValueMapOfHom legC hlegC (pushC U) (pushD U) (legC_s U hU)
          (legC_T U hU) c)
  /-- The value-level commuting square: both composites `𝒪(U) → 𝒪(U_D)` agree. -/
  row_comm : ∀ (U : RationalLocData R) (hU : U.IsRational) (x : presheafValue U),
    presheafValueMapOfHom legB hlegB (pushB U) (pushD U) (legB_s U hU) (legB_T U hU)
        (presheafValueMapOfHom φB hφB U (pushB U) (pushB_s U hU) (pushB_T U hU) x) =
      presheafValueMapOfHom legC hlegC (pushC U) (pushD U) (legC_s U hU) (legC_T U hU)
        (presheafValueMapOfHom φC hφC U (pushC U) (pushC_s U hU) (pushC_T U hU) x)
  /-- Compat transport at the `B`-vertex: `R`-level matching of two local sections
  implies `B`-level matching of their pushes over arbitrary common `B`-refinements
  (the instantiations discharge this via "push of intersection = intersection of
  pushes", cf. `pushedCompatB` in `FiniteJetSheafTransfer.lean`). -/
  pushedCompat_B : ∀ (U₁ U₂ : RationalLocData R) (hU₁ : U₁.IsRational)
    (hU₂ : U₂.IsRational),
    ∀ (x₁ : presheafValue U₁) (x₂ : presheafValue U₂),
    (∀ (D₃ : RationalLocData R)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₁.T U₁.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₂.T U₂.s),
      restrictionMap U₁ D₃ h₃₁ x₁ = restrictionMap U₂ D₃ h₃₂ x₂) →
    ∀ (E₃ : RationalLocData B)
      (hE₁ : rationalOpen E₃.T E₃.s ⊆ rationalOpen (pushB U₁).T (pushB U₁).s)
      (hE₂ : rationalOpen E₃.T E₃.s ⊆ rationalOpen (pushB U₂).T (pushB U₂).s),
      restrictionMap (pushB U₁) E₃ hE₁
          (presheafValueMapOfHom φB hφB U₁ (pushB U₁) (pushB_s U₁ hU₁)
            (pushB_T U₁ hU₁) x₁) =
        restrictionMap (pushB U₂) E₃ hE₂
          (presheafValueMapOfHom φB hφB U₂ (pushB U₂) (pushB_s U₂ hU₂)
            (pushB_T U₂ hU₂) x₂)
  pushedCompat_C : ∀ (U₁ U₂ : RationalLocData R) (hU₁ : U₁.IsRational)
    (hU₂ : U₂.IsRational),
    ∀ (x₁ : presheafValue U₁) (x₂ : presheafValue U₂),
    (∀ (D₃ : RationalLocData R)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₁.T U₁.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₂.T U₂.s),
      restrictionMap U₁ D₃ h₃₁ x₁ = restrictionMap U₂ D₃ h₃₂ x₂) →
    ∀ (E₃ : RationalLocData C)
      (hE₁ : rationalOpen E₃.T E₃.s ⊆ rationalOpen (pushC U₁).T (pushC U₁).s)
      (hE₂ : rationalOpen E₃.T E₃.s ⊆ rationalOpen (pushC U₂).T (pushC U₂).s),
      restrictionMap (pushC U₁) E₃ hE₁
          (presheafValueMapOfHom φC hφC U₁ (pushC U₁) (pushC_s U₁ hU₁)
            (pushC_T U₁ hU₁) x₁) =
        restrictionMap (pushC U₂) E₃ hE₂
          (presheafValueMapOfHom φC hφC U₂ (pushC U₂) (pushC_s U₂ hU₂)
            (pushC_T U₂ hU₂) x₂)

namespace MilnorSquareData

variable {φB : R →+* B} {φC : R →+* C} {φD : R →+* D}
  {hφB : Continuous φB} {hφC : Continuous φC} {hφD : Continuous φD}
  [DecidableEq (RationalLocData B)] [DecidableEq (RationalLocData C)]
  [DecidableEq (RationalLocData D)]

/-- The pushed covering at the `B`-vertex. -/
noncomputable def pushCoveringB (sq : MilnorSquareData φB φC φD hφB hφC hφD)
    (C₀ : RationalCoveringData R) (hC₀ : C₀.IsRational) : RationalCoveringData B where
  base := sq.pushB C₀.base
  covers := C₀.covers.image sq.pushB
  hsubset := by
    intro E hE
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hE
    exact sq.pushB_mono C₀.base W hC₀.1 (hC₀.piece hW) (C₀.hsubset W hW)
  hcover := by
    intro w hw
    obtain ⟨W, hW, hwW⟩ := sq.pushB_cover C₀.base C₀.covers hC₀.1
      (fun W hW => hC₀.piece hW) C₀.hcover w hw
    exact ⟨sq.pushB W, Finset.mem_image_of_mem _ hW, hwW⟩

/-- The pushed covering at the `C`-vertex. -/
noncomputable def pushCoveringC (sq : MilnorSquareData φB φC φD hφB hφC hφD)
    (C₀ : RationalCoveringData R) (hC₀ : C₀.IsRational) : RationalCoveringData C where
  base := sq.pushC C₀.base
  covers := C₀.covers.image sq.pushC
  hsubset := by
    intro E hE
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hE
    exact sq.pushC_mono C₀.base W hC₀.1 (hC₀.piece hW) (C₀.hsubset W hW)
  hcover := by
    intro w hw
    obtain ⟨W, hW, hwW⟩ := sq.pushC_cover C₀.base C₀.covers hC₀.1
      (fun W hW => hC₀.piece hW) C₀.hcover w hw
    exact ⟨sq.pushC W, Finset.mem_image_of_mem _ hW, hwW⟩

theorem pushCoveringB_isRational (sq : MilnorSquareData φB φC φD hφB hφC hφD)
    {C₀ : RationalCoveringData R} (hC₀ : C₀.IsRational) :
    (sq.pushCoveringB C₀ hC₀).IsRational := by
  refine ⟨sq.pushB_isRational C₀.base hC₀.1, ?_⟩
  intro E hE
  obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hE
  exact sq.pushB_isRational W (hC₀.piece hW)

theorem pushCoveringC_isRational (sq : MilnorSquareData φB φC φD hφB hφC hφD)
    {C₀ : RationalCoveringData R} (hC₀ : C₀.IsRational) :
    (sq.pushCoveringC C₀ hC₀).IsRational := by
  refine ⟨sq.pushC_isRational C₀.base hC₀.1, ?_⟩
  intro E hE
  obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hE
  exact sq.pushC_isRational W (hC₀.piece hW)

/-- The pushed covering at the `D`-vertex. -/
noncomputable def pushCoveringD (sq : MilnorSquareData φB φC φD hφB hφC hφD)
    (C₀ : RationalCoveringData R) (hC₀ : C₀.IsRational) : RationalCoveringData D where
  base := sq.pushD C₀.base
  covers := C₀.covers.image sq.pushD
  hsubset := by
    intro E hE
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hE
    exact sq.pushD_mono C₀.base W hC₀.1 (hC₀.piece hW) (C₀.hsubset W hW)
  hcover := by
    intro w hw
    obtain ⟨W, hW, hwW⟩ := sq.pushD_cover C₀.base C₀.covers hC₀.1
      (fun W hW => hC₀.piece hW) C₀.hcover w hw
    exact ⟨sq.pushD W, Finset.mem_image_of_mem _ hW, hwW⟩

theorem pushCoveringD_isRational (sq : MilnorSquareData φB φC φD hφB hφC hφD)
    {C₀ : RationalCoveringData R} (hC₀ : C₀.IsRational) :
    (sq.pushCoveringD C₀ hC₀).IsRational := by
  refine ⟨sq.pushD_isRational C₀.base hC₀.1, ?_⟩
  intro E hE
  obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hE
  exact sq.pushD_isRational W (hC₀.piece hW)

/-- Restriction of a transported value equals restriction of the value
(eliminated by `subst`; the two subset proofs are proof-irrelevant). -/
theorem cast_restrictionMap_B {X E : RationalLocData B} (heq : X = E)
    {D₃ : RationalLocData B}
    (h : rationalOpen D₃.T D₃.s ⊆ rationalOpen E.T E.s)
    (h' : rationalOpen D₃.T D₃.s ⊆ rationalOpen X.T X.s)
    (v : presheafValue X) :
    restrictionMap E D₃ h (heq ▸ v) = restrictionMap X D₃ h' v := by
  subst heq
  rfl

theorem cast_restrictionMap_C {X E : RationalLocData C} (heq : X = E)
    {D₃ : RationalLocData C}
    (h : rationalOpen D₃.T D₃.s ⊆ rationalOpen E.T E.s)
    (h' : rationalOpen D₃.T D₃.s ⊆ rationalOpen X.T X.s)
    (v : presheafValue X) :
    restrictionMap E D₃ h (heq ▸ v) = restrictionMap X D₃ h' v := by
  subst heq
  rfl

/-- Transport along an equality of data is continuous (eliminated by `subst`). -/
theorem cast_continuous {D₁ D₂ : RationalLocData B} (h : D₁ = D₂) :
    Continuous (fun v : presheafValue D₁ => h ▸ v : presheafValue D₁ → presheafValue D₂) := by
  subst h
  exact continuous_id

/-- Transport along an equality of `C`-data is continuous. -/
theorem cast_continuous_C {D₁ D₂ : RationalLocData C} (h : D₁ = D₂) :
    Continuous (fun v : presheafValue D₁ => h ▸ v : presheafValue D₁ → presheafValue D₂) := by
  subst h
  exact continuous_id

/-- Cast-compatibility of the `B`-leg push with restriction: the transported
per-piece row equals the restriction of the base row (the ▸ is eliminated by
substituting the free target datum). -/
theorem cast_push_restriction_B (sq : MilnorSquareData φB φC φD hφB hφC hφD)
    {U W : RationalLocData R} (hU : U.IsRational) (hW : W.IsRational)
    (hWsub : rationalOpen W.T W.s ⊆ rationalOpen U.T U.s)
    {E : RationalLocData B} (h : sq.pushB W = E)
    (hEsub : rationalOpen E.T E.s ⊆
      rationalOpen (sq.pushB U).T (sq.pushB U).s)
    (x : presheafValue U) :
    h ▸ (presheafValueMapOfHom φB hφB W (sq.pushB W) (sq.pushB_s W hW)
        (sq.pushB_T W hW) (restrictionMap U W hWsub x)) =
      restrictionMap (sq.pushB U) E hEsub
        (presheafValueMapOfHom φB hφB U (sq.pushB U) (sq.pushB_s U hU)
          (sq.pushB_T U hU) x) := by
  subst h
  exact sq.push_natural_B U W hU hW hWsub x

/-- Cast-compatibility of the `C`-leg push with restriction. -/
theorem cast_push_restriction_C (sq : MilnorSquareData φB φC φD hφB hφC hφD)
    {U W : RationalLocData R} (hU : U.IsRational) (hW : W.IsRational)
    (hWsub : rationalOpen W.T W.s ⊆ rationalOpen U.T U.s)
    {E : RationalLocData C} (h : sq.pushC W = E)
    (hEsub : rationalOpen E.T E.s ⊆
      rationalOpen (sq.pushC U).T (sq.pushC U).s)
    (x : presheafValue U) :
    h ▸ (presheafValueMapOfHom φC hφC W (sq.pushC W) (sq.pushC_s W hW)
        (sq.pushC_T W hW) (restrictionMap U W hWsub x)) =
      restrictionMap (sq.pushC U) E hEsub
        (presheafValueMapOfHom φC hφC U (sq.pushC U) (sq.pushC_s U hU)
          (sq.pushC_T U hU) x) := by
  subst h
  exact sq.push_natural_C U W hU hW hWsub x

end MilnorSquareData

/-- **Abstract Milnor descent for sheafiness** ([WP-paper] lem:sheaf-transfer;
reviewer §4.1): if a strict Milnor square-with-rows exists over `R` and the three
vertices `B`, `C`, `D` are sheafy, then `R` is sheafy. -/
theorem isSheafy_of_milnorSquare
    [DecidableEq (RationalLocData B)] [DecidableEq (RationalLocData C)]
    [DecidableEq (RationalLocData D)]
    (φB : R →+* B) (φC : R →+* C) (φD : R →+* D)
    (hφB : Continuous φB) (hφC : Continuous φC) (hφD : Continuous φD)
    (sq : MilnorSquareData φB φC φD hφB hφC hφD)
    (hB : IsSheafy B) (hC : IsSheafy C) (hD : IsSheafy D) :
    IsSheafy R := by
  constructor
  · -- Embedding half ([WP-paper] l.600–612): factor the product restriction of `R`
    -- through the vertex product restrictions via the row, then `of_comp`.
    intro C₀ hC₀
    -- component selection for the image-indexed pushed covers
    have hselB : ∀ E : ↥(sq.pushCoveringB C₀ hC₀).covers,
        ∃ W : ↥C₀.covers, sq.pushB W.1 = E.1 := by
      rintro ⟨E, hE⟩
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hE
      exact ⟨⟨W, hW⟩, rfl⟩
    have hselC : ∀ E : ↥(sq.pushCoveringC C₀ hC₀).covers,
        ∃ W : ↥C₀.covers, sq.pushC W.1 = E.1 := by
      rintro ⟨E, hE⟩
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hE
      exact ⟨⟨W, hW⟩, rfl⟩
    choose selB hselB_eq using hselB
    choose selC hselC_eq using hselC
    -- the factoring map g: per-piece rows followed by component selection
    set g : (∀ W : ↥C₀.covers, presheafValue W.1) →
        (∀ E : ↥(sq.pushCoveringB C₀ hC₀).covers, presheafValue E.1) ×
        (∀ E : ↥(sq.pushCoveringC C₀ hC₀).covers, presheafValue E.1) := fun s =>
      (fun E => (hselB_eq E) ▸
          presheafValueMapOfHom φB hφB (selB E).1 (sq.pushB (selB E).1)
            (sq.pushB_s (selB E).1 (hC₀.piece (selB E).2))
            (sq.pushB_T (selB E).1 (hC₀.piece (selB E).2)) (s (selB E)),
       fun E => (hselC_eq E) ▸
          presheafValueMapOfHom φC hφC (selC E).1 (sq.pushC (selC E).1)
            (sq.pushC_s (selC E).1 (hC₀.piece (selC E).2))
            (sq.pushC_T (selC E).1 (hC₀.piece (selC E).2)) (s (selC E))) with hg
    -- g ∘ productRestrictionSub R C₀ = (vertex product restrictions) ∘ (base row)
    have hfact : ∀ x : presheafValue C₀.base,
        g (productRestrictionSub R C₀ x) =
          (productRestrictionSub B (sq.pushCoveringB C₀ hC₀)
            (presheafValueMapOfHom φB hφB C₀.base (sq.pushB C₀.base)
              (sq.pushB_s C₀.base hC₀.1) (sq.pushB_T C₀.base hC₀.1) x),
           productRestrictionSub C (sq.pushCoveringC C₀ hC₀)
            (presheafValueMapOfHom φC hφC C₀.base (sq.pushC C₀.base)
              (sq.pushC_s C₀.base hC₀.1) (sq.pushC_T C₀.base hC₀.1) x)) := by
      intro x
      refine Prod.ext (funext fun E => ?_) (funext fun E => ?_)
      · simp only [hg]
        exact sq.cast_push_restriction_B hC₀.1 (hC₀.piece (selB E).2)
          (C₀.hsubset _ (selB E).2) (hselB_eq E)
          ((sq.pushCoveringB C₀ hC₀).hsubset E.1 E.2) x
      · simp only [hg]
        exact sq.cast_push_restriction_C hC₀.1 (hC₀.piece (selC E).2)
          (C₀.hsubset _ (selC E).2) (hselC_eq E)
          ((sq.pushCoveringC C₀ hC₀).hsubset E.1 E.2) x
    have hg_cont : Continuous g := by
      rw [hg]
      refine Continuous.prodMk (continuous_pi fun E => ?_) (continuous_pi fun E => ?_)
      · exact (MilnorSquareData.cast_continuous (hselB_eq E)).comp
          ((presheafValueMapOfHom_continuous φB hφB _ _ _ _).comp (continuous_apply _))
      · exact (MilnorSquareData.cast_continuous_C (hselC_eq E)).comp
          ((presheafValueMapOfHom_continuous φC hφC _ _ _ _).comp (continuous_apply _))
    have hgf : Topology.IsEmbedding (g ∘ productRestrictionSub R C₀) := by
      have heq : (g ∘ productRestrictionSub R C₀) =
          (fun q : (presheafValue (sq.pushB C₀.base)) ×
              (presheafValue (sq.pushC C₀.base)) =>
            (productRestrictionSub B (sq.pushCoveringB C₀ hC₀) q.1,
             productRestrictionSub C (sq.pushCoveringC C₀ hC₀) q.2)) ∘
          (fun x : presheafValue C₀.base =>
            (presheafValueMapOfHom φB hφB C₀.base (sq.pushB C₀.base)
              (sq.pushB_s C₀.base hC₀.1) (sq.pushB_T C₀.base hC₀.1) x,
             presheafValueMapOfHom φC hφC C₀.base (sq.pushC C₀.base)
              (sq.pushC_s C₀.base hC₀.1) (sq.pushC_T C₀.base hC₀.1) x)) := by
        funext x
        exact hfact x
      rw [heq]
      exact ((hB.embedding _ (sq.pushCoveringB_isRational hC₀)).prodMap
        (hC.embedding _ (sq.pushCoveringC_isRational hC₀))).comp
        (sq.row_embedding C₀.base hC₀.1)
    exact Topology.IsEmbedding.of_comp
      (continuous_pi fun W => restrictionMapHom_continuous C₀.base W.1
        (C₀.hsubset W.1 W.2))
      hg_cont hgf
  · -- Gluing half ([WP-paper] l.613–627): push, glue at the vertices, compare in
    -- `D` by separation, descend by `row_glue`, recover per-piece by
    -- `row_injective`.
    intro C₀ hC₀ f hcompat
    classical
    have hselB : ∀ E : ↥(sq.pushCoveringB C₀ hC₀).covers,
        ∃ W : ↥C₀.covers, sq.pushB W.1 = E.1 := by
      rintro ⟨E, hE⟩
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hE
      exact ⟨⟨W, hW⟩, rfl⟩
    have hselC : ∀ E : ↥(sq.pushCoveringC C₀ hC₀).covers,
        ∃ W : ↥C₀.covers, sq.pushC W.1 = E.1 := by
      rintro ⟨E, hE⟩
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hE
      exact ⟨⟨W, hW⟩, rfl⟩
    choose selB hselB_eq using hselB
    choose selC hselC_eq using hselC
    -- the pushed families
    set fB : ∀ E : ↥(sq.pushCoveringB C₀ hC₀).covers, presheafValue E.1 := fun E =>
      (hselB_eq E) ▸ (presheafValueMapOfHom φB hφB (selB E).1 (sq.pushB (selB E).1)
        (sq.pushB_s _ (hC₀.piece (selB E).2)) (sq.pushB_T _ (hC₀.piece (selB E).2))
        (f (selB E))) with hfB
    set fC : ∀ E : ↥(sq.pushCoveringC C₀ hC₀).covers, presheafValue E.1 := fun E =>
      (hselC_eq E) ▸ (presheafValueMapOfHom φC hφC (selC E).1 (sq.pushC (selC E).1)
        (sq.pushC_s _ (hC₀.piece (selC E).2)) (sq.pushC_T _ (hC₀.piece (selC E).2))
        (f (selC E))) with hfC
    -- compatibility of the pushed families, from the compat transports
    have hfBcompat : ∀ (E₁ E₂ : ↥(sq.pushCoveringB C₀ hC₀).covers)
        (D₃ : RationalLocData B)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
        restrictionMap E₁.1 D₃ h₃₁ (fB E₁) = restrictionMap E₂.1 D₃ h₃₂ (fB E₂) := by
      intro E₁ E₂ D₃ h₃₁ h₃₂
      simp only [hfB]
      rw [MilnorSquareData.cast_restrictionMap_B (hselB_eq E₁) h₃₁
          (by rw [hselB_eq E₁]; exact h₃₁),
        MilnorSquareData.cast_restrictionMap_B (hselB_eq E₂) h₃₂
          (by rw [hselB_eq E₂]; exact h₃₂)]

      exact sq.pushedCompat_B (selB E₁).1 (selB E₂).1 (hC₀.piece (selB E₁).2)
        (hC₀.piece (selB E₂).2) (f (selB E₁)) (f (selB E₂))
        (fun D₃' h₁ h₂ => hcompat (selB E₁) (selB E₂) D₃' h₁ h₂) D₃ _ _
    have hfCcompat : ∀ (E₁ E₂ : ↥(sq.pushCoveringC C₀ hC₀).covers)
        (D₃ : RationalLocData C)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
        restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂) := by
      intro E₁ E₂ D₃ h₃₁ h₃₂
      simp only [hfC]
      rw [MilnorSquareData.cast_restrictionMap_C (hselC_eq E₁) h₃₁
          (by rw [hselC_eq E₁]; exact h₃₁),
        MilnorSquareData.cast_restrictionMap_C (hselC_eq E₂) h₃₂
          (by rw [hselC_eq E₂]; exact h₃₂)]
      exact sq.pushedCompat_C (selC E₁).1 (selC E₂).1 (hC₀.piece (selC E₁).2)
        (hC₀.piece (selC E₂).2) (f (selC E₁)) (f (selC E₂))
        (fun D₃' h₁ h₂ => hcompat (selC E₁) (selC E₂) D₃' h₁ h₂) D₃ _ _
    -- glue at the B and C vertices
    obtain ⟨b, hb⟩ := hB.gluing _ (sq.pushCoveringB_isRational hC₀) fB hfBcompat
    obtain ⟨c, hc⟩ := hC.gluing _ (sq.pushCoveringC_isRational hC₀) fC hfCcompat
    -- normalize the glued sections' restrictions at genuine pushes
    have hb_at : ∀ (W : ↥C₀.covers),
        restrictionMap (sq.pushB C₀.base) (sq.pushB W.1)
            (sq.pushB_mono C₀.base W.1 hC₀.1 (hC₀.piece W.2)
              (C₀.hsubset W.1 W.2)) b =
          presheafValueMapOfHom φB hφB W.1 (sq.pushB W.1)
            (sq.pushB_s _ (hC₀.piece W.2)) (sq.pushB_T _ (hC₀.piece W.2)) (f W) := by
      intro W
      have hbW := hb ⟨sq.pushB W.1, Finset.mem_image_of_mem _ W.2⟩
      rw [show restrictionMap (sq.pushB C₀.base) (sq.pushB W.1)
            (sq.pushB_mono C₀.base W.1 hC₀.1 (hC₀.piece W.2)
              (C₀.hsubset W.1 W.2)) b =
          restrictionMap (sq.pushCoveringB C₀ hC₀).base (sq.pushB W.1)
            ((sq.pushCoveringB C₀ hC₀).hsubset _ (Finset.mem_image_of_mem _ W.2)) b from rfl,
        hbW]
      set P : ↥(sq.pushCoveringB C₀ hC₀).covers :=
        ⟨sq.pushB W.1, Finset.mem_image_of_mem _ W.2⟩ with hP
      have hcomp := sq.pushedCompat_B (selB P).1 W.1 (hC₀.piece (selB P).2)
        (hC₀.piece W.2) (f (selB P)) (f W)
        (fun D₃' h₁ h₂ => hcompat (selB P) W D₃' h₁ h₂) (sq.pushB W.1)
        (by rw [hselB_eq P]) (le_refl _)
      calc fB P
          = restrictionMap P.1 (sq.pushB W.1) (le_refl _) (fB P) :=
            (congrFun (restrictionMap_id (sq.pushB W.1)) _).symm
        _ = restrictionMap (sq.pushB (selB P).1) (sq.pushB W.1)
              (by rw [hselB_eq P])
              (presheafValueMapOfHom φB hφB (selB P).1 (sq.pushB (selB P).1)
                (sq.pushB_s _ (hC₀.piece (selB P).2))
                (sq.pushB_T _ (hC₀.piece (selB P).2)) (f (selB P))) := by
            simp only [hfB]
            exact MilnorSquareData.cast_restrictionMap_B (hselB_eq P) _ _ _
        _ = restrictionMap (sq.pushB W.1) (sq.pushB W.1) (le_refl _)
              (presheafValueMapOfHom φB hφB W.1 (sq.pushB W.1)
                (sq.pushB_s _ (hC₀.piece W.2)) (sq.pushB_T _ (hC₀.piece W.2))
                (f W)) := hcomp
        _ = presheafValueMapOfHom φB hφB W.1 (sq.pushB W.1)
              (sq.pushB_s _ (hC₀.piece W.2)) (sq.pushB_T _ (hC₀.piece W.2)) (f W) :=
            congrFun (restrictionMap_id (sq.pushB W.1)) _
    have hc_at : ∀ (W : ↥C₀.covers),
        restrictionMap (sq.pushC C₀.base) (sq.pushC W.1)
            (sq.pushC_mono C₀.base W.1 hC₀.1 (hC₀.piece W.2)
              (C₀.hsubset W.1 W.2)) c =
          presheafValueMapOfHom φC hφC W.1 (sq.pushC W.1)
            (sq.pushC_s _ (hC₀.piece W.2)) (sq.pushC_T _ (hC₀.piece W.2)) (f W) := by
      intro W
      have hcW := hc ⟨sq.pushC W.1, Finset.mem_image_of_mem _ W.2⟩
      rw [show restrictionMap (sq.pushC C₀.base) (sq.pushC W.1)
            (sq.pushC_mono C₀.base W.1 hC₀.1 (hC₀.piece W.2)
              (C₀.hsubset W.1 W.2)) c =
          restrictionMap (sq.pushCoveringC C₀ hC₀).base (sq.pushC W.1)
            ((sq.pushCoveringC C₀ hC₀).hsubset _ (Finset.mem_image_of_mem _ W.2)) c from rfl,
        hcW]
      set P : ↥(sq.pushCoveringC C₀ hC₀).covers :=
        ⟨sq.pushC W.1, Finset.mem_image_of_mem _ W.2⟩ with hP
      have hcomp := sq.pushedCompat_C (selC P).1 W.1 (hC₀.piece (selC P).2)
        (hC₀.piece W.2) (f (selC P)) (f W)
        (fun D₃' h₁ h₂ => hcompat (selC P) W D₃' h₁ h₂) (sq.pushC W.1)
        (by rw [hselC_eq P]) (le_refl _)
      calc fC P
          = restrictionMap P.1 (sq.pushC W.1) (le_refl _) (fC P) :=
            (congrFun (restrictionMap_id (sq.pushC W.1)) _).symm
        _ = restrictionMap (sq.pushC (selC P).1) (sq.pushC W.1)
              (by rw [hselC_eq P])
              (presheafValueMapOfHom φC hφC (selC P).1 (sq.pushC (selC P).1)
                (sq.pushC_s _ (hC₀.piece (selC P).2))
                (sq.pushC_T _ (hC₀.piece (selC P).2)) (f (selC P))) := by
            simp only [hfC]
            exact MilnorSquareData.cast_restrictionMap_C (hselC_eq P) _ _ _
        _ = restrictionMap (sq.pushC W.1) (sq.pushC W.1) (le_refl _)
              (presheafValueMapOfHom φC hφC W.1 (sq.pushC W.1)
                (sq.pushC_s _ (hC₀.piece W.2)) (sq.pushC_T _ (hC₀.piece W.2))
                (f W)) := hcomp
        _ = presheafValueMapOfHom φC hφC W.1 (sq.pushC W.1)
              (sq.pushC_s _ (hC₀.piece W.2)) (sq.pushC_T _ (hC₀.piece W.2)) (f W) :=
            congrFun (restrictionMap_id (sq.pushC W.1)) _
    -- D-comparison: the two leg-images of the glued sections agree, by separation
    have hd : presheafValueMapOfHom sq.legB sq.hlegB (sq.pushB C₀.base)
        (sq.pushD C₀.base) (sq.legB_s C₀.base hC₀.1) (sq.legB_T C₀.base hC₀.1) b =
      presheafValueMapOfHom sq.legC sq.hlegC (sq.pushC C₀.base)
        (sq.pushD C₀.base) (sq.legC_s C₀.base hC₀.1) (sq.legC_T C₀.base hC₀.1) c := by
      apply (hD.embedding _ (sq.pushCoveringD_isRational hC₀)).injective
      funext E
      obtain ⟨E, hE⟩ := E
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hE
      show restrictionMap (sq.pushD C₀.base) (sq.pushD W)
          (sq.pushD_mono C₀.base W hC₀.1 (hC₀.piece hW) (C₀.hsubset W hW))
          (presheafValueMapOfHom sq.legB sq.hlegB (sq.pushB C₀.base)
            (sq.pushD C₀.base) (sq.legB_s C₀.base hC₀.1) (sq.legB_T C₀.base hC₀.1) b) =
        restrictionMap (sq.pushD C₀.base) (sq.pushD W)
          (sq.pushD_mono C₀.base W hC₀.1 (hC₀.piece hW) (C₀.hsubset W hW))
          (presheafValueMapOfHom sq.legC sq.hlegC (sq.pushC C₀.base)
            (sq.pushD C₀.base) (sq.legC_s C₀.base hC₀.1) (sq.legC_T C₀.base hC₀.1) c)
      rw [← sq.leg_natural_B C₀.base W hC₀.1 (hC₀.piece hW) (C₀.hsubset W hW) b,
        ← sq.leg_natural_C C₀.base W hC₀.1 (hC₀.piece hW) (C₀.hsubset W hW) c,
        hb_at ⟨W, hW⟩, hc_at ⟨W, hW⟩]
      exact sq.row_comm W (hC₀.piece hW) (f ⟨W, hW⟩)
    -- descend to the base by middle exactness, then recover per piece
    obtain ⟨x, hxB, hxC⟩ := sq.row_glue C₀.base hC₀.1 b c hd
    refine ⟨x, ?_⟩
    intro W
    apply sq.row_injective W.1 (hC₀.piece W.2)
    · rw [sq.push_natural_B C₀.base W.1 hC₀.1 (hC₀.piece W.2)
        (C₀.hsubset W.1 W.2) x, hxB, hb_at W]
    · rw [sq.push_natural_C C₀.base W.1 hC₀.1 (hC₀.piece W.2)
        (C₀.hsubset W.1 W.2) x, hxC, hc_at W]

end ValuationSpectrum
