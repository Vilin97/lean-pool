/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Bases

/-!
# Kuratowski–Ulam: meager sections give a meager set

`isMeagre_of_isMeagre_sections`: if `A ⊆ X × Y` has the Baire property and every vertical
section `{y | (x, y) ∈ A}` is meager, then `A` is meager. This is the direction of the
Kuratowski–Ulam theorem ("Fubini for Baire category", Kechris CDST 8.41) needed for the
classical category route to Silver's theorem (step 3 of
`InfinitaryLogic/Conditional/SilverCategoryRoute.lean`; see `docs/silver-phase2-route.md`):
it makes the pullback relation on Cantor space meager once all its classes are meager.

## Proof

The auxiliary direction comes first: for a nowhere dense `F ⊆ X × Y` (with `Y` second
countable), residually many `x` have nowhere dense sections
(`residual_isNowhereDense_section`). Indeed, taking `F` closed with dense open complement
`U`, for each nonempty basic `V ⊆ Y` the set of `x` whose section of `U` meets `V` is open
(projection of an open set) and dense (density of `U` on boxes `G ×ˢ V`); on the countable
intersection over the basis, the section of `U` is dense open, so the section of `F` is
nowhere dense. Countable unions lift this to meager `M` (`residual_isMeagre_section`).

For the main theorem, write `A =ᵇ W` with `W` open (Baire property) and let `M` be the
(meager) symmetric difference. If `A` were non-meager then `W` is nonempty, so it contains
a box `G ×ˢ H`; residually many `x` have meager `M`-section, and since nonempty open sets
in the Baire space `X` are non-meager, some such `x₁` lies in `G`. Then
`H ⊆ {y | (x₁, y) ∈ A} ∪ {y | (x₁, y) ∈ M}` is meager, contradicting that `Y` is a Baire
space.
-/

open Set Filter Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- For a nowhere dense subset of a product (second factor second countable), residually
many vertical sections are nowhere dense. -/
private theorem residual_isNowhereDense_section [SecondCountableTopology Y]
    {F : Set (X × Y)} (hF : IsNowhereDense F) :
    {x : X | IsNowhereDense {y : Y | (x, y) ∈ F}} ∈ residual X := by
  classical
  -- Reduce to a closed nowhere dense superset
  obtain ⟨C, hFC, hC_nwd, hC_closed⟩ := hF.subset_of_closed_isNowhereDense
  suffices h : {x : X | IsNowhereDense {y : Y | (x, y) ∈ C}} ∈ residual X by
    refine Filter.mem_of_superset h fun x hx => ?_
    exact IsNowhereDense.mono (fun y hy => hFC hy) hx
  obtain ⟨hCc_open, hCc_dense⟩ := isClosed_isNowhereDense_iff_compl.mp ⟨hC_closed, hC_nwd⟩
  -- Countable basis of Y (with no empty member)
  obtain ⟨B, hB_count, hB_ne, hB⟩ := exists_countable_basis Y
  -- For each basic V, the set of x whose Cᶜ-section meets V
  set D : Set Y → Set X := fun V => {x : X | ∃ y ∈ V, (x, y) ∈ Cᶜ} with hD
  have hD_open : ∀ V : Set Y, IsOpen V → IsOpen (D V) := by
    intro V hV
    have himg : D V = Prod.fst '' (Cᶜ ∩ univ ×ˢ V) := by
      ext x
      simp only [hD, mem_ofPred_eq, mem_image, mem_inter_iff, mem_prod, mem_univ, true_and]
      constructor
      · rintro ⟨y, hyV, hyC⟩
        exact ⟨(x, y), ⟨hyC, hyV⟩, rfl⟩
      · rintro ⟨⟨x', y⟩, ⟨hyC, hyV⟩, rfl⟩
        exact ⟨y, hyV, hyC⟩
    rw [himg]
    exact isOpenMap_fst _ (hCc_open.inter (isOpen_univ.prod hV))
  have hD_dense : ∀ V : Set Y, IsOpen V → V.Nonempty → Dense (D V) := by
    intro V hV hVne
    rw [dense_iff_inter_open]
    intro G hG hGne
    obtain ⟨⟨x, y⟩, hmem, hCc⟩ :=
      hCc_dense.inter_open_nonempty (G ×ˢ V) (hG.prod hV) (hGne.prod hVne)
    exact ⟨x, hmem.1, y, hmem.2, hCc⟩
  -- The residual set: intersection of the D V over the basis
  have hres : (⋂ V ∈ B, D V) ∈ residual X := by
    refine (countable_bInter_mem hB_count).mpr fun V hV => ?_
    have hVne : V.Nonempty := nonempty_iff_ne_empty.mpr fun h => hB_ne (h ▸ hV)
    exact residual_of_dense_open (hD_open V (hB.isOpen hV)) (hD_dense V (hB.isOpen hV) hVne)
  refine Filter.mem_of_superset hres fun x hx => ?_
  -- On that set, the section of C is closed with dense complement, hence nowhere dense
  have hx' := mem_iInter₂.mp hx
  have hsec_closed : IsClosed {y : Y | (x, y) ∈ C} :=
    hC_closed.preimage (continuous_const.prodMk continuous_id)
  have hsec_dense : Dense {y : Y | (x, y) ∈ C}ᶜ := by
    rw [hB.dense_iff]
    intro o ho hone
    obtain ⟨y, hyo, hyC⟩ := hx' o ho
    exact ⟨y, hyo, hyC⟩
  exact (isClosed_isNowhereDense_iff_compl.mpr ⟨hsec_closed.isOpen_compl, hsec_dense⟩).2

/-- For a meager subset of a product (second factor second countable), residually many
vertical sections are meager. -/
private theorem residual_isMeagre_section [SecondCountableTopology Y]
    {M : Set (X × Y)} (hM : IsMeagre M) :
    {x : X | IsMeagre {y : Y | (x, y) ∈ M}} ∈ residual X := by
  obtain ⟨S, hS_nwd, hS_count, hS_sub⟩ := isMeagre_iff_countable_union_isNowhereDense.mp hM
  have hres : (⋂ F ∈ S, {x : X | IsNowhereDense {y : Y | (x, y) ∈ F}}) ∈ residual X :=
    (countable_bInter_mem hS_count).mpr fun F hF =>
      residual_isNowhereDense_section (hS_nwd F hF)
  refine Filter.mem_of_superset hres fun x hx => ?_
  have hx' := mem_iInter₂.mp hx
  have hsub : {y : Y | (x, y) ∈ M} ⊆ ⋃ F ∈ S, {y : Y | (x, y) ∈ F} := by
    intro y hy
    obtain ⟨F, hFS, hyF⟩ := hS_sub hy
    exact mem_biUnion hFS hyF
  exact (isMeagre_biUnion hS_count fun F hF => (hx' F hF).isMeagre).mono hsub

/-- **Kuratowski–Ulam** (the direction used for Silver's theorem): a set with the Baire
property in a product of Baire spaces, the second factor second countable, all of whose
vertical sections are meager, is meager. (Kechris, CDST 8.41.) -/
theorem isMeagre_of_isMeagre_sections [SecondCountableTopology Y]
    [BaireSpace X] [BaireSpace Y]
    {A : Set (X × Y)} (hA : BaireMeasurableSet A)
    (hsec : ∀ x : X, IsMeagre {y : Y | (x, y) ∈ A}) :
    IsMeagre A := by
  obtain ⟨W, hW_open, hAW⟩ := hA.residualEq_isOpen
  -- The symmetric difference of A and W is meager
  have hM : IsMeagre {p : X × Y | ¬(p ∈ A ↔ p ∈ W)} := by
    rw [IsMeagre, compl_ofPred]
    simp only [not_not]
    exact Filter.eventuallyEq_set.mp hAW
  by_contra hA_nm
  -- W is nonempty (otherwise A is contained in the symmetric difference)
  have hW_ne : W.Nonempty := by
    rcases W.eq_empty_or_nonempty with rfl | h
    · exact (hA_nm (hM.mono fun p hp => by simp [hp])).elim
    · exact h
  obtain ⟨p₀, hp₀⟩ := hW_ne
  -- A nonempty open box inside W
  obtain ⟨G, H, hG, hH, hxG, hyH, hGH⟩ :=
    isOpen_prod_iff.mp hW_open p₀.1 p₀.2 (by simpa using hp₀)
  -- Pick x₁ ∈ G whose section of the symmetric difference is meager
  obtain ⟨x₁, hx₁G, hx₁⟩ :=
    (dense_of_mem_residual (residual_isMeagre_section hM)).inter_open_nonempty G hG ⟨p₀.1, hxG⟩
  -- H is covered by the A-section and the symmetric-difference section at x₁
  have hHsub : H ⊆ {y : Y | (x₁, y) ∈ A} ∪ {y : Y | ¬((x₁, y) ∈ A ↔ (x₁, y) ∈ W)} := by
    intro y hy
    by_cases hyA : (x₁, y) ∈ A
    · exact Or.inl hyA
    · exact Or.inr fun h => hyA (h.mpr (hGH (mk_mem_prod hx₁G hy)))
  exact not_isMeagre_of_isOpen hH ⟨p₀.2, hyH⟩ (((hsec x₁).union hx₁).mono hHsub)
