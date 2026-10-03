/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development006
public import LeanPool.MovingSofa.Development.Geometry.Applications.Development002
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development007





public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development005



public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development008
public import LeanPool.MovingSofa.Development.Geometry.Applications.Development001


public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development002




/-!
# Moving sofa: related mathematical developments

* `Gerver.Applications.Development004`.
* `Bounds.Applications.Development003`.
* `Sofa.Applications.Development001`.
* `Motion.Applications.Development001`.
* `Sofa.Applications.Development002`.
* `Sofa.Applications.Development003`.
* `Motion.Applications.Development002`.
* `Main`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Gerver.Niche.Orientation`.
* `Gerver.ContactGeometry`.
* `Gerver.TailGeometry`.
* `Gerver.MeasureTranslation`.
* `Gerver.PhaseMeasures`.
* `Gerver.PhaseIntegration`.
* `Gerver.QMatch`.
* `Gerver.QVariation`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Orientation of the certified Gerver niche boundary

The niche of the certified Gerver outer cap is the strict region under the niche roof, and the
roof is the graph of a continuous height function `f` over the horizontal extent
`[gerverNicheLeft, gerverNicheRight]` of the roof (`exists_gerverRoofHeight`).  The closure of
the niche is therefore the closed subgraph of `f`, its interior the open subgraph, and the
counterclockwise loop `positiveGraphLoop` around that region traces their common frontier.

`gerverNicheBoundary` is the explicit four-piece traversal of that frontier: the second contact
curve reversed, the ambient path forwards, the fourth contact curve reversed, and the base
segment.  It runs backwards along the roof through a decreasing piecewise affine parameter
change (`gerverBoundaryParam`), so it is the positive-graph loop reparametrized by an increasing
map (`gerverNicheBoundary_orientedJordan`).  The main result `gerver_niche_orientation` collects
the consequences: the traversal is a continuous path of bounded variation, a counterclockwise
Jordan parametrization of the frontier of the closed niche, its signed curve area is the area of
the niche, and no roof point lies in the niche.

The same description of the niche as the strict region under the roof settles the opposite
inclusion for the fourth boundary piece: every interior point of the base segment does lie in
the niche (`gerver_bottom_segment_mem_gerverLiteralNiche`).
-/

public section

noncomputable section

namespace MovingSofa

/-- The stage-time inequalities of `gerverStageTimes_strictMono`, in the packaged form used
throughout this file. -/
private theorem gerverStageTimes_order :
    gerverStageTimes 0 = 0 ∧ gerverStageTimes 5 = Real.pi / 2 ∧
      0 < gerverStageTimes 1 ∧ gerverStageTimes 1 < gerverStageTimes 2 ∧
      gerverStageTimes 2 < gerverStageTimes 3 ∧ gerverStageTimes 3 < gerverStageTimes 4 ∧
      gerverStageTimes 4 < Real.pi / 2 := by
  have h := gerverStageTimes_strictMono
  exact ⟨gerverStageTimes_zero, rfl, h (show (0 : Fin 6) < 1 by decide),
    h (show (1 : Fin 6) < 2 by decide), h (show (2 : Fin 6) < 3 by decide),
    h (show (3 : Fin 6) < 4 by decide), h (show (4 : Fin 6) < 5 by decide)⟩

/-! ## The roof as the graph of a continuous height function -/

/-- The left end of the horizontal extent of the niche roof. -/
private def gerverNicheLeft : ℝ := paperGerverContacts 0 3 0

/-- The right end of the horizontal extent of the niche roof. -/
private def gerverNicheRight : ℝ := paperGerverContacts (Real.pi / 2) 1 0

private theorem gerverNicheRoof_zero :
    gerverNicheRoof ⟨0, le_rfl, by positivity⟩ = paperGerverContacts 0 3 := by
  obtain ⟨-, -, h01, h12, -, -, -⟩ := gerverStageTimes_order
  exact gerverNicheRoof_of_le_two _ (by linarith)

private theorem gerverNicheRoof_top :
    gerverNicheRoof ⟨Real.pi / 2, by positivity, le_rfl⟩ =
      paperGerverContacts (Real.pi / 2) 1 := by
  obtain ⟨-, -, -, -, -, h34, h45⟩ := gerverStageTimes_order
  exact gerverNicheRoof_of_ge_three _ (by linarith)

/-- The niche roof is the graph of a continuous function over its horizontal extent, which
vanishes at the two ends and is positive in between. -/
private theorem exists_gerverRoofHeight :
    ∃ f : ℝ → ℝ, Continuous f ∧
      (∀ s : Set.Icc (0 : ℝ) (Real.pi / 2), f (gerverNicheRoof s 0) = gerverNicheRoof s 1) ∧
      (∀ c ∈ Set.Icc gerverNicheLeft gerverNicheRight,
        ∃ s : Set.Icc (0 : ℝ) (Real.pi / 2), gerverNicheRoof s 0 = c) ∧
      gerverNicheLeft < gerverNicheRight ∧
      f gerverNicheLeft = 0 ∧ f gerverNicheRight = 0 ∧
      ∀ c ∈ Set.Ioo gerverNicheLeft gerverNicheRight, 0 < f c := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  set A : Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨0, le_rfl, hpi.le⟩ with hA
  set B : Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨Real.pi / 2, hpi.le, le_rfl⟩ with hB
  have hk : StrictMono fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ gerverNicheRoof s 0 :=
    gerver_niche_roof_strictMono
  have hk0 : Continuous fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ gerverNicheRoof s 0 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp continuous_gerverNicheRoof
  have hk1 : Continuous fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ gerverNicheRoof s 1 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp continuous_gerverNicheRoof
  have hAleft : gerverNicheRoof A 0 = gerverNicheLeft := by rw [gerverNicheRoof_zero]; rfl
  have hBright : gerverNicheRoof B 0 = gerverNicheRight := by rw [gerverNicheRoof_top]; rfl
  have hab : gerverNicheLeft < gerverNicheRight := by
    rw [← hAleft, ← hBright]
    exact hk (show A < B from hpi)
  have hmem : ∀ s, gerverNicheRoof s 0 ∈ Set.Icc gerverNicheLeft gerverNicheRight := fun s ↦
    ⟨hAleft ▸ hk.monotone (show A ≤ s from s.2.1), hBright ▸ hk.monotone (show s ≤ B from s.2.2)⟩
  set kmap : Set.Icc (0 : ℝ) (Real.pi / 2) → Set.Icc gerverNicheLeft gerverNicheRight :=
    fun s ↦ ⟨gerverNicheRoof s 0, hmem s⟩ with hkmap
  have hkc : Continuous kmap := hk0.subtype_mk _
  have hkinj : Function.Injective kmap := fun x y h ↦ hk.injective (congrArg Subtype.val h)
  have : PreconnectedSpace (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hksurj : Function.Surjective kmap := by
    intro s
    obtain ⟨t, ht⟩ := intermediate_value_univ A B hk0 (by rw [hAleft, hBright]; exact s.property)
    exact ⟨t, Subtype.ext ht⟩
  set khom : Set.Icc (0 : ℝ) (Real.pi / 2) ≃ₜ Set.Icc gerverNicheLeft gerverNicheRight :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective kmap ⟨hkinj, hksurj⟩) hkc
    with hkhom
  have hkhom_apply : ∀ s, (khom s : ℝ) = gerverNicheRoof s 0 := fun _ ↦ rfl
  have hsymm : ∀ x : Set.Icc gerverNicheLeft gerverNicheRight,
      gerverNicheRoof (khom.symm x) 0 = (x : ℝ) := by
    intro x
    rw [← hkhom_apply, khom.apply_symm_apply]
  refine ⟨fun c ↦ gerverNicheRoof (khom.symm (Set.projIcc _ _ hab.le c)) 1,
    hk1.comp (khom.symm.continuous.comp continuous_projIcc), ?_, ?_, hab, ?_, ?_, ?_⟩
  · -- the height function inverts the horizontal coordinate
    intro s
    have hval : Set.projIcc gerverNicheLeft gerverNicheRight hab.le (gerverNicheRoof s 0) =
        khom s := by
      rw [← hkhom_apply s, Set.projIcc_val]
    dsimp only
    rw [hval, khom.symm_apply_apply]
  · intro c hc
    exact ⟨khom.symm ⟨c, hc⟩, by rw [hsymm ⟨c, hc⟩]⟩
  · have hmemL : gerverNicheLeft ∈ Set.Icc gerverNicheLeft gerverNicheRight :=
      Set.left_mem_Icc.mpr hab.le
    have hval : Set.projIcc gerverNicheLeft gerverNicheRight hab.le gerverNicheLeft =
        ⟨gerverNicheLeft, hmemL⟩ := Set.projIcc_of_mem hab.le hmemL
    have hsA : khom.symm ⟨gerverNicheLeft, hmemL⟩ = A :=
      hk.injective (by dsimp only; rw [hsymm ⟨gerverNicheLeft, hmemL⟩, hAleft])
    dsimp only
    rw [hval, hsA, hA, gerverNicheRoof_zero]
    exact gerver_niche_piece_endpoints.2.2.2
  · have hmemR : gerverNicheRight ∈ Set.Icc gerverNicheLeft gerverNicheRight :=
      Set.right_mem_Icc.mpr hab.le
    have hval : Set.projIcc gerverNicheLeft gerverNicheRight hab.le gerverNicheRight =
        ⟨gerverNicheRight, hmemR⟩ := Set.projIcc_of_mem hab.le hmemR
    have hsB : khom.symm ⟨gerverNicheRight, hmemR⟩ = B :=
      hk.injective (by dsimp only; rw [hsymm ⟨gerverNicheRight, hmemR⟩, hBright])
    dsimp only
    rw [hval, hsB, hB, gerverNicheRoof_top]
    exact gerver_niche_piece_endpoints.2.2.1
  · intro c hc
    have hval : Set.projIcc gerverNicheLeft gerverNicheRight hab.le c =
        ⟨c, hc.1.le, hc.2.le⟩ := Set.projIcc_of_mem hab.le ⟨hc.1.le, hc.2.le⟩
    dsimp only
    rw [hval]
    set s := khom.symm (⟨c, hc.1.le, hc.2.le⟩ : Set.Icc gerverNicheLeft gerverNicheRight) with hs
    have hcs : gerverNicheRoof s 0 = c := hsymm _
    refine gerver_niche_roof_positive s ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le s.2.1 with h | h
      · exact absurd (by rw [show s = A from Subtype.ext h.symm, hAleft] at hcs; exact hcs)
          hc.1.ne
      · exact h
    · rcases eq_or_lt_of_le s.2.2 with h | h
      · exact absurd (by rw [show s = B from Subtype.ext h, hBright] at hcs; exact hcs.symm)
          hc.2.ne
      · exact h

/-! ## The literal niche is the strict region under the roof -/

/-- Every central path time is the reverse time of a middle roof parameter. -/
private theorem exists_gerverRoofReverseTime {t : ℝ}
    (ht : t ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 4)) :
    ∃ s : ℝ, gerverStageTimes 2 ≤ s ∧ s ≤ gerverStageTimes 3 ∧ gerverRoofReverseTime s = t := by
  obtain ⟨-, -, -, h12, h23, h34, -⟩ := gerverStageTimes_order
  have hd : (0 : ℝ) < gerverStageTimes 3 - gerverStageTimes 2 := by linarith
  have he : (0 : ℝ) < gerverStageTimes 4 - gerverStageTimes 1 := by linarith
  refine ⟨gerverStageTimes 2 + (gerverStageTimes 4 - t) *
    (gerverStageTimes 3 - gerverStageTimes 2) / (gerverStageTimes 4 - gerverStageTimes 1),
    ?_, ?_, ?_⟩
  · have : 0 ≤ (gerverStageTimes 4 - t) * (gerverStageTimes 3 - gerverStageTimes 2) /
        (gerverStageTimes 4 - gerverStageTimes 1) :=
      div_nonneg (mul_nonneg (by linarith [ht.2]) hd.le) he.le
    linarith
  · have : (gerverStageTimes 4 - t) * (gerverStageTimes 3 - gerverStageTimes 2) /
        (gerverStageTimes 4 - gerverStageTimes 1) ≤
        gerverStageTimes 3 - gerverStageTimes 2 := by
      rw [div_le_iff₀ he]
      nlinarith [ht.1, hd]
    linarith
  · rw [gerverRoofReverseTime]
    field_simp
    ring

/-- The literal niche is the strict vertical region under the niche roof. -/
private theorem gerverLiteralNiche_eq_roofFill :
    gerverLiteralNiche =
      {q : Point | ∃ s : Set.Icc (0 : ℝ) (Real.pi / 2),
        q 0 = gerverNicheRoof s 0 ∧ 0 ≤ q 1 ∧ q 1 < gerverNicheRoof s 1} := by
  obtain ⟨h0, h5, h01, h12, h23, h34, h45⟩ := gerverStageTimes_order
  rw [gerver_niche_vertical_fills]
  ext q
  simp only [strictVerticalFill, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ((⟨t, ht, hq0, hq1, hq2⟩ | ⟨t, ht, hq0, hq1, hq2⟩) | ⟨t, ht, hq0, hq1, hq2⟩)
    · rw [h0] at ht
      have hs : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨ht.1, by linarith [ht.2]⟩
      refine ⟨⟨t, hs⟩, ?_, hq1, ?_⟩
      · rw [gerverNicheRoof_of_le_two hs ht.2]; exact hq0
      · rw [gerverNicheRoof_of_le_two hs ht.2]; exact hq2
    · obtain ⟨s, hs1, hs2, hsrev⟩ := exists_gerverRoofReverseTime ht
      have hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
      refine ⟨⟨s, hs⟩, ?_, hq1, ?_⟩
      · rw [gerverNicheRoof_mid hs hs1 hs2, hsrev]; exact hq0
      · rw [gerverNicheRoof_mid hs hs1 hs2, hsrev]; exact hq2
    · rw [h5] at ht
      have hs : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith [ht.1], ht.2⟩
      refine ⟨⟨t, hs⟩, ?_, hq1, ?_⟩
      · rw [gerverNicheRoof_of_ge_three hs ht.1]; exact hq0
      · rw [gerverNicheRoof_of_ge_three hs ht.1]; exact hq2
  · rintro ⟨s, hq0, hq1, hq2⟩
    rcases le_or_gt s.val (gerverStageTimes 2) with hle | hgt
    · refine Or.inl (Or.inl ⟨s.val, ⟨by rw [h0]; exact s.2.1, hle⟩, ?_, hq1, ?_⟩)
      · rw [← gerverNicheRoof_of_le_two s.2 hle]; exact hq0
      · rw [← gerverNicheRoof_of_le_two s.2 hle]; exact hq2
    rcases le_or_gt s.val (gerverStageTimes 3) with hle3 | hgt3
    · refine Or.inl (Or.inr ⟨gerverRoofReverseTime s.val,
        gerverRoofReverseTime_mem_Icc hgt.le hle3, ?_, hq1, ?_⟩)
      · rw [← gerverNicheRoof_mid s.2 hgt.le hle3]; exact hq0
      · rw [← gerverNicheRoof_mid s.2 hgt.le hle3]; exact hq2
    · refine Or.inr ⟨s.val, ⟨hgt3.le, by rw [h5]; exact s.2.2⟩, ?_, hq1, ?_⟩
      · rw [← gerverNicheRoof_of_ge_three s.2 hgt3.le]; exact hq0
      · rw [← gerverNicheRoof_of_ge_three s.2 hgt3.le]; exact hq2

/-- The horizontal coordinate of the roof stays in its horizontal extent. -/
private theorem gerverNicheRoof_fst_mem (s : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    gerverNicheRoof s 0 ∈ Set.Icc gerverNicheLeft gerverNicheRight := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hk := gerver_niche_roof_strictMono
  constructor
  · have h := hk.monotone (show (⟨0, le_rfl, hpi.le⟩ : Set.Icc (0 : ℝ) (Real.pi / 2)) ≤ s
      from s.2.1)
    simp only [gerverNicheRoof_zero] at h
    exact h
  · have h := hk.monotone (show s ≤ (⟨Real.pi / 2, hpi.le, le_rfl⟩ :
      Set.Icc (0 : ℝ) (Real.pi / 2)) from s.2.2)
    simp only [gerverNicheRoof_top] at h
    exact h

/-- Read through the roof height function, the literal niche is the strict subgraph. -/
private theorem gerverLiteralNiche_eq_strictSubgraph {f : ℝ → ℝ}
    (hfgraph : ∀ s : Set.Icc (0 : ℝ) (Real.pi / 2),
      f (gerverNicheRoof s 0) = gerverNicheRoof s 1)
    (hfsurj : ∀ c ∈ Set.Icc gerverNicheLeft gerverNicheRight,
      ∃ s : Set.Icc (0 : ℝ) (Real.pi / 2), gerverNicheRoof s 0 = c) :
    gerverLiteralNiche = strictSubgraph gerverNicheLeft gerverNicheRight f := by
  rw [gerverLiteralNiche_eq_roofFill]
  ext q
  simp only [strictSubgraph, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, hq0, hq1, hq2⟩
    have hmem := gerverNicheRoof_fst_mem s
    rw [← hq0] at hmem
    exact ⟨hmem.1, hmem.2, hq1, by rw [hq0, hfgraph s]; exact hq2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨s, hs⟩ := hfsurj (q 0) ⟨h1, h2⟩
    exact ⟨s, hs.symm, h3, by rw [← hfgraph s, hs]; exact h4⟩

/-- The closed boundary parametrization of the Gerver niche. -/
def gerverNicheBoundary (s : Set.Icc (0 : ℝ) 4) : Point :=
  if s.val ≤ 1 then
    paperGerverContacts
      (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s.val) 1
  else if s.val ≤ 2 then
    paperGerverPath
      (gerverStageTimes 1 + (gerverStageTimes 4 - gerverStageTimes 1) * (s.val - 1))
  else if s.val ≤ 3 then
    paperGerverContacts (gerverStageTimes 2 * (3 - s.val)) 3
  else
    (4 - s.val) • paperGerverContacts 0 3 +
      (s.val - 3) • paperGerverContacts (Real.pi / 2) 1

/-! ## The four-piece traversal of the niche boundary -/

/-- On its first piece the niche traversal runs backwards along the second contact curve `B`,
from `B (π / 2)` at `s = 0` to `B t₃` at `s = 1`. -/
theorem gerverNicheBoundary_of_le_one {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 4) (h : s ≤ 1) :
    gerverNicheBoundary ⟨s, hs⟩ =
      paperGerverContacts (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s) 1 :=
  ite_eq_left h

/-- On its second piece the niche traversal runs forwards along the direct Gerver path, from
`x t₁` at `s = 1` to `x t₄` at `s = 2`. -/
theorem gerverNicheBoundary_mid {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 4)
    (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    gerverNicheBoundary ⟨s, hs⟩ =
      paperGerverPath (gerverStageTimes 1 +
        (gerverStageTimes 4 - gerverStageTimes 1) * (s - 1)) := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [gerverNicheBoundary_of_le_one hs heq.ge, ← heq,
      show Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * 1 = gerverStageTimes 3 by ring,
      show gerverStageTimes 1 + (gerverStageTimes 4 - gerverStageTimes 1) * ((1 : ℝ) - 1) =
        gerverStageTimes 1 by ring]
    exact gerver_niche_piece_endpoints.1
  · rw [gerverNicheBoundary, ite_eq_right (not_le.mpr hlt), ite_eq_left h2]

/-- On its third piece the niche traversal runs backwards along the fourth contact curve `D`,
from `D t₂` at `s = 2` to `D 0` at `s = 3`. -/
theorem gerverNicheBoundary_third {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 4)
    (h1 : 2 ≤ s) (h2 : s ≤ 3) :
    gerverNicheBoundary ⟨s, hs⟩ = paperGerverContacts (gerverStageTimes 2 * (3 - s)) 3 := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [gerverNicheBoundary_mid hs (by linarith) heq.ge, ← heq,
      show gerverStageTimes 1 + (gerverStageTimes 4 - gerverStageTimes 1) * ((2 : ℝ) - 1) =
        gerverStageTimes 4 by ring,
      show gerverStageTimes 2 * ((3 : ℝ) - 2) = gerverStageTimes 2 by ring]
    exact gerver_niche_piece_endpoints.2.1.symm
  · rw [gerverNicheBoundary, ite_eq_right (not_le.mpr (by linarith)),
      ite_eq_right (not_le.mpr hlt), ite_eq_left h2]

/-- On its last piece the niche traversal runs along the base segment of the niche, from `D 0`
at `s = 3` to `B (π / 2)` at `s = 4`. -/
theorem gerverNicheBoundary_base {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 4) (h : 3 ≤ s) :
    gerverNicheBoundary ⟨s, hs⟩ =
      (4 - s) • paperGerverContacts 0 3 + (s - 3) • paperGerverContacts (Real.pi / 2) 1 := by
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [gerverNicheBoundary_third hs (by linarith) heq.ge, ← heq,
      show gerverStageTimes 2 * ((3 : ℝ) - 3) = 0 by ring]
    norm_num
  · rw [gerverNicheBoundary, ite_eq_right (not_le.mpr (by linarith)),
      ite_eq_right (not_le.mpr (by linarith)), ite_eq_right (not_le.mpr hlt)]

private theorem continuous_gerverNicheBoundary : Continuous gerverNicheBoundary := by
  have hc1 : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦
      paperGerverContacts (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s.val) 1 :=
    (continuous_paperGerverContact 1).comp (by fun_prop)
  have hc2 : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦
      paperGerverPath (gerverStageTimes 1 +
        (gerverStageTimes 4 - gerverStageTimes 1) * (s.val - 1)) :=
    contDiff_paperGerverPath.continuous.comp (by fun_prop)
  have hc3 : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦
      paperGerverContacts (gerverStageTimes 2 * (3 - s.val)) 3 :=
    (continuous_paperGerverContact 3).comp (by fun_prop)
  have hc4 : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦
      (4 - s.val) • paperGerverContacts 0 3 +
        (s.val - 3) • paperGerverContacts (Real.pi / 2) 1 := by fun_prop
  have hinner2 : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦
      if s.val ≤ 3 then paperGerverContacts (gerverStageTimes 2 * (3 - s.val)) 3
      else (4 - s.val) • paperGerverContacts 0 3 +
        (s.val - 3) • paperGerverContacts (Real.pi / 2) 1 := by
    refine continuous_if_le continuous_subtype_val continuous_const hc3.continuousOn
      hc4.continuousOn ?_
    intro s hsv
    rw [hsv, show gerverStageTimes 2 * ((3 : ℝ) - 3) = 0 by ring]
    norm_num
  have hinner1 : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦
      if s.val ≤ 2 then
        paperGerverPath (gerverStageTimes 1 +
          (gerverStageTimes 4 - gerverStageTimes 1) * (s.val - 1))
      else if s.val ≤ 3 then paperGerverContacts (gerverStageTimes 2 * (3 - s.val)) 3
      else (4 - s.val) • paperGerverContacts 0 3 +
        (s.val - 3) • paperGerverContacts (Real.pi / 2) 1 := by
    refine continuous_if_le continuous_subtype_val continuous_const hc2.continuousOn
      hinner2.continuousOn ?_
    intro s hsv
    rw [hsv, ite_eq_left (show (2 : ℝ) ≤ 3 by norm_num),
      show gerverStageTimes 1 + (gerverStageTimes 4 - gerverStageTimes 1) * ((2 : ℝ) - 1) =
        gerverStageTimes 4 by ring,
      show gerverStageTimes 2 * ((3 : ℝ) - 2) = gerverStageTimes 2 by ring]
    exact gerver_niche_piece_endpoints.2.1.symm
  unfold gerverNicheBoundary
  refine continuous_if_le continuous_subtype_val continuous_const hc1.continuousOn
    hinner1.continuousOn ?_
  intro s hsv
  rw [hsv, ite_eq_left (show (1 : ℝ) ≤ 2 by norm_num),
    show Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * (1 : ℝ) = gerverStageTimes 3 by ring,
    show gerverStageTimes 1 + (gerverStageTimes 4 - gerverStageTimes 1) * ((1 : ℝ) - 1) =
      gerverStageTimes 1 by ring]
  exact gerver_niche_piece_endpoints.1

/-- The four-piece niche traversal is a continuous path of bounded variation: each of its six
analytic pieces is continuously differentiable on a closed parameter interval. -/
private theorem gerverNicheBoundary_mem_continuousBV :
    gerverNicheBoundary ∈ continuousBVSubmodule 0 4 := by
  obtain ⟨h0, h5, h01, h12, h23, h34, h45⟩ := gerverStageTimes_order
  refine ⟨continuous_gerverNicheBoundary, fun i ↦ ?_⟩
  have hd3 : (0 : ℝ) < Real.pi / 2 - gerverStageTimes 3 := by linarith
  set c1 : ℝ := (Real.pi / 2 - gerverStageTimes 4) / (Real.pi / 2 - gerverStageTimes 3) with hc1def
  set c2 : ℝ := 3 - gerverStageTimes 1 / gerverStageTimes 2 with hc2def
  have hv : (Real.pi / 2 - gerverStageTimes 3) * c1 = Real.pi / 2 - gerverStageTimes 4 := by
    rw [hc1def, mul_comm, div_mul_cancel₀ _ hd3.ne']
  have hu : gerverStageTimes 2 * (gerverStageTimes 1 / gerverStageTimes 2) =
      gerverStageTimes 1 := by
    rw [mul_comm, div_mul_cancel₀ _ (show gerverStageTimes 2 ≠ 0 by
      exact ne_of_gt (by linarith))]
  have hc10 : (0 : ℝ) ≤ c1 := by rw [hc1def]; exact div_nonneg (by linarith) hd3.le
  have hc11 : c1 ≤ 1 := by rw [hc1def]; exact (div_le_one hd3).mpr (by linarith)
  have hq0 : (0 : ℝ) ≤ gerverStageTimes 1 / gerverStageTimes 2 :=
    div_nonneg (by linarith) (by linarith)
  have hq1 : gerverStageTimes 1 / gerverStageTimes 2 ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  have hc22 : (2 : ℝ) ≤ c2 := by rw [hc2def]; linarith
  have hc23 : c2 ≤ 3 := by rw [hc2def]; linarith
  -- a contact curve composed with a smooth time change staying in one stage
  have hcontact : ∀ (j : Fin 4) (k : Fin 5) (arg : ℝ → ℝ) (l r : ℝ), ContDiff ℝ 1 arg →
      Set.MapsTo arg (Set.Icc l r) (gerverStageIntervals k) →
      ContDiffOn ℝ 1 (fun s ↦ paperGerverContacts (arg s) j) (Set.Icc l r) :=
    fun j k arg l r harg hmaps ↦
      (contDiffOn_paperGerverContact j k).comp harg.contDiffOn hmaps
  have harg1 : ContDiff ℝ 1 fun s : ℝ ↦
      Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s := by fun_prop
  have harg3 : ContDiff ℝ 1 fun s : ℝ ↦ gerverStageTimes 2 * (3 - s) := by fun_prop
  -- the six pieces
  have hp1 : ContDiffOn ℝ 1 (fun s ↦ paperGerverContacts
      (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s) 1) (Set.Icc 0 c1) := by
    refine hcontact 1 4 _ 0 c1 harg1 ?_
    intro s hs
    rw [gerverStageIntervals_four, h5]
    have hmul := mul_le_mul_of_nonneg_left hs.2 hd3.le
    rw [hv] at hmul
    exact ⟨by linarith, by nlinarith [hs.1]⟩
  have hp2 : ContDiffOn ℝ 1 (fun s ↦ paperGerverContacts
      (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s) 1) (Set.Icc c1 1) := by
    refine hcontact 1 3 _ c1 1 harg1 ?_
    intro s hs
    rw [gerverStageIntervals_three]
    have hmul := mul_le_mul_of_nonneg_left hs.1 hd3.le
    rw [hv] at hmul
    exact ⟨by nlinarith [hs.2], by linarith⟩
  have hp3 : ContDiffOn ℝ 1 (fun s ↦ paperGerverPath (gerverStageTimes 1 +
      (gerverStageTimes 4 - gerverStageTimes 1) * (s - 1))) (Set.Icc 1 2) :=
    (contDiff_paperGerverPath.comp (by fun_prop)).contDiffOn
  have hp4 : ContDiffOn ℝ 1 (fun s ↦ paperGerverContacts (gerverStageTimes 2 * (3 - s)) 3)
      (Set.Icc 2 c2) := by
    refine hcontact 3 1 _ 2 c2 harg3 ?_
    intro s hs
    rw [gerverStageIntervals_one]
    have hmul := mul_le_mul_of_nonneg_left (show 3 - s ≥ 3 - c2 by linarith [hs.2])
      (show (0:ℝ) ≤ gerverStageTimes 2 by linarith)
    rw [show (3 : ℝ) - c2 = gerverStageTimes 1 / gerverStageTimes 2 by rw [hc2def]; ring, hu]
      at hmul
    exact ⟨hmul, by nlinarith [hs.1]⟩
  have hp5 : ContDiffOn ℝ 1 (fun s ↦ paperGerverContacts (gerverStageTimes 2 * (3 - s)) 3)
      (Set.Icc c2 3) := by
    refine hcontact 3 0 _ c2 3 harg3 ?_
    intro s hs
    rw [gerverStageIntervals_zero, h0]
    have hmul := mul_le_mul_of_nonneg_left (show 3 - s ≤ 3 - c2 by linarith [hs.1])
      (show (0:ℝ) ≤ gerverStageTimes 2 by linarith)
    rw [show (3 : ℝ) - c2 = gerverStageTimes 1 / gerverStageTimes 2 by rw [hc2def]; ring, hu]
      at hmul
    exact ⟨by nlinarith [hs.2], hmul⟩
  have hp6 : ContDiffOn ℝ 1 (fun s : ℝ ↦ (4 - s) • paperGerverContacts 0 3 +
      (s - 3) • paperGerverContacts (Real.pi / 2) 1) (Set.Icc 3 4) := by
    apply ContDiff.contDiffOn
    fun_prop
  -- the variation of each coordinate on each of the six pieces
  have e1 := boundedVariationOn_coord_Icc_of_contDiffOn gerverNicheBoundary le_rfl hc10
    (show c1 ≤ 4 by linarith) hp1
    (fun t ↦ gerverNicheBoundary_of_le_one _ (t.2.2.trans hc11)) i
  have e2 := boundedVariationOn_coord_Icc_of_contDiffOn gerverNicheBoundary hc10 hc11
    (show (1 : ℝ) ≤ 4 by norm_num) hp2
    (fun t ↦ gerverNicheBoundary_of_le_one _ t.2.2) i
  have e3 := boundedVariationOn_coord_Icc_of_contDiffOn gerverNicheBoundary
    (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 2 by norm_num)
    (show (2 : ℝ) ≤ 4 by norm_num) hp3
    (fun t ↦ gerverNicheBoundary_mid _ t.2.1 t.2.2) i
  have e4 := boundedVariationOn_coord_Icc_of_contDiffOn gerverNicheBoundary
    (show (0 : ℝ) ≤ 2 by norm_num) hc22 (show c2 ≤ 4 by linarith) hp4
    (fun t ↦ gerverNicheBoundary_third _ t.2.1 (t.2.2.trans hc23)) i
  have e5 := boundedVariationOn_coord_Icc_of_contDiffOn gerverNicheBoundary
    (show (0 : ℝ) ≤ c2 by linarith) hc23 (show (3 : ℝ) ≤ 4 by norm_num) hp5
    (fun t ↦ gerverNicheBoundary_third _ (hc22.trans t.2.1) t.2.2) i
  have e6 := boundedVariationOn_coord_Icc_of_contDiffOn gerverNicheBoundary
    (show (0 : ℝ) ≤ 3 by norm_num) (show (3 : ℝ) ≤ 4 by norm_num) le_rfl hp6
    (fun t ↦ gerverNicheBoundary_base _ t.2.1) i
  -- glue them along the subdivision `0 ≤ c₁ ≤ 1 ≤ 2 ≤ c₂ ≤ 3 ≤ 4`
  have hsub : ∀ {x y : ℝ} {hx : x ∈ Set.Icc (0 : ℝ) 4} {hy : y ∈ Set.Icc (0 : ℝ) 4},
      x ≤ y → (⟨x, hx⟩ : Set.Icc (0 : ℝ) 4) ≤ ⟨y, hy⟩ := fun h ↦ h
  have q01 : (0 : ℝ) ≤ 1 := by norm_num
  have q12 : (1 : ℝ) ≤ 2 := by norm_num
  have q02 : (0 : ℝ) ≤ 2 := by norm_num
  have q03 : (0 : ℝ) ≤ 3 := by norm_num
  have q34 : (3 : ℝ) ≤ 4 := by norm_num
  have q0c2 : (0 : ℝ) ≤ c2 := by linarith
  have g1 := BoundedVariationOn.Icc_union_Icc (hsub hc10) (hsub hc11) e1 e2
  have g2 := BoundedVariationOn.Icc_union_Icc (hsub q01) (hsub q12) g1 e3
  have g3 := BoundedVariationOn.Icc_union_Icc (hsub q02) (hsub hc22) g2 e4
  have g4 := BoundedVariationOn.Icc_union_Icc (hsub q0c2) (hsub hc23) g3 e5
  change BoundedVariationOn (fun t : Set.Icc (0 : ℝ) 4 ↦ gerverNicheBoundary t i) Set.univ
  exact BoundedVariationOn.univ_of_Icc_endpoints (show (0 : ℝ) ≤ 4 by norm_num)
    (BoundedVariationOn.Icc_union_Icc (hsub q03) (hsub q34) g4 e6)

/-! ## The traversal is the roof, run backwards -/

/-- The decreasing piecewise affine parameter change carrying `[0, 3]` onto the roof
interval `[0, π/2]`. -/
private def gerverBoundaryParam (s : ℝ) : ℝ :=
  if s ≤ 1 then Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s
  else if s ≤ 2 then gerverStageTimes 2 + (gerverStageTimes 3 - gerverStageTimes 2) * (2 - s)
  else gerverStageTimes 2 * (3 - s)

private theorem gerverBoundaryParam_first {s : ℝ} (h : s ≤ 1) :
    gerverBoundaryParam s = Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s :=
  ite_eq_left h

private theorem gerverBoundaryParam_second {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    gerverBoundaryParam s =
      gerverStageTimes 2 + (gerverStageTimes 3 - gerverStageTimes 2) * (2 - s) := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [gerverBoundaryParam_first heq.ge, ← heq]; ring
  · rw [gerverBoundaryParam, ite_eq_right (not_le.mpr hlt), ite_eq_left h2]

private theorem gerverBoundaryParam_third {s : ℝ} (h1 : 2 ≤ s) :
    gerverBoundaryParam s = gerverStageTimes 2 * (3 - s) := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [gerverBoundaryParam_second (by linarith) heq.ge, ← heq]; ring
  · rw [gerverBoundaryParam, ite_eq_right (not_le.mpr (by linarith)),
      ite_eq_right (not_le.mpr hlt)]

private theorem gerverBoundaryParam_strictAntiOn :
    StrictAntiOn gerverBoundaryParam (Set.Icc (0 : ℝ) 3) := by
  obtain ⟨-, -, h01, h12, h23, h34, h45⟩ := gerverStageTimes_order
  have hD : (0 : ℝ) < Real.pi / 2 - gerverStageTimes 3 := by linarith
  have hE : (0 : ℝ) < gerverStageTimes 3 - gerverStageTimes 2 := by linarith
  have hF : (0 : ℝ) < gerverStageTimes 2 := by linarith
  have hle1 : ∀ s : ℝ, s ≤ 1 → gerverStageTimes 3 ≤ gerverBoundaryParam s := by
    intro s hs
    rw [gerverBoundaryParam_first hs]
    nlinarith
  have hlt1 : ∀ s : ℝ, 1 < s → s ≤ 3 → gerverBoundaryParam s < gerverStageTimes 3 := by
    intro s hs hs3
    rcases le_or_gt s 2 with h | h
    · rw [gerverBoundaryParam_second hs.le h]; nlinarith
    · rw [gerverBoundaryParam_third h.le]; nlinarith
  have hle2 : ∀ s : ℝ, 1 ≤ s → s ≤ 2 → gerverStageTimes 2 ≤ gerverBoundaryParam s := by
    intro s hs1 hs2
    rw [gerverBoundaryParam_second hs1 hs2]
    nlinarith
  have hlt2 : ∀ s : ℝ, 2 < s → gerverBoundaryParam s < gerverStageTimes 2 := by
    intro s hs
    rw [gerverBoundaryParam_third hs.le]
    nlinarith
  intro x hx y hy hxy
  rcases le_or_gt y 1 with hy1 | hy1
  · rw [gerverBoundaryParam_first (hxy.le.trans hy1), gerverBoundaryParam_first hy1]
    nlinarith
  rcases le_or_gt x 1 with hx1 | hx1
  · exact lt_of_lt_of_le (hlt1 y hy1 hy.2) (hle1 x hx1)
  rcases le_or_gt y 2 with hy2 | hy2
  · rw [gerverBoundaryParam_second hx1.le (hxy.le.trans hy2),
      gerverBoundaryParam_second (by linarith) hy2]
    nlinarith
  rcases le_or_gt x 2 with hx2 | hx2
  · exact lt_of_lt_of_le (hlt2 y hy2) (hle2 x hx1.le hx2)
  · rw [gerverBoundaryParam_third hx2.le, gerverBoundaryParam_third (by linarith)]
    nlinarith

private theorem gerverBoundaryParam_zero : gerverBoundaryParam 0 = Real.pi / 2 := by
  rw [gerverBoundaryParam_first (by norm_num)]; ring

private theorem gerverBoundaryParam_three : gerverBoundaryParam 3 = 0 := by
  rw [gerverBoundaryParam_third (by norm_num)]; ring

private theorem gerverBoundaryParam_mem {s : ℝ} (h1 : 0 ≤ s) (h2 : s ≤ 3) :
    gerverBoundaryParam s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  have hanti := gerverBoundaryParam_strictAntiOn.antitoneOn
  refine ⟨?_, ?_⟩
  · rw [← gerverBoundaryParam_three]
    exact hanti ⟨h1, h2⟩ (by norm_num) h2
  · rw [← gerverBoundaryParam_zero]
    exact hanti (by norm_num) ⟨h1, h2⟩ h1

/-- On its first three pieces the traversal runs backwards along the niche roof. -/
private theorem gerverNicheBoundary_eq_roof {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 4) (h : s ≤ 3) :
    gerverNicheBoundary ⟨s, hs⟩ =
      gerverNicheRoof ⟨gerverBoundaryParam s, gerverBoundaryParam_mem hs.1 h⟩ := by
  obtain ⟨-, -, h01, h12, h23, h34, h45⟩ := gerverStageTimes_order
  have hne : gerverStageTimes 3 - gerverStageTimes 2 ≠ 0 := by
    exact ne_of_gt (by linarith)
  rcases le_or_gt s 1 with h1 | h1
  · rw [gerverNicheBoundary_of_le_one hs h1,
      gerverNicheRoof_of_ge_three _ (by rw [gerverBoundaryParam_first h1]; nlinarith),
      gerverBoundaryParam_first h1]
  rcases le_or_gt s 2 with h2 | h2
  · rw [gerverNicheBoundary_mid hs h1.le h2,
      gerverNicheRoof_mid _ (by rw [gerverBoundaryParam_second h1.le h2]; nlinarith)
        (by rw [gerverBoundaryParam_second h1.le h2]; nlinarith)]
    congr 1
    rw [gerverRoofReverseTime, gerverBoundaryParam_second h1.le h2]
    field_simp
    ring
  · rw [gerverNicheBoundary_third hs h2.le h,
      gerverNicheRoof_of_le_two _ (by rw [gerverBoundaryParam_third h2.le]; nlinarith),
      gerverBoundaryParam_third h2.le]

/-- The four-piece traversal has the same image as the counterclockwise loop around the
region under the roof, and is a counterclockwise Jordan parametrization of it. -/
private theorem gerverNicheBoundary_orientedJordan {f : ℝ → ℝ} (hfc : Continuous f)
    (hfgraph : ∀ s : Set.Icc (0 : ℝ) (Real.pi / 2),
      f (gerverNicheRoof s 0) = gerverNicheRoof s 1)
    (hab : gerverNicheLeft < gerverNicheRight)
    (hfa : f gerverNicheLeft = 0) (hfb : f gerverNicheRight = 0)
    (hfpos : ∀ c ∈ Set.Ioo gerverNicheLeft gerverNicheRight, 0 < f c) :
    Set.range gerverNicheBoundary =
        Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f) ∧
      IsOrientedJordanParametrization (show (0 : ℝ) ≤ 4 by norm_num)
        (Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f)) true
        gerverNicheBoundary := by
  have hba : (0 : ℝ) < gerverNicheRight - gerverNicheLeft := by linarith
  obtain ⟨hjor, -⟩ := positiveGraphLoop_counterclockwise gerverNicheLeft gerverNicheRight
    hab f hfc.continuousOn hfa hfb hfpos
  -- the reparametrization of the loop by the four-piece traversal
  have hbnd : ∀ s : Set.Icc (0 : ℝ) 4, s.val ≤ 3 →
      gerverNicheBoundary s 0 ∈ Set.Icc gerverNicheLeft gerverNicheRight := by
    intro s hs
    rw [gerverNicheBoundary_eq_roof s.2 hs]
    exact gerverNicheRoof_fst_mem _
  have hpsimem : ∀ s : Set.Icc (0 : ℝ) 4,
      (if s.val ≤ 3 then (gerverNicheRight - gerverNicheBoundary s 0) /
        (gerverNicheRight - gerverNicheLeft) else s.val - 2) ∈ Set.Icc (0 : ℝ) 2 := by
    intro s
    by_cases hs : s.val ≤ 3
    · obtain ⟨hl, hr⟩ := hbnd s hs
      rw [ite_eq_left hs]
      exact ⟨div_nonneg (by linarith) hba.le, by
        refine le_trans ((div_le_one hba).mpr (by linarith)) (by norm_num)⟩
    · rw [ite_eq_right hs]
      exact ⟨by linarith [not_le.mp hs], by linarith [s.2.2]⟩
  set ψ : Set.Icc (0 : ℝ) 4 → Set.Icc (0 : ℝ) 2 := fun s ↦ ⟨_, hpsimem s⟩ with hψdef
  have hψval : ∀ s : Set.Icc (0 : ℝ) 4, (ψ s : ℝ) =
      if s.val ≤ 3 then (gerverNicheRight - gerverNicheBoundary s 0) /
        (gerverNicheRight - gerverNicheLeft) else s.val - 2 := fun _ ↦ rfl
  have hψle : ∀ s : Set.Icc (0 : ℝ) 4, s.val ≤ 3 → (ψ s : ℝ) ≤ 1 := by
    intro s hs
    rw [hψval, ite_eq_left hs]
    exact (div_le_one hba).mpr (by linarith [(hbnd s hs).1])
  have hψeq : ∀ s : Set.Icc (0 : ℝ) 4, s.val ≤ 3 →
      gerverNicheRight - (gerverNicheRight - gerverNicheLeft) * (ψ s : ℝ) =
        gerverNicheBoundary s 0 := by
    intro s hs
    rw [hψval, ite_eq_left hs, mul_div_cancel₀ _ hba.ne']
    ring
  have hbthree : ∀ s : Set.Icc (0 : ℝ) 4, s.val = 3 →
      gerverNicheBoundary s 0 = gerverNicheLeft := by
    intro s hs
    rw [gerverNicheBoundary_eq_roof s.2 hs.le]
    have h3 : gerverBoundaryParam s.val = 0 := by rw [hs]; exact gerverBoundaryParam_three
    simp only [h3]
    rw [gerverNicheRoof_zero]
    rfl
  -- the traversal is the loop, reparametrized
  have hΓψ : ∀ s : Set.Icc (0 : ℝ) 4,
      gerverNicheBoundary s = positiveGraphLoop gerverNicheLeft gerverNicheRight f (ψ s) := by
    intro s
    by_cases hs : s.val ≤ 3
    · rw [positiveGraphLoop_apply_of_le (hpsimem s) (hψle s hs), hψeq s hs]
      have hroof := gerverNicheBoundary_eq_roof s.2 hs
      have hheight : f (gerverNicheBoundary s 0) = gerverNicheBoundary s 1 := by
        rw [hroof, hfgraph]
      rw [hheight]
      exact Point.eq_vecNotation _
    · have hs' : (3 : ℝ) ≤ s.val := (not_le.mp hs).le
      rw [positiveGraphLoop_apply_of_not_le (hpsimem s) (by
        rw [ite_eq_right hs]; exact not_le.mpr (by linarith [not_le.mp hs])),
        ite_eq_right hs, gerverNicheBoundary_base s.2 hs']
      have hD : paperGerverContacts 0 3 = !₂[gerverNicheLeft, (0 : ℝ)] := by
        rw [Point.eq_vecNotation (paperGerverContacts 0 3), gerver_niche_piece_endpoints.2.2.2]
        rfl
      have hB : paperGerverContacts (Real.pi / 2) 1 = !₂[gerverNicheRight, (0 : ℝ)] := by
        rw [Point.eq_vecNotation (paperGerverContacts (Real.pi / 2) 1),
          gerver_niche_piece_endpoints.2.2.1]
        rfl
      rw [hD, hB]
      ext i
      fin_cases i
      · simp
        ring
      · simp
  have hΓfun : gerverNicheBoundary =
      positiveGraphLoop gerverNicheLeft gerverNicheRight f ∘ ψ := funext hΓψ
  -- strict monotonicity of the reparametrization
  have hψmono : StrictMono ψ := by
    intro s t hst
    have hstv : s.val < t.val := hst
    have hlt : (ψ s : ℝ) < (ψ t : ℝ) := by
      by_cases hs : s.val ≤ 3
      · by_cases ht : t.val ≤ 3
        · have hΓ : gerverNicheBoundary t 0 < gerverNicheBoundary s 0 := by
            rw [gerverNicheBoundary_eq_roof s.2 hs, gerverNicheBoundary_eq_roof t.2 ht]
            exact gerver_niche_roof_strictMono
              (show (⟨gerverBoundaryParam t.val, gerverBoundaryParam_mem t.2.1 ht⟩ :
                  Set.Icc (0 : ℝ) (Real.pi / 2)) <
                ⟨gerverBoundaryParam s.val, gerverBoundaryParam_mem s.2.1 hs⟩ from
                gerverBoundaryParam_strictAntiOn ⟨s.2.1, hs⟩ ⟨t.2.1, ht⟩ hstv)
          rw [hψval s, hψval t, ite_eq_left hs, ite_eq_left ht]
          have h2 : gerverNicheRight - gerverNicheBoundary s 0 <
              gerverNicheRight - gerverNicheBoundary t 0 := by linarith
          gcongr
        · rw [hψval t, ite_eq_right ht]
          exact lt_of_le_of_lt (hψle s hs) (by linarith [not_le.mp ht])
      · have ht : ¬ t.val ≤ 3 := fun h ↦ hs (le_trans hstv.le h)
        rw [hψval s, hψval t, ite_eq_right hs, ite_eq_right ht]
        linarith
    exact hlt
  -- the reparametrization matches the endpoints and is a continuous surjection
  have hz0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 4 := ⟨le_rfl, by norm_num⟩
  have hz4 : (4 : ℝ) ∈ Set.Icc (0 : ℝ) 4 := ⟨by norm_num, le_rfl⟩
  have hu0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 2 := ⟨le_rfl, by norm_num⟩
  have hu2 : (2 : ℝ) ∈ Set.Icc (0 : ℝ) 2 := ⟨by norm_num, le_rfl⟩
  have hbzero : gerverNicheBoundary ⟨0, hz0⟩ 0 = gerverNicheRight := by
    rw [gerverNicheBoundary_eq_roof hz0 (by norm_num)]
    have h3 : gerverBoundaryParam (0 : ℝ) = Real.pi / 2 := gerverBoundaryParam_zero
    simp only [h3]
    rw [gerverNicheRoof_top]
    rfl
  have hψ0 : ψ ⟨0, hz0⟩ = ⟨0, hu0⟩ := by
    refine Subtype.ext ?_
    rw [hψval, ite_eq_left (by norm_num), hbzero, sub_self, zero_div]
  have hψ4 : ψ ⟨4, hz4⟩ = ⟨2, hu2⟩ := by
    refine Subtype.ext ?_
    rw [hψval, ite_eq_right (by norm_num)]
    norm_num
  have hψcont : Continuous ψ := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_if_le continuous_subtype_val continuous_const
      ((continuous_const.sub ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp
        continuous_gerverNicheBoundary)).div_const _).continuousOn
      (continuous_subtype_val.sub continuous_const).continuousOn ?_
    intro s hsv
    rw [hbthree s hsv, hsv, div_self hba.ne']
    norm_num
  have : PreconnectedSpace (Set.Icc (0 : ℝ) 4) := Subtype.preconnectedSpace isPreconnected_Icc
  have hψsurj : Function.Surjective ψ := by
    intro u
    have hcont : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦ (ψ s : ℝ) :=
      continuous_subtype_val.comp hψcont
    have hmemu : (u : ℝ) ∈ Set.Icc
        ((fun s : Set.Icc (0 : ℝ) 4 ↦ (ψ s : ℝ)) ⟨0, hz0⟩)
        ((fun s : Set.Icc (0 : ℝ) 4 ↦ (ψ s : ℝ)) ⟨4, hz4⟩) := by
      simp only
      rw [congrArg Subtype.val hψ0, congrArg Subtype.val hψ4]
      exact u.property
    obtain ⟨t, ht⟩ := intermediate_value_univ _ _ hcont hmemu
    exact ⟨t, Subtype.ext ht⟩
  -- the traversal traces the loop, once
  have hrange : Set.range gerverNicheBoundary =
      Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f) := by
    rw [hΓfun, Set.range_comp, hψsurj.range_eq, Set.image_univ]
  have hinj : Set.InjOn gerverNicheBoundary {t : Set.Icc (0 : ℝ) 4 | (t : ℝ) < 4} := by
    intro x hx y hy hxy
    have hlt2 : ∀ z : Set.Icc (0 : ℝ) 4, (z : ℝ) < 4 →
        (ψ z : Set.Icc (0 : ℝ) 2) ∈ {t : Set.Icc (0 : ℝ) 2 | (t : ℝ) < 2} := by
      intro z hz
      have h := hψmono (show z < (⟨4, hz4⟩ : Set.Icc (0 : ℝ) 4) from hz)
      rw [hψ4] at h
      exact h
    refine hψmono.injective (hjor.2.2.2.2.2.1 (hlt2 x hx) (hlt2 y hy) ?_)
    rw [← hΓψ x, ← hΓψ y]
    exact hxy
  have hclosedpath : gerverNicheBoundary ⟨0, hz0⟩ = gerverNicheBoundary ⟨4, hz4⟩ := by
    rw [hΓψ, hΓψ, hψ0, hψ4]
    exact hjor.2.2.2.2.1
  have hwind : ∀ p ∈ jordanInterior
      (Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f)),
      curveWinding (show (0 : ℝ) ≤ 4 by norm_num) gerverNicheBoundary p = 1 := by
    intro p hp
    have hw2 : curveWinding (show (0 : ℝ) ≤ 2 by norm_num)
        (positiveGraphLoop gerverNicheLeft gerverNicheRight f) p = 1 := by
      simpa using hjor.2.2.2.2.2.2 p hp
    have hne : curveWinding (show (0 : ℝ) ≤ 2 by norm_num)
        (positiveGraphLoop gerverNicheLeft gerverNicheRight f) p ≠ 0 := by
      rw [hw2]; norm_num
    have hcomp := curveWinding_comp_of_endpoints (show (0 : ℝ) ≤ 2 by norm_num)
      (show (0 : ℝ) ≤ 4 by norm_num)
      (exists_curveAngleLift_of_curveWinding_ne_zero _ hne) hψcont hψ0 hψ4
    rw [← hΓfun] at hcomp
    rw [hcomp, hw2]
  have hOJP : IsOrientedJordanParametrization (show (0 : ℝ) ≤ 4 by norm_num)
      (Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f)) true
      gerverNicheBoundary :=
    ⟨by norm_num, hjor.2.1, continuous_gerverNicheBoundary, hrange, hclosedpath, hinj,
      fun p hp ↦ by simpa using hwind p hp⟩
  exact ⟨hrange, hOJP⟩

/-- No point of the niche roof lies in the strict region under the roof: the roof is the graph
of the height function, and that region lies strictly below the graph. -/
private theorem gerverNicheRoof_notMem_strictSubgraph {f : ℝ → ℝ}
    (hfgraph : ∀ s : Set.Icc (0 : ℝ) (Real.pi / 2),
      f (gerverNicheRoof s 0) = gerverNicheRoof s 1)
    (s : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    gerverNicheRoof s ∉ strictSubgraph gerverNicheLeft gerverNicheRight f := by
  intro hmem
  have h := hmem.2.2.2
  rw [hfgraph s] at h
  exact absurd h (lt_irrefl _)

theorem gerver_niche_orientation :
    ∃ K : RightAngleCapSpace, (K.val : Set Point) = gerverOuterCap ∧
      ∃ Γ : ContinuousBVPaths 0 4, Γ.val = gerverNicheBoundary ∧
        IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 4)
          (frontier (closure (capNiche K))) true Γ.val ∧
        closure (capNiche K) = jordanInterior (Set.range Γ.val) ∪ Set.range Γ.val ∧
        ClassicalResults.area (closure (capNiche K)) = ClassicalResults.area (capNiche K) ∧
        curveAreaFunctional Γ = ClassicalResults.area (capNiche K) ∧
        (∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
          paperGerverContacts t 1 ∉ capNiche K) ∧
        (∀ t ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 4),
          paperGerverPath t ∉ capNiche K) ∧
        (∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
          paperGerverContacts t 3 ∉ capNiche K) := by
  obtain ⟨-, ⟨K, hKset, hKniche⟩, -, -⟩ := gerver_paperNiche_identification
  obtain ⟨f, hfc, hfgraph, hfsurj, hab, hfa, hfb, hfpos⟩ := exists_gerverRoofHeight
  obtain ⟨h0, h5, h01, h12, h23, h34, h45⟩ := gerverStageTimes_order
  have hfcon : ContinuousOn f (Set.Icc gerverNicheLeft gerverNicheRight) := hfc.continuousOn
  -- the niche and its closure, read as subgraphs of the roof height
  have hniche : capNiche K = strictSubgraph gerverNicheLeft gerverNicheRight f := by
    rw [hKniche, gerverLiteralNiche_eq_strictSubgraph hfgraph hfsurj]
  have hclos : closure (capNiche K) = closedSubgraph gerverNicheLeft gerverNicheRight f := by
    rw [hniche, closure_strictSubgraph hab hfcon hfa hfb hfpos]
  -- the region enclosed by the counterclockwise loop around the same graph
  have hintU := jordanInterior_range_positiveGraphLoop hab hfcon hfa hfb hfpos
  have hdiff := closedSubgraph_sdiff_openSubgraph hab hfcon hfa hfb hfpos
  have hCUR := closedSubgraph_eq_openSubgraph_union_range hab hfcon hfa hfb hfpos
  have hfront : frontier (closure (capNiche K)) =
      Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f) := by
    rw [hclos]
    exact frontier_closedSubgraph hab hfcon hfa hfb hfpos
  obtain ⟨hrange, hOJP⟩ := gerverNicheBoundary_orientedJordan hfc hfgraph hab hfa hfb hfpos
  -- the boundary traversal sweeps a null set, so all three regions have the same area
  have hvolR : MeasureTheory.volume
      (Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f)) = 0 := by
    rw [← hrange]
    exact ContinuousBVPaths.volume_range_eq_zero_of_injOn (show (0 : ℝ) ≤ 4 by norm_num)
      ⟨gerverNicheBoundary, gerverNicheBoundary_mem_continuousBV⟩ hOJP.2.2.2.2.2.1
  have hCU : MeasureTheory.volume (closedSubgraph gerverNicheLeft gerverNicheRight f) =
      MeasureTheory.volume (openSubgraph gerverNicheLeft gerverNicheRight f) :=
    (MeasureTheory.measure_eq_measure_of_null_sdiff openSubgraph_subset_closedSubgraph
      (by rw [hdiff]; exact hvolR)).symm
  have hCS : MeasureTheory.volume (closedSubgraph gerverNicheLeft gerverNicheRight f) =
      MeasureTheory.volume (strictSubgraph gerverNicheLeft gerverNicheRight f) := by
    refine (MeasureTheory.measure_eq_measure_of_null_sdiff strictSubgraph_subset_closedSubgraph
      (MeasureTheory.measure_mono_null ?_ hvolR)).symm
    rw [← hdiff]
    exact fun q hq ↦ ⟨hq.1, fun hU ↦ hq.2 ⟨hq.1.1, hq.1.2.1, hq.1.2.2.1, hU.2.2.2⟩⟩
  have hroofnot : ∀ s : Set.Icc (0 : ℝ) (Real.pi / 2), gerverNicheRoof s ∉ capNiche K :=
    fun s ↦ hniche ▸ gerverNicheRoof_notMem_strictSubgraph hfgraph s
  refine ⟨K, hKset, ⟨gerverNicheBoundary, gerverNicheBoundary_mem_continuousBV⟩, rfl, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfront]
    exact hOJP
  · rw [hclos, show Set.range (⟨gerverNicheBoundary, gerverNicheBoundary_mem_continuousBV⟩ :
      ContinuousBVPaths 0 4).val = Set.range gerverNicheBoundary from rfl, hrange, hintU, hCUR]
  · rw [hclos, hniche]
    unfold ClassicalResults.area
    rw [hCS]
  · rw [curveArea_eq_jordanInterior_area 0 4 (show (0 : ℝ) ≤ 4 by norm_num)
      (Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f))
      ⟨gerverNicheBoundary, gerverNicheBoundary_mem_continuousBV⟩ hOJP, hintU, hniche]
    unfold ClassicalResults.area
    rw [← hCU, hCS]
  · intro t ht
    rw [h5] at ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith [ht.1], ht.2⟩
    rw [← gerverNicheRoof_of_ge_three htI ht.1]
    exact hroofnot _
  · intro t ht
    obtain ⟨σ, hσ1, hσ2, hσ⟩ := exists_gerverRoofReverseTime ht
    have hσI : σ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
    rw [← hσ, ← gerverNicheRoof_mid hσI hσ1 hσ2]
    exact hroofnot _
  · intro t ht
    rw [h0] at ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨ht.1, by linarith [ht.2]⟩
    rw [← gerverNicheRoof_of_le_two htI ht.2]
    exact hroofnot _

/-! ## The interior of the base segment -/

/-- The two ends of the base segment of the niche boundary are distinct: they are the images
of the parameters `3` and `0` of the boundary traversal, which is injective on `[0, 4)`. -/
theorem gerver_niche_bottom_ends_ne :
    paperGerverContacts 0 3 ≠ paperGerverContacts (Real.pi / 2) 1 := by
  obtain ⟨_, _, Γ, hΓ, hOJP, -⟩ := gerver_niche_orientation
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 4 := by norm_num
  have hmem3 : (3 : ℝ) ∈ Set.Icc (0 : ℝ) 4 := by norm_num
  have hb0 : gerverNicheBoundary ⟨0, hmem0⟩ = paperGerverContacts (Real.pi / 2) 1 := by
    norm_num [gerverNicheBoundary]
  have hb3 : gerverNicheBoundary ⟨3, hmem3⟩ = paperGerverContacts 0 3 := by
    norm_num [gerverNicheBoundary]
  intro heq
  have hinj := hOJP.2.2.2.2.2.1
  rw [hΓ] at hinj
  have h := hinj (show ((⟨3, hmem3⟩ : Set.Icc (0 : ℝ) 4) : ℝ) < 4 by norm_num)
    (show ((⟨0, hmem0⟩ : Set.Icc (0 : ℝ) 4) : ℝ) < 4 by norm_num) (by rw [hb3, hb0, heq])
  have h' := congrArg Subtype.val h
  norm_num at h'

/-- Every interior point of the base segment of the niche boundary, which runs from `D(0)` to
`B(π/2)`, lies in the literal Gerver niche.  Both ends sit on the wall, so the segment is
horizontal and its interior points have strictly intermediate horizontal coordinate; the
intermediate value theorem then puts a roof point directly above such a point, where the roof
has strictly positive height, and the description of the niche as the strict region under the
roof concludes. -/
theorem gerver_bottom_segment_mem_gerverLiteralNiche {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - a) • paperGerverContacts 0 3 + a • paperGerverContacts (Real.pi / 2) 1 ∈
      gerverLiteralNiche := by
  obtain ⟨h0, h5, h01, h12, h23, h34, h45⟩ := gerverStageTimes_order
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hD0y : paperGerverContacts 0 3 1 = 0 := gerver_niche_piece_endpoints.2.2.2
  have hBTy : paperGerverContacts (Real.pi / 2) 1 1 = 0 := gerver_niche_piece_endpoints.2.2.1
  -- The two ends differ, and they agree in their second coordinate, so they differ in the first.
  have hx : paperGerverContacts 0 3 0 ≠ paperGerverContacts (Real.pi / 2) 1 0 := by
    intro h
    refine gerver_niche_bottom_ends_ne ?_
    ext i
    fin_cases i
    · exact h
    · exact hD0y.trans hBTy.symm
  set P : Point := (1 - a) • paperGerverContacts 0 3 + a • paperGerverContacts (Real.pi / 2) 1
    with hPdef
  have hP0 : P 0 = (1 - a) * paperGerverContacts 0 3 0 +
      a * paperGerverContacts (Real.pi / 2) 1 0 := by
    simp [hPdef, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hP1 : P 1 = 0 := by
    simp [hPdef, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hD0y, hBTy]
  -- The roof, read as a curve of a real parameter, runs from one end of the segment to the other.
  have hR0 : gerverRoofCurve 0 = paperGerverContacts 0 3 := by
    rw [gerverRoofCurve, ite_eq_left (show (0 : ℝ) ≤ gerverStageTimes 2 by linarith)]
  have hRT : gerverRoofCurve (Real.pi / 2) = paperGerverContacts (Real.pi / 2) 1 := by
    rw [gerverRoofCurve, ite_eq_right (not_le.mpr (by linarith)),
      ite_eq_right (not_le.mpr (by linarith))]
  -- The intermediate value theorem produces a roof parameter above `P`.
  have hcont : ContinuousOn (fun s : ℝ ↦ gerverRoofCurve s 0) (Set.uIcc 0 (Real.pi / 2)) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp
      continuous_gerverRoofCurve).continuousOn
  have hPmem : P 0 ∈ Set.uIcc (gerverRoofCurve 0 0) (gerverRoofCurve (Real.pi / 2) 0) := by
    rw [hR0, hRT, Set.mem_uIcc, hP0]
    rcases lt_or_gt_of_ne hx with h | h
    · exact Or.inl ⟨by nlinarith [ha.1, ha.2], by nlinarith [ha.1, ha.2]⟩
    · exact Or.inr ⟨by nlinarith [ha.1, ha.2], by nlinarith [ha.1, ha.2]⟩
  obtain ⟨σ, hσmem, hσraw⟩ := intermediate_value_uIcc hcont hPmem
  have hσ : gerverRoofCurve σ 0 = P 0 := hσraw
  rw [Set.uIcc_of_le hpi.le] at hσmem
  -- That parameter is interior, because `P` is not an end of the segment.
  have hσ0 : σ ≠ 0 := by
    intro h
    rw [h, hR0, hP0] at hσ
    rcases mul_eq_zero.mp (show a * (paperGerverContacts (Real.pi / 2) 1 0 -
        paperGerverContacts 0 3 0) = 0 by linarith) with h' | h'
    · exact absurd h' (ne_of_gt ha.1)
    · exact hx (by linarith)
  have hσT : σ ≠ Real.pi / 2 := by
    intro h
    rw [h, hRT, hP0] at hσ
    rcases mul_eq_zero.mp (show (1 - a) * (paperGerverContacts (Real.pi / 2) 1 0 -
        paperGerverContacts 0 3 0) = 0 by linarith) with h' | h'
    · exact absurd h' (by linarith [ha.2] : (1 : ℝ) - a ≠ 0)
    · exact hx (by linarith)
  have hheight : 0 < gerverNicheRoof ⟨σ, hσmem⟩ 1 :=
    gerver_niche_roof_positive ⟨σ, hσmem⟩
      ⟨lt_of_le_of_ne hσmem.1 (Ne.symm hσ0), lt_of_le_of_ne hσmem.2 hσT⟩
  rw [gerverLiteralNiche_eq_roofFill]
  exact ⟨⟨σ, hσmem⟩, by rw [← gerverRoofCurve_eq ⟨σ, hσmem⟩]; exact hσ.symm,
    hP1.ge, by rw [hP1]; exact hheight⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The contact geometry of the paper Gerver sofa

Gerver's sofa is a monotone sofa, and its right-angle cap has all the contact geometry the
upper-bound argument reads off a monotone sofa: selected cap vertices and inner corner given
by the paper's curves `A`, `C` and `x`, a counterclockwise Jordan traversal of the niche
boundary, the interior of the base segment inside the niche and the three roof pieces outside
it, the two inner contact curves on the two inner walls of the supporting hallway, and the
signs of their stage speeds along the frame directions.

Every clause is about one and the same cap.  The cap is taken from `paperGerverCap_injectivity`
— which also supplies the density hypothesis that makes the selected contacts well defined —
and the caps produced by cap-support identification, niche identification and niche
orientation are identified with it through their common carrier `gerverOuterCap`.  The clauses
themselves are then assembled from the identification theorems together with
`gerver_bottom_segment_mem_gerverLiteralNiche`, the frame descriptions
`mem_rotatingHallwayParts_bRay_iff` and `mem_rotatingHallwayParts_dRay_iff` of the two inner
walls, the closed-interval velocity signs `paperGerverVelocityComponents_fst_nonpos` and
`paperGerverVelocityComponents_snd_nonneg`, and the stage speeds
`hasDerivWithinAt_paperGerverContacts_one_neg_smul` and
`hasDerivWithinAt_paperGerverContacts_three_pos_smul`.
-/

public section

noncomputable section

namespace MovingSofa

theorem paperGerver_contact_geometry :
    IsMonotoneSofa paperGerverSofa ∧
    ∃ K : RightAngleCapSpace,
      (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2) ∧
      ∃ hK : ∃ r s, HasCapDensities K r s,
        (∀ t : Set.Icc (0 : ℝ) (Real.pi / 2),
          (nondegenerateCapData K hK).1.1 t = paperGerverContacts t 0 ∧
          (nondegenerateCapData K hK).1.2 t = paperGerverContacts t 2 ∧
          capInnerCorner K t = paperGerverPath t) ∧
        (∃ Γ : ContinuousBVPaths 0 4, Γ.val = gerverNicheBoundary ∧
          IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 4)
            (frontier (closure (capNiche K))) true Γ.val ∧
          closure (capNiche K) = jordanInterior (Set.range Γ.val) ∪ Set.range Γ.val ∧
          ClassicalResults.area (closure (capNiche K)) = ClassicalResults.area (capNiche K)) ∧
        (∀ a ∈ Set.Ioo (0 : ℝ) 1,
          (1 - a) • paperGerverContacts 0 3 +
            a • paperGerverContacts (Real.pi / 2) 1 ∈ capNiche K) ∧
        (∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
          paperGerverContacts t 1 ∉ capNiche K ∧
          paperGerverContacts t 1 ∈
            (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).bRay) ∧
        (∀ t ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 4),
          paperGerverPath t ∉ capNiche K) ∧
        (∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
          paperGerverContacts t 3 ∉ capNiche K ∧
          paperGerverContacts t 3 ∈
            (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).dRay) ∧
        (∀ i : Fin 5, i = 3 ∨ i = 4 → ∀ t ∈ gerverStageIntervals i,
          ∃ c : ℝ, c < 0 ∧
            HasDerivWithinAt (fun s ↦ paperGerverContacts s 1)
              (c • tangentVector (t : Real.Angle)) (gerverStageIntervals i) t) ∧
        (∀ i : Fin 5, i = 0 ∨ i = 1 → ∀ t ∈ gerverStageIntervals i,
          ∃ c : ℝ, 0 < c ∧
            HasDerivWithinAt (fun s ↦ paperGerverContacts s 3)
              (c • normalVector (t : Real.Angle)) (gerverStageIntervals i) t) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hangsum : ∀ t : ℝ, (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + t : ℝ) : Real.Angle) := fun t => by
    rw [← Real.Angle.coe_add, add_comm]
  have ht0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have ht5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have h03 : (0 : ℝ) < gerverStageTimes 3 := by
    rw [← ht0]; exact gerverStageTimes_strictMono (by decide)
  have h25 : gerverStageTimes 2 < Real.pi / 2 := by
    rw [← ht5]; exact gerverStageTimes_strictMono (by decide)
  -- ### One cap serves every clause: the four theorems below all speak about `gerverOuterCap`
  obtain ⟨K, hKset, ⟨r, s, hdens, -⟩, -, -⟩ := paperGerverCap_injectivity
  have hK : ∃ r s, HasCapDensities K r s := ⟨r, s, hdens⟩
  obtain ⟨-, hGeq, -, -, hcapeq, ⟨K₁, hK₁set, hsing, hA0, hAT, hC0, hCT⟩, hsup⟩ :=
    gerver_capSupport_identification
  have hKcarrier : (K.val : Set Point) = gerverOuterCap := by rw [hKset, hGeq, hcapeq]
  have hcapK : ∀ K' : RightAngleCapSpace, (K'.val : Set Point) = gerverOuterCap → K' = K :=
    fun K' h => Subtype.ext (SetLike.coe_injective (h.trans hKcarrier.symm))
  rw [hcapK K₁ hK₁set] at hsing hA0 hAT hC0 hCT
  obtain ⟨-, ⟨K₂, hK₂set, hniche⟩, -, hmono⟩ := gerver_paperNiche_identification
  rw [hcapK K₂ hK₂set] at hniche
  obtain ⟨K₃, hK₃set, Γ, hΓ, hOJP, hclos, harea, -, hnotB, hnotx, hnotD⟩ :=
    gerver_niche_orientation
  rw [hcapK K₃ hK₃set] at hOJP hclos harea hnotB hnotx hnotD
  -- ### The two support values of the cap, and the resulting inner corner
  have hsupK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportValue (K.val : Set Point) (t : Real.Angle) =
        inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
      supportValue (K.val : Set Point) ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
    rw [hKcarrier]
    exact hsup gerverOuterCap (Or.inl rfl)
  have hcorner : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      capInnerCorner K t = paperGerverPath t := by
    intro t ht
    rw [capInnerCorner,
      (rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.1, hangsum,
      (hsupK t ht).1, (hsupK t ht).2, add_sub_cancel_right, add_sub_cancel_right,
      inner_normalVector_smul_add_inner_tangentVector_smul]
  refine ⟨hmono, K, hKset, hK, ?_, ⟨Γ, hΓ, hOJP, hclos, harea⟩, ?_, ?_, hnotx, ?_,
    fun i hi t ht => hasDerivWithinAt_paperGerverContacts_one_neg_smul hi ht,
    fun i hi t ht => hasDerivWithinAt_paperGerverContacts_three_pos_smul hi ht⟩
  · -- ### The selected cap vertices and the inner corner
    -- Strictly inside the interval the two exposed faces are singletons; at the two endpoints
    -- the selected contacts are the frozen one-sided contacts of cap-support identification,
    -- with the nondegeneracy proposition equating the two vertices at `π / 2`.
    intro t
    have htI : (t : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := t.2
    refine ⟨?_, ?_, hcorner t htI⟩
    · dsimp only [nondegenerateCapData]
      split_ifs with hT
      · rw [hT, hAT]
        rfl
      · rcases eq_or_lt_of_le htI.1 with h0 | h0
        · rw [← h0, hA0]
          exact congrArg (fun a : Real.Angle ↦ (edgeVertices (K.val) a).1) Real.Angle.coe_zero
        · have hmem : (t : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
            ⟨h0, lt_of_le_of_ne htI.2 hT⟩
          change (edgeVertices (K.val) ((t : ℝ) : Real.Angle)).1 = _
          rw [edgeVertices_eq_of_exposedEdge_singleton (hsing _ hmem).1]
    · change (edgeVertices (K.val) (((t : ℝ) + Real.pi / 2 : ℝ) : Real.Angle)).1 = _
      rcases eq_or_lt_of_le htI.1 with h0 | h0
      · rw [← h0, zero_add, hC0]
      rcases eq_or_lt_of_le htI.2 with hT | hT
      · have hnd : (edgeVertices (K.val) ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).1 =
            (edgeVertices (K.val) ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).2 :=
          ((capDensities_contact_eq K hK).2 (Real.pi / 2) ⟨hpi, le_rfl⟩).1
        rw [hT, hnd, hCT]
        exact congrArg (fun a : Real.Angle ↦ (edgeVertices (K.val) a).2)
          (congrArg (fun x : ℝ ↦ (x : Real.Angle)) (by ring))
      · rw [edgeVertices_eq_of_exposedEdge_singleton (hsing _ ⟨h0, hT⟩).2]
  · -- ### The open base segment lies in the niche
    intro a ha
    rw [hniche]
    exact gerver_bottom_segment_mem_gerverLiteralNiche ha
  · -- ### The second contact curve lies on the downward inner wall
    -- With `B = x + α v`, the two support values turn the wall condition into `α t ≤ 0`.
    intro t ht
    refine ⟨hnotB t ht, ?_⟩
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [ht.1], by rw [← ht5]; exact ht.2⟩
    rw [mem_rotatingHallwayParts_bRay_iff, hangsum, (hsupK t htI).1, (hsupK t htI).2,
      add_sub_cancel_right, add_sub_cancel_right]
    have hB : paperGerverContacts t 1 =
        paperGerverPath t + (paperGerverVelocityComponents t).1 •
          tangentVector (t : Real.Angle) := rfl
    rw [hB, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_tangentVector_normalVector_real t t, sub_self, Real.sin_zero,
      inner_tangentVector_self]
    exact ⟨by ring, by nlinarith [paperGerverVelocityComponents_fst_nonpos htI]⟩
  · -- ### The fourth contact curve lies on the leftward inner wall
    -- With `D = x - β u`, the same two support values turn the wall condition into `0 ≤ β t`.
    intro t ht
    refine ⟨hnotD t ht, ?_⟩
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by rw [← ht0]; exact ht.1, by linarith [ht.2]⟩
    rw [mem_rotatingHallwayParts_dRay_iff, hangsum, (hsupK t htI).1, (hsupK t htI).2,
      add_sub_cancel_right, add_sub_cancel_right]
    have hD : paperGerverContacts t 3 =
        paperGerverPath t - (paperGerverVelocityComponents t).2 •
          normalVector (t : Real.Angle) := rfl
    rw [hD, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
      inner_normalVector_self, inner_normalVector_tangentVector]
    exact ⟨by nlinarith [paperGerverVelocityComponents_snd_nonneg htI], by ring⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The left and right tails of the Gerver cap

`gerver_tailGeometry` identifies the two tails cut out of the Gerver cap by the inner hallway
walls.  Each tail is cut out by a one-parameter family of supporting half-planes whose contact
points are the two inner Gerver contact curves `B` and `D`, so the envelope-tangency lemmas of
`MovingSofa/Convex/EnvelopeFace.lean` identify every intervening face of a tail with a single
point of the corresponding contact curve, and the stagewise monotonicity of the contact curves
against a fixed frame direction (`MovingSofa/Gerver/StageRegularity.lean`) supplies both the
containment of the contact curves in the tails and the injectivity of the two
parametrizations.  The support sums are the cut identity `h_L (s + π) = -m s`.
-/

public section

noncomputable section

namespace MovingSofa

/-- A continuous injective parametrization traces the directed arc with the specified
endpoints. -/
def ParametrizesDirectedArc (f : ℝ → Point) (a b : ℝ) (Γ : DirectedArcData) : Prop :=
  a < b ∧ ContinuousOn f (Set.Icc a b) ∧ Set.InjOn f (Set.Icc a b) ∧
    f '' Set.Icc a b = Γ.carrier ∧ f a = Γ.startPoint ∧ f b = Γ.endPoint

private def gerverLeftTailSupport (s : ℝ) : ℝ :=
  inner ℝ (paperGerverPath (s - Real.pi / 2))
    (tangentVector ((s - Real.pi / 2 : ℝ) : Real.Angle))

private def gerverRightTailSupport (s : ℝ) : ℝ :=
  inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle))

private theorem gerver_tail_membership (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    (StrictAntiOn (fun s ↦ inner ℝ (paperGerverContacts s 3)
     (tangentVector ((gerverStageTimes 4 : ℝ) : Real.Angle)))
     (Set.Icc (gerverStageTimes 0) (gerverStageTimes 2))) ∧
    (StrictMonoOn (fun s ↦ inner ℝ (paperGerverContacts s 1)
     (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle)))
     (Set.Icc (gerverStageTimes 3) (gerverStageTimes 5))) ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
     paperGerverContacts t 3 ∈ (D : Set Point)) ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
     paperGerverContacts t 1 ∈ (B : Set Point)) := by
  -- ### One cap serves every clause, and it carries the literal contact geometry
  obtain ⟨-, hGeq, -, -, hcapeq, -, -⟩ := gerver_capSupport_identification
  have hcarrier : (K.val.val : Set Point) = gerverOuterCap := by rw [hK, hGeq, hcapeq]
  obtain ⟨-, K', hK'set, hdens, hsel, -, -, hBwall, -, hDwall, -, -⟩ :=
    paperGerver_contact_geometry
  have hKeq : K' = K.val := Subtype.ext (SetLike.coe_injective (hK'set.trans hK.symm))
  subst hKeq
  have ht0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have ht5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have hr : paperGerverConstants.2.1 = gerverStageTimes 1 := rfl
  have hl : paperGerverConstants.2.2 = gerverStageTimes 4 := rfl
  have h01' : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_strictMono (by decide)
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_strictMono (by decide)
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have h34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_strictMono (by decide)
  have h45' : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_strictMono (by decide)
  have h01 : (0 : ℝ) < gerverStageTimes 1 := ht0 ▸ h01'
  have h45 : gerverStageTimes 4 < Real.pi / 2 := ht5 ▸ h45'
  -- ### The support coordinates of the cap along the path
  have hcorner : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), capInnerCorner K.val t = paperGerverPath t :=
    fun t ht ↦ (hsel ⟨t, ht⟩).2.2
  have hsupu : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) =
        supportValue (K.val.val : Set Point) (t : Real.Angle) - 1 := by
    intro t ht
    rw [← hcorner t ht]
    exact inner_capInnerCorner_normalVector K.val t
  have hsupv : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) =
        supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    intro t ht
    rw [← hcorner t ht]
    exact inner_capInnerCorner_tangentVector K.val t
  -- ### The two families of supporting lines cutting the tails out of the cap
  have hmDval : ∀ t : ℝ, gerverLeftTailSupport (t + Real.pi / 2) =
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) := by
    intro t
    simp only [gerverLeftTailSupport, add_sub_cancel_right]
  have hmDsup : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), gerverLeftTailSupport (t + Real.pi / 2) =
      supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
    fun t ht ↦ (hmDval t).trans (hsupv t ht)
  have hcapupper : ∀ q ∈ (K.val.val : Set Point), 0 ≤ q 1 := fun q hq ↦ by
    simpa only [inner_normalVector_pi_div_two] using
      K.val.inner_normalVector_pi_div_two_nonneg hq
  have hcapD : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      paperGerverContacts t 3 ∈ (K.val.val : Set Point) := fun t ht ↦
    hcarrier ▸ gerver_niche_roof_membership.1 t ht
  have hcapB : ∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      paperGerverContacts t 1 ∈ (K.val.val : Set Point) := fun t ht ↦
    hcarrier ▸ gerver_niche_roof_membership.2.2 t ht
  -- ### Each contact curve stays above its own distinguished wall
  have hantiD : ∀ i : Fin 5, (i = 0 ∨ i = 1) →
      StrictAntiOn (fun s ↦ inner ℝ (paperGerverContacts s 3)
        (tangentVector ((gerverStageTimes 4 : ℝ) : Real.Angle))) (gerverStageIntervals i) := by
    intro i hi
    refine strictAntiOn_inner_paperGerverContacts_three hi ?_ ?_ <;> intro s hs <;>
      rcases hi with rfl | rfl
    · rw [gerverStageIntervals_zero] at hs; linarith only [hs.2, h12, h23, h34]
    · rw [gerverStageIntervals_one] at hs; linarith only [hs.2, h23, h34]
    · rw [gerverStageIntervals_zero] at hs; linarith only [hs.1, ht0, h45, Real.pi_pos]
    · rw [gerverStageIntervals_one] at hs; linarith only [hs.1, h01, h45, Real.pi_pos]
  have hmonoB : ∀ i : Fin 5, (i = 3 ∨ i = 4) →
      StrictMonoOn (fun s ↦ inner ℝ (paperGerverContacts s 1)
        (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle))) (gerverStageIntervals i) := by
    intro i hi
    refine strictMonoOn_inner_paperGerverContacts_one hi ?_ ?_ <;> intro s hs <;>
      rcases hi with rfl | rfl
    · rw [gerverStageIntervals_three] at hs; linarith only [hs.1, h12, h23]
    · rw [gerverStageIntervals_four] at hs; linarith only [hs.1, h12, h23, h34]
    · rw [gerverStageIntervals_three] at hs; linarith only [hs.2, h45, h01, Real.pi_pos]
    · rw [gerverStageIntervals_four] at hs; linarith only [hs.2, ht5, h01, Real.pi_pos]
  have hstrictD : StrictAntiOn (fun s ↦ inner ℝ (paperGerverContacts s 3)
      (tangentVector ((gerverStageTimes 4 : ℝ) : Real.Angle)))
      (Set.Icc (gerverStageTimes 0) (gerverStageTimes 2)) := by
    rw [← Set.Icc_union_Icc_eq_Icc h01'.le h12.le]
    exact (gerverStageIntervals_zero ▸ hantiD 0 (Or.inl rfl)).union
      (gerverStageIntervals_one ▸ hantiD 1 (Or.inr rfl))
      (isGreatest_Icc h01'.le) (isLeast_Icc h12.le)
  have hstrictB : StrictMonoOn (fun s ↦ inner ℝ (paperGerverContacts s 1)
      (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle)))
      (Set.Icc (gerverStageTimes 3) (gerverStageTimes 5)) := by
    rw [← Set.Icc_union_Icc_eq_Icc h34.le h45'.le]
    exact (gerverStageIntervals_three ▸ hmonoB 3 (Or.inl rfl)).union
      (gerverStageIntervals_four ▸ hmonoB 4 (Or.inr rfl))
      (isGreatest_Icc h34.le) (isLeast_Icc h45'.le)
  have hkeyD : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      inner ℝ (paperGerverContacts (gerverStageTimes 2) 3)
          (tangentVector ((gerverStageTimes 4 : ℝ) : Real.Angle)) ≤
        inner ℝ (paperGerverContacts t 3)
          (tangentVector ((gerverStageTimes 4 : ℝ) : Real.Angle)) :=
    fun t ht ↦ hstrictD.antitoneOn ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2
  have hkeyB : ∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      inner ℝ (paperGerverContacts (gerverStageTimes 3) 1)
          (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle)) ≤
        inner ℝ (paperGerverContacts t 1)
          (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle)) :=
    fun t ht ↦ hstrictB.monotoneOn ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  have hDfix : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      paperGerverContacts t 3 ∈ (innerWallUpperHalfPlanes K.val (gerverStageTimes 4)).2 := by
    intro t ht
    have hl4 : gerverStageTimes 4 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith only [h01, h12, h23, h34], h45.le⟩
    change supportValue (K.val.val : Set Point)
        ((gerverStageTimes 4 + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ (paperGerverContacts t 3)
        (normalVector ((gerverStageTimes 4 + Real.pi / 2 : ℝ) : Real.Angle))
    rw [← hmDsup _ hl4, hmDval, normalVector_add_pi_div_two_real,
      ← gerver_niche_piece_endpoints.2.1]
    exact hkeyD t ht
  have hBfix : ∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      paperGerverContacts t 1 ∈ (innerWallUpperHalfPlanes K.val (gerverStageTimes 1)).1 := by
    intro t ht
    have hr1 : gerverStageTimes 1 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨h01.le, by linarith only [h12, h23, h34, h45]⟩
    change supportValue (K.val.val : Set Point) ((gerverStageTimes 1 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ (paperGerverContacts t 1) (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle))
    rw [← hsupu _ hr1, ← gerver_niche_piece_endpoints.1]
    exact hkeyB t ht
  -- ### The remaining walls are excluded by the niche
  have hiq : ∀ s : ℝ, (rotatingHallwayParts (K.val.val : Set Point) (s : Real.Angle)).innerQuadrant
      = innerQuadrant (K.val.val : Set Point) s := by
    intro s
    rw [(rotatingHallwayParts_formulas (K.val.val : Set Point)
      (s : Real.Angle)).2.2.2.2.2.2.2.2, innerQuadrant, ← Real.Angle.coe_add]
  have hDside : (distinguishedCapSides K.val).2.upperHalfPlane =
      (innerWallUpperHalfPlanes K.val (gerverStageTimes 4)).2 := by rw [← hl]; rfl
  have hBside : (distinguishedCapSides K.val).1.upperHalfPlane =
      (innerWallUpperHalfPlanes K.val (gerverStageTimes 1)).1 := by rw [← hr]; rfl
  have hDwedge : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      ∀ s ∈ Set.Ioo (0 : ℝ) (gerverStageTimes 4),
      paperGerverContacts t 3 ∈ (innerWallUpperHalfPlanes K.val s).2 := by
    intro t ht s hs
    by_contra hmem
    have hquad := (cap_tail_monotonicity_intervals K).2.2.2 s
      ⟨hs.1.le, by rw [hl]; exact hs.2⟩ ⟨hs.1, by linarith only [hs.2, h45]⟩
    have hfix : paperGerverContacts t 3 ∈ (distinguishedCapSides K.val).2.upperHalfPlane := by
      rw [hDside]
      exact hDfix t ht
    have hin : paperGerverContacts t 3 ∈
        ((distinguishedCapSides K.val).2.upperHalfPlane ∩ {p : Point | 0 ≤ p 1}) \
          (innerWallUpperHalfPlanes K.val s).2 :=
      ⟨⟨hfix, hcapupper _ (hcapD t ht)⟩, hmem⟩
    rw [← hquad] at hin
    exact (hDwall t ht).1 ⟨hin.2.1, Set.mem_iUnion₂.2
      ⟨s, ⟨hs.1, by linarith only [hs.2, h45]⟩, (hiq s) ▸ hin.2.2⟩⟩
  have hBwedge : ∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      ∀ s ∈ Set.Ioo (gerverStageTimes 1) (Real.pi / 2),
      paperGerverContacts t 1 ∈ (innerWallUpperHalfPlanes K.val s).1 := by
    intro t ht s hs
    by_contra hmem
    have hquad := (cap_tail_monotonicity_intervals K).2.2.1 s
      ⟨by rw [hr]; exact hs.1, hs.2.le⟩ ⟨by linarith only [hs.1, h01], hs.2⟩
    have hfix : paperGerverContacts t 1 ∈ (distinguishedCapSides K.val).1.upperHalfPlane := by
      rw [hBside]
      exact hBfix t ht
    have hin : paperGerverContacts t 1 ∈
        ((distinguishedCapSides K.val).1.upperHalfPlane ∩ {p : Point | 0 ≤ p 1}) \
          (innerWallUpperHalfPlanes K.val s).1 :=
      ⟨⟨hfix, hcapupper _ (hcapB t ht)⟩, hmem⟩
    rw [← hquad] at hin
    exact (hBwall t ht).1 ⟨hin.2.1, Set.mem_iUnion₂.2
      ⟨s, ⟨by linarith only [hs.1, h01], hs.2⟩, (hiq s) ▸ hin.2.2⟩⟩
  -- ### Both contact curves lie in their tails
  have hDmem : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      paperGerverContacts t 3 ∈ (D : Set Point) := by
    intro t ht
    rw [hD]
    refine ⟨hcapD t ht, Set.mem_iInter₂.2 fun s hs ↦ ?_⟩
    rw [hl] at hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · change supportValue (K.val.val : Set Point) ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
        inner ℝ (paperGerverContacts t 3) (normalVector ((s + Real.pi / 2 : ℝ) : Real.Angle))
      rw [← h0, zero_add, K.val.property.2.2.2.1, inner_normalVector_pi_div_two]
      simpa only [sub_self] using hcapupper _ (hcapD t ht)
    rcases eq_or_lt_of_le hs.2 with h4 | h4
    · exact h4 ▸ hDfix t ht
    · exact hDwedge t ht s ⟨h0, h4⟩
  have hBmem : ∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      paperGerverContacts t 1 ∈ (B : Set Point) := by
    intro t ht
    rw [hB]
    refine ⟨hcapB t ht, Set.mem_iInter₂.2 fun s hs ↦ ?_⟩
    rw [hr] at hs
    rcases eq_or_lt_of_le hs.2 with hT | hT
    · change supportValue (K.val.val : Set Point) (s : Real.Angle) - 1 ≤
        inner ℝ (paperGerverContacts t 1) (normalVector (s : Real.Angle))
      rw [hT, K.val.property.2.2.2.1, inner_normalVector_pi_div_two]
      simpa only [sub_self] using hcapupper _ (hcapB t ht)
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · exact h1 ▸ hBfix t ht
    · exact hBwedge t ht s ⟨h1, hT⟩
  -- ### The singleton faces along the two contact curves
  exact ⟨hstrictD, hstrictB, hDmem, hBmem⟩

private theorem gerver_tail_support_lines (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
     inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) =
       supportValue (K.val.val : Set Point) (t : Real.Angle) - 1) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
     inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) =
       supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) ∧
    (∀ t : ℝ, gerverLeftTailSupport (t + Real.pi / 2) =
     inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle))) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), gerverLeftTailSupport (t + Real.pi / 2) =
     supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) ∧
    (∀ t : ℝ, HasDerivAt gerverLeftTailSupport
     (inner ℝ (paperGerverContacts t 3) (tangentVector ((t + Real.pi / 2 : ℝ) : Real.Angle)))
     (t + Real.pi / 2)) ∧
    (∀ t : ℝ, HasDerivAt gerverRightTailSupport
     (inner ℝ (paperGerverContacts t 1) (tangentVector (t : Real.Angle))) t) ∧
    (∀ q ∈ (D : Set Point), ∀ s ∈ Set.Icc (Real.pi / 2)
     (gerverStageTimes 4 + Real.pi / 2), gerverLeftTailSupport s ≤ inner ℝ q (normalVector (s :
       Real.Angle))) ∧
    (∀ q ∈ (B : Set Point), ∀ s ∈ Set.Icc (gerverStageTimes 1) (Real.pi / 2),
     gerverRightTailSupport s ≤ inner ℝ q (normalVector (s : Real.Angle))) ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
     inner ℝ (paperGerverContacts t 3) (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
       gerverLeftTailSupport (t + Real.pi / 2)) ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
     inner ℝ (paperGerverContacts t 1) (normalVector (t : Real.Angle)) = gerverRightTailSupport t)
       := by
  -- ### One cap serves every clause, and it carries the literal contact geometry
  obtain ⟨-, K', hK'set, hdens, hsel, -, -, hBwall, -, hDwall, -, -⟩ :=
    paperGerver_contact_geometry
  have hKeq : K' = K.val := Subtype.ext (SetLike.coe_injective (hK'set.trans hK.symm))
  subst hKeq
  have ht0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have ht5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have hr : paperGerverConstants.2.1 = gerverStageTimes 1 := rfl
  have hl : paperGerverConstants.2.2 = gerverStageTimes 4 := rfl
  have h01' : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_strictMono (by decide)
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_strictMono (by decide)
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have h34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_strictMono (by decide)
  have h45' : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_strictMono (by decide)
  have h01 : (0 : ℝ) < gerverStageTimes 1 := ht0 ▸ h01'
  have h45 : gerverStageTimes 4 < Real.pi / 2 := ht5 ▸ h45'
  -- ### The support coordinates of the cap along the path
  have hcorner : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), capInnerCorner K.val t = paperGerverPath t :=
    fun t ht ↦ (hsel ⟨t, ht⟩).2.2
  have hsupu : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) =
        supportValue (K.val.val : Set Point) (t : Real.Angle) - 1 := by
    intro t ht
    rw [← hcorner t ht]
    exact inner_capInnerCorner_normalVector K.val t
  have hsupv : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) =
        supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    intro t ht
    rw [← hcorner t ht]
    exact inner_capInnerCorner_tangentVector K.val t
  -- ### The two families of supporting lines cutting the tails out of the cap
  have hmDval : ∀ t : ℝ, gerverLeftTailSupport (t + Real.pi / 2) =
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) := by
    intro t
    simp only [gerverLeftTailSupport, add_sub_cancel_right]
  have hmDsup : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), gerverLeftTailSupport (t + Real.pi / 2) =
      supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
    fun t ht ↦ (hmDval t).trans (hsupv t ht)
  have hmDderiv : ∀ t : ℝ, HasDerivAt gerverLeftTailSupport
      (inner ℝ (paperGerverContacts t 3) (tangentVector ((t + Real.pi / 2 : ℝ) : Real.Angle)))
      (t + Real.pi / 2) := by
    intro t
    have h := (hasDerivAt_inner_paperGerverPath_tangentVector (t + Real.pi / 2 - Real.pi / 2)).comp
      (t + Real.pi / 2) ((hasDerivAt_id (t + Real.pi / 2)).sub_const (Real.pi / 2))
    rw [add_sub_cancel_right] at h
    rw [tangentVector_add_pi_div_two, inner_neg_right]
    unfold gerverLeftTailSupport
    simpa only [Function.comp_def, mul_one, id_eq] using h
  have hmBderiv : ∀ t : ℝ, HasDerivAt gerverRightTailSupport
      (inner ℝ (paperGerverContacts t 1) (tangentVector (t : Real.Angle))) t := by
    intro t
    unfold gerverRightTailSupport
    exact hasDerivAt_inner_paperGerverPath_normalVector t
  have hDle : ∀ q ∈ (D : Set Point), ∀ s ∈ Set.Icc (Real.pi / 2)
      (gerverStageTimes 4 + Real.pi / 2), gerverLeftTailSupport s ≤ inner ℝ q (normalVector (s :
        Real.Angle)) := by
    intro q hq s hs
    rw [hD] at hq
    have hs' : s - Real.pi / 2 ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2 :=
      ⟨by linarith only [hs.1], by rw [hl]; linarith only [hs.2]⟩
    have h : supportValue (K.val.val : Set Point)
        ((s - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
        inner ℝ q (normalVector ((s - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)) :=
      Set.mem_iInter₂.mp hq.2 (s - Real.pi / 2) hs'
    rw [sub_add_cancel] at h
    have hmem : s - Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨hs'.1, by linarith only [hs'.2, hl ▸ hs'.2, h45, ht5]⟩
    rw [show gerverLeftTailSupport s = gerverLeftTailSupport (s - Real.pi / 2 + Real.pi / 2) by rw
      [sub_add_cancel],
      hmDsup _ hmem, sub_add_cancel]
    exact h
  have hBle : ∀ q ∈ (B : Set Point), ∀ s ∈ Set.Icc (gerverStageTimes 1) (Real.pi / 2),
      gerverRightTailSupport s ≤ inner ℝ q (normalVector (s : Real.Angle)) := by
    intro q hq s hs
    rw [hB] at hq
    have h : supportValue (K.val.val : Set Point) (s : Real.Angle) - 1 ≤
        inner ℝ q (normalVector (s : Real.Angle)) :=
      Set.mem_iInter₂.mp hq.2 s ⟨by rw [hr]; exact hs.1, hs.2⟩
    simp only [gerverRightTailSupport]
    rw [hsupu s ⟨by linarith only [hs.1, h01], hs.2⟩]
    exact h
  -- ### The two contact curves touch their defining lines
  have hDtouch : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      inner ℝ (paperGerverContacts t 3) (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
        gerverLeftTailSupport (t + Real.pi / 2) := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨ht0 ▸ ht.1, by linarith only [ht.2, h23, h34, h45]⟩
    have h := (mem_rotatingHallwayParts_dRay_iff _ _ _).mp (hDwall t ht).2
    rw [normalVector_add_pi_div_two_real, hmDval t, h.2, hsupv t htI, Real.Angle.coe_add]
  have hBtouch : ∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      inner ℝ (paperGerverContacts t 1) (normalVector (t : Real.Angle)) = gerverRightTailSupport t
        := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith only [ht.1, h01, h12, h23], ht5 ▸ ht.2⟩
    have h := (mem_rotatingHallwayParts_bRay_iff _ _ _).mp (hBwall t ht).2
    simp only [gerverRightTailSupport]
    rw [hsupu t htI]
    exact h.1
  -- ### The cap lies in the upper half-plane, and both contact curves lie in the cap
  exact ⟨hsupu, hsupv, hmDval, hmDsup, hmDderiv, hmBderiv, hDle, hBle, hDtouch, hBtouch⟩

private theorem gerver_tail_contact_faces (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    (∀ t ∈ Set.Ioc (gerverStageTimes 0) (gerverStageTimes 2),
     exposedEdge D ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) = {paperGerverContacts t 3}) ∧
    (∀ t ∈ Set.Ico (gerverStageTimes 3) (gerverStageTimes 5),
     exposedEdge B ((Real.pi + t : ℝ) : Real.Angle) = {paperGerverContacts t 1}) ∧
    ((edgeVertices D ((3 * Real.pi / 2 + gerverStageTimes 4 : ℝ) : Real.Angle)).2 =
     paperGerverContacts (gerverStageTimes 2) 3) ∧
    ((edgeVertices B ((Real.pi + gerverStageTimes 1 : ℝ) : Real.Angle)).1 =
     paperGerverContacts (gerverStageTimes 3) 1) ∧
    ((edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
     paperGerverContacts 0 3) ∧
    ((edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 =
     paperGerverContacts (Real.pi / 2) 1) ∧
    (paperGerverContacts (gerverStageTimes 2) 3 ∈
     exposedEdge D ((3 * Real.pi / 2 + gerverStageTimes 4 : ℝ) : Real.Angle)) ∧
    (paperGerverContacts (gerverStageTimes 3) 1 ∈
     exposedEdge B ((Real.pi + gerverStageTimes 1 : ℝ) : Real.Angle)) := by
  -- ### One cap serves every clause, and it carries the literal contact geometry
  obtain ⟨-, hGeq, -, -, hcapeq, -, -⟩ := gerver_capSupport_identification
  have hcarrier : (K.val.val : Set Point) = gerverOuterCap := by rw [hK, hGeq, hcapeq]
  obtain ⟨-, K', hK'set, hdens, hsel, -, -, hBwall, -, hDwall, -, -⟩ :=
    paperGerver_contact_geometry
  have hKeq : K' = K.val := Subtype.ext (SetLike.coe_injective (hK'set.trans hK.symm))
  subst hKeq
  obtain ⟨hstrictD, hstrictB, hDmem, hBmem⟩ :=
    gerver_tail_membership K B D hK hB hD
  obtain ⟨hsupu, hsupv, hmDval, hmDsup, hmDderiv, hmBderiv, hDle, hBle, hDtouch, hBtouch⟩ :=
    gerver_tail_support_lines K B D hK hB hD
  have ht0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have ht5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have h01' : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_strictMono (by decide)
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_strictMono (by decide)
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have h34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_strictMono (by decide)
  have h45' : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_strictMono (by decide)
  have h01 : (0 : ℝ) < gerverStageTimes 1 := ht0 ▸ h01'
  have h45 : gerverStageTimes 4 < Real.pi / 2 := ht5 ▸ h45'
  -- ### The support coordinates of the cap along the path
  have hcast : ∀ x y : ℝ, x = y → ((x : ℝ) : Real.Angle) = ((y : ℝ) : Real.Angle) :=
    fun x y h ↦ by rw [h]
  have h02 : (0 : ℝ) < gerverStageTimes 2 := by linarith only [h01, h12]
  have h24 : gerverStageTimes 2 < gerverStageTimes 4 := by linarith only [h23, h34]
  have hl4I : gerverStageTimes 4 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith only [h01, h12, h23, h34], h45.le⟩
  have hmemD0 : (0 : ℝ) ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2) :=
    ⟨ht0.le, h02.le⟩
  have hmemD2 : gerverStageTimes 2 ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2) :=
    ⟨by linarith only [ht0.le, h02], le_rfl⟩
  have hmemB3 : gerverStageTimes 3 ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5) :=
    ⟨le_rfl, by linarith only [ht5.ge, h34, h45]⟩
  have hmemB5 : Real.pi / 2 ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5) :=
    ⟨by linarith only [h34, h45], ht5.ge⟩
  have hDleIoo : ∀ q ∈ (D : Set Point), ∀ s ∈ Set.Ioo (Real.pi / 2)
      (gerverStageTimes 4 + Real.pi / 2), gerverLeftTailSupport s ≤ inner ℝ q (normalVector (s :
        Real.Angle)) :=
    fun q hq s hs ↦ hDle q hq s ⟨hs.1.le, hs.2.le⟩
  have hBleIoo : ∀ q ∈ (B : Set Point), ∀ s ∈ Set.Ioo (gerverStageTimes 1) (Real.pi / 2),
      gerverRightTailSupport s ≤ inner ℝ q (normalVector (s : Real.Angle)) :=
    fun q hq s hs ↦ hBle q hq s ⟨hs.1.le, hs.2.le⟩
  have hDface : ∀ t ∈ Set.Ioc (gerverStageTimes 0) (gerverStageTimes 2),
      exposedEdge D ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) = {paperGerverContacts t 3} := by
    intro t ht
    have htI : t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2) := ⟨ht.1.le, ht.2⟩
    rw [ht0] at ht
    have h := exposedEdge_add_pi_eq_singleton_of_mem_Ioo (L := D) (m := gerverLeftTailSupport) (t
      := t + Real.pi / 2)
      ⟨by linarith only [ht.1], by linarith only [ht.2, h24]⟩ hDleIoo (hDmem t htI)
      (hDtouch t htI) (hmDderiv t)
    rwa [hcast _ _ (show t + Real.pi / 2 + Real.pi = 3 * Real.pi / 2 + t by ring)] at h
  have hBface : ∀ t ∈ Set.Ico (gerverStageTimes 3) (gerverStageTimes 5),
      exposedEdge B ((Real.pi + t : ℝ) : Real.Angle) = {paperGerverContacts t 1} := by
    intro t ht
    have htI : t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5) := ⟨ht.1, ht.2.le⟩
    rw [ht5] at ht
    have h := exposedEdge_add_pi_eq_singleton_of_mem_Ioo (L := B) (m := gerverRightTailSupport) (t
      := t)
      ⟨by linarith only [ht.1, h12, h23], ht.2⟩ hBleIoo (hBmem t htI) (hBtouch t htI)
      (hmBderiv t)
    rwa [hcast _ _ (show t + Real.pi = Real.pi + t by ring)] at h
  -- ### The two exact joins are contacts of the outer walls as well
  have hDjoin : inner ℝ (paperGerverContacts (gerverStageTimes 2) 3)
      (normalVector ((gerverStageTimes 4 + Real.pi / 2 : ℝ) : Real.Angle)) =
      gerverLeftTailSupport (gerverStageTimes 4 + Real.pi / 2) := by
    rw [hmDval, normalVector_add_pi_div_two_real, gerver_niche_piece_endpoints.2.1]
  have hBjoin : inner ℝ (paperGerverContacts (gerverStageTimes 3) 1)
      (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle)) = gerverRightTailSupport
        (gerverStageTimes 1) := by
    simp only [gerverRightTailSupport]
    rw [gerver_niche_piece_endpoints.1]
  have hDouter : paperGerverContacts (gerverStageTimes 2) 3 ∈
      exposedEdge D ((3 * Real.pi / 2 + gerverStageTimes 4 : ℝ) : Real.Angle) := by
    have h := exposedEdge_add_pi_eq_of_forall_le
      (fun q hq ↦ hDle q hq _ ⟨by linarith only [hl4I.1], le_rfl⟩) (hDmem _ hmemD2) hDjoin
    rw [hcast _ _ (show gerverStageTimes 4 + Real.pi / 2 + Real.pi =
      3 * Real.pi / 2 + gerverStageTimes 4 by ring)] at h
    rw [h]
    exact ⟨hDmem _ hmemD2, hDjoin⟩
  have hBouter : paperGerverContacts (gerverStageTimes 3) 1 ∈
      exposedEdge B ((Real.pi + gerverStageTimes 1 : ℝ) : Real.Angle) := by
    have h := exposedEdge_add_pi_eq_of_forall_le
      (fun q hq ↦ hBle q hq _ ⟨le_rfl, by linarith only [h12, h23, h34, h45]⟩)
      (hBmem _ hmemB3) hBjoin
    rw [hcast _ _ (show gerverStageTimes 1 + Real.pi = Real.pi + gerverStageTimes 1 by ring)] at h
    rw [h]
    exact ⟨hBmem _ hmemB3, hBjoin⟩
  -- ### The two arc endpoints at the outer normals
  have hDend : (edgeVertices D ((3 * Real.pi / 2 + gerverStageTimes 4 : ℝ) : Real.Angle)).2 =
      paperGerverContacts (gerverStageTimes 2) 3 := by
    have hsin : Real.sin (3 * Real.pi / 2 + gerverStageTimes 2 -
        (3 * Real.pi / 2 + gerverStageTimes 4)) ≠ 0 := by
      have : Real.sin (gerverStageTimes 4 - gerverStageTimes 2) > 0 :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith only [h24])
          (by linarith only [h45, h02, Real.pi_pos])
      rw [show 3 * Real.pi / 2 + gerverStageTimes 2 - (3 * Real.pi / 2 + gerverStageTimes 4) =
        -(gerverStageTimes 4 - gerverStageTimes 2) by ring, Real.sin_neg]
      linarith only [this]
    have hp := eq_supportingIntersection_of_mem_exposedEdge hsin
      ((hDface _ ⟨by linarith only [ht0.le, h02], le_rfl⟩) ▸ rfl) hDouter
    have hmem : supportingIntersection D ((3 * Real.pi / 2 + gerverStageTimes 2 : ℝ) : Real.Angle)
        ((3 * Real.pi / 2 + gerverStageTimes 4 : ℝ) : Real.Angle) ∈ D := by
      rw [← hp]
      exact hDmem _ hmemD2
    rw [← supportingIntersection_eq_edgeVertices_snd_of_mem D (by linarith only [h24])
      (by linarith only [h45, h02, Real.pi_pos]) hmem, ← hp]
  have hBstart : (edgeVertices B ((Real.pi + gerverStageTimes 1 : ℝ) : Real.Angle)).1 =
      paperGerverContacts (gerverStageTimes 3) 1 := by
    have hsin : Real.sin (Real.pi + gerverStageTimes 1 - (Real.pi + gerverStageTimes 3)) ≠ 0 := by
      have : Real.sin (gerverStageTimes 3 - gerverStageTimes 1) > 0 :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith only [h12, h23])
          (by linarith only [h34, h45, h01, Real.pi_pos])
      rw [show Real.pi + gerverStageTimes 1 - (Real.pi + gerverStageTimes 3) =
        -(gerverStageTimes 3 - gerverStageTimes 1) by ring, Real.sin_neg]
      linarith only [this]
    have hp := eq_supportingIntersection_of_mem_exposedEdge hsin hBouter
      ((hBface _ ⟨le_rfl, by linarith only [ht5.ge, h34, h45]⟩) ▸ rfl)
    have hmem : supportingIntersection B ((Real.pi + gerverStageTimes 1 : ℝ) : Real.Angle)
        ((Real.pi + gerverStageTimes 3 : ℝ) : Real.Angle) ∈ B := by
      rw [← hp]
      exact hBmem _ hmemB3
    rw [← supportingIntersection_eq_edgeVertices_fst_of_mem B (by linarith only [h12, h23])
      (by linarith only [h34, h45, h01, Real.pi_pos]) hmem, ← hp]
  have hDstart : (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      paperGerverContacts 0 3 := by
    have hpm : inner ℝ (paperGerverContacts 0 3)
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = gerverLeftTailSupport (Real.pi / 2) := by
      have h := hDtouch 0 hmemD0
      rwa [zero_add] at h
    have h := edgeVertices_add_pi_fst_eq_of_lt (L := D) (m := gerverLeftTailSupport)
      (a := Real.pi / 2) (b := gerverStageTimes 4 + Real.pi / 2)
      (by linarith only [hl4I.1, h01, h12, h23, h34]) hDleIoo
      (fun q hq ↦ hDle q hq _ ⟨le_rfl, by linarith only [hl4I.1]⟩) (hDmem 0 hmemD0) hpm
      (by simpa only [zero_add] using hmDderiv 0)
    rwa [hcast _ _ (show Real.pi / 2 + Real.pi = 3 * Real.pi / 2 by ring)] at h
  have hBend : (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 =
      paperGerverContacts (Real.pi / 2) 1 := by
    have h := edgeVertices_add_pi_snd_eq_of_lt (L := B) (m := gerverRightTailSupport)
      (a := gerverStageTimes 1) (b := Real.pi / 2)
      (by linarith only [h12, h23, h34, h45]) hBleIoo
      (fun q hq ↦ hBle q hq _ ⟨by linarith only [h12, h23, h34, h45], le_rfl⟩)
      (hBmem _ hmemB5) (hBtouch _ hmemB5) (hmBderiv _)
    rwa [hcast _ _ (show Real.pi / 2 + Real.pi = 3 * Real.pi / 2 by ring)] at h
  exact ⟨hDface, hBface, hDend, hBstart, hDstart, hBend, hDouter, hBouter⟩

theorem gerver_tailGeometry (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    (∀ t ∈ Set.Ioo (gerverStageTimes 0) (gerverStageTimes 2),
      edgeVertices D ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) =
        (paperGerverContacts t 3, paperGerverContacts t 3)) ∧
    (∀ t ∈ Set.Ioo (gerverStageTimes 3) (gerverStageTimes 5),
      edgeVertices B ((Real.pi + t : ℝ) : Real.Angle) =
        (paperGerverContacts t 1, paperGerverContacts t 1)) ∧
    (distinguishedCapSides K.val).2.corner = paperGerverContacts (gerverStageTimes 2) 3 ∧
    (rightLeftTailArcs B D).2.endPoint = paperGerverContacts (gerverStageTimes 2) 3 ∧
    edgeVertices D ((3 * Real.pi / 2 + gerverStageTimes 2 : ℝ) : Real.Angle) =
      (paperGerverContacts (gerverStageTimes 2) 3, paperGerverContacts (gerverStageTimes 2) 3) ∧
    ParametrizesDirectedArc (fun t ↦ paperGerverContacts t 3)
      (gerverStageTimes 0) (gerverStageTimes 2) (rightLeftTailArcs B D).2 ∧
    (distinguishedCapSides K.val).1.corner = paperGerverContacts (gerverStageTimes 3) 1 ∧
    (rightLeftTailArcs B D).1.startPoint = paperGerverContacts (gerverStageTimes 3) 1 ∧
    edgeVertices B ((Real.pi + gerverStageTimes 3 : ℝ) : Real.Angle) =
      (paperGerverContacts (gerverStageTimes 3) 1, paperGerverContacts (gerverStageTimes 3) 1) ∧
    ParametrizesDirectedArc (fun t ↦ paperGerverContacts t 1)
      (gerverStageTimes 3) (gerverStageTimes 5) (rightLeftTailArcs B D).1 ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      supportValue K.val.val ((Real.pi / 2 + t : ℝ) : Real.Angle) +
        supportValue D ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) = 1) ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      supportValue K.val.val (t : Real.Angle) +
        supportValue B ((Real.pi + t : ℝ) : Real.Angle) = 1) := by
  -- ### One cap serves every clause, and it carries the literal contact geometry
  obtain ⟨-, hGeq, -, -, hcapeq, -, -⟩ := gerver_capSupport_identification
  have hcarrier : (K.val.val : Set Point) = gerverOuterCap := by rw [hK, hGeq, hcapeq]
  obtain ⟨-, K', hK'set, hdens, hsel, -, -, hBwall, -, hDwall, -, -⟩ :=
    paperGerver_contact_geometry
  have hKeq : K' = K.val := Subtype.ext (SetLike.coe_injective (hK'set.trans hK.symm))
  subst hKeq
  obtain ⟨hstrictD, hstrictB, hDmem, hBmem⟩ :=
    gerver_tail_membership K B D hK hB hD
  obtain ⟨hsupu, hsupv, hmDval, hmDsup, hmDderiv, hmBderiv, hDle, hBle, hDtouch, hBtouch⟩ :=
    gerver_tail_support_lines K B D hK hB hD
  obtain ⟨hDface, hBface, hDend, hBstart, hDstart, hBend, hDouter, hBouter⟩ :=
    gerver_tail_contact_faces K B D hK hB hD
  have ht0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have ht5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have hr : paperGerverConstants.2.1 = gerverStageTimes 1 := rfl
  have hl : paperGerverConstants.2.2 = gerverStageTimes 4 := rfl
  have h01' : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_strictMono (by decide)
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_strictMono (by decide)
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have h34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_strictMono (by decide)
  have h45' : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_strictMono (by decide)
  have h01 : (0 : ℝ) < gerverStageTimes 1 := ht0 ▸ h01'
  have h45 : gerverStageTimes 4 < Real.pi / 2 := ht5 ▸ h45'
  -- ### The support coordinates of the cap along the path
  have hcorner : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), capInnerCorner K.val t = paperGerverPath t :=
    fun t ht ↦ (hsel ⟨t, ht⟩).2.2
  have hcast : ∀ x y : ℝ, x = y → ((x : ℝ) : Real.Angle) = ((y : ℝ) : Real.Angle) :=
    fun x y h ↦ by rw [h]
  have h02 : (0 : ℝ) < gerverStageTimes 2 := by linarith only [h01, h12]
  have h24 : gerverStageTimes 2 < gerverStageTimes 4 := by linarith only [h23, h34]
  have hl4I : gerverStageTimes 4 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith only [h01, h12, h23, h34], h45.le⟩
  have hmemD0 : (0 : ℝ) ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2) :=
    ⟨ht0.le, h02.le⟩
  have hmemD2 : gerverStageTimes 2 ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2) :=
    ⟨by linarith only [ht0.le, h02], le_rfl⟩
  have hmemB3 : gerverStageTimes 3 ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5) :=
    ⟨le_rfl, by linarith only [ht5.ge, h34, h45]⟩
  have hmemB5 : Real.pi / 2 ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5) :=
    ⟨by linarith only [h34, h45], ht5.ge⟩
  -- ### Injectivity of the two contact parametrizations
  have hinjD : Set.InjOn (fun t ↦ paperGerverContacts t 3)
      (Set.Icc (gerverStageTimes 0) (gerverStageTimes 2)) := fun x hx y hy hxy ↦
    hstrictD.injOn hx hy (by
      simpa only using congrArg (fun p : Point ↦ inner ℝ p
        (tangentVector ((gerverStageTimes 4 : ℝ) : Real.Angle))) hxy)
  have hinjB : Set.InjOn (fun t ↦ paperGerverContacts t 1)
      (Set.Icc (gerverStageTimes 3) (gerverStageTimes 5)) := fun x hx y hy hxy ↦
    hstrictB.injOn hx hy (by
      simpa only using congrArg (fun p : Point ↦ inner ℝ p
        (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle))) hxy)
  -- ### Assembling the twelve conclusions
  have hmemD2' : gerverStageTimes 2 ∈ Set.Ioc (gerverStageTimes 0) (gerverStageTimes 2) :=
    ⟨by linarith only [ht0.le, h02], le_rfl⟩
  have hmemB3' : gerverStageTimes 3 ∈ Set.Ico (gerverStageTimes 3) (gerverStageTimes 5) :=
    ⟨le_rfl, by linarith only [ht5.ge, h34, h45]⟩
  have hr1I : gerverStageTimes 1 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨h01.le, by linarith only [h12, h23, h34, h45]⟩
  have hDinner : paperGerverContacts (gerverStageTimes 2) 3 ∈
      exposedEdge D ((3 * Real.pi / 2 + gerverStageTimes 2 : ℝ) : Real.Angle) := by
    rw [hDface _ hmemD2']
    rfl
  have hBinner : paperGerverContacts (gerverStageTimes 3) 1 ∈
      exposedEdge B ((Real.pi + gerverStageTimes 3 : ℝ) : Real.Angle) := by
    rw [hBface _ hmemB3']
    rfl
  refine ⟨fun t ht ↦ edgeVertices_eq_of_exposedEdge_singleton (hDface t ⟨ht.1, ht.2.le⟩),
    fun t ht ↦ edgeVertices_eq_of_exposedEdge_singleton (hBface t ⟨ht.1.le, ht.2⟩), ?_, ?_,
    edgeVertices_eq_of_exposedEdge_singleton (hDface _ hmemD2'), ?_, ?_, ?_,
    edgeVertices_eq_of_exposedEdge_singleton (hBface _ hmemB3'), ?_, ?_, ?_⟩
  · change capInnerCorner K.val paperGerverConstants.2.2 = _
    rw [hl, hcorner _ hl4I]
    exact gerver_niche_piece_endpoints.2.1.symm
  · change (edgeVertices D ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 = _
    rw [hl]
    exact hDend
  · refine ⟨by linarith only [ht0.le, h02], (continuous_paperGerverContact 3).continuousOn,
      hinjD, ?_, ?_, ?_⟩
    · change (fun t ↦ paperGerverContacts t 3) ''
        Set.Icc (gerverStageTimes 0) (gerverStageTimes 2) =
        convexBoundaryArc D (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2)
      rw [hl, convexBoundaryArc]
      refine Set.Subset.antisymm ?_ ?_
      · rintro p ⟨t, ht, rfl⟩
        rcases eq_or_lt_of_le ht.1 with h0 | h0
        · exact Or.inl (Or.inl (by rw [Set.mem_singleton_iff, hDstart, ← h0, ht0]))
        · refine Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨3 * Real.pi / 2 + t,
            ⟨by linarith only [h0, ht0.ge], by linarith only [ht.2, h24]⟩, ?_⟩))
          rw [hDface t ⟨h0, ht.2⟩]
          rfl
      · rintro p ((hp | hp) | hp)
        · rw [Set.mem_singleton_iff, hDstart] at hp
          exact ⟨0, hmemD0, hp.symm⟩
        · obtain ⟨s, hs, hps⟩ := Set.mem_iUnion₂.1 hp
          rcases le_or_gt (s - 3 * Real.pi / 2) (gerverStageTimes 2) with h | h
          · have hmem : s - 3 * Real.pi / 2 ∈
                Set.Ioc (gerverStageTimes 0) (gerverStageTimes 2) :=
              ⟨by linarith only [hs.1, ht0.le], h⟩
            have hface := hDface (s - 3 * Real.pi / 2) hmem
            rw [hcast _ _ (show 3 * Real.pi / 2 + (s - 3 * Real.pi / 2) = s by ring)] at hface
            rw [hface, Set.mem_singleton_iff] at hps
            exact ⟨s - 3 * Real.pi / 2, ⟨hmem.1.le, hmem.2⟩, hps.symm⟩
          · have hface := exposedEdge_eq_singleton_of_mem_exposedEdge_of_mem_Ioo
              (L := D) (a := 3 * Real.pi / 2 + gerverStageTimes 2)
              (b := 3 * Real.pi / 2 + gerverStageTimes 4) (s := s)
              (by linarith only [h45, h02, Real.pi_pos])
              ⟨by linarith only [h], hs.2⟩ hDinner hDouter
            rw [hface, Set.mem_singleton_iff] at hps
            exact ⟨gerverStageTimes 2, hmemD2, hps.symm⟩
        · rw [Set.mem_singleton_iff, hDend] at hp
          exact ⟨gerverStageTimes 2, hmemD2, hp.symm⟩
    · change paperGerverContacts (gerverStageTimes 0) 3 =
        (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1
      rw [hDstart, ht0]
    · change paperGerverContacts (gerverStageTimes 2) 3 =
        (edgeVertices D ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2
      rw [hl, hDend]
  · change capInnerCorner K.val paperGerverConstants.2.1 = _
    rw [hr, hcorner _ hr1I]
    exact gerver_niche_piece_endpoints.1.symm
  · change (edgeVertices B ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 = _
    rw [hr]
    exact hBstart
  · refine ⟨by linarith only [h34, h45, ht5.ge], (continuous_paperGerverContact 1).continuousOn,
      hinjB, ?_, ?_, ?_⟩
    · change (fun t ↦ paperGerverContacts t 1) ''
        Set.Icc (gerverStageTimes 3) (gerverStageTimes 5) =
        convexBoundaryArc B (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)
      rw [hr, convexBoundaryArc]
      refine Set.Subset.antisymm ?_ ?_
      · rintro p ⟨t, ht, rfl⟩
        rcases eq_or_lt_of_le ht.2 with hT | hT
        · exact Or.inr (by rw [Set.mem_singleton_iff, hBend, hT, ht5])
        · refine Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨Real.pi + t,
            ⟨by linarith only [ht.1, h12, h23], by linarith only [hT, ht5.le]⟩, ?_⟩))
          rw [hBface t ⟨ht.1, hT⟩]
          rfl
      · rintro p ((hp | hp) | hp)
        · rw [Set.mem_singleton_iff, hBstart] at hp
          exact ⟨gerverStageTimes 3, hmemB3, hp.symm⟩
        · obtain ⟨s, hs, hps⟩ := Set.mem_iUnion₂.1 hp
          rcases lt_or_ge (s - Real.pi) (gerverStageTimes 3) with h | h
          · have hface := exposedEdge_eq_singleton_of_mem_exposedEdge_of_mem_Ioo
              (L := B) (a := Real.pi + gerverStageTimes 1)
              (b := Real.pi + gerverStageTimes 3) (s := s)
              (by linarith only [h34, h45, h01, Real.pi_pos])
              ⟨hs.1, by linarith only [h]⟩ hBouter hBinner
            rw [hface, Set.mem_singleton_iff] at hps
            exact ⟨gerverStageTimes 3, hmemB3, hps.symm⟩
          · have hmem : s - Real.pi ∈ Set.Ico (gerverStageTimes 3) (gerverStageTimes 5) :=
              ⟨h, by rw [ht5]; linarith only [hs.2]⟩
            have hface := hBface (s - Real.pi) hmem
            rw [hcast _ _ (show Real.pi + (s - Real.pi) = s by ring)] at hface
            rw [hface, Set.mem_singleton_iff] at hps
            exact ⟨s - Real.pi, ⟨hmem.1, hmem.2.le⟩, hps.symm⟩
        · rw [Set.mem_singleton_iff, hBend] at hp
          exact ⟨Real.pi / 2, hmemB5, hp.symm⟩
    · change paperGerverContacts (gerverStageTimes 3) 1 =
        (edgeVertices B ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1
      rw [hr, hBstart]
    · change paperGerverContacts (gerverStageTimes 5) 1 =
        (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
      rw [hBend, ht5]
  · intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨ht0 ▸ ht.1, by linarith only [ht.2, h23, h34, h45]⟩
    have hsup : supportValue D ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) =
        -gerverLeftTailSupport (t + Real.pi / 2) := by
      have h := supportValue_add_pi_eq_neg_of_forall_le (L := D)
        (fun q hq ↦ hDle q hq (t + Real.pi / 2)
          ⟨by linarith only [htI.1], by linarith only [ht.2, h23, h34]⟩)
        (hDmem t ht) (hDtouch t ht)
      rwa [hcast _ _ (show t + Real.pi / 2 + Real.pi = 3 * Real.pi / 2 + t by ring)] at h
    rw [hsup, hmDsup t htI, hcast _ _ (show Real.pi / 2 + t = t + Real.pi / 2 by ring)]
    ring
  · intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith only [ht.1, h01, h12, h23], ht5 ▸ ht.2⟩
    have hsup : supportValue B ((Real.pi + t : ℝ) : Real.Angle) = -gerverRightTailSupport t := by
      have h := supportValue_add_pi_eq_neg_of_forall_le (L := B)
        (fun q hq ↦ hBle q hq t ⟨by linarith only [ht.1, h12, h23], htI.2⟩)
        (hBmem t ht) (hBtouch t ht)
      rwa [hcast _ _ (show t + Real.pi = Real.pi + t by ring)] at h
    rw [hsup]
    simp only [gerverRightTailSupport]
    rw [hsupu t htI]
    ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The four contact densities of Gerver's cap

The rotating frame reads the four contact curves of Gerver's sofa as angular densities of two
surface measures: the two outer contacts `A`, `C` against the cap `K = C(G)` itself, and the two
inner contacts `B`, `D` against the two tail bodies through the opposite surface measure.

The two outer clauses are exactly the certified cap densities `gerver_surface_densities`,
rewritten with the tautological identity `⟨r • v_t, v_t⟩ = r` and translated by the quarter
turn that separates the `A` arc from the `C` arc.  The two inner clauses use that `B = A - u` and
`D = C - v` are the outer contacts translated by a frame vector, so each closed stage carries a
globally differentiable branch curve for them (`exists_branch_paperGerverContacts_one`,
`exists_branch_paperGerverContacts_three`); the tail geometry identifies those curves with the
positive vertices of the two tail bodies at the opposite normal, and
`oppositeSurfaceData_angleImage_eq_withDensity` turns each stage into a Lebesgue density.  The
stages are glued with `measure_angleImage_eq_of_union`, which puts every interior switch inside a
window that is closed on the right, so the only atom to compute is the one at the included left
endpoint `t₃` of the `B` arc.
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Push a real density measure on an angle window to angles modulo a full turn. -/
def angularDensityMeasure (f : ℝ → ℝ) (S : Set ℝ) : Measure Real.Angle :=
  Measure.map (fun t : ℝ ↦ (t : Real.Angle))
    ((volume.restrict S).withDensity (fun t ↦ ENNReal.ofReal (f t)))

/-- The measure has the specified integrable nonnegative density on the angular image of a
window. -/
def HasAngularDensity (μ : Measure Real.Angle) (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  Integrable f (volume.restrict S) ∧ (∀ᵐ t ∂volume.restrict S, 0 ≤ f t) ∧
    μ.restrict ((fun t : ℝ ↦ (t : Real.Angle)) '' S) = angularDensityMeasure f S

/-- An angular density identity on a window of at most one turn computes the measure of the
angular image of every measurable subset of the window. -/
theorem HasAngularDensity.angleImage_eq_setLIntegral {μ : Measure Real.Angle} {f : ℝ → ℝ}
    {S : Set ℝ} (h : HasAngularDensity μ f S) {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi)
    (hS : S ⊆ Set.Ioc a b) {T : Set ℝ} (hT : MeasurableSet T) (hTS : T ⊆ S) :
    μ ((fun t : ℝ ↦ (t : Real.Angle)) '' T) =
      ∫⁻ t in T, ENNReal.ofReal (f t) ∂volume := by
  have himage : MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' T) :=
    Real.Angle.measurableSet_image_of_subset_Ioc hturn hT (hTS.trans hS)
  have hrestrict : μ ((fun t : ℝ ↦ (t : Real.Angle)) '' T) =
      μ.restrict ((fun t : ℝ ↦ (t : Real.Angle)) '' S)
        ((fun t : ℝ ↦ (t : Real.Angle)) '' T) := by
    rw [Measure.restrict_apply himage, Set.inter_eq_left.2 (Set.image_mono hTS)]
  rw [hrestrict, h.2.2, angularDensityMeasure,
    Real.Angle.map_coe_withDensity_image_eq_setLIntegral hturn hS hT hTS]

private theorem gerver_angular_density_outer_first (K : SpecialCapSpace)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2)) :
    HasAngularDensity (surfaceAreaMeasure K.val.val)
      (fun t ↦ inner ℝ (deriv (fun s ↦ paperGerverContacts s 0) t)
        (tangentVector (t : Real.Angle))) (Set.Ico 0 (Real.pi / 2)) := by
  -- ### The certified cap carries the two envelope densities
  obtain ⟨K', hK'set, r, sden, hdens, ⟨M, hM⟩, hstage⟩ := gerver_surface_densities
  have hKeq : K' = K.val := Subtype.ext (SetLike.coe_injective (hK'set.trans hK.symm))
  subst hKeq
  have haeval : ∀ᵐ t ∂volume.restrict (Set.Ico (0 : ℝ) (Real.pi / 2)),
      inner ℝ (deriv (fun s ↦ paperGerverContacts s 0) t) (tangentVector (t : Real.Angle)) =
        (r t : ℝ) := by
    filter_upwards [ae_mem_openStage 0 (S := Set.Ico (0 : ℝ) (Real.pi / 2)) measurableSet_Ico
      (fun t ht ↦ ⟨ht.1, by linarith [ht.2]⟩)] with t ht
    obtain ⟨j, hj⟩ := ht
    rw [sub_zero] at hj
    rw [(hstage j t hj).1.deriv, real_inner_smul_left, inner_tangentVector_self, mul_one]
  have hrint : Integrable (fun t ↦ ((r t : ℝ)))
      (volume.restrict (Set.Ico (0 : ℝ) (Real.pi / 2))) := by
    have hfin : IsFiniteMeasure (volume.restrict (Set.Ico (0 : ℝ) (Real.pi / 2))) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ, Real.volume_Ico]
      exact ENNReal.ofReal_lt_top
    refine Integrable.mono' (integrable_const M)
      hdens.1.coe_nnreal_real.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (r t).coe_nonneg]
    exact (hM t ⟨ht.1, ht.2.le⟩).1
  refine ⟨hrint.congr (Filter.EventuallyEq.symm haeval), ?_, ?_⟩
  · filter_upwards [haeval] with t ht
    rw [ht]
    exact (r t).coe_nonneg
  · rw [hdens.2.2.1, angularDensityMeasure]
    congr 1
    refine withDensity_congr_ae ?_
    filter_upwards [haeval] with t ht
    rw [ht, ENNReal.ofReal_coe_nnreal]

private theorem gerver_angular_density_right_tail (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    HasAngularDensity (oppositeSurfaceData B).1
      (fun t ↦ inner ℝ (-(deriv (fun s ↦ paperGerverContacts s 1) t))
        (tangentVector (t : Real.Angle)))
      (Set.Ico (gerverStageTimes 3) (gerverStageTimes 5)) := by
  -- ### The strictly increasing stage times
  have h0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have h5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have h01 : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_strictMono (by decide)
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_strictMono (by decide)
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have h34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_strictMono (by decide)
  have h45 : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_strictMono (by decide)
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  -- ### The certified cap carries the two envelope densities
  obtain ⟨K', hK'set, r, sden, hdens, ⟨M, hM⟩, hstage⟩ := gerver_surface_densities
  have hKeq : K' = K.val := Subtype.ext (SetLike.coe_injective (hK'set.trans hK.symm))
  subst hKeq
  -- ### The two tails are traced by the two inner contact curves
  obtain ⟨htailD, htailB, -, -, htailD2, -, -, -, htailB3, -, -, -⟩ :=
    gerver_tailGeometry K B D hK hB hD
  obtain ⟨fB, hfBdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (-(deriv (fun s ↦ paperGerverContacts s 1) t)) (tangentVector (t : Real.Angle)) :=
    ⟨_, rfl⟩
  rw [← hfBdef]
  obtain ⟨F3, g3, hF3, hg3, hg3nn, hFeq3⟩ :=
    exists_branch_paperGerverContacts_one (i := 3) (Or.inl rfl)
  obtain ⟨F4, g4, hF4, hg4, hg4nn, hFeq4⟩ :=
    exists_branch_paperGerverContacts_one (i := 4) (Or.inr rfl)
  -- the positive vertex of `B` at normal `π + s` is the inner contact
  have hvB : ∀ s ∈ Set.Ico (gerverStageTimes 3) (gerverStageTimes 5),
      (edgeVertices B ((Real.pi + s : ℝ) : Real.Angle)).1 = paperGerverContacts s 1 := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with heq | hlt
    · rw [← heq, htailB3]
    · rw [htailB s ⟨hlt, hs.2⟩]
  -- the target density is the branch speed inside each of the two open stages
  have hfB3 : ∀ t ∈ Set.Ioo (gerverStageTimes 3) (gerverStageTimes 4), fB t = g3 t := by
    intro t ht
    simp only [hfBdef]
    rw [(hasDerivAt_of_eqOn_stage hF3 hFeq3 ht).deriv, neg_smul, neg_neg, real_inner_smul_left,
      inner_tangentVector_self, mul_one]
  have hfB4 : ∀ t ∈ Set.Ioo (gerverStageTimes 4) (gerverStageTimes 5), fB t = g4 t := by
    intro t ht
    simp only [hfBdef]
    rw [(hasDerivAt_of_eqOn_stage hF4 hFeq4 ht).deriv, neg_smul, neg_neg, real_inner_smul_left,
      inner_tangentVector_self, mul_one]
  -- the two stage windows
  have hagree3 : ∀ T, MeasurableSet T →
      T ⊆ Set.Ioc (gerverStageTimes 3) (gerverStageTimes 4) →
      (oppositeSurfaceData B).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (fB s)) T := by
    intro T hT hTsub
    refine oppositeSurfaceData_angleImage_eq_withDensity B h34 (by linarith) F3 fB g3 hF3 hg3
      hg3nn hfB3 ?_ hT hTsub
    exact fun s hs ↦ (hvB s ⟨hs.1, by linarith [hs.2]⟩).trans (hFeq3 s hs)
  have hagree4 : ∀ T, MeasurableSet T →
      T ⊆ Set.Ioo (gerverStageTimes 4) (gerverStageTimes 5) →
      (oppositeSurfaceData B).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (fB s)) T := by
    intro T hT hTsub
    refine oppositeSurfaceData_angleImage_eq_withDensity_of_openRight B h45 (by linarith) F4 fB
      g4 hF4 hg4 (fun s hs ↦ hg4nn s ⟨hs.1, hs.2.le⟩) hfB4 ?_ hT hTsub
    exact fun s hs ↦ (hvB s ⟨by linarith [hs.1], hs.2⟩).trans (hFeq4 s ⟨hs.1, hs.2.le⟩)
  -- the included left endpoint carries no surface atom
  have hatom : (oppositeSurfaceData B).1
      ((fun s : ℝ ↦ (s : Real.Angle)) '' {gerverStageTimes 3}) = 0 := by
    rw [oppositeSurfaceData_angleImage B
      (by rw [Set.image_singleton]; exact measurableSet_singleton _),
      Set.image_singleton, Set.image_singleton,
      (surfaceAreaMeasure_atom_length B
        ((gerverStageTimes 3 + Real.pi : ℝ) : Real.Angle)).2.1,
      show ((gerverStageTimes 3 + Real.pi : ℝ) : Real.Angle) =
        ((Real.pi + gerverStageTimes 3 : ℝ) : Real.Angle) from by rw [add_comm], htailB3]
    simp
  have hagreeAtom : ∀ T, MeasurableSet T → T ⊆ {gerverStageTimes 3} →
      (oppositeSurfaceData B).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (fB s)) T := by
    have hatomν : volume.withDensity (fun s ↦ ENNReal.ofReal (fB s))
        {gerverStageTimes 3} = 0 := by
      rw [withDensity_apply _ (measurableSet_singleton _)]
      exact setLIntegral_measure_zero _ _ (by simp)
    intro T _ hTsub
    rw [measure_mono_null (Set.image_mono hTsub) hatom, measure_mono_null hTsub hatomν]
  -- gluing the closed stage and then the final open stage
  have hstep1 : ∀ T, MeasurableSet T →
      T ⊆ Set.Icc (gerverStageTimes 3) (gerverStageTimes 4) →
      (oppositeSurfaceData B).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (fB s)) T := by
    intro T hT hTsub
    refine measure_angleImage_eq_of_union (c := gerverStageTimes 3 - 1)
      (d := gerverStageTimes 5) (by linarith) (I := {gerverStageTimes 3})
      (J := Set.Ioc (gerverStageTimes 3) (gerverStageTimes 4)) ?_ ?_
      (measurableSet_singleton _) measurableSet_Ioc ?_ hagreeAtom hagree3 T hT ?_
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨by linarith, by linarith⟩
    · exact fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · rw [Set.disjoint_singleton_left]
      simp
    · intro x hx
      rcases eq_or_lt_of_le (hTsub hx).1 with heq | hlt
      · exact Or.inl heq.symm
      · exact Or.inr ⟨hlt, (hTsub hx).2⟩
  have hstep2 : ∀ T, MeasurableSet T →
      T ⊆ Set.Ico (gerverStageTimes 3) (gerverStageTimes 5) →
      (oppositeSurfaceData B).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (fB s)) T := by
    intro T hT hTsub
    refine measure_angleImage_eq_of_union (c := gerverStageTimes 3 - 1)
      (d := gerverStageTimes 5) (by linarith)
      (I := Set.Icc (gerverStageTimes 3) (gerverStageTimes 4))
      (J := Set.Ioo (gerverStageTimes 4) (gerverStageTimes 5)) ?_ ?_
      measurableSet_Icc measurableSet_Ioo ?_ hstep1 hagree4 T hT ?_
    · exact fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · rw [Set.disjoint_left]
      exact fun x hx hx' ↦ absurd hx'.1 (not_lt.2 hx.2)
    · intro x hx
      rcases le_or_gt x (gerverStageTimes 4) with h | h
      · exact Or.inl ⟨(hTsub hx).1, h⟩
      · exact Or.inr ⟨h, (hTsub hx).2⟩
  -- almost every parameter of the window lies in one of the two open stages
  have hae : ∀ᵐ t ∂volume.restrict (Set.Ico (gerverStageTimes 3) (gerverStageTimes 5)),
      t ∈ Set.Ioo (gerverStageTimes 3) (gerverStageTimes 4) ∪
        Set.Ioo (gerverStageTimes 4) (gerverStageTimes 5) := by
    refine ae_restrict_mem_of_countable_diff measurableSet_Ico
      ((Set.countable_singleton (gerverStageTimes 4)).insert (gerverStageTimes 3)) ?_
    rintro x ⟨hx, hx'⟩
    rcases eq_or_lt_of_le hx.1 with heq | hlt
    · exact Or.inl heq.symm
    · rcases lt_trichotomy x (gerverStageTimes 4) with h | h | h
      · exact absurd (Or.inl ⟨hlt, h⟩) hx'
      · exact Or.inr (Set.mem_singleton_iff.2 h)
      · exact absurd (Or.inr ⟨h, hx.2⟩) hx'
  have hsplit : Set.Ico (gerverStageTimes 3) (gerverStageTimes 5) =
      Set.Icc (gerverStageTimes 3) (gerverStageTimes 4) ∪
        Set.Ioo (gerverStageTimes 4) (gerverStageTimes 5) :=
    (Set.Icc_union_Ioo_eq_Ico h34.le h45).symm
  refine ⟨?_, ?_, ?_⟩
  · have h1 : IntegrableOn fB (Set.Icc (gerverStageTimes 3) (gerverStageTimes 4)) volume := by
      refine (ContinuousOn.integrableOn_compact isCompact_Icc hg3.continuousOn).congr ?_
      have hae3 : ∀ᵐ t ∂volume.restrict (Set.Icc (gerverStageTimes 3) (gerverStageTimes 4)),
          t ∈ Set.Ioo (gerverStageTimes 3) (gerverStageTimes 4) := by
        refine ae_restrict_mem_of_countable_diff measurableSet_Icc
          ((Set.countable_singleton (gerverStageTimes 4)).insert (gerverStageTimes 3)) ?_
        rintro x ⟨hx, hx'⟩
        rcases eq_or_lt_of_le hx.1 with heq | hlt
        · exact Or.inl heq.symm
        · rcases eq_or_lt_of_le hx.2 with heq2 | hlt2
          · exact Or.inr (Set.mem_singleton_iff.2 heq2)
          · exact absurd ⟨hlt, hlt2⟩ hx'
      filter_upwards [hae3] with t ht using (hfB3 t ht).symm
    have h2 : IntegrableOn fB (Set.Ioo (gerverStageTimes 4) (gerverStageTimes 5)) volume := by
      refine (((ContinuousOn.integrableOn_compact (isCompact_Icc
        (a := gerverStageTimes 4) (b := gerverStageTimes 5))
          hg4.continuousOn)).mono_set Set.Ioo_subset_Icc_self).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using (hfB4 t ht).symm
    rw [show Integrable fB (volume.restrict (Set.Ico (gerverStageTimes 3)
      (gerverStageTimes 5))) = IntegrableOn fB (Set.Ico (gerverStageTimes 3)
        (gerverStageTimes 5)) volume from rfl, hsplit]
    exact h1.union h2
  · filter_upwards [hae] with t ht
    rcases ht with ht | ht
    · rw [hfB3 t ht]
      exact hg3nn t ⟨ht.1, ht.2.le⟩
    · rw [hfB4 t ht]
      exact hg4nn t ⟨ht.1, ht.2.le⟩
  · rw [angularDensityMeasure]
    exact measure_restrict_eq_map_withDensity measurableSet_Ico hstep2

private theorem gerver_angular_density_outer_second (K : SpecialCapSpace)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2)) :
    HasAngularDensity (surfaceAreaMeasure K.val.val)
      (fun t ↦ inner ℝ (-(deriv (fun s ↦ paperGerverContacts s 2) (t - Real.pi / 2)))
        (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)))
      (Set.Ioc (Real.pi / 2) Real.pi) := by
  -- ### The certified cap carries the two envelope densities
  obtain ⟨K', hK'set, r, sden, hdens, ⟨M, hM⟩, hstage⟩ := gerver_surface_densities
  have hKeq : K' = K.val := Subtype.ext (SetLike.coe_injective (hK'set.trans hK.symm))
  subst hKeq
  have haeval : ∀ᵐ u ∂volume.restrict (Set.Ioc (Real.pi / 2) Real.pi),
      inner ℝ (-(deriv (fun s ↦ paperGerverContacts s 2) (u - Real.pi / 2)))
          (normalVector ((u - Real.pi / 2 : ℝ) : Real.Angle)) =
        (sden (u - Real.pi / 2) : ℝ) := by
    filter_upwards [ae_mem_openStage (Real.pi / 2) (S := Set.Ioc (Real.pi / 2) Real.pi)
      measurableSet_Ioc (fun u hu ↦ ⟨hu.1.le, by linarith [hu.2]⟩)] with u hu
    obtain ⟨j, hj⟩ := hu
    rw [(hstage j _ hj).2.deriv, neg_smul, neg_neg, real_inner_smul_left,
      inner_normalVector_self, mul_one]
  have hsint : Integrable (fun u ↦ ((sden (u - Real.pi / 2) : ℝ)))
      (volume.restrict (Set.Ioc (Real.pi / 2) Real.pi)) := by
    have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (Real.pi / 2) Real.pi)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    refine Integrable.mono' (integrable_const M)
      ((hdens.2.1.coe_nnreal_real.comp (measurable_id.sub_const _)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sden _).coe_nonneg]
    exact (hM (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
  refine ⟨hsint.congr (Filter.EventuallyEq.symm haeval), ?_, ?_⟩
  · filter_upwards [haeval] with u hu
    rw [hu]
    exact (sden _).coe_nonneg
  · have himg : (fun t : ℝ ↦ t + Real.pi / 2) '' Set.Ioc 0 (Real.pi / 2) =
        Set.Ioc (Real.pi / 2) Real.pi := by
      ext u
      simp only [Set.mem_image, Set.mem_Ioc]
      constructor
      · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨u - Real.pi / 2, ⟨by linarith, by linarith⟩, by ring⟩
    have hcomp : (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
        (fun u : ℝ ↦ (u : Real.Angle)) ∘ (fun t : ℝ ↦ t + Real.pi / 2) := rfl
    rw [hdens.2.2.2, angularDensityMeasure, hcomp,
      ← Measure.map_map (g := fun u : ℝ ↦ (u : Real.Angle))
        (f := fun t : ℝ ↦ t + Real.pi / 2) Real.Angle.continuous_coe.measurable (by fun_prop),
      map_add_right_restrict_withDensity (Real.pi / 2), himg]
    congr 1
    refine withDensity_congr_ae ?_
    filter_upwards [haeval] with u hu
    rw [hu, ENNReal.ofReal_coe_nnreal]

private theorem gerver_angular_density_left_tail (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    HasAngularDensity (oppositeSurfaceData D).1
      (fun t ↦ inner ℝ (deriv (fun s ↦ paperGerverContacts s 3) (t - Real.pi / 2))
        (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)))
      (Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
        (Real.pi / 2 + gerverStageTimes 2)) := by
  -- ### The strictly increasing stage times
  have h0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have h5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have h01 : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_strictMono (by decide)
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_strictMono (by decide)
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have h34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_strictMono (by decide)
  have h45 : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_strictMono (by decide)
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  -- ### The certified cap carries the two envelope densities
  obtain ⟨K', hK'set, r, sden, hdens, ⟨M, hM⟩, hstage⟩ := gerver_surface_densities
  have hKeq : K' = K.val := Subtype.ext (SetLike.coe_injective (hK'set.trans hK.symm))
  subst hKeq
  -- ### The two tails are traced by the two inner contact curves
  obtain ⟨htailD, htailB, -, -, htailD2, -, -, -, htailB3, -, -, -⟩ :=
    gerver_tailGeometry K B D hK hB hD
  obtain ⟨fD, hfDdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (deriv (fun s ↦ paperGerverContacts s 3) (t - Real.pi / 2))
      (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)) := ⟨_, rfl⟩
  rw [← hfDdef]
  obtain ⟨F0, g0, hF0, hg0, hg0nn, hFeq0⟩ :=
    exists_branch_paperGerverContacts_three (i := 0) (Or.inl rfl)
  obtain ⟨F1, g1, hF1, hg1, hg1nn, hFeq1⟩ :=
    exists_branch_paperGerverContacts_three (i := 1) (Or.inr rfl)
  -- the stage data with the stage times spelled out, so that `linarith` sees them
  have hg0nn' : ∀ t ∈ Set.Ioc (gerverStageTimes 0) (gerverStageTimes 1), 0 ≤ g0 t := hg0nn
  have hFeq0' : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 1),
      paperGerverContacts t 3 = F0 t := hFeq0
  have hg1nn' : ∀ t ∈ Set.Ioc (gerverStageTimes 1) (gerverStageTimes 2), 0 ≤ g1 t := hg1nn
  have hFeq1' : ∀ t ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 2),
      paperGerverContacts t 3 = F1 t := hFeq1
  -- reparametrising the quarter-turn shift turns the normal speed into a tangent speed
  have hshift : ∀ (F : ℝ → Point) (g : ℝ → ℝ),
      (∀ s, HasDerivAt F (g s • normalVector (s : Real.Angle)) s) →
      ∀ u : ℝ, HasDerivAt (fun v : ℝ ↦ F (v - Real.pi / 2))
        (-(g (u - Real.pi / 2)) • tangentVector (u : Real.Angle)) u := by
    intro F g hF u
    have h := (hF (u - Real.pi / 2)).scomp u ((hasDerivAt_id u).sub_const (Real.pi / 2))
    have hv : tangentVector (u : Real.Angle) =
        -normalVector ((u - Real.pi / 2 : ℝ) : Real.Angle) := by
      have h2 := tangentVector_add_pi_div_two (u - Real.pi / 2)
      rw [show u - Real.pi / 2 + Real.pi / 2 = u from by ring] at h2
      exact h2
    rw [hv]
    refine h.congr_deriv ?_
    module
  -- the positive vertex of `D` at normal `π + u` is the inner contact
  have hvD : ∀ u ∈ Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
      (Real.pi / 2 + gerverStageTimes 2),
      (edgeVertices D ((Real.pi + u : ℝ) : Real.Angle)).1 =
        paperGerverContacts (u - Real.pi / 2) 3 := by
    intro u hu
    rw [show ((Real.pi + u : ℝ) : Real.Angle) =
      ((3 * Real.pi / 2 + (u - Real.pi / 2) : ℝ) : Real.Angle) from by congr 1; ring]
    rcases eq_or_lt_of_le hu.2 with heq | hlt
    · rw [show u - Real.pi / 2 = gerverStageTimes 2 from by linarith, htailD2]
    · rw [htailD (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith⟩]
  -- the target density is the shifted branch speed inside each of the two open stages
  have hfD0 : ∀ u ∈ Set.Ioo (Real.pi / 2 + gerverStageTimes 0)
      (Real.pi / 2 + gerverStageTimes 1), fD u = g0 (u - Real.pi / 2) := by
    intro u hu
    simp only [hfDdef]
    rw [(hasDerivAt_of_eqOn_stage hF0 hFeq0 (show u - Real.pi / 2 ∈
      Set.Ioo (gerverStageTimes 0) (gerverStageTimes 1) from
        ⟨by linarith [hu.1], by linarith [hu.2]⟩)).deriv, real_inner_smul_left,
      inner_normalVector_self, mul_one]
  have hfD1 : ∀ u ∈ Set.Ioo (Real.pi / 2 + gerverStageTimes 1)
      (Real.pi / 2 + gerverStageTimes 2), fD u = g1 (u - Real.pi / 2) := by
    intro u hu
    simp only [hfDdef]
    rw [(hasDerivAt_of_eqOn_stage hF1 hFeq1 (show u - Real.pi / 2 ∈
      Set.Ioo (gerverStageTimes 1) (gerverStageTimes 2) from
        ⟨by linarith [hu.1], by linarith [hu.2]⟩)).deriv, real_inner_smul_left,
      inner_normalVector_self, mul_one]
  -- the two stage windows
  have hagree0 : ∀ T, MeasurableSet T →
      T ⊆ Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 1) →
      (oppositeSurfaceData D).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (fD s)) T := by
    intro T hT hTsub
    refine oppositeSurfaceData_angleImage_eq_withDensity_of_openLeft D (by linarith)
      (by linarith) (fun v ↦ F0 (v - Real.pi / 2)) fD (fun u ↦ g0 (u - Real.pi / 2))
      (hshift F0 g0 hF0) (hg0.comp (continuous_id.sub continuous_const))
      (fun s hs ↦ hg0nn' _ ⟨by linarith [hs.1], by linarith [hs.2]⟩) hfD0 ?_ hT hTsub
    exact fun s hs ↦ (hvD s ⟨hs.1, by linarith [hs.2]⟩).trans
      (hFeq0' _ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hagree1 : ∀ T, MeasurableSet T →
      T ⊆ Set.Ioc (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2) →
      (oppositeSurfaceData D).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (fD s)) T := by
    intro T hT hTsub
    refine oppositeSurfaceData_angleImage_eq_withDensity D (by linarith) (by linarith)
      (fun v ↦ F1 (v - Real.pi / 2)) fD (fun u ↦ g1 (u - Real.pi / 2)) (hshift F1 g1 hF1)
      (hg1.comp (continuous_id.sub continuous_const))
      (fun s hs ↦ hg1nn' _ ⟨by linarith [hs.1], by linarith [hs.2]⟩) hfD1 ?_ hT hTsub
    exact fun s hs ↦ (hvD s ⟨by linarith [hs.1], by linarith [hs.2]⟩).trans
      (hFeq1' _ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hstep : ∀ T, MeasurableSet T →
      T ⊆ Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 2) →
      (oppositeSurfaceData D).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (fD s)) T := by
    intro T hT hTsub
    refine measure_angleImage_eq_of_union (c := Real.pi / 2 + gerverStageTimes 0)
      (d := Real.pi / 2 + gerverStageTimes 2) (by linarith)
      (I := Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 1))
      (J := Set.Ioc (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2)) ?_ ?_
      measurableSet_Ioc measurableSet_Ioc ?_ hagree0 hagree1 T hT ?_
    · exact fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
    · exact fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
    · rw [Set.disjoint_left]
      exact fun x hx hx' ↦ absurd hx'.1 (not_lt.2 hx.2)
    · intro x hx
      rcases le_or_gt x (Real.pi / 2 + gerverStageTimes 1) with h | h
      · exact Or.inl ⟨(hTsub hx).1, h⟩
      · exact Or.inr ⟨h, (hTsub hx).2⟩
  have hsplit : Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 2) =
      Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 1) ∪
        Set.Ioc (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2) :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
  have hae : ∀ᵐ u ∂volume.restrict (Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
      (Real.pi / 2 + gerverStageTimes 2)),
      u ∈ Set.Ioo (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 1) ∪
        Set.Ioo (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2) := by
    refine ae_restrict_mem_of_countable_diff measurableSet_Ioc
      ((Set.countable_singleton (Real.pi / 2 + gerverStageTimes 2)).insert
        (Real.pi / 2 + gerverStageTimes 1)) ?_
    rintro x ⟨hx, hx'⟩
    rcases lt_trichotomy x (Real.pi / 2 + gerverStageTimes 1) with h | h | h
    · exact absurd (Or.inl ⟨hx.1, h⟩) hx'
    · exact Or.inl h
    · rcases eq_or_lt_of_le hx.2 with heq | hlt
      · exact Or.inr (Set.mem_singleton_iff.2 heq)
      · exact absurd (Or.inr ⟨h, hlt⟩) hx'
  refine ⟨?_, ?_, ?_⟩
  · have hae01 : ∀ a b : ℝ, ∀ᵐ u ∂volume.restrict (Set.Ioc a b),
        u ∈ Set.Ioo a b := by
      intro a b
      refine ae_restrict_mem_of_countable_diff measurableSet_Ioc
        (Set.countable_singleton b) ?_
      rintro x ⟨hx, hx'⟩
      exact le_antisymm hx.2 (not_lt.1 fun h ↦ hx' ⟨hx.1, h⟩)
    have hint0 : IntegrableOn fD (Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
        (Real.pi / 2 + gerverStageTimes 1)) volume := by
      have hc0 : Continuous fun u : ℝ ↦ g0 (u - Real.pi / 2) :=
        hg0.comp (continuous_id.sub continuous_const)
      refine (((ContinuousOn.integrableOn_compact (isCompact_Icc
        (a := Real.pi / 2 + gerverStageTimes 0) (b := Real.pi / 2 + gerverStageTimes 1))
          hc0.continuousOn)).mono_set Set.Ioc_subset_Icc_self).congr ?_
      filter_upwards [hae01 _ _] with u hu using (hfD0 u hu).symm
    have hint1 : IntegrableOn fD (Set.Ioc (Real.pi / 2 + gerverStageTimes 1)
        (Real.pi / 2 + gerverStageTimes 2)) volume := by
      have hc1 : Continuous fun u : ℝ ↦ g1 (u - Real.pi / 2) :=
        hg1.comp (continuous_id.sub continuous_const)
      refine (((ContinuousOn.integrableOn_compact (isCompact_Icc
        (a := Real.pi / 2 + gerverStageTimes 1) (b := Real.pi / 2 + gerverStageTimes 2))
          hc1.continuousOn)).mono_set Set.Ioc_subset_Icc_self).congr ?_
      filter_upwards [hae01 _ _] with u hu using (hfD1 u hu).symm
    rw [show Integrable fD (volume.restrict (Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
      (Real.pi / 2 + gerverStageTimes 2))) = IntegrableOn fD
        (Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
          (Real.pi / 2 + gerverStageTimes 2)) volume from rfl, hsplit]
    exact hint0.union hint1
  · filter_upwards [hae] with u hu
    rcases hu with hu | hu
    · rw [hfD0 u hu]
      exact hg0nn' _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · rw [hfD1 u hu]
      exact hg1nn' _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · rw [angularDensityMeasure]
    exact measure_restrict_eq_map_withDensity measurableSet_Ioc hstep

theorem gerver_measureTranslation (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    HasAngularDensity (surfaceAreaMeasure K.val.val)
      (fun t ↦ inner ℝ (deriv (fun s ↦ paperGerverContacts s 0) t)
        (tangentVector (t : Real.Angle))) (Set.Ico 0 (Real.pi / 2)) ∧
    HasAngularDensity (oppositeSurfaceData B).1
      (fun t ↦ inner ℝ (-(deriv (fun s ↦ paperGerverContacts s 1) t))
        (tangentVector (t : Real.Angle)))
      (Set.Ico (gerverStageTimes 3) (gerverStageTimes 5)) ∧
    HasAngularDensity (surfaceAreaMeasure K.val.val)
      (fun t ↦ inner ℝ (-(deriv (fun s ↦ paperGerverContacts s 2) (t - Real.pi / 2)))
        (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)))
      (Set.Ioc (Real.pi / 2) Real.pi) ∧
    HasAngularDensity (oppositeSurfaceData D).1
      (fun t ↦ inner ℝ (deriv (fun s ↦ paperGerverContacts s 3) (t - Real.pi / 2))
        (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)))
      (Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
        (Real.pi / 2 + gerverStageTimes 2)) := by
  exact ⟨gerver_angular_density_outer_first K hK,
    gerver_angular_density_right_tail K B D hK hB hD,
    gerver_angular_density_outer_second K hK,
    gerver_angular_density_left_tail K B D hK hB hD⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The eight phase identities of Gerver's cap

The ten Gerver phase intervals cut the angular window `[0, π]` at the five stage times and at
their reflections.  On each of them the surface-area measure of the cap `K = C(G)` of Gerver's
sofa is one of: zero, the inner-corner measure `ι_K`, the opposite surface measure of one of the
two tail bodies, or a sum of the last two (`gerver_phaseMeasures`).

Every clause is proved set-wise.  The translated-measure proposition `gerver_measureTranslation`
presents the surface measure of the cap and the two opposite tail measures as angular densities
on the two half-windows, so each of them gives the angular image of a measurable subset of a
phase interval the Lebesgue integral of the corresponding contact derivative
(`HasAngularDensity.angleImage_eq_setLIntegral`), and the corner measure does the same with its
own density (`capCornerAngleMeasure_angleImage_eq_setLIntegral`).  The five stagewise contact
equations `gerver_stageODEs` identify those densities on the interior of each stage, which is
almost all of it, and `Real.Angle.measure_restrict_image_congr_of_ae_eq` turns an
almost-everywhere identity of densities into an equality of the restricted measures.  No atom
computation at the included stage endpoints is needed: a single parameter is Lebesgue-null and
the four measures are only ever evaluated through their densities.
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The angular image of one of the ten phase intervals. -/
def gerverPhaseAngles (j : Fin 10) : Set Real.Angle :=
  (fun t : ℝ ↦ (t : Real.Angle)) '' gerverPhaseIntervals j

/-- The phase-by-phase surface-measure identities relating the cap, corner and two tail
bodies. -/
def GerverPhaseMeasureIdentities (K : SpecialCapSpace) (B D : ConvexBody Point) : Prop :=
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 0) = 0 ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 1 ∪ gerverPhaseAngles 2) =
    (capCornerAngleMeasure K).restrict (gerverPhaseAngles 1 ∪ gerverPhaseAngles 2) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 3) =
    ((oppositeSurfaceData B).1 + capCornerAngleMeasure K).restrict (gerverPhaseAngles 3) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 4) =
    (oppositeSurfaceData B).1.restrict (gerverPhaseAngles 4) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 5) =
    (oppositeSurfaceData D).1.restrict (gerverPhaseAngles 5) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 6) =
    ((oppositeSurfaceData D).1 + capCornerAngleMeasure K).restrict (gerverPhaseAngles 6) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 7 ∪ gerverPhaseAngles 8) =
    (capCornerAngleMeasure K).restrict (gerverPhaseAngles 7 ∪ gerverPhaseAngles 8) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 9) = 0

/-! ### The corner density of the cap of Gerver's sofa

On each of the two open quarter turns the inner corner of the cap is the direct Gerver path
(`derivWithin_capInnerCorner_eq_deriv_paperGerverPath`), so the two branches of
`capCornerDensity` are the two velocity components `β` and `-α` of that path. -/

/-- On the first open quarter turn the corner density of the cap of Gerver's sofa is the
tangential velocity component of the direct Gerver path. -/
theorem capCornerDensity_eq_velocity_tangential (K : SpecialCapSpace)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2)) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    capCornerDensity K s = (paperGerverVelocityComponents s).2 := by
  simp only [capCornerDensity]
  split_ifs with h1 h2
  · simp only [capVelocityCoefficients, paperGerverVelocityComponents,
      derivWithin_capInnerCorner_eq_deriv_paperGerverPath K.val hK hs]
  · exact absurd ⟨hs.1, hs.2.le⟩ h1
  · exact absurd ⟨hs.1, hs.2.le⟩ h1

/-- On the second open quarter turn the corner density of the cap of Gerver's sofa is minus the
normal velocity component of the direct Gerver path, at the parameter shifted by a quarter
turn. -/
theorem capCornerDensity_eq_neg_velocity_normal (K : SpecialCapSpace)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2)) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.pi / 2) Real.pi) :
    capCornerDensity K s = -(paperGerverVelocityComponents (s - Real.pi / 2)).1 := by
  have hs' : s - Real.pi / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  simp only [capCornerDensity]
  split_ifs with h1 h2
  · exact absurd h1.2 (not_le.2 hs.1)
  · simp only [capVelocityCoefficients, paperGerverVelocityComponents,
      derivWithin_capInnerCorner_eq_deriv_paperGerverPath K.val hK hs']
  · exact absurd ⟨hs.1, hs.2.le⟩ h2

private theorem gerver_contact_density_stage_identities
    (fA fB fC fD : ℝ → ℝ)
    (hfAdef : fA = fun t ↦ inner ℝ
      (deriv (fun s ↦ paperGerverContacts s 0) t) (tangentVector (t : Real.Angle)))
    (hfBdef : fB = fun t ↦ inner ℝ
      (-(deriv (fun s ↦ paperGerverContacts s 1) t))
      (tangentVector (t : Real.Angle)))
    (hfCdef : fC = fun t ↦ inner ℝ
      (-(deriv (fun s ↦ paperGerverContacts s 2) (t - Real.pi / 2)))
      (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)))
    (hfDdef : fD = fun t ↦ inner ℝ
      (deriv (fun s ↦ paperGerverContacts s 3) (t - Real.pi / 2))
      (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)))
    : (∀ t ∈ Set.Ioo (0 : ℝ) GerversSofa.φ,
     fA t = 0 ∧ fC (t + Real.pi / 2) = fD (t + Real.pi / 2)) ∧
    (∀ t ∈ Set.Ioo GerversSofa.φ GerversSofa.θ,
     fA t = (paperGerverVelocityComponents t).2 ∧
     fC (t + Real.pi / 2) =
       fD (t + Real.pi / 2) - (paperGerverVelocityComponents t).1) ∧
    (∀ t ∈ Set.Ioo GerversSofa.θ (Real.pi / 2 - GerversSofa.θ),
     fA t = (paperGerverVelocityComponents t).2 ∧
     fC (t + Real.pi / 2) = -(paperGerverVelocityComponents t).1) ∧
    (∀ t ∈ Set.Ioo (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ),
     fA t = fB t + (paperGerverVelocityComponents t).2 ∧
     fC (t + Real.pi / 2) = -(paperGerverVelocityComponents t).1) ∧
    (∀ t ∈ Set.Ioo (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2),
     fA t = fB t ∧ fC (t + Real.pi / 2) = 0) := by
  -- ### The five closed stage intervals
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 GerversSofa.φ := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI1 : gerverStageIntervals 1 = Set.Icc GerversSofa.φ GerversSofa.θ := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI2 : gerverStageIntervals 2 =
      Set.Icc GerversSofa.θ (Real.pi / 2 - GerversSofa.θ) := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI4 : gerverStageIntervals 4 =
      Set.Icc (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes]
  -- ### Inside an open stage the stagewise derivatives are the global ones
  have hconv : ∀ (i : Fin 5) (a b t : ℝ), gerverStageIntervals i = Set.Icc a b →
      a < t → t < b →
      gerverStageContactDerivatives i t 0 = fA t ∧
      gerverStageContactDerivatives i t 1 = -fB t ∧
      gerverStageContactDerivatives i t 2 = fC (t + Real.pi / 2) ∧
      gerverStageContactDerivatives i t 3 = fD (t + Real.pi / 2) := by
    intro i a b t hI ha hb
    have hn : gerverStageIntervals i ∈ nhds t := by rw [hI]; exact Icc_mem_nhds ha hb
    have e : ∀ k : Fin 4,
        derivWithin (fun s ↦ paperGerverContacts s k) (gerverStageIntervals i) t =
          deriv (fun s ↦ paperGerverContacts s k) t := fun _ ↦ derivWithin_of_mem_nhds hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · change inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 0) (gerverStageIntervals i) t)
        (tangentVector (t : Real.Angle)) = fA t
      rw [e 0, hfAdef]
    · change inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 1) (gerverStageIntervals i) t)
        (tangentVector (t : Real.Angle)) = -fB t
      rw [e 1, hfBdef]
      simp [inner_neg_left]
    · change inner ℝ (-derivWithin (fun s ↦ paperGerverContacts s 2) (gerverStageIntervals i) t)
        (normalVector (t : Real.Angle)) = fC (t + Real.pi / 2)
      rw [e 2, hfCdef]
      simp
    · change inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 3) (gerverStageIntervals i) t)
        (normalVector (t : Real.Angle)) = fD (t + Real.pi / 2)
      rw [e 3, hfDdef]
      simp
  -- ### The five stage coefficient identities, at interior parameters
  have hode : ∀ (i : Fin 5) (a b t : ℝ), gerverStageIntervals i = Set.Icc a b →
      a < t → t < b →
      (gerverStageContactDerivatives i t 0, gerverStageContactDerivatives i t 2) =
        ![(0, gerverStageContactDerivatives i t 3),
          ((paperGerverVelocityComponents t).2,
            gerverStageContactDerivatives i t 3 - (paperGerverVelocityComponents t).1),
          ((paperGerverVelocityComponents t).2, -(paperGerverVelocityComponents t).1),
          (-gerverStageContactDerivatives i t 1 + (paperGerverVelocityComponents t).2,
            -(paperGerverVelocityComponents t).1),
          (-gerverStageContactDerivatives i t 1, 0)] i :=
    fun i a b t hI ha hb ↦ gerver_stageODEs i t (by rw [hI]; exact ⟨ha.le, hb.le⟩)
  have hs0 : ∀ t ∈ Set.Ioo (0 : ℝ) GerversSofa.φ,
      fA t = 0 ∧ fC (t + Real.pi / 2) = fD (t + Real.pi / 2) := by
    intro t ht
    obtain ⟨e0, -, e2, e3⟩ := hconv 0 _ _ t hI0 ht.1 ht.2
    have h := hode 0 _ _ t hI0 ht.1 ht.2
    simp only [Matrix.cons_val, Prod.mk.injEq] at h
    exact ⟨e0.symm.trans h.1, e2.symm.trans (h.2.trans e3)⟩
  have hs1 : ∀ t ∈ Set.Ioo GerversSofa.φ GerversSofa.θ,
      fA t = (paperGerverVelocityComponents t).2 ∧
      fC (t + Real.pi / 2) =
        fD (t + Real.pi / 2) - (paperGerverVelocityComponents t).1 := by
    intro t ht
    obtain ⟨e0, -, e2, e3⟩ := hconv 1 _ _ t hI1 ht.1 ht.2
    have h := hode 1 _ _ t hI1 ht.1 ht.2
    simp only [Matrix.cons_val, Prod.mk.injEq] at h
    exact ⟨e0.symm.trans h.1, e2.symm.trans (h.2.trans (by rw [e3]))⟩
  have hs2 : ∀ t ∈ Set.Ioo GerversSofa.θ (Real.pi / 2 - GerversSofa.θ),
      fA t = (paperGerverVelocityComponents t).2 ∧
      fC (t + Real.pi / 2) = -(paperGerverVelocityComponents t).1 := by
    intro t ht
    obtain ⟨e0, -, e2, -⟩ := hconv 2 _ _ t hI2 ht.1 ht.2
    have h := hode 2 _ _ t hI2 ht.1 ht.2
    simp only [Matrix.cons_val, Prod.mk.injEq] at h
    exact ⟨e0.symm.trans h.1, e2.symm.trans h.2⟩
  have hs3 : ∀ t ∈ Set.Ioo (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ),
      fA t = fB t + (paperGerverVelocityComponents t).2 ∧
      fC (t + Real.pi / 2) = -(paperGerverVelocityComponents t).1 := by
    intro t ht
    obtain ⟨e0, e1, e2, -⟩ := hconv 3 _ _ t hI3 ht.1 ht.2
    have h := hode 3 _ _ t hI3 ht.1 ht.2
    simp only [Matrix.cons_val, Prod.mk.injEq] at h
    refine ⟨e0.symm.trans (h.1.trans ?_), e2.symm.trans h.2⟩
    rw [e1, neg_neg]
  have hs4 : ∀ t ∈ Set.Ioo (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2),
      fA t = fB t ∧ fC (t + Real.pi / 2) = 0 := by
    intro t ht
    obtain ⟨e0, e1, e2, -⟩ := hconv 4 _ _ t hI4 ht.1 ht.2
    have h := hode 4 _ _ t hI4 ht.1 ht.2
    simp only [Matrix.cons_val, Prod.mk.injEq] at h
    refine ⟨e0.symm.trans (h.1.trans ?_), e2.symm.trans h.2⟩
    rw [e1, neg_neg]
  exact ⟨hs0, hs1, hs2, hs3, hs4⟩

private theorem gerver_phaseMeasures_first_half (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 0) = 0 ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 1 ∪ gerverPhaseAngles 2) =
    (capCornerAngleMeasure K).restrict (gerverPhaseAngles 1 ∪ gerverPhaseAngles 2) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 3) =
    ((oppositeSurfaceData B).1 + capCornerAngleMeasure K).restrict (gerverPhaseAngles 3) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 4) =
    (oppositeSurfaceData B).1.restrict (gerverPhaseAngles 4) := by
  -- ### The six stage endpoints, written out
  have hmono := gerverStageTimes_strictMono
  have h01 := hmono (show (0 : Fin 6) < 1 by decide)
  have h12 := hmono (show (1 : Fin 6) < 2 by decide)
  have h23 := hmono (show (2 : Fin 6) < 3 by decide)
  have h34 := hmono (show (3 : Fin 6) < 4 by decide)
  have h45 := hmono (show (4 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h12 h23 h34 h45
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hturn : Real.pi ≤ -1 + 2 * Real.pi := by linarith
  -- ### The five relevant phase intervals
  have hJ0 : gerverPhaseIntervals 0 = Set.Ico 0 GerversSofa.φ :=
    gerverPhaseIntervals_explicit 0
  have hJ1 : gerverPhaseIntervals 1 = Set.Ico GerversSofa.φ GerversSofa.θ :=
    gerverPhaseIntervals_explicit 1
  have hJ2 : gerverPhaseIntervals 2 =
      Set.Ico GerversSofa.θ (Real.pi / 2 - GerversSofa.θ) :=
    gerverPhaseIntervals_explicit 2
  have hJ3 : gerverPhaseIntervals 3 =
      Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) :=
    gerverPhaseIntervals_explicit 3
  have hJ4 : gerverPhaseIntervals 4 =
      Set.Ico (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) :=
    gerverPhaseIntervals_explicit 4
  -- ### The four contact densities of the translated-measure proposition
  have hd := gerver_measureTranslation K B D hK hB hD
  obtain ⟨fA, hfAdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (deriv (fun s ↦ paperGerverContacts s 0) t) (tangentVector (t : Real.Angle)) := ⟨_, rfl⟩
  obtain ⟨fB, hfBdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (-(deriv (fun s ↦ paperGerverContacts s 1) t))
      (tangentVector (t : Real.Angle)) := ⟨_, rfl⟩
  obtain ⟨fC, hfCdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (-(deriv (fun s ↦ paperGerverContacts s 2) (t - Real.pi / 2)))
      (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)) := ⟨_, rfl⟩
  obtain ⟨fD, hfDdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (deriv (fun s ↦ paperGerverContacts s 3) (t - Real.pi / 2))
      (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)) := ⟨_, rfl⟩
  rw [← hfAdef, ← hfBdef, ← hfCdef, ← hfDdef,
    show Set.Ico (gerverStageTimes 3) (gerverStageTimes 5) =
      Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) from by simp [gerverStageTimes],
    show Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 2) =
      Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) from by simp [gerverStageTimes]] at hd
  obtain ⟨hdA, hdB, -, -⟩ := hd
  -- ### The two relevant density windows sit inside a single turn
  have hsubA : Set.Ico (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioc (-1 : ℝ) Real.pi :=
    fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsubB : Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) ⊆
      Set.Ioc (-1 : ℝ) Real.pi := fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨hs0, hs1, hs2, hs3, hs4⟩ :=
    gerver_contact_density_stage_identities fA fB fC fD hfAdef hfBdef hfCdef hfDdef
  -- ### The strict interior signs of the injectivity condition of the given special cap
  have hβ : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ (paperGerverVelocityComponents t).2 := by
    intro t ht
    have h := (K.2.1.2.2 t ht).2
    rw [derivWithin_capInnerCorner_eq_deriv_paperGerverPath K.val hK ht] at h
    exact h.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsub : Set.Ico (0 : ℝ) GerversSofa.φ ⊆ Set.Ico (0 : ℝ) (Real.pi / 2) :=
      fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
    simp only [gerverPhaseAngles, hJ0]
    rw [Measure.restrict_eq_zero,
      hdA.angleImage_eq_setLIntegral hturn hsubA measurableSet_Ico hsub]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_restrict_Ico_mem_Ioo (μ := volume) 0 GerversSofa.φ] with t ht
    rw [(hs0 t ht).1, ENNReal.ofReal_zero]
  · have hsub : Set.Ico GerversSofa.φ (Real.pi / 2 - GerversSofa.θ) ⊆
        Set.Ico (0 : ℝ) (Real.pi / 2) :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsubI : Set.Ico GerversSofa.φ (Real.pi / 2 - GerversSofa.θ) ⊆
        Set.Icc (0 : ℝ) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hU : gerverPhaseAngles 1 ∪ gerverPhaseAngles 2 =
        (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ico GerversSofa.φ (Real.pi / 2 - GerversSofa.θ) := by
      simp only [gerverPhaseAngles, hJ1, hJ2, ← Set.image_union,
        Set.Ico_union_Ico_eq_Ico h12.le h23.le]
    rw [hU]
    refine Real.Angle.measure_restrict_image_congr_of_ae_eq measurableSet_Ico
      (fun T hT hTsub ↦ hdA.angleImage_eq_setLIntegral hturn hsubA hT (hTsub.trans hsub))
      (fun T hT hTsub ↦ capCornerAngleMeasure_angleImage_eq_setLIntegral K hT
        (hTsub.trans hsubI)) ?_
    filter_upwards [ae_restrict_Ico_mem_Ioo_union_Ioo (μ := volume) GerversSofa.φ GerversSofa.θ
      (Real.pi / 2 - GerversSofa.θ)] with t ht
    rcases ht with ht | ht
    · rw [(hs1 t ht).1,
        capCornerDensity_eq_velocity_tangential K hK ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    · rw [(hs2 t ht).1,
        capCornerDensity_eq_velocity_tangential K hK ⟨by linarith [ht.1], by linarith [ht.2]⟩]
  · have hsub : Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) ⊆
        Set.Ico (0 : ℝ) (Real.pi / 2) :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsubB' : Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) ⊆
        Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) :=
      fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
    have hsubI : Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) ⊆
        Set.Icc (0 : ℝ) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsubO : Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) ⊆
        Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hcorner : ∀ T, MeasurableSet T →
        T ⊆ Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) →
        capCornerAngleMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
          ∫⁻ t in T, ENNReal.ofReal ((paperGerverVelocityComponents t).2) ∂volume := by
      intro T hT hTsub
      rw [capCornerAngleMeasure_angleImage_eq_setLIntegral K hT (hTsub.trans hsubI)]
      exact setLIntegral_congr_fun hT fun t ht ↦ by
        rw [capCornerDensity_eq_velocity_tangential K hK (hsubO (hTsub ht))]
    have hf0 : ∀ᵐ t ∂volume.restrict
        (Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ)), 0 ≤ fB t :=
      ae_restrict_of_ae_restrict_of_subset hsubB' hdB.2.1
    have hg0 : ∀ᵐ t ∂volume.restrict
        (Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ)),
        0 ≤ (paperGerverVelocityComponents t).2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht using hβ t (hsubO ht)
    have hsum : ∀ᵐ t ∂volume.restrict
        (Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ)),
        fA t = fB t + (paperGerverVelocityComponents t).2 := by
      filter_upwards [ae_restrict_Ico_mem_Ioo (μ := volume) (Real.pi / 2 - GerversSofa.θ)
        (Real.pi / 2 - GerversSofa.φ)] with t ht using (hs3 t ht).1
    simp only [gerverPhaseAngles, hJ3]
    exact Real.Angle.measure_restrict_image_congr_add measurableSet_Ico
      (fun T hT hTsub ↦ hdA.angleImage_eq_setLIntegral hturn hsubA hT (hTsub.trans hsub))
      (fun T hT hTsub ↦ hdB.angleImage_eq_setLIntegral hturn hsubB hT (hTsub.trans hsubB'))
      hcorner (hdB.1.aemeasurable.mono_measure (Measure.restrict_mono hsubB' le_rfl))
      hf0 hg0 hsum
  · have hsub : Set.Ico (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) ⊆
        Set.Ico (0 : ℝ) (Real.pi / 2) := fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
    have hsubB' : Set.Ico (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) ⊆
        Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) :=
      fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
    simp only [gerverPhaseAngles, hJ4]
    refine Real.Angle.measure_restrict_image_congr_of_ae_eq measurableSet_Ico
      (fun T hT hTsub ↦ hdA.angleImage_eq_setLIntegral hturn hsubA hT (hTsub.trans hsub))
      (fun T hT hTsub ↦ hdB.angleImage_eq_setLIntegral hturn hsubB hT (hTsub.trans hsubB')) ?_
    filter_upwards [ae_restrict_Ico_mem_Ioo (μ := volume) (Real.pi / 2 - GerversSofa.φ)
      (Real.pi / 2)] with t ht
    rw [(hs4 t ht).1]

private theorem gerver_phaseMeasures_second_half (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 5) =
    (oppositeSurfaceData D).1.restrict (gerverPhaseAngles 5) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 6) =
    ((oppositeSurfaceData D).1 + capCornerAngleMeasure K).restrict (gerverPhaseAngles 6) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 7 ∪ gerverPhaseAngles 8) =
    (capCornerAngleMeasure K).restrict (gerverPhaseAngles 7 ∪ gerverPhaseAngles 8) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 9) = 0 := by
  -- ### The six stage endpoints, written out
  have hmono := gerverStageTimes_strictMono
  have h01 := hmono (show (0 : Fin 6) < 1 by decide)
  have h12 := hmono (show (1 : Fin 6) < 2 by decide)
  have h23 := hmono (show (2 : Fin 6) < 3 by decide)
  have h34 := hmono (show (3 : Fin 6) < 4 by decide)
  have h45 := hmono (show (4 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h12 h23 h34 h45
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hturn : Real.pi ≤ -1 + 2 * Real.pi := by linarith
  -- ### The five relevant phase intervals
  have hJ5 : gerverPhaseIntervals 5 =
      Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.φ) :=
    gerverPhaseIntervals_explicit 5
  have hJ6 : gerverPhaseIntervals 6 =
      Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) :=
    gerverPhaseIntervals_explicit 6
  have hJ7 : gerverPhaseIntervals 7 =
      Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.θ) :=
    gerverPhaseIntervals_explicit 7
  have hJ8 : gerverPhaseIntervals 8 =
      Set.Ioc (Real.pi - GerversSofa.θ) (Real.pi - GerversSofa.φ) :=
    gerverPhaseIntervals_explicit 8
  have hJ9 : gerverPhaseIntervals 9 = Set.Ioc (Real.pi - GerversSofa.φ) Real.pi :=
    gerverPhaseIntervals_explicit 9
  -- ### The four contact densities of the translated-measure proposition
  have hd := gerver_measureTranslation K B D hK hB hD
  obtain ⟨fA, hfAdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (deriv (fun s ↦ paperGerverContacts s 0) t) (tangentVector (t : Real.Angle)) := ⟨_, rfl⟩
  obtain ⟨fB, hfBdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (-(deriv (fun s ↦ paperGerverContacts s 1) t))
      (tangentVector (t : Real.Angle)) := ⟨_, rfl⟩
  obtain ⟨fC, hfCdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (-(deriv (fun s ↦ paperGerverContacts s 2) (t - Real.pi / 2)))
      (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)) := ⟨_, rfl⟩
  obtain ⟨fD, hfDdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (deriv (fun s ↦ paperGerverContacts s 3) (t - Real.pi / 2))
      (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)) := ⟨_, rfl⟩
  rw [← hfAdef, ← hfBdef, ← hfCdef, ← hfDdef,
    show Set.Ico (gerverStageTimes 3) (gerverStageTimes 5) =
      Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) from by simp [gerverStageTimes],
    show Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 2) =
      Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) from by simp [gerverStageTimes]] at hd
  obtain ⟨-, -, hdC, hdD⟩ := hd
  -- ### The two relevant density windows sit inside a single turn
  have hsubC : Set.Ioc (Real.pi / 2) Real.pi ⊆ Set.Ioc (-1 : ℝ) Real.pi :=
    fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
  have hsubD : Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) ⊆
      Set.Ioc (-1 : ℝ) Real.pi := fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨hs0, hs1, hs2, hs3, hs4⟩ :=
    gerver_contact_density_stage_identities fA fB fC fD hfAdef hfBdef hfCdef hfDdef
  -- ### The strict interior signs of the injectivity condition of the given special cap
  have hα : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ -(paperGerverVelocityComponents t).1 := by
    intro t ht
    have h := (K.2.1.2.2 t ht).1
    rw [derivWithin_capInnerCorner_eq_deriv_paperGerverPath K.val hK ht] at h
    exact neg_nonneg.2 h.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsub : Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.φ) ⊆
        Set.Ioc (Real.pi / 2) Real.pi := fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
    have hsubD' : Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.φ) ⊆
        Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) :=
      fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
    simp only [gerverPhaseAngles, hJ5]
    refine Real.Angle.measure_restrict_image_congr_of_ae_eq measurableSet_Ioc
      (fun T hT hTsub ↦ hdC.angleImage_eq_setLIntegral hturn hsubC hT (hTsub.trans hsub))
      (fun T hT hTsub ↦ hdD.angleImage_eq_setLIntegral hturn hsubD hT (hTsub.trans hsubD')) ?_
    filter_upwards [ae_restrict_Ioc_mem_Ioo (μ := volume) (Real.pi / 2)
      (Real.pi / 2 + GerversSofa.φ)] with u hu
    have h := (hs0 (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
    rw [show u - Real.pi / 2 + Real.pi / 2 = u from by ring] at h
    rw [h]
  · have hsub : Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) ⊆
        Set.Ioc (Real.pi / 2) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsubD' : Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) ⊆
        Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) :=
      fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
    have hsubI : Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) ⊆
        Set.Icc (0 : ℝ) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsubO : Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) ⊆
        Set.Ioo (Real.pi / 2) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hcorner : ∀ T, MeasurableSet T →
        T ⊆ Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) →
        capCornerAngleMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
          ∫⁻ u in T,
            ENNReal.ofReal (-(paperGerverVelocityComponents (u - Real.pi / 2)).1) ∂volume := by
      intro T hT hTsub
      rw [capCornerAngleMeasure_angleImage_eq_setLIntegral K hT (hTsub.trans hsubI)]
      exact setLIntegral_congr_fun hT fun u hu ↦ by
        rw [capCornerDensity_eq_neg_velocity_normal K hK (hsubO (hTsub hu))]
    have hf0 : ∀ᵐ u ∂volume.restrict
        (Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ)), 0 ≤ fD u :=
      ae_restrict_of_ae_restrict_of_subset hsubD' hdD.2.1
    have hg0 : ∀ᵐ u ∂volume.restrict
        (Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ)),
        0 ≤ -(paperGerverVelocityComponents (u - Real.pi / 2)).1 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact hα _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hsum : ∀ᵐ u ∂volume.restrict
        (Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ)),
        fC u = fD u + -(paperGerverVelocityComponents (u - Real.pi / 2)).1 := by
      filter_upwards [ae_restrict_Ioc_mem_Ioo (μ := volume) (Real.pi / 2 + GerversSofa.φ)
        (Real.pi / 2 + GerversSofa.θ)] with u hu
      have h := (hs1 (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
      rw [show u - Real.pi / 2 + Real.pi / 2 = u from by ring] at h
      rw [h]
      ring
    simp only [gerverPhaseAngles, hJ6]
    exact Real.Angle.measure_restrict_image_congr_add measurableSet_Ioc
      (fun T hT hTsub ↦ hdC.angleImage_eq_setLIntegral hturn hsubC hT (hTsub.trans hsub))
      (fun T hT hTsub ↦ hdD.angleImage_eq_setLIntegral hturn hsubD hT (hTsub.trans hsubD'))
      hcorner (hdD.1.aemeasurable.mono_measure (Measure.restrict_mono hsubD' le_rfl))
      hf0 hg0 hsum
  · have hsub : Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.φ) ⊆
        Set.Ioc (Real.pi / 2) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsubI : Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.φ) ⊆
        Set.Icc (0 : ℝ) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hU : gerverPhaseAngles 7 ∪ gerverPhaseAngles 8 =
        (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.φ) := by
      simp only [gerverPhaseAngles, hJ7, hJ8, ← Set.image_union,
        Set.Ioc_union_Ioc_eq_Ioc (by linarith : Real.pi / 2 + GerversSofa.θ ≤
          Real.pi - GerversSofa.θ) (by linarith : Real.pi - GerversSofa.θ ≤
          Real.pi - GerversSofa.φ)]
    rw [hU]
    refine Real.Angle.measure_restrict_image_congr_of_ae_eq measurableSet_Ioc
      (fun T hT hTsub ↦ hdC.angleImage_eq_setLIntegral hturn hsubC hT (hTsub.trans hsub))
      (fun T hT hTsub ↦ capCornerAngleMeasure_angleImage_eq_setLIntegral K hT
        (hTsub.trans hsubI)) ?_
    filter_upwards [ae_restrict_Ioc_mem_Ioo_union_Ioo (μ := volume)
      (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.θ)
      (Real.pi - GerversSofa.φ)] with u hu
    have hmem : u ∈ Set.Ioo (Real.pi / 2) Real.pi := by
      rcases hu with hu | hu
      · exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      · exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [capCornerDensity_eq_neg_velocity_normal K hK hmem]
    rcases hu with hu | hu
    · have h := (hs2 (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
      rw [show u - Real.pi / 2 + Real.pi / 2 = u from by ring] at h
      rw [h]
    · have h := (hs3 (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
      rw [show u - Real.pi / 2 + Real.pi / 2 = u from by ring] at h
      rw [h]
  · have hsub : Set.Ioc (Real.pi - GerversSofa.φ) Real.pi ⊆
        Set.Ioc (Real.pi / 2) Real.pi := fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
    simp only [gerverPhaseAngles, hJ9]
    rw [Measure.restrict_eq_zero,
      hdC.angleImage_eq_setLIntegral hturn hsubC measurableSet_Ioc hsub]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_restrict_Ioc_mem_Ioo (μ := volume) (Real.pi - GerversSofa.φ)
      Real.pi] with u hu
    have h := (hs4 (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
    rw [show u - Real.pi / 2 + Real.pi / 2 = u from by ring] at h
    rw [h, ENNReal.ofReal_zero]

theorem gerver_phaseMeasures (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    GerverPhaseMeasureIdentities K B D := by
  obtain ⟨h0, h1, h2, h3⟩ := gerver_phaseMeasures_first_half K B D hK hB hD
  obtain ⟨h4, h5, h6, h7⟩ := gerver_phaseMeasures_second_half K B D hK hB hD
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Integrating the variation of `𝒬` over the Gerver phases

The ten phase windows `gerverPhaseAngles j` partition the angular window `[0, π]` except for the
single angle `π/2`, and six of them cover the domain of the inner-corner measure except for two
angles.  Since the cap surface measure integrates a continuous integrand and the corner measure
has no atoms, `qVariationIntegral_eq_phaseSum` rewrites the four integrals of the variation
formula as the eight contributions of the source table (`gerverPhaseContribution`), grouped so
that `gerver_phaseMeasures` applies to each of them.

`gerverPhaseContribution_nonpos` then signs each contribution.  Six of the eight vanish or cancel
outright against the corner measure; on the two active right windows and the two active left
windows the phase identities turn the remaining cap measure into the tail measure, and the
resulting integrand is the difference between the competitor's support sum and the base support
sum, which is `≤ 1 - 1 = 0` by the cap-tail constraints.
-/

/-! ### The angular phase windows are measurable -/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Each of the ten angular phase windows of Gerver's cap is a Borel set. -/
theorem measurableSet_gerverPhaseAngles (j : Fin 10) : MeasurableSet (gerverPhaseAngles j) := by
  have hmono := gerverStageTimes_strictMono
  have h01 := hmono (show (0 : Fin 6) < 1 by decide)
  have h12 := hmono (show (1 : Fin 6) < 2 by decide)
  have h23 := hmono (show (2 : Fin 6) < 3 by decide)
  have h34 := hmono (show (3 : Fin 6) < 4 by decide)
  have h45 := hmono (show (4 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h12 h23 h34 h45
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hturn : Real.pi ≤ -1 + 2 * Real.pi := by linarith
  simp only [gerverPhaseAngles, gerverPhaseIntervals_explicit]
  fin_cases j <;>
    refine Real.Angle.measurableSet_image_of_subset_Ioc hturn
      (by first | exact measurableSet_Ico | exact measurableSet_Ioc) ?_ <;>
    exact fun x hx ↦ ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩

/-! ### The phase windows partition the upper half-circle -/

private theorem injOn_angleCoe_Icc_zero_pi :
    Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) (Set.Icc 0 Real.pi) := by
  have hsub : Set.Icc (0 : ℝ) Real.pi ⊆ Set.Ioc (-1 : ℝ) Real.pi :=
    fun x hx ↦ ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  exact (Real.Angle.injOn_coe_Ioc (by linarith [Real.pi_gt_three])).mono hsub

private theorem iUnion_gerverPhaseIntervals :
    (⋃ j, gerverPhaseIntervals j) =
      Set.Ico 0 (Real.pi / 2) ∪ Set.Ioc (Real.pi / 2) Real.pi := by
  have horder := gerverStageTimes_strictMono
  have h01 := horder (show (0 : Fin 6) < 1 by decide)
  have h12 := horder (show (1 : Fin 6) < 2 by decide)
  have h23 := horder (show (2 : Fin 6) < 3 by decide)
  have h34 := horder (show (3 : Fin 6) < 4 by decide)
  have h45 := horder (show (4 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h12 h23 h34 h45
  simp only [gerverPhaseIntervals_explicit]
  simp only [Set.iUnion_fin_add_one_eq_iUnion_succ, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Set.iUnion_of_empty, Set.union_empty]
  have hlo : (((Set.Ico 0 GerversSofa.φ ∪ Set.Ico GerversSofa.φ GerversSofa.θ) ∪
      Set.Ico GerversSofa.θ (Real.pi / 2 - GerversSofa.θ)) ∪
      Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ)) ∪
      Set.Ico (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) =
      Set.Ico 0 (Real.pi / 2) := by
    rw [Set.Ico_union_Ico_eq_Ico h01.le h12.le,
      Set.Ico_union_Ico_eq_Ico (by linarith) h23.le,
      Set.Ico_union_Ico_eq_Ico (by linarith) h34.le,
      Set.Ico_union_Ico_eq_Ico (by linarith) h45.le]
  have hhi : (((Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.φ) ∪
      Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ)) ∪
      Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.θ)) ∪
      Set.Ioc (Real.pi - GerversSofa.θ) (Real.pi - GerversSofa.φ)) ∪
      Set.Ioc (Real.pi - GerversSofa.φ) Real.pi = Set.Ioc (Real.pi / 2) Real.pi := by
    rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
      Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
      Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
      Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]
  rw [← hlo, ← hhi]
  ac_rfl

private theorem pairwise_disjoint_gerverPhaseIntervals :
    Pairwise (fun i j ↦ Disjoint (gerverPhaseIntervals i) (gerverPhaseIntervals j)) := by
  have horder := gerverStageTimes_strictMono
  have h01 := horder (show (0 : Fin 6) < 1 by decide)
  have h12 := horder (show (1 : Fin 6) < 2 by decide)
  have h23 := horder (show (2 : Fin 6) < 3 by decide)
  have h34 := horder (show (3 : Fin 6) < 4 by decide)
  have h45 := horder (show (4 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h12 h23 h34 h45
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hi hj
  rw [gerverPhaseIntervals_explicit] at hi hj
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals linarith [hi.1, hi.2, hj.1, hj.2]

private theorem gerverPhaseIntervals_subset_Icc (k : Fin 10) :
    gerverPhaseIntervals k ⊆ Set.Icc 0 Real.pi := by
  intro z hz
  have hz' := Set.mem_iUnion.mpr ⟨k, hz⟩
  rw [iUnion_gerverPhaseIntervals] at hz'
  rcases hz' with h | h
  · exact ⟨h.1, by linarith [h.2, Real.pi_pos]⟩
  · exact ⟨by linarith [h.1, Real.pi_pos], h.2⟩

private theorem iUnion_gerverPhaseAngles_union_top :
    (⋃ j, gerverPhaseAngles j) ∪ {((Real.pi / 2 : ℝ) : Real.Angle)} =
      (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc 0 Real.pi := by
  have hreal : (⋃ j, gerverPhaseIntervals j) ∪ {Real.pi / 2} = Set.Icc 0 Real.pi := by
    rw [iUnion_gerverPhaseIntervals]
    ext t
    simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioc, Set.mem_singleton_iff, Set.mem_Icc]
    constructor
    · rintro ((h | h) | rfl) <;> constructor <;> linarith [Real.pi_pos]
    · intro ht
      rcases lt_trichotomy t (Real.pi / 2) with h | h | h
      · exact Or.inl (Or.inl ⟨ht.1, h⟩)
      · exact Or.inr h
      · exact Or.inl (Or.inr ⟨h, ht.2⟩)
  rw [← hreal, Set.image_union, Set.image_iUnion]
  simp only [gerverPhaseAngles, Set.image_singleton]

private theorem pairwise_disjoint_gerverPhaseAngles :
    Pairwise (fun i j ↦ Disjoint (gerverPhaseAngles i) (gerverPhaseAngles j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro t ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hxy := injOn_angleCoe_Icc_zero_pi (gerverPhaseIntervals_subset_Icc j hy)
    (gerverPhaseIntervals_subset_Icc i hx) heq
  subst y
  exact Set.disjoint_left.mp (pairwise_disjoint_gerverPhaseIntervals hij) hx hy

/-- The two active right-tail phases make up the angular window `[π/2 - θ, π/2)`. -/
theorem gerverPhaseAngles_three_union_four :
    gerverPhaseAngles 3 ∪ gerverPhaseAngles 4 =
      (fun t : ℝ ↦ (t : Real.Angle)) ''
        Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) := by
  have horder := gerverStageTimes_strictMono
  have h34 := horder (show (3 : Fin 6) < 4 by decide)
  have h45 := horder (show (4 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h34 h45
  simp only [gerverPhaseAngles, ← Set.image_union, gerverPhaseIntervals_explicit,
    Matrix.cons_val]
  rw [Set.Ico_union_Ico_eq_Ico h34.le h45.le]

/-- The two active left-tail phases make up the angular window `(π/2, π/2 + θ]`. -/
theorem gerverPhaseAngles_five_union_six :
    gerverPhaseAngles 5 ∪ gerverPhaseAngles 6 =
      (fun t : ℝ ↦ (t : Real.Angle)) ''
        Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) := by
  have horder := gerverStageTimes_strictMono
  have h01 := horder (show (0 : Fin 6) < 1 by decide)
  have h12 := horder (show (1 : Fin 6) < 2 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h12
  simp only [gerverPhaseAngles, ← Set.image_union, gerverPhaseIntervals_explicit,
    Matrix.cons_val]
  rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]

/-! ### Splitting the four variation integrals over the phase windows -/

private theorem setIntegral_union_eq_left_of_measure_eq_zero (μ : Measure Real.Angle)
    (f : Real.Angle → ℝ) {S T : Set Real.Angle} (hT : μ T = 0) :
    (∫ t in S ∪ T, f t ∂μ) = ∫ t in S, f t ∂μ := by
  apply integral_union_eq_left_of_ae
  rw [Measure.restrict_eq_zero.mpr hT]
  simp

private theorem setIntegral_angleImage_Icc_eq_sum (μ : Measure Real.Angle)
    (f : Real.Angle → ℝ) (hf : Integrable f μ)
    (htop : f ((Real.pi / 2 : ℝ) : Real.Angle) = 0) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi, f t ∂μ) =
      ∑ j, ∫ t in gerverPhaseAngles j, f t ∂μ := by
  rw [← iUnion_gerverPhaseAngles_union_top,
    integral_union_eq_left_of_forall (measurableSet_singleton _) (by
      intro t ht
      obtain rfl := Set.mem_singleton_iff.mp ht
      exact htop)]
  exact integral_iUnion_fintype measurableSet_gerverPhaseAngles
    pairwise_disjoint_gerverPhaseAngles fun _ ↦ hf.restrict

private theorem setIntegral_right_window_eq_add (μ : Measure Real.Angle) (f : Real.Angle → ℝ)
    (hf : Integrable f μ)
    (hinactive : μ ((fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo paperGerverConstants.2.1 (Real.pi / 2 - GerversSofa.θ)) = 0) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo paperGerverConstants.2.1 (Real.pi / 2), f t ∂μ) =
      (∫ t in gerverPhaseAngles 3, f t ∂μ) + (∫ t in gerverPhaseAngles 4, f t ∂μ) := by
  have horder := gerverStageTimes_strictMono
  have h13 := horder (show (1 : Fin 6) < 3 by decide)
  have h35 := horder (show (3 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h13 h35
  have hreal : Set.Ioo paperGerverConstants.2.1 (Real.pi / 2) =
      Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) ∪
        Set.Ioo paperGerverConstants.2.1 (Real.pi / 2 - GerversSofa.θ) := by
    ext t
    change (_ < t ∧ t < _) ↔ (_ ≤ t ∧ t < _) ∨ (_ < t ∧ t < _)
    change (GerversSofa.φ < t ∧ t < Real.pi / 2) ↔ _
    constructor
    · intro ht
      by_cases h : Real.pi / 2 - GerversSofa.θ ≤ t
      · exact Or.inl ⟨h, ht.2⟩
      · exact Or.inr ⟨ht.1, lt_of_not_ge h⟩
    · rintro (h | h) <;> (try simp only [paperGerverConstants] at h) <;>
        constructor <;> linarith [h.1, h.2]
  rw [hreal, Set.image_union, ← gerverPhaseAngles_three_union_four,
    setIntegral_union_eq_left_of_measure_eq_zero μ f hinactive]
  exact setIntegral_union (pairwise_disjoint_gerverPhaseAngles (by decide : (3 : Fin 10) ≠ 4))
    (measurableSet_gerverPhaseAngles 4) hf.restrict hf.restrict

private theorem setIntegral_left_window_eq_add (μ : Measure Real.Angle) (f : Real.Angle → ℝ)
    (hf : Integrable f μ)
    (hinactive : μ ((fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo (Real.pi / 2 + GerversSofa.θ)
        (Real.pi / 2 + paperGerverConstants.2.2)) = 0) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2), f t ∂μ) =
      (∫ t in gerverPhaseAngles 5, f t ∂μ) + (∫ t in gerverPhaseAngles 6, f t ∂μ) := by
  have horder := gerverStageTimes_strictMono
  have h02 := horder (show (0 : Fin 6) < 2 by decide)
  have h24 := horder (show (2 : Fin 6) < 4 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h02 h24
  have hreal : Set.Ioo (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2) =
      Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) ∪
        Set.Ioo (Real.pi / 2 + GerversSofa.θ)
          (Real.pi / 2 + paperGerverConstants.2.2) := by
    ext t
    change (_ < t ∧ t < _) ↔ (_ < t ∧ t ≤ _) ∨ (_ < t ∧ t < _)
    change (Real.pi / 2 < t ∧ t < Real.pi / 2 + (Real.pi / 2 - GerversSofa.φ)) ↔ _
    constructor
    · intro ht
      by_cases h : t ≤ Real.pi / 2 + GerversSofa.θ
      · exact Or.inl ⟨ht.1, h⟩
      · exact Or.inr ⟨lt_of_not_ge h, ht.2⟩
    · rintro (h | h) <;> (try simp only [paperGerverConstants] at h) <;>
        constructor <;> linarith [h.1, h.2]
  rw [hreal, Set.image_union, ← gerverPhaseAngles_five_union_six,
    setIntegral_union_eq_left_of_measure_eq_zero μ f hinactive]
  exact setIntegral_union (pairwise_disjoint_gerverPhaseAngles (by decide : (5 : Fin 10) ≠ 6))
    (measurableSet_gerverPhaseAngles 6) hf.restrict hf.restrict

/-- The six phases on which the inner-corner measure is active. -/
private def cornerPhaseIndex : Fin 6 → Fin 10 := ![1, 2, 3, 6, 7, 8]

private theorem iUnion_gerverPhaseIntervals_cornerPhaseIndex :
    (⋃ i, gerverPhaseIntervals (cornerPhaseIndex i)) =
      Set.Ico paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
        Set.Ioc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2) := by
  have horder := gerverStageTimes_strictMono
  have h12 := horder (show (1 : Fin 6) < 2 by decide)
  have h23 := horder (show (2 : Fin 6) < 3 by decide)
  have h34 := horder (show (3 : Fin 6) < 4 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h12 h23 h34
  simp only [Set.iUnion_fin_add_one_eq_iUnion_succ, Function.comp_def,
    cornerPhaseIndex, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Set.iUnion_of_empty, Set.union_empty, gerverPhaseIntervals_explicit]
  simp only [Matrix.cons_val, paperGerverConstants]
  have hlo : (Set.Ico GerversSofa.φ GerversSofa.θ ∪
      Set.Ico GerversSofa.θ (Real.pi / 2 - GerversSofa.θ)) ∪
      Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) =
      Set.Ico GerversSofa.φ (Real.pi / 2 - GerversSofa.φ) := by
    rw [Set.Ico_union_Ico_eq_Ico h12.le h23.le, Set.Ico_union_Ico_eq_Ico (by linarith) h34.le]
  have hhi : (Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) ∪
      Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.θ)) ∪
      Set.Ioc (Real.pi - GerversSofa.θ) (Real.pi - GerversSofa.φ) =
      Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi - GerversSofa.φ) := by
    rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
      Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]
  have hend : Real.pi / 2 + (Real.pi / 2 - GerversSofa.φ) = Real.pi - GerversSofa.φ := by ring
  rw [hend, ← hlo, ← hhi]
  ac_rfl

private theorem iUnion_gerverPhaseAngles_cornerPhaseIndex_union_ends :
    (⋃ i, gerverPhaseAngles (cornerPhaseIndex i)) ∪
      {((paperGerverConstants.2.2 : ℝ) : Real.Angle),
        ((Real.pi / 2 + paperGerverConstants.2.1 : ℝ) : Real.Angle)} =
      (fun t : ℝ ↦ (t : Real.Angle)) ''
        (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
          Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
            (Real.pi / 2 + paperGerverConstants.2.2)) := by
  have horder := gerverStageTimes_strictMono
  have h14 := horder (show (1 : Fin 6) < 4 by decide)
  change paperGerverConstants.2.1 < paperGerverConstants.2.2 at h14
  have hreal : (⋃ i, gerverPhaseIntervals (cornerPhaseIndex i)) ∪
      {paperGerverConstants.2.2, Real.pi / 2 + paperGerverConstants.2.1} =
      Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
        Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2) := by
    rw [iUnion_gerverPhaseIntervals_cornerPhaseIndex]
    ext t
    simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioc, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_Icc]
    constructor
    · rintro ((h | h) | (rfl | rfl))
      · exact Or.inl ⟨h.1, h.2.le⟩
      · exact Or.inr ⟨h.1.le, h.2⟩
      · exact Or.inl ⟨h14.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, by linarith⟩
    · rintro (h | h)
      · rcases lt_or_eq_of_le h.2 with hlt | heq
        · exact Or.inl (Or.inl ⟨h.1, hlt⟩)
        · exact Or.inr (Or.inl heq)
      · rcases lt_or_eq_of_le h.1 with hlt | heq
        · exact Or.inl (Or.inr ⟨hlt, h.2⟩)
        · exact Or.inr (Or.inr heq.symm)
  rw [← hreal, Set.image_union, Set.image_iUnion]
  simp only [gerverPhaseAngles, Set.image_pair]

private theorem setIntegral_corner_window_eq_sum (μ : Measure Real.Angle)
    [NullSingletonClass μ] (f : Real.Angle → ℝ) (hf : Integrable f μ) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
        Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2)), f t ∂μ) =
      ∑ i, ∫ t in gerverPhaseAngles (cornerPhaseIndex i), f t ∂μ := by
  rw [← iUnion_gerverPhaseAngles_cornerPhaseIndex_union_ends,
    setIntegral_union_eq_left_of_measure_eq_zero μ f
      (((Set.finite_singleton _).insert _).measure_zero μ)]
  have hinj : Function.Injective cornerPhaseIndex := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [cornerPhaseIndex]
  exact integral_iUnion_fintype (fun i ↦ measurableSet_gerverPhaseAngles (cornerPhaseIndex i))
    (fun i j hij ↦ pairwise_disjoint_gerverPhaseAngles fun h ↦ hij (hinj h)) fun _ ↦ hf.restrict

/-! ### The eight phase contributions of the variation integral -/

/-- The eight contributions of the source table of the variation of `𝒬`: on each group of phases,
the cap surface integral of the support difference, minus the active inner-corner integral, plus
the active tail integral of the tail support difference. -/
def gerverPhaseContribution (X Y : CapTailSpace) : Fin 8 → ℝ :=
  let f := fun t ↦ supportValue Y.cap.val.val t - supportValue X.cap.val.val t
  let g := fun t ↦ (oppositeSurfaceData Y.rightBody).2 t -
    (oppositeSurfaceData X.rightBody).2 t
  let h := fun t ↦ (oppositeSurfaceData Y.leftBody).2 t -
    (oppositeSurfaceData X.leftBody).2 t
  let a := fun S ↦ ∫ t in S, f t ∂surfaceAreaMeasure X.cap.val.val
  let c := fun S ↦ ∫ t in S, f t ∂capCornerAngleMeasure X.cap
  let b := fun S ↦ ∫ t in S, g t ∂(oppositeSurfaceData X.rightBody).1
  let d := fun S ↦ ∫ t in S, h t ∂(oppositeSurfaceData X.leftBody).1
  ![a (gerverPhaseAngles 0),
    a (gerverPhaseAngles 1 ∪ gerverPhaseAngles 2) -
      c (gerverPhaseAngles 1 ∪ gerverPhaseAngles 2),
    a (gerverPhaseAngles 3) - c (gerverPhaseAngles 3) + b (gerverPhaseAngles 3),
    a (gerverPhaseAngles 4) + b (gerverPhaseAngles 4),
    a (gerverPhaseAngles 5) + d (gerverPhaseAngles 5),
    a (gerverPhaseAngles 6) - c (gerverPhaseAngles 6) + d (gerverPhaseAngles 6),
    a (gerverPhaseAngles 7 ∪ gerverPhaseAngles 8) -
      c (gerverPhaseAngles 7 ∪ gerverPhaseAngles 8),
    a (gerverPhaseAngles 9)]

private theorem setIntegral_add_of_restrict_eq_add {S : Set Real.Angle}
    {μ ν κ : Measure Real.Angle} {f g : Real.Angle → ℝ}
    (h : μ.restrict S = (ν + κ).restrict S)
    (hfν : Integrable f ν) (hfκ : Integrable f κ) (hg : Integrable g ν) :
    (∫ t in S, f t ∂μ) - (∫ t in S, f t ∂κ) + (∫ t in S, g t ∂ν) =
      ∫ t in S, (f t + g t) ∂ν := by
  rw [h, Measure.restrict_add, integral_add_measure hfν.restrict hfκ.restrict,
    integral_add hfν.restrict hg.restrict]
  ring

private theorem setIntegral_add_of_restrict_eq {S : Set Real.Angle}
    {μ ν : Measure Real.Angle} {f g : Real.Angle → ℝ}
    (h : μ.restrict S = ν.restrict S)
    (hf : Integrable f ν) (hg : Integrable g ν) :
    (∫ t in S, f t ∂μ) + (∫ t in S, g t ∂ν) =
      ∫ t in S, (f t + g t) ∂ν := by
  rw [h, integral_add hf.restrict hg.restrict]

private theorem right_support_difference_nonpos (X Y : CapTailSpace) (t : ℝ)
    (ht : t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2))
    (hX : supportValue X.cap.val.val (t : Real.Angle) +
      (oppositeSurfaceData X.rightBody).2 (t : Real.Angle) = 1) :
    (supportValue Y.cap.val.val (t : Real.Angle) -
      supportValue X.cap.val.val (t : Real.Angle)) +
      ((oppositeSurfaceData Y.rightBody).2 (t : Real.Angle) -
        (oppositeSurfaceData X.rightBody).2 (t : Real.Angle)) ≤ 0 := by
  have hY := Y.right_bound t ht
  simp only [oppositeSurfaceData] at hX ⊢
  simp only [Real.Angle.coe_add, add_comm (Real.pi : Real.Angle)] at hY
  linarith

private theorem left_support_difference_nonpos (X Y : CapTailSpace) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2)
    (hX : supportValue X.cap.val.val ((Real.pi / 2 + t : ℝ) : Real.Angle) +
      (oppositeSurfaceData X.leftBody).2 ((Real.pi / 2 + t : ℝ) : Real.Angle) = 1) :
    (supportValue Y.cap.val.val ((Real.pi / 2 + t : ℝ) : Real.Angle) -
      supportValue X.cap.val.val ((Real.pi / 2 + t : ℝ) : Real.Angle)) +
      ((oppositeSurfaceData Y.leftBody).2 ((Real.pi / 2 + t : ℝ) : Real.Angle) -
        (oppositeSurfaceData X.leftBody).2 ((Real.pi / 2 + t : ℝ) : Real.Angle)) ≤ 0 := by
  have hY := Y.left_bound t ht
  have heq : (((Real.pi / 2 + t : ℝ) : Real.Angle) + (Real.pi : Real.Angle)) =
      ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add]
    congr 1
    ring
  simp only [oppositeSurfaceData, heq] at hX ⊢
  linarith

private theorem exists_mem_right_tail_domain {t : Real.Angle}
    (ht : t ∈ gerverPhaseAngles 3 ∪ gerverPhaseAngles 4) :
    ∃ s ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2), (s : Real.Angle) = t := by
  have horder := gerverStageTimes_strictMono
  have h13 := horder (show (1 : Fin 6) < 3 by decide)
  have h35 := horder (show (3 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h13 h35
  rw [gerverPhaseAngles_three_union_four] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact ⟨s, ⟨le_trans h13.le hs.1, hs.2.le⟩, rfl⟩

private theorem exists_mem_left_tail_domain {t : Real.Angle}
    (ht : t ∈ gerverPhaseAngles 5 ∪ gerverPhaseAngles 6) :
    ∃ s ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
      ((Real.pi / 2 + s : ℝ) : Real.Angle) = t := by
  have horder := gerverStageTimes_strictMono
  have h02 := horder (show (0 : Fin 6) < 2 by decide)
  have h24 := horder (show (2 : Fin 6) < 4 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h02 h24
  rw [gerverPhaseAngles_five_union_six] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  refine ⟨s - Real.pi / 2, ⟨by linarith [hs.1], ?_⟩, ?_⟩
  · change s - Real.pi / 2 ≤ Real.pi / 2 - GerversSofa.φ
    linarith [hs.2]
  · congr 1
    ring

/-- Each of the eight phase contributions is nonpositive: the phase measure identities cancel the
cap measure against the active corner and tail measures, and the cap-tail constraints sign the
remaining tail integrands. -/
theorem gerverPhaseContribution_nonpos (X Y : CapTailSpace)
    (hphase : GerverPhaseMeasureIdentities X.cap X.rightBody X.leftBody)
    (hbaseB : ∀ t ∈ gerverPhaseAngles 3 ∪ gerverPhaseAngles 4,
      supportValue X.cap.val.val t + (oppositeSurfaceData X.rightBody).2 t = 1)
    (hbaseD : ∀ t ∈ gerverPhaseAngles 5 ∪ gerverPhaseAngles 6,
      supportValue X.cap.val.val t + (oppositeSurfaceData X.leftBody).2 t = 1)
    (i : Fin 8) : gerverPhaseContribution X Y i ≤ 0 := by
  obtain ⟨h0, h12, h3, h4, h5, h6, h78, h9⟩ := hphase
  have hfB : Integrable (fun t ↦ supportValue Y.cap.val.val t -
      supportValue X.cap.val.val t) (oppositeSurfaceData X.rightBody).1 :=
    Real.Angle.integrable_of_continuous
      ((continuous_supportValue _).sub (continuous_supportValue _))
  have hfD : Integrable (fun t ↦ supportValue Y.cap.val.val t -
      supportValue X.cap.val.val t) (oppositeSurfaceData X.leftBody).1 :=
    Real.Angle.integrable_of_continuous
      ((continuous_supportValue _).sub (continuous_supportValue _))
  have hfC : Integrable (fun t ↦ supportValue Y.cap.val.val t -
      supportValue X.cap.val.val t) (capCornerAngleMeasure X.cap) :=
    Real.Angle.integrable_of_continuous
      ((continuous_supportValue _).sub (continuous_supportValue _))
  have hgB : Integrable (fun t ↦ (oppositeSurfaceData Y.rightBody).2 t -
      (oppositeSurfaceData X.rightBody).2 t) (oppositeSurfaceData X.rightBody).1 :=
    Real.Angle.integrable_of_continuous
      ((continuous_oppositeSurfaceData_snd _).sub (continuous_oppositeSurfaceData_snd _))
  have hgD : Integrable (fun t ↦ (oppositeSurfaceData Y.leftBody).2 t -
      (oppositeSurfaceData X.leftBody).2 t) (oppositeSurfaceData X.leftBody).1 :=
    Real.Angle.integrable_of_continuous
      ((continuous_oppositeSurfaceData_snd _).sub (continuous_oppositeSurfaceData_snd _))
  have hB : ∀ t ∈ gerverPhaseAngles 3 ∪ gerverPhaseAngles 4,
      (supportValue Y.cap.val.val t - supportValue X.cap.val.val t) +
        ((oppositeSurfaceData Y.rightBody).2 t -
          (oppositeSurfaceData X.rightBody).2 t) ≤ 0 := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := exists_mem_right_tail_domain ht
    exact right_support_difference_nonpos X Y s hs (hbaseB _ ht)
  have hD : ∀ t ∈ gerverPhaseAngles 5 ∪ gerverPhaseAngles 6,
      (supportValue Y.cap.val.val t - supportValue X.cap.val.val t) +
        ((oppositeSurfaceData Y.leftBody).2 t -
          (oppositeSurfaceData X.leftBody).2 t) ≤ 0 := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := exists_mem_left_tail_domain ht
    exact left_support_difference_nonpos X Y s hs (hbaseD _ ht)
  fin_cases i
  · simp [gerverPhaseContribution, h0]
  · simp [gerverPhaseContribution, h12]
  · change (_ - _ + _) ≤ 0
    rw [setIntegral_add_of_restrict_eq_add h3 hfB hfC hgB]
    exact setIntegral_nonpos (measurableSet_gerverPhaseAngles 3) fun t ht ↦ hB t (Or.inl ht)
  · change (_ + _) ≤ 0
    rw [setIntegral_add_of_restrict_eq h4 hfB hgB]
    exact setIntegral_nonpos (measurableSet_gerverPhaseAngles 4) fun t ht ↦ hB t (Or.inr ht)
  · change (_ + _) ≤ 0
    rw [setIntegral_add_of_restrict_eq h5 hfD hgD]
    exact setIntegral_nonpos (measurableSet_gerverPhaseAngles 5) fun t ht ↦ hD t (Or.inl ht)
  · change (_ - _ + _) ≤ 0
    rw [setIntegral_add_of_restrict_eq_add h6 hfD hfC hgD]
    exact setIntegral_nonpos (measurableSet_gerverPhaseAngles 6) fun t ht ↦ hD t (Or.inr ht)
  · simp [gerverPhaseContribution, h78]
  · simp [gerverPhaseContribution, h9]

/-! ### The four variation integrals as the eight phase contributions -/

/-- The four integrals of the variation formula regroup into the eight contributions of the source
table, given that the two tails carry no surface measure between their active windows. -/
theorem qVariationIntegral_eq_phaseSum (X Y : CapTailSpace)
    (hinactiveB : (oppositeSurfaceData X.rightBody).1 ((fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo paperGerverConstants.2.1 (Real.pi / 2 - GerversSofa.θ)) = 0)
    (hinactiveD : (oppositeSurfaceData X.leftBody).1 ((fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo (Real.pi / 2 + GerversSofa.θ) (Real.pi / 2 + paperGerverConstants.2.2)) = 0) :
    qVariationIntegral X Y = ∑ i, gerverPhaseContribution X Y i := by
  have hfK : Integrable (fun t ↦ supportValue Y.cap.val.val t -
      supportValue X.cap.val.val t) (surfaceAreaMeasure X.cap.val.val) :=
    Real.Angle.integrable_of_continuous
      ((continuous_supportValue _).sub (continuous_supportValue _))
  have hfC : Integrable (fun t ↦ supportValue Y.cap.val.val t -
      supportValue X.cap.val.val t) (capCornerAngleMeasure X.cap) :=
    Real.Angle.integrable_of_continuous
      ((continuous_supportValue _).sub (continuous_supportValue _))
  have hgB : Integrable (fun t ↦ (oppositeSurfaceData Y.rightBody).2 t -
      (oppositeSurfaceData X.rightBody).2 t) (oppositeSurfaceData X.rightBody).1 :=
    Real.Angle.integrable_of_continuous
      ((continuous_oppositeSurfaceData_snd _).sub (continuous_oppositeSurfaceData_snd _))
  have hgD : Integrable (fun t ↦ (oppositeSurfaceData Y.leftBody).2 t -
      (oppositeSurfaceData X.leftBody).2 t) (oppositeSurfaceData X.leftBody).1 :=
    Real.Angle.integrable_of_continuous
      ((continuous_oppositeSurfaceData_snd _).sub (continuous_oppositeSurfaceData_snd _))
  rw [qVariationIntegral,
    setIntegral_angleImage_Icc_eq_sum _ _ hfK (by
      rw [Y.cap.val.property.2.2.2.1, X.cap.val.property.2.2.2.1, sub_self]),
    setIntegral_corner_window_eq_sum _ _ hfC,
    setIntegral_right_window_eq_add _ _ hgB hinactiveB,
    setIntegral_left_window_eq_add _ _ hgD hinactiveD]
  have h12 := pairwise_disjoint_gerverPhaseAngles (by decide : (1 : Fin 10) ≠ 2)
  have h78 := pairwise_disjoint_gerverPhaseAngles (by decide : (7 : Fin 10) ≠ 8)
  have hK12 := setIntegral_union h12 (measurableSet_gerverPhaseAngles 2)
    hfK.restrict hfK.restrict
  have hC12 := setIntegral_union h12 (measurableSet_gerverPhaseAngles 2)
    hfC.restrict hfC.restrict
  have hK78 := setIntegral_union h78 (measurableSet_gerverPhaseAngles 8)
    hfK.restrict hfK.restrict
  have hC78 := setIntegral_union h78 (measurableSet_gerverPhaseAngles 8)
    hfC.restrict hfC.restrict
  simp only [gerverPhaseContribution, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, cornerPhaseIndex,
    hK12, hC12, hK78, hC78]
  ring!

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver's cap attains the upper bound `Q`

`gerver_upperBoundQ_matches` evaluates the upper-bound functional `Q` at the cap of Gerver's
sofa together with its two canonical tails, and finds the sofa area functional `A` there.

The niche area is read off the four-piece counterclockwise traversal of the niche boundary
(`gerver_niche_orientation`): additivity of the curve area functional over that traversal
(`curveArea_concatenation`) expresses the niche area as the curve area of the middle corner
path minus the curve areas of the two inner contact curves, because the two contact pieces are
traversed backwards and the base segment lies on the line `y = 0`.  The tail geometry
(`gerver_tailGeometry`) identifies the two contact curves with the two convex tail arcs, so
their curve areas are the two `convexArcArea` terms of `Q`, and it identifies the two corners
of `Q`'s connector segments, whose signed areas therefore vanish.
-/

/-! ## The four-piece traversal of the niche boundary -/

public section

noncomputable section

namespace MovingSofa

/-- The niche traversal is the concatenation of four pieces, each reparametrized by `[0, 1]`
through an increasing surjection: the second contact curve reversed, the inner corner path over
`[t₁, t₄]`, the fourth contact curve reversed, and the base segment.  The two reversed contact
pieces enter as bounded-variation paths `y₁`, `y₃` on `[0, 1]`, described by the two affine
parameter changes of the traversal. -/
private theorem isPathConcatenation_gerverNicheBoundary (K : SpecialCapSpace)
    (hcorner : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      capInnerCorner K.val t = paperGerverPath t)
    {Γ : ContinuousBVPaths 0 4} (hΓ : Γ.val = gerverNicheBoundary)
    {y₁ y₃ : ContinuousBVPaths 0 1}
    (hy₁ : ∀ u : Set.Icc (0 : ℝ) 1, y₁.val u =
      paperGerverContacts (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * (u : ℝ)) 1)
    (hy₃ : ∀ u : Set.Icc (0 : ℝ) 1, y₃.val u =
      paperGerverContacts (gerverStageTimes 2 * (1 - (u : ℝ))) 3) :
    IsPathConcatenation (⟨0, 4, by norm_num, Γ⟩ : RectifiablePathData)
      ![(⟨0, 1, zero_le_one, y₁⟩ : RectifiablePathData),
        ⟨gerverStageTimes 1, gerverStageTimes 4,
          (gerverStageTimes_strictMono (show (1 : Fin 6) < 4 by decide)).le, capMiddleBV K⟩,
        ⟨0, 1, zero_le_one, y₃⟩,
        ⟨0, 1, zero_le_one, lineSegmentBVPath (paperGerverContacts 0 3)
          (paperGerverContacts (Real.pi / 2) 1)⟩] := by
  have h0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have h5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have h01 : gerverStageTimes 0 < gerverStageTimes 1 :=
    gerverStageTimes_strictMono (show (0 : Fin 6) < 1 by decide)
  have h45 : gerverStageTimes 4 < gerverStageTimes 5 :=
    gerverStageTimes_strictMono (show (4 : Fin 6) < 5 by decide)
  obtain ⟨ψ₂, hψ₂c, hψ₂m, hψ₂s, hψ₂v⟩ := Set.Icc.exists_affine_monotone_surjection zero_lt_one
    (gerverStageTimes_strictMono (show (1 : Fin 6) < 4 by decide))
  refine ⟨by norm_num, ![⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨2, by norm_num⟩,
    ⟨3, by norm_num⟩, ⟨4, by norm_num⟩], ?_, rfl, rfl, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | (exact absurd hij (by decide))
        | (refine Subtype.mk_le_mk.mpr ?_; norm_num)
  · intro i
    fin_cases i
    -- ### `[0, 1]`: the second contact curve, reversed
    · obtain ⟨ϕ, hϕc, hϕm, hϕs, hϕv⟩ :
          ∃ ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1, Continuous ϕ ∧ Monotone ϕ ∧
            Function.Surjective ϕ ∧ ∀ u : Set.Icc (0 : ℝ) 1, (ϕ u : ℝ) = 0 + (u : ℝ) :=
        Set.Icc.exists_translation_surjection (by norm_num)
      refine ⟨ϕ, id, hϕc, hϕm, hϕs, continuous_id, monotone_id, Function.surjective_id,
        fun u ↦ ?_⟩
      have hv := hϕv u
      have hmem : (ϕ u : ℝ) ∈ Set.Icc (0 : ℝ) 4 :=
        ⟨by rw [hv]; linarith [u.2.1], by rw [hv]; linarith [u.2.2]⟩
      have harg : Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * (ϕ u : ℝ) =
          Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * (u : ℝ) := by rw [hv]; ring
      rw [hΓ]
      refine (gerverNicheBoundary_of_le_one hmem (by rw [hv]; linarith [u.2.2])).trans ?_
      rw [harg]
      exact (hy₁ u).symm
    -- ### `[1, 2]`: the inner corner path, forwards
    · obtain ⟨ϕ, hϕc, hϕm, hϕs, hϕv⟩ :
          ∃ ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (1 : ℝ) 2, Continuous ϕ ∧ Monotone ϕ ∧
            Function.Surjective ϕ ∧ ∀ u : Set.Icc (0 : ℝ) 1, (ϕ u : ℝ) = 1 + (u : ℝ) :=
        Set.Icc.exists_translation_surjection (by norm_num)
      refine ⟨ϕ, ψ₂, hϕc, hϕm, hϕs, hψ₂c, hψ₂m, hψ₂s, fun u ↦ ?_⟩
      have hv := hϕv u
      have hmem : (ϕ u : ℝ) ∈ Set.Icc (0 : ℝ) 4 :=
        ⟨by rw [hv]; linarith [u.2.1], by rw [hv]; linarith [u.2.2]⟩
      have hψmem : (ψ₂ u : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [(ψ₂ u).2.1], by linarith [(ψ₂ u).2.2]⟩
      have harg : gerverStageTimes 1 +
          (gerverStageTimes 4 - gerverStageTimes 1) * ((ϕ u : ℝ) - 1) = (ψ₂ u : ℝ) := by
        rw [hv, hψ₂v u]; ring
      rw [hΓ]
      refine (gerverNicheBoundary_mid hmem (by rw [hv]; linarith [u.2.1])
        (by rw [hv]; linarith [u.2.2])).trans ?_
      rw [harg]
      exact (hcorner _ hψmem).symm
    -- ### `[2, 3]`: the fourth contact curve, reversed
    · obtain ⟨ϕ, hϕc, hϕm, hϕs, hϕv⟩ :
          ∃ ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (2 : ℝ) 3, Continuous ϕ ∧ Monotone ϕ ∧
            Function.Surjective ϕ ∧ ∀ u : Set.Icc (0 : ℝ) 1, (ϕ u : ℝ) = 2 + (u : ℝ) :=
        Set.Icc.exists_translation_surjection (by norm_num)
      refine ⟨ϕ, id, hϕc, hϕm, hϕs, continuous_id, monotone_id, Function.surjective_id,
        fun u ↦ ?_⟩
      have hv := hϕv u
      have hmem : (ϕ u : ℝ) ∈ Set.Icc (0 : ℝ) 4 :=
        ⟨by rw [hv]; linarith [u.2.1], by rw [hv]; linarith [u.2.2]⟩
      have harg : gerverStageTimes 2 * (3 - (ϕ u : ℝ)) =
          gerverStageTimes 2 * (1 - (u : ℝ)) := by rw [hv]; ring
      rw [hΓ]
      refine (gerverNicheBoundary_third hmem (by rw [hv]; linarith [u.2.1])
        (by rw [hv]; linarith [u.2.2])).trans ?_
      rw [harg]
      exact (hy₃ u).symm
    -- ### `[3, 4]`: the base segment
    · obtain ⟨ϕ, hϕc, hϕm, hϕs, hϕv⟩ :
          ∃ ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (3 : ℝ) 4, Continuous ϕ ∧ Monotone ϕ ∧
            Function.Surjective ϕ ∧ ∀ u : Set.Icc (0 : ℝ) 1, (ϕ u : ℝ) = 3 + (u : ℝ) :=
        Set.Icc.exists_translation_surjection (by norm_num)
      refine ⟨ϕ, id, hϕc, hϕm, hϕs, continuous_id, monotone_id, Function.surjective_id,
        fun u ↦ ?_⟩
      have hv := hϕv u
      have hmem : (ϕ u : ℝ) ∈ Set.Icc (0 : ℝ) 4 :=
        ⟨by rw [hv]; linarith [u.2.1], by rw [hv]; linarith [u.2.2]⟩
      rw [hΓ]
      refine (gerverNicheBoundary_base hmem (by rw [hv]; linarith [u.2.1])).trans ?_
      change _ = (lineSegmentBVPath (paperGerverContacts 0 3)
        (paperGerverContacts (Real.pi / 2) 1)).val u
      rw [lineSegmentBVPath_apply, hv, show (4 : ℝ) - (3 + (u : ℝ)) = 1 - (u : ℝ) from by ring,
        show (3 : ℝ) + (u : ℝ) - 3 = (u : ℝ) from by ring]

/-- Additivity of the curve area functional over the four-piece traversal of the niche
boundary.  The base segment contributes nothing because both of its endpoints lie on the line
`y = 0`, and the two contact pieces are traversed backwards, so their reparametrizations
contribute the negatives of their curve areas. -/
private theorem curveAreaFunctional_gerverNicheBoundary (K : SpecialCapSpace)
    (hcorner : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      capInnerCorner K.val t = paperGerverPath t)
    {Γ : ContinuousBVPaths 0 4} (hΓ : Γ.val = gerverNicheBoundary) :
    curveAreaFunctional Γ = curveAreaFunctional (capMiddleBV K) -
      curveAreaFunctional gerverRightContactBV - curveAreaFunctional gerverLeftContactBV := by
  have h0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have h5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have h35 : gerverStageTimes 3 < gerverStageTimes 5 :=
    gerverStageTimes_strictMono (show (3 : Fin 6) < 5 by decide)
  have h02 : gerverStageTimes 0 < gerverStageTimes 2 :=
    gerverStageTimes_strictMono (show (0 : Fin 6) < 2 by decide)
  obtain ⟨φ₁, hφ₁c, hφ₁a, hφ₁s, hφ₁v⟩ :=
    Set.Icc.exists_affine_antitone_surjection zero_lt_one h35
  obtain ⟨φ₃, hφ₃c, hφ₃a, hφ₃s, hφ₃v⟩ :=
    Set.Icc.exists_affine_antitone_surjection zero_lt_one h02
  obtain ⟨y₁, hy₁val, -, hy₁area⟩ := curveArea_reparametrization.1 _ _ 0 1 h35 zero_lt_one
    gerverRightContactBV φ₁ hφ₁c hφ₁s (Or.inr hφ₁a)
  obtain ⟨y₃, hy₃val, -, hy₃area⟩ := curveArea_reparametrization.1 _ _ 0 1 h02 zero_lt_one
    gerverLeftContactBV φ₃ hφ₃c hφ₃s (Or.inr hφ₃a)
  have hy₁ : ∀ u : Set.Icc (0 : ℝ) 1, y₁.val u =
      paperGerverContacts (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * (u : ℝ)) 1 := by
    intro u
    rw [hy₁val]
    exact congrArg (fun r : ℝ ↦ paperGerverContacts r 1) (by rw [hφ₁v u, h5]; ring)
  have hy₃ : ∀ u : Set.Icc (0 : ℝ) 1, y₃.val u =
      paperGerverContacts (gerverStageTimes 2 * (1 - (u : ℝ))) 3 := by
    intro u
    rw [hy₃val]
    exact congrArg (fun r : ℝ ↦ paperGerverContacts r 3) (by rw [hφ₃v u, h0]; ring)
  have hsum : curveAreaFunctional Γ = curveAreaFunctional y₁ +
      curveAreaFunctional (capMiddleBV K) + curveAreaFunctional y₃ +
      curveAreaFunctional (lineSegmentBVPath (paperGerverContacts 0 3)
        (paperGerverContacts (Real.pi / 2) 1)) := by
    have h := curveArea_concatenation (⟨0, 4, by norm_num, Γ⟩ : RectifiablePathData) _
      (isPathConcatenation_gerverNicheBoundary K hcorner hΓ hy₁ hy₃)
    rw [Fin.sum_univ_four] at h
    exact h
  have hseg : curveAreaFunctional (lineSegmentBVPath (paperGerverContacts 0 3)
      (paperGerverContacts (Real.pi / 2) 1)) = 0 := by
    rw [curveAreaFunctional_lineSegmentBVPath, segmentArea, planeCrossProduct,
      gerver_niche_piece_endpoints.2.2.1, gerver_niche_piece_endpoints.2.2.2]
    ring
  rw [hsum, hseg, hy₁area hφ₁a, hy₃area hφ₃a]
  ring

/-! ## The niche area of the Gerver cap -/

/-- The niche area of the Gerver cap, in terms of the signed curve areas of the three
nondegenerate pieces of its boundary traversal: the middle corner path, and the two inner
contact curves, which the traversal runs backwards. -/
theorem gerver_capNiche_area_eq (K : SpecialCapSpace)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2)) :
    ClassicalResults.area (capNiche K.val) =
      curveAreaFunctional (capMiddleBV K) - curveAreaFunctional gerverRightContactBV -
        curveAreaFunctional gerverLeftContactBV := by
  obtain ⟨-, hGeq, -, -, hcapeq, -, -⟩ := gerver_capSupport_identification
  have hcarrier : (K.val.val : Set Point) = gerverOuterCap := by rw [hK, hGeq, hcapeq]
  obtain ⟨K₃, hK₃set, Γ, hΓ, -, -, -, harea, -, -, -⟩ := gerver_niche_orientation
  have h3eq : K₃ = K.val := Subtype.ext (SetLike.coe_injective (hK₃set.trans hcarrier.symm))
  subst h3eq
  rw [← harea]
  exact curveAreaFunctional_gerverNicheBoundary K
    (fun _ ht ↦ capInnerCorner_eq_paperGerverPath K.val hK ht) hΓ

/-! ## The value of `Q` at Gerver's cap -/

theorem gerver_upperBoundQ_matches (X : CapTailSpace)
    (hK : (X.cap.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (X.rightBody : Set Point) = (canonicalTailSets X.cap).1)
    (hD : (X.leftBody : Set Point) = (canonicalTailSets X.cap).2) :
    rightAngleAreaFunctional X.cap.val = upperBoundQ X := by
  obtain ⟨-, -, hxL, hYD, -, hparamD, hxR, hXB, -, hparamB, -, -⟩ :=
    gerver_tailGeometry X.cap X.rightBody X.leftBody hK hB hD
  obtain ⟨hltB, -, hinjB, himgB, hstartB, hendB⟩ := hparamB
  obtain ⟨hltD, -, hinjD, himgD, hstartD, hendD⟩ := hparamD
  -- ### The two tail arcs carry the curve areas of the two inner contact curves
  have hareaB : convexArcArea X.rightBody (Real.pi + paperGerverConstants.2.1)
      (3 * Real.pi / 2) = curveAreaFunctional gerverRightContactBV :=
    convexArcArea_eq_curveAreaFunctional_of_injOn gerverRightContactBV hltB
      gerverRightContactBV_apply hinjB himgB hstartB hendB
  have hareaD : convexArcArea X.leftBody (3 * Real.pi / 2)
      (3 * Real.pi / 2 + paperGerverConstants.2.2) = curveAreaFunctional gerverLeftContactBV :=
    convexArcArea_eq_curveAreaFunctional_of_injOn gerverLeftContactBV hltD
      gerverLeftContactBV_apply hinjD himgD hstartD hendD
  -- ### Both connector segments have coincident endpoints, hence vanishing signed area
  have hsegL : segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
      (distinguishedCapSides X.cap.val).2.corner = 0 := by
    rw [hYD, hxL, segmentArea, planeCrossProduct]; ring
  have hsegR : segmentArea (distinguishedCapSides X.cap.val).1.corner
      (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint = 0 := by
    rw [hxR, hXB, segmentArea, planeCrossProduct]; ring
  simp only [rightAngleAreaFunctional, capAreaFunctional, upperBoundQ]
  rw [hareaB, hareaD, hsegL, hsegR, gerver_capNiche_area_eq X.cap hK]
  ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The variation of `𝒬` at Gerver's cap is nonpositive

At the Gerver base triple the tail geometry identifies the two tail endpoints with the two cap
corners, so `upperBoundQ_variation` presents the derivative as `qVariationIntegral`.  Two of its
four integration windows are larger than the two active tail windows, and the excess is null:
on `(φᴿ, π/2 - θ)` one and the same contact point supports the right tail at both endpoint
normals, and likewise for the left tail on `(π/2 + θ, π/2 + φᴸ)`, so
`oppositeSurfaceData_angleImage_Ioo_eq_zero_of_mem_exposedEdge` applies.

The variation integral is therefore the sum of the eight phase contributions
(`qVariationIntegral_eq_phaseSum`), and each of them is nonpositive
(`gerverPhaseContribution_nonpos`) because the tail support sums are exactly `1` on the two active
windows while the competitor's are at most `1`.
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem gerver_upperBoundQ_variation (X Y : CapTailSpace)
    (hK : (X.cap.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (X.rightBody : Set Point) = (canonicalTailSets X.cap).1)
    (hD : (X.leftBody : Set Point) = (canonicalTailSets X.cap).2) :
    convexDirectionalDerivative capTailCombination upperBoundQ X Y ≤ 0 := by
  have horder := gerverStageTimes_strictMono
  have h01 := horder (show (0 : Fin 6) < 1 by decide)
  have h02 := horder (show (0 : Fin 6) < 2 by decide)
  have h13 := horder (show (1 : Fin 6) < 3 by decide)
  have h24 := horder (show (2 : Fin 6) < 4 by decide)
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hr : paperGerverConstants.2.1 = GerversSofa.φ := rfl
  have ht2 : gerverStageTimes 2 = GerversSofa.θ := by simp [gerverStageTimes]
  have ht3 : gerverStageTimes 3 = Real.pi / 2 - GerversSofa.θ := by simp [gerverStageTimes]
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h02 h13 h24
  obtain ⟨-, -, hLcorner, hLend, hDvert, -, hRcorner, hRstart, hBvert, -, hsumD, hsumB⟩ :=
    gerver_tailGeometry X.cap X.rightBody X.leftBody hK hB hD
  -- ### The general variation formula applies at this base triple
  rw [upperBoundQ_variation X Y (hRstart.trans hRcorner.symm) (hLend.trans hLcorner.symm)]
  -- ### The right tail carries no surface measure between its two active windows
  have hinactiveB : (oppositeSurfaceData X.rightBody).1 ((fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo paperGerverConstants.2.1 (Real.pi / 2 - GerversSofa.θ)) = 0 := by
    refine oppositeSurfaceData_angleImage_Ioo_eq_zero_of_mem_exposedEdge X.rightBody
      (p := paperGerverContacts (gerverStageTimes 3) 1) h13 (by rw [hr]; linarith) ?_ ?_
    · have h : paperGerverContacts (gerverStageTimes 3) 1 =
          (edgeVertices X.rightBody
            ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 := hRstart.symm
      rw [h, show ((paperGerverConstants.2.1 + Real.pi : ℝ) : Real.Angle) =
        ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) from by congr 1; ring]
      exact edgeVertices_fst_mem _ _
    · have h : paperGerverContacts (gerverStageTimes 3) 1 =
          (edgeVertices X.rightBody
            ((Real.pi + gerverStageTimes 3 : ℝ) : Real.Angle)).2 := by rw [hBvert]
      rw [h, show ((Real.pi / 2 - GerversSofa.θ + Real.pi : ℝ) : Real.Angle) =
        ((Real.pi + gerverStageTimes 3 : ℝ) : Real.Angle) from by rw [ht3]; congr 1; ring]
      exact edgeVertices_snd_mem _ _
  -- ### The left tail carries no surface measure between its two active windows
  have hinactiveD : (oppositeSurfaceData X.leftBody).1 ((fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo (Real.pi / 2 + GerversSofa.θ)
        (Real.pi / 2 + paperGerverConstants.2.2)) = 0 := by
    have hlt : Real.pi / 2 + GerversSofa.θ < Real.pi / 2 + paperGerverConstants.2.2 := by
      change Real.pi / 2 + GerversSofa.θ < Real.pi / 2 + (Real.pi / 2 - GerversSofa.φ)
      linarith
    refine oppositeSurfaceData_angleImage_Ioo_eq_zero_of_mem_exposedEdge X.leftBody
      (p := paperGerverContacts (gerverStageTimes 2) 3) hlt (by
        change Real.pi / 2 + (Real.pi / 2 - GerversSofa.φ) <
          Real.pi / 2 + GerversSofa.θ + Real.pi
        linarith) ?_ ?_
    · have h : paperGerverContacts (gerverStageTimes 2) 3 =
          (edgeVertices X.leftBody
            ((3 * Real.pi / 2 + gerverStageTimes 2 : ℝ) : Real.Angle)).1 := by rw [hDvert]
      rw [h, show ((Real.pi / 2 + GerversSofa.θ + Real.pi : ℝ) : Real.Angle) =
        ((3 * Real.pi / 2 + gerverStageTimes 2 : ℝ) : Real.Angle) from by
          rw [ht2]; congr 1; ring]
      exact edgeVertices_fst_mem _ _
    · have h : paperGerverContacts (gerverStageTimes 2) 3 =
          (edgeVertices X.leftBody
            ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 := hLend.symm
      rw [h, show ((Real.pi / 2 + paperGerverConstants.2.2 + Real.pi : ℝ) : Real.Angle) =
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) from by congr 1; ring]
      exact edgeVertices_snd_mem _ _
  -- ### On the two active windows the base support sums are exactly one
  have hbaseB : ∀ t ∈ gerverPhaseAngles 3 ∪ gerverPhaseAngles 4,
      supportValue X.cap.val.val t + (oppositeSurfaceData X.rightBody).2 t = 1 := by
    intro t ht
    rw [gerverPhaseAngles_three_union_four] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have h := hsumB s (by rw [ht3]; exact ⟨hs.1, hs.2.le⟩)
    simp only [oppositeSurfaceData]
    rw [show ((s : Real.Angle) + ((Real.pi : ℝ) : Real.Angle)) =
      ((Real.pi + s : ℝ) : Real.Angle) from by rw [← Real.Angle.coe_add]; congr 1; ring]
    exact h
  have hbaseD : ∀ t ∈ gerverPhaseAngles 5 ∪ gerverPhaseAngles 6,
      supportValue X.cap.val.val t + (oppositeSurfaceData X.leftBody).2 t = 1 := by
    intro t ht
    rw [gerverPhaseAngles_five_union_six] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have h := hsumD (u - Real.pi / 2) (by
      rw [gerverStageTimes_zero, ht2]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    rw [show ((Real.pi / 2 + (u - Real.pi / 2) : ℝ) : Real.Angle) = (u : Real.Angle) from by
      congr 1; ring] at h
    simp only [oppositeSurfaceData]
    rw [show ((u : Real.Angle) + ((Real.pi : ℝ) : Real.Angle)) =
      ((3 * Real.pi / 2 + (u - Real.pi / 2) : ℝ) : Real.Angle) from by
      rw [← Real.Angle.coe_add]; congr 1; ring]
    exact h
  -- ### Each of the eight phase contributions is nonpositive
  rw [qVariationIntegral_eq_phaseSum X Y hinactiveB hinactiveD]
  exact Finset.sum_nonpos fun i _ ↦ gerverPhaseContribution_nonpos X Y
    (gerver_phaseMeasures X.cap X.rightBody X.leftBody hK hB hD) hbaseB hbaseD i

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Bounds.Upper.Properties`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Bounds / Upper / Properties
-/

public section

noncomputable section

namespace MovingSofa

theorem upperBoundQ_quadratic_concave :
    IsQuadraticFunctional capTailCombination upperBoundQ ∧
      IsConvexFunctional capTailCombination upperBoundQ true := by
  obtain ⟨hcomb, -⟩ := capTail_isConvexDomain
  obtain ⟨hmidConv, hmidQuad, hrConv, hrQuad, hlConv, hlQuad⟩ := sofaMamikon_quadratic_convex
  -- ### The three coordinate projections preserve the interpolation
  have hcapval : ∀ t X Y, (capTailCombination t X Y).cap = specialCapCombination t X.cap Y.cap :=
    fun t X Y ↦ Subtype.ext (Subtype.ext
      ((hcomb t X Y).1.trans (specialCap_isConvexDomain.1 t X.cap Y.cap).symm))
  have hcap : IsConvexLinear capTailCombination specialCapCombination
      fun X : CapTailSpace ↦ X.cap := hcapval
  have hright : IsConvexLinear capTailCombination convexBodyCombination
      fun X : CapTailSpace ↦ X.rightBody := fun t X Y ↦ (hcomb t X Y).2.1
  have hleft : IsConvexLinear capTailCombination convexBodyCombination
      fun X : CapTailSpace ↦ X.leftBody := fun t X Y ↦ (hcomb t X Y).2.2
  -- ### The middle equivalence exhibits the affine part of the cap term
  have hAlin : IsConvexLinear capTailCombination realCombination
      fun X : CapTailSpace ↦ middleMamikon X.cap + upperBoundMiddle X.cap := by
    intro t X Y
    have h := middleMamikon_equivalent_neg_upperBoundMiddle t X.cap Y.cap
    simp only [sub_neg_eq_add, realCombination] at h
    change middleMamikon (capTailCombination t X Y).cap +
      upperBoundMiddle (capTailCombination t X Y).cap = realCombination t _ _
    rw [hcapval t X Y]
    simp only [realCombination]
    linarith
  -- ### The exact decomposition, with the cap term split as affine minus convex
  have hQ : upperBoundQ = fun X : CapTailSpace ↦
      ((middleMamikon X.cap + upperBoundMiddle X.cap + -middleMamikon X.cap) +
        -rightTailMamikon X.rightBody) + -leftTailMamikon X.leftBody := by
    funext X
    rw [upperBoundQ_decomposition X]
    ring
  rw [hQ]
  exact ⟨((hAlin.isQuadraticFunctional.add (hmidQuad.comp_isConvexLinear hcap).neg).add
        (hrQuad.comp_isConvexLinear hright).neg).add (hlQuad.comp_isConvexLinear hleft).neg,
    (((hAlin.isConvexFunctional true).add (hmidConv.comp_isConvexLinear hcap).neg).add
        (hrConv.comp_isConvexLinear hright).neg).add (hlConv.comp_isConvexLinear hleft).neg⟩

/-- The right tail's initial vertex, the right fan point and the right inner corner all lie on the
right distinguished inner wall `b_K(φᴿ)`, so the two signed segment areas along it add. -/
private theorem segmentArea_add_segmentArea_rightWall (X : CapTailSpace) :
    segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
        (distinguishedCapSides X.cap.val).1.fanPoint +
      segmentArea (distinguishedCapSides X.cap.val).1.fanPoint
        (distinguishedCapSides X.cap.val).1.corner =
    segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
      (distinguishedCapSides X.cap.val).1.corner := by
  obtain ⟨hrIoo, -, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hcosr : 0 < Real.cos paperGerverConstants.2.1 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrIoo.1], hrIoo.2⟩
  have hXBdef : (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint =
      (edgeVertices X.rightBody ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 := rfl
  have hWdef : (distinguishedCapSides X.cap.val).1.fanPoint =
      (wedgeEndpoints X.cap.val paperGerverConstants.2.1).1 := rfl
  have hxRdef : (distinguishedCapSides X.cap.val).1.corner =
      capInnerCorner X.cap.val paperGerverConstants.2.1 := rfl
  have hXB : inner ℝ
      (edgeVertices X.rightBody ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1
      (normalVector ((paperGerverConstants.2.1 : ℝ) : Real.Angle)) =
      supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1 := by
    have hmem : inner ℝ
        (edgeVertices X.rightBody ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1
        (normalVector ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)) =
        supportValue (X.rightBody : Set Point)
          ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) :=
      (edgeVertices_fst_mem X.rightBody _).2
    have hneg : normalVector ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) =
        -normalVector ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
      rw [show (Real.pi + paperGerverConstants.2.1 : ℝ) =
        paperGerverConstants.2.1 + Real.pi from by ring]
      exact normalVector_add_pi _
    rw [hneg, inner_neg_right] at hmem
    have heq := X.right_eq paperGerverConstants.2.1 (by simp)
    linarith
  have hW : inner ℝ (wedgeEndpoints X.cap.val paperGerverConstants.2.1).1
      (normalVector ((paperGerverConstants.2.1 : ℝ) : Real.Angle)) =
      supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1 := by
    change inner ℝ (((supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) /
        Real.cos paperGerverConstants.2.1) • normalVector 0)
        (normalVector ((paperGerverConstants.2.1 : ℝ) : Real.Angle)) = _
    have h0 : normalVector (0 : Real.Angle) 0 = 1 := by simp [normalVector, frame]
    have h1 : normalVector (0 : Real.Angle) 1 = 0 := by simp [normalVector, frame]
    rw [real_inner_smul_left, inner_normalVector_real, h0, h1, one_mul, zero_mul, add_zero,
      div_mul_cancel₀ _ hcosr.ne']
  rw [hXBdef, hWdef, hxRdef]
  linarith [segmentArea_sub_segmentArea_of_inner_normalVector_eq hXB hW
    (inner_capInnerCorner_normalVector X.cap.val paperGerverConstants.2.1)]

/-- The left inner corner, the left fan point and the left tail's final vertex all lie on the
left distinguished inner wall `d_K(φᴸ)`, so the two signed segment areas along it add. -/
private theorem segmentArea_add_segmentArea_leftWall (X : CapTailSpace) :
    segmentArea (distinguishedCapSides X.cap.val).2.corner
        (distinguishedCapSides X.cap.val).2.fanPoint +
      segmentArea (distinguishedCapSides X.cap.val).2.fanPoint
        (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint =
    segmentArea (distinguishedCapSides X.cap.val).2.corner
      (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint := by
  obtain ⟨-, hlIoo, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hsinl : 0 < Real.sin paperGerverConstants.2.2 :=
    Real.sin_pos_of_pos_of_lt_pi hlIoo.1 (by linarith [Real.pi_pos, hlIoo.2])
  have hZdef : (distinguishedCapSides X.cap.val).2.fanPoint =
      (wedgeEndpoints X.cap.val paperGerverConstants.2.2).2 := rfl
  have hxLdef : (distinguishedCapSides X.cap.val).2.corner =
      capInnerCorner X.cap.val paperGerverConstants.2.2 := rfl
  have hYDdef : (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint =
      (edgeVertices X.leftBody
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 := rfl
  have hxL : inner ℝ (capInnerCorner X.cap.val paperGerverConstants.2.2)
      (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    rw [normalVector_add_pi_div_two_real]
    exact inner_capInnerCorner_tangentVector X.cap.val paperGerverConstants.2.2
  have hZ : inner ℝ (wedgeEndpoints X.cap.val paperGerverConstants.2.2).2
      (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    change inner ℝ (((supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
        Real.cos (Real.pi / 2 - paperGerverConstants.2.2)) •
        tangentVector ((Real.pi / 2 : ℝ) : Real.Angle))
        (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [real_inner_smul_left, inner_tangentVector_normalVector_real,
      show paperGerverConstants.2.2 + Real.pi / 2 - Real.pi / 2 = paperGerverConstants.2.2 from
        by ring, Real.cos_pi_div_two_sub, div_mul_cancel₀ _ hsinl.ne']
  have hYD : inner ℝ (edgeVertices X.leftBody
      ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2
      (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue (X.cap.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    have hmem : inner ℝ (edgeVertices X.leftBody
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2
        (normalVector ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)) =
        supportValue (X.leftBody : Set Point)
          ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) :=
      (edgeVertices_snd_mem X.leftBody _).2
    have hneg : normalVector ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
        -normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [show (3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) =
        paperGerverConstants.2.2 + Real.pi / 2 + Real.pi from by ring]
      exact normalVector_add_pi _
    rw [hneg, inner_neg_right] at hmem
    have heq := X.left_eq paperGerverConstants.2.2 (by simp)
    rw [show (Real.pi / 2 + paperGerverConstants.2.2 : ℝ) =
      paperGerverConstants.2.2 + Real.pi / 2 from by ring] at heq
    linarith
  rw [hZdef, hxLdef, hYDdef]
  linarith [segmentArea_sub_segmentArea_of_inner_normalVector_eq hxL hZ hYD]

theorem areaFunctional_le_upperBoundQ (X : CapTailSpace)
    (hB : (X.rightBody : Set Point) = (canonicalTailSets X.cap).1)
    (hD : (X.leftBody : Set Point) = (canonicalTailSets X.cap).2) :
    rightAngleAreaFunctional X.cap.val ≤ upperBoundQ X := by
  have hsplit := (niche_three_regions_area X.cap _ _ _ rfl rfl rfl).2.2.2.2.2.2.2.2.2.2
  have hmid := capMiddle_area_lower_bound X.cap
  rw [Set.sdiff_sdiff] at hmid
  obtain ⟨hrightTail, hleftTail⟩ :=
    canonicalTail_niche_area_lower_bounds X.cap X.rightBody X.leftBody hB hD
  have hwallR := segmentArea_add_segmentArea_rightWall X
  have hwallL := segmentArea_add_segmentArea_leftWall X
  have hswapR := segmentArea_swap (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
    (distinguishedCapSides X.cap.val).1.corner
  have hswapL := segmentArea_swap (distinguishedCapSides X.cap.val).2.corner
    (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
  simp only [rightAngleAreaFunctional, capAreaFunctional, upperBoundQ]
  linarith

theorem gerver_upperBoundQ_maximum :
    ∃ X : CapTailSpace,
      (X.cap.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2) ∧
      (X.rightBody : Set Point) = (canonicalTailSets X.cap).1 ∧
      (X.leftBody : Set Point) = (canonicalTailSets X.cap).2 ∧
      ∀ Y : CapTailSpace, upperBoundQ Y ≤ upperBoundQ X := by
  -- ### The special-cap space contains Gerver's cap, and the canonical tails extend it to `𝓛`
  obtain ⟨K, hK⟩ := specialCap_isConvexDomain.2.2.2
  obtain ⟨X, hXcap, hB, hD⟩ := exists_canonicalCapTail K
  subst K
  refine ⟨X, hK, hB, hD, ?_⟩
  -- ### `𝒬` is quadratic and concave, so nonpositive variation is exactly maximality
  obtain ⟨hquad, hconcave⟩ := upperBoundQ_quadratic_concave
  exact (quadratic_maximum_iff capTailCombination capTail_isConvexDomain.2 upperBoundQ hquad
    hconcave X).mpr fun Y ↦ gerver_upperBoundQ_variation X Y hK hB hD

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Sofa.Balanced`.
* `Sofa.BalancedConsumed`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Sofa / Balanced
-/

public section

noncomputable section

namespace MovingSofa

/-- A monotonized standard-position sofa whose associated cap is a balanced maximum cap. -/
def IsBalancedMaximumSofa (s : Set Point) (ω : ℝ) : Prop :=
  (∃ s₀ : Set Point, IsStandardPosition s₀ ω ∧ s = monotonization s₀ ω) ∧
    ∃ K : CapSpace ω, (K.val : Set Point) = capOfSofa s ω ∧ IsBalancedMaximumCap K

theorem exists_balancedMaximumSofa (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) :
    ∃ K : CapSpace ω, IsBalancedMaximumCap K ∧
      IsBalancedMaximumSofa ((K.val : Set Point) \ capNiche K) ω ∧
      ∀ s : Set Point, HasRotationAngle s ω →
        ClassicalResults.area s ≤ ClassicalResults.area ((K.val : Set Point) \ capNiche K) := by
  obtain ⟨K, hK⟩ := exists_balancedMaximumCap ω hω hω'
  obtain ⟨s₀, hs₀, hcap⟩ := (cap_isMonotoneCap_iff_niche_subset K).mpr
    (balancedMaximumCap_niche_subset K hK)
  have hshape := monotoneSofa_structure (monotonization s₀ ω) ω ⟨s₀, hs₀, rfl⟩ K hcap
  have hmonoS : ∃ s₀ : Set Point, IsStandardPosition s₀ ω ∧
      (K.val : Set Point) \ capNiche K = monotonization s₀ ω := ⟨s₀, hs₀, hshape.symm⟩
  have hcapS : (K.val : Set Point) = capOfSofa ((K.val : Set Point) \ capNiche K) ω := by
    rwa [← hshape]
  have hareaK := capAreaFunctional_eq_sofaArea _ ω hmonoS K hcapS
  refine ⟨K, hK, ⟨hmonoS, K, hcapS, hK⟩, ?_⟩
  intro s hs
  obtain ⟨v, hv⟩ := (exists_standardPosition_translation s ω hs ⟨hω, hω'⟩).1
  let s₁ := (fun p ↦ p + v) '' s
  have hstd := standardPosition_monotonization_standard s₁ ω hv
  obtain ⟨L, hL⟩ := standardPosition_cap (monotonization s₁ ω) ω hstd.1
  calc
    ClassicalResults.area s = ClassicalResults.area s₁ :=
      (ClassicalResults.area_image_add s v).symm
    _ ≤ ClassicalResults.area (monotonization s₁ ω) :=
      MeasureTheory.measureReal_mono hstd.2 hstd.1.1.measure_lt_top.ne
    _ = capAreaFunctional L :=
      (capAreaFunctional_eq_sofaArea _ ω ⟨s₁, hv, rfl⟩ L hL).symm
    _ ≤ capAreaFunctional K := balancedMaximumCap_maximizes_area K hK L
    _ = _ := hareaK

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Sofa / Balanced Consumed
-/

public section

noncomputable section

namespace MovingSofa

/-- The right wedge gap is bounded below by the calculation variable `g`. -/
private theorem le_wedgeGaps_fst_of_calculationVariables {ω : ℝ} (K : CapSpace ω)
    (hω' : ω < Real.pi / 2) {c d r g : ℝ}
    (hccos : c * Real.cos ω = 1 - Real.sin ω)
    (hsupp : supportValue K.val (0 : Real.Angle) = c + d)
    (hrsin : r * Real.sin ω = Real.sin ω - d * Real.cos ω)
    (hgsq : g ^ 2 = 1 - r ^ 2)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 ω) :
    g ≤ (wedgeGaps K t).1 := by
  have hpi := Real.pi_pos
  have hω0 : 0 < ω := K.property.1
  have hcos : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith, hω'⟩
  have hsin : 0 < Real.sin ω := Real.sin_pos_of_pos_of_lt_pi hω0 (by linarith)
  have hcost : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsint : 0 ≤ Real.sin t := (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2])).le
  have hsinδ : 0 ≤ Real.sin ω * Real.cos t - Real.cos ω * Real.sin t := by
    rw [← Real.sin_sub]
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1])).le
  have hcs : r * Real.sin t + g * Real.cos t ≤ 1 := by
    nlinarith [sq_nonneg (r - Real.sin t), sq_nonneg (g - Real.cos t),
      Real.sin_sq_add_cos_sq t]
  -- the support value at `t` is bounded by the value at the intersection point `R`
  have hbound : Real.sin ω * supportValue K.val (t : Real.Angle) ≤
      Real.sin (ω - t) * (c + d) + Real.sin t := by
    rw [mul_comm, ← le_div_iff₀ hsin]
    apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hx : p 0 ≤ c + d := by
      rw [← hsupp]
      simpa [normalVector, frame, PiLp.inner_apply] using
        inner_le_supportValue K.val hp (0 : Real.Angle)
    have hu : Real.cos ω * p 0 + Real.sin ω * p 1 ≤ 1 := by
      have hle := inner_le_supportValue K.val hp (ω : Real.Angle)
      rw [K.property.2.2.1] at hle
      simpa [normalVector, frame, PiLp.inner_apply] using hle
    have hval : inner ℝ p (normalVector (t : Real.Angle)) =
        Real.cos t * p 0 + Real.sin t * p 1 := by
      simp [normalVector, frame, PiLp.inner_apply]
    simp only [le_div_iff₀ hsin, hval, Real.sin_sub]
    nlinarith [mul_nonneg hsinδ (sub_nonneg.2 hx), mul_nonneg hsint (sub_nonneg.2 hu)]
  have hRu : Real.sin ω * ((c + d) * Real.cos t + r * Real.sin t) =
      Real.sin (ω - t) * (c + d) + Real.sin t := by
    rw [Real.sin_sub]
    linear_combination Real.sin t * hrsin + Real.sin t * hccos
  have hSle : supportValue K.val (t : Real.Angle) ≤ (c + d) * Real.cos t + r * Real.sin t := by
    rw [← hRu] at hbound
    exact le_of_mul_le_mul_left hbound hsin
  have hkey : supportValue K.val (t : Real.Angle) - 1 ≤ (c + d - g) * Real.cos t := by
    nlinarith
  rw [wedgeGaps_fst_eq_supportValue, hsupp, ← sub_nonneg]
  have := (div_le_iff₀ hcost).2 hkey
  linarith

/-- The exposed top face of a cap contains the horizontal segment of its own atomic
surface mass, measured leftwards from the upper distinguished point. -/
private theorem topFace_sub_smul_normalVector_mem {ω : ℝ} (K : CapSpace ω)
    (ho : (stripParallelogram ω).2.2 ∈ (K.val : Set Point)) {c g : ℝ}
    (hccos : c * Real.cos ω = 1 - Real.sin ω)
    (hcoord : (stripParallelogram ω).2.2 = !₂[c, 1]) (hcos : 0 < Real.cos ω)
    (hgnn : 0 ≤ g)
    (hg : g ≤ (surfaceAreaMeasure K.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal) :
    (stripParallelogram ω).2.2 - g • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) := by
  have hT1 : supportValue K.val ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := K.property.2.2.2.1
  have htan : tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) = -normalVector (0 : Real.Angle) := by
    ext i
    fin_cases i <;> simp [tangentVector, normalVector, frame]
  have hface : ∀ p ∈ exposedEdge K.val ((Real.pi / 2 : ℝ) : Real.Angle), p 1 = 1 ∧ p 0 ≤ c := by
    intro p hp
    have hpe : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue K.val ((Real.pi / 2 : ℝ) : Real.Angle) := hp.2
    rw [hT1] at hpe
    have h1 : p 1 = 1 := by simpa [normalVector, frame, PiLp.inner_apply] using hpe
    refine ⟨h1, ?_⟩
    have hle := inner_le_supportValue K.val hp.1 (ω : Real.Angle)
    rw [K.property.2.2.1] at hle
    simp [normalVector, frame, PiLp.inner_apply, h1] at hle
    nlinarith
  have hoedge : (stripParallelogram ω).2.2 ∈
      exposedEdge K.val ((Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨ho, ?_⟩
    change inner ℝ (stripParallelogram ω).2.2 (normalVector _) = _
    rw [hT1, hcoord]
    simp [normalVector, frame, PiLp.inner_apply]
  have hsnd := edgeVertices_snd_mem K.val ((Real.pi / 2 : ℝ) : Real.Angle)
  have hsndle : inner ℝ (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2
      (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
      inner ℝ (stripParallelogram ω).2.2 (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) := by
    rw [inner_edgeVertices_snd_tangent]
    refine csInf_le ?_ ⟨_, hoedge, rfl⟩
    exact ((isCompact_exposedEdge K.val _).image (continuous_id.inner continuous_const)).bddBelow
  have hsndeq : (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 =
      (stripParallelogram ω).2.2 := by
    obtain ⟨hy, hx⟩ := hface _ hsnd
    have hocx : inner ℝ (stripParallelogram ω).2.2
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) = -c := by
      rw [htan, inner_neg_right, hcoord]
      simp [normalVector, frame, PiLp.inner_apply]
    have hvx : inner ℝ (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        -(edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 0 := by
      rw [htan, inner_neg_right]
      simp [normalVector, frame, PiLp.inner_apply]
    rw [hocx, hvx] at hsndle
    have hx0 : (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 0 = c := by linarith
    rw [hcoord]
    ext i
    fin_cases i
    · simpa using hx0
    · simpa using hy
  obtain ⟨L, hL⟩ : ∃ L, (surfaceAreaMeasure K.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal = L :=
    ⟨_, rfl⟩
  rw [hL] at hg
  have hatom := surfaceAreaMeasure_atom_length K.val ((Real.pi / 2 : ℝ) : Real.Angle)
  rw [hL] at hatom
  have hfstK : (stripParallelogram ω).2.2 - L • normalVector (0 : Real.Angle) ∈
      (K.val : Set Point) := by
    rw [show (stripParallelogram ω).2.2 - L • normalVector (0 : Real.Angle) =
        (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).1 from by
      rw [hatom.2.2, hsndeq, htan, smul_neg, ← sub_eq_add_neg]]
    exact (edgeVertices_fst_mem K.val _).1
  rcases eq_or_lt_of_le (hgnn.trans hg) with hL0 | hLpos
  · have hg0 : g = 0 := le_antisymm (hg.trans hL0.symm.le) hgnn
    simpa [hg0] using ho
  · have hkey := K.val.convex ho hfstK (a := 1 - g / L) (b := g / L)
      (by
        have : g / L ≤ 1 := (div_le_one hLpos).2 hg
        linarith)
      (div_nonneg hgnn hLpos.le) (by ring)
    have hsmul : (1 - g / L) • (stripParallelogram ω).2.2 +
        (g / L) • ((stripParallelogram ω).2.2 - L • normalVector (0 : Real.Angle)) =
        (stripParallelogram ω).2.2 - g • normalVector (0 : Real.Angle) := by
      rw [smul_sub, smul_smul, div_mul_cancel₀ _ hLpos.ne']
      module
    rwa [hsmul] at hkey

/-- The three distinguished points lie in the inward quadrant at the angle `π / 2 - ω`
once the two contact points realize the strict calculation inequalities. -/
private theorem consumed_points_subset_innerQuadrant {ω : ℝ} (K : CapSpace ω)
    (hω4 : Real.pi / 4 < ω) (hω' : ω < Real.pi / 2) {c : ℝ} (hcpos : 0 < c)
    (hc0 : (stripParallelogram ω).2.2 - tangentVector 0 = c • normalVector (0 : Real.Angle))
    (hcω : (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) =
      c • tangentVector (ω : Real.Angle))
    {p q : Point} (hp : p ∈ (K.val : Set Point)) (hq : q ∈ (K.val : Set Point))
    (h1 : 1 < inner ℝ (p - ((stripParallelogram ω).2.2 - tangentVector 0))
      (normalVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)))
    (h2 : 1 < inner ℝ (q - ((stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)))
      (tangentVector ((Real.pi / 2 - ω : ℝ) : Real.Angle))) :
    ({0, (stripParallelogram ω).2.2 - tangentVector 0,
      (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)} : Set Point) ⊆
      innerQuadrant (K.val : Set Point) (Real.pi / 2 - ω) := by
  have hpi := Real.pi_pos
  have hcos : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith, hω'⟩
  have hsin : 0 < Real.sin ω := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcslt : Real.cos ω < Real.sin ω := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.strictMonoOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hnt : normalVector ((Real.pi / 2 - ω + Real.pi / 2 : ℝ) : Real.Angle) =
      tangentVector ((Real.pi / 2 - ω : ℝ) : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [normalVector, tangentVector, frame, Real.cos_add, Real.sin_add,
        -Real.Angle.coe_sub, -Real.Angle.coe_add]
  have hnn : inner ℝ (normalVector (0 : Real.Angle))
      (normalVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)) = Real.sin ω := by
    simp [normalVector, frame, PiLp.inner_apply, Real.cos_pi_div_two_sub, -Real.Angle.coe_sub]
  have hnt' : inner ℝ (normalVector (0 : Real.Angle))
      (tangentVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)) = -Real.cos ω := by
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Real.sin_pi_div_two_sub,
      -Real.Angle.coe_sub]
  have htn : inner ℝ (tangentVector (ω : Real.Angle))
      (normalVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)) =
      Real.cos ω ^ 2 - Real.sin ω ^ 2 := by
    simp [tangentVector, normalVector, frame, PiLp.inner_apply, Real.cos_pi_div_two_sub,
      Real.sin_pi_div_two_sub, -Real.Angle.coe_sub]
    ring
  have htt : inner ℝ (tangentVector (ω : Real.Angle))
      (tangentVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)) =
      2 * (Real.sin ω * Real.cos ω) := by
    simp [tangentVector, frame, PiLp.inner_apply, Real.cos_pi_div_two_sub,
      Real.sin_pi_div_two_sub, -Real.Angle.coe_sub]
    ring
  have hA := inner_le_supportValue K.val hp ((Real.pi / 2 - ω : ℝ) : Real.Angle)
  have hB := inner_le_supportValue K.val hq ((Real.pi / 2 - ω + Real.pi / 2 : ℝ) : Real.Angle)
  rw [hnt] at hB
  have hstrict1 : c * Real.sin ω <
      supportValue K.val ((Real.pi / 2 - ω : ℝ) : Real.Angle) - 1 := by
    rw [inner_sub_left, hc0, real_inner_smul_left, hnn] at h1
    linarith
  have hstrict2 : c * (2 * (Real.sin ω * Real.cos ω)) <
      supportValue K.val ((Real.pi / 2 - ω + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    rw [inner_sub_left, hcω, real_inner_smul_left, htt] at h2
    linarith
  have hmem : ∀ x : Point,
      inner ℝ x (normalVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)) <
        supportValue K.val ((Real.pi / 2 - ω : ℝ) : Real.Angle) - 1 →
      inner ℝ x (tangentVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)) <
        supportValue K.val ((Real.pi / 2 - ω + Real.pi / 2 : ℝ) : Real.Angle) - 1 →
      x ∈ innerQuadrant (K.val : Set Point) (Real.pi / 2 - ω) := by
    intro x hx1 hx2
    refine ⟨hx1, ?_⟩
    change inner ℝ x (normalVector ((Real.pi / 2 - ω + Real.pi / 2 : ℝ) : Real.Angle)) < _
    rwa [hnt]
  have hpos1 : 0 < c * Real.sin ω := mul_pos hcpos hsin
  have hpos2 : 0 < c * (2 * (Real.sin ω * Real.cos ω)) := by
    have := mul_pos hsin hcos
    nlinarith
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hmem _ (by rw [inner_zero_left]; linarith) (by rw [inner_zero_left]; linarith)
  · refine hmem _ ?_ ?_
    · rw [hc0, real_inner_smul_left, hnn]
      exact hstrict1
    · rw [hc0, real_inner_smul_left, hnt']
      nlinarith
  · refine hmem _ ?_ ?_
    · rw [hcω, real_inner_smul_left, htn]
      have hneg : c * (Real.cos ω ^ 2 - Real.sin ω ^ 2) < 0 :=
        mul_neg_of_pos_of_neg hcpos (by nlinarith)
      linarith
    · rw [hcω, real_inner_smul_left, htt]
      exact hstrict2

/-- Auxiliary form of the consumption theorem under the right-hand support bound. -/
private theorem consumed_of_le_supportValue_zero {ω : ℝ}
    (hω : Real.arccos (5 / 11 : ℝ) ≤ ω) (hω' : ω < Real.pi / 2)
    (K : CapSpace ω) (hBalanced : IsBalancedMaximumCap K)
    (ho : (stripParallelogram ω).2.2 ∈ (K.val : Set Point))
    (hd : rotationCalculationMinimum ⟨ω, hω, hω'⟩ + Real.tan ((Real.pi / 2 - ω) / 2) ≤
      supportValue K.val (0 : Real.Angle)) :
    ({0, (stripParallelogram ω).2.2 - tangentVector 0,
      (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)} : Set Point) ⊆
      innerQuadrant (K.val : Set Point) (Real.pi / 2 - ω) := by
  have hpi := Real.pi_pos
  have hω4 : Real.pi / 4 < ω := rotationCalculation_angle_bounds.1.trans_le hω
  have hω0 : 0 < ω := by linarith
  have hcos : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith, hω'⟩
  have hsin : 0 < Real.sin ω := Real.sin_pos_of_pos_of_lt_pi hω0 (by linarith)
  have hgap := parallelogram_gap ω ⟨hω0.le, hω'⟩
  have hcpos : 0 < Real.tan ((Real.pi / 2 - ω) / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have hccos : Real.tan ((Real.pi / 2 - ω) / 2) * Real.cos ω = 1 - Real.sin ω := by
    rw [hgap.2.2.2.2, Real.tan_eq_sin_div_cos]
    field_simp
  obtain ⟨d, hsupp⟩ : ∃ d, supportValue K.val (0 : Real.Angle) =
      Real.tan ((Real.pi / 2 - ω) / 2) + d :=
    ⟨supportValue K.val (0 : Real.Angle) - Real.tan ((Real.pi / 2 - ω) / 2), by ring⟩
  have hdmin : rotationCalculationMinimum ⟨ω, hω, hω'⟩ ≤ d := by
    rw [hsupp] at hd; linarith
  have hdpos : 0 < d := (rotationCalculationMinimum_pos _).trans_le hdmin
  have hq0K : supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle) ∈
      (K.val : Set Point) := supportValue_zero_smul_normalVector_mem K
  have hdtan : d ≤ Real.tan ω := by
    have hle := inner_le_supportValue K.val hq0K (ω : Real.Angle)
    rw [K.property.2.2.1, real_inner_smul_left] at hle
    have hinner : inner ℝ (normalVector (0 : Real.Angle))
        (normalVector (ω : Real.Angle)) = Real.cos ω := by
      simp [normalVector, frame, PiLp.inner_apply]
    rw [hinner, hsupp] at hle
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hcos]
    linarith
  have hrnn : 0 ≤ (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).1 := by
    change 0 ≤ 1 - d * (Real.cos ω / Real.sin ω)
    rw [sub_nonneg, mul_div_assoc', div_le_one hsin]
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hcos] at hdtan
    exact hdtan
  obtain ⟨r, hr⟩ :
      ∃ r, (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).1 = r := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ :
      ∃ g, (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).2.1 = g := ⟨_, rfl⟩
  have hrval : r = 1 - d * (Real.cos ω / Real.sin ω) := by rw [← hr]; rfl
  have hgval : g = Real.sqrt (1 - r ^ 2) := by rw [← hg, ← hr]; rfl
  have hrnn' : 0 ≤ r := by rw [← hr]; exact hrnn
  have hrle : r ≤ 1 := by
    rw [hrval]
    have := mul_nonneg hdpos.le (div_nonneg hcos.le hsin.le)
    linarith
  have hgnn : 0 ≤ g := by rw [hgval]; exact Real.sqrt_nonneg _
  have hgsq : g ^ 2 = 1 - r ^ 2 := by
    rw [hgval]
    exact Real.sq_sqrt (by nlinarith)
  have hrsin : r * Real.sin ω = Real.sin ω - d * Real.cos ω := by
    rw [hrval]
    field_simp
  -- the wedge-gap infimum, hence the vertical surface atom, is at least `g`
  have hinf : g ≤ (wedgeGapInfimum K).1 := by
    apply le_csInf ((Set.nonempty_Ioo.mpr hω0).image _)
    rintro _ ⟨t, ht, rfl⟩
    exact le_wedgeGaps_fst_of_calculationVariables K hω' hccos hsupp hrsin hgsq ht
  have hsurf := hinf.trans (balancedMaximumCap_gap_le_surface K hBalanced hω').1
  have hcoord : (stripParallelogram ω).2.2 = !₂[Real.tan ((Real.pi / 2 - ω) / 2), 1] := by
    have harg : Real.pi / 4 - ω / 2 = (Real.pi / 2 - ω) / 2 := by ring
    simp only [stripParallelogram, harg]
  have hq1K := topFace_sub_smul_normalVector_mem K ho hccos hcoord hcos hgnn hsurf
  have hineq := rotationCalculation_inequalities ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩ hrnn
  have hP0 : (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).2.2.1 ∈
      (K.val : Set Point) := by
    have hq : (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).2.2.1 =
        (stripParallelogram ω).2.2 - tangentVector 0 + d • normalVector (0 : Real.Angle) := rfl
    rw [hq, hgap.1, ← add_smul, ← hsupp]
    exact hq0K
  have hP1 : (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).2.2.2 ∈
      (K.val : Set Point) := by
    have hq : (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).2.2.2 =
        (stripParallelogram ω).2.2 -
          (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).2.1 •
            normalVector (0 : Real.Angle) := rfl
    rw [hq, hg]
    exact hq1K
  exact consumed_points_subset_innerQuadrant K hω4 hω' hcpos hgap.1 hgap.2.1 hP0 hP1
    hineq.1 hineq.2

theorem balancedMaximumCap_consumed {ω : ℝ} (K : CapSpace ω)
    (hω : Real.arccos (5 / 11 : ℝ) ≤ ω) (hω' : ω < Real.pi / 2)
    (hBalanced : IsBalancedMaximumCap K) (hArea : 11 / 5 ≤ capAreaFunctional K) :
    ∃ t ∈ Set.Ioo 0 ω,
      ({0, (stripParallelogram ω).2.2 - tangentVector 0,
        (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)} : Set Point) ⊆
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerQuadrant := by
  have hpi := Real.pi_pos
  have hω4 : Real.pi / 4 < ω := rotationCalculation_angle_bounds.1.trans_le hω
  have hω0 : 0 < ω := by linarith
  have hcos : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith, hω'⟩
  have hsin : 0 < Real.sin ω := Real.sin_pos_of_pos_of_lt_pi hω0 (by linarith)
  have hgap := parallelogram_gap ω ⟨hω0.le, hω'⟩
  have hccos : Real.tan ((Real.pi / 2 - ω) / 2) * Real.cos ω = 1 - Real.sin ω := by
    rw [hgap.2.2.2.2, Real.tan_eq_sin_div_cos]
    field_simp
  have hcoord : (stripParallelogram ω).2.2 = !₂[Real.tan ((Real.pi / 2 - ω) / 2), 1] := by
    have harg : Real.pi / 4 - ω / 2 = (Real.pi / 2 - ω) / 2 := by ring
    simp only [stripParallelogram, harg]
  -- the upper distinguished point belongs to the limiting cap
  have ho : (stripParallelogram ω).2.2 ∈ (K.val : Set Point) := by
    obtain ⟨n, hn, -, -, P, hmax, hlim⟩ := hBalanced
    exact ConvexBody.mem_of_tendsto_hausdorffDist _ (fun i ↦ (P i).val.val) K.val
      (Filter.Eventually.of_forall fun i ↦ (hmax i).1) hlim
  by_cases hcase : rotationCalculationMinimum ⟨ω, hω, hω'⟩ +
      Real.tan ((Real.pi / 2 - ω) / 2) ≤ supportValue K.val (0 : Real.Angle)
  · refine ⟨Real.pi / 2 - ω, ⟨by linarith, by linarith⟩, ?_⟩
    rw [rotatingHallwayParts_innerQuadrant]
    exact consumed_of_le_supportValue_zero hω hω' K hBalanced ho hcase
  push Not at hcase
  -- otherwise the clipped-cap area bound forces the left support value to be large
  have hother : rotationCalculationMinimum ⟨ω, hω, hω'⟩ + Real.tan ((Real.pi / 2 - ω) / 2) ≤
      supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) := by
    by_contra hcon
    push Not at hcon
    have hsub : (K.val : Set Point) ⊆
        clippedCap ω (rotationCalculationMinimum ⟨ω, hω, hω'⟩) := by
      intro p hp
      exact ⟨⟨K.subset_stripParallelogram hp,
        (inner_le_supportValue K.val hp (0 : Real.Angle)).trans hcase.le⟩,
        (inner_le_supportValue K.val hp ((ω + Real.pi / 2 : ℝ) : Real.Angle)).trans hcon.le⟩
    have hbdd : Bornology.IsBounded
        (clippedCap ω (rotationCalculationMinimum ⟨ω, hω, hω'⟩)) := by
      refine (EuclideanSpace.isBounded_coordinate_rectangle
        (-((rotationCalculationMinimum ⟨ω, hω, hω'⟩ +
            Real.tan ((Real.pi / 2 - ω) / 2)) / Real.sin ω))
        (rotationCalculationMinimum ⟨ω, hω, hω'⟩ + Real.tan ((Real.pi / 2 - ω) / 2))
        0 1).subset ?_
      intro p hp
      obtain ⟨⟨hy0, hy1⟩, -, hx, hz⟩ := (mem_clippedCap_iff _ _ p).1 hp
      refine ⟨?_, hx, hy0, hy1⟩
      have h2 : -(rotationCalculationMinimum ⟨ω, hω, hω'⟩ +
          Real.tan ((Real.pi / 2 - ω) / 2)) ≤ p 0 * Real.sin ω := by
        nlinarith [mul_nonneg hcos.le hy0]
      have h3 := (div_le_iff₀ hsin).2 h2
      rwa [neg_div] at h3
    have harea : ClassicalResults.area (K.val : Set Point) ≤
        ClassicalResults.area (clippedCap ω (rotationCalculationMinimum ⟨ω, hω, hω'⟩)) :=
      ENNReal.toReal_mono hbdd.measure_lt_top.ne (MeasureTheory.measure_mono hsub)
    have hmin : ClassicalResults.area
        (clippedCap ω (rotationCalculationMinimum ⟨ω, hω, hω'⟩)) < 11 / 5 :=
      clippedCap_minimum_area ⟨ω, hω, hω'⟩
    have hniche : 0 ≤ ClassicalResults.area (capNiche K) := ENNReal.toReal_nonneg
    rw [capAreaFunctional] at hArea
    linarith
  -- pass to the mirror cap, whose zero-angle support value is the left one
  have hMeq : mirrorReflection ω = ((capReflection ω : Point ≃ₗᵢ[ℝ] Point) : Point → Point) :=
    stripTopReflection_eq_capReflection ω hω0 K.property.2.1
  have htanω : normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle) =
      tangentVector (ω : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [normalVector, tangentVector, frame, Real.cos_add, Real.sin_add, -Real.Angle.coe_add]
  have htanT : tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) = -normalVector (0 : Real.Angle) := by
    ext i
    fin_cases i <;> simp [tangentVector, normalVector, frame]
  have hu0 : capReflection ω (normalVector (0 : Real.Angle)) = tangentVector (ω : Real.Angle) := by
    rw [capReflection_normalVector_angle,
      show reflectedAngle ω (0 : Real.Angle) = ((ω + Real.pi / 2 : ℝ) : Real.Angle) from by
        simp [reflectedAngle]]
    exact htanω
  have hvω : capReflection ω (tangentVector (ω : Real.Angle)) = normalVector (0 : Real.Angle) := by
    rw [capReflection_tangentVector_angle,
      show reflectedAngle ω (ω : Real.Angle) = ((Real.pi / 2 : ℝ) : Real.Angle) from by
        simp [reflectedAngle, Real.Angle.coe_add],
      htanT, neg_neg]
  have hc1 : Real.tan ((Real.pi / 2 - ω) / 2) * (1 + Real.sin ω) = Real.cos ω := by
    apply mul_right_cancel₀ hcos.ne'
    nlinarith [hccos, Real.sin_sq_add_cos_sq ω]
  have hfix : capReflection ω (stripParallelogram ω).2.2 = (stripParallelogram ω).2.2 := by
    have hx0 : capReflection ω (stripParallelogram ω).2.2 0 = (stripParallelogram ω).2.2 0 := by
      rw [capReflection_apply_zero, hcoord]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    have hx1 : capReflection ω (stripParallelogram ω).2.2 1 = (stripParallelogram ω).2.2 1 := by
      rw [capReflection_apply_one, hcoord]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    ext i
    fin_cases i
    · exact hx0
    · exact hx1
  have hQbal : IsBalancedMaximumCap
      (⟨reflectedBody ω K.val, reflectedBody_isCap K⟩ : CapSpace ω) := by
    obtain ⟨P, hPset, hPbal⟩ := balancedMaximumCap_mirror K hBalanced
    have hPQ : P = (⟨reflectedBody ω K.val, reflectedBody_isCap K⟩ : CapSpace ω) := by
      apply Subtype.ext
      apply ConvexBody.ext
      rw [hPset, hMeq]
      rfl
    exact hPQ ▸ hPbal
  have hoQ : (stripParallelogram ω).2.2 ∈ (reflectedBody ω K.val : Set Point) :=
    ⟨_, ho, hfix⟩
  have hQsupp : supportValue (reflectedBody ω K.val) (0 : Real.Angle) =
      supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [supportValue_reflectedBody]
    congr 1
    simp [reflectedAngle]
  have hmain : ({0, (stripParallelogram ω).2.2 - tangentVector 0,
      (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)} : Set Point) ⊆
      innerQuadrant (reflectedBody ω K.val : Set Point) (Real.pi / 2 - ω) :=
    consumed_of_le_supportValue_zero hω hω' ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
      hQbal hoQ (by rw [hQsupp]; exact hother)
  have hR1 : capReflection ω ((stripParallelogram ω).2.2 - tangentVector 0) =
      (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) := by
    rw [hgap.1, hgap.2.1, map_smul, hu0]
  have hR2 : capReflection ω ((stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)) =
      (stripParallelogram ω).2.2 - tangentVector 0 := by
    rw [hgap.1, hgap.2.1, map_smul, hvω]
  refine ⟨ω - (Real.pi / 2 - ω), ⟨by linarith, by linarith⟩, ?_⟩
  rw [rotatingHallwayParts_innerQuadrant]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  have hyR : capReflection ω y ∈ ({0, (stripParallelogram ω).2.2 - tangentVector 0,
      (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)} : Set Point) := by
    rcases hy with rfl | rfl | rfl
    · simp
    · rw [hR1]; simp
    · rw [hR2]; simp
  have h1 := hmain hyR
  rw [innerQuadrant_reflection, ← capReflection_preimage_eq_image] at h1
  simpa [capReflection_involutive] using h1

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Motion.RotationAngle`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Rotation Angle
-/

public section

noncomputable section

namespace MovingSofa

/-- A nonnegative combination of two points of a convex set containing the origin, with
coefficient sum at most one, lies in the set. -/
private theorem smul_add_smul_mem_of_convex {U : Set Point} (hU : Convex ℝ U)
    (h0 : (0 : Point) ∈ U) {x y : Point} (hx : x ∈ U) (hy : y ∈ U)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    a • x + b • y ∈ U := by
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ (![a, b, 1 - a - b] : Fin 3 → ℝ) i := by
    intro i _
    fin_cases i
    · exact ha
    · exact hb
    · change (0 : ℝ) ≤ 1 - a - b
      linarith
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin 3)), (![a, b, 1 - a - b] : Fin 3 → ℝ) i = 1 := by
    simp [Fin.sum_univ_three]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      (![x, y, (0 : Point)] : Fin 3 → Point) i ∈ U := by
    intro i _
    fin_cases i
    · exact hx
    · exact hy
    · exact h0
  simpa [Fin.sum_univ_three] using hU.sum_mem hw hsum hz

/-- A point of the strip parallelogram on or below the line through `o_ω - v₀` and
`o_ω - u_ω` lies in every convex set containing the origin and those two points. -/
private theorem mem_of_inner_add_le_one_sub_sin {ω : ℝ} (hω0 : 0 < ω) (hω : ω < Real.pi / 2)
    {U : Set Point} (hU : Convex ℝ U) (h0 : (0 : Point) ∈ U)
    (ha : (stripParallelogram ω).2.2 - tangentVector 0 ∈ U)
    (hb : (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) ∈ U)
    {p : Point} (hy : 0 ≤ p 1) (hx : 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)))
    (hsum : inner ℝ p (normalVector (ω : Real.Angle)) + p 1 ≤ 1 - Real.sin ω) :
    p ∈ U := by
  have hpi := Real.pi_pos
  have hcos : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith, hω⟩
  have hsinlt : Real.sin ω < 1 := by nlinarith [Real.sin_sq_add_cos_sq ω]
  have hgap := parallelogram_gap ω ⟨hω0.le, hω⟩
  have hccos : Real.tan ((Real.pi / 2 - ω) / 2) * Real.cos ω = 1 - Real.sin ω := by
    rw [hgap.2.2.2.2, Real.tan_eq_sin_div_cos]
    field_simp
  have hi1 : inner ℝ (normalVector (0 : Real.Angle)) (normalVector (ω : Real.Angle)) =
      Real.cos ω := by
    rw [← Real.Angle.coe_zero, inner_normalVector_normalVector, zero_sub, Real.cos_neg]
  have hi2 : inner ℝ (normalVector (0 : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [← Real.Angle.coe_zero, inner_normalVector_normalVector, zero_sub, Real.cos_neg,
      Real.cos_pi_div_two]
  have hi3 : inner ℝ (tangentVector (ω : Real.Angle)) (normalVector (ω : Real.Angle)) = 0 := by
    rw [inner_tangentVector_normalVector_real, sub_self, Real.sin_zero]
  have hi4 : inner ℝ (tangentVector (ω : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = Real.cos ω := by
    rw [inner_tangentVector_normalVector_real, Real.sin_pi_div_two_sub]
  have hsne : Real.sin (ω - Real.pi / 2) = -Real.cos ω := by
    rw [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have hden : (1 : ℝ) - Real.sin ω ≠ 0 := by linarith
  have hkey : p = (inner ℝ p (normalVector (ω : Real.Angle)) / (1 - Real.sin ω)) •
        ((stripParallelogram ω).2.2 - tangentVector 0) +
      (p 1 / (1 - Real.sin ω)) •
        ((stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)) := by
    refine eq_of_inner_normalVector_eq (s := ω) (t := Real.pi / 2) ?_ ?_ ?_
    · rw [hsne]
      exact neg_ne_zero.mpr hcos.ne'
    · rw [hgap.1, hgap.2.1, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_left, hi1, hi3, hccos]
      field_simp
      ring
    · rw [inner_normalVector_pi_div_two, hgap.1, hgap.2.1, inner_add_left,
        real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, hi2, hi4, hccos]
      field_simp
      ring
  rw [hkey]
  refine smul_add_smul_mem_of_convex hU h0 ha hb (div_nonneg hx (by linarith))
    (div_nonneg hy (by linarith)) ?_
  rw [← add_div, div_le_one (by linarith)]
  linarith

/-- The width of a clipped strip parallelogram is at most one in every direction between
its rotation angle and a right angle. -/
private theorem inner_sub_inner_le_one_of_clipped {ω : ℝ} (hω0 : 0 ≤ ω)
    (hcos : 0 < Real.cos ω) {p q : Point}
    (hpA : inner ℝ p (normalVector (ω : Real.Angle)) ≤ 1) (hpB : p 1 ≤ 1)
    (hqA : 0 ≤ inner ℝ q (normalVector (ω : Real.Angle))) (hqB : 0 ≤ q 1)
    (hq : 1 - Real.sin ω ≤ inner ℝ q (normalVector (ω : Real.Angle)) + q 1)
    {t : ℝ} (ht : ω ≤ t) (ht' : t ≤ Real.pi / 2) :
    inner ℝ p (normalVector (t : Real.Angle)) -
      inner ℝ q (normalVector (t : Real.Angle)) ≤ 1 := by
  have hpi := Real.pi_pos
  have hct : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ht'⟩
  have hst : 0 ≤ Real.sin (t - ω) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsub : Real.sin (t - ω) = Real.sin t * Real.cos ω - Real.cos t * Real.sin ω :=
    Real.sin_sub t ω
  have hid : ∀ z : Point, Real.cos ω * inner ℝ z (normalVector (t : Real.Angle)) =
      Real.cos t * inner ℝ z (normalVector (ω : Real.Angle)) + Real.sin (t - ω) * z 1 := by
    intro z
    rw [inner_normalVector_real, inner_normalVector_real, hsub]
    ring
  have hmain : Real.cos ω * (inner ℝ p (normalVector (t : Real.Angle)) -
      inner ℝ q (normalVector (t : Real.Angle))) ≤ Real.cos ω := by
    rw [mul_sub, hid p, hid q]
    have h1 : Real.cos t * inner ℝ p (normalVector (ω : Real.Angle)) ≤ Real.cos t :=
      mul_le_of_le_one_right hct hpA
    have h2 : Real.sin (t - ω) * p 1 ≤ Real.sin (t - ω) :=
      mul_le_of_le_one_right hst hpB
    rcases le_total (Real.cos t) (Real.sin (t - ω)) with hle | hle
    · have e1 : Real.cos t * (1 - Real.sin ω) ≤
          Real.cos t * (inner ℝ q (normalVector (ω : Real.Angle)) + q 1) :=
        mul_le_mul_of_nonneg_left hq hct
      have e2 : 0 ≤ (Real.sin (t - ω) - Real.cos t) * q 1 := mul_nonneg (by linarith) hqB
      have h3 : Real.cos t * (1 - Real.sin ω) ≤
          Real.cos t * inner ℝ q (normalVector (ω : Real.Angle)) + Real.sin (t - ω) * q 1 := by
        nlinarith [e1, e2]
      have h4 : Real.sin (t - ω) + Real.cos t * Real.sin ω = Real.sin t * Real.cos ω := by
        rw [hsub]; ring
      have h5 : Real.sin t * Real.cos ω ≤ Real.cos ω := by
        nlinarith [Real.sin_le_one t]
      linarith
    · have e1 : Real.sin (t - ω) * (1 - Real.sin ω) ≤
          Real.sin (t - ω) * (inner ℝ q (normalVector (ω : Real.Angle)) + q 1) :=
        mul_le_mul_of_nonneg_left hq hst
      have e2 : 0 ≤ (Real.cos t - Real.sin (t - ω)) *
          inner ℝ q (normalVector (ω : Real.Angle)) := mul_nonneg (by linarith) hqA
      have h3 : Real.sin (t - ω) * (1 - Real.sin ω) ≤
          Real.cos t * inner ℝ q (normalVector (ω : Real.Angle)) + Real.sin (t - ω) * q 1 := by
        nlinarith [e1, e2]
      have h4 : Real.cos t + Real.sin (t - ω) * Real.sin ω =
          Real.cos ω * Real.cos (t - ω) := by
        rw [hsub, Real.cos_sub]
        linear_combination (-Real.cos t) * Real.sin_sq_add_cos_sq ω
      have h5 : Real.cos ω * Real.cos (t - ω) ≤ Real.cos ω := by
        nlinarith [Real.cos_le_one (t - ω)]
      linarith
  nlinarith [hmain]

/-- Normalizing data for the rotated copies of a sofa of width at most one: a continuous
minimal height and a uniform horizontal bound. -/
private theorem exists_normalization_of_width {s : Set Point} {ω : ℝ}
    (hcpt : IsCompact s) (hne : s.Nonempty)
    (hwidth : ∀ t : ℝ, ω ≤ t → t ≤ Real.pi / 2 → ∀ p ∈ s, ∀ q ∈ s,
      inner ℝ p (normalVector (t : Real.Angle)) -
        inner ℝ q (normalVector (t : Real.Angle)) ≤ 1) :
    ∃ (low : ℝ → ℝ) (M : ℝ), Continuous low ∧
      (∀ d : ℝ, ∀ p ∈ s, (rotationMap ((d : ℝ) : Real.Angle) p) 0 ≤ M) ∧
      (∀ d : ℝ, ∀ p ∈ s, low d ≤ (rotationMap ((d : ℝ) : Real.Angle) p) 1) ∧
      (∀ d : ℝ, 0 ≤ d → d ≤ Real.pi / 2 - ω → ∀ p ∈ s,
        (rotationMap ((d : ℝ) : Real.Angle) p) 1 - low d ≤ 1) := by
  have hcoord1 : ∀ (d : ℝ) (p : Point), (rotationMap ((d : ℝ) : Real.Angle) p) 1 =
      inner ℝ p (normalVector ((Real.pi / 2 - d : ℝ) : Real.Angle)) := by
    intro d p
    rw [rotationMap_apply_one, inner_normalVector_real, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    ring
  obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall (0 : Point)
  refine ⟨fun d ↦ -supportValue s ((Real.pi / 2 - d + Real.pi : ℝ) : Real.Angle),
    max R 0, ?_, ?_, ?_, ?_⟩
  · exact ((compactSet_support_continuity s s hne hcpt hne hcpt).2.2.1.comp
      (Real.Angle.continuous_coe.comp (by fun_prop))).neg
  · intro d p hp
    have hnp : ‖p‖ ≤ max R 0 := by
      have h := hR hp
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact h.trans (le_max_left _ _)
    have hn : ‖rotationMap ((d : ℝ) : Real.Angle) p‖ = ‖p‖ := by
      change ‖(EuclideanGeometry.o.rotation ((d : ℝ) : Real.Angle)) p‖ = ‖p‖
      exact LinearIsometryEquiv.norm_map _ p
    calc (rotationMap ((d : ℝ) : Real.Angle) p) 0
        = inner ℝ (rotationMap ((d : ℝ) : Real.Angle) p)
            (normalVector ((0 : ℝ) : Real.Angle)) := (inner_normalVector_zero _).symm
      _ ≤ ‖rotationMap ((d : ℝ) : Real.Angle) p‖ *
            ‖normalVector ((0 : ℝ) : Real.Angle)‖ := real_inner_le_norm _ _
      _ = ‖p‖ := by rw [norm_normalVector_real, hn, mul_one]
      _ ≤ max R 0 := hnp
  · intro d p hp
    rw [hcoord1]
    have h := inner_le_supportValue_of_isCompact hcpt hp
      ((Real.pi / 2 - d + Real.pi : ℝ) : Real.Angle)
    rw [normalVector_add_pi, inner_neg_right] at h
    change -supportValue s ((Real.pi / 2 - d + Real.pi : ℝ) : Real.Angle) ≤ _
    linarith
  · intro d hd0 hd1 p hp
    have ht : ω ≤ Real.pi / 2 - d := by linarith
    have ht' : Real.pi / 2 - d ≤ Real.pi / 2 := by linarith
    have hstep : supportValue s ((Real.pi / 2 - d + Real.pi : ℝ) : Real.Angle) ≤
        1 - inner ℝ p (normalVector ((Real.pi / 2 - d : ℝ) : Real.Angle)) := by
      refine csSup_le (hne.image _) ?_
      rintro _ ⟨q, hq, rfl⟩
      simp only [normalVector_add_pi, inner_neg_right]
      have h := hwidth (Real.pi / 2 - d) ht ht' p hp q hq
      linarith
    rw [hcoord1]
    change inner ℝ p (normalVector ((Real.pi / 2 - d : ℝ) : Real.Angle)) -
      -supportValue s ((Real.pi / 2 - d + Real.pi : ℝ) : Real.Angle) ≤ 1
    linarith

/-- A sofa of rotation angle `ω` that can be placed at height between zero and one in every
intermediate rotated position admits, after rotating by `π/2 - ω`, a motion of rotation
angle `π/2`. -/
private theorem hasRotationAngle_rotationMap_of_normalization {s : Set Point} {ω : ℝ}
    (hlt : ω < Real.pi / 2) (hconn : IsConnected s) (hcpt : IsCompact s)
    (hrot : HasRotationAngle s ω) (low : ℝ → ℝ) (M : ℝ) (hlowcont : Continuous low)
    (hhoriz : ∀ d : ℝ, ∀ p ∈ s, (rotationMap ((d : ℝ) : Real.Angle) p) 0 ≤ M)
    (hloleq : ∀ d : ℝ, ∀ p ∈ s, low d ≤ (rotationMap ((d : ℝ) : Real.Angle) p) 1)
    (hupleq : ∀ d : ℝ, 0 ≤ d → d ≤ Real.pi / 2 - ω → ∀ p ∈ s,
      (rotationMap ((d : ℝ) : Real.Angle) p) 1 - low d ≤ 1) :
    HasRotationAngle (rotationMap ((Real.pi / 2 - ω : ℝ) : Real.Angle) '' s)
      (Real.pi / 2) := by
  have hrot0 : ∀ p : Point, rotationMap ((0 : ℝ) : Real.Angle) p = p := by
    intro p
    rw [rotationMap, Real.Angle.coe_zero, Orientation.rotation_zero]
    rfl
  set δ₀ : ℝ := Real.pi / 2 - ω with hδ₀def
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀def]; linarith
  -- the original motion witnessing rotation angle `ω`
  obtain ⟨m₀, hm₀, α₀, hα₀c, hα₀0, hα₀1, hm₀lift⟩ := hrot
  obtain ⟨v, hv⟩ := hm₀.2.2.2.1
  have hm₀0 : m₀ 0 0 = v := by rw [hv]; exact zero_add v
  have hinit : ∀ p ∈ s, p 0 + v 0 ≤ 1 ∧ 0 ≤ p 1 + v 1 ∧ p 1 + v 1 ≤ 1 := by
    intro p hp
    exact mem_horizontalHallway_coordinates (hm₀.2.2.2.2.2.1 ⟨p, hp, hv p⟩)
  have hmcam : Continuous
      (fun t : unitInterval ↦ (m₀ t).toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom.comp hm₀.2.2.1
  -- the reparametrized motion of the rotated sofa
  have hτmem : ∀ r : unitInterval, max (3 * (r : ℝ) - 2) 0 ∈ unitInterval :=
    fun r ↦ ⟨le_max_right _ _, max_le (by linarith [r.2.2]) (by norm_num)⟩
  set τ : unitInterval → unitInterval := fun r ↦ ⟨max (3 * (r : ℝ) - 2) 0, hτmem r⟩ with hτdef
  set Θ : unitInterval → ℝ := fun r ↦ -δ₀ * min (3 * (r : ℝ)) 1 + α₀ (τ r) with hΘdef
  set dd : unitInterval → ℝ := fun r ↦ δ₀ * (1 - min (3 * (r : ℝ)) 1) with hdddef
  set σ : unitInterval → ℝ := fun r ↦ min (max (3 * (r : ℝ) - 1) 0) 1 with hσdef
  set C : unitInterval → Point := fun r ↦
    (1 - σ r) • (!₂[-M, -low (dd r)] : Point) + σ r • v + (m₀ (τ r) 0 - v) with hCdef
  set n : unitInterval → Point ≃ᵃⁱ[ℝ] Point := fun r ↦
    (EuclideanGeometry.o.rotation ((Θ r : ℝ) : Real.Angle)).toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.vaddConst ℝ (C r)) with hndef
  have hnapp : ∀ (r : unitInterval) (p : Point),
      n r p = rotationMap ((Θ r : ℝ) : Real.Angle) p + C r := fun _ _ ↦ rfl
  have hn0eq : ∀ r : unitInterval, n r 0 = C r := by
    intro r
    rw [hnapp, rotationMap]
    simp
  have hcompose : ∀ (r : unitInterval) (p : Point),
      n r (rotationMap ((δ₀ : ℝ) : Real.Angle) p) =
        rotationMap ((dd r + α₀ (τ r) : ℝ) : Real.Angle) p + C r := by
    intro r p
    have hΘsum : Θ r + δ₀ = dd r + α₀ (τ r) := by
      change -δ₀ * min (3 * (r : ℝ)) 1 + α₀ (τ r) + δ₀ =
        δ₀ * (1 - min (3 * (r : ℝ)) 1) + α₀ (τ r)
      ring
    rw [hnapp]
    congr 1
    change (EuclideanGeometry.o.rotation ((Θ r : ℝ) : Real.Angle))
        ((EuclideanGeometry.o.rotation ((δ₀ : ℝ) : Real.Angle)) p) =
      (EuclideanGeometry.o.rotation ((dd r + α₀ (τ r) : ℝ) : Real.Angle)) p
    rw [Orientation.rotation_rotation, ← Real.Angle.coe_add, hΘsum]
  have hτzero : ∀ r : unitInterval, 3 * (r : ℝ) ≤ 2 → τ r = 0 := by
    intro r hr
    apply Subtype.ext
    change max (3 * (r : ℝ) - 2) 0 = 0
    exact max_eq_right (by linarith)
  -- phase one: rotating down to the horizontal position
  have hphaseA : ∀ r : unitInterval, 3 * (r : ℝ) ≤ 1 → ∀ p ∈ s,
      n r (rotationMap ((δ₀ : ℝ) : Real.Angle) p) ∈ horizontalHallway := by
    intro r hr p hp
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := r.2.1
    have hτ0 : τ r = 0 := hτzero r (by linarith)
    have hσ0 : σ r = 0 := by
      change min (max (3 * (r : ℝ) - 1) 0) 1 = 0
      rw [max_eq_right (by linarith)]
      exact min_eq_left (by norm_num)
    have hdd : dd r = δ₀ * (1 - 3 * (r : ℝ)) := by
      change δ₀ * (1 - min (3 * (r : ℝ)) 1) = _
      rw [min_eq_left hr]
    have hdd0 : 0 ≤ dd r := by
      rw [hdd]
      exact mul_nonneg hδ₀pos.le (by linarith)
    have hdd1 : dd r ≤ δ₀ := by
      have h := mul_le_mul_of_nonneg_left (show 1 - 3 * (r : ℝ) ≤ 1 by linarith) hδ₀pos.le
      rw [hdd]
      linarith [h]
    have hC : C r = (!₂[-M, -low (dd r)] : Point) := by
      change (1 - σ r) • (!₂[-M, -low (dd r)] : Point) + σ r • v + (m₀ (τ r) 0 - v) = _
      rw [hσ0, hτ0, hm₀0]
      simp
    have heval : n r (rotationMap ((δ₀ : ℝ) : Real.Angle) p) =
        rotationMap ((dd r : ℝ) : Real.Angle) p + (!₂[-M, -low (dd r)] : Point) := by
      rw [hcompose, hτ0, hα₀0, add_zero, hC]
    rw [heval]
    refine mem_horizontalHallway_of_coordinates _ ?_ ⟨?_, ?_⟩
    · change (rotationMap ((dd r : ℝ) : Real.Angle) p) 0 + -M ≤ 1
      have h := hhoriz (dd r) p hp
      linarith
    · change (0 : ℝ) ≤ (rotationMap ((dd r : ℝ) : Real.Angle) p) 1 + -low (dd r)
      have h := hloleq (dd r) p hp
      linarith
    · change (rotationMap ((dd r : ℝ) : Real.Angle) p) 1 + -low (dd r) ≤ 1
      have h := hupleq (dd r) hdd0 hdd1 p hp
      linarith
  -- phase two: translating to the initial placement of the original motion
  have hphaseB : ∀ r : unitInterval, 1 ≤ 3 * (r : ℝ) → 3 * (r : ℝ) ≤ 2 → ∀ p ∈ s,
      n r (rotationMap ((δ₀ : ℝ) : Real.Angle) p) ∈ horizontalHallway := by
    intro r hr hr' p hp
    have hτ0 : τ r = 0 := hτzero r hr'
    have hσ : σ r = 3 * (r : ℝ) - 1 := by
      change min (max (3 * (r : ℝ) - 1) 0) 1 = _
      rw [max_eq_left (by linarith)]
      exact min_eq_left (by linarith)
    have hσ0 : 0 ≤ σ r := by rw [hσ]; linarith
    have hσ1 : σ r ≤ 1 := by rw [hσ]; linarith
    have hdd : dd r = 0 := by
      change δ₀ * (1 - min (3 * (r : ℝ)) 1) = 0
      rw [min_eq_right hr]
      ring
    have hC : C r = (1 - σ r) • (!₂[-M, -low 0] : Point) + σ r • v := by
      change (1 - σ r) • (!₂[-M, -low (dd r)] : Point) + σ r • v + (m₀ (τ r) 0 - v) = _
      rw [hdd, hτ0, hm₀0]
      simp
    have heval : n r (rotationMap ((δ₀ : ℝ) : Real.Angle) p) =
        p + ((1 - σ r) • (!₂[-M, -low 0] : Point) + σ r • v) := by
      rw [hcompose, hτ0, hα₀0, add_zero, hdd, hrot0, hC]
    have h1 := hloleq 0 p hp
    have h2 := hupleq 0 le_rfl hδ₀pos.le p hp
    have hhz := hhoriz 0 p hp
    rw [hrot0] at h1 h2 hhz
    obtain ⟨hi1, hi2, hi3⟩ := hinit p hp
    rw [heval]
    refine mem_horizontalHallway_of_coordinates _ ?_ ⟨?_, ?_⟩
    · change p 0 + ((1 - σ r) * -M + σ r * v 0) ≤ 1
      have k1 : 0 ≤ (1 - σ r) * (M - p 0) := mul_nonneg (by linarith) (by linarith)
      have k2 : 0 ≤ σ r * (1 - (p 0 + v 0)) := mul_nonneg hσ0 (by linarith)
      nlinarith only [k1, k2, hσ1]
    · change (0 : ℝ) ≤ p 1 + ((1 - σ r) * -low 0 + σ r * v 1)
      have k3 : 0 ≤ (1 - σ r) * (p 1 - low 0) := mul_nonneg (by linarith) (by linarith)
      have k4 : 0 ≤ σ r * (p 1 + v 1) := mul_nonneg hσ0 (by linarith)
      nlinarith only [k3, k4]
    · change p 1 + ((1 - σ r) * -low 0 + σ r * v 1) ≤ 1
      have k5 : 0 ≤ (1 - σ r) * (1 - (p 1 - low 0)) := mul_nonneg (by linarith) (by linarith)
      have k6 : 0 ≤ σ r * (1 - (p 1 + v 1)) := mul_nonneg hσ0 (by linarith)
      nlinarith only [k5, k6]
  -- phase three: the original motion
  have hphaseC : ∀ r : unitInterval, 2 ≤ 3 * (r : ℝ) → ∀ p : Point,
      n r (rotationMap ((δ₀ : ℝ) : Real.Angle) p) = m₀ (τ r) p := by
    intro r hr p
    have hσ1 : σ r = 1 := by
      change min (max (3 * (r : ℝ) - 1) 0) 1 = 1
      rw [max_eq_left (by linarith)]
      exact min_eq_right (by linarith)
    have hdd : dd r = 0 := by
      change δ₀ * (1 - min (3 * (r : ℝ)) 1) = 0
      rw [min_eq_right (by linarith)]
      ring
    have hC : C r = m₀ (τ r) 0 := by
      change (1 - σ r) • (!₂[-M, -low (dd r)] : Point) + σ r • v + (m₀ (τ r) 0 - v) = _
      rw [hσ1]
      simp
    rw [hcompose, hC, hdd, zero_add, hm₀lift (τ r) p]
  -- continuity of the reparametrized motion
  have hτcont : Continuous τ := by
    rw [hτdef]
    exact Continuous.subtype_mk (by fun_prop) _
  have hσcont : Continuous σ := by rw [hσdef]; fun_prop
  have hddcont : Continuous dd := by rw [hdddef]; fun_prop
  have hΘcont : Continuous Θ := by
    rw [hΘdef]
    exact (continuous_const.mul (by fun_prop)).add (hα₀c.comp hτcont)
  have hbasecont : Continuous (fun r : unitInterval ↦ (!₂[-M, -low (dd r)] : Point)) := by
    have h : Continuous (fun r : unitInterval ↦ -low (dd r)) := (hlowcont.comp hddcont).neg
    fun_prop
  have hCcont : Continuous C := by
    rw [hCdef]
    exact (((continuous_const.sub hσcont).smul hbasecont).add
        (hσcont.smul continuous_const)).add
      (((hmcam.eval_const 0).comp hτcont).sub continuous_const)
  have hncont : Continuous n := by
    rw [hndef]
    exact continuous_rotation_trans_vaddConst (Real.Angle.continuous_coe.comp hΘcont) hCcont
  -- endpoint values
  have hτ1 : τ 1 = 1 := by
    apply Subtype.ext
    change max (3 * ((1 : unitInterval) : ℝ) - 2) 0 = ((1 : unitInterval) : ℝ)
    norm_num
  have hΘ0 : Θ 0 = 0 := by
    change -δ₀ * min (3 * ((0 : unitInterval) : ℝ)) 1 + α₀ (τ 0) = 0
    rw [hτzero 0 (by norm_num), hα₀0]
    norm_num
  have hΘ1 : Θ 1 = -(Real.pi / 2) := by
    change -δ₀ * min (3 * ((1 : unitInterval) : ℝ)) 1 + α₀ (τ 1) = -(Real.pi / 2)
    rw [hτ1, hα₀1, show (3 : ℝ) * ((1 : unitInterval) : ℝ) = 3 by norm_num,
      min_eq_right (by norm_num : (1 : ℝ) ≤ 3), hδ₀def]
    ring
  have hrotcont : Continuous (rotationMap ((δ₀ : ℝ) : Real.Angle)) :=
    (EuclideanGeometry.o.rotation ((δ₀ : ℝ) : Real.Angle)).continuous
  refine ⟨n, ⟨hconn.image _ hrotcont.continuousOn, (hcpt.image hrotcont).isClosed, hncont,
    ⟨C 0, ?_⟩, ?_, ?_, ?_, ?_⟩, Θ, hΘcont, hΘ0, hΘ1, ?_⟩
  · intro p
    rw [hnapp, hΘ0, hrot0]
  · intro t
    exact ⟨((Θ t : ℝ) : Real.Angle), fun p ↦ by rw [hnapp, hn0eq]⟩
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact hphaseA 0 (by norm_num) p hp
  · intro r
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rcases le_total (3 * (r : ℝ)) 1 with h | h
    · exact Set.subset_union_left (hphaseA r h p hp)
    · rcases le_total (3 * (r : ℝ)) 2 with h' | h'
      · exact Set.subset_union_left (hphaseB r h h' p hp)
      · rw [hphaseC r h' p]
        exact hm₀.2.2.2.2.2.2.1 (τ r) ⟨p, hp, rfl⟩
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [hphaseC 1 (by norm_num) p, hτ1]
    exact hm₀.2.2.2.2.2.2.2 ⟨p, hp, rfl⟩
  · intro r p
    rw [hnapp, hn0eq]

theorem balancedMaximumSofa_rightAngle (s : Set Point) (ω : ℝ)
    (hs : IsBalancedMaximumSofa s ω)
    (hω : ω ∈ Set.Icc (Real.arccos (5 / 11 : ℝ)) (Real.pi / 2))
    (hArea : 11 / 5 ≤ ClassicalResults.area s) :
    ∃ α : Real.Angle, HasRotationAngle (rotationMap α '' s) (Real.pi / 2) := by
  have hpi := Real.pi_pos
  obtain ⟨⟨s₀, hs₀, hsdef⟩, K, hKcap, hKbal⟩ := hs
  have hstd : IsStandardPosition s ω := by
    rw [hsdef]
    exact (standardPosition_monotonization_standard s₀ ω hs₀).1
  have hω0 : 0 < ω := hstd.2.2.1
  have hconn : IsConnected s := by
    rw [hsdef]
    exact standardPosition_monotonization_connected s₀ ω hs₀
  have hcpt : IsCompact s := hstd.1
  have hrot : HasRotationAngle s ω := hstd.2.1
  rcases eq_or_lt_of_le hω.2 with heq | hlt
  · refine ⟨((0 : ℝ) : Real.Angle), ?_⟩
    have hrot0 : ∀ p : Point, rotationMap ((0 : ℝ) : Real.Angle) p = p := by
      intro p
      rw [rotationMap, Real.Angle.coe_zero, Orientation.rotation_zero]
      rfl
    rw [show rotationMap ((0 : ℝ) : Real.Angle) = id from funext hrot0, Set.image_id]
    exact heq ▸ hrot
  -- the consumed corner triangle of the balanced maximum cap
  have hcos : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩
  have hstrip : s ⊆ (stripParallelogram ω).1 := by
    rw [hsdef]
    exact Set.inter_subset_left
  have hareaK : (11 : ℝ) / 5 ≤ capAreaFunctional K := by
    rw [capAreaFunctional_eq_sofaArea s ω ⟨s₀, hs₀, hsdef⟩ K hKcap]
    exact hArea
  have hsK : s = (K.val : Set Point) \ capNiche K :=
    monotoneSofa_structure s ω ⟨s₀, hs₀, hsdef⟩ K hKcap
  obtain ⟨t₀, ht₀, hsub3⟩ := balancedMaximumCap_consumed K hω.1 hlt hKbal hareaK
  rw [rotatingHallwayParts_innerQuadrant] at hsub3
  have hgap := parallelogram_gap ω ⟨hω0.le, hlt⟩
  have hccos : Real.tan ((Real.pi / 2 - ω) / 2) * Real.cos ω = 1 - Real.sin ω := by
    rw [hgap.2.2.2.2, Real.tan_eq_sin_div_cos]
    field_simp
  have hsinlt : Real.sin ω < 1 := by nlinarith [Real.sin_sq_add_cos_sq ω]
  have hcpos : 0 < Real.tan ((Real.pi / 2 - ω) / 2) := by nlinarith
  have hmem_capFan : ∀ z : Point, 0 ≤ inner ℝ z (normalVector (ω : Real.Angle)) →
      0 ≤ inner ℝ z (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) → z ∈ capFan ω :=
    fun _ h1 h2 ↦ ⟨h1, h2⟩
  have hfan0 : (0 : Point) ∈ capFan ω := hmem_capFan 0 (by simp) (by simp)
  have hfana : (stripParallelogram ω).2.2 - tangentVector 0 ∈ capFan ω := by
    rw [hgap.1]
    refine hmem_capFan _ ?_ ?_
    · rw [real_inner_smul_left, ← Real.Angle.coe_zero, inner_normalVector_normalVector,
        zero_sub, Real.cos_neg]
      exact mul_nonneg hcpos.le hcos.le
    · rw [real_inner_smul_left, ← Real.Angle.coe_zero, inner_normalVector_normalVector,
        zero_sub, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  have hfanb : (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) ∈ capFan ω := by
    rw [hgap.2.1]
    refine hmem_capFan _ ?_ ?_
    · rw [real_inner_smul_left, inner_tangentVector_normalVector_real, sub_self,
        Real.sin_zero, mul_zero]
    · rw [real_inner_smul_left, inner_tangentVector_normalVector_real,
        Real.sin_pi_div_two_sub]
      exact mul_nonneg hcpos.le hcos.le
  have hUconv : Convex ℝ (capFan ω ∩ innerQuadrant (K.val : Set Point) t₀) :=
    (convex_capFan ω).inter (convex_innerQuadrant _ _)
  have hUniche : capFan ω ∩ innerQuadrant (K.val : Set Point) t₀ ⊆ capNiche K :=
    fun z hz ↦ ⟨hz.1, Set.mem_iUnion₂.mpr ⟨t₀, ht₀, hz.2⟩⟩
  have h0U : (0 : Point) ∈ capFan ω ∩ innerQuadrant (K.val : Set Point) t₀ :=
    ⟨hfan0, hsub3 (by simp)⟩
  have haU : (stripParallelogram ω).2.2 - tangentVector 0 ∈
      capFan ω ∩ innerQuadrant (K.val : Set Point) t₀ := ⟨hfana, hsub3 (by simp)⟩
  have hbU : (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) ∈
      capFan ω ∩ innerQuadrant (K.val : Set Point) t₀ := ⟨hfanb, hsub3 (by simp)⟩
  have hlowbd : ∀ p ∈ s, 1 - Real.sin ω ≤ inner ℝ p (normalVector (ω : Real.Angle)) + p 1 := by
    intro p hp
    by_contra hcon
    push Not at hcon
    obtain ⟨hy, hx⟩ := (mem_stripParallelogram_iff ω p).1 (hstrip hp)
    have hmem := hUniche (mem_of_inner_add_le_one_sub_sin hω0 hlt hUconv h0U haU hbU
      hy.1 hx.1 hcon.le)
    rw [hsK] at hp
    exact hp.2 hmem
  have hwidth : ∀ t : ℝ, ω ≤ t → t ≤ Real.pi / 2 → ∀ p ∈ s, ∀ q ∈ s,
      inner ℝ p (normalVector (t : Real.Angle)) -
        inner ℝ q (normalVector (t : Real.Angle)) ≤ 1 := by
    intro t ht ht' p hp q hq
    obtain ⟨hp1, hp2⟩ := (mem_stripParallelogram_iff ω p).1 (hstrip hp)
    obtain ⟨hq1, hq2⟩ := (mem_stripParallelogram_iff ω q).1 (hstrip hq)
    exact inner_sub_inner_le_one_of_clipped hω0.le hcos hp2.2 hp1.2 hq2.1 hq1.1
      (hlowbd q hq) ht ht'
  obtain ⟨low, M, hlowcont, hhoriz, hloleq, hupleq⟩ :=
    exists_normalization_of_width hcpt hconn.nonempty hwidth
  exact ⟨((Real.pi / 2 - ω : ℝ) : Real.Angle),
    hasRotationAngle_rotationMap_of_normalization hlt hconn hcpt hrot low M hlowcont
      hhoriz hloleq hupleq⟩

private theorem hasRotationAngle_right_of_reaches_right (S : Set Point)
    (m : unitInterval → Point ≃ᵃⁱ[ℝ] Point) (hm : IsMovingSofa S m)
    (α : unitInterval → ℝ) (e : unitInterval → Point)
    (hαc : Continuous α) (hα0 : α 0 = 0)
    (hlift : ∀ t p, m t p = rotationMap (α t : Real.Angle) p + e t)
    (ts : unitInterval) (hts : α ts = -(Real.pi / 2)) :
    HasRotationAngle S (Real.pi / 2) := by
  have hcoord : ∀ (u v : Point) (i : Fin 2), (u + v) i = u i + v i := fun _ _ _ ↦ rfl
  have hH : ∀ p ∈ S, 0 ≤ p 1 ∧ p 1 ≤ 1 := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_horizontalHallway_coordinates (hm.initial hp)
    exact ⟨h1, h2⟩
  have hLt : ∀ (t : unitInterval) (p : Point), p ∈ S →
      (m t p) 0 ≤ 1 ∧ (m t p) 1 ≤ 1 ∧ (0 ≤ (m t p) 0 ∨ 0 ≤ (m t p) 1) := by
    intro t p hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := (mem_hallway_iff _).mp (hm.subset_hallway t ⟨p, hp, rfl⟩)
    exact ⟨h1, h2, h3⟩
  have hcs : ((α ts : ℝ) : Real.Angle).cos = 0 := by
    rw [Real.Angle.cos_coe, hts]
    simp
  have hsns : ((α ts : ℝ) : Real.Angle).sin = -1 := by
    rw [Real.Angle.sin_coe, hts]
    simp
  have hmts0 : ∀ p : Point, (m ts p) 0 = p 1 + (e ts) 0 := by
    intro p
    rw [hlift ts p, hcoord, rotationMap_apply_zero, hcs, hsns]
    ring
  have hmts1 : ∀ p : Point, (m ts p) 1 = -p 0 + (e ts) 1 := by
    intro p
    rw [hlift ts p, hcoord, rotationMap_apply_one, hcs, hsns]
    ring
  -- the supremum of the vertical coordinates of the initial placement
  obtain ⟨p₀, hp₀⟩ := hm.isConnected.nonempty
  have hTne : ((fun p : Point ↦ p 1) '' S).Nonempty := ⟨p₀ 1, p₀, hp₀, rfl⟩
  have hTbdd : BddAbove ((fun p : Point ↦ p 1) '' S) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (hH p hp).2
  set N : ℝ := sSup ((fun p : Point ↦ p 1) '' S) with hNdef
  have hNub : ∀ p ∈ S, p 1 ≤ N := fun p hp ↦ le_csSup hTbdd ⟨p, hp, rfl⟩
  have hNle : N ≤ 1 := by
    refine csSup_le hTne ?_
    rintro _ ⟨p, hp, rfl⟩
    exact (hH p hp).2
  have hNd : N + (e ts) 0 ≤ 1 := by
    have hle : N ≤ 1 - (e ts) 0 := by
      refine csSup_le hTne ?_
      rintro _ ⟨p, hp, rfl⟩
      have hx := (hLt ts p hp).1
      rw [hmts0 p] at hx
      linarith
    linarith
  set δ : ℝ := 1 - N - (e ts) 0 with hδdef
  have hδ : 0 ≤ δ := by
    rw [hδdef]
    linarith
  -- the reparametrized motion, followed by the horizontal translation
  have hφmem : ∀ r : unitInterval, min (2 * (r : ℝ)) 1 * (ts : ℝ) ∈ unitInterval := by
    intro r
    constructor
    · exact mul_nonneg (le_min (by linarith [r.2.1]) (by norm_num)) ts.2.1
    · calc min (2 * (r : ℝ)) 1 * (ts : ℝ) ≤ 1 * 1 :=
            mul_le_mul (min_le_right _ _) ts.2.2 ts.2.1 (by norm_num)
      _ = 1 := one_mul 1
  set φ : unitInterval → unitInterval :=
    fun r ↦ ⟨min (2 * (r : ℝ)) 1 * (ts : ℝ), hφmem r⟩ with hφdef
  set ψ : unitInterval → ℝ := fun r ↦ max (2 * (r : ℝ) - 1) 0 with hψdef
  set w : Point := !₂[δ, 0] with hwdef
  have hw0 : w 0 = δ := rfl
  have hw1 : w 1 = 0 := rfl
  set n : unitInterval → Point ≃ᵃⁱ[ℝ] Point :=
    fun r ↦ (m (φ r)).trans (AffineIsometryEquiv.vaddConst ℝ (ψ r • w)) with hndef
  have hnapp : ∀ (r : unitInterval) (p : Point), n r p = m (φ r) p + ψ r • w := fun _ _ ↦ rfl
  have hφcont : Continuous φ := by
    rw [hφdef]
    exact Continuous.subtype_mk (by fun_prop) _
  have hψcont : Continuous ψ := by
    rw [hψdef]
    fun_prop
  have hφ0 : φ 0 = 0 := by
    apply Subtype.ext
    change min (2 * ((0 : unitInterval) : ℝ)) 1 * (ts : ℝ) = 0
    norm_num
  have hφ1 : φ 1 = ts := by
    apply Subtype.ext
    change min (2 * ((1 : unitInterval) : ℝ)) 1 * (ts : ℝ) = (ts : ℝ)
    norm_num
  have hψ0 : ψ 0 = 0 := by
    change max (2 * ((0 : unitInterval) : ℝ) - 1) 0 = 0
    norm_num
  have hψ1 : ψ 1 = 1 := by
    change max (2 * ((1 : unitInterval) : ℝ) - 1) 0 = 1
    norm_num
  have hψnn : ∀ r : unitInterval, 0 ≤ ψ r := fun r ↦ le_max_right _ _
  have hψle : ∀ r : unitInterval, ψ r ≤ 1 := by
    intro r
    exact max_le (by linarith [r.2.2]) (by norm_num)
  have hψpos : ∀ r : unitInterval, ψ r ≠ 0 → φ r = ts := by
    intro r hr
    have hlt : 1 < 2 * (r : ℝ) := by
      by_contra hcon
      push Not at hcon
      apply hr
      change max (2 * (r : ℝ) - 1) 0 = 0
      exact max_eq_right (by linarith)
    apply Subtype.ext
    change min (2 * (r : ℝ)) 1 * (ts : ℝ) = (ts : ℝ)
    rw [min_eq_right hlt.le, one_mul]
  -- the hallway containment of the new motion
  have hnhall : ∀ (r : unitInterval), n r '' S ⊆ hallway := by
    rintro r _ ⟨p, hp, rfl⟩
    obtain ⟨hy0, hy1⟩ := hH p hp
    obtain ⟨hx1, hx2, hx3⟩ := hLt (φ r) p hp
    by_cases hr : ψ r = 0
    · have heq : n r p = m (φ r) p := by
        rw [hnapp, hr, zero_smul, add_zero]
      rw [heq]
      exact (mem_hallway_iff _).mpr ⟨⟨hx1, hx2⟩, hx3⟩
    · have hφr := hψpos r hr
      obtain ⟨hz1, hz2, hz3⟩ := hLt ts p hp
      have hc0 : (n r p) 0 = p 1 + (e ts) 0 + ψ r * δ := by
        rw [hnapp, hcoord, hφr, hmts0 p]
        change p 1 + (e ts) 0 + ψ r * w 0 = _
        rw [hw0]
      have hc1 : (n r p) 1 = -p 0 + (e ts) 1 := by
        rw [hnapp, hcoord, hφr, hmts1 p]
        change -p 0 + (e ts) 1 + ψ r * w 1 = _
        rw [hw1]
        ring
      rw [hmts0 p] at hz1 hz3
      rw [hmts1 p] at hz2 hz3
      refine (mem_hallway_iff _).mpr ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hc0]
        have hmul : ψ r * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right (hψle r) hδ
        have := hNub p hp
        rw [hδdef] at hmul
        linarith
      · rw [hc1]
        linarith
      · rcases hz3 with h | h
        · left
          rw [hc0]
          have : 0 ≤ ψ r * δ := mul_nonneg (hψnn r) hδ
          linarith
        · right
          rw [hc1]
          linarith
  have hnfinal : n 1 '' S ⊆ verticalHallway := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hy0, hy1⟩ := hH p hp
    obtain ⟨hz1, hz2, hz3⟩ := hLt ts p hp
    rw [hmts1 p] at hz2
    have hc0 : (n 1 p) 0 = p 1 + (e ts) 0 + δ := by
      rw [hnapp, hcoord, hφ1, hmts0 p, hψ1]
      change p 1 + (e ts) 0 + 1 * w 0 = _
      rw [hw0]
      ring
    have hc1 : (n 1 p) 1 = -p 0 + (e ts) 1 := by
      rw [hnapp, hcoord, hφ1, hmts1 p, hψ1]
      change -p 0 + (e ts) 1 + 1 * w 1 = _
      rw [hw1]
      ring
    refine mem_verticalHallway_of_coordinates _ ⟨?_, ?_⟩ ?_
    · rw [hc0, hδdef]
      linarith
    · rw [hc0, hδdef]
      have := hNub p hp
      linarith
    · rw [hc1]
      linarith
  have hmcam : Continuous (fun t : unitInterval ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom.comp hm.continuous
  have hncont : Continuous n := by
    rw [continuous_induced_rng]
    refine ContinuousAffineMap.continuous_rng (fun p ↦ ?_) ?_
    · change Continuous fun r : unitInterval ↦ m (φ r) p + ψ r • w
      exact ((hmcam.comp hφcont).eval_const p).add (hψcont.smul continuous_const)
    · change Continuous fun r : unitInterval ↦
        ((m (φ r)).toAffineIsometry.toContinuousAffineMap).contLinear
      exact ContinuousAffineMap.continuous_contLinear.comp (hmcam.comp hφcont)
  refine ⟨n, ⟨hm.isConnected, hm.isClosed, hncont, ⟨0, ?_⟩, ?_, ?_, hnhall, hnfinal⟩,
    fun r ↦ α (φ r), hαc.comp hφcont, ?_, ?_, ?_⟩
  · intro p
    rw [hnapp, hφ0, hψ0, zero_smul, add_zero, hm.zero]
    simp
  · intro r
    exact ⟨((α (φ r) : ℝ) : Real.Angle), fun p ↦ by
      rw [hnapp, hnapp, hlift (φ r) p, hlift (φ r) 0]
      simp [rotationMap]
      abel⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hid : n 0 p = p := by
      rw [hnapp, hφ0, hψ0, zero_smul, add_zero, hm.zero]
      rfl
    rw [hid]
    exact hm.initial hp
  · change α (φ 0) = 0
    rw [hφ0, hα0]
  · change α (φ 1) = -(Real.pi / 2)
    rw [hφ1, hts]
  · intro r p
    rw [hnapp, hnapp, hlift (φ r) p, hlift (φ r) 0]
    simp [rotationMap]
    abel

theorem movingSofa_rotationAngle_bound (s : Set Point)
    (hs : IsPaperMovingSofa s) (hArea : 11 / 5 ≤ ClassicalResults.area s) :
    ∃ ω ∈ Set.Icc (Real.arccos (5 / 11 : ℝ)) (Real.pi / 2),
      HasRotationAngle s ω := by
  obtain ⟨q, m, hm, hvol⟩ := canonical_paper_motion_bridge.1 s hs
  set S : Set Point := (fun p ↦ p + q) '' s with hSdef
  obtain ⟨α, e, hαc, hec, hα0, he0, hlift⟩ :=
    exists_continuous_motion_angle_lift m hm.continuous hm.zero
  have hcoord : ∀ (u v : Point) (i : Fin 2), (u + v) i = u i + v i := fun _ _ _ ↦ rfl
  have htransfer : ∀ ω : ℝ, HasRotationAngle S ω → HasRotationAngle s ω := by
    intro ω hω
    have h := hasRotationAngle_image_add S (-q) ω hω
    have himg : (fun p : Point ↦ p + -q) '' S = s := by
      rw [hSdef, Set.image_image]
      simp
    rwa [himg] at h
  have harea : (11 : ℝ) / 5 ≤ (MeasureTheory.volume S).toReal := by
    rw [hSdef, hvol]
    exact hArea
  have hH : ∀ p ∈ S, 0 ≤ p 1 ∧ p 1 ≤ 1 := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_horizontalHallway_coordinates (hm.initial hp)
    exact ⟨h1, h2⟩
  have hLt : ∀ (t : unitInterval) (p : Point), p ∈ S →
      (m t p) 0 ≤ 1 ∧ (m t p) 1 ≤ 1 ∧ (0 ≤ (m t p) 0 ∨ 0 ≤ (m t p) 1) := by
    intro t p hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := (mem_hallway_iff _).mp (hm.subset_hallway t ⟨p, hp, rfl⟩)
    exact ⟨h1, h2, h3⟩
  have hVf : ∀ p ∈ S, 0 ≤ (m 1 p) 0 ∧ (m 1 p) 0 ≤ 1 ∧ (m 1 p) 1 ≤ 1 :=
    fun p hp ↦ mem_verticalHallway_coordinates (hm.final ⟨p, hp, rfl⟩)
  -- the clockwise angle never reaches a counterclockwise quarter of a right angle
  have hquarter : ∀ t : unitInterval, α t ≠ Real.pi / 4 := by
    intro t ht
    set r := Real.sqrt 2 with hrdef
    have hrsq : r * r = 2 := Real.mul_self_sqrt (by norm_num)
    have hrpos : 0 < r := by rw [hrdef]; positivity
    have hc : ((α t : ℝ) : Real.Angle).cos = r / 2 := by
      rw [Real.Angle.cos_coe, ht, Real.cos_pi_div_four]
    have hsn : ((α t : ℝ) : Real.Angle).sin = r / 2 := by
      rw [Real.Angle.sin_coe, ht, Real.sin_pi_div_four]
    have hmul : ∀ x : ℝ, r * (r / 2 * x) = x := by
      intro x
      linear_combination x / 2 * hrsq
    have hbound : MeasureTheory.volume S ≤ ENNReal.ofReal r := by
      refine volume_le_of_subset_horizontalBand
        (f := fun y ↦ min (y + (r - r * (e t) 0)) (-y + (r - r * (e t) 1)) - r)
        (c := r) (by fun_prop) hrpos.le ?_
      intro p hp
      obtain ⟨hy0, hy1⟩ := hH p hp
      obtain ⟨hx1, hx2, hx3⟩ := hLt t p hp
      have hm0 : (m t p) 0 = r / 2 * p 0 - r / 2 * p 1 + (e t) 0 := by
        rw [hlift t p, hcoord, rotationMap_apply_zero, hc, hsn]
      have hm1 : (m t p) 1 = r / 2 * p 0 + r / 2 * p 1 + (e t) 1 := by
        rw [hlift t p, hcoord, rotationMap_apply_one, hc, hsn]
      rw [hm0] at hx1
      rw [hm1] at hx2
      rw [hm0, hm1] at hx3
      have g1 : p 0 - p 1 + r * (e t) 0 ≤ r := by
        have h := mul_le_mul_of_nonneg_left hx1 hrpos.le
        rwa [mul_add, mul_sub, hmul, hmul, mul_one] at h
      have g2 : p 0 + p 1 + r * (e t) 1 ≤ r := by
        have h := mul_le_mul_of_nonneg_left hx2 hrpos.le
        rwa [mul_add, mul_add, hmul, hmul, mul_one] at h
      have hmin := min_le_left (p 1 + (r - r * (e t) 0)) (-p 1 + (r - r * (e t) 1))
      have hmin' := min_le_right (p 1 + (r - r * (e t) 0)) (-p 1 + (r - r * (e t) 1))
      refine ⟨⟨hy0, hy1⟩, ?_, ?_⟩
      · simp only
        rcases hx3 with h | h
        · have h' := mul_le_mul_of_nonneg_left h hrpos.le
          rw [mul_zero, mul_add, mul_sub, hmul, hmul] at h'
          linarith
        · have h' := mul_le_mul_of_nonneg_left h hrpos.le
          rw [mul_zero, mul_add, mul_add, hmul, hmul] at h'
          linarith
      · simp only
        have hle' : p 0 ≤ min (p 1 + (r - r * (e t) 0)) (-p 1 + (r - r * (e t) 1)) :=
          le_min (by linarith) (by linarith)
        linarith
    have hle : (MeasureTheory.volume S).toReal ≤ r := ENNReal.toReal_le_of_le_ofReal hrpos.le hbound
    nlinarith [hrsq, hrpos, harea, hle, sq_nonneg (r - 11 / 5)]
  have hquarter' : ∀ t : unitInterval, α t < Real.pi / 4 := by
    intro t
    rcases lt_trichotomy (α t) (Real.pi / 4) with h | h | h
    · exact h
    · exact absurd h (hquarter t)
    · exfalso
      have hmem : Real.pi / 4 ∈ Set.range α := by
        refine intermediate_value_univ 0 t hαc ?_
        rw [hα0]
        exact ⟨by positivity, h.le⟩
      obtain ⟨u, hu⟩ := hmem
      exact hquarter u hu
  -- the final clockwise angle has small cosine
  have hcosbound : |Real.cos (α 1)| ≤ 5 / 11 := by
    by_contra hcon
    push Not at hcon
    have habs : (0 : ℝ) < |Real.cos (α 1)| := by linarith
    have hne : Real.cos (α 1) ≠ 0 := by
      intro h0
      rw [h0] at habs
      simp at habs
    have hbound : MeasureTheory.volume S ≤ ENNReal.ofReal (1 / |Real.cos (α 1)|) := by
      refine le_trans (MeasureTheory.measure_mono ?_)
        (volume_horizontalBand_inter_le (Real.cos (α 1)) (-Real.sin (α 1)) (-(e 1) 0) hne)
      intro p hp
      obtain ⟨hy0, hy1⟩ := hH p hp
      obtain ⟨hv0, hv1, -⟩ := hVf p hp
      have hm0 : (m 1 p) 0 = Real.cos (α 1) * p 0 - Real.sin (α 1) * p 1 + (e 1) 0 := by
        rw [hlift 1 p, hcoord, rotationMap_apply_zero, Real.Angle.cos_coe, Real.Angle.sin_coe]
      rw [hm0] at hv0 hv1
      exact ⟨⟨hy0, hy1⟩, by linarith, by linarith⟩
    have hle : (MeasureTheory.volume S).toReal ≤ 1 / |Real.cos (α 1)| :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hbound
    have hlt : 1 / |Real.cos (α 1)| < 11 / 5 := by
      rw [div_lt_iff₀ habs]
      linarith
    linarith
  -- the angle constants
  set A := Real.arccos (5 / 11 : ℝ) with hAdef
  have hcosA : Real.cos A = 5 / 11 := Real.cos_arccos (by norm_num) (by norm_num)
  have hApi2 : A ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (by norm_num)
  have hApi : A ≤ Real.pi := Real.arccos_le_pi _
  have hAquarter : Real.pi / 4 < A := by
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs2pos : (0 : ℝ) < Real.sqrt 2 := by positivity
    have hlt : (5 : ℝ) / 11 < Real.sqrt 2 / 2 := by nlinarith
    have h4 : Real.arccos (Real.sqrt 2 / 2) = Real.pi / 4 := by
      rw [← Real.cos_pi_div_four, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
    rw [hAdef, ← h4]
    exact Real.arccos_lt_arccos (by norm_num) hlt (by nlinarith)
  have hfinal : α 1 ≤ -A := by
    by_contra hcon
    push Not at hcon
    have habs : |α 1| < A := by
      rw [abs_lt]
      exact ⟨by linarith, lt_trans (hquarter' 1) hAquarter⟩
    have hmono : Real.cos A < Real.cos |α 1| :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hApi habs
    rw [Real.cos_abs] at hmono
    have := le_abs_self (Real.cos (α 1))
    linarith
  have hm0e : ∀ t : unitInterval, m t 0 = e t := by
    intro t
    rw [hlift t 0]
    simp [rotationMap]
  have hrot : HasRotationAngle S (-α 1) := by
    refine ⟨m, hm.isPaperMotion, α, hαc, hα0, by ring, fun t p ↦ ?_⟩
    rw [hlift t p, hm0e t]
  by_cases hbig : -α 1 ≤ Real.pi / 2
  · exact ⟨-α 1, ⟨by linarith, hbig⟩, htransfer _ hrot⟩
  · push Not at hbig
    refine ⟨Real.pi / 2, ⟨hApi2, le_refl _⟩, htransfer _ ?_⟩
    -- the intermediate right-angle time
    have hmemr : -(Real.pi / 2) ∈ Set.range α := by
      refine intermediate_value_univ 1 0 hαc ?_
      rw [hα0]
      exact ⟨by linarith, by linarith [Real.pi_pos]⟩
    obtain ⟨ts, hts⟩ := hmemr
    exact hasRotationAngle_right_of_reaches_right S m hm α e hαc hα0 hlift ts hts

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Sofa.BalancedRightAngle`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Sofa / Balanced Right Angle
-/

public section

noncomputable section

namespace MovingSofa

theorem exists_dominating_balancedRightAngleSofa (s : Set Point)
    (hs : IsPaperMovingSofa s) (harea : (11 : ℝ) / 5 ≤ ClassicalResults.area s) :
    ∃ s' : Set Point, IsBalancedMaximumSofa s' (Real.pi / 2) ∧
      ClassicalResults.area s ≤ ClassicalResults.area s' := by
  obtain ⟨ω, hω, hrot⟩ := movingSofa_rotationAngle_bound s hs harea
  have hω0 : 0 < ω := lt_of_lt_of_le (Real.arccos_pos.2 (by norm_num)) hω.1
  obtain ⟨K, -, hBsofa, hBmax⟩ := exists_balancedMaximumSofa ω hω0 hω.2
  have hsB : ClassicalResults.area s ≤
      ClassicalResults.area ((K.val : Set Point) \ capNiche K) := hBmax s hrot
  obtain ⟨α, hrotB⟩ := balancedMaximumSofa_rightAngle _ ω hBsofa hω (harea.trans hsB)
  obtain ⟨K', -, hS'sofa, hS'max⟩ :=
    exists_balancedMaximumSofa (Real.pi / 2) (by positivity) le_rfl
  refine ⟨(K'.val : Set Point) \ capNiche K', hS'sofa, hsB.trans ?_⟩
  calc ClassicalResults.area ((K.val : Set Point) \ capNiche K)
      = ClassicalResults.area (rotationMap α '' ((K.val : Set Point) \ capNiche K)) :=
        (area_image_rotationMap α _).symm
    _ ≤ _ := hS'max _ hrotB

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Sofa.Maximum`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver's sofa attains the maximum moving-sofa area

The paper's main theorem: Gerver's paper-frame set `paperGerverSofa` is a moving
sofa, and every moving sofa has area at most its area.

The proof splits on the certified lower bound `11 / 5`.  A sofa below that bound
is dominated outright.  A sofa at or above it is dominated by a balanced maximum
sofa of angle `π / 2`, whose cap lies in the special domain and extends to a
triple in the cap-tail space; the area functional is then bounded by `Q`, which
is maximized by Gerver's triple and matches the area functional there.
-/

public section

noncomputable section

namespace MovingSofa

theorem paperGerverSofa_maximum :
    IsPaperMovingSofa paperGerverSofa ∧
      ∀ s : Set Point, IsPaperMovingSofa s →
        ClassicalResults.area s ≤ ClassicalResults.area paperGerverSofa := by
  -- `G` is a moving sofa in standard position at angle `π / 2`.
  have hstd : IsStandardPosition paperGerverSofa (Real.pi / 2) := by
    rw [gerver_capSupport_identification.2.1]
    exact gerver_capSupport_identification.2.2.1
  -- `G` is monotone, so the sofa-area identity applies to it.
  have hmono : ∃ s₀ : Set Point, IsStandardPosition s₀ (Real.pi / 2) ∧
      paperGerverSofa = monotonization s₀ (Real.pi / 2) :=
    ⟨paperGerverSofa, hstd, (gerver_paperNiche_identification.2.2.1).symm⟩
  -- The certified lower bound, transported along the path identification.
  have hG : (11 : ℝ) / 5 ≤ ClassicalResults.area paperGerverSofa := by
    rw [← gerver_canonical_paper_literal.1]
    exact gerver_area_lower_bound.2
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hm, -⟩ := hstd.2.1
    exact ⟨m, hm⟩
  intro s hs
  by_cases harea : (11 : ℝ) / 5 ≤ ClassicalResults.area s
  · -- `K_G` maximizes `Q`, and `Q (K_G, B, D) = A (K_G) = |G|`.
    obtain ⟨X, hK, hB, hD, hmax⟩ := gerver_upperBoundQ_maximum
    have hGarea : rightAngleAreaFunctional X.cap.val = ClassicalResults.area paperGerverSofa :=
      capAreaFunctional_eq_sofaArea paperGerverSofa (Real.pi / 2) hmono X.cap.val hK
    -- Dominate `S` by a balanced maximum sofa of angle `π / 2`.
    obtain ⟨s', ⟨hmono', L, hL, hbalanced⟩, hdom⟩ :=
      exists_dominating_balancedRightAngleSofa s hs harea
    obtain ⟨M, hM⟩ := specialCap_isConvexDomain.2.2.1 L hbalanced
    obtain ⟨Y, rfl, hYR, hYL⟩ := exists_canonicalCapTail M
    calc
      ClassicalResults.area s ≤ ClassicalResults.area s' := hdom
      _ = rightAngleAreaFunctional L :=
        (capAreaFunctional_eq_sofaArea s' (Real.pi / 2) hmono' L hL).symm
      _ = rightAngleAreaFunctional Y.cap.val := by rw [hM]
      _ ≤ upperBoundQ Y := areaFunctional_le_upperBoundQ Y hYR hYL
      _ ≤ upperBoundQ X := hmax Y
      _ = rightAngleAreaFunctional X.cap.val := (gerver_upperBoundQ_matches X hK hB hD).symm
      _ = ClassicalResults.area paperGerverSofa := hGarea
  · exact (le_of_not_ge harea).trans hG

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Motion.CanonicalUpperBound`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The paper's upper bound transported to the canonical target

The paper's main theorem bounds the real area of every moving sofa in the paper normalization by
the area of the paper Gerver sofa. The canonical and paper Gerver sets coincide, every admissible
set is a paper moving sofa, and admissible sets are compact, so the comparison of real areas is a
comparison of Lebesgue measures.
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped unitInterval

/-- Every admissible set has Lebesgue measure at most that of Gerver's sofa. -/
theorem areaUpperBound : AreaUpperBound := by
  intro s m hs
  have harea := paperGerverSofa_maximum.2 s (canonical_paper_motion_bridge.2 s m hs)
  rw [← gerver_canonical_paper_literal.1] at harea
  obtain ⟨-, -, hfinS⟩ := canonical_motion_compactness s m hs
  obtain ⟨mG, hmG⟩ := isMovingSofa_gerversSofa
  obtain ⟨-, -, hfinG⟩ := canonical_motion_compactness gerversSofa mG hmG
  exact (real_area_le_iff_volume_le s gerversSofa hfinS hfinG).mp harea

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The moving sofa problem: proofs

The imported development proves uniqueness of Gerver's defining parameters in
`MovingSofa.GerversSofa.ABφθSpec.existsUnique` and admissibility of the resulting shape in
`MovingSofa.isMovingSofa_gerversSofa`. The main theorem combines this admissibility result
with the proved area upper bound `MovingSofa.areaUpperBound`.
-/

public section

namespace MovingSofa

open MeasureTheory

/-- Gerver's sofa attains the sofa constant (Baek, arXiv:2411.19826). -/
theorem sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa := by
  apply optimality_of_areaUpperBound
  exact areaUpperBound

end MovingSofa

end

end
