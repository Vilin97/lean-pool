/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Small
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Topology.Instances.Shrink
/-!
# Transporting local-field structures to a small representative

This file records the valuation and topology on the `Type 0` representative
of an arbitrary-universe nonarchimedean local field.
-/

@[expose] public section

noncomputable
section

namespace LocalFieldTheory

open ValuativeRel Filter
open scoped Topology

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem smallLocalField : Small.{0} K :=
  nonarchimedeanLocalField_small K

/-- The canonical valuation pulled back to the small carrier. -/
noncomputable def shrinkLocalFieldValuation :
    letI : Small.{0} K := smallLocalField K
    Valuation (Shrink.{0} K) (ValueGroupWithZero K) := by
  letI : Small.{0} K := smallLocalField K
  exact (valuation K).comap (Shrink.ringEquiv K).toRingHom

/-- The valuative relation on the small carrier, transported from `K`. -/
@[instance_reducible]
noncomputable def shrinkLocalFieldValuativeRel :
    letI : Small.{0} K := smallLocalField K
    ValuativeRel (Shrink.{0} K) := by
  letI : Small.{0} K := smallLocalField K
  exact ValuativeRel.ofValuation (shrinkLocalFieldValuation K)

/-- The small carrier inherits local compactness from `K`. -/
theorem shrinkLocalField_locallyCompact :
    letI : Small.{0} K := smallLocalField K
    LocallyCompactSpace (Shrink.{0} K) := by
  let : Small.{0} K := smallLocalField K
  exact (Shrink.homeomorph K).symm.isOpenEmbedding.locallyCompactSpace

/-- The pulled-back valuative relation is nontrivial. -/
theorem shrinkLocalField_isNontrivial :
    letI : Small.{0} K := smallLocalField K
    letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    ValuativeRel.IsNontrivial (Shrink.{0} K) := by
  let : Small.{0} K := smallLocalField K
  let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
  let v := shrinkLocalFieldValuation K
  let : v.Compatible := Valuation.Compatible.ofValuation v
  have hvK : (valuation K).IsNontrivial :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (valuation K)).mp inferInstance
  have hvS : v.IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := hvK.exists_val_nontrivial
    refine ⟨(Shrink.ringEquiv K).symm x, ?_, ?_⟩
    · simpa [v, shrinkLocalFieldValuation] using hx0
    · simpa [v, shrinkLocalFieldValuation] using hx1
  exact (ValuativeRel.isNontrivial_iff_isNontrivial v).2 hvS

/-- Strict valuation comparisons are preserved by the small-carrier ring
equivalence. -/
theorem shrinkLocalField_valuation_lt_iff :
    letI : Small.{0} K := smallLocalField K
    letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    ∀ x y : Shrink.{0} K,
      valuation (Shrink.{0} K) x < valuation (Shrink.{0} K) y ↔
        valuation K (Shrink.ringEquiv K x) <
          valuation K (Shrink.ringEquiv K y) := by
  let : Small.{0} K := smallLocalField K
  let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
  intro x y
  let v := shrinkLocalFieldValuation K
  let : v.Compatible := Valuation.Compatible.ofValuation v
  calc
    valuation (Shrink.{0} K) x < valuation (Shrink.{0} K) y
        ↔ x <ᵥ y := (valuation (Shrink.{0} K)).vlt_iff_lt.symm
    _ ↔ v x < v y := v.vlt_iff_lt
    _ ↔ valuation K (Shrink.ringEquiv K x) <
        valuation K (Shrink.ringEquiv K y) := by
          simp [v, shrinkLocalFieldValuation]

/-- The transported topology is compatible with the transported additive
group structure. -/
theorem shrinkLocalField_isTopologicalAddGroup :
    letI : Small.{0} K := smallLocalField K
    IsTopologicalAddGroup (Shrink.{0} K) := by
  let : Small.{0} K := smallLocalField K
  change @IsTopologicalAddGroup (Shrink.{0} K)
    (TopologicalSpace.induced (Shrink.ringEquiv K) inferInstance) _
  exact isTopologicalAddGroup_induced (Shrink.ringEquiv K).toAddMonoidHom

/-- The transported topology is the valuative topology of the pulled-back
valuation. -/
theorem shrinkLocalField_isValuativeTopology :
    letI : Small.{0} K := smallLocalField K
    letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    IsValuativeTopology (Shrink.{0} K) := by
  let : Small.{0} K := smallLocalField K
  let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
  let : IsTopologicalAddGroup (Shrink.{0} K) :=
    shrinkLocalField_isTopologicalAddGroup K
  let e : Shrink.{0} K ≃+* K := Shrink.ringEquiv K
  let h : Shrink.{0} K ≃ₜ K := (Shrink.homeomorph K).symm
  have hnhds (s : Set (Shrink.{0} K)) :
      s ∈ 𝓝 (0 : Shrink.{0} K) ↔ h '' s ∈ 𝓝 (0 : K) := by
    have h0 : h (0 : Shrink.{0} K) = (0 : K) := by
      change e (0 : Shrink.{0} K) = 0
      exact map_zero e
    calc
      s ∈ 𝓝 (0 : Shrink.{0} K) ↔
          h ⁻¹' (h '' s) ∈ 𝓝 (0 : Shrink.{0} K) := by
            rw [Set.preimage_image_eq _ h.injective]
      _ ↔ h '' s ∈ map h (𝓝 (0 : Shrink.{0} K)) := Iff.rfl
      _ ↔ h '' s ∈ 𝓝 (0 : K) := by rw [h.map_nhds_eq, h0]
  have basisK (t : Set K) :
      t ∈ 𝓝 (0 : K) ↔
        ∃ a : K, a ≠ 0 ∧ {z : K | valuation K z < valuation K a} ⊆ t := by
    rw [IsValuativeTopology.mem_nhds_zero_iff]
    constructor
    · rintro ⟨γ, hγ⟩
      obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero K)
      refine ⟨a, ?_, ?_⟩
      · intro ha0
        have hγ0 : (γ : ValueGroupWithZero K) = 0 := by
          simpa [ha0] using ha.symm
        exact γ.ne_zero hγ0
      · simpa [ha] using hγ
    · rintro ⟨a, ha0, hsub⟩
      refine ⟨Units.mk0 (valuation K a) (by simpa using ha0), ?_⟩
      simpa using hsub
  have basisSmall (s : Set (Shrink.{0} K)) :
      (∃ γ : (ValueGroupWithZero (Shrink.{0} K))ˣ,
        {z : Shrink.{0} K | valuation (Shrink.{0} K) z < γ} ⊆ s) ↔
      ∃ a : Shrink.{0} K, a ≠ 0 ∧
        {z : Shrink.{0} K |
          valuation (Shrink.{0} K) z < valuation (Shrink.{0} K) a} ⊆ s := by
    constructor
    · rintro ⟨γ, hγ⟩
      obtain ⟨a, ha⟩ :=
        ValuativeRel.valuation_surjective (γ : ValueGroupWithZero (Shrink.{0} K))
      refine ⟨a, ?_, ?_⟩
      · intro ha0
        have hγ0 : (γ : ValueGroupWithZero (Shrink.{0} K)) = 0 := by
          simpa [ha0] using ha.symm
        exact γ.ne_zero hγ0
      · simpa [ha] using hγ
    · rintro ⟨a, ha0, hsub⟩
      refine ⟨Units.mk0 (valuation (Shrink.{0} K) a) (by simpa using ha0), ?_⟩
      simpa using hsub
  apply IsValuativeTopology.of_zero
  intro s
  rw [hnhds s, basisK, basisSmall]
  constructor
  · rintro ⟨a, ha0, hsub⟩
    refine ⟨e.symm a, by simpa using ha0, ?_⟩
    intro z hz
    have hzK : e z ∈ h '' s := by
      apply hsub
      change valuation K (e z) < valuation K a
      have hv := (shrinkLocalField_valuation_lt_iff K z (e.symm a)).mp hz
      change valuation K (e z) < valuation K (e (e.symm a)) at hv
      simpa only [e.apply_symm_apply] using hv
    change e z ∈ e '' s at hzK
    rcases hzK with ⟨w, hw, hew⟩
    simpa [e.injective hew] using hw
  · rintro ⟨a, ha0, hsub⟩
    refine ⟨e a, by simpa using ha0, ?_⟩
    intro z hz
    have hzS : e.symm z ∈ s := hsub (by
      apply (shrinkLocalField_valuation_lt_iff K (e.symm z) a).2
      change valuation K (e (e.symm z)) < valuation K (e a)
      change valuation K z < valuation K (e a) at hz
      simpa only [e.apply_symm_apply] using hz)
    change z ∈ e '' s
    exact ⟨e.symm z, hzS, e.apply_symm_apply z⟩

/-- The small representative of a nonarchimedean local field is itself a
nonarchimedean local field for the transported structures. -/
theorem shrinkLocalField_isNonarchimedeanLocalField :
    letI : Small.{0} K := smallLocalField K
    letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    IsNonarchimedeanLocalField (Shrink.{0} K) := by
  let : Small.{0} K := smallLocalField K
  let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
  exact {
    toIsValuativeTopology := shrinkLocalField_isValuativeTopology K
    toLocallyCompactSpace := shrinkLocalField_locallyCompact K
    toIsNontrivial := shrinkLocalField_isNontrivial K
  }

section ValuationExtension

universe v w x y

/-- A valuation-extension relation survives transport along compatible field
equivalences.  This applies in particular to the two `Shrink` equivalences. -/
theorem hasExtension_comap_ringEquivs
    {F : Type v} {G : Type w} {F₀ : Type x} {G₀ : Type y}
    [Field F] [Field G] [Field F₀] [Field G₀]
    [Algebra F G] [Algebra F₀ G₀]
    {ΓF ΓG : Type*}
    [LinearOrderedCommGroupWithZero ΓF]
    [LinearOrderedCommGroupWithZero ΓG]
    (eF : F₀ ≃+* F) (eG : G₀ ≃+* G)
    (h : ∀ a : F₀, eG (algebraMap F₀ G₀ a) =
      algebraMap F G (eF a))
    (vF : Valuation F ΓF) (vG : Valuation G ΓG)
    [vF.HasExtension vG] :
    (vF.comap eF.toRingHom).HasExtension
      (vG.comap eG.toRingHom) := by
  constructor
  rw [Valuation.isEquiv_iff_val_le_one]
  intro a
  change vF (eF a) ≤ 1 ↔ vG (eG (algebraMap F₀ G₀ a)) ≤ 1
  rw [h]
  exact (Valuation.HasExtension.val_map_le_one_iff vF vG (eF a)).symm

/-- Equivalent valuations may replace both valuations in an extension
relation.  This is useful when a transported valuation is equivalent, but
not definitionally equal, to the canonical valuation on `Shrink`. -/
theorem hasExtension_of_isEquiv
    {F : Type v} {G : Type w}
    [CommRing F] [Ring G] [Algebra F G]
    {ΓF ΓF' ΓG ΓG' : Type*}
    [LinearOrderedCommMonoidWithZero ΓF]
    [LinearOrderedCommMonoidWithZero ΓF']
    [LinearOrderedCommMonoidWithZero ΓG]
    [LinearOrderedCommMonoidWithZero ΓG']
    (vF : Valuation F ΓF) (vF' : Valuation F ΓF')
    (vG : Valuation G ΓG) (vG' : Valuation G ΓG')
    [vF.HasExtension vG]
    (hF : vF.IsEquiv vF') (hG : vG.IsEquiv vG') :
    vF'.HasExtension vG' := by
  constructor
  intro x y
  have hext : vF.IsEquiv (vG.comap (algebraMap F G)) :=
    Valuation.HasExtension.val_isEquiv_comap
  exact (hF.symm x y).trans
    ((hext x y).trans
      (hG (algebraMap F G x) (algebraMap F G y)))

end ValuationExtension

end LocalFieldTheory
