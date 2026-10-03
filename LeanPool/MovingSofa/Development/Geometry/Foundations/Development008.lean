/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development006
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development007
/-!
# Moving sofa: related mathematical developments

* `Cap.Foundations.Development008`.
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

* `Cap.Monotone`.
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
# Cap / Monotone
-/

public section

noncomputable section
namespace MovingSofa

/-- Removing the niche from a cap leaves a compact set. -/
lemma isCompact_sdiff_capNiche {ω : ℝ} (K : CapSpace ω) :
    IsCompact ((K.val : Set Point) \ capNiche K) := by
  have hopen : IsOpen (⋃ t ∈ Set.Ioo 0 ω, innerQuadrant (K.val : Set Point) t) := by
    apply isOpen_iUnion
    intro t
    apply isOpen_iUnion
    intro _
    exact (isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt (by fun_prop) continuous_const)
  have heq : (K.val : Set Point) \ capNiche K =
      (K.val : Set Point) \ ⋃ t ∈ Set.Ioo 0 ω, innerQuadrant (K.val : Set Point) t := by
    ext p
    simp only [Set.mem_sdiff, capNiche, Set.mem_inter_iff]
    constructor
    · rintro ⟨hp, hn⟩
      exact ⟨hp, fun h ↦ hn ⟨K.subset_capFan hp, h⟩⟩
    · rintro ⟨hp, hn⟩
      exact ⟨hp, fun h ↦ hn h.2⟩
  rw [heq]
  exact K.val.isCompact.diff hopen

private theorem supportValue_sdiff_capNiche_eq {ω t : ℝ} (K : CapSpace ω)
    (hN : capNiche K ⊆ (K.val : Set Point))
    (ht : t ∈ Set.Icc 0 (ω + Real.pi / 2)) :
    supportValue ((K.val : Set Point) \ capNiche K) (t : Real.Angle) =
      supportValue K.val (t : Real.Angle) := by
  let S : Set Point := (K.val : Set Point) \ capNiche K
  have hNupper : capNiche K ⊆ (K.val : Set Point) \ capUpperBoundary K :=
    (cap_niche_connected_iff K).1.mp hN
  have hScompact : IsCompact S := isCompact_sdiff_capNiche K
  have hSsub : S ⊆ (K.val : Set Point) := Set.sdiff_subset
  have hSnonempty : S.Nonempty := by
    have hcorners := (cap_niche_connected_iff K).2.1.mp hNupper
    exact ((cap_niche_connected_iff K).2.2.mp hcorners).nonempty
  obtain ⟨p, hp⟩ := exposedEdge_nonempty K.val (t : Real.Angle)
  have hpupper : p ∈ capUpperBoundary K := by
    rw [capUpperBoundary]
    exact Set.mem_iUnion₂.mpr ⟨t, ht, hp⟩
  have hpS : p ∈ S := by
    refine ⟨hp.1, fun hpN ↦ ?_⟩
    exact (hNupper hpN).2 hpupper
  symm
  apply supportValue_eq_of_subset_of_inner_le hSnonempty hSsub
  intro q hq
  calc
    inner ℝ q (normalVector (t : Real.Angle)) ≤ supportValue K.val (t : Real.Angle) :=
      inner_le_supportValue K.val hq _
    _ = inner ℝ p (normalVector (t : Real.Angle)) := hp.2.symm
    _ ≤ supportValue S (t : Real.Angle) :=
      inner_le_supportValue_of_isCompact hScompact hpS _

private theorem mem_supportingHallway_of_mem_sdiff_capNiche {ω t : ℝ}
    (K : CapSpace ω) (ht : t ∈ Set.Icc 0 ω) {p : Point}
    (hp : p ∈ (K.val : Set Point) \ capNiche K) :
    p ∈ supportingHallway (K.val : Set Point) (t : Real.Angle) := by
  obtain ⟨hhall, _, _, _, _, _, _, houter, hinner⟩ :=
    rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)
  rw [hhall]
  refine ⟨?_, ?_⟩
  · rw [houter]
    exact ⟨inner_le_supportValue K.val hp.1 _, inner_le_supportValue K.val hp.1 _⟩
  · intro hq
    rw [hinner] at hq
    change p ∈ innerQuadrant (K.val : Set Point) t at hq
    by_cases ht0 : t = 0
    · subst t
      have h := hq.2
      change inner ℝ p (normalVector ((0 + Real.pi / 2 : ℝ) : Real.Angle)) <
        supportValue K.val ((0 + Real.pi / 2 : ℝ) : Real.Angle) - 1 at h
      rw [zero_add, K.property.2.2.2.1] at h
      have hf := (K.subset_capFan hp.1).2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hf
      linarith
    · by_cases htω : t = ω
      · subst t
        have h := hq.1
        change inner ℝ p (normalVector (ω : Real.Angle)) <
          supportValue K.val (ω : Real.Angle) - 1 at h
        rw [K.property.2.2.1] at h
        have hf := (K.subset_capFan hp.1).1
        change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hf
        linarith
      · apply hp.2
        exact ⟨K.subset_capFan hp.1, Set.mem_iUnion₂.mpr
          ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htω⟩, hq⟩⟩

private theorem cap_sdiff_niche_eq_monotonization_self {ω : ℝ} (K : CapSpace ω) :
    (K.val : Set Point) \ capNiche K = monotonization (K.val : Set Point) ω := by
  ext p
  constructor
  · intro hp
    refine ⟨K.subset_stripParallelogram hp.1,
      Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
    exact mem_supportingHallway_of_mem_sdiff_capNiche K ht hp
  · intro hp
    change p ∈ (stripParallelogram ω).1 ∩
      ⋂ t ∈ Set.Icc 0 ω, supportingHallway (K.val : Set Point) (t : Real.Angle) at hp
    have hpstrip := (mem_stripParallelogram_iff ω p).mp hp.1
    have hpFan : p ∈ capFan ω := by
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) ∧
        0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      refine ⟨hpstrip.2.1, ?_⟩
      simpa [normalVector, frame, PiLp.inner_apply] using hpstrip.1.1
    have hpK : p ∈ (K.val : Set Point) := by
      apply K.mem_of_mem_capFan_of_le_supportValue hpFan
      intro u hu
      rcases hu with hu | hu
      · have hhall := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 u) hu
        obtain ⟨hhallEq, _, _, _, _, _, _, houter, _⟩ :=
          rotatingHallwayParts_formulas (K.val : Set Point) (u : Real.Angle)
        rw [hhallEq, houter] at hhall
        exact hhall.1.1
      · let t := u - Real.pi / 2
        have ht : t ∈ Set.Icc 0 ω := by
          dsimp [t]
          constructor <;> linarith [hu.1, hu.2]
        have hhall := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
        obtain ⟨hhallEq, _, _, _, _, _, _, houter, _⟩ :=
          rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)
        rw [hhallEq, houter] at hhall
        have heq : (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
            (u : Real.Angle) := by
          rw [← Real.Angle.coe_add]
          congr 1
          dsimp [t]
          ring
        have hq := hhall.1.2
        change inner ℝ p
          (normalVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))) ≤
            supportValue K.val
              ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) at hq
        rw [heq] at hq
        exact hq
    refine ⟨hpK, ?_⟩
    rintro ⟨_, hN⟩
    obtain ⟨t, ht, hquad⟩ := Set.mem_iUnion₂.mp hN
    have hhall := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ⟨ht.1.le, ht.2.le⟩
    obtain ⟨hhallEq, _, _, _, _, _, _, _, hinner⟩ :=
      rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)
    rw [hhallEq] at hhall
    apply hhall.2
    rw [hinner]
    exact hquad

private theorem cap_eq_capOfSofa_sdiff_capNiche {ω : ℝ} (K : CapSpace ω)
    (hN : capNiche K ⊆ (K.val : Set Point)) :
    (K.val : Set Point) = capOfSofa ((K.val : Set Point) \ capNiche K) ω := by
  let S : Set Point := (K.val : Set Point) \ capNiche K
  have hsupp (t : ℝ) (ht : t ∈ Set.Icc 0 (ω + Real.pi / 2)) :
      supportValue S (t : Real.Angle) = supportValue K.val (t : Real.Angle) :=
    supportValue_sdiff_capNiche_eq K hN ht
  ext p
  constructor
  · intro hp
    refine ⟨K.subset_stripParallelogram hp,
      Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
    obtain ⟨_, _, _, _, _, _, _, houter, _⟩ :=
      rotatingHallwayParts_formulas S (t : Real.Angle)
    rw [houter]
    change inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue S (t : Real.Angle) ∧
      inner ℝ p
          (normalVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))) ≤
        supportValue S ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))
    have h₀ := hsupp t ⟨ht.1, ht.2.trans (le_add_of_nonneg_right (by positivity))⟩
    have h₁ := hsupp (t + Real.pi / 2)
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩
    simp only [Real.Angle.coe_add] at h₁
    rw [h₀, h₁]
    exact ⟨inner_le_supportValue K.val hp _, inner_le_supportValue K.val hp _⟩
  · intro hp
    have hpstrip := (mem_stripParallelogram_iff ω p).mp hp.1
    have hpFan : p ∈ capFan ω := by
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) ∧
        0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      refine ⟨hpstrip.2.1, ?_⟩
      simpa [normalVector, frame, PiLp.inner_apply] using hpstrip.1.1
    apply K.mem_of_mem_capFan_of_le_supportValue hpFan
    intro u hu
    rcases hu with hu | hu
    · have hq := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 u) hu
      obtain ⟨_, _, _, _, _, _, _, houter, _⟩ :=
        rotatingHallwayParts_formulas S (u : Real.Angle)
      rw [houter] at hq
      have heq := hsupp u
        ⟨hu.1, hu.2.trans (le_add_of_nonneg_right (by positivity))⟩
      have hq' := hq.1
      change inner ℝ p (normalVector (u : Real.Angle)) ≤
        supportValue S (u : Real.Angle) at hq'
      rw [heq] at hq'
      exact hq'
    · let t := u - Real.pi / 2
      have ht : t ∈ Set.Icc 0 ω := by
        dsimp [t]
        constructor <;> linarith [hu.1, hu.2]
      have hq := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
      obtain ⟨_, _, _, _, _, _, _, houter, _⟩ :=
        rotatingHallwayParts_formulas S (t : Real.Angle)
      rw [houter] at hq
      have hang : (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
          (u : Real.Angle) := by
        rw [← Real.Angle.coe_add]
        congr 1
        dsimp [t]
        ring
      have heq := hsupp u
        ⟨(by positivity : 0 ≤ Real.pi / 2).trans hu.1,
          hu.2⟩
      have hq' := hq.2
      change inner ℝ p
        (normalVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))) ≤
          supportValue S
            ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) at hq'
      rw [hang, heq] at hq'
      exact hq'

theorem cap_isMonotoneCap_iff_niche_subset {ω : ℝ} (K : CapSpace ω) :
    (∃ s₀ : Set Point, IsStandardPosition s₀ ω ∧
      (K.val : Set Point) = capOfSofa (monotonization s₀ ω) ω) ↔
      capNiche K ⊆ (K.val : Set Point) := by
  constructor
  · rintro ⟨s₀, hs₀, hK⟩
    let S := monotonization s₀ ω
    have hstructure : S = (K.val : Set Point) \ capNiche K :=
      monotoneSofa_structure S ω ⟨s₀, hs₀, rfl⟩ K hK
    have hconn : IsConnected S := standardPosition_monotonization_connected s₀ ω hs₀
    exact (cap_niche_connected_iff K).1.mpr
      ((cap_niche_connected_iff K).2.1.mpr
        ((cap_niche_connected_iff K).2.2.mpr (hstructure ▸ hconn)))
  · intro hN
    let S : Set Point := (K.val : Set Point) \ capNiche K
    have hNupper : capNiche K ⊆ (K.val : Set Point) \ capUpperBoundary K :=
      (cap_niche_connected_iff K).1.mp hN
    have hcorners := (cap_niche_connected_iff K).2.1.mp hNupper
    have hSconn : IsConnected S := (cap_niche_connected_iff K).2.2.mp hcorners
    have hScompact : IsCompact S := isCompact_sdiff_capNiche K
    have hSsub : S ⊆ monotonization (K.val : Set Point) ω := by
      rw [← cap_sdiff_niche_eq_monotonization_self K]
    have hrot : HasRotationAngle S ω :=
      hasRotationAngle_of_subset_supportingHallways (K.val : Set Point) S ω
        K.val.nonempty K.val.isCompact K.property.1.le K.property.2.2.1
        K.property.2.2.2.1 hSconn hScompact.isClosed hSsub
    have hsuppω : supportValue S (ω : Real.Angle) = 1 := by
      rw [supportValue_sdiff_capNiche_eq K hN
        ⟨K.property.1.le, le_add_of_nonneg_right (by positivity)⟩,
        K.property.2.2.1]
    have hsuppπ : supportValue S ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
      rw [supportValue_sdiff_capNiche_eq K hN
        ⟨by positivity, by linarith [K.property.1]⟩,
        K.property.2.2.2.1]
    have hstandard : IsStandardPosition S ω :=
      ⟨hScompact, hrot, K.property.1, K.property.2.1, hsuppω, hsuppπ⟩
    have hcap : (K.val : Set Point) = capOfSofa S ω :=
      cap_eq_capOfSofa_sdiff_capNiche K hN
    have hhall (t : ℝ) (ht : t ∈ Set.Icc 0 ω) :
        supportingHallway S (t : Real.Angle) =
          supportingHallway (K.val : Set Point) (t : Real.Angle) := by
      unfold supportingHallway
      congr 1
      funext p
      simp only [supportingPlacement]
      rw [supportValue_sdiff_capNiche_eq K hN
          ⟨ht.1, ht.2.trans (le_add_of_nonneg_right (by positivity))⟩]
      have hshift : t + Real.pi / 2 ∈ Set.Icc 0 (ω + Real.pi / 2) :=
        ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩
      have h₁ := supportValue_sdiff_capNiche_eq K hN hshift
      simp only [Real.Angle.coe_add] at h₁
      rw [h₁]
    have hmon : monotonization S ω = S := by
      calc
        monotonization S ω = monotonization (K.val : Set Point) ω := by
          unfold monotonization
          congr 1
          apply Set.iInter_congr
          intro t
          apply Set.iInter_congr
          exact hhall t
        _ = S := (cap_sdiff_niche_eq_monotonization_self K).symm
    exact ⟨S, hstandard, by rw [hmon]; exact hcap⟩

end MovingSofa

end

end

end

end

end

end
