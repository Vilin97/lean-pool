/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
module

public import LeanPool.HardSphereNBC.HardSphereNBC
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace


/-!
# HardSphereMeasure

Graph, coordinate, and measure constructions for the hard-sphere NBC volume identity.
-/

@[expose] public section

namespace HsVirial

open Set
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The standard finite-index coordinate equivalence used to flatten a hard-sphere
configuration. -/
def hardSphereIndexEquiv (k d : Nat) :
    Fin (k - 1) × Fin d ≃ Fin ((k - 1) * d) :=
  finProdFinEquiv

/-- A finite product of finite product measures is unchanged by currying. -/
lemma measurePreserving_curry_pi
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ α).symm
      (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ)))
      (Measure.pi (fun _ : ι × κ => μ)) := by
  refine ⟨(MeasurableEquiv.curry ι κ α).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (MeasurableEquiv.curry ι κ α).symm.measurable
    (MeasurableSet.pi Set.countable_univ (fun i _ => hs i))]
  have hpre :
      (MeasurableEquiv.curry ι κ α).symm ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext f
    simp [MeasurableEquiv.curry, Equiv.curry, Set.mem_pi]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : ι × κ => μ (s p))).symm

/-- The measurable equivalence from the anchored product of Euclidean spaces to
the usual flat Euclidean coordinate space.  The map only reindexes coordinates:
first each Euclidean block is represented by its real coordinates, then the
two finite indices are flattened. -/
def hardSphereFlattenEquiv (k d : Nat) :
    HardSphereConfiguration k d ≃ᵐ
      EuclideanSpace ℝ (Fin ((k - 1) * d)) :=
  let e₁ := MeasurableEquiv.piCongrRight
    (fun _ : Fin (k - 1) =>
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm)
  let e₂ := (MeasurableEquiv.curry (Fin (k - 1)) (Fin d) ℝ).symm
  let e₃ := MeasurableEquiv.piCongrLeft
    (fun _ : Fin ((k - 1) * d) => ℝ) (hardSphereIndexEquiv k d)
  let e₄ := MeasurableEquiv.toLp 2 (Fin ((k - 1) * d) → ℝ)
  e₁.trans (e₂.trans (e₃.trans e₄))

/-- The coordinate flattening preserves the canonical product Lebesgue measure
on the anchored configuration space. -/
theorem measurePreserving_hardSphereFlattenEquiv (k d : Nat) :
    MeasurePreserving (hardSphereFlattenEquiv k d)
      (volume : Measure (HardSphereConfiguration k d))
      (volume : Measure (EuclideanSpace ℝ (Fin ((k - 1) * d)))) := by
  let e₁ := MeasurableEquiv.piCongrRight
    (fun _ : Fin (k - 1) =>
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm)
  let e₂ := (MeasurableEquiv.curry (Fin (k - 1)) (Fin d) ℝ).symm
  let e₃ := MeasurableEquiv.piCongrLeft
    (fun _ : Fin ((k - 1) * d) => ℝ) (hardSphereIndexEquiv k d)
  let e₄ := MeasurableEquiv.toLp 2 (Fin ((k - 1) * d) → ℝ)
  have h₁ : MeasurePreserving e₁
      (volume : Measure (HardSphereConfiguration k d))
      (volume : Measure (Fin (k - 1) → Fin d → ℝ)) := by
    exact volume_preserving_pi
      (fun _ : Fin (k - 1) =>
        EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d))
  have h₂ : MeasurePreserving e₂
      (volume : Measure (Fin (k - 1) → Fin d → ℝ))
      (volume : Measure (Fin (k - 1) × Fin d → ℝ)) := by
    exact measurePreserving_curry_pi (μ := (volume : Measure ℝ))
  have h₃ : MeasurePreserving e₃
      (volume : Measure (Fin (k - 1) × Fin d → ℝ))
      (volume : Measure (Fin ((k - 1) * d) → ℝ)) := by
    exact volume_measurePreserving_piCongrLeft
      (fun _ : Fin ((k - 1) * d) => ℝ) (hardSphereIndexEquiv k d)
  have h₄ : MeasurePreserving e₄
      (volume : Measure (Fin ((k - 1) * d) → ℝ))
      (volume : Measure (EuclideanSpace ℝ (Fin ((k - 1) * d)))) := by
    exact PiLp.volume_preserving_toLp _
  change MeasurePreserving (e₁.trans (e₂.trans (e₃.trans e₄))) volume volume
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- A measure-preserving measurable equivalence preserves the volume of every
measurable subset. -/
theorem measure_image_eq_of_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β)
    (h : MeasurePreserving e μ ν) {s : Set α} (hs : MeasurableSet s) :
    ν (e '' s) = μ s := by
  rw [← h.map_eq, Measure.map_apply e.measurable (e.measurableSet_image.mpr hs)]
  simp

/-- In particular, every measurable NBC region has the same volume after the
coordinate flattening. -/
theorem hardSphereNBCRegion_flatten_volume
    {k d : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) :
    (volume : Measure (EuclideanSpace ℝ (Fin ((k - 1) * d))))
        (hardSphereFlattenEquiv k d ''
          nbcRegion (V := Fin k)
            (hardSphereActiveExact (k := k) (d := d)) T) =
      (volume : Measure (HardSphereConfiguration k d))
        (nbcRegion (V := Fin k)
          (hardSphereActiveExact (k := k) (d := d)) T) := by
  exact measure_image_eq_of_measurePreserving
    (hardSphereFlattenEquiv k d)
    (measurePreserving_hardSphereFlattenEquiv k d)
    (measurable_hardSphereNBCRegion T)

/-- The same NBC-region volume computed in the flat Euclidean model. -/
def hardSphereNBCVolumeFlat
    {k d : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin ((k - 1) * d)))).real
    (hardSphereFlattenEquiv k d ''
      nbcRegion (V := Fin k)
        (hardSphereActiveExact (k := k) (d := d)) T)

theorem hardSphereNBCVolumeFlat_eq
    {k d : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) :
    hardSphereNBCVolumeFlat (k := k) (d := d) T =
    hardSphereNBCVolume (k := k) (d := d) T := by
  unfold hardSphereNBCVolumeFlat hardSphereNBCVolume
  exact congrArg ENNReal.toReal (hardSphereNBCRegion_flatten_volume T)

/-- The NBC identity is unchanged when the configuration measure is written on
the flat Euclidean coordinate space. -/
theorem hardSphere_nbc_volume_identity_flat
    {k d : Nat} (hk : 2 ≤ k) :
    let _ : NeZero k := ⟨by omega⟩
    (k.factorial : ℝ) *
        |hardSphereBk (k := k) (d := d)| =
      ∑ T ∈ treeUniverse (V := Fin k),
        hardSphereNBCVolumeFlat (k := k) (d := d) T := by
  let _ : NeZero k := ⟨by omega⟩
  calc
    (k.factorial : ℝ) *
        |hardSphereBk (k := k) (d := d)| =
      ∑ T ∈ treeUniverse (V := Fin k),
        hardSphereNBCVolume (k := k) (d := d) T :=
      hardSphere_nbc_volume_identity hk
    _ = ∑ T ∈ treeUniverse (V := Fin k),
        hardSphereNBCVolumeFlat (k := k) (d := d) T := by
      apply Finset.sum_congr rfl
      intro T hT
      exact (hardSphereNBCVolumeFlat_eq T).symm

end

end HsVirial
