/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.Euclidean
public import LeanPool.CoarseGraining.Homogenization.Geometry.BoundedMeasurableDomain

/-!
# Normalized `L^p` quantities on bounded measurable domains

The normalized measure of a `BoundedMeasurableDomain` is the mathematical
meaning of the manuscript notation `fint_U`.  Extended norms are kept in
`ℝ≥0∞`; a finite real value is exposed only together with a `MemLp` witness.
The ambient `Vec d` norm remains untouched: the Euclidean vector lane below
uses the explicit function `euclideanNorm`.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal

namespace BoundedMeasurableDomain

/-- The extended normalized `L^p` seminorm, with respect to normalized volume. -/
noncomputable def normalizedLpENorm {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [ENorm E] (p : ℝ≥0∞) (f : Vec d → E) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then
    MeasureTheory.eLpNormEssSup f U.normalizedVolume
  else MeasureTheory.eLpNorm' f p.toReal U.normalizedVolume

/-- On measurable representatives the manuscript seminorm agrees with Mathlib's
`eLpNorm`. The explicit moment definition also preserves the manuscript's essential
supremum for arbitrary representatives, without imposing a measurability convention. -/
theorem normalizedLpENorm_eq_eLpNorm {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [TopologicalSpace E] [ENorm E] (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MeasureTheory.AEStronglyMeasurable f U.normalizedVolume) :
    U.normalizedLpENorm p f = MeasureTheory.eLpNorm f p U.normalizedVolume := by
  simp only [normalizedLpENorm, MeasureTheory.eLpNorm, hf, ite_true]

/-- Membership in `L^p` is unchanged by the strictly positive finite volume normalization. -/
theorem memLp_normalizedVolume_iff {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E] (p : ℝ≥0∞) (f : Vec d → E) :
    MeasureTheory.MemLp f p U.normalizedVolume ↔
      MeasureTheory.MemLp f p U.restrictedVolume := by
  constructor
  · intro hf
    have hrestricted : U.restrictedVolume =
        MeasureTheory.volume (U : Set (Vec d)) • U.normalizedVolume := by
      simp [normalizedVolume, smul_smul, ENNReal.mul_inv_cancel U.volume_ne_zero U.volume_ne_top]
    rw [hrestricted]
    exact hf.smul_measure U.volume_ne_top
  · intro hf
    change MeasureTheory.MemLp f p
      ((MeasureTheory.volume (U : Set (Vec d)))⁻¹ • U.restrictedVolume)
    exact hf.smul_measure (ENNReal.inv_ne_top.2 U.volume_ne_zero)

/-- The normalized extended norm, packaged with the finiteness supplied by `MemLp`. -/
noncomputable def normalizedLpFiniteENorm {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E] (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MeasureTheory.MemLp f p U.normalizedVolume) :
    {q : ℝ≥0∞ // q ≠ ∞} :=
  ⟨U.normalizedLpENorm p f, by
    rw [U.normalizedLpENorm_eq_eLpNorm p f hf.aestronglyMeasurable]
    exact hf.eLpNorm_ne_top⟩

/-- The finite real normalized `L^p` value certified by a `MemLp` witness. -/
noncomputable def normalizedLpNorm {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E] (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MeasureTheory.MemLp f p U.normalizedVolume) : ℝ :=
  (U.normalizedLpFiniteENorm p f hf).1.toReal

/-- The extended normalized `L^p` value depends only on the normalized-volume
almost-everywhere representative. -/
theorem normalizedLpENorm_congr_ae {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [ENorm E] (p : ℝ≥0∞) {f g : Vec d → E}
    (hfg : f =ᵐ[U.normalizedVolume] g) :
    U.normalizedLpENorm p f = U.normalizedLpENorm p g := by
  unfold normalizedLpENorm
  rw [MeasureTheory.eLpNormEssSup_congr_ae hfg, MeasureTheory.eLpNorm'_congr_ae hfg]

/-- A proof-carrying finite normalized `L^p` value depends only on the
normalized-volume almost-everywhere representative. -/
theorem normalizedLpNorm_congr_ae {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E] (p : ℝ≥0∞)
    {f g : Vec d → E} (hf : MeasureTheory.MemLp f p U.normalizedVolume)
    (hg : MeasureTheory.MemLp g p U.normalizedVolume)
    (hfg : f =ᵐ[U.normalizedVolume] g) :
    U.normalizedLpNorm p f hf = U.normalizedLpNorm p g hg := by
  exact congrArg ENNReal.toReal (U.normalizedLpENorm_congr_ae p hfg)

theorem normalizedLpFiniteENorm_value {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E] (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MeasureTheory.MemLp f p U.normalizedVolume) :
    (U.normalizedLpFiniteENorm p f hf).1 = U.normalizedLpENorm p f :=
  rfl

theorem normalizedLpFiniteENorm_ne_top {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E] (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MeasureTheory.MemLp f p U.normalizedVolume) :
    (U.normalizedLpFiniteENorm p f hf).1 ≠ ∞ :=
  (U.normalizedLpFiniteENorm p f hf).2

/-- The `p`-moment with respect to normalized volume.  Its use in the finite-
`p` characterization below is justified by the accompanying `MemLp` witness. -/
noncomputable def normalizedLpMoment {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞) (f : Vec d → E) : ℝ :=
  ∫ x, ‖f x‖ ^ p.toReal ∂U.normalizedVolume

/-- The normalized `p`-moment depends only on the normalized-volume
almost-everywhere representative. -/
theorem normalizedLpMoment_congr_ae {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞) {f g : Vec d → E}
    (hfg : f =ᵐ[U.normalizedVolume] g) :
    U.normalizedLpMoment p f = U.normalizedLpMoment p g := by
  unfold normalizedLpMoment
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

/-- For finite `p ≥ 1`, the normalized real norm is exactly the manuscript
quantity `(fint_U ‖f‖^p)^(1/p)`. -/
theorem normalizedLpNorm_eq_normalizedLpMoment_rpow {d : ℕ}
    (U : BoundedMeasurableDomain d) {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (f : Vec d → E)
    (hf : MeasureTheory.MemLp f p U.normalizedVolume) :
    U.normalizedLpNorm p f hf = (U.normalizedLpMoment p f) ^ p.toReal⁻¹ := by
  have hp_zero : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp_one)
  change (U.normalizedLpENorm p f).toReal = (U.normalizedLpMoment p f) ^ p.toReal⁻¹
  rw [U.normalizedLpENorm_eq_eLpNorm p f hf.aestronglyMeasurable]
  rw [hf.eLpNorm_eq_integral_rpow_norm hp_zero hp_top]
  change
    (ENNReal.ofReal ((∫ x, ‖f x‖ ^ p.toReal ∂U.normalizedVolume) ^ p.toReal⁻¹)).toReal =
      (∫ x, ‖f x‖ ^ p.toReal ∂U.normalizedVolume) ^ p.toReal⁻¹
  exact ENNReal.toReal_ofReal <| Real.rpow_nonneg
    (MeasureTheory.integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg (f x)) _) _

/-- At `p = ∞`, the normalized extended norm is Mathlib's essential supremum. -/
theorem normalizedLpENorm_top_eq_essSup {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [ENorm E] (f : Vec d → E) :
    U.normalizedLpENorm ∞ f =
      essSup (fun x => ‖f x‖ₑ) U.normalizedVolume := by
  simp [normalizedLpENorm, MeasureTheory.eLpNormEssSup_eq_essSup_enorm]

/-- The explicit Euclidean extended `L^p` value of a vector-valued function.
This does not change the global norm instance on `Vec d`. -/
noncomputable def normalizedEuclideanLpENorm {d n : ℕ} (U : BoundedMeasurableDomain d)
    (p : ℝ≥0∞) (f : Vec d → Vec n) : ℝ≥0∞ :=
  U.normalizedLpENorm p (fun x => euclideanNorm (f x))

/-- The finite Euclidean normalized `L^p` value certified by `MemLp`. -/
noncomputable def normalizedEuclideanLpNorm {d n : ℕ} (U : BoundedMeasurableDomain d)
    (p : ℝ≥0∞) (f : Vec d → Vec n)
    (hf : MeasureTheory.MemLp (fun x => euclideanNorm (f x)) p U.normalizedVolume) : ℝ :=
  U.normalizedLpNorm p (fun x => euclideanNorm (f x)) hf

/-- The extended Euclidean normalized `L^p` value depends only on the
normalized-volume almost-everywhere representative. -/
theorem normalizedEuclideanLpENorm_congr_ae {d n : ℕ} (U : BoundedMeasurableDomain d)
    (p : ℝ≥0∞) {f g : Vec d → Vec n}
    (hfg : f =ᵐ[U.normalizedVolume] g) :
    U.normalizedEuclideanLpENorm p f = U.normalizedEuclideanLpENorm p g := by
  unfold normalizedEuclideanLpENorm
  apply U.normalizedLpENorm_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

/-- A proof-carrying finite Euclidean normalized `L^p` value depends only on
the normalized-volume almost-everywhere representative. -/
theorem normalizedEuclideanLpNorm_congr_ae {d n : ℕ} (U : BoundedMeasurableDomain d)
    (p : ℝ≥0∞) {f g : Vec d → Vec n}
    (hf : MeasureTheory.MemLp (fun x => euclideanNorm (f x)) p U.normalizedVolume)
    (hg : MeasureTheory.MemLp (fun x => euclideanNorm (g x)) p U.normalizedVolume)
    (hfg : f =ᵐ[U.normalizedVolume] g) :
    U.normalizedEuclideanLpNorm p f hf = U.normalizedEuclideanLpNorm p g hg := by
  unfold normalizedEuclideanLpNorm
  apply U.normalizedLpNorm_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

/-- For finite `p ≥ 1`, the Euclidean vector lane has the exact normalized
moment formula from the manuscript. -/
theorem normalizedEuclideanLpNorm_eq_integral_rpow {d n : ℕ}
    (U : BoundedMeasurableDomain d) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (f : Vec d → Vec n)
    (hf : MeasureTheory.MemLp (fun x => euclideanNorm (f x)) p U.normalizedVolume) :
    U.normalizedEuclideanLpNorm p f hf =
      (∫ x, euclideanNorm (f x) ^ p.toReal ∂U.normalizedVolume) ^ p.toReal⁻¹ := by
  rw [normalizedEuclideanLpNorm,
    U.normalizedLpNorm_eq_normalizedLpMoment_rpow p hp_one hp_top]
  simp only [normalizedLpMoment, Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _)]

/-- At `p = ∞`, the Euclidean vector lane is the essential supremum of the
explicit Euclidean magnitude. -/
theorem normalizedEuclideanLpENorm_top_eq_essSup {d n : ℕ}
    (U : BoundedMeasurableDomain d) (f : Vec d → Vec n) :
    U.normalizedEuclideanLpENorm ∞ f =
      essSup (fun x => ENNReal.ofReal (euclideanNorm (f x)))
        U.normalizedVolume := by
  rw [normalizedEuclideanLpENorm, U.normalizedLpENorm_top_eq_essSup]
  congr with x
  exact Real.enorm_eq_ofReal (euclideanNorm_nonneg _)

end BoundedMeasurableDomain

end Homogenization
