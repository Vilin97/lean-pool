/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedGradientSpace
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SobolevDefinitions

/-! Measure-preserving Euclidean coordinates and the actual L² bridge to the cylinder. -/

@[expose] public section

noncomputable section

namespace EulerCylinderCoordinates

open MeasureTheory EulerSobolev EulerLiftedGradientSpace
open scoped ContDiff ENNReal NNReal Topology SchwartzMap


/-- Euclidean coordinate zero is the angle; coordinates one through three are spatial. -/
noncomputable def coordinateLinearEquiv : Domain 4 ≃ₗ[ℝ] LiftTangent where
  toFun z := (WithLp.toLp 2 (fun i : Fin 3 => z i.succ), z 0)
  invFun p := WithLp.toLp 2 (Fin.cons p.2 (fun i => p.1 i))
  left_inv z := by
    ext i
    cases i using Fin.cases <;> simp
  right_inv p := by
    apply Prod.ext
    · ext i
      simp
    · simp
  map_add' z w := by
    apply Prod.ext
    · ext i
      simp
    · simp
  map_smul' c z := by
    apply Prod.ext
    · ext i
      simp
    · simp

/-- The coordinate isomorphism, continuous in both directions. -/
noncomputable def coordinateEquiv : Domain 4 ≃L[ℝ] LiftTangent :=
  coordinateLinearEquiv.toContinuousLinearEquiv

@[simp] theorem coordinateEquiv_apply (z : Domain 4) :
    coordinateEquiv z = (WithLp.toLp 2 (fun i : Fin 3 => z i.succ), z 0) := rfl

@[simp] theorem coordinateEquiv_symm_apply (p : LiftTangent) :
    coordinateEquiv.symm p = WithLp.toLp 2 (Fin.cons p.2 (fun i => p.1 i)) := rfl

/-- The coordinate change preserves the genuine product Lebesgue measure exactly. -/
theorem coordinateEquiv_measurePreserving :
    MeasurePreserving coordinateEquiv (volume : Measure (Domain 4))
      ((volume : Measure Vector3).prod (volume : Measure ℝ)) := by
  have h₁ := PiLp.volume_preserving_ofLp (Fin 4)
  have h₂ := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have h₃ : MeasurePreserving (Prod.swap : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ) :=
    Measure.measurePreserving_swap
  have h₄ := (PiLp.volume_preserving_toLp (Fin 3)).prod (MeasurePreserving.id (μ := volume (α :=
      ℝ)))
  have h := h₄.comp (h₃.comp (h₂.comp h₁))
  convert! h using 1

variable (period : ℝ) [Fact (0 < period)]

/-- A fundamental strip in the real covering space. -/
noncomputable def fundamentalMeasure (a : ℝ) : Measure LiftTangent :=
  (volume : Measure Vector3).prod (volume.restrict (Set.Ioc a (a + period)))

/-- Covering coordinates restricted to one period preserve the cylinder's measure. -/
theorem covering_fundamental_measurePreserving (a : ℝ) :
    MeasurePreserving (coveringMap period) (fundamentalMeasure period a) (liftMeasure period) :=
  (MeasurePreserving.id (μ := (volume : Measure Vector3))).prod (AddCircle.measurePreserving_mk
      period a)

/-- Euclidean coordinates for the actual quotient covering map. -/
noncomputable def euclideanCover : Domain 4 → LiftDomain period :=
  coveringMap period ∘ coordinateEquiv

/-- Euclidean measure restricted to one fundamental angular strip. -/
noncomputable def stripMeasure (a : ℝ) : Measure (Domain 4) :=
  volume.restrict {z : Domain 4 | z 0 ∈ Set.Ioc a (a + period)}

omit [Fact (0 < period)] in
theorem coordinateEquiv_fundamental_measurePreserving (a : ℝ) :
    MeasurePreserving coordinateEquiv (stripMeasure period a) (fundamentalMeasure period a) := by
  have hm : MeasurableSet ((Set.univ : Set Vector3) ×ˢ Set.Ioc a (a + period)) :=
    MeasurableSet.univ.prod measurableSet_Ioc
  have h := coordinateEquiv_measurePreserving.restrict_preimage hm
  have he : coordinateEquiv ⁻¹' ((Set.univ : Set Vector3) ×ˢ Set.Ioc a (a + period)) =
      {z : Domain 4 | z 0 ∈ Set.Ioc a (a + period)} := by
    ext z
    simp
  rw [he] at h
  simpa only [stripMeasure, fundamentalMeasure, ← Measure.prod_restrict,
    Measure.restrict_univ] using h

theorem euclideanCover_fundamental_measurePreserving (a : ℝ) :
    MeasurePreserving (euclideanCover period) (stripMeasure period a) (liftMeasure period) :=
  (covering_fundamental_measurePreserving period a).comp
    (coordinateEquiv_fundamental_measurePreserving period a)

/-- The fundamental-strip Lᵖ seminorm is exactly the Lᵖ seminorm on the cylinder. -/
theorem eLpNorm_cover {F : Type*} [NormedAddCommGroup F]
    (f : LiftDomain period → F) (hf : AEStronglyMeasurable f (liftMeasure period))
    (a : ℝ) (p : ℝ≥0∞) :
    eLpNorm (f ∘ euclideanCover period) p (stripMeasure period a) =
      eLpNorm f p (liftMeasure period) :=
  eLpNorm_comp_measurePreserving hf (euclideanCover_fundamental_measurePreserving period a)

/-- Square integrability of actual fields transfers to their Euclidean periodic lifts. -/
theorem memLp_cover {F : Type*} [NormedAddCommGroup F]
    (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period)) (a : ℝ) :
    MemLp (f ∘ euclideanCover period) 2 (stripMeasure period a) :=
  hf.comp_measurePreserving (euclideanCover_fundamental_measurePreserving period a)


/-- Six consecutive fundamental strips, retaining the actual Euclidean measures. -/
noncomputable def chartMeasure : Measure (Domain 4) :=
  Measure.sum (fun i : Fin 6 => stripMeasure period (((i : ℝ) - 3) * period))

theorem chartSupport_cover : ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}) ⊆
    ⋃ i : Fin 6, {z : Domain 4 | z 0 ∈
      Set.Ioc (((i : ℝ)-3)*period) ((((i : ℝ)-3)*period)+period)} := by
  intro z hz
  have hT : 0 < period := Fact.out
  have hz' := abs_le.1 (show |z 0| ≤ 2 * period from hz)
  by_cases h₀ : z 0 ≤ -2 * period
  · apply Set.mem_iUnion.2 ⟨0, ?_⟩
    norm_num
    constructor <;> linarith
  by_cases h₁ : z 0 ≤ -period
  · apply Set.mem_iUnion.2 ⟨1, ?_⟩
    norm_num
    constructor <;> linarith
  by_cases h₂ : z 0 ≤ 0
  · apply Set.mem_iUnion.2 ⟨2, ?_⟩
    norm_num
    constructor <;> linarith
  by_cases h₃ : z 0 ≤ period
  · apply Set.mem_iUnion.2 ⟨3, ?_⟩
    norm_num
    constructor <;> linarith
  · apply Set.mem_iUnion.2 ⟨4, ?_⟩
    norm_num
    constructor <;> linarith

theorem chartSupport_measure_le :
    volume.restrict (({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period})) ≤ chartMeasure period :=
  (Measure.restrict_mono_set volume (chartSupport_cover period)).trans Measure.restrict_iUnion_le

/-- The finite chart cover has exactly six times the cylinder measure. -/
theorem euclideanCover_chart_measurePreserving :
    MeasurePreserving (euclideanCover period) (chartMeasure period)
      ((6 : ℝ≥0∞) • liftMeasure period) := by
  have hm := (euclideanCover_fundamental_measurePreserving period 0).measurable
  refine ⟨hm, ?_⟩
  rw [chartMeasure, Measure.sum_fintype, Measure.map_finset_sum' hm.aemeasurable]
  simp only [(euclideanCover_fundamental_measurePreserving period _).map_eq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul ℝ≥0∞ 6 (liftMeasure period)).symm

theorem eLpNorm_cover_chart {F : Type*} [NormedAddCommGroup F]
    (f : LiftDomain period → F) (hf : AEStronglyMeasurable f (liftMeasure period)) :
    eLpNorm (f ∘ euclideanCover period) 2 (chartMeasure period) =
      (6 : ℝ≥0∞) ^ (1/2 : ℝ) * eLpNorm f 2 (liftMeasure period) := by
  rw [eLpNorm_comp_measurePreserving (hf.smul_measure _)
    (euclideanCover_chart_measurePreserving period)]
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num)]
  norm_num

/-- A localized lift is controlled by the genuine cylinder norm, with explicit chart multiplicity.
-/
theorem eLpNorm_localized_le {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : LiftDomain period → F) (hf : AEStronglyMeasurable f (liftMeasure period))
    (g : Domain 4 → G) (hsupp : Function.support g ⊆ ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 *
        period}))
    (B : ℝ≥0) (hb : ∀ z, ‖g z‖ ≤ B * ‖f (euclideanCover period z)‖) :
    eLpNorm g 2 volume ≤ (B : ℝ≥0∞) * (6 : ℝ≥0∞) ^ (1/2 : ℝ) *
      eLpNorm f 2 (liftMeasure period) := by
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  calc
    _ ≤ eLpNorm g 2 (chartMeasure period) := eLpNorm_mono_measure g (chartSupport_measure_le period)
    _ ≤ (B : ℝ≥0∞) * eLpNorm (f ∘ euclideanCover period) 2 (chartMeasure period) :=
      eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall hb) 2
    _ = _ := by rw [eLpNorm_cover_chart period f hf, mul_assoc]

/-- The localized-lift estimate as an inequality between ordinary real L² norms. -/
theorem localized_L2_le {F : Type*} [NormedAddCommGroup F]
    (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period))
    (g : 𝓢(Domain 4, ℂ)) (hsupp : Function.support g ⊆ ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 *
        period}))
    (B : ℝ≥0) (hb : ∀ z, ‖g z‖ ≤ B * ‖f (euclideanCover period z)‖) :
    ‖g.toLp 2‖ ≤ (B : ℝ) * (6 : ℝ) ^ (1/2 : ℝ) * ‖hf.toLp f‖ := by
  have h := eLpNorm_localized_le period f hf.1 g hsupp B hb
  have hfin : (B : ℝ≥0∞) * (6 : ℝ≥0∞) ^ (1/2 : ℝ) *
      eLpNorm f 2 (liftMeasure period) ≠ ⊤ := by
    finiteness
  have hreal := ENNReal.toReal_mono hfin h
  simpa only [SchwartzMap.norm_toLp, Lp.norm_toLp, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat] using hreal

end EulerCylinderCoordinates
