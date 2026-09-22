/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionL2
import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent
import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientFieldHilbert
import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeMeasureBridge

/-!
# Finite-`p` transport under Dirichlet odd reflection

The Dirichlet odd reflection acts by coordinate signs on the gradient profile.
Those signs are Euclidean isometries.  Combined with the measure-preserving
cell fold maps, this gives exact finite-`p` transport from a cube to its full
reflection block.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

private theorem norm_hilbertVec_ofVec_cubeDirichletOddReflectionCellVectorField
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3) (G : Vec d → Vec d)
    (x : Vec d) :
    ‖HilbertVec.ofVec (cubeDirichletOddReflectionCellVectorField Q choice G x)‖ =
      ‖HilbertVec.ofVec (G (cubeFaceReflectionCellFoldMap Q choice x))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [HilbertVec.norm_sq_ofVec, HilbertVec.norm_sq_ofVec,
    cubeDirichletOddReflectionCellVectorField_apply]
  let v := G (cubeFaceReflectionCellFoldMap Q choice x)
  calc
    vecDot (cubeDirichletOddReflectionCellSign choice •
        cubeFaceReflectionCellFoldLinear choice v)
        (cubeDirichletOddReflectionCellSign choice •
          cubeFaceReflectionCellFoldLinear choice v) =
        vecDot (cubeFaceReflectionCellFoldLinear choice v)
          (cubeFaceReflectionCellFoldLinear choice v) := by
          simp [vecDot_smul_left, vecDot_smul_right]
          rw [← mul_assoc, cubeDirichletOddReflectionCellSign_mul_self]
          ring
    _ = vecDot v v := by
          rw [← vecDot_cubeFaceReflectionCellFoldLinear_left choice
            (cubeFaceReflectionCellFoldLinear choice v) v,
            cubeFaceReflectionCellFoldLinear_involutive]

private theorem norm_hilbertVec_ofVec_cubeDirichletOddReflectionVectorField_eq_cell
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3) (G : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    ‖HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x)‖ =
      ‖HilbertVec.ofVec (G (cubeFaceReflectionCellFoldMap Q choice x))‖ := by
  rw [cubeDirichletOddReflectionVectorField_eq_cellVectorField_of_mem_cellCube Q choice G hx]
  exact norm_hilbertVec_ofVec_cubeDirichletOddReflectionCellVectorField Q choice G x

private theorem aestronglyMeasurable_hilbertVec_ofVec_cellLinear
    {d : ℕ} (choice : Fin d → Fin 3) {α : Type*} [MeasurableSpace α]
    (G : α → Vec d)
    {μ : MeasureTheory.Measure α}
    (hG : MeasureTheory.AEStronglyMeasurable
      (fun x => HilbertVec.ofVec (G x)) μ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => HilbertVec.ofVec
        (cubeDirichletOddReflectionCellSign choice •
          cubeFaceReflectionCellFoldLinear choice (G x))) μ := by
  have hvec : MeasureTheory.AEStronglyMeasurable G μ := by
    simpa using
      (HilbertVec.continuousLinearEquivVec d).continuous.comp_aestronglyMeasurable hG
  have hlinear : MeasureTheory.AEStronglyMeasurable
      (fun x => cubeFaceReflectionCellFoldLinear choice (G x)) μ :=
    (cubeFaceReflectionCellFoldLinear choice).continuous.comp_aestronglyMeasurable hvec
  simpa using
    (HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable
      (hlinear.const_smul (cubeDirichletOddReflectionCellSign choice))

private theorem aestronglyMeasurable_hilbertVec_ofVec_cubeDirichletOddReflectionVectorField_cell
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3) (G : Vec d → Vec d)
    (hG : MeasureTheory.AEStronglyMeasurable (fun x => HilbertVec.ofVec (G x))
      (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x))
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
  have hmp : MeasureTheory.MeasurePreserving
      (cubeFaceReflectionCellFoldMap Q choice)
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice)))
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice] using
      (measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
        (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
        (openCubeSet Q)
  have hcomp : MeasureTheory.AEStronglyMeasurable
      (fun x => HilbertVec.ofVec (G (cubeFaceReflectionCellFoldMap Q choice x)))
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    have hGmap : MeasureTheory.AEStronglyMeasurable
        (fun x => HilbertVec.ofVec (G x))
        (MeasureTheory.Measure.map (cubeFaceReflectionCellFoldMap Q choice)
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice)))) := by
      rw [hmp.map_eq]
      exact hG
    simpa [Function.comp_def] using hGmap.comp_aemeasurable hmp.aemeasurable
  have hcell := aestronglyMeasurable_hilbertVec_ofVec_cellLinear
    choice (fun x => G (cubeFaceReflectionCellFoldMap Q choice x)) hcomp
  refine hcell.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))] with x hx
  simpa [cubeDirichletOddReflectionCellVectorField] using congrArg HilbertVec.ofVec
    (cubeDirichletOddReflectionVectorField_eq_cellVectorField_of_mem_cellCube Q choice G hx).symm

private theorem lintegral_cubeFaceReflectionCellCube_cubeDirichletOddReflectionVectorField
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3) (G : Vec d → Vec d)
    (p : FiniteLpExponent) :
    ∫⁻ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        ‖HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x)‖ₑ ^
          p.exponent.toReal ∂MeasureTheory.volume =
      ∫⁻ y in openCubeSet Q, ‖HilbertVec.ofVec (G y)‖ₑ ^
        p.exponent.toReal ∂MeasureTheory.volume := by
  calc
    ∫⁻ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        ‖HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x)‖ₑ ^
          p.exponent.toReal ∂MeasureTheory.volume =
      ∫⁻ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        ‖HilbertVec.ofVec (G (cubeFaceReflectionCellFoldMap Q choice x))‖ₑ ^
          p.exponent.toReal ∂MeasureTheory.volume := by
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem
            (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))] with x hx
          simpa only [ofReal_norm] using congrArg
            (fun t : ℝ => ENNReal.ofReal t ^ p.exponent.toReal)
            (norm_hilbertVec_ofVec_cubeDirichletOddReflectionVectorField_eq_cell
              Q choice G hx)
    _ = ∫⁻ y in openCubeSet Q, ‖HilbertVec.ofVec (G y)‖ₑ ^
          p.exponent.toReal ∂MeasureTheory.volume := by
          rw [← preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice]
          exact
            ((measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
              (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
              (openCubeSet Q)).lintegral_comp_emb
                (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
                (fun y => ‖HilbertVec.ofVec (G y)‖ₑ ^ p.exponent.toReal)

/-- A radial nonnegative integral is preserved on each face-reflection cell.
This is the measure-theoretic core behind all norm and level-tail transport
under Dirichlet odd reflection. -/
private theorem lintegral_cubeFaceReflectionCellCube_cubeDirichletOddReflectionVectorField_comp_norm
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3) (G : Vec d → Vec d)
    (Φ : ℝ → ℝ≥0∞) :
    ∫⁻ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        Φ ‖HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x)‖
          ∂MeasureTheory.volume =
      ∫⁻ y in openCubeSet Q, Φ ‖HilbertVec.ofVec (G y)‖
          ∂MeasureTheory.volume := by
  calc
    ∫⁻ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        Φ ‖HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x)‖
          ∂MeasureTheory.volume =
      ∫⁻ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        Φ ‖HilbertVec.ofVec (G (cubeFaceReflectionCellFoldMap Q choice x))‖
          ∂MeasureTheory.volume := by
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem
            (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))] with x hx
          rw [norm_hilbertVec_ofVec_cubeDirichletOddReflectionVectorField_eq_cell Q choice G hx]
    _ = ∫⁻ y in openCubeSet Q, Φ ‖HilbertVec.ofVec (G y)‖
          ∂MeasureTheory.volume := by
          rw [← preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice]
          exact
            ((measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
              (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
              (openCubeSet Q)).lintegral_comp_emb
                (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
                (fun y => Φ ‖HilbertVec.ofVec (G y)‖)

private theorem lintegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField
    {d : ℕ} (Q : TriadicCube d) (G : Vec d → Vec d) (p : FiniteLpExponent) :
    ∫⁻ x in cubeFaceReflectionBlockSet Q,
        ‖HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x)‖ₑ ^
          p.exponent.toReal ∂MeasureTheory.volume =
      ((3 : ℝ≥0∞) ^ d) *
        ∫⁻ y in openCubeSet Q, ‖HilbertVec.ofVec (G y)‖ₑ ^
          p.exponent.toReal ∂MeasureTheory.volume := by
  rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q,
    MeasureTheory.lintegral_iUnion]
  · simp_rw [lintegral_cubeFaceReflectionCellCube_cubeDirichletOddReflectionVectorField Q]
    simp [nsmul_eq_mul]
  · intro choice
    exact measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)
  · intro choice₁ choice₂ hne
    exact disjoint_openCubeSet_cubeFaceReflectionCellCube_of_ne Q hne

/-- The full Dirichlet reflection block consists of exactly `3^d` radial
copies of the source cube.  No integrability or measurability hypothesis is
needed for this nonnegative integral identity. -/
theorem lintegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField_comp_norm
    {d : ℕ} (Q : TriadicCube d) (G : Vec d → Vec d) (Φ : ℝ → ℝ≥0∞) :
    ∫⁻ x in cubeFaceReflectionBlockSet Q,
        Φ ‖HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x)‖
          ∂MeasureTheory.volume =
      ((3 : ℝ≥0∞) ^ d) *
        ∫⁻ y in openCubeSet Q, Φ ‖HilbertVec.ofVec (G y)‖
          ∂MeasureTheory.volume := by
  rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q,
    MeasureTheory.lintegral_iUnion]
  · simp_rw [lintegral_cubeFaceReflectionCellCube_cubeDirichletOddReflectionVectorField_comp_norm Q]
    simp [nsmul_eq_mul]
  · intro choice
    exact measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)
  · intro choice₁ choice₂ hne
    exact disjoint_openCubeSet_cubeFaceReflectionCellCube_of_ne Q hne

/-- Strong measurability transports from a source cube to the full Dirichlet
reflection block. -/
theorem aestronglyMeasurable_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d)
    (hG : MeasureTheory.AEStronglyMeasurable (fun x => HilbertVec.ofVec (G x))
      (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x))
      (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
  classical
  rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
  exact MeasureTheory.AEStronglyMeasurable.iUnion fun choice =>
    aestronglyMeasurable_hilbertVec_ofVec_cubeDirichletOddReflectionVectorField_cell
      Q choice G hG

private theorem finiteLpExponent_ne_zero (p : FiniteLpExponent) : p.exponent ≠ 0 :=
  (zero_lt_one.trans p.one_lt).ne'

private theorem finiteLpExponent_toReal_pos (p : FiniteLpExponent) :
    0 < p.exponent.toReal :=
  ENNReal.toReal_pos (finiteLpExponent_ne_zero p) p.lt_top.ne

private theorem aestronglyMeasurable_oddReflectionBlock_iff {d : ℕ} (Q : TriadicCube d)
    (G : Vec d → Vec d) :
    MeasureTheory.AEStronglyMeasurable (fun x => HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x))
      (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) ↔
    MeasureTheory.AEStronglyMeasurable (fun x => HilbertVec.ofVec (G x))
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  constructor
  · intro h
    have hrestrict := h.mono_measure (MeasureTheory.Measure.restrict_mono_set _
      (openCubeSet_subset_cubeFaceReflectionBlockSet Q))
    apply hrestrict.congr
    filter_upwards [MeasureTheory.ae_restrict_mem (isOpen_openCubeSet Q).measurableSet]
      with x hx
    rw [cubeDirichletOddReflectionVectorField_eq_self_of_mem_openCubeSet Q G hx]
  · intro h
    rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
    exact MeasureTheory.AEStronglyMeasurable.iUnion fun choice =>
      aestronglyMeasurable_hilbertVec_ofVec_cubeDirichletOddReflectionVectorField_cell Q choice G h

/-- The finite-`p` Euclidean norm of the odd-reflected vector field on the
full reflection block is exactly the `3^d` measure-scaling factor times the
norm on the source cube. -/
theorem eLpNorm_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField
    {d : ℕ} (Q : TriadicCube d) (G : Vec d → Vec d) (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm
      (fun x => HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x))
      p.exponent (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) =
      ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
        MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (G x)) p.exponent
          (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  by_cases h : MeasureTheory.AEStronglyMeasurable (fun x => HilbertVec.ofVec (G x))
      (MeasureTheory.volume.restrict (openCubeSet Q))
  · have href := (aestronglyMeasurable_oddReflectionBlock_iff Q G).mpr h
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (finiteLpExponent_ne_zero p) p.lt_top.ne href,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (finiteLpExponent_ne_zero p) p.lt_top.ne h,
      lintegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField]
    rw [ENNReal.mul_rpow_of_nonneg _ _
      (one_div_nonneg.mpr (finiteLpExponent_toReal_pos p).le)]
  · have href := mt (aestronglyMeasurable_oddReflectionBlock_iff Q G).mp h
    rw [MeasureTheory.eLpNorm_of_not_aestronglyMeasurable href,
      MeasureTheory.eLpNorm_of_not_aestronglyMeasurable h]
    rw [ENNReal.mul_top (by positivity)]

/-- Finite-`p` Euclidean integrability transports from a cube to the complete
Dirichlet odd-reflection block. -/
theorem memLp_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d) (p : FiniteLpExponent)
    (hG : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (G x)) p.exponent
      (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.MemLp
      (fun x => HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x))
      p.exponent (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
  unfold MeasureTheory.MemLp
  rw [eLpNorm_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField Q G p]
  refine ENNReal.mul_lt_top ?_ hG.eLpNorm_lt_top
  exact ENNReal.rpow_lt_top_of_nonneg
    (one_div_nonneg.mpr (finiteLpExponent_toReal_pos p).le) (by simp)

/-- On a centered origin cube, the odd-reflected Euclidean field has the
same exact unnormalized finite-`p` scaling on the parent cube. -/
theorem eLpNorm_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField
    {d : ℕ} {m : ℤ} (G : Vec d → Vec d) (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm
      (fun x => HilbertVec.ofVec
        (cubeDirichletOddReflectionVectorField (originCube d m) G x))
      p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1)))) =
      ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
        MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (G x)) p.exponent
          (MeasureTheory.volume.restrict (openCubeSet (originCube d m))) := by
  have hmeasure :
      MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1))) =
        MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa using MeasureTheory.Measure.restrict_congr_set
      (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  rw [hmeasure]
  exact eLpNorm_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField
    (originCube d m) G p

/-- Finite-`p` Euclidean integrability transports from an origin cube to its
centered parent under Dirichlet odd reflection. -/
theorem memLp_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField
    {d : ℕ} {m : ℤ} {G : Vec d → Vec d} (p : FiniteLpExponent)
    (hG : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (G x)) p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d m)))) :
    MeasureTheory.MemLp
      (fun x => HilbertVec.ofVec
        (cubeDirichletOddReflectionVectorField (originCube d m) G x))
      p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1)))) := by
  have hmeasure :
      MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1))) =
        MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa using MeasureTheory.Measure.restrict_congr_set
      (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  rw [hmeasure]
  exact memLp_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField
    (originCube d m) p hG

/-- Radial nonnegative integrals on a centered parent cube are exactly `3^d`
times the corresponding source-cube integrals under Dirichlet odd reflection. -/
theorem lintegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_comp_norm
    {d : ℕ} {m : ℤ} (G : Vec d → Vec d) (Φ : ℝ → ℝ≥0∞) :
    ∫⁻ x in openCubeSet (originCube d (m + 1)),
        Φ ‖HilbertVec.ofVec
          (cubeDirichletOddReflectionVectorField (originCube d m) G x)‖
          ∂MeasureTheory.volume =
      ((3 : ℝ≥0∞) ^ d) *
        ∫⁻ y in openCubeSet (originCube d m), Φ ‖HilbertVec.ofVec (G y)‖
          ∂MeasureTheory.volume := by
  have hmeasure :
      MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1))) =
        MeasureTheory.volume.restrict
          (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa using MeasureTheory.Measure.restrict_congr_set
      (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  rw [hmeasure]
  exact lintegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField_comp_norm
    (originCube d m) G Φ

/-- Strong measurability transports from a centered source cube to its parent
under Dirichlet odd reflection. -/
theorem aestronglyMeasurable_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField
    {d : ℕ} {m : ℤ} {G : Vec d → Vec d}
    (hG : MeasureTheory.AEStronglyMeasurable (fun x => HilbertVec.ofVec (G x))
      (MeasureTheory.volume.restrict (openCubeSet (originCube d m)))) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => HilbertVec.ofVec
        (cubeDirichletOddReflectionVectorField (originCube d m) G x))
      (MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1)))) := by
  have hmeasure :
      MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1))) =
        MeasureTheory.volume.restrict
          (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa using MeasureTheory.Measure.restrict_congr_set
      (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  rw [hmeasure]
  exact aestronglyMeasurable_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField
    (originCube d m) hG

private theorem normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet
    {d : ℕ} (m : ℤ) :
    normalizedCubeMeasure (originCube d m) =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        (MeasureTheory.volume.restrict (openCubeSet (originCube d m))) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube]

private theorem restrict_openCubeSet_originCube_eq_smul_normalizedCubeMeasure
    {d : ℕ} (m : ℤ) :
    MeasureTheory.volume.restrict (openCubeSet (originCube d m)) =
      ENNReal.ofReal (cubeVolume (originCube d m)) •
        normalizedCubeMeasure (originCube d m) := by
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet]
  rw [ENNReal.ofReal_inv_of_pos (cubeVolume_pos _)]
  rw [smul_smul]
  have hnonzero : ENNReal.ofReal (cubeVolume (originCube d m)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (cubeVolume_pos _)
  have hone : ENNReal.ofReal (cubeVolume (originCube d m)) *
      (ENNReal.ofReal (cubeVolume (originCube d m)))⁻¹ = 1 :=
    by simpa [mul_comm] using ENNReal.inv_mul_cancel hnonzero ENNReal.ofReal_ne_top
  rw [hone, one_smul]

private theorem cubeVolume_originCube_succ {d : ℕ} (m : ℤ) :
    cubeVolume (originCube d (m + 1)) =
      (3 : ℝ) ^ d * cubeVolume (originCube d m) := by
  simp [cubeVolume, cubeScaleFactor, originCube, zpow_add₀]
  rw [mul_pow]
  ring

private theorem normalized_originCube_reflection_factor_cancel
    {d : ℕ} (m : ℤ) (p : FiniteLpExponent) :
    ENNReal.ofReal ((cubeVolume (originCube d (m + 1)))⁻¹) ^
        (p.exponent.toReal)⁻¹ *
      ((3 : ENNReal) ^ d) ^ (p.exponent.toReal)⁻¹ =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) ^
        (p.exponent.toReal)⁻¹ := by
  let N : ℝ := (3 : ℝ) ^ d
  let V : ℝ := cubeVolume (originCube d m)
  have hN : 0 < N := by positivity
  have hV : 0 < V := cubeVolume_pos _
  have hvol : cubeVolume (originCube d (m + 1)) = N * V := by
    simpa [N, V] using cubeVolume_originCube_succ (d := d) m
  have hbase_real : (N * V)⁻¹ * N = V⁻¹ := by
    field_simp [hN.ne', hV.ne']
  have hbase : ENNReal.ofReal ((N * V)⁻¹) * ENNReal.ofReal N =
      ENNReal.ofReal V⁻¹ := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_nonneg hN.le hV.le))]
    exact congrArg ENNReal.ofReal hbase_real
  rw [hvol]
  calc
    ENNReal.ofReal ((N * V)⁻¹) ^ (p.exponent.toReal)⁻¹ *
        ((3 : ENNReal) ^ d) ^ (p.exponent.toReal)⁻¹ =
      (ENNReal.ofReal ((N * V)⁻¹) * ENNReal.ofReal N) ^
        (p.exponent.toReal)⁻¹ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
          congr 1
          norm_num [N]
    _ = ENNReal.ofReal V⁻¹ ^ (p.exponent.toReal)⁻¹ := by rw [hbase]

/-- Normalized origin-cube finite-`p` norms are exactly preserved by the
Dirichlet odd reflection from a cube to its centered parent. -/
theorem eLpNorm_normalizedCubeMeasure_succ_originCube_cubeDirichletOddReflectionVectorField
    {d : ℕ} {m : ℤ} (G : Vec d → Vec d) (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm
      (fun x => HilbertVec.ofVec
        (cubeDirichletOddReflectionVectorField (originCube d m) G x))
      p.exponent (normalizedCubeMeasure (originCube d (m + 1))) =
      MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (G x)) p.exponent
        (normalizedCubeMeasure (originCube d m)) := by
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet,
    normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet,
    MeasureTheory.eLpNorm_smul_measure_of_ne_zero_of_ne_top
      (finiteLpExponent_ne_zero p) p.lt_top.ne _,
    MeasureTheory.eLpNorm_smul_measure_of_ne_zero_of_ne_top
      (finiteLpExponent_ne_zero p) p.lt_top.ne _,
    eLpNorm_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField]
  simp only [smul_eq_mul, one_div, ENNReal.toReal_inv]
  rw [← mul_assoc, normalized_originCube_reflection_factor_cancel]

/-- Finite-`p` Euclidean integrability is preserved by the normalized
origin-cube odd-reflection transport. -/
theorem memLp_normalizedCubeMeasure_succ_originCube_cubeDirichletOddReflectionVectorField
    {d : ℕ} {m : ℤ} {G : Vec d → Vec d} (p : FiniteLpExponent)
    (hG : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (G x)) p.exponent
      (normalizedCubeMeasure (originCube d m))) :
    MeasureTheory.MemLp
      (fun x => HilbertVec.ofVec
        (cubeDirichletOddReflectionVectorField (originCube d m) G x))
      p.exponent (normalizedCubeMeasure (originCube d (m + 1))) := by
  have hGopen : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (G x)) p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d m))) := by
    rw [restrict_openCubeSet_originCube_eq_smul_normalizedCubeMeasure]
    exact hG.smul_measure ENNReal.ofReal_ne_top
  have hreflect := memLp_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField
    p hGopen
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet]
  exact hreflect.smul_measure ENNReal.ofReal_ne_top

private theorem aestronglyMeasurable_oddReflectionCell_iff
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3) (G : Vec d → Vec d) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x))
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice))) ↔
    MeasureTheory.AEStronglyMeasurable (fun x => HilbertVec.ofVec (G x))
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  constructor
  · intro h
    have htwice := aestronglyMeasurable_hilbertVec_ofVec_cellLinear choice
      (cubeDirichletOddReflectionVectorField Q G) h
    have hcomp : MeasureTheory.AEStronglyMeasurable
        (fun x => HilbertVec.ofVec (G (cubeFaceReflectionCellFoldMap Q choice x)))
        (MeasureTheory.volume.restrict
          (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
      apply htwice.congr
      filter_upwards [MeasureTheory.ae_restrict_mem
        (isOpen_openCubeSet (cubeFaceReflectionCellCube Q choice)).measurableSet]
        with x hx
      rw [cubeDirichletOddReflectionVectorField_eq_cellVectorField_of_mem_cellCube
        Q choice G hx, cubeDirichletOddReflectionCellVectorField_apply,
        map_smul, smul_smul, cubeDirichletOddReflectionCellSign_mul_self,
        cubeFaceReflectionCellFoldLinear_involutive, one_smul]
    have hmp : MeasureTheory.MeasurePreserving
        (cubeFaceReflectionCellFoldMap Q choice)
        (MeasureTheory.volume.restrict
          (openCubeSet (cubeFaceReflectionCellCube Q choice)))
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
      simpa [preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice] using
        (measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
          (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice) (openCubeSet Q)
    have hmap : MeasureTheory.AEStronglyMeasurable (fun x => HilbertVec.ofVec (G x))
        (MeasureTheory.Measure.map (cubeFaceReflectionCellFoldMap Q choice)
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice)))) :=
      (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice).aestronglyMeasurable_map_iff.mpr
        hcomp
    rwa [hmp.map_eq] at hmap
  · exact aestronglyMeasurable_hilbertVec_ofVec_cubeDirichletOddReflectionVectorField_cell
      Q choice G

/-- On one reflection cell, the odd-reflected Euclidean vector field has the
same finite-`p` norm as the original field on the source cube. -/
theorem eLpNorm_cubeFaceReflectionCellCube_cubeDirichletOddReflectionVectorField
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm
      (fun x => HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x))
      p.exponent
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice))) =
      MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (G x)) p.exponent
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  by_cases h : MeasureTheory.AEStronglyMeasurable (fun x => HilbertVec.ofVec (G x))
      (MeasureTheory.volume.restrict (openCubeSet Q))
  · have href := (aestronglyMeasurable_oddReflectionCell_iff Q choice G).mpr h
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (finiteLpExponent_ne_zero p) p.lt_top.ne href,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (finiteLpExponent_ne_zero p) p.lt_top.ne h,
      lintegral_cubeFaceReflectionCellCube_cubeDirichletOddReflectionVectorField]
  · have href := mt (aestronglyMeasurable_oddReflectionCell_iff Q choice G).mp h
    rw [MeasureTheory.eLpNorm_of_not_aestronglyMeasurable href,
      MeasureTheory.eLpNorm_of_not_aestronglyMeasurable h]

end

end Homogenization
