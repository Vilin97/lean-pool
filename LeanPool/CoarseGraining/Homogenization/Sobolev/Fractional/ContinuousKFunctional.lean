/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.WeakHessianEuclidean
import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Algebra.H1Function
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.UnitCubeEuclideanL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The continuous centered-cube `K`-functional

This is the literal real-interpolation kernel from the Chapter 1
constant-coefficient Dirichlet argument.  The unit centered open cube is used
for the coordinatewise `H¹` competitors; normalized volume is realized by its
a.e.-equal half-open cube.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- The source scale carrier `0 < t ≤ 1`. -/
abbrev ContinuousKScale := Set.Ioc (0 : ℝ) 1

theorem ContinuousKScale.pos (t : ContinuousKScale) : 0 < t.1 := t.2.1

theorem ContinuousKScale.le_one (t : ContinuousKScale) : t.1 ≤ 1 := t.2.2

/-- A source-faithful `H¹(square_0; ℝ^d)` competitor.  Its coordinates carry
genuine `H1Function` witnesses on the source-facing open cube. -/
structure ContinuousKCompetitor (d : ℕ) where
  /-- One genuine weak `H¹` witness for each target coordinate. -/
  coord : Fin d → H1Function (openCubeSet (originCube d 0))

namespace ContinuousKCompetitor

/-- The vector field represented by a coordinatewise `H¹` competitor. -/
def toField {d : ℕ} (G : ContinuousKCompetitor d) : Vec d → Vec d :=
  fun x i => G.coord i x

/-- The matrix of actual coordinate weak gradients. -/
def gradient {d : ℕ} (G : ContinuousKCompetitor d) : Vec d → Mat d :=
  fun x i j => (G.coord i).grad x j

@[simp] theorem toField_apply {d : ℕ} (G : ContinuousKCompetitor d)
    (x : Vec d) (i : Fin d) : G.toField x i = G.coord i x := rfl

@[simp] theorem gradient_apply {d : ℕ} (G : ContinuousKCompetitor d)
    (x : Vec d) (i j : Fin d) : G.gradient x i j = (G.coord i).grad x j := rfl

instance {d : ℕ} : Inhabited (ContinuousKCompetitor d) where
  default := { coord := fun _ => 0 }

/-- Euclidean `L²` control of the represented field, derived solely from the
coordinate `H¹` witnesses. -/
theorem euclideanMemL2 {d : ℕ} (G : ContinuousKCompetitor d) :
    MeasureTheory.MemLp (fun x => HilbertVec.ofVec (G.toField x)) (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume := by
  rw [MeasureTheory.memLp_piLp_iff]
  intro i
  simpa only [unitCenteredCubeDomain,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    Function.comp_apply, PiLp.toLp_apply, toField_apply] using
    (G.coord i).memL2_normalizedCubeMeasure

/-- Frobenius `L²` control of the actual weak-gradient matrix, derived from
the coordinate `H¹` witnesses and the shared Frobenius realization. -/
theorem gradientFrobeniusMemL2 {d : ℕ} (G : ContinuousKCompetitor d) :
    MeasureTheory.MemLp
      (fun x => matrixFrobeniusMagnitude (G.gradient x)) (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume := by
  have hmat : MeasureTheory.MemLp (fun x => HilbertMat.ofMat (G.gradient x)) (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    rw [MeasureTheory.memLp_piLp_iff]
    intro j
    simpa only [unitCenteredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      Function.comp_apply, PiLp.toLp_apply, gradient_apply] using
      (G.coord i).grad_memL2_normalizedCubeMeasure j
  simpa only [matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat] using
    hmat.norm

end ContinuousKCompetitor

/-- The normalized Euclidean `L²` residual in the continuous `K`-functional. -/
noncomputable def continuousKResidualNorm {d : ℕ} (F : UnitCubeEuclideanL2Field d)
    (G : ContinuousKCompetitor d) : ℝ :=
  (unitCenteredCubeDomain d).normalizedEuclideanLpNorm (2 : ℝ≥0∞)
    (fun x => F x - G.toField x) (by
      have hsub := F.euclideanMemL2.sub G.euclideanMemL2
      simpa only [euclideanNorm_eq_norm_ofVec, HilbertVec.ofVec, PiLp.toLp_apply,
        Pi.sub_apply] using! hsub.norm)

/-- The normalized Frobenius `L²` weak-gradient quantity in the continuous
`K`-functional. -/
noncomputable def continuousKGradientNorm {d : ℕ} (G : ContinuousKCompetitor d) : ℝ :=
  (unitCenteredCubeDomain d).normalizedLpNorm (2 : ℝ≥0∞)
    (fun x => matrixFrobeniusMagnitude (G.gradient x))
    G.gradientFrobeniusMemL2

theorem continuousKResidualNorm_nonneg {d : ℕ} (F : UnitCubeEuclideanL2Field d)
    (G : ContinuousKCompetitor d) : 0 ≤ continuousKResidualNorm F G :=
  ENNReal.toReal_nonneg

theorem continuousKGradientNorm_nonneg {d : ℕ} (G : ContinuousKCompetitor d) :
    0 ≤ continuousKGradientNorm G :=
  ENNReal.toReal_nonneg

/-- The exact square-root value contributed by one genuine `H¹` competitor. -/
noncomputable def continuousKFunctionalCompetitorValue {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) (G : ContinuousKCompetitor d) : ℝ :=
  Real.sqrt
    (continuousKResidualNorm F G ^ 2 + t.1 ^ 2 * continuousKGradientNorm G ^ 2)

theorem continuousKFunctionalCompetitorValue_nonneg {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) (G : ContinuousKCompetitor d) :
    0 ≤ continuousKFunctionalCompetitorValue t F G :=
  Real.sqrt_nonneg _

theorem continuousKFunctionalCompetitorValue_mono {d : ℕ}
    {t u : ContinuousKScale} (htu : t.1 ≤ u.1) (F : UnitCubeEuclideanL2Field d)
    (G : ContinuousKCompetitor d) :
    continuousKFunctionalCompetitorValue t F G ≤
      continuousKFunctionalCompetitorValue u F G := by
  apply Real.sqrt_le_sqrt
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right
  · simpa only [pow_two] using mul_self_le_mul_self (ContinuousKScale.pos t).le htu
  · exact sq_nonneg _

/-- The literal continuous real-interpolation `K`-functional. -/
noncomputable def continuousKFunctional {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) : ℝ :=
  sInf (Set.range fun G : ContinuousKCompetitor d =>
    continuousKFunctionalCompetitorValue t F G)

theorem continuousKFunctional_eq_sInf {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) :
    continuousKFunctional t F =
      sInf (Set.range fun G : ContinuousKCompetitor d =>
        continuousKFunctionalCompetitorValue t F G) := rfl

theorem continuousKFunctional_range_nonempty {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) :
    (Set.range fun G : ContinuousKCompetitor d =>
      continuousKFunctionalCompetitorValue t F G).Nonempty :=
  ⟨continuousKFunctionalCompetitorValue t F default, ⟨default, rfl⟩⟩

theorem continuousKFunctional_range_bddBelow {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) :
    BddBelow (Set.range fun G : ContinuousKCompetitor d =>
      continuousKFunctionalCompetitorValue t F G) := by
  refine ⟨0, ?_⟩
  rintro y ⟨G, rfl⟩
  exact continuousKFunctionalCompetitorValue_nonneg t F G

theorem continuousKFunctional_nonneg {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) : 0 ≤ continuousKFunctional t F := by
  unfold continuousKFunctional
  exact le_csInf (continuousKFunctional_range_nonempty t F) fun y hy => by
    rcases hy with ⟨G, rfl⟩
    exact continuousKFunctionalCompetitorValue_nonneg t F G

theorem continuousKFunctional_le_competitor {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) (G : ContinuousKCompetitor d) :
    continuousKFunctional t F ≤ continuousKFunctionalCompetitorValue t F G := by
  unfold continuousKFunctional
  exact csInf_le (continuousKFunctional_range_bddBelow t F) ⟨G, rfl⟩

theorem continuousKFunctional_mono {d : ℕ} {t u : ContinuousKScale}
    (htu : t.1 ≤ u.1) (F : UnitCubeEuclideanL2Field d) :
    continuousKFunctional t F ≤ continuousKFunctional u F := by
  unfold continuousKFunctional
  refine le_csInf (continuousKFunctional_range_nonempty u F) ?_
  rintro y ⟨G, rfl⟩
  calc
    sInf (Set.range fun G : ContinuousKCompetitor d =>
        continuousKFunctionalCompetitorValue t F G)
      ≤ continuousKFunctionalCompetitorValue t F G :=
        csInf_le (continuousKFunctional_range_bddBelow t F) ⟨G, rfl⟩
    _ ≤ continuousKFunctionalCompetitorValue u F G :=
      continuousKFunctionalCompetitorValue_mono htu F G

/-- The real-line representative of `K(t,F)` used for the continuum integral.
It agrees with the source `K`-functional on the open integration interval. -/
noncomputable def continuousKFunctionalOnOpenScale {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo (0 : ℝ) 1 then
    continuousKFunctional ⟨t, ⟨ht.1, ht.2.le⟩⟩ F
  else 0

theorem continuousKFunctionalOnOpenScale_monoOn {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) :
    MonotoneOn (continuousKFunctionalOnOpenScale F) (Set.Ioo (0 : ℝ) 1) := by
  intro t ht u hu htu
  simp only [continuousKFunctionalOnOpenScale, dif_pos ht, dif_pos hu]
  exact continuousKFunctional_mono htu F

theorem continuousKFunctionalOnOpenScale_aemeasurable {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) :
    AEMeasurable (continuousKFunctionalOnOpenScale F)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo
    (continuousKFunctionalOnOpenScale_monoOn F)

private theorem continuousKSeminormWeight_aemeasurable (s : ℝ) :
    AEMeasurable
      (fun t : ℝ => ENNReal.ofReal (Real.rpow t (-2 * s)) * ENNReal.ofReal t⁻¹)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  have hrpow : ContinuousOn (fun t : ℝ => Real.rpow t (-2 * s))
      (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    exact (Real.continuousAt_rpow_const t (-2 * s) (Or.inl (ne_of_gt ht.1))).continuousWithinAt
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Ioo (0 : ℝ) 1) :=
    continuousOn_inv₀.mono fun _ ht => ne_of_gt ht.1
  exact (hrpow.aemeasurable measurableSet_Ioo).ennreal_ofReal.mul
    (hinv.aemeasurable measurableSet_Ioo).ennreal_ofReal

/-- The nonnegative integrand in the continuum `K`-seminorm.  On the exact
integration interval it is `t^(-2s) K(t,F)^2 / t`. -/
noncomputable def continuousKSeminormIntegrand {d : ℕ}
    (s : ℝ) (F : UnitCubeEuclideanL2Field d) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow t (-2 * s)) *
    ENNReal.ofReal (continuousKFunctionalOnOpenScale F t ^ 2) *
    ENNReal.ofReal t⁻¹

theorem continuousKSeminormIntegrand_aemeasurable {d : ℕ}
    (s : ℝ) (F : UnitCubeEuclideanL2Field d) :
    AEMeasurable (continuousKSeminormIntegrand s F)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  unfold continuousKSeminormIntegrand
  simpa only [Pi.mul_def, pow_two, mul_assoc, mul_left_comm, mul_comm] using!
    (continuousKSeminormWeight_aemeasurable s).mul
      ((continuousKFunctionalOnOpenScale_aemeasurable F).mul
        (continuousKFunctionalOnOpenScale_aemeasurable F)).ennreal_ofReal

/-- On the source integration interval, the integrand is literally the
weighted square `t^(-2s) K(t,F)^2 / t`. -/
theorem continuousKSeminormIntegrand_eq_of_mem {d : ℕ}
    (s : ℝ) (F : UnitCubeEuclideanL2Field d) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    continuousKSeminormIntegrand s F t =
      ENNReal.ofReal (Real.rpow t (-2 * s)) *
        ENNReal.ofReal (continuousKFunctional ⟨t, ⟨ht.1, ht.2.le⟩⟩ F ^ 2) *
        ENNReal.ofReal t⁻¹ := by
  simp only [continuousKSeminormIntegrand, continuousKFunctionalOnOpenScale, dif_pos ht]

/-- The exact ENNReal-valued continuum interpolation seminorm.  Its integrand
is a genuine Lebesgue-measurable function on `(0,1)`, rather than a lower-
integral convention for an unverified representative. -/
noncomputable def continuousKSeminorm {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F t) ^ (1 / 2 : ℝ)

/-- Exact continuum-lintegral characterization of the interpolation seminorm,
including the source weight `t^(-2s)` and measure factor `dt / t`. -/
theorem continuousKSeminorm_eq_lintegral {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    continuousKSeminorm s F =
      (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F t) ^ (1 / 2 : ℝ) :=
  rfl

theorem continuousKResidualNorm_congr_ae {d : ℕ} {F H : UnitCubeEuclideanL2Field d}
    (G : ContinuousKCompetitor d)
    (hFH : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] H) :
    continuousKResidualNorm F G = continuousKResidualNorm H G := by
  unfold continuousKResidualNorm
  apply (unitCenteredCubeDomain d).normalizedEuclideanLpNorm_congr_ae
  filter_upwards [hFH] with x hx
  simp only [hx]

theorem continuousKFunctionalCompetitorValue_congr_ae {d : ℕ}
    (t : ContinuousKScale) {F H : UnitCubeEuclideanL2Field d} (G : ContinuousKCompetitor d)
    (hFH : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] H) :
    continuousKFunctionalCompetitorValue t F G = continuousKFunctionalCompetitorValue t H G := by
  unfold continuousKFunctionalCompetitorValue
  rw [continuousKResidualNorm_congr_ae G hFH]

theorem continuousKFunctional_congr_ae {d : ℕ}
    (t : ContinuousKScale) {F H : UnitCubeEuclideanL2Field d}
    (hFH : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] H) :
    continuousKFunctional t F = continuousKFunctional t H := by
  unfold continuousKFunctional
  congr 1
  ext y
  constructor
  · rintro ⟨G, rfl⟩
    exact ⟨G, (continuousKFunctionalCompetitorValue_congr_ae t G hFH).symm⟩
  · rintro ⟨G, rfl⟩
    exact ⟨G, continuousKFunctionalCompetitorValue_congr_ae t G hFH⟩

theorem continuousKFunctionalOnOpenScale_congr_ae {d : ℕ}
    {F H : UnitCubeEuclideanL2Field d}
    (hFH : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] H) (t : ℝ) :
    continuousKFunctionalOnOpenScale F t = continuousKFunctionalOnOpenScale H t := by
  unfold continuousKFunctionalOnOpenScale
  split_ifs with ht
  · rw [continuousKFunctional_congr_ae ⟨t, ⟨ht.1, ht.2.le⟩⟩ hFH]
  · rfl

theorem continuousKSeminormIntegrand_congr_ae {d : ℕ}
    (s : ℝ) {F H : UnitCubeEuclideanL2Field d}
    (hFH : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] H) (t : ℝ) :
    continuousKSeminormIntegrand s F t = continuousKSeminormIntegrand s H t := by
  unfold continuousKSeminormIntegrand
  rw [continuousKFunctionalOnOpenScale_congr_ae hFH t]

theorem continuousKSeminorm_congr_ae {d : ℕ}
    (s : FractionalOrder) {F H : UnitCubeEuclideanL2Field d}
    (hFH : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] H) :
    continuousKSeminorm s F = continuousKSeminorm s H := by
  unfold continuousKSeminorm
  congr 1
  apply MeasureTheory.lintegral_congr
  intro t
  exact continuousKSeminormIntegrand_congr_ae s.1 hFH t

end

end Homogenization
