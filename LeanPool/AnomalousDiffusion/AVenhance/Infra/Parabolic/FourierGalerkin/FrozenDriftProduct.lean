/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ProductCompactness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic

/-!
# Product-space realization of the drift

The drift is measurable on the Euclidean space-time cell. This module transfers that
measurability to time times the quotient torus, where the product-space Galerkin limits live.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance frozenProductMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance frozenProductMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance frozenProductProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance frozenProductProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance frozenProductSFiniteTorus : SFinite (volume : Measure Torus) := inferInstance
local instance frozenProductTopHolderTwo : (⊤ : ENNReal).HolderTriple 2 2 :=
  ENNReal.HolderTriple.symm
local instance frozenProductTopHolderTop : (⊤ : ENNReal).HolderTriple ⊤ ⊤ :=
  ENNReal.HolderTriple.symm

private theorem FrozenDriftProblem.torusDrift_aestronglyMeasurable
    (P : FrozenDriftProblem) :
    AEStronglyMeasurable
      (fun p : ℝ × Torus => AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2)
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
  let cell : Set (Vec 2) := AVenhance.Infra.Torus.unitCell 2
  let cellSubtype := {x : Vec 2 // x ∈ cell}
  let cellMeasure : Measure cellSubtype :=
    volume.comap (Subtype.val : cellSubtype → Vec 2)
  let cellSpatialMeasure : Measure (Vec 2) := volume.restrict cell
  let equiv := UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))
  have hmeasureCell : MeasurePreserving (fun x : cellSubtype => (x : Vec 2))
      cellMeasure cellSpatialMeasure := by
    change MeasurePreserving Subtype.val
      ((volume : Measure (Vec 2)).comap (Subtype.val : cellSubtype → Vec 2))
      ((volume : Measure (Vec 2)).restrict cell)
    exact ⟨measurable_subtype_coe,
      map_comap_subtype_coe (AVenhance.Infra.Torus.measurableSet_unitCell 2) volume⟩
  have hmeasureTorus : MeasurePreserving equiv (volume : Measure Torus) cellMeasure := by
    change MeasurePreserving equiv (volume : Measure Torus)
      ((volume : Measure (Vec 2)).comap (Subtype.val : cellSubtype → Vec 2))
    simpa [equiv, cell, AVenhance.Infra.Torus.unitCell,
      AVenhance.Infra.Torus.unitCellAt] using
      UnitAddTorus.measurePreserving_equivPiIoc (a := fun _ : Fin 2 => (0 : ℝ))
  have hSFiniteCell : SFinite cellMeasure := by
    exact hmeasureTorus.sfinite
  let timeMap : ℝ → ℝ := id
  have hmeasureProdTorus : MeasurePreserving (Prod.map timeMap equiv)
      (GalerkinTimeMeasure.prod (volume : Measure Torus))
      (GalerkinTimeMeasure.prod cellMeasure) := by
    exact MeasurePreserving.prod (MeasurePreserving.id GalerkinTimeMeasure) hmeasureTorus
  have hmeasureProdCell : MeasurePreserving
      (Prod.map timeMap (Subtype.val : cellSubtype → Vec 2))
      (GalerkinTimeMeasure.prod cellMeasure)
      (GalerkinTimeMeasure.prod cellSpatialMeasure) := by
    exact @MeasurePreserving.prod ℝ ℝ cellSubtype _ _ _ (Vec 2) _
      GalerkinTimeMeasure GalerkinTimeMeasure cellMeasure cellSpatialMeasure
      (inferInstance : SFinite GalerkinTimeMeasure) hSFiniteCell
      (f := id) (g := Subtype.val)
      (MeasurePreserving.id GalerkinTimeMeasure) hmeasureCell
  have hmeasureToEuclidean := hmeasureProdCell.comp hmeasureProdTorus
  have hdriftCell : AEStronglyMeasurable (fun p : ℝ × Vec 2 => P.b p.1 p.2)
      (volume.restrict (Ioc (0 : ℝ) 1 ×ˢ cell)) := by
    apply P.drift_measurable.mono_set
    intro p hp
    exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, Set.mem_univ _⟩
  have hdriftProd : AEStronglyMeasurable (fun p : ℝ × Vec 2 => P.b p.1 p.2)
      (GalerkinTimeMeasure.prod cellSpatialMeasure) := by
    change AEStronglyMeasurable (fun p : ℝ × Vec 2 => P.b p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict cell))
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (Vec 2)]
    exact hdriftCell
  have hcomp := hdriftProd.comp_measurePreserving hmeasureToEuclidean
  have heq : (fun p : ℝ × Torus => P.b p.1 (equiv p.2).1) =
      (fun p => AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2) := by
    funext p
    rfl
  exact heq ▸ hcomp

/-- The drift, pulled back to time times the quotient torus, is essentially bounded in the
vector `L²` norm associated with the Euclidean two-vector norm. -/
theorem FrozenDriftProblem.torusDrift_memLp_top (P : FrozenDriftProblem) :
    MemLp (fun p : ℝ × Torus =>
      (WithLp.toLp 2 (AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2) : SpatialVector))
      ⊤ (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
  obtain ⟨B, hB⟩ := P.drift_bounded
  have hBnonneg : 0 ≤ B := by
    have := hB 0 (by norm_num) (0 : Vec 2)
    exact (norm_nonneg _).trans this
  have hmeas := P.torusDrift_aestronglyMeasurable
  have hvec : AEStronglyMeasurable (fun p : ℝ × Torus =>
      (WithLp.toLp 2 (AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2) : SpatialVector))
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_aestronglyMeasurable hmeas
  apply MemLp.of_bound hvec (Real.sqrt 2 * B)
  have hprodSet : GalerkinTimeMeasure.prod (volume : Measure Torus) =
      (volume : Measure (ℝ × Torus)).restrict (Ioc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod ℝ Torus]
  rw [hprodSet]
  filter_upwards [ae_restrict_mem
    (MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ)] with p hp
  have htIcc : p.1 ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hp.1.1, hp.1.2⟩
  have hb := hB p.1 htIcc
  have hcoord (i : Fin 2) : |P.b p.1
      (AVenhance.Infra.Torus.unitTorusRepresentative 2 p.2) i| ≤ B := by
    have hnorm := (pi_norm_le_iff_of_nonempty (P.b p.1
      (AVenhance.Infra.Torus.unitTorusRepresentative 2 p.2))).1
        (hb (AVenhance.Infra.Torus.unitTorusRepresentative 2 p.2)) i
    simpa [Real.norm_eq_abs] using hnorm
  have hsq (i : Fin 2) : (P.b p.1
      (AVenhance.Infra.Torus.unitTorusRepresentative 2 p.2) i) ^ 2 ≤ B ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hBnonneg).2 (hcoord i)
    simpa [sq_abs] using h
  have heuclid : euclideanVecNorm (AVenhance.Infra.Torus.periodicToTorus
      (P.b p.1) p.2) ≤ Real.sqrt 2 * B := by
    unfold AVenhance.Infra.Torus.periodicToTorus
    apply (sq_le_sq₀ (euclideanVecNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hBnonneg)).1
    rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ)), euclideanVecNorm_sq]
    simp [Homogenization.vecNormSq, Homogenization.vecDot]
    nlinarith [hsq 0, hsq 1]
  simpa [spatialVector_norm_eq_euclideanVecNorm] using heuclid

theorem continuous_time_memLp_top {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp f ⊤ GalerkinTimeMeasure := by
  have hcompact : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  have himage : Bornology.IsBounded (f '' Icc (0 : ℝ) 1) :=
    (hcompact.image hf).isBounded
  obtain ⟨C, hCpos, hC⟩ := himage.subset_ball_lt 0 0
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
  have hball := hC ⟨t, ht', rfl⟩
  have hnorm : ‖f t‖ < C := by simpa [Metric.mem_ball, dist_eq_norm] using hball
  exact hnorm.le

theorem FrozenDriftProduct.realFourierExpansion_memLp_top (N : ℕ)
    (d : Coefficients (RealFourierDimension N)) :
    MemLp (modeExpansion (RealFourierDimension N) (realFourierModeFin N) d)
      ⊤ (volume : Measure Torus) := by
  have hcont : Continuous
      (modeExpansion (RealFourierDimension N) (realFourierModeFin N) d) := by
    unfold modeExpansion
    apply continuous_finsetSum Finset.univ
    intro i hi
    exact continuous_const.mul (realFourierModeFin_continuous N i)
  have hcompact : IsCompact (Set.univ : Set Torus) := isCompact_univ
  have himage : Bornology.IsBounded
      (modeExpansion (RealFourierDimension N) (realFourierModeFin N) d '' Set.univ) :=
    (hcompact.image hcont).isBounded
  obtain ⟨C, hCpos, hC⟩ := himage.subset_ball_lt 0 0
  apply MemLp.of_bound hcont.aestronglyMeasurable C
  filter_upwards with x
  have hball := hC ⟨x, Set.mem_univ _, rfl⟩
  have hnorm : ‖modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x‖ < C := by
    simpa [Metric.mem_ball, dist_eq_norm] using hball
  exact hnorm.le

/-- A separated scalar product-space test belongs to the product `L²` space. -/
theorem scalarProductTest_memLp {η : ℝ → ℝ} (hη : MemLp η ⊤ GalerkinTimeMeasure)
    (ψ : ScalarTorusL2) :
    MemLp (fun p : ℝ × Torus => η p.1 * ψ p.2) 2
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
  exact (hη.comp_fst (volume : Measure Torus)).mul
    ((Lp.memLp ψ).comp_snd GalerkinTimeMeasure)

/-- The `L²` class of a separated scalar product-space test. -/
noncomputable def scalarProductTestLp (η : ℝ → ℝ) (ψ : ScalarTorusL2)
    (hη : MemLp η ⊤ GalerkinTimeMeasure) : ScalarProductTimeL2 :=
  (scalarProductTest_memLp hη ψ).toLp (fun p : ℝ × Torus => η p.1 * ψ p.2)

/-- Pairing a finite scalar Galerkin sum against a separated product test agrees with the
corresponding Bochner time integral of spatial `L²` pairings. -/
theorem FrozenDriftProblem.scalarProductLp_pairing_time (P : FrozenDriftProblem) (N : ℕ)
    (η : ℝ → ℝ) (hη : MemLp η ⊤ GalerkinTimeMeasure) (ψ : ScalarTorusL2) :
    inner ℝ (P.scalarProductLp N) (scalarProductTestLp η ψ hη) =
      ∫ t, η t * inner ℝ (P.scalarTimeFunction N t) ψ ∂GalerkinTimeMeasure := by
  let f := P.scalarProductFunction N
  let q : ℝ × Torus → ℝ := fun p => η p.1 * ψ p.2
  let hf := scalarProductFunction_memLp P N
  let hq := scalarProductTest_memLp hη ψ
  have hmul : Integrable (fun p : ℝ × Torus => f p * q p)
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
    exact hf.integrable_mul hq
  have hslice (t : ℝ) :
      (∫ x : Torus, f (t, x) * q (t, x)) =
        η t * inner ℝ (P.scalarTimeFunction N t) ψ := by
    calc
      (∫ x : Torus, f (t, x) * q (t, x)) =
          η t * ∫ x : Torus, (P.scalarTimeFunction N t x) * ψ x := by
        have hEq : (fun x : Torus => f (t, x) * q (t, x)) =ᵐ[volume]
            fun x => η t * ((P.scalarTimeFunction N t x) * ψ x) := by
          filter_upwards [scalarProductFunction_slice_ae P N t] with x hx
          calc
            f (t, x) * q (t, x) = η t * (f (t, x) * ψ x) := by
              simp [q]
              ring
            _ = η t * ((P.scalarTimeFunction N t x) * ψ x) := by
              have hx' : f (t, x) = P.scalarTimeFunction N t x := hx
              rw [hx']
        rw [integral_congr_ae hEq]
        rw [integral_const_mul]
      _ = η t * inner ℝ (P.scalarTimeFunction N t) ψ := by
        rw [MeasureTheory.L2.inner_def]
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        simp [mul_comm]
  calc
    inner ℝ (P.scalarProductLp N) (scalarProductTestLp η ψ hη) =
        ∫ p, f p * q p ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(scalarProductFunction_memLp P N).coeFn_toLp,
        (scalarProductTest_memLp hη ψ).coeFn_toLp] with p hf' hq'
      change inner ℝ (P.scalarProductLp N p) (scalarProductTestLp η ψ hη p) = _
      rw [show P.scalarProductLp N p = f p from hf',
        show scalarProductTestLp η ψ hη p = q p from hq']
      simp [mul_comm]
    _ = ∫ t, ∫ x : Torus, f (t, x) * q (t, x)
        ∂(volume : Measure Torus) ∂GalerkinTimeMeasure := integral_prod _ hmul
    _ = ∫ t, η t * inner ℝ (P.scalarTimeFunction N t) ψ
        ∂GalerkinTimeMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hslice

/-- A separated gradient product-space test belongs to the product `L²` space. -/
theorem gradientProductTest_memLp {η : ℝ → ℝ} (hη : MemLp η ⊤ GalerkinTimeMeasure)
    (g : SpatialGradientL2) :
    MemLp (fun p : ℝ × Torus => η p.1 • g p.2) 2
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
  exact (hη.comp_fst (volume : Measure Torus)).smul
    ((Lp.memLp g).comp_snd GalerkinTimeMeasure)

/-- The `L²` class of a separated gradient product-space test. -/
noncomputable def gradientProductTestLp (η : ℝ → ℝ) (g : SpatialGradientL2)
    (hη : MemLp η ⊤ GalerkinTimeMeasure) : GradientProductTimeL2 :=
  (gradientProductTest_memLp hη g).toLp (fun p : ℝ × Torus => η p.1 • g p.2)

/-- Pairing a finite gradient Galerkin sum against a separated product test agrees with the
corresponding Bochner time integral of spatial `L²` pairings. -/
theorem FrozenDriftProblem.gradientProductLp_pairing_time (P : FrozenDriftProblem) (N : ℕ)
    (η : ℝ → ℝ) (hη : MemLp η ⊤ GalerkinTimeMeasure) (g : SpatialGradientL2) :
    inner ℝ (P.gradientProductLp N) (gradientProductTestLp η g hη) =
      ∫ t, η t * inner ℝ (P.gradientTimeFunction N t) g ∂GalerkinTimeMeasure := by
  let f := P.gradientProductFunction N
  let q : ℝ × Torus → SpatialVector := fun p => η p.1 • g p.2
  let hf := gradientProductFunction_memLp P N
  let hq := gradientProductTest_memLp hη g
  let F := hf.toLp f
  let Q := hq.toLp q
  have hAE : (fun p : ℝ × Torus => inner ℝ (F p) (Q p)) =ᵐ[
      GalerkinTimeMeasure.prod (volume : Measure Torus)]
      fun p => inner ℝ (f p) (q p) := by
    filter_upwards [hf.coeFn_toLp, hq.coeFn_toLp] with p hf' hq'
    rw [hf', hq']
  have hInt : Integrable (fun p : ℝ × Torus => inner ℝ (f p) (q p))
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) :=
    (MeasureTheory.L2.integrable_inner F Q).congr hAE
  have hslice (t : ℝ) :
      (∫ x : Torus, inner ℝ (f (t, x)) (q (t, x))) =
        η t * inner ℝ (P.gradientTimeFunction N t) g := by
    calc
      (∫ x : Torus, inner ℝ (f (t, x)) (q (t, x))) =
          η t * ∫ x : Torus, inner ℝ (f (t, x)) (g x) := by
        have hEq : (fun x : Torus => inner ℝ (f (t, x)) (q (t, x))) =
            fun x => η t * inner ℝ (f (t, x)) (g x) := by
          funext x
          simp [q, inner_smul_right]
        rw [hEq, integral_const_mul]
      _ = η t * inner ℝ (P.gradientTimeFunction N t) g := by
        rw [MeasureTheory.L2.inner_def]
        congr 1
        apply integral_congr_ae
        filter_upwards [gradientProductFunction_slice_ae P N t] with x hx
        have hx' : f (t, x) = P.gradientTimeFunction N t x := hx
        rw [hx']
  calc
    inner ℝ (P.gradientProductLp N) (gradientProductTestLp η g hη) =
        ∫ p, inner ℝ (F p) (Q p)
          ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
      exact MeasureTheory.L2.inner_def F Q
    _ = ∫ p, inner ℝ (f p) (q p)
          ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hq.coeFn_toLp] with p hf' hq'
      rw [hf', hq']
    _ = ∫ t, ∫ x : Torus, inner ℝ (f (t, x)) (q (t, x))
          ∂(volume : Measure Torus) ∂GalerkinTimeMeasure := by
      exact integral_prod _ hInt
    _ = ∫ t, η t * inner ℝ (P.gradientTimeFunction N t) g
          ∂GalerkinTimeMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hslice

/-- The bounded drift multiplied by a smooth finite Fourier test is an admissible vector
test for weak convergence of the Galerkin gradients. -/
def FrozenDriftProblem.weightedDriftProductTestFunction (P : FrozenDriftProblem)
    (η : ℝ → ℝ) (N : ℕ) (d : Coefficients (RealFourierDimension N)) :
    ℝ × Torus → SpatialVector := fun p =>
  (η p.1 * modeExpansion (RealFourierDimension N) (realFourierModeFin N) d p.2) •
    (WithLp.toLp 2
      (AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2) : SpatialVector)

theorem FrozenDriftProblem.weightedDriftProductTest_memLp (P : FrozenDriftProblem)
    {η : ℝ → ℝ} (hη : MemLp η ⊤ GalerkinTimeMeasure)
    (N : ℕ) (d : Coefficients (RealFourierDimension N)) :
    MemLp (P.weightedDriftProductTestFunction η N d)
      2 (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
  have hweight : MemLp (fun p : ℝ × Torus =>
      η p.1 * modeExpansion (RealFourierDimension N) (realFourierModeFin N) d p.2)
      ⊤ (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
    exact (hη.comp_fst (volume : Measure Torus)).mul
      ((FrozenDriftProduct.realFourierExpansion_memLp_top N d).comp_snd GalerkinTimeMeasure)
  have htop : MemLp (fun p : ℝ × Torus =>
      (η p.1 * modeExpansion (RealFourierDimension N) (realFourierModeFin N) d p.2) •
        (WithLp.toLp 2
          (AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2) : SpatialVector))
      ⊤ (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
    exact hweight.smul P.torusDrift_memLp_top
  have htop' : MemLp (P.weightedDriftProductTestFunction η N d) ⊤
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
    change MemLp (fun p : ℝ × Torus =>
      (η p.1 * modeExpansion (RealFourierDimension N) (realFourierModeFin N) d p.2) •
        (WithLp.toLp 2
          (AVenhance.Infra.Torus.periodicToTorus (P.b p.1) p.2) : SpatialVector))
      ⊤ (GalerkinTimeMeasure.prod (volume : Measure Torus))
    exact htop
  exact htop'.mono_exponent (by norm_num)

/-- The product `L²` class of the bounded-drift test field. -/
noncomputable def FrozenDriftProblem.weightedDriftProductTestLp (P : FrozenDriftProblem)
    (η : ℝ → ℝ) (N : ℕ) (d : Coefficients (RealFourierDimension N))
    (hη : MemLp η ⊤ GalerkinTimeMeasure) : GradientProductTimeL2 :=
  (P.weightedDriftProductTest_memLp hη N d).toLp
    (P.weightedDriftProductTestFunction η N d)

theorem FrozenDriftProduct.spatialVector_inner_toLp (v w : Vec 2) :
    inner ℝ (WithLp.toLp 2 v : SpatialVector) (WithLp.toLp 2 w : SpatialVector) =
      Homogenization.vecDot v w := by
  rw [PiLp.inner_apply]
  simp [Homogenization.vecDot, mul_comm]

/-- At each time, the spatial pairing of a finite gradient with the drift test is the
concrete finite drift bilinear form. -/
theorem FrozenDriftProblem.weightedDriftProduct_slice_integral (P : FrozenDriftProblem)
    (N : ℕ) (η : ℝ → ℝ) (d : Coefficients (RealFourierDimension N)) (t : ℝ) :
    (∫ x : Torus, inner ℝ (P.gradientProductFunction N (t, x))
      (P.weightedDriftProductTestFunction η N d (t, x))) =
      η t * realFourierDriftBilinearForm N
        (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) t
        (productExtendedCoefficients P N t) d := by
  let f := P.gradientProductFunction N
  let q := P.weightedDriftProductTestFunction η N d
  have hgrad (x : Torus) : Homogenization.vecDot
      (AVenhance.Infra.Torus.periodicToTorus (P.b t) x)
      (∑ j : Fin (RealFourierDimension N),
        (productExtendedCoefficients P N t j) • realFourierModeGradFin N j x) =
      ∑ j : Fin (RealFourierDimension N),
        (productExtendedCoefficients P N t j) * Homogenization.vecDot
          (AVenhance.Infra.Torus.periodicToTorus (P.b t) x)
          (realFourierModeGradFin N j x) := by
    simp only [Homogenization.vecDot, Pi.smul_apply, Finset.sum_apply,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hpoint (x : Torus) : inner ℝ (f (t, x)) (q (t, x)) =
      η t * (Homogenization.vecDot
        (AVenhance.Infra.Torus.periodicToTorus (P.b t) x)
        (∑ j : Fin (RealFourierDimension N),
          (productExtendedCoefficients P N t j) • realFourierModeGradFin N j x) *
        modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x) := by
    rw [show f (t, x) = ∑ j : Fin (RealFourierDimension N),
        (coefficientComponent P N j t) •
          (WithLp.toLp 2 (realFourierModeGradFin N j x) : SpatialVector) by rfl]
    rw [show q (t, x) =
        (η t * modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x) •
          (WithLp.toLp 2
            (AVenhance.Infra.Torus.periodicToTorus (P.b t) x) : SpatialVector) by rfl]
    rw [sum_inner]
    simp_rw [inner_smul_left, inner_smul_right, FrozenDriftProduct.spatialVector_inner_toLp]
    simp only [starRingEnd_apply, star_trivial]
    have hassoc :
        (∑ j : Fin (RealFourierDimension N),
          coefficientComponent P N j t *
            (η t * modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x *
              Homogenization.vecDot (realFourierModeGradFin N j x)
                (AVenhance.Infra.Torus.periodicToTorus (P.b t) x))) =
        ∑ j : Fin (RealFourierDimension N),
          (coefficientComponent P N j t *
            (η t * modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x)) *
            Homogenization.vecDot (realFourierModeGradFin N j x)
              (AVenhance.Infra.Torus.periodicToTorus (P.b t) x) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hassoc]
    calc
      _ = (η t * modeExpansion (RealFourierDimension N)
            (realFourierModeFin N) d x) *
            (∑ j : Fin (RealFourierDimension N),
              coefficientComponent P N j t * Homogenization.vecDot
                (AVenhance.Infra.Torus.periodicToTorus (P.b t) x)
                (realFourierModeGradFin N j x)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp [Homogenization.vecDot, mul_assoc, mul_comm, mul_left_comm]
      _ = η t * (Homogenization.vecDot
            (AVenhance.Infra.Torus.periodicToTorus (P.b t) x)
            (∑ j : Fin (RealFourierDimension N),
              (productExtendedCoefficients P N t j) • realFourierModeGradFin N j x) *
            modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x) := by
        have hgrad' : Homogenization.vecDot
            (AVenhance.Infra.Torus.periodicToTorus (P.b t) x)
            (∑ j : Fin (RealFourierDimension N),
              (coefficientComponent P N j t) • realFourierModeGradFin N j x) =
            ∑ j : Fin (RealFourierDimension N),
              (coefficientComponent P N j t) * Homogenization.vecDot
                (AVenhance.Infra.Torus.periodicToTorus (P.b t) x)
                (realFourierModeGradFin N j x) := by
          simpa [coefficientComponent, productExtendedCoefficients] using hgrad x
        rw [← hgrad']
        simp only [coefficientComponent, productExtendedCoefficients]
        ring
  calc
    (∫ x : Torus, inner ℝ (f (t, x)) (q (t, x))) =
        ∫ x : Torus, η t * (Homogenization.vecDot
          (AVenhance.Infra.Torus.periodicToTorus (P.b t) x)
          (∑ j : Fin (RealFourierDimension N),
            (productExtendedCoefficients P N t j) • realFourierModeGradFin N j x) *
          modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = η t * realFourierDriftBilinearForm N
        (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) t
        (productExtendedCoefficients P N t) d := by
      rw [integral_const_mul]
      rfl

/-- The gradient product pairing with the bounded-drift test field equals the time integral of the
concrete finite drift form. -/
theorem FrozenDriftProblem.gradientProductLp_weightedDrift_pairing_time
    (P : FrozenDriftProblem) (N : ℕ) (η : ℝ → ℝ)
    (hη : MemLp η ⊤ GalerkinTimeMeasure)
    (d : Coefficients (RealFourierDimension N)) :
    inner ℝ (P.gradientProductLp N) (P.weightedDriftProductTestLp η N d hη) =
      ∫ t, η t * realFourierDriftBilinearForm N
        (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) t
        (productExtendedCoefficients P N t) d ∂GalerkinTimeMeasure := by
  let f := P.gradientProductFunction N
  let q := P.weightedDriftProductTestFunction η N d
  let hf := gradientProductFunction_memLp P N
  let hq := P.weightedDriftProductTest_memLp hη N d
  let F := hf.toLp f
  let Q := hq.toLp q
  have hAE : (fun p : ℝ × Torus => inner ℝ (F p) (Q p)) =ᵐ[
      GalerkinTimeMeasure.prod (volume : Measure Torus)]
      fun p => inner ℝ (f p) (q p) := by
    filter_upwards [hf.coeFn_toLp, hq.coeFn_toLp] with p hf' hq'
    have hFp : F p = f p := by simpa [F] using hf'
    have hQp : Q p = q p := by
      change (hq.toLp q) p = q p
      exact hq'
    rw [hFp, hQp]
  have hInt : Integrable (fun p : ℝ × Torus => inner ℝ (f p) (q p))
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) :=
    (MeasureTheory.L2.integrable_inner F Q).congr hAE
  have hslice (t : ℝ) := P.weightedDriftProduct_slice_integral N η d t
  calc
    inner ℝ (P.gradientProductLp N) (P.weightedDriftProductTestLp η N d hη) =
        ∫ p, inner ℝ (F p) (Q p)
          ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)) :=
      MeasureTheory.L2.inner_def F Q
    _ = ∫ p, inner ℝ (f p) (q p)
          ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
      apply integral_congr_ae
      exact hAE
    _ = ∫ t, ∫ x : Torus, inner ℝ (f (t, x)) (q (t, x))
          ∂(volume : Measure Torus) ∂GalerkinTimeMeasure := integral_prod _ hInt
    _ = ∫ t, η t * realFourierDriftBilinearForm N
          (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) t
          (productExtendedCoefficients P N t) d ∂GalerkinTimeMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hslice

/-- The time-dependent finite drift pairing is integrable, by product-space `L²` integrability and
Fubini. -/
theorem FrozenDriftProblem.weightedDriftProduct_time_integrable (P : FrozenDriftProblem)
    (N : ℕ) (η : ℝ → ℝ) (hη : MemLp η ⊤ GalerkinTimeMeasure)
    (d : Coefficients (RealFourierDimension N)) :
    Integrable (fun t => η t * realFourierDriftBilinearForm N
      (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) t
      (productExtendedCoefficients P N t) d) GalerkinTimeMeasure := by
  let f := P.gradientProductFunction N
  let q := P.weightedDriftProductTestFunction η N d
  let hf := gradientProductFunction_memLp P N
  let hq := P.weightedDriftProductTest_memLp hη N d
  let F := hf.toLp f
  let Q := hq.toLp q
  have hAE : (fun p : ℝ × Torus => inner ℝ (F p) (Q p)) =ᵐ[
      GalerkinTimeMeasure.prod (volume : Measure Torus)]
      fun p => inner ℝ (f p) (q p) := by
    filter_upwards [hf.coeFn_toLp, hq.coeFn_toLp] with p hf' hq'
    have hFp : F p = f p := by simpa [F] using hf'
    have hQp : Q p = q p := by
      change (hq.toLp q) p = q p
      exact hq'
    rw [hFp, hQp]
  have hProd : Integrable (fun p : ℝ × Torus => inner ℝ (f p) (q p))
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) :=
    (MeasureTheory.L2.integrable_inner F Q).congr hAE
  have hSliceIntegrable := hProd.integral_prod_left
  have hSliceEq : (fun t => ∫ x : Torus, inner ℝ (f (t, x)) (q (t, x))) =
      fun t => η t * realFourierDriftBilinearForm N
        (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) t
        (productExtendedCoefficients P N t) d := by
    funext t
    exact P.weightedDriftProduct_slice_integral N η d t
  exact hSliceEq.symm ▸ hSliceIntegrable

end AVenhance.Infra.Parabolic.FourierGalerkin

end
