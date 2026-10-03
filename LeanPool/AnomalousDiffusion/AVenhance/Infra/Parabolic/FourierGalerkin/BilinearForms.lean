/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData

/-!
# Mixed Fourier weak forms

The finite ODE is tested by a potentially different Fourier vector from its evolving trial
vector.  These identities retain that bilinear structure and give bounds with constants that do
not depend on the cutoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization
open scoped RealInnerProductSpace

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance bilinearFormsMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance bilinearFormsMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance bilinearFormsProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Spatial drift form with independent trial and test Fourier coefficients. -/
def realFourierDriftBilinearForm (N : ℕ) (drift : ℝ → Torus → Vec 2) (t : ℝ)
    (c d : Coefficients (RealFourierDimension N)) : ℝ :=
  ∫ x : Torus,
    Homogenization.vecDot (drift t x)
      (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
        modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x

/-- Pointwise expansion of the mixed drift integrand. -/
theorem BilinearForms.realFourierDriftBilinearForm_pointwise (N : ℕ)
    (b : Torus → Vec 2) (c d : Coefficients (RealFourierDimension N)) :
    (fun x : Torus =>
      Homogenization.vecDot (b x)
        (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
          modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x) =
    fun x =>
    ∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
        d i * c j * (Homogenization.vecDot (b x) (realFourierModeGradFin N j x) *
          realFourierModeFin N i x) := by
  funext x
  have hgrad : Homogenization.vecDot (b x)
      (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) =
      ∑ j : Fin (RealFourierDimension N), c j *
        Homogenization.vecDot (b x) (realFourierModeGradFin N j x) := by
    simp only [Homogenization.vecDot, Pi.smul_apply, Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hgrad]
  simp only [modeExpansion]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The mixed drift integral is the corresponding rectangular matrix sum. -/
theorem BilinearForms.realFourierDriftBilinearForm_matrix (N : ℕ)
    (b : ℝ → Torus → Vec 2) (t : ℝ)
    (c d : Coefficients (RealFourierDimension N))
    (hentries : ∀ i j, Integrable (fun x : Torus =>
      Homogenization.vecDot (b t x) (realFourierModeGradFin N j x) *
        realFourierModeFin N i x) volume) :
    realFourierDriftBilinearForm N b t c d =
      ∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
        d i * c j * ∫ x : Torus,
          Homogenization.vecDot (b t x) (realFourierModeGradFin N j x) *
            realFourierModeFin N i x := by
  change (∫ x : Torus,
      Homogenization.vecDot (b t x)
        (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
          modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x) = _
  rw [show (fun x : Torus =>
      Homogenization.vecDot (b t x)
        (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
          modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x) =
      fun x =>
        ∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
          d i * c j * (Homogenization.vecDot (b t x)
            (realFourierModeGradFin N j x) * realFourierModeFin N i x) from
      BilinearForms.realFourierDriftBilinearForm_pointwise N (fun x => b t x) c d]
  have hinner (i : Fin (RealFourierDimension N)) :
      Integrable (fun x : Torus => ∑ j : Fin (RealFourierDimension N),
        d i * c j * (Homogenization.vecDot (b t x) (realFourierModeGradFin N j x) *
          realFourierModeFin N i x)) volume := by
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact (hentries i j).const_mul (d i * c j)
  rw [integral_finsetSum (s := Finset.univ) (f := fun i : Fin (RealFourierDimension N) =>
    fun x => ∑ j : Fin (RealFourierDimension N),
      d i * c j * (Homogenization.vecDot (b t x)
        (realFourierModeGradFin N j x) * realFourierModeFin N i x))
    (fun i hi => hinner i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum (s := Finset.univ) (f := fun j : Fin (RealFourierDimension N) =>
    fun x => d i * c j * (Homogenization.vecDot (b t x)
      (realFourierModeGradFin N j x) * realFourierModeFin N i x))]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul]
  · intro j hj
    exact (hentries i j).const_mul (d i * c j)

/-- The gradient pairing of two finite real Fourier sums is their mixed gradient matrix sum. -/
theorem BilinearForms.realFourierGradientMap_inner_mixed (N : ℕ)
    (c d : Coefficients (RealFourierDimension N)) :
    inner ℝ (realFourierGradientMap N c) (realFourierGradientMap N d) =
      ∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
        d i * c j * ∫ x : Torus,
          vecDot (realFourierModeGradFin N j x) (realFourierModeGradFin N i x) := by
  rw [realFourierGradientMap_apply, realFourierGradientMap_apply, sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right,
    realFourierModeGradL2_inner]
  simp_rw [starRingEnd_apply, star_trivial]
  simp_rw [fourierGalerkin_vecDot_eq_frozen]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem BilinearForms.matrixCoefficientCLM_inner_bilinear {n : ℕ}
    (A : Fin n → Fin n → ℝ) (c d : Coefficients n) :
    inner ℝ d (matrixCoefficientCLM A c) =
      ∑ i : Fin n, ∑ j : Fin n, d i * c j * A i j := by
  simp [PiLp.inner_apply, matrixCoefficientCLM_apply, Finset.mul_sum,
    mul_comm, mul_assoc]

/-- The finite weak-form matrix tested against `d` equals the spatial mixed weak form. -/
theorem positiveCutoffWeakForm_bilinear_identity (N : ℕ)
    (b : ℝ → Vec 2 → Vec 2) (κ t : ℝ)
    (c d : Coefficients (RealFourierDimension N))
    (hentries : ∀ i j, Integrable (fun x : Torus =>
      Homogenization.vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x)
        (realFourierModeGradFin N j x) * realFourierModeFin N i x) volume) :
    inner ℝ d (matrixCoefficientCLM (fun i j => weakFormMatrixEntry
      (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x) κ
      (realFourierModeFin N) (realFourierModeGradFin N) t i j) c) =
      -realFourierDriftBilinearForm N
        (fun s => AVenhance.Infra.Torus.periodicToTorus (b s)) t c d -
        κ * inner ℝ (realFourierGradientMap N c) (realFourierGradientMap N d) := by
  rw [BilinearForms.matrixCoefficientCLM_inner_bilinear]
  have hsplit :
      (∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
        d i * c j * weakFormMatrixEntry
          (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x) κ
          (realFourierModeFin N) (realFourierModeGradFin N) t i j) =
      -(∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
        d i * c j * ∫ x : Torus,
          Homogenization.vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x)
            (realFourierModeGradFin N j x) * realFourierModeFin N i x) - κ *
        ∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
          d i * c j * ∫ x : Torus,
            vecDot (realFourierModeGradFin N j x) (realFourierModeGradFin N i x) := by
    simp_rw [weakFormMatrixEntry, mul_sub, mul_neg, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib]
    simp_rw [fourierGalerkin_vecDot_eq_frozen]
    have hfactor :
        (∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
          d i * c j * (κ * ∫ x : Torus,
            Homogenization.vecDot (realFourierModeGradFin N j x)
              (realFourierModeGradFin N i x))) =
        κ * (∑ i : Fin (RealFourierDimension N), ∑ j : Fin (RealFourierDimension N),
          d i * c j * ∫ x : Torus,
            Homogenization.vecDot (realFourierModeGradFin N j x)
              (realFourierModeGradFin N i x)) := by
      calc
        _ = ∑ i : Fin (RealFourierDimension N), κ *
            ∑ j : Fin (RealFourierDimension N), d i * c j *
                ∫ x : Torus, Homogenization.vecDot (realFourierModeGradFin N j x)
                  (realFourierModeGradFin N i x) := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            _ = ∑ j : Fin (RealFourierDimension N), κ * (d i * c j *
                ∫ x : Torus, Homogenization.vecDot (realFourierModeGradFin N j x)
                  (realFourierModeGradFin N i x)) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = _ := by rw [Finset.mul_sum]
        _ = _ := by rw [Finset.mul_sum]
    rw [hfactor]
  let driftTorus : ℝ → Torus → Vec 2 := fun s x =>
    AVenhance.Infra.Torus.periodicToTorus (b s) x
  rw [hsplit,
    BilinearForms.realFourierDriftBilinearForm_matrix N driftTorus t c d (by simpa [driftTorus]
        using hentries),
    BilinearForms.realFourierGradientMap_inner_mixed]

/-- Mixed drift estimate, uniform in the real Fourier cutoff. -/
theorem positiveCutoffDriftBilinear_bound (N : ℕ)
    (b : ℝ → Vec 2 → Vec 2)
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (c d : Coefficients (RealFourierDimension N)) :
    |realFourierDriftBilinearForm N
        (fun s => AVenhance.Infra.Torus.periodicToTorus (b s)) t c d| ≤
      positiveCutoffDriftConstant b hb_bdd *
        ‖positiveCutoffGradientMap N c‖ * ‖d‖ := by
  let C : ℝ := Classical.choose hb_bdd
  have hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C :=
    Classical.choose_spec hb_bdd
  have hC_nonneg : 0 ≤ C := by
    have h := hC (1 / 2) (by norm_num) 0
    exact (norm_nonneg _).trans h
  let B : ℝ := Real.sqrt 2 * C
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) hC_nonneg
  have hdot : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x v,
      |Homogenization.vecDot (b t x) v| ≤ B * euclideanVecNorm v := by
    intro s hs x v
    exact vecDot_le_of_supNorm_le hC_nonneg (hC s hs x)
  let f : Torus → ℝ := fun x =>
    Homogenization.vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x)
      (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
        modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x
  let g : Torus → ℝ := fun x => euclideanVecNorm
    (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)
  let u : Torus → ℝ := modeExpansion (RealFourierDimension N) (realFourierModeFin N) d
  have hpoint : ∀ᵐ x ∂(volume : Measure Torus), |f x| ≤ B * (|g x| * |u x|) := by
    filter_upwards with x
    have hb := hdot t ht (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)
      (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)
    have hrep : AVenhance.Infra.Torus.periodicToTorus (b t) x =
        b t (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) := rfl
    change |Homogenization.vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x)
        (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
        modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x| ≤ _
    rw [hrep]
    calc
      _ = |Homogenization.vecDot (b t
          (AVenhance.Infra.Torus.unitTorusRepresentative 2 x))
          (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)| *
          |modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x| := abs_mul _ _
      _ ≤ (B * euclideanVecNorm
          (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)) *
          |modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x| :=
        mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = B * (|euclideanVecNorm
          (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)| *
          |modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x|) := by
        rw [abs_of_nonneg (euclideanVecNorm_nonneg _)]
        ring
  have hbound := driftIntegral_bound_of_L2_or_not f g u B hB hpoint
    (realFourierGradientExpansion_norm_memLp N c) (realFourierScalarExpansion_memLp N d)
  have hgradFactor : (∫ x : Torus, ‖g x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) =
      ‖positiveCutoffGradientMap N c‖ := by
    simpa [g, positiveCutoffGradientMap] using realFourierGradientExpansion_l2Factor N c
  have hscalarFactor : (∫ x : Torus, ‖u x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = ‖d‖ := by
    simpa [u, Real.norm_eq_abs] using realFourierScalarExpansion_l2Factor N d
  have hform : realFourierDriftBilinearForm N
      (fun s => AVenhance.Infra.Torus.periodicToTorus (b s)) t c d = ∫ x, f x := rfl
  rw [hgradFactor, hscalarFactor] at hbound
  calc
    |realFourierDriftBilinearForm N
        (fun s => AVenhance.Infra.Torus.periodicToTorus (b s)) t c d| =
        |∫ x, f x| := congrArg abs hform
    _ ≤ B * ‖positiveCutoffGradientMap N c‖ * ‖d‖ := by
      simpa [hgradFactor, hscalarFactor] using hbound
    _ = positiveCutoffDriftConstant b hb_bdd *
        ‖positiveCutoffGradientMap N c‖ * ‖d‖ := by
      rfl

end AVenhance.Infra.Parabolic.FourierGalerkin

end
