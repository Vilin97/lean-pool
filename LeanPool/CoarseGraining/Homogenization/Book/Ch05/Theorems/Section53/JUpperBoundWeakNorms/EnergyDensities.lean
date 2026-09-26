/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.CanonicalFields

/-! # Energy Densities -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# EnergyDensities

Energy densities, product densities, and integrability facts.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Parent half-energy density `1/2 ∇v · a∇v`. -/
noncomputable def topHalfEnergyDensityOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q : Vec d) : Vec d → ℝ :=
  fun x => (1 / 2 : ℝ) *
    Ch02.variationEnergyIntegrand (Ch02.cubeDomain Q) a
      (canonicalMaximizerSolutionOnCube Q a p q) x

/-- Centered raw Ch2 response on a cube. -/
noncomputable def centeredResponseJOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 q0 : Vec d) : ℝ :=
  Ch02.responseJ (Ch02.cubeDomain Q) a p q -
    (1 / 2 : ℝ) * vecDot p0 q0

/-- The product density in the centered splitting. -/
noncomputable def centeredProductDensityOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 q0 : Vec d) : Vec d → ℝ :=
  fun x =>
    (1 / 2 : ℝ) *
      vecDot (canonicalMaximizerGradientOnCube Q a p q x - p0)
        (canonicalMaximizerFluxOnCube Q a p q x - q0)

/-- The `q0` linear density in the centered splitting. -/
noncomputable def centeredGradientLinearDensityOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 q0 : Vec d) : Vec d → ℝ :=
  fun x => (1 / 2 : ℝ) *
    vecDot q0 (canonicalMaximizerGradientOnCube Q a p q x - p0)

/-- The `p0` linear density in the centered splitting. -/
noncomputable def centeredFluxLinearDensityOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 q0 : Vec d) : Vec d → ℝ :=
  fun x => (1 / 2 : ℝ) *
    vecDot p0 (canonicalMaximizerFluxOnCube Q a p q x - q0)

/-- The cutoff product term in the deterministic centered split. -/
noncomputable def cutoffProductTermOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (φ : Vec d → ℝ) (p q p0 q0 : Vec d) : ℝ :=
  cubeAverage Q (fun x => φ x * centeredProductDensityOnCube Q a p q p0 q0 x)

/-- The cutoff oscillation term in the deterministic centered split. -/
noncomputable def cutoffOscillationTermOnCubeAtDepth {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (j : ℕ) (φ : Vec d → ℝ) (p q : Vec d) : ℝ :=
  descendantsAverage Q j fun R =>
    cubeAverage R
      (fun x => (cubeAverage R φ - φ x) * topHalfEnergyDensityOnCube Q a p q x)

/-- The mean-defect parent-energy term before child-energy replacement. -/
noncomputable def meanDefectTopEnergyTermOnCubeAtDepth {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (j : ℕ) (φ : Vec d → ℝ) (p q : Vec d) : ℝ :=
  descendantsAverage Q j fun R =>
    (1 - cubeAverage R φ) *
      cubeAverage R (topHalfEnergyDensityOnCube Q a p q)

/-- Scalar additivity-cross term, indexed by child cubes. -/
noncomputable def additivityCrossTermOnCubeAtDepth {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (φ : Vec d → ℝ)
    (cross : TriadicCube d → ℝ) : ℝ :=
  descendantsAverage Q j fun R =>
    (1 - cubeAverage R φ) * cross R

/-- The cutoff `q0` linear term. -/
noncomputable def cutoffGradientLinearTermOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (φ : Vec d → ℝ) (p q p0 q0 : Vec d) : ℝ :=
  cubeAverage Q
    (fun x => φ x * centeredGradientLinearDensityOnCube Q a p q p0 q0 x)

/-- The cutoff `p0` linear term. -/
noncomputable def cutoffFluxLinearTermOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (φ : Vec d → ℝ) (p q p0 q0 : Vec d) : ℝ :=
  cubeAverage Q
    (fun x => φ x * centeredFluxLinearDensityOnCube Q a p q p0 q0 x)

/-- The two cutoff linear terms, in manuscript order. -/
noncomputable def cutoffLinearPairTermOnCube {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (φ : Vec d → ℝ) (p q p0 q0 : Vec d) : ℝ :=
  cutoffGradientLinearTermOnCube Q a φ p q p0 q0 +
    cutoffFluxLinearTermOnCube Q a φ p q p0 q0

/-- Cutoff-weighted child response for a deterministic triadic coefficient
family. -/
noncomputable def cutoffWeightedChildResponseJOnFamilyAtDepth {d : ℕ}
    (a : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) (j : ℕ)
    (φ : Vec d → ℝ) (p q : Vec d) : ℝ :=
  descendantsAverage Q j fun R =>
    cutoffChildWeight φ R *
      Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p q

/-- Pure vector algebra behind the product plus two linear terms. -/
theorem centered_product_add_linear_terms_eq_half_vecDot_sub_half_vecDot
    {d : ℕ} (g f p0 q0 : Vec d) :
    (1 / 2 : ℝ) * vecDot (g - p0) (f - q0) +
        (1 / 2 : ℝ) * vecDot q0 (g - p0) +
          (1 / 2 : ℝ) * vecDot p0 (f - q0) =
      (1 / 2 : ℝ) * vecDot g f - (1 / 2 : ℝ) * vecDot p0 q0 := by
  simp [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, vecDot_comm]
  ring

/-- Pointwise algebra turning the parent energy into product plus linear terms. -/
theorem centeredProduct_add_linear_densities_eq_topHalfEnergy_sub_half_dot
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 q0 : Vec d) (x : Vec d) :
    centeredProductDensityOnCube Q a p q p0 q0 x +
        centeredGradientLinearDensityOnCube Q a p q p0 q0 x +
          centeredFluxLinearDensityOnCube Q a p q p0 q0 x =
      topHalfEnergyDensityOnCube Q a p q x -
        (1 / 2 : ℝ) * vecDot p0 q0 := by
  calc
    centeredProductDensityOnCube Q a p q p0 q0 x +
        centeredGradientLinearDensityOnCube Q a p q p0 q0 x +
          centeredFluxLinearDensityOnCube Q a p q p0 q0 x =
        (1 / 2 : ℝ) *
            vecDot (canonicalMaximizerGradientOnCube Q a p q x)
              (canonicalMaximizerFluxOnCube Q a p q x) -
          (1 / 2 : ℝ) * vecDot p0 q0 := by
          exact centered_product_add_linear_terms_eq_half_vecDot_sub_half_vecDot
            (canonicalMaximizerGradientOnCube Q a p q x)
            (canonicalMaximizerFluxOnCube Q a p q x) p0 q0
    _ = topHalfEnergyDensityOnCube Q a p q x -
        (1 / 2 : ℝ) * vecDot p0 q0 := by
        simp [topHalfEnergyDensityOnCube, Ch02.variationEnergyIntegrand,
          canonicalMaximizerGradientOnCube, canonicalMaximizerFluxOnCube,
          vecDot_matVecMul_symmPart]

/-- Raw response as a parent half-energy average, centered by `p0 · q0 / 2`. -/
theorem centeredResponseJOnCube_eq_cubeAverage_topHalfEnergy_sub_half_dot
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 q0 : Vec d) :
    centeredResponseJOnCube Q a p q p0 q0 =
      cubeAverage Q (topHalfEnergyDensityOnCube Q a p q) -
        (1 / 2 : ℝ) * vecDot p0 q0 := by
  rw [centeredResponseJOnCube]
  rw [Ch02.responseJ_eq_energy_of_isResponseMaximizer
    ((Ch02.canonicalMaximizer
      (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) a) p q).isMaximizer)]
  rw [Ch02.variationEnergyValue, ch02_average_cubeDomain_eq_cubeAverage]
  rw [← cubeAverage_const_mul]
  rfl

/-- Raw response as a parent half-energy average. -/
theorem responseJOnCube_eq_cubeAverage_topHalfEnergy
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q : Vec d) :
    Ch02.responseJ (Ch02.cubeDomain Q) a p q =
      cubeAverage Q (topHalfEnergyDensityOnCube Q a p q) := by
  have h :=
    centeredResponseJOnCube_eq_cubeAverage_topHalfEnergy_sub_half_dot
      Q a p q (0 : Vec d) (0 : Vec d)
  simpa [centeredResponseJOnCube] using h

/-- The Chapter 2 energy integrand of a public solution is locally integrable. -/
theorem ch02_variationEnergyIntegrand_integrableOn {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (v : Ch02.Solution U a) :
    IntegrableOn (Ch02.variationEnergyIntegrand U a v)
      (U : Set (Vec d)) volume := by
  have hEll : IsAEEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField :=
    ch02_coeffOn_isAEEllipticFieldOn a
  have hflux : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x)) :=
    hEll.memVectorL2_matVecMul v.toH1.grad_memVectorL2
  have hUnsym :
      IntegrableOn
        (fun x => vecDot (v.toH1.grad x)
          (matVecMul (a.toCoeffField x) (v.toH1.grad x)))
        (U : Set (Vec d)) volume :=
    integrableOn_vecDot_of_memVectorL2 v.toH1.grad_memVectorL2 hflux
  refine hUnsym.congr_fun ?_ U.measurableSet
  intro x _hx
  exact (vecDot_matVecMul_symmPart (a.toCoeffField x) (v.toH1.grad x)).symm

/-- The Chapter 2 response integrand of a public solution is locally
integrable. -/
theorem ch02_responseIntegrand_integrableOn {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (p q : Vec d)
    (v : Ch02.Solution U a) :
    IntegrableOn (Ch02.responseIntegrand U a p q v)
      (U : Set (Vec d)) volume := by
  have hEnergy :
      IntegrableOn
        (fun x =>
          (1 / 2 : ℝ) *
            Ch02.variationEnergyIntegrand U a v x)
        (U : Set (Vec d)) volume :=
    (ch02_variationEnergyIntegrand_integrableOn U a v).const_mul (1 / 2 : ℝ)
  have hEll : IsAEEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField :=
    ch02_coeffOn_isAEEllipticFieldOn a
  have hFluxMem :
      MemVectorL2 (U : Set (Vec d))
        (fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x)) :=
    hEll.memVectorL2_matVecMul v.toH1.grad_memVectorL2
  have hFluxPair :
      IntegrableOn
        (fun x => vecDot p (matVecMul (a.toCoeffField x) (v.toH1.grad x)))
        (U : Set (Vec d)) volume :=
    CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 p hFluxMem
  have hGradPair :
      IntegrableOn (fun x => vecDot q (v.toH1.grad x))
        (U : Set (Vec d)) volume :=
    CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 q
      v.toH1.grad_memVectorL2
  have hAll :
      IntegrableOn
        (fun x =>
          -((1 / 2 : ℝ) *
              Ch02.variationEnergyIntegrand U a v x) -
            vecDot p (matVecMul (a.toCoeffField x) (v.toH1.grad x)) +
              vecDot q (v.toH1.grad x))
        (U : Set (Vec d)) volume :=
    (hEnergy.neg.sub hFluxPair).add hGradPair
  refine hAll.congr_fun ?_ U.measurableSet
  intro x _hx
  simp only [Ch02.responseIntegrand, Ch02.variationEnergyIntegrand]

/-- The parent half-energy density is integrable on the half-open cube. -/
theorem topHalfEnergyDensityOnCube_integrableOn_cubeSet {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q : Vec d) :
    IntegrableOn (topHalfEnergyDensityOnCube Q a p q) (cubeSet Q) volume := by
  have hOpen :=
    ch02_variationEnergyIntegrand_integrableOn
      (Ch02.cubeDomain Q) a (canonicalMaximizerSolutionOnCube Q a p q)
  have hCube :
      IntegrableOn
        (Ch02.variationEnergyIntegrand
          (Ch02.cubeDomain Q) a (canonicalMaximizerSolutionOnCube Q a p q))
      (cubeSet Q) volume := by
    rw [integrableOn_cubeSet_iff_integrableOn_openCubeSet]
    simpa [Ch02.cubeDomain_coe] using hOpen
  exact hCube.const_mul (1 / 2 : ℝ)

/-- The parent half-energy density is nonnegative a.e. on the half-open cube. -/
theorem topHalfEnergyDensityOnCube_ae_nonneg_cubeSet {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q : Vec d) :
    0 ≤ᵐ[volumeMeasureOn (cubeSet Q)] topHalfEnergyDensityOnCube Q a p q := by
  let coeff : CoeffField d := a.toCoeffField
  have hEllOpen :
      IsAEEllipticFieldOn a.lam a.Lam (openCubeSet Q) coeff := by
    simpa [coeff, Ch02.cubeDomain_coe] using
      (ch02_coeffOn_isAEEllipticFieldOn a)
  have hEll : IsAEEllipticFieldOn a.lam a.Lam (cubeSet Q) coeff :=
    hEllOpen.cubeSet_of_openCubeSet
  filter_upwards [hEll.ae_isEllipticMatrix] with x hxEll
  let g : Vec d := canonicalMaximizerGradientOnCube Q a p q x
  have hquad_nonneg :
      0 ≤ vecDot g (matVecMul (symmPart (coeff x)) g) := by
    have hlower := lowerBound_symmPart_of_isEllipticMatrix hxEll g
    have hnorm : 0 ≤ vecNormSq g := vecNormSq_nonneg g
    have hlam_pos : 0 < a.lam := hxEll.1
    nlinarith
  have henergy_nonneg :
      0 ≤
        vecDot ((canonicalMaximizerSolutionOnCube Q a p q).toH1.grad x)
          (matVecMul (symmPart (a.toCoeffField x))
            ((canonicalMaximizerSolutionOnCube Q a p q).toH1.grad x)) := by
    simpa [g, coeff, canonicalMaximizerGradientOnCube] using hquad_nonneg
  dsimp [topHalfEnergyDensityOnCube, Ch02.variationEnergyIntegrand]
  nlinarith

/-- A bounded a.e.-strongly-measurable multiplier preserves local
integrability. -/
theorem integrableOn_mul_left_of_integrableOn_of_ae_bounded
    {d : ℕ} {U : Set (Vec d)} {φ f : Vec d → ℝ} {C : ℝ}
    (hf : IntegrableOn f U volume)
    (hφ_meas : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφ_bound : ∀ᵐ x ∂ volumeMeasureOn U, ‖φ x‖ ≤ C) :
    IntegrableOn (fun x => φ x * f x) U volume := by
  have hf_int : Integrable f (volumeMeasureOn U) := by
    simpa [IntegrableOn, volumeMeasureOn] using hf
  simpa [IntegrableOn, volumeMeasureOn] using
    (hf_int.bdd_mul hφ_meas hφ_bound)

/-- Components of the raw canonical maximizer gradient defect are integrable
on the parent cube. -/
theorem canonicalMaximizerGradientDefectOnCube_component_integrableOn
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 : Vec d) (i : Fin d) :
    IntegrableOn (fun x => canonicalMaximizerGradientDefectOnCube Q a p q p0 x i)
      (cubeSet Q) volume := by
  have hcomp :
      MemLp (fun x => canonicalMaximizerGradientDefectOnCube Q a p q p0 x i)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_component_of_memLp
      (canonicalMaximizerGradientDefectOnCube Q a p q p0) i
      (canonicalMaximizerGradientDefectOnCube_memLp Q a p q p0)
  exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
    (hcomp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))

/-- Components of the raw canonical maximizer flux defect are integrable on
the parent cube. -/
theorem canonicalMaximizerFluxDefectOnCube_component_integrableOn
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q q0 : Vec d) (i : Fin d) :
    IntegrableOn (fun x => canonicalMaximizerFluxDefectOnCube Q a p q q0 x i)
      (cubeSet Q) volume := by
  have hcomp :
      MemLp (fun x => canonicalMaximizerFluxDefectOnCube Q a p q q0 x i)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_component_of_memLp
      (canonicalMaximizerFluxDefectOnCube Q a p q q0) i
      (canonicalMaximizerFluxDefectOnCube_memLp Q a p q q0)
  exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
    (hcomp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))

/-- The centered product density in the deterministic Section 5.3 split is
integrable on the parent cube. -/
theorem centeredProductDensityOnCube_integrableOn_cubeSet
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 q0 : Vec d) :
    IntegrableOn (centeredProductDensityOnCube Q a p q p0 q0)
      (cubeSet Q) volume := by
  let gradDef : Vec d → Vec d := canonicalMaximizerGradientDefectOnCube Q a p q p0
  let fluxDef : Vec d → Vec d := canonicalMaximizerFluxDefectOnCube Q a p q q0
  have hgrad : MemLp gradDef (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [gradDef] using canonicalMaximizerGradientDefectOnCube_memLp Q a p q p0
  have hflux : MemLp fluxDef (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [fluxDef] using canonicalMaximizerFluxDefectOnCube_memLp Q a p q q0
  have hdot :
      Integrable (fun x => vecDot (gradDef x) (fluxDef x))
        (normalizedCubeMeasure Q) := by
    rw [show (fun x => vecDot (gradDef x) (fluxDef x)) =
        fun x => ∑ i : Fin d, gradDef x i * fluxDef x i by
          funext x
          simp [vecDot]]
    exact MeasureTheory.integrable_finsetSum _ fun i _ =>
      (memLp_component_of_memLp gradDef i hgrad).integrable_mul
        (memLp_component_of_memLp fluxDef i hflux)
  have hprod :
      Integrable (centeredProductDensityOnCube Q a p q p0 q0)
        (normalizedCubeMeasure Q) := by
    change Integrable
      (fun x =>
        (1 / 2 : ℝ) *
          vecDot (canonicalMaximizerGradientDefectOnCube Q a p q p0 x)
            (canonicalMaximizerFluxDefectOnCube Q a p q q0 x))
      (normalizedCubeMeasure Q)
    simpa [gradDef, fluxDef, one_div] using
      hdot.const_mul (1 / 2 : ℝ)
  exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q) hprod

/-- The centered gradient-linear density in the deterministic Section 5.3
split is integrable on the parent cube. -/
theorem centeredGradientLinearDensityOnCube_integrableOn_cubeSet
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 q0 : Vec d) :
    IntegrableOn (centeredGradientLinearDensityOnCube Q a p q p0 q0)
      (cubeSet Q) volume := by
  let gradDef : Vec d → Vec d := canonicalMaximizerGradientDefectOnCube Q a p q p0
  have hgrad : MemLp gradDef (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [gradDef] using canonicalMaximizerGradientDefectOnCube_memLp Q a p q p0
  have hdot :
      Integrable (fun x => vecDot q0 (gradDef x)) (normalizedCubeMeasure Q) := by
    rw [show (fun x => vecDot q0 (gradDef x)) =
        fun x => ∑ i : Fin d, q0 i * gradDef x i by
          funext x
          simp [vecDot]]
    exact MeasureTheory.integrable_finsetSum _ fun i _ =>
      ((memLp_component_of_memLp gradDef i hgrad).integrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)).const_mul (q0 i)
  have hlin :
      Integrable (centeredGradientLinearDensityOnCube Q a p q p0 q0)
        (normalizedCubeMeasure Q) := by
    change Integrable
      (fun x =>
        (1 / 2 : ℝ) *
          vecDot q0 (canonicalMaximizerGradientDefectOnCube Q a p q p0 x))
      (normalizedCubeMeasure Q)
    simpa [gradDef, one_div] using
      hdot.const_mul (1 / 2 : ℝ)
  exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q) hlin

/-- The centered flux-linear density in the deterministic Section 5.3 split
is integrable on the parent cube. -/
theorem centeredFluxLinearDensityOnCube_integrableOn_cubeSet
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (p q p0 q0 : Vec d) :
    IntegrableOn (centeredFluxLinearDensityOnCube Q a p q p0 q0)
      (cubeSet Q) volume := by
  let fluxDef : Vec d → Vec d := canonicalMaximizerFluxDefectOnCube Q a p q q0
  have hflux : MemLp fluxDef (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [fluxDef] using canonicalMaximizerFluxDefectOnCube_memLp Q a p q q0
  have hdot :
      Integrable (fun x => vecDot p0 (fluxDef x)) (normalizedCubeMeasure Q) := by
    rw [show (fun x => vecDot p0 (fluxDef x)) =
        fun x => ∑ i : Fin d, p0 i * fluxDef x i by
          funext x
          simp [vecDot]]
    exact MeasureTheory.integrable_finsetSum _ fun i _ =>
      ((memLp_component_of_memLp fluxDef i hflux).integrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)).const_mul (p0 i)
  have hlin :
      Integrable (centeredFluxLinearDensityOnCube Q a p q p0 q0)
        (normalizedCubeMeasure Q) := by
    change Integrable
      (fun x =>
        (1 / 2 : ℝ) *
          vecDot p0 (canonicalMaximizerFluxDefectOnCube Q a p q q0 x))
      (normalizedCubeMeasure Q)
    simpa [fluxDef, one_div] using
      hdot.const_mul (1 / 2 : ℝ)
  exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q) hlin

/-- A bounded cutoff gives the descendant cutoff-oscillation integrability
condition. -/
theorem cutoffOscillationTermOnCubeAtDepth_integrableOn_descendants_of_ae_bounded
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (j : ℕ) {φ : Vec d → ℝ} {C : ℝ} (p q : Vec d)
    (hφ_meas : AEStronglyMeasurable φ (volumeMeasureOn (cubeSet Q)))
    (hφ_bound : ∀ᵐ x ∂ volumeMeasureOn (cubeSet Q), ‖φ x‖ ≤ C) :
    ∀ R ∈ descendantsAtDepth Q j,
      IntegrableOn
        (fun x =>
          (cubeAverage R φ - φ x) * topHalfEnergyDensityOnCube Q a p q x)
        (cubeSet R) volume := by
  intro R hR
  have hsubset : cubeSet R ⊆ cubeSet Q :=
    cubeSet_subset_of_mem_descendantsAtDepth hR
  have hle :
      volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
    simpa [volumeMeasureOn] using
      MeasureTheory.Measure.restrict_mono_set volume hsubset
  have hφ_measR :
      AEStronglyMeasurable φ (volumeMeasureOn (cubeSet R)) :=
    hφ_meas.mono_measure hle
  have hφ_boundR :
      ∀ᵐ x ∂ volumeMeasureOn (cubeSet R), ‖φ x‖ ≤ C :=
    hφ_bound.filter_mono (MeasureTheory.ae_mono hle)
  have hdiff_meas :
      AEStronglyMeasurable (fun x : Vec d => cubeAverage R φ - φ x)
        (volumeMeasureOn (cubeSet R)) :=
    (aestronglyMeasurable_const (b := cubeAverage R φ)).sub hφ_measR
  have hdiff_bound :
      ∀ᵐ x ∂ volumeMeasureOn (cubeSet R),
        ‖cubeAverage R φ - φ x‖ ≤ |cubeAverage R φ| + C := by
    filter_upwards [hφ_boundR] with x hx
    calc
      ‖cubeAverage R φ - φ x‖ = |cubeAverage R φ - φ x| :=
        Real.norm_eq_abs _
      _ ≤ |cubeAverage R φ| + |φ x| := by
            simpa [sub_eq_add_neg] using
              abs_add_le (cubeAverage R φ) (-φ x)
      _ = |cubeAverage R φ| + ‖φ x‖ := by simp [Real.norm_eq_abs]
      _ ≤ |cubeAverage R φ| + C := by nlinarith [hx]
  have hTopR :
      IntegrableOn (topHalfEnergyDensityOnCube Q a p q) (cubeSet R) volume :=
    (topHalfEnergyDensityOnCube_integrableOn_cubeSet Q a p q).mono_set hsubset
  exact
    integrableOn_mul_left_of_integrableOn_of_ae_bounded
      hTopR hdiff_meas hdiff_bound

/--
Cube-average estimate for a bounded oscillating scalar times a nonnegative
integrable density.
-/
theorem abs_cubeAverage_mul_nonneg_le_mul_cubeAverage_of_ae_abs_le
    {d : ℕ} (R : TriadicCube d) {w f : Vec d → ℝ} {B : ℝ}
    (hf_int : IntegrableOn f (cubeSet R) volume)
    (hwf_int : IntegrableOn (fun x => w x * f x) (cubeSet R) volume)
    (hf_nonneg : 0 ≤ᵐ[volumeMeasureOn (cubeSet R)] f)
    (hw_bound : ∀ᵐ x ∂ volumeMeasureOn (cubeSet R), |w x| ≤ B) :
    |cubeAverage R (fun x => w x * f x)| ≤
      B * cubeAverage R f := by
  have hwf_int' : Integrable (fun x => w x * f x)
      (volumeMeasureOn (cubeSet R)) := by
    simpa [IntegrableOn, volumeMeasureOn] using hwf_int
  have habs_int :
      Integrable (fun x => |w x * f x|)
        (volumeMeasureOn (cubeSet R)) := by
    simpa [Real.norm_eq_abs] using hwf_int'.norm
  have hBf_int :
      Integrable (fun x => B * f x) (volumeMeasureOn (cubeSet R)) := by
    have hf_int' : Integrable f (volumeMeasureOn (cubeSet R)) := by
      simpa [IntegrableOn, volumeMeasureOn] using hf_int
    exact hf_int'.const_mul B
  have hpoint :
      (fun x => |w x * f x|) ≤ᵐ[volumeMeasureOn (cubeSet R)]
        fun x => B * f x := by
    filter_upwards [hf_nonneg, hw_bound] with x hf_pos hw
    calc
      |w x * f x| = |w x| * f x := by
        rw [abs_mul, abs_of_nonneg hf_pos]
      _ ≤ B * f x := mul_le_mul_of_nonneg_right hw hf_pos
  have hint_abs_le :
      ∫ x, |w x * f x| ∂ volumeMeasureOn (cubeSet R) ≤
        ∫ x, B * f x ∂ volumeMeasureOn (cubeSet R) :=
    integral_mono_ae habs_int hBf_int hpoint
  rw [cubeAverage]
  have hinv_nonneg : 0 ≤ (cubeVolume R)⁻¹ :=
    inv_nonneg.mpr (cubeVolume_nonneg R)
  calc
    |(cubeVolume R)⁻¹ * ∫ x in cubeSet R, w x * f x ∂volume|
        = (cubeVolume R)⁻¹ *
            |∫ x in cubeSet R, w x * f x ∂volume| := by
          rw [abs_mul, abs_of_nonneg hinv_nonneg]
    _ ≤ (cubeVolume R)⁻¹ *
          ∫ x, |w x * f x| ∂ volumeMeasureOn (cubeSet R) := by
        exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hinv_nonneg
    _ ≤ (cubeVolume R)⁻¹ *
          ∫ x, B * f x ∂ volumeMeasureOn (cubeSet R) := by
        exact mul_le_mul_of_nonneg_left hint_abs_le hinv_nonneg
    _ = B * ((cubeVolume R)⁻¹ * ∫ x in cubeSet R, f x ∂volume) := by
        rw [integral_const_mul]
        ring

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
