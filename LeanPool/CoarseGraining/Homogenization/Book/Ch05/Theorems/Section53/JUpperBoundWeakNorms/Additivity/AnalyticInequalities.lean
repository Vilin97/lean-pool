/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.ParentRestriction

/-! # Analytic Inequalities -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# AdditivityAnalyticInequalities

Finite-measure Cauchy inequalities for the additivity-cross term.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- The local sum half-energy density is locally integrable. -/
theorem additivitySumHalfEnergyDensityOnFamilyOnCube_integrableOn
    {d : ℕ} [NeZero d] (a : Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    IntegrableOn (additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q)
      (cubeSet R) volume := by
  let : IsFiniteMeasure (volumeMeasureOn (cubeSet R)) := by
    let : Fact (volume (cubeSet R) < ⊤) := ⟨volume_cubeSet_lt_top R⟩
    change IsFiniteMeasure (volume.restrict (cubeSet R))
    infer_instance
  let topGrad : Vec d → Vec d :=
    canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q
  let childGrad : Vec d → Vec d :=
    canonicalMaximizerGradientOnCube R (a.coeffOn R) p q
  let coeff : CoeffField d := (a.coeffOn R).toCoeffField
  have hTop : MemVectorL2 (cubeSet R) topGrad := by
    simpa [topGrad, canonicalMaximizerGradientOnCube] using!
      (Ch03.publicH1ToCubeSet_grad_memVectorL2_descendant_cubeSet
        (Q := Q) (R := R) (j := j)
        (canonicalMaximizerSolutionOnCube Q (a.coeffOn Q) p q).toH1 hR)
  have hChild : MemVectorL2 (cubeSet R) childGrad := by
    have h :=
      (Ch03.publicH1ToCubeSet
        (Q := R) (canonicalMaximizerSolutionOnCube R (a.coeffOn R) p q).toH1).grad_memVectorL2
    simpa [childGrad, canonicalMaximizerGradientOnCube, Ch03.publicH1ToCubeSet_grad] using! h
  have hSumGrad : MemVectorL2 (cubeSet R) (fun x => topGrad x + childGrad x) := by
    simpa using! hTop.add hChild
  have hEllOpen :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (openCubeSet R) coeff := by
    simpa [coeff, Ch02.cubeDomain_coe] using
      (ch02_coeffOn_isAEEllipticFieldOn (a.coeffOn R))
  have hEll :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (cubeSet R) coeff :=
    hEllOpen.cubeSet_of_openCubeSet
  have hSymmSum :
      MemVectorL2 (cubeSet R)
        (fun x => matVecMul (symmPart (coeff x)) (topGrad x + childGrad x)) :=
    IsAEEllipticFieldOn.memVectorL2_matVecMul_symmPart hEll hSumGrad
  have hQuad :
      IntegrableOn
        (fun x => vecDot (topGrad x + childGrad x)
          (matVecMul (symmPart (coeff x)) (topGrad x + childGrad x)))
        (cubeSet R) volume :=
    integrableOn_vecDot_of_memVectorL2 hSumGrad hSymmSum
  show IntegrableOn
    (fun x =>
      (1 / 2 : ℝ) *
        vecDot
          (canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x +
            canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)
          (matVecMul (symmPart ((a.coeffOn R).toCoeffField x))
            (canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x +
              canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)))
      (cubeSet R) volume
  simpa [additivitySumHalfEnergyDensityOnFamilyOnCube, topGrad, childGrad, coeff] using!
    hQuad.const_mul (1 / 2 : ℝ)

/-- An integrable nonnegative scalar density has a square root in normalized
`L²`. -/
theorem memLp_sqrt_two_of_integrable_of_ae_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf_int : Integrable f μ) (hf_nonneg : 0 ≤ᵐ[μ] f) :
    MemLp (fun x => Real.sqrt (f x)) (2 : ℝ≥0∞) μ := by
  let sqrtF : α → ℝ := fun x => Real.sqrt (f x)
  have hf_mem_one : MemLp f 1 μ :=
    memLp_one_iff_integrable.mpr hf_int
  have hsqrt_meas : AEStronglyMeasurable sqrtF μ :=
    hf_int.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
  have hnorm_sq_ae :
      (fun x => ‖sqrtF x‖ ^ (2 : ℝ)) =ᵐ[μ] f := by
    filter_upwards [hf_nonneg] with x hx
    have hnorm : ‖sqrtF x‖ = Real.sqrt (f x) := by
      simp [sqrtF, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hnorm]
    simpa [Real.rpow_natCast] using Real.sq_sqrt hx
  have hnorm_sq_mem_one :
      MemLp (fun x => ‖sqrtF x‖ ^ (2 : ℝ)) 1 μ :=
    (memLp_congr_ae hnorm_sq_ae).2 hf_mem_one
  have hnorm_sq_mem_div :
      MemLp (fun x => ‖sqrtF x‖ ^ (2 : ℝ))
        ((2 : ℝ≥0∞) / (2 : ℝ≥0∞)) μ := by
    have hdiv : ((2 : ℝ≥0∞) / (2 : ℝ≥0∞)) = 1 :=
      ENNReal.div_self (by norm_num) (by norm_num)
    rw [hdiv]
    exact hnorm_sq_mem_one
  have hiff :=
    memLp_norm_rpow_iff
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      (f := sqrtF) (μ := μ) hsqrt_meas
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  simpa [sqrtF] using hiff.mp hnorm_sq_mem_div

/-- Cauchy-Schwarz for square roots of nonnegative integrable scalar
observables, in the form used by the stochastic additivity term. -/
theorem integral_sqrt_mul_sqrt_le_sqrt_integral_mul_sqrt_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {A B : α → ℝ}
    (hA_int : Integrable A μ) (hB_int : Integrable B μ)
    (hA_nonneg : 0 ≤ᵐ[μ] A) (hB_nonneg : 0 ≤ᵐ[μ] B) :
    ∫ x, Real.sqrt (A x) * Real.sqrt (B x) ∂μ ≤
      Real.sqrt (∫ x, A x ∂μ) * Real.sqrt (∫ x, B x ∂μ) := by
  let sqrtA : α → ℝ := fun x => Real.sqrt (A x)
  let sqrtB : α → ℝ := fun x => Real.sqrt (B x)
  have hSqrtA_mem :
      MemLp sqrtA (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa [sqrtA] using
      memLp_sqrt_two_of_integrable_of_ae_nonneg hA_int hA_nonneg
  have hSqrtB_mem :
      MemLp sqrtB (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa [sqrtB] using
      memLp_sqrt_two_of_integrable_of_ae_nonneg hB_int hB_nonneg
  have hSqrtA_nonneg : 0 ≤ᵐ[μ] sqrtA := by
    filter_upwards with x
    exact Real.sqrt_nonneg _
  have hSqrtB_nonneg : 0 ≤ᵐ[μ] sqrtB := by
    filter_upwards with x
    exact Real.sqrt_nonneg _
  have hHolder :
      ∫ x, sqrtA x * sqrtB x ∂μ ≤
        (∫ x, sqrtA x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, sqrtB x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      hSqrtA_nonneg hSqrtB_nonneg hSqrtA_mem hSqrtB_mem
  have hA_sq :
      (∫ x, sqrtA x ^ (2 : ℝ) ∂μ) = ∫ x, A x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hA_nonneg] with x hx
    simpa [sqrtA, Real.rpow_natCast] using Real.sq_sqrt hx
  have hB_sq :
      (∫ x, sqrtB x ^ (2 : ℝ) ∂μ) = ∫ x, B x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hB_nonneg] with x hx
    simpa [sqrtB, Real.rpow_natCast] using Real.sq_sqrt hx
  calc
    ∫ x, Real.sqrt (A x) * Real.sqrt (B x) ∂μ
        = ∫ x, sqrtA x * sqrtB x ∂μ := by rfl
    _ ≤
        (∫ x, sqrtA x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, sqrtB x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hHolder
    _ =
        Real.sqrt (∫ x, A x ∂μ) * Real.sqrt (∫ x, B x ∂μ) := by
          rw [hA_sq, hB_sq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

/-- Integrability companion to the square-root Cauchy estimate. -/
theorem integrable_sqrt_mul_sqrt_of_integrable_of_ae_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {A B : α → ℝ}
    (hA_int : Integrable A μ) (hB_int : Integrable B μ)
    (hA_nonneg : 0 ≤ᵐ[μ] A) (hB_nonneg : 0 ≤ᵐ[μ] B) :
    Integrable (fun x => Real.sqrt (A x) * Real.sqrt (B x)) μ := by
  let sqrtA : α → ℝ := fun x => Real.sqrt (A x)
  let sqrtB : α → ℝ := fun x => Real.sqrt (B x)
  have hSqrtA_mem :
      MemLp sqrtA (2 : ℝ≥0∞) μ := by
    simpa [sqrtA] using
      memLp_sqrt_two_of_integrable_of_ae_nonneg hA_int hA_nonneg
  have hSqrtB_mem :
      MemLp sqrtB (2 : ℝ≥0∞) μ := by
    simpa [sqrtB] using
      memLp_sqrt_two_of_integrable_of_ae_nonneg hB_int hB_nonneg
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) := by
    infer_instance
  have hProd_mem : MemLp (fun x => sqrtA x * sqrtB x) 1 μ := by
    simpa [sqrtA, sqrtB] using! hSqrtB_mem.mul hSqrtA_mem
  simpa [sqrtA, sqrtB] using hProd_mem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)

/-- Integrability of a nonnegative product from square integrability of both
factors. -/
theorem integrable_mul_of_integrable_sq_of_ae_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {X Y : α → ℝ}
    (hX_sq : Integrable (fun x => (X x) ^ 2) μ)
    (hY_sq : Integrable (fun x => (Y x) ^ 2) μ)
    (hX_nonneg : 0 ≤ᵐ[μ] X) (hY_nonneg : 0 ≤ᵐ[μ] Y) :
    Integrable (fun x => X x * Y x) μ := by
  have hsqrt :
      Integrable
        (fun x => Real.sqrt ((X x) ^ 2) * Real.sqrt ((Y x) ^ 2)) μ :=
    integrable_sqrt_mul_sqrt_of_integrable_of_ae_nonneg
      (A := fun x => (X x) ^ 2) (B := fun x => (Y x) ^ 2)
      hX_sq hY_sq
      (by filter_upwards with x; exact sq_nonneg (X x))
      (by filter_upwards with x; exact sq_nonneg (Y x))
  refine hsqrt.congr ?_
  filter_upwards [hX_nonneg, hY_nonneg] with x hx hy
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg hx, abs_of_nonneg hy]

/-- Cauchy-Schwarz in the form needed for the manuscript product of the two
scaled weak norms. -/
theorem integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq_of_ae_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {X Y : α → ℝ}
    (hX_sq : Integrable (fun x => (X x) ^ 2) μ)
    (hY_sq : Integrable (fun x => (Y x) ^ 2) μ)
    (hX_nonneg : 0 ≤ᵐ[μ] X) (hY_nonneg : 0 ≤ᵐ[μ] Y) :
    ∫ x, X x * Y x ∂μ ≤
      Real.sqrt (∫ x, (X x) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (Y x) ^ 2 ∂μ) := by
  have hsqrt :=
    integral_sqrt_mul_sqrt_le_sqrt_integral_mul_sqrt_integral
      (μ := μ) (A := fun x => (X x) ^ 2) (B := fun x => (Y x) ^ 2)
      hX_sq hY_sq
      (by filter_upwards with x; exact sq_nonneg (X x))
      (by filter_upwards with x; exact sq_nonneg (Y x))
  have hleft :
      ∫ x, X x * Y x ∂μ =
        ∫ x, Real.sqrt ((X x) ^ 2) * Real.sqrt ((Y x) ^ 2) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hX_nonneg, hY_nonneg] with x hx hy
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg hx, abs_of_nonneg hy]
  simpa [hleft] using hsqrt

/-- If `|F| ≤ sqrt A sqrt B` a.e. on a normalized cube, then the cube average
of `F` is bounded by the square roots of the cube averages of `A` and `B`. -/
theorem abs_cubeAverage_le_sqrt_cubeAverage_mul_sqrt_cubeAverage_of_ae_abs_le_sqrt_mul_sqrt
    {d : ℕ} (Q : TriadicCube d) {F A B : Vec d → ℝ}
    (hF_int : Integrable F (normalizedCubeMeasure Q))
    (hA_nonneg : 0 ≤ᵐ[normalizedCubeMeasure Q] A)
    (hB_nonneg : 0 ≤ᵐ[normalizedCubeMeasure Q] B)
    (hSqrtA_mem :
      MemLp (fun x => Real.sqrt (A x)) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hSqrtB_mem :
      MemLp (fun x => Real.sqrt (B x)) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hPoint :
      ∀ᵐ x ∂ normalizedCubeMeasure Q,
        |F x| ≤ Real.sqrt (A x) * Real.sqrt (B x)) :
    |cubeAverage Q F| ≤
      Real.sqrt (cubeAverage Q A) * Real.sqrt (cubeAverage Q B) := by
  let μ : Measure (Vec d) := normalizedCubeMeasure Q
  let sqrtA : Vec d → ℝ := fun x => Real.sqrt (A x)
  let sqrtB : Vec d → ℝ := fun x => Real.sqrt (B x)
  have hProd_nonneg : 0 ≤ᵐ[μ] fun x => sqrtA x * sqrtB x := by
    filter_upwards with x
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) := by
    infer_instance
  have hProd_mem : MemLp (fun x => sqrtA x * sqrtB x) 1 μ := by
    simpa [μ, sqrtA, sqrtB] using! hSqrtB_mem.mul hSqrtA_mem
  have hProd_int : Integrable (fun x => sqrtA x * sqrtB x) μ :=
    hProd_mem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  have hAbs_le :
      (fun x => |F x|) ≤ᵐ[μ] fun x => sqrtA x * sqrtB x := by
    simpa [μ, sqrtA, sqrtB] using! hPoint
  have hInt_abs_le :
      ∫ x, |F x| ∂μ ≤ ∫ x, sqrtA x * sqrtB x ∂μ :=
    integral_mono_ae hF_int.norm hProd_int hAbs_le
  have hProd_avg_nonneg :
      0 ≤ cubeAverage Q (fun x => sqrtA x * sqrtB x) := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_nonneg_of_ae (by simpa [μ] using hProd_nonneg)
  have hHolder :
      |cubeAverage Q (fun x => sqrtA x * sqrtB x)| ≤
        cubeLpNorm Q (2 : ℝ≥0∞) sqrtA *
          cubeLpNorm Q (2 : ℝ≥0∞) sqrtB := by
    let : ENNReal.HolderConjugate (2 : ℝ≥0∞) (2 : ℝ≥0∞) := by
      infer_instance
    exact
      abs_cubeAverage_mul_le_mul_cubeLpNorm_of_holderConjugate
        Q (2 : ℝ≥0∞) (2 : ℝ≥0∞) sqrtA sqrtB
        (by simpa [sqrtA] using hSqrtA_mem)
        (by simpa [sqrtB] using hSqrtB_mem)
  have hAavg_nonneg : 0 ≤ cubeAverage Q A := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_nonneg_of_ae hA_nonneg
  have hBavg_nonneg : 0 ≤ cubeAverage Q B := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_nonneg_of_ae hB_nonneg
  have hSqrtA_norm :
      cubeLpNorm Q (2 : ℝ≥0∞) sqrtA = Real.sqrt (cubeAverage Q A) := by
    have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hpTop : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
    have hpow :=
      cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
        (Q := Q) (p := (2 : ℝ≥0∞)) (f := sqrtA) hp0 hpTop
        (by simpa [sqrtA] using hSqrtA_mem)
    have hpow_two :
        cubeLpNorm Q (2 : ℝ≥0∞) sqrtA ^ (2 : ℝ) =
          cubeAverage Q (fun x => ‖sqrtA x‖ ^ (2 : ℝ)) := by
      simpa using hpow
    have havg_norm :
        cubeAverage Q (fun x => ‖sqrtA x‖ ^ (2 : ℝ)) =
          cubeAverage Q A := by
      rw [cubeAverage_eq_integral_normalizedCubeMeasure,
        cubeAverage_eq_integral_normalizedCubeMeasure]
      refine integral_congr_ae ?_
      filter_upwards [hA_nonneg] with x hx
      have hsqrt_abs : ‖sqrtA x‖ = Real.sqrt (A x) := by
        simp [sqrtA, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [hsqrt_abs]
      simpa [Real.rpow_natCast] using Real.sq_sqrt hx
    have hsq :
        cubeLpNorm Q (2 : ℝ≥0∞) sqrtA ^ 2 = cubeAverage Q A := by
      simpa [Real.rpow_natCast] using hpow_two.trans havg_norm
    symm
    rw [Real.sqrt_eq_iff_eq_sq hAavg_nonneg
      (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) sqrtA)]
    exact hsq.symm
  have hSqrtB_norm :
      cubeLpNorm Q (2 : ℝ≥0∞) sqrtB = Real.sqrt (cubeAverage Q B) := by
    have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hpTop : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
    have hpow :=
      cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
        (Q := Q) (p := (2 : ℝ≥0∞)) (f := sqrtB) hp0 hpTop
        (by simpa [sqrtB] using hSqrtB_mem)
    have hpow_two :
        cubeLpNorm Q (2 : ℝ≥0∞) sqrtB ^ (2 : ℝ) =
          cubeAverage Q (fun x => ‖sqrtB x‖ ^ (2 : ℝ)) := by
      simpa using hpow
    have havg_norm :
        cubeAverage Q (fun x => ‖sqrtB x‖ ^ (2 : ℝ)) =
          cubeAverage Q B := by
      rw [cubeAverage_eq_integral_normalizedCubeMeasure,
        cubeAverage_eq_integral_normalizedCubeMeasure]
      refine integral_congr_ae ?_
      filter_upwards [hB_nonneg] with x hx
      have hsqrt_abs : ‖sqrtB x‖ = Real.sqrt (B x) := by
        simp [sqrtB, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [hsqrt_abs]
      simpa [Real.rpow_natCast] using Real.sq_sqrt hx
    have hsq :
        cubeLpNorm Q (2 : ℝ≥0∞) sqrtB ^ 2 = cubeAverage Q B := by
      simpa [Real.rpow_natCast] using hpow_two.trans havg_norm
    symm
    rw [Real.sqrt_eq_iff_eq_sq hBavg_nonneg
      (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) sqrtB)]
    exact hsq.symm
  calc
    |cubeAverage Q F|
        = |∫ x, F x ∂μ| := by
            rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    _ ≤ ∫ x, |F x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, sqrtA x * sqrtB x ∂μ := hInt_abs_le
    _ = cubeAverage Q (fun x => sqrtA x * sqrtB x) := by
          rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    _ = |cubeAverage Q (fun x => sqrtA x * sqrtB x)| := by
          rw [abs_of_nonneg hProd_avg_nonneg]
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) sqrtA *
          cubeLpNorm Q (2 : ℝ≥0∞) sqrtB := hHolder
    _ = Real.sqrt (cubeAverage Q A) * Real.sqrt (cubeAverage Q B) := by
          rw [hSqrtA_norm, hSqrtB_norm]

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
