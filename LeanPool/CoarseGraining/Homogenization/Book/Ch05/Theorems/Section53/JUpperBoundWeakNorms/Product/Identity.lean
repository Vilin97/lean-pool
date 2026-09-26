/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Product.Bridge

/-! # Identity -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# ProductIdentity

Cutoff-product identities from first variation.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- First-variation identity converting the actual cutoff product term into
the flux-defect/product-gradient pairing consumed by the deterministic
cutoff-product bridge. -/
theorem cutoffProductTermOnCube_eq_neg_half_cubeAverage_fluxDefect_potentialDefect_smul_scalarCutoffGradientField
    {d : ℕ} (Q : TriadicCube d)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) {φ : Vec d → ℝ}
    (p q p0 q0 : Vec d)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet Q) :
    cutoffProductTermOnCube Q a φ p q p0 q0 =
      -(1 / 2 : ℝ) *
        cubeAverage Q
          (fun x =>
            vecDot (canonicalMaximizerFluxDefectOnCube Q a p q q0 x)
              (canonicalMaximizerPotentialDefectOnCube Q a p q p0 x •
                scalarCutoffGradientField φ x)) := by
  classical
  let U : Set (Vec d) := ((Ch02.cubeDomain Q : Ch02.Domain d) : Set (Vec d))
  let v : Ch02.Solution (Ch02.cubeDomain Q) a :=
    canonicalMaximizerSolutionOnCube Q a p q
  let flux : Vec d → Vec d :=
    fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x)
  let fluxDef : Vec d → Vec d := fun x => flux x - q0
  let u : H1Function U :=
    canonicalMaximizerPotentialDefectH1OnCube Q a p q p0
  let uφ : H1Function U := u.mulContDiffHasCompactSupport hφ hφ_compact
  have hφ_sub_U : tsupport φ ⊆ U := by
    simpa [U, Ch02.cubeDomain_coe] using hφ_sub
  let ψ : H10Function U :=
    u.mulContDiffHasCompactSupportToH10
      (Ch02.cubeDomain Q).isDomain hφ hφ_compact hφ_sub_U
  have hflux_mem : MemVectorL2 U flux := by
    simpa [U, flux, v, canonicalMaximizerSolutionOnCube] using
      Ch02.Solution.flux_memVectorL2 (canonicalMaximizerSolutionOnCube Q a p q)
  have hconst_mem : MemVectorL2 U (fun _ : Vec d => q0) :=
    MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) q0
  have hfluxDef_mem : MemVectorL2 U fluxDef := by
    simpa [fluxDef] using! hflux_mem.sub hconst_mem
  have hpair_vec_mem :
      MemVectorL2 U (fun x => u x • scalarCutoffGradientField φ x) := by
    simpa [MemVectorL2, volumeMeasureOn, Pi.smul_apply, smul_eq_mul, mul_comm] using
      (MeasureTheory.MemLp.of_eval fun i : Fin d => by
        have hgradφ_compact :
            HasCompactSupport (fun x => scalarCutoffGradientField φ x i) := by
          simpa [scalarCutoffGradientField] using
            hφ_compact.fderiv_apply (𝕜 := ℝ) (basisVec i)
        rcases
            memH1_mul_of_contDiff_hasCompactSupport
              (contDiff_scalarCutoffGradientField_component hφ i) hgradφ_compact
              u.memH1 with
          ⟨w, hw_toFun⟩
        simpa [hw_toFun, mul_comm] using w.memL2)
  have hpair_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (fluxDef x) (u x • scalarCutoffGradientField φ x)) U :=
    integrableOn_vecDot_of_memVectorL2 hfluxDef_mem hpair_vec_mem
  have hprod_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (fluxDef x) (uφ.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hfluxDef_mem uφ.grad_memVectorL2
  have hgrad_ae :
      (fun x => ψ.toH1Function.grad x) =ᵐ[MeasureTheory.volume.restrict U]
        (fun x => uφ.grad x) := by
    simpa only [ψ, uφ, H1Function.mulContDiffHasCompactSupport_grad] using
      WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
        u (Ch02.cubeDomain Q).isDomain hφ hφ_compact hφ_sub_U
  have hsol_ψ :
      ∫ x in U, vecDot (fluxDef x) (ψ.toH1Function.grad x)
          ∂MeasureTheory.volume = 0 := by
    have hdrop_const :
        ∫ x in U, vecDot (fluxDef x) (ψ.toH1Function.grad x)
            ∂MeasureTheory.volume =
          ∫ x in U, vecDot (flux x) (ψ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
      simpa [fluxDef] using
        integral_vecDot_sub_const_zeroTraceGrad_eq (U := U) hflux_mem ψ q0
    calc
      ∫ x in U, vecDot (fluxDef x) (ψ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, vecDot (flux x) (ψ.toH1Function.grad x)
          ∂MeasureTheory.volume := hdrop_const
      _ = 0 := by
        simpa [U, flux, v, canonicalMaximizerSolutionOnCube] using
          (canonicalMaximizerSolutionOnCube Q a p q).isHarmonic.2 ψ
  have hsol_uφ :
      ∫ x in U, vecDot (fluxDef x) (uφ.grad x) ∂MeasureTheory.volume = 0 := by
    calc
      ∫ x in U, vecDot (fluxDef x) (uφ.grad x) ∂MeasureTheory.volume =
          ∫ x in U, vecDot (fluxDef x) (ψ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [hgrad_ae] with x hx
              rw [hx]
      _ = 0 := hsol_ψ
  let first : Vec d → ℝ :=
    fun x => φ x * vecDot (fluxDef x) (u.grad x)
  let bridge : Vec d → ℝ :=
    fun x => vecDot (fluxDef x) (u x • scalarCutoffGradientField φ x)
  have hprod_split :
      (fun x => vecDot (fluxDef x) (uφ.grad x)) =
        fun x => first x + bridge x := by
    funext x
    have huφ_grad :
        uφ.grad x = φ x • u.grad x + u x • scalarCutoffGradientField φ x := by
      ext i
      simp [uφ, scalarCutoffGradientField, Pi.smul_apply, smul_eq_mul]
    calc
      vecDot (fluxDef x) (uφ.grad x)
          = vecDot (fluxDef x)
              (φ x • u.grad x + u x • scalarCutoffGradientField φ x) := by
                rw [huφ_grad]
      _ = vecDot (fluxDef x) (φ x • u.grad x) +
            vecDot (fluxDef x) (u x • scalarCutoffGradientField φ x) := by
                rw [vecDot_add_right]
      _ = φ x * vecDot (fluxDef x) (u.grad x) +
            vecDot (fluxDef x) (u x • scalarCutoffGradientField φ x) := by
                rw [vecDot_smul_right]
      _ = first x + bridge x := rfl
  have hfirst_int :
      MeasureTheory.IntegrableOn first U := by
    have hdiff_int :
        MeasureTheory.IntegrableOn
          (fun x => vecDot (fluxDef x) (uφ.grad x) - bridge x) U := by
      simpa [MeasureTheory.IntegrableOn] using!
        hprod_int.integrable.sub hpair_int.integrable
    have hfirst_eq :
        first = fun x => vecDot (fluxDef x) (uφ.grad x) - bridge x := by
      funext x
      have hx := congrFun hprod_split x
      linarith
    simpa [hfirst_eq] using hdiff_int
  have hsum_zero :
      ∫ x in U, (first x + bridge x) ∂MeasureTheory.volume = 0 := by
    calc
      ∫ x in U, (first x + bridge x) ∂MeasureTheory.volume =
          ∫ x in U, vecDot (fluxDef x) (uφ.grad x) ∂MeasureTheory.volume := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x => (congrFun hprod_split x).symm
      _ = 0 := hsol_uφ
  have hsum_zero' :
      ∫ x in U, first x ∂MeasureTheory.volume +
        ∫ x in U, bridge x ∂MeasureTheory.volume = 0 := by
    calc
      ∫ x in U, first x ∂MeasureTheory.volume +
          ∫ x in U, bridge x ∂MeasureTheory.volume =
        ∫ x in U, (first x + bridge x) ∂MeasureTheory.volume := by
          symm
          rw [MeasureTheory.integral_add hfirst_int hpair_int]
      _ = 0 := hsum_zero
  have hfirst_setIntegral :
      ∫ x in U, first x ∂MeasureTheory.volume =
        -∫ x in U, bridge x ∂MeasureTheory.volume := by
    linarith
  have hfirst_avg : cubeAverage Q first = -cubeAverage Q bridge := by
    calc
      cubeAverage Q first =
          (cubeVolume Q)⁻¹ *
            ∫ x in cubeSet Q, first x ∂MeasureTheory.volume := rfl
      _ = (cubeVolume Q)⁻¹ *
            ∫ x in U, first x ∂MeasureTheory.volume := by
            rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet (Q := Q) (f := first)]
            simp [U, Ch02.cubeDomain_coe]
      _ = (cubeVolume Q)⁻¹ *
            (-∫ x in U, bridge x ∂MeasureTheory.volume) := by
            rw [hfirst_setIntegral]
      _ = -((cubeVolume Q)⁻¹ *
            ∫ x in U, bridge x ∂MeasureTheory.volume) := by
            ring
      _ = -((cubeVolume Q)⁻¹ *
            ∫ x in cubeSet Q, bridge x ∂MeasureTheory.volume) := by
            rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet (Q := Q) (f := bridge)]
            simp [U, Ch02.cubeDomain_coe]
      _ = -cubeAverage Q bridge := rfl
  have hproduct_as_first :
      cutoffProductTermOnCube Q a φ p q p0 q0 =
        (1 / 2 : ℝ) * cubeAverage Q first := by
    calc
      cutoffProductTermOnCube Q a φ p q p0 q0 =
          cubeAverage Q (fun x => (1 / 2 : ℝ) * first x) := by
          unfold cutoffProductTermOnCube centeredProductDensityOnCube
          apply congrArg
          funext x
          simp [first, fluxDef, flux, u, v,
            canonicalMaximizerFluxOnCube, canonicalMaximizerGradientOnCube,
            canonicalMaximizerPotentialDefectH1OnCube_grad, vecDot_comm]
          ring
      _ = (1 / 2 : ℝ) * cubeAverage Q first := by
          rw [cubeAverage_const_mul]
  have hbridge_as_goal :
      bridge =
        fun x =>
          vecDot (canonicalMaximizerFluxDefectOnCube Q a p q q0 x)
            (canonicalMaximizerPotentialDefectOnCube Q a p q p0 x •
              scalarCutoffGradientField φ x) := by
    funext x
    simp [bridge, fluxDef, flux, u, v, canonicalMaximizerFluxDefectOnCube,
      canonicalMaximizerFluxOnCube, canonicalMaximizerGradientOnCube]
  calc
    cutoffProductTermOnCube Q a φ p q p0 q0 =
        (1 / 2 : ℝ) * cubeAverage Q first := hproduct_as_first
    _ = -(1 / 2 : ℝ) * cubeAverage Q bridge := by
        rw [hfirst_avg]
        ring
    _ =
        -(1 / 2 : ℝ) *
          cubeAverage Q
            (fun x =>
              vecDot (canonicalMaximizerFluxDefectOnCube Q a p q q0 x)
                (canonicalMaximizerPotentialDefectOnCube Q a p q p0 x •
                  scalarCutoffGradientField φ x)) := by
        rw [hbridge_as_goal]

theorem cubeAverage_vecDot_canonicalMaximizerFluxDefect_const_smul_scalarCutoffGradientField_eq_zero
    {d : ℕ} (Q : TriadicCube d)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) {φ : Vec d → ℝ}
    (p q q0 : Vec d) (c : ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet Q) :
    cubeAverage Q
        (fun x =>
          vecDot (canonicalMaximizerFluxDefectOnCube Q a p q q0 x)
            (c • scalarCutoffGradientField φ x)) = 0 := by
  classical
  let U : Set (Vec d) := ((Ch02.cubeDomain Q : Ch02.Domain d) : Set (Vec d))
  let v : Ch02.Solution (Ch02.cubeDomain Q) a :=
    canonicalMaximizerSolutionOnCube Q a p q
  let flux : Vec d → Vec d :=
    fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x)
  let fluxDef : Vec d → Vec d := fun x => flux x - q0
  let u : H1Function U := H1Function.const (U := U) c
  have hφ_sub_U : tsupport φ ⊆ U := by
    simpa [U, Ch02.cubeDomain_coe] using hφ_sub
  let ψ : H10Function U :=
    u.mulContDiffHasCompactSupportToH10
      (Ch02.cubeDomain Q).isDomain hφ hφ_compact hφ_sub_U
  have hflux_mem : MemVectorL2 U flux := by
    simpa [U, flux, v, canonicalMaximizerSolutionOnCube] using
      Ch02.Solution.flux_memVectorL2 (canonicalMaximizerSolutionOnCube Q a p q)
  have hdrop_const :
      ∫ x in U, vecDot (fluxDef x) (ψ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, vecDot (flux x) (ψ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
    simpa [fluxDef, ψ] using
      integral_vecDot_sub_const_zeroTraceGrad_eq (U := U) hflux_mem ψ q0
  have hsol :
      ∫ x in U, vecDot (fluxDef x) (ψ.toH1Function.grad x)
          ∂MeasureTheory.volume = 0 := by
    calc
      ∫ x in U, vecDot (fluxDef x) (ψ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, vecDot (flux x) (ψ.toH1Function.grad x)
          ∂MeasureTheory.volume := hdrop_const
      _ = 0 := by
        simpa [U, flux, v, canonicalMaximizerSolutionOnCube] using
          (canonicalMaximizerSolutionOnCube Q a p q).isHarmonic.2 ψ
  have hgrad_ae :
      (fun x => ψ.toH1Function.grad x) =ᵐ[MeasureTheory.volume.restrict U]
        fun x => c • scalarCutoffGradientField φ x := by
    have h :=
      WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
        u (Ch02.cubeDomain Q).isDomain hφ hφ_compact hφ_sub_U
    filter_upwards [h] with x hx
    ext i
    have hxi := congrFun hx i
    simpa [u, scalarCutoffGradientField, Pi.smul_apply, smul_eq_mul] using hxi
  have htarget :
      ∫ x in U,
          vecDot (canonicalMaximizerFluxDefectOnCube Q a p q q0 x)
            (c • scalarCutoffGradientField φ x) ∂MeasureTheory.volume = 0 := by
    calc
      ∫ x in U,
          vecDot (canonicalMaximizerFluxDefectOnCube Q a p q q0 x)
            (c • scalarCutoffGradientField φ x) ∂MeasureTheory.volume =
        ∫ x in U, vecDot (fluxDef x) (ψ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hgrad_ae] with x hx
          simp [canonicalMaximizerFluxDefectOnCube, fluxDef, flux, v,
            canonicalMaximizerFluxOnCube, canonicalMaximizerGradientOnCube, hx]
      _ = 0 := hsol
  rw [cubeAverage_eq_integralAverage_openCubeSet Q]
  unfold integralAverage
  have htarget_open :
      ∫ x in openCubeSet Q,
          vecDot (canonicalMaximizerFluxDefectOnCube Q a p q q0 x)
            (c • scalarCutoffGradientField φ x) ∂MeasureTheory.volume = 0 := by
    simpa [U, Ch02.cubeDomain_coe] using htarget
  rw [htarget_open]
  ring

theorem cutoffProductTermOnCube_eq_neg_half_cubeAverage_fluxDefect_centeredPotentialDefect_smul_scalarCutoffGradientField
    {d : ℕ} (Q : TriadicCube d)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) {φ : Vec d → ℝ}
    (p q p0 q0 : Vec d)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet Q)
    (hcutoffGradient :
      MemLp (scalarCutoffGradientField φ) ∞ (normalizedCubeMeasure Q)) :
    cutoffProductTermOnCube Q a φ p q p0 q0 =
      -(1 / 2 : ℝ) *
        cubeAverage Q
          (fun x =>
            vecDot (canonicalMaximizerFluxDefectOnCube Q a p q q0 x)
              (((canonicalMaximizerPotentialDefectOnCube Q a p q p0 x -
                    cubeAverage Q (canonicalMaximizerPotentialDefectOnCube Q a p q p0)) •
                  scalarCutoffGradientField φ x : Vec d))) := by
  classical
  let flux : Vec d → Vec d := canonicalMaximizerFluxDefectOnCube Q a p q q0
  let u : Vec d → ℝ := canonicalMaximizerPotentialDefectOnCube Q a p q p0
  let ξ : Vec d → Vec d := scalarCutoffGradientField φ
  let c : ℝ := cubeAverage Q u
  have hbase :=
    cutoffProductTermOnCube_eq_neg_half_cubeAverage_fluxDefect_potentialDefect_smul_scalarCutoffGradientField
      (Q := Q) (a := a) (φ := φ) p q p0 q0 hφ hφ_compact hφ_sub
  have hconst_zero :
      cubeAverage Q (fun x => vecDot (flux x) (c • ξ x)) = 0 := by
    simpa [flux, ξ, c] using
      cubeAverage_vecDot_canonicalMaximizerFluxDefect_const_smul_scalarCutoffGradientField_eq_zero
        Q a p q q0 c hφ hφ_compact hφ_sub
  have hflux_mem :
      MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [flux] using canonicalMaximizerFluxDefectOnCube_memLp Q a p q q0
  have hu_mem :
      MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [u] using canonicalMaximizerPotentialDefectOnCube_memLp Q a p q p0
  have hfluct :
      MemLp (fun x => u x - c) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hu_mem.sub (MeasureTheory.memLp_const c)
  have hprod_fluct :
      MemLp (fun x => (u x - c) • ξ x) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
    simpa [ξ] using! hcutoffGradient.smul
      (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hfluct
  have hprod_const :
      MemLp (fun x => c • ξ x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
    have hc : MemLp (fun _ : Vec d => c) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
      MeasureTheory.memLp_const c
    simpa [ξ] using! hcutoffGradient.smul
      (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hc
  have hdot_fluct :
      Integrable
        (fun x => vecDot (flux x) ((u x - c) • ξ x))
        (normalizedCubeMeasure Q) := by
    rw [show (fun x => vecDot (flux x) ((u x - c) • ξ x)) =
        fun x => ∑ i : Fin d, flux x i * ((u x - c) • ξ x) i by
          funext x
          simp [vecDot]]
    exact MeasureTheory.integrable_finsetSum _ fun i _ =>
      (memLp_component_of_memLp flux i hflux_mem).integrable_mul
        (memLp_component_of_memLp (fun x => (u x - c) • ξ x) i hprod_fluct)
  have hdot_const :
      Integrable
        (fun x => vecDot (flux x) (c • ξ x))
        (normalizedCubeMeasure Q) := by
    rw [show (fun x => vecDot (flux x) (c • ξ x)) =
        fun x => ∑ i : Fin d, flux x i * (c • ξ x) i by
          funext x
          simp [vecDot]]
    exact MeasureTheory.integrable_finsetSum _ fun i _ =>
      (memLp_component_of_memLp flux i hflux_mem).integrable_mul
        (memLp_component_of_memLp (fun x => c • ξ x) i hprod_const)
  have havg :
      cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x)) =
        cubeAverage Q (fun x => vecDot (flux x) ((u x - c) • ξ x)) := by
    have hpoint :
        (fun x => vecDot (flux x) (u x • ξ x)) =
          fun x =>
            vecDot (flux x) ((u x - c) • ξ x) +
              vecDot (flux x) (c • ξ x) := by
      funext x
      calc
        vecDot (flux x) (u x • ξ x)
            = vecDot (flux x) (((u x - c) • ξ x) + (c • ξ x)) := by
                congr 1
                ext i
                simp [Pi.smul_apply, smul_eq_mul]
                ring
        _ =
            vecDot (flux x) ((u x - c) • ξ x) +
              vecDot (flux x) (c • ξ x) := by
                rw [vecDot_add_right]
    rw [hpoint, cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    have hconst_zero_int :
        ∫ x, vecDot (flux x) (c • ξ x) ∂ normalizedCubeMeasure Q = 0 := by
      rw [← cubeAverage_eq_integral_normalizedCubeMeasure Q
        (fun x => vecDot (flux x) (c • ξ x))]
      exact hconst_zero
    rw [MeasureTheory.integral_add hdot_fluct hdot_const]
    rw [hconst_zero_int]
    ring
  calc
    cutoffProductTermOnCube Q a φ p q p0 q0
        =
      -(1 / 2 : ℝ) *
        cubeAverage Q
          (fun x =>
            vecDot (flux x) (u x • ξ x)) := by
          simpa [flux, u, ξ] using hbase
    _ =
      -(1 / 2 : ℝ) *
        cubeAverage Q
          (fun x =>
            vecDot (flux x) ((u x - c) • ξ x)) := by
          rw [havg]
    _ =
      -(1 / 2 : ℝ) *
        cubeAverage Q
          (fun x =>
            vecDot (canonicalMaximizerFluxDefectOnCube Q a p q q0 x)
              (((canonicalMaximizerPotentialDefectOnCube Q a p q p0 x -
                    cubeAverage Q (canonicalMaximizerPotentialDefectOnCube Q a p q p0)) •
                  scalarCutoffGradientField φ x : Vec d))) := by
          simp [flux, u, ξ, c]

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
