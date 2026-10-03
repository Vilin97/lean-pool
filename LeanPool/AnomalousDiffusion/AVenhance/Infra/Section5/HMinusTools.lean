/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.HMinusOneNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOne
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodicCore
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Tools for the extended-valued homogeneous negative norm. The
mean-zero bridge retains the distinction between all periodic tests and the
centred tests used in Ergodic. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance
open AVenhance.Infra.Ergodic
namespace AVenhance.Infra.Section5

local instance avInfraSection5HMinusToolsIsFiniteMeasure1 : IsFiniteMeasure (volume.restrict
    unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  unfold unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

theorem HMinusTools.cell_average_frozen (f : Vec 2 → ℝ) :
    cellAverage f = ∫ x in unitCube, f x := by
  rw [cellAverage_eq_unitCellIntegral]
  rw [unitCellSet_eq_torusUnitCell]
  exact Infra.Torus.integral_unitCell_eq_unitCube f

theorem HMinusTools.continuous_memL2 {f : Vec 2 → ℝ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict unitCube) := by
  have h := continuous_unitCell_memLp_two hf
  rw [Measure.restrict_congr_set Infra.Torus.unitCell_ae_eq_unitCube] at h
  simpa using h

theorem HMinusTools.gradient_average (φ : Vec 2 → ℝ) :
    gradientL2SquaredAverage φ = gradNormSq (spaceGrad φ) := by
  rw [gradientL2SquaredAverage, HMinusTools.cell_average_frozen]
  simp [gradNormSq, spaceGrad, vecNormSq, vecDot, basisVec, pow_two]

theorem HMinusTools.pair_integrable {g φ : Vec 2 → ℝ}
    (hg : MemLp g 2 (volume.restrict unitCube)) (hφ : Continuous φ) :
    IntegrableOn (fun x => g x * φ x) unitCube := by
  exact (hg.mul (HMinusTools.continuous_memL2 hφ) : MemLp (fun x => g x * φ x) 1
    (volume.restrict unitCube)).integrable le_rfl

/-- The App C analytic, centred test norm is bounded by the smooth-test
norm. The reverse inequality would need a density argument; it is not assumed. -/
theorem ergodic_hMinusOneNorm_le_frozen (g : Vec 2 → ℝ) :
    homogeneousHMinusOneNorm g ≤ hMinusOneNorm g := by
  apply iSup_le
  intro φ
  let test : {φ : Vec 2 → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ IsZ2Periodic φ ∧
    gradNormSq (spaceGrad φ) ≤ 1} := ⟨φ.val, φ.property.1, by
      intro k x
      exact φ.property.2.1 x k, by
      rw [← HMinusTools.gradient_average]
      exact φ.property.2.2.2⟩
  rw [HMinusTools.cell_average_frozen]
  exact le_iSup (fun ψ => ENNReal.ofReal |∫ x in unitCube, g x * ψ.val x|) test

/-- Poincare duality in the carriers, with its sharp torus constant. -/
theorem hMinusOneNorm_le_L2 {g : Vec 2 → ℝ}
    (hg : MemL2On unitCube g) (hm : MeanZeroOn unitCube g) :
    hMinusOneNorm g ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.sqrt (l2NormSq g)) := by
  apply iSup_le
  intro φ
  let c : ℝ := cellAverage φ.val
  let ψ : Vec 2 → ℝ := fun x => φ.val x - c
  have hs : ContDiff ℝ (⊤ : ℕ∞) ψ := φ.property.1.sub contDiff_const
  have hp : IsZ2Periodic ψ := by
    intro k x
    exact congrArg (fun y => y - c) (φ.property.2.1 k x)
  have hgrad : spaceGrad ψ = spaceGrad φ.val := by
    funext x i
    simp [spaceGrad, ψ, fderiv_sub_const]
  have hmean : ∫ x in unitCube, ψ x = 0 := by
    have hi := (HMinusTools.continuous_memL2 φ.property.1.continuous).integrable (by norm_num : (1
        : ENNReal) ≤ 2)
    have hc := (HMinusTools.continuous_memL2 (continuous_const : Continuous (fun _ : Vec 2 =>
        c))).integrable (by norm_num : (1 : ENNReal) ≤ 2)
    rw [show ψ = fun x => φ.val x - c from rfl, integral_sub hi hc]
    rw [← HMinusTools.cell_average_frozen, ← HMinusTools.cell_average_frozen]
    simp [c]
  have hpair : (∫ x in unitCube, g x * φ.val x) = ∫ x in unitCube, g x * ψ x := by
    simp only [ψ, mul_sub]
    rw [integral_sub (HMinusTools.pair_integrable hg φ.property.1.continuous)
      ((hg.mul_const c).integrable (by norm_num : (1 : ENNReal) ≤ 2)), integral_mul_const, hm]
    simp
  have hP := Infra.Torus.l2NormSq_le_fourierPoincare
    (hs.of_le (by simp)) hp hmean
  rw [hgrad] at hP
  have hψ : l2NormSq ψ ≤ (4 * Real.pi ^ 2)⁻¹ :=
    hP.trans (by simpa using mul_le_mul_of_nonneg_left φ.property.2.2 (by positivity : 0 ≤ (4 *
        Real.pi ^ 2)⁻¹))
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (f := fun x => |g x|) (g := fun x => |ψ x|)
    (μ := volume.restrict unitCube)
    Real.HolderConjugate.two_two
    (ae_of_all _ (fun x => abs_nonneg _)) (ae_of_all _ (fun x => abs_nonneg _))
    (by simpa [Real.norm_eq_abs] using hg.norm)
    (by simpa [Real.norm_eq_abs] using (HMinusTools.continuous_memL2 hs.continuous).norm)
  have hc : Real.sqrt ((4 * Real.pi ^ 2)⁻¹) = (2 * Real.pi)⁻¹ := by
    rw [Real.sqrt_inv, show 4 * Real.pi ^ 2 = (2 * Real.pi) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  apply ENNReal.ofReal_le_ofReal
  rw [hpair]
  calc
    _ ≤ ∫ x in unitCube, |g x| * |ψ x| := by
      simpa [Real.norm_eq_abs, abs_mul] using norm_integral_le_integral_norm (fun x => g x * ψ x)
    _ ≤ Real.sqrt (l2NormSq g) * Real.sqrt (l2NormSq ψ) := by
      simpa only [Real.rpow_two, sq_abs, Real.sqrt_eq_rpow, one_div, l2NormSq] using hholder
    _ ≤ Real.sqrt (l2NormSq g) * (2 * Real.pi)⁻¹ := by
      rw [← hc]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hψ) (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

private theorem hMinusOneNorm_le_of_divergence_sumBound1 :
  ∀ {V : Fin (2 : ℕ) → Vec (2 : ℕ) → ℝ} (φ : { φ : Vec (2 : ℕ) → ℝ // ContDiff ℝ (↑(⊤ : ℕ∞) :
    WithTop ℕ∞) φ ∧ IsZ2Periodic φ ∧ gradNormSq (spaceGrad φ) ≤ (1 : ℝ) }),
  let ψ : Vec (2 : ℕ) → ℝ := (↑φ : Vec (2 : ℕ) → ℝ);
  let ψc : Vec (2 : ℕ) → ℂ := fun (x : Vec (2 : ℕ)) => (↑(ψ x) : ℂ);
  let Vc : Fin (2 : ℕ) → Vec (2 : ℕ) → ℂ := fun (i : Fin (2 : ℕ)) (x : Vec (2 : ℕ)) => (↑(V i x)
    : ℂ);
  ∫ (x : Vec (2 : ℕ)) in Torus.unitCell (2 : ℕ), ∑ i : Fin (2 : ℕ), ‖Torus.coordDeriv i ψc x‖ ^
    (2 : ℕ) ≤ (1 : ℝ) → (∀ (i : Fin (2 : ℕ)), IntegrableOn (fun (x : Vec (2 : ℕ)) => ‖Vc i x‖ ^
    (2 : ℕ)) (Torus.unitCell (2 : ℕ)) volume) → (∀ (i : Fin (2 : ℕ)), IntegrableOn (fun (x : Vec
    (2 : ℕ)) => ‖Torus.coordDeriv i ψc x‖ ^ (2 : ℕ)) (Torus.unitCell (2 : ℕ)) volume) → ∑ i :
    Fin (2 : ℕ), (∫ (x : Vec (2 : ℕ)) in Torus.unitCell (2 : ℕ), ‖Vc i x‖ ^ (2 : ℕ)) ^ (1 / 2 :
    ℝ) * (∫ (x : Vec (2 : ℕ)) in Torus.unitCell (2 : ℕ), ‖Torus.coordDeriv i ψc x‖ ^ (2 : ℕ)) ^
    (1 / 2 : ℝ) ≤ √(∫ (x : Vec (2 : ℕ)) in Torus.unitCell (2 : ℕ), ∑ i : Fin (2 : ℕ), ‖Vc i x‖ ^
    (2 : ℕ))
    := by
  intro V φ ψ ψc Vc hgradIntegral hVintegrable hψderivIntegrable
  let A : Fin 2 → ℝ := fun i =>
    (∫ x in Infra.Torus.unitCell 2, ‖Vc i x‖ ^ 2) ^ (1 / 2 : ℝ)
  let B : Fin 2 → ℝ := fun i =>
    (∫ x in Infra.Torus.unitCell 2,
      ‖AVenhance.Infra.Torus.coordDeriv i ψc x‖ ^ 2) ^ (1 / 2 : ℝ)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 2)) A B
  have hA :
      (∑ i : Fin 2, A i ^ 2) =
        ∫ x in Infra.Torus.unitCell 2, ∑ i : Fin 2, ‖Vc i x‖ ^ 2 := by
    calc
      _ = ∑ i : Fin 2,
          ∫ x in Infra.Torus.unitCell 2, ‖Vc i x‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            dsimp [A]
            rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
            exact integral_nonneg (fun x => sq_nonneg (‖Vc i x‖))
      _ = _ := by
            have hsum := MeasureTheory.integral_finsetSum
              (Finset.univ : Finset (Fin 2))
              (μ := (volume : Measure (Homogenization.Vec 2)).restrict
                (Infra.Torus.unitCell 2))
              (f := fun i x => ‖Vc i x‖ ^ 2)
              (fun i _hi => (hVintegrable i).integrable)
            simpa using hsum.symm
  have hBnonneg :
      ∀ i : Fin 2, 0 ≤
        ∫ x in Infra.Torus.unitCell 2,
          ‖AVenhance.Infra.Torus.coordDeriv i ψc x‖ ^ 2 := by
    intro i
    exact integral_nonneg (fun x => sq_nonneg
      (‖AVenhance.Infra.Torus.coordDeriv i ψc x‖))
  have hB : (∑ i : Fin 2, B i ^ 2) ≤ 1 := by
    calc
      _ = ∫ x in Infra.Torus.unitCell 2,
          ∑ i : Fin 2,
            ‖AVenhance.Infra.Torus.coordDeriv i ψc x‖ ^ 2 := by
            calc
              _ = ∑ i : Fin 2,
                  ∫ x in Infra.Torus.unitCell 2,
                    ‖AVenhance.Infra.Torus.coordDeriv i ψc x‖ ^ 2 := by
                apply Finset.sum_congr rfl
                intro i hi
                dsimp [B]
                rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
                exact hBnonneg i
              _ = _ := by
                have hsum := MeasureTheory.integral_finsetSum
                  (Finset.univ : Finset (Fin 2))
                  (μ := (volume : Measure (Homogenization.Vec 2)).restrict
                    (Infra.Torus.unitCell 2))
                  (f := fun i x =>
                    ‖AVenhance.Infra.Torus.coordDeriv i ψc x‖ ^ 2)
                  (fun i _hi => (hψderivIntegrable i).integrable)
                simpa using hsum.symm
      _ ≤ 1 := hgradIntegral
  have hAroot : 0 ≤
      Real.sqrt (∫ x in Infra.Torus.unitCell 2,
        ∑ i : Fin 2, ‖Vc i x‖ ^ 2) := by positivity
  have hBroot : Real.sqrt (∑ i : Fin 2, B i ^ 2) ≤ 1 := by
    exact (Real.sqrt_le_one).mpr hB
  calc
    _ = ∑ i : Fin 2, A i * B i := by
      apply Finset.sum_congr rfl
      intro i hi
      rfl
    _ ≤ Real.sqrt (∑ i : Fin 2, A i ^ 2) *
        Real.sqrt (∑ i : Fin 2, B i ^ 2) := by
      simpa using hcs
    _ = Real.sqrt (∫ x in Infra.Torus.unitCell 2,
        ∑ i : Fin 2, ‖Vc i x‖ ^ 2) *
        Real.sqrt (∑ i : Fin 2, B i ^ 2) := by rw [hA]
    _ ≤ Real.sqrt (∫ x in Infra.Torus.unitCell 2,
        ∑ i : Fin 2, ‖Vc i x‖ ^ 2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hBroot hAroot

private theorem hMinusOneNorm_le_of_divergence_pairComplex2 :
  ∀ {h : Vec (2 : ℕ) → ℝ} {V : Fin (2 : ℕ) → Vec (2 : ℕ) → ℝ} (φ : { φ : Vec (2 : ℕ) → ℝ //
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ IsZ2Periodic φ ∧ gradNormSq (spaceGrad φ) ≤ (1 : ℝ)
    }),
  let ψ : Vec (2 : ℕ) → ℝ := (↑φ : Vec (2 : ℕ) → ℝ);
  let ψc : Vec (2 : ℕ) → ℂ := fun (x : Vec (2 : ℕ)) => (↑(ψ x) : ℂ);
  let Vc : Fin (2 : ℕ) → Vec (2 : ℕ) → ℂ := fun (i : Fin (2 : ℕ)) (x : Vec (2 : ℕ)) => (↑(V i x)
    : ℂ);
  ContDiff ℝ (1 : WithTop ℕ∞) ψc → (∀ (i : Fin (2 : ℕ)), ContDiff ℝ (1 : WithTop ℕ∞) (Vc i)) →
    (∀ (x : Vec (2 : ℕ)), (↑(h x) : ℂ) = ∑ i : Fin (2 : ℕ), Torus.coordDeriv i (Vc i) x) → (∀ (i
    : Fin (2 : ℕ)), ∫ (x : Vec (2 : ℕ)) in Torus.unitCell (2 : ℕ), Torus.coordDeriv i (Vc i) x *
    ψc x = -∫ (x : Vec (2 : ℕ)) in Torus.unitCell (2 : ℕ), Vc i x * Torus.coordDeriv i ψc x) → ∫
    (x : Vec (2 : ℕ)) in Torus.unitCell (2 : ℕ), (↑(h x) : ℂ) * ψc x = -∑ i : Fin (2 : ℕ), ∫ (x
    : Vec (2 : ℕ)) in Torus.unitCell (2 : ℕ), Vc i x * Torus.coordDeriv i ψc x
    := by
  intro h V φ ψ ψc Vc hψcDiff hVdiffC hdivC hIBP
  calc
    _ = ∫ x in Infra.Torus.unitCell 2,
        (∑ i : Fin 2,
          AVenhance.Infra.Torus.coordDeriv i (Vc i) x) * ψc x := by
        apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
        intro x hx
        change (h x : ℂ) * ψc x = _
        rw [hdivC x]
    _ = ∑ i : Fin 2,
        ∫ x in Infra.Torus.unitCell 2,
          AVenhance.Infra.Torus.coordDeriv i (Vc i) x * ψc x := by
        have hsumPoint (x : Homogenization.Vec 2) :
            (∑ i : Fin 2,
              AVenhance.Infra.Torus.coordDeriv i (Vc i) x) * ψc x =
              ∑ i : Fin 2,
                AVenhance.Infra.Torus.coordDeriv i (Vc i) x * ψc x := by
          rw [Finset.sum_mul]
        have hsum := MeasureTheory.integral_finsetSum
          (Finset.univ : Finset (Fin 2))
          (μ := (volume : Measure (Homogenization.Vec 2)).restrict
            (Infra.Torus.unitCell 2))
          (f := fun i x => AVenhance.Infra.Torus.coordDeriv i (Vc i) x * ψc x)
          (fun i _hi => continuous_complex_unitCell_integrable
            ((AVenhance.Infra.Torus.continuous_coordDeriv i (hVdiffC i)).mul
              hψcDiff.continuous))
        rw [show (fun x =>
            (∑ i : Fin 2,
              AVenhance.Infra.Torus.coordDeriv i (Vc i) x) * ψc x) =
            fun x => ∑ i : Fin 2,
              AVenhance.Infra.Torus.coordDeriv i (Vc i) x * ψc x by
              funext x
              exact hsumPoint x]
        simpa using hsum
    _ = -∑ i : Fin 2,
        ∫ x in Infra.Torus.unitCell 2,
          Vc i x * AVenhance.Infra.Torus.coordDeriv i ψc x := by
        symm
        calc
          -∑ i : Fin 2,
              ∫ x in Infra.Torus.unitCell 2,
                Vc i x * AVenhance.Infra.Torus.coordDeriv i ψc x
              = ∑ i : Fin 2,
                  -(∫ x in Infra.Torus.unitCell 2,
                    Vc i x * AVenhance.Infra.Torus.coordDeriv i ψc x) := by
                  rw [Finset.sum_neg_distrib]
          _ = _ := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact (hIBP i).symm

/-- Divergence duality for the C-infinity test class. This transfers
the integration-by-parts proof underlying the analytic-test estimate,
rather than asserting an unproved equality of the two test suprema. -/
theorem hMinusOneNorm_le_of_divergence {h : Vec 2 → ℝ} {V : Fin 2 → Vec 2 → ℝ}
    (hVdiff : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (V i))
    (hVper : ∀ i, IsZPeriodic (V i))
    (hdiv : ∀ x, h x = ∑ i, fderiv ℝ (V i) x (basisVec i)) :
    hMinusOneNorm h ≤ ENNReal.ofReal (Real.sqrt (vectorFieldL2SquaredAverage V)) := by
  classical
  apply iSup_le
  intro φ
  let ψ := φ.val
  have hψsmooth : ContDiff ℝ 1 ψ := φ.property.1.of_le (by simp)
  have hψper : Infra.Torus.IsZdPeriodic (fun x => (ψ x : ℂ)) := by
    intro k x
    exact congrArg Complex.ofReal (φ.property.2.1 k x)
  let ψc : Homogenization.Vec 2 → ℂ := fun x => ψ x
  let Vc : Fin 2 → Homogenization.Vec 2 → ℂ :=
    fun i x => V i x
  have hψcDiff : ContDiff ℝ 1 ψc := by
    exact Complex.ofRealCLM.contDiff.comp hψsmooth
  have hψcPer : Infra.Torus.IsZdPeriodic ψc := hψper
  have hVdiffC (i : Fin 2) : ContDiff ℝ 1 (Vc i) := by
    exact Complex.ofRealCLM.contDiff.comp ((hVdiff i).of_le (by simp))
  have hVperC (i : Fin 2) : Infra.Torus.IsZdPeriodic (Vc i) := by
    intro k x
    exact congrArg Complex.ofReal (hVper i x k)
  have hdivC (x : Homogenization.Vec 2) :
      (h x : ℂ) = ∑ i : Fin 2,
        AVenhance.Infra.Torus.coordDeriv i (Vc i) x := by
    calc
      (h x : ℂ) = Complex.ofReal
          (∑ i : Fin 2,
            fderiv ℝ (V i) x (Homogenization.basisVec i)) := by rw [hdiv x]
      _ = ∑ i : Fin 2,
          (fderiv ℝ (V i) x (Homogenization.basisVec i) : ℂ) := by simp
      _ = ∑ i : Fin 2, AVenhance.Infra.Torus.coordDeriv i (Vc i) x := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [coordDeriv_realCast_ergodic ((hVdiff i).of_le (by simp)) i x]
  have hgradIntegral :
      (∫ x in Infra.Torus.unitCell 2,
        ∑ i : Fin 2,
          ‖AVenhance.Infra.Torus.coordDeriv i ψc x‖ ^ 2) ≤ 1 := by
    have heq :
        (∫ x in Infra.Torus.unitCell 2,
          ∑ i : Fin 2,
            ‖AVenhance.Infra.Torus.coordDeriv i ψc x‖ ^ 2) =
          gradientL2SquaredAverage ψ := by
      unfold gradientL2SquaredAverage
      rw [cellAverage_eq_unitCellIntegral, unitCellSet_eq_torusUnitCell]
      apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
      intro x hx
      apply Finset.sum_congr rfl
      intro i hi
      rw [coordDeriv_realCast_ergodic hψsmooth i x]
      simp [Homogenization.basisVec]
    rw [heq]
    rw [HMinusTools.gradient_average]
    exact φ.property.2.2
  have hVintegrable (i : Fin 2) :
      IntegrableOn (fun x => ‖Vc i x‖ ^ 2) (Infra.Torus.unitCell 2) :=
    continuous_unitCell_integrable ((hVdiffC i).continuous.norm.pow 2)
  have hψderivIntegrable (i : Fin 2) :
      IntegrableOn
        (fun x => ‖AVenhance.Infra.Torus.coordDeriv i ψc x‖ ^ 2)
        (Infra.Torus.unitCell 2) :=
    continuous_unitCell_integrable
      ((AVenhance.Infra.Torus.continuous_coordDeriv i hψcDiff).norm.pow 2)
  have hIBP (i : Fin 2) :
      (∫ x in Infra.Torus.unitCell 2,
        AVenhance.Infra.Torus.coordDeriv i (Vc i) x * ψc x) =
      -(∫ x in Infra.Torus.unitCell 2,
        Vc i x * AVenhance.Infra.Torus.coordDeriv i ψc x) := by
    have h := AVenhance.Infra.Torus.integral_unitCell_coord_ibp i
      hψcDiff (hVdiffC i) hψcPer (hVperC i)
    calc
      _ = ∫ x in Infra.Torus.unitCell 2,
          ψc x * AVenhance.Infra.Torus.coordDeriv i (Vc i) x := by
            apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
            intro x hx
            ring
      _ = -(∫ x in Infra.Torus.unitCell 2,
          AVenhance.Infra.Torus.coordDeriv i ψc x * Vc i x) := h
      _ = _ := by
            congr 2
            funext x
            ring
  have hpairComplex :
      (∫ x in Infra.Torus.unitCell 2, (h x : ℂ) * ψc x) =
        -∑ i : Fin 2,
          ∫ x in Infra.Torus.unitCell 2,
            Vc i x * AVenhance.Infra.Torus.coordDeriv i ψc x := by
    exact @hMinusOneNorm_le_of_divergence_pairComplex2 h V φ hψcDiff hVdiffC hdivC hIBP
  have hpairCell :
      cellAverage (fun x => h x * ψ x) =
        ∫ x in Infra.Torus.unitCell 2, h x * ψ x := by
    rw [cellAverage_eq_unitCellIntegral, unitCellSet_eq_torusUnitCell]
  have hpairRealToComplex :
      Complex.ofReal (cellAverage (fun x => h x * ψ x)) =
        ∫ x in Infra.Torus.unitCell 2, (h x : ℂ) * ψc x := by
    rw [hpairCell]
    have hint : IntegrableOn (fun x => h x * ψ x) (Infra.Torus.unitCell 2) := by
      -- The divergence identity and smoothness of `V` make `h` continuous.
      have hcont : Continuous h := by
        have hsum : Continuous (fun x => ∑ i : Fin 2,
            fderiv ℝ (V i) x (Homogenization.basisVec i)) := by
          apply continuous_finsetSum
          intro i hi
          exact ((hVdiff i).continuous_fderiv (by simp)).clm_apply continuous_const
        have heq : h = fun x => ∑ i : Fin 2,
            fderiv ℝ (V i) x (Homogenization.basisVec i) := by
          funext x
          exact hdiv x
        rw [heq]
        exact hsum
      exact continuous_unitCell_integrable (hcont.mul hψsmooth.continuous)
    have hmap := Complex.ofRealCLM.integral_comp_comm
      (μ := (volume : Measure (Homogenization.Vec 2)).restrict
        (Infra.Torus.unitCell 2)) hint
    simpa [ψc, Complex.ofReal_mul] using hmap.symm
  have hcomponent (i : Fin 2) :
      ‖∫ x in Infra.Torus.unitCell 2,
        Vc i x * AVenhance.Infra.Torus.coordDeriv i ψc x‖ ≤
      (∫ x in Infra.Torus.unitCell 2, ‖Vc i x‖ ^ 2) ^ (1 / 2 : ℝ) *
      (∫ x in Infra.Torus.unitCell 2,
        ‖AVenhance.Infra.Torus.coordDeriv i ψc x‖ ^ 2) ^ (1 / 2 : ℝ) := by
    have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
      (f := fun x => ‖Vc i x‖)
      (g := fun x => ‖AVenhance.Infra.Torus.coordDeriv i ψc x‖)
      (μ := (volume : Measure (Homogenization.Vec 2)).restrict
        (Infra.Torus.unitCell 2)) Real.HolderConjugate.two_two
      (ae_of_all _ fun x => norm_nonneg _)
      (ae_of_all _ fun x => norm_nonneg _)
      (continuous_unitCell_memLp_two ((hVdiffC i).continuous.norm))
      (continuous_unitCell_memLp_two
        ((AVenhance.Infra.Torus.continuous_coordDeriv i hψcDiff).norm))
    calc
      _ ≤ ∫ x in Infra.Torus.unitCell 2,
          ‖Vc i x‖ * ‖AVenhance.Infra.Torus.coordDeriv i ψc x‖ := by
          calc
            _ = ‖∫ x in Infra.Torus.unitCell 2,
                Vc i x * AVenhance.Infra.Torus.coordDeriv i ψc x‖ := rfl
            _ ≤ ∫ x in Infra.Torus.unitCell 2,
                ‖Vc i x * AVenhance.Infra.Torus.coordDeriv i ψc x‖ :=
              norm_integral_le_integral_norm _
            _ = _ := by
              apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
              intro x hx
              exact norm_mul _ _
      _ ≤ _ := by simpa [Real.rpow_natCast] using hholder
  have hsumBound :
      ∑ i : Fin 2,
        (∫ x in Infra.Torus.unitCell 2, ‖Vc i x‖ ^ 2) ^ (1 / 2 : ℝ) *
        (∫ x in Infra.Torus.unitCell 2,
            ‖AVenhance.Infra.Torus.coordDeriv i ψc x‖ ^ 2) ^ (1 / 2 : ℝ) ≤
      Real.sqrt (∫ x in Infra.Torus.unitCell 2,
          ∑ i : Fin 2, ‖Vc i x‖ ^ 2) := by
    exact @hMinusOneNorm_le_of_divergence_sumBound1 V φ hgradIntegral hVintegrable hψderivIntegrable
  have hpairBound :
      |cellAverage (fun x => h x * ψ x)| ≤
        Real.sqrt (∫ x in Infra.Torus.unitCell 2,
          ∑ i : Fin 2, ‖Vc i x‖ ^ 2) := by
    calc
      |cellAverage (fun x => h x * ψ x)| =
          ‖(cellAverage (fun x => h x * ψ x) : ℂ)‖ := by simp
      _ = ‖∫ x in Infra.Torus.unitCell 2, (h x : ℂ) * ψc x‖ := by
          rw [hpairRealToComplex]
      _ = ‖∑ i : Fin 2,
          ∫ x in Infra.Torus.unitCell 2,
            Vc i x * AVenhance.Infra.Torus.coordDeriv i ψc x‖ := by
          rw [hpairComplex]
          rw [norm_neg]
      _ ≤ ∑ i : Fin 2,
          ‖∫ x in Infra.Torus.unitCell 2,
            Vc i x * AVenhance.Infra.Torus.coordDeriv i ψc x‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun i hi => hcomponent i
      _ ≤ _ := hsumBound
  have hVaverage : vectorFieldL2SquaredAverage V =
      ∫ x in Infra.Torus.unitCell 2,
        ∑ i : Fin 2, ‖Vc i x‖ ^ 2 := by
    unfold vectorFieldL2SquaredAverage
    rw [cellAverage_eq_unitCellIntegral, unitCellSet_eq_torusUnitCell]
    apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
    intro x hx
    simp [Vc]
  have hnonneg : 0 ≤ vectorFieldL2SquaredAverage V := by
    unfold vectorFieldL2SquaredAverage
    rw [cellAverage_eq_unitCellIntegral]
    apply integral_nonneg
    intro x
    exact Finset.sum_nonneg fun i hi => sq_nonneg _
  have hpairBound' :
      |cellAverage (fun x => h x * ψ x)| ≤
        Real.sqrt (vectorFieldL2SquaredAverage V) := by
    simpa [hVaverage] using hpairBound
  rw [HMinusTools.cell_average_frozen] at hpairBound'
  exact ENNReal.ofReal_le_ofReal hpairBound'

/-- Classical divergence written coordinatewise on the Vec carrier. -/
def cellDivergence (F : Vec 2 → Vec 2) (x : Vec 2) : ℝ :=
  ∑ i, fderiv ℝ (fun y => F y i) x (basisVec i)

/-- Vector-field form of divergence duality, with the Euclidean energy. -/
theorem hMinusOneNorm_divergence_le (F : Vec 2 → Vec 2)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : IsZ2Periodic F) :
    hMinusOneNorm (cellDivergence F) ≤ ENNReal.ofReal (Real.sqrt (gradNormSq F)) := by
  have hd (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => F x i) :=
    (contDiff_apply ℝ ℝ i).comp hF
  have hper (i : Fin 2) : IsZPeriodic (fun x => F x i) := by
    intro x k
    exact congrFun (hp k x) i
  have h := hMinusOneNorm_le_of_divergence hd hper (fun _ => rfl)
  have he : vectorFieldL2SquaredAverage (fun i x => F x i) = gradNormSq F := by
    rw [vectorFieldL2SquaredAverage, HMinusTools.cell_average_frozen]
    simp [gradNormSq, vecNormSq, vecDot, pow_two]
  rw [he] at h
  exact h

/-- Triangle inequality; L2 hypotheses justify addition of the dual integrals.
Means need not vanish: the extended norm retains infinite values. -/
theorem hMinusOneNorm_add_le {f g : Vec 2 → ℝ}
    (hf : MemL2On unitCube f) (hg : MemL2On unitCube g) :
    hMinusOneNorm (fun x => f x + g x) ≤ hMinusOneNorm f + hMinusOneNorm g := by
  apply iSup_le
  intro φ
  have h1 := HMinusTools.pair_integrable hf φ.property.1.continuous
  have h2 := HMinusTools.pair_integrable hg φ.property.1.continuous
  simp only [add_mul, integral_add h1 h2]
  calc
    _ ≤ ENNReal.ofReal (|∫ x in unitCube, f x * φ.val x| + |∫ x in unitCube, g x * φ.val x|) :=
      ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add (le_iSup (fun ψ => ENNReal.ofReal |∫ x in unitCube, f x * ψ.val x|) φ)
      (le_iSup (fun ψ => ENNReal.ofReal |∫ x in unitCube, g x * ψ.val x|) φ)

/-- Exact scaling, valid even for infinite negative norm. -/
theorem hMinusOneNorm_const_mul (a : ℝ) (g : Vec 2 → ℝ) :
    hMinusOneNorm (fun x => a * g x) = ENNReal.ofReal |a| * hMinusOneNorm g := by
  unfold hMinusOneNorm
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro φ
  simp only [mul_assoc, integral_const_mul, abs_mul]
  exact ENNReal.ofReal_mul (abs_nonneg _)

/-- Exactly the time-norm carrier occurring in the BigBound statement. -/
def timeHMinusOneNorm (f : ℝ → Vec 2 → ℝ) : ENNReal :=
  (∫⁻ t in Set.Ioo (0 : ℝ) 1, hMinusOneNorm (f t) ^ 2) ^ (1 / 2 : ℝ)

/-- Time-integrated Minkowski, with explicit measurability of the two norms. -/
theorem timeHMinusOneNorm_add_le {f g : ℝ → Vec 2 → ℝ}
    (hf : ∀ t ∈ Set.Ioo (0 : ℝ) 1, MemL2On unitCube (f t))
    (hg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, MemL2On unitCube (g t))
    (hmf : AEMeasurable (fun t => hMinusOneNorm (f t)) (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (hmg : AEMeasurable (fun t => hMinusOneNorm (g t)) (volume.restrict (Set.Ioo (0 : ℝ) 1))) :
    timeHMinusOneNorm (fun t x => f t x + g t x) ≤ timeHMinusOneNorm f + timeHMinusOneNorm g := by
  unfold timeHMinusOneNorm
  calc
    _ ≤ (∫⁻ t in Set.Ioo (0 : ℝ) 1,
      (hMinusOneNorm (f t) + hMinusOneNorm (g t)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      refine ENNReal.rpow_le_rpow ?_ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      simpa only [ENNReal.rpow_two] using pow_le_pow_left₀ bot_le (hMinusOneNorm_add_le (hf t ht)
          (hg t ht)) 2
    _ ≤ _ := by
      simpa only [Pi.add_apply, ENNReal.rpow_two] using ENNReal.lintegral_Lp_add_le hmf hmg (by
          norm_num : (1 : ℝ) ≤ 2)

/-- Pointwise bounds pass to the exact BigBound time norm. -/
theorem timeHMinusOneNorm_le_of_bound {f : ℝ → Vec 2 → ℝ} {B : ℝ → ENNReal}
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, hMinusOneNorm (f t) ≤ B t) :
    timeHMinusOneNorm f ≤ (∫⁻ t in Set.Ioo (0 : ℝ) 1, B t ^ 2) ^ (1 / 2 : ℝ) := by
  apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact pow_le_pow_left₀ bot_le (h t ht) 2

/-- Time-integrated L2-to-negative-norm estimate in carriers. -/
theorem timeHMinusOneNorm_le_L2 {f : ℝ → Vec 2 → ℝ}
    (hf : ∀ t ∈ Set.Ioo (0 : ℝ) 1, MemL2On unitCube (f t))
    (hm : ∀ t ∈ Set.Ioo (0 : ℝ) 1, MeanZeroOn unitCube (f t)) :
    timeHMinusOneNorm f ≤
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.sqrt (l2NormSq (f t))) ^ 2) ^ (1 / 2 : ℝ) :=
  timeHMinusOneNorm_le_of_bound (fun t ht => hMinusOneNorm_le_L2 (hf t ht) (hm t ht))

/-- The time primitive based at `0`, without a mean correction. -/
def periodicPrimitive (g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, g s

/-- The primitive is an actual antiderivative, not only a periodic integral. -/
theorem periodicPrimitive_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    HasDerivAt (periodicPrimitive g) (g t) t :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

/-- A mean-zero period integral makes the primitive periodic. -/
theorem periodicPrimitive_periodic {g : ℝ → ℝ} {T : ℝ}
    (hg : Continuous g) (hp : Function.Periodic g T)
    (hm : ∫ s in (0 : ℝ)..T, g s = 0) :
    Function.Periodic (periodicPrimitive g) T := by
  intro t
  unfold periodicPrimitive
  rw [hp.intervalIntegral_add_eq_add 0 t (fun a b => hg.intervalIntegrable a b)]
  simpa using hm

/-- Global supremum bound in a pointwise form, retaining all real times.
A bound just on one period is sufficient by periodicity. -/
theorem periodicPrimitive_abs_le {g : ℝ → ℝ} {T B : ℝ}
    (hT : 0 < T) (hg : Continuous g) (hp : Function.Periodic g T)
    (hm : ∫ s in (0 : ℝ)..T, g s = 0) (hB : 0 ≤ B)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) T, |g t| ≤ B) :
    ∀ t, |periodicPrimitive g t| ≤ T * B := by
  intro t
  let n := toIcoDiv hT 0 t
  let s := t - n • T
  have hs : s ∈ Set.Ico (0 : ℝ) T := by
    simpa only [zero_add] using sub_toIcoDiv_zsmul_mem_Ico hT 0 t
  have hQ := periodicPrimitive_periodic hg hp hm
  have heq : periodicPrimitive g s = periodicPrimitive g t := hQ.sub_zsmul_eq n
  rw [← heq]
  have hbound : |periodicPrimitive g s| ≤ B * |s - 0| := by
    simpa [periodicPrimitive, Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_of_norm_le_const (f := g) (a := (0 : ℝ)) (b := s)
        (fun x hx => by
          have hxs : x ∈ Set.Ioc (0 : ℝ) s := by simpa only [Set.uIoc_of_le hs.1] using hx
          simpa only [Real.norm_eq_abs] using hb x ⟨hxs.1.le, hxs.2.trans hs.2.le⟩)
  rw [sub_zero, abs_of_nonneg hs.1] at hbound
  exact hbound.trans (by nlinarith only [hs.2.le, hB])

end AVenhance.Infra.Section5
