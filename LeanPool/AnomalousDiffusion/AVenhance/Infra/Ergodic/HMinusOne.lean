/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragesL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.Flow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus

/-! # The homogeneous negative Sobolev duality on the unit torus -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open scoped ContDiff
open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The squared `L²` norm of the coordinate gradient on the unit cell. -/
def gradientL2SquaredAverage {d : ℕ} (φ : Homogenization.Vec d → ℝ) : ℝ :=
  cellAverage fun x => ∑ i, (fderiv ℝ φ x (Pi.single i (1 : ℝ))) ^ 2

/-- Smooth periodic mean-zero representatives with gradient norm at most one,
used for the homogeneous dual test space. -/
def HMinusOneTest (d : ℕ) :=
  {φ : Homogenization.Vec d → ℝ //
    ContDiff ℝ ∞ φ ∧ IsZPeriodic φ ∧ cellAverage φ = 0 ∧
      gradientL2SquaredAverage φ ≤ 1}

/-- The homogeneous `H⁻¹` dual seminorm, represented as an extended nonnegative
real to allow the defining supremum before its finiteness is proved. -/
def homogeneousHMinusOneNorm {d : ℕ} (h : Homogenization.Vec d → ℝ) : ℝ≥0∞ :=
  ⨆ φ : HMinusOneTest d,
    ENNReal.ofReal |cellAverage (fun x => h x * φ.val x)|

theorem HMinusOne.unitCellSet_eq_torusUnitCell (d : ℕ) :
    unitCellSet d = Torus.unitCell d := by
  ext x
  simp [unitCellSet, Torus.unitCell, Torus.unitCellAt]

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def HMinusOne.closedUnitCube (d : ℕ) : Set (Homogenization.Vec d) :=
  Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1

theorem HMinusOne.unitCell_subset_closedUnitCube (d : ℕ) :
    Torus.unitCell d ⊆ HMinusOne.closedUnitCube d := by
  intro x hx
  simp only [HMinusOne.closedUnitCube, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, by simpa using (hx i).2⟩

theorem HMinusOne.continuousComplex_unitCell_integrable {d : ℕ}
    {u : Homogenization.Vec d → ℂ} (hu : Continuous u) :
    IntegrableOn u (Torus.unitCell d) := by
  have hcube : IsCompact (HMinusOne.closedUnitCube d) := by
    simpa [HMinusOne.closedUnitCube] using isCompact_univ_pi fun _ : Fin d => isCompact_Icc
  exact hu.continuousOn.integrableOn_compact hcube |>.mono_set
    (HMinusOne.unitCell_subset_closedUnitCube d)

/-- Every admissible dual pairing is bounded by the homogeneous
`H⁻¹` seminorm. -/
theorem dualPairing_le_homogeneousHMinusOneNorm {d : ℕ}
    (h : Homogenization.Vec d → ℝ) (φ : HMinusOneTest d) :
    ENNReal.ofReal |cellAverage (fun x => h x * φ.val x)| ≤
      homogeneousHMinusOneNorm h := by
  exact le_iSup (fun ψ : HMinusOneTest d =>
    ENNReal.ofReal |cellAverage (fun x => h x * ψ.val x)|) φ

theorem HMinusOne.coordDeriv_realCast {d : ℕ} {f : Homogenization.Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin d) (x : Homogenization.Vec d) :
    AVenhance.Infra.Torus.coordDeriv i (fun y => (f y : ℂ)) x =
      (fderiv ℝ f x (Homogenization.basisVec i) : ℂ) := by
  have hreal := (hf.contDiffAt (x := x)).differentiableAt (by norm_num)
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x (Homogenization.basisVec i) = _
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt hreal]
  simp [Homogenization.basisVec]

/-- A Poincaré dual bound for the homogeneous `H⁻¹` seminorm. This is the
basic dual step used after an independent estimate of the product's cell
`L²` norm. -/
theorem homogeneousHMinusOneNorm_le_of_cellL2
    {d : ℕ} (hd : 0 < d) {h : Homogenization.Vec d → ℝ}
    (hL2 : MemLp h (ENNReal.ofReal (2 : ℝ))
      ((volume : Measure (Homogenization.Vec d)).restrict (Torus.unitCell d))) :
    homogeneousHMinusOneNorm h ≤ ENNReal.ofReal
      ((∫ x in Torus.unitCell d, h x ^ 2) ^ (1 / 2 : ℝ) *
        ((4 * Real.pi ^ 2)⁻¹) ^ (1 / 2 : ℝ)) := by
  classical
  apply iSup_le
  intro φ
  let ψ := φ.val
  have hψsmooth : ContDiff ℝ 1 ψ := φ.property.1.of_le (by simp)
  have hψper : Torus.IsZdPeriodic (fun x => (ψ x : ℂ)) := by
    intro k x
    exact congrArg Complex.ofReal (φ.property.2.1 x k)
  have hψcell : cellAverage ψ = ∫ x in Torus.unitCell d, ψ x := by
    rw [cellAverage_eq_unitCellIntegral, HMinusOne.unitCellSet_eq_torusUnitCell]
  have hψintReal : ∫ x in Torus.unitCell d, ψ x = 0 := by
    rw [← hψcell]
    exact φ.property.2.2.1
  have hψint : ∫ x in Torus.unitCell d, (ψ x : ℂ) = 0 := by
    have hψintegrable := continuous_unitCell_integrable hψsmooth.continuous
    have hmap := Complex.ofRealCLM.integral_comp_comm
      (μ := (volume : Measure (Homogenization.Vec d)).restrict (Torus.unitCell d))
      hψintegrable
    simpa [hψintReal] using hmap
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hP := AVenhance.Infra.Torus.meanZero_smoothPeriodic_poincare
    (f := fun x => (ψ x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hψsmooth) hψper hψint
  have hgrad :
      (∫ x in Torus.unitCell (n + 1),
        ∑ i : Fin (n + 1),
          ‖AVenhance.Infra.Torus.coordDeriv i (fun x => (ψ x : ℂ)) x‖ ^ 2) ≤ 1 := by
    have heq :
        (∫ x in Torus.unitCell (n + 1),
          ∑ i : Fin (n + 1),
            ‖AVenhance.Infra.Torus.coordDeriv i (fun x => (ψ x : ℂ)) x‖ ^ 2) =
      gradientL2SquaredAverage ψ := by
      unfold gradientL2SquaredAverage
      rw [cellAverage_eq_unitCellIntegral, HMinusOne.unitCellSet_eq_torusUnitCell]
      apply setIntegral_congr_fun (Torus.measurableSet_unitCell (n + 1))
      intro x hx
      calc
        _ = ∑ i : Fin (n + 1),
            (fderiv ℝ ψ x (Homogenization.basisVec i)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [HMinusOne.coordDeriv_realCast hψsmooth i x]
              simp
        _ = ∑ i : Fin (n + 1),
            (fderiv ℝ ψ x (Pi.single i (1 : ℝ))) ^ 2 := by
              simp [Homogenization.basisVec]
    rw [heq]
    exact φ.property.2.2.2
  have hψsq :
      ∫ x in Torus.unitCell (n + 1), ‖(ψ x : ℂ)‖ ^ 2 ≤
        (4 * Real.pi ^ 2)⁻¹ := by
    calc
      _ ≤ (4 * Real.pi ^ 2)⁻¹ *
          ∫ x in Torus.unitCell (n + 1),
            ∑ i : Fin (n + 1),
              ‖AVenhance.Infra.Torus.coordDeriv i (fun x => (ψ x : ℂ)) x‖ ^ 2 := hP
      _ ≤ (4 * Real.pi ^ 2)⁻¹ := by
        have hc : 0 ≤ (4 * Real.pi ^ 2)⁻¹ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hgrad hc]
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (f := fun x => |h x|) (g := fun x => |ψ x|)
    (μ := (volume : Measure (Homogenization.Vec (n + 1))).restrict
      (Torus.unitCell (n + 1)))
    Real.HolderConjugate.two_two
    (ae_of_all _ fun x => abs_nonneg _)
    (ae_of_all _ fun x => abs_nonneg _)
    (hL2.norm) (continuous_unitCell_memLp_two hψsmooth.continuous).norm
  have hcellPair :
      cellAverage (fun x => h x * ψ x) =
        ∫ x in Torus.unitCell (n + 1), h x * ψ x := by
    simpa [unitCellSet, Torus.unitCell, Torus.unitCellAt] using
      (cellAverage_eq_unitCellIntegral (f := fun x => h x * ψ x))
  have hpair : |cellAverage (fun x => h x * ψ x)| ≤
      (∫ x in Torus.unitCell (n + 1), h x ^ 2) ^ (1 / 2 : ℝ) *
        ((4 * Real.pi ^ 2)⁻¹) ^ (1 / 2 : ℝ) := by
    rw [hcellPair]
    calc
      |∫ x in Torus.unitCell (n + 1), h x * ψ x| ≤
          ∫ x in Torus.unitCell (n + 1), |h x| * |ψ x| := by
        calc
          _ = ‖∫ x in Torus.unitCell (n + 1), h x * ψ x‖ := by rw [Real.norm_eq_abs]
          _ ≤ ∫ x in Torus.unitCell (n + 1), ‖h x * ψ x‖ := norm_integral_le_integral_norm _
          _ = _ := by
            apply setIntegral_congr_fun (Torus.measurableSet_unitCell (n + 1))
            intro x hx
            simp [norm_mul]
      _ ≤ _ := by
        have hsqA : (∫ x in Torus.unitCell (n + 1), |h x| ^ 2) =
            ∫ x in Torus.unitCell (n + 1), h x ^ 2 := by
          apply setIntegral_congr_fun (Torus.measurableSet_unitCell (n + 1))
          intro x hx
          simp [sq_abs]
        have hsqB : (∫ x in Torus.unitCell (n + 1), |ψ x| ^ 2) ≤
            (4 * Real.pi ^ 2)⁻¹ := by
          calc
            _ = ∫ x in Torus.unitCell (n + 1), ‖(ψ x : ℂ)‖ ^ 2 := by
              apply setIntegral_congr_fun (Torus.measurableSet_unitCell (n + 1))
              intro x hx
              simp
            _ ≤ _ := hψsq
        have hholder' :
            (∫ x in Torus.unitCell (n + 1), |h x| * |ψ x|) ≤
              ((∫ x in Torus.unitCell (n + 1), |h x| ^ 2) ^ (1 / 2 : ℝ) *
                (∫ x in Torus.unitCell (n + 1), |ψ x| ^ 2) ^ (1 / 2 : ℝ)) := by
          simpa [Real.rpow_natCast] using hholder
        rw [hsqA] at hholder'
        have hrootB := Real.rpow_le_rpow
          (integral_nonneg (fun x => sq_nonneg (|ψ x|))) hsqB
          (by norm_num : 0 ≤ (1 / 2 : ℝ))
        have hrootA : 0 ≤
            (∫ x in Torus.unitCell (n + 1), h x ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_nonneg (integral_nonneg (fun _ => sq_nonneg _)) _
        exact hholder'.trans (mul_le_mul_of_nonneg_left hrootB
          hrootA)
  exact ENNReal.ofReal_le_ofReal hpair

/-! ### Divergence certificates

The source proof's frequency split is intended to produce a small vector
potential for its low-frequency product.  This duality lemma records the
analytic estimate needed after that construction: a periodic divergence has
homogeneous `H⁻¹` norm bounded by the `L²` norm of its potential. -/

/-- The cell-averaged squared size of a real vector field. -/
def vectorFieldL2SquaredAverage {d : ℕ}
    (V : Fin d → Homogenization.Vec d → ℝ) : ℝ :=
  cellAverage fun x => ∑ i, (V i x) ^ 2

theorem HMinusOne.cellAverage_const_mul {d : ℕ} (c : ℝ) (f : Homogenization.Vec d → ℝ) :
    cellAverage (fun x => c * f x) = c * cellAverage f := by
  unfold cellAverage torusFunction
  exact integral_const_mul c _

/-- Flow transport for the homogeneous dual norm. The `hmap` premise states
the precise test-function bound needed after composing tests with `X` and
rescaling them into the unit gradient ball. A derivative bound on `X` implies
this premise through the chain rule and measure preservation. -/
theorem homogeneousHMinusOneNorm_flow_le_of_testComposition
    {d : ℕ} {f g : Homogenization.Vec d → ℝ}
    (hf : IsZPeriodic f) (hg : IsZPeriodic g)
    (X : PeriodicVolumePreservingDiffeomorphism d) (L : ℝ) (hL : 0 < L)
    (hmap : ∀ (φ : Homogenization.Vec d → ℝ), ContDiff ℝ ∞ φ →
      IsZPeriodic φ → cellAverage φ = 0 → gradientL2SquaredAverage φ ≤ 1 →
      gradientL2SquaredAverage (fun x => L⁻¹ * φ (X.toFun x)) ≤ 1) :
    homogeneousHMinusOneNorm (fun x => f x * g (X.invFun x)) ≤
      ENNReal.ofReal L *
        homogeneousHMinusOneNorm (fun x => f (X.toFun x) * g x) := by
  classical
  unfold homogeneousHMinusOneNorm
  apply iSup_le
  intro φ
  let ψ : Homogenization.Vec d → ℝ := fun x => L⁻¹ * φ.val (X.toFun x)
  have hψsmooth : ContDiff ℝ ∞ ψ := by
    change ContDiff ℝ ∞ (fun x => L⁻¹ * φ.val (X.toFun x))
    exact contDiff_const.mul (φ.property.1.comp X.contDiff_toFun)
  have hψper : IsZPeriodic ψ := by
    intro x k
    change L⁻¹ * φ.val (X.toFun (x + latticeVector k)) = _
    rw [X.lattice_equivariant x k]
    exact congrArg (fun y : ℝ => L⁻¹ * y)
      (φ.property.2.1 (X.toFun x) k)
  have hψmean : cellAverage ψ = 0 := by
    rw [show ψ = fun x => L⁻¹ * φ.val (X.toFun x) by rfl,
      HMinusOne.cellAverage_const_mul, cellAverage_comp_flow_eq φ.val φ.property.2.1 X,
      φ.property.2.2.1]
    simp
  have hψgrad := hmap φ.val φ.property.1 φ.property.2.1
    φ.property.2.2.1 φ.property.2.2.2
  let ψtest : HMinusOneTest d := ⟨ψ, hψsmooth, hψper, hψmean, hψgrad⟩
  have hpairChange :
      cellAverage (fun x => f x * g (X.invFun x) * φ.val x) =
        cellAverage (fun x => f (X.toFun x) * g x * φ.val (X.toFun x)) := by
    have hperProd : IsZPeriodic (fun x => f x * φ.val x) := by
      intro x k
      simp [hf x k, φ.property.2.1 x k]
    have hchange := cellAverage_mul_comp_inv_eq hperProd hg X
    calc
      _ = cellAverage (fun x => (f x * φ.val x) * g (X.invFun x)) := by
        congr 1
        funext x
        ring
      _ = cellAverage (fun x => (f (X.toFun x) * φ.val (X.toFun x)) * g x) := hchange
      _ = _ := by
        congr 1
        funext x
        ring
  have hpairScale :
      cellAverage (fun x => f (X.toFun x) * g x * φ.val (X.toFun x)) =
        L * cellAverage (fun x => f (X.toFun x) * g x * ψ x) := by
    calc
      _ = cellAverage (fun x => L *
          (f (X.toFun x) * g x * ψ x)) := by
        congr 1
        funext x
        dsimp [ψ]
        field_simp [hL.ne']
      _ = _ := HMinusOne.cellAverage_const_mul L _
  have habs :
      |cellAverage (fun x => f x * g (X.invFun x) * φ.val x)| =
        L * |cellAverage (fun x => f (X.toFun x) * g x * ψ x)| := by
    rw [hpairChange, hpairScale, abs_mul, abs_of_nonneg hL.le]
  calc
    _ = ENNReal.ofReal L *
        ENNReal.ofReal |cellAverage (fun x => f (X.toFun x) * g x * ψ x)| := by
          rw [habs, ENNReal.ofReal_mul hL.le]
    _ ≤ ENNReal.ofReal L *
        homogeneousHMinusOneNorm (fun x => f (X.toFun x) * g x) := by
          gcongr
          exact dualPairing_le_homogeneousHMinusOneNorm _ ψtest

end

end AVenhance.Infra.Ergodic
