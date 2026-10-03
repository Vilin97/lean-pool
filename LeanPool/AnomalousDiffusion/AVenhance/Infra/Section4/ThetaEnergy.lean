/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaPeriodicity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Fourier
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Calculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge

/-! Ordered spatial derivatives at adjacent orders.

This is the pointwise component estimate used for the first-derivative
commutator group in the differentiated energy calculation: an order-`n+1`
coordinate derivative is a component of the gradient of an order-`n`
coordinate derivative.
-/

@[expose] public section

open Homogenization
open MeasureTheory

namespace AVenhance.Infra.Section4

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def ThetaEnergy.thetaClosedCell : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem ThetaEnergy.thetaClosedCell_compact : IsCompact ThetaEnergy.thetaClosedCell := by
  simpa [ThetaEnergy.thetaClosedCell] using (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem ThetaEnergy.thetaUnitCube_subset_closedCell : AVenhance.unitCube ⊆
    ThetaEnergy.thetaClosedCell := by
  intro x hx
  change (∀ i ∈ Set.univ, x i ∈ Set.Ioo (0 : ℝ) 1) at hx
  change (∀ i ∈ Set.univ, x i ∈ Set.Icc (0 : ℝ) 1)
  intro i hi
  exact ⟨le_of_lt (hx i hi).1, le_of_lt (hx i hi).2⟩

theorem ThetaEnergy.theta_integrableOn_unitCube {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f AVenhance.unitCube :=
  (hf.continuousOn.integrableOn_compact ThetaEnergy.thetaClosedCell_compact).mono_set
    ThetaEnergy.thetaUnitCube_subset_closedCell

theorem ThetaEnergy.theta_measurableSet_unitCube : MeasurableSet AVenhance.unitCube := by
  change MeasurableSet (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1)
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

theorem ThetaEnergy.thetaUnitCell_subset_closedCell :
    AVenhance.Infra.Torus.unitCell 2 ⊆ ThetaEnergy.thetaClosedCell := by
  intro x hx
  simp only [AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt,
    Set.mem_ofPred_eq, zero_add] at hx
  simp only [ThetaEnergy.thetaClosedCell, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, (hx i).2⟩

theorem ThetaEnergy.theta_integrableOn_unitCell {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f (AVenhance.Infra.Torus.unitCell 2) :=
  (hf.continuousOn.integrableOn_compact ThetaEnergy.thetaClosedCell_compact).mono_set
    ThetaEnergy.thetaUnitCell_subset_closedCell

theorem ThetaEnergy.theta_realToComplex_periodic {f : Vec 2 → ℝ}
    (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.Infra.Torus.IsZdPeriodic (AVenhance.Infra.Torus.realToComplex f) := by
  intro k x
  exact congrArg (fun y : ℝ => (y : ℂ))
    ((AVenhance.Infra.Torus.isZdPeriodic_iff_frozen f).2 hper k x)

theorem ThetaEnergy.theta_continuous_spaceGrad_coord {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    Continuous (fun x => AVenhance.spaceGrad f x i) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem ThetaEnergy.theta_integral_unitCube_coord_ibp {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hpf : AVenhance.IsZ2Periodic f) (hpg : AVenhance.IsZ2Periodic g)
    (i : Fin 2) :
    (∫ x in AVenhance.unitCube, f x * AVenhance.spaceGrad g x i) =
      -∫ x in AVenhance.unitCube, AVenhance.spaceGrad f x i * g x := by
  let fc := AVenhance.Infra.Torus.realToComplex f
  let gc := AVenhance.Infra.Torus.realToComplex g
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  have hfc : ContDiff ℝ 1 fc :=
    (Complex.ofRealCLM.contDiff.comp hf1).of_le (by simp)
  have hgc : ContDiff ℝ 1 gc :=
    (Complex.ofRealCLM.contDiff.comp hg1).of_le (by simp)
  have hcomplex := AVenhance.Infra.Torus.integral_unitCell_coord_ibp i hfc hgc
    (ThetaEnergy.theta_realToComplex_periodic hpf) (ThetaEnergy.theta_realToComplex_periodic hpg)
  have hcomplex' :
      (∫ x in AVenhance.Infra.Torus.unitCell 2,
        ((f x * AVenhance.spaceGrad g x i : ℝ) : ℂ)) =
      -∫ x in AVenhance.Infra.Torus.unitCell 2,
        ((AVenhance.spaceGrad f x i * g x : ℝ) : ℂ) := by
    calc
      _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
          fc x * AVenhance.Infra.Torus.coordDeriv i gc x := by
        apply setIntegral_congr_fun (AVenhance.Infra.Torus.measurableSet_unitCell 2)
        intro x hx
        simp only [fc, gc]
        rw [AVenhance.Infra.Torus.coordDeriv_realToComplex hg1 i x]
        simp [AVenhance.Infra.Torus.realToComplex, Complex.ofReal_mul]
      _ = -∫ x in AVenhance.Infra.Torus.unitCell 2,
          AVenhance.Infra.Torus.coordDeriv i fc x * gc x := hcomplex
      _ = -∫ x in AVenhance.Infra.Torus.unitCell 2,
          ((AVenhance.spaceGrad f x i * g x : ℝ) : ℂ) := by
        congr 1
        apply setIntegral_congr_fun (AVenhance.Infra.Torus.measurableSet_unitCell 2)
        intro x hx
        simp only [fc, gc]
        rw [AVenhance.Infra.Torus.coordDeriv_realToComplex hf1 i x]
        simp [AVenhance.Infra.Torus.realToComplex, Complex.ofReal_mul]
  have hleftInt : IntegrableOn
      (fun x : Vec 2 => f x * AVenhance.spaceGrad g x i)
      (AVenhance.Infra.Torus.unitCell 2) :=
    ThetaEnergy.theta_integrableOn_unitCell (hf.continuous.mul
      (ThetaEnergy.theta_continuous_spaceGrad_coord hg i))
  have hrightInt : IntegrableOn
      (fun x : Vec 2 => AVenhance.spaceGrad f x i * g x)
      (AVenhance.Infra.Torus.unitCell 2) :=
    ThetaEnergy.theta_integrableOn_unitCell ((ThetaEnergy.theta_continuous_spaceGrad_coord hf
        i).mul hg.continuous)
  have hleftCast :
      (∫ x in AVenhance.Infra.Torus.unitCell 2,
        ((f x * AVenhance.spaceGrad g x i : ℝ) : ℂ)) =
      ((∫ x in AVenhance.Infra.Torus.unitCell 2,
        f x * AVenhance.spaceGrad g x i : ℝ) : ℂ) := by
    simpa using (Complex.ofRealCLM.integral_comp_comm
      (μ := (volume : Measure (Vec 2)).restrict (AVenhance.Infra.Torus.unitCell 2))
      hleftInt)
  have hrightCast :
      (∫ x in AVenhance.Infra.Torus.unitCell 2,
        ((AVenhance.spaceGrad f x i * g x : ℝ) : ℂ)) =
      ((∫ x in AVenhance.Infra.Torus.unitCell 2,
        AVenhance.spaceGrad f x i * g x : ℝ) : ℂ) := by
    simpa using (Complex.ofRealCLM.integral_comp_comm
      (μ := (volume : Measure (Vec 2)).restrict (AVenhance.Infra.Torus.unitCell 2))
      hrightInt)
  have hrealCell :
      (∫ x in AVenhance.Infra.Torus.unitCell 2,
        f x * AVenhance.spaceGrad g x i) =
      -∫ x in AVenhance.Infra.Torus.unitCell 2,
        AVenhance.spaceGrad f x i * g x := by
    have hcast := hleftCast.symm.trans (hcomplex'.trans (congrArg Neg.neg hrightCast))
    have hre := congrArg Complex.re hcast
    simpa using hre
  rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube,
    ← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  exact hrealCell

theorem ThetaEnergy.theta_spaceGrad_periodic {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (AVenhance.spaceGrad f) := by
  intro k x
  let v : Vec 2 := AVenhance.latticeShift k
  have hfun : (fun y : Vec 2 => f (y + v)) = f := by
    funext y
    exact hper k y
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have htranslate : HasFDerivAt (fun y : Vec 2 => y + v)
      (ContinuousLinearMap.id ℝ (Vec 2)) x := by
    simpa only [id_eq] using (hasFDerivAt_id x).add_const v
  have hcomp := (hdiff (x + v)).hasFDerivAt.comp x htranslate
  have hshift : HasFDerivAt f (fderiv ℝ f (x + v)) x := by
    have hcomp' := hcomp
    change HasFDerivAt (fun y : Vec 2 => f (y + v))
      (fderiv ℝ f (x + v) ∘L ContinuousLinearMap.id ℝ (Vec 2)) x at hcomp'
    rw [ContinuousLinearMap.comp_id, hfun] at hcomp'
    exact hcomp'
  have hbase : HasFDerivAt f (fderiv ℝ f x) x := (hdiff x).hasFDerivAt
  have hderiv : fderiv ℝ f (x + v) = fderiv ℝ f x := hshift.unique hbase
  funext i
  change fderiv ℝ f (x + AVenhance.latticeShift k) (basisVec i) =
    fderiv ℝ f x (basisVec i)
  exact congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) hderiv

theorem ThetaEnergy.theta_spaceGrad_contDiff {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceGrad f) := by
  have hjoint : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Vec 2 × Vec 2 => fderiv ℝ f p.1 p.2) :=
    hf.contDiff_fderiv_apply (by simp)
  apply contDiff_pi.2
  intro i
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (x, basisVec i)) := by
    fun_prop
  have hcomp := hjoint.comp hmap
  simpa only [Function.comp_def, Prod.fst, Prod.snd, AVenhance.spaceGrad] using hcomp

theorem ThetaEnergy.theta_mixed_partial_commute {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y 0) x 1 =
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y 1) x 0 := by
  have hAt := hf.contDiffAt (x := x)
  have hC2 : ContDiffAt ℝ 2 f x := hAt.of_le (by norm_num)
  have hsymm := hC2.isSymmSndFDerivAt (by simp)
  have hc : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hCderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hAt.fderiv_right (m := 1) (by simp)
    exact hCderiv.differentiableAt (by norm_num)
  have hu0 : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec (0 : Fin 2)) x :=
    differentiableAt_const (basisVec (0 : Fin 2))
  have hu1 : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec (1 : Fin 2)) x :=
    differentiableAt_const (basisVec (1 : Fin 2))
  have hderiv0 : fderiv ℝ (fun y => fderiv ℝ f y (basisVec (0 : Fin 2))) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (basisVec (0 : Fin 2)) := by
    have h := fderiv_clm_apply hc hu0
    simpa using h
  have hderiv1 : fderiv ℝ (fun y => fderiv ℝ f y (basisVec (1 : Fin 2))) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (basisVec (1 : Fin 2)) := by
    have h := fderiv_clm_apply hc hu1
    simpa using h
  have hleft : AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y 0) x 1 =
      fderiv ℝ (fderiv ℝ f) x (basisVec 1) (basisVec 0) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (basisVec 0)) x (basisVec 1) = _
    rw [hderiv0]
    rfl
  have hright : AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y 1) x 0 =
      fderiv ℝ (fderiv ℝ f) x (basisVec 0) (basisVec 1) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (basisVec 1)) x (basisVec 0) = _
    rw [hderiv1]
    rfl
  rw [hleft, hright]
  exact hsymm (basisVec 1) (basisVec 0)

theorem ThetaEnergy.theta_spaceGrad_mul {f g : Vec 2 → ℝ} {x : Vec 2} (i : Fin 2)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    AVenhance.spaceGrad (fun y => f y * g y) x i =
      AVenhance.spaceGrad f x i * g x + f x * AVenhance.spaceGrad g x i := by
  change fderiv ℝ (fun y => f y * g y) x (basisVec i) = _
  rw [fderiv_fun_mul hf hg]
  simp [AVenhance.spaceGrad]
  ring

theorem ThetaEnergy.theta_streamVel_components {φ : ℝ → Vec 2 → ℝ} {t : ℝ} {x : Vec 2} :
    AVenhance.streamVel φ t x 0 = -AVenhance.spaceGrad (φ t) x 1 ∧
    AVenhance.streamVel φ t x 1 = AVenhance.spaceGrad (φ t) x 0 := by
  have hform : AVenhance.streamVel φ t x =
      ![-AVenhance.spaceGrad (φ t) x 1, AVenhance.spaceGrad (φ t) x 0] := by
    funext i
    fin_cases i <;> simp [AVenhance.streamVel, AVenhance.sigmaMat,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  constructor
  · have h := congrFun hform 0
    simpa using h
  · have h := congrFun hform 1
    simpa using h

/-- The spatial Laplacian contributes exactly the negative Dirichlet energy
when paired with a smooth periodic function on the unit torus cell. -/
theorem theta_laplacian_pairing {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : AVenhance.IsZ2Periodic f) :
    (∫ x in AVenhance.unitCube, f x * AVenhance.spaceLap f x) =
      -∫ x in AVenhance.unitCube, vecNormSq (AVenhance.spaceGrad f x) := by
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceGrad f) :=
    ThetaEnergy.theta_spaceGrad_contDiff hf
  have hgradPer : AVenhance.IsZ2Periodic (AVenhance.spaceGrad f) :=
    ThetaEnergy.theta_spaceGrad_periodic (hf.of_le (by simp)) hper
  have hcoord (i : Fin 2) :
      ∫ x in AVenhance.unitCube,
        f x * AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y i) x i =
        -∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 := by
    have hgi : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad f y i) :=
      contDiff_pi.mp hgrad i
    have hgiPer : AVenhance.IsZ2Periodic (fun y => AVenhance.spaceGrad f y i) :=
      fun k x => congrArg (fun V : Vec 2 => V i) (hgradPer k x)
    have hibp := ThetaEnergy.theta_integral_unitCube_coord_ibp
      (f := f) (g := fun y => AVenhance.spaceGrad f y i) hf hgi hper hgiPer i
    simpa only [pow_two] using hibp
  have hsecondContinuous (i : Fin 2) :
      Continuous (fun x => AVenhance.spaceGrad
        (fun y => AVenhance.spaceGrad f y i) x i) := by
    have hgi : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad f y i) :=
      contDiff_pi.mp hgrad i
    exact (hgi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hintegrable (i : Fin 2) : IntegrableOn
      (fun x => f x * AVenhance.spaceGrad
        (fun y => AVenhance.spaceGrad f y i) x i) AVenhance.unitCube :=
    ThetaEnergy.theta_integrableOn_unitCube (hf.continuous.mul (hsecondContinuous i))
  have hsumIntegrable := hintegrable 0
  have hsumIntegrable' := hintegrable 1
  have hlap : AVenhance.spaceLap f = fun x =>
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y 0) x 0 +
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y 1) x 1 := by
    funext x
    simp [AVenhance.spaceLap, Fin.sum_univ_two]
  rw [hlap]
  simp only [mul_add]
  rw [integral_add hsumIntegrable hsumIntegrable', hcoord 0, hcoord 1]
  have hnorm : (fun x => vecNormSq (AVenhance.spaceGrad f x)) = fun x =>
      (AVenhance.spaceGrad f x 0) ^ 2 + (AVenhance.spaceGrad f x 1) ^ 2 := by
    funext x
    simp [vecNormSq, vecDot, Fin.sum_univ_two, pow_two]
  rw [hnorm, integral_add]
  · ring
  · exact ThetaEnergy.theta_integrableOn_unitCube
      (((continuous_apply (0 : Fin 2)).comp hgrad.continuous).pow 2)
  · exact ThetaEnergy.theta_integrableOn_unitCube
      (((continuous_apply (1 : Fin 2)).comp hgrad.continuous).pow 2)

/-- A stream drift makes no contribution to the scalar energy pairing. The
proof expands the two coordinates, integrates each cross term by parts, and
uses symmetry of the stream Hessian. -/
theorem theta_stream_drift_pairing_zero {φ u : Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφper : AVenhance.IsZ2Periodic φ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huper : AVenhance.IsZ2Periodic u) :
    (∫ x in AVenhance.unitCube,
      u x * vecDot (AVenhance.streamVel (fun _ => φ) 0 x)
        (AVenhance.spaceGrad u x)) = 0 := by
  let φx : Vec 2 → ℝ := fun x => AVenhance.spaceGrad φ x 0
  let φy : Vec 2 → ℝ := fun x => AVenhance.spaceGrad φ x 1
  let ux : Vec 2 → ℝ := fun x => AVenhance.spaceGrad u x 0
  let uy : Vec 2 → ℝ := fun x => AVenhance.spaceGrad u x 1
  let φxy : Vec 2 → ℝ := fun x =>
    AVenhance.spaceGrad (fun y => AVenhance.spaceGrad φ y 0) x 1
  let φyx : Vec 2 → ℝ := fun x =>
    AVenhance.spaceGrad (fun y => AVenhance.spaceGrad φ y 1) x 0
  let A : ℝ := ∫ x in AVenhance.unitCube, (u x * φx x) * uy x
  let B : ℝ := ∫ x in AVenhance.unitCube, (u x * φy x) * ux x
  let P : ℝ := ∫ x in AVenhance.unitCube, u x ^ 2 * φxy x
  let Q : ℝ := ∫ x in AVenhance.unitCube, u x ^ 2 * φyx x
  have hφgrad : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceGrad φ) :=
    ThetaEnergy.theta_spaceGrad_contDiff hφ
  have hφx : ContDiff ℝ (⊤ : ℕ∞) φx := by
    exact (contDiff_pi.mp hφgrad 0)
  have hφy : ContDiff ℝ (⊤ : ℕ∞) φy := by
    exact (contDiff_pi.mp hφgrad 1)
  have hugrad : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceGrad u) :=
    ThetaEnergy.theta_spaceGrad_contDiff hu
  have hux : ContDiff ℝ (⊤ : ℕ∞) ux := contDiff_pi.mp hugrad 0
  have huy : ContDiff ℝ (⊤ : ℕ∞) uy := contDiff_pi.mp hugrad 1
  have hφxySmooth : ContDiff ℝ (⊤ : ℕ∞) φxy := by
    exact contDiff_pi.mp (ThetaEnergy.theta_spaceGrad_contDiff hφx) 1
  have hφyxSmooth : ContDiff ℝ (⊤ : ℕ∞) φyx := by
    exact contDiff_pi.mp (ThetaEnergy.theta_spaceGrad_contDiff hφy) 0
  have hφgradPer : AVenhance.IsZ2Periodic (AVenhance.spaceGrad φ) :=
    ThetaEnergy.theta_spaceGrad_periodic (hφ.of_le (by simp)) hφper
  have hφxPer : AVenhance.IsZ2Periodic φx := fun k x =>
    congrArg (fun v : Vec 2 => v 0) (hφgradPer k x)
  have hφyPer : AVenhance.IsZ2Periodic φy := fun k x =>
    congrArg (fun v : Vec 2 => v 1) (hφgradPer k x)
  have huPerGrad : AVenhance.IsZ2Periodic (AVenhance.spaceGrad u) :=
    ThetaEnergy.theta_spaceGrad_periodic (hu.of_le (by simp)) huper
  have huxPer : AVenhance.IsZ2Periodic ux := fun k x =>
    congrArg (fun v : Vec 2 => v 0) (huPerGrad k x)
  have huyPer : AVenhance.IsZ2Periodic uy := fun k x =>
    congrArg (fun v : Vec 2 => v 1) (huPerGrad k x)
  have hφxderivPer : AVenhance.IsZ2Periodic
      (AVenhance.spaceGrad φx) :=
    ThetaEnergy.theta_spaceGrad_periodic (hφx.of_le (by simp)) hφxPer
  have hφyderivPer : AVenhance.IsZ2Periodic
      (AVenhance.spaceGrad φy) :=
    ThetaEnergy.theta_spaceGrad_periodic (hφy.of_le (by simp)) hφyPer
  have hprodX : ContDiff ℝ (⊤ : ℕ∞) (fun x => u x * φx x) := hu.mul hφx
  have hprodY : ContDiff ℝ (⊤ : ℕ∞) (fun x => u x * φy x) := hu.mul hφy
  have hprodXPer : AVenhance.IsZ2Periodic (fun x => u x * φx x) := by
    intro k x
    change u (x + AVenhance.latticeShift k) * φx (x + AVenhance.latticeShift k) = _
    rw [huper k x, hφxPer k x]
  have hprodYPer : AVenhance.IsZ2Periodic (fun x => u x * φy x) := by
    intro k x
    change u (x + AVenhance.latticeShift k) * φy (x + AVenhance.latticeShift k) = _
    rw [huper k x, hφyPer k x]
  have hpartsX := ThetaEnergy.theta_integral_unitCube_coord_ibp
    (f := fun x => u x * φx x) (g := u) hprodX hu hprodXPer huper 1
  have hpartsY := ThetaEnergy.theta_integral_unitCube_coord_ibp
    (f := fun x => u x * φy x) (g := u) hprodY hu hprodYPer huper 0
  have hIntA : IntegrableOn (fun x => (u x * φx x) * uy x)
      AVenhance.unitCube := ThetaEnergy.theta_integrableOn_unitCube
        ((hu.continuous.mul hφx.continuous).mul huy.continuous)
  have hIntB : IntegrableOn (fun x => (u x * φy x) * ux x)
      AVenhance.unitCube := ThetaEnergy.theta_integrableOn_unitCube
        ((hu.continuous.mul hφy.continuous).mul hux.continuous)
  have hIntP : IntegrableOn (fun x => u x ^ 2 * φxy x)
      AVenhance.unitCube := ThetaEnergy.theta_integrableOn_unitCube
        ((hu.continuous.pow 2).mul hφxySmooth.continuous)
  have hIntQ : IntegrableOn (fun x => u x ^ 2 * φyx x)
      AVenhance.unitCube := ThetaEnergy.theta_integrableOn_unitCube
        ((hu.continuous.pow 2).mul hφyxSmooth.continuous)
  have hfunX : (fun x => AVenhance.spaceGrad
      (fun y => u y * φx y) x 1 * u x) =
      (fun x => (u x * φx x) * uy x + u x ^ 2 * φxy x) := by
    funext x
    rw [ThetaEnergy.theta_spaceGrad_mul 1 (hu.differentiable (by simp) x)
      (hφx.differentiable (by simp) x)]
    dsimp [uy, φxy]
    ring
  have hfunY : (fun x => AVenhance.spaceGrad
      (fun y => u y * φy y) x 0 * u x) =
      (fun x => (u x * φy x) * ux x + u x ^ 2 * φyx x) := by
    funext x
    rw [ThetaEnergy.theta_spaceGrad_mul 0 (hu.differentiable (by simp) x)
      (hφy.differentiable (by simp) x)]
    dsimp [ux, φyx]
    ring
  have hArel : A = -(A + P) := by
    calc
      A = -∫ x in AVenhance.unitCube,
          AVenhance.spaceGrad (fun y => u y * φx y) x 1 * u x := by
        dsimp [A]
        exact hpartsX
      _ = -(A + P) := by
        rw [hfunX, integral_add hIntA hIntP]
  have hBrel : B = -(B + Q) := by
    calc
      B = -∫ x in AVenhance.unitCube,
          AVenhance.spaceGrad (fun y => u y * φy y) x 0 * u x := by
        dsimp [B]
        exact hpartsY
      _ = -(B + Q) := by
        rw [hfunY, integral_add hIntB hIntQ]
  have hPQ : P = Q := by
    dsimp [P, Q]
    apply integral_congr_ae
    filter_upwards with x
    exact congrArg (fun z : ℝ => u x ^ 2 * z) (ThetaEnergy.theta_mixed_partial_commute hφ x)
  have hAB : A = B := by
    have hA : 2 * A = -P := by linarith [hArel]
    have hB : 2 * B = -Q := by linarith [hBrel]
    linarith
  have hpoint (x : Vec 2) :
      u x * vecDot (AVenhance.streamVel (fun _ => φ) 0 x)
          (AVenhance.spaceGrad u x) =
        (u x * φx x) * uy x - (u x * φy x) * ux x := by
    have hb := ThetaEnergy.theta_streamVel_components (φ := fun _ => φ) (t := 0) (x := x)
    simp [vecDot, Fin.sum_univ_two, φx, φy, ux, uy, hb.1, hb.2]
    ring
  calc
    (∫ x in AVenhance.unitCube,
      u x * vecDot (AVenhance.streamVel (fun _ => φ) 0 x)
        (AVenhance.spaceGrad u x)) = A - B := by
      rw [show (fun x => u x * vecDot
          (AVenhance.streamVel (fun _ => φ) 0 x) (AVenhance.spaceGrad u x)) =
        (fun x => (u x * φx x) * uy x - (u x * φy x) * ux x) from funext hpoint,
        integral_sub hIntA hIntB]
    _ = 0 := sub_eq_zero.mpr hAB

/-- Periodic integration by parts for the divergence of a smooth vector field. -/
theorem theta_divergence_pairing
    {u : Vec 2 → ℝ} {F : Vec 2 → Vec 2}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huper : AVenhance.IsZ2Periodic u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFper : AVenhance.IsZ2Periodic F) :
    (∫ x in AVenhance.unitCube, u x * AVenhance.vecDiv F x) =
      -(∫ x in AVenhance.unitCube,
        vecDot (AVenhance.spaceGrad u x) (F x)) := by
  have huGrad := ThetaEnergy.theta_spaceGrad_contDiff hu
  have hu0 : ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad u x 0) :=
    contDiff_pi.mp huGrad 0
  have hu1 : ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad u x 1) :=
    contDiff_pi.mp huGrad 1
  have hF0 : ContDiff ℝ (⊤ : ℕ∞) (fun x => F x 0) := contDiff_pi.mp hF 0
  have hF1 : ContDiff ℝ (⊤ : ℕ∞) (fun x => F x 1) := contDiff_pi.mp hF 1
  have hFper0 : AVenhance.IsZ2Periodic (fun x => F x 0) := fun k x =>
    congrArg (fun V : Vec 2 => V 0) (hFper k x)
  have hFper1 : AVenhance.IsZ2Periodic (fun x => F x 1) := fun k x =>
    congrArg (fun V : Vec 2 => V 1) (hFper k x)
  have hcoord0 := ThetaEnergy.theta_integral_unitCube_coord_ibp hu hF0 huper hFper0 (0 : Fin 2)
  have hcoord1 := ThetaEnergy.theta_integral_unitCube_coord_ibp hu hF1 huper hFper1 (1 : Fin 2)
  have hleft0 : IntegrableOn
      (fun x => u x * AVenhance.spaceGrad (fun y => F y 0) x 0)
      AVenhance.unitCube := ThetaEnergy.theta_integrableOn_unitCube <|
        hu.continuous.mul (ThetaEnergy.theta_continuous_spaceGrad_coord hF0 0)
  have hleft1 : IntegrableOn
      (fun x => u x * AVenhance.spaceGrad (fun y => F y 1) x 1)
      AVenhance.unitCube := ThetaEnergy.theta_integrableOn_unitCube <|
        hu.continuous.mul (ThetaEnergy.theta_continuous_spaceGrad_coord hF1 1)
  have hright0 : IntegrableOn
      (fun x => AVenhance.spaceGrad u x 0 * F x 0) AVenhance.unitCube :=
    ThetaEnergy.theta_integrableOn_unitCube (hu0.continuous.mul hF0.continuous)
  have hright1 : IntegrableOn
      (fun x => AVenhance.spaceGrad u x 1 * F x 1) AVenhance.unitCube :=
    ThetaEnergy.theta_integrableOn_unitCube (hu1.continuous.mul hF1.continuous)
  have hleft : (fun x => u x * AVenhance.vecDiv F x) = fun x =>
      u x * AVenhance.spaceGrad (fun y => F y 0) x 0 +
        u x * AVenhance.spaceGrad (fun y => F y 1) x 1 := by
    funext x
    simp [AVenhance.vecDiv, Fin.sum_univ_two]
    ring
  have hright : (fun x => vecDot (AVenhance.spaceGrad u x) (F x)) = fun x =>
      AVenhance.spaceGrad u x 0 * F x 0 + AVenhance.spaceGrad u x 1 * F x 1 := by
    funext x
    simp [vecDot, Fin.sum_univ_two]
  rw [hleft, integral_add hleft0 hleft1, hright, integral_add hright0 hright1]
  rw [hcoord0, hcoord1]
  ring

/-- A smooth periodic forced equation in divergence form has the usual
instantaneous energy pairing. The forcing enters through its flux, as in the
commutator equation for differentiated θ. -/
theorem theta_forced_classical_energy_pairing
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ}
    {u : ℝ → Vec 2 → ℝ} {F : ℝ → Vec 2 → Vec 2}
    (hφ : AVenhance.IsAdmissibleStream φ)
    {t : ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (u t))
    (huper : AVenhance.IsZ2Periodic (u t))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F t))
    (hFper : AVenhance.IsZ2Periodic (F t))
    (hpde : ∀ x, deriv (fun s => u s x) t -
      κ * AVenhance.spaceLap (u t) x +
      vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (u t) x) =
      AVenhance.vecDiv (F t) x) :
    (∫ x in AVenhance.unitCube,
      u t x * deriv (fun s => u s x) t) +
      κ * (∫ x in AVenhance.unitCube,
        vecNormSq (AVenhance.spaceGrad (u t) x)) =
      -(∫ x in AVenhance.unitCube,
        vecDot (AVenhance.spaceGrad (u t) x) (F t x)) := by
  have hφslice : ContDiff ℝ (⊤ : ℕ∞) (φ t) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
    convert hφ.1.comp hmap using 1
    ext x
    rfl
  have hφper : AVenhance.IsZ2Periodic (φ t) := by
    intro k x
    simpa using hφ.2 0 k t x
  have hdrift := theta_stream_drift_pairing_zero hφslice hφper hu huper
  have hlap := theta_laplacian_pairing hu huper
  have hgrad := ThetaEnergy.theta_spaceGrad_contDiff hu
  have hgrad0 := contDiff_pi.mp hgrad 0
  have hgrad1 := contDiff_pi.mp hgrad 1
  have hF0 := contDiff_pi.mp hF 0
  have hF1 := contDiff_pi.mp hF 1
  have hdotFormula :
      (fun x => vecDot (AVenhance.streamVel φ t x)
        (AVenhance.spaceGrad (u t) x)) =
      (fun x => AVenhance.streamVel φ t x 0 * AVenhance.spaceGrad (u t) x 0 +
        AVenhance.streamVel φ t x 1 * AVenhance.spaceGrad (u t) x 1) := by
    funext x
    simp [vecDot, Fin.sum_univ_two]
  have hdivFormula :
      (fun x => AVenhance.vecDiv (F t) x) =
      (fun x => AVenhance.spaceGrad (fun y => F t y 0) x 0 +
        AVenhance.spaceGrad (fun y => F t y 1) x 1) := by
    funext x
    simp [AVenhance.vecDiv, Fin.sum_univ_two]
  have hdotCont : Continuous (fun x => vecDot (AVenhance.streamVel φ t x)
      (AVenhance.spaceGrad (u t) x)) := by
    have hv0 : Continuous (fun x => AVenhance.streamVel φ t x 0) := by
      have hv : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel φ t) := by
        apply contDiff_pi.2
        intro i
        fin_cases i
        · have heq : (fun x => AVenhance.streamVel φ t x 0) =
              fun x => -AVenhance.spaceGrad (φ t) x 1 := by
            funext x
            exact (ThetaEnergy.theta_streamVel_components (φ := φ) (t := t) (x := x)).1
          change ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.streamVel φ t x 0)
          rw [heq]
          exact (contDiff_pi.mp (ThetaEnergy.theta_spaceGrad_contDiff hφslice) 1).neg
        · have heq : (fun x => AVenhance.streamVel φ t x 1) =
              fun x => AVenhance.spaceGrad (φ t) x 0 := by
            funext x
            exact (ThetaEnergy.theta_streamVel_components (φ := φ) (t := t) (x := x)).2
          change ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.streamVel φ t x 1)
          rw [heq]
          exact contDiff_pi.mp (ThetaEnergy.theta_spaceGrad_contDiff hφslice) 0
      exact (continuous_apply (0 : Fin 2)).comp hv.continuous
    have hv1 : Continuous (fun x => AVenhance.streamVel φ t x 1) := by
      have hv : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel φ t) := by
        apply contDiff_pi.2
        intro i
        fin_cases i
        · have heq : (fun x => AVenhance.streamVel φ t x 0) =
              fun x => -AVenhance.spaceGrad (φ t) x 1 := by
            funext x
            exact (ThetaEnergy.theta_streamVel_components (φ := φ) (t := t) (x := x)).1
          change ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.streamVel φ t x 0)
          rw [heq]
          exact (contDiff_pi.mp (ThetaEnergy.theta_spaceGrad_contDiff hφslice) 1).neg
        · have heq : (fun x => AVenhance.streamVel φ t x 1) =
              fun x => AVenhance.spaceGrad (φ t) x 0 := by
            funext x
            exact (ThetaEnergy.theta_streamVel_components (φ := φ) (t := t) (x := x)).2
          change ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.streamVel φ t x 1)
          rw [heq]
          exact contDiff_pi.mp (ThetaEnergy.theta_spaceGrad_contDiff hφslice) 0
      exact (continuous_apply (1 : Fin 2)).comp hv.continuous
    rw [hdotFormula]
    exact
      (hv0.mul ((continuous_apply (0 : Fin 2)).comp hgrad.continuous)).add
        (hv1.mul ((continuous_apply (1 : Fin 2)).comp hgrad.continuous))
  have hdivCont : Continuous (fun x => AVenhance.vecDiv (F t) x) := by
    rw [hdivFormula]
    exact (ThetaEnergy.theta_continuous_spaceGrad_coord hF0 0).add
      (ThetaEnergy.theta_continuous_spaceGrad_coord hF1 1)
  have hsourceCont : Continuous (fun x =>
      u t x * AVenhance.vecDiv (F t) x) := hu.continuous.mul hdivCont
  have hleft0 : IntegrableOn
      (fun x => u t x * deriv (fun s => u s x) t) AVenhance.unitCube := by
    have hsumCont : Continuous (fun x =>
        κ * (u t x * AVenhance.spaceLap (u t) x) -
          u t x * vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (u t) x) +
          u t x * AVenhance.vecDiv (F t) x) := by
      exact ((continuous_const.mul (hu.continuous.mul
        (by
          have hlapCont : Continuous (AVenhance.spaceLap (u t)) := by
            unfold AVenhance.spaceLap
            apply continuous_finsetSum
            intro i hi
            exact ThetaEnergy.theta_continuous_spaceGrad_coord
              (contDiff_pi.mp hgrad i) i
          exact hlapCont))).sub (hu.continuous.mul hdotCont)).add hsourceCont
    have heq : (fun x => u t x * deriv (fun s => u s x) t) = fun x =>
        κ * (u t x * AVenhance.spaceLap (u t) x) -
          u t x * vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (u t) x) +
          u t x * AVenhance.vecDiv (F t) x := by
      funext x
      have h := hpde x
      linear_combination (u t x) * h
    rw [heq]
    exact ThetaEnergy.theta_integrableOn_unitCube hsumCont
  have hgradSqInt : IntegrableOn
      (fun x => vecNormSq (AVenhance.spaceGrad (u t) x)) AVenhance.unitCube := by
    have hnorm : (fun x => vecNormSq (AVenhance.spaceGrad (u t) x)) = fun x =>
        (AVenhance.spaceGrad (u t) x 0) ^ 2 +
          (AVenhance.spaceGrad (u t) x 1) ^ 2 := by
      funext x
      simp [vecNormSq, vecDot, Fin.sum_univ_two, pow_two]
    rw [hnorm]
    exact (ThetaEnergy.theta_integrableOn_unitCube (hgrad0.continuous.pow 2)).add
      (ThetaEnergy.theta_integrableOn_unitCube (hgrad1.continuous.pow 2))
  have hfluxInt : IntegrableOn
      (fun x => vecDot (AVenhance.spaceGrad (u t) x) (F t x)) AVenhance.unitCube := by
    have hdot : Continuous (fun x =>
        AVenhance.spaceGrad (u t) x 0 * F t x 0 +
          AVenhance.spaceGrad (u t) x 1 * F t x 1) := by
      exact ((continuous_apply (0 : Fin 2)).comp hgrad.continuous).mul
          ((continuous_apply (0 : Fin 2)).comp hF.continuous) |>.add
        (((continuous_apply (1 : Fin 2)).comp hgrad.continuous).mul
          ((continuous_apply (1 : Fin 2)).comp hF.continuous))
    have heq : (fun x => vecDot (AVenhance.spaceGrad (u t) x) (F t x)) =
        fun x => AVenhance.spaceGrad (u t) x 0 * F t x 0 +
          AVenhance.spaceGrad (u t) x 1 * F t x 1 := by
      funext x
      simp [vecDot, Fin.sum_univ_two]
    rw [heq]
    exact ThetaEnergy.theta_integrableOn_unitCube hdot
  have hsourceInt : IntegrableOn
      (fun x => u t x * AVenhance.vecDiv (F t) x) AVenhance.unitCube :=
    ThetaEnergy.theta_integrableOn_unitCube hsourceCont
  have hlapCont : Continuous (AVenhance.spaceLap (u t)) := by
    unfold AVenhance.spaceLap
    apply continuous_finsetSum
    intro i hi
    exact ThetaEnergy.theta_continuous_spaceGrad_coord (contDiff_pi.mp hgrad i) i
  have hlapInt : IntegrableOn
      (fun x => u t x * AVenhance.spaceLap (u t) x) AVenhance.unitCube :=
    ThetaEnergy.theta_integrableOn_unitCube (hu.continuous.mul hlapCont)
  have hdriftInt : IntegrableOn
      (fun x => u t x * vecDot (AVenhance.streamVel φ t x)
        (AVenhance.spaceGrad (u t) x)) AVenhance.unitCube :=
    ThetaEnergy.theta_integrableOn_unitCube (hu.continuous.mul hdotCont)
  have hfirstInt : IntegrableOn
      (fun x => κ * (u t x * AVenhance.spaceLap (u t) x) -
        u t x * vecDot (AVenhance.streamVel φ t x)
          (AVenhance.spaceGrad (u t) x)) AVenhance.unitCube := by
    have h := (hlapInt.const_mul κ).sub hdriftInt
    exact IntegrableOn.congr_fun h (fun x _ => rfl)
      ThetaEnergy.theta_measurableSet_unitCube
  have hpoint (x : Vec 2) :
      u t x * deriv (fun s => u s x) t =
        κ * (u t x * AVenhance.spaceLap (u t) x) -
          u t x * vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (u t) x) +
          u t x * AVenhance.vecDiv (F t) x := by
    have h := hpde x
    linear_combination (u t x) * h
  have hbalance : (∫ x in AVenhance.unitCube,
      u t x * deriv (fun s => u s x) t) =
        κ * (∫ x in AVenhance.unitCube, u t x * AVenhance.spaceLap (u t) x) -
          (∫ x in AVenhance.unitCube,
            u t x * vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (u t) x)) +
          ∫ x in AVenhance.unitCube, u t x * AVenhance.vecDiv (F t) x := by
    calc
      _ = ∫ x in AVenhance.unitCube,
          (κ * (u t x * AVenhance.spaceLap (u t) x) -
            u t x * vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (u t) x) +
            u t x * AVenhance.vecDiv (F t) x) := by
              apply integral_congr_ae
              filter_upwards with x
              exact hpoint x
      _ = _ := by
        calc
          _ = ∫ x in AVenhance.unitCube,
              ((fun y => κ * (u t y * AVenhance.spaceLap (u t) y) -
                  u t y * vecDot (AVenhance.streamVel φ t y)
                    (AVenhance.spaceGrad (u t) y)) x +
                (fun y => u t y * AVenhance.vecDiv (F t) y) x) := rfl
          _ = (∫ x in AVenhance.unitCube,
                κ * (u t x * AVenhance.spaceLap (u t) x) -
                  u t x * vecDot (AVenhance.streamVel φ t x)
                    (AVenhance.spaceGrad (u t) x)) +
              ∫ x in AVenhance.unitCube, u t x * AVenhance.vecDiv (F t) x :=
                integral_add hfirstInt hsourceInt
          _ = _ := by
            rw [integral_sub (hlapInt.const_mul κ) hdriftInt]
            rw [integral_const_mul]
  have hdivPair := theta_divergence_pairing hu huper hF hFper
  have hdrift' : (∫ x in AVenhance.unitCube,
      u t x * vecDot (AVenhance.streamVel φ t x)
        (AVenhance.spaceGrad (u t) x)) = 0 := by
    simpa [AVenhance.streamVel] using hdrift
  rw [hlap, hdrift', hdivPair] at hbalance
  linarith

/-- The ordered derivative with first direction `i 0` is the corresponding
component of the gradient of the derivative in the remaining directions. -/
theorem ordered_derivative_eq_gradient_component {n : ℕ}
    {f : Vec 2 → ℝ} {x : Vec 2} (i : Fin (n + 1) → Fin 2)
    (h : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x) :
    iteratedFDeriv ℝ (n + 1) f x (fun j => basisVec (i j)) =
      AVenhance.spaceGrad
        (fun y => iteratedFDeriv ℝ n f y (fun j => basisVec (i j.succ))) x (i 0) := by
  rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' h]
  rfl

end AVenhance.Infra.Section4
