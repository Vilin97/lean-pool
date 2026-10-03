/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaEnergy

/-! Forced torus energy calculations for the actual classical increments. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def IteratesEnergy.iterateClosedCell : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem IteratesEnergy.iterateClosedCell_compact : IsCompact IteratesEnergy.iterateClosedCell := by
  simpa [IteratesEnergy.iterateClosedCell] using (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem IteratesEnergy.iterateUnitCube_subset_closedCell : AVenhance.unitCube ⊆
    IteratesEnergy.iterateClosedCell := by
  intro x hx
  change (∀ i ∈ Set.univ, x i ∈ Set.Ioo (0 : ℝ) 1) at hx
  change (∀ i ∈ Set.univ, x i ∈ Set.Icc (0 : ℝ) 1)
  intro i hi
  exact ⟨le_of_lt (hx i hi).1, le_of_lt (hx i hi).2⟩

theorem IteratesEnergy.iterate_integrableOn_unitCube {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f AVenhance.unitCube :=
  (hf.continuousOn.integrableOn_compact IteratesEnergy.iterateClosedCell_compact).mono_set
    IteratesEnergy.iterateUnitCube_subset_closedCell

theorem IteratesEnergy.iterate_measurableSet_unitCube : MeasurableSet AVenhance.unitCube := by
  change MeasurableSet (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1)
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

theorem IteratesEnergy.iterateUnitCell_subset_closedCell :
    AVenhance.Infra.Torus.unitCell 2 ⊆ IteratesEnergy.iterateClosedCell := by
  intro x hx
  simp only [AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt,
    Set.mem_ofPred_eq, zero_add] at hx
  simp only [IteratesEnergy.iterateClosedCell, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, (hx i).2⟩

theorem IteratesEnergy.iterate_integrableOn_unitCell {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f (AVenhance.Infra.Torus.unitCell 2) :=
  (hf.continuousOn.integrableOn_compact IteratesEnergy.iterateClosedCell_compact).mono_set
    IteratesEnergy.iterateUnitCell_subset_closedCell

theorem IteratesEnergy.iterate_realToComplex_periodic {f : Vec 2 → ℝ}
    (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.Infra.Torus.IsZdPeriodic (AVenhance.Infra.Torus.realToComplex f) := by
  intro k x
  exact congrArg (fun y : ℝ => (y : ℂ))
    ((AVenhance.Infra.Torus.isZdPeriodic_iff_frozen f).2 hper k x)

theorem IteratesEnergy.iterate_continuous_spaceGrad_coord {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    Continuous (fun x => AVenhance.spaceGrad f x i) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem IteratesEnergy.iterate_integral_unitCube_coord_ibp {f g : Vec 2 → ℝ}
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
    (IteratesEnergy.iterate_realToComplex_periodic hpf)
        (IteratesEnergy.iterate_realToComplex_periodic hpg)
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
    IteratesEnergy.iterate_integrableOn_unitCell (hf.continuous.mul
      (IteratesEnergy.iterate_continuous_spaceGrad_coord hg i))
  have hrightInt : IntegrableOn
      (fun x : Vec 2 => AVenhance.spaceGrad f x i * g x)
      (AVenhance.Infra.Torus.unitCell 2) :=
    IteratesEnergy.iterate_integrableOn_unitCell
        ((IteratesEnergy.iterate_continuous_spaceGrad_coord hf i).mul hg.continuous)
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

theorem IteratesEnergy.iterate_spaceGrad_periodic {f : Vec 2 → ℝ}
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

theorem IteratesEnergy.iterate_spaceGrad_contDiff {f : Vec 2 → ℝ}
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

theorem IteratesEnergy.iterate_mixed_partial_commute {f : Vec 2 → ℝ}
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

theorem IteratesEnergy.iterate_spaceGrad_mul {f g : Vec 2 → ℝ} {x : Vec 2} (i : Fin 2)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    AVenhance.spaceGrad (fun y => f y * g y) x i =
      AVenhance.spaceGrad f x i * g x + f x * AVenhance.spaceGrad g x i := by
  change fderiv ℝ (fun y => f y * g y) x (basisVec i) = _
  rw [fderiv_fun_mul hf hg]
  simp [AVenhance.spaceGrad]
  ring

theorem IteratesEnergy.iterate_streamVel_components {φ : ℝ → Vec 2 → ℝ} {t : ℝ} {x : Vec 2} :
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

/-- Instantaneous energy identity with the actual forcing retained. -/
theorem iterate_classical_energy_pairing
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {F : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ)
    (hsol : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ
      F θ₀ θ)
    {t : ℝ} (ht : 0 < t) (hF : Continuous (F t)) :
    (∫ x in AVenhance.unitCube,
      θ t x * deriv (fun s => θ s x) t) +
      κ * (∫ x in AVenhance.unitCube,
        vecNormSq (AVenhance.spaceGrad (θ t) x)) =
      ∫ x in AVenhance.unitCube, θ t x * F t x := by
  have hθ : ContDiff ℝ (⊤ : ℕ∞) (θ t) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
    have hcomp := hsol.1.comp_contDiff hmap
      (fun x => ⟨ht.le, Set.mem_univ x⟩)
    convert hcomp using 1
    ext x
    rfl
  have hθper : AVenhance.IsZ2Periodic (θ t) := hsol.2.1 t ht.le
  have hφslice : ContDiff ℝ (⊤ : ℕ∞) (φ t) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
    convert hφ.1.comp hmap using 1
    ext x
    rfl
  have hφper : AVenhance.IsZ2Periodic (φ t) := by
    intro k x
    have h := hφ.2 0 k t x
    simpa using h
  have hlap := theta_laplacian_pairing hθ hθper
  have hdrift := theta_stream_drift_pairing_zero hφslice hφper hθ hθper
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceGrad (θ t)) :=
    IteratesEnergy.iterate_spaceGrad_contDiff hθ
  have hθ0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad (θ t) x 0) := contDiff_pi.mp hgrad 0
  have hθ1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad (θ t) x 1) := contDiff_pi.mp hgrad 1
  have hθ00 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad
        (fun y => AVenhance.spaceGrad (θ t) y 0) x 0) :=
    contDiff_pi.mp (IteratesEnergy.iterate_spaceGrad_contDiff hθ0) 0
  have hθ11 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad
        (fun y => AVenhance.spaceGrad (θ t) y 1) x 1) :=
    contDiff_pi.mp (IteratesEnergy.iterate_spaceGrad_contDiff hθ1) 1
  have hlapForm : AVenhance.spaceLap (θ t) = fun x =>
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad (θ t) y 0) x 0 +
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad (θ t) y 1) x 1 := by
    funext x
    simp [AVenhance.spaceLap, Fin.sum_univ_two]
  have hlapSmooth : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceLap (θ t)) := by
    rw [hlapForm]
    exact hθ00.add hθ11
  have hvel : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel φ t) := by
    have hvel0 : (fun x => AVenhance.streamVel φ t x 0) =
        fun x => -AVenhance.spaceGrad (φ t) x 1 := by
      funext x
      exact (IteratesEnergy.iterate_streamVel_components (φ := φ) (t := t) (x := x)).1
    have hvel1 : (fun x => AVenhance.streamVel φ t x 1) =
        fun x => AVenhance.spaceGrad (φ t) x 0 := by
      funext x
      exact (IteratesEnergy.iterate_streamVel_components (φ := φ) (t := t) (x := x)).2
    apply contDiff_pi.2
    intro i
    fin_cases i
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.streamVel φ t x 0)
      rw [hvel0]
      exact (contDiff_pi.mp (IteratesEnergy.iterate_spaceGrad_contDiff hφslice) 1).neg
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.streamVel φ t x 1)
      rw [hvel1]
      exact contDiff_pi.mp (IteratesEnergy.iterate_spaceGrad_contDiff hφslice) 0
  have hvel0c : Continuous (fun x => AVenhance.streamVel φ t x 0) :=
    (continuous_apply (0 : Fin 2)).comp hvel.continuous
  have hvel1c : Continuous (fun x => AVenhance.streamVel φ t x 1) :=
    (continuous_apply (1 : Fin 2)).comp hvel.continuous
  have hgrad0c : Continuous (fun x => AVenhance.spaceGrad (θ t) x 0) :=
    (continuous_apply (0 : Fin 2)).comp hgrad.continuous
  have hgrad1c : Continuous (fun x => AVenhance.spaceGrad (θ t) x 1) :=
    (continuous_apply (1 : Fin 2)).comp hgrad.continuous
  have hdot : Continuous (fun x => vecDot (AVenhance.streamVel φ t x)
      (AVenhance.spaceGrad (θ t) x)) := by
    have hdotFun : (fun x => vecDot (AVenhance.streamVel φ t x)
        (AVenhance.spaceGrad (θ t) x)) =
        (fun x => AVenhance.streamVel φ t x 0 * AVenhance.spaceGrad (θ t) x 0 +
          AVenhance.streamVel φ t x 1 * AVenhance.spaceGrad (θ t) x 1) := by
      funext x
      simp [vecDot, Fin.sum_univ_two]
    rw [hdotFun]
    exact hvel0c.mul hgrad0c |>.add (hvel1c.mul hgrad1c)
  have hlapInt : IntegrableOn
      (fun x => θ t x * AVenhance.spaceLap (θ t) x) AVenhance.unitCube :=
    IteratesEnergy.iterate_integrableOn_unitCube (hθ.continuous.mul hlapSmooth.continuous)
  have hdriftInt : IntegrableOn
      (fun x => θ t x * vecDot (AVenhance.streamVel φ t x)
        (AVenhance.spaceGrad (θ t) x)) AVenhance.unitCube :=
    IteratesEnergy.iterate_integrableOn_unitCube (hθ.continuous.mul hdot)
  have hgradInt : IntegrableOn
      (fun x => vecNormSq (AVenhance.spaceGrad (θ t) x)) AVenhance.unitCube := by
    have hgradSq : (fun x => vecNormSq (AVenhance.spaceGrad (θ t) x)) =
        fun x => (AVenhance.spaceGrad (θ t) x 0) ^ 2 +
          (AVenhance.spaceGrad (θ t) x 1) ^ 2 := by
      funext x
      simp [vecNormSq, vecDot, Fin.sum_univ_two, pow_two]
    rw [hgradSq]
    exact (IteratesEnergy.iterate_integrableOn_unitCube (hgrad0c.pow 2)).add
      (IteratesEnergy.iterate_integrableOn_unitCube (hgrad1c.pow 2))
  have hforceInt := IteratesEnergy.iterate_integrableOn_unitCube (hθ.continuous.mul hF)
  have htimeEq (x : Vec 2) :
      θ t x * deriv (fun s => θ s x) t =
        κ * (θ t x * AVenhance.spaceLap (θ t) x) -
          θ t x * vecDot (AVenhance.streamVel φ t x)
            (AVenhance.spaceGrad (θ t) x) + θ t x * F t x := by
    have hpde := hsol.2.2.2 t ht x
    have hpde' : deriv (fun s => θ s x) t -
        κ * AVenhance.spaceLap (θ t) x +
        vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (θ t) x) = F t x := by
      simpa [AVenhance.advDiffOp] using hpde
    have hmul := congrArg (fun z : ℝ => θ t x * z) hpde'
    linear_combination hmul
  have htimeInt : IntegrableOn
      (fun x => θ t x * deriv (fun s => θ s x) t) AVenhance.unitCube := by
    have hRhs := ((hlapInt.const_mul κ).sub hdriftInt).add hforceInt
    exact IntegrableOn.congr_fun hRhs
      (fun x hx => (htimeEq x).symm)
      IteratesEnergy.iterate_measurableSet_unitCube
  have htimeIntegral :
      (∫ x in AVenhance.unitCube, θ t x * deriv (fun s => θ s x) t) =
        κ * (∫ x in AVenhance.unitCube,
          θ t x * AVenhance.spaceLap (θ t) x) -
          (∫ x in AVenhance.unitCube,
            θ t x * vecDot (AVenhance.streamVel φ t x)
              (AVenhance.spaceGrad (θ t) x)) +
          (∫ x in AVenhance.unitCube, θ t x * F t x) := by
    calc
      _ = ∫ x in AVenhance.unitCube,
          (κ * (θ t x * AVenhance.spaceLap (θ t) x) -
            θ t x * vecDot (AVenhance.streamVel φ t x)
              (AVenhance.spaceGrad (θ t) x) + θ t x * F t x) := by
          apply integral_congr_ae
          filter_upwards with x
          exact htimeEq x
      _ = κ * (∫ x in AVenhance.unitCube,
            θ t x * AVenhance.spaceLap (θ t) x) -
          (∫ x in AVenhance.unitCube,
            θ t x * vecDot (AVenhance.streamVel φ t x)
              (AVenhance.spaceGrad (θ t) x)) +
              (∫ x in AVenhance.unitCube, θ t x * F t x) := by
          have he := integral_add ((hlapInt.const_mul κ).sub hdriftInt) hforceInt
          change (∫ x in AVenhance.unitCube, κ * (θ t x * AVenhance.spaceLap (θ t) x) - θ t x *
              vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (θ t) x) + θ t x * F t x) =
              _ at he
          have hs := integral_sub (hlapInt.const_mul κ) hdriftInt
          change (∫ x in AVenhance.unitCube, κ * (θ t x * AVenhance.spaceLap (θ t) x) - θ t x *
              vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (θ t) x)) = _ at hs
          dsimp only [Pi.sub_apply, Pi.mul_apply] at he
          rw [hs, integral_const_mul] at he
          exact he
  have hdrift' : (∫ x in AVenhance.unitCube,
      θ t x * vecDot (AVenhance.streamVel φ t x)
        (AVenhance.spaceGrad (θ t) x)) = 0 := by
    simpa [AVenhance.streamVel] using hdrift
  rw [htimeIntegral, hlap, hdrift']
  ring

/-- Torus integration by parts for a smooth periodic vector forcing. -/
theorem iterate_divergence_pairing {u : Vec 2 → ℝ} {H : Vec 2 → Vec 2}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : AVenhance.IsZ2Periodic u)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHp : AVenhance.IsZ2Periodic H) :
    (∫ x in AVenhance.unitCube, u x * AVenhance.vecDiv H x) =
      -∫ x in AVenhance.unitCube, vecDot (AVenhance.spaceGrad u x) (H x) := by
  have hc (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => H x i) := contDiff_pi.mp hH i
  have hper (i : Fin 2) : AVenhance.IsZ2Periodic (fun x => H x i) := by
    intro k x
    exact congrFun (hHp k x) i
  have hleftInt (i : Fin 2) : IntegrableOn (fun x => u x *
      AVenhance.spaceGrad (fun y => H y i) x i) AVenhance.unitCube :=
    IteratesEnergy.iterate_integrableOn_unitCube (hu.continuous.mul
        (IteratesEnergy.iterate_continuous_spaceGrad_coord (hc i) i))
  have hrightInt (i : Fin 2) : IntegrableOn (fun x =>
      AVenhance.spaceGrad u x i * H x i) AVenhance.unitCube :=
    IteratesEnergy.iterate_integrableOn_unitCube
        ((IteratesEnergy.iterate_continuous_spaceGrad_coord hu i).mul (hc i).continuous)
  simp only [AVenhance.vecDiv, vecDot, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hleftInt i),
    integral_finsetSum Finset.univ (fun i _ => hrightInt i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact IteratesEnergy.iterate_integral_unitCube_coord_ibp hu (hc i) hup (hper i) i

theorem IteratesEnergy.iterate_young_scalar {κ a b : ℝ} (hκ : 0 < κ) :
    -(a * b) ≤ κ / 2 * a ^ 2 + (2 * κ)⁻¹ * b ^ 2 := by
  apply (mul_le_mul_iff_of_pos_left (by positivity : 0 < 2 * κ)).mp
  have heq : 2 * κ * (κ / 2 * a ^ 2 + (2 * κ)⁻¹ * b ^ 2) = κ ^ 2 * a ^ 2 + b ^ 2 := by
    field_simp
  rw [heq]
  nlinarith only [sq_nonneg (κ * a + b)]

/-- Pointwise forcing control with the dissipation coefficient retained. -/
theorem iterate_young_vector {κ : ℝ} (hκ : 0 < κ) (a b : Vec 2) :
    -vecDot a b ≤ κ / 2 * vecNormSq a + (2 * κ)⁻¹ * vecNormSq b := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    IteratesEnergy.iterate_young_scalar (a := a i) (b := b i) hκ)
  simpa only [vecDot, vecNormSq, ← Finset.sum_neg_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← pow_two] using h

/-- Entrywise coefficient control bounds the actual vector flux in dimension two. -/
theorem iterate_matrix_flux_bound {A : Matrix (Fin 2) (Fin 2) ℝ} {D : ℝ}
    (hA : ∀ i j, |A i j| ≤ D) (v : Vec 2) :
    vecNormSq (A.mulVec v) ≤ 4 * D ^ 2 * vecNormSq v := by
  have hsq (i j : Fin 2) : (A i j) ^ 2 ≤ D ^ 2 := by
    have hD : 0 ≤ D := (abs_nonneg (A i j)).trans (hA i j)
    have ha := (abs_le.mp (hA i j))
    nlinarith only [ha.1, ha.2, hD, sq_nonneg (D - A i j),
      sq_nonneg (D + A i j)]
  have row (i : Fin 2) : (A.mulVec v i) ^ 2 ≤
      2 * D ^ 2 * (v 0 ^ 2 + v 1 ^ 2) := by
    have h0 := mul_le_mul_of_nonneg_right (hsq i 0) (sq_nonneg (v 0))
    have h1 := mul_le_mul_of_nonneg_right (hsq i 1) (sq_nonneg (v 1))
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith only [h0, h1, sq_nonneg (A i 0 * v 0 - A i 1 * v 1)]
  have h0 := row 0
  have h1 := row 1
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  nlinarith only [h0, h1]

/-- A matrix forcing pairing can absorb any positive amount of dissipation. -/
theorem iterate_matrix_pairing_abs_bound {ρ D : ℝ} (hρ : 0 < ρ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (a b : Vec 2)
    (hA : ∀ i j, |A i j| ≤ D) :
    |vecDot a (A.mulVec b)| ≤ ρ * vecNormSq a + D ^ 2 / ρ * vecNormSq b := by
  have hf := iterate_matrix_flux_bound hA b
  have hscale : (2 * (2 * ρ))⁻¹ * (4 * D ^ 2 * vecNormSq b) =
      D ^ 2 / ρ * vecNormSq b := by
    field_simp
    ring
  have hn := iterate_young_vector (by positivity : 0 < 2 * ρ) a (A.mulVec b)
  have hp := iterate_young_vector (by positivity : 0 < 2 * ρ) (-a) (A.mulVec b)
  have hneg : vecNormSq (-a) = vecNormSq a := by
    simp only [vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg]
  have hdot : vecDot (-a) (A.mulVec b) = -vecDot a (A.mulVec b) := by
    simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [hneg, hdot, neg_neg] at hp
  have hf' := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ (2 * (2 * ρ))⁻¹)
  rw [hscale] at hf'
  apply abs_le.mpr
  constructor <;> linarith only [hn, hp, hf']

theorem IteratesEnergy.iterate_pair_continuous
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {a b : Vec 2 → Vec 2}
    (hA : Continuous A) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => vecDot (a x) ((A x).mulVec (b x))) := by
  unfold vecDot
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul ((continuous_apply i).comp ha)
  simp only [Matrix.mulVec, dotProduct]
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp ((continuous_apply i).comp hA)).mul
    ((continuous_apply j).comp hb)

/-- Transfer the current increment's gradient onto the preceding increment
in the constant-matrix boundary pairing of the primitive argument. -/
theorem iterate_constant_matrix_pairing_ibp
    {u v : Vec 2 → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hup : AVenhance.IsZ2Periodic u) (hvp : AVenhance.IsZ2Periodic v)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    (∫ x in AVenhance.unitCube, vecDot (AVenhance.spaceGrad u x)
      (Q.mulVec (AVenhance.spaceGrad v x))) =
      -(∫ x in AVenhance.unitCube, u x * ∑ i : Fin 2, ∑ j : Fin 2,
        Q i j * AVenhance.spaceGrad (fun y => AVenhance.spaceGrad v y j) x i) := by
  have hg (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad v y j) :=
    contDiff_pi.mp (IteratesEnergy.iterate_spaceGrad_contDiff hv) j
  have hgp (j : Fin 2) : AVenhance.IsZ2Periodic (fun y => AVenhance.spaceGrad v y j) := by
    intro k x
    exact congrFun (IteratesEnergy.iterate_spaceGrad_periodic (hv.of_le (by simp)) hvp k x) j
  have hl (i j : Fin 2) : IntegrableOn (fun x =>
      AVenhance.spaceGrad u x i * (Q i j * AVenhance.spaceGrad v x j)) AVenhance.unitCube :=
    IteratesEnergy.iterate_integrableOn_unitCube
        ((IteratesEnergy.iterate_continuous_spaceGrad_coord hu i).mul
      ((IteratesEnergy.iterate_continuous_spaceGrad_coord hv j).const_mul (Q i j)))
  have hr (i j : Fin 2) : IntegrableOn (fun x => u x *
      (Q i j * AVenhance.spaceGrad (fun y => AVenhance.spaceGrad v y j) x i))
      AVenhance.unitCube := IteratesEnergy.iterate_integrableOn_unitCube (hu.continuous.mul
        ((IteratesEnergy.iterate_continuous_spaceGrad_coord (hg j) i).const_mul (Q i j)))
  have hpair (i j : Fin 2) :
      (∫ x in AVenhance.unitCube, AVenhance.spaceGrad u x i *
        (Q i j * AVenhance.spaceGrad v x j)) =
      -(∫ x in AVenhance.unitCube, u x *
        (Q i j * AVenhance.spaceGrad (fun y => AVenhance.spaceGrad v y j) x i)) := by
    have hi := IteratesEnergy.iterate_integral_unitCube_coord_ibp hu (hg j) hup (hgp j) i
    have hlform : (fun x => AVenhance.spaceGrad u x i * (Q i j * AVenhance.spaceGrad v x j)) =
        (fun x => Q i j * (AVenhance.spaceGrad u x i * AVenhance.spaceGrad v x j)) := by
      funext x
      ring
    have hrform : (fun x => u x * (Q i j *
        AVenhance.spaceGrad (fun y => AVenhance.spaceGrad v y j) x i)) =
        (fun x => Q i j * (u x * AVenhance.spaceGrad (fun y => AVenhance.spaceGrad v y j) x i)) :=
            by
      funext x
      ring
    rw [hlform, hrform, integral_const_mul, integral_const_mul, hi]
    ring
  simp only [vecDot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hl i
      j)),
    integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hr i
        j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hl _ j)]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hr _ j)]
  simp_rw [hpair, Finset.sum_neg_distrib]

/-- The second-derivative contraction costs only the four matrix entries. -/
theorem iterate_matrix_contraction_sq_bound
    (Q H : Matrix (Fin 2) (Fin 2) ℝ) {D : ℝ}
    (hQ : ∀ i j, |Q i j| ≤ D) :
    (∑ i : Fin 2, ∑ j : Fin 2, Q i j * H i j) ^ 2 ≤
      4 * D ^ 2 * (∑ i : Fin 2, ∑ j : Fin 2, H i j ^ 2) := by
  have hD : 0 ≤ D := (abs_nonneg _).trans (hQ 0 0)
  have hs (i j : Fin 2) : Q i j ^ 2 ≤ D ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (Q i j)) hD).2 (hQ i j)
    simpa only [sq_abs] using h
  have row (i : Fin 2) : (∑ j : Fin 2, Q i j * H i j) ^ 2 ≤
      2 * D ^ 2 * (∑ j : Fin 2, H i j ^ 2) := by
    have h0 := mul_le_mul_of_nonneg_right (hs i 0) (sq_nonneg (H i 0))
    have h1 := mul_le_mul_of_nonneg_right (hs i 1) (sq_nonneg (H i 1))
    simp only [Fin.sum_univ_two]
    nlinarith only [h0, h1, sq_nonneg (Q i 0 * H i 0 - Q i 1 * H i 1)]
  have h0 := row 0
  have h1 := row 1
  simp only [Fin.sum_univ_two] at h0 h1 ⊢
  nlinarith only [h0, h1,
    sq_nonneg ((Q 0 0 * H 0 0 + Q 0 1 * H 0 1) - (Q 1 0 * H 1 0 + Q 1 1 * H 1 1))]

theorem IteratesEnergy.iterate_young_abs_scalar {ρ a b : ℝ} (hρ : 0 < ρ) :
    |a * b| ≤ ρ * a ^ 2 + (4 * ρ)⁻¹ * b ^ 2 := by
  have hn := IteratesEnergy.iterate_young_scalar (a := a) (b := b) (by positivity : 0 < 2 * ρ)
  have hp := IteratesEnergy.iterate_young_scalar (a := -a) (b := b) (by positivity : 0 < 2 * ρ)
  simp only [neg_mul, neg_neg, neg_sq] at hp
  apply abs_le.mpr
  have hhalf : 2 * ρ / 2 = ρ := by ring
  have hdouble : 2 * (2 * ρ) = 4 * ρ := by ring
  rw [hhalf, hdouble] at hn hp
  exact ⟨by linarith only [hn], hp⟩

/-- The boundary term from time integration by parts is controlled by
current L² energy and preceding second derivatives, without a pointwise
current-gradient norm. -/
theorem iterate_primitive_boundary_pairing_bound
    {u v : Vec 2 → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hup : AVenhance.IsZ2Periodic u) (hvp : AVenhance.IsZ2Periodic v)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) {ρ D : ℝ} (hρ : 0 < ρ)
    (hQ : ∀ i j, |Q i j| ≤ D) :
    |∫ x in AVenhance.unitCube, vecDot (AVenhance.spaceGrad u x)
      (Q.mulVec (AVenhance.spaceGrad v x))| ≤
      ρ * (∫ x in AVenhance.unitCube, u x ^ 2) + D ^ 2 / ρ *
        (∫ x in AVenhance.unitCube, ∑ i : Fin 2, ∑ j : Fin 2,
          (AVenhance.spaceGrad (fun y => AVenhance.spaceGrad v y j) x i) ^ 2) := by
  let H : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun x i j =>
    AVenhance.spaceGrad (fun y => AVenhance.spaceGrad v y j) x i
  let f := fun x => ∑ i : Fin 2, ∑ j : Fin 2, Q i j * H x i j
  let g := fun x => ∑ i : Fin 2, ∑ j : Fin 2, H x i j ^ 2
  have hH (i j : Fin 2) : Continuous (fun x => H x i j) :=
    IteratesEnergy.iterate_continuous_spaceGrad_coord
      (contDiff_pi.mp (IteratesEnergy.iterate_spaceGrad_contDiff hv) j) i
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (hH i j).const_mul (Q i j)
  have hg : Continuous g := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (hH i j).pow 2
  have hb (x : Vec 2) : |u x * f x| ≤ ρ * u x ^ 2 + D ^ 2 / ρ * g x := by
    have h := IteratesEnergy.iterate_young_abs_scalar (a := u x) (b := f x) hρ
    have hc := iterate_matrix_contraction_sq_bound Q (H x) hQ
    have ht := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (4 * ρ)⁻¹)
    have he : (4 * ρ)⁻¹ * (4 * D ^ 2 * g x) = D ^ 2 / ρ * g x := by
      field_simp
    rw [he] at ht
    exact h.trans (add_le_add_right ht _)
  have hi := integral_mono
    (IteratesEnergy.iterate_integrableOn_unitCube (hu.continuous.mul hf).abs)
    (((IteratesEnergy.iterate_integrableOn_unitCube (hu.continuous.pow 2)).const_mul ρ).add
      ((IteratesEnergy.iterate_integrableOn_unitCube hg).const_mul (D ^ 2 / ρ))) hb
  change (∫ x in AVenhance.unitCube, |u x * f x|) ≤
      (∫ x in AVenhance.unitCube, ρ * u x ^ 2 + D ^ 2 / ρ * g x) at hi
  have hs := integral_add ((IteratesEnergy.iterate_integrableOn_unitCube (hu.continuous.pow
      2)).const_mul ρ)
      ((IteratesEnergy.iterate_integrableOn_unitCube hg).const_mul (D ^ 2 / ρ))
  dsimp only [Pi.pow_apply] at hs
  rw [hs, integral_const_mul, integral_const_mul] at hi
  rw [iterate_constant_matrix_pairing_ibp hu hv hup hvp Q, abs_neg]
  exact abs_integral_le_integral_abs.trans hi

/-- Periodic self-adjointness transfers the two Laplacian derivatives onto
the preceding scalar derivative in the current material equation. -/
theorem iterate_laplacian_pairing_transfer
    {u v : Vec 2 → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hup : AVenhance.IsZ2Periodic u) (hvp : AVenhance.IsZ2Periodic v) :
    (∫ x in AVenhance.unitCube, AVenhance.spaceLap u x * v x) =
      (∫ x in AVenhance.unitCube, u x * AVenhance.spaceLap v x) := by
  have hgu (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad u x i) :=
    contDiff_pi.mp (IteratesEnergy.iterate_spaceGrad_contDiff hu) i
  have hgv (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad v x i) :=
    contDiff_pi.mp (IteratesEnergy.iterate_spaceGrad_contDiff hv) i
  have hpu (i : Fin 2) : AVenhance.IsZ2Periodic (fun x => AVenhance.spaceGrad u x i) := by
    intro k x
    exact congrFun (IteratesEnergy.iterate_spaceGrad_periodic (hu.of_le (by simp)) hup k x) i
  have hpv (i : Fin 2) : AVenhance.IsZ2Periodic (fun x => AVenhance.spaceGrad v x i) := by
    intro k x
    exact congrFun (IteratesEnergy.iterate_spaceGrad_periodic (hv.of_le (by simp)) hvp k x) i
  have hpair (i : Fin 2) :
      (∫ x in AVenhance.unitCube,
        AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y i) x i * v x) =
      (∫ x in AVenhance.unitCube,
        u x * AVenhance.spaceGrad (fun y => AVenhance.spaceGrad v y i) x i) := by
    have hl := IteratesEnergy.iterate_integral_unitCube_coord_ibp hv (hgu i) hvp (hpu i) i
    have hr := IteratesEnergy.iterate_integral_unitCube_coord_ibp hu (hgv i) hup (hpv i) i
    have hcomm : (∫ x in AVenhance.unitCube, AVenhance.spaceGrad v x i * AVenhance.spaceGrad u x
        i) =
        (∫ x in AVenhance.unitCube, AVenhance.spaceGrad u x i * AVenhance.spaceGrad v x i) := by
      apply integral_congr_ae
      filter_upwards with x
      exact mul_comm _ _
    have hcomm' : (∫ x in AVenhance.unitCube,
        AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y i) x i * v x) =
        (∫ x in AVenhance.unitCube, v x *
          AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y i) x i) := by
      apply integral_congr_ae
      filter_upwards with x
      exact mul_comm _ _
    rw [hcomm', hl, hcomm, ← hr]
  have hlint (i : Fin 2) : IntegrableOn (fun x =>
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y i) x i * v x) AVenhance.unitCube :=
    IteratesEnergy.iterate_integrableOn_unitCube
        ((IteratesEnergy.iterate_continuous_spaceGrad_coord (hgu i) i).mul hv.continuous)
  have hrint (i : Fin 2) : IntegrableOn (fun x =>
      u x * AVenhance.spaceGrad (fun y => AVenhance.spaceGrad v y i) x i) AVenhance.unitCube :=
    IteratesEnergy.iterate_integrableOn_unitCube (hu.continuous.mul
        (IteratesEnergy.iterate_continuous_spaceGrad_coord (hgv i) i))
  simp only [AVenhance.spaceLap, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hlint i),
    integral_finsetSum Finset.univ (fun i _ => hrint i)]
  exact Finset.sum_congr rfl (fun i _ => hpair i)

theorem IteratesEnergy.iterate_spaceLap_contDiff {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceLap f) := by
  unfold AVenhance.spaceLap
  apply ContDiff.sum
  intro i _
  exact contDiff_pi.mp (IteratesEnergy.iterate_spaceGrad_contDiff
    (contDiff_pi.mp (IteratesEnergy.iterate_spaceGrad_contDiff hf) i)) i

/-- Constant-matrix Laplacian transfer for vector fields, including the
actual gradient fields in the current material equation. -/
theorem iterate_vector_laplacian_pairing_transfer
    {a b : Vec 2 → Vec 2} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hap : AVenhance.IsZ2Periodic a) (hbp : AVenhance.IsZ2Periodic b)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    (∫ x in AVenhance.unitCube, vecDot
      (fun i => AVenhance.spaceLap (fun y => a y i) x) (Q.mulVec (b x))) =
    (∫ x in AVenhance.unitCube, vecDot (a x)
      (Q.mulVec (fun j => AVenhance.spaceLap (fun y => b y j) x))) := by
  have hac (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i) := contDiff_pi.mp ha i
  have hbc (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => b x j) := contDiff_pi.mp hb j
  have hapc (i : Fin 2) : AVenhance.IsZ2Periodic (fun x => a x i) := by
    intro k x
    exact congrFun (hap k x) i
  have hbpc (j : Fin 2) : AVenhance.IsZ2Periodic (fun x => b x j) := by
    intro k x
    exact congrFun (hbp k x) j
  have hpair (i j : Fin 2) :
      (∫ x in AVenhance.unitCube, AVenhance.spaceLap (fun y => a y i) x * (Q i j * b x j)) =
      (∫ x in AVenhance.unitCube, a x i * (Q i j * AVenhance.spaceLap (fun y => b y j) x)) := by
    have hlform : (fun x => AVenhance.spaceLap (fun y => a y i) x * (Q i j * b x j)) =
        (fun x => Q i j * (AVenhance.spaceLap (fun y => a y i) x * b x j)) := by
      funext x
      ring
    have hrform : (fun x => a x i * (Q i j * AVenhance.spaceLap (fun y => b y j) x)) =
        (fun x => Q i j * (a x i * AVenhance.spaceLap (fun y => b y j) x)) := by
      funext x
      ring
    rw [hlform, hrform, integral_const_mul, integral_const_mul,
      iterate_laplacian_pairing_transfer (hac i) (hbc j) (hapc i) (hbpc j)]
  have hl (i j : Fin 2) : IntegrableOn (fun x =>
      AVenhance.spaceLap (fun y => a y i) x * (Q i j * b x j)) AVenhance.unitCube :=
    IteratesEnergy.iterate_integrableOn_unitCube ((IteratesEnergy.iterate_spaceLap_contDiff (hac
        i)).continuous.mul
      ((hbc j).continuous.const_mul (Q i j)))
  have hr (i j : Fin 2) : IntegrableOn (fun x =>
      a x i * (Q i j * AVenhance.spaceLap (fun y => b y j) x)) AVenhance.unitCube :=
    IteratesEnergy.iterate_integrableOn_unitCube ((hac i).continuous.mul
      ((IteratesEnergy.iterate_spaceLap_contDiff (hbc j)).continuous.const_mul (Q i j)))
  simp only [vecDot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hl i
      j)),
    integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hr i
        j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hl _ j)]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hr _ j)]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl (fun j _ => hpair i j)

end AVenhance.Infra.Section4
