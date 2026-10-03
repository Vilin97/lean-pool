/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Drift
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Calculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Real-valued periodic integration by parts on the unit cell. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open Set
open AVenhance.Infra.Torus

namespace AVenhance.Infra.Classical

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def PeriodicCalculus.closedUnitCell : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem PeriodicCalculus.isCompact_closedUnitCell : IsCompact PeriodicCalculus.closedUnitCell := by
  simpa [PeriodicCalculus.closedUnitCell] using (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem PeriodicCalculus.unitCell_subset_closedUnitCell : unitCell 2 ⊆
    PeriodicCalculus.closedUnitCell := by
  intro x hx
  simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
  simp only [PeriodicCalculus.closedUnitCell, Set.mem_pi, mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, hx i |>.2⟩

theorem PeriodicCalculus.continuous_integrableOn_unitCell {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f (unitCell 2) :=
  (hf.continuousOn.integrableOn_compact PeriodicCalculus.isCompact_closedUnitCell).mono_set
    PeriodicCalculus.unitCell_subset_closedUnitCell

/-- Real periodic integration by parts, transferred from the complex-valued torus calculus. -/
theorem integral_unitCell_coord_ibp_real (i : Fin 2) {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hpf : AVenhance.IsZ2Periodic f) (hpg : AVenhance.IsZ2Periodic g) :
    (∫ x in unitCell 2, f x * AVenhance.spaceGrad g x i) =
      -∫ x in unitCell 2, AVenhance.spaceGrad f x i * g x := by
  have hper (u : Vec 2 → ℝ) (hu : AVenhance.IsZ2Periodic u) :
      IsZdPeriodic (realToComplex u) := by
    apply (isZdPeriodic_iff_frozen (realToComplex u)).2
    intro k x
    change ((u (x + AVenhance.latticeShift k) : ℝ) : ℂ) = (u x : ℂ)
    rw [hu k x]
  have hDf : coordDeriv i (realToComplex f) =
      fun x => (AVenhance.spaceGrad f x i : ℂ) := by
    funext x
    exact coordDeriv_realToComplex hf i x
  have hDg : coordDeriv i (realToComplex g) =
      fun x => (AVenhance.spaceGrad g x i : ℂ) := by
    funext x
    exact coordDeriv_realToComplex hg i x
  change coordDeriv i (Complex.ofRealCLM ∘ f) = _ at hDf
  change coordDeriv i (Complex.ofRealCLM ∘ g) = _ at hDg
  have hparts := integral_unitCell_coord_ibp (n := 1) i
    (Complex.ofRealCLM.contDiff.comp hf)
    (Complex.ofRealCLM.contDiff.comp hg) (hper f hpf) (hper g hpg)
  rw [hDf, hDg] at hparts
  have hleft :
      (↑(∫ x in unitCell 2, f x * AVenhance.spaceGrad g x i) : ℂ) =
        ∫ x in unitCell 2, (f x : ℂ) * (AVenhance.spaceGrad g x i : ℂ) := by
    symm
    simpa only [Complex.ofReal_mul] using
      (integral_complex_ofReal (f := fun x => f x * AVenhance.spaceGrad g x i))
  have hright :
      (↑(∫ x in unitCell 2, AVenhance.spaceGrad f x i * g x) : ℂ) =
        ∫ x in unitCell 2, (AVenhance.spaceGrad f x i : ℂ) * (g x : ℂ) := by
    symm
    simpa only [Complex.ofReal_mul] using
      (integral_complex_ofReal (f := fun x => AVenhance.spaceGrad f x i * g x))
  apply Complex.ofReal_injective
  calc
    (↑(∫ x in unitCell 2, f x * AVenhance.spaceGrad g x i) : ℂ) =
        ∫ x in unitCell 2, (f x : ℂ) * (AVenhance.spaceGrad g x i : ℂ) := hleft
    _ = -∫ x in unitCell 2, (AVenhance.spaceGrad f x i : ℂ) * (g x : ℂ) := hparts
    _ = (↑(-∫ x in unitCell 2, AVenhance.spaceGrad f x i * g x) : ℂ) := by
      calc
        -∫ x in unitCell 2, (AVenhance.spaceGrad f x i : ℂ) * (g x : ℂ) =
            -(↑(∫ x in unitCell 2, AVenhance.spaceGrad f x i * g x) : ℂ) :=
          congrArg Neg.neg hright.symm
        _ = ↑(-∫ x in unitCell 2, AVenhance.spaceGrad f x i * g x) :=
          (Complex.ofReal_neg _).symm

theorem PeriodicCalculus.spaceGrad_sq {w : Vec 2 → ℝ} (hw : ContDiff ℝ 1 w)
    (x : Vec 2) (i : Fin 2) :
    AVenhance.spaceGrad (fun y => w y ^ 2) x i =
      2 * w x * AVenhance.spaceGrad w x i := by
  change fderiv ℝ (fun y => w y ^ 2) x (Homogenization.basisVec i) = _
  rw [fderiv_fun_pow 2 (hw.differentiable (by simp) x)]
  simp [AVenhance.spaceGrad, pow_one, mul_assoc]

/-- Smooth periodic transport contributes no quadratic energy on the unit torus when its
classical divergence vanishes. -/
theorem integral_unitCell_transport_energy_zero
    (b : Vec 2 → Vec 2) (hb : ContDiff ℝ 1 b)
    (hbp : ∀ i : Fin 2, AVenhance.IsZ2Periodic (fun x => b x i))
    (hdiv : ∀ x, AVenhance.vecDiv b x = 0)
    (w : Vec 2 → ℝ) (hw : ContDiff ℝ 1 w)
    (hwp : AVenhance.IsZ2Periodic w) :
    (∫ x in unitCell 2,
      Homogenization.vecDot (b x) (AVenhance.spaceGrad w x) * w x) = 0 := by
  let wSq : Vec 2 → ℝ := fun x => w x ^ 2
  have hwSq : ContDiff ℝ 1 wSq := by
    dsimp [wSq]
    exact hw.pow 2
  have hwpSq : AVenhance.IsZ2Periodic wSq := by
    intro k x
    simp [wSq, hwp k x]
  have hbComp (i : Fin 2) : ContDiff ℝ 1 (fun x => b x i) :=
    (contDiff_pi.1 hb) i
  have hgradBSmooth (i : Fin 2) :
      Continuous (fun x => AVenhance.spaceGrad (fun y => b y i) x i) := by
    change Continuous (fun x => fderiv ℝ (fun y => b y i) x (Homogenization.basisVec i))
    exact (hbComp i).continuous_fderiv (by simp) |>.clm_apply continuous_const
  have hgradWSmooth (i : Fin 2) : Continuous (fun x => AVenhance.spaceGrad w x i) := by
    change Continuous (fun x => fderiv ℝ w x (Homogenization.basisVec i))
    exact hw.continuous_fderiv (by simp) |>.clm_apply continuous_const
  have hgradWSqSmooth (i : Fin 2) :
      Continuous (fun x => AVenhance.spaceGrad wSq x i) := by
    change Continuous (fun x => fderiv ℝ wSq x (Homogenization.basisVec i))
    exact hwSq.continuous_fderiv (by simp) |>.clm_apply continuous_const
  have htermsInt (i : Fin 2) :
      IntegrableOn (fun x => b x i * AVenhance.spaceGrad wSq x i) (unitCell 2) :=
    PeriodicCalculus.continuous_integrableOn_unitCell ((hbComp i).continuous.mul (hgradWSqSmooth i))
  have hdivTermsInt (i : Fin 2) :
      IntegrableOn
        (fun x => AVenhance.spaceGrad (fun y => b y i) x i * wSq x) (unitCell 2) :=
    PeriodicCalculus.continuous_integrableOn_unitCell ((hgradBSmooth i).mul hwSq.continuous)
  have htransportParts (i : Fin 2) :
      (∫ x in unitCell 2, b x i * AVenhance.spaceGrad wSq x i) =
        -∫ x in unitCell 2,
          AVenhance.spaceGrad (fun y => b y i) x i * wSq x := by
    exact integral_unitCell_coord_ibp_real i (hbComp i) hwSq (hbp i) hwpSq
  have hsumL := integral_finsetSum (Finset.univ : Finset (Fin 2))
    (μ := (volume : Measure (Vec 2)).restrict (unitCell 2))
    (f := fun i : Fin 2 => fun x => b x i * AVenhance.spaceGrad wSq x i)
    (fun i hi => htermsInt i)
  have hsumR := integral_finsetSum (Finset.univ : Finset (Fin 2))
    (μ := (volume : Measure (Vec 2)).restrict (unitCell 2))
    (f := fun i : Fin 2 => fun x =>
      AVenhance.spaceGrad (fun y => b y i) x i * wSq x)
    (fun i hi => hdivTermsInt i)
  have hdivIntegral :
      (∫ x in unitCell 2, AVenhance.vecDiv b x * wSq x) =
        ∑ i : Fin 2, ∫ x in unitCell 2,
          AVenhance.spaceGrad (fun y => b y i) x i * wSq x := by
    calc
      (∫ x in unitCell 2, AVenhance.vecDiv b x * wSq x) =
          ∫ x in unitCell 2, ∑ i : Fin 2,
            AVenhance.spaceGrad (fun y => b y i) x i * wSq x := by
        apply setIntegral_congr_ae (measurableSet_unitCell 2)
        filter_upwards with x hx
        simp only [AVenhance.vecDiv, Fin.sum_univ_two]
        ring
      _ = ∑ i : Fin 2, ∫ x in unitCell 2,
          AVenhance.spaceGrad (fun y => b y i) x i * wSq x := hsumR
  have hgradSqIntegral :
      (∫ x in unitCell 2,
        Homogenization.vecDot (b x) (AVenhance.spaceGrad wSq x)) = 0 := by
    calc
      (∫ x in unitCell 2,
          Homogenization.vecDot (b x) (AVenhance.spaceGrad wSq x)) =
          ∑ i : Fin 2, ∫ x in unitCell 2,
            b x i * AVenhance.spaceGrad wSq x i := by
        rw [← hsumL]
        congr 1
      _ = ∑ i : Fin 2, -(∫ x in unitCell 2,
            AVenhance.spaceGrad (fun y => b y i) x i * wSq x) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact htransportParts i
      _ = -(∑ i : Fin 2, ∫ x in unitCell 2,
            AVenhance.spaceGrad (fun y => b y i) x i * wSq x) := by
        rw [Finset.sum_neg_distrib]
      _ = -(∫ x in unitCell 2, AVenhance.vecDiv b x * wSq x) := by
        rw [hdivIntegral]
      _ = 0 := by simp [hdiv]
  have hrelation (x : Vec 2) :
      Homogenization.vecDot (b x) (AVenhance.spaceGrad wSq x) =
        2 * (Homogenization.vecDot (b x) (AVenhance.spaceGrad w x) * w x) := by
    simp [wSq, Homogenization.vecDot, PeriodicCalculus.spaceGrad_sq hw, Fin.sum_univ_two]
    ring
  have htargetIntegrable : IntegrableOn
      (fun x => Homogenization.vecDot (b x) (AVenhance.spaceGrad w x) * w x)
      (unitCell 2) := by
    apply PeriodicCalculus.continuous_integrableOn_unitCell
    change Continuous (fun x =>
      (∑ i : Fin 2, b x i * AVenhance.spaceGrad w x i) * w x)
    exact (continuous_finsetSum Finset.univ fun i hi =>
      (hbComp i).continuous.mul (hgradWSmooth i)).mul hw.continuous
  have htwice :
      (∫ x in unitCell 2, Homogenization.vecDot (b x) (AVenhance.spaceGrad wSq x)) =
        2 * (∫ x in unitCell 2,
          Homogenization.vecDot (b x) (AVenhance.spaceGrad w x) * w x) := by
    calc
      _ = ∫ x in unitCell 2,
          2 * (Homogenization.vecDot (b x) (AVenhance.spaceGrad w x) * w x) := by
        apply setIntegral_congr_ae (measurableSet_unitCell 2)
        filter_upwards with x hx
        exact hrelation x
      _ = 2 * (∫ x in unitCell 2,
          Homogenization.vecDot (b x) (AVenhance.spaceGrad w x) * w x) := by
        rw [integral_const_mul]
  rw [hgradSqIntegral] at htwice
  have hzero : 2 * (∫ x in unitCell 2,
      Homogenization.vecDot (b x) (AVenhance.spaceGrad w x) * w x) = 0 := by
    linarith
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- The admissible stream drift has vanishing quadratic transport energy for any smooth periodic
test function on the torus. -/
theorem streamVel_unitCell_transport_energy_zero
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ) (t : ℝ)
    (w : Vec 2 → ℝ) (hw : ContDiff ℝ 1 w) (hwp : AVenhance.IsZ2Periodic w) :
    (∫ x in unitCell 2,
      Homogenization.vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad w x) * w x) = 0 := by
  have hb := streamVel_smoothPeriodic φ hφ
  have hbSlice : ContDiff ℝ 1 (AVenhance.streamVel φ t) := by
    exact (hb.smooth.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id)
  have hbper (i : Fin 2) :
      AVenhance.IsZ2Periodic (fun x => AVenhance.streamVel φ t x i) := by
    intro k x
    have h := hb.periodic 0 k t x
    simpa [AVenhance.latticeShift] using congrArg (fun v : Vec 2 => v i) h
  exact integral_unitCell_transport_energy_zero (AVenhance.streamVel φ t)
    hbSlice hbper (streamVel_vecDiv_eq_zero φ hφ t) w hw hwp

/-- Coordinate derivatives of a smooth periodic real function remain periodic. -/
theorem periodic_spaceGrad_component {f : Vec 2 → ℝ}
    (hper : AVenhance.IsZ2Periodic f) (i : Fin 2) :
    AVenhance.IsZ2Periodic (fun x => AVenhance.spaceGrad f x i) := by
  intro n x
  let a := AVenhance.latticeShift n
  have hEq : (fun y => f (y + a)) = f := by
    funext y
    exact hper n y
  have hderiv : fderiv ℝ f (x + a) = fderiv ℝ f x := by
    calc
      fderiv ℝ f (x + a) = fderiv ℝ (fun y => f (y + a)) x := by
        rw [fderiv_comp_add_right]
      _ = fderiv ℝ f x := by rw [hEq]
  exact congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (Homogenization.basisVec i)) hderiv

/-- The periodic Laplacian transfers one derivative to an independent test function. -/
theorem integral_unitCell_lap_mul {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hpf : AVenhance.IsZ2Periodic f) (hpg : AVenhance.IsZ2Periodic g) :
    (∫ x in unitCell 2, f x * AVenhance.spaceLap g x) =
      -∫ x in unitCell 2,
        Homogenization.vecDot (AVenhance.spaceGrad f x) (AVenhance.spaceGrad g x) := by
  have hgrad (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad g x i) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ g x (Homogenization.basisVec i))
    exact (hg.fderiv_right (by simp)).clm_apply contDiff_const
  have hgradPer (i : Fin 2) :
      AVenhance.IsZ2Periodic (fun x => AVenhance.spaceGrad g x i) :=
    periodic_spaceGrad_component hpg i
  have htermInt (i : Fin 2) : IntegrableOn
      (fun x => f x * AVenhance.spaceGrad
        (fun y => AVenhance.spaceGrad g y i) x i) (unitCell 2) := by
    have hsecond : ContDiff ℝ 1 (fun x => AVenhance.spaceGrad g x i) :=
      (hgrad i).of_le (by norm_num)
    have hDsecond : Continuous
        (fun x => AVenhance.spaceGrad (fun y => AVenhance.spaceGrad g y i) x i) := by
      change Continuous (fun x => fderiv ℝ
        (fun y => AVenhance.spaceGrad g y i) x (Homogenization.basisVec i))
      exact (hsecond.continuous_fderiv (by simp)).clm_apply continuous_const
    exact PeriodicCalculus.continuous_integrableOn_unitCell (hf.continuous.mul hDsecond)
  have hparts (i : Fin 2) :
      (∫ x in unitCell 2, f x * AVenhance.spaceGrad
        (fun y => AVenhance.spaceGrad g y i) x i) =
      -∫ x in unitCell 2,
        AVenhance.spaceGrad f x i * AVenhance.spaceGrad g x i := by
    exact integral_unitCell_coord_ibp_real i (hf.of_le (by norm_num))
      ((hgrad i).of_le (by norm_num)) hpf (hgradPer i)
  have hgradProductInt (i : Fin 2) : IntegrableOn
      (fun x => AVenhance.spaceGrad f x i * AVenhance.spaceGrad g x i)
      (unitCell 2) := by
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
    exact PeriodicCalculus.continuous_integrableOn_unitCell
      (((hf1.continuous_fderiv (by simp)).clm_apply continuous_const).mul
        ((hgrad i).continuous))
  have hsumLap := integral_finsetSum (Finset.univ : Finset (Fin 2))
    (μ := (volume : Measure (Vec 2)).restrict (unitCell 2))
    (f := fun i : Fin 2 => fun x => f x * AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad g y i) x i)
    (fun i hi => htermInt i)
  have hsumGrad := integral_finsetSum (Finset.univ : Finset (Fin 2))
    (μ := (volume : Measure (Vec 2)).restrict (unitCell 2))
    (f := fun i : Fin 2 => fun x =>
      AVenhance.spaceGrad f x i * AVenhance.spaceGrad g x i)
    (fun i hi => hgradProductInt i)
  calc
    (∫ x in unitCell 2, f x * AVenhance.spaceLap g x) =
        ∑ i : Fin 2, ∫ x in unitCell 2, f x * AVenhance.spaceGrad
          (fun y => AVenhance.spaceGrad g y i) x i := by
      calc
        _ = ∫ x in unitCell 2, ∑ i : Fin 2, f x * AVenhance.spaceGrad
            (fun y => AVenhance.spaceGrad g y i) x i := by
          apply setIntegral_congr_ae (measurableSet_unitCell 2)
          filter_upwards with x hx
          simp only [AVenhance.spaceLap, Fin.sum_univ_two]
          ring
        _ = _ := hsumLap
    _ = -(∑ i : Fin 2, ∫ x in unitCell 2,
        AVenhance.spaceGrad f x i * AVenhance.spaceGrad g x i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact hparts i
    _ = -(∫ x in unitCell 2,
        Homogenization.vecDot (AVenhance.spaceGrad f x) (AVenhance.spaceGrad g x)) := by
      rw [← hsumGrad]
      congr 1

/-- Spatial integration by parts gives the quadratic Laplacian energy identity on the unit cell. -/
theorem integral_unitCell_lap_energy {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : AVenhance.IsZ2Periodic f) :
    (∫ x in unitCell 2, f x * AVenhance.spaceLap f x) =
      -∫ x in unitCell 2,
        Homogenization.vecDot (AVenhance.spaceGrad f x) (AVenhance.spaceGrad f x) := by
  have hgrad (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad f x i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (Homogenization.basisVec i))
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hgradPer (i : Fin 2) :
      AVenhance.IsZ2Periodic (fun x => AVenhance.spaceGrad f x i) :=
    periodic_spaceGrad_component hper i
  have htermInt (i : Fin 2) : IntegrableOn
      (fun x => f x * AVenhance.spaceGrad
        (fun y => AVenhance.spaceGrad f y i) x i) (unitCell 2) := by
    have hsecond : ContDiff ℝ 1 (fun x => AVenhance.spaceGrad f x i) :=
      (hgrad i).of_le (by norm_num)
    have hDsecond : Continuous
        (fun x => AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y i) x i) := by
      change Continuous (fun x => fderiv ℝ
        (fun y => AVenhance.spaceGrad f y i) x (Homogenization.basisVec i))
      exact (hsecond.continuous_fderiv (by simp)).clm_apply continuous_const
    exact PeriodicCalculus.continuous_integrableOn_unitCell (hf.continuous.mul hDsecond)
  have hparts (i : Fin 2) :
      (∫ x in unitCell 2, f x * AVenhance.spaceGrad
        (fun y => AVenhance.spaceGrad f y i) x i) =
      -∫ x in unitCell 2,
        AVenhance.spaceGrad f x i * AVenhance.spaceGrad f x i := by
    exact integral_unitCell_coord_ibp_real i (hf.of_le (by norm_num))
      ((hgrad i).of_le (by norm_num)) hper (hgradPer i)
  have hsumLap := integral_finsetSum (Finset.univ : Finset (Fin 2))
    (μ := (volume : Measure (Vec 2)).restrict (unitCell 2))
    (f := fun i : Fin 2 => fun x => f x * AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y i) x i)
    (fun i hi => htermInt i)
  have hsqInt (i : Fin 2) : IntegrableOn
      (fun x => (AVenhance.spaceGrad f x i) ^ 2) (unitCell 2) := by
    exact PeriodicCalculus.continuous_integrableOn_unitCell ((hgrad i).continuous.pow 2)
  have hsumSq := integral_finsetSum (Finset.univ : Finset (Fin 2))
    (μ := (volume : Measure (Vec 2)).restrict (unitCell 2))
    (f := fun i : Fin 2 => fun x => (AVenhance.spaceGrad f x i) ^ 2)
    (fun i hi => hsqInt i)
  calc
    (∫ x in unitCell 2, f x * AVenhance.spaceLap f x) =
        ∑ i : Fin 2, ∫ x in unitCell 2, f x * AVenhance.spaceGrad
          (fun y => AVenhance.spaceGrad f y i) x i := by
      calc
        (∫ x in unitCell 2, f x * AVenhance.spaceLap f x) =
            ∫ x in unitCell 2, ∑ i : Fin 2, f x * AVenhance.spaceGrad
              (fun y => AVenhance.spaceGrad f y i) x i := by
          apply setIntegral_congr_ae (measurableSet_unitCell 2)
          filter_upwards with x hx
          simp only [AVenhance.spaceLap, Fin.sum_univ_two]
          ring
        _ = ∑ i : Fin 2, ∫ x in unitCell 2, f x * AVenhance.spaceGrad
            (fun y => AVenhance.spaceGrad f y i) x i := hsumLap
    _ = -(∑ i : Fin 2, ∫ x in unitCell 2,
        (AVenhance.spaceGrad f x i) ^ 2) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simpa [pow_two] using hparts i
    _ = -(∫ x in unitCell 2,
        Homogenization.vecDot (AVenhance.spaceGrad f x) (AVenhance.spaceGrad f x)) := by
      rw [← hsumSq]
      congr 1
      apply setIntegral_congr_ae (measurableSet_unitCell 2)
      filter_upwards with x hx
      simp [Homogenization.vecDot, Fin.sum_univ_two, pow_two]

end AVenhance.Infra.Classical

end
