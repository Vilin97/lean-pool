/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ProductPathIdentification
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TorusBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.L2NormSq

/-!
# Spatial derivative tests for the synchronized Galerkin limit

The Galerkin gradients are weak derivatives on the torus. This module begins the corresponding
closedness argument in the synchronized product-space limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance productWeakGradientMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance productWeakGradientOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

/-- The spatial vector containing a scalar in coordinate `i` and zero in the other coordinate. -/
def scalarToSpatialVector (i : Fin 2) : ℝ →L[ℝ] SpatialVector :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) i)

/-- Embed a scalar torus `L²` function into one coordinate of the vector torus `L²` space. -/
def scalarToSpatialGradientL2 (i : Fin 2) : ScalarTorusL2 →L[ℝ] SpatialGradientL2 :=
  (scalarToSpatialVector i).compLpL 2 (volume : Measure Torus)

@[simp]
theorem scalarToSpatialVector_apply (i : Fin 2) (r : ℝ) :
    scalarToSpatialVector i r = WithLp.toLp 2 (Pi.single i r) := by
  simp [scalarToSpatialVector, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.single_apply]

@[simp]
theorem scalarToSpatialGradientL2_apply (i : Fin 2) (f : ScalarTorusL2) :
    scalarToSpatialGradientL2 i f =
      (scalarToSpatialVector i).compLp f := rfl

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def ProductWeakGradient.productWeakGradientClosedCell : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem ProductWeakGradient.productWeakGradientClosedCell_compact :
    IsCompact ProductWeakGradient.productWeakGradientClosedCell := by
  simpa [ProductWeakGradient.productWeakGradientClosedCell] using
    (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem ProductWeakGradient.productWeakGradient_cube_subset_closedCell :
    AVenhance.unitCube ⊆ ProductWeakGradient.productWeakGradientClosedCell := by
  intro x hx
  simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ, forall_true_left] at hx ⊢
  intro i _
  exact ⟨le_of_lt (hx i).1, le_of_lt (hx i).2⟩

theorem ProductWeakGradient.productWeakGradient_unitCell_subset_closedCell :
    AVenhance.Infra.Torus.unitCell 2 ⊆ ProductWeakGradient.productWeakGradientClosedCell := by
  intro x hx
  simp only [AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt,
    Set.mem_ofPred_eq, zero_add] at hx
  simp only [ProductWeakGradient.productWeakGradientClosedCell, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, (hx i).2⟩

theorem ProductWeakGradient.productWeakGradient_continuous_unitCell_integrable {f : Vec 2 → ℝ}
    (hf : Continuous f) : IntegrableOn f (AVenhance.Infra.Torus.unitCell 2) := by
  exact (hf.continuousOn.integrableOn_compact
      ProductWeakGradient.productWeakGradientClosedCell_compact).mono_set
    ProductWeakGradient.productWeakGradient_unitCell_subset_closedCell

theorem ProductWeakGradient.productWeakGradient_realToComplex_periodic {f : Vec 2 → ℝ}
    (hperiodic : AVenhance.IsZ2Periodic f) :
    AVenhance.Infra.Torus.IsZdPeriodic (AVenhance.Infra.Torus.realToComplex f) := by
  intro k x
  have h := (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen f).2 hperiodic k x
  exact congrArg (fun y : ℝ => (y : ℂ)) h

theorem ProductWeakGradient.productWeakGradient_integral_unitCube_coord_ibp
    {f g : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g)
    (hpf : AVenhance.IsZ2Periodic f) (hpg : AVenhance.IsZ2Periodic g)
    (i : Fin 2) :
    (∫ x in AVenhance.unitCube, f x * AVenhance.spaceGrad g x i) =
      -∫ x in AVenhance.unitCube, AVenhance.spaceGrad f x i * g x := by
  let fc := AVenhance.Infra.Torus.realToComplex f
  let gc := AVenhance.Infra.Torus.realToComplex g
  have hfc : ContDiff ℝ 1 fc := Complex.ofRealCLM.contDiff.comp hf
  have hgc : ContDiff ℝ 1 gc := Complex.ofRealCLM.contDiff.comp hg
  have hfcPer := ProductWeakGradient.productWeakGradient_realToComplex_periodic hpf
  have hgcPer := ProductWeakGradient.productWeakGradient_realToComplex_periodic hpg
  have hcomplex := AVenhance.Infra.Torus.integral_unitCell_coord_ibp i hfc hgc
    hfcPer hgcPer
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
        rw [AVenhance.Infra.Torus.coordDeriv_realToComplex hg i x]
        simp [AVenhance.Infra.Torus.realToComplex, Complex.ofReal_mul]
      _ = -∫ x in AVenhance.Infra.Torus.unitCell 2,
          AVenhance.Infra.Torus.coordDeriv i fc x * gc x := hcomplex
      _ = -∫ x in AVenhance.Infra.Torus.unitCell 2,
          ((AVenhance.spaceGrad f x i * g x : ℝ) : ℂ) := by
        congr 1
        apply setIntegral_congr_fun (AVenhance.Infra.Torus.measurableSet_unitCell 2)
        intro x hx
        simp only [fc, gc]
        rw [AVenhance.Infra.Torus.coordDeriv_realToComplex hf i x]
        simp [AVenhance.Infra.Torus.realToComplex, Complex.ofReal_mul]
  have hleftInt : IntegrableOn (fun x : Vec 2 => f x * AVenhance.spaceGrad g x i)
      (AVenhance.Infra.Torus.unitCell 2) :=
    ProductWeakGradient.productWeakGradient_continuous_unitCell_integrable
      (hf.continuous.mul ((hg.continuous_fderiv (by simp)).clm_apply continuous_const))
  have hrightInt : IntegrableOn
      (fun x : Vec 2 => AVenhance.spaceGrad f x i * g x)
      (AVenhance.Infra.Torus.unitCell 2) :=
    ProductWeakGradient.productWeakGradient_continuous_unitCell_integrable
      (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hg.continuous)
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

theorem ProductWeakGradient.productWeakGradient_smooth_memL2On {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : MemL2On AVenhance.unitCube f := by
  apply (memLp_two_iff_integrable_sq
    hf.continuous.measurable.aestronglyMeasurable).2
  exact (hf.continuous.pow 2).continuousOn.integrableOn_compact
    ProductWeakGradient.productWeakGradientClosedCell_compact |>.mono_set
      ProductWeakGradient.productWeakGradient_cube_subset_closedCell

theorem ProductWeakGradient.smoothPeriodicTestL2_coeFn {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hperiodic : AVenhance.IsZ2Periodic ψ) :
    (fun x : Torus => smoothPeriodicTestL2 hψ hperiodic x) =ᵐ[volume]
      AVenhance.Infra.Torus.periodicToTorus ψ := by
  have hmem : MemLp (AVenhance.Infra.Torus.periodicToTorus ψ) 2 volume :=
    frozenInitialData_memLp_torus (ProductWeakGradient.productWeakGradient_smooth_memL2On hψ)
  have hclass : smoothPeriodicTestL2 hψ hperiodic = hmem.toLp
      (AVenhance.Infra.Torus.periodicToTorus ψ) := by
    apply Lp.ext
    rfl
  rw [hclass]
  exact hmem.coeFn_toLp

theorem productWeakGradient_coord_contDiff {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad ψ x i) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ ψ) :=
    hψ.fderiv_right (by simp)
  exact hfd.clm_apply contDiff_const

theorem productWeakGradient_coord_periodic {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hperiodic : AVenhance.IsZ2Periodic ψ)
    (i : Fin 2) : AVenhance.IsZ2Periodic (fun x => AVenhance.spaceGrad ψ x i) := by
  have hvec : AVenhance.IsZ2Periodic (AVenhance.spaceGrad ψ) := by
    intro k x
    let v : Homogenization.Vec 2 := AVenhance.latticeShift k
    have hshift : (fun y : Vec 2 => ψ (y + v)) = ψ := by
      funext y
      exact hperiodic k y
    have hdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
    have htranslate : HasFDerivAt (fun y : Vec 2 => y + v)
        (ContinuousLinearMap.id ℝ (Homogenization.Vec 2)) x := by
      have hid : HasFDerivAt (fun y : Vec 2 => y)
          (ContinuousLinearMap.id ℝ (Homogenization.Vec 2)) x := hasFDerivAt_id x
      simpa only [id_eq] using hid.add_const v
    have hcomp := (hdiff (x + v)).hasFDerivAt.comp x htranslate
    have hderivShift : HasFDerivAt ψ (fderiv ℝ ψ (x + v)) x := by
      have hcomp' := hcomp
      change HasFDerivAt (fun y : Vec 2 => ψ (y + v))
        (fderiv ℝ ψ (x + v) ∘L ContinuousLinearMap.id ℝ (Vec 2)) x at hcomp'
      rw [ContinuousLinearMap.comp_id, hshift] at hcomp'
      exact hcomp'
    have hderivBase : HasFDerivAt ψ (fderiv ℝ ψ x) x := (hdiff x).hasFDerivAt
    have heq : fderiv ℝ ψ (x + v) = fderiv ℝ ψ x := hderivShift.unique hderivBase
    funext j
    change fderiv ℝ ψ (x + AVenhance.latticeShift k) (basisVec j) =
      fderiv ℝ ψ x (basisVec j)
    exact congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec j)) heq
  intro k x
  exact congrFun (hvec k x) i

theorem ProductWeakGradient.realFourierModeGradL2_coordinate_pairing
    (N : ℕ) (j : Fin (RealFourierDimension N)) (i : Fin 2)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) :
    inner ℝ (realFourierModeGradL2 N j)
        (scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic)) =
      -inner ℝ (realFourierModeL2 N j)
        (smoothPeriodicTestL2 (productWeakGradient_coord_contDiff hψ i)
          (productWeakGradient_coord_periodic hψ hperiodic i)) := by
  let f : Vec 2 → ℝ := realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j)
  have hfTop : ContDiff ℝ ⊤ f := by
    simpa [f] using realFourierModeAmbient_contDiff N
      ((realFourierIndexEquivFin N).symm j)
  have hf : ContDiff ℝ 1 f := hfTop.of_le (by simp)
  have hfp : AVenhance.IsZ2Periodic f := by
    exact realFourierModeAmbient_periodic N _
  let df : Vec 2 → Vec 2 := realFourierModeAmbientGrad N
    ((realFourierIndexEquivFin N).symm j)
  have hgrad : (fun x : Torus =>
      (WithLp.toLp 2 (realFourierModeGradFin N j x) : SpatialVector)) =ᵐ[volume]
      fun x => WithLp.toLp 2 (df (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)) := by
    filter_upwards with x
    simp [df, realFourierModeGradFin_eq_periodicToTorus,
      AVenhance.Infra.Torus.periodicToTorus]
  have htest := ProductWeakGradient.smoothPeriodicTestL2_coeFn hψ hperiodic
  have hderiv := ProductWeakGradient.smoothPeriodicTestL2_coeFn
    (productWeakGradient_coord_contDiff hψ i)
    (productWeakGradient_coord_periodic hψ hperiodic i)
  have hmode : (fun x : Torus => realFourierModeGradL2 N j x) =ᵐ[volume]
      fun x => WithLp.toLp 2 (realFourierModeGradFin N j x) := by
    simpa [realFourierModeGradL2] using (realFourierModeGradFin_memLp N j).coeFn_toLp
  have hvec : (fun x : Torus =>
      scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic) x) =ᵐ[volume]
      fun x => scalarToSpatialVector i (smoothPeriodicTestL2 hψ hperiodic x) := by
    change (fun x => ((scalarToSpatialVector i).compLp
      (smoothPeriodicTestL2 hψ hperiodic)) x) =ᵐ[volume] _
    exact (scalarToSpatialVector i).coeFn_compLp (smoothPeriodicTestL2 hψ hperiodic)
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : Torus, inner ℝ (realFourierModeGradL2 N j x)
        (scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic) x)) =
      ∫ x : Torus, df (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) i *
        AVenhance.Infra.Torus.periodicToTorus ψ x := by
          apply integral_congr_ae
          filter_upwards [hmode, hgrad, hvec, htest] with x hmodex hgradx hvecx hψx
          rw [hmodex, hgradx, hvecx, hψx]
          rw [PiLp.inner_apply]
          simp only [scalarToSpatialVector_apply, Pi.single_apply]
          simp
          ring
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
        AVenhance.spaceGrad f x i * ψ x := by
          rw [← AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell]
          apply integral_congr_ae
          filter_upwards with x
          change AVenhance.spaceGrad f
              (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) i *
                ψ (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) =
            AVenhance.spaceGrad f
              (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) i *
                ψ (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)
          rfl
    _ = ∫ x in AVenhance.unitCube, AVenhance.spaceGrad f x i * ψ x := by
          rw [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
    _ = -∫ x in AVenhance.unitCube, f x * AVenhance.spaceGrad ψ x i := by
          have hIBP := ProductWeakGradient.productWeakGradient_integral_unitCube_coord_ibp
            (hψ.of_le (by simp)) hf hperiodic hfp i
          calc
            _ = ∫ x in AVenhance.unitCube, ψ x * AVenhance.spaceGrad f x i := by
              apply integral_congr_ae
              filter_upwards with x
              ring
            _ = -∫ x in AVenhance.unitCube,
                AVenhance.spaceGrad ψ x i * f x := hIBP
            _ = -∫ x in AVenhance.unitCube, f x * AVenhance.spaceGrad ψ x i := by
              congr 1
              apply integral_congr_ae
              filter_upwards with x
              ring
    _ = -inner ℝ (realFourierModeL2 N j)
        (smoothPeriodicTestL2 (productWeakGradient_coord_contDiff hψ i)
          (productWeakGradient_coord_periodic hψ hperiodic i)) := by
          have hmode : (fun x : Torus => realFourierModeL2 N j x) =ᵐ[volume]
              AVenhance.Infra.Torus.periodicToTorus f := by
            filter_upwards [(realFourierModeFin_memLp N j).coeFn_toLp] with x hx
            calc
              realFourierModeL2 N j x = realFourierModeFin N j x := hx
              _ = AVenhance.Infra.Torus.periodicToTorus f x := by
                rw [realFourierModeFin_eq_periodicToTorus]
          have hcell : ∫ x in AVenhance.Infra.Torus.unitCell 2,
              f x * AVenhance.spaceGrad ψ x i =
              ∫ x in AVenhance.unitCube,
                f x * AVenhance.spaceGrad ψ x i := by
            exact AVenhance.Infra.Torus.integral_unitCell_eq_unitCube _
          have htorus : ∫ x : Torus,
              AVenhance.Infra.Torus.periodicToTorus f x *
                AVenhance.Infra.Torus.periodicToTorus
                  (fun y => AVenhance.spaceGrad ψ y i) x =
              ∫ x in AVenhance.Infra.Torus.unitCell 2,
                f x * AVenhance.spaceGrad ψ x i := by
            rw [← AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell]
            apply integral_congr_ae
            filter_upwards with x
            simp [AVenhance.Infra.Torus.periodicToTorus]
          calc
            _ = -(∫ x : Torus,
                AVenhance.Infra.Torus.periodicToTorus f x *
                  AVenhance.Infra.Torus.periodicToTorus
                    (fun y => AVenhance.spaceGrad ψ y i) x) := by
                    congr 1
                    exact hcell.symm.trans htorus.symm
            _ = -∫ x : Torus,
                inner ℝ (realFourierModeL2 N j x)
                  (smoothPeriodicTestL2
                    (productWeakGradient_coord_contDiff hψ i)
                    (productWeakGradient_coord_periodic hψ hperiodic i) x) := by
                    congr 1
                    apply integral_congr_ae
                    filter_upwards [hmode, hderiv] with x hx hd
                    rw [← hx, hd]
                    simp [mul_comm]
            _ = _ := by rw [MeasureTheory.L2.inner_def]

/-- Finite real Fourier sums satisfy the coordinate distributional-gradient identity against any
smooth periodic spatial test. -/
theorem realFourierGradientMap_coordinate_pairing
    (N : ℕ) (c : Coefficients (RealFourierDimension N)) (i : Fin 2)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) :
    inner ℝ (realFourierGradientMap N c)
        (scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic)) =
      -inner ℝ (realFourierScalarMap N c)
        (smoothPeriodicTestL2 (productWeakGradient_coord_contDiff hψ i)
          (productWeakGradient_coord_periodic hψ hperiodic i)) := by
  let ψT := smoothPeriodicTestL2 hψ hperiodic
  let dψT := smoothPeriodicTestL2 (productWeakGradient_coord_contDiff hψ i)
    (productWeakGradient_coord_periodic hψ hperiodic i)
  have hleft : inner ℝ (realFourierGradientMap N c)
      (scalarToSpatialGradientL2 i ψT) =
      ∑ j : Fin (RealFourierDimension N), c j *
        inner ℝ (realFourierModeGradL2 N j) (scalarToSpatialGradientL2 i ψT) := by
    rw [realFourierGradientMap_apply, sum_inner]
    simp_rw [inner_smul_left]
    simp
  have hright : inner ℝ (realFourierScalarMap N c) dψT =
      ∑ j : Fin (RealFourierDimension N), c j *
        inner ℝ (realFourierModeL2 N j) dψT := by
    rw [realFourierScalarMap_apply, sum_inner]
    simp_rw [inner_smul_left]
    simp
  change inner ℝ (realFourierGradientMap N c) (scalarToSpatialGradientL2 i ψT) =
    -inner ℝ (realFourierScalarMap N c) dψT
  rw [hleft, hright]
  calc
    (∑ j : Fin (RealFourierDimension N), c j *
        inner ℝ (realFourierModeGradL2 N j) (scalarToSpatialGradientL2 i ψT)) =
      ∑ j : Fin (RealFourierDimension N), -(c j *
        inner ℝ (realFourierModeL2 N j) dψT) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [ProductWeakGradient.realFourierModeGradL2_coordinate_pairing N j i hψ hperiodic]
          ring
    _ = -(∑ j : Fin (RealFourierDimension N), c j *
        inner ℝ (realFourierModeL2 N j) dψT) := by
          rw [← Finset.sum_neg_distrib]

private theorem FrozenDriftProblem.galerkinData_gradientMap
    (P : FrozenDriftProblem) (N : ℕ) :
    (P.galerkinData N).gradient = positiveCutoffGradientMap N := by
  rfl

private theorem FrozenDriftProblem.gradientTimeFunction_eq_gradientMap
    (P : FrozenDriftProblem) (N : ℕ) (t : ℝ) :
    P.gradientTimeFunction N t =
      realFourierGradientMap N (AVenhance.Infra.ODE.extendCurve
        (by norm_num) (P.coefficientPath N) t) := by
  change (P.galerkinData N).gradient _ = _
  rw [P.galerkinData_gradientMap, positiveCutoffGradientMap]
  rfl

/-- Every concrete finite Galerkin gradient is the spatial weak gradient of its scalar path when
paired against a smooth periodic test. -/
theorem FrozenDriftProblem.finite_gradient_coordinate_pairing
    (P : FrozenDriftProblem) (N : ℕ) (t : ℝ) (i : Fin 2)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) :
    inner ℝ (P.gradientTimeFunction N t)
        (scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic)) =
      -inner ℝ (P.scalarTimeFunction N t)
        (smoothPeriodicTestL2 (productWeakGradient_coord_contDiff hψ i)
          (productWeakGradient_coord_periodic hψ hperiodic i)) := by
  rw [FrozenDriftProblem.gradientTimeFunction_eq_gradientMap]
  exact realFourierGradientMap_coordinate_pairing N
    (AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N) t)
    i hψ hperiodic

/-- The finite product-space Galerkin scalar and gradient representatives satisfy the spatial
integration-by-parts identity for every separated bounded time test. -/
theorem FrozenDriftProblem.finite_product_spatial_derivative_identity
    (P : FrozenDriftProblem) (N : ℕ) (η : ℝ → ℝ)
    (hη : MemLp η ⊤ GalerkinTimeMeasure) (i : Fin 2)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) :
    inner ℝ (P.gradientProductLp N)
        (gradientProductTestLp η
          (scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic)) hη) =
      -inner ℝ (P.scalarProductLp N)
        (scalarProductTestLp η
          (smoothPeriodicTestL2 (productWeakGradient_coord_contDiff hψ i)
            (productWeakGradient_coord_periodic hψ hperiodic i)) hη) := by
  rw [P.gradientProductLp_pairing_time N η hη
      (scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic)),
    P.scalarProductLp_pairing_time N η hη
      (smoothPeriodicTestL2 (productWeakGradient_coord_contDiff hψ i)
        (productWeakGradient_coord_periodic hψ hperiodic i))]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with t
  rw [P.finite_gradient_coordinate_pairing N t i hψ hperiodic]
  ring

/-- The synchronized product-space weak limits inherit the spatial distributional-gradient
identity against every smooth periodic test and bounded time weight. -/
theorem FrozenDriftProblem.synchronized_limit_spatial_derivative_identity
    (P : FrozenDriftProblem) (σ : ℕ → ℕ)
    (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    (hUweak : ∀ v, Tendsto (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    (hGweak : ∀ v, Tendsto (fun n => inner ℝ (P.gradientProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Gprod v)))
    (η : ℝ → ℝ) (hη : MemLp η ⊤ GalerkinTimeMeasure) (i : Fin 2)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) :
    inner ℝ Gprod
        (gradientProductTestLp η
          (scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic)) hη) =
      -inner ℝ Uprod
        (scalarProductTestLp η
          (smoothPeriodicTestL2 (productWeakGradient_coord_contDiff hψ i)
            (productWeakGradient_coord_periodic hψ hperiodic i)) hη) := by
  let gtest := gradientProductTestLp η
    (scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic)) hη
  let utest := scalarProductTestLp η
    (smoothPeriodicTestL2 (productWeakGradient_coord_contDiff hψ i)
      (productWeakGradient_coord_periodic hψ hperiodic i)) hη
  let q : ℕ → ℝ := fun n => inner ℝ (P.gradientProductLp (σ n)) gtest +
    inner ℝ (P.scalarProductLp (σ n)) utest
  have hqzero : ∀ n, q n = 0 := by
    intro n
    have hfinite := P.finite_product_spatial_derivative_identity (σ n) η hη i hψ hperiodic
    change inner ℝ (P.gradientProductLp (σ n)) gtest =
      -inner ℝ (P.scalarProductLp (σ n)) utest at hfinite
    change _ + _ = 0
    rw [hfinite]
    ring
  have hqTendsto : Tendsto q atTop (𝓝 (
      inner ℝ Gprod gtest + inner ℝ Uprod utest)) := by
    exact (hGweak gtest).add (hUweak utest)
  have hqZeroTendsto : Tendsto q atTop (𝓝 0) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
    filter_upwards with n
    exact (hqzero n).symm
  have hsum : inner ℝ Gprod gtest + inner ℝ Uprod utest = 0 :=
    tendsto_nhds_unique hqTendsto hqZeroTendsto
  change inner ℝ Gprod gtest = -inner ℝ Uprod utest
  linarith

/-- The synchronized gradient limit has the spatial distributional derivative pairing of the
weakly continuous scalar path after the product scalar limit is identified. -/
theorem FrozenDriftProblem.synchronized_path_spatial_derivative_identity
    (P : FrozenDriftProblem) (σ : ℕ → ℕ)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    (hPathWeak : ∀ t v, Tendsto
      (fun n => inner ℝ (P.scalarPath (σ n) t) v) atTop
      (𝓝 (inner ℝ (u t) v)))
    (hUweak : ∀ v, Tendsto
      (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    (hGweak : ∀ v, Tendsto
      (fun n => inner ℝ (P.gradientProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Gprod v)))
    (η : ℝ → ℝ) (hηMem : MemLp η ⊤ GalerkinTimeMeasure) (i : Fin 2)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) :
    inner ℝ Gprod
        (gradientProductTestLp η
          (scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic)) hηMem) =
      -∫ t, if ht : t ∈ Icc (0 : ℝ) 1 then
        η t * inner ℝ (u ⟨t, ht⟩)
          (smoothPeriodicTestL2 (productWeakGradient_coord_contDiff hψ i)
            (productWeakGradient_coord_periodic hψ hperiodic i)) else 0
        ∂GalerkinTimeMeasure := by
  let dψT := smoothPeriodicTestL2 (productWeakGradient_coord_contDiff hψ i)
    (productWeakGradient_coord_periodic hψ hperiodic i)
  have hgradient := P.synchronized_limit_spatial_derivative_identity σ Uprod Gprod
    hUweak hGweak η hηMem i hψ hperiodic
  have hscalar := P.productScalar_pairing_eq_path_integral σ u Uprod
    hPathWeak hUweak hηMem dψT
  change inner ℝ Gprod
      (gradientProductTestLp η
        (scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic)) hηMem) =
    -inner ℝ Uprod (scalarProductTestLp η dψT hηMem) at hgradient
  rw [hscalar] at hgradient
  simpa [dψT] using hgradient

end AVenhance.Infra.Parabolic.FourierGalerkin

end
