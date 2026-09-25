/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpBelowTwo
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareZeroTrace
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.H10GradientUpgrade

/-!
# Scalar Poisson gradient estimates below the energy exponent

This file proves the centered-cube `L^q` gradient estimate for a zero-trace
solution of the scalar Poisson equation when `1 < q < 2`.  The proof uses
self-adjoint duality against the already-established divergence-form
Calderón--Zygmund estimate at the conjugate exponent.

Both functions in the mutual-testing step belong to `H¹₀`; no boundary
trace of a gradient coordinate is asserted or used.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace CubeCalderonZygmund

namespace ScalarPoissonGradientBelowTwo

private theorem normalizedVolume_zero_eq_volumeMeasureOn_openCubeSet
    (d : ℕ) :
    (centeredCubeDomain d 0).normalizedVolume =
      volumeMeasureOn (openCubeSet (originCube d 0)) := by
  unfold centeredCubeDomain
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  simp only [cubeVolume, cubeScaleFactor_originCube, zpow_zero, one_pow,
    inv_one, ENNReal.ofReal_one, one_smul, volumeMeasureOn]

private theorem castH10Function_apply {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) (x : Vec d) :
    (hUV ▸ u).toH1Function.toFun x = u.toH1Function.toFun x := by
  subst V
  rfl

private theorem castH10Function_grad {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) (x : Vec d) :
    (hUV ▸ u).toH1Function.grad x = u.toH1Function.grad x := by
  subst V
  rfl

private theorem centeredOpenCube_eq_smul_unitCenteredOpenCube
    {d : ℕ} (m : ℤ) :
    openCubeSet (originCube d m) =
      centeredCubeScale m • openCubeSet (originCube d 0) := by
  simpa only [centeredCubeScale, cubeScaleFactor_originCube] using
    openCubeSet_originCube_eq_smul_originCube_zero (d := d) m

/-- The normalized pullback of an `H¹₀` function from a centered cube to
the centered unit cube.  Its gradient is the unscaled physical gradient. -/
private noncomputable def centeredCubeH10Pullback {d : ℕ} {m : ℤ}
    (v : H10Function (openCubeSet (originCube d m))) :
    H10Function (openCubeSet (originCube d 0)) :=
  (centeredCubeScale m)⁻¹ • H10Function.unscale (centeredCubeScale_pos m)
    (centeredOpenCube_eq_smul_unitCenteredOpenCube m ▸ v)

@[simp] private theorem centeredCubeH10Pullback_apply {d : ℕ} {m : ℤ}
    (v : H10Function (openCubeSet (originCube d m))) (x : Vec d) :
    centeredCubeH10Pullback v x =
      (centeredCubeScale m)⁻¹ * v (centeredCubeScale m • x) := by
  unfold centeredCubeH10Pullback
  change (centeredCubeScale m)⁻¹ *
      (H10Function.unscale (centeredCubeScale_pos m)
        (centeredOpenCube_eq_smul_unitCenteredOpenCube m ▸ v)).toH1Function.toFun x = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_toFun]
  rw [castH10Function_apply]

@[simp] private theorem centeredCubeH10Pullback_grad {d : ℕ} {m : ℤ}
    (v : H10Function (openCubeSet (originCube d m))) (x : Vec d) :
    (centeredCubeH10Pullback v).toH1Function.grad x =
      v.toH1Function.grad (centeredCubeScale m • x) := by
  unfold centeredCubeH10Pullback
  change (centeredCubeScale m)⁻¹ •
      (H10Function.unscale (centeredCubeScale_pos m)
        (centeredOpenCube_eq_smul_unitCenteredOpenCube m ▸ v)).toH1Function.grad x = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_grad]
  rw [castH10Function_grad]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [centeredCubeScale_ne_zero m]

private theorem eLpNorm_centeredCubeH10Pullback_toFun
    {d : ℕ} {m : ℤ} (p : ℝ≥0∞)
    (v : H10Function (openCubeSet (originCube d m)))
    (hv : AEStronglyMeasurable v.toH1Function.toFun
      (centeredCubeDomain d m).normalizedVolume) :
    eLpNorm (centeredCubeH10Pullback v).toH1Function.toFun p
        (centeredCubeDomain d 0).normalizedVolume =
      ENNReal.ofReal (centeredCubeScale m)⁻¹ *
        eLpNorm v.toH1Function.toFun p
          (centeredCubeDomain d m).normalizedVolume := by
  have hcomp := eLpNorm_comp_measurePreserving (p := p) hv
    (centeredCubeDilationMeasurePreserving (d := d) m)
  rw [show (centeredCubeH10Pullback v).toH1Function.toFun =
      (centeredCubeScale m)⁻¹ •
        (v.toH1Function.toFun ∘ centeredCubeDilation m) by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      centeredCubeDilation, centeredCubeH10Pullback_apply]]
  rw [eLpNorm_const_smul, hcomp]
  rw [Real.enorm_eq_ofReal (inv_nonneg.mpr (centeredCubeScale_pos m).le)]

private theorem eLpNorm_centeredCubeH10Pullback_grad
    {d : ℕ} {m : ℤ} (p : ℝ≥0∞)
    (v : H10Function (openCubeSet (originCube d m)))
    (hv : MemLp (hilbertifyVecField v.toH1Function.grad) p
      (centeredCubeDomain d m).normalizedVolume) :
    eLpNorm (hilbertifyVecField (centeredCubeH10Pullback v).toH1Function.grad) p
        (centeredCubeDomain d 0).normalizedVolume =
      eLpNorm (hilbertifyVecField v.toH1Function.grad) p
        (centeredCubeDomain d m).normalizedVolume := by
  have hcomp := eLpNorm_comp_measurePreserving (p := p) hv.aestronglyMeasurable
    (centeredCubeDilationMeasurePreserving (d := d) m)
  rw [show hilbertifyVecField (centeredCubeH10Pullback v).toH1Function.grad =
      hilbertifyVecField v.toH1Function.grad ∘ centeredCubeDilation m by
    funext x
    simp only [hilbertifyVecField, Function.comp_apply, centeredCubeDilation,
      centeredCubeH10Pullback_grad]]
  exact hcomp

/-- Scale-correct normalized `L^p` Poincare control for an `H¹₀` function
on a centered cube, assuming the corresponding unit-cube `W¹ᵖ₀` estimate. -/
theorem centeredCubeH10_value_eLpNorm_le_scale_mul_grad
    {d : ℕ} [NeZero d] (p : FiniteLpExponent)
    (Cp : ℝ) (hCp : 0 ≤ Cp)
    (hPoincare :
      ∀ w : W10pFunction (openCubeSet (originCube d 0)) p.exponent,
        ENNReal.toReal (eLpNorm w.toFun p.exponent
          (volumeMeasureOn (openCubeSet (originCube d 0)))) ≤
          Cp * ∑ i : Fin d, ENNReal.toReal
            (eLpNorm (fun x => w.grad x i) p.exponent
              (volumeMeasureOn (openCubeSet (originCube d 0)))))
    (m : ℤ) (v : H10Function (openCubeSet (originCube d m)))
    (hvgrad : MemLp (hilbertifyVecField v.toH1Function.grad) p.exponent
      (centeredCubeDomain d m).normalizedVolume) :
    eLpNorm v.toH1Function.toFun p.exponent
        (centeredCubeDomain d m).normalizedVolume ≤
      ENNReal.ofReal (Cp * d) * ENNReal.ofReal (centeredCubeScale m) *
        eLpNorm (hilbertifyVecField v.toH1Function.grad) p.exponent
          (centeredCubeDomain d m).normalizedVolume := by
  let w : H10Function (openCubeSet (originCube d 0)) := centeredCubeH10Pullback v
  have hwpull : MemLp (hilbertifyVecField w.toH1Function.grad) p.exponent
      (centeredCubeDomain d 0).normalizedVolume := by
    have hcomp := hvgrad.comp_measurePreserving
      (centeredCubeDilationMeasurePreserving (d := d) m)
    rw [show hilbertifyVecField w.toH1Function.grad =
        hilbertifyVecField v.toH1Function.grad ∘ centeredCubeDilation m by
      funext x
      simp only [w, hilbertifyVecField, Function.comp_apply, centeredCubeDilation,
        centeredCubeH10Pullback_grad]]
    exact hcomp
  rw [normalizedVolume_zero_eq_volumeMeasureOn_openCubeSet] at hwpull
  have hwgrad : GradMemLpOn (openCubeSet (originCube d 0)) p.exponent
      w.toH1Function.grad := by
    intro i
    have hi := hwpull.eval_piLp i
    simpa only [hilbertifyVecField, HilbertVec.ofVec, PiLp.toLp_apply] using hi
  let wp : W10pFunction (openCubeSet (originCube d 0)) p.exponent :=
    w.toW10pOfGradMemLp
      (isOpenBoundedConvexDomain_openCubeSet (originCube d 0)) p hwgrad
  have hunit := hPoincare wp
  rw [show wp.toFun = w.toH1Function.toFun by
      exact H10Function.toW10pOfGradMemLp_toFun _ _ _ _,
    show wp.grad = w.toH1Function.grad by
      exact H10Function.toW10pOfGradMemLp_grad _ _ _ _] at hunit
  have hcoord : ∀ i : Fin d,
      ENNReal.toReal (eLpNorm (fun x => w.toH1Function.grad x i) p.exponent
        (volumeMeasureOn (openCubeSet (originCube d 0)))) ≤
        ENNReal.toReal (eLpNorm (hilbertifyVecField w.toH1Function.grad) p.exponent
          (volumeMeasureOn (openCubeSet (originCube d 0)))) := by
    intro i
    apply ENNReal.toReal_mono hwpull.eLpNorm_ne_top
    exact coordinate_eLpNorm_le_euclidean
      (volumeMeasureOn (openCubeSet (originCube d 0))) p w.toH1Function.grad i
  have hsum :
      ∑ i : Fin d, ENNReal.toReal
          (eLpNorm (fun x => w.toH1Function.grad x i) p.exponent
            (volumeMeasureOn (openCubeSet (originCube d 0)))) ≤
        d * ENNReal.toReal
          (eLpNorm (hilbertifyVecField w.toH1Function.grad) p.exponent
            (volumeMeasureOn (openCubeSet (originCube d 0)))) := by
    calc
      ∑ i : Fin d, ENNReal.toReal
          (eLpNorm (fun x => w.toH1Function.grad x i) p.exponent
            (volumeMeasureOn (openCubeSet (originCube d 0)))) ≤
          ∑ _i : Fin d, ENNReal.toReal
            (eLpNorm (hilbertifyVecField w.toH1Function.grad) p.exponent
              (volumeMeasureOn (openCubeSet (originCube d 0)))) := by
        exact Finset.sum_le_sum fun i _ => hcoord i
      _ = d * ENNReal.toReal
          (eLpNorm (hilbertifyVecField w.toH1Function.grad) p.exponent
            (volumeMeasureOn (openCubeSet (originCube d 0)))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  have hunit' :
      ENNReal.toReal (eLpNorm w.toH1Function.toFun p.exponent
        (volumeMeasureOn (openCubeSet (originCube d 0)))) ≤
        Cp * d * ENNReal.toReal
          (eLpNorm (hilbertifyVecField w.toH1Function.grad) p.exponent
            (volumeMeasureOn (openCubeSet (originCube d 0)))) := by
    exact hunit.trans <| by
      calc
        Cp * ∑ i : Fin d, ENNReal.toReal
            (eLpNorm (fun x => w.toH1Function.grad x i) p.exponent
              (volumeMeasureOn (openCubeSet (originCube d 0)))) ≤
            Cp * (d * ENNReal.toReal
              (eLpNorm (hilbertifyVecField w.toH1Function.grad) p.exponent
                (volumeMeasureOn (openCubeSet (originCube d 0))))) :=
          mul_le_mul_of_nonneg_left hsum hCp
        _ = _ := by ring
  have hvfunMeas : AEStronglyMeasurable v.toH1Function.toFun
      (centeredCubeDomain d m).normalizedVolume := by
    rw [show (centeredCubeDomain d m).normalizedVolume =
        ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
          volume.restrict (openCubeSet (originCube d m)) by
      change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
      rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
        normalizedCubeMeasure, cubeMeasure,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]]
    exact v.toH1Function.memL2.aestronglyMeasurable.mono_ac
      Measure.smul_absolutelyContinuous
  have hvalueEq := eLpNorm_centeredCubeH10Pullback_toFun p.exponent v hvfunMeas
  have hgradEq := eLpNorm_centeredCubeH10Pullback_grad p.exponent v hvgrad
  rw [normalizedVolume_zero_eq_volumeMeasureOn_openCubeSet] at hvalueEq hgradEq
  have hwfun : MemLp w.toH1Function.toFun p.exponent
      (volumeMeasureOn (openCubeSet (originCube d 0))) := by
    simpa only [wp, H10Function.toW10pOfGradMemLp_toFun] using wp.memLp
  have hprodtop : ENNReal.ofReal (centeredCubeScale m)⁻¹ *
      eLpNorm v.toH1Function.toFun p.exponent
        (centeredCubeDomain d m).normalizedVolume ≠ ∞ := by
    rw [← hvalueEq]
    exact hwfun.eLpNorm_ne_top
  have hvtop : eLpNorm v.toH1Function.toFun p.exponent
      (centeredCubeDomain d m).normalizedVolume ≠ ∞ := by
    intro hvtop
    apply hprodtop
    rw [hvtop, ENNReal.mul_top]
    exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (centeredCubeScale_pos m))
  rw [hvalueEq, hgradEq] at hunit'
  have hrighttop : ENNReal.ofReal (Cp * d) * ENNReal.ofReal (centeredCubeScale m) *
      eLpNorm (hilbertifyVecField v.toH1Function.grad) p.exponent
        (centeredCubeDomain d m).normalizedVolume ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      hvgrad.eLpNorm_ne_top
  apply (ENNReal.toReal_le_toReal hvtop hrighttop).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (mul_nonneg hCp (Nat.cast_nonneg d)),
      ENNReal.toReal_ofReal (centeredCubeScale_pos m).le] using
    (show ENNReal.toReal
        (eLpNorm v.toH1Function.toFun p.exponent
          (centeredCubeDomain d m).normalizedVolume) ≤
        (Cp * d) * centeredCubeScale m *
          ENNReal.toReal
            (eLpNorm (hilbertifyVecField v.toH1Function.grad) p.exponent
              (centeredCubeDomain d m).normalizedVolume) by
      have hs := centeredCubeScale_pos m
      have hcancel : (centeredCubeScale m)⁻¹ * centeredCubeScale m = 1 :=
        inv_mul_cancel₀ hs.ne'
      have hunit'' := hunit'
      rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (inv_nonneg.mpr hs.le)] at hunit''
      calc
        ENNReal.toReal
            (eLpNorm v.toH1Function.toFun p.exponent
              (centeredCubeDomain d m).normalizedVolume) =
            centeredCubeScale m *
              ((centeredCubeScale m)⁻¹ * ENNReal.toReal
                (eLpNorm v.toH1Function.toFun p.exponent
                  (centeredCubeDomain d m).normalizedVolume)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
        _ ≤ centeredCubeScale m *
            (Cp * d * ENNReal.toReal
              (eLpNorm (hilbertifyVecField v.toH1Function.grad) p.exponent
                (centeredCubeDomain d m).normalizedVolume)) :=
          mul_le_mul_of_nonneg_left hunit'' hs.le
        _ = (Cp * d) * centeredCubeScale m *
            ENNReal.toReal
              (eLpNorm (hilbertifyVecField v.toH1Function.grad) p.exponent
                (centeredCubeDomain d m).normalizedVolume) := by ring)

private theorem centeredCube_scalarPoisson_divergence_cross_pairing
    {d : ℕ} (m : ℤ) {sigma0 : ℝ}
    (u v : H10Function (openCubeSet (originCube d m)))
    (F : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : ∀ phi : H10Function (openCubeSet (originCube d m)),
      sigma0 * ∫ x, vecDot (u.toH1Function.grad x) (phi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume =
        ∫ x, F x * phi.toH1Function.toFun x
          ∂(centeredCubeDomain d m).normalizedVolume)
    (hv : ∀ phi : H10Function (openCubeSet (originCube d m)),
      sigma0 * ∫ x, vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume =
        -∫ x, vecDot (G x) (phi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume) :
    ∫ x, vecDot (u.toH1Function.grad x) (G x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      -∫ x, F x * v.toH1Function.toFun x
        ∂(centeredCubeDomain d m).normalizedVolume := by
  have hsymm :
      ∫ x, vecDot (v.toH1Function.grad x) (u.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume =
        ∫ x, vecDot (u.toH1Function.grad x) (v.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume := by
    apply integral_congr_ae
    filter_upwards with x
    exact vecDot_comm _ _
  have hneg :
      -(∫ x, vecDot (G x) (u.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume) =
        ∫ x, F x * v.toH1Function.toFun x
          ∂(centeredCubeDomain d m).normalizedVolume := by
    calc
      -(∫ x, vecDot (G x) (u.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume) =
          sigma0 * ∫ x, vecDot (v.toH1Function.grad x) (u.toH1Function.grad x)
            ∂(centeredCubeDomain d m).normalizedVolume := (hv u).symm
      _ = sigma0 * ∫ x, vecDot (u.toH1Function.grad x) (v.toH1Function.grad x)
            ∂(centeredCubeDomain d m).normalizedVolume := by rw [hsymm]
      _ = ∫ x, F x * v.toH1Function.toFun x
            ∂(centeredCubeDomain d m).normalizedVolume := hu v
  rw [neg_eq_iff_eq_neg] at hneg
  calc
    ∫ x, vecDot (u.toH1Function.grad x) (G x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      ∫ x, vecDot (G x) (u.toH1Function.grad x)
        ∂(centeredCubeDomain d m).normalizedVolume := by
      apply integral_congr_ae
      filter_upwards with x
      exact vecDot_comm _ _
    _ = _ := hneg

private theorem abs_integral_mul_le_eLpNorm_toReal_mul
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p r : ℝ≥0∞} [ENNReal.HolderConjugate p r]
    {F G : α → ℝ}
    (hF : MemLp F p μ) (hG : MemLp G r μ)
    (hFG : Integrable (fun x => F x * G x) μ) :
    |∫ x, F x * G x ∂μ| ≤
      (eLpNorm F p μ).toReal * (eLpNorm G r μ).toReal := by
  let f : α → ℝ := fun x => F x * G x
  have hfLp : MemLp f 1 μ := by
    rw [memLp_one_iff_integrable]
    exact hFG
  have hnorm : ENNReal.ofReal |∫ x, f x ∂μ| ≤ eLpNorm f 1 μ := by
    simpa only [Real.enorm_eq_ofReal_abs] using
      (enorm_integral_le_lintegral_enorm (μ := μ) f).trans_eq
        eLpNorm_one_eq_lintegral_enorm.symm
  have hholder : eLpNorm f 1 μ ≤ eLpNorm F p μ * eLpNorm G r μ := by
    simpa only [f, Pi.smul_apply, smul_eq_mul] using!
      eLpNorm_smul_le_mul_eLpNorm hG.aestronglyMeasurable hF.aestronglyMeasurable
  have hfirst := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    hfLp.eLpNorm_ne_top).mpr hnorm
  have hright : eLpNorm F p μ * eLpNorm G r μ ≠ ∞ :=
    ENNReal.mul_ne_top hF.eLpNorm_ne_top hG.eLpNorm_ne_top
  have hsecond := (ENNReal.toReal_le_toReal hfLp.eLpNorm_ne_top hright).mpr hholder
  calc
    |∫ x, F x * G x ∂μ| = ENNReal.toReal (ENNReal.ofReal |∫ x, f x ∂μ|) := by
      rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    _ ≤ ENNReal.toReal (eLpNorm f 1 μ) := hfirst
    _ ≤ ENNReal.toReal (eLpNorm F p μ * eLpNorm G r μ) := hsecond
    _ = _ := ENNReal.toReal_mul

private noncomputable def radialTruncationL2LpField
    {d : ℕ} [NeZero d] (m : ℤ) (q : FiniteLpExponent)
    (u : H10Function (openCubeSet (originCube d m))) (n : ℕ) :
    CubeEuclideanL2LpField (originCube d m) q.conjugate := by
  let U : Set (Vec d) := openCubeSet (originCube d m)
  let F : Vec d → Vec d := u.toH1Function.grad
  let G : Vec d → Vec d := INTERNAL.vectorRadialTruncation q.exponent.toReal n F
  letI : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).isFiniteMeasure_restrict_volume
  have hFraw : AEStronglyMeasurable (fun x => HilbertVec.ofVec (F x))
      (volumeMeasureOn U) := by
    simpa only [F, hilbertifyVecField] using!
      (memHilbertVectorL2_hilbertifyVecField
        u.toH1Function.grad_memVectorL2).aestronglyMeasurable
  have hqone : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hraw : MemLp (INTERNAL.hilbertRadialTruncation q.exponent.toReal n
      (fun x => HilbertVec.ofVec (F x))) q.conjugate.exponent
      (volumeMeasureOn U) :=
    INTERNAL.memLp_hilbertRadialTruncation hqone n hFraw
  have hraw2 : MemLp (INTERNAL.hilbertRadialTruncation q.exponent.toReal n
      (fun x => HilbertVec.ofVec (F x))) 2 (volumeMeasureOn U) :=
    INTERNAL.memLp_hilbertRadialTruncation hqone n hFraw
  refine { toCubeEuclideanLpField := ⟨G, ?_⟩, euclideanMemL2 := ?_ }
  · rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    simpa only [G, INTERNAL.vectorRadialTruncation, HilbertVec.ofVec_toVec] using
      hraw.smul_measure ENNReal.ofReal_ne_top
  · rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    simpa only [G, INTERNAL.vectorRadialTruncation, HilbertVec.ofVec_toVec] using
      hraw2.smul_measure ENNReal.ofReal_ne_top

private theorem radialTruncation_memVectorL2
    {d : ℕ} [NeZero d] (m : ℤ) (q : FiniteLpExponent)
    (u : H10Function (openCubeSet (originCube d m))) (n : ℕ) :
    MemVectorL2 (openCubeSet (originCube d m))
      (radialTruncationL2LpField m q u n).toField := by
  let U : Set (Vec d) := openCubeSet (originCube d m)
  let F : Vec d → Vec d := u.toH1Function.grad
  let : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).isFiniteMeasure_restrict_volume
  have hFraw : AEStronglyMeasurable (fun x => HilbertVec.ofVec (F x))
      (volumeMeasureOn U) := by
    simpa only [F, hilbertifyVecField] using!
      (memHilbertVectorL2_hilbertifyVecField
        u.toH1Function.grad_memVectorL2).aestronglyMeasurable
  have hqone : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  simpa only [radialTruncationL2LpField, F,
    INTERNAL.vectorRadialTruncation, HilbertVec.ofVec_toVec] using
    INTERNAL.memVectorL2_vectorRadialTruncation U hqone n F hFraw

private theorem centeredCube_integrable_vecDot
    {d : ℕ} (m : ℤ) {F G : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet (originCube d m)) F)
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    Integrable (fun x => vecDot (F x) (G x))
      (centeredCubeDomain d m).normalizedVolume := by
  rw [show (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
    change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
    rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]]
  exact (integrableOn_vecDot_of_memVectorL2 hF hG).smul_measure ENNReal.ofReal_ne_top

private theorem centeredCube_memLp_gradient_two
    {d : ℕ} {m : ℤ} (u : H10Function (openCubeSet (originCube d m))) :
    MemLp (hilbertifyVecField u.toH1Function.grad) 2
      (centeredCubeDomain d m).normalizedVolume := by
  rw [show (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
    change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
    rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]]
  exact (memHilbertVectorL2_hilbertifyVecField
    u.toH1Function.grad_memVectorL2).smul_measure ENNReal.ofReal_ne_top

private theorem centeredCube_memLp_value_two
    {d : ℕ} {m : ℤ} (u : H10Function (openCubeSet (originCube d m))) :
    MemLp u.toH1Function.toFun 2 (centeredCubeDomain d m).normalizedVolume := by
  rw [show (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
    change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
    rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]]
  exact u.toH1Function.memL2.smul_measure ENNReal.ofReal_ne_top

private theorem ofReal_vecDot_radialTruncation_eq_truncatedMoment
    {α : Type*} {d : ℕ} {q : ℝ} (hq : 1 < q) (n : ℕ)
    (F : α → Vec d) (x : α) :
    ENNReal.ofReal (vecDot (F x) (INTERNAL.vectorRadialTruncation q n F x)) =
      INTERNAL.truncatedMoment q n (fun y => HilbertVec.ofVec (F y)) x := by
  rw [vecDot_comm, INTERNAL.vecDot_vectorRadialTruncation_self hq n F]
  by_cases hx : euclideanNorm (F x) ≤ (n : ℝ)
  · have hx' : ‖HilbertVec.ofVec (F x)‖ ≤ (n : ℝ) := by
      simpa only [euclideanNorm_eq_norm_ofVec] using hx
    have hxmem : x ∈ {y | ‖HilbertVec.ofVec (F y)‖ ≤ (n : ℝ)} := hx'
    rw [if_pos hx, INTERNAL.truncatedMoment, Set.indicator_of_mem hxmem]
    rw [← ofReal_norm (HilbertVec.ofVec (F x))]
    simpa only [euclideanNorm_eq_norm_ofVec] using
      (ENNReal.ofReal_rpow_of_nonneg
        (norm_nonneg (HilbertVec.ofVec (F x))) (by linarith : 0 ≤ q)).symm
  · have hx' : ¬ ‖HilbertVec.ofVec (F x)‖ ≤ (n : ℝ) := by
      simpa only [euclideanNorm_eq_norm_ofVec] using hx
    have hxmem : x ∉ {y | ‖HilbertVec.ofVec (F y)‖ ≤ (n : ℝ)} := hx'
    rw [if_neg hx, INTERNAL.truncatedMoment, Set.indicator_of_notMem hxmem]
    exact ENNReal.ofReal_zero

private theorem eLpNorm_radialTruncation_rpow_conjugate_eq_truncatedMoment
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    (q : FiniteLpExponent) (n : ℕ) (F : α → HilbertVec d) :
    (eLpNorm (INTERNAL.hilbertRadialTruncation q.exponent.toReal n F)
      q.conjugate.exponent μ) ^ q.conjugate.exponent.toReal =
      ∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ne_of_gt (zero_lt_one.trans q.conjugate.one_lt)) q.conjugate.lt_top.ne,
    ← ENNReal.rpow_mul]
  have hqzero : q.conjugate.exponent.toReal ≠ 0 :=
    (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans q.conjugate.one_lt))
      q.conjugate.lt_top.ne).ne'
  rw [one_div, inv_mul_cancel₀ hqzero, ENNReal.rpow_one]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg,
    INTERNAL.norm_hilbertRadialTruncation_rpow_conjugate]
  by_cases hx : ‖F x‖ ≤ (n : ℝ)
  · have hxmem : x ∈ {y | ‖F y‖ ≤ (n : ℝ)} := hx
    rw [if_pos hx, INTERNAL.truncatedMoment, Set.indicator_of_mem hxmem,
      ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg]
  · have hxmem : x ∉ {y | ‖F y‖ ≤ (n : ℝ)} := hx
    rw [if_neg hx, INTERNAL.truncatedMoment, Set.indicator_of_notMem hxmem]
    exact ENNReal.ofReal_zero

private theorem eLpNorm_le_of_truncated_cross_bound
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ} {F : α → HilbertVec d} {A : ℝ≥0∞}
    (hq : 1 < q) (hF : AEStronglyMeasurable F μ)
    (htrunc : ∀ n : ℕ,
      (∫⁻ x, INTERNAL.truncatedMoment q n F x ∂μ) ≠ ∞ ∧
      (∫⁻ x, INTERNAL.truncatedMoment q n F x ∂μ) ≤
        A * (∫⁻ x, INTERNAL.truncatedMoment q n F x ∂μ) ^ (1 - q⁻¹)) :
    eLpNorm F (ENNReal.ofReal q) μ ≤ A := by
  have root_le_of_le_mul_rpow : ∀ {J B : ℝ≥0∞}, J ≠ ∞ →
      J ≤ B * J ^ (1 - q⁻¹) → J ≤ B ^ q := by
    intro J B hJtop hJ
    by_cases hJzero : J = 0
    · rw [hJzero]
      exact bot_le
    have hJpos : 0 < J := lt_of_le_of_ne bot_le (Ne.symm hJzero)
    have he : 0 ≤ 1 - q⁻¹ := (sub_pos.mpr (inv_lt_one_of_one_lt₀ hq)).le
    have hBpos : 0 < J ^ (1 - q⁻¹) := ENNReal.rpow_pos hJpos hJtop
    have hBtop : J ^ (1 - q⁻¹) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg he hJtop
    have hfac : J = J ^ (1 - q⁻¹) * J ^ q⁻¹ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ he (inv_nonneg.mpr (by linarith : 0 ≤ q))]
      rw [show (1 - q⁻¹) + q⁻¹ = 1 by ring, ENNReal.rpow_one]
    have hroot : J ^ q⁻¹ ≤ B := by
      apply (ENNReal.mul_le_mul_iff_left hBpos.ne' hBtop).mp
      calc
        J ^ q⁻¹ * J ^ (1 - q⁻¹) = J ^ (1 - q⁻¹) * J ^ q⁻¹ := mul_comm _ _
        _ = J := hfac.symm
        _ ≤ B * J ^ (1 - q⁻¹) := hJ
    calc
      J = (J ^ q⁻¹) ^ q := by
        rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (by linarith : q ≠ 0),
          ENNReal.rpow_one]
      _ ≤ B ^ q := ENNReal.rpow_le_rpow hroot (by linarith)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < q)).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ q)]
  have hmoment : (∫⁻ x, ‖F x‖ₑ ^ q ∂μ) ≤ A ^ q := by
    rw [INTERNAL.lintegral_enorm_rpow_eq_iSup_lintegral_truncatedMoment hF]
    exact iSup_le fun n => root_le_of_le_mul_rpow (htrunc n).1 (htrunc n).2
  calc
    (∫⁻ x, ‖F x‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (A ^ q) ^ (1 / q) :=
      ENNReal.rpow_le_rpow hmoment (by positivity)
    _ = A := by
      rw [show (1 / q : ℝ) = q⁻¹ by ring, ← ENNReal.rpow_mul,
        mul_inv_cancel₀ (by linarith : q ≠ 0), ENNReal.rpow_one]

end ScalarPoissonGradientBelowTwo

/-- Below the energy exponent, a supplied zero-trace solution of the scalar
Poisson equation on a centered cube has the scale-correct normalized `L^q`
gradient bound.  The source is represented directly by a scalar field with
separate normalized `L²` and `L^q` membership. -/
theorem centeredCubeH10ScalarPoisson_gradient_cz_of_lt_two
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (hq : q.exponent.toReal < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (F : Vec d → ℝ) (u : H10Function (openCubeSet (originCube d m))),
      MemLp F 2 (centeredCubeDomain d m).normalizedVolume →
      MemLp F q.exponent (centeredCubeDomain d m).normalizedVolume →
      0 < sigma0 →
      (∀ phi : H10Function (openCubeSet (originCube d m)),
        sigma0 * ∫ x, vecDot (u.toH1Function.grad x) (phi.toH1Function.grad x)
            ∂(centeredCubeDomain d m).normalizedVolume =
          ∫ x, F x * phi.toH1Function.toFun x
            ∂(centeredCubeDomain d m).normalizedVolume) →
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
          u.toH1Function.grad ≤
        C * ENNReal.ofReal (cubeScaleFactor (originCube d m)) *
          (ENNReal.ofReal sigma0)⁻¹ *
            eLpNorm F q.exponent (centeredCubeDomain d m).normalizedVolume := by
  obtain ⟨Ccz, hCczTop, hCcz⟩ := centeredCubeH10ScalarDivergence_cz_of_two_lt d
    q.conjugate (INTERNAL.conjugate_toReal_gt_two_of_lt_two q hq)
  obtain ⟨Cp, hCp, hPoincare⟩ :=
    W10pFunction.exists_poincare_constant_of_isOpenBoundedConvexDomain
      q.conjugate.one_lt q.conjugate.lt_top.ne
      (isOpenBoundedConvexDomain_openCubeSet (originCube d 0))
  let P : ℝ≥0∞ := ENNReal.ofReal (Cp * d)
  let C : ℝ≥0∞ := P * Ccz
  have hPTop : P ≠ ∞ := ENNReal.ofReal_ne_top
  have hCTop : C ≠ ∞ := ENNReal.mul_ne_top hPTop hCczTop.ne
  refine ⟨C, hCTop.lt_top, ?_⟩
  intro m sigma0 F u hF2 hFq hsigma0 hu
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let Ugrad : Vec d → HilbertVec d := hilbertifyVecField u.toH1Function.grad
  let : ENNReal.HolderConjugate q.exponent q.conjugate.exponent := q.holderConjugate
  have hqreal : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hUtwo : MemLp Ugrad 2 μ := by
    simpa only [Ugrad, μ] using
      ScalarPoissonGradientBelowTwo.centeredCube_memLp_gradient_two u
  have hUmeas : AEStronglyMeasurable Ugrad μ := hUtwo.aestronglyMeasurable
  let A : ℝ≥0∞ := C * ENNReal.ofReal (cubeScaleFactor (originCube d m)) *
    (ENNReal.ofReal sigma0)⁻¹ * eLpNorm F q.exponent μ
  have hmain : eLpNorm Ugrad q.exponent μ ≤ A := by
    rw [← ENNReal.ofReal_toReal q.lt_top.ne]
    apply ScalarPoissonGradientBelowTwo.eLpNorm_le_of_truncated_cross_bound
      hqreal hUmeas
    intro n
    let Gfield := ScalarPoissonGradientBelowTwo.radialTruncationL2LpField m q u n
    let G : Vec d → Vec d := Gfield.toField
    have hGtwo : MemVectorL2 (openCubeSet (originCube d m)) G := by
      simpa only [G, Gfield] using
        ScalarPoissonGradientBelowTwo.radialTruncation_memVectorL2 m q u n
    let v := openCubeSetScalarDivergenceSolution (originCube d m) hsigma0 G hGtwo
    have hk : Integrable (fun x => vecDot (u.toH1Function.grad x) (G x)) μ := by
      simpa only [μ] using ScalarPoissonGradientBelowTwo.centeredCube_integrable_vecDot m
        u.toH1Function.grad_memVectorL2 hGtwo
    have hk0 : 0 ≤ᵐ[μ] fun x => vecDot (u.toH1Function.grad x) (G x) := by
      filter_upwards with x
      change 0 ≤ vecDot (u.toH1Function.grad x)
        (INTERNAL.vectorRadialTruncation q.exponent.toReal n u.toH1Function.grad x)
      rw [vecDot_comm, INTERNAL.vecDot_vectorRadialTruncation_self hqreal]
      split_ifs
      · exact Real.rpow_nonneg (euclideanNorm_nonneg _) _
      · exact le_rfl
    have hpoint : ∀ᵐ x ∂μ, ENNReal.ofReal
        (vecDot (u.toH1Function.grad x) (G x)) =
          INTERNAL.truncatedMoment q.exponent.toReal n Ugrad x := by
      filter_upwards with x
      simpa only [Ugrad, G, Gfield] using!
        ScalarPoissonGradientBelowTwo.ofReal_vecDot_radialTruncation_eq_truncatedMoment
          hqreal n u.toH1Function.grad x
    have hJ : (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n Ugrad x ∂μ) =
        ENNReal.ofReal (∫ x, vecDot (u.toH1Function.grad x) (G x) ∂μ) :=
      INTERNAL.lintegral_truncatedMoment_eq_ofReal_integral hk hk0 hpoint
    refine ⟨?_, ?_⟩
    · rw [hJ]
      exact ENNReal.ofReal_ne_top
    have hvsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 v
        Gfield.toLpTwo := by
      intro phi
      simpa only [v, G, Gfield] using!
        INTERNAL.openCubeSetScalarDivergenceSolution_normalized_weak
          m hsigma0 G hGtwo phi
    have hvCZ := hCcz m sigma0 Gfield v hsigma0 hvsolution
    have hGq : MemLp (hilbertifyVecField G) q.conjugate.exponent μ := by
      simpa only [μ, G, Gfield, centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
        hilbertifyVecField] using! Gfield.euclideanMemLp
    have hVtwo : MemLp (hilbertifyVecField v.toH1Function.grad) 2 μ := by
      simpa only [v, μ] using
        ScalarPoissonGradientBelowTwo.centeredCube_memLp_gradient_two v
    have hVgradBound : eLpNorm (hilbertifyVecField v.toH1Function.grad)
        q.conjugate.exponent μ ≤ Ccz * (ENNReal.ofReal sigma0)⁻¹ *
          eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ := by
      simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
        BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
        eLpNorm_norm, μ, v, G, Gfield, hilbertifyVecField] using! hvCZ
    have hVq : MemLp (hilbertifyVecField v.toH1Function.grad)
        q.conjugate.exponent μ := by
      refine ⟨hVtwo.aestronglyMeasurable, ?_⟩
      exact lt_of_le_of_lt hVgradBound <| ENNReal.mul_lt_top
        (ENNReal.mul_lt_top hCczTop
          (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hsigma0)))
        hGq.eLpNorm_lt_top
    have hVvalueBound : eLpNorm v.toH1Function.toFun q.conjugate.exponent μ ≤
        P * ENNReal.ofReal (centeredCubeScale m) *
          eLpNorm (hilbertifyVecField v.toH1Function.grad)
            q.conjugate.exponent μ := by
      simpa only [P] using
        ScalarPoissonGradientBelowTwo.centeredCubeH10_value_eLpNorm_le_scale_mul_grad
          q.conjugate Cp hCp hPoincare m v hVq
    have hVvalueTwo : MemLp v.toH1Function.toFun 2 μ := by
      simpa only [v, μ] using
        ScalarPoissonGradientBelowTwo.centeredCube_memLp_value_two v
    have hVvalueQ : MemLp v.toH1Function.toFun q.conjugate.exponent μ := by
      refine ⟨hVvalueTwo.aestronglyMeasurable, ?_⟩
      exact lt_of_le_of_lt hVvalueBound <| ENNReal.mul_lt_top
        (ENNReal.mul_lt_top hPTop.lt_top ENNReal.ofReal_lt_top)
        hVq.eLpNorm_lt_top
    have hFV : Integrable (fun x => F x * v.toH1Function.toFun x) μ := by
      rw [← memLp_one_iff_integrable]
      exact hVvalueTwo.mul' hF2
    have hcross :=
      ScalarPoissonGradientBelowTwo.centeredCube_scalarPoisson_divergence_cross_pairing
        m u v F G hu
        (INTERNAL.openCubeSetScalarDivergenceSolution_normalized_weak
          m hsigma0 G hGtwo)
    have hholder := ScalarPoissonGradientBelowTwo.abs_integral_mul_le_eLpNorm_toReal_mul
      hFq hVvalueQ hFV
    have hGmoment : (eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ) ^
        q.conjugate.exponent.toReal =
          ∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n Ugrad x ∂μ := by
      simpa only [μ, Ugrad, G, Gfield, hilbertifyVecField] using!
        ScalarPoissonGradientBelowTwo.eLpNorm_radialTruncation_rpow_conjugate_eq_truncatedMoment
          q n Ugrad
    have hreal : q.exponent.toReal.HolderConjugate
        q.conjugate.exponent.toReal := ENNReal.HolderConjugate.toReal hqreal
    have hexp : (q.conjugate.exponent.toReal)⁻¹ =
        1 - q.exponent.toReal⁻¹ := by
      have hsum := hreal.one_div_add_one_div
      rw [one_div] at hsum
      norm_num at hsum
      linarith
    have hGnorm : eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ =
        (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n Ugrad x ∂μ) ^
          (1 - q.exponent.toReal⁻¹) := by
      have hr0 : q.conjugate.exponent.toReal ≠ 0 :=
        (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans q.conjugate.one_lt))
          q.conjugate.lt_top.ne).ne'
      calc
        eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ =
            (eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ ^
              q.conjugate.exponent.toReal) ^ (q.conjugate.exponent.toReal)⁻¹ := by
          rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hr0, ENNReal.rpow_one]
        _ = (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n Ugrad x ∂μ) ^
            (q.conjugate.exponent.toReal)⁻¹ := by rw [hGmoment]
        _ = _ := by rw [hexp]
    calc
      ∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n Ugrad x ∂μ =
          ENNReal.ofReal (∫ x, vecDot (u.toH1Function.grad x) (G x) ∂μ) := hJ
      _ = ENNReal.ofReal (-∫ x, F x * v.toH1Function.toFun x ∂μ) := by
        rw [hcross]
      _ ≤ ENNReal.ofReal |∫ x, F x * v.toH1Function.toFun x ∂μ| :=
        ENNReal.ofReal_le_ofReal (neg_le_abs _)
      _ ≤ ENNReal.ofReal ((eLpNorm F q.exponent μ).toReal *
          (eLpNorm v.toH1Function.toFun q.conjugate.exponent μ).toReal) :=
        ENNReal.ofReal_le_ofReal hholder
      _ = eLpNorm F q.exponent μ *
          eLpNorm v.toH1Function.toFun q.conjugate.exponent μ := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hFq.eLpNorm_lt_top.ne,
          ENNReal.ofReal_toReal hVvalueQ.eLpNorm_lt_top.ne]
      _ ≤ eLpNorm F q.exponent μ *
          (P * ENNReal.ofReal (centeredCubeScale m) *
            (Ccz * (ENNReal.ofReal sigma0)⁻¹ *
              eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ)) := by
        gcongr
        exact hVvalueBound.trans <| by gcongr
      _ = A * (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n Ugrad x ∂μ) ^
          (1 - q.exponent.toReal⁻¹) := by
        rw [hGnorm]
        dsimp only [A, C]
        rw [cubeScaleFactor_originCube]
        ac_rfl
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
    eLpNorm_norm, Ugrad, μ, A] using! hmain

end CubeCalderonZygmund

end
end Homogenization
