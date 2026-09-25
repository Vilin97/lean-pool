/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpDuality
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.CenteredCubeEuclideanL2

/-!
# Below-two support for cube Calderón--Zygmund estimates

This file isolates the self-adjoint weak-form calculation used to pass from
the already-established above-two estimate to `1 < q < 2`.  It deliberately
exports no source-facing Calderón--Zygmund theorem: the statements here only
turn the canonical adjoint solution into a normalized weak solution and
identify the two cross pairings.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund
namespace INTERNAL

/-- Two scalar divergence weak equations can be tested against one another.
The scalar coefficient cancels by symmetry of the Euclidean dot product; no
positivity assumption is needed for this algebraic cross-pairing identity. -/
theorem scalarDivergence_cross_pairing
    {d : ℕ} {U : Set (Vec d)} {sigma0 : ℝ}
    (u v : H10Function U) (h G : Vec d → Vec d)
    (hu : ∀ psi : H10Function U,
      sigma0 * ∫ x in U,
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        -∫ x in U, vecDot (h x) (psi.toH1Function.grad x) ∂volume)
    (hv : ∀ psi : H10Function U,
      sigma0 * ∫ x in U,
          vecDot (v.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        -∫ x in U, vecDot (G x) (psi.toH1Function.grad x) ∂volume) :
    ∫ x in U, vecDot (u.toH1Function.grad x) (G x) ∂volume =
      ∫ x in U, vecDot (h x) (v.toH1Function.grad x) ∂volume := by
  have hsymm :
      ∫ x in U, vecDot (v.toH1Function.grad x) (u.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (u.toH1Function.grad x) (v.toH1Function.grad x) ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    exact vecDot_comm _ _
  have hneg :
      -(∫ x in U, vecDot (G x) (u.toH1Function.grad x) ∂volume) =
        -(∫ x in U, vecDot (h x) (v.toH1Function.grad x) ∂volume) := by
    calc
      -(∫ x in U, vecDot (G x) (u.toH1Function.grad x) ∂volume) =
          sigma0 * ∫ x in U,
            vecDot (v.toH1Function.grad x) (u.toH1Function.grad x) ∂volume :=
        (hv u).symm
      _ = sigma0 * ∫ x in U,
            vecDot (u.toH1Function.grad x) (v.toH1Function.grad x) ∂volume := by
        rw [hsymm]
      _ = -(∫ x in U, vecDot (h x) (v.toH1Function.grad x) ∂volume) := hu v
  have hpair :
      ∫ x in U, vecDot (G x) (u.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (h x) (v.toH1Function.grad x) ∂volume :=
    neg_injective hneg
  calc
    ∫ x in U, vecDot (u.toH1Function.grad x) (G x) ∂volume =
        ∫ x in U, vecDot (G x) (u.toH1Function.grad x) ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      exact vecDot_comm _ _
    _ = _ := hpair

/-- The same cross-pairing calculation on a centered cube with normalized
volume.  This is the form consumed by the finite-exponent supplied-solution
predicate, so the below-two argument never needs to expose a normalization
cancellation to a caller. -/
theorem centeredCube_scalarDivergence_cross_pairing
    {d : ℕ} (m : ℤ) {sigma0 : ℝ}
    (u v : H10Function (openCubeSet (originCube d m))) (h G : Vec d → Vec d)
    (hu : ∀ psi : H10Function (openCubeSet (originCube d m)),
      sigma0 * ∫ x, vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume =
        -∫ x, vecDot (h x) (psi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume)
    (hv : ∀ psi : H10Function (openCubeSet (originCube d m)),
      sigma0 * ∫ x, vecDot (v.toH1Function.grad x) (psi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume =
        -∫ x, vecDot (G x) (psi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume) :
    ∫ x, vecDot (u.toH1Function.grad x) (G x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      ∫ x, vecDot (h x) (v.toH1Function.grad x)
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
        -(∫ x, vecDot (h x) (v.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume) := by
    calc
      -(∫ x, vecDot (G x) (u.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume) =
          sigma0 * ∫ x, vecDot (v.toH1Function.grad x) (u.toH1Function.grad x)
            ∂(centeredCubeDomain d m).normalizedVolume := (hv u).symm
      _ = sigma0 * ∫ x, vecDot (u.toH1Function.grad x) (v.toH1Function.grad x)
            ∂(centeredCubeDomain d m).normalizedVolume := by rw [hsymm]
      _ = -(∫ x, vecDot (h x) (v.toH1Function.grad x)
            ∂(centeredCubeDomain d m).normalizedVolume) := hu v
  have hpair :
      ∫ x, vecDot (G x) (u.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume =
        ∫ x, vecDot (h x) (v.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume := neg_injective hneg
  calc
    ∫ x, vecDot (u.toH1Function.grad x) (G x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      ∫ x, vecDot (G x) (u.toH1Function.grad x)
        ∂(centeredCubeDomain d m).normalizedVolume := by
        apply integral_congr_ae
        filter_upwards with x
        exact vecDot_comm _ _
    _ = _ := hpair

/-- The radial test field recovers the corresponding truncated gradient moment
under any measure. -/
theorem integral_vecDot_vectorRadialTruncation_eq_truncatedMoment
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    (q : ℝ) (hq : 1 < q) (n : ℕ) (F : α → Vec d) :
    ∫ x, vecDot (F x) (vectorRadialTruncation q n F x) ∂μ =
      ∫ x, if euclideanNorm (F x) ≤ (n : ℝ) then
        euclideanNorm (F x) ^ q else 0 ∂μ := by
  apply integral_congr_ae
  filter_upwards with x
  rw [vecDot_comm]
  exact vecDot_vectorRadialTruncation_self hq n F x

/-- Uniform estimates for radial truncations imply the full ENNReal moment,
without presupposing the conclusion that the original field is in `L^q`. -/
theorem lintegral_enorm_rpow_le_of_truncatedMoment
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ} {F : α → HilbertVec d} {A : ℝ≥0∞}
    (hF : AEStronglyMeasurable F μ)
    (htrunc : ∀ n : ℕ, ∫⁻ x, truncatedMoment q n F x ∂μ ≤ A) :
    (∫⁻ x, ‖F x‖ₑ ^ q ∂μ) ≤ A := by
  rw [lintegral_enorm_rpow_eq_iSup_lintegral_truncatedMoment hF]
  exact iSup_le htrunc

/-- A uniform bound for radial truncations supplies the missing `L^q`
membership once its right-hand side is finite. -/
theorem memLp_of_truncatedMoment_bound
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ} {F : α → HilbertVec d} {A : ℝ≥0∞}
    (hq : 0 < q) (hF : AEStronglyMeasurable F μ)
    (hA : A ≠ ∞)
    (htrunc : ∀ n : ℕ, ∫⁻ x, truncatedMoment q n F x ∂μ ≤ A) :
    MemLp F (ENNReal.ofReal q) μ := by
  refine ⟨hF, ?_⟩
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_pos.mpr hq |>.ne') ENNReal.ofReal_ne_top).mpr
  rw [ENNReal.toReal_ofReal hq.le]
  have hmoment := lintegral_enorm_rpow_le_of_truncatedMoment hF htrunc
  exact lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hA hmoment)

/-- The corresponding direct norm consequence of the truncated-moment
estimate. -/
theorem eLpNorm_le_rpow_of_truncatedMoment
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ} {F : α → HilbertVec d} {A : ℝ≥0∞}
    (hq : 0 < q) (hF : AEStronglyMeasurable F μ)
    (htrunc : ∀ n : ℕ, ∫⁻ x, truncatedMoment q n F x ∂μ ≤ A) :
    eLpNorm F (ENNReal.ofReal q) μ ≤ A ^ q⁻¹ := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hq |>.ne') ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le, one_div]
  exact ENNReal.rpow_le_rpow
    (lintegral_enorm_rpow_le_of_truncatedMoment hF htrunc) (inv_nonneg.mpr hq.le)

/-- Hölder control of an integrable Euclidean dot-product integral, stated
with the real values of the two finite `eLpNorm`s. -/
theorem abs_integral_vecDot_le_eLpNorm_toReal_mul
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    {p r : ℝ≥0∞} [ENNReal.HolderConjugate p r]
    {F G : α → Vec d}
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p μ)
    (hG : MemLp (fun x => HilbertVec.ofVec (G x)) r μ) :
    |∫ x, vecDot (F x) (G x) ∂μ| ≤
      (eLpNorm (fun x => HilbertVec.ofVec (F x)) p μ).toReal *
        (eLpNorm (fun x => HilbertVec.ofVec (G x)) r μ).toReal := by
  let f : α → ℝ := fun x => vecDot (F x) (G x)
  have hfm' : AEStronglyMeasurable
      (fun x => inner ℝ (HilbertVec.ofVec (F x)) (HilbertVec.ofVec (G x))) μ :=
    hF.aestronglyMeasurable.inner hG.aestronglyMeasurable
  have hfLp' : MemLp
      (fun x => inner ℝ (HilbertVec.ofVec (F x)) (HilbertVec.ofVec (G x))) 1 μ := by
    refine MemLp.of_bilin (r := 1)
      (b := fun x y : HilbertVec d => inner ℝ x y) (c := 1) hF hG hfm' ?_
    filter_upwards with x
    simpa using! norm_inner_le_norm (𝕜 := ℝ)
      (HilbertVec.ofVec (F x)) (HilbertVec.ofVec (G x))
  have hfLp : MemLp f 1 μ := by
    simpa only [f, HilbertVec.inner_def] using hfLp'
  have hnorm : ENNReal.ofReal |∫ x, f x ∂μ| ≤ eLpNorm f 1 μ := by
    simpa only [Real.enorm_eq_ofReal_abs] using
      (enorm_integral_le_lintegral_enorm (μ := μ) f).trans_eq
        eLpNorm_one_eq_lintegral_enorm.symm
  have hholder : eLpNorm f 1 μ ≤
      eLpNorm (fun x => HilbertVec.ofVec (F x)) p μ *
        eLpNorm (fun x => HilbertVec.ofVec (G x)) r μ := by
    simpa only [f] using eLpNorm_vecDot_le_mul hF hG
  have hright :
      eLpNorm (fun x => HilbertVec.ofVec (F x)) p μ *
        eLpNorm (fun x => HilbertVec.ofVec (G x)) r μ ≠ ∞ :=
    ENNReal.mul_ne_top hF.eLpNorm_ne_top hG.eLpNorm_ne_top
  have htoReal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hright).mpr
    (hnorm.trans hholder)
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul] using htoReal

/-- Cancellation of one finite positive radial norm factor. -/
private theorem rpow_sub_one_le_of_rpow_le_mul
    {a b : ℝ≥0∞} {r : ℝ} (ha0 : a ≠ 0) (hatop : a ≠ ∞)
    (h : a ^ r ≤ b * a) :
    a ^ (r - 1) ≤ b := by
  rw [ENNReal.rpow_sub r 1 ha0 hatop, ENNReal.rpow_one]
  exact (ENNReal.div_le_iff ha0 hatop).mpr h

/-- A real truncated-moment estimate transfers exactly to the ENNReal
truncation used in monotone convergence. -/
theorem lintegral_truncatedMoment_eq_ofReal_integral
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ} {F : α → HilbertVec d} {n : ℕ}
    {k : α → ℝ} (hk : Integrable k μ) (hk0 : 0 ≤ᵐ[μ] k)
    (hpoint : ∀ᵐ x ∂μ, ENNReal.ofReal (k x) = truncatedMoment q n F x) :
    ∫⁻ x, truncatedMoment q n F x ∂μ = ENNReal.ofReal (∫ x, k x ∂μ) := by
  calc
    ∫⁻ x, truncatedMoment q n F x ∂μ =
        ∫⁻ x, ENNReal.ofReal (k x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpoint] with x hx
      exact hx.symm
    _ = ENNReal.ofReal (∫ x, k x ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hk hk0).symm

/-- A uniform real bound for integrable radial moments gives the full
nonnegative ENNReal moment estimate. -/
theorem lintegral_enorm_rpow_le_of_real_truncated_bound
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ} {F : α → HilbertVec d} {A : ℝ}
    (hF : AEStronglyMeasurable F μ)
    (htrunc : ∀ n : ℕ, ∃ k : α → ℝ, Integrable k μ ∧ 0 ≤ᵐ[μ] k ∧
      (∀ᵐ x ∂μ, ENNReal.ofReal (k x) = truncatedMoment q n F x) ∧
      ∫ x, k x ∂μ ≤ A) :
    (∫⁻ x, ‖F x‖ₑ ^ q ∂μ) ≤ ENNReal.ofReal A := by
  apply lintegral_enorm_rpow_le_of_truncatedMoment hF
  intro n
  obtain ⟨k, hk, hk0, hpoint, hbound⟩ := htrunc n
  rw [lintegral_truncatedMoment_eq_ofReal_integral hk hk0 hpoint]
  exact ENNReal.ofReal_le_ofReal hbound

/-- Package the radial truncation of a measurable vector field on a cube as
simultaneous normalized `L²` and conjugate-`L^p` data. -/
noncomputable def cubeRadialTruncationL2LpField
    {d : ℕ} (Q : TriadicCube d) (q : FiniteLpExponent)
    (F : Vec d → Vec d)
    (hF : AEStronglyMeasurable (fun x ↦ HilbertVec.ofVec (F x))
      (volumeMeasureOn (openCubeSet Q))) (n : ℕ) :
    CubeEuclideanL2LpField Q q.conjugate := by
  let G : Vec d → Vec d := vectorRadialTruncation q.exponent.toReal n F
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hqone : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hraw : MemLp (hilbertRadialTruncation q.exponent.toReal n
      (fun x ↦ HilbertVec.ofVec (F x))) q.conjugate.exponent
      (volumeMeasureOn (openCubeSet Q)) :=
    memLp_hilbertRadialTruncation hqone n hF
  have hraw2 : MemLp (hilbertRadialTruncation q.exponent.toReal n
      (fun x ↦ HilbertVec.ofVec (F x))) 2
      (volumeMeasureOn (openCubeSet Q)) :=
    memLp_hilbertRadialTruncation hqone n hF
  refine { toCubeEuclideanLpField := ⟨G, ?_⟩, euclideanMemL2 := ?_ }
  · rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    simpa only [G, vectorRadialTruncation, HilbertVec.ofVec_toVec] using
      hraw.smul_measure ENNReal.ofReal_ne_top
  · rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    simpa only [G, vectorRadialTruncation, HilbertVec.ofVec_toVec] using
      hraw2.smul_measure ENNReal.ofReal_ne_top

/-- The field-generic radial truncation has the raw vector `L²` membership
required by the canonical adjoint solver. -/
theorem cubeRadialTruncation_memVectorL2
    {d : ℕ} (Q : TriadicCube d) (q : FiniteLpExponent)
    (F : Vec d → Vec d)
    (hF : AEStronglyMeasurable (fun x ↦ HilbertVec.ofVec (F x))
      (volumeMeasureOn (openCubeSet Q))) (n : ℕ) :
    MemVectorL2 (openCubeSet Q)
      (cubeRadialTruncationL2LpField Q q F hF n).toField := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hqone : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  simpa only [cubeRadialTruncationL2LpField, vectorRadialTruncation,
    HilbertVec.ofVec_toVec] using
    memVectorL2_vectorRadialTruncation (openCubeSet Q) hqone n F hF

/-- Package the radial truncation of the gradient of a centered-cube
`H¹₀` function as simultaneous normalized `L²` and conjugate-`L^p` data. -/
noncomputable def centeredCube_radialTruncationL2LpField
    {d : ℕ} [NeZero d] (m : ℤ) (q : FiniteLpExponent)
    (u : H10Function (openCubeSet (originCube d m))) (n : ℕ) :
    CubeEuclideanL2LpField (originCube d m) q.conjugate := by
  let U : Set (Vec d) := openCubeSet (originCube d m)
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let F : Vec d → Vec d := u.toH1Function.grad
  let G : Vec d → Vec d := vectorRadialTruncation q.exponent.toReal n F
  letI : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).isFiniteMeasure_restrict_volume
  have hFraw : AEStronglyMeasurable (fun x => HilbertVec.ofVec (F x))
      (volumeMeasureOn U) := by
    simpa only [F, hilbertifyVecField] using!
      (memHilbertVectorL2_hilbertifyVecField u.toH1Function.grad_memVectorL2).aestronglyMeasurable
  have hqone : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hraw : MemLp (hilbertRadialTruncation q.exponent.toReal n
      (fun x => HilbertVec.ofVec (F x))) q.conjugate.exponent
      (volumeMeasureOn U) :=
    memLp_hilbertRadialTruncation hqone n hFraw
  have hraw2 : MemLp (hilbertRadialTruncation q.exponent.toReal n
      (fun x => HilbertVec.ofVec (F x))) 2 (volumeMeasureOn U) :=
    memLp_hilbertRadialTruncation hqone n hFraw
  refine { toCubeEuclideanLpField := ⟨G, ?_⟩, euclideanMemL2 := ?_ }
  · rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    simpa only [G, vectorRadialTruncation, HilbertVec.ofVec_toVec] using
      hraw.smul_measure ENNReal.ofReal_ne_top
  · rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    simpa only [G, vectorRadialTruncation, HilbertVec.ofVec_toVec] using
      hraw2.smul_measure ENNReal.ofReal_ne_top

/-- The centered-cube radial truncation also has the raw vector `L²`
membership required by the canonical adjoint solver. -/
theorem centeredCube_radialTruncation_memVectorL2
    {d : ℕ} [NeZero d] (m : ℤ) (q : FiniteLpExponent)
    (u : H10Function (openCubeSet (originCube d m))) (n : ℕ) :
    MemVectorL2 (openCubeSet (originCube d m))
      (centeredCube_radialTruncationL2LpField m q u n).toField := by
  let U : Set (Vec d) := openCubeSet (originCube d m)
  let F : Vec d → Vec d := u.toH1Function.grad
  let : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).isFiniteMeasure_restrict_volume
  have hFraw : AEStronglyMeasurable (fun x => HilbertVec.ofVec (F x))
      (volumeMeasureOn U) := by
    simpa only [F, hilbertifyVecField] using!
      (memHilbertVectorL2_hilbertifyVecField u.toH1Function.grad_memVectorL2).aestronglyMeasurable
  have hqone : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  simpa only [centeredCube_radialTruncationL2LpField, F,
    vectorRadialTruncation, HilbertVec.ofVec_toVec] using
    memVectorL2_vectorRadialTruncation U hqone n F hFraw

/-- Two raw vector `L²` fields on a centered cube have an integrable dot
product for normalized cube volume. -/
theorem centeredCube_integrable_vecDot_of_memVectorL2
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
  exact (integrableOn_vecDot_of_memVectorL2 hF hG).smul_measure
    ENNReal.ofReal_ne_top

/-- The radial vector pairing is the corresponding ENNReal truncated moment. -/
theorem ofReal_vecDot_vectorRadialTruncation_eq_truncatedMoment
    {α : Type*} {d : ℕ} {q : ℝ} (hq : 1 < q) (n : ℕ)
    (F : α → Vec d) (x : α) :
    ENNReal.ofReal (vecDot (F x) (vectorRadialTruncation q n F x)) =
      truncatedMoment q n (fun y => HilbertVec.ofVec (F y)) x := by
  rw [vecDot_comm, vecDot_vectorRadialTruncation_self hq n F]
  by_cases hx : euclideanNorm (F x) ≤ (n : ℝ)
  · have hx' : ‖HilbertVec.ofVec (F x)‖ ≤ (n : ℝ) := by
      simpa only [euclideanNorm_eq_norm_ofVec] using hx
    have hxmem : x ∈ {y | ‖HilbertVec.ofVec (F y)‖ ≤ (n : ℝ)} := hx'
    rw [if_pos hx, truncatedMoment, Set.indicator_of_mem hxmem]
    have hq0 : 0 ≤ q := by linarith
    rw [← ofReal_norm (HilbertVec.ofVec (F x))]
    simpa only [euclideanNorm_eq_norm_ofVec] using
      (ENNReal.ofReal_rpow_of_nonneg
        (norm_nonneg (HilbertVec.ofVec (F x))) hq0).symm
  · have hx' : ¬ ‖HilbertVec.ofVec (F x)‖ ≤ (n : ℝ) := by
      simpa only [euclideanNorm_eq_norm_ofVec] using hx
    have hxmem : x ∉ {y | ‖HilbertVec.ofVec (F y)‖ ≤ (n : ℝ)} := hx'
    rw [if_neg hx, truncatedMoment, Set.indicator_of_notMem hxmem]
    exact ENNReal.ofReal_zero

/-- The conjugate norm of a radial truncation has exactly the original
truncated moment as its power. -/
theorem eLpNorm_hilbertRadialTruncation_rpow_conjugate_eq_truncatedMoment
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    (q : FiniteLpExponent) (n : ℕ) (F : α → HilbertVec d) :
    (eLpNorm (hilbertRadialTruncation q.exponent.toReal n F)
      q.conjugate.exponent μ) ^ q.conjugate.exponent.toReal =
      ∫⁻ x, truncatedMoment q.exponent.toReal n F x ∂μ := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ne_of_gt (zero_lt_one.trans q.conjugate.one_lt)) q.conjugate.lt_top.ne,
    ← ENNReal.rpow_mul]
  have hqnonzero : q.conjugate.exponent.toReal ≠ 0 := by
    exact ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans q.conjugate.one_lt)) q.conjugate.lt_top.ne |>.ne'
  rw [one_div, inv_mul_cancel₀ hqnonzero, ENNReal.rpow_one]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg,
    norm_hilbertRadialTruncation_rpow_conjugate]
  by_cases hx : ‖F x‖ ≤ (n : ℝ)
  · have hxmem : x ∈ {y | ‖F y‖ ≤ (n : ℝ)} := hx
    rw [if_pos hx, truncatedMoment, Set.indicator_of_mem hxmem]
    rw [← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg]
  · have hxmem : x ∉ {y | ‖F y‖ ≤ (n : ℝ)} := hx
    rw [if_neg hx, truncatedMoment, Set.indicator_of_notMem hxmem]
    exact ENNReal.ofReal_zero

private theorem centeredCube_normalizedVolume_eq_smul_openCubeVolume
    {d : ℕ} (m : ℤ) :
    (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
  change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- The canonical raw-adjoint solver also satisfies the centered-cube
volume-normalized weak equation.  This is a one-way transport: it merely
scales both sides and therefore requires neither a cancellation argument nor
an additional nonzero hypothesis. -/
theorem openCubeSetScalarDivergenceSolution_normalized_weak
    {d : ℕ} [NeZero d] (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (G : Vec d → Vec d) (hG : MemVectorL2 (openCubeSet (originCube d m)) G)
    (psi : H10Function (openCubeSet (originCube d m))) :
    sigma0 * ∫ x,
        vecDot
          ((openCubeSetScalarDivergenceSolution (originCube d m) hsigma0 G hG).toH1Function.grad x)
          (psi.toH1Function.grad x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      -∫ x, vecDot (G x) (psi.toH1Function.grad x)
        ∂(centeredCubeDomain d m).normalizedVolume := by
  rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume,
    integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul]
  calc
    sigma0 *
        ((ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          ∫ x in openCubeSet (originCube d m),
            vecDot
              ((openCubeSetScalarDivergenceSolution (originCube d m) hsigma0 G hG).toH1Function.grad x)
              (psi.toH1Function.grad x) ∂volume) =
        (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          (sigma0 * ∫ x in openCubeSet (originCube d m),
            vecDot
              ((openCubeSetScalarDivergenceSolution (originCube d m) hsigma0 G hG).toH1Function.grad x)
              (psi.toH1Function.grad x) ∂volume) := by
          ring
    _ = (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          (-(∫ x in openCubeSet (originCube d m),
            vecDot (G x) (psi.toH1Function.grad x) ∂volume)) := by
          rw [openCubeSetScalarDivergenceSolution_weak]
    _ = -((ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          ∫ x in openCubeSet (originCube d m),
            vecDot (G x) (psi.toH1Function.grad x) ∂volume) := by
          ring

/-- Specialization of `scalarDivergence_cross_pairing` to the canonical cube
adjoint.  The supplied solution is deliberately represented only by its raw
weak equation, which lets the finite-`q` endpoint derive that fact internally
from its own normalized predicate. -/
theorem openCubeSetScalarDivergenceSolution_cross_pairing
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (u : H10Function (openCubeSet Q)) (h G : Vec d → Vec d)
    (hu : ∀ psi : H10Function (openCubeSet Q),
      sigma0 * ∫ x in openCubeSet Q,
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet Q, vecDot (h x) (psi.toH1Function.grad x) ∂volume)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    ∫ x in openCubeSet Q, vecDot (u.toH1Function.grad x) (G x) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot (h x)
          ((openCubeSetScalarDivergenceSolution Q hsigma0 G hG).toH1Function.grad x) ∂volume := by
  exact scalarDivergence_cross_pairing u
    (openCubeSetScalarDivergenceSolution Q hsigma0 G hG) h G hu
    (openCubeSetScalarDivergenceSolution_weak Q hsigma0 G hG)

/-- The canonical adjoint cross-pairing directly on the normalized centered
cube.  This combines the supplied normalized weak equation with the canonical
normalized adjoint equation and is the exact bridge for the `q < 2` proof. -/
theorem openCubeSetScalarDivergenceSolution_normalized_cross_pairing
    {d : ℕ} [NeZero d] (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (u : H10Function (openCubeSet (originCube d m))) (h G : Vec d → Vec d)
    (hu : ∀ psi : H10Function (openCubeSet (originCube d m)),
      sigma0 * ∫ x, vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume =
        -∫ x, vecDot (h x) (psi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume)
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    ∫ x, vecDot (u.toH1Function.grad x) (G x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      ∫ x, vecDot (h x)
        ((openCubeSetScalarDivergenceSolution (originCube d m) hsigma0 G hG).toH1Function.grad x)
        ∂(centeredCubeDomain d m).normalizedVolume := by
  exact centeredCube_scalarDivergence_cross_pairing m u
    (openCubeSetScalarDivergenceSolution (originCube d m) hsigma0 G hG) h G hu
    (openCubeSetScalarDivergenceSolution_normalized_weak m hsigma0 G hG)

/-- The radial-truncation bootstrap: an estimate with one conjugate-norm
factor on the right already gives the desired `L^q` bound. -/
theorem eLpNorm_le_of_truncated_cross_bound
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ} {F : α → HilbertVec d} {A : ℝ≥0∞}
    (hq : 1 < q) (hF : AEStronglyMeasurable F μ)
    (htrunc : ∀ n : ℕ,
      (∫⁻ x, truncatedMoment q n F x ∂μ) ≠ ∞ ∧
      (∫⁻ x, truncatedMoment q n F x ∂μ) ≤
        A * (∫⁻ x, truncatedMoment q n F x ∂μ) ^ (1 - q⁻¹)) :
    eLpNorm F (ENNReal.ofReal q) μ ≤ A := by
  have root_le_of_le_mul_rpow : ∀ {J A : ℝ≥0∞}, J ≠ ∞ →
      J ≤ A * J ^ (1 - q⁻¹) → J ≤ A ^ q := by
    intro J B hJtop hJ
    by_cases hJzero : J = 0
    · rw [hJzero]
      exact bot_le
    have hJpos : 0 < J := lt_of_le_of_ne bot_le (Ne.symm hJzero)
    have hepos : 0 < 1 - q⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hq)
    have he : 0 ≤ 1 - q⁻¹ := hepos.le
    have hBpos : 0 < J ^ (1 - q⁻¹) := ENNReal.rpow_pos hJpos hJtop
    have hBtop : J ^ (1 - q⁻¹) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg he hJtop
    have hfac : J = J ^ (1 - q⁻¹) * J ^ q⁻¹ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ he
        (inv_nonneg.mpr (by linarith : 0 ≤ q))]
      have hsum : (1 - q⁻¹) + q⁻¹ = 1 := by ring
      rw [hsum, ENNReal.rpow_one]
    have hroot : J ^ q⁻¹ ≤ B := by
      apply (ENNReal.mul_le_mul_iff_left hBpos.ne' hBtop).mp
      calc
        J ^ q⁻¹ * J ^ (1 - q⁻¹) = J ^ (1 - q⁻¹) * J ^ q⁻¹ := mul_comm _ _
        _ = J := hfac.symm
        _ ≤ B * J ^ (1 - q⁻¹) := hJ
    have hq0 : q ≠ 0 := by linarith
    calc
      J = (J ^ q⁻¹) ^ q := by
        rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hq0, ENNReal.rpow_one]
      _ ≤ B ^ q := ENNReal.rpow_le_rpow hroot (by linarith)
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < q) |>.ne') ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ q)]
  have hmoment : (∫⁻ x, ‖F x‖ₑ ^ q ∂μ) ≤ A ^ q := by
    rw [lintegral_enorm_rpow_eq_iSup_lintegral_truncatedMoment hF]
    apply iSup_le
    intro n
    exact root_le_of_le_mul_rpow (htrunc n).1 (htrunc n).2
  calc
    (∫⁻ x, ‖F x‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (A ^ q) ^ (1 / q) :=
      ENNReal.rpow_le_rpow hmoment (by positivity)
    _ = A := by
      rw [show (1 / q : ℝ) = q⁻¹ by ring, ← ENNReal.rpow_mul]
      have hq0 : q ≠ 0 := by linarith
      rw [mul_inv_cancel₀ hq0, ENNReal.rpow_one]

/-- A truncated moment is finite whenever the full positive moment is finite. -/
theorem truncatedMoment_ne_top_of_memLp
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ} {F : α → HilbertVec d}
    (hq : 0 < q) (hF : MemLp F (ENNReal.ofReal q) μ) (n : ℕ) :
    (∫⁻ x, truncatedMoment q n F x ∂μ) ≠ ∞ := by
  apply ne_top_of_le_ne_top
    ((MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ENNReal.ofReal_pos.mpr hq |>.ne') ENNReal.ofReal_ne_top
      hF.eLpNorm_lt_top).ne)
  rw [ENNReal.toReal_ofReal hq.le]
  apply MeasureTheory.lintegral_mono
  intro x
  by_cases hx : ‖F x‖ ≤ (n : ℝ)
  · simp [truncatedMoment, hx]
  · simp [truncatedMoment, hx]

private theorem centeredCube_memLp_hilbertGradient_two
    {d : ℕ} {m : ℤ} (u : H10Function (openCubeSet (originCube d m))) :
    MemLp (hilbertifyVecField u.toH1Function.grad) 2
      (centeredCubeDomain d m).normalizedVolume := by
  rw [show (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
    simpa only using centeredCube_normalizedVolume_eq_smul_openCubeVolume m]
  exact (memHilbertVectorL2_hilbertifyVecField
    u.toH1Function.grad_memVectorL2).smul_measure ENNReal.ofReal_ne_top

end INTERNAL

/-- Internal duality branch of the supplied-solution cube CZ estimate. -/
private theorem centeredCubeH10ScalarDivergence_cz_of_one_lt_of_lt_two
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (hq : q.exponent.toReal < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h : CubeEuclideanL2LpField (originCube d m) q)
      (u : H10Function (openCubeSet (originCube d m))), 0 < sigma0 →
      IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo →
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        u.toH1Function.grad ≤ C * (ENNReal.ofReal sigma0)⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
            h.toField := by
  obtain ⟨C, hCtop, hC⟩ := centeredCubeH10ScalarDivergence_cz_of_two_lt d
    q.conjugate (INTERNAL.conjugate_toReal_gt_two_of_lt_two q hq)
  refine ⟨C, hCtop, ?_⟩
  intro m sigma0 h u hsigma0 hsolution
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let F : Vec d → HilbertVec d := hilbertifyVecField u.toH1Function.grad
  let H : Vec d → HilbertVec d := hilbertifyVecField h.toField
  let : ENNReal.HolderConjugate q.exponent q.conjugate.exponent := q.holderConjugate
  have hqreal : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hFtwo : MemLp F 2 μ := by
    simpa only [F, μ] using INTERNAL.centeredCube_memLp_hilbertGradient_two u
  have hHq : MemLp H q.exponent μ := by
    simpa only [H, μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemLp
  have hFmeas : AEStronglyMeasurable F μ := hFtwo.aestronglyMeasurable
  let A : ℝ≥0∞ := C * (ENNReal.ofReal sigma0)⁻¹ * eLpNorm H q.exponent μ
  have hmain : eLpNorm F q.exponent μ ≤ A := by
    rw [← ENNReal.ofReal_toReal q.lt_top.ne]
    apply INTERNAL.eLpNorm_le_of_truncated_cross_bound hqreal hFmeas
    intro n
    let Gfield := INTERNAL.centeredCube_radialTruncationL2LpField m q u n
    let G : Vec d → Vec d := Gfield.toField
    let v := openCubeSetScalarDivergenceSolution (originCube d m) hsigma0 G
      (INTERNAL.centeredCube_radialTruncation_memVectorL2 m q u n)
    have hGtwo : MemVectorL2 (openCubeSet (originCube d m)) G := by
      simpa only [G, Gfield] using
        INTERNAL.centeredCube_radialTruncation_memVectorL2 m q u n
    have hk : Integrable (fun x => vecDot (u.toH1Function.grad x) (G x)) μ := by
      simpa only [μ] using INTERNAL.centeredCube_integrable_vecDot_of_memVectorL2 m
        u.toH1Function.grad_memVectorL2 hGtwo
    have hk0 : 0 ≤ᵐ[μ] fun x => vecDot (u.toH1Function.grad x) (G x) := by
      filter_upwards with x
      change 0 ≤ vecDot (u.toH1Function.grad x)
        (INTERNAL.vectorRadialTruncation q.exponent.toReal n u.toH1Function.grad x)
      rw [vecDot_comm, INTERNAL.vecDot_vectorRadialTruncation_self hqreal]
      split_ifs with hx
      · exact Real.rpow_nonneg (euclideanNorm_nonneg _) _
      · exact le_rfl
    have hpoint : ∀ᵐ x ∂μ, ENNReal.ofReal
        (vecDot (u.toH1Function.grad x) (G x)) =
          INTERNAL.truncatedMoment q.exponent.toReal n F x := by
      filter_upwards with x
      simpa only [F, G, Gfield] using!
        INTERNAL.ofReal_vecDot_vectorRadialTruncation_eq_truncatedMoment
          hqreal n u.toH1Function.grad x
    have hJ : (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ) =
        ENNReal.ofReal (∫ x, vecDot (u.toH1Function.grad x) (G x) ∂μ) :=
      INTERNAL.lintegral_truncatedMoment_eq_ofReal_integral hk hk0 hpoint
    refine ⟨?_, ?_⟩
    · rw [hJ]
      exact ENNReal.ofReal_ne_top
    have hvsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 v
        Gfield.toLpTwo := by
      intro psi
      simpa only [v, G, Gfield] using!
        INTERNAL.openCubeSetScalarDivergenceSolution_normalized_weak m hsigma0 G hGtwo psi
    have hvbound := hC m sigma0 Gfield v hsigma0 hvsolution
    have hGq : MemLp (hilbertifyVecField G) q.conjugate.exponent μ := by
      simpa only [μ, G, Gfield, centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
        hilbertifyVecField] using! Gfield.euclideanMemLp
    have hVtwo : MemLp (hilbertifyVecField v.toH1Function.grad) 2 μ := by
      simpa only [v, μ] using INTERNAL.centeredCube_memLp_hilbertGradient_two v
    have hVbound : eLpNorm (hilbertifyVecField v.toH1Function.grad)
        q.conjugate.exponent μ ≤ C * (ENNReal.ofReal sigma0)⁻¹ *
          eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ := by
      simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
        BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
        MeasureTheory.eLpNorm_norm, μ, v, G, Gfield, hilbertifyVecField] using! hvbound
    have hVq : MemLp (hilbertifyVecField v.toH1Function.grad)
        q.conjugate.exponent μ := by
      refine ⟨hVtwo.aestronglyMeasurable, ?_⟩
      apply lt_of_le_of_lt hVbound
      apply ENNReal.mul_lt_top
      · exact (ENNReal.mul_ne_top hCtop.ne
          (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hsigma0)))).lt_top
      · exact hGq.eLpNorm_lt_top
    have huweak : ∀ psi : H10Function (openCubeSet (originCube d m)),
        sigma0 * ∫ x, vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂μ =
          -∫ x, vecDot (h.toField x) (psi.toH1Function.grad x) ∂μ := by
      intro psi
      simpa only [μ] using! hsolution psi
    have hcross := INTERNAL.openCubeSetScalarDivergenceSolution_normalized_cross_pairing
      m hsigma0 u h.toField G huweak hGtwo
    have hholder := INTERNAL.abs_integral_vecDot_le_eLpNorm_toReal_mul
      (F := h.toField) (G := v.toH1Function.grad) hHq hVq
    have hGmoment : (eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ) ^
        q.conjugate.exponent.toReal =
          ∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ := by
      simpa only [μ, F, G, Gfield, hilbertifyVecField] using!
        INTERNAL.eLpNorm_hilbertRadialTruncation_rpow_conjugate_eq_truncatedMoment q n F
    have hreal : q.exponent.toReal.HolderConjugate q.conjugate.exponent.toReal :=
      ENNReal.HolderConjugate.toReal hqreal
    have hexp : (q.conjugate.exponent.toReal)⁻¹ = 1 - q.exponent.toReal⁻¹ := by
      have hsum := hreal.one_div_add_one_div
      rw [one_div] at hsum
      norm_num at hsum
      linarith
    have hGnorm : eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ =
        (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ) ^
          (1 - q.exponent.toReal⁻¹) := by
      have hr0 : q.conjugate.exponent.toReal ≠ 0 := by
        exact ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans q.conjugate.one_lt))
          q.conjugate.lt_top.ne |>.ne'
      calc
        eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ =
            (eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ ^
              q.conjugate.exponent.toReal) ^ (q.conjugate.exponent.toReal)⁻¹ := by
              rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hr0, ENNReal.rpow_one]
        _ = (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ) ^
            (q.conjugate.exponent.toReal)⁻¹ := by rw [hGmoment]
        _ = _ := by rw [hexp]
    calc
      ∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ =
          ENNReal.ofReal (∫ x, vecDot (u.toH1Function.grad x) (G x) ∂μ) := hJ
      _ =
          ENNReal.ofReal (∫ x, vecDot (h.toField x) (v.toH1Function.grad x) ∂μ) := by
            rw [hcross]
      _ ≤ ENNReal.ofReal |∫ x, vecDot (h.toField x) (v.toH1Function.grad x) ∂μ| :=
        ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ENNReal.ofReal ((eLpNorm H q.exponent μ).toReal *
          (eLpNorm (hilbertifyVecField v.toH1Function.grad)
            q.conjugate.exponent μ).toReal) := ENNReal.ofReal_le_ofReal hholder
      _ = eLpNorm H q.exponent μ *
          eLpNorm (hilbertifyVecField v.toH1Function.grad)
            q.conjugate.exponent μ := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal hHq.eLpNorm_lt_top.ne,
            ENNReal.ofReal_toReal hVq.eLpNorm_lt_top.ne]
      _ ≤ eLpNorm H q.exponent μ *
          (C * (ENNReal.ofReal sigma0)⁻¹ *
            eLpNorm (hilbertifyVecField G) q.conjugate.exponent μ) := by
          gcongr
      _ = A * (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n F x ∂μ) ^
          (1 - q.exponent.toReal⁻¹) := by
          rw [hGnorm]
          dsimp only [A]
          ac_rfl
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
    MeasureTheory.eLpNorm_norm, F, H, μ, A] using! hmain

/-- The supplied-solution cube Calderón--Zygmund estimate for every finite
exponent.  The `q<2` branch is obtained by adjoint duality, the `q=2` branch
is the energy estimate, and the `q>2` branch is the good-`λ` theorem. -/
theorem centeredCubeH10ScalarDivergence_cz
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h : CubeEuclideanL2LpField (originCube d m) q)
      (u : H10Function (openCubeSet (originCube d m))), 0 < sigma0 →
      IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo →
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        u.toH1Function.grad ≤ C * (ENNReal.ofReal sigma0)⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
            h.toField := by
  by_cases hlt : q.exponent.toReal < 2
  · exact centeredCubeH10ScalarDivergence_cz_of_one_lt_of_lt_two d q hlt
  by_cases hgt : 2 < q.exponent.toReal
  · exact centeredCubeH10ScalarDivergence_cz_of_two_lt d q hgt
  have hreal : q.exponent.toReal = 2 := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
  have hexp : q.exponent = 2 := by
    apply (ENNReal.toReal_eq_toReal_iff' q.lt_top.ne (by norm_num)).mp
    simpa only [ENNReal.toReal_ofNat] using hreal
  have hq : q = FiniteLpExponent.two := by
    cases q
    simp only [FiniteLpExponent.two] at hexp ⊢
    cases hexp
    rfl
  subst q
  refine ⟨1, by norm_num, ?_⟩
  intro m sigma0 h u hsigma0 hsolution
  simpa only [one_mul] using
    centeredCubeH10ScalarDivergence_cz_two m sigma0 h u hsigma0 hsolution

end CubeCalderonZygmund

end
end Homogenization
