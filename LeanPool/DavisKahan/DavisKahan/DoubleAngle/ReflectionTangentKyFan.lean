/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.KyFanOrthonormal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.SpectralSelection
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SharpKyFan
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.Isometry
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramBandPolar

/-! # Reflection Tangent Ky Fan -/

open TauCeti.DavisKahan.Angle


/-!
# Branch-free Ky Fan reflection tangent estimate

This is the dimension-free analytic core of the Davis--Kahan Section 7
reflection proof.  The approximate singular family belongs to the **actual**
tangent corner `T`; no graph coordinate and no quarter-angle branch occurs.

The signed diagonal reflection blocks `C0` and `C1` satisfy the two Gram
identities

`C0⋆ C0 (1 + T⋆ T) = 1`, `C1⋆ C1 (1 + T T⋆) = 1`.

Their polar isometries absorb the sign of `cos 2Theta`.  Equation (7.6) then
leaves exactly two residual pairings.  Each is bounded by the same Ky Fan
gauge, so the printed constant `2` appears exactly once.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace BigOperators
open ApproximationNumber
open ExactSinTheta

noncomputable section

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

private theorem isUnit_modulus_of_isUnit_selfAdjoint
    (C : E0 →L[ℂ] E0) (hCsa : IsSelfAdjoint C) (hCunit : IsUnit C) :
    IsUnit C.modulus := by
  rw [C.isUnit_modulus_iff, hCsa.adjoint_eq, ← ContinuousLinearMap.mul_def]
  exact hCunit.mul hCunit

private theorem polar_apply_modulus_eq_self
    (C : E0 →L[ℂ] E0) (hCsa : IsSelfAdjoint C) (hCunit : IsUnit C) (x : E0) :
    C.polarIsometryOfIsUnitModulus (C.modulus x) = C x := by
  exact C.polarIsometryOfIsUnitModulus_modulus_apply
    (isUnit_modulus_of_isUnit_selfAdjoint C hCsa hCunit) x

private theorem selfAdjoint_polar_then_apply_eq_modulus
    (C : E0 →L[ℂ] E0) (hCsa : IsSelfAdjoint C) (hCunit : IsUnit C) (x : E0) :
    C (C.polarIsometryOfIsUnitModulus x) = C.modulus x := by
  let hM : IsUnit C.modulus := isUnit_modulus_of_isUnit_selfAdjoint C hCsa hCunit
  have hsq : C * C = C.modulus * C.modulus := by
    symm
    rw [C.modulus_mul_self, hCsa.adjoint_eq, ← ContinuousLinearMap.mul_def]
  have hunitM : C.modulus * Ring.inverse C.modulus = 1 :=
    Ring.mul_inverse_cancel _ hM
  rw [ContinuousLinearMap.polarIsometryOfIsUnitModulus_apply]
  change (C * C) (Ring.inverse C.modulus x) = C.modulus x
  rw [hsq]
  change C.modulus (C.modulus (Ring.inverse C.modulus x)) = C.modulus x
  have hcancel : C.modulus (Ring.inverse C.modulus x) = x := by
    have h := congrArg (fun M : E0 →L[ℂ] E0 => M x) hunitM
    change C.modulus (Ring.inverse C.modulus x) = x at h
    exact h
  exact congrArg C.modulus hcancel

private theorem norm_polar_apply
    (C : E0 →L[ℂ] E0) (hCsa : IsSelfAdjoint C) (hCunit : IsUnit C) (x : E0) :
    ‖C.polarIsometryOfIsUnitModulus x‖ = ‖x‖ :=
  C.norm_polarIsometryOfIsUnitModulus_apply
    (isUnit_modulus_of_isUnit_selfAdjoint C hCsa hCunit) x

private theorem orthonormal_polar_comp
    {m : ℕ} (C : E0 →L[ℂ] E0) (hCsa : IsSelfAdjoint C) (hCunit : IsUnit C)
    {f : Fin m → E0} (hf : Orthonormal ℂ f) :
    Orthonormal ℂ (fun i => C.polarIsometryOfIsUnitModulus (f i)) := by
  rw [orthonormal_iff_ite] at hf ⊢
  intro i j
  let hM : IsUnit C.modulus := isUnit_modulus_of_isUnit_selfAdjoint C hCsa hCunit
  let J := C.polarLinearIsometry hM
  change ⟪J (f i), J (f j)⟫_ℂ = _
  rw [J.inner_map_map]
  exact hf i j

omit [CompleteSpace E0] [CompleteSpace E1] in
private theorem approximationNumber_le_norm_local (T : E0 →L[ℂ] E1) (n : ℕ) :
    T.approximationNumber n ≤ ‖T‖ :=
  T.approximationNumber_le_norm n

/-- A uniform error coefficient for the actual-tangent approximate-pair
calculation.  It is deliberately generous: only finiteness and nonnegativity
matter because it is multiplied by `epsilon` and removed at the end. -/
def reflectionTangentErrorCoefficient
    (A0 : E0 →L[ℂ] E0) (A1 : E1 →L[ℂ] E1) (B T : E0 →L[ℂ] E1)
    (C0 : E0 →L[ℂ] E0) (C1 : E1 →L[ℂ] E1) : ℝ :=
  let q := Real.sqrt (1 + ‖T‖ ^ 2)
  let M0 := 2 * ‖C0‖ ^ 2 * ‖T‖ * q
  let M1 := 2 * ‖C1‖ ^ 2 * ‖T‖ * q
  q * (‖A0‖ * (‖T‖ * M1 + 1) +
    ‖A1‖ * (‖C1‖ + ‖T‖ * M1) + ‖B‖ * (M0 + M1))

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The reflection error coefficient is nonnegative. -/
theorem reflectionTangentErrorCoefficient_nonneg
    (A0 : E0 →L[ℂ] E0) (A1 : E1 →L[ℂ] E1) (B T : E0 →L[ℂ] E1)
    (C0 : E0 →L[ℂ] E0) (C1 : E1 →L[ℂ] E1) :
    0 ≤ reflectionTangentErrorCoefficient A0 A1 B T C0 C1 := by
  unfold reflectionTangentErrorCoefficient
  positivity

private theorem gram_residual_of_tangent_pair_right
    (C : E0 →L[ℂ] E0) (T : E0 →L[ℂ] E1)
    (hgram : C.adjoint ∘L C ∘L (1 + T.adjoint ∘L T) = 1)
    {u : E0} {v : E1} {t eps : ℝ}
    (ht0 : 0 ≤ t) (htnorm : t ≤ ‖T‖)
    (hTu : ‖T u - (t : ℂ) • v‖ ≤ eps)
    (hTv : ‖T.adjoint v - (t : ℂ) • u‖ ≤ eps) :
    let q := Real.sqrt (1 + ‖T‖ ^ 2)
    let c := (Real.sqrt (1 + t ^ 2))⁻¹
    ‖C.modulus u - (c : ℂ) • u‖ ≤
      (2 * ‖C‖ ^ 2 * ‖T‖ * q) * eps := by
  dsimp only
  set r : ℝ := Real.sqrt (1 + t ^ 2) with hr
  set q : ℝ := Real.sqrt (1 + ‖T‖ ^ 2) with hq
  set c : ℝ := r⁻¹ with hc
  have heps0 : 0 ≤ eps := (norm_nonneg _).trans hTu
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hrleq : r ≤ q := by
    rw [hr, hq]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hqc : 1 ≤ q * c := by
    dsimp [c]
    rw [le_mul_inv_iff₀ hr0]
    simpa [one_mul] using hrleq
  have hc_sq : c ^ 2 * (1 + t ^ 2) = 1 := by
    have hrsq : r ^ 2 = 1 + t ^ 2 := by
      rw [hr, sq, Real.mul_self_sqrt]
      nlinarith [sq_nonneg t]
    dsimp [c]
    field_simp [hr0.ne']
    nlinarith
  have hTT :
      ‖T.adjoint (T u) - ((t ^ 2 : ℝ) : ℂ) • u‖ ≤ 2 * ‖T‖ * eps := by
    have hsplit :
        T.adjoint (T u) - ((t ^ 2 : ℝ) : ℂ) • u =
          T.adjoint (T u - (t : ℂ) • v) +
            (t : ℂ) • (T.adjoint v - (t : ℂ) • u) := by
      rw [map_sub, ContinuousLinearMap.map_smul, smul_sub, smul_smul]
      norm_num [pow_two]
    rw [hsplit]
    calc
      _ ≤ ‖T.adjoint (T u - (t : ℂ) • v)‖ +
          ‖(t : ℂ) • (T.adjoint v - (t : ℂ) • u)‖ := norm_add_le _ _
      _ ≤ ‖T‖ * eps + t * eps := by
        have hleft := T.adjoint.le_opNorm (T u - (t : ℂ) • v)
        rw [ContinuousLinearMap.adjoint.norm_map] at hleft
        have hleft' := hleft.trans
          (mul_le_mul_of_nonneg_left hTu (norm_nonneg T))
        have hright : ‖(t : ℂ) • (T.adjoint v - (t : ℂ) • u)‖ ≤ t * eps := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
          exact mul_le_mul_of_nonneg_left hTv ht0
        exact add_le_add hleft' hright
      _ ≤ 2 * ‖T‖ * eps := by
        have hteps : t * eps ≤ ‖T‖ * eps :=
          mul_le_mul_of_nonneg_right htnorm heps0
        linarith only [hteps]
  have hGramPoint :
      ‖C.adjoint (C u) - ((c ^ 2 : ℝ) : ℂ) • u‖ ≤
        2 * ‖C‖ ^ 2 * ‖T‖ * eps := by
    have happ := congrArg (fun M : E0 →L[ℂ] E0 => M u) hgram
    simp only [ContinuousLinearMap.comp_apply, add_apply, one_apply_eq_self] at happ
    let e : E0 := T.adjoint (T u) - ((t ^ 2 : ℝ) : ℂ) • u
    have hTTeq : T.adjoint (T u) = ((t ^ 2 : ℝ) : ℂ) • u + e := by
      dsimp [e]
      abel
    have happExpanded :
        C.adjoint (C u) + C.adjoint (C (T.adjoint (T u))) = u := by
      simpa only [map_add] using happ
    have happScalar :
        (((1 + t ^ 2 : ℝ) : ℂ) • C.adjoint (C u)) +
          C.adjoint (C e) = u := by
      rw [hTTeq, map_add, ContinuousLinearMap.map_smul, map_add, ContinuousLinearMap.map_smul] at happExpanded
      calc
        (((1 + t ^ 2 : ℝ) : ℂ) • C.adjoint (C u)) + C.adjoint (C e) =
            C.adjoint (C u) +
              (((t ^ 2 : ℝ) : ℂ) • C.adjoint (C u) + C.adjoint (C e)) := by
              module
        _ = u := happExpanded
    have hscaled := congrArg (fun z : E0 => ((c ^ 2 : ℝ) : ℂ) • z) happScalar
    have hcprod :
        (((c ^ 2 : ℝ) : ℂ) * ((1 + t ^ 2 : ℝ) : ℂ)) = 1 := by
      exact_mod_cast hc_sq
    have hscaled' :
        C.adjoint (C u) + ((c ^ 2 : ℝ) : ℂ) • C.adjoint (C e) =
          ((c ^ 2 : ℝ) : ℂ) • u := by
      rw [smul_add, smul_smul] at hscaled
      rw [hcprod, one_smul] at hscaled
      exact hscaled
    have hrewrite :
        C.adjoint (C u) - ((c ^ 2 : ℝ) : ℂ) • u =
          -((c ^ 2 : ℝ) : ℂ) • C.adjoint (C e) := by
      rw [← hscaled']
      module
    have hnormScalar : ‖-((c ^ 2 : ℝ) : ℂ)‖ = c ^ 2 := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg c)]
    rw [hrewrite, norm_smul, hnormScalar]
    have hCC := C.adjoint.le_opNorm (C e)
    have hC := C.le_opNorm e
    rw [ContinuousLinearMap.adjoint.norm_map] at hCC
    have heNorm : ‖e‖ ≤ 2 * ‖T‖ * eps := by
      change ‖T.adjoint (T u) - ((t ^ 2 : ℝ) : ℂ) • u‖ ≤ 2 * ‖T‖ * eps
      exact hTT
    have hbound : ‖C.adjoint (C e)‖ ≤ ‖C‖ ^ 2 * (2 * ‖T‖ * eps) := by
      calc
        _ ≤ ‖C‖ * ‖C e‖ := hCC
        _ ≤ ‖C‖ * (‖C‖ * ‖e‖) :=
          mul_le_mul_of_nonneg_left hC (norm_nonneg C)
        _ ≤ ‖C‖ * (‖C‖ * (2 * ‖T‖ * eps)) := by
          gcongr
        _ = ‖C‖ ^ 2 * (2 * ‖T‖ * eps) := by ring
    have hc2le : c ^ 2 ≤ 1 := by
      have hr1 : 1 ≤ r := by
        rw [hr]
        calc
          1 = Real.sqrt 1 := by norm_num
          _ ≤ Real.sqrt (1 + t ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
      dsimp [c]
      have hinv : r⁻¹ ≤ 1 := by
        exact (inv_le_one₀ hr0).2 hr1
      nlinarith [sq_nonneg r⁻¹]
    calc
      c ^ 2 * ‖C.adjoint (C e)‖
          ≤ c ^ 2 * (‖C‖ ^ 2 * (2 * ‖T‖ * eps)) :=
            mul_le_mul_of_nonneg_left hbound (sq_nonneg c)
      _ ≤ 1 * (‖C‖ ^ 2 * (2 * ‖T‖ * eps)) := by
        exact mul_le_mul_of_nonneg_right hc2le (by positivity)
      _ = 2 * ‖C‖ ^ 2 * ‖T‖ * eps := by ring
  have hgramForMod :
      ‖gramOperator C u - ((c ^ 2 : ℝ) : ℂ) • u‖ ≤
        (2 * ‖C‖ ^ 2 * ‖T‖ * q * eps) * c := by
    change ‖C.adjoint (C u) - ((c ^ 2 : ℝ) : ℂ) • u‖ ≤ _
    refine hGramPoint.trans ?_
    have hbase0 : 0 ≤ 2 * ‖C‖ ^ 2 * ‖T‖ * eps := by positivity
    calc
      2 * ‖C‖ ^ 2 * ‖T‖ * eps
          ≤ (2 * ‖C‖ ^ 2 * ‖T‖ * eps) * (q * c) := by
            nlinarith
      _ = (2 * ‖C‖ ^ 2 * ‖T‖ * q * eps) * c := by ring
  have hmod := modulus_residual_le_of_gram_residual
    (X := C) (x := u) (lam := c)
    (δ := 2 * ‖C‖ ^ 2 * ‖T‖ * q * eps)
    hc0 (by positivity) hgramForMod
  exact hmod

omit [CompleteSpace E0] in
private theorem abs_re_inner_error_left
    {x y z : E0} :
    |RCLike.re ⟪x, z⟫_ℂ - RCLike.re ⟪y, z⟫_ℂ| ≤ ‖x - y‖ * ‖z‖ := by
  rw [← map_sub, ← inner_sub_left]
  exact (RCLike.abs_re_le_norm _).trans (norm_inner_le_norm _ _)

omit [CompleteSpace E0] in
private theorem abs_re_inner_error_right
    {x y z : E0} :
    |RCLike.re ⟪z, x⟫_ℂ - RCLike.re ⟪z, y⟫_ℂ| ≤ ‖z‖ * ‖x - y‖ := by
  rw [← map_sub, ← inner_sub_right]
  exact (RCLike.abs_re_le_norm _).trans (norm_inner_le_norm _ _)

private theorem reflectionTangent_pair_norm_estimates
    (T : E0 →L[ℂ] E1) (C0 : E0 →L[ℂ] E0) (C1 : E1 →L[ℂ] E1)
    (hC0 : IsSelfAdjoint C0) (hC1 : IsSelfAdjoint C1)
    (hC0unit : IsUnit C0) (hC1unit : IsUnit C1)
    (hgram0 : C0.adjoint ∘L C0 ∘L (1 + T.adjoint ∘L T) = 1)
    (hgram1 : C1.adjoint ∘L C1 ∘L (1 + T ∘L T.adjoint) = 1)
    {u : E0} {v : E1} {t eps : ℝ} (ht0 : 0 ≤ t) (htnorm : t ≤ ‖T‖)
    (hTu : ‖T u - (t : ℂ) • v‖ ≤ eps)
    (hTv : ‖T.adjoint v - (t : ℂ) • u‖ ≤ eps) :
    let J0 := C0.polarIsometryOfIsUnitModulus
    let J1 := C1.polarIsometryOfIsUnitModulus
    let q : ℝ := Real.sqrt (1 + ‖T‖ ^ 2)
    let c : ℝ := (Real.sqrt (1 + t ^ 2))⁻¹
    let M0 : ℝ := 2 * ‖C0‖ ^ 2 * ‖T‖ * q
    let M1 : ℝ := 2 * ‖C1‖ ^ 2 * ‖T‖ * q
    (‖C1.modulus v - (c : ℂ) • v‖ ≤ M1 * eps) ∧
      (‖C0 u - (c : ℂ) • J0 u‖ ≤ M0 * eps) ∧
      (‖T.adjoint (C1.modulus v) - ((c * t : ℝ) : ℂ) • u‖ ≤
        (‖T‖ * M1 + 1) * eps) ∧
      (‖C1 (T u) - ((c * t : ℝ) : ℂ) • J1 v‖ ≤
        (‖C1‖ + ‖T‖ * M1) * eps) := by
  let J0 := C0.polarIsometryOfIsUnitModulus
  let J1 := C1.polarIsometryOfIsUnitModulus
  let q : ℝ := Real.sqrt (1 + ‖T‖ ^ 2)
  let r : ℝ := Real.sqrt (1 + t ^ 2)
  let c : ℝ := r⁻¹
  let M0 : ℝ := 2 * ‖C0‖ ^ 2 * ‖T‖ * q
  let M1 : ℝ := 2 * ‖C1‖ ^ 2 * ‖T‖ * q
  have heps0 : 0 ≤ eps := (norm_nonneg _).trans hTu
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hmod0 : ‖C0.modulus u - (c : ℂ) • u‖ ≤ M0 * eps := by
    simpa [q, r, c, M0] using
      gram_residual_of_tangent_pair_right C0 T hgram0 ht0 htnorm hTu hTv
  have hmod1 : ‖C1.modulus v - (c : ℂ) • v‖ ≤ M1 * eps := by
    have htnormAdj : t ≤ ‖T.adjoint‖ := by
      simpa only [ContinuousLinearMap.adjoint.norm_map] using htnorm
    have hgram1Adj :
        C1.adjoint ∘L C1 ∘L (1 + (T.adjoint).adjoint ∘L T.adjoint) = 1 := by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using hgram1
    have hTuAdj : ‖T.adjoint.adjoint u - (t : ℂ) • v‖ ≤ eps := by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using hTu
    have hraw := gram_residual_of_tangent_pair_right
      (C := C1) (T := T.adjoint) (u := v) (v := u) (t := t) (eps := eps)
      hgram1Adj ht0 htnormAdj hTv hTuAdj
    simpa [q, r, c, M1, ContinuousLinearMap.adjoint.norm_map] using hraw
  have hC0polar : ‖C0 u - (c : ℂ) • J0 u‖ ≤ M0 * eps := by
    have hM0 : IsUnit C0.modulus := isUnit_modulus_of_isUnit_selfAdjoint C0 hC0 hC0unit
    have hJ0modulus : J0 (C0.modulus u) = C0 u := by
      dsimp [J0]
      exact C0.polarIsometryOfIsUnitModulus_modulus_apply hM0 u
    have hvec0 :
        C0 u - (c : ℂ) • J0 u =
          J0 (C0.modulus u - (c : ℂ) • u) := by
      rw [J0.map_sub, J0.map_smul (c : ℂ) u, hJ0modulus]
    calc
      ‖C0 u - (c : ℂ) • J0 u‖ =
          ‖J0 (C0.modulus u - (c : ℂ) • u)‖ := by rw [hvec0]
      _ = ‖C0.modulus u - (c : ℂ) • u‖ := by
        simpa only [J0] using
          C0.norm_polarIsometryOfIsUnitModulus_apply hM0
            (C0.modulus u - (c : ℂ) • u)
      _ ≤ M0 * eps := hmod0
  have hC1polar : ‖C1 v - (c : ℂ) • J1 v‖ ≤ M1 * eps := by
    have hM1 : IsUnit C1.modulus := isUnit_modulus_of_isUnit_selfAdjoint C1 hC1 hC1unit
    have hJ1modulus : J1 (C1.modulus v) = C1 v := by
      dsimp [J1]
      exact C1.polarIsometryOfIsUnitModulus_modulus_apply hM1 v
    have hvec1 :
        C1 v - (c : ℂ) • J1 v =
          J1 (C1.modulus v - (c : ℂ) • v) := by
      rw [J1.map_sub, J1.map_smul (c : ℂ) v, hJ1modulus]
    calc
      ‖C1 v - (c : ℂ) • J1 v‖ =
          ‖J1 (C1.modulus v - (c : ℂ) • v)‖ := by rw [hvec1]
      _ = ‖C1.modulus v - (c : ℂ) • v‖ := by
        simpa only [J1] using
          C1.norm_polarIsometryOfIsUnitModulus_apply hM1
            (C1.modulus v - (c : ℂ) • v)
      _ ≤ M1 * eps := hmod1
  have hTstarMod :
      ‖T.adjoint (C1.modulus v) - ((c * t : ℝ) : ℂ) • u‖ ≤
        (‖T‖ * M1 + 1) * eps := by
    have hsplit :
        T.adjoint (C1.modulus v) - ((c * t : ℝ) : ℂ) • u =
          T.adjoint (C1.modulus v - (c : ℂ) • v) +
            (c : ℂ) • (T.adjoint v - (t : ℂ) • u) := by
      rw [map_sub, ContinuousLinearMap.map_smul, smul_sub, smul_smul]
      norm_num
    rw [hsplit]
    calc
      _ ≤ ‖T.adjoint (C1.modulus v - (c : ℂ) • v)‖ +
          ‖(c : ℂ) • (T.adjoint v - (t : ℂ) • u)‖ := norm_add_le _ _
      _ ≤ ‖T‖ * (M1 * eps) + c * eps := by
        have hleft := T.adjoint.le_opNorm (C1.modulus v - (c : ℂ) • v)
        rw [ContinuousLinearMap.adjoint.norm_map] at hleft
        have hleft' := hleft.trans
          (mul_le_mul_of_nonneg_left hmod1 (norm_nonneg T))
        have hright : ‖(c : ℂ) • (T.adjoint v - (t : ℂ) • u)‖ ≤ c * eps := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
          exact mul_le_mul_of_nonneg_left hTv hc0.le
        exact add_le_add hleft' hright
      _ ≤ (‖T‖ * M1 + 1) * eps := by
        have hc_le_one : c ≤ 1 := by
          have hr1 : 1 ≤ r := by
            dsimp [r]
            calc
              1 = Real.sqrt 1 := by norm_num
              _ ≤ Real.sqrt (1 + t ^ 2) :=
                Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg t])
          dsimp [c]
          exact (inv_le_one₀ hr0).2 hr1
        have hceps : c * eps ≤ eps := by
          have := mul_le_mul_of_nonneg_right hc_le_one heps0
          simpa [one_mul] using this
        linarith only [hceps]
  have hC1T :
      ‖C1 (T u) - ((c * t : ℝ) : ℂ) • J1 v‖ ≤
        (‖C1‖ + ‖T‖ * M1) * eps := by
    have hsplit :
        C1 (T u) - ((c * t : ℝ) : ℂ) • J1 v =
          C1 (T u - (t : ℂ) • v) +
            (t : ℂ) • (C1 v - (c : ℂ) • J1 v) := by
      rw [map_sub, ContinuousLinearMap.map_smul, smul_sub, smul_smul]
      module
    rw [hsplit]
    calc
      _ ≤ ‖C1 (T u - (t : ℂ) • v)‖ +
          ‖(t : ℂ) • (C1 v - (c : ℂ) • J1 v)‖ := norm_add_le _ _
      _ ≤ ‖C1‖ * eps + t * (M1 * eps) := by
        have hleft := C1.le_opNorm (T u - (t : ℂ) • v)
        have hleft' := hleft.trans
          (mul_le_mul_of_nonneg_left hTu (norm_nonneg C1))
        have hright : ‖(t : ℂ) • (C1 v - (c : ℂ) • J1 v)‖ ≤ t * (M1 * eps) := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
          exact mul_le_mul_of_nonneg_left hC1polar ht0
        exact add_le_add hleft' hright
      _ ≤ (‖C1‖ + ‖T‖ * M1) * eps := by
        have hM1eps : 0 ≤ M1 * eps := by
          dsimp [M1]
          positivity
        have htM1 : t * (M1 * eps) ≤ ‖T‖ * (M1 * eps) :=
          mul_le_mul_of_nonneg_right htnorm hM1eps
        linarith only [htM1]
  exact ⟨hmod1, hC0polar, hTstarMod, hC1T⟩

omit [CompleteSpace E0] [CompleteSpace E1] in
private theorem abs_re_inner_map_approx_scaled
    (B : E0 →L[ℂ] E1) {x y : E0} {z : E1} {c M eps : ℝ}
    (hz : ‖z‖ = 1) (hc0 : 0 < c) (hxy : ‖x - (c : ℂ) • y‖ ≤ M * eps) :
    |RCLike.re ⟪z, B x⟫_ℂ| ≤
      c * |RCLike.re ⟪z, B y⟫_ℂ| + ‖B‖ * (M * eps) := by
  let x0 : ℝ := RCLike.re ⟪z, B (x)⟫_ℂ
  let y0 : ℝ := RCLike.re ⟪z, B (y)⟫_ℂ
  let e0 : ℝ := ‖B‖ * (M * eps)
  have hscale :
      RCLike.re ⟪z, B ((c : ℂ) • y)⟫_ℂ = c * y0 := by
    change RCLike.re ⟪z, B ((c : ℂ) • y)⟫_ℂ =
      c * RCLike.re ⟪z, B (y)⟫_ℂ
    rw [B.map_smul (c : ℂ) (y), inner_smul_right]
    change (((c : ℂ) * ⟪z, B (y)⟫_ℂ).re) =
      c * (⟪z, B (y)⟫_ℂ).re
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have herr : |x0 - c * y0| ≤ e0 := by
    have hBerr : ‖B (x) - B ((c : ℂ) • y)‖ ≤ e0 := by
      dsimp [e0]
      rw [← map_sub]
      exact (B.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hxy (norm_nonneg B))
    have hinner := abs_re_inner_error_right
      (z := z) (x := B (x)) (y := B ((c : ℂ) • y))
    have hbound := hinner.trans (by simpa [hz] using hBerr)
    dsimp [x0]
    rw [hscale] at hbound
    exact hbound
  calc
    |RCLike.re ⟪z, B (x)⟫_ℂ| = |x0| := by rfl
    _ = |(x0 - c * y0) + c * y0| := by congr 1; ring
    _ ≤ |x0 - c * y0| + |c * y0| := abs_add_le _ _
    _ ≤ e0 + c * |y0| := by
      gcongr
      rw [abs_mul, abs_of_pos hc0]
    _ = c * |y0| + e0 := by ring
    _ = c * |RCLike.re ⟪z, B (y)⟫_ℂ| + ‖B‖ * (M * eps) := by rfl

/-- Per approximate singular pair, equation (7.6) controls the **actual**
tangent singular value by two residual pairings.  The polar factors of the
signed cosine blocks are where the two angle branches are absorbed. -/
theorem reflectionTangent_approximate_pair
    (A0 : E0 →L[ℂ] E0) (A1 : E1 →L[ℂ] E1) (B T : E0 →L[ℂ] E1)
    (C0 : E0 →L[ℂ] E0) (C1 : E1 →L[ℂ] E1)
    (_hA0 : IsSelfAdjoint A0) (_hA1 : IsSelfAdjoint A1)
    (hC0 : IsSelfAdjoint C0) (hC1 : IsSelfAdjoint C1)
    (hC0unit : IsUnit C0) (hC1unit : IsUnit C1)
    {a b : ℝ} (_hab : a < b)
    (hA0high : ∀ x : E0, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A0 x, x⟫_ℂ)
    (hA1low : ∀ y : E1, RCLike.re ⟪A1 y, y⟫_ℂ ≤ a * ‖y‖ ^ 2)
    (hgram0 : C0.adjoint ∘L C0 ∘L (1 + T.adjoint ∘L T) = 1)
    (hgram1 : C1.adjoint ∘L C1 ∘L (1 + T ∘L T.adjoint) = 1)
    (heq76 : (C1 ∘L T) ∘L A0 - A1 ∘L (C1 ∘L T) =
      B ∘L C0 + C1 ∘L B)
    {u : E0} {v : E1} {t eps : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ht0 : 0 ≤ t) (htnorm : t ≤ ‖T‖)
    (hTu : ‖T u - (t : ℂ) • v‖ ≤ eps)
    (hTv : ‖T.adjoint v - (t : ℂ) • u‖ ≤ eps) :
    (b - a) * t ≤
      |RCLike.re ⟪v, B u⟫_ℂ| +
        |RCLike.re ⟪C1.polarIsometryOfIsUnitModulus v,
          B (C0.polarIsometryOfIsUnitModulus u)⟫_ℂ| +
        reflectionTangentErrorCoefficient A0 A1 B T C0 C1 * eps := by
  let J0 := C0.polarIsometryOfIsUnitModulus
  let J1 := C1.polarIsometryOfIsUnitModulus
  let q : ℝ := Real.sqrt (1 + ‖T‖ ^ 2)
  let r : ℝ := Real.sqrt (1 + t ^ 2)
  let c : ℝ := r⁻¹
  let M0 : ℝ := 2 * ‖C0‖ ^ 2 * ‖T‖ * q
  let M1 : ℝ := 2 * ‖C1‖ ^ 2 * ‖T‖ * q
  have heps0 : 0 ≤ eps := (norm_nonneg _).trans hTu
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hrleq : r ≤ q := by
    dsimp [r, q]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hqc : 1 ≤ q * c := by
    dsimp [c]
    rw [le_mul_inv_iff₀ hr0]
    simpa [one_mul] using hrleq
  have hJ0norm : ‖J0 u‖ = 1 := by
    dsimp [J0]
    rw [norm_polar_apply C0 hC0 hC0unit, hu]
  have hJ1norm : ‖J1 v‖ = 1 := by
    dsimp [J1]
    rw [norm_polar_apply C1 hC1 hC1unit, hv]
  obtain ⟨hmod1, hC0polar, hTstarMod, hC1T⟩ :=
    reflectionTangent_pair_norm_estimates T C0 C1 hC0 hC1 hC0unit hC1unit
      hgram0 hgram1 ht0 htnorm hTu hTv
  change ‖C1.modulus v - (c : ℂ) • v‖ ≤ M1 * eps at hmod1
  change ‖C0 u - (c : ℂ) • J0 u‖ ≤ M0 * eps at hC0polar
  change ‖T.adjoint (C1.modulus v) - ((c * t : ℝ) : ℂ) • u‖ ≤
    (‖T‖ * M1 + 1) * eps at hTstarMod
  change ‖C1 (T u) - ((c * t : ℝ) : ℂ) • J1 v‖ ≤
    (‖C1‖ + ‖T‖ * M1) * eps at hC1T
  have hEq := congrArg (fun L : E0 →L[ℂ] E1 => L u) heq76
  simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply] at hEq
  have hEqInner := congrArg (fun z : E1 => RCLike.re ⟪J1 v, z⟫_ℂ) hEq
  simp only [inner_sub_right, inner_add_right, map_sub, map_add] at hEqInner
  have hterm0 :
      c * t * b - ‖A0‖ * ((‖T‖ * M1 + 1) * eps) ≤
        RCLike.re ⟪J1 v, C1 (T (A0 u))⟫_ℂ := by
    have hmove : ⟪J1 v, C1 (T (A0 u))⟫_ℂ =
        ⟪T.adjoint (C1.modulus v), A0 u⟫_ℂ := by
      calc
        _ = ⟪C1 (J1 v), T (A0 u)⟫_ℂ := by
          rw [← ContinuousLinearMap.adjoint_inner_left, hC1.adjoint_eq]
        _ = ⟪C1.modulus v, T (A0 u)⟫_ℂ := by
          rw [selfAdjoint_polar_then_apply_eq_modulus C1 hC1 hC1unit]
        _ = _ := (ContinuousLinearMap.adjoint_inner_left T _ _).symm
    rw [hmove]
    have herr := abs_re_inner_error_left
      (x := T.adjoint (C1.modulus v)) (y := ((c * t : ℝ) : ℂ) • u)
      (z := A0 u)
    have hA0u : ‖A0 u‖ ≤ ‖A0‖ := by
      calc ‖A0 u‖ ≤ ‖A0‖ * ‖u‖ := A0.le_opNorm u
        _ = ‖A0‖ := by rw [hu, mul_one]
    have herr' :
        |RCLike.re ⟪T.adjoint (C1.modulus v), A0 u⟫_ℂ -
          c * t * RCLike.re ⟪u, A0 u⟫_ℂ| ≤
          ‖A0‖ * ((‖T‖ * M1 + 1) * eps) := by
      have := herr.trans (mul_le_mul hTstarMod hA0u (norm_nonneg _) (by positivity))
      simpa [inner_smul_left, RCLike.re_ofReal_mul, mul_assoc, mul_left_comm,
        mul_comm] using this
    have hform : b ≤ RCLike.re ⟪u, A0 u⟫_ℂ := by
      have h := hA0high u
      rw [hu] at h
      calc
        b ≤ RCLike.re ⟪A0 u, u⟫_ℂ := by simpa using h
        _ = RCLike.re ⟪u, A0 u⟫_ℂ := inner_re_symm (A0 u) u
    rw [abs_le] at herr'
    have hct0 : 0 ≤ c * t := mul_nonneg hc0.le ht0
    have hformScaled := mul_le_mul_of_nonneg_left hform hct0
    linarith only [herr'.1, hformScaled]
  have hterm1 :
      RCLike.re ⟪J1 v, A1 (C1 (T u))⟫_ℂ ≤
        c * t * a + ‖A1‖ * ((‖C1‖ + ‖T‖ * M1) * eps) := by
    have herr := abs_re_inner_error_right
      (z := J1 v) (x := A1 (C1 (T u)))
      (y := A1 (((c * t : ℝ) : ℂ) • J1 v))
    have hAerr :
        ‖A1 (C1 (T u)) - A1 (((c * t : ℝ) : ℂ) • J1 v)‖ ≤
          ‖A1‖ * ((‖C1‖ + ‖T‖ * M1) * eps) := by
      rw [← map_sub]
      exact (A1.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hC1T (norm_nonneg A1))
    have herr' :
        |RCLike.re ⟪J1 v, A1 (C1 (T u))⟫_ℂ -
          c * t * RCLike.re ⟪J1 v, A1 (J1 v)⟫_ℂ| ≤
          ‖A1‖ * ((‖C1‖ + ‖T‖ * M1) * eps) := by
      have := herr.trans (by simpa [hJ1norm] using hAerr)
      simpa [ContinuousLinearMap.map_smul, inner_smul_right, RCLike.re_ofReal_mul, mul_assoc] using this
    rw [abs_le] at herr'
    have hform : RCLike.re ⟪J1 v, A1 (J1 v)⟫_ℂ ≤ a := by
      have h := hA1low (J1 v)
      rw [hJ1norm] at h
      calc
        RCLike.re ⟪J1 v, A1 (J1 v)⟫_ℂ =
            RCLike.re ⟪A1 (J1 v), J1 v⟫_ℂ := inner_re_symm (J1 v) (A1 (J1 v))
        _ ≤ a := by simpa using h
    have hct0 : 0 ≤ c * t := mul_nonneg hc0.le ht0
    have hformScaled := mul_le_mul_of_nonneg_left hform hct0
    linarith only [herr'.2, hformScaled]
  have hrhs0 :
      |RCLike.re ⟪J1 v, B (C0 u)⟫_ℂ| ≤
        c * |RCLike.re ⟪J1 v, B (J0 u)⟫_ℂ| + ‖B‖ * (M0 * eps) :=
    abs_re_inner_map_approx_scaled B hJ1norm hc0 hC0polar
  have hrhs1 :
      |RCLike.re ⟪J1 v, C1 (B u)⟫_ℂ| ≤
        c * |RCLike.re ⟪v, B u⟫_ℂ| + ‖B‖ * (M1 * eps) := by
    have hmove : ⟪J1 v, C1 (B u)⟫_ℂ = ⟪C1.modulus v, B u⟫_ℂ := by
      calc
        _ = ⟪C1 (J1 v), B u⟫_ℂ := by
          rw [← ContinuousLinearMap.adjoint_inner_left, hC1.adjoint_eq]
        _ = _ := by rw [selfAdjoint_polar_then_apply_eq_modulus C1 hC1 hC1unit]
    rw [hmove]
    let x1 : ℝ := RCLike.re ⟪C1.modulus v, B u⟫_ℂ
    let y1 : ℝ := RCLike.re ⟪v, B u⟫_ℂ
    let e1 : ℝ := ‖B‖ * (M1 * eps)
    have hBu : ‖B u‖ ≤ ‖B‖ := by
      calc
        ‖B u‖ ≤ ‖B‖ * ‖u‖ := B.le_opNorm u
        _ = ‖B‖ := by rw [hu, mul_one]
    have hscale : RCLike.re ⟪(c : ℂ) • v, B u⟫_ℂ = c * y1 := by
      change RCLike.re ⟪(c : ℂ) • v, B u⟫_ℂ =
        c * RCLike.re ⟪v, B u⟫_ℂ
      rw [inner_smul_left, Complex.conj_ofReal]
      change (((c : ℂ) * ⟪v, B u⟫_ℂ).re) = c * (⟪v, B u⟫_ℂ).re
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have herr : |x1 - c * y1| ≤ e1 := by
      have hinner := abs_re_inner_error_left
        (x := C1.modulus v) (y := (c : ℂ) • v) (z := B u)
      have hM1eps : 0 ≤ M1 * eps := by
        dsimp [M1]
        positivity
      have hbound := hinner.trans
        (mul_le_mul hmod1 hBu (norm_nonneg _) hM1eps)
      dsimp [x1, e1]
      rw [hscale] at hbound
      simpa [mul_comm] using hbound
    calc
      |RCLike.re ⟪C1.modulus v, B u⟫_ℂ| = |x1| := by rfl
      _ = |(x1 - c * y1) + c * y1| := by congr 1; ring
      _ ≤ |x1 - c * y1| + |c * y1| := abs_add_le _ _
      _ ≤ e1 + c * |y1| := by
        gcongr
        rw [abs_mul, abs_of_pos hc0]
      _ = c * |y1| + e1 := by ring
      _ = c * |RCLike.re ⟪v, B u⟫_ℂ| + ‖B‖ * (M1 * eps) := by rfl
  have hmain :
      c * ((b - a) * t) ≤
        c * (|RCLike.re ⟪v, B u⟫_ℂ| +
          |RCLike.re ⟪J1 v, B (J0 u)⟫_ℂ|) +
        (‖A0‖ * (‖T‖ * M1 + 1) +
          ‖A1‖ * (‖C1‖ + ‖T‖ * M1) + ‖B‖ * (M0 + M1)) * eps := by
    have hEqReal :
        RCLike.re ⟪J1 v, C1 (T (A0 u))⟫_ℂ -
            RCLike.re ⟪J1 v, A1 (C1 (T u))⟫_ℂ =
          RCLike.re ⟪J1 v, B (C0 u)⟫_ℂ +
            RCLike.re ⟪J1 v, C1 (B u)⟫_ℂ := hEqInner
    have hRabs :
        RCLike.re ⟪J1 v, B (C0 u)⟫_ℂ +
            RCLike.re ⟪J1 v, C1 (B u)⟫_ℂ ≤
          |RCLike.re ⟪J1 v, B (C0 u)⟫_ℂ| +
            |RCLike.re ⟪J1 v, C1 (B u)⟫_ℂ| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    linarith only [hterm0, hterm1, hEqReal, hRabs, hrhs0, hrhs1]
  have hcr : r * c = 1 := by
    dsimp [c]
    exact mul_inv_cancel₀ hr0.ne'
  let Ecoef : ℝ := ‖A0‖ * (‖T‖ * M1 + 1) +
    ‖A1‖ * (‖C1‖ + ‖T‖ * M1) + ‖B‖ * (M0 + M1)
  have hE0 : 0 ≤ Ecoef * eps := by
    dsimp [Ecoef]
    positivity
  have hmainMul := mul_le_mul_of_nonneg_left hmain hr0.le
  have hEr : r * (Ecoef * eps) ≤ q * (Ecoef * eps) :=
    mul_le_mul_of_nonneg_right hrleq hE0
  calc
    (b - a) * t = r * (c * ((b - a) * t)) := by
      rw [← mul_assoc, hcr, one_mul]
    _ ≤ r * (c * (|RCLike.re ⟪v, B u⟫_ℂ| +
          |RCLike.re ⟪J1 v, B (J0 u)⟫_ℂ|) + Ecoef * eps) := by
      simpa only [Ecoef] using hmainMul
    _ = |RCLike.re ⟪v, B u⟫_ℂ| +
          |RCLike.re ⟪J1 v, B (J0 u)⟫_ℂ| + r * (Ecoef * eps) := by
      rw [mul_add, ← mul_assoc, hcr, one_mul]
    _ ≤ |RCLike.re ⟪v, B u⟫_ℂ| +
          |RCLike.re ⟪J1 v, B (J0 u)⟫_ℂ| + q * (Ecoef * eps) := by
      gcongr
    _ = |RCLike.re ⟪v, B u⟫_ℂ| +
          |RCLike.re ⟪J1 v, B (J0 u)⟫_ℂ| +
            reflectionTangentErrorCoefficient A0 A1 B T C0 C1 * eps := by
      unfold reflectionTangentErrorCoefficient
      dsimp only [q, M0, M1, Ecoef]
      ring

/-- Sum the per-pair estimate over an approximate leading singular family. -/
theorem reflectionTangent_selected_le_kyFan_add_error
    (A0 : E0 →L[ℂ] E0) (A1 : E1 →L[ℂ] E1) (B T : E0 →L[ℂ] E1)
    (C0 : E0 →L[ℂ] E0) (C1 : E1 →L[ℂ] E1)
    (hA0 : IsSelfAdjoint A0) (hA1 : IsSelfAdjoint A1)
    (hC0 : IsSelfAdjoint C0) (hC1 : IsSelfAdjoint C1)
    (hC0unit : IsUnit C0) (hC1unit : IsUnit C1)
    {a b : ℝ} (hab : a < b)
    (hA0high : ∀ x : E0, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A0 x, x⟫_ℂ)
    (hA1low : ∀ y : E1, RCLike.re ⟪A1 y, y⟫_ℂ ≤ a * ‖y‖ ^ 2)
    (hgram0 : C0.adjoint ∘L C0 ∘L (1 + T.adjoint ∘L T) = 1)
    (hgram1 : C1.adjoint ∘L C1 ∘L (1 + T ∘L T.adjoint) = 1)
    (heq76 : (C1 ∘L T) ∘L A0 - A1 ∘L (C1 ∘L T) =
      B ∘L C0 + C1 ∘L B)
    {k : ℕ} {eps : ℝ} (F : ApproximateLeadingSingularFamily T k eps) :
    (b - a) * ∑ i : Fin F.count, T.approximationNumber (i : ℕ) ≤
      2 * kyFanApproximationGauge F.count B +
        F.count * (reflectionTangentErrorCoefficient A0 A1 B T C0 C1 * eps) := by
  let J0 := C0.polarIsometryOfIsUnitModulus
  let J1 := C1.polarIsometryOfIsUnitModulus
  have hJ0 := orthonormal_polar_comp C0 hC0 hC0unit F.right_orthonormal
  have hJ1 := orthonormal_polar_comp C1 hC1 hC1unit F.left_orthonormal
  have hscalar : ∀ i : Fin F.count,
      (b - a) * T.approximationNumber (i : ℕ) ≤
        |RCLike.re ⟪F.left i, B (F.right i)⟫_ℂ| +
          |RCLike.re ⟪J1 (F.left i), B (J0 (F.right i))⟫_ℂ| +
          reflectionTangentErrorCoefficient A0 A1 B T C0 C1 * eps := by
    intro i
    exact reflectionTangent_approximate_pair A0 A1 B T C0 C1
      hA0 hA1 hC0 hC1 hC0unit hC1unit hab hA0high hA1low hgram0 hgram1 heq76
      (F.right_orthonormal.norm_eq_one i) (F.left_orthonormal.norm_eq_one i)
      (T.approximationNumber_nonneg _) (approximationNumber_le_norm_local T _)
      (F.apply_residual i) (F.adjoint_residual i)
  have hsum :
      ∑ i : Fin F.count, (b - a) * T.approximationNumber (i : ℕ) ≤
        ∑ i : Fin F.count,
          (|RCLike.re ⟪F.left i, B (F.right i)⟫_ℂ| +
            |RCLike.re ⟪J1 (F.left i), B (J0 (F.right i))⟫_ℂ| +
            reflectionTangentErrorCoefficient A0 A1 B T C0 C1 * eps) := by
    exact Finset.sum_le_sum (fun i _ => hscalar i)
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hvar0 := sum_abs_le_kyFanApproximationGauge_of_orthonormal B
    F.left_orthonormal F.right_orthonormal
    (t := fun i => |RCLike.re ⟪F.left i, B (F.right i)⟫_ℂ|)
    (fun _i => le_rfl)
  have hvar1 := sum_abs_le_kyFanApproximationGauge_of_orthonormal B
    hJ1 hJ0
    (t := fun i => |RCLike.re ⟪J1 (F.left i), B (J0 (F.right i))⟫_ℂ|)
    (fun _i => le_rfl)
  calc
    (b - a) * ∑ i : Fin F.count, T.approximationNumber (i : ℕ) =
        ∑ i : Fin F.count, (b - a) * T.approximationNumber (i : ℕ) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin F.count, |RCLike.re ⟪F.left i, B (F.right i)⟫_ℂ| +
        ∑ i : Fin F.count, |RCLike.re ⟪J1 (F.left i), B (J0 (F.right i))⟫_ℂ| +
          F.count * (reflectionTangentErrorCoefficient A0 A1 B T C0 C1 * eps) := hsum
    _ ≤ kyFanApproximationGauge F.count B + kyFanApproximationGauge F.count B +
          F.count * (reflectionTangentErrorCoefficient A0 A1 B T C0 C1 * eps) := by
          exact add_le_add (add_le_add hvar0 hvar1) le_rfl
    _ = 2 * kyFanApproximationGauge F.count B +
          F.count * (reflectionTangentErrorCoefficient A0 A1 B T C0 C1 * eps) := by ring

/-- **Dimension-free Ky Fan reflection tangent theorem.** -/
theorem reflectionTangent_all_kyFan
    (A0 : E0 →L[ℂ] E0) (A1 : E1 →L[ℂ] E1) (B T : E0 →L[ℂ] E1)
    (C0 : E0 →L[ℂ] E0) (C1 : E1 →L[ℂ] E1)
    (hA0 : IsSelfAdjoint A0) (hA1 : IsSelfAdjoint A1)
    (hC0 : IsSelfAdjoint C0) (hC1 : IsSelfAdjoint C1)
    (hC0unit : IsUnit C0) (hC1unit : IsUnit C1)
    {a b : ℝ} (hab : a < b)
    (hA0high : ∀ x : E0, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A0 x, x⟫_ℂ)
    (hA1low : ∀ y : E1, RCLike.re ⟪A1 y, y⟫_ℂ ≤ a * ‖y‖ ^ 2)
    (hgram0 : C0.adjoint ∘L C0 ∘L (1 + T.adjoint ∘L T) = 1)
    (hgram1 : C1.adjoint ∘L C1 ∘L (1 + T ∘L T.adjoint) = 1)
    (heq76 : (C1 ∘L T) ∘L A0 - A1 ∘L (C1 ∘L T) =
      B ∘L C0 + C1 ∘L B) :
    ∀ k : ℕ, (b - a) * kyFanApproximationGauge k T ≤
      2 * kyFanApproximationGauge k B := by
  intro k
  have hd : 0 < b - a := by linarith
  set Ctot := reflectionTangentErrorCoefficient A0 A1 B T C0 C1 with hCtot
  have hCtot0 : 0 ≤ Ctot := reflectionTangentErrorCoefficient_nonneg A0 A1 B T C0 C1
  refine le_of_forall_pos_le_add ?_
  intro eta heta
  set D : ℝ := (k : ℝ) * (Ctot + (b - a)) + 1 with hD
  have hD0 : 0 < D := by
    have : 0 ≤ (k : ℝ) * (Ctot + (b - a)) := by positivity
    rw [hD]
    linarith
  set eps : ℝ := min 1 (eta / D) with heps
  have heps0 : 0 < eps := by
    rw [heps]
    exact lt_min (by norm_num) (div_pos heta hD0)
  have hepsta : eps ≤ eta / D := min_le_right _ _
  obtain ⟨F⟩ := exists_approximateLeadingSingularFamily T k heps0
  have hselected := reflectionTangent_selected_le_kyFan_add_error A0 A1 B T C0 C1
    hA0 hA1 hC0 hC1 hC0unit hC1unit hab hA0high hA1low hgram0 hgram1 heq76 F
  have hBmono : kyFanApproximationGauge F.count B ≤ kyFanApproximationGauge k B :=
    kyFanApproximationGauge_mono_length B F.count_le
  have hprefix :
      (b - a) * Finset.sum (Finset.range F.count) (fun n => T.approximationNumber n) ≤
        2 * kyFanApproximationGauge k B + (k : ℝ) * (Ctot * eps) := by
    have hsumfin : ∑ i : Fin F.count, T.approximationNumber (i : ℕ) =
        Finset.sum (Finset.range F.count) (fun n => T.approximationNumber n) := by
      rw [← Fin.sum_univ_eq_sum_range]
    rw [hsumfin, ← hCtot] at hselected
    have hcount : (F.count : ℝ) ≤ k := by exact_mod_cast F.count_le
    have herr : (F.count : ℝ) * (Ctot * eps) ≤ k * (Ctot * eps) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    linarith only [hselected, hBmono, herr]
  have htail :
      Finset.sum (Finset.Ico F.count k) (fun n => T.approximationNumber n) ≤
        (k - F.count : ℕ) * eps := by
    calc
      _ ≤ Finset.sum (Finset.Ico F.count k) (fun _n => eps) := by
        refine Finset.sum_le_sum ?_
        intro n hn
        rw [Finset.mem_Ico] at hn
        exact F.tail_small n hn.1 hn.2
      _ = (k - F.count : ℕ) * eps := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
          Nat.cast_sub F.count_le]
  have hsplit :
      kyFanApproximationGauge k T =
        Finset.sum (Finset.range F.count) (fun n => T.approximationNumber n) +
          Finset.sum (Finset.Ico F.count k) (fun n => T.approximationNumber n) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    rw [← Finset.sum_range_add_sum_Ico (f := fun n => T.approximationNumber n) F.count_le]
  have htailScaled :
      (b - a) * Finset.sum (Finset.Ico F.count k) (fun n => T.approximationNumber n) ≤
        (k : ℝ) * ((b - a) * eps) := by
    have h := mul_le_mul_of_nonneg_left htail hd.le
    have hkdiff : ((k - F.count : ℕ) : ℝ) ≤ k := by
      exact_mod_cast Nat.sub_le k F.count
    have hnonneg : 0 ≤ (b - a) * eps := mul_nonneg hd.le heps0.le
    calc
      _ ≤ (b - a) * ((k - F.count : ℕ) * eps) := h
      _ = ((k - F.count : ℕ) : ℝ) * ((b - a) * eps) := by ring
      _ ≤ (k : ℝ) * ((b - a) * eps) :=
        mul_le_mul_of_nonneg_right hkdiff hnonneg
  rw [hsplit, mul_add]
  have herror :
      (k : ℝ) * (Ctot * eps) + (k : ℝ) * ((b - a) * eps) ≤ eta := by
    have hcoef0 : 0 ≤ (k : ℝ) * (Ctot + (b - a)) := by positivity
    have hstep : (k : ℝ) * (Ctot + (b - a)) * eps ≤
        (k : ℝ) * (Ctot + (b - a)) * (eta / D) :=
      mul_le_mul_of_nonneg_left hepsta hcoef0
    have hstep2 : (k : ℝ) * (Ctot + (b - a)) * (eta / D) ≤ eta := by
      rw [mul_div_assoc', div_le_iff₀ hD0]
      rw [hD]
      nlinarith [heta.le]
    calc
      _ = (k : ℝ) * (Ctot + (b - a)) * eps := by ring
      _ ≤ (k : ℝ) * (Ctot + (b - a)) * (eta / D) := hstep
      _ ≤ eta := hstep2
  linarith only [hprefix, htailScaled, herror]

/-- Reflection-block form of `reflectionTangent_all_kyFan`.

The two Pythagorean identities come directly from `Z² = 1`.  The two
intertwining identities say that the cross block is obtained by multiplying the
actual tangent corner by the signed cosine block on either side.  This is the
form in which Section 7 naturally presents the geometry. -/
theorem reflectionTangent_all_kyFan_of_pythagorean
    (A0 : E0 →L[ℂ] E0) (A1 : E1 →L[ℂ] E1) (B T G : E0 →L[ℂ] E1)
    (C0 : E0 →L[ℂ] E0) (C1 : E1 →L[ℂ] E1)
    (hA0 : IsSelfAdjoint A0) (hA1 : IsSelfAdjoint A1)
    (hC0 : IsSelfAdjoint C0) (hC1 : IsSelfAdjoint C1)
    (hC0unit : IsUnit C0) (hC1unit : IsUnit C1)
    {a b : ℝ} (hab : a < b)
    (hA0high : ∀ x : E0, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A0 x, x⟫_ℂ)
    (hA1low : ∀ y : E1, RCLike.re ⟪A1 y, y⟫_ℂ ≤ a * ‖y‖ ^ 2)
    (hpyth0 : C0 ∘L C0 + G.adjoint ∘L G = 1)
    (hpyth1 : C1 ∘L C1 + G ∘L G.adjoint = 1)
    (hleft : C1 ∘L T = G) (hright : T ∘L C0 = G)
    (heq76G : G ∘L A0 - A1 ∘L G = B ∘L C0 + C1 ∘L B) :
    ∀ k : ℕ, (b - a) * kyFanApproximationGauge k T ≤
      2 * kyFanApproximationGauge k B := by
  have hadjIntertwine : C0 ∘L T.adjoint = T.adjoint ∘L C1 := by
    have h := congrArg ContinuousLinearMap.adjoint (hleft.trans hright.symm)
    simpa [ContinuousLinearMap.adjoint_comp, hC0.adjoint_eq, hC1.adjoint_eq,
      ContinuousLinearMap.adjoint_adjoint] using h.symm
  have hcomm0 : C0 ∘L (T.adjoint ∘L T) = (T.adjoint ∘L T) ∘L C0 := by
    calc
      C0 ∘L (T.adjoint ∘L T) = (C0 ∘L T.adjoint) ∘L T := by
        rw [ContinuousLinearMap.comp_assoc]
      _ = (T.adjoint ∘L C1) ∘L T := by rw [hadjIntertwine]
      _ = T.adjoint ∘L (C1 ∘L T) := by rw [ContinuousLinearMap.comp_assoc]
      _ = T.adjoint ∘L (T ∘L C0) := by rw [hleft, hright]
      _ = (T.adjoint ∘L T) ∘L C0 := by rw [ContinuousLinearMap.comp_assoc]
  have hcomm1 : C1 ∘L (T ∘L T.adjoint) = (T ∘L T.adjoint) ∘L C1 := by
    calc
      C1 ∘L (T ∘L T.adjoint) = (C1 ∘L T) ∘L T.adjoint := by
        rw [ContinuousLinearMap.comp_assoc]
      _ = (T ∘L C0) ∘L T.adjoint := by rw [hleft, hright]
      _ = T ∘L (C0 ∘L T.adjoint) := by rw [ContinuousLinearMap.comp_assoc]
      _ = T ∘L (T.adjoint ∘L C1) := by rw [hadjIntertwine]
      _ = (T ∘L T.adjoint) ∘L C1 := by rw [ContinuousLinearMap.comp_assoc]
  have hGadjG : G.adjoint ∘L G = C0 ∘L (T.adjoint ∘L T) ∘L C0 := by
    rw [← hright]
    simp only [ContinuousLinearMap.adjoint_comp, hC0.adjoint_eq,
      ContinuousLinearMap.comp_assoc]
  have hGGadj : G ∘L G.adjoint = C1 ∘L (T ∘L T.adjoint) ∘L C1 := by
    rw [← hleft]
    simp only [ContinuousLinearMap.adjoint_comp, hC1.adjoint_eq,
      ContinuousLinearMap.comp_assoc]
  have hgram0 : C0.adjoint ∘L C0 ∘L (1 + T.adjoint ∘L T) = 1 := by
    rw [hC0.adjoint_eq]
    have h := hpyth0
    rw [hGadjG] at h
    calc
      C0 ∘L C0 ∘L (1 + T.adjoint ∘L T) =
          C0 ∘L C0 + C0 ∘L C0 ∘L (T.adjoint ∘L T) := by
            ext x
            simp only [ContinuousLinearMap.comp_apply, add_apply, one_apply_eq_self,
              map_add]
      _ = C0 ∘L C0 + C0 ∘L (T.adjoint ∘L T) ∘L C0 := by
            noncomm_ring [hcomm0]
      _ = 1 := h
  have hgram1 : C1.adjoint ∘L C1 ∘L (1 + T ∘L T.adjoint) = 1 := by
    rw [hC1.adjoint_eq]
    have h := hpyth1
    rw [hGGadj] at h
    calc
      C1 ∘L C1 ∘L (1 + T ∘L T.adjoint) =
          C1 ∘L C1 + C1 ∘L C1 ∘L (T ∘L T.adjoint) := by
            ext x
            simp only [ContinuousLinearMap.comp_apply, add_apply, one_apply_eq_self,
              map_add]
      _ = C1 ∘L C1 + C1 ∘L (T ∘L T.adjoint) ∘L C1 := by
            noncomm_ring [hcomm1]
      _ = 1 := h
  have heq76 : (C1 ∘L T) ∘L A0 - A1 ∘L (C1 ∘L T) =
      B ∘L C0 + C1 ∘L B := by simpa [hleft] using heq76G
  exact reflectionTangent_all_kyFan A0 A1 B T C0 C1 hA0 hA1 hC0 hC1
    hC0unit hC1unit hab hA0high hA1low hgram0 hgram1 heq76

end
end DavisKahan
end TauCeti
