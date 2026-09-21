/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.Vector
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotation
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.BoundedSpectralTransport
import LeanPool.DavisKahan.DavisKahan.SinTheta.FrameFactorization
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CoerciveUnit
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.OperatorAngle

/-! # Quarter Acute Form Gap -/

open TauCeti.DavisKahan.Angle


/-!
# Dimension-free quarter-angle branch for the off-diagonal tan 2Theta theorem

This is the missing arbitrary-Hilbert-space branch argument.  It does not use
an eigenvector attaining the norm of `(P_U-P_V)^2`.

Put `J = 2P_U-1`, `K = 2P_V-1`, center the two operators at the midpoint of
the common gap, and set

`B = J (A-c)` and `C = K (A+H-c)`.

The ordered form hypotheses make `B` and `C` strictly positive by the same
half-gap.  Off-diagonality gives the exact Lyapunov identity

`C (KJ) + (KJ)^* C = 2 B`.

Conjugating `KJ` by `C^(1/2)` therefore gives a strictly accretive operator.
Similarity transports the spectrum, while `KJ` is normal (indeed unitary), so
the continuous functional calculus turns the strict spectral half-plane bound
into a strict lower bound on `KJ + (KJ)^*`.  Finally

`KJ + JK = 2 - 4(P_U-P_V)^2`

gives `||P_U-P_V||^2 < 1/2`, i.e. the quarter-acute branch.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
private theorem norm_sq_projection_add_norm_sq_complement
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] (x : E) :
    ‖U.starProjection x‖ ^ 2 + ‖x - U.starProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
  have horth : ⟪U.starProjection x, x - U.starProjection x⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (U.starProjection_apply_mem x) (U.sub_starProjection_mem_orthogonal x)
  have hx : U.starProjection x + (x - U.starProjection x) = x := by abel
  calc
    ‖U.starProjection x‖ ^ 2 + ‖x - U.starProjection x‖ ^ 2 =
        ‖U.starProjection x + (x - U.starProjection x)‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℂ), horth, map_zero]
      ring
    _ = ‖x‖ ^ 2 := by rw [hx]


private theorem re_conj_real_mul (r : ℝ) (z : ℂ) :
    RCLike.re ((starRingEnd ℂ) (r : ℂ) * z) = r * RCLike.re z := by
  rw [Complex.conj_ofReal]
  simp

omit [CompleteSpace E] in
private theorem re_conj_real_mul_inner_self (r : ℝ) (x : E) :
    RCLike.re ((starRingEnd ℂ) (r : ℂ) * ⟪x, x⟫_ℂ) = r * ‖x‖ ^ 2 := by
  rw [re_conj_real_mul, inner_self_eq_norm_sq]

omit [CompleteSpace E] in
private theorem re_inner_smul_self (z : ℂ) (x : E) :
    RCLike.re ⟪z • x, x⟫_ℂ = z.re * ‖x‖ ^ 2 := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [RCLike.re_to_complex, pow_two]

omit [CompleteSpace E] in
/-- Reflection through a subspace with doubling written as a complex scalar. -/
private theorem reflection_apply_ofNat_smul
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (w : E) :
    K.reflection w = (2 : ℂ) • K.starProjection w - w := by
  rw [Submodule.reflection_apply, ← Nat.cast_smul_eq_nsmul ℂ]
  norm_num

private theorem star_id_clm :
    star (ContinuousLinearMap.id ℂ E) = ContinuousLinearMap.id ℂ E := by
  change star (1 : E →L[ℂ] E) = (1 : E →L[ℂ] E)
  exact star_one _

omit [CompleteSpace E] in
private theorem opNorm_le_sqrt_of_sq_apply_le
    (D : E →L[ℂ] E) {c : ℝ} (hc : 0 ≤ c)
    (hD : ∀ x, ‖D x‖ ^ 2 ≤ c * ‖x‖ ^ 2) :
    ‖D‖ ≤ Real.sqrt c := by
  refine D.opNorm_le_bound (Real.sqrt_nonneg c) ?_
  intro x
  calc
    ‖D x‖ = Real.sqrt (‖D x‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg (D x))]
    _ ≤ Real.sqrt (c * ‖x‖ ^ 2) := Real.sqrt_le_sqrt (hD x)
    _ = Real.sqrt c * ‖x‖ := by
      rw [Real.sqrt_mul hc, Real.sqrt_sq (norm_nonneg x)]

/-- The reflected centered operator is coercive by half the ordered gap. -/
theorem reflected_centered_form_lower
    (A : E →L[ℂ] E) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A) (hAU : ∀ x ∈ U, A x ∈ U)
    {a b : ℝ}
    (hUhigh : ∀ x ∈ U,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (x : E) :
    (b - a) / 2 * ‖x‖ ^ 2 ≤
      RCLike.re ⟪(U.reflectionOperator ∘L
        (A - (((a + b) / 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E)) x, x⟫_ℂ := by
  have hAsym : A.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hUperp : ∀ y ∈ Uᗮ, A y ∈ Uᗮ := by
    intro y hy
    exact map_mem_orthogonal_of_forall_map_mem hAsym hAU hy
  let p : E := U.starProjection x
  let m : E := x - U.starProjection x
  have hp : p ∈ U := U.starProjection_apply_mem x
  have hm : m ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have hxpm : x = p + m := by simp only [p, m]; abel
  have hAp : A p - (((a + b) / 2 : ℝ) : ℂ) • p ∈ U :=
    U.sub_mem (hAU p hp) (U.smul_mem _ hp)
  have hAm : A m - (((a + b) / 2 : ℝ) : ℂ) • m ∈ Uᗮ :=
    Uᗮ.sub_mem (hUperp m hm) (Uᗮ.smul_mem _ hm)
  have hJx : U.reflectionOperator x = p - m := by
    rw [Submodule.reflectionOperator_apply]
    simp only [p, m]
    module
  have hsplit :
      A x - (((a + b) / 2 : ℝ) : ℂ) • x =
        (A p - (((a + b) / 2 : ℝ) : ℂ) • p) +
        (A m - (((a + b) / 2 : ℝ) : ℂ) • m) := by
    rw [hxpm, map_add, smul_add]
    module
  have hJAp :
      U.reflectionOperator (A p - (((a + b) / 2 : ℝ) : ℂ) • p) =
        A p - (((a + b) / 2 : ℝ) : ℂ) • p := by
    rw [Submodule.reflectionOperator_apply,
      Submodule.starProjection_eq_self_iff.mpr hAp]
    module
  have hJAm :
      U.reflectionOperator (A m - (((a + b) / 2 : ℝ) : ℂ) • m) =
        -(A m - (((a + b) / 2 : ℝ) : ℂ) • m) := by
    rw [Submodule.reflectionOperator_apply,
      (Submodule.starProjection_apply_eq_zero_iff U).mpr hAm]
    module
  have hreflect :
      U.reflectionOperator
          (A x - (((a + b) / 2 : ℝ) : ℂ) • x) =
        (A p - (((a + b) / 2 : ℝ) : ℂ) • p) -
        (A m - (((a + b) / 2 : ℝ) : ℂ) • m) := by
    rw [hsplit, map_add, hJAp, hJAm]
    module
  have hAp_m :
      ⟪A p - (((a + b) / 2 : ℝ) : ℂ) • p, m⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hAp hm
  have hAm_p :
      ⟪A m - (((a + b) / 2 : ℝ) : ℂ) • m, p⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hp hAm
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, smul_apply]
  rw [hreflect, hxpm, inner_sub_left, inner_add_right,
    inner_add_right, hAp_m, hAm_p]
  simp only [add_zero, zero_add, inner_sub_left, inner_smul_left, map_sub]
  have hpBound := hUhigh p hp
  have hmBound := hUperpLow m hm
  have hswapP : RCLike.re ⟪p, A p⟫_ℂ = RCLike.re ⟪A p, p⟫_ℂ :=
    inner_re_symm p (A p)
  have hswapM : RCLike.re ⟪m, A m⟫_ℂ = RCLike.re ⟪A m, m⟫_ℂ :=
    inner_re_symm m (A m)
  have hpyth := norm_sq_projection_add_norm_sq_complement U x
  change ‖p‖ ^ 2 + ‖m‖ ^ 2 = ‖x‖ ^ 2 at hpyth
  have hnormpm : ‖p + m‖ ^ 2 = ‖x‖ ^ 2 := by rw [← hxpm]
  rw [re_conj_real_mul_inner_self, re_conj_real_mul_inner_self, hnormpm]
  calc
    (b - a) / 2 * ‖x‖ ^ 2 =
        (b - a) / 2 * (‖p‖ ^ 2 + ‖m‖ ^ 2) := by rw [hpyth]
    _ = (b * ‖p‖ ^ 2 - (a + b) / 2 * ‖p‖ ^ 2) +
        ((a + b) / 2 * ‖m‖ ^ 2 - a * ‖m‖ ^ 2) := by ring
    _ ≤ (RCLike.re ⟪A p, p⟫_ℂ - (a + b) / 2 * ‖p‖ ^ 2) +
        ((a + b) / 2 * ‖m‖ ^ 2 - RCLike.re ⟪A m, m⟫_ℂ) :=
      add_le_add
        (sub_le_sub_right hpBound ((a + b) / 2 * ‖p‖ ^ 2))
        (sub_le_sub_left hmBound ((a + b) / 2 * ‖m‖ ^ 2))
    _ = RCLike.re ⟪A p, p⟫_ℂ - (a + b) / 2 * ‖p‖ ^ 2 -
        (RCLike.re ⟪A m, m⟫_ℂ - (a + b) / 2 * ‖m‖ ^ 2) := by ring

omit [CompleteSpace E] in
/-- Full off-diagonality is anticommutation with the source reflection. -/
theorem reflection_anticommutes_of_maps_orthogonal
    (H : E →L[ℂ] E) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    U.reflectionOperator ∘L H = -(H ∘L U.reflectionOperator) := by
  apply ContinuousLinearMap.ext
  intro x
  let p : E := U.starProjection x
  let m : E := x - U.starProjection x
  have hp : p ∈ U := U.starProjection_apply_mem x
  have hm : m ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have hxpm : x = p + m := by simp only [p, m]; abel
  have hHp : H p ∈ Uᗮ := hHU p hp
  have hHm : H m ∈ U := hHUperp m hm
  have hJp : U.reflectionOperator p = p := by
    rw [Submodule.reflectionOperator_apply,
      Submodule.starProjection_eq_self_iff.mpr hp]
    module
  have hJm : U.reflectionOperator m = -m := by
    rw [Submodule.reflectionOperator_apply,
      (Submodule.starProjection_apply_eq_zero_iff U).mpr hm]
    module
  have hJHp : U.reflectionOperator (H p) = -(H p) := by
    rw [Submodule.reflectionOperator_apply,
      (Submodule.starProjection_apply_eq_zero_iff U).mpr hHp]
    module
  have hJHm : U.reflectionOperator (H m) = H m := by
    rw [Submodule.reflectionOperator_apply,
      Submodule.starProjection_eq_self_iff.mpr hHm]
    module
  simp only [ContinuousLinearMap.comp_apply, neg_apply]
  calc
    U.reflectionOperator (H x) = U.reflectionOperator (H p + H m) := by
      rw [hxpm, map_add]
    _ = U.reflectionOperator (H p) + U.reflectionOperator (H m) := map_add _ _ _
    _ = -(H p) + H m := by rw [hJHp, hJHm]
    _ = -(H (p - m)) := by
      have hmap : H (p - m) = H p - H m := map_sub H p m
      rw [hmap]
      abel
    _ = -(H (U.reflectionOperator x)) := by
      have hJx : U.reflectionOperator x = p - m := by
        rw [hxpm, map_add, hJp, hJm]
        module
      rw [hJx]

/-- A coercive quadratic form bounds the real spectrum below. -/
theorem spectrum_re_lower_of_coercive
    (T : E →L[ℂ] E) {α : ℝ} (_hα : 0 < α)
    (hcoer : ∀ x, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_ℂ) :
    ∀ z ∈ spectrum ℂ T, α ≤ z.re := by
  intro z hz
  by_contra hnot
  have hgap : 0 < α - z.re := sub_pos.mpr (lt_of_not_ge hnot)
  have hshift : ∀ x,
      (α - z.re) * ‖x‖ ^ 2 ≤
        RCLike.re ⟪(T - z • ContinuousLinearMap.id ℂ E) x, x⟫_ℂ := by
    intro x
    have hx := hcoer x
    have hzinner : RCLike.re ⟪z • x, x⟫_ℂ = z.re * ‖x‖ ^ 2 :=
      re_inner_smul_self z x
    simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, map_sub]
    rw [hzinner]
    linarith
  have hunit : IsUnit (T - z • ContinuousLinearMap.id ℂ E) :=
    TauCeti.ContinuousLinearMap.isUnit_of_coercive hgap hshift
  rw [spectrum.mem_iff] at hz
  apply hz
  rw [Algebra.algebraMap_eq_smul_one]
  have hneg : z • (1 : E →L[ℂ] E) - T = -(T - z • (1 : E →L[ℂ] E)) := by
    module
  rw [hneg]
  exact hunit.neg

/-- A positive Lyapunov identity forces the conjugated operator's spectrum into a right half-plane. -/
private theorem exists_spectrum_re_lower_of_lyapunov
    (W B C : E →L[ℂ] E) {δ : ℝ} (hδ : 0 < δ)
    (hBcoer : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_ℂ)
    (hCstar : IsSelfAdjoint C)
    (hCcoer : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪C x, x⟫_ℂ)
    (hlyap : C ∘L W + star W ∘L C = B + B) :
    ∃ α : ℝ, 0 < α ∧ ∀ z ∈ spectrum ℂ W, α ≤ z.re := by
  classical
  have hCnonneg : (0 : E →L[ℂ] E) ≤ C := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hCstar, ?_⟩
    intro x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    exact (mul_nonneg hδ.le (sq_nonneg ‖x‖)).trans (hCcoer x)
  have hCunit : IsUnit C :=
    TauCeti.ContinuousLinearMap.isUnit_of_coercive hδ hCcoer
  let R : E →L[ℂ] E := C ^ (1 / 2 : ℝ)
  let Rinv : E →L[ℂ] E := C ^ (-1 / 2 : ℝ)
  have hRinvR : Rinv ∘L R = ContinuousLinearMap.id ℂ E := by
    change Rinv * R = 1
    calc
      Rinv * R = C ^ (-1 / 2 : ℝ) * C ^ (1 / 2 : ℝ) := rfl
      _ = C ^ ((-1 / 2 : ℝ) + (1 / 2 : ℝ)) :=
        (CFC.rpow_add hCunit).symm
      _ = C ^ (0 : ℝ) := by norm_num
      _ = 1 := CFC.rpow_zero C hCnonneg
  have hRRinv : R ∘L Rinv = ContinuousLinearMap.id ℂ E := by
    change R * Rinv = 1
    calc
      R * Rinv = C ^ (1 / 2 : ℝ) * C ^ (-1 / 2 : ℝ) := rfl
      _ = C ^ ((1 / 2 : ℝ) + (-1 / 2 : ℝ)) :=
        (CFC.rpow_add hCunit).symm
      _ = C ^ (0 : ℝ) := by norm_num
      _ = 1 := CFC.rpow_zero C hCnonneg
  have hRR : R ∘L R = C := by
    change R * R = C
    calc
      R * R = C ^ (1 / 2 : ℝ) * C ^ (1 / 2 : ℝ) := rfl
      _ = C ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) :=
        (CFC.rpow_add hCunit).symm
      _ = C ^ (1 : ℝ) := by norm_num
      _ = C := CFC.rpow_one C hCnonneg
  have hRstar : star R = R := by
    exact (CFC.rpow_nonneg (a := C) (y := (1 / 2 : ℝ))).isSelfAdjoint.star_eq
  have hRinvstar : star Rinv = Rinv := by
    exact (CFC.rpow_nonneg (a := C) (y := (-1 / 2 : ℝ))).isSelfAdjoint.star_eq
  let Z : E →L[ℂ] E := R ∘L W ∘L Rinv
  have hZstar : star Z = Rinv ∘L star W ∘L R := by
    dsimp [Z]
    change star (R * W * Rinv) = Rinv * star W * R
    rw [star_mul, star_mul, hRstar, hRinvstar]
    simp only [mul_assoc]
  have hleft : Rinv ∘L C = R := by
    apply ContinuousLinearMap.ext
    intro x
    have hRRx := DFunLike.congr_fun hRR x
    have hInv := DFunLike.congr_fun hRinvR (R x)
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hRRx hInv ⊢
    rw [← hRRx]
    exact hInv
  have hright : C ∘L Rinv = R := by
    apply ContinuousLinearMap.ext
    intro x
    have hRRx := DFunLike.congr_fun hRR (Rinv x)
    have hInv := DFunLike.congr_fun hRRinv x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hRRx hInv ⊢
    rw [← hRRx, hInv]
  have hZherm :
      Z + star Z =
        (Rinv ∘L B ∘L Rinv) + (Rinv ∘L B ∘L Rinv) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [hZstar]
    dsimp [Z]
    simp only [add_apply, ContinuousLinearMap.comp_apply]
    have hlyapx := DFunLike.congr_fun hlyap (Rinv x)
    have hconj := congrArg (fun y : E => Rinv y) hlyapx
    simp only [add_apply, ContinuousLinearMap.comp_apply, map_add] at hconj
    have hleftx := DFunLike.congr_fun hleft (W (Rinv x))
    have hrightx := DFunLike.congr_fun hright x
    simp only [ContinuousLinearMap.comp_apply] at hleftx hrightx
    rw [hleftx, hrightx] at hconj
    exact hconj
  let α : ℝ := δ / (1 + ‖R‖ ^ 2)
  have hα : 0 < α := by
    dsimp [α]
    positivity
  have hZcoer : ∀ x, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪Z x, x⟫_ℂ := by
    intro x
    let y : E := Rinv x
    have hxy : R y = x := by
      dsimp [y]
      have := DFunLike.congr_fun hRRinv x
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using this
    have hreal : RCLike.re ⟪Z x, x⟫_ℂ = RCLike.re ⟪B y, y⟫_ℂ := by
      have hsum := congrArg
        (fun T : E →L[ℂ] E => RCLike.re ⟪T x, x⟫_ℂ) hZherm
      simp only [add_apply, inner_add_left, map_add,
        ContinuousLinearMap.comp_apply] at hsum
      have hstarReal : RCLike.re ⟪star Z x, x⟫_ℂ =
          RCLike.re ⟪Z x, x⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_left]
        exact inner_re_symm x (Z x)
      have hRinvAdj : ContinuousLinearMap.adjoint Rinv = Rinv := by
        rw [← ContinuousLinearMap.star_eq_adjoint]
        exact hRinvstar
      have hRinvInner : RCLike.re ⟪Rinv (B y), x⟫_ℂ =
          RCLike.re ⟪B y, y⟫_ℂ := by
        rw [← hRinvAdj, ContinuousLinearMap.adjoint_inner_left]
      rw [hstarReal, hRinvInner] at hsum
      linarith
    have hB := hBcoer y
    have hnorm : ‖x‖ ≤ ‖R‖ * ‖y‖ := by
      rw [← hxy]
      exact R.le_opNorm y
    have hsq : ‖x‖ ^ 2 ≤ ‖R‖ ^ 2 * ‖y‖ ^ 2 := by
      nlinarith [hnorm, norm_nonneg x, norm_nonneg R, norm_nonneg y]
    rw [hreal]
    dsimp [α]
    have hden : 0 < 1 + ‖R‖ ^ 2 := by positivity
    have hcoef : δ / (1 + ‖R‖ ^ 2) * ‖R‖ ^ 2 ≤ δ := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).2
      nlinarith [hδ]
    have hscaled : δ / (1 + ‖R‖ ^ 2) * ‖x‖ ^ 2 ≤ δ * ‖y‖ ^ 2 := by
      calc
        δ / (1 + ‖R‖ ^ 2) * ‖x‖ ^ 2 ≤
            δ / (1 + ‖R‖ ^ 2) * (‖R‖ ^ 2 * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (div_nonneg hδ.le hden.le)
        _ = (δ / (1 + ‖R‖ ^ 2) * ‖R‖ ^ 2) * ‖y‖ ^ 2 := by ring
        _ ≤ δ * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖y‖)
    exact hscaled.trans hB
  have hspecZ : ∀ z ∈ spectrum ℂ Z, α ≤ z.re :=
    spectrum_re_lower_of_coercive Z hα hZcoer
  have hspecWZ : spectrum ℂ W = spectrum ℂ Z := by
    exact spectrum_eq_of_inverse_conjugation W Z Rinv R
      hRRinv hRinvR rfl
  have hspecW : ∀ z ∈ spectrum ℂ W, α ≤ z.re := by
    intro z hz
    rw [hspecWZ] at hz
    exact hspecZ z hz
  exact ⟨α, hα, hspecW⟩

/-- A positive spectral bound for the reflection product gives a strict quarter angle. -/
private theorem isQuarterAcute_of_reflection_spectrum_lower
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {α : ℝ} (hα : 0 < α)
    (hspecW : ∀ z ∈ spectrum ℂ (V.reflectionOperator ∘L U.reflectionOperator), α ≤ z.re) :
    IsQuarterAcute U V := by
  classical
  let J : E →L[ℂ] E := U.reflectionOperator
  let K : E →L[ℂ] E := V.reflectionOperator
  let W : E →L[ℂ] E := K ∘L J
  have hWstar : star W = J ∘L K := by
    change star (K * J) = J * K
    rw [star_mul]
    simp only [J, K, TauCeti.DavisKahan.star_reflectionOperator_complex]
  have hWunit : W ∈ unitary (E →L[ℂ] E) := by
    simpa only [W, K, J, ContinuousLinearMap.mul_def] using
      TauCeti.DavisKahan.spectraReflectionProduct_mem_unitary U V
  let hWnormal : IsStarNormal W := isStarNormal_of_mem_unitary hWunit
  let : IsStarNormal W := hWnormal
  have hshiftForm : ∀ x : E,
      0 ≤ RCLike.re
        ⟪(W + star W - ((2 * α : ℝ) : ℂ) • 1) x, x⟫_ℂ := by
    intro x
    let X : C(spectrum ℂ W, ℂ) :=
      (ContinuousMap.id ℂ).restrict (spectrum ℂ W)
    let g : C(spectrum ℂ W, ℝ) :=
      ⟨fun z => 2 * (z : ℂ).re - 2 * α,
        (continuous_const.mul
          (Complex.continuous_re.comp continuous_subtype_val)).sub continuous_const⟩
    have hg : ∀ z, 0 ≤ g z := by
      intro z
      dsimp [g]
      have hz := hspecW (z : ℂ) z.property
      linarith
    have hpos :=
      TauCeti.BorelCalculus.inner_cfcHom_ofReal_nonneg hWnormal hg x
    have hsymbol :
        TauCeti.BorelCalculus.ofRealLM g =
          X + star X - ((2 * α : ℝ) : ℂ) • 1 := by
      ext z
      dsimp [g, X]
      apply Complex.ext
      · simp
        ring
      · simp
    rw [hsymbol, map_sub, map_add, map_star, map_smul, map_one,
      cfcHom_id] at hpos
    change 0 ≤ RCLike.re
      ⟪x, (W + star W - ((2 * α : ℝ) : ℂ) • 1) x⟫_ℂ at hpos
    exact hpos.trans_eq (inner_re_symm x
      ((W + star W - ((2 * α : ℝ) : ℂ) • 1) x))
  let D : E →L[ℂ] E := U.starProjection - V.starProjection
  have hreflectionAlgebra :
      W + star W =
        (2 : ℂ) • (1 : E →L[ℂ] E) - (4 : ℂ) • (D * D) := by
    rw [hWstar]
    apply ContinuousLinearMap.ext
    intro x
    simp only [add_apply, sub_apply, smul_apply, one_apply_eq_self,
      mul_apply_eq_comp, ContinuousLinearMap.comp_apply]
    dsimp [W, J, K, D]
    have hKJ :
        V.reflectionOperator (U.reflectionOperator x) =
          (4 : ℂ) • V.starProjection (U.starProjection x) -
            (2 : ℂ) • V.starProjection x -
            (2 : ℂ) • U.starProjection x + x := by
      rw [Submodule.reflectionOperator_apply V, Submodule.reflectionOperator_apply U]
      simp only [map_sub, map_smul]
      module
    have hJK :
        U.reflectionOperator (V.reflectionOperator x) =
          (4 : ℂ) • U.starProjection (V.starProjection x) -
            (2 : ℂ) • U.starProjection x -
            (2 : ℂ) • V.starProjection x + x := by
      rw [Submodule.reflectionOperator_apply U, Submodule.reflectionOperator_apply V]
      simp only [map_sub, map_smul]
      module
    have hPU : U.starProjection (U.starProjection x) = U.starProjection x :=
      Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
    have hPV : V.starProjection (V.starProjection x) = V.starProjection x :=
      Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
    have hDDx :
        (U.starProjection - V.starProjection)
            ((U.starProjection - V.starProjection) x) =
          U.starProjection x - U.starProjection (V.starProjection x) -
            V.starProjection (U.starProjection x) + V.starProjection x := by
      simp only [sub_apply, map_sub, hPU, hPV]
      abel
    rw [hKJ, hJK, hDDx]
    module
  have hpoint : ∀ x, ‖D x‖ ^ 2 ≤ (1 - α) / 2 * ‖x‖ ^ 2 := by
    intro x
    have hpositive := hshiftForm x
    rw [hreflectionAlgebra] at hpositive
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, mul_apply_eq_comp] at hpositive
    have hDstar : IsSelfAdjoint D := by
      dsimp [D]
      exact (isSelfAdjoint_starProjection U).sub (isSelfAdjoint_starProjection V)
    have hDsq : RCLike.re ⟪D (D x), x⟫_ℂ = ‖D x‖ ^ 2 := by
      calc
        RCLike.re ⟪D (D x), x⟫_ℂ =
            RCLike.re ⟪(star D) (D x), x⟫_ℂ := by rw [hDstar.star_eq]
        _ = RCLike.re ⟪D x, D x⟫_ℂ := by
          rw [ContinuousLinearMap.star_eq_adjoint,
            ContinuousLinearMap.adjoint_inner_left]
        _ = ‖D x‖ ^ 2 := by rw [inner_self_eq_norm_sq]
    rw [map_sub, map_sub] at hpositive
    have htwo :
        RCLike.re ((starRingEnd ℂ) (2 : ℂ) * ⟪x, x⟫_ℂ) =
          2 * ‖x‖ ^ 2 := by
      simpa using re_conj_real_mul_inner_self (E := E) 2 x
    have hfour :
        RCLike.re ((starRingEnd ℂ) (4 : ℂ) * ⟪D (D x), x⟫_ℂ) =
          4 * RCLike.re ⟪D (D x), x⟫_ℂ := by
      exact re_conj_real_mul 4 ⟪D (D x), x⟫_ℂ
    have halpha :
        RCLike.re ((starRingEnd ℂ) (((2 * α : ℝ) : ℂ)) * ⟪x, x⟫_ℂ) =
          (2 * α) * ‖x‖ ^ 2 := by
      simpa using re_conj_real_mul_inner_self (E := E) (2 * α) x
    rw [htwo, hfour, halpha, hDsq] at hpositive
    linarith
  rcases subsingleton_or_nontrivial E with htriv | hnontriv
  · change ‖U.starProjection - V.starProjection‖ < Real.sqrt 2 / 2
    have hzero : U.starProjection - V.starProjection = 0 :=
      ContinuousLinearMap.ext fun x => Subsingleton.elim _ _
    rw [hzero, norm_zero]
    positivity
  · have hαle1 : α ≤ 1 := by
      obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne (0 : E)
      have hp := hpoint x
      have hxn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
      have hmul : 0 ≤ (1 - α) / 2 * ‖x‖ ^ 2 :=
        (sq_nonneg ‖D x‖).trans hp
      have hc0 : 0 ≤ (1 - α) / 2 :=
        nonneg_of_mul_nonneg_right (by simpa only [mul_comm] using hmul) hxn
      linarith
    have hc : 0 ≤ (1 - α) / 2 := by linarith
    have hDnorm : ‖D‖ ≤ Real.sqrt ((1 - α) / 2) :=
      opNorm_le_sqrt_of_sq_apply_le D hc hpoint
    have hDsq : ‖D‖ ^ 2 < (1 : ℝ) / 2 := by
      have hsquare := pow_le_pow_left₀ (norm_nonneg D) hDnorm 2
      rw [Real.sq_sqrt hc] at hsquare
      have hstrict : (1 - α) / 2 < (1 : ℝ) / 2 := by linarith
      exact hsquare.trans_lt hstrict
    change ‖U.starProjection - V.starProjection‖ < Real.sqrt 2 / 2
    have hthresholdSq : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hthresholdPos : 0 < Real.sqrt 2 / 2 := by positivity
    by_contra hnot
    have hle : Real.sqrt 2 / 2 ≤ ‖D‖ := le_of_not_gt hnot
    have hsqle := pow_le_pow_left₀ hthresholdPos.le hle 2
    rw [hthresholdSq] at hsqle
    exact (not_le_of_gt hDsq) hsqle

/-- Dimension-free strict quarter-angle branch from the paper's ordered form
hypotheses and full off-diagonality. -/
theorem isQuarterAcute_of_orderedFormGap
    (A H : E →L[ℂ] E)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A)
    (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ)
    (hVperpLow : ∀ x ∈ Vᗮ,
      RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    IsQuarterAcute U V := by
  classical
  let c : ℝ := (a + b) / 2
  let δ : ℝ := (b - a) / 2
  let T0 : E →L[ℂ] E := A - (c : ℂ) • ContinuousLinearMap.id ℂ E
  let S0 : E →L[ℂ] E := A + H - (c : ℂ) • ContinuousLinearMap.id ℂ E
  let J : E →L[ℂ] E := U.reflectionOperator
  let K : E →L[ℂ] E := V.reflectionOperator
  let B : E →L[ℂ] E := J ∘L T0
  let C : E →L[ℂ] E := K ∘L S0
  let W : E →L[ℂ] E := K ∘L J
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hAH : IsSelfAdjoint (A + H) := hA.add hH
  have hAsym : A.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hAHsym : (A + H).toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAH
  have hUred : A.Reduces U := ContinuousLinearMap.IsSymmetric.reduces_of_invariant hAsym hAU
  have hVred : ContinuousLinearMap.Reduces (A + H) V :=
    ContinuousLinearMap.IsSymmetric.reduces_of_invariant hAHsym hAplusH_V
  have hJcommA : J ∘L A = A ∘L J := by
    simpa only [J] using Submodule.reflectionOperator_comm_of_reduces A U hUred
  have hKcommAH : K ∘L (A + H) = (A + H) ∘L K := by
    simpa only [K] using Submodule.reflectionOperator_comm_of_reduces (A + H) V hVred
  have hJstar : star J = J := by
    simpa only [J] using
      TauCeti.DavisKahan.star_reflectionOperator_complex U
  have hKstar : star K = K := by
    simpa only [K] using
      TauCeti.DavisKahan.star_reflectionOperator_complex V
  have hJ2 : J ∘L J = ContinuousLinearMap.id ℂ E := by
    simpa only [J] using Submodule.reflectionOperator_involutive U
  have hK2 : K ∘L K = ContinuousLinearMap.id ℂ E := by
    simpa only [K] using Submodule.reflectionOperator_involutive V
  have hT0star : IsSelfAdjoint T0 := by
    rw [isSelfAdjoint_iff]
    dsimp [T0, c]
    rw [star_sub, star_smul, hA.star_eq, star_id_clm]
    simp
  have hS0star : IsSelfAdjoint S0 := by
    rw [isSelfAdjoint_iff]
    dsimp [S0, c]
    rw [star_sub, star_smul, hAH.star_eq, star_id_clm]
    simp
  have hJcommT0 : J ∘L T0 = T0 ∘L J := by
    dsimp [T0]
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      hJcommA]
    ext x
    simp
  have hKcommS0 : K ∘L S0 = S0 ∘L K := by
    dsimp [S0]
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      hKcommAH]
    ext x
    simp
  have hBstar : IsSelfAdjoint B := by
    rw [isSelfAdjoint_iff]
    dsimp [B]
    change star (J * T0) = J * T0
    rw [star_mul, hT0star.star_eq, hJstar]
    change T0 ∘L J = J ∘L T0
    exact hJcommT0.symm
  have hCstar : IsSelfAdjoint C := by
    rw [isSelfAdjoint_iff]
    dsimp [C]
    change star (K * S0) = K * S0
    rw [star_mul, hS0star.star_eq, hKstar]
    change S0 ∘L K = K ∘L S0
    exact hKcommS0.symm
  have hBcoer : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_ℂ := by
    intro x
    simpa only [B, T0, J, c, δ, ContinuousLinearMap.comp_apply,
      sub_apply, smul_apply, ContinuousLinearMap.id_apply] using
      reflected_centered_form_lower A U hA hAU hUhigh hUperpLow x
  have hCcoer : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪C x, x⟫_ℂ := by
    intro x
    simpa only [C, S0, K, c, δ, ContinuousLinearMap.comp_apply,
      sub_apply, smul_apply, ContinuousLinearMap.id_apply] using
      reflected_centered_form_lower (A + H) V hAH hAplusH_V
        hVhigh hVperpLow x
  have hJH : J ∘L H = -(H ∘L J) := by
    simpa only [J] using reflection_anticommutes_of_maps_orthogonal H U hHU hHUperp
  have hWstar : star W = J ∘L K := by
    dsimp [W]
    change star (K * J) = J * K
    rw [star_mul, hJstar, hKstar]
  have hlyap : C ∘L W + star W ∘L C = B + B := by
    rw [hWstar]
    apply ContinuousLinearMap.ext
    intro x
    simp only [add_apply, ContinuousLinearMap.comp_apply]
    change K (S0 (K (J x))) + J (K (K (S0 x))) =
      J (T0 x) + J (T0 x)
    have hKcomm_apply (y : E) : K (S0 y) = S0 (K y) := by
      have h := DFunLike.congr_fun hKcommS0 y
      simpa only [ContinuousLinearMap.comp_apply] using h
    have hK2_apply (y : E) : K (K y) = y := by
      have h := DFunLike.congr_fun hK2 y
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h
    have hJT0_apply (y : E) : J (T0 y) = T0 (J y) := by
      have h := DFunLike.congr_fun hJcommT0 y
      simpa only [ContinuousLinearMap.comp_apply] using h
    have hJH_apply (y : E) : J (H y) = -H (J y) := by
      have h := DFunLike.congr_fun hJH y
      simpa only [ContinuousLinearMap.comp_apply, neg_apply] using h
    have hS0_apply (y : E) : S0 y = T0 y + H y := by
      dsimp [S0, T0]
      simp only [sub_apply, add_apply, smul_apply,
        ContinuousLinearMap.id_apply]
      module
    have hfirst : K (S0 (K (J x))) = S0 (J x) := by
      rw [hKcomm_apply, hK2_apply]
    have hsecond : J (K (K (S0 x))) = J (S0 x) := by
      rw [hK2_apply]
    rw [hfirst, hsecond, hS0_apply, hS0_apply,
      map_add, hJT0_apply, hJH_apply]
    abel
  obtain ⟨α, hα, hspecW⟩ := exists_spectrum_re_lower_of_lyapunov
    W B C hδ hBcoer hCstar hCcoer hlyap
  exact isQuarterAcute_of_reflection_spectrum_lower U V hα hspecW

/-! ### The non-strict quarter angle, and why it is stated separately

`isQuarterAcute_of_orderedFormGap` concludes `subspaceGap U V < √2/2`, strictly.
That is stronger than Davis and Kahan's printed `Θ ≤ π/4`, and the strictness is
paid for with the constant `α = δ / (1 + ‖C‖)`, which degenerates as `‖A‖ → ∞`.

The printed conclusion needs only the *non-strict* bound, and that follows from
the reflection product being positive with no constant at all.  Everything below
is the last third of the bounded proof with `α = 0`, extracted so that an
unbounded argument can reach the source conclusion without reproducing the part
that does not survive. -/

omit [CompleteSpace E] in
/-- **The reflection product's real part, in terms of the projector
difference.**  `K J + J K = 2 - 4 (P_U - P_V)²`. -/
theorem reflectionProduct_add_swap_eq
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    V.reflectionOperator * U.reflectionOperator
        + U.reflectionOperator * V.reflectionOperator =
      (2 : ℂ) • (1 : E →L[ℂ] E) -
        (4 : ℂ) • ((U.starProjection - V.starProjection) *
          (U.starProjection - V.starProjection)) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [add_apply, sub_apply, smul_apply, one_apply_eq_self,
    mul_apply_eq_comp]
  have hKJ :
      V.reflectionOperator (U.reflectionOperator x) =
        (4 : ℂ) • V.starProjection (U.starProjection x) -
          (2 : ℂ) • V.starProjection x -
          (2 : ℂ) • U.starProjection x + x := by
    rw [Submodule.reflectionOperator_apply V, Submodule.reflectionOperator_apply U]
    simp only [map_sub, map_smul]
    module
  have hJK :
      U.reflectionOperator (V.reflectionOperator x) =
        (4 : ℂ) • U.starProjection (V.starProjection x) -
          (2 : ℂ) • U.starProjection x -
          (2 : ℂ) • V.starProjection x + x := by
    rw [Submodule.reflectionOperator_apply U, Submodule.reflectionOperator_apply V]
    simp only [map_sub, map_smul]
    module
  have hPU : U.starProjection (U.starProjection x) = U.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  have hPV : V.starProjection (V.starProjection x) = V.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
  have hDDx :
      U.starProjection (U.starProjection x - V.starProjection x) -
          V.starProjection (U.starProjection x - V.starProjection x) =
        U.starProjection x - U.starProjection (V.starProjection x) -
          V.starProjection (U.starProjection x) + V.starProjection x := by
    simp only [map_sub, hPU, hPV]
    abel
  rw [hKJ, hJK, hDDx]
  module

/-- **`Θ ≤ π/4` from a positive reflection product.**

Davis--Kahan's printed Section 8 conclusion, in projector form: if the real part
of `K J` is nonnegative -- equivalently `K J + J K ≥ 0` -- then
`‖P_U − P_V‖ ≤ √2/2`.

No constant appears anywhere, which is exactly why this survives to unbounded
scope where `isQuarterAcute_of_orderedFormGap`'s strict bound does not. -/
theorem subspaceGap_le_of_reflectionProduct_form_nonneg
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : ∀ x : E, 0 ≤ RCLike.re ⟪(V.reflectionOperator * U.reflectionOperator
      + U.reflectionOperator * V.reflectionOperator) x, x⟫_ℂ) :
    U.projectionGap V ≤ Real.sqrt 2 / 2 := by
  obtain ⟨D, hDdef⟩ : ∃ D : E →L[ℂ] E, D = U.starProjection - V.starProjection := ⟨_, rfl⟩
  have hDstar : IsSelfAdjoint D := by
    rw [hDdef]
    exact (isSelfAdjoint_starProjection U).sub (isSelfAdjoint_starProjection V)
  have hpoint : ∀ x : E, ‖D x‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
    intro x
    have hx := h x
    rw [reflectionProduct_add_swap_eq U V, ← hDdef] at hx
    have hval : ((2 : ℂ) • (1 : E →L[ℂ] E) - (4 : ℂ) • (D * D)) x
        = (2 : ℂ) • x - (4 : ℂ) • D (D x) := by
      simp only [sub_apply, smul_apply, one_apply_eq_self, mul_apply_eq_comp]
    rw [hval, inner_sub_left, map_sub, inner_smul_left, inner_smul_left] at hx
    have hDsq : RCLike.re ⟪D (D x), x⟫_ℂ = ‖D x‖ ^ 2 := by
      calc RCLike.re ⟪D (D x), x⟫_ℂ = RCLike.re ⟪(star D) (D x), x⟫_ℂ := by
            rw [hDstar.star_eq]
        _ = RCLike.re ⟪D x, D x⟫_ℂ := by
            rw [ContinuousLinearMap.star_eq_adjoint,
              ContinuousLinearMap.adjoint_inner_left]
        _ = ‖D x‖ ^ 2 := by rw [inner_self_eq_norm_sq]
    have htwo : RCLike.re ((starRingEnd ℂ) (2 : ℂ) * ⟪x, x⟫_ℂ) = 2 * ‖x‖ ^ 2 := by
      simpa using re_conj_real_mul_inner_self (E := E) 2 x
    have hfour : RCLike.re ((starRingEnd ℂ) (4 : ℂ) * ⟪D (D x), x⟫_ℂ) =
        4 * RCLike.re ⟪D (D x), x⟫_ℂ := re_conj_real_mul 4 ⟪D (D x), x⟫_ℂ
    rw [htwo, hfour, hDsq] at hx
    linarith
  have hDnorm : ‖D‖ ≤ Real.sqrt (1 / 2 : ℝ) :=
    opNorm_le_sqrt_of_sq_apply_le D (by norm_num) hpoint
  have hsqrt : Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
    rw [show (1 / 2 : ℝ) = 2 / 2 ^ 2 by norm_num, Real.sqrt_div' 2 (by norm_num),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  change ‖U.starProjection - V.starProjection‖ ≤ Real.sqrt 2 / 2
  rw [← hDdef, ← hsqrt]
  exact hDnorm

/-- **The pointwise strict form.**  Where the reflection product's real part is
strictly positive on a vector, the projector difference is strictly below the
`√2/2` threshold *at that vector*.

This is the same computation as `hpoint` inside
`subspaceGap_le_of_reflectionProduct_form_nonneg`, kept strict.  A supremum
bound does not follow -- the strictness is pointwise and need not be uniform --
which is exactly the distinction Section 8 turns on at unbounded scope. -/
theorem norm_starProjection_sub_sq_lt_of_reflectionProduct_form_pos
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] {x : E}
    (h : 0 < RCLike.re ⟪(V.reflectionOperator * U.reflectionOperator
      + U.reflectionOperator * V.reflectionOperator) x, x⟫_ℂ) :
    ‖U.starProjection x - V.starProjection x‖ ^ 2 < (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
  obtain ⟨D, hDdef⟩ : ∃ D : E →L[ℂ] E, D = U.starProjection - V.starProjection := ⟨_, rfl⟩
  have hDstar : IsSelfAdjoint D := by
    rw [hDdef]
    exact (isSelfAdjoint_starProjection U).sub (isSelfAdjoint_starProjection V)
  have hDx : D x = U.starProjection x - V.starProjection x := by rw [hDdef]; rfl
  have hx := h
  rw [reflectionProduct_add_swap_eq U V, ← hDdef] at hx
  have hval : ((2 : ℂ) • (1 : E →L[ℂ] E) - (4 : ℂ) • (D * D)) x
      = (2 : ℂ) • x - (4 : ℂ) • D (D x) := by
    simp only [sub_apply, smul_apply, one_apply_eq_self, mul_apply_eq_comp]
  rw [hval, inner_sub_left, map_sub, inner_smul_left, inner_smul_left] at hx
  have hDsq : RCLike.re ⟪D (D x), x⟫_ℂ = ‖D x‖ ^ 2 := by
    calc RCLike.re ⟪D (D x), x⟫_ℂ = RCLike.re ⟪(star D) (D x), x⟫_ℂ := by
          rw [hDstar.star_eq]
      _ = RCLike.re ⟪D x, D x⟫_ℂ := by
          rw [ContinuousLinearMap.star_eq_adjoint,
            ContinuousLinearMap.adjoint_inner_left]
      _ = ‖D x‖ ^ 2 := by rw [inner_self_eq_norm_sq]
  have htwo : RCLike.re ((starRingEnd ℂ) (2 : ℂ) * ⟪x, x⟫_ℂ) = 2 * ‖x‖ ^ 2 := by
    simpa using re_conj_real_mul_inner_self (E := E) 2 x
  have hfour : RCLike.re ((starRingEnd ℂ) (4 : ℂ) * ⟪D (D x), x⟫_ℂ) =
      4 * RCLike.re ⟪D (D x), x⟫_ℂ := re_conj_real_mul 4 ⟪D (D x), x⟫_ℂ
  rw [htwo, hfour, hDsq] at hx
  rw [← hDx]
  linarith

/-- **`Θ ≤ π/4` in the printed angle form.** -/
theorem maximalAngle_le_pi_div_four_of_reflectionProduct_form_nonneg
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : ∀ x : E, 0 ≤ RCLike.re ⟪(V.reflectionOperator * U.reflectionOperator
      + U.reflectionOperator * V.reflectionOperator) x, x⟫_ℂ) :
    TauCeti.DavisKahanExt.maximalAngle U V ≤ Real.pi / 4 := by
  have hle := subspaceGap_le_of_reflectionProduct_form_nonneg U V h
  have hpi : Real.arcsin (Real.sqrt 2 / 2) = Real.pi / 4 := by
    rw [← Real.sin_pi_div_four]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  calc TauCeti.DavisKahanExt.maximalAngle U V
      = Real.arcsin (U.projectionGap V) := rfl
    _ ≤ Real.arcsin (Real.sqrt 2 / 2) := Real.arcsin_le_arcsin hle
    _ = Real.pi / 4 := hpi

end

end DavisKahan
end TauCeti
