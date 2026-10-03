/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebraDefs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebraContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Matrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.OddSupportTsum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnsatzGradient

/-! # Exact decomposition of `∇θTilde_m - F ∇T_{m-1}` (`e.grad.tildetheta.again`, 8112–8143)

Source: `enhance.tex` 8112–8170.  At a fixed time `t` and position `x`, for `T` with smooth slice
`T t` and `HTilde_m(t)` differentiable at `x`,
`∇θTilde_m - F ∇T_{m-1} = ∑_{k odd} ξ_{m,k} (E¹_k + E²_k + E³_k) + ∇HTilde_m`,
where `E¹, E², E³` are `leadingErrFlowInv`, `leadingErrFlowFwd`, `leadingErrHessian`
(`LeadingErrorAlgebraDefs`), the finite sum running over the odd support of `ξ_{m,·}(t)`.
The joint continuity of each field on `Ici 0 ×ˢ univ` is in `LeadingErrorAlgebraContinuity`
(imported here, so this module is the single entry point).

The identity part of `F` is handled by the partition of unity `∑_{k odd} ξ_{m,k} = 1`
(`leadingMatrix_eq_finset`). -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Matrix identity behind the second and third terms. -/
theorem mulVec_split_flow (A C Fl : Matrix (Fin 2) (Fin 2) ℝ) (g : Vec 2) :
    (A * C).mulVec (Fl.mulVec g) - C.mulVec g =
      ((A - 1) * C).mulVec g + (A * C * (Fl - 1)).mulVec g := by
  rw [Matrix.mulVec_mulVec, sub_mul, one_mul, mul_sub, mul_one, Matrix.sub_mulVec,
    Matrix.sub_mulVec]
  abel

/-- The `k`-th pairing `ΧTilde_{m,k} · G_{l_k}` of the ansatz. -/
def ansatzPairing (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ)
    (y : Vec 2) : ℝ :=
  vecDot (I.chiTilde hΦ m κm k t y) (G I hΦ m T (lIdx β I.Λ m k) t y)

theorem contDiff_ansatzPairing (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (k : ℤ) {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) :
    ContDiff ℝ ∞ (ansatzPairing I hΦ m κm T k t) := by
  have hχ := contDiff_chiTilde I hΦ m κm k t
  have hG := contDiff_G I hΦ m T (lIdx β I.Λ m k) hTt
  unfold ansatzPairing vecDot
  exact ContDiff.sum fun j _ =>
    ((contDiff_apply ℝ ℝ j).comp hχ).mul ((contDiff_apply ℝ ℝ j).comp hG)

/-- Gradient of the `k`-th pairing: the `(∇ΧTilde) G` part and the Hessian part. -/
theorem spaceGrad_ansatzPairing (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (k : ℤ) {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) (x : Vec 2) (i : Fin 2) :
    spaceGrad (ansatzPairing I hΦ m κm T k t) x i =
      ((gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) x *
          gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).mulVec
          ((I.flowGrad hΦ m (lIdx β I.Λ m k) t x).mulVec (spaceGrad (T t) x))) i +
        leadingErrHessian I hΦ m κm T k t x i := by
  have hχ := ((contDiff_chiTilde I hΦ m κm k t).differentiable (by simp) x).hasFDerivAt
  have hG := (((contDiff_G I hΦ m T (lIdx β I.Λ m k) hTt).differentiable (by simp)) x).hasFDerivAt
  have h := spaceGrad_vecDot hχ hG i
  have hT := (hTt.differentiable (by simp) x).hasFDerivAt
  have hX := (((contDiff_xFlow_slice I hΦ m (lIdx β I.Λ m k) t).differentiable (by simp))
    (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).hasFDerivAt
  have hGx := G_eq_flowGrad_mulVec I hΦ m T (lIdx β I.Λ m k) t x hT hX
    (xFlow_xFlowInv I hΦ m _ t x)
  unfold ansatzPairing
  rw [h, gradMatrix_chiTilde_eq, hGx]
  congr 1
  unfold leadingErrHessian
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [spaceGrad_G_component I hΦ m T _ hTt x i j]
  rfl

/-- The ansatz as a finite sum over the odd support of `ξ_{m,·}(t)`. -/
theorem ansatz_eq_finset_sum (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) :
    I.ansatz hΦ m κm T t = fun y =>
      T t y + (∑ q ∈ (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t * ansatzPairing I hΦ m κm T q.1 t y) + I.Hm hΦ m κm T t y := by
  classical
  funext y
  rw [Integration.ansatz_eq_summand]
  congr 2
  have hzero : ∀ k ∉ (I.xiMK_support_finite m t).toFinset,
      Integration.ansatzSummand I hΦ m κm T k t y = 0 := fun k hk =>
    Integration.ansatzSummand_eq_zero I hΦ m κm T
      (by by_contra hne; exact hk ((I.xiMK_support_finite m t).mem_toFinset.mpr hne)) y
  rw [tsum_eq_sum hzero]
  have hodd : ∀ k ∈ (I.xiMK_support_finite m t).toFinset,
      Integration.ansatzSummand I hΦ m κm T k t y ≠ 0 → Odd k := by
    intro k _ hne
    by_contra hk
    apply hne
    simp [Integration.ansatzSummand, Ingredients.chiTilde, chiMK_eq_zero_of_not_odd I κm m hk t,
      vecDot]
  rw [← Finset.sum_filter_of_ne hodd]
  have h := xiMK_odd_integer_support_sum_eq_subtype_sum I m hm t
    (fun k => ansatzPairing I hΦ m κm T k t y)
  simp only [smul_eq_mul] at h
  exact h

/-- **Exact decomposition of `∇θTilde_m - F ∇T_{m-1}`** (`e.grad.tildetheta.again`). -/
theorem ansatz_spaceGrad_sub_leadingGrad (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) (x : Vec 2)
    (hHt : DifferentiableAt ℝ (I.Hm hΦ m κm T t) x) :
    spaceGrad (I.ansatz hΦ m κm T t) x - LeftToShow.leadingGrad I hΦ m κm T t x =
      ∑ k ∈ (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m k.1 t • (leadingErrFlowInv I hΦ m κm T k.1 t x +
          leadingErrFlowFwd I hΦ m κm T k.1 t x + leadingErrHessian I hΦ m κm T k.1 t x) +
      spaceGrad (I.Hm hΦ m κm T t) x := by
  classical
  set U := (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset with hU
  funext i
  have hT := (hTt.differentiable (by simp) x).hasFDerivAt
  have hH := hHt.hasFDerivAt
  have hP (q : {k : ℤ // Odd k}) : HasFDerivAt (ansatzPairing I hΦ m κm T q.1 t)
      (fderiv ℝ (ansatzPairing I hΦ m κm T q.1 t) x) x :=
    ((contDiff_ansatzPairing I hΦ m κm T q.1 hTt).differentiable (by simp) x).hasFDerivAt
  have hsum := spaceGrad_finiteWeightedSum U (T t) (I.Hm hΦ m κm T t)
    (fun q => I.xiMK m q.1 t) (fun q => ansatzPairing I hΦ m κm T q.1 t) x
    (fun q => fderiv ℝ (ansatzPairing I hΦ m κm T q.1 t) x) hT hH (fun q _ => hP q) i
  rw [ansatz_eq_finset_sum I hΦ hm κm T t, Pi.sub_apply, hsum]
  unfold LeftToShow.leadingGrad
  rw [LeftToShow.leadingMatrix_eq_finset I hΦ hm κm t x, Matrix.add_mulVec, Matrix.sum_mulVec]
  simp only [Matrix.one_mulVec, Matrix.smul_mulVec, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ q ∈ U, I.xiMK m q.1 t * spaceGrad (ansatzPairing I hΦ m κm T q.1 t) x i -
      I.xiMK m q.1 t * (gradMatrix (I.chiMK κm m q.1 t)
        (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x)).mulVec (spaceGrad (T t) x) i =
      I.xiMK m q.1 t * (leadingErrFlowInv I hΦ m κm T q.1 t x i +
        leadingErrFlowFwd I hΦ m κm T q.1 t x i + leadingErrHessian I hΦ m κm T q.1 t x i) := by
    intro q _
    rw [← mul_sub, spaceGrad_ansatzPairing I hΦ m κm T q.1 hTt x i]
    congr 1
    have := congrFun (mulVec_split_flow
      (gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t z) x)
      (gradMatrix (I.chiMK κm m q.1 t) (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x))
      (I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x) (spaceGrad (T t) x)) i
    simp only [Pi.sub_apply, Pi.add_apply] at this
    unfold leadingErrFlowInv leadingErrFlowFwd
    linarith
  have hsub := Finset.sum_congr rfl hterm
  rw [Finset.sum_sub_distrib] at hsub
  linarith

end AVenhance.Infra.Section5.RelativeError
