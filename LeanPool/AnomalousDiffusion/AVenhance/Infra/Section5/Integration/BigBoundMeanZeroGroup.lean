/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBoundRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.OddSupportTsum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.Regroup
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.PiolaColumn

/-! The grouped corrector error mean is the mean of an explicit periodic
finite-mode divergence.

LeftJacobian the left-Jacobian form: the slots `twistie4`, `twistie5`, `normie3` differ from the
    pre-LeftJacobian bodies
`twistie4ND`, `twistie5ND`, `normie3Old = Σ_k ξ_k (𝒥 - C_k) : ∇G_k` by
`Σ_k ξ_k (F_kᵀ - 1) P : ∇G_k`, `P = 𝒥 - κ I` (`LeftJacobian.twistie4Plus_eq`,
    `LeftJacobian.normie3_matrix_split`),
and `(F_kᵀ - 1) P` has zero column divergence (`LeftJacobian.piola_column_hasFDerivAt`), so this
    extra term
is again a divergence of a smooth periodic field. -/

@[expose] public section

noncomputable section

open Homogenization MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

theorem BigBoundMeanZeroGroup.meanZeroGroup_xFlowInv_right_inverse {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2) :
    I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x) = x := by
  let b := streamVel (Φ (m - 1))
  let F := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  let hF : IsFlow b F := flow_isFlow b
    (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  change F t (F s x t) s = x
  calc
    F t (F s x t) s = F t x t :=
      Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hF x t s t
    _ = x := hF.1 x t

theorem BigBoundMeanZeroGroup.meanZeroGroup_vecDot_matrixMulVec_transpose
    (A : Matrix (Fin 2) (Fin 2) ℝ) (u v : Vec 2) :
    vecDot u (A.mulVec v) = vecDot (A.transpose.mulVec u) v := by
  simp [vecDot, Matrix.mulVec, dotProduct, Matrix.transpose, Fin.sum_univ_two]
  ring

theorem BigBoundMeanZeroGroup.meanZeroGroup_vecDot_comm (u v : Vec 2) :
    vecDot u v = vecDot v u := by
  simp [vecDot, Fin.sum_univ_two, mul_comm]

theorem BigBoundMeanZeroGroup.meanZeroGroup_timeDerivative_pairing_pushforward {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ) (x : Vec 2)
    (hT : ContDiff ℝ 1 (T t)) :
    vecDot (chiMKTimeDerivative I m κ k t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
        (G I hΦ m T (lIdx β I.Λ m k) t x) =
      vecDot (chiTimePushforwardFlux I hΦ m κ k t x)
        (spaceGrad (T t) x) := by
  have hG := G_eq_flowGrad_mulVec I hΦ m T (lIdx β I.Λ m k) t x
    ((hT.differentiable (by norm_num) x).hasFDerivAt)
    ((xFlow_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k) t).differentiable
      (by norm_num) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).hasFDerivAt
    (BigBoundMeanZeroGroup.meanZeroGroup_xFlowInv_right_inverse I hΦ m (lIdx β I.Λ m k) t x)
  calc
    _ = vecDot (chiMKTimeDerivative I m κ k t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
        ((I.flowGrad hΦ m (lIdx β I.Λ m k) t x).mulVec (spaceGrad (T t) x)) := by
          rw [hG]
    _ = vecDot ((I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose.mulVec
        (chiMKTimeDerivative I m κ k t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))) (spaceGrad (T t) x) :=
      BigBoundMeanZeroGroup.meanZeroGroup_vecDot_matrixMulVec_transpose _ _ _
    _ = _ := rfl

theorem BigBoundMeanZeroGroup.matrixMulVec_contDiff_infty
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : Vec 2 → Vec 2}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (A x).mulVec (V x)) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ j : Fin 2, A x i j * V x j)
  apply ContDiff.sum
  intro j hj
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul (contDiff_pi.mp hV j)

/-- The pre-LeftJacobian body of `normie3`: `Σ_k ξ_k (𝒥 - C_k) : ∇G_k` with the pulled corrector
    flux `C_k`. -/
def BigBoundMeanZeroGroup.meanZeroGroupNormie3Old {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2
    → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k},
    I.xiMK m k.1 t * frob (I.flux κm m t - correctorFlux I hΦ m κm k.1 t x)
      (gradG I hΦ m T (lIdx β I.Λ m k.1) t x)

private theorem group_meanZero_of_slice_groupOld1 :
  ∀ {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm
    : (1 : ℕ) ≤ m) (κ : ℝ) (T : ℝ → Vec (2 : ℕ) → ℝ) {t : ℝ}, ContDiff ℝ ∞ (T t) →
  let U : Finset { k : ℤ // Odd k } := (Section3.xiMK_odd_support_finite I hm t).toFinset;
  let J : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ := I.flux κ m t;
  let F0 : { k : ℤ // Odd k } → Vec (2 : ℕ) → Vec (2 : ℕ) := fun (k : { k : ℤ // Odd k }) (x :
    Vec (2 : ℕ)) => (J - correctorFlux I hΦ m κ (↑k : ℤ) t x).mulVec (G I hΦ m T (lIdx β I.Λ m
    (↑k : ℤ)) t x) + T t x • chiTimePushforwardFlux I hΦ m κ (↑k : ℤ) t x;
  (∀ k ∈ U, I.xiMK m (↑k : ℤ) t ≠ (0 : ℝ)) → (twistie4ND I hΦ m κ T t = fun (x : Vec (2 : ℕ)) =>
    -∑ k ∈ U, I.xiMK m (↑k : ℤ) t * vecDot (G I hΦ m T (lIdx β I.Λ m (↑k : ℤ)) t x) (matDiv
    (correctorDefectMatrix I hΦ m (↑k : ℤ) t κ) x)) → (twistie5ND I hΦ m κ T t = fun (x : Vec (2
    : ℕ)) => -∑ k ∈ U, I.xiMK m (↑k : ℤ) t * vecDot (G I hΦ m T (lIdx β I.Λ m (↑k : ℤ)) t x)
    (matDiv (correctorPushforwardMatrix I hΦ m (↑k : ℤ) t κ) x)) →
    (BigBoundMeanZeroGroup.meanZeroGroupNormie3Old I hΦ m κ T t = fun (x : Vec (2 : ℕ)) => ∑ k
    ∈ U, I.xiMK m (↑k : ℤ) t * frob (J - correctorFlux I hΦ m κ (↑k : ℤ) t x) (gradG I hΦ m T
    (lIdx β I.Λ m (↑k : ℤ)) t x)) → (∀ k ∈ U, ContDiff ℝ ∞ (correctorFlux I hΦ m κ (↑k : ℤ) t))
    → (∀ (k : { k : ℤ // Odd k }), ContDiff ℝ ∞ (G I hΦ m T (lIdx β I.Λ m (↑k : ℤ)) t)) → (∀ (k
    : { k : ℤ // Odd k }), ContDiff ℝ ∞ (chiTimePushforwardFlux I hΦ m κ (↑k : ℤ) t)) → ∀ (x :
    Vec (2 : ℕ)), twistie4ND I hΦ m κ T t x + twistie5ND I hΦ m κ T t x +
    BigBoundMeanZeroGroup.meanZeroGroupNormie3Old I hΦ m κ T t x = ∑ k ∈ U, I.xiMK m (↑k : ℤ) t
    * vecDiv (F0 k) x
    := by
  intro β I Φ hΦ m hm κ T t hTsm U J F0 hxi h4rep h5rep h3rep hCsm hGsm hPsm x
  rw [h4rep, h5rep, h3rep]
  change -(∑ k ∈ U, I.xiMK m k.1 t *
      vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
        (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x)) -
    (∑ k ∈ U, I.xiMK m k.1 t *
      vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
        (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x)) +
    (∑ k ∈ U, I.xiMK m k.1 t *
      frob (J - correctorFlux I hΦ m κ k.1 t x)
        (gradG I hΦ m T (lIdx β I.Λ m k.1) t x)) = _
  have hsum :
      -(∑ k ∈ U, I.xiMK m k.1 t *
        vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
          (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x)) -
      (∑ k ∈ U, I.xiMK m k.1 t *
        vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
          (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x)) +
      (∑ k ∈ U, I.xiMK m k.1 t *
        frob (J - correctorFlux I hΦ m κ k.1 t x)
          (gradG I hΦ m T (lIdx β I.Λ m k.1) t x)) =
      ∑ k ∈ U, I.xiMK m k.1 t *
        (-vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
            (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x) -
          vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
            (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x) +
          frob (J - correctorFlux I hΦ m κ k.1 t x)
            (gradG I hΦ m T (lIdx β I.Λ m k.1) t x)) := by
    let f : {k : ℤ // Odd k} → ℝ := fun k => I.xiMK m k.1 t *
      vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
        (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x)
    let g : {k : ℤ // Odd k} → ℝ := fun k => I.xiMK m k.1 t *
      vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
        (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x)
    let h : {k : ℤ // Odd k} → ℝ := fun k => I.xiMK m k.1 t *
      frob (J - correctorFlux I hΦ m κ k.1 t x)
        (gradG I hΦ m T (lIdx β I.Λ m k.1) t x)
    change -(∑ k ∈ U, f k) - (∑ k ∈ U, g k) + (∑ k ∈ U, h k) = _
    have hf : -(∑ k ∈ U, f k) = ∑ k ∈ U, -f k := by simp
    have hg : -(∑ k ∈ U, g k) = ∑ k ∈ U, -g k := by simp
    rw [hf]
    change (∑ k ∈ U, -f k) + -(∑ k ∈ U, g k) +
      (∑ k ∈ U, h k) = _
    rw [hg]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [f, g, h]
    ring
  rw [hsum]
  apply Finset.sum_congr rfl
  intro k hk
  have hC := hCsm k hk
  have hG := hGsm k
  have hP := hPsm k
  have hCder (i j : Fin 2) : HasFDerivAt
      (fun y => correctorFlux I hΦ m κ k.1 t y i j)
      (fderiv ℝ (fun y => correctorFlux I hΦ m κ k.1 t y i j) x) x :=
    ((contDiff_pi.mp (contDiff_pi.mp hC i) j).differentiable
      (by simp) x).hasFDerivAt
  have hGder : HasFDerivAt (G I hΦ m T (lIdx β I.Λ m k.1) t)
      (fderiv ℝ (G I hΦ m T (lIdx β I.Λ m k.1) t) x) x :=
    (hG.differentiable (by simp) x).hasFDerivAt
  let A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun y =>
    J - correctorFlux I hΦ m κ k.1 t y
  have hAder (i j : Fin 2) : HasFDerivAt (fun y => A y i j)
      (0 - fderiv ℝ (fun y => correctorFlux I hΦ m κ k.1 t y i j) x) x := by
    dsimp [A]
    exact (hasFDerivAt_const (J i j) x).sub (hCder i j)
  have hmatA : matDiv A x = -matDiv (correctorFlux I hΦ m κ k.1 t) x := by
    ext j
    simp only [matDiv, Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [spaceGrad, (hAder i j).fderiv, spaceGrad, (hCder i j).fderiv]
    simp
  have hprodA := vecDiv_matrixMulVec_frob hAder hGder
  rw [hmatA] at hprodA
  have hCG := vecDiv_matrixMulVec_frob hCder hGder
  have hgradG : gradG I hΦ m T (lIdx β I.Λ m k.1) t x =
      gradMatrix (G I hΦ m T (lIdx β I.Λ m k.1) t) x := rfl
  rw [← hgradG] at hprodA
  have hexp := correctorFlux_mulVec_G_divergence_expansion I hΦ m hm κ T k.1 t x
    k.2 (hxi k hk) hCder hGder
  have hdivC : vecDot (matDiv (correctorFlux I hΦ m κ k.1 t) x)
      (G I hΦ m T (lIdx β I.Λ m k.1) t x) =
      vecDot (fun j => deriv (fun s => I.chiMK κ m k.1 s
        (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x) j) t)
        (G I hΦ m T (lIdx β I.Λ m k.1) t x) +
      vecDot (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x)
        (G I hΦ m T (lIdx β I.Λ m k.1) t x) +
      vecDot (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x)
        (G I hΦ m T (lIdx β I.Λ m k.1) t x) := by
    rw [hCG] at hexp
    linarith [hexp]
  have hpair := BigBoundMeanZeroGroup.meanZeroGroup_timeDerivative_pairing_pushforward I hΦ m κ
      T k.1 t x
    (hTsm.of_le (by norm_num))
  have hPdiv (y : Vec 2) :
      vecDiv (chiTimePushforwardFlux I hΦ m κ k.1 t) y = 0 :=
    (chiTimePushforwardFlux_regular I hΦ hm κ k.1 t).2.2 y
  have hTdiv := vecDiv_scalar_mul (x := x) hTsm hP
  rw [hPdiv x, mul_zero, add_zero] at hTdiv
  have hTpair : vecDiv (fun y => (T t y) •
      chiTimePushforwardFlux I hΦ m κ k.1 t y) x =
      vecDot (chiMKTimeDerivative I m κ k.1 t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x))
        (G I hΦ m T (lIdx β I.Λ m k.1) t x) := by
    rw [hTdiv, BigBoundMeanZeroGroup.meanZeroGroup_vecDot_comm, hpair]
  have hsumDiv : vecDiv (fun y => (A y).mulVec
      (G I hΦ m T (lIdx β I.Λ m k.1) t y) + (T t y) •
        chiTimePushforwardFlux I hΦ m κ k.1 t y) x =
      vecDiv (fun y => (A y).mulVec
        (G I hΦ m T (lIdx β I.Λ m k.1) t y)) x +
      vecDiv (fun y => (T t y) • chiTimePushforwardFlux I hΦ m κ k.1 t y) x := by
    have hAmul : ContDiff ℝ (⊤ : ℕ∞) (fun y => (A y).mulVec
        (G I hΦ m T (lIdx β I.Λ m k.1) t y)) :=
      BigBoundMeanZeroGroup.matrixMulVec_contDiff_infty
        ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => J)).sub hC) hG
    have hAprod : HasFDerivAt (fun y => A y |>.mulVec
        (G I hΦ m T (lIdx β I.Λ m k.1) t y))
        (fderiv ℝ (fun y => A y |>.mulVec
          (G I hΦ m T (lIdx β I.Λ m k.1) t y)) x) x :=
      (hAmul.differentiable (by norm_num) x).hasFDerivAt
    have hTp : HasFDerivAt (fun y => (T t y) •
        chiTimePushforwardFlux I hΦ m κ k.1 t y)
        (fderiv ℝ (fun y => (T t y) •
          chiTimePushforwardFlux I hΦ m κ k.1 t y) x) x :=
      ((hTsm.smul hP).differentiable (by simp) x).hasFDerivAt
    exact vecDiv_add_of_hasFDerivAt hAprod hTp
  have hcore :
      -vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
          (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x) -
        vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
          (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x) +
        frob (J - correctorFlux I hΦ m κ k.1 t x)
          (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) =
        vecDiv (F0 k) x := by
    dsimp [F0, A] at hsumDiv ⊢
    rw [hsumDiv, hprodA, hTpair]
    have hnegdot : vecDot (-matDiv (correctorFlux I hΦ m κ k.1 t) x)
        (G I hΦ m T (lIdx β I.Λ m k.1) t x) =
        -vecDot (matDiv (correctorFlux I hΦ m κ k.1 t) x)
          (G I hΦ m T (lIdx β I.Λ m k.1) t x) := by
      simp [vecDot, Finset.sum_neg_distrib]
    rw [hnegdot]
    have hDcomm := BigBoundMeanZeroGroup.meanZeroGroup_vecDot_comm
      (G I hΦ m T (lIdx β I.Λ m k.1) t x)
      (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x)
    have hEcomm := BigBoundMeanZeroGroup.meanZeroGroup_vecDot_comm
      (G I hΦ m T (lIdx β I.Λ m k.1) t x)
      (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x)
    rw [hDcomm, hEcomm]
    have htimeEq : vecDot (fun j => deriv (fun s => I.chiMK κ m k.1 s
        (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x) j) t)
        (G I hΦ m T (lIdx β I.Λ m k.1) t x) =
        vecDot (chiMKTimeDerivative I m κ k.1 t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x))
          (G I hΦ m T (lIdx β I.Λ m k.1) t x) := rfl
    rw [htimeEq] at hdivC
    dsimp [A]
    linarith [hdivC]
  calc
    _ = I.xiMK m k.1 t *
        (-vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
            (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x) -
          vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
            (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x) +
          frob (J - correctorFlux I hΦ m κ k.1 t x)
            (gradG I hΦ m T (lIdx β I.Λ m k.1) t x)) := by ring
    _ = I.xiMK m k.1 t * vecDiv (F0 k) x := by rw [hcore]

private theorem group_meanZero_of_slice_newPoint2 :
  ∀ {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm
    : (1 : ℕ) ≤ m) (κ : ℝ) (T : ℝ → Vec (2 : ℕ) → ℝ) {t : ℝ}, ContDiff ℝ ∞ (T t) →
  let U : Finset { k : ℤ // Odd k } := (Section3.xiMK_odd_support_finite I hm t).toFinset;
  let J : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ := I.flux κ m t;
  let P : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ := J - κ • (1 : Matrix (Fin (2 : ℕ)) (Fin (2 :
    ℕ)) ℝ);
  let R : { k : ℤ // Odd k } → Vec (2 : ℕ) → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ := fun (k : {
    k : ℤ // Odd k }) (y : Vec (2 : ℕ)) => (flowGradK I hΦ m (↑k : ℤ) t y).transpose * P - P;
  ∀ (x : Vec (2 : ℕ)), twistie4 I hΦ m κ T t x + twistie5 I hΦ m κ T t x + normie3 I hΦ m κ T t
    x = twistie4ND I hΦ m κ T t x + twistie5ND I hΦ m κ T t x +
    BigBoundMeanZeroGroup.meanZeroGroupNormie3Old I hΦ m κ T t x + ∑ k ∈ U, I.xiMK m (↑k : ℤ) t
    * frob (R k x) (gradG I hΦ m T (lIdx β I.Λ m (↑k : ℤ)) t x)
    := by
  intro β I Φ hΦ m hm κ T t hTsm U J P R x
  have h4 : twistie4 I hΦ m κ T t x = twistie4ND I hΦ m κ T t x -
      ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t *
        frob (correctorDefectMatrix I hΦ m k.1 t κ x)
          (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) :=
    LeftJacobian.twistie4Plus_eq I hΦ m hm κ T t x hTsm
  have h5 : twistie5 I hΦ m κ T t x = twistie5ND I hΦ m κ T t x -
      ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t *
        frob (correctorPushforwardMatrix I hΦ m k.1 t κ x)
          (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) :=
    LeftJacobian.twistie5Plus_eq I hΦ m hm κ T t x hTsm
  rw [LeftJacobian.tsum_xi_mul_eq_sum I m hm t] at h4 h5
  have hmat (k : {k : ℤ // Odd k}) :
      (flowGradK I hΦ m k.1 t x).transpose * (J - cellFlux I hΦ m κ k.1 t x) =
        (J - correctorFlux I hΦ m κ k.1 t x) + R k x +
          correctorDefectMatrix I hΦ m k.1 t κ x +
          correctorPushforwardMatrix I hΦ m k.1 t κ x := by
    have h := LeftJacobian.normie3_matrix_split I hΦ m κ k.1 t x
    have hB : (flowGradK I hΦ m k.1 t x).transpose * (I.flux κ m t - cellFlux I hΦ m κ k.1 t x) =
        (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (flowGradK I hΦ m k.1 t x).transpose *
            (I.flux κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) -
          correctorFlux I hΦ m κ k.1 t x) +
        correctorDefectMatrix I hΦ m k.1 t κ x +
        correctorPushforwardMatrix I hΦ m k.1 t κ x := by
      rw [h]
      abel
    rw [hB]
    simp only [R, P, J]
    abel
  have h3 : normie3 I hΦ m κ T t x =
      BigBoundMeanZeroGroup.meanZeroGroupNormie3Old I hΦ m κ T t x +
        ∑ k ∈ U, I.xiMK m k.1 t * (frob (R k x) (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) +
          frob (correctorDefectMatrix I hΦ m k.1 t κ x)
            (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) +
          frob (correctorPushforwardMatrix I hΦ m k.1 t κ x)
            (gradG I hΦ m T (lIdx β I.Λ m k.1) t x)) := by
    unfold normie3 BigBoundMeanZeroGroup.meanZeroGroupNormie3Old
    rw [LeftJacobian.tsum_xi_mul_eq_sum I m hm t, LeftJacobian.tsum_xi_mul_eq_sum I m hm t,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hmat k, LeftJacobian.frob_add_left, LeftJacobian.frob_add_left,
        LeftJacobian.frob_add_left]
    ring
  rw [h3, h4, h5]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

private theorem group_meanZero_of_slice_perk3 :
  ∀ {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm
    : (1 : ℕ) ≤ m) (κ : ℝ) (T : ℝ → Vec (2 : ℕ) → ℝ) {t : ℝ},
  let U : Finset { k : ℤ // Odd k } := (Section3.xiMK_odd_support_finite I hm t).toFinset;
  let J : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ := I.flux κ m t;
  let F0 : { k : ℤ // Odd k } → Vec (2 : ℕ) → Vec (2 : ℕ) := fun (k : { k : ℤ // Odd k }) (x :
    Vec (2 : ℕ)) => (J - correctorFlux I hΦ m κ (↑k : ℤ) t x).mulVec (G I hΦ m T (lIdx β I.Λ m
    (↑k : ℤ)) t x) + T t x • chiTimePushforwardFlux I hΦ m κ (↑k : ℤ) t x;
  (∀ (k : { k : ℤ // Odd k }), ContDiff ℝ ∞ (G I hΦ m T (lIdx β I.Λ m (↑k : ℤ)) t)) → (∀ k ∈ U,
    ∀ (x : Vec (2 : ℕ)), HasFDerivAt (F0 k) (fderiv ℝ (F0 k) x) x) →
  let P : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ := J - κ • (1 : Matrix (Fin (2 : ℕ)) (Fin (2 :
    ℕ)) ℝ);
  let R : { k : ℤ // Odd k } → Vec (2 : ℕ) → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ := fun (k : {
    k : ℤ // Odd k }) (y : Vec (2 : ℕ)) => (flowGradK I hΦ m (↑k : ℤ) t y).transpose * P - P;
  let F : { k : ℤ // Odd k } → Vec (2 : ℕ) → Vec (2 : ℕ) := fun (k : { k : ℤ // Odd k }) (y :
    Vec (2 : ℕ)) => F0 k y + (R k y).mulVec (G I hΦ m T (lIdx β I.Λ m (↑k : ℤ)) t y);
  (∀ (k : { k : ℤ // Odd k }), ContDiff ℝ ∞ (R k)) → ∀ k ∈ U, ∀ (x : Vec (2 : ℕ)), vecDiv (F k)
    x = vecDiv (F0 k) x + frob (R k x) (gradG I hΦ m T (lIdx β I.Λ m (↑k : ℤ)) t x)
    := by
  intro β I Φ hΦ m hm κ T t U J F0 hGsm hF0der P R F hRsm k hk x
  have hG := hGsm k
  have hGder : HasFDerivAt (G I hΦ m T (lIdx β I.Λ m k.1) t)
      (fderiv ℝ (G I hΦ m T (lIdx β I.Λ m k.1) t) x) x :=
    (hG.differentiable (by simp) x).hasFDerivAt
  obtain ⟨LA, hA, hdiv⟩ := LeftJacobian.piola_column_hasFDerivAt I hΦ m k.1 t P 0 x
  have hRder (i j : Fin 2) : HasFDerivAt (fun y => R k y i j) (LA i j - 0) x := by
    have hfun : (fun y => R k y i j) = fun y => ((0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (flowGradK I hΦ m k.1 t y).transpose * P) i j - P i j := by
      funext y
      simp [R]
    rw [hfun]
    exact (hA i j).sub (hasFDerivAt_const (P i j) x)
  have hmatR : matDiv (R k) x = 0 := by
    funext j
    unfold matDiv
    have hterm (i : Fin 2) : spaceGrad (fun y => R k y i j) x i = LA i j (basisVec i) := by
      rw [spaceGrad, (hRder i j).fderiv]
      simp
    simp only [hterm]
    exact hdiv j
  have hprod := vecDiv_matrixMulVec_frob hRder hGder
  rw [hmatR] at hprod
  have hRG : HasFDerivAt (fun y => (R k y).mulVec (G I hΦ m T (lIdx β I.Λ m k.1) t y))
      (fderiv ℝ (fun y => (R k y).mulVec (G I hΦ m T (lIdx β I.Λ m k.1) t y)) x) x :=
    ((BigBoundMeanZeroGroup.matrixMulVec_contDiff_infty (hRsm k) hG).differentiable (by simp)
        x).hasFDerivAt
  have hadd := vecDiv_add_of_hasFDerivAt (hF0der k hk x) hRG
  change vecDiv (fun y => F0 k y + (R k y).mulVec (G I hΦ m T (lIdx β I.Λ m k.1) t y)) x = _
  rw [hadd, hprod]
  have hgradG : gradG I hΦ m T (lIdx β I.Λ m k.1) t x =
      gradMatrix (G I hΦ m T (lIdx β I.Λ m k.1) t) x := rfl
  rw [hgradG]
  simp [vecDot]

/-- The sum of the three corrector error terms is a divergence.  Its flux is
the finite active-mode sum of `(J-C_k)G_k + T PDot_k`, where `PDot_k` is the
Piola push-forward of the fixed-space time derivative of the shear. -/
theorem group_meanZero_of_slice {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) {t : ℝ}
    (hTsm : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hTper : IsZ2Periodic (T t)) :
    MeanZeroOn unitCube (fun x => twistie4 I hΦ m κ T t x +
      twistie5 I hΦ m κ T t x + normie3 I hΦ m κ T t x) := by
  classical
  let U := (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  let J := I.flux κ m t
  let F0 : {k : ℤ // Odd k} → Vec 2 → Vec 2 := fun k x =>
    (J - correctorFlux I hΦ m κ k.1 t x).mulVec
        (G I hΦ m T (lIdx β I.Λ m k.1) t x) +
      (T t x) • chiTimePushforwardFlux I hΦ m κ k.1 t x
  have hxi (k : {k : ℤ // Odd k}) (hk : k ∈ U) :
      I.xiMK m k.1 t ≠ 0 := by
    exact (Infra.Section3.xiMK_odd_support_finite I hm t).mem_toFinset.mp hk
  have h4rep : twistie4ND I hΦ m κ T t = fun x =>
      -∑ k ∈ U, I.xiMK m k.1 t *
        vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
          (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x) := by
    funext x
    simp only [twistie4ND]
    change -(∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t *
      vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
        (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x)) = _
    have hs := xiMK_odd_tsum_eq_subtype_support_sum I m hm t
      (fun k => vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
        (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x))
    rw [show (∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t *
        vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
          (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x)) =
        ∑ k ∈ U, I.xiMK m k.1 t *
          vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
            (matDiv (correctorDefectMatrix I hΦ m k.1 t κ) x) from by
          simpa only [smul_eq_mul] using hs]
  have h5rep : twistie5ND I hΦ m κ T t = fun x =>
      -∑ k ∈ U, I.xiMK m k.1 t *
        vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
          (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x) := by
    funext x
    simp only [twistie5ND]
    change -(∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t *
      vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
        (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x)) = _
    have hs := xiMK_odd_tsum_eq_subtype_support_sum I m hm t
      (fun k => vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
        (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x))
    rw [show (∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t *
        vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
          (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x)) =
        ∑ k ∈ U, I.xiMK m k.1 t *
          vecDot (G I hΦ m T (lIdx β I.Λ m k.1) t x)
            (matDiv (correctorPushforwardMatrix I hΦ m k.1 t κ) x) from by
          simpa only [smul_eq_mul] using hs]
  have h3rep : BigBoundMeanZeroGroup.meanZeroGroupNormie3Old I hΦ m κ T t = fun x =>
      ∑ k ∈ U, I.xiMK m k.1 t *
        frob (J - correctorFlux I hΦ m κ k.1 t x)
          (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) := by
    funext x
    unfold BigBoundMeanZeroGroup.meanZeroGroupNormie3Old
    have hs := xiMK_odd_tsum_eq_subtype_support_sum I m hm t
      (fun k => frob (J - correctorFlux I hΦ m κ k.1 t x)
        (gradG I hΦ m T (lIdx β I.Λ m k.1) t x))
    rw [show (∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t *
        frob (J - correctorFlux I hΦ m κ k.1 t x)
          (gradG I hΦ m T (lIdx β I.Λ m k.1) t x)) =
        ∑ k ∈ U, I.xiMK m k.1 t *
          frob (J - correctorFlux I hΦ m κ k.1 t x)
            (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) from by
          simpa only [smul_eq_mul] using hs]
  have hCsm (k : {k : ℤ // Odd k}) (hk : k ∈ U) :
      ContDiff ℝ (⊤ : ℕ∞) (correctorFlux I hΦ m κ k.1 t) :=
    (correctorFlux_regular_of_mode I hΦ m hm κ k.1 t k.2 (hxi k hk)).1
  have hGsm (k : {k : ℤ // Odd k}) :
      ContDiff ℝ (⊤ : ℕ∞) (G I hΦ m T (lIdx β I.Λ m k.1) t) :=
    G_contDiff_infty I hΦ m T t (lIdx β I.Λ m k.1) hTsm
  have hPsm (k : {k : ℤ // Odd k}) :
      ContDiff ℝ (⊤ : ℕ∞) (chiTimePushforwardFlux I hΦ m κ k.1 t) :=
    (chiTimePushforwardFlux_regular I hΦ hm κ k.1 t).1
  have hF0sm (k : {k : ℤ // Odd k}) (hk : k ∈ U) :
      ContDiff ℝ (⊤ : ℕ∞) (F0 k) := by
    dsimp [F0]
    exact (BigBoundMeanZeroGroup.matrixMulVec_contDiff_infty
        ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
          (fun _ : Vec 2 => J)).sub (hCsm k hk)) (hGsm k)).add
      (hTsm.smul (hPsm k))
  have hF0per (k : {k : ℤ // Odd k}) (hk : k ∈ U) : IsZ2Periodic (F0 k) := by
    intro z x
    dsimp [F0]
    have hCper := (correctorFlux_regular_of_mode I hΦ m hm κ k.1 t k.2
      (hxi k hk)).2
    have hGper := G_isZ2Periodic I hΦ m T t (lIdx β I.Λ m k.1)
      hTper (hTsm.of_le (by norm_num))
    have hPper := (chiTimePushforwardFlux_regular I hΦ hm κ k.1 t).2.1
    rw [hCper z x, hGper z x, hTper z x, hPper z x]
  have hF0der (k : {k : ℤ // Odd k}) (hk : k ∈ U) (x : Vec 2) :
      HasFDerivAt (F0 k) (fderiv ℝ (F0 k) x) x :=
    (hF0sm k hk).differentiable (by simp) x |>.hasFDerivAt
  have hgroupOld (x : Vec 2) :
      twistie4ND I hΦ m κ T t x + twistie5ND I hΦ m κ T t x +
        BigBoundMeanZeroGroup.meanZeroGroupNormie3Old I hΦ m κ T t x =
      ∑ k ∈ U, I.xiMK m k.1 t * vecDiv (F0 k) x := by
    exact @group_meanZero_of_slice_groupOld1 β I Φ hΦ m hm κ T t hTsm hxi h4rep h5rep h3rep hCsm
        hGsm hPsm x
  -- LeftJacobian: the extra Piola term `Σ_k ξ_k (F_kᵀ - 1) P : ∇G_k`, `P = 𝒥 - κ I`
  let P : Matrix (Fin 2) (Fin 2) ℝ := J - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  let R : {k : ℤ // Odd k} → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun k y =>
    (flowGradK I hΦ m k.1 t y).transpose * P - P
  let F : {k : ℤ // Odd k} → Vec 2 → Vec 2 := fun k y =>
    F0 k y + (R k y).mulVec (G I hΦ m T (lIdx β I.Λ m k.1) t y)
  have hRsm (k : {k : ℤ // Odd k}) : ContDiff ℝ (⊤ : ℕ∞) (R k) := by
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    simp only [R, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact (ContDiff.sum fun a _ =>
      (LeftJacobian.contDiff_flowGradK_entry I hΦ m k.1 t a i).mul contDiff_const).sub
          contDiff_const
  have hRper (k : {k : ℤ // Odd k}) : IsZ2Periodic (R k) := by
    intro z x
    have h' : flowGradK I hΦ m k.1 t (x + latticeShift z) = flowGradK I hΦ m k.1 t x := by
      ext i j
      exact Infra.Section4.amnr_flowGrad_spatial_periodic I hΦ m (lIdx β I.Λ m k.1) t i j z x
    simp only [R]
    rw [h']
  have hFsm (k : {k : ℤ // Odd k}) (hk : k ∈ U) : ContDiff ℝ (⊤ : ℕ∞) (F k) :=
    (hF0sm k hk).add (BigBoundMeanZeroGroup.matrixMulVec_contDiff_infty (hRsm k) (hGsm k))
  have hFper (k : {k : ℤ // Odd k}) (hk : k ∈ U) : IsZ2Periodic (F k) := by
    intro z x
    have h0 := hF0per k hk z x
    have h1 := hRper k z x
    have h2 := G_isZ2Periodic I hΦ m T t (lIdx β I.Λ m k.1)
      hTper (hTsm.of_le (by norm_num)) z x
    simp only [F]
    rw [h0, h1, h2]
  have hFder (k : {k : ℤ // Odd k}) (hk : k ∈ U) (x : Vec 2) :
      HasFDerivAt (F k) (fderiv ℝ (F k) x) x :=
    (hFsm k hk).differentiable (by simp) x |>.hasFDerivAt
  -- divergence of the extra term
  have hperk (k : {k : ℤ // Odd k}) (hk : k ∈ U) (x : Vec 2) :
      vecDiv (F k) x = vecDiv (F0 k) x +
        frob (R k x) (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) := by
    exact @group_meanZero_of_slice_perk3 β I Φ hΦ m hm κ T t hGsm hF0der hRsm k hk x
  -- the new slot bodies against the old ones
  have hnewPoint (x : Vec 2) :
      twistie4 I hΦ m κ T t x + twistie5 I hΦ m κ T t x + normie3 I hΦ m κ T t x =
        twistie4ND I hΦ m κ T t x + twistie5ND I hΦ m κ T t x +
          BigBoundMeanZeroGroup.meanZeroGroupNormie3Old I hΦ m κ T t x +
        ∑ k ∈ U, I.xiMK m k.1 t * frob (R k x) (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) := by
    exact @group_meanZero_of_slice_newPoint2 β I Φ hΦ m hm κ T t hTsm x
  have hpointFlux (x : Vec 2) :
      twistie4 I hΦ m κ T t x + twistie5 I hΦ m κ T t x +
        normie3 I hΦ m κ T t x =
      vecDiv (fun y => ∑ k ∈ U, I.xiMK m k.1 t • F k y) x := by
    rw [hnewPoint, hgroupOld]
    symm
    rw [vecDiv_finite_weighted_sum U (fun k => I.xiMK m k.1 t) F x
      (fun k hk => hFder k hk x)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hperk k hk x]
    ring
  have hWsm : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => ∑ k ∈ U, I.xiMK m k.1 t • F k y) := by
    apply ContDiff.sum
    intro k hk
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => I.xiMK m k.1 t)).smul (hFsm k hk)
  have hWper : IsZ2Periodic (fun y => ∑ k ∈ U, I.xiMK m k.1 t • F k y) := by
    intro z x
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    exact congrArg (fun v : Vec 2 => I.xiMK m k.1 t • v i)
      (hFper k hk z x)
  unfold MeanZeroOn
  have hmean := meanZeroOn_vecDiv_of_contDiff_periodic hWsm hWper
  calc
    (∫ x in unitCube,
        twistie4 I hΦ m κ T t x + twistie5 I hΦ m κ T t x +
          normie3 I hΦ m κ T t x) =
        ∫ x in unitCube, vecDiv
          (fun y => ∑ k ∈ U, I.xiMK m k.1 t • F k y) x := by
            congr 1
            funext x
            exact hpointFlux x
    _ = 0 := hmean

end AVenhance.Infra.Section5.Integration

end
