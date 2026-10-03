/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.Candidate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.Transport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.PiolaColumn
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenShearDiffusionOperator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorDiffusionDivergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ResidualR46
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.OddSupportTsum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.DivergenceLinearity

/-!: the literal-name residual identity (36) from the material and
diffusion expansions.

This is the corrected-form analogue of `frozen_residual_identity_of_expansions`: the
`hnorm` step is replaced by the identity
`Σ_q ξ_q (κ I + F_qᵀ P) : ∇G_q - Σ_q ξ_q C_q : ∇G_q = normie3Sel`, and the averaged
transport contraction is replaced by the divergence of the coarse transport flux
`V_tr` (`transportFluxPlus`), which is evaluated through the Piola column lemma. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem Assembly.vecDot_comm' (u v : Vec 2) : vecDot u v = vecDot v u := by
  simp [vecDot, Fin.sum_univ_two]
  ring

/-- `frob` is additive-subtractive in its first slot. -/
theorem Assembly.asm_frob_sub_left (A B C : Matrix (Fin 2) (Fin 2) ℝ) :
    frob (A - B) C = frob A C - frob B C := by
  simp only [frob, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The field `y ↦ (κ I + F_k(y)ᵀ P) V(y)` is differentiable at `x` when `V` is. -/
theorem Assembly.asm_piola_mulVec_differentiableAt (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ)
    (P : Matrix (Fin 2) (Fin 2) ℝ) (κm : ℝ) (V : Vec 2 → Vec 2) (x : Vec 2)
    (hV : DifferentiableAt ℝ V x) :
    DifferentiableAt ℝ (fun y => (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (flowGradK I hΦ m k t y).transpose * P).mulVec (V y)) x := by
  obtain ⟨LA, hA, _⟩ := piola_column_hasFDerivAt I hΦ m k t P κm x
  rw [differentiableAt_pi]
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine DifferentiableAt.fun_sum fun p _ => ?_
  exact (hA i p).differentiableAt.mul ((differentiableAt_pi.mp hV) p)

/-- `V_tr` is differentiable at `x` under the regularity hypotheses of the divergence formula. -/
theorem Assembly.asm_transportFluxPlus_differentiableAt (hΦ : IsStreamSeq I Φ) (m : ℕ)
    (hm : 1 ≤ m) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (hT : ContDiff ℝ 1 (T t)) (x : Vec 2)
    (hG : ∀ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
      DifferentiableAt ℝ (fun y => G I hΦ m T (lIdx β I.Λ m q.1) t y) x)
    (hr46 : DifferentiableAt ℝ (r46Flux I hΦ m κm T t) x) :
    DifferentiableAt ℝ (transportFluxPlus I hΦ m κm T t) x := by
  classical
  have hfun : transportFluxPlus I hΦ m κm T t = fun y =>
      (∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t • ((κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (flowGradK I hΦ m q.1 t y).transpose * (I.flux κm m t - κm • 1)).mulVec
            (G I hΦ m T (lIdx β I.Λ m q.1) t y))) + r46Flux I hΦ m κm T t y := by
    funext y
    exact transportFluxPlus_eq_selected I hΦ m hm κm T t hT y
  rw [hfun]
  refine DifferentiableAt.add ?_ hr46
  exact DifferentiableAt.fun_sum fun q hq =>
    (Assembly.asm_piola_mulVec_differentiableAt I hΦ m q.1 t _ κm _ x (hG q hq)).fun_const_smul _

/-- The divergence of the coarse transport flux `V_tr` at `x`: the finite Piola sum of
`ξ_q (κ I + F_qᵀ P) : ∇G_q` plus the transition remainder `R46`. -/
theorem Assembly.asm_vecDiv_transportFluxPlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (hT : ContDiff ℝ 1 (T t)) (x : Vec 2)
    (hG : ∀ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
      DifferentiableAt ℝ (fun y => G I hΦ m T (lIdx β I.Λ m q.1) t y) x)
    (hr46 : DifferentiableAt ℝ (r46Flux I hΦ m κm T t) x) :
    vecDiv (transportFluxPlus I hΦ m κm T t) x =
      (∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t *
          frob (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            (flowGradK I hΦ m q.1 t x).transpose *
              (I.flux κm m t - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
            (gradG I hΦ m T (lIdx β I.Λ m q.1) t x)) +
      R46 I hΦ m κm T t x := by
  classical
  set U := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset with hU
  set P : Matrix (Fin 2) (Fin 2) ℝ := I.flux κm m t - κm • 1 with hP
  let W : {k : ℤ // Odd k} → Vec 2 → Vec 2 := fun q y =>
    (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (flowGradK I hΦ m q.1 t y).transpose * P).mulVec
      (G I hΦ m T (lIdx β I.Λ m q.1) t y)
  have hW : ∀ q ∈ U, DifferentiableAt ℝ (W q) x := fun q hq =>
    Assembly.asm_piola_mulVec_differentiableAt I hΦ m q.1 t P κm _ x (hG q hq)
  have hfun : transportFluxPlus I hΦ m κm T t = fun y =>
      (∑ q ∈ U, I.xiMK m q.1 t • W q y) + r46Flux I hΦ m κm T t y := by
    funext y
    exact transportFluxPlus_eq_selected I hΦ m hm κm T t hT y
  have hsum : DifferentiableAt ℝ (fun y => ∑ q ∈ U, I.xiMK m q.1 t • W q y) x :=
    DifferentiableAt.fun_sum fun q hq => (hW q hq).fun_const_smul _
  rw [hfun, vecDiv_add_of_hasFDerivAt hsum.hasFDerivAt hr46.hasFDerivAt,
    vecDiv_finite_weighted_sum U (fun q => I.xiMK m q.1 t) W x
      (fun q hq => (hW q hq).hasFDerivAt)]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [vecDiv_piola_mulVec I hΦ m q.1 t P κm _ x (hG q hq)]
  rfl

private theorem variantA_residual_identity_sel_of_expansions_chiErrorSplit1 :
  ∀ {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm
    : (1 : ℕ) ≤ m) (κ : ℝ) (T : ℝ → Vec (2 : ℕ) → ℝ) (e : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)) (t : ℝ)
    (x : Vec (2 : ℕ)), gradDiv (fun (s : ℝ) (y : Vec (2 : ℕ)) => (I.Kmat κ m s + I.sMat hΦ m κ s
    y).mulVec (spaceGrad (T s) y) + e s y) t x = gradDiv (fun (s : ℝ) (y : Vec (2 : ℕ)) =>
    (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec (spaceGrad (T s) y)) t x + gradDiv e t x →
  let U : Finset { k : ℤ // Odd k } := (Section3.xiMK_odd_support_finite I hm t).toFinset;
  ∑ q ∈ U, I.xiMK m (↑q : ℤ) t * vecDot (I.chiTilde hΦ m κ (↑q : ℤ) t x) ((I.flowGrad hΦ m (lIdx
    β I.Λ m (↑q : ℤ)) t x).mulVec (gradDiv e t x)) = ∑' (q : { k : ℤ // Odd k }), I.xiMK m (↑q :
    ℤ) t * vecDot (I.chiTilde hΦ m κ (↑q : ℤ) t x) ((I.flowGrad hΦ m (lIdx β I.Λ m (↑q : ℤ)) t
    x).mulVec (gradDiv e t x)) → ∑ q ∈ U, I.xiMK m (↑q : ℤ) t * vecDot (I.chiTilde hΦ m κ (↑q :
    ℤ) t x) ((I.flowGrad hΦ m (lIdx β I.Λ m (↑q : ℤ)) t x).mulVec (gradDiv (fun (s : ℝ) (y : Vec
    (2 : ℕ)) => (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec (spaceGrad (T s) y) + e s y) t x)) =
    twistie1 I hΦ m κ T t x + ∑' (q : { k : ℤ // Odd k }), I.xiMK m (↑q : ℤ) t * vecDot
    (I.chiTilde hΦ m κ (↑q : ℤ) t x) ((I.flowGrad hΦ m (lIdx β I.Λ m (↑q : ℤ)) t x).mulVec
    (gradDiv e t x))
    := by
  intro β I Φ hΦ m hm κ T e t x hgradDivSplit U hchiError'
  have hsplit :
      (∑ q ∈ U, I.xiMK m q.1 t *
        vecDot (I.chiTilde hΦ m κ q.1 t x)
          ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
            (gradDiv (fun s y =>
              (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec
                  (spaceGrad (T s) y) + e s y) t x))) =
        (∑ q ∈ U, I.xiMK m q.1 t *
          vecDot (I.chiTilde hΦ m κ q.1 t x)
            ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
              (gradDiv (fun s y =>
                (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec
                    (spaceGrad (T s) y)) t x))) +
          (∑ q ∈ U, I.xiMK m q.1 t *
            vecDot (I.chiTilde hΦ m κ q.1 t x)
              ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
                (gradDiv e t x))) := by
    rw [hgradDivSplit, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    simp [Matrix.mulVec_add, vecDot, Fin.sum_univ_two]
    ring
  have hK := xiMK_odd_tsum_eq_subtype_support_sum I m hm t
    (fun q => vecDot (I.chiTilde hΦ m κ q.1 t x)
      ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
        (gradDiv (fun s y =>
          (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec
              (spaceGrad (T s) y)) t x)))
  rw [hsplit]
  have hK' :
      (∑ q ∈ U, I.xiMK m q.1 t *
        vecDot (I.chiTilde hΦ m κ q.1 t x)
          ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
            (gradDiv (fun s y =>
              (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec
                  (spaceGrad (T s) y)) t x))) =
        twistie1 I hΦ m κ T t x := by
    simpa [twistie1, flowGradK, smul_eq_mul] using hK.symm
  rw [hK', hchiError']

/-- **corrected-form literal residual identity (36)** from the two expansions.

Hypotheses, all of the shape of `frozen_residual_identity_of_expansions` except as noted:
* `hS`, `hpartition`: `S` is the finite support of the odd transition weights at time `t`,
  and those weights sum to one on it.
* `hgradDivSplit`: the coefficient `I.sMat` splits `gradDiv` against `e` (a
  differentiability fact, identical to the one; no `sMatPlus` is needed here).
* `hmaterial`: the source material expansion, with the averaged-flux term replaced by the
  divergence of `V_tr + d + e` (`transportFluxPlus`).
* `hdiffusion`: the selected diffusion expansion, identical to the one.
* `hT`: `T t` is `C¹` (so `G_l = F_l ∇T` and `V_tr` has its selected form).
* `hG`: each `G_q`, `q ∈ S`, is differentiable at `x`.
* `hr46`: the transition flux `r46Flux` is differentiable at `x`.
* `hde`: `d t + e t` is differentiable at `x`.
* `hAnsatz`: the ansatz is `C²` at `x` (for the operator divergence split). -/
theorem variantA_residual_identity_sel_of_expansions
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (x : Vec 2) (S : Finset {k : ℤ // Odd k})
    (hS : S = (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset)
    (hpartition : ∑ q ∈ S, I.xiMK m q.1 t = 1)
    (hgradDivSplit :
      gradDiv (fun s y =>
        (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec
            (spaceGrad (T s) y) + e s y) t x =
        gradDiv (fun s y =>
          (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec
              (spaceGrad (T s) y)) t x + gradDiv e t x)
    (hmaterial :
      deriv (fun s => I.ansatz hΦ m κ T s x) t +
          vecDot (streamVel (Φ (m - 1)) t x)
            (spaceGrad (I.ansatz hΦ m κ T t) x) =
        cutoff1 I hΦ m κ T t x +
          (∑ q ∈ S, I.xiMK m q.1 t *
            vecDot (fun j => deriv (fun s => I.chiMK κ m q.1 s
              (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
              (G I hΦ m T (lIdx β I.Λ m q.1) t x)) +
          (∑ q ∈ S, I.xiMK m q.1 t *
            vecDot (I.chiTilde hΦ m κ q.1 t x)
              ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
                (gradDiv (fun s y =>
                  (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec
                    (spaceGrad (T s) y) + e s y) t x))) +
          vecDiv (fun y => transportFluxPlus I hΦ m κ T t y + d t y + e t y) x)
    (hdiffusion :
      vecDiv (fun y => (diffusionMatrix I hΦ m κ t y).mulVec
          (spaceGrad (I.ansatz hΦ m κ T t) y)) x =
        (∑ q ∈ S, I.xiMK m q.1 t *
          vecDot (matDiv (correctorDefectMatrix I hΦ m q.1 t κ) x)
            (G I hΦ m T (lIdx β I.Λ m q.1) t x)) +
        (∑ q ∈ S, I.xiMK m q.1 t *
          vecDot (matDiv (correctorPushforwardMatrix I hΦ m q.1 t κ) x)
            (G I hΦ m T (lIdx β I.Λ m q.1) t x)) +
        (∑ q ∈ S, I.xiMK m q.1 t *
          frob (correctorFlux I hΦ m κ q.1 t x)
            (gradG I hΦ m T (lIdx β I.Λ m q.1) t x)) +
        (∑ q ∈ S, I.xiMK m q.1 t *
          vecDot (fun j => deriv (fun s => I.chiMK κ m q.1 s
            (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
            (G I hΦ m T (lIdx β I.Λ m q.1) t x)) -
        twistie3 I hΦ m κ T t x - normie1 I hΦ m κ T t x -
          normie2 I hΦ m κ T t x)
    (hT : ContDiff ℝ 1 (T t))
    (hG : ∀ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
      DifferentiableAt ℝ (fun y => G I hΦ m T (lIdx β I.Λ m q.1) t y) x)
    (hr46 : DifferentiableAt ℝ (r46Flux I hΦ m κ T t) x)
    (hde : DifferentiableAt ℝ (fun y => d t y + e t y) x)
    (hAnsatz : ContDiffAt ℝ 2 (I.ansatz hΦ m κ T t) x) :
    residualIdentitySel I hΦ m κ T d e (streamVel (Φ m)) t x := by
  classical
  subst S
  let U := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have hdefect :
      (∑ q ∈ U, I.xiMK m q.1 t *
        vecDot (matDiv (correctorDefectMatrix I hΦ m q.1 t κ) x)
          (G I hΦ m T (lIdx β I.Λ m q.1) t x)) =
        -twistie4ND I hΦ m κ T t x := by
    have hbridge := xiMK_odd_tsum_eq_subtype_support_sum I m hm t
      (fun q => vecDot (G I hΦ m T (lIdx β I.Λ m q.1) t x)
        (matDiv (correctorDefectMatrix I hΦ m q.1 t κ) x))
    calc
      _ = ∑ q ∈ U, I.xiMK m q.1 t *
          vecDot (G I hΦ m T (lIdx β I.Λ m q.1) t x)
            (matDiv (correctorDefectMatrix I hΦ m q.1 t κ) x) := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [Assembly.vecDot_comm']
      _ = ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t *
          vecDot (G I hΦ m T (lIdx β I.Λ m q.1) t x)
            (matDiv (correctorDefectMatrix I hΦ m q.1 t κ) x) := by
              simpa [smul_eq_mul] using hbridge.symm
      _ = -twistie4ND I hΦ m κ T t x := by
        simp only [twistie4ND, neg_neg]
        apply tsum_congr
        intro q
        rfl
  have hpush :
      (∑ q ∈ U, I.xiMK m q.1 t *
        vecDot (matDiv (correctorPushforwardMatrix I hΦ m q.1 t κ) x)
          (G I hΦ m T (lIdx β I.Λ m q.1) t x)) =
        -twistie5ND I hΦ m κ T t x := by
    have hbridge := xiMK_odd_tsum_eq_subtype_support_sum I m hm t
      (fun q => vecDot (G I hΦ m T (lIdx β I.Λ m q.1) t x)
        (matDiv (correctorPushforwardMatrix I hΦ m q.1 t κ) x))
    have hterm (q : {k : ℤ // Odd k}) :
        correctorPushforwardMatrix I hΦ m q.1 t κ = fun y =>
          (1 - (flowGradK I hΦ m q.1 t y).transpose) *
            ((I.hatZetaML m (lIdx β I.Λ m q.1) t * I.zetaMK m q.1 t *
                psi β I.Λ m q.1
                  (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t y)) • sigmaMat +
              κ • gradMatrix (fun z => I.chiMK κ m q.1 t z)
                (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t y)) := by
      funext y
      simp [correctorPushforwardMatrix, correctorBaseMatrix, flowGradK,
        Ingredients.zetaProd]
    calc
      _ = ∑ q ∈ U, I.xiMK m q.1 t *
          vecDot (G I hΦ m T (lIdx β I.Λ m q.1) t x)
            (matDiv (correctorPushforwardMatrix I hΦ m q.1 t κ) x) := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [Assembly.vecDot_comm']
      _ = ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t *
          vecDot (G I hΦ m T (lIdx β I.Λ m q.1) t x)
            (matDiv (correctorPushforwardMatrix I hΦ m q.1 t κ) x) := by
              simpa [smul_eq_mul] using hbridge.symm
      _ = -twistie5ND I hΦ m κ T t x := by
        simp [twistie5ND, hterm]
  have hchiTime := xiMK_odd_tsum_eq_subtype_support_sum I m hm t
    (fun q => vecDot (fun j => deriv (fun s => I.chiMK κ m q.1 s
      (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
      (G I hΦ m T (lIdx β I.Λ m q.1) t x))
  have hchiError := xiMK_odd_tsum_eq_subtype_support_sum I m hm t
    (fun q => vecDot (I.chiTilde hΦ m κ q.1 t x)
      ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
        (gradDiv e t x)))
  have hchiError' :
      (∑ q ∈ U, I.xiMK m q.1 t *
        vecDot (I.chiTilde hΦ m κ q.1 t x)
          ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
            (gradDiv e t x))) =
        ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t *
          vecDot (I.chiTilde hΦ m κ q.1 t x)
            ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
              (gradDiv e t x)) := by
    simpa [smul_eq_mul] using hchiError.symm
  have hchiErrorSplit :
      (∑ q ∈ U, I.xiMK m q.1 t *
        vecDot (I.chiTilde hΦ m κ q.1 t x)
          ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
            (gradDiv (fun s y =>
              (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec
                  (spaceGrad (T s) y) + e s y) t x))) =
        twistie1 I hΦ m κ T t x +
          ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t *
            vecDot (I.chiTilde hΦ m κ q.1 t x)
              ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
                (gradDiv e t x)) := by
    exact @variantA_residual_identity_sel_of_expansions_chiErrorSplit1 β I Φ hΦ m hm κ T e t x
        hgradDivSplit hchiError'
  have htimeFin :
      (∑ q ∈ U, I.xiMK m q.1 t *
        vecDot (fun j => deriv (fun s => I.chiMK κ m q.1 s
          (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
          (G I hΦ m T (lIdx β I.Λ m q.1) t x)) =
      ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t *
        vecDot (fun j => deriv (fun s => I.chiMK κ m q.1 s
          (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
          (G I hΦ m T (lIdx β I.Λ m q.1) t x) := by
    simpa [smul_eq_mul] using hchiTime.symm
  have hdivSplit :
      vecDiv (fun y => transportFluxPlus I hΦ m κ T t y + d t y + e t y) x =
        ((∑ q ∈ U, I.xiMK m q.1 t *
          frob (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            (flowGradK I hΦ m q.1 t x).transpose *
              (I.flux κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
            (gradG I hΦ m T (lIdx β I.Λ m q.1) t x)) +
          R46 I hΦ m κ T t x) + vecDiv (fun y => d t y + e t y) x := by
    have hVtr := Assembly.asm_vecDiv_transportFluxPlus I hΦ m hm κ T t hT x hG hr46
    have hVdiff : DifferentiableAt ℝ (transportFluxPlus I hΦ m κ T t) x := by
      exact Assembly.asm_transportFluxPlus_differentiableAt I hΦ m hm κ T t hT x hG hr46
    have hfun : (fun y => transportFluxPlus I hΦ m κ T t y + d t y + e t y) =
        fun y => transportFluxPlus I hΦ m κ T t y + (d t y + e t y) := by
      funext y
      exact add_assoc _ _ _
    rw [hfun, vecDiv_add_of_hasFDerivAt hVdiff.hasFDerivAt hde.hasFDerivAt, hVtr]
  have hnorm :
      (∑ q ∈ U, I.xiMK m q.1 t *
          frob (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            (flowGradK I hΦ m q.1 t x).transpose *
              (I.flux κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
            (gradG I hΦ m T (lIdx β I.Λ m q.1) t x)) -
        (∑ q ∈ U, I.xiMK m q.1 t *
          frob (correctorFlux I hΦ m κ q.1 t x)
            (gradG I hΦ m T (lIdx β I.Λ m q.1) t x)) =
        normie3Sel I hΦ m κ T t x := by
    have hTsum := xiMK_odd_tsum_eq_subtype_support_sum I m hm t
      (fun q => frob (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (flowGradK I hΦ m q.1 t x).transpose *
          (I.flux κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) -
        correctorFlux I hΦ m κ q.1 t x)
        (gradG I hΦ m T (lIdx β I.Λ m q.1) t x))
    have hfin : normie3Sel I hΦ m κ T t x =
        ∑ q ∈ U, I.xiMK m q.1 t *
          frob (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            (flowGradK I hΦ m q.1 t x).transpose *
              (I.flux κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) -
            correctorFlux I hΦ m κ q.1 t x)
            (gradG I hΦ m T (lIdx β I.Λ m q.1) t x) := by
      simpa [normie3Sel, smul_eq_mul] using hTsum
    rw [hfin, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [Assembly.asm_frob_sub_left]
    ring
  have hoperator := frozen_stream_advDiffOp_divergence_split
    I hΦ m hm κ (I.ansatz hΦ m κ T) t x hAnsatz
  have hoperator' : advDiffOp (streamVel (Φ m)) κ (I.ansatz hΦ m κ T) t x =
      (deriv (fun s => I.ansatz hΦ m κ T s x) t +
        vecDot (streamVel (Φ (m - 1)) t x)
          (spaceGrad (I.ansatz hΦ m κ T t) x)) -
        vecDiv (fun y => (diffusionMatrix I hΦ m κ t y).mulVec
          (spaceGrad (I.ansatz hΦ m κ T t) y)) x := by
    simpa [diffusionMatrix] using hoperator
  change advDiffOp (streamVel (Φ m)) κ (I.ansatz hΦ m κ T) t x =
      nineTermsSel I hΦ m κ T d e t x + R46 I hΦ m κ T t x
  rw [hoperator', hmaterial, hdiffusion]
  rw [hdefect, hpush, htimeFin, hchiErrorSplit, hdivSplit]
  simp only [nineTermsSel, tiny, flowGradK]
  simp only [flowGradK] at hnorm
  linear_combination hnorm

end AVenhance.Infra.Section5.LeftJacobian

end
