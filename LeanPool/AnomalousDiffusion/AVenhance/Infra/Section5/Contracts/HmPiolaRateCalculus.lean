/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmSourceRatesGradientCore
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.PulledFluxSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.Transport

/-! # Pointwise calculus for the LeftJacobian Piola source

For a constant matrix `M`, the divergence of the pulled gap flux
`y ↦ Σ_l ξ̂_l F_lᵀ M F_l ∇T` is bounded pointwise by
`32 A · hmPiolaQ`, where `A` bounds the entries of `M` and `hmPiolaQ` is the
Hessian/gradient majorant already used for the averaged pulled gradient.  The
proof is the plain product rule: the derivative of `F_l` is expressed through
the second flow derivative `xFlowHess` and the Jacobian of the inverse flow, and
all active flow factors are bounded by the stream-function estimates. -/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.RelativeError
open AVenhance.Infra.Section4

/-- The pointwise majorant of the entries of `∇G_l`, built from `∇T` and the
two first-order Hessian rows of `T`. -/
def hmPiolaQ (E : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  4 * (Real.sqrt (vecNormSq
        (spaceGrad (iterateSpatialWord [0] (T t)) x)) +
      Real.sqrt (vecNormSq
        (spaceGrad (iterateSpatialWord [1] (T t)) x))) +
    2 ^ 19 / E * Real.sqrt (vecNormSq (spaceGrad (T t) x))

theorem hmPiolaQ_nonneg (E : ℝ) (hE : 0 < E) (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (x : Vec 2) : 0 ≤ hmPiolaQ E T t x := by
  unfold hmPiolaQ
  positivity

theorem hmPiolaQ_ge (E : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    2 ^ 19 / E * Real.sqrt (vecNormSq (spaceGrad (T t) x)) ≤
      hmPiolaQ E T t x := by
  unfold hmPiolaQ
  have h0 := Real.sqrt_nonneg (vecNormSq
    (spaceGrad (iterateSpatialWord [0] (T t)) x))
  have h1 := Real.sqrt_nonneg (vecNormSq
    (spaceGrad (iterateSpatialWord [1] (T t)) x))
  linarith

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Per-`l` pointwise bound for the entries of `∇G_l` (the per-`l` content of
the bound for `∇GDot`). -/
theorem hmPiola_spaceGrad_G_abs_le
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (T : ℝ → Vec 2 → ℝ) {t : ℝ}
    (hTt : ContDiff ℝ ∞ (T t)) {E : ℝ} (hE : 0 < E) (l : ℤ)
    (hFlow : ∀ x i j, |I.flowGrad hΦ m l t x i j| ≤ 2)
    (hInv : ∀ x i j,
      |gradMatrix (fun y => I.xFlowInv hΦ m l t y) x i j| ≤ 2)
    (hHess : ∀ x p j q, |xFlowHess I hΦ m l t x p j q| ≤ 2 ^ 16 / E)
    (x : Vec 2) (i j : Fin 2) :
    |spaceGrad (fun y => G I hΦ m T l t y j) x i| ≤ hmPiolaQ E T t x := by
  rw [spaceGrad_G_component I hΦ m T l hTt x i j]
  have hgrad (p : Fin 2) :
      |spaceGrad (T t) x p| ≤ Real.sqrt (vecNormSq (spaceGrad (T t) x)) :=
    abs_apply_le_sqrt_vecNormSq _ p
  have hhess (p : Fin 2) :
      |spaceHess (T t) x i p| ≤ Real.sqrt (vecNormSq
        (spaceGrad (iterateSpatialWord [p] (T t)) x)) :=
    abs_apply_le_sqrt_vecNormSq
      (spaceGrad (iterateSpatialWord [p] (T t)) x) i
  have hsqrt := Real.sqrt_nonneg (vecNormSq (spaceGrad (T t) x))
  have hE19 : 0 ≤ 2 ^ 18 / E := by positivity
  have hterm (p : Fin 2) :
      |I.flowGrad hΦ m l t x j p * spaceHess (T t) x i p +
        (∑ q : Fin 2, gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
            xFlowHess I hΦ m l t (I.xFlowInv hΦ m l t x) p j q) *
          spaceGrad (T t) x p| ≤
        2 * Real.sqrt (vecNormSq
          (spaceGrad (iterateSpatialWord [p] (T t)) x)) +
          (2 ^ 18 / E) * Real.sqrt (vecNormSq (spaceGrad (T t) x)) := by
    have hfirst :
        |I.flowGrad hΦ m l t x j p * spaceHess (T t) x i p| ≤
          2 * Real.sqrt (vecNormSq
            (spaceGrad (iterateSpatialWord [p] (T t)) x)) := by
      rw [abs_mul]
      exact mul_le_mul (hFlow x j p) (hhess p) (abs_nonneg _) (by positivity)
    have hinner :
        |∑ q : Fin 2, gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
            xFlowHess I hΦ m l t (I.xFlowInv hΦ m l t x) p j q| ≤
          2 ^ 18 / E := by
      calc
        _ ≤ ∑ q : Fin 2,
            |gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
              xFlowHess I hΦ m l t (I.xFlowInv hΦ m l t x) p j q| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _q : Fin 2, 2 * (2 ^ 16 / E) := by
          apply Finset.sum_le_sum
          intro q _
          rw [abs_mul]
          exact mul_le_mul (hInv x i q) (hHess _ p j q)
            (abs_nonneg _) (by positivity)
        _ = _ := by simp only [Fin.sum_univ_two]; ring
    have hsecond :
        |(∑ q : Fin 2, gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
            xFlowHess I hΦ m l t (I.xFlowInv hΦ m l t x) p j q) *
          spaceGrad (T t) x p| ≤
          (2 ^ 18 / E) * Real.sqrt (vecNormSq (spaceGrad (T t) x)) := by
      rw [abs_mul]
      exact mul_le_mul hinner (hgrad p) (abs_nonneg _) hE19
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  calc
    _ ≤ ∑ p : Fin 2,
        |I.flowGrad hΦ m l t x j p * spaceHess (T t) x i p +
          (∑ q : Fin 2, gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
              xFlowHess I hΦ m l t (I.xFlowInv hΦ m l t x) p j q) *
            spaceGrad (T t) x p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : Fin 2,
        (2 * Real.sqrt (vecNormSq
          (spaceGrad (iterateSpatialWord [p] (T t)) x)) +
          (2 ^ 18 / E) * Real.sqrt (vecNormSq (spaceGrad (T t) x))) :=
      Finset.sum_le_sum fun p _ => hterm p
    _ = 2 * (Real.sqrt (vecNormSq
          (spaceGrad (iterateSpatialWord [0] (T t)) x)) +
        Real.sqrt (vecNormSq
          (spaceGrad (iterateSpatialWord [1] (T t)) x))) +
        2 * ((2 ^ 18 / E) * Real.sqrt (vecNormSq (spaceGrad (T t) x))) := by
      simp only [Fin.sum_univ_two]
      ring
    _ ≤ hmPiolaQ E T t x := by
      unfold hmPiolaQ
      have h0 := Real.sqrt_nonneg (vecNormSq
        (spaceGrad (iterateSpatialWord [0] (T t)) x))
      have h1 := Real.sqrt_nonneg (vecNormSq
        (spaceGrad (iterateSpatialWord [1] (T t)) x))
      have hcoef : 2 * (2 ^ 18 / E) = 2 ^ 19 / E := by ring
      have h2 : 2 * ((2 ^ 18 / E) * Real.sqrt (vecNormSq (spaceGrad (T t) x))) =
          2 ^ 19 / E * Real.sqrt (vecNormSq (spaceGrad (T t) x)) := by
        rw [← mul_assoc, hcoef]
      rw [h2]
      linarith

/-- The spatial derivative of an entry of `F_l = flowGrad`:
`∂_i (F_l)_{pr} = Σ_q (∇Y_l)_{iq} · ∂_q ∂_p X^r_l(Y_l x)`. -/
theorem hmPiola_spaceGrad_flowGrad_entry
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2)
    (i p r : Fin 2) :
    spaceGrad (fun y => I.flowGrad hΦ m l t y p r) x i =
      ∑ q : Fin 2, gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
        xFlowHess I hΦ m l t (I.xFlowInv hΦ m l t x) r p q := by
  have hXs := contDiff_xFlow_slice I hΦ m l t
  have hYs := contDiff_xFlowInv_slice I hΦ m l t
  have hXp : ContDiff ℝ ∞ (fun u => I.xFlow hΦ m l t u r) :=
    (contDiff_apply ℝ ℝ r).comp hXs
  have hfpj : ContDiff ℝ ∞
      (fun w => spaceGrad (fun u => I.xFlow hΦ m l t u r) w p) :=
    Integration.contDiff_spaceGrad_component hXp p
  have hYx := (hYs.differentiable (by simp) x).hasFDerivAt
  have hfx : HasFDerivAt
      (fun w => spaceGrad (fun u => I.xFlow hΦ m l t u r) w p)
      (fderiv ℝ (fun w => spaceGrad (fun u => I.xFlow hΦ m l t u r) w p)
        (I.xFlowInv hΦ m l t x)) (I.xFlowInv hΦ m l t x) :=
    ((hfpj.differentiable (by simp)) _).hasFDerivAt
  have hchain := spaceGrad_comp_eq_gradMatrix_mul hfx hYx i
  have hfun : (fun y => I.flowGrad hΦ m l t y p r) =
      fun y => (fun w => spaceGrad (fun u => I.xFlow hΦ m l t u r) w p)
        (I.xFlowInv hΦ m l t y) := by
    funext y
    simp [Ingredients.flowGrad, gradMatrix, Matrix.of_apply]
  rw [hfun, hchain]
  simp only [xFlowHess]

/-- Finite weighted sums commute with the divergence. -/
theorem hmPiola_vecDiv_sum_smul {S : Finset ℤ} (c : ℤ → ℝ)
    {V : ℤ → Vec 2 → Vec 2} {x : Vec 2}
    (hV : ∀ l ∈ S, DifferentiableAt ℝ (V l) x) :
    vecDiv (fun y => ∑ l ∈ S, c l • V l y) x =
      ∑ l ∈ S, c l * vecDiv (V l) x := by
  unfold vecDiv spaceGrad
  have hcomp (i : Fin 2) (l : ℤ) (hl : l ∈ S) :
      DifferentiableAt ℝ (fun y => c l * V l y i) x := by
    have h := (ContinuousLinearMap.proj i).differentiableAt.comp x (hV l hl)
    exact (by simpa [Function.comp_def] using h : DifferentiableAt ℝ (fun y => V l y i)
        x).const_mul _
  have hi (i : Fin 2) :
      fderiv ℝ (fun y => (∑ l ∈ S, c l • V l y) i) x (basisVec i) =
        ∑ l ∈ S, c l * fderiv ℝ (fun y => V l y i) x (basisVec i) := by
    have hfun : (fun y => (∑ l ∈ S, c l • V l y) i) =
        fun y => ∑ l ∈ S, c l * V l y i := by
      funext y
      simp [Finset.sum_apply]
    rw [hfun, fderiv_fun_sum (fun l hl => hcomp i l hl)]
    simp only [sum_apply]
    refine Finset.sum_congr rfl fun l hl => ?_
    have h := (ContinuousLinearMap.proj i).differentiableAt.comp x (hV l hl)
    have hd : DifferentiableAt ℝ (fun y => V l y i) x := by
      simpa [Function.comp_def] using h
    rw [fderiv_const_mul hd]
    rfl
  simp only [hi]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]

/-- The per-`l` pulled flux `y ↦ F_lᵀ M F_l ∇T` is smooth. -/
theorem hmPiola_term_contDiff
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hT : ContDiff ℝ ∞ (T t)) :
    ContDiff ℝ ∞ (fun y =>
      (I.flowGrad hΦ m l t y).transpose.mulVec
        (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y)))) := by
  have hg := LeftJacobian.contDiff_spaceGrad_T hT
  have hF := LeftJacobian.contDiff_flowGrad_entry I hΦ m l t
  apply contDiff_pi.2
  intro i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine ContDiff.sum (fun p _ => (hF p i).mul ?_)
  refine ContDiff.sum (fun q _ => contDiff_const.mul ?_)
  refine ContDiff.sum (fun r _ => (hF q r).mul ((contDiff_pi.1 hg) r))

/-- Real arithmetic closing the pointwise Piola bound. -/
theorem HmPiolaRateCalculus.hmPiola_arith {A Q g E : ℝ} (hA : 0 ≤ A)
    (hQ : 2 ^ 19 / E * g ≤ Q) :
    4 * (4 * A * Q + 2 ^ 21 * A * g / E) ≤ 32 * A * Q := by
  have h1 : 2 ^ 21 * A * g / E = 4 * A * (2 ^ 19 / E * g) := by ring
  have h2 : 4 * A * (2 ^ 19 / E * g) ≤ 4 * A * Q :=
    mul_le_mul_of_nonneg_left hQ (by positivity)
  rw [h1]
  nlinarith

/-- Per-`l` pointwise bound for the divergence of `F_lᵀ M F_l ∇T`. -/
theorem hmPiola_vecDiv_term_abs_le
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (T : ℝ → Vec 2 → ℝ) {t : ℝ}
    (hTt : ContDiff ℝ ∞ (T t)) {E : ℝ} (hE : 0 < E) (l : ℤ)
    (hFlow : ∀ x i j, |I.flowGrad hΦ m l t x i j| ≤ 2)
    (hInv : ∀ x i j,
      |gradMatrix (fun y => I.xFlowInv hΦ m l t y) x i j| ≤ 2)
    (hHess : ∀ x p j q, |xFlowHess I hΦ m l t x p j q| ≤ 2 ^ 16 / E)
    (M : Matrix (Fin 2) (Fin 2) ℝ) {A : ℝ} (hA : ∀ i j, |M i j| ≤ A)
    (x : Vec 2) :
    |vecDiv (fun y =>
      (I.flowGrad hΦ m l t y).transpose.mulVec
        (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y)))) x| ≤
      32 * A * hmPiolaQ E T t x := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 0)
  have hT1 : ContDiff ℝ 1 (T t) := hTt.of_le (by simp)
  have hGeq (y : Vec 2) : G I hΦ m T l t y =
      (I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y) :=
    LeftJacobian.G_eq_flowGrad_mulVec_of_contDiff I hΦ m T t hT1 l y
  have hGsm (q : Fin 2) : ContDiff ℝ ∞ (fun y => G I hΦ m T l t y q) :=
    (contDiff_apply ℝ ℝ q).comp (contDiff_G I hΦ m T l hTt)
  have hFsm (p r : Fin 2) :
      ContDiff ℝ ∞ (fun y => I.flowGrad hΦ m l t y p r) :=
    LeftJacobian.contDiff_flowGrad_entry I hΦ m l t p r
  -- the components of the flux
  have hcomp (y : Vec 2) (i : Fin 2) :
      ((I.flowGrad hΦ m l t y).transpose.mulVec
        (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y)))) i =
      ∑ p : Fin 2, I.flowGrad hΦ m l t y p i *
        ∑ q : Fin 2, M p q * G I hΦ m T l t y q := by
    rw [← hGeq y]
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have hwsm (p : Fin 2) :
      ContDiff ℝ ∞ (fun y => ∑ q : Fin 2, M p q * G I hΦ m T l t y q) :=
    ContDiff.sum fun q _ => contDiff_const.mul (hGsm q)
  have hwgrad (p i : Fin 2) :
      spaceGrad (fun y => ∑ q : Fin 2, M p q * G I hΦ m T l t y q) x i =
        ∑ q : Fin 2, M p q * spaceGrad (fun y => G I hΦ m T l t y q) x i := by
    have hwq (q : Fin 2) :
        ContDiff ℝ ∞ (fun y => M p q * G I hΦ m T l t y q) :=
      contDiff_const.mul (hGsm q)
    rw [spaceGrad_sum_univ_of_differentiableAt
      (fun q => (hwq q).differentiable (by simp) x)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [spaceGrad_mul_of_differentiableAt
      (differentiableAt_const (M p q))
      ((hGsm q).differentiable (by simp) x)]
    simp [spaceGrad]
  -- bounds
  set g0 := Real.sqrt (vecNormSq (spaceGrad (T t) x)) with hg0
  have hg0nn : 0 ≤ g0 := Real.sqrt_nonneg _
  have hGbound (q : Fin 2) : |G I hΦ m T l t x q| ≤ 4 * g0 := by
    rw [hGeq x]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hq0 := hFlow x q 0
    have hq1 := hFlow x q 1
    have h0 := abs_apply_le_sqrt_vecNormSq (spaceGrad (T t) x) 0
    have h1 := abs_apply_le_sqrt_vecNormSq (spaceGrad (T t) x) 1
    calc
      _ ≤ |I.flowGrad hΦ m l t x q 0 * spaceGrad (T t) x 0| +
          |I.flowGrad hΦ m l t x q 1 * spaceGrad (T t) x 1| := abs_add_le _ _
      _ ≤ 2 * g0 + 2 * g0 := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul hq0 h0 (abs_nonneg _) (by norm_num))
          (mul_le_mul hq1 h1 (abs_nonneg _) (by norm_num))
      _ = 4 * g0 := by ring
  have hwbound (p : Fin 2) :
      |∑ q : Fin 2, M p q * G I hΦ m T l t x q| ≤ 8 * A * g0 := by
    simp only [Fin.sum_univ_two]
    calc
      _ ≤ |M p 0 * G I hΦ m T l t x 0| + |M p 1 * G I hΦ m T l t x 1| :=
        abs_add_le _ _
      _ ≤ A * (4 * g0) + A * (4 * g0) := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul (hA p 0) (hGbound 0) (abs_nonneg _) hA0)
          (mul_le_mul (hA p 1) (hGbound 1) (abs_nonneg _) hA0)
      _ = 8 * A * g0 := by ring
  have hdF (i p : Fin 2) :
      |spaceGrad (fun y => I.flowGrad hΦ m l t y p i) x i| ≤ 2 ^ 18 / E := by
    rw [hmPiola_spaceGrad_flowGrad_entry I hΦ m l t x i p i]
    calc
      _ ≤ ∑ q : Fin 2,
          |gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
            xFlowHess I hΦ m l t (I.xFlowInv hΦ m l t x) i p q| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q : Fin 2, 2 * (2 ^ 16 / E) := by
        apply Finset.sum_le_sum
        intro q _
        rw [abs_mul]
        exact mul_le_mul (hInv x i q) (hHess _ i p q)
          (abs_nonneg _) (by positivity)
      _ = _ := by simp only [Fin.sum_univ_two]; ring
  have hQge : 2 ^ 19 / E * g0 ≤ hmPiolaQ E T t x := hmPiolaQ_ge E T t x
  have hQnn : 0 ≤ hmPiolaQ E T t x := hmPiolaQ_nonneg E hE T t x
  -- the (i, p) summand
  have hsummand (i p : Fin 2) :
      |I.flowGrad hΦ m l t x p i *
          spaceGrad (fun y => ∑ q : Fin 2, M p q * G I hΦ m T l t y q) x i +
        (∑ q : Fin 2, M p q * G I hΦ m T l t x q) *
          spaceGrad (fun y => I.flowGrad hΦ m l t y p i) x i| ≤
        4 * A * hmPiolaQ E T t x + 2 ^ 21 * A * g0 / E := by
    have hfirst : |I.flowGrad hΦ m l t x p i *
        spaceGrad (fun y => ∑ q : Fin 2, M p q * G I hΦ m T l t y q) x i| ≤
        4 * A * hmPiolaQ E T t x := by
      rw [hwgrad, abs_mul]
      have hs : |∑ q : Fin 2, M p q * spaceGrad (fun y => G I hΦ m T l t y q) x i| ≤
          2 * A * hmPiolaQ E T t x := by
        simp only [Fin.sum_univ_two]
        calc
          _ ≤ |M p 0 * spaceGrad (fun y => G I hΦ m T l t y 0) x i| +
              |M p 1 * spaceGrad (fun y => G I hΦ m T l t y 1) x i| :=
            abs_add_le _ _
          _ ≤ A * hmPiolaQ E T t x + A * hmPiolaQ E T t x := by
            rw [abs_mul, abs_mul]
            exact add_le_add
              (mul_le_mul (hA p 0)
                (hmPiola_spaceGrad_G_abs_le I hΦ T hTt hE l hFlow hInv hHess x i 0)
                (abs_nonneg _) hA0)
              (mul_le_mul (hA p 1)
                (hmPiola_spaceGrad_G_abs_le I hΦ T hTt hE l hFlow hInv hHess x i 1)
                (abs_nonneg _) hA0)
          _ = 2 * A * hmPiolaQ E T t x := by ring
      calc
        _ ≤ 2 * (2 * A * hmPiolaQ E T t x) :=
          mul_le_mul (hFlow x p i) hs (abs_nonneg _) (by norm_num)
        _ = 4 * A * hmPiolaQ E T t x := by ring
    have hsecond : |(∑ q : Fin 2, M p q * G I hΦ m T l t x q) *
        spaceGrad (fun y => I.flowGrad hΦ m l t y p i) x i| ≤
        2 ^ 21 * A * g0 / E := by
      rw [abs_mul]
      calc
        _ ≤ (8 * A * g0) * (2 ^ 18 / E) :=
          mul_le_mul (hwbound p) (hdF i p) (abs_nonneg _) (by positivity)
        _ = 2 ^ 21 * A * g0 / E := by ring
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  -- divergence
  have hdiv : vecDiv (fun y =>
      (I.flowGrad hΦ m l t y).transpose.mulVec
        (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y)))) x =
      ∑ i : Fin 2, ∑ p : Fin 2,
        (I.flowGrad hΦ m l t x p i *
            spaceGrad (fun y => ∑ q : Fin 2, M p q * G I hΦ m T l t y q) x i +
          (∑ q : Fin 2, M p q * G I hΦ m T l t x q) *
            spaceGrad (fun y => I.flowGrad hΦ m l t y p i) x i) := by
    unfold vecDiv
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfun : (fun y => ((I.flowGrad hΦ m l t y).transpose.mulVec
        (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y)))) i) =
        fun y => ∑ p : Fin 2, I.flowGrad hΦ m l t y p i *
          ∑ q : Fin 2, M p q * G I hΦ m T l t y q := by
      funext y
      exact hcomp y i
    rw [hfun, spaceGrad_sum_univ_of_differentiableAt
      (fun p => ((hFsm p i).mul (hwsm p)).differentiable (by simp) x)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [spaceGrad_mul_of_differentiableAt
      ((hFsm p i).differentiable (by simp) x)
      ((hwsm p).differentiable (by simp) x)]
  rw [hdiv]
  calc
    _ ≤ ∑ i : Fin 2, |∑ p : Fin 2,
        (I.flowGrad hΦ m l t x p i *
            spaceGrad (fun y => ∑ q : Fin 2, M p q * G I hΦ m T l t y q) x i +
          (∑ q : Fin 2, M p q * G I hΦ m T l t x q) *
            spaceGrad (fun y => I.flowGrad hΦ m l t y p i) x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 2, ∑ p : Fin 2,
        (4 * A * hmPiolaQ E T t x + 2 ^ 21 * A * g0 / E) := by
      refine Finset.sum_le_sum fun i _ => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact Finset.sum_le_sum fun p _ => hsummand i p
    _ = 4 * (4 * A * hmPiolaQ E T t x + 2 ^ 21 * A * g0 / E) := by
      simp only [Fin.sum_univ_two]
      ring
    _ ≤ 32 * A * hmPiolaQ E T t x := HmPiolaRateCalculus.hmPiola_arith hA0 hQge

/-- Pointwise bound for the divergence of the full `ξ̂`-weighted pulled gap flux. -/
theorem hmPiola_vecDiv_tsum_abs_le
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (T : ℝ → Vec 2 → ℝ) {t : ℝ}
    (hTt : ContDiff ℝ ∞ (T t)) {E : ℝ} (hE : 0 < E)
    (hFlow : ∀ l : ℤ, I.hatXiML m l t ≠ 0 → ∀ x i j,
      |I.flowGrad hΦ m l t x i j| ≤ 2)
    (hInv : ∀ l : ℤ, I.hatXiML m l t ≠ 0 → ∀ x i j,
      |gradMatrix (fun y => I.xFlowInv hΦ m l t y) x i j| ≤ 2)
    (hHess : ∀ l : ℤ, I.hatXiML m l t ≠ 0 → ∀ x p j q,
      |xFlowHess I hΦ m l t x p j q| ≤ 2 ^ 16 / E)
    (M : Matrix (Fin 2) (Fin 2) ℝ) {A : ℝ} (hA : ∀ i j, |M i j| ≤ A)
    (x : Vec 2) :
    |vecDiv (fun y => ∑' l : ℤ, I.hatXiML m l t •
      ((I.flowGrad hΦ m l t y).transpose.mulVec
        (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y))))) x| ≤
      32 * A * hmPiolaQ E T t x := by
  classical
  set S := (I.hatXiML_support_finite hm t).toFinset with hS
  have hmem (l : ℤ) (hl : l ∈ S) : I.hatXiML m l t ≠ 0 :=
    (I.hatXiML_support_finite hm t).mem_toFinset.mp hl
  have hfun : (fun y => ∑' l : ℤ, I.hatXiML m l t •
      ((I.flowGrad hΦ m l t y).transpose.mulVec
        (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y))))) =
      fun y => ∑ l ∈ S, I.hatXiML m l t •
        ((I.flowGrad hΦ m l t y).transpose.mulVec
          (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y)))) := by
    funext y
    exact LeftJacobian.tsum_hatXiML_smul_eq_sum I m hm t _
  have hdiffl (l : ℤ) : DifferentiableAt ℝ (fun y =>
      (I.flowGrad hΦ m l t y).transpose.mulVec
        (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y)))) x :=
    (hmPiola_term_contDiff I hΦ m l M T hTt).differentiable (by simp) x
  rw [hfun, hmPiola_vecDiv_sum_smul (S := S)
    (fun l => I.hatXiML m l t) (fun l _ => hdiffl l)]
  have hw : ∑ l ∈ S, I.hatXiML m l t = 1 := LeftJacobian.sum_hatXiML_support I m hm t
  have hwnn (l : ℤ) : 0 ≤ I.hatXiML m l t :=
    (Infra.Ingredients.hatXiML_mem_Icc I hm l t).1
  calc
    _ ≤ ∑ l ∈ S, |I.hatXiML m l t * vecDiv (fun y =>
        (I.flowGrad hΦ m l t y).transpose.mulVec
          (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y)))) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ S, I.hatXiML m l t * (32 * A * hmPiolaQ E T t x) := by
      refine Finset.sum_le_sum fun l hl => ?_
      rw [abs_mul, abs_of_nonneg (hwnn l)]
      exact mul_le_mul_of_nonneg_left
        (hmPiola_vecDiv_term_abs_le I hΦ T hTt hE l (hFlow l (hmem l hl))
          (hInv l (hmem l hl)) (hHess l (hmem l hl)) M hA x) (hwnn l)
    _ = 32 * A * hmPiolaQ E T t x := by rw [← Finset.sum_mul, hw, one_mul]

end AVenhance.Infra.Section5.Contracts

end
