/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelClassical

/-!
# The full Euclidean heat Hessian

The earlier heat-kernel development realized and estimated the diagonal
coordinate derivatives.  A genuine Frechet second derivative also needs the
mixed entries.  This file introduces the uniform `(j,k)` Hessian kernel and
proves its analytic foundation: integrability, zero total mass, cancellation,
and the spatial Holder gain with the correct parabolic homogeneity.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- The `(j,k)` entry of the Euclidean heat-kernel Hessian. -/
def heatHessianKernelEntryND {n : ℕ} (t : ℝ) (z : Fin n → ℝ)
    (j k : Fin n) : ℝ :=
  heatKernelND t z *
    (z j * z k / (4 * t ^ 2) - if j = k then 1 / (2 * t) else 0)

@[simp] theorem heatHessianKernelEntryND_diag {n : ℕ} (t : ℝ)
    (z : Fin n → ℝ) (k : Fin n) :
    heatHessianKernelEntryND t z k k =
      heatKernelND t z * (z k ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
  simp [heatHessianKernelEntryND, pow_two]

theorem heatHessianKernelEntryND_offdiag {n : ℕ} (t : ℝ)
    (z : Fin n → ℝ) {j k : Fin n} (hjk : j ≠ k) :
    heatHessianKernelEntryND t z j k =
      heatKernelND t z * (z j * z k / (4 * t ^ 2)) := by
  simp [heatHessianKernelEntryND, hjk]

/-- The mixed kernel is dominated by the sum of two positive diagonal
majorants.  This deliberately harmless factor-two estimate lets all existing
fractional Gaussian-moment calculations be reused. -/
lemma abs_heatHessianKernelEntryND_offdiag_le {n : ℕ} {t : ℝ} (ht : 0 < t)
    (z : Fin n → ℝ) {j k : Fin n} (hjk : j ≠ k) :
    |heatHessianKernelEntryND t z j k| ≤
      heatKernelND t z * (z j ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) +
      heatKernelND t z * (z k ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) := by
  rw [heatHessianKernelEntryND_offdiag t z hjk, abs_mul,
    abs_of_nonneg (heatKernelND_nonneg ht z), abs_div,
    abs_mul, abs_of_pos (show 0 < 4 * t ^ 2 by positivity)]
  have hsq : |z j| * |z k| ≤ z j ^ 2 + z k ^ 2 := by
    nlinarith [sq_nonneg (|z j| - |z k|), sq_abs (z j), sq_abs (z k),
      abs_nonneg (z j), abs_nonneg (z k)]
  have hK : 0 ≤ heatKernelND t z := heatKernelND_nonneg ht z
  have hden : 0 < 4 * t ^ 2 := by positivity
  calc
    heatKernelND t z * (|z j| * |z k| / (4 * t ^ 2)) ≤
        heatKernelND t z * ((z j ^ 2 + z k ^ 2) / (4 * t ^ 2)) := by
      gcongr
    _ ≤ heatKernelND t z * (z j ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) +
        heatKernelND t z * (z k ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) := by
      have hi : 0 ≤ 1 / (2 * t) := by positivity
      have heqL : heatKernelND t z * ((z j ^ 2 + z k ^ 2) / (4 * t ^ 2)) =
          heatKernelND t z * (z j ^ 2 / (4 * t ^ 2)) +
          heatKernelND t z * (z k ^ 2 / (4 * t ^ 2)) := by ring
      rw [heqL]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hi) hK)
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hi) hK)

/-- Every entry of the heat-kernel Hessian is integrable. -/
lemma integrable_heatHessianKernelEntryND {n : ℕ} {t : ℝ} (ht : 0 < t)
    (j k : Fin n) : Integrable (fun z : Fin n → ℝ =>
      heatHessianKernelEntryND t z j k) := by
  by_cases hjk : j = k
  · subst j
    simpa only [heatHessianKernelEntryND_diag] using
      integrable_secondDeriv_coord_heatKernelND ht k
  · let M : (Fin n → ℝ) → ℝ := fun z =>
      heatKernelND t z * (z j ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) +
      heatKernelND t z * (z k ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
    have hMi : Integrable M := by
      exact (integrable_heatKernelND_mul_sq_coord_add_inv ht j).add
        (integrable_heatKernelND_mul_sq_coord_add_inv ht k)
    refine hMi.mono' ?_ (Filter.Eventually.of_forall (fun z => ?_))
    · exact ((continuous_heatKernelND t).mul (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact abs_heatHessianKernelEntryND_offdiag_le ht z hjk

/-- The signed first moment of the one-dimensional heat kernel vanishes. -/
lemma integral_mul_heatKernel1D_eq_zero {t : ℝ} (ht : 0 < t) :
    (∫ z : ℝ, z * heatKernel1D t z) = 0 := by
  let g : ℝ → ℝ := fun z => z * heatKernel1D t z
  have hodd : ∀ z, g (-z) = -g z := by
    intro z
    simp only [g, heatKernel1D_apply, neg_sq]
    ring
  have hsame : (∫ z, g (-z)) = ∫ z, g z := integral_neg_eq_self g volume
  have hneg : (∫ z, g (-z)) = -∫ z, g z := by
    rw [show (∫ z, g (-z)) = ∫ z, -g z from
      integral_congr_ae (Filter.Eventually.of_forall hodd), integral_neg]
  linarith

/-- A genuinely mixed Hessian entry has zero total mass. -/
theorem integral_heatHessianKernelEntryND_eq_zero_of_ne {n : ℕ} {t : ℝ}
    (ht : 0 < t) {j k : Fin n} (hjk : j ≠ k) :
    (∫ z : Fin n → ℝ, heatHessianKernelEntryND t z j k) = 0 := by
  classical
  let F : Fin n → ℝ → ℝ := fun i a =>
    if i = j then a * heatKernel1D t a
    else if i = k then a * heatKernel1D t a
    else heatKernel1D t a
  have hp : (fun z : Fin n → ℝ => heatHessianKernelEntryND t z j k) =
      fun z => (1 / (4 * t ^ 2)) * ∏ i, F i (z i) := by
    funext z
    rw [heatHessianKernelEntryND_offdiag t z hjk, heatKernelND_apply]
    have hFi : ∀ i, F i (z i) =
        (if i = j then z j else 1) * (if i = k then z k else 1) *
          heatKernel1D t (z i) := by
      intro i
      by_cases hij : i = j
      · subst i
        simp [F, hjk]
      · by_cases hik : i = k
        · subst i
          simp [F, hij]
        · simp [F, hij, hik]
    rw [Finset.prod_congr rfl (fun i _ => hFi i),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp
    ring
  rw [hp, integral_const_mul, integral_fin_nat_prod_volume_eq_prod]
  have hjzero : (∫ a : ℝ, F j a) = 0 := by
    simp only [F, if_pos]
    exact integral_mul_heatKernel1D_eq_zero ht
  rw [Finset.prod_eq_zero (Finset.mem_univ j) hjzero, mul_zero]

/-- Every heat Hessian entry has zero total mass. -/
theorem integral_heatHessianKernelEntryND_eq_zero {n : ℕ} {t : ℝ}
    (ht : 0 < t) (j k : Fin n) :
    (∫ z : Fin n → ℝ, heatHessianKernelEntryND t z j k) = 0 := by
  by_cases hjk : j = k
  · subst j
    simpa only [heatHessianKernelEntryND_diag] using
      integral_secondDeriv_coord_heatKernelND_eq_zero ht k
  · exact integral_heatHessianKernelEntryND_eq_zero_of_ne ht hjk

/-- Translation-invariant zero-mass identity for every Hessian entry. -/
theorem integral_heatHessianKernelEntryND_sub_eq_zero {n : ℕ} {t : ℝ}
    (ht : 0 < t) (j k : Fin n) (x : Fin n → ℝ) :
    (∫ y : Fin n → ℝ, heatHessianKernelEntryND t (x - y) j k) = 0 := by
  rw [integral_sub_left_eq_self
    (fun z : Fin n → ℝ => heatHessianKernelEntryND t z j k) volume x]
  exact integral_heatHessianKernelEntryND_eq_zero ht j k

/-- The shifted Hessian entry times bounded measurable data is integrable. -/
lemma integrable_heatHessianKernelEntryND_sub_mul {n : ℕ} {t : ℝ}
    (ht : 0 < t) (j k : Fin n) {f : (Fin n → ℝ) → ℝ} {C : ℝ}
    (x : Fin n → ℝ) (hfm : AEStronglyMeasurable f)
    (hfb : ∀ y, ‖f y‖ ≤ C) :
    Integrable (fun y : Fin n → ℝ =>
      heatHessianKernelEntryND t (x - y) j k * f y) := by
  exact ((integrable_heatHessianKernelEntryND ht j k).comp_sub_left x).mul_bdd
    hfm (Filter.Eventually.of_forall hfb)

/-- Hessian cancellation replaces the datum by its increment. -/
theorem heatHessianKernelEntryND_convolution_eq_increment {n : ℕ} {t : ℝ}
    (ht : 0 < t) {f : (Fin n → ℝ) → ℝ} {C : ℝ}
    (x : Fin n → ℝ) (j k : Fin n) (hfm : AEStronglyMeasurable f)
    (hfb : ∀ y, ‖f y‖ ≤ C) :
    (∫ y : Fin n → ℝ, heatHessianKernelEntryND t (x - y) j k * f y) =
      ∫ y : Fin n → ℝ,
        heatHessianKernelEntryND t (x - y) j k * (f y - f x) := by
  let K : (Fin n → ℝ) → ℝ := fun y =>
    heatHessianKernelEntryND t (x - y) j k
  have hK : Integrable K := (integrable_heatHessianKernelEntryND ht j k).comp_sub_left x
  have hKf : Integrable (fun y => K y * f y) := hK.mul_bdd hfm
    (Filter.Eventually.of_forall hfb)
  have hKc : Integrable (fun y => K y * f x) := hK.mul_const (f x)
  have hpoint : (fun y => K y * (f y - f x)) =
      fun y => K y * f y - K y * f x := by
    funext y
    ring
  change (∫ y, K y * f y) = ∫ y, K y * (f y - f x)
  rw [hpoint, integral_sub hKf hKc]
  have hc : (∫ y, K y * f x) = f x * ∫ y, K y := by
    calc
      _ = ∫ y, f x * K y := by congr 1; funext y; ring
      _ = _ := by rw [integral_const_mul]
  rw [hc]
  have hzero : (∫ y, K y) = 0 := by
    simpa only [K] using integral_heatHessianKernelEntryND_sub_eq_zero ht j k x
  rw [hzero]
  ring

/-- A weighted mixed Hessian kernel is controlled by the sum of the two
corresponding positive diagonal majorants. -/
lemma integrable_abs_coord_rpow_mul_abs_heatHessianKernelEntryND
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (ell j k : Fin n) :
    Integrable (fun z : Fin n → ℝ => |z ell| ^ r *
      |heatHessianKernelEntryND t z j k|) := by
  by_cases hjk : j = k
  · subst j
    simpa only [heatHessianKernelEntryND_diag] using
      integrable_abs_coord_rpow_mul_abs_secondDeriv_heatKernelND ht hr ell k
  · let M : (Fin n → ℝ) → ℝ := fun z => |z ell| ^ r *
      (heatKernelND t z * (z j ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) +
       heatKernelND t z * (z k ^ 2 / (4 * t ^ 2) + 1 / (2 * t)))
    have hMi : Integrable M := by
      have hj := integrable_abs_coord_rpow_secondDeriv_majorantND ht hr ell j
      have hk := integrable_abs_coord_rpow_secondDeriv_majorantND ht hr ell k
      have heq : M = fun z : Fin n → ℝ =>
          (|z ell| ^ r * heatKernelND t z *
            (z j ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) +
          (|z ell| ^ r * heatKernelND t z *
            (z k ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) := by
        funext z
        simp only [M]
        ring
      rw [heq]
      exact hj.add hk
    refine hMi.mono' ?_ (Filter.Eventually.of_forall (fun z => ?_))
    · exact (((continuous_abs.comp (continuous_apply ell)).rpow_const
        (fun _ => Or.inr hr)).mul
        ((continuous_heatKernelND t).mul (by fun_prop)).abs).aestronglyMeasurable
    · rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) r) (abs_nonneg _))]
      exact mul_le_mul_of_nonneg_left
        (abs_heatHessianKernelEntryND_offdiag_le ht z hjk)
        (Real.rpow_nonneg (abs_nonneg _) r)

/-- Time-independent Gaussian constant controlling one full Hessian entry. -/
def heatHessianEntryHolderMoment (n : ℕ) (r : ℝ) (j k : Fin n) : ℝ :=
  heatHessianHolderMoment n r j + heatHessianHolderMoment n r k

lemma heatHessianEntryHolderMoment_nonneg (n : ℕ) (r : ℝ) (j k : Fin n) :
    0 ≤ heatHessianEntryHolderMoment n r j k :=
  add_nonneg (heatHessianHolderMoment_nonneg n r j)
    (heatHessianHolderMoment_nonneg n r k)

/-- Full-entry Euclidean spatial Schauder estimate.  The diagonal case reuses
the sharper earlier theorem; the mixed case is dominated by two positive
diagonal majorants. -/
theorem abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    {f : (Fin n → ℝ) → ℝ} {C H : ℝ} (hH : 0 ≤ H)
    (x : Fin n → ℝ) (j k : Fin n)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C)
    (hholder : ∀ y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    |∫ y : Fin n → ℝ,
      heatHessianKernelEntryND t (x - y) j k * f y| ≤
      H * t ^ (-1 + r / 2) * heatHessianEntryHolderMoment n r j k := by
  classical
  by_cases hjk : j = k
  · subst j
    have h := abs_secondDeriv_heatKernelND_convolution_le_of_coordHolder_scale
      ht hr hH x k hfm hfb hholder
    calc
      |∫ y : Fin n → ℝ,
          heatHessianKernelEntryND t (x - y) k k * f y| ≤
          H * t ^ (-1 + r / 2) * heatHessianHolderMoment n r k := by
        simpa only [heatHessianKernelEntryND_diag] using h
      _ ≤ H * t ^ (-1 + r / 2) * heatHessianHolderMoment n r k +
          H * t ^ (-1 + r / 2) * heatHessianHolderMoment n r k := by
        exact le_add_of_nonneg_right
          (mul_nonneg (mul_nonneg hH (Real.rpow_nonneg ht.le _))
            (heatHessianHolderMoment_nonneg n r k))
      _ = H * t ^ (-1 + r / 2) * heatHessianEntryHolderMoment n r k k := by
        simp only [heatHessianEntryHolderMoment]
        ring
  · let K : (Fin n → ℝ) → ℝ := fun y =>
      heatHessianKernelEntryND t (x - y) j k
    let W : Fin n → (Fin n → ℝ) → ℝ := fun ell y => |(x - y) ell| ^ r * |K y|
    have hWi : ∀ ell, Integrable (W ell) := by
      intro ell
      have h :=
        (integrable_abs_coord_rpow_mul_abs_heatHessianKernelEntryND ht hr ell j k).comp_sub_left x
      simpa only [W, K] using h
    have hsum : Integrable (fun y => ∑ ell : Fin n, W ell y) :=
      integrable_finset_sum Finset.univ (fun ell _ => hWi ell)
    have hdom : Integrable (fun y => H * ∑ ell : Fin n, W ell y) := hsum.const_mul H
    rw [heatHessianKernelEntryND_convolution_eq_increment ht x j k hfm hfb]
    change |∫ y, K y * (f y - f x)| ≤ _
    calc
      _ ≤ ∫ y, H * ∑ ell : Fin n, W ell y := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hdom
          (Filter.Eventually.of_forall (fun y => ?_))
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |K y| * |f y - f x| ≤
              |K y| * (H * ∑ ell : Fin n, |(x - y) ell| ^ r) :=
            mul_le_mul_of_nonneg_left (hholder y) (abs_nonneg _)
          _ = H * ∑ ell : Fin n, W ell y := by
            calc
              |K y| * (H * ∑ ell : Fin n, |(x - y) ell| ^ r) =
                  H * (|K y| * ∑ ell : Fin n, |(x - y) ell| ^ r) := by ring
              _ = H * ∑ ell : Fin n, |K y| * |(x - y) ell| ^ r := by
                rw [Finset.mul_sum]
              _ = H * ∑ ell : Fin n, W ell y := by
                congr 1
                apply Finset.sum_congr rfl
                intro ell _
                simp only [W]
                ring
      _ = H * ∑ ell : Fin n, ∫ y, W ell y := by
        rw [integral_const_mul, integral_finset_sum Finset.univ (fun ell _ => hWi ell)]
      _ ≤ H * t ^ (-1 + r / 2) * heatHessianEntryHolderMoment n r j k := by
        have hterm : ∀ ell : Fin n, (∫ y, W ell y) ≤
            t ^ (-1 + r / 2) *
              ((if ell = j then gaussianAbsMoment (r + 2) / 4 + gaussianAbsMoment r / 2
                else gaussianAbsMoment r) +
               (if ell = k then gaussianAbsMoment (r + 2) / 4 + gaussianAbsMoment r / 2
                else gaussianAbsMoment r)) := by
          intro ell
          let Mj : (Fin n → ℝ) → ℝ := fun z => |z ell| ^ r * heatKernelND t z *
            (z j ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
          let Mk : (Fin n → ℝ) → ℝ := fun z => |z ell| ^ r * heatKernelND t z *
            (z k ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
          have hMji := integrable_abs_coord_rpow_secondDeriv_majorantND ht hr ell j
          have hMki := integrable_abs_coord_rpow_secondDeriv_majorantND ht hr ell k
          have htrans : (∫ y, W ell y) = ∫ z : Fin n → ℝ,
              |z ell| ^ r * |heatHessianKernelEntryND t z j k| := by
            rw [integral_sub_left_eq_self
              (fun z : Fin n → ℝ => |z ell| ^ r *
                |heatHessianKernelEntryND t z j k|) volume x]
          rw [htrans]
          calc
            _ ≤ ∫ z : Fin n → ℝ, (Mj z + Mk z) := by
              refine integral_mono
                (integrable_abs_coord_rpow_mul_abs_heatHessianKernelEntryND ht hr ell j k)
                (hMji.add hMki) (fun z => ?_)
              dsimp only [Mj, Mk]
              have hp := mul_le_mul_of_nonneg_left
                (abs_heatHessianKernelEntryND_offdiag_le ht z hjk)
                (Real.rpow_nonneg (abs_nonneg (z ell)) r)
              simpa only [mul_add, mul_assoc] using hp
            _ = (∫ z, Mj z) + ∫ z, Mk z := integral_add hMji hMki
            _ = t ^ (-1 + r / 2) *
                ((if ell = j then gaussianAbsMoment (r + 2) / 4 + gaussianAbsMoment r / 2
                  else gaussianAbsMoment r) +
                 (if ell = k then gaussianAbsMoment (r + 2) / 4 + gaussianAbsMoment r / 2
                  else gaussianAbsMoment r)) := by
              have hjval : (∫ z, Mj z) = t ^ (-1 + r / 2) *
                  (if ell = j then gaussianAbsMoment (r + 2) / 4 + gaussianAbsMoment r / 2
                   else gaussianAbsMoment r) := by
                by_cases helj : ell = j
                · subst ell
                  simp only [Mj, if_pos]
                  rw [integral_abs_coord_rpow_secondDeriv_majorantND_diag_eq ht hr j,
                    diagonal_hessianMoment_scale ht]
                · simp only [Mj, if_neg helj]
                  rw [integral_abs_coord_rpow_secondDeriv_majorantND_offdiag_eq ht hr ell j helj,
                    offdiagonal_hessianMoment_scale ht]
              have hkval : (∫ z, Mk z) = t ^ (-1 + r / 2) *
                  (if ell = k then gaussianAbsMoment (r + 2) / 4 + gaussianAbsMoment r / 2
                   else gaussianAbsMoment r) := by
                by_cases helk : ell = k
                · subst ell
                  simp only [Mk, if_pos]
                  rw [integral_abs_coord_rpow_secondDeriv_majorantND_diag_eq ht hr k,
                    diagonal_hessianMoment_scale ht]
                · simp only [Mk, if_neg helk]
                  rw [integral_abs_coord_rpow_secondDeriv_majorantND_offdiag_eq ht hr ell k helk,
                    offdiagonal_hessianMoment_scale ht]
              rw [hjval, hkval]
              ring
        calc
          H * ∑ ell : Fin n, ∫ y, W ell y ≤
              H * ∑ ell : Fin n, t ^ (-1 + r / 2) *
                ((if ell = j then gaussianAbsMoment (r + 2) / 4 + gaussianAbsMoment r / 2
                  else gaussianAbsMoment r) +
                 (if ell = k then gaussianAbsMoment (r + 2) / 4 + gaussianAbsMoment r / 2
                  else gaussianAbsMoment r)) := by
            gcongr with ell
            exact hterm ell
          _ = H * t ^ (-1 + r / 2) * heatHessianEntryHolderMoment n r j k := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            simp only [heatHessianEntryHolderMoment, heatHessianHolderMoment]
            ring

/-! ## Actual mixed differentiation -/

/-- Product-Gaussian envelope for differentiating the `k`-gradient in a
different coordinate `j`. -/
lemma integrable_gaussianFirstPairEnvelope_erase_prod {n : ℕ} {t : ℝ}
    (ht : 0 < t) (x : Fin n → ℝ) {j k : Fin n} (hjk : j ≠ k) :
    Integrable (fun y : Fin n → ℝ =>
      ((1 + |y j - x j|) * Real.exp (-(y j - x j) ^ 2 / (8 * t))) *
        |y k - x k| *
        ∏ i ∈ Finset.univ.erase j, heatKernel1D t (x i - y i)) := by
  classical
  have hb8 : 0 < (8 * t)⁻¹ := by positivity
  have h0 : Integrable (fun w : ℝ => Real.exp (-(8 * t)⁻¹ * w ^ 2)) :=
    integrable_exp_neg_mul_sq hb8
  have h1 : Integrable (fun w : ℝ => w ^ (1 : ℝ) *
      Real.exp (-(8 * t)⁻¹ * w ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hb8 (by norm_num)
  have hbase : Integrable (fun w : ℝ =>
      (1 + |w|) * Real.exp (-w ^ 2 / (8 * t))) := by
    have hsum := h0.add h1.abs
    refine hsum.congr (Filter.Eventually.of_forall (fun w => ?_))
    simp only [Pi.add_apply, Real.rpow_one]
    have he : -(8 * t)⁻¹ * w ^ 2 = -w ^ 2 / (8 * t) := by
      rw [neg_div, div_eq_inv_mul]
      ring
    rw [he, abs_mul, abs_of_pos (Real.exp_pos _)]
    ring
  have hjint : Integrable (fun a : ℝ =>
      (1 + |a - x j|) * Real.exp (-(a - x j) ^ 2 / (8 * t))) :=
    hbase.comp_sub_right (x j)
  have hkint : Integrable (fun a : ℝ =>
      |a - x k| * heatKernel1D t (x k - a)) := by
    have h := (integrable_abs_mul_heatKernel1D ht).comp_sub_right (x k)
    convert h using 1
    funext a
    rw [show x k - a = -(a - x k) by ring, heatKernel1D_neg]
  let F : Fin n → ℝ → ℝ := fun i a =>
    if i = j then
      (1 + |a - x j|) * Real.exp (-(a - x j) ^ 2 / (8 * t))
    else if i = k then |a - x k| * heatKernel1D t (x k - a)
    else heatKernel1D t (x i - a)
  have hp : (fun y : Fin n → ℝ =>
      ((1 + |y j - x j|) * Real.exp (-(y j - x j) ^ 2 / (8 * t))) *
        |y k - x k| *
        ∏ i ∈ Finset.univ.erase j, heatKernel1D t (x i - y i)) =
      fun y => ∏ i, F i (y i) := by
    funext y
    rw [(Finset.mul_prod_erase Finset.univ (fun i => F i (y i))
      (Finset.mem_univ j)).symm]
    have hFj : F j (y j) =
        (1 + |y j - x j|) * Real.exp (-(y j - x j) ^ 2 / (8 * t)) := by
      simp [F]
    rw [hFj]
    have hrest : (∏ i ∈ Finset.univ.erase j, F i (y i)) =
        |y k - x k| * ∏ i ∈ Finset.univ.erase j,
          heatKernel1D t (x i - y i) := by
      have hFi : ∀ i ∈ Finset.univ.erase j, F i (y i) =
          (if i = k then |y k - x k| else 1) *
            heatKernel1D t (x i - y i) := by
        intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        by_cases hik : i = k
        · subst i
          simp [F, hjk.symm]
        · simp [F, hij, hik]
      rw [Finset.prod_congr rfl hFi, Finset.prod_mul_distrib,
        Finset.prod_ite_eq']
      simp [Finset.mem_erase, hjk.symm]
    rw [hrest]
    ring
  have hvol : (volume : Measure (Fin n → ℝ)) = Measure.pi (fun _ => volume) := by
    rw [volume_pi]
  rw [hp, hvol]
  refine Integrable.fin_nat_prod (f := F) (fun i => ?_)
  by_cases hij : i = j
  · subst i
    simpa [F] using hjint
  · by_cases hik : i = k
    · subst i
      simpa [F, hjk.symm] using hkint
    · simpa [F, hij, hik] using (integrable_heatKernel1D ht).comp_sub_left (x i)

/-- For distinct coordinates, the coordinate-gradient convolution is
differentiable in the transverse coordinate and its derivative is the mixed
heat Hessian convolution. -/
theorem hasDerivAt_heatSemigroupND_coordGradient_offdiag
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ)
    {j k : Fin n} (hjk : j ≠ k)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    HasDerivAt
      (fun a => ∫ y : Fin n → ℝ,
        (heatKernelND t (Function.update x j a - y) *
          (-((Function.update x j a - y) k) / (2 * t))) * f y)
      (∫ y : Fin n → ℝ,
        heatHessianKernelEntryND t (x - y) j k * f y) (x j) := by
  classical
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have h4t2 : (0 : ℝ) < 4 * t ^ 2 := by positivity
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hfb 0)
  let F : ℝ → (Fin n → ℝ) → ℝ := fun a y =>
    (heatKernelND t (Function.update x j a - y) *
      (-((Function.update x j a - y) k) / (2 * t))) * f y
  let F' : ℝ → (Fin n → ℝ) → ℝ := fun a y =>
    heatKernel1D t (a - y j) * (-(a - y j) / (2 * t)) *
      (∏ i ∈ Finset.univ.erase j, heatKernel1D t ((x - y) i)) *
      (-((x - y) k) / (2 * t)) * f y
  let M : ℝ := (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
    C / (4 * t ^ 2)
  let bound : (Fin n → ℝ) → ℝ := fun y => M *
    (((1 + |y j - x j|) * Real.exp (-(y j - x j) ^ 2 / (8 * t))) *
      |y k - x k| *
      ∏ i ∈ Finset.univ.erase j, heatKernel1D t ((x - y) i))
  have hsub : ∀ (a : ℝ) (y : Fin n → ℝ),
      Function.update x j a - y = Function.update (x - y) j (a - y j) := by
    intro a y
    funext i
    by_cases hij : i = j
    · subst i
      simp
    · simp [Function.update_of_ne hij]
  have hkconst : ∀ (a : ℝ) (y : Fin n → ℝ),
      (Function.update x j a - y) k = (x - y) k := by
    intro a y
    simp [Function.update_of_ne hjk.symm]
  have hF'base : F' (x j) = fun y =>
      heatHessianKernelEntryND t (x - y) j k * f y := by
    funext y
    simp only [F']
    rw [heatHessianKernelEntryND_offdiag t (x - y) hjk,
      heatKernelND_eq_update_mul n t (x - y) j]
    simp only [Pi.sub_apply]
    ring
  have hFmeas : ∀ᶠ a in nhds (x j),
      AEStronglyMeasurable (F a) (volume : Measure (Fin n → ℝ)) := by
    filter_upwards with a
    exact ((continuous_heatKernelND_sub t (Function.update x j a)).mul
      (by fun_prop)).aestronglyMeasurable.mul hfm
  have hFint : Integrable (F (x j)) (volume : Measure (Fin n → ℝ)) := by
    have hg := integrable_deriv_coord_heatKernelND_sub_mul ht k x hfm hfb
    simpa only [F, Function.update_eq_self] using hg
  have hF'meas : AEStronglyMeasurable (F' (x j))
      (volume : Measure (Fin n → ℝ)) := by
    rw [hF'base]
    exact ((continuous_heatKernelND_sub t x).mul
      (by fun_prop)).aestronglyMeasurable.mul hfm
  have hboundint : Integrable bound (volume : Measure (Fin n → ℝ)) := by
    simpa only [bound, Pi.sub_apply] using
      (integrable_gaussianFirstPairEnvelope_erase_prod ht x hjk).const_mul M
  have hbnd : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      ∀ a ∈ Metric.ball (x j) 1, ‖F' a y‖ ≤ bound y := by
    filter_upwards with y a ha
    rw [Metric.mem_ball, Real.dist_eq] at ha
    have hale : |a - x j| ≤ 1 := ha.le
    have hax2 : (a - x j) ^ 2 ≤ 1 := by
      rw [← Real.sqrt_le_sqrt_iff (by positivity), Real.sqrt_one,
        Real.sqrt_sq_eq_abs]
      exact hale
    have hpre : 0 < (4 * π * t) ^ (-(1 : ℝ) / 2) :=
      heatKernel1D_prefactor_pos ht
    have hKj : heatKernel1D t (a - y j) ≤
        (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
          Real.exp (-(y j - x j) ^ 2 / (8 * t)) := by
      rw [heatKernel1D_apply,
        mul_assoc ((4 * π * t) ^ (-(1 : ℝ) / 2)), ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ hpre.le
      apply Real.exp_le_exp.mpr
      have hq : (a - y j) ^ 2 ≥
          (y j - x j) ^ 2 / 2 - (a - x j) ^ 2 := by
        nlinarith [sq_nonneg ((y j - x j) - 2 * (a - x j))]
      rw [← sub_nonneg]
      have he : 1 / (4 * t) + -(y j - x j) ^ 2 / (8 * t) -
          -(a - y j) ^ 2 / (4 * t) =
          (2 - ((y j - x j) ^ 2 - 2 * (a - y j) ^ 2)) / (8 * t) := by
        field_simp
        ring
      rw [he]
      apply div_nonneg _ (by positivity)
      nlinarith [hq, hax2]
    have haj : |a - y j| ≤ 1 + |y j - x j| := by
      have he : a - y j = (a - x j) + (x j - y j) := by ring
      calc
        |a - y j| ≤ |a - x j| + |x j - y j| := by
          rw [he]
          exact abs_add_le _ _
        _ ≤ 1 + |y j - x j| := by rw [abs_sub_comm (x j) (y j)]; linarith
    have hfa : |f y| ≤ C := (Real.norm_eq_abs (f y) ▸ hfb y)
    have hQ : 0 ≤ ∏ i ∈ Finset.univ.erase j,
        heatKernel1D t ((x - y) i) :=
      Finset.prod_nonneg (fun i _ => heatKernel1D_nonneg ht _)
    have hnorm : ‖F' a y‖ =
        heatKernel1D t (a - y j) * (|a - y j| / (2 * t)) *
          (∏ i ∈ Finset.univ.erase j, heatKernel1D t ((x - y) i)) *
          (|y k - x k| / (2 * t)) * |f y| := by
      simp only [F']
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_div, abs_neg, abs_div, abs_neg, abs_of_pos h2t,
        abs_of_nonneg (heatKernel1D_nonneg ht _), abs_of_nonneg hQ,
        Pi.sub_apply,
        abs_sub_comm (x k) (y k)]
    rw [hnorm]
    have hleft : heatKernel1D t (a - y j) * |a - y j| ≤
        ((4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
          Real.exp (-(y j - x j) ^ 2 / (8 * t))) *
          (1 + |y j - x j|) := by
      exact mul_le_mul hKj haj (abs_nonneg _) (by positivity)
    have hnonneg : 0 ≤ |y k - x k| *
        (∏ i ∈ Finset.univ.erase j, heatKernel1D t ((x - y) i)) :=
      mul_nonneg (abs_nonneg _) hQ
    calc
      heatKernel1D t (a - y j) * (|a - y j| / (2 * t)) *
          (∏ i ∈ Finset.univ.erase j, heatKernel1D t ((x - y) i)) *
          (|y k - x k| / (2 * t)) * |f y| ≤
        (((4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
          Real.exp (-(y j - x j) ^ 2 / (8 * t))) *
          (1 + |y j - x j|)) /
          (4 * t ^ 2) *
          ((∏ i ∈ Finset.univ.erase j, heatKernel1D t ((x - y) i)) *
            |y k - x k|) * C := by
        have hscaled := mul_le_mul_of_nonneg_right hleft
          (mul_nonneg (by positivity : 0 ≤ (4 * t ^ 2)⁻¹)
            (mul_nonneg hnonneg hCnn))
        calc
          _ = (heatKernel1D t (a - y j) * |a - y j|) *
              ((4 * t ^ 2)⁻¹ *
                (|y k - x k| *
                  ∏ i ∈ Finset.univ.erase j, heatKernel1D t ((x - y) i)) * |f y|) := by
            field_simp
            ring
          _ ≤ (((4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (1 / (4 * t)) *
              Real.exp (-(y j - x j) ^ 2 / (8 * t))) *
              (1 + |y j - x j|)) *
              ((4 * t ^ 2)⁻¹ *
                (|y k - x k| *
                  ∏ i ∈ Finset.univ.erase j, heatKernel1D t ((x - y) i)) * C) := by
            exact mul_le_mul hleft
              (mul_le_mul_of_nonneg_left hfa
                (mul_nonneg (by positivity) hnonneg))
              (by positivity) (by positivity)
          _ = _ := by field_simp
      _ = bound y := by
        simp only [bound, M]
        ring
  have hderiv : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      ∀ a ∈ Metric.ball (x j) 1,
        HasDerivAt (fun a' => F a' y) (F' a y) a := by
    filter_upwards with y a _
    have hin : HasDerivAt (fun a' : ℝ => a' - y j) 1 a := by
      simpa using (hasDerivAt_id a).sub_const (y j)
    have hker := (hasDerivAt_heatKernelND_coord_at n t ht (x - y) j
      (a - y j)).comp a hin
    rw [mul_one] at hker
    have hrewrite : (fun a' => F a' y) = fun a' =>
        heatKernelND t (Function.update (x - y) j (a' - y j)) *
          (-((x - y) k) / (2 * t)) * f y := by
      funext a'
      simp only [F, hkconst]
      rw [hsub]
    rw [hrewrite]
    simpa only [F', Function.comp_apply] using
      (hker.mul_const (-((x - y) k) / (2 * t))).mul_const (f y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Fin n → ℝ))) (F := F) (x₀ := x j)
    (bound := bound) (s := Metric.ball (x j) 1)
    (Metric.ball_mem_nhds (x j) one_pos) hFmeas hFint hF'meas hbnd
    hboundint hderiv
  have hfun : (fun a => ∫ y : Fin n → ℝ,
      (heatKernelND t (Function.update x j a - y) *
        (-((Function.update x j a - y) k) / (2 * t))) * f y) =
      fun a => ∫ y, F a y := by rfl
  rw [hfun, ← hF'base]
  exact key.2

/-- Uniform actual derivative theorem for every Hessian entry. -/
theorem hasDerivAt_heatSemigroupND_coordGradient_entry
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ)
    (j k : Fin n) (hfm : AEStronglyMeasurable f)
    (hfb : ∀ y, ‖f y‖ ≤ C) :
    HasDerivAt
      (fun a => ∫ y : Fin n → ℝ,
        (heatKernelND t (Function.update x j a - y) *
          (-((Function.update x j a - y) k) / (2 * t))) * f y)
      (∫ y : Fin n → ℝ,
        heatHessianKernelEntryND t (x - y) j k * f y) (x j) := by
  by_cases hjk : j = k
  · subst j
    simpa only [heatHessianKernelEntryND_diag] using
      hasDerivAt_heatSemigroupND_coordGradient ht x k hfm hfb
  · exact hasDerivAt_heatSemigroupND_coordGradient_offdiag ht x hjk hfm hfb

end AnalyticPDE
end RicciFlow
