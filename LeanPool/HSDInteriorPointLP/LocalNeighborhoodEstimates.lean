/-
Copyright (c) 2026 Makoto Yamashita. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Makoto Yamashita
-/

import LeanPool.HSDInteriorPointLP.NewtonSystem

/-!
# Fixed local neighborhood estimates

This file contains the local predictor/corrector estimates that are considered
fixed.  It should be edited only when the mathematical local estimates themselves
change.

Naming convention: this refactor uses `YTM` consistently.  In this development,
`YTM` refers to the Ye--Todd--Mizuno homogeneous LP / neighborhood framework used
by the proof.  Earlier mixed alternative abbreviations in comments and identifiers have been renamed
to avoid two names for the same local-estimate layer.

Lean-reading hints for beginners:
* `linarith` proves goals from linear equalities/inequalities over ordered rings.
* `nlinarith` is the nonlinear version; it can use products and squares.
* `ring` proves polynomial identities such as rearrangements of sums/products.
* `field_simp` clears denominators after you provide nonzero-denominator proofs.
-/
noncomputable section

open scoped BigOperators

namespace HSDInteriorPointLP

/-!
## Short Lean proof-command guide

The file is written for readers who know the interior-point algebra but may be new
to Lean.

* `intro` introduces an assumption or quantified variable from the current goal.
* `have h : P := by ...` proves and names an intermediate claim.
* `rcases h with ⟨...⟩` unpacks conjunctions, existentials, and structures.
* `simp only [...]` performs controlled rewriting using only the listed facts.
* `simpa [defs] using h` simplifies the goal and the type of `h`, then applies `h`.
* `linarith` closes linear real-arithmetic goals from the available hypotheses.
* `nlinarith` is the same idea for nonlinear arithmetic such as products/squares.
* `ring` proves polynomial identities over rings such as `ℝ`.
-/

/-!
# Active YTM local estimates, refactored

This file keeps only the active local estimates needed by the current skeleton.
The imported core file contains the HLP block operator, Schur-complement
complementarity arguments, and all warning-clean fixed lemmas.
-/

/-! ## Corrector-side algebra already derivable from the HSD equations -/

/-- A full corrector step preserves the homogenized complementarity gap, hence also
preserves `mu`.  This is only the gap algebra; the central-neighborhood estimate is
handled separately below. -/
theorem corrector_mu_full_step {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 1) :
    mu (addStep w d 1) = mu w := by
  unfold mu
  rw [gap_addStep_of_HSDStepDirection w d 1 1 hdir]
  ring

/-- Product identity for the vector complementarity pairs after a full corrector step. -/
theorem corrector_component_product_full_step {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 1) (i : Fin n) :
    (addStep w d 1).x i * (addStep w d 1).s i =
      mu w + d.dx i * d.ds i := by
  have hc := hdir.compl.component_eq i
  dsimp [addStep]
  calc
    (w.x i + 1 * d.dx i) * (w.s i + 1 * d.ds i)
        = w.x i * w.s i + (w.x i * d.ds i + w.s i * d.dx i)
            + d.dx i * d.ds i := by
            ring
    _ = w.x i * w.s i + (1 * mu w - w.x i * w.s i)
            + d.dx i * d.ds i := by
            rw [hc]
    _ = mu w + d.dx i * d.ds i := by
            ring

/-- Product identity for the scalar complementarity pair after a full corrector step. -/
theorem corrector_scalar_product_full_step {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 1) :
    (addStep w d 1).tau * (addStep w d 1).kappa =
      mu w + d.dtau * d.dkappa := by
  have hc := hdir.compl.scalar_eq
  dsimp [addStep]
  calc
    (w.tau + 1 * d.dtau) * (w.kappa + 1 * d.dkappa)
        = w.tau * w.kappa + (w.tau * d.dkappa + w.kappa * d.dtau)
            + d.dtau * d.dkappa := by
            ring
    _ = w.tau * w.kappa + (1 * mu w - w.tau * w.kappa)
            + d.dtau * d.dkappa := by
            rw [hc]
    _ = mu w + d.dtau * d.dkappa := by
            ring

/-- After a full corrector step, the new centrality residual is exactly the squared
norm of the second-order complementarity products. -/
theorem corrector_centerSq_full_step_eq_cross_sq {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 1) :
    centerSq (addStep w d 1).x (addStep w d 1).tau
      (addStep w d 1).s (addStep w d 1).kappa
      (mu (addStep w d 1)) =
      (∑ i : Fin n, (d.dx i * d.ds i) ^ 2) +
        (d.dtau * d.dkappa) ^ 2 := by
  have hmu := corrector_mu_full_step w d hdir
  have hsum :
      (∑ i : Fin n,
          ((addStep w d 1).x i * (addStep w d 1).s i - mu w) ^ 2) =
        ∑ i : Fin n, (d.dx i * d.ds i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    have hp := corrector_component_product_full_step w d hdir i
    simp_all
  have hscalar :
      ((addStep w d 1).tau * (addStep w d 1).kappa - mu w) ^ 2 =
        (d.dtau * d.dkappa) ^ 2 := by
    have hp := corrector_scalar_product_full_step w d hdir
    simp_all
  unfold centerSq
  simp_all


/-! ## Elementary estimates for the corrector obligation -/

/-- The homogenized dimension `n + 1` is strictly positive. -/
theorem hdim_pos (n : Nat) : 0 < hdim n := by
  unfold hdim
  have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  linarith

/-- Interior points have positive complementarity gap. -/
theorem gap_pos_of_interior {n : Nat} (w : HSState n)
    (hinterior : Interior w) : 0 < gap w := by
  rcases hinterior with ⟨hxpos, htpos, hspos, hkpos⟩
  have hdot_nonneg : 0 ≤ dot w.x w.s := by
    unfold dot
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (le_of_lt (hxpos i)) (le_of_lt (hspos i)))
  have hscalar_pos : 0 < w.tau * w.kappa := mul_pos htpos hkpos
  unfold gap hdot
  linarith

/-- Interior points have positive duality measure. -/
theorem mu_pos_of_interior {n : Nat} (w : HSState n)
    (hinterior : Interior w) : 0 < mu w := by
  unfold mu
  exact div_pos (gap_pos_of_interior w hinterior) (hdim_pos n)

/-- The skew-orthogonality part of a step direction, written as the finite sum of
second-order complementarity products. -/
theorem corrector_second_order_sum_zero {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 1) :
    (∑ i : Fin n, d.dx i * d.ds i) + d.dtau * d.dkappa = 0 := by
  simpa [hdot, dot] using hdir.skew.cross_zero

/-- Componentwise quadratic estimate obtained from the corrector linearized
complementarity equation.  This is the elementary identity
`(x Δs - s Δx)^2 = (μ - xs)^2 - 4xs ΔxΔs` together with nonnegativity of squares. -/
theorem corrector_component_second_order_upper {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 1) (i : Fin n) :
    4 * (w.x i * w.s i) * (d.dx i * d.ds i) ≤
      (mu w - w.x i * w.s i) ^ 2 := by
  have hsq : 0 ≤ (w.x i * d.ds i - w.s i * d.dx i) ^ 2 := sq_nonneg _
  have hc := hdir.compl.component_eq i
  have hident :
      (w.x i * d.ds i - w.s i * d.dx i) ^ 2 =
        (mu w - w.x i * w.s i) ^ 2 -
          4 * (w.x i * w.s i) * (d.dx i * d.ds i) := by
    calc
      (w.x i * d.ds i - w.s i * d.dx i) ^ 2
          = (w.x i * d.ds i + w.s i * d.dx i) ^ 2 -
              4 * (w.x i * w.s i) * (d.dx i * d.ds i) := by
              ring
      _ = (mu w - w.x i * w.s i) ^ 2 -
              4 * (w.x i * w.s i) * (d.dx i * d.ds i) := by
              simp_all
  nlinarith

/-- Scalar analogue of `corrector_component_second_order_upper`. -/
theorem corrector_scalar_second_order_upper {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 1) :
    4 * (w.tau * w.kappa) * (d.dtau * d.dkappa) ≤
      (mu w - w.tau * w.kappa) ^ 2 := by
  have hsq : 0 ≤ (w.tau * d.dkappa - w.kappa * d.dtau) ^ 2 := sq_nonneg _
  have hc := hdir.compl.scalar_eq
  have hident :
      (w.tau * d.dkappa - w.kappa * d.dtau) ^ 2 =
        (mu w - w.tau * w.kappa) ^ 2 -
          4 * (w.tau * w.kappa) * (d.dtau * d.dkappa) := by
    calc
      (w.tau * d.dkappa - w.kappa * d.dtau) ^ 2
          = (w.tau * d.dkappa + w.kappa * d.dtau) ^ 2 -
              4 * (w.tau * w.kappa) * (d.dtau * d.dkappa) := by
              ring
      _ = (mu w - w.tau * w.kappa) ^ 2 -
              4 * (w.tau * w.kappa) * (d.dtau * d.dkappa) := by
              simp_all
  nlinarith


/-- Extract the centrality bound from an `HSDNeighborhood`.  Keeping this as a
separate lemma prevents later proofs from repeatedly destructing the nested `And`. -/
theorem neighborhood_centerSq_le {n : Nat} (β : ℝ) (w : HSState n)
    (hneigh : HSDNeighborhood β w) :
    centerSq w.x w.tau w.s w.kappa (mu w) ≤ (β * mu w) ^ 2 := by
  exact hneigh.2.2.2

/-- A point in a central neighborhood has positive `mu`. -/
theorem mu_pos_of_neighborhood {n : Nat} (β : ℝ) (w : HSState n)
    (hneigh : HSDNeighborhood β w) :
    0 < mu w := by
  exact mu_pos_of_interior w hneigh.1

/-- Each vector complementarity product has squared deviation bounded by the whole
centrality residual. -/
theorem neighborhood_component_dev_sq_le_bound {n : Nat} (β : ℝ)
    (w : HSState n) (hneigh : HSDNeighborhood β w) (i : Fin n) :
    (mu w - w.x i * w.s i) ^ 2 ≤ (β * mu w) ^ 2 := by
  have hcenter := neighborhood_centerSq_le β w hneigh
  unfold centerSq at hcenter
  have hsingle :
      (w.x i * w.s i - mu w) ^ 2 ≤
        ∑ j : Fin n, (w.x j * w.s j - mu w) ^ 2 := by
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (w.x j * w.s j - mu w))
      (by simp)
  have hscalar_nonneg : 0 ≤ (w.tau * w.kappa - mu w) ^ 2 := sq_nonneg _
  have hsame :
      (mu w - w.x i * w.s i) ^ 2 =
        (w.x i * w.s i - mu w) ^ 2 := by
    ring
  rw [hsame]
  nlinarith

/-- The scalar complementarity product has squared deviation bounded by the whole
centrality residual. -/
theorem neighborhood_scalar_dev_sq_le_bound {n : Nat} (β : ℝ)
    (w : HSState n) (hneigh : HSDNeighborhood β w) :
    (mu w - w.tau * w.kappa) ^ 2 ≤ (β * mu w) ^ 2 := by
  have hcenter := neighborhood_centerSq_le β w hneigh
  unfold centerSq at hcenter
  have hsum_nonneg :
      0 ≤ ∑ j : Fin n, (w.x j * w.s j - mu w) ^ 2 := by
    exact Finset.sum_nonneg
      (fun j _ => sq_nonneg (w.x j * w.s j - mu w))
  have hsame :
      (mu w - w.tau * w.kappa) ^ 2 =
        (w.tau * w.kappa - mu w) ^ 2 := by
    ring
  rw [hsame]
  nlinarith

/-- In the wide neighborhood, every vector complementarity product is at least
`mu/2`.  This keeps the scalar `τκ` separate from the `Fin n` sum, as in the
separated proof plan. -/
theorem neighborhood_component_product_lower_wide {n : Nat}
    (w : HSState n) (hneigh : HSDNeighborhood ytmBetaWide w) (i : Fin n) :
    mu w / 2 ≤ w.x i * w.s i := by
  have hdev := neighborhood_component_dev_sq_le_bound ytmBetaWide w hneigh i
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaWide w hneigh
  unfold ytmBetaWide at hdev
  have hs : 0 ≤ (w.x i * w.s i - mu w / 2) ^ 2 := sq_nonneg _
  nlinarith

/-- Scalar analogue of `neighborhood_component_product_lower_wide`. -/
theorem neighborhood_scalar_product_lower_wide {n : Nat}
    (w : HSState n) (hneigh : HSDNeighborhood ytmBetaWide w) :
    mu w / 2 ≤ w.tau * w.kappa := by
  have hdev := neighborhood_scalar_dev_sq_le_bound ytmBetaWide w hneigh
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaWide w hneigh
  unfold ytmBetaWide at hdev
  have hs : 0 ≤ (w.tau * w.kappa - mu w / 2) ^ 2 := sq_nonneg _
  nlinarith

/-- Positive part used in the YTM corrector estimate.  It is deliberately kept as a
small elementary definition instead of using an order-theory abstraction. -/
def posPart (a : ℝ) : ℝ := if 0 ≤ a then a else 0

/-- Absolute value expressed through the positive part.  This identity is useful for
turning the skew relation `Σ δᵢ + η = 0` into an `ℓ₁` bound. -/
theorem abs_eq_two_posPart_sub (a : ℝ) :
    |a| = 2 * posPart a - a := by
  unfold posPart
  by_cases h : 0 ≤ a
  · have h_abs : |a| = a := abs_of_nonneg h
    rw [ite_eq_left h, h_abs]
    ring
  · have hlt : a < 0 := lt_of_not_ge h
    have h_abs : |a| = -a := abs_of_neg hlt
    rw [ite_eq_right h, h_abs]
    ring

/-- The positive part of each vector second-order complementarity product is bounded
by the corresponding squared centrality deviation divided by `2 mu`.  This is the
componentwise bridge from the corrector identity to the positive-part summation
argument. -/
theorem corrector_component_posPart_bound {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) (i : Fin n) :
    posPart (d.dx i * d.ds i) ≤
      (mu w - w.x i * w.s i) ^ 2 / (2 * mu w) := by
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaWide w hneigh
  have hzlower := neighborhood_component_product_lower_wide w hneigh i
  have hquad := corrector_component_second_order_upper w d hdir i
  unfold posPart
  by_cases hδ : 0 ≤ d.dx i * d.ds i
  · rw [ite_eq_left hδ]
    have hcoef : 2 * mu w ≤ 4 * (w.x i * w.s i) := by
      nlinarith
    have hmul : 2 * mu w * (d.dx i * d.ds i) ≤
        4 * (w.x i * w.s i) * (d.dx i * d.ds i) := by
      exact mul_le_mul_of_nonneg_right hcoef hδ
    have hbound : 2 * mu w * (d.dx i * d.ds i) ≤
        (mu w - w.x i * w.s i) ^ 2 := le_trans hmul hquad
    have hbound' : (d.dx i * d.ds i) * (2 * mu w) ≤
        (mu w - w.x i * w.s i) ^ 2 := by
      calc
        (d.dx i * d.ds i) * (2 * mu w)
            = 2 * mu w * (d.dx i * d.ds i) := by ring
        _ ≤ (mu w - w.x i * w.s i) ^ 2 := hbound
    have hden : 0 < 2 * mu w := by nlinarith
    exact (le_div_iff₀ hden).2 hbound'
  · rw [ite_eq_right hδ]
    have hden_nonneg : 0 ≤ 2 * mu w := by nlinarith
    exact div_nonneg (sq_nonneg _) hden_nonneg

/-- Scalar analogue of `corrector_component_posPart_bound`. -/
theorem corrector_scalar_posPart_bound {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) :
    posPart (d.dtau * d.dkappa) ≤
      (mu w - w.tau * w.kappa) ^ 2 / (2 * mu w) := by
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaWide w hneigh
  have hzlower := neighborhood_scalar_product_lower_wide w hneigh
  have hquad := corrector_scalar_second_order_upper w d hdir
  unfold posPart
  by_cases hδ : 0 ≤ d.dtau * d.dkappa
  · rw [ite_eq_left hδ]
    have hcoef : 2 * mu w ≤ 4 * (w.tau * w.kappa) := by
      nlinarith
    have hmul : 2 * mu w * (d.dtau * d.dkappa) ≤
        4 * (w.tau * w.kappa) * (d.dtau * d.dkappa) := by
      exact mul_le_mul_of_nonneg_right hcoef hδ
    have hbound : 2 * mu w * (d.dtau * d.dkappa) ≤
        (mu w - w.tau * w.kappa) ^ 2 := le_trans hmul hquad
    have hbound' : (d.dtau * d.dkappa) * (2 * mu w) ≤
        (mu w - w.tau * w.kappa) ^ 2 := by
      calc
        (d.dtau * d.dkappa) * (2 * mu w)
            = 2 * mu w * (d.dtau * d.dkappa) := by ring
        _ ≤ (mu w - w.tau * w.kappa) ^ 2 := hbound
    have hden : 0 < 2 * mu w := by nlinarith
    exact (le_div_iff₀ hden).2 hbound'
  · rw [ite_eq_right hδ]
    have hden_nonneg : 0 ≤ 2 * mu w := by nlinarith
    exact div_nonneg (sq_nonneg _) hden_nonneg

/-- Summed positive-part bound, still keeping the vector and scalar pieces separate.
This is the key estimate needed before converting the zero-sum relation into an
absolute-value bound. -/
theorem corrector_positive_part_sum_bound {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) :
    (∑ i : Fin n, posPart (d.dx i * d.ds i)) +
      posPart (d.dtau * d.dkappa) ≤ mu w / 8 := by
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaWide w hneigh
  have hvec :
      (∑ i : Fin n, posPart (d.dx i * d.ds i)) ≤
        ∑ i : Fin n, (mu w - w.x i * w.s i) ^ 2 / (2 * mu w) := by
    exact Finset.sum_le_sum (fun i _ =>
      corrector_component_posPart_bound w d hneigh hdir i)
  have hscalar := corrector_scalar_posPart_bound w d hneigh hdir
  have hvec_rewrite :
      (∑ i : Fin n, (mu w - w.x i * w.s i) ^ 2 / (2 * mu w)) =
        (∑ i : Fin n, (w.x i * w.s i - mu w) ^ 2) / (2 * mu w) := by
    calc
      (∑ i : Fin n, (mu w - w.x i * w.s i) ^ 2 / (2 * mu w))
          = ∑ i : Fin n, (w.x i * w.s i - mu w) ^ 2 / (2 * mu w) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i : Fin n, (w.x i * w.s i - mu w) ^ 2) / (2 * mu w) := by
              rw [← Finset.sum_div]
  have hscalar_rewrite :
      (mu w - w.tau * w.kappa) ^ 2 / (2 * mu w) =
        (w.tau * w.kappa - mu w) ^ 2 / (2 * mu w) := by
    ring
  have hsum_rewrite :
      (∑ i : Fin n, (mu w - w.x i * w.s i) ^ 2 / (2 * mu w)) +
        (mu w - w.tau * w.kappa) ^ 2 / (2 * mu w) =
      ((∑ i : Fin n, (w.x i * w.s i - mu w) ^ 2) +
        (w.tau * w.kappa - mu w) ^ 2) / (2 * mu w) := by
    calc
      (∑ i : Fin n, (mu w - w.x i * w.s i) ^ 2 / (2 * mu w)) +
          (mu w - w.tau * w.kappa) ^ 2 / (2 * mu w)
          = (∑ i : Fin n, (w.x i * w.s i - mu w) ^ 2) / (2 * mu w) +
              (w.tau * w.kappa - mu w) ^ 2 / (2 * mu w) := by
              rw [hvec_rewrite, hscalar_rewrite]
      _ = ((∑ i : Fin n, (w.x i * w.s i - mu w) ^ 2) +
            (w.tau * w.kappa - mu w) ^ 2) / (2 * mu w) := by
              ring
  have hcenter := neighborhood_centerSq_le ytmBetaWide w hneigh
  unfold centerSq at hcenter
  unfold ytmBetaWide at hcenter
  have hbound_center :
      ((∑ i : Fin n, (w.x i * w.s i - mu w) ^ 2) +
        (w.tau * w.kappa - mu w) ^ 2) / (2 * mu w) ≤ mu w / 8 := by
    have hcenter' :
        ((∑ i : Fin n, (w.x i * w.s i - mu w) ^ 2) +
          (w.tau * w.kappa - mu w) ^ 2) ≤ (mu w / 2) ^ 2 := by
      convert hcenter using 1
      ring
    have hden : 0 < 2 * mu w := by nlinarith
    rw [div_le_iff₀ hden]
    nlinarith [hcenter']
  calc
    (∑ i : Fin n, posPart (d.dx i * d.ds i)) +
        posPart (d.dtau * d.dkappa)
        ≤ (∑ i : Fin n, (mu w - w.x i * w.s i) ^ 2 / (2 * mu w)) +
            (mu w - w.tau * w.kappa) ^ 2 / (2 * mu w) := by
            exact add_le_add hvec hscalar
    _ = ((∑ i : Fin n, (w.x i * w.s i - mu w) ^ 2) +
          (w.tau * w.kappa - mu w) ^ 2) / (2 * mu w) := hsum_rewrite
    _ ≤ mu w / 8 := hbound_center


/-- If a finite family together with one scalar has zero total sum, then the sum of
absolute values is twice the sum of positive parts. -/
theorem abs_sum_add_abs_eq_two_posPart_sum_of_sum_add_zero {n : Nat}
    (a : Fin n → ℝ) (η : ℝ)
    (hzero : (∑ i : Fin n, a i) + η = 0) :
    (∑ i : Fin n, |a i|) + |η| =
      2 * ((∑ i : Fin n, posPart (a i)) + posPart η) := by
  simp_rw [abs_eq_two_posPart_sub]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  nlinarith

/-- The positive-part bound plus zero-sum relation gives an ℓ₁ bound for the
second-order complementarity products. -/
theorem corrector_cross_l1_bound {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) :
    (∑ i : Fin n, |d.dx i * d.ds i|) + |d.dtau * d.dkappa| ≤ mu w / 4 := by
  have hzero := corrector_second_order_sum_zero w d hdir
  have hpos := corrector_positive_part_sum_bound w d hneigh hdir
  have habs := abs_sum_add_abs_eq_two_posPart_sum_of_sum_add_zero
    (fun i : Fin n => d.dx i * d.ds i) (d.dtau * d.dkappa) hzero
  calc
    (∑ i : Fin n, |d.dx i * d.ds i|) + |d.dtau * d.dkappa|
        = 2 * ((∑ i : Fin n, posPart (d.dx i * d.ds i)) +
            posPart (d.dtau * d.dkappa)) := habs
    _ ≤ 2 * (mu w / 8) := by
          exact mul_le_mul_of_nonneg_left hpos (by norm_num)
    _ = mu w / 4 := by ring

/-- A square-sum is bounded by the square of the corresponding ℓ₁ norm.  The scalar
term is kept separate from the `Fin n` sum to match the HSDE notation. -/
theorem sum_sq_add_sq_le_l1_sq {n : Nat} (a : Fin n → ℝ) (η : ℝ) :
    (∑ i : Fin n, (a i) ^ 2) + η ^ 2 ≤
      ((∑ i : Fin n, |a i|) + |η|) ^ 2 := by
  let L : ℝ := (∑ i : Fin n, |a i|) + |η|
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact add_nonneg
      (Finset.sum_nonneg (fun i _ => abs_nonneg (a i)))
      (abs_nonneg η)
  have hterm : ∀ i : Fin n, (a i) ^ 2 ≤ |a i| * L := by
    intro i
    have hsingle : |a i| ≤ ∑ j : Fin n, |a j| := by
      exact Finset.single_le_sum
        (fun j _ => abs_nonneg (a j))
        (by simp)
    have hleL : |a i| ≤ L := by
      dsimp [L]
      nlinarith [abs_nonneg η]
    calc
      (a i) ^ 2 = |a i| * |a i| := by
        rw [← sq_abs]
        ring
      _ ≤ |a i| * L := by
        exact mul_le_mul_of_nonneg_left hleL (abs_nonneg (a i))
  have hsum : (∑ i : Fin n, (a i) ^ 2) ≤ (∑ i : Fin n, |a i|) * L := by
    calc
      (∑ i : Fin n, (a i) ^ 2) ≤ ∑ i : Fin n, |a i| * L := by
        exact Finset.sum_le_sum (fun i _ => hterm i)
      _ = (∑ i : Fin n, |a i|) * L := by
        rw [← Finset.sum_mul]
  have hscalar : η ^ 2 ≤ |η| * L := by
    have hleL : |η| ≤ L := by
      dsimp [L]
      have hsum_nonneg : 0 ≤ ∑ i : Fin n, |a i| := by
        exact Finset.sum_nonneg (fun i _ => abs_nonneg (a i))
      nlinarith
    calc
      η ^ 2 = |η| * |η| := by
        rw [← sq_abs]
        ring
      _ ≤ |η| * L := by
        exact mul_le_mul_of_nonneg_left hleL (abs_nonneg η)
  calc
    (∑ i : Fin n, (a i) ^ 2) + η ^ 2
        ≤ (∑ i : Fin n, |a i|) * L + |η| * L := by
          exact add_le_add hsum hscalar
    _ = L ^ 2 := by
          dsimp [L]
          ring

/-- The ℓ₁ bound implies the YTM square-sum bound for the corrector products. -/
theorem corrector_cross_sq_sum_bound {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) :
    (∑ i : Fin n, (d.dx i * d.ds i) ^ 2) +
      (d.dtau * d.dkappa) ^ 2 ≤ (mu w / 4) ^ 2 := by
  have hl1 := corrector_cross_l1_bound w d hneigh hdir
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaWide w hneigh
  have hsquares := sum_sq_add_sq_le_l1_sq
    (fun i : Fin n => d.dx i * d.ds i) (d.dtau * d.dkappa)
  have hL_nonneg :
      0 ≤ (∑ i : Fin n, |d.dx i * d.ds i|) + |d.dtau * d.dkappa| := by
    exact add_nonneg
      (Finset.sum_nonneg (fun i _ => abs_nonneg (d.dx i * d.ds i)))
      (abs_nonneg (d.dtau * d.dkappa))
  have hmu4_nonneg : 0 ≤ mu w / 4 := by nlinarith
  have hsq_l1 :
      ((∑ i : Fin n, |d.dx i * d.ds i|) + |d.dtau * d.dkappa|) ^ 2
        ≤ (mu w / 4) ^ 2 := by
    nlinarith
  exact le_trans hsquares hsq_l1

/-- Each vector second-order product is individually bounded by `mu/4` in absolute
value. -/
theorem corrector_component_cross_abs_le_quarter_mu {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) (i : Fin n) :
    |d.dx i * d.ds i| ≤ mu w / 4 := by
  have hl1 := corrector_cross_l1_bound w d hneigh hdir
  have hsingle : |d.dx i * d.ds i| ≤ ∑ j : Fin n, |d.dx j * d.ds j| := by
    exact Finset.single_le_sum
      (fun j _ => abs_nonneg (d.dx j * d.ds j))
      (by simp)
  have hle_total :
      |d.dx i * d.ds i| ≤
        (∑ j : Fin n, |d.dx j * d.ds j|) + |d.dtau * d.dkappa| := by
    nlinarith [abs_nonneg (d.dtau * d.dkappa)]
  exact le_trans hle_total hl1

/-- The scalar second-order product is individually bounded by `mu/4` in absolute
value. -/
theorem corrector_scalar_cross_abs_le_quarter_mu {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) :
    |d.dtau * d.dkappa| ≤ mu w / 4 := by
  have hl1 := corrector_cross_l1_bound w d hneigh hdir
  have hsum_nonneg : 0 ≤ ∑ j : Fin n, |d.dx j * d.ds j| := by
    exact Finset.sum_nonneg (fun j _ => abs_nonneg (d.dx j * d.ds j))
  have hle_total :
      |d.dtau * d.dkappa| ≤
        (∑ j : Fin n, |d.dx j * d.ds j|) + |d.dtau * d.dkappa| := by
    nlinarith
  exact le_trans hle_total hl1

/-- If two factors have positive product and a positive weighted sum with positive
weights, then both factors are positive. -/
theorem factors_pos_of_mul_pos_and_weighted_sum_pos {a b wa wb : ℝ}
    (hwa : 0 < wa) (hwb : 0 < wb)
    (hmul : 0 < a * b)
    (hsum : 0 < wb * a + wa * b) :
    0 < a ∧ 0 < b := by
  rcases (mul_pos_iff.mp hmul) with hpos | hneg
  · exact hpos
  · rcases hneg with ⟨ha, hb⟩
    have hterm1 : wb * a < 0 := mul_neg_of_pos_of_neg hwb ha
    have hterm2 : wa * b < 0 := mul_neg_of_pos_of_neg hwa hb
    have hsum_neg : wb * a + wa * b < 0 := by nlinarith
    nlinarith

/-- Positivity of each vector pair after the full corrector step. -/
theorem corrector_component_pair_pos_full_step {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) (i : Fin n) :
    0 < (addStep w d 1).x i ∧ 0 < (addStep w d 1).s i := by
  rcases hneigh.1 with ⟨hxpos, htpos, hspos, hkpos⟩
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaWide w hneigh
  have habs := corrector_component_cross_abs_le_quarter_mu w d hneigh hdir i
  have hlower : -(mu w / 4) ≤ d.dx i * d.ds i := (abs_le.mp habs).1
  have hprod_mu : 0 < mu w + d.dx i * d.ds i := by
    nlinarith
  have hprod : 0 < (addStep w d 1).x i * (addStep w d 1).s i := by
    rw [corrector_component_product_full_step w d hdir i]
    exact hprod_mu
  have hweighted :
      0 < w.s i * (addStep w d 1).x i + w.x i * (addStep w d 1).s i := by
    have hc := hdir.compl.component_eq i
    have hxs : 0 < w.x i * w.s i := mul_pos (hxpos i) (hspos i)
    have heq :
        w.s i * (addStep w d 1).x i + w.x i * (addStep w d 1).s i =
          w.x i * w.s i + mu w := by
      dsimp [addStep]
      calc
        w.s i * (w.x i + 1 * d.dx i) +
            w.x i * (w.s i + 1 * d.ds i)
            = 2 * (w.x i * w.s i) + (w.x i * d.ds i + w.s i * d.dx i) := by
              ring_nf
        _ = 2 * (w.x i * w.s i) + (1 * mu w - w.x i * w.s i) := by
              rw [hc]
        _ = w.x i * w.s i + mu w := by
              ring_nf
    rw [heq]
    nlinarith
  exact factors_pos_of_mul_pos_and_weighted_sum_pos
    (hxpos i) (hspos i) hprod hweighted

/-- Positivity of the scalar pair after the full corrector step. -/
theorem corrector_scalar_pair_pos_full_step {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) :
    0 < (addStep w d 1).tau ∧ 0 < (addStep w d 1).kappa := by
  rcases hneigh.1 with ⟨hxpos, htpos, hspos, hkpos⟩
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaWide w hneigh
  have habs := corrector_scalar_cross_abs_le_quarter_mu w d hneigh hdir
  have hlower : -(mu w / 4) ≤ d.dtau * d.dkappa := (abs_le.mp habs).1
  have hprod_mu : 0 < mu w + d.dtau * d.dkappa := by
    nlinarith
  have hprod : 0 < (addStep w d 1).tau * (addStep w d 1).kappa := by
    rw [corrector_scalar_product_full_step w d hdir]
    exact hprod_mu
  have hweighted :
      0 < w.kappa * (addStep w d 1).tau + w.tau * (addStep w d 1).kappa := by
    have hc := hdir.compl.scalar_eq
    have htk : 0 < w.tau * w.kappa := mul_pos htpos hkpos
    have heq :
        w.kappa * (addStep w d 1).tau + w.tau * (addStep w d 1).kappa =
          w.tau * w.kappa + mu w := by
      dsimp [addStep]
      calc
        w.kappa * (w.tau + 1 * d.dtau) +
            w.tau * (w.kappa + 1 * d.dkappa)
            = 2 * (w.tau * w.kappa) + (w.tau * d.dkappa + w.kappa * d.dtau) := by
              ring_nf
        _ = 2 * (w.tau * w.kappa) + (1 * mu w - w.tau * w.kappa) := by
              rw [hc]
        _ = w.tau * w.kappa + mu w := by
              ring_nf
    rw [heq]
    nlinarith
  exact factors_pos_of_mul_pos_and_weighted_sum_pos
    htpos hkpos hprod hweighted

/-- The full corrector step remains in the positive orthant. -/
theorem corrector_full_step_interior {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) :
    Interior (addStep w d 1) := by
  have hpair : ∀ i : Fin n,
      0 < (addStep w d 1).x i ∧ 0 < (addStep w d 1).s i := by
    intro i
    exact corrector_component_pair_pos_full_step w d hneigh hdir i
  have hscalar := corrector_scalar_pair_pos_full_step w d hneigh hdir
  exact ⟨fun i => (hpair i).1, hscalar.1, fun i => (hpair i).2, hscalar.2⟩

/-- Scaled YTM corrector estimate for the second-order complementarity products.

This is the single genuinely analytic ingredient in the corrector half.  In the usual
notation put

* `u = (x, τ)`, `v = (s, κ)`,
* `Δu = (dx, dτ)`, `Δv = (ds, dκ)`,
* `zᵢ = uᵢ vᵢ`, `μ = (Σ zᵢ)/(n+1)`.

For a corrector direction, the linearized complementarity equations give

`uᵢ Δvᵢ + vᵢ Δuᵢ = μ - zᵢ`,

and skew orthogonality gives

`Σ Δuᵢ Δvᵢ = 0`.

The standard YTM argument sets `pᵢ = Δuᵢ/uᵢ` and `qᵢ = Δvᵢ/vᵢ`.  Then
`pᵢ + qᵢ = μ/zᵢ - 1`, while `Σ zᵢ pᵢqᵢ = 0`.  Since `w ∈ N(1/2)`, each `zᵢ` is
within `μ/2` of `μ`; this bounds the positive part of `zᵢ pᵢqᵢ` by the squared
centrality residual.  Hence all full-step products stay positive and

`Σ (Δuᵢ Δvᵢ)^2 ≤ (μ/4)^2`.

The rest of the Lean file has already reduced the corrector theorem to exactly this
statement.  This lemma is intentionally isolated so that the remaining paper estimate
is no longer mixed with the bookkeeping around `centerSq` and `mu`. -/
theorem YTM_corrector_scaled_estimate {n : Nat}
    (w : HSState n) (d : HSDirection n) :
    HSDNeighborhood ytmBetaWide w →
    HSDStepDirection w d 1 →
    Interior (addStep w d 1) ∧
      (∑ i : Fin n, (d.dx i * d.ds i) ^ 2) +
        (d.dtau * d.dkappa) ^ 2 ≤
        (ytmBetaTight * mu w) ^ 2 := by
  intro hneigh hdir
  refine ⟨corrector_full_step_interior w d hneigh hdir, ?_⟩
  have hsq := corrector_cross_sq_sum_bound w d hneigh hdir
  unfold ytmBetaTight
  convert hsq using 1
  ring

/-- The corrector-side local bound, reduced to the isolated scaled YTM estimate.

Unlike the previous version, this theorem itself no longer contains the paper-level
analytic obligation: after `YTM_corrector_scaled_estimate`, the proof is just the
algebraic identities already established above. -/
theorem YTM_corrector_interior_and_center_bound {n : Nat}
    (w : HSState n) (d : HSDirection n) :
    HSDNeighborhood ytmBetaWide w →
    HSDStepDirection w d 1 →
    Interior (addStep w d 1) ∧
      centerSq (addStep w d 1).x (addStep w d 1).tau
        (addStep w d 1).s (addStep w d 1).kappa
        (mu (addStep w d 1)) ≤
        (ytmBetaTight * mu (addStep w d 1)) ^ 2 := by
  intro hneigh hdir
  rcases YTM_corrector_scaled_estimate w d hneigh hdir with
    ⟨hinterior, hsecond⟩
  refine ⟨hinterior, ?_⟩
  rw [corrector_centerSq_full_step_eq_cross_sq w d hdir]
  rw [corrector_mu_full_step w d hdir]
  exact hsecond

/-- Corrector full-step local estimate, now reduced to the explicit analytic bound
`YTM_corrector_interior_and_center_bound`; no placeholder remains in this wrapper. -/
theorem YTM_corrector_full_step_local_estimate {n : Nat}
    (w : HSState n) (d : HSDirection n) :
    HSDNeighborhood ytmBetaWide w →
    HSDStepDirection w d 1 →
    Interior (addStep w d 1) ∧ HSDNeighborhood ytmBetaTight (addStep w d 1) := by
  intro hneigh hdir
  rcases YTM_corrector_interior_and_center_bound w d hneigh hdir with
    ⟨hinterior, hcenter⟩
  have hbeta_pos : 0 < ytmBetaTight := by
    unfold ytmBetaTight
    norm_num
  have hbeta_lt : ytmBetaTight < 1 := by
    unfold ytmBetaTight
    norm_num
  exact ⟨hinterior, ⟨hinterior, ⟨hbeta_pos, ⟨hbeta_lt, hcenter⟩⟩⟩⟩



/-! ## Predictor-side elementary step-size and product identities -/

/-- The fixed YTM predictor step constant is positive. -/
theorem ytmStepConstant_pos : 0 < ytmStepConstant := by
  unfold ytmStepConstant
  positivity

/-- The fixed YTM predictor step constant is at most one. -/
theorem ytmStepConstant_le_one : ytmStepConstant ≤ 1 := by
  unfold ytmStepConstant
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (8 : ℝ) := by
    simp_all
  have hden_pos : 0 < (8 : ℝ) ^ 2 * Real.sqrt (8 : ℝ) := by
    positivity
  rw [div_le_iff₀ hden_pos]
  nlinarith [hsqrt_ge_one]

/-- The homogenized dimension is at least one. -/
theorem one_le_hdim (n : Nat) : (1 : ℝ) ≤ hdim n := by
  unfold hdim
  simp_all

/-- The square root of the homogenized dimension is positive. -/
theorem sqrt_hdim_pos (n : Nat) : 0 < Real.sqrt (hdim n) := by
  exact Real.sqrt_pos.2 (hdim_pos n)

/-- The square root of the homogenized dimension is at least one. -/
theorem one_le_sqrt_hdim (n : Nat) : (1 : ℝ) ≤ Real.sqrt (hdim n) := by
  have h := Real.sqrt_le_sqrt (one_le_hdim n)
  simpa using h

/-- Positivity of the fixed predictor step length. -/
theorem predictor_alpha_fixed_pos (n : Nat) :
    0 < ytmStepConstant / Real.sqrt (hdim n) := by
  exact div_pos ytmStepConstant_pos (sqrt_hdim_pos n)

/-- The fixed predictor step length is at most one. -/
theorem predictor_alpha_fixed_le_one (n : Nat) :
    ytmStepConstant / Real.sqrt (hdim n) ≤ 1 := by
  have hden : 0 < Real.sqrt (hdim n) := sqrt_hdim_pos n
  rw [div_le_iff₀ hden]
  nlinarith [ytmStepConstant_le_one, one_le_sqrt_hdim n]

/-- Predictor step formula for `mu`.  For `γ = 0`, the homogenized gap and hence
`mu` are multiplied by `1 - α`. -/
theorem predictor_mu_step {n : Nat}
    (w : HSState n) (d : HSDirection n) (α : ℝ)
    (hdir : HSDStepDirection w d 0) :
    mu (addStep w d α) = (1 - α) * mu w := by
  unfold mu
  rw [gap_addStep_of_HSDStepDirection w d α 0 hdir]
  ring

/-- Predictor product identity for each vector complementarity pair. -/
theorem predictor_component_product_step {n : Nat}
    (w : HSState n) (d : HSDirection n) (α : ℝ)
    (hdir : HSDStepDirection w d 0) (i : Fin n) :
    (addStep w d α).x i * (addStep w d α).s i =
      (1 - α) * (w.x i * w.s i) + α ^ 2 * (d.dx i * d.ds i) := by
  have hc := hdir.compl.component_eq i
  dsimp [addStep]
  calc
    (w.x i + α * d.dx i) * (w.s i + α * d.ds i)
        = w.x i * w.s i + α * (w.x i * d.ds i + w.s i * d.dx i) +
            α ^ 2 * (d.dx i * d.ds i) := by
            ring
    _ = w.x i * w.s i + α * (0 * mu w - w.x i * w.s i) +
            α ^ 2 * (d.dx i * d.ds i) := by
            rw [hc]
    _ = (1 - α) * (w.x i * w.s i) + α ^ 2 * (d.dx i * d.ds i) := by
            ring

/-- Predictor product identity for the scalar complementarity pair. -/
theorem predictor_scalar_product_step {n : Nat}
    (w : HSState n) (d : HSDirection n) (α : ℝ)
    (hdir : HSDStepDirection w d 0) :
    (addStep w d α).tau * (addStep w d α).kappa =
      (1 - α) * (w.tau * w.kappa) + α ^ 2 * (d.dtau * d.dkappa) := by
  have hc := hdir.compl.scalar_eq
  dsimp [addStep]
  calc
    (w.tau + α * d.dtau) * (w.kappa + α * d.dkappa)
        = w.tau * w.kappa + α * (w.tau * d.dkappa + w.kappa * d.dtau) +
            α ^ 2 * (d.dtau * d.dkappa) := by
            ring
    _ = w.tau * w.kappa + α * (0 * mu w - w.tau * w.kappa) +
            α ^ 2 * (d.dtau * d.dkappa) := by
            rw [hc]
    _ = (1 - α) * (w.tau * w.kappa) + α ^ 2 * (d.dtau * d.dkappa) := by
            ring





/-! ## Predictor positivity bookkeeping -/

/-- Predictor weighted-sum identity for each vector pair.

Together with positivity of the product after the step, this identity lets us recover
positivity of each individual factor.  This is useful because the remaining YTM
estimate naturally controls the products. -/
theorem predictor_component_weighted_sum_step {n : Nat}
    (w : HSState n) (d : HSDirection n) (α : ℝ)
    (hdir : HSDStepDirection w d 0) (i : Fin n) :
    w.s i * (addStep w d α).x i + w.x i * (addStep w d α).s i =
      (2 - α) * (w.x i * w.s i) := by
  have hc := hdir.compl.component_eq i
  dsimp [addStep]
  calc
    w.s i * (w.x i + α * d.dx i) +
        w.x i * (w.s i + α * d.ds i)
        = 2 * (w.x i * w.s i) +
            α * (w.x i * d.ds i + w.s i * d.dx i) := by
            ring
    _ = 2 * (w.x i * w.s i) +
            α * (0 * mu w - w.x i * w.s i) := by
            rw [hc]
    _ = (2 - α) * (w.x i * w.s i) := by
            ring

/-- Predictor weighted-sum identity for the scalar pair. -/
theorem predictor_scalar_weighted_sum_step {n : Nat}
    (w : HSState n) (d : HSDirection n) (α : ℝ)
    (hdir : HSDStepDirection w d 0) :
    w.kappa * (addStep w d α).tau + w.tau * (addStep w d α).kappa =
      (2 - α) * (w.tau * w.kappa) := by
  have hc := hdir.compl.scalar_eq
  dsimp [addStep]
  calc
    w.kappa * (w.tau + α * d.dtau) +
        w.tau * (w.kappa + α * d.dkappa)
        = 2 * (w.tau * w.kappa) +
            α * (w.tau * d.dkappa + w.kappa * d.dtau) := by
            ring
    _ = 2 * (w.tau * w.kappa) +
            α * (0 * mu w - w.tau * w.kappa) := by
            rw [hc]
    _ = (2 - α) * (w.tau * w.kappa) := by
            ring

/-- If the predictor step keeps the product of one vector complementarity pair
positive, then the two factors themselves are positive. -/
theorem predictor_component_pair_pos_of_product_pos {n : Nat}
    (w : HSState n) (d : HSDirection n) (α : ℝ)
    (hinterior : Interior w)
    (hdir : HSDStepDirection w d 0)
    (hαle : α ≤ 1) (i : Fin n)
    (hprod : 0 < (addStep w d α).x i * (addStep w d α).s i) :
    0 < (addStep w d α).x i ∧ 0 < (addStep w d α).s i := by
  rcases hinterior with ⟨hxpos, htpos, hspos, hkpos⟩
  have hxs : 0 < w.x i * w.s i := mul_pos (hxpos i) (hspos i)
  have hcoef : 0 < 2 - α := by nlinarith
  have hweighted :
      0 < w.s i * (addStep w d α).x i +
        w.x i * (addStep w d α).s i := by
    rw [predictor_component_weighted_sum_step w d α hdir i]
    exact mul_pos hcoef hxs
  exact factors_pos_of_mul_pos_and_weighted_sum_pos
    (hxpos i) (hspos i) hprod hweighted

/-- Scalar analogue of `predictor_component_pair_pos_of_product_pos`. -/
theorem predictor_scalar_pair_pos_of_product_pos {n : Nat}
    (w : HSState n) (d : HSDirection n) (α : ℝ)
    (hinterior : Interior w)
    (hdir : HSDStepDirection w d 0)
    (hαle : α ≤ 1)
    (hprod : 0 < (addStep w d α).tau * (addStep w d α).kappa) :
    0 < (addStep w d α).tau ∧ 0 < (addStep w d α).kappa := by
  rcases hinterior with ⟨hxpos, htpos, hspos, hkpos⟩
  have htk : 0 < w.tau * w.kappa := mul_pos htpos hkpos
  have hcoef : 0 < 2 - α := by nlinarith
  have hweighted :
      0 < w.kappa * (addStep w d α).tau +
        w.tau * (addStep w d α).kappa := by
    rw [predictor_scalar_weighted_sum_step w d α hdir]
    exact mul_pos hcoef htk
  exact factors_pos_of_mul_pos_and_weighted_sum_pos
    htpos hkpos hprod hweighted

/-- Product positivity for all complementarity pairs implies that the predictor step
stays in the interior. -/
theorem predictor_step_interior_of_product_pos {n : Nat}
    (w : HSState n) (d : HSDirection n) (α : ℝ)
    (hinterior : Interior w)
    (hdir : HSDStepDirection w d 0)
    (hαle : α ≤ 1)
    (hprod_vec : ∀ i : Fin n,
      0 < (addStep w d α).x i * (addStep w d α).s i)
    (hprod_scalar : 0 < (addStep w d α).tau * (addStep w d α).kappa) :
    Interior (addStep w d α) := by
  have hpair : ∀ i : Fin n,
      0 < (addStep w d α).x i ∧ 0 < (addStep w d α).s i := by
    intro i
    exact predictor_component_pair_pos_of_product_pos
      w d α hinterior hdir hαle i (hprod_vec i)
  have hscalar := predictor_scalar_pair_pos_of_product_pos
    w d α hinterior hdir hαle hprod_scalar
  exact ⟨fun i => (hpair i).1, hscalar.1, fun i => (hpair i).2, hscalar.2⟩


/-- Predictor residual identity for each vector complementarity pair.  This is the
main bookkeeping formula needed for the remaining neighborhood estimate: the new
centrality residual is the old residual contracted by `1 - α`, plus the second-order
predictor product. -/
theorem predictor_component_center_residual_step {n : Nat}
    (w : HSState n) (d : HSDirection n) (α : ℝ)
    (hdir : HSDStepDirection w d 0) (i : Fin n) :
    (addStep w d α).x i * (addStep w d α).s i -
        mu (addStep w d α) =
      (1 - α) * (w.x i * w.s i - mu w) +
        α ^ 2 * (d.dx i * d.ds i) := by
  rw [predictor_component_product_step w d α hdir i]
  rw [predictor_mu_step w d α hdir]
  ring

/-- Scalar version of the predictor residual identity. -/
theorem predictor_scalar_center_residual_step {n : Nat}
    (w : HSState n) (d : HSDirection n) (α : ℝ)
    (hdir : HSDStepDirection w d 0) :
    (addStep w d α).tau * (addStep w d α).kappa -
        mu (addStep w d α) =
      (1 - α) * (w.tau * w.kappa - mu w) +
        α ^ 2 * (d.dtau * d.dkappa) := by
  rw [predictor_scalar_product_step w d α hdir]
  rw [predictor_mu_step w d α hdir]
  ring

/-- Exact expansion of the predictor centrality residual after an arbitrary
predictor step.  No estimate is used here; this only isolates the expression that
has to be bounded in the remaining YTM predictor argument. -/
theorem predictor_centerSq_step_eq {n : Nat}
    (w : HSState n) (d : HSDirection n) (α : ℝ)
    (hdir : HSDStepDirection w d 0) :
    centerSq (addStep w d α).x (addStep w d α).tau
      (addStep w d α).s (addStep w d α).kappa
      (mu (addStep w d α)) =
      (∑ i : Fin n,
        ((1 - α) * (w.x i * w.s i - mu w) +
          α ^ 2 * (d.dx i * d.ds i)) ^ 2) +
        ((1 - α) * (w.tau * w.kappa - mu w) +
          α ^ 2 * (d.dtau * d.dkappa)) ^ 2 := by
  have hsum :
      (∑ i : Fin n,
        ((addStep w d α).x i * (addStep w d α).s i -
          mu (addStep w d α)) ^ 2) =
      ∑ i : Fin n,
        ((1 - α) * (w.x i * w.s i - mu w) +
          α ^ 2 * (d.dx i * d.ds i)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [predictor_component_center_residual_step w d α hdir i]
  have hscalar :
      ((addStep w d α).tau * (addStep w d α).kappa -
          mu (addStep w d α)) ^ 2 =
        ((1 - α) * (w.tau * w.kappa - mu w) +
          α ^ 2 * (d.dtau * d.dkappa)) ^ 2 := by
    rw [predictor_scalar_center_residual_step w d α hdir]
  unfold centerSq
  exact congrArg₂ (fun a b : ℝ => a + b) hsum hscalar

/-- Fixed-step specialization of `predictor_mu_step`. -/
theorem predictor_fixed_mu_step {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 0) :
    mu (addStep w d (ytmStepConstant / Real.sqrt (hdim n))) =
      (1 - ytmStepConstant / Real.sqrt (hdim n)) * mu w := by
  simpa using
    predictor_mu_step w d (ytmStepConstant / Real.sqrt (hdim n)) hdir

/-- Fixed-step specialization of the vector predictor product identity. -/
theorem predictor_fixed_component_product_step {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 0) (i : Fin n) :
    (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).x i *
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).s i =
      (1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.x i * w.s i) +
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dx i * d.ds i) := by
  simpa using
    predictor_component_product_step w d
      (ytmStepConstant / Real.sqrt (hdim n)) hdir i

/-- Fixed-step specialization of the scalar predictor product identity. -/
theorem predictor_fixed_scalar_product_step {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 0) :
    (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).tau *
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).kappa =
      (1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.tau * w.kappa) +
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dtau * d.dkappa) := by
  simpa using
    predictor_scalar_product_step w d
      (ytmStepConstant / Real.sqrt (hdim n)) hdir

/-- Fixed-step specialization of the exact predictor centrality-residual expansion. -/
theorem predictor_fixed_centerSq_step_eq {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 0) :
    centerSq (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).x
      (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).tau
      (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).s
      (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).kappa
      (mu (addStep w d (ytmStepConstant / Real.sqrt (hdim n)))) =
      (∑ i : Fin n,
        ((1 - ytmStepConstant / Real.sqrt (hdim n)) *
            (w.x i * w.s i - mu w) +
          (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
            (d.dx i * d.ds i)) ^ 2) +
        ((1 - ytmStepConstant / Real.sqrt (hdim n)) *
            (w.tau * w.kappa - mu w) +
          (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
            (d.dtau * d.dkappa)) ^ 2 := by
  simpa using
    predictor_centerSq_step_eq w d
      (ytmStepConstant / Real.sqrt (hdim n)) hdir

/-- Fixed-parameter YTM local theory.

This version matches the proof in Ye--Todd--Mizuno: predictor moves from the
`1/4` neighborhood to the `1/2` neighborhood with a step of order
`8^{-2.5}/sqrt(n+1)`, while corrector moves from the `1/2` neighborhood back to
`1/4` using the full step. -/
structure YTMFixedLocalTheory (n : Nat) where
  predictor_estimate_fixed : ∀ (w : HSState n) (d : HSDirection n),
    HSDNeighborhood ytmBetaTight w →
    HSDStepDirection w d 0 →
    ∃ α, PredictorStepGuarantee ytmBetaWide ytmStepConstant w d α
  corrector_estimate_fixed : ∀ (w : HSState n) (d : HSDirection n),
    HSDNeighborhood ytmBetaWide w →
    HSDStepDirection w d 1 →
    CorrectorStepGuarantee ytmBetaTight w d



/-- Predictor estimate used in the YTM proof.

This packages the two ingredients of the predictor half of Theorem 6:
starting from the tight neighborhood `N(1/4)`, the predictor direction with `γ = 0`
has a step of length at least `ytmStepConstant / sqrt(n+1)` and the resulting point
remains in the wide neighborhood `N(1/2)` with the corresponding gap decrease. -/
structure YTMPredictorEstimate (n : Nat) : Prop where
  estimate : ∀ (w : HSState n) (d : HSDirection n),
    HSDNeighborhood ytmBetaTight w →
    HSDStepDirection w d 0 →
    ∃ α, PredictorStepGuarantee ytmBetaWide ytmStepConstant w d α

/-- A lower bound on the second-order predictor products implies positivity of all
fixed-step vector complementarity products.  This is purely algebraic: the product
identity says `x⁺ᵢs⁺ᵢ = (1 - α) xᵢsᵢ + α² ΔxᵢΔsᵢ`. -/
theorem predictor_fixed_component_product_pos_of_cross_lower {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 0)
    (hcross : ∀ i : Fin n,
      -((1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.x i * w.s i)) <
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dx i * d.ds i)) :
    ∀ i : Fin n,
      0 < (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).x i *
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).s i := by
  intro i
  rw [predictor_fixed_component_product_step w d hdir i]
  nlinarith [hcross i]

/-- Scalar analogue of `predictor_fixed_component_product_pos_of_cross_lower`. -/
theorem predictor_fixed_scalar_product_pos_of_cross_lower {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 0)
    (hcross :
      -((1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.tau * w.kappa)) <
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dtau * d.dkappa)) :
    0 < (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).tau *
      (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).kappa := by
  rw [predictor_fixed_scalar_product_step w d hdir]
  nlinarith [hcross]



/-- If the fixed predictor step keeps both factors of a vector pair positive, then
its second-order product cannot cancel the first-order complementarity product. -/
theorem predictor_fixed_component_cross_lower_of_step_product_pos {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 0) (i : Fin n)
    (hprod :
      0 < (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).x i *
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).s i) :
      -((1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.x i * w.s i)) <
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dx i * d.ds i) := by
  rw [predictor_fixed_component_product_step w d hdir i] at hprod
  nlinarith

/-- Scalar analogue of `predictor_fixed_component_cross_lower_of_step_product_pos`. -/
theorem predictor_fixed_scalar_cross_lower_of_step_product_pos {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hdir : HSDStepDirection w d 0)
    (hprod :
      0 < (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).tau *
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).kappa) :
      -((1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.tau * w.kappa)) <
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dtau * d.dkappa) := by
  rw [predictor_fixed_scalar_product_step w d hdir] at hprod
  nlinarith

/-- Relative componentwise bounds imply positivity of a vector complementarity
product after the fixed predictor step. -/
theorem predictor_fixed_component_product_pos_of_relative_bounds {n : Nat}
    (w : HSState n) (d : HSDirection n) (i : Fin n)
    (hxrel : |(ytmStepConstant / Real.sqrt (hdim n)) * d.dx i| < w.x i)
    (hsrel : |(ytmStepConstant / Real.sqrt (hdim n)) * d.ds i| < w.s i) :
    0 < (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).x i *
      (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).s i := by
  dsimp [addStep]
  have hxlower := (abs_lt.mp hxrel).1
  have hslower := (abs_lt.mp hsrel).1
  have hxpos : 0 < w.x i + (ytmStepConstant / Real.sqrt (hdim n)) * d.dx i := by
    linarith
  have hspos : 0 < w.s i + (ytmStepConstant / Real.sqrt (hdim n)) * d.ds i := by
    linarith
  exact mul_pos hxpos hspos

/-- Scalar analogue of `predictor_fixed_component_product_pos_of_relative_bounds`. -/
theorem predictor_fixed_scalar_product_pos_of_relative_bounds {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (htrel : |(ytmStepConstant / Real.sqrt (hdim n)) * d.dtau| < w.tau)
    (hkrel : |(ytmStepConstant / Real.sqrt (hdim n)) * d.dkappa| < w.kappa) :
    0 < (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).tau *
      (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).kappa := by
  dsimp [addStep]
  have htlower := (abs_lt.mp htrel).1
  have hklower := (abs_lt.mp hkrel).1
  have htpos : 0 < w.tau + (ytmStepConstant / Real.sqrt (hdim n)) * d.dtau := by
    linarith
  have hkpos : 0 < w.kappa + (ytmStepConstant / Real.sqrt (hdim n)) * d.dkappa := by
    linarith
  exact mul_pos htpos hkpos


/-- Elementary conversion from a scaled relative bound to an unscaled relative bound. -/
theorem abs_step_lt_of_scaled_abs_lt_one
    (x a α : ℝ) (hx : 0 < x)
    (hscaled : |α * (a / x)| < 1) :
    |α * a| < x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hinner : α * a = x * (α * (a / x)) := by
    field_simp [hxne]
  calc
    |α * a| = |x * (α * (a / x))| := by rw [hinner]
    _ = |x| * |α * (a / x)| := by rw [abs_mul]
    _ = x * |α * (a / x)| := by rw [abs_of_pos hx]
    _ < x * 1 := mul_lt_mul_of_pos_left hscaled hx
    _ = x := by ring

/-! ## Fixed predictor scaled residual notation

The last remaining predictor estimate is easier to read if the fixed step length,
the scaled direction components, and the explicit post-predictor centrality
residual are named.  These definitions do not add new assumptions; they are just
abbreviations for the formulas already used in `PredictorFixedScaledNormBounds`. -/

/-- The fixed predictor step length used in the YTM local analysis. -/
abbrev predictorFixedAlpha (n : Nat) : ℝ :=
  ytmStepConstant / Real.sqrt (hdim n)

/-- Scaled `x`-direction component multiplied by the fixed predictor step. -/
abbrev predictorScaledDx {n : Nat} (w : HSState n) (d : HSDirection n)
    (i : Fin n) : ℝ :=
  predictorFixedAlpha n * (d.dx i / w.x i)

/-- Scaled `s`-direction component multiplied by the fixed predictor step. -/
abbrev predictorScaledDs {n : Nat} (w : HSState n) (d : HSDirection n)
    (i : Fin n) : ℝ :=
  predictorFixedAlpha n * (d.ds i / w.s i)

/-- Scaled `tau`-direction component multiplied by the fixed predictor step. -/
abbrev predictorScaledDtau {n : Nat} (w : HSState n)
    (d : HSDirection n) : ℝ :=
  predictorFixedAlpha n * (d.dtau / w.tau)

/-- Scaled `kappa`-direction component multiplied by the fixed predictor step. -/
abbrev predictorScaledDkappa {n : Nat} (w : HSState n)
    (d : HSDirection n) : ℝ :=
  predictorFixedAlpha n * (d.dkappa / w.kappa)

/-- Explicit vector residual after substituting the predictor product identity. -/
abbrev predictorVecResidualAfter {n : Nat} (w : HSState n)
    (d : HSDirection n) (i : Fin n) : ℝ :=
  (1 - predictorFixedAlpha n) * (w.x i * w.s i - mu w) +
    (predictorFixedAlpha n) ^ 2 * (d.dx i * d.ds i)

/-- Explicit scalar residual after substituting the predictor product identity. -/
abbrev predictorScalarResidualAfter {n : Nat} (w : HSState n)
    (d : HSDirection n) : ℝ :=
  (1 - predictorFixedAlpha n) * (w.tau * w.kappa - mu w) +
    (predictorFixedAlpha n) ^ 2 * (d.dtau * d.dkappa)

/-- Core form of the remaining fixed-step YTM estimate.

Compared with `PredictorFixedScaledNormBounds`, this version uses named scaled
variables and named residuals.  Thus the final predictor obligation is precisely the
mathematical YTM estimate, rather than a long expanded expression. -/
structure PredictorFixedScaledCoreBounds {n : Nat}
    (w : HSState n) (d : HSDirection n) : Prop where
  scaled_vec : ∀ i : Fin n,
    |predictorScaledDx w d i| < 1 ∧
    |predictorScaledDs w d i| < 1
  scaled_tau : |predictorScaledDtau w d| < 1
  scaled_kappa : |predictorScaledDkappa w d| < 1
  center :
    (∑ i : Fin n, (predictorVecResidualAfter w d i) ^ 2) +
      (predictorScalarResidualAfter w d) ^ 2 ≤
      (ytmBetaWide * ((1 - predictorFixedAlpha n) * mu w)) ^ 2


/-- Fixed-step scaled-norm bounds for the predictor direction.

This is the same analytic information as the relative-step formulation below, but
written in the natural YTM scaled variables `dx/x`, `ds/s`, `dtau/tau`, and
`dkappa/kappa`.  The surrounding lemmas convert these scaled bounds into the
unscaled relative inequalities needed for positivity of the step. -/
structure PredictorFixedScaledNormBounds {n : Nat}
    (w : HSState n) (d : HSDirection n) : Prop where
  scaled_vec : ∀ i : Fin n,
    |(ytmStepConstant / Real.sqrt (hdim n)) * (d.dx i / w.x i)| < 1 ∧
    |(ytmStepConstant / Real.sqrt (hdim n)) * (d.ds i / w.s i)| < 1
  scaled_tau : |(ytmStepConstant / Real.sqrt (hdim n)) * (d.dtau / w.tau)| < 1
  scaled_kappa : |(ytmStepConstant / Real.sqrt (hdim n)) * (d.dkappa / w.kappa)| < 1
  center :
    (∑ i : Fin n,
      ((1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.x i * w.s i - mu w) +
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dx i * d.ds i)) ^ 2) +
      ((1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.tau * w.kappa - mu w) +
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dtau * d.dkappa)) ^ 2 ≤
      (ytmBetaWide *
        ((1 - ytmStepConstant / Real.sqrt (hdim n)) * mu w)) ^ 2

/-- Fixed-step scaled-direction bounds needed in the predictor half of the YTM proof.

This record isolates the genuinely analytic estimate from the surrounding Lean
bookkeeping.  Its first three fields say that the fixed predictor step is
componentwise small relative to the current interior point.  The last field is
the explicit `N(1/2)` centrality estimate after substituting the predictor
product identities. -/
structure PredictorFixedScaledDirectionBounds {n : Nat}
    (w : HSState n) (d : HSDirection n) : Prop where
  rel_vec : ∀ i : Fin n,
    |(ytmStepConstant / Real.sqrt (hdim n)) * d.dx i| < w.x i ∧
    |(ytmStepConstant / Real.sqrt (hdim n)) * d.ds i| < w.s i
  rel_tau : |(ytmStepConstant / Real.sqrt (hdim n)) * d.dtau| < w.tau
  rel_kappa : |(ytmStepConstant / Real.sqrt (hdim n)) * d.dkappa| < w.kappa
  center :
    (∑ i : Fin n,
      ((1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.x i * w.s i - mu w) +
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dx i * d.ds i)) ^ 2) +
      ((1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.tau * w.kappa - mu w) +
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dtau * d.dkappa)) ^ 2 ≤
      (ytmBetaWide *
        ((1 - ytmStepConstant / Real.sqrt (hdim n)) * mu w)) ^ 2

/-- Convert the natural scaled-norm bounds into the relative-step bounds used in
the positivity bookkeeping. -/
theorem predictor_fixed_scaled_norm_bounds_to_direction_bounds {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hbounds : PredictorFixedScaledNormBounds w d) :
    PredictorFixedScaledDirectionBounds w d := by
  rcases hneigh.1 with ⟨hxpos, htpos, hspos, hkpos⟩
  refine
    { rel_vec := ?_
      rel_tau := ?_
      rel_kappa := ?_
      center := hbounds.center }
  · intro i
    exact ⟨
      abs_step_lt_of_scaled_abs_lt_one
        (w.x i) (d.dx i) (ytmStepConstant / Real.sqrt (hdim n))
        (hxpos i) (hbounds.scaled_vec i).1,
      abs_step_lt_of_scaled_abs_lt_one
        (w.s i) (d.ds i) (ytmStepConstant / Real.sqrt (hdim n))
        (hspos i) (hbounds.scaled_vec i).2⟩
  · exact abs_step_lt_of_scaled_abs_lt_one
      w.tau d.dtau (ytmStepConstant / Real.sqrt (hdim n))
      htpos hbounds.scaled_tau
  · exact abs_step_lt_of_scaled_abs_lt_one
      w.kappa d.dkappa (ytmStepConstant / Real.sqrt (hdim n))
      hkpos hbounds.scaled_kappa

/-- Convert the named core estimate back to the expanded scaled-norm package. -/
theorem predictor_fixed_scaled_core_to_norm_bounds {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hcore : PredictorFixedScaledCoreBounds w d) :
    PredictorFixedScaledNormBounds w d := by
  refine
    { scaled_vec := ?_
      scaled_tau := ?_
      scaled_kappa := ?_
      center := ?_ }
  · intro i
    exact hcore.scaled_vec i
  · exact hcore.scaled_tau
  · exact hcore.scaled_kappa
  · exact hcore.center

end HSDInteriorPointLP
