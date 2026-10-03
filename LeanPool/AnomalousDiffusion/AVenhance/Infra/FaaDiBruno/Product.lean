/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Seminorm
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Product estimates for the Appendix B seminorm
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

namespace AVenhance.FaaDiBruno

/-- The coordinate derivative seminorm of a product is bounded by the
binomial convolution of the two derivative seminorms. -/
theorem derivativeSup_mul_le {d n : ℕ} [Nonempty (Fin d)]
    (f g : Vec d → ℝ) (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    derivativeSup n (fun x ↦ f x * g x) ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ENNReal) *
        derivativeSup k f * derivativeSup (n - k) g := by
  let μ := vecVolume d
  have hfae : ∀ᵐ x ∂μ, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k (liftVecOne f) (WithLp.toLp 1 x)‖ₑ ≤ derivativeSup k f := by
    apply ae_all_iff.2
    intro k
    exact operatorDerivative_ae_le_derivativeSup (n := k) f
  have hgae : ∀ᵐ x ∂μ, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k (liftVecOne g) (WithLp.toLp 1 x)‖ₑ ≤ derivativeSup k g := by
    apply ae_all_iff.2
    intro k
    exact operatorDerivative_ae_le_derivativeSup (n := k) g
  have hpoint : ∀ᵐ x ∂μ,
      ‖iteratedFDeriv ℝ n (liftVecOne (fun y ↦ f y * g y)) (WithLp.toLp 1 x)‖ₑ ≤
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ENNReal) *
          derivativeSup k f * derivativeSup (n - k) g := by
    filter_upwards [hfae, hgae] with x hfx hgx
    have hreal := norm_iteratedFDeriv_mul_le
      (contDiff_liftVecOne hf) (contDiff_liftVecOne hg)
      (WithLp.toLp 1 x) (n := n) le_rfl
    have hreal_nonneg : ∀ k ∈ Finset.range (n + 1),
        0 ≤ (n.choose k : ℝ) *
          ‖iteratedFDeriv ℝ k (liftVecOne f) (WithLp.toLp 1 x)‖ *
          ‖iteratedFDeriv ℝ (n - k) (liftVecOne g) (WithLp.toLp 1 x)‖ := by
      intro k hk
      positivity
    have htoENN :
        ENNReal.ofReal (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
          ‖iteratedFDeriv ℝ k (liftVecOne f) (WithLp.toLp 1 x)‖ *
          ‖iteratedFDeriv ℝ (n - k) (liftVecOne g) (WithLp.toLp 1 x)‖) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ENNReal) *
          ‖iteratedFDeriv ℝ k (liftVecOne f) (WithLp.toLp 1 x)‖ₑ *
          ‖iteratedFDeriv ℝ (n - k) (liftVecOne g) (WithLp.toLp 1 x)‖ₑ := by
      rw [ENNReal.ofReal_sum_of_nonneg hreal_nonneg]
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp [ENNReal.ofReal_natCast]
    calc
      _ = ENNReal.ofReal
          ‖iteratedFDeriv ℝ n (liftVecOne (fun y ↦ f y * g y)) (WithLp.toLp 1 x)‖ := by
            simp
      _ ≤ ENNReal.ofReal (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
          ‖iteratedFDeriv ℝ k (liftVecOne f) (WithLp.toLp 1 x)‖ *
          ‖iteratedFDeriv ℝ (n - k) (liftVecOne g) (WithLp.toLp 1 x)‖) :=
            ENNReal.ofReal_le_ofReal hreal
      _ = _ := htoENN
      _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ENNReal) *
          derivativeSup k f * derivativeSup (n - k) g := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        gcongr
        · exact hfx k
        · exact hgx (n - k)
  have hOp := essSup_le_of_ae_le _ (by
    filter_upwards [hpoint] with x hx
    simpa [Real.enorm_eq_ofReal_abs] using hx)
  calc
    derivativeSup n (fun x ↦ f x * g x) ≤
        operatorDerivativeSup n (fun x ↦ f x * g x) :=
          derivativeSup_le_operatorDerivativeSup _
    _ = essSup
        (fun x : Vec d ↦
          ‖iteratedFDeriv ℝ n (liftVecOne (fun y ↦ f y * g y)) (WithLp.toLp 1 x)‖ₑ) μ := by
          simp [μ, operatorDerivativeSup, eLpNormEssSup_eq_essSup_enorm,
            Real.enorm_eq_ofReal_abs]
    _ ≤ _ := by simpa [μ] using hOp

/-- Sum of the reciprocals of the first positive integers up to the given order. -/
noncomputable def Product.harmonicOne (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, (k + 1 : ℝ)⁻¹

/-- Sum of the reciprocal squares of the first positive integers up to the given order. -/
noncomputable def Product.harmonicTwo (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, ((k + 1 : ℝ) ^ 2)⁻¹

theorem Product.weightedConvolution_identity (m : ℕ) :
    (∑ k ∈ Finset.range m,
      (m : ℝ) ^ 2 / ((k + 1 : ℝ) ^ 2 * (m - k : ℝ) ^ 2)) =
      ((m : ℝ) / (m + 1)) ^ 2 *
        (2 * Product.harmonicTwo m + 4 * Product.harmonicOne m / (m + 1)) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range m) :
      (m : ℝ) ^ 2 / ((k + 1 : ℝ) ^ 2 * (m - k : ℝ) ^ 2) =
        ((m : ℝ) / (m + 1)) ^ 2 *
          (((k + 1 : ℝ) ^ 2)⁻¹ + 1 / (m - k : ℝ) ^ 2 +
            2 / ((k + 1 : ℝ) * (m - k : ℝ))) := by
    have hsum : (k + 1 : ℝ) + (m - k : ℝ) = m + 1 := by ring
    have ha : 0 < (k + 1 : ℝ) := by positivity
    have hklt : k < m := Finset.mem_range.mp hk
    have hkltReal : (k : ℝ) < m := by exact_mod_cast hklt
    have hb : 0 < (m - k : ℝ) := sub_pos.mpr hkltReal
    have hc : 0 < (m + 1 : ℝ) := by positivity
    field_simp
    nlinarith [hsum]
  calc
    _ = ∑ k ∈ Finset.range m,
        (((m : ℝ) / (m + 1)) ^ 2 *
          (((k + 1 : ℝ) ^ 2)⁻¹ + 1 / (m - k : ℝ) ^ 2 +
            2 / ((k + 1 : ℝ) * (m - k : ℝ)))) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hterm k hk
    _ = ((m : ℝ) / (m + 1)) ^ 2 *
        ∑ k ∈ Finset.range m,
          (((k + 1 : ℝ) ^ 2)⁻¹ + 1 / (m - k : ℝ) ^ 2 +
            2 / ((k + 1 : ℝ) * (m - k : ℝ))) := by
          rw [← Finset.mul_sum]
    _ = ((m : ℝ) / (m + 1)) ^ 2 *
        (2 * Product.harmonicTwo m + 4 * Product.harmonicOne m / (m + 1)) := by
          congr 2
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          have hreflectTwo :
              (∑ k ∈ Finset.range m, 1 / (m - k : ℝ) ^ 2) = Product.harmonicTwo m := by
            calc
              _ = ∑ k ∈ Finset.range m,
                  1 / (((m - 1 - k : ℕ) + 1 : ℝ) ^ 2) := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    have hmk : (m : ℝ) - k = ((m - 1 - k : ℕ) + 1 : ℝ) := by
                      have hle : k ≤ m - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)
                      have hklt : k < m := Finset.mem_range.mp hk
                      have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by omega)
                      rw [Nat.cast_sub hle, Nat.cast_sub hm]
                      push_cast
                      ring
                    rw [hmk]
              _ = Product.harmonicTwo m := by
                    simpa [Product.harmonicTwo] using
                      (Finset.sum_range_reflect (fun j : ℕ ↦ ((j + 1 : ℝ) ^ 2)⁻¹) m)
          have hreflectOne :
              (∑ k ∈ Finset.range m, (m - k : ℝ)⁻¹) = Product.harmonicOne m := by
            calc
              _ = ∑ k ∈ Finset.range m,
                  (((m - 1 - k : ℕ) + 1 : ℝ))⁻¹ := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    have hmk : (m : ℝ) - k = ((m - 1 - k : ℕ) + 1 : ℝ) := by
                      have hle : k ≤ m - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)
                      have hklt : k < m := Finset.mem_range.mp hk
                      have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by omega)
                      rw [Nat.cast_sub hle, Nat.cast_sub hm]
                      push_cast
                      ring
                    rw [hmk]
              _ = Product.harmonicOne m := by
                    simpa [Product.harmonicOne] using
                      (Finset.sum_range_reflect (fun j : ℕ ↦ (j + 1 : ℝ)⁻¹) m)
          rw [hreflectTwo]
          have hcross :
              (∑ k ∈ Finset.range m,
                1 / ((k + 1 : ℝ) * (m - k : ℝ))) =
                2 * Product.harmonicOne m / (m + 1) := by
            calc
              _ = ∑ k ∈ Finset.range m,
                  (1 / (m + 1 : ℝ)) *
                    ((k + 1 : ℝ)⁻¹ + (m - k : ℝ)⁻¹) := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      have hsum : (k + 1 : ℝ) + (m - k : ℝ) = m + 1 := by ring
                      have ha : (k + 1 : ℝ) ≠ 0 := ne_of_gt (by positivity)
                      have hklt : (k : ℝ) < m := by
                        exact_mod_cast (Finset.mem_range.mp hk)
                      have hb : (m - k : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hklt)
                      have hc : (m + 1 : ℝ) ≠ 0 := ne_of_gt (by positivity)
                      field_simp [ha, hb, hc]
                      nlinarith [hsum]
              _ = (1 / (m + 1 : ℝ)) *
                  (∑ k ∈ Finset.range m,
                    ((k + 1 : ℝ)⁻¹ + (m - k : ℝ)⁻¹)) := by
                    rw [← Finset.mul_sum]
              _ = (1 / (m + 1 : ℝ)) * (Product.harmonicOne m + Product.harmonicOne m) := by
                    rw [Finset.sum_add_distrib, hreflectOne]
                    simp [Product.harmonicOne]
              _ = _ := by ring
          calc
            _ = (∑ k ∈ Finset.range m, ((k + 1 : ℝ) ^ 2)⁻¹) + Product.harmonicTwo m +
                2 * (∑ k ∈ Finset.range m,
                  1 / ((k + 1 : ℝ) * (m - k : ℝ))) := by
                  apply congrArg (fun z : ℝ =>
                    (∑ k ∈ Finset.range m, ((k + 1 : ℝ) ^ 2)⁻¹) + Product.harmonicTwo m + z)
                  calc
                    _ = ∑ k ∈ Finset.range m,
                        2 * (1 / ((k + 1 : ℝ) * (m - k : ℝ))) := by
                          apply Finset.sum_congr rfl
                          intro k hk
                          ring
                    _ = _ := by rw [Finset.mul_sum]
            _ = 2 * Product.harmonicTwo m + 4 * Product.harmonicOne m / (m + 1) := by
                  rw [hcross]
                  simp [Product.harmonicTwo]
                  ring

theorem Product.tailReciprocalSquares (q : ℕ) :
    (∑ k ∈ Finset.range q, ((k + 6 : ℝ) ^ 2)⁻¹) ≤ 1 / 5 := by
  have hterm (k : ℕ) : ((k + 6 : ℝ) ^ 2)⁻¹ ≤
      1 / (k + 5 : ℝ) - 1 / (k + 6 : ℝ) := by
    have ha : (k + 5 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hb : (k + 6 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    field_simp [ha, hb]
    nlinarith
  have htel (q : ℕ) :
      (∑ k ∈ Finset.range q,
        (1 / (k + 5 : ℝ) - 1 / (k + 6 : ℝ))) = 1 / 5 - 1 / (q + 5 : ℝ) := by
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  calc
    _ ≤ ∑ k ∈ Finset.range q,
        (1 / (k + 5 : ℝ) - 1 / (k + 6 : ℝ)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hterm k
    _ = 1 / 5 - 1 / (q + 5 : ℝ) := htel q
    _ ≤ 1 / 5 := by
          have hnonneg : 0 ≤ (q + 5 : ℝ)⁻¹ := by positivity
          simp only [one_div]
          linarith

theorem Product.harmonicTwo_le_five_thirds (m : ℕ) : Product.harmonicTwo m ≤ 5 / 3 := by
  by_cases hm : m ≤ 5
  · have hsubset : Finset.range m ⊆ Finset.range 5 :=
      Finset.range_subset.mpr (by
        intro k hk
        exact Finset.mem_range.mpr (hk.trans_le hm))
    calc
      Product.harmonicTwo m ≤ Product.harmonicTwo 5 := by
        unfold Product.harmonicTwo
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro k hk hnot
        positivity
      _ ≤ 5 / 3 := by norm_num [Product.harmonicTwo, Finset.sum_range_succ]
  · have hm5 : 5 ≤ m := Nat.le_of_not_ge hm
    have hdecomp : m = 5 + (m - 5) := by omega
    rw [hdecomp]
    unfold Product.harmonicTwo
    rw [Finset.sum_range_add]
    change (∑ k ∈ Finset.range 5, ((k + 1 : ℝ) ^ 2)⁻¹) +
      (∑ k ∈ Finset.range (m - 5), ((↑(5 + k) + 1 : ℝ) ^ 2)⁻¹) ≤ 5 / 3
    have hconst :
        (∑ k ∈ Finset.range 5, ((k + 1 : ℝ) ^ 2)⁻¹) ≤ 22 / 15 := by
      norm_num [Finset.sum_range_succ]
    have htail := Product.tailReciprocalSquares (m - 5)
    have htail' :
        (∑ k ∈ Finset.range (m - 5), ((↑(5 + k) + 1 : ℝ) ^ 2)⁻¹) ≤ 1 / 5 := by
      calc
        _ = ∑ k ∈ Finset.range (m - 5), ((k + 6 : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_congr rfl
          intro k hk
          congr 2
          push_cast
          ring
        _ ≤ 1 / 5 := htail
    linarith

theorem Product.harmonicOne_nonneg (m : ℕ) : 0 ≤ Product.harmonicOne m := by
  unfold Product.harmonicOne
  apply Finset.sum_nonneg
  intro k hk
  positivity

theorem Product.harmonicOne_sq_le (m : ℕ) :
    Product.harmonicOne m ^ 2 ≤ (m : ℝ) * Product.harmonicTwo m := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m)
    (fun _ : ℕ ↦ (1 : ℝ)) (fun k ↦ (k + 1 : ℝ)⁻¹)
  simpa [Product.harmonicOne, Product.harmonicTwo] using hc

theorem Product.harmonicOne_sqrt_bound {m : ℕ} (hm : 32 ≤ m) :
    Real.sqrt (5 * (m : ℝ) / 3) ≤ (m : ℝ) / 6 + 2 := by
  have hm' : (32 : ℝ) ≤ m := by exact_mod_cast hm
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hsq : (0 : ℝ) ≤ ((m : ℝ) / 6 + 2) ^ 2 - 5 * (m : ℝ) / 3 := by
      have hs := sq_nonneg ((m : ℝ) - 18)
      nlinarith [hm']
    nlinarith [hsq]

theorem Product.weightedConvolution_bound_large {m : ℕ} (hm : 32 ≤ m) :
    ((m : ℝ) / (m + 1)) ^ 2 *
      (2 * Product.harmonicTwo m + 4 * Product.harmonicOne m / (m + 1)) ≤ 4 := by
  have hmOnePos : 0 < (m + 1 : ℝ) := by positivity
  have hone : Product.harmonicOne m ≤ Real.sqrt (5 * (m : ℝ) / 3) := by
    apply (Real.le_sqrt (Product.harmonicOne_nonneg m) (by positivity)).mpr
    calc
      Product.harmonicOne m ^ 2 ≤ (m : ℝ) * Product.harmonicTwo m := Product.harmonicOne_sq_le m
      _ ≤ (m : ℝ) * (5 / 3) := by gcongr; exact Product.harmonicTwo_le_five_thirds m
      _ = 5 * (m : ℝ) / 3 := by ring
  have hone' : Product.harmonicOne m ≤ (m : ℝ) / 6 + 2 :=
    hone.trans (Product.harmonicOne_sqrt_bound hm)
  have hbound : 2 * Product.harmonicTwo m + 4 * Product.harmonicOne m / (m + 1) ≤
      10 / 3 + 4 * ((m : ℝ) / 6 + 2) / (m + 1) := by
    gcongr
    · linarith [Product.harmonicTwo_le_five_thirds m]
  calc
    _ ≤ ((m : ℝ) / (m + 1)) ^ 2 *
        (10 / 3 + 4 * ((m : ℝ) / 6 + 2) / (m + 1)) := by gcongr
    _ ≤ 4 := by
      have hmden : (m + 1 : ℝ) ≠ 0 := ne_of_gt hmOnePos
      field_simp [hmden]
      nlinarith [sq_nonneg (m : ℝ), hmOnePos]

theorem Product.weightedConvolution_le_four (m : ℕ) :
    (∑ k ∈ Finset.range m,
      (m : ℝ) ^ 2 / ((k + 1 : ℝ) ^ 2 * (m - k : ℝ) ^ 2)) ≤ 4 := by
  by_cases hm : m < 32
  · have hm31 : m ≤ 31 := Nat.le_of_lt_succ (by omega)
    interval_cases m <;> norm_num [Finset.sum_range_succ]
  · have hm32 : 32 ≤ m := Nat.le_of_not_gt hm
    rw [Product.weightedConvolution_identity]
    exact Product.weightedConvolution_bound_large hm32

/-- The scalar weight sum in the paper's product estimate is at most four. -/
theorem weightedConvolution_le_four_paper (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (n + 1 : ℝ) ^ 2 / ((k + 1 : ℝ) ^ 2 * ((n - k + 1 : ℕ) : ℝ) ^ 2)) ≤ 4 := by
  have heq : (∑ k ∈ Finset.range (n + 1),
      (n + 1 : ℝ) ^ 2 / ((k + 1 : ℝ) ^ 2 * ((n - k + 1 : ℕ) : ℝ) ^ 2)) =
      ∑ k ∈ Finset.range (n + 1),
        (n + 1 : ℝ) ^ 2 / ((k + 1 : ℝ) ^ 2 * (n + 1 - k : ℝ) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < n + 1 := Finset.mem_range.mp hk
    have hnat : n + 1 - k = n - k + 1 := by omega
    have hcastSub : ((n + 1 - k : ℕ) : ℝ) = (n + 1 : ℝ) - k := by
      rw [Nat.cast_sub (Nat.le_of_lt hklt)]
      push_cast
      ring
    have hcastNat : ((n + 1 - k : ℕ) : ℝ) = ((n - k + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hden : ((n - k + 1 : ℕ) : ℝ) = (n + 1 : ℝ) - k := hcastNat.symm.trans hcastSub
    rw [hden]
  rw [heq]
  simpa [Nat.cast_add] using Product.weightedConvolution_le_four (n + 1)

theorem Product.weightedCoefficient_identity {n k : ℕ} (hk : k ≤ n) (R : ℝ) :
    let r := (ENNReal.ofReal R)⁻¹
    ENNReal.ofReal (((n + 1 : ℝ) ^ 2) / n.factorial) * r ^ n *
        ENNReal.ofReal (n.choose k : ℝ) =
      ENNReal.ofReal
          ((n + 1 : ℝ) ^ 2 /
            ((k + 1 : ℝ) ^ 2 * ((n - k + 1 : ℕ) : ℝ) ^ 2)) *
        (ENNReal.ofReal (((k + 1 : ℝ) ^ 2) / k.factorial) * r ^ k) *
        (ENNReal.ofReal ((((n - k + 1 : ℕ) : ℝ) ^ 2) / (n - k).factorial) * r ^ (n - k)) := by
  dsimp
  let r := (ENNReal.ofReal R)⁻¹
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hk
  have hchoose : (n.choose k : ℝ) * k.factorial * (n - k).factorial = n.factorial := by
    exact_mod_cast hchooseNat
  have hreal :
      ((n + 1 : ℝ) ^ 2 / n.factorial) * (n.choose k : ℝ) =
        ((n + 1 : ℝ) ^ 2 /
          ((k + 1 : ℝ) ^ 2 * ((n - k + 1 : ℕ) : ℝ) ^ 2)) *
          ((((k + 1 : ℝ) ^ 2) / k.factorial) *
            (((n - k + 1 : ℕ) : ℝ) ^ 2 / (n - k).factorial)) := by
    field_simp
    nlinarith [hchoose]
  have hnNonneg : 0 ≤ ((n + 1 : ℝ) ^ 2 / n.factorial) := by positivity
  have hwNonneg : 0 ≤ ((n + 1 : ℝ) ^ 2 /
      ((k + 1 : ℝ) ^ 2 * ((n - k + 1 : ℕ) : ℝ) ^ 2)) := by positivity
  have hkNonneg : 0 ≤ (((k + 1 : ℝ) ^ 2) / k.factorial) := by positivity
  have hlNonneg : 0 ≤ (((n - k + 1 : ℕ) : ℝ) ^ 2 / (n - k).factorial) := by
    positivity
  have hpow : r ^ n = r ^ k * r ^ (n - k) := by
    calc
      r ^ n = r ^ (k + (n - k)) :=
        congrArg (fun j : ℕ ↦ r ^ j) (Nat.add_sub_of_le hk).symm
      _ = r ^ k * r ^ (n - k) := by rw [pow_add]
  calc
    ENNReal.ofReal (((n + 1 : ℝ) ^ 2) / n.factorial) * r ^ n *
        ENNReal.ofReal (n.choose k : ℝ) =
      (ENNReal.ofReal (((n + 1 : ℝ) ^ 2) / n.factorial) *
        ENNReal.ofReal (n.choose k : ℝ)) * r ^ n := by ac_rfl
    _ = ENNReal.ofReal ((((n + 1 : ℝ) ^ 2) / n.factorial) *
        (n.choose k : ℝ)) * r ^ n := by
      rw [← ENNReal.ofReal_mul hnNonneg]
    _ = ENNReal.ofReal
        (((n + 1 : ℝ) ^ 2 /
          ((k + 1 : ℝ) ^ 2 * ((n - k + 1 : ℕ) : ℝ) ^ 2)) *
          ((((k + 1 : ℝ) ^ 2) / k.factorial) *
            (((n - k + 1 : ℕ) : ℝ) ^ 2 / (n - k).factorial))) *
          (r ^ k * r ^ (n - k)) := by rw [hreal, hpow]
    _ = _ := by
      rw [ENNReal.ofReal_mul hwNonneg, ENNReal.ofReal_mul hkNonneg]
      ac_rfl

/-- The product seminorm is bounded by the weighted binomial convolution
before applying the numerical factor-four estimate. -/
theorem snorm_mul_le_weightedSum {d n : ℕ} [Nonempty (Fin d)]
    (f g : Vec d → ℝ) (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (R : ℝ) :
    snorm (fun x ↦ f x * g x) n R ≤
      ∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal
          ((n + 1 : ℝ) ^ 2 /
            ((k + 1 : ℝ) ^ 2 * ((n - k + 1 : ℕ) : ℝ) ^ 2)) *
          snorm f k R * snorm g (n - k) R := by
  let r := (ENNReal.ofReal R)⁻¹
  let c (j : ℕ) := ENNReal.ofReal (((j + 1 : ℝ) ^ 2) / j.factorial)
  have hderiv := derivativeSup_mul_le f g hf hg
  calc
    snorm (fun x ↦ f x * g x) n R = (c n * r ^ n) *
        derivativeSup n (fun x ↦ f x * g x) := by
          simp [snorm, c, r, mul_assoc]
    _ ≤ (c n * r ^ n) *
        (∑ k ∈ Finset.range (n + 1), (n.choose k : ENNReal) *
          derivativeSup k f * derivativeSup (n - k) g) := by
          gcongr
    _ = ∑ k ∈ Finset.range (n + 1),
        ((c n * r ^ n) * (n.choose k : ENNReal) *
          derivativeSup k f * derivativeSup (n - k) g) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = ∑ k ∈ Finset.range (n + 1),
        (ENNReal.ofReal
            ((n + 1 : ℝ) ^ 2 /
              ((k + 1 : ℝ) ^ 2 * ((n - k + 1 : ℕ) : ℝ) ^ 2)) *
          snorm f k R * snorm g (n - k) R) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkbound : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          have hcoeff := Product.weightedCoefficient_identity hkbound R
          rw [← ENNReal.ofReal_natCast (n.choose k)]
          rw [hcoeff]
          simp only [snorm, Nat.cast_add, Nat.cast_one]
          ac_rfl

/-- The finite maximum of the seminorms of orders zero through `n`. -/
def snormMax {d : ℕ} (f : Vec d → ℝ) (n : ℕ) (R : ℝ) : ENNReal :=
  ⨆ j : Fin (n + 1), snorm f j R

/-- The full product estimate of Appendix B.1, with the paper's constant. -/
theorem productEstimate {d n : ℕ} [Nonempty (Fin d)]
    (f g : Vec d → ℝ) (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    {R : ℝ} (_hR : 0 < R) :
    snorm (fun x ↦ f x * g x) n R ≤
      4 * snormMax f n R * snormMax g n R := by
  have hweighted := snorm_mul_le_weightedSum f g hf hg R
  have hweightSum :
      (∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal
          ((n + 1 : ℝ) ^ 2 /
            ((k + 1 : ℝ) ^ 2 * ((n - k + 1 : ℕ) : ℝ) ^ 2))) ≤ 4 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.range (n + 1))]
    · simpa using ENNReal.ofReal_le_ofReal (weightedConvolution_le_four_paper n)
    · intro k hk
      positivity
  have hF (k : ℕ) (hk : k ≤ n) : snorm f k R ≤ snormMax f n R := by
    exact le_iSup_of_le ⟨k, Nat.lt_succ_of_le hk⟩ le_rfl
  have hG (k : ℕ) (hk : k ≤ n) : snorm g k R ≤ snormMax g n R := by
    exact le_iSup_of_le ⟨k, Nat.lt_succ_of_le hk⟩ le_rfl
  calc
    snorm (fun x ↦ f x * g x) n R ≤
        ∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal
            ((n + 1 : ℝ) ^ 2 /
              ((k + 1 : ℝ) ^ 2 * ((n - k + 1 : ℕ) : ℝ) ^ 2)) *
            snormMax f n R * snormMax g n R := by
          refine hweighted.trans ?_
          apply Finset.sum_le_sum
          intro k hk
          have hkbound : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          have hlbound : n - k ≤ n := Nat.sub_le _ _
          gcongr
          · exact hF k hkbound
          · exact hG (n - k) hlbound
    _ = (∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal
          ((n + 1 : ℝ) ^ 2 /
            ((k + 1 : ℝ) ^ 2 * ((n - k + 1 : ℕ) : ℝ) ^ 2))) *
          snormMax f n R * snormMax g n R := by
          rw [Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ 4 * snormMax f n R * snormMax g n R := by
          calc
            _ ≤ (4 * snormMax f n R) * snormMax g n R := by
              apply mul_le_mul_of_nonneg_right
              · gcongr
              · positivity
            _ = 4 * (snormMax f n R * snormMax g n R) := by ring
            _ = 4 * snormMax f n R * snormMax g n R := by ring

/-- The zeroth-order derivative seminorm is the essential supremum of the
function itself. -/
theorem Product.derivativeSup_zero {d : ℕ} (f : Vec d → ℝ) :
    derivativeSup 0 f = eLpNormEssSup f (vecVolume d) := by
  simp [derivativeSup, partialSup, orderedPartial]

end AVenhance.FaaDiBruno

end
