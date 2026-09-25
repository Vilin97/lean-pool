/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.Operator


/-!
# Uniqueness for resolvents on bounded measurable functions

This file proves three elementary contraction principles for maps acting on bounded measurable
real functions. The first gives uniqueness for a bounded multiplicative perturbation equation.
The second propagates equality of two resolvent families from all sufficiently large shifts to
every positive shift by the resolvent identity. The third combines the first two principles.

Main results: `perturbed_unique`, `resolventFamily_eq_of_eventually`, and
`perturbed_eq_of_resolventFamilies`.

The operators are plain maps on functions; no Banach-space carrier or continuity is asserted.
-/

@[expose] public section

noncomputable section PortComputability

open Filter

namespace MarkovProcess

section

private theorem function_eq_zero_of_geometric_bound {alpha : Type*} {d : alpha → ℝ}
    {r D : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hD0 : 0 ≤ D)
    (himprove : ∀ {B : ℝ}, 0 ≤ B → (∀ x, |d x| ≤ B) → ∀ x, |d x| ≤ r * B)
    (hdD : ∀ x, |d x| ≤ D) : d = 0 := by
  have hpow : ∀ n : ℕ, ∀ x, |d x| ≤ r ^ n * D := by
    intro n
    induction n with
    | zero =>
        simpa only [pow_zero, one_mul] using hdD
    | succ n ih =>
        have hnext := himprove (mul_nonneg (pow_nonneg hr0 n) hD0) ih
        intro x
        simpa only [pow_succ, mul_assoc, mul_comm r (r ^ n), mul_left_comm] using hnext x
  funext x
  have hlim : Tendsto (fun n : ℕ ↦ r ^ n * D) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const D
  have hx0 : |d x| ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall fun n ↦ hpow n x)
  exact abs_eq_zero.mp (le_antisymm hx0 (abs_nonneg _))

variable {alpha : Type*} [MeasurableSpace alpha] [Nonempty alpha]

/-- **Uniqueness for a bounded perturbation equation.**  Suppose `R` is additive on bounded
measurable functions and has the uniform bound `|R f x| ≤ D / λ` whenever `|f| ≤ D`.  If
`0 ≤ q ≤ C` and `C < λ`, then two maps preserving bounded measurable functions and solving
`Z f = R f - R (q * Z f)` agree on every bounded measurable function.

At a fixed sufficiently large shift, this gives the bounded-measurable equality needed by
`resolventFamily_eq_of_eventually`.  The `Nonempty alpha` assumption is used to extract
`0 ≤ C` and nonnegativity of bounds from their pointwise hypotheses. -/
theorem perturbed_unique
    (R X Y : (alpha → ℝ) → alpha → ℝ) {q : alpha → ℝ} {C lam : ℝ}
    (hR_add : ∀ {f g : alpha → ℝ}, Measurable f → Measurable g →
      (∃ D, ∀ x, |f x| ≤ D) → (∃ D, ∀ x, |g x| ≤ D) → R (f + g) = R f + R g)
    (hR_bound : ∀ {f : alpha → ℝ}, Measurable f → ∀ {D : ℝ},
      (∀ x, |f x| ≤ D) → ∀ x, |R f x| ≤ D / lam)
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (hqC : ∀ x, q x ≤ C) (hlam : C < lam)
    (hX_meas : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Measurable (X f))
    (hY_meas : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Measurable (Y f))
    (hX_bound : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      ∃ D, ∀ x, |X f x| ≤ D)
    (hY_bound : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      ∃ D, ∀ x, |Y f x| ≤ D)
    (hX_fixed : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X f = R f - R (fun x ↦ q x * X f x))
    (hY_fixed : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y f = R f - R (fun x ↦ q x * Y f x))
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    X f = Y f := by
  have hfBound : ∃ E : ℝ, ∀ x, |f x| ≤ E := ⟨D, hfD⟩
  have hXeq := hX_fixed hf hfBound
  have hYeq := hY_fixed hf hfBound
  have hXm : Measurable (X f) := hX_meas hf hfBound
  have hYm : Measurable (Y f) := hY_meas hf hfBound
  obtain ⟨DX, hDX⟩ := hX_bound hf hfBound
  obtain ⟨DY, hDY⟩ := hY_bound hf hfBound
  let d : alpha → ℝ := X f - Y f
  have hdMeas : Measurable d := hXm.sub hYm
  have hdBound : ∀ x, |d x| ≤ |DX| + |DY| := by
    intro x
    calc
      |d x| ≤ |X f x| + |Y f x| := abs_sub _ _
      _ ≤ DX + DY := add_le_add (hDX x) (hDY x)
      _ ≤ |DX| + |DY| := add_le_add (le_abs_self _) (le_abs_self _)
  let alpha0 : alpha := Classical.choice inferInstance
  have hC0 : 0 ≤ C := (hq0 alpha0).trans (hqC alpha0)
  have hlam0 : 0 < lam := hC0.trans_lt hlam
  have hratio0 : 0 ≤ C / lam := div_nonneg hC0 hlam0.le
  have hratio1 : C / lam < 1 := (div_lt_one hlam0).mpr hlam
  have hdEq : d = fun x ↦ -R (fun y ↦ q y * d y) x := by
    have hqXm : Measurable (fun x ↦ q x * X f x) := hq.mul hXm
    have hqYm : Measurable (fun x ↦ q x * Y f x) := hq.mul hYm
    have hqXBound : ∃ E, ∀ x, |q x * X f x| ≤ E := by
      refine ⟨C * |DX|, fun x ↦ ?_⟩
      rw [abs_mul]
      exact mul_le_mul (by simpa only [abs_of_nonneg (hq0 x)] using hqC x)
        ((hDX x).trans (le_abs_self _)) (abs_nonneg _) hC0
    have hqYBound : ∃ E, ∀ x, |q x * Y f x| ≤ E := by
      refine ⟨C * |DY|, fun x ↦ ?_⟩
      rw [abs_mul]
      exact mul_le_mul (by simpa only [abs_of_nonneg (hq0 x)] using hqC x)
        ((hDY x).trans (le_abs_self _)) (abs_nonneg _) hC0
    have hnegMeas : Measurable (fun x ↦ -(q x * Y f x)) := hqYm.neg
    have hnegBound : ∃ E, ∀ x, |-(q x * Y f x)| ≤ E := by
      simpa only [abs_neg] using hqYBound
    have hRsum := hR_add hqXm hnegMeas hqXBound hnegBound
    have hzeroMeas : Measurable (fun _ : alpha ↦ (0 : ℝ)) := measurable_const
    have hzeroBound : ∃ E : ℝ, ∀ x : alpha, |(0 : ℝ)| ≤ E :=
      ⟨0, fun _ ↦ by simp only [abs_zero, le_refl]⟩
    have hRzero : R (fun _ : alpha ↦ (0 : ℝ)) = 0 := by
      have h := hR_add hzeroMeas hzeroMeas hzeroBound hzeroBound
      rw [show (fun _ : alpha ↦ (0 : ℝ)) + (fun _ ↦ 0) = fun _ ↦ 0 by
        funext x
        simp only [Pi.add_apply, zero_add]] at h
      funext x
      have hx := congrFun h x
      simp only [Pi.add_apply] at hx
      change R (fun _ ↦ 0) x = (0 : ℝ)
      linarith only [hx]
    have hRneg : R (fun x ↦ -(q x * Y f x)) = -R (fun x ↦ q x * Y f x) := by
      have hcancel := hR_add hqYm hnegMeas hqYBound hnegBound
      rw [show (fun x ↦ q x * Y f x) + (fun x ↦ -(q x * Y f x)) = fun _ ↦ 0 by
        funext x
        simp only [Pi.add_apply, add_neg_cancel], hRzero] at hcancel
      funext x
      have hx := congrFun hcancel x
      simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hx ⊢
      linarith only [hx]
    funext x
    have hpoint := congrFun hRsum x
    have hnegPoint := congrFun hRneg x
    simp only [Pi.add_apply, Pi.neg_apply] at hpoint hnegPoint
    have hinput : (fun y ↦ q y * (X f y - Y f y)) =
        (fun y ↦ q y * X f y) + fun y ↦ -(q y * Y f y) := by
      funext y
      simp only [Pi.add_apply]
      ring
    have hRdiff : R (fun y ↦ q y * (X f y - Y f y)) x =
        R (fun y ↦ q y * X f y) x - R (fun y ↦ q y * Y f y) x := by
      rw [hinput, hpoint]
      have hn : R (fun y ↦ -(q y * Y f y)) x =
          -R (fun y ↦ q y * Y f y) x := by
        exact hnegPoint
      rw [hn]
      ring
    dsimp only [d]
    change X f x - Y f x = -R (fun y ↦ q y * (X f y - Y f y)) x
    calc
      X f x - Y f x =
          (R f x - R (fun y ↦ q y * X f y) x) -
            (R f x - R (fun y ↦ q y * Y f y) x) := by
        rw [congrFun hXeq x, congrFun hYeq x]
        simp only [Pi.sub_apply]
      _ = -R (fun y ↦ q y * (X f y - Y f y)) x := by
        rw [hRdiff]
        ring
  have himprove : ∀ {B : ℝ}, 0 ≤ B → (∀ x, |d x| ≤ B) →
      ∀ x, |d x| ≤ (C / lam) * B := by
    intro B hB hdB x
    have hprodMeas : Measurable (fun y ↦ q y * d y) := hq.mul hdMeas
    have hprodBound : ∀ y, |q y * d y| ≤ C * B := by
      intro y
      rw [abs_mul, abs_of_nonneg (hq0 y)]
      exact mul_le_mul (hqC y) (hdB y) (abs_nonneg _) hC0
    rw [congrFun hdEq x, abs_neg]
    calc
      |R (fun y ↦ q y * d y) x| ≤ C * B / lam :=
        hR_bound hprodMeas hprodBound x
      _ = (C / lam) * B := by field_simp
  have hd0 := function_eq_zero_of_geometric_bound hratio0 hratio1
    (add_nonneg (abs_nonneg _) (abs_nonneg _)) himprove hdBound
  exact sub_eq_zero.mp hd0

/-- **Equality of resolvent families from equality at large shifts.**  Let `X` and `Y` be
families of maps on bounded measurable real functions. Suppose `X` is additive and satisfies the
bound `|X_λ f| ≤ D / λ`, while both families preserve measurability and boundedness. If both
satisfy the resolvent identity and agree on bounded measurable functions above a fixed threshold,
then they agree on bounded measurable functions at every positive shift.

The large-shift equality need only hold at the bounded measurable arguments used by the proof. -/
theorem resolventFamily_eq_of_eventually
    (X Y : ℝ → (alpha → ℝ) → alpha → ℝ) (C : ℝ)
    (hX_add : ∀ {lam : ℝ}, 0 < lam → ∀ {f g : alpha → ℝ},
      Measurable f → Measurable g → (∃ D, ∀ x, |f x| ≤ D) →
      (∃ D, ∀ x, |g x| ≤ D) → X lam (f + g) = X lam f + X lam g)
    (hX_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (X lam f))
    (hY_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (Y lam f))
    (hX_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      ∀ {D : ℝ}, (∀ x, |f x| ≤ D) → ∀ x, |X lam f x| ≤ D / lam)
    (hY_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → ∃ D, ∀ x, |Y lam f x| ≤ D)
    (hX_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X mu f = X lam f + (lam - mu) • X lam (X mu f))
    (hY_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y mu f = Y lam f + (lam - mu) • Y lam (Y mu f))
    (hlarge : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {g : alpha → ℝ}, Measurable g →
      (∃ D, ∀ x, |g x| ≤ D) → X lam g = Y lam g) {mu : ℝ} (hmu : 0 < mu)
    {f : alpha → ℝ} (hfMeas : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    X mu f = Y mu f := by
  let lam : ℝ := max C mu + 1
  have hClam : C < lam := (le_max_left C mu).trans_lt (lt_add_of_pos_right _ zero_lt_one)
  have hmulam : mu < lam := (le_max_right C mu).trans_lt (lt_add_of_pos_right _ zero_lt_one)
  have hlam : 0 < lam := hmu.trans hmulam
  have hfBound : ∃ E, ∀ x, |f x| ≤ E := ⟨D, hfD⟩
  have hXm : Measurable (X mu f) := hX_meas hmu hfMeas hfBound
  have hYm : Measurable (Y mu f) := hY_meas hmu hfMeas hfBound
  have hDX := hX_bound hmu hfMeas hfD
  obtain ⟨EY, hEY⟩ := hY_bound hmu hfMeas hfBound
  let d : alpha → ℝ := X mu f - Y mu f
  have hdMeas : Measurable d := hXm.sub hYm
  have hdBound : ∀ x, |d x| ≤ D / mu + EY := by
    intro x
    exact (abs_sub _ _).trans (add_le_add (hDX x) (hEY x))
  let alpha0 : alpha := Classical.choice inferInstance
  have hDmu0 : 0 ≤ D / mu := by
    have hD0 : 0 ≤ D := (abs_nonneg (f alpha0)).trans (hfD alpha0)
    exact div_nonneg hD0 hmu.le
  have hEY0 : 0 ≤ EY := (abs_nonneg (Y mu f alpha0)).trans (hEY alpha0)
  have hdEq : d = (lam - mu) • X lam d := by
    have hXid := hX_resolvent hmu hlam hfMeas hfBound
    have hYid := hY_resolvent hmu hlam hfMeas hfBound
    have hXYf := hlarge hClam hlam hfMeas hfBound
    have hXYY := hlarge hClam hlam hYm ⟨EY, hEY⟩
    rw [← hXYf, ← hXYY] at hYid
    have hzeroMeas : Measurable (fun _ : alpha ↦ (0 : ℝ)) := measurable_const
    have hzeroBound : ∃ E : ℝ, ∀ x : alpha, |(0 : ℝ)| ≤ E :=
      ⟨0, fun _ ↦ by simp only [abs_zero, le_refl]⟩
    have hXzero : X lam (fun _ ↦ 0) = 0 := by
      have h := hX_add hlam hzeroMeas hzeroMeas hzeroBound hzeroBound
      have hzadd : (fun _ : alpha ↦ (0 : ℝ)) + (fun _ ↦ 0) = fun _ ↦ 0 := by
        funext x
        simp only [Pi.add_apply, zero_add]
      rw [hzadd] at h
      funext x
      have hx := congrFun h x
      simp only [Pi.add_apply] at hx
      change X lam (fun _ ↦ 0) x = (0 : ℝ)
      linarith only [hx]
    have hnegBound : ∃ E, ∀ x, |-(Y mu f x)| ≤ E :=
      ⟨EY, fun x ↦ by simpa only [abs_neg] using hEY x⟩
    have hnegMeas : Measurable (fun x ↦ -(Y mu f x)) := hYm.neg
    have hsum := hX_add hlam hXm hnegMeas ⟨D / mu, hDX⟩ hnegBound
    have hneg : X lam (fun x ↦ -(Y mu f x)) = -X lam (Y mu f) := by
      have hcancel := hX_add hlam hYm hnegMeas ⟨EY, hEY⟩ hnegBound
      rw [show (Y mu f + fun x ↦ -(Y mu f x)) = fun _ ↦ 0 by
        funext x
        simp only [Pi.add_apply, add_neg_cancel]] at hcancel
      rw [hXzero] at hcancel
      funext x
      have hx := congrFun hcancel x
      simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hx ⊢
      linarith only [hx]
    funext x
    have hsumx := congrFun hsum x
    have hnegx := congrFun hneg x
    have hXx := congrFun hXid x
    have hYx := congrFun hYid x
    dsimp only [d]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsumx hXx hYx ⊢
    change X lam (fun z ↦ -(Y mu f z)) x = -X lam (Y mu f) x at hnegx
    rw [show X mu f - Y mu f = X mu f + fun z ↦ -(Y mu f z) by
      funext z
      simp only [Pi.sub_apply, Pi.add_apply]
      ring]
    rw [hsumx, hnegx]
    rw [hXx, hYx]
    ring
  have hratio0 : 0 ≤ (lam - mu) / lam :=
    div_nonneg (sub_nonneg.mpr hmulam.le) hlam.le
  have hratio1 : (lam - mu) / lam < 1 := (div_lt_one hlam).mpr (sub_lt_self lam hmu)
  have himprove : ∀ {B : ℝ}, 0 ≤ B → (∀ x, |d x| ≤ B) →
      ∀ x, |d x| ≤ ((lam - mu) / lam) * B := by
    intro B hB hdB x
    rw [congrFun hdEq x, Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr hmulam.le)]
    calc
      (lam - mu) * |X lam d x| ≤ (lam - mu) * (B / lam) :=
        mul_le_mul_of_nonneg_left (hX_bound hlam hdMeas hdB x)
          (sub_nonneg.mpr hmulam.le)
      _ = ((lam - mu) / lam) * B := by field_simp
  have hd0 := function_eq_zero_of_geometric_bound hratio0 hratio1
    (add_nonneg hDmu0 hEY0) himprove hdBound
  exact sub_eq_zero.mp hd0

/-- **Equality of perturbed resolvent families.**  Two resolvent families that satisfy the same
bounded perturbation equation above the potential bound agree on every bounded measurable
function at every positive shift. The first family must be additive and contractive; the second
need only preserve boundedness. Both preserve measurability and satisfy the resolvent identity. -/
theorem perturbed_eq_of_resolventFamilies
    (R X Y : ℝ → (alpha → ℝ) → alpha → ℝ) {q : alpha → ℝ} {C : ℝ}
    (hR_add : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f g : alpha → ℝ},
      Measurable f → Measurable g → (∃ D, ∀ x, |f x| ≤ D) →
      (∃ D, ∀ x, |g x| ≤ D) → R lam (f + g) = R lam f + R lam g)
    (hR_bound : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → ∀ {D : ℝ}, (∀ x, |f x| ≤ D) →
      ∀ x, |R lam f x| ≤ D / lam)
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (hqC : ∀ x, q x ≤ C)
    (hX_add : ∀ {lam : ℝ}, 0 < lam → ∀ {f g : alpha → ℝ},
      Measurable f → Measurable g → (∃ D, ∀ x, |f x| ≤ D) →
      (∃ D, ∀ x, |g x| ≤ D) → X lam (f + g) = X lam f + X lam g)
    (hX_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (X lam f))
    (hY_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (Y lam f))
    (hX_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      ∀ {D : ℝ}, (∀ x, |f x| ≤ D) → ∀ x, |X lam f x| ≤ D / lam)
    (hY_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → ∃ D, ∀ x, |Y lam f x| ≤ D)
    (hX_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X mu f = X lam f + (lam - mu) • X lam (X mu f))
    (hY_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y mu f = Y lam f + (lam - mu) • Y lam (Y mu f))
    (hX_fixed : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X lam f = R lam f - R lam (fun x ↦ q x * X lam f x))
    (hY_fixed : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y lam f = R lam f - R lam (fun x ↦ q x * Y lam f x))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    X lam f = Y lam f := by
  apply resolventFamily_eq_of_eventually X Y C hX_add hX_meas hY_meas
    hX_bound hY_bound hX_resolvent hY_resolvent _ hlam hf hfD
  intro mu hCmu hmu g hg hgb
  obtain ⟨E, hgE⟩ := hgb
  exact perturbed_unique (R mu) (X mu) (Y mu) (hR_add hCmu hmu)
    (hR_bound hCmu hmu) hq hq0 hqC hCmu (hX_meas hmu) (hY_meas hmu)
    (fun hf' hf'b ↦ by
      obtain ⟨E', hfE'⟩ := hf'b
      exact ⟨E' / mu, hX_bound hmu hf' hfE'⟩)
    (hY_bound hmu)
    (hX_fixed hCmu hmu) (hY_fixed hCmu hmu) hg hgE

end

end MarkovProcess

end PortComputability
