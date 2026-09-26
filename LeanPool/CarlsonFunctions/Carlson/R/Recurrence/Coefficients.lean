/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Pochhammer.Gamma
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Analysis.Analytic.Polynomial

/-! # Coefficient algebra for Carlson's homogeneity recurrence -/

open Complex
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The `n`th elementary symmetric polynomial evaluated at the Carlson variables. -/
def carlsonElementarySymmetric (n : ℕ) (z : ι → ℂ) : ℂ :=
  (MvPolynomial.esymm ι ℂ n).eval z

/-- The finite generating polynomial for the elementary symmetric coefficients. -/
theorem carlsonElementarySymmetric_generating_polynomial (w : ℂ) :
    (∏ i : ι, (1 + MvPolynomial.C w * MvPolynomial.X i)) =
      ∑ n ∈ Finset.range (Fintype.card ι + 1),
        MvPolynomial.C (w ^ n) * MvPolynomial.esymm ι ℂ n := by
  rw [Finset.prod_one_add, Finset.sum_powerset]
  simp only [Finset.card_univ]
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.esymm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hs).2, map_pow]

/-- Euler's identity for an elementary symmetric polynomial. -/
theorem carlsonElementarySymmetric_euler (n : ℕ) (z : ι → ℂ) :
    ∑ i, z i * (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z =
      n * carlsonElementarySymmetric n z := by
  have hhom : (MvPolynomial.esymm ι ℂ n).IsHomogeneous n := by
    unfold MvPolynomial.esymm
    apply MvPolynomial.IsHomogeneous.sum
    intro s hs
    have H := MvPolynomial.IsHomogeneous.prod s (fun i => MvPolynomial.X i) (fun _ => 1)
      (fun i _ => MvPolynomial.isHomogeneous_X ℂ i)
    simpa [(Finset.mem_powersetCard.mp hs).2] using H
  have H := congrArg (MvPolynomial.eval z) hhom.sum_X_mul_pderiv
  simpa [carlsonElementarySymmetric, nsmul_eq_mul] using H

open scoped Classical in
/-- Differentiating the generating polynomial with respect to one Carlson variable. -/
theorem carlsonElementarySymmetric_generating_pderiv (w : ℂ) (z : ι → ℂ) (i : ι) :
    w * (∏ j ∈ Finset.univ.erase i, (1 + w * z j)) =
      ∑ n ∈ Finset.range (Fintype.card ι + 1),
        w ^ n * (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z := by
  have hz (s : Finset ι) (hi : i ∉ s) :
      MvPolynomial.pderiv i (∏ j ∈ s, (1 + MvPolynomial.C w * MvPolynomial.X j)) = 0 := by
    induction s using Finset.induction with
    | empty => simp
    | @insert j s hj ih =>
      simp only [Finset.mem_insert, not_or] at hi
      simp [hj, Derivation.leibniz, ih hi.2, hi.1, smul_eq_mul]
  have H := congrArg (MvPolynomial.pderiv i)
    (carlsonElementarySymmetric_generating_polynomial (ι := ι) w)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Derivation.leibniz] at H
  simp only [hz _ (Finset.notMem_erase _ _), smul_zero, zero_add] at H
  have H' := congrArg (MvPolynomial.eval z) H
  simpa [Derivation.leibniz, smul_eq_mul, mul_comm] using H'

open scoped Classical in
/-- The polynomial factor in the differentiated ray kernel, expanded as in (8.4-6). -/
theorem carlsonAssociatedRecurrenceKernel_polynomial (a w : ℂ) (b z : ι → ℂ) :
    a * (∏ i, (1 + w * z i)) + w *
        ∑ i, (1 - b i) * z i * ∏ j ∈ Finset.univ.erase i, (1 + w * z j) =
      ∑ n ∈ Finset.range (Fintype.card ι + 1), w ^ n *
        ((a + n) * carlsonElementarySymmetric n z -
          ∑ i, b i * z i * (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z) := by
  have hg : (∏ i, (1 + w * z i)) =
      ∑ n ∈ Finset.range (Fintype.card ι + 1), w ^ n * carlsonElementarySymmetric n z := by
    simpa [carlsonElementarySymmetric] using
      congrArg (MvPolynomial.eval z) (carlsonElementarySymmetric_generating_polynomial (ι := ι) w)
  have hd (i : ι) : w * ((1 - b i) * z i *
      ∏ j ∈ Finset.univ.erase i, (1 + w * z j)) =
      ∑ n ∈ Finset.range (Fintype.card ι + 1), w ^ n * ((1 - b i) * z i *
        (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z) := by
    rw [show w * ((1 - b i) * z i * ∏ j ∈ Finset.univ.erase i, (1 + w * z j)) =
      ((1 - b i) * z i) * (w * ∏ j ∈ Finset.univ.erase i, (1 + w * z j)) by ring,
      carlsonElementarySymmetric_generating_pderiv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hg, Finset.mul_sum, Finset.mul_sum]
  simp_rw [hd]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.mul_sum]
  have he : (∑ i, (1 - b i) * z i *
      (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z) =
      n * carlsonElementarySymmetric n z -
        ∑ i, b i * z i * (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z := by
    simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
    rw [carlsonElementarySymmetric_euler]
  rw [he]
  ring

/-- Carlson's coefficient `Aₙ` from Relation 8.4-1 in its displayed quotient form.
`eval_carlsonAssociatedRecurrencePolynomial` identifies its polynomial form away from
the two displayed denominators. -/
def carlsonAssociatedRecurrenceCoeff
    (n : ℕ) (a a' : ℂ) (b z : ι → ℂ) : ℂ :=
  (ascPochhammer ℂ n).eval a *
    (ascPochhammer ℂ (Fintype.card ι - n)).eval (a' - Fintype.card ι) /
      (a * (a' - Fintype.card ι)) *
    ((a + n) * carlsonElementarySymmetric n z -
      ∑ i, b i * z i * (MvPolynomial.pderiv i
        (MvPolynomial.esymm ι ℂ n)).eval z)

/-- The top elementary symmetric polynomial is the product of all variables. -/
theorem carlsonElementarySymmetric_card (z : ι → ℂ) :
    carlsonElementarySymmetric (Fintype.card ι) z = ∏ i, z i := by
  simp [carlsonElementarySymmetric, MvPolynomial.esymm,
    ← Finset.card_univ, Finset.powersetCard_self]

private lemma X_mul_pderiv_esymm_card (i : ι) :
    MvPolynomial.X i * MvPolynomial.pderiv i
      (MvPolynomial.esymm ι ℂ (Fintype.card ι)) =
        MvPolynomial.esymm ι ℂ (Fintype.card ι) := by
  have he : MvPolynomial.esymm ι ℂ (Fintype.card ι) =
      MvPolynomial.monomial (∑ j : ι, Finsupp.single j 1) (1 : ℂ) := by
    simp [MvPolynomial.esymm, ← Finset.card_univ, Finset.powersetCard_self,
      MvPolynomial.monomial_sum_one, MvPolynomial.X]
  rw [he, MvPolynomial.X_mul_pderiv_monomial]
  simp

/-- Carlson's last coefficient has a removable singularity at `a' = card ι`. -/
theorem carlsonAssociatedRecurrenceCoeff_card [Nonempty ι]
    {a a' : ℂ} {b z : ι → ℂ}
    (hsum : a + a' = ∑ i, b i) (ha : a ≠ 0)
    (ha' : a' ≠ Fintype.card ι) :
    carlsonAssociatedRecurrenceCoeff (Fintype.card ι) a a' b z =
      -(ascPochhammer ℂ (Fintype.card ι - 1)).eval (a + 1) * ∏ i, z i := by
  have hcard : Fintype.card ι = (Fintype.card ι - 1) + 1 :=
    (Nat.sub_add_cancel Fintype.card_pos).symm
  have hp : (ascPochhammer ℂ (Fintype.card ι)).eval a =
      a * (ascPochhammer ℂ (Fintype.card ι - 1)).eval (a + 1) := by
    conv_lhs => rw [hcard, ascPochhammer_succ_left]
    simp
  have hd (i : ι) : z i * (MvPolynomial.pderiv i
      (MvPolynomial.esymm ι ℂ (Fintype.card ι))).eval z = ∏ j, z j := by
    have h := congrArg (MvPolynomial.eval z) (X_mul_pderiv_esymm_card (ι := ι) i)
    simp only [map_mul, MvPolynomial.eval_X] at h
    exact h.trans (carlsonElementarySymmetric_card z)
  have hs : (∑ i, b i * z i * (MvPolynomial.pderiv i
      (MvPolynomial.esymm ι ℂ (Fintype.card ι))).eval z) =
      (a + a') * ∏ j, z j := by
    simp_rw [mul_assoc, hd]
    rw [← Finset.sum_mul, hsum]
  simp only [carlsonAssociatedRecurrenceCoeff, Nat.sub_self, ascPochhammer_zero,
    Polynomial.eval_one, mul_one, hp, carlsonElementarySymmetric_card, hs]
  field_simp
  ring

/-- Carlson's first coefficient has a removable singularity at `a = 0`. -/
theorem carlsonAssociatedRecurrenceCoeff_zero [Nonempty ι]
    {a a' : ℂ} (b z : ι → ℂ) (ha : a ≠ 0) (ha' : a' ≠ Fintype.card ι) :
    carlsonAssociatedRecurrenceCoeff 0 a a' b z =
      (ascPochhammer ℂ (Fintype.card ι - 1)).eval (a' - Fintype.card ι + 1) := by
  have hcard : Fintype.card ι = (Fintype.card ι - 1) + 1 :=
    (Nat.sub_add_cancel Fintype.card_pos).symm
  have hp : (ascPochhammer ℂ (Fintype.card ι)).eval (a' - Fintype.card ι) =
      (a' - Fintype.card ι) *
        (ascPochhammer ℂ (Fintype.card ι - 1)).eval (a' - Fintype.card ι + 1) := by
    have h := congrArg (Polynomial.eval (a' - Fintype.card ι))
      (ascPochhammer_succ_left ℂ (Fintype.card ι - 1))
    simpa only [← hcard, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one] using h
  simp only [carlsonAssociatedRecurrenceCoeff, Nat.sub_zero, ascPochhammer_zero,
    Polynomial.eval_one, one_mul, Nat.cast_zero, add_zero, carlsonElementarySymmetric,
    MvPolynomial.esymm_zero, MvPolynomial.pderiv_one, map_zero, mul_zero,
    Finset.sum_const_zero, sub_zero, hp]
  simp only [map_one, mul_one]
  field_simp

/-- The division-free polynomial coefficient in Carlson's recurrence for a nonempty index
type, including its removable-singularity values. The endpoint formulas are used separately
because the
corresponding factors cancel against the expression involving the symmetric polynomial. -/
def carlsonAssociatedRecurrencePolynomial
    (n : ℕ) (a a' : ℂ) (b : ι → ℂ) : MvPolynomial ι ℂ :=
  if n = 0 then
    MvPolynomial.C ((ascPochhammer ℂ (Fintype.card ι - 1)).eval
      (a' - Fintype.card ι + 1))
  else if n = Fintype.card ι then
    MvPolynomial.C (-(ascPochhammer ℂ (Fintype.card ι - 1)).eval (a + 1)) *
      MvPolynomial.esymm ι ℂ n
  else
    MvPolynomial.C ((ascPochhammer ℂ (n - 1)).eval (a + 1) *
      (ascPochhammer ℂ (Fintype.card ι - n - 1)).eval
        (a' - Fintype.card ι + 1)) *
      (MvPolynomial.C (a + n) * MvPolynomial.esymm ι ℂ n -
        ∑ i, MvPolynomial.C (b i) * MvPolynomial.X i *
          MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n))

/-- Away from the two displayed denominators, the polynomial coefficients agree with
Carlson's quotient formula. No parameter-dependent denominator remains in the polynomial. -/
theorem eval_carlsonAssociatedRecurrencePolynomial [Nonempty ι]
    {n : ℕ} (hn : n ≤ Fintype.card ι) {a a' : ℂ} {b z : ι → ℂ}
    (hsum : a + a' = ∑ i, b i) (ha : a ≠ 0) (ha' : a' ≠ Fintype.card ι) :
    (carlsonAssociatedRecurrencePolynomial n a a' b).eval z =
      carlsonAssociatedRecurrenceCoeff n a a' b z := by
  by_cases hn0 : n = 0
  · subst n
    simp [carlsonAssociatedRecurrencePolynomial,
      carlsonAssociatedRecurrenceCoeff_zero b z ha ha']
  by_cases hnk : n = Fintype.card ι
  · subst n
    simp [carlsonAssociatedRecurrencePolynomial, Fintype.card_ne_zero,
      carlsonAssociatedRecurrenceCoeff_card hsum ha ha',
      ← carlsonElementarySymmetric_card z, carlsonElementarySymmetric]
  have hp (m : ℕ) (hm : 0 < m) (w : ℂ) :
      (ascPochhammer ℂ m).eval w =
        w * (ascPochhammer ℂ (m - 1)).eval (w + 1) := by
    have h := congrArg (Polynomial.eval w) (ascPochhammer_succ_left ℂ (m - 1))
    simpa only [Nat.sub_add_cancel hm, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one] using h
  simp only [carlsonAssociatedRecurrencePolynomial, ite_eq_right hn0, ite_eq_right hnk,
    map_mul, MvPolynomial.eval_C, map_sub, map_sum, MvPolynomial.eval_X,
    carlsonAssociatedRecurrenceCoeff, carlsonElementarySymmetric,
    hp n (Nat.pos_of_ne_zero hn0), hp (Fintype.card ι - n) (by omega)]
  field_simp

/-- Polynomial recurrence coefficients depend analytically on analytic parameters. -/
theorem analyticAt_carlsonAssociatedRecurrencePolynomial_eval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x : E} {a a' : E → ℂ} {b : E → ι → ℂ}
    (ha : AnalyticAt ℂ a x) (ha' : AnalyticAt ℂ a' x)
    (hb : ∀ i, AnalyticAt ℂ (fun y ↦ b y i) x) (n : ℕ) (z : ι → ℂ) :
    AnalyticAt ℂ (fun y ↦ (carlsonAssociatedRecurrencePolynomial n
      (a y) (a' y) (b y)).eval z) x := by
  have hp (m : ℕ) {f : E → ℂ} (hf : AnalyticAt ℂ f x) :
      AnalyticAt ℂ (fun y ↦ (ascPochhammer ℂ m).eval (f y)) x :=
    ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (ascPochhammer ℂ m))
      (f x) (Set.mem_univ _)).comp_of_eq hf rfl
  simp only [carlsonAssociatedRecurrencePolynomial]
  split_ifs
  · simp only [MvPolynomial.eval_C]
    exact hp _ ((ha'.sub analyticAt_const).add analyticAt_const)
  · simp only [map_mul, MvPolynomial.eval_C]
    exact (hp _ (ha.add analyticAt_const)).neg.mul analyticAt_const
  · simp only [map_mul, map_sub, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X]
    refine ((hp _ (ha.add analyticAt_const)).mul
      (hp _ ((ha'.sub analyticAt_const).add analyticAt_const))).mul ?_
    refine ((ha.add analyticAt_const).mul analyticAt_const).sub ?_
    exact Finset.analyticAt_fun_sum _ (fun i _ ↦
      ((hb i).mul analyticAt_const).mul analyticAt_const)

end DirichletTransform
