/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Data.Nat.Choose.Multinomial

/-! # Coefficients of Carlson's R-polynomials

Home for Carlson's Section 6.2: multi-index coefficients, zero specializations, and termination.
-/

open Complex Finset
@[expose] public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The coefficient form of the multinomial theorem for Carlson's homogeneous power
polynomial.  This is the algebraic core of Carlson's representation 6.2-1. -/
theorem coeff_carlsonPowerPolynomial (n : ℕ) (z : ι → ℂ) (m : ι →₀ ℕ) :
    (carlsonPowerPolynomial n z).coeff m =
      if m.sum (fun _ e ↦ e) = n then
        (m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e)
      else 0 := by
  rw [carlsonPowerPolynomial]
  have hlinear : carlsonAffinePolynomial z =
      ∑ i, z i • (MvPolynomial.X i : MvPolynomial ι ℂ) := by
    simp [carlsonAffinePolynomial, Algebra.smul_def]
  rw [hlinear, MvPolynomial.coeff_linearCombination_X_pow_of_fintype]

/-- Only multi-indices of total degree `n` can occur in Carlson's degree-`n` power
polynomial. -/
theorem coeff_carlsonPowerPolynomial_eq_zero_of_sum_ne (n : ℕ) (z : ι → ℂ)
    (m : ι →₀ ℕ) (hm : m.sum (fun _ e ↦ e) ≠ n) :
    (carlsonPowerPolynomial n z).coeff m = 0 := by
  simp [coeff_carlsonPowerPolynomial, hm]

/-- Carlson's regularized polynomial written as the finite sum of its total-degree `n`
multi-index terms. -/
theorem regCarlsonRPolynomial_eq_sum_support (n : ℕ) (b z : ι → ℂ) :
    regCarlsonRPolynomial n b z =
      ∑ m ∈ (carlsonPowerPolynomial n z).support,
        ((m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e)) *
          regDirichletMonomialTransform (m : ι → ℕ) b := by
  unfold regCarlsonRPolynomial regDirichletMvPolynomialTransform
  apply Finset.sum_congr rfl
  intro m hm
  have hmdeg : m.sum (fun _ e ↦ e) = n := by
    by_contra hne
    have hz := coeff_carlsonPowerPolynomial_eq_zero_of_sum_ne n z m hne
    exact (MvPolynomial.mem_support_iff.mp hm) hz
  rw [coeff_carlsonPowerPolynomial]
  simp [hmdeg]

/-- Carlson's regularized polynomial written explicitly in Pochhammer--Gamma form. -/
theorem regCarlsonRPolynomial_eq_pochhammer_sum (n : ℕ) (b z : ι → ℂ) :
    regCarlsonRPolynomial n b z =
      ∑ m ∈ (carlsonPowerPolynomial n z).support,
        ((m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e)) *
          ((∏ i, (ascPochhammer ℂ (m i)).eval (b i)) *
            (Gamma (∑ i, (b i + m i : ℂ)))⁻¹) := by
  rw [regCarlsonRPolynomial_eq_sum_support]
  apply Finset.sum_congr rfl
  intro m _
  rw [regDirichletMonomialTransform_eq]

/-- The Pochhammer numerator of Carlson's degree-`n` R-polynomial.

Carlson's usual polynomial is obtained by dividing this expression by
`(∑ i, b i)ₙ`.  Keeping the numerator separate makes transformation identities valid
without exclusions at zeros of that Pochhammer symbol. -/
def carlsonRPolynomialNumerator (n : ℕ) (b z : ι → ℂ) : ℂ :=
  ∑ m ∈ (carlsonPowerPolynomial n z).support,
    (m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e) *
      ∏ i, (ascPochhammer ℂ (m i)).eval (b i)

/-- The Pochhammer numerator of the degree-zero R-polynomial is one. -/
@[simp] theorem carlsonRPolynomialNumerator_zero (b z : ι → ℂ) :
    carlsonRPolynomialNumerator 0 b z = 1 := by
  simp [carlsonRPolynomialNumerator, carlsonPowerPolynomial, Finsupp.multinomial]

/-- The Pochhammer numerator in degree one is the weighted linear form
`∑ i, b i * z i`, as in Carlson's formula 5.7(2). -/
theorem carlsonRPolynomialNumerator_one (b z : ι → ℂ) :
    carlsonRPolynomialNumerator 1 b z = ∑ i, b i * z i := by
  rw [carlsonRPolynomialNumerator]
  calc
    (∑ m ∈ (carlsonPowerPolynomial 1 z).support,
        (m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e) *
          ∏ i, (ascPochhammer ℂ (m i)).eval (b i)) =
      Finsupp.sum (AddMonoidAlgebra.coeff (carlsonPowerPolynomial 1 z)) fun m c =>
        c * ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
          rw [MvPolynomial.sum_def]
          apply Finset.sum_congr rfl
          intro m hm
          have hmdeg : m.sum (fun _ e ↦ e) = 1 := by
            by_contra hne
            exact (MvPolynomial.mem_support_iff.mp hm)
              (coeff_carlsonPowerPolynomial_eq_zero_of_sum_ne 1 z m hne)
          rw [coeff_carlsonPowerPolynomial]
          simp [hmdeg]
    _ = ∑ i, b i * z i := by
      rw [show carlsonPowerPolynomial 1 z =
          ∑ i, MvPolynomial.C (z i) * MvPolynomial.X i by
        simp [carlsonPowerPolynomial, carlsonAffinePolynomial]]
      have hcoeff : AddMonoidAlgebra.coeff
          (∑ i, MvPolynomial.C (z i) * MvPolynomial.X i) =
          ∑ i, AddMonoidAlgebra.coeff
            (MvPolynomial.C (z i) * MvPolynomial.X i) := by
        simp
      rw [hcoeff]
      rw [← Finsupp.sum_finsetSum_index (s := Finset.univ)
        (g := fun i => AddMonoidAlgebra.coeff
          (MvPolynomial.C (z i) * MvPolynomial.X i))]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [MvPolynomial.C_mul_X_eq_monomial]
        change (Finsupp.single (Finsupp.single i 1) (z i)).sum
          (fun m c => c * ∏ j, (ascPochhammer ℂ (m j)).eval (b j)) = b i * z i
        rw [Finsupp.sum_single_index]
        have hp : (∏ j, (ascPochhammer ℂ ((Finsupp.single i 1) j)).eval (b j)) = b i := by
          rw [Finset.prod_eq_single i]
          · simp
          · intro j _ hji
            simp [hji.symm]
          · simp
        rw [hp]
        ring
        simp
      · intro m
        simp
      · intro m c d
        ring

/-- The regularized Carlson polynomial is its Pochhammer numerator times the reciprocal
Gamma factor at the translated total parameter. -/
theorem regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma
    (n : ℕ) (b z : ι → ℂ) :
    regCarlsonRPolynomial n b z =
      carlsonRPolynomialNumerator n b z * (Gamma ((∑ i, b i) + n))⁻¹ := by
  rw [regCarlsonRPolynomial_eq_pochhammer_sum]
  unfold carlsonRPolynomialNumerator
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  have hmdeg : m.sum (fun _ e ↦ e) = n := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hm)
      (coeff_carlsonPowerPolynomial_eq_zero_of_sum_ne n z m hne)
  have hsum : ∑ i, (b i + m i : ℂ) = (∑ i, b i) + n := by
    rw [Finset.sum_add_distrib]
    congr 1
    have hmfun : ∑ i, m i = n := by
      rw [← m.sum_fintype (fun _ e ↦ e) (fun _ ↦ rfl)]
      exact hmdeg
    exact_mod_cast hmfun
  rw [hsum]
  ring

/-- Carlson's degree-zero power polynomial is the constant polynomial one. -/
@[simp] theorem carlsonPowerPolynomial_zero (z : ι → ℂ) :
    carlsonPowerPolynomial 0 z = 1 := by
  simp [carlsonPowerPolynomial]

/-- Carlson's degree-one power polynomial is its defining affine polynomial. -/
@[simp] theorem carlsonPowerPolynomial_one (z : ι → ℂ) :
    carlsonPowerPolynomial 1 z = carlsonAffinePolynomial z := by
  simp [carlsonPowerPolynomial]

/-- The regularized Carlson polynomial of degree zero is the reciprocal Gamma factor. -/
@[simp] theorem regCarlsonRPolynomial_zero (b z : ι → ℂ) :
    regCarlsonRPolynomial 0 b z = (Gamma (∑ i, b i))⁻¹ := by
  simp [regCarlsonRPolynomial, regDirichletMvPolynomialTransform]
  change regDirichletMonomialTransform (fun _ ↦ 0) b = (Gamma (∑ i, b i))⁻¹
  exact regDirichletMonomialTransform_zero b

/-- If all Carlson variables vanish, every positive-degree Carlson polynomial vanishes. -/
@[simp] theorem regCarlsonRPolynomial_zero_variables (b : ι → ℂ) {n : ℕ} (hn : n ≠ 0) :
    regCarlsonRPolynomial n b (fun _ ↦ 0) = 0 := by
  rw [regCarlsonRPolynomial]
  have hp : carlsonPowerPolynomial n (fun _ : ι ↦ (0 : ℂ)) = 0 := by
    simp [carlsonPowerPolynomial, carlsonAffinePolynomial, hn]
  rw [hp]
  simp [regDirichletMvPolynomialTransform]

open scoped Classical in
/-- Reindexing the degree-`n` Finsupp antidiagonal along `Finsupp.equivFunOnFinite`. -/
theorem map_equivFunOnFinite_piAntidiag_univ (n : ℕ) :
    (piAntidiag (univ : Finset ι) n).map
      ⟨Finsupp.equivFunOnFinite.symm, Equiv.injective _⟩ =
      finsuppAntidiag (univ : Finset ι) n := by
  apply Finset.ext
  intro m
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_piAntidiag,
    mem_finsuppAntidiag]
  constructor
  · rintro ⟨f, ⟨hfsum, _⟩, rfl⟩
    refine ⟨?_, subset_univ _⟩
    simpa [Finsupp.equivFunOnFinite] using hfsum
  · intro ⟨hsum, _⟩
    refine ⟨(m : ι → ℕ), ⟨hsum, fun _ _ => mem_univ _⟩, ?_⟩
    exact Finsupp.equivFunOnFinite.symm_apply_apply m

open scoped Classical in
/-- The Pochhammer numerator is the complete degree-`n` multinomial expansion. -/
theorem carlsonRPolynomialNumerator_eq_multinomial_sum (n : ℕ) (b z : ι → ℂ) :
    carlsonRPolynomialNumerator n b z =
      ∑ m ∈ piAntidiag (univ : Finset ι) n,
        (Nat.multinomial univ m : ℂ) * (∏ i, z i ^ m i) *
          ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
  unfold carlsonRPolynomialNumerator
  have hsub : (carlsonPowerPolynomial n z).support ⊆
      finsuppAntidiag (univ : Finset ι) n := by
    intro m hm
    have hdeg : m.sum (fun _ e ↦ e) = n := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hm)
        (coeff_carlsonPowerPolynomial_eq_zero_of_sum_ne n z m hne)
    refine (mem_finsuppAntidiag (s := univ) (n := n) (f := m)).2 ⟨?_, subset_univ _⟩
    have : univ.sum (m : ι → ℕ) = m.sum (fun _ e ↦ e) := by
      simpa using
        (Finsupp.sum_of_support_subset m (subset_univ m.support)
          (fun _ e ↦ e) (fun _ _ ↦ rfl)).symm
    exact this.trans hdeg
  have hsum :
      ∑ m ∈ (carlsonPowerPolynomial n z).support,
          (m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e) *
            ∏ i, (ascPochhammer ℂ (m i)).eval (b i) =
        ∑ m ∈ finsuppAntidiag (univ : Finset ι) n,
          (m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e) *
            ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
    apply Finset.sum_subset hsub
    intro m hm hn
    have hdeg : univ.sum (m : ι → ℕ) = n :=
      (mem_finsuppAntidiag.mp hm).1
    have hcoeff := coeff_carlsonPowerPolynomial n z m
    have hz : (carlsonPowerPolynomial n z).coeff m = 0 :=
      MvPolynomial.notMem_support_iff.mp hn
    have hsum' : m.sum (fun _ e ↦ e) = n := by
      have : univ.sum (m : ι → ℕ) = m.sum (fun _ e ↦ e) := by
        simpa using
          (Finsupp.sum_of_support_subset m (subset_univ m.support)
            (fun _ e ↦ e) (fun _ _ ↦ rfl)).symm
      exact this.symm.trans hdeg
    simp only [hsum', ↓reduceIte] at hcoeff
    have : (m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e) = 0 :=
      hcoeff ▸ hz
    rw [this, zero_mul]
  rw [hsum, ← map_equivFunOnFinite_piAntidiag_univ, sum_map]
  apply sum_congr rfl
  intro f hf
  simp only [Function.Embedding.coeFn_mk]
  have hsupp : (Finsupp.equivFunOnFinite.symm f).support ⊆ univ := subset_univ _
  rw [Finsupp.multinomial_eq_of_support_subset hsupp]
  have hprod :
      (Finsupp.equivFunOnFinite.symm f).prod (fun i e ↦ z i ^ e) =
        ∏ i, z i ^ f i := by
    rw [Finsupp.prod_of_support_subset _ hsupp (fun i e ↦ z i ^ e) (by simp)]
    simp
  simp [hprod]

/-- Regularized Carlson polynomials preserve analytic dependence jointly in
their nodes and Dirichlet parameters. -/
theorem analyticAt_regCarlsonR_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x : E} {b z : E → ι → ℂ}
    (hb : ∀ i, AnalyticAt ℂ (fun y => b y i) x)
    (hz : ∀ i, AnalyticAt ℂ (fun y => z y i) x) (n : ℕ) :
    AnalyticAt ℂ (fun y => regCarlsonR n (z y) (b y)) x := by
  simp only [regCarlsonR, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
    carlsonRPolynomialNumerator_eq_multinomial_sum]
  apply AnalyticAt.mul
  · apply Finset.analyticAt_fun_sum
    intro m _
    refine (analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i _ => (hz i).pow _))).mul ?_
    exact Finset.analyticAt_fun_prod _ (fun i _ =>
      ((AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ (m i))) _
        (Set.mem_univ _)).comp (hb i))
  · have hsum : AnalyticAt ℂ (fun y => (∑ i, b y i) + n) x :=
      (Finset.analyticAt_fun_sum _ (fun i _ => hb i)).add analyticAt_const
    exact (Complex.differentiable_one_div_Gamma.analyticAt (z := (∑ i, b x i) + n)).comp_of_eq
      hsum rfl

end DirichletTransform
end CarlsonRPolynomial
