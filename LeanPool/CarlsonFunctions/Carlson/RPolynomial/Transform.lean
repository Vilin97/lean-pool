/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.Binomial
public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.Differential

import LeanPool.CarlsonFunctions.Pochhammer.Gamma
import LeanPool.CarlsonFunctions.Pochhammer.Vandermonde

/-!
# Linear transformations of Carlson's R-polynomials

This file contains the algebraic infrastructure for [Carl77, Section 6.5].
The Pochhammer reflection identity used in the book's proof is
`Complex.ascPochhammer_eval_split_reflection` in `Pochhammer.Gamma`.
-/

open Complex Finset
@[expose] public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Scaling all Carlson variables scales their degree-`n` polynomial kernel by `a ^ n`. -/
theorem eval_carlsonPowerPolynomial_smul (n : ℕ) (a : ℂ) (z x : ι → ℂ) :
    (carlsonPowerPolynomial n (fun i ↦ a * z i)).eval x =
      a ^ n * (carlsonPowerPolynomial n z).eval x := by
  rw [carlsonPowerPolynomial_smul]
  simp

open scoped Classical in
/-- Carlson's transformed Dirichlet parameters for degree `n`, with `i` chosen as the
distinguished coordinate in Relation 6.5-3. -/
def carlsonRTransformParameters (n : ℕ) (i : ι) (b : ι → ℂ) : ι → ℂ :=
  Function.update b i (1 - (∑ j, b j) - n)

open scoped Classical in
/-- Carlson's transformed variables for Relation 6.5-3. The distinguished variable stays
fixed and every other variable is replaced by its difference from that variable. -/
def carlsonRTransformVariables (i : ι) (z : ι → ℂ) : ι → ℂ :=
  fun j => if j = i then z i else z i - z j

/-- The sum of Carlson's transformed parameters is `1 - b i - n`. -/
theorem sum_carlsonRTransformParameters (n : ℕ) (i : ι) (b : ι → ℂ) :
    ∑ j, carlsonRTransformParameters n i b j = 1 - b i - n := by
  classical
  unfold carlsonRTransformParameters
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hs : ∑ x ∈ Finset.univ \ {i}, b x + b i = ∑ x, b x := by
    simpa only [Finset.sdiff_singleton_eq_erase] using
      Finset.sum_erase_add Finset.univ b (Finset.mem_univ i)
  rw [← hs]
  ring

open scoped Classical in
/-- The Pochhammer numerator of a constant vector of variables is a single Pochhammer
symbol, by the multinomial Chu–Vandermonde identity. -/
theorem carlsonRPolynomialNumerator_const (n : ℕ) (b : ι → ℂ) (w : ℂ) :
    carlsonRPolynomialNumerator n b (fun _ => w) =
      (ascPochhammer ℂ n).eval (∑ i, b i) * w ^ n := by
  rw [carlsonRPolynomialNumerator_eq_multinomial_sum, ascPochhammer_eval_sum univ b n]
  rw [sum_mul]
  refine sum_congr rfl fun m hm => ?_
  have hpow : (∏ i, (w : ℂ) ^ m i) = w ^ n := by
    rw [prod_pow_eq_pow_sum]
    have : ∑ i, m i = n := (mem_piAntidiag.mp hm).1
    simp [this]
  rw [hpow]
  ring

open scoped Classical in
/-- A numerator with just one nonzero node is a single Pochhammer symbol. -/
theorem carlsonRPolynomialNumerator_single (n : ℕ) (i : ι) (b : ι → ℂ) (w : ℂ) :
    carlsonRPolynomialNumerator n b (Pi.single i w) =
      (ascPochhammer ℂ n).eval (b i) * w ^ n := by
  have hp : carlsonPowerPolynomial n (Pi.single i w) =
      MvPolynomial.monomial (Finsupp.single i n) (w ^ n) := by
    have hlin : carlsonAffinePolynomial (Pi.single i w) =
        MvPolynomial.C w * MvPolynomial.X i := by
      simp [carlsonAffinePolynomial, Pi.single_apply, apply_ite, ite_mul]
    rw [carlsonPowerPolynomial, hlin, mul_pow, ← MvPolynomial.C_pow,
      MvPolynomial.C_mul_X_pow_eq_monomial]
  have heq : carlsonRPolynomialNumerator n b (Pi.single i w) =
      (AddMonoidAlgebra.coeff (carlsonPowerPolynomial n (Pi.single i w))).sum
        (fun m c => c * ∏ j, (ascPochhammer ℂ (m j)).eval (b j)) := by
    rw [carlsonRPolynomialNumerator, MvPolynomial.sum_def]
    apply sum_congr rfl
    intro m hm
    have hdeg : m.sum (fun _ e => e) = n := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hm)
        (coeff_carlsonPowerPolynomial_eq_zero_of_sum_ne n (Pi.single i w) m hne)
    simp [coeff_carlsonPowerPolynomial, hdeg]
  rw [heq, hp, MvPolynomial.sum_monomial_eq (by simp)]
  have hprod : (∏ j, (ascPochhammer ℂ ((Finsupp.single i n) j)).eval (b j)) =
      (ascPochhammer ℂ n).eval (b i) := by
    rw [prod_eq_single i]
    · simp
    · intro j _ hji; simp [Finsupp.single_eq_of_ne hji]
    · simp
  rw [hprod, mul_comm]

omit [Fintype ι] in
open scoped Classical in
private lemma carlsonRTransformVariables_update {i j : ι} (hji : j ≠ i)
    (z : ι → ℂ) (w : ℂ) :
    carlsonRTransformVariables i (Function.update z j w) =
      Function.update (carlsonRTransformVariables i z) j (z i - w) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [carlsonRTransformVariables, hji.symm]
  · by_cases hkj : k = j
    · subst k
      simp [carlsonRTransformVariables, hji, hji.symm]
    · simp [carlsonRTransformVariables, hki, hkj, hji.symm]

open scoped Classical in
private lemma carlsonRTransformParameters_addDirichletUnit
    (n : ℕ) {i j : ι} (hji : j ≠ i) (b : ι → ℂ) :
    carlsonRTransformParameters n i (addDirichletUnit b j) =
      addDirichletUnit (carlsonRTransformParameters (n + 1) i b) j := by
  have hs : (∑ k, addDirichletUnit b j k) = (∑ k, b k) + 1 := by
    simp only [addDirichletUnit, sum_update_of_mem (mem_univ j), sdiff_singleton_eq_erase]
    rw [← sum_erase_add univ b (mem_univ j)]
    ring
  funext k
  by_cases hki : k = i
  · subst k
    simp only [addDirichletUnit] at hs
    simp only [carlsonRTransformParameters, Function.update_self, addDirichletUnit,
      Function.update_of_ne hji.symm, hs, Nat.cast_add, Nat.cast_one]
    ring
  · by_cases hkj : k = j
    · subst k
      simp [carlsonRTransformParameters, addDirichletUnit, hji]
    · simp [carlsonRTransformParameters, addDirichletUnit, hki, hkj]

open scoped Classical in
omit [Fintype ι] in
/-- If changing any coordinate other than `i` leaves a function unchanged, it agrees
with its value at the constant vector whose entries are `z i`. -/
private lemma eq_const_of_update_eq [Finite ι] (f : (ι → ℂ) → ℂ) (i : ι)
    (hf : ∀ j, j ≠ i → ∀ z w, f (Function.update z j w) = f z) (z : ι → ℂ) :
    f z = f (fun _ => z i) := by
  classical
  let _ := Fintype.ofFinite ι
  have H (s : Finset ι) : ∀ v : ι → ℂ, (∀ k ∉ s, v k = z i) →
      (∀ k ∈ s, k ≠ i) → f v = f (fun _ => z i) := by
    induction s using Finset.induction_on with
    | empty =>
      intro v hv _
      have heq : v = fun _ => z i := funext fun k => hv k (by simp)
      rw [heq]
    | @insert j s hjs ih =>
      intro v hv hs
      rw [← hf j (hs j (mem_insert_self _ _)) v (z i)]
      apply ih
      · intro k hk
        by_cases hkj : k = j
        · subst k; simp
        · rw [Function.update_of_ne hkj]
          exact hv k (by simp [hkj, hk])
      · exact fun k hk => hs k (mem_insert_of_mem hk)
  apply H (univ.erase i) z
  · intro k hk
    have hki : k = i := by simpa using hk
    rw [hki]
  · intro k hk
    exact (mem_erase.mp hk).1

open scoped Classical in
/-- Division-free form of Carlson's multivariate linear transformation 6.5-3.

Using the Pochhammer numerator avoids hypotheses excluding exceptional parameters. Carlson's
usual identity follows after division by the relevant total-parameter Pochhammer symbols.

Induction on the degree shows that the difference has zero derivative in every node except
the distinguished one. At a constant node vector, Pochhammer reflection makes it zero. -/
theorem carlsonRPolynomialNumerator_transform (n : ℕ) (i : ι) (b z : ι → ℂ) :
    carlsonRPolynomialNumerator n b z =
      (-1 : ℂ) ^ n * carlsonRPolynomialNumerator n
        (carlsonRTransformParameters n i b) (carlsonRTransformVariables i z) := by
  induction n generalizing b z with
  | zero => simp
  | succ n ih =>
    let b' := carlsonRTransformParameters (n + 1) i b
    let F := fun z => carlsonRPolynomialNumerator (n + 1) b z -
      (-1 : ℂ) ^ (n + 1) * carlsonRPolynomialNumerator (n + 1) b'
        (carlsonRTransformVariables i z)
    have hder (j : ι) (hji : j ≠ i) (v : ι → ℂ) (w : ℂ) :
        HasDerivAt (fun t => F (Function.update v j t)) 0 w := by
      have hleft : HasDerivAt
          (fun t => carlsonRPolynomialNumerator (n + 1) b (Function.update v j t))
          ((n + 1 : ℂ) * b j * carlsonRPolynomialNumerator n (addDirichletUnit b j)
            (Function.update v j w)) w := by
        simpa only [Function.update_self, Function.update_idem] using
          hasDerivAt_carlsonRPolynomialNumerator_update_succ n j b (Function.update v j w)
      have hright : HasDerivAt
          (fun t => carlsonRPolynomialNumerator (n + 1) b'
            (Function.update (carlsonRTransformVariables i v) j t))
          ((n + 1 : ℂ) * b' j * carlsonRPolynomialNumerator n (addDirichletUnit b' j)
            (Function.update (carlsonRTransformVariables i v) j (v i - w))) (v i - w) := by
        simpa only [Function.update_self, Function.update_idem] using
          hasDerivAt_carlsonRPolynomialNumerator_update_succ n j b'
            (Function.update (carlsonRTransformVariables i v) j (v i - w))
      have H := hleft.sub ((hright.comp w
        ((hasDerivAt_const w (v i)).sub (hasDerivAt_id w))).const_mul ((-1 : ℂ) ^ (n + 1)))
      change HasDerivAt (fun t => carlsonRPolynomialNumerator (n + 1) b (Function.update v j t) -
        (-1 : ℂ) ^ (n + 1) * carlsonRPolynomialNumerator (n + 1) b'
          (carlsonRTransformVariables i (Function.update v j t))) 0 w
      simp_rw [carlsonRTransformVariables_update hji]
      apply H.congr_deriv
      rw [ih (addDirichletUnit b j) (Function.update v j w),
        carlsonRTransformParameters_addDirichletUnit n hji,
        carlsonRTransformVariables_update hji]
      simp only [b', carlsonRTransformParameters, Function.update_of_ne hji, pow_succ]
      ring
    have hupdate : ∀ j, j ≠ i → ∀ v w, F (Function.update v j w) = F v := by
      intro j hji v w
      have H := is_const_of_deriv_eq_zero (fun t => (hder j hji v t).differentiableAt)
        (fun t => (hder j hji v t).deriv) w (v j)
      simpa only [Function.update_eq_self] using H
    have hT : carlsonRTransformVariables i (fun _ : ι => z i) = Pi.single i (z i) := by
      funext j
      simp [carlsonRTransformVariables, Pi.single_apply]
    have hbase : F (fun _ => z i) = 0 := by
      dsimp only [F]
      rw [carlsonRPolynomialNumerator_const, hT, carlsonRPolynomialNumerator_single]
      have href := ascPochhammer_eval_split_reflection (∑ j, b j)
        (m := 0) (n := n + 1) (Nat.zero_le _)
      simp only [Nat.sub_zero, ascPochhammer_zero, Polynomial.eval_one, mul_one] at href
      simp only [b', carlsonRTransformParameters, Function.update_self]
      rw [href]
      ring
    apply sub_eq_zero.mp
    change F z = 0
    rw [eq_const_of_update_eq F i hupdate z, hbase]

/- The two-variable transformations 6.5-1 are specializations of
`carlsonRPolynomialNumerator_transform`. -/

end DirichletTransform
end CarlsonRPolynomial
