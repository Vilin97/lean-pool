/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.SingleIntegral.UnitInterval

/-! # Unit-interval representation at arbitrary Dirichlet parameters -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The unit-interval kernel obeys parameter raising even outside the simplex
integral's convergence region. Only the two endpoint exponents must converge. -/
private theorem carlsonRUnitIntervalIntegral_raise
    {a a' : ℂ} (b : ι → ℂ) {z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    carlsonRUnitIntervalIntegral a a' b z =
      carlsonRUnitIntervalIntegral a (a' + 1) (addDirichletUnit b i) z +
        z i * carlsonRUnitIntervalIntegral (a + 1) a' (addDirichletUnit b i) z := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 1)
  let K := singleIntegralKernel (addDirichletUnit b i) z
  have hint (v w : ℂ) (hv : 0 < v.re) (hw : 0 < w.re) :
      Integrable (fun u : ℝ => (u : ℂ) ^ (v - 1) * (1 - u : ℂ) ^ (w - 1) * K u) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      ((betaIntegral_convergent hv hw).mul_continuousOn
        (by simpa [Set.uIcc_of_le zero_le_one] using
            continuousOn_singleIntegralKernel_fixed (addDirichletUnit b i)
              (carlsonRVariableDomain_subset_slitDomain hz)))
  have h₀ := hint a (a' + 1) ha (by simpa using add_pos ha' zero_lt_one)
  have h₁ := hint (a + 1) a' (by simpa using add_pos ha zero_lt_one) ha'
  dsimp only [K, singleIntegralKernel] at h₀ h₁
  change (∫ u, _ ∂μ) = (∫ u, _ ∂μ) + z i * (∫ u, _ ∂μ)
  rw [← integral_const_mul, ← integral_add h₀ (h₁.const_mul (z i))]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
  have hu1 : (1 - u : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hu.2).ne'
  let v : ℂ := (1 - u : ℂ) + (u : ℂ) * z i
  have hv : v ≠ 0 := ne_zero_of_re_pos
    (affineSegment_mem_rightHalfPlane hz ⟨hu.1.le, hu.2.le⟩ i)
  have hK : singleIntegralKernel b z u = v * K u := by
    dsimp only [singleIntegralKernel, K]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i,
      Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp only [addDirichletUnit, Function.update_self]
    have hp : v * v ^ (-(b i + 1)) = v ^ (-b i) := by
      calc
        v * v ^ (-(b i + 1)) = v ^ (1 : ℂ) * v ^ (-(b i + 1)) := by rw [cpow_one]
        _ = v ^ (1 + -(b i + 1)) := (cpow_add _ _ hv).symm
        _ = _ := by congr 1; ring
    change v ^ (-b i) * _ = v * (v ^ (-(b i + 1)) * _)
    rw [← mul_assoc, hp]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [Function.update_of_ne j.property]
  have hp (w x : ℂ) (hx : x ≠ 0) : x ^ w = x ^ (w - 1) * x := by
    calc
      x ^ w = x ^ (w - 1 + 1) := by congr 1; ring
      _ = x ^ (w - 1) * x := by rw [cpow_add _ _ hx, cpow_one]
  change (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) * singleIntegralKernel b z u = _
  rw [hK]
  simp only [add_sub_cancel_right]
  rw [hp a _ hu0, hp a' _ hu1]
  dsimp only [v, K, singleIntegralKernel]
  ring

/-- Carlson's single-integral representation for arbitrary complex Dirichlet
parameters. The restrictions concern only the convergent endpoint exponents,
not the individual entries of `b`. -/
theorem carlsonRUnitIntervalIntegral_eq_gamma_mul_continued
    {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i) (hz : z ∈ carlsonRVariableDomain) :
    carlsonRUnitIntervalIntegral a a' b z =
      (Gamma a * Gamma a') * regCarlsonRContinued (-a) z hz b := by
  have hraise (n : ι → ℕ) : ∀ (a a' : ℂ) (b : ι → ℂ),
      0 < a.re → 0 < a'.re → a + a' = ∑ i, b i →
      (fun i => b i + n i) ∈ mvBetaConvergent →
      carlsonRUnitIntervalIntegral a a' b z =
        (Gamma a * Gamma a') * regCarlsonRContinued (-a) z hz b := by
    induction n using (measure (fun n : ι → ℕ => ∑ i, n i)).wf.induction with
    | h n ih =>
      intro a a' b ha ha' hsum hpos
      by_cases hn : n = 0
      · have hb : b ∈ mvBetaConvergent := by simpa [hn] using hpos
        rw [regCarlsonRContinued_eq_integral _ hz hb,
          carlsonRUnitIntervalIntegral_eq ha ha' hsum hb hz,
          betaIntegral_eq_Gamma_mul_div _ _ ha ha', carlsonRIntegral, ← hsum]
        have hG := Gamma_ne_zero_of_re_pos (show 0 < (a + a').re by simpa using add_pos ha ha')
        field_simp
      obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
        simpa only [funext_iff, Pi.zero_apply, not_forall] using hn
      let n' := Function.update n i (n i - 1)
      have hlt : (∑ j, n' j) < ∑ j, n j := by
        apply Finset.sum_lt_sum
        · intro j _
          by_cases hji : j = i <;> simp [n', hji]
        · exact ⟨i, Finset.mem_univ _, by simp [n']; omega⟩
      have hpos' : (fun j => addDirichletUnit b i j + n' j) ∈ mvBetaConvergent := by
        convert hpos using 1
        ext j
        by_cases hji : j = i
        · subst j
          simp only [addDirichletUnit, n', Function.update_self]
          rw [Nat.cast_sub (by omega : 1 ≤ n i)]
          push_cast
          ring
        · simp [addDirichletUnit, n', hji]
      have hs₀ : a + (a' + 1) = ∑ j, addDirichletUnit b i j := by
        rw [sum_addDirichletUnit, ← hsum]; ring
      have hs₁ : a + 1 + a' = ∑ j, addDirichletUnit b i j := by
        rw [sum_addDirichletUnit, ← hsum]; ring
      rw [carlsonRUnitIntervalIntegral_raise b ha ha' hz i,
        ih n' hlt a (a' + 1) _ ha (by simpa using add_pos ha' zero_lt_one) hs₀ hpos',
        ih n' hlt (a + 1) a' _ (by simpa using add_pos ha zero_lt_one) ha' hs₁ hpos',
        Gamma_add_one a (ne_zero_of_re_pos ha), Gamma_add_one a' (ne_zero_of_re_pos ha'),
        regCarlsonRContinued_eq_addDirichletUnit (-a) b hz i, ← hsum]
      rw [show -(a + 1) = -a - 1 by ring]
      ring
  choose n hn using fun i => exists_nat_gt (-(b i).re)
  exact hraise n a a' b ha ha' hsum (fun i => by
    have := hn i
    change 0 < (b i + (n i : ℂ)).re
    simp only [add_re, natCast_re]
    linarith)

end DirichletTransform
