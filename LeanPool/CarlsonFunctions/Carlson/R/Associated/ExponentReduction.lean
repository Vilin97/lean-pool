/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.Associated.LinearDependence
public import LeanPool.CarlsonFunctions.Carlson.Associated.Shift
public import LeanPool.CarlsonFunctions.Carlson.R.AssociatedRecurrence
public import LeanPool.CarlsonFunctions.Carlson.R.Relations
public import LeanPool.CarlsonFunctions.Pochhammer.Gamma

/-! # Reduction of integral exponent shifts to a finite polynomial span -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The last polynomial recurrence coefficient can be used to lower the exponent at
every downward step. Unlike the quotient presentation, this statement includes `a = 0`. -/
theorem carlsonAssociatedRecurrencePolynomial_lower_ne_zero [Nonempty ι]
    {t : ℂ} (ht : IsCarlsonGammaRegular (1 - t)) (b z : ι → ℂ)
    (hz : z ∈ carlsonRVariableDomain) (m : ℕ) :
    (carlsonAssociatedRecurrencePolynomial (Fintype.card ι) (-t + m)
      ((∑ i, b i) + t - m) b).eval z ≠ 0 := by
  simp only [carlsonAssociatedRecurrencePolynomial, ite_eq_right Fintype.card_ne_zero,
    ↓reduceIte, map_mul, MvPolynomial.eval_C]
  change -(ascPochhammer ℂ (Fintype.card ι - 1)).eval (-t + m + 1) *
    carlsonElementarySymmetric (Fintype.card ι) z ≠ 0
  rw [show -t + (m : ℂ) + 1 = (1 - t) + m by ring, carlsonElementarySymmetric_card]
  exact mul_ne_zero (neg_ne_zero.mpr ((ht.add_nat m).ascPochhammer_ne_zero _))
    (Finset.prod_ne_zero_iff.mpr (fun i _ ↦
      slitPlane_ne_zero (carlsonRightHalfPlane_subset_slitPlane (hz i))))

/-- The first polynomial recurrence coefficient can be used to raise the exponent at
every upward step. The second regularity hypothesis of Carlson's reduction lemma is
exactly the one needed here. -/
theorem carlsonAssociatedRecurrencePolynomial_raise_ne_zero
    {t : ℂ} (b z : ι → ℂ)
    (ht : IsCarlsonGammaRegular ((∑ i, b i) + t - Fintype.card ι + 2)) (m : ℕ) :
    (carlsonAssociatedRecurrencePolynomial 0 (-(t + m + 1))
      ((∑ i, b i) + t + m + 1) b).eval z ≠ 0 := by
  simp only [carlsonAssociatedRecurrencePolynomial, ↓reduceIte, MvPolynomial.eval_C]
  rw [show (∑ i, b i) + t + m + 1 - Fintype.card ι + 1 =
    ((∑ i, b i) + t - Fintype.card ι + 2) + m by ring]
  exact (ht.add_nat m).ascPochhammer_ne_zero _

/-- Denominator-cleared exponent reduction. The identity holds on the whole variable
domain, including the zero set of the denominator polynomial. -/
theorem exists_polynomial_carlsonAssociated_exponent_reduction
    (t : ℂ) (b : ι → ℂ) (n : ℤ)
    (hb : b ∈ mvBetaConvergent)
    (ht : IsCarlsonGammaRegular (1 - t))
    (hct : IsCarlsonGammaRegular ((∑ i, b i) + t - Fintype.card ι + 2)) :
    ∃ d : MvPolynomial ι ℂ, d ≠ 0 ∧
      ∃ p : Fin (Fintype.card ι) → MvPolynomial ι ℂ,
        ∀ z ∈ carlsonRVariableDomain,
          d.eval z * carlsonRIntegral (t + n) b z =
            ∑ j, (p j).eval z * carlsonRIntegral (t - (j : ℕ)) b z := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let _ := hι
    refine ⟨1, one_ne_zero, 0, ?_⟩
    simp [carlsonRIntegral]
  | inr hι =>
    let _ := hι
    let D := {z : ι → ℂ // z ∈ carlsonRVariableDomain}
    let A := MvPolynomial ι ℂ
    let : Module A (D → ℂ) := Module.compHom _
      (RingHom.pi (fun z : D => MvPolynomial.eval z.1))
    let F : ℂ → D → ℂ := fun u z => carlsonRIntegral u b z.1
    let P : Submodule A (D → ℂ) :=
      Submodule.span A (Set.range (fun j : Fin (Fintype.card ι) => F (t - (j : ℕ))))
    let Q := denominatorClosure P
    have hbase (j : ℕ) (hj : j < Fintype.card ι) : F (t - j) ∈ Q :=
      mem_denominatorClosure P (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    have hstep (a : ℂ) (i : ℕ) (hi : i ≤ Fintype.card ι)
        (hci : carlsonAssociatedRecurrencePolynomial i a ((∑ j, b j) - a) b ≠ 0)
        (hrest : ∀ j ∈ Finset.range (Fintype.card ι + 1), j ≠ i → F (-a - j) ∈ Q) :
        F (-a - i) ∈ Q := by
      let C := fun j => carlsonAssociatedRecurrencePolynomial j a ((∑ l, b l) - a) b
      have hsum : ∑ j ∈ Finset.range (Fintype.card ι + 1), C j • F (-a - j) = 0 := by
        ext z
        simp only [Finset.sum_apply, Pi.zero_apply]
        exact sum_carlsonAssociatedRecurrencePolynomial_mul_rIntegral a hb z.2
      have hmem : ∑ j ∈ (Finset.range (Fintype.card ι + 1)).erase i,
          C j • F (-a - j) ∈ Q := by
        apply Q.sum_mem
        intro j hj
        exact Q.smul_mem _ (hrest j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1)
      have heq := Finset.sum_erase_add (Finset.range (Fintype.card ι + 1))
        (fun j => C j • F (-a - j)) (Finset.mem_range.mpr (by omega : i < Fintype.card ι + 1))
      rw [hsum] at heq
      apply denominatorClosure_cancel P hci
      exact (eq_neg_of_add_eq_zero_right heq) ▸ Q.neg_mem hmem
    have hdown (m : ℕ) : F (t - m) ∈ Q := by
      induction m using Nat.strong_induction_on with
      | h m ih =>
        by_cases hm : m < Fintype.card ι
        · exact hbase m hm
        have he : t - (m : ℂ) = -(-t + (m - Fintype.card ι : ℕ)) - Fintype.card ι := by
          rw [Nat.cast_sub (by omega : Fintype.card ι ≤ m)]
          ring
        rw [he]
        apply hstep _ _ le_rfl
        · have hc := carlsonAssociatedRecurrencePolynomial_lower_ne_zero ht b
            (fun _ => 1) (by intro i; norm_num [carlsonRVariableDomain, carlsonRightHalfPlane])
            (m - Fintype.card ι)
          intro h
          apply hc
          rw [show (∑ i, b i) + t - (m - Fintype.card ι : ℕ) =
            (∑ i, b i) - (-t + (m - Fintype.card ι : ℕ)) by ring, h, map_zero]
        · intro j hj hji
          have hj' := Finset.mem_range.mp hj
          have heq : -(-t + (m - Fintype.card ι : ℕ)) - j =
              t - (m - Fintype.card ι + j : ℕ) := by push_cast; ring
          rw [heq]
          exact ih _ (by omega)
    have hup (m : ℕ) : F (t + m) ∈ Q := by
      induction m using Nat.strong_induction_on with
      | h m ih =>
        cases m with
        | zero => simpa using hdown 0
        | succ m =>
          have he : t + (m + 1 : ℕ) = -(-(t + m + 1)) - (0 : ℕ) := by push_cast; ring
          rw [he]
          apply hstep _ _ (Nat.zero_le _)
          · have hc := carlsonAssociatedRecurrencePolynomial_raise_ne_zero b (fun _ => 1) hct m
            intro h
            apply hc
            rw [show (∑ i, b i) + t + m + 1 = (∑ i, b i) - (-(t + m + 1)) by ring,
              h, map_zero]
          · intro j hj hj0
            by_cases hjm : j ≤ m + 1
            · have heq : -(-(t + m + 1)) - j = t + (m + 1 - j : ℕ) := by
                rw [Nat.cast_sub hjm]; push_cast; ring
              rw [heq]
              exact ih _ (by omega)
            · have heq : -(-(t + m + 1)) - j = t - (j - (m + 1) : ℕ) := by
                rw [Nat.cast_sub (by omega : m + 1 ≤ j)]; push_cast; ring
              rw [heq]
              exact hdown _
    have hn : F (t + n) ∈ Q := by
      cases n with
      | ofNat m => exact hup m
      | negSucc m => simpa [Int.cast_negSucc, sub_eq_add_neg] using hdown (m + 1)
    obtain ⟨d, hd, hspan⟩ := hn
    obtain ⟨p, hp⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hspan
    refine ⟨d, hd, p, ?_⟩
    intro z hz
    have heq := congrFun hp (⟨z, hz⟩ : D)
    simp only [Finset.sum_apply] at heq
    change (∑ j, (p j).eval z * carlsonRIntegral (t - (j : ℕ)) b z) =
      d.eval z * carlsonRIntegral (t + n) b z at heq
    exact heq.symm

/-- Carlson's reduction lemma 8.4-2: all integral exponent shifts with fixed parameters lie
in the rational-function span of `card ι` consecutive R-functions. -/
theorem exists_rational_carlsonAssociated_exponent_reduction
    (t : ℂ) (b : ι → ℂ) (n : ℤ)
    (hb : b ∈ mvBetaConvergent)
    (ht : IsCarlsonGammaRegular (1 - t))
    (hct : IsCarlsonGammaRegular ((∑ i, b i) + t - Fintype.card ι + 2)) :
    ∃ q : Fin (Fintype.card ι) → CarlsonRRationalCoefficient ι,
      ∀ z ∈ carlsonRVariableDomain,
        (∀ j, (q j).denominator.eval z ≠ 0) →
        carlsonRIntegral (t + n) b z =
          ∑ j, (q j).eval z * carlsonRIntegral (t - (j : ℕ)) b z := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let _ := hι
    refine ⟨fun j => False.elim (by simpa using j.isLt), ?_⟩
    simp [carlsonRIntegral]
  | inr hι =>
    let _ := hι
    obtain ⟨d, hd, p, hp⟩ :=
      exists_polynomial_carlsonAssociated_exponent_reduction t b n hb ht hct
    refine ⟨fun j => ⟨p j, d, hd⟩, ?_⟩
    intro z hz hden
    have hd_eval : d.eval z ≠ 0 := hden ⟨0, Fintype.card_pos⟩
    change _ = ∑ j, ((p j).eval z / d.eval z) * _
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← hp z hz]
    exact (mul_div_cancel_left₀ _ hd_eval).symm

end DirichletTransform
