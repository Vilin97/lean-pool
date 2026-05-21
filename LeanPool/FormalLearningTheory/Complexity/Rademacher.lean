/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.VCDimension
import LeanPool.FormalLearningTheory.Complexity.Generalization
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Rademacher Complexity

Measure-theoretic complexity measure. Upper bounds generalization error.
Upper bounded by VC dimension. Bridges to lean-rademacher library (K₂).

## Main results

- `rademacherCorrelation_abs_le_one` : |corr(h,σ,xs)| ≤ 1
- `empiricalRademacherComplexity_le_one` : EmpRad ≤ 1
- `rademacherComplexity_le_one` : Rad ≤ 1 (population)
- `rademacherComplexity_nonneg` : 0 ≤ Rad
- `vcdim_bounds_rademacher_quantitative` : Rad ≤ √(2d·log(em/d)/m)
- `rademacher_vanishing_imp_pac` : uniform Rad vanishing → PAC
- `vcdim_finite_imp_rademacher_vanishing` : VCDim < ⊤ → Rad → 0
-/

universe u v

/-- Convert Bool labels to ±1 reals. true ↦ 1, false ↦ -1. -/
noncomputable def boolToSign (b : Bool) : ℝ := if b then 1 else -1

theorem boolToSign_abs_eq_one (b : Bool) : |boolToSign b| = 1 := by
  unfold boolToSign; cases b <;> simp

theorem boolToSign_abs_le_one (b : Bool) : |boolToSign b| ≤ 1 := by
  rw [boolToSign_abs_eq_one]

theorem boolToSign_sq (b : Bool) : boolToSign b ^ 2 = 1 := by
  unfold boolToSign; cases b <;> norm_num

theorem boolToSign_sum_zero : ∑ b : Bool, boolToSign b = 0 := by
  simp [boolToSign]

theorem boolToSign_mul_abs_le_one (b₁ b₂ : Bool) : |boolToSign b₁ * boolToSign b₂| ≤ 1 := by
  rw [abs_mul]
  have h₁ := boolToSign_abs_le_one b₁; have h₂ := boolToSign_abs_le_one b₂
  nlinarith [abs_nonneg (boolToSign b₁), abs_nonneg (boolToSign b₂)]

/-- Boolean sign assignments used as Rademacher variables. -/
abbrev SignVector (m : ℕ) := Fin m → Bool

/-- Bit-flip at coordinate i: σ ↦ σ' where σ'(i) = !σ(i), σ'(k) = σ(k) for k ≠ i. -/
private def flipAt {m : ℕ} (i : Fin m) (σ : SignVector m) : SignVector m :=
  Function.update σ i (!σ i)

private theorem flipAt_involutive {m : ℕ} (i : Fin m) : Function.Involutive (flipAt i) := by
  intro σ; ext k; unfold flipAt
  simp only [Function.update_apply]
  split
  · next h => subst h; simp [Bool.not_not]
  · rfl

private theorem flipAt_boolToSign {m : ℕ} (i : Fin m) (σ : SignVector m) :
    boolToSign (flipAt i σ i) = -boolToSign (σ i) := by
  unfold flipAt; simp only [Function.update_self]
  unfold boolToSign; cases σ i <;> simp

private theorem flipAt_other {m : ℕ} (i : Fin m) (σ : SignVector m) (k : Fin m) (hk : k ≠ i) :
    flipAt i σ k = σ k := by
  unfold flipAt; simp [hk]

private theorem sum_boolToSign_cancel {m : ℕ} (i : Fin m) (f : SignVector m → ℝ)
    (hf : ∀ σ σ', (∀ k, k ≠ i → σ k = σ' k) → f σ = f σ') :
    ∑ σ : SignVector m, boolToSign (σ i) * f σ = 0 := by
  set g : SignVector m → ℝ := fun σ => boolToSign (σ i) * f σ
  have h_eq : ∑ σ : SignVector m, g σ = ∑ σ : SignVector m, g (flipAt i σ) := by
    let e : SignVector m ≃ SignVector m :=
      Equiv.ofBijective (flipAt i) (flipAt_involutive i).bijective
    rw [show ∑ σ, g (flipAt i σ) = ∑ σ, g (e σ) from rfl]
    exact (Equiv.sum_comp e g).symm
  have h_neg : ∀ σ, g (flipAt i σ) = -g σ := fun σ => by
    change boolToSign (flipAt i σ i) * f (flipAt i σ) = -(boolToSign (σ i) * f σ)
    rw [flipAt_boolToSign, hf (flipAt i σ) σ (fun k hk => flipAt_other i σ k hk)]; ring
  have h_neg_sum : ∑ σ : SignVector m, g σ = -(∑ σ : SignVector m, g σ) := by
    conv_lhs => rw [h_eq]
    simp_rw [h_neg, Finset.sum_neg_distrib]
  linarith

private theorem rademacher_cross_cancel {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ∑ σ : SignVector m, boolToSign (σ i) * boolToSign (σ j) = 0 :=
  sum_boolToSign_cancel i (fun σ => boolToSign (σ j))
    (fun σ σ' h => by simp only; rw [h j hij.symm])

/-- Rademacher diagonal: Σ_σ boolToSign(σ i)² = |SignVector m| = 2^m. -/
private theorem rademacher_diagonal {m : ℕ} (i : Fin m) :
    ∑ σ : SignVector m, boolToSign (σ i) ^ 2 = (Fintype.card (SignVector m) : ℝ) := by
  simp_rw [boolToSign_sq]
  simp [Finset.sum_const, Finset.card_univ]

private theorem rademacher_variance_eq {m : ℕ} (_hm : 0 < m) (a : Fin m → ℝ)
    (ha : ∀ i, |a i| = 1) :
    ∑ σ : SignVector m, (∑ i : Fin m, boolToSign (σ i) * a i) ^ 2 =
      (m : ℝ) * (Fintype.card (SignVector m) : ℝ) := by
  set N := (Fintype.card (SignVector m) : ℝ)
  suffices h_each : ∀ i : Fin m, ∑ σ : SignVector m,
      ∑ j : Fin m, (boolToSign (σ i) * a i) * (boolToSign (σ j) * a j) = N by
    simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    simp_rw [h_each]; simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  intro i
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  have h_term : ∀ j : Fin m, ∑ σ : SignVector m,
      (boolToSign (σ i) * a i) * (boolToSign (σ j) * a j) =
      (a i * a j) * ∑ σ : SignVector m, boolToSign (σ i) * boolToSign (σ j) := by
    intro j; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => by ring)
  simp_rw [h_term]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h_cross_sum : ∑ j ∈ Finset.univ.erase i, a i * a j *
      ∑ σ : SignVector m, boolToSign (σ i) * boolToSign (σ j) = 0 :=
    Finset.sum_eq_zero (fun j hj => by
      rw [rademacher_cross_cancel i j (Finset.ne_of_mem_erase hj).symm, mul_zero])
  rw [h_cross_sum, add_zero,
      show ∑ σ : SignVector m, boolToSign (σ i) * boolToSign (σ i) =
           ∑ σ : SignVector m, boolToSign (σ i) ^ 2 from
        Finset.sum_congr rfl (fun σ _ => by ring),
      rademacher_diagonal]
  rw [show a i * a i = 1 from by nlinarith [sq_abs (a i), sq_nonneg (a i), ha i], one_mul]

/-- Normalized signed correlation of a hypothesis on a finite sample. -/
noncomputable def rademacherCorrelation {X : Type u} {m : ℕ}
    (h : Concept X Bool) (σ : SignVector m) (xs : Fin m → X) : ℝ :=
  if _hm : m = 0 then 0
  else (1 / (m : ℝ)) * ∑ i : Fin m, boolToSign (σ i) * boolToSign (h (xs i))

theorem rademacherCorrelation_abs_le_one {X : Type u} {m : ℕ} (hm : 0 < m)
    (h : Concept X Bool) (σ : SignVector m) (xs : Fin m → X) :
    |rademacherCorrelation h σ xs| ≤ 1 := by
  unfold rademacherCorrelation
  rw [dif_neg (by omega)]
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rw [abs_mul, abs_div, abs_one, abs_of_pos hm_pos]
  have hsum_le : |∑ i : Fin m, boolToSign (σ i) * boolToSign (h (xs i))| ≤ m :=
    (norm_sum_le Finset.univ (fun i => boolToSign (σ i) * boolToSign (h (xs i)))).trans
      (by calc ∑ i : Fin m, ‖boolToSign (σ i) * boolToSign (h (xs i))‖
              ≤ ∑ _i : Fin m, (1 : ℝ) :=
                Finset.sum_le_sum (fun i _ => by
                  rw [Real.norm_eq_abs]; exact boolToSign_mul_abs_le_one (σ i) (h (xs i)))
            _ = m := by simp [Finset.sum_const])
  calc 1 / (m : ℝ) * |∑ i, boolToSign (σ i) * boolToSign (h (xs i))|
      ≤ 1 / m * m := mul_le_mul_of_nonneg_left hsum_le (div_nonneg one_pos.le hm_pos.le)
    _ = 1 := by field_simp

/-- Empirical Rademacher complexity of a Boolean concept class on a fixed sample. -/
noncomputable def EmpiricalRademacherComplexity (X : Type u)
    (C : ConceptClass X Bool) {m : ℕ} (xs : Fin m → X) : ℝ :=
  if _hm : m = 0 then 0
  else
    let numSigns : ℝ := (Fintype.card (SignVector m) : ℝ)
    (1 / numSigns) * ∑ σ : SignVector m,
      sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs }

theorem empiricalRademacherComplexity_le_one (X : Type u)
    (C : ConceptClass X Bool) {m : ℕ} (hm : 0 < m) (xs : Fin m → X) :
    EmpiricalRademacherComplexity X C xs ≤ 1 := by
  unfold EmpiricalRademacherComplexity
  rw [dif_neg (by omega)]
  have hnum_pos : (0 : ℝ) < (Fintype.card (SignVector m) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h_each_le_one : ∀ σ : SignVector m,
      sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } ≤ 1 := by
    intro σ
    by_cases hC : C.Nonempty
    · apply csSup_le
      · obtain ⟨h, hh⟩ := hC
        exact ⟨rademacherCorrelation h σ xs, h, hh, rfl⟩
      · rintro r ⟨h, _, rfl⟩
        exact le_trans (le_abs_self _) (rademacherCorrelation_abs_le_one hm h σ xs)
    · rw [Set.not_nonempty_iff_eq_empty] at hC
      have : { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } = ∅ := by
        ext r; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h, hh, _⟩; simp [hC] at hh
      rw [this, Real.sSup_empty]; exact zero_le_one
  have h_sum_le : ∑ σ : SignVector m,
      sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } ≤
      Fintype.card (SignVector m) := by
    calc ∑ σ : SignVector m, sSup _ ≤ ∑ _σ : SignVector m, (1 : ℝ) :=
          Finset.sum_le_sum (fun σ _ => h_each_le_one σ)
      _ = Fintype.card (SignVector m) := by simp [Finset.sum_const, Finset.card_univ]
  calc 1 / (Fintype.card (SignVector m) : ℝ) *
      ∑ σ, sSup { r | ∃ h ∈ C, r = rademacherCorrelation h σ xs }
      ≤ 1 / (Fintype.card (SignVector m) : ℝ) * Fintype.card (SignVector m) := by
        apply mul_le_mul_of_nonneg_left h_sum_le
        exact div_nonneg one_pos.le hnum_pos.le
    _ = 1 := by field_simp

/-- Distributional Rademacher complexity, averaging empirical complexity over samples. -/
noncomputable def RademacherComplexity (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (m : ℕ) : ℝ :=
  ∫ xs : Fin m → X,
    EmpiricalRademacherComplexity X C xs
    ∂(MeasureTheory.Measure.pi (fun _ : Fin m => D))

private theorem empRad_nonneg {X : Type u} (C : ConceptClass X Bool) {m : ℕ}
    (hm : m ≠ 0) (xs : Fin m → X) :
    0 ≤ EmpiricalRademacherComplexity X C xs := by
  unfold EmpiricalRademacherComplexity
  rw [dif_neg hm]
  apply mul_nonneg (div_nonneg one_pos.le (Nat.cast_nonneg _))
  by_cases hC : C.Nonempty
  · obtain ⟨h₀, hh₀⟩ := hC
    have hbdd : ∀ σ, BddAbove { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } :=
      fun σ => ⟨1, fun r hr => by
        obtain ⟨h', _, rfl⟩ := hr
        exact le_trans (le_abs_self _)
          (rademacherCorrelation_abs_le_one (Nat.pos_of_ne_zero hm) h' σ xs)⟩
    linarith [(show ∑ σ : SignVector m, rademacherCorrelation h₀ σ xs = 0 from by
        simp only [rademacherCorrelation, dif_neg hm]
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp [fun i => sum_boolToSign_cancel i (fun _ => boolToSign (h₀ (xs i)))
          (fun _ _ _ => rfl)]) ▸
      Finset.sum_le_sum (fun σ _ => le_csSup_of_le (hbdd σ) ⟨h₀, hh₀, rfl⟩ le_rfl)]
  · rw [Set.not_nonempty_iff_eq_empty] at hC
    apply Finset.sum_nonneg; intro σ _
    have : { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } = ∅ := by
      ext r; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h, hh, _⟩; simp [hC] at hh
    rw [this, Real.sSup_empty]

theorem rademacherComplexity_le_one (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (m : ℕ) (hm : 0 < m)
    [MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.pi (fun _ : Fin m => D))] :
    RademacherComplexity X C D m ≤ 1 := by
  unfold RademacherComplexity
  calc ∫ xs, EmpiricalRademacherComplexity X C xs ∂(MeasureTheory.Measure.pi _)
      ≤ ∫ _xs, (1 : ℝ) ∂(MeasureTheory.Measure.pi (fun _ : Fin m => D)) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact MeasureTheory.ae_of_all _ (fun xs =>
            empRad_nonneg C (Nat.pos_iff_ne_zero.mp hm) xs)
        · exact MeasureTheory.integrable_const 1
        · exact MeasureTheory.ae_of_all _
            (fun xs => empiricalRademacherComplexity_le_one X C hm xs)
    _ = 1 := by simp [MeasureTheory.integral_const]

theorem rademacherComplexity_nonneg (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (m : ℕ) (hm : 0 < m)
    [MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.pi (fun _ : Fin m => D))] :
    0 ≤ RademacherComplexity X C D m :=
  MeasureTheory.integral_nonneg (fun xs => empRad_nonneg C (Nat.pos_iff_ne_zero.mp hm) xs)

theorem rademacher_gen_bound (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure D]
    (m : ℕ) (hm : 0 < m) (c : Concept X Bool) (_hcC : c ∈ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (bound : ℝ), bound = 2 * RademacherComplexity X C D m + ε ∧ bound ≥ 0 :=
  ⟨_, rfl, by linarith [rademacherComplexity_nonneg X C D m hm]⟩

private theorem corr_eq_one_of_agree {X : Type u} {m : ℕ} (hm : 0 < m)
    (h : Concept X Bool) (σ : SignVector m) (xs : Fin m → X)
    (hagree : ∀ i : Fin m, h (xs i) = σ i) :
    rademacherCorrelation h σ xs = 1 := by
  unfold rademacherCorrelation
  rw [dif_neg (by omega)]
  simp_rw [fun i => show boolToSign (σ i) * boolToSign (h (xs i)) = 1 by
    rw [hagree i]; unfold boolToSign; cases σ i <;> simp]
  simp [Finset.sum_const]
  field_simp

private theorem shatters_subset {X : Type u} (C : ConceptClass X Bool)
    (T S : Finset X) (hTS : S ⊆ T) (hT : Shatters X C T) :
    Shatters X C S := by
  classical
  intro f
  obtain ⟨c, hcC, hcT⟩ := hT (fun ⟨x, _⟩ => if hxS : x ∈ S then f ⟨x, hxS⟩ else true)
  exact ⟨c, hcC, fun ⟨x, hxS⟩ => by
    have h := hcT ⟨x, hTS hxS⟩; change c x = f ⟨x, hxS⟩
    rw [h]; simp [dif_pos hxS]⟩

private theorem empRad_eq_one_of_all_labelings {X : Type u}
    (C : ConceptClass X Bool) {m : ℕ} (hm : 0 < m) (xs : Fin m → X)
    (h_realize : ∀ σ : SignVector m, ∃ h ∈ C, ∀ i : Fin m, h (xs i) = σ i) :
    EmpiricalRademacherComplexity X C xs = 1 := by
  have hbdd : ∀ σ, BddAbove { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } :=
    fun σ => ⟨1, fun r hr => by
      obtain ⟨h', _, rfl⟩ := hr
      exact le_trans (le_abs_self _) (rademacherCorrelation_abs_le_one hm h' σ xs)⟩
  have h_ssup_eq_one : ∀ σ : SignVector m,
      sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } = 1 := fun σ => by
    obtain ⟨c, hcC, hc_agree⟩ := h_realize σ
    apply le_antisymm
    · apply csSup_le
      · exact ⟨rademacherCorrelation c σ xs, c, hcC, rfl⟩
      · rintro r ⟨h, _, rfl⟩
        exact le_trans (le_abs_self _) (rademacherCorrelation_abs_le_one hm h σ xs)
    · exact le_csSup_of_le (hbdd σ) ⟨c, hcC, rfl⟩
        (by rw [corr_eq_one_of_agree hm c σ xs hc_agree])
  unfold EmpiricalRademacherComplexity
  rw [dif_neg (by omega)]
  simp_rw [h_ssup_eq_one]
  simp [Finset.sum_const, Finset.card_univ]

/-! ## Helpers for VCDim → Rademacher bound (Massart + Sauer-Shelah) -/

theorem exp_mul_sup'_le_sum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) (_ht : 0 ≤ t) :
    Real.exp (t * s.sup' hs f) ≤ ∑ i ∈ s, Real.exp (t * f i) := by
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_mem_eq_sup' hs f
  rw [hmax]
  exact Finset.single_le_sum (f := fun i => Real.exp (t * f i))
    (fun i _ => (Real.exp_pos _).le) hi₀

/-- cosh(x) ≤ exp(x²/2). Standard sub-Gaussian bound. -/
theorem cosh_le_exp_sq_half (x : ℝ) : Real.cosh x ≤ Real.exp (x ^ 2 / 2) :=
  Real.cosh_le_exp_half_sq x

/-- Rademacher MGF bound. -/
theorem rademacher_mgf_bound {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) (c : ℝ) (_hc : 0 ≤ c)
    (ha : ∀ i, |a i| ≤ c) (t : ℝ) (_ht : 0 ≤ t) :
    (1 / (Fintype.card (SignVector m) : ℝ)) *
      ∑ σ : SignVector m, Real.exp (t * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) ≤
    Real.exp (t ^ 2 * c ^ 2 / (2 * m)) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have h_step1 : ∀ σ : SignVector m,
      Real.exp (t * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) =
      ∏ i : Fin m, Real.exp (t * a i * boolToSign (σ i) / m) := by
    intro σ
    have h_sum : t * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i)) =
        ∑ i : Fin m, (t * a i * boolToSign (σ i) / m) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      congr 1; ext i; ring
    rw [h_sum, Real.exp_sum]
  simp_rw [h_step1]
  rw [show ∑ σ : SignVector m, ∏ i : Fin m, Real.exp (t * a i * boolToSign (σ i) / ↑m) =
      ∏ i : Fin m, ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) from by
    rw [← Fintype.piFinset_univ (β := fun _ : Fin m => Bool)]
    exact Finset.sum_prod_piFinset Finset.univ
      (fun (i : Fin m) (b : Bool) => Real.exp (t * a i * boolToSign b / ↑m))]
  rw [show (1 : ℝ) / (Fintype.card (SignVector m) : ℝ) = ∏ _i : Fin m, (1 / 2 : ℝ) from by
      have : Fintype.card (SignVector m) = 2 ^ m := by
        change Fintype.card (Fin m → Bool) = 2 ^ m
        simp [Fintype.card_fin, Fintype.card_bool]
      push_cast [this]; simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
    ← Finset.prod_mul_distrib]
  have h_factor_bound : ∀ i : Fin m,
      (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) ≤
      Real.exp ((t * a i / ↑m) ^ 2 / 2) := by
    intro i
    set u := t * a i / (↑m : ℝ) with hu_def
    have h_sum_eq : ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) =
        Real.exp u + Real.exp (-u) := by
      simp only [Fintype.sum_bool, boolToSign, ↓reduceIte, Bool.false_eq_true]
      congr 1
      · congr 1; rw [hu_def]; ring
      · congr 1; rw [hu_def]; ring
    rw [h_sum_eq, show (1 / 2 : ℝ) * (Real.exp u + Real.exp (-u)) = Real.cosh u from by
      rw [Real.cosh_eq]; ring]
    exact cosh_le_exp_sq_half _
  have h_factor_nonneg : ∀ i ∈ Finset.univ (α := Fin m),
      0 ≤ (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) :=
    fun i _ => mul_nonneg (by norm_num) (Finset.sum_nonneg (fun b _ => (Real.exp_pos _).le))
  calc ∏ i : Fin m, (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m)
      ≤ ∏ i : Fin m, Real.exp ((t * a i / ↑m) ^ 2 / 2) :=
        Finset.prod_le_prod h_factor_nonneg (fun i _ => h_factor_bound i)
    _ = Real.exp (∑ i : Fin m, (t * a i / ↑m) ^ 2 / 2) :=
        (Real.exp_sum Finset.univ _).symm
    _ ≤ Real.exp (t ^ 2 * c ^ 2 / (2 * ↑m)) := by
        apply Real.exp_le_exp_of_le
        have h_sum_eq : ∑ i : Fin m, (t * a i / ↑m) ^ 2 / 2 =
            t ^ 2 / (2 * ↑m ^ 2) * ∑ i : Fin m, a i ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _; ring
        rw [h_sum_eq]
        have h_sum_sq_le : ∑ i : Fin m, a i ^ 2 ≤ ↑m * c ^ 2 := by
          calc ∑ i : Fin m, a i ^ 2
              ≤ ∑ _i : Fin m, c ^ 2 := by
                apply Finset.sum_le_sum; intro i _
                exact sq_le_sq' (abs_le.mp (ha i)).1 (abs_le.mp (ha i)).2
            _ = ↑m * c ^ 2 := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        calc t ^ 2 / (2 * ↑m ^ 2) * ∑ i : Fin m, a i ^ 2
            ≤ t ^ 2 / (2 * ↑m ^ 2) * (↑m * c ^ 2) := by
              apply mul_le_mul_of_nonneg_left h_sum_sq_le; positivity
          _ = t ^ 2 * c ^ 2 / (2 * ↑m) := by field_simp

/-- Massart finite lemma: E_σ[max_{j ≤ N} Z_j] ≤ σ√(2 log N). -/
theorem finite_massart_lemma {m : ℕ} (_hm : 0 < m) {N : ℕ} (hN : 0 < N)
    (Z : Fin N → SignVector m → ℝ) (σ_param : ℝ) (hσ : 0 < σ_param)
    (h_mgf : ∀ j t, 0 ≤ t →
      (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ sv : SignVector m, Real.exp (t * Z j sv) ≤
      Real.exp (t ^ 2 * σ_param ^ 2 / 2)) :
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
    (1 / (Fintype.card (SignVector m) : ℝ)) *
      ∑ sv : SignVector m, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv) ≤
    σ_param * Real.sqrt (2 * Real.log N) := by
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  set E_max := (1 / (Fintype.card (SignVector m) : ℝ)) *
    ∑ sv : SignVector m, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv)
  have h1card_pos : (0 : ℝ) < 1 / (Fintype.card (SignVector m) : ℝ) := by positivity
  have h_exp_bound : ∀ t : ℝ, 0 < t →
      Real.exp (t * E_max) ≤ ↑N * Real.exp (t ^ 2 * σ_param ^ 2 / 2) := by
    intro t ht
    have h_jensen : Real.exp (t * E_max) ≤
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ sv : SignVector m, Real.exp (t * Finset.univ.sup' Finset.univ_nonempty
            (fun j => Z j sv)) := by
      have h_conv := convexOn_exp.map_sum_le (t := Finset.univ)
        (w := fun _ => 1 / (Fintype.card (SignVector m) : ℝ))
        (p := fun sv => t * Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv))
        (fun _ _ => le_of_lt h1card_pos)
        (by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
        (fun _ _ => Set.mem_univ _)
      simp only [smul_eq_mul] at h_conv
      rw [Finset.mul_sum]
      refine le_trans ?_ h_conv
      apply le_of_eq; congr 1
      simp only [E_max, ← Finset.mul_sum]; ring
    calc Real.exp (t * E_max)
        ≤ (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ sv, Real.exp (t * Finset.univ.sup' Finset.univ_nonempty
              (fun j => Z j sv)) := h_jensen
      _ ≤ (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ sv, ∑ j, Real.exp (t * Z j sv) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun sv _ => exp_mul_sup'_le_sum Finset.univ
              Finset.univ_nonempty (fun j => Z j sv) t (le_of_lt ht)))
            (le_of_lt h1card_pos)
      _ = ∑ j, (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ sv, Real.exp (t * Z j sv) := by
          rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      _ ≤ ∑ _ : Fin N, Real.exp (t ^ 2 * σ_param ^ 2 / 2) :=
          Finset.sum_le_sum (fun j _ => h_mgf j t (le_of_lt ht))
      _ = ↑N * Real.exp (t ^ 2 * σ_param ^ 2 / 2) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  have h_linear_bound : ∀ t : ℝ, 0 < t →
      E_max ≤ Real.log N / t + t * σ_param ^ 2 / 2 := by
    intro t ht
    have h_log : t * E_max ≤ Real.log N + t ^ 2 * σ_param ^ 2 / 2 := by
      have h1 : t * E_max ≤ Real.log (↑N * Real.exp (t ^ 2 * σ_param ^ 2 / 2)) := by
        rw [← Real.log_exp (t * E_max)]
        exact Real.log_le_log (Real.exp_pos _) (h_exp_bound t ht)
      rw [Real.log_mul (ne_of_gt hN_pos) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h1
      exact h1
    rw [div_add_div _ _ (ne_of_gt ht) (ne_of_gt (by positivity : (0:ℝ) < 2))]
    rw [le_div_iff₀ (mul_pos ht (by positivity : (0:ℝ) < 2))]
    nlinarith [sq_nonneg t]
  have hlog_N_nonneg : 0 ≤ Real.log ↑N := Real.log_natCast_nonneg N
  by_cases hlog : Real.log ↑N = 0
  · simp only [hlog, mul_zero, Real.sqrt_zero, mul_zero]
    by_contra h_neg
    push Not at h_neg
    have ht₀_pos : 0 < E_max / σ_param ^ 2 := div_pos h_neg (sq_pos_of_pos hσ)
    have h_bd := h_linear_bound _ ht₀_pos; rw [hlog] at h_bd; simp only [zero_div, zero_add] at h_bd
    linarith [show E_max / σ_param ^ 2 * σ_param ^ 2 / 2 = E_max / 2 by field_simp]
  · have hsqrt_pos : 0 < Real.sqrt (2 * Real.log ↑N) :=
      Real.sqrt_pos_of_pos (by linarith [lt_of_le_of_ne hlog_N_nonneg (Ne.symm hlog)])
    set t₀ := Real.sqrt (2 * Real.log ↑N) / σ_param
    refine le_trans (h_linear_bound t₀ (div_pos hsqrt_pos hσ)) (le_of_eq ?_)
    rw [show Real.log ↑N / t₀ = σ_param * Real.sqrt (2 * Real.log ↑N) / 2 from by
        simp only [t₀]; rw [div_div_eq_mul_div, div_eq_div_iff (ne_of_gt hsqrt_pos) two_ne_zero]
        nlinarith [Real.mul_self_sqrt (by linarith [hlog_N_nonneg] : 0 ≤ 2 * Real.log ↑N)],
      show t₀ * σ_param ^ 2 / 2 = σ_param * Real.sqrt (2 * Real.log ↑N) / 2 from by
        simp only [t₀]; rw [div_mul_eq_mul_div, div_div]
        rw [div_eq_div_iff (mul_ne_zero (ne_of_gt hσ) two_ne_zero) two_ne_zero]; ring]
    ring

/-! ### Helper lemmas for Sauer-Shelah exponential bound -/

private theorem ncard_restrictions_le_sum_choose_set {X : Type u}
    (C : ConceptClass X Bool) (S : Finset X) (d : ℕ)
    (hvc : VCDim X C = ↑d) :
    ({ f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } : Set (↥S → Bool)).ncard ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i := by
  classical
  set R := { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } with hR_def
  rw [Set.ncard_eq_toFinset_card']
  set R_fin := R.toFinset with hR_fin_def
  set AA := R_fin.image (fun f => Finset.univ.filter (fun x => f x = true)) with hAA_def
  have h_inj : Function.Injective
      (fun (f : ↥S → Bool) => Finset.univ.filter (fun x => f x = true)) := by
    intro f g hfg; funext x
    have := Finset.ext_iff.mp hfg x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    cases hf : f x <;> cases hg : g x <;> simp_all
  have h4 : AA.vcDim ≤ d := by
    simp only [Finset.vcDim]
    apply Finset.sup_le
    intro T hT
    have hTs : AA.Shatters T := Finset.mem_shatterer.mp hT
    set Tval := T.map ⟨Subtype.val, Subtype.val_injective⟩ with hTval_def
    suffices hShats : Shatters X C Tval by
      exact_mod_cast WithTop.coe_le_coe.mp (show (T.card : WithTop ℕ) ≤ ↑d from by
        rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩, ← hTval_def]
        exact (le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) => (S.card : WithTop ℕ))
          _ hShats).trans (le_of_eq hvc))
    intro g
    let g' : ↥S → Bool := fun x =>
      if h : (↑x : X) ∈ Tval then g ⟨↑x, h⟩ else false
    let t_sub : Finset ↥S := T.filter (fun x => g' x = true)
    have ht_sub : t_sub ⊆ T := Finset.filter_subset _ _
    obtain ⟨A, hA, hTA⟩ := hTs ht_sub
    simp only [hAA_def, Finset.mem_image] at hA
    obtain ⟨f, hf_mem, rfl⟩ := hA
    rw [Set.mem_toFinset] at hf_mem
    obtain ⟨c, hcC, hcf⟩ := hf_mem
    refine ⟨c, hcC, ?_⟩
    intro ⟨y, hyTval⟩
    obtain ⟨⟨y', hy'S⟩, hy'T, hy'eq⟩ := by rwa [hTval_def, Finset.mem_map] at hyTval
    simp only [Function.Embedding.coeFn_mk] at hy'eq
    subst hy'eq
    have hcf_y := hcf ⟨y', hy'S⟩
    have h1 : (⟨y', hy'S⟩ : ↥S) ∈ T ∩ Finset.univ.filter (fun x => f x = true) ↔
        f ⟨y', hy'S⟩ = true := by simp [Finset.mem_inter, Finset.mem_filter, hy'T]
    have h2 : (⟨y', hy'S⟩ : ↥S) ∈ t_sub ↔ g' ⟨y', hy'S⟩ = true := by
      simp [t_sub, Finset.mem_filter, hy'T]
    have h_f_iff_g' : f ⟨y', hy'S⟩ = true ↔ g' ⟨y', hy'S⟩ = true :=
      ⟨fun hf => h2.mp (hTA ▸ h1.mpr hf), fun hg => h1.mp (hTA ▸ h2.mpr hg)⟩
    have h_g'_eq : g' ⟨y', hy'S⟩ = g ⟨y', hyTval⟩ := by simp only [g', dif_pos hyTval]
    rw [hcf_y, ← h_g'_eq]
    cases hf : f ⟨y', hy'S⟩ <;> cases hg : g' ⟨y', hy'S⟩ <;> simp_all
  have h3 := @Finset.card_shatterer_le_sum_vcDim ↥S _ AA
  calc R.toFinset.card
      = AA.card := by rw [hAA_def]; exact (Finset.card_image_of_injective _ h_inj).symm
    _ ≤ AA.shatterer.card := Finset.card_le_card_shatterer AA
    _ ≤ ∑ k ∈ Finset.Iic AA.vcDim, (Fintype.card ↥S).choose k := h3
    _ = ∑ k ∈ Finset.Iic AA.vcDim, S.card.choose k := by rw [Fintype.card_coe]
    _ ≤ ∑ k ∈ Finset.Iic d, S.card.choose k :=
        Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr h4)
    _ = ∑ k ∈ Finset.range (d + 1), S.card.choose k := by
        congr 1; ext x; simp [Finset.mem_Iic, Finset.mem_range]

private theorem growth_function_le_sum_choose_set {X : Type u}
    (C : ConceptClass X Bool) (d m : ℕ) (_hdm : d ≤ m) (hvc : VCDim X C = ↑d) :
    GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by
  unfold GrowthFunction; apply csSup_le'
  intro n hn
  obtain ⟨⟨S, hSm⟩, rfl⟩ := hn
  change ({ f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } : Set _).ncard ≤ _
  exact (ncard_restrictions_le_sum_choose_set C S d hvc).trans (by rw [hSm])

theorem sum_choose_le_exp_pow (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) :
    (∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℝ) ≤ (Real.exp 1 * ↑m / ↑d) ^ d := by
  have hd_pos : (0 : ℝ) < ↑d := Nat.cast_pos.mpr hd
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hd hdm)
  have hdm_r : (d : ℝ) ≤ ↑m := Nat.cast_le.mpr hdm
  have hm_div_d_ge : (1 : ℝ) ≤ ↑m / ↑d := le_div_iff₀ hd_pos |>.mpr (by linarith)
  set t := (d : ℝ) / ↑m with ht_def
  have ht_pos : 0 < t := div_pos hd_pos hm_pos
  have h_partial_le_binom : ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i ≤
      (1 + t) ^ m := by
    rw [show (1 + t) ^ m = ∑ i ∈ Finset.range (m + 1), ↑(Nat.choose m i) * t ^ i from by
      have := add_pow t 1 m; rw [add_comm] at this; rw [this]
      congr 1; ext i; rw [one_pow, mul_one]; ring]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
    · intro i _ _; exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt ht_pos) _)
  have h_exp_bound : (1 + t) ^ m ≤ Real.exp 1 ^ d :=
    calc (1 + t) ^ m
        ≤ (Real.exp t) ^ m := pow_le_pow_left₀ (by linarith)
              (by linarith [Real.add_one_le_exp t]) m
      _ = Real.exp (t * ↑m) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ = Real.exp ↑d := by rw [show t * ↑m = ↑d from by simp only [ht_def]; field_simp]
      _ = Real.exp 1 ^ d := by rw [← Real.exp_nat_mul]; simp
  have h_factor : (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ)) ≤
      (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := by
    rw [Finset.sum_congr rfl (fun i _ => show (Nat.choose m i : ℝ) =
        ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ i from by
      rw [mul_assoc, ← mul_pow,
        show t * (↑m / ↑d) = 1 from by simp only [ht_def]; field_simp, one_pow, mul_one])]
    calc ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ i
        ≤ ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ d :=
          Finset.sum_le_sum (fun i hi => by
            apply mul_le_mul_of_nonneg_left
            · exact pow_right_mono₀ hm_div_d_ge (by simp only [Finset.mem_range] at hi; omega)
            · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt ht_pos) _))
      _ = (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := by
          rw [← Finset.sum_mul, mul_comm]
  calc (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ))
      ≤ (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := h_factor
    _ ≤ (↑m / ↑d) ^ d * ((1 + t) ^ m) := mul_le_mul_of_nonneg_left h_partial_le_binom
        (pow_nonneg (div_nonneg (le_of_lt hm_pos) (le_of_lt hd_pos)) d)
    _ ≤ (↑m / ↑d) ^ d * Real.exp 1 ^ d := mul_le_mul_of_nonneg_left h_exp_bound
        (pow_nonneg (div_nonneg (le_of_lt hm_pos) (le_of_lt hd_pos)) d)
    _ = (Real.exp 1 * ↑m / ↑d) ^ d := by rw [mul_div_assoc, ← mul_pow, mul_comm (Real.exp 1) _]

theorem sauer_shelah_exp_bound {X : Type u} (C : ConceptClass X Bool)
    (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) (hvc : VCDim X C = ↑d) :
    GrowthFunction X C m ≤ (Real.exp 1 * m / d) ^ d :=
  calc (↑(GrowthFunction X C m) : ℝ)
      ≤ ↑(∑ i ∈ Finset.range (d + 1), Nat.choose m i) := by
        exact_mod_cast growth_function_le_sum_choose_set C d m hdm hvc
    _ = (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ)) := by push_cast; rfl
    _ ≤ (Real.exp 1 * ↑m / ↑d) ^ d := sum_choose_le_exp_pow d m hd hdm

private theorem conceptClass_nonempty_of_vcdim_eq_pos {X : Type u}
    (C : ConceptClass X Bool) {d : ℕ} (hd : VCDim X C = ↑d) (hd_pos : 0 < d) :
    C.Nonempty := by
  by_contra hC_empty
  rw [Set.not_nonempty_iff_eq_empty] at hC_empty
  have hd0 : d = 0 := WithTop.coe_injective (hd.symm.trans (by
    simp only [VCDim]; apply le_antisymm _ bot_le; apply iSup₂_le; intro S hS
    exfalso; obtain ⟨c, hcC, _⟩ := hS (fun _ => true)
    rw [hC_empty] at hcC; exact hcC))
  omega

/-! ## VCDim → Rademacher bound -/

/-- VC dimension upper bounds Rademacher complexity: Rad ≤ √(2d·log(em/d)/m). -/
theorem vcdim_bounds_rademacher_quantitative (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (m : ℕ) (hm : 0 < m)
    (d : ℕ) (hd : VCDim X C = ↑d) (hd_pos : 0 < d) (hdm : d ≤ m)
    [MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.pi (fun _ : Fin m => D))] :
    RademacherComplexity X C D m ≤ Real.sqrt (2 * d * Real.log (Real.exp 1 * ↑m / d) / m) := by
  set B := Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m)
  suffices h_pw : ∀ (xs : Fin m → X), EmpiricalRademacherComplexity X C xs ≤ B by
    unfold RademacherComplexity
    calc ∫ xs, EmpiricalRademacherComplexity X C xs ∂(MeasureTheory.Measure.pi _)
        ≤ ∫ _xs, B ∂(MeasureTheory.Measure.pi (fun _ : Fin m => D)) := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact MeasureTheory.ae_of_all _
              (fun xs => empRad_nonneg C (Nat.pos_iff_ne_zero.mp hm) xs)
          · exact MeasureTheory.integrable_const B
          · exact MeasureTheory.ae_of_all _ h_pw
      _ = B := by simp [MeasureTheory.integral_const]
  intro xs
  by_cases hB1 : 1 ≤ B
  · exact le_trans (empiricalRademacherComplexity_le_one X C hm xs) hB1
  · push Not at hB1
    classical
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hd_pos_r : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
    have h1card_pos : (0 : ℝ) < 1 / (Fintype.card (SignVector m) : ℝ) := by positivity
    have hC_ne : C.Nonempty := conceptClass_nonempty_of_vcdim_eq_pos C hd hd_pos
    obtain ⟨h₀, hh₀⟩ := hC_ne
    let dpats : Finset (Fin m → Bool) :=
        Finset.univ.filter (fun p => ∃ h ∈ C, ∀ i, h (xs i) = p i)
    have hdpats_ne : dpats.Nonempty := by
      refine ⟨fun i => h₀ (xs i), ?_⟩
      simp only [dpats, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h₀, hh₀, fun _ => rfl⟩
    set cf : SignVector m → (Fin m → Bool) → ℝ :=
      fun σ p => (1 / (m : ℝ)) * ∑ i : Fin m, boolToSign (σ i) * boolToSign (p i)
    have h_corr_eq : ∀ (h : Concept X Bool) (σ : SignVector m),
        rademacherCorrelation h σ xs = cf σ (fun i => h (xs i)) := by
      intro h σ; unfold rademacherCorrelation
      rw [dif_neg (Nat.pos_iff_ne_zero.mp hm)]
    have h_mem_dpats : ∀ h ∈ C, (fun i => h (xs i)) ∈ dpats := fun h hh => by
      simp only [dpats, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h, hh, fun _ => rfl⟩
    have h_ssup_le_sup' : ∀ σ : SignVector m,
        sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } ≤
        dpats.sup' hdpats_ne (cf σ) := fun σ => by
      apply csSup_le
      · exact ⟨rademacherCorrelation h₀ σ xs, h₀, hh₀, rfl⟩
      · rintro r ⟨h, hh, rfl⟩; rw [h_corr_eq]
        exact Finset.le_sup' (cf σ) (h_mem_dpats h hh)
    have h_empRad_le : EmpiricalRademacherComplexity X C xs ≤
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ σ : SignVector m, dpats.sup' hdpats_ne (cf σ) := by
      unfold EmpiricalRademacherComplexity
      rw [dif_neg (Nat.pos_iff_ne_zero.mp hm)]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun σ _ => h_ssup_le_sup' σ)) (le_of_lt h1card_pos)
    set N := dpats.card
    have hN_pos : 0 < N := Finset.Nonempty.card_pos hdpats_ne
    have hcard_dpats : Fintype.card { p // p ∈ dpats } = N := Fintype.card_coe dpats
    let e : { p // p ∈ dpats } ≃ Fin N := hcard_dpats ▸ Fintype.equivFin _
    let Z : Fin N → SignVector m → ℝ := fun j σ => cf σ (e.symm j).val
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN_pos
    have h_empRad_le2 : EmpiricalRademacherComplexity X C xs ≤
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ σ : SignVector m, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j σ) :=
      h_empRad_le.trans_eq (by congr 1; exact Finset.sum_congr rfl (fun σ _ => by
        apply le_antisymm
        · rw [Finset.sup'_le_iff]; intro p hp
          exact Finset.le_sup'_of_le (f := fun j => Z j σ) (Finset.mem_univ (e ⟨p, hp⟩))
            (by change cf σ p ≤ cf σ (e.symm (e ⟨p, hp⟩)).val; simp [Equiv.symm_apply_apply])
        · rw [Finset.sup'_le_iff]; intro j _
          exact Finset.le_sup' (cf σ) (e.symm j).prop))
    set σ_param := (1 : ℝ) / Real.sqrt m
    have hσ_pos : 0 < σ_param := by positivity
    have h_mgf_Z : ∀ j : Fin N, ∀ t : ℝ, 0 ≤ t →
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ sv : SignVector m, Real.exp (t * Z j sv) ≤
        Real.exp (t ^ 2 * σ_param ^ 2 / 2) := by
      intro j t ht
      set p := (e.symm j).val with hp_def
      have h_bound := rademacher_mgf_bound hm (fun i => boolToSign (p i)) 1 (by norm_num)
        (fun i => le_of_eq (boolToSign_abs_eq_one (p i))) t ht
      have h_Z_rewrite : ∀ sv, Z j sv =
          (1 / (m : ℝ)) * ∑ i, (fun i => boolToSign (p i)) i * boolToSign (sv i) := fun sv => by
        change cf sv p = _; simp only [cf]
        congr 1; exact Finset.sum_congr rfl (fun i _ => by ring)
      simp_rw [show ∀ sv, Real.exp (t * Z j sv) = Real.exp (t * ((1 / (m : ℝ)) *
            ∑ i, (fun i => boolToSign (p i)) i * boolToSign (sv i))) from
          fun sv => by rw [h_Z_rewrite]]
      rwa [show t ^ 2 * σ_param ^ 2 / 2 = t ^ 2 * 1 ^ 2 / (2 * ↑m) from by
        rw [one_pow, mul_one, show σ_param = 1 / Real.sqrt ↑m from rfl]
        rw [one_div, inv_pow, Real.sq_sqrt (le_of_lt hm_pos)]; ring]
    have h_massart := finite_massart_lemma hm hN_pos Z σ_param hσ_pos h_mgf_Z
    set S := Finset.univ.image xs
    have h_dpats_card_le : (N : ℝ) ≤ (Real.exp 1 * ↑m / ↑d) ^ d := by
      set R := { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }
      have h_dpats_mem : ∀ p ∈ dpats, ∃ c ∈ C, ∀ i, c (xs i) = p i :=
        fun p hp => (Finset.mem_filter.mp hp).2
      have h_inj_card : N ≤ R.toFinset.card := by
        apply Finset.card_le_card_of_injOn
          (fun (p : Fin m → Bool) (x : ↥S) => p ((Finset.mem_image.mp x.prop).choose))
          (fun p hp => by
            obtain ⟨c, hcC, hc_agree⟩ := h_dpats_mem p hp
            exact Set.mem_toFinset.mpr ⟨c, hcC, fun ⟨x, hx⟩ => by
              change c x = p ((Finset.mem_image.mp hx).choose)
              conv_lhs => rw [← (Finset.mem_image.mp hx).choose_spec.2]; exact hc_agree _⟩)
          (fun p₁ hp₁ p₂ hp₂ heq => by
            obtain ⟨c₁, _, hc₁⟩ := h_dpats_mem p₁ hp₁
            obtain ⟨c₂, _, hc₂⟩ := h_dpats_mem p₂ hp₂
            funext i
            have hxi_in : xs i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
            rw [← hc₁ i, ← hc₂ i, ← (Finset.mem_image.mp hxi_in).choose_spec.2, hc₁, hc₂]
            exact congr_fun heq ⟨xs i, hxi_in⟩)
      have h_ncard_le := ncard_restrictions_le_sum_choose_set C S d hd
      calc (N : ℝ)
          ≤ ↑R.toFinset.card := by exact_mod_cast h_inj_card
        _ = ↑R.ncard := by rw [Set.ncard_eq_toFinset_card']
        _ ≤ ↑(∑ i ∈ Finset.range (d + 1), Nat.choose S.card i) := by exact_mod_cast h_ncard_le
        _ ≤ ↑(∑ i ∈ Finset.range (d + 1), Nat.choose m i) := by
            push_cast
            exact Finset.sum_le_sum (fun i _ => by
              exact_mod_cast Nat.choose_le_choose i (Finset.card_image_le.trans (by simp)))
        _ ≤ (Real.exp 1 * ↑m / ↑d) ^ d := by
            have := sum_choose_le_exp_pow d m hd_pos hdm; push_cast at this ⊢; exact this
    calc EmpiricalRademacherComplexity X C xs
        ≤ (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ σ, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j σ) := h_empRad_le2
      _ ≤ σ_param * Real.sqrt (2 * Real.log ↑N) := h_massart
      _ ≤ σ_param * Real.sqrt (2 * (↑d * Real.log (Real.exp 1 * ↑m / ↑d))) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hσ_pos)
          apply Real.sqrt_le_sqrt
          nlinarith [(Real.log_le_log (Nat.cast_pos.mpr hN_pos) h_dpats_card_le).trans
            (by rw [Real.log_pow])]
      _ = Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m) := by
          rw [show 2 * (↑d * Real.log (Real.exp 1 * ↑m / ↑d)) =
              2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) by ring]
          rw [show σ_param = 1 / Real.sqrt ↑m from rfl]
          rw [one_div, ← Real.sqrt_inv, ← Real.sqrt_mul (inv_nonneg.mpr (le_of_lt hm_pos))]
          congr 1; rw [inv_mul_eq_div]
      _ = B := rfl

/-! ## Rademacher ↔ PAC -/

/-- Key combinatorial lemma: injective samples from a shattered set have EmpRad = 1. -/
private theorem empRad_eq_one_of_injective_in_shattered {X : Type u}
    (C : ConceptClass X Bool) {m : ℕ} (hm : 0 < m)
    (T : Finset X) (hT : Shatters X C T)
    (xs : Fin m → X) (h_inj : Function.Injective xs)
    (h_range : ∀ i : Fin m, xs i ∈ T) :
    EmpiricalRademacherComplexity X C xs = 1 := by
  classical
  apply empRad_eq_one_of_all_labelings C hm xs
  intro σ
  set S := Finset.univ.image xs with hS_def
  have hS_shat : Shatters X C S := shatters_subset C T S (by
    intro x hx
    simp only [hS_def, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact h_range i) hT
  let f : ↥S → Bool := fun ⟨x, hx⟩ => σ (Finset.mem_image.mp hx).choose
  obtain ⟨c, hcC, hc_agree⟩ := hS_shat f
  refine ⟨c, hcC, fun i => ?_⟩
  have hxs_in_S : xs i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have h_agree_i := hc_agree ⟨xs i, hxs_in_S⟩
  change c (xs i) = σ i
  rw [h_agree_i]
  change σ (Finset.mem_image.mp hxs_in_S).choose = σ i
  congr 1
  apply h_inj
  exact (Finset.mem_image.mp hxs_in_S).choose_spec.2

private theorem uniform_injective_tuple_measure_half
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (hne : Nonempty α) (m : ℕ) (hlarge : 4 * m ^ 2 + 1 ≤ Fintype.card α) :
    let D_sub := uniformMeasure α hne
    let μ_sub := MeasureTheory.Measure.pi (fun _ : Fin m => D_sub)
    (1 : ℝ) / 2 ≤ (μ_sub {ys : Fin m → α | Function.Injective ys}).toReal := by
  classical
  intro D_sub μ_sub
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr hne
  have hD_sub_prob : MeasureTheory.IsProbabilityMeasure D_sub :=
    uniformMeasure_isProbability α hne hpos
  haveI : MeasureTheory.IsProbabilityMeasure μ_sub :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  set B := {ys : Fin m → α | Function.Injective ys}
  have hB_meas : MeasurableSet B := Set.Finite.measurableSet (Set.toFinite B)
  set n := Fintype.card α with hn_def
  have hn_pos : 0 < n := by rw [hn_def]; exact hpos
  have hn_ne : (n : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn_nt : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hDsub_sing : ∀ t : α, D_sub {t} = 1 / (n : ENNReal) := by
    intro t
    simp only [D_sub, uniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
    rw [@MeasureTheory.Measure.count_apply_finite' α _ _
      (Set.toFinite _) (measurableSet_singleton t)]
    simp [Set.Finite.toFinset, hn_def]
  haveI : MeasureTheory.IsFiniteMeasure D_sub := by
    constructor; rw [hD_sub_prob.measure_univ]; exact ENNReal.one_lt_top
  haveI : MeasureTheory.SigmaFinite D_sub :=
    @MeasureTheory.IsFiniteMeasure.toSigmaFinite α _ D_sub inferInstance
  set pairs := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2) with pairs_def
  have hBc_sub : Bᶜ ⊆ ⋃ p ∈ pairs, {ys : Fin m → α | ys p.1 = ys p.2} := by
    intro ys hys
    rw [Set.mem_compl_iff] at hys
    change ¬ Function.Injective ys at hys
    rw [Function.Injective] at hys
    push Not at hys
    obtain ⟨i, j, hij_eq, hij_ne⟩ := hys
    rw [Set.mem_iUnion]
    rcases lt_or_gt_of_ne hij_ne with h | h
    · exact ⟨(i, j), Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hij_eq⟩⟩
    · exact ⟨(j, i), Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hij_eq.symm⟩⟩
  have hcoll_bound : ∀ p ∈ pairs,
      μ_sub {ys : Fin m → α | ys p.1 = ys p.2} ≤ 1 / (n : ENNReal) := by
    intro ⟨i, j⟩ hp
    have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hp).2
    set Cij := {ys : Fin m → α | ys i = ys j}
    have hcyl : ∀ t : α, {ys : Fin m → α | ys i = t ∧ ys j = t} =
        Set.pi Set.univ (fun k => if k = i then {t} else if k = j then {t} else Set.univ) := by
      intro t; ext ys
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro ⟨h1, h2⟩ k
        split_ifs with hki hkj
        · exact hki ▸ h1
        · exact hkj ▸ h2
        · trivial
      · intro h
        constructor
        · simpa using h i
        · simpa [Ne.symm hij] using h j
    have hfiber_bound : ∀ t : α,
        μ_sub {ys : Fin m → α | ys i = t ∧ ys j = t} ≤ (1 / (n : ENNReal)) ^ 2 := by
      intro t
      rw [hcyl t]
      change (MeasureTheory.Measure.pi (fun _ : Fin m => D_sub)) _ ≤ _
      rw [MeasureTheory.Measure.pi_pi]
      have hfact_le : ∀ k : Fin m,
          D_sub (if k = i then {t} else if k = j then {t} else Set.univ) ≤
          (if k = i then 1 / (n : ENNReal) else if k = j then 1 / (n : ENNReal) else 1) := by
        intro k; split_ifs <;> [rw [hDsub_sing]; rw [hDsub_sing]; rw [hD_sub_prob.measure_univ]]
      have hfact_eq : ∀ k : Fin m,
          (if k = i then 1 / (n : ENNReal) else if k = j then 1 / (n : ENNReal) else 1) =
          (if k = i ∨ k = j then 1 / (n : ENNReal) else 1) := by
        intro k; split_ifs with h1 h2 h3 <;> simp_all
      calc ∏ k : Fin m, D_sub (if k = i then {t} else if k = j then {t} else Set.univ)
          ≤ ∏ k : Fin m,
              (if k = i ∨ k = j then 1 / (n : ENNReal) else 1) := by
            apply Finset.prod_le_prod'
            intro k _; exact (hfact_eq k) ▸ (hfact_le k)
        _ = (1 / (n : ENNReal)) ^ 2 := by
            have hprod_ij : ∏ k : Fin m,
                (if k = i ∨ k = j then 1 / (n : ENNReal) else 1) =
                1 / (n : ENNReal) * (1 / (n : ENNReal)) := by
              rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
              rw [← Finset.mul_prod_erase _ _
                (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
              rw [show ∏ k ∈ ((Finset.univ : Finset (Fin m)).erase i).erase j,
                  (if k = i ∨ k = j then 1 / (n : ENNReal) else 1) = 1 from
                Finset.prod_eq_one (fun k hk => by
                  simp [(Finset.mem_erase.mp hk).1,
                    (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1])]
              simp [hij, hij.symm, mul_one]
            rw [hprod_ij, sq]
    calc μ_sub Cij
        ≤ ∑ t : α, μ_sub {ys : Fin m → α | ys i = t ∧ ys j = t} := by
          conv_lhs => rw [show Cij = ⋃ t : α, {ys : Fin m → α | ys i = t ∧ ys j = t} from by
            ext ys; simp only [Cij, Set.mem_setOf_eq, Set.mem_iUnion]
            exact ⟨fun h => ⟨ys i, rfl, h.symm⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2.symm⟩]
          exact (MeasureTheory.measure_iUnion_le _).trans_eq (tsum_fintype _)
      _ ≤ ∑ _t : α, (1 / (n : ENNReal)) ^ 2 :=
          Finset.sum_le_sum (fun t _ => hfiber_bound t)
      _ = (n : ENNReal) * (1 / (n : ENNReal)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, hn_def, nsmul_eq_mul]
      _ = 1 / (n : ENNReal) := by
          rw [sq, ← mul_assoc]
          rw [show (↑n : ENNReal) * (1 / ↑n) = 1 from by
            rw [one_div, ENNReal.mul_inv_cancel hn_ne hn_nt], one_mul]
  have hBc_le : μ_sub Bᶜ ≤ pairs.card * (1 / (n : ENNReal)) :=
    calc μ_sub Bᶜ
        ≤ μ_sub (⋃ p ∈ pairs, {ys : Fin m → α | ys p.1 = ys p.2}) :=
          MeasureTheory.measure_mono hBc_sub
      _ ≤ ∑ p ∈ pairs, μ_sub {ys : Fin m → α | ys p.1 = ys p.2} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ ∑ _p ∈ pairs, (1 / (n : ENNReal)) :=
          Finset.sum_le_sum hcoll_bound
      _ = pairs.card * (1 / (n : ENNReal)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hBc_half : μ_sub Bᶜ ≤ 1 / 2 := by
    have hmm_le : (m * m : ℕ) * (1 / (n : ENNReal)) ≤ 1 / 2 := by
      have h_key : (↑(m * m) : ENNReal) ≤ (↑n : ENNReal) / 2 := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (2 : ENNReal) ≠ 0))
          (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤))]
        calc (↑(m * m) : ENNReal) * 2 = ↑(m * m * 2 : ℕ) := by push_cast; ring
          _ ≤ ↑n := Nat.cast_le.mpr (by rw [hn_def]; nlinarith [hlarge])
      calc (↑(m * m) : ENNReal) * (1 / ↑n)
          ≤ (↑n / 2) * (1 / ↑n) :=
            mul_le_mul_of_nonneg_right h_key (zero_le _)
        _ = 1 / 2 := by
            rw [one_div (↑n : ENNReal)]
            rw [div_eq_mul_inv, mul_assoc, mul_comm (2 : ENNReal)⁻¹ (↑n)⁻¹,
                ← mul_assoc, ENNReal.mul_inv_cancel hn_ne hn_nt, one_mul, inv_eq_one_div]
    exact (hBc_le.trans (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr ((Finset.card_filter_le _ _).trans (by simp [Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin]))) (zero_le _))).trans hmm_le
  have hB_ge : 1 / 2 ≤ μ_sub B := by
    rw [MeasureTheory.prob_compl_eq_one_sub hB_meas (μ := μ_sub)] at hBc_half
    have h1 : 1 - (1 : ENNReal) / 2 ≤ 1 - (1 - μ_sub B) := tsub_le_tsub_left hBc_half 1
    simp only [show (1 : ENNReal) - 1 / 2 = 1 / 2 from by norm_num] at h1
    rwa [ENNReal.sub_sub_cancel ENNReal.one_ne_top
      ((MeasureTheory.measure_mono (Set.subset_univ B)).trans
        (le_of_eq MeasureTheory.measure_univ))] at h1
  calc (1 : ℝ) / 2 = ((1 : ENNReal) / 2).toReal := by norm_num
    _ ≤ (μ_sub B).toReal :=
        ENNReal.toReal_mono (MeasureTheory.measure_ne_top μ_sub B) hB_ge

/-- Adversarial Rademacher lower bound on shattered sets. -/
theorem rademacher_lower_bound_on_shattered (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (T : Finset X) (hT : Shatters X C T)
    (m : ℕ) (hm : 0 < m) (hT_large : 4 * m ^ 2 + 1 ≤ T.card) :
    ∃ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ∧
      (1 : ℝ) / 2 ≤ RademacherComplexity X C D m := by
  classical
  have hT_ne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hT_large
  haveI : Fintype ↥T := T.fintypeCoeSort
  letI msT : MeasurableSpace ↥T := ⊤
  haveI : @MeasurableSingletonClass ↥T ⊤ := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hTne_type : Nonempty ↥T := hT_ne.coe_sort
  have hTpos : 0 < Fintype.card ↥T := by
    rw [Fintype.card_coe]; exact Finset.Nonempty.card_pos hT_ne
  let D_sub := @uniformMeasure ↥T ⊤ _ hTne_type
  have hD_sub_prob : @MeasureTheory.IsProbabilityMeasure ↥T ⊤ D_sub :=
    @uniformMeasure_isProbability ↥T ⊤ _ ⟨fun _ => trivial⟩ hTne_type hTpos
  have hval_meas : @Measurable ↥T X ⊤ _ Subtype.val :=
    fun _ _ => MeasurableSpace.measurableSet_top
  let D := @MeasureTheory.Measure.map ↥T X ⊤ _ Subtype.val D_sub
  have hDprob : MeasureTheory.IsProbabilityMeasure D := by
    constructor; show D Set.univ = 1
    simp only [D, MeasureTheory.Measure.map_apply hval_meas MeasurableSet.univ]
    rw [Set.preimage_univ]; exact hD_sub_prob.measure_univ
  refine ⟨D, hDprob, ?_⟩
  have hEmpRad_nn : ∀ xs : Fin m → X, 0 ≤ EmpiricalRademacherComplexity X C xs :=
    fun xs => empRad_nonneg C (Nat.pos_iff_ne_zero.mp hm) xs
  have hEmpRad_le : ∀ xs : Fin m → X, EmpiricalRademacherComplexity X C xs ≤ 1 :=
    fun xs => empiricalRademacherComplexity_le_one X C hm xs
  change (1 : ℝ) / 2 ≤ RademacherComplexity X C D m
  unfold RademacherComplexity
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  set A := { xs : Fin m → X | Function.Injective xs ∧ ∀ i, xs i ∈ T }
  haveI : MeasurableSingletonClass (Fin m → X) := Pi.instMeasurableSingletonClass
  have hA_meas : MeasurableSet A :=
    Set.Finite.measurableSet
      ((Set.Finite.pi' (fun _ => T.finite_toSet)).subset (fun xs ⟨_, hr⟩ => hr))
  haveI : MeasurableSingletonClass (Fin m → ↥T) := Pi.instMeasurableSingletonClass
  let μ_sub : MeasureTheory.Measure (Fin m → ↥T) :=
    MeasureTheory.Measure.pi (fun _ : Fin m => D_sub)
  haveI : MeasureTheory.IsProbabilityMeasure μ_sub :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  let φ : (Fin m → ↥T) → (Fin m → X) := fun ys i => Subtype.val (ys i)
  have hφ_emb : MeasurableEmbedding φ := by
    refine ⟨fun a b hab => funext (fun i => Subtype.val_injective (congr_fun hab i)),
      measurable_pi_lambda _ (fun i => hval_meas.comp (measurable_pi_apply i)),
      fun s _ => ?_⟩
    apply Set.Finite.measurableSet
    apply (Set.Finite.pi' (fun _ => T.finite_toSet)).subset
    intro xs hxs
    obtain ⟨ys, _, rfl⟩ := hxs
    exact fun i => (ys i).property
  have hμ_eq : μ = μ_sub.map φ := by
    simp only [μ, μ_sub, D, φ]
    exact (MeasureTheory.Measure.pi_map_pi (fun _ => hval_meas.aemeasurable)).symm
  have h_int_eq : ∫ xs, EmpiricalRademacherComplexity X C xs ∂μ =
      ∫ ys, EmpiricalRademacherComplexity X C (φ ys) ∂μ_sub := by
    conv_lhs => rw [hμ_eq]; exact hφ_emb.integral_map _
  have hf_sub_int : MeasureTheory.Integrable
      (fun ys => EmpiricalRademacherComplexity X C (φ ys)) μ_sub :=
    MeasureTheory.Integrable.of_bound (measurable_of_finite _).aestronglyMeasurable 1
      (MeasureTheory.ae_of_all _ (fun ys => by
        rw [Real.norm_of_nonneg (hEmpRad_nn _)]; exact hEmpRad_le _))
  have h_int_bound : (μ A).toReal ≤ ∫ xs, EmpiricalRademacherComplexity X C xs ∂μ := by
    rw [h_int_eq]
    set B := {ys : Fin m → ↥T | Function.Injective ys}
    have hB_meas : MeasurableSet B := Set.Finite.measurableSet (Set.toFinite B)
    have h_pw : ∀ ys : Fin m → ↥T,
        B.indicator (fun _ => (1 : ℝ)) ys ≤ EmpiricalRademacherComplexity X C (φ ys) := by
      intro ys; simp only [Set.indicator]; split
      · next hys => exact le_of_eq (empRad_eq_one_of_injective_in_shattered C hm T hT _
            (Subtype.val_injective.comp hys) (fun i => (ys i).property)).symm
      · exact hEmpRad_nn _
    calc (μ A).toReal
        ≤ (μ_sub B).toReal :=
          ENNReal.toReal_mono (MeasureTheory.measure_ne_top μ_sub _) (by
            rw [hμ_eq, MeasureTheory.Measure.map_apply hφ_emb.measurable hA_meas]
            apply MeasureTheory.measure_mono
            intro ys (hys : φ ys ∈ A); exact hys.1.of_comp)
      _ ≤ ∫ ys, EmpiricalRademacherComplexity X C (φ ys) ∂μ_sub := by
          linarith [MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ (fun ys =>
              Set.indicator_nonneg (fun _ _ => zero_le_one) ys))
            hf_sub_int (MeasureTheory.ae_of_all _ h_pw),
            show ∫ ys, B.indicator (fun _ => (1 : ℝ)) ys ∂μ_sub = (μ_sub B).toReal from by
              rw [MeasureTheory.integral_indicator hB_meas,
                MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]; rfl]
  suffices h_birthday : (1 : ℝ) / 2 ≤ (μ A).toReal by linarith
  set B := {ys : Fin m → ↥T | Function.Injective ys}
  rw [show μ A = μ_sub B from by
    rw [hμ_eq, MeasureTheory.Measure.map_apply hφ_emb.measurable hA_meas]
    congr 1; ext ys; constructor
    · intro (hys : φ ys ∈ A); exact hys.1.of_comp
    · intro (hys : Function.Injective ys)
      exact ⟨Subtype.val_injective.comp hys, fun i => (ys i).property⟩]
  simpa [μ_sub, D_sub, B] using
    uniform_injective_tuple_measure_half (α := ↥T) hTne_type m (by
      simpa [Fintype.card_coe] using hT_large)

/-- When VCDim = 0, all concepts in C agree on every point. -/
private theorem vcdim_zero_concepts_agree (X : Type u) (C : ConceptClass X Bool)
    (hd : VCDim X C = (0 : ℕ)) (h₁ h₂ : Concept X Bool) (hh₁ : h₁ ∈ C) (hh₂ : h₂ ∈ C)
    (x : X) : h₁ x = h₂ x := by
  by_contra hne
  have hshat : Shatters X C {x} := by
    intro f
    by_cases hf : f ⟨x, Finset.mem_singleton_self x⟩ = h₁ x
    · refine ⟨h₁, hh₁, fun ⟨y, hy⟩ => ?_⟩
      have hyx := Finset.mem_singleton.mp hy; subst hyx; exact hf.symm
    · have hf2 : f ⟨x, Finset.mem_singleton_self x⟩ = h₂ x := by
        cases hv1 : h₁ x <;> cases hv2 : h₂ x <;> simp_all
      refine ⟨h₂, hh₂, fun ⟨y, hy⟩ => ?_⟩
      have hyx := Finset.mem_singleton.mp hy; subst hyx; exact hf2.symm
  have h1le : (1 : WithTop ℕ) ≤ VCDim X C := le_iSup₂_of_le {x} hshat (by simp)
  rw [hd] at h1le; exact absurd h1le (by norm_num)

private theorem vcdim_zero_rademacher_le_inv_sqrt (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (hd : VCDim X C = (0 : ℕ))
    (m : ℕ) (hm : 0 < m)
    [MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.pi (fun _ : Fin m => D))] :
    RademacherComplexity X C D m ≤ 1 / Real.sqrt m := by
  by_cases hC : C.Nonempty
  · suffices h_pw : ∀ xs : Fin m → X, EmpiricalRademacherComplexity X C xs ≤ 1 / Real.sqrt m by
      unfold RademacherComplexity
      calc ∫ xs, EmpiricalRademacherComplexity X C xs ∂(MeasureTheory.Measure.pi _)
          ≤ ∫ _xs, (1 / Real.sqrt m) ∂(MeasureTheory.Measure.pi (fun _ : Fin m => D)) := by
            apply MeasureTheory.integral_mono_of_nonneg
            · exact MeasureTheory.ae_of_all _
                (fun xs => empRad_nonneg C (Nat.pos_iff_ne_zero.mp hm) xs)
            · exact MeasureTheory.integrable_const _
            · exact MeasureTheory.ae_of_all _ h_pw
        _ = 1 / Real.sqrt m := by simp [MeasureTheory.integral_const]
    intro xs
    obtain ⟨h₀, hh₀⟩ := hC
    have h_ssup_eq : ∀ σ : SignVector m,
        sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } =
          rademacherCorrelation h₀ σ xs := by
      intro σ
      have h_eq : { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } =
          {rademacherCorrelation h₀ σ xs} := by
        ext r; constructor
        · rintro ⟨h, hh, rfl⟩
          simp only [Set.mem_singleton_iff]
          unfold rademacherCorrelation; split
          · rfl
          · next hm' =>
            congr 1; apply Finset.sum_congr rfl; intro i _
            rw [vcdim_zero_concepts_agree X C hd h h₀ hh hh₀ (xs i)]
        · intro hr; rw [Set.mem_singleton_iff.mp hr]; exact ⟨h₀, hh₀, rfl⟩
      rw [h_eq, csSup_singleton]
    have h_emprad_zero : EmpiricalRademacherComplexity X C xs = 0 := by
      unfold EmpiricalRademacherComplexity
      rw [dif_neg (by omega)]
      simp_rw [h_ssup_eq]
      have : ∑ σ : SignVector m, rademacherCorrelation h₀ σ xs = 0 := by
        simp only [rademacherCorrelation, dif_neg (by omega : ¬m = 0)]
        rw [← Finset.mul_sum, Finset.sum_comm]
        have : ∀ i : Fin m, ∑ σ : SignVector m,
            boolToSign (σ i) * boolToSign (h₀ (xs i)) = 0 :=
          fun i => sum_boolToSign_cancel i (fun _ => boolToSign (h₀ (xs i)))
            (fun _ _ _ => rfl)
        simp [this]
      rw [this, mul_zero]
    rw [h_emprad_zero]
    exact div_nonneg one_pos.le (Real.sqrt_nonneg _)
  · rw [Set.not_nonempty_iff_eq_empty] at hC
    have h_emp_zero : ∀ xs : Fin m → X, EmpiricalRademacherComplexity X C xs = 0 := by
      intro xs
      unfold EmpiricalRademacherComplexity
      rw [dif_neg (by omega)]
      have h_ssup_zero : ∀ σ : SignVector m,
          sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } = 0 := by
        intro σ
        have : { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } = ∅ := by
          ext r; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨h, hh, _⟩; simp [hC] at hh
        rw [this, Real.sSup_empty]
      simp [h_ssup_zero]
    simp only [RademacherComplexity, show ∀ xs : Fin m → X,
        EmpiricalRademacherComplexity X C xs = 0 from h_emp_zero,
        MeasureTheory.integral_zero]
    exact div_nonneg one_pos.le (Real.sqrt_nonneg _)

private theorem analytical_log_sqrt_bound (d m : ℕ) (ε : ℝ)
    (hε : 0 < ε) (_hε1 : ε ≤ 1) (hd_pos : 0 < d) (hdm : d ≤ m)
    (hm_large : (Nat.ceil (32 * (↑d + 1) / ε ^ 4) + 1 : ℕ) ≤ m) :
    2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m < ε ^ 2 := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast Nat.lt_of_lt_of_le (by omega : 0 < d) hdm
  have hd_pos_r : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  set t := (m : ℝ) / d with ht_def
  have ht_pos : 0 < t := div_pos hm_pos hd_pos_r
  have h_rewrite : 2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m =
      2 * Real.log (Real.exp 1 * t) / t := by rw [ht_def]; field_simp
  rw [h_rewrite]
  have h_log_t_bound : Real.log t ≤ 2 * Real.sqrt t := by
    have h1 := Real.log_le_rpow_div (le_of_lt ht_pos) (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [show t ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) = 2 * t ^ (1 / 2 : ℝ) from by ring] at h1
    rwa [Real.sqrt_eq_rpow]
  rw [show 2 * Real.log (Real.exp 1 * t) / t = 2 / t + 2 * Real.log t / t from by
    rw [Real.log_mul (ne_of_gt he_pos) (ne_of_gt ht_pos), Real.log_exp]; ring]
  have h_mid : 2 / t + 2 * Real.log t / t ≤ 2 / t + 4 / Real.sqrt t := by
    have hle : 2 * Real.log t / t ≤ 4 * Real.sqrt t / t :=
      div_le_div_of_nonneg_right (by nlinarith [h_log_t_bound, Real.sqrt_nonneg t])
        (le_of_lt ht_pos)
    have h_sq : 4 * Real.sqrt t / t = 4 / Real.sqrt t := by
      rw [div_eq_div_iff (ne_of_gt ht_pos) (ne_of_gt (Real.sqrt_pos.mpr ht_pos)),
        show 4 * Real.sqrt t * Real.sqrt t = 4 * (Real.sqrt t * Real.sqrt t) from by ring,
        Real.mul_self_sqrt (le_of_lt ht_pos)]
    linarith [hle, h_sq.symm.le]
  have hε4_pos : (0 : ℝ) < ε ^ 4 := by positivity
  have hε2_pos : (0 : ℝ) < ε ^ 2 := by positivity
  have h_t_large : 32 / ε ^ 4 < t := by
    rw [ht_def, div_lt_div_iff₀ hε4_pos hd_pos_r]
    have hceil : (32 * (↑d + 1) / ε ^ 4 : ℝ) < m :=
      (Nat.le_ceil _).trans_lt (by exact_mod_cast (by omega : ⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊ < m))
    rw [div_lt_iff₀ hε4_pos] at hceil; nlinarith
  have h_sqrt_t_lower : 4 * Real.sqrt 2 / ε ^ 2 < Real.sqrt t := by
    rw [Real.lt_sqrt (by positivity)]
    calc (4 * Real.sqrt 2 / ε ^ 2) ^ 2
        = 32 / ε ^ 4 := by
          rw [div_pow, mul_pow, sq (Real.sqrt 2),
              Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
      _ < t := h_t_large
  have h_4_over_sqrt : 4 / Real.sqrt t < ε ^ 2 / Real.sqrt 2 := by
    rw [div_lt_div_iff₀ (Real.sqrt_pos.mpr ht_pos)
        (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
    calc 4 * Real.sqrt 2 = ε ^ 2 * (4 * Real.sqrt 2 / ε ^ 2) := by field_simp
      _ < ε ^ 2 * Real.sqrt t := mul_lt_mul_of_pos_left h_sqrt_t_lower hε2_pos
  have h_2_over_t : 2 / t < ε ^ 2 / 16 := by
    rw [div_lt_div_iff₀ ht_pos (by norm_num : (0:ℝ) < 16)]
    nlinarith [mul_lt_mul_of_pos_left h_t_large hε2_pos,
      show ε ^ 2 * (32 / ε ^ 4) = 32 / ε ^ 2 from by field_simp,
      show (32 : ℝ) ≤ 32 / ε ^ 2 from by rw [le_div_iff₀ hε2_pos]; nlinarith,
      show ε ^ 2 ≤ 1 from by nlinarith [_hε1]]
  linarith [h_mid, h_2_over_t, h_4_over_sqrt,
    show ε ^ 2 / Real.sqrt 2 < 3 * ε ^ 2 / 4 from by
      rw [div_lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))
          (by norm_num : (0:ℝ) < 4)]
      nlinarith [show (4 : ℝ) / 3 < Real.sqrt 2 from by
        rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 4 / 3)]; norm_num]]

/-- VCDim finite → Rademacher vanishes uniformly.
    The bound m₀ depends only on d and ε, NOT on D. -/
theorem vcdim_finite_imp_rademacher_vanishing (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hvcdim : VCDim X C < ⊤) :
    ∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D →
      ∀ m ≥ m₀, RademacherComplexity X C D m < ε := by
  rw [WithTop.lt_top_iff_ne_top] at hvcdim
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hvcdim
  intro ε hε
  by_cases hε1 : 1 < ε
  · use 1; intro D hD m hm
    haveI : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.pi (fun _ : Fin m => D)) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    exact lt_of_le_of_lt (rademacherComplexity_le_one X C D m (by omega)) hε1
  · push Not at hε1
    use max (d + 1) (Nat.ceil (32 * (↑d + 1) / ε ^ 4) + 1)
    intro D hD m hm
    have hm_pos : 0 < m := by omega
    haveI : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.pi (fun _ : Fin m => D)) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    by_cases hd_pos : d = 0
    · have hd0 : VCDim X C = (0 : ℕ) := by rw [← hd]; subst hd_pos; rfl
      calc RademacherComplexity X C D m
          ≤ 1 / Real.sqrt m := vcdim_zero_rademacher_le_inv_sqrt X C D hd0 m hm_pos
        _ < ε := by
          rw [div_lt_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm_pos))]
          have h_ceil_le_m : (32 * ((d : ℝ) + 1) / ε ^ 4 : ℝ) < m :=
            (Nat.le_ceil _).trans_lt (by exact_mod_cast
              (by omega : ⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊ < m))
          subst hd_pos; simp only [Nat.cast_zero, zero_add, mul_one] at h_ceil_le_m
          have hε2_pos : (0 : ℝ) < ε ^ 2 := by positivity
          have h_sqrt_m : 1 / ε < Real.sqrt m := by
            rw [Real.lt_sqrt (by positivity), div_pow, one_pow]
            linarith [show 1 / ε ^ 2 ≤ 32 / ε ^ 4 from by
              rw [div_le_div_iff₀ hε2_pos (by positivity)]
              nlinarith [show ε ^ 2 ≤ 1 from by nlinarith]]
          nlinarith [mul_lt_mul_of_pos_left h_sqrt_m hε, show ε * (1 / ε) = 1 from by field_simp]
    · have hd_pos' : 0 < d := Nat.pos_of_ne_zero hd_pos
      have hdm : d ≤ m := by omega
      calc RademacherComplexity X C D m
          ≤ Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m) :=
            vcdim_bounds_rademacher_quantitative X C D m hm_pos d hd.symm hd_pos' hdm
        _ < Real.sqrt (ε ^ 2) := by
            apply Real.sqrt_lt_sqrt
            · apply div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
                (Real.log_nonneg (by
                  rw [le_div_iff₀ (Nat.cast_pos.mpr hd_pos')]
                  nlinarith [Real.add_one_le_exp (1 : ℝ),
                    show (0 : ℝ) < d from Nat.cast_pos.mpr hd_pos',
                    show (d : ℝ) ≤ m from Nat.cast_le.mpr hdm,
                    Real.exp_pos 1])))
                (Nat.cast_nonneg m)
            · exact analytical_log_sqrt_bound d m ε hε hε1 hd_pos' hdm (by omega)
        _ = ε := by rw [Real.sqrt_sq (le_of_lt hε)]

-- fundamental_rademacher_equiv assembled in Theorem/PAC.lean (DAG constraint).
