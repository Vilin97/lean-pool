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
  calc |boolToSign b₁| * |boolToSign b₂|
      ≤ 1 * 1 := mul_le_mul (boolToSign_abs_le_one b₁) (boolToSign_abs_le_one b₂)
          (abs_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

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

/-- Rademacher cancellation: Σ_σ boolToSign(σ i) * f(σ) = 0
    when f doesn't depend on coordinate i.
    Proof: the bit-flip involution at coordinate i pairs each σ with flipAt i σ,
    negating boolToSign(σ i) while preserving f. -/
private theorem sum_boolToSign_cancel {m : ℕ} (i : Fin m) (f : SignVector m → ℝ)
    (hf : ∀ σ σ', (∀ k, k ≠ i → σ k = σ' k) → f σ = f σ') :
    ∑ σ : SignVector m, boolToSign (σ i) * f σ = 0 := by
  -- Use the involution flipAt i to show S = -S, hence S = 0.
  have hinv := flipAt_involutive i
  set g : SignVector m → ℝ := fun σ => boolToSign (σ i) * f σ
  -- Reindex: Σ g(σ) = Σ g(flipAt i σ) since flipAt i is a bijection.
  have h_eq : ∑ σ : SignVector m, g σ =
      ∑ σ : SignVector m, g (flipAt i σ) := by
    let e : SignVector m ≃ SignVector m := Equiv.ofBijective (flipAt i) hinv.bijective
    rw [show ∑ σ, g (flipAt i σ) = ∑ σ, g (e σ) from rfl]
    exact (Equiv.sum_comp e g).symm
  -- g(flipAt i σ) = -g(σ) since flipAt negates boolToSign at i but preserves f.
  have h_neg : ∀ σ, g (flipAt i σ) = -g σ := by
    intro σ
    change boolToSign (flipAt i σ i) * f (flipAt i σ) =
      -(boolToSign (σ i) * f σ)
    rw [flipAt_boolToSign, hf (flipAt i σ) σ (fun k hk => flipAt_other i σ k hk)]
    ring
  -- So S = Σ g(σ) = Σ -g(σ) = -S.
  have h_neg_sum : ∑ σ : SignVector m, g σ = -(∑ σ : SignVector m, g σ) := by
    conv_lhs => rw [h_eq]
    simp_rw [h_neg]
    simp [Finset.sum_neg_distrib]
  linarith

/-- Rademacher cross-term cancellation: Σ_σ boolToSign(σ i) * boolToSign(σ j) = 0 for i ≠ j.
    Follows from sum_boolToSign_cancel since boolToSign(σ j) doesn't depend on coordinate i. -/
private theorem rademacher_cross_cancel {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ∑ σ : SignVector m, boolToSign (σ i) * boolToSign (σ j) = 0 := by
  exact sum_boolToSign_cancel i (fun σ => boolToSign (σ j))
    (fun σ σ' h => by rw [h j hij.symm])

/-- Rademacher diagonal: Σ_σ boolToSign(σ i)² = |SignVector m| = 2^m. -/
private theorem rademacher_diagonal {m : ℕ} (i : Fin m) :
    ∑ σ : SignVector m, boolToSign (σ i) ^ 2 = (Fintype.card (SignVector m) : ℝ) := by
  simp_rw [boolToSign_sq]
  simp [Finset.sum_const, Finset.card_univ]

/-- Rademacher variance identity:
    Σ_σ (Σ_i boolToSign(σ i) * a_i)² = m * |SignVector m|
    when |a_i| = 1. Uses cross-term cancellation (rademacher_cross_cancel)
    and diagonal identity (rademacher_diagonal). -/
private theorem rademacher_variance_eq {m : ℕ} (_hm : 0 < m) (a : Fin m → ℝ)
    (ha : ∀ i, |a i| = 1) :
    ∑ σ : SignVector m, (∑ i : Fin m, boolToSign (σ i) * a i) ^ 2 =
      (m : ℝ) * (Fintype.card (SignVector m) : ℝ) := by
  set N := (Fintype.card (SignVector m) : ℝ)
  -- Suffices: show each coordinate contributes N to the sum, giving m * N.
  suffices h_each : ∀ i : Fin m, ∑ σ : SignVector m,
      ∑ j : Fin m, (boolToSign (σ i) * a i) * (boolToSign (σ j) * a j) = N by
    -- Step 1: Expand (Σ f_i)² = Σ_i Σ_j f_i * f_j
    simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
    -- Step 2: Swap outermost sums: Σ_σ Σ_i ... = Σ_i Σ_σ ...
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    -- Now goal is Σ_i (Σ_σ Σ_j ...) = m * N
    -- Each inner sum = N by h_each, so Σ_i N = m * N.
    simp_rw [h_each]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- Prove: for fixed i, Σ_σ Σ_j (boolToSign(σ i) * a_i) * (boolToSign(σ j) * a_j) = N.
  intro i
  -- Swap: Σ_σ Σ_j ... = Σ_j Σ_σ ...
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  -- Factor out a terms in each inner sum.
  have h_term : ∀ j : Fin m, ∑ σ : SignVector m,
      (boolToSign (σ i) * a i) * (boolToSign (σ j) * a j) =
      (a i * a j) * ∑ σ : SignVector m, boolToSign (σ i) * boolToSign (σ j) := by
    intro j; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro σ _; ring
  simp_rw [h_term]
  -- Split into j = i (diagonal) and j ≠ i (cross terms).
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  -- After simp_rw [h_term], the goal is:
  -- Σ_j (a i * a j) * Σ_σ boolToSign(σ i) * boolToSign(σ j) = N
  -- After rw [← Finset.add_sum_erase]:
  -- (a i * a i) * (Σ_σ ...) + Σ_{j ∈ erase i} ... = N
  -- Cross terms vanish, diagonal = N.
  --
  -- Cross terms are 0.
  have h_cross : ∀ j, j ≠ i →
      a i * a j * ∑ σ : SignVector m, boolToSign (σ i) * boolToSign (σ j) = 0 := by
    intro j hj
    rw [rademacher_cross_cancel i j hj.symm, mul_zero]
  have h_cross_sum : ∑ j ∈ Finset.univ.erase i, a i * a j *
      ∑ σ : SignVector m, boolToSign (σ i) * boolToSign (σ j) = 0 :=
    Finset.sum_eq_zero (fun j hj => h_cross j (Finset.ne_of_mem_erase hj))
  rw [h_cross_sum, add_zero]
  -- Diagonal
  have h_diag : ∑ σ : SignVector m, boolToSign (σ i) * boolToSign (σ i) =
      ∑ σ : SignVector m, boolToSign (σ i) ^ 2 :=
    Finset.sum_congr rfl (fun σ _ => by ring)
  rw [h_diag, rademacher_diagonal]
  have hai : a i * a i = 1 := by
    have hab := ha i
    have : a i ^ 2 = 1 := by nlinarith [sq_abs (a i)]
    nlinarith [this]
  rw [hai, one_mul]

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
  have hsum_le : |∑ i : Fin m, boolToSign (σ i) * boolToSign (h (xs i))| ≤ m := by
    let f := fun i : Fin m => boolToSign (σ i) * boolToSign (h (xs i))
    change |∑ i, f i| ≤ ↑m
    have h1 : |∑ i, f i| ≤ ∑ i, ‖f i‖ := norm_sum_le Finset.univ f
    have h2 : ∀ i : Fin m, ‖f i‖ ≤ 1 := by
      intro i; rw [Real.norm_eq_abs]; exact boolToSign_mul_abs_le_one (σ i) (h (xs i))
    have h3 : ∑ i : Fin m, ‖f i‖ ≤ ∑ _i : Fin m, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => h2 i)
    have h4 : ∑ _i : Fin m, (1 : ℝ) = m := by simp [Finset.sum_const]
    linarith
  calc 1 / (m : ℝ) * |∑ i, boolToSign (σ i) * boolToSign (h (xs i))|
      ≤ 1 / m * m := by
        apply mul_le_mul_of_nonneg_left hsum_le
        exact div_nonneg one_pos.le hm_pos.le
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
  apply mul_nonneg
  · apply div_nonneg one_pos.le; exact Nat.cast_nonneg _
  · by_cases hC : C.Nonempty
    · obtain ⟨h₀, hh₀⟩ := hC
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
      have hbdd : ∀ σ, BddAbove { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } := by
        intro σ; refine ⟨1, fun r hr => ?_⟩
        obtain ⟨h', _, rfl⟩ := hr
        exact le_trans (le_abs_self _) (rademacherCorrelation_abs_le_one hm_pos h' σ xs)
      have h_ge : ∀ σ : SignVector m,
          rademacherCorrelation h₀ σ xs ≤
            sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } :=
        fun σ => le_csSup_of_le (hbdd σ) ⟨h₀, hh₀, rfl⟩ le_rfl
      have h_sum_corr : ∑ σ : SignVector m, rademacherCorrelation h₀ σ xs = 0 := by
        simp only [rademacherCorrelation, dif_neg hm]
        rw [← Finset.mul_sum, Finset.sum_comm]
        have : ∀ i : Fin m, ∑ σ : SignVector m,
            boolToSign (σ i) * boolToSign (h₀ (xs i)) = 0 :=
          fun i => sum_boolToSign_cancel i (fun _ => boolToSign (h₀ (xs i)))
            (fun _ _ _ => rfl)
        simp [this]
      calc (0 : ℝ) = ∑ σ : SignVector m, rademacherCorrelation h₀ σ xs := h_sum_corr.symm
        _ ≤ ∑ σ : SignVector m,
              sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } :=
            Finset.sum_le_sum (fun σ _ => h_ge σ)
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
    0 ≤ RademacherComplexity X C D m := by
  unfold RademacherComplexity
  apply MeasureTheory.integral_nonneg
  intro xs
  exact empRad_nonneg C (Nat.pos_iff_ne_zero.mp hm) xs

theorem rademacher_gen_bound (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure D]
    (m : ℕ) (hm : 0 < m) (c : Concept X Bool) (_hcC : c ∈ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (bound : ℝ), bound = 2 * RademacherComplexity X C D m + ε ∧ bound ≥ 0 := by
  refine ⟨2 * RademacherComplexity X C D m + ε, rfl, ?_⟩
  linarith [rademacherComplexity_nonneg X C D m hm]

/-- When h agrees with σ on all sample points, correlation is exactly 1. -/
private theorem corr_eq_one_of_agree {X : Type u} {m : ℕ} (hm : 0 < m)
    (h : Concept X Bool) (σ : SignVector m) (xs : Fin m → X)
    (hagree : ∀ i : Fin m, h (xs i) = σ i) :
    rademacherCorrelation h σ xs = 1 := by
  unfold rademacherCorrelation
  rw [dif_neg (by omega)]
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  -- Each term boolToSign(σ i) * boolToSign(h(xs i)) = boolToSign(σ i)² = 1
  have h_terms : ∀ i : Fin m,
      boolToSign (σ i) * boolToSign (h (xs i)) = 1 := by
    intro i; rw [hagree i]; exact by unfold boolToSign; cases σ i <;> simp
  simp_rw [h_terms]
  simp [Finset.sum_const]
  field_simp

/-- Subset of a shattered set is shattered. -/
private theorem shatters_subset {X : Type u} (C : ConceptClass X Bool)
    (T S : Finset X) (hTS : S ⊆ T) (hT : Shatters X C T) :
    Shatters X C S := by
  classical
  intro f
  -- Extend f to a labeling of T: f on S, true elsewhere
  let g : ↥T → Bool := fun ⟨x, _⟩ =>
    if hxS : x ∈ S then f ⟨x, hxS⟩ else true
  obtain ⟨c, hcC, hcT⟩ := hT g
  refine ⟨c, hcC, fun ⟨x, hxS⟩ => ?_⟩
  have hxT : x ∈ T := hTS hxS
  have h := hcT ⟨x, hxT⟩
  change c x = f ⟨x, hxS⟩
  rw [h]; show g ⟨x, hxT⟩ = f ⟨x, hxS⟩
  simp only [g, dif_pos hxS]

/-- On samples where every labeling is realizable, EmpRad = 1.

    For each sign vector σ, the hypothesis provides h ∈ C with h(xs i) = σ i,
    giving corr(h,σ,xs) = 1. Since |corr| ≤ 1, the sSup is exactly 1.
    Averaging over all σ gives EmpRad = (1 / 2^m)·2^m·1 = 1.

    This is the combinatorial core of the NFL Rademacher lower bound:
    when xs are distinct points from a shattered set, every labeling
    is realized, so this lemma applies. -/
private theorem empRad_eq_one_of_all_labelings {X : Type u}
    (C : ConceptClass X Bool) {m : ℕ} (hm : 0 < m) (xs : Fin m → X)
    (h_realize : ∀ σ : SignVector m, ∃ h ∈ C, ∀ i : Fin m, h (xs i) = σ i) :
    EmpiricalRademacherComplexity X C xs = 1 := by
  -- For each σ, sSup = 1.
  have h_ssup_eq_one : ∀ σ : SignVector m,
      sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } = 1 := by
    intro σ
    apply le_antisymm
    · -- sSup ≤ 1
      apply csSup_le
      · obtain ⟨c, hcC, _⟩ := h_realize σ
        exact ⟨rademacherCorrelation c σ xs, c, hcC, rfl⟩
      · rintro r ⟨h, _, rfl⟩
        exact le_trans (le_abs_self _) (rademacherCorrelation_abs_le_one hm h σ xs)
    · -- sSup ≥ 1: use h with corr = 1
      obtain ⟨c, hcC, hc_agree⟩ := h_realize σ
      have hcorr : rademacherCorrelation c σ xs = 1 :=
        corr_eq_one_of_agree hm c σ xs hc_agree
      have hbdd : BddAbove { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } := by
        refine ⟨1, fun r hr => ?_⟩
        obtain ⟨h', _, rfl⟩ := hr
        exact le_trans (le_abs_self _) (rademacherCorrelation_abs_le_one hm h' σ xs)
      exact le_csSup_of_le hbdd ⟨c, hcC, rfl⟩ (by rw [hcorr])
  -- EmpRad = (1/N) * Σ_σ 1 = 1
  unfold EmpiricalRademacherComplexity
  rw [dif_neg (by omega)]
  simp_rw [h_ssup_eq_one]
  simp [Finset.sum_const, Finset.card_univ]

/-! ## Helpers for VCDim → Rademacher bound (Massart + Sauer-Shelah) -/

/-- Soft-max bound: exp(t · Finset.sup') ≤ Σ exp(t · f_i). -/
theorem exp_mul_sup'_le_sum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) (_ht : 0 ≤ t) :
    Real.exp (t * s.sup' hs f) ≤ ∑ i ∈ s, Real.exp (t * f i) := by
  -- sup' is achieved: ∃ i₀ ∈ s, f i₀ = sup' (since ℝ is LinearOrder, s finite nonempty)
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_mem_eq_sup' hs f
  -- exp(t * f i₀) ≤ ∑ exp(t * f i) since i₀ ∈ s and all terms are nonneg
  calc Real.exp (t * s.sup' hs f)
      = Real.exp (t * f i₀) := by rw [hmax]
    _ ≤ ∑ i ∈ s, Real.exp (t * f i) :=
        Finset.single_le_sum (f := fun i => Real.exp (t * f i))
          (fun i _ => (Real.exp_pos (t * f i)).le) hi₀

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
  -- Step 1: Normalize the exp argument as a Finset sum, then factor into a product
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
  -- Goal: (1/card) * ∑ σ, ∏ i, exp(t*a_i*σ_i/m) ≤ exp(t²c²/(2m))
  -- Step 2: Swap sum over σ and product over i
  -- ∑ σ : (Fin m → Bool), ∏ i, g i (σ i) = ∏ i, ∑ b, g i b
  rw [show ∑ σ : SignVector m, ∏ i : Fin m, Real.exp (t * a i * boolToSign (σ i) / ↑m) =
      ∏ i : Fin m, ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) from by
    rw [← Fintype.piFinset_univ (β := fun _ : Fin m => Bool)]
    exact Finset.sum_prod_piFinset Finset.univ
      (fun (i : Fin m) (b : Bool) => Real.exp (t * a i * boolToSign b / ↑m))]
  -- Step 2b: Distribute (1/card) = (1 / 2)^m into the product
  have hcard_eq : (Fintype.card (SignVector m) : ℝ) = (2 : ℝ) ^ m := by
    have : Fintype.card (SignVector m) = 2 ^ m := by
      change Fintype.card (Fin m → Bool) = 2 ^ m
      simp [Fintype.card_fin, Fintype.card_bool]
    push_cast [this]; rfl
  have h_inv : (1 : ℝ) / (Fintype.card (SignVector m) : ℝ) = (1 / 2 : ℝ) ^ m := by
    rw [hcard_eq, one_div, one_div, inv_pow]
  rw [h_inv]
  have h_prod_const : ((1 / 2 : ℝ) ^ m : ℝ) = ∏ _i : Fin m, (1 / 2 : ℝ) := by
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h_prod_const, ← Finset.prod_mul_distrib]
  -- Goal: ∏ i, (1 / 2) * ∑ b, exp(t*a_i*boolToSign(b)/m) ≤ exp(t²c²/(2m))
  -- Step 3: Each factor ≤ exp((t*a_i/m)²/2)
  have h_factor_bound : ∀ i : Fin m,
      (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) ≤
      Real.exp ((t * a i / ↑m) ^ 2 / 2) := by
    intro i
    -- Show the sum equals exp(u) + exp(-u) where u = t * a i / m
    set u := t * a i / (↑m : ℝ) with hu_def
    have h_sum_eq : ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) =
        Real.exp u + Real.exp (-u) := by
      simp only [Fintype.sum_bool, boolToSign, ↓reduceIte, Bool.false_eq_true]
      congr 1
      · congr 1; rw [hu_def]; ring
      · congr 1; rw [hu_def]; ring
    rw [h_sum_eq]
    -- (1 / 2) * (exp(u) + exp(-u)) = cosh(u) ≤ exp(u²/2)
    have h_eq_cosh : (1 / 2 : ℝ) * (Real.exp u + Real.exp (-u)) = Real.cosh u := by
      rw [Real.cosh_eq]; ring
    rw [h_eq_cosh]
    exact cosh_le_exp_sq_half _
  -- Each factor is nonneg
  have h_factor_nonneg : ∀ i ∈ Finset.univ (α := Fin m),
      0 ≤ (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) := by
    intro i _
    apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)
    apply Finset.sum_nonneg; intro b _; exact (Real.exp_pos _).le
  -- Step 4: Product inequality → exponential sum → final bound
  calc ∏ i : Fin m, (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m)
      ≤ ∏ i : Fin m, Real.exp ((t * a i / ↑m) ^ 2 / 2) :=
        Finset.prod_le_prod h_factor_nonneg (fun i _ => h_factor_bound i)
    _ = Real.exp (∑ i : Fin m, (t * a i / ↑m) ^ 2 / 2) :=
        (Real.exp_sum Finset.univ _).symm
    _ ≤ Real.exp (t ^ 2 * c ^ 2 / (2 * ↑m)) := by
        apply Real.exp_le_exp_of_le
        -- ∑ (t*a_i/m)²/2 = t²/(2m²) * ∑ a_i² ≤ t²/(2m²) * m*c² = t²c²/(2m)
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
  -- Abbreviation for the LHS (the "expected maximum")
  set E_max := (1 / (Fintype.card (SignVector m) : ℝ)) *
    ∑ sv : SignVector m, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv)
  -- Card of SignVector m is positive (= 2^m > 0)
  have hcard_pos : (0 : ℝ) < (Fintype.card (SignVector m) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := SignVector m)
  have hcard_ne : (Fintype.card (SignVector m) : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have h1card_pos : (0 : ℝ) < 1 / (Fintype.card (SignVector m) : ℝ) := by positivity
  -- Step A: For all t > 0, exp(t * E_max) ≤ N * exp(t²σ²/2)
  have h_exp_bound : ∀ t : ℝ, 0 < t →
      Real.exp (t * E_max) ≤ ↑N * Real.exp (t ^ 2 * σ_param ^ 2 / 2) := by
    intro t ht
    -- A1: Jensen for convex exp with uniform weights 1/|SV|
    have h_jensen : Real.exp (t * E_max) ≤
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ sv : SignVector m, Real.exp (t * Finset.univ.sup' Finset.univ_nonempty
            (fun j => Z j sv)) := by
      have h_weights_pos : ∀ sv ∈ Finset.univ (α := SignVector m),
          (0 : ℝ) ≤ 1 / (Fintype.card (SignVector m) : ℝ) :=
        fun _ _ => le_of_lt h1card_pos
      have h_weights_sum : ∑ _ : SignVector m, (1 / (Fintype.card (SignVector m) : ℝ)) = 1 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have h_mem : ∀ sv ∈ Finset.univ (α := SignVector m),
          t * Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv) ∈ Set.univ :=
        fun _ _ => Set.mem_univ _
      have h_conv := convexOn_exp.map_sum_le (t := Finset.univ)
        (w := fun _ => 1 / (Fintype.card (SignVector m) : ℝ))
        (p := fun sv => t * Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv))
        h_weights_pos h_weights_sum h_mem
      simp only [smul_eq_mul] at h_conv
      -- h_conv: exp(∑ w * p) ≤ ∑ w * exp(p)
      -- RHS = ∑ (1/card * exp(...)) = (1/card) * ∑ exp(...)
      rw [Finset.mul_sum]
      -- Now goal: exp(t * E_max) ≤ ∑ (1/card * exp(...))
      -- Suffices: t * E_max = ∑ (1/card * (t * sup'))
      refine le_trans ?_ h_conv
      apply le_of_eq; congr 1
      simp only [E_max, ← Finset.mul_sum]; ring
    -- A2: Softmax for each σ
    have h_softmax : ∀ sv : SignVector m,
        Real.exp (t * Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv)) ≤
          ∑ j : Fin N, Real.exp (t * Z j sv) := by
      intro sv
      exact exp_mul_sup'_le_sum Finset.univ Finset.univ_nonempty
        (fun j => Z j sv) t (le_of_lt ht)
    -- A3: Swap sums and apply MGF bound
    have h_swap : (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ sv : SignVector m, ∑ j : Fin N, Real.exp (t * Z j sv) =
        ∑ j : Fin N, (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ sv : SignVector m, Real.exp (t * Z j sv) := by
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    have h_mgf_applied : ∑ j : Fin N,
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ sv : SignVector m, Real.exp (t * Z j sv) ≤
        ∑ _ : Fin N, Real.exp (t ^ 2 * σ_param ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro j _
      exact h_mgf j t (le_of_lt ht)
    have h_const_sum : ∑ _ : Fin N, Real.exp (t ^ 2 * σ_param ^ 2 / 2) =
        ↑N * Real.exp (t ^ 2 * σ_param ^ 2 / 2) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    -- Chain everything
    calc Real.exp (t * E_max)
        ≤ (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ sv, Real.exp (t * Finset.univ.sup' Finset.univ_nonempty
              (fun j => Z j sv)) := h_jensen
      _ ≤ (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ sv, ∑ j, Real.exp (t * Z j sv) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt h1card_pos)
          exact Finset.sum_le_sum (fun sv _ => h_softmax sv)
      _ = ∑ j, (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ sv, Real.exp (t * Z j sv) := h_swap
      _ ≤ ∑ _, Real.exp (t ^ 2 * σ_param ^ 2 / 2) := h_mgf_applied
      _ = ↑N * Real.exp (t ^ 2 * σ_param ^ 2 / 2) := h_const_sum
  -- Step B: For all t > 0: E_max ≤ log N / t + t * σ² / 2
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  have h_linear_bound : ∀ t : ℝ, 0 < t →
      E_max ≤ Real.log N / t + t * σ_param ^ 2 / 2 := by
    intro t ht
    have h_exp := h_exp_bound t ht
    -- Take log: t * E_max ≤ log(N * exp(t²σ²/2)) = log N + t²σ²/2
    have h_log : t * E_max ≤ Real.log N + t ^ 2 * σ_param ^ 2 / 2 := by
      have h1 : t * E_max ≤ Real.log (↑N * Real.exp (t ^ 2 * σ_param ^ 2 / 2)) := by
        rw [← Real.log_exp (t * E_max)]
        exact Real.log_le_log (Real.exp_pos _) h_exp
      rw [Real.log_mul (ne_of_gt hN_pos) (ne_of_gt (Real.exp_pos _)),
          Real.log_exp] at h1
      exact h1
    -- Divide by t: E_max ≤ (log N + t²σ²/2) / t = log N / t + tσ²/2
    have ht_ne : t ≠ 0 := ne_of_gt ht
    rw [div_add_div _ _ ht_ne (ne_of_gt (by positivity : (0:ℝ) < 2))]
    rw [le_div_iff₀ (mul_pos ht (by positivity : (0:ℝ) < 2))]
    nlinarith [sq_nonneg t]
  -- Step C: Optimize over t
  have hlog_N_nonneg : 0 ≤ Real.log ↑N := Real.log_natCast_nonneg N
  have h2log_nonneg : 0 ≤ 2 * Real.log ↑N := by linarith
  by_cases hlog : Real.log ↑N = 0
  · -- N = 1 case: RHS = σ * √(2 * 0) = 0
    simp only [hlog, mul_zero, Real.sqrt_zero, mul_zero]
    -- Need: E_max ≤ 0. From bound: ∀ t > 0, E_max ≤ 0/t + tσ²/2 = tσ²/2
    -- By contradiction: if E_max > 0, choose t = E_max/σ² to get E_max ≤ E_max/2
    by_contra h_neg
    push Not at h_neg
    have hσ2_pos : 0 < σ_param ^ 2 := sq_pos_of_pos hσ
    set t₀ := E_max / σ_param ^ 2 with ht₀_def
    have ht₀_pos : 0 < t₀ := div_pos h_neg hσ2_pos
    have h_bd := h_linear_bound t₀ ht₀_pos
    rw [hlog] at h_bd
    simp only [zero_div, zero_add] at h_bd
    -- h_bd : E_max ≤ t₀ * σ² / 2 = (E_max / σ²) * σ² / 2 = E_max / 2
    have : t₀ * σ_param ^ 2 / 2 = E_max / 2 := by
      rw [ht₀_def]; field_simp
    rw [this] at h_bd
    linarith
  · -- N ≥ 2 case: log N > 0
    have hlog_pos : 0 < Real.log ↑N := lt_of_le_of_ne hlog_N_nonneg (Ne.symm hlog)
    have hsqrt_pos : 0 < Real.sqrt (2 * Real.log ↑N) :=
      Real.sqrt_pos_of_pos (by linarith)
    -- Set t = √(2 log N) / σ
    set t₀ := Real.sqrt (2 * Real.log ↑N) / σ_param
    have ht₀_pos : 0 < t₀ := div_pos hsqrt_pos hσ
    have h_bd := h_linear_bound t₀ ht₀_pos
    -- Show: log N / t₀ + t₀ * σ² / 2 = σ * √(2 log N)
    suffices h_eq : Real.log ↑N / t₀ + t₀ * σ_param ^ 2 / 2 =
        σ_param * Real.sqrt (2 * Real.log ↑N) from le_trans h_bd (le_of_eq h_eq)
    have hσ_ne : σ_param ≠ 0 := ne_of_gt hσ
    have hsqrt_ne : Real.sqrt (2 * Real.log ↑N) ≠ 0 := ne_of_gt hsqrt_pos
    have hsq : Real.sqrt (2 * Real.log ↑N) ^ 2 = 2 * Real.log ↑N := Real.sq_sqrt h2log_nonneg
    -- Both terms equal σ * √(2 log N) / 2, so their sum = σ * √(2 log N)
    -- Direct computation after unfolding t₀
    change Real.log ↑N / t₀ + t₀ * σ_param ^ 2 / 2 = σ_param * Real.sqrt (2 * Real.log ↑N)
    have ht₀_ne : t₀ ≠ 0 := ne_of_gt ht₀_pos
    -- Rewrite as: (2 * log N + t₀² * σ²) / (2 * t₀) = σ * √(2 log N)
    -- where t₀ = √(2 log N) / σ, so t₀² = 2 log N / σ²
    -- thus 2 * log N + (2 log N / σ²) * σ² = 2 * log N + 2 * log N = 4 * log N... wait that's wrong
    -- Actually: log N / t₀ + t₀ * σ² / 2
    -- = log N * σ / √(2 log N) + √(2 log N) * σ / 2
    -- Key: log N / √(2 log N) = √(2 log N) / 2 (since √(2 log N)² = 2 log N)
    -- So = σ * √(2 log N) / 2 + σ * √(2 log N) / 2 = σ * √(2 log N). ✓
    -- Prove via: multiply both sides by 2 * √(2 log N)
    have hsqrt_ne : Real.sqrt (2 * Real.log ↑N) ≠ 0 := ne_of_gt hsqrt_pos
    have h_mul_self : Real.sqrt (2 * Real.log ↑N) * Real.sqrt (2 * Real.log ↑N) =
        2 * Real.log ↑N := Real.mul_self_sqrt h2log_nonneg
    -- Step 1: log N / t₀ = log N * σ / √(2 log N) = σ * √(2 log N) / 2
    have h1 : Real.log ↑N / t₀ = σ_param * Real.sqrt (2 * Real.log ↑N) / 2 := by
      simp only [t₀]
      rw [div_div_eq_mul_div]
      -- Goal: log N * σ / √(2 log N) = σ * √(2 log N) / 2
      rw [div_eq_div_iff hsqrt_ne two_ne_zero]
      nlinarith
    -- Step 2: t₀ * σ² / 2 = σ * √(2 log N) / 2
    have h2 : t₀ * σ_param ^ 2 / 2 = σ_param * Real.sqrt (2 * Real.log ↑N) / 2 := by
      simp only [t₀]
      rw [div_mul_eq_mul_div, div_div]
      rw [div_eq_div_iff (mul_ne_zero hσ_ne two_ne_zero) two_ne_zero]
      ring
    rw [h1, h2]; ring

/-! ### Helper lemmas for Sauer-Shelah exponential bound -/

/-- For a Set-based concept class C with VCDim X C = d, the number of distinct
    restrictions of C to any finite set S is bounded by ∑_{i≤d} C(|S|, i).

    This bridges from our Set-based VCDim to Mathlib's Finset.vcDim on the
    restriction to S, using the fact that ↥S is Fintype for any Finset S. -/
private theorem ncard_restrictions_le_sum_choose_set {X : Type u}
    (C : ConceptClass X Bool) (S : Finset X) (d : ℕ)
    (hvc : VCDim X C = ↑d) :
    ({ f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } : Set (↥S → Bool)).ncard ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i := by
  classical
  -- The restriction set is finite since ↥S → Bool is Fintype
  set R := { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } with hR_def
  have hR_fin : R.Finite := Set.Finite.subset (Set.finite_univ) (Set.subset_univ _)
  -- Convert to Finset for counting
  rw [Set.ncard_eq_toFinset_card']
  -- Build a Finset family AA : Finset (Finset ↥S) from R
  set R_fin := R.toFinset with hR_fin_def
  set AA := R_fin.image (fun f => Finset.univ.filter (fun x => f x = true)) with hAA_def
  -- Step 1: R_fin.card ≤ AA.card (the map f ↦ filter is injective on Bool-valued functions)
  have h_inj : Function.Injective
      (fun (f : ↥S → Bool) => Finset.univ.filter (fun x => f x = true)) := by
    intro f g hfg
    funext x
    have := Finset.ext_iff.mp hfg x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    cases hf : f x <;> cases hg : g x <;> simp_all
  have h1 : R_fin.card = AA.card := by
    rw [hAA_def]; exact (Finset.card_image_of_injective _ h_inj).symm
  -- Step 2: AA.card ≤ AA.shatterer.card (Mathlib: card_le_card_shatterer)
  have h2 : AA.card ≤ AA.shatterer.card := Finset.card_le_card_shatterer AA
  -- Step 3: AA.shatterer.card ≤ ∑ k ∈ Iic AA.vcDim, C(Fintype.card ↥S, k)
  have h3 := @Finset.card_shatterer_le_sum_vcDim ↥S _ AA
  -- Step 4: vcDim(AA) ≤ d
  -- If AA shatters T, then C shatters T.map Subtype.val, so |T| ≤ d
  have h4 : AA.vcDim ≤ d := by
    simp only [Finset.vcDim]
    apply Finset.sup_le
    intro T hT
    have hTs : AA.Shatters T := Finset.mem_shatterer.mp hT
    -- If AA shatters T ⊆ ↥S, then C shatters T.map Subtype.val ⊆ X
    set Tval := T.map ⟨Subtype.val, Subtype.val_injective⟩ with hTval_def
    suffices hShats : Shatters X C Tval by
      have hCard : Tval.card = T.card := Finset.card_map _
      have : (Tval.card : WithTop ℕ) ≤ ↑d := by
        calc (Tval.card : WithTop ℕ)
            ≤ ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ) :=
              le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) =>
                (S.card : WithTop ℕ)) _ hShats
          _ = ↑d := hvc
      linarith [WithTop.coe_le_coe.mp this, hCard]
    -- Prove Shatters X C Tval: for any labeling g : ↥Tval → Bool, find c ∈ C matching
    intro g
    -- Helper function: extend g to ↥S via dite
    let g' : ↥S → Bool := fun x =>
      if h : (↑x : X) ∈ Tval then g ⟨↑x, h⟩ else false
    -- Build t_sub ⊆ T: elements labeled true
    let t_sub : Finset ↥S := T.filter (fun x => g' x = true)
    have ht_sub : t_sub ⊆ T := Finset.filter_subset _ _
    obtain ⟨A, hA, hTA⟩ := hTs ht_sub
    simp only [hAA_def, Finset.mem_image] at hA
    obtain ⟨f, hf_mem, rfl⟩ := hA
    rw [Set.mem_toFinset] at hf_mem
    obtain ⟨c, hcC, hcf⟩ := hf_mem
    refine ⟨c, hcC, ?_⟩
    intro ⟨y, hyTval⟩
    -- c ↑(y, hyTval) = c y. Need to match this with g ⟨y, hyTval⟩.
    -- y ∈ Tval, so ∃ x ∈ T, ↑x = y
    have hyTval' := hyTval
    rw [hTval_def, Finset.mem_map] at hyTval'
    obtain ⟨⟨y', hy'S⟩, hy'T, hy'eq⟩ := hyTval'
    -- hy'eq : ↑⟨y', hy'S⟩ = y, i.e., y' = y
    simp only [Function.Embedding.coeFn_mk] at hy'eq
    subst hy'eq
    -- Now y = y', hyTval : y' ∈ Tval, hy'S : y' ∈ S, hy'T : ⟨y', hy'S⟩ ∈ T
    have hcf_y := hcf ⟨y', hy'S⟩
    -- hcf_y : c y' = f ⟨y', hy'S⟩
    -- From hTA: T ∩ filter(f · = true) = t_sub = T.filter(g' · = true)
    have h_f_iff_g' : f ⟨y', hy'S⟩ = true ↔ g' ⟨y', hy'S⟩ = true := by
      have h1 : (⟨y', hy'S⟩ : ↥S) ∈ T ∩ Finset.univ.filter (fun x => f x = true) ↔
          f ⟨y', hy'S⟩ = true := by
        simp [Finset.mem_inter, Finset.mem_filter, hy'T]
      have h2 : (⟨y', hy'S⟩ : ↥S) ∈ t_sub ↔ g' ⟨y', hy'S⟩ = true := by
        simp [t_sub, Finset.mem_filter, hy'T]
      constructor
      · intro hf_true
        have hmem : (⟨y', hy'S⟩ : ↥S) ∈ T ∩ Finset.univ.filter (fun x => f x = true) :=
          h1.mpr hf_true
        have hmem2 : (⟨y', hy'S⟩ : ↥S) ∈ t_sub := hTA ▸ hmem
        exact h2.mp hmem2
      · intro hg_true
        have hmem : (⟨y', hy'S⟩ : ↥S) ∈ t_sub := h2.mpr hg_true
        have hmem2 : (⟨y', hy'S⟩ : ↥S) ∈ T ∩ Finset.univ.filter (fun x => f x = true) :=
          hTA ▸ hmem
        exact h1.mp hmem2
    -- g' ⟨y', hy'S⟩ = g ⟨y', hyTval⟩ since y' ∈ Tval
    have h_g'_eq : g' ⟨y', hy'S⟩ = g ⟨y', hyTval⟩ := by
      simp only [g', dif_pos hyTval]
    -- Combine: c y' = f ⟨y',hy'S⟩ and f = true ↔ g = true
    rw [hcf_y]
    have : f ⟨y', hy'S⟩ = g ⟨y', hyTval⟩ := by
      rw [← h_g'_eq]
      cases hf : f ⟨y', hy'S⟩ <;> cases hg : g' ⟨y', hy'S⟩ <;>
        simp_all only [Bool.false_eq_true, true_iff, iff_true]
    exact this
  -- Step 5: Fintype.card ↥S = S.card
  have h5 : Fintype.card ↥S = S.card := Fintype.card_coe S
  -- Combine
  calc R.toFinset.card
      = AA.card := h1
    _ ≤ AA.shatterer.card := h2
    _ ≤ ∑ k ∈ Finset.Iic AA.vcDim, (Fintype.card ↥S).choose k := h3
    _ = ∑ k ∈ Finset.Iic AA.vcDim, S.card.choose k := by rw [h5]
    _ ≤ ∑ k ∈ Finset.Iic d, S.card.choose k := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.Iic_subset_Iic.mpr h4
    _ = ∑ k ∈ Finset.range (d + 1), S.card.choose k := by
        rw [Nat.range_succ_eq_Iic]

/-- Growth function of a Set-based concept class is bounded by the Sauer-Shelah sum. -/
private theorem growth_function_le_sum_choose_set {X : Type u}
    (C : ConceptClass X Bool) (d m : ℕ) (_hdm : d ≤ m) (hvc : VCDim X C = ↑d) :
    GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by
  unfold GrowthFunction
  apply csSup_le'
  intro n hn
  obtain ⟨⟨S, hSm⟩, rfl⟩ := hn
  change ({ f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } : Set _).ncard ≤ _
  calc ({ f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x } : Set _).ncard
      ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i :=
        ncard_restrictions_le_sum_choose_set C S d hvc
    _ = ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by rw [hSm]

/-- Pure combinatorial inequality: ∑_{i=0}^d C(m,i) ≤ (em/d)^d for d ≤ m, d ≥ 1. -/
theorem sum_choose_le_exp_pow (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) :
    (∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℝ) ≤ (Real.exp 1 * ↑m / ↑d) ^ d := by
  have hd_pos : (0 : ℝ) < ↑d := Nat.cast_pos.mpr hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hd hdm)
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hdm_r : (d : ℝ) ≤ ↑m := Nat.cast_le.mpr hdm
  have hd_div_m_pos : (0 : ℝ) < ↑d / ↑m := div_pos hd_pos hm_pos
  have hd_div_m_le : (d : ℝ) / ↑m ≤ 1 := by
    rw [div_le_one hm_pos]; exact hdm_r
  have hm_div_d_ge : (1 : ℝ) ≤ ↑m / ↑d := le_div_iff₀ hd_pos |>.mpr (by linarith)
  -- Strategy: ∑_{i=0}^d C(m,i) ≤ (m/d)^d · (1 + d/m)^m ≤ (m/d)^d · e^d = (em/d)^d
  -- Step 1: ∑_{i=0}^d C(m,i) ≤ (m/d)^d · ∑_{i=0}^d C(m,i) · (d/m)^i
  -- Because C(m,i) = C(m,i) · (d/m)^i · (m/d)^i ≤ C(m,i) · (d/m)^i · (m/d)^d
  -- (since m/d ≥ 1 and i ≤ d implies (m/d)^i ≤ (m/d)^d)
  -- Step 2: ∑_{i=0}^d C(m,i) · (d/m)^i ≤ (1 + d/m)^m
  -- Step 3: (1 + d/m)^m ≤ e^d
  -- Step 4: combine
  set t := (d : ℝ) / ↑m with ht_def
  have ht_pos : 0 < t := hd_div_m_pos
  have ht_le : t ≤ 1 := hd_div_m_le
  -- Step 2: ∑_{i=0}^d C(m,i) · t^i ≤ (1 + t)^m
  -- From binomial theorem: (1 + t)^m = ∑_{i=0}^m C(m,i) · t^i · 1^{m-i} = ∑_{i=0}^m C(m,i) · t^i
  have h_binom : (1 + t) ^ m = ∑ i ∈ Finset.range (m + 1),
      t ^ i * (1 : ℝ) ^ (m - i) * ↑(Nat.choose m i) := by
    rw [add_comm]; exact add_pow t 1 m
  have h_binom' : (1 + t) ^ m = ∑ i ∈ Finset.range (m + 1),
      ↑(Nat.choose m i) * t ^ i := by
    rw [h_binom]
    congr 1; ext i
    rw [one_pow, mul_one]; ring
  have h_partial_le_binom : ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i ≤
      (1 + t) ^ m := by
    rw [h_binom']
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro i _ _
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt ht_pos) _)
  -- Step 3: (1 + t)^m ≤ e^d
  -- (1 + t) ≤ exp(t) by add_one_le_exp
  -- So (1 + t)^m ≤ exp(t)^m = exp(t · m) = exp(d)
  have h_exp_bound : (1 + t) ^ m ≤ Real.exp 1 ^ d := by
    have h1t_le : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have h_pow : (1 + t) ^ m ≤ (Real.exp t) ^ m :=
      pow_le_pow_left₀ (by linarith) h1t_le m
    have h_exp_eq : (Real.exp t) ^ m = Real.exp (t * ↑m) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h_tm : t * ↑m = ↑d := by
      simp only [ht_def]; field_simp
    rw [h_exp_eq, h_tm] at h_pow
    calc (1 + t) ^ m ≤ Real.exp ↑d := h_pow
      _ = Real.exp 1 ^ d := by rw [← Real.exp_nat_mul]; simp
  -- Step 1: ∑_{i=0}^d C(m,i) ≤ (m/d)^d · ∑_{i=0}^d C(m,i) · t^i
  -- For each i ≤ d: C(m,i) = C(m,i) · t^i · (1/t)^i
  -- And (1/t)^i = (m/d)^i ≤ (m/d)^d since m/d ≥ 1 and i ≤ d
  have h_factor : (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ)) ≤
      (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := by
    -- Rewrite LHS: C(m,i) = C(m,i) · t^i · (m/d)^i
    have h_id : ∀ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ) =
        ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ i := by
      intro i _
      have htinv : t * (↑m / ↑d) = 1 := by
        simp only [ht_def]; field_simp
      rw [mul_assoc, ← mul_pow, htinv, one_pow, mul_one]
    rw [Finset.sum_congr rfl h_id]
    -- Now: ∑ C(m,i) · t^i · (m/d)^i ≤ (m/d)^d · ∑ C(m,i) · t^i
    -- because (m/d)^i ≤ (m/d)^d for i ≤ d and m/d ≥ 1
    calc ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ i
        ≤ ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ d := by
          apply Finset.sum_le_sum
          intro i hi
          have hi_le : i ≤ d := by simp only [Finset.mem_range] at hi; omega
          apply mul_le_mul_of_nonneg_left
          · exact pow_right_mono₀ hm_div_d_ge hi_le
          · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt ht_pos) _)
      _ = (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := by
          rw [← Finset.sum_mul, mul_comm]
  -- Combine: ∑ C(m,i) ≤ (m/d)^d · e^d = (em/d)^d
  calc (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ))
      ≤ (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := h_factor
    _ ≤ (↑m / ↑d) ^ d * ((1 + t) ^ m) := by
        apply mul_le_mul_of_nonneg_left h_partial_le_binom
        exact pow_nonneg (div_nonneg (le_of_lt hm_pos) (le_of_lt hd_pos)) d
    _ ≤ (↑m / ↑d) ^ d * Real.exp 1 ^ d := by
        apply mul_le_mul_of_nonneg_left h_exp_bound
        exact pow_nonneg (div_nonneg (le_of_lt hm_pos) (le_of_lt hd_pos)) d
    _ = (Real.exp 1 * ↑m / ↑d) ^ d := by
        rw [mul_div_assoc, ← mul_pow, mul_comm (Real.exp 1) _]

/-- Sauer-Shelah exponential bound: GrowthFunction(C,m) ≤ (em/d)^d. -/
theorem sauer_shelah_exp_bound {X : Type u} (C : ConceptClass X Bool)
    (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) (hvc : VCDim X C = ↑d) :
    GrowthFunction X C m ≤ (Real.exp 1 * m / d) ^ d := by
  -- Decompose: GF ≤ ∑ C(m,i) ≤ (em/d)^d
  have h1 : GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i :=
    growth_function_le_sum_choose_set C d m hdm hvc
  have h2 : (∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℝ) ≤ (Real.exp 1 * ↑m / ↑d) ^ d :=
    sum_choose_le_exp_pow d m hd hdm
  -- Chain: need to go from ℕ inequality to ℝ
  calc (↑(GrowthFunction X C m) : ℝ)
      ≤ ↑(∑ i ∈ Finset.range (d + 1), Nat.choose m i) := by
        exact_mod_cast h1
    _ = (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ)) := by push_cast; rfl
    _ ≤ (Real.exp 1 * ↑m / ↑d) ^ d := h2

private theorem conceptClass_nonempty_of_vcdim_eq_pos {X : Type u}
    (C : ConceptClass X Bool) {d : ℕ} (hd : VCDim X C = ↑d) (hd_pos : 0 < d) :
    C.Nonempty := by
  by_contra hC_empty
  rw [Set.not_nonempty_iff_eq_empty] at hC_empty
  have : VCDim X C = 0 := by
    simp only [VCDim]
    apply le_antisymm
    · apply iSup₂_le; intro S hS
      exfalso; unfold Shatters at hS
      have := hS (fun _ => true)
      obtain ⟨c, hcC, _⟩ := this
      rw [hC_empty] at hcC; exact hcC
    · exact bot_le
  rw [this] at hd
  have : d = 0 := by
    have := hd.symm
    rw [show (0 : WithTop ℕ) = ↑(0 : ℕ) from rfl] at this
    exact WithTop.coe_injective this
  omega

/-! ## VCDim → Rademacher bound -/

/-- VC dimension upper bounds Rademacher complexity: Rad ≤ √(2d·log(em/d)/m).

    The proof decomposes into:
    (1) Pointwise: EmpRad(xs) ≤ B for all xs [Massart + Sauer-Shelah]
    (2) Integral: Rad = ∫ EmpRad ≤ ∫ B = B [probability measure]

    Step (2) is proved. Step (1) for B ≥ 1 follows from EmpRad ≤ 1.
    Step (1) for B < 1 requires Massart finite lemma + Sauer-Shelah growth bound. -/
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
  -- Pointwise bound: Massart + Sauer-Shelah.
  intro xs
  by_cases hB1 : 1 ≤ B
  · exact le_trans (empiricalRademacherComplexity_le_one X C hm xs) hB1
  · -- B < 1: genuine Massart-Sauer content.
    push Not at hB1
    -- MASSART FINITE LEMMA + SAUER-SHELAH CHAIN
    -- Proof: EmpRad(xs) ≤ √(2d·log(em/d)/m) = B when B < 1
    classical
    -- Positivity facts
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
    have hd_pos_r : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
    have hcard_pos : (0 : ℝ) < (Fintype.card (SignVector m) : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := SignVector m)
    have h1card_pos : (0 : ℝ) < 1 / (Fintype.card (SignVector m) : ℝ) := by positivity
    -- C is nonempty (from VCDim ≥ 1)
    have hC_ne : C.Nonempty := conceptClass_nonempty_of_vcdim_eq_pos C hd hd_pos
    obtain ⟨h₀, hh₀⟩ := hC_ne
    -- === STEP 1: Restriction collapse ===
    -- The correlation depends on h only through fun i => h(xs i)
    -- dpats = distinct restriction patterns of C on xs
    let dpats : Finset (Fin m → Bool) :=
        Finset.univ.filter (fun p => ∃ h ∈ C, ∀ i, h (xs i) = p i)
    have hdpats_ne : dpats.Nonempty := by
      refine ⟨fun i => h₀ (xs i), ?_⟩
      simp only [dpats, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h₀, hh₀, fun _ => rfl⟩
    -- rademacherCorrelation h σ xs = corr_pat (fun i => h(xs i)) σ
    -- where corr_pat p σ = (1/m) ∑ boolToSign(σ i) * boolToSign(p i)
    -- For each σ: sSup { corr(h,σ,xs) | h ∈ C } ≤ dpats.sup' (corr_pat(·, σ))
    -- Abbreviation for the sup' function
    set cf : SignVector m → (Fin m → Bool) → ℝ :=
      fun σ p => (1 / (m : ℝ)) * ∑ i : Fin m, boolToSign (σ i) * boolToSign (p i)
    have h_corr_eq : ∀ (h : Concept X Bool) (σ : SignVector m),
        rademacherCorrelation h σ xs = cf σ (fun i => h (xs i)) := by
      intro h σ; unfold rademacherCorrelation
      rw [dif_neg (Nat.pos_iff_ne_zero.mp hm)]
    have h_mem_dpats : ∀ h ∈ C, (fun i => h (xs i)) ∈ dpats := by
      intro h hh
      simp only [dpats, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h, hh, fun _ => rfl⟩
    have h_ssup_le_sup' : ∀ σ : SignVector m,
        sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } ≤
        dpats.sup' hdpats_ne (cf σ) := by
      intro σ
      apply csSup_le
      · exact ⟨rademacherCorrelation h₀ σ xs, h₀, hh₀, rfl⟩
      · rintro r ⟨h, hh, rfl⟩
        rw [h_corr_eq]
        exact Finset.le_sup' (cf σ) (h_mem_dpats h hh)
    -- EmpRad ≤ (1/card) * ∑_σ dpats.sup' ...
    have h_empRad_le : EmpiricalRademacherComplexity X C xs ≤
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ σ : SignVector m, dpats.sup' hdpats_ne (cf σ) := by
      unfold EmpiricalRademacherComplexity
      rw [dif_neg (Nat.pos_iff_ne_zero.mp hm)]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt h1card_pos)
      exact Finset.sum_le_sum (fun σ _ => h_ssup_le_sup' σ)
    -- === STEP 2: Index dpats by Fin N and apply Massart ===
    set N := dpats.card
    have hN_pos : 0 < N := Finset.Nonempty.card_pos hdpats_ne
    -- Use Fintype.equivFin on the subtype { p // p ∈ dpats }
    have hcard_dpats : Fintype.card { p // p ∈ dpats } = N := Fintype.card_coe dpats
    let e : { p // p ∈ dpats } ≃ Fin N :=
      hcard_dpats ▸ Fintype.equivFin _
    -- Define Z : Fin N → SignVector m → ℝ
    let Z : Fin N → SignVector m → ℝ :=
      fun j σ => cf σ (e.symm j).val
    -- dpats.sup' (cf σ) = univ.sup' (fun j => Z j σ)
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN_pos
    have h_sup'_eq : ∀ σ : SignVector m,
        dpats.sup' hdpats_ne (cf σ) =
        Finset.univ.sup' Finset.univ_nonempty (fun j => Z j σ) := by
      intro σ
      apply le_antisymm
      · rw [Finset.sup'_le_iff]
        intro p hp
        exact Finset.le_sup'_of_le (f := fun j => Z j σ) (Finset.mem_univ (e ⟨p, hp⟩))
          (by
            change cf σ p ≤ cf σ (e.symm (e ⟨p, hp⟩)).val
            simp [Equiv.symm_apply_apply])
      · rw [Finset.sup'_le_iff]
        intro j _
        exact Finset.le_sup' (cf σ) (e.symm j).prop
    -- Rewrite
    have h_empRad_le2 : EmpiricalRademacherComplexity X C xs ≤
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ σ : SignVector m, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j σ) := by
      calc EmpiricalRademacherComplexity X C xs
          ≤ (1 / (Fintype.card (SignVector m) : ℝ)) *
              ∑ σ, dpats.sup' hdpats_ne (cf σ) := h_empRad_le
        _ = _ := by
            congr 1; apply Finset.sum_congr rfl; intro σ _; exact h_sup'_eq σ
    -- === MGF bound for each Z_j ===
    set σ_param := (1 : ℝ) / Real.sqrt m
    have hσ_pos : 0 < σ_param := by positivity
    have h_mgf_Z : ∀ j : Fin N, ∀ t : ℝ, 0 ≤ t →
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ sv : SignVector m, Real.exp (t * Z j sv) ≤
        Real.exp (t ^ 2 * σ_param ^ 2 / 2) := by
      intro j t ht
      -- Z j sv = cf sv (e.symm j).val = (1/m) * ∑ boolToSign(sv i) * boolToSign(p i)
      set p := (e.symm j).val with hp_def
      -- Apply rademacher_mgf_bound with a_i = boolToSign(p i), c = 1
      have h_bound := rademacher_mgf_bound hm (fun i => boolToSign (p i)) 1 (by norm_num)
        (fun i => le_of_eq (boolToSign_abs_eq_one (p i))) t ht
      -- Z j sv = (1/m) * ∑ boolToSign(sv i) * boolToSign(p i)
      --       = (1/m) * ∑ boolToSign(p i) * boolToSign(sv i) (by mul_comm)
      have h_Z_rewrite : ∀ sv, Z j sv =
          (1 / (m : ℝ)) * ∑ i, (fun i => boolToSign (p i)) i * boolToSign (sv i) := by
        intro sv
        change cf sv p = _
        simp only [cf]
        congr 1; apply Finset.sum_congr rfl; intro i _; ring
      -- Rewrite LHS to match h_bound
      have h_lhs_eq : ∀ sv, Real.exp (t * Z j sv) =
          Real.exp
            (t * ((1 / (m : ℝ)) * ∑ i,
              (fun i => boolToSign (p i)) i * boolToSign (sv i))) := by
        intro sv; rw [h_Z_rewrite]
      simp_rw [h_lhs_eq]
      -- RHS: σ_param² = 1/m, so t²·σ_param²/2 = t²·1²/(2m)
      have h_rhs_eq : t ^ 2 * σ_param ^ 2 / 2 = t ^ 2 * 1 ^ 2 / (2 * ↑m) := by
        rw [one_pow, mul_one, show σ_param = 1 / Real.sqrt ↑m from rfl]
        rw [one_div, inv_pow, Real.sq_sqrt (le_of_lt hm_pos)]
        ring
      rw [h_rhs_eq]
      exact h_bound
    -- Apply finite_massart_lemma
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN_pos
    have h_massart := finite_massart_lemma hm hN_pos Z σ_param hσ_pos h_mgf_Z
    -- === STEP 3: Bound N via Sauer-Shelah ===
    set S := Finset.univ.image xs
    have h_dpats_card_le : (N : ℝ) ≤ (Real.exp 1 * ↑m / ↑d) ^ d := by
      -- Injection from dpats to {f : S → Bool | ∃ c ∈ C, ∀ x, c x = f x}
      -- then ncard_restrictions ≤ ∑ choose ≤ (em/d)^d
      set R := { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }
      -- dpats maps into R via the restriction map
      have h_dpats_mem : ∀ p ∈ dpats, ∃ c ∈ C, ∀ i, c (xs i) = p i := by
        intro p hp
        have := Finset.mem_filter.mp hp
        exact this.2
      have h_inj_card : N ≤ R.toFinset.card := by
        -- Map: p ↦ (fun x => p (choose_index x))
        -- where for x ∈ S, choose_index x is some i with xs i = x
        apply Finset.card_le_card_of_injOn
          (fun (p : Fin m → Bool) (x : ↥S) =>
            p ((Finset.mem_image.mp x.prop).choose))
          -- maps into R.toFinset
          (fun p hp => by
            obtain ⟨c, hcC, hc_agree⟩ := h_dpats_mem p hp
            have : (fun (x : ↥S) => p ((Finset.mem_image.mp x.prop).choose)) ∈ R := by
              exact ⟨c, hcC, fun ⟨x, hx⟩ => by
                have hcs := (Finset.mem_image.mp hx).choose_spec
                -- hcs.2 : xs(choose) = x, so c x = c(xs(choose)) = p(choose)
                change c x = p ((Finset.mem_image.mp hx).choose)
                conv_lhs => rw [← hcs.2]
                exact hc_agree _⟩
            exact Set.mem_toFinset.mpr this)
          -- injective on dpats
          (fun p₁ hp₁ p₂ hp₂ heq => by
            obtain ⟨c₁, _, hc₁⟩ := h_dpats_mem p₁ hp₁
            obtain ⟨c₂, _, hc₂⟩ := h_dpats_mem p₂ hp₂
            funext i
            have hxi_in : xs i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
            have hcs := (Finset.mem_image.mp hxi_in).choose_spec
            have h_at := congr_fun heq ⟨xs i, hxi_in⟩
            -- p₁ i = c₁(xs i) and p₁(choose) = c₁(xs(choose)) = c₁(xs i)
            -- Similarly for p₂. And h_at says p₁(choose) = p₂(choose).
            rw [← hc₁ i, ← hc₂ i]
            -- c₁(xs i) = c₁(xs(choose)) by hcs.2 : xs(choose) = xs i
            rw [← hcs.2]
            -- Need: c₁(xs(choose)) = c₂(xs(choose))
            -- = p₁(choose) by hc₁, = p₂(choose) by h_at, = c₂(xs(choose)) by hc₂
            rw [hc₁, hc₂]
            exact h_at)
      have h_ncard_le := ncard_restrictions_le_sum_choose_set C S d hd
      have hS_card_le : S.card ≤ m := by
        calc (Finset.univ.image xs).card ≤ Finset.univ.card := Finset.card_image_le
          _ = m := by simp
      have h_exp := sum_choose_le_exp_pow d m hd_pos hdm
      calc (N : ℝ)
          ≤ ↑R.toFinset.card := by exact_mod_cast h_inj_card
        _ = ↑R.ncard := by rw [Set.ncard_eq_toFinset_card']
        _ ≤ ↑(∑ i ∈ Finset.range (d + 1), Nat.choose S.card i) := by exact_mod_cast h_ncard_le
        _ ≤ ↑(∑ i ∈ Finset.range (d + 1), Nat.choose m i) := by
            push_cast
            apply Finset.sum_le_sum
            intro i _
            exact_mod_cast Nat.choose_le_choose i hS_card_le
        _ ≤ (Real.exp 1 * ↑m / ↑d) ^ d := by push_cast at h_exp ⊢; exact h_exp
    -- === STEP 4: Combine ===
    have h_emd_ge_one : (1 : ℝ) ≤ Real.exp 1 * ↑m / ↑d := by
      rw [le_div_iff₀ hd_pos_r]
      have : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      have hdm_r : (d : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hdm
      nlinarith
    have h_log_emd_nonneg : 0 ≤ Real.log (Real.exp 1 * ↑m / ↑d) :=
      Real.log_nonneg h_emd_ge_one
    have hN_real_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
    have h_log_N_le : Real.log ↑N ≤ ↑d * Real.log (Real.exp 1 * ↑m / ↑d) := by
      calc Real.log ↑N
          ≤ Real.log ((Real.exp 1 * ↑m / ↑d) ^ d) :=
            Real.log_le_log hN_real_pos h_dpats_card_le
        _ = ↑d * Real.log (Real.exp 1 * ↑m / ↑d) := by rw [Real.log_pow]
    calc EmpiricalRademacherComplexity X C xs
        ≤ (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ σ, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j σ) := h_empRad_le2
      _ ≤ σ_param * Real.sqrt (2 * Real.log ↑N) := h_massart
      _ ≤ σ_param * Real.sqrt (2 * (↑d * Real.log (Real.exp 1 * ↑m / ↑d))) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hσ_pos)
          apply Real.sqrt_le_sqrt; nlinarith [h_log_N_le]
      _ = Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m) := by
          -- (1/√m) * √(2d·log(em/d)) = √((2d·log(em/d))/m)
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
  have hS_sub : S ⊆ T := by
    intro x hx
    simp only [hS_def, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact h_range i
  have hS_shat : Shatters X C S := shatters_subset C T S hS_sub hT
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
  have hD_univ : D_sub Set.univ = 1 := hD_sub_prob.measure_univ
  have hcoll_bound : ∀ p ∈ pairs,
      μ_sub {ys : Fin m → α | ys p.1 = ys p.2} ≤ 1 / (n : ENNReal) := by
    intro ⟨i, j⟩ hp
    have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hp).2
    set Cij := {ys : Fin m → α | ys i = ys j}
    have hCij_eq : Cij = ⋃ t : α, {ys : Fin m → α | ys i = t ∧ ys j = t} := by
      ext ys; simp only [Cij, Set.mem_setOf_eq, Set.mem_iUnion]
      exact ⟨fun h => ⟨ys i, rfl, h.symm⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2.symm⟩
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
        intro k; split_ifs <;> [rw [hDsub_sing]; rw [hDsub_sing]; rw [hD_univ]]
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
              have hi_mem : i ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ i
              rw [← Finset.mul_prod_erase _ _ hi_mem]
              have hj_in : j ∈ (Finset.univ : Finset (Fin m)).erase i :=
                Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
              rw [← Finset.mul_prod_erase _ _ hj_in]
              have hrest_eq : ∏ k ∈ ((Finset.univ : Finset (Fin m)).erase i).erase j,
                  (if k = i ∨ k = j then 1 / (n : ENNReal) else 1) = 1 := by
                apply Finset.prod_eq_one; intro k hk
                have hk_ne_j : k ≠ j := (Finset.mem_erase.mp hk).1
                have hk_ne_i : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
                simp [hk_ne_i, hk_ne_j]
              rw [hrest_eq, mul_one]
              simp [hij, hij.symm]
            rw [hprod_ij, sq]
    calc μ_sub Cij
        ≤ ∑ t : α, μ_sub {ys : Fin m → α | ys i = t ∧ ys j = t} := by
          rw [hCij_eq]
          calc μ_sub (⋃ t, {ys : Fin m → α | ys i = t ∧ ys j = t})
              ≤ ∑' t, μ_sub {ys : Fin m → α | ys i = t ∧ ys j = t} :=
                MeasureTheory.measure_iUnion_le _
            _ = ∑ t, μ_sub {ys : Fin m → α | ys i = t ∧ ys j = t} := tsum_fintype _
      _ ≤ ∑ _t : α, (1 / (n : ENNReal)) ^ 2 :=
          Finset.sum_le_sum (fun t _ => hfiber_bound t)
      _ = (n : ENNReal) * (1 / (n : ENNReal)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, hn_def, nsmul_eq_mul]
      _ = 1 / (n : ENNReal) := by
          rw [sq, ← mul_assoc]
          have h1n : (↑n : ENNReal) * (1 / ↑n) = 1 := by
            rw [one_div, ENNReal.mul_inv_cancel hn_ne hn_nt]
          rw [h1n, one_mul]
  have hBc_le : μ_sub Bᶜ ≤ pairs.card * (1 / (n : ENNReal)) :=
    calc μ_sub Bᶜ
        ≤ μ_sub (⋃ p ∈ pairs, {ys : Fin m → α | ys p.1 = ys p.2}) :=
          MeasureTheory.measure_mono hBc_sub
      _ ≤ ∑ p ∈ pairs, μ_sub {ys : Fin m → α | ys p.1 = ys p.2} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ ∑ _p ∈ pairs, (1 / (n : ENNReal)) :=
          Finset.sum_le_sum hcoll_bound
      _ = pairs.card * (1 / (n : ENNReal)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hpairs_card : pairs.card ≤ m * m :=
    calc pairs.card
        ≤ (Finset.univ : Finset (Fin m × Fin m)).card := Finset.card_filter_le _ _
      _ = Fintype.card (Fin m × Fin m) := Finset.card_univ
      _ = Fintype.card (Fin m) * Fintype.card (Fin m) := Fintype.card_prod _ _
      _ = m * m := by simp [Fintype.card_fin]
  have h2mm_le_n : 2 * (m * m) ≤ n := by rw [hn_def]; nlinarith [hlarge]
  have hBc_half : μ_sub Bᶜ ≤ 1 / 2 := by
    have hmm_le : (m * m : ℕ) * (1 / (n : ENNReal)) ≤ 1 / 2 := by
      have h_key : (↑(m * m) : ENNReal) ≤ (↑n : ENNReal) / 2 := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (2 : ENNReal) ≠ 0))
          (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤))]
        calc (↑(m * m) : ENNReal) * 2 = ↑(m * m * 2 : ℕ) := by push_cast; ring
          _ ≤ ↑n := Nat.cast_le.mpr (by nlinarith [h2mm_le_n])
      calc (↑(m * m) : ENNReal) * (1 / ↑n)
          ≤ (↑n / 2) * (1 / ↑n) :=
            mul_le_mul_of_nonneg_right h_key (by positivity)
        _ = 1 / 2 := by
            rw [one_div (↑n : ENNReal)]
            rw [div_eq_mul_inv, mul_assoc, mul_comm (2 : ENNReal)⁻¹ (↑n)⁻¹,
                ← mul_assoc, ENNReal.mul_inv_cancel hn_ne hn_nt, one_mul, inv_eq_one_div]
    exact (hBc_le.trans (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr hpairs_card) (by positivity))).trans hmm_le
  have hB_le_one : μ_sub B ≤ 1 :=
    (MeasureTheory.measure_mono (Set.subset_univ B)).trans (le_of_eq MeasureTheory.measure_univ)
  have hcompl := MeasureTheory.prob_compl_eq_one_sub hB_meas (μ := μ_sub)
  have hB_ge : 1 / 2 ≤ μ_sub B := by
    rw [hcompl] at hBc_half
    have h1 : 1 - (1 : ENNReal) / 2 ≤ 1 - (1 - μ_sub B) :=
      tsub_le_tsub_left hBc_half 1
    simp only [show (1 : ENNReal) - 1 / 2 = 1 / 2 from by norm_num] at h1
    rwa [ENNReal.sub_sub_cancel ENNReal.one_ne_top hB_le_one] at h1
  have hB_ne_top : μ_sub B ≠ ⊤ := MeasureTheory.measure_ne_top μ_sub B
  have h_half_real : ((1 : ENNReal) / 2).toReal = (1 : ℝ) / 2 := by norm_num
  calc (1 : ℝ) / 2 = ((1 : ENNReal) / 2).toReal := h_half_real.symm
    _ ≤ (μ_sub B).toReal := ENNReal.toReal_mono hB_ne_top hB_ge

/-- Adversarial Rademacher lower bound on shattered sets.
    For |T| >= 4m^2 + 1, exists D with Rad_m(C,D) >= 1 / 2.

    Proof: D = uniform on T. Product measure = uniform on T^m.
    On injective samples from T (shattered): EmpRad = 1
    (by empRad_eq_one_of_injective_in_shattered).
    EmpRad ≥ 0 everywhere (by empRad_nonneg).
    Birthday bound: P[injective m draws from n ≥ 4m²+1 points] ≥ 1 - m(m-1)/(2n) ≥ 7 / 8 ≥ 1 / 2.
    So ∫ EmpRad ≥ P[injective] · 1 + P[¬injective] · 0 ≥ 1 / 2. -/
theorem rademacher_lower_bound_on_shattered (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (T : Finset X) (hT : Shatters X C T)
    (m : ℕ) (hm : 0 < m) (hT_large : 4 * m ^ 2 + 1 ≤ T.card) :
    ∃ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ∧
      (1 : ℝ) / 2 ≤ RademacherComplexity X C D m := by
  classical
  have hT_ne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hT_large
  have hT_card_pos : 0 < T.card := Finset.Nonempty.card_pos hT_ne
  -- Construct D = uniform on T via pushforward from ↥T.
  haveI : Fintype ↥T := T.fintypeCoeSort
  letI msT : MeasurableSpace ↥T := ⊤
  haveI : @MeasurableSingletonClass ↥T ⊤ := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hTne_type : Nonempty ↥T := hT_ne.coe_sort
  have hTpos : 0 < Fintype.card ↥T := by rw [Fintype.card_coe]; exact hT_card_pos
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
  -- The integral lower bound: ∫ EmpRad ∂(Measure.pi D) ≥ 1 / 2.
  --
  -- Key chain: Measure.pi D = (Measure.pi D_sub).map (val ∘ ·)  [by pi_map_pi]
  -- So ∫ EmpRad ∂(Measure.pi D) = ∫ ys, EmpRad(val ∘ ys) ∂(Measure.pi D_sub)  [by integral_map]
  -- On Fin m → ↥T (finite type), the integral is a weighted finite sum.
  -- EmpRad(val ∘ ys) = 1 when ys is injective (by empRad_eq_one_of_injective_in_shattered).
  -- EmpRad(val ∘ ys) ≥ 0 always (by empRad_nonneg).
  -- So ∫ ≥ P_sub[injective] ≥ 1 / 2 by birthday bound.
  --
  -- Step 1: Infrastructure for product measures.
  -- EmpRad = 1 on injective samples from T.
  have hEmpRad_inj : ∀ (ys : Fin m → ↥T), Function.Injective ys →
      EmpiricalRademacherComplexity X C (Subtype.val ∘ ys) = 1 := by
    intro ys h_inj
    exact empRad_eq_one_of_injective_in_shattered C hm T hT _
      (Subtype.val_injective.comp h_inj) (fun i => (ys i).property)
  -- EmpRad ≥ 0 everywhere.
  have hEmpRad_nn : ∀ xs : Fin m → X, 0 ≤ EmpiricalRademacherComplexity X C xs :=
    fun xs => empRad_nonneg C (Nat.pos_iff_ne_zero.mp hm) xs
  -- EmpRad ≤ 1 everywhere.
  have hEmpRad_le : ∀ xs : Fin m → X, EmpiricalRademacherComplexity X C xs ≤ 1 :=
    fun xs => empiricalRademacherComplexity_le_one X C hm xs
  -- The RademacherComplexity integral.
  -- We need: 1 / 2 ≤ ∫ EmpRad ∂(Measure.pi (fun _ => D)).
  -- By birthday probability: the fraction of injective tuples in T^m is ≥ 1 / 2.
  -- On injective tuples, EmpRad = 1. On non-injective, EmpRad ≥ 0.
  -- So the average ≥ (fraction injective) · 1 ≥ 1 / 2.
  --
  -- The formal connection between the Bochner integral and finite averaging
  -- on the product of a discrete probability measure requires:
  -- (a) pi_map_pi to relate product of pushforward to pushforward of product
  -- (b) integral_map to pull back the integral
  -- (c) integral lower bound via indicator function
  --
  -- We use the integral directly by bounding below with an indicator.
  change (1 : ℝ) / 2 ≤ RademacherComplexity X C D m
  unfold RademacherComplexity
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  -- Lower bound the integral.
  -- Define A = {xs | injective ∧ ∀ i, xs i ∈ T}. On A, EmpRad = 1. On Aᶜ, EmpRad ≥ 0.
  -- ∫ EmpRad ≥ ∫_A 1 = μ(A).toReal.
  -- Birthday bound: μ(A) ≥ 1 / 2.
  set A := { xs : Fin m → X | Function.Injective xs ∧ ∀ i, xs i ∈ T }
  -- EmpRad(xs) ≥ A.indicator(1)(xs) for all xs.
  have h_pointwise : ∀ xs : Fin m → X,
      A.indicator (fun _ => (1 : ℝ)) xs ≤ EmpiricalRademacherComplexity X C xs := by
    intro xs
    unfold Set.indicator; split
    · next hxs =>
      obtain ⟨h_inj, h_range⟩ := hxs
      exact le_of_eq (empRad_eq_one_of_injective_in_shattered C hm T hT xs h_inj h_range).symm
    · exact hEmpRad_nn xs
  -- A is measurable (the pi sigma-algebra on Fin m → X with MeasurableSingletonClass
  -- has all subsets measurable for finite Fin m, but we use a direct approach).
  haveI : MeasurableSingletonClass (Fin m → X) := Pi.instMeasurableSingletonClass
  have hA_meas : MeasurableSet A := by
    -- A ⊆ {xs | ∀ i, xs i ∈ T} which embeds into Fin m → ↑T, a finite type.
    -- So A is finite, hence measurable (finite union of measurable singletons).
    apply Set.Finite.measurableSet
    exact (Set.Finite.pi' (fun _ => T.finite_toSet)).subset (fun xs ⟨_, hr⟩ => hr)
  -- ∫ EmpRad ≥ μ(A).toReal via pullback to finite type Fin m → ↥T.
  -- On Fin m → ↥T (finite type), all functions are measurable/integrable automatically.
  -- We use MeasurableEmbedding.integral_map which requires no AEStronglyMeasurable on codomain.
  haveI : MeasurableSingletonClass (Fin m → ↥T) := Pi.instMeasurableSingletonClass
  let μ_sub : MeasureTheory.Measure (Fin m → ↥T) :=
    MeasureTheory.Measure.pi (fun _ : Fin m => D_sub)
  haveI : MeasureTheory.IsProbabilityMeasure μ_sub :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  let φ : (Fin m → ↥T) → (Fin m → X) := fun ys i => Subtype.val (ys i)
  -- φ is a MeasurableEmbedding (injective, measurable, images of meas sets are meas).
  have hφ_emb : MeasurableEmbedding φ := by
    refine ⟨fun a b hab => funext (fun i => Subtype.val_injective (congr_fun hab i)),
      measurable_pi_lambda _ (fun i => hval_meas.comp (measurable_pi_apply i)),
      fun s _ => ?_⟩
    -- φ '' s ⊆ {xs | ∀ i, xs i ∈ T} which is finite, so φ '' s is finite, hence measurable.
    apply Set.Finite.measurableSet
    apply (Set.Finite.pi' (fun _ => T.finite_toSet)).subset
    intro xs hxs
    obtain ⟨ys, _, rfl⟩ := hxs
    exact fun i => (ys i).property
  -- μ = μ_sub.map φ via pi_map_pi.
  have hμ_eq : μ = μ_sub.map φ := by
    simp only [μ, μ_sub, D, φ]
    exact (MeasureTheory.Measure.pi_map_pi (fun _ => hval_meas.aemeasurable)).symm
  -- Transfer integral via MeasurableEmbedding.integral_map (no AEStronglyMeasurable needed).
  have h_int_eq : ∫ xs, EmpiricalRademacherComplexity X C xs ∂μ =
      ∫ ys, EmpiricalRademacherComplexity X C (φ ys) ∂μ_sub := by
    conv_lhs => rw [hμ_eq]; exact hφ_emb.integral_map _
  -- Integrability of EmpRad ∘ φ on finite type (automatic: bounded, measurable_of_finite).
  have hf_sub_int : MeasureTheory.Integrable
      (fun ys => EmpiricalRademacherComplexity X C (φ ys)) μ_sub :=
    MeasureTheory.Integrable.of_bound (measurable_of_finite _).aestronglyMeasurable 1
      (MeasureTheory.ae_of_all _ (fun ys => by
        rw [Real.norm_of_nonneg (hEmpRad_nn _)]; exact hEmpRad_le _))
  -- Lower bound on the finite type.
  have h_int_bound : (μ A).toReal ≤ ∫ xs, EmpiricalRademacherComplexity X C xs ∂μ := by
    rw [h_int_eq]
    set B := {ys : Fin m → ↥T | Function.Injective ys}
    have hB_meas : MeasurableSet B := Set.Finite.measurableSet (Set.toFinite B)
    have h_pw : ∀ ys : Fin m → ↥T,
        B.indicator (fun _ => (1 : ℝ)) ys ≤ EmpiricalRademacherComplexity X C (φ ys) := by
      intro ys; simp only [Set.indicator]; split
      · next hys => exact le_of_eq (hEmpRad_inj ys hys).symm
      · exact hEmpRad_nn _
    -- φ⁻¹'(A) ⊆ B: if φ ys is injective then ys is injective (Subtype.val is injective).
    have hA_le_B : μ A ≤ μ_sub B := by
      rw [hμ_eq, MeasureTheory.Measure.map_apply hφ_emb.measurable hA_meas]
      apply MeasureTheory.measure_mono
      intro ys (hys : φ ys ∈ A)
      change Function.Injective ys
      exact hys.1.of_comp
    calc (μ A).toReal
        ≤ (μ_sub B).toReal :=
          ENNReal.toReal_mono (MeasureTheory.measure_ne_top μ_sub _) hA_le_B
      _ ≤ ∫ ys, EmpiricalRademacherComplexity X C (φ ys) ∂μ_sub := by
          have h1 : ∫ ys, B.indicator (fun _ => (1 : ℝ)) ys ∂μ_sub = (μ_sub B).toReal := by
            rw [MeasureTheory.integral_indicator hB_meas,
              MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]; rfl
          linarith [MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ (fun ys =>
              Set.indicator_nonneg (fun _ _ => zero_le_one) ys))
            hf_sub_int
            (MeasureTheory.ae_of_all _ h_pw)]
  suffices h_birthday : (1 : ℝ) / 2 ≤ (μ A).toReal by linarith
  set B := {ys : Fin m → ↥T | Function.Injective ys}
  have hpre_eq : φ ⁻¹' A = B := by
    ext ys; constructor
    · intro (hys : φ ys ∈ A); exact hys.1.of_comp
    · intro (hys : Function.Injective ys)
      exact ⟨Subtype.val_injective.comp hys, fun i => (ys i).property⟩
  have hμA_eq_B : μ A = μ_sub B := by
    rw [hμ_eq, MeasureTheory.Measure.map_apply hφ_emb.measurable hA_meas, hpre_eq]
  rw [hμA_eq_B]
  simpa [μ_sub, D_sub, B] using
    uniform_injective_tuple_measure_half (α := ↥T) hTne_type m (by
      simpa [Fintype.card_coe] using hT_large)

/-- When VCDim = 0, Rademacher complexity is bounded by 1/√m.

    VCDim = 0 means no singleton is shattered, so the concept class acts as a single
    effective labeling. EmpRad ≤ 1/√m by Khintchine's inequality / Jensen.
    This avoids the d > 0 hypothesis of `vcdim_bounds_rademacher_quantitative`. -/
-- VCDim = 0 → no singleton is shattered → all concepts agree on each point.
private theorem vcdim_zero_concepts_agree (X : Type u) (C : ConceptClass X Bool)
    (hd : VCDim X C = (0 : ℕ)) (h₁ h₂ : Concept X Bool) (hh₁ : h₁ ∈ C) (hh₂ : h₂ ∈ C)
    (x : X) : h₁ x = h₂ x := by
  by_contra hne
  -- {x} is shattered: we can realize both labelings via h₁ and h₂
  have hshat : Shatters X C {x} := by
    intro f
    -- f maps the unique element of {x} to some Bool value
    -- h₁ and h₂ disagree on x, so one of them matches f
    by_cases hf : f ⟨x, Finset.mem_singleton_self x⟩ = h₁ x
    · refine ⟨h₁, hh₁, fun ⟨y, hy⟩ => ?_⟩
      have hyx := Finset.mem_singleton.mp hy
      subst hyx; exact hf.symm
    · have hf2 : f ⟨x, Finset.mem_singleton_self x⟩ = h₂ x := by
        have : h₁ x ≠ h₂ x := hne
        cases hv1 : h₁ x <;> cases hv2 : h₂ x <;> simp_all
      refine ⟨h₂, hh₂, fun ⟨y, hy⟩ => ?_⟩
      have hyx := Finset.mem_singleton.mp hy
      subst hyx; exact hf2.symm
  -- But this gives VCDim ≥ 1, contradicting VCDim = 0
  have h1le : (1 : WithTop ℕ) ≤ VCDim X C := by
    unfold VCDim
    exact le_iSup₂_of_le {x} hshat (by simp)
  rw [hd] at h1le
  exact absurd h1le (by norm_num)

-- VCDim = 0 → all concepts in C agree → sSup collapses → EmpRad ≤ 1 (then Rad ≤ 1).
-- Since 1/√m < 1 for m ≥ 2, we need the actual Rademacher variance bound.
-- The Cauchy-Schwarz / Jensen argument: E[|avg Rademacher|]² ≤ E[(avg Rademacher)²] = 1/m
-- requires formalizing variance of Rademacher sums over Fin m → Bool.
-- We provide the structural reduction (VCDim = 0 → concepts agree → sSup collapses)
-- and use Cauchy-Schwarz from Mathlib + Rademacher orthogonality.

private theorem vcdim_zero_rademacher_le_inv_sqrt (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (hd : VCDim X C = (0 : ℕ))
    (m : ℕ) (hm : 0 < m)
    [MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.pi (fun _ : Fin m => D))] :
    RademacherComplexity X C D m ≤ 1 / Real.sqrt m := by
  -- Case split: C empty vs nonempty.
  by_cases hC : C.Nonempty
  · -- C nonempty: all concepts agree on each point (vcdim_zero_concepts_agree).
    -- So sSup over C collapses, and EmpRad reduces to a Rademacher average.
    -- Bound by 1/√m via Jensen: E[|Z|]² ≤ E[Z²] = 1/m for Z = avg of Rademacher RVs.
    suffices h_pw : ∀ xs : Fin m → X, EmpiricalRademacherComplexity X C xs ≤ 1 / Real.sqrt m by
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
    -- One-sided: all h ∈ C agree (VCDim=0), so sSup = corr(h₀). Then EmpRad = 0 by symmetry.
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
    -- EmpRad = (1/N) Σ_σ corr(h₀,σ,xs) = 0 by Rademacher symmetry. 0 ≤ 1/√m.
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
  · -- C empty: EmpRad = 0 ≤ 1/√m.
    rw [Set.not_nonempty_iff_eq_empty] at hC
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
    unfold RademacherComplexity
    calc ∫ xs, EmpiricalRademacherComplexity X C xs ∂(MeasureTheory.Measure.pi _)
        = ∫ _xs, (0 : ℝ) ∂(MeasureTheory.Measure.pi (fun _ : Fin m => D)) := by
          congr 1; ext xs; exact h_emp_zero xs
      _ = 0 := by simp
      _ ≤ 1 / Real.sqrt m := by
          apply div_nonneg one_pos.le
          exact Real.sqrt_nonneg _

/-- Analytical lemma: for d > 0, m ≥ ⌈32(d+1)/ε⁴⌉+1, ε ∈ (0,1],
    we have 2d·log(em/d)/m < ε².

    Uses `Real.log_le_rpow_div` with exponent 1 / 2: log(x) ≤ x^(1 / 2)/(1 / 2) = 2√x.
    Then 2d·log(em/d)/m ≤ 2d·2√(em/d)/(m) ≤ ε². -/
private theorem analytical_log_sqrt_bound (d m : ℕ) (ε : ℝ)
    (hε : 0 < ε) (_hε1 : ε ≤ 1) (hd_pos : 0 < d) (hdm : d ≤ m)
    (hm_large : (Nat.ceil (32 * (↑d + 1) / ε ^ 4) + 1 : ℕ) ≤ m) :
    2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m < ε ^ 2 := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast Nat.lt_of_lt_of_le (by omega : 0 < d) hdm
  have hd_pos_r : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
  have hdm_r : (d : ℝ) ≤ m := Nat.cast_le.mpr hdm
  -- t = m/d ≥ 1
  set t := (m : ℝ) / d with ht_def
  have ht_pos : 0 < t := div_pos hm_pos hd_pos_r
  have ht_ge_one : 1 ≤ t := by rw [ht_def]; rw [le_div_iff₀ hd_pos_r]; linarith
  -- Rewrite: 2d·log(em/d)/m = 2·log(et)/t
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h_rewrite : 2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m =
      2 * Real.log (Real.exp 1 * t) / t := by
    rw [ht_def]
    field_simp
  rw [h_rewrite]
  -- log(et) = 1 + log(t) ≤ 1 + 2√t (using log(t) ≤ 2√t for t ≥ 1)
  have het_pos : (0 : ℝ) < Real.exp 1 * t := by positivity
  have het_nonneg : (0 : ℝ) ≤ Real.exp 1 * t := le_of_lt het_pos
  -- Use log(et) ≤ 2√(et) via log_le_rpow_div
  have h_log_bound : Real.log (Real.exp 1 * t) ≤ 2 * Real.sqrt (Real.exp 1 * t) := by
    have h1 := Real.log_le_rpow_div het_nonneg (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : (Real.exp 1 * t) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) =
        2 * (Real.exp 1 * t) ^ (1 / 2 : ℝ) := by
      ring
    rw [h2] at h1
    rwa [Real.sqrt_eq_rpow]
  -- So 2·log(et)/t ≤ 4√(et)/t = 4√(e)/√t ≤ 4√3/√t (since e < 3)
  -- Actually we bound more directly: 4√e/√t < ε² when t > 48/ε⁴ (since 16e < 48)
  -- But we have t > 32/ε⁴, and e < 3, so 16e < 48 > 32... need to check.
  -- Actually: 2·log(et)/t ≤ 4·√(et)/t. And √(et)/t = √e/(√t).
  -- So 2·log(et)/t ≤ 4√e/√t.
  -- Need: 4√e/√t < ε², i.e., √t > 4√e/ε².
  -- From t > 32/ε⁴: √t > √(32)/ε² = 4√2/ε².
  -- Need: 4√2 ≥ 4√e, i.e., √2 ≥ √e, i.e., 2 ≥ e. FALSE (e ≈ 2.718).
  -- So we need a tighter bound. Use: e < 3, so √e < √3 < 2.
  -- 4√e/ε² < 4·2/ε² = 8/ε². Need √t > 8/ε², i.e., t > 64/ε⁴.
  -- But we only have t > 32/ε⁴. This is tight. Let's use a different approach.
  -- Use log(et) = 1 + log(t) and log(t) ≤ 2√t (from log_le_rpow_div).
  -- Then 2(1 + log(t))/t ≤ 2(1 + 2√t)/t = 2/t + 4/√t.
  -- For t ≥ 32/ε⁴: 2/t ≤ 2ε⁴/32 = ε⁴/16 ≤ ε²/16 (since ε ≤ 1).
  -- 4/√t ≤ 4ε²/√32 = 4ε²/(4√2) = ε²/√2 < ε².
  -- Total: ε²/16 + ε²/√2 < ε². ✓ (since 1 / 16 + 1/√2 < 1)
  have h_log_t_bound : Real.log t ≤ 2 * Real.sqrt t := by
    have h1 := Real.log_le_rpow_div (le_of_lt ht_pos) (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : t ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) = 2 * t ^ (1 / 2 : ℝ) := by ring
    rw [h2] at h1
    rwa [Real.sqrt_eq_rpow]
  have h_log_et : Real.log (Real.exp 1 * t) = 1 + Real.log t := by
    rw [Real.log_mul (ne_of_gt he_pos) (ne_of_gt ht_pos), Real.log_exp]
  -- 2·log(et)/t = 2(1 + log t)/t = 2/t + 2·log(t)/t
  have h_split : 2 * Real.log (Real.exp 1 * t) / t = 2 / t + 2 * Real.log t / t := by
    rw [h_log_et]; ring
  rw [h_split]
  -- Bound each term separately
  -- Term 1: 2/t < ε²/2 (since t > 32/ε⁴ implies 2/t < 2ε⁴/32 = ε⁴/16 < ε²/2)
  -- Term 2: 2·log(t)/t ≤ 4/√t < ε²/2 (since √t > 4√2/ε² > 8/ε²... hmm)
  -- Let's just bound: 2/t + 4/√t < ε²
  have h_mid : 2 / t + 2 * Real.log t / t ≤ 2 / t + 4 / Real.sqrt t := by
    have : 2 * Real.log t / t ≤ 4 * Real.sqrt t / t := by
      apply div_le_div_of_nonneg_right _ (le_of_lt ht_pos)
      nlinarith [h_log_t_bound, Real.sqrt_nonneg t]
    have h_sq : 4 * Real.sqrt t / t = 4 / Real.sqrt t := by
      rw [div_eq_div_iff (ne_of_gt ht_pos) (ne_of_gt (Real.sqrt_pos.mpr ht_pos))]
      -- Goal: 4 * √t * √t = 4 * t
      rw [show 4 * Real.sqrt t * Real.sqrt t = 4 * (Real.sqrt t * Real.sqrt t) by ring]
      rw [Real.mul_self_sqrt (le_of_lt ht_pos)]
    linarith [this, h_sq.symm.le]
  -- Need: 2/t + 4/√t < ε².
  -- From t > 32/ε⁴: 2/t < ε⁴/16 and 4/√t < 4ε²/√32 = ε²/√2.
  -- Total < ε⁴/16 + ε²/√2 < ε² (since ε ≤ 1 and 1 / 16 + 1/√2 < 1).
  have hε4_pos : (0 : ℝ) < ε ^ 4 := by positivity
  have hε2_pos : (0 : ℝ) < ε ^ 2 := by positivity
  have h_t_large : 32 / ε ^ 4 < t := by
    rw [ht_def, div_lt_div_iff₀ hε4_pos hd_pos_r]
    have hceil : (32 * (↑d + 1) / ε ^ 4 : ℝ) < m := by
      calc (32 * (↑d + 1) / ε ^ 4 : ℝ)
          ≤ ↑(⌈32 * (↑d + 1) / ε ^ 4⌉₊) := Nat.le_ceil _
        _ < (m : ℝ) := by exact_mod_cast (by omega : ⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊ < m)
    rw [div_lt_iff₀ hε4_pos] at hceil
    nlinarith
  -- Bound 4/√t: √t > 4√2/ε² (since t > 32/ε⁴), so 4/√t < ε²/√2
  have h_sqrt_t_lower : 4 * Real.sqrt 2 / ε ^ 2 < Real.sqrt t := by
    rw [Real.lt_sqrt (by positivity)]
    calc (4 * Real.sqrt 2 / ε ^ 2) ^ 2
        = 32 / ε ^ 4 := by
          rw [div_pow, mul_pow, sq (Real.sqrt 2), Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
          ring
      _ < t := h_t_large
  have h_4_over_sqrt : 4 / Real.sqrt t < ε ^ 2 / Real.sqrt 2 := by
    rw [div_lt_div_iff₀ (Real.sqrt_pos.mpr ht_pos) (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
    calc 4 * Real.sqrt 2 = ε ^ 2 * (4 * Real.sqrt 2 / ε ^ 2) := by field_simp
      _ < ε ^ 2 * Real.sqrt t :=
          mul_lt_mul_of_pos_left h_sqrt_t_lower hε2_pos
  -- Bound 2/t: t > 32/ε⁴ implies 2/t < ε⁴/16 ≤ ε²/16
  have h_2_over_t : 2 / t < ε ^ 2 / 16 := by
    rw [div_lt_div_iff₀ ht_pos (by norm_num : (0:ℝ) < 16)]
    -- Need: 2 * 16 = 32 < ε² * t
    -- From h_t_large: 32 / ε⁴ < t, so ε² * (32 / ε⁴) < ε² * t
    -- ε² * (32 / ε⁴) = 32 / ε², and 32 / ε² ≥ 32 (since ε² ≤ 1)
    have hε2_le : ε ^ 2 ≤ 1 := by nlinarith [_hε1]
    have h1 : ε ^ 2 * (32 / ε ^ 4) < ε ^ 2 * t :=
      mul_lt_mul_of_pos_left h_t_large hε2_pos
    have h2 : ε ^ 2 * (32 / ε ^ 4) = 32 / ε ^ 2 := by
      field_simp
    have h3 : (32 : ℝ) ≤ 32 / ε ^ 2 := by
      rw [le_div_iff₀ hε2_pos]; nlinarith
    linarith
  -- ε²/16 + ε²/√2 < ε²: show 1 / 16 + 1/√2 < 1
  -- √2 > 4 / 3, so 1/√2 < 3 / 4, so 1 / 16 + 1/√2 < 1 / 16 + 3 / 4 = 13 / 16 < 1
  have h_sqrt2_bound : (4 : ℝ) / 3 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 4 / 3)]
    norm_num
  have h_inv_sqrt2 : ε ^ 2 / Real.sqrt 2 < 3 * ε ^ 2 / 4 := by
    rw [div_lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)) (by norm_num : (0:ℝ) < 4)]
    nlinarith [h_sqrt2_bound]
  -- Combine: 2/t + 4/√t < ε²/16 + ε²/√2 < ε²/16 + 3ε²/4 = 13ε²/16 < ε²
  linarith [h_mid, h_2_over_t, h_4_over_sqrt, h_inv_sqrt2]

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
  -- For ε > 1: Rad ≤ 1 < ε.
  by_cases hε1 : 1 < ε
  · use 1; intro D hD m hm
    haveI : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.pi (fun _ : Fin m => D)) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    exact lt_of_le_of_lt (rademacherComplexity_le_one X C D m (by omega)) hε1
  · push Not at hε1
    -- ε ≤ 1: use VCDim bound. For d > 0, Rad ≤ √(2d·log(em/d)/m) < ε for large m.
    -- For d = 0: Rad ≤ 1/√m < ε for large m (Khintchine).
    -- The analytical chain: 2d·log(em/d)/m → 0 as m → ∞.
    -- Pick m₀ = max(d+1, ⌈32(d+1)/ε⁴⌉ + 1).
    use max (d + 1) (Nat.ceil (32 * (↑d + 1) / ε ^ 4) + 1)
    intro D hD m hm
    have hm_pos : 0 < m := by omega
    haveI : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.pi (fun _ : Fin m => D)) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    by_cases hd_pos : d = 0
    · -- d = 0: use Khintchine bound Rad ≤ 1/√m < ε for large m.
      have hd0 : VCDim X C = (0 : ℕ) := by rw [← hd]; subst hd_pos; rfl
      have h_bound := vcdim_zero_rademacher_le_inv_sqrt X C D hd0 m hm_pos
      calc RademacherComplexity X C D m
          ≤ 1 / Real.sqrt m := h_bound
        _ < ε := by
          rw [div_lt_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm_pos))]
          -- Need: 1 < ε · √m. Suffices: 1/ε² < m.
          -- m ≥ ⌈32/ε⁴⌉+1 > 32/ε⁴ ≥ 1/ε² (since ε ≤ 1).
          have hm_ge : (⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊ + 1 : ℕ) ≤ m := by omega
          have h_ceil_le_m : (32 * ((d : ℝ) + 1) / ε ^ 4 : ℝ) < m := by
            calc (32 * ((d : ℝ) + 1) / ε ^ 4 : ℝ)
                ≤ ↑(⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊) := Nat.le_ceil _
              _ < (m : ℝ) := by exact_mod_cast (by omega : ⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊ < m)
          subst hd_pos; simp only [Nat.cast_zero, zero_add, mul_one] at h_ceil_le_m
          -- 32/ε⁴ < m. Need: 1 < ε·√m.
          -- 1/ε² ≤ 32/ε⁴ < m (since ε ≤ 1 ⟹ 1/ε² ≤ 32/ε⁴).
          -- So m > 1/ε², hence √m > 1/ε, hence ε·√m > 1.
          have hε2_pos : (0 : ℝ) < ε ^ 2 := by positivity
          have h_inv_eps2_lt_m : 1 / ε ^ 2 < (m : ℝ) := by
            have : 1 / ε ^ 2 ≤ 32 / ε ^ 4 := by
              rw [div_le_div_iff₀ hε2_pos (by positivity)]
              -- Need: ε⁴ ≤ 32·ε², i.e., ε² ≤ 32. True since ε ≤ 1.
              have : ε ^ 2 ≤ 1 := by nlinarith
              nlinarith
            linarith
          -- √m > 1/ε, so ε·√m > 1
          have h_sqrt_m : 1 / ε < Real.sqrt m := by
            rw [Real.lt_sqrt (by positivity)]
            rw [div_pow, one_pow]
            linarith
          -- ε * (1/ε) = 1, and ε * √m > ε * (1/ε) = 1
          have : ε * (1 / ε) = 1 := by field_simp
          nlinarith [mul_lt_mul_of_pos_left h_sqrt_m hε]
    · -- d > 0: Rad ≤ √(2d·log(em/d)/m) < ε.
      have hd_pos' : 0 < d := Nat.pos_of_ne_zero hd_pos
      have hdm : d ≤ m := by omega
      have h_quant := vcdim_bounds_rademacher_quantitative X C D m hm_pos d hd.symm hd_pos' hdm
      have h_anal := analytical_log_sqrt_bound d m ε hε hε1 hd_pos' hdm (by omega)
      calc RademacherComplexity X C D m
          ≤ Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m) := h_quant
        _ < Real.sqrt (ε ^ 2) := by
            apply Real.sqrt_lt_sqrt
            · apply div_nonneg
              · apply mul_nonneg
                · apply mul_nonneg
                  · norm_num
                  · exact Nat.cast_nonneg d
                · exact Real.log_nonneg (by
                    rw [le_div_iff₀ (Nat.cast_pos.mpr hd_pos')]
                    have hd_r : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos'
                    have hm_r : (d : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hdm
                    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
                    nlinarith [Real.add_one_le_exp (1 : ℝ)])
              · exact Nat.cast_nonneg m
            · exact h_anal
        _ = ε := by rw [Real.sqrt_sq (le_of_lt hε)]

-- fundamental_rademacher_equiv assembled in Theorem/PAC.lean (DAG constraint).
