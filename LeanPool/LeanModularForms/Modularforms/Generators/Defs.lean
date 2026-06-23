/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import LeanPool.LeanModularForms.Modularforms.DimensionFormulas
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Generators of the graded ring of level 1 modular forms: Definitions

This file defines the weight function `E₄E₆Weight`, the evaluation homomorphism
`evalE₄E₆ : ℂ[X₀, X₁] →ₐ[ℂ] ⨁ k, M_k(Γ(1))`, and the polynomial `DeltaPoly`,
along with basic API lemmas (evaluation on generators, odd-weight vanishing,
monomial weight existence, and `Δ ∈ range evalE₄E₆`).
-/

@[expose] public section

open ModularForm hiding E₄ E₆
open LevelOneEisenstein
open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup

noncomputable section

/-- Weight function assigning weight 4 to E₄ (variable 0) and weight 6 to E₆ (variable 1). -/
def E₄E₆Weight : Fin 2 → ℕ := ![4, 6]

/-- Evaluation homomorphism sending `ℂ[X₀, X₁]` to the graded ring of level 1 modular forms
via `X₀ ↦ E₄` and `X₁ ↦ E₆`. -/
noncomputable def evalE₄E₆ :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ]
      DirectSum ℤ (fun k => ModularForm (CongruenceSubgroup.Gamma 1) k) :=
  MvPolynomial.aeval
    ![DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄,
      DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆]

/-- The polynomial `Δ_poly = (1/1728)(X₀³ - X₁²)` in `ℂ[X₀, X₁]`,
mapping to `Δ` under `evalE₄E₆`. -/
noncomputable def DeltaPoly : MvPolynomial (Fin 2) ℂ :=
  (1 / 1728 : ℂ) • (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)

/-! ## Odd-weight vanishing -/

/-- For odd weight k, every modular form of weight k for Γ(1) is zero. -/
theorem levelOne_odd_weight_eq_zero {k : ℤ} (hk : Odd k)
    (f : ModularForm (CongruenceSubgroup.Gamma 1) k) : f = 0 := by
  ext z
  have hmod : (f.toFun ∣[k] (-1 : SL(2, ℤ))) z = f z :=
    congrFun (f.slash_action_eq' _
      (Subgroup.mem_map_of_mem _ (CongruenceSubgroup.mem_Gamma_one (-1)))) z
  rw [SL_slash_apply, ModularGroup.SL_neg_smul, one_smul] at hmod
  have hdenom : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) (-1 : SL(2, ℤ)))) ↑z = -1 := by
    rw [ModularGroup.denom_apply]
    simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply, ne_eq, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, neg_zero, Int.cast_zero, zero_mul, Matrix.one_apply_eq, Int.reduceNeg,
      Int.cast_neg, Int.cast_one, zero_add]
  rw [hdenom, zpow_neg, hk.neg_one_zpow, inv_neg, inv_one] at hmod
  simp only [SlashInvariantForm.toFun_eq_coe, ModularForm.toSlashInvariantForm_coe] at hmod
  simp only [ModularForm.zero_apply]
  exact (mul_eq_zero.mp (show 2 * f z = 0 by linear_combination -hmod)).resolve_left two_ne_zero

/-- For odd weight k, the space of modular forms of weight k for Γ(1) has rank zero. -/
theorem levelOne_odd_weight_rank_zero {k : ℤ} (hk : Odd k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = 0 :=
  rank_zero_iff_forall_zero.mpr (levelOne_odd_weight_eq_zero hk)

/-! ## Combinatorial helpers for monomial weight decomposition -/

/-- For even k ≥ 4, there exist a, b ∈ ℕ with 4a + 6b = k. -/
lemma monomial_weight_exists (k : ℕ) (hk : 4 ≤ k) (hkeven : Even k) :
    ∃ a b : ℕ, 4 * a + 6 * b = k := by
  obtain ⟨m, rfl⟩ := hkeven
  rcases Nat.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact ⟨n, 0, by omega⟩
  · exact ⟨n - 1, 1, by omega⟩

/-! ## Q-expansion helpers -/

/-- The 0th q-expansion coefficient of E_k raised to the n-th power equals 1. -/
lemma Ek_q_exp_zero_pow (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (n : ℕ) :
    (qExpansion 1 (E k hk)).coeff 0 ^ n = 1 := by simp [Ek_q_exp_zero k hk hk2]

/-! ## Delta in the range of evalE₄E₆ -/

/-- Key computation: `evalE₄E₆ (X 0) = DirectSum.of _ 4 E₄`. -/
lemma evalE₄E₆_X0 :
    evalE₄E₆ (MvPolynomial.X 0) =
      DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄ := by
  simp only [evalE₄E₆, MvPolynomial.aeval_X, Matrix.cons_val_zero]

/-- Key computation: `evalE₄E₆ (X 1) = DirectSum.of _ 6 E₆`. -/
lemma evalE₄E₆_X1 :
    evalE₄E₆ (MvPolynomial.X 1) =
      DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆ := by
  simp only [evalE₄E₆, Fin.isValue, MvPolynomial.aeval_X, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

/-- `evalE₄E₆ (C c) = algebraMap ℂ _ c`. -/
lemma evalE₄E₆_C (c : ℂ) :
    evalE₄E₆ (MvPolynomial.C c) =
      algebraMap ℂ (DirectSum ℤ (fun k => ModularForm Γ(1) k)) c :=
  MvPolynomial.aeval_C _ c

/-- The evaluation of `DeltaPoly` under `evalE₄E₆`. -/
lemma evalE₄E₆_Delta_poly :
    evalE₄E₆ DeltaPoly =
      (1 / 1728 : ℂ) •
        ((DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄) ^ 3 -
         (DirectSum.of (fun k : ℤ =>
            ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆) ^ 2) := by
  simp only [DeltaPoly, map_smul, map_sub, map_pow, evalE₄E₆_X0, evalE₄E₆_X1]

/-- The discriminant `Δ` lies in the range of `evalE₄E₆`. -/
lemma delta_mem_range_evalE₄E₆ :
    DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 12
      (ModFormMk (CongruenceSubgroup.Gamma 1) 12 Delta) ∈ Set.range evalE₄E₆ := by
  refine ⟨DeltaPoly, ?_⟩
  rw [evalE₄E₆_Delta_poly]
  ext i
  by_cases hi : i = 12
  · subst hi
    simp only [DirectSum.smul_apply, DirectSum.sub_apply, DirectSum.of_eq_same]
    rw [show ModFormMk Γ(1) 12 Delta = ModFormMk Γ(1) 12 DeltaE4E6Aux from by
      rw [Delta_E4_eqn], Delta_E4_E6_eq]
    simp only [DirectSum.sub_apply]
  · simp only [DirectSum.smul_apply, DirectSum.sub_apply, DirectSum.of_eq_of_ne _ _ _ hi]
    have he4 : ((DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄)
        ^ 3) i = 0 := by
      rw [pow_three, DirectSum.of_mul_of, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_ne _ _ _ (by omega)
    have he6 : ((DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆)
        ^ 2) i = 0 := by
      rw [pow_two, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_ne _ _ _ (by omega)
    rw [he4, he6, sub_self, smul_zero]

/-! ## Additional API lemmas -/

/-- `evalE₄E₆` maps the monomial `X₀^a * X₁^b` to `(of _ 4 E₄)^a * (of _ 6 E₆)^b`. -/
lemma evalE₄E₆_monomial (a b : ℕ) :
    evalE₄E₆ (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      (DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄) ^ a *
      (DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆) ^ b := by
  rw [map_mul, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1]

/-- The weight-12 component of `evalE₄E₆ DeltaPoly` is the discriminant `Δ`. -/
lemma evalE₄E₆_Delta_poly_grade :
    (evalE₄E₆ DeltaPoly) (12 : ℤ) = ModFormMk (CongruenceSubgroup.Gamma 1) 12 Delta := by
  rw [evalE₄E₆_Delta_poly]
  simp only [DirectSum.smul_apply, DirectSum.sub_apply]
  rw [show ModFormMk Γ(1) 12 Delta = ModFormMk Γ(1) 12 DeltaE4E6Aux from by
    rw [Delta_E4_eqn], Delta_E4_E6_eq]
  simp only [DirectSum.sub_apply]

/-- A weighted-homogeneous polynomial evaluates to a single-graded DirectSum element. -/
lemma evalE₄E₆_whc_eq_single (n : ℕ) (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n) :
    evalE₄E₆ p = DirectSum.of _ (↑n : ℤ) ((evalE₄E₆ p) ↑n) := by
  apply DFinsupp.ext; intro k
  by_cases hk : k = (↑n : ℤ)
  · subst hk; simp [DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ hk]
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]; rw [map_sum]
    rw [show (∑ x ∈ p.support, evalE₄E₆ ((MvPolynomial.monomial x) (MvPolynomial.coeff x p))) k =
      ∑ x ∈ p.support, (evalE₄E₆ ((MvPolynomial.monomial x) (MvPolynomial.coeff x p))) k from
      map_sum (DFinsupp.evalAddMonoidHom k) _ _]
    apply Finset.sum_eq_zero
    intro d hd
    have hweight := hp (MvPolynomial.mem_support_iff.mp hd)
    have hd0 : MvPolynomial.monomial d (MvPolynomial.coeff d p) =
        MvPolynomial.C (MvPolynomial.coeff d p) * MvPolynomial.X 0 ^ d 0 *
          MvPolynomial.X 1 ^ d 1 := by
      rw [MvPolynomial.monomial_eq, mul_assoc]; congr 1
      rw [Finsupp.prod, Finset.prod_subset (fun _ _ => Finset.mem_univ _) (fun i _ hi => by
        have : d i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hi
        rw [this, pow_zero])]
      simp only [Fin.prod_univ_two]
    rw [hd0, show MvPolynomial.C (MvPolynomial.coeff d p) *
        MvPolynomial.X (0 : Fin 2) ^ d 0 * MvPolynomial.X (1 : Fin 2) ^ d 1 =
        MvPolynomial.C (MvPolynomial.coeff d p) *
        (MvPolynomial.X (0 : Fin 2) ^ d 0 * MvPolynomial.X (1 : Fin 2) ^ d 1)
        from mul_assoc _ _ _]
    rw [map_mul, evalE₄E₆_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      DirectSum.smul_apply, evalE₄E₆_monomial, DirectSum.ofPow, DirectSum.ofPow,
      DirectSum.of_mul_of]
    simp only [Int.nsmul_eq_mul]
    rw [DirectSum.of_eq_of_ne _ _ _ (by
      intro heq; apply hk; rw [heq]
      have : Finsupp.weight E₄E₆Weight d = d 0 * 4 + d 1 * 6 := by
        change (Finsupp.linearCombination ℕ E₄E₆Weight).toAddMonoidHom d = d 0 * 4 + d 1 * 6
        simp only [LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply]
        rw [d.sum_fintype (fun i a => a • E₄E₆Weight i) (fun i => by simp only [zero_smul])]
        simp only [Fin.sum_univ_two, E₄E₆Weight, Matrix.cons_val_zero, Matrix.cons_val_one,
          mul_comm, smul_eq_mul]
      rw [this] at hweight; push_cast [← hweight]; ring), smul_zero]

/-- Weight casting for DirectSum elements. -/
lemma DirectSum_of_cast_eq {k₁ k₂ : ℤ} (hk : k₁ = k₂)
    (x : ModularForm (CongruenceSubgroup.Gamma 1) k₁) :
    DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) k₁ x =
    DirectSum.of _ k₂ (hk ▸ x) := by subst hk; rfl

/-- The 0th q-expansion coefficient of `Δ` is 0 (Δ is a cusp form). -/
lemma qExpansion_coeff_zero_Delta :
    (qExpansion 1 (ModFormMk (CongruenceSubgroup.Gamma 1) 12 Delta)).coeff 0 = 0 :=
  (IsCuspForm_iff_coeffZero_eq_zero 12 _).mp ⟨Delta, rfl⟩

/-- In a 1-dimensional weight space, if the generator is in the image of `evalE₄E₆`,
then all elements are. -/
lemma surj_of_rank_one {k : ℤ}
    (hrank : Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = 1)
    {g : ModularForm (CongruenceSubgroup.Gamma 1) k} (hg : g ≠ 0)
    (p : MvPolynomial (Fin 2) ℂ) (hp : evalE₄E₆ p = DirectSum.of _ k g)
    (f : ModularForm (CongruenceSubgroup.Gamma 1) k) :
    DirectSum.of _ k f ∈ Set.range evalE₄E₆ := by
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_rank_one hrank hg f
  exact ⟨MvPolynomial.C c * p, by
    rw [map_mul, evalE₄E₆_C, hp, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, ← DirectSum.of_smul]⟩
