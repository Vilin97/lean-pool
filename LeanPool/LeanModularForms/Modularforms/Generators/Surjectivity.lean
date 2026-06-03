/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import LeanPool.LeanModularForms.Modularforms.Generators.Defs

/-!
# Generators of the graded ring of level 1 modular forms: Surjectivity

We prove that `evalE₄E₆` is surjective by showing each `DirectSum.of _ k f` lies in
its range (strong induction on weight), then using the subalgebra closure of the range.
-/

@[expose] public section

open ModularForm hiding E₄ E₆
open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup

noncomputable section

/-- Transport a rank fact about level-one modular forms from `𝒮ℒ` to the (definitionally distinct)
group `↑Γ(1)`. `rw`/`▸` fail because `ModularForm` carries `IsArithmetic`/`HasDetOne` instance
arguments that the motive cannot abstract; `subst` on a generalized group variable avoids this. -/
private lemma rank_modularForm_gammaOne {k : ℤ} {r : Cardinal}
    (h : Module.rank ℂ (ModularForm 𝒮ℒ k) = r) : Module.rank ℂ (ModularForm Γ(1) k) = r := by
  have key : ∀ (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] [G.HasDetOne],
      G = (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)) →
      Module.rank ℂ (ModularForm G k) = r → Module.rank ℂ (ModularForm Γ(1) k) = r := by
    intro G _ _ hh hrank; subst hh; exact hrank
  exact key 𝒮ℒ CongruenceSubgroup.Gamma_one_coe_eq_SL.symm h

private lemma mul_modform_ne_zero_of_coeff_one {k₁ k₂ : ℤ}
    (f : ModularForm Γ(1) k₁) (g : ModularForm Γ(1) k₂)
    (hf : (qExpansion 1 f).coeff 0 = 1) (hg : (qExpansion 1 g).coeff 0 = 1) :
    (f.mul g : ModularForm Γ(1) (k₁ + k₂)) ≠ 0 := by
  intro h
  have hcoeff : (qExpansion 1 (f.mul g)).coeff 0 = 1 := by
    have := qExpansion_mul_coeff 1 k₁ k₂ f g
    simp only [Nat.cast_one] at this; rw [this]
    simp only [PowerSeries.coeff_mul, Finset.antidiagonal_zero, Finset.sum_singleton, hf, hg,
      mul_one]
  have hcoe : (⇑(f.mul g) : ℍ → ℂ) = 0 := by
    rw [h]; ext z; simp only [zero_apply, Pi.zero_apply]
  rw [show qExpansion 1 (f.mul g) = qExpansion 1 (0 : ℍ → ℂ) from
    congr_arg (qExpansion 1) hcoe, qExpansion_zero] at hcoeff
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_zero,
    zero_ne_one] at hcoeff

private lemma mul_Delta_map_eq_DirectSum_mul (n : ℕ) (_hn : 12 ≤ n)
    (h : ModularForm Γ(1) (↑n - 12)) :
    DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) ↑n (mulDeltaMap ↑n h) =
      DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) (↑n - 12) h *
        DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 12 (ModFormMk Γ(1) 12 Delta) := by
  rw [DirectSum.of_mul_of]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  have hind : (↑n : ℤ) - 12 + 12 = ↑n := by omega
  apply ModularForm.gradedMonoid_eq_of_cast hind.symm
  simp only [GradedMonoid.mk, mulDeltaMap]
  ext z
  simp only [mcast, mul, GradedMonoid.GMul.mul]
  rfl

private lemma cuspform_eq_mul_Delta (n : ℕ) (_hn : 12 ≤ n) (g : ModularForm Γ(1) ↑n)
    (hg : IsCuspForm Γ(1) ↑n g) :
    g = mulDeltaMap ↑n
      (CuspFormsIsoModforms ↑n (IsCuspFormToCuspForm Γ(1) ↑n g hg)) := by
  set g_cusp := IsCuspFormToCuspForm Γ(1) ↑n g hg
  set h := CuspFormsIsoModforms ↑n g_cusp
  ext z
  have hgz : g z = g_cusp z := by
    have := congr_fun (CuspForm_to_ModularForm_Fun_coe Γ(1) ↑n g hg) z
    simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
      ModularForm.toSlashInvariantForm_coe] at this
    exact this.symm
  rw [hgz, show g_cusp z = (ModformMulDelta' ↑n h) z from
    DFunLike.congr_fun ((CuspFormsIsoModforms ↑n).left_inv g_cusp).symm z,
    Modform_mul_Delta_apply, mul_Delta_map_eq]

lemma monomial_coeff_zero_eq_one (n a b : ℕ) (hab : 4 * a + 6 * b = n) :
    (qExpansion 1
      (((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ a *
        (DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ b)
        (↑n : ℤ))).coeff 0 = 1 := by
  subst hab
  have hab' : (↑(4 * a + 6 * b) : ℤ) = ↑a * 4 + ↑b * 6 := by push_cast; ring
  rw [hab', DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of]
  convert_to (qExpansion 1 (⇑(GradedMonoid.GMul.mul (GradedMonoid.GMonoid.gnpow a E₄)
      (GradedMonoid.GMonoid.gnpow b E₆)))).coeff 0 = 1 using 2
  · simp only [Int.nsmul_eq_mul, DirectSum.of_eq_same]
  change (qExpansion 1 (⇑((GradedMonoid.GMonoid.gnpow a E₄).mul
      (GradedMonoid.GMonoid.gnpow b E₆)))).coeff 0 = 1
  have hqm := qExpansion_mul_coeff 1 (a • (4 : ℤ)) (b • (6 : ℤ))
      (GradedMonoid.GMonoid.gnpow a E₄) (GradedMonoid.GMonoid.gnpow b E₆)
  simp only [Nat.cast_one] at hqm; rw [hqm]
  have gnpow_eq (k : ℤ) (e : ModularForm Γ(1) k) (m : ℕ) :
      (GradedMonoid.GMonoid.gnpow m e : ModularForm Γ(1) (m • k)) =
      ((DirectSum.of _ k e) ^ m) (m • k) := by
    rw [DirectSum.ofPow]; simp only [Int.nsmul_eq_mul, DirectSum.of_eq_same]
  simp_rw [gnpow_eq]
  change (qExpansion 1 ⇑(((DirectSum.of _ 4 E₄) ^ a) (↑a * 4)) *
       qExpansion 1 ⇑(((DirectSum.of _ 6 E₆) ^ b) (↑b * 6))).coeff 0 = 1
  rw [qExpansion_pow, qExpansion_pow]
  simp [PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
    show PowerSeries.constantCoeff (qExpansion 1 (⇑E₄)) = 1 from by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact E4_q_exp_zero,
    show PowerSeries.constantCoeff (qExpansion 1 (⇑E₆)) = 1 from by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact E6_q_exp_zero]

/-! ### Helpers for `surj_of_rank_one` base cases -/

private lemma one_modform_ne_zero : (1 : ModularForm Γ(1) 0) ≠ 0 := by
  intro h; have := congr_fun (congr_arg (fun x => x.toFun) h) UpperHalfPlane.I
  simp only [SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, one_coe_eq_one,
    Pi.one_apply, zero_apply, one_ne_zero] at this

private lemma evalE₄E₆_one :
    evalE₄E₆ 1 = DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 0 1 := by
  rw [map_one]; rfl

private lemma evalE₄E₆_X0_sq :
    evalE₄E₆ (MvPolynomial.X 0 ^ 2) =
      DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 8 (E₄.mul E₄) := by
  rw [map_pow, evalE₄E₆_X0, pow_two, DirectSum.of_mul_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq
    (ModularForm.gradedMonoid_eq_of_cast (show (4 : ℤ) + 4 = 8 by norm_num).symm rfl)

private lemma evalE₄E₆_X0_X1 :
    evalE₄E₆ (MvPolynomial.X 0 * MvPolynomial.X 1) =
      DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 10 (E₄.mul E₆) := by
  rw [map_mul, evalE₄E₆_X0, evalE₄E₆_X1, DirectSum.of_mul_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq
    (ModularForm.gradedMonoid_eq_of_cast (show (4 : ℤ) + 6 = 10 by norm_num).symm rfl)

/-! ### Inductive step -/

/-- Inductive step: for n >= 12 even, surjectivity at weight n follows from
surjectivity at all lower weights via the cusp-form / Delta decomposition. -/
private lemma surj_inductive_step (n : ℕ) (hn12 : 12 ≤ n) (hk_even : Even n)
    (ih : ∀ m < n, ∀ (f : ModularForm Γ(1) ↑m),
      DirectSum.of _ (↑m : ℤ) f ∈ Set.range evalE₄E₆)
    (f : ModularForm Γ(1) ↑n) :
    DirectSum.of _ (↑n : ℤ) f ∈ Set.range evalE₄E₆ := by
  obtain ⟨a, b, hab⟩ := monomial_weight_exists n (by omega) hk_even
  set mo := ((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ a *
    (DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ b)
  set mn := mo (↑n : ℤ)
  set c := (qExpansion 1 f).coeff 0
  have hmn_coeff : (qExpansion 1 mn).coeff 0 = 1 := monomial_coeff_zero_eq_one n a b hab
  have hg_cusp : IsCuspForm Γ(1) ↑n (f - c • mn) := by
    rw [IsCuspForm_iff_coeffZero_eq_zero]
    have hsp : (1 : ℝ) ∈ Γ(1).strictPeriods := by
      simp only [CongruenceSubgroup.strictPeriods_Gamma, Nat.cast_one,
        AddSubgroup.mem_zmultiples]
    set Q := qExpansionAddHom (by norm_num : (0 : ℝ) < 1) hsp (↑n)
    have hQ_smul : Q (c • mn) = c • Q mn :=
      ModularForm.qExpansion_smul (by norm_num : (0 : ℝ) < 1) hsp c mn
    have hQf : Q f = qExpansion 1 f := rfl
    have hQmn : Q mn = qExpansion 1 mn := rfl
    have : (Q (f - c • mn)).coeff 0 =
        (qExpansion 1 (f : ℍ → ℂ)).coeff 0 - c * (qExpansion 1 (mn : ℍ → ℂ)).coeff 0 := by
      rw [show Q (f - c • mn) = Q f - Q (c • mn) from map_sub Q f (c • mn),
        hQ_smul, hQf, hQmn]
      simp [map_sub, map_smul, smul_eq_mul]
    rw [show (qExpansion 1 (f - c • mn : ModularForm Γ(1) ↑n)).coeff 0 =
      (Q (f - c • mn)).coeff 0 from rfl, this, hmn_coeff, mul_one, sub_self]
  set g := f - c • mn
  have hcast : (↑n : ℤ) - 12 = (↑(n - 12) : ℤ) := by omega
  set h' := CuspFormsIsoModforms ↑n (IsCuspFormToCuspForm Γ(1) ↑n g hg_cusp)
  have hg_ds : DirectSum.of _ (↑n : ℤ) g =
      DirectSum.of _ ((↑n : ℤ) - 12) h' *
      DirectSum.of _ 12 (ModFormMk Γ(1) 12 Delta) := by
    rw [cuspform_eq_mul_Delta n (by omega) g hg_cusp]
    exact mul_Delta_map_eq_DirectSum_mul n (by omega) h'
  have hih : DirectSum.of _ ((↑n : ℤ) - 12) h' ∈ Set.range evalE₄E₆ := by
    rw [DirectSum_of_cast_eq hcast]; exact ih (n - 12) (by omega) (hcast ▸ h')
  have hg_in : DirectSum.of _ (↑n : ℤ) g ∈ Set.range evalE₄E₆ := by
    rw [hg_ds]; obtain ⟨p1, hp1⟩ := hih; obtain ⟨p2, hp2⟩ := delta_mem_range_evalE₄E₆
    exact ⟨p1 * p2, by rw [map_mul, hp1, hp2]⟩
  have hmn_in : mo ∈ Set.range evalE₄E₆ :=
    ⟨MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b, evalE₄E₆_monomial a b⟩
  have hmn_eq : DirectSum.of _ (↑n : ℤ) mn = mo := by
    simp only [mn, mo, DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of]
    rw [show (↑n : ℤ) = a • (4 : ℤ) + b • (6 : ℤ) from by
      simp only [Int.nsmul_eq_mul]; linarith, DirectSum.of_eq_same]
  have hf_eq : f = g + c • mn := by simp only [g, sub_add_cancel]
  have hf_ds : DirectSum.of _ (↑n : ℤ) f =
      DirectSum.of _ (↑n : ℤ) g + c • DirectSum.of _ (↑n : ℤ) mn := by
    rw [hf_eq, map_add, ← DirectSum.of_smul]
  rw [hf_ds, hmn_eq]
  obtain ⟨p1, hp1⟩ := hg_in; obtain ⟨p2, hp2⟩ := hmn_in
  exact ⟨p1 + MvPolynomial.C c * p2, by
    rw [map_add, hp1, map_mul, evalE₄E₆_C, hp2,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]⟩

/-! ### Main surjectivity proof -/

private lemma surj_of_weight : ∀ (k : ℤ) (f : ModularForm Γ(1) k),
    DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) k f ∈ Set.range evalE₄E₆ := by
  intro k f
  by_cases hk_neg : k < 0
  · rw [rank_zero_iff_forall_zero.mp
      (rank_modularForm_gammaOne (ModularForm.levelOne_neg_weight_rank_zero hk_neg)) f,
      map_zero]
    exact ⟨0, map_zero _⟩
  · push Not at hk_neg
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, by omega⟩
    revert f
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro f
    by_cases hk_odd : Odd (n : ℤ)
    · rw [levelOne_odd_weight_eq_zero hk_odd f, map_zero]; exact ⟨0, map_zero _⟩
    · rw [Int.not_odd_iff_even] at hk_odd
      by_cases hn12 : n < 12
      · -- Base cases: weights 0, 2, 4, 6, 8, 10 (all even < 12)
        by_cases hn0 : n = 0
        · subst hn0
          exact surj_of_rank_one
            (rank_modularForm_gammaOne ModularForm.levelOne_weight_zero_rank_one)
            one_modform_ne_zero 1 evalE₄E₆_one f
        by_cases hn2 : n = 2
        · subst hn2; rw [weight_two_zero f, map_zero]; exact ⟨0, map_zero _⟩
        by_cases hn4 : n = 4
        · subst hn4; exact surj_of_rank_one weight_four_one_dimensional E4_ne_zero
            (MvPolynomial.X 0) evalE₄E₆_X0 f
        by_cases hn6 : n = 6
        · subst hn6; exact surj_of_rank_one weight_six_one_dimensional E6_ne_zero
            (MvPolynomial.X 1) evalE₄E₆_X1 f
        by_cases hn8 : n = 8
        · subst hn8; exact surj_of_rank_one
            (weight_eight_one_dimensional 8 (by norm_num) ⟨4, rfl⟩ (by norm_num))
            (mul_modform_ne_zero_of_coeff_one E₄ E₄ E4_q_exp_zero E4_q_exp_zero)
            (MvPolynomial.X 0 ^ 2) evalE₄E₆_X0_sq f
        by_cases hn10 : n = 10
        · subst hn10; exact surj_of_rank_one
            (weight_eight_one_dimensional 10 (by norm_num) ⟨5, rfl⟩ (by norm_num))
            (mul_modform_ne_zero_of_coeff_one E₄ E₆ E4_q_exp_zero E6_q_exp_zero)
            (MvPolynomial.X 0 * MvPolynomial.X 1) evalE₄E₆_X0_X1 f
        · exfalso; obtain ⟨m, hm⟩ := hk_odd; omega
      · push Not at hn12
        exact surj_inductive_step n hn12 (by exact_mod_cast hk_odd)
          (fun m hm => ih m hm (by omega)) f

/-- The evaluation homomorphism `evalE₄E₆ : ℂ[X₀, X₁] →ₐ[ℂ] ⨁_k M_k(Γ(1))`
is surjective. -/
theorem evalE₄E₆_surjective : Function.Surjective evalE₄E₆ := by
  classical
  intro x
  suffices x ∈ Set.range evalE₄E₆ from this
  rw [show x = x.sum (fun i m => DirectSum.of _ i m) from
    (DFinsupp.sum_single (f := x)).symm,
    show Set.range evalE₄E₆ = ↑evalE₄E₆.range from (AlgHom.coe_range evalE₄E₆).symm]
  apply Subalgebra.sum_mem
  intro k _
  rw [AlgHom.mem_range]
  exact surj_of_weight k (x k)
