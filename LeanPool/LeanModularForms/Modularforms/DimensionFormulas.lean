/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import LeanPool.LeanModularForms.Modularforms.Eisenstein

/-! # DimensionFormulas -/


@[expose] public section

open ModularForm hiding E₄ E₆
open LevelOneEisenstein
open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup

noncomputable section

/-- Multiplication by the discriminant `Δ`, as a map from weight `k - 12` to weight `k`. -/
def mulDeltaMap (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
    ModularForm (CongruenceSubgroup.Gamma 1) k := by
  have := (f.mul (ModFormMk _ 12 Delta))
  have hk : k - 12 + 12 = k := by ring
  exact ModularForm.mcast hk this

lemma mcast_apply {a b : ℤ} {Γ : Subgroup SL(2, ℤ)} (h : a = b) (f : ModularForm Γ a) (z : ℍ) :
  (ModularForm.mcast h f) z = f z := by rfl

lemma mul_Delta_map_eq (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) (z : ℍ) :
  (mulDeltaMap k f) z = f z * Delta z := by
  rw [mulDeltaMap, mcast_apply ]
  rfl

lemma mul_Delta_map_eq_mul (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
  ((mulDeltaMap k f) : ℍ → ℂ) = (f.mul (ModFormMk _ 12 Delta)) := by
  ext z
  rw [mulDeltaMap, mcast_apply ]

lemma qExpansion_coe_smul {n : ℕ} [NeZero n] {k : ℤ} (a : ℂ) (f : ModularForm Γ(n) k) :
    qExpansion n (⇑(a • f)) = qExpansion n (a • ⇑f) := rfl

lemma qExpansion_coe_smul_cusp {n : ℕ} [NeZero n] {k : ℤ} (a : ℂ) (f : CuspForm Γ(n) k) :
    qExpansion n (⇑(a • f)) = qExpansion n (a • ⇑f) := rfl

lemma qExpansion_coe_sub {k : ℤ} (f g : ModularForm Γ(1) k) :
    qExpansion (1 : ℕ) (⇑(f - g)) = qExpansion (1 : ℕ) (⇑f - ⇑g) := rfl

lemma mul_Delta_IsCuspForm (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
  IsCuspForm (CongruenceSubgroup.Gamma 1) k (mulDeltaMap k f) := by
  rw [IsCuspForm_iff_coeffZero_eq_zero, qExpansion_ext2 _ _ (mul_Delta_map_eq_mul k f),
    ← Nat.cast_one (R := ℝ), qExpansion_mul_coeff]
  simp only [PowerSeries.coeff_mul, Finset.antidiagonal_zero, Prod.mk_zero_zero,
    Finset.sum_singleton, Prod.fst_zero, Prod.snd_zero]
  simp only [mul_eq_zero]
  right
  rw [Nat.cast_one, ← IsCuspForm_iff_coeffZero_eq_zero, IsCuspForm, CuspFormSubmodule,
    CuspFormToModularForm]
  simp

/-- Multiplication by the discriminant `Δ` packaged as a cusp form of weight `k`. -/
def ModformMulDelta' (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
    CuspForm (CongruenceSubgroup.Gamma 1) k :=
  IsCuspFormToCuspForm _ k (mulDeltaMap k f) (mul_Delta_IsCuspForm k f)

theorem slashInvariantForm_mul_apply {k₁ k₂ : ℤ} {Γ : Subgroup SL(2, ℤ)}
    (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) (z : ℍ) : (f.mul g) z = f z * g z := rfl

lemma Modform_mul_Delta_apply (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12))
    (z : ℍ) : (ModformMulDelta' k f) z = f z * Delta z := by
  rw [ModformMulDelta']
  have := congr_fun
    (CuspForm_to_ModularForm_Fun_coe _ _ (mulDeltaMap k f) (mul_Delta_IsCuspForm k f)) z
  simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
    toSlashInvariantForm_coe] at *
  rw [mul_Delta_map_eq] at this
  exact this

/-- The linear isomorphism between weight-`k` cusp forms and weight-`(k - 12)` modular forms,
given by dividing by `Δ`. -/
def CuspFormsIsoModforms (k : ℤ) : CuspForm (CongruenceSubgroup.Gamma 1) k ≃ₗ[ℂ]
    ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) where
      toFun f := CuspFormDivDiscriminant k f
      map_add' a b := CuspForm_div_Discriminant_Add k a b
      map_smul' := by
        intro m a
        ext z
        simp only [CuspForm_div_Discriminant_apply, CuspForm.IsGLPos.smul_apply, smul_eq_mul,
          RingHom.id_apply, IsGLPos.smul_apply]
        exact mul_div_assoc m (a z) (Δ z)
      invFun := ModformMulDelta' k
      left_inv := by
        intro f
        ext z
        simp only [Modform_mul_Delta_apply, CuspForm_div_Discriminant_apply]
        rw [Delta_apply, div_mul_cancel₀]
        apply Δ_ne_zero
      right_inv := by
        intro f
        ext z
        simp only [CuspForm_div_Discriminant_apply, Modform_mul_Delta_apply]
        rw [Delta_apply, mul_div_cancel_right₀]
        apply Δ_ne_zero

/-- Transport a rank fact about level-one modular forms from `𝒮ℒ` to the (definitionally distinct)
group `↑Γ(1)`. The `rw`/`▸`-based transports fail here because `ModularForm` carries
`IsArithmetic`/`HasDetOne` instance arguments that the motive cannot abstract; `subst` on a
generalized group variable avoids the issue. -/
private lemma rank_modularForm_gammaOne {k : ℤ} {r : Cardinal}
    (h : Module.rank ℂ (ModularForm 𝒮ℒ k) = r) : Module.rank ℂ (ModularForm Γ(1) k) = r := by
  have key : ∀ (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] [G.HasDetOne],
      G = (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)) →
      Module.rank ℂ (ModularForm G k) = r → Module.rank ℂ (ModularForm Γ(1) k) = r := by
    intro G _ _ hh hrank; subst hh; exact hrank
  exact key 𝒮ℒ CongruenceSubgroup.Gamma_one_coe_eq_SL.symm h

lemma delta_eq_E4E6_const : ∃ (c : ℂ), (c • Delta) = DeltaE4E6Aux := by
  have hr : Module.finrank ℂ (CuspForm Γ(1) 12) = 1 := by
    apply Module.finrank_eq_of_rank_eq
    rw [LinearEquiv.rank_eq (CuspFormsIsoModforms 12),
      show (12 - 12 : ℤ) = 0 from by norm_num]
    exact rank_modularForm_gammaOne ModularForm.levelOne_weight_zero_rank_one
  apply (finrank_eq_one_iff_of_nonzero' Delta Delta_ne_zero).mp hr DeltaE4E6Aux

lemma cuspform_weight_lt_12_zero (k : ℤ) (hk : k < 12) : Module.rank ℂ (CuspForm Γ(1) k) = 0 := by
  rw [LinearEquiv.rank_eq (CuspFormsIsoModforms k)]
  exact rank_modularForm_gammaOne (ModularForm.levelOne_neg_weight_rank_zero (by linarith))

lemma IsCuspForm_weight_lt_eq_zero (k : ℤ) (hk : k < 12) (f : ModularForm Γ(1) k)
    (hf : IsCuspForm Γ(1) k f) : f = 0 := by
  have hfc2:= CuspForm_to_ModularForm_coe _ _ f hf
  ext z
  simp only [ModularForm.zero_apply] at *
  have hy := congr_arg (fun x ↦ x.1) hfc2
  have hz := congr_fun hy z
  simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
  toSlashInvariantForm_coe] at hz
  rw [← hz]
  have := rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero k hk)
    (IsCuspFormToCuspForm Γ(1) k f hf)
  rw [this]
  simp only [CuspForm.zero_apply]

lemma Delta_E4_E6_eq : ModFormMk _ _ DeltaE4E6Aux =
  ((1/ 1728 : ℂ) • (((DirectSum.of _ 4 E₄)^3 - (DirectSum.of _ 6 E₆)^2) 12 )) := by
  ext
  rfl

lemma Delta_E4_E6_aux_q_one_term : (qExpansion 1 DeltaE4E6Aux).coeff 1 = 1 := by
  have := Delta_E4_E6_eq
  have h1 : (qExpansion 1 DeltaE4E6Aux) = qExpansion 1 (ModFormMk Γ(1) 12 DeltaE4E6Aux) := by
    apply qExpansion_ext2 DeltaE4E6Aux (ModFormMk Γ(1) 12 DeltaE4E6Aux) ?_
    ext z
    rw [DeltaE4E6Aux, ModFormMk]
    simp
    rfl
  rw [h1, Delta_E4_E6_eq]
  simp only [one_div, DirectSum.sub_apply]
  let A : ModularForm Γ(1) 12 := (((DirectSum.of _ 4 E₄) ^ 3) 12)
  let B : ModularForm Γ(1) 12 := (((DirectSum.of _ 6 E₆) ^ 2) 12)
  change (PowerSeries.coeff 1) (qExpansion 1 ⇑((1728⁻¹ : ℂ) • (A - B))) = 1
  rw [show qExpansion 1 ⇑((1728⁻¹ : ℂ) • (A - B)) = qExpansion 1 ((1728⁻¹ : ℂ) • (A - B)) by rfl]
  change (PowerSeries.coeff 1) (qExpansion 1 ((1728⁻¹ : ℂ) • ((A - B : ModularForm Γ(1) 12)))) = 1
  rw [← Nat.cast_one (R := ℝ), ← qExpansion_smul2]
  have hsub1 : qExpansion 1 ⇑(A - B) = qExpansion 1 (⇑A - ⇑B) := by rfl
  have hsub2 : qExpansion 1 (⇑A - ⇑B) = qExpansion 1 ⇑A - qExpansion 1 ⇑B := by
    simpa using (ModularForm.qExpansion_sub (h := (1 : ℕ))
      (hh := by positivity) (hΓ := by simp) (f := A) (g := B))
  have hmain : (PowerSeries.coeff 1) ((1728⁻¹ : ℂ) • (qExpansion 1 ⇑A - qExpansion 1 ⇑B)) = 1 := by
    have h4 := qExpansion_pow E₄ 3
    have h6 := qExpansion_pow E₆ 2
    simp only [Nat.cast_ofNat, Int.reduceMul] at h4 h6
    have hA : qExpansion 1 A = (qExpansion 1 E₄) ^ 3 := h4
    have hB : qExpansion 1 B = (qExpansion 1 E₆) ^ 2 := h6
    rw [hA, hB]
    have he4_0 := E4_q_exp_zero
    have he6_0 := E6_q_exp_zero
    have he4_1 := E4_q_exp_one
    have he6_1 := E6_q_exp_one
    -- Direct computation: coeff_1(E₄³ - E₆²) = 1728
    -- In Lean 4.29, rw/simp can't match through coercion layers (PowerSeries.coeff,
    -- ModularForm → ℍ → ℂ). Use sub_eq_sub_of_eq with manual term construction.
    rw [pow_three, pow_two]
    have hmul4a := qExpansion_mul_coeff 1 4 4 E₄ E₄
    have hmul4b := qExpansion_mul_coeff 1 4 8 E₄ (E₄.mul E₄)
    have hmul6 := qExpansion_mul_coeff 1 6 6 E₆ E₆
    simp only [Nat.cast_one] at hmul4a hmul4b hmul6
    -- Build the argument equality
    have h_arg_eq : (1728⁻¹ : ℂ) • (qExpansion 1 ⇑E₄ * (qExpansion 1 ⇑E₄ * qExpansion 1 ⇑E₄) -
        qExpansion 1 ⇑E₆ * qExpansion 1 ⇑E₆) =
        (1728⁻¹ : ℂ) • (qExpansion 1 ⇑(E₄.mul (E₄.mul E₄)) -
        qExpansion 1 ⇑(E₆.mul E₆)) := by
      congr 1
      exact congrArg₂ (· - ·) (hmul4b.trans (congrArg _ hmul4a)).symm hmul6.symm
    -- Transport through LinearMap application via congr_arg then ▸
    have h_trans := congrArg (PowerSeries.coeff 1) h_arg_eq
    -- Use ▸ which works at the definitional level
    calc (PowerSeries.coeff 1)
          (1728⁻¹ • (qExpansion 1 ⇑E₄ * (qExpansion 1 ⇑E₄ * qExpansion 1 ⇑E₄) -
          qExpansion 1 ⇑E₆ * qExpansion 1 ⇑E₆))
        = (PowerSeries.coeff 1)
          (1728⁻¹ • (qExpansion 1 ⇑(E₄.mul (E₄.mul E₄)) -
          qExpansion 1 ⇑(E₆.mul E₆))) := h_trans
      _ = 1728⁻¹ * ((PowerSeries.coeff 1) (qExpansion 1 ⇑(E₄.mul (E₄.mul E₄))) -
          (PowerSeries.coeff 1) (qExpansion 1 ⇑(E₆.mul E₆))) := by
        rw [map_smul, smul_eq_mul, map_sub]
      _ = 1728⁻¹ * (3 * 240 - (PowerSeries.coeff 1) (qExpansion 1 ⇑(E₆.mul E₆))) := by
        rw [E4_pow_q_exp_one]
      _ = 1728⁻¹ * (3 * 240 - (PowerSeries.coeff 1) (qExpansion 1 ⇑E₆ * qExpansion 1 ⇑E₆)) := by
        rw [congrArg (PowerSeries.coeff 1) hmul6]
      _ = 1 := by
        rw [PowerSeries.coeff_mul, antidiagonal_one]
        simp only [Finset.sum_insert (by decide : (1, 0) ∉ ({(0, 1)} : Finset _)),
          Finset.sum_singleton, he6_0, he6_1]
        norm_num
  simpa [hsub1, hsub2] using hmain

theorem Delta_E4_eqn : Delta = DeltaE4E6Aux := by
  ext z
  obtain ⟨c, H⟩ := delta_eq_E4E6_const
  suffices h2 : c = 1 by
    rw [h2] at H
    simp only [one_smul] at H
    rw [H]
  · have h1 := Delta_q_one_term
    have h2 := Delta_E4_E6_aux_q_one_term
    rw [← H] at h2
    have hs := (ModularForm.qExpansion_smul (h := (1 : ℕ))
      (hh := by positivity) (hΓ := by simp) c Delta).symm
    have hsmul : qExpansion 1 ⇑(c • Delta) = qExpansion 1 (c • ⇑Delta) := by rfl
    rw [hsmul, ← Nat.cast_one (R := ℝ), ← hs] at h2
    simp only [Nat.cast_one, map_smul, smul_eq_mul] at h2
    rw [h1] at h2
    simpa using h2


/-- A weight-`k` level-one space with a generator `g` whose `q`-expansion has constant term `1`
is one-dimensional, provided `k < 12` so that the cuspidal part vanishes. -/
private lemma rank_one_of_qExpansion_coeff_zero_eq_one {k : ℤ} (hk : k < 12)
    (g : ModularForm Γ(1) k) (hg_ne : g ≠ 0) (hg0 : (qExpansion 1 ⇑g).coeff 0 = 1) :
    Module.rank ℂ (ModularForm Γ(1) k) = 1 := by
  rw [rank_eq_one_iff]
  refine ⟨g, hg_ne, ?_⟩
  by_contra h
  simp only [not_forall, not_exists] at h
  obtain ⟨f, hf⟩ := h
  by_cases hf2 : IsCuspForm Γ(1) k f
  · have hfc1 := hf 0
    simp only [zero_smul] at *
    have := IsCuspForm_weight_lt_eq_zero k hk f hf2
    aesop
  · have hc1 : (qExpansion 1 f).coeff 0 ≠ 0 := by
      intro h
      rw [← IsCuspForm_iff_coeffZero_eq_zero] at h
      exact hf2 h
    set c := (qExpansion 1 f).coeff 0 with hc
    have hcusp : IsCuspForm Γ(1) k (g - c⁻¹• f) := by
      rw [IsCuspForm_iff_coeffZero_eq_zero]
      rw [← Nat.cast_one (R := ℝ), qExpansion_coe_sub,
        ModularForm.qExpansion_sub (h := (1 : ℕ)) (hh := by positivity) (hΓ := by simp)]
      have hnorm0 := modularForm_normalise f hf2
      have hcInv : c⁻¹ = ((PowerSeries.coeff 0) (qExpansion 1 ⇑f))⁻¹ := by simp [hc]
      have hnorm : (PowerSeries.coeff 0) (qExpansion 1 ⇑(c⁻¹ • f)) = 1 := by
        calc
          (PowerSeries.coeff 0) (qExpansion 1 ⇑(c⁻¹ • f)) =
              (PowerSeries.coeff 0) (qExpansion 1 (c⁻¹ • ⇑f)) := by rfl
          _ = (PowerSeries.coeff 0) (qExpansion 1 (((PowerSeries.coeff 0)
                (qExpansion 1 ⇑f))⁻¹ • ⇑f)) := by simp [hcInv]
          _ = 1 := hnorm0
      have hnorm' : PowerSeries.constantCoeff (qExpansion 1 (c⁻¹ • ⇑f)) = 1 := by
        simpa [PowerSeries.constantCoeff] using hnorm
      simp [map_sub, hg0, hnorm']
    have := IsCuspForm_weight_lt_eq_zero k hk (g - c⁻¹• f) hcusp
    have hfc := hf c
    rw [@sub_eq_zero] at this
    aesop

lemma weight_six_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 6) = 1 :=
  rank_one_of_qExpansion_coeff_zero_eq_one (by norm_num) E₆ E6_ne_zero E6_q_exp_zero

lemma weight_four_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 4) = 1 :=
  rank_one_of_qExpansion_coeff_zero_eq_one (by norm_num) E₄ E4_ne_zero E4_q_exp_zero

lemma weight_eight_one_dimensional (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (hk3 : k < 12) :
    Module.rank ℂ (ModularForm Γ(1) k) = 1 :=
  rank_one_of_qExpansion_coeff_zero_eq_one (by simpa using hk3) (E k hk) (Ek_ne_zero k hk hk2)
    (Ek_q_exp_zero k hk hk2)

lemma weight_two_zero (f : ModularForm (CongruenceSubgroup.Gamma 1) 2) : f = 0 := by
/- cant be a cuspform from the above, so let a be its constant term, then f^2 = a^2 E₄ and
f^3 = a^3 E₆, but now this would mean that Δ = 0 or a = 0, which is a contradiction. -/
  by_cases hf : IsCuspForm (CongruenceSubgroup.Gamma 1) 2 f
  · exact IsCuspForm_weight_lt_eq_zero 2 (by norm_num) f hf
  · have hc1 : (qExpansion 1 f).coeff 0 ≠ 0 := by
      intro h
      rw [← IsCuspForm_iff_coeffZero_eq_zero] at h
      exact hf h
    obtain ⟨c6, hc6⟩ := exists_smul_eq_of_rank_one' weight_six_one_dimensional E6_ne_zero
      ((f.mul f).mul f)
    have hc6e : c6 = ((qExpansion 1 f).coeff 0)^3 := by
      have h1 : qExpansion (1 : ℕ) ⇑(c6 • E₆)
          = qExpansion (1 : ℕ) ⇑(f.mul f) * qExpansion (1 : ℕ) ⇑f := by
        rw [hc6]; exact qExpansion_mul_coeff 1 4 2 (f.mul f) f
      have h2 := qExpansion_mul_coeff 1 2 2 f f
      rw [qExpansion_coe_smul, ← qExpansion_smul2 1 c6, h2] at h1
      have hh := congr_arg (fun x => x.coeff 0) h1
      simp only [_root_.map_smul, smul_eq_mul] at hh
      rw [Nat.cast_one, E6_q_exp_zero] at hh
      rw [pow_three]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, ne_eq, Int.reduceAdd, mul_one,
        map_mul] at *
      rw [← mul_assoc]
      exact hh
    obtain ⟨c4, hc4⟩ := exists_smul_eq_of_rank_one' weight_four_one_dimensional E4_ne_zero
      (f.mul f)
    have hc4e : c4 = ((qExpansion 1 f).coeff 0)^2 := by
      have h1 : qExpansion (1 : ℕ) ⇑(c4 • E₄) = qExpansion (1 : ℕ) ⇑f * qExpansion (1 : ℕ) ⇑f := by
        rw [hc4]; exact qExpansion_mul_coeff 1 2 2 f f
      rw [qExpansion_coe_smul (a := c4) (f := E₄), ← qExpansion_smul2 1 c4] at h1
      have hh := congr_arg (fun x => x.coeff 0) h1
      simp only [_root_.map_smul, smul_eq_mul] at hh
      rw [Nat.cast_one, E4_q_exp_zero] at hh
      rw [pow_two]
      simpa using hh
    exfalso
    let F := DirectSum.of _ 2 f
    let D := DirectSum.of _ 12 (ModFormMk Γ(1) 12 Delta) 12
    have : D ≠ 0 := ModForm_mk_inj _ _ _ Delta_ne_zero
    have HF2 : (F^2) = c4 • (DirectSum.of _ 4 E₄) := by
      rw [← DirectSum.of_smul, hc4]
      simp only [F]
      rw [pow_two, DirectSum.of_mul_of]
      rfl
    have HF3 : (F^3) = c6 • (DirectSum.of _ 6 E₆) := by
      rw [← DirectSum.of_smul, hc6]
      simp only [Int.reduceAdd]
      rw [pow_three, ← mul_assoc, DirectSum.of_mul_of, DirectSum.of_mul_of]
      rfl
    have HF12 : (((F^2)^3) 12) = ((qExpansion 1 f).coeff 0)^6 • (E₄.mul (E₄.mul E₄)) := by
      rw [HF2, pow_three]
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Int.reduceAdd,
        PowerSeries.coeff_zero_eq_constantCoeff]
      rw [DirectSum.of_mul_of, DirectSum.of_mul_of, hc4e, smul_smul, smul_smul]
      ring_nf
      rw [@DirectSum.smul_apply]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, Int.reduceAdd]
      rfl
    have hF2 : (((F^3)^2) 12) = ((qExpansion 1 f).coeff 0)^6 • ((E₆.mul E₆)) := by
      rw [HF3, pow_two]
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Int.reduceAdd,
        PowerSeries.coeff_zero_eq_constantCoeff]
      rw [DirectSum.of_mul_of, hc6e, smul_smul]
      ring_nf
      rw [@DirectSum.smul_apply]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, Int.reduceAdd]
      rfl
    have V : (1 / 1728 : ℂ) • ((((F^2)^3) 12) - (((F^3)^2) 12)) = ((qExpansion 1 f).coeff 0)^6 • D
      := by
      rw [HF12, hF2]
      simp only [one_div, Int.reduceAdd, PowerSeries.coeff_zero_eq_constantCoeff,
        DirectSum.of_eq_same, D]
      rw [Delta_E4_eqn, Delta_E4_E6_eq, pow_two, pow_three, DirectSum.of_mul_of,
        DirectSum.of_mul_of,DirectSum.of_mul_of]
      simp only [one_div, Int.reduceAdd, DirectSum.sub_apply]
      ext y
      simp only [IsGLPos.smul_apply, sub_apply, smul_eq_mul]
      ring_nf
      rfl
    have ht : (1 / 1728 : ℂ) • ((((F^2)^3) 12) - (((F^3)^2) 12)) = 0 := by
      ext y
      simp only [one_div, IsGLPos.smul_apply, sub_apply, smul_eq_mul, zero_apply, mul_eq_zero,
        inv_eq_zero, OfNat.ofNat_ne_zero, false_or, F]
      ring_nf
    rw [ht] at V
    have hr := congr_fun (congr_arg (fun x ↦ x.toFun) V) UpperHalfPlane.I
    simp only [SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, zero_apply,
      PowerSeries.coeff_zero_eq_constantCoeff, DirectSum.of_eq_same, IsGLPos.smul_apply,
      smul_eq_mul, zero_eq_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      D] at hr
    rcases hr with h | h
    · simp only [PowerSeries.coeff_zero_eq_constantCoeff, ne_eq, Int.reduceAdd, one_div,
      isUnit_iff_ne_zero, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.smul_eq_zero,
      F, D] at *
      exact hc1 h
    · simp only [ModFormMk] at h
      have hDelta := Δ_ne_zero UpperHalfPlane.I
      rw [← Delta_apply] at hDelta
      exact hDelta h

lemma dim_modforms_eq_one_add_dim_cuspforms (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) =
    1 + Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := by
  have h1 : Module.rank ℂ (CuspFormSubmodule (CongruenceSubgroup.Gamma 1) k) =
      Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := by
    simpa using LinearEquiv.rank_eq (CuspFormIsoCuspFormSubmodule Γ(1) k).symm
  rw [← h1, ← Submodule.rank_quotient_add_rank (CuspFormSubmodule (CongruenceSubgroup.Gamma 1) k)]
  congr
  rw [rank_eq_one_iff]
  refine ⟨Submodule.Quotient.mk (E k hk), ?_, ?_⟩
  · intro hq
    have hq' := (Submodule.Quotient.mk_eq_zero _).mp hq
    rw [CuspFormSubmodule_mem_iff_coeffZero_eq_zero, Ek_q_exp_zero k hk hk2] at hq'
    simp at hq'
  · intro v
    obtain ⟨f, rfl⟩ := Quotient.exists_rep v
    refine ⟨(qExpansion 1 f).coeff 0, ?_⟩
    change Submodule.Quotient.mk (((qExpansion 1 f).coeff 0) • E k hk) = Submodule.Quotient.mk f
    rw [Submodule.Quotient.eq, CuspFormSubmodule_mem_iff_coeffZero_eq_zero]
    let c : ℂ := (qExpansion 1 f).coeff 0
    change (PowerSeries.coeff 0) (qExpansion 1 ⇑(c • E k hk - f)) = 0
    have hqsub :
        qExpansion 1 ⇑(c • E k hk - f) =
          qExpansion 1 ⇑(c • E k hk) - qExpansion 1 ⇑f := by
      simpa using
        (ModularForm.qExpansion_sub (h := (1 : ℕ)) (hh := by positivity) (hΓ := by simp)
          (f := c • E k hk) (g := f))
    have hsmul : qExpansion 1 ⇑(c • E k hk) = c • qExpansion 1 (E k hk) := by
      calc
        qExpansion 1 ⇑(c • E k hk) = qExpansion 1 (c • ⇑(E k hk)) := by rfl
        _ = c • qExpansion 1 (E k hk) := by simpa using (qExpansion_smul2 1 c (E k hk)).symm
    rw [hqsub, hsmul, ← Nat.cast_one (R := ℝ)]
    simp [PowerSeries.coeff_zero_eq_constantCoeff, map_sub, smul_eq_mul, Ek_q_exp_zero k hk hk2,
      c]

theorem dim_weight_two : Module.rank ℂ (ModularForm Γ(1) ↑2) = 0 :=
  rank_zero_iff_forall_zero.mpr weight_two_zero

lemma floor_lem1 (k a : ℚ) (ha : 0 < a) (hak : a ≤ k) :
    1 + Nat.floor ((k - a) / a) = Nat.floor (k / a) := by
  rw [div_sub_same (Ne.symm (ne_of_lt ha))]
  have := Nat.floor_sub_one (k/a)
  norm_cast at *
  rw [this]
  refine Nat.add_sub_cancel' ?_
  refine Nat.le_floor ?_
  refine (le_div_iff₀ ha).mpr ?_
  simpa using hak

lemma dim_modforms_lvl_one (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) (k)) = if 12 ∣ ((k) : ℤ) - 2 then
    Nat.floor ((k : ℚ)/ 12) else Nat.floor ((k : ℚ) / 12) + 1 := by
  induction k using Nat.strong_induction_on with | h k ihn =>
  rw [dim_modforms_eq_one_add_dim_cuspforms (k) (by omega) hk2 ,
    LinearEquiv.rank_eq (CuspFormsIsoModforms (((k)) : ℤ))]
  by_cases HK : (3 : ℤ) ≤ (((k : ℤ) - 12))
  · have iH := ihn (k - 12) (by omega) ?_ ?_
    · have hk12 : (((k - 12) : ℕ) : ℤ) = k - 12 := by
        norm_cast
        refine Eq.symm (Int.subNatNat_of_le ?_)
        omega
      rw [hk12] at iH
      have : ((k - 12) : ℕ) = (k : ℚ) - 12 := by norm_cast
      rw [iH, this]
      by_cases h12 : 12 ∣ ((k) : ℤ) - 2
      · have h12k : 12 ∣ (k : ℤ) -12 - 2 := by omega
        simp only [h12k, ↓reduceIte, h12]
        have := floor_lem1 k 12 (by norm_num)
        norm_cast at *
        apply this
        omega
      · have h12k : ¬ 12 ∣ (k : ℤ) -12 - 2 := by omega
        simp only [h12k, ↓reduceIte, Nat.cast_add, Nat.cast_one, h12]
        have := floor_lem1 k 12 (by norm_num)
        norm_cast at *
        rw [← add_assoc, this]
        omega
    · omega
    · refine (Nat.even_sub ?_).mpr ?_
      · omega
      simp only [hk2, true_iff]
      decide
  · simp only [not_le] at HK
    have hkop : k ∈ Finset.filter Even (Finset.Icc 3 14) := by
      simp only [Finset.mem_filter, Finset.mem_Icc, hk2, and_true]
      omega
    have : Finset.filter Even (Finset.Icc 3 14) = ({4,6,8,10,12, 14} : Finset ℕ) := by decide
    rw [this] at hkop
    fin_cases hkop <;> simp_all only [Nat.ofNat_le_cast, Nat.cast_ite, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, Int.reduceLE, Int.reduceSub, Int.reduceLT, dvd_refl,
      ↓reduceIte]-- k = 4: weight k - 12 = -8
    · convert (congrArg (1 + ·) (rank_modularForm_gammaOne
        (ModularForm.levelOne_neg_weight_rank_zero
          (show (-8 : ℤ) < 0 by norm_num)))) using 1
      all_goals first | rfl | (rw [Nat.floor_eq_zero.mpr (by norm_num)]; norm_num)
    -- k = 6: weight k - 12 = -6
    · convert (congrArg (1 + ·) (rank_modularForm_gammaOne
        (ModularForm.levelOne_neg_weight_rank_zero
          (show (-6 : ℤ) < 0 by norm_num)))) using 1
      all_goals first | rfl | (rw [Nat.floor_eq_zero.mpr (by norm_num)]; norm_num)
    -- k = 8: weight k - 12 = -4
    · convert (congrArg (1 + ·) (rank_modularForm_gammaOne
        (ModularForm.levelOne_neg_weight_rank_zero
          (show (-4 : ℤ) < 0 by norm_num)))) using 1
      all_goals first | rfl | (rw [Nat.floor_eq_zero.mpr (by norm_num)]; norm_num)
    -- k = 10: weight k - 12 = -2
    · convert (congrArg (1 + ·) (rank_modularForm_gammaOne
        (ModularForm.levelOne_neg_weight_rank_zero
          (show (-2 : ℤ) < 0 by norm_num)))) using 1
      all_goals first | rfl | (rw [Nat.floor_eq_zero.mpr (by norm_num)]; norm_num)
    -- k = 12: weight k - 12 = 0
    · convert (congrArg (1 + ·)
        (rank_modularForm_gammaOne ModularForm.levelOne_weight_zero_rank_one)) using 1
      all_goals first | rfl | norm_num [show ⌊(12 : ℚ) / 12⌋₊ = 1 from by norm_num]
    -- k = 14: weight k - 12 = 2
    · have hfloor : ⌊(14 : ℚ) / 12⌋₊ = 1 := by
        rw [Nat.floor_eq_iff] <;> norm_num
      convert (congrArg (1 + ·) dim_weight_two) using 1
      all_goals first | rfl | simp only [hfloor, Nat.cast_one]
      all_goals norm_num

lemma ModularForm.dimension_level_one (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) (k)) = if 12 ∣ ((k) : ℤ) - 2 then
    Nat.floor ((k : ℚ)/ 12) else Nat.floor ((k : ℚ) / 12) + 1 :=
  dim_modforms_lvl_one k hk hk2
