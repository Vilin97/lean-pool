/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 10240-10341.
Modifications: extracted the generic transvection conjugacy lemmas and
specialized the later ICC endpoint locally. See the upstream PORT_MAP.md.
-/
import LeanPool.ConnesRigidity.Foundation.GroupTheory.SpecialLinear.Basic

/-!
# Special-linear conjugacy and ICC for Zhou §5
-/

namespace Connes
namespace SpecialLinear

/-- Conjugacy equality is equivalent to commuting with a quotient conjugator. Paper: §5. -/
theorem conjugates_eq_iff_quotient_commutes
    {G : Type*} [Group G] (u v g : G) :
    u * g * u⁻¹ = v * g * v⁻¹ ↔ Commute (v⁻¹ * u) g := by
  constructor
  · intro h
    change (v⁻¹ * u) * g = g * (v⁻¹ * u)
    calc
      (v⁻¹ * u) * g = v⁻¹ * (u * g * u⁻¹) * u := by group
      _ = v⁻¹ * (v * g * v⁻¹) * u := by rw [h]
      _ = g * (v⁻¹ * u) := by group
  · intro h
    change (v⁻¹ * u) * g = g * (v⁻¹ * u) at h
    calc
      u * g * u⁻¹ = v * ((v⁻¹ * u) * g) * u⁻¹ := by group
      _ = v * (g * (v⁻¹ * u)) * u⁻¹ := by rw [h]
      _ = v * g * v⁻¹ := by group

/-- Transvection conjugacy equality is equivalent to a commuting relation. Paper: §5. -/
theorem transvection_conjugates_eq_iff_commutes
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    {i j : ι} (hij : i ≠ j) (a b : A)
    (g : Matrix.SpecialLinearGroup ι A) :
    Matrix.SpecialLinearGroup.transvection hij a * g *
        (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij b * g *
        (Matrix.SpecialLinearGroup.transvection hij b)⁻¹ ↔
      Commute (Matrix.SpecialLinearGroup.transvection hij (a - b)) g := by
  rw [conjugates_eq_iff_quotient_commutes,
    Matrix.SpecialLinearGroup.transvection_inv,
    ← Matrix.SpecialLinearGroup.transvection_add]
  simp only [add_comm, sub_eq_add_neg]

/-- A nonzero commuting transvection forces its matrix unit to commute. Paper: §5. -/
theorem commute_matrixUnit_of_commute_nonzero_transvection
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [IsDomain A]
    {i j : ι} (hij : i ≠ j) (a : A) (ha : a ≠ 0)
    (g : Matrix.SpecialLinearGroup ι A)
    (h : Commute (Matrix.SpecialLinearGroup.transvection hij a) g) :
    Commute (Matrix.single i j (1 : A)) (g : Matrix ι ι A) := by
  have hmatrix := congrArg
    (fun u : Matrix.SpecialLinearGroup ι A => (u : Matrix ι ι A)) h.eq
  change ((1 : Matrix ι ι A) + Matrix.single i j a) *
    (g : Matrix ι ι A) = (g : Matrix ι ι A) *
      ((1 : Matrix ι ι A) + Matrix.single i j a) at hmatrix
  have hsingle : Matrix.single i j a * (g : Matrix ι ι A) =
      (g : Matrix ι ι A) * Matrix.single i j a := by
    simpa only [Matrix.add_mul, one_mul, Matrix.mul_add, mul_one, add_right_inj] using hmatrix
  have hrepr : Matrix.single i j a = a • Matrix.single i j (1 : A) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hrepr, Matrix.smul_mul, Matrix.mul_smul] at hsingle
  change Matrix.single i j (1 : A) * (g : Matrix ι ι A) =
    (g : Matrix ι ι A) * Matrix.single i j (1 : A)
  ext k l
  have hentry := congrArg (fun M : Matrix ι ι A => M k l) hsingle
  simpa only [Matrix.smul_apply, smul_eq_mul] using
    (mul_left_cancel₀ ha hentry)

/-- Noncommuting matrix units make transvection conjugation injective. Paper: §5. -/
theorem transvection_conjugates_injective_of_not_commute_matrixUnit
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [IsDomain A]
    {i j : ι} (hij : i ≠ j)
    (g : Matrix.SpecialLinearGroup ι A)
    (hnot : ¬Commute (Matrix.single i j (1 : A)) (g : Matrix ι ι A)) :
    Function.Injective (fun a : A =>
      Matrix.SpecialLinearGroup.transvection hij a * g *
        (Matrix.SpecialLinearGroup.transvection hij a)⁻¹) := by
  intro a b hab
  by_contra hne
  apply hnot
  apply commute_matrixUnit_of_commute_nonzero_transvection hij (a - b)
    (sub_ne_zero.mpr hne) g
  exact (transvection_conjugates_eq_iff_commutes hij a b g).mp hab

private theorem specialLinear_transvection_injective
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    {i j : ι} (hij : i ≠ j) :
    Function.Injective (Matrix.SpecialLinearGroup.transvection hij :
      A → Matrix.SpecialLinearGroup ι A) := by
  intro a b hab
  have hentry := congrArg (fun u : Matrix.SpecialLinearGroup ι A => u i j) hab
  simpa only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, ne_eq, hij,
    not_false_eq_true, Matrix.one_apply_ne, Matrix.single_apply_same, zero_add] using hentry

private theorem sl3_scalar_eq_one
    (g : SL3)
    (hscalar : (g : Matrix (Fin 3) (Fin 3) R) ∈ Set.range (Matrix.scalar (Fin 3))) :
    (g : Matrix (Fin 3) (Fin 3) R) = 1 := by
  obtain ⟨a, ha⟩ := hscalar
  have hroot : a ^ Fintype.card (Fin 3) = 1 := by
    simpa only [← ha, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ] using g.property
  have hroot3 : a ^ 3 = 1 := by
    simpa using hroot
  have hunit : IsUnit a := IsUnit.of_pow_eq_one hroot3 (by norm_num)
  have hdegree : a.degree = 0 := Polynomial.degree_eq_zero_of_isUnit hunit
  have haC : a = Polynomial.C (a.coeff 0) :=
    Polynomial.eq_C_of_degree_eq_zero hdegree
  have hcoeff : a.coeff 0 = 1 := by
    have hrootC := hroot3
    rw [haC] at hrootC
    generalize hb : a.coeff 0 = b
    have hc : b = 0 ∨ b = 1 := by
      fin_cases b
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with hzero | hone
    · exfalso
      have hzero' : a.coeff 0 = 0 := hb.trans hzero
      simp [hzero'] at hrootC
    · exact hone
  rw [← ha, haC, hcoeff]
  simp

/-- ICC boundary for the special-linear group. Paper: §5. -/
theorem sl3_isICC : IsICC sl3Group := by
  let transvection : R → SL3 :=
    Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide)
  have htrans_inj : Function.Injective transvection :=
    specialLinear_transvection_injective (i := 0) (j := 1) (by decide)
  change Infinite SL3 ∧ ∀ g : SL3, g ≠ 1 →
    Set.Infinite (conjugatesOf g)
  constructor
  · exact Infinite.of_injective transvection htrans_inj
  · intro g hg
    have hnot_scalar :
        ¬(g.val : Matrix (Fin 3) (Fin 3) R) ∈
          Set.range (Matrix.scalar (Fin 3)) := by
      intro hscalar
      have hidentity := sl3_scalar_eq_one g hscalar
      apply hg
      apply Subtype.ext
      simpa using hidentity
    have hnot_all : ¬∀ (i j : Fin 3), i ≠ j →
        Commute (Matrix.single i j (1 : R))
          (g.val : Matrix (Fin 3) (Fin 3) R) := by
      intro hcomm
      exact hnot_scalar (Matrix.mem_range_scalar_of_commute_single hcomm)
    push Not at hnot_all
    obtain ⟨i, j, hij, hnot⟩ := hnot_all
    let lift (a : R) : SL3 :=
      Matrix.SpecialLinearGroup.transvection hij a
    have hinj : Function.Injective (fun a : R => lift a * g * (lift a)⁻¹) := by
      intro a b hab
      apply transvection_conjugates_injective_of_not_commute_matrixUnit
        hij g hnot
      simpa [lift] using hab
    apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨a, rfl⟩
    exact isConj_iff.mpr ⟨lift a, rfl⟩

end SpecialLinear
end Connes
