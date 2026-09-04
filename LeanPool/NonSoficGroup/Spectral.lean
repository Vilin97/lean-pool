/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.NonSoficGroup.Foundations
import all LeanPool.NonSoficGroup.Foundations
import all Mathlib.Analysis.InnerProductSpace.Reproducing

noncomputable section

namespace SoficGroups

section

open Filter Topology

section ThreeProjectionSumOfSquares

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A three-vector polarization identity used in the spectral-gap argument. -/
public theorem three_pair_sum_norm_sq (a b c : H) :
    ‖a + b‖ ^ 2 + ‖b + c‖ ^ 2 + ‖c + a‖ ^ 2 =
      ‖a + b + c‖ ^ 2 + (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have hca :
      RCLike.re (inner ℂ c a) = RCLike.re (inner ℂ a c) := by
    exact @inner_re_symm ℂ H _ _ _ c a
  simp only [@norm_add_sq ℂ H, inner_add_left, map_add]
  nlinarith

omit [InnerProductSpace ℂ H] in
theorem norm_add_three_sq_le_three_mul (a b c : H) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have htriangle : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    calc
      ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le (a + b) c
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by gcongr; exact norm_add_le a b
  have hsquare :
      ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htriangle
  nlinarith [sq_nonneg (‖a‖ - ‖b‖),
    sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖c‖ - ‖a‖)]

theorem three_pairwise_residual_spectral_gap
    (a b c : H) (ε : ℝ)
    (hab : (1 - ε) * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ ‖a + b‖ ^ 2)
    (hbc : (1 - ε) * (‖b‖ ^ 2 + ‖c‖ ^ 2) ≤ ‖b + c‖ ^ 2)
    (hca : (1 - ε) * (‖c‖ ^ 2 + ‖a‖ ^ 2) ≤ ‖c + a‖ ^ 2) :
    (1 - 2 * ε) * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) ≤
      ‖a + b + c‖ ^ 2 := by
  nlinarith [three_pair_sum_norm_sq a b c]

end ThreeProjectionSumOfSquares

section TwoOrthogonalSectors

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_sq_le_of_orthogonal_two_sector
    (a₀ a₁ b₀ b₁ : H)
    (ha : inner ℂ a₀ a₁ = 0)
    (hb : inner ℂ b₀ b₁ = 0)
    (hcross₀ : inner ℂ a₀ b₁ = 0)
    (hcross₁ : inner ℂ a₁ b₀ = 0)
    (h₀ : 8 * ‖inner ℂ a₀ b₀‖ ^ 2 ≤ ‖a₀‖ ^ 2 * ‖b₀‖ ^ 2)
    (h₁ : 8 * ‖inner ℂ a₁ b₁‖ ^ 2 ≤ ‖a₁‖ ^ 2 * ‖b₁‖ ^ 2) :
    8 * ‖inner ℂ (a₀ + a₁) (b₀ + b₁)‖ ^ 2 ≤
      ‖a₀ + a₁‖ ^ 2 * ‖b₀ + b₁‖ ^ 2 := by
  have hproduct :
      (8 * ‖inner ℂ a₀ b₀‖ * ‖inner ℂ a₁ b₁‖) ^ 2 ≤
        (‖a₀‖ * ‖a₁‖ * ‖b₀‖ * ‖b₁‖) ^ 2 := by
    calc
      (8 * ‖inner ℂ a₀ b₀‖ * ‖inner ℂ a₁ b₁‖) ^ 2 =
          (8 * ‖inner ℂ a₀ b₀‖ ^ 2) *
            (8 * ‖inner ℂ a₁ b₁‖ ^ 2) := by ring
      _ ≤ (‖a₀‖ ^ 2 * ‖b₀‖ ^ 2) *
          (‖a₁‖ ^ 2 * ‖b₁‖ ^ 2) :=
        mul_le_mul h₀ h₁ (by positivity) (by positivity)
      _ = (‖a₀‖ * ‖a₁‖ * ‖b₀‖ * ‖b₁‖) ^ 2 := by ring
  have hcross :
      8 * ‖inner ℂ a₀ b₀‖ * ‖inner ℂ a₁ b₁‖ ≤
        ‖a₀‖ * ‖a₁‖ * ‖b₀‖ * ‖b₁‖ :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hproduct
  have hscalar :
      8 * (‖inner ℂ a₀ b₀‖ + ‖inner ℂ a₁ b₁‖) ^ 2 ≤
        (‖a₀‖ ^ 2 + ‖a₁‖ ^ 2) *
          (‖b₀‖ ^ 2 + ‖b₁‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a₀‖ * ‖b₁‖ - ‖a₁‖ * ‖b₀‖)]
  have hinner :
      inner ℂ (a₀ + a₁) (b₀ + b₁) =
        inner ℂ a₀ b₀ + inner ℂ a₁ b₁ := by
    simp only [CStarModule.inner_add_right, CStarModule.inner_add_left, hcross₁, add_zero, hcross₀,
      zero_add]
  have hnorm :
      ‖inner ℂ (a₀ + a₁) (b₀ + b₁)‖ ≤
        ‖inner ℂ a₀ b₀‖ + ‖inner ℂ a₁ b₁‖ := by
    rw [hinner]
    exact norm_add_le _ _
  have hnormsq :
      ‖inner ℂ (a₀ + a₁) (b₀ + b₁)‖ ^ 2 ≤
        (‖inner ℂ a₀ b₀‖ + ‖inner ℂ a₁ b₁‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  have ha' : ‖a₀ + a₁‖ ^ 2 = ‖a₀‖ ^ 2 + ‖a₁‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), ha]
    simp only [RCLike.re_to_complex, Complex.zero_re, mul_zero, add_zero]
  have hb' : ‖b₀ + b₁‖ ^ 2 = ‖b₀‖ ^ 2 + ‖b₁‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), hb]
    simp only [RCLike.re_to_complex, Complex.zero_re, mul_zero, add_zero]
  rw [ha', hb']
  nlinarith

theorem inner_sq_le_of_finite_orthogonal_sector_splitting
    {ι : Type*} [Finite ι]
    (F : ι → Submodule ℂ H)
    [∀ i, (F i).HasOrthogonalProjection]
    (U V : Submodule ℂ H)
    (hU : ∀ (i : ι) ⦃x : H⦄, x ∈ U →
      (F i).starProjection x ∈ U)
    (hV : ∀ (i : ι) ⦃x : H⦄, x ∈ V →
      (F i).starProjection x ∈ V)
    (hF : ∀ (i j : ι) ⦃x : H⦄, x ∈ F j →
      (F i).starProjection x ∈ F j)
    (hsector : ∀ (i : ι) (a b : H),
      a ∈ U → b ∈ V → a ∈ (F i)ᗮ → b ∈ (F i)ᗮ →
        8 * ‖inner ℂ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2)
    (hterminal : ∀ (a b : H), a ∈ U → b ∈ V →
      (∀ i, a ∈ F i) → (∀ i, b ∈ F i) → inner ℂ a b = 0)
    (a b : H) (ha : a ∈ U) (hb : b ∈ V) :
    8 * ‖inner ℂ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hind : ∀ (s : Finset ι) (x y : H),
      x ∈ U → y ∈ V →
      (∀ j, j ∉ s → x ∈ F j) →
      (∀ j, j ∉ s → y ∈ F j) →
      8 * ‖inner ℂ x y‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro x y hx hy hxF hyF
        have hzero : inner ℂ x y = 0 :=
          hterminal x y hx hy
            (fun j => hxF j (by simp only [Finset.notMem_empty, not_false_eq_true]))
            (fun j => hyF j (by simp only [Finset.notMem_empty, not_false_eq_true]))
        simpa only [hzero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          mul_zero,
          ge_iff_le] using mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖)
    | @insert i s hi ih =>
        intro x y hx hy hxF hyF
        let x₀ : H := (F i).starProjection x
        let x₁ : H := (F i)ᗮ.starProjection x
        let y₀ : H := (F i).starProjection y
        let y₁ : H := (F i)ᗮ.starProjection y
        have hx₀ : x₀ ∈ U := hU i hx
        have hy₀ : y₀ ∈ V := hV i hy
        have hx₁ : x₁ ∈ U := by
          dsimp [x₁]
          rw [Submodule.starProjection_orthogonal_val]
          exact U.sub_mem hx (hU i hx)
        have hy₁ : y₁ ∈ V := by
          dsimp [y₁]
          rw [Submodule.starProjection_orthogonal_val]
          exact V.sub_mem hy (hV i hy)
        have hx₀i : x₀ ∈ F i :=
          Submodule.starProjection_apply_mem (F i) x
        have hy₀i : y₀ ∈ F i :=
          Submodule.starProjection_apply_mem (F i) y
        have hx₁i : x₁ ∈ (F i)ᗮ :=
          Submodule.starProjection_apply_mem (F i)ᗮ x
        have hy₁i : y₁ ∈ (F i)ᗮ :=
          Submodule.starProjection_apply_mem (F i)ᗮ y
        have hx₀F : ∀ j, j ∉ s → x₀ ∈ F j := by
          intro j hj
          by_cases hji : j = i
          · subst j
            exact hx₀i
          · apply hF i j
            apply hxF j
            simp only [Finset.mem_insert, hji, hj, or_self, not_false_eq_true]
        have hy₀F : ∀ j, j ∉ s → y₀ ∈ F j := by
          intro j hj
          by_cases hji : j = i
          · subst j
            exact hy₀i
          · apply hF i j
            apply hyF j
            simp only [Finset.mem_insert, hji, hj, or_self, not_false_eq_true]
        have h₀ :
            8 * ‖inner ℂ x₀ y₀‖ ^ 2 ≤
              ‖x₀‖ ^ 2 * ‖y₀‖ ^ 2 :=
          ih x₀ y₀ hx₀ hy₀ hx₀F hy₀F
        have h₁ :
            8 * ‖inner ℂ x₁ y₁‖ ^ 2 ≤
              ‖x₁‖ ^ 2 * ‖y₁‖ ^ 2 :=
          hsector i x₁ y₁ hx₁ hy₁ hx₁i hy₁i
        have hsumx : x₀ + x₁ = x :=
          (F i).starProjection_add_starProjection_orthogonal x
        have hsumy : y₀ + y₁ = y :=
          (F i).starProjection_add_starProjection_orthogonal y
        have htwo := inner_sq_le_of_orthogonal_two_sector
          x₀ x₁ y₀ y₁
          (Submodule.inner_right_of_mem_orthogonal hx₀i hx₁i)
          (Submodule.inner_right_of_mem_orthogonal hy₀i hy₁i)
          (Submodule.inner_right_of_mem_orthogonal hx₀i hy₁i)
          (Submodule.inner_left_of_mem_orthogonal hy₀i hx₁i)
          h₀ h₁
        rwa [hsumx, hsumy] at htwo
  apply hind Finset.univ a b ha hb
  · intro j hj
    exact (hj (Finset.mem_univ j)).elim
  · intro j hj
    exact (hj (Finset.mem_univ j)).elim

end TwoOrthogonalSectors

section ThreeOrthogonalProjections

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

theorem ejStarProjection_re_inner (W : Submodule ℂ H)
    [W.HasOrthogonalProjection] (x : H) :
    RCLike.re (inner ℂ (W.starProjection x) x) =
      ‖W.starProjection x‖ ^ 2 := by
  have hidem : W.starProjection (W.starProjection x) =
      W.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr
      (Submodule.starProjection_apply_mem W x)
  have hinner :
      inner ℂ (W.starProjection x) x =
        inner ℂ (W.starProjection x) (W.starProjection x) := by
    calc
      inner ℂ (W.starProjection x) x =
          inner ℂ x (W.starProjection x) :=
        Submodule.inner_starProjection_left_eq_right W x x
      _ = inner ℂ x (W.starProjection (W.starProjection x)) :=
        congrArg (inner ℂ x) hidem.symm
      _ = inner ℂ (W.starProjection x) (W.starProjection x) :=
        (Submodule.inner_starProjection_left_eq_right W x
          (W.starProjection x)).symm
  rw [hinner]
  exact (norm_sq_eq_re_inner _).symm

def ejResidualProjection (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] : H →L[ℂ] H :=
  Vᗮ.starProjection

@[simp]
theorem ejResidualProjection_apply (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] (x : H) :
    ejResidualProjection V x = x - V.starProjection x :=
  Submodule.starProjection_orthogonal_val x

theorem ejResidualProjection_idempotent (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] (x : H) :
    ejResidualProjection V (ejResidualProjection V x) =
      ejResidualProjection V x := by
  change Vᗮ.starProjection (Vᗮ.starProjection x) = Vᗮ.starProjection x
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem Vᗮ x)

theorem ejResidualProjection_inner (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] (x y : H) :
    inner ℂ (ejResidualProjection V x) y =
      inner ℂ x (ejResidualProjection V y) :=
  Submodule.inner_starProjection_left_eq_right Vᗮ x y

theorem ejResidualProjection_re_inner (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] (x : H) :
    RCLike.re (inner ℂ (ejResidualProjection V x) x) =
      ‖ejResidualProjection V x‖ ^ 2 := by
  have hinner :
      inner ℂ (ejResidualProjection V x) x =
        inner ℂ (ejResidualProjection V x)
          (ejResidualProjection V x) := by
    calc
      inner ℂ (ejResidualProjection V x) x =
          inner ℂ x (ejResidualProjection V x) :=
        ejResidualProjection_inner V x x
      _ = inner ℂ x
          (ejResidualProjection V (ejResidualProjection V x)) :=
        congrArg (inner ℂ x)
          (ejResidualProjection_idempotent V x).symm
      _ = inner ℂ (ejResidualProjection V x)
          (ejResidualProjection V x) :=
        (ejResidualProjection_inner V x
          (ejResidualProjection V x)).symm
  rw [hinner]
  exact (norm_sq_eq_re_inner _).symm

variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]

def ejThreeResidualMap : H →L[ℂ] H :=
  ejResidualProjection (V 0) + ejResidualProjection (V 1) +
    ejResidualProjection (V 2)

def ejThreeResidualEnergy (x : H) : ℝ :=
  ‖ejResidualProjection (V 0) x‖ ^ 2 +
    ‖ejResidualProjection (V 1) x‖ ^ 2 +
    ‖ejResidualProjection (V 2) x‖ ^ 2

def ejThreeProjectionAverage : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H -
    (3 : ℂ)⁻¹ • ejThreeResidualMap V

@[simp]
theorem ejThreeResidualMap_apply (x : H) :
    ejThreeResidualMap V x =
      ejResidualProjection (V 0) x +
        ejResidualProjection (V 1) x +
        ejResidualProjection (V 2) x := by
  rfl

@[simp]
theorem ejThreeProjectionAverage_apply (x : H) :
    ejThreeProjectionAverage V x =
      x - (3 : ℂ)⁻¹ • ejThreeResidualMap V x := by
  rfl

theorem ejThreeResidualEnergy_nonneg (x : H) :
    0 ≤ ejThreeResidualEnergy V x := by
  unfold ejThreeResidualEnergy
  positivity

theorem ejThreeResidualEnergy_eq_re_inner (x : H) :
    ejThreeResidualEnergy V x =
      RCLike.re (inner ℂ (ejThreeResidualMap V x) x) := by
  simp only [ejThreeResidualEnergy, ejThreeResidualMap_apply,
    inner_add_left, map_add]
  rw [ejResidualProjection_re_inner (V 0) x,
    ejResidualProjection_re_inner (V 1) x,
    ejResidualProjection_re_inner (V 2) x]

theorem ejThreeResidualMap_norm_sq_le (x : H) :
    ‖ejThreeResidualMap V x‖ ^ 2 ≤
      3 * ejThreeResidualEnergy V x := by
  simpa only [ejThreeResidualMap_apply, Fin.isValue, ejResidualProjection_apply,
    ejThreeResidualEnergy] using
    norm_add_three_sq_le_three_mul (ejResidualProjection (V 0) x) (ejResidualProjection (V 1) x)
      (ejResidualProjection (V 2) x)

theorem ejResidualProjection_norm_le (i : Fin 3) (x : H) :
    ‖ejResidualProjection (V i) x‖ ≤ ‖x‖ :=
  (V i)ᗮ.norm_starProjection_apply_le x

theorem ejThreeResidualEnergy_le_three_norm_sq (x : H) :
    ejThreeResidualEnergy V x ≤ 3 * ‖x‖ ^ 2 := by
  have h0 : ‖ejResidualProjection (V 0) x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (ejResidualProjection_norm_le V 0 x)
  have h1 : ‖ejResidualProjection (V 1) x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (ejResidualProjection_norm_le V 1 x)
  have h2 : ‖ejResidualProjection (V 2) x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (ejResidualProjection_norm_le V 2 x)
  unfold ejThreeResidualEnergy
  linarith

theorem ejResidualProjection_cross_inner (W : Submodule ℂ H)
    [W.HasOrthogonalProjection] (x z : H) :
    inner ℂ (ejResidualProjection W x) (ejResidualProjection W z) =
      inner ℂ (ejResidualProjection W x) z := by
  calc
    inner ℂ (ejResidualProjection W x) (ejResidualProjection W z) =
        inner ℂ (ejResidualProjection W
          (ejResidualProjection W x)) z :=
      (ejResidualProjection_inner W (ejResidualProjection W x) z).symm
    _ = inner ℂ (ejResidualProjection W x) z := by
      rw [ejResidualProjection_idempotent W x]

theorem ejThreeResidual_cross_re_inner (x : H) :
    RCLike.re (inner ℂ (ejResidualProjection (V 0) x)
        (ejResidualProjection (V 0) (ejThreeResidualMap V x))) +
      RCLike.re (inner ℂ (ejResidualProjection (V 1) x)
        (ejResidualProjection (V 1) (ejThreeResidualMap V x))) +
      RCLike.re (inner ℂ (ejResidualProjection (V 2) x)
        (ejResidualProjection (V 2) (ejThreeResidualMap V x))) =
      ‖ejThreeResidualMap V x‖ ^ 2 := by
  calc
    _ = RCLike.re (inner ℂ (ejResidualProjection (V 0) x)
          (ejThreeResidualMap V x)) +
        RCLike.re (inner ℂ (ejResidualProjection (V 1) x)
          (ejThreeResidualMap V x)) +
        RCLike.re (inner ℂ (ejResidualProjection (V 2) x)
          (ejThreeResidualMap V x)) := by
      rw [ejResidualProjection_cross_inner (V 0),
        ejResidualProjection_cross_inner (V 1),
        ejResidualProjection_cross_inner (V 2)]
    _ = RCLike.re (inner ℂ
        (ejResidualProjection (V 0) x +
          ejResidualProjection (V 1) x +
          ejResidualProjection (V 2) x)
        (ejThreeResidualMap V x)) := by
      simp only [inner_add_left, map_add]
    _ = ‖ejThreeResidualMap V x‖ ^ 2 := by
      rw [← ejThreeResidualMap_apply V x]
      exact (norm_sq_eq_re_inner _).symm

theorem norm_sub_one_third_smul_sq (a b : H) :
    ‖a - (3 : ℂ)⁻¹ • b‖ ^ 2 =
      ‖a‖ ^ 2 - (2 / 3 : ℝ) * RCLike.re (inner ℂ a b) +
        (1 / 9 : ℝ) * ‖b‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
  norm_num [Complex.mul_re]
  ring

theorem ejResidualProjection_average_norm_sq
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (x z : H) :
    ‖ejResidualProjection W (x - (3 : ℂ)⁻¹ • z)‖ ^ 2 =
      ‖ejResidualProjection W x‖ ^ 2 -
        (2 / 3 : ℝ) * RCLike.re
          (inner ℂ (ejResidualProjection W x)
            (ejResidualProjection W z)) +
        (1 / 9 : ℝ) * ‖ejResidualProjection W z‖ ^ 2 := by
  rw [map_sub, map_smul]
  exact norm_sub_one_third_smul_sq
    (ejResidualProjection W x) (ejResidualProjection W z)

theorem ejThreeResidualEnergy_average (x : H) :
    ejThreeResidualEnergy V (ejThreeProjectionAverage V x) =
      ejThreeResidualEnergy V x -
        (2 / 3 : ℝ) * ‖ejThreeResidualMap V x‖ ^ 2 +
        (1 / 9 : ℝ) *
          ejThreeResidualEnergy V (ejThreeResidualMap V x) := by
  unfold ejThreeResidualEnergy
  rw [ejThreeProjectionAverage_apply,
    ejResidualProjection_average_norm_sq (V 0),
    ejResidualProjection_average_norm_sq (V 1),
    ejResidualProjection_average_norm_sq (V 2)]
  have hcross := ejThreeResidual_cross_re_inner V x
  nlinarith

theorem ejThreeResidualMap_spectral_gap (x : H) (ε : ℝ)
    (h01 : (1 - ε) *
      (‖ejResidualProjection (V 0) x‖ ^ 2 +
        ‖ejResidualProjection (V 1) x‖ ^ 2) ≤
      ‖ejResidualProjection (V 0) x +
        ejResidualProjection (V 1) x‖ ^ 2)
    (h12 : (1 - ε) *
      (‖ejResidualProjection (V 1) x‖ ^ 2 +
        ‖ejResidualProjection (V 2) x‖ ^ 2) ≤
      ‖ejResidualProjection (V 1) x +
        ejResidualProjection (V 2) x‖ ^ 2)
    (h20 : (1 - ε) *
      (‖ejResidualProjection (V 2) x‖ ^ 2 +
        ‖ejResidualProjection (V 0) x‖ ^ 2) ≤
      ‖ejResidualProjection (V 2) x +
        ejResidualProjection (V 0) x‖ ^ 2) :
    (1 - 2 * ε) * ejThreeResidualEnergy V x ≤
      ‖ejThreeResidualMap V x‖ ^ 2 := by
  exact three_pairwise_residual_spectral_gap
    (ejResidualProjection (V 0) x)
    (ejResidualProjection (V 1) x)
    (ejResidualProjection (V 2) x)
    ε h01 h12 h20

theorem ejThreeResidualEnergy_average_le
    (x : H) (δ : ℝ)
    (hgap : δ * ejThreeResidualEnergy V x ≤
      ‖ejThreeResidualMap V x‖ ^ 2) :
    ejThreeResidualEnergy V (ejThreeProjectionAverage V x) ≤
      (1 - δ / 3) * ejThreeResidualEnergy V x := by
  rw [ejThreeResidualEnergy_average]
  have hupper := ejThreeResidualEnergy_le_three_norm_sq V
    (ejThreeResidualMap V x)
  nlinarith

theorem ejStarProjection_mem_inf_orthogonal
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    (w : H) (hw : w ∈ (U ⊓ V)ᗮ) :
    U.starProjection w ∈ (U ⊓ V)ᗮ := by
  intro q hq
  calc
    inner ℂ q (U.starProjection w) =
        inner ℂ (U.starProjection q) w :=
      (Submodule.inner_starProjection_left_eq_right U q w).symm
    _ = inner ℂ q w := by
      rw [Submodule.starProjection_eq_self_iff.mpr hq.1]
    _ = 0 := hw q hq

theorem ejTwoProjection_norm_sq_sum_le_of_angle
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (c : ℝ) (hc : 0 ≤ c)
    (hangle : ∀ (u v : H),
      u ∈ U → u ∈ (U ⊓ V)ᗮ →
      v ∈ V → v ∈ (U ⊓ V)ᗮ →
        ‖inner ℂ u v‖ ≤ c * ‖u‖ * ‖v‖)
    (w : H) (hw : w ∈ (U ⊓ V)ᗮ) :
    ‖U.starProjection w‖ ^ 2 + ‖V.starProjection w‖ ^ 2 ≤
      (1 + c) * ‖w‖ ^ 2 := by
  let u : H := U.starProjection w
  let v : H := V.starProjection w
  have hu : u ∈ U := Submodule.starProjection_apply_mem U w
  have hv : v ∈ V := Submodule.starProjection_apply_mem V w
  have huorth : u ∈ (U ⊓ V)ᗮ :=
    ejStarProjection_mem_inf_orthogonal U V w hw
  have hvorth : v ∈ (U ⊓ V)ᗮ := by
    have h := ejStarProjection_mem_inf_orthogonal V U w (by
      simpa only [inf_comm] using hw)
    simpa only [inf_comm] using h
  have hre : RCLike.re (inner ℂ u v) ≤ c * ‖u‖ * ‖v‖ :=
    (RCLike.re_le_norm (inner ℂ u v)).trans
      (hangle u v hu huorth hv hvorth)
  have hsum :
      ‖u + v‖ ^ 2 ≤
        (1 + c) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    rw [norm_add_sq (𝕜 := ℂ)]
    nlinarith [mul_nonneg hc (sq_nonneg (‖u‖ - ‖v‖))]
  have huinner :
      (inner ℂ (U.starProjection w) w).re =
        ‖U.starProjection w‖ ^ 2 := by
    change RCLike.re (inner ℂ (U.starProjection w) w) = _
    exact ejStarProjection_re_inner U w
  have hvinner :
      (inner ℂ (V.starProjection w) w).re =
        ‖V.starProjection w‖ ^ 2 := by
    change RCLike.re (inner ℂ (V.starProjection w) w) = _
    exact ejStarProjection_re_inner V w
  have hlinear :
      ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ ‖u + v‖ * ‖w‖ := by
    calc
      ‖u‖ ^ 2 + ‖v‖ ^ 2 =
          RCLike.re (inner ℂ (u + v) w) := by
        dsimp [u, v]
        simp only [inner_add_left, Complex.add_re]
        rw [huinner, hvinner]
      _ ≤ ‖inner ℂ (u + v) w‖ :=
        RCLike.re_le_norm _
      _ ≤ ‖u + v‖ * ‖w‖ :=
        norm_inner_le_norm _ _
  have hsq :
      (‖u‖ ^ 2 + ‖v‖ ^ 2) ^ 2 ≤
        (‖u + v‖ * ‖w‖) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hlinear
  have hcancel :
      (‖u‖ ^ 2 + ‖v‖ ^ 2) *
          (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤
        ((1 + c) * ‖w‖ ^ 2) *
          (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    calc
      _ = (‖u‖ ^ 2 + ‖v‖ ^ 2) ^ 2 := by ring
      _ ≤ (‖u + v‖ * ‖w‖) ^ 2 := hsq
      _ = ‖u + v‖ ^ 2 * ‖w‖ ^ 2 := by ring
      _ ≤ ((1 + c) * (‖u‖ ^ 2 + ‖v‖ ^ 2)) *
          ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsum (sq_nonneg ‖w‖)
      _ = ((1 + c) * ‖w‖ ^ 2) *
          (‖u‖ ^ 2 + ‖v‖ ^ 2) := by ring
  change ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ (1 + c) * ‖w‖ ^ 2
  by_cases hz : ‖u‖ ^ 2 + ‖v‖ ^ 2 = 0
  · rw [hz]
    positivity
  · have hpos : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hpos).mp
    calc
      _ ≤ ((1 + c) * ‖w‖ ^ 2) *
          (‖u‖ ^ 2 + ‖v‖ ^ 2) := hcancel
      _ = (‖u‖ ^ 2 + ‖v‖ ^ 2) *
          ((1 + c) * ‖w‖ ^ 2) := by ring

theorem ejTwoResidualEnergy_ge_of_angle
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (c : ℝ) (hc : 0 ≤ c)
    (hangle : ∀ (u v : H),
      u ∈ U → u ∈ (U ⊓ V)ᗮ →
      v ∈ V → v ∈ (U ⊓ V)ᗮ →
        ‖inner ℂ u v‖ ≤ c * ‖u‖ * ‖v‖)
    (w : H) (hw : w ∈ (U ⊓ V)ᗮ) :
    (1 - c) * ‖w‖ ^ 2 ≤
      ‖ejResidualProjection U w‖ ^ 2 +
        ‖ejResidualProjection V w‖ ^ 2 := by
  have hU := U.norm_sq_eq_add_norm_sq_starProjection w
  have hV := V.norm_sq_eq_add_norm_sq_starProjection w
  change ‖w‖ ^ 2 =
    ‖U.starProjection w‖ ^ 2 +
      ‖ejResidualProjection U w‖ ^ 2 at hU
  change ‖w‖ ^ 2 =
    ‖V.starProjection w‖ ^ 2 +
      ‖ejResidualProjection V w‖ ^ 2 at hV
  have hsum :=
    ejTwoProjection_norm_sq_sum_le_of_angle U V c hc hangle w hw
  nlinarith

theorem ejTwoResidual_sum_re_inner
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (w : H) :
    RCLike.re (inner ℂ
      (ejResidualProjection U w + ejResidualProjection V w) w) =
        ‖ejResidualProjection U w‖ ^ 2 +
          ‖ejResidualProjection V w‖ ^ 2 := by
  have hU :
      (inner ℂ (ejResidualProjection U w) w).re =
        ‖ejResidualProjection U w‖ ^ 2 := by
    change RCLike.re (inner ℂ (ejResidualProjection U w) w) = _
    exact ejResidualProjection_re_inner U w
  have hV :
      (inner ℂ (ejResidualProjection V w) w).re =
        ‖ejResidualProjection V w‖ ^ 2 := by
    change RCLike.re (inner ℂ (ejResidualProjection V w) w) = _
    exact ejResidualProjection_re_inner V w
  change
    (inner ℂ
      (ejResidualProjection U w + ejResidualProjection V w) w).re = _
  simp only [inner_add_left, Complex.add_re]
  rw [hU, hV]

theorem ejTwoResidual_spectral_gap_of_angle
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [(U ⊓ V).HasOrthogonalProjection]
    (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 1)
    (hangle : ∀ (u v : H),
      u ∈ U → u ∈ (U ⊓ V)ᗮ →
      v ∈ V → v ∈ (U ⊓ V)ᗮ →
        ‖inner ℂ u v‖ ≤ c * ‖u‖ * ‖v‖)
    (x : H) :
    (1 - c) *
        (‖ejResidualProjection U x‖ ^ 2 +
          ‖ejResidualProjection V x‖ ^ 2) ≤
      ‖ejResidualProjection U x +
        ejResidualProjection V x‖ ^ 2 := by
  let q : H := (U ⊓ V).starProjection x
  let w : H := x - q
  have hw : w ∈ (U ⊓ V)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal x
  have hq : q ∈ U ⊓ V :=
    Submodule.starProjection_apply_mem (U ⊓ V) x
  have hqU : ejResidualProjection U q = 0 := by
    rw [ejResidualProjection_apply,
      Submodule.starProjection_eq_self_iff.mpr hq.1, sub_self]
  have hqV : ejResidualProjection V q = 0 := by
    rw [ejResidualProjection_apply,
      Submodule.starProjection_eq_self_iff.mpr hq.2, sub_self]
  have hwU : ejResidualProjection U w =
      ejResidualProjection U x := by
    dsimp [w]
    rw [map_sub, hqU, sub_zero]
  have hwV : ejResidualProjection V w =
      ejResidualProjection V x := by
    dsimp [w]
    rw [map_sub, hqV, sub_zero]
  let e : ℝ :=
    ‖ejResidualProjection U w‖ ^ 2 +
      ‖ejResidualProjection V w‖ ^ 2
  let z : H :=
    ejResidualProjection U w + ejResidualProjection V w
  have he : 0 ≤ e := by
    dsimp [e]
    positivity
  have hcoercive : (1 - c) * ‖w‖ ^ 2 ≤ e :=
    ejTwoResidualEnergy_ge_of_angle U V c hc hangle w hw
  have hlinear : e ≤ ‖z‖ * ‖w‖ := by
    calc
      e = RCLike.re (inner ℂ z w) :=
        (ejTwoResidual_sum_re_inner U V w).symm
      _ ≤ ‖inner ℂ z w‖ := RCLike.re_le_norm _
      _ ≤ ‖z‖ * ‖w‖ := norm_inner_le_norm _ _
  have hsq : e ^ 2 ≤ (‖z‖ * ‖w‖) ^ 2 :=
    (sq_le_sq₀ he (by positivity)).mpr hlinear
  have hgap : (1 - c) * e ≤ ‖z‖ ^ 2 := by
    by_cases hz : e = 0
    · rw [hz, mul_zero]
      positivity
    · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hepos).mp
      calc
        e * ((1 - c) * e) = (1 - c) * e ^ 2 := by ring
        _ ≤ (1 - c) * (‖z‖ * ‖w‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr hc')
        _ = ‖z‖ ^ 2 * ((1 - c) * ‖w‖ ^ 2) := by ring
        _ ≤ ‖z‖ ^ 2 * e :=
          mul_le_mul_of_nonneg_left hcoercive (sq_nonneg ‖z‖)
        _ = e * ‖z‖ ^ 2 := by ring
  change (1 - c) * e ≤ ‖z‖ ^ 2 at hgap
  dsimp [e, z] at hgap
  rw [hwU, hwV] at hgap
  exact hgap

theorem ejThreeProjectionAverage_dist_sq (x : H) :
    dist x (ejThreeProjectionAverage V x) ^ 2 =
      (1 / 9 : ℝ) * ‖ejThreeResidualMap V x‖ ^ 2 := by
  rw [dist_eq_norm, ejThreeProjectionAverage_apply]
  have hsub :
      x - (x - (3 : ℂ)⁻¹ • ejThreeResidualMap V x) =
        (3 : ℂ)⁻¹ • ejThreeResidualMap V x := by
    abel
  rw [hsub, norm_smul, norm_inv]
  norm_num
  ring

theorem ejThreeProjectionAverage_dist_sq_le (x : H) :
    dist x (ejThreeProjectionAverage V x) ^ 2 ≤
      ejThreeResidualEnergy V x / 3 := by
  rw [ejThreeProjectionAverage_dist_sq]
  have h := ejThreeResidualMap_norm_sq_le V x
  nlinarith

theorem ejThreeResidualEnergy_iterate_le
    (δ : ℝ) (hδ : δ ≤ 3)
    (hgap : ∀ x : H,
      δ * ejThreeResidualEnergy V x ≤ ‖ejThreeResidualMap V x‖ ^ 2)
    (x : H) (n : ℕ) :
    ejThreeResidualEnergy V
        (((ejThreeProjectionAverage V : H → H)^[n]) x) ≤
      (1 - δ / 3) ^ n * ejThreeResidualEnergy V x := by
  have hnonneg : 0 ≤ 1 - δ / 3 := by linarith
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, pow_zero, one_mul, Std.le_refl]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        ejThreeResidualEnergy V
            (ejThreeProjectionAverage V
              (((ejThreeProjectionAverage V : H → H)^[n]) x)) ≤
          (1 - δ / 3) * ejThreeResidualEnergy V
            (((ejThreeProjectionAverage V : H → H)^[n]) x) :=
          ejThreeResidualEnergy_average_le V _ δ (hgap _)
        _ ≤ (1 - δ / 3) *
            ((1 - δ / 3) ^ n * ejThreeResidualEnergy V x) :=
          mul_le_mul_of_nonneg_left ih hnonneg
        _ = (1 - δ / 3) ^ n.succ *
            ejThreeResidualEnergy V x := by
          rw [pow_succ]
          ring

theorem ejThreeProjectionAverage_iterate_dist_le_geometric
    (δ : ℝ) (hδ : δ ≤ 3)
    (hgap : ∀ x : H,
      δ * ejThreeResidualEnergy V x ≤ ‖ejThreeResidualMap V x‖ ^ 2)
    (x : H) (n : ℕ) :
    dist (((ejThreeProjectionAverage V : H → H)^[n]) x)
        (((ejThreeProjectionAverage V : H → H)^[n + 1]) x) ≤
      Real.sqrt (ejThreeResidualEnergy V x / 3) *
        (1 - δ / 6) ^ n := by
  let q : ℝ := 1 - δ / 3
  let r : ℝ := 1 - δ / 6
  have hq : 0 ≤ q := by
    dsimp [q]
    linarith
  have hr : 0 ≤ r := by
    dsimp [r]
    linarith
  have hqr : q ≤ r ^ 2 := by
    dsimp [q, r]
    nlinarith [sq_nonneg δ]
  let y : H := ((ejThreeProjectionAverage V : H → H)^[n]) x
  have hiter :
      ejThreeResidualEnergy V y ≤
        q ^ n * ejThreeResidualEnergy V x :=
    ejThreeResidualEnergy_iterate_le V δ hδ hgap x n
  have hpow : q ^ n ≤ (r ^ 2) ^ n :=
    pow_le_pow_left₀ hq hqr n
  have henergy :
      ejThreeResidualEnergy V y ≤
        r ^ (2 * n) * ejThreeResidualEnergy V x := by
    calc
      ejThreeResidualEnergy V y ≤
          q ^ n * ejThreeResidualEnergy V x := hiter
      _ ≤ (r ^ 2) ^ n * ejThreeResidualEnergy V x :=
        mul_le_mul_of_nonneg_right hpow
          (ejThreeResidualEnergy_nonneg V x)
      _ = r ^ (2 * n) * ejThreeResidualEnergy V x := by
        rw [pow_mul]
  have hstep := ejThreeProjectionAverage_dist_sq_le V y
  have hsqrt :
      (Real.sqrt (ejThreeResidualEnergy V x / 3)) ^ 2 =
        ejThreeResidualEnergy V x / 3 :=
    Real.sq_sqrt
      (div_nonneg (ejThreeResidualEnergy_nonneg V x) (by norm_num))
  have hsquared :
      dist y (ejThreeProjectionAverage V y) ^ 2 ≤
        (Real.sqrt (ejThreeResidualEnergy V x / 3) * r ^ n) ^ 2 := by
    rw [mul_pow, hsqrt]
    have hpower : (r ^ n) ^ 2 = r ^ (2 * n) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hpower]
    nlinarith
  have hdist :
      dist y (ejThreeProjectionAverage V y) ≤
        Real.sqrt (ejThreeResidualEnergy V x / 3) * r ^ n :=
    (sq_le_sq₀ (dist_nonneg) (by positivity)).mp hsquared
  change dist y
    (((ejThreeProjectionAverage V : H → H)^[n + 1]) x) ≤
      Real.sqrt (ejThreeResidualEnergy V x / 3) * r ^ n
  rw [Function.iterate_succ_apply']
  exact hdist

theorem ejThreeResidual_spectral_gap_of_pair_angles
    [∀ i j : Fin 3, (V i ⊓ V j).HasOrthogonalProjection]
    (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 1)
    (hangle : ∀ (i j : Fin 3) (u v : H),
      u ∈ V i → u ∈ (V i ⊓ V j)ᗮ →
      v ∈ V j → v ∈ (V i ⊓ V j)ᗮ →
        ‖inner ℂ u v‖ ≤ c * ‖u‖ * ‖v‖)
    (x : H) :
    (1 - 2 * c) * ejThreeResidualEnergy V x ≤
      ‖ejThreeResidualMap V x‖ ^ 2 := by
  apply ejThreeResidualMap_spectral_gap V x c
  · exact ejTwoResidual_spectral_gap_of_angle
      (V 0) (V 1) c hc hc' (hangle 0 1) x
  · exact ejTwoResidual_spectral_gap_of_angle
      (V 1) (V 2) c hc hc' (hangle 1 2) x
  · exact ejTwoResidual_spectral_gap_of_angle
      (V 2) (V 0) c hc hc' (hangle 2 0) x

theorem ejThreeProjectionAverage_iterate_dist_le_of_pair_angles
    [∀ i j : Fin 3, (V i ⊓ V j).HasOrthogonalProjection]
    (c : ℝ) (hc : 0 ≤ c) (hchalf : c < (1 / 2 : ℝ))
    (hangle : ∀ (i j : Fin 3) (u v : H),
      u ∈ V i → u ∈ (V i ⊓ V j)ᗮ →
      v ∈ V j → v ∈ (V i ⊓ V j)ᗮ →
        ‖inner ℂ u v‖ ≤ c * ‖u‖ * ‖v‖)
    (x : H) (n : ℕ) :
    dist (((ejThreeProjectionAverage V : H → H)^[n]) x)
        (((ejThreeProjectionAverage V : H → H)^[n + 1]) x) ≤
      Real.sqrt (ejThreeResidualEnergy V x / 3) *
        (1 - (1 - 2 * c) / 6) ^ n := by
  have hc' : c ≤ 1 := by linarith
  apply ejThreeProjectionAverage_iterate_dist_le_geometric V
    (1 - 2 * c) (by linarith)
  intro y
  exact ejThreeResidual_spectral_gap_of_pair_angles
    V c hc hc' hangle y

theorem ejThreeResidualEnergy_sqrt_div_three_le
    (x : H) (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ i : Fin 3,
      ‖ejResidualProjection (V i) x‖ ≤ T) :
    Real.sqrt (ejThreeResidualEnergy V x / 3) ≤ T := by
  have h₀ : ‖ejResidualProjection (V 0) x‖ ^ 2 ≤ T ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hT).mpr (hbound 0)
  have h₁ : ‖ejResidualProjection (V 1) x‖ ^ 2 ≤ T ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hT).mpr (hbound 1)
  have h₂ : ‖ejResidualProjection (V 2) x‖ ^ 2 ≤ T ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hT).mpr (hbound 2)
  apply Real.sqrt_le_iff.mpr
  refine ⟨hT, ?_⟩
  unfold ejThreeResidualEnergy
  nlinarith

theorem ejThreeProjectionAverage_fixed_iff_residualMap_eq_zero (x : H) :
    ejThreeProjectionAverage V x = x ↔
      ejThreeResidualMap V x = 0 := by
  constructor
  · intro h
    rw [ejThreeProjectionAverage_apply] at h
    have hz : (3 : ℂ)⁻¹ • ejThreeResidualMap V x = 0 :=
      sub_eq_self.mp h
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  · intro h
    simp only [ejThreeProjectionAverage_apply, h, smul_zero, sub_zero]

theorem ejThreeResidualEnergy_eq_zero_iff (x : H) :
    ejThreeResidualEnergy V x = 0 ↔
      ∀ i : Fin 3, ejResidualProjection (V i) x = 0 := by
  constructor
  · intro h i
    have h₀ : 0 ≤ ‖ejResidualProjection (V 0) x‖ ^ 2 :=
      sq_nonneg _
    have h₁ : 0 ≤ ‖ejResidualProjection (V 1) x‖ ^ 2 :=
      sq_nonneg _
    have h₂ : 0 ≤ ‖ejResidualProjection (V 2) x‖ ^ 2 :=
      sq_nonneg _
    unfold ejThreeResidualEnergy at h
    fin_cases i
    · change ejResidualProjection (V 0) x = 0
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (ejResidualProjection (V 0) x)]
    · change ejResidualProjection (V 1) x = 0
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (ejResidualProjection (V 1) x)]
    · change ejResidualProjection (V 2) x = 0
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (ejResidualProjection (V 2) x)]
  · intro h
    unfold ejThreeResidualEnergy
    simp only [Fin.isValue, h 0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      h 1,
      add_zero, h 2]

theorem ejThreeProjectionAverage_fixed_mem
    (x : H) (hx : ejThreeProjectionAverage V x = x)
    (i : Fin 3) : x ∈ V i := by
  have hD : ejThreeResidualMap V x = 0 :=
    (ejThreeProjectionAverage_fixed_iff_residualMap_eq_zero V x).mp hx
  have hE : ejThreeResidualEnergy V x = 0 := by
    rw [ejThreeResidualEnergy_eq_re_inner V x, hD]
    simp only [inner_zero_left, RCLike.re_to_complex, Complex.zero_re]
  have hres : ejResidualProjection (V i) x = 0 :=
    (ejThreeResidualEnergy_eq_zero_iff V x).mp hE i
  rw [ejResidualProjection_apply, sub_eq_zero] at hres
  exact Submodule.starProjection_eq_self_iff.mp hres.symm

end ThreeOrthogonalProjections

section ThreeFiniteUnitaryFixedSpaces

universe u₂ v₂

def ejUnitaryFixedSubmodule
    {G : Type u₂} {H : Type v₂} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) :
    Submodule ℂ H where
  carrier := {x : H | ∀ k : K, π (k : G) x = x}
  zero_mem' k := by simp only [map_zero]
  add_mem' hx hy k := by
    simp only [map_add, hx k, hy k]
  smul_mem' c x hx k := by
    simp only [map_smul, hx k]

@[simp]
theorem mem_ejUnitaryFixedSubmodule
    {G : Type u₂} {H : Type v₂} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) (x : H) :
    x ∈ ejUnitaryFixedSubmodule π K ↔
      ∀ k : K, π (k : G) x = x :=
  Iff.rfl

theorem ejUnitaryFixedSubmodule_isClosed
    {G : Type u₂} {H : Type v₂} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) :
    IsClosed (ejUnitaryFixedSubmodule π K : Set H) := by
  have hset :
      (ejUnitaryFixedSubmodule π K : Set H) =
        ⋂ k : K, {x : H | π (k : G) x = x} := by
    ext x
    simp only [SetLike.mem_coe, mem_ejUnitaryFixedSubmodule, Subtype.forall, Set.mem_iInter,
      Set.mem_ofPred_eq]
  rw [hset]
  exact isClosed_iInter fun k =>
    isClosed_eq (π (k : G)).continuous continuous_id

theorem ejUnitaryFixedSubmodule_inf_isClosed
    {G : Type u₂} {H : Type v₂} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K J : Subgroup G) :
    IsClosed
      ((ejUnitaryFixedSubmodule π K ⊓
        ejUnitaryFixedSubmodule π J : Submodule ℂ H) : Set H) := by
  change IsClosed
    ((ejUnitaryFixedSubmodule π K : Set H) ∩
      (ejUnitaryFixedSubmodule π J : Set H))
  exact (ejUnitaryFixedSubmodule_isClosed π K).inter
    (ejUnitaryFixedSubmodule_isClosed π J)

instance ejUnitaryFixedSubmodule_completeSpace
    {G : Type u₂} {H : Type v₂} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) :
    CompleteSpace (ejUnitaryFixedSubmodule π K) :=
  (ejUnitaryFixedSubmodule_isClosed π K).isComplete.completeSpace_coe

instance ejUnitaryFixedSubmodule_inf_completeSpace
    {G : Type u₂} {H : Type v₂} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K J : Subgroup G) :
    CompleteSpace
      (↑(ejUnitaryFixedSubmodule π K ⊓
        ejUnitaryFixedSubmodule π J : Submodule ℂ H) : Type v₂) :=
  (ejUnitaryFixedSubmodule_inf_isClosed π K J).isComplete.completeSpace_coe

end ThreeFiniteUnitaryFixedSpaces

end

namespace ErshovJaikinFiniteSpectral

open Filter Topology

universe u v

section FiniteUnitaryAveraging

variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finiteUnitarySubgroupAverage
    (π : UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K] (x : H) : H :=
  (Fintype.card K : ℂ)⁻¹ • ∑ k : K, π (k : G) x

theorem finiteUnitarySubgroupAverage_fixed
    (π : UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K] (x : H) (g : K) :
    π (g : G) (finiteUnitarySubgroupAverage π K x) =
      finiteUnitarySubgroupAverage π K x := by
  classical
  unfold finiteUnitarySubgroupAverage
  rw [map_smul, map_sum]
  congr 1
  calc
    (∑ k : K, π (g : G) (π (k : G) x)) =
        ∑ k : K, π ((g * k : K) : G) x := by
          apply Finset.sum_congr rfl
          intro k _
          simp only [Subgroup.coe_mul, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]
    _ = ∑ k : K, π (k : G) x :=
      Function.Bijective.sum_comp (Group.mulLeft_bijective g)
        (fun k : K => π (k : G) x)

theorem finiteUnitarySubgroupAverage_sub
    (π : UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K] (x : H) :
    finiteUnitarySubgroupAverage π K x - x =
      (Fintype.card K : ℂ)⁻¹ •
        ∑ k : K, (π (k : G) x - x) := by
  classical
  have hcard : (Fintype.card K : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold finiteUnitarySubgroupAverage
  rw [Finset.sum_sub_distrib, smul_sub]
  have hconst :
      (Fintype.card K : ℂ)⁻¹ • (∑ _k : K, x) = x := by
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ne_eq,
      hcard,
      not_false_eq_true, inv_mul_cancel₀, one_smul]
  rw [hconst]

theorem norm_finiteUnitarySubgroupAverage_sub_le
    (π : UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K] (x : H) :
    ‖finiteUnitarySubgroupAverage π K x - x‖ ≤
      (Fintype.card K : ℝ)⁻¹ *
        ∑ k : K, ‖π (k : G) x - x‖ := by
  classical
  rw [finiteUnitarySubgroupAverage_sub, norm_smul, norm_inv,
    Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left
    (norm_sum_le Finset.univ (fun k : K => π (k : G) x - x))
    (by positivity)

theorem norm_sub_starProjection_le_finiteUnitarySubgroupAverage
    (π : UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K]
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (x : H) (hmem : finiteUnitarySubgroupAverage π K x ∈ U) :
    ‖x - U.starProjection x‖ ≤
      ‖finiteUnitarySubgroupAverage π K x - x‖ := by
  rw [Submodule.starProjection_minimal]
  have hbound : BddBelow
      (Set.range fun z : U => ‖x - (z : H)‖) :=
    ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
  calc
    (⨅ z : U, ‖x - (z : H)‖) ≤
        ‖x - (⟨finiteUnitarySubgroupAverage π K x, hmem⟩ : U)‖ :=
      ciInf_le hbound _
    _ = ‖finiteUnitarySubgroupAverage π K x - x‖ :=
      norm_sub_rev _ _

end FiniteUnitaryAveraging

theorem hasPropertyT_of_geometric_finite_averaging
    {G : Type u} [Group G] (S : Finset G) (q : ℝ)
    (hq1 : q < 1)
    (haverage :
      ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] (π : UnitaryRepresentation G H),
        ∃ A : H →L[ℂ] H,
          (∀ (x : H) (n : ℕ),
            dist ((A : H → H)^[n] x)
                ((A : H → H)^[n + 1] x) ≤
              (∑ g ∈ S, ‖π g x - x‖) * q ^ n) ∧
          (∀ x : H, A x = x → ∀ g : G, π g x = x)) :
    HasPropertyT.{u, v} G := by
  classical
  let δ : ℝ := (1 - q) / (2 * (S.card + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    apply div_pos (sub_pos.mpr hq1)
    positivity
  refine ⟨⟨{
    generators := S
    kazhdanConstant := δ
    positive := hδ
    invariant := ?_
  }⟩⟩
  intro H _ _ _ π ξ hξ hsmall
  obtain ⟨A, hstep, hfixed⟩ := haverage H π
  let C : ℝ := ∑ g ∈ S, ‖π g ξ - ξ‖
  let f : ℕ → H := fun n => ((A : H → H)^[n]) ξ
  have hgeometric : ∀ n : ℕ,
      dist (f n) (f (n + 1)) ≤ C * q ^ n := by
    intro n
    exact hstep ξ n
  have hcauchy : CauchySeq f :=
    cauchySeq_of_le_geometric q C hq1 hgeometric
  obtain ⟨η, hηlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hηfixed : A η = η :=
    isFixedPt_of_tendsto_iterate hηlim A.continuous.continuousAt
  have hdist : dist ξ η ≤ C / (1 - q) := by
    simpa [f] using
      (dist_le_of_le_geometric_of_tendsto₀ q C hq1 hgeometric hηlim)
  have hsum : C ≤ S.card * δ := by
    dsimp [C]
    calc
      (∑ g ∈ S, ‖π g ξ - ξ‖) ≤ ∑ _g ∈ S, δ := by
        exact Finset.sum_le_sum fun g hg => (hsmall g hg).le
      _ = S.card * δ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hhalf : C < (1 - q) / 2 := by
    calc
      C ≤ S.card * δ := hsum
      _ < (1 - q) / 2 := by
        dsimp [δ]
        have hpos : 0 < (1 - q) := sub_pos.mpr hq1
        have hc : (S.card : ℝ) < (S.card : ℝ) + 1 := by linarith
        have hcpos : 0 < (S.card : ℝ) + 1 := by positivity
        rw [show (2 * (↑S.card + 1) : ℝ) =
          2 * ((S.card : ℝ) + 1) by norm_cast]
        calc
          (S.card : ℝ) *
              ((1 - q) / (2 * ((S.card : ℝ) + 1))) =
            ((1 - q) / 2) *
              ((S.card : ℝ) / ((S.card : ℝ) + 1)) := by
                field_simp
          _ < ((1 - q) / 2) * 1 := by
            apply mul_lt_mul_of_pos_left
              (div_lt_one hcpos |>.mpr hc)
            positivity
          _ = (1 - q) / 2 := mul_one _
  have hηne : η ≠ 0 := by
    intro hzero
    subst η
    have hone : dist ξ (0 : H) = 1 := by simpa only [dist_zero_right] using hξ
    rw [hone] at hdist
    have hden : 0 < 1 - q := sub_pos.mpr hq1
    have hlt : C / (1 - q) < 1 / 2 :=
      (div_lt_iff₀ hden).mpr (by nlinarith [hhalf])
    linarith
  exact ⟨η, hηne, hfixed η hηfixed⟩

def threeFiniteSubgroupGenerators
    {G : Type u} [Group G] (K : Fin 3 → Subgroup G)
    [∀ i, Fintype (K i)] : Finset G := by
  classical
  exact Finset.univ.biUnion fun i : Fin 3 =>
    Finset.univ.image fun g : K i => (g : G)

theorem mem_threeFiniteSubgroupGenerators
    {G : Type u} [Group G] (K : Fin 3 → Subgroup G)
    [∀ i, Fintype (K i)] (g : G) :
    g ∈ threeFiniteSubgroupGenerators K ↔ ∃ i : Fin 3, g ∈ K i := by
  classical
  simp only [threeFiniteSubgroupGenerators, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
    true_and,
    Subtype.exists, exists_prop, exists_eq_right]

def unitaryVectorStabilizer
    {G : Type u} {H : Type v} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H)
    (x : H) : Subgroup G where
  carrier := {g : G | π g x = x}
  one_mem' := by simp only [Set.mem_ofPred_eq, map_one, LinearIsometryEquiv.coe_one, id_eq]
  mul_mem' := by
    intro g h hg hh
    change π g x = x at hg
    change π h x = x at hh
    change π (g * h) x = x
    simpa only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hh] using hg
  inv_mem' := by
    intro g hg
    change π g x = x at hg
    change π g⁻¹ x = x
    have h := congrArg (fun z : H => π g⁻¹ z) hg
    simpa only [map_inv, LinearIsometryEquiv.coe_inv, LinearIsometryEquiv.symm_apply_apply] using
      h.symm

theorem hasPropertyT_of_three_finite_subgroups_geometric
    {G : Type u} [Group G]
    (K : Fin 3 → Subgroup G) [∀ i, Fintype (K i)]
    (hgen : (⨆ i : Fin 3, K i) = ⊤)
    (q : ℝ) (hq : q < 1)
    (haverage :
      ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] (π : UnitaryRepresentation G H),
        ∃ A : H →L[ℂ] H,
          (∀ (x : H) (n : ℕ),
            dist ((A : H → H)^[n] x)
                ((A : H → H)^[n + 1] x) ≤
              (∑ g ∈ threeFiniteSubgroupGenerators K,
                ‖π g x - x‖) * q ^ n) ∧
          (∀ x : H, A x = x →
            ∀ (i : Fin 3) (g : K i), π (g : G) x = x)) :
    HasPropertyT.{u, v} G := by
  apply hasPropertyT_of_geometric_finite_averaging
    (threeFiniteSubgroupGenerators K) q hq
  intro H _ _ _ π
  obtain ⟨A, hstep, hfixed⟩ := haverage H π
  refine ⟨A, hstep, ?_⟩
  intro x hx g
  have hK : ∀ i : Fin 3,
      K i ≤ unitaryVectorStabilizer π x := by
    intro i k hk
    exact hfixed x hx i ⟨k, hk⟩
  have htop : (⊤ : Subgroup G) ≤ unitaryVectorStabilizer π x := by
    rw [← hgen]
    exact iSup_le hK
  exact htop (show g ∈ (⊤ : Subgroup G) from Subgroup.mem_top g)

theorem inv_sqrt_eight_pos : 0 < (Real.sqrt (8 : ℝ))⁻¹ := by
  positivity

theorem inv_sqrt_eight_lt_one_half :
    (Real.sqrt (8 : ℝ))⁻¹ < (1 / 2 : ℝ) := by
  have hsqrt : 2 < Real.sqrt (8 : ℝ) := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
    have hnonneg := Real.sqrt_nonneg (8 : ℝ)
    nlinarith
  simpa only [one_div, gt_iff_lt] using (one_div_lt_one_div_of_lt (show (0 : ℝ) < 2 by norm_num)
    hsqrt)

theorem norm_inner_le_inv_sqrt_eight_of_sq
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b : H)
    (h : 8 * ‖inner ℂ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2) :
    ‖inner ℂ a b‖ ≤
      (Real.sqrt (8 : ℝ))⁻¹ * ‖a‖ * ‖b‖ := by
  have hsqrt : 0 < Real.sqrt (8 : ℝ) := by positivity
  have hsquare : Real.sqrt (8 : ℝ) ^ 2 = 8 :=
    Real.sq_sqrt (by norm_num)
  have hsq :
      ‖inner ℂ a b‖ ^ 2 ≤
        ((Real.sqrt (8 : ℝ))⁻¹ * ‖a‖ * ‖b‖) ^ 2 := by
    calc
      ‖inner ℂ a b‖ ^ 2 ≤
          (‖a‖ ^ 2 * ‖b‖ ^ 2) / 8 := by
            apply (le_div_iff₀ (show (0 : ℝ) < 8 by norm_num)).mpr
            nlinarith
      _ = ((Real.sqrt (8 : ℝ))⁻¹ * ‖a‖ * ‖b‖) ^ 2 := by
        field_simp
        nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

theorem hasPropertyT_of_three_finite_subgroups_friedrichs_angle
    {G : Type u} [Group G]
    (K : Fin 3 → Subgroup G) [∀ i, Finite (K i)]
    (hgen : (⨆ i : Fin 3, K i) = ⊤)
    (c : ℝ) (hc : 0 ≤ c) (hchalf : c < (1 / 2 : ℝ))
    (hangle :
      ∀ (H : Type v) [NormedAddCommGroup H]
        [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : UnitaryRepresentation G H)
        (i j : Fin 3), i ≠ j →
        ∀ (a b : H),
          a ∈ ejUnitaryFixedSubmodule π (K i) →
          a ∈ (ejUnitaryFixedSubmodule π (K i) ⊓
            ejUnitaryFixedSubmodule π (K j))ᗮ →
          b ∈ ejUnitaryFixedSubmodule π (K j) →
          b ∈ (ejUnitaryFixedSubmodule π (K i) ⊓
            ejUnitaryFixedSubmodule π (K j))ᗮ →
            ‖inner ℂ a b‖ ≤ c * ‖a‖ * ‖b‖) :
    HasPropertyT.{u, v} G := by
  classical
  let : ∀ i, Fintype (K i) := fun i => Fintype.ofFinite (K i)
  let q : ℝ := 1 - (1 - 2 * c) / 6
  have hq : q < 1 := by
    dsimp [q]
    linarith
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    linarith
  apply hasPropertyT_of_three_finite_subgroups_geometric K hgen q hq
  intro H _ _ _ π
  let V : Fin 3 → Submodule ℂ H :=
    fun i => ejUnitaryFixedSubmodule π (K i)
  let : ∀ i : Fin 3, (V i).HasOrthogonalProjection := fun i => by
    dsimp [V]
    infer_instance
  let : ∀ i j : Fin 3,
      (V i ⊓ V j).HasOrthogonalProjection := fun i j => by
    dsimp [V]
    infer_instance
  refine ⟨ejThreeProjectionAverage V, ?_, ?_⟩
  · intro x n
    let T : ℝ := ∑ g ∈ threeFiniteSubgroupGenerators K,
      ‖π g x - x‖
    have hT : 0 ≤ T := by
      dsimp [T]
      positivity
    have hpoint (i : Fin 3) (k : K i) :
        ‖π (k : G) x - x‖ ≤ T := by
      dsimp [T]
      exact Finset.single_le_sum
        (s := threeFiniteSubgroupGenerators K)
        (f := fun g : G => ‖π g x - x‖)
        (fun g _ => norm_nonneg _)
        ((mem_threeFiniteSubgroupGenerators K (k : G)).mpr
          ⟨i, k.property⟩)
    have havgbound (i : Fin 3) :
        ‖finiteUnitarySubgroupAverage π (K i) x - x‖ ≤ T := by
      calc
        ‖finiteUnitarySubgroupAverage π (K i) x - x‖ ≤
            (Fintype.card (K i) : ℝ)⁻¹ *
              ∑ k : K i, ‖π (k : G) x - x‖ :=
          norm_finiteUnitarySubgroupAverage_sub_le π (K i) x
        _ ≤ (Fintype.card (K i) : ℝ)⁻¹ *
              ∑ _k : K i, T := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.sum_le_sum fun k _ => hpoint i k
          · positivity
        _ = T := by
          have hcard : (Fintype.card (K i) : ℝ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ne_eq, hcard,
            not_false_eq_true,
            inv_mul_cancel_left₀]
    have hres (i : Fin 3) :
        ‖ejResidualProjection (V i) x‖ ≤ T := by
      rw [ejResidualProjection_apply]
      apply le_trans
        (norm_sub_starProjection_le_finiteUnitarySubgroupAverage
          π (K i) (V i) x ?_)
        (havgbound i)
      exact (mem_ejUnitaryFixedSubmodule π (K i) _).mpr
        (finiteUnitarySubgroupAverage_fixed π (K i) x)
    have hfullangle : ∀ (i j : Fin 3) (a b : H),
        a ∈ V i → a ∈ (V i ⊓ V j)ᗮ →
        b ∈ V j → b ∈ (V i ⊓ V j)ᗮ →
          ‖inner ℂ a b‖ ≤ c * ‖a‖ * ‖b‖ := by
      intro i j a b ha haorth hb hborth
      by_cases hij : i = j
      · subst j
        have hazero : a = 0 :=
          inner_self_eq_zero.mp (haorth a ⟨ha, ha⟩)
        simp only [hazero, inner_zero_left, norm_zero, mul_zero, zero_mul, Std.le_refl]
      · exact hangle H π i j hij a b ha haorth hb hborth
    calc
      dist (((ejThreeProjectionAverage V : H → H)^[n]) x)
          (((ejThreeProjectionAverage V : H → H)^[n + 1]) x)
          ≤ Real.sqrt (ejThreeResidualEnergy V x / 3) *
              (1 - (1 - 2 * c) / 6) ^ n :=
        ejThreeProjectionAverage_iterate_dist_le_of_pair_angles
          V c hc hchalf hfullangle x n
      _ ≤ T * q ^ n := by
        change Real.sqrt (ejThreeResidualEnergy V x / 3) *
          q ^ n ≤ T * q ^ n
        exact mul_le_mul_of_nonneg_right
          (ejThreeResidualEnergy_sqrt_div_three_le
            V x T hT hres)
          (pow_nonneg hqnonneg n)
      _ = (∑ g ∈ threeFiniteSubgroupGenerators K,
            ‖π g x - x‖) * q ^ n := by
        rfl
  · intro x hx i k
    have hxmem : x ∈ V i :=
      ejThreeProjectionAverage_fixed_mem V x hx i
    exact (mem_ejUnitaryFixedSubmodule π (K i) x).mp
      hxmem k

end ErshovJaikinFiniteSpectral

section

open scoped BigOperators commutatorElement

abbrev finiteBlockGaloisField : Type := GaloisField 2 3

def finiteBlockGaloisBasis :
    Module.Basis (Fin 3) (ZMod 2) finiteBlockGaloisField :=
  Module.finBasisOfFinrankEq (ZMod 2) finiteBlockGaloisField
    (GaloisField.finrank 2 (by decide))

def finiteBlockGaloisMatrix :
    finiteBlockGaloisField →ₐ[ZMod 2]
      Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Algebra.leftMulMatrix finiteBlockGaloisBasis

theorem finiteBlockGaloisField_natCard :
    Nat.card finiteBlockGaloisField = 8 := by
  simpa only [Nat.reducePow] using (GaloisField.card 2 3 (by decide))

def finiteBlockGaloisMatrixOver (R : Type*) [Ring R]
    [Algebra (ZMod 2) R] :
    finiteBlockGaloisField →+* Matrix (Fin 3) (Fin 3) R :=
  (RingHom.mapMatrix (algebraMap (ZMod 2) R)).comp
    finiteBlockGaloisMatrix.toRingHom

section ActualBlockRoots

variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]

theorem finiteBlockCoefficientMatrix_mul_binary_mem
    (W : Submodule (ZMod 2) R)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i j, A i j ∈ W)
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    ∀ i j,
      (A * RingHom.mapMatrix (algebraMap (ZMod 2) R) B) i j ∈ W := by
  intro i j
  rw [Matrix.mul_apply]
  apply Submodule.sum_mem
  intro k _
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [← Algebra.commutes, ← Algebra.smul_def]
  exact W.smul_mem (B k j) (hA i k)

theorem finiteBlockCoefficientMatrix_binary_mul_mem
    (W : Submodule (ZMod 2) R)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i j, A i j ∈ W)
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    ∀ i j,
      (RingHom.mapMatrix (algebraMap (ZMod 2) R) B * A) i j ∈ W := by
  intro i j
  rw [Matrix.mul_apply]
  apply Submodule.sum_mem
  intro k _
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← Algebra.smul_def]
  exact W.smul_mem (B i k) (hA k j)

theorem finiteBlockCoefficientMatrix_mul_galois_mem
    (W : Submodule (ZMod 2) R)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i j, A i j ∈ W)
    (t : finiteBlockGaloisField) :
    ∀ i j, (A * finiteBlockGaloisMatrixOver R t) i j ∈ W := by
  change ∀ i j,
    (A * RingHom.mapMatrix (algebraMap (ZMod 2) R)
      (finiteBlockGaloisMatrix t)) i j ∈ W
  exact finiteBlockCoefficientMatrix_mul_binary_mem W A hA
    (finiteBlockGaloisMatrix t)

theorem finiteBlockCoefficientMatrix_galois_mul_mem
    (W : Submodule (ZMod 2) R)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i j, A i j ∈ W)
    (t : finiteBlockGaloisField) :
    ∀ i j, (finiteBlockGaloisMatrixOver R t * A) i j ∈ W := by
  change ∀ i j,
    (RingHom.mapMatrix (algebraMap (ZMod 2) R)
      (finiteBlockGaloisMatrix t) * A) i j ∈ W
  exact finiteBlockCoefficientMatrix_binary_mul_mem W A hA
    (finiteBlockGaloisMatrix t)

def finiteBlockCoefficientMatrixHom
    (W : Submodule (ZMod 2) R) :
    Matrix (Fin 3) (Fin 3) W →+
      Matrix (Fin 3) (Fin 3) R :=
  W.subtype.toAddMonoidHom.mapMatrix

def finiteOuterBlockRootHom
    (W : Submodule (ZMod 2) R) (i j : Fin 3) (hij : i ≠ j) :
    Multiplicative (Matrix (Fin 3) (Fin 3) W) →*
      elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
  (elementaryRootHom (R := Matrix (Fin 3) (Fin 3) R) i j hij).comp
    (finiteBlockCoefficientMatrixHom W).toMultiplicative

def finiteOuterBlockRootSubgroup
    (W : Submodule (ZMod 2) R) (i j : Fin 3) (hij : i ≠ j) :
    Subgroup (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) :=
  (finiteOuterBlockRootHom W i j hij).range

theorem finite_finiteOuterBlockRootSubgroup
    (W : Submodule (ZMod 2) R) [Finite W]
    (i j : Fin 3) (hij : i ≠ j) :
    Finite (finiteOuterBlockRootSubgroup W i j hij) := by
  let f : Multiplicative (Matrix (Fin 3) (Fin 3) W) →
      finiteOuterBlockRootSubgroup W i j hij :=
    fun x => ⟨finiteOuterBlockRootHom W i j hij x, ⟨x, rfl⟩⟩
  apply Finite.of_surjective f
  intro x
  obtain ⟨a, ha⟩ := x.property
  exact ⟨a, Subtype.ext ha⟩

omit [Algebra (ZMod 2) R] in
theorem finiteOuterElementaryRoot_commutator
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (A B : Matrix (Fin 3) (Fin 3) R) :
    ⁅elementaryRootHom i j hij (Multiplicative.ofAdd A),
      elementaryRootHom j k hjk (Multiplicative.ofAdd B)⁆ =
      elementaryRootHom i k hik (Multiplicative.ofAdd (A * B)) := by
  apply Subtype.ext
  exact elementaryUnit_commutator i j k hij hjk hik A B

omit [Algebra (ZMod 2) R] in
theorem finiteOuterElementaryRoot_conjugate_by_successor
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (A B : Matrix (Fin 3) (Fin 3) R) :
    let x := elementaryRootHom i j hij (Multiplicative.ofAdd A)
    let y := elementaryRootHom j k hjk (Multiplicative.ofAdd B)
    let z := elementaryRootHom i k hik (Multiplicative.ofAdd (A * B))
    y * x * y⁻¹ = z⁻¹ * x := by
  dsimp
  rw [← finiteOuterElementaryRoot_commutator i j k hij hjk hik A B]
  simp only [commutatorElement_def]
  group

omit [Algebra (ZMod 2) R] in
theorem finiteOuterElementaryUnit_commute_of_nonadjacent
    (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (A B : Matrix (Fin 3) (Fin 3) R) :
    Commute (elementaryUnit i j hij A) (elementaryUnit k l hkl B) := by
  apply Units.ext
  change
    (1 + Matrix.single i j A) * (1 + Matrix.single k l B) =
      (1 + Matrix.single k l B) * (1 + Matrix.single i j A)
  have hAB : Matrix.single i j A * Matrix.single k l B = 0 :=
    Matrix.single_mul_single_of_ne (c := A) i j k hjk B
  have hBA : Matrix.single k l B * Matrix.single i j A = 0 :=
    Matrix.single_mul_single_of_ne (c := B) k l i hli A
  noncomm_ring [hAB, hBA]

omit [Algebra (ZMod 2) R] in
theorem finiteOuterElementaryRoot_commute_of_nonadjacent
    (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (A B : Matrix (Fin 3) (Fin 3) R) :
    Commute
      (elementaryRootHom i j hij (Multiplicative.ofAdd A))
      (elementaryRootHom k l hkl (Multiplicative.ofAdd B)) := by
  apply Subtype.ext
  exact (finiteOuterElementaryUnit_commute_of_nonadjacent
    i j k l hij hkl hjk hli A B).eq

omit [Algebra (ZMod 2) R] in
theorem finiteOuterElementaryRoot_commute_same
    (i j : Fin 3) (hij : i ≠ j)
    (A B : Matrix (Fin 3) (Fin 3) R) :
    Commute
      (elementaryRootHom i j hij (Multiplicative.ofAdd A))
      (elementaryRootHom i j hij (Multiplicative.ofAdd B)) := by
  change
    elementaryRootHom i j hij (Multiplicative.ofAdd A) *
      elementaryRootHom i j hij (Multiplicative.ofAdd B) =
    elementaryRootHom i j hij (Multiplicative.ofAdd B) *
      elementaryRootHom i j hij (Multiplicative.ofAdd A)
  calc
    _ = elementaryRootHom i j hij
        (Multiplicative.ofAdd A * Multiplicative.ofAdd B) :=
      (map_mul (elementaryRootHom i j hij)
        (Multiplicative.ofAdd A) (Multiplicative.ofAdd B)).symm
    _ = elementaryRootHom i j hij
        (Multiplicative.ofAdd B * Multiplicative.ofAdd A) := by
      rw [mul_comm]
    _ = _ := map_mul (elementaryRootHom i j hij)
      (Multiplicative.ofAdd B) (Multiplicative.ofAdd A)

def finiteBlockCoefficientMatrixRightMul
    (W : Submodule (ZMod 2) R)
    (B : Matrix (Fin 3) (Fin 3) W) :
    Matrix (Fin 3) (Fin 3) W →+
      Matrix (Fin 3) (Fin 3) R where
  toFun A :=
    finiteBlockCoefficientMatrixHom W A *
      finiteBlockCoefficientMatrixHom W B
  map_zero' := by simp only [map_zero, zero_mul]
  map_add' A C := by simp only [map_add, add_mul]

def finiteOuterBlockProductCentralRootHom
    (W : Submodule (ZMod 2) R)
    (i k : Fin 3) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W) :
    Multiplicative (Matrix (Fin 3) (Fin 3) W) →*
      elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
  (elementaryRootHom
    (R := Matrix (Fin 3) (Fin 3) R) i k hik).comp
      (finiteBlockCoefficientMatrixRightMul W B).toMultiplicative

def finiteOuterBlockProductCentralRootSubgroup
    (W : Submodule (ZMod 2) R)
    (i k : Fin 3) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W) :
    Subgroup (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) :=
  (finiteOuterBlockProductCentralRootHom W i k hik B).range

theorem finiteOuterBlockRoot_commutator_mem_productCentral
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (A B : Matrix (Fin 3) (Fin 3) W) :
    ⁅finiteOuterBlockRootHom W i j hij (Multiplicative.ofAdd A),
      finiteOuterBlockRootHom W j k hjk (Multiplicative.ofAdd B)⁆ ∈
      finiteOuterBlockProductCentralRootSubgroup W i k hik B := by
  refine ⟨Multiplicative.ofAdd A, ?_⟩
  change
    elementaryRootHom i k hik
      (Multiplicative.ofAdd
        (finiteBlockCoefficientMatrixHom W A *
          finiteBlockCoefficientMatrixHom W B)) =
      ⁅elementaryRootHom i j hij
        (Multiplicative.ofAdd (finiteBlockCoefficientMatrixHom W A)),
       elementaryRootHom j k hjk
        (Multiplicative.ofAdd (finiteBlockCoefficientMatrixHom W B))⁆
  exact (finiteOuterElementaryRoot_commutator i j k hij hjk hik
    (finiteBlockCoefficientMatrixHom W A)
    (finiteBlockCoefficientMatrixHom W B)).symm

theorem finiteOuterBlockRoot_commutator_exists_productCentral
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x y : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
    (hx : x ∈ finiteOuterBlockRootSubgroup W i j hij)
    (hy : y ∈ finiteOuterBlockRootSubgroup W j k hjk) :
    ∃ B : Matrix (Fin 3) (Fin 3) W,
      ⁅x, y⁆ ∈ finiteOuterBlockProductCentralRootSubgroup W i k hik B := by
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := hy
  exact ⟨B.toAdd,
    finiteOuterBlockRoot_commutator_mem_productCentral
      W i j k hij hjk hik A.toAdd B.toAdd⟩

theorem finiteOuterBlockProductCentralRoot_commute_left
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (x z : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
    (hx : x ∈ finiteOuterBlockRootSubgroup W i j hij)
    (hz : z ∈ finiteOuterBlockProductCentralRootSubgroup W i k hik B) :
    Commute x z := by
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨C, rfl⟩ := hz
  exact finiteOuterElementaryRoot_commute_of_nonadjacent
    i j i k hij hik hij.symm hik.symm
    (finiteBlockCoefficientMatrixHom W A.toAdd)
    (finiteBlockCoefficientMatrixRightMul W B C.toAdd)

theorem finiteOuterBlockProductCentralRoot_commute_right
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hjk : j ≠ k) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (y z : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
    (hy : y ∈ finiteOuterBlockRootSubgroup W j k hjk)
    (hz : z ∈ finiteOuterBlockProductCentralRootSubgroup W i k hik B) :
    Commute y z := by
  obtain ⟨A, rfl⟩ := hy
  obtain ⟨C, rfl⟩ := hz
  exact finiteOuterElementaryRoot_commute_of_nonadjacent
    j k i k hjk hik hik.symm hjk.symm
    (finiteBlockCoefficientMatrixHom W A.toAdd)
    (finiteBlockCoefficientMatrixRightMul W B C.toAdd)

theorem finiteOuterBlockProductCentralRoot_pair_le_centralizer
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W) :
    finiteOuterBlockRootSubgroup W i j hij ⊔
      finiteOuterBlockRootSubgroup W j k hjk ≤
      Subgroup.centralizer
        (finiteOuterBlockProductCentralRootSubgroup W i k hik B :
          Set (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))) := by
  apply sup_le
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (finiteOuterBlockProductCentralRoot_commute_left
      W i j k hij hik B x z hx hz).symm.eq
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (finiteOuterBlockProductCentralRoot_commute_right
      W i j k hjk hik B y z hy hz).symm.eq

theorem finiteOuterBlockProductCentralRoots_commute
    (W : Submodule (ZMod 2) R)
    (i k : Fin 3) (hik : i ≠ k)
    (B C : Matrix (Fin 3) (Fin 3) W)
    (z w : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
    (hz : z ∈ finiteOuterBlockProductCentralRootSubgroup W i k hik B)
    (hw : w ∈ finiteOuterBlockProductCentralRootSubgroup W i k hik C) :
    Commute z w := by
  obtain ⟨A, rfl⟩ := hz
  obtain ⟨D, rfl⟩ := hw
  exact finiteOuterElementaryRoot_commute_same i k hik
    (finiteBlockCoefficientMatrixRightMul W B A.toAdd)
    (finiteBlockCoefficientMatrixRightMul W C D.toAdd)

def finiteBlockGaloisLeftProductCoefficientMatrix
    (W : Submodule (ZMod 2) R)
    (B : Matrix (Fin 3) (Fin 3) W)
    (t : finiteBlockGaloisField) :
    Matrix (Fin 3) (Fin 3) W :=
  fun p q =>
    ⟨(finiteBlockGaloisMatrixOver R t *
        finiteBlockCoefficientMatrixHom W B) p q,
      finiteBlockCoefficientMatrix_galois_mul_mem W
        (finiteBlockCoefficientMatrixHom W B)
        (fun i j => (B i j).property) t p q⟩

theorem finiteBlockCoefficientMatrixHom_galoisLeftProduct
    (W : Submodule (ZMod 2) R)
    (B : Matrix (Fin 3) (Fin 3) W)
    (t : finiteBlockGaloisField) :
    finiteBlockCoefficientMatrixHom W
      (finiteBlockGaloisLeftProductCoefficientMatrix W B t) =
      finiteBlockGaloisMatrixOver R t *
        finiteBlockCoefficientMatrixHom W B := by
  ext p q
  rfl

def finiteOuterBlockGaloisConjugatorWithCoefficient
    (W : Submodule (ZMod 2) R)
    (j k : Fin 3) (hjk : j ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (t : finiteBlockGaloisField) :
    elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
  elementaryRootHom j k hjk
    (Multiplicative.ofAdd
      (finiteBlockGaloisMatrixOver R t *
        finiteBlockCoefficientMatrixHom W B))

theorem finiteOuterBlockGaloisConjugatorWithCoefficient_mem
    (W : Submodule (ZMod 2) R)
    (j k : Fin 3) (hjk : j ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (t : finiteBlockGaloisField) :
    finiteOuterBlockGaloisConjugatorWithCoefficient W j k hjk B t ∈
      finiteOuterBlockRootSubgroup W j k hjk := by
  refine ⟨Multiplicative.ofAdd
    (finiteBlockGaloisLeftProductCoefficientMatrix W B t), ?_⟩
  change
    elementaryRootHom j k hjk
      (Multiplicative.ofAdd
        (finiteBlockCoefficientMatrixHom W
          (finiteBlockGaloisLeftProductCoefficientMatrix W B t))) =
      elementaryRootHom j k hjk
        (Multiplicative.ofAdd
          (finiteBlockGaloisMatrixOver R t *
            finiteBlockCoefficientMatrixHom W B))
  rw [finiteBlockCoefficientMatrixHom_galoisLeftProduct]

def finiteOuterBlockGaloisConjugateRootWithCoefficient
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (t : finiteBlockGaloisField) :
    Subgroup (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) :=
  (finiteOuterBlockRootSubgroup W i j hij).map
    (MulAut.conj
      (finiteOuterBlockGaloisConjugatorWithCoefficient
        W j k hjk B t)).toMonoidHom

omit [Algebra (ZMod 2) R] in
theorem finiteOuterElementaryRootConjugates_commute
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (A C P Q : Matrix (Fin 3) (Fin 3) R) :
    Commute
      (MulAut.conj
        (elementaryRootHom j k hjk (Multiplicative.ofAdd P))
        (elementaryRootHom i j hij (Multiplicative.ofAdd A)))
      (MulAut.conj
        (elementaryRootHom j k hjk (Multiplicative.ofAdd Q))
        (elementaryRootHom i j hij (Multiplicative.ofAdd C))) := by
  rw [MulAut.conj_apply, MulAut.conj_apply,
    finiteOuterElementaryRoot_conjugate_by_successor
      i j k hij hjk hik A P,
    finiteOuterElementaryRoot_conjugate_by_successor
      i j k hij hjk hik C Q]
  have hzz := finiteOuterElementaryRoot_commute_same
    i k hik (A * P) (C * Q)
  have hzx := finiteOuterElementaryRoot_commute_of_nonadjacent
    i k i j hik hij hik.symm hij.symm (A * P) C
  have hxz := finiteOuterElementaryRoot_commute_of_nonadjacent
    i j i k hij hik hij.symm hik.symm A (C * Q)
  have hxx := finiteOuterElementaryRoot_commute_same i j hij A C
  exact (hzz.inv_inv.mul_right hzx.inv_left).mul_left
    (hxz.inv_right.mul_right hxx)

theorem finiteOuterBlockGaloisConjugateRootsWithCoefficient_commute
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (s t : finiteBlockGaloisField)
    (x y : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
    (hx : x ∈ finiteOuterBlockGaloisConjugateRootWithCoefficient
      W i j k hij hjk B s)
    (hy : y ∈ finiteOuterBlockGaloisConjugateRootWithCoefficient
      W i j k hij hjk B t) :
    Commute x y := by
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨C, rfl⟩, rfl⟩ := hy
  exact finiteOuterElementaryRootConjugates_commute
    i j k hij hjk hik
    (finiteBlockCoefficientMatrixHom W A.toAdd)
    (finiteBlockCoefficientMatrixHom W C.toAdd)
    (finiteBlockGaloisMatrixOver R s *
      finiteBlockCoefficientMatrixHom W B)
    (finiteBlockGaloisMatrixOver R t *
      finiteBlockCoefficientMatrixHom W B)

def finiteBlockGaloisRightInverseCoefficientMatrix
    (W : Submodule (ZMod 2) R)
    (A : Matrix (Fin 3) (Fin 3) W)
    (s t : finiteBlockGaloisField) :
    Matrix (Fin 3) (Fin 3) W :=
  fun p q =>
    ⟨(finiteBlockCoefficientMatrixHom W A *
        finiteBlockGaloisMatrixOver R (t - s)⁻¹) p q,
      finiteBlockCoefficientMatrix_mul_galois_mem W
        (finiteBlockCoefficientMatrixHom W A)
        (fun i j => (A i j).property) (t - s)⁻¹ p q⟩

theorem finiteBlockCoefficientMatrixHom_galoisRightInverse
    (W : Submodule (ZMod 2) R)
    (A : Matrix (Fin 3) (Fin 3) W)
    (s t : finiteBlockGaloisField) :
    finiteBlockCoefficientMatrixHom W
      (finiteBlockGaloisRightInverseCoefficientMatrix W A s t) =
      finiteBlockCoefficientMatrixHom W A *
        finiteBlockGaloisMatrixOver R (t - s)⁻¹ := by
  ext p q
  rfl

theorem finiteBlockGalois_right_inverse_difference
    (s t : finiteBlockGaloisField) (hst : s ≠ t)
    (C : Matrix (Fin 3) (Fin 3) R) :
    (C * finiteBlockGaloisMatrixOver R (t - s)⁻¹) *
        finiteBlockGaloisMatrixOver R t -
      (C * finiteBlockGaloisMatrixOver R (t - s)⁻¹) *
        finiteBlockGaloisMatrixOver R s = C := by
  rw [← mul_sub, ← map_sub, mul_assoc, ← map_mul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hst.symm), map_one, mul_one]

theorem finiteOuterBlockProductCentralRoot_le_galoisConjugates
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (s t : finiteBlockGaloisField) (hst : s ≠ t) :
    finiteOuterBlockProductCentralRootSubgroup W i k hik B ≤
      finiteOuterBlockGaloisConjugateRootWithCoefficient
          W i j k hij hjk B s ⊔
        finiteOuterBlockGaloisConjugateRootWithCoefficient
          W i j k hij hjk B t := by
  intro z hz
  obtain ⟨A, rfl⟩ := hz
  let D : Matrix (Fin 3) (Fin 3) W :=
    finiteBlockGaloisRightInverseCoefficientMatrix W A.toAdd s t
  let x : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
    finiteOuterBlockRootHom W i j hij (Multiplicative.ofAdd D)
  let ys : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
    finiteOuterBlockGaloisConjugatorWithCoefficient W j k hjk B s
  let yt : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
    finiteOuterBlockGaloisConjugatorWithCoefficient W j k hjk B t
  let J : Subgroup (elementaryGroup (Fin 3)
      (Matrix (Fin 3) (Fin 3) R)) :=
    finiteOuterBlockGaloisConjugateRootWithCoefficient
        W i j k hij hjk B s ⊔
      finiteOuterBlockGaloisConjugateRootWithCoefficient
        W i j k hij hjk B t
  have hx : x ∈ finiteOuterBlockRootSubgroup W i j hij :=
    ⟨Multiplicative.ofAdd D, rfl⟩
  have hs : MulAut.conj ys x ∈
      finiteOuterBlockGaloisConjugateRootWithCoefficient
        W i j k hij hjk B s :=
    ⟨x, hx, rfl⟩
  have ht : MulAut.conj yt x ∈
      finiteOuterBlockGaloisConjugateRootWithCoefficient
        W i j k hij hjk B t :=
    ⟨x, hx, rfl⟩
  have hprod : MulAut.conj ys x * (MulAut.conj yt x)⁻¹ ∈ J :=
    J.mul_mem (Subgroup.mem_sup_left hs)
      (J.inv_mem (Subgroup.mem_sup_right ht))
  let C₀ : Matrix (Fin 3) (Fin 3) R :=
    finiteBlockCoefficientMatrixHom W A.toAdd
  let B₀ : Matrix (Fin 3) (Fin 3) R :=
    finiteBlockCoefficientMatrixHom W B
  let D₀ : Matrix (Fin 3) (Fin 3) R :=
    finiteBlockCoefficientMatrixHom W D
  let P : Matrix (Fin 3) (Fin 3) R :=
    finiteBlockGaloisMatrixOver R s * B₀
  let Q : Matrix (Fin 3) (Fin 3) R :=
    finiteBlockGaloisMatrixOver R t * B₀
  have hD : D₀ = C₀ * finiteBlockGaloisMatrixOver R (t - s)⁻¹ :=
    finiteBlockCoefficientMatrixHom_galoisRightInverse W A.toAdd s t
  have hdiff : - (D₀ * P) + D₀ * Q = C₀ * B₀ := by
    calc
      - (D₀ * P) + D₀ * Q =
          (D₀ * finiteBlockGaloisMatrixOver R t -
            D₀ * finiteBlockGaloisMatrixOver R s) * B₀ := by
        dsimp [P, Q]
        noncomm_ring
      _ = C₀ * B₀ := by
        rw [hD, finiteBlockGalois_right_inverse_difference s t hst C₀]
  have hroot :
      (elementaryRootHom i k hik (Multiplicative.ofAdd (D₀ * P)))⁻¹ *
        elementaryRootHom i k hik (Multiplicative.ofAdd (D₀ * Q)) =
      finiteOuterBlockProductCentralRootHom W i k hik B A := by
    calc
      _ = elementaryRootHom i k hik
          ((Multiplicative.ofAdd (D₀ * P))⁻¹ *
            Multiplicative.ofAdd (D₀ * Q)) := by
        simp only [map_mul, map_inv]
      _ = elementaryRootHom i k hik
          (Multiplicative.ofAdd (C₀ * B₀)) := by
        congr 1
      _ = finiteOuterBlockProductCentralRootHom W i k hik B A := by
        rfl
  change
    MulAut.conj
        (elementaryRootHom j k hjk (Multiplicative.ofAdd P))
        (elementaryRootHom i j hij (Multiplicative.ofAdd D₀)) *
      (MulAut.conj
        (elementaryRootHom j k hjk (Multiplicative.ofAdd Q))
        (elementaryRootHom i j hij (Multiplicative.ofAdd D₀)))⁻¹ ∈ J
    at hprod
  simp only [MulAut.conj_apply] at hprod
  rw [finiteOuterElementaryRoot_conjugate_by_successor
        i j k hij hjk hik D₀ P,
      finiteOuterElementaryRoot_conjugate_by_successor
        i j k hij hjk hik D₀ Q] at hprod
  have hcancel :
      ((elementaryRootHom i k hik (Multiplicative.ofAdd (D₀ * P)))⁻¹ *
        elementaryRootHom i j hij (Multiplicative.ofAdd D₀)) *
        ((elementaryRootHom i k hik (Multiplicative.ofAdd (D₀ * Q)))⁻¹ *
          elementaryRootHom i j hij (Multiplicative.ofAdd D₀))⁻¹ =
      (elementaryRootHom i k hik (Multiplicative.ofAdd (D₀ * P)))⁻¹ *
        elementaryRootHom i k hik (Multiplicative.ofAdd (D₀ * Q)) := by
    group
  rw [hcancel, hroot] at hprod
  exact hprod

end ActualBlockRoots

universe u₁ v₁

def UnitaryRepresentation.toRepresentation
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) : Representation ℂ G H where
  toFun g := (π g).toLinearEquiv.toLinearMap
  map_one' := by
    ext x
    simp only [map_one, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.coe_one,
      id_eq, Module.End.one_apply]
  map_mul' g h := by
    ext x
    simp only [map_mul, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.coe_mul,
      Function.comp_apply, Module.End.mul_apply]

def unitaryFixedSubmodule
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) : Submodule ℂ H :=
  Representation.invariants (π.toRepresentation.comp K.subtype)

@[simp] theorem mem_unitaryFixedSubmodule
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) (x : H) :
    x ∈ unitaryFixedSubmodule π K ↔ ∀ g : K, π (g : G) x = x :=
  Iff.rfl

def unitaryVectorStabilizer
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (x : H) : Subgroup G where
  carrier := {g : G | π g x = x}
  one_mem' := by simp only [Set.mem_ofPred_eq, map_one, LinearIsometryEquiv.coe_one, id_eq]
  mul_mem' := by
    intro g h hg hh
    change π g x = x at hg
    change π h x = x at hh
    change π (g * h) x = x
    simpa only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hh] using hg
  inv_mem' := by
    intro g hg
    change π g x = x at hg
    change π g⁻¹ x = x
    have heq := congrArg (fun y : H => π g⁻¹ y) hg
    simpa only [map_inv, LinearIsometryEquiv.coe_inv, LinearIsometryEquiv.symm_apply_apply] using
      heq.symm

theorem unitaryFixedSubmodule_sup
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K J : Subgroup G) :
    unitaryFixedSubmodule π (K ⊔ J) =
      unitaryFixedSubmodule π K ⊓ unitaryFixedSubmodule π J := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · change x ∈ unitaryFixedSubmodule π K
      rw [mem_unitaryFixedSubmodule]
      intro k
      exact (mem_unitaryFixedSubmodule π (K ⊔ J) x).mp hx
        ⟨k, Subgroup.mem_sup_left k.property⟩
    · change x ∈ unitaryFixedSubmodule π J
      rw [mem_unitaryFixedSubmodule]
      intro j
      exact (mem_unitaryFixedSubmodule π (K ⊔ J) x).mp hx
        ⟨j, Subgroup.mem_sup_right j.property⟩
  · rintro ⟨hxK, hxJ⟩
    have hK : K ≤ unitaryVectorStabilizer π x := by
      intro k hk
      exact (mem_unitaryFixedSubmodule π K x).mp hxK ⟨k, hk⟩
    have hJ : J ≤ unitaryVectorStabilizer π x := by
      intro j hj
      exact (mem_unitaryFixedSubmodule π J x).mp hxJ ⟨j, hj⟩
    rw [mem_unitaryFixedSubmodule]
    intro g
    exact (sup_le hK hJ) g.property

theorem unitaryFixedSubmodule_isClosed
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) :
    IsClosed (unitaryFixedSubmodule π K : Set H) := by
  have hset :
      (unitaryFixedSubmodule π K : Set H) =
        ⋂ g : K, {x : H | π (g : G) x = x} := by
    ext x
    simp only [SetLike.mem_coe, mem_unitaryFixedSubmodule, Subtype.forall, Set.mem_iInter,
      Set.mem_ofPred_eq]
  rw [hset]
  exact isClosed_iInter fun g =>
    isClosed_eq (π (g : G)).continuous continuous_id

instance unitaryFixedSubmodule_completeSpace
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) :
    CompleteSpace (unitaryFixedSubmodule π K) :=
  (unitaryFixedSubmodule_isClosed π K).isComplete.completeSpace_coe

theorem unitaryFixedSubmodule_map_of_centralizes
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) (g : G)
    (hg : ∀ k : K, Commute g (k : G)) :
    (unitaryFixedSubmodule π K).map (π g).toLinearEquiv.toLinearMap =
      unitaryFixedSubmodule π K := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_unitaryFixedSubmodule]
    intro k
    have hk := (mem_unitaryFixedSubmodule π K x).mp hx k
    calc
      π (k : G) (π g x) = π ((k : G) * g) x := by simp only [map_mul, LinearIsometryEquiv.coe_mul,
        Function.comp_apply]
      _ = π (g * (k : G)) x := by rw [(hg k).eq]
      _ = π g (π (k : G) x) := by simp only [map_mul, LinearIsometryEquiv.coe_mul,
        Function.comp_apply]
      _ = π g x := by rw [hk]
  · intro hz
    refine ⟨π g⁻¹ z, ?_, ?_⟩
    · change π g⁻¹ z ∈ unitaryFixedSubmodule π K
      rw [mem_unitaryFixedSubmodule]
      intro k
      have hk := (mem_unitaryFixedSubmodule π K z).mp hz k
      calc
        π (k : G) (π g⁻¹ z) = π ((k : G) * g⁻¹) z := by simp only [map_inv,
          LinearIsometryEquiv.coe_inv, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]
        _ = π (g⁻¹ * (k : G)) z := by rw [(hg k).inv_left.eq]
        _ = π g⁻¹ (π (k : G) z) := by simp only [map_mul, map_inv, LinearIsometryEquiv.coe_mul,
          LinearIsometryEquiv.coe_inv, Function.comp_apply]
        _ = π g⁻¹ z := by rw [hk]
    · simp only [map_inv, LinearIsometryEquiv.coe_inv, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv,
        LinearIsometryEquiv.apply_symm_apply]

theorem unitaryFixedSubmodule_starProjection_commute
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) (g : G)
    (hg : ∀ k : K, Commute g (k : G)) (x : H) :
    (unitaryFixedSubmodule π K).starProjection (π g x) =
      π g ((unitaryFixedSubmodule π K).starProjection x) := by
  let : CompleteSpace (unitaryFixedSubmodule π K) :=
    unitaryFixedSubmodule_completeSpace π K
  have hmap := unitaryFixedSubmodule_map_of_centralizes π K g hg
  simpa only [hmap, LinearIsometryEquiv.symm_apply_apply] using
    Submodule.starProjection_map_apply (π g) (unitaryFixedSubmodule π K) (π g x)

theorem unitaryFixedSubmodule_starProjection_mem_of_commute
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K J : Subgroup G)
    (hcomm : ∀ k : K, ∀ j : J, Commute (k : G) (j : G))
    {x : H} (hx : x ∈ unitaryFixedSubmodule π J) :
    (unitaryFixedSubmodule π K).starProjection x ∈
      unitaryFixedSubmodule π J := by
  let : CompleteSpace (unitaryFixedSubmodule π K) :=
    unitaryFixedSubmodule_completeSpace π K
  rw [mem_unitaryFixedSubmodule]
  intro j
  have hj := (mem_unitaryFixedSubmodule π J x).mp hx j
  have he := unitaryFixedSubmodule_starProjection_commute π K (j : G)
    (fun k => (hcomm k j).symm) x
  simpa only [hj] using he.symm

theorem norm_finset_sum_sq_eq_of_pairwise_inner_zero
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (f : ι → H) (s : Finset ι)
    (horth : ∀ ⦃i j : ι⦄, i ≠ j → inner ℂ (f i) (f j) = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [norm_add_sq (𝕜 := ℂ)]
      have hzero : inner ℂ (f i) (∑ j ∈ s, f j) = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro j hj
        exact horth (by
          intro h
          subst j
          exact hi hj)
      simp only [hzero, RCLike.re_to_complex, Complex.zero_re, mul_zero, add_zero, ih]

theorem unitaryImages_inner_sq_mul_card_le
    {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ι → H ≃ₗᵢ[ℂ] H) (a b : H)
    (hb : ∀ i : ι, U i b = b)
    (horth : ∀ ⦃i j : ι⦄, i ≠ j →
      inner ℂ (U i a) (U j a) = 0) :
    (Fintype.card ι : ℝ) * ‖inner ℂ a b‖ ^ 2 ≤
      ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  classical
  have hnorm :
      ‖∑ i : ι, U i a‖ ^ 2 =
        (Fintype.card ι : ℝ) * ‖a‖ ^ 2 := by
    calc
      ‖∑ i : ι, U i a‖ ^ 2 =
          ∑ i : ι, ‖U i a‖ ^ 2 := by
            simpa only [norm_map, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
              norm_finset_sum_sq_eq_of_pairwise_inner_zero (fun i : ι => U i a) Finset.univ horth
      _ = (Fintype.card ι : ℝ) * ‖a‖ ^ 2 := by simp only [norm_map, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
  have hterm (i : ι) : inner ℂ (U i a) b = inner ℂ a b := by
    calc
      inner ℂ (U i a) b = inner ℂ (U i a) (U i b) := by rw [hb i]
      _ = inner ℂ a b := (U i).inner_map_map a b
  have hinner :
      inner ℂ (∑ i : ι, U i a) b =
        (Fintype.card ι : ℂ) * inner ℂ a b := by
    rw [sum_inner]
    simp_rw [hterm]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcs :
      (Fintype.card ι : ℝ) * ‖inner ℂ a b‖ ≤
        ‖∑ i : ι, U i a‖ * ‖b‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (∑ i : ι, U i a) b
    rw [hinner, norm_mul, Complex.norm_natCast] at h
    exact h
  have hsq :
      ((Fintype.card ι : ℝ) * ‖inner ℂ a b‖) ^ 2 ≤
        (‖∑ i : ι, U i a‖ * ‖b‖) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hcs
  rw [mul_pow, mul_pow, hnorm] at hsq
  by_cases hcard : Fintype.card ι = 0
  · simp only [hcard, Nat.cast_zero, zero_mul]
    positivity
  · have hpos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hcard
    apply (mul_le_mul_iff_right₀ hpos).mp
    calc
      (Fintype.card ι : ℝ) *
          ((Fintype.card ι : ℝ) * ‖inner ℂ a b‖ ^ 2) =
        (Fintype.card ι : ℝ) ^ 2 * ‖inner ℂ a b‖ ^ 2 := by ring
      _ ≤ ((Fintype.card ι : ℝ) * ‖a‖ ^ 2) * ‖b‖ ^ 2 := hsq
      _ = (Fintype.card ι : ℝ) * (‖a‖ ^ 2 * ‖b‖ ^ 2) := by ring

theorem unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K Z : Subgroup G)
    (hcomm : ∀ k : K, ∀ z : Z, Commute (k : G) (z : G))
    {x : H} (hx : x ∈ (unitaryFixedSubmodule π Z)ᗮ) :
    (unitaryFixedSubmodule π K).starProjection x ∈
      (unitaryFixedSubmodule π Z)ᗮ := by
  let : CompleteSpace (unitaryFixedSubmodule π K) :=
    unitaryFixedSubmodule_completeSpace π K
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hpz := unitaryFixedSubmodule_starProjection_mem_of_commute
    π K Z hcomm hz
  calc
    inner ℂ z ((unitaryFixedSubmodule π K).starProjection x) =
        inner ℂ ((unitaryFixedSubmodule π K).starProjection z) x :=
      (Submodule.inner_starProjection_left_eq_right
        (unitaryFixedSubmodule π K) z x).symm
    _ = 0 :=
      (Submodule.mem_orthogonal (unitaryFixedSubmodule π Z) x).mp hx
        ((unitaryFixedSubmodule π K).starProjection z) hpz

theorem unitaryFixedSubmodule_orthogonal_map_of_centralizes
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (Z : Subgroup G) (g : G)
    (hg : ∀ z : Z, Commute g (z : G))
    {x : H} (hx : x ∈ (unitaryFixedSubmodule π Z)ᗮ) :
    π g x ∈ (unitaryFixedSubmodule π Z)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hmap := unitaryFixedSubmodule_map_of_centralizes
    π Z g⁻¹ (fun k => (hg k).inv_left)
  have hzpre : π g⁻¹ z ∈ unitaryFixedSubmodule π Z := by
    rw [← hmap]
    exact ⟨z, hz, rfl⟩
  calc
    inner ℂ z (π g x) =
        inner ℂ (π g (π g⁻¹ z)) (π g x) := by simp only [map_inv, LinearIsometryEquiv.coe_inv,
          LinearIsometryEquiv.apply_symm_apply]
    _ = inner ℂ (π g⁻¹ z) x := (π g).inner_map_map (π g⁻¹ z) x
    _ = 0 :=
      (Submodule.mem_orthogonal (unitaryFixedSubmodule π Z) x).mp
        hx (π g⁻¹ z) hzpre

theorem unitaryFixedSubmodules_inner_eq_zero_of_commute_centerComplement
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K J Z : Subgroup G)
    (hcomm : ∀ k : K, ∀ j : J, Commute (k : G) (j : G))
    (hKZ : ∀ k : K, ∀ z : Z, Commute (k : G) (z : G))
    (hcenter : Z ≤ K ⊔ J)
    {a b : H}
    (ha : a ∈ unitaryFixedSubmodule π K)
    (hb : b ∈ unitaryFixedSubmodule π J)
    (hbZ : b ∈ (unitaryFixedSubmodule π Z)ᗮ) :
    inner ℂ a b = 0 := by
  let : CompleteSpace (unitaryFixedSubmodule π K) :=
    unitaryFixedSubmodule_completeSpace π K
  let p : H := (unitaryFixedSubmodule π K).starProjection b
  have hpK : p ∈ unitaryFixedSubmodule π K :=
    Submodule.starProjection_apply_mem _ _
  have hpJ : p ∈ unitaryFixedSubmodule π J :=
    unitaryFixedSubmodule_starProjection_mem_of_commute
      π K J hcomm hb
  have hpJoin : p ∈ unitaryFixedSubmodule π (K ⊔ J) := by
    rw [unitaryFixedSubmodule_sup]
    exact ⟨hpK, hpJ⟩
  have hpZ : p ∈ unitaryFixedSubmodule π Z := by
    rw [mem_unitaryFixedSubmodule]
    intro z
    exact (mem_unitaryFixedSubmodule π (K ⊔ J) p).mp
      hpJoin ⟨z, hcenter z.property⟩
  have hpZorth : p ∈ (unitaryFixedSubmodule π Z)ᗮ :=
    unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
      π K Z hKZ hbZ
  have hpzero : p = 0 := by
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp
      ((Submodule.mem_orthogonal (unitaryFixedSubmodule π Z) p).mp
        hpZorth p hpZ)
  apply inner_eq_zero_symm.mp
  simpa [p, hpzero] using
    (Submodule.starProjection_inner_eq_zero
      (K := unitaryFixedSubmodule π K) b a ha)

def heisenbergConjugateSubgroup
    {G : Type*} [Group G] (X : Subgroup G) (g : G) :
    Subgroup G :=
  X.map (MulAut.conj g).toMonoidHom

theorem heisenbergFiniteFamily_centerComplement_inner_sq_le
    {G : Type u₁} {H : Type v₁} {ι : Type*}
    [Group G] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H)
    (X Z : Subgroup G) (y : ι → G)
    (hXZ : ∀ x : X, ∀ z : Z, Commute (x : G) (z : G))
    (hyZ : ∀ i : ι, ∀ z : Z, Commute (y i) (z : G))
    (hcomm : ∀ ⦃i j : ι⦄, i ≠ j →
      ∀ x : heisenbergConjugateSubgroup X (y i),
      ∀ x' : heisenbergConjugateSubgroup X (y j),
        Commute (x : G) (x' : G))
    (hcenter : ∀ ⦃i j : ι⦄, i ≠ j →
      Z ≤ heisenbergConjugateSubgroup X (y i) ⊔
        heisenbergConjugateSubgroup X (y j))
    {a b : H}
    (ha : a ∈ unitaryFixedSubmodule π X)
    (haZ : a ∈ (unitaryFixedSubmodule π Z)ᗮ)
    (hb : ∀ i : ι, π (y i) b = b) :
    (Fintype.card ι : ℝ) * ‖inner ℂ a b‖ ^ 2 ≤
      ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have hfix (i : ι) :
      π (y i) a ∈ unitaryFixedSubmodule π
        (heisenbergConjugateSubgroup X (y i)) := by
    rw [mem_unitaryFixedSubmodule]
    rintro ⟨_, ⟨g, hg, rfl⟩⟩
    have hga := (mem_unitaryFixedSubmodule π X a).mp ha ⟨g, hg⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, map_mul, map_inv,
      LinearIsometryEquiv.coe_mul, LinearIsometryEquiv.coe_inv, Function.comp_apply,
        LinearIsometryEquiv.symm_apply_apply,
      hga]
  have horthZ (i : ι) :
      π (y i) a ∈ (unitaryFixedSubmodule π Z)ᗮ :=
    unitaryFixedSubmodule_orthogonal_map_of_centralizes
      π Z (y i) (hyZ i) haZ
  have hJZ (i : ι) :
      ∀ x : heisenbergConjugateSubgroup X (y i),
      ∀ z : Z, Commute (x : G) (z : G) := by
    rintro ⟨_, ⟨g, hg, rfl⟩⟩ z
    change Commute (y i * g * (y i)⁻¹) (z : G)
    exact ((hyZ i z).mul_left (hXZ ⟨g, hg⟩ z)).mul_left
      (hyZ i z).inv_left
  apply unitaryImages_inner_sq_mul_card_le
    (fun i : ι => π (y i)) a b hb
  intro i j hij
  exact unitaryFixedSubmodules_inner_eq_zero_of_commute_centerComplement
    π (heisenbergConjugateSubgroup X (y i))
    (heisenbergConjugateSubgroup X (y j)) Z
    (hcomm hij) (hJZ i) (hcenter hij)
    (hfix i) (hfix j) (horthZ j)

theorem finiteOuterBlockProductCentral_centerComplement_inner_sq_le
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    {H : Type v₁} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (π : UnitaryRepresentation
      (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) H)
    {a b : H}
    (ha : a ∈ unitaryFixedSubmodule π
      (finiteOuterBlockRootSubgroup W i j hij))
    (haZ : a ∈
      (unitaryFixedSubmodule π
        (finiteOuterBlockProductCentralRootSubgroup W i k hik B))ᗮ)
    (hb : b ∈ unitaryFixedSubmodule π
      (finiteOuterBlockRootSubgroup W j k hjk)) :
    8 * ‖inner ℂ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  let : Fintype finiteBlockGaloisField :=
    Fintype.ofFinite finiteBlockGaloisField
  have hcard : Fintype.card finiteBlockGaloisField = 8 := by
    simpa only [Nat.card_eq_fintype_card] using
      finiteBlockGaloisField_natCard
  have hbound := heisenbergFiniteFamily_centerComplement_inner_sq_le
    π
    (finiteOuterBlockRootSubgroup W i j hij)
    (finiteOuterBlockProductCentralRootSubgroup W i k hik B)
    (fun t : finiteBlockGaloisField =>
      finiteOuterBlockGaloisConjugatorWithCoefficient W j k hjk B t)
    (by
      intro x z
      exact finiteOuterBlockProductCentralRoot_commute_left
        W i j k hij hik B x z x.property z.property)
    (by
      intro t z
      exact finiteOuterBlockProductCentralRoot_commute_right
        W i j k hjk hik B
        (finiteOuterBlockGaloisConjugatorWithCoefficient
          W j k hjk B t) z
        (finiteOuterBlockGaloisConjugatorWithCoefficient_mem
          W j k hjk B t) z.property)
    (by
      intro s t hst x x'
      exact finiteOuterBlockGaloisConjugateRootsWithCoefficient_commute
        W i j k hij hjk hik B s t x x' x.property x'.property)
    (by
      intro s t hst
      exact finiteOuterBlockProductCentralRoot_le_galoisConjugates
        W i j k hij hjk hik B s t hst)
    ha haZ
    (by
      intro t
      exact
        (mem_unitaryFixedSubmodule π
          (finiteOuterBlockRootSubgroup W j k hjk) b).mp hb
          ⟨finiteOuterBlockGaloisConjugatorWithCoefficient
            W j k hjk B t,
            finiteOuterBlockGaloisConjugatorWithCoefficient_mem
              W j k hjk B t⟩)
  simpa only [ge_iff_le, hcard, Nat.cast_ofNat] using hbound

section FiniteSubgroupAveraging

variable {G : Type*} {H : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finiteUnitarySubgroupAverage
    (π : UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K] (x : H) : H :=
  (Fintype.card K : ℂ)⁻¹ • ∑ k : K, π (k : G) x

theorem finiteUnitarySubgroupAverage_fixed
    (π : UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K] (x : H) (g : K) :
    π (g : G) (finiteUnitarySubgroupAverage π K x) =
      finiteUnitarySubgroupAverage π K x := by
  classical
  unfold finiteUnitarySubgroupAverage
  rw [map_smul, map_sum]
  congr 1
  calc
    (∑ k : K, π (g : G) (π (k : G) x)) =
        ∑ k : K, π ((g * k : K) : G) x := by
          apply Finset.sum_congr rfl
          intro k _
          simp only [Subgroup.coe_mul, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]
    _ = ∑ k : K, π (k : G) x :=
      Function.Bijective.sum_comp (Group.mulLeft_bijective g)
        (fun k : K => π (k : G) x)

theorem inner_finiteUnitarySubgroupAverage_of_fixed_left
    (π : UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K] (a b : H)
    (ha : ∀ k : K, π (k : G) a = a) :
    inner ℂ a (finiteUnitarySubgroupAverage π K b) =
      inner ℂ a b := by
  classical
  have hcard : (Fintype.card K : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hterm (k : K) :
      inner ℂ a (π (k : G) b) = inner ℂ a b := by
    calc
      inner ℂ a (π (k : G) b) =
          inner ℂ (π (k : G) a) (π (k : G) b) := by rw [ha k]
      _ = inner ℂ a b := (π (k : G)).inner_map_map a b
  unfold finiteUnitarySubgroupAverage
  rw [inner_smul_right, inner_sum]
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ne_eq, hcard, not_false_eq_true,
    inv_mul_cancel_left₀]

theorem finiteUnitarySubgroupAverage_fixed_of_orbit_fixed
    (π : UnitaryRepresentation G H)
    (K J : Subgroup G) [Fintype K] (b : H)
    (horbit : ∀ (k : K) (j : J),
      π (j : G) (π (k : G) b) = π (k : G) b)
    (j : J) :
    π (j : G) (finiteUnitarySubgroupAverage π K b) =
      finiteUnitarySubgroupAverage π K b := by
  classical
  unfold finiteUnitarySubgroupAverage
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact horbit k j

theorem inner_eq_zero_of_finite_subgroupAverage_pair_orthogonal
    (π : UnitaryRepresentation G H)
    (K J : Subgroup G) [Finite K] (a b : H)
    (ha : ∀ k : K, π (k : G) a = a)
    (horbit : ∀ (k : K) (j : J),
      π (j : G) (π (k : G) b) = π (k : G) b)
    (horth : ∀ z : H,
      (∀ k : K, π (k : G) z = z) →
      (∀ j : J, π (j : G) z = z) →
      inner ℂ a z = 0) :
    inner ℂ a b = 0 := by
  let : Fintype K := Fintype.ofFinite K
  let z : H := finiteUnitarySubgroupAverage π K b
  have hzK : ∀ k : K, π (k : G) z = z :=
    finiteUnitarySubgroupAverage_fixed π K b
  have hzJ : ∀ j : J, π (j : G) z = z :=
    finiteUnitarySubgroupAverage_fixed_of_orbit_fixed
      π K J b horbit
  calc
    inner ℂ a b = inner ℂ a z :=
      (inner_finiteUnitarySubgroupAverage_of_fixed_left
        π K a b ha).symm
    _ = 0 := horth z hzK hzJ

end FiniteSubgroupAveraging

theorem finiteOuterBlockRootSubgroups_pair_inner_sq_le
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    {H : Type v₁} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule (ZMod 2) R) [Finite W]
    (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (π : UnitaryRepresentation
      (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) H)
    {a b : H}
    (ha : a ∈ unitaryFixedSubmodule π
      (finiteOuterBlockRootSubgroup W i j hij))
    (hb : b ∈ unitaryFixedSubmodule π
      (finiteOuterBlockRootSubgroup W j k hjk))
    (haQ : a ∈
      (unitaryFixedSubmodule π
        (finiteOuterBlockRootSubgroup W i j hij) ⊓
       unitaryFixedSubmodule π
        (finiteOuterBlockRootSubgroup W j k hjk))ᗮ)
    (hbQ : b ∈
      (unitaryFixedSubmodule π
        (finiteOuterBlockRootSubgroup W i j hij) ⊓
       unitaryFixedSubmodule π
        (finiteOuterBlockRootSubgroup W j k hjk))ᗮ) :
    8 * ‖inner ℂ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  classical
  let : Fintype W := Fintype.ofFinite W
  let X := finiteOuterBlockRootSubgroup W i j hij
  let Y := finiteOuterBlockRootSubgroup W j k hjk
  let Z (B : Matrix (Fin 3) (Fin 3) W) :=
    finiteOuterBlockProductCentralRootSubgroup W i k hik B
  let Q : Submodule ℂ H :=
    unitaryFixedSubmodule π X ⊓ unitaryFixedSubmodule π Y
  let U : Submodule ℂ H := unitaryFixedSubmodule π X ⊓ Qᗮ
  let V : Submodule ℂ H := unitaryFixedSubmodule π Y ⊓ Qᗮ
  let F (B : Matrix (Fin 3) (Fin 3) W) :=
    unitaryFixedSubmodule π (Z B)
  let : Finite X := finite_finiteOuterBlockRootSubgroup W i j hij
  let : Fintype X := Fintype.ofFinite X
  let (B : Matrix (Fin 3) (Fin 3) W) : CompleteSpace (F B) :=
    unitaryFixedSubmodule_completeSpace π (Z B)
  have hpairCentral (B : Matrix (Fin 3) (Fin 3) W) :
      ∀ z : Z B, ∀ g :
        (X ⊔ Y : Subgroup
          (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))),
        Commute
          (z : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
          (g : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) := by
    intro z g
    have hg := finiteOuterBlockProductCentralRoot_pair_le_centralizer
      W i j k hij hjk hik B g.property
    rw [Subgroup.mem_centralizer_iff] at hg
    change (z : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
      (g : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) =
      (g : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
      (z : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
    exact hg z z.property
  refine inner_sq_le_of_finite_orthogonal_sector_splitting
    F U V ?_ ?_ ?_ ?_ ?_ a b ⟨ha, haQ⟩ ⟨hb, hbQ⟩
  · intro B x hx
    change (unitaryFixedSubmodule π (Z B)).starProjection x ∈
      unitaryFixedSubmodule π X ⊓ Qᗮ
    refine ⟨?_, ?_⟩
    · exact unitaryFixedSubmodule_starProjection_mem_of_commute
        π (Z B) X
        (fun z x =>
          (finiteOuterBlockProductCentralRoot_commute_left
            W i j k hij hik B x z x.property z.property).symm)
        hx.1
    · have hq : x ∈ (unitaryFixedSubmodule π (X ⊔ Y))ᗮ := by
        rw [unitaryFixedSubmodule_sup]
        exact hx.2
      have hp := unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
        π (Z B) (X ⊔ Y) (hpairCentral B) hq
      rw [unitaryFixedSubmodule_sup] at hp
      exact hp
  · intro B x hx
    change (unitaryFixedSubmodule π (Z B)).starProjection x ∈
      unitaryFixedSubmodule π Y ⊓ Qᗮ
    refine ⟨?_, ?_⟩
    · exact unitaryFixedSubmodule_starProjection_mem_of_commute
        π (Z B) Y
        (fun z y =>
          (finiteOuterBlockProductCentralRoot_commute_right
            W i j k hjk hik B y z y.property z.property).symm)
        hx.1
    · have hq : x ∈ (unitaryFixedSubmodule π (X ⊔ Y))ᗮ := by
        rw [unitaryFixedSubmodule_sup]
        exact hx.2
      have hp := unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
        π (Z B) (X ⊔ Y) (hpairCentral B) hq
      rw [unitaryFixedSubmodule_sup] at hp
      exact hp
  · intro B C x hx
    change (unitaryFixedSubmodule π (Z B)).starProjection x ∈
      unitaryFixedSubmodule π (Z C)
    exact unitaryFixedSubmodule_starProjection_mem_of_commute
      π (Z B) (Z C)
      (fun z w => finiteOuterBlockProductCentralRoots_commute
        W i k hik B C z w z.property w.property)
      hx
  · intro B x y hx hy hxZ _
    exact finiteOuterBlockProductCentral_centerComplement_inner_sq_le
      W i j k hij hjk hik B π hx.1 hxZ hy.1
  · intro x y hx hy _ hyF
    apply inner_eq_zero_of_finite_subgroupAverage_pair_orthogonal
      π X Y x y
    · exact (mem_unitaryFixedSubmodule π X x).mp hx.1
    · intro s t
      obtain ⟨B, hB⟩ :=
        finiteOuterBlockRoot_commutator_exists_productCentral
          W i j k hij hjk hik s t s.property t.property
      let c : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
        ⁅(s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)),
          (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))⁆
      have hcb : π c⁻¹ y = y :=
        (mem_unitaryFixedSubmodule π (Z B) y).mp (hyF B)
          ⟨c⁻¹, (Z B).inv_mem hB⟩
      have htb : π (t : elementaryGroup (Fin 3)
          (Matrix (Fin 3) (Fin 3) R)) y = y :=
        (mem_unitaryFixedSubmodule π Y y).mp hy.1 t
      have hsc : Commute
          (s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) c :=
        finiteOuterBlockProductCentralRoot_commute_left
          W i j k hij hik B s c s.property hB
      have hgroup :
          (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
              (s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) =
            (s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
              c⁻¹ *
              (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) := by
        calc
          (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
              (s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) =
            c⁻¹ *
              (s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
              (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) := by
                dsimp [c]
                simp only [commutatorElement_def]
                group
          _ = (s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
              c⁻¹ *
              (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) := by
                rw [hsc.inv_right.eq]
      calc
        π (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
            (π (s : elementaryGroup (Fin 3)
              (Matrix (Fin 3) (Fin 3) R)) y) =
          π ((t : elementaryGroup (Fin 3)
            (Matrix (Fin 3) (Fin 3) R)) * s) y := by
              simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]
        _ = π ((s : elementaryGroup (Fin 3)
              (Matrix (Fin 3) (Fin 3) R)) * c⁻¹ * t) y := by
              rw [hgroup]
        _ = π (s : elementaryGroup (Fin 3)
              (Matrix (Fin 3) (Fin 3) R))
            (π c⁻¹ (π (t : elementaryGroup (Fin 3)
              (Matrix (Fin 3) (Fin 3) R)) y)) := by
              simp only [map_mul, map_inv, LinearIsometryEquiv.coe_mul, LinearIsometryEquiv.coe_inv,
                Function.comp_apply]
        _ = π (s : elementaryGroup (Fin 3)
              (Matrix (Fin 3) (Fin 3) R)) y := by
              rw [htb, hcb]
    · intro z hzX hzY
      apply (Submodule.mem_orthogonal' Q x).mp hx.2
      exact ⟨(mem_unitaryFixedSubmodule π X z).mpr hzX,
        (mem_unitaryFixedSubmodule π Y z).mpr hzY⟩

def finiteOuterBlockCyclicRootFamily
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    (W : Submodule (ZMod 2) R) (i : Fin 3) :
    Subgroup (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) :=
  finiteOuterBlockRootSubgroup W i (i + 1) (by
    fin_cases i <;> decide)

theorem finiteOuterBlockCyclicRootFamily_pair_inner_sq_le
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    {H : Type v₁} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule (ZMod 2) R) [Finite W]
    (π : UnitaryRepresentation
      (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) H)
    (i j : Fin 3) (hij : i ≠ j) (a b : H)
    (ha : a ∈ unitaryFixedSubmodule π
      (finiteOuterBlockCyclicRootFamily W i))
    (haQ : a ∈
      (unitaryFixedSubmodule π (finiteOuterBlockCyclicRootFamily W i) ⊓
       unitaryFixedSubmodule π (finiteOuterBlockCyclicRootFamily W j))ᗮ)
    (hb : b ∈ unitaryFixedSubmodule π
      (finiteOuterBlockCyclicRootFamily W j))
    (hbQ : b ∈
      (unitaryFixedSubmodule π (finiteOuterBlockCyclicRootFamily W i) ⊓
       unitaryFixedSubmodule π (finiteOuterBlockCyclicRootFamily W j))ᗮ) :
    8 * ‖inner ℂ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact finiteOuterBlockRootSubgroups_pair_inner_sq_le
      W 0 1 2 (by decide) (by decide) (by decide)
      π ha hb haQ hbQ
  · rw [inf_comm] at haQ hbQ
    have h := finiteOuterBlockRootSubgroups_pair_inner_sq_le
        W 2 0 1 (by decide) (by decide) (by decide)
        π hb ha hbQ haQ
    calc
      8 * ‖inner ℂ a b‖ ^ 2 = 8 * ‖inner ℂ b a‖ ^ 2 := by
        rw [norm_inner_symm a b]
      _ ≤ ‖b‖ ^ 2 * ‖a‖ ^ 2 := h
      _ = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by rw [mul_comm]
  · rw [inf_comm] at haQ hbQ
    have h := finiteOuterBlockRootSubgroups_pair_inner_sq_le
        W 0 1 2 (by decide) (by decide) (by decide)
        π hb ha hbQ haQ
    calc
      8 * ‖inner ℂ a b‖ ^ 2 = 8 * ‖inner ℂ b a‖ ^ 2 := by
        rw [norm_inner_symm a b]
      _ ≤ ‖b‖ ^ 2 * ‖a‖ ^ 2 := h
      _ = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by rw [mul_comm]
  · exact (hij rfl).elim
  · exact finiteOuterBlockRootSubgroups_pair_inner_sq_le
      W 1 2 0 (by decide) (by decide) (by decide)
      π ha hb haQ hbQ
  · exact finiteOuterBlockRootSubgroups_pair_inner_sq_le
      W 2 0 1 (by decide) (by decide) (by decide)
      π ha hb haQ hbQ
  · rw [inf_comm] at haQ hbQ
    have h := finiteOuterBlockRootSubgroups_pair_inner_sq_le
        W 1 2 0 (by decide) (by decide) (by decide)
        π hb ha hbQ haQ
    calc
      8 * ‖inner ℂ a b‖ ^ 2 = 8 * ‖inner ℂ b a‖ ^ 2 := by
        rw [norm_inner_symm a b]
      _ ≤ ‖b‖ ^ 2 * ‖a‖ ^ 2 := h
      _ = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by rw [mul_comm]
  · exact (hij rfl).elim

end

section

open scoped BigOperators commutatorElement

universe u

section BinaryCoefficientSpan

variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]

def finiteBlockCoefficientSpan (s : Finset R) : Submodule (ZMod 2) R :=
  Submodule.span (ZMod 2) ({1} ∪ (↑s : Set R))

theorem one_mem_finiteBlockCoefficientSpan (s : Finset R) :
    (1 : R) ∈ finiteBlockCoefficientSpan s := by
  apply Submodule.subset_span
  exact Set.mem_union_left _ (Set.mem_singleton 1)

theorem mem_finiteBlockCoefficientSpan_of_mem
    (s : Finset R) {a : R} (ha : a ∈ s) :
    a ∈ finiteBlockCoefficientSpan s := by
  apply Submodule.subset_span
  exact Set.mem_union_right _ ha

instance finiteBlockCoefficientSpan_finite (s : Finset R) :
    Finite (finiteBlockCoefficientSpan s) := by
  let : Module.Finite (ZMod 2) (finiteBlockCoefficientSpan s) :=
    Module.Finite.span_of_finite (ZMod 2)
      (Set.finite_singleton 1 |>.union s.finite_toSet)
  exact Module.finite_of_finite (ZMod 2)

end BinaryCoefficientSpan

section FiniteBlockRoots

variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]

def finiteBlockIndex (i p : Fin 3) : Fin 9 :=
  finProdFinEquiv (i, p)

theorem finiteBlockIndex_ne_of_ne
    {i j : Fin 3} (hij : i ≠ j) (p q : Fin 3) :
    finiteBlockIndex i p ≠ finiteBlockIndex j q := by
  intro h
  exact hij (congrArg Prod.fst (finProdFinEquiv.injective h))

def finiteBlockFlattenRingEquiv :
    Matrix (Fin 3) (Fin 3) (Matrix (Fin 3) (Fin 3) R) ≃+*
      Matrix (Fin 9) (Fin 9) R :=
  (Matrix.compRingEquiv (Fin 3) (Fin 3) R).trans
    (Matrix.reindexRingEquiv R finProdFinEquiv)

def finiteBlockRootHom
    (W : Submodule (ZMod 2) R) (i j : Fin 3) (hij : i ≠ j) :
    Multiplicative (Matrix (Fin 3) (Fin 3) W) →*
      (Matrix (Fin 9) (Fin 9) R)ˣ :=
  (Units.mapEquiv (finiteBlockFlattenRingEquiv (R := R)).toMulEquiv).toMonoidHom.comp
    (((elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)).subtype.comp
      (elementaryRootHom (R := Matrix (Fin 3) (Fin 3) R) i j hij)).comp
        (finiteBlockCoefficientMatrixHom W).toMultiplicative)

def finiteBlockRootSubgroup
    (W : Submodule (ZMod 2) R) (i j : Fin 3) (hij : i ≠ j) :
    Subgroup (Matrix (Fin 9) (Fin 9) R)ˣ :=
  (finiteBlockRootHom W i j hij).range

theorem finiteBlockRootHom_single
    (W : Submodule (ZMod 2) R)
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin 3) (a : W) :
    finiteBlockRootHom W i j hij
        (Multiplicative.ofAdd (Matrix.single p q a)) =
      elementaryUnit (finiteBlockIndex i p) (finiteBlockIndex j q)
        (finiteBlockIndex_ne_of_ne hij p q) (a : R) := by
  apply Units.ext
  change
    finiteBlockFlattenRingEquiv
      (1 + Matrix.single i j
        ((finiteBlockCoefficientMatrixHom W) (Matrix.single p q a))) =
      1 + Matrix.single (finiteBlockIndex i p) (finiteBlockIndex j q) (a : R)
  have hsingle :
      finiteBlockCoefficientMatrixHom W (Matrix.single p q a) =
        Matrix.single p q (a : R) := by
    ext k l
    by_cases hp : p = k
    · subst k
      by_cases hq : q = l
      · subst l
        simp only [finiteBlockCoefficientMatrixHom, AddMonoidHom.mapMatrix_apply,
          LinearMap.toAddMonoidHom_coe,
          Submodule.coe_subtype, Matrix.map_apply, Matrix.single_apply_same]
      · simp only [finiteBlockCoefficientMatrixHom, AddMonoidHom.mapMatrix_apply,
        LinearMap.toAddMonoidHom_coe,
          Submodule.coe_subtype, Matrix.map_apply, hq, and_false, not_false_eq_true,
            Matrix.single_apply_of_ne,
          ZeroMemClass.coe_zero]
    · simp only [finiteBlockCoefficientMatrixHom, AddMonoidHom.mapMatrix_apply,
      LinearMap.toAddMonoidHom_coe,
        Submodule.coe_subtype, Matrix.map_apply, hp, false_and, not_false_eq_true,
          Matrix.single_apply_of_ne,
        ZeroMemClass.coe_zero]
  rw [hsingle]
  rw [map_add, map_one]
  congr 1
  change
    Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.comp (Fin 3) (Fin 3) (Fin 3) (Fin 3) R
        (Matrix.single i j (Matrix.single p q (a : R)))) =
      Matrix.single (finiteBlockIndex i p) (finiteBlockIndex j q) (a : R)
  rw [Matrix.comp_single_single]
  ext x y
  simp only [Nat.reduceMul, Matrix.reindex, Equiv.coe_fn_mk, Matrix.submatrix_apply,
    Matrix.single_apply,
    Equiv.eq_symm_apply, finiteBlockIndex]

theorem elementaryUnit_mem_finiteBlockRootSubgroup
    (W : Submodule (ZMod 2) R)
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin 3)
    (a : R) (ha : a ∈ W) :
    elementaryUnit (finiteBlockIndex i p) (finiteBlockIndex j q)
        (finiteBlockIndex_ne_of_ne hij p q) a ∈
      finiteBlockRootSubgroup W i j hij := by
  refine ⟨Multiplicative.ofAdd (Matrix.single p q (⟨a, ha⟩ : W)), ?_⟩
  exact finiteBlockRootHom_single W i j hij p q ⟨a, ha⟩

theorem finiteBlockRootSubgroup_le_elementaryGroup
    (W : Submodule (ZMod 2) R)
    (i j : Fin 3) (hij : i ≠ j) :
    finiteBlockRootSubgroup W i j hij ≤
      elementaryGroup (Fin 9) R := by
  rintro _ ⟨A, rfl⟩
  change
    finiteBlockRootHom W i j hij
        (Multiplicative.ofAdd A.toAdd) ∈
      elementaryGroup (Fin 9) R
  refine Matrix.induction_on'
    (P := fun M : Matrix (Fin 3) (Fin 3) W =>
      finiteBlockRootHom W i j hij (Multiplicative.ofAdd M) ∈
        elementaryGroup (Fin 9) R)
    A.toAdd ?_ ?_ ?_
  · change finiteBlockRootHom W i j hij 1 ∈ elementaryGroup (Fin 9) R
    rw [map_one]
    exact (elementaryGroup (Fin 9) R).one_mem
  · intro P Q hP hQ
    change
      finiteBlockRootHom W i j hij
          (Multiplicative.ofAdd (P + Q)) ∈
        elementaryGroup (Fin 9) R
    change
      finiteBlockRootHom W i j hij
          (Multiplicative.ofAdd P * Multiplicative.ofAdd Q) ∈
        elementaryGroup (Fin 9) R
    rw [map_mul]
    exact (elementaryGroup (Fin 9) R).mul_mem hP hQ
  · intro p q a
    rw [finiteBlockRootHom_single]
    exact elementaryUnit_mem _ _ _ (a : R)

def cyclicFiniteBlockRootSubgroup
    (W : Submodule (ZMod 2) R) :
    Subgroup (Matrix (Fin 9) (Fin 9) R)ˣ :=
  finiteBlockRootSubgroup W 0 1 (by decide) ⊔
    finiteBlockRootSubgroup W 1 2 (by decide) ⊔
      finiteBlockRootSubgroup W 2 0 (by decide)

theorem cyclicFiniteBlockRootSubgroup_le_elementaryGroup
    (W : Submodule (ZMod 2) R) :
    cyclicFiniteBlockRootSubgroup W ≤ elementaryGroup (Fin 9) R := by
  unfold cyclicFiniteBlockRootSubgroup
  exact sup_le
    (sup_le
      (finiteBlockRootSubgroup_le_elementaryGroup W 0 1 (by decide))
      (finiteBlockRootSubgroup_le_elementaryGroup W 1 2 (by decide)))
    (finiteBlockRootSubgroup_le_elementaryGroup W 2 0 (by decide))

theorem elementaryUnit_mem_cyclicFiniteBlockRootSubgroup_of_block_ne
    (W : Submodule (ZMod 2) R) (hW : (1 : R) ∈ W)
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin 3)
    (a : R) (ha : a ∈ W) :
    elementaryUnit (finiteBlockIndex i p) (finiteBlockIndex j q)
        (finiteBlockIndex_ne_of_ne hij p q) a ∈
      cyclicFiniteBlockRootSubgroup W := by
  let H : Subgroup (Matrix (Fin 9) (Fin 9) R)ˣ :=
    cyclicFiniteBlockRootSubgroup W
  have h01 (p q : Fin 3) (a : R) (ha : a ∈ W) :
      elementaryUnit (finiteBlockIndex 0 p) (finiteBlockIndex 1 q)
          (finiteBlockIndex_ne_of_ne (by decide) p q) a ∈ H := by
    apply (show finiteBlockRootSubgroup W 0 1 (by decide) ≤ H from
      (show finiteBlockRootSubgroup W 0 1 (by decide) ≤
        (finiteBlockRootSubgroup W 0 1 (by decide) ⊔
          finiteBlockRootSubgroup W 1 2 (by decide)) ⊔
          finiteBlockRootSubgroup W 2 0 (by decide) from
        le_trans le_sup_left le_sup_left))
    exact elementaryUnit_mem_finiteBlockRootSubgroup
      W 0 1 (by decide) p q a ha
  have h12 (p q : Fin 3) (a : R) (ha : a ∈ W) :
      elementaryUnit (finiteBlockIndex 1 p) (finiteBlockIndex 2 q)
          (finiteBlockIndex_ne_of_ne (by decide) p q) a ∈ H := by
    apply (show finiteBlockRootSubgroup W 1 2 (by decide) ≤ H from
      (show finiteBlockRootSubgroup W 1 2 (by decide) ≤
        (finiteBlockRootSubgroup W 0 1 (by decide) ⊔
          finiteBlockRootSubgroup W 1 2 (by decide)) ⊔
          finiteBlockRootSubgroup W 2 0 (by decide) from
        le_trans le_sup_right le_sup_left))
    exact elementaryUnit_mem_finiteBlockRootSubgroup
      W 1 2 (by decide) p q a ha
  have h20 (p q : Fin 3) (a : R) (ha : a ∈ W) :
      elementaryUnit (finiteBlockIndex 2 p) (finiteBlockIndex 0 q)
          (finiteBlockIndex_ne_of_ne (by decide) p q) a ∈ H := by
    apply (show finiteBlockRootSubgroup W 2 0 (by decide) ≤ H from
      (show finiteBlockRootSubgroup W 2 0 (by decide) ≤
        (finiteBlockRootSubgroup W 0 1 (by decide) ⊔
          finiteBlockRootSubgroup W 1 2 (by decide)) ⊔
          finiteBlockRootSubgroup W 2 0 (by decide) from le_sup_right))
    exact elementaryUnit_mem_finiteBlockRootSubgroup
      W 2 0 (by decide) p q a ha
  have h02 (p q : Fin 3) (a : R) (ha : a ∈ W) :
      elementaryUnit (finiteBlockIndex 0 p) (finiteBlockIndex 2 q)
          (finiteBlockIndex_ne_of_ne (by decide) p q) a ∈ H :=
    elementaryUnit_mem_of_two_step H
      (finiteBlockIndex 0 p) (finiteBlockIndex 1 0)
      (finiteBlockIndex 2 q)
      (finiteBlockIndex_ne_of_ne (by decide) p 0)
      (finiteBlockIndex_ne_of_ne (by decide) 0 q)
      (finiteBlockIndex_ne_of_ne (by decide) p q) a
      (h01 p 0 a ha) (h12 0 q 1 hW)
  have h10 (p q : Fin 3) (a : R) (ha : a ∈ W) :
      elementaryUnit (finiteBlockIndex 1 p) (finiteBlockIndex 0 q)
          (finiteBlockIndex_ne_of_ne (by decide) p q) a ∈ H :=
    elementaryUnit_mem_of_two_step H
      (finiteBlockIndex 1 p) (finiteBlockIndex 2 0)
      (finiteBlockIndex 0 q)
      (finiteBlockIndex_ne_of_ne (by decide) p 0)
      (finiteBlockIndex_ne_of_ne (by decide) 0 q)
      (finiteBlockIndex_ne_of_ne (by decide) p q) a
      (h12 p 0 a ha) (h20 0 q 1 hW)
  have h21 (p q : Fin 3) (a : R) (ha : a ∈ W) :
      elementaryUnit (finiteBlockIndex 2 p) (finiteBlockIndex 1 q)
          (finiteBlockIndex_ne_of_ne (by decide) p q) a ∈ H :=
    elementaryUnit_mem_of_two_step H
      (finiteBlockIndex 2 p) (finiteBlockIndex 0 0)
      (finiteBlockIndex 1 q)
      (finiteBlockIndex_ne_of_ne (by decide) p 0)
      (finiteBlockIndex_ne_of_ne (by decide) 0 q)
      (finiteBlockIndex_ne_of_ne (by decide) p q) a
      (h20 p 0 a ha) (h01 0 q 1 hW)
  change
    elementaryUnit (finiteBlockIndex i p) (finiteBlockIndex j q)
        (finiteBlockIndex_ne_of_ne hij p q) a ∈ H
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h01 p q a ha
  · exact h02 p q a ha
  · exact h10 p q a ha
  · exact (hij rfl).elim
  · exact h12 p q a ha
  · exact h20 p q a ha
  · exact h21 p q a ha
  · exact (hij rfl).elim

theorem elementaryUnit_mem_cyclicFiniteBlockRootSubgroup
    (W : Submodule (ZMod 2) R) (hW : (1 : R) ∈ W)
    (x y : Fin 9) (hxy : x ≠ y) (a : R) (ha : a ∈ W) :
    elementaryUnit x y hxy a ∈ cyclicFiniteBlockRootSubgroup W := by
  obtain ⟨⟨i, p⟩, rfl⟩ :=
    (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective x
  obtain ⟨⟨j, q⟩, rfl⟩ :=
    (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective y
  change
    elementaryUnit (finiteBlockIndex i p) (finiteBlockIndex j q) hxy a ∈
      cyclicFiniteBlockRootSubgroup W
  by_cases hij : i = j
  · subst j
    let k : Fin 3 := i + 1
    have hik : i ≠ k := by
      dsimp [k]
      fin_cases i <;> decide
    exact elementaryUnit_mem_of_two_step
      (cyclicFiniteBlockRootSubgroup W)
      (finiteBlockIndex i p) (finiteBlockIndex k 0)
      (finiteBlockIndex i q)
      (finiteBlockIndex_ne_of_ne hik p 0)
      (finiteBlockIndex_ne_of_ne hik.symm 0 q)
      hxy a
      (elementaryUnit_mem_cyclicFiniteBlockRootSubgroup_of_block_ne
        W hW i k hik p 0 a ha)
      (elementaryUnit_mem_cyclicFiniteBlockRootSubgroup_of_block_ne
        W hW k i hik.symm 0 q 1 hW)
  · exact elementaryUnit_mem_cyclicFiniteBlockRootSubgroup_of_block_ne
      W hW i j hij p q a ha

theorem cyclicFiniteBlockRootSubgroup_eq_elementaryGroup
    (s : Finset R)
    (hs : Algebra.adjoin (ZMod 2) (↑s : Set R) = ⊤) :
    cyclicFiniteBlockRootSubgroup (finiteBlockCoefficientSpan s) =
      elementaryGroup (Fin 9) R := by
  let W : Submodule (ZMod 2) R := finiteBlockCoefficientSpan s
  let H : Subgroup (Matrix (Fin 9) (Fin 9) R)ˣ :=
    cyclicFiniteBlockRootSubgroup W
  have hW : (1 : R) ∈ W := one_mem_finiteBlockCoefficientSpan s
  have hunit : ∀ (i j : Fin 9) (hij : i ≠ j),
      elementaryUnit i j hij (1 : R) ∈ H := by
    intro i j hij
    exact elementaryUnit_mem_cyclicFiniteBlockRootSubgroup
      W hW i j hij 1 hW
  let C : Subalgebra (ZMod 2) R :=
    elementaryCoefficientSubalgebra 9 (by decide) H hunit
  have hgen : (↑s : Set R) ⊆ (C : Set R) := by
    intro a ha
    change ∀ (i j : Fin 9) (hij : i ≠ j),
      elementaryUnit i j hij a ∈ H
    intro i j hij
    exact elementaryUnit_mem_cyclicFiniteBlockRootSubgroup
      W hW i j hij a
      (mem_finiteBlockCoefficientSpan_of_mem s ha)
  have hC : C = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Algebra.adjoin_le hgen
  change H = elementaryGroup (Fin 9) R
  apply le_antisymm
  · exact cyclicFiniteBlockRootSubgroup_le_elementaryGroup W
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    have ha : a ∈ C := by simp only [hC, Algebra.mem_top]
    exact ha i j hij

end FiniteBlockRoots

end

section

open scoped BigOperators

universe vSharp

theorem hasPropertyT_of_finiteOuterBlockCyclicRootFamily_generate
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    (W : Submodule (ZMod 2) R) [Finite W]
    (hgen :
      (⨆ i : Fin 3, finiteOuterBlockCyclicRootFamily W i) = ⊤) :
    HasPropertyT.{_, vSharp}
      (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) := by
  classical
  have hfinite (i : Fin 3) :
      Finite (finiteOuterBlockCyclicRootFamily W i) := by
    fin_cases i
    · exact finite_finiteOuterBlockRootSubgroup W 0 1 (by decide)
    · exact finite_finiteOuterBlockRootSubgroup W 1 2 (by decide)
    · exact finite_finiteOuterBlockRootSubgroup W 2 0 (by decide)
  let (i : Fin 3) : Finite (finiteOuterBlockCyclicRootFamily W i) :=
    hfinite i
  let (i : Fin 3) : Fintype (finiteOuterBlockCyclicRootFamily W i) :=
    Fintype.ofFinite _
  apply ErshovJaikinFiniteSpectral.hasPropertyT_of_three_finite_subgroups_friedrichs_angle
    (finiteOuterBlockCyclicRootFamily W) hgen
    (Real.sqrt (8 : ℝ))⁻¹
    (le_of_lt ErshovJaikinFiniteSpectral.inv_sqrt_eight_pos)
    ErshovJaikinFiniteSpectral.inv_sqrt_eight_lt_one_half
  intro H _ _ _ π i j hij a b ha haQ hb hbQ
  have hfixed
      (K : Subgroup
        (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))) :
      unitaryFixedSubmodule π K = ejUnitaryFixedSubmodule π K := by
    ext z
    rfl
  rw [← hfixed] at ha haQ hb hbQ
  exact ErshovJaikinFiniteSpectral.norm_inner_le_inv_sqrt_eight_of_sq a b
    (finiteOuterBlockCyclicRootFamily_pair_inner_sq_le
      W π i j hij a b ha haQ hb hbQ)

end

section

open scoped BigOperators

universe vSharp

def finiteOuterBlockFlattenHom
    {R : Type*} [Ring R] :
    elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) →*
      (Matrix (Fin 9) (Fin 9) R)ˣ :=
  (Units.mapEquiv (finiteBlockFlattenRingEquiv (R := R)).toMulEquiv).toMonoidHom.comp
    (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)).subtype

theorem finiteOuterBlockRootSubgroup_map_flatten
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    (W : Submodule (ZMod 2) R)
    (i j : Fin 3) (hij : i ≠ j) :
    (finiteOuterBlockRootSubgroup W i j hij).map
      (finiteOuterBlockFlattenHom (R := R)) =
        finiteBlockRootSubgroup W i j hij := by
  change (finiteOuterBlockRootHom W i j hij).range.map
    (finiteOuterBlockFlattenHom (R := R)) =
      (finiteBlockRootHom W i j hij).range
  rw [MonoidHom.map_range]
  rfl

theorem finiteOuterBlockCyclicRootFamily_iSup_eq_top
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    (s : Finset R)
    (hs : Algebra.adjoin (ZMod 2) (↑s : Set R) = ⊤) :
    (⨆ i : Fin 3,
      finiteOuterBlockCyclicRootFamily (finiteBlockCoefficientSpan s) i) =
        ⊤ := by
  let W : Submodule (ZMod 2) R := finiteBlockCoefficientSpan s
  let L : Subgroup
      (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) :=
    finiteOuterBlockRootSubgroup W 0 1 (by decide) ⊔
      finiteOuterBlockRootSubgroup W 1 2 (by decide) ⊔
        finiteOuterBlockRootSubgroup W 2 0 (by decide)
  let φ := finiteOuterBlockFlattenHom (R := R)
  have hmap :
      L.map φ = elementaryGroup (Fin 9) R := by
    calc
      L.map φ = cyclicFiniteBlockRootSubgroup W := by
        dsimp [L, φ]
        rw [Subgroup.map_sup, Subgroup.map_sup,
          finiteOuterBlockRootSubgroup_map_flatten,
          finiteOuterBlockRootSubgroup_map_flatten,
          finiteOuterBlockRootSubgroup_map_flatten]
        rfl
      _ = elementaryGroup (Fin 9) R := by
        exact cyclicFiniteBlockRootSubgroup_eq_elementaryGroup s hs
  let e :
      elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) ≃*
        elementaryGroup (Fin 9) R :=
    (LeavittElementaryMorita.elementaryBlockGroupEquiv
      (ι := Fin 3) (κ := Fin 3) (R := R)).trans
      (LeavittElementaryMorita.elementaryReindexGroupEquiv
        (R := R) (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9))
  have hcompat
      (x : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) :
      (e x : (Matrix (Fin 9) (Fin 9) R)ˣ) = φ x := by
    rfl
  have hinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    exact (Units.mapEquiv
      (finiteBlockFlattenRingEquiv (R := R)).toMulEquiv).injective hxy
  have hLtop : L = ⊤ := by
    apply top_unique
    intro x _
    have hx :
        φ x ∈ elementaryGroup (Fin 9) R := by
      rw [← hcompat]
      exact (e x).property
    rw [← hmap] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have heq : z = x := hinj hzx
    simpa only [heq, SetLike.mem_coe] using hz
  apply top_unique
  rw [← hLtop]
  dsimp [L, W]
  exact sup_le
    (sup_le
      (le_iSup (finiteOuterBlockCyclicRootFamily
        (finiteBlockCoefficientSpan s)) 0)
      (le_iSup (finiteOuterBlockCyclicRootFamily
        (finiteBlockCoefficientSpan s)) 1))
    (le_iSup (finiteOuterBlockCyclicRootFamily
      (finiteBlockCoefficientSpan s)) 2)

theorem binaryLeavittElementaryNine_hasPropertyT_unconditional :
    HasPropertyT.{0, vSharp} (binaryLeavittElementaryGroup 9) := by
  classical
  obtain ⟨s, hs⟩ :=
    Algebra.FiniteType.out (R := ZMod 2) (A := BinaryLeavitt)
  let : HasPropertyT.{0, vSharp}
      (elementaryGroup (Fin 3)
        (Matrix (Fin 3) (Fin 3) BinaryLeavitt)) :=
    hasPropertyT_of_finiteOuterBlockCyclicRootFamily_generate
      (finiteBlockCoefficientSpan s)
      (finiteOuterBlockCyclicRootFamily_iSup_eq_top s hs)
  exact hasPropertyT_of_mulEquiv
    ((LeavittElementaryMorita.elementaryBlockGroupEquiv
      (ι := Fin 3) (κ := Fin 3) (R := BinaryLeavitt)).trans
      (LeavittElementaryMorita.elementaryReindexGroupEquiv
        (R := BinaryLeavitt)
        (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9)))

theorem alphaPrefixElementaryGroup_hasPropertyT_unconditional :
    HasPropertyT.{0, vSharp} (prefixElementaryGroup alphaPrefixCode) := by
  let : HasPropertyT.{0, vSharp} (binaryLeavittElementaryGroup 9) :=
    binaryLeavittElementaryNine_hasPropertyT_unconditional
  exact LeavittElementaryMorita.alphaPrefixElementaryGroup_hasPropertyT_of_nine

theorem alphaZeroPrefixElementaryGroup_hasPropertyT_unconditional :
    HasPropertyT.{0, vSharp} (prefixElementaryGroup alphaZeroPrefixCode) := by
  let : HasPropertyT.{0, vSharp} (binaryLeavittElementaryGroup 9) :=
    binaryLeavittElementaryNine_hasPropertyT_unconditional
  exact LeavittElementaryMorita.alphaZeroPrefixElementaryGroup_hasPropertyT_of_nine

theorem ninePrefixElementaryGroup_hasPropertyT_unconditional :
    HasPropertyT.{0, vSharp} (prefixElementaryGroup ninePrefixCode) := by
  let : HasPropertyT.{0, vSharp} (binaryLeavittElementaryGroup 9) :=
    binaryLeavittElementaryNine_hasPropertyT_unconditional
  exact hasPropertyT_of_mulEquiv ninePrefixElementaryGroupEquiv

end

namespace KunThomFiberCoarea

def firstFiber {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) : Finset (V × V) :=
  U.filter (fun z => z.1 = x)

def secondFiber {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) : Finset (V × V) :=
  U.filter (fun z => z.2 = x)

def firstMultiplicity {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) : ℕ :=
  (firstFiber U x).card

def secondMultiplicity {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) : ℕ :=
  (secondFiber U x).card

def projFiber {V : Type*} [DecidableEq V] (π : V × V → V)
    (U : Finset (V × V)) (x : V) : Finset (V × V) :=
  U.filter (fun z => π z = x)

theorem sum_projFiber_card {V : Type*} [Fintype V] [DecidableEq V]
    (π : V × V → V) (U : Finset (V × V)) :
    (∑ x : V, (projFiber π U x).card) = U.card := by
  classical
  simpa only [projFiber] using
    (Finset.card_eq_sum_card_fiberwise (f := π) (s := U) (t := Finset.univ) (fun _ _ =>
      Finset.mem_univ _)).symm

theorem sum_firstFiber_card {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (∑ x : V, (firstFiber U x).card) = U.card :=
  sum_projFiber_card Prod.fst U

theorem sum_secondFiber_card {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (∑ x : V, (secondFiber U x).card) = U.card :=
  sum_projFiber_card Prod.snd U

theorem natDist_card_le_sdiff {α : Type*} [DecidableEq α]
    (A B : Finset α) :
    Nat.dist A.card B.card ≤ (A \ B).card + (B \ A).card := by
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  have hinter : (A ∩ B).card = (B ∩ A).card := by
    rw [Finset.inter_comm]
  by_cases h : A.card ≤ B.card
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_not_ge h)]
    omega

theorem projFiber_sdiff {V : Type*} [DecidableEq V]
    (π : V × V → V) (U W : Finset (V × V)) (x : V) :
    projFiber π (U \ W) x = projFiber π U x \ projFiber π W x := by
  classical
  ext z
  simp only [projFiber, Finset.mem_filter, Finset.mem_sdiff]
  aesop

theorem projMultiplicity_variation_le_relation_difference
    {V : Type*} [Fintype V] [DecidableEq V]
    (π : V × V → V) (U W : Finset (V × V)) :
    (∑ x : V, Nat.dist (projFiber π U x).card
      (projFiber π W x).card) ≤
        (U \ W).card + (W \ U).card := by
  classical
  calc
    (∑ x : V, Nat.dist (projFiber π U x).card
      (projFiber π W x).card) ≤
        ∑ x : V,
          ((projFiber π U x \ projFiber π W x).card +
            (projFiber π W x \ projFiber π U x).card) := by
          apply Finset.sum_le_sum
          intro x _
          exact natDist_card_le_sdiff (projFiber π U x) (projFiber π W x)
    _ = (∑ x : V, (projFiber π (U \ W) x).card) +
          (∑ x : V, (projFiber π (W \ U) x).card) := by
          simp_rw [projFiber_sdiff]
          rw [Finset.sum_add_distrib]
    _ = (U \ W).card + (W \ U).card := by
          rw [sum_projFiber_card, sum_projFiber_card]

theorem firstMultiplicity_variation_le_relation_difference
    {V : Type*} [Fintype V] [DecidableEq V]
    (U W : Finset (V × V)) :
    (∑ x : V, Nat.dist (firstMultiplicity U x)
      (firstMultiplicity W x)) ≤
        (U \ W).card + (W \ U).card :=
  projMultiplicity_variation_le_relation_difference Prod.fst U W

theorem secondMultiplicity_variation_le_relation_difference
    {V : Type*} [Fintype V] [DecidableEq V]
    (U W : Finset (V × V)) :
    (∑ x : V, Nat.dist (secondMultiplicity U x)
      (secondMultiplicity W x)) ≤
        (U \ W).card + (W \ U).card :=
  projMultiplicity_variation_le_relation_difference Prod.snd U W

def diagonalImage {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) : Finset (V × V) :=
  U.image (p.prodCongr p)

def diagonalExit {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) : ℕ :=
  (U.filter fun z => (p.prodCongr p) z ∉ U).card

theorem diagonalImage_card {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) :
    (diagonalImage p U).card = U.card := by
  exact Finset.card_image_of_injective U (p.prodCongr p).injective

theorem projFiber_diagonalImage {V : Type*} [DecidableEq V]
    (π : V × V → V) (p : Equiv.Perm V)
    (hπ : ∀ z : V × V, π ((p.prodCongr p) z) = p (π z))
    (U : Finset (V × V)) (x : V) :
    projFiber π (diagonalImage p U) (p x) =
      (projFiber π U x).image (p.prodCongr p) := by
  classical
  ext z
  simp only [projFiber, diagonalImage, Finset.mem_filter,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, hzw⟩, hzproj⟩
    refine ⟨w, ⟨hw, ?_⟩, hzw⟩
    apply p.injective
    rw [← hπ w, hzw]
    exact hzproj
  · rintro ⟨w, ⟨hw, hwproj⟩, hzw⟩
    refine ⟨⟨w, hw, hzw⟩, ?_⟩
    rw [← hzw, hπ w, hwproj]

theorem projMultiplicity_diagonalImage {V : Type*} [DecidableEq V]
    (π : V × V → V) (p : Equiv.Perm V)
    (hπ : ∀ z : V × V, π ((p.prodCongr p) z) = p (π z))
    (U : Finset (V × V)) (x : V) :
    (projFiber π (diagonalImage p U) (p x)).card =
      (projFiber π U x).card := by
  rw [projFiber_diagonalImage π p hπ U x]
  exact Finset.card_image_of_injective _ (p.prodCongr p).injective

theorem diagonalImage_sdiff_eq_image_exit {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) :
    diagonalImage p U \ U =
      (U.filter fun z => (p.prodCongr p) z ∉ U).image
        (p.prodCongr p) := by
  classical
  ext z
  simp only [diagonalImage, Finset.mem_sdiff, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨w, hw, hzw⟩, hzout⟩
    exact ⟨w, ⟨hw, by simpa only [hzw] using hzout⟩, hzw⟩
  · rintro ⟨w, ⟨hw, hwout⟩, hzw⟩
    exact ⟨⟨w, hw, hzw⟩, by simpa only [← hzw, Equiv.prodCongr_apply] using hwout⟩

theorem diagonalImage_sdiff_cards {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) :
    (diagonalImage p U \ U).card = diagonalExit p U ∧
      (U \ diagonalImage p U).card = diagonalExit p U := by
  have hforward : (diagonalImage p U \ U).card = diagonalExit p U := by
    rw [diagonalImage_sdiff_eq_image_exit]
    exact Finset.card_image_of_injective _ (p.prodCongr p).injective
  have hU := Finset.card_sdiff_add_card_inter U (diagonalImage p U)
  have hI := Finset.card_sdiff_add_card_inter (diagonalImage p U) U
  have hinter : (U ∩ diagonalImage p U).card =
      (diagonalImage p U ∩ U).card := by
    rw [Finset.inter_comm]
  have hcard := diagonalImage_card p U
  exact ⟨hforward, by omega⟩

theorem projMultiplicity_diagonal_variation_le_twice_exit
    {V : Type*} [Fintype V] [DecidableEq V]
    (π : V × V → V) (p : Equiv.Perm V)
    (hπ : ∀ z : V × V, π ((p.prodCongr p) z) = p (π z))
    (U : Finset (V × V)) :
    (∑ x : V, Nat.dist (projFiber π U (p x)).card
      (projFiber π U x).card) ≤ 2 * diagonalExit p U := by
  classical
  calc
    (∑ x : V, Nat.dist (projFiber π U (p x)).card
      (projFiber π U x).card) =
        ∑ x : V, Nat.dist (projFiber π U (p x)).card
          (projFiber π (diagonalImage p U) (p x)).card := by
          apply Finset.sum_congr rfl
          intro x _
          rw [projMultiplicity_diagonalImage π p hπ U x]
    _ = ∑ x : V, Nat.dist (projFiber π U x).card
          (projFiber π (diagonalImage p U) x).card :=
          Equiv.sum_comp p (fun x =>
            Nat.dist (projFiber π U x).card
              (projFiber π (diagonalImage p U) x).card)
    _ ≤ (U \ diagonalImage p U).card +
          (diagonalImage p U \ U).card :=
          projMultiplicity_variation_le_relation_difference
            π U (diagonalImage p U)
    _ = 2 * diagonalExit p U := by
          obtain ⟨hforward, hbackward⟩ := diagonalImage_sdiff_cards p U
          rw [hforward, hbackward]
          omega

theorem projMultiplicity_totalVariation_le_twice_diagonalBoundary
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (π : V × V → V) (σ : ι → Equiv.Perm V)
    (hπ : ∀ (p : Equiv.Perm V) (z : V × V),
      π ((p.prodCongr p) z) = p (π z))
    (U : Finset (V × V)) :
    (∑ i : ι, ∑ x : V,
      Nat.dist (projFiber π U (σ i x)).card
        (projFiber π U x).card) ≤
          2 * boundary
            (fun i => (σ i).prodCongr (σ i)) U := by
  classical
  calc
    (∑ i : ι, ∑ x : V,
      Nat.dist (projFiber π U (σ i x)).card
        (projFiber π U x).card) ≤
        ∑ i : ι, 2 * diagonalExit (σ i) U := by
          apply Finset.sum_le_sum
          intro i _
          exact projMultiplicity_diagonal_variation_le_twice_exit
            π (σ i) (hπ (σ i)) U
    _ = 2 * boundary
          (fun i => (σ i).prodCongr (σ i)) U := by
          simp only [diagonalExit, Equiv.prodCongr_apply, boundary, Finset.mul_sum]

theorem firstMultiplicity_totalVariation_le_twice_diagonalBoundary
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V)) :
    (∑ i : ι, ∑ x : V,
      Nat.dist (firstMultiplicity U (σ i x))
        (firstMultiplicity U x)) ≤
          2 * boundary
            (fun i => (σ i).prodCongr (σ i)) U :=
  projMultiplicity_totalVariation_le_twice_diagonalBoundary
    Prod.fst σ (fun _ _ => rfl) U

theorem secondMultiplicity_totalVariation_le_twice_diagonalBoundary
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V)) :
    (∑ i : ι, ∑ x : V,
      Nat.dist (secondMultiplicity U (σ i x))
        (secondMultiplicity U x)) ≤
          2 * boundary
            (fun i => (σ i).prodCongr (σ i)) U :=
  projMultiplicity_totalVariation_le_twice_diagonalBoundary
    Prod.snd σ (fun _ _ => rfl) U

def permutationVariation {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℕ) : ℕ :=
  ∑ i : ι, ∑ x : V, Nat.dist (f (σ i x)) (f x)

def positiveNatSupport {V : Type*} [Fintype V]
    (f : V → ℕ) : Finset V :=
  Finset.univ.filter (fun x => 0 < f x)

@[simp]
theorem mem_positiveNatSupport {V : Type*} [Fintype V]
    (f : V → ℕ) (x : V) :
    x ∈ positiveNatSupport f ↔ 0 < f x := by
  simp only [positiveNatSupport, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_entering_eq_card_exiting
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (A : Finset V) :
    (Finset.univ.filter fun x => x ∉ A ∧ p x ∈ A).card =
      (A.filter fun x => p x ∉ A).card := by
  classical
  let P : Finset V := Finset.univ.filter fun x => p x ∈ A
  have hP : P.card = A.card := by
    apply Finset.card_bij (fun x _ => p x)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x _ y _ hxy
      exact p.injective hxy
    · intro y hy
      refine ⟨p.symm y, ?_, by simp only [Equiv.apply_symm_apply]⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simpa only [Equiv.apply_symm_apply] using hy⟩
  have hsplitA :=
    Finset.card_filter_add_card_filter_not (s := A)
      (fun x => p x ∈ A)
  have hsplitP :=
    Finset.card_filter_add_card_filter_not (s := P)
      (fun x => x ∈ A)
  have hinternal :
      (P.filter fun x => x ∈ A).card =
        (A.filter fun x => p x ∈ A).card := by
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm, P]
  have henter :
      (P.filter fun x => x ∉ A).card =
        (Finset.univ.filter fun x => x ∉ A ∧ p x ∈ A).card := by
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm, P]
  omega

theorem sum_indicator_nat_eq_mul_card
    {V : Type*}
    (A : Finset V) (q : V → Prop) [DecidablePred q] (m : ℕ) :
    (∑ x ∈ A, if q x then m else 0) =
      m * (A.filter q).card := by
  calc
    (∑ x ∈ A, if q x then m else 0) =
        m * (∑ x ∈ A, if q x then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          split <;> simp
    _ = m * (A.filter q).card := by
          congr 1
          exact Finset.sum_boole (R := ℕ) q A

theorem permutationVariation_subtract_layer
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (f : V → ℕ)
    (A : Finset V) (m : ℕ)
    (hinside : ∀ x ∈ A, m ≤ f x)
    (houtside : ∀ x, x ∉ A → f x = 0) :
    permutationVariation σ f =
      permutationVariation σ
          (fun x => if x ∈ A then f x - m else 0) +
        2 * m * boundary σ A := by
  classical
  let g : V → ℕ := fun x => if x ∈ A then f x - m else 0
  have hpair (i : ι) (x : V) :
      Nat.dist (f (σ i x)) (f x) =
        Nat.dist (g (σ i x)) (g x) +
          (if x ∈ A ∧ σ i x ∉ A then m else 0) +
          (if x ∉ A ∧ σ i x ∈ A then m else 0) := by
    by_cases hx : x ∈ A
    · by_cases hy : σ i x ∈ A
      · have hxlow := hinside x hx
        have hylow := hinside (σ i x) hy
        simp only [Nat.dist, hy, ↓reduceIte, hx, not_true_eq_false, and_false, add_zero, and_true,
          g]
        omega
      · have hyzero := houtside (σ i x) hy
        have hxlow := hinside x hx
        simp only [Nat.dist, hyzero, zero_tsub, tsub_zero, zero_add, hy, ↓reduceIte, hx,
          not_false_eq_true, and_self,
          not_true_eq_false, add_zero, g]
        omega
    · by_cases hy : σ i x ∈ A
      · have hxzero := houtside x hx
        have hylow := hinside (σ i x) hy
        simp only [Nat.dist, hxzero, tsub_zero, zero_tsub, add_zero, hy, ↓reduceIte, hx,
          not_true_eq_false, and_self,
          not_false_eq_true, g]
        omega
      · simp only [houtside (σ i x) hy, houtside x hx, Nat.dist_self, hy, ↓reduceIte, hx,
        not_false_eq_true, and_true,
          add_zero, and_false, g]
  have hone (i : ι) :
      (∑ x : V, Nat.dist (f (σ i x)) (f x)) =
        (∑ x : V, Nat.dist (g (σ i x)) (g x)) +
          2 * m * (A.filter fun x => σ i x ∉ A).card := by
    have hexit :
        (∑ x : V, if x ∈ A ∧ σ i x ∉ A then m else 0) =
          m * (A.filter fun x => σ i x ∉ A).card := by
      have hset :
          Finset.univ.filter
              (fun x : V => x ∈ A ∧ σ i x ∉ A) =
            A.filter fun x => σ i x ∉ A := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [hset] using
        sum_indicator_nat_eq_mul_card Finset.univ
          (fun x : V => x ∈ A ∧ σ i x ∉ A) m
    have henter :
        (∑ x : V, if x ∉ A ∧ σ i x ∈ A then m else 0) =
          m * (Finset.univ.filter fun x =>
            x ∉ A ∧ σ i x ∈ A).card :=
      sum_indicator_nat_eq_mul_card
        Finset.univ (fun x => x ∉ A ∧ σ i x ∈ A) m
    calc
      (∑ x : V, Nat.dist (f (σ i x)) (f x)) =
          ∑ x : V,
            (Nat.dist (g (σ i x)) (g x) +
              (if x ∈ A ∧ σ i x ∉ A then m else 0) +
              (if x ∉ A ∧ σ i x ∈ A then m else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            exact hpair i x
      _ = (∑ x : V, Nat.dist (g (σ i x)) (g x)) +
            (∑ x : V, if x ∈ A ∧ σ i x ∉ A then m else 0) +
            (∑ x : V, if x ∉ A ∧ σ i x ∈ A then m else 0) := by
            simp_rw [Finset.sum_add_distrib]
      _ = (∑ x : V, Nat.dist (g (σ i x)) (g x)) +
            m * (A.filter fun x => σ i x ∉ A).card +
            m * (Finset.univ.filter fun x =>
              x ∉ A ∧ σ i x ∈ A).card := by
            rw [hexit, henter]
      _ = (∑ x : V, Nat.dist (g (σ i x)) (g x)) +
            2 * m * (A.filter fun x => σ i x ∉ A).card := by
            rw [card_entering_eq_card_exiting]
            ring
  unfold permutationVariation boundary
  calc
    (∑ i : ι, ∑ x : V, Nat.dist (f (σ i x)) (f x)) =
        ∑ i : ι,
          ((∑ x : V, Nat.dist (g (σ i x)) (g x)) +
            2 * m * (A.filter fun x => σ i x ∉ A).card) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hone i
    _ = (∑ i : ι, ∑ x : V,
          Nat.dist (g (σ i x)) (g x)) +
          2 * m *
            ∑ i : ι, (A.filter fun x => σ i x ∉ A).card := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem permutation_small_support_coarea
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (f : V → ℕ)
    (hhalf : 2 * (positiveNatSupport f).card ≤ Fintype.card V) :
    2 * h * (∑ x : V, f x) ≤
      (permutationVariation σ f : ℝ) := by
  classical
  generalize hn : (positiveNatSupport f).card = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hnonempty : (positiveNatSupport f).Nonempty
    · let A : Finset V := positiveNatSupport f
      have hA : A.Nonempty := hnonempty
      have himage : (A.image f).Nonempty := Finset.image_nonempty.mpr hA
      let m : ℕ := (A.image f).min' himage
      have hm_mem : m ∈ A.image f := Finset.min'_mem _ _
      obtain ⟨z, hzA, hzm⟩ := Finset.mem_image.mp hm_mem
      have hmpos : 0 < m := by
        rw [← hzm]
        exact (mem_positiveNatSupport f z).mp hzA
      have hm_le : ∀ x ∈ A, m ≤ f x := by
        intro x hx
        exact Finset.min'_le (A.image f) (f x)
          (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      let g : V → ℕ := fun x => if x ∈ A then f x - m else 0
      have hg_sub : positiveNatSupport g ⊆ A := by
        intro x hx
        have hxpos := (mem_positiveNatSupport g x).mp hx
        by_contra hxA
        simp only [hxA, ↓reduceIte, lt_self_iff_false, g] at hxpos
      have hz_not : z ∉ positiveNatSupport g := by
        intro hz
        have hzpos := (mem_positiveNatSupport g z).mp hz
        have hzero : g z = 0 := by
          simp only [hzA, ↓reduceIte, hzm, tsub_self, g]
        simp only [hzero, lt_self_iff_false] at hzpos
      have hstrict : positiveNatSupport g ⊂ A := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hg_sub, ?_⟩
        intro heq
        exact hz_not (heq.symm ▸ hzA)
      have hg_card : (positiveNatSupport g).card < n := by
        rw [← hn]
        exact Finset.card_lt_card hstrict
      have hg_half :
          2 * (positiveNatSupport g).card ≤ Fintype.card V :=
        (Nat.mul_le_mul_left 2 (Finset.card_le_card hg_sub)).trans hhalf
      have hg_bound :
          2 * h * (∑ x : V, g x) ≤
            (permutationVariation σ g : ℝ) :=
        ih (positiveNatSupport g).card hg_card g hg_half rfl
      have hg_bound' :
          2 * h * (∑ x : V, (g x : ℝ)) ≤
            (permutationVariation σ g : ℝ) := by
        simpa only [Nat.cast_sum] using hg_bound
      have hhalf_real :
          (2 : ℝ) * A.card ≤ Fintype.card V := by
        exact_mod_cast hhalf
      have hmin :
          (A.card : ℝ) ≤ (Fintype.card V : ℝ) - A.card := by
        linarith
      have hcut :
          h * (A.card : ℝ) ≤
            (boundary σ A : ℝ) := by
        simpa only [min_eq_left hmin] using hexp A
      have houtside : ∀ x, x ∉ A → f x = 0 := by
        intro x hx
        have hxnot : ¬ 0 < f x := by
          intro hpos
          exact hx ((mem_positiveNatSupport f x).mpr hpos)
        omega
      have hsum :
          (∑ x : V, f x) =
            (∑ x : V, g x) + m * A.card := by
        calc
          (∑ x : V, f x) =
              ∑ x : V, (g x + if x ∈ A then m else 0) := by
                apply Finset.sum_congr rfl
                intro x _
                by_cases hx : x ∈ A
                · have hxlow := hm_le x hx
                  simp only [hx, ↓reduceIte, g]
                  omega
                · simp only [houtside x hx, hx, ↓reduceIte, add_zero, g]
          _ = (∑ x : V, g x) +
                (∑ x : V, if x ∈ A then m else 0) := by
                rw [Finset.sum_add_distrib]
          _ = (∑ x : V, g x) + m * A.card := by
                rw [sum_indicator_nat_eq_mul_card]
                simp only [Finset.subset_univ, Finset.filter_mem_eq_of_subset]
      have hvar :
          permutationVariation σ f =
            permutationVariation σ g +
              2 * m * boundary σ A :=
        permutationVariation_subtract_layer
          σ f A m hm_le houtside
      calc
        2 * h * (∑ x : V, f x) =
            2 * h *
              ((∑ x : V, (g x : ℝ)) +
                (m : ℝ) * (A.card : ℝ)) := by
              rw [hsum]
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum]
        _ = 2 * h * (∑ x : V, (g x : ℝ)) +
              (2 * (m : ℝ)) * (h * (A.card : ℝ)) := by
              ring
        _ ≤ (permutationVariation σ g : ℝ) +
              (2 * (m : ℝ)) *
                (boundary σ A : ℝ) := by
              apply add_le_add hg_bound'
              exact mul_le_mul_of_nonneg_left hcut (by positivity)
        _ = (permutationVariation σ f : ℝ) := by
              exact_mod_cast hvar.symm
    · have hzero : ∀ x, f x = 0 := by
        intro x
        by_contra hx
        apply hnonempty
        refine ⟨x, (mem_positiveNatSupport f x).mpr ?_⟩
        exact Nat.pos_of_ne_zero hx
      simp only [hzero, Finset.sum_const_zero, CharP.cast_eq_zero, mul_zero, permutationVariation,
        Nat.dist_self,
        Std.le_refl]

theorem natDist_sub_one_le (a b : ℕ) :
    Nat.dist (a - 1) (b - 1) ≤ Nat.dist a b := by
  simp only [Nat.dist]
  omega

theorem natDist_zero_indicator_le (a b : ℕ) :
    Nat.dist (if a = 0 then 1 else 0)
      (if b = 0 then 1 else 0) ≤ Nat.dist a b := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · simp only [ha, ↓reduceIte, hb, Nat.dist_self, Std.le_refl]
    · simp only [Nat.dist, ha, ↓reduceIte, hb, tsub_zero, zero_tsub, add_zero, zero_add]
      omega
  · by_cases hb : b = 0
    · simp only [Nat.dist, ha, ↓reduceIte, hb, zero_tsub, tsub_zero, zero_add, add_zero]
      omega
    · simp only [ha, ↓reduceIte, hb, Nat.dist_self, zero_le]

theorem permutationVariation_sub_one_le
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℕ) :
    permutationVariation σ (fun x => f x - 1) ≤
      permutationVariation σ f := by
  unfold permutationVariation
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro x _
  exact natDist_sub_one_le (f (σ i x)) (f x)

theorem permutationVariation_zero_indicator_le
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℕ) :
    permutationVariation σ (fun x => if f x = 0 then 1 else 0) ≤
      permutationVariation σ f := by
  unfold permutationVariation
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro x _
  exact natDist_zero_indicator_le (f (σ i x)) (f x)

def singletonSupport {V : Type*} [Fintype V]
    (f : V → ℕ) : Finset V :=
  Finset.univ.filter (fun x => f x = 1)

@[simp]
theorem mem_singletonSupport {V : Type*} [Fintype V]
    (f : V → ℕ) (x : V) :
    x ∈ singletonSupport f ↔ f x = 1 := by
  simp only [singletonSupport, Finset.mem_filter, Finset.mem_univ, true_and]

theorem excess_support_card_le_half_of_singletons
    {V : Type*} [Fintype V]
    (f : V → ℕ)
    (hsingle : Fintype.card V ≤ 2 * (singletonSupport f).card) :
    2 * (positiveNatSupport (fun x => f x - 1)).card ≤
      Fintype.card V := by
  classical
  have hsub :
      positiveNatSupport (fun x => f x - 1) ⊆
        Finset.univ \ singletonSupport f := by
    intro x hx
    have hxpos :=
      (mem_positiveNatSupport (fun x => f x - 1) x).mp hx
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hxone
    have hone := (mem_singletonSupport f x).mp hxone
    simp only [hone, tsub_self, lt_self_iff_false] at hxpos
  have hcard := Finset.card_le_card hsub
  have hpartition := Finset.card_sdiff_add_card_inter
    (Finset.univ : Finset V) (singletonSupport f)
  have hinter :
      ((Finset.univ : Finset V) ∩ singletonSupport f).card =
        (singletonSupport f).card := by
    simp only [Finset.univ_inter]
  have huniv : (Finset.univ : Finset V).card = Fintype.card V := by
    rfl
  omega

theorem zero_support_card_le_half_of_singletons
    {V : Type*} [Fintype V]
    (f : V → ℕ)
    (hsingle : Fintype.card V ≤ 2 * (singletonSupport f).card) :
    2 * (positiveNatSupport
      (fun x => if f x = 0 then 1 else 0)).card ≤
        Fintype.card V := by
  classical
  have hsub :
      positiveNatSupport (fun x => if f x = 0 then 1 else 0) ⊆
        Finset.univ \ singletonSupport f := by
    intro x hx
    have hxpos :=
      (mem_positiveNatSupport
        (fun x => if f x = 0 then 1 else 0) x).mp hx
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hxone
    have hone := (mem_singletonSupport f x).mp hxone
    simp only [hone, one_ne_zero, ↓reduceIte, lt_self_iff_false] at hxpos
  have hcard := Finset.card_le_card hsub
  have hpartition := Finset.card_sdiff_add_card_inter
    (Finset.univ : Finset V) (singletonSupport f)
  have hinter :
      ((Finset.univ : Finset V) ∩ singletonSupport f).card =
        (singletonSupport f).card := by
    simp only [Finset.univ_inter]
  have huniv : (Finset.univ : Finset V).card = Fintype.card V := by
    rfl
  omega

theorem excess_mass_le_of_diagonal_variation
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (f : V → ℕ) (B : ℕ)
    (hsingle : Fintype.card V ≤ 2 * (singletonSupport f).card)
    (hvariation : permutationVariation σ f ≤ 2 * B) :
    h * (∑ x : V, (f x - 1 : ℕ)) ≤ (B : ℝ) := by
  have hhalf := excess_support_card_le_half_of_singletons f hsingle
  have hcoarea := permutation_small_support_coarea
    σ h hexp (fun x => f x - 1) hhalf
  have hcontract := permutationVariation_sub_one_le σ f
  have htotal :
      permutationVariation σ (fun x => f x - 1) ≤ 2 * B :=
    hcontract.trans hvariation
  have htotal_real :
      (permutationVariation σ (fun x => f x - 1) : ℝ) ≤
        2 * (B : ℝ) := by
    exact_mod_cast htotal
  linarith

theorem zero_mass_le_of_diagonal_variation
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (f : V → ℕ) (B : ℕ)
    (hsingle : Fintype.card V ≤ 2 * (singletonSupport f).card)
    (hvariation : permutationVariation σ f ≤ 2 * B) :
    h * (Finset.univ.filter fun x : V => f x = 0).card ≤
      (B : ℝ) := by
  have hhalf := zero_support_card_le_half_of_singletons f hsingle
  have hcoarea := permutation_small_support_coarea
    σ h hexp (fun x => if f x = 0 then 1 else 0) hhalf
  have hcontract := permutationVariation_zero_indicator_le σ f
  have htotal :
      permutationVariation σ (fun x => if f x = 0 then 1 else 0) ≤
        2 * B := hcontract.trans hvariation
  have htotal_real :
      (permutationVariation σ
        (fun x => if f x = 0 then 1 else 0) : ℝ) ≤
          2 * (B : ℝ) := by
    exact_mod_cast htotal
  have hsum :
      (∑ x : V, if f x = 0 then 1 else 0) =
        (Finset.univ.filter fun x : V => f x = 0).card := by
    simp only [Finset.sum_boole, Nat.cast_id]
  rw [hsum] at hcoarea
  linarith

theorem first_excess_mass_le_diagonalBoundary
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V)) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (hsingle : Fintype.card V ≤
      2 * (singletonSupport (firstMultiplicity U)).card) :
    h * (∑ x : V, (firstMultiplicity U x - 1 : ℕ)) ≤
      (boundary
        (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  apply excess_mass_le_of_diagonal_variation
    σ h hexp (firstMultiplicity U)
      (boundary
        (fun i => (σ i).prodCongr (σ i)) U) hsingle
  exact firstMultiplicity_totalVariation_le_twice_diagonalBoundary
    σ U

theorem second_excess_mass_le_diagonalBoundary
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V)) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (hsingle : Fintype.card V ≤
      2 * (singletonSupport (secondMultiplicity U)).card) :
    h * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) ≤
      (boundary
        (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  apply excess_mass_le_of_diagonal_variation
    σ h hexp (secondMultiplicity U)
      (boundary
        (fun i => (σ i).prodCongr (σ i)) U) hsingle
  exact secondMultiplicity_totalVariation_le_twice_diagonalBoundary
    σ U

theorem first_zero_mass_le_diagonalBoundary
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V)) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (hsingle : Fintype.card V ≤
      2 * (singletonSupport (firstMultiplicity U)).card) :
    h * (Finset.univ.filter fun x : V =>
      firstMultiplicity U x = 0).card ≤
        (boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  apply zero_mass_le_of_diagonal_variation
    σ h hexp (firstMultiplicity U)
      (boundary
        (fun i => (σ i).prodCongr (σ i)) U) hsingle
  exact firstMultiplicity_totalVariation_le_twice_diagonalBoundary
    σ U

def nonSingletonFirstEdges {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) : Finset (V × V) :=
  U.filter (fun z => firstMultiplicity U z.1 ≠ 1)

def nonSingletonSecondEdges {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) : Finset (V × V) :=
  U.filter (fun z => secondMultiplicity U z.2 ≠ 1)

def matchedFiberEdges {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) : Finset (V × V) :=
  U.filter (fun z =>
    firstMultiplicity U z.1 = 1 ∧ secondMultiplicity U z.2 = 1)

theorem firstFiber_nonSingletonFirstEdges
    {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) :
    firstFiber (nonSingletonFirstEdges U) x =
      if firstMultiplicity U x ≠ 1 then firstFiber U x else ∅ := by
  classical
  ext z
  by_cases hz : z.1 = x
  · by_cases hx : firstMultiplicity U x = 1
    · simp only [firstFiber, nonSingletonFirstEdges, ne_eq, Finset.mem_filter, hz, hx,
      not_true_eq_false, and_false,
        and_true, ↓reduceIte, Finset.notMem_empty]
    · simp only [firstFiber, nonSingletonFirstEdges, ne_eq, Finset.mem_filter, hz, hx,
      not_false_eq_true, and_true,
        ↓reduceIte]
  · by_cases hx : firstMultiplicity U x = 1
    · simp only [firstFiber, nonSingletonFirstEdges, ne_eq, Finset.mem_filter, hz, and_false, hx,
      not_true_eq_false,
        ↓reduceIte, Finset.notMem_empty]
    · simp only [firstFiber, nonSingletonFirstEdges, ne_eq, Finset.mem_filter, hz, and_false, hx,
      not_false_eq_true,
        ↓reduceIte]

theorem secondFiber_nonSingletonSecondEdges
    {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) :
    secondFiber (nonSingletonSecondEdges U) x =
      if secondMultiplicity U x ≠ 1 then secondFiber U x else ∅ := by
  classical
  ext z
  by_cases hz : z.2 = x
  · by_cases hx : secondMultiplicity U x = 1
    · simp only [secondFiber, nonSingletonSecondEdges, ne_eq, Finset.mem_filter, hz, hx,
      not_true_eq_false,
        and_false, and_true, ↓reduceIte, Finset.notMem_empty]
    · simp only [secondFiber, nonSingletonSecondEdges, ne_eq, Finset.mem_filter, hz, hx,
      not_false_eq_true,
        and_true, ↓reduceIte]
  · by_cases hx : secondMultiplicity U x = 1
    · simp only [secondFiber, nonSingletonSecondEdges, ne_eq, Finset.mem_filter, hz, and_false, hx,
        not_true_eq_false, ↓reduceIte, Finset.notMem_empty]
    · simp only [secondFiber, nonSingletonSecondEdges, ne_eq, Finset.mem_filter, hz, and_false, hx,
        not_false_eq_true, ↓reduceIte]

theorem card_nonSingletonFirstEdges_le_twice_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (nonSingletonFirstEdges U).card ≤
      2 * ∑ x : V, (firstMultiplicity U x - 1 : ℕ) := by
  classical
  calc
    (nonSingletonFirstEdges U).card =
        ∑ x : V, (firstFiber (nonSingletonFirstEdges U) x).card :=
          (sum_firstFiber_card (nonSingletonFirstEdges U)).symm
    _ = ∑ x : V,
          if firstMultiplicity U x ≠ 1
            then firstMultiplicity U x else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [firstFiber_nonSingletonFirstEdges]
          split <;> simp [firstMultiplicity]
    _ ≤ ∑ x : V, 2 * (firstMultiplicity U x - 1) := by
          apply Finset.sum_le_sum
          intro x _
          split <;> rename_i hx
          · omega
          · omega
    _ = 2 * ∑ x : V, (firstMultiplicity U x - 1) := by
          rw [Finset.mul_sum]

theorem card_nonSingletonSecondEdges_le_twice_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (nonSingletonSecondEdges U).card ≤
      2 * ∑ x : V, (secondMultiplicity U x - 1 : ℕ) := by
  classical
  calc
    (nonSingletonSecondEdges U).card =
        ∑ x : V, (secondFiber (nonSingletonSecondEdges U) x).card :=
          (sum_secondFiber_card (nonSingletonSecondEdges U)).symm
    _ = ∑ x : V,
          if secondMultiplicity U x ≠ 1
            then secondMultiplicity U x else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [secondFiber_nonSingletonSecondEdges]
          split <;> simp [secondMultiplicity]
    _ ≤ ∑ x : V, 2 * (secondMultiplicity U x - 1) := by
          apply Finset.sum_le_sum
          intro x _
          split <;> rename_i hx
          · omega
          · omega
    _ = 2 * ∑ x : V, (secondMultiplicity U x - 1) := by
          rw [Finset.mul_sum]

theorem nonmatchedFiberEdges_subset
    {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) :
    U \ matchedFiberEdges U ⊆
      nonSingletonFirstEdges U ∪ nonSingletonSecondEdges U := by
  classical
  intro z hz
  obtain ⟨hzU, hznot⟩ := Finset.mem_sdiff.mp hz
  have hnot : ¬ (firstMultiplicity U z.1 = 1 ∧
      secondMultiplicity U z.2 = 1) := by
    intro h
    apply hznot
    exact Finset.mem_filter.mpr ⟨hzU, h⟩
  by_cases hfirst : firstMultiplicity U z.1 = 1
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨hzU, fun hsecond => hnot ⟨hfirst, hsecond⟩⟩
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hzU, hfirst⟩

theorem card_nonmatchedFiberEdges_le_twice_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (U \ matchedFiberEdges U).card ≤
      2 * (∑ x : V, (firstMultiplicity U x - 1 : ℕ)) +
        2 * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) := by
  calc
    (U \ matchedFiberEdges U).card ≤
        (nonSingletonFirstEdges U ∪ nonSingletonSecondEdges U).card :=
      Finset.card_le_card (nonmatchedFiberEdges_subset U)
    _ ≤ (nonSingletonFirstEdges U).card +
          (nonSingletonSecondEdges U).card :=
      Finset.card_union_le _ _
    _ ≤ 2 * (∑ x : V, (firstMultiplicity U x - 1 : ℕ)) +
          2 * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) :=
      Nat.add_le_add
        (card_nonSingletonFirstEdges_le_twice_excess U)
        (card_nonSingletonSecondEdges_le_twice_excess U)

def singletonFirstEdges {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) : Finset (V × V) :=
  U.filter (fun z => firstMultiplicity U z.1 = 1)

theorem firstFiber_singletonFirstEdges
    {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) :
    firstFiber (singletonFirstEdges U) x =
      if firstMultiplicity U x = 1 then firstFiber U x else ∅ := by
  classical
  ext z
  by_cases hz : z.1 = x
  · by_cases hx : firstMultiplicity U x = 1
    · simp only [firstFiber, singletonFirstEdges, Finset.mem_filter, hz, hx, and_true, ↓reduceIte]
    · simp only [firstFiber, singletonFirstEdges, Finset.mem_filter, hz, hx, and_false, and_true,
      ↓reduceIte,
        Finset.notMem_empty]
  · by_cases hx : firstMultiplicity U x = 1
    · simp only [firstFiber, singletonFirstEdges, Finset.mem_filter, hz, and_false, hx, ↓reduceIte]
    · simp only [firstFiber, singletonFirstEdges, Finset.mem_filter, hz, and_false, hx, ↓reduceIte,
        Finset.notMem_empty]

theorem card_singletonFirstEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (singletonFirstEdges U).card =
      (singletonSupport (firstMultiplicity U)).card := by
  classical
  calc
    (singletonFirstEdges U).card =
        ∑ x : V, (firstFiber (singletonFirstEdges U) x).card :=
          (sum_firstFiber_card (singletonFirstEdges U)).symm
    _ = ∑ x : V, if firstMultiplicity U x = 1 then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [firstFiber_singletonFirstEdges]
          split <;> rename_i hx
          · simpa only [firstMultiplicity] using hx
          · simp only [Finset.card_empty]
    _ = (singletonSupport (firstMultiplicity U)).card := by
          simp only [Finset.sum_boole, Nat.cast_id, singletonSupport]

theorem singletonFirstEdges_subset_matching_union
    {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) :
    singletonFirstEdges U ⊆
      matchedFiberEdges U ∪ nonSingletonSecondEdges U := by
  classical
  intro z hz
  obtain ⟨hzU, hrow⟩ := Finset.mem_filter.mp hz
  by_cases hcol : secondMultiplicity U z.2 = 1
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hzU, hrow, hcol⟩
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hzU, hcol⟩

theorem card_singletonSupport_le_matching_add_column_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (singletonSupport (firstMultiplicity U)).card ≤
      (matchedFiberEdges U).card +
        2 * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) := by
  rw [← card_singletonFirstEdges U]
  calc
    (singletonFirstEdges U).card ≤
        (matchedFiberEdges U ∪ nonSingletonSecondEdges U).card :=
      Finset.card_le_card (singletonFirstEdges_subset_matching_union U)
    _ ≤ (matchedFiberEdges U).card +
          (nonSingletonSecondEdges U).card :=
      Finset.card_union_le _ _
    _ ≤ (matchedFiberEdges U).card +
          2 * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) :=
      Nat.add_le_add_left
        (card_nonSingletonSecondEdges_le_twice_excess U) _

theorem card_le_zero_singleton_excess
    {V : Type*} [Fintype V]
    (f : V → ℕ) :
    Fintype.card V ≤
      (Finset.univ.filter fun x : V => f x = 0).card +
        (singletonSupport f).card +
        ∑ x : V, (f x - 1 : ℕ) := by
  classical
  calc
    Fintype.card V = ∑ _ : V, (1 : ℕ) := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    _ ≤ ∑ x : V,
          ((if f x = 0 then 1 else 0) +
            (if f x = 1 then 1 else 0) + (f x - 1)) := by
          apply Finset.sum_le_sum
          intro x _
          by_cases hzero : f x = 0
          · simp only [hzero, ↓reduceIte, zero_ne_one, add_zero, zero_tsub, Std.le_refl]
          · by_cases hone : f x = 1
            · simp only [hone, one_ne_zero, ↓reduceIte, zero_add, tsub_self, add_zero, Std.le_refl]
            · simp only [hzero, ↓reduceIte, hone, add_zero, zero_add]
              omega
    _ = (Finset.univ.filter fun x : V => f x = 0).card +
          (singletonSupport f).card +
          ∑ x : V, (f x - 1 : ℕ) := by
          simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id, singletonSupport]

theorem unmatched_vertices_le_zero_and_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    Fintype.card V - (matchedFiberEdges U).card ≤
      (Finset.univ.filter fun x : V => firstMultiplicity U x = 0).card +
        (∑ x : V, (firstMultiplicity U x - 1 : ℕ)) +
        2 * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) := by
  have hpopulation := card_le_zero_singleton_excess
    (firstMultiplicity U)
  have hsingle := card_singletonSupport_le_matching_add_column_excess U
  omega

theorem matchedFiberEdges_relation_loss_bound
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V))
    (h : ℝ) (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (hfirst : Fintype.card V ≤
      2 * (singletonSupport (firstMultiplicity U)).card)
    (hsecond : Fintype.card V ≤
      2 * (singletonSupport (secondMultiplicity U)).card) :
    h * ((U \ matchedFiberEdges U).card : ℝ) ≤
      4 * (boundary
        (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  have hcount := card_nonmatchedFiberEdges_le_twice_excess U
  have hcount_real :
      ((U \ matchedFiberEdges U).card : ℝ) ≤
        2 * ((∑ x : V, (firstMultiplicity U x - 1 : ℕ)) : ℝ) +
          2 * ((∑ x : V, (secondMultiplicity U x - 1 : ℕ)) : ℝ) := by
    exact_mod_cast hcount
  have hrow := first_excess_mass_le_diagonalBoundary
    σ U h hexp hfirst
  have hcol := second_excess_mass_le_diagonalBoundary
    σ U h hexp hsecond
  have hrow' :
      h * (∑ x : V, ((firstMultiplicity U x - 1 : ℕ) : ℝ)) ≤
        (boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
    simpa only [Nat.cast_sum] using hrow
  have hcol' :
      h * (∑ x : V, ((secondMultiplicity U x - 1 : ℕ) : ℝ)) ≤
        (boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
    simpa only [Nat.cast_sum] using hcol
  calc
    h * ((U \ matchedFiberEdges U).card : ℝ) ≤
        h *
          (2 * ((∑ x : V, (firstMultiplicity U x - 1 : ℕ)) : ℝ) +
            2 * ((∑ x : V, (secondMultiplicity U x - 1 : ℕ)) : ℝ)) :=
      mul_le_mul_of_nonneg_left hcount_real hpositive.le
    _ = 2 *
          (h * (∑ x : V, ((firstMultiplicity U x - 1 : ℕ) : ℝ))) +
          2 *
          (h * (∑ x : V, ((secondMultiplicity U x - 1 : ℕ) : ℝ))) := by
      ring
    _ ≤ 4 * (boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
      linarith

theorem matchedFiberEdges_vertex_loss_bound
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V))
    (h : ℝ) (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (hfirst : Fintype.card V ≤
      2 * (singletonSupport (firstMultiplicity U)).card)
    (hsecond : Fintype.card V ≤
      2 * (singletonSupport (secondMultiplicity U)).card) :
    h * ((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) ≤
      4 * (boundary
        (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  have hcount := unmatched_vertices_le_zero_and_excess U
  have hcount_real :
      ((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) ≤
        ((Finset.univ.filter fun x : V =>
          firstMultiplicity U x = 0).card : ℝ) +
          ((∑ x : V, (firstMultiplicity U x - 1 : ℕ)) : ℝ) +
          2 * ((∑ x : V, (secondMultiplicity U x - 1 : ℕ)) : ℝ) := by
    exact_mod_cast hcount
  have hzero := first_zero_mass_le_diagonalBoundary
    σ U h hexp hfirst
  have hrow := first_excess_mass_le_diagonalBoundary
    σ U h hexp hfirst
  have hcol := second_excess_mass_le_diagonalBoundary
    σ U h hexp hsecond
  have hrow' :
      h * (∑ x : V, ((firstMultiplicity U x - 1 : ℕ) : ℝ)) ≤
        (boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
    simpa only [Nat.cast_sum] using hrow
  have hcol' :
      h * (∑ x : V, ((secondMultiplicity U x - 1 : ℕ) : ℝ)) ≤
        (boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
    simpa only [Nat.cast_sum] using hcol
  calc
    h * ((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) ≤
        h *
          (((Finset.univ.filter fun x : V =>
            firstMultiplicity U x = 0).card : ℝ) +
            ((∑ x : V, (firstMultiplicity U x - 1 : ℕ)) : ℝ) +
            2 * ((∑ x : V, (secondMultiplicity U x - 1 : ℕ)) : ℝ)) :=
      mul_le_mul_of_nonneg_left hcount_real hpositive.le
    _ = h * ((Finset.univ.filter fun x : V =>
          firstMultiplicity U x = 0).card : ℝ) +
          h * (∑ x : V, ((firstMultiplicity U x - 1 : ℕ) : ℝ)) +
          2 *
            (h * (∑ x : V, ((secondMultiplicity U x - 1 : ℕ) : ℝ))) := by
      ring
    _ ≤ 4 * (boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
      linarith

theorem exists_permutation_extending_matchedFiberEdges
    {V : Type*} [DecidableEq V] (U : Finset (V × V)) :
    ∃ p : Equiv.Perm V,
      ∀ z ∈ matchedFiberEdges U, p z.1 = z.2 := by
  classical
  let A := {z : V × V // z ∈ matchedFiberEdges U}
  let f : A → V := fun z => z.1.1
  let g : A → V := fun z => z.1.2
  have hf : Function.Injective f := by
    intro z w h
    have hz := Finset.mem_filter.mp z.property
    have hw := Finset.mem_filter.mp w.property
    have hcard :
        (U.filter fun t => t.1 = z.1.1).card ≤ 1 := by
      have heq : firstMultiplicity U z.1.1 = 1 := hz.2.1
      simpa only [ge_iff_le, firstMultiplicity, firstFiber] using Nat.le_of_eq heq
    have hzmem : z.1 ∈ U.filter fun t => t.1 = z.1.1 :=
      Finset.mem_filter.mpr ⟨hz.1, rfl⟩
    have hwmem : w.1 ∈ U.filter fun t => t.1 = z.1.1 := by
      apply Finset.mem_filter.mpr
      refine ⟨hw.1, ?_⟩
      exact h.symm
    exact Subtype.ext
      ((Finset.card_le_one_iff.mp hcard) hzmem hwmem)
  have hg : Function.Injective g := by
    intro z w h
    have hz := Finset.mem_filter.mp z.property
    have hw := Finset.mem_filter.mp w.property
    have hcard :
        (U.filter fun t => t.2 = z.1.2).card ≤ 1 := by
      have heq : secondMultiplicity U z.1.2 = 1 := hz.2.2
      simpa only [ge_iff_le, secondMultiplicity, secondFiber] using Nat.le_of_eq heq
    have hzmem : z.1 ∈ U.filter fun t => t.2 = z.1.2 :=
      Finset.mem_filter.mpr ⟨hz.1, rfl⟩
    have hwmem : w.1 ∈ U.filter fun t => t.2 = z.1.2 := by
      apply Finset.mem_filter.mpr
      refine ⟨hw.1, ?_⟩
      exact h.symm
    exact Subtype.ext
      ((Finset.card_le_one_iff.mp hcard) hzmem hwmem)
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨p, ?_⟩
  intro z hz
  exact hp ⟨z, hz⟩

theorem exists_permutationGraph_containing_matchedFiberEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    ∃ p : Equiv.Perm V,
      matchedFiberEdges U ⊆ permutationGraph p := by
  obtain ⟨p, hp⟩ := exists_permutation_extending_matchedFiberEdges U
  refine ⟨p, ?_⟩
  intro z hz
  have h :=
    (mem_permutationGraph p z.1 z.2).mpr (hp z hz).symm
  simpa only [Prod.mk.eta] using h

theorem permutationGraph_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) :
    (permutationGraph p).card = Fintype.card V := by
  classical
  have hinj : Function.Injective (fun x : V => (x, p x)) := by
    intro x y h
    exact congrArg Prod.fst h
  simpa only [permutationGraph, Finset.card_univ] using (Finset.card_image_of_injective Finset.univ
    hinj)

theorem permutationGraph_sdiff_bounds_of_matchedFiberEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (p : Equiv.Perm V)
    (hp : matchedFiberEdges U ⊆ permutationGraph p) :
    (permutationGraph p \ U).card ≤
        Fintype.card V - (matchedFiberEdges U).card ∧
      (U \ permutationGraph p).card ≤
        (U \ matchedFiberEdges U).card := by
  classical
  have hGU : matchedFiberEdges U ⊆ U := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  have hleftsub :
      matchedFiberEdges U ⊆ U ∩ permutationGraph p := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨hGU hz, hp hz⟩
  have hrightsub :
      matchedFiberEdges U ⊆ permutationGraph p ∩ U := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨hp hz, hGU hz⟩
  have hleftcard := Finset.card_le_card hleftsub
  have hrightcard := Finset.card_le_card hrightsub
  have hgraph := permutationGraph_card p
  have hleft := Finset.card_sdiff_add_card_inter
    (permutationGraph p) U
  have hright := Finset.card_sdiff_add_card_inter
    U (permutationGraph p)
  have hmatched := Finset.card_sdiff_add_card_inter U (matchedFiberEdges U)
  have hinter :
      (U ∩ matchedFiberEdges U).card =
        (matchedFiberEdges U).card := by
    have hset : U ∩ matchedFiberEdges U = matchedFiberEdges U := by
      exact Finset.inter_eq_right.mpr hGU
    rw [hset]
  have hswap :
      (U ∩ permutationGraph p).card =
        (permutationGraph p ∩ U).card := by
    rw [Finset.inter_comm]
  constructor <;> omega

theorem boundary_le_boundary_add_sdiff
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U W : Finset V) :
    boundary σ U ≤ boundary σ W +
      Fintype.card ι * ((U \ W).card + (W \ U).card) := by
  classical
  have hpoint (i : ι) :
      (U.filter fun x => σ i x ∉ U).card ≤
        (W.filter fun x => σ i x ∉ W).card +
          (U \ W).card + (W \ U).card := by
    let BU := U.filter fun x => σ i x ∉ U
    let BW := W.filter fun x => σ i x ∉ W
    let E := U \ W
    let C := (W \ U).image (σ i).symm
    have hC : C.card = (W \ U).card := by
      dsimp [C]
      exact Finset.card_image_of_injective _ (σ i).symm.injective
    have hsub : BU ⊆ (BW ∪ E) ∪ C := by
      intro x hx
      obtain ⟨hxU, hxout⟩ := Finset.mem_filter.mp hx
      by_cases hxW : x ∈ W
      · by_cases himage : σ i x ∈ W
        · apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨σ i x, Finset.mem_sdiff.mpr ⟨himage, hxout⟩, ?_⟩
          simp only [Equiv.symm_apply_apply]
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          exact Finset.mem_filter.mpr ⟨hxW, himage⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_sdiff.mpr ⟨hxU, hxW⟩
    change BU.card ≤ BW.card + (U \ W).card + (W \ U).card
    calc
      BU.card ≤ ((BW ∪ E) ∪ C).card := Finset.card_le_card hsub
      _ ≤ (BW ∪ E).card + C.card := Finset.card_union_le _ _
      _ ≤ (BW.card + E.card) + C.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = BW.card + (U \ W).card + (W \ U).card := by
        rw [hC]
  unfold boundary
  calc
    (∑ i : ι, (U.filter fun x => σ i x ∉ U).card) ≤
        ∑ i : ι,
          ((W.filter fun x => σ i x ∉ W).card +
            (U \ W).card + (W \ U).card) := by
          apply Finset.sum_le_sum
          intro i _
          exact hpoint i
    _ = (∑ i : ι, (W.filter fun x => σ i x ∉ W).card) +
          Fintype.card ι * ((U \ W).card + (W \ U).card) := by
          simp only [add_assoc, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            smul_eq_mul,
            mul_add]

theorem exists_boundary_controlled_permutation_repair
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V))
    (h : ℝ) (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (hfirst : Fintype.card V ≤
      2 * (singletonSupport (firstMultiplicity U)).card)
    (hsecond : Fintype.card V ≤
      2 * (singletonSupport (secondMultiplicity U)).card) :
    ∃ q : Equiv.Perm V,
      matchedFiberEdges U ⊆ permutationGraph q ∧
        h * (permutationCommutationDefect σ q : ℝ) ≤
          (h + 8 * (Fintype.card ι : ℝ)) *
            (boundary
              (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  classical
  obtain ⟨q, hq⟩ :=
    exists_permutationGraph_containing_matchedFiberEdges U
  obtain ⟨hgraphleft, hgraphright⟩ :=
    permutationGraph_sdiff_bounds_of_matchedFiberEdges U q hq
  have hboundary := boundary_le_boundary_add_sdiff
    (fun i => (σ i).prodCongr (σ i))
      (permutationGraph q) U
  have hdefect :
      permutationCommutationDefect σ q ≤
        boundary
            (fun i => (σ i).prodCongr (σ i)) U +
          Fintype.card ι *
            ((Fintype.card V - (matchedFiberEdges U).card) +
              (U \ matchedFiberEdges U).card) := by
    rw [← boundary_permutationGraph_eq_commutationDefect]
    apply hboundary.trans
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_left (Fintype.card ι)
        (Nat.add_le_add hgraphleft hgraphright)) _
  have hdefect_real :
      (permutationCommutationDefect σ q : ℝ) ≤
        (boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) +
          (Fintype.card ι : ℝ) *
            (((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) +
              ((U \ matchedFiberEdges U).card : ℝ)) := by
    exact_mod_cast hdefect
  have hvertex := matchedFiberEdges_vertex_loss_bound
    σ U h hpositive hexp hfirst hsecond
  have hrelation := matchedFiberEdges_relation_loss_bound
    σ U h hpositive hexp hfirst hsecond
  have hsum :
      h *
          (((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) +
            ((U \ matchedFiberEdges U).card : ℝ)) ≤
        8 * (boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
    nlinarith
  have hdnonneg : (0 : ℝ) ≤ Fintype.card ι := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hdnonneg
  refine ⟨q, hq, ?_⟩
  calc
    h * (permutationCommutationDefect σ q : ℝ) ≤
        h *
          ((boundary
            (fun i => (σ i).prodCongr (σ i)) U : ℝ) +
            (Fintype.card ι : ℝ) *
              (((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) +
                ((U \ matchedFiberEdges U).card : ℝ))) :=
      mul_le_mul_of_nonneg_left hdefect_real hpositive.le
    _ ≤ (h + 8 * (Fintype.card ι : ℝ)) *
          (boundary
            (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
      nlinarith

theorem permutationDistance_eq_card_permutationGraph_sdiff
    {V : Type*} [Fintype V] [DecidableEq V]
    (p q : Equiv.Perm V) :
    permutationDistance p q =
      (permutationGraph p \
        permutationGraph q).card := by
  classical
  unfold permutationDistance hammingDist
  apply Finset.card_bij (fun x _ => (x, p x))
  · intro x hx
    obtain ⟨_, hne⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_permutationGraph p x (p x)).mpr rfl, ?_⟩
    intro hxq
    exact hne ((mem_permutationGraph q x (p x)).mp hxq)
  · intro x _ y _ h
    exact congrArg Prod.fst h
  · intro z hz
    obtain ⟨hzp, hzq⟩ := Finset.mem_sdiff.mp hz
    have hzsecond :=
      (mem_permutationGraph p z.1 z.2).mp hzp
    refine ⟨z.1, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro heq
      apply hzq
      exact (mem_permutationGraph q z.1 z.2).mpr
        (hzsecond.trans heq)
    · exact Prod.ext rfl hzsecond.symm

theorem permutationDistance_le_matching_loss_add_reference
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (q p : Equiv.Perm V)
    (hq : matchedFiberEdges U ⊆ permutationGraph q) :
    permutationDistance q p ≤
      Fintype.card V - (matchedFiberEdges U).card +
        (U \ permutationGraph p).card := by
  classical
  obtain ⟨hleft, _⟩ :=
    permutationGraph_sdiff_bounds_of_matchedFiberEdges U q hq
  have hsub :
      permutationGraph q \
          permutationGraph p ⊆
        (permutationGraph q \ U) ∪
          (U \ permutationGraph p) := by
    intro z hz
    obtain ⟨hzq, hznot⟩ := Finset.mem_sdiff.mp hz
    by_cases hzU : z ∈ U
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨hzU, hznot⟩
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨hzq, hzU⟩
  rw [permutationDistance_eq_card_permutationGraph_sdiff]
  calc
    (permutationGraph q \
      permutationGraph p).card ≤
        ((permutationGraph q \ U) ∪
          (U \ permutationGraph p)).card :=
      Finset.card_le_card hsub
    _ ≤ (permutationGraph q \ U).card +
          (U \ permutationGraph p).card :=
      Finset.card_union_le _ _
    _ ≤ Fintype.card V - (matchedFiberEdges U).card +
          (U \ permutationGraph p).card :=
      Nat.add_le_add_right hleft _

theorem exists_boundary_controlled_permutation_repair_close_to_reference
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V))
    (p : Equiv.Perm V) (h : ℝ) (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (hfirst : Fintype.card V ≤
      2 * (singletonSupport (firstMultiplicity U)).card)
    (hsecond : Fintype.card V ≤
      2 * (singletonSupport (secondMultiplicity U)).card) :
    ∃ q : Equiv.Perm V,
      h * (permutationDistance q p : ℝ) ≤
          4 * (boundary
            (fun i => (σ i).prodCongr (σ i)) U : ℝ) +
            h * ((U \ permutationGraph p).card : ℝ) ∧
        h * (permutationCommutationDefect σ q : ℝ) ≤
          (h + 8 * (Fintype.card ι : ℝ)) *
            (boundary
              (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  obtain ⟨q, hq, hdefect⟩ :=
    exists_boundary_controlled_permutation_repair
      σ U h hpositive hexp hfirst hsecond
  have hdistance :=
    permutationDistance_le_matching_loss_add_reference U q p hq
  have hdistance_real :
      (permutationDistance q p : ℝ) ≤
        ((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) +
          ((U \ permutationGraph p).card : ℝ) := by
    exact_mod_cast hdistance
  have hvertex := matchedFiberEdges_vertex_loss_bound
    σ U h hpositive hexp hfirst hsecond
  refine ⟨q, ?_, hdefect⟩
  have hscaled := mul_le_mul_of_nonneg_left hdistance_real hpositive.le
  nlinarith

theorem hasAlmostCentralizerImprovement_of_expanding_diagonal_cuts
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (h : ℝ) (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (hcut : ∀ p : Equiv.Perm V,
      permutationCommutationDefect σ p ≤ 2 * tolerance →
        ∃ U : Finset (V × V),
          Fintype.card V ≤
            2 * (singletonSupport (firstMultiplicity U)).card ∧
          Fintype.card V ≤
            2 * (singletonSupport (secondMultiplicity U)).card ∧
          (h + 8 * (Fintype.card ι : ℝ)) *
              (boundary
                (fun i => (σ i).prodCongr (σ i)) U : ℝ) ≤
            h * (tolerance : ℝ) ∧
          (5 : ℝ) *
              (4 * (boundary
                (fun i => (σ i).prodCongr (σ i)) U : ℝ) +
                h * ((U \ permutationGraph p).card : ℝ)) ≤
            h * (Fintype.card V : ℝ)) :
    HasAlmostCentralizerImprovement σ tolerance := by
  refine ⟨?_⟩
  intro p hp
  obtain ⟨U, hfirst, hsecond, hcutdefect, hcutdistance⟩ := hcut p hp
  obtain ⟨q, hqdistance, hqdefect⟩ :=
    exists_boundary_controlled_permutation_repair_close_to_reference
      σ U p h hpositive hexp hfirst hsecond
  have hdefect_real :
      (permutationCommutationDefect σ q : ℝ) ≤
        (tolerance : ℝ) := by
    nlinarith
  have hdefect :
      permutationCommutationDefect σ q ≤ tolerance := by
    exact_mod_cast hdefect_real
  have hscaled := mul_le_mul_of_nonneg_left hqdistance
    (show (0 : ℝ) ≤ 5 by norm_num)
  have hdistance_real :
      (5 : ℝ) * (permutationDistance q p : ℝ) ≤
        (Fintype.card V : ℝ) := by
    nlinarith
  have hdistance :
      5 * permutationDistance q p ≤ Fintype.card V := by
    exact_mod_cast hdistance_real
  exact ⟨q, hdefect, hdistance⟩

theorem projMultiplicity_permutationGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (π : V × V → V) (p : Equiv.Perm V) (w : V → V × V)
    (hmem : ∀ x, w x ∈ permutationGraph p)
    (hproj : ∀ x, π (w x) = x)
    (hpoint : ∀ z ∈ permutationGraph p, w (π z) = z)
    (x : V) :
    (projFiber π (permutationGraph p) x).card = 1 := by
  classical
  have hset :
      projFiber π (permutationGraph p) x = {w x} := by
    ext z
    simp only [projFiber, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hzx⟩
      rw [← hpoint z hz, hzx]
    · rintro rfl
      exact ⟨hmem x, hproj x⟩
  rw [hset, Finset.card_singleton]

theorem firstMultiplicity_permutationGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (x : V) :
    firstMultiplicity (permutationGraph p) x = 1 :=
  projMultiplicity_permutationGraph Prod.fst p (fun y => (y, p y))
    (fun y => (mem_permutationGraph p y (p y)).mpr rfl)
    (fun _ => rfl)
    (fun z hz => Prod.ext rfl
      ((mem_permutationGraph p z.1 z.2).mp hz).symm)
    x

theorem secondMultiplicity_permutationGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (x : V) :
    secondMultiplicity (permutationGraph p) x = 1 :=
  projMultiplicity_permutationGraph Prod.snd p (fun y => (p.symm y, y))
    (fun y => (mem_permutationGraph p (p.symm y) y).mpr
      (p.apply_symm_apply y).symm)
    (fun _ => rfl)
    (fun z hz => Prod.ext
      (by rw [(mem_permutationGraph p z.1 z.2).mp hz,
        p.symm_apply_apply])
      rfl)
    x

theorem card_nonSingletonMultiplicity_le_total_distance
    {V : Type*} [Fintype V]
    (f : V → ℕ) :
    (Finset.univ.filter fun x : V => f x ≠ 1).card ≤
      ∑ x : V, Nat.dist (f x) 1 := by
  classical
  calc
    (Finset.univ.filter fun x : V => f x ≠ 1).card =
        ∑ x : V, if f x ≠ 1 then 1 else 0 := by
          exact
            (Finset.sum_boole (R := ℕ)
              (fun x : V => f x ≠ 1) Finset.univ).symm
    _ ≤ ∑ x : V, Nat.dist (f x) 1 := by
          apply Finset.sum_le_sum
          intro x _
          by_cases hx : f x = 1
          · simp only [hx, ne_eq, not_true_eq_false, ↓reduceIte, Nat.dist_self, Std.le_refl]
          · simp only [ne_eq, hx, not_false_eq_true, ↓reduceIte, Nat.dist]
            omega

theorem card_nonSingletonFirstMultiplicity_le_reference_difference
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (p : Equiv.Perm V) :
    (Finset.univ.filter fun x : V =>
      firstMultiplicity U x ≠ 1).card ≤
        (U \ permutationGraph p).card +
          (permutationGraph p \ U).card := by
  have hcount := card_nonSingletonMultiplicity_le_total_distance
    (firstMultiplicity U)
  have hvariation := firstMultiplicity_variation_le_relation_difference
    U (permutationGraph p)
  simp_rw [firstMultiplicity_permutationGraph] at hvariation
  exact hcount.trans hvariation

theorem card_nonSingletonSecondMultiplicity_le_reference_difference
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (p : Equiv.Perm V) :
    (Finset.univ.filter fun x : V =>
      secondMultiplicity U x ≠ 1).card ≤
        (U \ permutationGraph p).card +
          (permutationGraph p \ U).card := by
  have hcount := card_nonSingletonMultiplicity_le_total_distance
    (secondMultiplicity U)
  have hvariation := secondMultiplicity_variation_le_relation_difference
    U (permutationGraph p)
  simp_rw [secondMultiplicity_permutationGraph] at hvariation
  exact hcount.trans hvariation

theorem first_singleton_half_of_reference_difference
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (p : Equiv.Perm V)
    (hnear :
      2 * ((U \ permutationGraph p).card +
        (permutationGraph p \ U).card) ≤
          Fintype.card V) :
    Fintype.card V ≤
      2 * (singletonSupport (firstMultiplicity U)).card := by
  have hbad := card_nonSingletonFirstMultiplicity_le_reference_difference
    U p
  have hpartition :
      (singletonSupport (firstMultiplicity U)).card +
          (Finset.univ.filter fun x : V =>
            firstMultiplicity U x ≠ 1).card = Fintype.card V := by
    simpa only [singletonSupport, ne_eq, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (fun x =>
        firstMultiplicity U x = 1))
  omega

theorem second_singleton_half_of_reference_difference
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (p : Equiv.Perm V)
    (hnear :
      2 * ((U \ permutationGraph p).card +
        (permutationGraph p \ U).card) ≤
          Fintype.card V) :
    Fintype.card V ≤
      2 * (singletonSupport (secondMultiplicity U)).card := by
  have hbad := card_nonSingletonSecondMultiplicity_le_reference_difference
    U p
  have hpartition :
      (singletonSupport (secondMultiplicity U)).card +
          (Finset.univ.filter fun x : V =>
            secondMultiplicity U x ≠ 1).card = Fintype.card V := by
    simpa only [singletonSupport, ne_eq, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (fun x =>
        secondMultiplicity U x = 1))
  omega

theorem hasAlmostCentralizerImprovement_of_rooted_reference_cuts
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (h : ℝ) (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ))
    (hcut : ∀ p : Equiv.Perm V,
      permutationCommutationDefect σ p ≤ 2 * tolerance →
        ∃ U : Finset (V × V),
          2 * ((U \ permutationGraph p).card +
            (permutationGraph p \ U).card) ≤
              Fintype.card V ∧
          (h + 8 * (Fintype.card ι : ℝ)) *
              (boundary
                (fun i => (σ i).prodCongr (σ i)) U : ℝ) ≤
            h * (tolerance : ℝ) ∧
          (5 : ℝ) *
              (4 * (boundary
                (fun i => (σ i).prodCongr (σ i)) U : ℝ) +
                h * ((U \ permutationGraph p).card : ℝ)) ≤
            h * (Fintype.card V : ℝ)) :
    HasAlmostCentralizerImprovement σ tolerance := by
  apply hasAlmostCentralizerImprovement_of_expanding_diagonal_cuts
    σ tolerance h hpositive hexp
  intro p hp
  obtain ⟨U, hnear, hdefect, hdistance⟩ := hcut p hp
  exact ⟨U,
    first_singleton_half_of_reference_difference U p hnear,
    second_singleton_half_of_reference_difference U p hnear,
    hdefect, hdistance⟩

end KunThomFiberCoarea

namespace KunRootedIndicatorCrossing

universe u

open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology

theorem sum_sq_le_sq_sum_of_same_sign
    {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (h : (∀ i, 0 ≤ a i) ∨ (∀ i, a i ≤ 0)) :
    (∑ i, a i ^ 2) ≤ (∑ i, a i) ^ 2 := by
  rcases h with h | h
  · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => h i)
  · have hn := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := fun i : ι => -a i)
      (fun i _ => neg_nonneg.mpr (h i))
    simpa only [sq, ge_iff_le, mul_neg, neg_mul, neg_neg, Finset.sum_neg_distrib] using hn

theorem indicator_displacements_same_sign
    {ι V : Type*} (p : ι → V → V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (x : V) :
    (∀ i, 0 ≤ f (p i x) - f x) ∨
      (∀ i, f (p i x) - f x ≤ 0) := by
  rcases hf x with hx | hx
  · left
    intro i
    rcases hf (p i x) with hi | hi <;> simp [hx, hi]
  · right
    intro i
    rcases hf (p i x) with hi | hi <;> simp [hx, hi]

theorem sum_indicator_displacement_sq_le
    {ι V : Type*} [Fintype ι] (p : ι → V → V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (x : V) :
    (∑ i, (f (p i x) - f x) ^ 2) ≤
      (∑ i, (f (p i x) - f x)) ^ 2 :=
  sum_sq_le_sq_sum_of_same_sign _
    (indicator_displacements_same_sign p f hf x)

theorem sum_sum_indicator_displacement_sq_le
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → V → V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) :
    (∑ i, ∑ x, (f (p i x) - f x) ^ 2) ≤
      ∑ x, (∑ i, (f (p i x) - f x)) ^ 2 := by
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun x _ =>
    sum_indicator_displacement_sq_le p f hf x

theorem sum_sum_indicator_displacement_sq_le_card_sq_mul_markov_defect
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → V → V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) :
    (∑ i, ∑ x, (f (p i x) - f x) ^ 2) ≤
      (Fintype.card ι : ℝ) ^ 2 *
        ∑ x, ((∑ i, f (p i x)) / (Fintype.card ι : ℝ) - f x) ^ 2 := by
  have hd : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hpoint (x : V) :
      (Fintype.card ι : ℝ) ^ 2 *
          ((∑ i, f (p i x)) / (Fintype.card ι : ℝ) - f x) ^ 2 =
        (∑ i, (f (p i x) - f x)) ^ 2 := by
    rw [← mul_pow]
    congr 1
    rw [mul_sub, mul_div_cancel₀ _ hd, Finset.sum_sub_distrib]
    simp only [mul_comm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    (∑ i, ∑ x, (f (p i x) - f x) ^ 2) ≤
        ∑ x, (∑ i, (f (p i x) - f x)) ^ 2 :=
      sum_sum_indicator_displacement_sq_le p f hf
    _ = (Fintype.card ι : ℝ) ^ 2 *
        ∑ x, ((∑ i, f (p i x)) / (Fintype.card ι : ℝ) - f x) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => (hpoint x).symm

def permutationUnitary {V : Type*} [Fintype V] (p : Equiv.Perm V) :
    EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ p

theorem permutationUnitary_mul {V : Type*} [Fintype V]
    (p q : Equiv.Perm V) (ξ : EuclideanSpace ℂ V) :
    permutationUnitary (p * q) ξ =
      permutationUnitary p (permutationUnitary q ξ) := by
  ext x
  change ξ ((p * q).symm x) = ξ (q.symm (p.symm x))
  rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply]

@[simp]
theorem permutationUnitary_one {V : Type*} [Fintype V]
    (ξ : EuclideanSpace ℂ V) :
    permutationUnitary (1 : Equiv.Perm V) ξ = ξ := by
  ext x
  change ξ x = ξ x
  rfl

theorem permutationUnitary_eq_of_agree_on_support
    {V : Type*} [Fintype V] (p q : Equiv.Perm V)
    (ξ : EuclideanSpace ℂ V)
    (h : ∀ x : V, ξ x ≠ 0 → p x = q x) :
    permutationUnitary p ξ = permutationUnitary q ξ := by
  ext y
  change ξ (p.symm y) = ξ (q.symm y)
  by_cases hp : ξ (p.symm y) = 0
  · rw [hp]
    have hzero : ξ (q.symm y) = 0 := by
      by_contra hq
      have hsame : q.symm y = p.symm y := by
        apply p.injective
        simpa only [Equiv.apply_symm_apply] using h (q.symm y) hq
      apply hq
      rw [hsame]
      exact hp
    exact hzero.symm
  · have hsame : p.symm y = q.symm y := by
      apply q.injective
      simpa only [Equiv.apply_symm_apply] using (h (p.symm y) hp).symm
    rw [hsame]

theorem permutationUnitary_model_mul_of_agree_on_support
    {G V : Type*} [Group G] [Fintype V]
    (σ : G → Equiv.Perm V) (a g : G) (ξ : EuclideanSpace ℂ V)
    (hroot : ∀ x : V, ξ x ≠ 0 →
      σ (a * g) x = (σ a * σ g) x) :
    permutationUnitary (σ (a * g)) ξ =
      permutationUnitary (σ a) (permutationUnitary (σ g) ξ) := by
  rw [permutationUnitary_eq_of_agree_on_support
    (σ (a * g)) (σ a * σ g) ξ hroot,
    permutationUnitary_mul]

def indicatorVector {V : Type*}
    (f : V → ℝ) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 fun x => (f x : ℂ)

def permutationMarkov {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (ξ : EuclideanSpace ℂ V) :
    EuclideanSpace ℂ V :=
  (Fintype.card ι : ℂ)⁻¹ • ∑ i, permutationUnitary (p i) ξ

@[simp]
theorem permutationMarkov_apply {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (ξ : EuclideanSpace ℂ V) (x : V) :
    permutationMarkov p ξ x =
      (∑ i, ξ ((p i).symm x)) / (Fintype.card ι : ℂ) := by
  simp only [permutationMarkov, permutationUnitary, PiLp.smul_apply, WithLp.ofLp_sum,
    LinearIsometryEquiv.piLpCongrLeft_apply, Finset.sum_apply, Equiv.piCongrLeft'_apply,
      smul_eq_mul, div_eq_mul_inv,
    mul_comm]

theorem permutation_indicator_displacement_norm_sq
    {V : Type*} [Fintype V] (p : Equiv.Perm V) (f : V → ℝ) :
    ‖permutationUnitary p (indicatorVector f) - indicatorVector f‖ ^ 2 =
      ∑ x, (f (p.symm x) - f x) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  change ‖(f (p.symm x) : ℂ) - (f x : ℂ)‖ ^ 2 =
    (f (p.symm x) - f x) ^ 2
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

theorem permutation_indicator_markov_defect_norm_sq
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    ‖permutationMarkov p (indicatorVector f) - indicatorVector f‖ ^ 2 =
      ∑ x, ((∑ i, f ((p i).symm x)) /
        (Fintype.card ι : ℝ) - f x) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  change ‖permutationMarkov p (indicatorVector f) x -
      indicatorVector f x‖ ^ 2 = _
  rw [permutationMarkov_apply]
  change ‖(∑ i, (f ((p i).symm x) : ℂ)) /
    (Fintype.card ι : ℂ) - (f x : ℂ)‖ ^ 2 = _
  have hcast :
      (∑ i, (f ((p i).symm x) : ℂ)) /
          (Fintype.card ι : ℂ) - (f x : ℂ) =
        (((∑ i, f ((p i).symm x)) /
          (Fintype.card ι : ℝ) - f x : ℝ) : ℂ) := by
    norm_cast
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem sum_permutation_indicator_displacement_norm_sq_le
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) :
    (∑ i, ‖permutationUnitary (p i) (indicatorVector f) -
      indicatorVector f‖ ^ 2) ≤
        (Fintype.card ι : ℝ) ^ 2 *
          ‖permutationMarkov p (indicatorVector f) -
            indicatorVector f‖ ^ 2 := by
  simp_rw [permutation_indicator_displacement_norm_sq,
    permutation_indicator_markov_defect_norm_sq]
  exact sum_sum_indicator_displacement_sq_le_card_sq_mul_markov_defect
    (fun i x => (p i).symm x) f hf

theorem permutation_indicator_displacement_norm_le_card_mul_markov_defect
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (i : ι) :
    ‖permutationUnitary (p i) (indicatorVector f) - indicatorVector f‖ ≤
      (Fintype.card ι : ℝ) *
        ‖permutationMarkov p (indicatorVector f) - indicatorVector f‖ := by
  have hsingle :
      ‖permutationUnitary (p i) (indicatorVector f) -
        indicatorVector f‖ ^ 2 ≤
        ∑ j, ‖permutationUnitary (p j) (indicatorVector f) -
          indicatorVector f‖ ^ 2 :=
    Finset.single_le_sum
      (f := fun j : ι =>
        ‖permutationUnitary (p j) (indicatorVector f) -
          indicatorVector f‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have htotal :=
    sum_permutation_indicator_displacement_norm_sq_le p f hf
  have hsq :
      ‖permutationUnitary (p i) (indicatorVector f) -
        indicatorVector f‖ ^ 2 ≤
        ((Fintype.card ι : ℝ) *
          ‖permutationMarkov p (indicatorVector f) -
            indicatorVector f‖) ^ 2 := by
    rw [mul_pow]
    exact hsingle.trans htotal
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity)
    (norm_nonneg _))).mp hsq

def normalizedIndicatorDisplacement
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (q : Equiv.Perm V) :
    EuclideanSpace ℂ V :=
  ((‖permutationMarkov p (indicatorVector f) -
      indicatorVector f‖ : ℝ) : ℂ)⁻¹ •
    (permutationUnitary q (indicatorVector f) - indicatorVector f)

theorem norm_normalizedIndicatorDisplacement_generator_le
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hdefect : permutationMarkov p (indicatorVector f) ≠
      indicatorVector f) (i : ι) :
    ‖normalizedIndicatorDisplacement p f (p i)‖ ≤
      (Fintype.card ι : ℝ) := by
  have hpos : 0 < ‖permutationMarkov p (indicatorVector f) -
      indicatorVector f‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hdefect)
  rw [normalizedIndicatorDisplacement, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  apply (inv_mul_le_iff₀ hpos).mpr
  simpa only [mul_comm] using permutation_indicator_displacement_norm_le_card_mul_markov_defect p f
    hf i

theorem normalizedIndicatorDisplacement_mul
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (q r : Equiv.Perm V) :
    normalizedIndicatorDisplacement p f (q * r) =
      normalizedIndicatorDisplacement p f q +
        permutationUnitary q (normalizedIndicatorDisplacement p f r) := by
  unfold normalizedIndicatorDisplacement
  rw [permutationUnitary_mul]
  simp only [map_smul, map_sub, smul_sub]
  abel

theorem norm_normalizedIndicatorDisplacement_list_prod_le
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hdefect : permutationMarkov p (indicatorVector f) ≠
      indicatorVector f) (w : List ι) :
    ‖normalizedIndicatorDisplacement p f (w.map p).prod‖ ≤
      (Fintype.card ι : ℝ) * w.length := by
  induction w with
  | nil =>
      simp only [normalizedIndicatorDisplacement, List.map_nil, List.prod_nil,
        permutationUnitary_one, sub_self,
        smul_zero, norm_zero, List.length_nil, CharP.cast_eq_zero, mul_zero, Std.le_refl]
  | cons i w ih =>
      rw [List.map_cons, List.prod_cons,
        normalizedIndicatorDisplacement_mul]
      calc
        ‖normalizedIndicatorDisplacement p f (p i) +
          permutationUnitary (p i)
            (normalizedIndicatorDisplacement p f (w.map p).prod)‖ ≤
            ‖normalizedIndicatorDisplacement p f (p i)‖ +
              ‖permutationUnitary (p i)
                (normalizedIndicatorDisplacement p f (w.map p).prod)‖ :=
          norm_add_le _ _
        _ = ‖normalizedIndicatorDisplacement p f (p i)‖ +
              ‖normalizedIndicatorDisplacement p f (w.map p).prod‖ := by
          rw [(permutationUnitary (p i)).norm_map]
        _ ≤ (Fintype.card ι : ℝ) +
              (Fintype.card ι : ℝ) * w.length :=
          add_le_add
            (norm_normalizedIndicatorDisplacement_generator_le
              p f hf hdefect i) ih
        _ = (Fintype.card ι : ℝ) * (i :: w).length := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

def normalizedIndicatorDefect
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    EuclideanSpace ℂ V :=
  ((‖permutationMarkov p (indicatorVector f) -
      indicatorVector f‖ : ℝ) : ℂ)⁻¹ •
    (permutationMarkov p (indicatorVector f) - indicatorVector f)

theorem norm_normalizedIndicatorDefect
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hdefect : permutationMarkov p (indicatorVector f) ≠
      indicatorVector f) :
    ‖normalizedIndicatorDefect p f‖ = 1 := by
  have hne : ‖permutationMarkov p (indicatorVector f) -
      indicatorVector f‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hdefect)
  simp only [normalizedIndicatorDefect, norm_smul, norm_inv, Complex.norm_real, norm_norm, ne_eq,
    hne,
    not_false_eq_true, inv_mul_cancel₀]

theorem average_permutation_indicator_displacement
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    (Fintype.card ι : ℂ)⁻¹ •
        (∑ i, (permutationUnitary (p i) (indicatorVector f) -
          indicatorVector f)) =
      permutationMarkov p (indicatorVector f) - indicatorVector f := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_sub, smul_smul, ne_eq, hd, not_false_eq_true, inv_mul_cancel₀, one_smul,
    permutationMarkov]

theorem average_normalizedIndicatorDisplacement
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    (Fintype.card ι : ℂ)⁻¹ •
        (∑ i, normalizedIndicatorDisplacement p f (p i)) =
      normalizedIndicatorDefect p f := by
  simp_rw [normalizedIndicatorDisplacement]
  rw [← Finset.smul_sum, smul_comm,
    average_permutation_indicator_displacement]
  rfl

theorem normalizedIndicatorDisplacement_cocycle_of_agree_on_support
    {G ι V : Type*} [Group G] [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (a g : G)
    (hroot : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * g) x = (σ a * σ g) x) :
    normalizedIndicatorDisplacement p f (σ (a * g)) =
      normalizedIndicatorDisplacement p f (σ a) +
        permutationUnitary (σ a)
          (normalizedIndicatorDisplacement p f (σ g)) := by
  unfold normalizedIndicatorDisplacement
  rw [permutationUnitary_model_mul_of_agree_on_support
    σ a g (indicatorVector f) hroot]
  simp only [map_smul, map_sub, smul_sub]
  abel

def normalizedPairDisplacement
    {G ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (q : G × G) :
    EuclideanSpace ℂ V :=
  normalizedIndicatorDisplacement p f (σ q.1) -
    normalizedIndicatorDisplacement p f (σ q.2)

theorem normalizedPairDisplacement_diagonal
    {G ι V : Type*} [Group G] [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (a g h : G)
    (hg : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * g) x = (σ a * σ g) x)
    (hh : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * h) x = (σ a * σ h) x) :
    normalizedPairDisplacement p f σ (a * g, a * h) =
      permutationUnitary (σ a)
        (normalizedPairDisplacement p f σ (g, h)) := by
  unfold normalizedPairDisplacement
  rw [normalizedIndicatorDisplacement_cocycle_of_agree_on_support
    p f σ a g hg,
    normalizedIndicatorDisplacement_cocycle_of_agree_on_support
      p f σ a h hh, map_sub]
  abel

theorem normalizedPairDisplacement_inner_diagonal
    {G ι V : Type*} [Group G] [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (a g h j k : G)
    (hg : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * g) x = (σ a * σ g) x)
    (hh : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * h) x = (σ a * σ h) x)
    (hj : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * j) x = (σ a * σ j) x)
    (hk : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * k) x = (σ a * σ k) x) :
    @inner ℂ (EuclideanSpace ℂ V) _
      (normalizedPairDisplacement p f σ (a * g, a * h))
      (normalizedPairDisplacement p f σ (a * j, a * k)) =
    @inner ℂ (EuclideanSpace ℂ V) _
      (normalizedPairDisplacement p f σ (g, h))
      (normalizedPairDisplacement p f σ (j, k)) := by
  rw [normalizedPairDisplacement_diagonal p f σ a g h hg hh,
    normalizedPairDisplacement_diagonal p f σ a j k hj hk]
  exact (permutationUnitary (σ a)).inner_map_map _ _

theorem normalizedPairDisplacement_add
    {G ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (g h j : G) :
    normalizedPairDisplacement p f σ (g, h) +
      normalizedPairDisplacement p f σ (h, j) =
        normalizedPairDisplacement p f σ (g, j) := by
  unfold normalizedPairDisplacement
  abel

theorem norm_normalizedPairDisplacement_le_of_words
    {G ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hdefect : permutationMarkov p (indicatorVector f) ≠
      indicatorVector f)
    (σ : G → Equiv.Perm V) (w : G → List ι)
    (hw : ∀ g, σ g = ((w g).map p).prod) (g h : G) :
    ‖normalizedPairDisplacement p f σ (g, h)‖ ≤
      (Fintype.card ι : ℝ) *
        ((w g).length + (w h).length) := by
  unfold normalizedPairDisplacement
  calc
    ‖normalizedIndicatorDisplacement p f (σ g) -
      normalizedIndicatorDisplacement p f (σ h)‖ ≤
        ‖normalizedIndicatorDisplacement p f (σ g)‖ +
          ‖normalizedIndicatorDisplacement p f (σ h)‖ :=
      norm_sub_le _ _
    _ ≤ (Fintype.card ι : ℝ) * (w g).length +
          (Fintype.card ι : ℝ) * (w h).length := by
      rw [hw g, hw h]
      exact add_le_add
        (norm_normalizedIndicatorDisplacement_list_prod_le
          p f hf hdefect (w g))
        (norm_normalizedIndicatorDisplacement_list_prod_le
          p f hf hdefect (w h))
    _ = (Fintype.card ι : ℝ) *
          ((w g).length + (w h).length) := by
      ring

theorem exists_hyperfilter_gram_limit_of_pointwise_bound
    {I : Type*} {H : ℕ → Type*}
    [∀ n, SeminormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (v : ∀ n, I → H n) (B : I → ℝ)
    (hbound : ∀ n i, ‖v n i‖ ≤ B i) :
    ∃ K : Matrix I I ℂ,
      ∀ i j, Tendsto (fun n => ⟪v n i, v n j⟫_ℂ)
        (Filter.hyperfilter ℕ) (𝓝 (K i j)) := by
  have hinnerbound (n : ℕ) (i j : I) :
      ‖⟪v n i, v n j⟫_ℂ‖ ≤ B i * B j := by
    calc
      ‖⟪v n i, v n j⟫_ℂ‖ ≤ ‖v n i‖ * ‖v n j‖ :=
        norm_inner_le_norm _ _
      _ ≤ B i * B j :=
        mul_le_mul (hbound n i) (hbound n j)
          (norm_nonneg _) ((norm_nonneg _).trans (hbound n i))
  let b : ℕ → (q : I × I) →
      Metric.closedBall (0 : ℂ) (B q.1 * B q.2) :=
    fun n q =>
      ⟨⟪v n q.1, v n q.2⟫_ℂ,
        by simpa only [Metric.mem_closedBall, dist_zero_right] using hinnerbound n q.1 q.2⟩
  let u := Ultrafilter.map b (Filter.hyperfilter ℕ)
  let L : (q : I × I) →
      Metric.closedBall (0 : ℂ) (B q.1 * B q.2) := u.lim
  let K : Matrix I I ℂ := fun i j => (L (i, j) : ℂ)
  refine ⟨K, ?_⟩
  have hu : Tendsto b (Filter.hyperfilter ℕ) (𝓝 L) := by
    change Filter.map b (↑(Filter.hyperfilter ℕ) : Filter ℕ) ≤
      𝓝 u.lim
    simpa only [u, Ultrafilter.coe_map] using u.le_nhds_lim
  intro i j
  have heval :
      Tendsto
        (fun f : (q : I × I) →
          Metric.closedBall (0 : ℂ) (B q.1 * B q.2) => f (i, j))
        (𝓝 L) (𝓝 (L (i, j))) :=
    (continuous_apply (i, j)).tendsto L
  have hval :
      Tendsto
        (fun z : Metric.closedBall (0 : ℂ) (B i * B j) => (z : ℂ))
        (𝓝 (L (i, j))) (𝓝 (L (i, j) : ℂ)) :=
    continuous_subtype_val.tendsto (L (i, j))
  have hcomp := hval.comp (heval.comp hu)
  change Tendsto (fun n => ⟪v n i, v n j⟫_ℂ)
    (Filter.hyperfilter ℕ) (𝓝 (L (i, j) : ℂ)) at hcomp
  exact hcomp

theorem gram_posSemidef_infinite
    {I H : Type*} [SeminormedAddCommGroup H]
    [InnerProductSpace ℂ H] (v : I → H) :
    (Matrix.gram ℂ v).PosSemidef := by
  refine ⟨Matrix.isHermitian_gram ℂ v, ?_⟩
  intro c
  calc
    (0 : ℂ) ≤
        ⟪c.sum (fun i z => z • v i),
          c.sum (fun i z => z • v i)⟫_ℂ :=
      RCLike.nonneg_iff.mpr ⟨inner_self_nonneg, inner_self_im _⟩
    _ = c.sum (fun i z =>
          c.sum (fun j w => star z * (Matrix.gram ℂ v) i j * w)) := by
      rw [Finsupp.sum_inner]
      apply Finsupp.sum_congr
      intro i hi
      rw [Finsupp.inner_sum]
      apply Finsupp.sum_congr
      intro j hj
      simp only [inner_smul_left, inner_smul_right,
        Matrix.gram_apply, RCLike.star_def]
      ring

theorem exists_hyperfilter_positive_gram_kernel_of_pointwise_bound
    {I : Type*} {H : ℕ → Type*}
    [∀ n, SeminormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (v : ∀ n, I → H n) (B : I → ℝ)
    (hbound : ∀ n i, ‖v n i‖ ≤ B i) :
    ∃ K : Matrix I I ℂ,
      K.PosSemidef ∧
      ∀ i j, Tendsto (fun n => ⟪v n i, v n j⟫_ℂ)
        (Filter.hyperfilter ℕ) (𝓝 (K i j)) := by
  obtain ⟨K, hconv⟩ :=
    exists_hyperfilter_gram_limit_of_pointwise_bound v B hbound
  have hhermitian : K.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    apply tendsto_nhds_unique (hconv j i).star
    have hsymm :
        (fun n => star ⟪v n j, v n i⟫_ℂ) =
          (fun n => ⟪v n i, v n j⟫_ℂ) := by
      funext n
      exact inner_conj_symm _ _
    rw [hsymm]
    exact hconv i j
  refine ⟨K, ⟨hhermitian, ?_⟩, hconv⟩
  intro c
  have hquadratic :
      Tendsto
        (fun n => c.sum fun i z =>
          c.sum fun j w => star z * ⟪v n i, v n j⟫_ℂ * w)
        (Filter.hyperfilter ℕ)
        (𝓝 (c.sum fun i z =>
          c.sum fun j w => star z * K i j * w)) := by
    simpa only [Finsupp.sum] using
      tendsto_finsetSum c.support (fun i _ =>
        tendsto_finsetSum c.support (fun j _ =>
          (tendsto_const_nhds.mul (hconv i j)).mul
            tendsto_const_nhds))
  apply ge_of_tendsto hquadratic
  exact Eventually.of_forall fun n =>
    (gram_posSemidef_infinite (v n)).2 c

theorem exists_hyperfilter_diagonal_positive_pair_kernel
    {G : Type*} [Group G] {H : ℕ → Type*}
    [∀ n, SeminormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (v : ∀ n, G × G → H n) (B : G × G → ℝ)
    (hbound : ∀ n q, ‖v n q‖ ≤ B q)
    (hdiagonal : ∀ a g h j k : G,
      ∀ᶠ n in Filter.atTop,
        ⟪v n (a * g, a * h), v n (a * j, a * k)⟫_ℂ =
          ⟪v n (g, h), v n (j, k)⟫_ℂ)
    (hadd : ∀ n (g h j : G),
      v n (g, h) + v n (h, j) = v n (g, j)) :
    ∃ K : Matrix (G × G) (G × G) ℂ,
      K.PosSemidef ∧
      (∀ a g h j k : G,
        K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k)) ∧
      (∀ g h j : G, ∀ q : G × G,
        K (g, h) q + K (h, j) q = K (g, j) q) ∧
      ∀ q r, Tendsto (fun n => ⟪v n q, v n r⟫_ℂ)
        (Filter.hyperfilter ℕ) (𝓝 (K q r)) := by
  obtain ⟨K, hpositive, hconv⟩ :=
    exists_hyperfilter_positive_gram_kernel_of_pointwise_bound
      v B hbound
  refine ⟨K, hpositive, ?_, ?_, hconv⟩
  · intro a g h j k
    have hevent :
        (fun n =>
          ⟪v n (a * g, a * h), v n (a * j, a * k)⟫_ℂ) =ᶠ[
          (Filter.hyperfilter ℕ : Filter ℕ)]
            (fun n => ⟪v n (g, h), v n (j, k)⟫_ℂ) :=
      (hdiagonal a g h j k).filter_mono Nat.hyperfilter_le_atTop
    exact tendsto_nhds_unique
      (hconv (a * g, a * h) (a * j, a * k))
      (Tendsto.congr' hevent.symm (hconv (g, h) (j, k)))
  · intro g h j q
    have haddconv :=
      (hconv (g, h) q).add (hconv (h, j) q)
    have hfunctions :
        (fun n =>
          ⟪v n (g, h), v n q⟫_ℂ +
            ⟪v n (h, j), v n q⟫_ℂ) =
          (fun n => ⟪v n (g, j), v n q⟫_ℂ) := by
      funext n
      rw [← inner_add_left, hadd]
    exact tendsto_nhds_unique haddconv
      (by rw [hfunctions]; exact hconv (g, j) q)

theorem exists_hyperfilter_diagonal_positive_pair_kernel_of_rooted_indicators
    {G ι : Type*} [Group G] [Fintype ι] [Nonempty ι]
    {V : ℕ → Type*} [∀ n, Fintype (V n)]
    (p : ∀ n, ι → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (w : G → List ι)
    (hf : ∀ n x, f n x = 0 ∨ f n x = 1)
    (hdefect : ∀ n, permutationMarkov (p n) (indicatorVector (f n)) ≠
      indicatorVector (f n))
    (hw : ∀ n g, σ n g = ((w g).map (p n)).prod)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x) :
    ∃ K : Matrix (G × G) (G × G) ℂ,
      K.PosSemidef ∧
      (∀ a g h j k : G,
        K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k)) ∧
      (∀ g h j : G, ∀ q : G × G,
        K (g, h) q + K (h, j) q = K (g, j) q) ∧
      ∀ q r,
        Tendsto
          (fun n =>
            ⟪normalizedPairDisplacement (p n) (f n) (σ n) q,
              normalizedPairDisplacement (p n) (f n) (σ n) r⟫_ℂ)
          (Filter.hyperfilter ℕ) (𝓝 (K q r)) := by
  let v : ∀ n, G × G → EuclideanSpace ℂ (V n) :=
    fun n q => normalizedPairDisplacement (p n) (f n) (σ n) q
  let B : G × G → ℝ := fun q =>
    (Fintype.card ι : ℝ) * ((w q.1).length + (w q.2).length)
  apply exists_hyperfilter_diagonal_positive_pair_kernel v B
  · intro n q
    exact norm_normalizedPairDisplacement_le_of_words
      (p n) (f n) (hf n) (hdefect n) (σ n) w (hw n) q.1 q.2
  · intro a g h j k
    filter_upwards [hroot a g, hroot a h, hroot a j, hroot a k]
      with n hg hh hj hk
    exact normalizedPairDisplacement_inner_diagonal
      (p n) (f n) (σ n) a g h j k hg hh hj hk
  · intro n g h j
    exact normalizedPairDisplacement_add (p n) (f n) (σ n) g h j

def scalarOperatorKernel {I : Type u} (K : Matrix I I ℂ) :
    Matrix I I (ℂ →L[ℂ] ℂ) :=
  fun g h => ContinuousLinearMap.toSpanSingleton ℂ (K g h)

theorem scalarOperatorKernel_posSemidef {I : Type u}
    (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    (scalarOperatorKernel K).PosSemidef := by
  apply ((RKHS.posSemidef_tfae
    (K := scalarOperatorKernel K)).out 2 0).mp
  constructor
  · apply Matrix.IsHermitian.ext
    intro g h
    change star (ContinuousLinearMap.toSpanSingleton ℂ (K h g)) =
      ContinuousLinearMap.toSpanSingleton ℂ (K g h)
    rw [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_toSpanSingleton]
    apply ContinuousLinearMap.ext
    intro z
    calc
      (innerSL ℂ (K h g)) z = star (K h g) * z := by
        simp only [innerSL_apply_apply, RCLike.inner_apply',
          RCLike.star_def]
      _ = K g h * z := by rw [hK.isHermitian.apply g h]
      _ = z * K g h := mul_comm _ _
      _ = (ContinuousLinearMap.toSpanSingleton ℂ (K g h)) z := by
        simp only [ContinuousLinearMap.toSpanSingleton_apply,
          smul_eq_mul]
  · intro c
    have hc := hK.2 c
    have hreal :
        0 ≤ RCLike.re (c.sum fun g z =>
          c.sum fun h w => star z * K g h * w) :=
      (RCLike.nonneg_iff.mp hc).1
    simp only [scalarOperatorKernel,
      ContinuousLinearMap.toSpanSingleton_apply,
      RCLike.inner_apply', smul_eq_mul, map_mul]
    simpa only [← RCLike.star_def, hK.isHermitian.apply,
      mul_assoc, mul_left_comm, mul_comm] using hreal

theorem preKernel_inner_single {I : Type u}
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (i j : I × ℂ) (z w : ℂ) :
    ⟪(Finsupp.single i z : RKHS.H₀ (scalarOperatorKernel K)),
      (Finsupp.single j w : RKHS.H₀ (scalarOperatorKernel K))⟫_ℂ =
      star z * w *
        ⟪scalarOperatorKernel K j.1 i.1 i.2, j.2⟫_ℂ := by
  change
    (Finsupp.single i z).sum (fun yu c =>
      (Finsupp.single j w).sum (fun xv d =>
        star c * d *
          ⟪scalarOperatorKernel K xv.1 yu.1 yu.2, xv.2⟫_ℂ)) = _
  simp only [RCLike.star_def, RCLike.inner_apply, mul_zero, zero_mul, Finsupp.sum_single_index,
    map_zero]

def actionPreKernelTranslation {G I : Type u} [Group G]
    (K : Matrix I I ℂ) (ρ : G →* Equiv.Perm I) (a : G) :
    RKHS.H₀ (scalarOperatorKernel K) ≃ₗ[ℂ]
      RKHS.H₀ (scalarOperatorKernel K) :=
  Finsupp.domLCongr ((ρ a).prodCongr (Equiv.refl ℂ))

theorem actionPreKernelTranslation_inner {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) (f g : RKHS.H₀ (scalarOperatorKernel K)) :
    ⟪actionPreKernelTranslation K ρ a f,
      actionPreKernelTranslation K ρ a g⟫_ℂ = ⟪f, g⟫_ℂ := by
  induction f using Finsupp.induction_linear generalizing g with
  | zero => simp only [map_zero, inner_zero_left]
  | add f₁ f₂ ih₁ ih₂ =>
    simp only [map_add, inner_add_left, ih₁ g, ih₂ g]
  | single i z =>
    induction g using Finsupp.induction_linear with
    | zero => simp only [map_zero, inner_zero_right]
    | add g₁ g₂ ih₁ ih₂ =>
      simp only [map_add, inner_add_right, ih₁, ih₂]
    | single j w =>
      simp only [actionPreKernelTranslation,
        Finsupp.domLCongr_single, preKernel_inner_single,
        scalarOperatorKernel,
        ContinuousLinearMap.toSpanSingleton_apply]
      change
        star z * w * ⟪i.2 • K (ρ a j.1) (ρ a i.1), j.2⟫_ℂ =
          star z * w * ⟪i.2 • K j.1 i.1, j.2⟫_ℂ
      rw [hinv]

def actionPreKernelTranslationIsometry {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) :
    RKHS.H₀ (scalarOperatorKernel K) ≃ₗᵢ[ℂ]
      RKHS.H₀ (scalarOperatorKernel K) :=
  (actionPreKernelTranslation K ρ a).isometryOfInner
    (actionPreKernelTranslation_inner K ρ hinv a)

def actionKernelTranslationMap {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) :
    RKHS.OfKernel (scalarOperatorKernel K) →L[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K) :=
  ContinuousLinearMap.completion
    ((actionPreKernelTranslationIsometry K ρ hinv a).toLinearIsometry.toContinuousLinearMap)

@[simp]
theorem actionKernelTranslationMap_coe {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) (f : RKHS.H₀ (scalarOperatorKernel K)) :
    actionKernelTranslationMap K ρ hinv a
      (f : RKHS.OfKernel (scalarOperatorKernel K)) =
        (actionPreKernelTranslation K ρ a f :
          RKHS.OfKernel (scalarOperatorKernel K)) := by
  exact ContinuousLinearMap.completion_apply_coe
    ((actionPreKernelTranslationIsometry K ρ hinv a).toLinearIsometry.toContinuousLinearMap) f

theorem actionKernelTranslationMap_isometry {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) : Isometry (actionKernelTranslationMap K ρ hinv a) := by
  change Isometry (UniformSpace.Completion.map
    (actionPreKernelTranslationIsometry K ρ hinv a))
  exact (actionPreKernelTranslationIsometry K ρ hinv a).isometry.completion_map

theorem actionPreKernelTranslation_mul_apply {G I : Type u} [Group G]
    (K : Matrix I I ℂ) (ρ : G →* Equiv.Perm I)
    (a b : G) (f : RKHS.H₀ (scalarOperatorKernel K)) :
    actionPreKernelTranslation K ρ (a * b) f =
      actionPreKernelTranslation K ρ a
        (actionPreKernelTranslation K ρ b f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i z =>
    simp only [actionPreKernelTranslation,
      Finsupp.domLCongr_single]
    change Finsupp.single (ρ (a * b) i.1, i.2) z =
      Finsupp.single (ρ a (ρ b i.1), i.2) z
    rw [map_mul]
    rfl

@[simp]
theorem actionPreKernelTranslation_one_apply {G I : Type u} [Group G]
    (K : Matrix I I ℂ) (ρ : G →* Equiv.Perm I)
    (f : RKHS.H₀ (scalarOperatorKernel K)) :
    actionPreKernelTranslation K ρ 1 f = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i z =>
    simp only [actionPreKernelTranslation,
      Finsupp.domLCongr_single]
    change Finsupp.single (ρ 1 i.1, i.2) z =
      Finsupp.single (i.1, i.2) z
    simp only [map_one, Equiv.Perm.coe_one, id_eq, Prod.mk.eta]

theorem actionKernelTranslationMap_mul_apply {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a b : G) (x : RKHS.OfKernel (scalarOperatorKernel K)) :
    actionKernelTranslationMap K ρ hinv (a * b) x =
      actionKernelTranslationMap K ρ hinv a
        (actionKernelTranslationMap K ρ hinv b x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (actionKernelTranslationMap K ρ hinv (a * b)).continuous
      ((actionKernelTranslationMap K ρ hinv a).continuous.comp
        (actionKernelTranslationMap K ρ hinv b).continuous)
  | ih f =>
    simp only [actionKernelTranslationMap_coe,
      actionPreKernelTranslation_mul_apply]

@[simp]
theorem actionKernelTranslationMap_one_apply {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (x : RKHS.OfKernel (scalarOperatorKernel K)) :
    actionKernelTranslationMap K ρ hinv 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (actionKernelTranslationMap K ρ hinv 1).continuous
      continuous_id
  | ih f =>
    simp only [actionKernelTranslationMap_coe,
      actionPreKernelTranslation_one_apply]

def actionKernelTranslationLinearEquiv {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) :
    RKHS.OfKernel (scalarOperatorKernel K) ≃ₗ[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K) where
  toLinearMap := (actionKernelTranslationMap K ρ hinv a).toLinearMap
  invFun := actionKernelTranslationMap K ρ hinv a⁻¹
  left_inv x := by
    calc
      actionKernelTranslationMap K ρ hinv a⁻¹
        (actionKernelTranslationMap K ρ hinv a x) =
          actionKernelTranslationMap K ρ hinv (a⁻¹ * a) x :=
            (actionKernelTranslationMap_mul_apply
              K ρ hinv a⁻¹ a x).symm
      _ = x := by simp only [inv_mul_cancel, actionKernelTranslationMap_one_apply]
  right_inv x := by
    calc
      actionKernelTranslationMap K ρ hinv a
        (actionKernelTranslationMap K ρ hinv a⁻¹ x) =
          actionKernelTranslationMap K ρ hinv (a * a⁻¹) x :=
            (actionKernelTranslationMap_mul_apply
              K ρ hinv a a⁻¹ x).symm
      _ = x := by simp only [mul_inv_cancel, actionKernelTranslationMap_one_apply]

def actionKernelTranslationUnitary {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) :
    RKHS.OfKernel (scalarOperatorKernel K) ≃ₗᵢ[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K) where
  toLinearEquiv := actionKernelTranslationLinearEquiv K ρ hinv a
  norm_map' :=
    (actionKernelTranslationMap_isometry K ρ hinv a).norm_map_of_map_zero
      (map_zero (actionKernelTranslationMap K ρ hinv a))

def actionKernelUnitaryRepresentation {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j) :
    G →* (RKHS.OfKernel (scalarOperatorKernel K) ≃ₗᵢ[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K)) where
  toFun := actionKernelTranslationUnitary K ρ hinv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change actionKernelTranslationMap K ρ hinv 1 x = x
    exact actionKernelTranslationMap_one_apply K ρ hinv x
  map_mul' a b := by
    apply LinearIsometryEquiv.ext
    intro x
    change actionKernelTranslationMap K ρ hinv (a * b) x =
      actionKernelTranslationMap K ρ hinv a
        (actionKernelTranslationMap K ρ hinv b x)
    exact actionKernelTranslationMap_mul_apply K ρ hinv a b x

def diagonalPairAction (G : Type u) [Group G] :
    G →* Equiv.Perm (G × G) where
  toFun a := (Equiv.mulLeft a).prodCongr (Equiv.mulLeft a)
  map_one' := by
    apply Equiv.ext
    intro x
    exact Prod.ext (one_mul x.1) (one_mul x.2)
  map_mul' a b := by
    apply Equiv.ext
    intro x
    apply Prod.ext
    · exact mul_assoc a b x.1
    · exact mul_assoc a b x.2

def diagonalPairKernelUnitaryRepresentation {G : Type u} [Group G]
    (K : Matrix (G × G) (G × G) ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (hinv : ∀ a g h j k : G,
      K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k)) :
    G →* (RKHS.OfKernel (scalarOperatorKernel K) ≃ₗᵢ[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K)) :=
  actionKernelUnitaryRepresentation K (diagonalPairAction G)
    (fun a x y => hinv a x.1 x.2 y.1 y.2)

theorem ofKernel_kerFun_one_eq_coe_single
    {I : Type u} (L : Matrix I I (ℂ →L[ℂ] ℂ))
    [Fact L.PosSemidef] (i : I) :
    RKHS.kerFun (RKHS.OfKernel L) i (1 : ℂ) =
      ((Finsupp.single (i, (1 : ℂ)) (1 : ℂ) : RKHS.H₀ L) :
        RKHS.OfKernel L) := by
  simp only [RKHS.kerFun, RKHS.coeCLM, ContinuousLinearMap.proj_pi,
    ContinuousLinearMap.adjoint_adjoint,
    LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]

theorem actionKernelUnitaryRepresentation_kerFun_one
    {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) (i : I) :
    actionKernelUnitaryRepresentation K ρ hinv a
      (RKHS.kerFun (RKHS.OfKernel (scalarOperatorKernel K)) i
        (1 : ℂ)) =
      RKHS.kerFun (RKHS.OfKernel (scalarOperatorKernel K))
        (ρ a i) (1 : ℂ) := by
  rw [ofKernel_kerFun_one_eq_coe_single
    (scalarOperatorKernel K) i,
    ofKernel_kerFun_one_eq_coe_single
      (scalarOperatorKernel K) (ρ a i)]
  change
    actionKernelTranslationMap K ρ hinv a
      ((Finsupp.single (i, (1 : ℂ)) (1 : ℂ) :
        RKHS.H₀ (scalarOperatorKernel K)) :
          RKHS.OfKernel (scalarOperatorKernel K)) = _
  rw [actionKernelTranslationMap_coe]
  simp only [actionPreKernelTranslation, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_single, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq]

theorem diagonalPairKernelUnitaryRepresentation_kerFun_one
    {G : Type u} [Group G]
    (K : Matrix (G × G) (G × G) ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (hinv : ∀ a g h j k : G,
      K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k))
    (a g h : G) :
    diagonalPairKernelUnitaryRepresentation K hinv a
      (RKHS.kerFun (RKHS.OfKernel (scalarOperatorKernel K))
        (g, h) (1 : ℂ)) =
      RKHS.kerFun (RKHS.OfKernel (scalarOperatorKernel K))
        (a * g, a * h) (1 : ℂ) := by
  exact actionKernelUnitaryRepresentation_kerFun_one K
    (diagonalPairAction G)
    (fun a x y => hinv a x.1 x.2 y.1 y.2) a (g, h)

structure HilbertKernelRealization {I : Type u}
    (K : Matrix I I ℂ) where
  carrier : Type u
  [normed : NormedAddCommGroup carrier]
  [inner : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  vector : I → carrier
  gram : ∀ g h, ⟪vector g, vector h⟫_ℂ = K g h

instance hilbertKernelRealizationNormedAddCommGroup
    {I : Type u} {K : Matrix I I ℂ}
    (R : HilbertKernelRealization K) : NormedAddCommGroup R.carrier :=
  R.normed

instance hilbertKernelRealizationInnerProductSpace
    {I : Type u} {K : Matrix I I ℂ}
    (R : HilbertKernelRealization K) : InnerProductSpace ℂ R.carrier :=
  R.inner

instance hilbertKernelRealizationCompleteSpace
    {I : Type u} {K : Matrix I I ℂ}
    (R : HilbertKernelRealization K) : CompleteSpace R.carrier :=
  R.complete

theorem hilbertKernelRealization_pair_vector_add
    {G : Type u} (K : Matrix (G × G) (G × G) ℂ)
    (R : HilbertKernelRealization K)
    (hadd : ∀ g h j : G, ∀ q : G × G,
      K (g, h) q + K (h, j) q = K (g, j) q)
    (g h j : G) :
    R.vector (g, h) + R.vector (h, j) = R.vector (g, j) := by
  have horth (q : G × G) :
      ⟪R.vector (g, h) + R.vector (h, j) - R.vector (g, j),
        R.vector q⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_add_left,
      R.gram, R.gram, R.gram, hadd]
    exact sub_self _
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_sub_right, inner_add_right,
    horth (g, h), horth (h, j), horth (g, j)]
  simp only [add_zero, sub_self]

structure EquivariantHilbertKernelRealization
    {G : Type u} [Group G]
    (K : Matrix (G × G) (G × G) ℂ) where
  realization : HilbertKernelRealization K
  representation : G →*
    (realization.carrier ≃ₗᵢ[ℂ] realization.carrier)
  equivariant : ∀ a g h : G,
    representation a (realization.vector (g, h)) =
      realization.vector (a * g, a * h)

theorem exists_equivariantHilbertKernelRealization
    {G : Type u} [Group G]
    (K : Matrix (G × G) (G × G) ℂ)
    (hpositive : K.PosSemidef)
    (hdiagonal : ∀ a g h j k : G,
      K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k)) :
    Nonempty (EquivariantHilbertKernelRealization K) := by
  let : Fact (scalarOperatorKernel K).PosSemidef :=
    ⟨scalarOperatorKernel_posSemidef K hpositive⟩
  let H := RKHS.OfKernel (scalarOperatorKernel K)
  let R : HilbertKernelRealization K := {
    carrier := H
    vector := fun q => RKHS.kerFun H q (1 : ℂ)
    gram := by
      intro q r
      rw [RKHS.kerFun_inner, RKHS.kerFun_apply,
        RKHS.OfKernel.kernel_ofKernel]
      simp only [scalarOperatorKernel, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
        one_mul,
        RCLike.inner_apply, map_one, mul_one]
  }
  refine ⟨{
    realization := R
    representation := diagonalPairKernelUnitaryRepresentation K hdiagonal
    equivariant := ?_
  }⟩
  intro a g h
  exact diagonalPairKernelUnitaryRepresentation_kerFun_one
    K hdiagonal a g h

def equivariantPairCocycle {G : Type u} [Group G]
    {K : Matrix (G × G) (G × G) ℂ}
    (R : EquivariantHilbertKernelRealization K) (g : G) :
    R.realization.carrier :=
  R.realization.vector (g, 1)

theorem equivariantPairCocycle_mul {G : Type u} [Group G]
    (K : Matrix (G × G) (G × G) ℂ)
    (R : EquivariantHilbertKernelRealization K)
    (hadd : ∀ g h j : G, ∀ q : G × G,
      K (g, h) q + K (h, j) q = K (g, j) q)
    (a g : G) :
    equivariantPairCocycle R (a * g) =
      equivariantPairCocycle R a +
        R.representation a (equivariantPairCocycle R g) := by
  unfold equivariantPairCocycle
  rw [R.equivariant]
  simp only [mul_one]
  rw [add_comm]
  exact (hilbertKernelRealization_pair_vector_add K R.realization
    hadd (a * g) a 1).symm

theorem normalizedPairDisplacement_generator_of_model
    {G ι V : Type*} [Group G] [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (s : ι → G)
    (hone : σ 1 = 1) (hgenerator : ∀ i, σ (s i) = p i)
    (i : ι) :
    normalizedPairDisplacement p f σ (s i, 1) =
      normalizedIndicatorDisplacement p f (p i) := by
  simp only [normalizedPairDisplacement, normalizedIndicatorDisplacement, hgenerator, hone,
    permutationUnitary_one, sub_self, smul_zero, sub_zero]

theorem norm_average_normalizedPairDisplacement_of_model
    {G ι V : Type*} [Group G] [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (s : ι → G)
    (hone : σ 1 = 1) (hgenerator : ∀ i, σ (s i) = p i)
    (hdefect : permutationMarkov p (indicatorVector f) ≠
      indicatorVector f) :
    ‖(Fintype.card ι : ℂ)⁻¹ •
      ∑ i, normalizedPairDisplacement p f σ (s i, 1)‖ = 1 := by
  simp_rw [normalizedPairDisplacement_generator_of_model
    p f σ s hone hgenerator]
  rw [average_normalizedIndicatorDisplacement,
    norm_normalizedIndicatorDefect p f hdefect]

theorem inner_smul_finset_sum_self
    {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (z : I → E) (F : Finset I) (c : ℂ) :
    ⟪c • ∑ i ∈ F, z i, c • ∑ i ∈ F, z i⟫_ℂ =
      star c * (∑ i ∈ F, ∑ j ∈ F, ⟪z i, z j⟫_ℂ) * c := by
  rw [inner_smul_left, inner_smul_right, sum_inner]
  simp_rw [inner_sum]
  simp only [RCLike.star_def]
  ring

theorem tendsto_norm_sq_smul_finset_sum_of_gram
    {N I H : Type*} {E : N → Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [∀ n, NormedAddCommGroup (E n)]
    [∀ n, InnerProductSpace ℂ (E n)]
    (l : Filter N) (z : ∀ n, I → E n) (v : I → H)
    (hgram : ∀ i j,
      Tendsto (fun n => ⟪z n i, z n j⟫_ℂ) l
        (𝓝 ⟪v i, v j⟫_ℂ))
    (F : Finset I) (c : ℂ) :
    Tendsto (fun n => ‖c • ∑ i ∈ F, z n i‖ ^ 2) l
      (𝓝 (‖c • ∑ i ∈ F, v i‖ ^ 2)) := by
  have hsum :
      Tendsto
        (fun n => ∑ i ∈ F, ∑ j ∈ F, ⟪z n i, z n j⟫_ℂ) l
        (𝓝 (∑ i ∈ F, ∑ j ∈ F, ⟪v i, v j⟫_ℂ)) :=
    tendsto_finsetSum F fun i _ =>
      tendsto_finsetSum F fun j _ => hgram i j
  have hinner :
      Tendsto
        (fun n => ⟪c • ∑ i ∈ F, z n i,
          c • ∑ i ∈ F, z n i⟫_ℂ) l
        (𝓝 ⟪c • ∑ i ∈ F, v i,
          c • ∑ i ∈ F, v i⟫_ℂ) := by
    simpa only [inner_smul_finset_sum_self] using
      (tendsto_const_nhds.mul hsum).mul tendsto_const_nhds
  have hreal := (Complex.continuous_re.tendsto _).comp hinner
  change Tendsto
    (fun n => (⟪c • ∑ i ∈ F, z n i,
      c • ∑ i ∈ F, z n i⟫_ℂ).re) l
    (𝓝 (⟪c • ∑ i ∈ F, v i,
      c • ∑ i ∈ F, v i⟫_ℂ).re) at hreal
  convert hreal using 1
  · funext n
    exact norm_sq_eq_re_inner (𝕜 := ℂ) (c • ∑ i ∈ F, z n i)
  · congr 1
    exact norm_sq_eq_re_inner (𝕜 := ℂ) (c • ∑ i ∈ F, v i)

theorem norm_smul_finset_sum_eq_one_of_gram
    {N I H : Type*} {E : N → Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [∀ n, NormedAddCommGroup (E n)]
    [∀ n, InnerProductSpace ℂ (E n)]
    (l : Filter N) [NeBot l]
    (z : ∀ n, I → E n) (v : I → H)
    (hgram : ∀ i j,
      Tendsto (fun n => ⟪z n i, z n j⟫_ℂ) l
        (𝓝 ⟪v i, v j⟫_ℂ))
    (F : Finset I) (c : ℂ)
    (hnorm : ∀ n, ‖c • ∑ i ∈ F, z n i‖ = 1) :
    ‖c • ∑ i ∈ F, v i‖ = 1 := by
  have hlimit :=
    tendsto_norm_sq_smul_finset_sum_of_gram l z v hgram F c
  have hone :
      Tendsto (fun n => ‖c • ∑ i ∈ F, z n i‖ ^ 2) l
        (𝓝 (1 : ℝ)) := by
    simpa only [hnorm, one_pow] using
      (tendsto_const_nhds :
        Tendsto (fun _ : N => (1 : ℝ)) l (𝓝 1))
  have hsq : ‖c • ∑ i ∈ F, v i‖ ^ 2 = 1 :=
    tendsto_nhds_unique hlimit hone
  nlinarith [norm_nonneg (c • ∑ i ∈ F, v i)]

theorem exists_equivariant_hilbert_normalized_rooted_pair_realization
    {G ι : Type u} [Group G] [Fintype ι] [Nonempty ι]
    {V : ℕ → Type u} [∀ n, Fintype (V n)]
    (p : ∀ n, ι → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (s : ι → G) (w : G → List ι)
    (hf : ∀ n x, f n x = 0 ∨ f n x = 1)
    (hdefect : ∀ n, permutationMarkov (p n) (indicatorVector (f n)) ≠
      indicatorVector (f n))
    (hw : ∀ n g, σ n g = ((w g).map (p n)).prod)
    (hone : ∀ n, σ n 1 = 1)
    (hgenerator : ∀ n i, σ n (s i) = p n i)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x) :
    ∃ (K : Matrix (G × G) (G × G) ℂ)
      (R : EquivariantHilbertKernelRealization K),
      K.PosSemidef ∧
      (∀ a g h j k : G,
        K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k)) ∧
      (∀ a g h : G,
        R.representation a (R.realization.vector (g, h)) =
          R.realization.vector (a * g, a * h)) ∧
      (∀ g h j : G,
        R.realization.vector (g, h) +
          R.realization.vector (h, j) =
            R.realization.vector (g, j)) ∧
      (∀ a g : G,
        equivariantPairCocycle R (a * g) =
          equivariantPairCocycle R a +
            R.representation a (equivariantPairCocycle R g)) ∧
      ‖(Fintype.card ι : ℂ)⁻¹ •
        ∑ i, equivariantPairCocycle R (s i)‖ = 1 ∧
      ∀ q r,
        Tendsto
          (fun n =>
            ⟪normalizedPairDisplacement (p n) (f n) (σ n) q,
              normalizedPairDisplacement (p n) (f n) (σ n) r⟫_ℂ)
          (Filter.hyperfilter ℕ)
          (𝓝 ⟪R.realization.vector q,
            R.realization.vector r⟫_ℂ) := by
  obtain ⟨K, hpositive, hdiagonal, hadd, hconv⟩ :=
    exists_hyperfilter_diagonal_positive_pair_kernel_of_rooted_indicators
      p f σ w hf hdefect hw hroot
  obtain ⟨R⟩ :=
    exists_equivariantHilbertKernelRealization K hpositive hdiagonal
  refine ⟨K, R, hpositive, hdiagonal, R.equivariant, ?_, ?_, ?_, ?_⟩
  · exact hilbertKernelRealization_pair_vector_add
      K R.realization hadd
  · exact equivariantPairCocycle_mul K R hadd
  · apply norm_smul_finset_sum_eq_one_of_gram
      (Filter.hyperfilter ℕ)
      (fun n i => normalizedPairDisplacement (p n) (f n) (σ n)
        (s i, 1))
      (fun i => equivariantPairCocycle R (s i))
      (F := Finset.univ) (c := (Fintype.card ι : ℂ)⁻¹)
    · intro i j
      simpa only [equivariantPairCocycle, R.realization.gram] using
        hconv (s i, 1) (s j, 1)
    · intro n
      simpa only using
        norm_average_normalizedPairDisplacement_of_model (p n) (f n) (σ n) s (hone n) (hgenerator n)
          (hdefect n)
  · intro q r
    simpa only [R.realization.gram] using hconv q r

end KunRootedIndicatorCrossing

namespace KunThomInvariantOrthogonal

section

open Filter Topology
open scoped ComplexConjugate Pointwise

universe u v

variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def invariantSubmodule (π : UnitaryRepresentation G H) :
    Submodule ℂ H where
  carrier := {x | ∀ g : G, π g x = x}
  zero_mem' := by
    intro g
    exact map_zero (π g)
  add_mem' := by
    intro x y hx hy g
    rw [map_add, hx g, hy g]
  smul_mem' := by
    intro c x hx g
    rw [map_smul, hx g]

theorem map_mem_invariantSubmodule_orthogonal
    (π : UnitaryRepresentation G H) (g : G) {x : H}
    (hx : x ∈ (invariantSubmodule π)ᗮ) :
    π g x ∈ (invariantSubmodule π)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hysymm : (π g).symm y = y := by
    have hyinv : π g⁻¹ y = y := hy g⁻¹
    simpa only [map_inv, LinearIsometryEquiv.inv_def] using hyinv
  calc
    @inner ℂ H _ y (π g x) =
        @inner ℂ H _ ((π g).symm y) x := by
          simpa only [LinearIsometryEquiv.symm_apply_apply] using ((π g).symm.inner_map_map y (π g
            x)).symm
    _ = @inner ℂ H _ y x := by rw [hysymm]
    _ = 0 := (Submodule.mem_orthogonal _ _).mp hx y hy

def orthogonalLinearIsometryEquiv
    (π : UnitaryRepresentation G H) (g : G) :
    (invariantSubmodule π)ᗮ ≃ₗᵢ[ℂ] (invariantSubmodule π)ᗮ where
  toFun x := ⟨π g x, map_mem_invariantSubmodule_orthogonal π g x.property⟩
  invFun x :=
    ⟨π g⁻¹ x, map_mem_invariantSubmodule_orthogonal π g⁻¹ x.property⟩
  left_inv x := by
    apply Subtype.ext
    change π g⁻¹ (π g (x : H)) = x
    simp only [map_inv, LinearIsometryEquiv.inv_def, LinearIsometryEquiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    change π g (π g⁻¹ (x : H)) = x
    simp only [map_inv, LinearIsometryEquiv.inv_def, LinearIsometryEquiv.apply_symm_apply]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (π g) (x : H) (y : H)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (π g) c (x : H)
  norm_map' x := (π g).norm_map (x : H)

def orthogonalRepresentation (π : UnitaryRepresentation G H) :
    UnitaryRepresentation G ((invariantSubmodule π)ᗮ) where
  toFun := orthogonalLinearIsometryEquiv π
  map_one' := by
    ext x
    change π 1 (x : H) = x
    simp only [map_one, LinearIsometryEquiv.coe_one, id_eq]
  map_mul' g h := by
    ext x
    change π (g * h) (x : H) = π g (π h (x : H))
    rw [map_mul]
    rfl

theorem orthogonalRepresentation_no_fixed
    (π : UnitaryRepresentation G H)
    (x : (invariantSubmodule π)ᗮ)
    (hx : ∀ g : G, orthogonalRepresentation π g x = x) :
    x = 0 := by
  have hxinv : (x : H) ∈ invariantSubmodule π := by
    intro g
    exact congrArg Subtype.val (hx g)
  have hinner : @inner ℂ H _ (x : H) (x : H) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hxinv x.property
  apply Subtype.ext
  change (x : H) = 0
  exact inner_self_eq_zero.mp hinner

theorem cocycle_one
    (π : UnitaryRepresentation G H) (b : G → H)
    (hb : ∀ g h : G, b (g * h) = b g + π g (b h)) :
    b 1 = 0 := by
  have hcancel : b 1 + b 1 = b 1 + 0 := by
    simpa only [add_zero, add_eq_left, map_one, LinearIsometryEquiv.coe_one, id_eq, mul_one] using
      (hb 1 1).symm
  exact add_left_cancel hcancel

theorem inner_cocycle_inv_of_invariant
    (π : UnitaryRepresentation G H) (b : G → H)
    (hb : ∀ g h : G, b (g * h) = b g + π g (b h))
    (y : H) (hy : ∀ g : G, π g y = y) (g : G) :
    @inner ℂ H _ y (b g⁻¹) = -@inner ℂ H _ y (b g) := by
  have hysymm : (π g).symm y = y := by
    have hyinv := hy g⁻¹
    simpa only [map_inv, LinearIsometryEquiv.inv_def] using hyinv
  have htransport :
      @inner ℂ H _ y (π g (b g⁻¹)) = @inner ℂ H _ y (b g⁻¹) := by
    calc
      @inner ℂ H _ y (π g (b g⁻¹)) =
          @inner ℂ H _ ((π g).symm y) (b g⁻¹) := by
            simpa only [LinearIsometryEquiv.symm_apply_apply] using ((π g).symm.inner_map_map y (π g
              (b g⁻¹))).symm
      _ = @inner ℂ H _ y (b g⁻¹) := by rw [hysymm]
  have hsum : b g + π g (b g⁻¹) = 0 := by
    calc
      b g + π g (b g⁻¹) = b (g * g⁻¹) := (hb g g⁻¹).symm
      _ = b 1 := by rw [mul_inv_cancel]
      _ = 0 := cocycle_one π b hb
  have hinner :
      @inner ℂ H _ y (b g) + @inner ℂ H _ y (b g⁻¹) = 0 := by
    have h := congrArg (fun x : H => @inner ℂ H _ y x) hsum
    simpa only [CStarModule.inner_add_right, htransport, inner_zero_right] using h
  apply (add_eq_zero_iff_eq_neg).mp
  simpa only [add_comm] using hinner

theorem inner_cocycle_sum_eq_zero_of_invariant
    (π : UnitaryRepresentation G H) (b : G → H)
    (hb : ∀ g h : G, b (g * h) = b g + π g (b h))
    (S : Finset G) (hS : ∀ g ∈ S, g⁻¹ ∈ S)
    (y : H) (hy : ∀ g : G, π g y = y) :
    @inner ℂ H _ y (∑ g ∈ S, b g) = 0 := by
  classical
  rw [inner_sum]
  have hsymmetric : S⁻¹ = S := by
    ext g
    constructor
    · intro hg
      obtain ⟨a, ha, rfl⟩ := Finset.mem_inv.mp hg
      exact hS a ha
    · intro hg
      apply Finset.mem_inv.mpr
      exact ⟨g⁻¹, hS g hg, inv_inv g⟩
  have hneg :
      (∑ g ∈ S, @inner ℂ H _ y (b g)) =
        -(∑ g ∈ S, @inner ℂ H _ y (b g)) := by
    calc
      (∑ g ∈ S, @inner ℂ H _ y (b g)) =
          ∑ g ∈ S⁻¹, @inner ℂ H _ y (b g) := by rw [hsymmetric]
      _ = ∑ g ∈ S, @inner ℂ H _ y (b g⁻¹) :=
        Finset.sum_inv_index S (fun g => @inner ℂ H _ y (b g))
      _ = ∑ g ∈ S, -@inner ℂ H _ y (b g) := by
        apply Finset.sum_congr rfl
        intro g hg
        exact inner_cocycle_inv_of_invariant π b hb y hy g
      _ = -(∑ g ∈ S, @inner ℂ H _ y (b g)) := by
        rw [Finset.sum_neg_distrib]
  have hdouble :
      (2 : ℂ) * (∑ g ∈ S, @inner ℂ H _ y (b g)) = 0 := by
    calc
      (2 : ℂ) * (∑ g ∈ S, @inner ℂ H _ y (b g)) =
          (∑ g ∈ S, @inner ℂ H _ y (b g)) +
            (∑ g ∈ S, @inner ℂ H _ y (b g)) := two_mul _
      _ = (∑ g ∈ S, @inner ℂ H _ y (b g)) +
          -(∑ g ∈ S, @inner ℂ H _ y (b g)) :=
        congrArg (fun z : ℂ => (∑ g ∈ S, @inner ℂ H _ y (b g)) + z) hneg
      _ = 0 := add_neg_cancel _
  exact (mul_eq_zero.mp hdouble).resolve_left (by norm_num)

theorem inner_smul_cocycle_sum_eq_zero_of_invariant
    (π : UnitaryRepresentation G H) (b : G → H)
    (hb : ∀ g h : G, b (g * h) = b g + π g (b h))
    (S : Finset G) (hS : ∀ g ∈ S, g⁻¹ ∈ S) (c : ℂ)
    (y : H) (hy : ∀ g : G, π g y = y) :
    @inner ℂ H _ y (c • ∑ g ∈ S, b g) = 0 := by
  rw [inner_smul_right, inner_cocycle_sum_eq_zero_of_invariant π b hb S hS y hy,
    mul_zero]

theorem norm_add_le_two_sub_sq_div_four
    (x y : H) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδtwo : δ ≤ 2)
    (hnorm : ‖y‖ = ‖x‖)
    (hseparated : δ * ‖x‖ ≤ ‖x - y‖) :
    ‖x + y‖ ≤ (2 - δ ^ 2 / 4) * ‖x‖ := by
  have hpar := parallelogram_law_with_norm ℂ x y
  have hsq : (δ * ‖x‖) ^ 2 ≤ ‖x - y‖ ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hδ (norm_nonneg x))
      (norm_nonneg (x - y))).mpr hseparated
  have hδsq : δ ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (2 - δ), sq_nonneg δ]
  have htarget : 0 ≤ (2 - δ ^ 2 / 4) * ‖x‖ :=
    mul_nonneg (by nlinarith) (norm_nonneg x)
  have hadd :
      ‖x + y‖ ^ 2 ≤ ((2 - δ ^ 2 / 4) * ‖x‖) ^ 2 := by
    rw [hnorm] at hpar
    nlinarith [sq_nonneg (δ ^ 2 * ‖x‖)]
  exact (sq_le_sq₀ (norm_nonneg (x + y)) htarget).mp hadd

omit [InnerProductSpace ℂ H] in
theorem norm_finset_sum_le_pair_add
    {X : Type*} (S : Finset X) (f : X → H)
    (a b : X) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (r : ℝ) (hnorm : ∀ s ∈ S, ‖f s‖ = r) :
    ‖∑ s ∈ S, f s‖ ≤
      ‖f a + f b‖ + ((S.card : ℝ) - 2) * r := by
  classical
  let T : Finset X := (S.erase a).erase b
  have hb' : b ∈ S.erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hsum :
      (∑ s ∈ S, f s) = f a + f b + ∑ s ∈ T, f s := by
    calc
      (∑ s ∈ S, f s) = f a + ∑ s ∈ S.erase a, f s :=
        (Finset.add_sum_erase S f ha).symm
      _ = f a + (f b + ∑ s ∈ T, f s) := by
        congr 1
        exact (Finset.add_sum_erase (S.erase a) f hb').symm
      _ = f a + f b + ∑ s ∈ T, f s := by abel
  have hcard : (T.card : ℝ) = (S.card : ℝ) - 2 := by
    dsimp [T]
    rw [Finset.cast_card_erase_of_mem hb',
      Finset.cast_card_erase_of_mem ha]
    ring
  have htail : (∑ s ∈ T, ‖f s‖) = (T.card : ℝ) * r := by
    calc
      (∑ s ∈ T, ‖f s‖) = ∑ _s ∈ T, r := by
        apply Finset.sum_congr rfl
        intro s hs
        exact hnorm s
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hs))
      _ = (T.card : ℝ) * r := by simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    ‖∑ s ∈ S, f s‖ = ‖(f a + f b) + ∑ s ∈ T, f s‖ := by
      rw [hsum]
    _ ≤ ‖f a + f b‖ + ‖∑ s ∈ T, f s‖ :=
      norm_add_le _ _
    _ ≤ ‖f a + f b‖ + ∑ s ∈ T, ‖f s‖ := by
      exact add_le_add (le_refl _) (norm_sum_le T f)
    _ = ‖f a + f b‖ + (T.card : ℝ) * r := by rw [htail]
    _ = ‖f a + f b‖ + ((S.card : ℝ) - 2) * r := by
      rw [hcard]

end

section

open Filter Topology
open scoped ComplexConjugate Pointwise

universe u v

variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem kazhdan_generator_displacement_of_orthogonal_invariants
    [CompleteSpace H] (P : KazhdanPair.{u, v} G)
    (π : UnitaryRepresentation G H) (x : H)
    (hx : x ≠ 0)
    (horth : ∀ y : H,
      (∀ g : G, π g y = y) → @inner ℂ H _ y x = 0) :
    ∃ g ∈ P.generators,
      P.kazhdanConstant * ‖x‖ ≤ ‖π g x - x‖ := by
  let z : (invariantSubmodule π)ᗮ :=
    ⟨x, (Submodule.mem_orthogonal _ _).mpr
      (fun y hy => horth y hy)⟩
  have hz : z ≠ 0 := by
    intro h
    apply hx
    exact congrArg Subtype.val h
  obtain ⟨g, hg, hgap⟩ :=
    kazhdan_generator_displacement P
      (orthogonalRepresentation π)
      (orthogonalRepresentation_no_fixed π) z hz
  refine ⟨g, hg, ?_⟩
  simpa only [Submodule.coe_norm, orthogonalRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
    orthogonalLinearIsometryEquiv, map_inv, LinearIsometryEquiv.coe_inv, LinearIsometryEquiv.coe_mk,
      LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, AddSubgroupClass.coe_sub] using hgap

theorem kazhdan_generator_sum_contraction
    [CompleteSpace H] (P : KazhdanPair.{u, v} G)
    (π : UnitaryRepresentation G H)
    (S : Finset G) (hone : 1 ∈ S)
    (hsub : P.generators ⊆ S) (x : H)
    (horth : ∀ y : H,
      (∀ g : G, π g y = y) → @inner ℂ H _ y x = 0) :
    ‖∑ g ∈ S, π g x‖ ≤
      ((S.card : ℝ) - P.kazhdanConstant ^ 2 / 4) * ‖x‖ := by
  classical
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, Finset.sum_const_zero, norm_zero, mul_zero, Std.le_refl]
  obtain ⟨g, hg, hgap⟩ :=
    kazhdan_generator_displacement_of_orthogonal_invariants
      P π x hx horth
  have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hupper : ‖π g x - x‖ ≤ 2 * ‖x‖ := by
    calc
      ‖π g x - x‖ ≤ ‖π g x‖ + ‖x‖ := norm_sub_le _ _
      _ = 2 * ‖x‖ := by rw [(π g).norm_map]; ring
  have hκtwo : P.kazhdanConstant ≤ 2 :=
    le_of_mul_le_mul_right (hgap.trans hupper) hnormpos
  have hgone : g ≠ 1 := by
    intro h
    subst g
    have hpos : 0 < P.kazhdanConstant * ‖x‖ :=
      mul_pos P.positive hnormpos
    have hbad : P.kazhdanConstant * ‖x‖ ≤ 0 := by
      simpa only [map_one, LinearIsometryEquiv.coe_one, id_eq, sub_self, norm_zero] using hgap
    exact not_le_of_gt hpos hbad
  have hpair :
      ‖x + π g x‖ ≤
        (2 - P.kazhdanConstant ^ 2 / 4) * ‖x‖ := by
    apply norm_add_le_two_sub_sq_div_four x (π g x)
      P.kazhdanConstant P.positive.le hκtwo
      ((π g).norm_map x)
    rw [norm_sub_rev]
    exact hgap
  have hsum := norm_finset_sum_le_pair_add
    S (fun a : G => π a x) 1 g hone (hsub hg) (Ne.symm hgone)
    ‖x‖ (fun a _ => (π a).norm_map x)
  calc
    ‖∑ a ∈ S, π a x‖ ≤
        ‖π 1 x + π g x‖ + ((S.card : ℝ) - 2) * ‖x‖ := hsum
    _ = ‖x + π g x‖ + ((S.card : ℝ) - 2) * ‖x‖ := by
      simp only [map_one, LinearIsometryEquiv.coe_one, id_eq]
    _ ≤ (2 - P.kazhdanConstant ^ 2 / 4) * ‖x‖ +
        ((S.card : ℝ) - 2) * ‖x‖ :=
      add_le_add hpair (le_refl _)
    _ = ((S.card : ℝ) - P.kazhdanConstant ^ 2 / 4) * ‖x‖ := by
      ring

def unitaryFinsetMarkov
    (π : UnitaryRepresentation G H)
    (S : Finset G) (x : H) : H :=
  ((S.card : ℂ)⁻¹) • S.sum (fun g => π g x)

def kazhdanMarkovContractionFactor
    (P : KazhdanPair.{u, v} G) (S : Finset G) : ℝ :=
  max 0 (1 - P.kazhdanConstant ^ 2 / (4 * (S.card : ℝ)))

theorem kazhdanMarkovContractionFactor_lt_one
    (P : KazhdanPair.{u, v} G)
    (S : Finset G) (hS : S.Nonempty) :
    kazhdanMarkovContractionFactor P S < 1 := by
  have hcard : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hpositive :
      0 < P.kazhdanConstant ^ 2 / (4 * (S.card : ℝ)) := by
    exact div_pos (sq_pos_of_pos P.positive)
      (mul_pos (by norm_num) hcard)
  unfold kazhdanMarkovContractionFactor
  exact max_lt (by norm_num) (by linarith)

theorem kazhdanMarkovContractionFactor_nonneg
    (P : KazhdanPair.{u, v} G) (S : Finset G) :
    0 ≤ kazhdanMarkovContractionFactor P S :=
  le_max_left _ _

theorem unitaryFinsetMarkov_norm_le
    [CompleteSpace H] (P : KazhdanPair.{u, v} G)
    (π : UnitaryRepresentation G H)
    (S : Finset G) (hone : 1 ∈ S)
    (hsub : P.generators ⊆ S) (x : H)
    (horth : ∀ y : H,
      (∀ g : G, π g y = y) → @inner ℂ H _ y x = 0) :
    ‖unitaryFinsetMarkov π S x‖ ≤
      kazhdanMarkovContractionFactor P S * ‖x‖ := by
  have hcard : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  have hsum := kazhdan_generator_sum_contraction
    P π S hone hsub x horth
  calc
    ‖unitaryFinsetMarkov π S x‖ =
        (S.card : ℝ)⁻¹ * ‖∑ g ∈ S, π g x‖ := by
      simp only [unitaryFinsetMarkov, norm_smul, norm_inv, RCLike.norm_natCast]
    _ ≤ (S.card : ℝ)⁻¹ *
        (((S.card : ℝ) - P.kazhdanConstant ^ 2 / 4) * ‖x‖) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcard.le)
    _ = (1 - P.kazhdanConstant ^ 2 /
        (4 * (S.card : ℝ))) * ‖x‖ := by
      field_simp
    _ ≤ kazhdanMarkovContractionFactor P S * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      exact le_max_right 0 _

theorem unitaryFinsetMarkov_orthogonal_invariants
    (π : UnitaryRepresentation G H)
    (S : Finset G) (x : H)
    (horth : ∀ y : H,
      (∀ g : G, π g y = y) → @inner ℂ H _ y x = 0) :
    ∀ y : H, (∀ g : G, π g y = y) →
      @inner ℂ H _ y (unitaryFinsetMarkov π S x) = 0 := by
  have hx : x ∈ (invariantSubmodule π)ᗮ :=
    (Submodule.mem_orthogonal _ _).mpr (fun y hy => horth y hy)
  have hsum : (∑ g ∈ S, π g x) ∈ (invariantSubmodule π)ᗮ := by
    apply Submodule.sum_mem
    intro g hg
    exact map_mem_invariantSubmodule_orthogonal π g hx
  have hmarkov :
      unitaryFinsetMarkov π S x ∈ (invariantSubmodule π)ᗮ := by
    exact (invariantSubmodule π)ᗮ.smul_mem _ hsum
  intro y hy
  exact (Submodule.mem_orthogonal _ _).mp hmarkov y hy

theorem unitaryFinsetMarkov_iterate_norm_le
    [CompleteSpace H] (P : KazhdanPair.{u, v} G)
    (π : UnitaryRepresentation G H)
    (S : Finset G) (hone : 1 ∈ S)
    (hsub : P.generators ⊆ S) (x : H)
    (horth : ∀ y : H,
      (∀ g : G, π g y = y) → @inner ℂ H _ y x = 0)
    (n : ℕ) :
    ‖((unitaryFinsetMarkov π S)^[n]) x‖ ≤
      kazhdanMarkovContractionFactor P S ^ n * ‖x‖ := by
  have horthn (k : ℕ) :
      ∀ y : H, (∀ g : G, π g y = y) →
        @inner ℂ H _ y (((unitaryFinsetMarkov π S)^[k]) x) = 0 := by
    induction k with
    | zero => simpa only [Function.iterate_zero, id_eq] using horth
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact unitaryFinsetMarkov_orthogonal_invariants
        π S (((unitaryFinsetMarkov π S)^[k]) x) ih
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, pow_zero, one_mul, Std.le_refl]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      ‖unitaryFinsetMarkov π S
          (((unitaryFinsetMarkov π S)^[n]) x)‖ ≤
        kazhdanMarkovContractionFactor P S *
          ‖((unitaryFinsetMarkov π S)^[n]) x‖ :=
        unitaryFinsetMarkov_norm_le P π S hone hsub _ (horthn n)
      _ ≤ kazhdanMarkovContractionFactor P S *
          (kazhdanMarkovContractionFactor P S ^ n * ‖x‖) :=
        mul_le_mul_of_nonneg_left ih
          (kazhdanMarkovContractionFactor_nonneg P S)
      _ = kazhdanMarkovContractionFactor P S ^ n.succ * ‖x‖ := by
        rw [pow_succ]
        ring

end

end KunThomInvariantOrthogonal

namespace KunRootedWordPower

open Filter Topology
open KunRootedIndicatorCrossing
open KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise

universe u v w

def pairedWordAverage
    {G ι E : Type*} [Group G] [Fintype ι]
    [AddCommMonoid E] [Module ℂ E]
    (s : ι → G) (z : G × G → E) :
    ℕ → G × G → E
  | 0, q => z q
  | k + 1, q =>
      (Fintype.card ι : ℂ)⁻¹ •
        ∑ i, pairedWordAverage s z k (s i * q.1, s i * q.2)

def pairedDefectWordAverage
    {G ι E : Type*} [Group G] [Fintype ι]
    [AddCommMonoid E] [Module ℂ E]
    (s : ι → G) (z : G × G → E) (k : ℕ) : E :=
  (Fintype.card ι : ℂ)⁻¹ •
    ∑ i, pairedWordAverage s z k (s i, 1)

theorem inner_smul_fintype_sum
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : ι → E) (c : ℂ) :
    ⟪c • ∑ i, x i, c • ∑ j, y j⟫_ℂ =
      star c * (∑ i, ∑ j, ⟪x i, y j⟫_ℂ) * c := by
  rw [inner_smul_left, inner_smul_right, sum_inner]
  simp_rw [inner_sum]
  simp only [RCLike.star_def]
  ring

theorem tendsto_inner_pairedWordAverage_of_gram
    {G ι N H : Type*} [Group G] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {E : N → Type*}
    [∀ n, NormedAddCommGroup (E n)]
    [∀ n, InnerProductSpace ℂ (E n)]
    (l : Filter N) (s : ι → G)
    (z : ∀ n, G × G → E n) (v : G × G → H)
    (hgram : ∀ q r,
      Tendsto (fun n => ⟪z n q, z n r⟫_ℂ) l
        (𝓝 ⟪v q, v r⟫_ℂ))
    (k : ℕ) (q r : G × G) :
    Tendsto
      (fun n =>
        ⟪pairedWordAverage s (z n) k q,
          pairedWordAverage s (z n) k r⟫_ℂ)
      l
      (𝓝 ⟪pairedWordAverage s v k q,
        pairedWordAverage s v k r⟫_ℂ) := by
  induction k generalizing q r with
  | zero =>
      simpa only [pairedWordAverage] using hgram q r
  | succ k ih =>
      have hsum :
          Tendsto
            (fun n =>
              ∑ i : ι, ∑ j : ι,
                ⟪pairedWordAverage s (z n) k
                    (s i * q.1, s i * q.2),
                  pairedWordAverage s (z n) k
                    (s j * r.1, s j * r.2)⟫_ℂ)
            l
            (𝓝 (∑ i : ι, ∑ j : ι,
              ⟪pairedWordAverage s v k
                  (s i * q.1, s i * q.2),
                pairedWordAverage s v k
                  (s j * r.1, s j * r.2)⟫_ℂ)) :=
        tendsto_finsetSum Finset.univ fun i _ =>
          tendsto_finsetSum Finset.univ fun j _ =>
            ih (s i * q.1, s i * q.2)
              (s j * r.1, s j * r.2)
      simpa only [pairedWordAverage, inner_smul_fintype_sum] using
        (tendsto_const_nhds.mul hsum).mul tendsto_const_nhds

theorem tendsto_norm_pairedDefectWordAverage_of_gram
    {G ι N H : Type*} [Group G] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {E : N → Type*}
    [∀ n, NormedAddCommGroup (E n)]
    [∀ n, InnerProductSpace ℂ (E n)]
    (l : Filter N) (s : ι → G)
    (z : ∀ n, G × G → E n) (v : G × G → H)
    (hgram : ∀ q r,
      Tendsto (fun n => ⟪z n q, z n r⟫_ℂ) l
        (𝓝 ⟪v q, v r⟫_ℂ))
    (k : ℕ) :
    Tendsto
      (fun n => ‖pairedDefectWordAverage s (z n) k‖)
      l
      (𝓝 ‖pairedDefectWordAverage s v k‖) := by
  have hsq :
      Tendsto
        (fun n => ‖pairedDefectWordAverage s (z n) k‖ ^ 2)
        l
        (𝓝 (‖pairedDefectWordAverage s v k‖ ^ 2)) := by
    simpa only [pairedDefectWordAverage] using
      KunRootedIndicatorCrossing.tendsto_norm_sq_smul_finset_sum_of_gram
        l
        (fun n (i : ι) =>
          pairedWordAverage s (z n) k (s i, 1))
        (fun i : ι => pairedWordAverage s v k (s i, 1))
        (fun i j =>
          tendsto_inner_pairedWordAverage_of_gram l s z v hgram k
            (s i, 1) (s j, 1))
        Finset.univ (Fintype.card ι : ℂ)⁻¹
  have hroot :=
    (Real.continuous_sqrt.tendsto
      (‖pairedDefectWordAverage s v k‖ ^ 2)).comp hsq
  convert hroot using 1
  · funext n
    change ‖pairedDefectWordAverage s (z n) k‖ =
      Real.sqrt (‖pairedDefectWordAverage s (z n) k‖ ^ 2)
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · congr 1
    rw [Real.sqrt_sq (norm_nonneg _)]

def permutationMarkovLinear
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) :
    EuclideanSpace ℂ V →ₗ[ℂ] EuclideanSpace ℂ V :=
  (Fintype.card ι : ℂ)⁻¹ •
    ∑ i, (permutationUnitary (p i)).toLinearEquiv.toLinearMap

@[simp]
theorem permutationMarkovLinear_apply
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (x : EuclideanSpace ℂ V) :
    permutationMarkovLinear p x = permutationMarkov p x := by
  simp only [permutationMarkovLinear, LinearMap.smul_apply, LinearMap.coe_sum, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, Finset.sum_apply, permutationMarkov]

theorem permutationMarkovLinear_pow_apply
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (k : ℕ)
    (x : EuclideanSpace ℂ V) :
    ((permutationMarkovLinear p) ^ k) x =
      ((permutationMarkov p)^[k]) x := by
  induction k with
  | zero => simp only [pow_zero, Module.End.one_apply, Function.iterate_zero, id_eq]
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply,
        Function.iterate_succ_apply']
      rw [ih, permutationMarkovLinear_apply]

theorem permutationMarkov_pair_of_rooted
    {G ι V : Type*} [Group G] [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (s : ι → G)
    (hgenerator : ∀ i, σ (s i) = p i)
    (q : G × G)
    (hroot : ∀ i,
      (∀ x : V, indicatorVector f x ≠ 0 →
        σ (s i * q.1) x = (σ (s i) * σ q.1) x) ∧
      (∀ x : V, indicatorVector f x ≠ 0 →
        σ (s i * q.2) x = (σ (s i) * σ q.2) x)) :
    permutationMarkov p (normalizedPairDisplacement p f σ q) =
      pairedWordAverage s (normalizedPairDisplacement p f σ) 1 q := by
  simp only [permutationMarkov, pairedWordAverage]
  apply congrArg (fun x => (Fintype.card ι : ℂ)⁻¹ • x)
  apply Finset.sum_congr rfl
  intro i _
  rw [← hgenerator i]
  exact (normalizedPairDisplacement_diagonal p f σ
    (s i) q.1 q.2 (hroot i).1 (hroot i).2).symm

theorem eventually_permutationMarkov_pair_of_rooted
    {G ι : Type*} [Group G] [Fintype ι]
    {V : ℕ → Type*} [∀ n, Fintype (V n)]
    (p : ∀ n, ι → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (s : ι → G)
    (hgenerator : ∀ n i, σ n (s i) = p n i)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x)
    (q : G × G) :
    ∀ᶠ n in Filter.atTop,
      permutationMarkov (p n)
        (normalizedPairDisplacement (p n) (f n) (σ n) q) =
        pairedWordAverage s
          (normalizedPairDisplacement (p n) (f n) (σ n)) 1 q := by
  have hnodes :
      ∀ᶠ n in Filter.atTop, ∀ i : ι,
        (∀ x : V n, indicatorVector (f n) x ≠ 0 →
          σ n (s i * q.1) x =
            (σ n (s i) * σ n q.1) x) ∧
        (∀ x : V n, indicatorVector (f n) x ≠ 0 →
          σ n (s i * q.2) x =
            (σ n (s i) * σ n q.2) x) :=
    (Filter.eventually_all).2 fun i =>
      (hroot (s i) q.1).and (hroot (s i) q.2)
  filter_upwards [hnodes] with n hn
  exact permutationMarkov_pair_of_rooted
    (p n) (f n) (σ n) s (hgenerator n) q hn

theorem eventually_linear_pairedWordAverage_pow
    {G ι N : Type*} [Group G] [Fintype ι]
    {E : N → Type*}
    [∀ n, AddCommMonoid (E n)]
    [∀ n, Module ℂ (E n)]
    (l : Filter N) (s : ι → G)
    (L : ∀ n, E n →ₗ[ℂ] E n)
    (z : ∀ n, G × G → E n)
    (hbase : ∀ q, ∀ᶠ n in l,
      L n (z n q) = pairedWordAverage s (z n) 1 q)
    (k : ℕ) (q : G × G) :
    ∀ᶠ n in l,
      ((L n) ^ k) (z n q) = pairedWordAverage s (z n) k q := by
  induction k generalizing q with
  | zero =>
      exact Filter.Eventually.of_forall fun n => by
        simp only [pow_zero, Module.End.one_apply, pairedWordAverage]
  | succ k ih =>
      have hnodes :
          ∀ᶠ n in l, ∀ i : ι,
            ((L n) ^ k) (z n (s i * q.1, s i * q.2)) =
              pairedWordAverage s (z n) k
                (s i * q.1, s i * q.2) :=
        (Filter.eventually_all).2 fun i =>
          ih (s i * q.1, s i * q.2)
      filter_upwards [hbase q, hnodes] with n hn hnode
      rw [pow_succ, Module.End.mul_apply, hn,
        pairedWordAverage, pairedWordAverage, map_smul, map_sum]
      apply congrArg (fun x => (Fintype.card ι : ℂ)⁻¹ • x)
      exact Finset.sum_congr rfl fun i _ => hnode i

theorem eventually_linear_pairedDefectWordAverage_pow
    {G ι N : Type*} [Group G] [Fintype ι]
    {E : N → Type*}
    [∀ n, AddCommMonoid (E n)]
    [∀ n, Module ℂ (E n)]
    (l : Filter N) (s : ι → G)
    (L : ∀ n, E n →ₗ[ℂ] E n)
    (z : ∀ n, G × G → E n)
    (hbase : ∀ q, ∀ᶠ n in l,
      L n (z n q) = pairedWordAverage s (z n) 1 q)
    (k : ℕ) :
    ∀ᶠ n in l,
      ((L n) ^ k) (pairedDefectWordAverage s (z n) 0) =
        pairedDefectWordAverage s (z n) k := by
  have hnodes :
      ∀ᶠ n in l, ∀ i : ι,
        ((L n) ^ k) (z n (s i, 1)) =
          pairedWordAverage s (z n) k (s i, 1) :=
    (Filter.eventually_all).2 fun i =>
      eventually_linear_pairedWordAverage_pow l s L z hbase k
        (s i, 1)
  filter_upwards [hnodes] with n hn
  simp only [pairedDefectWordAverage, pairedWordAverage,
    map_smul, map_sum]
  exact congrArg (fun x => (Fintype.card ι : ℂ)⁻¹ • x)
    (Finset.sum_congr rfl fun i _ => hn i)

theorem pairedDefectWordAverage_zero_eq_normalizedIndicatorDefect
    {G ι V : Type*} [Group G] [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (s : ι → G)
    (hone : σ 1 = 1) (hgenerator : ∀ i, σ (s i) = p i) :
    pairedDefectWordAverage s
      (normalizedPairDisplacement p f σ) 0 =
        normalizedIndicatorDefect p f := by
  simp only [pairedDefectWordAverage, pairedWordAverage]
  simp_rw [normalizedPairDisplacement_generator_of_model
    p f σ s hone hgenerator]
  exact average_normalizedIndicatorDisplacement p f

theorem tendsto_norm_normalizedIndicatorDefect_markov_pow
    {G ι H : Type*} [Group G] [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {V : ℕ → Type*} [∀ n, Fintype (V n)]
    (p : ∀ n, ι → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (s : ι → G)
    (v : G × G → H)
    (hone : ∀ n, σ n 1 = 1)
    (hgenerator : ∀ n i, σ n (s i) = p n i)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x)
    (hgram : ∀ q r,
      Tendsto
        (fun n =>
          ⟪normalizedPairDisplacement (p n) (f n) (σ n) q,
            normalizedPairDisplacement (p n) (f n) (σ n) r⟫_ℂ)
        (Filter.hyperfilter ℕ)
        (𝓝 ⟪v q, v r⟫_ℂ))
    (k : ℕ) :
    Tendsto
      (fun n =>
        ‖((permutationMarkov (p n))^[k])
          (normalizedIndicatorDefect (p n) (f n))‖)
      (Filter.hyperfilter ℕ)
      (𝓝 ‖pairedDefectWordAverage s v k‖) := by
  let z : ∀ n, G × G → EuclideanSpace ℂ (V n) :=
    fun n => normalizedPairDisplacement (p n) (f n) (σ n)
  let L : ∀ n, EuclideanSpace ℂ (V n) →ₗ[ℂ]
      EuclideanSpace ℂ (V n) :=
    fun n => permutationMarkovLinear (p n)
  have hbase : ∀ q, ∀ᶠ n in Filter.atTop,
      L n (z n q) = pairedWordAverage s (z n) 1 q := by
    intro q
    simpa only [L, permutationMarkovLinear_apply, z] using
      eventually_permutationMarkov_pair_of_rooted
        p f σ s hgenerator hroot q
  have hp := eventually_linear_pairedDefectWordAverage_pow
    Filter.atTop s L z hbase k
  have hpow :
      ∀ᶠ n in Filter.atTop,
        ((permutationMarkov (p n))^[k])
          (normalizedIndicatorDefect (p n) (f n)) =
            pairedDefectWordAverage s (z n) k := by
    filter_upwards [hp] with n hn
    rw [← permutationMarkovLinear_pow_apply]
    change ((L n) ^ k) (normalizedIndicatorDefect (p n) (f n)) =
      pairedDefectWordAverage s (z n) k
    rw [← pairedDefectWordAverage_zero_eq_normalizedIndicatorDefect
      (p n) (f n) (σ n) s (hone n) (hgenerator n)]
    exact hn
  have hlimit :=
    tendsto_norm_pairedDefectWordAverage_of_gram
      (Filter.hyperfilter ℕ) s z v hgram k
  have heq :
      (fun n =>
        ‖((permutationMarkov (p n))^[k])
          (normalizedIndicatorDefect (p n) (f n))‖) =ᶠ[
            (Filter.hyperfilter ℕ : Filter ℕ)]
        (fun n => ‖pairedDefectWordAverage s (z n) k‖) :=
    (hpow.filter_mono Nat.hyperfilter_le_atTop).mono
      fun n hn => congrArg norm hn
  exact hlimit.congr' heq.symm

def representationFamilyMarkovLinear
    {G ι H : Type*} [Group G] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (s : ι → G) :
    H →ₗ[ℂ] H :=
  (Fintype.card ι : ℂ)⁻¹ •
    ∑ i, (π (s i)).toLinearEquiv.toLinearMap

theorem representationFamilyMarkovLinear_subtype_apply
    {G H : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H)
    (S : Finset G) (x : H) :
    representationFamilyMarkovLinear π (fun i : ↥S => (i : G)) x =
      unitaryFinsetMarkov π S x := by
  simp only [representationFamilyMarkovLinear, Fintype.card_coe, Finset.univ_eq_attach,
    LinearMap.smul_apply,
    LinearMap.coe_sum, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, Finset.sum_apply,
    unitaryFinsetMarkov, ← Finset.sum_coe_sort S]

theorem representationFamilyMarkovLinear_subtype_pow_apply
    {G H : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H)
    (S : Finset G) (k : ℕ) (x : H) :
    (representationFamilyMarkovLinear π
        (fun i : ↥S => (i : G)) ^ k) x =
      ((unitaryFinsetMarkov π S)^[k]) x := by
  induction k with
  | zero => simp only [pow_zero, Module.End.one_apply, Function.iterate_zero, id_eq]
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply,
        Function.iterate_succ_apply', ih,
        representationFamilyMarkovLinear_subtype_apply]

theorem representationFamilyMarkovLinear_pair_of_equivariant
    {G ι H : Type*} [Group G] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H)
    (s : ι → G) (v : G × G → H)
    (hequivariant : ∀ a g h : G,
      π a (v (g, h)) = v (a * g, a * h))
    (q : G × G) :
    representationFamilyMarkovLinear π s (v q) =
      pairedWordAverage s v 1 q := by
  rcases q with ⟨g, h⟩
  simp only [representationFamilyMarkovLinear, LinearMap.smul_apply, LinearMap.coe_sum,
    LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, Finset.sum_apply, hequivariant, pairedWordAverage]

theorem linear_pairedWordAverage_pow
    {G ι E : Type*} [Group G] [Fintype ι]
    [AddCommMonoid E] [Module ℂ E]
    (s : ι → G) (L : E →ₗ[ℂ] E)
    (z : G × G → E)
    (hbase : ∀ q, L (z q) = pairedWordAverage s z 1 q)
    (k : ℕ) (q : G × G) :
    (L ^ k) (z q) = pairedWordAverage s z k q := by
  induction k generalizing q with
  | zero => simp only [pow_zero, Module.End.one_apply, pairedWordAverage]
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hbase q,
        pairedWordAverage, pairedWordAverage,
        map_smul, map_sum]
      apply congrArg (fun x => (Fintype.card ι : ℂ)⁻¹ • x)
      exact Finset.sum_congr rfl fun i _ =>
        ih (s i * q.1, s i * q.2)

theorem pairedDefectWordAverage_eq_unitaryFinsetMarkov_iterate
    {G H : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H)
    (S : Finset G) (v : G × G → H)
    (hequivariant : ∀ a g h : G,
      π a (v (g, h)) = v (a * g, a * h))
    (k : ℕ) :
    pairedDefectWordAverage (fun i : ↥S => (i : G)) v k =
      ((unitaryFinsetMarkov π S)^[k])
        (pairedDefectWordAverage (fun i : ↥S => (i : G)) v 0) := by
  let s : ↥S → G := fun i => (i : G)
  let L : H →ₗ[ℂ] H := representationFamilyMarkovLinear π s
  have hbase : ∀ q, L (v q) = pairedWordAverage s v 1 q :=
    fun q => representationFamilyMarkovLinear_pair_of_equivariant
      π s v hequivariant q
  have hpow :
      (L ^ k) (pairedDefectWordAverage s v 0) =
        pairedDefectWordAverage s v k := by
    simp only [pairedDefectWordAverage, pairedWordAverage,
      map_smul, map_sum]
    apply congrArg (fun x => (Fintype.card (↥S) : ℂ)⁻¹ • x)
    exact Finset.sum_congr rfl fun i _ =>
      linear_pairedWordAverage_pow s L v hbase k (s i, 1)
  have hrewrite :=
    representationFamilyMarkovLinear_subtype_pow_apply
      π S k (pairedDefectWordAverage s v 0)
  exact hpow.symm.trans hrewrite

theorem eventually_normalizedIndicatorDefect_markov_pow_lt_of_rooted
    {G : Type u} [Group G]
    (P : KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    {V : ℕ → Type u} [∀ n, Fintype (V n)]
    (p : ∀ n, ↥S → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (w : G → List ↥S)
    (hf : ∀ n x, f n x = 0 ∨ f n x = 1)
    (hdefect : ∀ n,
      permutationMarkov (p n) (indicatorVector (f n)) ≠
        indicatorVector (f n))
    (hw : ∀ n g, σ n g = ((w g).map (p n)).prod)
    (hone : ∀ n, σ n 1 = 1)
    (hgenerator : ∀ n (i : ↥S), σ n (i : G) = p n i)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ),
      ‖((permutationMarkov (p n))^[k])
          (normalizedIndicatorDefect (p n) (f n))‖ <
        kazhdanMarkovContractionFactor P S ^ k + ε := by
  let : Nonempty (↥S) := ⟨⟨1, honeS⟩⟩
  let s : ↥S → G := fun i => (i : G)
  obtain ⟨K, R, _hpositive, _hdiagonal, hequivariant,
      _hadd, hcocycle, hunit, hgram⟩ :=
    exists_equivariant_hilbert_normalized_rooted_pair_realization
      p f σ s w hf hdefect hw hone hgenerator hroot
  let z : R.realization.carrier :=
    pairedDefectWordAverage s R.realization.vector 0
  have hzone : ‖z‖ = 1 := by
    simpa only [z, pairedDefectWordAverage, pairedWordAverage,
      equivariantPairCocycle] using hunit
  have hzform :
      z = (S.card : ℂ)⁻¹ •
        ∑ g ∈ S, equivariantPairCocycle R g := by
    change
      (Fintype.card (↥S) : ℂ)⁻¹ •
        (∑ i : ↥S, R.realization.vector ((i : G), 1)) =
          (S.card : ℂ)⁻¹ •
            ∑ g ∈ S, equivariantPairCocycle R g
    rw [Fintype.card_coe, ← Finset.sum_coe_sort S]
    rfl
  have horth : ∀ y : R.realization.carrier,
      (∀ g : G, R.representation g y = y) →
        @inner ℂ R.realization.carrier _ y z = 0 := by
    intro y hy
    rw [hzform]
    exact inner_smul_cocycle_sum_eq_zero_of_invariant
      R.representation (equivariantPairCocycle R) hcocycle
      S hsymmetric (S.card : ℂ)⁻¹ y hy
  have hbound :
      ‖pairedDefectWordAverage s R.realization.vector k‖ ≤
        kazhdanMarkovContractionFactor P S ^ k := by
    rw [pairedDefectWordAverage_eq_unitaryFinsetMarkov_iterate
      R.representation S R.realization.vector hequivariant k]
    change ‖((unitaryFinsetMarkov R.representation S)^[k]) z‖ ≤ _
    calc
      ‖((unitaryFinsetMarkov R.representation S)^[k]) z‖ ≤
          kazhdanMarkovContractionFactor P S ^ k * ‖z‖ :=
        unitaryFinsetMarkov_iterate_norm_le
          P R.representation S honeS hcover z horth k
      _ = kazhdanMarkovContractionFactor P S ^ k := by
        rw [hzone, mul_one]
  have hstrict :
      ‖pairedDefectWordAverage s R.realization.vector k‖ <
        kazhdanMarkovContractionFactor P S ^ k + ε :=
    hbound.trans_lt (lt_add_of_pos_right _ hε)
  have hlimit := tendsto_norm_normalizedIndicatorDefect_markov_pow
    p f σ s R.realization.vector hone hgenerator hroot hgram k
  exact hlimit.eventually (Iio_mem_nhds hstrict)

structure RootedIndicatorMarkovModel (G ι : Type u) where
  carrier : Type u
  [fintype : Fintype carrier]
  generator : ι → Equiv.Perm carrier
  indicator : carrier → ℝ
  evaluation : G → Equiv.Perm carrier

instance rootedIndicatorMarkovModelFintype
    {G ι : Type u} (X : RootedIndicatorMarkovModel G ι) : Fintype X.carrier :=
  X.fintype

structure RootedIndicatorMarkovModel.IsGenerated
    {G ι : Type u} [Group G] [Fintype ι]
    (X : RootedIndicatorMarkovModel G ι)
    (s : ι → G) (w : G → List ι) : Prop where
  indicator_mem : ∀ x, X.indicator x = 0 ∨ X.indicator x = 1
  word_evaluation : ∀ g,
    X.evaluation g = ((w g).map X.generator).prod
  identity_evaluation : X.evaluation 1 = 1
  generator_evaluation : ∀ i, X.evaluation (s i) = X.generator i

structure RootedIndicatorMarkovModel.IsRootedAtRadius
    {G ι : Type u} [Group G]
    (X : RootedIndicatorMarkovModel G ι)
    (w : G → List ι) (r : ℕ) : Prop where
  out : ∀ a g : G,
    (w a).length + (w g).length + (w (a * g)).length ≤ r →
      ∀ x : X.carrier, indicatorVector X.indicator x ≠ 0 →
        X.evaluation (a * g) x =
          (X.evaluation a * X.evaluation g) x

theorem eventually_rooted_of_growing_word_radius
    {G ι : Type u} [Group G]
    (X : ℕ → RootedIndicatorMarkovModel G ι)
    (w : G → List ι)
    (hroot : ∀ n, (X n).IsRootedAtRadius w n)
    (a g : G) :
    ∀ᶠ n in Filter.atTop,
      ∀ x : (X n).carrier,
        indicatorVector (X n).indicator x ≠ 0 →
          (X n).evaluation (a * g) x =
            ((X n).evaluation a * (X n).evaluation g) x := by
  filter_upwards [Filter.eventually_ge_atTop
    ((w a).length + (w g).length + (w (a * g)).length)]
      with n hn
  exact (hroot n).out a g hn

theorem exists_rooted_word_radius_normalized_markov_contraction
    {G : Type u} [Group G]
    (P : KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      permutationMarkov X.generator (indicatorVector X.indicator) ≠
        indicatorVector X.indicator →
      ‖((permutationMarkov X.generator)^[k])
          (normalizedIndicatorDefect X.generator X.indicator)‖ <
        kazhdanMarkovContractionFactor P S ^ k + ε := by
  classical
  let : Nonempty (↥S) := ⟨⟨1, honeS⟩⟩
  by_contra h
  push Not at h
  choose X hgenerated hradius hdefect hbad using h
  let V : ℕ → Type u := fun n => (X n).carrier
  let p : ∀ n, ↥S → Equiv.Perm (V n) :=
    fun n => (X n).generator
  let f : ∀ n, V n → ℝ := fun n => (X n).indicator
  let σ : ∀ n, G → Equiv.Perm (V n) :=
    fun n => (X n).evaluation
  have hf : ∀ n x, f n x = 0 ∨ f n x = 1 :=
    fun n => (hgenerated n).indicator_mem
  have hw : ∀ n g, σ n g = ((w g).map (p n)).prod :=
    fun n => (hgenerated n).word_evaluation
  have hone : ∀ n, σ n 1 = 1 :=
    fun n => (hgenerated n).identity_evaluation
  have hgenerator : ∀ n (i : ↥S), σ n (i : G) = p n i :=
    fun n => (hgenerated n).generator_evaluation
  have hroots : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x := by
    intro a g
    exact eventually_rooted_of_growing_word_radius
      X w hradius a g
  have hstrict :=
    eventually_normalizedIndicatorDefect_markov_pow_lt_of_rooted
      P S honeS hcover hsymmetric p f σ w hf hdefect
        hw hone hgenerator hroots k ε hε
  have hbad' : ∀ n,
      kazhdanMarkovContractionFactor P S ^ k + ε ≤
        ‖((permutationMarkov (p n))^[k])
          (normalizedIndicatorDefect (p n) (f n))‖ :=
    hbad
  obtain ⟨n, hlt, hge⟩ :=
    (hstrict.and (Filter.Eventually.of_forall hbad')).exists
  exact (not_lt_of_ge hge) hlt

theorem permutationMarkov_iterate_difference
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (x : EuclideanSpace ℂ V)
    (k : ℕ) :
    ((permutationMarkov p)^[k + 1]) x -
        ((permutationMarkov p)^[k]) x =
      ((permutationMarkovLinear p) ^ k)
        (permutationMarkov p x - x) := by
  rw [Function.iterate_succ_apply]
  rw [← permutationMarkovLinear_pow_apply p k
    (permutationMarkov p x),
    ← permutationMarkovLinear_pow_apply p k x,
    ← map_sub]

theorem norm_normalizedIndicatorDefect_markov_pow
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (k : ℕ) :
    ‖((permutationMarkov p)^[k])
        (normalizedIndicatorDefect p f)‖ =
      ‖((permutationMarkovLinear p) ^ k)
          (permutationMarkov p (indicatorVector f) -
            indicatorVector f)‖ /
        ‖permutationMarkov p (indicatorVector f) -
          indicatorVector f‖ := by
  rw [← permutationMarkovLinear_pow_apply]
  simp only [normalizedIndicatorDefect, map_smul, map_sub, norm_smul, norm_inv, Complex.norm_real,
    norm_norm,
    div_eq_mul_inv, mul_comm]

theorem exists_rooted_word_radius_markov_iterate_contraction
    {G : Type u} [Group G]
    (P : KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      ‖((permutationMarkov X.generator)^[k + 1])
            (indicatorVector X.indicator) -
          ((permutationMarkov X.generator)^[k])
            (indicatorVector X.indicator)‖ ≤
        (kazhdanMarkovContractionFactor P S ^ k + ε) *
          ‖permutationMarkov X.generator
              (indicatorVector X.indicator) -
            indicatorVector X.indicator‖ := by
  obtain ⟨r, hr⟩ :=
    exists_rooted_word_radius_normalized_markov_contraction
      P S honeS hcover hsymmetric w k ε hε
  refine ⟨r, ?_⟩
  intro X hgenerated hroot
  by_cases hfixed :
      permutationMarkov X.generator
        (indicatorVector X.indicator) =
          indicatorVector X.indicator
  · rw [Function.iterate_fixed hfixed (k + 1),
      Function.iterate_fixed hfixed k, hfixed]
    simp only [sub_self, norm_zero, mul_zero, Std.le_refl]
  · have hpositive :
        0 < ‖permutationMarkov X.generator
          (indicatorVector X.indicator) -
            indicatorVector X.indicator‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hfixed)
    have hnormalized := hr X hgenerated hroot hfixed
    rw [norm_normalizedIndicatorDefect_markov_pow]
      at hnormalized
    have hdenormalized :=
      (div_lt_iff₀ hpositive).mp hnormalized
    rw [permutationMarkov_iterate_difference]
    exact hdenormalized.le

end KunRootedWordPower

namespace KunActualSoficRootRadius

open Filter Topology
open scoped BigOperators Pointwise

def modelMultiplicationBad {G : Type*} [Group G]
    (M : PermutationModel G) (g h : G) :
    Finset (Fin M.size) :=
  Finset.univ.filter (fun x =>
    M.action (g * h) x ≠ (M.action g * M.action h) x)

@[simp]
theorem mem_modelMultiplicationBad {G : Type*} [Group G]
    (M : PermutationModel G) (g h : G)
    (x : Fin M.size) :
    x ∈ modelMultiplicationBad M g h ↔
      M.action (g * h) x ≠ (M.action g * M.action h) x := by
  simp only [modelMultiplicationBad, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem modelMultiplicationBad_density_tendsto_zero
    {G : Type*} [Group G]
    (A : SoficApproximation G) (g h : G) :
    Tendsto
      (fun n =>
        ((modelMultiplicationBad (A.model n) g h).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  simpa only [modelMultiplicationBad, Equiv.Perm.coe_mul, Function.comp_apply, ne_eq,
    normalizedHamming,
    hammingDist, Fintype.card_fin] using A.multiplicative g h

def modelSeparationBad {G : Type*} [Group G]
    (M : PermutationModel G) (g h : G) :
    Finset (Fin M.size) :=
  agreementSet (M.action g) (M.action h)

@[simp]
theorem mem_modelSeparationBad {G : Type*} [Group G]
    (M : PermutationModel G) (g h : G)
    (x : Fin M.size) :
    x ∈ modelSeparationBad M g h ↔ M.action g x = M.action h x := by
  simp only [modelSeparationBad, agreementSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem modelSeparationBad_density_tendsto_zero
    {G : Type*} [Group G]
    (A : SoficApproximation G)
    {g h : G} (hne : g ≠ h) :
    Tendsto
      (fun n =>
        ((modelSeparationBad (A.model n) g h).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  have hdist :=
    CompressionCriterion.normalizedHamming_distinct_tendsto
      A hne
  have hlimit :
      Tendsto
        (fun n =>
          (1 : ℝ) - normalizedHamming
            ((A.model n).action g) ((A.model n).action h))
        atTop (𝓝 0) := by
    have hone :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa only [sub_self] using hone.sub hdist
  convert hlimit using 1
  funext n
  have hcard :
      (agreementSet
        ((A.model n).action g) ((A.model n).action h)).card +
        hammingDist
          (fun x => (A.model n).action g x)
          (fun x => (A.model n).action h x) =
        (A.model n).size := by
    simpa only [Fintype.card_fin] using
      agreementSet_card_add_hammingDist ((A.model n).action g) ((A.model n).action h)
  have hreal :
      ((agreementSet
          ((A.model n).action g) ((A.model n).action h)).card : ℝ) +
        (hammingDist
          (fun x => (A.model n).action g x)
          (fun x => (A.model n).action h x) : ℝ) =
          (A.model n).size := by
    exact_mod_cast hcard
  have hden : ((A.model n).size : ℝ) ≠ 0 := by
    exact_mod_cast (A.model n).size_pos.ne'
  simp only [modelSeparationBad, normalizedHamming,
    Fintype.card_fin]
  field_simp
  linarith

def finiteMultiplicationBad {G : Type*} [Group G]
    (M : PermutationModel G) (F : Finset G) :
    Finset (Fin M.size) := by
  classical
  exact (F.product F).biUnion fun q =>
    modelMultiplicationBad M q.1 q.2

def finiteSeparationBad {G : Type*} [Group G]
    (M : PermutationModel G) (F : Finset G) :
    Finset (Fin M.size) := by
  classical
  exact ((F.product F).filter fun q => q.1 ≠ q.2).biUnion fun q =>
    modelSeparationBad M q.1 q.2

def finiteRootBad {G : Type*} [Group G]
    (M : PermutationModel G) (F : Finset G) :
    Finset (Fin M.size) :=
  finiteMultiplicationBad M F ∪ finiteSeparationBad M F

theorem finiteMultiplicationBad_density_tendsto_zero
    {G : Type*} [Group G]
    (A : SoficApproximation G) (F : Finset G) :
    Tendsto
      (fun n =>
        ((finiteMultiplicationBad (A.model n) F).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  classical
  have h := finite_union_bad_density_tendsto_zero
    (F.product F)
    (fun n => (Finset.univ : Finset (Fin (A.model n).size)))
    (fun n (q : G × G) =>
      modelMultiplicationBad (A.model n) q.1 q.2)
    (fun q _ => by
      simpa only [Finset.univ_inter, Finset.card_univ,
        Fintype.card_fin] using
        modelMultiplicationBad_density_tendsto_zero A q.1 q.2)
  simpa only [finiteMultiplicationBad, Finset.univ_inter,
    Finset.card_univ, Fintype.card_fin] using h

theorem finiteSeparationBad_density_tendsto_zero
    {G : Type*} [Group G]
    (A : SoficApproximation G) (F : Finset G) :
    Tendsto
      (fun n =>
        ((finiteSeparationBad (A.model n) F).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  classical
  have h := finite_union_bad_density_tendsto_zero
    ((F.product F).filter fun q : G × G => q.1 ≠ q.2)
    (fun n => (Finset.univ : Finset (Fin (A.model n).size)))
    (fun n (q : G × G) =>
      modelSeparationBad (A.model n) q.1 q.2)
    (fun q hq => by
      simpa only [Finset.univ_inter, Finset.card_univ,
        Fintype.card_fin] using
        modelSeparationBad_density_tendsto_zero
          A (Finset.mem_filter.mp hq).2)
  simpa only [finiteSeparationBad, Finset.univ_inter,
    Finset.card_univ, Fintype.card_fin] using h

theorem finiteRootBad_density_tendsto_zero
    {G : Type*} [Group G]
    (A : SoficApproximation G) (F : Finset G) :
    Tendsto
      (fun n =>
        ((finiteRootBad (A.model n) F).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  have hsum :
      Tendsto
        (fun n =>
          ((finiteMultiplicationBad (A.model n) F).card : ℝ) /
              (A.model n).size +
            ((finiteSeparationBad (A.model n) F).card : ℝ) /
              (A.model n).size)
        atTop (𝓝 0) := by
    simpa only [add_zero] using
      (finiteMultiplicationBad_density_tendsto_zero A F).add
        (finiteSeparationBad_density_tendsto_zero A F)
  refine squeeze_zero (fun n => by positivity) ?_ hsum
  intro n
  have hcard :
      ((finiteRootBad (A.model n) F).card : ℝ) ≤
        (finiteMultiplicationBad (A.model n) F).card +
          (finiteSeparationBad (A.model n) F).card := by
    exact_mod_cast Finset.card_union_le
      (finiteMultiplicationBad (A.model n) F)
      (finiteSeparationBad (A.model n) F)
  calc
    ((finiteRootBad (A.model n) F).card : ℝ) /
        (A.model n).size ≤
      (((finiteMultiplicationBad (A.model n) F).card : ℝ) +
        (finiteSeparationBad (A.model n) F).card) /
          (A.model n).size :=
        div_le_div_of_nonneg_right hcard (by positivity)
    _ = ((finiteMultiplicationBad (A.model n) F).card : ℝ) /
          (A.model n).size +
        ((finiteSeparationBad (A.model n) F).card : ℝ) /
          (A.model n).size := by
        rw [add_div]

theorem finiteRootBad_multiplicative
    {G : Type*} [Group G]
    (M : PermutationModel G) (F : Finset G)
    {g h : G} (hg : g ∈ F) (hh : h ∈ F)
    {x : Fin M.size} (hx : x ∉ finiteRootBad M F) :
    M.action (g * h) x = (M.action g * M.action h) x := by
  classical
  have hnot : x ∉ modelMultiplicationBad M g h := by
    intro hbad
    apply hx
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr
      ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, hbad⟩
  simpa only [Equiv.Perm.coe_mul, Function.comp_apply, mem_modelMultiplicationBad, ne_eq,
    Decidable.not_not] using hnot

theorem finiteRootBad_separated
    {G : Type*} [Group G]
    (M : PermutationModel G) (F : Finset G)
    {g h : G} (hg : g ∈ F) (hh : h ∈ F) (hne : g ≠ h)
    {x : Fin M.size} (hx : x ∉ finiteRootBad M F) :
    M.action g x ≠ M.action h x := by
  classical
  intro heq
  apply hx
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr
    ⟨(g, h), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hg, hh⟩, hne⟩,
      (mem_modelSeparationBad M g h x).mpr heq⟩

theorem finiteRootBad_injective_word_evaluation
    {G : Type*} [Group G]
    (M : PermutationModel G) (F : Finset G)
    {x : Fin M.size} (hx : x ∉ finiteRootBad M F) :
    Set.InjOn (fun g : G => M.action g x) (↑F : Set G) := by
  intro g hg h hh heq
  by_contra hne
  exact finiteRootBad_separated M F hg hh hne hx heq

theorem normalizedHamming_mul_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (p p' q q' : Equiv.Perm V) :
    normalizedHamming (p * q) (p' * q') ≤
      normalizedHamming p p' +
        normalizedHamming q q' := by
  calc
    normalizedHamming (p * q) (p' * q') ≤
        normalizedHamming (p * q) (p' * q) +
          normalizedHamming (p' * q) (p' * q') :=
      normalizedHamming_triangle _ _ _
    _ = normalizedHamming p p' +
          normalizedHamming q q' := by
      rw [normalizedHamming_mul_right,
        normalizedHamming_mul_left]

theorem action_list_prod_tendsto
    {G : Type*} [Group G]
    (A : SoficApproximation G) (l : List G) :
    Tendsto
      (fun n =>
        normalizedHamming
          ((A.model n).action l.prod)
          ((l.map (A.model n).action).prod))
      atTop (𝓝 0) := by
  induction l with
  | nil =>
      simp only [List.prod_nil, PermutationModel.map_one, List.map_nil, normalizedHamming_self,
        tendsto_const_nhds_iff]
  | cons g l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hmul := A.multiplicative g l.prod
      have hupper :
          Tendsto
            (fun n =>
              normalizedHamming
                  ((A.model n).action (g * l.prod))
                  ((A.model n).action g * (A.model n).action l.prod) +
                normalizedHamming
                  ((A.model n).action l.prod)
                  ((l.map (A.model n).action).prod))
            atTop (𝓝 0) := by
        simpa only [add_zero] using hmul.add ih
      refine squeeze_zero
        (fun n => normalizedHamming_nonneg _ _) ?_ hupper
      intro n
      have htriangle := normalizedHamming_triangle
        ((A.model n).action (g * l.prod))
        ((A.model n).action g * (A.model n).action l.prod)
        ((A.model n).action g *
          (l.map (A.model n).action).prod)
      rw [normalizedHamming_mul_left] at htriangle
      exact htriangle

def chosenWordEvaluation
    {G ι : Type*} [Group G]
    (A : SoficApproximation G)
    (s : ι → G) (w : G → List ι) (n : ℕ) (g : G) :
    Equiv.Perm (Fin (A.model n).size) :=
  ((w g).map fun i => (A.model n).action (s i)).prod

theorem chosenWordEvaluation_tendsto_action
    {G ι : Type*} [Group G]
    (A : SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g, ((w g).map s).prod = g) (g : G) :
    Tendsto
      (fun n =>
        normalizedHamming
          ((A.model n).action g)
          (chosenWordEvaluation A s w n g))
      atTop (𝓝 0) := by
  have h := action_list_prod_tendsto A ((w g).map s)
  simpa only [chosenWordEvaluation, hw g, List.map_map, Function.comp_def] using h

theorem chosenWordEvaluation_multiplicative_tendsto
    {G ι : Type*} [Group G]
    (A : SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g, ((w g).map s).prod = g) (g h : G) :
    Tendsto
      (fun n =>
        normalizedHamming
          (chosenWordEvaluation A s w n (g * h))
          (chosenWordEvaluation A s w n g *
            chosenWordEvaluation A s w n h))
      atTop (𝓝 0) := by
  have hgh := chosenWordEvaluation_tendsto_action A s w hw (g * h)
  have hgh' :
      Tendsto
        (fun n =>
          normalizedHamming
            (chosenWordEvaluation A s w n (g * h))
            ((A.model n).action (g * h)))
        atTop (𝓝 0) := by
    convert hgh using 1
    funext n
    exact normalizedHamming_comm _ _
  have hg := chosenWordEvaluation_tendsto_action A s w hw g
  have hh := chosenWordEvaluation_tendsto_action A s w hw h
  have hmul := A.multiplicative g h
  have hupper :
      Tendsto
        (fun n =>
          normalizedHamming
              (chosenWordEvaluation A s w n (g * h))
              ((A.model n).action (g * h)) +
            normalizedHamming
              ((A.model n).action (g * h))
              ((A.model n).action g * (A.model n).action h) +
            (normalizedHamming
                ((A.model n).action g)
                (chosenWordEvaluation A s w n g) +
              normalizedHamming
                ((A.model n).action h)
                (chosenWordEvaluation A s w n h)))
        atTop (𝓝 0) := by
    simpa only [add_zero] using (hgh'.add hmul).add (hg.add hh)
  refine squeeze_zero
    (fun n => normalizedHamming_nonneg _ _) ?_ hupper
  intro n
  have hfirst := normalizedHamming_triangle
    (chosenWordEvaluation A s w n (g * h))
    ((A.model n).action (g * h))
    (chosenWordEvaluation A s w n g *
      chosenWordEvaluation A s w n h)
  have hsecond := normalizedHamming_triangle
    ((A.model n).action (g * h))
    ((A.model n).action g * (A.model n).action h)
    (chosenWordEvaluation A s w n g *
      chosenWordEvaluation A s w n h)
  have hproduct := normalizedHamming_mul_le
    ((A.model n).action g) (chosenWordEvaluation A s w n g)
    ((A.model n).action h) (chosenWordEvaluation A s w n h)
  linarith

def chosenWordMultiplicationBad
    {G ι : Type*} [Group G]
    (A : SoficApproximation G)
    (s : ι → G) (w : G → List ι) (n : ℕ) (g h : G) :
    Finset (Fin (A.model n).size) :=
  Finset.univ.filter (fun x =>
    chosenWordEvaluation A s w n (g * h) x ≠
      (chosenWordEvaluation A s w n g *
        chosenWordEvaluation A s w n h) x)

@[simp]
theorem mem_chosenWordMultiplicationBad
    {G ι : Type*} [Group G]
    (A : SoficApproximation G)
    (s : ι → G) (w : G → List ι) (n : ℕ) (g h : G)
    (x : Fin (A.model n).size) :
    x ∈ chosenWordMultiplicationBad A s w n g h ↔
      chosenWordEvaluation A s w n (g * h) x ≠
        (chosenWordEvaluation A s w n g *
          chosenWordEvaluation A s w n h) x := by
  simp only [chosenWordMultiplicationBad, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem chosenWordMultiplicationBad_density_tendsto_zero
    {G ι : Type*} [Group G]
    (A : SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g, ((w g).map s).prod = g) (g h : G) :
    Tendsto
      (fun n =>
        ((chosenWordMultiplicationBad A s w n g h).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  simpa only [chosenWordMultiplicationBad, Equiv.Perm.coe_mul, Function.comp_apply, ne_eq,
    normalizedHamming,
    hammingDist, Fintype.card_fin] using chosenWordEvaluation_multiplicative_tendsto A s w hw g h

def chosenFiniteMultiplicationBad
    {G ι : Type*} [Group G]
    (A : SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (F : Finset G) (n : ℕ) : Finset (Fin (A.model n).size) := by
  classical
  exact (F.product F).biUnion fun q =>
    chosenWordMultiplicationBad A s w n q.1 q.2

theorem chosenFiniteMultiplicationBad_density_tendsto_zero
    {G ι : Type*} [Group G]
    (A : SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g, ((w g).map s).prod = g) (F : Finset G) :
    Tendsto
      (fun n =>
        ((chosenFiniteMultiplicationBad A s w F n).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  classical
  have h := finite_union_bad_density_tendsto_zero
    (F.product F)
    (fun n => (Finset.univ : Finset (Fin (A.model n).size)))
    (fun n (q : G × G) =>
      chosenWordMultiplicationBad A s w n q.1 q.2)
    (fun q _ => by
      simpa only [Finset.univ_inter, Finset.card_univ,
        Fintype.card_fin] using
        chosenWordMultiplicationBad_density_tendsto_zero
          A s w hw q.1 q.2)
  simpa only [chosenFiniteMultiplicationBad, Finset.univ_inter,
    Finset.card_univ, Fintype.card_fin] using h

theorem chosenFiniteMultiplicationBad_rooted
    {G ι : Type*} [Group G]
    (A : SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (F : Finset G) (n : ℕ)
    {g h : G} (hg : g ∈ F) (hh : h ∈ F)
    {x : Fin (A.model n).size}
    (hx : x ∉ chosenFiniteMultiplicationBad A s w F n) :
    chosenWordEvaluation A s w n (g * h) x =
      (chosenWordEvaluation A s w n g *
        chosenWordEvaluation A s w n h) x := by
  classical
  have hnot : x ∉ chosenWordMultiplicationBad A s w n g h := by
    intro hbad
    apply hx
    exact Finset.mem_biUnion.mpr
      ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, hbad⟩
  simpa only [Equiv.Perm.coe_mul, Function.comp_apply, mem_chosenWordMultiplicationBad, ne_eq,
    Decidable.not_not] using hnot

def chosenFiniteRootBad
    {G ι : Type*} [Group G]
    (A : SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (F : Finset G) (n : ℕ) : Finset (Fin (A.model n).size) :=
  finiteRootBad (A.model n) F ∪
    chosenFiniteMultiplicationBad A s w F n

theorem chosenFiniteRootBad_density_tendsto_zero
    {G ι : Type*} [Group G]
    (A : SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g, ((w g).map s).prod = g) (F : Finset G) :
    Tendsto
      (fun n =>
        ((chosenFiniteRootBad A s w F n).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  have hsum :
      Tendsto
        (fun n =>
          ((finiteRootBad (A.model n) F).card : ℝ) /
              (A.model n).size +
            ((chosenFiniteMultiplicationBad A s w F n).card : ℝ) /
              (A.model n).size)
        atTop (𝓝 0) := by
    simpa only [add_zero] using
      (finiteRootBad_density_tendsto_zero A F).add
        (chosenFiniteMultiplicationBad_density_tendsto_zero A s w hw F)
  refine squeeze_zero (fun n => by positivity) ?_ hsum
  intro n
  have hcard :
      ((chosenFiniteRootBad A s w F n).card : ℝ) ≤
        (finiteRootBad (A.model n) F).card +
          (chosenFiniteMultiplicationBad A s w F n).card := by
    exact_mod_cast Finset.card_union_le
      (finiteRootBad (A.model n) F)
      (chosenFiniteMultiplicationBad A s w F n)
  calc
    ((chosenFiniteRootBad A s w F n).card : ℝ) /
        (A.model n).size ≤
      (((finiteRootBad (A.model n) F).card : ℝ) +
        (chosenFiniteMultiplicationBad A s w F n).card) /
          (A.model n).size :=
        div_le_div_of_nonneg_right hcard (by positivity)
    _ = ((finiteRootBad (A.model n) F).card : ℝ) /
          (A.model n).size +
        ((chosenFiniteMultiplicationBad A s w F n).card : ℝ) /
          (A.model n).size := by
        rw [add_div]

theorem chosenFiniteRootBad_injective_word_evaluation
    {G ι : Type*} [Group G]
    (A : SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (F : Finset G) (n : ℕ)
    {x : Fin (A.model n).size}
    (hx : x ∉ chosenFiniteRootBad A s w F n) :
    Set.InjOn (fun g : G => (A.model n).action g x)
      (↑F : Set G) := by
  apply finiteRootBad_injective_word_evaluation
    (A.model n) F
  intro hbad
  exact hx (Finset.mem_union_left _ hbad)

theorem exists_generator_word_of_symmetric_generates
    {G : Type*} [Group G]
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (g : G) :
    ∃ l : List ↥S,
      ((l.map fun i : ↥S => (i : G)).prod) = g := by
  classical
  have hg : g ∈ Subgroup.closure (S : Set G) := by
    rw [hgenerates]
    simp only [Subgroup.mem_top]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      exact ⟨[⟨x, hx⟩], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]⟩
  | one =>
      exact ⟨[], by simp only [List.map_nil, List.prod_nil]⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨lx, hlx⟩ := ihx
      obtain ⟨ly, hly⟩ := ihy
      refine ⟨lx ++ ly, ?_⟩
      rw [List.map_append, List.prod_append, hlx, hly]
  | inv x _ ih =>
      obtain ⟨l, hl⟩ := ih
      let invLetter : ↥S → ↥S :=
        fun i => ⟨(i : G)⁻¹, hsymmetric (i : G) i.property⟩
      refine ⟨(l.map invLetter).reverse, ?_⟩
      rw [List.map_reverse, List.map_map]
      change ((l.map fun i : ↥S => (i : G)⁻¹).reverse).prod = x⁻¹
      have hmap :
          (l.map fun i : ↥S => (i : G)⁻¹) =
            (l.map (fun i : ↥S => (i : G))).map
              (fun x : G => x⁻¹) := by
        rw [List.map_map]
        rfl
      rw [hmap, ← List.prod_inv_reverse, hl]

def symmetricGeneratorWord
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (g : G) : List ↥S := by
  classical
  by_cases hone : g = 1
  · exact []
  · by_cases hg : g ∈ S
    · exact [⟨g, hg⟩]
    · exact (exists_generator_word_of_symmetric_generates
        S hsymmetric hgenerates g).choose

theorem symmetricGeneratorWord_prod
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (g : G) :
    (((symmetricGeneratorWord S hsymmetric hgenerates g).map
      fun i : ↥S => (i : G)).prod) = g := by
  classical
  unfold symmetricGeneratorWord
  split <;> rename_i hone
  · simp only [List.map_nil, List.prod_nil, hone]
  · split <;> rename_i hg
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    · exact (exists_generator_word_of_symmetric_generates
        S hsymmetric hgenerates g).choose_spec

@[simp]
theorem symmetricGeneratorWord_one
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) :
    symmetricGeneratorWord S hsymmetric hgenerates (1 : G) = [] := by
  simp only [symmetricGeneratorWord, ↓reduceDIte]

theorem symmetricGeneratorWord_generator
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (i : ↥S) (hi : (i : G) ≠ 1) :
    symmetricGeneratorWord S hsymmetric hgenerates (i : G) = [i] := by
  classical
  simp only [symmetricGeneratorWord, hi, ↓reduceDIte, i.property, Subtype.coe_eta]

theorem chosen_symmetric_wordEvaluation_one
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficApproximation G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (n : ℕ) :
    chosenWordEvaluation A (fun i : ↥S => (i : G))
      (symmetricGeneratorWord S hsymmetric hgenerates) n 1 = 1 := by
  simp only [chosenWordEvaluation, symmetricGeneratorWord_one, List.map_nil, List.prod_nil]

theorem chosen_symmetric_wordEvaluation_generator
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficApproximation G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (n : ℕ) (i : ↥S) :
    chosenWordEvaluation A (fun j : ↥S => (j : G))
      (symmetricGeneratorWord S hsymmetric hgenerates)
      n (i : G) =
        (A.model n).action (i : G) := by
  classical
  by_cases hi : (i : G) = 1
  · simp only [chosenWordEvaluation, hi, symmetricGeneratorWord_one, List.map_nil, List.prod_nil,
      PermutationModel.map_one]
  · rw [chosenWordEvaluation,
      symmetricGeneratorWord_generator S hsymmetric hgenerates i hi]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem generator_word_prod_mem_pow
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G) (l : List ↥S) :
    ((l.map fun i : ↥S => (i : G)).prod) ∈ S ^ l.length := by
  induction l with
  | nil => simp only [List.length_nil, pow_zero, List.map_nil, List.prod_nil, Finset.mem_one]
  | cons a l ih =>
      simpa only [List.length_cons, pow_succ', List.map_cons, List.map_subtype, List.map_id_fun',
        id_eq,
        List.prod_cons] using (Finset.mul_mem_mul a.property ih)

theorem mem_generator_pow_of_chosen_word_length
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G) (hone : 1 ∈ S)
    (w : G → List ↥S)
    (hw : ∀ g, ((w g).map fun i : ↥S => (i : G)).prod = g)
    {g : G} {r : ℕ} (hgr : (w g).length ≤ r) :
    g ∈ S ^ r := by
  have hword : g ∈ S ^ (w g).length := by
    simpa only [hw g] using generator_word_prod_mem_pow S (w g)
  exact Finset.pow_subset_pow_right hone hgr hword

def chosenCayleyRadiusBad
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficApproximation G)
    (S : Finset G) (w : G → List ↥S) (n r : ℕ) :
    Finset (Fin (A.model n).size) :=
  chosenFiniteRootBad A (fun i : ↥S => (i : G)) w (S ^ r) n

theorem chosenCayleyRadiusBad_density_tendsto_zero
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficApproximation G)
    (S : Finset G) (w : G → List ↥S)
    (hw : ∀ g, ((w g).map fun i : ↥S => (i : G)).prod = g)
    (r : ℕ) :
    Tendsto
      (fun n =>
        ((chosenCayleyRadiusBad A S w n r).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) :=
  chosenFiniteRootBad_density_tendsto_zero
    A (fun i : ↥S => (i : G)) w hw (S ^ r)

theorem chosenCayleyRadiusBad_rooted
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficApproximation G)
    (S : Finset G) (hone : 1 ∈ S)
    (w : G → List ↥S)
    (hw : ∀ g, ((w g).map fun i : ↥S => (i : G)).prod = g)
    (n r : ℕ) (a g : G)
    (hword : (w a).length + (w g).length +
      (w (a * g)).length ≤ r)
    {x : Fin (A.model n).size}
    (hx : x ∉ chosenCayleyRadiusBad A S w n r) :
    chosenWordEvaluation A (fun i : ↥S => (i : G)) w n (a * g) x =
      (chosenWordEvaluation A (fun i : ↥S => (i : G)) w n a *
        chosenWordEvaluation A (fun i : ↥S => (i : G)) w n g) x := by
  have ha : (w a).length ≤ r := by omega
  have hg : (w g).length ≤ r := by omega
  have ha' : a ∈ S ^ r :=
    mem_generator_pow_of_chosen_word_length S hone w hw ha
  have hg' : g ∈ S ^ r :=
    mem_generator_pow_of_chosen_word_length S hone w hw hg
  apply chosenFiniteMultiplicationBad_rooted
    A (fun i : ↥S => (i : G)) w (S ^ r) n ha' hg'
  intro hbad
  exact hx (Finset.mem_union_right _ hbad)

theorem chosenCayleyRadiusBad_injective_ball
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficApproximation G)
    (S : Finset G) (w : G → List ↥S) (n r : ℕ)
    {x : Fin (A.model n).size}
    (hx : x ∉ chosenCayleyRadiusBad A S w n r) :
    Set.InjOn (fun g : G => (A.model n).action g x)
      (↑(S ^ r) : Set G) := by
  exact chosenFiniteRootBad_injective_word_evaluation
    A (fun i : ↥S => (i : G)) w (S ^ r) n hx

end KunActualSoficRootRadius

namespace KunDirectedIndicatorJensen

open scoped BigOperators

def realIndicator {V : Type*} [DecidableEq V]
    (T : Finset V) (x : V) : ℝ :=
  if x ∈ T then 1 else 0

def realPermutationMarkov {V ι : Type*} [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (x : V) : ℝ :=
  (∑ i : ι, f ((σ i).symm x)) / Fintype.card ι

theorem sq_realIndicator_displacement
    {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (T : Finset V) (x : V) :
    (realIndicator T (p x) - realIndicator T x) ^ 2 =
      (if x ∈ T ∧ p x ∉ T then (1 : ℝ) else 0) +
      (if x ∉ T ∧ p x ∈ T then (1 : ℝ) else 0) := by
  classical
  by_cases hx : x ∈ T <;> by_cases hp : p x ∈ T <;>
    simp [realIndicator, hx, hp]

theorem sum_sq_realIndicator_displacement
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (T : Finset V) :
    (∑ x : V,
      (realIndicator T (p x) - realIndicator T x) ^ 2) =
      2 * ((T.filter fun x => p x ∉ T).card : ℝ) := by
  classical
  simp_rw [sq_realIndicator_displacement]
  rw [Finset.sum_add_distrib]
  have hleave :
      (∑ x : V,
        if x ∈ T ∧ p x ∉ T then (1 : ℝ) else 0) =
        ((T.filter fun x => p x ∉ T).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have henter :
      (∑ x : V,
        if x ∉ T ∧ p x ∈ T then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun x => x ∉ T ∧ p x ∈ T).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hleave, henter,
    KunThomFiberCoarea.card_entering_eq_card_exiting]
  ring

theorem sum_sq_realIndicator_inverse_displacement
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (T : Finset V) :
    (∑ x : V,
      (realIndicator T (p.symm x) - realIndicator T x) ^ 2) =
      2 * ((T.filter fun x => p x ∉ T).card : ℝ) := by
  classical
  calc
    (∑ x : V,
      (realIndicator T (p.symm x) - realIndicator T x) ^ 2) =
        ∑ x : V,
          (realIndicator T (p.symm (p x)) -
            realIndicator T (p x)) ^ 2 := by
          exact (Equiv.sum_comp p
            (fun x : V =>
              (realIndicator T (p.symm x) - realIndicator T x) ^ 2)).symm
    _ = ∑ x : V,
          (realIndicator T (p x) - realIndicator T x) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [p.symm_apply_apply]
          ring
    _ = 2 * ((T.filter fun x => p x ∉ T).card : ℝ) :=
      sum_sq_realIndicator_displacement p T

theorem sum_sum_sq_realIndicator_inverse_displacement
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (T : Finset V) :
    (∑ i : ι, ∑ x : V,
      (realIndicator T ((σ i).symm x) - realIndicator T x) ^ 2) =
      2 * (boundary σ T : ℝ) := by
  classical
  simp_rw [sum_sq_realIndicator_inverse_displacement]
  unfold boundary
  push_cast
  rw [Finset.mul_sum]

theorem realPermutationMarkov_sub_sq_le_average_sq
    {V ι : Type*} [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (x : V) :
    (realPermutationMarkov σ f x - f x) ^ 2 ≤
      (∑ i : ι,
        (f ((σ i).symm x) - f x) ^ 2) /
        (Fintype.card ι : ℝ) := by
  classical
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty ι)
  have hmean :
      realPermutationMarkov σ f x - f x =
        (∑ i : ι, (f ((σ i).symm x) - f x)) /
          (Fintype.card ι : ℝ) := by
    unfold realPermutationMarkov
    rw [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hcauchy :
      (∑ i : ι, (f ((σ i).symm x) - f x)) ^ 2 ≤
        (Fintype.card ι : ℝ) *
          ∑ i : ι, (f ((σ i).symm x) - f x) ^ 2 := by
    simpa only [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ)
        (f := fun i : ι => f ((σ i).symm x) - f x))
  rw [hmean, div_pow]
  calc
    (∑ i : ι, (f ((σ i).symm x) - f x)) ^ 2 /
        (Fintype.card ι : ℝ) ^ 2 ≤
      ((Fintype.card ι : ℝ) *
        ∑ i : ι, (f ((σ i).symm x) - f x) ^ 2) /
          (Fintype.card ι : ℝ) ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hd)).mpr hcauchy
    _ = (∑ i : ι,
        (f ((σ i).symm x) - f x) ^ 2) /
          (Fintype.card ι : ℝ) := by
        field_simp

theorem realPermutationMarkov_indicator_defect_sq_le_boundary
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) :
    (∑ x : V,
      (realPermutationMarkov σ (realIndicator T) x -
        realIndicator T x) ^ 2) ≤
      2 * (boundary σ T : ℝ) /
        (Fintype.card ι : ℝ) := by
  classical
  calc
    (∑ x : V,
      (realPermutationMarkov σ (realIndicator T) x -
        realIndicator T x) ^ 2) ≤
      ∑ x : V,
        (∑ i : ι,
          (realIndicator T ((σ i).symm x) -
            realIndicator T x) ^ 2) / (Fintype.card ι : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          exact realPermutationMarkov_sub_sq_le_average_sq
            σ (realIndicator T) x
    _ = (∑ i : ι, ∑ x : V,
          (realIndicator T ((σ i).symm x) -
            realIndicator T x) ^ 2) / (Fintype.card ι : ℝ) := by
          rw [← Finset.sum_div, Finset.sum_comm]
    _ = 2 * (boundary σ T : ℝ) /
          (Fintype.card ι : ℝ) := by
          rw [sum_sum_sq_realIndicator_inverse_displacement]

end KunDirectedIndicatorJensen

namespace KunFinitePermutationMarkovMass

open scoped BigOperators

def realIndicator {V : Type*} [DecidableEq V]
    (T : Finset V) (x : V) : ℝ :=
  if x ∈ T then 1 else 0

def realPermutationMarkov {V ι : Type*} [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (x : V) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, f ((σ i).symm x)

theorem realPermutationMarkov_nonneg {V ι : Type*}
    [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (x : V) :
    0 ≤ realPermutationMarkov σ f x := by
  unfold realPermutationMarkov
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => hf ((σ i).symm x))

theorem realPermutationMarkov_le_one {V ι : Type*}
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x ≤ 1) (x : V) :
    realPermutationMarkov σ f x ≤ 1 := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum :
      (∑ i : ι, f ((σ i).symm x)) ≤ ∑ _i : ι, (1 : ℝ) := by
    exact Finset.sum_le_sum fun i _ => hf ((σ i).symm x)
  calc
    realPermutationMarkov σ f x =
        (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, f ((σ i).symm x) := rfl
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left hsum
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ne_eq, hcard,
        not_false_eq_true,
        inv_mul_cancel₀]

theorem sum_realPermutationMarkov {V ι : Type*}
    [Fintype V] [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) :
    (∑ x : V, realPermutationMarkov σ f x) = ∑ x : V, f x := by
  classical
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    (∑ x : V, realPermutationMarkov σ f x) =
        (Fintype.card ι : ℝ)⁻¹ *
          ∑ i : ι, ∑ x : V, f ((σ i).symm x) := by
      simp only [realPermutationMarkov, ← Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = (Fintype.card ι : ℝ)⁻¹ *
          ∑ i : ι, ∑ x : V, f x := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp (σ i).symm f
    _ = ∑ x : V, f x := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ne_eq, hcard, not_false_eq_true,
        inv_mul_cancel_left₀]

theorem realPermutationMarkov_iterate_nonneg {V ι : Type*}
    [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (k : ℕ) :
    ∀ x, 0 ≤ ((realPermutationMarkov σ)^[k]) f x := by
  induction k with
  | zero => simpa only [Function.iterate_zero, id_eq] using hf
  | succ k ih =>
    intro x
    rw [Function.iterate_succ_apply']
    exact realPermutationMarkov_nonneg σ _ ih x

theorem realPermutationMarkov_iterate_le_one {V ι : Type*}
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x ≤ 1) (k : ℕ) :
    ∀ x, ((realPermutationMarkov σ)^[k]) f x ≤ 1 := by
  induction k with
  | zero => simpa only [Function.iterate_zero, id_eq] using hf
  | succ k ih =>
    intro x
    rw [Function.iterate_succ_apply']
    exact realPermutationMarkov_le_one σ _ ih x

theorem sum_realPermutationMarkov_iterate {V ι : Type*}
    [Fintype V] [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (k : ℕ) :
    (∑ x : V, ((realPermutationMarkov σ)^[k]) f x) =
      ∑ x : V, f x := by
  induction k with
  | zero => simp only [Function.iterate_zero, id_eq]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (sum_realPermutationMarkov σ
      (((realPermutationMarkov σ)^[k]) f)).trans ih

theorem sum_realIndicator {V : Type*}
    [Fintype V] [DecidableEq V] (T : Finset V) :
    (∑ x : V, realIndicator T x) = (T.card : ℝ) := by
  classical
  simp only [realIndicator, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    mul_one]

theorem sum_realPermutationMarkov_iterate_indicator {V ι : Type*}
    [Fintype V] [DecidableEq V] [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (k : ℕ) :
    (∑ x : V,
      ((realPermutationMarkov σ)^[k]) (realIndicator T) x) =
        (T.card : ℝ) := by
  rw [sum_realPermutationMarkov_iterate]
  exact sum_realIndicator T

theorem realPermutationMarkov_iterate_indicator_mem_unitInterval
    {V ι : Type*}
    [DecidableEq V] [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (k : ℕ) (x : V) :
    0 ≤ ((realPermutationMarkov σ)^[k]) (realIndicator T) x ∧
      ((realPermutationMarkov σ)^[k]) (realIndicator T) x ≤ 1 := by
  constructor
  · apply realPermutationMarkov_iterate_nonneg
    intro y
    by_cases hy : y ∈ T
    · simp only [realIndicator, hy, ↓reduceIte, zero_le_one]
    · simp only [realIndicator, hy, ↓reduceIte, Std.le_refl]
  · apply realPermutationMarkov_iterate_le_one
    intro y
    by_cases hy : y ∈ T
    · simp only [realIndicator, hy, ↓reduceIte, Std.le_refl]
    · simp only [realIndicator, hy, ↓reduceIte, zero_le_one]

end KunFinitePermutationMarkovMass

namespace KunResidualExpanderDecomposition

open Filter Topology
open scoped BigOperators symmDiff

theorem boundary_eq_sum_indicator {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (A : Finset V) :
    boundary σ A =
      ∑ i : ι, ∑ x : V,
        if x ∈ A ∧ σ i x ∉ A then 1 else 0 := by
  classical
  unfold boundary
  apply Finset.sum_congr rfl
  intro i _
  have hfilter :
      (A.filter fun x => σ i x ∉ A) =
        Finset.univ.filter fun x : V => x ∈ A ∧ σ i x ∉ A := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfilter, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem boundary_eq_sum_entering_indicator {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (A : Finset V) :
    boundary σ A =
      ∑ i : ι, ∑ x : V,
        if x ∉ A ∧ σ i x ∈ A then 1 else 0 := by
  classical
  unfold boundary
  apply Finset.sum_congr rfl
  intro i _
  rw [← KunThomFiberCoarea.card_entering_eq_card_exiting
    (σ i) A, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem boundary_complement {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (A : Finset V) :
    boundary σ (Finset.univ \ A) =
      boundary σ A := by
  rw [boundary_eq_sum_indicator σ (Finset.univ \ A),
    boundary_eq_sum_entering_indicator σ A]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Decidable.not_not]

theorem boundary_le_degree_mul_card {V ι : Type*}
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (A : Finset V) :
    boundary σ A ≤ Fintype.card ι * A.card := by
  unfold boundary
  calc
    (∑ i : ι, (A.filter fun x => σ i x ∉ A).card) ≤
        ∑ _i : ι, A.card := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.card_filter_le _ _
    _ = Fintype.card ι * A.card := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem boundary_inter_add_boundary_sdiff_le {V ι : Type*}
    [Finite V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (R U : Finset V) :
    boundary σ (R ∩ U) +
        boundary σ (R \ U) ≤
      boundary σ R + 2 * boundary σ U := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hpoint (i : ι) (x : V) :
      (if x ∈ R ∩ U ∧ σ i x ∉ R ∩ U then 1 else 0) +
          (if x ∈ R \ U ∧ σ i x ∉ R \ U then 1 else 0) ≤
        (if x ∈ R ∧ σ i x ∉ R then 1 else 0) +
          (if x ∈ U ∧ σ i x ∉ U then 1 else 0) +
          (if x ∉ U ∧ σ i x ∈ U then 1 else 0) := by
    by_cases hxR : x ∈ R <;>
      by_cases hxU : x ∈ U <;>
      by_cases hyR : σ i x ∈ R <;>
      by_cases hyU : σ i x ∈ U <;>
      simp [hxR, hxU, hyR, hyU]
  calc
    boundary σ (R ∩ U) +
        boundary σ (R \ U) =
      ∑ i : ι, ∑ x : V,
        ((if x ∈ R ∩ U ∧ σ i x ∉ R ∩ U then 1 else 0) +
         (if x ∈ R \ U ∧ σ i x ∉ R \ U then 1 else 0)) := by
          rw [boundary_eq_sum_indicator, boundary_eq_sum_indicator]
          simp_rw [Finset.sum_add_distrib]
    _ ≤ ∑ i : ι, ∑ x : V,
        ((if x ∈ R ∧ σ i x ∉ R then 1 else 0) +
         (if x ∈ U ∧ σ i x ∉ U then 1 else 0) +
         (if x ∉ U ∧ σ i x ∈ U then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro x _
          exact hpoint i x
    _ = boundary σ R +
        2 * boundary σ U := by
          rw [boundary_eq_sum_indicator σ R,
            boundary_eq_sum_indicator σ U]
          have henter := boundary_eq_sum_entering_indicator σ U
          rw [boundary_eq_sum_indicator σ U] at henter
          simp_rw [Finset.sum_add_distrib]
          omega

theorem exists_minimum_sparse_residual_cut {V ι : Type*}
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (R : Finset V) (γ : ℝ)
    (hsparse : ∃ T : Finset V, T ⊆ R ∧
      (boundary σ T : ℝ) < γ * (T.card : ℝ)) :
    ∃ T : Finset V, T ⊆ R ∧
      (boundary σ T : ℝ) < γ * (T.card : ℝ) ∧
      ∀ E : Finset V, E ⊆ R →
        (boundary σ E : ℝ) < γ * (E.card : ℝ) →
        T.card ≤ E.card := by
  classical
  let candidates : Finset (Finset V) :=
    R.powerset.filter fun T =>
      (boundary σ T : ℝ) < γ * (T.card : ℝ)
  have hcandidates : candidates.Nonempty := by
    obtain ⟨T, hTR, hT⟩ := hsparse
    refine ⟨T, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_powerset, hTR, hT, and_self, candidates]
  obtain ⟨T, hT, hminimum⟩ :=
    Finset.exists_min_image candidates Finset.card hcandidates
  have hT' := (Finset.mem_filter.mp hT)
  refine ⟨T, Finset.mem_powerset.mp hT'.1, hT'.2, ?_⟩
  intro E hER hE
  apply hminimum E
  simp only [Finset.mem_filter, Finset.mem_powerset, hER, hE, and_self, candidates]

theorem close_residual_inter_properties {V : Type*} [DecidableEq V]
    (R T U : Finset V) (hTR : T ⊆ R)
    (hclose : 3 * (U ∆ T).card < T.card) :
    (R ∩ U).Nonempty ∧
      U.card ≤ 2 * (R ∩ U).card ∧
      (R ∩ U).card < 2 * T.card := by
  classical
  have hmissing :
      (T \ U).card ≤ (U ∆ T).card :=
    Finset.card_le_card
      (Finset.symmDiff_subset_sdiff' (s := U) (t := T))
  have hexcess :
      (U \ T).card ≤ (U ∆ T).card :=
    Finset.card_le_card
      (Finset.symmDiff_subset_sdiff (s := U) (t := T))
  have hTinter :
      (T ∩ U).card ≤ (R ∩ U).card := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨hTR (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
  have hUinter :
      (U ∩ T).card ≤ (R ∩ U).card := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨hTR (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1⟩
  have hTsplit := Finset.card_sdiff_add_card_inter T U
  have hUsplit := Finset.card_sdiff_add_card_inter U T
  have hintercomm : (T ∩ U).card = (U ∩ T).card := by
    rw [Finset.inter_comm]
  have hPsub : (R ∩ U).card ≤ U.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hPpos : 0 < (R ∩ U).card := by omega
  exact ⟨Finset.card_pos.mp hPpos, by omega, by omega⟩

theorem minimum_sparse_cut_expands_close_residual_part
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (R T U : Finset V) (γ : ℝ)
    (hTR : T ⊆ R)
    (hminimum : ∀ E : Finset V, E ⊆ R →
      (boundary σ E : ℝ) < γ * (E.card : ℝ) →
      T.card ≤ E.card)
    (hclose : 3 * (U ∆ T).card < T.card) :
    ∀ E : Finset V, E ⊆ R ∩ U →
      2 * E.card ≤ (R ∩ U).card →
      γ * (E.card : ℝ) ≤ (boundary σ E : ℝ) := by
  intro E hE hhalf
  by_contra h
  have hbad :
      (boundary σ E : ℝ) < γ * (E.card : ℝ) :=
    lt_of_not_ge h
  have hER : E ⊆ R := hE.trans Finset.inter_subset_left
  have hmin := hminimum E hER hbad
  have hsize := (close_residual_inter_properties R T U hTR hclose).2.2
  omega

theorem exists_expanding_residual_finpartition
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B : Finset V) (γ α : ℝ)
    (hα : 0 ≤ α)
    (himprove : ∀ T : Finset V, T ⊆ Finset.univ \ B →
      (boundary σ T : ℝ) < γ * (T.card : ℝ) →
      ∃ U : Finset V, 3 * (U ∆ T).card < T.card ∧
        (boundary σ U : ℝ) ≤ α * (U.card : ℝ))
    (R : Finset V) (hRB : R ⊆ Finset.univ \ B) :
    ∃ P : Finpartition R,
      (∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤ (boundary σ E : ℝ)) ∧
      (∑ C ∈ P.parts, (boundary σ C : ℝ)) ≤
        (boundary σ R : ℝ) +
          4 * α * (R.card : ℝ) := by
  classical
  have hmain : ∀ R : Finset V, R ⊆ Finset.univ \ B →
      ∃ P : Finpartition R,
        (∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
          2 * E.card ≤ C.card →
            γ * (E.card : ℝ) ≤
              (boundary σ E : ℝ)) ∧
        (∑ C ∈ P.parts, (boundary σ C : ℝ)) ≤
          (boundary σ R : ℝ) +
            4 * α * (R.card : ℝ) := by
    intro R
    refine Finset.strongInductionOn R ?_
    intro R ih hRgood
    by_cases hR : R.Nonempty
    · by_cases hsparse : ∃ T : Finset V, T ⊆ R ∧
          (boundary σ T : ℝ) < γ * (T.card : ℝ)
      · obtain ⟨T, hTR, hTsparse, hTminimum⟩ :=
          exists_minimum_sparse_residual_cut σ R γ hsparse
        obtain ⟨U, hclose, hUboundary⟩ :=
          himprove T (hTR.trans hRgood) hTsparse
        have hpiece :=
          close_residual_inter_properties R T U hTR hclose
        let C : Finset V := R ∩ U
        have hCnonempty : C.Nonempty := by
          simpa only [C] using hpiece.1
        have hCR : C ⊆ R := Finset.inter_subset_left
        have hstrict : R \ C ⊂ R :=
          Finset.sdiff_ssubset hCR hCnonempty
        have hresgood : R \ C ⊆ Finset.univ \ B :=
          Finset.Subset.trans Finset.sdiff_subset hRgood
        obtain ⟨Q, hQexpand, hQbudget⟩ :=
          ih (R \ C) hstrict hresgood
        have hdisjoint : Disjoint (R \ C) C :=
          Finset.sdiff_disjoint
        have hunion : (R \ C) ⊔ C = R := by
          change (R \ C) ∪ C = R
          exact Finset.sdiff_union_of_subset hCR
        let P : Finpartition R :=
          Q.extend hCnonempty.ne_empty hdisjoint hunion
        have hCnot : C ∉ Q.parts := by
          intro hCQ
          have hsub := Q.subset hCQ
          obtain ⟨x, hx⟩ := hCnonempty
          exact (Finset.mem_sdiff.mp (hsub hx)).2 hx
        refine ⟨P, ?_, ?_⟩
        · intro D hD E hED hhalf
          have hparts : D = C ∨ D ∈ Q.parts := by
            simpa [P, Finpartition.extend] using hD
          rcases hparts with rfl | hDQ
          · exact minimum_sparse_cut_expands_close_residual_part
              σ R T U γ hTR hTminimum hclose E
              (by simpa only [C] using hED)
              (by simpa only [C] using hhalf)
          · exact hQexpand D hDQ E hED hhalf
        · have hUcard : (U.card : ℝ) ≤
              2 * (C.card : ℝ) := by
            exact_mod_cast hpiece.2.1
          have hUcost :
              2 * (boundary σ U : ℝ) ≤
                4 * α * (C.card : ℝ) := by
            have hscale := mul_le_mul_of_nonneg_left hUcard hα
            linarith only [hscale, hUboundary]
          have hsplit :
              (boundary σ C : ℝ) +
                  (boundary σ (R \ C) : ℝ) ≤
                (boundary σ R : ℝ) +
                  2 * (boundary σ U : ℝ) := by
            have h := boundary_inter_add_boundary_sdiff_le σ R U
            have hres : R \ C = R \ U := by
              ext x
              simp only [Finset.sdiff_inter_self_left, Finset.mem_sdiff, C]
            simpa only [C, hres, Nat.cast_add, Nat.cast_mul,
              Nat.cast_ofNat] using
              (show
                ((boundary σ (R ∩ U) +
                  boundary σ (R \ U) : ℕ) : ℝ) ≤
                ((boundary σ R +
                  2 * boundary σ U : ℕ) : ℝ)
                from by exact_mod_cast h)
          have hcard :
              ((R \ C).card : ℝ) + (C.card : ℝ) =
                (R.card : ℝ) := by
            exact_mod_cast Finset.card_sdiff_add_card_eq_card hCR
          calc
            (∑ D ∈ P.parts, (boundary σ D : ℝ)) =
                (boundary σ C : ℝ) +
                  ∑ D ∈ Q.parts,
                    (boundary σ D : ℝ) := by
                  simp only [Finpartition.extend, hCnot, not_false_eq_true, Finset.sum_insert, P]
            _ ≤ (boundary σ C : ℝ) +
                  ((boundary σ (R \ C) : ℝ) +
                    4 * α * ((R \ C).card : ℝ)) :=
                    add_le_add (le_refl _) hQbudget
            _ ≤ (boundary σ R : ℝ) +
                  2 * (boundary σ U : ℝ) +
                    4 * α * ((R \ C).card : ℝ) := by
                  linarith
            _ ≤ (boundary σ R : ℝ) +
                  4 * α * (C.card : ℝ) +
                    4 * α * ((R \ C).card : ℝ) := by
                  linarith
            _ = (boundary σ R : ℝ) +
                  4 * α * (R.card : ℝ) := by
                  linear_combination (4 * α) * hcard
      · refine ⟨Finpartition.indiscrete hR.ne_empty, ?_, ?_⟩
        · intro C hC E hEC _
          have hCR : C = R := by
            simpa only [Finpartition.indiscrete, Finset.mem_singleton] using hC
          subst C
          by_contra h
          apply hsparse
          exact ⟨E, hEC, lt_of_not_ge h⟩
        · simp only [Finpartition.indiscrete, Finset.sum_singleton]
          have hnonneg : 0 ≤ 4 * α * (R.card : ℝ) := by
            positivity
          linarith
    · have hzero : R = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hR
      subst R
      refine ⟨Finpartition.empty (Finset V), ?_, ?_⟩
      · simp only [Finpartition.empty_parts, Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
      · simp only [Finpartition.empty_parts, boundary, Nat.cast_sum, Finset.sum_empty,
        Finset.notMem_empty,
          not_false_eq_true, Finset.filter_empty, Finset.card_empty, Finset.sum_const_zero,
            CharP.cast_eq_zero, mul_zero,
          add_zero, Std.le_refl]
  exact hmain R hRB

theorem exists_expanding_clean_finpartition
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B : Finset V) (γ α : ℝ)
    (hα : 0 ≤ α)
    (himprove : ∀ T : Finset V, T ⊆ Finset.univ \ B →
      (boundary σ T : ℝ) < γ * (T.card : ℝ) →
      ∃ U : Finset V, 3 * (U ∆ T).card < T.card ∧
        (boundary σ U : ℝ) ≤ α * (U.card : ℝ)) :
    ∃ P : Finpartition (Finset.univ \ B),
      (∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤ (boundary σ E : ℝ)) ∧
      (∑ C ∈ P.parts, (boundary σ C : ℝ)) ≤
        (Fintype.card ι : ℝ) * (B.card : ℝ) +
          4 * α * ((Finset.univ \ B).card : ℝ) := by
  obtain ⟨P, hP, hbudget⟩ :=
    exists_expanding_residual_finpartition σ B γ α hα himprove
      (Finset.univ \ B) (Finset.Subset.refl _)
  refine ⟨P, hP, ?_⟩
  calc
    (∑ C ∈ P.parts, (boundary σ C : ℝ)) ≤
        (boundary σ (Finset.univ \ B) : ℝ) +
          4 * α * ((Finset.univ \ B).card : ℝ) := hbudget
    _ = (boundary σ B : ℝ) +
          4 * α * ((Finset.univ \ B).card : ℝ) := by
            rw [boundary_complement]
    _ ≤ (Fintype.card ι : ℝ) * (B.card : ℝ) +
          4 * α * ((Finset.univ \ B).card : ℝ) := by
            have hdegree := boundary_le_degree_mul_card σ B
            have hdegreeReal :
                (boundary σ B : ℝ) ≤
                  (Fintype.card ι : ℝ) * (B.card : ℝ) := by
              exact_mod_cast hdegree
            linarith

noncomputable def completeCleanFinpartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (P : Finpartition (Finset.univ \ B)) :
    Finpartition (Finset.univ : Finset V) := by
  classical
  let parts : Finset (Finset V) :=
    P.parts ∪ (⊥ : Finpartition B).parts
  refine Finpartition.ofExistsUnique parts ?_ ?_ ?_
  · intro C _
    exact Finset.subset_univ C
  · intro x _
    by_cases hx : x ∈ B
    · refine ⟨{x}, ⟨?_, by simp only [Finset.mem_singleton]⟩, ?_⟩
      · exact Finset.mem_union_right _
          (Finpartition.mem_bot_iff.mpr ⟨x, hx, rfl⟩)
      · intro C hC
        obtain ⟨hpart, hxC⟩ := hC
        rcases Finset.mem_union.mp hpart with hclean | hbad
        · have hxc := P.subset hclean hxC
          exact ((Finset.mem_sdiff.mp hxc).2 hx).elim
        · obtain ⟨y, _, hy⟩ := Finpartition.mem_bot_iff.mp hbad
          subst C
          simp only [Finset.mem_singleton] at hxC
          subst y
          rfl
    · have hxclean : x ∈ (Finset.univ \ B : Finset V) := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, hx, not_false_eq_true, and_self]
      obtain ⟨C, ⟨hCP, hxC⟩, hunique⟩ :=
        P.existsUnique_mem hxclean
      refine ⟨C, ⟨Finset.mem_union_left _ hCP, hxC⟩, ?_⟩
      intro D hD
      obtain ⟨hpart, hxD⟩ := hD
      rcases Finset.mem_union.mp hpart with hclean | hbad
      · exact hunique D ⟨hclean, hxD⟩
      · obtain ⟨y, hyB, hy⟩ := Finpartition.mem_bot_iff.mp hbad
        subst D
        simp only [Finset.mem_singleton] at hxD
        exact (hx (hxD.symm ▸ hyB)).elim
  · intro hempty
    rcases Finset.mem_union.mp hempty with hclean | hbad
    · exact P.empty_notMem_parts hclean
    · obtain ⟨x, _, hx⟩ := Finpartition.mem_bot_iff.mp hbad
      simp only [Finset.singleton_ne_empty] at hx

@[simp]
theorem completeCleanFinpartition_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (P : Finpartition (Finset.univ \ B)) :
    (completeCleanFinpartition B P).parts =
      P.parts ∪ (⊥ : Finpartition B).parts := by
  rfl

theorem disjoint_clean_parts_singleton_bad_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (P : Finpartition (Finset.univ \ B)) :
    Disjoint P.parts (⊥ : Finpartition B).parts := by
  apply Finset.disjoint_left.mpr
  intro C hCP hCB
  obtain ⟨x, hxB, hxC⟩ := Finpartition.mem_bot_iff.mp hCB
  subst C
  have hxclean := P.subset hCP (Finset.mem_singleton_self x)
  exact (Finset.mem_sdiff.mp hxclean).2 hxB

theorem sum_singleton_bad_boundary_le
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B : Finset V) :
    (∑ C ∈ (⊥ : Finpartition B).parts,
      (boundary σ C : ℝ)) ≤
        (Fintype.card ι : ℝ) * (B.card : ℝ) := by
  classical
  calc
    (∑ C ∈ (⊥ : Finpartition B).parts,
      (boundary σ C : ℝ)) =
        ∑ x ∈ B, (boundary σ {x} : ℝ) := by
          simp only [Finpartition.parts_bot, Finset.sum_map, Function.Embedding.coeFn_mk]
    _ ≤ ∑ _x ∈ B, (Fintype.card ι : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          have h := boundary_le_degree_mul_card σ ({x} : Finset V)
          have h' :
              boundary σ ({x} : Finset V) ≤
                Fintype.card ι := by
            simpa only [Finset.card_singleton, mul_one] using h
          exact_mod_cast h'
    _ = (Fintype.card ι : ℝ) * (B.card : ℝ) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem completeCleanFinpartition_half_expansion
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B : Finset V)
    (P : Finpartition (Finset.univ \ B)) (γ : ℝ)
    (hexpand : ∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (boundary σ E : ℝ)) :
    ∀ C ∈ (completeCleanFinpartition B P).parts,
      ∀ E : Finset V, E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤ (boundary σ E : ℝ) := by
  classical
  intro C hC E hEC hhalf
  rw [completeCleanFinpartition_parts] at hC
  rcases Finset.mem_union.mp hC with hclean | hbad
  · exact hexpand C hclean E hEC hhalf
  · obtain ⟨x, _, hx⟩ := Finpartition.mem_bot_iff.mp hbad
    subst C
    have hE : E = ∅ := by
      apply Finset.card_eq_zero.mp
      simp only [Finset.card_singleton] at hhalf
      omega
    subst E
    simp only [Finset.card_empty, CharP.cast_eq_zero, mul_zero, boundary, Finset.notMem_empty,
      not_false_eq_true,
      Finset.filter_empty, Finset.sum_const_zero, Std.le_refl]

theorem exists_expanding_full_finpartition
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B : Finset V) (γ α : ℝ)
    (hα : 0 ≤ α)
    (himprove : ∀ T : Finset V, T ⊆ Finset.univ \ B →
      (boundary σ T : ℝ) < γ * (T.card : ℝ) →
      ∃ U : Finset V, 3 * (U ∆ T).card < T.card ∧
        (boundary σ U : ℝ) ≤ α * (U.card : ℝ)) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤ (boundary σ E : ℝ)) ∧
      (∑ C ∈ P.parts, (boundary σ C : ℝ)) ≤
        2 * (Fintype.card ι : ℝ) * (B.card : ℝ) +
          4 * α * (Fintype.card V : ℝ) := by
  classical
  obtain ⟨Q, hQexpand, hQbudget⟩ :=
    exists_expanding_clean_finpartition σ B γ α hα himprove
  let P : Finpartition (Finset.univ : Finset V) :=
    completeCleanFinpartition B Q
  refine ⟨P, ?_, ?_⟩
  · exact completeCleanFinpartition_half_expansion
      σ B Q γ hQexpand
  · have hbad := sum_singleton_bad_boundary_le σ B
    have hdisjoint :=
      disjoint_clean_parts_singleton_bad_parts B Q
    have hclean :
        ((Finset.univ \ B).card : ℝ) ≤
          (Fintype.card V : ℝ) := by
      exact_mod_cast
        (Finset.card_le_card
          (Finset.sdiff_subset :
            Finset.univ \ B ⊆ (Finset.univ : Finset V)))
    have hscaled := mul_le_mul_of_nonneg_left hclean
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hα)
    calc
      (∑ C ∈ P.parts, (boundary σ C : ℝ)) =
          (∑ C ∈ Q.parts, (boundary σ C : ℝ)) +
            (∑ C ∈ (⊥ : Finpartition B).parts,
              (boundary σ C : ℝ)) := by
                change
                  (∑ C ∈ (completeCleanFinpartition B Q).parts,
                    (boundary σ C : ℝ)) = _
                rw [completeCleanFinpartition_parts,
                  Finset.sum_union hdisjoint]
      _ ≤ ((Fintype.card ι : ℝ) * (B.card : ℝ) +
            4 * α * ((Finset.univ \ B).card : ℝ)) +
          (Fintype.card ι : ℝ) * (B.card : ℝ) :=
            add_le_add hQbudget hbad
      _ ≤ 2 * (Fintype.card ι : ℝ) * (B.card : ℝ) +
          4 * α * (Fintype.card V : ℝ) := by
            nlinarith

theorem exists_expanding_full_finpartition_sequence
    (ι : Type*) [Fintype ι]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)]
    [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (B : (n : ℕ) → Finset (V n))
    (γ : ℝ) (hγ : 0 < γ)
    (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n)
    (hαzero : Tendsto α atTop (nhds 0))
    (hbad : Tendsto
      (fun n => ((B n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0))
    (himprove : ∀ n (T : Finset (V n)),
      T ⊆ Finset.univ \ B n →
      (boundary (σ n) T : ℝ) <
        γ * (T.card : ℝ) →
      ∃ U : Finset (V n), 3 * (U ∆ T).card < T.card ∧
        (boundary (σ n) U : ℝ) ≤
          α n * (U.card : ℝ)) :
    ∃ P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)),
      0 < γ ∧
      (∀ n, ∀ C ∈ (P n).parts, ∀ E : Finset (V n), E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤
            (boundary (σ n) E : ℝ)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (P n).parts,
            (boundary (σ n) C : ℝ)) /
              Fintype.card (V n))
        atTop (nhds 0) := by
  classical
  have hchoose (n : ℕ) :=
    exists_expanding_full_finpartition
      (σ n) (B n) γ (α n) (hα n) (himprove n)
  let P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)) :=
    fun n => (hchoose n).choose
  have hexpand (n : ℕ) :
      ∀ C ∈ (P n).parts, ∀ E : Finset (V n), E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤
            (boundary (σ n) E : ℝ) :=
    (hchoose n).choose_spec.1
  have hbudget (n : ℕ) :
      (∑ C ∈ (P n).parts,
        (boundary (σ n) C : ℝ)) ≤
        2 * (Fintype.card ι : ℝ) * ((B n).card : ℝ) +
          4 * α n * (Fintype.card (V n) : ℝ) :=
    (hchoose n).choose_spec.2
  have hpositive (n : ℕ) :
      (0 : ℝ) < Fintype.card (V n) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hupper (n : ℕ) :
      (∑ C ∈ (P n).parts,
        (boundary (σ n) C : ℝ)) /
          Fintype.card (V n) ≤
        (2 * (Fintype.card ι : ℝ)) *
          (((B n).card : ℝ) / Fintype.card (V n)) +
            4 * α n := by
    calc
      (∑ C ∈ (P n).parts,
        (boundary (σ n) C : ℝ)) /
          Fintype.card (V n) ≤
        (2 * (Fintype.card ι : ℝ) * ((B n).card : ℝ) +
          4 * α n * (Fintype.card (V n) : ℝ)) /
            Fintype.card (V n) :=
              div_le_div_of_nonneg_right (hbudget n)
                (hpositive n).le
      _ = (2 * (Fintype.card ι : ℝ)) *
            (((B n).card : ℝ) / Fintype.card (V n)) +
          4 * α n := by
            field_simp [(hpositive n).ne']
  have hlimit : Tendsto
      (fun n =>
        (2 * (Fintype.card ι : ℝ)) *
          (((B n).card : ℝ) / Fintype.card (V n)) +
            4 * α n)
      atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using (hbad.const_mul (2 * (Fintype.card ι : ℝ))).add
      (hαzero.const_mul 4)
  refine ⟨P, hγ, hexpand, ?_⟩
  exact squeeze_zero
    (fun n => div_nonneg
      (Finset.sum_nonneg fun C _ => Nat.cast_nonneg _)
      (hpositive n).le)
    hupper hlimit

theorem original_boundary_le_completed_add_component_boundary
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (C : Finset V)
    (τ : ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ i (x : V) (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (A : Finset {x : V // x ∈ C}) :
    boundary σ
        (A.map (Function.Embedding.subtype (fun x : V => x ∈ C))) ≤
      boundary τ A +
        boundary σ C := by
  classical
  let E : Finset V :=
    A.map (Function.Embedding.subtype (fun x : V => x ∈ C))
  change
    (∑ i : ι, (E.filter fun x => σ i x ∉ E).card) ≤
      (∑ i : ι, (A.filter fun x => τ i x ∉ A).card) +
        ∑ i : ι, (C.filter fun x => σ i x ∉ C).card
  calc
    (∑ i : ι, (E.filter fun x => σ i x ∉ E).card) ≤
      ∑ i : ι,
        ((A.filter fun x => τ i x ∉ A).card +
          (C.filter fun x => σ i x ∉ C).card) := by
        apply Finset.sum_le_sum
        intro i _
        let F : Finset V :=
          (A.filter fun x => τ i x ∉ A).map
            (Function.Embedding.subtype (fun x : V => x ∈ C))
        let D : Finset V := C.filter fun x => σ i x ∉ C
        have hsub :
            (E.filter fun x => σ i x ∉ E) ⊆ F ∪ D := by
          intro x hx
          obtain ⟨hxE, hxout⟩ := Finset.mem_filter.mp hx
          obtain ⟨z, hzA, rfl⟩ := Finset.mem_map.mp hxE
          by_cases hzinternal : σ i (z : V) ∈ C
          · have hnot : τ i z ∉ A := by
              intro hmem
              apply hxout
              apply Finset.mem_map.mpr
              refine ⟨τ i z, hmem, ?_⟩
              exact hτ i (z : V) z.property hzinternal
            apply Finset.mem_union_left
            exact Finset.mem_map.mpr
              ⟨z, Finset.mem_filter.mpr ⟨hzA, hnot⟩, rfl⟩
          · apply Finset.mem_union_right
            exact Finset.mem_filter.mpr ⟨z.property, hzinternal⟩
        calc
          (E.filter fun x => σ i x ∉ E).card ≤
              (F ∪ D).card :=
                Finset.card_le_card hsub
          _ ≤ F.card + D.card :=
                Finset.card_union_le F D
          _ = (A.filter fun x => τ i x ∉ A).card +
                (C.filter fun x => σ i x ∉ C).card := by
                  simp only [Finset.card_map, F, D]
    _ = (∑ i : ι, (A.filter fun x => τ i x ∉ A).card) +
          ∑ i : ι, (C.filter fun x => σ i x ∉ C).card := by
            rw [Finset.sum_add_distrib]

theorem completed_component_additive_expansion
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (C : Finset V)
    (τ : ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ i (x : V) (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (γ : ℝ)
    (hexpand : ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (boundary σ E : ℝ)) :
    ∀ A : Finset {x : V // x ∈ C},
      γ * min (A.card : ℝ) ((C.card : ℝ) - A.card) -
          (boundary σ C : ℝ) ≤
        (boundary τ A : ℝ) := by
  classical
  have hhalf (A : Finset {x : V // x ∈ C})
      (hA : 2 * A.card ≤ C.card) :
      γ * (A.card : ℝ) -
          (boundary σ C : ℝ) ≤
        (boundary τ A : ℝ) := by
    let E : Finset V :=
      A.map (Function.Embedding.subtype (fun x : V => x ∈ C))
    have hEC : E ⊆ C := by
      intro x hx
      exact Finset.property_of_mem_map_subtype A hx
    have hEcard : E.card = A.card := by
      dsimp [E]
      exact Finset.card_map _
    have hEhalf : 2 * E.card ≤ C.card := by
      simpa only [hEcard] using hA
    have hsource := hexpand E hEC hEhalf
    have hboundary :
        (boundary σ E : ℝ) ≤
          (boundary τ A : ℝ) +
            (boundary σ C : ℝ) := by
      have h :=
        original_boundary_le_completed_add_component_boundary
          σ C τ hτ A
      change
        ((boundary σ E : ℕ) : ℝ) ≤ _
      exact_mod_cast h
    rw [hEcard] at hsource
    linarith
  intro A
  by_cases hA : 2 * A.card ≤ C.card
  · have hreal :
        (2 : ℝ) * (A.card : ℝ) ≤ (C.card : ℝ) := by
      exact_mod_cast hA
    rw [min_eq_left (by linarith)]
    exact hhalf A hA
  · let D : Finset {x : V // x ∈ C} := Finset.univ \ A
    have hcard :
        D.card + A.card = C.card := by
      dsimp [D]
      have h :=
        Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ A)
      simpa only [Finset.univ_eq_attach, Finset.card_attach] using h
    have hDhalf : 2 * D.card ≤ C.card := by
      omega
    have hD := hhalf D hDhalf
    have hDreal :
        (D.card : ℝ) = (C.card : ℝ) - (A.card : ℝ) := by
      have hreal :
          (D.card : ℝ) + (A.card : ℝ) = (C.card : ℝ) := by
        exact_mod_cast hcard
      linarith
    have hreal :
        (C.card : ℝ) < 2 * (A.card : ℝ) := by
      exact_mod_cast Nat.lt_of_not_ge hA
    rw [min_eq_right (by linarith)]
    rw [hDreal] at hD
    have hcomplement :
        boundary τ D =
          boundary τ A := by
      simpa only [D] using boundary_complement τ A
    rw [hcomplement] at hD
    exact hD

end KunResidualExpanderDecomposition

namespace KunDiagonalGoodRootGraphLoss

open scoped BigOperators symmDiff

def goodPermutationGraph {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) : Finset (V × V) :=
  (permutationGraph p).filter
    (fun z => z.1 ∉ B ∧ z.2 ∉ B)

theorem goodPermutationGraph_subset {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    goodPermutationGraph p B ⊆ permutationGraph p :=
  Finset.filter_subset _ _

theorem card_filter_permutationGraph_proj_mem {V : Type*}
    [Fintype V] [DecidableEq V]
    (π : V × V → V) (p : Equiv.Perm V) (w : V → V × V)
    (hmem : ∀ x, w x ∈ permutationGraph p)
    (hproj : ∀ x, π (w x) = x)
    (hpoint : ∀ z ∈ permutationGraph p, w (π z) = z)
    (B : Finset V) :
    ((permutationGraph p).filter
      fun z => π z ∈ B).card = B.card := by
  classical
  apply Finset.card_bij (fun z _ => π z)
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro z hz w' hw' hproj'
    rw [← hpoint z (Finset.mem_filter.mp hz).1,
      ← hpoint w' (Finset.mem_filter.mp hw').1, hproj']
  · intro x hx
    exact ⟨w x, Finset.mem_filter.mpr
      ⟨hmem x, by rw [hproj x]; exact hx⟩, hproj x⟩

theorem card_filter_permutationGraph_fst_mem {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    ((permutationGraph p).filter
      fun z => z.1 ∈ B).card = B.card :=
  card_filter_permutationGraph_proj_mem Prod.fst p (fun y => (y, p y))
    (fun y => (mem_permutationGraph p y (p y)).mpr rfl)
    (fun _ => rfl)
    (fun z hz => Prod.ext rfl
      ((mem_permutationGraph p z.1 z.2).mp hz).symm)
    B

theorem card_filter_permutationGraph_snd_mem {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    ((permutationGraph p).filter
      fun z => z.2 ∈ B).card = B.card :=
  card_filter_permutationGraph_proj_mem Prod.snd p (fun y => (p.symm y, y))
    (fun y => (mem_permutationGraph p (p.symm y) y).mpr
      (p.apply_symm_apply y).symm)
    (fun _ => rfl)
    (fun z hz => Prod.ext
      (by rw [(mem_permutationGraph p z.1 z.2).mp hz,
        p.symm_apply_apply])
      rfl)
    B

theorem permutationGraph_sdiff_goodPermutationGraph_subset {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    permutationGraph p \ goodPermutationGraph p B ⊆
      ((permutationGraph p).filter fun z => z.1 ∈ B) ∪
        ((permutationGraph p).filter fun z => z.2 ∈ B) := by
  intro z hz
  obtain ⟨hzgraph, hzgood⟩ := Finset.mem_sdiff.mp hz
  by_cases hfirst : z.1 ∈ B
  · exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hzgraph, hfirst⟩)
  · have hsecond : z.2 ∈ B := by
      by_contra h
      apply hzgood
      exact Finset.mem_filter.mpr ⟨hzgraph, hfirst, h⟩
    exact Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨hzgraph, hsecond⟩)

theorem card_permutationGraph_sdiff_goodPermutationGraph_le {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    (permutationGraph p \ goodPermutationGraph p B).card ≤
      2 * B.card := by
  calc
    (permutationGraph p \ goodPermutationGraph p B).card ≤
        (((permutationGraph p).filter fun z => z.1 ∈ B) ∪
          ((permutationGraph p).filter
            fun z => z.2 ∈ B)).card :=
      Finset.card_le_card
        (permutationGraph_sdiff_goodPermutationGraph_subset p B)
    _ ≤ ((permutationGraph p).filter
          fun z => z.1 ∈ B).card +
        ((permutationGraph p).filter
          fun z => z.2 ∈ B).card := Finset.card_union_le _ _
    _ = 2 * B.card := by
      rw [card_filter_permutationGraph_fst_mem,
        card_filter_permutationGraph_snd_mem]
      omega

theorem card_goodPermutationGraph_add_graph_loss {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    (permutationGraph p \ goodPermutationGraph p B).card +
        (goodPermutationGraph p B).card = Fintype.card V := by
  calc
    (permutationGraph p \ goodPermutationGraph p B).card +
        (goodPermutationGraph p B).card =
        (permutationGraph p).card :=
      Finset.card_sdiff_add_card_eq_card
        (goodPermutationGraph_subset p B)
    _ = Fintype.card V :=
      KunThomFiberCoarea.permutationGraph_card p

theorem card_goodPermutationGraph_ge_card_sub_twice_bad {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    (Fintype.card V : ℝ) - 2 * (B.card : ℝ) ≤
      ((goodPermutationGraph p B).card : ℝ) := by
  have hloss :
      (((permutationGraph p \
        goodPermutationGraph p B).card : ℕ) : ℝ) ≤
          2 * (B.card : ℝ) := by
    exact_mod_cast card_permutationGraph_sdiff_goodPermutationGraph_le p B
  have htotal :
      (((permutationGraph p \
        goodPermutationGraph p B).card : ℕ) : ℝ) +
          ((goodPermutationGraph p B).card : ℝ) =
        (Fintype.card V : ℝ) := by
    exact_mod_cast card_goodPermutationGraph_add_graph_loss p B
  linarith

theorem boundary_goodPermutationGraph_le_commutationDefect_add {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (p : Equiv.Perm V) (B : Finset V) :
    boundary
        (fun i => (σ i).prodCongr (σ i)) (goodPermutationGraph p B) ≤
      permutationCommutationDefect σ p +
        2 * Fintype.card ι * B.card := by
  have hboundary :=
    KunThomFiberCoarea.boundary_le_boundary_add_sdiff
      (fun i => (σ i).prodCongr (σ i))
      (goodPermutationGraph p B) (permutationGraph p)
  rw [boundary_permutationGraph_eq_commutationDefect,
    Finset.sdiff_eq_empty_iff_subset.mpr
      (goodPermutationGraph_subset p B),
    Finset.card_empty, zero_add] at hboundary
  calc
    boundary
        (fun i => (σ i).prodCongr (σ i)) (goodPermutationGraph p B) ≤
      permutationCommutationDefect σ p +
        Fintype.card ι *
          (permutationGraph p \
            goodPermutationGraph p B).card := hboundary
    _ ≤ permutationCommutationDefect σ p +
        Fintype.card ι * (2 * B.card) := by
      gcongr
      exact card_permutationGraph_sdiff_goodPermutationGraph_le p B
    _ = permutationCommutationDefect σ p +
        2 * Fintype.card ι * B.card := by
      ring

end KunDiagonalGoodRootGraphLoss

namespace KunCompletedPrunedComponent

open scoped BigOperators

theorem hasAlmostCentralizerImprovement_zero
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) :
    HasAlmostCentralizerImprovement σ 0 := by
  refine ⟨fun p hp => ⟨p, ?_, ?_⟩⟩
  · simpa only [nonpos_iff_eq_zero, mul_zero] using hp
  · simp only [permutationDistance_self, mul_zero, zero_le]


theorem boundary_expansion_of_half
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hhalf : ∀ A : Finset V,
      2 * A.card ≤ Fintype.card V →
        h * (A.card : ℝ) ≤ (boundary σ A : ℝ)) :
    ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (boundary σ A : ℝ) := by
  classical
  intro A
  by_cases hA : 2 * A.card ≤ Fintype.card V
  · have hAreal :
        (2 : ℝ) * A.card ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hA
    rw [min_eq_left (by linarith)]
    exact hhalf A hA
  · let C : Finset V := Finset.univ \ A
    have hcard : C.card + A.card = Fintype.card V := by
      dsimp [C]
      simpa only [Finset.card_univ] using (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ
        A))
    have hChalf : 2 * C.card ≤ Fintype.card V := by
      omega
    have hC := hhalf C hChalf
    have hAreal :
        (Fintype.card V : ℝ) < (2 : ℝ) * A.card := by
      exact_mod_cast Nat.lt_of_not_ge hA
    have hCreal :
        (C.card : ℝ) = (Fintype.card V : ℝ) - A.card := by
      have hcardReal :
          (C.card : ℝ) + A.card = (Fintype.card V : ℝ) := by
        exact_mod_cast hcard
      linarith
    rw [min_eq_right (by linarith)]
    rw [hCreal] at hC
    simpa [C, KunResidualExpanderDecomposition.boundary_complement] using hC

theorem inducedBoundary_le_completed_boundary
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B Z : Finset V)
    (hZ : Z = Finset.univ \ B)
    (τ : ι → Equiv.Perm {x : V // x ∈ Z})
    (hτ : ∀ i (x : V) (hx : x ∈ Z) (_hy : σ i x ∈ Z),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ Z}) : V) = σ i x)
    (A : Finset {x : V // x ∈ Z}) :
    inducedBoundary σ B
        (A.map (Function.Embedding.subtype (fun x : V => x ∈ Z))) ≤
      boundary τ A := by
  classical
  let E : Finset V :=
    A.map (Function.Embedding.subtype (fun x : V => x ∈ Z))
  have hmemZ (x : V) : x ∈ Z ↔ x ∉ B := by
    rw [hZ]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  change
    (∑ i : ι,
      (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E).card) ≤
      ∑ i : ι, (A.filter fun x => τ i x ∉ A).card
  apply Finset.sum_le_sum
  intro i _
  have hsub :
      (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E) ⊆
        (A.filter fun x => τ i x ∉ A).map
          (Function.Embedding.subtype (fun x : V => x ∈ Z)) := by
    intro x hx
    obtain ⟨hxE, hxB, hxout⟩ := Finset.mem_filter.mp hx
    obtain ⟨z, hzA, rfl⟩ := Finset.mem_map.mp hxE
    have himage : σ i (z : V) ∈ Z :=
      (hmemZ (σ i (z : V))).2 hxB
    have hnot : τ i z ∉ A := by
      intro hmem
      apply hxout
      exact Finset.mem_map.mpr
        ⟨τ i z, hmem, hτ i (z : V) z.property himage⟩
    exact Finset.mem_map.mpr
      ⟨z, Finset.mem_filter.mpr ⟨hzA, hnot⟩, rfl⟩
  calc
    (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E).card ≤
        ((A.filter fun x => τ i x ∉ A).map
          (Function.Embedding.subtype (fun x : V => x ∈ Z))).card :=
      Finset.card_le_card hsub
    _ = (A.filter fun x => τ i x ∉ A).card :=
      Finset.card_map _

theorem exists_completed_pruned_expander
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ell a : ℝ)
    (hgap : ell < γ)
    (hadd : ∀ A : Finset V,
      γ * min (A.card : ℝ)
          ((Fintype.card V : ℝ) - (A.card : ℝ)) -
        a * (Fintype.card V : ℝ) ≤
          (boundary σ A : ℝ))
    (hsmall :
      2 * a * (2 * (γ - ell) + (Fintype.card ι : ℝ)) ≤
        (γ - ell) ^ 2) :
    ∃ (B : Finset V)
      (τ : ι → Equiv.Perm
        {x : V // x ∈ (Finset.univ \ B)}),
      2 * B.card ≤ Fintype.card V ∧
      (B.card : ℝ) ≤
        a * (Fintype.card V : ℝ) / (γ - ell) ∧
      (∀ i (x : V) (hx : x ∈ Finset.univ \ B)
        (_hy : σ i x ∈ Finset.univ \ B),
        ((τ i ⟨x, hx⟩ :
          {x : V // x ∈ Finset.univ \ B}) : V) = σ i x) ∧
      ∀ A : Finset {x : V // x ∈ Finset.univ \ B},
        ell * min (A.card : ℝ)
          ((Fintype.card {x : V // x ∈ Finset.univ \ B} : ℝ) -
            A.card) ≤ (boundary τ A : ℝ) := by
  classical
  obtain ⟨B, hBhalf, hBsize, hprune⟩ :=
    exists_pruned_expander σ γ ell a hgap hadd hsmall
  let Z : Finset V := Finset.univ \ B
  have hZ : Z = Finset.univ \ B := rfl
  choose τ hτ using
    (fun i : ι =>
      exists_completion_of_internal_permutation
        (σ i) Z)
  have hcardZ :
      Fintype.card {x : V // x ∈ Z} =
        Fintype.card V - B.card := by
    rw [Fintype.card_coe]
    dsimp [Z]
    exact Finset.card_sdiff_of_subset (Finset.subset_univ B)
  have hexp :
      ∀ A : Finset {x : V // x ∈ Z},
        ell * min (A.card : ℝ)
          ((Fintype.card {x : V // x ∈ Z} : ℝ) - A.card) ≤
            (boundary τ A : ℝ) := by
    apply boundary_expansion_of_half τ ell
    intro A hA
    let E : Finset V :=
      A.map (Function.Embedding.subtype (fun x : V => x ∈ Z))
    have hEcard : E.card = A.card := by
      dsimp [E]
      exact Finset.card_map _
    have hdisj : Disjoint B E := by
      apply Finset.disjoint_left.mpr
      intro x hxB hxE
      have hxZ : x ∈ Z :=
        Finset.property_of_mem_map_subtype A hxE
      rw [hZ] at hxZ
      exact (Finset.mem_sdiff.mp hxZ).2 hxB
    have hhalf : 2 * E.card ≤ Fintype.card V - B.card := by
      rw [hEcard, ← hcardZ]
      exact hA
    have hcut := hprune E hdisj hhalf
    have hbound :
        (inducedBoundary σ B E : ℝ) ≤
          (boundary τ A : ℝ) := by
      exact_mod_cast
        inducedBoundary_le_completed_boundary σ B Z hZ τ hτ A
    rw [hEcard] at hcut
    exact hcut.trans hbound
  refine ⟨B, τ, hBhalf, hBsize, ?_, ?_⟩
  · simpa only [Z] using hτ
  · intro A
    have hA := hexp A
    simpa only [Fintype.card_coe] using hA

end KunCompletedPrunedComponent

namespace MatchedComponentCompletion

open scoped BigOperators

noncomputable def completedRestriction {V : Type*} [Fintype V]
    (p : Equiv.Perm V) (Z : Finset V) :
    Equiv.Perm (↥Z) :=
  Classical.choose (exists_completion_of_internal_permutation p Z)

theorem completedRestriction_apply_of_mem
    {V : Type*} [Fintype V]
    (p : Equiv.Perm V) (Z : Finset V)
    (x : V) (hx : x ∈ Z) (hp : p x ∈ Z) :
    ((completedRestriction p Z ⟨x, hx⟩ : {x : V // x ∈ Z}) : V) = p x :=
  (Classical.choose_spec
    (exists_completion_of_internal_permutation p Z)) x hx hp

@[simp] theorem completedRestriction_one
    {V : Type*} [Fintype V] (Z : Finset V) :
    completedRestriction (1 : Equiv.Perm V) Z = 1 := by
  ext x
  simpa only [Equiv.Perm.coe_one, id_eq, SetLike.coe_eq_coe, Subtype.coe_eta] using
    completedRestriction_apply_of_mem (1 : Equiv.Perm V) Z x x.property x.property

def subtypeBad {V : Type*} [DecidableEq V]
    (Z E : Finset V) : Finset (↥Z) :=
  Finset.univ.filter (fun x => (x : V) ∈ E)

@[simp] theorem mem_subtypeBad
    {V : Type*} [DecidableEq V]
    (Z E : Finset V) (x : {x : V // x ∈ Z}) :
    x ∈ subtypeBad Z E ↔ (x : V) ∈ E := by
  simp only [subtypeBad, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach, true_and]

theorem card_subtypeBad
    {V : Type*} [DecidableEq V]
    (Z E : Finset V) :
    (subtypeBad Z E).card = (Z ∩ E).card := by
  classical
  have hmap :
      (subtypeBad Z E).map
        (Function.Embedding.subtype (fun x : V => x ∈ Z)) = Z ∩ E := by
    ext x
    simp only [subtypeBad, Finset.univ_eq_attach, Finset.mem_map, Finset.mem_filter,
      Finset.mem_attach, true_and,
      Function.Embedding.subtype_apply, and_comm, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_left,
      Finset.mem_inter]
  simpa only [Finset.card_map] using congrArg Finset.card hmap

theorem permutationDistance_le_subtypeBad
    {V : Type*} [DecidableEq V]
    (Z E : Finset V)
    (p q : Equiv.Perm {x : V // x ∈ Z})
    (hagrees : ∀ x : {x : V // x ∈ Z},
      (x : V) ∉ E → p x = q x) :
    permutationDistance p q ≤ (subtypeBad Z E).card := by
  unfold permutationDistance hammingDist
  apply Finset.card_le_card
  intro x hx
  have hneq : p x ≠ q x := (Finset.mem_filter.mp hx).2
  apply (mem_subtypeBad Z E x).2
  by_contra hnot
  exact hneq (hagrees x hnot)

theorem card_lt_five_mul_permutationDistance_of_subtypeBad
    {V : Type*} [DecidableEq V]
    (Z E : Finset V) (hZ : Z.Nonempty)
    (p q : Equiv.Perm {x : V // x ∈ Z})
    (hbad : 5 * (subtypeBad Z E).card ≤ Fintype.card {x : V // x ∈ Z})
    (hseparated : ∀ x : {x : V // x ∈ Z},
      (x : V) ∉ E → p x ≠ q x) :
    Fintype.card {x : V // x ∈ Z} <
      5 * permutationDistance p q := by
  have hagree :
      (agreementSet p q).card ≤ (subtypeBad Z E).card := by
    apply Finset.card_le_card
    intro x hx
    have heq : p x = q x := (Finset.mem_filter.mp hx).2
    apply (mem_subtypeBad Z E x).2
    by_contra hnot
    exact hseparated x hnot heq
  have hpartition := agreementSet_card_add_hammingDist p q
  change
    (agreementSet p q).card +
        permutationDistance p q =
      Fintype.card {x : V // x ∈ Z} at hpartition
  have hpositive : 0 < Fintype.card {x : V // x ∈ Z} := by
    simpa only [Fintype.card_coe] using hZ.card_pos
  omega

noncomputable def sourceCompletionBad
    {V ι J : Type*} [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) : Finset V := by
  classical
  let T := CompressionCriterion.productTrackedTable F
  exact
    (Finset.univ.biUnion fun i : ι =>
      Z.filter fun z => σ i z ∉ Z) ∪
    (T.biUnion fun j =>
      Z.filter fun z => p j z ∉ Z) ∪
    (Finset.univ.biUnion fun i : ι =>
      T.biUnion fun j =>
        Z.filter fun z => p j (σ i z) ≠ σ i (p j z)) ∪
    (Finset.univ.biUnion fun i : ι =>
      T.biUnion fun j =>
        Z.filter fun z => p j (σ i z) ∉ Z) ∪
    (F.biUnion fun j =>
      F.biUnion fun k =>
        Z.filter fun z => p (j * k) z ≠ p j (p k z)) ∪
    (F.biUnion fun j =>
      F.biUnion fun k =>
        Z.filter fun z => j ≠ k ∧ p j z = p k z)

theorem sourceCompletionBad_subset
    {V ι J : Type*} [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) :
    sourceCompletionBad σ p F Z ⊆ Z := by
  classical
  intro x hx
  simp only [sourceCompletionBad, ne_eq, Finset.union_assoc, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_univ, Finset.mem_filter, true_and, exists_and_left] at hx
  aesop

theorem card_subtype_sourceCompletionBad
    {V ι J : Type*} [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) :
    (subtypeBad Z (sourceCompletionBad σ p F Z)).card =
      (sourceCompletionBad σ p F Z).card := by
  rw [card_subtypeBad, Finset.inter_eq_right.mpr]
  exact sourceCompletionBad_subset σ p F Z

theorem sourceCompletionBad_good
    {V ι J : Type*} [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V)
    (x : V) (hx : x ∈ Z)
    (hgood : x ∉ sourceCompletionBad σ p F Z) :
    (∀ i, σ i x ∈ Z) ∧
    (∀ j ∈ CompressionCriterion.productTrackedTable F,
      p j x ∈ Z) ∧
    (∀ i, ∀ j ∈ CompressionCriterion.productTrackedTable F,
      p j (σ i x) = σ i (p j x)) ∧
    (∀ i, ∀ j ∈ CompressionCriterion.productTrackedTable F,
      p j (σ i x) ∈ Z) ∧
    (∀ j ∈ F, ∀ k ∈ F,
      p (j * k) x = p j (p k x)) ∧
    (∀ j ∈ F, ∀ k ∈ F, j ≠ k → p j x ≠ p k x) := by
  classical
  simp only [sourceCompletionBad, ne_eq, Finset.union_assoc, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, hx, true_and,
    not_or, not_exists, Decidable.not_not, not_and] at hgood
  exact hgood

theorem completedRestriction_mul_of_not_mem_sourceCompletionBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V)
    {j k : J} (hj : j ∈ F) (hk : k ∈ F)
    (z : {x : V // x ∈ Z})
    (hz : (z : V) ∉ sourceCompletionBad σ p F Z) :
    completedRestriction (p (j * k)) Z z =
      (completedRestriction (p j) Z * completedRestriction (p k) Z) z := by
  have hg := sourceCompletionBad_good σ p F Z z z.property hz
  have hjT :=
    CompressionCriterion.mem_productTrackedTable hj
  have hkT :=
    CompressionCriterion.mem_productTrackedTable hk
  have hjkT :=
    CompressionCriterion.mul_mem_productTrackedTable hj hk
  have hkZ : p k (z : V) ∈ Z := hg.2.1 k hkT
  have hjkZ : p (j * k) (z : V) ∈ Z := hg.2.1 (j * k) hjkT
  have hmul : p (j * k) (z : V) = p j (p k (z : V)) :=
    hg.2.2.2.2.1 j hj k hk
  have hinner : p j (p k (z : V)) ∈ Z := by
    rw [← hmul]
    exact hjkZ
  have hkvalue :
      ((completedRestriction (p k) Z z : {x : V // x ∈ Z}) : V) =
        p k (z : V) :=
    completedRestriction_apply_of_mem (p k) Z z z.property hkZ
  apply Subtype.ext
  change
    ((completedRestriction (p (j * k)) Z z : {x : V // x ∈ Z}) : V) =
      ((completedRestriction (p j) Z
        (completedRestriction (p k) Z z) : {x : V // x ∈ Z}) : V)
  calc
    ((completedRestriction (p (j * k)) Z z : {x : V // x ∈ Z}) : V) =
        p (j * k) (z : V) :=
      completedRestriction_apply_of_mem (p (j * k)) Z z z.property hjkZ
    _ = p j (p k (z : V)) := hmul
    _ = p j
        ((completedRestriction (p k) Z z : {x : V // x ∈ Z}) : V) := by
      rw [hkvalue]
    _ = ((completedRestriction (p j) Z
        (completedRestriction (p k) Z z) : {x : V // x ∈ Z}) : V) := by
      symm
      apply completedRestriction_apply_of_mem
      change
        p j ((completedRestriction (p k) Z z :
          {x : V // x ∈ Z}) : V) ∈ Z
      rw [hkvalue]
      exact hinner

theorem completedRestriction_ne_of_not_mem_sourceCompletionBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V)
    {j k : J} (hj : j ∈ F) (hk : k ∈ F) (hne : j ≠ k)
    (z : {x : V // x ∈ Z})
    (hz : (z : V) ∉ sourceCompletionBad σ p F Z) :
    completedRestriction (p j) Z z ≠ completedRestriction (p k) Z z := by
  have hg := sourceCompletionBad_good σ p F Z z z.property hz
  have hjT :=
    CompressionCriterion.mem_productTrackedTable hj
  have hkT :=
    CompressionCriterion.mem_productTrackedTable hk
  have hjZ : p j (z : V) ∈ Z := hg.2.1 j hjT
  have hkZ : p k (z : V) ∈ Z := hg.2.1 k hkT
  intro heq
  apply hg.2.2.2.2.2 j hj k hk hne
  have hval := congrArg
    (fun x : {x : V // x ∈ Z} => (x : V)) heq
  rwa [completedRestriction_apply_of_mem (p j) Z z z.property hjZ,
    completedRestriction_apply_of_mem (p k) Z z z.property hkZ] at hval

theorem completedRestriction_commute_of_not_mem_sourceCompletionBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V)
    (σZ : ι → Equiv.Perm {x : V // x ∈ Z})
    (hσZ : ∀ i (x : V) (hx : x ∈ Z) (_hi : σ i x ∈ Z),
      ((σZ i ⟨x, hx⟩ : {x : V // x ∈ Z}) : V) = σ i x)
    {j : J}
    (hj : j ∈ CompressionCriterion.productTrackedTable F)
    (i : ι) (z : {x : V // x ∈ Z})
    (hz : (z : V) ∉ sourceCompletionBad σ p F Z) :
    completedRestriction (p j) Z (σZ i z) =
      σZ i (completedRestriction (p j) Z z) := by
  have hg := sourceCompletionBad_good σ p F Z z z.property hz
  have hσmem : σ i (z : V) ∈ Z := hg.1 i
  have hjmem : p j (z : V) ∈ Z := hg.2.1 j hj
  have hcomm : p j (σ i (z : V)) = σ i (p j (z : V)) :=
    hg.2.2.1 i j hj
  have hcomposite : p j (σ i (z : V)) ∈ Z :=
    hg.2.2.2.1 i j hj
  have hσvalue :
      ((σZ i z : {x : V // x ∈ Z}) : V) = σ i (z : V) :=
    hσZ i z z.property hσmem
  have hjvalue :
      ((completedRestriction (p j) Z z : {x : V // x ∈ Z}) : V) =
        p j (z : V) :=
    completedRestriction_apply_of_mem (p j) Z z z.property hjmem
  have hleftmem : p j ((σZ i z : {x : V // x ∈ Z}) : V) ∈ Z := by
    rw [hσvalue]
    exact hcomposite
  have hrightmem :
      σ i
        ((completedRestriction (p j) Z z : {x : V // x ∈ Z}) : V) ∈ Z := by
    rw [hjvalue, ← hcomm]
    exact hcomposite
  apply Subtype.ext
  calc
    ((completedRestriction (p j) Z (σZ i z) :
        {x : V // x ∈ Z}) : V) =
        p j ((σZ i z : {x : V // x ∈ Z}) : V) :=
      completedRestriction_apply_of_mem
        (p j) Z (σZ i z) (σZ i z).property hleftmem
    _ = p j (σ i (z : V)) := congrArg (p j) hσvalue
    _ = σ i (p j (z : V)) := hcomm
    _ = σ i
        ((completedRestriction (p j) Z z : {x : V // x ∈ Z}) : V) :=
      congrArg (σ i) hjvalue.symm
    _ = ((σZ i (completedRestriction (p j) Z z) :
        {x : V // x ∈ Z}) : V) :=
      (hσZ i (completedRestriction (p j) Z z)
        (completedRestriction (p j) Z z).property hrightmem).symm

theorem completedRestriction_mul_distance_le_sourceCompletionBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V)
    {j k : J} (hj : j ∈ F) (hk : k ∈ F) :
    permutationDistance
      (completedRestriction (p (j * k)) Z)
      (completedRestriction (p j) Z * completedRestriction (p k) Z) ≤
        (sourceCompletionBad σ p F Z).card := by
  calc
    permutationDistance
      (completedRestriction (p (j * k)) Z)
      (completedRestriction (p j) Z * completedRestriction (p k) Z) ≤
        (subtypeBad Z (sourceCompletionBad σ p F Z)).card := by
          apply permutationDistance_le_subtypeBad
          intro z hz
          exact completedRestriction_mul_of_not_mem_sourceCompletionBad
            σ p F Z hj hk z hz
    _ = (sourceCompletionBad σ p F Z).card :=
      card_subtype_sourceCompletionBad σ p F Z

theorem completedRestriction_separated_of_sourceCompletionBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) (hZ : Z.Nonempty)
    (hbad : 5 * (sourceCompletionBad σ p F Z).card ≤ Z.card)
    {j k : J} (hj : j ∈ F) (hk : k ∈ F) (hne : j ≠ k) :
    Fintype.card {x : V // x ∈ Z} <
      5 * permutationDistance
        (completedRestriction (p j) Z) (completedRestriction (p k) Z) := by
  apply card_lt_five_mul_permutationDistance_of_subtypeBad
    Z (sourceCompletionBad σ p F Z) hZ
  · simpa only [card_subtype_sourceCompletionBad, Fintype.card_coe]
      using hbad
  · intro z hz
    exact completedRestriction_ne_of_not_mem_sourceCompletionBad
      σ p F Z hj hk hne z hz

theorem completedRestriction_commutationDefect_le_sourceCompletionBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V)
    (σZ : ι → Equiv.Perm {x : V // x ∈ Z})
    (hσZ : ∀ i (x : V) (hx : x ∈ Z) (_hi : σ i x ∈ Z),
      ((σZ i ⟨x, hx⟩ : {x : V // x ∈ Z}) : V) = σ i x)
    {j : J}
    (hj : j ∈ CompressionCriterion.productTrackedTable F) :
    permutationCommutationDefect
        σZ (completedRestriction (p j) Z) ≤
      Fintype.card ι * (sourceCompletionBad σ p F Z).card := by
  classical
  unfold permutationCommutationDefect
  calc
    (∑ i : ι,
      (Finset.univ.filter fun x : {x : V // x ∈ Z} =>
        completedRestriction (p j) Z (σZ i x) ≠
          σZ i (completedRestriction (p j) Z x)).card) ≤
        ∑ _i : ι, (subtypeBad Z (sourceCompletionBad σ p F Z)).card := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.card_le_card
          intro x hx
          apply (mem_subtypeBad Z (sourceCompletionBad σ p F Z) x).2
          by_contra hnot
          exact (Finset.mem_filter.mp hx).2
            (completedRestriction_commute_of_not_mem_sourceCompletionBad
              σ p F Z σZ hσZ hj i x hnot)
    _ = Fintype.card ι * (sourceCompletionBad σ p F Z).card := by
      simp only [card_subtype_sourceCompletionBad, Finset.sum_const, Finset.card_univ, smul_eq_mul]

end MatchedComponentCompletion

namespace MatchedComponentExitBudget

open Filter Topology
open scoped BigOperators

theorem card_permutation_exit_le_deleted
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (Z : Finset V) :
    (Z.filter fun x => p x ∉ Z).card ≤
      (Finset.univ \ Z).card := by
  apply Finset.card_le_card_of_injOn p
  · intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  · exact p.injective.injOn

theorem card_composite_exit_le_deleted
    {V : Type*} [Fintype V] [DecidableEq V]
    (p q : Equiv.Perm V) (Z : Finset V) :
    (Z.filter fun x => p (q x) ∉ Z).card ≤
      (Finset.univ \ Z).card := by
  apply Finset.card_le_card_of_injOn (p * q)
  · intro x hx
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [Equiv.Perm.mul_apply] using (Finset.mem_filter.mp hx).2
  · exact (p * q).injective.injOn

theorem card_biUnion_permutation_exit_le
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (I : Finset ι) (p : ι → Equiv.Perm V) (Z : Finset V) :
    (I.biUnion fun i => Z.filter fun x => p i x ∉ Z).card ≤
      I.card * (Finset.univ \ Z).card := by
  classical
  calc
    (I.biUnion fun i => Z.filter fun x => p i x ∉ Z).card ≤
        ∑ i ∈ I, (Z.filter fun x => p i x ∉ Z).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, (Finset.univ \ Z).card := by
      apply Finset.sum_le_sum
      intro i _
      exact card_permutation_exit_le_deleted (p i) Z
    _ = I.card * (Finset.univ \ Z).card := by simp only [Finset.sum_const, smul_eq_mul]

theorem card_biUnion_composite_exit_le
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    (I : Finset ι) (K : Finset κ)
    (p : ι → Equiv.Perm V) (q : κ → Equiv.Perm V)
    (Z : Finset V) :
    (I.biUnion fun i =>
      K.biUnion fun k => Z.filter fun x => q k (p i x) ∉ Z).card ≤
        I.card * K.card * (Finset.univ \ Z).card := by
  classical
  calc
    (I.biUnion fun i =>
      K.biUnion fun k => Z.filter fun x => q k (p i x) ∉ Z).card ≤
        ∑ i ∈ I,
          (K.biUnion fun k => Z.filter fun x => q k (p i x) ∉ Z).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, K.card * (Finset.univ \ Z).card := by
      apply Finset.sum_le_sum
      intro i _
      calc
        (K.biUnion fun k =>
          Z.filter fun x => q k (p i x) ∉ Z).card ≤
            ∑ k ∈ K, (Z.filter fun x => q k (p i x) ∉ Z).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _k ∈ K, (Finset.univ \ Z).card := by
          apply Finset.sum_le_sum
          intro k _
          exact card_composite_exit_le_deleted (q k) (p i) Z
        _ = K.card * (Finset.univ \ Z).card := by simp only [Finset.sum_const, smul_eq_mul]
    _ = I.card * K.card * (Finset.univ \ Z).card := by
      simp only [Finset.sum_const, smul_eq_mul, Nat.mul_assoc]

noncomputable def sourceWordTestBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) : Finset V := by
  classical
  let T := CompressionCriterion.productTrackedTable F
  exact
    (Finset.univ.biUnion fun i : ι =>
      T.biUnion fun j =>
        Finset.univ.filter fun z => p j (σ i z) ≠ σ i (p j z)) ∪
    (F.biUnion fun j =>
      F.biUnion fun k =>
        Finset.univ.filter fun z => p (j * k) z ≠ p j (p k z)) ∪
    (F.biUnion fun j =>
      F.biUnion fun k =>
        Finset.univ.filter fun z => j ≠ k ∧ p j z = p k z)

theorem sourceCompletionBad_subset_exit_union_wordBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) :
    MatchedComponentCompletion.sourceCompletionBad σ p F Z ⊆
      (Finset.univ.biUnion fun i : ι =>
        Z.filter fun z => σ i z ∉ Z) ∪
      ((CompressionCriterion.productTrackedTable F).biUnion
        fun j => Z.filter fun z => p j z ∉ Z) ∪
      (Finset.univ.biUnion fun i : ι =>
        (CompressionCriterion.productTrackedTable F).biUnion
          fun j => Z.filter fun z => p j (σ i z) ∉ Z) ∪
      sourceWordTestBad σ p F := by
  classical
  intro x hx
  simp only [MatchedComponentCompletion.sourceCompletionBad, ne_eq, Finset.union_assoc,
    Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and, exists_and_left,
      sourceWordTestBad] at hx ⊢
  rcases hx with hgen | hfactor | hcomm | hcomposite | hmul | hsep
  · obtain ⟨hxZ, i, hi⟩ := hgen
    exact Or.inl ⟨hxZ, i, hi⟩
  · obtain ⟨j, hj, hxZ, hexit⟩ := hfactor
    exact Or.inr (Or.inl ⟨j, hj, hxZ, hexit⟩)
  · obtain ⟨i, j, hj, _, hfailure⟩ := hcomm
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, hj, hfailure⟩)))
  · obtain ⟨i, j, hj, hxZ, hfailure⟩ := hcomposite
    exact Or.inr (Or.inr (Or.inl ⟨i, j, hj, hxZ, hfailure⟩))
  · obtain ⟨j, hj, k, hk, _, hfailure⟩ := hmul
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨j, hj, k, hk, hfailure⟩))))
  · obtain ⟨j, hj, k, hk, _, hne, hfailure⟩ := hsep
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨j, hj, k, hk, hne, hfailure⟩))))

theorem card_sourceCompletionBad_le_deleted_add_wordBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) :
    (MatchedComponentCompletion.sourceCompletionBad
      σ p F Z).card ≤
        (Fintype.card ι +
          (CompressionCriterion.productTrackedTable F).card +
          Fintype.card ι *
            (CompressionCriterion.productTrackedTable F).card) *
          (Finset.univ \ Z).card +
        (sourceWordTestBad σ p F).card := by
  classical
  let I : Finset ι := Finset.univ
  let T : Finset J :=
    CompressionCriterion.productTrackedTable F
  let A : Finset V :=
    I.biUnion fun i => Z.filter fun z => σ i z ∉ Z
  let D : Finset V :=
    T.biUnion fun j => Z.filter fun z => p j z ∉ Z
  let C : Finset V :=
    I.biUnion fun i =>
      T.biUnion fun j => Z.filter fun z => p j (σ i z) ∉ Z
  let W : Finset V := sourceWordTestBad σ p F
  let deleted : Finset V := Finset.univ \ Z
  have hA : A.card ≤ Fintype.card ι * deleted.card := by
    simpa only [Finset.card_univ] using card_biUnion_permutation_exit_le (Finset.univ : Finset ι) σ
      Z
  have hD : D.card ≤ T.card * deleted.card := by
    simpa only using card_biUnion_permutation_exit_le T p Z
  have hC : C.card ≤ Fintype.card ι * T.card * deleted.card := by
    simpa only [Finset.card_univ] using card_biUnion_composite_exit_le (Finset.univ : Finset ι) T σ
      p Z
  have hsubset :
      MatchedComponentCompletion.sourceCompletionBad
          σ p F Z ⊆ A ∪ D ∪ C ∪ W := by
    simpa only [Finset.union_assoc] using sourceCompletionBad_subset_exit_union_wordBad σ p F Z
  have hunion :
      (A ∪ D ∪ C ∪ W).card ≤ A.card + D.card + C.card + W.card := by
    have hAD := Finset.card_union_le A D
    have hADC := Finset.card_union_le (A ∪ D) C
    have hADCW := Finset.card_union_le (A ∪ D ∪ C) W
    omega
  calc
    (MatchedComponentCompletion.sourceCompletionBad
        σ p F Z).card ≤ (A ∪ D ∪ C ∪ W).card :=
      Finset.card_le_card hsubset
    _ ≤ A.card + D.card + C.card + W.card := hunion
    _ ≤ Fintype.card ι * deleted.card +
        T.card * deleted.card +
        Fintype.card ι * T.card * deleted.card + W.card := by
      omega
    _ = (Fintype.card ι +
          (CompressionCriterion.productTrackedTable F).card +
          Fintype.card ι *
            (CompressionCriterion.productTrackedTable F).card) *
          (Finset.univ \ Z).card +
        (sourceWordTestBad σ p F).card := by
      dsimp [T, deleted, W]
      ring

theorem sourceCompletionBad_subset_survivors
    {V ι J : Type*} [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) :
    MatchedComponentCompletion.sourceCompletionBad
      σ p F Z ⊆ Z := by
  classical
  intro x hx
  simp only [MatchedComponentCompletion.sourceCompletionBad, ne_eq, Finset.union_assoc,
    Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and, exists_and_left] at hx
  aesop

theorem sourceCompletionBad_original_density_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (B : (n : ℕ) → Finset (V n))
    (hdeleted : Tendsto
      (fun n => ((B n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0))
    (hword : Tendsto
      (fun n =>
        ((sourceWordTestBad (σ n) (p n) F).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((MatchedComponentCompletion.sourceCompletionBad
          (σ n) (p n) F (Finset.univ \ B n)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
  let c : ℝ :=
    (Fintype.card ι +
      (CompressionCriterion.productTrackedTable F).card +
      Fintype.card ι *
        (CompressionCriterion.productTrackedTable F).card : ℕ)
  have hupper (n : ℕ) :
      ((MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (Finset.univ \ B n)).card : ℝ) /
          Fintype.card (V n) ≤
        c * (((B n).card : ℝ) / Fintype.card (V n)) +
          ((sourceWordTestBad (σ n) (p n) F).card : ℝ) /
            Fintype.card (V n) := by
    have hfinite := card_sourceCompletionBad_le_deleted_add_wordBad
      (σ n) (p n) F (Finset.univ \ B n)
    have hdeleted_eq :
        (Finset.univ \ (Finset.univ \ B n) : Finset (V n)) = B n := by
      ext x
      simp only [sdiff_sdiff_right_self, Finset.subset_univ, inf_of_le_right]
    rw [hdeleted_eq] at hfinite
    have hreal :
        ((MatchedComponentCompletion.sourceCompletionBad
          (σ n) (p n) F (Finset.univ \ B n)).card : ℝ) ≤
            c * ((B n).card : ℝ) +
              (sourceWordTestBad (σ n) (p n) F).card := by
      dsimp [c]
      exact_mod_cast hfinite
    calc
      ((MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (Finset.univ \ B n)).card : ℝ) /
          Fintype.card (V n) ≤
          (c * ((B n).card : ℝ) +
            (sourceWordTestBad (σ n) (p n) F).card) /
              Fintype.card (V n) :=
            div_le_div_of_nonneg_right hreal (by positivity)
      _ = c * (((B n).card : ℝ) / Fintype.card (V n)) +
          ((sourceWordTestBad (σ n) (p n) F).card : ℝ) /
            Fintype.card (V n) := by
          ring
  have hlimit : Tendsto
      (fun n =>
        c * (((B n).card : ℝ) / Fintype.card (V n)) +
          ((sourceWordTestBad (σ n) (p n) F).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using (hdeleted.const_mul c).add hword
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun n => by positivity)
    (Filter.Eventually.of_forall hupper)
    hlimit

theorem sourceCompletionBad_surviving_density_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (B : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Finset.univ \ B n : Finset (V n)).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((B n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0))
    (hword : Tendsto
      (fun n =>
        ((sourceWordTestBad (σ n) (p n) F).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((MatchedComponentCompletion.sourceCompletionBad
          (σ n) (p n) F (Finset.univ \ B n)).card : ℝ) /
            (Finset.univ \ B n : Finset (V n)).card)
      atTop (nhds 0) := by
  let U : (n : ℕ) → Finset (V n) := fun _ => Finset.univ
  let Z : (n : ℕ) → Finset (V n) := fun n => Finset.univ \ B n
  let E : (n : ℕ) → Finset (V n) := fun n =>
    MatchedComponentCompletion.sourceCompletionBad
      (σ n) (p n) F (Z n)
  have hU (n : ℕ) : (U n).Nonempty := by
    obtain ⟨x, _⟩ := hZ n
    exact ⟨x, Finset.mem_univ _⟩
  have hcover : Tendsto
      (fun n => ((Z n).card : ℝ) / (U n).card)
      atTop (nhds 1) := by
    have hbase : Tendsto
        (fun n => (1 : ℝ) -
          ((B n).card : ℝ) / Fintype.card (V n))
        atTop (nhds 1) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hdeleted
    convert hbase using 1
    funext n
    have hcard : Fintype.card (V n) ≠ 0 := by
      exact Finset.card_ne_zero.mpr (hU n)
    dsimp [U, Z]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ (B n)),
      Finset.card_univ, Nat.cast_sub (Finset.card_le_univ (B n))]
    field_simp
  have hglobal : Tendsto
      (fun n => (((U n ∩ E n).card : ℝ) / (U n).card))
      atTop (nhds 0) := by
    simpa [U, Z, E] using
      sourceCompletionBad_original_density_tendsto_zero
        V σ p F B hdeleted hword
  have hretained := retained_bad_density_tendsto_zero
    U Z E hU hZ
    (fun n => Finset.subset_univ (Z n)) hcover hglobal
  convert hretained using 1
  funext n
  dsimp [Z, E]
  rw [Finset.inter_eq_right.mpr
    (sourceCompletionBad_subset_survivors
      (σ n) (p n) F (Finset.univ \ B n))]

theorem pruned_component_card_tendsto_atTop
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (B : (n : ℕ) → Finset (V n))
    (hsize : Tendsto (fun n => Fintype.card (V n)) atTop atTop)
    (hdeleted : Tendsto
      (fun n => ((B n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto (fun n => (Finset.univ \ B n : Finset (V n)).card)
      atTop atTop := by
  have hhalf : ∀ᶠ n in atTop,
      ((B n).card : ℝ) / Fintype.card (V n) < (1 / 2 : ℝ) :=
    hdeleted.eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hpositive : ∀ᶠ n in atTop, 0 < Fintype.card (V n) := by
    have hevent := (Filter.tendsto_atTop.1 hsize) 1
    filter_upwards [hevent] with n hn
    omega
  have hhalfsize :
      Tendsto (fun n => Fintype.card (V n) / 2) atTop atTop :=
    (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hsize
  refine tendsto_atTop_mono' atTop ?_ hhalfsize
  filter_upwards [hhalf, hpositive] with n hn hnpositive
  have hrealpos : (0 : ℝ) < Fintype.card (V n) := by
    exact_mod_cast hnpositive
  have hratio := (div_lt_iff₀ hrealpos).1 hn
  have hbadlt : 2 * (B n).card < Fintype.card (V n) := by
    exact_mod_cast (show
      (2 : ℝ) * (B n).card < Fintype.card (V n) by linarith)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ (B n)),
    Finset.card_univ]
  omega

end MatchedComponentExitBudget

namespace KunRealComplexMarkovBridge

open scoped BigOperators ComplexOrder InnerProductSpace Topology

def realMarkov {ι V : Type*} [Fintype ι]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (x : V) : ℝ :=
  (∑ i, f ((p i).symm x)) / (Fintype.card ι : ℝ)

def permutationUnitary {V : Type*} [Fintype V] (p : Equiv.Perm V) :
    EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ p

def indicatorVector {V : Type*}
    (f : V → ℝ) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 fun x => (f x : ℂ)

@[simp]
theorem indicatorVector_apply {V : Type*}
    (f : V → ℝ) (x : V) :
    indicatorVector f x = (f x : ℂ) := rfl

def permutationMarkov {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (ξ : EuclideanSpace ℂ V) :
    EuclideanSpace ℂ V :=
  (Fintype.card ι : ℂ)⁻¹ • ∑ i, permutationUnitary (p i) ξ

@[simp]
theorem permutationMarkov_apply {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (ξ : EuclideanSpace ℂ V) (x : V) :
    permutationMarkov p ξ x =
      (∑ i, ξ ((p i).symm x)) / (Fintype.card ι : ℂ) := by
  simp only [permutationMarkov, permutationUnitary, PiLp.smul_apply, WithLp.ofLp_sum,
    LinearIsometryEquiv.piLpCongrLeft_apply, Finset.sum_apply, Equiv.piCongrLeft'_apply,
      smul_eq_mul, div_eq_mul_inv,
    mul_comm]

theorem indicatorVector_realMarkov
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    indicatorVector (realMarkov p f) =
      permutationMarkov p (indicatorVector f) := by
  ext x
  rw [indicatorVector_apply, permutationMarkov_apply]
  simp only [indicatorVector_apply]
  change (((∑ i, f ((p i).symm x)) /
    (Fintype.card ι : ℝ) : ℝ) : ℂ) =
      (∑ i, (f ((p i).symm x) : ℂ)) / (Fintype.card ι : ℂ)
  norm_cast

theorem indicatorVector_iterate_realMarkov
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (k : ℕ) :
    indicatorVector (((realMarkov p)^[k]) f) =
      ((permutationMarkov p)^[k]) (indicatorVector f) := by
  induction k with
  | zero => simp only [Function.iterate_zero, id_eq]
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        indicatorVector_realMarkov, ih]

theorem norm_indicatorVector_sub_sq
    {V : Type*} [Fintype V] (f g : V → ℝ) :
    ‖indicatorVector f - indicatorVector g‖ ^ 2 =
      ∑ x, (f x - g x) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  change ‖(f x : ℂ) - (g x : ℂ)‖ ^ 2 = (f x - g x) ^ 2
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_permutationMarkov_indicator_sub_sq
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    ‖permutationMarkov p (indicatorVector f) - indicatorVector f‖ ^ 2 =
      ∑ x, (realMarkov p f x - f x) ^ 2 := by
  rw [← indicatorVector_realMarkov, norm_indicatorVector_sub_sq]

theorem norm_iterate_permutationMarkov_indicator_sub_sq
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (k : ℕ) :
    ‖((permutationMarkov p)^[k]) (indicatorVector f) -
        indicatorVector f‖ ^ 2 =
      ∑ x, ((((realMarkov p)^[k]) f) x - f x) ^ 2 := by
  rw [← indicatorVector_iterate_realMarkov,
    norm_indicatorVector_sub_sq]

theorem norm_iterate_permutationMarkov_indicator_sub_iterate_sq
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (k : ℕ) :
    ‖((permutationMarkov p)^[k + 1]) (indicatorVector f) -
        ((permutationMarkov p)^[k]) (indicatorVector f)‖ ^ 2 =
      ∑ x, ((((realMarkov p)^[k + 1]) f) x -
        (((realMarkov p)^[k]) f) x) ^ 2 := by
  rw [← indicatorVector_iterate_realMarkov,
    ← indicatorVector_iterate_realMarkov,
    norm_indicatorVector_sub_sq]

end KunRealComplexMarkovBridge


end SoficGroups

end
