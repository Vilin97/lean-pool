/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.HeckeTheta

/-!
# The normalised class theta and its clean functional equation  (SP1-AGE-4, bricks 2–3)

The unit-averaged Hecke theta `heckeG I t` of `HeckeTheta.lean` depends on the ideal `I`,
not just its class: `g_{x·I}(t) = g_I(|N(x)|²·t)` (`heckeG_principal_mul`). Normalising the
ray parameter by `N(I)⁻²·β` with `β = 4^{r₂}/|Δ_K|` kills that dependence:

* `heckeGClass C x` — the **normalised class theta** `Ĝ_C(x) = g_I(N(I)⁻²·β·x)`, attached
  to an ideal class `C` through any representative (`heckeGClass_eq`);
* `heckeGClass_inversion` — the **clean Hecke symmetry** `Ĝ_C(1/x) = √x·Ĝ_{C^∨}(x)`, where
  `C^∨ = [𝔡_K⁻¹]·C⁻¹` is the trace-dual class: with this `β` the covolume, norm and
  `4^{2r₂}` factors of `heckeG_inversion` cancel to **exactly 1**;
* `heckeF x = ∑_C Ĝ_C(x)` — the total theta, with `heckeF_inversion : f(1/x) = √x·f(x)`,
  the input to mathlib's abstract functional-equation machinery (`WeakFEPair`, weight
  `k = 1/2`, root number `ε = 1`) producing the completed Dedekind zeta function.

Supporting material: the general fraction-field version of `ClassGroup.mk_eq_mk`
(`classGroup_mk_eq_mk_iff`), the real ideal norm `idealNormR` and its behaviour under
principal rescaling and trace duality, and the class-group bijection `dualClass`.
-/

namespace DedekindResidue

@[expose] public section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
open FractionalIdeal (spanSingleton)
open scoped nonZeroDivisors Real

variable (K : Type*) [Field K] [NumberField K]


/-- Two invertible fractional ideals lie in the same ideal class iff they differ by a
principal fractional ideal (general fraction field version of `ClassGroup.mk_eq_mk`,
via `ClassGroup.mk_eq_one_iff`). -/
theorem classGroup_mk_eq_mk_iff {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    ClassGroup.mk K I = ClassGroup.mk K J
      ↔ ∃ x : Kˣ, toPrincipalIdeal (𝓞 K) K x * I = J := by
  constructor
  · intro h
    have h1 : ClassGroup.mk K (J * I⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    obtain ⟨x, hx⟩ := (ClassGroup.mk_eq_one_iff.mp h1).principal
    have hxne : x ≠ 0 := by
      rintro rfl
      have : ((J * I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
          = (0 : FractionalIdeal (𝓞 K)⁰ K) := by
        apply FractionalIdeal.coeToSubmodule_injective
        change ((↑(J * I⁻¹) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
          = ((0 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
        rw [FractionalIdeal.coe_zero, hx, Submodule.span_zero_singleton]
      exact Units.ne_zero _ this
    have hspan : toPrincipalIdeal (𝓞 K) K (Units.mk0 x hxne) = J * I⁻¹ := by
      rw [← Units.val_inj, coe_toPrincipalIdeal]
      apply FractionalIdeal.coeToSubmodule_injective
      change ((spanSingleton (𝓞 K)⁰ x : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
        = ((↑(J * I⁻¹) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
      rw [FractionalIdeal.coe_spanSingleton, hx]
    exact ⟨Units.mk0 x hxne, by rw [hspan, inv_mul_cancel_right]⟩
  · rintro ⟨x, rfl⟩
    rw [map_mul]
    have h1 : ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K x) = 1 := by
      rw [ClassGroup.mk_eq_one_iff]
      exact ⟨⟨(x : K), by rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]⟩⟩
    rw [h1, one_mul]

/-- The units-inverse of an invertible fractional ideal is the fractional-ideal inverse. -/
theorem val_unit_inv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- The real absolute norm of an invertible fractional ideal. -/
noncomputable def idealNormR (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ)

theorem absNorm_unit_ne_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  have h1 : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K)
      * FractionalIdeal.absNorm ((I : FractionalIdeal (𝓞 K)⁰ K))⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (Units.ne_zero I), FractionalIdeal.absNorm_one]
  exact left_ne_zero_of_mul_eq_one h1

theorem idealNormR_pos (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : 0 < idealNormR K I := by
  rw [idealNormR, Rat.cast_pos]
  exact lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _)
    (Ne.symm (absNorm_unit_ne_zero K I))

theorem idealNormR_principal_mul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : Kˣ) :
    idealNormR K (toPrincipalIdeal (𝓞 K) K y * I)
      = ((|Algebra.norm ℚ (y : K)| : ℚ) : ℝ) * idealNormR K I := by
  rw [idealNormR, idealNormR, Units.val_mul, map_mul, coe_toPrincipalIdeal,
    FractionalIdeal.absNorm_span_singleton, Rat.cast_mul]

/-- The Hecke normalisation constant `β = 4^{r₂}/|Δ_K|`. -/
noncomputable def heckeBeta : ℝ := 4 ^ nrComplexPlaces K / ((discr K).natAbs : ℝ)

theorem natAbs_discr_pos : (0 : ℝ) < ((discr K).natAbs : ℝ) := by
  have h := discr_ne_zero K
  exact_mod_cast Nat.pos_of_ne_zero (fun hc => h (Int.natAbs_eq_zero.mp hc))

theorem heckeBeta_pos : 0 < heckeBeta K := by
  rw [heckeBeta]
  have := natAbs_discr_pos K
  positivity

open scoped Classical in
/-- The normalised theta value `g_I(N(I)⁻²·β·x)` depends only on the ideal class of `I`. -/
theorem heckeG_normalized_eq_of_mk_eq {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K I = ClassGroup.mk K J) {x : ℝ} (hx : 0 ≤ x) :
    heckeG K I ((idealNormR K I)⁻¹ ^ 2 * heckeBeta K * x)
      = heckeG K J ((idealNormR K J)⁻¹ ^ 2 * heckeBeta K * x) := by
  obtain ⟨y, rfl⟩ := (classGroup_mk_eq_mk_iff K).mp h
  have hbeta := heckeBeta_pos K
  have hIpos := idealNormR_pos K I
  rw [heckeG_principal_mul K I y (by positivity), idealNormR_principal_mul]
  congr 1
  have hy : ((|Algebra.norm ℚ (y : K)| : ℚ) : ℝ) ≠ 0 := by
    rw [Rat.cast_ne_zero, abs_ne_zero]
    exact Algebra.norm_ne_zero_iff.mpr (Units.ne_zero y)
  field_simp

open scoped Classical in
/-- A choice of invertible-fractional-ideal representative for each ideal class. -/
noncomputable def classRep (C : ClassGroup (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K ((ClassGroup.mk0_surjective C).choose)

theorem mk_classRep (C : ClassGroup (𝓞 K)) : ClassGroup.mk K (classRep K C) = C := by
  rw [classRep, ClassGroup.mk_mk0]
  exact (ClassGroup.mk0_surjective C).choose_spec

open scoped Classical in
/-- **The normalised class theta** `Ĝ_C(x) = g_I(N(I)⁻²·β·x)` for any representative `I`
of the class `C` (well-defined by `heckeG_normalized_eq_of_mk_eq`). -/
noncomputable def heckeGClass (C : ClassGroup (𝓞 K)) (x : ℝ) : ℝ :=
  heckeG K (classRep K C)
    ((idealNormR K (classRep K C))⁻¹ ^ 2 * heckeBeta K * x)

open scoped Classical in
theorem heckeGClass_eq {C : ClassGroup (𝓞 K)} (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : ClassGroup.mk K I = C) {x : ℝ} (hx : 0 ≤ x) :
    heckeGClass K C x = heckeG K I ((idealNormR K I)⁻¹ ^ 2 * heckeBeta K * x) := by
  rw [heckeGClass]
  exact heckeG_normalized_eq_of_mk_eq K (by rw [mk_classRep, ← h]) hx

/-- `dualIdealUnit` factors as the dual of `1` times the inverse. -/
theorem dualIdealUnit_eq_mul_inv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualIdealUnit K I = dualIdealUnit K 1 * I⁻¹ := by
  rw [← Units.val_inj, Units.val_mul]
  change FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)
    = FractionalIdeal.dual ℤ ℚ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K)
  rw [val_unit_inv, Units.val_one, FractionalIdeal.dual_eq_mul_inv]

/-- The map on classes induced by the trace dual. -/
noncomputable def dualClass (C : ClassGroup (𝓞 K)) : ClassGroup (𝓞 K) :=
  ClassGroup.mk K (dualIdealUnit K 1) * C⁻¹

theorem mk_dualIdealUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk K (dualIdealUnit K I) = dualClass K (ClassGroup.mk K I) := by
  rw [dualIdealUnit_eq_mul_inv, map_mul, map_inv, dualClass]

/-- `dualClass` is a bijection of the (finite) class group. -/
theorem dualClass_bijective : Function.Bijective (dualClass K) := by
  have : dualClass K = (fun C => ClassGroup.mk K (dualIdealUnit K 1) * C) ∘ (fun C => C⁻¹) := by
    funext C
    simp [dualClass]
  rw [this]
  exact ((Equiv.inv (ClassGroup (𝓞 K))).trans
    (Equiv.mulLeft (ClassGroup.mk K (dualIdealUnit K 1)))).bijective

open scoped Classical in
theorem idealNormR_dualIdealUnit (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    idealNormR K (dualIdealUnit K I)
      = (idealNormR K I)⁻¹ * (((discr K).natAbs : ℝ))⁻¹ := by
  rw [idealNormR, idealNormR, absNorm_dualIdealUnit]
  push_cast
  ring

open scoped Classical in
/-- **The clean Hecke symmetry of the normalised class theta**:
`Ĝ_C(1/x) = √x · Ĝ_{C^∨}(x)` — the normalisation `β = 4^{r₂}/|Δ|` makes the coefficient
exactly `1`. -/
theorem heckeGClass_inversion (C : ClassGroup (𝓞 K)) {x : ℝ} (hx : 0 < x) :
    heckeGClass K C (1 / x) = Real.sqrt x * heckeGClass K (dualClass K C) x := by
  have hNpos := idealNormR_pos K (classRep K C)
  have hβ := heckeBeta_pos K
  have hD := natAbs_discr_pos K
  rw [heckeGClass, heckeG_inversion K (classRep K C) (by positivity),
    heckeGClass_eq K (dualIdealUnit K (classRep K C))
      (by rw [mk_dualIdealUnit, mk_classRep]) hx.le,
    covolume_idealZLattice]
  have hDD : |((discr K : ℤ) : ℝ)| = (((discr K).natAbs : ℕ) : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have hA : (4 : ℝ) ^ (2 * nrComplexPlaces K)
        * ((idealNormR K (classRep K C))⁻¹ ^ 2 * heckeBeta K * (1 / x))⁻¹
      = (idealNormR K (dualIdealUnit K (classRep K C)))⁻¹ ^ 2 * heckeBeta K * x := by
    rw [idealNormR_dualIdealUnit, heckeBeta]
    field_simp
    ring
  rw [hA]
  have hsq : (idealNormR K (classRep K C))⁻¹ ^ 2 * heckeBeta K
      = ((idealNormR K (classRep K C))⁻¹ * 2 ^ nrComplexPlaces K
          / Real.sqrt (((discr K).natAbs : ℕ) : ℝ)) ^ 2 := by
    rw [heckeBeta, div_pow, mul_pow, Real.sq_sqrt hD.le, ← pow_mul,
      show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm (nrComplexPlaces K) 2,
      mul_div_assoc]
  have hmid : (Real.sqrt ((idealNormR K (classRep K C))⁻¹ ^ 2 * heckeBeta K * (1 / x)))⁻¹
      = (idealNormR K (classRep K C) * Real.sqrt (((discr K).natAbs : ℕ) : ℝ)
          / 2 ^ nrComplexPlaces K) * Real.sqrt x := by
    rw [Real.sqrt_mul (by positivity), hsq, Real.sqrt_sq (by positivity),
      one_div, Real.sqrt_inv, mul_inv, inv_inv]
    have h2 : (0:ℝ) < 2 ^ nrComplexPlaces K := by positivity
    have hsD : (0:ℝ) < Real.sqrt (((discr K).natAbs : ℕ) : ℝ) := Real.sqrt_pos.mpr hD
    field_simp
  rw [hmid, hDD]
  have hsD : (0:ℝ) < Real.sqrt (((discr K).natAbs : ℕ) : ℝ) := Real.sqrt_pos.mpr hD
  have h2 : (0:ℝ) < (2:ℝ) ^ nrComplexPlaces K := by positivity
  field_simp
  have hfold : ((FractionalIdeal.absNorm ((classRep K C : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) = idealNormR K (classRep K C) := rfl
  rw [hfold]
  have h12 : ((1:ℝ)/2) ^ nrComplexPlaces K * 2 ^ nrComplexPlaces K = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination (-(idealNormR K (classRep K C) * heckeG K (dualIdealUnit K (classRep K C))
    (heckeBeta K * x / idealNormR K (dualIdealUnit K (classRep K C)) ^ 2))) * h12

open scoped Classical in
/-- The total normalised theta: the sum of the class thetas over the (finite) class group.
This is the `f` of the abstract functional-equation pair for `Λ_K`. -/
noncomputable def heckeF (x : ℝ) : ℝ := ∑ C : ClassGroup (𝓞 K), heckeGClass K C x

open scoped Classical in
/-- **Hecke symmetry of the total theta**: `f(1/x) = √x · f(x)` — summing the class
inversion over the class group, along the `dualClass` bijection. -/
theorem heckeF_inversion {x : ℝ} (hx : 0 < x) :
    heckeF K (1 / x) = Real.sqrt x * heckeF K x := by
  rw [heckeF, heckeF, Finset.mul_sum,
    Finset.sum_congr rfl (fun C _ => heckeGClass_inversion K C hx)]
  exact Fintype.sum_bijective (dualClass K) (dualClass_bijective K) _ _ (fun C => rfl)

end

end DedekindResidue
