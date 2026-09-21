/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseInterface

/-!
# Reflection of sparse bounds

Reflection preserves the test-function class, interval lengths, sparsity, and local averages.
These identities transfer sparse estimates between an operator and its reflected counterpart.
-/

open Function MeasureTheory Set
open scoped ENNReal Topology ComplexConjugate

namespace QuadraticCarleson


namespace L0Infinity

/-- Reflection of a bounded, compactly supported test function about the origin. -/
def reflect (f : L0Infinity) : L0Infinity where
  toFun := fun x ↦ f (-x)
  measurable_toFun := f.measurable_toFun.comp measurable_neg
  bounded_toFun := by
    obtain ⟨C, hC⟩ := f.bounded_toFun
    exact ⟨C, fun x ↦ hC (-x)⟩
  hasCompactSupport_toFun := f.hasCompactSupport_toFun.comp_homeomorph (Homeomorph.neg ℝ)

@[simp] theorem reflect_apply (f : L0Infinity) (x : ℝ) : reflect f x = f (-x) := rfl

@[simp] theorem reflect_reflect (f : L0Infinity) : reflect (reflect f) = f := by
  cases f
  simp [reflect]

end L0Infinity

namespace RealInterval

/-- Reflection of an interval about the origin, with the endpoint order reversed. -/
def reflect (I : RealInterval) : RealInterval :=
  ⟨-I.right, -I.left, neg_lt_neg I.left_lt_right⟩

@[simp] theorem reflect_left (I : RealInterval) : I.reflect.left = -I.right := rfl
@[simp] theorem reflect_right (I : RealInterval) : I.reflect.right = -I.left := rfl
@[simp] theorem reflect_reflect (I : RealInterval) : I.reflect.reflect = I := by
  cases I
  simp [reflect]

@[simp] theorem reflect_length (I : RealInterval) : I.reflect.length = I.length := by
  simp [length, reflect]
  ring

theorem reflect_injective : Injective reflect :=
  (show Involutive reflect from reflect_reflect).injective

/-- Half-open endpoints flip under reflection; the carriers agree after
reflection outside their two null endpoints. -/
theorem preimage_neg_reflect_carrier_ae (I : RealInterval) :
    (fun x : ℝ ↦ -x) ⁻¹' I.reflect.carrier =ᵐ[volume] I.carrier := by
  have heq : (fun x : ℝ ↦ -x) ⁻¹' I.reflect.carrier = Ico I.left I.right := by
    ext x
    change (-I.right < -x ∧ -x ≤ -I.left) ↔ (I.left ≤ x ∧ x < I.right)
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [heq]
  exact Ico_ae_eq_Ioc

end RealInterval

namespace KrauseLaceySparseReflection

/-- The interval family pulled back under reflection. -/
def reflectedFamily (S : Set RealInterval) : Set RealInterval := RealInterval.reflect ⁻¹' S

@[simp] theorem reflectedFamily_reflectedFamily (S : Set RealInterval) :
    reflectedFamily (reflectedFamily S) = S := by
  ext I
  simp [reflectedFamily]

/-- The index equivalence between a reflected interval family and the original family. -/
def reflectedIndexEquiv (S : Set RealInterval) :
    {I : RealInterval // I ∈ reflectedFamily S} ≃ {I : RealInterval // I ∈ S} where
  toFun I := ⟨I.1.reflect, I.2⟩
  invFun I := ⟨I.1.reflect, by simp [reflectedFamily]⟩
  left_inv I := by ext; simp
  right_inv I := by ext; simp

/-- Reflection preserves the exact sparse parameter. Removing one endpoint
from each reflected major subset reconciles the project's `Ioc` convention. -/
theorem isSparse_reflectedFamily {η : ℝ} {S : Set RealInterval} (hS : IsSparse η S) :
    IsSparse η (reflectedFamily S) := by
  rcases hS with ⟨hη, hη1, E, hEm, hEs, hEd, hEv⟩
  let e := reflectedIndexEquiv S
  let F : {I : RealInterval // I ∈ reflectedFamily S} → Set ℝ :=
    fun I ↦ (fun x : ℝ ↦ -x) ⁻¹' E (e I) \ {I.1.left}
  refine ⟨hη, hη1, F, ?_, ?_, ?_, ?_⟩
  · intro I
    exact ((hEm (e I)).preimage measurable_neg).diff (measurableSet_singleton _)
  · intro I x hx
    have hxE := hEs (e I) hx.1
    change -I.1.right < -x ∧ -x ≤ -I.1.left at hxE
    change I.1.left < x ∧ x ≤ I.1.right
    have hxne : x ≠ I.1.left := hx.2
    exact ⟨lt_of_le_of_ne (by linarith) hxne.symm, by linarith⟩
  · intro I J hIJ
    apply Disjoint.mono sdiff_subset sdiff_subset
    exact (hEd (e.injective.ne hIJ)).preimage _
  · intro I
    have hv : volume (F I) = volume (E (e I)) := by
      change volume ((fun x : ℝ ↦ -x) ⁻¹' E (e I) \ {I.1.left}) = _
      rw [measure_sdiff_null (measure_singleton _)]
      exact (Measure.measurePreserving_neg volume).measure_preimage (hEm (e I)).nullMeasurableSet
    rw [hv]
    have hh := hEv (e I)
    change η * I.1.reflect.length ≤ (volume (E (e I))).toReal at hh
    simpa only [RealInterval.reflect_length] using hh

theorem isSparse_reflectedFamily_iff {η : ℝ} {S : Set RealInterval} :
    IsSparse η (reflectedFamily S) ↔ IsSparse η S := by
  constructor
  · intro h
    simpa using isSparse_reflectedFamily h
  · exact isSparse_reflectedFamily

theorem localAverage_reflect (p : ℝ) (f : ℝ → ℂ) (I : RealInterval) :
    localAverage p (fun x ↦ f (-x)) I.reflect = localAverage p f I := by
  unfold localAverage
  rw [RealInterval.reflect_length]
  congr 2
  rw [RealInterval.carrier, ← intervalIntegral.integral_of_le I.reflect.left_lt_right.le]
  change (∫ x in I.reflect.left..I.reflect.right, (fun y ↦ ‖f y‖ ^ p) (-x)) = _
  rw [intervalIntegral.integral_comp_neg (fun y : ℝ ↦ ‖f y‖ ^ p)]
  simp only [RealInterval.reflect_right, RealInterval.reflect_left, neg_neg]
  exact intervalIntegral.integral_of_le I.left_lt_right.le

theorem sparseForm_reflectedFamily (p : ℝ) (f g : ℝ → ℂ) (S : Set RealInterval) :
    sparseForm p f g (reflectedFamily S) =
      sparseForm p (fun x ↦ f (-x)) (fun x ↦ g (-x)) S := by
  unfold sparseForm
  rw [← (reflectedIndexEquiv S).tsum_eq]
  congr 1
  funext I
  change ENNReal.ofReal (I.1.length * localAverage 1 f I.1 * localAverage p g I.1) =
    ENNReal.ofReal (I.1.reflect.length * localAverage 1 (fun x ↦ f (-x)) I.1.reflect *
      localAverage p (fun x ↦ g (-x)) I.1.reflect)
  rw [RealInterval.reflect_length, localAverage_reflect, localAverage_reflect]

/-- Transport of a test operator by reflection of its input and output coordinates. -/
def reflectedOperator (T : TestOperator) : TestOperator :=
  fun f x ↦ T (L0Infinity.reflect f) (-x)

@[simp] theorem reflectedOperator_reflectedOperator (T : TestOperator) :
    reflectedOperator (reflectedOperator T) = T := by
  funext f x
  simp [reflectedOperator]

theorem operatorPairing_reflectedOperator (T : TestOperator) (f g : L0Infinity) :
    operatorPairing (reflectedOperator T) f g =
      operatorPairing T (L0Infinity.reflect f) (L0Infinity.reflect g) := by
  unfold operatorPairing reflectedOperator
  have h := integral_neg_eq_self (fun x ↦ T (L0Infinity.reflect f) x * star (g (-x))) volume
  simpa only [neg_neg, L0Infinity.reflect_apply] using h

/-- Sparse bounds pass to reflection without any loss in their constant
or their `1/4` sparseness parameter. -/
theorem hasSparseOnePBound_reflectedOperator {C p : ℝ} {T : TestOperator}
    (hT : HasSparseOnePBound C p T) : HasSparseOnePBound C p (reflectedOperator T) := by
  intro f g
  obtain ⟨S, hS, hbound⟩ := hT (L0Infinity.reflect f) (L0Infinity.reflect g)
  refine ⟨reflectedFamily S, isSparse_reflectedFamily hS, ?_⟩
  rw [operatorPairing_reflectedOperator, sparseForm_reflectedFamily]
  exact hbound

theorem hasSparseOnePBound_reflectedOperator_iff {C p : ℝ} {T : TestOperator} :
    HasSparseOnePBound C p (reflectedOperator T) ↔ HasSparseOnePBound C p T := by
  constructor
  · intro h
    simpa using hasSparseOnePBound_reflectedOperator h
  · exact hasSparseOnePBound_reflectedOperator

theorem sparseOnePNorm_reflectedOperator (p : ℝ) (T : TestOperator) :
    sparseOnePNorm p (reflectedOperator T) = sparseOnePNorm p T := by
  simp only [sparseOnePNorm, hasSparseOnePBound_reflectedOperator_iff]

/-- Two sparse bounds are combined by choosing the family with the larger
sparse form. The chosen family retains its original density parameter. -/
theorem hasSparseOnePBound_of_pairing_le_add
    {C D p : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) {T V U : TestOperator}
    (hT : HasSparseOnePBound C p T) (hV : HasSparseOnePBound D p V)
    (hU : ∀ f g : L0Infinity,
      ‖operatorPairing U f g‖ ≤ ‖operatorPairing T f g‖ + ‖operatorPairing V f g‖) :
    HasSparseOnePBound (C + D) p U := by
  intro f g
  obtain ⟨S, hS, hbS⟩ := hT f g
  obtain ⟨R, hR, hbR⟩ := hV f g
  have hbound : ENNReal.ofReal ‖operatorPairing U f g‖ ≤
      ENNReal.ofReal C * sparseForm p f g S + ENNReal.ofReal D * sparseForm p f g R := by
    apply (ENNReal.ofReal_le_ofReal (hU f g)).trans
    rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact add_le_add hbS hbR
  rcases le_total (sparseForm p f g S) (sparseForm p f g R) with hSR | hRS
  · refine ⟨R, hR, hbound.trans ?_⟩
    rw [ENNReal.ofReal_add hC hD, add_mul]
    exact add_le_add (mul_le_mul' le_rfl hSR) le_rfl
  · refine ⟨S, hS, hbound.trans ?_⟩
    rw [ENNReal.ofReal_add hC hD, add_mul]
    exact add_le_add le_rfl (mul_le_mul' le_rfl hRS)

/-- The difference between an operator and its reflected operator. -/
def reflectionDifference (T : TestOperator) : TestOperator :=
  fun f x ↦ T f x - reflectedOperator T f x

/-- The actual odd difference has sparse constant at most `2C`. The
integrability premise makes subtraction of the two Bochner pairings valid. -/
theorem hasSparseOnePBound_reflectionDifference
    {C p : ℝ} (hC : 0 ≤ C) {T : TestOperator} (hT : HasSparseOnePBound C p T)
    (hTi : ∀ f g : L0Infinity, Integrable (fun x ↦ T f x * star (g x))) :
    HasSparseOnePBound (2 * C) p (reflectionDifference T) := by
  have hR := hasSparseOnePBound_reflectedOperator hT
  have h := hasSparseOnePBound_of_pairing_le_add hC hC hT hR
    (U := reflectionDifference T) ?_
  · simpa only [two_mul] using h
  intro f g
  have hRi : Integrable (fun x ↦ reflectedOperator T f x * star (g x)) := by
    have hi := (hTi (L0Infinity.reflect f) (L0Infinity.reflect g)).comp_neg
    simpa only [reflectedOperator, L0Infinity.reflect_apply, neg_neg] using hi
  have heq : operatorPairing (reflectionDifference T) f g =
      operatorPairing T f g - operatorPairing (reflectedOperator T) f g := by
    simp only [operatorPairing, reflectionDifference, sub_mul]
    exact integral_sub (hTi f g) hRi
  rw [heq]
  exact norm_sub_le _ _


/-- The pointwise norm of a test function, embedded back into the complex test-function class. -/
noncomputable def normInput (g : L0Infinity) : L0Infinity where
  toFun := fun x ↦ (‖g x‖ : ℂ)
  measurable_toFun := Complex.measurable_ofReal.comp g.measurable_toFun.norm
  bounded_toFun := by
    obtain ⟨C, hC⟩ := g.bounded_toFun
    exact ⟨C, fun x ↦ by simpa using hC x⟩
  hasCompactSupport_toFun := by
    exact g.hasCompactSupport_toFun.comp_left (g := fun z : ℂ ↦ (‖z‖ : ℂ)) (by simp)

theorem localAverage_normInput (p : ℝ) (g : L0Infinity) (I : RealInterval) :
    localAverage p (normInput g) I = localAverage p g I := by
  simp [localAverage, normInput]

theorem sparseForm_normInput (p : ℝ) (f : ℝ → ℂ) (g : L0Infinity) (S : Set RealInterval) :
    sparseForm p f (normInput g) S = sparseForm p f g S := by
  simp only [sparseForm, localAverage_normInput]

theorem norm_operatorPairing_absolute_normInput (T : TestOperator) (f g : L0Infinity) :
    ‖operatorPairing (absoluteValueOperator T) f (normInput g)‖ =
      ∫ x, ‖T f x‖ * ‖g x‖ := by
  have heq : operatorPairing (absoluteValueOperator T) f (normInput g) =
      ((∫ x, ‖T f x‖ * ‖g x‖ : ℝ) : ℂ) := by
    simp only [operatorPairing, absoluteValueOperator, normInput, Complex.star_def,
      Complex.conj_ofReal, ← Complex.ofReal_mul]
    exact integral_ofReal
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Pointwise domination by an operator and its reflection transfers
absolute sparse bounds with factor two. Pairing integrability is stated
explicitly because the project's total Bochner integral is zero on
nonintegrable functions, so a bare signed sparse bound cannot supply it. -/
theorem hasSparseOnePBound_of_norm_le_add_reflected
    {C p : ℝ} (hC : 0 ≤ C) {T U : TestOperator}
    (hT : HasSparseOnePBound C p (absoluteValueOperator T))
    (hTi : ∀ f g : L0Infinity, Integrable (fun x ↦ T f x * star (g x)))
    (hU : ∀ (f : L0Infinity) (x : ℝ),
      ‖U f x‖ ≤ ‖T f x‖ + ‖reflectedOperator T f x‖) :
    HasSparseOnePBound (2 * C) p U := by
  intro f g
  obtain ⟨S, hS, hbS⟩ := hT f (normInput g)
  have hR : HasSparseOnePBound C p (absoluteValueOperator (reflectedOperator T)) :=
    hasSparseOnePBound_reflectedOperator hT
  obtain ⟨R, hR, hbR⟩ := hR f (normInput g)
  rw [norm_operatorPairing_absolute_normInput, sparseForm_normInput] at hbS hbR
  have hi : Integrable (fun x ↦ ‖T f x‖ * ‖g x‖) := by
    simpa only [norm_mul, norm_star] using (hTi f g).norm
  have hir : Integrable (fun x ↦ ‖reflectedOperator T f x‖ * ‖g x‖) := by
    have hi := (hTi (L0Infinity.reflect f) (L0Infinity.reflect g)).comp_neg.norm
    simpa only [reflectedOperator, L0Infinity.reflect_apply, neg_neg, norm_mul, norm_star] using hi
  have hb : ‖operatorPairing U f g‖ ≤
      (∫ x, ‖T f x‖ * ‖g x‖) + ∫ x, ‖reflectedOperator T f x‖ * ‖g x‖ := by
    rw [← integral_add hi hir]
    apply norm_integral_le_of_norm_le (hi.add hir)
    filter_upwards with x
    rw [norm_mul, norm_star, Pi.add_apply, ← add_mul]
    exact mul_le_mul_of_nonneg_right (hU f x) (norm_nonneg _)
  have hb' : ENNReal.ofReal ‖operatorPairing U f g‖ ≤
      ENNReal.ofReal C * sparseForm p f g S + ENNReal.ofReal C * sparseForm p f g R := by
    apply (ENNReal.ofReal_le_ofReal hb).trans
    rw [ENNReal.ofReal_add (integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact add_le_add hbS hbR
  have hCC : ENNReal.ofReal (2 * C) = ENNReal.ofReal C + ENNReal.ofReal C := by
    rw [two_mul, ENNReal.ofReal_add hC hC]
  rcases le_total (sparseForm p f g S) (sparseForm p f g R) with hSR | hRS
  · refine ⟨R, hR, hb'.trans ?_⟩
    rw [hCC, add_mul]
    exact add_le_add (mul_le_mul' le_rfl hSR) le_rfl
  · refine ⟨S, hS, hb'.trans ?_⟩
    rw [hCC, add_mul]
    exact add_le_add le_rfl (mul_le_mul' le_rfl hRS)


/-- Locally integrable outputs supply the pairing-integrability premise
against every bounded compact-support test function. -/
theorem integrable_pairing_of_locallyIntegrable {u : ℝ → ℂ}
    (hu : LocallyIntegrable u volume) (g : L0Infinity) :
    Integrable (fun x ↦ u x * star (g x)) := by
  have hs : support (fun x ↦ u x * star (g x)) ⊆ tsupport g := by
    intro x hx
    apply subset_tsupport g
    change g x ≠ 0
    intro hg
    exact hx (by simp [hg])
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  obtain ⟨C, hC⟩ := g.bounded_toFun
  have hgm : Measurable (fun x : ℝ ↦ star (g x)) :=
    continuous_star.measurable.comp g.measurable_toFun
  have hi := (hu.integrableOn_isCompact g.hasCompactSupport_toFun).bdd_mul
    hgm.aestronglyMeasurable.restrict
    (ae_of_all _ fun x ↦ by simpa only [norm_star] using hC x)
  simpa only [IntegrableOn, mul_comm] using hi

theorem hasSparseOnePBound_of_norm_le_add_reflected_of_locallyIntegrable
    {C p : ℝ} (hC : 0 ≤ C) {T U : TestOperator}
    (hT : HasSparseOnePBound C p (absoluteValueOperator T))
    (hTi : ∀ f : L0Infinity, LocallyIntegrable (T f) volume)
    (hU : ∀ (f : L0Infinity) (x : ℝ),
      ‖U f x‖ ≤ ‖T f x‖ + ‖reflectedOperator T f x‖) :
    HasSparseOnePBound (2 * C) p U :=
  hasSparseOnePBound_of_norm_le_add_reflected hC hT
    (fun f g ↦ integrable_pairing_of_locallyIntegrable (hTi f) g) hU



end KrauseLaceySparseReflection
end QuadraticCarleson
