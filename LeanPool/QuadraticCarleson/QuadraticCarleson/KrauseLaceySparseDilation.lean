/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseReflection
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyFullDyadicSparseTransfer
import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodBoundaryControl

/-!
# Exact positive dilation and conjugation of smooth sparse bounds

The change of variables normalizing a nonzero quadratic modulation is an
arbitrary positive dilation, not necessarily a dyadic dilation.  Accordingly
the exact operator identities below use finite sets of actual positive
smooth radii.  The project's rounded-radius maximum is a special case,
but the rounded radii themselves are not asserted to commute with dilation.

The geometric transfer proves the change of variables for the test space,
intervals, major subsets, local averages, sparse forms, and pairings.  No
sparse conclusion or invariance property is postulated.

The final unit input quantifies over arbitrary positive radii.  The existing
unit dyadic-suffix sparse theorem supplies only rounded dyadic radii.  Passing
from that latter input to this one still requires an annular comparison with
a sparse maximal-average bound, or an extension of the unit analytic proof
to arbitrary scale offsets; that additional implication is not assumed here.
-/

open Function MeasureTheory Set
open scoped ENNReal Topology ComplexConjugate

namespace QuadraticCarleson


noncomputable section

namespace L0Infinity

/-- The input in the change of variables `u = a*x`. -/
def dilate (a : ℝ) (ha : 0 < a) (f : L0Infinity) : L0Infinity where
  toFun := fun x ↦ f (x / a)
  measurable_toFun := f.measurable_toFun.comp (measurable_id.div_const a)
  bounded_toFun := by
    obtain ⟨C, hC⟩ := f.bounded_toFun
    exact ⟨C, fun x ↦ hC (x / a)⟩
  hasCompactSupport_toFun := by
    simpa only [Homeomorph.coe_mulRight₀, div_eq_mul_inv, Function.comp_def] using
      f.hasCompactSupport_toFun.comp_homeomorph
        (Homeomorph.mulRight₀ a⁻¹ (inv_ne_zero ha.ne'))

@[simp] theorem dilate_apply (a : ℝ) (ha : 0 < a) (f : L0Infinity) (x : ℝ) :
    dilate a ha f x = f (x / a) := rfl

@[simp] theorem dilate_dilate_inv (a : ℝ) (ha : 0 < a) (f : L0Infinity) :
    dilate a⁻¹ (inv_pos.mpr ha) (dilate a ha f) = f := by
  cases f
  simp [dilate, div_eq_mul_inv, ha.ne']

@[simp] theorem dilate_inv_dilate (a : ℝ) (ha : 0 < a) (f : L0Infinity) :
    dilate a ha (dilate a⁻¹ (inv_pos.mpr ha) f) = f := by
  cases f
  simp [dilate, div_eq_mul_inv, ha.ne']

def conjugate (f : L0Infinity) : L0Infinity where
  toFun := fun x ↦ conj (f x)
  measurable_toFun := Complex.continuous_conj.measurable.comp f.measurable_toFun
  bounded_toFun := by
    obtain ⟨C, hC⟩ := f.bounded_toFun
    exact ⟨C, fun x ↦ by simpa using hC x⟩
  hasCompactSupport_toFun := f.hasCompactSupport_toFun.comp_left (by simp)

@[simp] theorem conjugate_apply (f : L0Infinity) (x : ℝ) :
    conjugate f x = conj (f x) := rfl

@[simp] theorem conjugate_conjugate (f : L0Infinity) :
    conjugate (conjugate f) = f := by
  cases f
  simp [conjugate]

end L0Infinity

namespace RealInterval

def dilate (a : ℝ) (ha : 0 < a) (I : RealInterval) : RealInterval :=
  ⟨a * I.left, a * I.right, mul_lt_mul_of_pos_left I.left_lt_right ha⟩

@[simp] theorem dilate_left (a : ℝ) (ha : 0 < a) (I : RealInterval) :
    (I.dilate a ha).left = a * I.left := rfl

@[simp] theorem dilate_right (a : ℝ) (ha : 0 < a) (I : RealInterval) :
    (I.dilate a ha).right = a * I.right := rfl

@[simp] theorem dilate_length (a : ℝ) (ha : 0 < a) (I : RealInterval) :
    (I.dilate a ha).length = a * I.length := by
  simp only [length, dilate_left, dilate_right, mul_sub]

@[simp] theorem dilate_inv_dilate (a : ℝ) (ha : 0 < a) (I : RealInterval) :
    (I.dilate a⁻¹ (inv_pos.mpr ha)).dilate a ha = I := by
  cases I
  simp [dilate, ha.ne']

@[simp] theorem dilate_dilate_inv (a : ℝ) (ha : 0 < a) (I : RealInterval) :
    (I.dilate a ha).dilate a⁻¹ (inv_pos.mpr ha) = I := by
  cases I
  simp [dilate, ha.ne']

theorem dilate_injective (a : ℝ) (ha : 0 < a) : Injective (dilate a ha) :=
  (show LeftInverse (dilate a⁻¹ (inv_pos.mpr ha)) (dilate a ha) from
    dilate_dilate_inv a ha).injective

@[simp] theorem preimage_mul_dilate_carrier (a : ℝ) (ha : 0 < a) (I : RealInterval) :
    (fun x : ℝ ↦ a * x) ⁻¹' (I.dilate a ha).carrier = I.carrier := by
  ext x
  exact and_congr (mul_lt_mul_iff_right₀ ha) (mul_le_mul_iff_right₀ ha)

end RealInterval

namespace KrauseLaceySparseDilation

open KrauseLaceySharpSmoothAdapter QuadraticHilbertMaximalMeasurable

/-- Pull a family back by `x ↦ a*x`; its intervals are divided by `a`. -/
def pullbackFamily (a : ℝ) (ha : 0 < a) (S : Set RealInterval) : Set RealInterval :=
  RealInterval.dilate a ha ⁻¹' S

@[simp] theorem pullbackFamily_inverse (a : ℝ) (ha : 0 < a) (S : Set RealInterval) :
    pullbackFamily a⁻¹ (inv_pos.mpr ha) (pullbackFamily a ha S) = S := by
  ext I
  simp [pullbackFamily]

def pullbackIndexEquiv (a : ℝ) (ha : 0 < a) (S : Set RealInterval) :
    {I : RealInterval // I ∈ pullbackFamily a ha S} ≃
      {I : RealInterval // I ∈ S} where
  toFun I := ⟨I.1.dilate a ha, I.2⟩
  invFun I := ⟨I.1.dilate a⁻¹ (inv_pos.mpr ha), by simp [pullbackFamily, I.2]⟩
  left_inv I := by ext; simp
  right_inv I := by ext; simp

/-- The major subsets are pulled back by the same dilation.  In particular
the exact density parameter, including the source's `1/4`, is preserved. -/
theorem isSparse_pullbackFamily (a : ℝ) (ha : 0 < a)
    {η : ℝ} {S : Set RealInterval} (hS : IsSparse η S) :
    IsSparse η (pullbackFamily a ha S) := by
  rcases hS with ⟨hη, hη1, E, hEm, hEs, hEd, hEv⟩
  let e := pullbackIndexEquiv a ha S
  let F : {I : RealInterval // I ∈ pullbackFamily a ha S} → Set ℝ :=
    fun I ↦ (fun x : ℝ ↦ a * x) ⁻¹' E (e I)
  refine ⟨hη, hη1, F, ?_, ?_, ?_, ?_⟩
  · intro I
    exact (hEm (e I)).preimage (measurable_const.mul measurable_id)
  · intro I
    have hh := preimage_mono (f := fun x : ℝ ↦ a * x) (hEs (e I))
    change F I ⊆ (fun x : ℝ ↦ a * x) ⁻¹' (I.1.dilate a ha).carrier at hh
    simpa only [RealInterval.preimage_mul_dilate_carrier] using hh
  · intro I J hIJ
    exact (hEd (e.injective.ne hIJ)).preimage _
  · intro I
    have hv : (volume (F I)).toReal = a⁻¹ * (volume (E (e I))).toReal := by
      change (volume ((fun x : ℝ ↦ a * x) ⁻¹' E (e I))).toReal = _
      rw [Real.volume_preimage_mul_left ha.ne', ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr ha)]
    rw [hv]
    have hh := mul_le_mul_of_nonneg_left (hEv (e I)) (inv_nonneg.mpr ha.le)
    change a⁻¹ * (η * (I.1.dilate a ha).length) ≤ _ at hh
    rw [RealInterval.dilate_length] at hh
    convert hh using 1
    field_simp

theorem isSparse_pullbackFamily_iff (a : ℝ) (ha : 0 < a)
    {η : ℝ} {S : Set RealInterval} :
    IsSparse η (pullbackFamily a ha S) ↔ IsSparse η S := by
  constructor
  · intro h
    simpa using isSparse_pullbackFamily a⁻¹ (inv_pos.mpr ha) h
  · exact isSparse_pullbackFamily a ha

/-- Exact normalized local averages under positive dilation. -/
theorem localAverage_dilate (p : ℝ) (a : ℝ) (ha : 0 < a)
    (f : ℝ → ℂ) (I : RealInterval) :
    localAverage p (fun x ↦ f (x / a)) (I.dilate a ha) =
      localAverage p f I := by
  unfold localAverage
  rw [RealInterval.dilate_length]
  have hi : (∫ x in (I.dilate a ha).carrier, ‖f (x / a)‖ ^ p) =
      a * ∫ x in I.carrier, ‖f x‖ ^ p := by
    rw [RealInterval.carrier,
      ← intervalIntegral.integral_of_le (I.dilate a ha).left_lt_right.le]
    change (∫ x in a * I.left..a * I.right, (fun y ↦ ‖f y‖ ^ p) (x / a)) = _
    rw [intervalIntegral.integral_comp_div (fun y ↦ ‖f y‖ ^ p) ha.ne']
    simp only [mul_div_cancel_left₀ _ ha.ne', smul_eq_mul]
    rw [intervalIntegral.integral_of_le I.left_lt_right.le]
    rfl
  rw [hi]
  congr 1
  field_simp

theorem sparseForm_pullbackFamily (p : ℝ) (a : ℝ) (ha : 0 < a)
    (f g : ℝ → ℂ) (S : Set RealInterval) :
    sparseForm p f g (pullbackFamily a ha S) =
      ENNReal.ofReal a⁻¹ *
        sparseForm p (fun x ↦ f (x / a)) (fun x ↦ g (x / a)) S := by
  unfold sparseForm
  rw [← (pullbackIndexEquiv a ha S).tsum_eq, ← ENNReal.tsum_mul_left]
  congr 1
  funext I
  change ENNReal.ofReal (I.1.length * localAverage 1 f I.1 * localAverage p g I.1) =
    ENNReal.ofReal a⁻¹ * ENNReal.ofReal
      ((I.1.dilate a ha).length * localAverage 1 (fun x ↦ f (x / a))
        (I.1.dilate a ha) * localAverage p (fun x ↦ g (x / a)) (I.1.dilate a ha))
  rw [RealInterval.dilate_length, localAverage_dilate, localAverage_dilate,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
  congr 1
  field_simp

def dilatedOperator (a : ℝ) (ha : 0 < a) (T : TestOperator) : TestOperator :=
  fun f x ↦ T (L0Infinity.dilate a ha f) (a * x)

theorem operatorPairing_dilatedOperator (a : ℝ) (ha : 0 < a)
    (T : TestOperator) (f g : L0Infinity) :
    operatorPairing (dilatedOperator a ha T) f g =
      a⁻¹ • operatorPairing T (L0Infinity.dilate a ha f) (L0Infinity.dilate a ha g) := by
  have hi := Measure.integral_comp_mul_left
    (fun x ↦ T (L0Infinity.dilate a ha f) x * star (g (x / a))) a
  simpa only [operatorPairing, dilatedOperator, L0Infinity.dilate_apply,
    mul_div_cancel_left₀ _ ha.ne', abs_of_pos (inv_pos.mpr ha)] using hi

/-- Sparse constants are unchanged, because the pairing and the sparse form
acquire exactly the same positive Jacobian. -/
theorem hasSparseOnePBound_dilatedOperator (a : ℝ) (ha : 0 < a)
    {C p : ℝ} {T : TestOperator} (hT : HasSparseOnePBound C p T) :
    HasSparseOnePBound C p (dilatedOperator a ha T) := by
  intro f g
  obtain ⟨S, hS, hb⟩ := hT (L0Infinity.dilate a ha f) (L0Infinity.dilate a ha g)
  refine ⟨pullbackFamily a ha S, isSparse_pullbackFamily a ha hS, ?_⟩
  rw [operatorPairing_dilatedOperator, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ha), ENNReal.ofReal_mul (inv_nonneg.mpr ha.le),
    sparseForm_pullbackFamily]
  calc
    _ ≤ ENNReal.ofReal a⁻¹ * (ENNReal.ofReal C *
        sparseForm p (L0Infinity.dilate a ha f) (L0Infinity.dilate a ha g) S) :=
      mul_le_mul' le_rfl hb
    _ = _ := by rw [mul_left_comm]; rfl

@[simp] theorem dilatedOperator_inverse (a : ℝ) (ha : 0 < a) (T : TestOperator) :
    dilatedOperator a⁻¹ (inv_pos.mpr ha) (dilatedOperator a ha T) = T := by
  funext f x
  simp [dilatedOperator, ha.ne']

theorem hasSparseOnePBound_dilatedOperator_iff (a : ℝ) (ha : 0 < a)
    {C p : ℝ} {T : TestOperator} :
    HasSparseOnePBound C p (dilatedOperator a ha T) ↔ HasSparseOnePBound C p T := by
  constructor
  · intro h
    simpa using hasSparseOnePBound_dilatedOperator a⁻¹ (inv_pos.mpr ha) h
  · exact hasSparseOnePBound_dilatedOperator a ha

theorem sparseOnePNorm_dilatedOperator (p a : ℝ) (ha : 0 < a) (T : TestOperator) :
    sparseOnePNorm p (dilatedOperator a ha T) = sparseOnePNorm p T := by
  simp only [sparseOnePNorm, hasSparseOnePBound_dilatedOperator_iff]

theorem localAverage_conjugate (p : ℝ) (f : ℝ → ℂ) (I : RealInterval) :
    localAverage p (fun x ↦ conj (f x)) I = localAverage p f I := by
  simp [localAverage]

theorem sparseForm_conjugate (p : ℝ) (f g : ℝ → ℂ) (S : Set RealInterval) :
    sparseForm p (fun x ↦ conj (f x)) (fun x ↦ conj (g x)) S = sparseForm p f g S := by
  simp only [sparseForm, localAverage_conjugate]

def conjugatedOperator (T : TestOperator) : TestOperator :=
  fun f x ↦ conj (T (L0Infinity.conjugate f) x)

@[simp] theorem conjugatedOperator_conjugatedOperator (T : TestOperator) :
    conjugatedOperator (conjugatedOperator T) = T := by
  funext f x
  simp [conjugatedOperator]

theorem operatorPairing_conjugatedOperator (T : TestOperator) (f g : L0Infinity) :
    operatorPairing (conjugatedOperator T) f g =
      conj (operatorPairing T (L0Infinity.conjugate f) (L0Infinity.conjugate g)) := by
  rw [operatorPairing, operatorPairing, ← integral_conj]
  congr 1
  funext x
  simp [conjugatedOperator]

theorem hasSparseOnePBound_conjugatedOperator {C p : ℝ} {T : TestOperator}
    (hT : HasSparseOnePBound C p T) :
    HasSparseOnePBound C p (conjugatedOperator T) := by
  intro f g
  obtain ⟨S, hS, hb⟩ := hT (L0Infinity.conjugate f) (L0Infinity.conjugate g)
  refine ⟨S, hS, ?_⟩
  rw [operatorPairing_conjugatedOperator, Complex.norm_conj]
  simpa only [L0Infinity.conjugate, sparseForm_conjugate] using hb

theorem hasSparseOnePBound_conjugatedOperator_iff {C p : ℝ} {T : TestOperator} :
    HasSparseOnePBound C p (conjugatedOperator T) ↔ HasSparseOnePBound C p T := by
  constructor
  · intro h
    simpa using hasSparseOnePBound_conjugatedOperator h
  · exact hasSparseOnePBound_conjugatedOperator

theorem sparseOnePNorm_conjugatedOperator (p : ℝ) (T : TestOperator) :
    sparseOnePNorm p (conjugatedOperator T) = sparseOnePNorm p T := by
  simp only [sparseOnePNorm, hasSparseOnePBound_conjugatedOperator_iff]

/-- The cutoff ratio itself is invariant when the radius and space are
scaled together; this follows from the actual definition, not dyadic
telescoping.  The factor `a` is the kernel Jacobian. -/
theorem smoothQuadraticHighPassKernel_scale (sigma : ℝ) (a : ℝ) (ha : 0 < a)
    (ρ t : ℝ) :
    smoothQuadraticHighPassKernel (sigma * a ^ 2) ρ t =
      (a : ℂ) * smoothQuadraticHighPassKernel sigma (a * ρ) (a * t) := by
  by_cases ht : t = 0
  · simp [ht, smoothQuadraticHighPassKernel]
  have hratio : (a * t) / (4 * (a * ρ)) = t / (4 * ρ) := by
    rw [show 4 * (a * ρ) = a * (4 * ρ) by ring,
      mul_div_mul_left _ _ ha.ne']
  rw [smoothQuadraticHighPassKernel, ite_eq_right ht,
    smoothQuadraticHighPassKernel, ite_eq_right (mul_ne_zero ha.ne' ht), hratio,
    quadratic_phase_scale]
  push_cast
  field_simp [ha.ne', ht]

/-- Exact smooth high-pass change of variables, valid even without an
integrability premise under the total Bochner-integral convention. -/
theorem smoothQuadraticHighPass_scale (sigma : ℝ) (a : ℝ) (ha : 0 < a)
    (ρ : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    smoothQuadraticHighPass (sigma * a ^ 2) ρ f x =
      smoothQuadraticHighPass sigma (a * ρ) (fun u ↦ f (u / a)) (a * x) := by
  let F : ℝ → ℂ := fun u ↦
    smoothQuadraticHighPassKernel sigma (a * ρ) (a * x - u) * f (u / a)
  have hi := Measure.integral_comp_mul_left F a
  rw [abs_of_pos (inv_pos.mpr ha)] at hi
  calc
    _ = (a : ℂ) * ∫ y, F (a * y) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      dsimp [F]
      rw [smoothQuadraticHighPassKernel_scale sigma a ha,
        mul_div_cancel_left₀ _ ha.ne', mul_sub]
      ring
    _ = (a : ℂ) * (a⁻¹ • ∫ u, F u) := by rw [hi]
    _ = _ := by simp [smoothQuadraticHighPass, F, ha.ne']

theorem smoothQuadraticHighPass_normalize_nonzero {lam : ℝ} (hlam : lam ≠ 0)
    (ρ : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    smoothQuadraticHighPass lam ρ f x =
      smoothQuadraticHighPass (if lam < 0 then (-1 : ℝ) else 1)
        (Real.sqrt |lam| * ρ) (fun u ↦ f (u / Real.sqrt |lam|))
          (Real.sqrt |lam| * x) := by
  conv_lhs => rw [nonzero_modulation_eq_signed_sqrt_square hlam]
  exact smoothQuadraticHighPass_scale _ _ (Real.sqrt_pos.2 (abs_pos.2 hlam)) ρ f x

theorem smoothQuadraticHighPassKernel_neg_one_eq_conj (ρ t : ℝ) :
    smoothQuadraticHighPassKernel (-1) ρ t =
      conj (smoothQuadraticHighPassKernel 1 ρ t) := by
  by_cases ht : t = 0
  · simp [ht, smoothQuadraticHighPassKernel]
  simp only [smoothQuadraticHighPassKernel, ite_eq_right ht, map_mul,
    Complex.conj_ofReal, ← phase_neg_eq_conj]
  congr 2
  ring

theorem smoothQuadraticHighPass_neg_one_eq_conj (ρ : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    smoothQuadraticHighPass (-1) ρ f x =
      conj (smoothQuadraticHighPass 1 ρ (fun y ↦ conj (f y)) x) := by
  unfold smoothQuadraticHighPass
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with y
  simp [smoothQuadraticHighPassKernel_neg_one_eq_conj]

/-- Actual positive smooth radii, without a dyadic rounding operation. -/
abbrev PositiveSmoothRadius := {ρ : ℝ // 0 < ρ}

def scaleRadius (a : ℝ) (ha : 0 < a) (ρ : PositiveSmoothRadius) : PositiveSmoothRadius :=
  ⟨a * ρ.1, mul_pos ha ρ.2⟩

def scaleRadii (a : ℝ) (ha : 0 < a) (s : Finset PositiveSmoothRadius) :
    Finset PositiveSmoothRadius := by
  classical
  exact s.image (scaleRadius a ha)

def finiteSmoothMaxNNNorm (lam : ℝ) (s : Finset PositiveSmoothRadius)
    (f : L0Infinity) (x : ℝ) : NNReal :=
  s.sup fun ρ ↦ ‖smoothQuadraticHighPass lam ρ.1 f x‖₊

def finiteSmoothMaxOperator (lam : ℝ) (s : Finset PositiveSmoothRadius) : TestOperator :=
  fun f x ↦ ((finiteSmoothMaxNNNorm lam s f x : ℝ) : ℂ)

@[simp] theorem absoluteValue_finiteSmoothMaxOperator
    (lam : ℝ) (s : Finset PositiveSmoothRadius) :
    absoluteValueOperator (finiteSmoothMaxOperator lam s) = finiteSmoothMaxOperator lam s := by
  funext f x
  simp [absoluteValueOperator, finiteSmoothMaxOperator]

/-- No scale set is rounded in this identity. -/
theorem finiteSmoothMaxOperator_scale (sigma : ℝ) (a : ℝ) (ha : 0 < a)
    (s : Finset PositiveSmoothRadius) :
    finiteSmoothMaxOperator (sigma * a ^ 2) s =
      dilatedOperator a ha (finiteSmoothMaxOperator sigma (scaleRadii a ha s)) := by
  classical
  funext f x
  simp only [finiteSmoothMaxOperator, finiteSmoothMaxNNNorm, dilatedOperator,
    scaleRadii, Finset.sup_image]
  congr 2
  apply Finset.sup_congr rfl
  intro ρ hρ
  rw [smoothQuadraticHighPass_scale sigma a ha]
  rfl

theorem finiteSmoothMaxOperator_neg_one_eq_conjugated (s : Finset PositiveSmoothRadius) :
    finiteSmoothMaxOperator (-1) s = conjugatedOperator (finiteSmoothMaxOperator 1 s) := by
  funext f x
  have hn (z : ℂ) : ‖conj z‖₊ = ‖z‖₊ := NNReal.eq (Complex.norm_conj z)
  simp only [finiteSmoothMaxOperator, finiteSmoothMaxNNNorm, conjugatedOperator,
    Complex.conj_ofReal, smoothQuadraticHighPass_neg_one_eq_conj, hn]
  rfl

/-- The negative sign needs no extra analytic hypothesis. -/
theorem hasSparseOnePBound_finiteSmoothMaxOperator_neg_one {C p : ℝ}
    (s : Finset PositiveSmoothRadius)
    (h : HasSparseOnePBound C p (finiteSmoothMaxOperator 1 s)) :
    HasSparseOnePBound C p (finiteSmoothMaxOperator (-1) s) := by
  rw [finiteSmoothMaxOperator_neg_one_eq_conjugated]
  exact hasSparseOnePBound_conjugatedOperator h

/-- For one selected finite family, the unit-phase estimate is needed only
at its exact normalized radius set. -/
theorem hasSparseOnePBound_finiteSmoothMaxOperator_nonzero_of_scaled_unit {C p : ℝ}
    {lam : ℝ} (hlam : lam ≠ 0) (s : Finset PositiveSmoothRadius)
    (hunit : HasSparseOnePBound C p (finiteSmoothMaxOperator 1
      (scaleRadii (Real.sqrt |lam|) (Real.sqrt_pos.2 (abs_pos.2 hlam)) s))) :
    HasSparseOnePBound C p (finiteSmoothMaxOperator lam s) := by
  let a : ℝ := Real.sqrt |lam|
  have ha : 0 < a := Real.sqrt_pos.2 (abs_pos.2 hlam)
  have hdecomp := nonzero_modulation_eq_signed_sqrt_square hlam
  rw [hdecomp, finiteSmoothMaxOperator_scale _ a ha]
  apply hasSparseOnePBound_dilatedOperator
  split_ifs
  · exact hasSparseOnePBound_finiteSmoothMaxOperator_neg_one _ hunit
  · exact hunit

/-- Every nonzero modulation reduces to the positive unit phase, with the
same sparse constant, by exact dilation and conjugation. -/
theorem hasSparseOnePBound_finiteSmoothMaxOperator_nonzero {C p : ℝ}
    (hunit : ∀ s : Finset PositiveSmoothRadius,
      HasSparseOnePBound C p (finiteSmoothMaxOperator 1 s))
    {lam : ℝ} (hlam : lam ≠ 0) (s : Finset PositiveSmoothRadius) :
    HasSparseOnePBound C p (finiteSmoothMaxOperator lam s) :=
  hasSparseOnePBound_finiteSmoothMaxOperator_nonzero_of_scaled_unit hlam s (hunit _)

def roundedRadii (s : Finset densePositiveRadii) : Finset PositiveSmoothRadius := by
  classical
  exact s.image fun ε ↦
    ⟨dyadicCeilRadius ε.1.1 ε.1.2, dyadicCeilRadius_pos ε.1.1 ε.1.2⟩

theorem finiteRadiusSmoothHighPassMaxTestOperator_eq_finiteSmoothMaxOperator
    (lam : ℝ) (s : Finset densePositiveRadii) :
    finiteRadiusSmoothHighPassMaxTestOperator lam s =
      finiteSmoothMaxOperator lam (roundedRadii s) := by
  classical
  funext f x
  simp [finiteRadiusSmoothHighPassMaxTestOperator, finiteRadiusSmoothHighPassMaxNNNorm,
    finiteSmoothMaxOperator, finiteSmoothMaxNNNorm, roundedRadii, Finset.sup_image,
    Function.comp_def]

theorem hasSparseOnePBound_finiteRadiusSmoothHighPassMax_nonzero {C p : ℝ}
    (hunit : ∀ s : Finset PositiveSmoothRadius,
      HasSparseOnePBound C p (finiteSmoothMaxOperator 1 s))
    {lam : ℝ} (hlam : lam ≠ 0) (s : Finset densePositiveRadii) :
    HasSparseOnePBound C p (finiteRadiusSmoothHighPassMaxTestOperator lam s) := by
  rw [finiteRadiusSmoothHighPassMaxTestOperator_eq_finiteSmoothMaxOperator]
  exact hasSparseOnePBound_finiteSmoothMaxOperator_nonzero hunit hlam _

/-- Local integrability of every finite smooth maximum is a direct kernel
bound; it is not an extra assumption in the sparse transfer. -/
theorem locallyIntegrable_finiteSmoothMaxOperator
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (f : L0Infinity) :
    LocallyIntegrable (finiteSmoothMaxOperator lam s f) volume := by
  classical
  have hmeas (ρ : PositiveSmoothRadius) :
      Measurable (fun x ↦ smoothQuadraticHighPass lam ρ.1 f x) := by
    unfold smoothQuadraticHighPass
    have hk := (measurable_smoothQuadraticHighPassKernel lam ρ.1).comp
      (measurable_fst.sub measurable_snd)
    have hj : StronglyMeasurable (fun z : ℝ × ℝ ↦
        smoothQuadraticHighPassKernel lam ρ.1 (z.1 - z.2) * f z.2) :=
      (hk.mul (f.measurable_toFun.comp measurable_snd)).stronglyMeasurable
    exact hj.integral_prod_right'.measurable
  have hmax : Measurable (fun x ↦ (finiteSmoothMaxNNNorm lam s f x : ℝ)) := by
    unfold finiteSmoothMaxNNNorm
    induction s using Finset.induction_on with
    | empty => simp
    | @insert ρ s hρ ih =>
        simp only [Finset.sup_insert, NNReal.coe_max, coe_nnnorm]
        exact (hmeas ρ).norm.max ih
  rw [locallyIntegrable_iff]
  intro K hK
  change IntegrableOn (fun x ↦ ((finiteSmoothMaxNNNorm lam s f x : ℝ) : ℂ)) K volume
  let C : ℝ := ∑ ρ ∈ s, (2 / ρ.1) * ∫ y, ‖f y‖
  refine IntegrableOn.of_bound hK.measure_lt_top
    ((Complex.measurable_ofReal.comp hmax).aestronglyMeasurable.restrict) C ?_
  filter_upwards with x
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (NNReal.coe_nonneg _)]
  unfold finiteSmoothMaxNNNorm
  calc
    _ ≤ ∑ ρ ∈ s, ‖smoothQuadraticHighPass lam ρ.1 f x‖ := by
      have hs : s.sup (fun ρ ↦ ‖smoothQuadraticHighPass lam ρ.1 f x‖₊) ≤
          ∑ ρ ∈ s, ‖smoothQuadraticHighPass lam ρ.1 f x‖₊ := by
        apply Finset.sup_le
        intro ρ hρ
        exact Finset.single_le_sum
          (f := fun δ : PositiveSmoothRadius ↦ ‖smoothQuadraticHighPass lam δ.1 f x‖₊)
          (fun δ _ ↦ zero_le) hρ
      simpa only [NNReal.coe_sum, coe_nnnorm] using NNReal.coe_le_coe.mpr hs
    _ ≤ C := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hi : Integrable (fun y ↦
          smoothQuadraticHighPassKernel lam ρ.1 (x - y) * f y) :=
        OscillatoryReduction.integrable_kernel_mul_l0 f x
          (measurable_smoothQuadraticHighPassKernel _ _)
          (fun t ↦ smoothQuadraticHighPassKernel_norm_le lam ρ.2)
      rw [smoothQuadraticHighPass]
      calc
        ‖∫ y, smoothQuadraticHighPassKernel lam ρ.1 (x - y) * f y‖ ≤
            ∫ y, ‖smoothQuadraticHighPassKernel lam ρ.1 (x - y) * f y‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ y, (2 / ρ.1) * ‖f y‖ := by
          apply integral_mono hi.norm (f.integrable.norm.const_mul _)
          intro y
          change ‖smoothQuadraticHighPassKernel lam ρ.1 (x - y) * f y‖ ≤ _
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            (smoothQuadraticHighPassKernel_norm_le lam ρ.2) (norm_nonneg _)
        _ = _ := integral_const_mul _ _

/-- Exact unit-phase input with arbitrary finite positive smooth radii.
This is deliberately not identified with the dyadically rounded input. -/
def HasUnitFiniteSmoothSparseBound (A : ℝ) : Prop :=
  0 ≤ A ∧ ∀ (s : Finset PositiveSmoothRadius) (p : ℝ), 1 < p → p < 2 →
    HasSparseOnePBound (A * holderConjugate p) p (finiteSmoothMaxOperator 1 s)

/-- The sharper unit input needed by the paper-facing rounded maximum:
one common positive dilation of each rounded family.  This permits arbitrary
scale offsets but does not ask for unrelated arbitrary radii. -/
def HasUnitScaleOffsetSmoothSparseBound (A : ℝ) : Prop :=
  0 ≤ A ∧ ∀ (a : ℝ) (ha : 0 < a) (s : Finset densePositiveRadii) (p : ℝ),
    1 < p → p < 2 → HasSparseOnePBound (A * holderConjugate p) p
      (finiteSmoothMaxOperator 1 (scaleRadii a ha (roundedRadii s)))

/-- Exact paper-facing reduction with the sharper scale-offset unit input.
All local-integrability clauses, both modulation signs, and the unchanged
quantitative constant are established rather than assumed. -/
theorem hasUniformFiniteRadiusSmoothSparseBound_of_unit_scaleOffset
    {A : ℝ} (hA : HasUnitScaleOffsetSmoothSparseBound A) :
    HardyLittlewoodBoundaryControl.HasUniformFiniteRadiusSmoothSparseBound A := by
  refine ⟨hA.1, ?_⟩
  intro lam hlam s
  rw [finiteRadiusSmoothHighPassMaxTestOperator_eq_finiteSmoothMaxOperator]
  refine ⟨locallyIntegrable_finiteSmoothMaxOperator lam (roundedRadii s), ?_⟩
  intro p hp hp2
  rw [absoluteValue_finiteSmoothMaxOperator]
  have hbound := hasSparseOnePBound_finiteSmoothMaxOperator_nonzero_of_scaled_unit
    hlam (roundedRadii s)
      (hA.2 (Real.sqrt |lam|) (Real.sqrt_pos.2 (abs_pos.2 hlam)) s p hp hp2)
  have hC : 0 ≤ A * holderConjugate p :=
    mul_nonneg hA.1 (holderConjugate_spec hp).symm.pos.le
  exact ⟨⟨A * holderConjugate p, hC, hbound⟩,
    KrauseLaceyFullDyadicSparseTransfer.sparseOnePNorm_le_of_bound hC hbound⟩

/-- Convenient stronger unit-phase input with arbitrary finite positive
radii.  The scale-offset theorem above records exactly which families this
adapter actually uses. -/
theorem hasUniformFiniteRadiusSmoothSparseBound_of_unit
    {A : ℝ} (hA : HasUnitFiniteSmoothSparseBound A) :
    HardyLittlewoodBoundaryControl.HasUniformFiniteRadiusSmoothSparseBound A := by
  apply hasUniformFiniteRadiusSmoothSparseBound_of_unit_scaleOffset
  exact ⟨hA.1, fun a ha s p hp hp2 ↦ hA.2 (scaleRadii a ha (roundedRadii s)) p hp hp2⟩


end KrauseLaceySparseDilation
end
end QuadraticCarleson
