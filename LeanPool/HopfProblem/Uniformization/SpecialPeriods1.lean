/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1

/-!
# Hopf problem: uniformization · special periods 1

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private def SpecialPeriods.rho : ℂ :=
  (1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2

@[simp]
private theorem SpecialPeriods.rho_re : rho.re = 1 / 2 := by
  norm_num [rho, Complex.div_re, Complex.normSq_apply]

@[simp]
private theorem SpecialPeriods.rho_im : rho.im = Real.sqrt 3 / 2 := by
  norm_num [rho, Complex.div_im, Complex.normSq_apply]

private theorem SpecialPeriods.rho_im_pos : 0 < rho.im := by
  rw [rho_im]
  positivity

private theorem
    SpecialPeriods.rho_eq_exp : rho = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  unfold rho
  ring

private theorem SpecialPeriods.rho_sq : rho ^ 2 = rho - 1 := by
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re, rho_re, rho_im, Complex.sub_re, Complex.one_re]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · simp only [pow_two, Complex.mul_im, rho_re, rho_im, Complex.sub_im, Complex.one_im]
    ring

private theorem SpecialPeriods.norm_rho : ‖rho‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, Complex.sq_norm, Complex.normSq_apply, rho_re,
    rho_im]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private theorem SpecialPeriods.rho_cube : rho ^ 3 = -1 := by
  calc
    rho ^ 3 = rho * rho ^ 2 := by ring
    _ = rho * (rho - 1) := by rw [rho_sq]
    _ = -1 := by linear_combination rho_sq

private theorem SpecialPeriods.conj_rho : starRingEnd ℂ rho = 1 - rho := by
  apply Complex.ext <;> simp
  ring

private def SpecialPeriods.cayley (a z : ℂ) : ℂ :=
  (a - starRingEnd ℂ a * z) / (1 - z)

@[simp]
private theorem SpecialPeriods.cayley_zero (a : ℂ) : cayley a 0 = a := by simp [cayley]

private theorem
    SpecialPeriods.one_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := (sub_eq_zero.mp h).symm
  simp [this] at hz

private theorem SpecialPeriods.cayley_im (a z : ℂ) :
    (cayley a z).im = a.im * (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
  simp only [cayley, Complex.div_im, Complex.sub_im, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.sub_re, Complex.mul_re, Complex.one_re, Complex.one_im,
    Complex.normSq_apply]
  ring

private theorem SpecialPeriods.cayley_im_pos {a z : ℂ} (ha : 0 < a.im) (hz : ‖z‖ < 1) :
    0 < (cayley a z).im := by
  rw [cayley_im]
  apply div_pos
  · apply mul_pos ha
    rw [sub_pos, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  · exact Complex.normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hz)

private theorem
    SpecialPeriods.cayley_contDiffOn (a : ℂ) : ContDiffOn ℂ ω (cayley a) (Metric.ball 0 1) := by
  apply ContDiffOn.div
  · exact contDiffOn_const.sub (contDiffOn_const.mul contDiffOn_id)
  · exact contDiffOn_const.sub contDiffOn_id
  · intro z hz
    exact one_sub_ne_zero_of_norm_lt_one (by simpa using hz)

private def SpecialPeriods.sectionThree (τ : ℂ) : PeriodPoint :=
  ⟨τ, (2 - τ) / 3, 2 * τ / 3 - Complex.I⟩

private def SpecialPeriods.sectionFour (τ : ℂ) : PeriodPoint :=
  ⟨τ, (1 - τ) / 2, 3 * τ / 2 - Complex.I⟩

private theorem SpecialPeriods.sectionThree_discriminant (τ : ℂ) (hτ : τ.im ≠ 0) :
    (sectionThree τ).discriminant = -1 := by
  apply mul_left_cancel₀ hτ
  simp [sectionThree, PeriodPoint.discriminant]
  field_simp
  ring

private theorem SpecialPeriods.sectionFour_discriminant (τ : ℂ) (hτ : τ.im ≠ 0) :
    (sectionFour τ).discriminant = -1 := by
  apply mul_left_cancel₀ hτ
  simp [sectionFour, PeriodPoint.discriminant]
  field_simp
  ring

private theorem SpecialPeriods.sectionThree_admissible {τ : ℂ} (hτ : 0 < τ.im) :
    (sectionThree τ).Admissible := by
  refine ⟨hτ, ?_⟩
  rw [sectionThree_discriminant τ hτ.ne']
  norm_num

private theorem SpecialPeriods.sectionFour_admissible {τ : ℂ} (hτ : 0 < τ.im) :
    (sectionFour τ).Admissible := by
  refine ⟨hτ, ?_⟩
  rw [sectionFour_discriminant τ hτ.ne']
  norm_num

private theorem SpecialPeriods.sectionThree_step (τ : ℂ) (hτ : τ ≠ 0) :
    (sectionThree τ).step₁ = sectionThree ((τ - 1) / τ) := by
  apply PeriodPoint.ext <;> simp [sectionThree, PeriodPoint.step₁] <;> field_simp <;> ring

private theorem SpecialPeriods.sectionFour_step (τ : ℂ) (hτ : τ ≠ 0) :
    (sectionFour τ).step₂ = sectionFour (-1 / τ) := by
  apply PeriodPoint.ext <;> simp [sectionFour, PeriodPoint.step₂] <;> field_simp <;> ring

private def SpecialPeriods.rotateThree (z : ℂ) : ℂ :=
  -rho * z

private def SpecialPeriods.rotateFour (z : ℂ) : ℂ :=
  -Complex.I * z

@[simp]
private theorem SpecialPeriods.norm_rotateThree (z : ℂ) : ‖rotateThree z‖ = ‖z‖ := by
  simp [rotateThree, norm_rho]

private theorem
    SpecialPeriods.rotateThree_cube (z : ℂ) : rotateThree (rotateThree (rotateThree z)) = z :=
  by
  change -rho * (-rho * (-rho * z)) = z
  calc
    -rho * (-rho * (-rho * z)) = -(rho ^ 3) * z := by ring
    _ = z := by rw [rho_cube]; ring

private theorem SpecialPeriods.rotateFour_fourth (z : ℂ) :
    rotateFour (rotateFour (rotateFour (rotateFour z))) = z := by simp [rotateFour, ← mul_assoc]

private def SpecialPeriods.tauThree (z : ℂ) : ℂ :=
  cayley rho z

private def SpecialPeriods.tauFour (z : ℂ) : ℂ :=
  cayley Complex.I (z ^ 2)

private theorem SpecialPeriods.tauThree_im_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (tauThree z).im :=
  cayley_im_pos rho_im_pos hz

private theorem SpecialPeriods.tauFour_im_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (tauFour z).im := by
  apply cayley_im_pos (by simp)
  rw [norm_pow]
  nlinarith [norm_nonneg z]

private theorem SpecialPeriods.tauThree_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : tauThree z ≠ 0 := by
  intro he
  have := tauThree_im_pos hz
  simp [he] at this

private theorem SpecialPeriods.tauFour_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : tauFour z ≠ 0 := by
  intro he
  have := tauFour_im_pos hz
  simp [he] at this

private theorem SpecialPeriods.tauThree_rotate {z : ℂ} (hz : ‖z‖ < 1) :
    tauThree (rotateThree z) = (tauThree z - 1) / tauThree z := by
  have hd : 1 - z ≠ 0 := one_sub_ne_zero_of_norm_lt_one hz
  have hr : 1 + rho * z ≠ 0 := by
    simpa only [rotateThree, neg_mul, sub_neg_eq_add] using
      one_sub_ne_zero_of_norm_lt_one (show ‖rotateThree z‖ < 1 by simpa using hz)
  have hn : rho - (1 - rho) * (-rho * z) = rho + z := by linear_combination -z * rho_sq
  rw [eq_div_iff (tauThree_ne_zero hz)]
  simp only [tauThree, cayley, conj_rho, rotateThree]
  rw [hn]
  simp only [neg_mul, sub_neg_eq_add]
  field_simp
  linear_combination (1 - z ^ 2) * rho_sq

private theorem SpecialPeriods.tauFour_rotate {z : ℂ} (hz : ‖z‖ < 1) :
    tauFour (rotateFour z) = -1 / tauFour z := by
  have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have hd : 1 - z ^ 2 ≠ 0 := one_sub_ne_zero_of_norm_lt_one hz2
  have hp : 1 + z ^ 2 ≠ 0 := by
    intro h
    have he : z ^ 2 = -1 := eq_neg_of_add_eq_zero_right h
    simp [he] at hz2
  simp [tauFour, cayley, rotateFour, mul_pow, Complex.I_sq]
  field_simp
  ring_nf
  simp

private theorem SpecialPeriods.tauThree_contDiffOn : ContDiffOn ℂ ω tauThree (Metric.ball 0 1) :=
  cayley_contDiffOn rho

private theorem SpecialPeriods.tauFour_contDiffOn : ContDiffOn ℂ ω tauFour (Metric.ball 0 1) := by
  apply (cayley_contDiffOn Complex.I).comp (contDiffOn_id.pow 2)
  intro z hz
  simp only [Metric.mem_ball, dist_zero_right, norm_pow, id_eq] at *
  nlinarith [norm_nonneg z]

private def SpecialPeriods.localThree (z : ℂ) : PeriodPoint :=
  sectionThree (tauThree z)

private def SpecialPeriods.localFour (z : ℂ) : PeriodPoint :=
  sectionFour (tauFour z)

private theorem
    SpecialPeriods.localThree_admissible {z : ℂ} (hz : ‖z‖ < 1) : (localThree z).Admissible :=
  sectionThree_admissible (tauThree_im_pos hz)

private theorem
    SpecialPeriods.localFour_admissible {z : ℂ} (hz : ‖z‖ < 1) : (localFour z).Admissible :=
  sectionFour_admissible (tauFour_im_pos hz)

private theorem SpecialPeriods.localThree_rotate {z : ℂ} (hz : ‖z‖ < 1) :
    localThree (rotateThree z) = (localThree z).step₁ := by
  rw [localThree, tauThree_rotate hz]
  exact (sectionThree_step _ (tauThree_ne_zero hz)).symm

private theorem SpecialPeriods.localFour_rotate {z : ℂ} (hz : ‖z‖ < 1) :
    localFour (rotateFour z) = (localFour z).step₂ := by
  rw [localFour, tauFour_rotate hz]
  exact (sectionFour_step _ (tauFour_ne_zero hz)).symm

/-- The open unit disc in the complex plane. -/
public
def SpecialPeriods.unitDisc : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- The complex open unit disc as a subtype. -/
public
abbrev SpecialPeriods.Disc :=
  unitDisc

private theorem SpecialPeriods.disc_norm_lt_one (z : Disc) : ‖(z : ℂ)‖ < 1 := by
  simpa [unitDisc] using z.property

private theorem SpecialPeriods.tauThree_holomorphic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : Disc => tauThree z) :=
  tauThree_contDiffOn.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)

private theorem SpecialPeriods.tauFour_holomorphic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : Disc => tauFour z) :=
  tauFour_contDiffOn.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)

private def SpecialPeriods.threePeriodMap : HolomorphicPeriodMap ℂ Disc
    where
  point z := ⟨localThree z, localThree_admissible (disc_norm_lt_one z)⟩
  holomorphic_tau := tauThree_holomorphic
  holomorphic_mu := (contMDiff_const.sub tauThree_holomorphic).div_const 3
  holomorphic_beta := ((contMDiff_const.mul tauThree_holomorphic).div_const 3).sub contMDiff_const

private def SpecialPeriods.fourPeriodMap : HolomorphicPeriodMap ℂ Disc
    where
  point z := ⟨localFour z, localFour_admissible (disc_norm_lt_one z)⟩
  holomorphic_tau := tauFour_holomorphic
  holomorphic_mu := (contMDiff_const.sub tauFour_holomorphic).div_const 2
  holomorphic_beta := ((contMDiff_const.mul tauFour_holomorphic).div_const 2).sub contMDiff_const

private def SpecialPeriods.discZero : Disc :=
  ⟨0, by simp [unitDisc]⟩

@[simp]
private theorem SpecialPeriods.discZero_val : (discZero : ℂ) = 0 :=
  rfl

private def SpecialPeriods.discScalar (c : ℂ) (hc : ‖c‖ = 1) (z : Disc) : Disc :=
  ⟨c * z, by
    have hn : ‖c * (z : ℂ)‖ < 1 := by simpa [norm_mul, hc] using disc_norm_lt_one z
    simpa [unitDisc] using hn⟩

@[simp]
private theorem SpecialPeriods.discScalar_val (c : ℂ) (hc : ‖c‖ = 1) (z : Disc) :
    (discScalar c hc z : ℂ) = c * z :=
  rfl

private theorem SpecialPeriods.discScalar_holomorphic (c : ℂ) (hc : ‖c‖ = 1) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (discScalar c hc) := by
  intro z
  have he :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun w : Disc => (discScalar c hc w : ℂ)) z ↔
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (discScalar c hc) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((contMDiff_const.mul contMDiff_subtype_val) z)

private theorem SpecialPeriods.discScalar_iterate_val (c : ℂ) (hc : ‖c‖ = 1) (n : ℕ) (z : Disc) :
    ((discScalar c hc)^[n] z : ℂ) = c ^ n * z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', discScalar_val, ih, pow_succ']
    rw [mul_assoc]

private def SpecialPeriods.discRotateThree : Disc → Disc :=
  discScalar (-rho) (by simpa using norm_rho)

private def SpecialPeriods.discRotateFour : Disc → Disc :=
  discScalar (-Complex.I) (by simp)

private theorem SpecialPeriods.discRotateThree_holomorphic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω discRotateThree :=
  discScalar_holomorphic _ _

private theorem
    SpecialPeriods.discRotateFour_holomorphic : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω discRotateFour :=
  discScalar_holomorphic _ _

private theorem SpecialPeriods.discRotateThree_cube (z : Disc) :
    discRotateThree (discRotateThree (discRotateThree z)) = z :=
  Subtype.ext (rotateThree_cube z)

private theorem SpecialPeriods.discRotateFour_fourth (z : Disc) :
    discRotateFour (discRotateFour (discRotateFour (discRotateFour z))) = z :=
  Subtype.ext (rotateFour_fourth z)

private theorem SpecialPeriods.discRotateThree_iterate_order : discRotateThree^[3] = id := by
  funext z
  exact discRotateThree_cube z

private theorem SpecialPeriods.discRotateFour_iterate_order : discRotateFour^[4] = id := by
  funext z
  exact discRotateFour_fourth z

private def SpecialPeriods.threeRotation : Diffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) Disc Disc ω
    where
  toFun := discRotateThree
  invFun := discRotateThree ∘ discRotateThree
  left_inv := discRotateThree_cube
  right_inv := discRotateThree_cube
  contMDiff_toFun := discRotateThree_holomorphic
  contMDiff_invFun := discRotateThree_holomorphic.comp discRotateThree_holomorphic

private def SpecialPeriods.fourRotation : Diffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) Disc Disc ω
    where
  toFun := discRotateFour
  invFun := discRotateFour ∘ discRotateFour ∘ discRotateFour
  left_inv := discRotateFour_fourth
  right_inv := discRotateFour_fourth
  contMDiff_toFun := discRotateFour_holomorphic
  contMDiff_invFun :=
    discRotateFour_holomorphic.comp (discRotateFour_holomorphic.comp discRotateFour_holomorphic)

private theorem
    SpecialPeriods.neg_rho_pow_ne_one {n : ℕ} (hn : 0 < n) (hn' : n < 3) : (-rho) ^ n ≠ 1 := by
  interval_cases n
  · simp only [pow_one]
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.neg_im, Complex.one_im] at hh
    linarith [rho_im_pos]
  · rw [neg_sq, rho_sq]
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at hh
    linarith [rho_im_pos]

private theorem SpecialPeriods.neg_I_pow_ne_one {n : ℕ} (hn : 0 < n) (hn' : n < 4) :
    (-Complex.I) ^ n ≠ 1 := by
  interval_cases n
  · intro he
    have hh := congrArg Complex.im he
    norm_num at hh
  · norm_num
  · intro he
    have hh := congrArg Complex.im he
    norm_num [pow_succ] at hh

private theorem SpecialPeriods.discScalar_iterate_fixed_iff (c : ℂ) (hc : ‖c‖ = 1) (n : ℕ)
    (hn : c ^ n ≠ 1) (z : Disc) : (discScalar c hc)^[n] z = z ↔ z = discZero := by
  constructor
  · intro he
    apply Subtype.ext
    have hv := congrArg Subtype.val he
    rw [discScalar_iterate_val] at hv
    by_contra hz
    apply hn
    exact mul_right_cancel₀ hz (by simpa using hv)
  · intro he
    subst z
    apply Subtype.ext
    rw [discScalar_iterate_val]
    simp

private theorem SpecialPeriods.discRotateThree_iterate_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 3)
    (z : Disc) : discRotateThree^[n] z = z ↔ z = discZero :=
  discScalar_iterate_fixed_iff _ _ n (neg_rho_pow_ne_one hn hn') z

private theorem SpecialPeriods.discRotateFour_iterate_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 4)
    (z : Disc) : discRotateFour^[n] z = z ↔ z = discZero :=
  discScalar_iterate_fixed_iff _ _ n (neg_I_pow_ne_one hn hn') z

private theorem SpecialPeriods.threePeriodMap_rotate (z : Disc) :
    threePeriodMap.point (discRotateThree z) = (threePeriodMap.point z).step₁ :=
  Subtype.ext (localThree_rotate (disc_norm_lt_one z))

private theorem SpecialPeriods.fourPeriodMap_rotate (z : Disc) :
    fourPeriodMap.point (discRotateFour z) = (fourPeriodMap.point z).step₂ :=
  Subtype.ext (localFour_rotate (disc_norm_lt_one z))

private theorem SpecialPeriods.threePeriodMap_matrix_covariance (z : Disc) :
    (threePeriodMap.point (discRotateThree z)).val.matrix * A₁.map (Int.castRingHom ℂ) =
      (threePeriodMap.point z).val.R₁ * (threePeriodMap.point z).val.matrix := by
  rw [threePeriodMap_rotate]
  change (threePeriodMap.point z).val.step₁.matrix * _ = _
  rw [PeriodPoint.step₁_matrix _
      ((threePeriodMap.point z).val.τ_ne_zero (threePeriodMap.point z).property.1),
    Matrix.mul_assoc]
  have h : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
    change T₁.transpose.map (Int.castRingHom ℂ) * A₁.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₁.transpose * A₁ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

private theorem SpecialPeriods.fourPeriodMap_matrix_covariance (z : Disc) :
    (fourPeriodMap.point (discRotateFour z)).val.matrix * A₂.map (Int.castRingHom ℂ) =
      (fourPeriodMap.point z).val.R₂ * (fourPeriodMap.point z).val.matrix := by
  rw [fourPeriodMap_rotate]
  change (fourPeriodMap.point z).val.step₂.matrix * _ = _
  rw [PeriodPoint.step₂_matrix _
      ((fourPeriodMap.point z).val.τ_ne_zero (fourPeriodMap.point z).property.1),
    Matrix.mul_assoc]
  have h : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
    change T₂.transpose.map (Int.castRingHom ℂ) * A₂.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₂.transpose * A₂ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

end Mathoverflow1973

end
