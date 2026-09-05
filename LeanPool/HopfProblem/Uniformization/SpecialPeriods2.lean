/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SpecialPeriods3
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Foundations.LocalOrbitQuotient
import all LeanPool.HopfProblem.Threefold.SpecialPeriods3

/-!
# Hopf problem: uniformization · special periods 2

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

private def SpecialPeriods.Triangle.width : ℝ :=
  1 + Real.sqrt 2

private theorem SpecialPeriods.Triangle.width_pos : 0 < width := by
  unfold width
  positivity

private theorem SpecialPeriods.Triangle.one_lt_width : 1 < width := by
  unfold width
  have : 0 < Real.sqrt 2 := by positivity
  linarith

private theorem SpecialPeriods.Triangle.width_ne_zero : width ≠ 0 :=
  width_pos.ne'

private theorem SpecialPeriods.Triangle.width_sq : width ^ 2 = 2 * width + 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold width
  nlinarith

private theorem
    SpecialPeriods.Triangle.width_sub_one_sq : (width - 1) ^ 2 = 2 := by nlinarith [width_sq]

private def SpecialPeriods.Triangle.generatorOneSL : SL(2, ℝ) :=
  ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two_of]⟩

private def SpecialPeriods.Triangle.generatorTwoSL : SL(2, ℝ) :=
  ⟨!![1, width + 1; -1, -width], by simp [Matrix.det_fin_two_of]⟩

private def SpecialPeriods.Triangle.cuspInverseSL : SL(2, ℝ) :=
  ⟨!![1, width; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private def SpecialPeriods.Triangle.cuspSL : SL(2, ℝ) :=
  cuspInverseSL⁻¹

@[simp]
private theorem SpecialPeriods.Triangle.coe_generatorOneSL :
    (generatorOneSL : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 1] :=
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.coe_generatorTwoSL :
    (generatorTwoSL : Matrix (Fin 2) (Fin 2) ℝ) = !![1, width + 1; -1, -width] :=
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.coe_cuspSL :
    (cuspSL : Matrix (Fin 2) (Fin 2) ℝ) = !![1, -width; 0, 1] := by
  have hco : (cuspInverseSL : Matrix (Fin 2) (Fin 2) ℝ) = !![1, width; 0, 1] := rfl
  simp [hco, cuspSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

private theorem SpecialPeriods.Triangle.coe_generatorOneSL_sq :
    ((generatorOneSL ^ 2 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, -1; 1, 0] := by
  norm_num [Matrix.SpecialLinearGroup.coe_pow, pow_two, Matrix.mul_fin_two]

private theorem SpecialPeriods.Triangle.generatorOneSL_cube : generatorOneSL ^ 3 = -1 := by
  apply Subtype.ext
  norm_num [Matrix.SpecialLinearGroup.coe_pow, pow_succ, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

private theorem SpecialPeriods.Triangle.coe_generatorTwoSL_sq :
    ((generatorTwoSL ^ 2 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-width, -2 * width; width - 1, width] := by
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_generatorTwoSL, pow_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> nlinarith [width_sq]

private theorem SpecialPeriods.Triangle.generatorTwoSL_fourth : generatorTwoSL ^ 4 = -1 := by
  have hsq : (generatorTwoSL ^ 2) ^ 2 = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_generatorTwoSL_sq,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, pow_two,
      Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> nlinarith [width_sq]
  simpa only [← pow_mul] using hsq

private theorem SpecialPeriods.Triangle.generatorOneSL_mul_generatorTwoSL :
    generatorOneSL * generatorTwoSL = cuspInverseSL := by
  apply Subtype.ext
  simp [cuspInverseSL]

private theorem SpecialPeriods.Triangle.generatorOneSL_mul_generatorTwoSL_mul_cuspSL :
    generatorOneSL * generatorTwoSL * cuspSL = 1 := by
  rw [generatorOneSL_mul_generatorTwoSL, cuspSL, mul_inv_cancel]

private theorem SpecialPeriods.Triangle.cuspSL_inv : cuspSL⁻¹ = cuspInverseSL :=
  inv_inv _

private theorem SpecialPeriods.Triangle.sub_conj_ne_zero (a z : ℍ) :
    (z : ℂ) - starRingEnd ℂ (a : ℂ) ≠ 0 := by
  intro he
  have him := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im, UpperHalfPlane.coe_im] at him
  linarith [a.im_pos, z.im_pos]

private def SpecialPeriods.Triangle.cayleyCoordinate (a z : ℍ) : ℂ :=
  ((z : ℂ) - a) / ((z : ℂ) - starRingEnd ℂ (a : ℂ))

private theorem SpecialPeriods.Triangle.cayleyCoordinate_norm_lt_one (a z : ℍ) :
    ‖cayleyCoordinate a z‖ < 1 := by
  rw [cayleyCoordinate, norm_div]
  apply (div_lt_one (norm_pos_iff.mpr (sub_conj_ne_zero a z))).mpr
  have hsq : Complex.normSq ((z : ℂ) - a) < Complex.normSq ((z : ℂ) - starRingEnd ℂ (a : ℂ)) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
      Complex.conj_im, UpperHalfPlane.coe_im]
    nlinarith [mul_pos a.im_pos z.im_pos]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg ((z : ℂ) - a), norm_nonneg ((z : ℂ) - starRingEnd ℂ (a : ℂ))]

private def SpecialPeriods.Triangle.toDisc (a z : ℍ) : SpecialPeriods.Disc :=
  ⟨cayleyCoordinate a z, by
    simpa [SpecialPeriods.unitDisc] using cayleyCoordinate_norm_lt_one a z⟩

@[simp]
private theorem
    SpecialPeriods.Triangle.toDisc_val (a z : ℍ) : (toDisc a z : ℂ) = cayleyCoordinate a z :=
  rfl

private def SpecialPeriods.Triangle.fromDisc (a : ℍ) (z : SpecialPeriods.Disc) : ℍ :=
  UpperHalfPlane.ofComplex (SpecialPeriods.cayley a z)

@[simp]
private theorem SpecialPeriods.Triangle.fromDisc_val (a : ℍ) (z : SpecialPeriods.Disc) :
    (fromDisc a z : ℂ) = SpecialPeriods.cayley a z := by
  simp only [fromDisc,
    UpperHalfPlane.ofComplex_apply_of_im_pos
        (SpecialPeriods.cayley_im_pos a.im_pos (SpecialPeriods.disc_norm_lt_one z))]

@[simp]
private theorem SpecialPeriods.Triangle.toDisc_center (a : ℍ) :
    toDisc a a = (⟨0, by simp [SpecialPeriods.unitDisc]⟩ : SpecialPeriods.Disc) := by
  apply Subtype.ext
  simp [toDisc, cayleyCoordinate]

private theorem SpecialPeriods.Triangle.cayleyCoordinate_holomorphic (a : ℍ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyCoordinate a) :=
  (UpperHalfPlane.contMDiff_coe.sub contMDiff_const).div₀
    (UpperHalfPlane.contMDiff_coe.sub contMDiff_const) (sub_conj_ne_zero a)

private theorem
    SpecialPeriods.Triangle.toDisc_holomorphic (a : ℍ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toDisc a) := by
  intro z
  have he :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w : ℍ => (toDisc a w : ℂ)) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (toDisc a) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (cayleyCoordinate_holomorphic a z)

private theorem SpecialPeriods.Triangle.fromDisc_holomorphic (a : ℍ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fromDisc a) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : SpecialPeriods.Disc => SpecialPeriods.cayley a z) :=
    (SpecialPeriods.cayley_contDiffOn (a : ℂ)).contMDiffOn.comp_contMDiff contMDiff_subtype_val
      (fun z => z.property)
  intro z
  exact
    (UpperHalfPlane.contMDiffAt_ofComplex
          (SpecialPeriods.cayley_im_pos a.im_pos (SpecialPeriods.disc_norm_lt_one z))).comp
      z (hc z)

private theorem
    SpecialPeriods.Triangle.fromDisc_toDisc (a z : ℍ) : fromDisc a (toDisc a z) = z := by
  apply UpperHalfPlane.ext
  rw [fromDisc_val, toDisc_val]
  have hd := sub_conj_ne_zero a z
  have ha := sub_conj_ne_zero a a
  have hc := SpecialPeriods.one_sub_ne_zero_of_norm_lt_one (cayleyCoordinate_norm_lt_one a z)
  unfold SpecialPeriods.cayley cayleyCoordinate at *
  field_simp [hd, ha, hc]
  ring

private theorem SpecialPeriods.Triangle.toDisc_fromDisc (a : ℍ) (z : SpecialPeriods.Disc) :
    toDisc a (fromDisc a z) = z := by
  apply Subtype.ext
  rw [toDisc_val]
  unfold cayleyCoordinate
  rw [fromDisc_val]
  have hd := SpecialPeriods.one_sub_ne_zero_of_norm_lt_one (SpecialPeriods.disc_norm_lt_one z)
  have ha := sub_conj_ne_zero a a
  have hz := sub_conj_ne_zero a (fromDisc a z)
  rw [fromDisc_val] at hz
  unfold SpecialPeriods.cayley at *
  field_simp [hd, ha, hz]
  ring_nf
  field_simp [ha]

private def SpecialPeriods.Triangle.cayleyBiholomorph (a : ℍ) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℍ SpecialPeriods.Disc ω
    where
  toFun := toDisc a
  invFun := fromDisc a
  left_inv := fromDisc_toDisc a
  right_inv := toDisc_fromDisc a
  contMDiff_toFun := toDisc_holomorphic a
  contMDiff_invFun := fromDisc_holomorphic a

private def SpecialPeriods.Triangle.slDenom (g : SL(2, ℝ)) (z : ℂ) : ℂ :=
  (g 1 0 : ℂ) * z + (g 1 1 : ℂ)

private theorem SpecialPeriods.Triangle.slDenom_ne_zero (g : SL(2, ℝ)) (z : ℍ) : slDenom g z ≠ 0 :=
  UpperHalfPlane.linear_ne_zero z (g.row_ne_zero 1)

private theorem
    SpecialPeriods.Triangle.sl_fixed_equation (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    (g 0 0 : ℂ) * a + (g 0 1 : ℂ) = (a : ℂ) * slDenom g a := by
  have he := congrArg (fun z : ℍ => (z : ℂ)) hfix
  apply (div_eq_iff (slDenom_ne_zero g a)).mp
  simpa only [UpperHalfPlane.coe_specialLinearGroup_apply, Algebra.algebraMap_self,
    RingHom.id_apply, slDenom] using he

private theorem
    SpecialPeriods.Triangle.sl_fixed_conj_equation (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    (g 0 0 : ℂ) * starRingEnd ℂ (a : ℂ) + (g 0 1 : ℂ) =
      starRingEnd ℂ (a : ℂ) * slDenom g (starRingEnd ℂ (a : ℂ)) := by
  simpa [slDenom] using congrArg (starRingEnd ℂ) (sl_fixed_equation g a hfix)

private theorem SpecialPeriods.Triangle.sl_fixed_denominator_identity (g : SL(2, ℝ)) (a : ℍ)
    (hfix : g • a = a) : ((g 0 0 : ℂ) - (g 1 0 : ℂ) * (a : ℂ)) * slDenom g a = 1 := by
  have hdet : (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1 := by
    exact_mod_cast
      (show g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 from
        (Matrix.det_fin_two g.val).symm.trans g.property)
  have hf := sl_fixed_equation g a hfix
  unfold slDenom at *
  linear_combination (g 1 0 : ℂ) * hf + hdet

private theorem SpecialPeriods.Triangle.sl_fixed_conj_denominator (g : SL(2, ℝ)) (a : ℍ)
    (hfix : g • a = a) : (g 0 0 : ℂ) - (g 1 0 : ℂ) * starRingEnd ℂ (a : ℂ) = slDenom g a := by
  have hf := sl_fixed_equation g a hfix
  have him := congrArg Complex.im hf
  simp only [slDenom, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    MulZeroClass.zero_mul, add_zero, Complex.add_re, Complex.mul_re, sub_zero] at him
  have hr : g 0 0 = 2 * g 1 0 * (a : ℂ).re + g 1 1 := by
    apply mul_right_cancel₀ (show (a : ℂ).im ≠ 0 from a.im_ne_zero)
    calc
      g 0 0 * (a : ℂ).im =
          (a : ℂ).re * (g 1 0 * (a : ℂ).im) + (a : ℂ).im * (g 1 0 * (a : ℂ).re + g 1 1) :=
        him
      _ = (2 * g 1 0 * (a : ℂ).re + g 1 1) * (a : ℂ).im := by ring
  apply Complex.ext <;>
      simp only [slDenom, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im] <;>
    nlinarith [hr]

private theorem SpecialPeriods.Triangle.sl_fixed_denominator_norm (g : SL(2, ℝ)) (a : ℍ)
    (hfix : g • a = a) : ‖slDenom g a‖ = 1 := by
  have hc : starRingEnd ℂ (slDenom g a) = (g 0 0 : ℂ) - (g 1 0 : ℂ) * (a : ℂ) := by
    simpa only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_conj] using
      (congrArg (starRingEnd ℂ) (sl_fixed_conj_denominator g a hfix)).symm
  have hm : starRingEnd ℂ (slDenom g a) * slDenom g a = 1 := by
    rw [hc, sl_fixed_denominator_identity g a hfix]
  have hn := congrArg Norm.norm hm
  simp only [norm_mul, Complex.norm_conj, NormOneClass.norm_one] at hn
  nlinarith [norm_nonneg (slDenom g a)]

private def SpecialPeriods.Triangle.slMultiplier (g : SL(2, ℝ)) (a : ℍ) : ℂ :=
  1 / slDenom g a ^ 2

private theorem SpecialPeriods.Triangle.sl_hasStrictDerivAt_smul (g : SL(2, ℝ)) (a : ℍ) :
    HasStrictDerivAt (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (slMultiplier g a)
      (a : ℂ) := by
  have h :=
    UpperHalfPlane.hasStrictDerivAt_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by simp) a
  simpa [MulAction.compHom_smul_def, slMultiplier, slDenom, UpperHalfPlane.denom] using h

private theorem SpecialPeriods.Triangle.sl_deriv_smul (g : SL(2, ℝ)) (a : ℍ) :
    deriv (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (a : ℂ) = slMultiplier g a :=
  (sl_hasStrictDerivAt_smul g a).hasDerivAt.deriv

private theorem
    SpecialPeriods.Triangle.slMultiplier_norm (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    ‖slMultiplier g a‖ = 1 := by simp [slMultiplier, sl_fixed_denominator_norm g a hfix]

private theorem SpecialPeriods.Triangle.cayleyCoordinate_smul (g : SL(2, ℝ)) (a z : ℍ)
    (hfix : g • a = a) : cayleyCoordinate a (g • z) = slMultiplier g a * cayleyCoordinate a z := by
  have hd := slDenom_ne_zero g z
  have ha := slDenom_ne_zero g a
  have hn :
    ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / slDenom g z - (a : ℂ) =
      ((g 0 0 : ℂ) - (g 1 0 : ℂ) * (a : ℂ)) * ((z : ℂ) - a) / slDenom g z := by
    have hf := sl_fixed_equation g a hfix
    field_simp [hd]
    unfold slDenom at *
    linear_combination hf
  have hnbar :
    ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / slDenom g z - starRingEnd ℂ (a : ℂ) =
      ((g 0 0 : ℂ) - (g 1 0 : ℂ) * starRingEnd ℂ (a : ℂ)) * ((z : ℂ) - starRingEnd ℂ (a : ℂ)) /
        slDenom g z := by
    have hf := sl_fixed_conj_equation g a hfix
    field_simp [hd]
    unfold slDenom at *
    linear_combination hf
  have hcoef : ((g 0 0 : ℂ) - (g 1 0 : ℂ) * (a : ℂ)) / slDenom g a = slMultiplier g a := by
    rw [slMultiplier, div_eq_div_iff ha (pow_ne_zero 2 ha)]
    have hf := sl_fixed_denominator_identity g a hfix
    linear_combination slDenom g a * hf
  unfold cayleyCoordinate
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  change
    (((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / slDenom g z - (a : ℂ)) /
        (((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / slDenom g z - starRingEnd ℂ (a : ℂ)) =
      _
  rw [hn, hnbar, div_div_div_cancel_right₀ hd, sl_fixed_conj_denominator g a hfix,
    mul_div_mul_comm, hcoef]

/-- The homomorphism from a finite cyclic group generated by an element of bounded order. -/
public
def SpecialPeriods.cyclicPowerHom {G : Type*} [Group G] (n : ℕ) (a : G) (ha : a ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  (ZMod.lift n
      ⟨zmultiplesHom (Additive G) (Additive.ofMul a),
        by
        change a ^ (n : ℤ) = 1
        simpa only [zpow_natCast] using ha⟩).toMultiplicativeLeft

@[simp]
private theorem SpecialPeriods.cyclicPowerHom_intCast {G : Type*} [Group G] (n : ℕ) (a : G)
    (ha : a ^ n = 1) (k : ℤ) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (k : ZMod n)) = a ^ k := by simp [cyclicPowerHom]

@[simp]
private theorem
    SpecialPeriods.cyclicPowerHom_one {G : Type*} [Group G] (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (1 : ZMod n)) = a := by
  simpa using cyclicPowerHom_intCast n a ha 1

private theorem SpecialPeriods.cyclic_eq_generator_zpow_mo1973_15645 {n : ℕ}
    (x : Multiplicative (ZMod n)) : ∃ k : ℤ, x = Multiplicative.ofAdd (1 : ZMod n) ^ k := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective x.toAdd
  refine ⟨k, ?_⟩
  change x.toAdd = k • (1 : ZMod n)
  simpa using hk.symm

private theorem SpecialPeriods.cyclic_hom_ext_mo1973_15646 {G : Type*} [Group G] {n : ℕ}
    {f g : Multiplicative (ZMod n) →* G}
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨k, rfl⟩ := cyclic_eq_generator_zpow_mo1973_15645 x
  rw [map_zpow, map_zpow, h]

/-- The free product of cyclic groups of orders three and four. -/
public
abbrev SpecialPeriods.TriangleGroup :=
  Monoid.Coprod (Multiplicative (ZMod 3)) (Multiplicative (ZMod 4))

private def SpecialPeriods.triangleGenerator₁ : TriangleGroup :=
  Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 3))

private def SpecialPeriods.triangleGenerator₂ : TriangleGroup :=
  Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4))

private def SpecialPeriods.triangleCuspGenerator : TriangleGroup :=
  (triangleGenerator₁ * triangleGenerator₂)⁻¹

private theorem SpecialPeriods.triangleGenerator₁_order : orderOf triangleGenerator₁ = 3 := by
  rw [triangleGenerator₁, orderOf_injective _ Monoid.Coprod.inl_injective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

private theorem SpecialPeriods.triangleGenerator₂_order : orderOf triangleGenerator₂ = 4 := by
  rw [triangleGenerator₂, orderOf_injective _ Monoid.Coprod.inr_injective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

@[simp]
private theorem SpecialPeriods.triangleGenerator₁_cube : triangleGenerator₁ ^ 3 = 1 := by
  simpa only [triangleGenerator₁_order] using pow_orderOf_eq_one triangleGenerator₁

private theorem SpecialPeriods.triangle_generators_generate :
    Subgroup.closure ({ triangleGenerator₁, triangleGenerator₂ } : Set TriangleGroup) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using Monoid.Coprod.induction_on with
  | inl x =>
    obtain ⟨k, rfl⟩ := cyclic_eq_generator_zpow_mo1973_15645 x
    rw [map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp [triangleGenerator₁])) k
  | inr x =>
    obtain ⟨k, rfl⟩ := cyclic_eq_generator_zpow_mo1973_15645 x
    rw [map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp [triangleGenerator₂])) k
  | mul x y hx hy => exact Subgroup.mul_mem _ hx hy

/-- The triangle-group homomorphism determined by elements of orders three and four. -/
public
def SpecialPeriods.triangleLift {G : Type*} [Group G] (a b : G) (ha : a ^ 3 = 1)
    (hb : b ^ 4 = 1) : TriangleGroup →* G :=
  Monoid.Coprod.lift (cyclicPowerHom 3 a ha) (cyclicPowerHom 4 b hb)

@[simp]
private theorem
    SpecialPeriods.triangleLift_generator₁ {G : Type*} [Group G] (a b : G) (ha : a ^ 3 = 1)
    (hb : b ^ 4 = 1) : triangleLift a b ha hb triangleGenerator₁ = a := by
  simp [triangleLift, triangleGenerator₁]

@[simp]
private theorem
    SpecialPeriods.triangleLift_generator₂ {G : Type*} [Group G] (a b : G) (ha : a ^ 3 = 1)
    (hb : b ^ 4 = 1) : triangleLift a b ha hb triangleGenerator₂ = b := by
  simp [triangleLift, triangleGenerator₂]

@[simp]
private theorem SpecialPeriods.triangleLift_cusp {G : Type*} [Group G] (a b : G) (ha : a ^ 3 = 1)
    (hb : b ^ 4 = 1) : triangleLift a b ha hb triangleCuspGenerator = (a * b)⁻¹ := by
  simp [triangleCuspGenerator]

private theorem SpecialPeriods.triangle_hom_ext {G : Type*} [Group G] {f g : TriangleGroup →* G}
    (h₁ : f triangleGenerator₁ = g triangleGenerator₁)
    (h₂ : f triangleGenerator₂ = g triangleGenerator₂) : f = g := by
  apply Monoid.Coprod.hom_ext
  · exact cyclic_hom_ext_mo1973_15646 h₁
  · exact cyclic_hom_ext_mo1973_15646 h₂

private theorem SpecialPeriods.triangle_range {G : Type*} [Group G] (f : TriangleGroup →* G) :
    f.range = Subgroup.closure ({f triangleGenerator₁, f triangleGenerator₂} : Set G) := by
  rw [MonoidHom.range_eq_map, ← triangle_generators_generate, MonoidHom.map_closure,
    Set.image_pair]

/-- The first special-linear lattice generator, of order three. -/
public
def SpecialPeriods.triangleLatticeT₁ : SL(4, ℤ) :=
  ⟨T₁, det_T₁⟩

/-- The second special-linear lattice generator, of order four. -/
public
def SpecialPeriods.triangleLatticeT₂ : SL(4, ℤ) :=
  ⟨T₂, det_T₂⟩

public
theorem SpecialPeriods.triangleLatticeT₁_cube : triangleLatticeT₁ ^ 3 = 1 :=
  Subtype.ext T₁_cube

public
theorem SpecialPeriods.triangleLatticeT₂_fourth : triangleLatticeT₂ ^ 4 = 1 :=
  Subtype.ext T₂_fourth

/-- The special-linear representation of the triangle group on the lattice. -/
public
def SpecialPeriods.triangleLatticeRepresentation : TriangleGroup →* SL(4, ℤ) :=
  triangleLift triangleLatticeT₁ triangleLatticeT₂ triangleLatticeT₁_cube triangleLatticeT₂_fourth

@[simp]
private theorem SpecialPeriods.triangleLatticeRepresentation_generator₁ :
    triangleLatticeRepresentation triangleGenerator₁ = triangleLatticeT₁ :=
  triangleLift_generator₁ ..

@[simp]
private theorem SpecialPeriods.triangleLatticeRepresentation_generator₂ :
    triangleLatticeRepresentation triangleGenerator₂ = triangleLatticeT₂ :=
  triangleLift_generator₂ ..

private theorem SpecialPeriods.triangleLatticeRepresentation_cusp_matrix :
    (triangleLatticeRepresentation triangleCuspGenerator : LatticeMatrix) = T₀ := by
  rw [triangleLatticeRepresentation, triangleLift_cusp]
  decide

/-- The contragredient automorphism of the special linear lattice group. -/
public
def SpecialPeriods.latticeContragredient : SL(4, ℤ) →* SL(4, ℤ)
    where
  toFun A := Matrix.SpecialLinearGroup.transpose A⁻¹
  map_one' := Subtype.ext (by simp [Matrix.SpecialLinearGroup.transpose])
  map_mul' A
    B :=
    Subtype.ext
      (by
        change
          (((A * B)⁻¹ : SL(4, ℤ)) : LatticeMatrix).transpose =
            ((A⁻¹ : SL(4, ℤ)) : LatticeMatrix).transpose *
              ((B⁻¹ : SL(4, ℤ)) : LatticeMatrix).transpose
        simp only [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul])

/-- The contragredient triangle-group representation on the lattice. -/
public
def SpecialPeriods.triangleDualRepresentation : TriangleGroup →* SL(4, ℤ) :=
  latticeContragredient.comp triangleLatticeRepresentation

private theorem SpecialPeriods.triangleDualRepresentation_generator₁_matrix :
    (triangleDualRepresentation triangleGenerator₁ : LatticeMatrix) = A₁ := by
  rw [triangleDualRepresentation, MonoidHom.comp_apply, triangleLatticeRepresentation_generator₁]
  decide

private theorem SpecialPeriods.triangleDualRepresentation_generator₂_matrix :
    (triangleDualRepresentation triangleGenerator₂ : LatticeMatrix) = A₂ := by
  rw [triangleDualRepresentation, MonoidHom.comp_apply, triangleLatticeRepresentation_generator₂]
  decide

private theorem SpecialPeriods.triangleDualRepresentation_cusp_matrix :
    (triangleDualRepresentation triangleCuspGenerator : LatticeMatrix) = M₀ := by
  change
    (Matrix.adjugate
          (triangleLatticeRepresentation triangleCuspGenerator : LatticeMatrix)).transpose =
      M₀
  rw [triangleLatticeRepresentation_cusp_matrix]
  decide

private def SpecialPeriods.Triangle.realSLPermutation : SL(2, ℝ) →* Equiv.Perm ℍ :=
  MulAction.toPermHom (SL(2, ℝ)) ℍ

@[simp]
private theorem SpecialPeriods.Triangle.realSLPermutation_apply (A : SL(2, ℝ)) (z : ℍ) :
    realSLPermutation A z = A • z :=
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.realSLPermutation_neg_one : realSLPermutation (-1) = 1 := by
  apply Equiv.ext
  intro z
  apply UpperHalfPlane.ext
  change (((-1 : SL(2, ℝ)) • z : ℍ) : ℂ) = z
  norm_num [UpperHalfPlane.coe_specialLinearGroup_apply, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]

private def SpecialPeriods.Triangle.generatorOnePerm : Equiv.Perm ℍ :=
  realSLPermutation generatorOneSL

private def SpecialPeriods.Triangle.generatorTwoPerm : Equiv.Perm ℍ :=
  realSLPermutation generatorTwoSL

private theorem SpecialPeriods.Triangle.generatorOnePerm_cube : generatorOnePerm ^ 3 = 1 := by
  rw [generatorOnePerm, ← map_pow, generatorOneSL_cube, realSLPermutation_neg_one]

private theorem SpecialPeriods.Triangle.generatorTwoPerm_fourth : generatorTwoPerm ^ 4 = 1 := by
  rw [generatorTwoPerm, ← map_pow, generatorTwoSL_fourth, realSLPermutation_neg_one]

private def SpecialPeriods.Triangle.horizontalTranslation : Multiplicative ℝ →* Equiv.Perm ℍ :=
  (AddAction.toPermHom ℝ ℍ).toMultiplicativeLeft

@[simp]
private theorem SpecialPeriods.Triangle.horizontalTranslation_apply (t : ℝ) (z : ℍ) :
    horizontalTranslation (Multiplicative.ofAdd t) z = t +ᵥ z :=
  rfl

private theorem SpecialPeriods.Triangle.cuspSL_apply (z : ℍ) : cuspSL • z = (-width) +ᵥ z := by
  apply UpperHalfPlane.ext
  simp [UpperHalfPlane.coe_specialLinearGroup_apply, coe_cuspSL, add_comm]

private theorem SpecialPeriods.Triangle.cuspSL_permutation_eq_translation :
    realSLPermutation cuspSL = horizontalTranslation (Multiplicative.ofAdd (-width)) := by
  apply Equiv.ext
  exact cuspSL_apply

private def SpecialPeriods.triangleGeometricRepresentation : TriangleGroup →* Equiv.Perm ℍ :=
  triangleLift Triangle.generatorOnePerm Triangle.generatorTwoPerm Triangle.generatorOnePerm_cube
    Triangle.generatorTwoPerm_fourth

@[instance_reducible]
private def SpecialPeriods.triangleGeometricAction : MulAction TriangleGroup ℍ :=
  MulAction.compHom ℍ triangleGeometricRepresentation

private theorem SpecialPeriods.triangleGeometricAction_smul (g : TriangleGroup) (z : ℍ) :
    letI := triangleGeometricAction
    g • z = triangleGeometricRepresentation g z :=
  rfl

@[simp]
private theorem SpecialPeriods.triangleGeometricRepresentation_generator₁ :
    triangleGeometricRepresentation triangleGenerator₁ = Triangle.generatorOnePerm :=
  triangleLift_generator₁ ..

@[simp]
private theorem SpecialPeriods.triangleGeometricRepresentation_generator₂ :
    triangleGeometricRepresentation triangleGenerator₂ = Triangle.generatorTwoPerm :=
  triangleLift_generator₂ ..

private theorem SpecialPeriods.triangleGeometricRepresentation_generator₁_apply (z : ℍ) :
    triangleGeometricRepresentation triangleGenerator₁ z = Triangle.generatorOneSL • z := by
  rw [triangleGeometricRepresentation_generator₁]
  rfl

private theorem SpecialPeriods.triangleGeometricRepresentation_generator₂_apply (z : ℍ) :
    triangleGeometricRepresentation triangleGenerator₂ z = Triangle.generatorTwoSL • z := by
  rw [triangleGeometricRepresentation_generator₂]
  rfl

private theorem SpecialPeriods.triangleGeometricRepresentation_has_SL_lift (g : TriangleGroup) :
    ∃ A : SL(2, ℝ), Triangle.realSLPermutation A = triangleGeometricRepresentation g := by
  have hr : triangleGeometricRepresentation.range ≤ Triangle.realSLPermutation.range := by
    rw [triangle_range]
    apply (Subgroup.closure_le _).mpr
    intro p hp
    rcases hp with rfl | rfl
    · exact ⟨Triangle.generatorOneSL, triangleGeometricRepresentation_generator₁.symm⟩
    · exact ⟨Triangle.generatorTwoSL, triangleGeometricRepresentation_generator₂.symm⟩
  exact hr ⟨g, rfl⟩

private theorem SpecialPeriods.triangleGeometricRepresentation_cusp :
    triangleGeometricRepresentation triangleCuspGenerator =
      Triangle.realSLPermutation Triangle.cuspSL := by
  rw [triangleGeometricRepresentation, triangleLift_cusp, Triangle.generatorOnePerm,
    Triangle.generatorTwoPerm, ← map_mul, Triangle.generatorOneSL_mul_generatorTwoSL, ← map_inv]
  rfl

private theorem SpecialPeriods.triangleGeometricRepresentation_cusp_eq_translation :
    triangleGeometricRepresentation triangleCuspGenerator =
      Triangle.horizontalTranslation (Multiplicative.ofAdd (-Triangle.width)) :=
  triangleGeometricRepresentation_cusp.trans Triangle.cuspSL_permutation_eq_translation

@[simp]
private theorem SpecialPeriods.triangleGeometricRepresentation_cusp_apply (z : ℍ) :
    triangleGeometricRepresentation triangleCuspGenerator z = (-Triangle.width) +ᵥ z := by
  rw [triangleGeometricRepresentation_cusp_eq_translation]
  rfl

private theorem SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_apply (n : ℤ) (z : ℍ) :
    triangleGeometricRepresentation (triangleCuspGenerator ^ n) z =
      (-(n : ℝ) * Triangle.width) +ᵥ z := by
  rw [map_zpow, triangleGeometricRepresentation_cusp_eq_translation, ← map_zpow, ← ofAdd_zsmul,
    Triangle.horizontalTranslation_apply]
  congr 1
  simp only [zsmul_eq_mul, mul_neg, neg_mul]

private theorem SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_coe (n : ℤ) (z : ℍ) :
    (triangleGeometricRepresentation (triangleCuspGenerator ^ n) z : ℂ) =
      z - (n : ℂ) * Triangle.width := by
  rw [triangleGeometricRepresentation_cusp_zpow_apply, UpperHalfPlane.coe_vadd]
  push_cast
  ring

private theorem SpecialPeriods.triangleGeometricRepresentation_cusp_orbit_injective (z : ℍ) :
    Function.Injective
      (fun n : ℤ => triangleGeometricRepresentation (triangleCuspGenerator ^ n) z) := by
  intro m n h
  simp only [triangleGeometricRepresentation_cusp_zpow_apply] at h
  have he := (UpperHalfPlane.vadd_right_cancel_iff z).mp h
  have hmn := neg_injective (mul_right_cancel₀ Triangle.width_ne_zero he)
  exact_mod_cast hmn

private theorem SpecialPeriods.Triangle.specialLinear_holomorphic (g : SL(2, ℝ)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℍ => g • z) := by
  exact UpperHalfPlane.contMDiff_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by simp)

private def SpecialPeriods.Triangle.centerOne : ℍ :=
  ⟨SpecialPeriods.rho - 1, by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using SpecialPeriods.rho_im_pos⟩

private def SpecialPeriods.Triangle.centerTwo : ℍ :=
  ⟨-((width : ℂ) + 1) / 2 + ((width : ℂ) - 1) / 2 * Complex.I,
    by
    simp only [Complex.add_im, Complex.div_ofNat_im, Complex.neg_im, Complex.add_im,
      Complex.ofReal_im, Complex.one_im, Complex.sub_im, Complex.mul_im, Complex.div_ofNat_re,
      Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.I_im, Complex.I_re]
    linarith [one_lt_width]⟩

@[simp]
private theorem SpecialPeriods.Triangle.centerOne_val : (centerOne : ℂ) = SpecialPeriods.rho - 1 :=
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.centerTwo_val :
    (centerTwo : ℂ) = -((width : ℂ) + 1) / 2 + ((width : ℂ) - 1) / 2 * Complex.I :=
  rfl

private theorem SpecialPeriods.Triangle.centerTwo_re : centerTwo.re = -(width + 1) / 2 := by
  simp [UpperHalfPlane.re, centerTwo]

private theorem SpecialPeriods.Triangle.centerTwo_im : centerTwo.im = (width - 1) / 2 := by
  simp [UpperHalfPlane.im, centerTwo]

private theorem SpecialPeriods.Triangle.width_complex_sq : (width : ℂ) ^ 2 = 2 * width + 1 := by
  exact_mod_cast width_sq

private theorem SpecialPeriods.Triangle.generatorOne_coe (z : ℍ) :
    ((generatorOneSL • z : ℍ) : ℂ) = -1 / ((z : ℂ) + 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [generatorOneSL]

private theorem SpecialPeriods.Triangle.generatorTwo_coe (z : ℍ) :
    ((generatorTwoSL • z : ℍ) : ℂ) = ((z : ℂ) + (width : ℂ) + 1) / (-(z : ℂ) - width) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [generatorTwoSL, add_assoc, sub_eq_add_neg]

private theorem SpecialPeriods.Triangle.denominatorOne_ne_zero (z : ℍ) : (z : ℂ) + 1 ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.add_im, Complex.one_im, Complex.zero_im, add_zero,
    UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

private theorem SpecialPeriods.Triangle.denominatorTwo_ne_zero (z : ℍ) : -(z : ℂ) - width ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, sub_zero, Complex.zero_im,
    neg_eq_zero, UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

private theorem SpecialPeriods.Triangle.centerTwo_polynomial :
    (centerTwo : ℂ) ^ 2 + ((width : ℂ) + 1) * centerTwo + ((width : ℂ) + 1) = 0 := by
  rw [centerTwo_val]
  calc
    _ =
        -((width : ℂ) + 1) ^ 2 / 4 + ((width : ℂ) - 1) ^ 2 / 4 * Complex.I ^ 2 +
          ((width : ℂ) + 1) := by ring
    _ = -((width : ℂ) ^ 2 - 2 * width - 1) / 2 := by rw [Complex.I_sq]; ring
    _ = 0 := by rw [width_complex_sq]; ring

@[simp]
private theorem
    SpecialPeriods.Triangle.generatorOne_fix : generatorOneSL • centerOne = centerOne := by
  apply UpperHalfPlane.ext
  rw [generatorOne_coe, centerOne_val]
  have hd : SpecialPeriods.rho ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.zero_im] at hi
    exact (ne_of_gt SpecialPeriods.rho_im_pos) hi
  simp only [sub_add_cancel]
  apply (div_eq_iff hd).mpr
  linear_combination -SpecialPeriods.rho_sq

@[simp]
private theorem
    SpecialPeriods.Triangle.generatorTwo_fix : generatorTwoSL • centerTwo = centerTwo := by
  apply UpperHalfPlane.ext
  rw [generatorTwo_coe]
  apply (div_eq_iff (denominatorTwo_ne_zero centerTwo)).mpr
  linear_combination centerTwo_polynomial

private theorem SpecialPeriods.Triangle.generatorOne_derivative_coefficient :
    1 / ((centerOne : ℂ) + 1) ^ 2 = -SpecialPeriods.rho := by
  rw [centerOne_val, sub_add_cancel]
  apply
    (div_eq_iff
        (pow_ne_zero 2
          (by
            intro he
            have hi := congrArg Complex.im he
            simp only [Complex.zero_im] at hi
            exact (ne_of_gt SpecialPeriods.rho_im_pos) hi))).mpr
  linear_combination SpecialPeriods.rho_cube

private theorem SpecialPeriods.Triangle.generatorTwo_denominator_sq :
    (-(centerTwo : ℂ) - width) ^ 2 = Complex.I := by
  rw [centerTwo_val]
  calc
    _ = ((width : ℂ) - 1) ^ 2 / 4 * (1 + 2 * Complex.I + Complex.I ^ 2) := by ring
    _ = Complex.I := by
      rw [Complex.I_sq]
      have hs : ((width : ℂ) - 1) ^ 2 = 2 := by exact_mod_cast width_sub_one_sq
      rw [hs]
      ring

private theorem SpecialPeriods.Triangle.generatorTwo_derivative_coefficient :
    1 / (-(centerTwo : ℂ) - width) ^ 2 = -Complex.I := by
  rw [generatorTwo_denominator_sq]
  simp

private theorem SpecialPeriods.Triangle.generatorOne_multiplier :
    slMultiplier generatorOneSL centerOne = -SpecialPeriods.rho := by
  simpa [slMultiplier, slDenom, generatorOneSL] using generatorOne_derivative_coefficient

private theorem SpecialPeriods.Triangle.generatorTwo_multiplier :
    slMultiplier generatorTwoSL centerTwo = -Complex.I := by
  simpa [slMultiplier, slDenom, generatorTwoSL, sub_eq_add_neg] using
    generatorTwo_derivative_coefficient

private theorem SpecialPeriods.Triangle.generatorTwo_hasStrictDerivAt :
    HasStrictDerivAt (fun z : ℂ => ((generatorTwoSL • UpperHalfPlane.ofComplex z : ℍ) : ℂ))
      (-Complex.I) (centerTwo : ℂ) := by
  rw [← generatorTwo_multiplier]
  exact sl_hasStrictDerivAt_smul _ _

private theorem SpecialPeriods.Triangle.generatorOne_cayley (z : ℍ) :
    cayleyCoordinate centerOne (generatorOneSL • z) =
      -SpecialPeriods.rho * cayleyCoordinate centerOne z := by
  rw [cayleyCoordinate_smul _ _ _ generatorOne_fix, generatorOne_multiplier]

private theorem SpecialPeriods.Triangle.generatorTwo_cayley (z : ℍ) :
    cayleyCoordinate centerTwo (generatorTwoSL • z) = -Complex.I * cayleyCoordinate centerTwo z :=
  by rw [cayleyCoordinate_smul _ _ _ generatorTwo_fix, generatorTwo_multiplier]

private theorem SpecialPeriods.Triangle.generatorOne_toDisc (z : ℍ) :
    toDisc centerOne (generatorOneSL • z) = SpecialPeriods.discRotateThree (toDisc centerOne z) :=
  by
  apply Subtype.ext
  exact generatorOne_cayley z

private theorem SpecialPeriods.Triangle.generatorTwo_toDisc (z : ℍ) :
    toDisc centerTwo (generatorTwoSL • z) = SpecialPeriods.discRotateFour (toDisc centerTwo z) := by
  apply Subtype.ext
  exact generatorTwo_cayley z

private theorem SpecialPeriods.Triangle.generatorOne_pow_toDisc (n : ℕ) (z : ℍ) :
    toDisc centerOne (generatorOneSL ^ n • z) =
      SpecialPeriods.discRotateThree^[n] (toDisc centerOne z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', SemigroupAction.mul_smul, generatorOne_toDisc, ih,
      Function.iterate_succ_apply']

private theorem SpecialPeriods.Triangle.generatorTwo_pow_toDisc (n : ℕ) (z : ℍ) :
    toDisc centerTwo (generatorTwoSL ^ n • z) =
      SpecialPeriods.discRotateFour^[n] (toDisc centerTwo z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', SemigroupAction.mul_smul, generatorTwo_toDisc, ih,
      Function.iterate_succ_apply']

private theorem
    SpecialPeriods.Triangle.generatorOne_pow_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 3)
    (z : ℍ) : generatorOneSL ^ n • z = z ↔ z = centerOne := by
  have he :
    generatorOneSL ^ n • z = z ↔ toDisc centerOne (generatorOneSL ^ n • z) = toDisc centerOne z :=
    (cayleyBiholomorph centerOne).injective.eq_iff.symm
  rw [he, generatorOne_pow_toDisc, SpecialPeriods.discRotateThree_iterate_fixed_iff n hn hn']
  have hc : toDisc centerOne centerOne = SpecialPeriods.discZero := toDisc_center _
  rw [← hc]
  exact (cayleyBiholomorph centerOne).injective.eq_iff

private theorem
    SpecialPeriods.Triangle.generatorTwo_pow_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 4)
    (z : ℍ) : generatorTwoSL ^ n • z = z ↔ z = centerTwo := by
  have he :
    generatorTwoSL ^ n • z = z ↔ toDisc centerTwo (generatorTwoSL ^ n • z) = toDisc centerTwo z :=
    (cayleyBiholomorph centerTwo).injective.eq_iff.symm
  rw [he, generatorTwo_pow_toDisc, SpecialPeriods.discRotateFour_iterate_fixed_iff n hn hn']
  have hc : toDisc centerTwo centerTwo = SpecialPeriods.discZero := toDisc_center _
  rw [← hc]
  exact (cayleyBiholomorph centerTwo).injective.eq_iff

private theorem SpecialPeriods.triangleGeometricRepresentation_holomorphic (g : TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (triangleGeometricRepresentation g : ℍ → ℍ) := by
  obtain ⟨A, hA⟩ := triangleGeometricRepresentation_has_SL_lift g
  rw [← hA]
  exact Triangle.specialLinear_holomorphic A

private def
    SpecialPeriods.triangleGeometricBiholomorph (g : TriangleGroup) : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℍ ℍ ω
    where
  toEquiv := triangleGeometricRepresentation g
  contMDiff_toFun := triangleGeometricRepresentation_holomorphic g
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (((triangleGeometricRepresentation g)⁻¹ : Equiv.Perm ℍ) : ℍ → ℍ)
    rw [← map_inv]
    exact triangleGeometricRepresentation_holomorphic g⁻¹

private def SpecialPeriods.Triangle.stripLeft : ℝ :=
  -(width + 1) / 2

private def SpecialPeriods.Triangle.stripRight : ℝ :=
  (width - 1) / 2

private theorem SpecialPeriods.Triangle.strip_width : stripRight - stripLeft = width := by
  unfold stripRight stripLeft
  ring

private theorem SpecialPeriods.Triangle.stripRight_pos : 0 < stripRight := by
  unfold stripRight
  linarith [one_lt_width]

private theorem SpecialPeriods.Triangle.stripRight_sq : stripRight ^ 2 = 1 / 2 := by
  unfold stripRight
  nlinarith [width_sub_one_sq]

private theorem SpecialPeriods.Triangle.half_lt_stripRight : 1 / 2 < stripRight := by
  nlinarith [stripRight_sq, stripRight_pos]

private def SpecialPeriods.Triangle.fordRegion : Set ℍ :=
  {z | stripLeft ≤ z.re ∧ z.re ≤ stripRight ∧ 1 ≤ ‖(z : ℂ) + 1‖ ∧ 1 ≤ ‖(z : ℂ)‖}

private theorem SpecialPeriods.Triangle.fordRegion_closed : IsClosed fordRegion :=
  (isClosed_le continuous_const UpperHalfPlane.continuous_re).inter
    ((isClosed_le UpperHalfPlane.continuous_re continuous_const).inter
      ((isClosed_le continuous_const
            ((UpperHalfPlane.continuous_coe.add continuous_const).norm)).inter
        (isClosed_le continuous_const UpperHalfPlane.continuous_coe.norm)))

private theorem SpecialPeriods.Triangle.mem_fordRegion_of_one_le_im (z : ℍ) (hl : stripLeft ≤ z.re)
    (hr : z.re ≤ stripRight) (hi : 1 ≤ z.im) : z ∈ fordRegion := by
  refine ⟨hl, hr, ?_, ?_⟩
  · have hh := Complex.im_le_norm ((z : ℂ) + 1)
    simp only [Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_im] at hh
    exact hi.trans hh
  · exact hi.trans (Complex.im_le_norm (z : ℂ))

private theorem SpecialPeriods.Triangle.exists_cusp_translate_in_strip (z : ℍ) :
    ∃ n : ℤ,
      stripLeft ≤ ((-(n : ℝ) * width) +ᵥ z).re ∧ ((-(n : ℝ) * width) +ᵥ z).re < stripRight := by
  let n : ℤ := ⌊(z.re - stripLeft) / width⌋
  have hlo : (n : ℝ) ≤ (z.re - stripLeft) / width := Int.floor_le _
  have hhi : (z.re - stripLeft) / width < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hlo' := (le_div_iff₀ width_pos).mp hlo
  have hhi' := (div_lt_iff₀ width_pos).mp hhi
  refine ⟨n, ?_, ?_⟩ <;> simp only [UpperHalfPlane.vadd_re] <;> nlinarith [strip_width]

private theorem SpecialPeriods.Triangle.sl_im (g : SL(2, ℝ)) (z : ℍ) :
    (g • z).im = z.im / Complex.normSq (slDenom g z) := by
  have h := UpperHalfPlane.im_smul_eq_div_normSq (Matrix.SpecialLinearGroup.mapGL ℝ g) z
  simpa [MulAction.compHom_smul_def, UpperHalfPlane.denom, slDenom] using h

private theorem SpecialPeriods.Triangle.generatorOne_im (z : ℍ) :
    (generatorOneSL • z).im = z.im / Complex.normSq ((z : ℂ) + 1) := by
  rw [sl_im]
  simp [slDenom, generatorOneSL]

private theorem SpecialPeriods.Triangle.generatorOne_sq_im (z : ℍ) :
    (generatorOneSL ^ 2 • z).im = z.im / Complex.normSq (z : ℂ) := by
  rw [sl_im]
  have h0 : (generatorOneSL ^ 2 : SL(2, ℝ)) 1 0 = 1 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) coe_generatorOneSL_sq
  have h1 : (generatorOneSL ^ 2 : SL(2, ℝ)) 1 1 = 0 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) coe_generatorOneSL_sq
  simp [slDenom, h0, h1]

private theorem SpecialPeriods.Triangle.im_lt_generatorOne_im (z : ℍ) (hz : ‖(z : ℂ) + 1‖ < 1) :
    z.im < (generatorOneSL • z).im := by
  rw [generatorOne_im]
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hs : Complex.normSq ((z : ℂ) + 1) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((z : ℂ) + 1)]
  apply (lt_div_iff₀ hd).mpr
  nlinarith [z.im_pos]

private theorem SpecialPeriods.Triangle.im_lt_generatorOne_sq_im (z : ℍ) (hz : ‖(z : ℂ)‖ < 1) :
    z.im < (generatorOneSL ^ 2 • z).im := by
  rw [generatorOne_sq_im]
  have hs : Complex.normSq (z : ℂ) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z : ℂ)]
  apply (lt_div_iff₀ z.normSq_pos).mpr
  nlinarith [z.im_pos]

private theorem SpecialPeriods.Triangle.outside_fordRegion_increases_height (z : ℍ)
    (hl : stripLeft ≤ z.re) (hr : z.re ≤ stripRight) (hz : z ∉ fordRegion) :
    z.im < (generatorOneSL • z).im ∨ z.im < (generatorOneSL ^ 2 • z).im := by
  by_cases h : 1 ≤ ‖(z : ℂ) + 1‖
  · right
    apply im_lt_generatorOne_sq_im
    exact lt_of_not_ge (fun hh => hz ⟨hl, hr, h, hh⟩)
  · exact Or.inl (im_lt_generatorOne_im z (lt_of_not_ge h))

private theorem SpecialPeriods.Triangle.fordRegion_im_lower_bound (z : ℍ) (hz : z ∈ fordRegion) :
    stripRight ≤ z.im := by
  obtain ⟨hl, hr, hleft, hright⟩ := hz
  have hnorm_left : 1 ≤ Complex.normSq ((z : ℂ) + 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((z : ℂ) + 1)]
  have hnorm_right : 1 ≤ Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z : ℂ)]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hnorm_left hnorm_right
  by_cases hx : z.re ≤ -(1 / 2)
  · have hlow : -stripRight ≤ z.re + 1 := by
      unfold stripLeft stripRight at *
      linarith
    have hupp : z.re + 1 ≤ stripRight := by linarith [half_lt_stripRight]
    have hsq : (z.re + 1) ^ 2 ≤ stripRight ^ 2 := sq_le_sq' hlow hupp
    nlinarith [stripRight_sq, stripRight_pos, z.im_pos]
  · have hlow : -stripRight ≤ z.re := by linarith [half_lt_stripRight]
    have hsq : z.re ^ 2 ≤ stripRight ^ 2 := sq_le_sq' hlow hr
    nlinarith [stripRight_sq, stripRight_pos, z.im_pos]

private def SpecialPeriods.Triangle.reductionBox (lo hi : ℝ) : Set ℍ :=
  {z | stripLeft ≤ z.re ∧ z.re ≤ stripRight ∧ lo ≤ z.im ∧ z.im ≤ hi}

private theorem SpecialPeriods.Triangle.coe_reductionBox (lo hi : ℝ) (hlo : 0 < lo) :
    ((↑) : ℍ → ℂ) '' reductionBox lo hi = (Set.Icc stripLeft stripRight) ×ℂ (Set.Icc lo hi) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
  · rintro ⟨⟨hl, hr⟩, hlow, hupp⟩
    exact ⟨⟨z, hlo.trans_le hlow⟩, ⟨hl, hr, hlow, hupp⟩, rfl⟩

private theorem SpecialPeriods.Triangle.reductionBox_compact (lo hi : ℝ) (hlo : 0 < lo) :
    IsCompact (reductionBox lo hi) := by
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff, coe_reductionBox lo hi hlo]
  exact CompactIccSpace.isCompact_Icc.reProdIm CompactIccSpace.isCompact_Icc

private def SpecialPeriods.Triangle.truncatedFordRegion (hi : ℝ) : Set ℍ :=
  {z | z ∈ fordRegion ∧ z.im ≤ hi}

private theorem SpecialPeriods.Triangle.truncatedFordRegion_compact (hi : ℝ) :
    IsCompact (truncatedFordRegion hi) := by
  refine
    (reductionBox_compact stripRight hi stripRight_pos).of_isClosed_subset
      (fordRegion_closed.inter (isClosed_le UpperHalfPlane.continuous_im continuous_const)) ?_
  intro z hz
  exact ⟨hz.1.1, hz.1.2.1, fordRegion_im_lower_bound z hz.1, hz.2⟩

private theorem SpecialPeriods.Triangle.cuspSL_zpow_translate (n : ℤ) (z : ℍ) :
    (cuspSL ^ n : SL(2, ℝ)) • z = (-(n : ℝ) * width) +ᵥ z := by
  change realSLPermutation (cuspSL ^ n) z = _
  rw [map_zpow, cuspSL_permutation_eq_translation, ← map_zpow, ← ofAdd_zsmul,
    horizontalTranslation_apply]
  congr 1
  simp only [zsmul_eq_mul, mul_neg, neg_mul]

private theorem
    SpecialPeriods.Triangle.subgroup_normalize_strip (Γ : Subgroup SL(2, ℝ)) (hc : cuspSL ∈ Γ)
    (z : ℍ) : ∃ g : Γ, stripLeft ≤ (g • z).re ∧ (g • z).re ≤ stripRight ∧ (g • z).im = z.im := by
  obtain ⟨n, hl, hr⟩ := exists_cusp_translate_in_strip z
  let g : Γ := (⟨cuspSL, hc⟩ : Γ) ^ n
  have he : g • z = (-(n : ℝ) * width) +ᵥ z := by
    change ((g : SL(2, ℝ)) • z) = _
    simpa [g] using cuspSL_zpow_translate n z
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa only [he] using hl
  · simpa only [he] using hr.le
  · rw [he, UpperHalfPlane.vadd_im]

private theorem
    SpecialPeriods.Triangle.subgroup_exists_fordRegion_representative (Γ : Subgroup SL(2, ℝ))
    [ProperlyDiscontinuousSMul Γ ℍ] (ha : generatorOneSL ∈ Γ) (hc : cuspSL ∈ Γ) (z : ℍ) :
    ∃ g : Γ, g • z ∈ fordRegion := by
  classical
  by_cases hh : ∃ g : Γ, 1 ≤ (g • z).im
  · obtain ⟨g, hg⟩ := hh
    obtain ⟨k, hkl, hkr, hki⟩ := subgroup_normalize_strip Γ hc (g • z)
    refine ⟨k * g, ?_⟩
    rw [SemigroupAction.mul_smul]
    exact mem_fordRegion_of_one_le_im _ hkl hkr (hki ▸ hg)
  have hbound (g : Γ) : (g • z).im < 1 := lt_of_not_ge (fun hg => hh ⟨g, hg⟩)
  let candidates : Set Γ := {g | g • z ∈ reductionBox z.im 1}
  have hfinite : candidates.Finite := by
    have h :=
      ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ) (K := { z })
        isCompact_singleton (reductionBox_compact z.im 1 z.im_pos)
    simpa only [Set.image_singleton, Set.singleton_inter_nonempty] using h
  have hnonempty : candidates.Nonempty := by
    obtain ⟨g, hl, hr, hi⟩ := subgroup_normalize_strip Γ hc z
    refine ⟨g, hl, hr, ?_, (hbound g).le⟩
    rw [hi]
  obtain ⟨g, hg, hmax⟩ := Set.exists_max_image candidates (fun g => (g • z).im) hfinite hnonempty
  refine ⟨g, ?_⟩
  by_contra hout
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (g • z).im < (generatorOneSL ^ m • (g • z)).im := by
    rcases outside_fordRegion_increases_height (g • z) hg.1 hg.2.1 hout with h | h
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, h⟩
  let a : Γ := ⟨generatorOneSL, ha⟩
  let u : Γ := a ^ m * g
  have hinc : (g • z).im < (u • z).im := by
    dsimp only [u]
    rw [SemigroupAction.mul_smul]
    exact hm
  obtain ⟨k, hkl, hkr, hki⟩ := subgroup_normalize_strip Γ hc (u • z)
  let v : Γ := k * u
  have hvim : (v • z).im = (u • z).im := by simpa only [v, SemigroupAction.mul_smul] using hki
  have hv : v ∈ candidates := by
    refine ⟨?_, ?_, ?_, (hbound v).le⟩
    · simpa only [v, SemigroupAction.mul_smul] using hkl
    · simpa only [v, SemigroupAction.mul_smul] using hkr
    · have hbase : z.im ≤ (g • z).im := hg.2.2.1
      linarith
  have hle := hmax v hv
  linarith

private def SpecialPeriods.Triangle.pingPongOne : Set ℍ :=
  {z | -1 < z.re}

private def SpecialPeriods.Triangle.pingPongTwo : Set ℍ :=
  {z | z.re < -1}

private theorem SpecialPeriods.Triangle.pingPongOne_nonempty : pingPongOne.Nonempty := by
  exact ⟨UpperHalfPlane.I, by norm_num [pingPongOne]⟩

private theorem SpecialPeriods.Triangle.pingPongTwo_nonempty : pingPongTwo.Nonempty := by
  refine ⟨⟨(-2 : ℂ) + Complex.I, by norm_num⟩, ?_⟩
  norm_num [pingPongTwo]

private theorem SpecialPeriods.Triangle.pingPong_disjoint : Disjoint pingPongOne pingPongTwo := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  change -1 < z.re at hz₁
  change z.re < -1 at hz₂
  exact lt_asymm hz₁ hz₂

private theorem SpecialPeriods.Triangle.smul_coe_of_matrix_mo1973_15784 (g : SL(2, ℝ))
    (a b c d : ℝ) (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d]) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = ((a : ℂ) * z + b) / ((c : ℂ) * z + d) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change
    (((((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) : ℂ) * z +
          (((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) : ℂ)) /
        (((((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) : ℂ)) * z +
          (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) : ℂ))) =
      _
  rw [hg]
  rfl

private theorem SpecialPeriods.Triangle.add_real_ne_zero_mo1973_15785 (z : ℍ) (c : ℝ) :
    (z : ℂ) + c ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im,
    UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

private theorem SpecialPeriods.Triangle.generatorOneSL_smul_coe (z : ℍ) :
    ((generatorOneSL • z : ℍ) : ℂ) = -((z : ℂ) + 1)⁻¹ := by
  rw [smul_coe_of_matrix_mo1973_15784 generatorOneSL 0 (-1) 1 1 coe_generatorOneSL]
  simp [div_eq_mul_inv]

private theorem SpecialPeriods.Triangle.generatorOneSL_sq_smul_coe (z : ℍ) :
    (((generatorOneSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ) = -1 - (z : ℂ)⁻¹ := by
  rw [smul_coe_of_matrix_mo1973_15784 (generatorOneSL ^ 2) (-1) (-1) 1 0 coe_generatorOneSL_sq]
  push_cast
  field_simp [z.ne_zero]
  ring

private theorem SpecialPeriods.Triangle.generatorTwoSL_smul_coe (z : ℍ) :
    ((generatorTwoSL • z : ℍ) : ℂ) = -1 - ((z : ℂ) + (width : ℂ))⁻¹ := by
  rw [smul_coe_of_matrix_mo1973_15784 generatorTwoSL 1 (width + 1) (-1) (-width)
      coe_generatorTwoSL]
  push_cast
  let u : ℂ := (z : ℂ) + (width : ℂ)
  have hu : u ≠ 0 := add_real_ne_zero_mo1973_15785 z width
  calc
    _ = (u + 1) / (-u) := by dsimp [u]; congr 1 <;> ring
    _ = -(1 + u⁻¹) := by rw [div_neg, add_div, div_self hu, one_div]
    _ = -1 - u⁻¹ := by ring

private theorem SpecialPeriods.Triangle.generatorTwoSL_sq_smul_coe (z : ℍ) :
    (((generatorTwoSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ) =
      -1 - ((z : ℂ) + (width : ℂ)) / (((width : ℂ) - 1) * z + (width : ℂ)) := by
  rw [smul_coe_of_matrix_mo1973_15784 (generatorTwoSL ^ 2) (-width) (-2 * width) (width - 1) width
      coe_generatorTwoSL_sq]
  have hd : ((width : ℂ) - 1) * (z : ℂ) + (width : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
      Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_zero, MulZeroClass.zero_mul,
      add_zero, UpperHalfPlane.coe_im] at hi
    exact (mul_pos (sub_pos.mpr one_lt_width) z.im_pos).ne' hi
  push_cast
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hd]
  ring

private theorem SpecialPeriods.Triangle.coe_generatorTwoSL_cube :
    ((generatorTwoSL ^ 3 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![width, width + 1; -1, -1] :=
  by
  rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, coe_generatorTwoSL_sq, coe_generatorTwoSL,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> nlinarith [width_sq]

private theorem SpecialPeriods.Triangle.generatorTwoSL_cube_smul_coe (z : ℍ) :
    (((generatorTwoSL ^ 3 : SL(2, ℝ)) • z : ℍ) : ℂ) = -(width : ℂ) - ((z : ℂ) + 1)⁻¹ := by
  rw [smul_coe_of_matrix_mo1973_15784 (generatorTwoSL ^ 3) width (width + 1) (-1) (-1)
      coe_generatorTwoSL_cube]
  have hd : (z : ℂ) + 1 ≠ 0 := by simpa using add_real_ne_zero_mo1973_15785 z 1
  push_cast
  let u : ℂ := (z : ℂ) + 1
  calc
    _ = ((width : ℂ) * u + 1) / (-u) := by dsimp [u]; congr 1 <;> ring
    _ = -((width : ℂ) + u⁻¹) := by rw [div_neg, add_div, mul_div_cancel_right₀ _ hd, one_div]
    _ = -(width : ℂ) - u⁻¹ := by ring

private theorem SpecialPeriods.Triangle.generatorOne_pingPong :
    Set.MapsTo (fun z : ℍ => generatorOneSL • z) pingPongTwo pingPongOne := by
  intro z hz
  change -1 < (generatorOneSL • z).re
  change z.re < -1 at hz
  rw [← UpperHalfPlane.coe_re, generatorOneSL_smul_coe]
  simp only [Complex.neg_re, Complex.inv_re, Complex.add_re, Complex.one_re,
    UpperHalfPlane.coe_re]
  have hden : 0 < Complex.normSq ((z : ℂ) + 1) :=
    Complex.normSq_pos.mpr (by simpa using add_real_ne_zero_mo1973_15785 z 1)
  have hn : (z.re + 1) / Complex.normSq ((z : ℂ) + 1) < 0 :=
    div_neg_of_neg_of_pos (by linarith) hden
  linarith

private theorem SpecialPeriods.Triangle.generatorOne_sq_pingPong :
    Set.MapsTo (fun z : ℍ => (generatorOneSL ^ 2 : SL(2, ℝ)) • z) pingPongTwo pingPongOne := by
  intro z hz
  change -1 < ((generatorOneSL ^ 2 : SL(2, ℝ)) • z).re
  change z.re < -1 at hz
  rw [← UpperHalfPlane.coe_re, generatorOneSL_sq_smul_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.inv_re,
    UpperHalfPlane.coe_re]
  have hn : z.re / Complex.normSq (z : ℂ) < 0 := div_neg_of_neg_of_pos (by linarith) z.normSq_pos
  linarith

private theorem SpecialPeriods.Triangle.generatorTwo_pingPong :
    Set.MapsTo (fun z : ℍ => generatorTwoSL • z) pingPongOne pingPongTwo := by
  intro z hz
  change (generatorTwoSL • z).re < -1
  change -1 < z.re at hz
  rw [← UpperHalfPlane.coe_re, generatorTwoSL_smul_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.inv_re, Complex.add_re,
    Complex.ofReal_re, UpperHalfPlane.coe_re]
  have hp : 0 < (z.re + width) / Complex.normSq ((z : ℂ) + (width : ℂ)) :=
    div_pos (by linarith [one_lt_width])
      (Complex.normSq_pos.mpr (add_real_ne_zero_mo1973_15785 z width))
  linarith

private theorem SpecialPeriods.Triangle.generatorTwo_sq_pingPong :
    Set.MapsTo (fun z : ℍ => (generatorTwoSL ^ 2 : SL(2, ℝ)) • z) pingPongOne pingPongTwo := by
  intro z hz
  change ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z).re < -1
  change -1 < z.re at hz
  rw [← UpperHalfPlane.coe_re, generatorTwoSL_sq_smul_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  suffices hpos : 0 < (((z : ℂ) + (width : ℂ)) / (((width : ℂ) - 1) * z + (width : ℂ))).re by
    linarith
  let u : ℂ := (z : ℂ) + (width : ℂ)
  let v : ℂ := ((width : ℂ) - 1) * z + (width : ℂ)
  have hu : 0 < u.re := by
    change 0 < z.re + width
    linarith [one_lt_width]
  have hv : 0 < v.re := by
    simp only [v, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.one_re, Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_zero,
      MulZeroClass.zero_mul, UpperHalfPlane.coe_re]
    nlinarith [one_lt_width]
  have hvi : 0 < v.im := by
    simp only [v, Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.ofReal_re,
      Complex.one_re, Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_zero,
      MulZeroClass.zero_mul, add_zero, UpperHalfPlane.coe_im]
    exact mul_pos (sub_pos.mpr one_lt_width) z.im_pos
  have hui : 0 < u.im := by simpa [u] using z.im_pos
  have hn : 0 < Complex.normSq v := by
    apply Complex.normSq_pos.mpr
    intro h
    exact hv.ne' (by simpa using congrArg Complex.re h)
  change 0 < (u / v).re
  rw [Complex.div_re]
  exact add_pos (div_pos (mul_pos hu hv) hn) (div_pos (mul_pos hui hvi) hn)

private theorem SpecialPeriods.Triangle.generatorTwo_cube_pingPong :
    Set.MapsTo (fun z : ℍ => (generatorTwoSL ^ 3 : SL(2, ℝ)) • z) pingPongOne pingPongTwo := by
  intro z hz
  change ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z).re < -1
  change -1 < z.re at hz
  rw [← UpperHalfPlane.coe_re, generatorTwoSL_cube_smul_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.inv_re, Complex.add_re,
    Complex.one_re, UpperHalfPlane.coe_re]
  have hp : 0 < (z.re + 1) / Complex.normSq ((z : ℂ) + 1) :=
    div_pos (by linarith)
      (Complex.normSq_pos.mpr (by simpa using add_real_ne_zero_mo1973_15785 z 1))
  linarith [one_lt_width]

private theorem SpecialPeriods.Triangle.generatorOnePerm_pow_apply (n : ℕ) (z : ℍ) :
    (generatorOnePerm ^ n) z = (generatorOneSL ^ n : SL(2, ℝ)) • z := by
  rw [generatorOnePerm, ← map_pow, realSLPermutation_apply]

private theorem SpecialPeriods.Triangle.generatorTwoPerm_pow_apply (n : ℕ) (z : ℍ) :
    (generatorTwoPerm ^ n) z = (generatorTwoSL ^ n : SL(2, ℝ)) • z := by
  rw [generatorTwoPerm, ← map_pow, realSLPermutation_apply]

private theorem SpecialPeriods.cyclicPowerHom_natCast'_mo1973_15799 {G : Type*} [Group G] (n : ℕ)
    (a : G) (ha : a ^ n = 1) (m : ℕ) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (m : ZMod n)) = a ^ m := by
  simpa only [Int.cast_natCast, zpow_natCast] using cyclicPowerHom_intCast n a ha (m : ℤ)

private theorem SpecialPeriods.cyclicPowerHom_two'_mo1973_15800 {G : Type*} [Group G] (n : ℕ)
    (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (2 : ZMod n)) = a ^ 2 := by
  simpa only [Nat.cast_ofNat] using cyclicPowerHom_natCast'_mo1973_15799 n a ha 2

private theorem SpecialPeriods.cyclicPowerHom_three'_mo1973_15801 {G : Type*} [Group G] (n : ℕ)
    (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (3 : ZMod n)) = a ^ 3 := by
  simpa only [Nat.cast_ofNat] using cyclicPowerHom_natCast'_mo1973_15799 n a ha 3

private theorem
    SpecialPeriods.triangleLift_injective_of_pingPong {G α : Type*} [Group G] [MulAction G α]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y : Set α) (hXY : Disjoint X Y)
    (hX : X.Nonempty) (hY : Y.Nonempty) (ha₁ : Set.MapsTo (fun z => a • z) Y X)
    (ha₂ : Set.MapsTo (fun z => a ^ 2 • z) Y X) (hb₁ : Set.MapsTo (fun z => b • z) X Y)
    (hb₂ : Set.MapsTo (fun z => b ^ 2 • z) X Y) (hb₃ : Set.MapsTo (fun z => b ^ 3 • z) X Y) :
    Function.Injective (triangleLift a b ha hb) := by
  let H : Bool → Type := fun i => cond i (Multiplicative (ZMod 4)) (Multiplicative (ZMod 3))
  let : ∀ i, Group (H i) :=
    Bool.rec (inferInstance : Group (Multiplicative (ZMod 3)))
      (inferInstance : Group (Multiplicative (ZMod 4)))
  let f : ∀ i, H i →* G := fun i =>
    match i with
    | false => cyclicPowerHom 3 a ha
    | true => cyclicPowerHom 4 b hb
  let toI : TriangleGroup →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := Bool.false))
      (Monoid.CoprodI.of (M := H) (i := Bool.true))
  let fromI : Monoid.CoprodI H →* TriangleGroup :=
    Monoid.CoprodI.lift fun i =>
      match i with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id TriangleGroup := by
    apply triangle_hom_ext
    · simp [toI, fromI, triangleGenerator₁]
    · simp [toI, fromI, triangleGenerator₂]
  have htoI : Function.Injective toI := by
    apply Function.LeftInverse.injective (g := fromI)
    intro z
    exact DFunLike.congr_fun hleft z
  have hrepresentation : triangleLift a b ha hb = (Monoid.CoprodI.lift f).comp toI := by
    apply triangle_hom_ext
    · simp only [triangleLift_generator₁, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 3 a ha).symm
    · simp only [triangleLift_generator₂, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 4 b hb).symm
  rw [hrepresentation, MonoidHom.coe_comp]
  apply Function.Injective.comp _ htoI
  let U : Bool → Set α := fun i => cond i Y X
  apply Monoid.CoprodI.lift_injective_of_ping_pong f _ U
  · intro i
    cases i
    · exact hX
    · exact hY
  · intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hXY
    · exact hXY.symm
    · exact (hij rfl).elim
  · intro i j hij g hg
    cases i <;> cases j
    · exact (hij rfl).elim
    · change cyclicPowerHom 3 a ha g • Y ⊆ X
      have hc : g = Multiplicative.ofAdd (1 : ZMod 3) ∨ g = Multiplicative.ofAdd (2 : ZMod 3) := by
        exact
          (by decide :
              ∀ x : Multiplicative (ZMod 3),
                x ≠ 1 → x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2)
            g hg
      rcases hc with rfl | rfl
      · rw [cyclicPowerHom_one]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => ha₁ hz)
      · rw [cyclicPowerHom_two'_mo1973_15800 3 a ha]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => ha₂ hz)
    · change cyclicPowerHom 4 b hb g • X ⊆ Y
      have hc :
        g = Multiplicative.ofAdd (1 : ZMod 4) ∨
          g = Multiplicative.ofAdd (2 : ZMod 4) ∨ g = Multiplicative.ofAdd (3 : ZMod 4) := by
        exact
          (by decide :
              ∀ x : Multiplicative (ZMod 4),
                x ≠ 1 →
                  x = Multiplicative.ofAdd 1 ∨
                    x = Multiplicative.ofAdd 2 ∨ x = Multiplicative.ofAdd 3)
            g hg
      rcases hc with rfl | rfl | rfl
      · rw [cyclicPowerHom_one]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₁ hz)
      · rw [cyclicPowerHom_two'_mo1973_15800 4 b hb]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₂ hz)
      · rw [cyclicPowerHom_three'_mo1973_15801 4 b hb]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₃ hz)
    · exact (hij rfl).elim
  · right
    refine ⟨Bool.false, ?_⟩
    change 3 ≤ Cardinal.mk (Multiplicative (ZMod 3))
    simp

private theorem SpecialPeriods.triangleGeometricRepresentation_injective :
    Function.Injective triangleGeometricRepresentation := by
  apply
    triangleLift_injective_of_pingPong Triangle.generatorOnePerm Triangle.generatorTwoPerm
      Triangle.generatorOnePerm_cube Triangle.generatorTwoPerm_fourth Triangle.pingPongOne
      Triangle.pingPongTwo Triangle.pingPong_disjoint Triangle.pingPongOne_nonempty
      Triangle.pingPongTwo_nonempty
  · intro z hz
    exact Triangle.generatorOne_pingPong hz
  · intro z hz
    change (Triangle.generatorOnePerm ^ 2) z ∈ Triangle.pingPongOne
    rw [Triangle.generatorOnePerm_pow_apply]
    exact Triangle.generatorOne_sq_pingPong hz
  · intro z hz
    exact Triangle.generatorTwo_pingPong hz
  · intro z hz
    change (Triangle.generatorTwoPerm ^ 2) z ∈ Triangle.pingPongTwo
    rw [Triangle.generatorTwoPerm_pow_apply]
    exact Triangle.generatorTwo_sq_pingPong hz
  · intro z hz
    change (Triangle.generatorTwoPerm ^ 3) z ∈ Triangle.pingPongTwo
    rw [Triangle.generatorTwoPerm_pow_apply]
    exact Triangle.generatorTwo_cube_pingPong hz

private theorem SpecialPeriods.finiteTest_mixed_word_mo1973_15805 {G α : Type*} [Group G]
    [MulAction G α] {H : Bool → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G) (U : Bool → Set α)
    (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • U j ⊆ U i)
    (hcard : 3 ≤ Cardinal.mk (H Bool.false)) (xB : α) (hxB : xB ∈ U Bool.true)
    (w : Monoid.CoprodI.NeWord H Bool.false Bool.true) :
    ∃ h : H Bool.false,
      (f Bool.false h * Monoid.CoprodI.lift f w.prod * (f Bool.false h)⁻¹) • xB ∈ U Bool.false := by
  obtain ⟨h, hn1, hnh⟩ := Cardinal.exists_ne_ne_of_three_le hcard 1 w.head⁻¹
  have hnot1 : h * w.head ≠ 1 := by
    rw [← div_inv_eq_mul]
    exact div_ne_one_of_ne hnh
  let w' : Monoid.CoprodI.NeWord H Bool.false Bool.false :=
    Monoid.CoprodI.NeWord.append (w.mulHead h hnot1) (by decide)
      (Monoid.CoprodI.NeWord.singleton h⁻¹ (inv_ne_one.mpr hn1))
  have hw' : Monoid.CoprodI.lift f w'.prod • xB ∈ U Bool.false :=
    Set.smul_set_subset_iff.mp (Monoid.CoprodI.lift_word_ping_pong f U hpp w' (by decide)) hxB
  refine ⟨h, ?_⟩
  simpa [w'] using hw'

private theorem SpecialPeriods.finiteTest_coprodI_mo1973_15806 {G α : Type*} [Group G]
    [MulAction G α] {H : Bool → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G) (U : Bool → Set α)
    (hdisj : Disjoint (U Bool.false) (U Bool.true))
    (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • U j ⊆ U i)
    (hcard : 3 ≤ Cardinal.mk (H Bool.false)) (xA xB : α) (hxA : xA ∈ U Bool.false)
    (hxB : xB ∈ U Bool.true) (w : Monoid.CoprodI H)
    (hA : Monoid.CoprodI.lift f w • xA ∈ U Bool.false)
    (hB :
      ∀ h : H Bool.false,
        (f Bool.false h * Monoid.CoprodI.lift f w * (f Bool.false h)⁻¹) • xB ∈ U Bool.true ∧
          (f Bool.false h * (Monoid.CoprodI.lift f w)⁻¹ * (f Bool.false h)⁻¹) • xB ∈
            U Bool.true) :
    Monoid.CoprodI.lift f w = 1 := by
  classical
  let r := Monoid.CoprodI.Word.equiv (M := H) w
  have hr : r.prod = w := (Monoid.CoprodI.Word.equiv (M := H)).symm_apply_apply w
  by_cases hr0 : r = Monoid.CoprodI.Word.empty
  · have hw1 : w = 1 := by rw [← hr, hr0, Monoid.CoprodI.Word.prod_empty]
    simp [hw1]
  obtain ⟨i, j, v, hv⟩ := Monoid.CoprodI.NeWord.of_word r hr0
  have hvprod : v.prod = w := by
    change v.toWord.prod = w
    rw [hv]
    exact hr
  rw [← hvprod] at hA hB ⊢
  suffices False by contradiction
  cases i <;> cases j
  · have hm : Monoid.CoprodI.lift f v.prod • xB ∈ U Bool.false :=
      Set.smul_set_subset_iff.mp (Monoid.CoprodI.lift_word_ping_pong f U hpp v (by decide)) hxB
    have hn : Monoid.CoprodI.lift f v.prod • xB ∈ U Bool.true := by
      simpa only [map_one, one_mul, inv_one, mul_one] using (hB 1).1
    exact hdisj.le_bot ⟨hm, hn⟩
  · obtain ⟨h, hm⟩ := finiteTest_mixed_word_mo1973_15805 f U hpp hcard xB hxB v
    exact hdisj.le_bot ⟨hm, (hB h).1⟩
  · obtain ⟨h, hm⟩ := finiteTest_mixed_word_mo1973_15805 f U hpp hcard xB hxB v.inv
    have hm' :
      (f Bool.false h * (Monoid.CoprodI.lift f v.prod)⁻¹ * (f Bool.false h)⁻¹) • xB ∈
        U Bool.false := by simpa only [Monoid.CoprodI.NeWord.inv_prod, map_inv] using hm
    exact hdisj.le_bot ⟨hm', (hB h).2⟩
  · have hm : Monoid.CoprodI.lift f v.prod • xA ∈ U Bool.true :=
      Set.smul_set_subset_iff.mp (Monoid.CoprodI.lift_word_ping_pong f U hpp v (by decide)) hxA
    exact hdisj.le_bot ⟨hA, hm⟩

private theorem SpecialPeriods.finiteTest_cyclicPowerHom_two_mo1973_15807 {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (2 : ZMod n)) = a ^ 2 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (2 : ℤ)

private theorem SpecialPeriods.finiteTest_cyclicPowerHom_three_mo1973_15808 {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (3 : ZMod n)) = a ^ 3 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (3 : ℤ)

private theorem SpecialPeriods.triangleLift_eq_one_of_pingPong_finite_tests {G α : Type*} [Group G]
    [MulAction G α] (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y : Set α) (hXY : Disjoint X Y)
    (ha₁ : Set.MapsTo (fun z => a • z) Y X) (ha₂ : Set.MapsTo (fun z => a ^ 2 • z) Y X)
    (hb₁ : Set.MapsTo (fun z => b • z) X Y) (hb₂ : Set.MapsTo (fun z => b ^ 2 • z) X Y)
    (hb₃ : Set.MapsTo (fun z => b ^ 3 • z) X Y) (xA xB : α) (hxA : xA ∈ X) (hxB : xB ∈ Y)
    (w : TriangleGroup) (hA : triangleLift a b ha hb w • xA ∈ X)
    (hB :
      ∀ h : Multiplicative (ZMod 3),
        (cyclicPowerHom 3 a ha h * triangleLift a b ha hb w * (cyclicPowerHom 3 a ha h)⁻¹) • xB ∈
            Y ∧
          (cyclicPowerHom 3 a ha h * (triangleLift a b ha hb w)⁻¹ * (cyclicPowerHom 3 a ha h)⁻¹) •
              xB ∈
            Y) :
    triangleLift a b ha hb w = 1 := by
  let H : Bool → Type := fun i => cond i (Multiplicative (ZMod 4)) (Multiplicative (ZMod 3))
  let : ∀ i, Group (H i) :=
    Bool.rec (inferInstance : Group (Multiplicative (ZMod 3)))
      (inferInstance : Group (Multiplicative (ZMod 4)))
  let f : ∀ i, H i →* G := fun i =>
    match i with
    | false => cyclicPowerHom 3 a ha
    | true => cyclicPowerHom 4 b hb
  let toI : TriangleGroup →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := Bool.false))
      (Monoid.CoprodI.of (M := H) (i := Bool.true))
  have hrepresentation : triangleLift a b ha hb = (Monoid.CoprodI.lift f).comp toI := by
    apply triangle_hom_ext
    · simp only [triangleLift_generator₁, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 3 a ha).symm
    · simp only [triangleLift_generator₂, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 4 b hb).symm
  let U : Bool → Set α := fun i => cond i Y X
  have hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • U j ⊆ U i := by
    intro i j hij g hg
    cases i <;> cases j
    · exact (hij rfl).elim
    · change cyclicPowerHom 3 a ha g • Y ⊆ X
      have hc : g = Multiplicative.ofAdd (1 : ZMod 3) ∨ g = Multiplicative.ofAdd (2 : ZMod 3) := by
        exact
          (by decide :
              ∀ x : Multiplicative (ZMod 3),
                x ≠ 1 → x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2)
            g hg
      rcases hc with rfl | rfl
      · rw [cyclicPowerHom_one]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => ha₁ hz)
      · rw [finiteTest_cyclicPowerHom_two_mo1973_15807 3 a ha]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => ha₂ hz)
    · change cyclicPowerHom 4 b hb g • X ⊆ Y
      have hc :
        g = Multiplicative.ofAdd (1 : ZMod 4) ∨
          g = Multiplicative.ofAdd (2 : ZMod 4) ∨ g = Multiplicative.ofAdd (3 : ZMod 4) := by
        exact
          (by decide :
              ∀ x : Multiplicative (ZMod 4),
                x ≠ 1 →
                  x = Multiplicative.ofAdd 1 ∨
                    x = Multiplicative.ofAdd 2 ∨ x = Multiplicative.ofAdd 3)
            g hg
      rcases hc with rfl | rfl | rfl
      · rw [cyclicPowerHom_one]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₁ hz)
      · rw [finiteTest_cyclicPowerHom_two_mo1973_15807 4 b hb]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₂ hz)
      · rw [finiteTest_cyclicPowerHom_three_mo1973_15808 4 b hb]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₃ hz)
    · exact (hij rfl).elim
  have hcard : 3 ≤ Cardinal.mk (H Bool.false) := by
    change 3 ≤ Cardinal.mk (Multiplicative (ZMod 3))
    simp
  have heval : triangleLift a b ha hb w = Monoid.CoprodI.lift f (toI w) :=
    DFunLike.congr_fun hrepresentation w
  rw [heval] at hA hB ⊢
  exact finiteTest_coprodI_mo1973_15806 f U hXY hpp hcard xA xB hxA hxB (toI w) hA hB

private def SpecialPeriods.Triangle.matrixGroup : Subgroup (SL(2, ℝ)) :=
  Subgroup.closure ({ generatorOneSL, generatorTwoSL } : Set (SL(2, ℝ)))

private theorem
    SpecialPeriods.Triangle.generatorOneSL_mem_matrixGroup : generatorOneSL ∈ matrixGroup :=
  Subgroup.subset_closure (by simp)

private theorem
    SpecialPeriods.Triangle.generatorTwoSL_mem_matrixGroup : generatorTwoSL ∈ matrixGroup :=
  Subgroup.subset_closure (by simp)

private theorem SpecialPeriods.Triangle.cuspSL_mem_matrixGroup : cuspSL ∈ matrixGroup := by
  have h :=
    matrixGroup.inv_mem
      (matrixGroup.mul_mem generatorOneSL_mem_matrixGroup generatorTwoSL_mem_matrixGroup)
  simpa only [generatorOneSL_mul_generatorTwoSL, cuspSL] using h

private theorem
    SpecialPeriods.Triangle.neg_one_mem_matrixGroup : (-1 : SL(2, ℝ)) ∈ matrixGroup := by
  have h := matrixGroup.pow_mem generatorOneSL_mem_matrixGroup 3
  simpa only [generatorOneSL_cube] using h

private theorem SpecialPeriods.Triangle.matrixGroup_map_realSLPermutation :
    matrixGroup.map realSLPermutation = SpecialPeriods.triangleGeometricRepresentation.range := by
  rw [matrixGroup, MonoidHom.map_closure, Set.image_pair, SpecialPeriods.triangle_range]
  simp only [SpecialPeriods.triangleGeometricRepresentation_generator₁,
    SpecialPeriods.triangleGeometricRepresentation_generator₂, generatorOnePerm, generatorTwoPerm]

private theorem SpecialPeriods.Triangle.matrixGroup_permutation_lift (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) :
    ∃ w : SpecialPeriods.TriangleGroup,
      SpecialPeriods.triangleGeometricRepresentation w = realSLPermutation A := by
  have hm : realSLPermutation A ∈ matrixGroup.map realSLPermutation := ⟨A, hA, rfl⟩
  rw [matrixGroup_map_realSLPermutation] at hm
  exact hm

private theorem SpecialPeriods.Triangle.triangleGeometricRepresentation_matrixGroup_lift
    (w : SpecialPeriods.TriangleGroup) :
    ∃ A : matrixGroup, realSLPermutation A = SpecialPeriods.triangleGeometricRepresentation w := by
  have hm :
    SpecialPeriods.triangleGeometricRepresentation w ∈
      SpecialPeriods.triangleGeometricRepresentation.range :=
    ⟨w, rfl⟩
  rw [← matrixGroup_map_realSLPermutation] at hm
  obtain ⟨A, hA, hA'⟩ := hm
  exact ⟨⟨A, hA⟩, hA'⟩

private theorem SpecialPeriods.Triangle.realSLPermutation_eq_one_iff (A : SL(2, ℝ)) :
    realSLPermutation A = 1 ↔ A = 1 ∨ A = -1 := by
  constructor
  · intro h
    have hfix : ∀ z : ℍ, Matrix.SpecialLinearGroup.mapGL ℝ A • z = z := by
      intro z
      change realSLPermutation A z = z
      rw [h]
      rfl
    have hc := UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mp hfix
    obtain ⟨r, hr⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
    change Matrix.scalar (Fin 2) r = (A : Matrix (Fin 2) (Fin 2) ℝ) at hr
    have hs : r ^ 2 = 1 := by
      simpa [Matrix.scalar_apply, Matrix.det_diagonal] using congrArg Matrix.det hr
    rcases sq_eq_one_iff.mp hs with h₁ | hneg
    · left
      apply Subtype.ext
      simpa [h₁] using hr.symm
    · right
      apply Subtype.ext
      simpa only [hneg, map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one] using hr.symm
  · rintro (rfl | rfl)
    · exact map_one realSLPermutation
    · exact realSLPermutation_neg_one

private def SpecialPeriods.Triangle.testPointOne : ℍ :=
  UpperHalfPlane.I

private def SpecialPeriods.Triangle.testPointTwo : ℍ :=
  ⟨(-2 : ℂ) + Complex.I, by norm_num⟩

private theorem SpecialPeriods.Triangle.testPointOne_mem : testPointOne ∈ pingPongOne := by
  norm_num [testPointOne, pingPongOne]

private theorem SpecialPeriods.Triangle.testPointTwo_mem : testPointTwo ∈ pingPongTwo := by
  norm_num [testPointTwo, pingPongTwo]

private theorem SpecialPeriods.Triangle.pingPongOne_isOpen : IsOpen pingPongOne :=
  isOpen_lt continuous_const UpperHalfPlane.continuous_re

private theorem SpecialPeriods.Triangle.pingPongTwo_isOpen : IsOpen pingPongTwo :=
  isOpen_lt UpperHalfPlane.continuous_re continuous_const

private def SpecialPeriods.Triangle.cyclicConjugator (h : Multiplicative (ZMod 3)) : SL(2, ℝ) :=
  generatorOneSL ^ h.toAdd.val

private theorem SpecialPeriods.Triangle.cyclicConjugator_permutation (h : Multiplicative (ZMod 3)) :
    realSLPermutation (cyclicConjugator h) =
      SpecialPeriods.cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h := by
  rw [cyclicConjugator, map_pow]
  change generatorOnePerm ^ h.toAdd.val = _
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, ofAdd_toAdd, zpow_natCast] using
    (SpecialPeriods.cyclicPowerHom_intCast 3 generatorOnePerm generatorOnePerm_cube
        (h.toAdd.val : ℤ)).symm

private def SpecialPeriods.Triangle.identityTestSet : Set (SL(2, ℝ)) :=
  {A |
    0 < A 0 0 ∧
      A • testPointOne ∈ pingPongOne ∧
        ∀ h : Multiplicative (ZMod 3),
          (cyclicConjugator h * A * (cyclicConjugator h)⁻¹) • testPointTwo ∈ pingPongTwo ∧
            (cyclicConjugator h * A⁻¹ * (cyclicConjugator h)⁻¹) • testPointTwo ∈ pingPongTwo}

private theorem SpecialPeriods.Triangle.identityTestSet_isOpen : IsOpen identityTestSet := by
  have he : IsOpen {A : SL(2, ℝ) | 0 < A 0 0} := isOpen_lt continuous_const (by fun_prop)
  have h₁ : IsOpen {A : SL(2, ℝ) | A • testPointOne ∈ pingPongOne} :=
    pingPongOne_isOpen.preimage (by fun_prop)
  have h₂ (h : Multiplicative (ZMod 3)) :
    IsOpen
      {A : SL(2, ℝ) |
        (cyclicConjugator h * A * (cyclicConjugator h)⁻¹) • testPointTwo ∈ pingPongTwo ∧
          (cyclicConjugator h * A⁻¹ * (cyclicConjugator h)⁻¹) • testPointTwo ∈ pingPongTwo} :=
    (pingPongTwo_isOpen.preimage (by fun_prop)).inter (pingPongTwo_isOpen.preimage (by fun_prop))
  simpa only [identityTestSet, Set.ofPred_and, Set.ofPred_forall] using
    he.inter (h₁.inter (isOpen_iInter_of_finite h₂))

private theorem
    SpecialPeriods.Triangle.one_mem_identityTestSet : (1 : SL(2, ℝ)) ∈ identityTestSet := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  · simpa using testPointOne_mem
  · intro h
    simpa using And.intro testPointTwo_mem testPointTwo_mem

private theorem
    SpecialPeriods.Triangle.realSLPermutation_eq_one_of_mem_identityTestSet {A : SL(2, ℝ)}
    (hA : A ∈ matrixGroup) (hT : A ∈ identityTestSet) : realSLPermutation A = 1 := by
  obtain ⟨w, hw⟩ := matrixGroup_permutation_lift A hA
  rw [← hw]
  refine
    SpecialPeriods.triangleLift_eq_one_of_pingPong_finite_tests generatorOnePerm generatorTwoPerm
      generatorOnePerm_cube generatorTwoPerm_fourth pingPongOne pingPongTwo pingPong_disjoint ?_
      ?_ ?_ ?_ ?_ testPointOne testPointTwo testPointOne_mem testPointTwo_mem w ?_ ?_
  · intro z hz
    exact generatorOne_pingPong hz
  · intro z hz
    change (generatorOnePerm ^ 2) z ∈ pingPongOne
    rw [generatorOnePerm_pow_apply]
    exact generatorOne_sq_pingPong hz
  · intro z hz
    exact generatorTwo_pingPong hz
  · intro z hz
    change (generatorTwoPerm ^ 2) z ∈ pingPongTwo
    rw [generatorTwoPerm_pow_apply]
    exact generatorTwo_sq_pingPong hz
  · intro z hz
    change (generatorTwoPerm ^ 3) z ∈ pingPongTwo
    rw [generatorTwoPerm_pow_apply]
    exact generatorTwo_cube_pingPong hz
  · change SpecialPeriods.triangleGeometricRepresentation w testPointOne ∈ pingPongOne
    rw [hw]
    exact hT.2.1
  · intro h
    change
      (SpecialPeriods.cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h *
                SpecialPeriods.triangleGeometricRepresentation w *
              (SpecialPeriods.cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h)⁻¹)
            testPointTwo ∈
          pingPongTwo ∧
        (SpecialPeriods.cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h *
                (SpecialPeriods.triangleGeometricRepresentation w)⁻¹ *
              (SpecialPeriods.cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h)⁻¹)
            testPointTwo ∈
          pingPongTwo
    rw [hw, ← cyclicConjugator_permutation]
    have ht := hT.2.2 h
    change
      realSLPermutation (cyclicConjugator h * A * (cyclicConjugator h)⁻¹) testPointTwo ∈
          pingPongTwo ∧
        realSLPermutation (cyclicConjugator h * A⁻¹ * (cyclicConjugator h)⁻¹) testPointTwo ∈
          pingPongTwo at ht
    simpa only [map_mul, map_inv] using ht

private theorem SpecialPeriods.Triangle.eq_one_of_mem_identityTestSet {A : SL(2, ℝ)}
    (hA : A ∈ matrixGroup) (hT : A ∈ identityTestSet) : A = 1 := by
  rcases
    (realSLPermutation_eq_one_iff A).mp
      (realSLPermutation_eq_one_of_mem_identityTestSet hA hT) with
    h | h
  · exact h
  · have hp := hT.1
    subst A
    norm_num [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply] at hp

private theorem SpecialPeriods.Triangle.identityTestSet_preimage_matrixGroup :
    (fun A : matrixGroup => (A : SL(2, ℝ))) ⁻¹' identityTestSet = { 1 } := by
  ext A
  constructor
  · intro h
    exact Set.mem_singleton_iff.mpr (Subtype.ext (eq_one_of_mem_identityTestSet A.property h))
  · rintro rfl
    exact one_mem_identityTestSet

private instance SpecialPeriods.Triangle.matrixGroup_discrete : DiscreteTopology matrixGroup := by
  apply discreteTopology_of_isOpen_singleton_one
  rw [← identityTestSet_preimage_matrixGroup]
  exact identityTestSet_isOpen.preimage continuous_subtype_val

private theorem
    SpecialPeriods.Triangle.matrixGroup_isClosed : IsClosed (matrixGroup : Set (SL(2, ℝ))) :=
  Subgroup.isClosed_of_discrete

private instance SpecialPeriods.Triangle.matrixGroup_properlyDiscontinuous :
    ProperlyDiscontinuousSMul matrixGroup ℍ :=
  inferInstance

private instance SpecialPeriods.Triangle.matrixGroup_properSMul : ProperSMul matrixGroup ℍ := by
  have : IsClosed (matrixGroup : Set (SL(2, ℝ))) := matrixGroup_isClosed
  infer_instance

private theorem
    SpecialPeriods.Triangle.matrixGroup_isCompact_transporter {K L : Set ℍ} (hK : IsCompact K)
    (hL : IsCompact L) : IsCompact {g : matrixGroup | (g • K ∩ L).Nonempty} :=
  ProperSMul.isCompact_setOfPred_inter_nonempty hK hL

private theorem SpecialPeriods.Triangle.matrixGroup_finite_compact_transporter {K L : Set ℍ}
    (hK : IsCompact K) (hL : IsCompact L) : {g : matrixGroup | (g • K ∩ L).Nonempty}.Finite :=
  isCompact_iff_finite.mp (matrixGroup_isCompact_transporter hK hL)

private theorem SpecialPeriods.Triangle.matrixGroup_exists_fordRegion_representative (z : ℍ) :
    ∃ g : matrixGroup, g • z ∈ fordRegion :=
  subgroup_exists_fordRegion_representative matrixGroup generatorOneSL_mem_matrixGroup
    cuspSL_mem_matrixGroup z

private theorem SpecialPeriods.triangle_exists_fordRegion_representative (z : ℍ) :
    ∃ g : TriangleGroup, triangleGeometricRepresentation g z ∈ Triangle.fordRegion := by
  obtain ⟨A, hA⟩ := Triangle.matrixGroup_exists_fordRegion_representative z
  obtain ⟨g, hg⟩ := Triangle.matrixGroup_permutation_lift A A.property
  refine ⟨g, ?_⟩
  rw [hg]
  exact hA

private theorem SpecialPeriods.triangle_exists_fordRegion_preimage (z : ℍ) :
    ∃ w ∈ Triangle.fordRegion, ∃ g : TriangleGroup, triangleGeometricRepresentation g w = z := by
  obtain ⟨g, hg⟩ := triangle_exists_fordRegion_representative z
  refine ⟨triangleGeometricRepresentation g z, hg, g⁻¹, ?_⟩
  rw [map_inv]
  exact (triangleGeometricRepresentation g).symm_apply_apply z

private theorem SpecialPeriods.triangle_translates_fordRegion_cover :
    (⋃ g : TriangleGroup, (triangleGeometricRepresentation g) '' Triangle.fordRegion) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨w, hw, g, hg⟩ := triangle_exists_fordRegion_preimage z
  exact Set.mem_iUnion.mpr ⟨g, w, hw, hg⟩

private def SpecialPeriods.Triangle.shimizuTranslation (w : ℝ) : SL(2, ℝ) :=
  ⟨!![1, w; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp]
private theorem SpecialPeriods.Triangle.coe_shimizuTranslation (w : ℝ) :
    (shimizuTranslation w : Matrix (Fin 2) (Fin 2) ℝ) = !![1, w; 0, 1] :=
  rfl

private theorem SpecialPeriods.Triangle.shimizuTranslation_width :
    shimizuTranslation width = cuspInverseSL :=
  rfl

private theorem SpecialPeriods.Triangle.shimizu_conjugate_matrix (w : ℝ) (A : SL(2, ℝ)) :
    ((A * shimizuTranslation w * A⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1 - w * A 0 0 * A 1 0, w * (A 0 0) ^ 2; -w * (A 1 0) ^ 2, 1 + w * A 0 0 * A 1 0] := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 :=
    (Matrix.det_fin_two A.val).symm.trans A.property
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    coe_shimizuTranslation, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hdet]

private def SpecialPeriods.Triangle.shimizuSequence (w : ℝ) (A : SL(2, ℝ)) : ℕ → SL(2, ℝ)
  | 0 => A
  | n + 1 => shimizuSequence w A n * shimizuTranslation w * (shimizuSequence w A n)⁻¹

private theorem SpecialPeriods.Triangle.shimizuSequence_mem (Γ : Subgroup (SL(2, ℝ))) (w : ℝ)
    (A : SL(2, ℝ)) (hT : shimizuTranslation w ∈ Γ) (hA : A ∈ Γ) (n : ℕ) :
    shimizuSequence w A n ∈ Γ := by
  induction n with
  | zero => exact hA
  | succ n ih => exact Γ.mul_mem (Γ.mul_mem ih hT) (Γ.inv_mem ih)

private theorem SpecialPeriods.Triangle.shimizuSequence_succ_matrix (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    (shimizuSequence w A (n + 1) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1 - w * shimizuSequence w A n 0 0 * shimizuSequence w A n 1 0,
          w * (shimizuSequence w A n 0 0) ^ 2;
        -w * (shimizuSequence w A n 1 0) ^ 2,
          1 + w * shimizuSequence w A n 0 0 * shimizuSequence w A n 1 0] :=
  shimizu_conjugate_matrix w (shimizuSequence w A n)

private theorem
    SpecialPeriods.Triangle.shimizuSequence_succ_zero_zero (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) 0 0 =
      1 - shimizuSequence w A n 0 0 * (w * shimizuSequence w A n 1 0) := by
  have h :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) (shimizuSequence_succ_matrix w A n)
  simpa only [Matrix.of_apply, Matrix.cons_val_zero, mul_left_comm, mul_assoc] using h

private theorem
    SpecialPeriods.Triangle.shimizuSequence_succ_zero_one (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) 0 1 = w * (shimizuSequence w A n 0 0) ^ 2 := by
  simpa using
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) (shimizuSequence_succ_matrix w A n)

private theorem
    SpecialPeriods.Triangle.shimizuSequence_succ_one_zero (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) 1 0 = -w * (shimizuSequence w A n 1 0) ^ 2 := by
  simpa using
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) (shimizuSequence_succ_matrix w A n)

private theorem
    SpecialPeriods.Triangle.shimizuSequence_succ_one_one (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) 1 1 =
      1 + shimizuSequence w A n 0 0 * (w * shimizuSequence w A n 1 0) := by
  have h :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) (shimizuSequence_succ_matrix w A n)
  simpa only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, mul_left_comm,
    mul_assoc] using h

private theorem
    SpecialPeriods.Triangle.shimizuSequence_succ_scaled_lower_left (w : ℝ) (A : SL(2, ℝ))
    (n : ℕ) : w * shimizuSequence w A (n + 1) 1 0 = -(w * shimizuSequence w A n 1 0) ^ 2 := by
  rw [shimizuSequence_succ_one_zero]
  ring

private theorem SpecialPeriods.Triangle.shimizuSequence_lower_left_ne_zero (w : ℝ) (A : SL(2, ℝ))
    (hw : w ≠ 0) (hA : A 1 0 ≠ 0) (n : ℕ) : shimizuSequence w A n 1 0 ≠ 0 := by
  induction n with
  | zero => exact hA
  | succ n ih =>
    rw [shimizuSequence_succ_one_zero]
    exact mul_ne_zero (neg_ne_zero.mpr hw) (pow_ne_zero 2 ih)

private theorem SpecialPeriods.Triangle.shimizu_recurrence_abs_le_initial (q : ℕ → ℝ)
    (hq : ∀ n, q (n + 1) = -(q n) ^ 2) (hsmall : |q 0| ≤ 1) (n : ℕ) : |q n| ≤ |q 0| := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [hq, abs_neg, abs_pow, pow_two]
    calc
      |q n| * |q n| ≤ |q 0| * |q 0| := mul_le_mul ih ih (abs_nonneg _) (abs_nonneg _)
      _ ≤ |q 0| := by nlinarith [abs_nonneg (q 0)]

private theorem SpecialPeriods.Triangle.shimizu_recurrence_geometric_bound (q : ℕ → ℝ)
    (hq : ∀ n, q (n + 1) = -(q n) ^ 2) (hsmall : |q 0| ≤ 1) (n : ℕ) : |q n| ≤ |q 0| ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hq, abs_neg, abs_pow, pow_two]
    calc
      |q n| * |q n| ≤ |q 0| * |q 0| ^ (n + 1) :=
        mul_le_mul (shimizu_recurrence_abs_le_initial q hq hsmall n) ih (abs_nonneg _)
          (abs_nonneg _)
      _ = |q 0| ^ (n + 1 + 1) := by rw [pow_succ]; ring

private theorem SpecialPeriods.Triangle.shimizu_recurrence_a_bound (q a : ℕ → ℝ)
    (hq : ∀ n, q (n + 1) = -(q n) ^ 2) (ha : ∀ n, a (n + 1) = 1 - a n * q n) (hsmall : |q 0| < 1)
    (n : ℕ) : |a n| ≤ (1 + |a 0|) / (1 - |q 0|) := by
  let M : ℝ := (1 + |a 0|) / (1 - |q 0|)
  have hd : 0 < 1 - |q 0| := sub_pos.mpr hsmall
  have hM : 0 ≤ M := div_nonneg (by positivity) hd.le
  have hM_eq : M * (1 - |q 0|) = 1 + |a 0| := div_mul_cancel₀ _ hd.ne'
  have hM_step : 1 + M * |q 0| ≤ M := by nlinarith [abs_nonneg (a 0)]
  change |a n| ≤ M
  induction n with
  | zero =>
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (abs_nonneg (a 0)) (abs_nonneg (q 0))]
  | succ n ih =>
    rw [ha]
    calc
      |1 - a n * q n| ≤ |(1 : ℝ)| + |a n * q n| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (1 : ℝ) (a n * q n)
      _ = 1 + |a n| * |q n| := by rw [abs_one, abs_mul]
      _ ≤ 1 + M * |q 0| :=
        (add_le_add (le_refl 1)
          (mul_le_mul ih (shimizu_recurrence_abs_le_initial q hq hsmall.le n) (abs_nonneg _) hM))
      _ ≤ M := hM_step

private theorem SpecialPeriods.Triangle.shimizu_recurrence_tendsto (q a : ℕ → ℝ)
    (hq : ∀ n, q (n + 1) = -(q n) ^ 2) (ha : ∀ n, a (n + 1) = 1 - a n * q n)
    (hsmall : |q 0| < 1) :
    Filter.Tendsto q Filter.atTop (𝓝 0) ∧ Filter.Tendsto a Filter.atTop (𝓝 1) := by
  have hpow : Filter.Tendsto (fun n : ℕ => |q 0| ^ (n + 1)) Filter.atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hsmall).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hqt : Filter.Tendsto q Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (f := q) (fun n => ?_) hpow
    exact shimizu_recurrence_geometric_bound q hq hsmall.le n
  let M : ℝ := (1 + |a 0|) / (1 - |q 0|)
  have hM : 0 ≤ M := div_nonneg (by positivity) (sub_pos.mpr hsmall).le
  have hprod : Filter.Tendsto (fun n => a n * q n) Filter.atTop (𝓝 0) := by
    refine
      squeeze_zero_norm (f := fun n : ℕ => a n * q n) (a := fun n => M * |q 0| ^ (n + 1)) ?_ ?_
    · intro n
      rw [Real.norm_eq_abs, abs_mul]
      exact
        mul_le_mul (shimizu_recurrence_a_bound q a hq ha hsmall n)
          (shimizu_recurrence_geometric_bound q hq hsmall.le n) (abs_nonneg _) hM
    · simpa only [MulZeroClass.mul_zero] using hpow.const_mul M
  refine ⟨hqt, (Filter.tendsto_add_atTop_iff_nat 1).mp ?_⟩
  simpa only [ha, sub_zero] using hprod.const_sub 1

private theorem SpecialPeriods.Triangle.shimizuSequence_tendsto_translation (w : ℝ) (A : SL(2, ℝ))
    (hw : w ≠ 0) (hsmall : |w * A 1 0| < 1) :
    Filter.Tendsto (shimizuSequence w A) Filter.atTop (𝓝 (shimizuTranslation w)) := by
  obtain ⟨hq, ha⟩ :=
    shimizu_recurrence_tendsto (fun n => w * shimizuSequence w A n 1 0)
      (fun n => shimizuSequence w A n 0 0) (shimizuSequence_succ_scaled_lower_left w A)
      (shimizuSequence_succ_zero_zero w A) hsmall
  have hc : Filter.Tendsto (fun n => shimizuSequence w A n 1 0) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [hw] using hq.div_const w
  have hp :
    Filter.Tendsto (fun n => shimizuSequence w A n 0 0 * (w * shimizuSequence w A n 1 0))
      Filter.atTop (𝓝 (0 : ℝ)) := by simpa only [one_mul] using ha.mul hq
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j
  · change Filter.Tendsto (fun n => shimizuSequence w A n 0 0) Filter.atTop (𝓝 (1 : ℝ))
    exact ha
  · change Filter.Tendsto (fun n => shimizuSequence w A n 0 1) Filter.atTop (𝓝 w)
    apply (Filter.tendsto_add_atTop_iff_nat 1).mp
    simpa only [shimizuSequence_succ_zero_one, one_pow, mul_one] using (ha.pow 2).const_mul w
  · change Filter.Tendsto (fun n => shimizuSequence w A n 1 0) Filter.atTop (𝓝 (0 : ℝ))
    exact hc
  · change Filter.Tendsto (fun n => shimizuSequence w A n 1 1) Filter.atTop (𝓝 (1 : ℝ))
    apply (Filter.tendsto_add_atTop_iff_nat 1).mp
    simpa only [shimizuSequence_succ_one_one, add_zero] using hp.const_add 1

private theorem SpecialPeriods.Triangle.shimizu_leutbecher_scaled (Γ : Subgroup (SL(2, ℝ)))
    [DiscreteTopology Γ] (w : ℝ) (hw : w ≠ 0) (hT : shimizuTranslation w ∈ Γ) (A : SL(2, ℝ))
    (hA : A ∈ Γ) (hc : A 1 0 ≠ 0) : 1 ≤ |w * A 1 0| := by
  by_contra! hsmall
  let u : ℕ → Γ := fun n => ⟨shimizuSequence w A n, shimizuSequence_mem Γ w A hT hA n⟩
  let t : Γ := ⟨shimizuTranslation w, hT⟩
  have ht : Filter.Tendsto u Filter.atTop (𝓝 t) :=
    tendsto_subtype_rng.mpr (shimizuSequence_tendsto_translation w A hw hsmall)
  have he : ∀ᶠ n in Filter.atTop, u n = t := by
    simpa only [nhds_discrete, Filter.tendsto_pure] using ht
  obtain ⟨n, hn⟩ := he.exists
  have hzero : shimizuSequence w A n 1 0 = 0 := by
    have h := congrArg (fun B : Γ => (B : SL(2, ℝ)) 1 0) hn
    simpa [u, t, shimizuTranslation] using h
  exact shimizuSequence_lower_left_ne_zero w A hw hc n hzero

private theorem
    SpecialPeriods.Triangle.shimizu_leutbecher (Γ : Subgroup (SL(2, ℝ))) [DiscreteTopology Γ]
    (w : ℝ) (hw : 0 < w) (hT : shimizuTranslation w ∈ Γ) (A : SL(2, ℝ)) (hA : A ∈ Γ)
    (hc : A 1 0 ≠ 0) : 1 / w ≤ |A 1 0| := by
  apply (div_le_iff₀ hw).mpr
  simpa only [abs_mul, abs_of_pos hw, mul_comm] using
    shimizu_leutbecher_scaled Γ w hw.ne' hT A hA hc

private theorem
    SpecialPeriods.Triangle.matrixGroup_lower_left_bound (A : SL(2, ℝ)) (hA : A ∈ matrixGroup)
    (hc : A 1 0 ≠ 0) : 1 / width ≤ |A 1 0| := by
  apply shimizu_leutbecher matrixGroup width width_pos ?_ A hA hc
  rw [shimizuTranslation_width, ← generatorOneSL_mul_generatorTwoSL]
  exact matrixGroup.mul_mem generatorOneSL_mem_matrixGroup generatorTwoSL_mem_matrixGroup

private def SpecialPeriods.modularProjectivization : SL(2, ℤ) →* PSL(2, ℤ) :=
  QuotientGroup.mk' (Subgroup.center (SL(2, ℤ)))

private theorem SpecialPeriods.modular_neg_one_mem_center_mo1973_15869 :
    (-1 : SL(2, ℤ)) ∈ Subgroup.center (SL(2, ℤ)) := by
  apply Subgroup.mem_center_iff.mpr
  intro A
  apply Subtype.ext
  change (A : Matrix (Fin 2) (Fin 2) ℤ) * (-1) = (-1) * A
  simp

private theorem SpecialPeriods.modularProjectivization_neg_one : modularProjectivization (-1) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr modular_neg_one_mem_center_mo1973_15869

@[simp]
private theorem SpecialPeriods.modularProjectivization_neg (A : SL(2, ℤ)) :
    modularProjectivization (-A) = modularProjectivization A := by
  have hn : (-1 : SL(2, ℤ)) * A = -A := by
    apply Subtype.ext
    change (-1 : Matrix (Fin 2) (Fin 2) ℤ) * A = -(A : Matrix (Fin 2) (Fin 2) ℤ)
    simp
  rw [← hn, map_mul, modularProjectivization_neg_one, one_mul]

private def SpecialPeriods.triangleModularA : SL(2, ℤ) :=
  ⟨!![1, -1; 1, 0], by decide⟩

private theorem SpecialPeriods.triangleModularA_eq_T_mul_S :
    triangleModularA = ModularGroup.T * ModularGroup.S := by decide

private theorem SpecialPeriods.triangleModularA_cube : triangleModularA ^ 3 = -1 := by decide

private theorem SpecialPeriods.modularS_square : ModularGroup.S ^ 2 = -1 := by decide

private theorem SpecialPeriods.triangleModularA_mul_S :
    triangleModularA * ModularGroup.S = -ModularGroup.T := by decide

private def SpecialPeriods.triangleModularGenerator₁ : PSL(2, ℤ) :=
  modularProjectivization triangleModularA

private def SpecialPeriods.triangleModularGenerator₂ : PSL(2, ℤ) :=
  modularProjectivization ModularGroup.S

@[simp]
private theorem
    SpecialPeriods.triangleModularGenerator₁_cube : triangleModularGenerator₁ ^ 3 = 1 := by
  rw [triangleModularGenerator₁, ← map_pow, triangleModularA_cube,
    modularProjectivization_neg_one]

@[simp]
private theorem
    SpecialPeriods.triangleModularGenerator₂_square : triangleModularGenerator₂ ^ 2 = 1 := by
  rw [triangleModularGenerator₂, ← map_pow, modularS_square, modularProjectivization_neg_one]

private theorem
    SpecialPeriods.triangleModularGenerator₂_fourth : triangleModularGenerator₂ ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, triangleModularGenerator₂_square, one_pow]

private theorem SpecialPeriods.triangleModularGenerator₁_mul_generator₂ :
    triangleModularGenerator₁ * triangleModularGenerator₂ =
      modularProjectivization ModularGroup.T := by
  rw [triangleModularGenerator₁, triangleModularGenerator₂, ← map_mul, triangleModularA_mul_S,
    modularProjectivization_neg]

private def SpecialPeriods.triangleModularRepresentation : TriangleGroup →* PSL(2, ℤ) :=
  triangleLift triangleModularGenerator₁ triangleModularGenerator₂ triangleModularGenerator₁_cube
    triangleModularGenerator₂_fourth

@[simp]
private theorem SpecialPeriods.triangleModularRepresentation_generator₁ :
    triangleModularRepresentation triangleGenerator₁ = triangleModularGenerator₁ :=
  triangleLift_generator₁ ..

@[simp]
private theorem SpecialPeriods.triangleModularRepresentation_generator₂ :
    triangleModularRepresentation triangleGenerator₂ = triangleModularGenerator₂ :=
  triangleLift_generator₂ ..

@[simp]
private theorem SpecialPeriods.triangleModularRepresentation_cusp :
    triangleModularRepresentation triangleCuspGenerator =
      modularProjectivization ModularGroup.T⁻¹ := by
  rw [triangleModularRepresentation, triangleLift_cusp, triangleModularGenerator₁_mul_generator₂,
    map_inv]

private theorem SpecialPeriods.modular_center_eq_one_or_neg_one_mo1973_15891 (A : SL(2, ℤ))
    (hA : A ∈ Subgroup.center (SL(2, ℤ))) : A = 1 ∨ A = -1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr₂ : r ^ 2 = 1 := by simpa using hr
  rcases sq_eq_one_iff.mp hr₂ with rfl | rfl
  · left
    apply Subtype.ext
    simpa using hrA.symm
  · right
    apply Subtype.ext
    simpa using hrA.symm

private theorem SpecialPeriods.modular_center_le_permutation_kernel_mo1973_15892 :
    Subgroup.center (SL(2, ℤ)) ≤ (MulAction.toPermHom (SL(2, ℤ)) ℍ).ker := by
  intro A hA
  rcases modular_center_eq_one_or_neg_one_mo1973_15891 A hA with rfl | rfl
  · exact map_one _
  · apply Equiv.ext
    intro z
    change (-1 : SL(2, ℤ)) • z = z
    simp

private def SpecialPeriods.modularPSLPermutation : PSL(2, ℤ) →* Equiv.Perm ℍ :=
  QuotientGroup.lift (Subgroup.center (SL(2, ℤ))) (MulAction.toPermHom (SL(2, ℤ)) ℍ)
    modular_center_le_permutation_kernel_mo1973_15892

@[simp]
private theorem SpecialPeriods.modularPSLPermutation_projectivization (A : SL(2, ℤ)) (z : ℍ) :
    modularPSLPermutation (modularProjectivization A) z = A • z :=
  rfl

private def SpecialPeriods.triangleModularAction : TriangleGroup →* Equiv.Perm ℍ :=
  modularPSLPermutation.comp triangleModularRepresentation

@[simp]
private theorem SpecialPeriods.triangleModularAction_generator₁_apply (z : ℍ) :
    triangleModularAction triangleGenerator₁ z = triangleModularA • z := by
  simp [triangleModularAction, triangleModularGenerator₁]

@[simp]
private theorem SpecialPeriods.triangleModularAction_generator₂_apply (z : ℍ) :
    triangleModularAction triangleGenerator₂ z = ModularGroup.S • z := by
  simp [triangleModularAction, triangleModularGenerator₂]

private theorem SpecialPeriods.triangleModularAction_generator₁_coe (z : ℍ) :
    (triangleModularAction triangleGenerator₁ z : ℂ) = (z - 1) / z := by
  rw [triangleModularAction_generator₁_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [triangleModularA, sub_eq_add_neg]

private theorem SpecialPeriods.triangleModularAction_generator₂_coe (z : ℍ) :
    (triangleModularAction triangleGenerator₂ z : ℂ) = -1 / z := by
  rw [triangleModularAction_generator₂_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [ModularGroup.S]

@[simp]
private theorem SpecialPeriods.triangleModularAction_cusp_apply (z : ℍ) :
    triangleModularAction triangleCuspGenerator z = (-1 : ℝ) +ᵥ z := by
  change modularPSLPermutation (triangleModularRepresentation triangleCuspGenerator) z = _
  rw [triangleModularRepresentation_cusp, modularPSLPermutation_projectivization]
  simpa using UpperHalfPlane.modular_T_zpow_smul z (-1)

private theorem SpecialPeriods.triangleModularAction_cusp_coe (z : ℍ) :
    (triangleModularAction triangleCuspGenerator z : ℂ) = z - 1 := by
  simp [sub_eq_add_neg, add_comm]

private theorem SpecialPeriods.neg_triangleModularA_cube : (-triangleModularA) ^ 3 = 1 := by decide

private theorem SpecialPeriods.modularS_fourth : ModularGroup.S ^ 4 = 1 := by decide

private theorem SpecialPeriods.neg_triangleModularA_mul_S :
    (-triangleModularA) * ModularGroup.S = ModularGroup.T := by decide

private def SpecialPeriods.triangleModularLinearRepresentation : TriangleGroup →* SL(2, ℤ) :=
  triangleLift (-triangleModularA) ModularGroup.S neg_triangleModularA_cube modularS_fourth

@[simp]
private theorem SpecialPeriods.triangleModularLinearRepresentation_cusp :
    triangleModularLinearRepresentation triangleCuspGenerator = ModularGroup.T⁻¹ := by
  rw [triangleModularLinearRepresentation, triangleLift_cusp, neg_triangleModularA_mul_S]

private theorem SpecialPeriods.equalDiagonalTriangular_pow_succ_mo1973_15916 {R : Type*}
    [CommSemiring R] (a b : R) (n : ℕ) :
    (!![a, b; 0, a] : Matrix (Fin 2) (Fin 2) R) ^ (n + 1) =
      !![a ^ (n + 1), ((n + 1 : ℕ) : R) * a ^ n * b; 0, a ^ (n + 1)] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Nat.cast_add, Nat.cast_one]
    all_goals ring

private theorem SpecialPeriods.integerTriangular_pow_upper_right_dvd_mo1973_15917 (a b : ℤ)
    (n : ℕ) : (n : ℤ) ∣ ((!![a, b; 0, a] : Matrix (Fin 2) (Fin 2) ℤ) ^ n) 0 1 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [equalDiagonalTriangular_pow_succ_mo1973_15916]
    refine ⟨a ^ n * b, ?_⟩
    simp [mul_assoc]

private theorem SpecialPeriods.integerMatrix_commute_translation_entries_mo1973_15918
    (M : Matrix (Fin 2) (Fin 2) ℤ) (h : Commute M !![1, -1; 0, 1]) : M 1 0 = 0 ∧ M 0 0 = M 1 1 := by
  have h₀ := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℤ => N 0 0) h.eq
  have h₁ := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℤ => N 0 1) h.eq
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h₀ h₁
  constructor <;> linarith

private theorem SpecialPeriods.integerMatrix_translationInverse_pow_exponent
    (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) (h : M ^ n = !![1, -1; 0, 1]) : n = 1 := by
  have hc : Commute M !![1, -1; 0, 1] := by
    rw [← h]
    exact Commute.self_pow M n
  obtain ⟨hc₀, hc₁⟩ := integerMatrix_commute_translation_entries_mo1973_15918 M hc
  have hM : M = !![M 0 0, M 0 1; 0, M 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc₀, hc₁]
  have hd := integerTriangular_pow_upper_right_dvd_mo1973_15917 (M 0 0) (M 0 1) n
  rw [← hM, h] at hd
  apply Nat.eq_one_of_dvd_one
  simpa [Int.natCast_dvd] using hd

private theorem SpecialPeriods.modular_T_inv_pow_exponent (M : SL(2, ℤ)) (n : ℕ)
    (h : M ^ n = ModularGroup.T⁻¹) : n = 1 := by
  apply integerMatrix_translationInverse_pow_exponent (M : Matrix (Fin 2) (Fin 2) ℤ) n
  simpa only [Matrix.SpecialLinearGroup.coe_pow, ModularGroup.coe_T_inv] using
    congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ)) h

private theorem SpecialPeriods.triangleCuspGenerator_pow_root_exponent (g : TriangleGroup) (n : ℕ)
    (h : g ^ n = triangleCuspGenerator) : n = 1 := by
  apply modular_T_inv_pow_exponent (triangleModularLinearRepresentation g) n
  rw [← map_pow, h, triangleModularLinearRepresentation_cusp]

private theorem SpecialPeriods.triangleCuspGenerator_zpow_root_exponent (g : TriangleGroup) (k : ℤ)
    (h : g ^ k = triangleCuspGenerator) : k.natAbs = 1 := by
  cases k with
  | ofNat n =>
    apply triangleCuspGenerator_pow_root_exponent g n
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using h
  | negSucc n =>
    apply triangleCuspGenerator_pow_root_exponent g⁻¹ (n + 1)
    simpa only [zpow_negSucc, inv_pow] using h

@[simp]
private theorem SpecialPeriods.Triangle.shimizuTranslation_zero : shimizuTranslation 0 = 1 := by
  apply Subtype.ext
  simp [coe_shimizuTranslation, Matrix.one_fin_two]

private theorem SpecialPeriods.Triangle.shimizuTranslation_add (s t : ℝ) :
    shimizuTranslation (s + t) = shimizuTranslation s * shimizuTranslation t := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_shimizuTranslation, add_comm]

@[simp]
private theorem SpecialPeriods.Triangle.shimizuTranslation_inv (t : ℝ) :
    (shimizuTranslation t)⁻¹ = shimizuTranslation (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← shimizuTranslation_add, add_neg_cancel, shimizuTranslation_zero]

private def SpecialPeriods.Triangle.shimizuTranslationHom : Multiplicative ℝ →* SL(2, ℝ)
    where
  toFun t := shimizuTranslation t.toAdd
  map_one' := shimizuTranslation_zero
  map_mul' s t := shimizuTranslation_add s.toAdd t.toAdd

@[simp]
private theorem SpecialPeriods.Triangle.shimizuTranslationHom_apply (t : ℝ) :
    shimizuTranslationHom (Multiplicative.ofAdd t) = shimizuTranslation t :=
  rfl

private theorem SpecialPeriods.Triangle.shimizuTranslation_zpow (t : ℝ) (n : ℤ) :
    shimizuTranslation t ^ n = shimizuTranslation ((n : ℝ) * t) := by
  simpa only [← ofAdd_zsmul, shimizuTranslationHom_apply, zsmul_eq_mul] using
    (map_zpow shimizuTranslationHom (Multiplicative.ofAdd t) n).symm

private theorem SpecialPeriods.Triangle.shimizuTranslation_injective :
    Function.Injective shimizuTranslation := by
  intro s t h
  have he := congrArg (fun A : SL(2, ℝ) => A 0 1) h
  simpa [shimizuTranslation] using he

private theorem
    SpecialPeriods.Triangle.shimizuTranslation_continuous : Continuous shimizuTranslation := by
  apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
  change Continuous (fun t : ℝ => (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    first
    | exact continuous_const
    | exact continuous_id

private theorem SpecialPeriods.Triangle.shimizuTranslation_neg_width :
    shimizuTranslation (-width) = cuspSL := by
  rw [← shimizuTranslation_inv, shimizuTranslation_width]
  rfl

private def SpecialPeriods.Triangle.translationSubgroup (Γ : Subgroup (SL(2, ℝ))) : AddSubgroup ℝ
    where
  carrier := {t | shimizuTranslation t ∈ Γ}
  zero_mem' := by
    change shimizuTranslation 0 ∈ Γ
    rw [shimizuTranslation_zero]
    exact Γ.one_mem
  add_mem' := by
    intro s t hs ht
    change shimizuTranslation (s + t) ∈ Γ
    rw [shimizuTranslation_add]
    exact Γ.mul_mem hs ht
  neg_mem' := by
    intro t ht
    change shimizuTranslation (-t) ∈ Γ
    rw [← shimizuTranslation_inv]
    exact Γ.inv_mem ht

private def SpecialPeriods.Triangle.translationSubgroupMap (Γ : Subgroup (SL(2, ℝ))) :
    translationSubgroup Γ → Γ := fun t => ⟨shimizuTranslation t, t.property⟩

private theorem SpecialPeriods.Triangle.translationSubgroupMap_injective (Γ : Subgroup (SL(2, ℝ))) :
    Function.Injective (translationSubgroupMap Γ) := by
  intro s t h
  apply Subtype.ext
  exact shimizuTranslation_injective (congrArg Subtype.val h)

private theorem
    SpecialPeriods.Triangle.translationSubgroupMap_continuous (Γ : Subgroup (SL(2, ℝ))) :
    Continuous (translationSubgroupMap Γ) := by
  apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
  exact shimizuTranslation_continuous.comp continuous_subtype_val

private instance SpecialPeriods.Triangle.translationSubgroup_discrete (Γ : Subgroup (SL(2, ℝ)))
    [DiscreteTopology Γ] : DiscreteTopology (translationSubgroup Γ) :=
  DiscreteTopology.of_continuous_injective (translationSubgroupMap_continuous Γ)
    (translationSubgroupMap_injective Γ)

private theorem SpecialPeriods.Triangle.translationSubgroup_cyclic (Γ : Subgroup (SL(2, ℝ)))
    [DiscreteTopology Γ] : ∃ t : ℝ, translationSubgroup Γ = AddSubgroup.zmultiples t := by
  have hc : IsAddCyclic (translationSubgroup Γ) :=
    AddSubgroup.discrete_iff_addCyclic.mpr inferInstance
  obtain ⟨t, ht⟩ :=
    (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top (translationSubgroup Γ)).mp hc
  exact ⟨t, ht.symm⟩

private theorem SpecialPeriods.Triangle.width_mem_translationSubgroup_matrixGroup :
    width ∈ translationSubgroup matrixGroup := by
  change shimizuTranslation width ∈ matrixGroup
  rw [shimizuTranslation_width, ← cuspSL_inv]
  exact matrixGroup.inv_mem cuspSL_mem_matrixGroup

private theorem SpecialPeriods.Triangle.neg_width_mem_translationSubgroup_matrixGroup :
    -width ∈ translationSubgroup matrixGroup := by
  change shimizuTranslation (-width) ∈ matrixGroup
  rw [shimizuTranslation_neg_width]
  exact cuspSL_mem_matrixGroup

private theorem SpecialPeriods.Triangle.upperTriangular_det (A : SL(2, ℝ)) (hc : A 1 0 = 0) :
    A 0 0 * A 1 1 = 1 := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 :=
    (Matrix.det_fin_two A.val).symm.trans A.property
  simpa only [hc, MulZeroClass.mul_zero, sub_zero] using hdet

private theorem SpecialPeriods.Triangle.upperTriangular_zero_zero_ne_zero (A : SL(2, ℝ))
    (hc : A 1 0 = 0) : A 0 0 ≠ 0 := by
  intro ha
  have h := upperTriangular_det A hc
  simp [ha] at h

private theorem
    SpecialPeriods.Triangle.upperTriangular_one_one_ne_zero (A : SL(2, ℝ)) (hc : A 1 0 = 0) :
    A 1 1 ≠ 0 := by
  intro hd
  have h := upperTriangular_det A hc
  simp [hd] at h

private theorem SpecialPeriods.Triangle.upperTriangular_conjugate_translation (A : SL(2, ℝ))
    (hc : A 1 0 = 0) (t : ℝ) :
    A * shimizuTranslation t * A⁻¹ = shimizuTranslation (t * (A 0 0) ^ 2) := by
  apply Subtype.ext
  rw [shimizu_conjugate_matrix, coe_shimizuTranslation]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc]

private theorem SpecialPeriods.Triangle.upperTriangular_inverse_lower_left (A : SL(2, ℝ))
    (hc : A 1 0 = 0) : (A⁻¹ : SL(2, ℝ)) 1 0 = 0 := by
  change (Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 = 0
  simp [Matrix.adjugate_fin_two, hc]

private theorem SpecialPeriods.Triangle.inverse_upper_left (A : SL(2, ℝ)) :
    (A⁻¹ : SL(2, ℝ)) 0 0 = A 1 1 := by
  change (Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 = A 1 1
  simp [Matrix.adjugate_fin_two]

private theorem SpecialPeriods.Triangle.neg_one_mul_realSL_mo1973_15956 (A : SL(2, ℝ)) :
    (-1 : SL(2, ℝ)) * A = -A := by
  apply Subtype.ext
  change (-1 : Matrix (Fin 2) (Fin 2) ℝ) * A = -(A : Matrix (Fin 2) (Fin 2) ℝ)
  simp

private theorem SpecialPeriods.Triangle.realSLPermutation_neg (A : SL(2, ℝ)) :
    realSLPermutation (-A) = realSLPermutation A := by
  rw [← neg_one_mul_realSL_mo1973_15956, map_mul, realSLPermutation_neg_one, one_mul]

private theorem SpecialPeriods.Triangle.realSLPermutation_eq_iff (A B : SL(2, ℝ)) :
    realSLPermutation A = realSLPermutation B ↔ A = B ∨ A = -B := by
  constructor
  · intro h
    have hk : realSLPermutation (A * B⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    rcases (realSLPermutation_eq_one_iff _).mp hk with hk | hk
    · exact Or.inl (mul_inv_eq_one.mp hk)
    · right
      have he := congrArg (fun C : SL(2, ℝ) => C * B) hk
      simpa only [mul_assoc, inv_mul_cancel, mul_one, neg_one_mul_realSL_mo1973_15956] using he
  · rintro (rfl | rfl)
    · rfl
    · exact realSLPermutation_neg B

private theorem SpecialPeriods.Triangle.matrixGroup_of_permutation_mem_range (A : SL(2, ℝ))
    (h : realSLPermutation A ∈ SpecialPeriods.triangleGeometricRepresentation.range) :
    A ∈ matrixGroup := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨B, hB⟩ := triangleGeometricRepresentation_matrixGroup_lift g
  rcases (realSLPermutation_eq_iff A B).mp (hg.symm.trans hB.symm) with he | he
  · rw [he]
    exact B.property
  · rw [he, ← neg_one_mul_realSL_mo1973_15956]
    exact matrixGroup.mul_mem neg_one_mem_matrixGroup B.property

private theorem SpecialPeriods.Triangle.same_permutation_lower_left_zero_iff (A B : SL(2, ℝ))
    (h : realSLPermutation A = realSLPermutation B) : A 1 0 = 0 ↔ B 1 0 = 0 := by
  rcases (realSLPermutation_eq_iff A B).mp h with rfl | rfl
  · rfl
  · change -(B 1 0) = 0 ↔ B 1 0 = 0
    exact neg_eq_zero

private theorem SpecialPeriods.Triangle.matrixGroup_translationSubgroup_eq :
    translationSubgroup matrixGroup = AddSubgroup.zmultiples width := by
  obtain ⟨t, ht⟩ := translationSubgroup_cyclic matrixGroup
  have ht_mem : shimizuTranslation t ∈ matrixGroup := by
    change t ∈ translationSubgroup matrixGroup
    rw [ht]
    exact AddSubgroup.mem_zmultiples t
  have hw := neg_width_mem_translationSubgroup_matrixGroup
  rw [ht, AddSubgroup.mem_zmultiples_iff] at hw
  obtain ⟨k, hk⟩ := hw
  obtain ⟨g, hg⟩ := matrixGroup_permutation_lift (shimizuTranslation t) ht_mem
  have hroot : g ^ k = SpecialPeriods.triangleCuspGenerator := by
    apply SpecialPeriods.triangleGeometricRepresentation_injective
    rw [map_zpow, hg, ← map_zpow, shimizuTranslation_zpow]
    have hk' : (k : ℝ) * t = -width := by simpa only [zsmul_eq_mul] using hk
    rw [hk', shimizuTranslation_neg_width]
    exact SpecialPeriods.triangleGeometricRepresentation_cusp.symm
  have hk_abs := SpecialPeriods.triangleCuspGenerator_zpow_root_exponent g k hroot
  have hk_cases : k = 1 ∨ k = -1 := by omega
  rcases hk_cases with rfl | rfl
  · have ht' : t = -width := by simpa using hk
    rw [ht, ht', AddSubgroup.zmultiples_neg]
  · have ht' : t = width := by simpa using congrArg Neg.neg hk
    rw [ht, ht']

private theorem SpecialPeriods.Triangle.shimizuTranslation_mem_matrixGroup_iff (t : ℝ) :
    shimizuTranslation t ∈ matrixGroup ↔ ∃ n : ℤ, t = (n : ℝ) * width := by
  change t ∈ translationSubgroup matrixGroup ↔ _
  rw [matrixGroup_translationSubgroup_eq, AddSubgroup.mem_zmultiples_iff]
  simp only [zsmul_eq_mul, eq_comm]

private theorem SpecialPeriods.Triangle.upperTriangular_square_is_integer_mo1973_15963
    (A : SL(2, ℝ)) (hA : A ∈ matrixGroup) (hc : A 1 0 = 0) : ∃ n : ℤ, (A 0 0) ^ 2 = (n : ℝ) := by
  have hT : shimizuTranslation width ∈ matrixGroup := width_mem_translationSubgroup_matrixGroup
  have hconj := matrixGroup.mul_mem (matrixGroup.mul_mem hA hT) (matrixGroup.inv_mem hA)
  rw [upperTriangular_conjugate_translation A hc width] at hconj
  obtain ⟨n, hn⟩ := (shimizuTranslation_mem_matrixGroup_iff _).mp hconj
  refine ⟨n, mul_left_cancel₀ width_ne_zero ?_⟩
  simpa only [mul_comm] using hn

private theorem SpecialPeriods.Triangle.matrixGroup_upperTriangular_square_eq_one (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 = 0) : (A 0 0) ^ 2 = 1 := by
  obtain ⟨m, hm⟩ := upperTriangular_square_is_integer_mo1973_15963 A hA hc
  obtain ⟨n, hn⟩ :=
    upperTriangular_square_is_integer_mo1973_15963 A⁻¹ (matrixGroup.inv_mem hA)
      (upperTriangular_inverse_lower_left A hc)
  rw [inverse_upper_left] at hn
  have hmpos : (0 : ℤ) < m := by
    have hp : (0 : ℝ) < (m : ℝ) := by
      rw [← hm]
      exact sq_pos_of_ne_zero (upperTriangular_zero_zero_ne_zero A hc)
    exact_mod_cast hp
  have hnpos : (0 : ℤ) < n := by
    have hp : (0 : ℝ) < (n : ℝ) := by
      rw [← hn]
      exact sq_pos_of_ne_zero (upperTriangular_one_one_ne_zero A hc)
    exact_mod_cast hp
  have hmn : m * n = 1 := by
    have he : (m : ℝ) * (n : ℝ) = 1 := by
      rw [← hm, ← hn, ← mul_pow, upperTriangular_det A hc, one_pow]
    exact_mod_cast he
  have hm1 : (1 : ℤ) ≤ m := by omega
  have hn1 : (1 : ℤ) ≤ n := by omega
  have hprod : 0 ≤ m * (n - 1) := mul_nonneg hmpos.le (sub_nonneg.mpr hn1)
  have hm_eq : m = 1 := by nlinarith [hmn]
  rw [hm, hm_eq, Int.cast_one]

private theorem SpecialPeriods.Triangle.upperTriangular_eq_signed_translation_mo1973_15965
    (A : SL(2, ℝ)) (hc : A 1 0 = 0) (ha : (A 0 0) ^ 2 = 1) :
    A = shimizuTranslation (A 0 0 * A 0 1) ∨ A = -shimizuTranslation (A 0 0 * A 0 1) := by
  have hdet := upperTriangular_det A hc
  rcases sq_eq_one_iff.mp ha with ha | ha
  · have hd : A 1 1 = 1 := by simpa [ha] using hdet
    left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_shimizuTranslation, ha, hd, hc]
  · have hd : A 1 1 = -1 := by rw [ha] at hdet; linarith
    right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_shimizuTranslation, ha, hd, hc]

private theorem SpecialPeriods.Triangle.translation_int_width_eq_cusp_zpow_mo1973_15966 (n : ℤ) :
    shimizuTranslation ((n : ℝ) * width) = cuspSL ^ (-n) := by
  rw [← shimizuTranslation_neg_width, shimizuTranslation_zpow]
  simp

private theorem SpecialPeriods.Triangle.matrixGroup_upperTriangular_iff (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) : A 1 0 = 0 ↔ ∃ n : ℤ, A = cuspSL ^ n ∨ A = -(cuspSL ^ n) := by
  constructor
  · intro hc
    have hs :=
      upperTriangular_eq_signed_translation_mo1973_15965 A hc
        (matrixGroup_upperTriangular_square_eq_one A hA hc)
    have ht : shimizuTranslation (A 0 0 * A 0 1) ∈ matrixGroup := by
      rcases hs with he | he
      · exact he ▸ hA
      · have hneg : -A ∈ matrixGroup := by
          rw [← neg_one_mul_realSL_mo1973_15956]
          exact matrixGroup.mul_mem neg_one_mem_matrixGroup hA
        have he' := congrArg (fun B : SL(2, ℝ) => -B) he
        rw [neg_neg] at he'
        exact he' ▸ hneg
    obtain ⟨n, hn⟩ := (shimizuTranslation_mem_matrixGroup_iff _).mp ht
    refine ⟨-n, ?_⟩
    simpa only [hn, translation_int_width_eq_cusp_zpow_mo1973_15966] using hs
  · rintro ⟨n, rfl | rfl⟩
    · rw [← shimizuTranslation_neg_width, shimizuTranslation_zpow]
      rfl
    · change -((cuspSL ^ n) 1 0) = 0
      rw [← shimizuTranslation_neg_width, shimizuTranslation_zpow]
      simp [shimizuTranslation]

private theorem SpecialPeriods.Triangle.matrixGroup_upperTriangular_permutation (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 = 0) :
    ∃ n : ℤ,
      realSLPermutation A =
        SpecialPeriods.triangleGeometricRepresentation
          (SpecialPeriods.triangleCuspGenerator ^ n) := by
  obtain ⟨n, he | he⟩ := (matrixGroup_upperTriangular_iff A hA).mp hc
  · refine ⟨n, ?_⟩
    rw [he, map_zpow, map_zpow, SpecialPeriods.triangleGeometricRepresentation_cusp]
  · refine ⟨n, ?_⟩
    rw [he, realSLPermutation_neg, map_zpow, map_zpow,
      SpecialPeriods.triangleGeometricRepresentation_cusp]

private theorem SpecialPeriods.Triangle.matrixGroup_upperTriangular_smul (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 = 0) : ∃ n : ℤ, ∀ z : ℍ, A • z = (-(n : ℝ) * width) +ᵥ z :=
  by
  obtain ⟨n, hn⟩ := matrixGroup_upperTriangular_permutation A hA hc
  refine ⟨n, fun z => ?_⟩
  change realSLPermutation A z = _
  rw [hn, SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_apply]

private theorem SpecialPeriods.Triangle.triangleGeometric_upperTriangular_lift_iff
    (g : SpecialPeriods.TriangleGroup) (A : SL(2, ℝ))
    (hA : realSLPermutation A = SpecialPeriods.triangleGeometricRepresentation g) :
    A 1 0 = 0 ↔ g ∈ Subgroup.zpowers SpecialPeriods.triangleCuspGenerator := by
  constructor
  · intro hc
    have hmem : A ∈ matrixGroup := matrixGroup_of_permutation_mem_range A ⟨g, hA.symm⟩
    obtain ⟨n, hn⟩ := matrixGroup_upperTriangular_permutation A hmem hc
    exact
      Subgroup.mem_zpowers_iff.mpr
        ⟨n, SpecialPeriods.triangleGeometricRepresentation_injective (hn.symm.trans hA)⟩
  · intro hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have he : realSLPermutation A = realSLPermutation (cuspSL ^ n) := by
      rw [hA, map_zpow, map_zpow, SpecialPeriods.triangleGeometricRepresentation_cusp]
    apply (same_permutation_lower_left_zero_iff _ _ he).mpr
    rw [← shimizuTranslation_neg_width, shimizuTranslation_zpow]
    rfl

private def SpecialPeriods.Triangle.horodisc (Y : ℝ) : TopologicalSpace.Opens ℍ :=
  ⟨{z | Y < z.im}, isOpen_lt continuous_const UpperHalfPlane.continuous_im⟩

private theorem SpecialPeriods.Triangle.normSq_slDenom_lower_bound (A : SL(2, ℝ)) (z : ℍ) :
    (A 1 0) ^ 2 * z.im ^ 2 ≤ Complex.normSq (slDenom A z) := by
  have he : Complex.normSq (slDenom A z) = (A 1 0 * z.re + A 1 1) ^ 2 + (A 1 0 * z.im) ^ 2 := by
    simp [slDenom, Complex.normSq_apply, pow_two]
  rw [he]
  nlinarith [sq_nonneg (A 1 0 * z.re + A 1 1)]

private theorem SpecialPeriods.Triangle.matrixGroup_nonparabolic_im_bound (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 ≠ 0) (z : ℍ) : (A • z).im ≤ width ^ 2 / z.im := by
  have hlow := matrixGroup_lower_left_bound A hA hc
  have hmul : 1 ≤ |A 1 0| * width := (div_le_iff₀ width_pos).mp hlow
  have hsq : 1 ≤ (A 1 0) ^ 2 * width ^ 2 := by
    have hs :=
      sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg (abs_nonneg (A 1 0)) width_pos.le) |>.mpr
        hmul
    simpa only [one_pow, mul_pow, sq_abs] using hs
  have hn := normSq_slDenom_lower_bound A z
  have hden := Complex.normSq_pos.mpr (slDenom_ne_zero A z)
  rw [sl_im]
  apply (div_le_iff₀ hden).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ z.im_pos).mpr
  have h₁ := mul_le_mul_of_nonneg_left hn (sq_nonneg width)
  have h₂ := mul_le_mul_of_nonneg_right hsq (sq_nonneg z.im)
  nlinarith

private theorem SpecialPeriods.Triangle.matrixGroup_nonparabolic_above_width (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 ≠ 0) (z : ℍ) (hz : width < z.im) : (A • z).im < width := by
  apply lt_of_le_of_lt (matrixGroup_nonparabolic_im_bound A hA hc z)
  apply (div_lt_iff₀ z.im_pos).mpr
  nlinarith [width_pos]

private theorem SpecialPeriods.Triangle.matrixGroup_nonparabolic_disjoint_horodisc (Y : ℝ)
    (hY : width ≤ Y) (A : SL(2, ℝ)) (hA : A ∈ matrixGroup) (hc : A 1 0 ≠ 0) :
    Disjoint ((fun z : ℍ => A • z) '' (horodisc Y : Set ℍ)) (horodisc Y) := by
  apply Set.disjoint_left.mpr
  rintro w ⟨z, hz, rfl⟩ hw
  have hlow := matrixGroup_nonparabolic_above_width A hA hc z (hY.trans_lt hz)
  exact (not_lt_of_ge (le_trans hlow.le hY)) hw

private theorem SpecialPeriods.Triangle.matrixGroup_horodisc_overlap_lower_left_zero (Y : ℝ)
    (hY : width ≤ Y) (A : SL(2, ℝ)) (hA : A ∈ matrixGroup)
    (hinter : ((fun z : ℍ => A • z) '' (horodisc Y : Set ℍ) ∩ horodisc Y).Nonempty) : A 1 0 = 0 :=
  by
  by_contra hc
  exact
    (Set.disjoint_iff_inter_eq_empty.mp
          (matrixGroup_nonparabolic_disjoint_horodisc Y hY A hA hc)) ▸
        hinter |>.ne_empty
      rfl

private theorem
    SpecialPeriods.Triangle.horodisc_nonempty (Y : ℝ) : (horodisc Y : Set ℍ).Nonempty := by
  let z : ℍ :=
    ⟨((Max.max Y 0 + 1 : ℝ) : ℂ) * Complex.I,
      by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
        mul_one, MulZeroClass.mul_zero, add_zero]
      linarith [le_max_right Y 0]⟩
  refine ⟨z, ?_⟩
  change Y < (((Max.max Y 0 + 1 : ℝ) : ℂ) * Complex.I).im
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
    mul_one, MulZeroClass.mul_zero, add_zero]
  linarith [le_max_left Y 0]

private theorem SpecialPeriods.Triangle.cusp_horodisc_invariant (Y : ℝ)
    (g : Subgroup.zpowers SpecialPeriods.triangleCuspGenerator) :
    Set.MapsTo
      (fun z : ℍ =>
        SpecialPeriods.triangleGeometricRepresentation (g : SpecialPeriods.TriangleGroup) z)
      (horodisc Y) (horodisc Y) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
  intro z hz
  change
    Y < (SpecialPeriods.triangleGeometricRepresentation (g : SpecialPeriods.TriangleGroup) z).im
  rw [← hn, SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_apply,
    UpperHalfPlane.vadd_im]
  exact hz

private theorem SpecialPeriods.Triangle.triangle_horodisc_overlap_mem_cusp (Y : ℝ) (hY : width ≤ Y)
    (g : SpecialPeriods.TriangleGroup)
    (hinter :
      ((SpecialPeriods.triangleGeometricRepresentation g) '' (horodisc Y : Set ℍ) ∩
          horodisc Y).Nonempty) :
    g ∈ Subgroup.zpowers SpecialPeriods.triangleCuspGenerator := by
  obtain ⟨A, hA⟩ := triangleGeometricRepresentation_matrixGroup_lift g
  apply (triangleGeometric_upperTriangular_lift_iff g A hA).mp
  apply matrixGroup_horodisc_overlap_lower_left_zero Y hY A A.property
  have he :
    (fun z : ℍ => (A : SL(2, ℝ)) • z) = SpecialPeriods.triangleGeometricRepresentation g := by
    funext z
    change realSLPermutation A z = SpecialPeriods.triangleGeometricRepresentation g z
    rw [hA]
  simpa only [he] using hinter

private def SpecialPeriods.Triangle.orbitHeightBound (z : ℍ) : ℝ :=
  Max.max z.im (width ^ 2 / z.im)

private theorem SpecialPeriods.Triangle.orbitHeightBound_continuous : Continuous orbitHeightBound :=
  UpperHalfPlane.continuous_im.max
    (continuous_const.div UpperHalfPlane.continuous_im (fun z => z.im_ne_zero))

private theorem SpecialPeriods.Triangle.matrixGroup_im_le_orbitHeightBound (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (z : ℍ) : (A • z).im ≤ orbitHeightBound z := by
  by_cases hc : A 1 0 = 0
  · obtain ⟨n, hn⟩ := matrixGroup_upperTriangular_smul A hA hc
    rw [hn z, UpperHalfPlane.vadd_im]
    exact le_max_left _ _
  · exact (matrixGroup_nonparabolic_im_bound A hA hc z).trans (le_max_right _ _)

private theorem
    SpecialPeriods.Triangle.triangle_im_le_orbitHeightBound (g : SpecialPeriods.TriangleGroup)
    (z : ℍ) : (SpecialPeriods.triangleGeometricRepresentation g z).im ≤ orbitHeightBound z := by
  obtain ⟨A, hA⟩ := triangleGeometricRepresentation_matrixGroup_lift g
  rw [← hA]
  exact matrixGroup_im_le_orbitHeightBound A A.property z

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.triangleMatrixLift (g : TriangleGroup) : Triangle.matrixGroup :=
  (Triangle.triangleGeometricRepresentation_matrixGroup_lift g).choose

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.triangleMatrixLift_spec (g : TriangleGroup) :
    Triangle.realSLPermutation (triangleMatrixLift g) = triangleGeometricRepresentation g :=
  (Triangle.triangleGeometricRepresentation_matrixGroup_lift g).choose_spec

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem
    SpecialPeriods.triangleMatrixLift_injective : Function.Injective triangleMatrixLift := by
  intro g h hgh
  apply triangleGeometricRepresentation_injective
  rw [← triangleMatrixLift_spec, ← triangleMatrixLift_spec, hgh]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.triangleMatrixLift_smul (g : TriangleGroup) (z : ℍ) :
    triangleMatrixLift g • z = g • z := by
  exact congrArg (fun f : Equiv.Perm ℍ => f z) (triangleMatrixLift_spec g)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.triangleGeometricAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul TriangleGroup ℍ where
  finite_disjoint_inter_image {K L} hK
    hL := by
    have hf := Triangle.matrixGroup_finite_compact_transporter hK hL
    apply (hf.preimage triangleMatrixLift_injective.injOn).subset
    rintro g ⟨y, ⟨x, hx, hxy⟩, hy⟩
    exact ⟨y, ⟨x, hx, (triangleMatrixLift_smul g x).trans hxy⟩, hy⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem
    SpecialPeriods.triangleGeometricAction_continuous : ContinuousConstSMul TriangleGroup ℍ
    where continuous_const_smul g := (triangleGeometricRepresentation_holomorphic g).continuous

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangle_isOfFinOrder_of_fixed (g : TriangleGroup) (z : ℍ)
    (hg : triangleGeometricRepresentation g z = z) : IsOfFinOrder g :=
  FreeActionLocus.isOfFinOrder_of_smul_eq TriangleGroup ℍ g z hg

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.triangleRegularLocus : Set ℍ :=
  FreeActionLocus.locus TriangleGroup ℍ

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.mem_triangleRegularLocus_iff (z : ℍ) :
    z ∈ triangleRegularLocus ↔
      ∀ g : TriangleGroup, triangleGeometricRepresentation g z = z → g = 1 :=
  Iff.rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleRegularLocus_invariant (g : TriangleGroup) (z : ℍ) :
    triangleGeometricRepresentation g z ∈ triangleRegularLocus ↔ z ∈ triangleRegularLocus :=
  FreeActionLocus.smul_mem_locus_iff TriangleGroup ℍ g z

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.triangleRegularDomain : TopologicalSpace.Opens ℍ :=
  FreeActionLocus.opens TriangleGroup ℍ

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private abbrev SpecialPeriods.TriangleRegularPoint :=
  triangleRegularDomain

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private instance SpecialPeriods.triangleRegularPoint_locallyCompact :
    LocallyCompactSpace TriangleRegularPoint :=
  triangleRegularDomain.isOpen.locallyCompactSpace

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private instance
    SpecialPeriods.triangleRegularAction : MulAction TriangleGroup TriangleRegularPoint :=
  FreeActionLocus.mulAction TriangleGroup ℍ

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private instance SpecialPeriods.triangleRegularAction_free :
    IsCancelSMul TriangleGroup TriangleRegularPoint :=
  FreeActionLocus.isCancelSMul TriangleGroup ℍ

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private instance SpecialPeriods.triangleRegularAction_continuous :
    ContinuousConstSMul TriangleGroup TriangleRegularPoint :=
  FreeActionLocus.continuousConstSMul TriangleGroup ℍ

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private instance SpecialPeriods.triangleRegularAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul TriangleGroup TriangleRegularPoint :=
  FreeActionLocus.properlyDiscontinuousSMul TriangleGroup ℍ

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleRegularAction_holomorphic (g : TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : TriangleRegularPoint => g • z) :=
  FreeActionLocus.smul_contMDiff TriangleGroup ℍ ℂ ω triangleGeometricRepresentation_holomorphic g

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private abbrev SpecialPeriods.TriangleRegularQuotient :=
  Quotient (MulAction.orbitRel TriangleGroup TriangleRegularPoint)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def
    SpecialPeriods.triangleRegularProject : TriangleRegularPoint → TriangleRegularQuotient :=
  Quotient.mk _

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleRegularProject_surjective :
    Function.Surjective triangleRegularProject :=
  Quotient.mk_surjective

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleRegularProject_covering :
    IsQuotientCoveringMap triangleRegularProject TriangleGroup :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[instance_reducible]
private def
    SpecialPeriods.triangleRegularQuotientChartedSpace : ChartedSpace ℂ TriangleRegularQuotient :=
  CoveringQuotient.chartedSpace (E := ℂ) triangleRegularProject_covering

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleRegularQuotient_isManifold :
    letI := triangleRegularQuotientChartedSpace
    IsManifold 𝓘(ℂ) ω TriangleRegularQuotient :=
  CoveringQuotient.isManifold triangleRegularProject_covering ω triangleRegularAction_holomorphic

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleRegularProject_isLocalDiffeomorph :
    letI := triangleRegularQuotientChartedSpace
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularProject :=
  CoveringQuotient.project_isLocalDiffeomorph triangleRegularProject_covering
    triangleRegularAction_holomorphic

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleRegularProject_holomorphic :
    letI := triangleRegularQuotientChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularProject := by
  let := triangleRegularQuotientChartedSpace
  exact triangleRegularProject_isLocalDiffeomorph.contMDiff

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private abbrev SpecialPeriods.TriangleOrbitSpace :=
  Quotient (MulAction.orbitRel TriangleGroup ℍ)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.triangleOrbitProjection : ℍ → TriangleOrbitSpace :=
  Quotient.mk _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleOrbitProjection_surjective :
    Function.Surjective triangleOrbitProjection :=
  Quotient.mk_surjective

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem
    SpecialPeriods.triangleOrbitProjection_continuous : Continuous triangleOrbitProjection :=
  continuous_quot_mk

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleOrbitProjection_eq_iff (x y : ℍ) :
    triangleOrbitProjection x = triangleOrbitProjection y ↔
      ∃ g : TriangleGroup, triangleGeometricRepresentation g y = x :=
  Quotient.eq''

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.triangleOrbitProjection_smul (g : TriangleGroup) (z : ℍ) :
    triangleOrbitProjection (triangleGeometricRepresentation g z) = triangleOrbitProjection z :=
  (triangleOrbitProjection_eq_iff _ _).mpr ⟨g, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleOrbitProjection_isOpenQuotientMap :
    IsOpenQuotientMap triangleOrbitProjection :=
  MulAction.isOpenQuotientMap_quotientMk

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem
    SpecialPeriods.triangleOrbitProjection_isOpenMap : IsOpenMap triangleOrbitProjection :=
  triangleOrbitProjection_isOpenQuotientMap.isOpenMap

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private instance SpecialPeriods.triangleOrbitSpace_t2 : T2Space TriangleOrbitSpace :=
  inferInstance

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private instance SpecialPeriods.triangleOrbitSpace_locallyCompact :
    LocallyCompactSpace TriangleOrbitSpace :=
  triangleOrbitProjection_isOpenQuotientMap.locallyCompactSpace

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.triangleOrbitCenterOne : TriangleOrbitSpace :=
  triangleOrbitProjection Triangle.centerOne

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.triangleOrbitCenterTwo : TriangleOrbitSpace :=
  triangleOrbitProjection Triangle.centerTwo

private abbrev SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  OnePoint TriangleOrbitSpace

private def SpecialPeriods.triangleCuspPoint : TriangleCompactifiedOrbitSpace :=
  (OnePoint.infty)

private def
    SpecialPeriods.triangleOpenInclusion : TriangleOrbitSpace → TriangleCompactifiedOrbitSpace :=
  OnePoint.some

private theorem SpecialPeriods.triangleOpenInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding triangleOpenInclusion :=
  OnePoint.isOpenEmbedding_coe

private theorem SpecialPeriods.triangleOpenInclusion_ne_cusp (q : TriangleOrbitSpace) :
    triangleOpenInclusion q ≠ triangleCuspPoint :=
  OnePoint.coe_ne_infty q

private theorem SpecialPeriods.triangleCompactifiedOrbitSpace_compact :
    CompactSpace TriangleCompactifiedOrbitSpace :=
  inferInstance

private def SpecialPeriods.Triangle.cuspImage (Y : ℝ) :
    TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace :=
  ⟨SpecialPeriods.triangleOrbitProjection '' (horodisc Y : Set ℍ),
    SpecialPeriods.triangleOrbitProjection_isOpenMap _ (horodisc Y).isOpen⟩

@[simp]
private theorem
    SpecialPeriods.Triangle.mem_cuspImage (Y : ℝ) (q : SpecialPeriods.TriangleOrbitSpace) :
    q ∈ cuspImage Y ↔ ∃ z : ℍ, Y < z.im ∧ SpecialPeriods.triangleOrbitProjection z = q :=
  Iff.rfl

private theorem SpecialPeriods.Triangle.cuspImage_antitone :
    Antitone (fun Y : ℝ => (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace)) := by
  intro Y Z hYZ q hq
  obtain ⟨z, hz, rfl⟩ := hq
  exact ⟨z, hYZ.trans_lt hz, rfl⟩

private theorem SpecialPeriods.Triangle.cuspImage_compl_subset_truncated_image (Y : ℝ) :
    (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace)ᶜ ⊆
      SpecialPeriods.triangleOrbitProjection '' truncatedFordRegion Y := by
  intro q hq
  obtain ⟨z, rfl⟩ := SpecialPeriods.triangleOrbitProjection_surjective q
  obtain ⟨g, hg⟩ := SpecialPeriods.triangle_exists_fordRegion_representative z
  have he :
    SpecialPeriods.triangleOrbitProjection (SpecialPeriods.triangleGeometricRepresentation g z) =
      SpecialPeriods.triangleOrbitProjection z :=
    SpecialPeriods.triangleOrbitProjection_smul g z
  refine ⟨SpecialPeriods.triangleGeometricRepresentation g z, ⟨hg, ?_⟩, he⟩
  apply le_of_not_gt
  intro hi
  exact hq ⟨SpecialPeriods.triangleGeometricRepresentation g z, hi, he⟩

private theorem SpecialPeriods.Triangle.cuspImage_compl_compact (Y : ℝ) :
    IsCompact (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace)ᶜ :=
  ((truncatedFordRegion_compact Y).image
        SpecialPeriods.triangleOrbitProjection_continuous).of_isClosed_subset
    (cuspImage Y).isOpen.isClosed_compl (cuspImage_compl_subset_truncated_image Y)

private def SpecialPeriods.Triangle.cuspNeighborhood (Y : ℝ) :
    TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  OnePoint.opensOfCompl (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace)ᶜ
    (cuspImage Y).isOpen.isClosed_compl (cuspImage_compl_compact Y)

@[simp]
private theorem SpecialPeriods.Triangle.cuspPoint_mem_cuspNeighborhood (Y : ℝ) :
    SpecialPeriods.triangleCuspPoint ∈ cuspNeighborhood Y :=
  OnePoint.infty_mem_opensOfCompl _ _

@[simp]
private theorem SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood (Y : ℝ)
    (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.triangleOpenInclusion q ∈ cuspNeighborhood Y ↔ q ∈ cuspImage Y := by
  change
    (q : OnePoint SpecialPeriods.TriangleOrbitSpace) ∉
        ((↑) : SpecialPeriods.TriangleOrbitSpace → OnePoint SpecialPeriods.TriangleOrbitSpace) ''
          (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace)ᶜ ↔
      _
  simp only [OnePoint.coe_injective.mem_set_image, Set.mem_compl_iff, Classical.not_not]
  rfl

private theorem SpecialPeriods.Triangle.cuspNeighborhood_preimage (Y : ℝ) :
    SpecialPeriods.triangleOpenInclusion ⁻¹'
        (cuspNeighborhood Y : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) =
      cuspImage Y := by
  ext q
  exact openInclusion_mem_cuspNeighborhood Y q

private theorem SpecialPeriods.Triangle.cuspNeighborhood_mem_nhds (Y : ℝ) :
    (cuspNeighborhood Y : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
      𝓝 SpecialPeriods.triangleCuspPoint :=
  (cuspNeighborhood Y).isOpen.mem_nhds (cuspPoint_mem_cuspNeighborhood Y)

private theorem SpecialPeriods.Triangle.width_coe_ne_zero_mo1973_16106 : (width : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr width_ne_zero

private def SpecialPeriods.Triangle.cuspQ (z : ℍ) : ℂ :=
  Function.Periodic.qParam width z

private theorem SpecialPeriods.Triangle.cuspQ_eq_exp (z : ℍ) :
    cuspQ z = Complex.exp (2 * Real.pi * Complex.I * z / width) :=
  rfl

private theorem SpecialPeriods.Triangle.cuspQ_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω cuspQ :=
  (Function.Periodic.contDiff_qParam (h := width) ω).contMDiff.comp UpperHalfPlane.contMDiff_coe

private theorem SpecialPeriods.Triangle.cuspQ_continuous : Continuous cuspQ :=
  cuspQ_holomorphic.continuous

private theorem SpecialPeriods.Triangle.cuspQ_ne_zero (z : ℍ) : cuspQ z ≠ 0 :=
  Function.Periodic.qParam_ne_zero z

private theorem SpecialPeriods.Triangle.cuspQ_hasStrictDerivAt (z : ℍ) :
    HasStrictDerivAt (cuspQ ∘ UpperHalfPlane.ofComplex)
      (cuspQ z * (2 * Real.pi * Complex.I / width)) (z : ℂ) := by
  have h :
    HasStrictDerivAt (Function.Periodic.qParam width)
      (cuspQ z * (2 * Real.pi * Complex.I / width)) (z : ℂ) := by
    simpa only [id_eq, mul_one] using!
      (((hasStrictDerivAt_id (z : ℂ)).const_mul (2 * Real.pi * Complex.I)).div_const
          (width : ℂ)).cexp
  apply h.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.im_pos] with w hw
  change
    Function.Periodic.qParam width w = Function.Periodic.qParam width (UpperHalfPlane.ofComplex w)
  exact congrArg (Function.Periodic.qParam width) hw.symm

private theorem SpecialPeriods.Triangle.cuspQ_deriv_ne_zero (z : ℍ) :
    deriv (cuspQ ∘ UpperHalfPlane.ofComplex) (z : ℂ) ≠ 0 := by
  rw [(cuspQ_hasStrictDerivAt z).hasDerivAt.deriv]
  exact
    mul_ne_zero (cuspQ_ne_zero z)
      (div_ne_zero Complex.two_pi_I_ne_zero width_coe_ne_zero_mo1973_16106)

private theorem SpecialPeriods.Triangle.cuspQ_norm_lt_one (z : ℍ) : ‖cuspQ z‖ < 1 :=
  Function.Periodic.norm_qParam_lt_one width_pos z.im_pos

private theorem SpecialPeriods.Triangle.cuspQ_norm_lt_exp_iff (A : ℝ) (z : ℍ) :
    ‖cuspQ z‖ < Real.exp (-2 * Real.pi * A / width) ↔ A < z.im :=
  Function.Periodic.norm_qParam_lt_iff width_pos A z

private theorem SpecialPeriods.Triangle.cuspQ_cusp_zpow (n : ℤ) (z : ℍ) :
    cuspQ
        (SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleCuspGenerator ^ n)
          z) =
      cuspQ z := by
  rw [cuspQ, SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_coe, cuspQ]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-n, ?_⟩
  push_cast
  rw [mul_div_assoc, sub_div, mul_div_cancel_right₀ _ width_coe_ne_zero_mo1973_16106]
  ring

private theorem SpecialPeriods.Triangle.cuspQ_eq_iff (z w : ℍ) :
    cuspQ z = cuspQ w ↔
      ∃ n : ℤ,
        SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleCuspGenerator ^ n)
            w =
          z := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := Function.Periodic.qParam_left_inv_mod_period width_ne_zero (z : ℂ)
    obtain ⟨n, hn⟩ := Function.Periodic.qParam_left_inv_mod_period width_ne_zero (w : ℂ)
    change Function.Periodic.invQParam width (cuspQ z) = (z : ℂ) + m * width at hm
    change Function.Periodic.invQParam width (cuspQ w) = (w : ℂ) + n * width at hn
    rw [h, hn] at hm
    refine ⟨m - n, ?_⟩
    apply UpperHalfPlane.ext
    rw [SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_coe]
    push_cast
    linear_combination hm
  · rintro ⟨n, rfl⟩
    exact cuspQ_cusp_zpow n w

private def SpecialPeriods.Triangle.puncturedDisc : TopologicalSpace.Opens ℂ :=
  ⟨{q : ℂ | q ≠ 0 ∧ ‖q‖ < 1},
    isOpen_compl_singleton.inter (isOpen_lt continuous_norm continuous_const)⟩

private abbrev SpecialPeriods.Triangle.PuncturedDisc :=
  puncturedDisc

private def SpecialPeriods.Triangle.cuspQMap (z : ℍ) : PuncturedDisc :=
  ⟨cuspQ z, cuspQ_ne_zero z, cuspQ_norm_lt_one z⟩

private theorem SpecialPeriods.Triangle.cuspQMap_surjective : Function.Surjective cuspQMap := by
  intro q
  refine
    ⟨⟨Function.Periodic.invQParam width q,
        Function.Periodic.im_invQParam_pos_of_norm_lt_one width_pos q.property.2 q.property.1⟩,
      ?_⟩
  apply Subtype.ext
  exact Function.Periodic.qParam_right_inv width_ne_zero q.property.1

private theorem SpecialPeriods.Triangle.qParam_width_isOpenMap_mo1973_16141 :
    IsOpenMap (Function.Periodic.qParam width) := by
  change IsOpenMap (Complex.exp ∘ (fun z : ℂ => 2 * Real.pi * Complex.I * z / width))
  apply Complex.isOpenMap_exp.comp
  have he :
    (fun z : ℂ => 2 * Real.pi * Complex.I * z / width) =
      (fun z : ℂ => (2 * Real.pi * Complex.I / width) * z) := by
    funext z
    ring
  rw [he]
  exact
    (Homeomorph.mulLeft₀ _
        (div_ne_zero Complex.two_pi_I_ne_zero width_coe_ne_zero_mo1973_16106)).isOpenMap

private theorem SpecialPeriods.Triangle.cuspQ_isOpenMap : IsOpenMap cuspQ :=
  qParam_width_isOpenMap_mo1973_16141.comp UpperHalfPlane.isOpenEmbedding_coe.isOpenMap

private theorem SpecialPeriods.Triangle.cuspQ_tendsto_atImInfty :
    Filter.Tendsto cuspQ UpperHalfPlane.atImInfty (𝓝[≠] (0 : ℂ)) :=
  (Function.Periodic.qParam_tendsto width_pos).comp UpperHalfPlane.tendsto_coe_atImInfty

private def SpecialPeriods.Triangle.cuspRadius (Y : ℝ) : ℝ :=
  Real.exp (-2 * Real.pi * Y / width)

@[simp]
private theorem SpecialPeriods.Triangle.cuspRadius_pos (Y : ℝ) : 0 < cuspRadius Y :=
  Real.exp_pos _

private theorem
    SpecialPeriods.Triangle.cuspRadius_le_one (Y : ℝ) (hY : 0 ≤ Y) : cuspRadius Y ≤ 1 := by
  rw [cuspRadius, Real.exp_le_one_iff]
  apply div_nonpos_of_nonpos_of_nonneg _ width_pos.le
  exact
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) Real.pi_pos.le)
      hY

private def SpecialPeriods.Triangle.puncturedCuspBall (Y : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨{q : ℂ | q ≠ 0 ∧ ‖q‖ < cuspRadius Y},
    isOpen_compl_singleton.inter (isOpen_lt continuous_norm continuous_const)⟩

@[simp]
private theorem SpecialPeriods.Triangle.mem_puncturedCuspBall (Y : ℝ) (q : ℂ) :
    q ∈ puncturedCuspBall Y ↔ q ≠ 0 ∧ ‖q‖ < cuspRadius Y :=
  Iff.rfl

private theorem SpecialPeriods.Triangle.cuspQ_mem_puncturedCuspBall_iff (Y : ℝ) (z : ℍ) :
    cuspQ z ∈ puncturedCuspBall Y ↔ z ∈ horodisc Y := by
  change (cuspQ z ≠ 0 ∧ ‖cuspQ z‖ < Real.exp (-2 * Real.pi * Y / width)) ↔ Y < z.im
  constructor
  · intro h
    exact (cuspQ_norm_lt_exp_iff Y z).mp h.2
  · intro h
    exact ⟨cuspQ_ne_zero z, (cuspQ_norm_lt_exp_iff Y z).mpr h⟩

private def SpecialPeriods.Triangle.cuspQHorodisc (Y : ℝ) (z : horodisc Y) : puncturedCuspBall Y :=
  ⟨cuspQ z, (cuspQ_mem_puncturedCuspBall_iff Y z).mpr z.property⟩

private theorem SpecialPeriods.Triangle.cuspQHorodisc_eq_iff (Y : ℝ) (z w : horodisc Y) :
    cuspQHorodisc Y z = cuspQHorodisc Y w ↔
      ∃ n : ℤ,
        SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleCuspGenerator ^ n)
            (w : ℍ) =
          (z : ℍ) :=
  Subtype.ext_iff.trans (cuspQ_eq_iff z w)

private theorem SpecialPeriods.Triangle.cuspQHorodisc_holomorphic (Y : ℝ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspQHorodisc Y) := by
  have h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : horodisc Y => cuspQ (z : ℍ)) :=
    cuspQ_holomorphic.comp contMDiff_subtype_val
  intro z
  have hi :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w : horodisc Y => (cuspQHorodisc Y w : ℂ)) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspQHorodisc Y) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact hi.mp (h z)

private theorem
    SpecialPeriods.Triangle.cuspQHorodisc_continuous (Y : ℝ) : Continuous (cuspQHorodisc Y) :=
  (cuspQHorodisc_holomorphic Y).continuous

private theorem
    SpecialPeriods.Triangle.cuspQHorodisc_isOpenMap (Y : ℝ) : IsOpenMap (cuspQHorodisc Y) := by
  apply (puncturedCuspBall Y).isOpen.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
  exact cuspQ_isOpenMap.comp (horodisc Y).isOpen.isOpenEmbedding_subtypeVal.isOpenMap

private theorem SpecialPeriods.Triangle.cuspQHorodisc_surjective (Y : ℝ) (hY : 0 ≤ Y) :
    Function.Surjective (cuspQHorodisc Y) := by
  intro q
  let q' : PuncturedDisc := ⟨q, q.property.1, q.property.2.trans_le (cuspRadius_le_one Y hY)⟩
  obtain ⟨z, hz⟩ := cuspQMap_surjective q'
  have hzq : cuspQ z = (q : ℂ) := congrArg Subtype.val hz
  have hzY : z ∈ horodisc Y := by
    apply (cuspQ_mem_puncturedCuspBall_iff Y z).mp
    rw [hzq]
    exact q.property
  refine ⟨⟨z, hzY⟩, ?_⟩
  exact Subtype.ext hzq

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private abbrev SpecialPeriods.Triangle.CuspHorodiscQuotient (Y : ℝ) :=
  LocalOrbitQuotient.LocalQuotient (Subgroup.zpowers SpecialPeriods.triangleCuspGenerator)
    (horodisc Y) (cusp_horodisc_invariant Y)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.cuspHorodiscProjection (Y : ℝ) :
    horodisc Y → CuspHorodiscQuotient Y :=
  LocalOrbitQuotient.localProjection _ _ _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.cuspHorodiscProjection_eq_iff (Y : ℝ) (z w : horodisc Y) :
    cuspHorodiscProjection Y z = cuspHorodiscProjection Y w ↔
      ∃ n : ℤ,
        SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleCuspGenerator ^ n)
            (w : ℍ) =
          (z : ℍ) := by
  rw [cuspHorodiscProjection, LocalOrbitQuotient.localProjection_eq_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
    refine ⟨n, ?_⟩
    rw [hn]
    exact hg
  · rintro ⟨n, hn⟩
    exact ⟨⟨SpecialPeriods.triangleCuspGenerator ^ n, Subgroup.zpow_mem_zpowers _ _⟩, hn⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.cuspHorodiscProjection_surjective (Y : ℝ) :
    Function.Surjective (cuspHorodiscProjection Y) :=
  LocalOrbitQuotient.localProjection_surjective _ _ _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.cuspHorodiscProjection_continuous (Y : ℝ) :
    Continuous (cuspHorodiscProjection Y) :=
  LocalOrbitQuotient.localProjection_continuous _ _ _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.cuspImageProjection (Y : ℝ) : horodisc Y → cuspImage Y :=
  LocalOrbitQuotient.imageProjection (G := SpecialPeriods.TriangleGroup) (horodisc Y)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.cuspImageProjection_surjective (Y : ℝ) :
    Function.Surjective (cuspImageProjection Y) :=
  LocalOrbitQuotient.imageProjection_surjective (horodisc Y)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.cuspHorodiscImageHomeomorph (Y : ℝ) (hY : width ≤ Y) :
    CuspHorodiscQuotient Y ≃ₜ cuspImage Y :=
  LocalOrbitQuotient.localHomeomorph (Subgroup.zpowers SpecialPeriods.triangleCuspGenerator)
    (horodisc Y) (cusp_horodisc_invariant Y) (triangle_horodisc_overlap_mem_cusp Y hY)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.cuspHorodiscImageHomeomorph_mk (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) :
    cuspHorodiscImageHomeomorph Y hY (cuspHorodiscProjection Y z) = cuspImageProjection Y z :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.cuspHorodiscImageHomeomorph_symm_mk (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) :
    (cuspHorodiscImageHomeomorph Y hY).symm (cuspImageProjection Y z) =
      cuspHorodiscProjection Y z :=
  (cuspHorodiscImageHomeomorph Y hY).symm_apply_apply (cuspHorodiscProjection Y z)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.cuspImageProjection_eq_iff (Y : ℝ) (hY : width ≤ Y)
    (z w : horodisc Y) :
    cuspImageProjection Y z = cuspImageProjection Y w ↔ cuspQ (z : ℍ) = cuspQ (w : ℍ) := by
  rw [← cuspHorodiscImageHomeomorph_mk Y hY z, ← cuspHorodiscImageHomeomorph_mk Y hY w,
    (cuspHorodiscImageHomeomorph Y hY).injective.eq_iff, cuspHorodiscProjection_eq_iff,
    cuspQ_eq_iff]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.cuspHorodiscToBall (Y : ℝ) :
    CuspHorodiscQuotient Y → puncturedCuspBall Y :=
  Quotient.lift (cuspQHorodisc Y) fun z w h =>
    (cuspQHorodisc_eq_iff Y z w).mpr ((cuspHorodiscProjection_eq_iff Y z w).mp (Quotient.sound h))

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.cuspHorodiscToBall_injective (Y : ℝ) :
    Function.Injective (cuspHorodiscToBall Y) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro z w h
  exact (cuspHorodiscProjection_eq_iff Y z w).mpr ((cuspQHorodisc_eq_iff Y z w).mp h)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.cuspHorodiscToBall_surjective (Y : ℝ) (hY : 0 ≤ Y) :
    Function.Surjective (cuspHorodiscToBall Y) := by
  intro q
  obtain ⟨z, rfl⟩ := cuspQHorodisc_surjective Y hY q
  exact ⟨cuspHorodiscProjection Y z, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.cuspHorodiscToBall_continuous (Y : ℝ) :
    Continuous (cuspHorodiscToBall Y) :=
  (cuspQHorodisc_continuous Y).quotient_lift _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.cuspHorodiscToBall_isOpenMap (Y : ℝ) :
    IsOpenMap (cuspHorodiscToBall Y) :=
  IsOpenMap.of_comp (cuspHorodiscProjection_continuous Y) (cuspHorodiscProjection_surjective Y)
    (cuspQHorodisc_isOpenMap Y)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.cuspHorodiscBallHomeomorph (Y : ℝ) (hY : 0 ≤ Y) :
    CuspHorodiscQuotient Y ≃ₜ puncturedCuspBall Y :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (cuspHorodiscToBall Y)
      ⟨cuspHorodiscToBall_injective Y, cuspHorodiscToBall_surjective Y hY⟩)
    (cuspHorodiscToBall_continuous Y) (cuspHorodiscToBall_isOpenMap Y)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.cuspImageHomeomorph (Y : ℝ) (hY : width ≤ Y) :
    cuspImage Y ≃ₜ puncturedCuspBall Y :=
  (cuspHorodiscImageHomeomorph Y hY).symm.trans
    (cuspHorodiscBallHomeomorph Y (width_pos.le.trans hY))

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem
    SpecialPeriods.Triangle.cuspImageHomeomorph_mk (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    cuspImageHomeomorph Y hY (cuspImageProjection Y z) = cuspQHorodisc Y z := by
  change
    cuspHorodiscToBall Y ((cuspHorodiscImageHomeomorph Y hY).symm (cuspImageProjection Y z)) = _
  rw [cuspHorodiscImageHomeomorph_symm_mk]
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.cuspImageHomeomorph_mk_coe (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) : (cuspImageHomeomorph Y hY (cuspImageProjection Y z) : ℂ) = cuspQ (z : ℍ) :=
  by
  rw [cuspImageHomeomorph_mk]
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.cuspImageHomeomorph_symm_q (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) :
    (cuspImageHomeomorph Y hY).symm (cuspQHorodisc Y z) = cuspImageProjection Y z := by
  rw [← cuspImageHomeomorph_mk Y hY z, Homeomorph.symm_apply_apply]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.cuspImageHomeomorph_norm_lt_iff (Y Z : ℝ) (hY : width ≤ Y)
    (hYZ : Y ≤ Z) (x : cuspImage Y) :
    ‖(cuspImageHomeomorph Y hY x : ℂ)‖ < cuspRadius Z ↔
      (x : SpecialPeriods.TriangleOrbitSpace) ∈ cuspImage Z := by
  obtain ⟨z, rfl⟩ := cuspImageProjection_surjective Y x
  rw [cuspImageHomeomorph_mk_coe]
  change
    ‖cuspQ (z : ℍ)‖ < Real.exp (-2 * Real.pi * Z / width) ↔
      ∃ w : ℍ,
        Z < w.im ∧
          SpecialPeriods.triangleOrbitProjection w =
            SpecialPeriods.triangleOrbitProjection (z : ℍ)
  rw [cuspQ_norm_lt_exp_iff]
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨w, hw, he⟩
    have hwY : w ∈ horodisc Y := hYZ.trans_lt hw
    have he' : cuspImageProjection Y ⟨w, hwY⟩ = cuspImageProjection Y z := Subtype.ext he
    have hq := (cuspImageProjection_eq_iff Y hY ⟨w, hwY⟩ z).mp he'
    have hnorm := (cuspQ_norm_lt_exp_iff Z w).mpr hw
    rw [hq] at hnorm
    exact (cuspQ_norm_lt_exp_iff Z (z : ℍ)).mp hnorm

private def SpecialPeriods.Triangle.boundedOrbitImage (R : ℝ) :
    TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace :=
  ⟨SpecialPeriods.triangleOrbitProjection '' {z : ℍ | orbitHeightBound z < R},
    SpecialPeriods.triangleOrbitProjection_isOpenMap _
      (isOpen_lt orbitHeightBound_continuous continuous_const)⟩

private theorem SpecialPeriods.Triangle.boundedOrbitImage_mono :
    Monotone (fun R : ℝ => (boundedOrbitImage R : Set SpecialPeriods.TriangleOrbitSpace)) := by
  intro R S hRS q hq
  obtain ⟨z, hz, rfl⟩ := hq
  exact ⟨z, hz.trans_le hRS, rfl⟩

private theorem SpecialPeriods.Triangle.boundedOrbitImage_subset_cuspImage_compl (R : ℝ) :
    (boundedOrbitImage R : Set SpecialPeriods.TriangleOrbitSpace) ⊆
      (cuspImage R : Set SpecialPeriods.TriangleOrbitSpace)ᶜ := by
  rintro q ⟨z, hz, rfl⟩ ⟨w, hw, he⟩
  obtain ⟨g, hg⟩ := (SpecialPeriods.triangleOrbitProjection_eq_iff w z).mp he
  have hb := triangle_im_le_orbitHeightBound g z
  rw [hg] at hb
  exact (not_lt_of_ge (le_trans hb hz.le)) hw

private theorem SpecialPeriods.Triangle.boundedOrbitImage_cover :
    (⋃ R : ℝ, (boundedOrbitImage R : Set SpecialPeriods.TriangleOrbitSpace)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨z, rfl⟩ := SpecialPeriods.triangleOrbitProjection_surjective q
  refine Set.mem_iUnion.mpr ⟨orbitHeightBound z + 1, z, ?_, rfl⟩
  change orbitHeightBound z < orbitHeightBound z + 1
  linarith

private theorem SpecialPeriods.Triangle.compact_subset_cuspImage_compl
    {K : Set SpecialPeriods.TriangleOrbitSpace} (hK : IsCompact K) :
    ∃ Y : ℝ, width ≤ Y ∧ K ⊆ (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace)ᶜ := by
  obtain ⟨R, hR⟩ :=
    hK.elim_directed_cover
      (fun R : ℝ => (boundedOrbitImage R : Set SpecialPeriods.TriangleOrbitSpace))
      (fun R => (boundedOrbitImage R).isOpen)
      (by rw [boundedOrbitImage_cover]; exact Set.subset_univ K)
      (fun R S =>
        ⟨Max.max R S, boundedOrbitImage_mono (le_max_left R S),
          boundedOrbitImage_mono (le_max_right R S)⟩)
  refine ⟨Max.max R width, le_max_right _ _, ?_⟩
  exact
    hR.trans
      ((boundedOrbitImage_mono (le_max_left R width)).trans
        (boundedOrbitImage_subset_cuspImage_compl (Max.max R width)))

private theorem SpecialPeriods.Triangle.cuspNeighborhood_basis :
    (𝓝 SpecialPeriods.triangleCuspPoint).HasBasis (fun Y : ℝ => width ≤ Y)
      (fun Y => (cuspNeighborhood Y : Set SpecialPeriods.TriangleCompactifiedOrbitSpace)) := by
  rw [Filter.hasBasis_iff]
  intro U
  constructor
  · intro hU
    obtain ⟨K, ⟨hKclosed, hKcompact⟩, hKU⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hU
    obtain ⟨Y, hY, hKY⟩ := compact_subset_cuspImage_compl hKcompact
    refine ⟨Y, hY, ?_⟩
    intro x hx
    induction x using OnePoint.rec
    · exact hKU (Or.inr rfl)
    · rename_i q
      have hq : q ∈ cuspImage Y := (openInclusion_mem_cuspNeighborhood Y q).mp hx
      exact hKU (Or.inl ⟨q, fun hqK => hKY hqK hq, rfl⟩)
  · rintro ⟨Y, _, hYU⟩
    exact Filter.mem_of_superset (cuspNeighborhood_mem_nhds Y) hYU

private instance
    SpecialPeriods.triangleOrbitSpace_noncompact : NoncompactSpace TriangleOrbitSpace where
  noncompact_univ := by
    intro hK
    obtain ⟨Y, _, hY⟩ := Triangle.compact_subset_cuspImage_compl hK
    obtain ⟨z, hz⟩ := Triangle.horodisc_nonempty Y
    exact hY (Set.mem_univ (triangleOrbitProjection z)) ⟨z, hz, rfl⟩

private theorem SpecialPeriods.triangleCompactifiedOrbitSpace_connected :
    ConnectedSpace TriangleCompactifiedOrbitSpace :=
  inferInstance

private theorem SpecialPeriods.Triangle.cuspRadius_tendsto_zero :
    Filter.Tendsto cuspRadius Filter.atTop (𝓝 0) := by
  have hneg : -2 * Real.pi < 0 := by nlinarith [Real.pi_pos]
  exact
    Real.tendsto_exp_atBot.comp
      ((Filter.tendsto_id.const_mul_atTop_of_neg hneg).atBot_div_const width_pos)

private theorem SpecialPeriods.Triangle.exists_high_cuspRadius_lt (Y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Z : ℝ, Y ≤ Z ∧ width ≤ Z ∧ cuspRadius Z < ε := by
  have hsmall : ∀ᶠ Z in Filter.atTop, cuspRadius Z < ε :=
    cuspRadius_tendsto_zero.eventually (gt_mem_nhds hε)
  obtain ⟨Z, hZ⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨Max.max Y (Max.max width Z), le_max_left _ _, ?_, hZ _ ?_⟩
  · exact (le_max_left width Z).trans (le_max_right Y _)
  · exact (le_max_right width Z).trans (le_max_right Y _)

private def SpecialPeriods.Triangle.cuspFullForward (Y : ℝ) (hY : width ≤ Y) :
    SpecialPeriods.TriangleCompactifiedOrbitSpace → ℂ := by
  classical
    exact
    OnePoint.rec 0
      (fun q : SpecialPeriods.TriangleOrbitSpace =>
        if hq : q ∈ cuspImage Y then (cuspImageHomeomorph Y hY ⟨q, hq⟩ : ℂ) else 0)

@[simp]
private theorem SpecialPeriods.Triangle.cuspFullForward_cuspPoint (Y : ℝ) (hY : width ≤ Y) :
    cuspFullForward Y hY SpecialPeriods.triangleCuspPoint = 0 :=
  rfl

private theorem SpecialPeriods.Triangle.cuspFullForward_openInclusion (Y : ℝ) (hY : width ≤ Y)
    (q : SpecialPeriods.TriangleOrbitSpace) (hq : q ∈ cuspImage Y) :
    cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q) =
      (cuspImageHomeomorph Y hY ⟨q, hq⟩ : ℂ) := by
  classical
  change (if h : q ∈ cuspImage Y then (cuspImageHomeomorph Y hY ⟨q, h⟩ : ℂ) else 0) = _
  rw [dite_eq_left hq]

private def SpecialPeriods.Triangle.cuspFullInverse (Y : ℝ) (hY : width ≤ Y) :
    ℂ → SpecialPeriods.TriangleCompactifiedOrbitSpace := by
  classical
    exact fun z =>
    if hz : z ∈ puncturedCuspBall Y then
      SpecialPeriods.triangleOpenInclusion
        ((cuspImageHomeomorph Y hY).symm ⟨z, hz⟩ : SpecialPeriods.TriangleOrbitSpace)
    else SpecialPeriods.triangleCuspPoint

@[simp]
private theorem SpecialPeriods.Triangle.cuspFullInverse_zero (Y : ℝ) (hY : width ≤ Y) :
    cuspFullInverse Y hY 0 = SpecialPeriods.triangleCuspPoint := by
  classical simp [cuspFullInverse]

private theorem SpecialPeriods.Triangle.cuspFullInverse_of_mem (Y : ℝ) (hY : width ≤ Y) (z : ℂ)
    (hz : z ∈ puncturedCuspBall Y) :
    cuspFullInverse Y hY z =
      SpecialPeriods.triangleOpenInclusion
        ((cuspImageHomeomorph Y hY).symm ⟨z, hz⟩ : SpecialPeriods.TriangleOrbitSpace) := by
  classical simp [cuspFullInverse, hz]

private theorem SpecialPeriods.Triangle.cuspFullInverse_of_not_mem (Y : ℝ) (hY : width ≤ Y) (z : ℂ)
    (hz : z ∉ puncturedCuspBall Y) : cuspFullInverse Y hY z = SpecialPeriods.triangleCuspPoint := by
  classical simp [cuspFullInverse, hz]

private theorem SpecialPeriods.Triangle.cuspFullForward_continuousAt_openInclusion (Y : ℝ)
    (hY : width ≤ Y) (q : SpecialPeriods.TriangleOrbitSpace) (hq : q ∈ cuspImage Y) :
    ContinuousAt (cuspFullForward Y hY) (SpecialPeriods.triangleOpenInclusion q) := by
  apply OnePoint.continuousAt_coe.mpr
  have hc :
    ContinuousOn
      (fun q : SpecialPeriods.TriangleOrbitSpace =>
        cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q))
      (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change
      Continuous
        (fun q : cuspImage Y => cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q))
    have he :
      (fun q : cuspImage Y => cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q)) =
        (fun q : cuspImage Y => (cuspImageHomeomorph Y hY q : ℂ)) := by
      funext q
      exact cuspFullForward_openInclusion Y hY q q.property
    rw [he]
    exact continuous_subtype_val.comp (cuspImageHomeomorph Y hY).continuous
  exact hc.continuousAt ((cuspImage Y).isOpen.mem_nhds hq)

private theorem
    SpecialPeriods.Triangle.cuspFullForward_continuousAt_cuspPoint (Y : ℝ) (hY : width ≤ Y) :
    ContinuousAt (cuspFullForward Y hY) SpecialPeriods.triangleCuspPoint := by
  change Filter.Tendsto (cuspFullForward Y hY) (𝓝 SpecialPeriods.triangleCuspPoint) (𝓝 (0 : ℂ))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨Z, hYZ, _, hZε⟩ := exists_high_cuspRadius_lt Y hε
  filter_upwards [cuspNeighborhood_mem_nhds Z] with x hx
  induction x using OnePoint.rec
  · change Dist.dist (0 : ℂ) 0 < ε
    simpa only [dist_self] using hε
  · rename_i q
    have hqZ : q ∈ cuspImage Z := (openInclusion_mem_cuspNeighborhood Z q).mp hx
    have hqY : q ∈ cuspImage Y := cuspImage_antitone hYZ hqZ
    have hn := (cuspImageHomeomorph_norm_lt_iff Y Z hY hYZ ⟨q, hqY⟩).mpr hqZ
    change Dist.dist (cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q)) 0 < ε
    rw [cuspFullForward_openInclusion Y hY q hqY, dist_zero_right]
    exact hn.trans hZε

private theorem SpecialPeriods.Triangle.cuspFullForward_continuousOn (Y : ℝ) (hY : width ≤ Y) :
    ContinuousOn (cuspFullForward Y hY)
      (cuspNeighborhood Y : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  intro x hx
  induction x using OnePoint.rec
  · exact (cuspFullForward_continuousAt_cuspPoint Y hY).continuousWithinAt
  · rename_i q
    exact
      (cuspFullForward_continuousAt_openInclusion Y hY q
          ((openInclusion_mem_cuspNeighborhood Y q).mp hx)).continuousWithinAt

private theorem SpecialPeriods.Triangle.cuspFullInverse_continuousAt_of_mem (Y : ℝ) (hY : width ≤ Y)
    (z : ℂ) (hz : z ∈ puncturedCuspBall Y) : ContinuousAt (cuspFullInverse Y hY) z := by
  have hc : ContinuousOn (cuspFullInverse Y hY) (puncturedCuspBall Y : Set ℂ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun z : puncturedCuspBall Y => cuspFullInverse Y hY z)
    have he :
      (fun z : puncturedCuspBall Y => cuspFullInverse Y hY z) =
        (fun z : puncturedCuspBall Y =>
          SpecialPeriods.triangleOpenInclusion
            ((cuspImageHomeomorph Y hY).symm z : SpecialPeriods.TriangleOrbitSpace)) := by
      funext z
      exact cuspFullInverse_of_mem Y hY z z.property
    rw [he]
    exact
      SpecialPeriods.triangleOpenInclusion_isOpenEmbedding.continuous.comp
        (continuous_subtype_val.comp (cuspImageHomeomorph Y hY).symm.continuous)
  exact hc.continuousAt ((puncturedCuspBall Y).isOpen.mem_nhds hz)

private theorem SpecialPeriods.Triangle.cuspFullInverse_continuousAt_zero (Y : ℝ) (hY : width ≤ Y) :
    ContinuousAt (cuspFullInverse Y hY) 0 := by
  classical
  change Filter.Tendsto (cuspFullInverse Y hY) (𝓝 (0 : ℂ)) (𝓝 (cuspFullInverse Y hY 0))
  rw [cuspFullInverse_zero, cuspNeighborhood_basis.tendsto_right_iff]
  intro Z _
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (cuspRadius_pos (Max.max Y Z))] with z hz
  by_cases hp : z ∈ puncturedCuspBall Y
  · rw [cuspFullInverse_of_mem Y hY z hp]
    apply (openInclusion_mem_cuspNeighborhood Z _).mpr
    apply cuspImage_antitone (le_max_right Y Z)
    apply
      (cuspImageHomeomorph_norm_lt_iff Y (Max.max Y Z) hY (le_max_left Y Z)
          ((cuspImageHomeomorph Y hY).symm ⟨z, hp⟩)).mp
    simpa using hz
  · rw [cuspFullInverse_of_not_mem Y hY z hp]
    exact cuspPoint_mem_cuspNeighborhood Z

private theorem SpecialPeriods.Triangle.cuspFullInverse_continuousOn (Y : ℝ) (hY : width ≤ Y) :
    ContinuousOn (cuspFullInverse Y hY) (Metric.ball (0 : ℂ) (cuspRadius Y)) := by
  classical
  intro z hz
  by_cases h0 : z = 0
  · subst z
    exact (cuspFullInverse_continuousAt_zero Y hY).continuousWithinAt
  · exact (cuspFullInverse_continuousAt_of_mem Y hY z ⟨h0, by simpa using hz⟩).continuousWithinAt

private def SpecialPeriods.Triangle.cuspFullChart (Y : ℝ) (hY : width ≤ Y) :
    OpenPartialHomeomorph SpecialPeriods.TriangleCompactifiedOrbitSpace ℂ := by
  classical
    exact
    { toFun := cuspFullForward Y hY
      invFun := cuspFullInverse Y hY
      source := cuspNeighborhood Y
      target := Metric.ball 0 (cuspRadius Y)
      map_source' := by
        intro x hx
        induction x using OnePoint.rec
        · change (0 : ℂ) ∈ Metric.ball 0 (cuspRadius Y)
          simpa only [Metric.mem_ball, dist_self] using cuspRadius_pos Y
        · rename_i q
          have hq : q ∈ cuspImage Y := (openInclusion_mem_cuspNeighborhood Y q).mp hx
          change
            cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q) ∈
              Metric.ball 0 (cuspRadius Y)
          rw [cuspFullForward_openInclusion Y hY q hq]
          simpa using (cuspImageHomeomorph Y hY ⟨q, hq⟩).property.2
      map_target' := by
        intro z _
        by_cases hz : z ∈ puncturedCuspBall Y
        · rw [cuspFullInverse_of_mem Y hY z hz]
          exact
            (openInclusion_mem_cuspNeighborhood Y _).mpr
              ((cuspImageHomeomorph Y hY).symm ⟨z, hz⟩).property
        · rw [cuspFullInverse_of_not_mem Y hY z hz]
          exact cuspPoint_mem_cuspNeighborhood Y
      left_inv' := by
        intro x hx
        induction x using OnePoint.rec
        · exact cuspFullInverse_zero Y hY
        · rename_i q
          have hq : q ∈ cuspImage Y := (openInclusion_mem_cuspNeighborhood Y q).mp hx
          change
            cuspFullInverse Y hY (cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q)) =
              SpecialPeriods.triangleOpenInclusion q
          rw [cuspFullForward_openInclusion Y hY q hq]
          rw [cuspFullInverse_of_mem Y hY _ (cuspImageHomeomorph Y hY ⟨q, hq⟩).property]
          change
            SpecialPeriods.triangleOpenInclusion
                ((cuspImageHomeomorph Y hY).symm (cuspImageHomeomorph Y hY ⟨q, hq⟩)) =
              _
          rw [Homeomorph.symm_apply_apply]
      right_inv' := by
        intro z hz
        by_cases h0 : z = 0
        · subst z
          rw [cuspFullInverse_zero, cuspFullForward_cuspPoint]
        · have hp : z ∈ puncturedCuspBall Y := ⟨h0, by simpa using hz⟩
          rw [cuspFullInverse_of_mem Y hY z hp]
          rw [cuspFullForward_openInclusion Y hY _
              ((cuspImageHomeomorph Y hY).symm ⟨z, hp⟩).property]
          exact congrArg Subtype.val ((cuspImageHomeomorph Y hY).apply_symm_apply ⟨z, hp⟩)
      open_source := (cuspNeighborhood Y).isOpen
      open_target := Metric.isOpen_ball
      continuousOn_toFun := cuspFullForward_continuousOn Y hY
      continuousOn_invFun := cuspFullInverse_continuousOn Y hY }

@[simp]
private theorem SpecialPeriods.Triangle.cuspFullChart_source (Y : ℝ) (hY : width ≤ Y) :
    (cuspFullChart Y hY).source =
      (cuspNeighborhood Y : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.cuspFullChart_target (Y : ℝ) (hY : width ≤ Y) :
    (cuspFullChart Y hY).target = Metric.ball 0 (cuspRadius Y) :=
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.cuspFullChart_cuspPoint (Y : ℝ) (hY : width ≤ Y) :
    cuspFullChart Y hY SpecialPeriods.triangleCuspPoint = 0 :=
  rfl

@[simp]
private theorem SpecialPeriods.Triangle.cuspFullChart_symm_zero (Y : ℝ) (hY : width ≤ Y) :
    (cuspFullChart Y hY).symm 0 = SpecialPeriods.triangleCuspPoint :=
  cuspFullInverse_zero Y hY

private theorem SpecialPeriods.Triangle.cuspFullChart_openInclusion (Y : ℝ) (hY : width ≤ Y)
    (q : SpecialPeriods.TriangleOrbitSpace) (hq : q ∈ cuspImage Y) :
    cuspFullChart Y hY (SpecialPeriods.triangleOpenInclusion q) =
      (cuspImageHomeomorph Y hY ⟨q, hq⟩ : ℂ) :=
  cuspFullForward_openInclusion Y hY q hq

private theorem SpecialPeriods.Triangle.cuspFullChart_mk (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    cuspFullChart Y hY
        (SpecialPeriods.triangleOpenInclusion
          (SpecialPeriods.triangleOrbitProjection (z : UpperHalfPlane))) =
      cuspQ (z : UpperHalfPlane) := by
  change cuspFullChart Y hY (SpecialPeriods.triangleOpenInclusion (cuspImageProjection Y z)) = _
  rw [cuspFullChart_openInclusion Y hY _ (cuspImageProjection Y z).property]
  exact cuspImageHomeomorph_mk_coe Y hY z

private theorem SpecialPeriods.cyclic_eq_positive_generator_pow_mo1973_16242 {n : ℕ} [NeZero n]
    (a : Multiplicative (ZMod n)) (ha : a ≠ 1) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ a = Multiplicative.ofAdd (1 : ZMod n) ^ k := by
  refine ⟨a.toAdd.val, ZMod.val_pos.mpr ?_, ZMod.val_lt _, ?_⟩
  · exact ha
  · change a.toAdd = a.toAdd.val • (1 : ZMod n)
    simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

private theorem SpecialPeriods.triangle_nontrivial_isOfFinOrder_conjugate_generator_power
    (g : TriangleGroup) (hg : IsOfFinOrder g) (hne : g ≠ 1) :
    (∃ n : ℕ, 0 < n ∧ n < 3 ∧ IsConj (triangleGenerator₁ ^ n) g) ∨
      ∃ n : ℕ, 0 < n ∧ n < 4 ∧ IsConj (triangleGenerator₂ ^ n) g := by
  obtain ⟨a, hane, ha⟩ | ⟨a, hane, ha⟩ :=
    CoprodTorsion.coprod_nontrivial_isOfFinOrder_conjugate_factor g hg hne
  · obtain ⟨n, hn0, hn3, rfl⟩ := cyclic_eq_positive_generator_pow_mo1973_16242 a hane
    exact Or.inl ⟨n, hn0, hn3, by simpa only [map_pow, triangleGenerator₁] using ha⟩
  · obtain ⟨n, hn0, hn4, rfl⟩ := cyclic_eq_positive_generator_pow_mo1973_16242 a hane
    exact Or.inr ⟨n, hn0, hn4, by simpa only [map_pow, triangleGenerator₂] using ha⟩

private theorem SpecialPeriods.triangle_nontrivial_isOfFinOrder_eq_conjugate_generator_power
    (g : TriangleGroup) (hg : IsOfFinOrder g) (hne : g ≠ 1) :
    (∃ (h : TriangleGroup) (n : ℕ), 0 < n ∧ n < 3 ∧ g = h * triangleGenerator₁ ^ n * h⁻¹) ∨
      (∃ (h : TriangleGroup) (n : ℕ), 0 < n ∧ n < 4 ∧ g = h * triangleGenerator₂ ^ n * h⁻¹) := by
  obtain ⟨n, hn0, hn3, hn⟩ | ⟨n, hn0, hn4, hn⟩ :=
    triangle_nontrivial_isOfFinOrder_conjugate_generator_power g hg hne
  · obtain ⟨h, hh⟩ := isConj_iff.mp hn
    exact Or.inl ⟨h, n, hn0, hn3, hh.symm⟩
  · obtain ⟨h, hh⟩ := isConj_iff.mp hn
    exact Or.inr ⟨h, n, hn0, hn4, hh.symm⟩

private def SpecialPeriods.rhoPoint : ℍ :=
  ⟨rho, rho_im_pos⟩

@[simp]
private theorem SpecialPeriods.coe_rhoPoint : (rhoPoint : ℂ) = rho :=
  rfl

private theorem SpecialPeriods.rho_ne_zero : rho ≠ 0 :=
  rhoPoint.ne_zero

private theorem SpecialPeriods.rho_fourth : rho ^ 4 = -rho := by
  calc
    rho ^ 4 = rho ^ 3 * rho := by ring
    _ = -rho := by rw [rho_cube]; ring

private theorem SpecialPeriods.rho_fourth_ne_one : rho ^ 4 ≠ 1 := by
  intro h
  have hr : rho = -1 := neg_eq_iff_eq_neg.mp (rho_fourth.symm.trans h)
  have := rho_im_pos
  simp [hr] at this

private theorem SpecialPeriods.TS_smul_rhoPoint :
    (ModularGroup.T * ModularGroup.S) • rhoPoint = rhoPoint := by
  rw [SemigroupAction.mul_smul, UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_S_smul]
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_vadd, Complex.ofReal_one, coe_rhoPoint, inv_neg]
  field_simp [rho_ne_zero]
  linear_combination -rho_sq

private theorem SpecialPeriods.S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  rw [UpperHalfPlane.modular_S_smul]
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_I, inv_neg, Complex.inv_I, neg_neg]

private theorem
    SpecialPeriods.levelOne_transform {k : ℤ} (f : ModularForm 𝒮ℒ k) (g : SL(2, ℤ)) (z : ℍ) :
    f (g • z) = (UpperHalfPlane.denom g z) ^ k * f z :=
  SlashInvariantForm.slash_action_eqn'' f (show (g : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨g, rfl⟩) z

private theorem SpecialPeriods.E₄_rhoPoint : ModularForm.E₄ rhoPoint = 0 := by
  have h := levelOne_transform ModularForm.E₄ (ModularGroup.T * ModularGroup.S) rhoPoint
  rw [TS_smul_rhoPoint] at h
  have hd : UpperHalfPlane.denom (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) rhoPoint = rho := by
    have h10 : (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 0 = 1 := by decide
    have h11 : (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 1 = 0 := by decide
    rw [ModularGroup.denom_apply, h10, h11]
    simp
  rw [hd, zpow_ofNat] at h
  exact
    (mul_eq_zero.mp
          (show (rho ^ 4 - 1) * ModularForm.E₄ rhoPoint = 0 by
            linear_combination -h)).resolve_left
      (sub_ne_zero.mpr rho_fourth_ne_one)

private theorem SpecialPeriods.E₆_I : ModularForm.E₆ UpperHalfPlane.I = 0 := by
  have h := levelOne_transform ModularForm.E₆ ModularGroup.S UpperHalfPlane.I
  rw [S_smul_I, ModularGroup.denom_S, UpperHalfPlane.coe_I, zpow_ofNat] at h
  have hi : Complex.I ^ 6 = -1 := by norm_num [Complex.I_sq, pow_succ]
  rw [hi] at h
  linear_combination h / 2

private theorem SpecialPeriods.E₄_E₆_not_both_zero (z : ℍ) :
    ModularForm.E₄ z ≠ 0 ∨ ModularForm.E₆ z ≠ 0 := by
  by_contra! h
  have hd := ModularForm.discriminant_ne_zero z
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, h.1, h.2] at hd
  norm_num at hd

private theorem SpecialPeriods.E₆_rhoPoint_ne_zero : ModularForm.E₆ rhoPoint ≠ 0 := by
  simpa only [E₄_rhoPoint, ne_self_iff_false, false_or] using E₄_E₆_not_both_zero rhoPoint

private theorem SpecialPeriods.E₄_I_ne_zero : ModularForm.E₄ UpperHalfPlane.I ≠ 0 := by
  simpa only [E₆_I, ne_self_iff_false, or_false] using E₄_E₆_not_both_zero UpperHalfPlane.I

private theorem SpecialPeriods.levelOne_eq_of_qExpansion_coeff_zero {k : ℤ} (hk : k < 12)
    (f g : ModularForm 𝒮ℒ k)
    (hfg : (UpperHalfPlane.qExpansion 1 f).coeff 0 = (UpperHalfPlane.qExpansion 1 g).coeff 0) :
    f = g := by
  have hq : (UpperHalfPlane.qExpansion 1 (f - g)).coeff 0 = 0 := by
    rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, map_sub, hfg, sub_self]
  have hzero : ModularForm.toCuspForm (f - g) hq = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve hk) _
  ext z
  have hz := congrArg (fun F : CuspForm 𝒮ℒ k => F z) hzero
  exact sub_eq_zero.mp hz

private theorem SpecialPeriods.modularForm_analyticAt {k : ℤ} (f : ModularForm 𝒮ℒ k) (z : ℍ) :
    AnalyticAt ℂ (f ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp f.holo').analyticOnNhd
    UpperHalfPlane.isOpen_upperHalfPlaneSet _ z.im_pos

private def SpecialPeriods.modularJ (z : ℍ) : ℂ :=
  ModularForm.E₄ z ^ 3 / ModularForm.discriminant z

private theorem SpecialPeriods.modularJ_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) modularJ :=
  (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo' ModularForm.discriminant_ne_zero

private theorem SpecialPeriods.modularJ_analyticAt (z : ℍ) :
    AnalyticAt ℂ (modularJ ∘ UpperHalfPlane.ofComplex) z :=
  (UpperHalfPlane.mdifferentiable_iff.mp modularJ_mdifferentiable).analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

private theorem SpecialPeriods.modularJ_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω modularJ := by
  intro z
  exact UpperHalfPlane.contMDiffAt_iff.mpr (modularJ_analyticAt z).contDiffAt

private theorem SpecialPeriods.modularJ_continuous : Continuous modularJ :=
  modularJ_holomorphic.continuous

private theorem SpecialPeriods.modularJ_invariant (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) (z : ℍ) :
    modularJ (γ • z) = modularJ z := by
  have h₄ := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hγ z
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ z
  change
    ModularForm.discriminant (γ • z) =
      UpperHalfPlane.denom γ z ^ (12 : ℤ) * ModularForm.discriminant z at hΔ
  simp only [modularJ, h₄, hΔ, zpow_ofNat, mul_pow, ← pow_mul]
  norm_num
  exact mul_div_mul_left _ _ (pow_ne_zero 12 (UpperHalfPlane.denom_ne_zero γ z))

private theorem SpecialPeriods.modularJ_SL_invariant (γ : SL(2, ℤ)) (z : ℍ) :
    modularJ (γ • z) = modularJ z :=
  modularJ_invariant γ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) z

private theorem SpecialPeriods.modularJ_sub_1728 (z : ℍ) :
    modularJ z - 1728 = ModularForm.E₆ z ^ 2 / ModularForm.discriminant z := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  rw [eq_div_iff (by norm_num : (1728 : ℂ) ≠ 0)] at h
  unfold modularJ
  field_simp [ModularForm.discriminant_ne_zero z]
  linear_combination -h

private theorem
    SpecialPeriods.modularJ_eq_zero_iff (z : ℍ) : modularJ z = 0 ↔ ModularForm.E₄ z = 0 := by
  simp [modularJ, ModularForm.discriminant_ne_zero]

private theorem
    SpecialPeriods.modularJ_eq_1728_iff (z : ℍ) : modularJ z = 1728 ↔ ModularForm.E₆ z = 0 := by
  rw [← sub_eq_zero, modularJ_sub_1728]
  simp [ModularForm.discriminant_ne_zero]

@[simp]
private theorem SpecialPeriods.modularJ_rhoPoint : modularJ rhoPoint = 0 :=
  (modularJ_eq_zero_iff rhoPoint).mpr E₄_rhoPoint

@[simp]
private theorem SpecialPeriods.modularJ_I : modularJ UpperHalfPlane.I = 1728 :=
  (modularJ_eq_1728_iff UpperHalfPlane.I).mpr E₆_I

private def SpecialPeriods.discriminantUnit (q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24

@[simp]
private theorem SpecialPeriods.discriminantUnit_zero : discriminantUnit 0 = 1 := by
  simp [discriminantUnit]

private theorem SpecialPeriods.discriminantUnit_differentiableOn :
    DifferentiableOn ℂ discriminantUnit (Metric.ball 0 1) :=
  ModularForm.differentiableOn_tprod_one_sub_pow_pow 24

private theorem SpecialPeriods.discriminantUnit_analyticAt_zero : AnalyticAt ℂ discriminantUnit 0 :=
  discriminantUnit_differentiableOn.analyticAt (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

private def SpecialPeriods.modularJUnit (q : ℂ) : ℂ :=
  UpperHalfPlane.cuspFunction 1 ModularForm.E₄ q ^ 3 / discriminantUnit q

private theorem SpecialPeriods.E₄_cuspFunction_zero :
    UpperHalfPlane.cuspFunction 1 ModularForm.E₄ 0 = 1 := by
  have h :=
    EisensteinSeries.E_qExpansion_coeff_zero (show 3 ≤ 4 by decide) (show Even 4 by decide)
  simpa [UpperHalfPlane.qExpansion_coeff] using h

@[simp]
private theorem SpecialPeriods.modularJUnit_zero : modularJUnit 0 = 1 := by
  simp [modularJUnit, E₄_cuspFunction_zero]

private theorem SpecialPeriods.modularJUnit_analyticAt_zero : AnalyticAt ℂ modularJUnit 0 :=
  ((ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ zero_lt_one
            one_mem_strictPeriods_SL).pow
        3).div
    discriminantUnit_analyticAt_zero (by simp)

private theorem SpecialPeriods.modularJ_eq_unit_div_q (z : ℍ) :
    modularJ z = modularJUnit (Function.Periodic.qParam 1 z) / Function.Periodic.qParam 1 z := by
  have hE :=
    SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ z one_mem_strictPeriods_SL one_ne_zero
  have hΔ := ModularForm.discriminant_eq_q_prod z
  change
    ModularForm.discriminant z =
      Function.Periodic.qParam 1 z * discriminantUnit (Function.Periodic.qParam 1 z) at hΔ
  rw [modularJ, hΔ, modularJUnit, hE]
  rw [div_div, mul_comm]

private def SpecialPeriods.modularJInQ (q : ℂ) : ℂ :=
  modularJUnit q / q

private theorem SpecialPeriods.modularJInQ_qParam (z : ℍ) :
    modularJInQ (Function.Periodic.qParam 1 z) = modularJ z :=
  (modularJ_eq_unit_div_q z).symm

private theorem SpecialPeriods.modularJInQ_order : meromorphicOrderAt modularJInQ 0 = (-1 : ℤ) := by
  have hu : meromorphicOrderAt modularJUnit 0 = 0 := by
    rw [modularJUnit_analyticAt_zero.meromorphicOrderAt_eq,
      (modularJUnit_analyticAt_zero.analyticOrderAt_eq_zero.mpr (by simp))]
    rfl
  change meromorphicOrderAt (modularJUnit / id) 0 = _
  rw [meromorphicOrderAt_div modularJUnit_analyticAt_zero.meromorphicAt
      analyticAt_id.meromorphicAt,
    hu, meromorphicOrderAt_id]
  norm_num

private theorem SpecialPeriods.q_mul_modularJ_tendsto :
    Filter.Tendsto (fun z : ℍ => Function.Periodic.qParam 1 z * modularJ z)
      UpperHalfPlane.atImInfty (𝓝 1) := by
  have h :=
    modularJUnit_analyticAt_zero.continuousAt.tendsto.comp
      (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one)
  simp only [modularJUnit_zero, Function.comp_def] at h
  apply h.congr
  intro z
  rw [modularJ_eq_unit_div_q]
  exact (mul_div_cancel₀ _ (Function.Periodic.qParam_ne_zero z)).symm

private theorem SpecialPeriods.norm_modularJ_tendsto :
    Filter.Tendsto (fun z : ℍ => ‖modularJ z‖) UpperHalfPlane.atImInfty Filter.atTop := by
  have hq :
    Filter.Tendsto (fun z : ℍ => Function.Periodic.qParam 1 z) UpperHalfPlane.atImInfty
      (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one, ?_⟩
    exact Filter.Eventually.of_forall (fun z => Function.Periodic.qParam_ne_zero z)
  have hj : Filter.Tendsto modularJInQ (𝓝[≠] (0 : ℂ)) (Bornology.cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg
      (by
        rw [modularJInQ_order]
        exact_mod_cast (show (-1 : ℤ) < 0 by norm_num))
  have h := (tendsto_norm_atTop_iff_cobounded.mpr hj).comp hq
  simpa only [Function.comp_def, modularJInQ_qParam] using h

private theorem SpecialPeriods.modularJ_not_constant : ¬∃ c : ℂ, ∀ z : ℍ, modularJ z = c := by
  rintro ⟨c, hc⟩
  have h :
    Filter.Tendsto (fun z : ℍ => Function.Periodic.qParam 1 z * c) UpperHalfPlane.atImInfty
      (𝓝 0) := by simpa using (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one).mul_const c
  have h' :
    Filter.Tendsto (fun z : ℍ => Function.Periodic.qParam 1 z * c) UpperHalfPlane.atImInfty
      (𝓝 1) := by simpa only [hc] using q_mul_modularJ_tendsto
  exact zero_ne_one (tendsto_nhds_unique h h')

private theorem SpecialPeriods.inv_modularJ_sub_tendsto (c : ℂ) :
    Filter.Tendsto (fun z : ℍ => (modularJ z - c)⁻¹) UpperHalfPlane.atImInfty (𝓝 0) := by
  exact
    Filter.tendsto_inv₀_cobounded.comp
      ((tendsto_sub_const_cobounded c).comp
        (tendsto_norm_atTop_iff_cobounded.mp norm_modularJ_tendsto))

private theorem SpecialPeriods.inv_modularJ_sub_slash_mo1973_16294 (c : ℂ) (γ : SL(2, ℤ)) :
    (fun z : ℍ => (modularJ z - c)⁻¹) ∣[(0 : ℤ)] γ = fun z : ℍ => (modularJ z - c)⁻¹ := by
  funext z
  simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
  exact congrArg (fun w : ℂ => (w - c)⁻¹) (modularJ_SL_invariant γ z)

private def SpecialPeriods.omittedValueModularForm_mo1973_16295 (c : ℂ)
    (hc : ∀ z : ℍ, modularJ z ≠ c) : ModularForm 𝒮ℒ 0
    where
  toFun z := (modularJ z - c)⁻¹
  slash_action_eq' := by
    rintro γ ⟨γ', rfl⟩
    exact inv_modularJ_sub_slash_mo1973_16294 c γ'
  holo' :=
    (modularJ_mdifferentiable.sub mdifferentiable_const).inv (fun z => sub_ne_zero.mpr (hc z))
  bdd_at_cusps' {s}
    hs := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hs]
    intro γ _
    rw [inv_modularJ_sub_slash_mo1973_16294]
    exact Filter.ZeroAtFilter.boundedAtFilter (inv_modularJ_sub_tendsto c)

private theorem SpecialPeriods.modularJ_surjective : Function.Surjective modularJ := by
  intro c
  by_contra h
  have hc : ∀ z : ℍ, modularJ z ≠ c := fun z hz => h ⟨z, hz⟩
  let f := omittedValueModularForm_mo1973_16295 c hc
  obtain ⟨a, ha⟩ := ModularFormClass.levelOne_weight_zero_const f
  have hlim : Filter.Tendsto (fun _ : ℍ => a) UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
    change Filter.Tendsto (Function.const ℍ a) UpperHalfPlane.atImInfty (𝓝 (0 : ℂ))
    rw [← ha]
    exact inv_modularJ_sub_tendsto c
  have ha₀ : a = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  have hz : (modularJ UpperHalfPlane.I - c)⁻¹ = 0 := by
    have he := congr_fun ha UpperHalfPlane.I
    change (modularJ UpperHalfPlane.I - c)⁻¹ = a at he
    exact he.trans ha₀
  exact inv_ne_zero (sub_ne_zero.mpr (hc UpperHalfPlane.I)) hz

private theorem
    SpecialPeriods.modularJ_eventually_ne (c : ℂ) (z : ℍ) : ∀ᶠ w in 𝓝[≠] z, modularJ w ≠ c := by
  by_contra h
  have hfreq : ∃ᶠ w in 𝓝[≠] z, modularJ w = c := by
    simpa only [Classical.not_not] using (Filter.not_eventually.mp h)
  have hzero : (fun w : ℍ => modularJ w - c) = 0 :=
    UpperHalfPlane.eq_zero_of_frequently (modularJ_mdifferentiable.sub mdifferentiable_const)
      (hfreq.mono fun w hw => sub_eq_zero.mpr hw)
  apply modularJ_not_constant
  exact ⟨c, fun w => sub_eq_zero.mp (congr_fun hzero w)⟩

private theorem
    SpecialPeriods.modularJ_preimage_finite_closed_discrete {s : Set ℂ} (hs : s.Finite) :
    IsClosed (modularJ ⁻¹' s) ∧ IsDiscrete (modularJ ⁻¹' s) := by
  rw [isClosed_and_discrete_iff]
  intro z
  rw [Filter.disjoint_principal_right]
  have h : ∀ᶠ w in 𝓝[≠] z, ∀ c ∈ s, modularJ w ≠ c :=
    hs.eventually_all.mpr (fun c _ => modularJ_eventually_ne c z)
  exact h.mono fun w hw hmem => hw (modularJ w) hmem rfl

private theorem
    SpecialPeriods.modularJ_fibre_isClosed (c : ℂ) : IsClosed {z : ℍ | modularJ z = c} :=
  (modularJ_preimage_finite_closed_discrete (Set.finite_singleton c)).1

private theorem
    SpecialPeriods.modularJ_fibre_isDiscrete (c : ℂ) : IsDiscrete {z : ℍ | modularJ z = c} :=
  (modularJ_preimage_finite_closed_discrete (Set.finite_singleton c)).2

private theorem SpecialPeriods.modularJ_isOpenMap : IsOpenMap modularJ := by
  have hA : AnalyticOnNhd ℂ (modularJ ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := by
    intro z hz
    exact modularJ_analyticAt ⟨z, hz⟩
  have hU : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hO :=
    (hA.is_constant_or_isOpen hU).resolve_left
      (by
        rintro ⟨c, hc⟩
        apply modularJ_not_constant
        refine ⟨c, fun z => ?_⟩
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hc z z.im_pos)
  intro s hs
  have ho :=
    hO (((↑) : ℍ → ℂ) '' s)
      (by
        rintro _ ⟨z, _, rfl⟩
        exact z.im_pos)
      (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap s hs)
  simpa only [Set.image_image, Function.comp_def, UpperHalfPlane.ofComplex_apply] using ho

private def SpecialPeriods.upperHalfPlaneEuclideanHomeomorph_mo1973_16307 : ℂ ≃ₜ ℍ
    where
  toFun z := ⟨⟨z.re, Real.exp z.im⟩, Real.exp_pos z.im⟩
  invFun z := ⟨z.re, Real.log z.im⟩
  left_inv z := by apply Complex.ext <;> simp
  right_inv
    z := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [Real.exp_log z.im_pos]
  continuous_toFun :=
    Continuous.upperHalfPlaneMk
      (Complex.equivRealProdCLM.symm.continuous.comp
        (Complex.continuous_re.prodMk (Real.continuous_exp.comp Complex.continuous_im)))
      (fun z => Real.exp_pos z.im)
  continuous_invFun :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (UpperHalfPlane.continuous_re.prodMk
        (UpperHalfPlane.continuous_im.log (fun z => ne_of_gt z.im_pos)))

private theorem SpecialPeriods.upperHalfPlane_compl_isPathConnected_of_countable {s : Set ℍ}
    (hs : s.Countable) : IsPathConnected sᶜ := by
  let e := upperHalfPlaneEuclideanHomeomorph_mo1973_16307
  have h : IsPathConnected (e ⁻¹' s)ᶜ :=
    (hs.preimage e.injective).isPathConnected_compl_of_one_lt_rank (by simp)
  exact e.isPathConnected_preimage.mp h

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleGenerator₁_ne_one : triangleGenerator₁ ≠ 1 := by
  intro h
  have ho := triangleGenerator₁_order
  simp [h] at ho

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleGenerator₂_ne_one : triangleGenerator₂ ≠ 1 := by
  intro h
  have ho := triangleGenerator₂_order
  simp [h] at ho

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangle_generator₁_pow_apply (n : ℕ) (z : ℍ) :
    triangleGeometricRepresentation (triangleGenerator₁ ^ n) z =
      Triangle.generatorOneSL ^ n • z := by
  rw [map_pow, triangleGeometricRepresentation_generator₁]
  exact Triangle.generatorOnePerm_pow_apply n z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangle_generator₂_pow_apply (n : ℕ) (z : ℍ) :
    triangleGeometricRepresentation (triangleGenerator₂ ^ n) z =
      Triangle.generatorTwoSL ^ n • z := by
  rw [map_pow, triangleGeometricRepresentation_generator₂]
  exact Triangle.generatorTwoPerm_pow_apply n z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangle_generator₁_pow_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 3)
    (z : ℍ) :
    triangleGeometricRepresentation (triangleGenerator₁ ^ n) z = z ↔ z = Triangle.centerOne := by
  rw [triangle_generator₁_pow_apply]
  exact Triangle.generatorOne_pow_fixed_iff n hn hn' z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangle_generator₂_pow_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 4)
    (z : ℍ) :
    triangleGeometricRepresentation (triangleGenerator₂ ^ n) z = z ↔ z = Triangle.centerTwo := by
  rw [triangle_generator₂_pow_apply]
  exact Triangle.generatorTwo_pow_fixed_iff n hn hn' z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangle_conjugate_fixed_iff_mo1973_16318 (g h : TriangleGroup)
    (z : ℍ) :
    triangleGeometricRepresentation (h * g * h⁻¹) z = z ↔
      triangleGeometricRepresentation g (triangleGeometricRepresentation h⁻¹ z) =
        triangleGeometricRepresentation h⁻¹ z := by
  change (h * g * h⁻¹) • z = z ↔ g • (h⁻¹ • z) = h⁻¹ • z
  constructor
  · intro hz
    simpa only [SemigroupAction.mul_smul, inv_smul_smul] using congrArg (fun x : ℍ => h⁻¹ • x) hz
  · intro hz
    simpa only [SemigroupAction.mul_smul, smul_inv_smul] using congrArg (fun x : ℍ => h • x) hz

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangle_conjugate_generator₁_fixed_iff (h : TriangleGroup) (n : ℕ)
    (hn : 0 < n) (hn' : n < 3) (z : ℍ) :
    triangleGeometricRepresentation (h * triangleGenerator₁ ^ n * h⁻¹) z = z ↔
      z = triangleGeometricRepresentation h Triangle.centerOne := by
  rw [triangle_conjugate_fixed_iff_mo1973_16318, triangle_generator₁_pow_fixed_iff n hn hn']
  change h⁻¹ • z = Triangle.centerOne ↔ z = h • Triangle.centerOne
  exact inv_smul_eq_iff

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangle_conjugate_generator₂_fixed_iff (h : TriangleGroup) (n : ℕ)
    (hn : 0 < n) (hn' : n < 4) (z : ℍ) :
    triangleGeometricRepresentation (h * triangleGenerator₂ ^ n * h⁻¹) z = z ↔
      z = triangleGeometricRepresentation h Triangle.centerTwo := by
  rw [triangle_conjugate_fixed_iff_mo1973_16318, triangle_generator₂_pow_fixed_iff n hn hn']
  change h⁻¹ • z = Triangle.centerTwo ↔ z = h • Triangle.centerTwo
  exact inv_smul_eq_iff

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangle_centerOne_not_regular :
    Triangle.centerOne ∉ triangleRegularLocus := by
  intro h
  rw [mem_triangleRegularLocus_iff] at h
  exact
    triangleGenerator₁_ne_one
      (h triangleGenerator₁
        ((triangleGeometricRepresentation_generator₁_apply _).trans Triangle.generatorOne_fix))

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangle_centerTwo_not_regular :
    Triangle.centerTwo ∉ triangleRegularLocus := by
  intro h
  rw [mem_triangleRegularLocus_iff] at h
  exact
    triangleGenerator₂_ne_one
      (h triangleGenerator₂
        ((triangleGeometricRepresentation_generator₂_apply _).trans Triangle.generatorTwo_fix))

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.triangleEllipticSet : Set ℍ :=
  Set.range (fun g : TriangleGroup => triangleGeometricRepresentation g Triangle.centerOne) ∪
    Set.range (fun g : TriangleGroup => triangleGeometricRepresentation g Triangle.centerTwo)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleRegularLocus_eq_compl_ellipticSet :
    triangleRegularLocus = triangleEllipticSetᶜ := by
  ext z
  constructor
  · intro hz hze
    rcases hze with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact
        triangle_centerOne_not_regular
          ((triangleRegularLocus_invariant g Triangle.centerOne).mp hz)
    · exact
        triangle_centerTwo_not_regular
          ((triangleRegularLocus_invariant g Triangle.centerTwo).mp hz)
  · intro hz g hg
    by_contra hgne
    obtain ⟨h, n, hn, hn', hgh⟩ | ⟨h, n, hn, hn', hgh⟩ :=
      triangle_nontrivial_isOfFinOrder_eq_conjugate_generator_power g
        (triangle_isOfFinOrder_of_fixed g z hg) hgne
    · rw [hgh] at hg
      exact hz (Or.inl ⟨h, ((triangle_conjugate_generator₁_fixed_iff h n hn hn' z).mp hg).symm⟩)
    · rw [hgh] at hg
      exact hz (Or.inr ⟨h, ((triangle_conjugate_generator₂_fixed_iff h n hn hn' z).mp hg).symm⟩)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangle_orbit_inter_compact_finite (a : ℍ) {K : Set ℍ}
    (hK : IsCompact K) :
    (Set.range (fun g : TriangleGroup => triangleGeometricRepresentation g a) ∩ K).Finite := by
  have hf : {g : TriangleGroup | triangleGeometricRepresentation g a ∈ K}.Finite := by
    simpa only [Set.image_singleton, Set.singleton_inter_nonempty,
      triangleGeometricAction_smul] using
      (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := TriangleGroup)
        (isCompact_singleton (x := a)) hK)
  convert hf.image (fun g : TriangleGroup => triangleGeometricRepresentation g a) using 1
  ext z
  constructor
  · rintro ⟨⟨g, rfl⟩, hg⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, hg⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem
    SpecialPeriods.triangleEllipticSet_inter_compact_finite {K : Set ℍ} (hK : IsCompact K) :
    (triangleEllipticSet ∩ K).Finite := by
  rw [triangleEllipticSet, Set.union_inter_distrib_right]
  exact
    (triangle_orbit_inter_compact_finite Triangle.centerOne hK).union
      (triangle_orbit_inter_compact_finite Triangle.centerTwo hK)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleEllipticSet_closed_discrete :
    IsClosed triangleEllipticSet ∧ IsDiscrete triangleEllipticSet := by
  rw [isClosed_and_discrete_iff]
  intro z
  obtain ⟨K, hK, hKz⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds z
  have hf := triangleEllipticSet_inter_compact_finite hK
  have hf' : ((triangleEllipticSet ∩ K) ∩ ({ z } : Set ℍ)ᶜ).Finite :=
    hf.subset Set.inter_subset_left
  have hU : ((triangleEllipticSet ∩ K) ∩ ({ z } : Set ℍ)ᶜ)ᶜ ∈ 𝓝 z :=
    hf'.isClosed.isOpen_compl.mem_nhds (by simp)
  rw [Filter.disjoint_principal_right]
  filter_upwards [nhdsWithin_le_nhds hKz, nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with y hyK
    hyU hyz
  intro hyE
  exact hyU ⟨⟨hyE, hyK⟩, hyz⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleEllipticSet_isDiscrete : IsDiscrete triangleEllipticSet :=
  triangleEllipticSet_closed_discrete.2

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleEllipticSet_countable : triangleEllipticSet.Countable :=
  (HereditarilyLindelofSpace.isLindelof triangleEllipticSet).countable_of_isDiscrete
    triangleEllipticSet_isDiscrete

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleRegularLocus_isPathConnected :
    IsPathConnected triangleRegularLocus := by
  rw [triangleRegularLocus_eq_compl_ellipticSet]
  exact upperHalfPlane_compl_isPathConnected_of_countable triangleEllipticSet_countable

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private instance SpecialPeriods.triangleRegularPoint_pathConnected :
    PathConnectedSpace TriangleRegularPoint :=
  isPathConnected_iff_pathConnectedSpace.mp triangleRegularLocus_isPathConnected

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private instance SpecialPeriods.triangleRegularQuotient_pathConnected :
    PathConnectedSpace TriangleRegularQuotient :=
  triangleRegularProject_surjective.pathConnectedSpace triangleRegularProject_covering.continuous

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.triangleRegularToOrbit : TriangleRegularQuotient → TriangleOrbitSpace :=
  Quotient.lift (fun z : TriangleRegularPoint => triangleOrbitProjection z.val) fun x y h =>
    by
    obtain ⟨g, hg⟩ := h
    apply (triangleOrbitProjection_eq_iff _ _).mpr
    exact ⟨g, congrArg Subtype.val hg⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.triangleRegularToOrbit_project (z : TriangleRegularPoint) :
    triangleRegularToOrbit (triangleRegularProject z) = triangleOrbitProjection z.val :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem
    SpecialPeriods.triangleRegularToOrbit_continuous : Continuous triangleRegularToOrbit :=
  (triangleOrbitProjection_continuous.comp continuous_subtype_val).quotient_lift _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleRegularToOrbit_injective :
    Function.Injective triangleRegularToOrbit := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff _ _).mp hab
  apply Quotient.sound
  exact ⟨g, Subtype.ext hg⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem
    SpecialPeriods.triangleRegularToOrbit_isOpenMap : IsOpenMap triangleRegularToOrbit :=
  IsOpenMap.of_comp triangleRegularProject_covering.continuous triangleRegularProject_surjective
    (triangleOrbitProjection_isOpenMap.comp triangleRegularDomain.isOpen.isOpenMap_subtype_val)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleRegularToOrbit_isOpenEmbedding :
    Topology.IsOpenEmbedding triangleRegularToOrbit :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap triangleRegularToOrbit_continuous
    triangleRegularToOrbit_injective triangleRegularToOrbit_isOpenMap

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleRegularToOrbit_range :
    Set.range triangleRegularToOrbit = triangleOrbitProjection '' triangleRegularLocus := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := triangleRegularProject_surjective y
    exact ⟨z.val, z.property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨triangleRegularProject ⟨z, hz⟩, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.triangleOrbitRegularDomain : TopologicalSpace.Opens TriangleOrbitSpace :=
  ⟨Set.range triangleRegularToOrbit, triangleRegularToOrbit_isOpenEmbedding.isOpen_range⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff (z : ℍ) :
    triangleOrbitProjection z ∈ triangleOrbitRegularDomain ↔ z ∈ triangleRegularLocus := by
  change triangleOrbitProjection z ∈ Set.range triangleRegularToOrbit ↔ _
  rw [triangleRegularToOrbit_range]
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff _ _).mp he
    exact (triangleRegularLocus_invariant g z).mp (hg ▸ hw)
  · intro hz
    exact ⟨z, hz, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangleOrbitRegularDomain_mem_iff (x : TriangleOrbitSpace) :
    x ∈ triangleOrbitRegularDomain ↔ x ≠ triangleOrbitCenterOne ∧ x ≠ triangleOrbitCenterTwo := by
  obtain ⟨z, rfl⟩ := triangleOrbitProjection_surjective x
  rw [triangleOrbitProjection_mem_regularDomain_iff, triangleRegularLocus_eq_compl_ellipticSet]
  simp only [triangleEllipticSet, Set.mem_compl_iff, Set.mem_union, Set.mem_range, not_or, ne_eq,
    triangleOrbitCenterOne, triangleOrbitCenterTwo, triangleOrbitProjection_eq_iff]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.triangleRegularOrbitHomeomorph :
    TriangleRegularQuotient ≃ₜ triangleOrbitRegularDomain :=
  triangleRegularToOrbit_isOpenEmbedding.toIsEmbedding.toHomeomorph

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.triangleRegularOrbitParametrization :
    OpenPartialHomeomorph TriangleRegularQuotient TriangleOrbitSpace :=
  triangleRegularToOrbit_isOpenEmbedding.toOpenPartialHomeomorph triangleRegularToOrbit

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.triangleRegularOrbitParametrization_target :
    triangleRegularOrbitParametrization.target =
      (triangleOrbitRegularDomain : Set TriangleOrbitSpace) := by
  simp [triangleRegularOrbitParametrization, triangleOrbitRegularDomain]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.triangleRegularOrbitParametrization_symm_apply
    (x : TriangleRegularQuotient) :
    triangleRegularOrbitParametrization.symm (triangleRegularToOrbit x) = x :=
  triangleRegularOrbitParametrization.left_inv (Set.mem_univ x)

private theorem
    SpecialPeriods.Triangle.horodisc_subset_triangleRegularLocus (Y : ℝ) (hY : width ≤ Y) :
    (horodisc Y : Set ℍ) ⊆ SpecialPeriods.triangleRegularLocus := by
  intro z hz
  apply (SpecialPeriods.mem_triangleRegularLocus_iff z).mpr
  intro g hg
  have hgC := triangle_horodisc_overlap_mem_cusp Y hY g ⟨z, ⟨z, hz, hg⟩, hz⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgC
  have hfixed :
    SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleCuspGenerator ^ n) z =
      z := by
    rw [hn]
    exact hg
  have hzero :
    SpecialPeriods.triangleGeometricRepresentation
        (SpecialPeriods.triangleCuspGenerator ^ (0 : ℤ)) z =
      z := by simp
  have hn0 :=
    SpecialPeriods.triangleGeometricRepresentation_cusp_orbit_injective z
      (hfixed.trans hzero.symm)
  rw [← hn, hn0, zpow_zero]

private theorem SpecialPeriods.Triangle.cuspImage_subset_regularDomain (Y : ℝ) (hY : width ≤ Y) :
    (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace) ⊆
      SpecialPeriods.triangleOrbitRegularDomain := by
  rintro q ⟨z, hz, rfl⟩
  exact
    (SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff z).mpr
      (horodisc_subset_triangleRegularLocus Y hY hz)

private theorem SpecialPeriods.exists_analytic_openPartialHomeomorph {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hderiv : deriv f x ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      x ∈ e.source ∧
        (∀ z, e z = f z) ∧ AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target := by
  let e₀ : OpenPartialHomeomorph ℂ ℂ :=
    (hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hderiv).toOpenPartialHomeomorph f
  have hx : x ∈ e₀.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have hi : AnalyticAt ℂ e₀.symm (f x) := hf.analyticAt_localInverse hderiv
  let e₁ := e₀.restrOpen {z | AnalyticAt ℂ f z} (isOpen_analyticAt ℂ f)
  let e := (e₁.symm.restrOpen {z | AnalyticAt ℂ e₀.symm z} (isOpen_analyticAt ℂ e₀.symm)).symm
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · change (x ∈ e₀.source ∧ AnalyticAt ℂ f x) ∧ AnalyticAt ℂ e₀.symm (f x)
    exact ⟨⟨hx, hf⟩, hi⟩
  · intro z
    rfl
  · intro z hz
    change AnalyticAt ℂ f z
    exact hz.1.2
  · intro z hz
    change AnalyticAt ℂ e₀.symm z
    exact hz.2

private theorem SpecialPeriods.Triangle.upperHalfPlaneCoe_isLocalDiffeomorph_mo1973_16358 :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (UpperHalfPlane.coe : ℍ → ℂ) := by
  let Φ : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℍ ℂ ω :=
    { toPartialEquiv := UpperHalfPlane.ofComplex.symm.toPartialEquiv
      open_source := UpperHalfPlane.ofComplex.symm.open_source
      open_target := UpperHalfPlane.ofComplex.symm.open_target
      contMDiffOn_toFun := UpperHalfPlane.contMDiff_coe.contMDiffOn
      contMDiffOn_invFun := by
        intro w hw
        have he : ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) = w :=
          UpperHalfPlane.ofComplex.left_inv hw
        have hwim : 0 < w.im := by
          rw [← he]
          exact (UpperHalfPlane.ofComplex w).im_pos
        exact (UpperHalfPlane.contMDiffAt_ofComplex hwim).contMDiffWithinAt }
  intro z
  refine ⟨Φ, ?_, fun _ _ => rfl⟩
  exact Set.mem_univ z

private theorem SpecialPeriods.Triangle.cuspQ_coordinate_isLocalDiffeomorphAt_mo1973_16359
    (z : ℍ) : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspQ ∘ UpperHalfPlane.ofComplex) (z : ℂ) := by
  have ha : AnalyticAt ℂ (cuspQ ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
    (UpperHalfPlane.contMDiffAt_iff.mp (cuspQ_holomorphic z)).analyticAt
  obtain ⟨e, hz, he, hforward, hinverse⟩ :=
    SpecialPeriods.exists_analytic_openPartialHomeomorph ha (cuspQ_deriv_ne_zero z)
  refine
    ⟨{  toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := (hforward.contDiffOn e.open_source.uniqueDiffOn).contMDiffOn
        contMDiffOn_invFun := (hinverse.contDiffOn e.open_target.uniqueDiffOn).contMDiffOn }, hz,
      ?_⟩
  intro w _
  exact (he w).symm

private theorem
    SpecialPeriods.Triangle.cuspQ_isLocalDiffeomorph : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω cuspQ :=
  by
  intro z
  have h :=
    (upperHalfPlaneCoe_isLocalDiffeomorph_mo1973_16358 z).comp (K := 𝓘(ℂ)) (P := ℂ)
      (cuspQ_coordinate_isLocalDiffeomorphAt_mo1973_16359 z)
  simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply] using h

private theorem SpecialPeriods.Triangle.cuspQHorodisc_isLocalDiffeomorph (Y : ℝ) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (cuspQHorodisc Y) := by
  intro z
  exact
    isLocalDiffeomorphAt_restrictOpens 𝓘(ℂ) 𝓘(ℂ) (cuspQ_isLocalDiffeomorph (z : ℍ)) (horodisc Y)
      (puncturedCuspBall Y) (fun w hw => (cuspQ_mem_puncturedCuspBall_iff Y w).mpr hw) z.property

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
private theorem SpecialPeriods.instIsManifold1 : IsManifold 𝓘(ℂ) ω TriangleRegularQuotient :=
  triangleRegularQuotient_isManifold

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
private def SpecialPeriods.regularFullChart (x : TriangleRegularQuotient) :
    OpenPartialHomeomorph TriangleOrbitSpace ℂ :=
  triangleRegularOrbitParametrization.symm.trans (chartAt ℂ x)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
private theorem SpecialPeriods.regularFullChart_mem_source_iff (x : TriangleRegularQuotient)
    (y : TriangleOrbitSpace) :
    y ∈ (regularFullChart x).source ↔
      y ∈ triangleOrbitRegularDomain ∧
        triangleRegularOrbitParametrization.symm y ∈ (chartAt ℂ x).source := by
  change
    (y ∈ triangleRegularOrbitParametrization.target ∧
        triangleRegularOrbitParametrization.symm y ∈ (chartAt ℂ x).source) ↔
      _
  rw [triangleRegularOrbitParametrization_target]
  rfl

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
private theorem SpecialPeriods.regularFullChart_source_subset (x : TriangleRegularQuotient) :
    (regularFullChart x).source ⊆ triangleOrbitRegularDomain := fun _ hy =>
  ((regularFullChart_mem_source_iff x _).mp hy).1

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
@[simp]
private theorem SpecialPeriods.regularFullChart_apply_inclusion (x y : TriangleRegularQuotient) :
    regularFullChart x (triangleRegularToOrbit y) = chartAt ℂ x y := by
  change chartAt ℂ x (triangleRegularOrbitParametrization.symm (triangleRegularToOrbit y)) = _
  rw [triangleRegularOrbitParametrization_symm_apply]

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
@[simp]
private theorem
    SpecialPeriods.regularFullChart_mem_source_inclusion_iff (x y : TriangleRegularQuotient) :
    triangleRegularToOrbit y ∈ (regularFullChart x).source ↔ y ∈ (chartAt ℂ x).source := by
  rw [regularFullChart_mem_source_iff, triangleRegularOrbitParametrization_symm_apply]
  exact and_iff_right ⟨y, rfl⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
private theorem SpecialPeriods.regularFullChart_mem_source (x : TriangleRegularQuotient) :
    triangleRegularToOrbit x ∈ (regularFullChart x).source :=
  (regularFullChart_mem_source_inclusion_iff x x).mpr (mem_chart_source ℂ x)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
private theorem SpecialPeriods.exists_regularFullChart (y : TriangleOrbitSpace)
    (hy : y ∈ triangleOrbitRegularDomain) :
    ∃ x : TriangleRegularQuotient, y ∈ (regularFullChart x).source := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, regularFullChart_mem_source x⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
@[simp]
private theorem SpecialPeriods.regularFullChart_projection (x : TriangleRegularQuotient)
    (z : TriangleRegularPoint) :
    regularFullChart x (triangleOrbitProjection z.val) = chartAt ℂ x (triangleRegularProject z) :=
  by rw [← triangleRegularToOrbit_project z, regularFullChart_apply_inclusion]

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
private def SpecialPeriods.triangleRegularCoordinatePartial (x : TriangleRegularQuotient) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleRegularQuotient ℂ ω
    where
  toPartialEquiv := (chartAt ℂ x).toPartialEquiv
  open_source := (chartAt ℂ x).open_source
  open_target := (chartAt ℂ x).open_target
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
private theorem SpecialPeriods.regularFullChart_pullback_isLocalDiffeomorphAt
    (x : TriangleRegularQuotient) {z : ℍ}
    (hz : triangleOrbitProjection z ∈ (regularFullChart x).source) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (regularFullChart x ∘ triangleOrbitProjection) z := by
  have hzreg : z ∈ triangleRegularLocus :=
    (triangleOrbitProjection_mem_regularDomain_iff z).mp (regularFullChart_source_subset x hz)
  let a : TriangleRegularPoint := ⟨z, hzreg⟩
  have hsource : triangleRegularProject a ∈ (chartAt ℂ x).source := by
    apply (regularFullChart_mem_source_inclusion_iff x (triangleRegularProject a)).mp
    simpa only [triangleRegularToOrbit_project] using hz
  have hchart : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x) (triangleRegularProject a) :=
    (triangleRegularCoordinatePartial x).isLocalDiffeomorphAt _ _ _ hsource
  have hreg : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x ∘ triangleRegularProject) a :=
    (triangleRegularProject_isLocalDiffeomorph a).comp (K := 𝓘(ℂ)) (P := ℂ) hchart
  have heq :
    (regularFullChart x ∘ triangleOrbitProjection) ∘ (Subtype.val : TriangleRegularPoint → ℍ) =
      chartAt ℂ x ∘ triangleRegularProject := by
    funext w
    exact regularFullChart_projection x w
  have hrestricted :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      ((regularFullChart x ∘ triangleOrbitProjection) ∘ (Subtype.val : TriangleRegularPoint → ℍ))
      a := by
    rw [heq]
    exact hreg
  exact isLocalDiffeomorphAt_of_comp_opensSubtypeVal 𝓘(ℂ) 𝓘(ℂ) triangleRegularDomain a hrestricted

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
private theorem SpecialPeriods.regularFullChart_pullback_holomorphic (x : TriangleRegularQuotient) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (regularFullChart x ∘ triangleOrbitProjection)
      (triangleOrbitProjection ⁻¹' (regularFullChart x).source) :=
  fun _ hz => (regularFullChart_pullback_isLocalDiffeomorphAt x hz).contMDiffAt.contMDiffWithinAt

private theorem SpecialPeriods.cyclic_eq_bounded_generator_pow_mo1973_16380 {n : ℕ} [NeZero n]
    (a : Multiplicative (ZMod n)) : ∃ k : ℕ, k < n ∧ a = Multiplicative.ofAdd (1 : ZMod n) ^ k := by
  refine ⟨a.toAdd.val, ZMod.val_lt _, ?_⟩
  change a.toAdd = a.toAdd.val • (1 : ZMod n)
  simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

private theorem SpecialPeriods.triangleGenerator₁_commute_eq_pow (g : TriangleGroup)
    (h : Commute triangleGenerator₁ g) : ∃ n : ℕ, n < 3 ∧ g = triangleGenerator₁ ^ n := by
  obtain ⟨a, ha⟩ :=
    CoprodTorsion.coprod_commute_inl (Multiplicative.ofAdd (1 : ZMod 3)) (by decide) g h
  obtain ⟨n, hn, rfl⟩ := cyclic_eq_bounded_generator_pow_mo1973_16380 a
  exact ⟨n, hn, by simpa only [map_pow, triangleGenerator₁] using ha⟩

private theorem SpecialPeriods.triangleGenerator₂_commute_eq_pow (g : TriangleGroup)
    (h : Commute triangleGenerator₂ g) : ∃ n : ℕ, n < 4 ∧ g = triangleGenerator₂ ^ n := by
  obtain ⟨a, ha⟩ :=
    CoprodTorsion.coprod_commute_inr (Multiplicative.ofAdd (1 : ZMod 4)) (by decide) g h
  obtain ⟨n, hn, rfl⟩ := cyclic_eq_bounded_generator_pow_mo1973_16380 a
  exact ⟨n, hn, by simpa only [map_pow, triangleGenerator₂] using ha⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.Triangle.realSLPermutation_commute_of_fixed (A B : SL(2, ℝ)) (a : ℍ)
    (hA : A • a = a) (hB : B • a = a) : Commute (realSLPermutation A) (realSLPermutation B) := by
  apply Equiv.ext
  intro z
  apply (cayleyBiholomorph a).injective
  apply Subtype.ext
  change cayleyCoordinate a (A • (B • z)) = cayleyCoordinate a (B • (A • z))
  rw [cayleyCoordinate_smul A a _ hA, cayleyCoordinate_smul B a _ hB,
    cayleyCoordinate_smul B a _ hB, cayleyCoordinate_smul A a _ hA]
  ring

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.triangle_commute_of_common_fixed (g h : TriangleGroup) (z : ℍ)
    (hg : triangleGeometricRepresentation g z = z)
    (hh : triangleGeometricRepresentation h z = z) : Commute g h := by
  apply triangleGeometricRepresentation_injective
  rw [map_mul, map_mul]
  obtain ⟨A, hA⟩ := triangleGeometricRepresentation_has_SL_lift g
  obtain ⟨B, hB⟩ := triangleGeometricRepresentation_has_SL_lift h
  have ha : A • z = z := (congrArg (fun f : Equiv.Perm ℍ => f z) hA).trans hg
  have hb : B • z = z := (congrArg (fun f : Equiv.Perm ℍ => f z) hB).trans hh
  simpa only [hA, hB] using (Triangle.realSLPermutation_commute_of_fixed A B z ha hb).eq

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.triangle_fixed_centerOne_iff (g : TriangleGroup) :
    triangleGeometricRepresentation g Triangle.centerOne = Triangle.centerOne ↔
      ∃ n : ℕ, n < 3 ∧ g = triangleGenerator₁ ^ n := by
  constructor
  · intro hg
    apply triangleGenerator₁_commute_eq_pow g
    exact
      triangle_commute_of_common_fixed _ _ Triangle.centerOne
        ((triangleGeometricRepresentation_generator₁_apply _).trans Triangle.generatorOne_fix) hg
  · rintro ⟨n, hn, rfl⟩
    clear hn
    rw [triangle_generator₁_pow_apply]
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ', SemigroupAction.mul_smul, ih, Triangle.generatorOne_fix]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.triangle_fixed_centerTwo_iff (g : TriangleGroup) :
    triangleGeometricRepresentation g Triangle.centerTwo = Triangle.centerTwo ↔
      ∃ n : ℕ, n < 4 ∧ g = triangleGenerator₂ ^ n := by
  constructor
  · intro hg
    apply triangleGenerator₂_commute_eq_pow g
    exact
      triangle_commute_of_common_fixed _ _ Triangle.centerTwo
        ((triangleGeometricRepresentation_generator₂_apply _).trans Triangle.generatorTwo_fix) hg
  · rintro ⟨n, hn, rfl⟩
    clear hn
    rw [triangle_generator₂_pow_apply]
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ', SemigroupAction.mul_smul, ih, Triangle.generatorTwo_fix]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.triangle_stabilizer_centerOne :
    MulAction.stabilizer TriangleGroup Triangle.centerOne = Subgroup.zpowers triangleGenerator₁ :=
  by
  apply le_antisymm
  · intro g hg
    obtain ⟨n, _, rfl⟩ := (triangle_fixed_centerOne_iff g).mp hg
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    exact (triangleGeometricRepresentation_generator₁_apply _).trans Triangle.generatorOne_fix

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.triangle_stabilizer_centerTwo :
    MulAction.stabilizer TriangleGroup Triangle.centerTwo = Subgroup.zpowers triangleGenerator₂ :=
  by
  apply le_antisymm
  · intro g hg
    obtain ⟨n, _, rfl⟩ := (triangle_fixed_centerTwo_iff g).mp hg
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    exact (triangleGeometricRepresentation_generator₂_apply _).trans Triangle.generatorTwo_fix

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.triangleOrbitCenterOne_ne_centerTwo :
    triangleOrbitCenterOne ≠ triangleOrbitCenterTwo := by
  intro he
  obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff _ _).mp he.symm
  have hfix :
    triangleGeometricRepresentation (g * triangleGenerator₁ * g⁻¹) Triangle.centerTwo =
      Triangle.centerTwo := by
    simpa only [pow_one] using
      (triangle_conjugate_generator₁_fixed_iff g 1 (by norm_num) (by norm_num)
            Triangle.centerTwo).mpr
        hg.symm
  obtain ⟨n, _, hn⟩ := (triangle_fixed_centerTwo_iff _).mp hfix
  have ho : orderOf (g * triangleGenerator₁ * g⁻¹) = 3 := by
    change orderOf ((MulAut.conj g) triangleGenerator₁) = 3
    exact
      (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
            triangleGenerator₁).trans
        triangleGenerator₁_order
  have hd := orderOf_pow_dvd (x := triangleGenerator₂) n
  rw [← hn, ho, triangleGenerator₂_order] at hd
  norm_num at hd

private def SpecialPeriods.Triangle.cayleyBall (a : ℍ) (r : ℝ) : TopologicalSpace.Opens ℍ :=
  ⟨{z | ‖cayleyCoordinate a z‖ < r},
    isOpen_lt (cayleyCoordinate_holomorphic a).continuous.norm continuous_const⟩

@[simp]
private theorem SpecialPeriods.Triangle.mem_cayleyBall (a z : ℍ) (r : ℝ) :
    z ∈ cayleyBall a r ↔ ‖cayleyCoordinate a z‖ < r :=
  Iff.rfl

private theorem SpecialPeriods.Triangle.center_mem_cayleyBall (a : ℍ) (r : ℝ) :
    a ∈ cayleyBall a r ↔ 0 < r := by simp [cayleyBall, cayleyCoordinate]

private def
    SpecialPeriods.Triangle.cayleyBallToDisc (a : ℍ) (r : ℝ) (hr : 0 < r) (z : cayleyBall a r) :
    SpecialPeriods.Disc :=
  ⟨cayleyCoordinate a z / (r : ℂ),
    by
    have hn : ‖cayleyCoordinate a z / (r : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact (div_lt_one hr).mpr z.property
    simpa [SpecialPeriods.unitDisc] using hn⟩

@[simp]
private theorem SpecialPeriods.Triangle.cayleyBallToDisc_val (a : ℍ) (r : ℝ) (hr : 0 < r)
    (z : cayleyBall a r) : (cayleyBallToDisc a r hr z : ℂ) = cayleyCoordinate a z / (r : ℂ) :=
  rfl

private def SpecialPeriods.Triangle.cayleyBallDiscScale (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (z : SpecialPeriods.Disc) : SpecialPeriods.Disc :=
  ⟨(r : ℂ) * z,
    by
    have hn : ‖(r : ℂ) * (z : ℂ)‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_lt_of_lt_one_right hr (SpecialPeriods.disc_norm_lt_one z)).trans_le hr1
    simpa [SpecialPeriods.unitDisc] using hn⟩

@[simp]
private theorem SpecialPeriods.Triangle.cayleyBallDiscScale_val (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (z : SpecialPeriods.Disc) : (cayleyBallDiscScale r hr hr1 z : ℂ) = (r : ℂ) * z :=
  rfl

private theorem SpecialPeriods.Triangle.cayleyBallDiscScale_norm (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (z : SpecialPeriods.Disc) : ‖(cayleyBallDiscScale r hr hr1 z : ℂ)‖ < r := by
  rw [cayleyBallDiscScale_val, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  exact mul_lt_of_lt_one_right hr (SpecialPeriods.disc_norm_lt_one z)

private def SpecialPeriods.Triangle.cayleyBallFromDisc (a : ℍ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (z : SpecialPeriods.Disc) : cayleyBall a r :=
  ⟨fromDisc a (cayleyBallDiscScale r hr hr1 z),
    by
    change ‖(toDisc a (fromDisc a (cayleyBallDiscScale r hr hr1 z)) : ℂ)‖ < r
    rw [toDisc_fromDisc]
    exact cayleyBallDiscScale_norm r hr hr1 z⟩

private theorem SpecialPeriods.Triangle.cayleyBallFromDisc_toDisc (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) (z : cayleyBall a r) :
    cayleyBallFromDisc a r hr hr1 (cayleyBallToDisc a r hr z) = z := by
  apply Subtype.ext
  change fromDisc a (cayleyBallDiscScale r hr hr1 (cayleyBallToDisc a r hr z)) = z
  have he : cayleyBallDiscScale r hr hr1 (cayleyBallToDisc a r hr z) = toDisc a z := by
    apply Subtype.ext
    simp only [cayleyBallDiscScale_val, cayleyBallToDisc_val, toDisc_val]
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')
  rw [he, fromDisc_toDisc]

private theorem SpecialPeriods.Triangle.cayleyBallToDisc_fromDisc (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) (z : SpecialPeriods.Disc) :
    cayleyBallToDisc a r hr (cayleyBallFromDisc a r hr hr1 z) = z := by
  apply Subtype.ext
  change (toDisc a (fromDisc a (cayleyBallDiscScale r hr hr1 z)) : ℂ) / (r : ℂ) = z
  rw [toDisc_fromDisc, cayleyBallDiscScale_val]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')

private theorem SpecialPeriods.Triangle.cayleyBallToDisc_holomorphic (a : ℍ) (r : ℝ) (hr : 0 < r) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyBallToDisc a r hr) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : cayleyBall a r => cayleyCoordinate a z / (r : ℂ)) :=
    ((cayleyCoordinate_holomorphic a).comp contMDiff_subtype_val).div₀ contMDiff_const
      (fun _ => Complex.ofReal_ne_zero.mpr hr.ne')
  intro z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp (hc z)

private theorem SpecialPeriods.Triangle.cayleyBallDiscScale_holomorphic (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyBallDiscScale r hr hr1) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : SpecialPeriods.Disc => (r : ℂ) * z) :=
    contMDiff_const.mul contMDiff_subtype_val
  intro z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp (hc z)

private theorem SpecialPeriods.Triangle.cayleyBallFromDisc_holomorphic (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyBallFromDisc a r hr hr1) := by
  have hc := (fromDisc_holomorphic a).comp (cayleyBallDiscScale_holomorphic r hr hr1)
  intro z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp (hc z)

private def
    SpecialPeriods.Triangle.cayleyBallBiholomorph (a : ℍ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (cayleyBall a r) SpecialPeriods.Disc ω
    where
  toFun := cayleyBallToDisc a r hr
  invFun := cayleyBallFromDisc a r hr hr1
  left_inv := cayleyBallFromDisc_toDisc a r hr hr1
  right_inv := cayleyBallToDisc_fromDisc a r hr hr1
  contMDiff_toFun := cayleyBallToDisc_holomorphic a r hr
  contMDiff_invFun := cayleyBallFromDisc_holomorphic a r hr hr1

@[simp]
private theorem SpecialPeriods.Triangle.cayleyBallToDisc_center (a : ℍ) (r : ℝ) (hr : 0 < r) :
    cayleyBallToDisc a r hr ⟨a, (center_mem_cayleyBall a r).mpr hr⟩ = SpecialPeriods.discZero := by
  apply Subtype.ext
  simp [cayleyBallToDisc_val, cayleyCoordinate]

@[simp]
private theorem SpecialPeriods.Triangle.cayleyBallBiholomorph_center (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) :
    cayleyBallBiholomorph a r hr hr1 ⟨a, (center_mem_cayleyBall a r).mpr hr⟩ =
      SpecialPeriods.discZero :=
  cayleyBallToDisc_center a r hr

private theorem
    SpecialPeriods.Triangle.exists_cayleyBall_subset (a : ℍ) {U : Set ℍ} (hU : U ∈ 𝓝 a) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ (cayleyBall a r : Set ℍ) ⊆ U := by
  have hc : fromDisc a SpecialPeriods.discZero = a := by
    apply UpperHalfPlane.ext
    simp [fromDisc_val]
  have hpre : fromDisc a ⁻¹' U ∈ 𝓝 SpecialPeriods.discZero :=
    (fromDisc_holomorphic a).continuous.continuousAt.preimage_mem_nhds (by simpa [hc] using hU)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨Min.min r 1, lt_min hr zero_lt_one, min_le_right _ _, ?_⟩
  intro z hz
  have hm : toDisc a z ∈ Metric.ball SpecialPeriods.discZero r := by
    change Dist.dist (toDisc a z : ℂ) (SpecialPeriods.discZero : ℂ) < r
    rw [toDisc_val, SpecialPeriods.discZero_val, dist_zero_right]
    exact lt_of_lt_of_le hz (min_le_left _ _)
  simpa only [Set.mem_preimage, fromDisc_toDisc] using hsub hm

private theorem SpecialPeriods.Triangle.smul_mem_cayleyBall_iff (g : SL(2, ℝ)) (a z : ℍ) (r : ℝ)
    (hfix : g • a = a) : g • z ∈ cayleyBall a r ↔ z ∈ cayleyBall a r := by
  simp only [mem_cayleyBall, cayleyCoordinate_smul g a z hfix, norm_mul,
    slMultiplier_norm g a hfix, one_mul]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticOtherKind : Elliptic.Kind → Elliptic.Kind
  | .three => .four
  | .four => .three

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticCenter : Elliptic.Kind → ℍ
  | .three => centerOne
  | .four => centerTwo

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticGenerator : Elliptic.Kind → SpecialPeriods.TriangleGroup
  | .three => SpecialPeriods.triangleGenerator₁
  | .four => SpecialPeriods.triangleGenerator₂

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticGeneratorSL : Elliptic.Kind → SL(2, ℝ)
  | .three => generatorOneSL
  | .four => generatorTwoSL

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticGenerator_smul (j : Elliptic.Kind) (z : ℍ) :
    ellipticGenerator j • z = ellipticGeneratorSL j • z := by
  cases j
  · exact SpecialPeriods.triangleGeometricRepresentation_generator₁_apply z
  · exact SpecialPeriods.triangleGeometricRepresentation_generator₂_apply z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticGeneratorSL_fixed (j : Elliptic.Kind) :
    ellipticGeneratorSL j • ellipticCenter j = ellipticCenter j := by
  cases j
  · exact generatorOne_fix
  · exact generatorTwo_fix

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticOrbitCenter (j : Elliptic.Kind) :
    SpecialPeriods.TriangleOrbitSpace :=
  SpecialPeriods.triangleOrbitProjection (ellipticCenter j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticOrbitCenter_three :
    ellipticOrbitCenter .three = SpecialPeriods.triangleOrbitCenterOne :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticOrbitCenter_four :
    ellipticOrbitCenter .four = SpecialPeriods.triangleOrbitCenterTwo :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticOrbitCenter_ne_other (j : Elliptic.Kind) :
    ellipticOrbitCenter j ≠ ellipticOrbitCenter (ellipticOtherKind j) := by
  cases j
  · exact SpecialPeriods.triangleOrbitCenterOne_ne_centerTwo
  · exact SpecialPeriods.triangleOrbitCenterOne_ne_centerTwo.symm

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticStabilizer (j : Elliptic.Kind) :
    Subgroup SpecialPeriods.TriangleGroup :=
  MulAction.stabilizer SpecialPeriods.TriangleGroup (ellipticCenter j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.mem_ellipticStabilizer_iff (j : Elliptic.Kind)
    (g : SpecialPeriods.TriangleGroup) :
    g ∈ ellipticStabilizer j ↔ ∃ n : ℕ, n < j.order ∧ g = ellipticGenerator j ^ n := by
  cases j
  · exact SpecialPeriods.triangle_fixed_centerOne_iff g
  · exact SpecialPeriods.triangle_fixed_centerTwo_iff g

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticStabilizer_eq_zpowers (j : Elliptic.Kind) :
    ellipticStabilizer j = Subgroup.zpowers (ellipticGenerator j) := by
  cases j
  · exact SpecialPeriods.triangle_stabilizer_centerOne
  · exact SpecialPeriods.triangle_stabilizer_centerTwo

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticGenerator_mem_stabilizer (j : Elliptic.Kind) :
    ellipticGenerator j ∈ ellipticStabilizer j := by
  change ellipticGenerator j • ellipticCenter j = ellipticCenter j
  rw [ellipticGenerator_smul, ellipticGeneratorSL_fixed]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticStabilizerGenerator (j : Elliptic.Kind) :
    ellipticStabilizer j :=
  ⟨ellipticGenerator j, ellipticGenerator_mem_stabilizer j⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticStabilizerGenerator_val (j : Elliptic.Kind) :
    (ellipticStabilizerGenerator j : SpecialPeriods.TriangleGroup) = ellipticGenerator j :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticStabilizer_eq_generator_pow (j : Elliptic.Kind)
    (g : ellipticStabilizer j) : ∃ n : ℕ, n < j.order ∧ g = ellipticStabilizerGenerator j ^ n := by
  obtain ⟨n, hn, hg⟩ := (mem_ellipticStabilizer_iff j g).mp g.property
  exact ⟨n, hn, Subtype.ext hg⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticOtherOrbitComplement (j : Elliptic.Kind) :
    TopologicalSpace.Opens ℍ :=
  ⟨{z | SpecialPeriods.triangleOrbitProjection z ≠ ellipticOrbitCenter (ellipticOtherKind j)},
    isOpen_ne_fun SpecialPeriods.triangleOrbitProjection_continuous continuous_const⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem
    SpecialPeriods.Triangle.ellipticCenter_mem_otherOrbitComplement (j : Elliptic.Kind) :
    ellipticCenter j ∈ ellipticOtherOrbitComplement j :=
  ellipticOrbitCenter_ne_other j

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.exists_ellipticNeighborhoodRadius (j : Elliptic.Kind) :
    ∃ r : ℝ,
      0 < r ∧
        r ≤ 1 ∧
          (∀ g : SpecialPeriods.TriangleGroup,
              (((g • ·) '' (cayleyBall (ellipticCenter j) r : Set ℍ)) ∩
                    cayleyBall (ellipticCenter j) r).Nonempty →
                g ∈ ellipticStabilizer j) ∧
            (cayleyBall (ellipticCenter j) r : Set ℍ) ⊆ ellipticOtherOrbitComplement j := by
  obtain ⟨U, hU, hret⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self SpecialPeriods.TriangleGroup
      (ellipticCenter j)
  have hV :=
    (ellipticOtherOrbitComplement j).isOpen.mem_nhds (ellipticCenter_mem_otherOrbitComplement j)
  obtain ⟨r, hr, hr1, hball⟩ :=
    exists_cayleyBall_subset (ellipticCenter j) (Filter.inter_mem hU hV)
  refine ⟨r, hr, hr1, ?_, fun z hz => (hball hz).2⟩
  intro g hg
  obtain ⟨z, ⟨w, hw, hgw⟩, hz⟩ := hg
  exact hret g ⟨z, ⟨w, (hball hw).1, hgw⟩, (hball hz).1⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticNeighborhoodRadius (j : Elliptic.Kind) : ℝ :=
  (exists_ellipticNeighborhoodRadius j).choose

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticNeighborhoodRadius_pos (j : Elliptic.Kind) :
    0 < ellipticNeighborhoodRadius j :=
  (exists_ellipticNeighborhoodRadius j).choose_spec.1

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticNeighborhoodRadius_le_one (j : Elliptic.Kind) :
    ellipticNeighborhoodRadius j ≤ 1 :=
  (exists_ellipticNeighborhoodRadius j).choose_spec.2.1

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def
    SpecialPeriods.Triangle.ellipticNeighborhood (j : Elliptic.Kind) : TopologicalSpace.Opens ℍ :=
  cayleyBall (ellipticCenter j) (ellipticNeighborhoodRadius j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticCenter_mem_neighborhood (j : Elliptic.Kind) :
    ellipticCenter j ∈ ellipticNeighborhood j :=
  (center_mem_cayleyBall _ _).mpr (ellipticNeighborhoodRadius_pos j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticNeighborhood_mem_nhds (j : Elliptic.Kind) :
    (ellipticNeighborhood j : Set ℍ) ∈ 𝓝 (ellipticCenter j) :=
  (ellipticNeighborhood j).isOpen.mem_nhds (ellipticCenter_mem_neighborhood j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticNeighborhood_return (j : Elliptic.Kind)
    (g : SpecialPeriods.TriangleGroup)
    (hret : (((g • ·) '' (ellipticNeighborhood j : Set ℍ)) ∩ ellipticNeighborhood j).Nonempty) :
    g ∈ ellipticStabilizer j :=
  (exists_ellipticNeighborhoodRadius j).choose_spec.2.2.1 g hret

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticNeighborhood_subset_otherOrbitComplement
    (j : Elliptic.Kind) : (ellipticNeighborhood j : Set ℍ) ⊆ ellipticOtherOrbitComplement j :=
  (exists_ellipticNeighborhoodRadius j).choose_spec.2.2.2

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem
    SpecialPeriods.Triangle.ellipticNeighborhood_avoids_other (j : Elliptic.Kind) (z : ℍ)
    (hz : z ∈ ellipticNeighborhood j) :
    SpecialPeriods.triangleOrbitProjection z ≠ ellipticOrbitCenter (ellipticOtherKind j) :=
  ellipticNeighborhood_subset_otherOrbitComplement j hz

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticStabilizer_cayleyBall_invariant (j : Elliptic.Kind)
    (g : ellipticStabilizer j) (r : ℝ) (z : ℍ) :
    (g : SpecialPeriods.TriangleGroup) • z ∈ cayleyBall (ellipticCenter j) r ↔
      z ∈ cayleyBall (ellipticCenter j) r := by
  have hfix :
    (SpecialPeriods.triangleMatrixLift g : SL(2, ℝ)) • ellipticCenter j = ellipticCenter j :=
    (SpecialPeriods.triangleMatrixLift_smul g _).trans g.property
  rw [← SpecialPeriods.triangleMatrixLift_smul]
  exact smul_mem_cayleyBall_iff (SpecialPeriods.triangleMatrixLift g) (ellipticCenter j) z r hfix

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticNeighborhood_invariant (j : Elliptic.Kind)
    (g : ellipticStabilizer j) (z : ℍ) :
    (g : SpecialPeriods.TriangleGroup) • z ∈ ellipticNeighborhood j ↔
      z ∈ ellipticNeighborhood j :=
  ellipticStabilizer_cayleyBall_invariant j g _ z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticNeighborhood_mapsTo (j : Elliptic.Kind)
    (g : ellipticStabilizer j) :
    Set.MapsTo (fun z : ℍ => (g : SpecialPeriods.TriangleGroup) • z) (ellipticNeighborhood j)
      (ellipticNeighborhood j) :=
  fun z hz => (ellipticNeighborhood_invariant j g z).mpr hz

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[instance_reducible]
private def SpecialPeriods.Triangle.ellipticNeighborhoodAction (j : Elliptic.Kind) :
    MulAction (ellipticStabilizer j) (ellipticNeighborhood j) :=
  LocalOrbitQuotient.restrictedAction (ellipticStabilizer j) (ellipticNeighborhood j)
    (ellipticNeighborhood_mapsTo j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticNeighborhood_smul_val (j : Elliptic.Kind)
    (g : ellipticStabilizer j) (z : ellipticNeighborhood j) :
    letI := ellipticNeighborhoodAction j
    ((g • z : ellipticNeighborhood j) : ℍ) = (g : SpecialPeriods.TriangleGroup) • (z : ℍ) :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticNeighborhoodCenter (j : Elliptic.Kind) :
    ellipticNeighborhood j :=
  ⟨ellipticCenter j, ellipticCenter_mem_neighborhood j⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticNeighborhoodChart (j : Elliptic.Kind) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (ellipticNeighborhood j) SpecialPeriods.Disc ω :=
  cayleyBallBiholomorph (ellipticCenter j) (ellipticNeighborhoodRadius j)
    (ellipticNeighborhoodRadius_pos j) (ellipticNeighborhoodRadius_le_one j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticNeighborhoodChart_val (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    (ellipticNeighborhoodChart j z : ℂ) =
      cayleyCoordinate (ellipticCenter j) z / (ellipticNeighborhoodRadius j : ℂ) :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
private theorem SpecialPeriods.Triangle.ellipticNeighborhoodChart_center (j : Elliptic.Kind) :
    ellipticNeighborhoodChart j (ellipticNeighborhoodCenter j) = SpecialPeriods.discZero :=
  cayleyBallBiholomorph_center _ _ _ _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticNeighborhoodChart_generator (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    letI := ellipticNeighborhoodAction j
    ellipticNeighborhoodChart j (ellipticStabilizerGenerator j • z) =
      Elliptic.familyRotation j (ellipticNeighborhoodChart j z) := by
  let := ellipticNeighborhoodAction j
  apply Subtype.ext
  change
    cayleyCoordinate (ellipticCenter j) (ellipticGenerator j • (z : ℍ)) /
        (ellipticNeighborhoodRadius j : ℂ) =
      _
  rw [ellipticGenerator_smul]
  cases j
  · change
      cayleyCoordinate centerOne (generatorOneSL • (z : ℍ)) /
          (ellipticNeighborhoodRadius .three : ℂ) =
        -SpecialPeriods.rho *
          (cayleyCoordinate centerOne z / (ellipticNeighborhoodRadius .three : ℂ))
    rw [generatorOne_cayley, mul_div_assoc]
  · change
      cayleyCoordinate centerTwo (generatorTwoSL • (z : ℍ)) /
          (ellipticNeighborhoodRadius .four : ℂ) =
        -Complex.I * (cayleyCoordinate centerTwo z / (ellipticNeighborhoodRadius .four : ℂ))
    rw [generatorTwo_cayley, mul_div_assoc]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem
    SpecialPeriods.Triangle.ellipticNeighborhood_projection_eq_center_iff (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    SpecialPeriods.triangleOrbitProjection z = ellipticOrbitCenter j ↔
      z = ellipticNeighborhoodCenter j := by
  constructor
  · intro hz
    obtain ⟨g, hg⟩ := (SpecialPeriods.triangleOrbitProjection_eq_iff z (ellipticCenter j)).mp hz
    have hgH : g ∈ ellipticStabilizer j :=
      ellipticNeighborhood_return j g
        ⟨z, ⟨ellipticCenter j, ellipticCenter_mem_neighborhood j, hg⟩, z.property⟩
    apply Subtype.ext
    exact hg.symm.trans hgH
  · rintro rfl
    rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private abbrev SpecialPeriods.Triangle.EllipticNeighborhoodQuotient (j : Elliptic.Kind) :=
  LocalOrbitQuotient.LocalQuotient (ellipticStabilizer j) (ellipticNeighborhood j)
    (ellipticNeighborhood_mapsTo j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticNeighborhoodImage (j : Elliptic.Kind) :
    TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace :=
  LocalOrbitQuotient.imageOpen (G := SpecialPeriods.TriangleGroup) (ellipticNeighborhood j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private def SpecialPeriods.Triangle.ellipticNeighborhoodQuotientHomeomorph (j : Elliptic.Kind) :
    EllipticNeighborhoodQuotient j ≃ₜ ellipticNeighborhoodImage j :=
  LocalOrbitQuotient.localHomeomorph (ellipticStabilizer j) (ellipticNeighborhood j)
    (ellipticNeighborhood_mapsTo j) (ellipticNeighborhood_return j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem
    SpecialPeriods.Triangle.ellipticOrbitCenter_mem_neighborhoodImage (j : Elliptic.Kind) :
    ellipticOrbitCenter j ∈ ellipticNeighborhoodImage j :=
  ⟨ellipticCenter j, ellipticCenter_mem_neighborhood j, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.Triangle.ellipticOtherOrbitCenter_not_mem_neighborhoodImage
    (j : Elliptic.Kind) :
    ellipticOrbitCenter (ellipticOtherKind j) ∉ ellipticNeighborhoodImage j := by
  rintro ⟨z, hz, he⟩
  exact ellipticNeighborhood_avoids_other j z hz he

private theorem SpecialPeriods.TriangleQuotientPower.discPower_isOpenMap (m : ℕ) (hm : 0 < m) :
    IsOpenMap (Elliptic.discPower m hm) := by
  let : NeZero m := ⟨hm.ne'⟩
  have h : IsOpenMap (fun z : SpecialPeriods.Disc => (z : ℂ) ^ m) :=
    (Complex.isOpenQuotientMap_pow m).isOpenMap.comp
      SpecialPeriods.unitDisc.isOpen.isOpenMap_subtype_val
  exact h.subtype_mk _

private theorem SpecialPeriods.TriangleQuotientPower.map_pow_smul {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) (n : ℕ) (y : Y) :
    e ((a ^ n) • y) = (Elliptic.familyRotation j)^[n] (e y) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', SemigroupAction.mul_smul, heq, ih, Function.iterate_succ_apply']

private theorem SpecialPeriods.TriangleQuotientPower.powerCoordinate_eq_iff_mem_orbit {H Y : Type*}
    [Group H] [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind)
    (e : Y ≃ₜ SpecialPeriods.Disc) (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) (x y : Y) :
    Elliptic.discPower j.order j.order_pos (e x) = Elliptic.discPower j.order j.order_pos (e y) ↔
      x ∈ MulAction.orbit H y := by
  rw [Elliptic.discPower_eq_iff_familyRotation]
  constructor
  · rintro ⟨n, hn, hxy⟩
    refine ⟨a ^ n, ?_⟩
    apply e.injective
    exact (map_pow_smul j e a heq n y).trans hxy
  · rintro ⟨h, hh⟩
    obtain ⟨n, hn, rfl⟩ := hgen h
    exact ⟨n, hn, (map_pow_smul j e a heq n y).symm.trans (congrArg e hh)⟩

private def
    SpecialPeriods.TriangleQuotientPower.orbitDiscMap {H Y : Type*} [Group H] [TopologicalSpace Y]
    [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc) (a : H)
    (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) :
    Quotient (MulAction.orbitRel H Y) → SpecialPeriods.Disc :=
  Quotient.lift (fun y => Elliptic.discPower j.order j.order_pos (e y)) fun x y hxy =>
    (powerCoordinate_eq_iff_mem_orbit j e a hgen heq x y).mpr hxy

@[simp]
private theorem SpecialPeriods.TriangleQuotientPower.orbitDiscMap_mk {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) (y : Y) :
    orbitDiscMap j e a hgen heq (Quotient.mk (MulAction.orbitRel H Y) y) =
      Elliptic.discPower j.order j.order_pos (e y) :=
  rfl

private theorem SpecialPeriods.TriangleQuotientPower.orbitDiscMap_continuous {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) :
    Continuous (orbitDiscMap j e a hgen heq) :=
  ((Elliptic.discPower_continuous j.order j.order_pos).comp e.continuous).quotient_lift _

private theorem SpecialPeriods.TriangleQuotientPower.orbitDiscMap_surjective {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) :
    Function.Surjective (orbitDiscMap j e a hgen heq) := by
  intro z
  obtain ⟨w, hw⟩ := Elliptic.discPower_surjective j.order j.order_pos z
  refine ⟨Quotient.mk (MulAction.orbitRel H Y) (e.symm w), ?_⟩
  simpa only [orbitDiscMap_mk, e.apply_symm_apply] using hw

private theorem SpecialPeriods.TriangleQuotientPower.orbitDiscMap_injective {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) :
    Function.Injective (orbitDiscMap j e a hgen heq) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y hxy
  apply Quotient.sound
  exact (powerCoordinate_eq_iff_mem_orbit j e a hgen heq x y).mp hxy

private theorem SpecialPeriods.TriangleQuotientPower.orbitDiscMap_isOpenMap {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) :
    IsOpenMap (orbitDiscMap j e a hgen heq) := by
  apply
    IsOpenMap.of_comp
      (show Continuous (Quotient.mk (MulAction.orbitRel H Y)) from continuous_quotient_mk')
      Quotient.mk_surjective
  exact (discPower_isOpenMap j.order j.order_pos).comp e.isOpenMap

private def SpecialPeriods.TriangleQuotientPower.orbitDiscHomeomorph {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) :
    Quotient (MulAction.orbitRel H Y) ≃ₜ SpecialPeriods.Disc :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (orbitDiscMap j e a hgen heq)
      ⟨orbitDiscMap_injective j e a hgen heq, orbitDiscMap_surjective j e a hgen heq⟩)
    (orbitDiscMap_continuous j e a hgen heq) (orbitDiscMap_isOpenMap j e a hgen heq)

private theorem SpecialPeriods.Triangle.cayleyCoordinate_eq_zero_iff (a z : ℍ) :
    cayleyCoordinate a z = 0 ↔ z = a := by
  simp [cayleyCoordinate, div_eq_zero_iff, sub_conj_ne_zero a z, sub_eq_zero]

private theorem SpecialPeriods.Triangle.cayleyCoordinate_analyticAt (a z : ℍ) :
    AnalyticAt ℂ (cayleyCoordinate a ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp
        ((cayleyCoordinate_holomorphic a).mdifferentiable (by simp))).analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

private theorem SpecialPeriods.Triangle.cayleyCoordinate_hasStrictDerivAt_center (a : ℍ) :
    HasStrictDerivAt (cayleyCoordinate a ∘ UpperHalfPlane.ofComplex)
      (1 / ((a : ℂ) - starRingEnd ℂ (a : ℂ))) (a : ℂ) := by
  have hd := sub_conj_ne_zero a a
  have h :
    HasStrictDerivAt (fun z : ℂ => (z - (a : ℂ)) / (z - starRingEnd ℂ (a : ℂ)))
      (1 / ((a : ℂ) - starRingEnd ℂ (a : ℂ))) (a : ℂ) := by
    have hn : HasStrictDerivAt (fun z : ℂ => z - (a : ℂ)) 1 (a : ℂ) :=
      (hasStrictDerivAt_id (a : ℂ)).sub_const (a : ℂ)
    have hd' : HasStrictDerivAt (fun z : ℂ => z - starRingEnd ℂ (a : ℂ)) 1 (a : ℂ) :=
      (hasStrictDerivAt_id (a : ℂ)).sub_const (starRingEnd ℂ (a : ℂ))
    convert hn.div hd' hd using 1
    all_goals
      first
      | rfl
      | (field_simp; ring)
  apply h.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex a.im_pos] with z hz
  change (UpperHalfPlane.ofComplex z : ℂ) = z at hz
  simp only [Function.comp_apply, cayleyCoordinate, hz]

private theorem SpecialPeriods.Triangle.cayleyCoordinate_order_center (a : ℍ) :
    analyticOrderAt (cayleyCoordinate a ∘ UpperHalfPlane.ofComplex) (a : ℂ) = 1 := by
  apply (cayleyCoordinate_analyticAt a a).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simp [cayleyCoordinate]
  · rw [(cayleyCoordinate_hasStrictDerivAt_center a).hasDerivAt.deriv]
    exact one_div_ne_zero (sub_conj_ne_zero a a)

private def SpecialPeriods.Triangle.complexDivideBiholomorph (c : ℂ) (hc : c ≠ 0) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ω where
  toFun z := z / c
  invFun z := z * c
  left_inv z := div_mul_cancel₀ z hc
  right_inv z := mul_div_cancel_right₀ z hc
  contMDiff_toFun := contMDiff_id.div₀ contMDiff_const (fun _ => hc)
  contMDiff_invFun := contMDiff_id.mul contMDiff_const

private def SpecialPeriods.Triangle.normalizedCayley (a : ℍ) (r : ℝ) (z : ℍ) : ℂ :=
  cayleyCoordinate a z / (r : ℂ)

private theorem SpecialPeriods.Triangle.normalizedCayley_holomorphic (a : ℍ) (r : ℝ) (hr : r ≠ 0) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (normalizedCayley a r) :=
  (cayleyCoordinate_holomorphic a).div₀ contMDiff_const (fun _ => Complex.ofReal_ne_zero.mpr hr)

private theorem
    SpecialPeriods.Triangle.normalizedCayley_isLocalDiffeomorph (a : ℍ) (r : ℝ) (hr : r ≠ 0) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (normalizedCayley a r) := by
  intro z
  have hc :=
    ((cayleyBiholomorph a).isLocalDiffeomorph z).comp (K := 𝓘(ℂ)) (P := ℂ)
      (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) SpecialPeriods.unitDisc (toDisc a z))
  exact
    hc.comp (K := 𝓘(ℂ)) (P := ℂ)
      ((complexDivideBiholomorph (r : ℂ) (Complex.ofReal_ne_zero.mpr hr)).isLocalDiffeomorph
        (cayleyCoordinate a z))

private def SpecialPeriods.Triangle.normalizedCayleyBranch (a : ℍ) (r : ℝ) (m : ℕ) (z : ℍ) : ℂ :=
  normalizedCayley a r z ^ m

private theorem
    SpecialPeriods.Triangle.normalizedCayleyBranch_holomorphic (a : ℍ) (r : ℝ) (hr : r ≠ 0)
    (m : ℕ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (normalizedCayleyBranch a r m) :=
  (normalizedCayley_holomorphic a r hr).pow m

private theorem
    SpecialPeriods.Triangle.normalizedCayleyBranch_isLocalDiffeomorphAt (a z : ℍ) (r : ℝ)
    (hr : r ≠ 0) (m : ℕ) (hm : 0 < m) (hz : z ≠ a) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (normalizedCayleyBranch a r m) z := by
  have hc : normalizedCayley a r z ≠ 0 :=
    div_ne_zero ((cayleyCoordinate_eq_zero_iff a z).not.mpr hz) (Complex.ofReal_ne_zero.mpr hr)
  exact
    (normalizedCayley_isLocalDiffeomorph a r hr z).comp (K := 𝓘(ℂ)) (P := ℂ)
      (Elliptic.complexPower_isLocalDiffeomorphAt m hm (normalizedCayley a r z) hc)

end Mathoverflow1973

end
