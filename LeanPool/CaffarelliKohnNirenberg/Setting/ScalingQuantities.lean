/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.Theta
public import LeanPool.CaffarelliKohnNirenberg.Statements.Gamma
public import LeanPool.CaffarelliKohnNirenberg.Statements.Lambda

/-!
# Scale invariance of the dimensionless quantities

This module formalizes the rescaled fields of Definition `def:rescaling` of
`paper/ckn.tex` and the transformation law of Lemma `lem:scaling-quantities`:
at the rescaled base point each of `α`, `β`, `γ`, `δ`, `λ`, `θ` is unchanged
from its value at the original point with the radius scaled by the dilation.

The analytic input is the parabolic change of variables for cylinder integrals
and time-slice essential suprema, together with the elementary algebra of the
exponents.  The essential supremum of the velocity `L²` energy is handled with
the boundedness assumption that makes the transform of an essential supremum
legitimate; every other quantity is unconditional.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

/-! ### The rescaled fields -/

/-- The velocity component of the parabolically rescaled solution of Definition
`def:rescaling`: `u^{μ,z₀}(y,s) = μ u(x₀ + μ y, t₀ + μ² s)`. -/
noncomputable def rescaleVelocity (μ : ℝ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun w => μ • u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w))

/-- The pressure component of the parabolically rescaled solution of Definition
`def:rescaling`: `p^{μ,z₀}(y,s) = μ² p(x₀ + μ y, t₀ + μ² s)`. -/
noncomputable def rescalePressure (μ : ℝ) (z₀ : ParabolicPoint)
    (p : ParabolicPoint → ℝ) : ParabolicPoint → ℝ :=
  fun w => μ ^ 2 * p (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w))

/-- The force component of the parabolically rescaled solution of Definition
`def:rescaling`: `f^{μ,z₀}(y,s) = μ³ f(x₀ + μ y, t₀ + μ² s)`. -/
noncomputable def rescaleForce (μ : ℝ) (z₀ : ParabolicPoint)
    (f : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun w => μ ^ 3 • f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w))

/-- The rescaled spatial gradient datum matching `rescaleVelocity`: the chain
rule gives `∇(u^{μ,z₀}) = μ² (∇u) ∘ T` for `T(y,s) = (x₀ + μ y, t₀ + μ² s)`. -/
noncomputable def rescaleGradient (μ : ℝ) (z₀ : ParabolicPoint)
    (Du : ParabolicPoint → Fin 3 → Vec3) : ParabolicPoint → Fin 3 → Vec3 :=
  fun w i => μ ^ 2 • Du (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)) i

/-! ### The underlying affine map and its Jacobian -/

/-- The spatial part `y ↦ x + a y` of the parabolic rescaling. -/
def spatialAffine (a : ℝ) (x : Vec3) : Vec3 → Vec3 := fun y => x + a • y

/-- The time part `s ↦ t + a² s` of the parabolic rescaling. -/
def timeAffine (a : ℝ) (t : ℝ) : ℝ → ℝ := fun s => t + a ^ 2 * s

/-- The parabolic rescaling map `z ↦ (x₀ + μ z₁, t₀ + μ² z₂)`. -/
def parabolicAffine (a : ℝ) (x : Vec3) (t : ℝ) : ParabolicPoint → ParabolicPoint :=
  fun z => parabolicTranslate x t (parabolicScale a z)

private theorem spatialAffine_measurableEmbedding (a : ℝ) (ha : 0 < a) (x : Vec3) :
    MeasurableEmbedding (spatialAffine a x) := by
  have h : spatialAffine a x =
      (fun y : Vec3 => x + y) ∘
        (fun y : Vec3 => (isUnit_iff_ne_zero.2 ha.ne').unit • y) := by
    funext y
    simp [spatialAffine, Units.smul_def]
  rw [h]
  exact (Homeomorph.addLeft x).measurableEmbedding.comp
    (Homeomorph.smul (isUnit_iff_ne_zero.2 ha.ne').unit).measurableEmbedding

private theorem timeAffine_measurableEmbedding (a : ℝ) (ha : 0 < a) (t : ℝ) :
    MeasurableEmbedding (timeAffine a t) := by
  have h : timeAffine a t =
      (fun s : ℝ => t + s) ∘
        (fun s : ℝ => (isUnit_iff_ne_zero.2 (sq_pos_of_pos ha).ne').unit • s) := by
    funext s
    simp [timeAffine, Units.smul_def, sq]
  rw [h]
  exact (Homeomorph.addLeft t).measurableEmbedding.comp
    (Homeomorph.smul (isUnit_iff_ne_zero.2 (sq_pos_of_pos ha).ne').unit).measurableEmbedding

private theorem parabolicAffine_measurableEmbedding (a : ℝ) (ha : 0 < a)
    (x : Vec3) (t : ℝ) : MeasurableEmbedding (parabolicAffine a x t) := by
  have h : parabolicAffine a x t = Prod.map (spatialAffine a x) (timeAffine a t) := by
    funext z
    rcases z with ⟨y, s⟩
    rfl
  rw [h]
  exact MeasurableEmbedding.prodMap
    (spatialAffine_measurableEmbedding a ha x)
    (timeAffine_measurableEmbedding a ha t)

private theorem map_spatialAffine (a : ℝ) (ha : 0 < a) (x : Vec3) :
    Measure.map (spatialAffine a x) (volume : Measure Vec3) =
      ENNReal.ofReal (a⁻¹ ^ 3) • (volume : Measure Vec3) := by
  have h : spatialAffine a x = (fun y : Vec3 => x + y) ∘ (fun y : Vec3 => a • y) := by
    funext y
    simp [spatialAffine]
  rw [h, ← Measure.map_map (measurable_const_add x) (measurable_const_smul a)]
  rw [Measure.map_addHaar_smul (μ := (volume : Measure Vec3)) ha.ne', Measure.map_smul]
  on_goal 1 => rw [MeasureTheory.map_add_left_eq_self]
  · congr 1
    rw [Module.finrank_fin_fun, abs_of_pos (inv_pos.mpr (pow_pos ha 3)), ← inv_pow]
  · exact (measurable_const_add x).aemeasurable

private theorem map_timeAffine (a : ℝ) (ha : 0 < a) (t : ℝ) :
    Measure.map (timeAffine a t) (volume : Measure ℝ) =
      ENNReal.ofReal ((a ^ 2)⁻¹) • (volume : Measure ℝ) := by
  have h : timeAffine a t = (fun s : ℝ => t + s) ∘ (fun s : ℝ => a ^ 2 • s) := by
    funext s
    simp [timeAffine, smul_eq_mul]
  rw [h, ← Measure.map_map (measurable_const_add t) (measurable_const_smul (a ^ 2))]
  rw [Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (sq_pos_of_pos ha).ne',
    Measure.map_smul]
  on_goal 1 => rw [MeasureTheory.map_add_left_eq_self]
  · congr 1
    rw [Module.finrank_self]
    norm_num
  · exact (measurable_const_add t).aemeasurable

private theorem map_parabolicAffine (a : ℝ) (ha : 0 < a) (x : Vec3) (t : ℝ) :
    Measure.map (parabolicAffine a x t) (volume : Measure ParabolicPoint) =
      ENNReal.ofReal (a⁻¹ ^ 5) • (volume : Measure ParabolicPoint) := by
  change Measure.map (fun z : Vec3 × ℝ => (x + a • z.1, t + a ^ 2 * z.2))
      (volume : Measure (Vec3 × ℝ)) =
    ENNReal.ofReal (a⁻¹ ^ 5) • (volume : Measure (Vec3 × ℝ))
  have hcoef : ENNReal.ofReal (a⁻¹ ^ 3) * ENNReal.ofReal ((a ^ 2)⁻¹) =
      ENNReal.ofReal (a⁻¹ ^ 5) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [inv_pow, inv_pow]
    rw [mul_comm (a ^ 3)⁻¹, ← mul_inv_rev, ← pow_add]
  have hfun : (fun z : Vec3 × ℝ => (x + a • z.1, t + a ^ 2 * z.2)) =
      Prod.map (spatialAffine a x) (timeAffine a t) := rfl
  have hvol : (volume : Measure (Vec3 × ℝ)) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) := rfl
  have hmap := Measure.map_prod_map (volume : Measure Vec3) (volume : Measure ℝ)
    (spatialAffine_measurableEmbedding a ha x).measurable
    (timeAffine_measurableEmbedding a ha t).measurable
  rw [map_spatialAffine a ha x, map_timeAffine a ha t, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul] at hmap
  rw [hfun, hvol, ← hmap, hcoef]

private theorem parabolicCylinder_meas (x : Vec3) (t r : ℝ) :
    MeasurableSet (parabolicCylinder x t r) :=
  (vec3Ball_measurable x r).prod measurableSet_Ioc

/-- The nonnegative integral over a parabolic cylinder is invariant under the
parabolic rescaling `T(y,s) = (x₀ + μ y, t₀ + μ² s)` up to the Jacobian factor
`μ⁻⁵`, matching the change of variables used in Lemma `lem:scaling-quantities`. -/
theorem cylinder_lintegral_comp_parabolicRescale {μ : ℝ} (hμ : 0 < μ)
    (x : Vec3) (t r : ℝ) (F : ParabolicPoint → ℝ≥0∞) :
    ∫⁻ z in parabolicCylinder 0 0 r, F (parabolicTranslate x t (parabolicScale μ z)) =
      ENNReal.ofReal (μ⁻¹ ^ 5) *
        ∫⁻ z in parabolicCylinder x t (μ * r), F z := by
  have hemb := parabolicAffine_measurableEmbedding μ hμ x t
  have himg : parabolicAffine μ x t '' parabolicCylinder 0 0 r =
      parabolicCylinder x t (μ * r) := by
    change (fun z => parabolicTranslate x t (parabolicScale μ z)) ''
        parabolicCylinder 0 0 r = _
    rw [← Set.image_image]
    exact parabolicCylinder_rescale_image hμ x t r
  have hpre : parabolicAffine μ x t ⁻¹' parabolicCylinder x t (μ * r) =
      parabolicCylinder 0 0 r := by
    rw [← himg, Set.preimage_image_eq _ hemb.injective]
  have hmap : Measure.map (parabolicAffine μ x t)
      (volume.restrict (parabolicCylinder 0 0 r)) =
      ENNReal.ofReal (μ⁻¹ ^ 5) •
        volume.restrict (parabolicCylinder x t (μ * r)) := by
    have h := Measure.restrict_map (μ := (volume : Measure ParabolicPoint))
      hemb.measurable (parabolicCylinder_meas x t (μ * r))
    rw [map_parabolicAffine μ hμ x t, Measure.restrict_smul, hpre] at h
    exact h.symm
  calc
    ∫⁻ z in parabolicCylinder 0 0 r, F (parabolicTranslate x t (parabolicScale μ z))
        = ∫⁻ z, F (parabolicAffine μ x t z)
            ∂volume.restrict (parabolicCylinder 0 0 r) := by
          simp only [parabolicAffine]
    _ = ∫⁻ w, F w ∂Measure.map (parabolicAffine μ x t)
            (volume.restrict (parabolicCylinder 0 0 r)) :=
          (hemb.lintegral_map F).symm
    _ = ∫⁻ w, F w ∂(ENNReal.ofReal (μ⁻¹ ^ 5) •
            volume.restrict (parabolicCylinder x t (μ * r))) := by rw [hmap]
    _ = ENNReal.ofReal (μ⁻¹ ^ 5) *
          ∫⁻ w in parabolicCylinder x t (μ * r), F w := by
          rw [lintegral_smul_measure]
          rfl

/-! ### Exponential algebra -/

/-- `μ⁻¹ μ⁻⁵ = μ⁻¹` in the form needed for the Dirichlet energy. -/
private lemma inv_cube_mul_sq (μ : ℝ) (hμ : μ ≠ 0) : (μ⁻¹) ^ 3 * μ ^ 2 = μ⁻¹ := by
  rw [inv_pow]
  field_simp

/-- The real power `μ⁻²` agrees with the second power of `μ⁻¹`. -/
private lemma rpow_neg_two_eq_inv_sq (μ : ℝ) (hμ : 0 < μ) :
    μ ^ (-2 : ℝ) = (μ⁻¹) ^ 2 := by
  rw [Real.rpow_neg hμ.le 2, inv_pow]
  congr 1
  exact Real.rpow_natCast μ 2

/-- `r⁻¹ (μ⁻¹ E) = (μ r)⁻¹ E`. -/
private lemma inv_mul_mul (μ r E : ℝ) : r⁻¹ * (μ⁻¹ * E) = (μ * r)⁻¹ * E := by
  rw [mul_inv_rev]
  ring

/-- `r⁻² μ⁻² = (μ r)⁻²` for positive factors. -/
private lemma rpow_neg_two_mul (μ r : ℝ) (hμ : 0 < μ) (hr : 0 < r) :
    r ^ (-2 : ℝ) * (μ⁻¹) ^ 2 = (μ * r) ^ (-2 : ℝ) := by
  rw [show (μ⁻¹) ^ 2 = μ ^ (-2 : ℝ) from (rpow_neg_two_eq_inv_sq μ hμ).symm]
  rw [mul_comm, ← Real.mul_rpow hμ.le hr.le]

/-- `μ^{3q} μ⁻⁵ = μ^{3q-5}` for a positive dilation, the exponent identity behind
the scaling of `λ`. -/
private lemma rpow_three_q_mul_inv_pow_five (q μ : ℝ) (hμ : 0 < μ) :
    μ ^ (3 * q) * μ⁻¹ ^ 5 = μ ^ (3 * q - 5) := by
  have h5 : μ⁻¹ ^ 5 = μ ^ (-5 : ℝ) := by
    rw [inv_pow, ← Real.rpow_natCast μ 5, ← Real.rpow_neg hμ.le ((5 : ℕ) : ℝ)]
    norm_num
  rw [h5, ← Real.rpow_add hμ]
  congr 1

/-- The `λ` exponent identity `r^{3-5/q} (μ^{3q-5})^{1/q} = (μr)^{3-5/q}`, stated
with an arbitrary tail factor so that it applies to the force integral. -/
private lemma lambda_rpow_factor (q μ r J : ℝ) (hμ : 0 < μ) (hr : 0 < r) (hq : 0 < q) :
    r ^ (3 - 5 / q) * ((μ ^ (3 * q - 5)) ^ (1 / q) * J ^ (1 / q)) =
      (μ * r) ^ (3 - 5 / q) * J ^ (1 / q) := by
  have hsq : (3 * q - 5) * (1 / q) = 3 - 5 / q := by field_simp
  rw [Real.mul_rpow hμ.le hr.le, ← Real.rpow_mul hμ.le, hsq]
  ring

/-! ### The Dirichlet energy `β` -/

private lemma spatialGradientSq_rescale (μ : ℝ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (w : ParabolicPoint) :
    spatialGradientSq (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du) w =
      μ ^ 4 * spatialGradientSq u Du
        (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)) := by
  simp only [spatialGradientSq, rescaleGradient, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem beta_lintegral_rescale (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3) (r : ℝ) :
    ∫⁻ w in parabolicCylinder 0 0 r,
        ENNReal.ofReal (spatialGradientSq (rescaleVelocity μ z₀ u)
          (rescaleGradient μ z₀ Du) w) =
      ENNReal.ofReal (μ⁻¹) *
        ∫⁻ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
          ENNReal.ofReal (spatialGradientSq u Du w) := by
  have hpt : ∀ w, ENNReal.ofReal (spatialGradientSq (rescaleVelocity μ z₀ u)
        (rescaleGradient μ z₀ Du) w) =
      ENNReal.ofReal (μ ^ 4) * ENNReal.ofReal (spatialGradientSq u Du
        (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w))) := by
    intro w
    rw [spatialGradientSq_rescale, ENNReal.ofReal_mul (by positivity)]
  have hcoef : ENNReal.ofReal (μ ^ 4) * ENNReal.ofReal (μ⁻¹ ^ 5) =
      ENNReal.ofReal (μ⁻¹) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [inv_pow]
    field_simp
  calc
    ∫⁻ w in parabolicCylinder 0 0 r, ENNReal.ofReal
        (spatialGradientSq (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du) w)
        = ∫⁻ w in parabolicCylinder 0 0 r, ENNReal.ofReal (μ ^ 4) *
            ENNReal.ofReal (spatialGradientSq u Du
              (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w))) :=
          lintegral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ENNReal.ofReal (μ ^ 4) * ∫⁻ w in parabolicCylinder 0 0 r,
            ENNReal.ofReal (spatialGradientSq u Du
              (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (μ ^ 4) * (ENNReal.ofReal (μ⁻¹ ^ 5) *
            ∫⁻ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
              ENNReal.ofReal (spatialGradientSq u Du w)) := by
          rw [cylinder_lintegral_comp_parabolicRescale hμ z₀.1 z₀.2 r
            (fun w => ENNReal.ofReal (spatialGradientSq u Du w))]
    _ = ENNReal.ofReal (μ⁻¹) * ∫⁻ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
            ENNReal.ofReal (spatialGradientSq u Du w) := by
          rw [← mul_assoc, hcoef]

/-- Lemma `lem:scaling-quantities`, Dirichlet energy: `β` of the rescaled
solution at the rescaled base point equals `β` of the original solution at the
original base point with the radius scaled by `μ`. -/
theorem beta_rescale (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3) (r : ℝ) :
    beta (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du) ((0 : Vec3), (0 : ℝ)) r =
      beta u Du z₀ (μ * r) := by
  simp only [beta]
  rw [beta_lintegral_rescale μ hμ z₀ u Du r, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ μ⁻¹)]
  refine congrArg (fun y : ℝ => y ^ (1 / 2 : ℝ)) ?_
  rw [mul_inv_rev]
  ring

/-! ### The velocity `L²` energy `α` -/

/-- Scaling of the time-slice ball energy under multiplication of the integrand
by a constant. -/
private lemma timeSliceBallEnergy_const_mul (c : ℝ) (x : Vec3) (r s : ℝ)
    (g : ParabolicPoint → ℝ) :
    timeSliceBallEnergy x r s (fun w => c * g w) =
      ENNReal.ofReal (c ^ 2) * timeSliceBallEnergy x r s g := by
  unfold timeSliceBallEnergy
  have hpoint : ∀ y : Vec3, ‖c * g (y, s)‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (c ^ 2) * ‖g (y, s)‖ₑ ^ (2 : ℝ) := by
    intro y
    simp only [enorm_mul, Real.enorm_eq_ofReal_abs, ENNReal.rpow_ofNat, mul_pow,
      ← ENNReal.ofReal_pow (abs_nonneg c), sq_abs]
  calc
    ∫⁻ y in vec3Ball x r, ‖c * g (y, s)‖ₑ ^ (2 : ℝ)
        = ∫⁻ y in vec3Ball x r,
            ENNReal.ofReal (c ^ 2) * ‖g (y, s)‖ₑ ^ (2 : ℝ) :=
          lintegral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ENNReal.ofReal (c ^ 2) * ∫⁻ y in vec3Ball x r, ‖g (y, s)‖ₑ ^ (2 : ℝ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Pulling a constant multiple out of the time-slice energy essential supremum. -/
private lemma timeSliceEnergyEssSup_const_mul (c : ℝ) (x : Vec3) (t r : ℝ)
    (g : ParabolicPoint → ℝ) :
    timeSliceEnergyEssSup x t r (fun w => c * g w) =
      ENNReal.ofReal (c ^ 2) * timeSliceEnergyEssSup x t r g := by
  unfold timeSliceEnergyEssSup
  simp_rw [timeSliceBallEnergy_const_mul c x r _ g]
  exact ENNReal.essSup_const_mul

/-- Under the parabolic rescaling, the time-slice energy essential supremum of a
constant multiple picks up the spatial Jacobian `μ⁻³` together with the square
`μ²` of the amplitude factor. -/
private theorem timeSliceEnergyEssSup_comp_const_mul (μ : ℝ) (hμ : 0 < μ)
    (x : Vec3) (t r : ℝ) (g : ParabolicPoint → ℝ)
    (hs : Filter.IsBoundedUnder (· ≤ ·) (ae (volume.restrict (Ioc (-r ^ 2) 0)))
      (fun s => timeSliceBallEnergy x (μ * r) (t + μ ^ 2 * s) g))
    (ht : Filter.IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Ioc (t - (μ * r) ^ 2) t)))
      (fun s => timeSliceBallEnergy x (μ * r) s g)) :
    timeSliceEnergyEssSup 0 0 r
        (fun z => (fun w => μ * g w) (parabolicTranslate x t (parabolicScale μ z))) =
      ENNReal.ofReal (μ⁻¹) * timeSliceEnergyEssSup x t (μ * r) g := by
  have hs' : Filter.IsBoundedUnder (· ≤ ·) (ae (volume.restrict (Ioc (-r ^ 2) 0)))
      (fun s => timeSliceBallEnergy x (μ * r) (t + μ ^ 2 * s) (fun w => μ * g w)) := by
    have h := hs.comp (v := fun x => ENNReal.ofReal (μ ^ 2) * x)
      (fun a b hab => mul_le_mul_of_nonneg_left hab
        (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (μ ^ 2)))
    simpa only [Function.comp_def, timeSliceBallEnergy_const_mul] using h
  have ht' : Filter.IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Ioc (t - (μ * r) ^ 2) t)))
      (fun s => timeSliceBallEnergy x (μ * r) s (fun w => μ * g w)) := by
    have h := ht.comp (v := fun x => ENNReal.ofReal (μ ^ 2) * x)
      (fun a b hab => mul_le_mul_of_nonneg_left hab
        (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (μ ^ 2)))
    simpa only [Function.comp_def, timeSliceBallEnergy_const_mul] using h
  have hcomp := timeSliceEnergyEssSup_comp_parabolicRescale (a := μ) hμ x t r
    (fun w => μ * g w) hs' ht'
  have hright : timeSliceEnergyEssSup x t (μ * r) (fun w => μ * g w) =
      ENNReal.ofReal (μ ^ 2) * timeSliceEnergyEssSup x t (μ * r) g :=
    timeSliceEnergyEssSup_const_mul μ x t (μ * r) g
  rw [hcomp, hright, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ μ⁻¹ ^ 3)]
  rw [show μ⁻¹ ^ 3 * μ ^ 2 = μ⁻¹ from inv_cube_mul_sq μ hμ.ne']

/-- Lemma `lem:scaling-quantities`, velocity `L²` energy: `α` of the rescaled
solution at the rescaled base point equals `α` of the original solution at the
original base point with the radius scaled by `μ`.  The two boundedness
hypotheses are those needed to transform the time-slice essential supremum. -/
theorem alpha_rescale (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (r : ℝ)
    (hs : Filter.IsBoundedUnder (· ≤ ·) (ae (volume.restrict (Ioc (-r ^ 2) 0)))
      (fun s => timeSliceBallEnergy z₀.1 (μ * r) (z₀.2 + μ ^ 2 * s)
        (fun w => vec3EuclideanNorm (u w))))
    (ht : Filter.IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Ioc (z₀.2 - (μ * r) ^ 2) z₀.2)))
      (fun s => timeSliceBallEnergy z₀.1 (μ * r) s (fun w => vec3EuclideanNorm (u w)))) :
    alpha (rescaleVelocity μ z₀ u) ((0 : Vec3), (0 : ℝ)) r = alpha u z₀ (μ * r) := by
  simp only [alpha]
  have hnorm : (fun w => vec3EuclideanNorm (rescaleVelocity μ z₀ u w)) =
      fun z => (fun w => μ * vec3EuclideanNorm (u w))
        (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) := by
    funext w
    simp only [rescaleVelocity]
    rw [vec3EuclideanNorm_smul, abs_of_pos hμ]
  rw [hnorm, timeSliceEnergyEssSup_comp_const_mul μ hμ z₀.1 z₀.2 r
      (fun w => vec3EuclideanNorm (u w)) hs ht,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ μ⁻¹)]
  refine congrArg (fun y : ℝ => y ^ (1 / 2 : ℝ)) ?_
  rw [inv_mul_mul]

/-! ### The velocity cubic quantity `γ` -/

/-- Cubing a scaled Euclidean norm, on the `ℝ≥0∞` side: the amplitude `c³`
factors out of the `L³` density of `γ`. -/
private lemma ofReal_vec3EuclideanNorm_smul_rpow_three (c : ℝ) (hc : 0 ≤ c) (v : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm (c • v)) ^ (3 : ℝ) =
      ENNReal.ofReal (c ^ 3) * ENNReal.ofReal (vec3EuclideanNorm v) ^ (3 : ℝ) := by
  rw [vec3EuclideanNorm_smul, abs_of_nonneg hc, ENNReal.ofReal_mul hc,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3)]
  rw [show ENNReal.ofReal c ^ (3 : ℝ) = ENNReal.ofReal (c ^ 3) by
    rw [ENNReal.ofReal_rpow_of_nonneg hc (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num]

private theorem gamma_lintegral_rescale (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (r : ℝ) :
    ∫⁻ w in parabolicCylinder 0 0 r,
        ENNReal.ofReal (vec3EuclideanNorm (rescaleVelocity μ z₀ u w)) ^ (3 : ℝ) =
      ENNReal.ofReal ((μ⁻¹) ^ 2) *
        ∫⁻ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) := by
  have hpt : ∀ w, ENNReal.ofReal (vec3EuclideanNorm (rescaleVelocity μ z₀ u w)) ^ (3 : ℝ) =
      ENNReal.ofReal (μ ^ 3) * ENNReal.ofReal (vec3EuclideanNorm
        (u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)))) ^ (3 : ℝ) := by
    intro w
    simp only [rescaleVelocity]
    exact ofReal_vec3EuclideanNorm_smul_rpow_three μ hμ.le _
  have hcoef : ENNReal.ofReal (μ ^ 3) * ENNReal.ofReal (μ⁻¹ ^ 5) =
      ENNReal.ofReal ((μ⁻¹) ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [inv_pow, inv_pow]
    field_simp
  calc
    ∫⁻ w in parabolicCylinder 0 0 r,
        ENNReal.ofReal (vec3EuclideanNorm (rescaleVelocity μ z₀ u w)) ^ (3 : ℝ)
        = ∫⁻ w in parabolicCylinder 0 0 r, ENNReal.ofReal (μ ^ 3) *
            ENNReal.ofReal (vec3EuclideanNorm
              (u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)))) ^ (3 : ℝ) :=
          lintegral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ENNReal.ofReal (μ ^ 3) * ∫⁻ w in parabolicCylinder 0 0 r,
            ENNReal.ofReal (vec3EuclideanNorm
              (u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)))) ^ (3 : ℝ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (μ ^ 3) * (ENNReal.ofReal (μ⁻¹ ^ 5) *
            ∫⁻ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
              ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) := by
          rw [cylinder_lintegral_comp_parabolicRescale hμ z₀.1 z₀.2 r
            (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))]
    _ = ENNReal.ofReal ((μ⁻¹) ^ 2) * ∫⁻ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
            ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) := by
          rw [← mul_assoc, hcoef]

/-- Lemma `lem:scaling-quantities`, velocity cubic quantity: `γ` of the rescaled
solution at the rescaled base point equals `γ` of the original solution at the
original base point with the radius scaled by `μ`. -/
theorem gamma_rescale (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (r : ℝ) (hr : 0 < r) :
    gamma (rescaleVelocity μ z₀ u) ((0 : Vec3), (0 : ℝ)) r = gamma u z₀ (μ * r) := by
  simp only [gamma]
  rw [gamma_lintegral_rescale μ hμ z₀ u r, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (μ⁻¹) ^ 2)]
  refine congrArg (fun y : ℝ => y ^ (1 / 3 : ℝ)) ?_
  rw [← mul_assoc, rpow_neg_two_mul μ r hμ hr]

/-! ### The pressure quantity `δ` -/

/-- Raising a scaled absolute value to the power `3/2`, on the `ℝ≥0∞` side: the
amplitude `μ³` factors out of the `L^{3/2}` density of `δ`. -/
private lemma ofReal_abs_sq_mul_rpow_three_halves (μ : ℝ) (hμ : 0 < μ) (y : ℝ) :
    ENNReal.ofReal |μ ^ 2 * y| ^ (3 / 2 : ℝ) =
      ENNReal.ofReal (μ ^ 3) * ENNReal.ofReal |y| ^ (3 / 2 : ℝ) := by
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ μ ^ 2),
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ μ ^ 2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  rw [show ENNReal.ofReal (μ ^ 2) ^ (3 / 2 : ℝ) = ENNReal.ofReal (μ ^ 3) by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ μ ^ 2)
      (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    rw [show (μ ^ 2 : ℝ) ^ (3 / 2 : ℝ) = μ ^ 3 by
      rw [← Real.rpow_natCast μ 2, ← Real.rpow_mul hμ.le]
      norm_num]]

private theorem delta_lintegral_rescale (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    (p : ParabolicPoint → ℝ) (r : ℝ) :
    ∫⁻ w in parabolicCylinder 0 0 r,
        ENNReal.ofReal |rescalePressure μ z₀ p w| ^ (3 / 2 : ℝ) =
      ENNReal.ofReal ((μ⁻¹) ^ 2) *
        ∫⁻ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
          ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) := by
  have hpt : ∀ w, ENNReal.ofReal |rescalePressure μ z₀ p w| ^ (3 / 2 : ℝ) =
      ENNReal.ofReal (μ ^ 3) * ENNReal.ofReal
        |p (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w))| ^ (3 / 2 : ℝ) := by
    intro w
    simp only [rescalePressure]
    exact ofReal_abs_sq_mul_rpow_three_halves μ hμ _
  have hcoef : ENNReal.ofReal (μ ^ 3) * ENNReal.ofReal (μ⁻¹ ^ 5) =
      ENNReal.ofReal ((μ⁻¹) ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [inv_pow, inv_pow]
    field_simp
  calc
    ∫⁻ w in parabolicCylinder 0 0 r,
        ENNReal.ofReal |rescalePressure μ z₀ p w| ^ (3 / 2 : ℝ)
        = ∫⁻ w in parabolicCylinder 0 0 r, ENNReal.ofReal (μ ^ 3) *
            ENNReal.ofReal
              |p (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w))| ^ (3 / 2 : ℝ) :=
          lintegral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ENNReal.ofReal (μ ^ 3) * ∫⁻ w in parabolicCylinder 0 0 r,
            ENNReal.ofReal
              |p (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w))| ^ (3 / 2 : ℝ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (μ ^ 3) * (ENNReal.ofReal (μ⁻¹ ^ 5) *
            ∫⁻ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
              ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) := by
          rw [cylinder_lintegral_comp_parabolicRescale hμ z₀.1 z₀.2 r
            (fun w => ENNReal.ofReal |p w| ^ (3 / 2 : ℝ))]
    _ = ENNReal.ofReal ((μ⁻¹) ^ 2) * ∫⁻ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
            ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) := by
          rw [← mul_assoc, hcoef]

/-- Lemma `lem:scaling-quantities`, pressure quantity: `δ` of the rescaled
solution at the rescaled base point equals `δ` of the original solution at the
original base point with the radius scaled by `μ`. -/
theorem delta_rescale (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    (p : ParabolicPoint → ℝ) (r : ℝ) (hr : 0 < r) :
    delta (rescalePressure μ z₀ p) ((0 : Vec3), (0 : ℝ)) r = delta p z₀ (μ * r) := by
  simp only [delta]
  rw [delta_lintegral_rescale μ hμ z₀ p r, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (μ⁻¹) ^ 2)]
  refine congrArg (fun y : ℝ => y ^ (1 / 3 : ℝ)) ?_
  rw [← mul_assoc, rpow_neg_two_mul μ r hμ hr]

/-! ### The force quantity `λ` -/

/-- Raising a scaled Euclidean norm to the power `q`, on the `ℝ≥0∞` side: the
amplitude `μ^{3q}` factors out of the `L^q` density of `λ`. -/
private lemma ofReal_vec3EuclideanNorm_smul_rpow (q μ : ℝ) (hq : 0 ≤ q) (hμ : 0 < μ)
    (v : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm (μ ^ 3 • v)) ^ q =
      ENNReal.ofReal (μ ^ (3 * q)) * ENNReal.ofReal (vec3EuclideanNorm v) ^ q := by
  rw [vec3EuclideanNorm_smul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ μ ^ 3),
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ μ ^ 3),
    ENNReal.mul_rpow_of_nonneg _ _ hq]
  rw [show ENNReal.ofReal (μ ^ 3) ^ q = ENNReal.ofReal (μ ^ (3 * q)) by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ μ ^ 3) hq]
    rw [← Real.rpow_natCast μ 3, ← Real.rpow_mul hμ.le]
    congr 1]

private theorem lambda_lintegral_rescale (q : ℝ) (μ : ℝ) (hq : 0 ≤ q) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (f : ParabolicPoint → Vec3) (r : ℝ) :
    ∫⁻ w in parabolicCylinder 0 0 r,
        ENNReal.ofReal (vec3EuclideanNorm (rescaleForce μ z₀ f w)) ^ q =
      ENNReal.ofReal (μ ^ (3 * q - 5)) *
        ∫⁻ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q := by
  have hpt : ∀ w, ENNReal.ofReal (vec3EuclideanNorm (rescaleForce μ z₀ f w)) ^ q =
      ENNReal.ofReal (μ ^ (3 * q)) * ENNReal.ofReal (vec3EuclideanNorm
        (f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)))) ^ q := by
    intro w
    simp only [rescaleForce]
    exact ofReal_vec3EuclideanNorm_smul_rpow q μ hq hμ _
  have hcoef : ENNReal.ofReal (μ ^ (3 * q)) * ENNReal.ofReal (μ⁻¹ ^ 5) =
      ENNReal.ofReal (μ ^ (3 * q - 5)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    exact rpow_three_q_mul_inv_pow_five q μ hμ
  calc
    ∫⁻ w in parabolicCylinder 0 0 r,
        ENNReal.ofReal (vec3EuclideanNorm (rescaleForce μ z₀ f w)) ^ q
        = ∫⁻ w in parabolicCylinder 0 0 r, ENNReal.ofReal (μ ^ (3 * q)) *
            ENNReal.ofReal (vec3EuclideanNorm
              (f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)))) ^ q :=
          lintegral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ENNReal.ofReal (μ ^ (3 * q)) * ∫⁻ w in parabolicCylinder 0 0 r,
            ENNReal.ofReal (vec3EuclideanNorm
              (f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)))) ^ q :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (μ ^ (3 * q)) * (ENNReal.ofReal (μ⁻¹ ^ 5) *
            ∫⁻ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
              ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) := by
          rw [cylinder_lintegral_comp_parabolicRescale hμ z₀.1 z₀.2 r
            (fun w => ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q)]
    _ = ENNReal.ofReal (μ ^ (3 * q - 5)) * ∫⁻ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
            ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q := by
          rw [← mul_assoc, hcoef]

/-- Lemma `lem:scaling-quantities`, force quantity: `λ` of the rescaled force at
the rescaled base point equals `λ` of the original force at the original base
point with the radius scaled by `μ`, at the same exponent `q`. -/
theorem lambda_rescale (q : ℝ) (μ : ℝ) (hq : 0 < q) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (f : ParabolicPoint → Vec3) (r : ℝ) (hr : 0 < r) :
    lambda q (rescaleForce μ z₀ f) ((0 : Vec3), (0 : ℝ)) r = lambda q f z₀ (μ * r) := by
  simp only [lambda]
  rw [lambda_lintegral_rescale q μ hq.le hμ z₀ f r, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ μ ^ (3 * q - 5)),
    Real.mul_rpow (Real.rpow_nonneg hμ.le _) ENNReal.toReal_nonneg]
  exact lambda_rpow_factor q μ r _ hμ hr hq

/-! ### The iteration quantity `θ` -/

/-- Lemma `lem:scaling-quantities`, iteration quantity: `θ` of the rescaled
solution at the rescaled base point equals `θ` of the original solution at the
original base point with the radius scaled by `μ`, as the sum of the rescaled
`α`, `β` and `δ`. -/
theorem theta_rescale (κ μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (r : ℝ) (hr : 0 < r)
    (hs : Filter.IsBoundedUnder (· ≤ ·) (ae (volume.restrict (Ioc (-r ^ 2) 0)))
      (fun s => timeSliceBallEnergy z₀.1 (μ * r) (z₀.2 + μ ^ 2 * s)
        (fun w => vec3EuclideanNorm (u w))))
    (ht : Filter.IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Ioc (z₀.2 - (μ * r) ^ 2) z₀.2)))
      (fun s => timeSliceBallEnergy z₀.1 (μ * r) s (fun w => vec3EuclideanNorm (u w)))) :
    theta κ (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
        (rescalePressure μ z₀ p) ((0 : Vec3), (0 : ℝ)) r =
      theta κ u Du p z₀ (μ * r) := by
  simp only [theta]
  rw [alpha_rescale μ hμ z₀ u r hs ht, beta_rescale μ hμ z₀ u Du r,
    delta_rescale μ hμ z₀ p r hr]

end CKN

end
