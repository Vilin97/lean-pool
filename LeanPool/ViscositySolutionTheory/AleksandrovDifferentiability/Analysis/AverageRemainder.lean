/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.OneDimConvex
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Averaged one-dimensional remainders

This file begins the interval-integral route to the remaining one-dimensional averaging lemma.
The first named fact records the exact integral of the linear model that will appear after
linearizing the right derivative.
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter Set
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Local interval-integral representation of the affine remainder using the project-local right
derivative increment. For convex functions this should follow from FTC for one-sided derivatives. -/
def HasRightDerivIntegralRemainderAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ᶠ z in nhds 0,
    f (x + z) - f x - rightDeriv f x * z =
      ∫ t in x..x + z, rightDeriv f t - rightDeriv f x

/-- The integral of the right-derivative increment is locally modeled by the integral of the
linearized derivative increment. This is the estimate supplied by differentiability of
`rightDeriv f` once interval-integral bounds are available. -/
def HasRightDerivIntegralLinearizationAt (f : ℝ → ℝ) (x q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ z in nhds 0,
      ‖(∫ t in x..x + z, rightDeriv f t - rightDeriv f x) -
        ∫ t in x..x + z, q * (t - x)‖ ≤ ε * ‖z‖ ^ 2

/-- If `U` is a neighborhood of `x`, then every sufficiently short interval from `x` to `x + z`
is contained in `U`. -/
theorem eventually_uIcc_subset_of_mem_nhds {x : ℝ} {U : Set ℝ} (hU : U ∈ nhds x) :
    ∀ᶠ z in nhds 0, Set.uIcc x (x + z) ⊆ U := by
  rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδpos, hδsub⟩
  have hsmall : ∀ᶠ z : ℝ in nhds (0 : ℝ), ‖z‖ < δ := by
    filter_upwards [(Metric.ball_mem_nhds (0 : ℝ) hδpos :
      Metric.ball (0 : ℝ) δ ∈ nhds (0 : ℝ))] with z hz
    simpa [Metric.mem_ball, Real.dist_eq, Real.norm_eq_abs] using hz
  filter_upwards [hsmall] with z hz t ht
  refine hδsub ?_
  rw [Metric.mem_ball, Real.dist_eq]
  have ht_le : |t - x| ≤ |x + z - x| :=
    abs_sub_left_of_mem_uIcc ht
  have ht_lt : |t - x| < δ := by
    exact lt_of_le_of_lt ht_le (by simpa [Real.norm_eq_abs] using hz)
  simpa [Real.dist_eq] using ht_lt

/-- Integral of the affine derivative model along the interval from `x` to `x + z`. -/
theorem intervalIntegral_linear_deriv_model (x z q : ℝ) :
    ∫ t in x..x + z, q * (t - x) = (1 / 2 : ℝ) * q * z ^ 2 := by
  let F : ℝ → ℝ := fun t => (1 / 2 : ℝ) * q * (t - x) ^ 2
  have hderiv : ∀ t ∈ Set.uIcc x (x + z), HasDerivAt F (q * (t - x)) t := by
    intro t ht
    have hpow : HasDerivAt (fun t : ℝ => (t - x) ^ 2) (2 * (t - x)) t := by
      convert ((hasDerivAt_id t).sub_const x).mul
        ((hasDerivAt_id t).sub_const x) using 1
      · funext y
        simp [Pi.mul_apply, pow_two]
      · simp only [id_eq]
        ring
    have hscaled := hpow.const_mul ((1 / 2 : ℝ) * q)
    simpa [F, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hint : IntervalIntegrable (fun t : ℝ => q * (t - x)) volume x (x + z) := by
    exact (by fun_prop : Continuous fun t : ℝ => q * (t - x)).intervalIntegrable x (x + z)
  have hFTC :
      ∫ t in x..x + z, q * (t - x) = F (x + z) - F x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC]
  simp [F]

/-- If an integrand on `[0,1]` is uniformly close to the affine model `a + t q`, then its
integral is close to `a + q / 2`.

This is the calculus bookkeeping in the source proof's final line-segment integration: once the
right derivative of the line restriction is controlled by the linear model, the endpoint
increment has the corresponding quadratic model. -/
theorem norm_unit_interval_remainder_le_of_integral_model_bound
    {f g : ℝ → ℝ} {a q R : ℝ}
    (hrepr : f 1 - f 0 = ∫ t in (0 : ℝ)..1, g t)
    (hint : IntervalIntegrable g volume (0 : ℝ) 1)
    (hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖g t - (a + t * q)‖ ≤ R) :
    ‖f 1 - f 0 - a - (1 / 2 : ℝ) * q‖ ≤ R := by
  let model : ℝ → ℝ := fun t => a + q * (t - 0)
  have hmodel_int : IntervalIntegrable model volume (0 : ℝ) 1 := by
    exact (by fun_prop : Continuous model).intervalIntegrable 0 1
  have hmodel_integral :
      (∫ t in (0 : ℝ)..1, model t) = a + (1 / 2 : ℝ) * q := by
    have hlin : IntervalIntegrable (fun t : ℝ => q * (t - 0)) volume (0 : ℝ) 1 := by
      exact (by fun_prop : Continuous fun t : ℝ => q * (t - 0)).intervalIntegrable 0 1
    rw [show model = fun t : ℝ => a + q * (t - 0) by rfl]
    rw [intervalIntegral.integral_add intervalIntegrable_const hlin]
    have hq : (∫ t in (0 : ℝ)..1, q * (t - 0)) = (1 / 2 : ℝ) * q := by
      simpa using intervalIntegral_linear_deriv_model (0 : ℝ) (1 : ℝ) q
    rw [hq]
    simp
  have hdiff :
      f 1 - f 0 - a - (1 / 2 : ℝ) * q =
        ∫ t in (0 : ℝ)..1, g t - model t := by
    rw [hrepr]
    rw [intervalIntegral.integral_sub hint hmodel_int]
    rw [hmodel_integral]
    ring
  calc
    ‖f 1 - f 0 - a - (1 / 2 : ℝ) * q‖
        = ‖∫ t in (0 : ℝ)..1, g t - model t‖ := by rw [hdiff]
    _ ≤ R * |(1 : ℝ) - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro t ht
        simpa [model, mul_comm] using hbound t ht
    _ = R := by simp

/-- Differentiability of the project-local right derivative controls the endpoint average of its
increment by the linear model. -/
theorem eventually_norm_half_rightDeriv_increment_sub_linear_model_le
    {S : Set ℝ} {f : ℝ → ℝ} {x q : ℝ}
    (hx : x ∈ interior S) (hderiv : HasDerivWithinAt (rightDeriv f) q (interior S) x) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖(1 / 2 : ℝ) * (rightDeriv f (x + z) - rightDeriv f x) * z -
          (1 / 2 : ℝ) * q * z ^ 2‖ ≤ ε * ‖z‖ ^ 2 := by
  intro ε hε
  have hεtwo : 0 < 2 * ε := by positivity
  have hto_nhds :
      Filter.Tendsto (fun z : ℝ => x + z) (nhds 0) (nhds x) := by
    simpa using (tendsto_const_nhds.add Filter.tendsto_id :
      Filter.Tendsto (fun z : ℝ => x + z) (nhds 0) (nhds (x + 0)))
  have hmem :
      ∀ᶠ z in nhds 0, x + z ∈ interior S :=
    hto_nhds (isOpen_interior.mem_nhds hx)
  have hto_within :
      Filter.Tendsto (fun z : ℝ => x + z) (nhds 0) (nhdsWithin x (interior S)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hto_nhds, hmem⟩
  have hderiv_comp :
      (fun z : ℝ => rightDeriv f (x + z) - rightDeriv f x - q * z)
        =o[nhds 0] fun z : ℝ => z := by
    have hcomp := hderiv.isLittleO.comp_tendsto hto_within
    simpa [Function.comp_def, mul_comm] using hcomp
  have hderiv_bound :
      ∀ᶠ z in nhds 0,
        ‖rightDeriv f (x + z) - rightDeriv f x - q * z‖ ≤ (2 * ε) * ‖z‖ := by
    simpa using hderiv_comp.def hεtwo
  filter_upwards [hderiv_bound] with z hz
  have hsplit :
      (1 / 2 : ℝ) * (rightDeriv f (x + z) - rightDeriv f x) * z -
          (1 / 2 : ℝ) * q * z ^ 2 =
        (1 / 2 : ℝ) * (rightDeriv f (x + z) - rightDeriv f x - q * z) * z := by
    ring
  rw [hsplit]
  calc
    ‖(1 / 2 : ℝ) * (rightDeriv f (x + z) - rightDeriv f x - q * z) * z‖ =
        ‖(1 / 2 : ℝ)‖ *
          ‖rightDeriv f (x + z) - rightDeriv f x - q * z‖ * ‖z‖ := by
      simp [norm_mul, mul_assoc]
    _ ≤ ‖(1 / 2 : ℝ)‖ * ((2 * ε) * ‖z‖) * ‖z‖ := by
      gcongr
    _ = ε * ‖z‖ ^ 2 := by
      simp only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      nlinarith [sq_abs z]

/-- Near an interior point of a one-dimensional convex domain, the project-local right derivative
is interval-integrable on the small interval from `x` to `x + z`. -/
theorem ConvexOn.eventually_intervalIntegrable_rightDeriv
    {S : Set ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    ∀ᶠ z in nhds 0, IntervalIntegrable (rightDeriv f) volume x (x + z) := by
  have hmono : MonotoneOn (rightDeriv f) (interior S) :=
    AleksandrovDifferentiability.ConvexOn.monotoneOn_projectRightDeriv
      (S := S) (f := f) hf
  have hinterval :
      ∀ᶠ z in nhds 0, Set.uIcc x (x + z) ⊆ interior S :=
    eventually_uIcc_subset_of_mem_nhds (isOpen_interior.mem_nhds hx)
  filter_upwards [hinterval] with z hz
  have hmono_interval : MonotoneOn (rightDeriv f) (Set.uIcc x (x + z)) := by
    intro a ha b hb hab
    exact hmono (hz ha) (hz hb) hab
  exact hmono_interval.intervalIntegrable

/-- If the whole interval between `a` and `b` lies in the interior of a one-dimensional convex
domain, then the right derivative is interval-integrable on that interval. -/
theorem ConvexOn.intervalIntegrable_rightDeriv_of_uIcc_subset_interior
    {S : Set ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hf : ConvexOn ℝ S f) (hinterval : Set.uIcc a b ⊆ interior S) :
    IntervalIntegrable (rightDeriv f) volume a b := by
  have hmono : MonotoneOn (rightDeriv f) (interior S) :=
    AleksandrovDifferentiability.ConvexOn.monotoneOn_projectRightDeriv
      (S := S) (f := f) hf
  have hmono_interval : MonotoneOn (rightDeriv f) (Set.uIcc a b) := by
    intro x hx y hy hxy
    exact hmono (hinterval hx) (hinterval hy) hxy
  exact hmono_interval.intervalIntegrable

/-- Local right-derivative FTC identity for a one-dimensional convex function at an interior
point. -/
theorem ConvexOn.eventually_integral_rightDeriv_eq_sub
    {S : Set ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    ∀ᶠ z in nhds 0, ∫ t in x..x + z, rightDeriv f t = f (x + z) - f x := by
  have hinterval :
      ∀ᶠ z in nhds 0, Set.uIcc x (x + z) ⊆ interior S :=
    eventually_uIcc_subset_of_mem_nhds (isOpen_interior.mem_nhds hx)
  filter_upwards [
    AleksandrovDifferentiability.ConvexOn.eventually_intervalIntegrable_rightDeriv
      (S := S) (f := f) (x := x) hf hx,
    hinterval] with z hint_z hinterval_z
  have hcont : ContinuousOn f (Set.uIcc x (x + z)) :=
    hf.continuousOn_interior.mono hinterval_z
  have hderiv :
      ∀ t ∈ Set.Ioo (min x (x + z)) (max x (x + z)),
        HasDerivWithinAt f (rightDeriv f t) (Set.Ioi t) t := by
    intro t ht
    exact AleksandrovDifferentiability.ConvexOn.hasDerivWithinAt_rightDeriv
      (S := S) (f := f) (x := t) hf (hinterval_z (Set.Ioo_subset_Icc_self ht))
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint_z

/-- Right-derivative FTC identity on any interval contained in the interior of a
one-dimensional convex domain. -/
theorem ConvexOn.integral_rightDeriv_eq_sub_of_uIcc_subset_interior
    {S : Set ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hf : ConvexOn ℝ S f) (hinterval : Set.uIcc a b ⊆ interior S) :
    ∫ t in a..b, rightDeriv f t = f b - f a := by
  have hint :
      IntervalIntegrable (rightDeriv f) volume a b :=
    ConvexOn.intervalIntegrable_rightDeriv_of_uIcc_subset_interior
      (S := S) (f := f) hf hinterval
  have hcont : ContinuousOn f (Set.uIcc a b) :=
    hf.continuousOn_interior.mono hinterval
  have hderiv :
      ∀ t ∈ Set.Ioo (min a b) (max a b),
        HasDerivWithinAt f (rightDeriv f t) (Set.Ioi t) t := by
    intro t ht
    exact AleksandrovDifferentiability.ConvexOn.hasDerivWithinAt_rightDeriv
      (S := S) (f := f) (x := t) hf (hinterval (Set.Ioo_subset_Icc_self ht))
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint

/-- Local affine-remainder integral representation for a one-dimensional convex function at an
interior point. -/
theorem ConvexOn.hasRightDerivIntegralRemainderAt
    {S : Set ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    HasRightDerivIntegralRemainderAt f x := by
  filter_upwards [
    AleksandrovDifferentiability.ConvexOn.eventually_integral_rightDeriv_eq_sub
      (S := S) (f := f) (x := x) hf hx,
    AleksandrovDifferentiability.ConvexOn.eventually_intervalIntegrable_rightDeriv
      (S := S) (f := f) (x := x) hf hx] with z hftc hint_z
  have hconst :
      ∫ t in x..x + z, (rightDeriv f x : ℝ) = rightDeriv f x * z := by
    simp [sub_eq_add_neg, mul_comm]
  calc
    f (x + z) - f x - rightDeriv f x * z
        = (∫ t in x..x + z, rightDeriv f t) - ∫ t in x..x + z, (rightDeriv f x : ℝ) := by
      rw [hftc, hconst]
    _ = ∫ t in x..x + z, rightDeriv f t - rightDeriv f x := by
      rw [intervalIntegral.integral_sub
        hint_z intervalIntegrable_const]

/-- Differentiability of `rightDeriv f`, together with local interval integrability of
`rightDeriv f`, gives the integral linearization estimate. The extra integrability hypothesis is
the part later supplied by convexity, via monotonicity of one-sided derivatives. -/
theorem hasRightDerivIntegralLinearizationAt_of_hasDerivWithinAt_of_eventually_intervalIntegrable
    {S : Set ℝ} {f : ℝ → ℝ} {x q : ℝ}
    (hx : x ∈ interior S)
    (hderiv : HasDerivWithinAt (rightDeriv f) q (interior S) x)
    (hint : ∀ᶠ z in nhds 0, IntervalIntegrable (rightDeriv f) volume x (x + z)) :
    HasRightDerivIntegralLinearizationAt f x q := by
  intro ε hε
  let P : Set ℝ :=
    {t | ‖rightDeriv f t - rightDeriv f x - q * (t - x)‖ ≤ ε * ‖t - x‖}
  have hP_within : P ∈ nhdsWithin x (interior S) := by
    change ∀ᶠ t in nhdsWithin x (interior S),
      ‖rightDeriv f t - rightDeriv f x - q * (t - x)‖ ≤ ε * ‖t - x‖
    simpa [Real.norm_eq_abs, mul_comm] using hderiv.isLittleO.def hε
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hP_within with ⟨U, hU, hUsub⟩
  have hinterior_mem : interior S ∈ nhds x :=
    isOpen_interior.mem_nhds hx
  have hinterval :
      ∀ᶠ z in nhds 0, Set.uIcc x (x + z) ⊆ U ∩ interior S :=
    eventually_uIcc_subset_of_mem_nhds (inter_mem hU hinterior_mem)
  filter_upwards [hint, hinterval] with z hint_z hinterval_z
  have hrdinc_int :
      IntervalIntegrable (fun t : ℝ => rightDeriv f t - rightDeriv f x) volume x (x + z) :=
    hint_z.sub intervalIntegrable_const
  have hmodel_int :
      IntervalIntegrable (fun t : ℝ => q * (t - x)) volume x (x + z) := by
    exact (by fun_prop : Continuous fun t : ℝ => q * (t - x)).intervalIntegrable x (x + z)
  have hbound :
      ∀ t ∈ Set.uIoc x (x + z),
        ‖(rightDeriv f t - rightDeriv f x) - q * (t - x)‖ ≤ ε * ‖z‖ := by
    intro t ht
    have htucc : t ∈ Set.uIcc x (x + z) :=
      Set.uIoc_subset_uIcc ht
    have htP : t ∈ P :=
      hUsub (hinterval_z htucc)
    have ht_norm_le : ‖t - x‖ ≤ ‖z‖ := by
      have ht_abs : |t - x| ≤ |x + z - x| :=
        abs_sub_left_of_mem_uIcc htucc
      simpa [Real.norm_eq_abs] using ht_abs
    exact htP.trans (mul_le_mul_of_nonneg_left ht_norm_le hε.le)
  calc
    ‖(∫ t in x..x + z, rightDeriv f t - rightDeriv f x) -
        ∫ t in x..x + z, q * (t - x)‖ =
        ‖∫ t in x..x + z, (rightDeriv f t - rightDeriv f x) - q * (t - x)‖ := by
      rw [intervalIntegral.integral_sub hrdinc_int hmodel_int]
    _ ≤ (ε * ‖z‖) * |x + z - x| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ε * ‖z‖ ^ 2 := by
      simp [Real.norm_eq_abs, pow_two, mul_assoc]

/-- For a one-dimensional convex function, differentiability of the project-local right derivative
within the interior gives the integral linearization estimate. -/
theorem ConvexOn.hasRightDerivIntegralLinearizationAt_of_hasDerivWithinAt
    {S : Set ℝ} {f : ℝ → ℝ} {x q : ℝ}
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hderiv : HasDerivWithinAt (rightDeriv f) q (interior S) x) :
    HasRightDerivIntegralLinearizationAt f x q :=
  hasRightDerivIntegralLinearizationAt_of_hasDerivWithinAt_of_eventually_intervalIntegrable
    (S := S) (f := f) (x := x) (q := q) hx hderiv
    (AleksandrovDifferentiability.ConvexOn.eventually_intervalIntegrable_rightDeriv
      (S := S) (f := f) (x := x) hf hx)

/-- If the affine remainder has the interval-integral representation and that integral is
quadratically close to the linearized right-derivative model, then differentiability of the right
derivative gives the averaged endpoint-remainder estimate. -/
theorem hasRightDerivAverageRemainderAt_of_integral_linearization
    {S : Set ℝ} {f : ℝ → ℝ} {x q : ℝ}
    (hx : x ∈ interior S)
    (hrepr : HasRightDerivIntegralRemainderAt f x)
    (hlin : HasRightDerivIntegralLinearizationAt f x q)
    (hderiv : HasDerivWithinAt (rightDeriv f) q (interior S) x) :
    HasRightDerivAverageRemainderAt f x := by
  intro ε hε
  have hεhalf : 0 < ε / 2 := by positivity
  have hend :=
    eventually_norm_half_rightDeriv_increment_sub_linear_model_le
      (S := S) (f := f) (x := x) (q := q) hx hderiv (ε / 2) hεhalf
  filter_upwards [hrepr, hlin (ε / 2) hεhalf, hend] with z hrepr_z hlin_z hend_z
  let I : ℝ := ∫ t in x..x + z, rightDeriv f t - rightDeriv f x
  let M : ℝ := (1 / 2 : ℝ) * q * z ^ 2
  let E : ℝ := (1 / 2 : ℝ) * (rightDeriv f (x + z) - rightDeriv f x) * z
  have hlin_z' : ‖I - M‖ ≤ (ε / 2) * ‖z‖ ^ 2 := by
    rw [intervalIntegral_linear_deriv_model x z q] at hlin_z
    simpa [I, M] using hlin_z
  have hend_z' : ‖E - M‖ ≤ (ε / 2) * ‖z‖ ^ 2 := by
    simpa [E, M] using hend_z
  have hsplit :
      f (x + z) - f x - rightDeriv f x * z -
          (1 / 2 : ℝ) * (rightDeriv f (x + z) - rightDeriv f x) * z =
        (I - M) - (E - M) := by
    rw [hrepr_z]
    simp [I, M, E]
  calc
    ‖f (x + z) - f x - rightDeriv f x * z -
        (1 / 2 : ℝ) * (rightDeriv f (x + z) - rightDeriv f x) * z‖ =
        ‖(I - M) - (E - M)‖ := by rw [hsplit]
    _ ≤ ‖I - M‖ + ‖E - M‖ := norm_sub_le (I - M) (E - M)
    _ ≤ (ε / 2) * ‖z‖ ^ 2 + (ε / 2) * ‖z‖ ^ 2 :=
      add_le_add hlin_z' hend_z'
    _ = ε * ‖z‖ ^ 2 := by ring

/-- For a convex one-dimensional function, the local affine-remainder integral representation
is the only remaining ingredient needed to obtain the averaged right-derivative remainder
estimate at points where the right derivative is differentiable within the interior. -/
theorem ConvexOn.hasRightDerivAverageRemainderAt_of_integralRemainder_of_hasDerivWithinAt
    {S : Set ℝ} {f : ℝ → ℝ} {x q : ℝ}
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hrepr : HasRightDerivIntegralRemainderAt f x)
    (hderiv : HasDerivWithinAt (rightDeriv f) q (interior S) x) :
    HasRightDerivAverageRemainderAt f x :=
  hasRightDerivAverageRemainderAt_of_integral_linearization
    (S := S) (f := f) (x := x) (q := q) hx hrepr
    (AleksandrovDifferentiability.ConvexOn.hasRightDerivIntegralLinearizationAt_of_hasDerivWithinAt
      (S := S) (f := f) (x := x) (q := q) hf hx hderiv)
    hderiv

/-- Derivative-good points of a convex one-dimensional function satisfy the averaged
right-derivative remainder estimate once the local affine-remainder integral representation is
known there. -/
theorem ConvexOn.hasRightDerivAverageRemainderAt_of_good_of_integralRemainder
    {S : Set ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hgood : x ∈ oneSidedDerivDifferentiabilitySet S f)
    (hrepr : HasRightDerivIntegralRemainderAt f x) :
    HasRightDerivAverageRemainderAt f x :=
  ConvexOn.hasRightDerivAverageRemainderAt_of_integralRemainder_of_hasDerivWithinAt
    (S := S) (f := f) (x := x)
    (q := derivWithin (rightDeriv f) (interior S) x) hf hx hrepr hgood.1.hasDerivWithinAt

end AleksandrovDifferentiability
