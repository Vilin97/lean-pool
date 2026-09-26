/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBridge
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The tensor `U` built from a mean-free velocity field

This file records the tensor that `paper/ckn.tex` attaches to the local energy
class in the proof of Lemma `lem:U-bounds` (equation `eq:Uij`): at a point
`y` of the spatial ball `B_ρ = vec3Ball x₀ ρ` and at time `t`,

`U_ij(y,t) = -u_i(y,t) * (u_j(y,t) - ⨍_{B_ρ} u_j(·,t))`,

where the second factor is the mean-free part of the velocity field, averaged
in space over `B_ρ` with `MeasureTheory.average`.  Writing

`|U| = (∑_{i,j} U_ij²)^{1/2}`,

the main result `U_bounds_of_sobolevPoincare` is the two displays
`eq:U-bounds` of the paper:

* `(∫_{B_ρ} |U|^{3/2})^{2/3} ≤ C₅ · 𝔲(t) · 𝔤(t)`;
* `∫_{B_ρ} |U| ≤ (4π/3)^{1/3} C₅ ρ · 𝔲(t) · 𝔤(t)`,

with `𝔲(t) = (∫_{B_ρ} |u(·,t)|²)^{1/2}` and
`𝔤(t) = (∫_{B_ρ} |∇u(·,t)|²)^{1/2}`.  The only analytic input is the
same-ball `L⁶` Sobolev–Poincaré inequality (equation
`eq:sobolev-poincare-6`), taken as an explicit hypothesis on the mean-free
field; everything else is the pointwise rank-one identity `|U| = |u| |v|`,
Hölder's inequality, and the volume of `B_ρ`.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


namespace CKN

noncomputable section

/-- The `j`-th component of `u(·,t)` with its spatial average over
`B_ρ = vec3Ball x₀ ρ` subtracted, the mean-free component appearing in
equation `eq:Uij` of `paper/ckn.tex`. -/
@[expose]
def meanFreeComponent (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ : ℝ) (t : ℝ)
    (j : Fin 3) (y : Vec3) : ℝ :=
  u (y, t) j - MeasureTheory.average
    (MeasureTheory.volume.restrict (vec3Ball x₀ ρ)) (fun z => u (z, t) j)

/-- The mean-free velocity `v = u(·,t) - ⨍_{B_ρ} u(·,t)` of equation
`eq:Uij` in `paper/ckn.tex`. -/
@[expose]
def meanFreeVec (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ : ℝ) (t : ℝ)
    (y : Vec3) : Vec3 :=
  fun j => meanFreeComponent u x₀ ρ t j y

/-- The rank-one tensor `U_ij = -u_i (u_j - ⨍_{B_ρ} u_j)` of equation
`eq:Uij` in `paper/ckn.tex`. -/
@[expose]
def utensor (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ t : ℝ) (i j : Fin 3)
    (y : Vec3) : ℝ :=
  - u (y, t) i * meanFreeComponent u x₀ ρ t j y

/-- The pointwise norm `|U| = (∑_{i,j} U_ij²)^{1/2}` of the tensor of
equation `eq:Uij` in `paper/ckn.tex`. -/
@[expose]
def utensorNorm (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ t : ℝ) (y : Vec3) : ℝ :=
  Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, (utensor u x₀ ρ t i j y) ^ (2 : ℕ))

/-- `U` is rank one: `|U|` is the product of the norms of `u(·,t)` and of its
mean-free part.  This is the pointwise identity used in `eq:U-bounds`. -/
theorem utensorNorm_eq (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ t : ℝ)
    (y : Vec3) :
    utensorNorm u x₀ ρ t y =
      vec3EuclideanNorm (u (y, t)) * vec3EuclideanNorm (meanFreeVec u x₀ ρ t y) := by
  have hsq : ∑ i : Fin 3, ∑ j : Fin 3, (utensor u x₀ ρ t i j y) ^ (2 : ℕ) =
      (∑ i : Fin 3, (u (y, t) i) ^ (2 : ℕ)) *
        (∑ j : Fin 3, (meanFreeVec u x₀ ρ t y j) ^ (2 : ℕ)) := by
    simp only [utensor, meanFreeVec, meanFreeComponent, neg_mul, neg_sq, mul_pow]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  rw [utensorNorm, vec3EuclideanNorm, vec3EuclideanNorm, hsq]
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg (u (y, t) i)))]

/-- The Euclidean norm on `Vec3` is continuous. -/
private theorem continuous_vec3EuclideanNorm :
    Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
  unfold vec3EuclideanNorm
  fun_prop

/-- The triangle inequality for `vec3EuclideanNorm`, transported from the
`L²` norm on `WithLp 2`. -/
private lemma vec3EuclideanNorm_sub_le (a b : Vec3) :
    vec3EuclideanNorm (a - b) ≤ vec3EuclideanNorm a + vec3EuclideanNorm b := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    WithLp.toLp_sub]
  exact norm_sub_le _ _

/-- The lower integral of the `ofReal` of a nonnegative function is finite
when the function lies in the corresponding `Lᵖ` space.  This is the bridge
between the `MemLp` hypotheses of `eq:U-bounds` and the finiteness hypotheses
of Hölder's inequality. -/
private lemma lintegral_ofReal_rpow_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} {p : ℝ} (hp : 0 < p) (hg0 : ∀ y, 0 ≤ g y)
    (hg : MemLp g (ENNReal.ofReal p) μ) :
    ∫⁻ y, ENNReal.ofReal (g y) ^ p ∂μ < ⊤ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hp
  have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 ENNReal.ofReal_ne_top
    hg.aestronglyMeasurable).mp hg.eLpNorm_lt_top
  rw [ENNReal.toReal_ofReal hp.le] at h
  have heq : ∫⁻ y, ‖g y‖ₑ ^ p ∂μ = ∫⁻ y, ENNReal.ofReal (g y) ^ p ∂μ := by
    apply lintegral_congr
    intro y
    rw [← ofReal_norm (g y), Real.norm_of_nonneg (hg0 y)]
  rwa [heq] at h

/-- `ofReal` of a Bochner integral of a nonnegative function is the lower
integral of the `ofReal` of that function, when the latter is finite. -/
private lemma ofReal_integral_eq_lintegral {μ : Measure Vec3} {f : Vec3 → ℝ}
    (hf0 : ∀ y, 0 ≤ f y) (hfm : AEStronglyMeasurable f μ)
    (hfin : ∫⁻ y, ENNReal.ofReal (f y) ∂μ ≠ ⊤) :
    ENNReal.ofReal (∫ y, f y ∂μ) = ∫⁻ y, ENNReal.ofReal (f y) ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfm,
    ENNReal.ofReal_toReal hfin]

/-- The lower integral of `ofReal f ^ n` is the `ofReal` of the Bochner
integral of `f ^ n`, for a nonnegative `f` and a natural exponent `n`. -/
private lemma lintegral_ofReal_pow_eq_ofReal_integral {μ : Measure Vec3} {f : Vec3 → ℝ}
    (hf0 : ∀ y, 0 ≤ f y) (hfm : AEMeasurable f μ) (n : ℕ)
    (hfin : ∫⁻ y, ENNReal.ofReal (f y) ^ ((n : ℝ)) ∂μ < ⊤) :
    ∫⁻ y, ENNReal.ofReal (f y) ^ ((n : ℝ)) ∂μ =
      ENNReal.ofReal (∫ y, f y ^ n ∂μ) := by
  have hcongr : ∫⁻ y, ENNReal.ofReal (f y) ^ ((n : ℝ)) ∂μ =
      ∫⁻ y, ENNReal.ofReal (f y ^ n) ∂μ := by
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_rpow_of_nonneg (hf0 y) (by positivity), Real.rpow_natCast]
  rw [hcongr]
  exact (ofReal_integral_eq_lintegral (fun y => pow_nonneg (hf0 y) n)
    ((hfm.pow_const n).aestronglyMeasurable)
    (by rw [← hcongr]; exact hfin.ne)).symm

/-- Hölder's inequality in lower-integral form, with the exponents `3/4` and
`1/4` that produce the `3/2` powers of `eq:U-bounds`: the `ofReal` of
`(f g)^{3/2}` is bounded by the `3/4`- and `1/4`-powers of the corresponding
`L²` and `L⁶` lower integrals. -/
private lemma lintegral_rpow_three_halves_le {μ : Measure Vec3} {f g : Vec3 → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf0 : ∀ y, 0 ≤ f y) (hg0 : ∀ y, 0 ≤ g y) :
    ∫⁻ y, ENNReal.ofReal ((f y * g y) ^ (3 / 2 : ℝ)) ∂μ ≤
      (∫⁻ y, ENNReal.ofReal (f y) ^ (2 : ℝ) ∂μ) ^ (3 / 4 : ℝ) *
        (∫⁻ y, ENNReal.ofReal (g y) ^ (6 : ℝ) ∂μ) ^ (1 / 4 : ℝ) := by
  have hf' : AEMeasurable (fun y => ENNReal.ofReal (f y) ^ (2 : ℝ)) μ :=
    (hf.ennreal_ofReal).pow_const 2
  have hg' : AEMeasurable (fun y => ENNReal.ofReal (g y) ^ (6 : ℝ)) μ :=
    (hg.ennreal_ofReal).pow_const 6
  have hHolder := ENNReal.lintegral_mul_norm_pow_le hf' hg'
    (show (0 : ℝ) ≤ 3 / 4 by norm_num) (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (show (3 : ℝ) / 4 + 1 / 4 = 1 by norm_num)
  have hpoint : ∀ y, (ENNReal.ofReal (f y) ^ (2 : ℝ)) ^ (3 / 4 : ℝ) *
      (ENNReal.ofReal (g y) ^ (6 : ℝ)) ^ (1 / 4 : ℝ) =
      ENNReal.ofReal ((f y * g y) ^ (3 / 2 : ℝ)) := by
    intro y
    have hx0 : 0 ≤ f y * g y := mul_nonneg (hf0 y) (hg0 y)
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num,
      show (6 : ℝ) * (1 / 4) = 3 / 2 by norm_num,
      ← ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 3 / 2 by norm_num),
      ← ENNReal.ofReal_mul (hf0 y),
      ENNReal.ofReal_rpow_of_nonneg hx0 (show (0 : ℝ) ≤ 3 / 2 by norm_num)]
  simpa only [hpoint] using hHolder

/-- The `L^{3/2}` norm of the product of the velocity and the mean-free field
is controlled by the `L²` norm of the former and the `L⁶` norm of the latter;
this is part `(a)` of `eq:U-bounds` in `paper/ckn.tex` before the
Sobolev–Poincaré inequality is applied. -/
private lemma integral_rpow_three_halves_le {μ : Measure Vec3} {f g : Vec3 → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf0 : ∀ y, 0 ≤ f y) (hg0 : ∀ y, 0 ≤ g y)
    (hfint : ∫⁻ y, ENNReal.ofReal (f y) ^ (2 : ℝ) ∂μ < ⊤)
    (hgint : ∫⁻ y, ENNReal.ofReal (g y) ^ (6 : ℝ) ∂μ < ⊤) :
    (∫ y, (f y * g y) ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) ≤
      (∫ y, f y ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) *
        (∫ y, g y ^ (6 : ℕ) ∂μ) ^ (1 / 6 : ℝ) := by
  have hprod0 : ∀ y, 0 ≤ f y * g y := fun y => mul_nonneg (hf0 y) (hg0 y)
  have hmul : AEMeasurable (fun y => (f y * g y) ^ (3 / 2 : ℝ)) μ :=
    (hf.mul hg).pow_const (3 / 2)
  have hHolder := lintegral_rpow_three_halves_le hf hg hf0 hg0
  have hXfin : ∫⁻ y, ENNReal.ofReal ((f y * g y) ^ (3 / 2 : ℝ)) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt hHolder (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfint.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hgint.ne))).ne
  have hX : ∫⁻ y, ENNReal.ofReal ((f y * g y) ^ (3 / 2 : ℝ)) ∂μ =
      ENNReal.ofReal (∫ y, (f y * g y) ^ (3 / 2 : ℝ) ∂μ) :=
    (ofReal_integral_eq_lintegral (fun y => Real.rpow_nonneg (hprod0 y) (3 / 2))
      hmul.aestronglyMeasurable hXfin).symm
  have hA : (∫⁻ y, ENNReal.ofReal (f y) ^ (2 : ℝ) ∂μ) =
      ENNReal.ofReal (∫ y, f y ^ (2 : ℕ) ∂μ) :=
    lintegral_ofReal_pow_eq_ofReal_integral hf0 hf 2 (by simpa using hfint)
  have hB : (∫⁻ y, ENNReal.ofReal (g y) ^ (6 : ℝ) ∂μ) =
      ENNReal.ofReal (∫ y, g y ^ (6 : ℕ) ∂μ) :=
    lintegral_ofReal_pow_eq_ofReal_integral hg0 hg 6 (by simpa using hgint)
  have hstep : ENNReal.ofReal (∫ y, (f y * g y) ^ (3 / 2 : ℝ) ∂μ) ≤
      ENNReal.ofReal (∫ y, f y ^ (2 : ℕ) ∂μ) ^ (3 / 4 : ℝ) *
        ENNReal.ofReal (∫ y, g y ^ (6 : ℕ) ∂μ) ^ (1 / 4 : ℝ) := by
    rw [hX, hA, hB] at hHolder
    exact hHolder
  have hmain := ENNReal.rpow_le_rpow hstep (show (0 : ℝ) ≤ 2 / 3 by norm_num)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 2 / 3 by norm_num),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    show (3 : ℝ) / 4 * (2 / 3) = 1 / 2 by norm_num,
    show (1 : ℝ) / 4 * (2 / 3) = 1 / 6 by norm_num] at hmain
  have hL0 : 0 ≤ ∫ y, (f y * g y) ^ (3 / 2 : ℝ) ∂μ :=
    integral_nonneg (fun y => Real.rpow_nonneg (hprod0 y) (3 / 2))
  have hM0 : 0 ≤ ∫ y, f y ^ (2 : ℕ) ∂μ :=
    integral_nonneg (fun y => pow_nonneg (hf0 y) 2)
  have hN0 : 0 ≤ ∫ y, g y ^ (6 : ℕ) ∂μ :=
    integral_nonneg (fun y => pow_nonneg (hg0 y) 6)
  rw [ENNReal.ofReal_rpow_of_nonneg hL0 (show (0 : ℝ) ≤ 2 / 3 by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hM0 (show (0 : ℝ) ≤ 1 / 2 by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hN0 (show (0 : ℝ) ≤ 1 / 6 by norm_num),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hM0 (1 / 2))] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg hM0 (1 / 2)) (Real.rpow_nonneg hN0 (1 / 6)))).mp hmain

/-- Hölder's inequality against the volume of the ambient ball: the `L¹` norm
of the product is controlled by its `L^{3/2}` norm and the `1/3`-power of the
total mass.  This is the estimate underlying part `(b)` of `eq:U-bounds` in
`paper/ckn.tex`. -/
private lemma integral_mul_le_volume_rpow {μ : Measure Vec3} [IsFiniteMeasure μ]
    {f g : Vec3 → ℝ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf0 : ∀ y, 0 ≤ f y) (hg0 : ∀ y, 0 ≤ g y)
    (hXfin : ∫⁻ y, ENNReal.ofReal ((f y * g y) ^ (3 / 2 : ℝ)) ∂μ < ⊤) :
    ∫ y, f y * g y ∂μ ≤
      (μ Set.univ).toReal ^ (1 / 3 : ℝ) *
        (∫ y, (f y * g y) ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) := by
  have hprod0 : ∀ y, 0 ≤ f y * g y := fun y => mul_nonneg (hf0 y) (hg0 y)
  have hmul : AEMeasurable (fun y => (f y * g y) ^ (3 / 2 : ℝ)) μ :=
    (hf.mul hg).pow_const (3 / 2)
  have hF : AEMeasurable (fun y => ENNReal.ofReal ((f y * g y) ^ (3 / 2 : ℝ))) μ :=
    hmul.ennreal_ofReal
  have hOne : AEMeasurable (fun _ : Vec3 => (1 : ℝ≥0∞)) μ := aemeasurable_const
  have hHolder := ENNReal.lintegral_mul_norm_pow_le hF hOne
    (show (0 : ℝ) ≤ 2 / 3 by norm_num) (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    (show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num)
  have hLHS : ∫⁻ y, ENNReal.ofReal ((f y * g y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
      (1 : ℝ≥0∞) ^ (1 / 3 : ℝ) ∂μ = ∫⁻ y, ENNReal.ofReal (f y * g y) ∂μ := by
    apply lintegral_congr
    intro y
    have hx0 : 0 ≤ f y * g y := hprod0 y
    rw [ENNReal.one_rpow, mul_one,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hx0 (3 / 2))
        (show (0 : ℝ) ≤ 2 / 3 by norm_num),
      ← Real.rpow_mul hx0, show (3 : ℝ) / 2 * (2 / 3) = 1 by norm_num, Real.rpow_one]
  rw [hLHS, lintegral_one] at hHolder
  have hRfin : (∫⁻ y, ENNReal.ofReal ((f y * g y) ^ (3 / 2 : ℝ)) ∂μ) ^ (2 / 3 : ℝ) *
      (μ Set.univ) ^ (1 / 3 : ℝ) ≠ ⊤ :=
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hXfin.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (IsFiniteMeasure.measure_univ_lt_top.ne))).ne
  have htoReal := ENNReal.toReal_mono hRfin hHolder
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at htoReal
  rw [← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hprod0)
        (hf.mul hg).aestronglyMeasurable,
      ← integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall (fun y => Real.rpow_nonneg (hprod0 y) (3 / 2)))
        hmul.aestronglyMeasurable] at htoReal
  rw [mul_comm] at htoReal
  exact htoReal

/-- Lemma `lem:U-bounds` of `paper/ckn.tex` (equation `eq:U-bounds`).  For a
velocity field `u` whose time slice is in `L²` and `L⁶` on the spatial ball
`B_ρ = vec3Ball x₀ ρ`, and assuming the same-ball `L⁶` Sobolev–Poincaré
inequality (equation `eq:sobolev-poincare-6`) for the mean-free field, the
tensor `U` of `eq:Uij` satisfies

`(∫_{B_ρ} |U|^{3/2})^{2/3} ≤ C₅ 𝔲(t) 𝔤(t)` and
`∫_{B_ρ} |U| ≤ (4π/3)^{1/3} C₅ ρ 𝔲(t) 𝔤(t)`,

where `𝔲(t) = (∫_{B_ρ} |u(·,t)|²)^{1/2}` and
`𝔤(t) = (∫_{B_ρ} |∇u(·,t)|²)^{1/2}`. -/
theorem U_bounds_of_sobolevPoincare
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3) (x₀ : Vec3)
    {ρ t C₅ : ℝ} (hρ : 0 < ρ)
    (humeas : AEMeasurable (fun y : Vec3 => u (y, t))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hu2 : MemLp (fun y : Vec3 => vec3EuclideanNorm (u (y, t))) 2
      (volume.restrict (vec3Ball x₀ ρ)))
    (hu6 : MemLp (fun y : Vec3 => vec3EuclideanNorm (u (y, t))) 6
      (volume.restrict (vec3Ball x₀ ρ)))
    (hsob :
      (∫ y in vec3Ball x₀ ρ,
          (vec3EuclideanNorm (meanFreeVec u x₀ ρ t y)) ^ (6 : ℕ)) ^ (1 / 6 : ℝ) ≤
        C₅ * (∫ y in vec3Ball x₀ ρ, spatialGradientSq u Du (y, t)) ^ (1 / 2 : ℝ)) :
    ((∫ y in vec3Ball x₀ ρ, (utensorNorm u x₀ ρ t y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        C₅ * (∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (u (y, t)) ^ (2 : ℕ)) ^
            (1 / 2 : ℝ) *
          (∫ y in vec3Ball x₀ ρ, spatialGradientSq u Du (y, t)) ^ (1 / 2 : ℝ)) ∧
      (∫ y in vec3Ball x₀ ρ, utensorNorm u x₀ ρ t y ≤
        (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * C₅ * ρ *
          (∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (u (y, t)) ^ (2 : ℕ)) ^
            (1 / 2 : ℝ) *
          (∫ y in vec3Ball x₀ ρ, spatialGradientSq u Du (y, t)) ^ (1 / 2 : ℝ)) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball x₀ ρ)
  let gu : Vec3 → ℝ := fun y => vec3EuclideanNorm (u (y, t))
  let gv : Vec3 → ℝ := fun y => vec3EuclideanNorm (meanFreeVec u x₀ ρ t y)
  let cvec : Vec3 := fun j => MeasureTheory.average μ (fun z => u (z, t) j)
  let G : ℝ := (∫ y, spatialGradientSq u Du (y, t) ∂μ) ^ (1 / 2 : ℝ)
  have hgu0 : ∀ y, 0 ≤ gu y := fun y => vec3EuclideanNorm_nonneg _
  have hgv0 : ∀ y, 0 ≤ gv y := fun y => vec3EuclideanNorm_nonneg _
  have hgu : AEMeasurable gu μ := hu2.aestronglyMeasurable.aemeasurable
  have hμfin : IsFiniteMeasure μ := by
    change IsFiniteMeasure (volume.restrict (vec3Ball x₀ ρ))
    rw [isFiniteMeasure_restrict, volume_vec3Ball_eq]
    exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top).ne
  have : IsFiniteMeasure μ := hμfin
  have hmeanfree : meanFreeVec u x₀ ρ t = fun y : Vec3 => u (y, t) - cvec := rfl
  have hcmeas : AEMeasurable (fun y : Vec3 => u (y, t) - cvec) μ :=
    humeas.sub aemeasurable_const
  have hgvmeas : AEStronglyMeasurable gv μ := by
    have h : AEMeasurable (fun y : Vec3 => vec3EuclideanNorm (u (y, t) - cvec)) μ :=
      continuous_vec3EuclideanNorm.measurable.comp_aemeasurable hcmeas
    simpa only [gv, hmeanfree, Function.comp_apply] using h.aestronglyMeasurable
  have hpt : ∀ y, ‖gv y‖ ≤ ‖gu y + vec3EuclideanNorm cvec‖ := by
    intro y
    have hsub := vec3EuclideanNorm_sub_le (u (y, t)) cvec
    rw [Real.norm_of_nonneg (hgv0 y),
      Real.norm_of_nonneg (add_nonneg (hgu0 y) (vec3EuclideanNorm_nonneg _))]
    simpa only [gv, gu, hmeanfree] using hsub
  have hguC : MemLp (fun y => gu y + vec3EuclideanNorm cvec) 6 μ :=
    hu6.add (memLp_const _)
  have hgv6 : MemLp gv 6 μ := hguC.of_le hgvmeas (Eventually.of_forall hpt)
  have hu2' : MemLp gu (ENNReal.ofReal (2 : ℝ)) μ := by
    have h : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by simp
    rw [h]; simpa only [gu, μ] using hu2
  have hgv6' : MemLp gv (ENNReal.ofReal (6 : ℝ)) μ := by
    have h : ENNReal.ofReal (6 : ℝ) = (6 : ℝ≥0∞) := by simp
    rw [h]; simpa only [gv, μ] using hgv6
  have hgu2fin : ∫⁻ y, ENNReal.ofReal (gu y) ^ (2 : ℝ) ∂μ < ⊤ :=
    lintegral_ofReal_rpow_lt_top (p := (2 : ℝ)) (by norm_num) hgu0 hu2'
  have hgv6fin : ∫⁻ y, ENNReal.ofReal (gv y) ^ (6 : ℝ) ∂μ < ⊤ :=
    lintegral_ofReal_rpow_lt_top (p := (6 : ℝ)) (by norm_num) hgv0 hgv6'
  have hgvaemeas : AEMeasurable gv μ := hgvmeas.aemeasurable
  have hbounded :=
    integral_rpow_three_halves_le hgu hgvaemeas hgu0 hgv0 hgu2fin hgv6fin
  have hRHSfin : (∫⁻ y, ENNReal.ofReal (gu y) ^ (2 : ℝ) ∂μ) ^ (3 / 4 : ℝ) *
      (∫⁻ y, ENNReal.ofReal (gv y) ^ (6 : ℝ) ∂μ) ^ (1 / 4 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hgu2fin.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hgv6fin.ne)
  have hXfin : ∫⁻ y, ENNReal.ofReal ((gu y * gv y) ^ (3 / 2 : ℝ)) ∂μ < ⊤ :=
    lt_of_le_of_lt (lintegral_rpow_three_halves_le hgu hgvaemeas hgu0 hgv0) hRHSfin
  have hUnorm : ∀ y, utensorNorm u x₀ ρ t y = gu y * gv y := by
    intro y
    rw [utensorNorm_eq]
  have hIntEq : (∫ y in vec3Ball x₀ ρ, (utensorNorm u x₀ ρ t y) ^ (3 / 2 : ℝ)) =
      ∫ y, (gu y * gv y) ^ (3 / 2 : ℝ) ∂μ := by
    refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
    change utensorNorm u x₀ ρ t y ^ (3 / 2 : ℝ) = (gu y * gv y) ^ (3 / 2 : ℝ)
    rw [hUnorm y]
  have hIntEq1 : (∫ y in vec3Ball x₀ ρ, utensorNorm u x₀ ρ t y) =
      ∫ y, gu y * gv y ∂μ := by
    refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
    change utensorNorm u x₀ ρ t y = gu y * gv y
    rw [hUnorm y]
  have hmid : (∫ y, (gu y * gv y) ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) ≤
      C₅ * (∫ y, gu y ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) * G := by
    have hsob' : (∫ y, gv y ^ (6 : ℕ) ∂μ) ^ (1 / 6 : ℝ) ≤ C₅ * G := by
      simpa only [G, μ, gv] using hsob
    calc (∫ y, (gu y * gv y) ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ)
        ≤ (∫ y, gu y ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) *
            (∫ y, gv y ^ (6 : ℕ) ∂μ) ^ (1 / 6 : ℝ) := hbounded
      _ ≤ (∫ y, gu y ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) * (C₅ * G) :=
            mul_le_mul_of_nonneg_left hsob'
              (Real.rpow_nonneg (integral_nonneg (fun y => pow_nonneg (hgu0 y) 2)) _)
      _ = C₅ * (∫ y, gu y ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) * G := by ring
  have hvol : (μ Set.univ).toReal ^ (1 / 3 : ℝ) =
      ρ * (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) := by
    have huniv : μ Set.univ = volume (vec3Ball x₀ ρ) := by
      simp only [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    have hval : (μ Set.univ).toReal = ρ ^ 3 * (Real.pi * 4 / 3) := by
      rw [huniv, volume_vec3Ball_eq, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (le_of_lt hρ), ENNReal.toReal_ofReal (by positivity)]
    rw [hval, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast ρ 3, ← Real.rpow_mul (le_of_lt hρ),
      show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one]
  refine ⟨?_, ?_⟩
  · rw [hIntEq]
    exact hmid
  · rw [hIntEq1]
    have hcore := integral_mul_le_volume_rpow hgu hgvaemeas hgu0 hgv0 hXfin
    calc ∫ y, gu y * gv y ∂μ
        ≤ (μ Set.univ).toReal ^ (1 / 3 : ℝ) *
            (∫ y, (gu y * gv y) ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) := hcore
      _ ≤ (μ Set.univ).toReal ^ (1 / 3 : ℝ) * (C₅ * (∫ y, gu y ^ (2 : ℕ) ∂μ) ^
            (1 / 2 : ℝ) * G) :=
            mul_le_mul_of_nonneg_left hmid (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      _ = (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * C₅ * ρ *
            (∫ y, gu y ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) * G := by
            rw [hvol]; ring

private lemma euclideanBall_eq_vec3Ball_utensor {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change (x ∈ euclideanBall x₀ r) ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

private lemma vec3EuclideanNorm_le_sqrt_three_native_utensor (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    have hv : vec3EuclideanNorm v ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
      unfold vec3EuclideanNorm
      exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    rw [hv, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      ∑ i : Fin 3, v i ^ 2 ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) 2
      _ = 3 * ‖v‖ ^ 2 := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : |vec3EuclideanNorm v| ≤ |Real.sqrt 3 * ‖v‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (vec3EuclideanNorm_nonneg v),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg v))] at h2

private lemma vec3EuclideanNorm_add_le_utensor (a b : Vec3) :
    vec3EuclideanNorm (a + b) ≤ vec3EuclideanNorm a + vec3EuclideanNorm b := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

/-- The paper's `eq:U-bounds` holds for almost every time slice of a suitable
weak solution on a cylinder whose closure lies in its open carrier. -/
theorem U_bounds
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ t ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (((∫ y in vec3Ball z.1 ρ,
          (utensorNorm u z.1 ρ t y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
          9 * sobolevPoincareL6Constant.toReal *
            (∫ y in vec3Ball z.1 ρ,
              vec3EuclideanNorm (u (y, t)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) *
            (∫ y in vec3Ball z.1 ρ,
              spatialGradientSq u Du (y, t)) ^ (1 / 2 : ℝ)) ∧
        (∫ y in vec3Ball z.1 ρ, utensorNorm u z.1 ρ t y ≤
          (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
            (9 * sobolevPoincareL6Constant.toReal) * ρ *
            (∫ y in vec3Ball z.1 ρ,
              vec3EuclideanNorm (u (y, t)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) *
            (∫ y in vec3Ball z.1 ρ,
              spatialGradientSq u Du (y, t)) ^ (1 / 2 : ℝ))) := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hball : vec3Ball z.1 ρ ⊆ Ω' := by
    intro y hy
    have hz : (y, z.2) ∈ parabolicCylinder z.1 z.2 ρ := by
      rw [parabolicCylinder]
      exact ⟨hy, ⟨by linarith only [sq_pos_of_pos hρ], le_rfl⟩⟩
    exact (hcyl hz).1
  have htime : Ioc (z.2 - ρ ^ 2) z.2 ⊆ J := by
    intro t ht
    have hx : z.1 ∈ vec3Ball z.1 ρ := by
      rw [mem_vec3Ball]
      simpa [vec3EuclideanNorm_zero] using hρ
    have hz : (z.1, t) ∈ parabolicCylinder z.1 z.2 ρ := by
      rw [parabolicCylinder]
      exact ⟨hx, ht⟩
    exact (hcyl hz).2
  obtain ⟨_hu, _hDu, _hp, _hf, _hess, _henergy, _hp', _hf', hgrad⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  have hgradAll : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun x => u (x, s) i) (fun x => Du (x, s) i) := by
    filter_upwards [hgrad 0, hgrad 1, hgrad 2] with s h0 h1 h2
    intro i
    fin_cases i <;> assumption
  have hsliceJ := slice_memLp_ae_of_sws hsol hbox
  have hslice : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
      MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω') :=
    ae_restrict_of_ae_restrict_of_subset htime hsliceJ
  have hgradI := ae_restrict_of_ae_restrict_of_subset htime hgradAll
  have hopen : IsOpen (euclideanBall z.1 ρ) := by
    change IsOpen {x : Vec3 | euclideanSqDist x z.1 < ρ ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left z.1).continuous continuous_const
  have hballEq : euclideanBall z.1 ρ = vec3Ball z.1 ρ :=
    euclideanBall_eq_vec3Ball_utensor hρ
  have hballE : euclideanBall z.1 ρ ⊆ Ω' := by
    rw [hballEq]
    exact hball
  filter_upwards [hslice, hgradI] with t hts hgt
  let μ : Measure Vec3 := volume.restrict (vec3Ball z.1 ρ)
  have hμtop : μ Set.univ < ∞ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      (by
        rw [volume_vec3Ball_eq]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top : volume (vec3Ball z.1 ρ) < ∞)
  have : IsFiniteMeasure μ := ⟨hμtop⟩
  have huB : MemLp (fun x : Vec3 => u (x, t)) 2 μ := by
    simpa [μ] using hts.1.mono_measure (Measure.restrict_mono_set volume hball)
  have hDuB : MemLp (fun x : Vec3 => Du (x, t)) 2
      (volume.restrict (euclideanBall z.1 ρ)) := by
    exact hts.2.mono_measure (Measure.restrict_mono_set volume hballE)
  have humeas : AEMeasurable (fun x : Vec3 => u (x, t)) μ :=
    huB.aestronglyMeasurable.aemeasurable
  have humeasNorm : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) μ := by
    exact (continuous_vec3EuclideanNorm.measurable.comp_aemeasurable humeas).aestronglyMeasurable
  have hu2 : MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 μ := by
    apply huB.of_le_mul humeasNorm
    on_goal 1 => filter_upwards [] with y
    on_goal 1 => rw [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact vec3EuclideanNorm_le_sqrt_three_native_utensor (u (y, t))
  let huH1 : ∀ i : Fin 3, H1Function (euclideanBall z.1 ρ) := fun i =>
    { toFun := fun x => u (x, t) i
      grad := fun x => Du (x, t) i
      memL2 := (MemLp.eval hts.1 i).mono_measure
        (Measure.restrict_mono_set volume hballE)
      gradMemL2 := fun j => (MemLp.eval (MemLp.eval hts.2 i) j).mono_measure
        (Measure.restrict_mono_set volume hballE)
      hasWeakGradient := (hgt i).restrict hopen hballE }
  have hcomp : ∀ i : Fin 3,
      (huH1 i).toFun = fun x => (fun y => u (y, t)) x i := by
    intro i
    simp [huH1]
  have hgrad' : ∀ i : Fin 3,
      (huH1 i).grad = fun x => (fun y => Du (y, t)) x i := by
    intro i
    simp [huH1]
  have hbridge := vector_h1_sobolev_ball_integral hρ (fun x => u (x, t))
    (fun x i => Du (x, t) i) huH1 hcomp hgrad'
  have hW : MemLp (fun y : Vec3 => vec3EuclideanNorm (fun i : Fin 3 =>
      u (y, t) i - average μ (fun z => u (z, t) i))) 6 μ := by
    simpa [μ] using hbridge.1
  let cvec : Vec3 := fun j => average μ (fun z => u (z, t) j)
  let gw : Vec3 → ℝ := fun y => vec3EuclideanNorm (fun i : Fin 3 =>
    u (y, t) i - cvec i)
  let gu : Vec3 → ℝ := fun y => vec3EuclideanNorm (u (y, t))
  have hgw : MemLp gw 6 μ := by simpa [gw] using hW
  have hgu6 : MemLp gu 6 μ := by
    have hsum : MemLp (fun y => gw y + vec3EuclideanNorm cvec) 6 μ :=
      hgw.add (memLp_const _)
    apply hsum.of_le humeasNorm
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _),
      Real.norm_of_nonneg (add_nonneg (vec3EuclideanNorm_nonneg _)
        (vec3EuclideanNorm_nonneg _))]
    change vec3EuclideanNorm (u (y, t)) ≤
      vec3EuclideanNorm (fun i : Fin 3 => u (y, t) i - cvec i) +
        vec3EuclideanNorm cvec
    have hdecomp : u (y, t) = (fun i =>
        u (y, t) i - cvec i) + cvec := by
      funext i
      dsimp [cvec]
      ring
    calc
      vec3EuclideanNorm (u (y, t)) =
          vec3EuclideanNorm ((fun i => u (y, t) i - cvec i) + cvec) := by
            exact congrArg vec3EuclideanNorm hdecomp
      _ ≤ vec3EuclideanNorm (fun i => u (y, t) i - cvec i) +
          vec3EuclideanNorm cvec := vec3EuclideanNorm_add_le_utensor _ _
  have hsob :
      (∫ y in vec3Ball z.1 ρ,
          (vec3EuclideanNorm (meanFreeVec u z.1 ρ t y)) ^ (6 : ℕ)) ^
            (1 / 6 : ℝ) ≤
        (9 * sobolevPoincareL6Constant.toReal) *
          (∫ y in vec3Ball z.1 ρ,
            spatialGradientSq u Du (y, t)) ^ (1 / 2 : ℝ) := by
    change (∫ y in vec3Ball z.1 ρ,
        (vec3EuclideanNorm (fun i : Fin 3 =>
          u (y, t) i - average μ (fun z => u (z, t) i))) ^ (6 : ℕ)) ^
          (1 / 6 : ℝ) ≤
      (9 * sobolevPoincareL6Constant.toReal) *
        (∫ y in vec3Ball z.1 ρ,
          spatialGradientSq u Du (y, t)) ^ (1 / 2 : ℝ)
    simpa [μ, spatialGradientSq] using hbridge.2
  exact U_bounds_of_sobolevPoincare u Du z.1 hρ humeas hu2 hgu6 hsob

end

end CKN
