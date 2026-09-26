/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Setting.Monotonicity
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingQuantities
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Finiteness

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section
namespace CKN

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-!
# Finiteness of the scale quantities on suitable weak solutions

The quantities `α`, `β`, `γ`, `δ`, `λ` of `paper/ckn.tex` are real-valued, so the
lemmas `lem:monotonicity` and `lem:scaling-quantities` for them carry side
conditions saying that the underlying nonnegative integrals are finite (a
necessary input when passing an `ℝ≥0∞` integral to `ℝ≥0`).  The class `def:sws`
of suitable weak solutions supplies exactly these finiteness properties on every
local box, and this file transfers them to the parabolic cylinders `Q_r(z)` of
the monotonicity and scaling statements.

The main transfer fact is that a cylinder whose closure lies in the open carrier
`Ω × I` is contained in a local box: the spatial slice is enclosed in a metric
thickening of its closed ball, and the time slice in a thickening of its closed
interval, both chosen small enough to stay inside `Ω` and `I`.
-/

/-! ### Elementary comparisons of the two norms on `Vec3` -/

/-- The default (supremum) norm is dominated by the Euclidean norm on `Vec3`. -/
private lemma norm_sub_le_vec3EuclideanNorm (x y : Vec3) :
    ‖y - x‖ ≤ vec3EuclideanNorm (y - x) := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg _)]
  intro i
  change |(y - x) i| ≤ vec3EuclideanNorm (y - x)
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _hj => sq_nonneg ((y - x) j)) (Finset.mem_univ i)

/-- The Euclidean closed ball of `Vec3` is compact. -/
private lemma isCompact_vec3EuclideanClosedBall (x : Vec3) (r : ℝ) :
    IsCompact {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} := by
  have hclosed : IsClosed {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} := by
    have hc : Continuous (fun y : Vec3 => vec3EuclideanNorm (y - x)) := by
      unfold vec3EuclideanNorm; fun_prop
    exact isClosed_Iic.preimage hc
  have hsub : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} ⊆ Metric.closedBall x r := by
    intro y hy
    simp only [Metric.mem_closedBall]
    exact (norm_sub_le_vec3EuclideanNorm x y).trans hy
  exact (isCompact_closedBall x r).of_isClosed_subset hclosed hsub

/-- On any seminormed additive group the `enorm` of the norm raised to the
second power is the `ofReal` of the squared norm. -/
private lemma enorm_norm_pow_two {E : Type*} [SeminormedAddGroup E] (v : E) :
    ‖v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2, ENNReal.rpow_natCast,
    show ‖v‖ₑ = ENNReal.ofReal ‖v‖ from (ofReal_norm v).symm,
    ← ENNReal.ofReal_pow (norm_nonneg v)]

/-- The Euclidean norm on `Vec3` is at most `√3` times the supremum norm. -/
private lemma vec3EuclideanNorm_le_sqrt_three_mul_norm (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    rw [show (vec3EuclideanNorm v) ^ 2 = ∑ i, v i ^ 2 by
      rw [vec3EuclideanNorm, Real.sq_sqrt]
      exact Finset.sum_nonneg (fun i _hi => sq_nonneg (v i))]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) 2
      _ = 3 * ‖v‖ ^ 2 := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : |vec3EuclideanNorm v| ≤ |Real.sqrt 3 * ‖v‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (vec3EuclideanNorm_nonneg v),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg v))] at h2

/-- The squared Euclidean density of a vector is dominated by three times the
square of its supremum norm, on the `ℝ≥0∞` side. -/
private lemma ofReal_vec3EuclideanNorm_pow_two_le (v : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) ≤ 3 * ‖v‖ₑ ^ (2 : ℝ) := by
  have h2n : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2n]
  have hle : vec3EuclideanNorm v ^ 2 ≤ 3 * ‖v‖ ^ 2 := by
    have h := vec3EuclideanNorm_le_sqrt_three_mul_norm v
    have h2 : (vec3EuclideanNorm v) ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 :=
      pow_le_pow_left₀ (vec3EuclideanNorm_nonneg v) h 2
    simpa [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using h2
  calc ENNReal.ofReal (vec3EuclideanNorm v) ^ ((2 : ℕ) : ℝ)
      = ENNReal.ofReal (vec3EuclideanNorm v ^ ((2 : ℕ) : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg v) (by norm_num)
    _ = ENNReal.ofReal (vec3EuclideanNorm v ^ 2) := by rw [Real.rpow_natCast]
    _ ≤ ENNReal.ofReal (3 * ‖v‖ ^ 2) := ENNReal.ofReal_le_ofReal hle
    _ = 3 * ‖v‖ₑ ^ ((2 : ℕ) : ℝ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        show ENNReal.ofReal (3 : ℝ) = 3 by norm_num,
        show ‖v‖ₑ ^ ((2 : ℕ) : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) from by
          rw [ENNReal.rpow_natCast,
            show ‖v‖ₑ = ENNReal.ofReal ‖v‖ from (ofReal_norm v).symm,
            ← ENNReal.ofReal_pow (norm_nonneg v)]]

/-- The Euclidean density of a vector to the power `q ≥ 0` is dominated by the
`q`-th power of its supremum norm, up to the constant `(√3)^q`, on the `ℝ≥0∞`
side. -/
private lemma ofReal_vec3EuclideanNorm_rpow_le (q : ℝ) (hq : 0 ≤ q) (v : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm v) ^ q ≤
      ENNReal.ofReal ((Real.sqrt 3) ^ q) * ‖v‖ₑ ^ q := by
  have h1 : vec3EuclideanNorm v ^ q ≤ (Real.sqrt 3 * ‖v‖) ^ q :=
    Real.rpow_le_rpow (vec3EuclideanNorm_nonneg v)
      (vec3EuclideanNorm_le_sqrt_three_mul_norm v) hq
  rw [Real.mul_rpow (Real.sqrt_nonneg 3) (norm_nonneg v)] at h1
  calc ENNReal.ofReal (vec3EuclideanNorm v) ^ q
      = ENNReal.ofReal (vec3EuclideanNorm v ^ q) :=
        ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg v) hq
    _ ≤ ENNReal.ofReal ((Real.sqrt 3) ^ q * ‖v‖ ^ q) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal ((Real.sqrt 3) ^ q) * ENNReal.ofReal (‖v‖ ^ q) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg (Real.sqrt_nonneg 3) q)
    _ = ENNReal.ofReal ((Real.sqrt 3) ^ q) * ‖v‖ₑ ^ q := by
        rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg v) hq, ofReal_norm]

/-- The squared spatial-gradient density `spatialGradientSq` of a `3 × 3`
gradient is dominated by nine times the square of the gradient's supremum norm. -/
private lemma ofReal_spatialGradientSq_le (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    ENNReal.ofReal (spatialGradientSq u Du z) ≤ 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
  have hsq : spatialGradientSq u Du z ≤ 9 * ‖Du z‖ ^ 2 := by
    rw [spatialGradientSq]
    calc ∑ i, ∑ j, (Du z i j) ^ (2 : ℕ)
        ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖Du z‖ ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _)
            ((norm_le_pi_norm (Du z i) j).trans (norm_le_pi_norm (Du z) i)) 2
      _ = 9 * ‖Du z‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          try ring
  calc ENNReal.ofReal (spatialGradientSq u Du z)
      ≤ ENNReal.ofReal (9 * ‖Du z‖ ^ 2) := ENNReal.ofReal_le_ofReal hsq
    _ = 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
          show ENNReal.ofReal (9 : ℝ) = 9 by norm_num,
          ← enorm_norm_pow_two (Du z)]

/-! ### Cylinders inside local boxes -/

/-- A parabolic cylinder whose closure lies in the open carrier `Ω × I` is
contained in a local box `Ω' × J`.  The box is obtained by thickening the
compact closed slices of the cylinder; the carrier is open, so a positive
thickening radius keeps it inside. -/
theorem exists_localBox_of_closure_subset {Ω : Set Vec3} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) {x : Vec3} {t r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder x t r) ⊆ spaceTimeSet Ω I) :
    ∃ Ω' J, localBox Ω I Ω' J ∧ parabolicCylinder x t r ⊆ spaceTimeSet Ω' J := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hcl : closure (parabolicCylinder x t r) =
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} ×ˢ Icc (t - r ^ 2) t :=
    closure_parabolicCylinder hr
  have hEΩ : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} ⊆ Ω := by
    intro y hy
    have hs : t - r ^ 2 ∈ Icc (t - r ^ 2) t := ⟨le_refl _, by linarith only [hr2]⟩
    have hmem : (y, t - r ^ 2) ∈ spaceTimeSet Ω I :=
      hsub (by rw [hcl]; exact ⟨hy, hs⟩)
    exact hmem.1
  have hTI : Icc (t - r ^ 2) t ⊆ I := by
    intro s hs
    have h0 : vec3EuclideanNorm (x - x) ≤ r := by simp [vec3EuclideanNorm_zero, hr.le]
    have hmem : (x, s) ∈ spaceTimeSet Ω I := hsub (by rw [hcl]; exact ⟨h0, hs⟩)
    exact hmem.2
  obtain ⟨δE, hδE, hδEsub⟩ :=
    (isCompact_vec3EuclideanClosedBall x r).exists_cthickening_subset_open hΩ hEΩ
  obtain ⟨δT, hδT, hδTsub⟩ :=
    isCompact_Icc.exists_thickening_subset_open hI hTI
  have hEsub : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} ⊆
      thickening (δE / 2) {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} :=
    self_subset_thickening (half_pos hδE) _
  refine ⟨thickening (δE / 2) {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r},
    Ioo (t - r ^ 2 - δT / 2) (t + δT / 2), ?_, ?_⟩
  · refine ⟨isOpen_thickening, ?_, ?_, ordConnected_Ioo, ?_, ?_⟩
    · have hsub' : closure (thickening (δE / 2)
          {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r}) ⊆
          cthickening (δE / 2) {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} :=
        closure_thickening_subset_cthickening _ _
      exact ((isCompact_vec3EuclideanClosedBall x r).cthickening).of_isClosed_subset
        isClosed_closure hsub'
    · exact (closure_thickening_subset_cthickening _ _).trans
        ((cthickening_mono (by linarith only [hδE]) _).trans hδEsub)
    · rw [show closure (Ioo (t - r ^ 2 - δT / 2) (t + δT / 2)) =
          Icc (t - r ^ 2 - δT / 2) (t + δT / 2) from
        closure_Ioo (by linarith only [hr2, hδT])]
      exact isCompact_Icc
    · rw [show closure (Ioo (t - r ^ 2 - δT / 2) (t + δT / 2)) =
          Icc (t - r ^ 2 - δT / 2) (t + δT / 2) from
        closure_Ioo (by linarith only [hr2, hδT])]
      intro s hs
      refine hδTsub ?_
      rw [mem_thickening_iff]
      rcases le_total s (t - r ^ 2) with hle | hle
      · refine ⟨t - r ^ 2, ⟨le_refl _, by linarith only [hr2]⟩, ?_⟩
        rw [Real.dist_eq, abs_of_nonpos (by linarith only [hle])]
        linarith only [hs.1, hδT]
      · rcases le_total s t with hle' | hle'
        · exact ⟨s, ⟨hle, hle'⟩, by simpa using hδT⟩
        · refine ⟨t, ⟨by linarith only [hr2], le_refl _⟩, ?_⟩
          rw [Real.dist_eq, abs_of_nonneg (by linarith only [hle'])]
          linarith only [hs.2, hδT]
  · intro z hz
    rw [parabolicCylinder] at hz
    exact ⟨hEsub (le_of_lt (mem_vec3Ball.mp hz.1)), ⟨by linarith only [hz.2.1, hδT, hr2],
      by linarith only [hz.2.2, hδT]⟩⟩

/-! ### The finiteness data on a local box -/

/-- The finiteness and integrability fields of `def:sws` restricted to the four
quantities used by the monotonicity lemmas. -/
private lemma sws_local_box_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) :
    essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict J) < ⊤ ∧
    (∫⁻ z in spaceTimeSet Ω' J, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
    MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet Ω' J)) ∧
    MemLp f (ENNReal.ofReal q) (volume.restrict (spaceTimeSet Ω' J)) := by
  obtain ⟨-, -, -, -, hEssSup, henergy, hp_mem, hf_mem, -⟩ :=
    h.2.2.2.2.2.1 Ω' J hbox
  exact ⟨hEssSup, henergy, hp_mem, hf_mem⟩

/-! ### Finiteness of the time-slice energy (`α`) -/

/-- On a cylinder whose closure lies in the carrier, the `def:sws` time-slice
energy estimate bounds the essential supremum of the Euclidean time-slice energy
occurring in `lem:monotonicity` for `α`. -/
theorem sws_timeSliceEnergyEssSup_lt_top
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    timeSliceEnergyEssSup z.1 z.2 r (fun w => vec3EuclideanNorm (u w)) < ⊤ := by
  unfold timeSliceEnergyEssSup
  have hΩ : IsOpen Ω := h.1
  have hI : IsOpen I := h.2.1
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset hΩ hI hr hsub
  obtain ⟨hEssSup, -, -, -⟩ := sws_local_box_data h hbox
  have hball : vec3Ball z.1 r ⊆ Ω' := by
    intro y hy
    have h1 : (y, z.2) ∈ spaceTimeSet Ω' J :=
      hcyl (by rw [parabolicCylinder]; exact ⟨hy, ⟨by linarith only [hr2], le_refl _⟩⟩)
    exact h1.1
  have hIocJ : Ioc (z.2 - r ^ 2) z.2 ⊆ J := by
    intro s hs
    have hx : z.1 ∈ vec3Ball z.1 r := by
      rw [mem_vec3Ball]; simpa [vec3EuclideanNorm_zero] using hr
    have h1 : (z.1, s) ∈ spaceTimeSet Ω' J :=
      hcyl (by rw [parabolicCylinder]; exact ⟨hx, hs⟩)
    exact h1.2
  have hpoint : ∀ s, timeSliceBallEnergy z.1 r s (fun w => vec3EuclideanNorm (u w)) ≤
      3 * ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ) := by
    intro s
    unfold timeSliceBallEnergy
    calc ∫⁻ y in vec3Ball z.1 r, ‖vec3EuclideanNorm (u (y, s))‖ₑ ^ (2 : ℝ)
        = ∫⁻ y in vec3Ball z.1 r,
            ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ) :=
          lintegral_congr (fun y => by
            rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)])
      _ ≤ ∫⁻ y in vec3Ball z.1 r, 3 * ‖u (y, s)‖ₑ ^ (2 : ℝ) :=
          lintegral_mono (fun y => ofReal_vec3EuclideanNorm_pow_two_le (u (y, s)))
      _ = 3 * ∫⁻ y in vec3Ball z.1 r, ‖u (y, s)‖ₑ ^ (2 : ℝ) :=
          lintegral_const_mul' 3 _ (by norm_num)
      _ ≤ 3 * ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hball) (by positivity)
  have hmono := essSup_mono_measure_and_ae
    (μ := volume.restrict (Ioc (z.2 - r ^ 2) z.2))
    (ν := volume.restrict J)
    (Measure.restrict_mono hIocJ le_rfl) (Filter.Eventually.of_forall hpoint)
  rw [ENNReal.essSup_const_mul] at hmono
  exact lt_of_le_of_lt hmono (ENNReal.mul_lt_top (by norm_num) hEssSup)

/-- Restatement of `sws_timeSliceEnergyEssSup_lt_top` in the `≠ ⊤` form in which
the hypothesis appears in `lem:monotonicity`. -/
theorem sws_timeSliceEnergyEssSup_ne_top
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    timeSliceEnergyEssSup z.1 z.2 r (fun w => vec3EuclideanNorm (u w)) ≠ ⊤ :=
  ne_of_lt (sws_timeSliceEnergyEssSup_lt_top h hr hsub)

/-! ### Finiteness of the gradient, pressure and force integrals -/

/-- The Dirichlet-energy integral of `lem:monotonicity` for `β` is finite on a
cylinder whose closure lies in the carrier. -/
theorem sws_gradient_integral_lt_top
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (spatialGradientSq u Du w)) < ⊤ := by
  have hΩ : IsOpen Ω := h.1
  have hI : IsOpen I := h.2.1
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset hΩ hI hr hsub
  obtain ⟨-, henergy, -, -⟩ := sws_local_box_data h hbox
  calc ∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal (spatialGradientSq u Du w)
      ≤ ∫⁻ w in parabolicCylinder z.1 z.2 r,
          9 * (‖u w‖ₑ ^ (2 : ℝ) + ‖Du w‖ₑ ^ (2 : ℝ)) := by
        refine lintegral_mono (fun w => ?_)
        exact (ofReal_spatialGradientSq_le u Du w).trans
          (mul_le_mul_of_nonneg_left (le_add_left le_rfl) (by norm_num))
    _ = 9 * ∫⁻ w in parabolicCylinder z.1 z.2 r,
          (‖u w‖ₑ ^ (2 : ℝ) + ‖Du w‖ₑ ^ (2 : ℝ)) :=
        lintegral_const_mul' 9 _ (by norm_num)
    _ ≤ 9 * ∫⁻ w in spaceTimeSet Ω' J,
          (‖u w‖ₑ ^ (2 : ℝ) + ‖Du w‖ₑ ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (lintegral_mono_set hcyl) (by norm_num)
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) henergy

/-- The pressure integral of `lem:monotonicity` for `δ` is finite on a cylinder
whose closure lies in the carrier. -/
theorem sws_pressure_integral_lt_top
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) < ⊤ := by
  have hΩ : IsOpen Ω := h.1
  have hI : IsOpen I := h.2.1
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset hΩ hI hr hsub
  obtain ⟨-, -, hp_mem, -⟩ := sws_local_box_data h hbox
  have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := ENNReal.ofReal (3 / 2 : ℝ))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num)))
    ENNReal.ofReal_ne_top hp_mem.eLpNorm_lt_top
  have hbox_int : (∫⁻ w in spaceTimeSet Ω' J, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) < ⊤ := by
    simpa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2), Real.enorm_eq_ofReal_abs]
      using hlt
  exact lt_of_le_of_lt (lintegral_mono_set hcyl) hbox_int

/-- The force integral of `lem:monotonicity` for `λ` is finite on a cylinder
whose closure lies in the carrier, for the exponent `q > 0` of `def:sws`. -/
theorem sws_force_integral_lt_top
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) < ⊤ := by
  have hΩ : IsOpen Ω := h.1
  have hI : IsOpen I := h.2.1
  have hq : 0 < q := lt_trans (by norm_num : (0 : ℝ) < 5 / 2) h.2.2.2.1
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset hΩ hI hr hsub
  obtain ⟨-, -, -, hf_mem⟩ := sws_local_box_data h hbox
  have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := ENNReal.ofReal q)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top hf_mem.eLpNorm_lt_top
  have hbox_int : (∫⁻ w in spaceTimeSet Ω' J, ‖f w‖ₑ ^ q) < ⊤ := by
    simpa [ENNReal.toReal_ofReal hq.le] using hlt
  calc ∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q
      ≤ ∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal ((Real.sqrt 3) ^ q) * ‖f w‖ₑ ^ q :=
        lintegral_mono (fun w => ofReal_vec3EuclideanNorm_rpow_le q hq.le (f w))
    _ = ENNReal.ofReal ((Real.sqrt 3) ^ q) *
          ∫⁻ w in parabolicCylinder z.1 z.2 r, ‖f w‖ₑ ^ q :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((Real.sqrt 3) ^ q) *
          ∫⁻ w in spaceTimeSet Ω' J, ‖f w‖ₑ ^ q :=
        mul_le_mul_of_nonneg_left (lintegral_mono_set hcyl) (by positivity)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbox_int

/-! ### Hypothesis-free monotonicity for suitable weak solutions -/

/-- `lem:monotonicity` for the velocity energy `α`, with the finiteness
hypothesis supplied by `def:sws`. -/
theorem alpha_mono_radius_of_sws
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂)
    (hsub : closure (parabolicCylinder z.1 z.2 r₂) ⊆ spaceTimeSet Ω I) :
    alpha u z r₁ ≤ (r₂ / r₁) ^ (1 / 2 : ℝ) * alpha u z r₂ :=
  alpha_mono_radius u z hr₁ hrr
    (sws_timeSliceEnergyEssSup_ne_top h (z := z) (lt_of_lt_of_le hr₁ hrr) hsub)

/-- `lem:monotonicity` for the gradient quantity `β`, with the finiteness
hypothesis supplied by `def:sws`. -/
theorem beta_mono_radius_of_sws
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂)
    (hsub : closure (parabolicCylinder z.1 z.2 r₂) ⊆ spaceTimeSet Ω I) :
    beta u Du z r₁ ≤ (r₂ / r₁) ^ (1 / 2 : ℝ) * beta u Du z r₂ :=
  beta_mono_radius u Du z hr₁ hrr
    (ne_of_lt (sws_gradient_integral_lt_top h (z := z) (lt_of_lt_of_le hr₁ hrr) hsub))

/-- `lem:monotonicity` for the pressure quantity `δ` in squared form, with the
finiteness hypothesis supplied by `def:sws`. -/
theorem delta_sq_mono_radius_of_sws
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂)
    (hsub : closure (parabolicCylinder z.1 z.2 r₂) ⊆ spaceTimeSet Ω I) :
    delta p z r₁ ^ 2 ≤ (r₂ / r₁) ^ (4 / 3 : ℝ) * delta p z r₂ ^ 2 :=
  delta_sq_mono_radius p z hr₁ hrr
    (ne_of_lt (sws_pressure_integral_lt_top h (z := z) (lt_of_lt_of_le hr₁ hrr) hsub))

/-- `lem:monotonicity` for the force quantity `λ`, with the finiteness
hypothesis supplied by `def:sws`. -/
theorem lambda_mono_radius_of_sws
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂)
    (hsub : closure (parabolicCylinder z.1 z.2 r₂) ⊆ spaceTimeSet Ω I) :
    lambda q f z r₁ ≤ (r₁ / r₂) ^ (3 - 5 / q) * lambda q f z r₂ :=
  lambda_mono_radius q f z (lt_trans (by norm_num : (0 : ℝ) < 5 / 2) h.2.2.2.1) hr₁ hrr
    (ne_of_lt (sws_force_integral_lt_top h (z := z) (lt_of_lt_of_le hr₁ hrr) hsub))

/-- `lem:scaling-quantities` for the velocity energy `α`, with the two
boundedness hypotheses supplied by `def:sws` (they hold for every nonnegative
energy profile, so no assumption on the solution is needed). -/
theorem alpha_rescale_of_sws
    (_ : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (r : ℝ) :
    alpha (rescaleVelocity μ z₀ u) ((0 : Vec3), (0 : ℝ)) r = alpha u z₀ (μ * r) :=
  alpha_rescale μ hμ z₀ u r
    ⟨_, ENNReal.ae_le_essSup _⟩ ⟨_, ENNReal.ae_le_essSup _⟩

/-- `lem:scaling-quantities` for the iteration quantity `θ`, with the two
boundedness hypotheses of `α` supplied as in `alpha_rescale_of_sws`. -/
theorem theta_rescale_of_sws
    (_ : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (κ μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (r : ℝ) (hr : 0 < r) :
    theta κ (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du) (rescalePressure μ z₀ p)
        ((0 : Vec3), (0 : ℝ)) r = theta κ u Du p z₀ (μ * r) :=
  theta_rescale κ μ hμ z₀ u Du p r hr
    ⟨_, ENNReal.ae_le_essSup _⟩ ⟨_, ENNReal.ae_le_essSup _⟩

end CKN
