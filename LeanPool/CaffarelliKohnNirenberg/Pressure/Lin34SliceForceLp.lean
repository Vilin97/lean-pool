/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpP8
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP7Solution
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallOrigin

/-!
# Lin34 Slice Force Lp

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean

noncomputable section

namespace CKN

/-!
# The force potential `p₇ + p₈` is `L^{3/2}` on a.e. time slice

The decomposition `prop:pressure-decomposition`, grouped in `cor:CZ-harmonic`,
splits the local pressure into a Calderón–Zygmund part, a harmonic remainder,
and the force potentials `p₇` and `p₈` built from the cutoff `η` and the force `f` of a
suitable weak solution `def:sws`.  This file records the time-slice form of the force
estimate needed by the quantitative Hölder consumer `prop:lin34`: for almost every time in
the lower half of a parabolic cylinder, the sum `p₇ + p₈` is `L^{3/2}` on every round ball
of the spatial slice.

The proof combines three ingredients from
`CKN/Pressure/PkBoundsP7Solution.lean` and `CKN/Pressure/HarmonicRemainderForceTerms.lean`:
the a.e.-in-time slice data for the force, the `L^q` membership of the two families of
sources `η fⱼ` and `(∂ⱼ η) fⱼ`, and the local `L^{3/2}` theory of the Newtonian potentials
`CKN.Foundation.Euclidean.pressureP7_add_pressureP8_memLp_and_lpNorm_growth`.
-/

/-! ### Step 1: a.e. slice data for the force -/

/-- The sup norm on `Vec3 = Fin 3 → ℝ` is bounded by the Euclidean norm. -/
private theorem vec3_norm_le_euclidean_local (v : Vec3) :
    ‖v‖ ≤ vec3EuclideanNorm v := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg v)]
  intro i
  change |v i| ≤ vec3EuclideanNorm v
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _hj => sq_nonneg (v j))
    (Finset.mem_univ i)

/-- The `L^q` integral of the force over a parabolic cylinder is finite whenever the
cylinder's closure lies in the carrier `Ω × I`. -/
private theorem sws_force_norm_integral_lt_top_local
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ, ‖f w‖ₑ ^ q) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono ?_)
    (sws_force_integral_lt_top hsol (z := (x₀, t₀)) (r := ρ) hρ hsub)
  intro w
  change ‖f w‖ₑ ^ q ≤ ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q
  rw [← ofReal_norm]
  exact ENNReal.rpow_le_rpow
    (ENNReal.ofReal_le_ofReal (vec3_norm_le_euclidean_local (f w)))
    (by linarith only [hsol.2.2.2.1])

/-- A.e.-in-time slice data for the force: on the lower half-cylinder the force slice is
a.e. strongly measurable on the spatial ball and has finite `L^q` integral there. -/
private theorem force_slice_data_local
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀),
      AEStronglyMeasurable (fun x : Vec3 => f (x, s))
          (volume.restrict (vec3Ball x₀ ρ)) ∧
        (∫⁻ x in vec3Ball x₀ ρ, ‖f (x, s)‖ₑ ^ q) < ⊤ := by
  have hΩ : IsOpen Ω := hsol.1
  have hIopen : IsOpen I := hsol.2.1
  obtain ⟨Ω', J, hbox, hcyl⟩ :=
    exists_localBox_of_closure_subset hΩ hIopen hρ hsub
  let B : Set Vec3 := vec3Ball x₀ ρ
  let T : Set ℝ := Ioc (t₀ - ρ ^ 2) t₀
  have hB : B ⊆ Ω' := by
    intro y hy
    have hz : (y, t₀) ∈ parabolicCylinder x₀ t₀ ρ := by
      rw [parabolicCylinder]
      exact ⟨hy, ⟨by nlinarith only [sq_pos_of_pos hρ], le_rfl⟩⟩
    exact (hcyl hz).1
  have hT : T ⊆ J := by
    intro s hs
    have hs' : s ∈ Ioc (t₀ - ρ ^ 2) t₀ := by simpa [T] using hs
    have hx : x₀ ∈ B := by
      dsimp [B]
      rw [mem_vec3Ball]
      simpa [vec3EuclideanNorm_zero] using hρ
    have hz : (x₀, s) ∈ parabolicCylinder x₀ t₀ ρ := by
      rw [parabolicCylinder]
      exact ⟨hx, hs'⟩
    exact (hcyl hz).2
  have hfglobal : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.2.1
  have hfprod' : AEStronglyMeasurable f
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hfglobal
  have hfprod : AEStronglyMeasurable f
      ((volume.restrict B).prod (volume.restrict T)) :=
    hfprod'.mono_measure
      (Measure.prod_mono (Measure.restrict_mono_set volume hB)
        (Measure.restrict_mono_set volume hT))
  have hFpow : AEMeasurable
      (fun z : Vec3 × ℝ => ‖f z‖ₑ ^ q)
      ((volume.restrict B).prod (volume.restrict T)) :=
    hfprod.enorm.pow_const q
  have hFtime : AEMeasurable (fun s : ℝ =>
      ∫⁻ x in B, ‖f (x, s)‖ₑ ^ q) (volume.restrict T) :=
    hFpow.lintegral_prod_left'
  have htotal : (∫⁻ s in T, ∫⁻ x in B, ‖f (x, s)‖ₑ ^ q) =
      ∫⁻ w in parabolicCylinder x₀ t₀ ρ, ‖f w‖ₑ ^ q := by
    have hprod : (∫⁻ w in B ×ˢ T, ‖f w‖ₑ ^ q) =
        ∫⁻ s in T, ∫⁻ x in B, ‖f (x, s)‖ₑ ^ q := by
      rw [show volume.restrict (B ×ˢ T) =
          (volume.restrict B).prod (volume.restrict T) by
        rw [Measure.prod_restrict B T,
          MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]]
      rw [MeasureTheory.lintegral_prod _ hFpow]
      rw [MeasureTheory.lintegral_lintegral_swap hFpow]
    calc
      _ = ∫⁻ w in B ×ˢ T, ‖f w‖ₑ ^ q := hprod.symm
      _ = ∫⁻ w in parabolicCylinder x₀ t₀ ρ, ‖f w‖ₑ ^ q := by
        rw [parabolicCylinder, MeasureTheory.Measure.volume_eq_prod Vec3 ℝ,
          CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
        rfl
  have htotal_lt : (∫⁻ s in T, ∫⁻ x in B, ‖f (x, s)‖ₑ ^ q) < ⊤ := by
    rw [htotal]
    exact sws_force_norm_integral_lt_top_local hsol hρ hsub
  have hIae : ∀ᵐ s ∂volume.restrict T,
      (∫⁻ x in B, ‖f (x, s)‖ₑ ^ q) < ⊤ :=
    ae_lt_top' hFtime (ne_of_lt htotal_lt)
  filter_upwards [hfprod.prodMk_right, hIae] with s hfs hIf
  exact ⟨hfs, hIf⟩

/-! ### Step 2: the two families of `L^q` sources -/

/-- The native Euclidean norm `vecEuclideanNorm` agrees with `vec3EuclideanNorm`. -/
private theorem vecEuclideanNorm_eq_vec3_local (v : Vec3) :
    vecEuclideanNorm v = vec3EuclideanNorm v := by
  simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/-- Measurability transfers from a restricted measure to the full measure when the function
vanishes off the measurable set. -/
private theorem aestronglyMeasurable_of_restrict_of_support_local
    {h : Vec3 → ℝ} {s : Set Vec3} (hs : MeasurableSet s)
    (hmeas : AEStronglyMeasurable h (volume.restrict s))
    (hsupp : Function.support h ⊆ s) :
    AEStronglyMeasurable h volume := by
  exact _root_.CKN.Foundation.Measure.aestronglyMeasurable_of_restrict_of_support hs hmeas hsupp

/-- An `L^q` function on a restricted measure whose support is contained in the restricting
set is `L^q` on the full measure. -/
private theorem memLp_volume_of_memLp_restrict_of_support_q_local
    {h : Vec3 → ℝ} {s : Set Vec3} {q : ℝ}
    (hmeas : AEStronglyMeasurable h volume) (hsupp : Function.support h ⊆ s)
    (hh : MemLp h (ENNReal.ofReal q) (volume.restrict s)) :
    MemLp h (ENNReal.ofReal q) volume := by
  rw [memLp_iff] at hh ⊢
  rwa [eLpNorm_restrict_eq_of_support_subset hmeas hsupp] at hh

/-- The two families of sources `η fⱼ` and `(∂ⱼ η) fⱼ` built from a smooth cutoff supported
in a ball and a slice of the force are `L^q`, for `6/5 ≤ q`. -/
private theorem force_sources_memLp_of_slice_data_local
    {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {x₀ : Vec3} {ρ s q : ℝ}
    (hq : 6 / 5 ≤ q)
    (hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηderiv : ∀ j y, |spatialDeriv η j y| ≤ cutoffGradientConstant / ρ)
    (hηsupport : tsupport η ⊆ vec3Ball x₀ ρ)
    (hηbound : ∀ y, |η y| ≤ 1)
    (hf : AEStronglyMeasurable (fun y : Vec3 => f (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hI : (∫⁻ y in vec3Ball x₀ ρ,
      ‖f (y, s)‖ₑ ^ q) < ∞)
    (hsource₇ : ∀ j : Fin 3, AEStronglyMeasurable
      (fun y => η y * f (y, s) j) volume) :
    (∀ j : Fin 3, MemLp (fun y => η y * f (y, s) j)
      (ENNReal.ofReal q) volume) ∧
    (∀ j : Fin 3, MemLp (fun y => spatialDeriv η j y * f (y, s) j)
      (ENNReal.ofReal q) volume) := by
  let B : Set Vec3 := vec3Ball x₀ ρ
  have hq0 : 0 < q := by linarith only [hq]
  have : IsFiniteMeasure (volume.restrict B) :=
    ⟨by
      simpa only [Measure.restrict_apply_univ, B] using
        (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top
          (x := x₀) (r := ρ))⟩
  have hF : MemLp (fun y : Vec3 => f (y, s))
      (ENNReal.ofReal q) (volume.restrict B) := by
    rw [memLp_iff, eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hq0).ne'
      ENNReal.ofReal_ne_top hf, eLpNorm'_eq_lintegral_enorm]
    have hI' : (∫⁻ y in B, ‖f (y, s)‖ₑ ^ (ENNReal.ofReal q).toReal) < ⊤ := by
      simpa only [B, ENNReal.toReal_ofReal hq0.le] using hI
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt hI')
  have hcomponent (j : Fin 3) : MemLp (fun y : Vec3 => f (y, s) j)
      (ENNReal.ofReal q) (volume.restrict B) := by
    apply hF.of_le
      ((ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hf)
    filter_upwards [] with y
    change ‖f (y, s) j‖ ≤ ‖f (y, s)‖
    exact norm_le_pi_norm (f (y, s)) j
  have hsource₇_support (j : Fin 3) :
      Function.support (fun y : Vec3 => η y * f (y, s) j) ⊆ B := by
    intro y hy
    by_contra hyB
    apply hy
    change η y * f (y, s) j = 0
    have hzero : η y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hηy => hyB (hηsupport hηy))
    rw [hzero, zero_mul]
  have hsource₈_support (j : Fin 3) :
      Function.support
        (fun y : Vec3 => spatialDeriv η j y * f (y, s) j) ⊆ B := by
    intro y hy
    by_contra hyB
    apply hy
    change spatialDeriv η j y * f (y, s) j = 0
    have hzero : spatialDeriv η j y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hηy => hyB
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport hηy))
    rw [hzero, zero_mul]
  have hsource₇_mem (j : Fin 3) : MemLp
      (fun y : Vec3 => η y * f (y, s) j)
      (ENNReal.ofReal q) (volume.restrict B) := by
    apply (hcomponent j).of_le
      ((hsource₇ j).mono_measure Measure.restrict_le_self)
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [Real.norm_eq_abs, one_mul] using
      (mul_le_mul_of_nonneg_right (hηbound y) (abs_nonneg (f (y, s) j)))
  have hsource₇_mem_global (j : Fin 3) : MemLp
      (fun y : Vec3 => η y * f (y, s) j)
      (ENNReal.ofReal q) volume := by
    exact memLp_volume_of_memLp_restrict_of_support_q_local
      ((hsource₇ j)) (hsource₇_support j) (hsource₇_mem j)
  have hderiv_meas (j : Fin 3) : AEStronglyMeasurable
      (spatialDeriv η j) volume := by
    have hηd := contDiff_spatialDeriv_smooth hηsmooth j
    exact hηd.continuous.aestronglyMeasurable
  have hsource₈_int (j : Fin 3) : Integrable
      (fun y : Vec3 => spatialDeriv η j y * f (y, s) j) volume := by
    have hqone : 1 ≤ q := by linarith only [hq]
    have hmul := (hcomponent j).integrable
      (ENNReal.one_le_ofReal.2 hqone)
    have hderiv_meas_B : AEStronglyMeasurable (spatialDeriv η j)
        (volume.restrict B) :=
      (hderiv_meas j).mono_measure Measure.restrict_le_self
    have hmul' := hmul.mul_bdd
      hderiv_meas_B
      (Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using
          hηderiv j y))
    have hmul'' : Integrable
        (fun y : Vec3 => spatialDeriv η j y * f (y, s) j)
        (volume.restrict B) := by
      simpa only [mul_comm] using hmul'
    exact decomposition_full_of_on_sws hmul''
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := fun y : Vec3 => f (y, s) j)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport))
  constructor
  · exact fun j => hsource₇_mem_global j
  · intro j
    apply memLp_volume_of_memLp_restrict_of_support_q_local
      (hsource₈_int j).aestronglyMeasurable (hsource₈_support j)
    let c : ℝ := max (cutoffGradientConstant / ρ) 0
    have hc : 0 ≤ c := le_max_right _ _
    have hcmem : MemLp (fun y : Vec3 => c * f (y, s) j)
        (ENNReal.ofReal q) (volume.restrict B) := (hcomponent j).const_mul c
    apply hcmem.of_le
      ((hsource₈_int j).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc] using
      (mul_le_mul_of_nonneg_right
        ((hηderiv j y).trans (le_max_left _ _)) (abs_nonneg (f (y, s) j)))

/-! ### Step 3: local support and ball-inclusion helpers -/

/-- The spatial derivative of the convolution cutoff obeys the gradient bound. -/
private theorem cutoff_spatialDeriv_bound_local (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec3) (i : Fin 3) :
    |spatialDeriv (mollifiedBallCutoff x₀ hρ) i y| ≤
      cutoffGradientConstant / ρ := by
  have hg := mollifiedBallCutoff_gradient_bound x₀ hρ y
  have hi := abs_apply_le_vecEuclideanNorm
    (classicalGradient (mollifiedBallCutoff x₀ hρ) y) i
  have hle := hi.trans hg
  simpa [spatialDeriv, classicalGradient, classicalGradient_apply, basisVec_apply] using hle

/-- The support of the convolution cutoff is contained in the open ball of the same radius. -/
private theorem cutoff_tsupport_subset_vec3Ball_local (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (mollifiedBallCutoff x₀ hρ) ⊆ vec3Ball x₀ ρ := by
  intro y hy
  have houter := mollifiedBallCutoff_tsupport_subset_outer x₀ hρ hy
  apply (mem_vec3Ball).2
  have hlt := (mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by positivity : (0 : ℝ) < 3 * ρ / 4)).1 houter
  rw [vecEuclideanNorm_eq_vec3_local] at hlt
  exact lt_of_lt_of_le hlt (by linarith only [hρ])

/-- A round ball about `x` is contained in the round ball about the origin of radius
`vec3EuclideanNorm x + R`. -/
private theorem euclideanBall_subset_origin_local (x : Vec3) {R : ℝ} (hR : 0 < R) :
    euclideanBall x R ⊆ euclideanBall (0 : Vec3) (vec3EuclideanNorm x + R) := by
  intro y hy
  have hρ' : 0 < vec3EuclideanNorm x + R := by
    linarith only [hR, vec3EuclideanNorm_nonneg x]
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hρ', vecEuclideanNorm_eq_vec3_local,
    sub_zero]
  have hy' : vec3EuclideanNorm (y - x) < R := by
    rw [← vecEuclideanNorm_eq_vec3_local]
    exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hy
  have htri : vec3EuclideanNorm y ≤
      vec3EuclideanNorm (y - x) + vec3EuclideanNorm x := by
    rw [show y = (y - x) + x by abel]
    simpa [vec3EuclideanNorm_eq_l2, WithLp.toLp_add] using
      (norm_add_le (WithLp.toLp 2 (y - x)) (WithLp.toLp 2 x))
  linarith only [htri, hy']

/-! ### The time-slice `L^{3/2}` statement for the force potentials -/

/-- `prop:lin34` (force side), in the form consumed by the quantitative Hölder estimate: for
almost every time `s` in the lower half of a parabolic cylinder whose closure lies in the
carrier, the force potentials `p₇ + p₈` of `lem:pk-bounds` built from the ball cutoff at
`z` and radius `ρ` are `L^{3/2}` on every round ball of the spatial slice. -/
theorem lin34_force_slice_memLp_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ (x : Vec3) (R : ℝ), 0 < R →
        MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
            pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x R)) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  have hq : 6 / 5 ≤ q := by linarith only [hsol.2.2.2.1]
  have hR₀ : 0 < vec3EuclideanNorm z.1 + ρ := by
    linarith only [hρ, vec3EuclideanNorm_nonneg z.1]
  have hsupport : tsupport η ⊆ vec3Ball z.1 ρ :=
    cutoff_tsupport_subset_vec3Ball_local z.1 hρ
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η := mollifiedBallCutoff_smooth z.1 hρ
  have hηbound : ∀ y, |η y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (mollifiedBallCutoff_nonneg z.1 hρ y)]
    exact mollifiedBallCutoff_le_one z.1 hρ y
  have hηmeas : AEStronglyMeasurable η volume := hηsmooth.continuous.aestronglyMeasurable
  have hηderiv : ∀ j y, |spatialDeriv η j y| ≤ cutoffGradientConstant / ρ :=
    fun j y => cutoff_spatialDeriv_bound_local z.1 hρ y j
  filter_upwards [force_slice_data_local (x₀ := z.1) (t₀ := z.2) (ρ := ρ) hsol hρ hsub]
    with s hdata
  obtain ⟨hf, hI⟩ := hdata
  have hsource₇ : ∀ j : Fin 3, AEStronglyMeasurable
      (fun y => η y * f (y, s) j) volume := by
    intro j
    have hηB : AEStronglyMeasurable η (volume.restrict (vec3Ball z.1 ρ)) :=
      hηmeas.mono_measure Measure.restrict_le_self
    have hcompB : AEStronglyMeasurable (fun y : Vec3 => f (y, s) j)
        (volume.restrict (vec3Ball z.1 ρ)) := by
      simpa only [ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hf
    have hmulB : AEStronglyMeasurable (fun y : Vec3 => η y * f (y, s) j)
        (volume.restrict (vec3Ball z.1 ρ)) := hηB.mul hcompB
    refine aestronglyMeasurable_of_restrict_of_support_local
      (vec3Ball_measurable z.1 ρ) hmulB ?_
    intro y hy
    by_contra hyB
    apply hy
    change η y * f (y, s) j = 0
    have hzero : η y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hηy => hyB (hsupport hηy))
    rw [hzero, zero_mul]
  obtain ⟨hdata₇, hdata₈⟩ := force_sources_memLp_of_slice_data_local
    (f := f) (η := η) (x₀ := z.1) (ρ := ρ) (s := s) (q := q)
    hq hηsmooth hηderiv hsupport hηbound hf hI hsource₇
  have hsupp₇ : ∀ (j : Fin 3) (y : Vec3),
      y ∉ Metric.closedBall (0 : Vec3) (vec3EuclideanNorm z.1 + ρ) →
        η y * f (y, s) j = 0 := by
    intro j y hy
    have hyB : y ∉ vec3Ball z.1 ρ := fun h =>
      hy ((vec3Ball_subset_closedBall_zero z.1 ρ) h)
    have hzero : η y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hηy => hyB (hsupport hηy))
    rw [hzero, zero_mul]
  have hsupp₈ : ∀ (j : Fin 3) (y : Vec3),
      y ∉ Metric.closedBall (0 : Vec3) (vec3EuclideanNorm z.1 + ρ) →
        spatialDeriv η j y * f (y, s) j = 0 := by
    intro j y hy
    have hyB : y ∉ vec3Ball z.1 ρ := fun h =>
      hy ((vec3Ball_subset_closedBall_zero z.1 ρ) h)
    have hzero : spatialDeriv η j y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hηy => hyB
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hsupport hηy))
    rw [hzero, zero_mul]
  have hmem := (pressureP7_add_pressureP8_memLp_and_lpNorm_growth
    (η := η) (f := f) (s := s) (R := vec3EuclideanNorm z.1 + ρ) (q := q)
    hR₀ hq hdata₇ hsupp₇ hdata₈ hsupp₈).1
  intro x R hR
  exact (hmem (vec3EuclideanNorm x + R)
      (by linarith only [hR, vec3EuclideanNorm_nonneg x])).mono_measure
    (Measure.restrict_mono_set volume (euclideanBall_subset_origin_local x hR))

end CKN
