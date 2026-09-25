/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayShell
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayGeometry
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayGrowthSum

/-!
# Linear growth of local `L^{3/2}` norms from decay at infinity

The Liouville step of the pressure identification needs its residual to satisfy
`‖r‖_{L^{3/2}(B_ρ)} ≤ C * (1 + ρ)` on the round balls `euclideanBall 0 ρ`.  This
file turns the pointwise decay `|h x| ≤ M * ‖x‖⁻¹` of a Newtonian potential of
compactly supported data into exactly that bound, with an explicit constant
built from the local norm near the origin and the universal ball constant
`invNormBallConstant` of `CKN.Pressure.PotentialDecayShell`.

This is the decay-at-infinity input to the uniqueness half of the Newtonian
representation `ext:newtonian` of the paper, whose proof applies Liouville's
theorem to a harmonic function that tends to zero in the `L^{3/2}` average
sense at infinity.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

private lemma norm_le_vecEuclideanNorm_vec3 (x : Vec3) :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖x i‖₊) ≤
      ⟨vecEuclideanNorm x, vecEuclideanNorm_nonneg x⟩ := by
    apply Finset.sup_le
    intro i _hi
    exact_mod_cast abs_apply_le_vecEuclideanNorm x i
  exact_mod_cast hnn

/-- The round Euclidean ball sits inside the ambient ball of the same radius. -/
theorem euclideanBall_subset_ball {ρ : ℝ} (hρ : 0 < ρ) :
    euclideanBall (0 : Vec3) ρ ⊆ Metric.ball (0 : Vec3) ρ := by
  intro x hx
  have h := (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).1 hx
  rw [sub_zero] at h
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_le_of_lt (norm_le_vecEuclideanNorm_vec3 x) h

private lemma exponent_ne_zero : (ENNReal.ofReal (3 / 2 : ℝ)) ≠ 0 := by
  rw [Ne, ENNReal.ofReal_eq_zero, not_le]
  norm_num

private lemma exponent_toReal : (ENNReal.ofReal (3 / 2 : ℝ)).toReal = (3 / 2 : ℝ) := by
  rw [ENNReal.toReal_ofReal]
  norm_num

private lemma one_le_exponent : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ) := by
  rw [ENNReal.one_le_ofReal]
  norm_num

/-- The `L^{3/2}` norm of the radial profile `M * ‖x‖⁻¹` over the round ball of
radius `ρ` grows linearly in `ρ`. -/
theorem eLpNorm_const_mul_inv_norm_euclideanBall_le
    {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 < ρ) :
    eLpNorm (fun x : Vec3 => M * ‖x‖⁻¹) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
      ENNReal.ofReal (M * invNormBallConstant ^ (2 / 3 : ℝ) * ρ) := by
  have hmeasfun : Measurable (fun x : Vec3 => M * ‖x‖⁻¹) := by fun_prop
  have hpoint : ∀ x : Vec3, ‖M * ‖x‖⁻¹‖ₑ ^ (3 / 2 : ℝ) =
      ENNReal.ofReal (M ^ (3 / 2 : ℝ)) *
        ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ)) := by
    intro x
    have hnn : (0 : ℝ) ≤ M * ‖x‖⁻¹ := by positivity
    rw [Real.enorm_eq_ofReal hnn,
      ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num),
      Real.mul_rpow hM (by positivity),
      Real.inv_rpow (norm_nonneg x), ← Real.rpow_neg (norm_nonneg x),
      ENNReal.ofReal_mul (Real.rpow_nonneg hM _)]
  have hint : ∫⁻ x in euclideanBall (0 : Vec3) ρ,
        ‖M * ‖x‖⁻¹‖ₑ ^ (3 / 2 : ℝ) ≤
      ENNReal.ofReal (M ^ (3 / 2 : ℝ) *
        (invNormBallConstant * ρ ^ (3 / 2 : ℝ))) := by
    calc ∫⁻ x in euclideanBall (0 : Vec3) ρ, ‖M * ‖x‖⁻¹‖ₑ ^ (3 / 2 : ℝ)
        = ∫⁻ x in euclideanBall (0 : Vec3) ρ,
            ENNReal.ofReal (M ^ (3 / 2 : ℝ)) *
              ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ)) :=
          lintegral_congr (fun x => hpoint x)
      _ = ENNReal.ofReal (M ^ (3 / 2 : ℝ)) *
            ∫⁻ x in euclideanBall (0 : Vec3) ρ,
              ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ)) :=
          lintegral_const_mul _ (by fun_prop)
      _ ≤ ENNReal.ofReal (M ^ (3 / 2 : ℝ)) *
            ∫⁻ x in Metric.ball (0 : Vec3) ρ,
              ENNReal.ofReal (‖x‖ ^ (-(3 / 2) : ℝ)) := by
          gcongr
          exact euclideanBall_subset_ball hρ
      _ = ENNReal.ofReal (M ^ (3 / 2 : ℝ)) *
            ENNReal.ofReal (invNormBallConstant * ρ ^ (3 / 2 : ℝ)) := by
          rw [lintegral_ball_inv_norm_rpow_eq_const hρ]
      _ = ENNReal.ofReal (M ^ (3 / 2 : ℝ) *
            (invNormBallConstant * ρ ^ (3 / 2 : ℝ))) :=
          (ENNReal.ofReal_mul (Real.rpow_nonneg hM _)).symm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal exponent_ne_zero ENNReal.ofReal_ne_top
    hmeasfun.aestronglyMeasurable, exponent_toReal,
    show (1 : ℝ) / (3 / 2 : ℝ) = (2 / 3 : ℝ) by norm_num]
  have hpow := ENNReal.rpow_le_rpow hint (by norm_num : (0 : ℝ) ≤ 2 / 3)
  refine hpow.trans_eq ?_
  have hcr : (0 : ℝ) ≤ invNormBallConstant * ρ ^ (3 / 2 : ℝ) :=
    mul_nonneg invNormBallConstant_nonneg (Real.rpow_nonneg hρ.le _)
  rw [ENNReal.ofReal_rpow_of_nonneg
    (mul_nonneg (Real.rpow_nonneg hM _) hcr) (by norm_num)]
  congr 1
  rw [Real.mul_rpow (Real.rpow_nonneg hM _) hcr,
    Real.mul_rpow invNormBallConstant_nonneg (Real.rpow_nonneg hρ.le _),
    ← Real.rpow_mul hM, ← Real.rpow_mul hρ.le]
  norm_num
  ring

/-- Splitting estimate: a function that is `L^{3/2}` on the ambient ball of
radius `2 * R` and decays like `M * ‖x‖⁻¹` outside it has `L^{3/2}` norm at most
`‖h‖_{L^{3/2}(B_{2R})} + M * invNormBallConstant ^ (2/3) * ρ` on the round ball
of radius `ρ`. -/
theorem eLpNorm_euclideanBall_le_of_inv_norm_decay
    {h : Vec3 → ℝ} {M R : ℝ} (hM : 0 ≤ M)
    (hmeas : AEStronglyMeasurable h volume)
    (hdecay : ∀ x : Vec3, 2 * R ≤ ‖x‖ → |h x| ≤ M * ‖x‖⁻¹)
    {ρ : ℝ} (hρ : 0 < ρ) :
    eLpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
      eLpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (Metric.ball (0 : Vec3) (2 * R))) +
        ENNReal.ofReal (M * invNormBallConstant ^ (2 / 3 : ℝ) * ρ) := by
  classical
  have hsm : MeasurableSet (Metric.ball (0 : Vec3) (2 * R)) := measurableSet_ball
  have hsplit : h = (Metric.ball (0 : Vec3) (2 * R)).indicator h +
      (Metric.ball (0 : Vec3) (2 * R))ᶜ.indicator h := by
    funext x
    by_cases hx : x ∈ Metric.ball (0 : Vec3) (2 * R)
    · have hx' : x ∉ (Metric.ball (0 : Vec3) (2 * R))ᶜ := by simpa using hx
      simp [Set.indicator_of_mem hx, Set.indicator_of_notMem hx']
    · have hx' : x ∈ (Metric.ball (0 : Vec3) (2 * R))ᶜ := hx
      simp [Set.indicator_of_notMem hx, Set.indicator_of_mem hx']
  have hbound1 : eLpNorm ((Metric.ball (0 : Vec3) (2 * R)).indicator h)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
      eLpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (Metric.ball (0 : Vec3) (2 * R))) := by
    have hres : (volume : Measure Vec3).restrict (euclideanBall (0 : Vec3) ρ) ≤
        volume := Measure.restrict_le_self
    have heq : eLpNorm ((Metric.ball (0 : Vec3) (2 * R)).indicator h)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume =
        eLpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (Metric.ball (0 : Vec3) (2 * R))) :=
      eLpNorm_indicator_eq_eLpNorm_restrict hsm
    exact (eLpNorm_mono_measure (p := ENNReal.ofReal (3 / 2 : ℝ))
      ((Metric.ball (0 : Vec3) (2 * R)).indicator h) hres).trans heq.le
  have hbound2 : eLpNorm ((Metric.ball (0 : Vec3) (2 * R))ᶜ.indicator h)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
      ENNReal.ofReal (M * invNormBallConstant ^ (2 / 3 : ℝ) * ρ) := by
    refine le_trans (eLpNorm_mono_real ?_ ?_)
      (eLpNorm_const_mul_inv_norm_euclideanBall_le hM hρ)
    · exact (hmeas.restrict).indicator hsm.compl
    · intro x
      by_cases hx : x ∈ Metric.ball (0 : Vec3) (2 * R)
      · have hx' : x ∉ (Metric.ball (0 : Vec3) (2 * R))ᶜ := by simpa using hx
        rw [Set.indicator_of_notMem hx', norm_zero]
        positivity
      · have hx' : x ∈ (Metric.ball (0 : Vec3) (2 * R))ᶜ := hx
        have hxn : 2 * R ≤ ‖x‖ := by
          simp only [Metric.mem_ball, dist_zero_right, not_lt] at hx
          exact hx
        rw [Set.indicator_of_mem hx']
        simpa only [Real.norm_eq_abs] using hdecay x hxn
  calc eLpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))
      = eLpNorm ((Metric.ball (0 : Vec3) (2 * R)).indicator h +
          (Metric.ball (0 : Vec3) (2 * R))ᶜ.indicator h)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) := by rw [← hsplit]
    _ ≤ eLpNorm ((Metric.ball (0 : Vec3) (2 * R)).indicator h)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) +
        eLpNorm ((Metric.ball (0 : Vec3) (2 * R))ᶜ.indicator h)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
      eLpNorm_add_le one_le_exponent
    _ ≤ _ := add_le_add hbound1 hbound2

/-- The explicit growth constant attached to an inverse-distance decay
estimate: the local norm near the origin plus the decay constant times the
universal ball constant. -/
def invNormGrowthConstant (h : Vec3 → ℝ) (M R : ℝ) : ℝ :=
  lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) (2 * R))) +
    M * invNormBallConstant ^ (2 / 3 : ℝ)

theorem invNormGrowthConstant_nonneg {h : Vec3 → ℝ} {M R : ℝ} (hM : 0 ≤ M) :
    0 ≤ invNormGrowthConstant h M R := by
  have h1 : (0 : ℝ) ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) (2 * R))) := lpNorm_nonneg
  have h2 : (0 : ℝ) ≤ M * invNormBallConstant ^ (2 / 3 : ℝ) :=
    mul_nonneg hM (Real.rpow_nonneg invNormBallConstant_nonneg _)
  rw [invNormGrowthConstant]
  linarith only [h1, h2]

/-- Membership in `L^{3/2}` of every round ball, for a function that is
`L^{3/2}` near the origin and decays like `M * ‖x‖⁻¹` at infinity. -/
theorem memLp_euclideanBall_of_inv_norm_decay
    {h : Vec3 → ℝ} {M R : ℝ} (hM : 0 ≤ M)
    (hmeas : AEStronglyMeasurable h volume)
    (hnear : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) (2 * R))))
    (hdecay : ∀ x : Vec3, 2 * R ≤ ‖x‖ → |h x| ≤ M * ‖x‖⁻¹)
    {ρ : ℝ} (hρ : 0 < ρ) :
    MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) := by
  rw [memLp_iff]
  refine lt_of_le_of_lt
    (eLpNorm_euclideanBall_le_of_inv_norm_decay hM hmeas hdecay hρ) ?_
  exact ENNReal.add_lt_top.2 ⟨memLp_iff.1 hnear, ENNReal.ofReal_lt_top⟩

/-- Linear growth of the local `L^{3/2}` norms: this is the exact shape of the
growth hypothesis of the Liouville theorem for weakly harmonic functions. -/
theorem lpNorm_euclideanBall_le_of_inv_norm_decay
    {h : Vec3 → ℝ} {M R : ℝ} (hM : 0 ≤ M)
    (hmeas : AEStronglyMeasurable h volume)
    (hnear : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) (2 * R))))
    (hdecay : ∀ x : Vec3, 2 * R ≤ ‖x‖ → |h x| ≤ M * ‖x‖⁻¹)
    {ρ : ℝ} (hρ : 0 < ρ) :
    lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
      invNormGrowthConstant h M R * (1 + ρ) := by
  have hle := eLpNorm_euclideanBall_le_of_inv_norm_decay hM hmeas hdecay hρ
  have hKnn : (0 : ℝ) ≤ M * invNormBallConstant ^ (2 / 3 : ℝ) * ρ := by
    have h2 : (0 : ℝ) ≤ M * invNormBallConstant ^ (2 / 3 : ℝ) :=
      mul_nonneg hM (Real.rpow_nonneg invNormBallConstant_nonneg _)
    exact mul_nonneg h2 hρ.le
  have hfin : eLpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (Metric.ball (0 : Vec3) (2 * R))) +
      ENNReal.ofReal (M * invNormBallConstant ^ (2 / 3 : ℝ) * ρ) ≠ ⊤ :=
    (ENNReal.add_lt_top.2 ⟨memLp_iff.1 hnear, ENNReal.ofReal_lt_top⟩).ne
  have htoReal := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_add (memLp_iff.1 hnear).ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hKnn, toReal_eLpNorm, toReal_eLpNorm] at htoReal
  have hA : (0 : ℝ) ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) (2 * R))) := lpNorm_nonneg
  have hAρ : (0 : ℝ) ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) (2 * R))) * ρ :=
    mul_nonneg hA hρ.le
  have hMc : (0 : ℝ) ≤ M * invNormBallConstant ^ (2 / 3 : ℝ) :=
    mul_nonneg hM (Real.rpow_nonneg invNormBallConstant_nonneg _)
  rw [invNormGrowthConstant]
  nlinarith only [htoReal, hAρ, hMc]

/-- The pair of hypotheses consumed by
`weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth`, produced from an
inverse-distance decay estimate centred at the origin. -/
theorem memLp_and_lpNorm_linear_growth_of_inv_norm_decay
    {h : Vec3 → ℝ} {M R : ℝ} (hM : 0 ≤ M)
    (hmeas : AEStronglyMeasurable h volume)
    (hnear : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) (2 * R))))
    (hdecay : ∀ x : Vec3, 2 * R ≤ ‖x‖ → |h x| ≤ M * ‖x‖⁻¹) :
    (∀ ρ : ℝ, 0 < ρ → MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          invNormGrowthConstant h M R * (1 + ρ) :=
  ⟨fun _ρ hρ => memLp_euclideanBall_of_inv_norm_decay hM hmeas hnear hdecay hρ,
    fun _ρ hρ => lpNorm_euclideanBall_le_of_inv_norm_decay hM hmeas hnear hdecay hρ⟩

/-- The same conclusion from a decay estimate centred at an arbitrary point
`x₀`, obtained by re-centring at the origin. -/
theorem memLp_and_lpNorm_linear_growth_of_inv_norm_decay_centre
    {h : Vec3 → ℝ} {x₀ : Vec3} {M R : ℝ} (hM : 0 ≤ M) (hR : 0 < R)
    (hmeas : AEStronglyMeasurable h volume)
    (hnear : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) (2 * (2 * R + 2 * ‖x₀‖)))))
    (hdecay : ∀ z : Vec3, 2 * R ≤ ‖z - x₀‖ → |h z| ≤ M * ‖z - x₀‖⁻¹) :
    (∀ ρ : ℝ, 0 < ρ → MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          invNormGrowthConstant h (2 * M) (2 * R + 2 * ‖x₀‖) * (1 + ρ) := by
  refine memLp_and_lpNorm_linear_growth_of_inv_norm_decay
    (by linarith only [hM] : (0 : ℝ) ≤ 2 * M) hmeas hnear ?_
  intro x hx
  exact inv_norm_decay_recentre hM hR hdecay hx

/-! ### Compactly supported and globally `L^{3/2}` data

The remaining pieces of a pressure residual are either compactly supported
`L^{3/2}` functions (such as `η p`) or globally `L^{3/2}` functions (such as the
image of `η U` under the second-order singular integral).  Both satisfy the
linear-growth bound with constant their global `L^{3/2}` norm. -/

theorem memLp_euclideanBall_family_add {f g : Vec3 → ℝ}
    (hf : ∀ ρ : ℝ, 0 < ρ → MemLp f (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hg : ∀ ρ : ℝ, 0 < ρ → MemLp g (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ))) :
    ∀ ρ : ℝ, 0 < ρ → MemLp (f + g) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
  fun ρ hρ => (hf ρ hρ).add (hg ρ hρ)

theorem memLp_euclideanBall_family_sub {f g : Vec3 → ℝ}
    (hf : ∀ ρ : ℝ, 0 < ρ → MemLp f (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hg : ∀ ρ : ℝ, 0 < ρ → MemLp g (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ))) :
    ∀ ρ : ℝ, 0 < ρ → MemLp (f - g) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
  fun ρ hρ => (hf ρ hρ).sub (hg ρ hρ)

theorem memLp_euclideanBall_family_sum {ι : Type*} {s : Finset ι}
    {f : ι → Vec3 → ℝ}
    (hf : ∀ i ∈ s, ∀ ρ : ℝ, 0 < ρ → MemLp (f i) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ))) :
    ∀ ρ : ℝ, 0 < ρ → MemLp (∑ i ∈ s, f i) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
  fun ρ hρ => memLp_finsetSum' s (fun i hi => hf i hi ρ hρ)

/-! ### Converting higher-order far-field decay to inverse-distance decay

The first and second derivative potentials decay like `‖x - x₀‖⁻²` and
`‖x - x₀‖⁻³`; on the far region `2 * R ≤ ‖x - x₀‖` these are stronger than the
inverse-distance decay required by the growth estimate. -/

/-- A far-field bound of the shape `A / ‖x - x₀‖ ^ 2` gives inverse-distance
decay with constant `A / (2 * R)`. -/
theorem inv_norm_decay_of_div_norm_sq {h : Vec3 → ℝ} {x₀ : Vec3} {A R : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A)
    (hd : ∀ x : Vec3, 2 * R ≤ ‖x - x₀‖ → |h x| ≤ A / ‖x - x₀‖ ^ 2) :
    ∀ x : Vec3, 2 * R ≤ ‖x - x₀‖ → |h x| ≤ (A / (2 * R)) * ‖x - x₀‖⁻¹ := by
  intro x hx
  have hR2 : (0 : ℝ) < 2 * R := by linarith only [hR]
  have hpos : (0 : ℝ) < ‖x - x₀‖ := lt_of_lt_of_le hR2 hx
  have heq : (A / (2 * R)) * ‖x - x₀‖⁻¹ = A / ((2 * R) * ‖x - x₀‖) := by
    field_simp
  rw [heq]
  refine (hd x hx).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hgap : (0 : ℝ) ≤ ‖x - x₀‖ - 2 * R := by linarith only [hx]
  have hprod : (0 : ℝ) ≤ A * (‖x - x₀‖ - 2 * R) * ‖x - x₀‖ :=
    mul_nonneg (mul_nonneg hA hgap) hpos.le
  nlinarith only [hprod]

end CKN
