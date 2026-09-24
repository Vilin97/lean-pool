/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyC1
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyEnergy
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyGradient
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyPoincare
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyScaling
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Smooth

/-!
# Unit-ball Sobolev localization through the two-reflection extension

The compactly supported cutoff of the `C¹` extension is the smooth input for the
same-ball estimate.  This module records the localization step explicitly; the
remaining reduction of its outer-ball terms to the original ball is kept separate.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem eLpNorm_two_sq {β : Type*} [NormedAddCommGroup β]
    (f : Vec 3 → β) (s : Set (Vec 3)) (hf : Continuous f) :
    eLpNorm f 2 (volume.restrict s) ^ (2 : ℝ) =
      ∫⁻ x in s, ENNReal.ofReal (‖f x‖ ^ 2) ∂volume := by
  change eLpNorm f (↑(2 : NNReal)) (volume.restrict s) ^ (2 : ℝ) = _
  have hm : AEStronglyMeasurable f (volume.restrict s) :=
    hf.aestronglyMeasurable
  rw [eLpNorm_nnreal_eq_lintegral (p := (2 : NNReal)) (by norm_num) hm]
  rw [← ENNReal.rpow_mul]
  norm_num

private theorem eLpNorm_two_le_of_energy {β : Type*} [NormedAddCommGroup β]
    (f g : Vec 3 → β) (s t : Set (Vec 3)) (K : ℝ≥0∞)
    (hf : Continuous f) (hg : Continuous g) (_ : 0 ≤ K)
    (henergy :
      ∫⁻ x in s, ENNReal.ofReal (‖f x‖ ^ 2) ∂volume ≤
        K * ∫⁻ y in t, ENNReal.ofReal (‖g y‖ ^ 2) ∂volume) :
    eLpNorm f 2 (volume.restrict s) ≤
      K ^ (1 / 2 : ℝ) * eLpNorm g 2 (volume.restrict t) := by
  have hsq :
      eLpNorm f 2 (volume.restrict s) ^ (2 : ℕ) ≤
        K * eLpNorm g 2 (volume.restrict t) ^ (2 : ℕ) := by
    have hf2 := eLpNorm_two_sq f s hf
    have hg2 := eLpNorm_two_sq g t hg
    norm_num at hf2 hg2 ⊢
    rw [hf2, hg2]
    have hf2' :
        (∫⁻ x in s, ‖f x‖ₑ ^ (2 : ℕ) ∂volume) =
          ∫⁻ x in s, ENNReal.ofReal (‖f x‖ ^ 2) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [] with x
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
    have hg2' :
        (∫⁻ x in t, ‖g x‖ₑ ^ (2 : ℕ) ∂volume) =
          ∫⁻ x in t, ENNReal.ofReal (‖g x‖ ^ 2) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [] with x
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [hf2', hg2']
    exact henergy
  have hsq' := ENNReal.rpow_le_rpow hsq
    (by positivity : 0 ≤ (1 / 2 : ℝ))
  calc
    eLpNorm f 2 (volume.restrict s) =
        (eLpNorm f 2 (volume.restrict s) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ ≤ (K * eLpNorm g 2 (volume.restrict t) ^ (2 : ℕ)) ^
        (1 / 2 : ℝ) := hsq'
    _ = K ^ (1 / 2 : ℝ) * eLpNorm g 2 (volume.restrict t) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

private theorem lintegral_norm_sq_eq_outer_sq {β : Type*} [NormedAddCommGroup β]
    (f : Vec 3 → β) (s : Set (Vec 3)) :
    ∫⁻ x in s, ENNReal.ofReal (‖f x‖ ^ 2) ∂volume =
      ∫⁻ x in s, ENNReal.ofReal ‖f x‖ ^ 2 ∂volume := by
  apply lintegral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.ofReal_pow (norm_nonneg (f x))]

private theorem euclideanBall_two_eq_closedBall_one_union_outer :
    euclideanBall (0 : Vec 3) 2 =
      euclideanClosedBall (0 : Vec 3) 1 ∪ seeleyOuterAnnulus := by
  ext x
  constructor
  · intro hx
    have hnorm : vecEuclideanNorm x < 2 := by
      simpa only [sub_zero] using
        (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
    by_cases hle : vecEuclideanNorm x ≤ 1
    · left
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2 (by
        simpa only [sub_zero] using hle)
    · right
      exact ⟨lt_of_not_ge hle, hnorm⟩
  · intro hx
    have hnorm : vecEuclideanNorm x < 2 := by
      rcases hx with hx | hx
      · exact lt_of_le_of_lt
          (by simpa only [sub_zero] using
            (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).1 hx)
          (by norm_num)
      · exact hx.2
    exact (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2 (by
      simpa only [sub_zero] using hnorm)

private theorem euclideanClosedBall_one_disjoint_outer :
    Disjoint (euclideanClosedBall (0 : Vec 3) 1) seeleyOuterAnnulus := by
  rw [Set.disjoint_left]
  intro x hxC hxO
  exact (not_lt_of_ge
    (by simpa only [sub_zero] using
      (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).1 hxC)) hxO.1

private theorem seeleyExtension_value_energy_ball_two_le
    (v : Vec 3 → ℝ) (c : ℝ) (hv : Continuous v) :
    ∫⁻ x in euclideanBall (0 : Vec 3) 2,
        ENNReal.ofReal |seeleyExtension (fun y => v y - c) x| ^ 2 ∂volume ≤
      (6337 : ℝ≥0∞) *
        ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal |v y - c| ^ 2 ∂volume := by
  rw [euclideanBall_two_eq_closedBall_one_union_outer,
    lintegral_union seeleyOuterAnnulus_measurableSet
      euclideanClosedBall_one_disjoint_outer]
  have hinner :
      (∫⁻ x in euclideanClosedBall (0 : Vec 3) 1,
        ENNReal.ofReal |seeleyExtension (fun y => v y - c) x| ^ 2 ∂volume) =
        ∫⁻ x in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal |v x - c| ^ 2 ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem
      (isClosed_euclideanClosedBall (0 : Vec 3) 1).measurableSet] with x hx
    rw [seeleyExtension_eq_on_closedBall hx]
  calc
    _ = (∫⁻ x in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal |seeleyExtension (fun y => v y - c) x| ^ 2 ∂volume) +
        ∫⁻ x in seeleyOuterAnnulus,
          ENNReal.ofReal |seeleyExtension (fun y => v y - c) x| ^ 2 ∂volume := rfl
    _ = (∫⁻ x in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal |v x - c| ^ 2 ∂volume) +
        ∫⁻ x in seeleyOuterAnnulus,
          ENNReal.ofReal |seeleyExtension (fun y => v y - c) x| ^ 2 ∂volume := by
      rw [hinner]
    _ ≤ (∫⁻ x in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal |v x - c| ^ 2 ∂volume) +
        6336 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal |v y - c| ^ 2 ∂volume := by
      exact add_le_add_right (seeleyExtension_value_energy_le v c hv) _
    _ = 6337 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal |v y - c| ^ 2 ∂volume := by ring

private theorem seeleyExtension_gradient_energy_ball_two_le
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) :
    ∫⁻ x in euclideanBall (0 : Vec 3) 2,
        ENNReal.ofReal (‖classicalGradient (seeleyExtension v) x‖ ^ 2) ∂volume ≤
      (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648 : ℝ≥0∞) *
        ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume := by
  rw [euclideanBall_two_eq_closedBall_one_union_outer,
    lintegral_union seeleyOuterAnnulus_measurableSet
      euclideanClosedBall_one_disjoint_outer]
  have hinner :
      (∫⁻ x in euclideanClosedBall (0 : Vec 3) 1,
        ENNReal.ofReal (‖classicalGradient (seeleyExtension v) x‖ ^ 2) ∂volume) =
        ∫⁻ x in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal (‖classicalGradient v x‖ ^ 2) ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem
      (isClosed_euclideanClosedBall (0 : Vec 3) 1).measurableSet] with x hx
    rw [seeleyExtension_classicalGradient_eq_of_mem_closedBall v hv hx]
  calc
    _ = (∫⁻ x in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal (‖classicalGradient (seeleyExtension v) x‖ ^ 2) ∂volume) +
        ∫⁻ x in seeleyOuterAnnulus,
          ENNReal.ofReal (‖classicalGradient (seeleyExtension v) x‖ ^ 2) ∂volume := rfl
    _ = (∫⁻ x in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal (‖classicalGradient v x‖ ^ 2) ∂volume) +
        ∫⁻ x in seeleyOuterAnnulus,
          ENNReal.ofReal (‖classicalGradient (seeleyExtension v) x‖ ^ 2) ∂volume := by
      rw [hinner]
    _ ≤ (∫⁻ x in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal (‖classicalGradient v x‖ ^ 2) ∂volume) +
        (2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648 : ℝ≥0∞) *
          ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
            ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume := by
      exact add_le_add_right (seeleyExtension_gradient_energy_le v hv) _
    _ = (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648 : ℝ≥0∞) *
        ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume := by ring

private theorem norm_le_vecEuclideanNorm_local (x : Vec 3) :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖x i‖₊) ≤
      ⟨vecEuclideanNorm x, vecEuclideanNorm_nonneg x⟩ := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast abs_apply_le_vecEuclideanNorm x i
  exact_mod_cast hnn

private theorem classicalGradient_mul_local
    {f g : Vec 3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    classicalGradient (fun x => f x * g x) =
      fun x => f x • classicalGradient g x + g x • classicalGradient f x := by
  funext x i
  rw [classicalGradient_apply]
  have h := congrArg (fun L : Vec 3 →L[ℝ] ℝ => L (basisVec i))
    (fderiv_mul (hf x) (hg x))
  have hfun : (fun y : Vec 3 => f y * g y) = f * g := by
    funext y
    rfl
  rw [hfun]
  simpa [Pi.mul_apply, smul_eq_mul, classicalGradient_apply, add_comm] using h

private theorem seeleyCutoffExtension_value_energy_ball_two_le
    (v : Vec 3 → ℝ) (c : ℝ) (hv : Continuous v) :
    ∫⁻ x in euclideanBall (0 : Vec 3) 2,
        ENNReal.ofReal |seeleyCutoffExtension (fun y => v y - c) x| ^ 2 ∂volume ≤
      (6337 : ℝ≥0∞) *
        ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal |v y - c| ^ 2 ∂volume := by
  let η : Vec 3 → ℝ := canonicalBallCutoff (0 : Vec 3) 1 2
  let w : Vec 3 → ℝ := fun y => v y - c
  let e : Vec 3 → ℝ := seeleyExtension w
  have hη0 : ∀ x, 0 ≤ η x := fun x =>
    canonicalBallCutoff_nonneg (0 : Vec 3) 1 2 x
  have hη1 : ∀ x, η x ≤ 1 := fun x =>
    canonicalBallCutoff_le_one (0 : Vec 3) 1 2 x
  have hpoint : ∀ x : Vec 3,
      ENNReal.ofReal |η x * e x| ^ 2 ≤ ENNReal.ofReal |e x| ^ 2 := by
    intro x
    have habs : |η x * e x| ≤ |e x| := by
      rw [abs_mul, abs_of_nonneg (hη0 x)]
      exact mul_le_of_le_one_left (abs_nonneg (e x)) (hη1 x)
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal habs) 2
  have hraw :
      ∫⁻ x in euclideanBall (0 : Vec 3) 2,
          ENNReal.ofReal |e x| ^ 2 ∂volume ≤
        (6337 : ℝ≥0∞) *
          ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
            ENNReal.ofReal |v y - c| ^ 2 ∂volume := by
    simpa [e] using seeleyExtension_value_energy_ball_two_le v c hv
  calc
    ∫⁻ x in euclideanBall (0 : Vec 3) 2,
        ENNReal.ofReal |seeleyCutoffExtension (fun y => v y - c) x| ^ 2 ∂volume ≤
        ∫⁻ x in euclideanBall (0 : Vec 3) 2,
          ENNReal.ofReal |e x| ^ 2 ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (by
        change MeasurableSet {x : Vec 3 | euclideanSqDist x 0 < (2 : ℝ) ^ 2}
        exact (isOpen_lt (contDiff_euclideanSqDist_left (0 : Vec 3)).continuous
          continuous_const).measurableSet)] with x hx
      change ENNReal.ofReal |η x * e x| ^ 2 ≤ _
      exact hpoint x
    _ ≤ _ := hraw

private theorem seeleyCutoffExtension_gradient_energy_ball_two_le
    (v : Vec 3 → ℝ) (c : ℝ) (hv : ContDiff ℝ 1 v) :
    ∫⁻ x in euclideanBall (0 : Vec 3) 2,
        ENNReal.ofReal
          (‖classicalGradient (seeleyCutoffExtension (fun y => v y - c)) x‖ ^ 2) ∂volume ≤
      2 * (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648) *
          ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
            ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume +
        2 * 32 ^ 2 * 6337 *
          ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
            ENNReal.ofReal |v y - c| ^ 2 ∂volume := by
  let η : Vec 3 → ℝ := canonicalBallCutoff (0 : Vec 3) 1 2
  let w : Vec 3 → ℝ := fun y => v y - c
  let e : Vec 3 → ℝ := seeleyExtension w
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    canonicalBallCutoff_smooth (0 : Vec 3) (by norm_num) (by norm_num)
  have hw : ContDiff ℝ 1 w := hv.sub contDiff_const
  have he : ContDiff ℝ 1 e := seeleyExtension_contDiff w hw
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hηdiff : Differentiable ℝ η := hη1.differentiable (by norm_num)
  have hed : Differentiable ℝ e := he.differentiable (by norm_num)
  have hprod : classicalGradient (fun x => η x * e x) =
      fun x => η x • classicalGradient e x + e x • classicalGradient η x := by
    exact classicalGradient_mul_local hηdiff hed
  have hpoint : ∀ x : Vec 3,
      ENNReal.ofReal (‖classicalGradient (fun y => η y * e y) x‖ ^ 2) ≤
        2 * ENNReal.ofReal (‖classicalGradient e x‖ ^ 2) +
          (2 * 32 ^ 2 : ℝ≥0∞) * ENNReal.ofReal |e x| ^ 2 := by
    intro x
    have hη0 : 0 ≤ η x := canonicalBallCutoff_nonneg (0 : Vec 3) 1 2 x
    have hη1 : η x ≤ 1 := canonicalBallCutoff_le_one (0 : Vec 3) 1 2 x
    have hgradη : ‖classicalGradient η x‖ ≤ 32 := by
      have hcut := canonicalBallCutoff_gradient_bound
        (x₀ := (0 : Vec 3)) (r := (1 : ℝ)) (R := 2)
        (by norm_num) (by norm_num) x
      dsimp [η]
      norm_num at hcut
      exact (norm_le_vecEuclideanNorm_local _).trans hcut
    have hsum :
        ‖classicalGradient (fun y => η y * e y) x‖ ≤
          ‖classicalGradient e x‖ + 32 * |e x| := by
      rw [hprod]
      calc
        ‖η x • classicalGradient e x + e x • classicalGradient η x‖ ≤
            ‖η x • classicalGradient e x‖ +
              ‖e x • classicalGradient η x‖ := norm_add_le _ _
        _ ≤ ‖classicalGradient e x‖ + 32 * |e x| := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs]
          have hfirst := mul_le_mul_of_nonneg_right hη1
            (norm_nonneg (classicalGradient e x))
          have hsecond := mul_le_mul_of_nonneg_left hgradη (abs_nonneg (e x))
          calc
            |η x| * ‖classicalGradient e x‖ + ‖e x‖ * ‖classicalGradient η x‖ =
                η x * ‖classicalGradient e x‖ + |e x| * ‖classicalGradient η x‖ := by
                  rw [abs_of_nonneg hη0, Real.norm_eq_abs]
            _ ≤ 1 * ‖classicalGradient e x‖ + |e x| * 32 :=
              add_le_add hfirst hsecond
            _ = ‖classicalGradient e x‖ + 32 * |e x| := by ring
    have hsq :
        ‖classicalGradient (fun y => η y * e y) x‖ ^ 2 ≤
          2 * ‖classicalGradient e x‖ ^ 2 + 2 * (32 * |e x|) ^ 2 := by
      have hsq' := (sq_le_sq₀
        (norm_nonneg (classicalGradient (fun y => η y * e y) x)) (by positivity)).2 hsum
      nlinarith only [hsq', sq_nonneg
        (‖classicalGradient e x‖ - 32 * |e x|)]
    calc
      _ ≤ ENNReal.ofReal
          (2 * ‖classicalGradient e x‖ ^ 2 + 2 * (32 * |e x|) ^ 2) :=
        ENNReal.ofReal_le_ofReal hsq
      _ = 2 * ENNReal.ofReal (‖classicalGradient e x‖ ^ 2) +
          (2 * 32 ^ 2 : ℝ≥0∞) * ENNReal.ofReal |e x| ^ 2 := by
        simp only [norm_nonneg, ENNReal.ofReal_pow, ofReal_norm]
        norm_num
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        norm_num
        rw [mul_pow]
        ring
  have hgrad_w : classicalGradient w = classicalGradient v := by
    funext x i
    rw [classicalGradient_apply, classicalGradient_apply]
    simp only [w]
    rw [fderiv_sub_const]
  have hgradB :
      ∫⁻ x in euclideanBall (0 : Vec 3) 2,
          ENNReal.ofReal (‖classicalGradient e x‖ ^ 2) ∂volume ≤
        (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648 : ℝ≥0∞) *
          ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
            ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume := by
    simpa [e, hgrad_w] using seeleyExtension_gradient_energy_ball_two_le w hw
  have hvalueB := seeleyExtension_value_energy_ball_two_le v c hv.continuous
  have hcontGrad : Continuous (classicalGradient e) := by
    apply continuous_pi
    intro i
    simpa only [classicalGradient_apply] using
      (he.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hmeas₁ : Measurable (fun x =>
      2 * ENNReal.ofReal (‖classicalGradient e x‖ ^ 2)) := by
    simpa using (ENNReal.measurable_ofReal.comp
      (hcontGrad.norm.pow 2).measurable).const_mul (2 : ℝ≥0∞)
  have hmeas₂ : Measurable (fun x =>
    (2 * 32 ^ 2 : ℝ≥0∞) * ENNReal.ofReal |e x| ^ 2) := by
    have habs : Measurable (fun x => |e x|) := he.continuous.abs.measurable
    have hof : Measurable (fun x => ENNReal.ofReal |e x|) := by
      change Measurable (ENNReal.ofReal ∘ fun x => |e x|)
      exact ENNReal.measurable_ofReal.comp habs
    exact (hof.pow_const 2).const_mul (2 * 32 ^ 2 : ℝ≥0∞)
  have hprod_energy := calc
    ∫⁻ x in euclideanBall (0 : Vec 3) 2,
        ENNReal.ofReal (‖classicalGradient (fun y => η y * e y) x‖ ^ 2) ∂volume ≤
        ∫⁻ x in euclideanBall (0 : Vec 3) 2,
          2 * ENNReal.ofReal (‖classicalGradient e x‖ ^ 2) +
            (2 * 32 ^ 2 : ℝ≥0∞) * ENNReal.ofReal |e x| ^ 2 ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (by
        change MeasurableSet {x : Vec 3 | euclideanSqDist x 0 < (2 : ℝ) ^ 2}
        exact (isOpen_lt (contDiff_euclideanSqDist_left (0 : Vec 3)).continuous
          continuous_const).measurableSet)] with x hx
      exact hpoint x
    _ = 2 * ∫⁻ x in euclideanBall (0 : Vec 3) 2,
          ENNReal.ofReal (‖classicalGradient e x‖ ^ 2) ∂volume +
          (2 * 32 ^ 2 : ℝ≥0∞) * ∫⁻ x in euclideanBall (0 : Vec 3) 2,
            ENNReal.ofReal |e x| ^ 2 ∂volume := by
      rw [lintegral_add_left hmeas₁,
        lintegral_const_mul' 2 _ (by norm_num),
        lintegral_const_mul' (2 * 32 ^ 2) _ (by norm_num)]
    _ ≤ 2 * (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648) *
          ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
            ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume +
        (2 * 32 ^ 2) * 6337 *
          ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
            ENNReal.ofReal |v y - c| ^ 2 ∂volume := by
      have hgrad_term :
          2 * ∫⁻ x in euclideanBall (0 : Vec 3) 2,
              ENNReal.ofReal (‖classicalGradient e x‖ ^ 2) ∂volume ≤
            2 * (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648) *
              ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
                ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume := by
        convert mul_le_mul_of_nonneg_left hgradB
          (by positivity : 0 ≤ (2 : ℝ≥0∞)) using 1
        ring
      have hvalue_term := mul_le_mul_of_nonneg_left hvalueB
        (by positivity : 0 ≤ (2 * 32 ^ 2 : ℝ≥0∞))
      have hvalue_term' :
          (2 * 32 ^ 2 : ℝ≥0∞) *
              ∫⁻ x in euclideanBall (0 : Vec 3) 2,
                ENNReal.ofReal |e x| ^ 2 ≤
            (2 * 32 ^ 2 : ℝ≥0∞) * 6337 *
              ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
                ENNReal.ofReal |v y - c| ^ 2 := by
        change (2 * 32 ^ 2 : ℝ≥0∞) *
            ∫⁻ x in euclideanBall (0 : Vec 3) 2,
              ENNReal.ofReal |seeleyExtension (fun y => v y - c) x| ^ 2 ≤ _
        calc
          _ ≤ (2 * 32 ^ 2 : ℝ≥0∞) *
              (6337 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
                ENNReal.ofReal |v y - c| ^ 2) := hvalue_term
          _ = _ := by ring
      exact add_le_add hgrad_term hvalue_term'
  change ∫⁻ x in euclideanBall (0 : Vec 3) 2,
      ENNReal.ofReal (‖classicalGradient (fun y => η y * e y) x‖ ^ 2) ∂volume ≤ _
  exact hprod_energy

theorem seeleyCutoffExtension_contDiff (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (seeleyCutoffExtension v) := by
  exact (canonicalBallCutoff_smooth (0 : Vec 3) (by norm_num) (by norm_num)
    |>.of_le (by simp)).mul (seeleyExtension_contDiff v hv)

theorem seeleyCutoffExtension_eq_on_unitBall {v : Vec 3 → ℝ} {x : Vec 3}
    (hx : x ∈ euclideanBall (0 : Vec 3) 1) :
    seeleyCutoffExtension v x = v x := by
  have hnorm : vecEuclideanNorm (x - (0 : Vec 3)) < 1 :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  have hxC : x ∈ euclideanClosedBall (0 : Vec 3) 1 := by
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2 hnorm.le
  rw [seeleyCutoffExtension, Pi.mul_apply]
  rw [canonicalBallCutoff_eq_one_on_inner
    (x₀ := (0 : Vec 3)) (r := 1) (R := 2) (by norm_num) (by norm_num) hx]
  simp only [one_mul, seeleyExtension, hxC, ite_true]

theorem seeleyLocalizedSobolevBound (v : Vec 3 → ℝ) (c : ℝ)
    (hv : ContDiff ℝ 1 v) :
    lpNormOn 6 (euclideanBall (0 : Vec 3) 1) (fun x => v x - c) ≤
      localSobolevConstant *
        (gradientLpNormOn 2 (euclideanBall (0 : Vec 3) 2)
            (seeleyCutoffExtension (fun x => v x - c)) +
          (Real.toNNReal (32 : ℝ) : ℝ≥0∞) *
            lpNormOn 2 (euclideanBall (0 : Vec 3) 2)
              (seeleyCutoffExtension (fun x => v x - c)) ) := by
  have hball : MeasurableSet (euclideanBall (0 : Vec 3) 1) := by
    change MeasurableSet {x : Vec 3 | euclideanSqDist x 0 < (1 : ℝ) ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left (0 : Vec 3)).continuous
      continuous_const).measurableSet
  have hw : ContDiff ℝ 1 (fun x => v x - c) :=
    hv.sub contDiff_const
  have hsob := smoothSobolevBall (x₀ := (0 : Vec 3)) (r := (1 : ℝ))
    (by norm_num) (seeleyCutoffExtension_contDiff (fun x => v x - c) hw)
  calc
    lpNormOn 6 (euclideanBall (0 : Vec 3) 1) (fun x => v x - c) =
        lpNormOn 6 (euclideanBall (0 : Vec 3) 1)
          (seeleyCutoffExtension (fun x => v x - c)) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem hball] with x hx
      exact (seeleyCutoffExtension_eq_on_unitBall (v := fun y => v y - c) hx).symm
    _ ≤ _ := by
      convert hsob using 1
      all_goals norm_num

/-- Finite coefficient in the L⁶ Poincare–Sobolev estimate on a Euclidean ball. -/
noncomputable def sobolevPoincareL6Constant : ℝ≥0∞ :=
  let Cg : ℝ≥0∞ :=
    2 * (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648) +
      2 * 32 ^ 2 * 6337 * euclideanBallPoincareConstant
  localSobolevConstant *
    (Cg ^ (1 / 2 : ℝ) +
      32 * ((6337 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        euclideanBallPoincareConstant ^ (1 / 2 : ℝ)))

theorem sobolevPoincare_L6_unit (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) :
    lpNormOn 6 (euclideanBall (0 : Vec 3) 1)
        (fun x => v x - MeasureTheory.average
          (volume.restrict (euclideanBall (0 : Vec 3) 1)) v) ≤
      sobolevPoincareL6Constant *
        gradientLpNormOn 2 (euclideanBall (0 : Vec 3) 1) v := by
  let B₁ : Set (Vec 3) := euclideanBall (0 : Vec 3) 1
  let B₂ : Set (Vec 3) := euclideanBall (0 : Vec 3) 2
  let c : ℝ := MeasureTheory.average (volume.restrict B₁) v
  let w : Vec 3 → ℝ := fun x => v x - c
  let E : Vec 3 → ℝ := seeleyCutoffExtension w
  let Cv : ℝ≥0∞ := 6337
  let Cp : ℝ≥0∞ := euclideanBallPoincareConstant
  let Cg : ℝ≥0∞ :=
    2 * (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648) +
      2 * 32 ^ 2 * Cv * Cp
  have hw : ContDiff ℝ 1 w := hv.sub contDiff_const
  have hE : ContDiff ℝ 1 E := seeleyCutoffExtension_contDiff w hw
  have hgradE : Continuous (classicalGradient E) := by
    apply continuous_pi
    intro i
    simpa only [classicalGradient_apply] using
      (hE.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgradv : Continuous (classicalGradient v) := by
    apply continuous_pi
    intro i
    simpa only [classicalGradient_apply] using
      (hv.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hP_energy := euclideanBall_value_energy_poincare v hv
  have hP_energy' :
      ∫⁻ y in B₁, ENNReal.ofReal (‖w y‖ ^ 2) ∂volume ≤
        Cp * ∫⁻ y in B₁,
          ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume := by
    calc
      _ = ∫⁻ y in B₁, ENNReal.ofReal |w y| ^ 2 ∂volume :=
        lintegral_norm_sq_eq_outer_sq w B₁
      _ ≤ Cp * ∫⁻ y in B₁,
          ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume := by
        simpa [B₁, c, w, Cp] using hP_energy
  have hgrad_energy0 := seeleyCutoffExtension_gradient_energy_ball_two_le v c hv
  have hvalue_energy0 := seeleyCutoffExtension_value_energy_ball_two_le v c hv.continuous
  have hvalue_energy' :
      ∫⁻ x in B₂, ENNReal.ofReal (‖E x‖ ^ 2) ∂volume ≤
        Cv * ∫⁻ y in B₁, ENNReal.ofReal (‖w y‖ ^ 2) ∂volume := by
    calc
      _ = ∫⁻ x in B₂, ENNReal.ofReal |E x| ^ 2 ∂volume :=
        lintegral_norm_sq_eq_outer_sq E B₂
      _ ≤ Cv * ∫⁻ y in B₁, ENNReal.ofReal |w y| ^ 2 ∂volume := by
        have h := hvalue_energy0
        rw [Measure.restrict_congr_set euclideanClosedBall_one_ae_eq_euclideanBall] at h
        simpa [B₁, B₂, c, w, E, Cv] using h
      _ = _ := by
        exact congrArg (fun z : ℝ≥0∞ => Cv * z)
          (lintegral_norm_sq_eq_outer_sq w B₁).symm
  have hP_outer :
      ∫⁻ y in B₁, ENNReal.ofReal |w y| ^ 2 ∂volume ≤
        Cp * ∫⁻ y in B₁,
          ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume := by
    simpa [B₁, c, w, Cp] using hP_energy
  have hgrad_energy' :
      ∫⁻ x in B₂, ENNReal.ofReal (‖classicalGradient E x‖ ^ 2) ∂volume ≤
        Cg * ∫⁻ y in B₁,
          ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume := by
    calc
      _ ≤ 2 * (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648) *
            ∫⁻ y in B₁,
              ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume +
          2 * 32 ^ 2 * Cv *
            ∫⁻ y in B₁, ENNReal.ofReal |w y| ^ 2 ∂volume := by
        have h := hgrad_energy0
        rw [Measure.restrict_congr_set euclideanClosedBall_one_ae_eq_euclideanBall] at h
        simpa [B₁, B₂, c, w, E, Cv] using h
      _ ≤ 2 * (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648) *
            ∫⁻ y in B₁,
              ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume +
          2 * 32 ^ 2 * Cv *
            (Cp * ∫⁻ y in B₁,
              ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hP_outer (by positivity))
      _ = _ := by ring
  have hgrad_norm := eLpNorm_two_le_of_energy
    (classicalGradient E) (classicalGradient v) B₂ B₁ Cg hgradE hgradv
    (by positivity) hgrad_energy'
  have hvalue_norm := eLpNorm_two_le_of_energy E w B₂ B₁ Cv hE.continuous
    hw.continuous (by positivity) hvalue_energy'
  have hvalueP0 := eLpNorm_two_le_of_energy w
    (fun y => ‖classicalGradient v y‖) B₁ B₁ Cp hw.continuous hgradv.norm
      (by positivity) (by
        simpa [Real.norm_eq_abs] using hP_energy')
  have hvalueP :
      eLpNorm w 2 (volume.restrict B₁) ≤
        Cp ^ (1 / 2 : ℝ) *
          eLpNorm (classicalGradient v) 2 (volume.restrict B₁) := by
    calc
      _ ≤ Cp ^ (1 / 2 : ℝ) *
          eLpNorm (fun y => ‖classicalGradient v y‖) 2
            (volume.restrict B₁) := hvalueP0
      _ = _ := by rw [eLpNorm_norm _ hgradv.aestronglyMeasurable]
  have hvalue_total :
      eLpNorm E 2 (volume.restrict B₂) ≤
        Cv ^ (1 / 2 : ℝ) *
          (Cp ^ (1 / 2 : ℝ) *
            eLpNorm (classicalGradient v) 2 (volume.restrict B₁)) := by
    calc
      _ ≤ Cv ^ (1 / 2 : ℝ) * eLpNorm w 2 (volume.restrict B₁) := hvalue_norm
      _ ≤ _ := mul_le_mul_of_nonneg_left hvalueP (by positivity)
  have hloc := seeleyLocalizedSobolevBound v c hv
  have hsum :
      eLpNorm (classicalGradient E) 2 (volume.restrict B₂) +
          (Real.toNNReal (32 : ℝ) : ℝ≥0∞) *
            eLpNorm E 2 (volume.restrict B₂) ≤
        Cg ^ (1 / 2 : ℝ) *
            eLpNorm (classicalGradient v) 2 (volume.restrict B₁) +
          32 * (Cv ^ (1 / 2 : ℝ) *
            (Cp ^ (1 / 2 : ℝ) *
              eLpNorm (classicalGradient v) 2 (volume.restrict B₁))) := by
    exact add_le_add hgrad_norm
      (by simpa using mul_le_mul_of_nonneg_left hvalue_total (by positivity))
  calc
    lpNormOn 6 B₁ (fun x => v x - c) ≤
        localSobolevConstant *
          (gradientLpNormOn 2 B₂ E +
            (Real.toNNReal (32 : ℝ) : ℝ≥0∞) * lpNormOn 2 B₂ E) := by
      simpa [B₁, B₂, c, E] using hloc
    _ ≤ localSobolevConstant *
        (Cg ^ (1 / 2 : ℝ) *
            eLpNorm (classicalGradient v) 2 (volume.restrict B₁) +
          32 * (Cv ^ (1 / 2 : ℝ) *
            (Cp ^ (1 / 2 : ℝ) *
              eLpNorm (classicalGradient v) 2 (volume.restrict B₁)))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = sobolevPoincareL6Constant *
        gradientLpNormOn 2 (euclideanBall (0 : Vec 3) 1) v := by
      simp [sobolevPoincareL6Constant, B₁, Cg, Cv, Cp, gradientLpNormOn]
      ring
    _ = _ := by simp

theorem sobolevPoincare_L6_ball
    (x₀ : Vec 3) {r : ℝ} (hr : 0 < r) (v : Vec 3 → ℝ)
    (hv : ContDiff ℝ 1 v) :
    lpNormOn 6 (euclideanBall x₀ r)
        (fun x => v x - average (volume.restrict (euclideanBall x₀ r)) v) ≤
      sobolevPoincareL6Constant * gradientLpNormOn 2
        (euclideanBall x₀ r) v := by
  let F : Vec 3 → Vec 3 := seeleyAffineMap x₀ r
  have hF : ContDiff ℝ 1 F := by
    change ContDiff ℝ 1 (fun x : Vec 3 => x₀ + r • x)
    exact contDiff_const.add (contDiff_id.const_smul r)
  have hu : ContDiff ℝ 1 (v ∘ F) := hv.comp hF
  have hunit := sobolevPoincare_L6_unit (v ∘ F) hu
  have havg := seeleyAffine_average (x₀ := x₀) hr hv.continuous
  have hgradv : Continuous (classicalGradient v) := by
    apply continuous_pi
    intro i
    simpa only [classicalGradient_apply] using
      (hv.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hvalv : Continuous
      (fun x => v x - average (volume.restrict (euclideanBall x₀ r)) v) :=
    hv.continuous.sub continuous_const
  have hvalcomp :
      eLpNorm (fun x => (v ∘ F) x -
          average (volume.restrict (euclideanBall (0 : Vec 3) 1)) (v ∘ F))
          6 (volume.restrict (euclideanBall (0 : Vec 3) 1)) =
        ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / 6 : ℝ) *
          eLpNorm (fun x => v x -
            average (volume.restrict (euclideanBall x₀ r)) v) 6
            (volume.restrict (euclideanBall x₀ r)) := by
    have heq :
        (fun x => (v ∘ F) x -
            average (volume.restrict (euclideanBall (0 : Vec 3) 1)) (v ∘ F)) =
          (fun x => (fun y => v y -
            average (volume.restrict (euclideanBall x₀ r)) v) (F x)) := by
      funext x
      simp only [Function.comp_apply, F]
      rw [havg]
    rw [heq]
    simpa [F, Function.comp_def] using
      (seeleyAffine_eLpNorm_comp (x₀ := x₀) hr hvalv 6)
  have hgrad_eq :
      classicalGradient (v ∘ F) =
        r • (classicalGradient v ∘ F) := by
    funext x
    simpa [F] using seeleyAffine_classicalGradient hv x
  have hgradcomp :
      eLpNorm (classicalGradient (v ∘ F)) 2
          (volume.restrict (euclideanBall (0 : Vec 3) 1)) =
        ENNReal.ofReal r *
          (ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) *
            eLpNorm (classicalGradient v) 2
              (volume.restrict (euclideanBall x₀ r))) := by
    rw [hgrad_eq, eLpNorm_const_smul]
    have hcomp := seeleyAffine_eLpNorm_comp (x₀ := x₀) (f := classicalGradient v)
      hr hgradv 2
    rw [hcomp]
    norm_num
    rw [Real.enorm_eq_ofReal hr.le]
  have hscale :
      ENNReal.ofReal r * ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / 6 : ℝ) := by
    rw [ENNReal.ofReal_pow (inv_nonneg.mpr hr.le) 3,
      ENNReal.ofReal_inv_of_pos hr]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    rw [← ENNReal.rpow_mul]
    have h32 : (↑(3 : ℕ) : ℝ) * (1 / 2 : ℝ) = 3 / 2 := by norm_num
    rw [h32]
    calc
      ENNReal.ofReal r * (ENNReal.ofReal r)⁻¹ ^ (3 / 2 : ℝ) =
          (ENNReal.ofReal r)⁻¹ ^ (1 / 2 : ℝ) := by
        calc
          ENNReal.ofReal r * (ENNReal.ofReal r)⁻¹ ^ (3 / 2 : ℝ) =
              (ENNReal.ofReal r) ^ (1 : ℝ) *
                (ENNReal.ofReal r)⁻¹ ^ (3 / 2 : ℝ) := by simp
          _ = (ENNReal.ofReal r) ^ (1 : ℝ) *
                ((ENNReal.ofReal r) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [ENNReal.inv_rpow]
          _ = (ENNReal.ofReal r) ^ (1 : ℝ) *
                (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) := by
            rw [← ENNReal.rpow_neg]
          _ = (ENNReal.ofReal r) ^ (1 + -(3 / 2 : ℝ)) := by
            rw [← ENNReal.rpow_add _ _
              (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top]
          _ = (ENNReal.ofReal r)⁻¹ ^ (1 / 2 : ℝ) := by
            rw [show (1 + -(3 / 2 : ℝ)) = -(1 / 2 : ℝ) by norm_num]
            rw [ENNReal.rpow_neg, ← ENNReal.inv_rpow]
      _ = (ENNReal.ofReal r)⁻¹ ^ (3 * (1 / 6 : ℝ)) := by
        have hz : (3 : ℝ) * (1 / 6 : ℝ) = 1 / 2 := by norm_num
        change (ENNReal.ofReal r)⁻¹ ^ (1 / 2 : ℝ) =
          (ENNReal.ofReal r)⁻¹ ^ ((3 : ℝ) * (1 / 6 : ℝ))
        rw [hz]
  have hscaled :
      ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / 6 : ℝ) *
          eLpNorm (fun x => v x -
            average (volume.restrict (euclideanBall x₀ r)) v) 6
            (volume.restrict (euclideanBall x₀ r)) ≤
        ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / 6 : ℝ) *
          (sobolevPoincareL6Constant *
            eLpNorm (classicalGradient v) 2
              (volume.restrict (euclideanBall x₀ r))) := by
    calc
      _ = eLpNorm (fun x => (v ∘ F) x -
          average (volume.restrict (euclideanBall (0 : Vec 3) 1)) (v ∘ F))
          6 (volume.restrict (euclideanBall (0 : Vec 3) 1)) := hvalcomp.symm
      _ ≤ sobolevPoincareL6Constant *
          eLpNorm (classicalGradient (v ∘ F)) 2
            (volume.restrict (euclideanBall (0 : Vec 3) 1)) := by
        simpa [lpNormOn, gradientLpNormOn] using hunit
      _ = _ := by
        rw [hgradcomp]
        calc
          sobolevPoincareL6Constant *
                (ENNReal.ofReal r *
                  (ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) *
                    eLpNorm (classicalGradient v) 2
                      (volume.restrict (euclideanBall x₀ r)))) =
              sobolevPoincareL6Constant *
                ((ENNReal.ofReal r *
                  ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / 2 : ℝ)) *
                    eLpNorm (classicalGradient v) 2
                      (volume.restrict (euclideanBall x₀ r))) := by ring
          _ = sobolevPoincareL6Constant *
                (ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / 6 : ℝ) *
                  eLpNorm (classicalGradient v) 2
                    (volume.restrict (euclideanBall x₀ r))) := by rw [hscale]
          _ = _ := by ring
  have hscale_pos :
      0 < ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / 6 : ℝ) := by positivity
  have hscale_top :
      ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / 6 : ℝ) ≠ ∞ := by finiteness
  have hcancel := (ENNReal.mul_le_iff_le_inv hscale_pos.ne' hscale_top).mp hscaled
  rw [← mul_assoc, ENNReal.inv_mul_cancel hscale_pos.ne' hscale_top, one_mul] at hcancel
  simpa [lpNormOn, gradientLpNormOn] using hcancel

end
end CKN
