/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Covering
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Setting.SingularSetClosed
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq

/-!
# Conditional nullity of the singular set

This module formalizes the reduction from the gradient criterion to vanishing
parabolic one dimensional Hausdorff measure.  The criterion is supplied as a
hypothesis so that a later regularity theorem can instantiate it directly.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open Metric

noncomputable section
namespace CKN

private lemma parabolicCylinder_subset_metricBall_self
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    parabolicCylinder z.1 z.2 r ⊆ Metric.ball z r := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_parabolicDist]
  rcases hy with ⟨hspace, hlow, hupp⟩
  change max (vec3EuclideanNorm (y.1 - z.1)) (Real.sqrt |y.2 - z.2|) < r
  refine max_lt hspace ?_
  apply (Real.sqrt_lt' hr).2
  apply abs_lt.2
  constructor
  · linarith only [hlow]
  · linarith only [hupp, sq_pos_of_pos hr]

private lemma exists_local_box_nhds
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (z : spaceTimeSet Ω I) :
    ∃ Ω' J, localBox Ω I Ω' J ∧ IsOpen J ∧
      (z : ParabolicPoint) ∈ spaceTimeSet Ω' J := by
  rcases Metric.mem_nhds_iff.mp (hΩ.mem_nhds z.property.1) with ⟨a, ha, haΩ⟩
  rcases Metric.mem_nhds_iff.mp (hI.mem_nhds z.property.2) with ⟨b, hb, hbI⟩
  let Ω' : Set Vec3 := Metric.ball z.1.1 (a / 2)
  let J : Set ℝ := Ioo (z.1.2 - b / 2) (z.1.2 + b / 2)
  have ha2 : 0 < a / 2 := by linarith only [ha]
  have hb2 : 0 < b / 2 := by linarith only [hb]
  have hΩ' : IsOpen Ω' := by
    exact Metric.isOpen_ball
  have hclΩ' : IsCompact (closure Ω') := by
    apply (ProperSpace.isCompact_closedBall z.1.1 (a / 2)).of_isClosed_subset
      isClosed_closure
    exact Metric.closure_ball_subset_closedBall
  have hclΩ'sub : closure Ω' ⊆ Ω := by
    apply Metric.closure_ball_subset_closedBall.trans
    exact (Metric.closedBall_subset_ball (by linarith only [ha])).trans haΩ
  have hJ : IsOpen J := by
    exact isOpen_Ioo
  have hab : z.1.2 - b / 2 < z.1.2 + b / 2 := by
    linarith only [hb]
  have hclJ : closure J = Icc (z.1.2 - b / 2) (z.1.2 + b / 2) := by
    dsimp [J]
    exact closure_Ioo hab.ne
  have hclJcomp : IsCompact (closure J) := by
    rw [hclJ]
    exact isCompact_Icc
  have hclJsub : closure J ⊆ I := by
    rw [hclJ]
    intro s hs
    apply hbI
    rw [Metric.mem_ball, Real.dist_eq]
    apply abs_lt.2
    constructor <;> linarith only [hs.1, hs.2, hb]
  refine ⟨Ω', J, ⟨hΩ', hclΩ', hclΩ'sub, ordConnected_Ioo,
    hclJcomp, hclJsub⟩, hJ, ?_⟩
  exact ⟨by simpa [Ω'] using ha2, by constructor <;> linarith only [hb]⟩

private lemma spatialGradientSq_le_norm
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) :
    spatialGradientSq u Du z ≤ 9 * ‖Du z‖ ^ (2 : ℕ) := by
  unfold spatialGradientSq
  calc
    ∑ i, ∑ j, (Du z i j) ^ (2 : ℕ) ≤
        ∑ i, ∑ j, (‖Du z‖ : ℝ) ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hi' : ‖Du z i‖ ≤ ‖Du z‖ := by
        simpa only [WithLp.ofLp_toLp, PiLp.norm_toLp] using
          (PiLp.norm_apply_le (WithLp.toLp (∞ : ℝ≥0∞) (Du z)) i)
      have hj' : ‖(Du z i) j‖ ≤ ‖Du z i‖ := by
        simpa only [WithLp.ofLp_toLp, PiLp.norm_toLp] using
          (PiLp.norm_apply_le (WithLp.toLp (∞ : ℝ≥0∞) (Du z i)) j)
      have hnorm : ‖(Du z i) j‖ ≤ ‖Du z‖ := hj'.trans hi'
      have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
      simpa only [Real.norm_eq_abs, sq_abs] using hsq
    _ = 9 * ‖Du z‖ ^ (2 : ℕ) := by norm_num [Finset.sum_const, Finset.card_univ]; ring

end CKN
namespace CKN
private lemma spatialGradientSq_enorm_le
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) :
    ENNReal.ofReal (spatialGradientSq u Du z) ≤
      9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
  have hreal := spatialGradientSq_le_norm u Du z
  calc
    ENNReal.ofReal (spatialGradientSq u Du z) ≤
        ENNReal.ofReal (9 * ‖Du z‖ ^ (2 : ℕ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm]
      norm_num [ENNReal.rpow_natCast]
end CKN
namespace CKN

private lemma singularSet_null_of_gradient_criterion_closed_hSA_1 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} (ε₁ : ℝ),
      (0 : ℝ) < ε₁ →
        ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          (∀ z₀ ∈ spaceTimeSet Ω I,
              limsup
                    (fun (r : ℝ) =>
                      (ENNReal.ofReal r)⁻¹ *
                        ∫⁻ (w : ParabolicPoint) in parabolicCylinder z₀.1 z₀.2 r,
                          ENNReal.ofReal (spatialGradientSq u Du w))
                    (𝓝[>] (0 : ℝ)) <
                  ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
                IsRegularPoint Ω I u z₀) →
            (∀ (Ω' : Set Vec3) (J : Set ℝ),
                localBox Ω I Ω' J →
                  AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J)) ∧
                    AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J)) ∧
                      AEStronglyMeasurable p (volume.restrict (spaceTimeSet Ω' J)) ∧
                        AEStronglyMeasurable f (volume.restrict (spaceTimeSet Ω' J)) ∧
                          essSup (fun (s : ℝ) => ∫⁻ (x : Vec3) in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
                                (volume.restrict J) <
                              ∞ ∧
                            ∫⁻ (z : ParabolicPoint) in spaceTimeSet Ω' J,
                                  ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) <
                                ∞ ∧
                              MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
                                  (volume.restrict (spaceTimeSet Ω' J)) ∧
                                MemLp f (ENNReal.ofReal q) (volume.restrict (spaceTimeSet Ω' J)) ∧
                                  ∀ (i : Fin (3 : ℕ)),
                                    ∀ᵐ (s : ℝ) ∂volume.restrict J,
                                      HasWeakGradientOn Ω' (fun (x : Vec (3 : ℕ)) => u (x, s) i)
                                        fun (x : Vec (3 : ℕ)) => Du (x, s) i) →
              ∀ (Ω' : { z : ParabolicPoint // z ∈ spaceTimeSet Ω I } → Set Vec3)
                (J : { z : ParabolicPoint // z ∈ spaceTimeSet Ω I } → Set ℝ),
                (∀ (z : { z : ParabolicPoint // z ∈ spaceTimeSet Ω I }),
                    localBox Ω I (Ω' z) (J z) ∧
                      IsOpen (J z) ∧ (↑z : ParabolicPoint) ∈ spaceTimeSet (Ω' z) (J z)) →
                  let U : { z : ParabolicPoint // z ∈ spaceTimeSet Ω I } → Set ParabolicPoint :=
                    fun (z : { z : ParabolicPoint // z ∈ spaceTimeSet Ω I }) =>
                    spaceTimeSet (Ω' z) (J z);
                  (∀ (z : { z : ParabolicPoint // z ∈ spaceTimeSet Ω I }), IsOpen (U z)) →
                    ∀ (A : Set { z : ParabolicPoint // z ∈ spaceTimeSet Ω I }) (z : (↑A : Type)),
                      (parabolicHausdorffMeasure (1 : ℝ≥0∞) : Set ParabolicPoint → ℝ≥0∞)
                          (SingularSet Ω I u ∩
                            U (↑z : { z : ParabolicPoint // z ∈ spaceTimeSet Ω I })) =
                        (0 : ℝ≥0∞)
    := by
  intro Ω I q ε₁ hε u Du p f hcrit hloc Ω' J hΩJ U hUopen A z
  have hboxz := hΩJ z.1
  rcases hloc (Ω' z.1) (J z.1) hboxz.1 with
    ⟨hu, hDu, hp, hf, hslic, henergy, hpLp, hfLp, hgrad⟩
  let Du' : ParabolicPoint → Fin 3 → Vec3 := hDu.mk Du
  let G : ParabolicPoint → ℝ≥0∞ :=
    (U z.1).indicator (fun w => (9 : ℝ≥0∞) * ‖Du' w‖ₑ ^ (2 : ℝ))
  have hUmeas : MeasurableSet (U z.1) := (hUopen z.1).measurableSet
  have hG : Measurable G := by
    apply Measurable.indicator
    · have hnorm : Measurable (fun w => ‖Du' w‖ₑ) := hDu.measurable_mk.enorm
      have hpow : Measurable (fun w => ‖Du' w‖ₑ ^ (2 : ℝ)) :=
        (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp hnorm
      exact hpow.const_mul (9 : ℝ≥0∞)
    · exact hUmeas
  have hDuInt :
      (∫⁻ w in U z.1, ‖Du w‖ₑ ^ (2 : ℝ)) < ∞ := by
    calc
      (∫⁻ w in U z.1, ‖Du w‖ₑ ^ (2 : ℝ)) ≤
          ∫⁻ w in U z.1,
            ‖u w‖ₑ ^ (2 : ℝ) + ‖Du w‖ₑ ^ (2 : ℝ) := by
        apply lintegral_mono_ae
        exact Eventually.of_forall (fun w =>
          le_add_of_nonneg_left (by positivity))
      _ < ∞ := henergy
  have hGfin : (∫⁻ w, G w) < ∞ := by
    rw [show G = (U z.1).indicator
        (fun w => (9 : ℝ≥0∞) * ‖Du' w‖ₑ ^ (2 : ℝ)) by rfl,
      lintegral_indicator hUmeas]
    have hAE : Du =ᵐ[volume.restrict (U z.1)] Du' := hDu.ae_eq_mk
    have hAEpow :
        (fun w => (9 : ℝ≥0∞) * ‖Du' w‖ₑ ^ (2 : ℝ)) =ᵐ[
          volume.restrict (U z.1)]
        (fun w => (9 : ℝ≥0∞) * ‖Du w‖ₑ ^ (2 : ℝ)) := by
      filter_upwards [hAE] with w hw
      rw [hw]
    calc
      (∫⁻ w in U z.1, (9 : ℝ≥0∞) * ‖Du' w‖ₑ ^ (2 : ℝ)) =
          ∫⁻ w in U z.1, (9 : ℝ≥0∞) * ‖Du w‖ₑ ^ (2 : ℝ) :=
        lintegral_congr_ae hAEpow
      _ = (9 : ℝ≥0∞) * (∫⁻ w in U z.1, ‖Du w‖ₑ ^ (2 : ℝ)) := by
        exact lintegral_const_mul' (μ := volume.restrict (U z.1))
          (9 : ℝ≥0∞) (fun w => ‖Du w‖ₑ ^ (2 : ℝ)) ENNReal.coe_ne_top
      _ < ∞ := ENNReal.mul_lt_top (by norm_num) hDuInt
  have hsmall : ∀ y ∈ SingularSet Ω I u ∩ U z.1, ∀ n : ℕ, ∃ r : ℝ,
      0 < r ∧ r < 1 / ((n + 1 : ℕ) : ℝ) ∧
        parabolicCylinder y.1 y.2 r ⊆ U z.1 ∧
          ((NNReal.mk (ε₁ ^ (2 : ℕ) / 2) (by positivity) : NNReal) : ℝ≥0∞) *
              ENNReal.ofReal r <
            ∫⁻ w in parabolicCylinder y.1 y.2 r, G w := by
    intro y hy n
    have hyS : y ∈ SingularSet Ω I u := hy.1
    have hyO : y ∈ spaceTimeSet Ω I := hyS.1
    have hyreg : ¬ IsRegularPoint Ω I u y := hyS.2
    have hnot : ¬ Filter.limsup (fun r : ℝ =>
        (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w in parabolicCylinder y.1 y.2 r,
            ENNReal.ofReal (spatialGradientSq u Du w))
        (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) := by
      intro hlim
      exact hyreg (hcrit y hyO hlim)
    have hlim : ENNReal.ofReal (ε₁ ^ (2 : ℕ)) ≤
        Filter.limsup (fun r : ℝ =>
          (ENNReal.ofReal r)⁻¹ *
            ∫⁻ w in parabolicCylinder y.1 y.2 r,
              ENNReal.ofReal (spatialGradientSq u Du w))
          (𝓝[>] (0 : ℝ)) := le_of_not_gt hnot
    have hhalf : 0 < ε₁ ^ (2 : ℕ) / 2 := by positivity
    have hhalf_lt : ε₁ ^ (2 : ℕ) / 2 < ε₁ ^ (2 : ℕ) := by
      linarith only [hhalf]
    have hfreq : ∃ᶠ r in (𝓝[>] (0 : ℝ)),
        ENNReal.ofReal (ε₁ ^ (2 : ℕ) / 2) <
          (ENNReal.ofReal r)⁻¹ *
            ∫⁻ w in parabolicCylinder y.1 y.2 r,
              ENNReal.ofReal (spatialGradientSq u Du w) := by
      refine frequently_lt_of_lt_limsup (hu := by isBoundedDefault) (h := ?_)
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hhalf_lt |>.trans_le hlim
    rcases Metric.mem_nhds_iff.mp ((hUopen z.1).mem_nhds hy.2) with
      ⟨δ, hδ, hδU⟩
    have hev : ∀ᶠ r in (𝓝[>] (0 : ℝ)),
        0 < r ∧ r < 1 / ((n + 1 : ℕ) : ℝ) ∧
          parabolicCylinder y.1 y.2 r ⊆ U z.1 := by
      have hδev : ∀ᶠ r in (𝓝[>] (0 : ℝ)), r ∈ Ioo (0 : ℝ) δ :=
        Ioo_mem_nhdsGT hδ
      have hnev : ∀ᶠ r in (𝓝[>] (0 : ℝ)),
          r ∈ Ioo (0 : ℝ) (1 / ((n + 1 : ℕ) : ℝ)) :=
        Ioo_mem_nhdsGT (by positivity)
      filter_upwards [hδev, hnev] with r hrδ hrn
      refine ⟨hrδ.1, hrn.2, ?_⟩
      exact (parabolicCylinder_subset_metricBall_self hrδ.1).trans
        ((Metric.ball_subset_ball hrδ.2.le).trans hδU)
    rcases (hfreq.and_eventually hev).exists with ⟨r, hrE, hr⟩
    have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr.1).ne'
    have hmul := ENNReal.mul_lt_mul_right hr0 ENNReal.ofReal_ne_top hrE
    have hmul' : ENNReal.ofReal (ε₁ ^ (2 : ℕ) / 2) * ENNReal.ofReal r <
        ∫⁻ w in parabolicCylinder y.1 y.2 r,
          ENNReal.ofReal (spatialGradientSq u Du w) := by
      calc
        ENNReal.ofReal (ε₁ ^ (2 : ℕ) / 2) * ENNReal.ofReal r =
            ENNReal.ofReal r * ENNReal.ofReal (ε₁ ^ (2 : ℕ) / 2) := by
              rw [mul_comm]
        _ < ENNReal.ofReal r *
            ((ENNReal.ofReal r)⁻¹ *
              ∫⁻ w in parabolicCylinder y.1 y.2 r,
                ENNReal.ofReal (spatialGradientSq u Du w)) := hmul
        _ = ∫⁻ w in parabolicCylinder y.1 y.2 r,
            ENNReal.ofReal (spatialGradientSq u Du w) := by
              rw [← mul_assoc, ENNReal.mul_inv_cancel hr0 ENNReal.ofReal_ne_top,
                one_mul]
    have hCmeas : MeasurableSet (parabolicCylinder y.1 y.2 r) := by
      rw [parabolicCylinder]
      exact (vec3Ball_measurable _ _).prod measurableSet_Ioc
    have hAE_C : Du =ᵐ[volume.restrict (parabolicCylinder y.1 y.2 r)] Du' :=
      Eventually.filter_mono (ae_mono (Measure.restrict_mono hr.2.2 le_rfl))
        hDu.ae_eq_mk
    have hgradG :
        (∫⁻ w in parabolicCylinder y.1 y.2 r,
            ENNReal.ofReal (spatialGradientSq u Du w)) ≤
          ∫⁻ w in parabolicCylinder y.1 y.2 r, G w := by
      apply lintegral_mono_ae
      filter_upwards [hAE_C, ae_restrict_mem hCmeas] with w hw hwC
      change ENNReal.ofReal (spatialGradientSq u Du w) ≤
        (U z.1).indicator (fun w => (9 : ℝ≥0∞) * ‖Du' w‖ₑ ^ (2 : ℝ)) w
      rw [Set.indicator_of_mem (hr.2.2 hwC)]
      calc
        ENNReal.ofReal (spatialGradientSq u Du w) =
            ENNReal.ofReal (spatialGradientSq u Du' w) := by
              congr 1
              unfold spatialGradientSq
              rw [hw]
        _ ≤ 9 * ‖Du' w‖ₑ ^ (2 : ℝ) := spatialGradientSq_enorm_le u Du' w
    have hmulG := hmul'.trans_le hgradG
    refine ⟨r, hr.1, hr.2.1, hr.2.2, ?_⟩
    have hcoe :
        ((NNReal.mk (ε₁ ^ (2 : ℕ) / 2) (by positivity) : NNReal) : ℝ≥0∞) =
          ENNReal.ofReal (ε₁ ^ (2 : ℕ) / 2) := by
      symm
      exact ENNReal.ofReal_eq_coe_nnreal (by positivity)
    rw [hcoe]
    exact hmulG
  have hεNN : 0 < (NNReal.mk (ε₁ ^ (2 : ℕ) / 2) (by positivity) : NNReal) := by
    change 0 < ε₁ ^ (2 : ℕ) / 2
    positivity
  exact parabolicHausdorffMeasure_one_eq_zero_of_small_cylinders
    hG (hUopen z.1) inter_subset_right
    hεNN hsmall hGfin

theorem singularSet_null_of_gradient_criterion_closed
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hq : 5 / 2 < q) (ε₁ : ℝ) (hε : 0 < ε₁)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hcrit : ∀ z₀ ∈ spaceTimeSet Ω I,
      Filter.limsup (fun r : ℝ =>
          (ENNReal.ofReal r)⁻¹ *
            ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
              ENNReal.ofReal (spatialGradientSq u Du w))
        (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
        IsRegularPoint Ω I u z₀) :
    parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0 := by
  rcases hsol with ⟨hΩ, hI, hIord, hqsol, hlocf, hloc, hS2, hS3, hS4⟩
  obtain ⟨Sclosed, hSclosed, hSrepr⟩ := isClosed_singularSet_within Ω I u
  have := hq
  have hbox : ∀ z : {z // z ∈ spaceTimeSet Ω I},
      ∃ Ω' J, localBox Ω I Ω' J ∧ IsOpen J ∧
        (z : ParabolicPoint) ∈ spaceTimeSet Ω' J := by
    intro z
    exact exists_local_box_nhds hΩ hI z
  choose Ω' J hΩJ using hbox
  let U (z : {z // z ∈ spaceTimeSet Ω I}) : Set ParabolicPoint :=
    spaceTimeSet (Ω' z) (J z)
  have hUopen (z : {z // z ∈ spaceTimeSet Ω I}) : IsOpen (U z) := by
    exact isOpen_spaceTimeSet (Ω' z) (J z) (hΩJ z).1.1 (hΩJ z).2.1
  let V (z : {z // z ∈ spaceTimeSet Ω I}) :
      Set {z // z ∈ spaceTimeSet Ω I} :=
    (fun y : {z // z ∈ spaceTimeSet Ω I} => (y : ParabolicPoint)) ⁻¹' U z
  have hVnhds (z : {z // z ∈ spaceTimeSet Ω I}) : V z ∈ 𝓝 z := by
    apply (hUopen z).preimage continuous_subtype_val |>.mem_nhds
    exact hΩJ z |>.2.2
  obtain ⟨A, hAcount, hAcov⟩ := countable_cover_nhds hVnhds
  let _ : Countable A := hAcount.to_subtype
  have hSA := @singularSet_null_of_gradient_criterion_closed_hSA_1 Ω I q ε₁ hε u Du p f hcrit hloc
    Ω' J hΩJ hUopen A
  have hUclosureData (z : A) :
      IsCompact (closure (U z.1)) ∧
        closure (U z.1) ⊆ spaceTimeSet Ω I := by
    rcases (hΩJ z.1).1 with ⟨_, hΩcompact, hΩsub, _, hJcompact, hJsub⟩
    let K : Set ParabolicPoint := parabolicHomeomorph ⁻¹'
      (closure (Ω' z.1) ×ˢ closure (J z.1))
    have hKcompact : IsCompact K :=
      parabolicHomeomorph.isCompact_preimage.mpr (hΩcompact.prod hJcompact)
    have hKsub : K ⊆ spaceTimeSet Ω I := by
      intro w hw
      rcases w with ⟨x, t⟩
      change x ∈ closure (Ω' z.1) ∧ t ∈ closure (J z.1) at hw
      exact ⟨hΩsub hw.1, hJsub hw.2⟩
    have hUsub : U z.1 ⊆ K := by
      intro w hw
      rcases w with ⟨x, t⟩
      change x ∈ Ω' z.1 ∧ t ∈ J z.1 at hw
      change x ∈ closure (Ω' z.1) ∧ t ∈ closure (J z.1)
      exact ⟨subset_closure hw.1, subset_closure hw.2⟩
    have hKclosed : IsClosed K := by
      exact (isClosed_closure.prod isClosed_closure).preimage
        parabolicHomeomorph.continuous
    have hclosure : closure (U z.1) ⊆ K := closure_minimal hUsub hKclosed
    exact ⟨hKcompact.of_isClosed_subset isClosed_closure hclosure,
      hclosure.trans hKsub⟩
  have hSclosureNull : ∀ z : A,
      parabolicHausdorffMeasure 1 (SingularSet Ω I u ∩ closure (U z.1)) = 0 := by
    intro z
    have hrepr : SingularSet Ω I u ∩ closure (U z.1) =
        Sclosed ∩ closure (U z.1) := by
      ext w
      change (w ∈ SingularSet Ω I u ∧ w ∈ closure (U z.1)) ↔
        (w ∈ Sclosed ∧ w ∈ closure (U z.1))
      rw [hSrepr]
      simp only [mem_inter_iff]
      constructor
      · rintro ⟨⟨hwS, _⟩, hwK⟩
        exact ⟨hwS, hwK⟩
      · rintro ⟨hwS, hwK⟩
        exact ⟨⟨hwS, (hUclosureData z).2 hwK⟩, hwK⟩
    have hSclosedPiece : IsClosed
        (SingularSet Ω I u ∩ closure (U z.1)) := by
      rw [hrepr]
      exact hSclosed.inter isClosed_closure
    have hScompact : IsCompact
        (SingularSet Ω I u ∩ closure (U z.1)) :=
      (hUclosureData z).1.of_isClosed_subset hSclosedPiece inter_subset_right
    have hcover : SingularSet Ω I u ∩ closure (U z.1) ⊆
        ⋃ a : A, U a.1 := by
      intro w hw
      let w' : {x // x ∈ spaceTimeSet Ω I} := ⟨w, hw.1.1⟩
      have hwV : w' ∈ ⋃ a ∈ A, V a := by
        rw [hAcov]
        trivial
      rcases mem_iUnion₂.1 hwV with ⟨a, haA, hwa⟩
      refine mem_iUnion.2 ⟨⟨a, haA⟩, ?_⟩
      simpa [V] using hwa
    obtain ⟨t, ht⟩ := hScompact.elim_finite_subcover
      (fun a : A => U a.1) (fun a => hUopen a.1) hcover
    have hfiniteNull : parabolicHausdorffMeasure 1
        (⋃ a : t, SingularSet Ω I u ∩ U a.1.1) = 0 :=
      measure_iUnion_null (fun a => hSA a.1)
    have hsub : SingularSet Ω I u ∩ closure (U z.1) ⊆
        ⋃ a : t, SingularSet Ω I u ∩ U a.1.1 := by
      intro w hw
      rcases mem_iUnion₂.1 (ht hw) with ⟨a, ha, hwa⟩
      exact mem_iUnion.2 ⟨⟨a, ha⟩, ⟨hw.1, hwa⟩⟩
    apply le_antisymm
    · calc
        parabolicHausdorffMeasure 1 (SingularSet Ω I u ∩ closure (U z.1)) ≤
            parabolicHausdorffMeasure 1
              (⋃ a : t, SingularSet Ω I u ∩ U a.1.1) := measure_mono hsub
        _ = 0 := hfiniteNull
    · exact bot_le
  have hcover : SingularSet Ω I u ⊆
      ⋃ z : A, SingularSet Ω I u ∩ closure (U z.1) := by
    intro y hy
    let y' : {z // z ∈ spaceTimeSet Ω I} := ⟨y, hy.1⟩
    have hyV : y' ∈ ⋃ z ∈ A, V z := by
      rw [hAcov]
      trivial
    rcases mem_iUnion₂.1 hyV with ⟨z, hzA, hyVz⟩
    have hyU : y ∈ U z := by simpa [V] using hyVz
    exact mem_iUnion.2 ⟨⟨z, hzA⟩, ⟨hy, subset_closure hyU⟩⟩
  apply le_antisymm
  · calc
      parabolicHausdorffMeasure 1 (SingularSet Ω I u) ≤
          parabolicHausdorffMeasure 1 (⋃ z : A,
            SingularSet Ω I u ∩ closure (U z.1)) := measure_mono hcover
      _ = 0 := measure_iUnion_null hSclosureNull
  · exact bot_le

end CKN
