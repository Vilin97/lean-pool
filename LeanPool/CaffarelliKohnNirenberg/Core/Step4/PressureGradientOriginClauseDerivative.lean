/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseDerivativeLocal
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseDerivativeGeometry
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsBridge

/-! # Clipped origin growth from the fixed derivative decomposition

The harmonic and far-force temporal envelope is the same input as in the
fixed-field derivative construction. A finite relative cover of the backward
origin carrier transfers the local signed decompositions to one measurable
weak gradient. Its actual clipped spatial norms supply the growth estimate.
The finite-cover argument uses the same-repository collar assembly pattern;
its backward patches include the final time without requiring future Morrey data.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Foundation.Heat
open CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

private theorem derivative_finite_cover_morrey
    {κ : ℝ} {K : Set ParabolicPoint} {D : ParabolicPoint → ℝ}
    (hD : Measurable D) {ι : Type*} (s : Finset ι) (U : ι → Set ParabolicPoint)
    (hU : ∀ a ∈ s, MeasurableSet (U a)) (hcover : K ⊆ ⋃ a ∈ s, U a)
    (hN : ∀ a ∈ s, morreyNorm (6/5 : ℝ) κ ((U a).indicator D) < ⊤) :
    morreyNorm (6/5 : ℝ) κ (K.indicator D) < ⊤ := by
  classical
  have hsum : morreyNorm (6/5 : ℝ) κ
      (fun w => ∑ a ∈ s, |(U a).indicator D w|) < ⊤ := by
    apply finite_sum_morreyNorm_lt_top (by norm_num)
      s (F := fun a w => |(U a).indicator D w|)
      (fun a ha => by simpa only [Function.comp_def, Real.norm_eq_abs] using
        measurable_norm.comp (hD.indicator (hU a ha)))
    intro a ha
    rw [morreyNorm_abs]
    exact hN a ha
  apply (routeA_morreyNorm_mono_ae (by norm_num : (0 : ℝ) ≤ 6/5)
    (Eventually.of_forall ?_)).trans_lt hsum
  intro w
  rw [show |(∑ a ∈ s, |(U a).indicator D w|)| = ∑ a ∈ s, |(U a).indicator D w| from
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))]
  by_cases hw : w ∈ K
  · obtain ⟨a, ha, haw⟩ := mem_iUnion₂.mp (hcover hw)
    rw [indicator_of_mem hw]
    calc
      |D w| = |(U a).indicator D w| := by rw [indicator_of_mem haw]
      _ ≤ ∑ b ∈ s, |(U b).indicator D w| := Finset.single_le_sum (f := fun b => |(U b).indicator D w|)
        (fun _ _ => abs_nonneg _) ha
  · rw [indicator_of_notMem hw, abs_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- The fixed harmonic/far temporal-envelope input gives finite Morrey norms
of one selected weak pressure derivative on the entire backward origin carrier.
Only the original larger-carrier velocity and gradient Morrey data are used. -/
theorem originClause_derivative_morrey_of_shared_remainder
    (hrem : ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      ∃ M : ℝ → ℝ≥0∞, AEMeasurable M volume ∧
        (∫⁻ s, M s ^ (3 / 2 : ℝ)) < ⊤ ∧
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
            ‖classicalGradient
              (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                (sourceSliceCentredMean z.1 ρ u) p s +
                pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤ M s)
    {q τ R₀ R₁ : ℝ} {KU KD : ℝ≥0∞}
    (hq : 5/2 < q) (hτ : 25/3 ≤ τ) (hτhi : τ ≤ 25)
    (hR₁ : 0 < R₁) (hgap : R₁ < R₀) (hR₀ : R₀ < 1)
    (hKU : KU < ⊤) (hKD : KD < ⊤)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hU : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => u w i)) ≤ KU)
    (hDu : ∀ i j, morreyNorm 2 (25/8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => Du w i j)) ≤ KD) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
          (fun y => p (y,s)) (fun y => Dp (y,s) i)) ∧
      ∀ i : Fin 3, morreyNorm (6/5 : ℝ) (min ((1/τ+8/25)⁻¹) q)
        ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun w => Dp w i)) < ⊤ := by
  classical
  let κ := min ((1/τ+8/25)⁻¹) q
  let Q := parabolicCylinder (0 : Vec3) 0 R₁
  let K := closure Q
  have hR₀pos := hR₁.trans hgap
  obtain ⟨Dp, hm, hw⟩ := origin_measurable_weak_gradient_of_sws hsol hdom hR₀pos hR₀
  have hlocal (w : K) : ∃ U : Set ParabolicPoint, IsOpen U ∧ w.1 ∈ U ∧
      ∀ i : Fin 3, morreyNorm (6/5 : ℝ) κ ((U ∩ Q).indicator (fun v => Dp v i)) < ⊤ := by
    obtain ⟨z, ρ, U, hρ, ho, hwu, hcl, hQ, hB, hcut⟩ :=
      originClause_backward_derivative_patch hR₁ hgap w.2
    have hsub := hcl.trans ((closure_parabolicCylinder_mono hR₀pos.le hR₀.le).trans hdom)
    have hbox := originClause_localBox_of_closed_cylinder hρ hsub
    have hUI (i : Fin 3) : morreyNorm 3 τ
        ((parabolicCylinder z.1 z.2 ρ).indicator (fun v => u v i)) < ⊤ :=
      ((morreyNorm_indicator_mono_set (by norm_num) hQ _).trans (hU i)).trans_lt hKU
    have hDI (i j : Fin 3) : morreyNorm 2 (25/8 : ℝ)
        ((parabolicCylinder z.1 z.2 ρ).indicator (fun v => Du v i j)) < ⊤ :=
      ((morreyNorm_indicator_mono_set (by norm_num) hQ _).trans (hDu i j)).trans_lt hKD
    have hJI : Ioc (z.2-ρ^2) z.2 ⊆ I := subset_closure.trans hbox.2.2.2.2.2
    have hwlocal : ∀ᵐ s ∂volume.restrict (Ioc (z.2-ρ^2) z.2), ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball z.1 (ρ/2)) volume ∧
        HasWeakPartialDerivOn (vec3Ball z.1 (ρ/2)) i
          (fun y => p (y,s)) (fun y => Dp (y,s) i) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI hw] with s hs i
      exact ⟨(hs i).1.mono_set hB, (hs i).2.1.restrict (isOpen_vec3Ball _ _) hB⟩
    have hn := originClause_local_derivative_morrey_of_remainder hq hτ hτhi hρ
      (hrem hsol hρ hsub) hsol hsub hbox hUI hDI hm hwlocal
    refine ⟨U, ho, hwu, fun i => ?_⟩
    exact (morreyNorm_indicator_mono_set (by norm_num) hcut _).trans_lt (hn i)
  choose U hUopen hUmem hUn using hlocal
  have hcover : K ⊆ ⋃ w : K, U w := by
    intro w hwK
    exact mem_iUnion.mpr ⟨⟨w,hwK⟩, hUmem ⟨w,hwK⟩⟩
  obtain ⟨s, hs⟩ := (originClause_closed_carrier_compact hR₁).elim_finite_subcover U hUopen hcover
  refine ⟨Dp, hm, ?_, ?_⟩
  · filter_upwards [hw] with t ht i
    have hb := vec3Ball_mono (x := (0 : Vec3)) hgap.le
    exact ⟨(ht i).1.mono_set hb, (ht i).2.1.restrict (isOpen_vec3Ball _ _) hb⟩
  · intro i
    apply derivative_finite_cover_morrey ((measurable_pi_apply i).comp hm) s
      (fun w => U w ∩ Q) (fun w _ => (hUopen w).measurableSet.inter
        (measurableSet_parabolicCylinder _ _ _)) ?_ (fun w _ => hUn w i)
    intro v hv
    obtain ⟨w, hws, hvw⟩ := mem_iUnion₂.mp (hs (subset_closure hv))
    exact mem_iUnion₂.mpr ⟨w,hws,hvw,hv⟩

/-- The actual clipped slice norms of one selected derivative obey the
origin clause's growth formula with a single finite coefficient before all
components, centres, and positive radii. The only analytic input beyond the
standing solution data is the shared fixed harmonic/far temporal envelope. -/
theorem originClause_clipped_growth_of_shared_remainder
    (hrem : ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      ∃ M : ℝ → ℝ≥0∞, AEMeasurable M volume ∧
        (∫⁻ s, M s ^ (3 / 2 : ℝ)) < ⊤ ∧
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
            ‖classicalGradient
              (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                (sourceSliceCentredMean z.1 ρ u) p s +
                pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤ M s)
    {q τ R₀ R₁ : ℝ} {KU KD : ℝ≥0∞}
    (hq : 5/2 < q) (hτ : 25/3 ≤ τ) (hτhi : τ ≤ 25)
    (hR₁ : 0 < R₁) (hgap : R₁ < R₀) (hR₀ : R₀ < 1)
    (hKU : KU < ⊤) (hKD : KD < ⊤)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hU : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => u w i)) ≤ KU)
    (hDu : ∀ i j, morreyNorm 2 (25/8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => Du w i j)) ≤ KD) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
          (fun y => p (y,s)) (fun y => Dp (y,s) i)) ∧
      ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ (i : Fin 3) (z : ParabolicPoint) (r : ℝ), 0 < r →
        (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-R₁^2) 0,
          eLpNorm (fun y => Dp (y,s) i) (ENNReal.ofReal (6/5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6/5 : ℝ)) ≤
          A * ENNReal.ofReal (r ^ (5 * (1 - (6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))) := by
  obtain ⟨Dp, hm, hw, hn⟩ := originClause_derivative_morrey_of_shared_remainder
    hrem hq hτ hτhi hR₁ hgap hR₀ hKU hKD hsol hdom hU hDu
  let κ := min ((1/τ+8/25)⁻¹) q
  let Q := parabolicCylinder (0 : Vec3) 0 R₁
  let N := fun i : Fin 3 => morreyNorm (6/5 : ℝ) κ (Q.indicator (fun w => Dp w i))
  let A := ∑ i : Fin 3, N i ^ (6/5 : ℝ)
  have hA : A < ⊤ := ENNReal.sum_lt_top.mpr
    (fun i _ => ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hn i).ne)
  refine ⟨Dp,hm,hw,A,hA,?_⟩
  intro i z r hr
  have hQm : MeasurableSet Q := measurableSet_parabolicCylinder _ _ _
  have hFi := (measurable_pi_apply i).comp hm
  have hmass := cylinderPowerIntegral_le_morreyNorm_pow (q := κ)
    (by norm_num : (0 : ℝ) < 6/5) (hFi.indicator hQm).aemeasurable (z := z) hr
  rw [ENNReal.ofReal_rpow_of_pos hr] at hmass
  have hnA : N i ^ (6/5 : ℝ) ≤ A :=
    Finset.single_le_sum (f := fun j : Fin 3 => N j ^ (6/5 : ℝ))
      (fun _ _ => bot_le) (Finset.mem_univ i)
  have hbound : cylinderPowerIntegral (6/5 : ℝ) (Q.indicator (fun w => Dp w i)) z r ≤
      A * ENNReal.ofReal (r ^ (5 * (1 - (6/5 : ℝ)/κ))) :=
    hmass.trans ((mul_le_mul' le_rfl hnA).trans_eq (mul_comm _ _))
  have hprod : AEStronglyMeasurable (fun w => Dp w i)
      ((volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)).prod
        (volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-R₁^2) 0))) := by
    rw [← originClauseRestrict_prod_eq]
    exact hFi.aestronglyMeasurable.restrict
  rw [(glued_slice_norm_power_integral (by norm_num : (0 : ℝ) < 6/5) hprod).2]
  rw [cylinderPowerIntegral_carrier_eq (by norm_num) hQm,
    parabolicCylinder_inter_origin_eq_prod] at hbound
  convert hbound using 1
  simp only [Real.enorm_eq_ofReal_abs]
  rfl

end CKN.Core.Step4
