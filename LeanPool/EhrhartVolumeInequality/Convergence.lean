/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.EhrhartVolumeInequality.Convexity
import all LeanPool.EhrhartVolumeInequality.Convexity

/-!
# Ehrhart volume inequality: Convergence

The final concentration argument and Ehrhart volume inequality.
-/

noncomputable local instance {n : ℕ} :
    CoeFun (ContDiffBump (0 : Fin n → ℝ)) (fun _ => (Fin n → ℝ) → ℝ) :=
  ⟨ContDiffBump.toFun⟩

noncomputable section

namespace Ehrhart

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace BergmanJetDualGradientConcentration

open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentInteriorLegendre
open scoped ENNReal NNReal Topology

private theorem ae_differentiableAt_of_locallyLipschitzOn_open
    {n : ℕ} {s : Set (Space n)}
    (hs : IsOpen s) {f : Space n → ℝ}
    (hf : LocallyLipschitzOn s f) :
    ∀ᵐ x : Space n ∂(volume : Measure (Space n)),
      x ∈ s → DifferentiableAt ℝ f x := by
  classical
  have hlocal : ∀ x : s,
      ∃ (u : Set (Space n)) (C : ℝ≥0),
        IsOpen u ∧ (x : Space n) ∈ u ∧
          u ⊆ s ∧ LipschitzOnWith C f u := by
    intro x
    obtain ⟨C, t, ht, hft⟩ := hf x.property
    have ht' : t ∈ 𝓝 (x : Space n) := by
      rw [nhdsWithin_eq_nhds.mpr (hs.mem_nhds x.property)] at ht
      exact ht
    obtain ⟨v, hvt, hvopen, hxv⟩ := mem_nhds_iff.mp ht'
    refine ⟨v ∩ s, C, hvopen.inter hs,
      ⟨hxv, x.property⟩, inter_subset_right, ?_⟩
    exact hft.mono (fun y hy => hvt hy.1)
  choose u C huopen hux hus hflip using hlocal
  obtain ⟨T, hT, hTu⟩ :=
    TopologicalSpace.isOpen_iUnion_countable u huopen
  have hucover : (⋃ x : s, u x) = s := by
    apply le_antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hus i hi
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hux ⟨x, hx⟩⟩
  have hTcover : (⋃ i ∈ T, u i) = s := hTu.trans hucover
  have hae :
      ∀ᵐ x : Space n
        ∂((volume : Measure (Space n)).restrict s),
        DifferentiableAt ℝ f x := by
    rw [← hTcover]
    apply (ae_restrict_biUnion_iff u hT _).2
    intro i _hi
    have hrad :
        ∀ᵐ x : Space n
          ∂((volume : Measure (Space n)).restrict (u i)),
          DifferentiableWithinAt ℝ f (u i) x :=
      (hflip i).ae_differentiableWithinAt (huopen i).measurableSet
    filter_upwards [hrad,
      ae_restrict_mem (huopen i).measurableSet] with x hx hxu
    exact hx.differentiableAt ((huopen i).mem_nhds hxu)
  exact ae_imp_of_ae_restrict hae

private theorem ae_differentiableAt_finiteEnergySourceLegendre_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᵐ u : Space n ∂(volume : Measure (Space n)),
      u ∈ interior K.carrier →
        DifferentiableAt ℝ (legendreTransform F.potential) u := by
  exact ae_differentiableAt_of_locallyLipschitzOn_open
    isOpen_interior
    (locallyLipschitzOn_finiteEnergySourceLegendre_interior
      F htransport)

private theorem ae_differentiableAt_finiteEnergySourceLegendre_interior_restrict
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᵐ u : Space n
      ∂((volume : Measure (Space n)).restrict
        (interior K.carrier)),
      DifferentiableAt ℝ (legendreTransform F.potential) u := by
  exact (ae_restrict_iff' isOpen_interior.measurableSet).2
    (ae_differentiableAt_finiteEnergySourceLegendre_interior
      F htransport)

private theorem ae_differentiableAt_finiteEnergySourceLegendre_target
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᵐ u : Space n ∂(normalizedTargetBodyMeasure K),
      DifferentiableAt ℝ (legendreTransform F.potential) u := by
  rw [normalizedTargetBodyMeasure_eq_interior_restrict K]
  exact Measure.ae_smul_measure
    (ae_differentiableAt_finiteEnergySourceLegendre_interior_restrict
      F htransport)
    (((volume : Measure (Space n)) K.carrier)⁻¹)

end BergmanJetDualGradientConcentration

namespace BergmanJetDualPhaseConcentration

open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open MomentRegularity MomentInteriorLegendre
open scoped BigOperators ENNReal NNReal Topology

private theorem finiteEnergySourceLegendre_gradient_eq_phaseMaximizer
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hdu : DifferentiableAt ℝ (legendreTransform F.potential) u)
    (x : Space n)
    (hmax : ∀ z : Space n,
      phase u F.potential z ≤ phase u F.potential x) :
    SpatialBergmanFatouScheffe.actualGradient
      (legendreTransform F.potential) u = x := by
  classical
  ext i
  let v : Space n := Pi.single i (1 : ℝ)
  have hline : HasDerivAt
      (fun t : ℝ => u + t • v) v 0 := by
    simpa only [hasDerivAt_const_add_iff, id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have hpair : HasDerivAt
      (fun t : ℝ => pairing (u + t • v) x)
      (pairing v x) 0 := by
    simpa only [pairing_add_left, pairing_smul_left, hasDerivAt_const_add_iff, id_eq, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const
        (pairing v x)).const_add (pairing u x)
  have hdual : HasDerivAt
      (fun t : ℝ =>
        legendreTransform F.potential (u + t • v))
      ((fderiv ℝ (legendreTransform F.potential) u) v) 0 := by
    have hu0 : u = (fun t : ℝ => u + t • v) 0 := by
      simp only [zero_smul, add_zero]
    simpa only [comp_def] using
      hdu.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline hu0
  have hinterior :
      ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), u + t • v ∈ interior K.carrier := by
    have hmem :
        interior K.carrier ∈
          𝓝 ((fun t : ℝ => u + t • v) 0) := by
      simpa only [zero_smul, add_zero, interior_mem_nhds] using isOpen_interior.mem_nhds hu
    exact hline.continuousAt hmem
  have hlocal : IsLocalMin
      (fun t : ℝ =>
        legendreTransform F.potential (u + t • v) -
          pairing (u + t • v) x) 0 := by
    filter_upwards [hinterior] with t ht
    have hbound :=
      finiteEnergySourcePhase_bddAbove_of_mem_interior
        F htransport ht
    have hfen :
        phase (u + t • v) F.potential x ≤
          legendreTransform F.potential (u + t • v) := by
      exact le_csSup hbound ⟨x, rfl⟩
    have hbase := legendreTransform_eq_of_maximizer x hmax
    simp only [zero_smul, add_zero]
    rw [hbase]
    unfold phase at hfen ⊢
    linarith
  have hzero :
      (fderiv ℝ (legendreTransform F.potential) u) v -
        pairing v x = 0 := by
    have hd := (hdual.sub hpair).deriv
    change
      deriv
        (fun t : ℝ =>
          legendreTransform F.potential (u + t • v) -
            pairing (u + t • v) x) 0 =
          (fderiv ℝ (legendreTransform F.potential) u) v -
            pairing v x at hd
    rw [hlocal.deriv_eq_zero] at hd
    linarith
  have hcoordinate :
      pairing
        (SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential) u) v =
        pairing x v := by
    rw [SpatialBergmanFatouScheffe.pairing_actualGradient_eq_fderiv]
    have hcomm : pairing v x = pairing x v := by
      simp only [pairing, mul_comm]
    linarith
  simpa [v, pairing, Pi.single_apply] using hcoordinate

private theorem momentNormalized_phaseMaximizer_iff
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (u x : Space n) :
    (∀ z : Space n,
      phase u (momentNormalizedPotential F) z ≤
        phase u (momentNormalizedPotential F) x) ↔
    (∀ z : Space n,
      phase u F.potential z ≤ phase u F.potential x) := by
  constructor <;> intro h z
  · have hz := h z
    simp only [phase, momentNormalizedPotential] at hz ⊢
    linarith
  · have hz := h z
    simp only [phase, momentNormalizedPotential] at hz ⊢
    linarith

end BergmanJetDualPhaseConcentration

namespace BergmanJetMovingPhaseConcentration

open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman BergmanJetPhaseLaplace
open BergmanJetDualPhaseConcentration
open scoped BigOperators ENNReal NNReal Topology

private theorem momentNormalized_off_phase_setIntegral_le_exp_mul_base
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {s : Set (Space n)} (hs : MeasurableSet s)
    {M : ℝ}
    (hphase : ∀ x ∈ s,
      phase u (momentNormalizedPotential F) x ≤ M)
    {k : ℝ} (hk : 1 ≤ k) :
    (∫ x : Space n in s,
      monomialWeight k u (momentNormalizedPotential F) x
      ∂(volume : Measure (Space n))) ≤
      Real.exp ((k - 1) * M) *
        monomialIntegral 1 u (momentNormalizedPotential F) := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hkint :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hu hkpos
  have hbase :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hu (k := (1 : ℝ)) zero_lt_one
  have hmajor := hbase.const_mul (Real.exp ((k - 1) * M))
  calc
    (∫ x : Space n in s,
      monomialWeight k u (momentNormalizedPotential F) x
      ∂(volume : Measure (Space n))) ≤
      ∫ x : Space n in s,
        Real.exp ((k - 1) * M) *
          monomialWeight 1 u (momentNormalizedPotential F) x
        ∂(volume : Measure (Space n)) := by
      apply setIntegral_mono_on hkint.integrableOn
        hmajor.integrableOn hs
      intro x hx
      unfold monomialWeight
      change
        Real.exp (k *
          (pairing u x - momentNormalizedPotential F x)) ≤
          Real.exp ((k - 1) * M) *
            Real.exp (1 *
              (pairing u x - momentNormalizedPotential F x))
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := hphase x hx
      unfold phase at h
      nlinarith
    _ ≤ ∫ x : Space n,
        Real.exp ((k - 1) * M) *
          monomialWeight 1 u (momentNormalizedPotential F) x
        ∂(volume : Measure (Space n)) := by
      apply setIntegral_le_integral hmajor
      exact Filter.Eventually.of_forall fun x =>
        mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp ((k - 1) * M) *
          monomialIntegral 1 u (momentNormalizedPotential F) := by
      rw [integral_const_mul]
      rfl

private theorem exists_momentNormalized_phase_gap_outside_ball
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hdu : DifferentiableAt ℝ (legendreTransform F.potential) u)
    (x₀ : Space n)
    (hmax : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤
        phase u (momentNormalizedPotential F) x₀)
    {r : ℝ} (hr : 0 < r) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : Space n,
      x ∉ Metric.ball x₀ r →
        phase u (momentNormalizedPotential F) x ≤
          phase u (momentNormalizedPotential F) x₀ - η := by
  obtain ⟨δ, C, hδ, hcoercive⟩ :=
    exists_momentNormalized_phase_linear_coercivity
      F htransport hu
  let R : ℝ :=
    max 0 ((C - phase u (momentNormalizedPotential F) x₀ + 1) / δ)
  have houter : ∀ x : Space n,
      x ∉ Metric.closedBall (0 : Space n) R →
        phase u (momentNormalizedPotential F) x ≤
          phase u (momentNormalizedPotential F) x₀ - 1 := by
    intro x hx
    have hxnorm : R < ‖x‖ := by
      apply lt_of_not_ge
      intro h
      apply hx
      simpa only [mem_closedBall, dist_zero_right] using h
    have hR :
        C - phase u (momentNormalizedPotential F) x₀ + 1 ≤
          δ * R := by
      have hle :
          (C - phase u (momentNormalizedPotential F) x₀ + 1) / δ ≤ R :=
        le_max_right _ _
      simpa only [ge_iff_le, mul_comm] using (div_le_iff₀ hδ).mp hle
    have hscale := mul_lt_mul_of_pos_left hxnorm hδ
    have hcoerce := hcoercive x
    nlinarith
  let t : Set (Space n) :=
    Metric.closedBall (0 : Space n) R ∩
      (Metric.ball x₀ r)ᶜ
  have htcompact : IsCompact t := by
    exact (isCompact_closedBall (0 : Space n) R).inter_right
      Metric.isOpen_ball.isClosed_compl
  by_cases ht : t.Nonempty
  · obtain ⟨z, hz, hzmax⟩ :=
      htcompact.exists_isMaxOn ht
        (continuous_phase u
          (continuous_momentNormalizedPotential F)).continuousOn
    have hzout : z ∉ Metric.ball x₀ r := hz.2
    have hzne : z ≠ x₀ := by
      intro heq
      subst z
      exact hzout (Metric.mem_ball_self hr)
    have hznephase :
        phase u (momentNormalizedPotential F) z ≠
          phase u (momentNormalizedPotential F) x₀ := by
      intro heq
      have hzglobal : ∀ y : Space n,
          phase u (momentNormalizedPotential F) y ≤
            phase u (momentNormalizedPotential F) z := by
        intro y
        rw [heq]
        exact hmax y
      have hxdual := finiteEnergySourceLegendre_gradient_eq_phaseMaximizer
        F htransport hu hdu x₀
        ((momentNormalized_phaseMaximizer_iff F u x₀).mp hmax)
      have hzdual := finiteEnergySourceLegendre_gradient_eq_phaseMaximizer
        F htransport hu hdu z
        ((momentNormalized_phaseMaximizer_iff F u z).mp hzglobal)
      exact hzne (hxdual.symm.trans hzdual).symm
    have hzlt :
        phase u (momentNormalizedPotential F) z <
          phase u (momentNormalizedPotential F) x₀ :=
      lt_of_le_of_ne (hmax z) hznephase
    let η : ℝ :=
      min 1 (phase u (momentNormalizedPotential F) x₀ -
        phase u (momentNormalizedPotential F) z)
    have hη : 0 < η :=
      lt_min zero_lt_one (sub_pos.mpr hzlt)
    refine ⟨η, hη, fun x hx => ?_⟩
    by_cases hxR : x ∈ Metric.closedBall (0 : Space n) R
    · have hxt : x ∈ t := ⟨hxR, hx⟩
      have hzx :
          phase u (momentNormalizedPotential F) x ≤
            phase u (momentNormalizedPotential F) z := hzmax hxt
      have hηle :
          η ≤ phase u (momentNormalizedPotential F) x₀ -
            phase u (momentNormalizedPotential F) z :=
        min_le_right _ _
      linarith
    · have hout := houter x hxR
      have hηle : η ≤ (1 : ℝ) := min_le_left _ _
      linarith
  · refine ⟨1, zero_lt_one, fun x hx => ?_⟩
    apply houter x
    intro hxR
    exact ht ⟨x, hxR, hx⟩

end BergmanJetMovingPhaseConcentration

namespace BergmanJetMovingMonomialConcentration

open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open MomentRegularity MomentWeakBergman BergmanJetMovingPhaseConcentration
open scoped BigOperators ENNReal NNReal Topology

private theorem concaveOn_momentNormalized_phase
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (u : Space n) :
    ConcaveOn ℝ Set.univ
      (phase u (momentNormalizedPotential F)) := by
  have hlinear :
      ConcaveOn ℝ Set.univ
        (BergmanAsymptotics.pairingLinear u) :=
    (BergmanAsymptotics.pairingLinear u).concaveOn convex_univ
  have hphase :
      (BergmanAsymptotics.pairingLinear u :
        Space n → ℝ) -
          momentNormalizedPotential F =
        phase u (momentNormalizedPotential F) := by
    funext x
    rfl
  rw [← hphase]
  exact hlinear.sub (convexOn_momentNormalizedPotential F)

private theorem concave_radial_gap_of_off_ball
    {n : ℕ} {f : Space n → ℝ}
    (hconc : ConcaveOn ℝ Set.univ f)
    (x₀ : Space n)
    {r η : ℝ} (hr : 0 < r)
    (hgap : ∀ x : Space n,
      x ∉ Metric.ball x₀ r → f x ≤ f x₀ - η)
    (x : Space n)
    (hx : r ≤ ‖x - x₀‖) :
    f x ≤ f x₀ - (η / r) * ‖x - x₀‖ := by
  let d : ℝ := ‖x - x₀‖
  let t : ℝ := r / d
  have hd : 0 < d := lt_of_lt_of_le hr hx
  have htpos : 0 < t := div_pos hr hd
  have htone : t ≤ 1 := (div_le_one hd).mpr hx
  let y : Space n := x₀ + t • (x - x₀)
  have hydist : dist y x₀ = r := by
    calc
      dist y x₀ = ‖t • (x - x₀)‖ := by
        dsimp [y]
        rw [dist_eq_norm]
        simp only [add_sub_cancel_left]
      _ = t * d := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      _ = r := by
        dsimp [t]
        exact div_mul_cancel₀ r hd.ne'
  have hyout : y ∉ Metric.ball x₀ r := by
    rw [Metric.mem_ball]
    exact not_lt.mpr (le_of_eq hydist.symm)
  have hsegle :
      (1 - t) * f x₀ + t * f x ≤ f y := by
    have hraw := hconc.2
      (Set.mem_univ x₀) (Set.mem_univ x)
      (sub_nonneg.mpr htone) htpos.le
      (show (1 - t) + t = 1 by ring)
    have hcomb : (1 - t) • x₀ + t • x = y := by
      dsimp [y]
      module
    rw [hcomb] at hraw
    simpa only [ge_iff_le, smul_eq_mul] using hraw
  have hygap := hgap y hyout
  have htbound : t * (f x - f x₀) ≤ -η := by
    linarith
  have hquot : (r * (f x - f x₀)) / d ≤ -η := by
    calc
      (r * (f x - f x₀)) / d =
        t * (f x - f x₀) := by
          dsimp [t]
          ring
      _ ≤ -η := htbound
  have hscale : r * (f x - f x₀) ≤ -η * d :=
    (div_le_iff₀ hd).mp hquot
  have hratio : (η / r) * r = η :=
    div_mul_cancel₀ η hr.ne'
  nlinarith

private theorem exists_eventual_momentNormalized_moving_phase_gap_outside_ball
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (hdu₀ : DifferentiableAt ℝ (legendreTransform F.potential) u₀)
    (x₀ : Space n)
    (hmax : ∀ x : Space n,
      phase u₀ (momentNormalizedPotential F) x ≤
        phase u₀ (momentNormalizedPotential F) x₀)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    {r : ℝ} (hr : 0 < r) :
    ∃ η : ℝ, 0 < η ∧
      ∀ᶠ k : ℕ in atTop, ∀ x : Space n,
        x ∉ Metric.ball x₀ r →
          phase (u k) (momentNormalizedPotential F) x ≤
            phase (u k) (momentNormalizedPotential F) x₀ - η := by
  obtain ⟨η, hη, hgap⟩ :=
    exists_momentNormalized_phase_gap_outside_ball
      F htransport hu₀ hdu₀ x₀ hmax (half_pos hr)
  have hnorm :
      Tendsto
        (fun k : ℕ => (n : ℝ) * ‖u k - u₀‖)
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, mul_zero] using ((hu.sub_const u₀).norm).const_mul (n : ℝ)
  have hsmall :
      ∀ᶠ k : ℕ in atTop,
        (n : ℝ) * ‖u k - u₀‖ < η / r :=
    hnorm (Iio_mem_nhds (div_pos hη hr))
  refine ⟨η, hη, ?_⟩
  filter_upwards [hsmall] with k hk x hx
  have hdist : r ≤ ‖x - x₀‖ := by
    have hd : r ≤ dist x x₀ := by
      exact le_of_not_gt (by simpa only [not_lt, mem_ball] using hx)
    simpa only [ge_iff_le, dist_eq_norm] using hd
  have hradial := concave_radial_gap_of_off_ball
    (concaveOn_momentNormalized_phase F u₀)
    x₀ (half_pos hr) hgap x (le_trans (by linarith) hdist)
  have hpert :
      pairing (u k - u₀) (x - x₀) ≤
        (η / r) * ‖x - x₀‖ := by
    calc
      pairing (u k - u₀) (x - x₀) ≤
          |pairing (u k - u₀) (x - x₀)| := le_abs_self _
      _ ≤ ((n : ℝ) * ‖u k - u₀‖) * ‖x - x₀‖ :=
        MonomialDivergence.abs_pairing_le_dimension_mul_norm
          (u k - u₀) (x - x₀)
      _ ≤ (η / r) * ‖x - x₀‖ :=
        mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)
  have hsplit :
      phase (u k) (momentNormalizedPotential F) x -
          phase (u k) (momentNormalizedPotential F) x₀ =
        (phase u₀ (momentNormalizedPotential F) x -
          phase u₀ (momentNormalizedPotential F) x₀) +
            pairing (u k - u₀) (x - x₀) := by
    simp only [phase, pairing, Pi.sub_apply, sub_mul, mul_sub,
      Finset.sum_sub_distrib]
    ring
  have hscale : (η / r) * ‖x - x₀‖ ≥ η := by
    have hq : 0 ≤ η / r := (div_pos hη hr).le
    calc
      η = (η / r) * r := (div_mul_cancel₀ η hr.ne').symm
      _ ≤ (η / r) * ‖x - x₀‖ :=
        mul_le_mul_of_nonneg_left hdist hq
  have hhalf : η / (r / 2) = 2 * (η / r) := by
    field_simp
  rw [hhalf] at hradial
  linarith

end BergmanJetMovingMonomialConcentration

namespace BergmanJetMovingMonomialProbability

open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman
open scoped BigOperators ENNReal NNReal Topology

private theorem exists_eventual_momentNormalized_moving_ball_volume_exp_le_monomialIntegral
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    (x₀ : Space n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧
      0 < (volume : Measure (Space n)).real
        (Metric.ball x₀ r) ∧
      ∀ᶠ j : ℕ in atTop, ∀ {k : ℝ}, 0 < k →
        (volume : Measure (Space n)).real
            (Metric.ball x₀ r) *
          Real.exp
            (k *
              (phase (u j) (momentNormalizedPotential F) x₀ - ε)) ≤
        monomialIntegral k (u j) (momentNormalizedPotential F) := by
  let φ : Space n → ℝ := momentNormalizedPotential F
  have hopen : IsOpen
      {x : Space n |
        phase u₀ φ x₀ - ε / 2 < phase u₀ φ x} :=
    isOpen_lt continuous_const
      (continuous_phase u₀ (continuous_momentNormalizedPotential F))
  have hx₀ : x₀ ∈
      {x : Space n |
        phase u₀ φ x₀ - ε / 2 < phase u₀ φ x} := by
    change phase u₀ φ x₀ - ε / 2 < phase u₀ φ x₀
    linarith
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp hopen) x₀ hx₀
  have hballpos :
      0 < (volume : Measure (Space n))
        (Metric.ball x₀ r) := by
    apply (volume : Measure (Space n)).measure_pos_of_nonempty_interior
    rw [Metric.isOpen_ball.interior_eq]
    exact ⟨x₀, Metric.mem_ball_self hr⟩
  have hballfinite :
      (volume : Measure (Space n))
        (Metric.ball x₀ r) ≠ ⊤ :=
    (measure_ball_lt_top
      (μ := (volume : Measure (Space n)))
      (x := x₀) (r := r)).ne
  have hrealpos :
      0 < (volume : Measure (Space n)).real
        (Metric.ball x₀ r) :=
    ENNReal.toReal_pos hballpos.ne' hballfinite
  have hnorm :
      Tendsto
        (fun j : ℕ => ((n : ℝ) * ‖u j - u₀‖) * r)
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, mul_zero, zero_mul] using
      (((hu.sub_const u₀).norm).const_mul (n : ℝ)).mul_const r
  have hsmall :
      ∀ᶠ j : ℕ in atTop,
        ((n : ℝ) * ‖u j - u₀‖) * r < ε / 2 :=
    hnorm (Iio_mem_nhds (half_pos hε))
  have hinterior :
      ∀ᶠ j : ℕ in atTop, u j ∈ interior K.carrier :=
    hu.eventually (isOpen_interior.mem_nhds hu₀)
  refine ⟨r, hr, hrealpos, ?_⟩
  filter_upwards [hsmall, hinterior] with j hj hju k hk
  have hkint :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hju hk
  have hconst : IntegrableOn
      (fun _ : Space n =>
        Real.exp (k * (phase (u j) φ x₀ - ε)))
      (Metric.ball x₀ r)
      (volume : Measure (Space n)) :=
    integrableOn_const hballfinite
  calc
    (volume : Measure (Space n)).real
        (Metric.ball x₀ r) *
      Real.exp (k * (phase (u j) φ x₀ - ε)) =
        ∫ _x : Space n in Metric.ball x₀ r,
          Real.exp (k * (phase (u j) φ x₀ - ε))
          ∂(volume : Measure (Space n)) := by
      rw [setIntegral_const]
      simp only [smul_eq_mul]
    _ ≤ ∫ x : Space n in Metric.ball x₀ r,
          monomialWeight k (u j) φ x
          ∂(volume : Measure (Space n)) := by
      apply setIntegral_mono_on hconst hkint.integrableOn
        Metric.isOpen_ball.measurableSet
      intro x hx
      have hxnorm : ‖x - x₀‖ < r := by
        simpa only [mem_ball, dist_eq_norm] using hx
      have hpair :
          |pairing (u j - u₀) (x - x₀)| < ε / 2 := by
        calc
          |pairing (u j - u₀) (x - x₀)| ≤
              ((n : ℝ) * ‖u j - u₀‖) * ‖x - x₀‖ :=
            MonomialDivergence.abs_pairing_le_dimension_mul_norm
              (u j - u₀) (x - x₀)
          _ ≤ ((n : ℝ) * ‖u j - u₀‖) * r := by
            apply mul_le_mul_of_nonneg_left hxnorm.le
            positivity
          _ < ε / 2 := hj
      have hsplit :
          phase (u j) φ x - phase (u j) φ x₀ =
            (phase u₀ φ x - phase u₀ φ x₀) +
              pairing (u j - u₀) (x - x₀) := by
        simp only [phase, pairing, Pi.sub_apply, sub_mul, mul_sub,
          Finset.sum_sub_distrib]
        ring
      have hlocal := hball hx
      have hphase : phase (u j) φ x₀ - ε ≤ phase (u j) φ x := by
        have habs := (abs_lt.mp hpair).1
        change phase u₀ φ x₀ - ε / 2 < phase u₀ φ x at hlocal
        linarith
      unfold monomialWeight
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left hphase hk.le
    _ ≤ monomialIntegral k (u j) φ := by
      unfold monomialIntegral
      apply setIntegral_le_integral hkint
      exact Filter.Eventually.of_forall fun x => (Real.exp_pos _).le

end BergmanJetMovingMonomialProbability

namespace BergmanJetMovingMonomialTailConvergence

open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity BergmanJetPointwiseLogKernel
open BergmanJetMovingPhaseConcentration BergmanJetMovingMonomialConcentration
open BergmanJetMovingMonomialProbability
open scoped BigOperators ENNReal NNReal Topology

private theorem exists_eventual_momentNormalized_moving_off_ball_exponential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (hdu₀ : DifferentiableAt ℝ (legendreTransform F.potential) u₀)
    (x₀ : Space n)
    (hmax : ∀ x : Space n,
      phase u₀ (momentNormalizedPotential F) x ≤
        phase u₀ (momentNormalizedPotential F) x₀)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    {r : ℝ} (hr : 0 < r) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ᶠ k : ℕ in atTop,
        (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
          monomialWeight (k : ℝ) (u k)
            (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n))) /
            monomialIntegral (k : ℝ) (u k)
              (momentNormalizedPotential F) ≤
          A * Real.exp (-((k : ℝ) * (η / 2))) := by
  let φ : Space n → ℝ := momentNormalizedPotential F
  obtain ⟨η, hη, hgap⟩ :=
    exists_eventual_momentNormalized_moving_phase_gap_outside_ball
      F htransport hu₀ hdu₀ x₀ hmax u hu hr
  obtain ⟨ρ, hρ, hvol, hden⟩ :=
    exists_eventual_momentNormalized_moving_ball_volume_exp_le_monomialIntegral
      F htransport hu₀ u hu x₀ (half_pos hη)
  obtain ⟨B, hB, hbase⟩ :=
    exists_eventual_momentNormalized_moving_base_integral_bound
      K F htransport hu₀ u hu
  let V : ℝ :=
    (volume : Measure (Space n)).real
      (Metric.ball x₀ ρ)
  let P₀ : ℝ := phase u₀ φ x₀
  let A : ℝ := (B / V) * Real.exp (η + 1 - P₀)
  have hV : 0 < V := hvol
  have hA : 0 < A :=
    mul_pos (div_pos hB hV) (Real.exp_pos _)
  have hptendsto :
      Tendsto (fun k : ℕ => phase (u k) φ x₀)
        atTop (𝓝 P₀) := by
    simpa [phase, P₀] using
      (((continuous_pairing_left x₀).continuousAt.tendsto.comp hu).sub_const
        (φ x₀))
  have hplower :
      ∀ᶠ k : ℕ in atTop,
        P₀ - 1 < phase (u k) φ x₀ :=
    hptendsto (Ioi_mem_nhds (by linarith))
  have hinterior :
      ∀ᶠ k : ℕ in atTop, u k ∈ interior K.carrier :=
    hu.eventually (isOpen_interior.mem_nhds hu₀)
  refine ⟨A, η, hA, hη, ?_⟩
  filter_upwards [hgap, hden, hbase, hplower, hinterior,
    eventually_ge_atTop (1 : ℕ)]
    with k hkgap hkden hkbase hkp hkint hkone
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hkone
  have hkpos : 0 < (k : ℝ) := lt_of_lt_of_le zero_lt_one hkreal
  have hnum :=
    momentNormalized_off_phase_setIntegral_le_exp_mul_base
      F htransport hkint Metric.isOpen_ball.measurableSet.compl
      hkgap hkreal
  have hupper :
      (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
        monomialWeight (k : ℝ) (u k) φ x
        ∂(volume : Measure (Space n))) ≤
          Real.exp
            (((k : ℝ) - 1) * (phase (u k) φ x₀ - η)) * B := by
    calc
      (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
        monomialWeight (k : ℝ) (u k) φ x
        ∂(volume : Measure (Space n))) ≤
          Real.exp
            (((k : ℝ) - 1) * (phase (u k) φ x₀ - η)) *
              monomialIntegral 1 (u k) φ := hnum
      _ ≤ Real.exp
            (((k : ℝ) - 1) * (phase (u k) φ x₀ - η)) * B :=
        mul_le_mul_of_nonneg_left hkbase (Real.exp_pos _).le
  have hden' :
      V * Real.exp
          ((k : ℝ) * (phase (u k) φ x₀ - η / 2)) ≤
        monomialIntegral (k : ℝ) (u k) φ :=
    hkden hkpos
  have hquot :=
    div_le_div₀
      (mul_nonneg (Real.exp_pos _).le hB.le)
      hupper
      (mul_pos hV (Real.exp_pos _))
      hden'
  calc
    (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
      monomialWeight (k : ℝ) (u k) φ x
      ∂(volume : Measure (Space n))) /
        monomialIntegral (k : ℝ) (u k) φ ≤
      (Real.exp
        (((k : ℝ) - 1) * (phase (u k) φ x₀ - η)) * B) /
        (V * Real.exp
          ((k : ℝ) * (phase (u k) φ x₀ - η / 2))) := hquot
    _ = (B / V) *
        (Real.exp
          (((k : ℝ) - 1) * (phase (u k) φ x₀ - η)) /
          Real.exp
            ((k : ℝ) * (phase (u k) φ x₀ - η / 2))) := by
      field_simp
    _ = (B / V) *
        Real.exp
          ((((k : ℝ) - 1) * (phase (u k) φ x₀ - η)) -
            (k : ℝ) * (phase (u k) φ x₀ - η / 2)) := by
      rw [Real.exp_sub]
    _ = (B / V) *
        Real.exp
          ((η - phase (u k) φ x₀) +
            (-((k : ℝ) * (η / 2)))) := by
      congr 2
      ring
    _ = ((B / V) * Real.exp (η - phase (u k) φ x₀)) *
          Real.exp (-((k : ℝ) * (η / 2))) := by
      rw [Real.exp_add]
      ring
    _ ≤ ((B / V) * Real.exp (η + 1 - P₀)) *
          Real.exp (-((k : ℝ) * (η / 2))) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ (div_pos hB hV).le
      apply Real.exp_le_exp.mpr
      linarith
    _ = A * Real.exp (-((k : ℝ) * (η / 2))) := rfl

private theorem tendsto_momentNormalized_moving_off_ball_probability
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (hdu₀ : DifferentiableAt ℝ (legendreTransform F.potential) u₀)
    (x₀ : Space n)
    (hmax : ∀ x : Space n,
      phase u₀ (momentNormalizedPotential F) x ≤
        phase u₀ (momentNormalizedPotential F) x₀)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    {r : ℝ} (hr : 0 < r) :
    Tendsto
      (fun k : ℕ =>
        (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
          monomialWeight (k : ℝ) (u k)
            (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n))) /
          monomialIntegral (k : ℝ) (u k)
            (momentNormalizedPotential F))
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨A, η, hA, hη, hbound⟩ :=
    exists_eventual_momentNormalized_moving_off_ball_exponential
      F htransport hu₀ hdu₀ x₀ hmax u hu hr
  have htop :
      Tendsto (fun k : ℕ => (k : ℝ) * (η / 2)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const
      (half_pos hη)
  have hbot :
      Tendsto (fun k : ℕ => -((k : ℝ) * (η / 2)))
        atTop atBot := by
    simpa only [tendsto_neg_atBot_iff, comp_def] using
      tendsto_neg_atTop_atBot.comp htop
  have hdecay :
      Tendsto
        (fun k : ℕ => Real.exp (-((k : ℝ) * (η / 2))))
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.tendsto_exp_comp_nhds_zero, tendsto_neg_atBot_iff,
      comp_def] using Real.tendsto_exp_atBot.comp hbot
  have hmajor :
      Tendsto
        (fun k : ℕ => A * Real.exp (-((k : ℝ) * (η / 2))))
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hdecay.const_mul A
  apply squeeze_zero' _ hbound hmajor
  exact Filter.Eventually.of_forall fun k =>
    div_nonneg
      (setIntegral_nonneg Metric.isOpen_ball.measurableSet.compl
        fun x _ => (Real.exp_pos _).le)
      (by
        unfold monomialIntegral
        exact integral_nonneg fun x => (Real.exp_pos _).le)

end BergmanJetMovingMonomialTailConvergence

namespace BergmanJetMovingMonomialObservableConvergence

open Set Function Filter MeasureTheory Metric
open LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman BergmanJetMovingMonomialTailConvergence
open scoped BigOperators ENNReal NNReal Topology

private theorem tendsto_integral_bounded_continuous_of_concentrating_normalized_density
    {n : ℕ}
    (w : ℕ → Space n → ℝ)
    (hw : ∀ᶠ k : ℕ in atTop,
      Integrable (w k) (volume : Measure (Space n)))
    (hwnonneg : ∀ k : ℕ, ∀ x : Space n, 0 ≤ w k x)
    (hwmass : ∀ᶠ k : ℕ in atTop,
      (∫ x : Space n, w k x
        ∂(volume : Measure (Space n))) = 1)
    (x₀ : Space n)
    (hwtail : ∀ {r : ℝ}, 0 < r →
      Tendsto
        (fun k : ℕ =>
          ∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n)))
        atTop (𝓝 (0 : ℝ)))
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    Tendsto
      (fun k : ℕ =>
        ∫ x : Space n, f x * w k x
          ∂(volume : Measure (Space n)))
      atTop (𝓝 (f x₀)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨r, hr, hclose⟩ :=
    (Metric.continuousAt_iff.mp hf.continuousAt)
      (ε / 2) (half_pos hε)
  have htail :
      ∀ᶠ k : ℕ in atTop,
        (2 * C) *
          (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n))) < ε / 2 := by
    have ht :
        Tendsto
          (fun k : ℕ =>
            (2 * C) *
              (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
                w k x ∂(volume : Measure (Space n))))
          atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using (hwtail hr).const_mul (2 * C)
    have hopen : Set.Iio (ε / 2) ∈ 𝓝 (0 : ℝ) :=
      Iio_mem_nhds (half_pos hε)
    simpa only [eventually_atTop, mem_map, mem_atTop_sets, mem_preimage, mem_Iio] using ht hopen
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [hw, hwmass, htail] with k hk hkmass hktail
  have hfint :
      Integrable (fun x : Space n => f x * w k x)
        (volume : Measure (Space n)) :=
    hk.bdd_mul hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hC x)
  have hcint :
      Integrable (fun x : Space n => f x₀ * w k x)
        (volume : Measure (Space n)) :=
    hk.const_mul (f x₀)
  have hdiffint :
      Integrable
        (fun x : Space n => (f x - f x₀) * w k x)
        (volume : Measure (Space n)) := by
    refine (hfint.sub hcint).congr ?_
    filter_upwards [] with x
    change
      f x * w k x - f x₀ * w k x =
        (f x - f x₀) * w k x
    ring
  have hdiff :
      (∫ x : Space n, f x * w k x
        ∂(volume : Measure (Space n))) - f x₀ =
        ∫ x : Space n,
          (f x - f x₀) * w k x
          ∂(volume : Measure (Space n)) := by
    calc
      (∫ x : Space n, f x * w k x
        ∂(volume : Measure (Space n))) - f x₀ =
          (∫ x : Space n, f x * w k x
            ∂(volume : Measure (Space n))) -
            f x₀ *
              (∫ x : Space n, w k x
                ∂(volume : Measure (Space n))) := by
          rw [hkmass]
          ring
      _ = (∫ x : Space n, f x * w k x
            ∂(volume : Measure (Space n))) -
            (∫ x : Space n, f x₀ * w k x
              ∂(volume : Measure (Space n))) := by
          rw [MeasureTheory.integral_const_mul]
      _ = ∫ x : Space n,
            (f x - f x₀) * w k x
            ∂(volume : Measure (Space n)) := by
          rw [← MeasureTheory.integral_sub hfint hcint]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          ring
  have hnormint := hdiffint.norm
  have hball :
      (∫ x : Space n in Metric.ball x₀ r,
        ‖(f x - f x₀) * w k x‖
        ∂(volume : Measure (Space n))) ≤
        (ε / 2) *
          (∫ x : Space n in Metric.ball x₀ r,
            w k x ∂(volume : Measure (Space n))) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_mono_on
      hnormint.integrableOn
      ((hk.const_mul (ε / 2)).integrableOn)
      Metric.isOpen_ball.measurableSet
    intro x hx
    have hnear : |f x - f x₀| < ε / 2 := by
      have hd := hclose (Metric.mem_ball.mp hx)
      simpa only [gt_iff_lt, Real.dist_eq] using hd
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hwnonneg k x)]
    exact mul_le_mul_of_nonneg_right hnear.le (hwnonneg k x)
  have hfar :
      (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
        ‖(f x - f x₀) * w k x‖
        ∂(volume : Measure (Space n))) ≤
        (2 * C) *
          (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n))) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_mono_on
      hnormint.integrableOn
      ((hk.const_mul (2 * C)).integrableOn)
      Metric.isOpen_ball.measurableSet.compl
    intro x _
    have habs : |f x - f x₀| ≤ 2 * C := by
      calc
        |f x - f x₀| ≤ |f x| + |f x₀| := abs_sub _ _
        _ ≤ C + C := add_le_add (hC x) (hC x₀)
        _ = 2 * C := by ring
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hwnonneg k x)]
    exact mul_le_mul_of_nonneg_right habs (hwnonneg k x)
  have hballmass :
      (∫ x : Space n in Metric.ball x₀ r,
        w k x ∂(volume : Measure (Space n))) ≤ 1 := by
    rw [← hkmass]
    exact setIntegral_le_integral hk
      (Filter.Eventually.of_forall fun x => hwnonneg k x)
  rw [Real.dist_eq, hdiff]
  calc
    |∫ x : Space n,
        (f x - f x₀) * w k x
        ∂(volume : Measure (Space n))| ≤
        ∫ x : Space n,
          ‖(f x - f x₀) * w k x‖
          ∂(volume : Measure (Space n)) := by
      simpa only [norm_mul, Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (fun x : Space n => (f x - f x₀) * w k x))
    _ =
        (∫ x : Space n in Metric.ball x₀ r,
          ‖(f x - f x₀) * w k x‖
          ∂(volume : Measure (Space n))) +
        (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
          ‖(f x - f x₀) * w k x‖
          ∂(volume : Measure (Space n))) :=
      (integral_add_compl Metric.isOpen_ball.measurableSet hnormint).symm
    _ ≤ (ε / 2) *
          (∫ x : Space n in Metric.ball x₀ r,
            w k x ∂(volume : Measure (Space n))) +
        (2 * C) *
          (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n))) :=
      add_le_add hball hfar
    _ ≤ ε / 2 +
        (2 * C) *
          (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n))) := by
      have hb :=
        mul_le_mul_of_nonneg_left hballmass (half_pos hε).le
      nlinarith
    _ < ε := by linarith

private theorem tendsto_momentNormalized_moving_monomial_bounded_observable
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (hdu₀ : DifferentiableAt ℝ (legendreTransform F.potential) u₀)
    (x₀ : Space n)
    (hmax : ∀ x : Space n,
      phase u₀ (momentNormalizedPotential F) x ≤
        phase u₀ (momentNormalizedPotential F) x₀)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    Tendsto
      (fun k : ℕ =>
        (∫ x : Space n,
          f x * monomialWeight (k : ℝ) (u k)
            (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n))) /
          monomialIntegral (k : ℝ) (u k)
            (momentNormalizedPotential F))
      atTop (𝓝 (f x₀)) := by
  let φ : Space n → ℝ := momentNormalizedPotential F
  let w : ℕ → Space n → ℝ := fun k x =>
    monomialWeight (k : ℝ) (u k) φ x /
      monomialIntegral (k : ℝ) (u k) φ
  have hinterior :
      ∀ᶠ k : ℕ in atTop, u k ∈ interior K.carrier :=
    hu.eventually (isOpen_interior.mem_nhds hu₀)
  have hwint :
      ∀ᶠ k : ℕ in atTop,
        Integrable (w k) (volume : Measure (Space n)) := by
    filter_upwards [hinterior, eventually_ge_atTop (1 : ℕ)]
      with k hkint hkone
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hkone)
    exact
      (integrable_monomialWeight_momentNormalized_of_mem_interior
        F htransport hkint hkpos).div_const _
  have hwnonneg : ∀ k : ℕ, ∀ x : Space n, 0 ≤ w k x := by
    intro k x
    dsimp [w]
    apply div_nonneg (Real.exp_pos _).le
    unfold monomialIntegral
    exact integral_nonneg fun y => (Real.exp_pos _).le
  have hwmass :
      ∀ᶠ k : ℕ in atTop,
        (∫ x : Space n, w k x
          ∂(volume : Measure (Space n))) = 1 := by
    filter_upwards [hinterior, eventually_ge_atTop (1 : ℕ)]
      with k hkint hkone
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hkone)
    dsimp [w]
    rw [MeasureTheory.integral_div]
    exact div_self
      (monomialIntegral_momentNormalized_pos
        F htransport hkint hkpos).ne'
  have hwtail : ∀ {r : ℝ}, 0 < r →
      Tendsto
        (fun k : ℕ =>
          ∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n)))
        atTop (𝓝 (0 : ℝ)) := by
    intro r hr
    have ht := tendsto_momentNormalized_moving_off_ball_probability
      F htransport hu₀ hdu₀ x₀ hmax u hu hr
    simpa [w, φ, MeasureTheory.integral_div] using ht
  have ht :=
    tendsto_integral_bounded_continuous_of_concentrating_normalized_density
      w hwint hwnonneg hwmass x₀ hwtail f hf C hC
  simpa [w, φ, ← mul_div_assoc, MeasureTheory.integral_div] using ht

end BergmanJetMovingMonomialObservableConvergence

namespace BergmanJetTriangularLatticeConvergence

open Set Filter MeasureTheory Metric
open LatticeAsymptotics
open scoped BigOperators ENNReal NNReal Topology

private def triangularUnitLatticeStep {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (s : Set (Space n))
    (G : ℕ → Space n → ℝ)
    (k : ℕ) (x : Space n) : ℝ :=
  ∑ J ∈ (BoxIntegral.unitPartition.prepartition (k + 1) B).boxes,
    (J : Set (Space n)).indicator
      (fun _ : Space n =>
        s.indicator (G (k + 1))
          ((BoxIntegral.unitPartition.prepartition (k + 1) B).tag J)) x

private theorem triangularUnitLatticeStep_integrable {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (s : Set (Space n))
    (G : ℕ → Space n → ℝ)
    (k : ℕ) :
    Integrable (triangularUnitLatticeStep B s G k)
      (volume : Measure (Space n)) := by
  classical
  unfold triangularUnitLatticeStep
  apply integrable_finsetSum
  intro J hJ
  exact (integrableOn_const
    (μ := (volume : Measure (Space n)))
    (C := s.indicator (G (k + 1))
      ((BoxIntegral.unitPartition.prepartition (k + 1) B).tag J))
    (BoxIntegral.Box.measure_coe_lt_top J
      (volume : Measure (Space n))).ne).integrable_indicator
    J.measurableSet_coe

private theorem integral_triangularUnitLatticeStep_eq_integralSum {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (s : Set (Space n))
    (G : ℕ → Space n → ℝ)
    (k : ℕ) :
    (∫ x : Space n, triangularUnitLatticeStep B s G k x
      ∂(volume : Measure (Space n))) =
      BoxIntegral.integralSum (s.indicator (G (k + 1)))
        (BoxIntegral.BoxAdditiveMap.toSMul
          (Measure.toBoxAdditive (volume : Measure (Space n))))
        (BoxIntegral.unitPartition.prepartition (k + 1) B) := by
  classical
  unfold triangularUnitLatticeStep
  rw [MeasureTheory.integral_finsetSum]
  · unfold BoxIntegral.integralSum
    apply Finset.sum_congr rfl
    intro J hJ
    rw [MeasureTheory.integral_indicator_const _ J.measurableSet_coe]
    rfl
  · intro J hJ
    exact (integrableOn_const
      (μ := (volume : Measure (Space n)))
      (C := s.indicator (G (k + 1))
        ((BoxIntegral.unitPartition.prepartition (k + 1) B).tag J))
      (BoxIntegral.Box.measure_coe_lt_top J
        (volume : Measure (Space n))).ne).integrable_indicator
      J.measurableSet_coe

private theorem integral_triangularUnitLatticeStep_eq_lattice_sum {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (hB : BoxIntegral.hasIntegralVertices B)
    (s : Set (Space n))
    (hs : s ⊆ (B : Set (Space n)))
    (G : ℕ → Space n → ℝ)
    (k : ℕ) :
    (∫ x : Space n, triangularUnitLatticeStep B s G k x
      ∂(volume : Measure (Space n))) =
      (∑' x : ↑(s ∩ scaledIntegerLattice n (k + 1)), G (k + 1) x) /
        ((k + 1 : ℕ) : ℝ) ^ n := by
  rw [integral_triangularUnitLatticeStep_eq_integralSum]
  simpa only [scaledIntegerLattice, Nat.cast_add, Nat.cast_one, Fintype.card_fin] using
    (BoxIntegral.unitPartition.integralSum_eq_tsum_div
      (n := k + 1) s (G (k + 1)) hB hs)

private theorem tendsto_unitPartition_tag_index {n : ℕ}
    (x : Space n) :
    Tendsto (fun k : ℕ =>
      BoxIntegral.unitPartition.tag (k + 1)
        (BoxIntegral.unitPartition.index (k + 1) x))
      atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun k => norm_nonneg _) ?_
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  let ν : Fin n → ℤ := BoxIntegral.unitPartition.index (k + 1) x
  have hxm : x ∈ BoxIntegral.unitPartition.box (k + 1) ν := by
    apply BoxIntegral.unitPartition.mem_box_iff_index.mpr
    rfl
  have htm : BoxIntegral.unitPartition.tag (k + 1) ν ∈
      BoxIntegral.unitPartition.box (k + 1) ν :=
    BoxIntegral.unitPartition.tag_mem (k + 1) ν
  have hd :
      dist (BoxIntegral.unitPartition.tag (k + 1) ν) x ≤
        1 / ((k + 1 : ℕ) : ℝ) :=
    (Metric.dist_le_diam_of_mem
      (BoxIntegral.Box.isBounded_Icc
        (BoxIntegral.unitPartition.box (k + 1) ν))
      (BoxIntegral.Box.coe_subset_Icc htm)
      (BoxIntegral.Box.coe_subset_Icc hxm)).trans
        (BoxIntegral.unitPartition.diam_boxIcc (k + 1) ν)
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hcast : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_add_right k 1)
  calc
    ‖BoxIntegral.unitPartition.tag (k + 1)
        (BoxIntegral.unitPartition.index (k + 1) x) - x‖ =
        dist (BoxIntegral.unitPartition.tag (k + 1) ν) x := by
          rw [dist_eq_norm]
    _ ≤ 1 / ((k + 1 : ℕ) : ℝ) := hd
    _ ≤ 1 / (k : ℝ) := one_div_le_one_div_of_le hkr hcast

private theorem triangularUnitLatticeStep_eq_tag_of_mem {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (hB : BoxIntegral.hasIntegralVertices B)
    (s : Set (Space n))
    (G : ℕ → Space n → ℝ)
    (k : ℕ) (x : Space n)
    (hx : x ∈ (B : Set (Space n))) :
    triangularUnitLatticeStep B s G k x =
      s.indicator (G (k + 1))
        (BoxIntegral.unitPartition.tag (k + 1)
          (BoxIntegral.unitPartition.index (k + 1) x)) := by
  classical
  let ν : Fin n → ℤ := BoxIntegral.unitPartition.index (k + 1) x
  let J : BoxIntegral.Box (Fin n) :=
    BoxIntegral.unitPartition.box (k + 1) ν
  have hν : ν ∈ BoxIntegral.unitPartition.admissibleIndex (k + 1) B :=
    BoxIntegral.unitPartition.mem_admissibleIndex_of_mem_box
      (k + 1) hB hx
  have hJ : J ∈
      (BoxIntegral.unitPartition.prepartition (k + 1) B).boxes :=
    BoxIntegral.unitPartition.mem_prepartition_boxes_iff.mpr
      ⟨ν, hν, rfl⟩
  have hxJ : x ∈ (J : Set (Space n)) := by
    exact BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl
  unfold triangularUnitLatticeStep
  rw [Finset.sum_eq_single J]
  · rw [Set.indicator_of_mem hxJ]
    rw [BoxIntegral.unitPartition.prepartition_tag (k + 1) hν]
  · intro I hI hne
    apply Set.indicator_of_notMem
    intro hxI
    apply hne
    exact (BoxIntegral.unitPartition.prepartition (k + 1) B)
      |>.toPrepartition.eq_of_mem_of_mem hI hJ hxI hxJ
  · intro hnot
    exact (hnot hJ).elim

private theorem triangularUnitLatticeStep_eq_zero_of_not_mem {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (s : Set (Space n))
    (G : ℕ → Space n → ℝ)
    (k : ℕ) (x : Space n)
    (hx : x ∉ (B : Set (Space n))) :
    triangularUnitLatticeStep B s G k x = 0 := by
  classical
  unfold triangularUnitLatticeStep
  apply Finset.sum_eq_zero
  intro J hJ
  apply Set.indicator_of_notMem
  intro hxJ
  apply hx
  exact ((BoxIntegral.unitPartition.prepartition (k + 1) B)
    |>.toPrepartition.le_of_mem hJ) hxJ

private theorem tendsto_moving_lattice_sum_of_ae_tag_convergence {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (hB : BoxIntegral.hasIntegralVertices B)
    (s : Set (Space n))
    (hs : s ⊆ (B : Set (Space n)))
    (hsm : MeasurableSet s)
    (G : ℕ → Space n → ℝ)
    (g : Space n → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ k : ℕ, 0 < k → ∀ u ∈ s,
      u ∈ scaledIntegerLattice n k → ‖G k u‖ ≤ C)
    (hpoint : ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
      Tendsto (fun k : ℕ =>
        s.indicator (G (k + 1))
          (BoxIntegral.unitPartition.tag (k + 1)
            (BoxIntegral.unitPartition.index (k + 1) x)))
        atTop (𝓝 (s.indicator g x))) :
    Tendsto
      (fun k : ℕ =>
        (∑' u : ↑(s ∩ scaledIntegerLattice n (k + 1)),
          G (k + 1) u) / ((k + 1 : ℕ) : ℝ) ^ n)
      atTop (𝓝 (∫ x in s, g x
        ∂(volume : Measure (Space n)))) := by
  classical
  have hmajor : Integrable
      ((B : Set (Space n)).indicator
        (fun _ : Space n => C))
      (volume : Measure (Space n)) :=
    (integrableOn_const
      (μ := (volume : Measure (Space n)))
      (C := C)
      (BoxIntegral.Box.measure_coe_lt_top B
        (volume : Measure (Space n))).ne).integrable_indicator
      B.measurableSet_coe
  have hsteps : ∀ k : ℕ, AEStronglyMeasurable
      (triangularUnitLatticeStep B s G k)
      (volume : Measure (Space n)) :=
    fun k => (triangularUnitLatticeStep_integrable B s G k).1
  have hdom : ∀ k : ℕ, ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
      ‖triangularUnitLatticeStep B s G k x‖ ≤
        (B : Set (Space n)).indicator
          (fun _ : Space n => C) x := by
    intro k
    filter_upwards [] with x
    by_cases hx : x ∈ (B : Set (Space n))
    · rw [triangularUnitLatticeStep_eq_tag_of_mem B hB s G k x hx]
      rw [Set.indicator_of_mem hx]
      let u : Space n :=
        BoxIntegral.unitPartition.tag (k + 1)
          (BoxIntegral.unitPartition.index (k + 1) x)
      have hulattice : u ∈ scaledIntegerLattice n (k + 1) := by
        change
          BoxIntegral.unitPartition.tag (k + 1)
            (BoxIntegral.unitPartition.index (k + 1) x) ∈
            scaledIntegerLattice n (k + 1)
        rw [scaledIntegerLattice, ← Submodule.coe_pointwise_smul]
        exact BoxIntegral.unitPartition.tag_mem_smul_span
          (k + 1) (BoxIntegral.unitPartition.index (k + 1) x)
      by_cases hu : u ∈ s
      · simpa [u, Set.indicator_of_mem hu] using
          hbound (k + 1) (Nat.zero_lt_succ k) u hu hulattice
      · rw [Set.indicator_of_notMem hu]
        simpa only [norm_zero, ge_iff_le] using hC
    · rw [triangularUnitLatticeStep_eq_zero_of_not_mem B s G k x hx]
      rw [Set.indicator_of_notMem hx]
      simp only [norm_zero, Std.le_refl]
  have hlim : ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
      Tendsto (fun k : ℕ => triangularUnitLatticeStep B s G k x)
        atTop (𝓝 (s.indicator g x)) := by
    filter_upwards [hpoint] with x hxpoint
    by_cases hx : x ∈ (B : Set (Space n))
    · exact hxpoint.congr' (Filter.Eventually.of_forall fun k =>
        (triangularUnitLatticeStep_eq_tag_of_mem B hB s G k x hx).symm)
    · have hxs : x ∉ s := fun h => hx (hs h)
      have hzero : s.indicator g x = 0 := Set.indicator_of_notMem hxs g
      rw [hzero]
      exact (tendsto_congr'
        (Filter.Eventually.of_forall fun k =>
          triangularUnitLatticeStep_eq_zero_of_not_mem B s G k x hx)).2
        tendsto_const_nhds
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    ((B : Set (Space n)).indicator
      (fun _ : Space n => C))
    hsteps hmajor hdom hlim
  simpa only [Nat.cast_add, Nat.cast_one,
    integral_triangularUnitLatticeStep_eq_lattice_sum B hB s hs G,
    MeasureTheory.integral_indicator hsm] using hdct

end BergmanJetTriangularLatticeConvergence

namespace BergmanJetDualGradientInverseTransport

open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentWeakFirstVariation MomentFirstVariation
open MomentTargetGeodesic MomentRegularity BergmanJetDualGradientConcentration
open BergmanJetDualPhaseConcentration
open scoped ENNReal NNReal Topology

private theorem measurable_finiteEnergySourceLegendreGradient
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Measurable
      (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_fderiv_apply_const ℝ
    (legendreTransform F.potential)
    (Pi.single i (1 : ℝ))

private theorem ae_finiteEnergySourceLegendreGradient_left_inverse_gibbs
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᵐ x : Space n
      ∂(finiteEnergySourceGibbsProbability F),
      SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential)
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) = x := by
  have hsource :
      ∀ᵐ x : Space n
        ∂(finiteEnergySourceGibbsProbability F),
        DifferentiableAt ℝ
          (F.potential : Space n → ℝ) x :=
    finiteEnergySourceGibbs_ae_of_volume F _
      (ae_differentiableAt_finiteEnergySource F)
  have htarget :
      ∀ᵐ u : Space n
        ∂(finiteEnergySourceGradientPushforward F),
        DifferentiableAt ℝ (legendreTransform F.potential) u := by
    rw [htransport]
    exact ae_differentiableAt_finiteEnergySourceLegendre_target
      F htransport
  unfold finiteEnergySourceGradientPushforward at htarget
  have hdual :
      ∀ᵐ x : Space n
        ∂(finiteEnergySourceGibbsProbability F),
        DifferentiableAt ℝ
          (legendreTransform F.potential)
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) :=
    MeasureTheory.ae_of_ae_map
      (measurable_finiteEnergySourceGradient F).aemeasurable
      htarget
  filter_upwards [hsource,
    ae_finiteEnergySourceGradient_mem_interior_gibbs F htransport,
    hdual] with x hx hinterior hdx
  exact finiteEnergySourceLegendre_gradient_eq_phaseMaximizer
    F htransport hinterior hdx x
      (fun z => finiteEnergySourcePhase_actualGradient_le F x hx z)

private theorem finiteEnergySourceLegendreGradient_pushforward_target
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Measure.map
        (SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential))
        (normalizedTargetBodyMeasure K) =
      finiteEnergySourceGibbsProbability F := by
  let G : Space n → Space n :=
    SpatialBergmanFatouScheffe.actualGradient F.potential
  let D : Space n → Space n :=
    SpatialBergmanFatouScheffe.actualGradient
      (legendreTransform F.potential)
  have hG : Measurable G :=
    measurable_finiteEnergySourceGradient F
  have hD : Measurable D :=
    measurable_finiteEnergySourceLegendreGradient F
  have hleft :
      (D ∘ G) =ᵐ[finiteEnergySourceGibbsProbability F]
        (fun x : Space n => x) := by
    filter_upwards
      [ae_finiteEnergySourceLegendreGradient_left_inverse_gibbs
        F htransport] with x hx
    change
      SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential)
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) = x
    exact hx
  change Measure.map D (normalizedTargetBodyMeasure K) =
    finiteEnergySourceGibbsProbability F
  calc
    Measure.map D (normalizedTargetBodyMeasure K) =
        Measure.map D (finiteEnergySourceGradientPushforward F) := by
      rw [htransport]
    _ = Measure.map (D ∘ G)
          (finiteEnergySourceGibbsProbability F) := by
      unfold finiteEnergySourceGradientPushforward
      exact Measure.map_map hD hG
    _ = Measure.map (fun x : Space n => x)
          (finiteEnergySourceGibbsProbability F) :=
      Measure.map_congr hleft
    _ = finiteEnergySourceGibbsProbability F := Measure.map_id'

private theorem integral_finiteEnergySourceLegendreGradient_target
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f) :
    (∫ u : Space n,
      f (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u)
      ∂(normalizedTargetBodyMeasure K)) =
      ∫ x : Space n, f x
        ∂(finiteEnergySourceGibbsProbability F) := by
  calc
    (∫ u : Space n,
      f (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u)
      ∂(normalizedTargetBodyMeasure K)) =
        ∫ x : Space n, f x
          ∂(Measure.map
            (SpatialBergmanFatouScheffe.actualGradient
              (legendreTransform F.potential))
            (normalizedTargetBodyMeasure K)) := by
      symm
      exact MeasureTheory.integral_map
        (measurable_finiteEnergySourceLegendreGradient F).aemeasurable
        hf.aestronglyMeasurable
    _ = ∫ x : Space n, f x
          ∂(finiteEnergySourceGibbsProbability F) := by
      rw [finiteEnergySourceLegendreGradient_pushforward_target
        F htransport]

end BergmanJetDualGradientInverseTransport

namespace BergmanJetRoundedMonomialObservableConvergence

open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open BergmanJetPhaseLaplace BergmanJetDualPhaseConcentration
open scoped ENNReal NNReal Topology

private theorem momentNormalizedPhase_dualGradient_maximizer
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hdu : DifferentiableAt ℝ (legendreTransform F.potential) u) :
    ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤
        phase u (momentNormalizedPotential F)
          (SpatialBergmanFatouScheffe.actualGradient
            (legendreTransform F.potential) u) := by
  obtain ⟨x₀, hx₀⟩ :=
    exists_momentNormalizedPhaseMaximizer F htransport hu
  have hgradient :
      SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u = x₀ :=
    finiteEnergySourceLegendre_gradient_eq_phaseMaximizer
      F htransport hu hdu x₀
        ((momentNormalized_phaseMaximizer_iff F u x₀).mp hx₀)
  simpa only [hgradient] using hx₀

end BergmanJetRoundedMonomialObservableConvergence

namespace BergmanJetDiagonalObservableLatticeIdentity

open Set Function Filter MeasureTheory
open BergmanMonomials BergmanNormalization LatticeAsymptotics MonomialIntegrability MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergmanProbabilityEndpoint
open scoped BigOperators ENNReal NNReal Topology

private def momentNormalizedLaurentObservable
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (k : ℕ)
    (f : Space n → ℝ)
    (u : Space n) : ℝ :=
  (∫ x : Space n,
    f x * monomialWeight (k : ℝ) u
      (momentNormalizedPotential F) x
    ∂(volume : Measure (Space n))) /
    monomialIntegral (k : ℝ) u
      (momentNormalizedPotential F)

private theorem momentNormalizedLaurentObservable_eq_integral_normalizedMonomialDensity
    {n k : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (f : Space n → ℝ)
    (u : monomialIndex K k) :
    momentNormalizedLaurentObservable
        F k f (u : Space n) =
      ∫ x : Space n,
        f x * normalizedMonomialDensity
          K k (momentNormalizedPotential F) u x
        ∂(volume : Measure (Space n)) := by
  unfold momentNormalizedLaurentObservable
    normalizedMonomialDensity monomialNormSquared
  simp_rw [← mul_div_assoc]
  rw [MeasureTheory.integral_div]

private theorem abs_momentNormalizedLaurentObservable_le
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C)
    (u : monomialIndex K k) :
    |momentNormalizedLaurentObservable
        F k f (u : Space n)| ≤ C := by
  rw [momentNormalizedLaurentObservable_eq_integral_normalizedMonomialDensity]
  let ρ : Space n → ℝ :=
    normalizedMonomialDensity
      K k (momentNormalizedPotential F) u
  have hρ : Integrable ρ
      (volume : Measure (Space n)) :=
    normalizedMonomialDensity_momentNormalized_integrable
      K hk F htransport u
  have hρpos : ∀ x : Space n, 0 ≤ ρ x := fun x =>
    (normalizedMonomialDensity_momentNormalized_pos
      K hk F htransport u x).le
  have hprod :
      Integrable (fun x : Space n => f x * ρ x)
        (volume : Measure (Space n)) :=
    hρ.bdd_mul hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hC x)
  change |∫ x : Space n, f x * ρ x
    ∂(volume : Measure (Space n))| ≤ C
  calc
    |∫ x : Space n, f x * ρ x
      ∂(volume : Measure (Space n))| ≤
        ∫ x : Space n, ‖f x * ρ x‖
          ∂(volume : Measure (Space n)) := by
      simpa only [norm_mul, Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (fun x : Space n => f x * ρ x))
    _ ≤ ∫ x : Space n, C * ρ x
          ∂(volume : Measure (Space n)) := by
      apply MeasureTheory.integral_mono_ae
        hprod.norm (hρ.const_mul C)
      filter_upwards [] with x
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hρpos x)]
      exact mul_le_mul_of_nonneg_right (hC x) (hρpos x)
    _ = C := by
      rw [MeasureTheory.integral_const_mul]
      change C *
        (∫ x : Space n,
          normalizedMonomialDensity
            K k (momentNormalizedPotential F) u x
          ∂(volume : Measure (Space n))) = C
      rw [integral_normalizedMonomialDensity_momentNormalized
        K hk F htransport u]
      ring

private theorem integral_momentNormalizedDiagonal_eq_laurentObservable_average
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    (∫ x : Space n,
      f x * normalizedDiagonalDensity
        K k (momentNormalizedPotential F) x
      ∂(volume : Measure (Space n))) =
      (∑' u : monomialIndex K k,
        momentNormalizedLaurentObservable
          F k f (u : Space n)) /
        (bergmanDimension K k : ℝ) := by
  classical
  let := (monomialIndex_finite K hk).fintype
  have hmono : ∀ u : monomialIndex K k,
      Integrable
        (fun x : Space n =>
          f x * normalizedMonomialDensity
            K k (momentNormalizedPotential F) u x)
        (volume : Measure (Space n)) := by
    intro u
    exact
      (normalizedMonomialDensity_momentNormalized_integrable
        K hk F htransport u).bdd_mul
        hf.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using hC x)
  calc
    (∫ x : Space n,
      f x * normalizedDiagonalDensity
        K k (momentNormalizedPotential F) x
      ∂(volume : Measure (Space n))) =
        (∫ x : Space n,
          f x * weightedDiagonalKernel
            K k (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n))) /
          (bergmanDimension K k : ℝ) := by
      unfold normalizedDiagonalDensity
      simp_rw [← mul_div_assoc]
      rw [MeasureTheory.integral_div]
    _ = (∑ u : monomialIndex K k,
          ∫ x : Space n,
            f x * normalizedMonomialDensity
              K k (momentNormalizedPotential F) u x
            ∂(volume : Measure (Space n))) /
          (bergmanDimension K k : ℝ) := by
      congr 1
      unfold weightedDiagonalKernel
      simp_rw [tsum_fintype]
      simp_rw [Finset.mul_sum]
      rw [MeasureTheory.integral_finsetSum]
      intro u _
      exact hmono u
    _ = (∑' u : monomialIndex K k,
          momentNormalizedLaurentObservable
            F k f (u : Space n)) /
          (bergmanDimension K k : ℝ) := by
      rw [tsum_fintype]
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      exact
        (momentNormalizedLaurentObservable_eq_integral_normalizedMonomialDensity
          K F f u).symm

end BergmanJetDiagonalObservableLatticeIdentity

namespace BergmanJetUpperTaggedMonomialObservableConvergence

open Set Function Filter MeasureTheory
open LaplaceAsymptotics LatticeAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetDualGradientConcentration BergmanJetMovingMonomialObservableConvergence
open BergmanJetRoundedMonomialObservableConvergence BergmanJetTriangularLatticeConvergence
open BergmanJetDiagonalObservableLatticeIdentity
open scoped BigOperators ENNReal NNReal Topology

private def upperTaggedLatticeExponent {n : ℕ}
    (k : ℕ) (u : Space n) : Space n :=
  fun i => (⌈(k : ℝ) * u i⌉ : ℝ) / (k : ℝ)

private theorem upperTaggedLatticeExponent_eq_unitPartition_tag
    {n k : ℕ}
    (u : Space n) :
    upperTaggedLatticeExponent k u =
      BoxIntegral.unitPartition.tag k
        (BoxIntegral.unitPartition.index k u) := by
  funext i
  simp only [upperTaggedLatticeExponent, BoxIntegral.unitPartition.tag,
    BoxIntegral.unitPartition.index, Int.cast_sub, Int.cast_one, sub_add_cancel]

private theorem tendsto_upperTaggedLatticeExponent
    {n : ℕ} (u : Space n) :
    Tendsto (fun k : ℕ => upperTaggedLatticeExponent k u)
      atTop (𝓝 u) := by
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  have htag := tendsto_unitPartition_tag_index u
  simpa only [upperTaggedLatticeExponent_eq_unitPartition_tag] using htag

private def momentTaggedLaurentObservable
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (k : ℕ)
    (f : Space n → ℝ)
    (u : Space n) : ℝ := by
  classical
  exact
    if hk : 0 < k then
      if hu : u ∈ scaledIntegerLattice n k then
        momentNormalizedLaurentObservable F k f u
      else 0
    else 0

private theorem unitPartition_tag_index_mem_scaledIntegerLattice
    {n : ℕ} (k : ℕ) (u : Space n) :
    BoxIntegral.unitPartition.tag (k + 1)
        (BoxIntegral.unitPartition.index (k + 1) u) ∈
      scaledIntegerLattice n (k + 1) := by
  rw [scaledIntegerLattice, ← Submodule.coe_pointwise_smul]
  exact BoxIntegral.unitPartition.tag_mem_smul_span
    (n := k + 1)
    (BoxIntegral.unitPartition.index (k + 1) u)

private theorem norm_momentTaggedLaurentObservable_le_of_mem_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    ∀ k : ℕ, ∀ u ∈ interior K.carrier,
      ‖momentTaggedLaurentObservable F k f u‖ ≤ C := by
  classical
  have hCnonneg : 0 ≤ C :=
    (abs_nonneg (f (0 : Space n))).trans (hC 0)
  intro k u hu
  unfold momentTaggedLaurentObservable
  split_ifs with hk hl
  · let v : monomialIndex K k := ⟨u, ⟨hu, hl⟩⟩
    simpa only [Real.norm_eq_abs, ge_iff_le] using
      abs_momentNormalizedLaurentObservable_le
        K hk F htransport f hf C hC v
  · simpa only [norm_zero] using hCnonneg
  · simpa only [norm_zero] using hCnonneg

private theorem tendsto_momentTaggedLaurentObservable_unitPartition_tag
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hdu : DifferentiableAt ℝ (legendreTransform F.potential) u)
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    Tendsto
      (fun k : ℕ =>
        momentTaggedLaurentObservable F (k + 1) f
          (BoxIntegral.unitPartition.tag (k + 1)
            (BoxIntegral.unitPartition.index (k + 1) u)))
      atTop
      (𝓝 (f
        (SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential) u))) := by
  have hraw :
      Tendsto
        (fun k : ℕ =>
          momentNormalizedLaurentObservable F k f
            (upperTaggedLatticeExponent k u))
        atTop
        (𝓝 (f
          (SpatialBergmanFatouScheffe.actualGradient
            (legendreTransform F.potential) u))) := by
    unfold momentNormalizedLaurentObservable
    exact tendsto_momentNormalized_moving_monomial_bounded_observable
      F htransport hu hdu
      (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u)
      (momentNormalizedPhase_dualGradient_maximizer
        F htransport hu hdu)
      (fun k => upperTaggedLatticeExponent k u)
      (tendsto_upperTaggedLatticeExponent u)
      f hf C hC
  have hshift := hraw.comp (Filter.tendsto_add_atTop_nat 1)
  have htag (k : ℕ) :
      BoxIntegral.unitPartition.tag (k + 1)
          (BoxIntegral.unitPartition.index (k + 1) u) ∈
        scaledIntegerLattice n (k + 1) :=
    unitPartition_tag_index_mem_scaledIntegerLattice k u
  simpa only [momentTaggedLaurentObservable, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
    ↓reduceDIte, htag, comp_def, upperTaggedLatticeExponent_eq_unitPartition_tag] using hshift

private theorem ae_tendsto_momentTaggedLaurentObservable_interior_unitPartition_tag
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    ∀ᵐ x : Space n
      ∂(volume : Measure (Space n)),
      Tendsto
        (fun k : ℕ =>
          (interior K.carrier).indicator
            (momentTaggedLaurentObservable F (k + 1) f)
            (BoxIntegral.unitPartition.tag (k + 1)
              (BoxIntegral.unitPartition.index (k + 1) x)))
        atTop
        (𝓝 ((interior K.carrier).indicator
          (fun u : Space n =>
            f (SpatialBergmanFatouScheffe.actualGradient
              (legendreTransform F.potential) u)) x)) := by
  have hfront :
      ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
        x ∉ frontier (interior K.carrier) :=
    compl_mem_ae_iff.mpr
      (K.convex.interior.addHaar_frontier
        (volume : Measure (Space n)))
  filter_upwards [hfront,
    ae_differentiableAt_finiteEnergySourceLegendre_interior
      F htransport] with x hxfront hxdual
  by_cases hx : x ∈ interior K.carrier
  · have htags :
        ∀ᶠ k : ℕ in atTop,
          BoxIntegral.unitPartition.tag (k + 1)
              (BoxIntegral.unitPartition.index (k + 1) x) ∈
            interior K.carrier :=
      (tendsto_unitPartition_tag_index x).eventually
        (isOpen_interior.mem_nhds hx)
    rw [Set.indicator_of_mem hx]
    apply
      (tendsto_momentTaggedLaurentObservable_unitPartition_tag
        F htransport hx (hxdual hx) f hf C hC).congr'
    filter_upwards [htags] with k hk
    simp only [Set.indicator_of_mem hk]
  · have hxclosure : x ∉ closure (interior K.carrier) := by
      intro hcl
      apply hxfront
      change x ∈ closure (interior K.carrier) \
        interior (interior K.carrier)
      exact ⟨hcl, by simpa only [interior_interior] using hx⟩
    have hcomp :
        (closure (interior K.carrier))ᶜ ∈ 𝓝 x :=
      isClosed_closure.isOpen_compl.mem_nhds hxclosure
    have htags :
        ∀ᶠ k : ℕ in atTop,
          BoxIntegral.unitPartition.tag (k + 1)
              (BoxIntegral.unitPartition.index (k + 1) x) ∉
            interior K.carrier := by
      have hout :=
        (tendsto_unitPartition_tag_index x).eventually hcomp
      filter_upwards [hout] with k hk
      exact fun hmem => hk (subset_closure hmem)
    rw [Set.indicator_of_notMem hx]
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [htags] with k hk
    simp only [Set.indicator_of_notMem hk]

end BergmanJetUpperTaggedMonomialObservableConvergence

namespace Volume

open Set Function Filter MeasureTheory
open TorusCharacters LatticeAsymptotics BergmanMonomials BergmanNormalization LaplaceAsymptotics
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open MomentRegularity BergmanJetPartitionEndpoint BergmanJetTriangularLatticeConvergence
open BergmanJetDiagonalObservableLatticeIdentity BergmanJetDualGradientInverseTransport
open BergmanJetUpperTaggedMonomialObservableConvergence BergmanJetPortmanteauActualVolumeBridge
open BergmanJetRadialHaarWeakProbabilityLift
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction

private theorem interior_dualGradient_average_eq_sourceGibbs
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f) :
    (∫ u in interior K.carrier,
      f (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u)
      ∂(volume : Measure (Space n))) /
        normalizedVolume K.carrier =
      ∫ x : Space n, f x
        ∂(finiteEnergySourceGibbsProbability F) := by
  have hinterior :
      (∫ u in interior K.carrier,
        f (SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential) u)
        ∂(volume : Measure (Space n))) =
        ∫ u in K.carrier,
          f (SpatialBergmanFatouScheffe.actualGradient
            (legendreTransform F.potential) u)
          ∂(volume : Measure (Space n)) :=
    MeasureTheory.setIntegral_congr_set
      (interior_ae_eq_of_null_frontier
        (K.convex.addHaar_frontier
          (volume : Measure (Space n))))
  rw [hinterior]
  calc
    (∫ u in K.carrier,
      f (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u)
      ∂(volume : Measure (Space n))) /
        normalizedVolume K.carrier =
      ∫ u : Space n,
        f (SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential) u)
        ∂(normalizedTargetBodyMeasure K) := by
      rw [integral_normalizedTargetBodyMeasure]
      ring
    _ = ∫ x : Space n, f x
        ∂(finiteEnergySourceGibbsProbability F) :=
      integral_finiteEnergySourceLegendreGradient_target
        F htransport f hf

private theorem momentNormalizedDiagonalRadialWeakTests_unconditional
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ f : Space n →ᵇ ℝ,
      Tendsto
        (fun k : ℕ =>
          ∫ x : Space n,
            f x * normalizedDiagonalDensity
              K (k + 1) (momentNormalizedPotential F) x
              ∂(volume : Measure (Space n)))
        atTop
        (𝓝 (∫ x : Space n, f x
          ∂(finiteEnergySourceGibbsProbability F))) := by
  intro f
  have hf : Continuous (fun x : Space n => f x) := f.continuous
  have hC : ∀ x : Space n, |f x| ≤ ‖f‖ := fun x => by
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
  obtain ⟨B, hB, hsubset⟩ :=
    BoxIntegral.le_hasIntegralVertices_of_isBounded
      (K.compact.isBounded.subset interior_subset)
  let G : ℕ → Space n → ℝ := fun k u =>
    momentTaggedLaurentObservable F k (fun x => f x) u
  let g : Space n → ℝ := fun u =>
    f (SpatialBergmanFatouScheffe.actualGradient
      (legendreTransform F.potential) u)
  have hbound :
      ∀ k : ℕ, 0 < k → ∀ u ∈ interior K.carrier,
        u ∈ scaledIntegerLattice n k → ‖G k u‖ ≤ ‖f‖ := by
    intro k hk u hu hulattice
    exact norm_momentTaggedLaurentObservable_le_of_mem_interior
      F htransport (fun x => f x) hf ‖f‖ hC k u hu
  have hpoint :
      ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
        Tendsto
          (fun k : ℕ =>
            (interior K.carrier).indicator
              (G (k + 1))
              (BoxIntegral.unitPartition.tag (k + 1)
                (BoxIntegral.unitPartition.index (k + 1) x)))
          atTop (𝓝 ((interior K.carrier).indicator g x)) :=
    ae_tendsto_momentTaggedLaurentObservable_interior_unitPartition_tag
      F htransport (fun x => f x) hf ‖f‖ hC
  have hscaled :=
    tendsto_moving_lattice_sum_of_ae_tag_convergence
      B hB (interior K.carrier) hsubset
      isOpen_interior.measurableSet
      G g ‖f‖ (norm_nonneg f) hbound hpoint
  have hscaled' :
      Tendsto
        (fun k : ℕ =>
          (∑' u : monomialIndex K (k + 1),
            G (k + 1) (u : Space n)) /
              (((k + 1 : ℕ) : ℝ) ^ n))
        atTop
        (𝓝 (∫ u in interior K.carrier,
          g u ∂(volume : Measure (Space n)))) := by
    simpa only [monomialIndex, Nat.cast_add, Nat.cast_one] using hscaled
  have haverage :
      Tendsto
        (fun k : ℕ =>
          (∑' u : monomialIndex K (k + 1),
            G (k + 1) (u : Space n)) /
              (bergmanDimension K (k + 1) : ℝ))
        atTop
        (𝓝 ((∫ u in interior K.carrier,
          g u ∂(volume : Measure (Space n))) /
            normalizedVolume K.carrier)) := by
    have hquot := hscaled'.div
      ((bergmanDimension_div_pow_tendsto_volume K).comp
        (Filter.tendsto_add_atTop_nat 1)) K.volume_pos.ne'
    refine hquot.congr' (Filter.Eventually.of_forall fun k => ?_)
    exact div_div_div_cancel_right₀ (by positivity)
      (∑' u : monomialIndex K (k + 1),
        G (k + 1) (u : Space n))
      (bergmanDimension K (k + 1) : ℝ)
  have hG :
      (fun k : ℕ =>
        (∑' u : monomialIndex K (k + 1),
          G (k + 1) (u : Space n)) /
            (bergmanDimension K (k + 1) : ℝ)) =
      fun k : ℕ =>
        (∑' u : monomialIndex K (k + 1),
          momentNormalizedLaurentObservable
            F (k + 1) (fun x => f x) (u : Space n)) /
            (bergmanDimension K (k + 1) : ℝ) := by
    funext k
    congr 1
    apply tsum_congr
    intro u
    change
      momentTaggedLaurentObservable
        F (k + 1) (fun x => f x) (u : Space n) =
        momentNormalizedLaurentObservable
          F (k + 1) (fun x => f x) (u : Space n)
    simp only [momentTaggedLaurentObservable, Nat.zero_lt_succ k, ↓reduceDIte, u.property.2]
  rw [hG] at haverage
  have hlimit :
      (∫ u in interior K.carrier,
        g u ∂(volume : Measure (Space n))) /
        normalizedVolume K.carrier =
        ∫ x : Space n, f x
          ∂(finiteEnergySourceGibbsProbability F) :=
    interior_dualGradient_average_eq_sourceGibbs
      F htransport (fun x => f x) hf
  rw [hlimit] at haverage
  have hdiagonal :
      (fun k : ℕ =>
        ∫ x : Space n,
          f x * normalizedDiagonalDensity
            K (k + 1) (momentNormalizedPotential F) x
            ∂(volume : Measure (Space n))) =
        fun k : ℕ =>
          (∑' u : monomialIndex K (k + 1),
            momentNormalizedLaurentObservable
              F (k + 1) (fun x => f x) (u : Space n)) /
              (bergmanDimension K (k + 1) : ℝ) := by
    funext k
    exact integral_momentNormalizedDiagonal_eq_laurentObservable_average
      K (Nat.zero_lt_succ k) F htransport (fun x => f x) hf ‖f‖ hC
  rw [← hdiagonal] at haverage
  exact haverage

private theorem momentBodyBergmanWeakProbabilityConvergence_unconditional
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p)) :=
  momentBodyBergmanWeakProbabilityConvergence_of_radial_tests K p
    (momentNormalizedDiagonalRadialWeakTests_unconditional
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K))

/-- Ehrhart's sharp volume inequality for a centered convex body with one interior lattice point. -/
public
theorem ehrhart_volume_inequality_for_sets {n : ℕ} (hn : 0 < n)
    (S : Set (Space n)) (hconvex : Convex ℝ S)
    (hcompact : IsCompact S) (hinterior : (interior S).Nonempty)
    (hcentered : barycenter S = 0)
    (hlattice : interiorLatticePoints S = {0}) :
    normalizedVolume S ≤ ((n : ℝ) + 1) ^ n / (n.factorial : ℝ) := by
  let K : CenteredBody n :=
    { carrier := S
      convex := hconvex
      compact := hcompact
      fullDimensional := hinterior
      centered := hcentered
      uniqueInteriorLatticePoint := hlattice }
  simpa only [ge_iff_le, sharpConstant] using
    normalizedVolume_le_sharpConstant_of_momentBodyWeakProbability hn K
      (momentBodyBergmanWeakProbabilityConvergence_unconditional
        K (0 : LogSpace n))

end Volume

end Ehrhart

end
