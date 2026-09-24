/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedTransferClause
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSmallCell
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCorrectedSWS
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSlice
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientSWS
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstancePairing
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.ThetaDecayTShape
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Neighborhood
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ProducerRegularity
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradientInstances
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAOneRoundFinal
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAFirstRoundConsumer
public import LeanPool.CaffarelliKohnNirenberg.Core.Parameters
public import LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecOn
public import LeanPool.CaffarelliKohnNirenberg.Statements.RegularPoint
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremBAdaptersCZ
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremBAdaptersCZSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.GradientSlotDuhamel

/-! # The gradient regularity criterion from a small-cell majorant

For `thm:B`, suitable-solution slice derivatives determine one measurable
pressure gradient. The slice majorant in `sec:pressure` transfers to this
field by uniqueness. Finite covering supplies its whole-carrier integral,
and the two cell regimes give the pressure-gradient input of the criterion.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Core.Step3 CKN.Core.Step4
noncomputable section

namespace CKN.Core.Endgame
private theorem finite_cover_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} (s : Finset ι) (U : ι → Set α) (f : α → ℝ≥0∞)
    (h : ∀ i ∈ s, (∫⁻ x in U i, f x ∂μ) < ⊤) :
    (∫⁻ x in ⋃ i ∈ s, U i, f x ∂μ) < ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact lt_of_le_of_lt (lintegral_union_le f _ _)
      (ENNReal.add_lt_top.mpr ⟨h a (by simp), ih (fun i hi => h i (by simp [hi]))⟩)

private theorem compact_integral_of_cylinders
    {K : Set ParabolicPoint} (hK : IsCompact K) {g : ParabolicPoint → ℝ}
    {P r : ℝ} (hr : 0 < r)
    (hcell : ∀ z : ParabolicPoint, cylinderPowerIntegral P g z r < ⊤) :
    (∫⁻ z in K, ENNReal.ofReal |g z| ^ P) < ⊤ := by
  classical
  let U : ParabolicPoint → Set ParabolicPoint := fun z =>
    vec3Ball z.1 r ×ˢ Ioo (z.2 - r ^ 2 / 2) (z.2 + r ^ 2 / 2)
  have hU : ∀ z, IsOpen (U z) := fun z =>
    ((isOpen_vec3Ball z.1 r).prod isOpen_Ioo).preimage parabolicHomeomorph.continuous
  have hcover : K ⊆ ⋃ z : ParabolicPoint, U z := by
    intro z _
    refine mem_iUnion.mpr ⟨z, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · change vec3EuclideanNorm (z.1 - z.1) < r
      simpa only [sub_self, vec3EuclideanNorm_zero] using hr
    · have hsq := sq_pos_of_pos hr
      linarith only [hsq]
    · have hsq := sq_pos_of_pos hr
      linarith only [hsq]
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU hcover
  apply lt_of_le_of_lt (lintegral_mono_set hs)
  apply finite_cover_integral s U _
  intro z _
  have hsub : U z ⊆ parabolicCylinder z.1 (z.2 + r ^ 2 / 2) r := by
    intro w hw
    refine ⟨hw.1, ?_, hw.2.2.le⟩
    linarith only [hw.2.1]
  exact lt_of_le_of_lt (lintegral_mono_set hsub) (hcell (z.1, z.2 + r ^ 2 / 2))

/-- Suitability supplies one measurable weak pressure gradient on a larger
spatial carrier throughout the symmetric time window of `thm:B`. -/
theorem theoremB_measurable_pressure_gradient_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R)
    (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      ∀ᵐ s ∂volume.restrict (Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2)), ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball z₀.1 (3 * R / 4)) volume ∧
        HasWeakPartialDerivOn (vec3Ball z₀.1 (3 * R / 4)) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i) := by
  let J := Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2)
  have hbox := localBox_of_parabolic_ball hR hdom
  have hp := Core.Step4.pressure_integrable_on_of_suitable_local_box hsol hbox (Subset.refl _)
  have hpProd : Integrable (fun z : Vec3 × ℝ => p z)
      ((volume.restrict (vec3Ball z₀.1 R)).prod (volume.restrict J)) := by
    change Integrable (fun z : Vec3 × ℝ => p z) (volume.restrict (vec3Ball z₀.1 R ×ˢ J)) at hp
    rwa [Measure.volume_eq_prod, ← Measure.prod_restrict] at hp
  have hploc : ∀ᵐ s ∂volume.restrict J,
      LocallyIntegrableOn (fun x => p (x, s)) (vec3Ball z₀.1 R) volume :=
    hpProd.prod_left_ae.mono (fun _ hs => IntegrableOn.locallyIntegrableOn hs)
  have hJI : J ⊆ I := subset_closure.trans hbox.2.2.2.2.2
  have hslices (i : Fin 3) : ∀ᵐ s ∂volume.restrict J, ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball z₀.1 R) volume ∧
      HasWeakPartialDerivOn (vec3Ball z₀.1 R) i (fun x => p (x, s)) g := by
    apply Core.Step4.ae_exists_weakPartialDerivOn_ball_of_small_euclidean_cylinders
      isOpen_Ioo (subset_closure.trans hbox.2.2.1) hploc
    intro c t ρ hρ hsub
    have hsub' : closure (parabolicCylinder c t ρ) ⊆ spaceTimeSet Ω I :=
      hsub.trans (Set.prod_mono Subset.rfl hJI)
    have hs := Core.Step4.slice_selected_gradient_corrected_ae_of_sws_data
      (1000 * harmonicInteriorDisplayConstant) czP1OperatorConstant
      sliceForceGradientConstant le_rfl le_rfl le_rfl hsol (z := (c, t)) hρ hsub'
    filter_upwards [hs] with s h
    obtain ⟨D, hloc, _hmem, hweak, _hbound⟩ := h
    exact ⟨fun x => D x i, hloc i, hweak i⟩
  have hUB : closure (vec3Ball z₀.1 (3 * R / 4)) ⊆ vec3Ball z₀.1 R :=
    Core.Step4.closure_vec3Ball_subset_vec3Ball (by positivity) (by linarith only [hR])
  obtain ⟨Dp, hDp, hw⟩ := exists_measurable_weakGradient_on_time_union
    (isOpen_vec3Ball _ _) (isOpen_vec3Ball _ _)
    (CKN.Foundation.Parabolic.isCompact_closure_vec3Ball (by positivity)) hUB
    (I := J) (J := fun _ : ℕ => J) (fun _ => measurableSet_Ioo) (iUnion_const J)
    (fun _ => hp) hslices
  exact ⟨Dp, hDp, hw.mono (fun _ h i => ⟨(h i).1, (h i).2.1⟩)⟩

private theorem field_pairing
    {B U : Set Vec3} {J : Set ℝ} {p : ParabolicPoint → ℝ} {Dp : ParabolicPoint → Vec3}
    (hU : IsOpen U) (hUB : U ⊆ B)
    (hp : IntegrableOn p (U ×ˢ J) volume)
    (hDp : ∀ i, IntegrableOn (fun z => Dp z i) (U ×ˢ J) volume)
    (hfield : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakPartialDerivOn B i (fun x => p (x,s)) (fun x => Dp (x,s) i))
    (i : Fin 3) (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) univ univ)
    (hsupp : tsupport ψ ⊆ U ×ˢ J) :
    (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
      -(∫ z : ParabolicPoint, Dp z i * ψ z) := by
  apply Core.Step4.OriginInstance.spacetime_pairing_of_iterated hψ hsupp hp (hDp i)
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [hfield] with s hs
  obtain ⟨hsm, hcomp, hsp⟩ := slice_testFunction hψ.1 hψ.2.1 hsupp s
  exact (hs i).restrict hU hUB (fun x => ψ (x,s)) hsm hcomp hsp

private theorem small_cells
    {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {R κ : ℝ}
    {p : ParabolicPoint → ℝ} {Dp : ParabolicPoint → Vec3} {A : ℝ≥0∞}
    (hR : 0 < R) (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I)
    (hDp : Measurable Dp)
    (hfield : ∀ᵐ s ∂volume.restrict (Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2)), ∀ i,
      LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball z₀.1 (3 * R / 4)) volume ∧
      HasWeakPartialDerivOn (vec3Ball z₀.1 (3 * R / 4)) i
        (fun y => p (y,s)) (fun y => Dp (y,s) i))
    (N : Fin 3 → Vec3 → ℝ → ℝ → ℝ → ℝ≥0∞)
    (hslice : ∀ i c t ρ, 0 < ρ →
      closure (parabolicCylinder c t ρ) ⊆ spaceTimeSet Ω I →
      ∀ᵐ s ∂volume.restrict (Ioc (t - ρ ^ 2) t), ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) i (fun y => p (y,s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall c (ρ / 2))) ≤ N i c t ρ s)
    (hgrowth : ∀ (i : Fin 3) (z : ParabolicPoint) (r : ℝ), 0 < r → r ≤ R / 16 →
      (parabolicCylinder z.1 z.2 r ∩ Metric.ball z₀ (R / 2)).Nonempty →
      (∫⁻ s in Ioc (z.2 - r ^ 2) z.2, N i z.1 z.2 (2*r) s ^ (6/5 : ℝ)) ≤
        A * ENNReal.ofReal (r ^ (5 * (1 - (6/5 : ℝ) / κ)))) :
    ∀ i z r, 0 < r → r ≤ R / 16 →
      cylinderPowerIntegral (6/5 : ℝ)
        ((Metric.ball z₀ (R/2)).indicator (fun w => Dp w i)) z r ≤
        A * ENNReal.ofReal (r ^ (5 * (1 - (6/5 : ℝ) / κ))) := by
  intro i z r hr hsmall
  by_cases hmeet : (parabolicCylinder z.1 z.2 r ∩ Metric.ball z₀ (R / 2)).Nonempty
  · obtain ⟨hx, hlo, hhi⟩ := symmetric_margin_premises_of_meet hr hmeet
    have htri0 (a b c : Vec3) : vec3EuclideanNorm (a-c) ≤
        vec3EuclideanNorm (a-b) + vec3EuclideanNorm (b-c) := by
      simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
      simpa only [dist_eq_norm] using
        dist_triangle (WithLp.toLp 2 a) (WithLp.toLp 2 b) (WithLp.toLp 2 c)
    have hball : vec3Ball z.1 r ⊆ vec3Ball z₀.1 (3 * R / 4) := by
      intro y hy
      have htri := htri0 y z.1 z₀.1
      change vec3EuclideanNorm (y-z.1) < r at hy
      change vec3EuclideanNorm (y-z₀.1) < 3*R/4
      linarith only [hy,htri,hx,hsmall,hR]
    have hrr : r ^ 2 ≤ (R/16)^2 := (sq_le_sq₀ hr.le (by positivity)).mpr hsmall
    have htime : Ioc (z.2-r^2) z.2 ⊆ Ioo (z₀.2-R^2) (z₀.2+R^2) := by
      intro s hs
      constructor
      · nlinarith only [hs.1,hlo,hrr,sq_nonneg R]
      · nlinarith only [hs.2,hhi,hrr,sq_nonneg R]
    have hw : ∀ᵐ s ∂volume.restrict (Ioc (z.2-r^2) z.2),
        LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball z₀.1 (3*R/4)) volume ∧
        HasWeakPartialDerivOn (vec3Ball z₀.1 (3*R/4)) i
          (fun y => p (y,s)) (fun y => Dp (y,s) i) :=
      (ae_restrict_of_ae_restrict_of_subset htime hfield).mono (fun _ h => h i)
    exact (symmetric_margin_indicator_cylinderPowerIntegral_le hdom hR hr
      (by linarith only [hsmall,hR]) hball
      (((measurable_pi_apply i).comp hDp).aemeasurable) hw (hslice i)).trans
      (hgrowth i z r hr hsmall hmeet)
  · rw [cylinderPowerIntegral_indicator_eq_zero_of_disjoint (by norm_num : (0:ℝ)<6/5)
      (Set.not_nonempty_iff_eq_empty.mp hmeet)]
    exact bot_le
private theorem carrier_power_finite
    {z₀ : ParabolicPoint} {R κ : ℝ} {Dp : ParabolicPoint → Vec3} {A : ℝ≥0∞}
    (hR : 0 < R) (hA : A < ⊤)
    (hsmall : ∀ i z r, 0 < r → r ≤ R / 16 →
      cylinderPowerIntegral (6/5 : ℝ)
        ((Metric.ball z₀ (R/2)).indicator (fun w => Dp w i)) z r ≤
        A * ENNReal.ofReal (r ^ (5 * (1 - (6/5 : ℝ) / κ)))) :
    ∀ i, (∫⁻ w in Metric.ball z₀ (R/2), ENNReal.ofReal |Dp w i| ^ (6/5 : ℝ)) < ⊤ := by
  let S := Metric.ball z₀ (R/2)
  let K : Set ParabolicPoint := parabolicHomeomorph ⁻¹'
    (closure (vec3Ball z₀.1 (R/2)) ×ˢ Icc (z₀.2-R^2/4) (z₀.2+R^2/4))
  have hK : IsCompact K := parabolicHomeomorph.isCompact_preimage.mpr
    ((CKN.Foundation.Parabolic.isCompact_closure_vec3Ball (by positivity : 0 < R/2)).prod isCompact_Icc)
  have hSK : S ⊆ K := by
    rw [show S = Metric.ball z₀ (R/2) from rfl, metricBall_eq_parabolicBall]
    intro w hw
    refine ⟨subset_closure hw.1, ?_, ?_⟩
    · dsimp [K]
      nlinarith only [hw.2.1]
    · dsimp [K]
      nlinarith only [hw.2.2]
  intro i
  have hfin := compact_integral_of_cylinders hK (by positivity : 0 < R/16)
    (g := S.indicator (fun w => Dp w i)) (P := (6/5 : ℝ)) (fun z =>
      lt_of_le_of_lt (hsmall i z (R/16) (by positivity) le_rfl)
        (ENNReal.mul_lt_top hA ENNReal.ofReal_lt_top))
  have hle := lt_of_le_of_lt (lintegral_mono_set hSK) hfin
  rw [lintegral_carrier_indicator_eq measurableSet_ball] at hle
  exact hle

private theorem integrable_of_power_finite
    {S : Set ParabolicPoint} [IsFiniteMeasure (volume.restrict S)]
    {g : ParabolicPoint → ℝ} (hg : AEMeasurable g (volume.restrict S))
    (hfin : (∫⁻ w in S, ENNReal.ofReal |g w| ^ (6/5 : ℝ)) < ⊤) :
    Integrable g (volume.restrict S) := by
  have hmem : MemLp g (ENNReal.ofReal (6/5 : ℝ)) (volume.restrict S) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num)
      ENNReal.ofReal_ne_top hg.aestronglyMeasurable).mpr
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 6/5),
      Real.enorm_eq_ofReal_abs] using hfin
  exact hmem.integrable (by norm_num)

/-- A finite small-cell slice majorant supplies the full pressure-gradient
input of `thm:B`; the carrier integral follows by finite covering. -/
theorem theoremB_gradient_producer_of_small_cell_majorant
    (hGaugeCorrectedSmallCellMajorant :
      ∀ q τ : ℝ, 5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
        ∀ {Ω : Set Vec3} {I : Set ℝ}
          {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
          Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
          morreyVecMem 3 τ (Metric.ball z₀ R) u →
          (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
            (Metric.ball z₀ R) (fun z => Du z i)) →
          ∃ (A : ℝ≥0∞) (N : Fin 3 → Vec3 → ℝ → ℝ → ℝ → ℝ≥0∞), A < ⊤ ∧
            (∀ (i : Fin 3) (c : Vec3) (t ρ : ℝ), 0 < ρ →
              closure (parabolicCylinder c t ρ) ⊆ spaceTimeSet Ω I →
              ∀ᵐ s ∂volume.restrict (Ioc (t - ρ ^ 2) t), ∃ g : Vec3 → ℝ,
                LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
                HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) i
                  (fun y => p (y, s)) g ∧
                eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
                  (volume.restrict (euclideanBall c (ρ / 2))) ≤ N i c t ρ s) ∧
            (∀ (i : Fin 3) (z : ParabolicPoint) (r : ℝ), 0 < r → r ≤ R / 16 →
              (parabolicCylinder z.1 z.2 r ∩ Metric.ball z₀ (R / 2)).Nonempty →
              (∫⁻ s in Ioc (z.2 - r ^ 2) z.2,
                N i z.1 z.2 (2 * r) s ^ (6 / 5 : ℝ)) ≤
                A * ENNReal.ofReal
                  (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))))
    : routeAGradientProducerUniform := by
  apply routeA_gradient_of_glued_field_cell_bounds
  intro q τ hq hτ hτ' Ω I u Du p f hsol z₀ R hR hdom hu hDu
  obtain ⟨A, N, hA, hslice, hgrowth⟩ :=
    hGaugeCorrectedSmallCellMajorant q τ hq hτ hτ' hsol z₀ R hR hdom hu hDu
  obtain ⟨Dp, hDp, hfield⟩ := theoremB_measurable_pressure_gradient_of_sws hsol z₀ hR hdom
  have hsmall := small_cells hR hdom hDp hfield N hslice hgrowth
  have hfin := carrier_power_finite hR hA hsmall
  let S := Metric.ball z₀ (R/2)
  let U := vec3Ball z₀.1 (R/2)
  let J := Ioo (z₀.2-R^2/4) (z₀.2+R^2/4)
  have hSbox : S = U ×ˢ J := by
    rw [show S = Metric.ball z₀ (R/2) from rfl, metricBall_eq_parabolicBall]
    change vec3Ball z₀.1 (R/2) ×ˢ Ioo (z₀.2-(R/2)^2) (z₀.2+(R/2)^2) = _
    rw [show (R/2)^2 = R^2/4 by ring]
  have hJc : IsCompact (closure J) := by
    rw [show J = Ioo (z₀.2-R^2/4) (z₀.2+R^2/4) from rfl,
      closure_Ioo (by nlinarith only [sq_pos_of_pos hR] : z₀.2-R^2/4 ≠ z₀.2+R^2/4)]
    exact isCompact_Icc
  let : IsFiniteMeasure (volume.restrict S) := by
    rw [hSbox]
    exact Core.Step3.local_box_isFiniteMeasure
      (CKN.Foundation.Parabolic.isCompact_closure_vec3Ball (by positivity)) hJc
  have hInt (i : Fin 3) : Integrable (fun w => Dp w i) (volume.restrict S) :=
    integrable_of_power_finite (((measurable_pi_apply i).comp hDp).aemeasurable) (hfin i)
  have hJsub : J ⊆ Ioo (z₀.2-R^2) (z₀.2+R^2) := by
    intro s hs
    constructor
    · dsimp [J] at hs
      nlinarith only [hs.1,sq_nonneg R]
    · dsimp [J] at hs
      nlinarith only [hs.2,sq_nonneg R]
  have hUsub : U ⊆ vec3Ball z₀.1 (3*R/4) := by
    apply vec3Ball_mono
    linarith only [hR]
  have hpBig := pressure_integrable_on_of_suitable_local_box hsol
    (localBox_of_parabolic_ball hR hdom) (Subset.refl _)
  have hp : IntegrableOn p (U ×ˢ J) volume := hpBig.mono_set
    (prod_mono (vec3Ball_mono (by linarith only [hR] : R/2 ≤ R)) hJsub)
  refine ⟨Dp, fun i => ((measurable_pi_apply i).comp hDp).aemeasurable, hInt, ?_, ?_⟩
  · intro i ψ hψ hsupp
    apply field_pairing (isOpen_vec3Ball _ _) hUsub hp
      (fun j => by
        change Integrable (fun z => Dp z j) (volume.restrict (U ×ˢ J))
        rw [← hSbox]
        exact hInt j)
      ((ae_restrict_of_ae_restrict_of_subset hJsub hfield).mono
        (fun _ h j => (h j).2)) i ψ hψ
    intro z hz
    exact hSbox ▸ hsupp hz
  · let B := ∑ i : Fin 3, ∫⁻ w in S, ENNReal.ofReal |Dp w i| ^ (6/5 : ℝ)
    have hB : B < ⊤ := by
      exact ENNReal.sum_lt_top.mpr (fun i _ => hfin i)
    apply exists_routeA_cell_constant_of_small_cells_and_carrier_integral
      (routeA_uniform_kappa_min_lower hq hτ) (by positivity : 0 < R/16) hA hB hsmall
    intro i
    exact Finset.single_le_sum
      (f := fun j : Fin 3 => ∫⁻ w in S, ENNReal.ofReal |Dp w j| ^ (6/5 : ℝ))
      (fun _ _ => bot_le) (Finset.mem_univ i)

/-- The gradient criterion `thm:B`, conditional only on the finite
small-cell majorant for the pressure-gradient slices in `sec:pressure`. -/
theorem epsilonRegularityGradient_closer_of_small_cell_majorant
    (q : ℝ) (hq : 5 / 2 < q)
    (hGaugeCorrectedSmallCellMajorant :
      ∀ q τ : ℝ, 5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
        ∀ {Ω : Set Vec3} {I : Set ℝ}
          {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
          Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
          morreyVecMem 3 τ (Metric.ball z₀ R) u →
          (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
            (Metric.ball z₀ R) (fun z => Du z i)) →
          ∃ (A : ℝ≥0∞) (N : Fin 3 → Vec3 → ℝ → ℝ → ℝ → ℝ≥0∞), A < ⊤ ∧
            (∀ (i : Fin 3) (c : Vec3) (t ρ : ℝ), 0 < ρ →
              closure (parabolicCylinder c t ρ) ⊆ spaceTimeSet Ω I →
              ∀ᵐ s ∂volume.restrict (Ioc (t - ρ ^ 2) t), ∃ g : Vec3 → ℝ,
                LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
                HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) i
                  (fun y => p (y, s)) g ∧
                eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
                  (volume.restrict (euclideanBall c (ρ / 2))) ≤ N i c t ρ s) ∧
            (∀ (i : Fin 3) (z : ParabolicPoint) (r : ℝ), 0 < r → r ≤ R / 16 →
              (parabolicCylinder z.1 z.2 r ∩ Metric.ball z₀ (R / 2)).Nonempty →
              (∫⁻ s in Ioc (z.2 - r ^ 2) z.2,
                N i z.1 z.2 (2 * r) s ^ (6 / 5 : ℝ)) ≤
                A * ENNReal.ofReal
                  (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))))) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) →
        ∀ z₀ ∈ spaceTimeSet Ω I,
          Filter.limsup (fun r : ℝ =>
              (ENNReal.ofReal r)⁻¹ *
                ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
                  ENNReal.ofReal (spatialGradientSq u Du w))
            (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
          IsRegularPoint Ω I u z₀ := by
  let C₁₂_p1 := (9 * max CKN.Foundation.Euclidean.czP1OperatorConstant 0) *
    (9 * CKN.sobolevPoincareL6Constant.toReal)
  have hCZ_p1 := theoremB_hCZ_p1_of_sws q
  have hG := theoremB_gradient_producer_of_small_cell_majorant hGaugeCorrectedSmallCellMajorant
  obtain ⟨C₂₇, C₂₈, hC₂₇, hC₂₈, hThetaDecay⟩ :=
    CKN.Core.Step3.thetaDecay_T_of_inputs q C₁₂_p1 hCZ_p1
  refine ⟨iterationEpsilonStar C₂₇, iterationEpsilonStar_pos hC₂₇, ?_⟩
  intro Ω I u Du p f hsol z₀ hz₀ hgradient
  obtain ⟨r₂, M, hr₂, _hM, hcarrier, _hdecay, hu, hDu, _hp⟩ :=
    Core.Endgame.morrey_sources_of_gradient_limsup hsol hq hz₀ hC₂₇ hC₂₈
      (hThetaDecay Ω I u Du p f hsol) hgradient
  exact Core.Endgame.regular_point_of_local_producers q hq hG
    (routeA_one_round_velocity_improvement_of_gradient_inputs
      (by
        intro q' hq'
        exact hG q' (25 / 3) hq' (by norm_num) (by norm_num))
      CKN.Core.Step3.localized_gradient_slot_duhamel_of_sws)
    CKN.Core.Step3.localized_gradient_slot_duhamel_of_sws
    localized_gradient_source_package_of_sws
    hsol z₀ (r₂ / 4) (by positivity)
    ((Metric.ball_subset_ball (by linarith only [hr₂])).trans hcarrier) hu hDu

end CKN.Core.Endgame
