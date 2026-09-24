/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBSlotInstancesCollar
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBSlotThreshold
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceMeasurable
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBSlotEnergy

/-! # The whole-carrier pressure-gradient time mass of `prop:bootstrap`

The B slot of `prop:bootstrap` asks for the actual clipped `L^{6/5}` time mass
of a selected weak pressure gradient on the origin carrier `B_{R₁}`, measured
against a coefficient carrying no velocity or gradient Morrey datum.  This file
proves that estimate at the two exponent/radius triples of the endgame, above
one absolute Calderón–Zygmund threshold.

The route is: transfer the binder's field to the interior measurable weak
gradient of `eq:pressure-gradient-morrey`, cover the carrier by the fixed finite
lattice of collars of radius `1/8`, and add the collar estimates.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- Any weak slice derivative of the pressure on an origin carrier agrees
almost everywhere with the interior measurable weak gradient of
`eq:pressure-gradient-morrey` on the ball of radius `7/8`. -/
theorem bslot_origin_gradient_transfer
    {Ω : Set Vec3} {I : Set ℝ} {q R₁ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR₁ : R₁ ≤ 7 / 8)
    (Dp : ParabolicPoint → Vec3)
    (hw : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i)) :
    ∃ D : ParabolicPoint → Vec3, Measurable D ∧
      (∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
        LocallyIntegrableOn (fun x => D (x, s) k) (vec3Ball (0 : Vec3) (7 / 8)) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) (7 / 8)) k
          (fun x => p (x, s)) (fun x => D (x, s) k) ∧
        (fun x => D (x, s) k) =ᵐ[volume.restrict (vec3Ball (0 : Vec3) R₁)]
          (fun x => Dp (x, s) k)) := by
  obtain ⟨D, hmD, hDae⟩ := origin_measurable_weak_gradient_of_sws hsol hdom
    (by norm_num : (0 : ℝ) < 7 / 8) (by norm_num : (7 : ℝ) / 8 < 1)
  refine ⟨D, hmD, ?_⟩
  filter_upwards [hDae, hw] with s hs hws
  intro k
  exact ⟨(hs k).1, (hs k).2.1,
    (hs k).2.2 (vec3Ball (0 : Vec3) R₁) (isOpen_vec3Ball _ _) (vec3Ball_mono hR₁)
      (fun y => Dp (y, s) k) (hws k).1 (hws k).2⟩

/-- The fixed lattice of collars covers every origin carrier of radius at most
`11/16`, so the carrier mass is at most the sum of the cell masses. -/
theorem bslot_carrier_mass_le_cell_sum
    {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 11 / 16) (Φ : ParabolicPoint → ℝ≥0∞) :
    (∫⁻ w in parabolicCylinder (0 : Vec3) 0 R, Φ w) ≤
      ∑' k : {k : (Fin 3 → ℤ) × ℤ // k ∈ originBSlotLatticeIndices},
        ∫⁻ w in parabolicCylinder
          (originLatticeCentre (1 / 16) (k : (Fin 3 → ℤ) × ℤ)).1
          (originLatticeCentre (1 / 16) (k : (Fin 3 → ℤ) × ℤ)).2 (1 / 16), Φ w := by
  have hsub : parabolicCylinder (0 : Vec3) 0 R ⊆
      ⋃ k : {k : (Fin 3 → ℤ) × ℤ // k ∈ originBSlotLatticeIndices},
        parabolicCylinder (originLatticeCentre (1 / 16) (k : (Fin 3 → ℤ) × ℤ)).1
          (originLatticeCentre (1 / 16) (k : (Fin 3 → ℤ) × ℤ)).2 (1 / 16) := by
    intro w hw
    obtain ⟨k, hk, hmem⟩ :=
      originBSlotLatticeIndices_covers w (parabolicCylinder_mono hR0 hR hw)
    exact Set.mem_iUnion.mpr ⟨⟨k, hk⟩, hmem⟩
  exact (lintegral_mono_set hsub).trans (lintegral_iUnion_le _ _)

/-- A ball of radius `1/4` inside the unit ball has its centre well inside the
ball of radius `13/16`. -/
private theorem bslot_centre_norm_le {x : Vec3}
    (h : vec3Ball x (1 / 4 : ℝ) ⊆ vec3Ball (0 : Vec3) 1) :
    vec3EuclideanNorm x ≤ 13 / 16 := by
  rcases eq_or_lt_of_le (vec3EuclideanNorm_nonneg x) with h0 | h0
  · rw [← h0]
    norm_num
  · set n : ℝ := vec3EuclideanNorm x with hn
    set c : ℝ := (3 / 16) / n with hc
    have hc0 : 0 ≤ c := by positivity
    have hshift : (1 + c) • x - x = c • x := by
      rw [add_smul, one_smul, add_sub_cancel_left]
    have hy : (1 + c) • x ∈ vec3Ball x (1 / 4 : ℝ) := by
      change vec3EuclideanNorm ((1 + c) • x - x) < 1 / 4
      rw [hshift, vec3EuclideanNorm_smul, abs_of_nonneg hc0, hc, ← hn,
        div_mul_cancel₀ _ (ne_of_gt h0)]
      norm_num
    have hmem := h hy
    change vec3EuclideanNorm ((1 + c) • x - 0) < 1 at hmem
    rw [sub_zero, vec3EuclideanNorm_smul, abs_of_nonneg (by linarith only [hc0]),
      ← hn, add_mul, one_mul, hc] at hmem
    rw [div_mul_cancel₀ _ (ne_of_gt h0)] at hmem
    linarith only [hmem]

/-- The absolute harmonic remainder constant of `eq:pressure-gradient-decomposition`,
supplied by the interior estimate for the harmonic pressure part. -/
def bslotRemainderConstant : ℝ :=
  Classical.choose exists_fixed_remainder_quantitative_majorant

/-- The remainder constant is nonnegative and majorizes the smooth remainder
gradient on every collar half ball. -/
theorem bslotRemainderConstant_spec :
    0 ≤ bslotRemainderConstant ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} (_hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
        {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ/2),
            ‖classicalGradient
              (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                (sourceSliceCentredMean z.1 ρ u) p s +
                pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤
              fixedRemainderSliceMajorant bslotRemainderConstant ρ z.1 u f p s :=
  Classical.choose_spec exists_fixed_remainder_quantitative_majorant

/-- The whole-carrier coefficient of `prop:bootstrap`: the fixed collar count
times the collar coefficient at radius `1/8`. -/
def bslotCarrierConstant : ℝ≥0∞ :=
  ((49 ^ 3 * 243 : ℕ) : ℝ≥0∞) * bslotCollarConstant bslotRemainderConstant (1 / 8)

/-- The absolute Calderón–Zygmund threshold above which the B slot of
`prop:bootstrap` is paid by its own coefficient. -/
def bslotThresholdB : ℝ := bslotCarrierConstant.toReal

/-- **The whole-carrier pressure-gradient time mass.**  Any weak slice
derivative of the pressure on an origin carrier of radius at most `11/16` has
`6/5` time mass at most an explicit absolute multiple of `ε + 1`. -/
theorem bslot_carrier_time_mass_le
    (ε : ℝ) (hε : 0 ≤ ε)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε)
    {R₁ : ℝ} (hR₁0 : 0 ≤ R₁) (hR₁ : R₁ ≤ 11 / 16)
    (Dp : ParabolicPoint → Vec3)
    (hw : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i))
    (i : Fin 3) :
    (∫⁻ s in Ioc (-(R₁ ^ 2)) 0,
      eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
      bslotCarrierConstant * (ENNReal.ofReal ε + 1) := by
  obtain ⟨hC0, hCmaj⟩ := bslotRemainderConstant_spec
  obtain ⟨D, hmD, hDae⟩ := bslot_origin_gradient_transfer hsol hdom
    (by linarith only [hR₁] : R₁ ≤ 7 / 8) Dp hw
  -- the carrier time interval sits inside the solution's time interval
  obtain ⟨_, hIcc⟩ := OriginInstance.originUnitBall_subset_of_dom hdom
  have hJsub : Ioc (-(R₁ ^ 2)) 0 ⊆ I := by
    intro t ht
    refine hIcc ⟨?_, ht.2⟩
    have h1 : R₁ ^ 2 ≤ 1 := by nlinarith only [hR₁, hR₁0]
    linarith only [ht.1, h1]
  -- replace the binder's field by the interior measurable weak gradient
  have hcongr : (∫⁻ s in Ioc (-(R₁ ^ 2)) 0,
      eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) =
      ∫⁻ s in Ioc (-(R₁ ^ 2)) 0,
        eLpNorm (fun y => D (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mono (Measure.restrict_mono hJsub le_rfl) hDae] with s hs
    rw [eLpNorm_congr_ae (hs i).2.2]
  rw [hcongr]
  have hDmi : Measurable (fun w : ParabolicPoint => D w i) :=
    (measurable_pi_apply i).comp hmD
  have hEJ : vec3Ball (0 : Vec3) R₁ ×ˢ Ioc (-(R₁ ^ 2)) 0 =
      parabolicCylinder (0 : Vec3) 0 R₁ := by
    rw [parabolicCylinder, zero_sub]
  rw [vector_time_slice_norm_power_eq (V := ℝ) (P := (6 / 5 : ℝ)) (by norm_num)
    (G := fun w : ParabolicPoint => D w i) (E := vec3Ball (0 : Vec3) R₁)
    (J := Ioc (-(R₁ ^ 2)) 0) hDmi.aestronglyMeasurable, hEJ]
  -- every cell obeys the collar estimate
  have hcell : ∀ k : {k : (Fin 3 → ℤ) × ℤ // k ∈ originBSlotLatticeIndices},
      (∫⁻ w in parabolicCylinder
        (originLatticeCentre (1 / 16) (k : (Fin 3 → ℤ) × ℤ)).1
        (originLatticeCentre (1 / 16) (k : (Fin 3 → ℤ) × ℤ)).2 (1 / 16),
        ENNReal.ofReal ‖D w i‖ ^ (6 / 5 : ℝ)) ≤
      bslotCollarConstant bslotRemainderConstant (1 / 8) * (ENNReal.ofReal ε + 1) := by
    intro k
    set zc : ParabolicPoint := originLatticeCentre (1 / 16) (k : (Fin 3 → ℤ) × ℤ) with hzc
    have hparent := originBSlotLatticeIndices_parent_subset k.2
    have hx : vec3EuclideanNorm zc.1 ≤ 13 / 16 := by
      refine bslot_centre_norm_le (fun y hy => ?_)
      have hmem : ((y, zc.2) : ParabolicPoint) ∈
          parabolicCylinder zc.1 zc.2 (1 / 4 : ℝ) := ⟨hy, by constructor <;> norm_num⟩
      exact (hparent hmem).1
    have hQ2 : parabolicCylinder zc.1 zc.2 (2 * (1 / 8 : ℝ)) ⊆
        parabolicCylinder (0 : Vec3) 0 1 := by
      rw [show 2 * (1 / 8 : ℝ) = 1 / 4 by norm_num]
      exact hparent
    have hQ1 : parabolicCylinder zc.1 zc.2 (1 / 8 : ℝ) ⊆
        parabolicCylinder (0 : Vec3) 0 1 :=
      (parabolicCylinder_mono (by norm_num) (by norm_num : (1 / 8 : ℝ) ≤ 2 * (1 / 8))).trans hQ2
    have hsubcl : closure (parabolicCylinder zc.1 zc.2 (1 / 8 : ℝ)) ⊆ spaceTimeSet Ω I :=
      (closure_mono hQ1).trans hdom
    have hrem := hCmaj hsol (show (0 : ℝ) < 1 / 8 by norm_num) hsubcl
    have hballsub : vec3Ball zc.1 ((1 / 8 : ℝ) / 2) ⊆ vec3Ball (0 : Vec3) (7 / 8) := by
      intro y hy
      have htri := vec3EuclideanNorm_add_le (y - zc.1) zc.1
      rw [sub_add_cancel] at htri
      have hnear : vec3EuclideanNorm (y - zc.1) < (1 / 8 : ℝ) / 2 := hy
      change vec3EuclideanNorm (y - 0) < 7 / 8
      rw [sub_zero]
      linarith only [htri, hx, hnear]
    have hJsub2 : Ioc (zc.2 - (1 / 8 : ℝ) ^ 2) zc.2 ⊆ I := by
      intro t ht
      have hmem : ((zc.1, t) : ParabolicPoint) ∈ parabolicCylinder zc.1 zc.2 (1 / 8 : ℝ) := by
        refine ⟨?_, ht⟩
        change vec3EuclideanNorm (zc.1 - zc.1) < 1 / 8
        rw [sub_self, vec3EuclideanNorm_zero]
        norm_num
      have h1 := (hQ1 hmem).2
      refine hIcc ⟨?_, h1.2⟩
      have hlt : (0 : ℝ) - 1 ^ 2 < t := h1.1
      linarith only [hlt]
    have hD2 : ∀ᵐ s ∂volume.restrict (Ioc (zc.2 - (1 / 8 : ℝ) ^ 2) zc.2), ∀ j : Fin 3,
        LocallyIntegrableOn (fun y => D (y, s) j) (vec3Ball zc.1 ((1 / 8 : ℝ) / 2)) volume ∧
        HasWeakPartialDerivOn (vec3Ball zc.1 ((1 / 8 : ℝ) / 2)) j
          (fun y => p (y, s)) (fun y => D (y, s) j) := by
      filter_upwards [ae_mono (Measure.restrict_mono hJsub2 le_rfl) hDae] with s hs
      intro j
      exact ⟨(hs j).1.mono_set hballsub,
        (hs j).2.1.restrict (isOpen_vec3Ball _ _) hballsub⟩
    have hmain := collar_gradient_time_mass_le bslotRemainderConstant ε hε hsol hdom hsmall
      (show (0 : ℝ) < 1 / 8 by norm_num) (by norm_num : 2 * (1 / 8 : ℝ) ≤ 1)
      (by simpa only [show (1 : ℝ) / 8 = 1 / 8 from rfl] using bslot_eighth_ball_volume_le_one)
      hQ2 hrem D hD2 i
    have hDm2 : AEStronglyMeasurable (fun w : ParabolicPoint => D w i)
        (volume.restrict (vec3Ball zc.1 ((1 / 8 : ℝ) / 2) ×ˢ
          Ioc (zc.2 - (1 / 8 : ℝ) ^ 2) zc.2)) := hDmi.aestronglyMeasurable
    have hsubcell : parabolicCylinder zc.1 zc.2 (1 / 16) ⊆
        vec3Ball zc.1 ((1 / 8 : ℝ) / 2) ×ˢ Ioc (zc.2 - (1 / 8 : ℝ) ^ 2) zc.2 := by
      refine Set.prod_mono ?_ ?_
      · rw [show (1 / 8 : ℝ) / 2 = 1 / 16 by norm_num]
      · exact Ioc_subset_Ioc
          (sub_le_sub_left (by norm_num : ((1 : ℝ) / 16) ^ 2 ≤ ((1 : ℝ) / 8) ^ 2) zc.2) le_rfl
    calc (∫⁻ w in parabolicCylinder zc.1 zc.2 (1 / 16),
          ENNReal.ofReal ‖D w i‖ ^ (6 / 5 : ℝ))
        ≤ ∫⁻ w in vec3Ball zc.1 ((1 / 8 : ℝ) / 2) ×ˢ Ioc (zc.2 - (1 / 8 : ℝ) ^ 2) zc.2,
            ENNReal.ofReal ‖D w i‖ ^ (6 / 5 : ℝ) := lintegral_mono_set hsubcell
      _ = ∫⁻ s in Ioc (zc.2 - (1 / 8 : ℝ) ^ 2) zc.2,
            eLpNorm (fun y => D (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
              (volume.restrict (vec3Ball zc.1 ((1 / 8 : ℝ) / 2))) ^ (6 / 5 : ℝ) :=
          (vector_time_slice_norm_power_eq (by norm_num) hDm2).symm
      _ ≤ _ := hmain
  refine (bslot_carrier_mass_le_cell_sum hR₁0 hR₁ _).trans ?_
  refine (ENNReal.tsum_le_tsum hcell).trans ?_
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
    bslotCarrierConstant, ← mul_assoc]
  refine mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
  exact Nat.cast_le.mpr originBSlotLatticeIndices_card_le

/-- The collar coefficient is finite at every positive radius. -/
theorem bslotCollarConstant_lt_top (C ρ : ℝ) : bslotCollarConstant C ρ < ⊤ := by
  have h1 : (3 * ENNReal.ofReal
      (czGradientComponentConstant rieszSecondWeakTypeConstant 1)) ^ (6 / 5 : ℝ) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)).ne
  have h2 : ((18 : ℝ≥0∞)) ^ (6 / 5 : ℝ) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num)).ne
  have hv : volume (vec3Ball (0 : Vec3) ρ) ≠ ⊤ :=
    CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top.ne
  have h3 : (18 * ENNReal.ofReal (cutoffGradientConstant / ρ) *
      volume (vec3Ball (0 : Vec3) ρ) ^ (1 / 6 : ℝ)) ^ (6 / 5 : ℝ) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hv).ne)).ne
  have h4 : (4 * volume (vec3Ball (0 : Vec3) ρ) ^ (13 / 30 : ℝ)) ^ (6 / 5 : ℝ) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hv).ne)).ne
  have h5 := (fixedRemainderMomentConstant_lt_top C ρ 0).ne
  have h6 : volume (vec3Ball (0 : Vec3) (ρ / 2)) ≠ ⊤ :=
    CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top.ne
  have h7 : volume (parabolicCylinder (0 : Vec3) 0 ρ) ≠ ⊤ :=
    CKN.Foundation.Parabolic.Integration.volume_parabolicCylinder_lt_top.ne
  rw [lt_top_iff_ne_top]
  unfold bslotCollarConstant
  refine ENNReal.mul_ne_top (by norm_num)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩)
  · refine ENNReal.mul_ne_top h1 (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩))
    · exact ENNReal.mul_ne_top h2
        (ENNReal.add_ne_top.mpr ⟨by norm_num, ENNReal.ofReal_ne_top⟩)
    · exact ENNReal.mul_ne_top h3
        (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, by norm_num⟩)
    · exact ENNReal.mul_ne_top h4
        (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, by norm_num⟩)
  · exact ENNReal.mul_ne_top h6
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, h5⟩)
  · exact ENNReal.mul_ne_top h1 (ENNReal.add_ne_top.mpr ⟨h7, by norm_num⟩)

/-- The whole-carrier coefficient is finite. -/
theorem bslotCarrierConstant_lt_top : bslotCarrierConstant < ⊤ := by
  rw [bslotCarrierConstant]
  rw [lt_top_iff_ne_top]
  exact ENNReal.mul_ne_top (by norm_num)
    (bslotCollarConstant_lt_top bslotRemainderConstant (1 / 8)).ne

/-- The threshold is the real value of the finite whole-carrier coefficient. -/
theorem ofReal_bslotThresholdB :
    ENNReal.ofReal bslotThresholdB = bslotCarrierConstant := by
  rw [bslotThresholdB, ENNReal.ofReal_toReal bslotCarrierConstant_lt_top.ne]

/-- **The B slot of `prop:bootstrap` at the two endgame instances.**  Above the
absolute threshold `bslotThresholdB`, the actual clipped `L^{6/5}` time mass of
any weak pressure gradient on the origin carrier is paid by the numerical
coefficient of `prop:bootstrap`, which carries no Morrey datum. -/
theorem theoremA_bslot_integral_instances :
    ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → bslotThresholdB ≤ C_CZ →
    ((τ = 25 / 3 ∧ R₀ = 11 / 16 ∧ R₁ = 43 / 64) ∨
      (τ = 25 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32)) →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε → KU < ⊤ → KD < ⊤ →
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      (∀ i, morreyNorm 3 τ
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
      (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
      ((∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
      ∀ Dp : ParabolicPoint → Vec3, Measurable Dp →
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i)) →
      ∀ i : Fin 3,
        (∫⁻ s in Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
          ((ENNReal.ofReal (|C_CZ| + 1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
            ENNReal.ofReal (max 1 ((2 * R₁ / (1 - R₁)) ^
              (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))))) := by
  intro q τ C_CZ R₀ R₁ ε KU KD _hq _hτ _hτu _hC hthr hinst hR₁ _hR₁R₀ _hR₀ hε _hKU _hKD
    Ω I u Du p f hsol hdom _hU _hD hsmall Dp _hmDp hw i
  have hR₁le : R₁ ≤ 11 / 16 := by
    rcases hinst with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;> norm_num
  refine le_trans (bslot_carrier_time_mass_le ε hε hsol hdom hsmall hR₁.le hR₁le Dp hw i) ?_
  exact mass_le_bslot_coefficient hε (le_of_eq ofReal_bslotThresholdB.symm) hthr

end CKN.Core.Step4
