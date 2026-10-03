/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotLargeCellsGeometry
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeIntegrals

/-! # From margin cells to all cells in the origin A slot of `prop:bootstrap`

The clipped cell estimate of `prop:bootstrap` for the spatial pressure gradient
is proved directly only on *margin cells*: cells whose centre lies in the
closure of the origin carrier of radius `R₁` and whose radius is at most
`(1 - R₁)/4`.  This file removes both restrictions, at the cost of one absolute
factor on the Calderón–Zygmund constant.

The clipped time integral of the `6/5` power of the spatial `L^{6/5}` slice
norm is the space-time mass of `|∂ᵢp|^{6/5}` over the cell clipped to the
carrier, so it is monotone in the cell.  Two comparisons then suffice.

* A cell of radius at most `(1 - R₁)/8` clipped to the carrier is contained in
  a margin cell of twice the radius centred in the carrier.  Doubling the
  radius costs the factor `2^θ ≤ 8`, since the growth exponent `θ` of
  `prop:bootstrap` is at most `71/25`.
* A cell of radius larger than `(1 - R₁)/8` is bounded by the whole clipped
  carrier mass, and the carrier is covered by `197³ · 4611` margin cells of
  radius exactly `(1 - R₁)/8`, each of which is smaller than the given radius,
  so the growth factor only improves.

Both costs are absolute, and the affine slot `originKPAffineASlot` is
superhomogeneous in `|C_CZ| + 1`, so both are absorbed by requiring
`C_CZ ≥ originASlotLargeCellThreshold Cbase`.  Nothing else is assumed: the
centre of the given cell is arbitrary and its radius is arbitrary.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-- The Calderón–Zygmund threshold at which every clipped cell of the origin
carrier inherits the margin-cell A slot: the number of margin cells used to
cover the carrier, times the constant of the margin-cell estimate. -/
def originASlotLargeCellThreshold (Cbase : ℝ) : ℝ :=
  35252814903 * (|Cbase| + 1)

/-- The threshold multiplies the affine slot by the cover count. -/
theorem originKPAffineASlot_cover_count_mul_le {q ε Cbase C_CZ : ℝ} {KU KD : ℝ≥0∞}
    (hthreshold : originASlotLargeCellThreshold Cbase ≤ C_CZ) :
    (35252814903 : ℝ≥0∞) * originKPAffineASlot q Cbase ε KU KD ≤
      originKPAffineASlot q C_CZ ε KU KD := by
  refine originKPAffineASlot_const_mul_le (by norm_num) ?_
  have hcast : (35252814903 : ℝ≥0∞) = ENNReal.ofReal (35252814903 : ℝ) := by
    rw [ENNReal.ofReal]
    norm_num
  rw [hcast, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have habs : C_CZ ≤ |C_CZ| := le_abs_self C_CZ
  have hth : 35252814903 * (|Cbase| + 1) ≤ C_CZ := hthreshold
  linarith only [habs, hth]

/-- **Margin cells control every cell.**  Given the clipped A-slot estimate of
`prop:bootstrap` on margin cells at the constant `Cbase`, every clipped cell —
any centre, any positive radius — obeys the same estimate at any constant above
`originASlotLargeCellThreshold Cbase`. -/
theorem originASlot_clipped_cell_of_margin_cells
    {q τ R₁ ε Cbase C_CZ : ℝ} {KU KD : ℝ≥0∞}
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτhi : τ ≤ 25)
    (hR₁ : 0 < R₁) (hR₁lt : R₁ < 3 / 4)
    (hthreshold : originASlotLargeCellThreshold Cbase ≤ C_CZ)
    {Dp : ParabolicPoint → Vec3} (hDp : Measurable Dp) (i : Fin 3)
    (hmargin : ∀ w ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ (1 - R₁) / 4 →
      (∫⁻ s in Ioc (w.2 - ρ ^ 2) w.2 ∩ Ioc (-(R₁ ^ 2)) 0,
        eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball w.1 ρ ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
        originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
          (ρ ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))))
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
      eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
      originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
        (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
  have hS : MeasurableSet (parabolicCylinder (0 : Vec3) 0 R₁) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  have hmeas : Measurable (fun w : ParabolicPoint => Dp w i) :=
    (measurable_pi_apply i).comp hDp
  have key : ∀ (x : Vec3) (t ρ : ℝ),
      (∫⁻ s in Ioc (t - ρ ^ 2) t ∩ Ioc (-(R₁ ^ 2)) 0,
        eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball x ρ ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) =
      ∫⁻ w in parabolicCylinder x t ρ ∩ parabolicCylinder (0 : Vec3) 0 R₁,
        ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) := by
    intro x t ρ
    rw [origin_clipped_slice_norm_power_eq (P := (6 / 5 : ℝ)) (by norm_num) R₁
      hmeas.aemeasurable x t ρ]
    exact cylinderPowerIntegral_indicator (by norm_num) hS (fun w => Dp w i) (x, t) ρ
  have hslot : (35252814903 : ℝ≥0∞) * originKPAffineASlot q Cbase ε KU KD ≤
      originKPAffineASlot q C_CZ ε KU KD :=
    originKPAffineASlot_cover_count_mul_le hthreshold
  rw [key z.1 z.2 r]
  rcases le_or_gt r ((1 - R₁) / 8) with hsplit | hsplit
  · -- A small cell is doubled onto a margin cell centred in the carrier.
    have hshift := originASlotShiftedCentre_mem hR₁ z r
    have hsub : parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁ ⊆
        parabolicCylinder (originASlotShiftedCentre R₁ z r).1
          (originASlotShiftedCentre R₁ z r).2 (2 * r) ∩
          parabolicCylinder (0 : Vec3) 0 R₁ :=
      Set.subset_inter (originASlotShiftedCentre_subset hr z) inter_subset_right
    calc
      (∫⁻ w in parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
          ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ))
          ≤ ∫⁻ w in parabolicCylinder (originASlotShiftedCentre R₁ z r).1
              (originASlotShiftedCentre R₁ z r).2 (2 * r) ∩
              parabolicCylinder (0 : Vec3) 0 R₁,
              ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) := lintegral_mono_set hsub
      _ ≤ originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
            ((2 * r) ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
          rw [← key (originASlotShiftedCentre R₁ z r).1
            (originASlotShiftedCentre R₁ z r).2 (2 * r)]
          exact hmargin (originASlotShiftedCentre R₁ z r) (subset_closure hshift) (2 * r)
            (by linarith only [hr]) (by linarith only [hsplit])
      _ ≤ originKPAffineASlot q Cbase ε KU KD *
            (8 * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) :=
          mul_le_mul' le_rfl (originASlot_ofReal_two_mul_rpow_le hq hτ hτhi hr)
      _ = (8 : ℝ≥0∞) * originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
          ring
      _ ≤ (35252814903 : ℝ≥0∞) * originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) :=
          mul_le_mul' (mul_le_mul' (by norm_num) le_rfl) le_rfl
      _ ≤ originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) :=
          mul_le_mul' hslot le_rfl
  · -- A large cell is bounded by the whole clipped carrier mass.
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (1 - R₁) / 16 := ⟨_, rfl⟩
    have hapos : 0 < a := by rw [ha]; linarith only [hR₁lt]
    have hmarginfit : 2 * a ≤ (1 - R₁) / 4 := by rw [ha]; linarith only [hR₁lt]
    have hcellsmall : 2 * a ≤ r := by rw [ha]; linarith only [hsplit]
    set V : {k : (Fin 3 → ℤ) × ℤ // k ∈ originASlotCoverBox} → Set ParabolicPoint :=
      fun k => parabolicCylinder
        (originASlotShiftedCentre R₁ (originLatticeCentre a k.1) a).1
        (originASlotShiftedCentre R₁ (originLatticeCentre a k.1) a).2 (2 * a) ∩
        parabolicCylinder (0 : Vec3) 0 R₁ with hV
    have hcover : parabolicCylinder (0 : Vec3) 0 R₁ ⊆ ⋃ k, V k := by
      intro w hw
      obtain ⟨k, hk, hwk⟩ :=
        Set.mem_iUnion₂.mp (originASlot_carrier_subset_shifted_cells hR₁ hR₁lt ha hw)
      exact Set.mem_iUnion.mpr ⟨⟨k, Finset.mem_coe.mp hk⟩, hwk, hw⟩
    have hterm : ∀ k : {k : (Fin 3 → ℤ) × ℤ // k ∈ originASlotCoverBox},
        (∫⁻ w in V k, ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
          originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
      intro k
      have hcentre := originASlotShiftedCentre_mem hR₁ (originLatticeCentre a k.1) a
      calc
        (∫⁻ w in V k, ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ))
            ≤ originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
                ((2 * a) ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
              rw [hV, ← key
                (originASlotShiftedCentre R₁ (originLatticeCentre a k.1) a).1
                (originASlotShiftedCentre R₁ (originLatticeCentre a k.1) a).2 (2 * a)]
              exact hmargin _ (subset_closure hcentre) (2 * a)
                (by linarith only [hapos]) hmarginfit
        _ ≤ originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) :=
            mul_le_mul' le_rfl (originASlot_ofReal_rpow_mono hq hτ
              (by linarith only [hapos]) hcellsmall)
    calc
      (∫⁻ w in parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
          ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ))
          ≤ ∫⁻ w in parabolicCylinder (0 : Vec3) 0 R₁,
              ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) :=
            lintegral_mono_set inter_subset_right
      _ ≤ ∫⁻ w in ⋃ k, V k, ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) :=
            lintegral_mono_set hcover
      _ ≤ ∑' k, ∫⁻ w in V k, ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) :=
            lintegral_iUnion_le _ _
      _ = ∑ k : {k : (Fin 3 → ℤ) × ℤ // k ∈ originASlotCoverBox},
              ∫⁻ w in V k, ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) := tsum_fintype _
      _ ≤ (Finset.univ : Finset {k : (Fin 3 → ℤ) × ℤ // k ∈ originASlotCoverBox}).card •
            (originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) :=
            Finset.sum_le_card_nsmul _ _ _ (fun k _ => hterm k)
      _ = (35252814903 : ℝ≥0∞) * (originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) := by
            rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_coe, originASlotCoverBox_card]
            norm_num
      _ = (35252814903 : ℝ≥0∞) * originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
            rw [mul_assoc]
      _ ≤ originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) :=
            mul_le_mul' hslot le_rfl

/-- **The A slot of `prop:bootstrap` above the threshold.**  The clipped
component-cell estimate for every centre in `Q(3/4)` and every radius
`0 < r ≤ R₁` follows from its margin-cell restriction — centres in the closure
of the carrier, radii at most `(1 - R₁)/4` — once the Calderón–Zygmund constant
is at least `originASlotLargeCellThreshold Cbase`.  No hypothesis on the
solution beyond those of the margin-cell estimate is used. -/
theorem theoremA_aSlot_integral_of_margin_cells (Cbase : ℝ) (hCbase : 0 ≤ Cbase)
    (hmargin :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → Cbase ≤ C_CZ →
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
      ∀ i : Fin 3, ∀ z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁),
        ∀ r : ℝ, 0 < r → r ≤ (1 - R₁) / 4 →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
          originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ →
    originASlotLargeCellThreshold Cbase ≤ C_CZ →
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
      ∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        ∀ r : ℝ, 0 < r → r ≤ R₁ →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
          originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
  intro q τ C_CZ R₀ R₁ ε KU KD hq hτ hτhi hC hthreshold hR₁ hR₁R₀ hR₀ hε hKU hKD Ω I u Du p f
    hsol hdom hU hDu hsize Dp hDp hweak i z _hz r hr _hrR₁
  exact originASlot_clipped_cell_of_margin_cells hq hτ hτhi hR₁
    (lt_trans hR₁R₀ hR₀) hthreshold hDp i
    (fun w hw ρ hρ hρle =>
      hmargin q τ Cbase R₀ R₁ ε KU KD hq hτ hτhi hCbase le_rfl hR₁ hR₁R₀ hR₀ hε hKU hKD
        hsol hdom hU hDu hsize Dp hDp hweak i w hw ρ hρ hρle)
    z hr

end CKN.Core.Step4
