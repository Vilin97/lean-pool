/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremAFullSumAssembly
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremACloser

/-! # Absolute thresholds for the clipped pressure-gradient slots

The two actual-integral estimates are used above one fixed absolute
Calderón–Zygmund threshold. Their spatial and temporal clipping is preserved.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- The actual clipped cell and time-mass bounds above a fixed threshold
produce the affine pressure-gradient estimate at every admissible constant. -/
theorem theoremA_hGA_of_integral_slots_threshold
    (Cstar : ℝ)
    (hAIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → Cstar ≤ C_CZ →
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
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))))
    (hBIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → Cstar ≤ C_CZ →
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
            (volume.restrict (vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤ ((ENNReal.ofReal (|C_CZ| + 1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
        ENNReal.ofReal (max 1 ((2 * R₁ / (1 - R₁)) ^
          (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))))) :
  ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    0 ≤ C_CZ → Cstar ≤ C_CZ →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
    KU < ∞ → KD < ∞ →
    oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD < ⊤ ∧
    ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∀ i, morreyNorm 3 τ
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
            (fun z => u z i)) ≤ KU) →
        (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
            (fun z => Du z i j)) ≤ KD) →
        ((∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
            Integrable (fun z => Dp z i)
              (volume.restrict (spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ)
              (min ((1 / τ + 8 / 25)⁻¹) q)
              ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
                (fun z => Dp z i)) ≤
            oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD) := by
  intro q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hthreshold hR₁ hR₁R₀ hR₀ hε hKU hKD
  refine ⟨oneSidedPressureGradientKPAffine_lt_top q' τ C_CZ R₀ R₁ ε KU KD hq' hKU hKD, ?_⟩
  intro Ω I u Du p f hsol hdom hU hD hsize
  obtain ⟨Dp, hm, hw, _hn⟩ := originClause_derivative_morrey_of_temporal_majorant
    fixed_remainder_temporal_majorant_of_sws hq' hτ hτu hR₁ hR₁R₀
    (by linarith only [hR₀]) hKU hKD hsol hdom hU hD
  let A := originKPAffineASlot q' C_CZ ε KU KD
  let B := ((ENNReal.ofReal (|C_CZ| + 1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
        ENNReal.ofReal (max 1 ((2 * R₁ / (1 - R₁)) ^
          (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q')))))
  let M : Fin 3 → Vec3 → ℝ → ℝ → ℝ≥0∞ := fun i x r s =>
    eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁))
  obtain ⟨htop, hint⟩ := origin_carrier_slice_time_obligations_of_sws
    hR₁ (hR₁R₀.trans hR₀) hsol hdom Dp hm hw
  have hgrowth := hAIntegral q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hthreshold hR₁ hR₁R₀ hR₀ hε hKU hKD
    hsol hdom hU hD hsize Dp hm hw
  have hglobal : ∀ i : Fin 3,
      (∫⁻ s in Ioc (-(R₁ ^ 2)) 0, M i (0 : Vec3) R₁ s ^ (6 / 5 : ℝ)) ≤ B := by
    simpa only [M, B, inter_self] using
      hBIntegral q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hthreshold hR₁ hR₁R₀ hR₀ hε hKU hKD
        hsol hdom hU hD hsize Dp hm hw
  have htop' : ∀ i : Fin 3, ∀ᵐ s ∂(volume.restrict I), M i (0 : Vec3) R₁ s ≠ ⊤ := by
    simpa only [M, inter_self] using htop
  have hint' : ∀ i : Fin 3, ∀ T : Set ℝ, IsCompact (closure T) → closure T ⊆ I →
      Integrable (fun s => (M i (0 : Vec3) R₁ s).toReal) (volume.restrict T) := by
    simpa only [M, inter_self] using hint
  obtain ⟨D, hAE, hInt, hpair, hcells⟩ :=
    theoremA_origin_cell_producer_of_clipped_data (A := A) (B := B)
      (KP := oneSidedPressureGradientKPAffine q' τ C_CZ R₀ R₁ ε KU KD)
      hq' hτ hR₁ hR₁R₀ hR₀ hsol hdom M
      ⟨(fun j x r => hw.mono (fun s hs =>
        ⟨fun y => Dp (y, s) j, (hs j).1, (hs j).2, le_rfl⟩)),
        htop', hint', hgrowth, hglobal⟩
      (theoremA_full_sum_le_KPAffine_of_coefficients q' τ C_CZ R₀ R₁ ε KU KD A B le_rfl le_rfl)
  exact ⟨D, hAE, hInt, hpair,
    fun i => pressure_gradient_morrey_bound (fun z r => hcells i z r)⟩


/-- The small-data conclusion from the two actual-integral slots.
The final absolute constant is the maximum of their common threshold and
`9 * max czP1OperatorConstant 0`, so the same constant also supplies the
singly centred Calderón–Zygmund estimate. The endgame uses `C_CZ = Cstar`
and `C₁₂_p1 = Cstar * 9 * sobolevPoincareL6Constant.toReal`. -/
theorem epsilonRegularityL3_of_threshold_slots
    (Cslot : ℝ) (hCslot : 0 ≤ Cslot)
    (hAIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → Cslot ≤ C_CZ →
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
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))))
    (hBIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → Cslot ≤ C_CZ →
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
            (volume.restrict (vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤ ((ENNReal.ofReal (|C_CZ| + 1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
        ENNReal.ofReal (max 1 ((2 * R₁ / (1 - R₁)) ^
          (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))))))
    (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
              ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z := by
  let Cstar : ℝ := max Cslot (9 * max czP1OperatorConstant 0)
  have hfinal : 0 ≤ Cstar := hCslot.trans (le_max_left _ _)
  apply epsilonRegularityL3_closer_of_pending_inputs q
    (Cstar * 9 * sobolevPoincareL6Constant.toReal) Cstar hq hfinal
  · apply theoremA_hCZ_p1_of_slice_bounds q
      (Cstar * 9 * sobolevPoincareL6Constant.toReal)
      (9 * max czP1OperatorConstant 0)
      (mul_nonneg (by norm_num) (le_max_right _ _))
    · calc
        _ ≤ Cstar * (9 * sobolevPoincareL6Constant.toReal) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ = _ := by ring
    · intro Ω I u Du p f hsol z ρ hρ hsub
      exact theoremB_pressureP1_slice_of_sws (max czP1OperatorConstant 0)
        (le_max_right _ _) (le_max_left _ _) hsol hρ hsub
  · intro q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu _hC hR₁ hR₁R₀ hR₀ hε hKU hKD
    obtain ⟨hKP, hpressure⟩ := theoremA_hGA_of_integral_slots_threshold Cslot
      hAIntegral hBIntegral q' τ Cstar R₀ R₁ ε KU KD hq' hτ hτu
      hfinal (le_max_left _ _) hR₁ hR₁R₀ hR₀ hε hKU hKD
    exact ⟨_, hKP, hpressure⟩

/-- Combine the independent absolute cell and time-mass thresholds with
the singly centred Calderón–Zygmund constant. Their maximum is nonnegative
without any additional hypothesis. Repeating the maximum with the
Calderón–Zygmund constant in the common-threshold theorem leaves it unchanged. -/
theorem epsilonRegularityL3_of_separate_threshold_slots
    (CA CB : ℝ)
    (hAIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → CA ≤ C_CZ →
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
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))))
    (hBIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → CB ≤ C_CZ →
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
            (volume.restrict (vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤ ((ENNReal.ofReal (|C_CZ| + 1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
        ENNReal.ofReal (max 1 ((2 * R₁ / (1 - R₁)) ^
          (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))))))
    (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
              ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z := by
  let Cstar : ℝ := max (max CA CB) (9 * max czP1OperatorConstant 0)
  have hnonneg : 0 ≤ Cstar :=
    (mul_nonneg (by norm_num) (le_max_right czP1OperatorConstant 0)).trans
      (le_max_right _ _)
  apply epsilonRegularityL3_of_threshold_slots Cstar hnonneg
  · intro q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hthreshold
    exact hAIntegral q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC
      ((le_max_left CA CB).trans ((le_max_left _ _).trans hthreshold))
  · intro q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hthreshold
    exact hBIntegral q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC
      ((le_max_right CA CB).trans ((le_max_left _ _).trans hthreshold))
  · exact hq

end CKN.Core.Endgame
