/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPAffineSlot
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPComparison
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremABudgetBridge
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRemainderMajorant
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseDerivativeShared
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTranslatedSlice

/-! # Full-sum comparison from bounds on its two coefficients

The coefficients here are the sum of the actual carrier Morrey norms to
the `6/5` power and its radius-weighted multiple. They are distinct from
bounds on individual clipped cell integrals or the actual total time mass.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Core.Step4
noncomputable section
namespace CKN.Core.Endgame

/-- Bounds on the two coefficients of the one-sided expression imply its
comparison with the enlarged numerical constant. -/
theorem theoremA_full_sum_le_KPAffine_of_coefficients
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD A B : ℝ≥0∞)
    (hA : A ≤ originKPAffineASlot q C_CZ ε KU KD)
    (hB : B ≤ ((ENNReal.ofReal (|C_CZ| + 1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
        ENNReal.ofReal (max 1 ((2 * R₁ / (1 - R₁)) ^
          (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))))) :
    oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q) R₁ A B ≤
      oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD := by
  exact oneSidedMorreyBound_mono (by norm_num) hA hB


/-- Bounds on actual clipped cell integrals and actual total time mass give
an AE pressure-gradient producer directly, without replacing those two
coefficients by powers of its Morrey norms. -/
theorem theoremA_hGA_of_integral_slots
    (hAIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ →
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
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ →
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
    0 ≤ C_CZ →
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
  intro q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hR₁ hR₁R₀ hR₀ hε hKU hKD
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
  have hgrowth := hAIntegral q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hR₁ hR₁R₀ hR₀ hε hKU hKD
    hsol hdom hU hD hsize Dp hm hw
  have hglobal : ∀ i : Fin 3,
      (∫⁻ s in Ioc (-(R₁ ^ 2)) 0, M i (0 : Vec3) R₁ s ^ (6 / 5 : ℝ)) ≤ B := by
    simpa only [M, B, inter_self] using
      hBIntegral q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hR₁ hR₁R₀ hR₀ hε hKU hKD
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





end CKN.Core.Endgame
