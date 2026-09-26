/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremAClosersInstances

/-! # Pressure-gradient estimates at the two exponent-radius triples

The proof of `thm:A` uses `lem:pressure-gradient-morrey` exactly twice: once
inside the bootstrap round `prop:bootstrap` at velocity exponent `τ = 25/3`,
and once inside `thm:endgame` at `τ = 25`. Each use fixes the two radii as
well, so only the triples `(25/3, 11/16, 43/64)` and `(25, 5/8, 19/32)` are
needed. The estimates in this module carry that restriction, together with a
lower bound on the Calderón-Zygmund constant so that a single constant
dominates every coefficient the two estimates require; enlarging that
constant weakens nothing.

`epsilonRegularityL3_of_instance_slots_q` is the proof of `thm:A` itself.
Its steps are, in order: the start lemma `lem:thmA-start` and Steps 1 and 2
(`theoremA_initial_uniform_of_displays`), the single bootstrap round of
`prop:bootstrap` and `cor:one-round`
(`exists_uniform_bootstrap_of_initial_pressure`), and `thm:endgame` on the
one-sided cylinder (`exists_uniform_halfCylinder_of_final_pressure`), with
all sources split at `t = 0` as Step 3 requires. The same composition is
written, with an unrestricted pressure-gradient hypothesis, in
`CKN.Core.Endgame.epsilonRegularityL3_closer_of_pending_inputs`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- The two actual-integral slots at the prescribed exponent/radius triples
produce the affine pressure-gradient estimate at those same triples. -/
theorem theoremA_hGA_of_integral_slots_instances_q
    (Cstar : ℝ → ℝ)
    (hAIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → Cstar q ≤ C_CZ →
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
      ∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        ∀ r : ℝ, 0 < r → r ≤ R₁ →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
          originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))))
    (hBIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → Cstar q ≤ C_CZ →
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
            (volume.restrict (vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤ ((ENNReal.ofReal (|C_CZ| +
              1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
        ENNReal.ofReal (max 1 ((2 * R₁ / (1 - R₁)) ^
          (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))))) :
  ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    0 ≤ C_CZ → Cstar q ≤ C_CZ →
    ((τ = 25 / 3 ∧ R₀ = 11 / 16 ∧ R₁ = 43 / 64) ∨
      (τ = 25 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32)) →
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
  intro q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hthreshold hinstances hR₁ hR₁R₀ hR₀ hε hKU hKD
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
  have hgrowth := hAIntegral q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hthreshold hinstances hR₁ hR₁R₀
    hR₀ hε hKU hKD
    hsol hdom hU hD hsize Dp hm hw
  have hglobal : ∀ i : Fin 3,
      (∫⁻ s in Ioc (-(R₁ ^ 2)) 0, M i (0 : Vec3) R₁ s ^ (6 / 5 : ℝ)) ≤ B := by
    simpa only [M, B, inter_self] using
      hBIntegral q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hthreshold hinstances hR₁ hR₁R₀ hR₀ hε hKU
        hKD
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


/-- The small-data conclusion from the actual-integral slots at the
two triples used by the bootstrap and final pressure steps. The coefficient depending only on the
  force exponent also absorbs the singly centred Calderón–Zygmund constant. -/
theorem epsilonRegularityL3_of_instance_slots_q
    (Cslot : ℝ → ℝ) (hCslot : ∀ q, 0 ≤ Cslot q)
    (hAIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → Cslot q ≤ C_CZ →
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
      ∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        ∀ r : ℝ, 0 < r → r ≤ R₁ →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
          originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))))
    (hBIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → Cslot q ≤ C_CZ →
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
            (volume.restrict (vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤ ((ENNReal.ofReal (|C_CZ| +
              1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
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
  let Cstar : ℝ → ℝ := fun q => max (Cslot q) (9 * max czP1OperatorConstant 0)
  have hCstar : 0 ≤ Cstar q := (hCslot q).trans (le_max_left _ _)
  let C₁₂_p1 := Cstar q * 9 * sobolevPoincareL6Constant.toReal
  have hconst : (9 * max czP1OperatorConstant 0) *
      (9 * sobolevPoincareL6Constant.toReal) ≤ C₁₂_p1 := by
    calc
      _ ≤ Cstar q * (9 * sobolevPoincareL6Constant.toReal) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = _ := by dsimp only [C₁₂_p1]; ring
  have hCZ_p1 := theoremA_hCZ_p1_of_slice_bounds q C₁₂_p1
    (9 * max czP1OperatorConstant 0)
    (mul_nonneg (by norm_num) (le_max_right _ _)) hconst
    (fun Ω I u Du p f hsol z ρ hρ hsub =>
      theoremB_pressureP1_slice_of_sws (max czP1OperatorConstant 0)
        (le_max_right _ _) (le_max_left _ _) hsol hρ hsub)
  have hGA := theoremA_hGA_of_integral_slots_instances_q Cslot hAIntegral hBIntegral
  let C₃₂ := theoremALin34Constant q
  have hC₃₂ : 0 ≤ C₃₂ := theoremALin34Constant_nonneg q hq
  obtain ⟨C₂₇, C₂₈, hC₂₇, hC₂₈, hThetaDecay⟩ :=
    thetaDecay_T_of_inputs q C₁₂_p1 hCZ_p1
  obtain ⟨ε₀, KUinitial, KD, hε₀, hKUinitial, hKD, hinitial⟩ :=
    theoremA_initial_uniform_of_displays q startGammaConstant (caccioppoliC₂₆ q)
      C₂₇ C₂₈ C₃₂ hq hC₂₇ hC₂₈ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hC₃₂
      (fun hsol => caccioppoli_gamma_display_fixed hsol) (theoremA_hLin34_of_sws q)
      (fun {Ω I u Du p f} hsol => hThetaDecay Ω I u Du p f hsol)
  obtain ⟨KU, hKU, hbootstrap⟩ := exists_uniform_bootstrap_of_initial_pressure
    q ε₀ KUinitial KD hq hKUinitial hKD
    (by
      obtain ⟨hKP, hpressure⟩ := hGA q (25 / 3) (Cstar q) (11 / 16) (43 / 64)
        ε₀ KUinitial KD hq (by norm_num) (by norm_num) hCstar (le_max_left _ _)
        (Or.inl ⟨rfl, rfl, rfl⟩)
        (by norm_num) (by norm_num) (by norm_num) hε₀.le hKUinitial hKD
      refine ⟨_, hKP, ?_⟩
      intro Ω I u f Du p hsol hdom hsmall hU hD
      obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hpressure hsol hdom hU hD hsmall
      refine ⟨Dp, hAE, hInt, hweak, ?_⟩
      intro i
      have hmin : min (((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹) q = 25 / 11 := by
        rw [show ((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹ = 25 / 11 by norm_num]
        exact min_eq_left (by linarith only [hq])
      simpa only [hmin] using hN i)
    (fun _ _ _ _ _ _ _ hsol _ _ _ hφ hbox hsupp hInt hweak =>
      localized_gradient_slot_duhamel_of_sws hsol hφ hbox hsupp hInt hweak)
  obtain ⟨C₄, hC₄, hfinal⟩ := exists_uniform_halfCylinder_of_final_pressure
    q ε₀ KU KUinitial KD hq hε₀.le hKU hKUinitial hKD
    (by
      obtain ⟨hKP, hpressure⟩ := hGA q 25 (Cstar q) (5 / 8) (19 / 32)
        ε₀ KU KD hq (by norm_num) (by norm_num) hCstar (le_max_left _ _)
        (Or.inr ⟨rfl, rfl, rfl⟩)
        (by norm_num) (by norm_num) (by norm_num) hε₀.le hKU hKD
      refine ⟨_, hKP, ?_⟩
      intro Ω I u f Du p hsol hdom hsmall hU hD
      obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hpressure hsol hdom hU hD hsmall
      refine ⟨Dp, hAE, hInt, hweak, ?_⟩
      intro i
      have hexp : ((1 / (25 : ℝ)) + 8 / 25)⁻¹ = 25 / 9 := by norm_num
      simpa only [hexp, min_comm] using hN i)
    (fun _ _ _ _ _ _ _ hsol _ _ _ hφ hbox hsupp hInt hweak =>
      localized_gradient_slot_duhamel_of_sws hsol hφ hbox hsupp hInt hweak)
  refine ⟨ε₀, stepGamma₀ q, C₄, hε₀, stepGamma₀_pos hq,
    (stepGamma₀_le_fifth q).trans (by norm_num), hC₄, ?_⟩
  intro Ω I u Du p f hsol hdom hsmall
  obtain ⟨hUinitial, hD⟩ := hinitial hsol hdom hsmall
  have hU := hbootstrap Ω I u f Du p hsol hdom hUinitial hD hsmall
  have hsub : parabolicCylinder (0 : Vec3) 0 (5 / 8) ⊆
      parabolicCylinder (0 : Vec3) 0 (11 / 16) :=
    parabolicCylinder_mono (by norm_num) (by norm_num)
  apply hfinal Ω I u f Du p hsol hdom hU
  · intro i
    exact (morreyNorm_indicator_mono_set (by norm_num : (0 : ℝ) ≤ 3)
      hsub (fun z => u z i)).trans (hUinitial i)
  · intro i j
    exact (morreyNorm_indicator_mono_set (by norm_num : (0 : ℝ) ≤ 2)
      hsub (fun z => Du z i j)).trans (hD i j)
  · exact hsmall

/-- Combine the independent cell and time-mass threshold functions with
the singly centred Calderón–Zygmund constant. Their maximum is nonnegative
without any additional hypothesis. Repeating the maximum with the
Calderón–Zygmund constant in the common-threshold theorem leaves it unchanged. -/
theorem epsilonRegularityL3_of_separate_instance_slots_q
    (CA CB : ℝ → ℝ)
    (hAIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → CA q ≤ C_CZ →
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
      ∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        ∀ r : ℝ, 0 < r → r ≤ R₁ →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
          originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))))
    (hBIntegral :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → CB q ≤ C_CZ →
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
            (volume.restrict (vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤ ((ENNReal.ofReal (|C_CZ| +
              1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
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
  let Cstar : ℝ → ℝ := fun q => max (max (CA q) (CB q)) (9 * max czP1OperatorConstant 0)
  have hnonneg : ∀ q, 0 ≤ Cstar q := fun _ =>
    (mul_nonneg (by norm_num) (le_max_right czP1OperatorConstant 0)).trans
      (le_max_right _ _)
  apply epsilonRegularityL3_of_instance_slots_q Cstar hnonneg
  · intro q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hthreshold
    exact hAIntegral q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC
      ((le_max_left (CA q') (CB q')).trans ((le_max_left _ _).trans hthreshold))
  · intro q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hthreshold
    exact hBIntegral q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC
      ((le_max_right (CA q') (CB q')).trans ((le_max_left _ _).trans hthreshold))
  · exact hq

end CKN.Core.Endgame
