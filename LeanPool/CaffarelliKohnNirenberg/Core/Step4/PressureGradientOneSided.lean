/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSourceMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ForceSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMorrey
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Cylinders
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersSphere
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-!
# Pressure Gradient One Sided

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section

namespace CKN.Core.Step4

/-! The slice interface used by the one-sided pressure estimate.  The outer
ball is the region on which the slice weak derivative is supplied; the norm
bound is recorded on the inner half-ball exactly as in display (3.5). -/

def pressureGradientOneScaleAt
    (C_CZ R₀ : ℝ) (V : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) (t : ℝ) : Prop :=
  ∀ k : Fin 3, ∃ g : Vec3 → ℝ,
    LocallyIntegrableOn g (vec3Ball 0 R₀) volume ∧
    HasWeakPartialDerivOn (vec3Ball 0 R₀) k
      (fun y => p (y, t)) g ∧
    ∀ x : Vec3, ∀ ρ : ℝ,
      0 < ρ → vec3Ball x (4 * ρ) ⊆ vec3Ball 0 R₀ →
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball x (ρ / 2))) ≤
        ENNReal.ofReal C_CZ *
          (eLpNorm (fun y => V (y, t)) (ENNReal.ofReal (6 / 5 : ℝ))
              (volume.restrict (vec3Ball x (3 * ρ / 2))) +
            ENNReal.ofReal (ρ ^ (-1 / 2 : ℝ)) *
              eLpNorm (fun y => p (y, t)) (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (vec3Ball x ρ)))

def pressureGradientOneScaleBound
    {J : Set ℝ} (C_CZ R₀ : ℝ)
    (V : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) : Prop :=
  ∀ᵐ t ∂(volume.restrict J),
    pressureGradientOneScaleAt C_CZ R₀ V p t

/-! A slice bound gives product integrability once its time majorant is
integrable.  The spatial finite-measure factor is retained explicitly; this
is the factor supplied by the bounded inner ball in the application. -/

theorem pressure_gradient_integrable_on_of_slice_bound
    {B : Set Vec3} {J : Set ℝ} {f : ParabolicPoint → ℝ}
    {K : ℝ → ℝ≥0∞} [IsFiniteMeasure (volume.restrict B)]
    (hfmeas : AEStronglyMeasurable f
      ((volume.restrict B).prod (volume.restrict J)))
    (hslice : ∀ᵐ t ∂(volume.restrict J),
      eLpNorm (fun x => f (x, t)) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B) ≤ K t)
    (hKtop : ∀ᵐ t ∂(volume.restrict J), K t ≠ ∞)
    (hKint : Integrable (fun t => (K t).toReal) (volume.restrict J)) :
    Integrable f ((volume.restrict B).prod (volume.restrict J)) := by
  let p : ℝ≥0∞ := ENNReal.ofReal (6 / 5 : ℝ)
  have hp1 : (1 : ℝ≥0∞) ≤ p := by
    dsimp [p]
    norm_num
  have hptop : p ≠ ∞ := by
    dsimp [p]
    norm_num
  have hpexp : 0 ≤ 1 / (1 : ℝ) - 1 / p.toReal := by
    dsimp [p]
    norm_num
  apply (integrable_prod_iff' hfmeas).2
  constructor
  · filter_upwards [hslice, hKtop] with t ht htop
    have hmem : MemLp (fun x => f (x, t)) p (volume.restrict B) := by
      rw [memLp_iff]
      exact ht.trans_lt (lt_top_iff_ne_top.2 htop)
    exact (hmem.mono_exponent hp1).integrable le_rfl
  · have hmeas : AEStronglyMeasurable
        (fun t => ∫ x, ‖f (x, t)‖ ∂(volume.restrict B)) (volume.restrict J) :=
      hfmeas.prod_swap.norm.integral_prod_right'
    let C : ℝ :=
      ((volume.restrict B) Set.univ ^ (1 / (1 : ℝ) - 1 / p.toReal)).toReal
    have hmajor : Integrable (fun t => C * (K t).toReal)
        (volume.restrict J) := hKint.const_mul C
    apply hmajor.mono' hmeas
    filter_upwards [hslice, hKtop] with t ht htop
    have hmem : MemLp (fun x => f (x, t)) p (volume.restrict B) := by
      rw [memLp_iff]
      exact ht.trans_lt (lt_top_iff_ne_top.2 htop)
    have hmem1 := hmem.mono_exponent hp1
    have hnorm := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1
      hmem.aestronglyMeasurable
    have hright : K t *
        (volume.restrict B) Set.univ ^ (1 / (1 : ℝ) - 1 / p.toReal) ≠ ∞ :=
      ENNReal.mul_ne_top htop
        (ENNReal.rpow_ne_top_of_nonneg hpexp (measure_ne_top _ _))
    have hnorm' := hnorm.trans
      (mul_le_mul_of_nonneg_right ht (by positivity :
        0 ≤ (volume.restrict B) Set.univ ^
          (1 / ENNReal.toReal 1 - 1 / p.toReal)))
    have hnorm'' : eLpNorm (fun x => f (x, t)) 1 (volume.restrict B) ≤
        K t * (volume.restrict B) Set.univ ^ (1 / (1 : ℝ) - 1 / p.toReal) := by
      simpa only [ENNReal.toReal_one] using hnorm'
    have hto := (ENNReal.toReal_le_toReal hmem1.eLpNorm_lt_top.ne hright).2 hnorm''
    rw [integral_norm_eq_lintegral_enorm hmem.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm hmem.aestronglyMeasurable]
    simpa [C, ENNReal.toReal_mul, mul_comm] using hto

theorem pressure_gradient_integrable_on_of_selected_bounds
    {B : Set Vec3} {J : Set ℝ} {Dp : ParabolicPoint → Vec3}
    {K : Fin 3 → ℝ → ℝ≥0∞} [IsFiniteMeasure (volume.restrict B)]
    (hDpmeas : ∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
      ((volume.restrict B).prod (volume.restrict J)))
    (hbound : ∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict J),
      eLpNorm (fun x => Dp (x, t) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B) ≤ K i t)
    (hKtop : ∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict J), K i t ≠ ∞)
    (hKint : ∀ i : Fin 3,
      Integrable (fun t => (K i t).toReal) (volume.restrict J)) :
    ∀ i : Fin 3, Integrable (fun z => Dp z i)
      ((volume.restrict B).prod (volume.restrict J)) := by
  intro i
  exact pressure_gradient_integrable_on_of_slice_bound
    (hDpmeas i).aestronglyMeasurable (hbound i) (hKtop i) (hKint i)

/-! The pressure factor needed by the selector is locally integrable on every
compact solution box.  The spatial set may be any subset of the box, which
is the form used after the fixed-radius cutoff is intersected with a local
box. -/

theorem pressure_integrable_on_of_suitable_local_box
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {U : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I U J)
    {B : Set Vec3} (hB : B ⊆ U) :
    IntegrableOn p (B ×ˢ J) volume := by
  have hdata := hsol.2.2.2.2.2.1 U J hbox
  obtain ⟨_hu, _hDu, _hpmeas, _hfmeas, _hess, _henergy, hpLp, _hfLp, _hgrad⟩ := hdata
  let _ : IsFiniteMeasure (volume.restrict (spaceTimeSet U J)) :=
    CKN.Core.Step3.local_box_isFiniteMeasure hbox.2.1 hbox.2.2.2.2.1
  have hpInt : Integrable p (volume.restrict (spaceTimeSet U J)) :=
    hpLp.integrable (by norm_num)
  apply hpInt.mono_measure
  apply Measure.restrict_mono
  · exact Set.prod_mono hB subset_rfl
  · exact le_rfl

/-! The quantitative target is recorded with constants before the fields.  The
local-integrability conjunct is the interface used by localized equation
representations on arbitrary sub-boxes. -/

def oneSidedPressureGradientKP
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞) : ℝ≥0∞ :=
  let κ := min ((1 / τ + 8 / 25)⁻¹) q
  let c := ENNReal.ofReal (|C_CZ| + 1)
  let A := c * (3 * (3 * KU * KD + forceSourceMorreyBound q ε))
  let B := c * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)
  oneSidedMorreyBound (6 / 5) κ R₁ A B

theorem oneSidedPressureGradientKP_lt_top
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (_ : 25 / 3 ≤ τ) (_ : τ ≤ 25)
    (_ : 0 ≤ C_CZ) (_ : 0 < R₁) (_ : R₁ < R₀)
    (_ : R₀ < 3 / 4) (_ : 0 ≤ ε)
    (hKU : KU < ⊤) (hKD : KD < ⊤) :
    oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD < ⊤ := by
  have hforce : forceSourceMorreyBound q ε < ⊤ :=
    forceSourceMorreyBound_lt_top q ε hq
  have hc : ENNReal.ofReal (|C_CZ| + 1) < ⊤ := ENNReal.ofReal_lt_top
  have hA :
      (ENNReal.ofReal (|C_CZ| + 1)) *
          (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) < ⊤ := by
    apply ENNReal.mul_lt_top hc
    apply ENNReal.mul_lt_top (by simp)
    apply ENNReal.add_lt_top.mpr
    constructor
    · apply ENNReal.mul_lt_top
      · exact ENNReal.mul_lt_top (by simp) hKU
      · exact hKD
    · exact hforce
  have hB :
      (ENNReal.ofReal (|C_CZ| + 1)) *
          ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) < ⊤ :=
    ENNReal.mul_lt_top hc ENNReal.ofReal_lt_top
  dsimp [oneSidedPressureGradientKP]
  apply oneSidedMorreyBound_lt_top (by norm_num) hA hB

def oneSidedPressureGradientQuantitative : Prop :=
  ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    0 ≤ C_CZ →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
    KU < ∞ → KD < ∞ →
    oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD < ⊤ ∧
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
            oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD)

/-! This wrapper exposes the numerical call used by Theorem A.  It
retains the pressure field on the returned support and normalizes only the
Morrey exponent arithmetic. -/

theorem initial_pressure_gradient_of_quantitative
    (hGA : oneSidedPressureGradientQuantitative)
    (q C_CZ ε₀ : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hC : 0 ≤ C_CZ) (hε₀ : 0 ≤ ε₀)
    (hKU : KU < ⊤) (hKD : KD < ⊤) :
    ∃ KP : ℝ≥0∞, KP < ⊤ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∀ i, morreyNorm 3 (25 / 3)
          ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
            (fun z => u z i)) ≤ KU) →
        (∀ i j, morreyNorm 2 (25 / 8)
          ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
            (fun z => Du z i j)) ≤ KD) →
        ((∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball 0 (43 / 64) ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball 0 (43 / 64) → ∀ i,
            Integrable (fun z => Dp z i)
              (volume.restrict (spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball 0 (43 / 64) ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          (∀ i, morreyNorm (6 / 5) (25 / 11 : ℝ)
            ((parabolicCylinder (0 : Vec3) 0 (43 / 64)).indicator
              (fun z => Dp z i)) ≤ KP) := by
  let KP := oneSidedPressureGradientKP q (25 / 3) C_CZ (11 / 16) (43 / 64)
    ε₀ KU KD
  obtain ⟨hKP, hout⟩ := hGA q (25 / 3) C_CZ (11 / 16) (43 / 64)
    ε₀ KU KD hq (by norm_num) (by norm_num) hC (by norm_num)
    (by norm_num) (by norm_num) hε₀ hKU hKD
  refine ⟨KP, ?_, ?_⟩
  · simpa only [KP] using hKP
  ·
    intro Ω I u Du p f hsol hdom hU hD hsmall
    obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hout hsol hdom hU hD hsmall
    refine ⟨Dp, hAE, hInt, hweak, ?_⟩
    intro i
    have hmin : min (((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹) q = 25 / 11 := by
      rw [show ((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹ = 25 / 11 by norm_num]
      exact min_eq_left (by linarith only [hq])
    simpa only [KP, hmin] using hN i

end CKN.Core.Step4
