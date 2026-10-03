/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.Energy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Energy
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Energy data for finite Galerkin ODEs with an integrable forcing. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open AVenhance.Infra.Parabolic.FourierGalerkin

namespace AVenhance.Infra.Classical

/-- A finite weak-form Galerkin system together with a coefficient-side forcing. -/
structure EnergyWeakFormData (E G : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] where
  /-- Time-dependent linear operator in the Galerkin evolution equation. -/
  coefficient : ℝ → E →L[ℝ] E
  /-- Uniform operator-norm bound for the Galerkin coefficient. -/
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  coefficient_aestronglyMeasurable : AEStronglyMeasurable coefficient volume
  coefficient_norm_le : ∀ t, ‖coefficient t‖ ≤ coefficientBound
  /-- Positive diffusion coefficient in the energy identity. -/
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  /-- Continuous linear gradient operator on the Galerkin state space. -/
  gradient : E →L[ℝ] G
  /-- Constant controlling the drift contribution to the energy estimate. -/
  driftBound : ℝ
  /-- Quadratic drift contribution appearing in the energy identity. -/
  driftForm : ℝ → E → ℝ
  weakForm_energy : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ c,
    2 * inner ℝ c (coefficient t c) =
      -2 * driftForm t c - 2 * diffusivity * ‖gradient c‖ ^ 2
  drift_bound : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ c,
    |driftForm t c| ≤ driftBound * ‖gradient c‖ * ‖c‖

/-- The energy fields extracted from a weak-form Fourier Galerkin system. -/
noncomputable def WeakFormGalerkinData.toEnergyWeakForm {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (W : WeakFormGalerkinData n G) :
    EnergyWeakFormData (Coefficients n) G where
  coefficient := W.coefficient
  coefficientBound := W.coefficientBound
  coefficientBound_nonneg := W.coefficientBound_nonneg
  coefficient_aestronglyMeasurable := W.coefficient_aestronglyMeasurable
  coefficient_norm_le := W.coefficient_norm_le
  diffusivity := W.diffusivity
  diffusivity_pos := W.diffusivity_pos
  gradient := W.gradient
  driftBound := W.driftBound
  driftForm := W.driftForm
  weakForm_energy := W.weakForm_energy
  drift_bound := W.drift_bound

/-- An energy-controlled finite-dimensional linear ODE with an integrable forcing. -/
structure ForcedGalerkinData (E G : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] where
  /-- Coefficient, gradient, and energy identity for the unforced equation. -/
  weak : EnergyWeakFormData E G
  /-- Initial Galerkin state at time zero. -/
  initial : E
  /-- Integrable time-dependent forcing in the Galerkin state space. -/
  forcing : ℝ → E
  forcing_integrable : IntervalIntegrable forcing volume 0 1

namespace ForcedGalerkinData

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The inhomogeneous finite-dimensional linear ODE. -/
def ode (D : ForcedGalerkinData E G) :
    AVenhance.Infra.ODE.LinearODEData (E := E) 0 1 (by norm_num) where
  A := D.weak.coefficient
  f := D.forcing
  y₀ := D.initial
  operatorBound := D.weak.coefficientBound
  operatorBound_nonneg := D.weak.coefficientBound_nonneg
  operator_aestronglyMeasurable := D.weak.coefficient_aestronglyMeasurable
  operator_norm_le := D.weak.coefficient_norm_le
  forcing_intervalIntegrable := D.forcing_integrable

/-- Existence and uniqueness of the forced coefficient path. -/
theorem existsUnique_solution (D : ForcedGalerkinData E G) :
    ∃! u : C(Icc (0 : ℝ) 1, E),
      AVenhance.Infra.ODE.IsLinearIntegralSolution D.weak.coefficient D.forcing
          D.initial 0 1 (AVenhance.Infra.ODE.extendCurve (by norm_num) u) ∧
        AbsolutelyContinuousOnInterval
          (AVenhance.Infra.ODE.extendCurve (by norm_num) u) 0 1 := by
  exact D.ode.existsUnique_absolutelyContinuous_integralSolution

private theorem uniformEnergyEstimateOfLinearGrowth_point1.{v_extracted_2, v_extracted_1} :
  ∀ {E : Type v_extracted_1} {G_1 : Type v_extracted_2} [inst : NormedAddCommGroup E] [inst_1 :
    InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] [inst_3 : NormedAddCommGroup G_1] [inst_4
    : NormedSpace ℝ G_1] (D : ForcedGalerkinData E G_1) (u : C(↑(Icc 0 1), E)) {A G : ℝ}, (∀ t ∈
    Icc 0 1, ‖D.forcing t‖ ≤ A * ‖ODE.extendCurve (by norm_num) u t‖ + G) →
  let y := ODE.extendCurve (by norm_num) u;
  let z := fun s => ‖y s‖ ^ 2;
  let g := fun s => ‖D.weak.gradient (y s)‖ ^ 2;
  let B := max D.weak.driftBound 0;
  let c := B ^ 2 / D.weak.diffusivity + 2 * A + 1;
  let q := fun s => 2 * inner ℝ (y s) ((D.weak.coefficient s) (y s) + D.forcing s);
  ∀ᵐ (s : ℝ) ∂volume.restrict (Icc 0 1), q s ≤ c * z s + G ^ 2 - D.weak.diffusivity * g s
    := by
  intro E G_1 inst inst_1 inst_2 inst_3 inst_4 D u A G hforce y z g B c q
  filter_upwards [D.weak.weakForm_energy, D.weak.drift_bound,
    ae_restrict_mem measurableSet_Icc] with s hform hdrift hs
  have hform := hform (y s)
  have hdrift := hdrift (y s)
  have hforce' := hforce s hs
  have hforceAbs := abs_real_inner_le_norm (y s) (D.forcing s)
  have hforceProduct : ‖y s‖ * ‖D.forcing s‖ ≤
      ‖y s‖ * (A * ‖y s‖ + G) :=
    mul_le_mul_of_nonneg_left hforce' (norm_nonneg _)
  have hforceYoung : 2 * (‖y s‖ * G) ≤ ‖y s‖ ^ 2 + G ^ 2 := by
    nlinarith [sq_nonneg (‖y s‖ - G)]
  have hforcing : 2 * inner ℝ (y s) (D.forcing s) ≤
      2 * A * ‖y s‖ ^ 2 + ‖y s‖ ^ 2 + G ^ 2 := by
    have habs : inner ℝ (y s) (D.forcing s) ≤
        |inner ℝ (y s) (D.forcing s)| := le_abs_self _
    calc
      2 * inner ℝ (y s) (D.forcing s) ≤
          2 * |inner ℝ (y s) (D.forcing s)| := by nlinarith
      _ ≤ 2 * (‖y s‖ * ‖D.forcing s‖) := by nlinarith [hforceAbs]
      _ ≤ 2 * (‖y s‖ * (A * ‖y s‖ + G)) := by nlinarith [hforceProduct]
      _ = 2 * A * ‖y s‖ ^ 2 + 2 * (‖y s‖ * G) := by ring
      _ ≤ 2 * A * ‖y s‖ ^ 2 + (‖y s‖ ^ 2 + G ^ 2) := by
        nlinarith [hforceYoung]
      _ = 2 * A * ‖y s‖ ^ 2 + ‖y s‖ ^ 2 + G ^ 2 := by ring
  have hdriftBound : |D.weak.driftForm s (y s)| ≤
      max D.weak.driftBound 0 * ‖D.weak.gradient (y s)‖ * ‖y s‖ := by
    calc
      |D.weak.driftForm s (y s)| ≤
          D.weak.driftBound * ‖D.weak.gradient (y s)‖ * ‖y s‖ := hdrift
      _ = D.weak.driftBound *
            (‖D.weak.gradient (y s)‖ * ‖y s‖) := by ring
      _ ≤ max D.weak.driftBound 0 *
            (‖D.weak.gradient (y s)‖ * ‖y s‖) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg
          (norm_nonneg _) (norm_nonneg _))
      _ = max D.weak.driftBound 0 * ‖D.weak.gradient (y s)‖ * ‖y s‖ := by ring
  have hdriftAbsorb := AVenhance.Infra.Parabolic.FourierGalerkin.drift_absorption
    D.weak.diffusivity_pos hdriftBound
  have hA : 2 * inner ℝ (y s) (D.weak.coefficient s (y s)) ≤
      (max D.weak.driftBound 0 ^ 2 / D.weak.diffusivity) *
        ‖y s‖ ^ 2 - D.weak.diffusivity *
          ‖D.weak.gradient (y s)‖ ^ 2 := by
    rw [hform]
    exact hdriftAbsorb
  calc
    q s = 2 * inner ℝ (y s) (D.weak.coefficient s (y s)) +
        2 * inner ℝ (y s) (D.forcing s) := by
      simp [q, inner_add_right]
      ring
    _ ≤ (max D.weak.driftBound 0 ^ 2 / D.weak.diffusivity) *
          ‖y s‖ ^ 2 - D.weak.diffusivity *
            ‖D.weak.gradient (y s)‖ ^ 2 +
              (2 * A * ‖y s‖ ^ 2 + ‖y s‖ ^ 2 + G ^ 2) :=
      add_le_add hA hforcing
    _ ≤ c * z s + G ^ 2 - D.weak.diffusivity * g s := by
      dsimp [c, z, g, B]
      exact le_of_eq (by ring_nf)

private theorem uniformEnergyEstimateOfLinearGrowth_plusIneq1.{v_extracted_2, v_extracted_1} :
  ∀ {E : Type v_extracted_1} {G_1 : Type v_extracted_2} [inst : NormedAddCommGroup E] [inst_1 :
    InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] [inst_3 : NormedAddCommGroup G_1] [inst_4
    : NormedSpace ℝ G_1] (D : ForcedGalerkinData E G_1) (u : C(↑(Icc 0 1), E)) {A G : ℝ},
  let y := ODE.extendCurve (by norm_num) u;
  let z := fun s => ‖y s‖ ^ 2;
  let B := max D.weak.driftBound 0;
  let c := B ^ 2 / D.weak.diffusivity + 2 * A + 1;
  0 < c → IntervalIntegrable (fun s => c * z s) volume 0 1 → IntervalIntegrable (fun x => G ^ 2)
    volume 0 1 → (∀ t ∈ Icc 0 1, z t ≤ z 0 + ∫ (s : ℝ) in 0..t, c * z s + G ^ 2) →
  let zplus := fun s => z s + G ^ 2 / c;
  ∀ t ∈ Icc 0 1, zplus t ≤ zplus 0 + ∫ (s : ℝ) in 0..t, c * zplus s
    := by
  intro E G_1 inst inst_1 inst_2 inst_3 inst_4 D u A G y z B c hc hczInt hforceSqInt hineq zplus t
      ht
  have hbase := hineq t ht
  have hsplit : (∫ s in 0..t, c * zplus s) =
      (∫ s in 0..t, c * z s) + G ^ 2 * t := by
    have hsubset : uIcc 0 t ⊆ uIcc 0 1 := by
      rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    calc
      _ = ∫ s in 0..t, (c * z s + G ^ 2) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp [zplus]
        field_simp
      _ = (∫ s in 0..t, c * z s) + ∫ s in 0..t, G ^ 2 :=
        intervalIntegral.integral_add (hczInt.mono_set hsubset)
          (hforceSqInt.mono_set hsubset)
      _ = (∫ s in 0..t, c * z s) + G ^ 2 * t := by
        simp [intervalIntegral.integral_const]
        ring
  have hsubset : uIcc 0 t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  rw [intervalIntegral.integral_add (hczInt.mono_set hsubset)
    (hforceSqInt.mono_set hsubset), intervalIntegral.integral_const] at hbase
  have hbase' : z t ≤ z 0 + ((∫ s in 0..t, c * z s) + G ^ 2 * t) := by
    simpa only [sub_zero, smul_eq_mul, mul_comm] using hbase
  rw [hsplit]
  dsimp [zplus]
  nlinarith [hbase']

private theorem uniformEnergyEstimateOfLinearGrowth_pointBound2.{v_extracted_2, v_extracted_1} :
  ∀ {E : Type v_extracted_1} {G_1 : Type v_extracted_2} [inst : NormedAddCommGroup E] [inst_1 :
    InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] [inst_3 : NormedAddCommGroup G_1] [inst_4
    : NormedSpace ℝ G_1] (D : ForcedGalerkinData E G_1) (u : C(↑(Icc 0 1), E)) {A G : ℝ},
  let y := ODE.extendCurve (by norm_num) u;
  let z := fun s => ‖y s‖ ^ 2;
  let B := max D.weak.driftBound 0;
  let c := B ^ 2 / D.weak.diffusivity + 2 * A + 1;
  0 < c → 0 ≤ c → 1 ≤ c →
  let zplus := fun s => z s + G ^ 2 / c;
  (∀ t ∈ Icc 0 1, zplus t ≤ zplus 0 * Real.exp (∫ (_ : ℝ) in 0..t, c)) → ∀ t ∈ Icc 0 1, z 0 =
    ‖D.initial‖ ^ 2 → ∀ s ∈ Icc 0 t, z s ≤ (‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t)
    := by
  intro E G_1 inst inst_1 inst_2 inst_3 inst_4 D u A G y z B c hc hc0 hcOne zplus hgronwall t ht
      hz0 s hs
  have hst : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
  have hbs := hgronwall s hst
  have hexps : ∫ r in 0..s, c = c * s := by
    simp [intervalIntegral.integral_const]
    ring
  have hplusS : zplus s ≤ zplus 0 * Real.exp (c * s) := by
    simpa [hexps] using hbs
  have htcmp : c * s ≤ c * t := mul_le_mul_of_nonneg_left hs.2 hc0
  have htmp : z s ≤ zplus 0 * Real.exp (c * s) := by
    dsimp [zplus] at hplusS ⊢
    have hdivnonneg : 0 ≤ G ^ 2 / c := div_nonneg (sq_nonneg _) hc0
    exact le_trans (by nlinarith [hdivnonneg]) hplusS
  calc
    z s ≤ zplus 0 * Real.exp (c * s) := htmp
    _ ≤ zplus 0 * Real.exp (c * t) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htcmp) (by
        dsimp [zplus]
        rw [hz0]
        positivity)
    _ ≤ (‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      dsimp [zplus]
      rw [hz0]
      have hdiv : G ^ 2 / c ≤ G ^ 2 := by
        exact div_le_self (sq_nonneg G) hcOne
      linarith

private theorem uniformEnergyEstimateOfLinearGrowth_ineq3.{v_extracted_2, v_extracted_1} :
  ∀ {E : Type v_extracted_1} {G_1 : Type v_extracted_2} [inst : NormedAddCommGroup E] [inst_1 :
    InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] [inst_3 : NormedAddCommGroup G_1] [inst_4
    : NormedSpace ℝ G_1] (D : ForcedGalerkinData E G_1) (u : C(↑(Icc 0 1), E)) {A G : ℝ},
  let y := ODE.extendCurve (by norm_num) u;
  let z := fun s => ‖y s‖ ^ 2;
  let g := fun s => ‖D.weak.gradient (y s)‖ ^ 2;
  let B := max D.weak.driftBound 0;
  let c := B ^ 2 / D.weak.diffusivity + 2 * A + 1;
  IntervalIntegrable (fun s => c * z s) volume 0 1 → IntervalIntegrable (fun x => G ^ 2) volume
    0 1 → IntervalIntegrable (fun s => c * z s + G ^ 2) volume 0 1 →
  let q := fun s => 2 * inner ℝ (y s) ((D.weak.coefficient s) (y s) + D.forcing s);
  IntervalIntegrable q volume 0 1 → (∀ᵐ (s : ℝ) ∂volume.restrict (Icc 0 1), q s ≤ c * z s + G ^
    2 - D.weak.diffusivity * g s) → (∀ t ∈ Icc 0 1, ∫ (s : ℝ) in 0..t, q s = z t - z 0) → ∀ t ∈
    Icc 0 1, z t ≤ z 0 + ∫ (s : ℝ) in 0..t, c * z s + G ^ 2
    := by
  intro E G_1 inst inst_1 inst_2 inst_3 inst_4 D u A G y z g B c hczInt hforceSqInt hsourceInt q
      hqInt hpoint hidentity t ht
  have hsubset : uIcc 0 t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hqT := hqInt.mono_set hsubset
  have hrhsT := hsourceInt.mono_set hsubset
  have hpointT : q ≤ᵐ[volume.restrict (Icc 0 t)]
      fun s => c * z s + G ^ 2 := by
    have hsubsetIcc : Icc (0 : ℝ) t ⊆ Icc 0 1 := by
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have hsmall := ae_mono (Measure.restrict_mono hsubsetIcc le_rfl) hpoint
    filter_upwards [hsmall] with s hs
    have hnonneg : 0 ≤ D.weak.diffusivity * g s :=
      mul_nonneg D.weak.diffusivity_pos.le (sq_nonneg _)
    linarith
  have hint := intervalIntegral.integral_mono_ae_restrict ht.1 hqT hrhsT hpointT
  rw [hidentity t ht] at hint
  have hsplit : ∫ s in 0..t, (c * z s + G ^ 2) =
      (∫ s in 0..t, c * z s) + G ^ 2 * t := by
    rw [intervalIntegral.integral_add (hczInt.mono_set hsubset)
      (hforceSqInt.mono_set hsubset), intervalIntegral.integral_const]
    ring
  rw [hsplit] at hint ⊢
  nlinarith

private theorem uniformEnergyEstimateOfLinearGrowth_branch1.{v_extracted_2, v_extracted_1} :
  ∀ {E : Type v_extracted_1} {G_1 : Type v_extracted_2} [inst : NormedAddCommGroup E] [inst_1 :
    InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] [inst_3 : NormedAddCommGroup G_1] [inst_4
    : NormedSpace ℝ G_1] (D : ForcedGalerkinData E G_1) (u : C(↑(Icc 0 1), E)) {A G : ℝ},
  let y := ODE.extendCurve (by norm_num) u;
  let z := fun s => ‖y s‖ ^ 2;
  let g := fun s => ‖D.weak.gradient (y s)‖ ^ 2;
  let B := max D.weak.driftBound 0;
  let c := B ^ 2 / D.weak.diffusivity + 2 * A + 1;
  0 < c → 0 ≤ c → 1 ≤ c → IntervalIntegrable z volume 0 1 → IntervalIntegrable g volume 0 1 →
    IntervalIntegrable (fun s => c * z s) volume 0 1 → IntervalIntegrable (fun x => G ^ 2)
    volume 0 1 → IntervalIntegrable (fun s => c * z s + G ^ 2) volume 0 1 →
  let q := fun s => 2 * inner ℝ (y s) ((D.weak.coefficient s) (y s) + D.forcing s);
  IntervalIntegrable q volume 0 1 → (∀ᵐ (s : ℝ) ∂volume.restrict (Icc 0 1), q s ≤ c * z s + G ^
    2 - D.weak.diffusivity * g s) → (∀ t ∈ Icc 0 1, ∫ (s : ℝ) in 0..t, q s = z t - z 0) →
  let zplus := fun s => z s + G ^ 2 / c;
  (∀ t ∈ Icc 0 1, zplus t ≤ zplus 0 * Real.exp (∫ (_ : ℝ) in 0..t, c)) → ∀ t ∈ Icc 0 1, z 0 =
    ‖D.initial‖ ^ 2 → ‖ODE.extendCurve (by norm_num) u t‖ ^ 2 + D.weak.diffusivity * ∫ (s : ℝ)
    in 0..t, ‖D.weak.gradient (ODE.extendCurve (by norm_num) u s)‖ ^ 2 ≤ ‖D.initial‖ ^ 2 + G ^ 2
    + (max D.weak.driftBound 0 ^ 2 / D.weak.diffusivity + 2 * A + 1) * (t * ((‖D.initial‖ ^ 2 +
    G ^ 2) * Real.exp ((max D.weak.driftBound 0 ^ 2 / D.weak.diffusivity + 2 * A + 1) * t)))
    := by
  intro E G_1 inst inst_1 inst_2 inst_3 inst_4 D u A G y z g B c hc hc0 hcOne hzInt hgInt hczInt
      hforceSqInt hsourceInt q hqInt hpoint hidentity zplus hgronwall t ht hz0
  have hsubset : uIcc 0 t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hqT := hqInt.mono_set hsubset
  have hrhsT := (hsourceInt.sub (hgInt.const_mul D.weak.diffusivity)).mono_set hsubset
  have hpointT : q ≤ᵐ[volume.restrict (Icc 0 t)]
      fun s => c * z s + G ^ 2 - D.weak.diffusivity * g s := by
    have hsubsetIcc : Icc (0 : ℝ) t ⊆ Icc 0 1 := by
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    exact ae_mono (Measure.restrict_mono hsubsetIcc le_rfl) hpoint
  have hint := intervalIntegral.integral_mono_ae_restrict ht.1 hqT hrhsT hpointT
  rw [hidentity t ht] at hint
  have hsourceEq : ∫ s in 0..t, (c * z s + G ^ 2) =
      c * (∫ s in 0..t, z s) + G ^ 2 * t := by
    rw [intervalIntegral.integral_add (hczInt.mono_set hsubset)
      (hforceSqInt.mono_set hsubset)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    ring
  have hgradientEq : ∫ s in 0..t, D.weak.diffusivity * g s =
      D.weak.diffusivity * ∫ s in 0..t, g s := by
    rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub (hsourceInt.mono_set hsubset)
    ((hgInt.const_mul D.weak.diffusivity).mono_set hsubset)] at hint
  have hpointBound : ∀ s ∈ Icc 0 t,
      z s ≤ (‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t) := by
    apply uniformEnergyEstimateOfLinearGrowth_pointBound2
    all_goals assumption
  have hconstInt : IntervalIntegrable
      (fun _ : ℝ => (‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t)) volume 0 t :=
    intervalIntegrable_const
  have hintZ := intervalIntegral.integral_mono_on ht.1 (hzInt.mono_set hsubset)
    hconstInt hpointBound
  have hintZ' : ∫ s in 0..t, z s ≤
      t * ((‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t)) := by
    calc
      ∫ s in 0..t, z s ≤ ∫ s in 0..t,
          (‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t) := hintZ
      _ = t * ((‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t)) := by
        simp [intervalIntegral.integral_const]
        ring
  have henergy : z t + D.weak.diffusivity * (∫ s in 0..t, g s) ≤
      z 0 + c * (∫ s in 0..t, z s) + G ^ 2 * t := by
    have hint' := add_le_add_right hint
      (z 0 + D.weak.diffusivity * (∫ s in 0..t, g s))
    calc
      z t + D.weak.diffusivity * ∫ s in 0..t, g s =
          (z t - z 0) +
            (z 0 + D.weak.diffusivity * (∫ s in 0..t, g s)) := by ring
      _ ≤ ((∫ s in 0..t, (c * z s + G ^ 2)) -
            (∫ s in 0..t, D.weak.diffusivity * g s)) +
            (z 0 + D.weak.diffusivity * (∫ s in 0..t, g s)) := by
        linarith [hint']
      _ = z 0 + c * (∫ s in 0..t, z s) + G ^ 2 * t := by
        rw [hsourceEq, hgradientEq]
        ring_nf
  have hmul := mul_le_mul_of_nonneg_left hintZ' hc0
  have htime : G ^ 2 * t ≤ G ^ 2 := by
    exact mul_le_of_le_one_right (sq_nonneg G) ht.2
  have hmul' : z 0 + c * ∫ s in 0..t, z s ≤
      z 0 + c * (t * ((‖D.initial‖ ^ 2 + G ^ 2) *
        Real.exp (c * t))) := by
    linarith [hmul]
  have henergyBound : z 0 + c * (∫ s in 0..t, z s) + G ^ 2 * t ≤
      z 0 + c * (t * ((‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t))) + G ^ 2 := by
    calc
      z 0 + c * (∫ s in 0..t, z s) + G ^ 2 * t =
          (z 0 + c * (∫ s in 0..t, z s)) + G ^ 2 * t := by ring_nf
      _ ≤ (z 0 + c * (t * ((‖D.initial‖ ^ 2 + G ^ 2) *
            Real.exp (c * t)))) + G ^ 2 :=
        add_le_add hmul' htime
      _ = z 0 + c * (t * ((‖D.initial‖ ^ 2 + G ^ 2) *
            Real.exp (c * t))) + G ^ 2 := by ring
  have henergy' : z t + D.weak.diffusivity * (∫ s in 0..t, g s) ≤
      z 0 + c * (t * ((‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t))) + G ^ 2 := by
    calc
      z t + D.weak.diffusivity * (∫ s in 0..t, g s) ≤
          z 0 + c * (∫ s in 0..t, z s) + G ^ 2 * t := henergy
      _ ≤ z 0 + c * (t * ((‖D.initial‖ ^ 2 + G ^ 2) *
            Real.exp (c * t))) + G ^ 2 := henergyBound
  rw [hz0] at henergy'
  have henergyFinal :
      ‖AVenhance.Infra.ODE.extendCurve (by norm_num) u t‖ ^ 2 +
          D.weak.diffusivity * ∫ s in 0..t,
            ‖D.weak.gradient (AVenhance.Infra.ODE.extendCurve (by norm_num) u s)‖ ^ 2 ≤
        ‖D.initial‖ ^ 2 + c *
          (t * ((‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t))) + G ^ 2 := by
    simpa [z, g, y] using henergy'
  have henergyFinal' :
      ‖AVenhance.Infra.ODE.extendCurve (by norm_num) u t‖ ^ 2 +
          D.weak.diffusivity * ∫ s in 0..t,
            ‖D.weak.gradient (AVenhance.Infra.ODE.extendCurve (by norm_num) u s)‖ ^ 2 ≤
        ‖D.initial‖ ^ 2 + G ^ 2 +
          c * (t * ((‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t))) := by
    calc
      _ ≤ ‖D.initial‖ ^ 2 + c *
            (t * ((‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t))) + G ^ 2 :=
        henergyFinal
      _ = ‖D.initial‖ ^ 2 + G ^ 2 +
            c * (t * ((‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t))) := by ring
  simpa only [c, B] using henergyFinal'

/-- Cutoff-independent scalar and integrated-gradient estimates for a forced Galerkin path.

The forcing bound is measured in coefficient-space `L²`. The constants depend on the drift bound,
diffusivity, initial datum, and forcing bound, but not on the mode dimension. -/
theorem uniformEnergyEstimateOfLinearGrowth (D : ForcedGalerkinData E G)
    (u : C(Icc (0 : ℝ) 1, E)) (hu : D.ode.IsSolution u)
    {A G : ℝ} (hAcoef : 0 ≤ A) (_hG : 0 ≤ G)
    (hforce : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖D.forcing t‖ ≤ A * ‖AVenhance.Infra.ODE.extendCurve (by norm_num) u t‖ + G) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖AVenhance.Infra.ODE.extendCurve (by norm_num) u t‖ ^ 2 ≤
        (‖D.initial‖ ^ 2 + G ^ 2) *
          Real.exp ((max D.weak.driftBound 0 ^ 2 / D.weak.diffusivity + 2 * A + 1) * t) ∧
      ‖AVenhance.Infra.ODE.extendCurve (by norm_num) u t‖ ^ 2 +
          D.weak.diffusivity * ∫ s in 0..t,
            ‖D.weak.gradient
              (AVenhance.Infra.ODE.extendCurve (by norm_num) u s)‖ ^ 2 ≤
        ‖D.initial‖ ^ 2 + G ^ 2 +
          (max D.weak.driftBound 0 ^ 2 / D.weak.diffusivity + 2 * A + 1) *
            (t * ((‖D.initial‖ ^ 2 + G ^ 2) *
              Real.exp ((max D.weak.driftBound 0 ^ 2 / D.weak.diffusivity + 2 * A + 1) * t)) ) := by
  let y : ℝ → E := AVenhance.Infra.ODE.extendCurve (by norm_num) u
  let z : ℝ → ℝ := fun s => ‖y s‖ ^ 2
  let g : ℝ → ℝ := fun s => ‖D.weak.gradient (y s)‖ ^ 2
  let B : ℝ := max D.weak.driftBound 0
  let c : ℝ := B ^ 2 / D.weak.diffusivity + 2 * A + 1
  have hB : 0 ≤ B := le_max_right _ _
  have hc : 0 < c := by
    dsimp [c]
    have hκ : 0 < D.weak.diffusivity := D.weak.diffusivity_pos
    positivity
  have hc0 : 0 ≤ c := hc.le
  have hcOne : 1 ≤ c := by
    dsimp [c]
    have hratio : 0 ≤ B ^ 2 / D.weak.diffusivity :=
      div_nonneg (sq_nonneg B) D.weak.diffusivity_pos.le
    have hApos : 0 ≤ 2 * A := mul_nonneg (by norm_num) hAcoef
    linarith
  have hycont : Continuous y := AVenhance.Infra.ODE.continuous_extendCurve (by norm_num) u
  have hzcont : Continuous z := by exact (continuous_norm.comp hycont).pow 2
  have hgcont : Continuous g := by
    exact (continuous_norm.comp (D.weak.gradient.continuous.comp hycont)).pow 2
  have hzInt : IntervalIntegrable z volume 0 1 :=
    hzcont.continuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hgInt : IntervalIntegrable g volume 0 1 :=
    hgcont.continuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hczInt : IntervalIntegrable (fun s => c * z s) volume 0 1 := hzInt.const_mul c
  have hforceSqInt : IntervalIntegrable (fun _ : ℝ => G ^ 2) volume 0 1 :=
    intervalIntegrable_const
  have hsourceInt : IntervalIntegrable (fun s => c * z s + G ^ 2) volume 0 1 :=
    hczInt.add hforceSqInt
  let q : ℝ → ℝ := fun s => 2 * inner ℝ (y s)
    (D.weak.coefficient s (y s) + D.forcing s)
  have hAC : AbsolutelyContinuousOnInterval z 0 1 := by
    simpa [z, y] using hu.energy_absolutelyContinuous D.ode
  have hqDeriv := hu.ae_energy_deriv D.ode
  have hqEq : q =ᵐ[volume.restrict (uIoc 0 1)] deriv z := by
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [hqDeriv] with s hs hsmem
    have hsmem' : s ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (uIoc_subset_uIcc hsmem)
    simpa [q, z, y, ForcedGalerkinData.ode,
      AVenhance.Infra.ODE.linearRhs] using (hs hsmem').deriv.symm
  have hqInt : IntervalIntegrable q volume 0 1 :=
    hAC.intervalIntegrable_deriv |>.congr_ae hqEq.symm
  have hpoint : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)),
      q s ≤ c * z s + G ^ 2 - D.weak.diffusivity * g s := by
    apply uniformEnergyEstimateOfLinearGrowth_point1
    all_goals assumption
  have hzero : y 0 = D.initial := by
    have hsol := hu.integralSolution D.ode
    have hz := hsol 0 ⟨le_rfl, by norm_num⟩
    simpa [y, ForcedGalerkinData.ode, AVenhance.Infra.ODE.linearRhs] using hz
  have hidentity (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∫ s in 0..t, q s = z t - z 0 := by
    have hsubset : uIcc 0 t ⊆ uIcc 0 1 := by
      rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have hsol := hu.integralSolution D.ode
    have hsolT : AVenhance.Infra.ODE.IsLinearIntegralSolution D.weak.coefficient
        D.forcing D.initial 0 t y := by
      intro s hs
      exact hsol s ⟨hs.1, hs.2.trans ht.2⟩
    have hrhsT : IntervalIntegrable
        (AVenhance.Infra.ODE.linearRhs D.weak.coefficient D.forcing y) volume 0 t := by
      change IntervalIntegrable (D.ode.rhs u) volume 0 t
      exact (D.ode.rhs_intervalIntegrable u).mono_set hsubset
    have hid := hsolT.energy_identity ht.1 hrhsT
    simpa [q, z, y, AVenhance.Infra.ODE.linearRhs] using hid
  have hineq : ∀ t ∈ Icc (0 : ℝ) 1,
      z t ≤ z 0 + ∫ s in 0..t, c * z s + G ^ 2 := by
    apply uniformEnergyEstimateOfLinearGrowth_ineq3
    all_goals assumption
  let zplus : ℝ → ℝ := fun s => z s + G ^ 2 / c
  have hzplusCont : Continuous zplus := hzcont.add continuous_const
  have hzplusInt : IntervalIntegrable zplus volume 0 1 :=
    hzplusCont.continuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hczplusInt : IntervalIntegrable (fun s => c * zplus s) volume 0 1 :=
    hzplusInt.const_mul c
  have hplusIneq : ∀ t ∈ Icc (0 : ℝ) 1,
      zplus t ≤ zplus 0 + ∫ s in 0..t, c * zplus s := by
    apply uniformEnergyEstimateOfLinearGrowth_plusIneq1
    all_goals assumption
  have hgronwall := AVenhance.Infra.ODE.integral_gronwall_bound
    (a := 0) (b := 1) (C := zplus 0) (show (0 : ℝ) ≤ 1 by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume 0 1)
    hczplusInt (fun _ _ => hc0) hplusIneq
  intro t ht
  have hexp : ∫ s in 0..t, c = c * t := by
    simp [intervalIntegral.integral_const]
    ring
  have hplusBound : zplus t ≤ zplus 0 * Real.exp (c * t) := by
    simpa [hexp] using hgronwall t ht
  have hz0 : z 0 = ‖D.initial‖ ^ 2 := by
    change ‖y 0‖ ^ 2 = ‖D.initial‖ ^ 2
    rw [hzero]
  have hscalar : z t ≤ (‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t) := by
    have htmp : z t ≤ zplus t := by
      dsimp [zplus]
      exact le_add_of_nonneg_right (div_nonneg (sq_nonneg G) hc0)
    have hbase : zplus 0 ≤ ‖D.initial‖ ^ 2 + G ^ 2 := by
      dsimp [zplus]
      rw [hz0]
      have hdiv : G ^ 2 / c ≤ G ^ 2 := by
        exact div_le_self (sq_nonneg G) hcOne
      linarith
    have hexp_nonneg : 0 ≤ Real.exp (c * t) := (Real.exp_pos _).le
    calc
      z t ≤ zplus t := htmp
      _ ≤ zplus 0 * Real.exp (c * t) := hplusBound
      _ ≤ (‖D.initial‖ ^ 2 + G ^ 2) * Real.exp (c * t) :=
        mul_le_mul_of_nonneg_right hbase hexp_nonneg
  constructor
  · simpa [z, y, c, B] using hscalar
  · apply uniformEnergyEstimateOfLinearGrowth_branch1
    all_goals assumption
end ForcedGalerkinData

namespace ForcedGalerkinData

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]

end ForcedGalerkinData

end AVenhance.Infra.Classical

end
