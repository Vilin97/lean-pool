/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.Density
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.BilinearForms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TimeHolder
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.CutoffNesting

/-!
# Equation-derived weak time moduli

Testing each larger-cutoff ODE by an embedded lower-cutoff Fourier vector yields a common
one-half-Hölder modulus, with the uniform spatial gradient energy supplying the time Cauchy bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance equationModulusMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance equationModulusMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance equationModulusProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance equationModulusTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- The cutoff-uniform spacetime gradient energy bound for the Galerkin solutions. -/
noncomputable def FrozenDriftProblem.gradientEnergyBound (P : FrozenDriftProblem) : ℝ :=
  ‖P.initialTorusL2‖ ^ 2 *
    (1 + (positiveCutoffDriftConstant P.b P.drift_bounded ^ 2 / P.κ) *
      Real.exp (positiveCutoffDriftConstant P.b P.drift_bounded ^ 2 / P.κ)) / P.κ

private theorem fourierPairing_modulus_of_cutoff_le_ordered1 :
  ∀ (P : FrozenDriftProblem) {M N : ℕ} (hMN : M ≤ N) (c : Coefficients (RealFourierDimension
    M)),
  let D := P.galerkinData N;
  let y : ℝ → Coefficients (RealFourierDimension N) := AVenhance.Infra.ODE.extendCurve (by
    norm_num) (P.coefficientPath N);
  let dN := realFourierCoefficientsLift hMN c;
  let g : ℝ → ℝ := fun r => ‖positiveCutoffGradientMap N (y r)‖;
  let E : ℝ := P.gradientEnergyBound;
  let K : ℝ := positiveCutoffDriftConstant P.b P.drift_bounded * ‖c‖ + P.κ *
    ‖realFourierGradientMap M c‖;
  (0 : ℝ) ≤ K → MemLp g (2 : ENNReal) (volume.restrict (Ioc (0 : ℝ) (1 : ℝ))) → (∀ᵐ (r : ℝ)
    ∂volume.restrict (Ioc (0 : ℝ) (1 : ℝ)), (0 : ℝ) ≤ g r) → IntervalIntegrable g volume (0 : ℝ)
    (1 : ℝ) → IntervalIntegrable (fun (r : ℝ) => (D.coefficient r : Coefficients
    (RealFourierDimension N) → Coefficients (RealFourierDimension N)) (y r)) volume (0 : ℝ) (1 :
    ℝ) → ODE.IsLinearIntegralSolution D.ode.A D.ode.f D.ode.y₀ (0 : ℝ) (1 : ℝ) (ODE.extendCurve
    (by norm_num) (P.coefficientPath N)) → (∀ (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (1 : ℝ)),
    ⟪(P.scalarPath N : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) → ↥ScalarTorusL2) ⟨r, hr⟩,
    (realFourierScalarMap M : Coefficients (RealFourierDimension M) → ↥ScalarTorusL2) c⟫ = ⟪y r,
    dN⟫) → (∀ᵐ (r : ℝ) ∂volume.restrict (Icc (0 : ℝ) (1 : ℝ)), |⟪dN, (D.coefficient r :
    Coefficients (RealFourierDimension N) → Coefficients (RealFourierDimension N)) (y r)⟫| ≤ K *
    g r) → ∀ (a b : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)), (↑a : ℝ) ≤ (↑b : ℝ) → |⟪(P.scalarPath N :
    (↑(Icc (0 : ℝ) (1 : ℝ)) : Type) → ↥ScalarTorusL2) b, (realFourierScalarMap M : Coefficients
    (RealFourierDimension M) → ↥ScalarTorusL2) c⟫ - ⟪(P.scalarPath N : (↑(Icc (0 : ℝ) (1 : ℝ)) :
    Type) → ↥ScalarTorusL2) a, (realFourierScalarMap M : Coefficients (RealFourierDimension M) →
    ↥ScalarTorusL2) c⟫| ≤ K * √(dist b a) * √E
    := by
  intro P M N hMN c D y dN g E K hK hgMem hgNonneg hgradInterval hglobalRhs' hODE hscalarPair
      hpoint a b hab
  let aa : ℝ := a
  let bb : ℝ := b
  have htimeSubsetAB : uIcc aa bb ⊆ uIcc (0 : ℝ) 1 := by
    change uIcc (a : ℝ) (b : ℝ) ⊆ uIcc (0 : ℝ) 1
    rw [uIcc_of_le hab, uIcc_of_le (by norm_num)]
    intro r hr
    exact ⟨a.property.1.trans hr.1, hr.2.trans b.property.2⟩
  have hrhsAB := hglobalRhs'.mono_set htimeSubsetAB
  have hsolA := hODE aa a.property
  have hsolB := hODE bb b.property
  have hsolA' : y aa = D.initial + ∫ r in (0 : ℝ)..aa, D.coefficient r (y r) := by
    simpa [y, D, WeakFormGalerkinData.ode, AVenhance.Infra.ODE.linearRhs] using hsolA
  have hsolB' : y bb = D.initial + ∫ r in (0 : ℝ)..bb, D.coefficient r (y r) := by
    simpa [y, D, WeakFormGalerkinData.ode, AVenhance.Infra.ODE.linearRhs] using hsolB
  have hvecDiff : y bb - y aa = ∫ r in aa..bb, D.coefficient r (y r) := by
    calc
      y bb - y aa =
          (D.initial + ∫ r in (0 : ℝ)..bb, D.coefficient r (y r)) -
            (D.initial + ∫ r in (0 : ℝ)..aa, D.coefficient r (y r)) := by
              rw [hsolB', hsolA']
      _ = (∫ r in (0 : ℝ)..bb, D.coefficient r (y r)) -
            ∫ r in (0 : ℝ)..aa, D.coefficient r (y r) := by abel
      _ = ∫ r in aa..bb, D.coefficient r (y r) :=
        intervalIntegral.integral_interval_sub_left
          (hglobalRhs'.mono_set (by
            rw [uIcc_of_le (show (0 : ℝ) ≤ bb by simpa [bb] using b.property.1),
              uIcc_of_le (by norm_num)]
            intro r hr
            exact ⟨hr.1, hr.2.trans (by simpa [bb] using b.property.2)⟩))
          (hglobalRhs'.mono_set (by
            rw [uIcc_of_le (show (0 : ℝ) ≤ aa by simpa [aa] using a.property.1),
              uIcc_of_le (by norm_num)]
            intro r hr
            exact ⟨hr.1, hr.2.trans (by simpa [aa] using a.property.2)⟩))
  have hmap := (innerSL ℝ dN).intervalIntegral_comp_comm hrhsAB
  have hpairDiff :
      inner ℝ (P.scalarPath N b) (realFourierScalarMap M c) -
          inner ℝ (P.scalarPath N a) (realFourierScalarMap M c) =
        ∫ r in aa..bb, inner ℝ dN (D.coefficient r (y r)) := by
    rw [hscalarPair bb b.property, hscalarPair aa a.property]
    calc
      inner ℝ (y bb) dN - inner ℝ (y aa) dN =
          inner ℝ (y bb - y aa) dN := by rw [inner_sub_left]
      _ = inner ℝ (∫ r in aa..bb, D.coefficient r (y r)) dN := by rw [hvecDiff]
      _ = inner ℝ dN (∫ r in aa..bb, D.coefficient r (y r)) := real_inner_comm _ _
      _ = ∫ r in aa..bb, inner ℝ dN (D.coefficient r (y r)) := hmap.symm
  have hKG : IntervalIntegrable (fun r => K * g r) volume aa bb := by
    have hgab : IntervalIntegrable g volume aa bb := hgradInterval.mono_set (by
      change uIcc (a : ℝ) (b : ℝ) ⊆ uIcc (0 : ℝ) 1
      rw [uIcc_of_le hab, uIcc_of_le (by norm_num)]
      intro r hr
      exact ⟨a.property.1.trans hr.1, hr.2.trans b.property.2⟩)
    exact hgab.const_mul K
  have hpointVol := (ae_restrict_iff' measurableSet_Icc).mp hpoint
  have hpoint' : ∀ᵐ r ∂volume, r ∈ Ioc aa bb →
      ‖inner ℝ dN (D.coefficient r (y r))‖ ≤ K * g r := by
    filter_upwards [hpointVol] with r hr hmem
    have hleft : (a : ℝ) ≤ r := le_of_lt (by simpa [aa] using hmem.1)
    have hright : r ≤ (b : ℝ) := by simpa [bb] using hmem.2
    have hrIcc : r ∈ Icc (0 : ℝ) 1 :=
      ⟨a.property.1.trans hleft, hright.trans b.property.2⟩
    rw [Real.norm_eq_abs]
    exact hr hrIcc
  have hmain := intervalIntegral.norm_integral_le_of_norm_le hab hpoint' hKG
  have htime := intervalIntegral_nonneg_le_sqrt_energy hab a.property.1 b.property.2
    hgMem hgNonneg (by simpa [g, E, D, FrozenDriftProblem.galerkinData,
      FrozenDriftProblem.gradientEnergyBound, positiveCutoffGalerkinData] using
        P.gradientEnergy_le N)
  rw [hpairDiff]
  calc
    |∫ r in aa..bb, inner ℝ dN (D.coefficient r (y r))| ≤ ∫ r in aa..bb, K * g r := by
      simpa [Real.norm_eq_abs] using hmain
    _ = K * ∫ r in aa..bb, g r := by rw [intervalIntegral.integral_const_mul]
    _ ≤ K * (Real.sqrt (bb - aa) * Real.sqrt E) :=
      mul_le_mul_of_nonneg_left htime hK
    _ = K * Real.sqrt (dist b a) * Real.sqrt E := by
      have hdist : dist b a = bb - aa := by
        change dist (b : ℝ) (a : ℝ) = bb - aa
        rw [Real.dist_eq]
        simp [aa, bb, abs_of_nonneg (sub_nonneg.mpr hab)]
      rw [hdist]
      ring

/-- Pairing with a fixed real Fourier vector has a uniform half-Hölder modulus for every
Galerkin cutoff containing its support. -/
theorem FrozenDriftProblem.fourierPairing_modulus_of_cutoff_le
    (P : FrozenDriftProblem) {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension M)) :
    ∀ t s : Icc (0 : ℝ) 1,
      |inner ℝ (P.scalarPath N t) (realFourierScalarMap M c) -
          inner ℝ (P.scalarPath N s) (realFourierScalarMap M c)| ≤
        (positiveCutoffDriftConstant P.b P.drift_bounded * ‖c‖ +
          P.κ * ‖realFourierGradientMap M c‖) *
          Real.sqrt (dist t s) * Real.sqrt P.gradientEnergyBound := by
  let D := P.galerkinData N
  let y : ℝ → Coefficients (RealFourierDimension N) :=
    AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N)
  let dN := realFourierCoefficientsLift hMN c
  let g : ℝ → ℝ := fun r => ‖positiveCutoffGradientMap N (y r)‖
  let E : ℝ := P.gradientEnergyBound
  let K : ℝ := positiveCutoffDriftConstant P.b P.drift_bounded * ‖c‖ +
    P.κ * ‖realFourierGradientMap M c‖
  have hκ : 0 < P.κ := P.κ_pos
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg
      (mul_nonneg (positiveCutoffDriftConstant_spec N P.b P.drift_measurable
        P.drift_bounded).1 (norm_nonneg _))
      (mul_nonneg P.κ_pos.le (norm_nonneg _))
  have hycont : Continuous y :=
    AVenhance.Infra.ODE.continuous_extendCurve (by norm_num) (P.coefficientPath N)
  have hgcont : Continuous g := by
    exact continuous_norm.comp ((D.gradient).continuous.comp hycont)
  have hpathnorm : ∀ r ∈ Icc (0 : ℝ) 1, ‖y r‖ ≤ P.scalarBound := by
    intro r hr
    let q : Icc (0 : ℝ) 1 := ⟨r, hr⟩
    have hscalar := P.scalarPath_norm_le N q
    have hyq : y r = (P.coefficientPath N) q := by
      exact AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) _ hr
    rw [show P.scalarPath N q = realFourierScalarMap N ((P.coefficientPath N) q) by rfl,
      realFourierScalarMap_norm] at hscalar
    simpa [y, q, hyq] using hscalar
  have hgBound : ∀ r ∈ Icc (0 : ℝ) 1, ‖g r‖ ≤ ‖D.gradient‖ * P.scalarBound := by
    intro r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      g r = ‖D.gradient (y r)‖ := by rfl
      _ ≤ ‖D.gradient‖ * ‖y r‖ := D.gradient.le_opNorm _
      _ ≤ ‖D.gradient‖ * P.scalarBound :=
        mul_le_mul_of_nonneg_left (hpathnorm r hr) (norm_nonneg _)
  have hgMem : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply MemLp.of_bound hgcont.aestronglyMeasurable (‖D.gradient‖ * P.scalarBound)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hgBound r (Ioc_subset_Icc_self hr)
  have hgNonneg : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) 1)), 0 ≤ g r :=
    Filter.Eventually.of_forall fun r => norm_nonneg _
  have henergy : ∫ r in (0 : ℝ)..1, g r ^ 2 ≤ E := by
    simpa [g, D, E, FrozenDriftProblem.galerkinData,
      FrozenDriftProblem.gradientEnergyBound, positiveCutoffGalerkinData] using
      P.gradientEnergy_le N
  have hgradContinuousOn : ContinuousOn g (Icc (0 : ℝ) 1) := hgcont.continuousOn
  have hgradInterval : IntervalIntegrable g volume 0 1 :=
    hgradContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hglobalRhs' : IntervalIntegrable (fun r => D.coefficient r (y r)) volume 0 1 := by
    have h := D.ode.rhs_intervalIntegrable (P.coefficientPath N)
    change IntervalIntegrable (D.ode.rhs (P.coefficientPath N)) volume 0 1 at h
    have heq : (fun r => D.ode.rhs (P.coefficientPath N) r) =
        (fun r => D.coefficient r (y r)) := by
      funext r
      simp [AVenhance.Infra.ODE.LinearODEData.rhs, WeakFormGalerkinData.ode, y, D]
    rw [← heq]
    exact h
  have hODE := (P.coefficientPath_isSolution N).integralSolution D.ode
  have hscalarPair (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      inner ℝ (P.scalarPath N ⟨r, hr⟩) (realFourierScalarMap M c) =
        inner ℝ (y r) dN := by
    have hy : y r = (P.coefficientPath N) ⟨r, hr⟩ := by
      exact AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) _ hr
    rw [show P.scalarPath N ⟨r, hr⟩ =
      realFourierScalarMap N ((P.coefficientPath N) ⟨r, hr⟩) by rfl,
      ← realFourierScalarMap_lift hMN c,
      realFourierScalarMap_inner]
    rw [← hy]
  have hpoint : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) 1)),
      |inner ℝ dN (D.coefficient r (y r))| ≤ K * g r := by
    have hentries := frozenDrift_realModeEntry_integrable_ae N P.b
      P.drift_measurable P.drift_bounded
    have hmatrix := D.matrix_spec
    filter_upwards [hentries, hmatrix, ae_restrict_mem measurableSet_Icc] with r herr hspec hr
    have hcoef : D.coefficient r (y r) = matrixCoefficientCLM
        (fun i j => weakFormMatrixEntry
          (fun s x => AVenhance.Infra.Torus.periodicToTorus (P.b s) x) P.κ
          (realFourierModeFin N) (realFourierModeGradFin N) r i j) (y r) := by
      ext i
      rw [matrixCoefficientCLM_apply]
      exact hspec (y r) i
    rw [hcoef]
    have hidentity := positiveCutoffWeakForm_bilinear_identity N P.b P.κ r
      (y r) dN herr
    have hdrift := positiveCutoffDriftBilinear_bound N P.b P.drift_bounded r hr
      (y r) dN
    have hgradTest : positiveCutoffGradientMap N dN = realFourierGradientMap M c := by
      rw [positiveCutoffGradientMap]
      exact realFourierGradientMap_lift hMN c
    have hgradTestReal : realFourierGradientMap N dN = realFourierGradientMap M c :=
      realFourierGradientMap_lift hMN c
    have hgradState : positiveCutoffGradientMap N (y r) =
        realFourierGradientMap N (y r) := by
      rw [positiveCutoffGradientMap]
    have hscalarTest : ‖dN‖ = ‖c‖ := by
      calc
        ‖dN‖ = ‖realFourierScalarMap N dN‖ := (realFourierScalarMap_norm N dN).symm
        _ = ‖realFourierScalarMap M c‖ := congrArg norm (realFourierScalarMap_lift hMN c)
        _ = ‖c‖ := realFourierScalarMap_norm M c
    rw [hidentity]
    rw [hgradState] at hdrift
    have hinner : |inner ℝ (realFourierGradientMap N (y r))
        (realFourierGradientMap N dN)| ≤
        ‖realFourierGradientMap N (y r)‖ * ‖realFourierGradientMap N dN‖ :=
      abs_real_inner_le_norm _ _
    dsimp [K, g]
    rw [hscalarTest] at hdrift
    calc
      abs (-realFourierDriftBilinearForm N
          (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) r (y r) dN -
          P.κ * inner ℝ (realFourierGradientMap N (y r))
            (realFourierGradientMap N dN)) ≤
          abs (realFourierDriftBilinearForm N
            (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) r (y r) dN) +
            abs (P.κ * inner ℝ (realFourierGradientMap N (y r))
              (realFourierGradientMap N dN)) := by
        simpa [Real.norm_eq_abs, sub_eq_add_neg, abs_neg] using
          (norm_add_le
            (-realFourierDriftBilinearForm N
              (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) r (y r) dN)
            (-P.κ * inner ℝ (realFourierGradientMap N (y r))
              (realFourierGradientMap N dN)))
      _ ≤ positiveCutoffDriftConstant P.b P.drift_bounded *
          ‖realFourierGradientMap N (y r)‖ * ‖c‖ +
          P.κ * (‖realFourierGradientMap N (y r)‖ *
            ‖realFourierGradientMap M c‖) := by
        exact add_le_add hdrift (by
          calc
            |P.κ * inner ℝ (realFourierGradientMap N (y r))
                (realFourierGradientMap N dN)| =
              |P.κ| * |inner ℝ (realFourierGradientMap N (y r))
                (realFourierGradientMap N dN)| := abs_mul _ _
            _ = P.κ * |inner ℝ (realFourierGradientMap N (y r))
                (realFourierGradientMap N dN)| := by rw [abs_of_pos hκ]
            _ ≤
              P.κ * (‖realFourierGradientMap N (y r)‖ *
                ‖realFourierGradientMap N dN‖) := by
                  exact mul_le_mul_of_nonneg_left hinner hκ.le
            _ = P.κ * (‖realFourierGradientMap N (y r)‖ *
                ‖realFourierGradientMap M c‖) := by rw [hgradTestReal])
      _ = K * g r := by
        rw [← hgradState]
        ring
  intro t s
  have hordered (a b : Icc (0 : ℝ) 1) (hab : (a : ℝ) ≤ b) :
      |inner ℝ (P.scalarPath N b) (realFourierScalarMap M c) -
          inner ℝ (P.scalarPath N a) (realFourierScalarMap M c)| ≤
        K * Real.sqrt (dist b a) * Real.sqrt E := by
    exact @fourierPairing_modulus_of_cutoff_le_ordered1 P M N hMN c hK hgMem hgNonneg
        hgradInterval hglobalRhs' hODE hscalarPair hpoint a b hab
  by_cases hst : (s : ℝ) ≤ t
  · exact hordered s t hst
  · have hts : (t : ℝ) ≤ s := le_of_not_ge hst
    have hswap := hordered t s hts
    simpa [E, K, abs_sub_comm, dist_comm, mul_assoc] using hswap

/-- Every fixed finite Galerkin scalar path is Lipschitz in time, with a constant determined by
the finite ODE operator bound and the common scalar `L²` bound. This controls the finite initial
cutoff exceptions for each fixed Fourier test. -/
theorem FrozenDriftProblem.scalarPath_pairing_lipschitz (P : FrozenDriftProblem) (N : ℕ)
    (w : ScalarTorusL2) (t s : Icc (0 : ℝ) 1) :
    |inner ℝ (P.scalarPath N t) w - inner ℝ (P.scalarPath N s) w| ≤
      ((P.galerkinData N).coefficientBound * P.scalarBound * ‖w‖) * dist t s := by
  let D := P.galerkinData N
  let y : ℝ → Coefficients (RealFourierDimension N) :=
    AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N)
  let B : ℝ := D.coefficientBound * P.scalarBound
  have hB : 0 ≤ B := mul_nonneg D.coefficientBound_nonneg P.scalarBound_nonneg
  have hpathnorm : ∀ r ∈ Icc (0 : ℝ) 1, ‖y r‖ ≤ P.scalarBound := by
    intro r hr
    let q : Icc (0 : ℝ) 1 := ⟨r, hr⟩
    have hscalar := P.scalarPath_norm_le N q
    have hyq : y r = (P.coefficientPath N) q :=
      AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) _ hr
    rw [show P.scalarPath N q = realFourierScalarMap N ((P.coefficientPath N) q) by rfl,
      realFourierScalarMap_norm] at hscalar
    simpa [y, q, hyq] using hscalar
  have hglobal : IntervalIntegrable (fun r => D.coefficient r (y r)) volume 0 1 := by
    have h := D.ode.rhs_intervalIntegrable (P.coefficientPath N)
    change IntervalIntegrable (D.ode.rhs (P.coefficientPath N)) volume 0 1 at h
    have heq : (fun r => D.ode.rhs (P.coefficientPath N) r) =
        fun r => D.coefficient r (y r) := by
      funext r
      simp [AVenhance.Infra.ODE.LinearODEData.rhs, WeakFormGalerkinData.ode, y, D]
    rw [← heq]
    exact h
  have hODE := (P.coefficientPath_isSolution N).integralSolution D.ode
  have hordered (a b : Icc (0 : ℝ) 1) (hab : (a : ℝ) ≤ b) :
      |inner ℝ (P.scalarPath N b) w - inner ℝ (P.scalarPath N a) w| ≤
        (D.coefficientBound * P.scalarBound * ‖w‖) * dist b a := by
    let aa : ℝ := a
    let bb : ℝ := b
    have hsolA := hODE aa a.property
    have hsolB := hODE bb b.property
    have hsolA' : y aa = D.initial + ∫ r in (0 : ℝ)..aa, D.coefficient r (y r) := by
      simpa [y, D, WeakFormGalerkinData.ode, AVenhance.Infra.ODE.linearRhs] using hsolA
    have hsolB' : y bb = D.initial + ∫ r in (0 : ℝ)..bb, D.coefficient r (y r) := by
      simpa [y, D, WeakFormGalerkinData.ode, AVenhance.Infra.ODE.linearRhs] using hsolB
    have hvecDiff : y bb - y aa = ∫ r in aa..bb, D.coefficient r (y r) := by
      calc
        y bb - y aa =
            (D.initial + ∫ r in (0 : ℝ)..bb, D.coefficient r (y r)) -
              (D.initial + ∫ r in (0 : ℝ)..aa, D.coefficient r (y r)) := by
                rw [hsolB', hsolA']
        _ = (∫ r in (0 : ℝ)..bb, D.coefficient r (y r)) -
              ∫ r in (0 : ℝ)..aa, D.coefficient r (y r) := by abel
        _ = ∫ r in aa..bb, D.coefficient r (y r) :=
          intervalIntegral.integral_interval_sub_left
            (hglobal.mono_set (by
              rw [uIcc_of_le (show (0 : ℝ) ≤ bb by simpa [bb] using b.property.1),
                uIcc_of_le (by norm_num)]
              intro r hr
              exact ⟨hr.1, hr.2.trans (by simpa [bb] using b.property.2)⟩))
            (hglobal.mono_set (by
              rw [uIcc_of_le (show (0 : ℝ) ≤ aa by simpa [aa] using a.property.1),
                uIcc_of_le (by norm_num)]
              intro r hr
              exact ⟨hr.1, hr.2.trans (by simpa [aa] using a.property.2)⟩))
    have hpoint : ∀ᵐ r ∂volume, r ∈ Ioc aa bb →
        ‖D.coefficient r (y r)‖ ≤ B := by
      filter_upwards with r hr
      have hrIcc : r ∈ Icc (0 : ℝ) 1 := by
        have hleft : (a : ℝ) ≤ r := le_of_lt (by simpa [aa] using hr.1)
        have hright : r ≤ (b : ℝ) := by simpa [bb] using hr.2
        constructor
        · exact a.property.1.trans hleft
        · exact hright.trans b.property.2
      calc
        ‖D.coefficient r (y r)‖ ≤ ‖D.coefficient r‖ * ‖y r‖ := D.coefficient r |>.le_opNorm _
        _ ≤ D.coefficientBound * P.scalarBound :=
          mul_le_mul (D.coefficient_norm_le r) (hpathnorm r hrIcc)
            (norm_nonneg _) D.coefficientBound_nonneg
        _ = B := rfl
    have hconst : IntervalIntegrable (fun _ : ℝ => B) volume aa bb := intervalIntegrable_const
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab hpoint hconst
    have hintegralNorm : ‖∫ r in aa..bb, D.coefficient r (y r)‖ ≤ B * (bb - aa) := by
      calc
        ‖∫ r in aa..bb, D.coefficient r (y r)‖ ≤ ∫ r in aa..bb, B := hnorm
        _ = B * (bb - aa) := by simp [intervalIntegral.integral_const, mul_comm]
    have hvecNorm : ‖y bb - y aa‖ ≤ B * (bb - aa) := by
      simpa [hvecDiff] using hintegralNorm
    have hextA : y aa = (P.coefficientPath N) a :=
      AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) _ a.property
    have hextB : y bb = (P.coefficientPath N) b :=
      AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) _ b.property
    have hscalarDiff : P.scalarPath N b - P.scalarPath N a =
        realFourierScalarMap N (y bb - y aa) := by
      change realFourierScalarMap N ((P.coefficientPath N) b) -
        realFourierScalarMap N ((P.coefficientPath N) a) = _
      rw [← map_sub]
      congr 1
      rw [← hextB, ← hextA]
    have hpairDiff : inner ℝ (P.scalarPath N b) w - inner ℝ (P.scalarPath N a) w =
        inner ℝ (P.scalarPath N b - P.scalarPath N a) w := by
      rw [inner_sub_left]
    have hdist : dist b a = bb - aa := by
      change dist (b : ℝ) (a : ℝ) = bb - aa
      rw [Real.dist_eq]
      simp [aa, bb, abs_of_nonneg (sub_nonneg.mpr hab)]
    calc
      |inner ℝ (P.scalarPath N b) w - inner ℝ (P.scalarPath N a) w| =
          |inner ℝ (P.scalarPath N b - P.scalarPath N a) w| := by rw [hpairDiff]
      _ ≤ ‖P.scalarPath N b - P.scalarPath N a‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ = ‖y bb - y aa‖ * ‖w‖ := by rw [hscalarDiff, realFourierScalarMap_norm]
      _ ≤ (B * (bb - aa)) * ‖w‖ := mul_le_mul_of_nonneg_right hvecNorm (norm_nonneg _)
      _ = (D.coefficientBound * P.scalarBound * ‖w‖) * dist b a := by
        rw [hdist]
        dsimp [B]
        ring
  by_cases hst : (s : ℝ) ≤ t
  · exact hordered s t hst
  · have hts : (t : ℝ) ≤ s := le_of_not_ge hst
    have hswap := hordered t s hts
    simpa [abs_sub_comm, dist_comm] using hswap

/-- Equation-derived half-Hölder moduli for every dense Fourier test, including the finitely many
cutoffs below that test's support. -/
theorem FrozenDriftProblem.fourierPairing_modulus
    (P : FrozenDriftProblem) {w : ScalarTorusL2} (hw : w ∈ realFourierSpan) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N t s,
      |inner ℝ (P.scalarPath N t) w - inner ℝ (P.scalarPath N s) w| ≤
        C * Real.sqrt (dist t s) := by
  obtain ⟨m, hm⟩ := mem_iUnion.mp hw
  obtain ⟨c, hc⟩ := hm
  let L : ℕ → ℝ := fun n => (P.galerkinData n).coefficientBound *
    P.scalarBound * ‖w‖
  let S : ℝ := ∑ n ∈ Finset.range m, L n
  let K : ℝ := positiveCutoffDriftConstant P.b P.drift_bounded * ‖c‖ +
    P.κ * ‖realFourierGradientMap m c‖
  let H : ℝ := K * Real.sqrt P.gradientEnergyBound
  let C : ℝ := S + H
  have hLnonneg (n : ℕ) : 0 ≤ L n := by
    dsimp [L]
    exact mul_nonneg (mul_nonneg (P.galerkinData n).coefficientBound_nonneg
      P.scalarBound_nonneg) (norm_nonneg _)
  have hS : 0 ≤ S := Finset.sum_nonneg fun n hn => hLnonneg n
  have hB := positiveCutoffDriftConstant_spec m P.b P.drift_measurable P.drift_bounded
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg hB.1 (norm_nonneg _))
      (mul_nonneg P.κ_pos.le (norm_nonneg _))
  have hH : 0 ≤ H := mul_nonneg hK (Real.sqrt_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; exact add_nonneg hS hH
  have hDistSqrt (t s : Icc (0 : ℝ) 1) : dist t s ≤ Real.sqrt (dist t s) := by
    have h0 : 0 ≤ dist t s := dist_nonneg
    have h1 : dist t s ≤ 1 := by
      change dist (t : ℝ) (s : ℝ) ≤ 1
      rw [Real.dist_eq]
      apply abs_le.mpr
      constructor <;> linarith [t.property.1, t.property.2, s.property.1, s.property.2]
    have hsqrt1 : Real.sqrt (dist t s) ≤ 1 := by
      calc
        Real.sqrt (dist t s) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
        _ = 1 := Real.sqrt_one
    have hmul := mul_le_mul_of_nonneg_right hsqrt1 (Real.sqrt_nonneg (dist t s))
    calc
      dist t s = Real.sqrt (dist t s) ^ 2 := (Real.sq_sqrt h0).symm
      _ = Real.sqrt (dist t s) * Real.sqrt (dist t s) := by ring
      _ ≤ 1 * Real.sqrt (dist t s) := hmul
      _ = Real.sqrt (dist t s) := by ring
  refine ⟨C, hC, ?_⟩
  intro N t s
  by_cases hN : m ≤ N
  · have hhigh := P.fourierPairing_modulus_of_cutoff_le hN c t s
    have hhigh' :
        |inner ℝ (P.scalarPath N t) w - inner ℝ (P.scalarPath N s) w| ≤
          H * Real.sqrt (dist t s) := by
      rw [← hc]
      calc
        |inner ℝ (P.scalarPath N t) (realFourierScalarMap m c) -
            inner ℝ (P.scalarPath N s) (realFourierScalarMap m c)| ≤
            K * (Real.sqrt (dist t s) * Real.sqrt P.gradientEnergyBound) := by
              simpa [K, mul_assoc] using hhigh
        _ = H * Real.sqrt (dist t s) := by dsimp [H]; ring
    calc
      |inner ℝ (P.scalarPath N t) w - inner ℝ (P.scalarPath N s) w| ≤
          H * Real.sqrt (dist t s) := hhigh'
      _ ≤ C * Real.sqrt (dist t s) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        dsimp [C]
        linarith
  · have hNm : N < m := Nat.lt_of_not_ge hN
    have hLS : L N ≤ S :=
      Finset.single_le_sum (fun n hn => hLnonneg n) (Finset.mem_range.mpr hNm)
    have hlip := P.scalarPath_pairing_lipschitz N w t s
    calc
      |inner ℝ (P.scalarPath N t) w - inner ℝ (P.scalarPath N s) w| ≤ L N * dist t s := by
        simpa [L] using hlip
      _ ≤ L N * Real.sqrt (dist t s) :=
        mul_le_mul_of_nonneg_left (hDistSqrt t s) (hLnonneg N)
      _ ≤ S * Real.sqrt (dist t s) :=
        mul_le_mul_of_nonneg_right hLS (Real.sqrt_nonneg _)
      _ ≤ C * Real.sqrt (dist t s) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        dsimp [C]
        linarith

end AVenhance.Infra.Parabolic.FourierGalerkin

end
