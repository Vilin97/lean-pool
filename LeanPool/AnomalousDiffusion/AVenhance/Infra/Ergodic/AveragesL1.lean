/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.BasicL1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.FourierDecay
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.LatticeDecay
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # The basic L¹ ergodic estimate -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open scoped ContDiff
open MeasureTheory
open Homogenization
open AVenhance.Infra.Torus

noncomputable section

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraErgodicAveragesL1MeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraErgodicAveragesL1MeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume
    : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraErgodicAveragesL1IsProbabilityMeasure3 : IsProbabilityMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem AveragesL1.toUnitTorus_isOpenQuotientMap (d : ℕ) :
    IsOpenQuotientMap (Torus.toUnitTorus d) := by
  let q : ℝ → UnitAddCircle := fun x => (x : UnitAddCircle)
  have hq : IsOpenQuotientMap q := by
    change IsOpenQuotientMap (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ))
    exact QuotientAddGroup.isOpenQuotientMap_mk
  change IsOpenQuotientMap (Pi.map (fun _ : Fin d => q))
  exact IsOpenQuotientMap.piMap (fun _ => hq)

theorem periodicToTorus_continuous_of_periodic {d : ℕ} {f : Vec d → ℂ}
    (hf : Continuous f) (hper : Torus.IsZdPeriodic f) :
    Continuous (Torus.periodicToTorus f) := by
  have hquot := AveragesL1.toUnitTorus_isOpenQuotientMap d
  apply hquot.continuous_comp_iff.mp
  have hcomp : Continuous
      (Torus.fromUnitTorus (Torus.periodicToTorus f)) := by
    rw [Torus.fromUnitTorus_periodicToTorus hper]
    exact hf
  exact hcomp

theorem AveragesL1.unitCell_subset_closedCube (d : ℕ) :
    Torus.unitCell d ⊆ Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1 := by
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, by simpa using (hx i).2⟩

theorem integrable_periodicToTorus_of_locallyIntegrable {d : ℕ}
    {g : Vec d → ℝ} (hg : LocallyIntegrable g (volume : Measure (Vec d))) :
    Integrable (Torus.periodicToTorus g) (volume : Measure (UnitTorus d)) := by
  let Q : Set (Vec d) := Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1
  have hQcompact : IsCompact Q := by
    simpa [Q] using isCompact_univ_pi fun _ : Fin d => isCompact_Icc
  have hQint : IntegrableOn g Q (volume : Measure (Vec d)) := hg.integrableOn_isCompact hQcompact
  have hcell : IntegrableOn g (Torus.unitCell d) (volume : Measure (Vec d)) :=
    hQint.mono_set (AveragesL1.unitCell_subset_closedCube d)
  have hsub : Integrable (fun x : Torus.unitCell d => g x.1)
      ((volume : Measure (Vec d)).comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal (f := g) (s := Torus.unitCell d)
      (μ := (volume : Measure (Vec d))) (Torus.measurableSet_unitCell d)).mp hcell
  have hmp := UnitAddTorus.measurePreserving_equivPiIoc
    (a := fun _ : Fin d => (0 : ℝ))
  have hLp : MemLp (fun x : Torus.unitCell d => g x.1) 1
      ((volume : Measure (Vec d)).comap Subtype.val) :=
    memLp_one_iff_integrable.mpr hsub
  have hLpcomp := hLp.comp_measurePreserving hmp
  have hcomp := memLp_one_iff_integrable.mp hLpcomp
  have hcomp' : Integrable
      (fun x : UnitTorus d =>
        g ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d => (0 : ℝ)) x).val))
      (volume : Measure (UnitTorus d)) := by
    convert hcomp using 1; rfl
  have heq : (fun x : UnitTorus d =>
      g ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d => (0 : ℝ)) x).val)) =
      Torus.periodicToTorus g := by
    funext x
    rfl
  rw [heq] at hcomp'
  exact hcomp'

theorem AveragesL1.smoothFourierCoeff_eq_mFourierCoeff_periodicToTorus
    {d : ℕ} {f : Vec d → ℂ} (hper : Torus.IsZdPeriodic f)
    (hf : Continuous f) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff
      (⟨Torus.periodicToTorus f,
        periodicToTorus_continuous_of_periodic hf hper⟩ :
          ContinuousMap (UnitTorus d) ℂ) k =
      smoothFourierCoeff f k := by
  have hchar (x : UnitTorus d) :
      Torus.torusCharacter k (Torus.unitTorusRepresentative d x) =
        UnitAddTorus.mFourier (-k) x := by
    simp [Torus.torusCharacter, Torus.toUnitTorus_unitTorusRepresentative]
  change (∫ x : UnitTorus d,
      UnitAddTorus.mFourier (-k) x • Torus.periodicToTorus f x) = _
  simp only [smul_eq_mul]
  change (∫ x : UnitTorus d,
      UnitAddTorus.mFourier (-k) x * Torus.periodicToTorus f x) =
    ∫ x in Torus.unitCell d, Torus.torusCharacter k x * f x
  rw [← Torus.integral_periodicToTorus_eq_unitCell
    (fun y => Torus.torusCharacter k y * f y)]
  apply integral_congr_ae
  filter_upwards with x
  rw [← hchar x]
  rfl

theorem fastFrequency_norm_ge_nat {d N : ℕ} (hN : 0 < N)
    {k : Fin d → ℤ} (hk0 : k ≠ 0) (hk : IsFastFrequency N k) :
    (N : ℝ) ≤ ‖k‖ := by
  obtain ⟨i, hi⟩ : ∃ i : Fin d, k i ≠ 0 := by
    by_contra h
    push Not at h
    apply hk0
    funext i
    exact h i
  obtain ⟨m, hm⟩ := hk i
  have hm0 : m ≠ 0 := by
    intro hmz
    apply hi
    rw [hm, hmz]
    simp
  have hcoord : (N : ℝ) ≤ |(k i : ℝ)| := by
    rw [hm, Int.cast_mul, abs_mul]
    have hmabs : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
      exact_mod_cast this
    have hNnonneg : (0 : ℝ) ≤ ((N : ℤ) : ℝ) := by positivity
    calc
      (N : ℝ) = ((N : ℤ) : ℝ) * 1 := by simp
      _ ≤ ((N : ℤ) : ℝ) * |(m : ℝ)| := mul_le_mul_of_nonneg_left hmabs hNnonneg
      _ = |((N : ℤ) : ℝ)| * |(m : ℝ)| := by
        rw [abs_of_nonneg hNnonneg]
  have hcoord_norm : |(k i : ℝ)| ≤ ‖k‖ := by
    have hp := norm_le_pi_norm k i
    simpa [Int.norm_eq_abs, Int.cast_abs] using hp
  exact hcoord.trans hcoord_norm

theorem AveragesL1.periodicToTorus_eq_torusFunction {d : ℕ} {α : Type*}
    (f : Vec d → α) : Torus.periodicToTorus f = torusFunction f := by
  rfl

private theorem cell_average_product_coefficient_bound :
  ∀ {d : ℕ},
    OfNat.ofNat 0 < d →
      ∀ {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (Cf r : ℝ),
        OfNat.ofNat 0 ≤ Cf →
          OfNat.ofNat 0 < r →
            HasCoordinateAnalyticL1Bounds (fun (x : Vec d) => Complex.ofReal (f x)) Cf r →
              ∀ (hperC : IsZdPeriodic fun (x : Vec d) => Complex.ofReal (f x)),
                let F : ContinuousMap (UnitTorus d) ℂ :=
                  ⟨Torus.periodicToTorus (fun x => (f x : ℂ)),
                    periodicToTorus_continuous_of_periodic
                      (Complex.continuous_ofReal.comp hf.continuous) hperC⟩;
                (∀ (k : Fin d → ℤ),
                    UnitAddTorus.mFourierCoeff (DFunLike.coe F) k =
                      smoothFourierCoeff (fun (x : Vec d) => Complex.ofReal (f x)) k) →
                  let M : ℝ := ∫ x : UnitTorus d, ‖F x‖;
                  OfNat.ofNat 0 ≤ M →
                    let B : ℝ := 512 * Cf + 2 * M;
                    OfNat.ofNat 512 * Cf ≤ B →
                      OfNat.ofNat 2 * M ≤ B →
                        ∀ (k : Fin d → ℤ),
                          ‖UnitAddTorus.mFourierCoeff (DFunLike.coe F) k‖ ≤ B * Real.exp (-(r /
                              OfNat.ofNat 512) * ‖k‖)
    := by
  intro d hd f hf Cf r hCf hr hderiv hperC F hFcoeff M hM B hBcf hBM k
  by_cases hk0 : k = 0
  · subst k
    have hcoeff := mFourierCoeff_norm_le_integral_norm F (0 : Fin d → ℤ)
    rw [show (0 : Fin d → ℤ) = 0 from rfl] at hcoeff
    rw [show Real.exp (-(r / 512) * ‖(0 : Fin d → ℤ)‖) = 1 by simp]
    calc
      ‖UnitAddTorus.mFourierCoeff F 0‖ ≤ M := by simpa [M] using hcoeff
      _ ≤ B := by dsimp [B]; linarith
      _ = B * 1 := by ring
  · by_cases hlarge : 1 ≤ r * ‖k‖
    · rw [hFcoeff]
      have hdec := smoothFourierCoeff_expDecay_of_coordinateAnalyticL1Bounds
        hd (Complex.ofRealCLM.contDiff.comp hf) hperC Cf r hCf hr hderiv k hk0 hlarge
      calc
        ‖smoothFourierCoeff (fun x => (f x : ℂ)) k‖ ≤
            512 * Cf * Real.exp (-r * ‖k‖ / 512) :=
          hdec
        _ = 512 * Cf * Real.exp (-(r / 512) * ‖k‖) := by congr 2; ring
        _ ≤ B * Real.exp (-(r / 512) * ‖k‖) := by
          exact mul_le_mul_of_nonneg_right hBcf (Real.exp_nonneg _)
    · have hsmall : r * ‖k‖ < 1 := lt_of_not_ge hlarge
      have harg : (r / 512) * ‖k‖ < 1 / 512 := by
        nlinarith
      have hw : (1 / 2 : ℝ) ≤ Real.exp (-(r / 512) * ‖k‖) := by
        have hlinear : 1 / 2 ≤ 1 - (r / 512) * ‖k‖ := by linarith
        have hexp := Real.add_one_le_exp (-((r / 512) * ‖k‖))
        have hexp' : 1 - (r / 512) * ‖k‖ ≤
            Real.exp (-(r / 512) * ‖k‖) := by
          calc
            1 - (r / 512) * ‖k‖ = -((r / 512) * ‖k‖) + 1 := by ring
            _ ≤ Real.exp (-((r / 512) * ‖k‖)) := hexp
            _ = Real.exp (-(r / 512) * ‖k‖) := by congr 1; ring
        calc
          (1 / 2 : ℝ) ≤ 1 - (r / 512) * ‖k‖ := hlinear
          _ ≤ Real.exp (-(r / 512) * ‖k‖) := hexp'
      have hcoeff := mFourierCoeff_norm_le_integral_norm F k
      have hlow : M ≤ 2 * M * Real.exp (-(r / 512) * ‖k‖) := by
        have := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 2 * M)
        nlinarith
      calc
        ‖UnitAddTorus.mFourierCoeff F k‖ ≤ M := by simpa [M] using hcoeff
        _ ≤ 2 * M * Real.exp (-(r / 512) * ‖k‖) := hlow
        _ ≤ B * Real.exp (-(r / 512) * ‖k‖) :=
          mul_le_mul_of_nonneg_right hBM (Real.exp_nonneg _)

/-- The basic ergodic covariance estimate. Its analytic premise is given in
coordinate form, since only repeated coordinate derivatives enter the Fourier
multiplier proof. The proof needs `r > 0`, `Cf ≥ 0`, and `Nr ≥ 1`; it does not
use the paper's extra upper bound `r ≤ 1`. -/
theorem cellAverage_mul_sub_le_of_coordinateAnalyticL1Bounds
    {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (hper : IsZPeriodic f)
    (Cf r : ℝ) (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hderiv : HasCoordinateAnalyticL1Bounds (fun x => (f x : ℂ)) Cf r)
    {g : Vec d → ℝ} (hg : LocallyIntegrable g (volume : Measure (Vec d)))
    (hfast : IsFastPeriodic N g) (hNr : 1 ≤ r * (N : ℝ)) :
    |cellAverage (fun x => f x * g x) - cellAverage f * cellAverage g| ≤
      512 * Cf * cellAverage (fun x => |g x|) *
        (∑' k : Fin d → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) *
        Real.exp (-(r * (N : ℝ)) / 1024) := by
  classical
  have hperC : Torus.IsZdPeriodic (fun x => (f x : ℂ)) := by
    intro k x
    exact congrArg Complex.ofReal (hper x k)
  let F : ContinuousMap (UnitTorus d) ℂ :=
    ⟨Torus.periodicToTorus (fun x => (f x : ℂ)),
      periodicToTorus_continuous_of_periodic
        (Complex.continuous_ofReal.comp hf.continuous) hperC⟩
  let G : UnitTorus d → ℂ := fun x =>
    ((Torus.periodicToTorus g x : ℝ) : ℂ)
  have hGreal : Integrable (Torus.periodicToTorus g)
      (volume : Measure (UnitTorus d)) :=
    integrable_periodicToTorus_of_locallyIntegrable hg
  have hG : Integrable G (volume : Measure (UnitTorus d)) := by
    exact hGreal.ofReal
  have hGinv : ∀ i x, G (x + fastTorusShift N i) = G x := by
    intro i x
    rw [show G = fun y => ((torusFunction g y : ℝ) : ℂ) by
      funext y
      exact congrArg Complex.ofReal
        (congrFun (AveragesL1.periodicToTorus_eq_torusFunction g) y)]
    exact congrArg Complex.ofReal
      (torusFunction_add_fastTorusShift_eq hN hfast i x)
  have hFcoeff (k : Fin d → ℤ) :
      UnitAddTorus.mFourierCoeff F k =
        smoothFourierCoeff (fun x => (f x : ℂ)) k := by
    exact AveragesL1.smoothFourierCoeff_eq_mFourierCoeff_periodicToTorus hperC
      (Complex.continuous_ofReal.comp hf.continuous) k
  have hrate : 0 < r / 512 := by positivity
  have hweightSummable : Summable
      (fun k : Fin d → ℤ => Real.exp (-(r / 512) * ‖k‖)) :=
    summable_exp_neg_piNorm (by positivity)
  let M : ℝ := ∫ x : UnitTorus d, ‖F x‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg (fun _ => norm_nonneg _)
  let B : ℝ := 512 * Cf + 2 * M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBcf : 512 * Cf ≤ B := by dsimp [B]; linarith
  have hBM : 2 * M ≤ B := by dsimp [B]; linarith
  have hcoeffBound : ∀ k : Fin d → ℤ,
      ‖UnitAddTorus.mFourierCoeff F k‖ ≤
        B * Real.exp (-(r / 512) * ‖k‖) := by
    exact @cell_average_product_coefficient_bound d hd f hf Cf r hCf hr hderiv hperC hFcoeff hM
        hBcf hBM
  have hmajor : Summable (fun k : Fin d → ℤ =>
      B * Real.exp (-(r / 512) * ‖k‖)) := hweightSummable.mul_left B
  have hcoeffNormSummable : Summable (fun k : Fin d → ℤ =>
      ‖UnitAddTorus.mFourierCoeff F k‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hcoeffBound
  have hFsum : Summable (UnitAddTorus.mFourierCoeff F) :=
    summable_norm_iff.mp hcoeffNormSummable
  have htail : Summable (fun k : Fin d → ℤ =>
      if k = 0 then 0 else if IsFastFrequency N k then
        Real.exp (-(r / 512) * ‖k‖) else 0) := by
    apply hweightSummable.of_nonneg_of_le
    · intro k
      by_cases hk0 : k = 0
      · simp [hk0]
      · by_cases hfast : IsFastFrequency N k
        · simpa [hk0, hfast] using Real.exp_nonneg (-(r / 512) * ‖k‖)
        · simp [hk0, hfast]
    · intro k
      by_cases hk0 : k = 0
      · simp [hk0]
      · by_cases hfast : IsFastFrequency N k
        · simp [hk0, hfast]
        · simp only [hk0, ↓reduceIte, hfast, neg_mul]
          exact Real.exp_nonneg _
  have hzero : ∀ k : Fin d → ℤ, k ≠ 0 → ¬ IsFastFrequency N k →
      UnitAddTorus.mFourierCoeff G (-k) = 0 := by
    intro k hk0 hnot
    apply mFourierCoeff_eq_zero_of_not_fastFrequencyLattice hN (-k) hGinv
    intro hneg
    apply hnot
    intro i
    have hi := hneg i
    simpa [IsFastFrequency] using hi
  have hdecay : ∀ k : Fin d → ℤ, k ≠ 0 → IsFastFrequency N k →
      ‖UnitAddTorus.mFourierCoeff F k‖ ≤
        (512 * Cf) * Real.exp (-(r / 512) * ‖k‖) := by
    intro k hk0 hfast
    have hkN := fastFrequency_norm_ge_nat hN hk0 hfast
    have hlarge : 1 ≤ r * ‖k‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hkN hr.le]
    calc
      ‖UnitAddTorus.mFourierCoeff F k‖ =
          ‖smoothFourierCoeff (fun x => (f x : ℂ)) k‖ := by rw [hFcoeff]
      _ ≤ 512 * Cf * Real.exp (-r * ‖k‖ / 512) :=
        smoothFourierCoeff_expDecay_of_coordinateAnalyticL1Bounds
          hd (Complex.ofRealCLM.contDiff.comp hf) hperC Cf r hCf hr hderiv k hk0 hlarge
      _ = 512 * Cf * Real.exp (-(r / 512) * ‖k‖) := by congr 2; ring
  have htailBound := fastFrequency_expTail_le (d := d) (N := N) hN hrate
    (t := r / 512) (by nlinarith [hNr])
  have hcov := torusCovariance_le_fourier_envelope F G hG hFsum
    (512 * Cf) (r / 512) (by positivity) hdecay hzero htail
  have hGint : ∫ x : UnitTorus d, G x = (cellAverage g : ℂ) := by
    calc
      _ = ∫ x : UnitTorus d, ((torusFunction g x : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards with x
        exact congrArg Complex.ofReal
          (congrFun (AveragesL1.periodicToTorus_eq_torusFunction g) x)
      _ = (∫ x : UnitTorus d, torusFunction g x : ℝ) := integral_complex_ofReal
      _ = (cellAverage g : ℂ) :=
        congrArg Complex.ofReal (cellAverage_eq_torus_integral g).symm
  have hFint : ∫ x : UnitTorus d, F x = (cellAverage f : ℂ) := by
    calc
      _ = ∫ x : UnitTorus d, ((torusFunction f x : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards with x
        exact congrArg Complex.ofReal
          (congrFun (AveragesL1.periodicToTorus_eq_torusFunction f) x)
      _ = (∫ x : UnitTorus d, torusFunction f x : ℝ) := integral_complex_ofReal
      _ = (cellAverage f : ℂ) :=
        congrArg Complex.ofReal (cellAverage_eq_torus_integral f).symm
  have hproduct : ∫ x : UnitTorus d, F x * G x =
      (cellAverage (fun x => f x * g x) : ℂ) := by
    calc
      _ = ∫ x : UnitTorus d,
          ((torusFunction (fun y => f y * g y) x : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [F, G, ContinuousMap.coe_mk]
        rw [AveragesL1.periodicToTorus_eq_torusFunction (fun y => (f y : ℂ)),
          AveragesL1.periodicToTorus_eq_torusFunction g]
        change ((torusFunction f x : ℝ) : ℂ) *
            ((torusFunction g x : ℝ) : ℂ) =
          ((torusFunction (fun y => f y * g y) x : ℝ) : ℂ)
        simp [torusFunction]
      _ = (∫ x : UnitTorus d,
          torusFunction (fun y => f y * g y) x : ℝ) := integral_complex_ofReal
      _ = (cellAverage (fun x => f x * g x) : ℂ) :=
        congrArg Complex.ofReal (cellAverage_eq_torus_integral _).symm
  have hGnorm : ∫ x : UnitTorus d, ‖G x‖ = cellAverage (fun x => |g x|) := by
    calc
      _ = ∫ x : UnitTorus d, |torusFunction g x| := by
        apply integral_congr_ae
        filter_upwards with x
        simp [G, AveragesL1.periodicToTorus_eq_torusFunction]
      _ = ∫ x : UnitTorus d, torusFunction (fun y => |g y|) x := by
        apply integral_congr_ae
        filter_upwards with x
        simp [torusFunction]
      _ = cellAverage (fun x => |g x|) :=
        (cellAverage_eq_torus_integral _).symm
  have hmain := hcov
  rw [hproduct, hFint, hGint, hGnorm] at hmain
  have htailBound' : (∑' k : Fin d → ℤ,
      if k = 0 then 0 else if IsFastFrequency N k then
        Real.exp (-(r / 512) * ‖k‖) else 0) ≤
      (∑' k : Fin d → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) *
        Real.exp (-(r * (N : ℝ)) / 1024) := by
    calc
      _ ≤ (∑' k : Fin d → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) *
          Real.exp (-((r / 512) * (N : ℝ)) / 2) := htailBound
      _ = _ := by congr 2; ring
  have hscalar : |cellAverage (fun x => f x * g x) -
      cellAverage f * cellAverage g| ≤
      (512 * Cf * cellAverage (fun x => |g x|)) *
        ((∑' k : Fin d → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) *
          Real.exp (-(r * (N : ℝ)) / 1024)) := by
    have hnonneg : 0 ≤
        (512 * Cf * cellAverage (fun x => |g x|)) := by
      apply mul_nonneg
      · exact mul_nonneg (by norm_num) hCf
      · unfold cellAverage
        apply integral_nonneg
        intro x
        exact abs_nonneg _
    have hnormeq : ‖((cellAverage (fun x => f x * g x) -
        cellAverage f * cellAverage g : ℝ) : ℂ)‖ =
        |cellAverage (fun x => f x * g x) - cellAverage f * cellAverage g| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [← hnormeq]
    calc
      _ ≤ (512 * Cf * cellAverage (fun x => |g x|)) *
            (∑' k : Fin d → ℤ,
              if k = 0 then 0 else if IsFastFrequency N k then
                Real.exp (-(r / 512) * ‖k‖) else 0) := by
          simpa [hproduct, hFint, hGint, hGnorm, mul_assoc] using hmain
      _ ≤ _ := mul_le_mul_of_nonneg_left htailBound' hnonneg
  simpa [mul_assoc, mul_left_comm, mul_comm] using hscalar

end

end AVenhance.Infra.Ergodic
