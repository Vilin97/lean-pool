/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.ScalarPath
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Frequency
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Modes
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Projection
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integral paths for weak Fourier coefficients

Testing the weak equation by a spatial Fourier mode and a smooth time factor gives an
ordinary scalar weak equation. The scalar reconstruction lemma then identifies each coefficient
with its absolutely continuous forcing path.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Parabolic.WeakUniqueness

theorem ModePath.modePath_timeCube_measure_eq_product :
    (volume.restrict AVenhance.timeCube) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube) := by
  rw [AVenhance.timeCube, Measure.prod_restrict,
    ← Measure.volume_eq_prod ℝ (Vec 2)]

theorem ModePath.modePath_timeMeasure_Ioo_eq_Ioc :
    volume.restrict (Set.Ioo (0 : ℝ) 1) =
      volume.restrict (Set.Ioc (0 : ℝ) 1) :=
  Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc

theorem ModePath.modePath_integral_timeCube_eq_interval_cell {F : ℝ × Vec 2 → ℝ}
    (hF : Integrable F (volume.restrict AVenhance.timeCube)) :
    ∫ p in AVenhance.timeCube, F p =
      ∫ t in (0 : ℝ)..1, ∫ x in AVenhance.unitCube, F (t, x) := by
  have hproduct : Integrable F
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube)) := by
    rwa [← ModePath.modePath_timeCube_measure_eq_product]
  calc
    ∫ p in AVenhance.timeCube, F p =
        ∫ t, ∫ x, F (t, x) ∂(volume.restrict AVenhance.unitCube)
        ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
            rw [ModePath.modePath_timeCube_measure_eq_product, integral_prod F hproduct]
    _ = ∫ t, ∫ x, F (t, x) ∂(volume.restrict AVenhance.unitCube)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
            rw [ModePath.modePath_timeMeasure_Ioo_eq_Ioc]
    _ = ∫ t in (0 : ℝ)..1, ∫ x in AVenhance.unitCube, F (t, x) := by
            symm
            exact intervalIntegral.integral_of_le (by norm_num)

theorem ModePath.modePath_intervalIntegrable_of_timeCube_integrable
    {F : ℝ × Vec 2 → ℝ} (hF : Integrable F (volume.restrict AVenhance.timeCube)) :
    IntervalIntegrable
      (fun t => ∫ x in AVenhance.unitCube, F (t, x)) volume 0 1 := by
  have hproduct : Integrable F
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube)) := by
    rwa [← ModePath.modePath_timeCube_measure_eq_product]
  have htime : Integrable (fun t => ∫ x, F (t, x)
      ∂(volume.restrict AVenhance.unitCube))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := hproduct.integral_prod_left
  have htime' : Integrable (fun t => ∫ x, F (t, x)
      ∂(volume.restrict AVenhance.unitCube))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [← ModePath.modePath_timeMeasure_Ioo_eq_Ioc]
    exact htime
  rw [intervalIntegrable_iff, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact htime'

/-- Cell pairing with one smooth periodic spatial test. -/
def weakModePairing (u : ℝ → Vec 2 → ℝ) (ψ : Vec 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in AVenhance.unitCube, u t x * ψ x

/-- The scalar forcing seen by a smooth spatial weak test. -/
def weakModeForcing (b : ℝ → Vec 2 → Vec 2) (κ : ℝ)
    (D : ℝ → Vec 2 → Vec 2) (ψ : Vec 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in AVenhance.unitCube,
    Homogenization.vecDot (b t x) (D t x) * ψ x +
      κ * Homogenization.vecDot (D t x) (AVenhance.spaceGrad ψ x)

theorem ModePath.modePath_timeCube_measurable : MeasurableSet AVenhance.timeCube := by
  rw [AVenhance.timeCube]
  refine measurableSet_Ioo.prod ?_
  unfold AVenhance.unitCube
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

theorem ModePath.modePath_continuous_joint_bound {F : ℝ × Vec 2 → ℝ}
    (hF : Continuous F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ p ∂(volume.restrict AVenhance.timeCube), ‖F p‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := weak_continuous_timeCube_bound hF
  refine ⟨C, hC, ?_⟩
  filter_upwards [ae_restrict_mem ModePath.modePath_timeCube_measurable] with p hp
  exact hbound p hp

private theorem weak_solution_mode_integral_path_weakScalar1 :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} {κ : ℝ} {f : Vec (2 : ℕ) → ℝ} {u : ℝ → Vec (2 : ℕ) → ℝ}
    {D : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)}, MemL2On unitCube f → ∀ {ψ : Vec (2 : ℕ) → ℝ}, ContDiff
    ℝ ∞ ψ → IsZ2Periodic ψ → (∀ t ∈ Icc (0 : ℝ) (1 : ℝ), IsZ2Periodic (u t) ∧ MemL2On unitCube
    (u t)) → MemLp (fun (p : ℝ × Vec (2 : ℕ)) => u p.1 p.2) (2 : ENNReal) (volume.restrict
    timeCube) → (∀ (φ : ℝ → Vec (2 : ℕ) → ℝ), IsTestFunction φ → ∫ (p : ℝ × Vec (2 : ℕ)) in
    timeCube, -u p.1 p.2 * deriv (fun (s : ℝ) => φ s p.2) p.1 + vecDot (b p.1 p.2) (D p.1 p.2) *
    φ p.1 p.2 + κ * vecDot (D p.1 p.2) (spaceGrad (φ p.1) p.2) = ∫ (x : Vec (2 : ℕ)) in
    unitCube, f x * φ (0 : ℝ) x) →
  let q : ℝ → ℝ := weakModeForcing b κ D ψ;
  let uψ : ℝ → ℝ := weakModePairing u ψ;
  let u₀ψ : ℝ := weakModePairing (fun (_ : ℝ) (x_1 : Vec (2 : ℕ)) => f x_1) ψ (0 : ℝ);
  ContDiff ℝ (1 : ℕ∞ω) ψ → MemL2On unitCube ψ → ContinuousOn uψ (Icc (0 : ℝ) (1 : ℝ)) →
    Integrable (fun (p : ℝ × Vec (2 : ℕ)) => vecDot (b p.1 p.2) (D p.1 p.2) * ψ p.2 + κ * vecDot
    (D p.1 p.2) (spaceGrad ψ p.2)) (volume.restrict timeCube) → IntervalIntegrable q volume (0 :
    ℝ) (1 : ℝ) → ∀ (η : ℝ → ℝ), ContDiff ℝ ∞ η → (∀ (t : ℝ), (1 : ℝ) ≤ t → η t = (0 : ℝ)) → ∫ (t
    : ℝ) in (0 : ℝ)..(1 : ℝ), -uψ t * deriv η t + q t * η t = u₀ψ * η (0 : ℝ)
    := by
  intro b κ f u D hf ψ hψ hψper hpoint hscalar hweak q uψ u₀ψ hψone hψmem huψcont hqjoint hqInt η
      hη hηterminal
  let φ : ℝ → Vec 2 → ℝ := fun t x => η t * ψ x
  have hφsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 * ψ p.2)
    exact (hη.comp contDiff_fst).mul (hψ.comp contDiff_snd)
  have hφper : ∀ t, AVenhance.IsZ2Periodic (φ t) := by
    intro t k x
    simp [φ, hψper k x]
  have hφterminal : ∀ t, 1 ≤ t → ∀ x, φ t x = 0 := by
    intro t ht x
    simp [φ, hηterminal t ht]
  have htest : AVenhance.IsTestFunction φ := ⟨hφsmooth, hφper, hφterminal⟩
  have hweakEq := hweak φ htest
  let timeTest : ℝ × Vec 2 → ℝ := fun p => deriv η p.1 * ψ p.2
  let forcing : ℝ × Vec 2 → ℝ := fun p =>
    Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) * ψ p.2 +
      κ * Homogenization.vecDot (D p.1 p.2) (AVenhance.spaceGrad ψ p.2)
  let first : ℝ × Vec 2 → ℝ := fun p =>
    -(u p.1 p.2 * timeTest p)
  let second : ℝ × Vec 2 → ℝ := fun p => η p.1 * forcing p
  have htimeTestCont : Continuous timeTest := by
    exact hη.continuous_deriv (by simp) |>.comp continuous_fst |>.mul
      (hψ.continuous.comp continuous_snd)
  have htimeTestL2 : MemLp timeTest 2
      (volume.restrict AVenhance.timeCube) :=
    weak_continuous_memLp_two_timeCube htimeTestCont
  have hfirstInt : Integrable first (volume.restrict AVenhance.timeCube) := by
    exact weak_product_integrable_timeCube hscalar htimeTestL2 |>.neg
  have hηjoint : Continuous (fun p : ℝ × Vec 2 => η p.1) :=
    hη.continuous.comp continuous_fst
  obtain ⟨_Cη, _hCη, hηbound⟩ := ModePath.modePath_continuous_joint_bound hηjoint
  have hsecondInt : Integrable second (volume.restrict AVenhance.timeCube) := by
    have hmul := hqjoint.mul_bdd hηjoint.measurable.aestronglyMeasurable hηbound
    apply hmul.congr
    filter_upwards with p
    simp [second, forcing]
    ring
  have hderiv (t : ℝ) (x : Vec 2) : deriv (fun s => φ s x) t = timeTest (t, x) := by
    dsimp [timeTest, φ]
    have hd := (hη.differentiable (by simp) t).hasDerivAt.mul_const (ψ x)
    exact hd.deriv
  have hgrad (t : ℝ) (x : Vec 2) (i : Fin 2) :
      AVenhance.spaceGrad (φ t) x i = η t * AVenhance.spaceGrad ψ x i := by
    change fderiv ℝ (η t • ψ) x (Homogenization.basisVec i) = _
    have hdiff := (hψone.differentiable (by norm_num) x)
    rw [fderiv_const_smul hdiff (η t)]
    rfl
  have hintegrand (p : ℝ × Vec 2) :
      AVenhance.Infra.Parabolic.WeakUniqueness.weakEquationIntegrand
          b κ u D φ p = first p + second p := by
    rcases p with ⟨t, x⟩
    have hgradVec : AVenhance.spaceGrad (φ t) x = η t • AVenhance.spaceGrad ψ x := by
      funext i
      exact hgrad t x i
    simp only [AVenhance.Infra.Parabolic.WeakUniqueness.weakEquationIntegrand,
      first, second, timeTest, forcing]
    rw [hderiv t x, hgradVec]
    simp [φ, Homogenization.vecDot]
    ring
  have hweakSplit :
      (∫ p in AVenhance.timeCube,
        AVenhance.Infra.Parabolic.WeakUniqueness.weakEquationIntegrand b κ u D φ p) =
        (∫ p in AVenhance.timeCube, first p) +
          ∫ p in AVenhance.timeCube, second p := by
    calc
      _ = ∫ p in AVenhance.timeCube, first p + second p := by
        exact integral_congr_ae
          (Filter.Eventually.of_forall fun p => hintegrand p)
      _ = _ := integral_add hfirstInt hsecondInt
  have hfirstFubini := ModePath.modePath_integral_timeCube_eq_interval_cell hfirstInt
  have hsecondFubini := ModePath.modePath_integral_timeCube_eq_interval_cell hsecondInt
  have hfirstInner : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      (∫ x in AVenhance.unitCube, first (t, x)) = -(uψ t) * deriv η t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    have hcell : Integrable (fun x => u t x * ψ x)
        (volume.restrict AVenhance.unitCube) :=
      weak_product_integrable_cell (hpoint t htcc).2 hψmem
    calc
      ∫ x in AVenhance.unitCube, first (t, x) =
          deriv η t * (-(∫ x in AVenhance.unitCube, u t x * ψ x)) := by
            calc
              _ = ∫ x in AVenhance.unitCube,
                  deriv η t * (-(u t x * ψ x)) := by
                    apply integral_congr_ae
                    filter_upwards [ae_restrict_mem (by
                      unfold AVenhance.unitCube
                      exact MeasurableSet.pi Set.countable_univ
                        (fun _ _ => measurableSet_Ioo))] with x hx
                    simp only [first, timeTest]
                    ring
              _ = deriv η t * (-(∫ x in AVenhance.unitCube,
                  u t x * ψ x)) := by rw [integral_const_mul, integral_neg]
      _ = -(uψ t) * deriv η t := by
            simp [uψ, weakModePairing]
            ring
  have hsecondInner : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      (∫ x in AVenhance.unitCube, second (t, x)) = q t * η t := by
    have hqprod : Integrable forcing
        ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
          (volume.restrict AVenhance.unitCube)) := by
      rw [← ModePath.modePath_timeCube_measure_eq_product]
      exact hqjoint
    have hsections := hqprod.prod_right_ae
    have hsectionsIoo : ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        Integrable (fun x => forcing (t, x))
          (volume.restrict AVenhance.unitCube) := by
      simpa [forcing, ModePath.modePath_timeCube_measure_eq_product] using hsections
    have hsectionsIoc : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        Integrable (fun x => forcing (t, x))
          (volume.restrict AVenhance.unitCube) := by
      rw [← ModePath.modePath_timeMeasure_Ioo_eq_Ioc]
      exact hsectionsIoo
    filter_upwards [hsectionsIoc] with t hsection
    calc
      ∫ x in AVenhance.unitCube, second (t, x) =
          η t * ∫ x in AVenhance.unitCube, forcing (t, x) := by
            dsimp [second]
            rw [integral_const_mul]
      _ = q t * η t := by
            dsimp [q, weakModeForcing]
            ring
  have hsecondInnerEq :
      (fun t => ∫ x in AVenhance.unitCube, second (t, x)) =ᵐ[
        volume.restrict (Set.Ioc (0 : ℝ) 1)] fun t => q t * η t := by
    filter_upwards [hsecondInner] with t ht
    exact ht
  have hsecondInnerInt :
      ∫ t in (0 : ℝ)..1, (∫ x in AVenhance.unitCube, second (t, x)) =
        ∫ t in (0 : ℝ)..1, q t * η t := by
    exact intervalIntegral.integral_congr_ae_restrict
      (by simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hsecondInnerEq)
  have hfirstInnerEq :
      (fun t => ∫ x in AVenhance.unitCube, first (t, x)) =ᵐ[
        volume.restrict (Set.Ioc (0 : ℝ) 1)] fun t => -(uψ t) * deriv η t := by
    filter_upwards [hfirstInner] with t ht
    exact ht
  have hfirstInnerInt :
      ∫ t in (0 : ℝ)..1, (∫ x in AVenhance.unitCube, first (t, x)) =
        ∫ t in (0 : ℝ)..1, -(uψ t) * deriv η t := by
    exact intervalIntegral.integral_congr_ae_restrict
      (by simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hfirstInnerEq)
  have hinitial :
      ∫ x in AVenhance.unitCube, f x * φ 0 x = u₀ψ * η 0 := by
    have hprod := weak_product_integrable_cell hf hψmem
    have hcalc : (fun x => f x * (η 0 * ψ x)) =
        fun x => η 0 * (f x * ψ x) := by
      funext x
      ring
    rw [show φ 0 = fun x => η 0 * ψ x by rfl, hcalc, integral_const_mul]
    simp [u₀ψ, weakModePairing]
    ring
  change (∫ p in AVenhance.timeCube,
      AVenhance.Infra.Parabolic.WeakUniqueness.weakEquationIntegrand b κ u D φ p) =
    ∫ x in AVenhance.unitCube, f x * φ 0 x at hweakEq
  calc
    ∫ t in (0 : ℝ)..1, (-(uψ t) * deriv η t + q t * η t) =
        (∫ t in (0 : ℝ)..1, -(uψ t) * deriv η t) +
          ∫ t in (0 : ℝ)..1, q t * η t := by
            have hηderivCont : Continuous (deriv η) := hη.continuous_deriv (by simp)
            have hfirstScCont : ContinuousOn (fun t => -(uψ t) * deriv η t)
                (Set.Icc (0 : ℝ) 1) := huψcont.neg.mul hηderivCont.continuousOn
            have hfirstScInt : IntervalIntegrable
                (fun t => -(uψ t) * deriv η t) volume 0 1 :=
              hfirstScCont.intervalIntegrable_of_Icc (by norm_num)
            have hsecondScInt : IntervalIntegrable (fun t => q t * η t) volume 0 1 :=
              hqInt.mul_continuousOn hη.continuous.continuousOn
            exact intervalIntegral.integral_add hfirstScInt hsecondScInt
    _ = (∫ p in AVenhance.timeCube, first p) +
          ∫ p in AVenhance.timeCube, second p := by
            rw [← hfirstInnerInt, ← hsecondInnerInt, ← hfirstFubini, ← hsecondFubini]
    _ = ∫ x in AVenhance.unitCube, f x * φ 0 x := by
      rw [← hweakSplit, hweakEq]
    _ = u₀ψ * η 0 := hinitial

/-- Every fixed smooth periodic Fourier coefficient of a weak solution satisfies its
integral equation on the whole closed time interval. -/
theorem weak_solution_mode_integral_path
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D)
    (hf : MemL2On AVenhance.unitCube f)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψper : AVenhance.IsZ2Periodic ψ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      weakModePairing u ψ t = weakModePairing (fun _ x => f x) ψ 0 -
        ∫ s in (0 : ℝ)..t, weakModeForcing b κ D ψ s := by
  rcases hu with ⟨hpoint, _hbound, hscalar, hgradient, _hH1, hdrift, hpairing, hweak⟩
  let q : ℝ → ℝ := weakModeForcing b κ D ψ
  let uψ : ℝ → ℝ := weakModePairing u ψ
  let u₀ψ : ℝ := weakModePairing (fun _ x => f x) ψ 0
  have hψone : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hψgradCont : Continuous (fun x : Vec 2 => AVenhance.spaceGrad ψ x) := by
    apply continuous_pi
    intro i
    exact ((hψone.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hψmem : MemL2On AVenhance.unitCube ψ := weak_continuous_memL2On hψ.continuous
  have hψgradmem (i : Fin 2) :
      MemLp (fun x => AVenhance.spaceGrad ψ x i) 2
        (volume.restrict AVenhance.unitCube) := by
    exact weak_continuous_memL2On ((continuous_apply i).comp hψgradCont)
  have huψcont : ContinuousOn uψ (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun t => ∫ x in AVenhance.unitCube, u t x * ψ x)
      (Set.Icc (0 : ℝ) 1)
    exact hpairing ψ hψ hψper
  have hqjoint : Integrable
      (fun p : ℝ × Vec 2 =>
        Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) * ψ p.2 +
          κ * Homogenization.vecDot (D p.1 p.2) (AVenhance.spaceGrad ψ p.2))
      (volume.restrict AVenhance.timeCube) := by
    have hψjoint : Continuous (fun p : ℝ × Vec 2 => ψ p.2) :=
      hψ.continuous.comp continuous_snd
    obtain ⟨Cψ, hCψ, hψbound⟩ := ModePath.modePath_continuous_joint_bound hψjoint
    have hdriftψ := hdrift.mul_bdd hψjoint.measurable.aestronglyMeasurable hψbound
    have hgradjoint (i : Fin 2) :
        MemLp (fun p : ℝ × Vec 2 => AVenhance.spaceGrad ψ p.2 i) 2
          (volume.restrict AVenhance.timeCube) :=
      weak_continuous_memLp_two_timeCube
        ((continuous_apply i).comp (hψgradCont.comp continuous_snd))
    have hdiffusionCoord (i : Fin 2) : Integrable
        (fun p : ℝ × Vec 2 => D p.1 p.2 i * AVenhance.spaceGrad ψ p.2 i)
        (volume.restrict AVenhance.timeCube) :=
      weak_product_integrable_timeCube (hgradient i) (hgradjoint i)
    have hdot : Integrable
        (fun p : ℝ × Vec 2 =>
          Homogenization.vecDot (D p.1 p.2) (AVenhance.spaceGrad ψ p.2))
        (volume.restrict AVenhance.timeCube) := by
      have hsum := integrable_finsetSum Finset.univ (fun i _ => hdiffusionCoord i)
      have hEq : (fun p : ℝ × Vec 2 =>
          Homogenization.vecDot (D p.1 p.2) (AVenhance.spaceGrad ψ p.2)) =
          fun p => ∑ i : Fin 2,
            D p.1 p.2 i * AVenhance.spaceGrad ψ p.2 i := by
        funext p
        rfl
      rw [hEq]
      exact hsum
    exact hdriftψ.add (hdot.const_mul κ)
  have hqInt : IntervalIntegrable q volume 0 1 := by
    dsimp [q, weakModeForcing]
    exact ModePath.modePath_intervalIntegrable_of_timeCube_integrable hqjoint
  have hweakScalar : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η →
      (∀ t, 1 ≤ t → η t = 0) →
      ∫ t in (0 : ℝ)..1, (-(uψ t) * deriv η t + q t * η t) = u₀ψ * η 0 := by
    exact @weak_solution_mode_integral_path_weakScalar1 b κ f u D hf ψ hψ hψper hpoint hscalar
        hweak hψone hψmem huψcont hqjoint hqInt
  have hpath := scalar_weak_tests_imply_integral_path huψcont hqInt hweakScalar
  intro t ht
  simpa [uψ, u₀ψ, q, weakModePairing, weakModeForcing] using hpath t ht

/-- The scalar forcing paired with a smooth periodic mode is integrable on the full time
interval. This is the coefficientwise input for the finite-dimensional energy balance. -/
theorem weak_solution_mode_forcing_intervalIntegrable
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    IntervalIntegrable (weakModeForcing b κ D ψ) volume 0 1 := by
  rcases hu with ⟨_hpoint, _hbound, _hscalar, hgradient, _hH1, hdrift,
    _hpairing, _hweak⟩
  let hψone : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  let hψgradCont : Continuous (fun x : Vec 2 => AVenhance.spaceGrad ψ x) := by
    apply continuous_pi
    intro i
    exact (hψone.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hψjoint : Continuous (fun p : ℝ × Vec 2 => ψ p.2) :=
    hψ.continuous.comp continuous_snd
  obtain ⟨_Cψ, _hCψ, hψbound⟩ := ModePath.modePath_continuous_joint_bound hψjoint
  have hdriftψ := hdrift.mul_bdd hψjoint.measurable.aestronglyMeasurable hψbound
  have hgradjoint (i : Fin 2) :
      MemLp (fun p : ℝ × Vec 2 => AVenhance.spaceGrad ψ p.2 i) 2
        (volume.restrict AVenhance.timeCube) :=
    weak_continuous_memLp_two_timeCube
      ((continuous_apply i).comp (hψgradCont.comp continuous_snd))
  have hdiffusionCoord (i : Fin 2) : Integrable
      (fun p : ℝ × Vec 2 => D p.1 p.2 i * AVenhance.spaceGrad ψ p.2 i)
      (volume.restrict AVenhance.timeCube) :=
    weak_product_integrable_timeCube (hgradient i) (hgradjoint i)
  have hdot : Integrable
      (fun p : ℝ × Vec 2 =>
        Homogenization.vecDot (D p.1 p.2) (AVenhance.spaceGrad ψ p.2))
      (volume.restrict AVenhance.timeCube) := by
    have hsum := integrable_finsetSum Finset.univ (fun i _ => hdiffusionCoord i)
    have hEq : (fun p : ℝ × Vec 2 =>
        Homogenization.vecDot (D p.1 p.2) (AVenhance.spaceGrad ψ p.2)) =
        fun p => ∑ i : Fin 2,
          D p.1 p.2 i * AVenhance.spaceGrad ψ p.2 i := by
      funext p
      rfl
    rw [hEq]
    exact hsum
  have hqjoint : Integrable
      (fun p : ℝ × Vec 2 =>
        Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) * ψ p.2 +
          κ * Homogenization.vecDot (D p.1 p.2) (AVenhance.spaceGrad ψ p.2))
      (volume.restrict AVenhance.timeCube) := by
    exact hdriftψ.add (hdot.const_mul κ)
  exact ModePath.modePath_intervalIntegrable_of_timeCube_integrable hqjoint

end AVenhance.Infra.Parabolic.WeakUniqueness

end
