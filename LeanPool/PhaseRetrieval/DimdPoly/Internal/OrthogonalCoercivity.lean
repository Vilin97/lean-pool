/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.FiniteBaseAnnulusEstimate
import LeanPool.PhaseRetrieval.DimdPoly.Internal.CoefficientLimitRigidity
import LeanPool.PhaseRetrieval.DimdPoly.Internal.ProductAnnulusLocalization

/-! # OrthogonalCoercivity -/


open MeasureTheory Complex
open scoped BigOperators

noncomputable section

namespace DimdPolyLEAN

/-!
# OrthogonalCoercivity

Terminal finite assembly scaffold. This file should expose one coercivity
theorem and no new analytic content.
-/

section

variable {d : Nat} (kappa : MultiIndex d)

local notation "Pk" => Pkappa d kappa

/-- `coeffPk`: coeff Pk. -/
def coeffPk (H : Pk) (alpha : Idx d) : ℂ := coeffPkappa H alpha

/-- `OrthogonalToPk`: Orthogonal To Pk. -/
def OrthogonalToPk (F G : Pk) : Prop := orthogonalToPk F G

/-- `defectPk`: defect Pk. -/
def defectPk (F G : Pk) : ℝ := defect F G

/-- `lowAnnulusMassPk`: low Annulus Mass Pk. -/
def lowAnnulusMassPk (J : Nat) (H : Pk) : ℝ := lowAnnulusMass J (ofPkappa kappa H)

/-- `highAnnulusMassPk`: high Annulus Mass Pk. -/
def highAnnulusMassPk (J : Nat) (H : Pk) : ℝ := highAnnulusMass J (ofPkappa kappa H)

private theorem defect_nonneg_wip
    (hd : 0 < d) {kappa : MultiIndex d}
    (F G : Pkappa d kappa) :
    0 ≤ defect F G := by
  let _ := hd
  exact Real.sqrt_nonneg _

private theorem norm_zero_pkappa_wip
    (hd : 0 < d) {kappa : MultiIndex d} :
    ‖(0 : Pkappa d kappa)‖ = 0 := by
  let _ := hd
  change
    Real.sqrt
      (Finset.sum (0 : Pkappa d kappa).support
        (fun alpha => ‖(0 : Pkappa d kappa) alpha‖ ^ 2)) = 0
  simp

private theorem norm_nonneg_pkappa_wip
    (hd : 0 < d) {kappa : MultiIndex d}
    (F : Pkappa d kappa) :
    0 ≤ ‖F‖ := by
  let _ := hd
  exact Real.sqrt_nonneg _

private theorem norm_ne_zero_of_ne_zero_pkappa_wip
    (hd : 0 < d) {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF : F ≠ 0) :
    ‖F‖ ≠ 0 := by
  let _ := hd
  intro hnorm
  apply hF
  ext alpha
  by_cases hmem : alpha ∈ F.support
  · have hcoeff_ne : F alpha ≠ 0 := Finsupp.mem_support_iff.mp hmem
    have hle :
        ‖F alpha‖ ^ 2 ≤ Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2) := by
      simpa using
        (Finset.single_le_sum (f := fun a : Idx d => ‖F a‖ ^ 2) (s := F.support) (a := alpha)
          (fun a _ => by positivity) hmem)
    have hterm_pos : 0 < ‖F alpha‖ ^ 2 := by
      have hnorm_pos : 0 < ‖F alpha‖ := norm_pos_iff.mpr hcoeff_ne
      nlinarith
    have hsum_pos : 0 < Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2) :=
      lt_of_lt_of_le hterm_pos hle
    change Real.sqrt (Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2)) = 0 at hnorm
    have hsqrt_pos :
        0 < Real.sqrt (Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2) ) :=
      Real.sqrt_pos.mpr hsum_pos
    linarith
  · exact Finsupp.notMem_support_iff.mp hmem

private theorem norm_smul_pkappa_wip
    (hd : 0 < d) {kappa : MultiIndex d}
    (c : ℂ) (F : Pkappa d kappa) :
    ‖c • F‖ = ‖c‖ * ‖F‖ := by
  let _ := hd
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul, norm_zero_pkappa_wip hd]
    simp
  · change
      Real.sqrt (Finset.sum (c • F).support (fun alpha => ‖(c • F) alpha‖ ^ 2)) =
        ‖c‖ * Real.sqrt (Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2))
    rw [Finsupp.support_smul_eq hc]
    have hsum :
        Finset.sum F.support (fun alpha => ‖(c • F) alpha‖ ^ 2) =
          ‖c‖ ^ 2 * Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro alpha halpha
      simp [Finsupp.smul_apply, mul_pow]
    rw [hsum, Real.sqrt_mul (sq_nonneg ‖c‖), Real.sqrt_sq_eq_abs]
    simp [abs_of_nonneg (norm_nonneg _)]

private theorem orthogonalToPk_smul_right_wip
    (hd : 0 < d) {kappa : MultiIndex d}
    (F G : Pkappa d kappa) (c : ℂ) :
    orthogonalToPk F G ->
      orthogonalToPk F (c • G) := by
  let _ := hd
  intro horth
  dsimp [orthogonalToPk, pkappaInner] at horth ⊢
  by_cases hc : c = 0
  · simp [hc]
  · simp only [Finsupp.sum, Finsupp.smul_apply] at horth ⊢
    rw [Finsupp.support_smul_eq hc]
    calc
      Finset.sum G.support (fun alpha => c * G alpha * star (F alpha))
          = c * Finset.sum G.support (fun alpha => G alpha * star (F alpha)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro alpha halpha
            ring
      _ = 0 := by simp [horth]

private theorem phi1D_eq_oneDimPhi_wip
    (k n : Nat) (z : ℂ) :
    phi1D k n z = Hermite1DimdLEAN.oneDimPhi k n z := by
  unfold phi1D complexHermite Hermite1DimdLEAN.oneDimPhi
  congr 1
  · simp [one_div, mul_comm]
  · rw [Nat.min_comm k n]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj' : j ≤ min n k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjn : j ≤ n := le_trans hj' (Nat.min_le_left _ _)
    have hfac_ne : (Nat.factorial (n - j) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - j)
    have hfactor :
        (Nat.factorial j : ℂ) * (Nat.choose n j : ℂ) =
          (Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) := by
      apply mul_right_cancel₀ hfac_ne
      calc
        ((Nat.factorial j : ℂ) * (Nat.choose n j : ℂ)) * (Nat.factorial (n - j) : ℂ)
            = (Nat.choose n j : ℂ) * (Nat.factorial j : ℂ) *
                (Nat.factorial (n - j) : ℂ) := by ring
        _ = (Nat.factorial n : ℂ) := by
            exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
        _ = ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
              (Nat.factorial (n - j) : ℂ) := by
            field_simp [hfac_ne]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      congrArg
        (fun x : ℂ =>
          ((-1 : ℂ) ^ j) * x * (Nat.choose k j : ℂ) * z ^ (n - j) * (star z) ^ (k - j))
        hfactor

private lemma continuous_Phi_wip
    {d : Nat} (kappa alpha : MultiIndex d) :
    Continuous (Phi kappa alpha) := by
  unfold Phi phi1D complexHermite
  continuity

private lemma continuous_evalPkappa_wip
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    Continuous (evalPkappa kappa F) := by
  unfold evalPkappa
  refine continuous_finsetSum _ ?_
  intro alpha halpha
  exact continuous_const.mul (continuous_Phi_wip kappa alpha)

private lemma integrable_oneDimPhi_cross_gaussian_wip
    (k m n : Nat) :
    Integrable
      (fun z : Cd 1 => phi1D k m (z 0) * (starRingEnd ℂ) (phi1D k n (z 0)))
      (gammaD 1) := by
  have hrewrite :
      (fun z : Cd 1 => phi1D k m (z 0) * (starRingEnd ℂ) (phi1D k n (z 0))) =
        fun z : Cd 1 =>
          Hermite1DimdLEAN.oneDimPhi k m (z 0) *
            (starRingEnd ℂ) (Hermite1DimdLEAN.oneDimPhi k n (z 0)) := by
    funext z
    rw [phi1D_eq_oneDimPhi_wip, phi1D_eq_oneDimPhi_wip]
  rw [hrewrite]
  change
    Integrable
      (fun z : Cd 1 => HermitekLEAN.Phi k m (z 0) *
        (starRingEnd ℂ) (HermitekLEAN.Phi k n (z 0)))
      (gammaD 1)
  rw [gammaD]
  rw [MeasureTheory.integrable_withDensity_iff_integrable_smul']
  · have hcross :
        Integrable
          (fun z : Cd 1 =>
            HermitekLEAN.Phi k m (z 0) * (starRingEnd ℂ) (HermitekLEAN.Phi k n (z 0)) *
              (Real.exp (-‖z 0‖ ^ 2) : ℂ)) := by
      have h :=
        (MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integrable_comp_of_integrable
          (g := fun z : ℂ =>
            HermitekLEAN.Phi k m z * (starRingEnd ℂ) (HermitekLEAN.Phi k n z) *
              (Real.exp (-‖z‖ ^ 2) : ℂ))
          (HermitekLEAN.integrable_weightedCross k m n)
      refine h.congr ?_
      filter_upwards with z
      have he : (MeasurableEquiv.funUnique (Fin 1) ℂ) z = z 0 := rfl
      simp only [Function.comp_apply, he, mul_assoc]
    have hsmul :
        Integrable
          (fun z : Cd 1 =>
            Real.exp (-‖z 0‖ ^ 2) •
              (HermitekLEAN.Phi k m (z 0) *
                (starRingEnd ℂ) (HermitekLEAN.Phi k n (z 0)))) := by
      convert hcross using 1
      funext z
      simp [Algebra.smul_def, mul_left_comm, mul_comm]
    refine (hsmul.const_mul (1 / Real.pi)).congr ?_
    filter_upwards with z
    symm
    let X : ℂ :=
      HermitekLEAN.Phi k m (z 0) * (starRingEnd ℂ) (HermitekLEAN.Phi k n (z 0))
    change (ENNReal.ofReal (gaussianDensity 1 z)).toReal • X =
      ((1 / Real.pi : ℂ) * (Real.exp (-‖z 0‖ ^ 2) • X))
    have hnonneg_density : 0 ≤ gaussianDensity 1 z := by
      unfold gaussianDensity
      positivity
    have hdensity :
        (ENNReal.ofReal (gaussianDensity 1 z)).toReal =
          Real.pi⁻¹ * Real.exp (-‖z 0‖ ^ 2) := by
      rw [ENNReal.toReal_ofReal hnonneg_density]
      simp [gaussianDensity]
    rw [hdensity]
    calc
      (Real.pi⁻¹ * Real.exp (-‖z 0‖ ^ 2)) • X =
          (((Real.pi⁻¹ * Real.exp (-‖z 0‖ ^ 2) : ℝ) : ℂ) * X) := by
            change
              (((Real.pi⁻¹ * Real.exp (-‖z 0‖ ^ 2) : ℝ) : ℂ) * X) =
                (((Real.pi⁻¹ * Real.exp (-‖z 0‖ ^ 2) : ℝ) : ℂ) * X)
            rfl
      _ = (1 / Real.pi : ℂ) * (Real.exp (-‖z 0‖ ^ 2) • X) := by
            simp [Algebra.smul_def, one_div, mul_assoc]
  · unfold gaussianDensity
    fun_prop
  · simp

private lemma integrable_productBasis_cross_wip
    {d : Nat} (kappa alpha beta : MultiIndex d) :
    Integrable
      (fun z : Cd d => Phi kappa alpha z * (starRingEnd ℂ) (Phi kappa beta z))
      (gammaD d) := by
  simpa [Phi, gammaD, gaussianDensity, Hermite1DimdLEAN.gaussianMeasure,
    Hermite1DimdLEAN.gaussianDensity, one_div,
    Finset.prod_mul_distrib,
    mul_assoc, mul_left_comm, mul_comm] using
    (Hermite1DimdLEAN.tensorGaussianFactorization d
      (fun q z => phi1D (kappa q) (alpha q) z)
      (fun q z => phi1D (kappa q) (beta q) z)
      (fun q => integrable_oneDimPhi_cross_gaussian_wip (kappa q) (alpha q) (beta q))).1

private lemma integrable_evalPkappa_cross_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    Integrable
      (fun z : Cd d => evalPkappa kappa F z * (starRingEnd ℂ) (evalPkappa kappa G z))
      (gammaD d) := by
  classical
  unfold evalPkappa
  have hrewrite :
      (fun z : Cd d =>
        (∑ alpha ∈ F.support, F alpha * Phi kappa alpha z) *
          (starRingEnd ℂ) (∑ beta ∈ G.support, G beta * Phi kappa beta z)) =
        (fun z : Cd d =>
          ∑ alpha ∈ F.support,
            ∑ beta ∈ G.support,
              F alpha * (starRingEnd ℂ) (G beta) *
                (Phi kappa alpha z * (starRingEnd ℂ) (Phi kappa beta z))) := by
    funext z
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    have hconjsum :
        (starRingEnd ℂ) (∑ beta ∈ G.support, G beta * Phi kappa beta z) =
          ∑ beta ∈ G.support, (starRingEnd ℂ) (G beta * Phi kappa beta z) := by
      simp
    rw [hconjsum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro beta hbeta
    simp [mul_assoc, mul_left_comm, mul_comm]
  change
    Integrable
      (fun z : Cd d =>
        (∑ alpha ∈ F.support, F alpha * Phi kappa alpha z) *
          (starRingEnd ℂ) (∑ beta ∈ G.support, G beta * Phi kappa beta z))
      (gammaD d)
  rw [hrewrite]
  refine MeasureTheory.integrable_finsetSum _ ?_
  intro alpha halpha
  refine MeasureTheory.integrable_finsetSum _ ?_
  intro beta hbeta
  simpa [mul_assoc] using
    (integrable_productBasis_cross_wip kappa alpha beta).const_mul
      (F alpha * (starRingEnd ℂ) (G beta))

private theorem gaussianL2Norm_eq_lpNorm_wip
    {d : Nat} {α : Type*} [NormedAddCommGroup α] [MeasurableSpace α] [NormedSpace ℝ α]
    [BorelSpace α] (F : Cd d → α)
    (hF : AEStronglyMeasurable F (gammaD d)) :
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      MeasureTheory.lpNorm F 2 (gammaD d) := by
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := gammaD d) (p := (2 : NNReal)) (f := F) htwo hF
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      MeasureTheory.lpNorm F (↑(2 : NNReal)) (gammaD d)
  rw [hlp]
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) ^ ((2 : ℝ)⁻¹)
  rw [Real.sqrt_eq_rpow]
  norm_num

private theorem memLp_two_evalPkappa_wip
    (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.MemLp (evalPkappa kappa F) 2 (gammaD d) := by
  let _ := hd
  have hmeas :
      AEStronglyMeasurable (evalPkappa kappa F) (gammaD d) :=
    (continuous_evalPkappa_wip kappa F).stronglyMeasurable.aestronglyMeasurable
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  simpa [pow_two, norm_mul] using (integrable_evalPkappa_cross_wip kappa F F).norm

private theorem evalPkappa_lpNorm_eq_norm_wip
    (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.lpNorm (evalPkappa kappa F) 2 (gammaD d) = ‖F‖ := by
  calc
    MeasureTheory.lpNorm (evalPkappa kappa F) 2 (gammaD d)
      = Real.sqrt (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ (2 : ℝ) ∂ gammaD d) := by
          symm
          exact gaussianL2Norm_eq_lpNorm_wip (evalPkappa kappa F)
            (memLp_two_evalPkappa_wip hd kappa F).1
    _ = ‖F‖ := by
          have hpow :
              (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ (2 : ℝ) ∂ gammaD d) =
                ∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d := by
            congr 1
            ext z
            exact Real.rpow_natCast ‖evalPkappa kappa F z‖ 2
          rw [hpow, evalPkappa_total_mass hd kappa F, Real.sqrt_sq_eq_abs]
          exact abs_of_nonneg (norm_nonneg_pkappa_wip hd F)

private def defectFunctionPkappa_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    Cd d → ℝ :=
  fun z => |‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖|

private lemma continuous_defectFunctionPkappa_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    Continuous (defectFunctionPkappa_wip kappa F G) := by
  unfold defectFunctionPkappa_wip
  exact (((continuous_evalPkappa_wip kappa (F + G)).norm.sub
    (continuous_evalPkappa_wip kappa F).norm).abs)

private theorem memLp_two_defectFunctionPkappa_wip
    (hd : 0 < d) (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    MeasureTheory.MemLp (defectFunctionPkappa_wip kappa F G) 2 (gammaD d) := by
  let _ := hd
  have hmeas :
      AEStronglyMeasurable (defectFunctionPkappa_wip kappa F G) (gammaD d) :=
    (continuous_defectFunctionPkappa_wip kappa F G).stronglyMeasurable.aestronglyMeasurable
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hplus_int :
      Integrable (fun z : Cd d => 2 * ‖evalPkappa kappa (F + G) z‖ ^ 2) (gammaD d) := by
    simpa [pow_two, norm_mul] using
      ((integrable_evalPkappa_cross_wip kappa (F + G) (F + G)).norm.const_mul 2)
  have hbase_int :
      Integrable (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) := by
    simpa [pow_two, norm_mul] using
      ((integrable_evalPkappa_cross_wip kappa F F).norm.const_mul 2)
  have hsq :
      Integrable
        (fun z : Cd d =>
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2)
        (gammaD d) := hplus_int.add hbase_int
  have hmeasSq :
      AEStronglyMeasurable (fun z : Cd d => defectFunctionPkappa_wip kappa F G z ^ 2) (gammaD d) :=
    (continuous_defectFunctionPkappa_wip kappa F G).pow 2 |>.stronglyMeasurable.aestronglyMeasurable
  have hbound :
      ∀ᵐ z ∂ gammaD d,
        ‖defectFunctionPkappa_wip kappa F G z ^ 2‖ ≤
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2 := by
    filter_upwards with z
    have hsqz :
        defectFunctionPkappa_wip kappa F G z ^ 2 ≤
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2 := by
      unfold defectFunctionPkappa_wip
      have : (‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖) ^ 2 ≤
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2 := by
        nlinarith [sq_nonneg (‖evalPkappa kappa (F + G) z‖ + ‖evalPkappa kappa F z‖)]
      simpa [sq_abs] using this
    have hnonneg : 0 ≤ defectFunctionPkappa_wip kappa F G z ^ 2 := by
      positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hsqz
  simpa [Real.norm_eq_abs, abs_of_nonneg] using
    MeasureTheory.Integrable.mono' hsq hmeasSq hbound

private theorem defect_lpNorm_eq_wip
    (hd : 0 < d) (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    defect F G = MeasureTheory.lpNorm (defectFunctionPkappa_wip kappa F G) 2 (gammaD d) := by
  let _ := hd
  simpa [defect, defectFunctionPkappa_wip, Real.norm_eq_abs, sq_abs] using
    gaussianL2Norm_eq_lpNorm_wip (defectFunctionPkappa_wip kappa F G)
      (memLp_two_defectFunctionPkappa_wip hd kappa F G).1

private theorem evalPkappa_add_apply_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) (z : Cd d) :
    evalPkappa kappa (F + G) z = evalPkappa kappa F z + evalPkappa kappa G z := by
  unfold evalPkappa
  rw [Finsupp.sum_add_index]
  · simp
  · intro alpha halpha b1 b2
    ring

private lemma evalPkappa_pointwise_bound_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) (z : Cd d) :
    ‖evalPkappa kappa G z‖ ≤
      defectFunctionPkappa_wip kappa F G z + 2 * ‖evalPkappa kappa F z‖ := by
  have hsub :
      evalPkappa kappa G z = evalPkappa kappa (F + G) z - evalPkappa kappa F z := by
    rw [evalPkappa_add_apply_wip kappa F G z, add_sub_cancel_left]
  have haux :
      ‖evalPkappa kappa (F + G) z‖ ≤
        defectFunctionPkappa_wip kappa F G z + ‖evalPkappa kappa F z‖ := by
    unfold defectFunctionPkappa_wip
    exact sub_le_iff_le_add.mp (le_abs_self _)
  calc
    ‖evalPkappa kappa G z‖ = ‖evalPkappa kappa (F + G) z - evalPkappa kappa F z‖ := by
      rw [hsub]
    _ ≤ ‖evalPkappa kappa (F + G) z‖ + ‖evalPkappa kappa F z‖ := norm_sub_le _ _
    _ ≤ defectFunctionPkappa_wip kappa F G z + ‖evalPkappa kappa F z‖ + ‖evalPkappa kappa F z‖ := by
          linarith
    _ = defectFunctionPkappa_wip kappa F G z + 2 * ‖evalPkappa kappa F z‖ := by ring

private theorem norm_le_defect_add_two_wip
    (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) (hF_norm : ‖F‖ = 1) :
    ‖G‖ ≤ defect F G + 2 := by
  let _ := hd
  have hdef_mem := memLp_two_defectFunctionPkappa_wip hd kappa F G
  have htwoF_mem :
      MeasureTheory.MemLp (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖) 2 (gammaD d) := by
    exact (memLp_two_evalPkappa_wip hd kappa F).norm.const_smul (2 : ℝ)
  have hsum_mem :
      MeasureTheory.MemLp
        (defectFunctionPkappa_wip kappa F G + fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
        2 (gammaD d) := by
    exact hdef_mem.add htwoF_mem
  have hmono :
      MeasureTheory.lpNorm (evalPkappa kappa G) 2 (gammaD d) ≤
        MeasureTheory.lpNorm
          (defectFunctionPkappa_wip kappa F G + fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
          2 (gammaD d) := by
    refine MeasureTheory.lpNorm_mono_real hsum_mem ?_
    intro z
    simpa using evalPkappa_pointwise_bound_wip kappa F G z
  have htri :
      MeasureTheory.lpNorm
          (defectFunctionPkappa_wip kappa F G + fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
          2 (gammaD d)
        ≤ MeasureTheory.lpNorm (defectFunctionPkappa_wip kappa F G) 2 (gammaD d) +
            MeasureTheory.lpNorm (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖) 2 (gammaD d) := by
    exact MeasureTheory.lpNorm_add_le hdef_mem (g := fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
      (by norm_num)
  have hnormEq :
      MeasureTheory.lpNorm (fun z : Cd d => ‖evalPkappa kappa F z‖) 2 (gammaD d) =
        MeasureTheory.lpNorm (evalPkappa kappa F) 2 (gammaD d) := by
    simpa using
      (MeasureTheory.lpNorm_norm (μ := gammaD d) (p := (2 : ENNReal))
        (memLp_two_evalPkappa_wip hd kappa F).aestronglyMeasurable)
  have htwoF_norm :
      MeasureTheory.lpNorm (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
        2 (gammaD d) = 2 := by
    calc
      MeasureTheory.lpNorm (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖) 2 (gammaD d)
          = MeasureTheory.lpNorm
              ((2 : ℝ) • fun z : Cd d => ‖evalPkappa kappa F z‖) 2 (gammaD d) := by
              rfl
      _ = ‖(2 : ℝ)‖ *
            MeasureTheory.lpNorm (fun z : Cd d => ‖evalPkappa kappa F z‖) 2 (gammaD d) := by
            rw [MeasureTheory.lpNorm_const_smul]
            norm_num
      _ = 2 * MeasureTheory.lpNorm (evalPkappa kappa F) 2 (gammaD d) := by
            rw [hnormEq]
            norm_num
      _ = 2 * ‖F‖ := by rw [evalPkappa_lpNorm_eq_norm_wip hd kappa F]
      _ = 2 := by simp [hF_norm]
  calc
    ‖G‖ = MeasureTheory.lpNorm (evalPkappa kappa G) 2 (gammaD d) := by
          symm
          exact evalPkappa_lpNorm_eq_norm_wip hd kappa G
    _ ≤ MeasureTheory.lpNorm
          (defectFunctionPkappa_wip kappa F G + fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
          2 (gammaD d) := hmono
    _ ≤ MeasureTheory.lpNorm (defectFunctionPkappa_wip kappa F G) 2 (gammaD d) +
          MeasureTheory.lpNorm (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖) 2 (gammaD d) := htri
    _ = defect F G + 2 := by rw [← defect_lpNorm_eq_wip hd kappa F G, htwoF_norm]

theorem orthogonal_coercivity
    (hd : 0 < d) (F : Pk) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1) :
    ∃ C_F_perp : ℝ, 0 < C_F_perp ∧
      ∀ G : Pk, OrthogonalToPk kappa F G ->
        ‖G‖ <= C_F_perp * defectPk kappa F G := by
  let _ := hd
  obtain ⟨J, delta_high, hdelta_high_pos, hhigh⟩ :=
    highAnnulusControl hd kappa F hF_ne hF_norm
  obtain ⟨delta_low, hdelta_low_pos, hlow⟩ :=
    lowAnnulusDefectControl hd kappa F hF_ne hF_norm J
  let delta : ℝ := min delta_high delta_low
  let C_F_perp : ℝ := max 2 delta⁻¹
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min hdelta_high_pos hdelta_low_pos
  have hC_F_perp_pos : 0 < C_F_perp := by
    dsimp [C_F_perp]
    exact lt_of_lt_of_le zero_lt_two (le_max_left _ _)
  refine ⟨C_F_perp, hC_F_perp_pos, ?_⟩
  intro G horth
  by_cases hG : G = 0
  · rw [hG, norm_zero_pkappa_wip hd]
    exact mul_nonneg (le_of_lt hC_F_perp_pos) (defect_nonneg_wip hd F 0)
  · let t : ℝ := ‖G‖
    let H : Pk := (((t : ℂ)⁻¹) : ℂ) • G
    have ht_ne : t ≠ 0 := by
      exact norm_ne_zero_of_ne_zero_pkappa_wip hd hG
    have ht_pos : 0 < t := by
      exact lt_of_le_of_ne (norm_nonneg_pkappa_wip hd G) ht_ne.symm
    have hH_orth : OrthogonalToPk kappa F H := by
      simpa [OrthogonalToPk, H] using
        orthogonalToPk_smul_right_wip hd F G (((t : ℂ)⁻¹) : ℂ) horth
    have hH_norm : ‖H‖ = 1 := by
      dsimp [H, t]
      rw [norm_smul_pkappa_wip hd]
      have htinv : t⁻¹ * t = 1 := by
        field_simp [ht_ne]
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos,
        abs_of_nonneg (inv_nonneg.mpr (le_of_lt ht_pos)), t] using htinv
    have hG_eq : G = t • H := by
      ext alpha
      change G alpha = ((t : ℂ) * (((t : ℂ)⁻¹) * G alpha))
      field_simp [ht_ne]
    have hlarge_bridge : t ≤ defectPk kappa F G + 2 := by
      simpa [t, defectPk] using norm_le_defect_add_two_wip hd kappa F G hF_norm
    by_cases hlt4 : t < 4
    · by_cases hsmall : defectPk kappa F G ≤ delta * t
      · have hdelta_le_high : delta ≤ delta_high := by
          dsimp [delta]
          exact min_le_left _ _
        have hdelta_le_low : delta ≤ delta_low := by
          dsimp [delta]
          exact min_le_right _ _
        have hdefect_high : defect F (t • H) ≤ delta_high * t := by
          have hstep : defectPk kappa F G ≤ delta_high * t := by
            refine le_trans hsmall ?_
            exact mul_le_mul_of_nonneg_right hdelta_le_high (le_of_lt ht_pos)
          simpa [defectPk, hG_eq] using hstep
        have hdefect_low : defect F (t • H) ≤ delta_low * t := by
          have hstep : defectPk kappa F G ≤ delta_low * t := by
            refine le_trans hsmall ?_
            exact mul_le_mul_of_nonneg_right hdelta_le_low (le_of_lt ht_pos)
          simpa [defectPk, hG_eq] using hstep
        have hhigh_mass : highAnnulusMass J (ofPkappa kappa H) ≤ 1 / 4 :=
          hhigh hH_orth hH_norm ht_pos (le_of_lt hlt4) hdefect_high
        have hlow_mass : lowAnnulusMass J (ofPkappa kappa H) ≤ 1 / 4 :=
          hlow hH_orth hH_norm ht_pos (le_of_lt hlt4) hhigh_mass hdefect_low
        have hpartition := annulusMassPartition hd kappa J H
        have hsum_le :
            lowAnnulusMass J (ofPkappa kappa H) + highAnnulusMass J (ofPkappa kappa H) ≤ 1 / 2 := by
          linarith
        have hnorm_sq : ‖H‖ ^ 2 = 1 := by
          rw [hH_norm]
          norm_num
        linarith
      · have hdelta_inv_le : delta⁻¹ ≤ C_F_perp := by
          dsimp [C_F_perp]
          exact le_max_right _ _
        have hstrict : delta * t < defectPk kappa F G := lt_of_not_ge hsmall
        have ht_le_delta : t ≤ delta⁻¹ * defectPk kappa F G := by
          have haux : t ≤ defectPk kappa F G / delta := by
            rw [le_div_iff₀ hdelta_pos]
            exact le_of_lt (by simpa [mul_comm] using hstrict)
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using haux
        calc
          ‖G‖ = t := rfl
          _ ≤ delta⁻¹ * defectPk kappa F G := ht_le_delta
          _ ≤ C_F_perp * defectPk kappa F G := by
            exact mul_le_mul_of_nonneg_right hdelta_inv_le (defect_nonneg_wip hd F G)
    · have hge4 : 4 ≤ t := le_of_not_gt hlt4
      have htwo_defect : t ≤ 2 * defectPk kappa F G := by
        have hdefect_nonneg : 0 ≤ defectPk kappa F G := defect_nonneg_wip hd F G
        nlinarith
      have htwo_le_C : 2 ≤ C_F_perp := by
        dsimp [C_F_perp]
        exact le_max_left _ _
      calc
        ‖G‖ = t := rfl
        _ ≤ 2 * defectPk kappa F G := htwo_defect
        _ ≤ C_F_perp * defectPk kappa F G := by
          exact mul_le_mul_of_nonneg_right htwo_le_C (defect_nonneg_wip hd F G)

end

end DimdPolyLEAN
