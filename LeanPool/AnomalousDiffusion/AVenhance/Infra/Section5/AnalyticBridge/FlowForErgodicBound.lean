/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowRegularityCore
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowHigherDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowInverseBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowBoundsAtScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.AppB2Smoothness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.FlowDiffeo
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Seminorm

/-! # Flow derivative bounds for the composed-analyticity bridge

The stream-function higher-derivative field is the corrected `e.Xm.bound.4` estimate in
coordinate directions. This module converts it to the derivative seminorm
used by `AnalyticBridge.FlowForErgodicBound`, and proves its support-time
hypothesis from the cutoffs and time scales.
-/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.AnalyticBridge

open AVenhance
open AVenhance.Infra.Construction
open AVenhance.FaaDiBruno

theorem FlowForErgodicBound.orderedPartial_eq_iteratedFDeriv
    {n : ℕ} {f : Vec 2 → Vec 2} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : Vec 2) (J : Fin n → Fin 2) :
    orderedPartial n f x J =
      iteratedFDeriv ℝ n f x (fun j => basisVec (J j)) := by
  unfold orderedPartial liftVecOne
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  change iteratedFDeriv ℝ n
      (f ∘ (vecOneEquiv 2).toContinuousLinearMap)
      (WithLp.toLp 1 x)
      (fun j => coordinateVectorOne 2 (J j)) = _
  rw [(vecOneEquiv 2).toContinuousLinearMap.iteratedFDeriv_comp_right
    hfN (WithLp.toLp 1 x) le_rfl]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    vecOneEquiv, coordinateVectorOne, Homogenization.basisVec,
    PiLp.coe_continuousLinearEquiv]

theorem FlowForErgodicBound.xiMK_ne_zero_abs_le
    {β : ℝ} (I : Ingredients β) (m : ℕ) {k : ℤ} {t : ℝ}
    (hne : I.xiMK m k t ≠ 0) :
    |t - (k : ℝ) * tau β I.Λ m| ≤ 5 / 4 * tau β I.Λ m := by
  have hτ := I.tau_pos' m
  set u := (t - k * tau β I.Λ m) / tau β I.Λ m with hu
  have hmem : u ∈ Set.Icc (-(5 / 4) : ℝ) (5 / 4) := by
    by_contra hnot
    apply hne
    have h1 := I.xi_le_ind u
    have h2 := I.ind_le_xi u
    rw [indIcc_eq_zero_of_not_mem hnot] at h1
    have h3 := indIcc_nonneg' (-(3 / 4)) (3 / 4) u
    exact le_antisymm h1 (h3.trans h2)
  have habs : |u| ≤ 5 / 4 := abs_le.mpr ⟨hmem.1, hmem.2⟩
  rw [hu, abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at habs
  linarith

/-- Coordinate form of the corrected `e.Xm.bound.4`, obtained directly from
the stream-function all-order field at the preceding scale. The radius coefficient is
`2^14`, as required by the source.
-/
theorem xFlow_derivativeSup_eXm_bound_four
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hΦ : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hΦ R M)
    {m : ℕ} (hm : 2 ≤ m) (k : ℤ)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 2))
    {t : ℝ} (ht : |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤
      2 ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹) :
    ∀ n : ℕ, 1 ≤ n →
      derivativeSup n (I.xFlow hΦ m (lIdx β I.Λ m k) t) ≤
        ENNReal.ofReal (2 * n.factorial *
          (2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹) ^ (n - 1)) := by
  intro n hn
  let start : ℝ := (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m
  have hprev' : Section2StreamInductionHypothesis (Φ := Φ) R M ((m - 1) - 1) := by
    simpa [Nat.sub_sub] using hprev
  have hHigher : ∀ x : Vec 2, ∀ J : Fin n → Fin 2,
      ‖iteratedFDeriv ℝ n (I.xFlow hΦ m (lIdx β I.Λ m k) t) x
        (fun j => basisVec (J j))‖ ≤
        2 * n.factorial *
          (2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹) ^ (n - 1) := by
    intro x J
    have h := section2_flow_higher_derivative_from_previous
      hscales happB2 (m - 1) (by omega) n hn hprev' start (t - start)
      (by simpa [start] using ht) x J
    change ‖iteratedFDeriv ℝ n
      (fun y : Vec 2 => constructionFlow hΦ (m - 1) t y start) x
      (fun j => basisVec (J j))‖ ≤ _
    simpa [start, add_sub_cancel_left] using h
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      (I.xFlow hΦ m (lIdx β I.Λ m k) t) :=
    (AVenhance.Infra.Section5.LeftToShow.xFlowDiffeo I hΦ m
      (lIdx β I.Λ m k) t).contDiff_toFun
  have hpartial : ∀ J : Fin n → Fin 2,
      partialSup n (I.xFlow hΦ m (lIdx β I.Λ m k) t) J ≤
        ENNReal.ofReal (2 * n.factorial *
          (2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹) ^ (n - 1)) := by
    intro J
    unfold partialSup
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards with x
    have hpoint := hHigher x J
    rw [← FlowForErgodicBound.orderedPartial_eq_iteratedFDeriv hf x J] at hpoint
    exact hpoint
  unfold derivativeSup
  exact iSup_le hpartial

theorem FlowForErgodicBound.xi_flow_time_window
    {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 2 ≤ m)
    (k : ℤ) {t : ℝ} (hξ : I.xiMK m k t ≠ 0) :
    |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤
      2 ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ := by
  have hτ := I.tau_pos' m
  have hτpp := I.tauPP_pos' m
  have hnear := FlowForErgodicBound.xiMK_ne_zero_abs_le I m hξ
  have hcell := Infra.Ingredients.taum_prime_supp
    (β := β) (Λ := I.Λ) k I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le) (by omega : 1 ≤ m)
  have hleftmem : (k : ℝ) * tau β I.Λ m - tau β I.Λ m / 2 ∈
    Set.Icc ((k : ℝ) * tau β I.Λ m - tau β I.Λ m / 2)
        ((k : ℝ) * tau β I.Λ m + tau β I.Λ m / 2) := by
    simp only [Set.mem_Icc]
    constructor <;> linarith [hτ.le]
  have hrightmem : (k : ℝ) * tau β I.Λ m + tau β I.Λ m / 2 ∈
    Set.Icc ((k : ℝ) * tau β I.Λ m - tau β I.Λ m / 2)
        ((k : ℝ) * tau β I.Λ m + tau β I.Λ m / 2) := by
    simp only [Set.mem_Icc]
    constructor <;> linarith [hτ.le]
  have hleft := hcell hleftmem
  have hright := hcell hrightmem
  have hcenter :
      |(k : ℝ) * tau β I.Λ m -
          (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤
        tauPP β I.Λ m / 2 - tau β I.Λ m / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hleft.1, hright.2]
  have hfactor : 5 ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
    unfold Infra.Ingredients.tauCellFactor
    have hceilpos : 0 <
        ⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ := by
      apply Nat.ceil_pos.mpr
      exact Real.rpow_pos_of_pos
        (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
          (by exact_mod_cast I.two_pow_seven_le)) _
    have hceil : 1 ≤
        (⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hceilpos)
    nlinarith
  have hratio := Infra.Ingredients.tauPP_eq_cellFactor_sq_mul_tau
    (β := β) (Λ := I.Λ) (m := m) (by omega : 1 ≤ m)
  have hsmall : tau β I.Λ m ≤ tauPP β I.Λ m / 25 := by
    have hF2 : 25 ≤ (Infra.Ingredients.tauCellFactor β I.Λ m) ^ 2 := by
      nlinarith [sq_nonneg (Infra.Ingredients.tauCellFactor β I.Λ m - 5)]
    have h25 : 25 * tau β I.Λ m ≤ tauPP β I.Λ m := by
      calc
        25 * tau β I.Λ m ≤
            Infra.Ingredients.tauCellFactor β I.Λ m ^ 2 * tau β I.Λ m :=
          mul_le_mul_of_nonneg_right hF2 hτ.le
        _ = tauPP β I.Λ m := hratio.symm
    nlinarith
  have hdist :
      |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤ tauPP β I.Λ m := by
    have hnearBounds := abs_le.mp hnear
    have hcenterBounds := abs_le.mp hcenter
    have hsum : t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m =
        (t - (k : ℝ) * tau β I.Λ m) +
          ((k : ℝ) * tau β I.Λ m -
            (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m) := by ring
    have hsumAbs :
        |(t - (k : ℝ) * tau β I.Λ m) +
          ((k : ℝ) * tau β I.Λ m -
            (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m)| ≤
          tauPP β I.Λ m / 2 + 3 / 4 * tau β I.Λ m := by
      rw [abs_le]
      constructor <;> nlinarith [hnearBounds.1, hnearBounds.2,
        hcenterBounds.1, hcenterBounds.2]
    calc
      _ = |(t - (k : ℝ) * tau β I.Λ m) +
          ((k : ℝ) * tau β I.Λ m -
            (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m)| := by rw [hsum]
      _ ≤ tauPP β I.Λ m / 2 + 3 / 4 * tau β I.Λ m := hsumAbs
      _ ≤ tauPP β I.Λ m := by nlinarith [hsmall]
  let e := epsilon β I.Λ (m - 1)
  have he : 0 < e := by
    dsimp [e]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      (by exact_mod_cast I.two_pow_seven_le)
  have he1 : e ≤ 1 := by
    dsimp [e]
    exact Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
      (by exact_mod_cast I.two_pow_seven_le)
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hpow : e ^ (2 - β + 2 * delta β) ≤ e ^ (2 - β) :=
    Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith)
  have hpp := Infra.Ingredients.tauPP_bounds I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le) (by omega : 1 ≤ m)
  have haInv : (a β I.Λ (m - 1))⁻¹ = e ^ (2 - β) := by
    dsimp [e, a]
    rw [show 2 - β = -(β - 2) by ring, Real.rpow_neg he.le]
  have hppWidth : tauPP β I.Λ m ≤
      2 ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ := by
    calc
      tauPP β I.Λ m ≤
          2 ^ (-25 : ℤ) * e ^ (2 - β + 2 * delta β) := hpp.2
      _ ≤ 2 ^ (-25 : ℤ) * e ^ (2 - β) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 2 ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ := by rw [haInv]
  exact hdist.trans hppWidth

/-- The exact unfolded `FlowForErgodicBound` target on the support of
`ξ_{m,k}`. Taking `A ≥ 2^14` lets the stream-function coefficient `2 · (2^14)^(n-1)` be
absorbed into the source form `A · A^(n-1)`. -/
theorem flowForErgodicBound_of_section2_previous
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hΦ : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hΦ R M)
    (m : ℕ) (hm : 2 ≤ m) (k : ℤ) (A : ℝ) (hA : 2 ^ (14 : ℕ) ≤ A)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 2)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, I.xiMK m k t ≠ 0 →
      ∀ n : ℕ, 1 ≤ n →
        derivativeSup n (I.xFlow hΦ m (lIdx β I.Λ m k) t) ≤
          ENNReal.ofReal
            (A * n.factorial *
              (A / epsilon β I.Λ (m - 1)) ^ (n - 1)) := by
  intro t _ht hξ n hn
  have hwindow := FlowForErgodicBound.xi_flow_time_window I hm k hξ
  have hbase := xFlow_derivativeSup_eXm_bound_four
    hscales happB2 hm k hprev hwindow n hn
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      (by exact_mod_cast I.two_pow_seven_le)
  have hratio :
      2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹ ≤
        A / epsilon β I.Λ (m - 1) := by
    calc
      2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹ =
          2 ^ 14 / epsilon β I.Λ (m - 1) := by rw [div_eq_mul_inv]
      _ ≤ A / epsilon β I.Λ (m - 1) := div_le_div_of_nonneg_right hA he.le
  have hpow :
      (2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹) ^ (n - 1) ≤
        (A / epsilon β I.Λ (m - 1)) ^ (n - 1) := by
    exact pow_le_pow_left₀ (by positivity) hratio (n - 1)
  have hcoeff : 2 ≤ A := by
    have : (2 : ℝ) ≤ (2 : ℝ) ^ (14 : ℕ) := by norm_num
    exact this.trans hA
  have htarget :
      2 * n.factorial *
          (2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹) ^ (n - 1) ≤
        A * n.factorial *
          (A / epsilon β I.Λ (m - 1)) ^ (n - 1) := by
    have hfac : 0 ≤ (n.factorial : ℝ) := by positivity
    have hbase : 0 ≤
        (2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹) ^ (n - 1) := by positivity
    have hA0 : 0 ≤ A := le_trans (by positivity) hA
    calc
      2 * n.factorial *
          (2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹) ^ (n - 1)
          ≤ A * n.factorial *
              (2 ^ 14 * (epsilon β I.Λ (m - 1))⁻¹) ^ (n - 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoeff hfac) hbase
      _ ≤ A * n.factorial *
            (A / epsilon β I.Λ (m - 1)) ^ (n - 1) := by
            exact mul_le_mul_of_nonneg_left hpow
              (mul_nonneg hA0 hfac)
  exact hbase.trans (ENNReal.ofReal_le_ofReal htarget)

/-- Produce the exact unfolded `hFlow` family from the stream-function all-order
AppB2 input. The previous-scale `e.indyhyp` is obtained by the proved Section
2 stream induction, so callers supply only the canonical scale and AppB2
data. The conclusion is definitionally equal to the
`FlowForErgodicBound` predicate at each supported time. -/
theorem flowForErgodicBound_of_appB2
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hΦ : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hΦ R M)
    (A : ℝ) (hA : 2 ^ (14 : ℕ) ≤ A) :
    ∀ m : ℕ, 2 ≤ m →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ k : ℤ, Odd k → I.xiMK m k t ≠ 0 →
        ∀ n : ℕ, 1 ≤ n →
          derivativeSup n (I.xFlow hΦ m (lIdx β I.Λ m k) t) ≤
            ENNReal.ofReal
              (A * n.factorial *
                (A / epsilon β I.Λ (m - 1)) ^ (n - 1)) := by
  have hind := section2_stream_induction hscales happB2
  intro m hm t ht k hk hξ n hn
  exact flowForErgodicBound_of_section2_previous hscales happB2
    m hm k A hA (hind (m - 2)) t ht hξ n hn

/-- Instantiate the exact unfolded `hFlow` family from the canonical
Section 2 scales and the smooth-flow AppB2 constructor. This is the form
available directly from the stream-function stream witness. -/
theorem flowForErgodicBound_of_stream
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (A : ℝ) (hA : 2 ^ (14 : ℕ) ≤ A) :
    ∀ m : ℕ, 2 ≤ m →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ k : ℤ, Odd k → I.xiMK m k t ≠ 0 →
        ∀ n : ℕ, 1 ≤ n →
          derivativeSup n (I.xFlow hΦ m (lIdx β I.Λ m k) t) ≤
            ENNReal.ofReal
              (A * n.factorial *
                (A / epsilon β I.Λ (m - 1)) ^ (n - 1)) := by
  let hscales := section2Scales_canonical I
  let happB2 := appB2InverseFlowData_of_smoothPeriodicFlow hΦ hscales
  exact flowForErgodicBound_of_appB2 hscales happB2 A hA

end AVenhance.Infra.Section5.AnalyticBridge

end
