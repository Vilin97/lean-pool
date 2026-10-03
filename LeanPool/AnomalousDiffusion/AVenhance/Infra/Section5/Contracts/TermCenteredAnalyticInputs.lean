/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsCentered
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.FlowForErgodicBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.CompBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.ScalarQuadraticL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragesL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalyticJets

/-! # Temperature, flow and cutoff inputs of the composed slow-factor bounds

* `ξ_{m,k}` is bounded by one;
* `PositiveTemperatureJets` give the `L²(unitCell)` word bounds of `T t`;
* the Section 2 derivative bounds of the flow slice give the pointwise coordinate-jet bounds of
  `X.toFun` (through the normalized seminorm `snorm`). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Construction AVenhance.Infra.Section5
open AVenhance.Infra.Section4 AVenhance.Infra.Section5.RelativeError

theorem sdi_xiMK_abs_le_one {β : ℝ} (I : Ingredients β) (m : ℕ) (k : ℤ) (t : ℝ) :
    |I.xiMK m k t| ≤ 1 := by
  have h1 := I.ind_le_xi ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
  have h2 := I.xi_le_ind ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
  have h3 : 0 ≤ indIcc (-(3 / 4) : ℝ) (3 / 4) ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) :=
    indIcc_nonneg' _ _ _
  have h4 : indIcc (-(5 / 4) : ℝ) (5 / 4) ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) ≤ 1 := by
    by_cases h : ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) ∈ Set.Icc (-(5 / 4) : ℝ) (5 / 4) <;>
      simp [indIcc, h]
  have hx : I.xiMK m k t = I.xi ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) := rfl
  rw [hx, abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ### Temperature -/

/-- Positive temperature jets give the `L²(unitCell)` word bounds of `T t`. -/
theorem sdi_T_word_bound {A ρ S : ℝ} {T : ℝ → Vec 2 → ℝ}
    (hJets : PositiveTemperatureJets A ρ S T) (hA : 0 ≤ A) (hρ : 0 < ρ) (hS : 0 ≤ S)
    {L : ℝ} (hL : A / ρ ≤ L) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hTt : ContDiff ℝ ∞ (T t)) (w : List (Fin 2)) (hw : 0 < w.length) :
    eLpNorm (amnrSpaceWord w (T t)) 2 (volume.restrict (Infra.Torus.unitCell 2)) ≤
      ENNReal.ofReal (A * S * w.length.factorial * L ^ w.length) := by
  have hcont : Continuous (amnrSpaceWord w (T t)) := (slowWord_smooth hTt w).continuous
  have hg : amnrSpaceWord w (T t) = fun x => iteratedFDeriv ℝ w.length (T t) x
      (fun j => basisVec (amnrSpatialIndices w j)) := by
    rw [amnrSpaceWord_eq_iteratedFDeriv hTt w, amnrSpatialDirections_eq]
  have hJ := hJets w.length (amnrSpatialIndices w) hw t ht
  rw [← hg] at hJ
  have hB0 : 0 ≤ A * S * w.length.factorial * (A / ρ) ^ w.length := by positivity
  have hsq := (Real.sqrt_le_iff.mp hJ).2
  have hint : IntegrableOn (fun x => amnrSpaceWord w (T t) x ^ 2) (Infra.Torus.unitCell 2) :=
    Ergodic.continuous_unitCell_integrable (hcont.pow 2)
  have hle : eLpNorm (amnrSpaceWord w (T t)) 2 (volume.restrict (Infra.Torus.unitCell 2)) ≤
      ENNReal.ofReal (A * S * w.length.factorial * (A / ρ) ^ w.length) := by
    refine amnr_scalar_eLpNorm_two_le_of_square hcont.aestronglyMeasurable hint hB0 ?_
    rw [Infra.Torus.integral_unitCell_eq_unitCube]
    exact hsq
  refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
  have : (A / ρ) ^ w.length ≤ L ^ w.length := pow_le_pow_left₀ (by positivity) hL _
  have h0 : 0 ≤ A * S * w.length.factorial := by positivity
  exact mul_le_mul_of_nonneg_left this h0

/-! ### Flow slice -/

theorem sdi_orderedPartial_eq_iteratedFDeriv {n : ℕ} {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (J : Fin n → Fin 2) :
    FaaDiBruno.orderedPartial n f x J = iteratedFDeriv ℝ n f x (fun j => basisVec (J j)) := by
  unfold FaaDiBruno.orderedPartial FaaDiBruno.liftVecOne
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  change iteratedFDeriv ℝ n
      (f ∘ (FaaDiBruno.vecOneEquiv 2).toContinuousLinearMap)
      (WithLp.toLp 1 x)
      (fun j => FaaDiBruno.coordinateVectorOne 2 (J j)) = _
  rw [(FaaDiBruno.vecOneEquiv 2).toContinuousLinearMap.iteratedFDeriv_comp_right
    hfN (WithLp.toLp 1 x) le_rfl]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    FaaDiBruno.vecOneEquiv, FaaDiBruno.coordinateVectorOne, Homogenization.basisVec,
    PiLp.coe_continuousLinearEquiv]

/-- Pointwise coordinate-jet bounds of the flow slice on `supp ξ_{m,k}`:
`|∂^w X_j| ≤ K ε · n! · (2·2^14/ε)^n` (`e.flow.for.ergodic`). -/
theorem sdi_xFlow_jet_bound {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hξ : I.xiMK m k t ≠ 0) {K : ℝ} (hK : ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n)
    (n : ℕ) (w : Fin n → Fin 2) (hn : 0 < n) (x : Vec 2) (j : Fin 2) :
    |(Infra.Ergodic.spatialJet n (I.xFlow hΦ m (lIdx β I.Λ m k) t) w x) j| ≤
      (K * epsilon β I.Λ (m - 1)) * n.factorial *
        (2 * 2 ^ 14 / epsilon β I.Λ (m - 1)) ^ n := by
  have he := sdw_eps_pos I (m - 1)
  have hscales := section2Scales_canonical I
  have happB2 := appB2InverseFlowData_of_smoothPeriodicFlow hΦ hscales
  have hind := section2_stream_induction hscales happB2
  have hX : AnalyticBridge.FlowForErgodicBound (2 ^ 14) (epsilon β I.Λ (m - 1))
      (I.xFlow hΦ m (lIdx β I.Λ m k) t) := fun n hn =>
    AnalyticBridge.flowForErgodicBound_of_section2_previous hscales happB2 m hm k (2 ^ 14)
      (by norm_num) (hind (m - 2)) t ht hξ n hn
  have hs := AnalyticBridge.snorm_flow_le hK (by norm_num : (0 : ℝ) < 2 ^ 14) he hX n hn
  have hXs : ContDiff ℝ (⊤ : ℕ∞) (I.xFlow hΦ m (lIdx β I.Λ m k) t) :=
    RelativeError.contDiff_xFlow_slice I hΦ m (lIdx β I.Λ m k) t
  have hK1 : 0 ≤ K := by
    have h0 := hK 0
    norm_num at h0
    linarith
  have hC : 0 ≤ K * epsilon β I.Λ (m - 1) := by positivity
  have hR : 0 < 2 * 2 ^ 14 / epsilon β I.Λ (m - 1) := by positivity
  have hp := FaaDiBruno.orderedPartial_norm_le_of_snorm_le (I.xFlow hΦ m (lIdx β I.Λ m k) t)
    (hXs.of_le (by exact_mod_cast le_top)) le_rfl hR hC hs x w
  rw [sdi_orderedPartial_eq_iteratedFDeriv hXs] at hp
  have hn2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h2 : K * epsilon β I.Λ (m - 1) * n.factorial * (2 * 2 ^ 14 / epsilon β I.Λ (m - 1)) ^ n /
      ((n : ℝ) + 1) ^ 2 ≤ K * epsilon β I.Λ (m - 1) * n.factorial *
        (2 * 2 ^ 14 / epsilon β I.Λ (m - 1)) ^ n :=
    div_le_self (by positivity) hn2
  refine le_trans ?_ (hp.trans h2)
  rw [← Real.norm_eq_abs]
  exact norm_le_pi_norm _ j

end AVenhance.Infra.Section5.Contracts
end
