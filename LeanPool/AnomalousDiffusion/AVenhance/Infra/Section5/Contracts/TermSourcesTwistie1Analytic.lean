/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1Flow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsCentered
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesForcingSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialPeriodicity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingFluxEnergy

/-! # Composed analyticity of the `twistie1` slow factor

For `ξ_{m,k}(t) ≠ 0` the slow factor `f = ξ_{m,k} (∇X ∘ X⁻¹) ∇ ∇·(B ∇T)` (component `j`, choice
`e.fg.choice.1`) composed with the flow slice `X = X_{m-1,l_k}(t)` is analytic in `L²(𝕋²)` with
amplitude `C_f` and radius `r`, in terms of the jets of the coefficient `B = K_m + s_{m-1}` and of
the positive jets of `T` at the common rate `L ≥ 2^{10}/ε_{m-1}`
(`slowFactorChoice1_composed_bounds`). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff ENNReal

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Ergodic

/-- Monotonicity of the analytic `L²` bounds in the radius. -/
theorem se_analyticL2_mono {f : Vec 2 → ℂ} {Cf r r' : ℝ} (hCf : 0 ≤ Cf) (hr' : 0 < r')
    (hrr : r' ≤ r) (h : HasCoordinateAnalyticL2Bounds f Cf r) :
    HasCoordinateAnalyticL2Bounds f Cf r' := by
  intro i n
  refine (h i n).trans ?_
  have hfac : (0 : ℝ) ≤ Cf * (n.factorial : ℝ) := by positivity
  exact div_le_div_of_nonneg_left hfac (pow_pos hr' n) (pow_le_pow_left₀ hr'.le hrr n)

/-- Periodicity of `∇ ∇·(B ∇ T)` (component `i`). -/
theorem se_slowFactorGradDiv_periodic {B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {T : Vec 2 → ℝ}
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x => B x i j)) (hBper : IsZ2Periodic B)
    (hT : ContDiff ℝ ∞ T) (hTper : IsZ2Periodic T) (i : Fin 2) :
    IsZ2Periodic (slowFactorGradDiv B T i) := by
  have hG : ∀ j, IsZ2Periodic (slowFactorG B T j) := by
    intro j n x
    simp only [slowFactorG, Finset.sum_apply, Pi.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show B (x + latticeShift n) j k = B x j k from by rw [hBper n x],
      amnrSpaceWord_periodic hT hTper [k] n x]
  have hDiv : IsZ2Periodic (slowFactorDiv B T) := by
    intro n x
    simp only [slowFactorDiv, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ =>
      amnrSpaceWord_periodic (slowFactorG_smooth hB hT j) (hG j) [j] n x
  have hDivS : ContDiff ℝ ∞ (slowFactorDiv B T) := by
    have hh := ContDiff.sum (s := Finset.univ)
      (fun j _ => slowWord_smooth (slowFactorG_smooth hB hT j) [j])
    convert hh using 1
    funext x
    simp only [slowFactorDiv, Finset.sum_apply]
  exact amnrSpaceWord_periodic hDivS hDiv [i]

theorem se_slowFactorChoice1_periodic {ξ : ℝ} {Q B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {T : Vec 2 → ℝ} (hQper : IsZ2Periodic Q)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x => B x i j)) (hBper : IsZ2Periodic B)
    (hT : ContDiff ℝ ∞ T) (hTper : IsZ2Periodic T) (j : Fin 2) :
    IsZPeriodic (slowFactorChoice1 ξ Q B T j) := by
  intro x n
  have hgd := fun i => se_slowFactorGradDiv_periodic hB hBper hT hTper i n x
  simp only [slowFactorChoice1, Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : (fun i => (n i : ℝ)) = latticeShift n := rfl
  rw [e, hQper n x, hgd i]

/-- The derivative bound `|∇ⁿ X| ≤ (ε/2^{13}) n! (2^{14}/ε)^n` of the flow slice in the form
required by the composition lemma. -/
theorem se_xFlow_hXb {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ) {t : ℝ} (hξ : I.xiMK m k t ≠ 0) :
    ∀ n (w : Fin n → Fin 2), 0 < n → ∀ x j,
      |(spatialJet n (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k) t).toFun w x) j| ≤
        (epsilon β I.Λ (m - 1) / 2 ^ 13) * n.factorial * (2 ^ 14 / epsilon β I.Λ (m - 1)) ^ n := by
  intro n w hn x j
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have h := se_xFlow_jet_le hΦ hm k hξ n hn w x
  have hj : |(spatialJet n (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k) t).toFun w x) j| ≤
      ‖iteratedFDeriv ℝ n (I.xFlow hΦ m (lIdx β I.Λ m k) t) x (fun j => basisVec (w j))‖ := by
    have := norm_le_pi_norm
      (iteratedFDeriv ℝ n (I.xFlow hΦ m (lIdx β I.Λ m k) t) x (fun j => basisVec (w j))) j
    simpa [spatialJet, Real.norm_eq_abs] using this
  refine hj.trans (h.trans (le_of_eq ?_))
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  field_simp

/-- **Composed analyticity of the slow factor of `twistie1`** (`e.fg.choice.1`,
`e.checking.f.ergodic`): the composition `f ∘ X_{m-1,l_k}(t)` has analytic `L²` bounds with
amplitude `2048 · 40 · C_B M L³` and radius `(16 L)⁻¹ / 2^{11}`, from the jets of `B` and the
positive jets of `T` at the rate `L ≥ 2^{10}/ε_{m-1}`. -/
theorem se_choice1_analytic {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ) {t : ℝ} (hξ : I.xiMK m k t ≠ 0)
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1)
    {B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x => B x i j)) (hBper : IsZ2Periodic B)
    {T : Vec 2 → ℝ} (hT : ContDiff ℝ ∞ T) (hTper : IsZ2Periodic T)
    {CB M L : ℝ} (hCB : 0 ≤ CB) (hM : 0 ≤ M) (hL : 2 ^ 10 / epsilon β I.Λ (m - 1) ≤ L)
    (hBb : ∀ i j w x, |amnrSpaceWord w (fun y => B y i j) x| ≤
      CB * w.length.factorial * L ^ w.length)
    (hTb : ∀ w : List (Fin 2), 0 < w.length →
      eLpNorm (amnrSpaceWord w T) 2 (volume.restrict (Infra.Torus.unitCell 2)) ≤
        ENNReal.ofReal (M * w.length.factorial * L ^ w.length)) (j : Fin 2) :
    HasCoordinateAnalyticL2Bounds
      (fun x => ((slowFactorChoice1 (I.xiMK m k t) (I.flowGrad hΦ m (lIdx β I.Λ m k) t) B T j
        (I.xFlow hΦ m (lIdx β I.Λ m k) t x) : ℝ) : ℂ))
      (2048 * 40 * CB * M * L ^ 3) ((16 * L)⁻¹ / 2 ^ 11) := by
  set e := epsilon β I.Λ (m - 1) with he_def
  have he : 0 < e := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he1 : e ≤ 1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have heL : 2 ^ 10 ≤ e * L := by
    have := mul_le_mul_of_nonneg_left hL he.le
    rwa [mul_div_cancel₀ _ he.ne'] at this
  set X := LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k) t with hX
  have hQ : ∀ i j, ContDiff ℝ ∞ (fun x => I.flowGrad hΦ m (lIdx β I.Λ m k) t x i j) := by
    intro i j
    exact (amnr_flowGrad_joint_contDiff_infty I hΦ m (lIdx β I.Λ m k) i j).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have hQb : ∀ i j w x, |amnrSpaceWord w (fun y => I.flowGrad hΦ m (lIdx β I.Λ m k) t y i j) x| ≤
      40 * w.length.factorial * L ^ w.length :=
    fun i j w x => se_flowGrad_entry_jet_le I hΦ hm k hξ hsmall hL w x i j
  have hξ1 : |I.xiMK m k t| ≤ 1 := by
    obtain ⟨h0, h1⟩ := Infra.Section3.xiMK_mem_Icc I (by omega : 1 ≤ m) k t
    rw [abs_of_nonneg h0]; exact h1
  have hper := se_slowFactorChoice1_periodic (ξ := I.xiMK m k t) (iterate_flowGrad_periodic I hΦ m
    (lIdx β I.Λ m k) t) hB hBper hT hTper j
  have hmain := slowFactorChoice1_composed_bounds X hQ hT (CQ := 40) (by norm_num) hM hL0
    (CX := e / 2 ^ 13) (R := 2 ^ 14 / e) (by positivity) (by positivity) hQb hTb
    (se_xFlow_hXb hΦ hm k hξ) hB hCB hξ1 hBb j hper
  refine se_analyticL2_mono (by positivity) (by positivity) ?_ hmain
  -- the radius comparison
  set r : ℝ := (16 * L)⁻¹ with hr
  have hr0 : 0 < r := by positivity
  have hrle : r ≤ e / 16 := by
    rw [hr, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hden : (2 ^ 14 / e) * (r + 2 * (e / 2 ^ 13)) ≤ 2 ^ 11 := by
    have h1 : (2 ^ 14 / e) * r ≤ 2 ^ 10 := by
      calc (2 ^ 14 / e) * r ≤ (2 ^ 14 / e) * (e / 16) :=
            mul_le_mul_of_nonneg_left hrle (by positivity)
        _ = 2 ^ 10 := by field_simp; norm_num
    have h2 : (2 ^ 14 / e) * (2 * (e / 2 ^ 13)) = 4 := by field_simp; norm_num
    nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end AVenhance.Infra.Section5.Contracts
end
