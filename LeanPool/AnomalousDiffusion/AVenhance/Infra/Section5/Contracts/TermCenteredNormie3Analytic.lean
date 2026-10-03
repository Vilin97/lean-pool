/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredNormie3Slow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalyticCompose
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalytic

/-! # Composed analyticity of the slow factor of `normie3`

`n3Slow_{pj} = slowFactorChoice3 ξ_k Y F (T t) p j` with `Y = Fᵀ` (the transpose of the flow
Jacobian, not `1 - Fᵀ`), so the choice-3 composed bound of `SlowFactorBoundsComposition`
applies with the word bound `41` of the entries of `Q = F` (`sdj_Q_word`). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section4
    AVenhance.Infra.Section5.RelativeError

theorem n3Slow_eq_choice3 {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ)
    (hT : ContDiff ℝ ∞ (T t)) (p j : Fin 2) :
    n3Slow I hΦ m T k t p j =
      slowFactorChoice3 (I.xiMK m k t)
        (fun x => (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose)
        (I.flowGrad hΦ m (lIdx β I.Λ m k) t) (T t) p j := by
  unfold n3Slow slowFactorChoice3 slowFactorContractH flowGradK
  simp_rw [slowFactorH_eq_actual_gradG I hΦ m T _ t hT]
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.mul_apply, Matrix.transpose_apply]

/-- The core of `n3_slow_composed_bounds`, with the constants explicit.  Here `A₁ = max A 2^14`,
`K` is the absolute polynomial-versus-exponential constant. -/
theorem n3c_core {β : ℝ} (A : ℝ) (hA : 1 ≤ A) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n)
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m)
    {S : ℝ} (hS : 0 ≤ S) (T : ℝ → Vec 2 → ℝ)
    (hJets : PositiveTemperatureJets A (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) S T)
    (hTs : ∀ t : ℝ, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (T t))
    (hTp : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (T t))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {k : ℤ} (hξ : I.xiMK m k t ≠ 0) (p j : Fin 2) :
    Infra.Ergodic.HasCoordinateAnalyticL2Bounds
        (fun x => ((n3Slow I hΦ m T k t p j
          (I.xFlow hΦ m (lIdx β I.Λ m k) t x) : ℝ) : ℂ))
        ((64 * 41 * 41 * A * (max A (2 ^ 14)) ^ 2) * S *
          ((epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ 2)⁻¹)
        (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) /
          (2 * 2 ^ 14 * 33 * K * max A (2 ^ 14))) := by
  set ε : ℝ := epsilon β I.Λ (m - 1) with hε
  set ρ : ℝ := ε ^ (1 + gamma β / 2) with hρdef
  set A₁ : ℝ := max A (2 ^ 14) with hA₁
  have hA₁1 : 1 ≤ A₁ := le_max_of_le_left hA
  have hA₁2 : (2 : ℝ) ^ 14 ≤ A₁ := le_max_right _ _
  have hA0 : 0 ≤ A := by linarith
  have he : 0 < ε := sdw_eps_pos I (m - 1)
  have he1 : ε ≤ 1 := sdw_eps_le_one I (m - 1)
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
  have hρ : 0 < ρ := Real.rpow_pos_of_pos he _
  have hρε : ρ ≤ ε := by
    have h := Real.rpow_le_rpow_of_exponent_ge he he1 (show (1 : ℝ) ≤ 1 + gamma β / 2 by linarith)
    simpa [hρdef] using h
  set L : ℝ := A₁ / ρ with hLdef
  have hL0 : 0 < L := by positivity
  have hL : 2 ^ 11 * ε⁻¹ ≤ L := by
    have hinv : ε⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ hρε
    have hεpos : 0 ≤ ε⁻¹ := by positivity
    calc 2 ^ 11 * ε⁻¹ ≤ 2 ^ 11 * ρ⁻¹ := by gcongr
      _ ≤ A₁ * ρ⁻¹ := by
          have : (2 : ℝ) ^ 11 ≤ A₁ := le_trans (by norm_num) hA₁2
          gcongr
      _ = L := by rw [hLdef, div_eq_mul_inv]
  have hLA : A / ρ ≤ L := div_le_div_of_nonneg_right (le_max_left _ _) hρ.le
  let X := LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k) t
  have hCX : 0 < K * ε := by positivity
  have hR : 0 < 2 * 2 ^ 14 / ε := by positivity
  have hXb : ∀ (n : ℕ) (w : Fin n → Fin 2), 0 < n → ∀ (x : Vec 2) (i : Fin 2),
      |(Infra.Ergodic.spatialJet n X.toFun w x) i| ≤ (K * ε) * n.factorial * (2 * 2 ^ 14 / ε) ^ n :=
    fun n w hn x i => sdi_xFlow_jet_bound I hΦ hm k ht hξ hK n w hn x i
  have ht0 : 0 ≤ t := ht.1.le
  have hTt : ContDiff ℝ ∞ (T t) := hTs t ht0
  have hTb : ∀ w : List (Fin 2), 0 < w.length →
      eLpNorm (amnrSpaceWord w (T t)) 2 (volume.restrict (Infra.Torus.unitCell 2)) ≤
        ENNReal.ofReal ((A * S) * w.length.factorial * L ^ w.length) :=
    fun w hw => sdi_T_word_bound hJets hA0 hρ hS hLA ⟨ht0, ht.2.le⟩ hTt w hw
  have hQ : ∀ i j, ContDiff ℝ ∞ (fun x => I.flowGrad hΦ m (lIdx β I.Λ m k) t x i j) :=
    fun i j => sdj_contDiff_flowGrad_entry hΦ m _ t i j
  have hQb : ∀ i j w x, |amnrSpaceWord w (fun y => I.flowGrad hΦ m (lIdx β I.Λ m k) t y i j) x| ≤
      41 * w.length.factorial * L ^ w.length := fun i j w x => sdj_Q_word hΦ hm k hξ hL i j w x
  have hξ1 := sdi_xiMK_abs_le_one I m k t
  have hrad : ρ / (2 * 2 ^ 14 * 33 * K * A₁) ≤
      (16 * L)⁻¹ / ((2 * 2 ^ 14 / ε) * ((16 * L)⁻¹ + 2 * (K * ε))) :=
    sdc_radius_ge hρ hρε hK1 hA₁1
  have hr' : 0 < ρ / (2 * 2 ^ 14 * 33 * K * A₁) := by positivity
  have hLsq : L ^ 2 = A₁ ^ 2 * (ρ ^ 2)⁻¹ := by
    rw [hLdef, div_pow, div_eq_mul_inv]
  have hY : ∀ i j, ContDiff ℝ ∞ (fun x =>
      (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose i j) := by
    intro i j
    simpa only [Matrix.transpose_apply] using hQ j i
  have hYb : ∀ i j w x, |amnrSpaceWord w (fun y =>
      (I.flowGrad hΦ m (lIdx β I.Λ m k) t y).transpose i j) x| ≤
      41 * w.length.factorial * L ^ w.length := by
    intro i j w x
    simpa only [Matrix.transpose_apply] using hQb j i w x
  have hper : Infra.Ergodic.IsZPeriodic (slowFactorChoice3 (I.xiMK m k t)
      (fun x => (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose)
      (I.flowGrad hΦ m (lIdx β I.Λ m k) t) (T t) p j) := by
    rw [← n3Slow_eq_choice3 I hΦ m T k t hTt p j]
    exact (n3Slow_smooth_periodic I hΦ m T hTt (hTp t ht0) k p j).2
  have hmain := slowFactorChoice3_composed_bounds X hQ hTt (CQ := 41) (M := A * S)
    (by norm_num) (by positivity) hL0 hCX hR hQb hTb hXb hY (CY := 41) (by norm_num) hξ1
    hYb p j hper
  have heq : (fun x => ((n3Slow I hΦ m T k t p j
        (I.xFlow hΦ m (lIdx β I.Λ m k) t x) : ℝ) : ℂ)) =
      fun x => ((slowFactorChoice3 (I.xiMK m k t)
        (fun x => (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose)
        (I.flowGrad hΦ m (lIdx β I.Λ m k) t) (T t) p j (X.toFun x) : ℝ) : ℂ) := by
    rw [n3Slow_eq_choice3 I hΦ m T k t hTt p j]
    rfl
  rw [heq]
  refine sdc_hasCoordinate_mono hmain (by positivity) ?_ hr' hrad
  rw [hLsq]
  exact le_of_eq (by ring)

/-- **Composed analyticity of the slow factor of `normie3` on `supp ξ_{m,k}`**.  The constants
depend only on the jet constant `A` and `β`. -/
theorem n3_slow_composed_bounds (β A : ℝ) (hA : 1 ≤ A) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (_hm : 2 ≤ m)
        {S : ℝ} (_hS : 0 ≤ S) (T : ℝ → Vec 2 → ℝ)
        (_hJets : PositiveTemperatureJets A (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) S T)
        (_hTs : ∀ t : ℝ, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (T t))
        (_hTp : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (T t))
        (_hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 / 4)
        {t : ℝ} (_ht : t ∈ Set.Ioo (0 : ℝ) 1) {k : ℤ} (_hξ : I.xiMK m k t ≠ 0) (p j : Fin 2),
        Infra.Ergodic.HasCoordinateAnalyticL2Bounds
          (fun x => ((n3Slow I hΦ m T k t p j
            (I.xFlow hΦ m (lIdx β I.Λ m k) t x) : ℝ) : ℂ))
          (c₁ * S * ((epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ 2)⁻¹)
          (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) / c₂) := by
  obtain ⟨K, hK1, hK⟩ := AnalyticBridge.exists_poly_le_two_pow
  have hA₁ : 1 ≤ max A (2 ^ 14) := le_max_of_le_left hA
  have hA0 : 0 < A := by linarith
  refine ⟨64 * 41 * 41 * A * (max A (2 ^ 14)) ^ 2, 2 * 2 ^ 14 * 33 * K * max A (2 ^ 14),
    by positivity, by positivity, ?_⟩
  intro I Φ hΦ m hm S hS T hJets hTs hTp hsmall t ht k hξ p j
  exact n3c_core A hA hK1 hK I hΦ hm hS T hJets hTs hTp ht hξ p j

end AVenhance.Infra.Section5.Contracts
end
