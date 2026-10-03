/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.SpaceErgodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ClassicalRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy

/-! Amplitude-generic leading-energy estimates on the actual datum and T iterates.
The quadratic error has amplitude S squared; the base consumes only integrated gradients. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section3 AVenhance.Infra.Section5.LeftToShow

/-! ## Abstract real arithmetic -/

/-- `e^{-qγ}` dominates `1` for `e ≤ 1`, and `(e^q/2)^{-γ} = 2^γ e^{-qγ}`. -/
theorem RelativeSpaceKill.rpow_half_neg_le {e q γ ε : ℝ} (he : 0 < e) (hγ : 0 ≤ γ)
    (hε : e ^ q / 2 ≤ ε) :
    ε ^ (-γ) ≤ 2 ^ γ * e ^ (-(q * γ)) := by
  have hpos : 0 < e ^ q / 2 := by positivity
  have h1 : ε ^ (-γ) ≤ (e ^ q / 2) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos hpos hε (by linarith)
  refine h1.trans (le_of_eq ?_)
  rw [Real.div_rpow (Real.rpow_nonneg he.le _) (by norm_num), ← Real.rpow_mul he.le,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  congr 2
  ring

/-- `2 B + 2 B² ≤ 4 b²` for `0 ≤ B ≤ b`, `1 ≤ b`. -/
theorem RelativeSpaceKill.two_mul_add_le {B b : ℝ} (hB : 0 ≤ B) (hBb : B ≤ b) (hb : 1 ≤ b) :
    2 * B + 2 * B ^ 2 ≤ 4 * b ^ 2 := by
  have h1 : B ≤ b ^ 2 := by
    calc B ≤ b := hBb
      _ = b * 1 := (mul_one b).symm
      _ ≤ b * b := mul_le_mul_of_nonneg_left hb (by linarith)
      _ = b ^ 2 := (sq b).symm
  have h2 : B ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hB hBb 2
  linarith only [h1, h2]

/-- Exponents combine: `e^{-P} · (e^{-qγ})² · e^{500+P+2qγ} = e^{500}`. -/
theorem RelativeSpaceKill.rpow_exponents_combine {e : ℝ} (he : 0 < e) (P qγ : ℝ) :
    e ^ (-P) * (e ^ (-qγ)) ^ 2 * e ^ (500 + P + 2 * qγ) = e ^ (500 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul he.le, ← Real.rpow_add he, ← Real.rpow_add he]
  congr 1
  push_cast
  ring

/-- The pure-real core of the scaled estimate. -/
theorem space_kill_scalar (A K q γ g P W : ℝ) (hA : 0 < A) (hK : 1 ≤ K) (hq : 0 ≤ q)
    (hγ : 0 ≤ γ) (hg : 0 < g) (hP : 0 ≤ P) (hW : 0 ≤ W) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ e ε κ B rN θ2 : ℝ, 0 < e → e ≤ 1 → e ^ q / 2 ≤ ε → 0 < κ → κ ≤ K →
      0 ≤ B → B ≤ K * ε ^ (-γ) → e ^ (-g) / (A * K) ≤ rN → 0 ≤ θ2 →
      κ * (4 * 512 * (A * e ^ (-P) * θ2) * (2 * B + 2 * B ^ 2) * W * Real.exp (-rN / 1024)) ≤
        C' * e ^ (500 : ℝ) * θ2 := by
  have hK0 : 0 < K := by linarith only [hK]
  have hAK : 0 < A * K := mul_pos hA hK0
  have hqγ : 0 ≤ q * γ := mul_nonneg hq hγ
  obtain ⟨K', hK'pos, hK'⟩ := exp_neg_rpow_le_rpow hg (by positivity : 0 < 1024 * (A * K))
    (by positivity : 0 ≤ 500 + P + 2 * (q * γ))
  have h2g : (1 : ℝ) ≤ 2 ^ γ := Real.one_le_rpow (by norm_num) hγ
  refine ⟨K * (2048 * A) * (4 * (K * 2 ^ γ) ^ 2) * W * K', by positivity, ?_⟩
  intro e ε κ B rN θ2 he he1 hε hκ hκK hB hBb hrN hθ
  have hEge : 1 ≤ e ^ (-(q * γ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos he he1 (by linarith only [hqγ])
  set E := e ^ (-(q * γ)) with hE
  have hBE : B ≤ K * (2 ^ γ * E) :=
    hBb.trans (mul_le_mul_of_nonneg_left (RelativeSpaceKill.rpow_half_neg_le he hγ hε) hK0.le)
  have hb1 : 1 ≤ K * (2 ^ γ * E) := by
    calc (1 : ℝ) = 1 * (1 * 1) := by norm_num
      _ ≤ K * (2 ^ γ * E) := by gcongr
  have hBsum : 2 * B + 2 * B ^ 2 ≤ 4 * (K * 2 ^ γ) ^ 2 * E ^ 2 := by
    refine (RelativeSpaceKill.two_mul_add_le hB hBE hb1).trans (le_of_eq ?_)
    ring
  have hexp : Real.exp (-rN / 1024) ≤ K' * e ^ (500 + P + 2 * (q * γ)) := by
    refine le_trans (Real.exp_le_exp.2 ?_) (hK' e he he1)
    have : e ^ (-g) / (1024 * (A * K)) ≤ rN / 1024 := by
      rw [div_le_iff₀ (by positivity)]
      calc e ^ (-g) = (e ^ (-g) / (A * K)) * (A * K) := by field_simp
        _ ≤ rN * (A * K) := by gcongr
        _ = rN / 1024 * (1024 * (A * K)) := by ring
    linarith only [this]
  have hcomb := RelativeSpaceKill.rpow_exponents_combine he P (q * γ)
  have hu : 0 ≤ e ^ (-P) := Real.rpow_nonneg he.le _
  have hw : 0 ≤ e ^ (500 + P + 2 * (q * γ)) := Real.rpow_nonneg he.le _
  have hEn : 0 ≤ E := by linarith only [hEge]
  have hexpn : 0 ≤ Real.exp (-rN / 1024) := (Real.exp_pos _).le
  calc κ * (4 * 512 * (A * e ^ (-P) * θ2) * (2 * B + 2 * B ^ 2) * W * Real.exp (-rN / 1024))
      ≤ K * (4 * 512 * (A * e ^ (-P) * θ2) * (4 * (K * 2 ^ γ) ^ 2 * E ^ 2) * W *
          (K' * e ^ (500 + P + 2 * (q * γ)))) := by
        gcongr
    _ = (K * (2048 * A) * (4 * (K * 2 ^ γ) ^ 2) * W * K') *
          (e ^ (-P) * E ^ 2 * e ^ (500 + P + 2 * (q * γ))) * θ2 := by ring
    _ = _ := by rw [hcomb]

/-- `r N ≥ ε_{m-1}^{-(q-1-γ/2)}/(AK)` from `ε_m ≤ K ε_{m-1}^q`. -/
theorem RelativeSpaceKill.rN_lower {e ε A K q γ : ℝ} (he : 0 < e) (hε : 0 < ε) (hA : 0 < A)
    (hεK : ε ≤ K * e ^ q) :
    e ^ (-(q - 1 - γ / 2)) / (A * K) ≤ e ^ (1 + γ / 2) / A * ε⁻¹ := by
  have hdiv : e ^ (-(q - 1 - γ / 2)) = e ^ (1 + γ / 2) / e ^ q := by
    rw [← Real.rpow_sub he]
    congr 1
    ring
  have hq : 0 < e ^ q := Real.rpow_pos_of_pos he q
  have hnum : 0 < e ^ (1 + γ / 2) := Real.rpow_pos_of_pos he _
  rw [hdiv, div_div, inv_eq_one_div, mul_one_div, div_div]
  refine div_le_div_of_nonneg_left hnum.le (by positivity) ?_
  calc A * ε ≤ A * (K * e ^ q) := by gcongr
    _ = e ^ q * (A * K) := by ring

/-- `1 ≤ ε^{-g}/(AK)` once `ε ≤ Λ⁻¹` and `(AK)^{1/g} ≤ Λ`. -/
theorem RelativeSpaceKill.one_le_of_small {e Λ A K g : ℝ} (he : 0 < e) (hΛ : 0 < Λ) (hA : 0 < A)
    (hK : 0 < K) (hg : 0 < g) (heΛ : e ≤ Λ⁻¹) (hΛ' : (A * K) ^ (1 / g) ≤ Λ) :
    1 ≤ e ^ (-g) / (A * K) := by
  have h1 : (Λ⁻¹) ^ (-g) ≤ e ^ (-g) := Real.rpow_le_rpow_of_nonpos he heΛ (by linarith)
  have h2 : (Λ⁻¹) ^ (-g) = Λ ^ g := by
    rw [Real.inv_rpow hΛ.le, Real.rpow_neg hΛ.le, inv_inv]
  have h3 : A * K ≤ Λ ^ g := by
    have := Real.rpow_le_rpow (by positivity) hΛ' hg.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hg.ne', Real.rpow_one] at this
  rw [le_div_iff₀ (by positivity), one_mul]
  exact h3.trans (h2 ▸ h1)

theorem RelativeSpaceKill.l2NormSq_nonneg_sk (f : Vec 2 → ℝ) : 0 ≤ l2NormSq f :=
  integral_nonneg fun x => sq_nonneg (f x)

theorem RelativeSpaceKill.a_nonneg_sk {β : ℝ} (I : Ingredients β) (m : ℕ) : 0 ≤ a β I.Λ m :=
  (Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)).le

/-- Integrating a pointwise bound on `(0,1)` over `[0,1]` (the endpoint is null). -/
theorem RelativeSpaceKill.norm_intervalIntegral_le_of_Ioo {f : ℝ → ℝ} {c : ℝ}
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |f t| ≤ c) : |∫ t in (0 : ℝ)..1, f t| ≤ c := by
  have hae : ∀ᵐ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 → ‖f t‖ ≤ c := by
    filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem volume] with t ht htI
    rw [Set.uIoc_of_le zero_le_one] at htI
    have hne : t ≠ 1 := fun h1 => ht (by simp [h1])
    have : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨htI.1, lt_of_le_of_ne htI.2 hne⟩
    simpa [Real.norm_eq_abs] using h t this
  have := intervalIntegral.norm_integral_le_of_norm_le_const_ae hae
  simpa [Real.norm_eq_abs] using this

/-- e.ergodic.space.kill (8510–8633). -/
theorem relative_ergodic_space_kill (β C₀ A P : ℝ) (hA : 0 < A) (hP : 0 ≤ P) :
    ∃ C : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (S : ℝ) (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ k : ℤ, Odd k → I.xiMK m k t ≠ 0 → ∀ i j : Fin 2,
          Infra.Ergodic.HasCoordinateAnalyticL1Bounds
            (fun y => ((spaceGrad (T (Nstar β) t) (I.xFlow hΦ m (lIdx β I.Λ m k) t y) i *
              spaceGrad (T (Nstar β) t) (I.xFlow hΦ m (lIdx β I.Λ m k) t y) j : ℝ) : ℂ))
            (A * epsilon β I.Λ (m - 1) ^ (-P) * S ^ 2)
            (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) / A)) →
        I.kappaSeq κ M m * |∫ t in (0 : ℝ)..1,
            ((∫ x in unitCube, vecNormSq (leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t
                x)) -
              gradQuad (T (Nstar β)) (leadingGramAvg I hΦ m (I.kappaSeq κ M m) t) t)| ≤
          C * epsilon β I.Λ (m - 1) ^ (500 : ℝ) * S ^ 2 := by
  classical
  obtain ⟨K, hK1, hKs⟩ := left_to_show_scales β C₀
  by_cases hb : 1 < β ∧ β < 4 / 3
  swap
  · exact ⟨0, fun I => absurd ⟨I.one_lt_beta, I.beta_lt⟩ hb⟩
  have hg : 0 < q β - 1 - gamma β / 2 := ergodic_gap_pos hb.1 hb.2
  have hγ : 0 ≤ gamma β := (Infra.Ingredients.gamma_pos hb.1 hb.2).le
  have hq0 : 0 ≤ q β := by linarith only [Infra.Ingredients.one_lt_q hb.1 hb.2]
  have hW : 0 ≤ ∑' k : Fin 2 → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  obtain ⟨C', hC'0, hC'⟩ := space_kill_scalar A K (q β) (gamma β) (q β - 1 - gamma β / 2) P
    (∑' k : Fin 2 → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) hA hK1 hq0 hγ hg hP hW
  refine ⟨max C' ((A * K) ^ (1 / (q β - 1 - gamma β / 2))), ?_⟩
  intro I hz hx hh hCΛ Φ hΦ κ hκ M hM hperm m hm hmM S θ₀ θprev T hT hAn
  obtain ⟨hκm0, hκle, hκK, -, -, hBK, hεK⟩ := hKs I hz hx hh κ hκ M hM hperm m hm hmM
  have hK0 : 0 < K := by linarith only [hK1]
  set e := epsilon β I.Λ (m - 1) with he_def
  set εm := epsilon β I.Λ m with hεm_def
  have he : 0 < e := Infra.Cutoff.epsilon_pos hb.1 hb.2 I.two_pow_seven_le
  have hεpos : 0 < εm := Infra.Cutoff.epsilon_pos hb.1 hb.2 I.two_pow_seven_le
  have hΛpos : (0 : ℝ) < I.Λ := by
    have : (128 : ℝ) ≤ I.Λ := by exact_mod_cast I.two_pow_seven_le
    linarith only [this]
  have heΛ : e ≤ (I.Λ : ℝ)⁻¹ :=
    epsilon_le_inv_Lambda hb.1 hb.2 I.two_pow_seven_le (m := m - 1) (by omega)
  have he1 : e ≤ 1 := by
    refine heΛ.trans ?_
    have : (1 : ℝ) ≤ I.Λ := by
      have : (128 : ℝ) ≤ I.Λ := by exact_mod_cast I.two_pow_seven_le
      linarith only [this]
    exact inv_le_one_of_one_le₀ this
  have hεlow : e ^ q β / 2 ≤ εm :=
    epsilon_pred_pow_q_div_two_le hb.1 hb.2 I.two_pow_seven_le hm
  have hAK : (A * K) ^ (1 / (q β - 1 - gamma β / 2)) ≤ I.Λ :=
    (le_max_right _ _).trans hCΛ
  have hrN_low := RelativeSpaceKill.rN_lower (γ := gamma β) he hεpos hA hεK
  have hrN1 := RelativeSpaceKill.one_le_of_small he hΛpos hA hK0 hg heΛ hAK
  have hNcast : (ergodicFrequency β I.Λ m : ℝ) = εm⁻¹ := ergodicFrequency_cast β I.Λ m
  have hrN_ge : e ^ (-(q β - 1 - gamma β / 2)) / (A * K) ≤
      e ^ (1 + gamma β / 2) / A * (ergodicFrequency β I.Λ m : ℝ) := by
    rw [hNcast]; exact hrN_low
  have hrN_one : 1 ≤ e ^ (1 + gamma β / 2) / A * (ergodicFrequency β I.Λ m : ℝ) :=
    hrN1.trans hrN_ge
  -- regularity of the last iterate
  have hN1 : 1 ≤ Nstar β := by
    have h := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  have hlast := hT.2 (Nstar β) hN1 le_rfl
  have hθ2 : 0 ≤ S ^ 2 := sq_nonneg S
  have hCf : 0 ≤ A * e ^ (-P) * S ^ 2 := by
    have : 0 ≤ e ^ (-P) := Real.rpow_nonneg he.le _
    positivity
  have hr : 0 < e ^ (1 + gamma β / 2) / A := div_pos (Real.rpow_pos_of_pos he _) hA
  have hBnn : 0 ≤ a β I.Λ m * εm ^ 2 / I.kappaSeq κ M m := by
    have := RelativeSpaceKill.a_nonneg_sk I m
    positivity
  have hslice : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      |(∫ x in unitCube, vecNormSq (leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x)) -
          gradQuad (T (Nstar β)) (leadingGramAvg I hΦ m (I.kappaSeq κ M m) t) t| ≤
        4 * 512 * (A * e ^ (-P) * S ^ 2) *
          (2 * (a β I.Λ m * εm ^ 2 / I.kappaSeq κ M m) +
            2 * (a β I.Λ m * εm ^ 2 / I.kappaSeq κ M m) ^ 2) *
          (∑' k : Fin 2 → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) *
          Real.exp (-(e ^ (1 + gamma β / 2) / A * (ergodicFrequency β I.Λ m : ℝ)) / 1024) := by
    intro t ht
    exact ergodic_space_kill_slice I hΦ (by omega) hκm0
      (Infra.Classical.classicalSmooth_slice_nonneg hlast.1 ht.1.le) (hlast.2.1 t ht.1.le) hCf hr
      (hAn t ht) hrN_one
  have hint := RelativeSpaceKill.norm_intervalIntegral_le_of_Ioo hslice
  have hfin := hC' e εm (I.kappaSeq κ M m) (a β I.Λ m * εm ^ 2 / I.kappaSeq κ M m)
    (e ^ (1 + gamma β / 2) / A * (ergodicFrequency β I.Λ m : ℝ)) (S ^ 2) he he1 hεlow
    hκm0 (hκle.trans hκK) hBnn hBK hrN_ge hθ2
  calc I.kappaSeq κ M m * _ ≤ _ := mul_le_mul_of_nonneg_left hint hκm0.le
    _ ≤ C' * e ^ (500 : ℝ) * S ^ 2 := hfin
    _ ≤ _ := by
      have h0 : 0 ≤ e ^ (500 : ℝ) * S ^ 2 := mul_nonneg (Real.rpow_nonneg he.le _) hθ2
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) h0

end AVenhance.Infra.Section5.RelativeError

end
