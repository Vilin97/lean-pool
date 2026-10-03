/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BracketFF
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.JhatFacts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.FlowDiffeo
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy

/-! # `e.ergodic.break.up.second` and `e.ergodic.break.up.last`, scaled

Source: `enhance.tex` 8466–8509 and 8640–8860.  The unscaled estimates `ergodic_break_up_second`,
`TJT_break`, `third_term_ibp` are combined with the scale package `left_to_show_scales`,
`left_to_show_condition` and the inputs `e.Tm.reg.upgrade` (`hT0`), `e.barf.cascade` (`hDt`). -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance AVenhance.Infra.Section3

/-! ## Abstract-real lemmas -/

/-- Squaring `√κ √G ≤ A √L`. -/
theorem mul_le_sq_of_sqrt_mul_le {κ G L A : ℝ} (hκ : 0 ≤ κ) (hG : 0 ≤ G)
    (h : Real.sqrt κ * Real.sqrt G ≤ A * Real.sqrt L) (hL : 0 ≤ L) : κ * G ≤ A ^ 2 * L := by
  have h0 : 0 ≤ Real.sqrt κ * Real.sqrt G := by positivity
  have h2 := pow_le_pow_left₀ h0 h 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hκ, Real.sq_sqrt hG, Real.sq_sqrt hL] at h2
  exact h2

/-- Final arithmetic of the `second` estimate. -/
theorem second_final {Lc X R κp e G L A K : ℝ} (hX0 : 0 ≤ X) (hR0 : 0 ≤ R) (hK : 0 ≤ K)
    (hκp : 0 ≤ κp) (hG : 0 ≤ G) (he : 0 ≤ e) (hXK : X ≤ K * κp) (hRK : R ≤ K * e) (hκG : κp * G ≤
        A ^ 2 * L) :
    2 * (Lc * X * R) * G ≤ (2 * |Lc| * K ^ 2) * e * (A ^ 2 * L) := by
  have h1 : Lc * X * R ≤ |Lc| * (K * κp) * (K * e) := by
    calc Lc * X * R ≤ |Lc| * X * R :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hX0) hR0
      _ ≤ |Lc| * (K * κp) * (K * e) := by
          gcongr
  have h2 : 2 * (Lc * X * R) * G ≤ 2 * (|Lc| * (K * κp) * (K * e)) * G := by gcongr
  have h3 : 2 * (|Lc| * (K * κp) * (K * e)) * G =
      (2 * |Lc| * K ^ 2) * e * (κp * G) := by ring
  have h4 : (2 * |Lc| * K ^ 2) * e * (κp * G) ≤ (2 * |Lc| * K ^ 2) * e * (A ^ 2 * L) := by
    gcongr
  exact h2.trans (h3 ▸ h4)

theorem spaceTimeGradNormSq_nonneg' (V : ℝ → Vec 2 → Vec 2) : 0 ≤ spaceTimeGradNormSq V :=
  integral_nonneg fun _ => vecNormSq_nonneg _

theorem l2NormSq_nonneg' (f : Vec 2 → ℝ) : 0 ≤ l2NormSq f :=
  integral_nonneg fun _ => sq_nonneg _

/-- Regularity of `T (Nstar β)` and periodicity of its slices. -/
theorem tIterates_classicalSol {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hΦ : IsStreamSeq I Φ} {m : ℕ} {κm κp : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κp θ₀ θprev T) :
    IsClassicalSol (streamVel (Φ (m - 1))) κp
      (I.TForcing hΦ m κm κp (T (Nstar β - 1))) θ₀ (T (Nstar β)) := by
  have hN : 1 ≤ Nstar β := by
    have h := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  exact hT.2 (Nstar β) hN le_rfl

/-! ## `e.ergodic.break.up.second` -/

/-- e.ergodic.break.up.second (8466–8509). -/
theorem ergodic_break_up_second_scaled (β C₀ A P : ℝ) (hA : 0 < A) (hP : 0 ≤ P) :
    ∃ C : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
        Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T (Nstar β) t) x)) ≤
          A * Real.sqrt (l2NormSq θ₀) →
        |∫ t in (0 : ℝ)..1, gradQuad (T (Nstar β))
            (I.kappaSeq κ M m • leadingGramAvg I hΦ m (I.kappaSeq κ M m) t -
              I.flux (I.kappaSeq κ M m) m t) t| ≤
          C * epsilon β I.Λ (m - 1) ^ (2 * delta β) * l2NormSq θ₀ := by
  have _hAP := And.intro hA hP
  obtain ⟨K, hK1, hK⟩ := left_to_show_scales β C₀
  obtain ⟨Λ₀, hΛ₀⟩ := left_to_show_condition β C₀
  refine ⟨max Λ₀ ((2 * |lFluxToEnergyConstant C₀| * K ^ 2) * A ^ 2), ?_⟩
  intro I hz hx hh hC Φ hΦ κ hκp M hM hperm m hm hmM θ₀ θprev T hTit hT0
  have hΛ0 : Λ₀ ≤ (I.Λ : ℝ) := le_trans (le_max_left _ _) hC
  obtain ⟨hκm, hmono, -, hs1, hs2, -, -⟩ := hK I hz hx hh κ hκp M hM hperm m hm hmM
  have hcond := hΛ₀ I hz hx hh hΛ0 κ hκp M hM hperm m hm hmM
  obtain ⟨hTsm, -, -, -⟩ := tIterates_classicalSol hTit
  have hκpp : 0 < I.kappaSeq κ M (m - 1) := lt_of_lt_of_le hκm hmono
  have hbound := ergodic_break_up_second I hΦ hz hh (by omega : 1 ≤ m) hκm hcond hTsm
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hεp : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hτ := I.tau_pos' m
  have hX0 : 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaSeq κ M m := by positivity
  have hR0 : 0 ≤ epsilon β I.Λ m ^ 2 / (I.kappaSeq κ M m * tau β I.Λ m) := by positivity
  have he : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) := Real.rpow_nonneg hεp.le _
  have hG : 0 ≤ spaceTimeGradNormSq (fun t x => spaceGrad (T (Nstar β) t) x) :=
    spaceTimeGradNormSq_nonneg' _
  have hL : 0 ≤ l2NormSq θ₀ := l2NormSq_nonneg' θ₀
  have hκG := mul_le_sq_of_sqrt_mul_le hκpp.le hG hT0 hL
  have hfin := second_final (Lc := lFluxToEnergyConstant C₀) hX0 hR0 (by linarith only [hK1])
      hκpp.le hG
    he hs1 hs2 hκG
  have hcc : (2 * |lFluxToEnergyConstant C₀| * K ^ 2) * A ^ 2 ≤ max Λ₀
      ((2 * |lFluxToEnergyConstant C₀| * K ^ 2) * A ^ 2) := le_max_right _ _
  have hnn : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) * l2NormSq θ₀ := mul_nonneg he hL
  refine hbound.trans (hfin.trans ?_)
  calc (2 * |lFluxToEnergyConstant C₀| * K ^ 2) * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
        (A ^ 2 * l2NormSq θ₀)
      = ((2 * |lFluxToEnergyConstant C₀| * K ^ 2) * A ^ 2) *
          (epsilon β I.Λ (m - 1) ^ (2 * delta β) * l2NormSq θ₀) := by ring
    _ ≤ max Λ₀ ((2 * |lFluxToEnergyConstant C₀| * K ^ 2) * A ^ 2) *
          (epsilon β I.Λ (m - 1) ^ (2 * delta β) * l2NormSq θ₀) :=
        mul_le_mul_of_nonneg_right hcc hnn
    _ = _ := by ring

/-! ## `e.ergodic.break.up.last` -/

/-- Arithmetic of the integration-by-parts bound (source 8800–8830). -/
theorem ibp_final {τpp τp KJ X K κp S Q A sL e3 x e2 : ℝ} (hτpp : 0 ≤ τpp) (hτp : 0 < τp)
    (hKJ : 0 ≤ KJ) (hXK : X ≤ K * κp) (hκ : 0 < κp) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hQ : 0 ≤ Q) (hA : 0 < A) (hsL : 0 ≤ sL) (he3 : 0 ≤ e3)
    (hSb : Real.sqrt κp * S ≤ A * sL)
    (hQb : Q ≤ A * e3 * (Real.sqrt κp)⁻¹ * sL * τp⁻¹)
    (hrat : τpp / τp ≤ 9 * x) (hx : e3 * x = e2) :
    8 * (4 * τpp) * (2 * (KJ * X)) * S * Q ≤ 576 * KJ * K * A ^ 2 * e2 * sL ^ 2 := by
  have hr : 0 < Real.sqrt κp := Real.sqrt_pos.mpr hκ
  have hr2 : Real.sqrt κp * Real.sqrt κp = κp := Real.mul_self_sqrt hκ.le
  generalize Real.sqrt κp = r at *
  subst hr2
  subst hx
  have hS' : S ≤ A * sL * r⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hr]
    linarith only [hSb]
  have hSQ : S * Q ≤ (A * sL * r⁻¹) * (A * e3 * r⁻¹ * sL * τp⁻¹) :=
    mul_le_mul hS' hQb hQ (by positivity)
  have hT12 : 8 * (4 * τpp) * (2 * (KJ * X)) ≤ 8 * (4 * τpp) * (2 * (KJ * (K * (r * r)))) := by
    gcongr
  calc 8 * (4 * τpp) * (2 * (KJ * X)) * S * Q
      = (8 * (4 * τpp) * (2 * (KJ * X))) * (S * Q) := by ring
    _ ≤ (8 * (4 * τpp) * (2 * (KJ * (K * (r * r))))) *
          ((A * sL * r⁻¹) * (A * e3 * r⁻¹ * sL * τp⁻¹)) :=
        mul_le_mul hT12 hSQ (mul_nonneg hS hQ) (by positivity)
    _ = 64 * KJ * K * A ^ 2 * sL ^ 2 * e3 * (τpp / τp) := by
        field_simp
        ring
    _ ≤ 64 * KJ * K * A ^ 2 * sL ^ 2 * e3 * (9 * x) := by gcongr
    _ = _ := by ring

/-- Arithmetic of the `J → JHat` remainder (source 8700–8780). -/
theorem remainder_final {c0 c0' X K κp r e G L A : ℝ} {N : ℕ} (hc0 : 0 ≤ c0) (hcc : c0 ≤ c0')
    (hX0 : 0 ≤ X) (hXK : X ≤ K * κp) (hK : 0 ≤ K) (hκp : 0 ≤ κp) (hr0 : 0 ≤ r)
    (hrK : r ≤ K * e) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hN : 1 ≤ N) (hG : 0 ≤ G)
    (hκG : κp * G ≤ A ^ 2 * L) :
    4 * (c0 * X * r ^ N) * G ≤ (4 * c0' * K ^ (N + 1)) * e * (A ^ 2 * L) := by
  have hrN : r ^ N ≤ K ^ N * e :=
    (pow_le_pow_left₀ hr0 hrK N).trans (mul_pow_le_pow_mul_self hK he0 he1 hN)
  have hc0' : 0 ≤ c0' := hc0.trans hcc
  have h1 : c0 * X * r ^ N ≤ c0' * (K * κp) * (K ^ N * e) := by
    calc c0 * X * r ^ N ≤ c0' * X * r ^ N := by gcongr
      _ ≤ c0' * (K * κp) * (K ^ N * e) := by gcongr
  have h2 : 4 * (c0 * X * r ^ N) * G ≤ 4 * (c0' * (K * κp) * (K ^ N * e)) * G := by gcongr
  have h3 : 4 * (c0' * (K * κp) * (K ^ N * e)) * G =
      (4 * c0' * K ^ (N + 1)) * e * (κp * G) := by ring
  have h4 : (4 * c0' * K ^ (N + 1)) * e * (κp * G) ≤
      (4 * c0' * K ^ (N + 1)) * e * (A ^ 2 * L) := by gcongr
  exact h2.trans (h3 ▸ h4)

/-- `4⌈x⌉ + 1 ≤ 9x` for `x ≥ 1`. -/
theorem four_ceil_add_one_le_nine {x : ℝ} (hx : 1 ≤ x) : 4 * (⌈x⌉₊ : ℝ) + 1 ≤ 9 * x := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ x by linarith only [hx])
  linarith only [h, hx]

/-- `ε^{3δ} ε^{-δ} = ε^{2δ}`. -/
theorem rpow_three_mul_neg_eq {ε δ : ℝ} (hε : 0 < ε) :
    ε ^ (3 * δ) * ε ^ (-δ) = ε ^ (2 * δ) := by
  rw [← Real.rpow_add hε]
  congr 1
  ring

/-- e.ergodic.break.up.last (8640–8860). -/
theorem ergodic_break_up_last (β C₀ A P : ℝ) (hA : 0 < A) (hP : 0 ≤ P) :
    ∃ C : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
        Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T (Nstar β) t) x)) ≤
          A * Real.sqrt (l2NormSq θ₀) →
        Real.sqrt (spaceTimeGradNormSq (materialGrad (streamVel (Φ (m - 1))) (T (Nstar β)))) ≤
          A * epsilon β I.Λ (m - 1) ^ (3 * delta β) * (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
            Real.sqrt (l2NormSq θ₀) * (tauP β I.Λ m)⁻¹ →
        |(∫ t in (0 : ℝ)..1, gradQuad (T (Nstar β)) (I.flux (I.kappaSeq κ M m) m t) t) -
            ∫ t in (0 : ℝ)..1, gradQuad (T (Nstar β))
              (timeAvgMat fun s => I.flux (I.kappaSeq κ M m) m s) t| ≤
          C * epsilon β I.Λ (m - 1) ^ (2 * delta β) * l2NormSq θ₀ := by
  have _hAP := And.intro hA hP
  obtain ⟨K, hK1, hK⟩ := left_to_show_scales β C₀
  obtain ⟨Λ₀, hΛ₀⟩ := left_to_show_condition β C₀
  obtain ⟨KJ, hKJ0, hKJ⟩ := Jhat_sub_kappa_entry_abs_le β C₀
  set c0' : ℝ := 4 * Real.pi ^ 2 * |C₀| * Nstar β * 2 ^ Nstar β with hc0'
  set Cm : ℝ := (4 * c0' * K ^ (Nstar β + 1)) * A ^ 2 + 576 * KJ * K * A ^ 2 with hCm
  refine ⟨max Λ₀ Cm, ?_⟩
  intro I hz hx hh hC Φ hΦ κ hκp M hM hperm m hm hmM θ₀ θprev T hTit hT0 hDt
  have hΛ0 : Λ₀ ≤ (I.Λ : ℝ) := le_trans (le_max_left _ _) hC
  have hΛ : 2 ^ 7 ≤ I.Λ := I.two_pow_seven_le
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hκm, hmono, -, hs1, hs2, -, -⟩ := hK I hz hx hh κ hκp M hM hperm m hm hmM
  have hcond := hΛ₀ I hz hx hh hΛ0 κ hκp M hM hperm m hm hmM
  obtain ⟨hTsm, hTper, -, -⟩ := tIterates_classicalSol hTit
  have hκpp : 0 < I.kappaSeq κ M (m - 1) := lt_of_lt_of_le hκm hmono
  have hN1 : 1 ≤ Nstar β := by
    have h := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt hΛ
  have hεp : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt hΛ
  have hεp1 : epsilon β I.Λ (m - 1) ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt hΛ
  have hδ := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hτ := I.tau_pos' m
  have hτp : 0 < tauP β I.Λ m := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt hΛ
  have hτpp : 0 < tauPP β I.Λ m := Infra.Cutoff.tauPP_pos I.one_lt_beta I.beta_lt hΛ
  have hX0 : 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaSeq κ M m := by positivity
  have hR0 : 0 ≤ epsilon β I.Λ m ^ 2 / (I.kappaSeq κ M m * tau β I.Λ m) := by positivity
  have he : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) := Real.rpow_nonneg hεp.le _
  have he1 : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 :=
    Real.rpow_le_one hεp.le hεp1 (by positivity)
  have he3 : 0 ≤ epsilon β I.Λ (m - 1) ^ (3 * delta β) := Real.rpow_nonneg hεp.le _
  have hG : 0 ≤ spaceTimeGradNormSq (fun t x => spaceGrad (T (Nstar β) t) x) :=
    spaceTimeGradNormSq_nonneg' _
  have hL : 0 ≤ l2NormSq θ₀ := l2NormSq_nonneg' θ₀
  have hκG := mul_le_sq_of_sqrt_mul_le hκpp.le hG hT0 hL
  -- `ε_m² / (κ_m τ_m) ≤ 1`
  have hratio1 : epsilon β I.Λ m ^ 2 / (I.kappaSeq κ M m * tau β I.Λ m) ≤ 1 := by
    rw [div_le_one (mul_pos hκm hτ)]
    linarith only [hcond, mul_pos hκm hτ]
  -- the J → JHat replacement
  have hbreak := TJT_break I hm1 hκm hTsm
  have hg : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T (Nstar β) p.1) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    (spaceGrad_continuousOn hTsm).mono (Set.prod_mono Set.Icc_subset_Ici_self subset_rfl)
  rw [← spaceTimeGradNormSq_eq_intervalIntegral hg] at hbreak
  have hCz0 : 0 ≤ I.Czeta := by linarith only [I.one_le_Czeta]
  have hc0 : 0 ≤ 4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β := by positivity
  have hcc : 4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β ≤ c0' := by
    have : I.Czeta ≤ |C₀| := hz.trans (le_abs_self C₀)
    rw [hc0']
    gcongr
  have hrem := remainder_final (N := Nstar β) hc0 hcc hX0 hs1 (by linarith only [hK1])
    hκpp.le hR0 hs2 he he1 hN1 hG hκG
  -- integration by parts in time for `JHat`
  obtain ⟨N, -, hNP⟩ := four_tauPP_reciprocal_nat I.one_lt_beta I.beta_lt hΛ hm1
  have hB0 := hKJ I hz hx hh m hm1 (I.kappaSeq κ M m) hκm hratio1
  have hB := fun t i j => Jhat_sub_timeAvg_entry_abs_le I hm1 hκm hB0 t i j
  have hibp := third_term_ibp (Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m))
    (fun t x => Infra.Construction.streamVel_spatialDivergence_eq_zero (hΦ.adm_pred m) t x)
    hTsm hTper (I.Jhat (I.kappaSeq κ M m) m) (Jhat_entry_continuous_pub I hm1 hκm)
    (P := 4 * tauPP β I.Λ m) (by linarith only [hτpp]) hNP (Jhat_entry_periodic I hm1 _) hB
  have hx1 : 1 ≤ epsilon β I.Λ (m - 1) ^ (-delta β) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hεp hεp1 (by linarith only [hδ])
  have hrat : tauPP β I.Λ m / tauP β I.Λ m ≤ 9 * epsilon β I.Λ (m - 1) ^ (-delta β) := by
    rw [tauPP_div_tauP_eq I.one_lt_beta I.beta_lt hΛ]
    exact four_ceil_add_one_le_nine hx1
  have hfin := ibp_final (KJ := KJ) hτpp.le hτp hKJ0 hs1 hκpp (by linarith only [hK1])
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hA (Real.sqrt_nonneg _) he3 hT0 hDt hrat
    (rpow_three_mul_neg_eq hεp)
  rw [Real.sq_sqrt hL] at hfin
  have hsum : |(∫ t in (0 : ℝ)..1, gradQuad (T (Nstar β)) (I.flux (I.kappaSeq κ M m) m t) t) -
        ∫ t in (0 : ℝ)..1, gradQuad (T (Nstar β))
          (timeAvgMat fun s => I.flux (I.kappaSeq κ M m) m s) t| ≤
      Cm * (epsilon β I.Λ (m - 1) ^ (2 * delta β) * l2NormSq θ₀) := by
    refine hbreak.trans ?_
    have h1 := add_le_add (hibp.trans hfin) hrem
    refine h1.trans (le_of_eq ?_)
    rw [hCm]
    ring
  have hnn : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) * l2NormSq θ₀ := mul_nonneg he hL
  refine hsum.trans ?_
  calc Cm * (epsilon β I.Λ (m - 1) ^ (2 * delta β) * l2NormSq θ₀)
      ≤ max Λ₀ Cm * (epsilon β I.Λ (m - 1) ^ (2 * delta β) * l2NormSq θ₀) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hnn
    _ = _ := by ring

end AVenhance.Infra.Section5.LeftToShow

end
