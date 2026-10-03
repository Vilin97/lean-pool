/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.SeparatedChainsContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.NoSelectionInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.Separation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelection.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelection.Steps
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelection.TailSup
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelection.FlipFacts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelection.LevelSep
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelection.ChainData
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelection.LimitData
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters

/-! # Separation persists for the two vanishing-viscosity families

`separatedChains_of_inputs`: `SeparatedChainsContract β C₀` conditional on the statements
`VelGradContract β C₀` and `CosineDatumContract`.

For a cosine mode `n` with `L_n = 1/(2πn)` in the window `[ε_m^{1+γ/2}, c₁ ε_m^{1+γ/2-δ/2}]`:
level `m` of the two chains topped at `½ ε_M^p`, `2 ε_M^p` is separated by `≳ ε_m^δ ‖θ₀‖`
(flip-flop + short-time separation at `t = c′ ε_m^{2-β}`); the telescoped step-down increments to
    level
`M = 2j+1` cost `≲ ε_m^δ ‖θ₀‖`, and the top tail `θ − θ_M` is `o(1)` as `j → ∞`. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem NoSel.kappaSeq_top {β : ℝ} (I : Ingredients β) (κ : ℝ) (M : ℕ) :
    I.kappaSeq κ M M = κ := by
  simp [Ingredients.kappaSeq, Ingredients.kappaAt]

private theorem separatedChains_of_inputs_branch1 :
  ∀ (β C₀ : ℝ), CosineDatumContract → (1 : ℝ) < β → β < (4 / 3 : ℝ) → (2 : ℝ) * β / (q β + (1 :
    ℝ)) = β - gamma β → ∀ (c₀ : ℝ), NoSel.SepWith c₀ → ∀ (Cb : ℝ), (0 : ℝ) ≤ Cb → (∀ (I :
    Ingredients β), I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → ∀ (Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ),
    IsStreamSeq I Φ → ∀ (m : ℕ), (1 : ℕ) ≤ m → ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ), ∀ (x : Vec (2 :
    ℕ)) (i j : Fin (2 : ℕ)), |spaceGrad (fun (y : Vec (2 : ℕ)) => streamVel (Φ m) t y i) x j| ≤
    Cb * epsilon β I.Λ m ^ (β - (2 : ℝ))) → ∀ (C₈ Λc Λ₁ ρ Cff : ℝ), (0 : ℝ) < ρ → (0 : ℝ) ≤ Cff
    → (∀ (I : Ingredients β), I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → Λ₁ ≤ ↑I.Λ → ∀ (M : ℕ),
    (2 : ℕ) ≤ M → ∀ (m : ℕ), (1 : ℕ) ≤ m → m ≤ M - (1 : ℕ) → Cff * epsilon β I.Λ m ^ ρ ≤
    Real.log (5 / 4 : ℝ) / (2 : ℝ) → (0 : ℝ) < I.kappaSeq ((1 / 2 : ℝ) * epsilon β I.Λ M ^ ((2 :
    ℝ) * β / (q β + (1 : ℝ)))) M m → (0 : ℝ) < I.kappaSeq ((2 : ℝ) * epsilon β I.Λ M ^ ((2 : ℝ)
    * β / (q β + (1 : ℝ)))) M m → (NoSel.ffk0 * epsilon β I.Λ m ^ (β + gamma β) ≤ I.kappaSeq ((1
    / 2 : ℝ) * epsilon β I.Λ M ^ ((2 : ℝ) * β / (q β + (1 : ℝ)))) M m ∧ I.kappaSeq ((1 / 2 : ℝ)
    * epsilon β I.Λ M ^ ((2 : ℝ) * β / (q β + (1 : ℝ)))) M m ≤ NoSel.ffK0 * epsilon β I.Λ m ^ (β
    + gamma β)) ∧ (NoSel.ffk0 * epsilon β I.Λ m ^ (β + gamma β) ≤ I.kappaSeq ((2 : ℝ) * epsilon
    β I.Λ M ^ ((2 : ℝ) * β / (q β + (1 : ℝ)))) M m ∧ I.kappaSeq ((2 : ℝ) * epsilon β I.Λ M ^ ((2
    : ℝ) * β / (q β + (1 : ℝ)))) M m ≤ NoSel.ffK0 * epsilon β I.Λ m ^ (β + gamma β)) ∧ ((3 : ℝ)
    * I.kappaSeq ((1 / 2 : ℝ) * epsilon β I.Λ M ^ ((2 : ℝ) * β / (q β + (1 : ℝ)))) M m ≤
    I.kappaSeq ((2 : ℝ) * epsilon β I.Λ M ^ ((2 : ℝ) * β / (q β + (1 : ℝ)))) M m ∧ I.kappaSeq
    ((2 : ℝ) * epsilon β I.Λ M ^ ((2 : ℝ) * β / (q β + (1 : ℝ)))) M m ≤ (5 : ℝ) * I.kappaSeq ((1
    / 2 : ℝ) * epsilon β I.Λ M ^ ((2 : ℝ) * β / (q β + (1 : ℝ)))) M m ∨ (3 : ℝ) * I.kappaSeq ((2
    : ℝ) * epsilon β I.Λ M ^ ((2 : ℝ) * β / (q β + (1 : ℝ)))) M m ≤ I.kappaSeq ((1 / 2 : ℝ) *
    epsilon β I.Λ M ^ ((2 : ℝ) * β / (q β + (1 : ℝ)))) M m ∧ I.kappaSeq ((1 / 2 : ℝ) * epsilon β
    I.Λ M ^ ((2 : ℝ) * β / (q β + (1 : ℝ)))) M m ≤ (5 : ℝ) * I.kappaSeq ((2 : ℝ) * epsilon β I.Λ
    M ^ ((2 : ℝ) * β / (q β + (1 : ℝ)))) M m)) → ∀ (Ct : ℝ), (1 : ℝ) ≤ Ct → (0 : ℝ) < NoSel.ffk0
    → (0 : ℝ) < NoSel.ffK0 →
  let Q : ℝ := max NoSel.ffK0 Cb + (1 : ℝ);
  let c' : ℝ := min (1 : ℝ) (c₀ / Q);
  (0 : ℝ) < c' → c' ≤ (1 : ℝ) → Cb * c' ≤ c₀ → NoSel.ffK0 * c' ≤ c₀ →
  let c₂ : ℝ := NoSel.ffk0 * c' / (2 : ℝ);
  c₂ = NoSel.ffk0 * c' / (2 : ℝ) →
  let Cp : ℝ := (2 : ℝ) * C₈;
  (∀ (I : Ingredients β), I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → Λc ≤ ↑I.Λ → ∀ (Φ : ℕ → ℝ →
    Vec (2 : ℕ) → ℝ), IsStreamSeq I Φ → ∀ (κ : ℝ) (M : ℕ), κ ∈ permittedInterval β I.Λ M → ∀ (m₀
    : ℕ), (2 : ℕ) ≤ m₀ → m₀ < M → ∀ (R : ℝ), (0 : ℝ) < R → ∀ (θ₀ : Vec (2 : ℕ) → ℝ), ContDiff ℝ
    (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ → MeanZeroOn unitCube θ₀ → IsThetaAnalytic R θ₀ → mTheta0 β
    I.Λ R ≤ m₀ + (1 : ℕ) → (∀ (j : ℕ), m₀ ≤ j → j ≤ M → (0 : ℝ) < I.kappaSeq κ M j) ∧ ∃ (θs : ℕ
    → ℝ → Vec (2 : ℕ) → ℝ), (∀ (j : ℕ), m₀ ≤ j → j ≤ M → IsClassicalSol (streamVel (Φ j))
    (I.kappaSeq κ M j) (fun (_ : ℝ) (_ : Vec (2 : ℕ)) => (0 : ℝ)) θ₀ (θs j)) ∧ ∀ t ∈ Set.Icc
    (0 : ℝ) (1 : ℝ), √(l2NormSq fun (x : Vec (2 : ℕ)) => θs M t x - θs m₀ t x) ≤ Cp * epsilon β
    I.Λ m₀ ^ delta β * √(l2NormSq θ₀)) → Cp = (2 : ℝ) * C₈ →
  let c₁ : ℝ := √(c₂ / ((3 : ℝ) + (2 : ℝ) * Cp));
  (0 : ℝ) < c₁ → c₂ / c₁ ^ (2 : ℕ) = (3 : ℝ) + (2 : ℝ) * Cp →
  let s : ℝ := (1 : ℝ) + gamma β / (2 : ℝ);
  s = (1 : ℝ) + gamma β / (2 : ℝ) → ∀ (Λ_a : ℝ), (∀ (x : ℝ), Λ_a ≤ x → Cff * x⁻¹ ^ ρ ≤ Real.log
    (5 / 4 : ℝ) / (2 : ℝ)) → ∀ (I : Ingredients β), I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → ∀
    (Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ), IsStreamSeq I Φ → ∀ (φ : ℝ → Vec (2 : ℕ) → ℝ), Λc ≤ ↑I.Λ → Λ₁
    ≤ ↑I.Λ → Λ_a ≤ ↑I.Λ → (2 : ℕ) ^ (7 : ℕ) ≤ I.Λ → (∀ (k : ℕ), (0 : ℝ) < epsilon β I.Λ k) → (∀
    (k : ℕ), (1 : ℕ) ≤ k → epsilon β I.Λ k ≤ (↑I.Λ)⁻¹) → ∀ (Bφ : ℝ), (∀ (M : ℕ) (t : ℝ) (x : Vec
    (2 : ℕ)), |φ t x - Φ M t x| ≤ Ct * epsilon β I.Λ (M + (1 : ℕ)) ^ β) → AEStronglyMeasurable
    (fun (p : ℝ × Vec (2 : ℕ)) => φ p.1 p.2) (volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ) ×ˢ
    Set.univ)) → (∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ), IsZ2Periodic (φ t)) → (∀ t ∈ Set.Icc (0 : ℝ) (1
    : ℝ), Differentiable ℝ (φ t)) → AEStronglyMeasurable (fun (p : ℝ × Vec (2 : ℕ)) => streamVel
    φ p.1 p.2) (volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ) ×ˢ Set.univ)) → (∀ t ∈ Set.Icc (0 : ℝ)
    (1 : ℝ), IsZ2Periodic (streamVel φ t)) → IsDivFree (streamVel φ) → (∀ t ∈ Set.Icc (0 : ℝ) (1
    : ℝ), ∀ (x : Vec (2 : ℕ)), ‖streamVel φ t x‖ ≤ Bφ) → ∀ n ∈ {n : ℕ | (1 : ℕ) ≤ n ∧ ∃ (m : ℕ),
    (2 : ℕ) ≤ m ∧ epsilon β I.Λ m ^ s ≤ (1 : ℝ) / ((2 : ℝ) * Real.pi * ↑n) ∧ (1 : ℝ) / ((2 : ℝ)
    * Real.pi * ↑n) ≤ c₁ * epsilon β I.Λ m ^ (s - delta β / (2 : ℝ))}, (1 : ℕ) ≤ n ∧ ∃ t ∈
    Set.Icc (0 : ℝ) (1 : ℝ), ∃ (σ : ℝ), (0 : ℝ) < σ ∧ ∃ (J : ℕ), ∀ (c : ℝ), c ≠ (0 : ℝ) → ∀ (j :
    ℕ), J ≤ j → ∀ (θa θb : ℝ → Vec (2 : ℕ) → ℝ), IsWeakSolution (streamVel φ) (epsilon β I.Λ ((2
    : ℕ) * j + (1 : ℕ)) ^ ((2 : ℝ) * β / (q β + (1 : ℝ))) / (2 : ℝ)) (fun (x : Vec (2 : ℕ)) => c
    * Real.cos ((2 : ℝ) * Real.pi * ↑n * x (0 : Fin (2 : ℕ)))) θa → IsWeakSolution (streamVel φ)
    ((2 : ℝ) * epsilon β I.Λ ((2 : ℕ) * j + (1 : ℕ)) ^ ((2 : ℝ) * β / (q β + (1 : ℝ)))) (fun (x
    : Vec (2 : ℕ)) => c * Real.cos ((2 : ℝ) * Real.pi * ↑n * x (0 : Fin (2 : ℕ)))) θb → σ * |c|
    ≤ |√(l2NormSq (θa t)) - √(l2NormSq (θb t))|
    := by
  intro β C₀ hC hβ1 hβ2 hp c₀ hS Cb hCb hVel C₈ Λc Λ₁ ρ Cff hρ hCff hKF Ct hCt1 hk0 hK0 Q c' hc'0
      hc'1 hCbc hKc c₂ hc₂def Cp hChain hCpdef c₁ hc₁ hc₂c₁ s hsdef Λ_a hΛa I hz hx hh Φ hΦ φ hΛc'
      hΛ₁' hΛa' hΛ7 hεpos hεle Bφ htail hφm hφp hφd hbm hbp hdiv hbb
  rintro n ⟨hn1, m, hm2, hlo, hup⟩
  refine ⟨hn1, ?_⟩
  set E := epsilon β I.Λ m with hEdef
  have hE : 0 < E := hεpos m
  have hE1 : E ≤ 1 := Infra.Construction.epsilon_le_one hβ1 hβ2 hΛ7
  have hEΛ : E ≤ (I.Λ : ℝ)⁻¹ := hεle m (by omega)
  have hEδ : 0 < E ^ delta β := Real.rpow_pos_of_pos hE _
  obtain ⟨J₀, hJ₀⟩ := NoSel.epsilon_rpow_eventually hβ1 hβ2 hΛ7
    (2 * Ct * (1 + Infra.Ingredients.supergeoConstant β) ^ β) (tailExp_pos hβ1 hβ2) hEδ
  have hEp : 0 < E ^ (2 - β) := Real.rpow_pos_of_pos hE _
  have hEp1 : E ^ (2 - β) ≤ 1 := Real.rpow_le_one hE.le hE1 (by linarith)
  have ht0 : 0 < c' * E ^ (2 - β) := mul_pos hc'0 hEp
  have ht1 : c' * E ^ (2 - β) ≤ 1 := by
    calc c' * E ^ (2 - β) ≤ 1 * 1 := mul_le_mul hc'1 hEp1 hEp.le zero_le_one
      _ = 1 := one_mul 1
  refine ⟨c' * E ^ (2 - β), ⟨ht0.le, ht1⟩, E ^ delta β / Real.sqrt 2, by positivity,
    max m J₀, ?_⟩
  intro c hc j hj θa θb hθa hθb
  have hmj : m ≤ j := (le_max_left _ _).trans hj
  have hJj : J₀ ≤ j := (le_max_right _ _).trans hj
  set M := 2 * j + 1 with hMdef
  have hMJ : J₀ ≤ M := by omega
  have hmM : m < M := by omega
  have hM2 : 2 ≤ M := by omega
  have hmM' : m ≤ M - 1 := by omega
  have htmem : c' * E ^ (2 - β) ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0.le, ht1⟩
  -- the datum
  obtain ⟨hθ₀, hper, hmean, hl2, -, hG, hH, han⟩ := hC n hn1 c
  set θ₀ : Vec 2 → ℝ := fun x => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0) with hθ₀def
  set lam : ℝ := 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 with hlamdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hLpos : 0 < 1 / (2 * Real.pi * (n : ℝ)) := by positivity
  have hlamL : lam * (1 / (2 * Real.pi * (n : ℝ))) ^ 2 = 1 := by
    rw [hlamdef]; field_simp; norm_num
  have hlam0 : 0 ≤ lam := by positivity
  obtain ⟨hl1, hl2'⟩ := NoSel.scale_algebra (E := E) (L := 1 / (2 * Real.pi * (n : ℝ)))
    (lam := lam) (c₁ := c₁) (s := s) (d := delta β / 2) hE hLpos hlamL hlo hup
  have e2s : 2 * s = 2 + gamma β := by rw [hsdef]; ring
  have e2d : 2 * (delta β / 2) = delta β := by ring
  rw [e2s] at hl1 hl2'
  rw [e2d] at hl2'
  -- mTheta0
  have hmT : mTheta0 β I.Λ (1 / (2 * Real.pi * (n : ℝ))) ≤ m + 1 := by
    refine (mTheta0_isLeast hβ1 hβ2 hΛ7 hLpos).2 ⟨by omega, ?_⟩
    simpa [hsdef] using hlo
  -- the two chains
  have hεp0 : 0 ≤ epsilon β I.Λ M ^ (2 * β / (q β + 1)) := Real.rpow_nonneg (hεpos M).le _
  have hκM1 : (1 / 2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) ∈ permittedInterval β I.Λ M :=
    ⟨le_rfl, by linarith⟩
  have hκM2 : (2 * epsilon β I.Λ M ^ (2 * β / (q β + 1))) ∈ permittedInterval β I.Λ M :=
    ⟨by linarith, le_rfl⟩
  obtain ⟨hpos1, θ1, hθ1, htel1⟩ := hChain I hz hx hh hΛc' Φ hΦ _ M hκM1 m hm2 hmM _ hLpos
    θ₀ hθ₀ hper hmean han hmT
  obtain ⟨hpos2, θ2, hθ2, htel2⟩ := hChain I hz hx hh hΛc' Φ hΦ _ M hκM2 m hm2 hmM _ hLpos
    θ₀ hθ₀ hper hmean han hmT
  -- level `m`
  have hsmall : Cff * epsilon β I.Λ m ^ ρ ≤ Real.log (5 / 4) / 2 :=
    (NoSel.mul_rpow_le_inv hCff hE.le hEΛ hρ.le).trans (hΛa _ hΛa')
  obtain ⟨⟨k1lo, k1hi⟩, ⟨k2lo, k2hi⟩, hratio⟩ := hKF I hz hx hh hΛ₁' M hM2 m (by omega) hmM'
    hsmall (hpos1 m le_rfl hmM.le) (hpos2 m le_rfl hmM.le)
  have hLu := hVel I hz hx hh Φ hΦ m (by omega)
  have hadm := streamSeq_isAdmissible hΦ m
  have hN : Real.sqrt (l2NormSq θ₀) = |c| / Real.sqrt 2 := by
    rw [hl2, Real.sqrt_div (sq_nonneg c), Real.sqrt_sq_eq_abs]
  set N := Real.sqrt (l2NormSq θ₀) with hNdef
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hsep : NoSel.ffk0 * c' / 2 * (E ^ delta β / c₁ ^ 2) * N ≤
      |Real.sqrt (l2NormSq (θ1 m (c' * E ^ (2 - β)))) -
        Real.sqrt (l2NormSq (θ2 m (c' * E ^ (2 - β))))| := by
    rcases hratio with ⟨h3, h5⟩ | ⟨h3, h5⟩
    · have := NoSel.level_sep hS hadm hCb hLu hθ₀ hper hlam0 hG hH hE hE1 (by linarith) hc₁ hc'0
        hc'1 hCbc hKc hK0.le hk0.le k1lo (hpos1 m le_rfl hmM.le) k2hi h3 h5 hl1 hl2'
        (hθ1 m le_rfl hmM.le) (hθ2 m le_rfl hmM.le)
      exact this.trans (le_abs_self _)
    · have := NoSel.level_sep hS hadm hCb hLu hθ₀ hper hlam0 hG hH hE hE1 (by linarith) hc₁ hc'0
        hc'1 hCbc hKc hK0.le hk0.le k2lo (hpos2 m le_rfl hmM.le) k1hi h3 h5 hl1 hl2'
        (hθ2 m le_rfl hmM.le) (hθ1 m le_rfl hmM.le)
      exact (this.trans (le_abs_self _)).trans (abs_sub_comm _ _).le
  -- continuity / `L²` membership
  have hmem1 : ∀ k, m ≤ k → k ≤ M →
      MemL2On unitCube (θ1 k (c' * E ^ (2 - β))) := fun k h1 h2 =>
    Infra.Section5.Integration.memL2On_unitCube_of_continuous
      (IsClassicalSol.continuous_slice (hθ1 k h1 h2) ht0.le)
  have hmem2 : ∀ k, m ≤ k → k ≤ M →
      MemL2On unitCube (θ2 k (c' * E ^ (2 - β))) := fun k h1 h2 =>
    Infra.Section5.Integration.memL2On_unitCube_of_continuous
      (IsClassicalSol.continuous_slice (hθ2 k h1 h2) ht0.le)
  -- increments
  have hinc1 := (NoSel.abs_sqrt_l2_sub_le (hmem1 M hmM.le le_rfl) (hmem1 m le_rfl hmM.le)).trans
    (htel1 _ htmem)
  have hinc2 := (NoSel.abs_sqrt_l2_sub_le (hmem2 M hmM.le le_rfl) (hmem2 m le_rfl hmM.le)).trans
    (htel2 _ htmem)
  -- tails
  have hθa' : IsWeakSolution (streamVel φ) (1 / 2 * epsilon β I.Λ M ^ (2 * β / (q β + 1)))
      θ₀ θa := by
    have e : epsilon β I.Λ M ^ (2 * β / (q β + 1)) / 2 =
        1 / 2 * epsilon β I.Λ M ^ (2 * β / (q β + 1)) := by ring
    rw [e] at hθa
    exact hθa
  have hθM1 := hθ1 M hmM.le le_rfl
  have hθM2 := hθ2 M hmM.le le_rfl
  rw [NoSel.kappaSeq_top] at hθM1 hθM2
  have hκlo1 : (1 / 2) * epsilon β I.Λ M ^ (β - gamma β) ≤
      1 / 2 * epsilon β I.Λ M ^ (2 * β / (q β + 1)) := by rw [hp]
  have hκlo2 : (1 / 2) * epsilon β I.Λ M ^ (β - gamma β) ≤
      2 * epsilon β I.Λ M ^ (2 * β / (q β + 1)) := by rw [hp]; rw [hp] at hεp0; linarith
  have htailA := NoSel.tail_sup (by linarith : 0 ≤ Ct) hΦ htail hφm hφp hφd hbm hbp hdiv hbb
    (by omega : 1 ≤ M) hκlo1 hθ₀ hper hθa' hθM1 _ htmem
  have htailB := NoSel.tail_sup (by linarith : 0 ≤ Ct) hΦ htail hφm hφp hφd hbm hbp hdiv hbb
    (by omega : 1 ≤ M) hκlo2 hθ₀ hper hθb hθM2 _ htmem
  have hKt := hJ₀ M hMJ
  have hmemA : MemL2On unitCube (θa (c' * E ^ (2 - β))) := by
    obtain ⟨Dθ, hDθ⟩ := hθa'
    exact (hDθ.1 _ htmem).2
  have hmemB : MemL2On unitCube (θb (c' * E ^ (2 - β))) := by
    obtain ⟨Dθ, hDθ⟩ := hθb
    exact (hDθ.1 _ htmem).2
  have hτA := (NoSel.abs_sqrt_l2_sub_le hmemA (hmem1 M hmM.le le_rfl)).trans
    (htailA.trans (mul_le_mul_of_nonneg_right hKt hN0))
  have hτB := (NoSel.abs_sqrt_l2_sub_le hmemB (hmem2 M hmM.le le_rfl)).trans
    (htailB.trans (mul_le_mul_of_nonneg_right hKt hN0))
  have hfin := NoSel.final_ineq hτA hτB hinc1 hinc2 hsep
  have hGeq : NoSel.ffk0 * c' / 2 * (E ^ delta β / c₁ ^ 2) * N = (3 + 2 * Cp) * (E ^ delta β *
      N) := by
    rw [← hc₂c₁, hc₂def]; ring
  have hσ : E ^ delta β / Real.sqrt 2 * |c| = E ^ delta β * N := by
    rw [hN]; ring
  rw [hσ]
  rw [hGeq] at hfin
  rw [hCpdef] at hfin
  linarith

theorem separatedChains_of_inputs (β C₀ : ℝ) (hV : VelGradContract β C₀)
    (hC : CosineDatumContract) : SeparatedChainsContract β C₀ := by
  by_cases hβr : 1 < β ∧ β < 4 / 3
  swap
  · exact ⟨0, fun I => absurd ⟨I.one_lt_beta, I.beta_lt⟩ hβr⟩
  obtain ⟨hβ1, hβ2⟩ := hβr
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ1 hβ2
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ1 hβ2
  have hδγ := Infra.Ingredients.four_delta_le_gamma hβ1 hβ2
  have hp : 2 * β / (q β + 1) = β - gamma β := two_beta_div_eq hβ1 hβ2
  obtain ⟨c₀, hc₀, hS⟩ := NoSel.sepWith_of_contract Contracts.separation_contract
  obtain ⟨Cb, hCb, hVel⟩ := hV
  obtain ⟨C₈, Λc, hC₈0, hChain⟩ := NoSel.chain_data β C₀
  obtain ⟨Λ₁, ρ, Cff, hρ, hCff, hKF⟩ := NoSel.kappa_facts β C₀
  obtain ⟨Ct, hCt1, hLim⟩ := NoSel.limit_data β
  -- constants
  have hk0 := NoSel.ffk0_pos
  have hK0 := NoSel.ffK0_pos
  set Q := max NoSel.ffK0 Cb + 1 with hQdef
  have hQ0 : 0 < Q := by
    have : 0 ≤ max NoSel.ffK0 Cb := (hK0.le).trans (le_max_left _ _)
    linarith
  set c' := min 1 (c₀ / Q) with hc'def
  have hc'0 : 0 < c' := lt_min one_pos (div_pos hc₀ hQ0)
  have hc'1 : c' ≤ 1 := min_le_left _ _
  have hc'2 : c' ≤ c₀ / Q := min_le_right _ _
  have hCbc : Cb * c' ≤ c₀ := by
    calc Cb * c' ≤ Q * (c₀ / Q) := by
          refine mul_le_mul (by linarith [le_max_right NoSel.ffK0 Cb]) hc'2 hc'0.le hQ0.le
      _ = c₀ := by field_simp
  have hKc : NoSel.ffK0 * c' ≤ c₀ := by
    calc NoSel.ffK0 * c' ≤ Q * (c₀ / Q) := by
          refine mul_le_mul (by linarith [le_max_left NoSel.ffK0 Cb]) hc'2 hc'0.le hQ0.le
      _ = c₀ := by field_simp
  set c₂ := NoSel.ffk0 * c' / 2 with hc₂def
  have hc₂ : 0 < c₂ := by positivity
  set Cp := 2 * C₈ with hCpdef
  have hCp : 0 ≤ Cp := by positivity
  set c₁ := Real.sqrt (c₂ / (3 + 2 * Cp)) with hc₁def
  have hc₁ : 0 < c₁ := Real.sqrt_pos.2 (by positivity)
  have hc₁sq : c₁ ^ 2 = c₂ / (3 + 2 * Cp) := Real.sq_sqrt (by positivity)
  have hc₂c₁ : c₂ / c₁ ^ 2 = 3 + 2 * Cp := by
    rw [hc₁sq]; field_simp
  set s := 1 + gamma β / 2 with hsdef
  have he1 : 0 < s - delta β / 2 := by rw [hsdef]; linarith
  have hlog5 : 0 < Real.log (5 / 4) / 2 := by
    have := Real.log_pos (show (1 : ℝ) < 5 / 4 by norm_num)
    linarith
  obtain ⟨Λ_a, hΛa⟩ := NoSel.exists_big Cff (Real.log (5 / 4) / 2) ρ hρ hlog5
  obtain ⟨Λ_b, hΛb⟩ := NoSel.exists_big 2 c₁ (delta β / 2) (by positivity) hc₁
  obtain ⟨Λ_c, hΛc⟩ := NoSel.exists_big (2 * Real.pi * c₁) (1 / 2) (s - delta β / 2) he1
    (by norm_num)
  refine ⟨max (max (max Λc Λ₁) (max Λ_a Λ_b)) Λ_c, ?_⟩
  intro I hz hx hh hΛ Φ hΦ φ htend
  have hΛc' : Λc ≤ (I.Λ : ℝ) :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hΛ
  have hΛ₁' : Λ₁ ≤ (I.Λ : ℝ) :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hΛ
  have hΛa' : Λ_a ≤ (I.Λ : ℝ) :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hΛ
  have hΛb' : Λ_b ≤ (I.Λ : ℝ) :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hΛ
  have hΛc'' : Λ_c ≤ (I.Λ : ℝ) := (le_max_right _ _).trans hΛ
  have hΛ7 := I.two_pow_seven_le
  have hεpos : ∀ k, 0 < epsilon β I.Λ k := fun k => Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hεle : ∀ k, 1 ≤ k → epsilon β I.Λ k ≤ (I.Λ : ℝ)⁻¹ := by
    intro k hk
    have := epsilon_rpow_le_inv hβ1 hβ2 hΛ7 hk (s := 1) le_rfl
    simpa using this
  obtain ⟨Bφ, htail, hφm, hφp, hφd, hbm, hbp, hdiv, hbb⟩ := hLim I Φ hΦ φ htend
  -- window facts for an arbitrary level
  have hwin2 : ∀ m : ℕ, 1 ≤ m → 2 * epsilon β I.Λ m ^ (delta β / 2) ≤ c₁ := by
    intro m hm
    have h := NoSel.mul_rpow_le_inv (C := 2) (by norm_num) (hεpos m).le (hεle m hm)
      (by linarith : 0 ≤ delta β / 2)
    exact h.trans (hΛb _ hΛb')
  have hwinX : ∀ m : ℕ, 1 ≤ m →
      2 * Real.pi * (c₁ * epsilon β I.Λ m ^ (s - delta β / 2)) ≤ 1 / 2 := by
    intro m hm
    have h := NoSel.mul_rpow_le_inv (C := 2 * Real.pi * c₁) (by positivity) (hεpos m).le
      (hεle m hm) he1.le
    have := h.trans (hΛc _ hΛc'')
    calc 2 * Real.pi * (c₁ * epsilon β I.Λ m ^ (s - delta β / 2))
        = 2 * Real.pi * c₁ * epsilon β I.Λ m ^ (s - delta β / 2) := by ring
      _ ≤ 1 / 2 := this
  refine ⟨{n : ℕ | 1 ≤ n ∧ ∃ m : ℕ, 2 ≤ m ∧ epsilon β I.Λ m ^ s ≤ 1 / (2 * Real.pi * n) ∧
      1 / (2 * Real.pi * n) ≤ c₁ * epsilon β I.Λ m ^ (s - delta β / 2)}, ?_, ?_⟩
  · -- unbounded
    intro N
    have hX : 0 < 1 / (2 * Real.pi * ((N : ℝ) + 1)) := by positivity
    obtain ⟨m, hm2, hsm⟩ := NoSel.epsilon_exists_small hβ1 hβ2 hΛ7 c₁ he1 hX 2
    obtain ⟨n, hn1, hlo, hup, hge⟩ := NoSel.exists_mode hc₁ (hεpos m) (hwin2 m (by omega))
      (hwinX m (by omega))
    refine ⟨n, ⟨hn1, m, hm2, hlo, hup⟩, ?_⟩
    have hX0 : 0 < c₁ * epsilon β I.Λ m ^ (s - delta β / 2) :=
      mul_pos hc₁ (Real.rpow_pos_of_pos (hεpos m) _)
    have h1 : (N : ℝ) + 1 ≤ 1 / (2 * Real.pi * (c₁ * epsilon β I.Λ m ^ (s - delta β / 2))) := by
      rw [le_div_iff₀ (by positivity)]
      rw [lt_div_iff₀ (by positivity)] at hsm
      nlinarith
    have : (N : ℝ) ≤ n := by linarith
    exact_mod_cast this
  · exact @separatedChains_of_inputs_branch1 β C₀ hC hβ1 hβ2 hp c₀ hS Cb hCb hVel C₈ Λc Λ₁ ρ Cff
      hρ hCff hKF Ct hCt1 hk0 hK0 hc'0 hc'1 hCbc hKc hc₂def hChain hCpdef hc₁ hc₂c₁ hsdef Λ_a hΛa
      I hz hx hh Φ hΦ φ hΛc' hΛ₁' hΛa' hΛ7 hεpos hεle Bφ htail hφm hφp hφd hbm hbp hdiv hbb
end AVenhance.Infra.FullTheorem
