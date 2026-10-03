/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TemperatureError
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTSourceScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusivityComparison
public import Mathlib.Analysis.Matrix.Normed

/-! Exact contract adapter for the abstract-amplitude temperature error leaf. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory

namespace AVenhance.Infra.Section5.Contracts

open AVenhance.Infra.Section5.Integration
open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5.RelativeError

/-- Equip the spatial matrix space with its coordinate supremum norm. -/
local instance avInfraSection5ContractsTemperatureErrorNormedAddCommGroup1 : NormedAddCommGroup
    (Matrix (Fin 2) (Fin 2) ℝ) :=
  Matrix.normedAddCommGroup
/-- Real normed-space structure for spatial matrices with the coordinate supremum norm. -/
local instance avInfraSection5ContractsTemperatureErrorNormedSpace2 : NormedSpace ℝ (Matrix (Fin
    2) (Fin 2) ℝ) :=
  Matrix.normedSpace

/-- The abstract-V estimate, with its `TemperatureErrorContract` conclusion.
The base profile is the `ThetaProfileContract` at amplitude
`S = √κprev · √spaceTimeGradNormSq(∇θprev)`; the flow and coefficient inputs retain the
precise hypotheses of the underlying open-time estimate. -/
theorem temperatureError_contract {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {κ : ℝ} {M m : ℕ} (hκ : κ ∈ permittedInterval β I.Λ M)
    (hm : 2 ≤ m) (hmM : m ≤ M)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1))
      (fun _ _ => 0) θ₀ θprev)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t))
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {c Ck K Cflow Cmean Rflow Cθ Rθ C₀ Ct : ℝ}
    (hc : 0 < c) (hCk : 0 ≤ Ck) (hK : 0 ≤ K) (hCf : 0 ≤ Cflow)
    (hCm : 0 ≤ Cmean) (hRf : 256 ≤ Rflow) (hRθ : 0 < Rθ)
    (hlower : c * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^
      (2 + gamma β)) ≤ I.kappaSeq κ M (m - 1))
    (hupper : I.kappaSeq κ M (m - 1) ≤ Ck * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^
      (2 + gamma β)))
    (hC₀ : iterateSourceConstant
      (iterateBudgetUniversalConstant K Ck c ((2 : ℝ) ^ (-25 : ℤ)) Cflow Cmean)
      Rflow Cθ ≤ C₀)
    (hsmall : C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
      max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * Rθ ^ (-2 : ℤ)) ≤ 1)
    (hKm : ∀ t j k, |I.Kmat (I.kappaSeq κ M m) m t j k| ≤ K * I.kappaSeq κ M (m - 1))
    (hmean : ∀ j k, |(timeAvgMat (I.Kmat (I.kappaSeq κ M m) m) - I.kappaSeq κ M (m - 1) •
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
        I.kappaSeq κ M (m - 1) * Cmean * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hzero : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ j k,
      |(I.flowGrad hΦ m l t x - 1) j k| ≤
        Cflow * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hpositive : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ p : List (Fin 2),
      1 ≤ p.length → ∀ j k,
      |iterateSpatialWord p (fun y => (I.flowGrad hΦ m l t y - 1) j k) x| ≤
        Cflow * (p.length.factorial : ℝ) *
          (Rflow / epsilon β I.Λ (m - 1)) ^ p.length)
    (hLater : epsilon β I.Λ (m - 1) ^
      (1 + gamma β / 2 - delta β) ≤ Rθ)
    (hbase : iterateCoordinateEnergyProfile θprev (I.kappaSeq κ M (m - 1))
      (Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq
        (fun s x => spaceGrad (θprev s) x)))
      (max (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (C₀ / Rθ)) 0)
    (hCt : (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ) * C₀ ^ 3 ≤ Ct) :
    TemperatureErrorContract I m (I.kappaSeq κ M (m - 1)) θprev T Ct
      (Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq
        (fun s x => spaceGrad (θprev s) x))) := by
  have heM : 0 < epsilon β I.Λ M :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hκpos : 0 < κ :=
    lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (Real.rpow_pos_of_pos heM _)) (Set.mem_Icc.mp hκ).1
  have hκm : 0 < I.kappaSeq κ M m := LeftToShow.kappaSeq_pos I hκpos M m
  have hκscale := iterate_kappaSeq_abs_le_previous I hκpos (by omega) hmM
  change Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq (fun s x =>
    spaceGrad (T (Nstar β) s) x - spaceGrad (θprev s) x)) ≤ _
  exact AVenhance.Infra.Section5.RelativeError.temperatureError_leaf_of_abstract_V
    I hΦ hT hθ hm hκm hflow hflowp hA3
    hc hCk hK hCf hCm hRf hRθ hlower hupper hC₀ hsmall hKm hmean hzero hpositive
    hκscale hLater hbase hCt

/-- The zeroth-word slice of the V-increment estimate telescopes to the exact
temperature-error contract. The scale bounds make the source and analytic
maxima equal to one and bound the error amplitude by the requested `S`. -/
theorem TemperatureError.temperatureError_of_VIncrement {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} {Cs R S : ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hCs : 1 ≤ Cs) (hS : 0 ≤ S) (hR : 0 < R)
    (hradius : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ R)
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * Cs ^ 3)⁻¹)
    (hV : VIncrementContract I m κprev T Cs R S) :
    TemperatureErrorContract I m κprev θprev T
      ((Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ) * Cs ^ 3) S := by
  let e := epsilon β I.Λ (m - 1)
  let η := Cs ^ 3 * e ^ (2 * delta β) *
    max 1 (e ^ (2 + gamma β) * R ^ (-2 : ℤ))
  have he : 0 < e := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hscale := iterate_T_source_scale he hR hCs hradius hsmall
  have hη0 : 0 ≤ η := by dsimp [η, e]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η, e]
    rw [hscale.1]
    have hηquarter := hscale.2.2
    linarith
  have hVzero : ∀ i, 1 ≤ i → i ≤ Nstar β →
      Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
        (fun s x => spaceGrad (iterateIncrement T i s) x)) ≤
        S * iterateAmplitude η i * ((2 * i).factorial : ℝ) := by
    intro i hi hNi
    have h := hV i hi hNi [] [] (by simp) 0 (by norm_num) (by norm_num)
    have hfirst : 0 ≤ Real.sqrt (l2NormSq (iterateIncrement T i 0)) := Real.sqrt_nonneg _
    have h' : Real.sqrt (l2NormSq (iterateIncrement T i 0)) +
        Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
          (fun s x => spaceGrad (iterateIncrement T i s) x)) ≤
        S * iterateAmplitude η i * ((2 * i).factorial : ℝ) := by
      simpa [iterateSpatialWord, iterateAnalyticWeight, η, e] using h
    linarith
  have hTemperature := temperature_error_of_V_zero_bounds I hΦ hT hθ
    (N := S) (η := η) hS hη0 hη1 hVzero
  change Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq (fun s x =>
      spaceGrad (T (Nstar β) s) x - spaceGrad (θprev s) x)) ≤ _
  calc
    _ ≤ (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ) * η * S := hTemperature
    _ = (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ) *
        Cs ^ 3 * e ^ (2 * delta β) * S := by
      dsimp [η, e]
      rw [hscale.1]
      ring

/-- Uniform temperature-error producer from the S-amplitude theta profile and
V-increment contracts. `CsReq`, the returned error coefficient, and the scale
threshold are all fixed before the ingredient instance. The profile is retained
as the common input shape for the theta-profile producers; the telescoping
estimate itself uses its companion V-increment bound. -/
theorem temperatureError_of_thetaProfile_contract (β Ccut CsReq : ℝ)
    (hReq : 1 ≤ CsReq) :
    ∃ Cs Ct C₁ : ℝ, CsReq ≤ Cs ∧ 0 ≤ Ct ∧
      OnA8Instances β Ccut C₁
        (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T =>
          ∀ S : ℝ, 0 ≤ S →
            ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs S →
            VIncrementContract I m (I.kappaSeq κ M (m - 1)) T Cs R S →
            TemperatureErrorContract I m (I.kappaSeq κ M (m - 1)) θprev T Ct S) := by
  let Cs := CsReq
  let Ct := (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ) * Cs ^ 3
  obtain ⟨C₁, hscale⟩ := iterate_contract_scales β Cs hReq
  refine ⟨Cs, Ct, C₁, le_rfl, ?_, ?_⟩
  · dsimp [Ct, Cs]
    positivity
  · intro I hCz hCx hChat hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hθ₀ hperiod hmean hana
      m hm hmM θm θprev T hθm hθprev hT S hS hbase hV
    obtain ⟨_hm2, hradius, hsmall⟩ := hscale I hΛ R hR m hm
    exact TemperatureError.temperatureError_of_VIncrement I hΦ hT hθprev hReq hS hR hradius hsmall
        hV

end AVenhance.Infra.Section5.Contracts
