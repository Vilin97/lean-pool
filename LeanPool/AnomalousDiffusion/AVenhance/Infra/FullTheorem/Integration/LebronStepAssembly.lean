/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.Statements
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.LemmaUContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.Interpolation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.KappaBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.VelocityBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.Pieces
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IndyStepDown
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.ClassicalWellposed
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0IsLeast
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesExist
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyClassical
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergySmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitFieldBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVelContinuous

/-! # Lemma r.LeBron (`lebron_step`), conditional on Lemma U

`lebron_step_of_lemmaU : LemmaUContract → LebronStepStatement β C₀`.

* sup part: the step-down estimate (`indystepdown`), conjunct (i), with the iterate witness from
  `RelativeError.exists_TIterates` (classical solvability, `AVenhance.classical_wellposed`);
* Hölder-`1/4` part: Lemma U for `θ_m` and `θ_{m-1}` with the uniform drift bound
  `velBound β` and the diffusivity window of `kappaSeq_window`;
* interpolation `interpolate_holder` with `μ = δ/(8δ+4P)`, `P = q(β+γ)`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem lebron_step_of_lemmaU (hU : LemmaUContract) (β C₀ : ℝ) :
    LebronStepStatement β C₀ := by
  by_cases hβr : 1 < β ∧ β < 4 / 3
  swap
  · refine ⟨1, 0, one_pos, fun I => ?_⟩
    exact absurd ⟨I.one_lt_beta, I.beta_lt⟩ hβr
  obtain ⟨hβ1, hβ2⟩ := hβr
  obtain ⟨CU, hCU, hUc⟩ := hU
  obtain ⟨C₈, hA8⟩ := AVenhance.indystepdown β C₀
  obtain ⟨c₁, Λ₁, hc₁, hκw⟩ := kappaSeq_window β C₀
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ1 hβ2
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ1 hβ2
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ1 hβ2
  have hP : 0 ≤ lebronP β := by unfold lebronP; positivity
  have hBv : 0 ≤ velBound β := velBound_nonneg hβ1
  set μ := lebronMu (delta β) (lebronP β) with hμ
  set C₈' := max C₈ 0 with hC₈'
  set S₀ := 2 * CU * (1 + velBound β) * (1 / Real.sqrt c₁) with hS₀
  have hS₀0 : 0 ≤ S₀ := by positivity
  set K := (2 * C₈') ^ (1 - 4 * μ) * S₀ ^ (4 * μ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨μ, max (max C₈ Λ₁) (C₈' + K), lebronMu_pos hδ hP, ?_⟩
  intro I hz hx hh hCΛ Φ hΦ κ hκ M hM hκM R hR θ₀ hθ₀ hper hmean han m hm1 hmM θm θprev
    hθm hθprev
  have hΛ7 := I.two_pow_seven_le
  have hC₈Λ : C₈ ≤ (I.Λ : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hCΛ
  have hΛ₁ : Λ₁ ≤ (I.Λ : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hCΛ
  have hKΛ : C₈' + K ≤ (I.Λ : ℝ) := (le_max_right _ _).trans hCΛ
  -- `m ≥ 2`
  have hm2 : 2 ≤ m := by
    have := (mTheta0_isLeast hβ1 hβ2 hΛ7 hR).1.1
    omega
  -- scales
  set E := epsilon β I.Λ (m - 1) with hE
  have hEpos : 0 < E := Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hE1 : E ≤ 1 := Infra.Construction.epsilon_le_one hβ1 hβ2 hΛ7
  -- diffusivity window
  obtain ⟨hκp1, hκp2⟩ := hκw I hz hx hh hΛ₁ κ hκ M hM hκM m hm2 hmM (m - 1) (Or.inl rfl)
  obtain ⟨hκm1, hκm2⟩ := hκw I hz hx hh hΛ₁ κ hκ M hM hκM m hm2 hmM m (Or.inr rfl)
  have hκppos : 0 < I.kappaSeq κ M (m - 1) := lt_of_lt_of_le (by positivity) hκp1
  have hκmpos : 0 < I.kappaSeq κ M m := lt_of_lt_of_le (by positivity) hκm1
  -- the data norms
  set N := Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)) with hN
  have hmc : MeasurableSet unitCube := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hgn : 0 ≤ gradNormSq (spaceGrad θ₀) :=
    setIntegral_nonneg hmc fun x _ => vecNormSq_nonneg _
  have hl2 : 0 ≤ l2NormSq θ₀ := setIntegral_nonneg hmc fun x _ => sq_nonneg _
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hn0N : Real.sqrt (l2NormSq θ₀) ≤ N := Real.sqrt_le_sqrt (by linarith)
  -- sup part: step-down estimate (i)
  have hsolv : ∀ j : ℕ, Infra.Section5.RelativeError.ClassicalSolvable (streamVel (Φ j)) := by
    intro j ν hν g hg hgp F hF hFp
    exact (AVenhance.classical_wellposed (Φ j) (streamSeq_isAdmissible hΦ j)
      ν hν F hF hFp g hg hgp).imp fun θ hθ => hθ.1
  obtain ⟨T, hT⟩ := Infra.Section5.RelativeError.exists_TIterates I hΦ (m := m) (by omega) hκmpos
      hκppos
    (hsolv (m - 1)) hθ₀ hper hθprev
  have hsup8 := (hA8 I hz hx hh hC₈Λ Φ hΦ κ hκ M hM hκM R hR θ₀ hθ₀ hper hmean han m hm1 hmM
    θm θprev T hθm hθprev hT).1
  have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) ≤ C₈' * E ^ delta β * N := by
    intro t ht
    have h1 := hsup8 t ht
    have h2 : 0 ≤ Real.sqrt (I.kappaSeq κ M m) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θm s) x -
          spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h3 : Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) ≤
        C₈ * E ^ delta β * Real.sqrt (l2NormSq θ₀) := by linarith
    have hEd : 0 ≤ E ^ delta β := Real.rpow_nonneg hEpos.le _
    calc _ ≤ C₈ * E ^ delta β * Real.sqrt (l2NormSq θ₀) := h3
      _ ≤ C₈' * E ^ delta β * Real.sqrt (l2NormSq θ₀) := by
          gcongr; exact le_max_left _ _
      _ ≤ C₈' * E ^ delta β * N := by gcongr
  -- Hölder part: Lemma U
  have hweak : ∀ (j : ℕ) (κj : ℝ), 0 < κj → κj ≤ 1 →
      ∀ θ : ℝ → Vec 2 → ℝ, IsClassicalSol (streamVel (Φ j)) κj (fun _ _ => 0) θ₀ θ →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (l2NormSq (fun x => θ t x - θ s x)) ≤
          CU * (1 + velBound β) / Real.sqrt κj * |t - s| ^ ((1 : ℝ) / 4) * N := by
    intro j κj hκj0 hκj1 θ hθ s hs t ht
    have hadm := streamSeq_isAdmissible hΦ j
    have hcont := hadm.vel_continuous
    have hweakθ := Infra.Section5.RelativeError.classical_isWeakSolutionGrad hcont hθ
    refine hUc (streamVel (Φ j)) (hcont.aestronglyMeasurable)
      (fun t _ => streamVel_isZ2Periodic hadm t) (isDivFree_streamVel hadm) (velBound β) hBv
      (fun t _ x => streamVel_norm_le hΦ j t x) κj hκj0 hκj1 θ₀ (fun x => spaceGrad θ₀ x)
      (Infra.Section5.RelativeError.isPeriodicH1With_of_contDiff
        (hθ₀.of_le (by exact_mod_cast le_top)) hper) θ (fun t x => spaceGrad (θ t) x)
      hweakθ s hs t ht
  have hSm : ∀ j : ℕ, ∀ κj : ℝ, c₁ * E ^ lebronP β ≤ κj →
      CU * (1 + velBound β) / Real.sqrt κj ≤ S₀ / 2 * E ^ (-(lebronP β / 2)) := by
    intro j κj hκj
    have h := one_div_sqrt_le hc₁ hEpos hκj
    calc CU * (1 + velBound β) / Real.sqrt κj
        = CU * (1 + velBound β) * (1 / Real.sqrt κj) := by ring
      _ ≤ CU * (1 + velBound β) * ((1 / Real.sqrt c₁) * E ^ (-(lebronP β / 2))) := by
          gcongr
      _ = S₀ / 2 * E ^ (-(lebronP β / 2)) := by rw [hS₀]; ring
  have hcm : ∀ t ∈ Set.Icc (0 : ℝ) 1, Continuous (θm t) := fun t ht =>
    IsClassicalSol.continuous_slice hθm ht.1
  have hcp : ∀ t ∈ Set.Icc (0 : ℝ) 1, Continuous (θprev t) := fun t ht =>
    IsClassicalSol.continuous_slice hθprev ht.1
  have hEP : 0 ≤ E ^ (-(lebronP β / 2)) := Real.rpow_nonneg hEpos.le _
  have hmU := hweak m _ hκmpos hκm2 θm hθm
  have hpU := hweak (m - 1) _ hκppos hκp2 θprev hθprev
  have hmb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θm t x - θm s x)) ≤
        (S₀ / 2 * E ^ (-(lebronP β / 2)) * N) * |t - s| ^ ((1 : ℝ) / 4) := by
    intro s hs t ht
    refine (hmU s hs t ht).trans ?_
    have := hSm m _ hκm1
    have hh : 0 ≤ |t - s| ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (abs_nonneg _) _
    calc _ = CU * (1 + velBound β) / Real.sqrt (I.kappaSeq κ M m) * N *
          |t - s| ^ ((1 : ℝ) / 4) := by ring
      _ ≤ _ := by gcongr
  have hpb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θprev t x - θprev s x)) ≤
        (S₀ / 2 * E ^ (-(lebronP β / 2)) * N) * |t - s| ^ ((1 : ℝ) / 4) := by
    intro s hs t ht
    refine (hpU s hs t ht).trans ?_
    have := hSm (m - 1) _ hκp1
    have hh : 0 ≤ |t - s| ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (abs_nonneg _) _
    calc _ = CU * (1 + velBound β) / Real.sqrt (I.kappaSeq κ M (m - 1)) * N *
          |t - s| ^ ((1 : ℝ) / 4) := by ring
      _ ≤ _ := by gcongr
  -- assemble
  have hmain : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => (θm t x - θprev t x) - (θm s x - θprev s x))) ≤
        K * E ^ (delta β / 2) * N * |t - s| ^ μ := by
    intro s hs t ht
    obtain ⟨h1, h2⟩ := difference_bounds hcm hcp hsup hmb hpb hs ht
    have h2' : Real.sqrt (l2NormSq (fun x => (θm t x - θprev t x) - (θm s x - θprev s x))) ≤
        S₀ * E ^ (-(lebronP β / 2)) * N * |t - s| ^ ((1 : ℝ) / 4) := by
      refine h2.trans (le_of_eq ?_)
      ring
    exact holder_step hEpos hδ hP (le_max_right _ _) hS₀0 hN0 (abs_nonneg _)
      (Real.sqrt_nonneg _) (by simpa using h1) h2'
  refine ⟨fun t ht => Infra.Section5.Integration.memL2On_unitCube_of_continuous
    ((hcm t ht).sub (hcp t ht)), C₈' * E ^ delta β * N, K * E ^ (delta β / 2) * N, ?_, hsup,
    fun s hs t ht => hmain s hs t ht⟩
  -- `A + B ≤ H`
  have hEd : E ^ delta β ≤ E ^ (delta β / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hEpos hE1 (by linarith)
  have hEh : 0 ≤ E ^ (delta β / 2) := Real.rpow_nonneg hEpos.le _
  have hC₈'0 : 0 ≤ C₈' := le_max_right _ _
  calc C₈' * E ^ delta β * N + K * E ^ (delta β / 2) * N
      ≤ C₈' * E ^ (delta β / 2) * N + K * E ^ (delta β / 2) * N := by gcongr
    _ = (C₈' + K) * E ^ (delta β / 2) * N := by ring
    _ ≤ (max (max C₈ Λ₁) (C₈' + K)) * E ^ (delta β / 2) * N := by
        gcongr; exact le_max_right _ _

end AVenhance.Infra.FullTheorem
