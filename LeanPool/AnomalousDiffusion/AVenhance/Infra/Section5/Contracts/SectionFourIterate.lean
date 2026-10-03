/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TLemmasMinusTheta
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVAbstractAmplitude
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTDischarge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFlowGeometry
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFlowClose
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFlowBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaProfileDischarge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaAnalyticData
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MStar
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LaterStart

/-! # Producer for the exact step-down part (i) SectionFourIterate contract -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5.Integration

private theorem sectionFourIterate_contract_bound1 :
  ∀ (β C₀ c Ck : ℝ), (0 : ℝ) < c → c < Ck →
  let Ctheta : ℝ := max (1 : ℝ) ((4 : ℝ) * max (thetaAnalyticRadiusBase c) (2 : ℝ));
  let Cflow : ℝ := (40 : ℝ);
  let Rflow : ℝ := (2 : ℝ) ^ (10 : ℕ);
  let K : ℝ := iterateKmatConstant β C₀;
  let P : ℝ := iterateRatioConstant β Ck;
  let Cmean : ℝ := iterateMeanScaleConstant β C₀ P;
  let Csource : ℝ := max (1 : ℝ) (iterateReducedSourceConstant β C₀ c Ck Cflow Rflow Ctheta);
  let p : ℝ := (2 : ℝ) * delta β;
  let Ct : ℝ := (8 : ℝ) * (↑((2 : ℕ) * Nstar β).factorial : ℝ) * Csource ^ (3 : ℕ);
  ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ) (hΦ : IsStreamSeq I Φ) (κ : ℝ) (M : ℕ) (R
    : ℝ), (0 : ℝ) < R → ∀ (θ₀ : Vec (2 : ℕ) → ℝ), IsThetaAnalytic R θ₀ → ∀ m ≤ M, ∀ (θprev : ℝ →
    Vec (2 : ℕ) → ℝ) (T : ℕ → ℝ → Vec (2 : ℕ) → ℝ), I.IsTIterates hΦ m (I.kappaSeq κ M m)
    (I.kappaSeq κ M (m - (1 : ℕ))) θ₀ θprev T → (2 : ℕ) ≤ m → (0 : ℝ) < κ → ((∀ (m : ℕ), (1 : ℕ)
    ≤ m → m < M → c * (AVenhance.a β I.Λ m * epsilon β I.Λ m ^ ((2 : ℝ) + gamma β)) ≤ I.kappaAt
    κ m (M - m) ∧ I.kappaAt κ m (M - m) ≤ Ck * (AVenhance.a β I.Λ m * epsilon β I.Λ m ^ ((2 : ℝ)
    + gamma β))) ∧ ∀ (m : ℕ), (2 : ℕ) ≤ m → m < M → c * epsilon β I.Λ (m - (1 : ℕ)) ^ ((4 : ℝ) *
    delta β) ≤ epsilon β I.Λ m ^ (2 : ℕ) / (I.kappaAt κ m (M - m) * tau β I.Λ m) ∧ epsilon β I.Λ
    m ^ (2 : ℕ) / (I.kappaAt κ m (M - m) * tau β I.Λ m) ≤ Ck * epsilon β I.Λ (m - (1 : ℕ)) ^ ((4
    : ℝ) * delta β)) → (∀ (j : ℕ), (1 : ℕ) ≤ j → ∀ (t : ℝ) (n : ℕ), (2 : ℕ) ≤ n → barNorm n ((2
    : ℝ) ^ (8 : ℕ) * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤ ENNReal.ofReal ((2 : ℝ) ^ (5 : ℕ) *
    AVenhance.a β I.Λ j * epsilon β I.Λ j ^ (2 : ℕ) * (((↑n : ℝ) + (2 : ℝ)) ^ (2 : ℕ) / ((↑n :
    ℝ) + (1 : ℝ)) ^ (3 : ℕ)))) → (0 : ℝ) < epsilon β I.Λ (m - (1 : ℕ)) → epsilon β I.Λ (m - (1 :
    ℕ)) ≤ (1 : ℝ) → (0 : ℝ) < delta β → epsilon β I.Λ (m - (1 : ℕ)) ^ ((2 : ℝ) + gamma β) ≤ (1 :
    ℝ) → Csource ^ (3 : ℕ) * epsilon β I.Λ (m - (1 : ℕ)) ^ p * max (1 : ℝ) (epsilon β I.Λ (m -
    (1 : ℕ)) ^ ((2 : ℝ) + gamma β) * (1 : ℝ) ^ (-2 : ℤ)) ≤ (1 : ℝ) → iterateSourceConstant
    (iterateBudgetUniversalConstant K Ck c ((2 : ℝ) ^ (-25 : ℤ)) Cflow Cmean) Rflow Ctheta ≤
    Csource → (8 : ℝ) * max (thetaAnalyticRadiusBase c) (2 : ℝ) ≤ Csource → epsilon β I.Λ (m -
    (1 : ℕ)) ^ ((1 : ℝ) + gamma β / (2 : ℝ)) ≤ R → (0 : ℝ) < I.kappaSeq κ M m → (0 : ℝ) ≤ K → (0
    : ℝ) ≤ Cmean → (0 : ℝ) ≤ Cflow → (256 : ℝ) ≤ Rflow → c * (a β I.Λ (m - (1 : ℕ)) * epsilon β
    I.Λ (m - (1 : ℕ)) ^ ((2 : ℝ) + gamma β)) ≤ I.kappaSeq κ M (m - (1 : ℕ)) → I.kappaSeq κ M (m
    - (1 : ℕ)) ≤ Ck * (a β I.Λ (m - (1 : ℕ)) * epsilon β I.Λ (m - (1 : ℕ)) ^ ((2 : ℝ) + gamma
    β)) → (∀ (t : ℝ) (j k : Fin (2 : ℕ)), |I.Kmat (I.kappaSeq κ M m) m t j k| ≤ K * I.kappaSeq κ
    M (m - (1 : ℕ))) → (∀ (j k : Fin (2 : ℕ)), |(timeAvgMat (I.Kmat (I.kappaSeq κ M m) m) -
    I.kappaSeq κ M (m - (1 : ℕ)) • (1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ)) j k| ≤ I.kappaSeq
    κ M (m - (1 : ℕ)) * Cmean * epsilon β I.Λ (m - (1 : ℕ)) ^ p) → (∀ (l : ℤ), ContDiff ℝ (↑(⊤ :
    ℕ∞) : WithTop ℕ∞) fun (z : AmnrSpace) => I.flowGrad hΦ m l z.1 z.2) → (∀ (t : ℝ), (0 : ℝ) <
    t → ∀ (l : ℤ), IsZ2Periodic (I.flowGrad hΦ m l t)) → (∀ (t : ℝ) (x : Vec (2 : ℕ)) (l : ℤ),
    I.hatXiML m l t ≠ (0 : ℝ) → ∀ (j k : Fin (2 : ℕ)), |(I.flowGrad hΦ m l t x - (1 : Matrix
    (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ)) j k| ≤ Cflow * epsilon β I.Λ (m - (1 : ℕ)) ^ p) → (∀ (t : ℝ)
    (x : Vec (2 : ℕ)) (l : ℤ), I.hatXiML m l t ≠ (0 : ℝ) → ∀ (w : List (Fin (2 : ℕ))), (1 : ℕ) ≤
    w.length → ∀ (j k : Fin (2 : ℕ)), |iterateSpatialWord w (fun (y : Vec (2 : ℕ)) =>
    (I.flowGrad hΦ m l t y - (1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ)) j k) x| ≤ Cflow *
    (↑w.length.factorial : ℝ) * (Rflow / epsilon β I.Λ (m - (1 : ℕ))) ^ w.length) →
    (IsAdmissibleStream fun (t : ℝ) => Φ (m - (1 : ℕ)) t) → IsClassicalSol (streamVel (Φ (m - (1
    : ℕ)))) (I.kappaSeq κ M (m - (1 : ℕ))) (fun (_ : ℝ) (_ : Vec (2 : ℕ)) => (0 : ℝ)) θ₀ θprev
    → (0 : ℝ) ≤ √(l2NormSq θ₀) → √(l2NormSq θ₀) ^ (2 : ℕ) = l2NormSq θ₀ → Csource / (1 : ℝ) ≤
    Csource * epsilon β I.Λ (m - (1 : ℕ)) ^ ((-1 : ℝ) - gamma β / (2 : ℝ)) →
  let Target : ℝ := Ct * epsilon β I.Λ (m - (1 : ℕ)) ^ delta β * √(l2NormSq θ₀);
  let F : ℝ := (↑((2 : ℕ) * Nstar β).factorial : ℝ) * ((4 : ℝ) * Csource ^ (3 : ℕ) * epsilon β
    I.Λ (m - (1 : ℕ)) ^ p);
  (0 : ℝ) ≤ Csource ^ (3 : ℕ) * epsilon β I.Λ (m - (1 : ℕ)) ^ p → Csource ^ (3 : ℕ) * epsilon β
    I.Λ (m - (1 : ℕ)) ^ p ≤ (1 / 4 : ℝ) → (∀ (r : ℝ), (0 : ℝ) ≤ r → ContDiff ℝ (↑(⊤ : ℕ∞) :
    WithTop ℕ∞) (θprev r)) → ∀ (q : ℝ), (0 : ℝ) < q → ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ), √(l2NormSq
    fun (x : Vec (2 : ℕ)) => T (Nstar β) t x - θprev t x) ≤ Target + F * q
    := by
  intro β C₀ c Ck hc hcC Ctheta Cflow Rflow K P Cmean Csource p Ct I Φ hΦ κ M R hR θ₀ hanalytic m
      hmM θprev T hT hm2 hκpos hA5 hA3 hE hE1 hδ hpowE hsmallV hsourceBound hRadius hRscale hκm
      hKnonneg hCmeannonneg hCflow hRflowBound hlower hupper hKm hMean hflow hflowp hzero
      hpositive hφ hthetaSol hrootnonneg hrootSq hLmax Target F heta hetaSmall hThetaSpatialSmooth
      q hq t ht
  let Amp := 2 * Real.sqrt (l2NormSq θ₀) + q
  have hAmpPos : 0 < Amp := by dsimp [Amp]; linarith [hrootnonneg]
  have hAmpRoot : Real.sqrt (l2NormSq θ₀) ≤ Amp := by
    dsimp [Amp]
    linarith
  have hInitial : l2NormSq θ₀ ≤ Amp ^ 2 := by
    rw [← hrootSq]
    exact (sq_le_sq₀ hrootnonneg (le_of_lt hAmpPos)).2 hAmpRoot
  have hzeroEnergy := theta_homogeneous_gradient_energy_le_of_initial_l2_sq
    hφ hthetaSol hInitial
  have htrace : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in unitCube, (classicalWordDerivative w θ₀ x) ^ 2) ≤
        Amp * ((w.length.factorial : ℝ) / R ^ w.length) := by
    intro w _
    have hword := theta_initial_word_l2_le_of_analytic hanalytic hthetaSol w
    have hfactor : 0 ≤ ((w.length.factorial : ℝ) / R ^ w.length) := by positivity
    exact hword.trans (mul_le_mul_of_nonneg_right hAmpRoot hfactor)
  have hbase := theta_iterate_profile_of_initial_trace_A3_A5 I Φ hΦ hm2 hmM
    hc hcC hAmpPos hR hRadius hRscale
    hzeroEnergy htrace hA3 hA5.1 hthetaSol
  have hLmax' : Csource ≤ Csource * epsilon β I.Λ (m - 1) ^
      (-1 - gamma β / 2) := by simpa using hLmax
  have hmaxL : max (Csource * epsilon β I.Λ (m - 1) ^
      (-1 - gamma β / 2)) Csource =
      Csource * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2) :=
    max_eq_left hLmax'
  have hbase' : iterateCoordinateEnergyProfile θprev (I.kappaSeq κ M (m - 1)) Amp
      (max (Csource * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2))
        (Csource / 1)) 0 := by
    rw [show Csource / 1 = Csource by ring, hmaxL]
    exact hbase
  have hV := iterate_V_abstract_amplitude_of_diffusivity_and_flow
    (I := I) (hΦ := hΦ) (hT := hT) (hθ := hthetaSol) (hm := hm2) (hκm := hκm)
    hflow hflowp hA3 (N := Amp) hAmpPos hc (hc.trans hcC).le hKnonneg hCflow
    hCmeannonneg hRflowBound (by norm_num : (0 : ℝ) < 1) hlower hupper
    hsourceBound hsmallV hKm hMean hzero hpositive
    (iterate_kappaSeq_abs_le_previous I hκpos (by omega) hmM) hbase'
  have hVzero : ∀ i ∈ Finset.range (Nstar β), ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (iterateIncrement T (i + 1) s)) +
        Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq
          (fun r x => spaceGrad (iterateIncrement T (i + 1) r) x)) ≤
        (Nat.factorial (2 * (i + 1)) : ℝ) *
          iterateAmplitude (Csource ^ 3 * epsilon β I.Λ (m - 1) ^ p) (i + 1) * Amp := by
    intro i hi s hs
    have hiN : i + 1 ≤ Nstar β := by have := Finset.mem_range.mp hi; omega
    have hv := hV (i + 1) (by omega) hiN [] [] rfl s hs.1 hs.2
    calc
      _ ≤ Amp * iterateAmplitude (Csource ^ 3 * epsilon β I.Λ (m - 1) ^ p)
          (i + 1) * (Nat.factorial (2 * (i + 1)) : ℝ) := by
        simpa [iterateSpatialWord, iterateAnalyticWeight, p, hpowE] using hv
      _ = _ := by ring
  have hvalue := iterate_Tm_minus_theta_value_bound_of_V_zero I hΦ hT
    hThetaSpatialSmooth (le_of_lt hAmpPos)
    heta hetaSmall (by rfl) (by positivity)
    hVzero t ht
  have hvalue' :
      Real.sqrt (l2NormSq (fun x => T (Nstar β) t x - θprev t x)) ≤
        ((2 * Nstar β).factorial : ℝ) *
          (4 * Csource ^ 3 * epsilon β I.Λ (m - 1) ^ p) * Amp := by
    simpa [p] using hvalue
  have hcoeff :
      ((2 * Nstar β).factorial : ℝ) *
        (4 * Csource ^ 3 * epsilon β I.Λ (m - 1) ^ p) *
          (2 * Real.sqrt (l2NormSq θ₀)) ≤ Target := by
    have heδ : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤
        epsilon β I.Λ (m - 1) ^ delta β :=
      Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith [hδ])
    calc
      _ = (8 * ((2 * Nstar β).factorial : ℝ) * Csource ^ 3 *
          Real.sqrt (l2NormSq θ₀)) * epsilon β I.Λ (m - 1) ^ p := by
            dsimp [p]
            ring
      _ ≤ (8 * ((2 * Nstar β).factorial : ℝ) * Csource ^ 3 *
          Real.sqrt (l2NormSq θ₀)) * epsilon β I.Λ (m - 1) ^ delta β :=
        mul_le_mul_of_nonneg_left (by simpa [p] using heδ) (by positivity)
      _ = Target := by dsimp [Target, Ct]; ring
  have hsplit : ((2 * Nstar β).factorial : ℝ) *
      (4 * Csource ^ 3 * epsilon β I.Λ (m - 1) ^ p) * Amp =
      ((2 * Nstar β).factorial : ℝ) *
        (4 * Csource ^ 3 * epsilon β I.Λ (m - 1) ^ p) *
          (2 * Real.sqrt (l2NormSq θ₀)) + F * q := by
    dsimp [F, Amp]
    ring
  rw [hsplit] at hvalue'
  exact hvalue'.trans (add_le_add hcoeff le_rfl)

private theorem sectionFourIterate_contract_Ethreshold2 :
  ∀ (β C₀ c Ck : ℝ),
  let Ctheta : ℝ := max (1 : ℝ) ((4 : ℝ) * max (thetaAnalyticRadiusBase c) (2 : ℝ));
  let Cflow : ℝ := (40 : ℝ);
  let Rflow : ℝ := (2 : ℝ) ^ (10 : ℕ);
  let Csource : ℝ := max (1 : ℝ) (iterateReducedSourceConstant β C₀ c Ck Cflow Rflow Ctheta);
  let D : ℝ := (4 : ℝ) * Csource ^ (3 : ℕ);
  let p : ℝ := (2 : ℝ) * delta β;
  ∀ (I : Ingredients β) (m : ℕ), (1 : ℕ) ≤ m - (1 : ℕ) → (0 : ℝ) < (↑I.Λ : ℝ) → (1 : ℝ) ≤ (↑I.Λ
    : ℝ) * D⁻¹ ^ p⁻¹ → epsilon β I.Λ (m - (1 : ℕ)) ≤ D⁻¹ ^ p⁻¹
    := by
  intro β C₀ c Ck Ctheta Cflow Rflow Csource D p I m hmpos hthresholdPos hprod
  have hLambdaOne : (1 : ℝ) ≤ (I.Λ : ℝ) := by
    have hnat : 1 ≤ I.Λ := le_trans (by norm_num : (1 : ℕ) ≤ 2 ^ 7)
      I.two_pow_seven_le
    exact_mod_cast hnat
  have hmreal : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hmpos
  have hexp : -((m - 1 : ℕ) : ℝ) ≤ (-1 : ℝ) := by linarith
  have hdecay := Infra.Ingredients.epsilon_le_lambda_pow
    I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have hEInv : epsilon β I.Λ (m - 1) ≤ (I.Λ : ℝ)⁻¹ := by
    calc
      _ ≤ (I.Λ : ℝ) ^ (-((m - 1 : ℕ) : ℝ)) := hdecay
      _ ≤ (I.Λ : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hLambdaOne hexp
      _ = (I.Λ : ℝ)⁻¹ := Real.rpow_neg_one _
  have hInv' : 1 / (I.Λ : ℝ) ≤ (D⁻¹) ^ (p⁻¹) :=
    (div_le_iff₀ hthresholdPos).2 (by simpa [mul_comm] using hprod)
  have hInv : (I.Λ : ℝ)⁻¹ ≤ (D⁻¹) ^ (p⁻¹) := by simpa only [one_div] using hInv'
  exact hEInv.trans hInv

private theorem sectionFourIterate_contract_target3 :
  ∀ (β C₀ c Ck : ℝ),
  let Ctheta : ℝ := max (1 : ℝ) ((4 : ℝ) * max (thetaAnalyticRadiusBase c) (2 : ℝ));
  let Cflow : ℝ := (40 : ℝ);
  let Rflow : ℝ := (2 : ℝ) ^ (10 : ℕ);
  let Csource : ℝ := max (1 : ℝ) (iterateReducedSourceConstant β C₀ c Ck Cflow Rflow Ctheta);
  let p : ℝ := (2 : ℝ) * delta β;
  let Ct : ℝ := (8 : ℝ) * (↑((2 : ℕ) * Nstar β).factorial : ℝ) * Csource ^ (3 : ℕ);
  ∀ (I : Ingredients β) (θ₀ : Vec (2 : ℕ) → ℝ) (m : ℕ) (θprev : ℝ → Vec (2 : ℕ) → ℝ) (T : ℕ → ℝ
    → Vec (2 : ℕ) → ℝ), (0 : ℝ) < epsilon β I.Λ (m - (1 : ℕ)) →
  let Target : ℝ := Ct * epsilon β I.Λ (m - (1 : ℕ)) ^ delta β * √(l2NormSq θ₀);
  let F : ℝ := (↑((2 : ℕ) * Nstar β).factorial : ℝ) * ((4 : ℝ) * Csource ^ (3 : ℕ) * epsilon β
    I.Λ (m - (1 : ℕ)) ^ p);
  (0 : ℝ) < F → (∀ (q : ℝ), (0 : ℝ) < q → ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ), √(l2NormSq fun (x : Vec
    (2 : ℕ)) => T (Nstar β) t x - θprev t x) ≤ Target + F * q) → ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ),
    √(l2NormSq fun (x : Vec (2 : ℕ)) => T (Nstar β) t x - θprev t x) ≤ Target
    := by
  intro β C₀ c Ck Ctheta Cflow Rflow Csource p Ct I θ₀ m θprev T hE Target F hFpos hbound t ht
  by_contra hnot
  let X := Real.sqrt (l2NormSq (fun x => T (Nstar β) t x - θprev t x))
  have hgap : Target < X := lt_of_not_ge hnot
  let q := (X - Target) / (2 * F)
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos (sub_pos.mpr hgap) (by positivity)
  have hqbound := hbound q hq t ht
  have hmul : F * q = (X - Target) / 2 := by
    dsimp [q]
    field_simp [ne_of_gt hFpos]
  have hless : Target + F * q < X := by
    rw [hmul]
    linarith only [hgap]
  exact (not_lt_of_ge hqbound) hless

private theorem sectionFourIterate_contract_Mean4 :
  ∀ (β C₀ Ck : ℝ),
  let P : ℝ := iterateRatioConstant β Ck;
  let Cmean : ℝ := iterateMeanScaleConstant β C₀ P;
  let p : ℝ := (2 : ℝ) * delta β;
  ∀ (I : Ingredients β) (κ : ℝ) (M : ℕ) (_ : ℝ), ∀ m ≤ M, (2 : ℕ) ≤ m → (0 : ℝ) < I.kappaSeq κ M
    m → (∀ (t : ℝ) (j k : Fin (2 : ℕ)), |I.Kmat (I.kappaAt κ m (M - m)) m t j k| ≤
    iterateKmatConstant β C₀ * I.kappaAt κ (m - (1 : ℕ)) (M - (m - (1 : ℕ)))) ∧ epsilon β I.Λ m
    ^ (2 : ℕ) ≤ I.kappaAt κ m (M - m) * tau β I.Λ m / (2 : ℝ) ∧ iterateMeanErrorBound I
    (I.kappaAt κ m (M - m)) m ≤ I.kappaAt κ (m - (1 : ℕ)) (M - (m - (1 : ℕ))) *
    iterateMeanScaleConstant β C₀ (iterateRatioConstant β Ck) * epsilon β I.Λ (m - (1 : ℕ)) ^
    ((2 : ℝ) * delta β) → ∀ (j k : Fin (2 : ℕ)), |(timeAvgMat (I.Kmat (I.kappaSeq κ M m) m) -
    I.kappaSeq κ M (m - (1 : ℕ)) • (1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ)) j k| ≤ I.kappaSeq
    κ M (m - (1 : ℕ)) * Cmean * epsilon β I.Λ (m - (1 : ℕ)) ^ p
    := by
  intro β C₀ Ck P Cmean p I κ M R m hmM hm2 hκm hinputs j k
  have hentry := iterate_mean_coefficient_bound I κ (by omega : 1 ≤ m)
    hmM hκm hinputs.2.1
  have hentry' :
      |(timeAvgMat (I.Kmat (I.kappaSeq κ M m) m) -
        I.kappaSeq κ M (m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
      iterateMeanErrorBound I (I.kappaSeq κ M m) m := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ k).trans ((norm_le_pi_norm _ j).trans hentry)
  have hbound := hentry'.trans hinputs.2.2
  simpa [p, Cmean, Ingredients.kappaSeq] using hbound

private theorem sectionFourIterate_contract_conclusion5 :
  ∀ (β C₀ c Ck : ℝ), (0 : ℝ) < c → c < Ck →
  let Ctheta : ℝ := max (1 : ℝ) ((4 : ℝ) * max (thetaAnalyticRadiusBase c) (2 : ℝ));
  let Cflow : ℝ := (40 : ℝ);
  let Rflow : ℝ := (2 : ℝ) ^ (10 : ℕ);
  let _ : ℝ := iterateKmatConstant β C₀;
  let P : ℝ := iterateRatioConstant β Ck;
  let _ : ℝ := iterateMeanScaleConstant β C₀ P;
  let Csource : ℝ := max (1 : ℝ) (iterateReducedSourceConstant β C₀ c Ck Cflow Rflow Ctheta);
  let p : ℝ := (2 : ℝ) * delta β;
  let Ct : ℝ := (8 : ℝ) * (↑((2 : ℕ) * Nstar β).factorial : ℝ) * Csource ^ (3 : ℕ);
  ∀ (I : Ingredients β), I.Czeta ≤ C₀ → I.Chat ≤ C₀ → ∀ (Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ) (hΦ :
    IsStreamSeq I Φ) (κ : ℝ) (M : ℕ), κ ∈ permittedInterval β I.Λ M → ∀ (R : ℝ), (0 : ℝ) < R → ∀
    (θ₀ : Vec (2 : ℕ) → ℝ), IsThetaAnalytic R θ₀ → ∀ (m : ℕ), mTheta0 β I.Λ R ≤ m → m ≤ M → ∀
    (θprev : ℝ → Vec (2 : ℕ) → ℝ) (T : ℕ → ℝ → Vec (2 : ℕ) → ℝ), IsClassicalSol (streamVel (Φ (m
    - (1 : ℕ)))) (I.kappaSeq κ M (m - (1 : ℕ))) (fun (_ : ℝ) (_ : Vec (2 : ℕ)) => (0 : ℝ)) θ₀
    θprev → I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - (1 : ℕ))) θ₀ θprev T → (2
    : ℕ) ≤ m → (1 : ℕ) ≤ m - (1 : ℕ) → (0 : ℝ) ≤ C₀ → (0 : ℝ) < κ → ((∀ (m : ℕ), (1 : ℕ) ≤ m → m
    < M → c * (AVenhance.a β I.Λ m * epsilon β I.Λ m ^ ((2 : ℝ) + gamma β)) ≤ I.kappaAt κ m (M -
    m) ∧ I.kappaAt κ m (M - m) ≤ Ck * (AVenhance.a β I.Λ m * epsilon β I.Λ m ^ ((2 : ℝ) + gamma
    β))) ∧ ∀ (m : ℕ), (2 : ℕ) ≤ m → m < M → c * epsilon β I.Λ (m - (1 : ℕ)) ^ ((4 : ℝ) * delta
    β) ≤ epsilon β I.Λ m ^ (2 : ℕ) / (I.kappaAt κ m (M - m) * tau β I.Λ m) ∧ epsilon β I.Λ m ^
    (2 : ℕ) / (I.kappaAt κ m (M - m) * tau β I.Λ m) ≤ Ck * epsilon β I.Λ (m - (1 : ℕ)) ^ ((4 :
    ℝ) * delta β)) → (∀ (j : ℕ), (1 : ℕ) ≤ j → ∀ (t : ℝ) (n : ℕ), (2 : ℕ) ≤ n → barNorm n ((2 :
    ℝ) ^ (8 : ℕ) * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤ ENNReal.ofReal ((2 : ℝ) ^ (5 : ℕ) *
    AVenhance.a β I.Λ j * epsilon β I.Λ j ^ (2 : ℕ) * (((↑n : ℝ) + (2 : ℝ)) ^ (2 : ℕ) / ((↑n :
    ℝ) + (1 : ℝ)) ^ (3 : ℕ)))) → (0 : ℝ) < epsilon β I.Λ (m - (1 : ℕ)) → epsilon β I.Λ (m - (1 :
    ℕ)) ≤ (1 : ℝ) → (0 : ℝ) < Csource → (0 : ℝ) < delta β → Csource ^ (3 : ℕ) * epsilon β I.Λ (m
    - (1 : ℕ)) ^ p ≤ (1 / 4 : ℝ) → epsilon β I.Λ (m - (1 : ℕ)) ^ p ≤ ((4 : ℝ) * Csource ^ (3 :
    ℕ))⁻¹ → (0 : ℝ) ≤ gamma β → epsilon β I.Λ (m - (1 : ℕ)) ^ ((2 : ℝ) + gamma β) ≤ (1 : ℝ) →
    Csource ^ (3 : ℕ) * epsilon β I.Λ (m - (1 : ℕ)) ^ p * max (1 : ℝ) (epsilon β I.Λ (m - (1 :
    ℕ)) ^ ((2 : ℝ) + gamma β) * (1 : ℝ) ^ (-2 : ℤ)) ≤ (1 : ℝ) → (1 : ℝ) ≤ Csource →
    iterateReducedSourceConstant β C₀ c Ck Cflow Rflow Ctheta ≤ Csource →
    SectionFourIterateContract I m θ₀ θprev T Ct
    := by
  intro β C₀ c Ck hc hcC Ctheta Cflow Rflow K P Cmean Csource p Ct I hCz hCh Φ hΦ κ M hperm R hR
      θ₀ hanalytic m hmθ hmM θprev T hθprev hT hm2 hmpos hCcut hκpos hA5 hA3 hE hE1 hCsourcePos hδ
      hsourceSmall hchainSmall hgamma hpowE hsmallV hCsrcGe1 hCsrcSource
  have hDthreshold : iterateDischargeThreshold β C₀ Ck ≤ Csource := by
    dsimp [Csource] at hCsrcSource ⊢
    exact (le_max_left _ _).trans hCsrcSource
  have hsourceBound :
      iterateSourceConstant
        (iterateBudgetUniversalConstant K Ck c ((2 : ℝ) ^ (-25 : ℤ)) Cflow Cmean)
        Rflow Ctheta ≤ Csource := by
    have h := (le_max_right _ _ :
      iterateSourceConstant
        (iterateBudgetUniversalConstant K Ck c ((2 : ℝ) ^ (-25 : ℤ)) Cflow Cmean)
        Rflow Ctheta ≤ iterateReducedSourceConstant β C₀ c Ck Cflow Rflow Ctheta)
    exact h.trans hCsrcSource
  have hThetaRadius : 4 * max (thetaAnalyticRadiusBase c) 2 ≤ Ctheta :=
    le_max_right _ _
  have hRadius := theta_profile_radius_absorbed_by_source_constant
    hThetaRadius hsourceBound
  have hRscale : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ R := by
    have hspecR := AVenhance.Infra.Section5.mTheta0_spec I.one_lt_beta I.beta_lt
      I.two_pow_seven_le hR
    have hindex : mTheta0 β I.Λ R - 1 ≤ m - 1 := by omega
    have hEmono := AVenhance.Infra.Section5.RelativeError.epsilon_antitone
      I.one_lt_beta I.beta_lt I.two_pow_seven_le hindex
    have hthetaE : 0 < epsilon β I.Λ (mTheta0 β I.Λ R - 1) :=
      Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hpow := Real.rpow_le_rpow (z := 1 + gamma β / 2) hE.le hEmono
      (by linarith [Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt])
    exact hpow.trans hspecR.2
  have hκm : 0 < I.kappaSeq κ M m := by
    simpa [Ingredients.kappaSeq] using Infra.Section3.kappaAt_pos I hκpos m (M - m)
  have hinputs := iterate_chain_upgrade_inputs I hCz hCh hm2 hmM hκpos hperm
    (hc.trans hcC).le hCsrcGe1 hDthreshold hchainSmall
    (fun j hj hjM => (hA5.2 j hj hjM).2)
  have hKnonneg : 0 ≤ K := by dsimp [K, iterateKmatConstant]; positivity
  have hCmeannonneg : 0 ≤ Cmean := by
    dsimp [Cmean, iterateMeanScaleConstant, P, iterateRatioConstant]
    positivity
  have hCflow : 0 ≤ Cflow := by dsimp [Cflow]; norm_num
  have hRflowBound : 256 ≤ Rflow := by dsimp [Rflow]; norm_num
  have hκprev : 0 < I.kappaSeq κ M (m - 1) := by
    have hlow := hA5.1 (m - 1) hmpos (by omega)
    have ha : 0 < a β I.Λ (m - 1) := by
      rw [a]
      exact Real.rpow_pos_of_pos hE _
    have hfactor : 0 < a β I.Λ (m - 1) *
        epsilon β I.Λ (m - 1) ^ (2 + gamma β) :=
      mul_pos ha (Real.rpow_pos_of_pos hE _)
    simpa [Ingredients.kappaSeq] using (mul_pos hc hfactor).trans_le hlow.1
  have hlower : c * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)) ≤
      I.kappaSeq κ M (m - 1) := by
    simpa [Ingredients.kappaSeq] using (hA5.1 (m - 1) hmpos (by omega)).1
  have hupper : I.kappaSeq κ M (m - 1) ≤
      Ck * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)) := by
    simpa [Ingredients.kappaSeq] using (hA5.1 (m - 1) hmpos (by omega)).2
  have hKm : ∀ t j k, |I.Kmat (I.kappaSeq κ M m) m t j k| ≤
      K * I.kappaSeq κ M (m - 1) := by
    intro t j k
    simpa [K, Ingredients.kappaSeq] using hinputs.1 t j k
  have hMean : ∀ j k,
      |(timeAvgMat (I.Kmat (I.kappaSeq κ M m) m) -
        I.kappaSeq κ M (m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
      I.kappaSeq κ M (m - 1) * Cmean * epsilon β I.Λ (m - 1) ^ p := by
    exact @sectionFourIterate_contract_Mean4 β C₀ Ck I κ M R m hmM hm2 hκm hinputs
  have hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2) :=
    fun l => iterate_flowGrad_joint_smooth I hΦ m l
  have hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t) := by
    intro t _ l
    exact iterate_flowGrad_periodic I hΦ m l t
  have hzero : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ j k,
      |(I.flowGrad hΦ m l t x - 1) j k| ≤ Cflow * epsilon β I.Λ (m - 1) ^ p := by
    intro t x l hn j k
    simpa [Cflow, p] using iterate_flowGrad_zero_bound I hΦ hm2 hn x j k
  have hpositive : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ w : List (Fin 2), 1 ≤ w.length → ∀ j k,
      |iterateSpatialWord w (fun y => (I.flowGrad hΦ m l t y - 1) j k) x| ≤
        Cflow * (w.length.factorial : ℝ) *
          (Rflow / epsilon β I.Λ (m - 1)) ^ w.length := by
    intro t x l hn w hw j k
    simpa [Cflow, Rflow] using iterate_flowGrad_word_bound I hΦ hm2 hn w x j k
  have hφ : IsAdmissibleStream (fun t => Φ (m - 1) t) :=
    theta_prev_stream_admissible I Φ hΦ hm2
  have hthetaSol : IsClassicalSol (streamVel (Φ (m - 1)))
      (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev := hθprev
  have hL2nonneg : 0 ≤ l2NormSq θ₀ := by
    unfold l2NormSq
    exact integral_nonneg fun _ => sq_nonneg _
  have hrootnonneg : 0 ≤ Real.sqrt (l2NormSq θ₀) := Real.sqrt_nonneg _
  have hrootSq : (Real.sqrt (l2NormSq θ₀)) ^ 2 = l2NormSq θ₀ :=
    Real.sq_sqrt hL2nonneg
  have hEnegative : 1 ≤ epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2) := by
    have hexp : (-1 : ℝ) - gamma β / 2 ≤ 0 := by linarith [hgamma]
    have hpow := Real.rpow_le_rpow_of_exponent_ge (y := 0)
      (z := -1 - gamma β / 2) hE hE1 hexp
    simpa using hpow
  have hLmax : Csource / 1 ≤ Csource * epsilon β I.Λ (m - 1) ^
      (-1 - gamma β / 2) := by
    rw [div_one]
    calc
      Csource = Csource * 1 := by ring
      _ ≤ Csource * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2) :=
        mul_le_mul_of_nonneg_left hEnegative (by linarith [hCsrcGe1])
  let Target := Ct * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀)
  let F := ((2 * Nstar β).factorial : ℝ) *
    (4 * Csource ^ 3 * epsilon β I.Λ (m - 1) ^ p)
  have heta : 0 ≤ Csource ^ 3 * epsilon β I.Λ (m - 1) ^ p := by positivity
  have hetaSmall : Csource ^ 3 * epsilon β I.Λ (m - 1) ^ p ≤ 1 / 4 :=
    hsourceSmall
  have hThetaSpatialSmooth : ∀ r : ℝ, 0 ≤ r → ContDiff ℝ (⊤ : ℕ∞) (θprev r) := by
    intro r hr
    exact classicalSmooth_slice_nonneg hthetaSol.1 (t := r) hr
  have hFpos : 0 < F := by dsimp [F]; positivity
  have hbound (q : ℝ) (hq : 0 < q) :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (l2NormSq (fun x => T (Nstar β) t x - θprev t x)) ≤ Target + F * q := by
    exact @sectionFourIterate_contract_bound1 β C₀ c Ck hc hcC I Φ hΦ κ M R hR θ₀ hanalytic m hmM
        θprev T hT hm2 hκpos hA5 hA3 hE hE1 hδ hpowE hsmallV hsourceBound hRadius hRscale hκm
        hKnonneg hCmeannonneg hCflow hRflowBound hlower hupper hKm hMean hflow hflowp hzero
        hpositive hφ hthetaSol hrootnonneg hrootSq hLmax heta hetaSmall hThetaSpatialSmooth q hq
  have htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => T (Nstar β) t x - θprev t x)) ≤ Target := by
    exact @sectionFourIterate_contract_target3 β C₀ c Ck I θ₀ m θprev T hE hFpos hbound
  intro t ht
  simpa [Target] using htarget t ht

/-- The step-down part (i) temperature closeness estimate in the contract shape.
The V theorem is applied with a positive slack above twice the initial L2 norm,
then the slack is eliminated by contradiction. -/
theorem sectionFourIterate_contract (β C₀ : ℝ) :
    ∃ C : ℝ, ∃ C₁ : ℝ,
      OnA8Instances β C₀ C₁ (fun I _Φ _hΦ _κ _M _R θ₀ m _θm θprev T =>
        SectionFourIterateContract I m θ₀ θprev T C) := by
  obtain ⟨c, Ck, hc, hcC, hrec⟩ := AVenhance.l_recurse β C₀
  let Ctheta := max 1 (4 * max (thetaAnalyticRadiusBase c) 2)
  let Cflow : ℝ := 40
  let Rflow : ℝ := 2 ^ 10
  let K := iterateKmatConstant β C₀
  let P := iterateRatioConstant β Ck
  let Cmean := iterateMeanScaleConstant β C₀ P
  let Csource := max 1
    (iterateReducedSourceConstant β C₀ c Ck Cflow Rflow Ctheta)
  let D := 4 * Csource ^ 3
  let p := 2 * delta β
  let threshold := max (128 : ℝ) ((D⁻¹) ^ (p⁻¹))⁻¹
  let Ct := 8 * ((2 * Nstar β).factorial : ℝ) * Csource ^ 3
  refine ⟨Ct, threshold, ?_⟩
  intro I hCz hCx hCh hΛ Φ hΦ κ hκperm M hM hperm R hR θ₀ hθsmooth hθperiodic
    hθmean hanalytic m hmθ hmM θm θprev T hθm hθprev hT
  have hm2 : 2 ≤ m := by
    have hspec := AVenhance.Infra.Section5.mTheta0_spec I.one_lt_beta I.beta_lt
      I.two_pow_seven_le hR
    exact hspec.1.trans hmθ
  have hmpos : 1 ≤ m - 1 := by omega
  have hMpos : 1 ≤ M := by omega
  have hCcut : 0 ≤ C₀ := (by norm_num : (0 : ℝ) ≤ 1).trans
    (le_trans I.one_le_Czeta hCz)
  have hpermissible : κ ∈ permissibleSet β I.Λ := by
    exact Set.mem_iUnion.mpr ⟨M, Set.mem_iUnion.mpr ⟨hMpos, hperm⟩⟩
  have hκpos : 0 < κ :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (Real.rpow_pos_of_pos
        (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) _)).trans_le
      hperm.1
  have hA5 := hrec I hCz hCx hCh κ hpermissible M hMpos hperm
  obtain ⟨_Creg, _hCreg, hreg⟩ := AVenhance.stream_regularity β
  have hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)) := by
    intro j hj t n hn
    exact (hreg I Φ hΦ j hj t).2.1 n hn
  have hE : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hE1 : epsilon β I.Λ (m - 1) ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hCsourcePos : 0 < Csource := by
    dsimp [Csource]
    positivity
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hp : 0 < p := by dsimp [p]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hDinv : 0 < D⁻¹ := inv_pos.mpr hD
  have hthreshold128 : (128 : ℝ) ≤ I.Λ := by
    have h := le_trans (le_max_left _ _) hΛ
    exact_mod_cast h
  have hthresholdInv : ((D⁻¹) ^ (p⁻¹))⁻¹ ≤ (I.Λ : ℝ) :=
    le_trans (le_max_right _ _) hΛ
  have hthresholdPos : 0 < (I.Λ : ℝ) := by positivity
  have hbasePos : 0 < (D⁻¹) ^ (p⁻¹) := Real.rpow_pos_of_pos hDinv _
  have hprod : 1 ≤ (I.Λ : ℝ) * (D⁻¹) ^ (p⁻¹) := by
    have hmul := mul_le_mul_of_nonneg_right hthresholdInv hbasePos.le
    have hinv : ((D⁻¹) ^ (p⁻¹))⁻¹ * (D⁻¹) ^ (p⁻¹) = 1 :=
      inv_mul_cancel₀ hbasePos.ne'
    rw [hinv] at hmul
    exact hmul
  have hEthreshold : epsilon β I.Λ (m - 1) ≤ (D⁻¹) ^ (p⁻¹) := by
    exact @sectionFourIterate_contract_Ethreshold2 β C₀ c Ck I m hmpos hthresholdPos hprod
  have hEthreshold' : epsilon β I.Λ (m - 1) ≤ (1 / D) ^ (p⁻¹) := by
    simpa [one_div] using hEthreshold
  have hDsmall := power_smallness_of_threshold hE.le hp hD
    (by norm_num : (0 : ℝ) ≤ 1) hEthreshold'
  have hpowSmall : epsilon β I.Λ (m - 1) ^ p ≤ D⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hD).2
    simpa [mul_comm] using hDsmall
  have hsourceSmall : Csource ^ 3 * epsilon β I.Λ (m - 1) ^ p ≤ 1 / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hpowSmall (by positivity : 0 ≤ Csource ^ 3)
    calc
      _ ≤ Csource ^ 3 * D⁻¹ := hmul
      _ = 1 / 4 := by
        dsimp [D]
        field_simp [ne_of_gt hCsourcePos]
  have hchainSmall : epsilon β I.Λ (m - 1) ^ p ≤ (4 * Csource ^ 3)⁻¹ := by
    simpa [D] using hpowSmall
  have hgamma : 0 ≤ gamma β :=
    (Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt).le
  have hpowE : epsilon β I.Λ (m - 1) ^ (2 + gamma β) ≤ 1 :=
    Real.rpow_le_one hE.le hE1 (by linarith)
  have hmax : max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) *
      (1 : ℝ) ^ (-2 : ℤ)) = 1 := by
    simp only [one_zpow, mul_one]
    exact max_eq_left hpowE
  have hsmallV : Csource ^ 3 * epsilon β I.Λ (m - 1) ^ p *
      max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) *
        (1 : ℝ) ^ (-2 : ℤ)) ≤ 1 := by
    rw [hmax, mul_one]
    exact hsourceSmall.trans (by norm_num)
  have hCsrcGe1 : 1 ≤ Csource := le_max_left _ _
  have hCsrcSource : iterateReducedSourceConstant β C₀ c Ck Cflow Rflow Ctheta ≤ Csource :=
    le_max_right _ _
  exact @sectionFourIterate_contract_conclusion5 β C₀ c Ck hc hcC I hCz hCh Φ hΦ κ M hperm R hR θ₀
      hanalytic m hmθ hmM θprev T hθprev hT hm2 hmpos hCcut hκpos hA5 hA3 hE hE1 hCsourcePos hδ
      hsourceSmall hchainSmall hgamma hpowE hsmallV hCsrcGe1 hCsrcSource
end AVenhance.Infra.Section5.Contracts
