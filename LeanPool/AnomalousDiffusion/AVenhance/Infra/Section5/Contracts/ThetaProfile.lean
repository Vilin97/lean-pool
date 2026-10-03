/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaProfileDischarge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaZeroBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LaterStart
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.BaseEnergyClassical
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MStar

/-! # Step-down estimate theta profile contract with constants fixed before the instance -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5
  AVenhance.Infra.Section5.Integration

theorem ThetaProfile.iterateSpatialWord_eq_classicalWordDerivative
    (w : List (Fin 2)) (f : Vec 2 → ℝ) :
    iterateSpatialWord w f = classicalWordDerivative w f := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [iterateSpatialWord, classicalWordDerivative,
    Classical.classicalWordDerivative, ih]

theorem ThetaProfile.theta_profile_of_explicit_A3_A5
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m M : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M)
    {κ R : ℝ}
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    (hR : 0 < R) (hscale : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ R)
    (hθ₀ : IsThetaAnalytic R θ₀)
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1)))
      (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev)
    {c C Cs : ℝ} (hc : 0 < c) (hcC : c < C)
    (hRadius : 8 * max (thetaAnalyticRadiusBase c) 2 ≤ Cs)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (hA5 : ∀ j : ℕ, 1 ≤ j → j < M →
      c * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) ≤
        I.kappaAt κ j (M - j) ∧
      I.kappaAt κ j (M - j) ≤ C * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β))) :
    iterateCoordinateEnergyProfile θprev (I.kappaSeq κ M (m - 1))
      (2 * Real.sqrt (l2NormSq θ₀))
      (Cs * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0 := by
  let B := 2 * Real.sqrt (l2NormSq θ₀)
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hSnonneg : 0 ≤ l2NormSq θ₀ := by
    unfold l2NormSq
    exact integral_nonneg fun _ => sq_nonneg _
  have hφ : IsAdmissibleStream (Φ (m - 1)) := theta_prev_stream_admissible I Φ hΦ hm
  have hlow := hA5 (m - 1) (by omega) (by omega)
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ha : 0 < a β I.Λ (m - 1) := by
    rw [a]
    exact Real.rpow_pos_of_pos he _
  have hκprev : 0 < I.kappaSeq κ M (m - 1) := by
    have hfactor : 0 < a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^
        (2 + gamma β) := mul_pos ha (Real.rpow_pos_of_pos he _)
    simpa [Ingredients.kappaSeq] using (mul_pos hc hfactor).trans_le hlow.1
  by_cases hBzero : B = 0
  · have hroot : Real.sqrt (l2NormSq θ₀) = 0 := by dsimp [B] at hBzero; linarith
    have hSzero : l2NormSq θ₀ = 0 := by
      have hsq := congrArg (fun x : ℝ => x ^ 2) hroot
      rw [Real.sq_sqrt hSnonneg] at hsq
      simpa using hsq
    have hθ₀smooth : ContDiff ℝ (⊤ : ℕ∞) θ₀ := by
      have hsmooth := classicalSmooth_slice_nonneg hθprev.1 (t := 0) (by norm_num)
      have hinit : θprev 0 = θ₀ := funext hθprev.2.2.1
      rw [← hinit]
      exact hsmooth
    have hθ₀zero : θ₀ = (fun _ : Vec 2 => 0) :=
      theta_continuous_periodic_eq_zero_of_l2NormSq_eq_zero
        hθ₀smooth
        (by
          have hper := hθprev.2.1 0 (by norm_num)
          have hinit : θprev 0 = θ₀ := funext hθprev.2.2.1
          rw [← hinit]
          exact hper)
        hSzero
    have hsolzero : IsClassicalSol (streamVel (Φ (m - 1)))
        (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) (fun _ => 0) θprev := by
      simpa [hθ₀zero] using hθprev
    have hprofile : iterateCoordinateEnergyProfile θprev
        (I.kappaSeq κ M (m - 1)) 0
        (Cs * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0 := by
      constructor
      · intro w hw s hs hs1
        have hsp := theta_zero_word_spatial_energy_eq_zero hφ hκprev hsolzero w hs
        have hnorm : l2NormSq (iterateSpatialWord w (θprev s)) = 0 := by
          simpa [l2NormSq, thetaWordSpatialEnergy,
            ThetaProfile.iterateSpatialWord_eq_classicalWordDerivative] using hsp
        rw [hnorm]
        simp [iterateAnalyticWeight]
      · intro w
        have hg := theta_zero_word_spacetime_gradient_energy_eq_zero hφ hκprev hsolzero w
        have hgrad : spaceTimeGradNormSq
            (fun t => spaceGrad (iterateSpatialWord w (θprev t))) = 0 := by
          simpa [thetaWordSpaceTimeGradientEnergy, spaceTimeGradNormSq,
            ThetaProfile.iterateSpatialWord_eq_classicalWordDerivative] using hg
        rw [hgrad]
        simp [iterateAnalyticWeight]
    simpa [B, hBzero] using hprofile
  · have hB : 0 < B := lt_of_le_of_ne hBnonneg (Ne.symm hBzero)
    have hBnorm : Real.sqrt (l2NormSq θ₀) ≤ B := by
      dsimp [B]
      nlinarith [Real.sqrt_nonneg (l2NormSq θ₀)]
    have hTraceAll := fun w => theta_initial_word_l2_le_of_analytic hθ₀ hθprev w
    have hTrace : ∀ w : List (Fin 2), 1 ≤ w.length →
        Real.sqrt (∫ x in unitCube, (classicalWordDerivative w θ₀ x) ^ 2) ≤
          B * ((w.length.factorial : ℝ) / R ^ w.length) := by
      intro w _
      exact (hTraceAll w).trans (mul_le_mul_of_nonneg_right hBnorm (by positivity))
    have hInitial : l2NormSq θ₀ ≤ B ^ 2 := by
      have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) (show 0 ≤ B by linarith)).mpr hBnorm
      rw [Real.sq_sqrt hSnonneg] at hsquare
      exact hsquare
    have hzero := theta_homogeneous_gradient_energy_le_of_initial_l2_sq hφ hθprev hInitial
    exact theta_iterate_profile_of_initial_trace_A3_A5 (C₀ := Cs) I Φ hΦ hm hmM
      hc hcC hB hR hRadius
      hscale hzero hTrace hA3 hA5 hθprev

private theorem thetaProfile_S_of_explicit_A3_A5_T1h_branch1 :
  ∀ {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ}, IsStreamSeq I Φ → ∀ {m M : ℕ}, (2
    : ℕ) ≤ m → m ≤ M → ∀ {κ Ctr Cs : ℝ} {θ₀ : Vec (2 : ℕ) → ℝ} {θprev : ℝ → Vec (2 : ℕ) → ℝ}, (1
    : ℝ) ≤ Ctr → (∀ (w : List (Fin (2 : ℕ))), (1 : ℕ) ≤ w.length → √(∫ (x : Vec (2 : ℕ)) in
    unitCube, classicalWordDerivative w θ₀ x ^ (2 : ℕ)) ≤ √(I.kappaSeq κ M (m - (1 : ℕ))) *
    √(spaceTimeGradNormSq fun (t : ℝ) => spaceGrad (θprev t)) * ((↑w.length.factorial : ℝ) /
    (epsilon β I.Λ (m - (1 : ℕ)) ^ ((1 : ℝ) + gamma β / (2 : ℝ)) / Ctr ^ (2 : ℕ)) ^ w.length)) →
    ∀ {c C : ℝ}, (0 : ℝ) < c → c < C → (8 : ℝ) * max (thetaAnalyticRadiusBase c) ((2 : ℝ) * Ctr
    ^ (2 : ℕ)) ≤ Cs → (∀ (j : ℕ), (1 : ℕ) ≤ j → ∀ (t : ℝ) (n : ℕ), (2 : ℕ) ≤ n → barNorm n ((2 :
    ℝ) ^ (8 : ℕ) * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤ ENNReal.ofReal ((2 : ℝ) ^ (5 : ℕ) *
    AVenhance.a β I.Λ j * epsilon β I.Λ j ^ (2 : ℕ) * (((↑n : ℝ) + (2 : ℝ)) ^ (2 : ℕ) / ((↑n :
    ℝ) + (1 : ℝ)) ^ (3 : ℕ)))) → (∀ (j : ℕ), (1 : ℕ) ≤ j → j < M → c * (AVenhance.a β I.Λ j *
    epsilon β I.Λ j ^ ((2 : ℝ) + gamma β)) ≤ I.kappaAt κ j (M - j) ∧ I.kappaAt κ j (M - j) ≤ C *
    (AVenhance.a β I.Λ j * epsilon β I.Λ j ^ ((2 : ℝ) + gamma β))) → IsClassicalSol (streamVel
    (Φ (m - (1 : ℕ)))) (I.kappaSeq κ M (m - (1 : ℕ))) (fun (_ : ℝ) (_ : Vec (2 : ℕ)) => (0 :
    ℝ)) θ₀ θprev →
  let κm : ℝ := I.kappaSeq κ M (m - (1 : ℕ));
  let e : ℝ := epsilon β I.Λ (m - (1 : ℕ));
  let p : ℝ := (1 : ℝ) + gamma β / (2 : ℝ);
  let S : ℝ := √κm * √(spaceTimeGradNormSq fun (t : ℝ) => spaceGrad (θprev t));
  (0 : ℝ) < e → (0 : ℝ) < κm → (0 : ℝ) ≤ S → (κm * spaceTimeGradNormSq fun (t : ℝ) => spaceGrad
    (θprev t)) ≤ S ^ (2 : ℕ) → (0 : ℝ) < e ^ p / Ctr ^ (2 : ℕ) → ¬S = (0 : ℝ) →
    iterateCoordinateEnergyProfile θprev (I.kappaSeq κ M (m - (1 : ℕ))) (√(I.kappaSeq κ M (m -
    (1 : ℕ))) * √(spaceTimeGradNormSq fun (t : ℝ) => spaceGrad (θprev t))) (Cs * epsilon β I.Λ
    (m - (1 : ℕ)) ^ ((-1 : ℝ) - gamma β / (2 : ℝ))) (0 : ℕ)
    := by
  intro β I Φ hΦ m M hm hmM κ Ctr Cs θ₀ θprev hCtr hT1h c C hc hcC hRadius hA3 hA5 hθprev κm e p S
      he hκpos hSnonneg hzero hρpos hSzero
  have hSpos : 0 < S := lt_of_le_of_ne hSnonneg (Ne.symm hSzero)
  have hTrace : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in unitCube, (classicalWordDerivative w θ₀ x) ^ 2) ≤
        S * ((w.length.factorial : ℝ) / (e ^ p / Ctr ^ 2) ^ w.length) := by
    intro w hw
    simpa [S, e, p] using hT1h w hw
  have henergy := theta_analytic_positive_energy_bound_of_initial_trace_A3_A5
    I Φ hΦ hm hmM hc hcC hSpos hρpos hzero hTrace hA3 hA5 hθprev
  have hκpos' : 0 < κm := hκpos
  let L := thetaAnalyticRadius c e (gamma β) (e ^ p / Ctr ^ 2)
  let l := 2 * L
  have hLpos : 0 < L := by
    dsimp [L, thetaAnalyticRadius]
    positivity
  have hbaseRadius : L ≤ max (thetaAnalyticRadiusBase c) (2 * Ctr ^ 2) * e ^ (-p) := by
    have hpow : e ^ (-p) = (e ^ p)⁻¹ := by
      rw [Real.rpow_neg he.le]
    have hsecond : 2 / (e ^ p / Ctr ^ 2) ≤ 2 * Ctr ^ 2 * e ^ (-p) := by
      have hEq : 2 / (e ^ p / Ctr ^ 2) = 2 * Ctr ^ 2 * e ^ (-p) := by
        rw [hpow]
        have hpowne : e ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos he p)
        have hCtrne : Ctr ^ 2 ≠ 0 := by positivity
        field_simp
      exact le_of_eq hEq
    dsimp [L, thetaAnalyticRadius]
    rw [show -1 - gamma β / 2 = -p by dsimp [p]; ring]
    apply max_le
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · exact (hsecond.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (by positivity)))
  have htargetRadius : 8 * L ≤ Cs * e ^ (-p) := by
    have h := mul_le_mul_of_nonneg_left hbaseRadius (by norm_num : (0 : ℝ) ≤ 8)
    calc
      8 * L ≤ 8 * (max (thetaAnalyticRadiusBase c) (2 * Ctr ^ 2) * e ^ (-p)) := h
      _ = (8 * max (thetaAnalyticRadiusBase c) (2 * Ctr ^ 2)) * e ^ (-p) := by ring
      _ ≤ Cs * e ^ (-p) := mul_le_mul_of_nonneg_right hRadius (by positivity)
  have hsource : ∀ v w : List (Fin 2), 1 ≤ v.length →
      w.length = v.length + 1 → ∀ s, 0 ≤ s → s ≤ 1 →
      Real.sqrt (l2NormSq (iterateSpatialWord v (θprev s))) +
        Real.sqrt κm * Real.sqrt
          (∫ z in timeCube, (iterateSpatialWord w (θprev z.1) z.2) ^ 2) ≤
        2 * S * (v.length.factorial : ℝ) * l ^ v.length := by
    intro v w hv hw s hs hs1
    cases w with
    | nil => simp at hw
    | cons j tail =>
      have hlen : tail.length = v.length := by simp at hw; omega
      let iv : Fin v.length → Fin 2 := fun k => v.get k
      let it : Fin tail.length → Fin 2 := fun k => tail.get k
      have hwordv : thetaCoordinateWord iv = v := List.ofFn_get v
      have hwordt : thetaCoordinateWord it = tail := List.ofFn_get tail
      have hlevelv := thetaEnergyLevel_le_of_coordinate θprev κm v.length iv
      rw [hwordv] at hlevelv
      have hboundv := henergy v.length hv
      have hspace : l2NormSq (iterateSpatialWord v (θprev s)) =
          thetaWordSpatialEnergy θprev v s := by
        simp only [l2NormSq, thetaWordSpatialEnergy]
        rw [ThetaProfile.iterateSpatialWord_eq_classicalWordDerivative]
      have hspatial := theta_word_spatial_energy_le_sup_of_classical
        hθprev v ⟨hs, hs1⟩
      have hspatial' : l2NormSq (iterateSpatialWord v (θprev s)) ≤
          thetaWordSpatialEnergySup θprev v := by
        rw [hspace]
        exact hspatial
      have hroot : Real.sqrt (l2NormSq (iterateSpatialWord v (θprev s))) ≤
          Real.sqrt (thetaWordSpatialEnergySup θprev v) := Real.sqrt_le_sqrt hspatial'
      have hlevel := hlevelv.trans hboundv
      have hgradnonneg : 0 ≤ Real.sqrt κm *
          Real.sqrt (thetaWordSpaceTimeGradientEnergy θprev v) := by positivity
      have hfirst : Real.sqrt (l2NormSq (iterateSpatialWord v (θprev s))) ≤
          2 * S * (v.length.factorial : ℝ) * L ^ v.length := by
        calc
          _ ≤ Real.sqrt (thetaWordSpatialEnergySup θprev v) := hroot
          _ ≤ 2 * S * (v.length.factorial : ℝ) * L ^ v.length := by
            linarith only [hlevel, hgradnonneg]
      have hlevelt := thetaEnergyLevel_le_of_coordinate θprev κm tail.length it
      rw [hwordt] at hlevelt
      have hboundt := henergy tail.length (by simpa [hlen] using hv)
      have hcomponent := iterate_word_gradient_component_energy_bound
        hθprev.1 tail j
      have hcomponent' :
          (∫ z in timeCube,
            (iterateSpatialWord (j :: tail) (θprev z.1) z.2) ^ 2) ≤
          thetaWordSpaceTimeGradientEnergy θprev tail := by
        calc
          _ ≤ spaceTimeGradNormSq
              (fun t => spaceGrad (iterateSpatialWord tail (θprev t))) := hcomponent
          _ = thetaWordSpaceTimeGradientEnergy θprev tail := by
            simp [thetaWordSpaceTimeGradientEnergy, spaceTimeGradNormSq,
              ThetaProfile.iterateSpatialWord_eq_classicalWordDerivative]
      have hrootComponent := Real.sqrt_le_sqrt hcomponent'
      have hlevelTail := hlevelt.trans hboundt
      have hsecondBound : Real.sqrt κm *
          Real.sqrt (thetaWordSpaceTimeGradientEnergy θprev tail) ≤
          2 * S * (tail.length.factorial : ℝ) * L ^ tail.length := by
        have hspatialNonneg : 0 ≤ Real.sqrt (thetaWordSpatialEnergySup θprev tail) :=
          Real.sqrt_nonneg _
        linarith only [hlevelTail, hspatialNonneg]
      have hsecond : Real.sqrt κm * Real.sqrt
          (∫ z in timeCube,
            (iterateSpatialWord (j :: tail) (θprev z.1) z.2) ^ 2) ≤
          2 * S * (v.length.factorial : ℝ) * L ^ v.length := by
        have hmul := mul_le_mul_of_nonneg_left hrootComponent (Real.sqrt_nonneg κm)
        simpa [hlen] using hmul.trans hsecondBound
      have hsum := add_le_add hfirst hsecond
      have hdouble := iterate_positive_order_radius_double hLpos.le le_rfl hv
      calc
        _ ≤ 4 * S * (v.length.factorial : ℝ) * L ^ v.length := by
          calc
            _ ≤ (2 * S * (v.length.factorial : ℝ) * L ^ v.length) +
                (2 * S * (v.length.factorial : ℝ) * L ^ v.length) := hsum
            _ = 4 * S * (v.length.factorial : ℝ) * L ^ v.length := by ring
        _ ≤ 2 * S * (v.length.factorial : ℝ) * l ^ v.length := by
          have hcoef : 0 ≤ 2 * S * (v.length.factorial : ℝ) := by positivity
          calc
            4 * S * (v.length.factorial : ℝ) * L ^ v.length =
                (2 * S * (v.length.factorial : ℝ)) * (2 * L ^ v.length) := by ring
            _ ≤ (2 * S * (v.length.factorial : ℝ)) * (2 * L) ^ v.length :=
              mul_le_mul_of_nonneg_left hdouble hcoef
            _ = 2 * S * (v.length.factorial : ℝ) * l ^ v.length := by rfl
  have hL : 4 * l ≤ Cs * e ^ (-p) := by
    dsimp [l]
    linarith only [htargetRadius]
  have hprofile := iterate_theta_gradient_base_profile hθprev.1 hκpos hSnonneg
    (by positivity : 0 ≤ l) hL hzero hsource
  have hExponent : -p = -1 - gamma β / 2 := by dsimp [p]; ring
  simpa [S, κm, e, p, hExponent] using hprofile

/-- S-amplitude theta profile under the literal conditional stream-function and diffusivity bounds
    data and
the named trace input. `Cs` is an explicit caller-selected profile
constant, so the uniform radius can be passed without choosing any
constant after the `Ingredients` instance. -/
theorem thetaProfile_S_of_explicit_A3_A5_T1h
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m M : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M)
    {κ Ctr Cs : ℝ}
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    (hCtr : 1 ≤ Ctr)
    (hmean : MeanZeroOn unitCube θ₀)
    (hT1h : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in unitCube,
        (classicalWordDerivative w θ₀ x) ^ 2) ≤
      (Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (θprev t)))) *
        ((w.length.factorial : ℝ) /
          ((epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) / Ctr ^ 2) ^ w.length))
    {c C : ℝ} (hc : 0 < c) (hcC : c < C)
    (hRadius : 8 * max (thetaAnalyticRadiusBase c) (2 * Ctr ^ 2) ≤ Cs)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (hA5 : ∀ j : ℕ, 1 ≤ j → j < M →
      c * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) ≤
        I.kappaAt κ j (M - j) ∧
      I.kappaAt κ j (M - j) ≤ C * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)))
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1)))
      (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev) :
    ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs
      (Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (θprev t)))) := by
  change iterateCoordinateEnergyProfile θprev (I.kappaSeq κ M (m - 1))
    (Real.sqrt (I.kappaSeq κ M (m - 1)) *
      Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (θprev t))))
    (Cs * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0
  let κm := I.kappaSeq κ M (m - 1)
  let e := epsilon β I.Λ (m - 1)
  let p := 1 + gamma β / 2
  let S := Real.sqrt κm * Real.sqrt (spaceTimeGradNormSq
    (fun t => spaceGrad (θprev t)))
  have he : 0 < e := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hφ : IsAdmissibleStream (Φ (m - 1)) := theta_prev_stream_admissible I Φ hΦ hm
  have hlow := hA5 (m - 1) (by omega) (by omega)
  have ha : 0 < a β I.Λ (m - 1) := by
    rw [a]
    exact Real.rpow_pos_of_pos he _
  have hκpos : 0 < κm := by
    have hfactor : 0 < a β I.Λ (m - 1) * e ^ (2 + gamma β) :=
      mul_pos ha (Real.rpow_pos_of_pos he _)
    simpa [κm, Ingredients.kappaSeq, e] using (mul_pos hc hfactor).trans_le hlow.1
  have hSnonneg : 0 ≤ S := by dsimp [S]; positivity
  have hGnonneg : 0 ≤ spaceTimeGradNormSq
      (fun t => spaceGrad (θprev t)) := by
    unfold spaceTimeGradNormSq
    apply integral_nonneg
    intro z
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hzero : κm * spaceTimeGradNormSq (fun t => spaceGrad (θprev t)) ≤ S ^ 2 := by
    dsimp [S]
    rw [mul_pow, Real.sq_sqrt hκpos.le, Real.sq_sqrt hGnonneg]
  have hρpos : 0 < e ^ p / Ctr ^ 2 := by
    have hCtrpos : 0 < Ctr := by linarith
    exact div_pos (Real.rpow_pos_of_pos he p) (by positivity)
  have hφAdmissible : IsAdmissibleStream (Φ (m - 1)) := hφ
  by_cases hSzero : S = 0
  · have hDiss := RelativeError.classical_dissipation_lower hφAdmissible hκpos hθprev hmean
    have hcoeff : 0 < min (1 / 4) (2 * Real.pi ^ 2 * κm) := by
      apply lt_min
      · norm_num
      · positivity
    have hgradzero : κm * spaceTimeGradNormSq
        (fun t => spaceGrad (θprev t)) = 0 := by
      rw [hSzero] at hzero
      have hnonneg := mul_nonneg hκpos.le hGnonneg
      have hzero' : κm * spaceTimeGradNormSq
          (fun t => spaceGrad (θprev t)) ≤ 0 := by simpa using hzero
      exact le_antisymm hzero' hnonneg
    have hnormzero : l2NormSq θ₀ = 0 := by
      have hnormnonneg : 0 ≤ l2NormSq θ₀ := by
        unfold l2NormSq
        exact integral_nonneg fun _ => sq_nonneg _
      rw [hgradzero] at hDiss
      nlinarith only [hDiss, hcoeff, hnormnonneg]
    have hθ₀smooth : ContDiff ℝ (⊤ : ℕ∞) θ₀ := by
      have hsmooth := classicalSmooth_slice_nonneg hθprev.1 (t := 0) (by norm_num)
      have hinit : θprev 0 = θ₀ := funext hθprev.2.2.1
      rw [← hinit]
      exact hsmooth
    have hθ₀periodic : IsZ2Periodic θ₀ := by
      have hper := hθprev.2.1 0 (by norm_num)
      have hinit : θprev 0 = θ₀ := funext hθprev.2.2.1
      rw [← hinit]
      exact hper
    have hθ₀zero : θ₀ = (fun _ : Vec 2 => 0) :=
      theta_continuous_periodic_eq_zero_of_l2NormSq_eq_zero
        hθ₀smooth hθ₀periodic hnormzero
    have hsolzero : IsClassicalSol (streamVel (Φ (m - 1))) κm
        (fun _ _ => 0) (fun _ => 0) θprev := by
      simpa [hθ₀zero] using hθprev
    have hprofile : iterateCoordinateEnergyProfile θprev κm 0
        (Cs * e ^ (-1 - gamma β / 2)) 0 := by
      constructor
      · intro w hw s hs hs1
        have hsp := theta_zero_word_spatial_energy_eq_zero hφ hκpos hsolzero w hs
        have hnorm : l2NormSq (iterateSpatialWord w (θprev s)) = 0 := by
          simpa [l2NormSq, thetaWordSpatialEnergy,
            ThetaProfile.iterateSpatialWord_eq_classicalWordDerivative] using hsp
        rw [hnorm]
        simp [iterateAnalyticWeight]
      · intro w
        have hg := theta_zero_word_spacetime_gradient_energy_eq_zero hφ hκpos hsolzero w
        have hgrad : spaceTimeGradNormSq
            (fun t => spaceGrad (iterateSpatialWord w (θprev t))) = 0 := by
          simpa [thetaWordSpaceTimeGradientEnergy, spaceTimeGradNormSq,
            ThetaProfile.iterateSpatialWord_eq_classicalWordDerivative] using hg
        rw [hgrad]
        simp [iterateAnalyticWeight]
    simpa [S, κm, e, hSzero] using hprofile
  · exact @thetaProfile_S_of_explicit_A3_A5_T1h_branch1 β I Φ hΦ m M hm hmM κ Ctr Cs θ₀ θprev hCtr
      hT1h c C hc hcC hRadius hA3 hA5 hθprev he hκpos hSnonneg hzero hρpos hSzero
/-! The S-amplitude profile has the same explicit stream-function and diffusivity bounds
    dependence as the
analytic-data profile. `hT1h` is the named AV-parameter trace instance input
until the wrapper lands. Its trace radius is the cutoff scale divided by
`Ctr^2`; this loss is paid by the profile radius constant, chosen before `I`. -/

/-- The named input consumed by the relative theta profile. It is the
positive-order wordwise trace, with amplitude exactly the integrated-gradient
quantity `S` and trace radius `epsilon^(1+gamma/2) / Ctr^2`. -/
def T1hThetaInitialTraceInput (β : ℝ) (I : Ingredients β) (κ : ℝ)
    (M m : ℕ) (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (Ctr : ℝ) : Prop :=
  let S := Real.sqrt (I.kappaSeq κ M (m - 1)) *
    Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (θprev t)))
  ∀ w : List (Fin 2), 1 ≤ w.length →
    Real.sqrt (∫ x in unitCube,
      (classicalWordDerivative w θ₀ x) ^ 2) ≤
      S * ((w.length.factorial : ℝ) /
      ((epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) / Ctr ^ 2) ^ w.length)

theorem ThetaProfile.hg_iterateAnalyticWeight_mono_radius {n i : ℕ} {L₁ L₂ : ℝ}
    (hL₁ : 0 ≤ L₁) (hL : L₁ ≤ L₂) :
    iterateAnalyticWeight n i L₁ ≤ iterateAnalyticWeight n i L₂ := by
  unfold iterateAnalyticWeight
  apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL₁ hL n)
  positivity

theorem ThetaProfile.hg_iterateCoordinateEnergyProfile_mono_radius
    {u : ℝ → Vec 2 → ℝ} {κ N L₁ L₂ : ℝ} {i : ℕ}
    (hL₁ : 0 ≤ L₁) (hL : L₁ ≤ L₂)
    (hprofile : iterateCoordinateEnergyProfile u κ N L₁ i) :
    iterateCoordinateEnergyProfile u κ N L₂ i := by
  constructor
  · intro w hw s hs hs1
    have hW := ThetaProfile.hg_iterateAnalyticWeight_mono_radius
      (n := w.length) (i := i) hL₁ hL
    have hW₁ := iterateAnalyticWeight_nonneg w.length i hL₁
    have hWsq : iterateAnalyticWeight w.length i L₁ ^ 2 ≤
        iterateAnalyticWeight w.length i L₂ ^ 2 :=
      (sq_le_sq₀ hW₁ (hW₁.trans hW)).mpr hW
    exact (hprofile.1 w hw s hs hs1).trans
      (mul_le_mul_of_nonneg_left hWsq (sq_nonneg N))
  · intro w
    have hW := ThetaProfile.hg_iterateAnalyticWeight_mono_radius
      (n := w.length) (i := i) hL₁ hL
    have hW₁ := iterateAnalyticWeight_nonneg w.length i hL₁
    have hWsq : iterateAnalyticWeight w.length i L₁ ^ 2 ≤
        iterateAnalyticWeight w.length i L₂ ^ 2 :=
      (sq_le_sq₀ hW₁ (hW₁.trans hW)).mpr hW
    exact (hprofile.2 w).trans
      (mul_le_mul_of_nonneg_left hWsq (sq_nonneg (N / Real.sqrt κ)))

/-- Conditional exact `ThetaProfileContract` at the relative amplitude `S`.
The only additional per-instance premise is the positive-order initial
trace. All profile constants are fixed before the `Ingredients` instance. -/
theorem thetaProfile_S_contract_of_T1h (β C₀ Ctr : ℝ) (hCtr : 1 ≤ Ctr) :
    ∃ Cs_S : ℝ, 1 ≤ Cs_S ∧ ∀ Cs : ℝ, Cs_S ≤ Cs →
      OnA8Instances β C₀ 0
        (fun I _Φ _hΦ κ M _R θ₀ m _θm θprev _T =>
          T1hThetaInitialTraceInput β I κ M m θ₀ θprev Ctr →
          ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs
            (Real.sqrt (I.kappaSeq κ M (m - 1)) *
              Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (θprev t))))) := by
  obtain ⟨c, C, hc, hcC, hrec⟩ := AVenhance.l_recurse β C₀
  obtain ⟨_, _, hstream⟩ := AVenhance.stream_regularity β
  let Cs_S := 8 * max (thetaAnalyticRadiusBase c) (2 * Ctr ^ 2)
  have hCsS : 1 ≤ Cs_S := by
    dsimp [Cs_S]
    have hCtrSq : 1 ≤ Ctr ^ 2 := by nlinarith [sq_nonneg (Ctr - 1)]
    have hmax : (2 : ℝ) ≤ max (thetaAnalyticRadiusBase c) (2 * Ctr ^ 2) := by
      calc
        2 ≤ 2 * Ctr ^ 2 := by nlinarith
        _ ≤ max (thetaAnalyticRadiusBase c) (2 * Ctr ^ 2) := le_max_right _ _
    nlinarith
  refine ⟨Cs_S, hCsS, ?_⟩
  intro Cs hCs I hCzeta hCxi hChat _hC₁ Φ hΦ κ hpermissible M hM hPerm R hR θ₀ _hθ₀smooth
    _hθ₀per hmean _hanalytic m hm0 hmM θm θprev _T _hθm hθprev _hT hT1h
  have hm : 2 ≤ m := by
    exact (mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR).1.trans hm0
  have hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)) := by
    intro j hj t n hn
    exact (hstream I Φ hΦ j hj t).2.1 n hn
  have hA5 : ∀ j : ℕ, 1 ≤ j → j < M →
      c * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) ≤
        I.kappaAt κ j (M - j) ∧
      I.kappaAt κ j (M - j) ≤ C * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) :=
    (hrec I hCzeta hCxi hChat κ hpermissible M hM hPerm).1
  have hprofile := thetaProfile_S_of_explicit_A3_A5_T1h I hΦ hm hmM
    (κ := κ) (Ctr := Ctr) (Cs := Cs_S) (θ₀ := θ₀) (θprev := θprev)
    hCtr hmean hT1h hc hcC (by dsimp [Cs_S]; exact le_rfl) hA3 hA5 hθprev
  have hε : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hradFactor : 0 < epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2) :=
    Real.rpow_pos_of_pos hε _
  have hradBase : 0 ≤ Cs_S * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2) :=
    mul_nonneg (by linarith [hCsS]) hradFactor.le
  have hradLe : Cs_S * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2) ≤
      Cs * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2) :=
    mul_le_mul_of_nonneg_right hCs hradFactor.le
  have hprofile' := ThetaProfile.hg_iterateCoordinateEnergyProfile_mono_radius
    hradBase hradLe hprofile
  simpa [ThetaProfileContract] using hprofile'

/-- The exact step-down estimate theta-profile contract at the amplitude.  The stream-function
    barNorm data and diffusivity bounds
diffusivity constants are extracted with constants fixed before the `Ingredients` instance. -/
theorem thetaProfile_contract (β C₀ : ℝ) :
    ∃ Cs C₁ : ℝ,
      OnA8Instances β C₀ C₁ (fun I _Φ _hΦ κ M _R θ₀ m _θm θprev _T =>
        ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs
          (2 * Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨c, C, hc, hcC, hrec⟩ := AVenhance.l_recurse β C₀
  obtain ⟨_, _, hstream⟩ := AVenhance.stream_regularity β
  let Cs := 8 * max (thetaAnalyticRadiusBase c) 2
  refine ⟨Cs, 0, ?_⟩
  intro I hCzeta hCxi hChat _hC₁ _Φ _hΦ κ hpermissible M hM hPerm _R hR θ₀ _hθ₀smooth
    _hθ₀per _hmean hanalytic m hm0 hmM _θm θprev _T _hθm hθprev _hT
  have hm : 2 ≤ m := by
    exact (mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR).1.trans hm0
  have hscale : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ _R := by
    have hstar := mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR
    have hmono : epsilon β I.Λ (m - 1) ≤ epsilon β I.Λ (mTheta0 β I.Λ _R - 1) :=
      AVenhance.Infra.Section5.RelativeError.epsilon_antitone
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (by omega)
    have hexp : 0 ≤ 1 + gamma β / 2 := by
      have hγ := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
      linarith
    exact (Real.rpow_le_rpow
      (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
      hmono hexp).trans hstar.2
  have hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (_Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)) := by
    intro j hj t n hn
    exact (hstream I _Φ _hΦ j hj t).2.1 n hn
  have hA5 : ∀ j : ℕ, 1 ≤ j → j < M →
      c * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) ≤
        I.kappaAt κ j (M - j) ∧
      I.kappaAt κ j (M - j) ≤ C * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) :=
    (hrec I hCzeta hCxi hChat κ hpermissible M hM hPerm).1
  have hCsRadius : 8 * max (thetaAnalyticRadiusBase c) 2 ≤ Cs := by
    dsimp [Cs]
    rfl
  have hprofile := ThetaProfile.theta_profile_of_explicit_A3_A5 I _hΦ hm hmM (κ := κ) (R := _R)
    (θ₀ := θ₀) (θprev := θprev) hR hscale hanalytic hθprev hc hcC
    hCsRadius hA3 hA5
  simpa [ThetaProfileContract, Cs] using hprofile

end AVenhance.Infra.Section5.Contracts

end
