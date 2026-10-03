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

/-! # `SourceErrorDContract`: the θ profile in the big-bound premise block

`Contracts/ThetaProfile.lean` produces `ThetaProfileContract` at `N = 2‖θ₀‖` in the step-down
    premise block
(`OnA8Instances`, which carries an unused classical `θ_m`); its core lemma is `private`.  The
    big-bound estimate
block has no `θ_m`, so the core lemma is reproduced here and produces the profile in the
    `OnA7Instances` block with a free
profile constant `Cs ≥ 8 max(r(c), 2)`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5
  AVenhance.Infra.Section5.Integration

theorem SourceErrorDTheta.sed_iterateSpatialWord_eq_classicalWordDerivative
    (w : List (Fin 2)) (f : Vec 2 → ℝ) :
    iterateSpatialWord w f = classicalWordDerivative w f := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [iterateSpatialWord, classicalWordDerivative,
    Classical.classicalWordDerivative, ih]

theorem SourceErrorDTheta.sed_theta_profile_of_explicit_A3_A5
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
            SourceErrorDTheta.sed_iterateSpatialWord_eq_classicalWordDerivative] using hsp
        rw [hnorm]
        simp [iterateAnalyticWeight]
      · intro w
        have hg := theta_zero_word_spacetime_gradient_energy_eq_zero hφ hκprev hsolzero w
        have hgrad : spaceTimeGradNormSq
            (fun t => spaceGrad (iterateSpatialWord w (θprev t))) = 0 := by
          simpa [thetaWordSpaceTimeGradientEnergy, spaceTimeGradNormSq,
            SourceErrorDTheta.sed_iterateSpatialWord_eq_classicalWordDerivative] using hg
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

/-- The θ profile at amplitude `2‖θ₀‖` in the big-bound premise block, for every profile constant
`Cs ≥ Cθ` (`Cθ` depends only on `β, C₀`). -/
theorem sed_thetaProfile_A7 (β C₀ : ℝ) :
    ∃ Cθ : ℝ, ∀ Cs : ℝ, Cθ ≤ Cs →
      OnA7Instances β C₀ 0 (fun I _Φ _hΦ κ M _R θ₀ m θprev _T =>
        ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs
          (2 * Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨c, C, hc, hcC, hrec⟩ := AVenhance.l_recurse β C₀
  obtain ⟨_, _, hstream⟩ := AVenhance.stream_regularity β
  refine ⟨8 * max (thetaAnalyticRadiusBase c) 2, ?_⟩
  intro Cs hCs I hCzeta hCxi hChat hC₁ Φ hΦ κ hpermissible M hM hPerm Rr hR θ₀ hθ₀smooth
    hθ₀per hmean hanalytic m hm0 hmM θprev _T hθprev hT
  have hm : 2 ≤ m := by
    exact (mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR).1.trans hm0
  have hscale : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rr := by
    have hstar := mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR
    have hmono : epsilon β I.Λ (m - 1) ≤ epsilon β I.Λ (mTheta0 β I.Λ Rr - 1) :=
      AVenhance.Infra.Section5.RelativeError.epsilon_antitone
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (by omega)
    have hexp : 0 ≤ 1 + gamma β / 2 := by
      have hγ := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
      linarith
    exact (Real.rpow_le_rpow
      (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
      hmono hexp).trans hstar.2
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
  have hprofile := SourceErrorDTheta.sed_theta_profile_of_explicit_A3_A5 I hΦ hm hmM (κ := κ) (R
      := Rr)
    (θ₀ := θ₀) (θprev := θprev) hR hscale hanalytic hθprev hc hcC hCs hA3 hA5
  simpa [ThetaProfileContract] using hprofile

end AVenhance.Infra.Section5.Contracts

end
