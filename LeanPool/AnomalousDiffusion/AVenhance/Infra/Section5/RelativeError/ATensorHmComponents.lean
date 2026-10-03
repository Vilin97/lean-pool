/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Params

/-! # Open-time `HTilde_m` gradient: componentwise estimates

Copies of the `HmBounds` gradient lemmas in which the spatial differentiability premises are
required only for `t > 0` (the iterates' `Amnr` recursion reads the arbitrary negative-time
extension of `T` at `t ≤ 0`).  The pointwise `funext` identities become a.e. identities with
respect to a measure carried on `{z | 0 < z.1}`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section4

/-- Differentiate the exact `Hmr` expansion once more in space.  This
is the source identity behind the `(k,ell)=(2,0)` instance of `p.Amnr`. -/
theorem hmr_spaceGrad_eq_second_spatial_derivative_sum_at {β : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    (t : ℝ)
    (hD1 : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2, ∀ x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => I.Amnr hΦ m κ n T r t y i j k) x)
    (hD2 : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2, ∀ x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => AVenhance.spaceGrad
            (fun x => I.Amnr hΦ m κ n T r t x i j k) y i) x)
    (x : Vec 2) (p : Fin 2) :
    AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r t x) x p =
      ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
        ∑ j : Fin 2, ∑ k : Fin 2,
          AVenhance.spaceGrad
            (fun y => AVenhance.spaceGrad
              (fun x => I.Amnr hΦ m κ n T r t x i j k) y i) x p *
            I.qMNR κ m n (r + 1) t j k := by
  classical
  have hfun : (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) =
      fun y => ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
        ∑ j : Fin 2, ∑ k : Fin 2,
          AVenhance.spaceGrad
            (fun x => I.Amnr hΦ m κ n T r t x i j k) y i *
              I.qMNR κ m n (r + 1) t j k := by
    funext y
    exact hmr_eq_spatial_derivative_sum I hΦ m κ T r t y
      (fun n hn i j k => hD1 n hn i j k y)
  have hKDiff (i : Fin 2) (n : ℕ)
      (hn : n ∈ Finset.range (AVenhance.Nstar β)) (j k : Fin 2) :
      DifferentiableAt ℝ (fun y : Vec 2 =>
        AVenhance.spaceGrad
          (fun x => I.Amnr hΦ m κ n T r t x i j k) y i *
            I.qMNR κ m n (r + 1) t j k) x :=
    (hD2 n hn i j k x).mul_const _
  have hJDiff (i : Fin 2) (n : ℕ)
      (hn : n ∈ Finset.range (AVenhance.Nstar β)) (j : Fin 2) :
      DifferentiableAt ℝ (fun y : Vec 2 =>
        ∑ k : Fin 2,
          AVenhance.spaceGrad
            (fun x => I.Amnr hΦ m κ n T r t x i j k) y i *
              I.qMNR κ m n (r + 1) t j k) x := by
    apply DifferentiableAt.fun_sum
    intro k _
    exact hKDiff i n hn j k
  have hNDiff (i : Fin 2) (n : ℕ)
      (hn : n ∈ Finset.range (AVenhance.Nstar β)) :
      DifferentiableAt ℝ (fun y : Vec 2 =>
        ∑ j : Fin 2, ∑ k : Fin 2,
          AVenhance.spaceGrad
            (fun x => I.Amnr hΦ m κ n T r t x i j k) y i *
              I.qMNR κ m n (r + 1) t j k) x := by
    apply DifferentiableAt.fun_sum
    intro j _
    exact hJDiff i n hn j
  have hIDiff (i : Fin 2) :
      DifferentiableAt ℝ (fun y : Vec 2 =>
        ∑ n ∈ Finset.range (AVenhance.Nstar β),
          ∑ j : Fin 2, ∑ k : Fin 2,
            AVenhance.spaceGrad
              (fun x => I.Amnr hΦ m κ n T r t x i j k) y i *
                I.qMNR κ m n (r + 1) t j k) x := by
    apply DifferentiableAt.fun_sum
    intro n hn
    exact hNDiff i n hn
  change fderiv ℝ (fun y => I.Hmr hΦ m κ T r t y) x
      (Homogenization.basisVec p) = _
  rw [hfun]
  rw [fderiv_fun_sum (fun i _ => hIDiff i), sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_sum (hNDiff i), sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fderiv_fun_sum (fun j _ => hJDiff i n hn j), sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_sum (fun k _ => hKDiff i n hn j k), sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_mul_const (hD2 n hn i j k x)
    (I.qMNR κ m n (r + 1) t j k)]
  simp [AVenhance.spaceGrad]
  ring

/-- Each output component of the gradient is bounded by the finite
`(i,n,j,k)` sum supplied by the `(k,ell)=(2,0)` AMNR estimate. -/
theorem hmr_spaceGrad_components_eLpNorm_le_of_pAmnr_qMNR_Ioi {β C₀ A : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    {μ : Measure (ℝ × Vec 2)} (hμ : ∀ᵐ z ∂μ, 0 < z.1)
    (hcutoff : I.Czeta ≤ C₀) (hm : 1 ≤ m) (hκ : 0 < κ)
    (hA : 0 ≤ A)
    (hratio : AVenhance.epsilon β I.Λ m ^ 2 /
      (κ * AVenhance.tau β I.Λ m) ≤ 1)
    (hAmnrHess : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      eLpNorm (amnrSpatialDivergenceGradientTensor I hΦ m κ T n r) 2 μ ≤
        ENNReal.ofReal A)
    (hHessEntryMeas : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k p : Fin 2,
        AEStronglyMeasurable
          (fun z : ℝ × Vec 2 => amnrSpatialDivergenceGradientTensor
            I hΦ m κ T n r z i j k p) μ)
    (hD1 : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2, ∀ t, 0 < t → ∀ x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => I.Amnr hΦ m κ n T r t y i j k) x)
    (hD2 : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2, ∀ t, 0 < t → ∀ x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => AVenhance.spaceGrad
            (fun x => I.Amnr hΦ m κ n T r t x i j k) y i) x) :
    ∀ p : Fin 2, eLpNorm (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2 p) 2 μ ≤
      8 * (AVenhance.Nstar β : ENNReal) *
        ENNReal.ofReal (hmrGradientQbase I C₀ m r * A) := by
  let R := AVenhance.epsilon β I.Λ m ^ 2 /
    (κ * AVenhance.tau β I.Λ m)
  let Q (n : ℕ) := (4 * Real.pi ^ 2 * C₀) *
    (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 2) *
    R ^ n * (8 * AVenhance.tau β I.Λ m) ^ (r + 1)
  let Qbase := hmrGradientQbase I C₀ m r
  have hτ := I.tau_pos' m
  have hε := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have ha := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hQbase0 : 0 ≤ Qbase := by
    dsimp [Qbase, hmrGradientQbase]
    have hC₀ : 0 ≤ C₀ := by linarith [I.one_le_Czeta, hcutoff]
    positivity
  have hqmatrix (n : ℕ) (hn : n ∈ Finset.range (AVenhance.Nstar β)) (t : ℝ) :
      ‖I.qMNR κ m n (r + 1) t‖ ≤ Q n := by
    have hnle : n ≤ AVenhance.Nstar β := by
      have hn' := Finset.mem_range.mp hn
      omega
    have hbound := AVenhance.Infra.Section3.qMNR_norm_paper_bound I hcutoff hm hκ
      hnle (r + 1) t
    simpa only [Q, R, Nat.succ_eq_add_one] using hbound
  have hQ0 (n : ℕ) (hn : n ∈ Finset.range (AVenhance.Nstar β)) :
      0 ≤ Q n := le_trans (norm_nonneg _) (hqmatrix n hn 0)
  have hqentry (n : ℕ) (hn : n ∈ Finset.range (AVenhance.Nstar β))
      (t : ℝ) (j k : Fin 2) : |I.qMNR κ m n (r + 1) t j k| ≤ Q n := by
    have hrow : ‖I.qMNR κ m n (r + 1) t j‖ ≤
        ‖I.qMNR κ m n (r + 1) t‖ :=
      norm_le_pi_norm (I.qMNR κ m n (r + 1) t) j
    have hentry : |I.qMNR κ m n (r + 1) t j k| ≤
        ‖I.qMNR κ m n (r + 1) t j‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm
        (I.qMNR κ m n (r + 1) t j) k
    exact hentry.trans (hrow.trans (hqmatrix n hn t))
  have hQle (n : ℕ) (hn : n ∈ Finset.range (AVenhance.Nstar β)) :
      Q n ≤ Qbase := by
    have hpow : R ^ n ≤ 1 := pow_le_one₀ hR0 hratio
    calc
      Q n = Qbase * R ^ n := by
        dsimp [Q, Qbase, hmrGradientQbase]
        ring
      _ ≤ Qbase * 1 := mul_le_mul_of_nonneg_left hpow hQbase0
      _ = Qbase := by ring
  have hHessEntryLp (n : ℕ) (hn : n ∈ Finset.range (AVenhance.Nstar β))
      (i j k p : Fin 2) :
      eLpNorm (fun z : ℝ × Vec 2 => amnrSpatialDivergenceGradientTensor
        I hΦ m κ T n r z i j k p) 2 μ ≤ ENNReal.ofReal A := by
    have hmono := eLpNorm_mono_ae (hHessEntryMeas n hn i j k p)
      (Filter.Eventually.of_forall fun z => by
        have h1 : ‖amnrSpatialDivergenceGradientTensor
            I hΦ m κ T n r z i j k p‖ ≤
            ‖amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k‖ :=
          norm_le_pi_norm _ _
        have h2 : ‖amnrSpatialDivergenceGradientTensor
            I hΦ m κ T n r z i j k‖ ≤
            ‖amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j‖ :=
          norm_le_pi_norm _ _
        have h3 : ‖amnrSpatialDivergenceGradientTensor
            I hΦ m κ T n r z i j‖ ≤
            ‖amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i‖ :=
          norm_le_pi_norm _ _
        have h4 : ‖amnrSpatialDivergenceGradientTensor
            I hΦ m κ T n r z i‖ ≤
            ‖amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z‖ :=
          norm_le_pi_norm _ _
        exact h1.trans (h2.trans (h3.trans h4))) (p := 2)
    exact hmono.trans (hAmnrHess n hn)
  have hprod (n : ℕ) (hn : n ∈ Finset.range (AVenhance.Nstar β))
      (i j k p : Fin 2) :
      eLpNorm (fun z : ℝ × Vec 2 =>
        amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p *
          I.qMNR κ m n (r + 1) z.1 j k) 2 μ ≤ ENNReal.ofReal (Qbase * A) := by
    have hqmeas : AEStronglyMeasurable
        (fun z : ℝ × Vec 2 => I.qMNR κ m n (r + 1) z.1 j k) μ := by
      have hc := AVenhance.Infra.Section3.qMNR_entry_continuous I κ m n (r + 1) j k
      exact (hc.comp continuous_fst).aestronglyMeasurable
    have hprod' := eLpNorm_mul_right_le_of_abs_bound (hQ0 n hn)
      (hHessEntryMeas n hn i j k p) hqmeas
      (fun z => hqentry n hn z.1 j k) (hHessEntryLp n hn i j k p)
    exact hprod'.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hQle n hn) hA))
  have hcomponentEq (p : Fin 2) :
      (fun z : ℝ × Vec 2 =>
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2 p) =ᵐ[μ]
      ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
        ∑ j : Fin 2, ∑ k : Fin 2,
          fun z : ℝ × Vec 2 =>
            amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p *
              I.qMNR κ m n (r + 1) z.1 j k := by
    filter_upwards [hμ] with z hz
    simpa [amnrSpatialDivergenceGradientTensor, Finset.sum_apply] using
      hmr_spaceGrad_eq_second_spatial_derivative_sum_at I hΦ m κ T r z.1
        (fun n hn i j k x => hD1 n hn i j k z.1 hz x)
        (fun n hn i j k x => hD2 n hn i j k z.1 hz x) z.2 p
  have hcomponentLp (p : Fin 2) :
      eLpNorm (fun z : ℝ × Vec 2 =>
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2 p) 2 μ ≤
        8 * (AVenhance.Nstar β : ENNReal) * ENNReal.ofReal (Qbase * A) := by
    rw [eLpNorm_congr_ae (hcomponentEq p)]
    calc
      eLpNorm (∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
          ∑ j : Fin 2, ∑ k : Fin 2,
            fun z : ℝ × Vec 2 =>
              amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p *
                I.qMNR κ m n (r + 1) z.1 j k) 2 μ
        ≤ ∑ i : Fin 2, eLpNorm (∑ n ∈ Finset.range (AVenhance.Nstar β),
            ∑ j : Fin 2, ∑ k : Fin 2,
              fun z : ℝ × Vec 2 =>
                amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p *
                  I.qMNR κ m n (r + 1) z.1 j k) 2 μ :=
          eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
      _ ≤ ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
            eLpNorm (∑ j : Fin 2, ∑ k : Fin 2,
              fun z : ℝ × Vec 2 =>
                amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p *
                  I.qMNR κ m n (r + 1) z.1 j k) 2 μ := by
          apply Finset.sum_le_sum
          intro i _
          exact eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
      _ ≤ ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
            ∑ j : Fin 2, eLpNorm (∑ k : Fin 2,
              fun z : ℝ × Vec 2 =>
                amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p *
                  I.qMNR κ m n (r + 1) z.1 j k) 2 μ := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro n _
          exact eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
      _ ≤ ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
            ∑ j : Fin 2, ∑ k : Fin 2,
              eLpNorm (fun z : ℝ × Vec 2 =>
                amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p *
                  I.qMNR κ m n (r + 1) z.1 j k) 2 μ := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro n _
          apply Finset.sum_le_sum
          intro j _
          exact eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
      _ ≤ ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
            ∑ j : Fin 2, ∑ k : Fin 2, ENNReal.ofReal (Qbase * A) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro n hn
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro k _
          exact hprod n hn i j k p
      _ = 8 * (AVenhance.Nstar β : ENNReal) * ENNReal.ofReal (Qbase * A) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            Finset.card_range, nsmul_eq_mul]
          ring
  simpa only [Qbase] using hcomponentLp

/-- Open-time vector-valued `∇Hmr` bound from the AMNR tensor bound. -/
theorem hmr_spaceGrad_eLpNorm_le_of_pAmnr_qMNR_Ioi {β C₀ A : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    {μ : Measure (ℝ × Vec 2)} (hμ : ∀ᵐ z ∂μ, 0 < z.1)
    (hcutoff : I.Czeta ≤ C₀) (hm : 1 ≤ m) (hκ : 0 < κ)
    (hA : 0 ≤ A)
    (hratio : AVenhance.epsilon β I.Λ m ^ 2 /
      (κ * AVenhance.tau β I.Λ m) ≤ 1)
    (hAmnrHess : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      eLpNorm (amnrSpatialDivergenceGradientTensor I hΦ m κ T n r) 2 μ ≤
        ENNReal.ofReal A)
    (hHessEntryMeas : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k p : Fin 2,
        AEStronglyMeasurable
          (fun z : ℝ × Vec 2 => amnrSpatialDivergenceGradientTensor
            I hΦ m κ T n r z i j k p) μ)
    (hGradientMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 =>
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) μ)
    (hD1 : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2, ∀ t, 0 < t → ∀ x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => I.Amnr hΦ m κ n T r t y i j k) x)
    (hD2 : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2, ∀ t, 0 < t → ∀ x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => AVenhance.spaceGrad
            (fun x => I.Amnr hΦ m κ n T r t x i j k) y i) x) :
    eLpNorm (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2 μ ≤
      ENNReal.ofReal
        (16 * (AVenhance.Nstar β : ℝ) * A *
          hmrGradientQbase I C₀ m r) := by
  have hcomponents := hmr_spaceGrad_components_eLpNorm_le_of_pAmnr_qMNR_Ioi
    I hΦ m κ T r hμ hcutoff hm hκ hA hratio hAmnrHess hHessEntryMeas hD1 hD2
  exact hmr_spaceGrad_eLpNorm_le_of_componentBounds
    I hΦ m κ T r hGradientMeas hcomponents

/-- Differentiation in `x` commutes with the finite `Hm` sum. -/
theorem hm_spaceGrad_eq_sum_hmr_at {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ)
    (hD : ∀ r ∈ Finset.range (AVenhance.Jcut β), ∀ x,
      DifferentiableAt ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x) :
    AVenhance.spaceGrad (fun x => I.Hm hΦ m κ T t x) =
      ∑ r ∈ Finset.range (AVenhance.Jcut β),
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r t x) := by
  funext x i
  have hsum' : HasFDerivAt
      (∑ r ∈ Finset.range (AVenhance.Jcut β),
        fun y : Vec 2 => I.Hmr hΦ m κ T r t y)
      (∑ r ∈ Finset.range (AVenhance.Jcut β),
        fderiv ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x) x :=
    HasFDerivAt.sum (fun r hr => (hD r hr x).hasFDerivAt)
  have hsum : HasFDerivAt
      (fun y : Vec 2 =>
        ∑ r ∈ Finset.range (AVenhance.Jcut β), I.Hmr hΦ m κ T r t y)
      (∑ r ∈ Finset.range (AVenhance.Jcut β),
        fderiv ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x) x := by
    convert hsum' using 1
    · funext y
      simp
  have hfd : fderiv ℝ (fun y : Vec 2 => I.Hm hΦ m κ T t y) x =
      ∑ r ∈ Finset.range (AVenhance.Jcut β),
        fderiv ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x := by
    simpa only [AVenhance.Ingredients.Hm] using hsum.fderiv
  change fderiv ℝ (fun x => I.Hm hΦ m κ T t x) x
      (Homogenization.basisVec i) = _
  rw [hfd]
  simp [AVenhance.spaceGrad]

/-- Open-time sum over `r < Jcut β` of the termwise `∇Hmr` bounds. -/
theorem hm_gradient_eLpNorm_le_sum_of_hmr_Ioi {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    {μ : Measure (ℝ × Vec 2)} (hμ : ∀ᵐ z ∂μ, 0 < z.1)
    (hD : ∀ r ∈ Finset.range (Jcut β), ∀ t, 0 < t → ∀ x,
      DifferentiableAt ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x)
    {B : ℕ → ℝ} (hB : ∀ r, 0 ≤ B r)
    (hterm : ∀ r ∈ Finset.range (Jcut β),
      eLpNorm (fun z : ℝ × Vec 2 =>
        spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2 μ ≤ ENNReal.ofReal (B r)) :
    eLpNorm (fun z : ℝ × Vec 2 =>
      spaceGrad (fun x => I.Hm hΦ m κ T z.1 x) z.2) 2 μ ≤
      ENNReal.ofReal (∑ r ∈ Finset.range (Jcut β), B r) := by
  have hfun : (fun z : ℝ × Vec 2 =>
      spaceGrad (fun x => I.Hm hΦ m κ T z.1 x) z.2) =ᵐ[μ]
      ∑ r ∈ Finset.range (Jcut β),
        fun z : ℝ × Vec 2 => spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2 := by
    filter_upwards [hμ] with z hz
    have hh := hm_spaceGrad_eq_sum_hmr_at I hΦ m κ T z.1
      (fun r hr x => hD r hr z.1 hz x)
    simpa using congrArg (fun g : Vec 2 → Vec 2 => g z.2) hh
  rw [eLpNorm_congr_ae hfun]
  calc
    eLpNorm (∑ r ∈ Finset.range (Jcut β),
        fun z : ℝ × Vec 2 => spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2 μ
      ≤ ∑ r ∈ Finset.range (Jcut β),
          eLpNorm (fun z : ℝ × Vec 2 =>
            spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2 μ :=
        eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
    _ ≤ ∑ r ∈ Finset.range (Jcut β), ENNReal.ofReal (B r) :=
      Finset.sum_le_sum fun r hr => hterm r hr
    _ = ENNReal.ofReal (∑ r ∈ Finset.range (Jcut β), B r) :=
      (ENNReal.ofReal_sum_of_nonneg fun r _ => hB r).symm

end AVenhance.Infra.Section5.RelativeError
