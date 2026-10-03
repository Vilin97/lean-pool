/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Hm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Params
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.Approx
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.DmBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FlowIntegral
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Source-scale reduction for the `HTilde_m`.  The cutoff is exactly
`range (Jcut β)`, as fixed by the corrected index conventions.  The analytic term estimates are kept
separate from the finite-sum and differentiation arguments below. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section4

/-- Absorption step in the source's flow FTC argument: a nonnegative
supremum satisfying `H² ≤ 2 L D H` is bounded by `2 L D`. -/
theorem hm_transport_absorb {H L D : ℝ} (hH : 0 < H)
    (htransport : H ^ 2 ≤ 2 * L * D * H) : H ≤ 2 * L * D := by
  have hdiv := div_le_div_of_nonneg_right htransport (le_of_lt hH)
  have hleft : H ^ 2 / H = H := by field_simp [hH.ne']
  have hright : (2 * L * D * H) / H = 2 * L * D := by field_simp [hH.ne']
  rw [hleft, hright] at hdiv
  exact hdiv

/-- Cellwise conclusion of the source's transported-energy FTC estimate.
`hFTC` is the inequality obtained after the flow change of variables,
Cauchy--Schwarz in time, and the source derivative bound; this lemma performs
the supremum absorption and then bounds every time in the cell. -/
theorem hm_transport_cell_sup_le {f : ℝ → ℝ} {cell : Set ℝ} {H L D : ℝ}
    (hH : 0 < H) (hattain : ∃ t ∈ cell, f t = H)
    (hupper : ∀ t ∈ cell, f t ≤ H)
    (hFTC : ∀ t ∈ cell, f t ^ 2 ≤ 2 * L * D * H) :
    ∀ t ∈ cell, f t ≤ 2 * L * D := by
  obtain ⟨t₀, ht₀, hf₀⟩ := hattain
  have habsorb := hm_transport_absorb hH (by simpa only [hf₀] using hFTC t₀ ht₀)
  intro t ht
  exact (hupper t ht).trans habsorb

/-- Expand the divergence defining `Hmr` into the finite sum of
spatial derivatives of `Amnr` times the time-only `qMNR` entries. -/
theorem hmr_eq_spatial_derivative_sum {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    (t : ℝ) (x : Vec 2)
    (hDtx : ∀ n ∈ Finset.range (AVenhance.Nstar β), ∀ i j k : Fin 2,
      DifferentiableAt ℝ
        (fun y : Vec 2 => I.Amnr hΦ m κ n T r t y i j k) x) :
    I.Hmr hΦ m κ T r t x =
      ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
        ∑ j : Fin 2, ∑ k : Fin 2,
          AVenhance.spaceGrad
            (fun y => I.Amnr hΦ m κ n T r t y i j k) x i *
              I.qMNR κ m n (r + 1) t j k := by
  classical
  unfold AVenhance.Ingredients.Hmr AVenhance.vecDiv
  change (∑ i : Fin 2,
      fderiv ℝ (fun y : Vec 2 =>
        ∑ n ∈ Finset.range (AVenhance.Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
          I.Amnr hΦ m κ n T r t y i j k * I.qMNR κ m n (r + 1) t j k)
        x (Homogenization.basisVec i)) = _
  apply Finset.sum_congr rfl
  intro i _
  have hNDiff : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      DifferentiableAt ℝ (fun y : Vec 2 =>
        ∑ j : Fin 2, ∑ k : Fin 2,
          I.Amnr hΦ m κ n T r t y i j k * I.qMNR κ m n (r + 1) t j k) x := by
    intro n hn
    apply DifferentiableAt.fun_sum
    intro j _
    apply DifferentiableAt.fun_sum
    intro k _
    exact (hDtx n hn i j k).mul_const _
  rw [fderiv_fun_sum hNDiff, sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have hJDiff : ∀ j ∈ (Finset.univ : Finset (Fin 2)),
      DifferentiableAt ℝ (fun y : Vec 2 =>
        ∑ k : Fin 2,
          I.Amnr hΦ m κ n T r t y i j k * I.qMNR κ m n (r + 1) t j k) x := by
    intro j _
    apply DifferentiableAt.fun_sum
    intro k _
    exact (hDtx n hn i j k).mul_const _
  rw [fderiv_fun_sum hJDiff, sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_sum (fun k _ => (hDtx n hn i j k).mul_const _),
    sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_mul_const (hDtx n hn i j k) (I.qMNR κ m n (r + 1) t j k)]
  simp [AVenhance.spaceGrad, mul_comm]

/-- The mixed second spatial derivative of `Amnr` selected by the divergence
index of `Hmr`. -/
def amnrSpatialDivergenceGradientTensor {β : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (n r : ℕ)
    (z : ℝ × Vec 2) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun i j k p => AVenhance.spaceGrad
    (fun y => AVenhance.spaceGrad
      (fun x => I.Amnr hΦ m κ n T r z.1 x i j k) y i) z.2 p

/-- Common paper-scale factor in the corrected qMNR estimate. -/
def hmrGradientQbase {β : ℝ} (I : AVenhance.Ingredients β)
    (C₀ : ℝ) (m r : ℕ) : ℝ :=
  (4 * Real.pi ^ 2 * C₀) *
    (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 2) *
    (8 * AVenhance.tau β I.Λ m) ^ (r + 1)

/-- Differentiate the exact `Hmr` expansion once more in space.  This
is the source identity behind the `(k,ell)=(2,0)` instance of `p.Amnr`. -/
theorem hmr_spaceGrad_eq_second_spatial_derivative_sum {β : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    (hD1 : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2, ∀ t x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => I.Amnr hΦ m κ n T r t y i j k) x)
    (hD2 : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2, ∀ t x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => AVenhance.spaceGrad
            (fun x => I.Amnr hΦ m κ n T r t x i j k) y i) x)
    (t : ℝ) (x : Vec 2) (p : Fin 2) :
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
      (fun n hn i j k => hD1 n hn i j k t y)
  have hKDiff (i : Fin 2) (n : ℕ)
      (hn : n ∈ Finset.range (AVenhance.Nstar β)) (j k : Fin 2) :
      DifferentiableAt ℝ (fun y : Vec 2 =>
        AVenhance.spaceGrad
          (fun x => I.Amnr hΦ m κ n T r t x i j k) y i *
            I.qMNR κ m n (r + 1) t j k) x :=
    (hD2 n hn i j k t x).mul_const _
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
  rw [fderiv_mul_const (hD2 n hn i j k t x)
    (I.qMNR κ m n (r + 1) t j k)]
  simp [AVenhance.spaceGrad]
  ring

/-- Each output component of the gradient is bounded by the finite
`(i,n,j,k)` sum supplied by the `(k,ell)=(2,0)` AMNR estimate. -/
theorem hmr_spaceGrad_components_eLpNorm_le_of_pAmnr_qMNR {β C₀ A : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    {μ : Measure (ℝ × Vec 2)}
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
      ∀ i j k : Fin 2, ∀ t x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => I.Amnr hΦ m κ n T r t y i j k) x)
    (hD2 : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2, ∀ t x,
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
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2 p) =
      ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
        ∑ j : Fin 2, ∑ k : Fin 2,
          fun z : ℝ × Vec 2 =>
            amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p *
              I.qMNR κ m n (r + 1) z.1 j k := by
    funext z
    simpa [amnrSpatialDivergenceGradientTensor, Finset.sum_apply] using
      hmr_spaceGrad_eq_second_spatial_derivative_sum I hΦ m κ T r
        hD1 hD2 z.1 z.2 p
  have hcomponentLp (p : Fin 2) :
      eLpNorm (fun z : ℝ × Vec 2 =>
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2 p) 2 μ ≤
        8 * (AVenhance.Nstar β : ENNReal) * ENNReal.ofReal (Qbase * A) := by
    rw [hcomponentEq p]
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

/-- Pointwise coordinate dominance gives this vector-valued L² comparison. -/
theorem eLpNorm_vec2_le_sum {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : α → Vec 2) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ≤ eLpNorm (fun x => ∑ p : Fin 2, ‖f x p‖) 2 μ := by
  have hpoint (x : α) : ‖f x‖ ≤ ∑ p : Fin 2, ‖f x p‖ := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun p _ => norm_nonneg _)).2
    intro p
    exact Finset.single_le_sum (fun q _ => norm_nonneg _) (Finset.mem_univ p)
  apply eLpNorm_mono_ae hf
  filter_upwards with x
  calc
    ‖f x‖ ≤ ∑ p : Fin 2, ‖f x p‖ := hpoint x
    _ = ‖∑ p : Fin 2, ‖f x p‖‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (Finset.sum_nonneg fun p _ => norm_nonneg _)]

/-- The sum of coordinate norms has the corresponding L² bound. -/
theorem eLpNorm_sum_norm_vec2_le_of_coordinate_le {α : Type*}
    [MeasurableSpace α] {μ : Measure α} (f : α → Vec 2)
    (hf : AEStronglyMeasurable f μ) {B : ENNReal}
    (hcoordinate : ∀ p : Fin 2, eLpNorm (fun x => f x p) 2 μ ≤ B) :
    eLpNorm (fun x => ∑ p : Fin 2, ‖f x p‖) 2 μ ≤ 2 * B := by
  have hfEntry (p : Fin 2) : AEStronglyMeasurable (fun x => f x p) μ :=
    (continuous_apply p).comp_aestronglyMeasurable hf
  calc
    eLpNorm (fun x => ∑ p : Fin 2, ‖f x p‖) 2 μ
      ≤ ∑ p : Fin 2, eLpNorm (fun x => ‖f x p‖) 2 μ :=
        eLpNorm_sum_le (α := α) (μ := μ) (p := 2)
          (f := fun p x => ‖f x p‖) (s := Finset.univ)
          (by norm_num : (1 : ENNReal) ≤ 2)
    _ = ∑ p : Fin 2, eLpNorm (fun x => f x p) 2 μ := by
      apply Finset.sum_congr rfl
      intro p _
      exact eLpNorm_norm _ (hfEntry p)
    _ ≤ ∑ p : Fin 2, B := Finset.sum_le_sum fun p _ => hcoordinate p
    _ = 2 * B := by simp

/-- The vector-valued L² norm is controlled by its two coordinate bounds. -/
theorem eLpNorm_vec2_le_of_coordinate_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : α → Vec 2) (hf : AEStronglyMeasurable f μ)
    {B : ENNReal}
    (hcoordinate : ∀ p : Fin 2, eLpNorm (fun x => f x p) 2 μ ≤ B) :
    eLpNorm f 2 μ ≤ 2 * B := by
  calc
    eLpNorm f 2 μ ≤ eLpNorm (fun x => ∑ p : Fin 2, ‖f x p‖) 2 μ :=
      eLpNorm_vec2_le_sum f hf
    _ ≤ 2 * B := eLpNorm_sum_norm_vec2_le_of_coordinate_le f hf hcoordinate

/-- Convert the finite component count in the previous lemma to the paper's
real-valued scale. -/
theorem hmr_component_count_identity (N : ℕ) (x y : ℝ) :
    2 * (8 * (N : ENNReal) * ENNReal.ofReal (x * y)) =
      ENNReal.ofReal (16 * (N : ℝ) * y * x) := by
  have hN : (N : ENNReal) = ENNReal.ofReal (N : ℝ) := by norm_num
  rw [hN]
  calc
    2 * (8 * ENNReal.ofReal (N : ℝ) * ENNReal.ofReal (x * y)) =
        (2 * 8) * ENNReal.ofReal (N : ℝ) * ENNReal.ofReal (x * y) := by ring
    _ = ENNReal.ofReal 16 * ENNReal.ofReal (N : ℝ) *
        ENNReal.ofReal (x * y) := by norm_num
    _ = ENNReal.ofReal (16 * (N : ℝ)) * ENNReal.ofReal (x * y) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
    _ = ENNReal.ofReal (16 * (N : ℝ) * (x * y)) := by
      rw [← ENNReal.ofReal_mul (by positivity :
        (0 : ℝ) ≤ 16 * (N : ℝ))]
    _ = ENNReal.ofReal (16 * (N : ℝ) * y * x) := by
      congr 1
      ring

/-- Assemble the two component estimates into the vector-valued `∇Hmr` estimate. -/
theorem hmr_spaceGrad_eLpNorm_le_of_componentBounds {β C₀ A : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    {μ : Measure (ℝ × Vec 2)}
    (hGradientMeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 =>
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) μ)
    (hComponentBound : ∀ p : Fin 2, eLpNorm (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2 p) 2 μ ≤
      8 * (AVenhance.Nstar β : ENNReal) *
        ENNReal.ofReal (hmrGradientQbase I C₀ m r * A)) :
    eLpNorm (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2 μ ≤
      ENNReal.ofReal
        (16 * (AVenhance.Nstar β : ℝ) * A * hmrGradientQbase I C₀ m r) := by
  calc
    eLpNorm (fun z : ℝ × Vec 2 =>
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2 μ
      ≤ 2 * (8 * (AVenhance.Nstar β : ENNReal) *
          ENNReal.ofReal (hmrGradientQbase I C₀ m r * A)) :=
        eLpNorm_vec2_le_of_coordinate_le _ hGradientMeas hComponentBound
    _ = ENNReal.ofReal
          (16 * (AVenhance.Nstar β : ℝ) * A * hmrGradientQbase I C₀ m r) :=
        hmr_component_count_identity (AVenhance.Nstar β)
          (hmrGradientQbase I C₀ m r) A

/-- Termwise spacetime L² bound for the actual gradient `∇Hmr`.
The AMNR input is the `(k,ell)=(2,0)` tensor estimate.  The corrected
qMNR norm bound controls each time-dependent coefficient, and the small
mode ratio replaces its individual `n` weight by the common upper factor. -/
theorem hmr_spaceGrad_eLpNorm_le_of_pAmnr_qMNR {β C₀ A : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    {μ : Measure (ℝ × Vec 2)}
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
      ∀ i j k : Fin 2, ∀ t x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => I.Amnr hΦ m κ n T r t y i j k) x)
    (hD2 : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2, ∀ t x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => AVenhance.spaceGrad
            (fun x => I.Amnr hΦ m κ n T r t x i j k) y i) x) :
    eLpNorm (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2 μ ≤
      ENNReal.ofReal
        (16 * (AVenhance.Nstar β : ℝ) * A *
          hmrGradientQbase I C₀ m r) := by
  have hcomponents := hmr_spaceGrad_components_eLpNorm_le_of_pAmnr_qMNR
    I hΦ m κ T r hcutoff hm hκ hA hratio hAmnrHess hHessEntryMeas hD1 hD2
  exact hmr_spaceGrad_eLpNorm_le_of_componentBounds
    I hΦ m κ T r hGradientMeas hcomponents

/-- The p.Amnr tensor bound controls each scalar spatial derivative entry. -/
def amnrSpatialGradientTensor {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (n r : ℕ)
    (z : ℝ × Vec 2) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun i j k p => AVenhance.spaceGrad
    (fun x => I.Amnr hΦ m κ n T r z.1 x i j k) z.2 p

/-- Differentiation in `x` commutes with the finite `Hm` sum. -/
theorem hm_spaceGrad_eq_sum_hmr {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (hD : ∀ r ∈ Finset.range (AVenhance.Jcut β), ∀ t x,
      DifferentiableAt ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x)
    (t : ℝ) :
    AVenhance.spaceGrad (fun x => I.Hm hΦ m κ T t x) =
      ∑ r ∈ Finset.range (AVenhance.Jcut β),
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r t x) := by
  funext x i
  have hsum' : HasFDerivAt
      (∑ r ∈ Finset.range (AVenhance.Jcut β),
        fun y : Vec 2 => I.Hmr hΦ m κ T r t y)
      (∑ r ∈ Finset.range (AVenhance.Jcut β),
        fderiv ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x) x :=
    HasFDerivAt.sum (fun r hr => (hD r hr t x).hasFDerivAt)
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

/-- The gradient L² bound for `Hm` reduces to the corresponding
termwise source-scale estimates at indices `r < Jcut`. -/
theorem hm_gradient_eLpNorm_le_of_hmr {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (hD : ∀ r ∈ Finset.range (AVenhance.Jcut β), ∀ t x,
      DifferentiableAt ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x)
    {B : ℝ} (hB : 0 ≤ B)
    (hterm : ∀ r ∈ Finset.range (AVenhance.Jcut β),
      eLpNorm (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2
        (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal B) :
    eLpNorm (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => I.Hm hΦ m κ T z.1 x) z.2) 2
      (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal ((AVenhance.Jcut β : ℝ) * B) := by
  have hfun : (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => I.Hm hΦ m κ T z.1 x) z.2) =
      ∑ r ∈ Finset.range (AVenhance.Jcut β),
        fun z : ℝ × Vec 2 =>
          AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2 := by
    funext z
    have hh := hm_spaceGrad_eq_sum_hmr I hΦ m κ T hD z.1
    simpa using congrArg (fun g : Vec 2 → Vec 2 => g z.2) hh
  rw [hfun]
  calc
    eLpNorm (∑ r ∈ Finset.range (AVenhance.Jcut β),
        fun z : ℝ × Vec 2 =>
          AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2
        (volume.restrict AVenhance.timeCube)
      ≤ ∑ r ∈ Finset.range (AVenhance.Jcut β),
          eLpNorm (fun z : ℝ × Vec 2 =>
            AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2
            (volume.restrict AVenhance.timeCube) :=
        eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
    _ ≤ ∑ _r ∈ Finset.range (AVenhance.Jcut β), ENNReal.ofReal B :=
      Finset.sum_le_sum fun r hr => hterm r hr
    _ = ENNReal.ofReal ((AVenhance.Jcut β : ℝ) * B) := by
      rw [Finset.sum_const, Finset.card_range]
      simp [nsmul_eq_mul, ENNReal.ofReal_mul hB, mul_comm]

/-- Source-scale form of the spacetime gradient reduction, retaining the
corrected summand range `r < Jcut`. -/
theorem hm_gradient_source_scale_of_hmr {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (hD : ∀ r ∈ Finset.range (AVenhance.Jcut β), ∀ t x,
      DifferentiableAt ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x)
    {E δ C θ Kinvhalf : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hKinv : 0 ≤ Kinvhalf)
    (hterm : ∀ r ∈ Finset.range (AVenhance.Jcut β),
      eLpNorm (fun z : ℝ × Vec 2 =>
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2
        (volume.restrict AVenhance.timeCube) ≤
          ENNReal.ofReal (C * E ^ (4 * δ) * Kinvhalf * θ)) :
    eLpNorm (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => I.Hm hΦ m κ T z.1 x) z.2) 2
      (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal
        ((AVenhance.Jcut β : ℝ) * C * E ^ (4 * δ) * Kinvhalf * θ) := by
  have hB : 0 ≤ C * E ^ (4 * δ) * Kinvhalf * θ := by positivity
  have h := hm_gradient_eLpNorm_le_of_hmr I hΦ m κ T hD hB
    (fun r hr => hterm r hr)
  simpa only [mul_assoc] using h

/-- Conditional p.Hm conclusion with the source FTC step isolated.  The
`hFTC` premise is precisely the transported squared-L² inequality on the
whole time interval; `flow_comp_hasDerivAt_of_fderiv` supplies its pointwise
material derivative once the source regularity is instantiated. -/
theorem hm_bounds_of_flowFTC_and_termwise_gradient {β : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (hD : ∀ r ∈ Finset.range (AVenhance.Jcut β), ∀ t x,
      DifferentiableAt ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x)
    {f H L D E δ C₀ C₁ θ Kinvhalf : ℝ}
    (hNorm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      eLpNorm (fun x : Vec 2 => I.Hm hΦ m κ T t x) 2
        (volume.restrict AVenhance.unitCube) = ENNReal.ofReal f)
    (hH : 0 < H)
    (hattain : ∃ t ∈ Set.Icc (0 : ℝ) 1, f = H)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) 1, f ≤ H)
    (hFTC : ∀ t ∈ Set.Icc (0 : ℝ) 1, f ^ 2 ≤ 2 * L * D * H)
    (hscale : 2 * L * D ≤ C₀ * E ^ δ * θ)
    (hE : 0 ≤ E) (hC₁ : 0 ≤ C₁) (hθ : 0 ≤ θ)
    (hKinv : 0 ≤ Kinvhalf)
    (hGradHmr : ∀ r ∈ Finset.range (AVenhance.Jcut β),
      eLpNorm (fun z : ℝ × Vec 2 =>
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2
          (volume.restrict AVenhance.timeCube) ≤
            ENNReal.ofReal (C₁ * E ^ (4 * δ) * Kinvhalf * θ)) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      eLpNorm (fun x : Vec 2 => I.Hm hΦ m κ T t x) 2
        (volume.restrict AVenhance.unitCube) ≤
          ENNReal.ofReal (C₀ * E ^ δ * θ)) ∧
    eLpNorm (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => I.Hm hΦ m κ T z.1 x) z.2) 2
        (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal
        ((AVenhance.Jcut β : ℝ) * C₁ * E ^ (4 * δ) * Kinvhalf * θ) := by
  have htransport := hm_transport_cell_sup_le hH hattain hupper hFTC
  constructor
  · intro t ht
    rw [hNorm t ht]
    exact ENNReal.ofReal_le_ofReal ((htransport t ht).trans hscale)
  · exact hm_gradient_source_scale_of_hmr I hΦ m κ T hD hE hC₁ hθ hKinv hGradHmr

/-- The p.Amnr `(k,ell)=(2,0)` bounds and corrected qMNR estimate provide
the termwise gradient input to the conditional p.Hm assembly.  The transported
FTC inequality remains an explicit premise because its endpoint and flow
measure-preservation steps are not consequences of p.Amnr alone. -/
theorem hm_bounds_of_flowFTC_and_pAmnr {β : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (hD : ∀ r ∈ Finset.range (AVenhance.Jcut β), ∀ t x,
      DifferentiableAt ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x)
    {C₀ C₁ A E δ θ Kinvhalf f H L D : ℝ}
    (hcutoff : I.Czeta ≤ C₀) (hm : 1 ≤ m) (hκ : 0 < κ)
    (hA : 0 ≤ A)
    (hratio : AVenhance.epsilon β I.Λ m ^ 2 /
      (κ * AVenhance.tau β I.Λ m) ≤ 1)
    (hAmnrHess : ∀ r ∈ Finset.range (AVenhance.Jcut β),
      ∀ n ∈ Finset.range (AVenhance.Nstar β),
        eLpNorm (amnrSpatialDivergenceGradientTensor I hΦ m κ T n r) 2
          (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal A)
    (hHessEntryMeas : ∀ r ∈ Finset.range (AVenhance.Jcut β),
      ∀ n ∈ Finset.range (AVenhance.Nstar β), ∀ i j k p : Fin 2,
        AEStronglyMeasurable
          (fun z : ℝ × Vec 2 => amnrSpatialDivergenceGradientTensor
            I hΦ m κ T n r z i j k p)
          (volume.restrict AVenhance.timeCube))
    (hGradientMeas : ∀ r ∈ Finset.range (AVenhance.Jcut β),
      AEStronglyMeasurable
        (fun z : ℝ × Vec 2 =>
          AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2)
        (volume.restrict AVenhance.timeCube))
    (hD1 : ∀ r ∈ Finset.range (AVenhance.Jcut β),
      ∀ n ∈ Finset.range (AVenhance.Nstar β),
        ∀ i j k : Fin 2, ∀ t x,
          DifferentiableAt ℝ
            (fun y : Vec 2 => I.Amnr hΦ m κ n T r t y i j k) x)
    (hD2 : ∀ r ∈ Finset.range (AVenhance.Jcut β),
      ∀ n ∈ Finset.range (AVenhance.Nstar β),
        ∀ i j k : Fin 2, ∀ t x,
          DifferentiableAt ℝ
            (fun y : Vec 2 => AVenhance.spaceGrad
              (fun x => I.Amnr hΦ m κ n T r t x i j k) y i) x)
    (hGradientScale : ∀ r ∈ Finset.range (AVenhance.Jcut β),
      16 * (AVenhance.Nstar β : ℝ) * A * hmrGradientQbase I C₀ m r ≤
        C₁ * E ^ (4 * δ) * Kinvhalf * θ)
    (hNorm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      eLpNorm (fun x : Vec 2 => I.Hm hΦ m κ T t x) 2
        (volume.restrict AVenhance.unitCube) = ENNReal.ofReal f)
    (hH : 0 < H)
    (hattain : ∃ t ∈ Set.Icc (0 : ℝ) 1, f = H)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) 1, f ≤ H)
    (hFTC : ∀ t ∈ Set.Icc (0 : ℝ) 1, f ^ 2 ≤ 2 * L * D * H)
    (hscale : 2 * L * D ≤ C₀ * E ^ δ * θ)
    (hE : 0 ≤ E) (hC₁ : 0 ≤ C₁) (hθ : 0 ≤ θ)
    (hKinv : 0 ≤ Kinvhalf) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      eLpNorm (fun x : Vec 2 => I.Hm hΦ m κ T t x) 2
        (volume.restrict AVenhance.unitCube) ≤
          ENNReal.ofReal (C₀ * E ^ δ * θ)) ∧
    eLpNorm (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => I.Hm hΦ m κ T z.1 x) z.2) 2
        (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal
        ((AVenhance.Jcut β : ℝ) * C₁ * E ^ (4 * δ) * Kinvhalf * θ) := by
  have hGradHmr : ∀ r ∈ Finset.range (AVenhance.Jcut β),
      eLpNorm (fun z : ℝ × Vec 2 =>
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2
          (volume.restrict AVenhance.timeCube) ≤
            ENNReal.ofReal (C₁ * E ^ (4 * δ) * Kinvhalf * θ) := by
    intro r hr
    have hterm := hmr_spaceGrad_eLpNorm_le_of_pAmnr_qMNR
      I hΦ m κ T r hcutoff hm hκ hA hratio (hAmnrHess r hr)
      (hHessEntryMeas r hr) (hGradientMeas r hr) (hD1 r hr) (hD2 r hr)
    exact hterm.trans (ENNReal.ofReal_le_ofReal (hGradientScale r hr))
  exact hm_bounds_of_flowFTC_and_termwise_gradient I hΦ m κ T hD hNorm hH
    hattain hupper hFTC hscale hE hC₁ hθ hKinv hGradHmr

end AVenhance.Infra.Section4
