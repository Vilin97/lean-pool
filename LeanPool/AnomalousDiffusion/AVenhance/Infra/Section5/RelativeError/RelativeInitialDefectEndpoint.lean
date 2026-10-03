/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenHmSourceIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters

/-! L2 estimate for the actual endpoint source in the Hm material telescope.
Unlike Hmr, this endpoint uses q_r (not q_{r+1}); the terminal r=Jcut needs
only one spatial derivative, within the corrected mixed budget. -/

@[expose] public section

noncomputable section
open scoped Matrix.Norms.Elementwise
open Homogenization MeasureTheory AVenhance AVenhance.Infra.Section4
open AVenhance.Infra.Section5
namespace AVenhance.Infra.Section5.RelativeError

/-- The endpoint spatial derivative fits at every correction level, including
Jcut. No two-spatial-letter estimate is consumed at the terminal level. -/
theorem relative_initial_endpoint_budget {β : ℝ} (I : Ingredients β)
    {r : ℕ} (hr : r ≤ Jcut β) : 1 ≤ Nstar β - 2 * r := by
  have hN := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
  unfold Jcut at hr
  omega

/-- Exact spatial derivative expansion of the endpoint, with q_r. -/
theorem relative_initial_endpoint_spatial_sum {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    (t : ℝ) (x : Vec 2)
    (hDtx : ∀ n ∈ Finset.range (AVenhance.Nstar β), ∀ i j k : Fin 2,
      DifferentiableAt ℝ
        (fun y : Vec 2 => I.Amnr hΦ m κ n T r t y i j k) x) :
    hmEndpoint I hΦ m κ T r t x =
      ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
        ∑ j : Fin 2, ∑ k : Fin 2,
          AVenhance.spaceGrad
            (fun y => I.Amnr hΦ m κ n T r t y i j k) x i *
              I.qMNR κ m n r t j k := by
  classical
  unfold hmEndpoint AVenhance.vecDiv
  change (∑ i : Fin 2,
      fderiv ℝ (fun y : Vec 2 =>
        ∑ n ∈ Finset.range (AVenhance.Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
          I.Amnr hΦ m κ n T r t y i j k * I.qMNR κ m n r t j k)
        x (Homogenization.basisVec i)) = _
  apply Finset.sum_congr rfl
  intro i _
  have hNDiff : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      DifferentiableAt ℝ (fun y : Vec 2 =>
        ∑ j : Fin 2, ∑ k : Fin 2,
          I.Amnr hΦ m κ n T r t y i j k * I.qMNR κ m n r t j k) x := by
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
          I.Amnr hΦ m κ n T r t y i j k * I.qMNR κ m n r t j k) x := by
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
  rw [fderiv_mul_const (hDtx n hn i j k) (I.qMNR κ m n r t j k)]
  simp [AVenhance.spaceGrad, mul_comm]

/-- The q coefficient is discharged from the physical paper-scale estimate;
the upstream AMNR gradient amplitude remains an abstract scalar. -/
theorem relative_initial_endpoint_L2_of_Amnr_gradient {β C₀ A : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    {μ : Measure (ℝ × Vec 2)}
    (hμ : μ ≪ volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hcutoff : I.Czeta ≤ C₀) (hm : 1 ≤ m) (hκ : 0 < κ)
    (hAmnrGrad : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      eLpNorm (amnrSpatialGradientTensor I hΦ m κ T n r) 2 μ ≤
        ENNReal.ofReal A)
    (hGradEntryMeas : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k p : Fin 2,
        AEStronglyMeasurable
          (fun z : ℝ × Vec 2 => AVenhance.spaceGrad
            (fun x => I.Amnr hΦ m κ n T r z.1 x i j k) z.2 p) μ)
    (hDifferentiable : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2, ∀ t, 0 < t → ∀ x,
        DifferentiableAt ℝ
          (fun y : Vec 2 => I.Amnr hΦ m κ n T r t y i j k) x) :
    eLpNorm (fun z : ℝ × Vec 2 => hmEndpoint I hΦ m κ T r z.1 z.2) 2 μ ≤
      ∑ n ∈ Finset.range (AVenhance.Nstar β),
        ENNReal.ofReal (8 *
          ((4 * Real.pi ^ 2 * C₀) *
            (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 2) *
            (AVenhance.epsilon β I.Λ m ^ 2 /
              (κ * AVenhance.tau β I.Λ m)) ^ n *
            (8 * AVenhance.tau β I.Λ m) ^ r) * A) := by
  let Q (n : ℕ) := (4 * Real.pi ^ 2 * C₀) *
    (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 2) *
    (AVenhance.epsilon β I.Λ m ^ 2 /
      (κ * AVenhance.tau β I.Λ m)) ^ n *
    (8 * AVenhance.tau β I.Λ m) ^ r
  have hqmatrix (n : ℕ) (hn : n ∈ Finset.range (AVenhance.Nstar β)) (t : ℝ) :
      ‖I.qMNR κ m n r t‖ ≤ Q n := by
    have hnle : n ≤ AVenhance.Nstar β := by
      have hn' := Finset.mem_range.mp hn
      omega
    have hbound := AVenhance.Infra.Section3.qMNR_norm_paper_bound I hcutoff hm hκ
      hnle r t
    simpa only [Q, Nat.succ_eq_add_one] using hbound
  have hQ0 (n : ℕ) (hn : n ∈ Finset.range (AVenhance.Nstar β)) :
      0 ≤ Q n := le_trans (norm_nonneg _) (hqmatrix n hn 0)
  have hqentry (n : ℕ) (hn : n ∈ Finset.range (AVenhance.Nstar β))
      (t : ℝ) (j k : Fin 2) :
      |I.qMNR κ m n r t j k| ≤ Q n := by
    have hrow : ‖I.qMNR κ m n r t j‖ ≤
        ‖I.qMNR κ m n r t‖ :=
      norm_le_pi_norm (I.qMNR κ m n r t) j
    have hentry : |I.qMNR κ m n r t j k| ≤
        ‖I.qMNR κ m n r t j‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm
        (I.qMNR κ m n r t j) k
    exact hentry.trans (hrow.trans (hqmatrix n hn t))
  have hgradEntryLp (n : ℕ) (hn : n ∈ Finset.range (AVenhance.Nstar β))
      (i j k p : Fin 2) :
      eLpNorm (fun z : ℝ × Vec 2 => AVenhance.spaceGrad
        (fun x => I.Amnr hΦ m κ n T r z.1 x i j k) z.2 p) 2 μ ≤
        ENNReal.ofReal A := by
    have hmono := eLpNorm_mono_ae (hGradEntryMeas n hn i j k p)
      (Filter.Eventually.of_forall fun z => by
        have h1 : ‖amnrSpatialGradientTensor I hΦ m κ T n r z i j k p‖ ≤
            ‖amnrSpatialGradientTensor I hΦ m κ T n r z i j k‖ :=
          norm_le_pi_norm _ _
        have h2 : ‖amnrSpatialGradientTensor I hΦ m κ T n r z i j k‖ ≤
            ‖amnrSpatialGradientTensor I hΦ m κ T n r z i j‖ :=
          norm_le_pi_norm _ _
        have h3 : ‖amnrSpatialGradientTensor I hΦ m κ T n r z i j‖ ≤
            ‖amnrSpatialGradientTensor I hΦ m κ T n r z i‖ :=
          norm_le_pi_norm _ _
        have h4 : ‖amnrSpatialGradientTensor I hΦ m κ T n r z i‖ ≤
            ‖amnrSpatialGradientTensor I hΦ m κ T n r z‖ :=
          norm_le_pi_norm _ _
        exact h1.trans (h2.trans (h3.trans h4))) (p := 2)
    exact hmono.trans (hAmnrGrad n hn)
  have hprod (n : ℕ) (hn : n ∈ Finset.range (AVenhance.Nstar β))
      (i j k : Fin 2) :
      eLpNorm (fun z : ℝ × Vec 2 =>
        AVenhance.spaceGrad
          (fun x => I.Amnr hΦ m κ n T r z.1 x i j k) z.2 i *
            I.qMNR κ m n r z.1 j k) 2 μ ≤
          ENNReal.ofReal (Q n * A) := by
    have hqmeas : AEStronglyMeasurable
        (fun z : ℝ × Vec 2 => I.qMNR κ m n r z.1 j k) μ := by
      have hc := AVenhance.Infra.Section3.qMNR_entry_continuous I κ m n r j k
      exact (hc.comp continuous_fst).aestronglyMeasurable
    exact eLpNorm_mul_right_le_of_abs_bound (hQ0 n hn)
      (hGradEntryMeas n hn i j k i) hqmeas
      (fun z => hqentry n hn z.1 j k) (hgradEntryLp n hn i j k i)
  have hfun : (fun z : ℝ × Vec 2 => hmEndpoint I hΦ m κ T r z.1 z.2) =ᵐ[μ]
      ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
        ∑ j : Fin 2, ∑ k : Fin 2,
          fun z : ℝ × Vec 2 => AVenhance.spaceGrad
            (fun x => I.Amnr hΦ m κ n T r z.1 x i j k) z.2 i *
              I.qMNR κ m n r z.1 j k := by
    filter_upwards [hμ.ae_le (ae_restrict_mem
      (measurableSet_Ioi.prod MeasurableSet.univ))] with z hz
    simp only [Finset.sum_apply]
    exact relative_initial_endpoint_spatial_sum I hΦ m κ T r z.1 z.2
      (fun n hn i j k => hDifferentiable n hn i j k z.1 hz.1 z.2)
  rw [eLpNorm_congr_ae hfun]
  calc
    eLpNorm (∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
        ∑ j : Fin 2, ∑ k : Fin 2,
          fun z : ℝ × Vec 2 => AVenhance.spaceGrad
            (fun x => I.Amnr hΦ m κ n T r z.1 x i j k) z.2 i *
              I.qMNR κ m n r z.1 j k) 2 μ
      ≤ ∑ i : Fin 2, eLpNorm (∑ n ∈ Finset.range (AVenhance.Nstar β),
          ∑ j : Fin 2, ∑ k : Fin 2,
            fun z : ℝ × Vec 2 => AVenhance.spaceGrad
              (fun x => I.Amnr hΦ m κ n T r z.1 x i j k) z.2 i *
                I.qMNR κ m n r z.1 j k) 2 μ :=
          eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
    _ ≤ ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
          eLpNorm (∑ j : Fin 2, ∑ k : Fin 2,
            fun z : ℝ × Vec 2 => AVenhance.spaceGrad
              (fun x => I.Amnr hΦ m κ n T r z.1 x i j k) z.2 i *
                I.qMNR κ m n r z.1 j k) 2 μ := by
      apply Finset.sum_le_sum
      intro i _
      exact eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
    _ ≤ ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
          ∑ j : Fin 2, eLpNorm (∑ k : Fin 2,
            fun z : ℝ × Vec 2 => AVenhance.spaceGrad
              (fun x => I.Amnr hΦ m κ n T r z.1 x i j k) z.2 i *
                I.qMNR κ m n r z.1 j k) 2 μ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro n _
      exact eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
    _ ≤ ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
          ∑ j : Fin 2, ∑ k : Fin 2,
            eLpNorm (fun z : ℝ × Vec 2 => AVenhance.spaceGrad
              (fun x => I.Amnr hΦ m κ n T r z.1 x i j k) z.2 i *
                I.qMNR κ m n r z.1 j k) 2 μ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro n _
      apply Finset.sum_le_sum
      intro j _
      exact eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)
    _ ≤ ∑ i : Fin 2, ∑ n ∈ Finset.range (AVenhance.Nstar β),
          ∑ j : Fin 2, ∑ k : Fin 2, ENNReal.ofReal (Q n * A) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact hprod n hn i j k
    _ = ∑ n ∈ Finset.range (AVenhance.Nstar β),
          ENNReal.ofReal (8 * Q n * A) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      calc
        (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
            ENNReal.ofReal (Q n * A)) =
          8 * ENNReal.ofReal (Q n * A) := by
            simp only [Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            ring
        _ = ENNReal.ofReal 8 * ENNReal.ofReal (Q n * A) := by norm_num
        _ = ENNReal.ofReal (8 * (Q n * A)) :=
            (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)).symm
        _ = ENNReal.ofReal (8 * Q n * A) := by
            apply congrArg ENNReal.ofReal
            ring
        _ = ENNReal.ofReal (8 *
            ((4 * Real.pi ^ 2 * C₀) *
              (AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 2) *
              (AVenhance.epsilon β I.Λ m ^ 2 /
                (κ * AVenhance.tau β I.Λ m)) ^ n *
              (8 * AVenhance.tau β I.Λ m) ^ r) * A) := by
            apply congrArg ENNReal.ofReal
            dsimp [Q]

end AVenhance.Infra.Section5.RelativeError
