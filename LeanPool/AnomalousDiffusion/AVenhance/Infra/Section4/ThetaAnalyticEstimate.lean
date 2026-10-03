/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaHonestRecursion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaClassicalUniqueness
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0

/-! Analytic estimates for the classical theta solution, conditional on the stream-regularity and
    diffusivity-recursion estimates. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Topology

namespace AVenhance.Infra.Section4

theorem ThetaAnalyticEstimate.theta_analytic_vecList_sum_apply
    (L : List (Vec 2)) (j : Fin 2) :
    L.sum j = (L.map fun v => v j).sum := by
  induction L with
  | nil => simp
  | cons v L ih =>
    simp [ih, Pi.add_apply]

/-- Closed time-space unit cell for the temperature analyticity estimate. -/
def ThetaAnalyticEstimate.thetaAnalyticClosedCell : Set (ℝ × Vec 2) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ
    (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem ThetaAnalyticEstimate.theta_analytic_closedCell_compact :
    IsCompact ThetaAnalyticEstimate.thetaAnalyticClosedCell := by
  apply IsCompact.prod isCompact_Icc
  simpa [ThetaAnalyticEstimate.thetaAnalyticClosedCell] using
    (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem ThetaAnalyticEstimate.theta_timeCube_subset_analyticClosedCell :
    AVenhance.timeCube ⊆ ThetaAnalyticEstimate.thetaAnalyticClosedCell := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  refine ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, ?_⟩
  change ∀ i ∈ Set.univ, x i ∈ Set.Icc (0 : ℝ) 1
  intro i hi
  exact ⟨le_of_lt (hx i hi).1, le_of_lt (hx i hi).2⟩

/-- The pointwise coefficient for an order-q derivative of the stream
potential, copied from the stream-regularity barNorm conclusion after the factorial and
radius weights are unpacked. -/
noncomputable def thetaPotentialDerivativeCoefficient
    {β : ℝ} {m : ℕ} (I : AVenhance.Ingredients β) (q : ℕ) : ℝ :=
  2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
    AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
    (q.factorial : ℝ) *
    (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ q

/-- For q at least two, the direct stream-flux estimate controls the
differentiated energy pairing by the qth coefficient and the two gradient
energies. -/
theorem theta_higher_order_stream_split_pairing_abs_le_of_A3
    {β κ : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : AVenhance.IsStreamSeq I Φ)
    (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel (fun t => Φ (m - 1) t)) κ
      (fun _ _ => 0) θ₀ θ)
    {T : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1)
    {w : List (Fin 2)} (split : List (Fin 2) × List (Fin 2))
    (hq : 2 ≤ split.1.length) :
    |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      vecDot (thetaWordGradientExtension θ w p)
        (thetaStreamSplitExtension (fun t => Φ (m - 1) t) θ split p)| ≤
      2 * thetaPotentialDerivativeCoefficient (m := m) I split.1.length *
        Real.sqrt (thetaIntervalWordGradientEnergy θ T w) *
        Real.sqrt (thetaIntervalWordGradientEnergy θ T split.2) := by
  let φ : ℝ → Vec 2 → ℝ := fun t => Φ (m - 1) t
  let M := thetaPotentialDerivativeCoefficient (m := m) I split.1.length
  have hφadm : AVenhance.IsAdmissibleStream φ :=
    theta_prev_stream_admissible I Φ hΦ hm
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    exact hφadm.1.contDiffOn.mono (by intro p hp; exact Set.mem_univ p)
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hsol.1
  have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
    AVenhance.Infra.Cutoff.epsilon_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ha : 0 < AVenhance.a β I.Λ (m - 1) := by
    rw [AVenhance.a]
    exact Real.rpow_pos_of_pos he _
  have hM : 0 ≤ M := by
    dsimp [M, thetaPotentialDerivativeCoefficient]
    positivity
  have hcoef : ∀ p ∈ Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      |thetaWordExtension φ split.1 p| ≤ M := by
    intro p hp
    have ht : 0 < p.1 := hp.1.1
    rw [thetaWordExtension_eq_slice (u := φ) (w := split.1) p.1 ht p.2]
    have hpoint := theta_prev_potential_word_abs_le_of_A3
      I Φ hΦ hm hA3 p.1 split.1 hq p.2
    simpa [M, thetaPotentialDerivativeCoefficient, φ] using hpoint
  have hpair := theta_interval_stream_split_pairing_abs_le
    (w := w) hθ hφ hT
    split hM hcoef
  change |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      vecDot (thetaWordGradientExtension θ w p)
        (fun j => thetaWordExtension φ split.1 p *
          thetaStreamWordExtension θ split.2 p j)| ≤ _
  exact hpair

/-- The gradient energy on an initial subinterval is bounded by the full
space-time gradient energy. -/
theorem theta_interval_word_gradient_energy_le
    {θ : ℝ → Vec 2 → ℝ} (hθ : ContDiffOn ℝ (⊤ : ℕ∞)
      (Function.uncurry θ) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {T : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1) (w : List (Fin 2)) :
    (∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
      Homogenization.vecNormSq
        (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)) ≤
      thetaWordSpaceTimeGradientEnergy θ w := by
  let f : ℝ × Vec 2 → ℝ := fun p =>
    Homogenization.vecNormSq (thetaWordGradientExtension θ w p)
  have hf : Continuous f := by
    change Continuous (fun p => ∑ j : Fin 2,
      thetaWordGradientExtension θ w p j * thetaWordGradientExtension θ w p j)
    have hgrad : Continuous (thetaWordGradientExtension θ w) :=
      thetaWordGradientExtension_continuous hθ
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp hgrad).mul
      ((continuous_apply j).comp hgrad)
  have hcube := theta_intervalCube_integral_eq_interval_integral hT hf
  have hsub : Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube ⊆ AVenhance.timeCube := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨ht.1, ht.2.trans_le hT.2⟩, hx⟩
  have hcell : AVenhance.timeCube ⊆ ThetaAnalyticEstimate.thetaAnalyticClosedCell :=
    ThetaAnalyticEstimate.theta_timeCube_subset_analyticClosedCell
  have hint : IntegrableOn f AVenhance.timeCube := by
    exact (hf.continuousOn.integrableOn_compact
        ThetaAnalyticEstimate.theta_analytic_closedCell_compact)
      |>.mono_set hcell
  have hnonneg : 0 ≤ᵐ[volume.restrict AVenhance.timeCube] f :=
    ae_of_all _ (fun _ => Homogenization.vecNormSq_nonneg _)
  have hmono := MeasureTheory.setIntegral_mono_set hint hnonneg
    (Filter.Eventually.of_forall hsub)
  have hfull : (∫ p in AVenhance.timeCube, f p) =
      thetaWordSpaceTimeGradientEnergy θ w := by
    dsimp [f]
    exact (thetaWordGradientExtension_energy_eq (u := θ) (w := w)).symm
  calc
    (∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
        Homogenization.vecNormSq
          (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)) =
      ∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube, f (t, x) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        have ht' : t ∈ Set.Ioc (0 : ℝ) T := by
          simpa only [Set.uIoc_of_le hT.1] using ht
        apply integral_congr_ae
        filter_upwards with x
        dsimp [f]
        rw [thetaWordGradientExtension_eq_slice
          (u := θ) (w := w) t ht'.1 x]
    _ = ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, f p := hcube.symm
    _ ≤ ∫ p in AVenhance.timeCube, f p := hmono
    _ = thetaWordSpaceTimeGradientEnergy θ w := hfull

/-- The time-integrated flux term in the differentiated energy identity is the
sum of the continuous representatives of its Leibniz splits. -/
theorem theta_classical_flux_interval_integral_eq_split_sum
    {φ θ : ℝ → Vec 2 → ℝ} {T : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) :
    (∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
      vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
        (thetaStreamCommutatorFlux w (φ t) (θ t) x)) =
      ((classicalWordCommutatorSplits w).map fun split =>
        ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
          vecDot (thetaWordGradientExtension θ w p)
            (thetaStreamSplitExtension φ θ split p)).sum := by
  let L := classicalWordCommutatorSplits w
  let Terms : List (ℝ × Vec 2 → ℝ) := L.map fun split p =>
    vecDot (thetaWordGradientExtension θ w p)
      (thetaStreamSplitExtension φ θ split p)
  have hgrad : Continuous (thetaWordGradientExtension θ w) :=
    thetaWordGradientExtension_continuous hθ
  have hterm (split : List (Fin 2) × List (Fin 2)) :
      Continuous (fun p => vecDot (thetaWordGradientExtension θ w p)
        (thetaStreamSplitExtension φ θ split p)) := by
    have hvec : Continuous (fun p => thetaStreamSplitExtension φ θ split p) := by
      apply continuous_pi
      intro j
      exact (thetaWordExtension_continuous hφ).mul
        ((continuous_apply j).comp
          (thetaStreamWordExtension_continuous hθ))
    change Continuous (fun p => ∑ j : Fin 2,
      thetaWordGradientExtension θ w p j *
        thetaStreamSplitExtension φ θ split p j)
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp hgrad).mul
      ((continuous_apply j).comp hvec)
  have hterms : ∀ f ∈ Terms, Continuous f := by
    intro f hf
    obtain ⟨split, hs, rfl⟩ := List.mem_map.mp hf
    exact hterm split
  have htotal : Continuous Terms.sum := by
    have hrec : ∀ L : List (ℝ × Vec 2 → ℝ),
        (∀ f ∈ L, Continuous f) → Continuous L.sum := by
      intro L
      induction L with
      | nil => intro _; exact continuous_const
      | cons f L ih =>
        intro hL
        have htail : ∀ g ∈ L, Continuous g := by
          intro g hg
          exact hL g (List.mem_cons_of_mem f hg)
        change Continuous (fun p => f p + L.sum p)
        exact (hL f (List.mem_cons_self ..)).add (ih htail)
    exact hrec Terms hterms
  have hpoint (t : ℝ) (ht : 0 < t) (x : Vec 2) :
      Terms.sum (t, x) =
        vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
          (thetaStreamCommutatorFlux w (φ t) (θ t) x) := by
    have hgradSlice := thetaWordGradientExtension_eq_slice
      (u := θ) (w := w) t ht x
    have htermSlice (split : List (Fin 2) × List (Fin 2)) :
        thetaStreamSplitExtension φ θ split (t, x) =
          thetaStreamCommutatorProductTerm split (φ t) (θ t) x := by
      funext j
      simp [thetaStreamSplitExtension,
        thetaWordExtension_eq_slice (u := φ) (w := split.1) t ht x,
        thetaStreamWordExtension_eq_slice (u := θ) (w := split.2) t ht x,
        thetaStreamCommutatorProductTerm]
    calc
      Terms.sum (t, x) =
          (Terms.map fun f => f (t, x)).sum :=
        theta_analytic_funList_sum_apply Terms (t, x)
      _ = (L.map fun split =>
          vecDot (thetaWordGradientExtension θ w (t, x))
            (thetaStreamSplitExtension φ θ split (t, x))).sum := by
        simp only [Terms, L, List.map_map, Function.comp_def]
      _ = (L.map fun split =>
          vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
            (thetaStreamCommutatorProductTerm split (φ t) (θ t) x)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro split hs
        rw [hgradSlice, htermSlice]
      _ = vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
          (L.map fun split =>
            thetaStreamCommutatorProductTerm split (φ t) (θ t) x).sum := by
        simpa only [List.map_map, Function.comp_def] using
          (theta_vecDot_list_sum
            (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
            (L.map fun split => thetaStreamCommutatorProductTerm split (φ t) (θ t) x)).symm
      _ = _ := by
        have hflux : thetaStreamCommutatorFlux w (φ t) (θ t) x =
            (L.map fun split => thetaStreamCommutatorProductTerm split
              (φ t) (θ t) x).sum := by
          funext j
          change (L.map fun split => thetaStreamCommutatorProductTerm split
              (φ t) (θ t) x j).sum =
            ((L.map fun split => thetaStreamCommutatorProductTerm split
              (φ t) (θ t) x).sum) j
          simpa only [List.map_map, Function.comp_def] using
            (ThetaAnalyticEstimate.theta_analytic_vecList_sum_apply
              (L.map fun split => thetaStreamCommutatorProductTerm split
                (φ t) (θ t) x) j).symm
        rw [hflux]
  have hslice (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) T) :
      (∫ x in AVenhance.unitCube, Terms.sum (t, x)) =
        ∫ x in AVenhance.unitCube,
          vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
            (thetaStreamCommutatorFlux w (φ t) (θ t) x) := by
    apply integral_congr_ae
    filter_upwards with x
    exact hpoint t ht.1 x
  have htime :
      (∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
        Terms.sum (t, x)) =
      ∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
        vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
          (thetaStreamCommutatorFlux w (φ t) (θ t) x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) T := by
      simpa only [Set.uIoc_of_le hT.1] using ht
    exact hslice t ht'
  have hFubini := theta_intervalCube_integral_eq_interval_integral hT htotal
  have hsplit := theta_time_flux_pairing_eq_split_sum (w := w) hφ hθ hT
  have hsplit' :
      (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, Terms.sum p) =
        ((classicalWordCommutatorSplits w).map fun split =>
          ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
            vecDot (thetaWordGradientExtension θ w p)
              (thetaStreamSplitExtension φ θ split p)).sum := by
    simpa [Terms, L] using hsplit
  calc
    (∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
        vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
          (thetaStreamCommutatorFlux w (φ t) (θ t) x)) =
      ∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube, Terms.sum (t, x) := htime.symm
    _ = ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, Terms.sum p := hFubini.symm
    _ = _ := hsplit'

end AVenhance.Infra.Section4

end
