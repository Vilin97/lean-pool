/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaTimeSpatialTrace
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaDifferentiatedEnergy
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Time integrated differentiated energy identities and their input bounds. -/

@[expose] public section

open Homogenization
open MeasureTheory Filter
open scoped Topology

namespace AVenhance.Infra.Section4

noncomputable section

/-- Joint time-space domain with nonnegative time, including the initial trace. -/
def ThetaIntegratedEnergy.thetaTraceDomain : Set (ℝ × Vec 2) :=
  Set.Ici (0 : ℝ) ×ˢ Set.univ

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def ThetaIntegratedEnergy.thetaTraceClosedCell : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem ThetaIntegratedEnergy.thetaTraceClosedCell_compact : IsCompact
    ThetaIntegratedEnergy.thetaTraceClosedCell := by
  simpa [ThetaIntegratedEnergy.thetaTraceClosedCell] using (isCompact_univ_pi fun _ : Fin 2 =>
      isCompact_Icc)

theorem ThetaIntegratedEnergy.thetaTrace_unitCube_subset_closedCell :
    AVenhance.unitCube ⊆ ThetaIntegratedEnergy.thetaTraceClosedCell := by
  intro x hx
  change (∀ i ∈ Set.univ, x i ∈ Set.Ioo (0 : ℝ) 1) at hx
  change (∀ i ∈ Set.univ, x i ∈ Set.Icc (0 : ℝ) 1)
  intro i hi
  exact ⟨le_of_lt (hx i hi).1, le_of_lt (hx i hi).2⟩

theorem ThetaIntegratedEnergy.thetaTrace_joint_extension_continuous
    {f : ℝ × Vec 2 → ℝ} (hf : ContinuousOn f ThetaIntegratedEnergy.thetaTraceDomain) :
    Continuous (fun p : ℝ × Vec 2 => f (max p.1 0, p.2)) := by
  have hmap : Continuous (fun p : ℝ × Vec 2 => (max p.1 0, p.2)) := by fun_prop
  have hmem : Set.MapsTo (fun p : ℝ × Vec 2 => (max p.1 0, p.2)) Set.univ
      ThetaIntegratedEnergy.thetaTraceDomain := by
    intro p hp
    constructor
    · change (0 : ℝ) ≤ max p.1 0
      exact le_max_right p.1 0
    · exact Set.mem_univ _
  have h := hf.comp hmap.continuousOn hmem
  change ContinuousOn (fun p : ℝ × Vec 2 => f (max p.1 0, p.2)) Set.univ at h
  exact continuousOn_univ.mp h

/- Integrating a jointly continuous-on-half-space function over the torus
cell gives a continuous function of time down to zero. The proof uses a
compact majorant on a closed unit cell and dominated convergence. -/
theorem theta_time_parametric_integral_continuousOn
    {f : ℝ × Vec 2 → ℝ} (hf : ContinuousOn f ThetaIntegratedEnergy.thetaTraceDomain) :
    ContinuousOn (fun t => ∫ x in AVenhance.unitCube, f (t, x))
      (Set.Ici (0 : ℝ)) := by
  let F : ℝ × Vec 2 → ℝ := fun p => f (max p.1 0, p.2)
  have hF : Continuous F := by
    simpa [F] using ThetaIntegratedEnergy.thetaTrace_joint_extension_continuous hf
  have hparam : Continuous (fun t => ∫ x in AVenhance.unitCube, F (t, x)) := by
    rw [continuous_iff_continuousAt]
    intro t₀
    let K : Set (ℝ × Vec 2) := Set.Icc (t₀ - 1) (t₀ + 1) ×ˢ
        ThetaIntegratedEnergy.thetaTraceClosedCell
    have hK : IsCompact K := by
      apply IsCompact.prod isCompact_Icc ThetaIntegratedEnergy.thetaTraceClosedCell_compact
    have hbounded := hK.exists_bound_of_continuousOn (hF.continuousOn.mono (by
      intro p hp
      exact Set.mem_univ p))
    obtain ⟨C, hC⟩ := hbounded
    have hCnonneg : 0 ≤ C := by
      have hzero : (t₀, (0 : Vec 2)) ∈ K := by
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        intro i hi
        simp
      exact le_trans (norm_nonneg _) (hC (t₀, 0) hzero)
    let B : ℝ := C + 1
    have hboundOn : ∀ t, |t - t₀| < 1 → ∀ x ∈ AVenhance.unitCube,
        ‖F (t, x)‖ ≤ B := by
      intro t ht x hx
      have ht' : t ∈ Set.Icc (t₀ - 1) (t₀ + 1) := by
        rw [abs_lt] at ht
        constructor <;> linarith
      have hx' : x ∈ ThetaIntegratedEnergy.thetaTraceClosedCell :=
          ThetaIntegratedEnergy.thetaTrace_unitCube_subset_closedCell hx
      exact le_trans (hC (t, x) ⟨ht', hx'⟩) (by dsimp [B]; linarith)
    let μ : Measure (Vec 2) := volume.restrict AVenhance.unitCube
    have hmeas : ∀ᶠ t in 𝓝 t₀,
        AEStronglyMeasurable (fun x : Vec 2 => F (t, x)) μ := by
      filter_upwards with t
      have hslice : Continuous (fun x : Vec 2 => F (t, x)) := by
        exact hF.comp (continuous_const.prodMk continuous_id)
      exact hslice.aestronglyMeasurable
    have hbound : ∀ᶠ t in 𝓝 t₀, ∀ᵐ x ∂μ,
        ‖F (t, x)‖ ≤ B := by
      filter_upwards [Metric.ball_mem_nhds t₀ (by norm_num : (0 : ℝ) < 1)] with t ht
      have ht' : |t - t₀| < 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at ht
        simpa [abs_sub_comm] using ht
      apply (ae_restrict_iff' thetaTime_measurableSet_unitCube).2
      filter_upwards with x hx
      exact hboundOn t ht' x hx
    have hBint : Integrable (fun _ : Vec 2 => B) μ := by
      change IntegrableOn (fun _ : Vec 2 => B) AVenhance.unitCube
      exact thetaTime_integrableOn_unitCube continuous_const
    have hlim : ∀ᵐ x ∂μ,
        Tendsto (fun t => F (t, x)) (𝓝 t₀) (𝓝 (F (t₀, x))) := by
      filter_upwards with x
      have hslice : Continuous (fun t : ℝ => F (t, x)) :=
        hF.comp (continuous_id.prodMk continuous_const)
      exact hslice.continuousAt.tendsto
    have hDCT := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := 𝓝 t₀) (F := fun t x => F (t, x))
      (bound := fun _ : Vec 2 => B) hmeas hbound hBint hlim
    change Tendsto (fun t => ∫ x in AVenhance.unitCube, F (t, x))
      (𝓝 t₀) (𝓝 (∫ x in AVenhance.unitCube, F (t₀, x)))
    simpa [μ] using hDCT
  apply hparam.continuousOn.congr
  intro t ht
  have htime : max t 0 = t := max_eq_left ht
  simp [F, htime]

/-- Evaluate a spatial derivative word of a curried field on joint time-space. -/
def ThetaIntegratedEnergy.thetaWordJointSlice (w : List (Fin 2))
    (ψ : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  classicalWordDerivative w (ψ p.1) p.2

/-- Rotated spatial gradient of a derivative word, giving its stream velocity. -/
def ThetaIntegratedEnergy.thetaJointStreamVelocity (w : List (Fin 2))
    (θ : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) (j : Fin 2) : ℝ :=
  if j = 0 then -ThetaIntegratedEnergy.thetaWordJointSlice (1 :: w) θ p
  else ThetaIntegratedEnergy.thetaWordJointSlice (0 :: w) θ p

/-- Flux assembled from the ordered-word commutator splits of two scalar fields. -/
def ThetaIntegratedEnergy.thetaJointStreamFlux (w : List (Fin 2))
    (φ θ : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) (j : Fin 2) : ℝ :=
  ((classicalWordCommutatorSplits w).map fun q =>
    ThetaIntegratedEnergy.thetaWordJointSlice q.1 φ p *
        ThetaIntegratedEnergy.thetaJointStreamVelocity q.2 θ p j).sum

theorem ThetaIntegratedEnergy.continuousOn_list_sum {α : Type*} [TopologicalSpace α]
    {L : List (α → ℝ)}
    {s : Set α} (hL : ∀ f ∈ L, ContinuousOn f s) : ContinuousOn L.sum s := by
  induction L with
  | nil =>
      change ContinuousOn (fun _ : α => (0 : ℝ)) s
      exact continuousOn_const
  | cons f L ih =>
      have hf := hL f (by simp)
      have htail : ∀ g ∈ L, ContinuousOn g s := by
        intro g hg
        exact hL g (by simp [hg])
      change ContinuousOn (fun x => f x + L.sum x) s
      exact hf.add (ih htail)

theorem ThetaIntegratedEnergy.thetaListSumEval {α : Type*} (L : List (α → ℝ)) (x : α) :
    L.sum x = (L.map fun f => f x).sum := by
  induction L with
  | nil => simp
  | cons f L ih => simp [ih]

theorem ThetaIntegratedEnergy.thetaJointStreamVelocity_continuousOn
    {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) ThetaIntegratedEnergy.thetaTraceDomain)
    (w : List (Fin 2)) (j : Fin 2) :
    ContinuousOn (fun p : ℝ × Vec 2 => ThetaIntegratedEnergy.thetaJointStreamVelocity w θ p j)
      ThetaIntegratedEnergy.thetaTraceDomain := by
  have hθ' : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    simpa [ThetaIntegratedEnergy.thetaTraceDomain] using hθ
  have hθword (q : List (Fin 2)) : ContDiffOn ℝ (⊤ : ℕ∞)
      (ThetaIntegratedEnergy.thetaWordJointSlice q θ) ThetaIntegratedEnergy.thetaTraceDomain := by
    have hh := theta_classical_word_joint_contDiffOn_nonneg hθ' q
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => classicalWordDerivative q (θ p.1) p.2)
          ThetaIntegratedEnergy.thetaTraceDomain at hh
    exact hh
  by_cases hj : j = 0
  · subst j
    have hneg : ContinuousOn
        (fun p : ℝ × Vec 2 => -ThetaIntegratedEnergy.thetaWordJointSlice (1 :: w) θ p)
            ThetaIntegratedEnergy.thetaTraceDomain :=
      (hθword (1 :: w)).continuousOn.neg
    simpa [ThetaIntegratedEnergy.thetaJointStreamVelocity] using hneg
  · have hpos : ContinuousOn
        (fun p : ℝ × Vec 2 => ThetaIntegratedEnergy.thetaWordJointSlice (0 :: w) θ p)
            ThetaIntegratedEnergy.thetaTraceDomain :=
      (hθword (0 :: w)).continuousOn
    simpa [ThetaIntegratedEnergy.thetaJointStreamVelocity, hj] using hpos

theorem ThetaIntegratedEnergy.thetaJointStreamFlux_continuousOn
    {φ θ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ) ThetaIntegratedEnergy.thetaTraceDomain)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) ThetaIntegratedEnergy.thetaTraceDomain)
    (w : List (Fin 2)) (j : Fin 2) :
    ContinuousOn (fun p => ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ p j)
        ThetaIntegratedEnergy.thetaTraceDomain := by
  have hφ' : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    simpa [ThetaIntegratedEnergy.thetaTraceDomain] using hφ
  have hφword (q : List (Fin 2)) : ContDiffOn ℝ (⊤ : ℕ∞)
      (ThetaIntegratedEnergy.thetaWordJointSlice q φ) ThetaIntegratedEnergy.thetaTraceDomain := by
    have hh := theta_classical_word_joint_contDiffOn_nonneg hφ' q
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => classicalWordDerivative q (φ p.1) p.2)
          ThetaIntegratedEnergy.thetaTraceDomain at hh
    exact hh
  let Terms : List (ℝ × Vec 2 → ℝ) :=
    (classicalWordCommutatorSplits w).map fun q =>
      fun p => ThetaIntegratedEnergy.thetaWordJointSlice q.1 φ p *
          ThetaIntegratedEnergy.thetaJointStreamVelocity q.2 θ p j
  have hterms : ∀ g ∈ Terms, ContinuousOn g ThetaIntegratedEnergy.thetaTraceDomain := by
    intro g hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    exact (hφword q.1).continuousOn.mul
      (ThetaIntegratedEnergy.thetaJointStreamVelocity_continuousOn hθ q.2 j)
  have heq : (fun p => ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ p j) = Terms.sum := by
    funext p
    change ((classicalWordCommutatorSplits w).map fun q =>
      ThetaIntegratedEnergy.thetaWordJointSlice q.1 φ p *
          ThetaIntegratedEnergy.thetaJointStreamVelocity q.2 θ p j).sum = Terms.sum p
    calc
      _ = (Terms.map fun g => g p).sum := by simp [Terms, List.map_map, Function.comp_def]
      _ = Terms.sum p := (ThetaIntegratedEnergy.thetaListSumEval Terms p).symm
  rw [heq]
  exact ThetaIntegratedEnergy.continuousOn_list_sum hterms

theorem ThetaIntegratedEnergy.thetaJointStreamVelocity_eq_slice
    {θ : ℝ → Vec 2 → ℝ} (w : List (Fin 2))
    {t : ℝ} (x : Vec 2) (j : Fin 2) :
    ThetaIntegratedEnergy.thetaJointStreamVelocity w θ (t, x) j =
      AVenhance.streamVel (fun _ => classicalWordDerivative w (θ t)) 0 x j := by
  fin_cases j
  · simp [ThetaIntegratedEnergy.thetaJointStreamVelocity,
      ThetaIntegratedEnergy.thetaWordJointSlice, classicalWordDerivative,
      Classical.classicalWordDerivative,
      AVenhance.streamVel, AVenhance.sigmaMat, Matrix.mulVec_apply_eq_sum,
      Fin.sum_univ_two]
  · simp [ThetaIntegratedEnergy.thetaJointStreamVelocity,
      ThetaIntegratedEnergy.thetaWordJointSlice, classicalWordDerivative,
      Classical.classicalWordDerivative,
      AVenhance.streamVel, AVenhance.sigmaMat, Matrix.mulVec_apply_eq_sum,
      Fin.sum_univ_two]

theorem ThetaIntegratedEnergy.thetaJointStreamFlux_eq_slice
    {φ θ : ℝ → Vec 2 → ℝ} (w : List (Fin 2))
    {t : ℝ} (x : Vec 2) :
    (fun j => ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ (t, x) j) =
      thetaStreamCommutatorFlux w (φ t) (θ t) x := by
  funext j
  simp only [ThetaIntegratedEnergy.thetaJointStreamFlux, thetaStreamCommutatorFlux]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  simp [ThetaIntegratedEnergy.thetaWordJointSlice,
      ThetaIntegratedEnergy.thetaJointStreamVelocity_eq_slice q.2 x j,
    thetaStreamCommutatorProductTerm]

theorem ThetaIntegratedEnergy.thetaJointEnergyFluxPairing_continuousOn
    {φ θ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ) ThetaIntegratedEnergy.thetaTraceDomain)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) ThetaIntegratedEnergy.thetaTraceDomain)
    (w : List (Fin 2)) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2)
        (fun j => ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ p j))
            ThetaIntegratedEnergy.thetaTraceDomain := by
  have hgrad (j : Fin 2) : ContinuousOn
      (fun p : ℝ × Vec 2 =>
        AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2 j)
      ThetaIntegratedEnergy.thetaTraceDomain := by
    have h := theta_classical_word_joint_contDiffOn_nonneg hθ (j :: w)
    simpa [classicalWordDerivative, Classical.classicalWordDerivative,
      ThetaIntegratedEnergy.thetaTraceDomain] using h.continuousOn
  have hflux (j : Fin 2) :
      ContinuousOn (fun p => ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ p j)
          ThetaIntegratedEnergy.thetaTraceDomain :=
    ThetaIntegratedEnergy.thetaJointStreamFlux_continuousOn hφ hθ w j
  have hsum : ContinuousOn (fun p : ℝ × Vec 2 =>
      (∑ j : Fin 2,
        AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2 j *
          ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ p j))
              ThetaIntegratedEnergy.thetaTraceDomain := by
    rw [show (fun p : ℝ × Vec 2 =>
        (∑ j : Fin 2,
          AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2 j *
            ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ p j)) =
        fun p =>
          (AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2 0 *
            ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ p 0) +
          (AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2 1 *
            ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ p 1) by
      funext p
      simp [Fin.sum_univ_two]]
    exact (hgrad 0).mul (hflux 0) |>.add ((hgrad 1).mul (hflux 1))
  have heq : (fun p : ℝ × Vec 2 =>
      vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2)
        (fun j => ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ p j)) =
      fun p =>
        (AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2 0 *
          ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ p 0) +
        (AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2 1 *
          ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ p 1) := by
    funext p
    simp [vecDot, Fin.sum_univ_two]
  rw [heq]
  simpa [Fin.sum_univ_two] using hsum

theorem ThetaIntegratedEnergy.thetaJointEnergyGradientNormSq_continuousOn
    {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) ThetaIntegratedEnergy.thetaTraceDomain)
    (w : List (Fin 2)) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      vecNormSq (AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2))
      ThetaIntegratedEnergy.thetaTraceDomain := by
  have hgrad (j : Fin 2) : ContinuousOn
      (fun p : ℝ × Vec 2 =>
        AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2 j)
      ThetaIntegratedEnergy.thetaTraceDomain := by
    have h := theta_classical_word_joint_contDiffOn_nonneg hθ (j :: w)
    simpa [classicalWordDerivative, Classical.classicalWordDerivative,
      ThetaIntegratedEnergy.thetaTraceDomain] using h.continuousOn
  have heq : (fun p : ℝ × Vec 2 =>
      vecNormSq (AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2)) =
      fun p =>
        (AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2 0) ^ 2 +
        (AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2 1) ^ 2 := by
    funext p
    simp [vecNormSq, vecDot, Fin.sum_univ_two, pow_two]
  rw [heq]
  exact (hgrad 0).pow 2 |>.add ((hgrad 1).pow 2)

/-- Time-integrated energy balance after differentiating the classical equation
by an arbitrary ordered spatial word.  The endpoint at zero is obtained from
continuity of the closed-half-space representative; differentiation is only
used on the open positive-time interval. -/
theorem theta_classical_differentiated_energy_integrated
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ)
    (hsol : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ
      (fun _ _ => 0) θ₀ θ)
    {T : ℝ} (hT : 0 ≤ T) (w : List (Fin 2)) :
    (∫ x in AVenhance.unitCube,
      (classicalWordDerivative w (θ T) x) ^ 2) +
      2 * κ * (∫ t in (0 : ℝ)..T,
        ∫ x in AVenhance.unitCube,
          vecNormSq (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)) =
    (∫ x in AVenhance.unitCube,
      (classicalWordDerivative w θ₀ x) ^ 2) -
      2 * (∫ t in (0 : ℝ)..T,
        ∫ x in AVenhance.unitCube,
          classicalWordDerivative w (θ t) x *
            (classicalWordDerivative w
                (classicalTransport (AVenhance.streamVel φ t) (θ t)) x -
              vecDot (AVenhance.streamVel φ t x)
                (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x))) ∧
    (∫ x in AVenhance.unitCube,
      (classicalWordDerivative w (θ T) x) ^ 2) +
      2 * κ * (∫ t in (0 : ℝ)..T,
        ∫ x in AVenhance.unitCube,
          vecNormSq (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)) =
    (∫ x in AVenhance.unitCube,
      (classicalWordDerivative w θ₀ x) ^ 2) -
      2 * (∫ t in (0 : ℝ)..T,
        ∫ x in AVenhance.unitCube,
          vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
            (thetaStreamCommutatorFlux w (φ t) (θ t) x)) := by
  let u : ℝ → Vec 2 → ℝ := fun t x => classicalWordDerivative w (θ t) x
  let Energy : ℝ → ℝ := fun t => ∫ x in AVenhance.unitCube, (u t x) ^ 2
  let Dissipation : ℝ → ℝ := fun t => ∫ x in AVenhance.unitCube,
    vecNormSq (AVenhance.spaceGrad (u t) x)
  let Pairing : ℝ → ℝ := fun t => ∫ x in AVenhance.unitCube,
    vecDot (AVenhance.spaceGrad (u t) x)
      (fun j => ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ (t, x) j)
  let CommutatorPairing : ℝ → ℝ := fun t => ∫ x in AVenhance.unitCube,
    u t x *
      (classicalWordDerivative w
          (classicalTransport (AVenhance.streamVel φ t) (θ t)) x -
        vecDot (AVenhance.streamVel φ t x)
          (AVenhance.spaceGrad (u t) x))
  have huJoint : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    have h := theta_classical_word_joint_contDiffOn_nonneg hsol.1 w
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => classicalWordDerivative w (θ p.1) p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)
    exact h
  have huJointDomain : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      ThetaIntegratedEnergy.thetaTraceDomain := by simpa [ThetaIntegratedEnergy.thetaTraceDomain]
          using huJoint
  have hEnergyCont : ContinuousOn Energy (Set.Icc (0 : ℝ) T) := by
    simpa [Energy] using theta_energy_continuousOn huJoint hT
  have hDissipationCont : ContinuousOn Dissipation (Set.Ici (0 : ℝ)) := by
    have hjoint := ThetaIntegratedEnergy.thetaJointEnergyGradientNormSq_continuousOn hsol.1 w
    simpa [Dissipation, u, ThetaIntegratedEnergy.thetaTraceDomain] using
      theta_time_parametric_integral_continuousOn hjoint
  have hPairingCont : ContinuousOn Pairing (Set.Ici (0 : ℝ)) := by
    have hφJoint : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
        ThetaIntegratedEnergy.thetaTraceDomain := by
      exact hφ.1.contDiffOn
    have hθJoint : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
        ThetaIntegratedEnergy.thetaTraceDomain := by
      change ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => θ p.1 p.2)
          ThetaIntegratedEnergy.thetaTraceDomain
      exact hsol.1
    have hjoint := ThetaIntegratedEnergy.thetaJointEnergyFluxPairing_continuousOn hφJoint hθJoint w
    simpa [Pairing, u, ThetaIntegratedEnergy.thetaTraceDomain] using
      theta_time_parametric_integral_continuousOn hjoint
  let Derivative : ℝ → ℝ := fun t => -2 * κ * Dissipation t - 2 * Pairing t
  have hDerivativeCont : ContinuousOn Derivative (Set.Icc (0 : ℝ) T) := by
    have hD : ContinuousOn Dissipation (Set.Icc (0 : ℝ) T) := hDissipationCont.mono (by
      intro t ht
      exact ht.1)
    have hP : ContinuousOn Pairing (Set.Icc (0 : ℝ) T) := hPairingCont.mono (by
      intro t ht
      exact ht.1)
    convert (hD.const_mul (-2 * κ)).sub (hP.const_mul 2) using 1
  have hDissipationInt : IntervalIntegrable Dissipation volume 0 T := by
    have hcont : ContinuousOn Dissipation (Set.uIcc 0 T) := by
      simpa [Set.uIcc_of_le hT] using hDissipationCont.mono (by
        intro t ht
        exact ht.1)
    exact hcont.intervalIntegrable
  have hPairingInt : IntervalIntegrable Pairing volume 0 T := by
    have hcont : ContinuousOn Pairing (Set.uIcc 0 T) := by
      simpa [Set.uIcc_of_le hT] using hPairingCont.mono (by
        intro t ht
        exact ht.1)
    exact hcont.intervalIntegrable
  have hDerivativeInt : IntervalIntegrable Derivative volume 0 T := by
    have hcont : ContinuousOn Derivative (Set.uIcc 0 T) := by
      simpa [Set.uIcc_of_le hT] using hDerivativeCont
    exact hcont.intervalIntegrable
  have hderiv (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
      HasDerivAt Energy (Derivative t) t := by
    have htpos : 0 < t := ht.1
    have hEnergyDeriv := theta_energy_hasDerivAt huJoint htpos
    have hpoint := theta_classical_differentiated_energy_pairing hφ hsol htpos w
    have huOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
        classicalPositiveTimeDomain := by
      have hsub : classicalPositiveTimeDomain ⊆
          (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
        intro p hp
        have hp' : 0 < p.1 := by
          simpa [classicalPositiveTimeDomain] using hp.1
        exact ⟨hp'.le, Set.mem_univ p.2⟩
      exact huJoint.mono hsub
    have htime := classicalTimePartial_eq_deriv huOpen htpos
    have htimeInt :
        (∫ x in AVenhance.unitCube, 2 * u t x * classicalTimePartial u (t, x)) =
          2 * (∫ x in AVenhance.unitCube, u t x * deriv (fun s => u s x) t) := by
      rw [show (fun x : Vec 2 => 2 * u t x * classicalTimePartial u (t, x)) =
          fun x => 2 * (u t x * deriv (fun s => u s x) t) by
        funext x
        rw [htime x]
        ring]
      rw [integral_const_mul]
    have hpair' :
        (∫ x in AVenhance.unitCube, u t x * deriv (fun s => u s x) t) +
            κ * Dissipation t = -Pairing t := by
      simpa [u, Dissipation, Pairing, vecDot, Fin.sum_univ_two,
        ThetaIntegratedEnergy.thetaJointStreamFlux_eq_slice] using hpoint
    have hderivValue :
        (∫ x in AVenhance.unitCube, 2 * u t x * classicalTimePartial u (t, x)) =
          Derivative t := by
      rw [htimeInt]
      dsimp [Derivative]
      nlinarith [hpair']
    exact hEnergyDeriv.congr_deriv hderivValue
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    hEnergyCont hderiv hDerivativeInt
  have hderivativeIntegral :
      (∫ t in (0 : ℝ)..T, Derivative t) =
        -2 * κ * (∫ t in (0 : ℝ)..T, Dissipation t) -
          2 * (∫ t in (0 : ℝ)..T, Pairing t) := by
    dsimp [Derivative]
    rw [intervalIntegral.integral_sub
        (hDissipationInt.const_mul (-2 * κ)) (hPairingInt.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hresult :
      Energy T + 2 * κ * (∫ t in (0 : ℝ)..T, Dissipation t) +
        2 * (∫ t in (0 : ℝ)..T, Pairing t) = Energy 0 := by
    rw [hderivativeIntegral] at hFTC
    linarith
  have hPairingSlice : ∀ t : ℝ, 0 ≤ t →
      Pairing t = ∫ x in AVenhance.unitCube,
        vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
          (thetaStreamCommutatorFlux w (φ t) (θ t) x) := by
    intro t ht
    apply integral_congr_ae
    filter_upwards with x
    rw [show (fun j => ThetaIntegratedEnergy.thetaJointStreamFlux w φ θ (t, x) j) =
        thetaStreamCommutatorFlux w (φ t) (θ t) x by
      exact ThetaIntegratedEnergy.thetaJointStreamFlux_eq_slice w x]
  have hPairingCommSlice : ∀ t : ℝ, 0 < t →
      Pairing t = CommutatorPairing t := by
    intro t ht
    have hflux := hPairingSlice t ht.le
    have hfluxEnergy := theta_classical_differentiated_energy_pairing hφ hsol ht w
    have hcommEnergy := theta_classical_differentiated_transport_energy_pairing
      hφ hsol ht w
    have hfluxEnergy' :
        (∫ x in AVenhance.unitCube,
          u t x * deriv (fun s => u s x) t) +
          κ * (∫ x in AVenhance.unitCube,
            vecNormSq (AVenhance.spaceGrad (u t) x)) = -Pairing t := by
      rw [← hflux] at hfluxEnergy
      simpa [Pairing, u] using hfluxEnergy
    have hcommEnergy' :
        (∫ x in AVenhance.unitCube,
          u t x * deriv (fun s => u s x) t) +
          κ * (∫ x in AVenhance.unitCube,
            vecNormSq (AVenhance.spaceGrad (u t) x)) = -CommutatorPairing t := by
      simpa [CommutatorPairing, u] using hcommEnergy
    linarith
  have hPairingIntegral :
      (∫ t in (0 : ℝ)..T, Pairing t) =
        ∫ t in (0 : ℝ)..T,
          ∫ x in AVenhance.unitCube,
            classicalWordDerivative w (θ t) x *
              (classicalWordDerivative w
                  (classicalTransport (AVenhance.streamVel φ t) (θ t)) x -
                vecDot (AVenhance.streamVel φ t x)
                  (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) T := by
      simpa only [Set.uIoc_of_le hT] using ht
    change Pairing t = CommutatorPairing t
    exact hPairingCommSlice t ht'.1
  have hPairingFluxIntegral :
      (∫ t in (0 : ℝ)..T, Pairing t) =
        ∫ t in (0 : ℝ)..T,
          ∫ x in AVenhance.unitCube,
            vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
              (thetaStreamCommutatorFlux w (φ t) (θ t) x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) T := by
      simpa only [Set.uIoc_of_le hT] using ht
    exact hPairingSlice t ht'.1.le
  have hDissipationIntegral :
      (∫ t in (0 : ℝ)..T, Dissipation t) =
        ∫ t in (0 : ℝ)..T,
          ∫ x in AVenhance.unitCube,
            vecNormSq (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x) := by
    rfl
  have hEnergyT : Energy T = ∫ x in AVenhance.unitCube,
      (classicalWordDerivative w (θ T) x) ^ 2 := by rfl
  have hEnergy0 : Energy 0 = ∫ x in AVenhance.unitCube,
      (classicalWordDerivative w θ₀ x) ^ 2 := by
    dsimp [Energy, u]
    apply integral_congr_ae
    filter_upwards with x
    rw [show θ 0 = θ₀ by funext y; exact hsol.2.2.1 y]
  rw [hEnergyT, hEnergy0, hDissipationIntegral] at hresult
  have hfluxResult := hresult
  rw [hPairingFluxIntegral] at hfluxResult
  rw [hPairingIntegral] at hresult
  constructor <;> linarith

end
end AVenhance.Infra.Section4
