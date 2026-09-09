/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalCompensation
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricHeatTail

@[expose] public section

/-!
# Terminal compensation for genuinely parameter-dependent debts

The physical heat parameter is `1-η²`. This module retains its contribution
to the debt derivative. Smoothness at the ends of a compact parameter range
is relative smoothness; all endpoint derivatives are actual `derivWithin`.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open NavierStokes.TerminalCompensation

namespace NavierStokes.ParametricTerminalCompensation

noncomputable def FirstJetWithinBound (P : Patch) (a : ℝ → ℝ) (c : ℝ → Coeff)
    (S : Set ℝ) (η L : ℝ) : Prop :=
  ∀ x : ℝ, |a η * correction P (c η) x| ≤ L ∧
    |a η * deriv (correction P (c η)) x| ≤ L ∧
    |derivWithin (fun θ => a θ * correction P (c θ) x) S η| ≤ L

theorem FirstJetWithinBound.mono {P : Patch} {a : ℝ → ℝ} {c : ℝ → Coeff}
    {S : Set ℝ} {η L M : ℝ} (h : FirstJetWithinBound P a c S η L) (hLM : L ≤ M) :
    FirstJetWithinBound P a c S η M := by
  intro x
  exact ⟨(h x).1.trans hLM, (h x).2.1.trans hLM, (h x).2.2.trans hLM⟩

theorem FirstJetWithinBound.toFirstJetBound {P : Patch} {a : ℝ → ℝ} {c : ℝ → Coeff}
    {S : Set ℝ} {η L : ℝ} (h : FirstJetWithinBound P a c S η L) (hS : S ∈ 𝓝 η) :
    FirstJetBound P a c η L := by
  intro x
  simpa only [derivWithin_of_mem_nhds hS] using h x

theorem compact_amplitude_within_bounds {S : Set ℝ} (hS : IsCompact S)
    (huniq : UniqueDiffOn ℝ S) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a S)
    (hpos : ∀ η ∈ S, 0 < a η) :
    ∃ D : ℝ, 0 < D ∧ ∀ η ∈ S,
      ‖amplitudeFactors (a η)‖ ≤ D ∧
      ‖derivWithin (fun θ => amplitudeFactors (a θ)) S η‖ ≤ D ∧
      |a η| ≤ D ∧ |derivWithin a S η| ≤ D := by
  have hF := amplitudeFactors_contDiffOn ha hpos
  have hFd : ContDiffOn ℝ ∞ (derivWithin (fun θ => amplitudeFactors (a θ)) S) S :=
    hF.derivWithin huniq (by simp)
  have had : ContDiffOn ℝ ∞ (derivWithin a S) S := ha.derivWithin huniq (by simp)
  obtain ⟨B₀, hb₀⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨B₁, hb₁⟩ := hS.exists_bound_of_continuousOn hFd.continuousOn
  obtain ⟨B₂, hb₂⟩ := hS.exists_bound_of_continuousOn ha.continuousOn
  obtain ⟨B₃, hb₃⟩ := hS.exists_bound_of_continuousOn had.continuousOn
  let D : ℝ := 1 + |B₀| + |B₁| + |B₂| + |B₃|
  have hD₀ : B₀ ≤ D := by dsimp [D]; linarith [le_abs_self B₀, abs_nonneg B₁, abs_nonneg B₂,
    abs_nonneg B₃]
  have hD₁ : B₁ ≤ D := by dsimp [D]; linarith [le_abs_self B₁, abs_nonneg B₀, abs_nonneg B₂,
    abs_nonneg B₃]
  have hD₂ : B₂ ≤ D := by dsimp [D]; linarith [le_abs_self B₂, abs_nonneg B₀, abs_nonneg B₁,
    abs_nonneg B₃]
  have hD₃ : B₃ ≤ D := by dsimp [D]; linarith [le_abs_self B₃, abs_nonneg B₀, abs_nonneg B₁,
    abs_nonneg B₂]
  refine ⟨D, by dsimp [D]; positivity, fun η hη => ⟨(hb₀ η hη).trans hD₀,
    (hb₁ η hη).trans hD₁, ?_, ?_⟩⟩
  · exact (hb₂ η hη).trans hD₂
  · exact (hb₃ η hη).trans hD₃

theorem amplitudeDebt_variable_contDiffOn {S : Set ℝ} {a : ℝ → ℝ} {v : ℝ → Coeff}
    (ha : ContDiffOn ℝ ∞ a S) (hpos : ∀ η ∈ S, 0 < a η) (hv : ContDiffOn ℝ ∞ v S) :
    ContDiffOn ℝ ∞ (fun η => amplitudeDebt (a η) (v η)) S :=
  ((amplitudeFactors_contDiffOn ha hpos).mul hv).neg

/-- Both terms are present: the amplitude derivative and the genuine debt derivative. -/
theorem amplitudeDebt_variable_derivWithin {S : Set ℝ} {a : ℝ → ℝ} {v : ℝ → Coeff}
    {η : ℝ} (huniq : UniqueDiffWithinAt ℝ S η)
    (ha : DifferentiableWithinAt ℝ (fun θ => amplitudeFactors (a θ)) S η)
    (hv : DifferentiableWithinAt ℝ v S η) :
    derivWithin (fun θ => amplitudeDebt (a θ) (v θ)) S η =
      -(derivWithin (fun θ => amplitudeFactors (a θ)) S η * v η +
        amplitudeFactors (a η) * derivWithin v S η) :=
  ((ha.hasDerivWithinAt.mul hv.hasDerivWithinAt).neg).derivWithin huniq

theorem amplitudeDebt_variable_bounds {S : Set ℝ} (huniq : UniqueDiffOn ℝ S)
    {a : ℝ → ℝ} {v : ℝ → Coeff} (ha : ContDiffOn ℝ ∞ a S)
    (hpos : ∀ η ∈ S, 0 < a η) (hv : ContDiffOn ℝ ∞ v S)
    {D : ℝ} (hD : ∀ η ∈ S, ‖amplitudeFactors (a η)‖ ≤ D ∧
      ‖derivWithin (fun θ => amplitudeFactors (a θ)) S η‖ ≤ D)
    {η : ℝ} (hη : η ∈ S) :
    ‖amplitudeDebt (a η) (v η)‖ ≤ D * ‖v η‖ ∧
      ‖derivWithin (fun θ => amplitudeDebt (a θ) (v θ)) S η‖ ≤
        D * (‖v η‖ + ‖derivWithin v S η‖) := by
  have hF : DifferentiableWithinAt ℝ (fun θ => amplitudeFactors (a θ)) S η :=
    ((amplitudeFactors_contDiffOn ha hpos) η hη).differentiableWithinAt (by simp)
  have hv' : DifferentiableWithinAt ℝ v S η :=
    (hv η hη).differentiableWithinAt (by simp)
  constructor
  · dsimp [amplitudeDebt]
    rw [norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hD η hη).1 (norm_nonneg _))
  · rw [amplitudeDebt_variable_derivWithin (huniq η hη) hF hv', norm_neg]
    calc
      _ ≤ ‖derivWithin (fun θ => amplitudeFactors (a θ)) S η * v η‖ +
          ‖amplitudeFactors (a η) * derivWithin v S η‖ := norm_add_le _ _
      _ ≤ D * ‖v η‖ + D * ‖derivWithin v S η‖ := by
        exact add_le_add
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hD η hη).2 (norm_nonneg _)))
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hD η hη).1 (norm_nonneg _)))
      _ = _ := by ring

theorem composed_solver_derivWithin_bound {g : Coeff → Coeff} {ε C : ℝ}
    (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 ε))
    (hbound : ∀ v ∈ Metric.ball (0 : Coeff) ε, ‖fderiv ℝ g v‖ ≤ C)
    {S : Set ℝ} {d : ℝ → Coeff} {η : ℝ} (huniq : UniqueDiffWithinAt ℝ S η)
    (hd : DifferentiableWithinAt ℝ d S η) (hmem : d η ∈ Metric.ball (0 : Coeff) ε) :
    ‖derivWithin (g ∘ d) S η‖ ≤ C * ‖derivWithin d S η‖ := by
  have hgd := (hg.contDiffAt (Metric.isOpen_ball.mem_nhds hmem)).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  rw [(hgd.hasFDerivAt.comp_hasDerivWithinAt η hd.hasDerivWithinAt).derivWithin huniq]
  exact ((fderiv ℝ g (d η)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hbound (d η) hmem) (norm_nonneg _))

theorem correction_parameter_derivWithin (P : Patch) {S : Set ℝ} {c : ℝ → Coeff} {η : ℝ}
    (huniq : UniqueDiffWithinAt ℝ S η) (hc : DifferentiableWithinAt ℝ c S η) (x : ℝ) :
    derivWithin (fun θ => correction P (c θ) x) S η = correction P (derivWithin c S η) x :=
  ((correctionCLM P x).hasFDerivAt.comp_hasDerivWithinAt η hc.hasDerivWithinAt).derivWithin huniq

/-- The constructed three-row inverse applies to a genuinely varying debt.
The derivative estimate includes its actual first parameter derivative. -/
theorem exists_variable_compensation (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam)
    {S : Set ℝ} (hS : IsCompact S) (huniq : UniqueDiffOn ℝ S)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a S) (hpos : ∀ η ∈ S, 0 < a η) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ v : ℝ → Coeff,
      ContDiffOn ℝ ∞ v S → (∀ η ∈ S, ‖v η‖ < ε) →
      ∃ c : ℝ → Coeff, ContDiffOn ℝ ∞ c S ∧ ∀ η ∈ S,
        momentMap P lam (c η) = amplitudeDebt (a η) (v η) ∧
        ‖c η‖ ≤ C * ‖v η‖ ∧
        ‖derivWithin c S η‖ ≤ C * (‖v η‖ + ‖derivWithin v S η‖) ∧
        FirstJetWithinBound P a c S η (C * (‖v η‖ + ‖derivWithin v S η‖)) ∧
        ∀ x : ℝ, 0 < x → 0 < a η * (baseProfile lam x + correction P (c η) x) := by
  obtain ⟨g, ε₀, C₀, hε₀, hC₀, hg, hg0, hspec⟩ := exists_normalized_compensation P lam hlam
  obtain ⟨D, hD, hbounds⟩ := compact_amplitude_within_bounds hS huniq ha hpos
  obtain ⟨J, hJ, hjet⟩ := correction_first_jet_bound P
  let B : ℝ := C₀ * D
  let T : ℝ := D * B + D * (J * B)
  let C : ℝ := 1 + B + T
  have hB : 0 < B := mul_pos hC₀ hD
  have hT : 0 < T := by dsimp [T]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hTC : T ≤ C := by dsimp [C]; linarith
  have hDBC : D * B ≤ C := by dsimp [T] at hTC; nlinarith [mul_pos hD (mul_pos hJ hB)]
  refine ⟨ε₀ / D, C, div_pos hε₀ hD, hC, ?_⟩
  intro v hv hvsmall
  let d : ℝ → Coeff := fun η => amplitudeDebt (a η) (v η)
  have hd : ContDiffOn ℝ ∞ d S := amplitudeDebt_variable_contDiffOn ha hpos hv
  have hd_bound : ∀ η ∈ S, ‖d η‖ ≤ D * ‖v η‖ ∧
      ‖derivWithin d S η‖ ≤ D * (‖v η‖ + ‖derivWithin v S η‖) := by
    intro η hη
    exact amplitudeDebt_variable_bounds huniq ha hpos hv
      (fun θ hθ => ⟨(hbounds θ hθ).1, (hbounds θ hθ).2.1⟩) hη
  have hmap : MapsTo d S (Metric.ball (0 : Coeff) ε₀) := by
    intro η hη
    change dist (d η) 0 < ε₀
    rw [dist_zero_right]
    apply (hd_bound η hη).1.trans_lt
    have ht := (lt_div_iff₀ hD).mp (hvsmall η hη)
    simpa only [mul_comm] using ht
  let c : ℝ → Coeff := g ∘ d
  have hc : ContDiffOn ℝ ∞ c S := hg.comp hd hmap
  refine ⟨c, hc, ?_⟩
  intro η hη
  let N : ℝ := ‖v η‖ + ‖derivWithin v S η‖
  have hN : 0 ≤ N := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hvN : ‖v η‖ ≤ N := le_add_of_nonneg_right (norm_nonneg _)
  have hm : d η ∈ Metric.ball (0 : Coeff) ε₀ := hmap hη
  have hval : ‖c η‖ ≤ B * ‖v η‖ := by
    exact ((hspec (d η) hm).2.1).trans
      (by simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left (hd_bound η hη).1 hC₀.le)
  have hdif : DifferentiableWithinAt ℝ d S η := (hd η hη).differentiableWithinAt (by simp)
  have hcdif : DifferentiableWithinAt ℝ c S η := (hc η hη).differentiableWithinAt (by simp)
  have hcderiv : ‖derivWithin c S η‖ ≤ B * N := by
    apply (composed_solver_derivWithin_bound hg (fun w hw => (hspec w hw).2.2.1)
      (huniq η hη) hdif hm).trans
    simpa only [B, N, mul_assoc] using mul_le_mul_of_nonneg_left (hd_bound η hη).2 hC₀.le
  have hcorr : ∀ x, |correction P (c η) x| ≤ B * ‖v η‖ ∧
      |deriv (correction P (c η)) x| ≤ B * ‖v η‖ := by
    intro x
    have hb : C₀ * ‖d η‖ ≤ B * ‖v η‖ := by
      simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left (hd_bound η hη).1 hC₀.le
    exact ⟨((hspec (d η) hm).2.2.2 x).1.1.trans hb,
      ((hspec (d η) hm).2.2.2 x).1.2.trans hb⟩
  refine ⟨(hspec (d η) hm).1,
    hval.trans (mul_le_mul_of_nonneg_right hBC (norm_nonneg _)),
    hcderiv.trans (mul_le_mul_of_nonneg_right hBC hN), ?_, ?_⟩
  · intro x
    have ha₀ : |a η| ≤ D := (hbounds η hη).2.2.1
    have ha₁ : |derivWithin a S η| ≤ D := (hbounds η hη).2.2.2
    have hparam : |correction P (derivWithin c S η) x| ≤ (J * B) * N := by
      exact ((hjet (derivWithin c S η) x).1).trans
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcderiv hJ.le)
    have hmul₀ : |a η * correction P (c η) x| ≤ (D * B) * ‖v η‖ := by
      rw [abs_mul]
      exact (mul_le_mul ha₀ (hcorr x).1 (abs_nonneg _) hD.le).trans_eq (by ring)
    have hmul₁ : |a η * deriv (correction P (c η)) x| ≤ (D * B) * ‖v η‖ := by
      rw [abs_mul]
      exact (mul_le_mul ha₀ (hcorr x).2 (abs_nonneg _) hD.le).trans_eq (by ring)
    have hsize : (D * B) * ‖v η‖ ≤ C * N :=
      (mul_le_mul_of_nonneg_right hDBC (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hvN hC.le)
    refine ⟨hmul₀.trans hsize, hmul₁.trans hsize, ?_⟩
    have hadif : DifferentiableWithinAt ℝ a S η := (ha η hη).differentiableWithinAt (by simp)
    have hfd : HasDerivWithinAt (fun θ => correction P (c θ) x)
        (correction P (derivWithin c S η) x) S η :=
      (correctionCLM P x).hasFDerivAt.comp_hasDerivWithinAt η hcdif.hasDerivWithinAt
    rw [(hadif.hasDerivWithinAt.fun_mul hfd).derivWithin (huniq η hη)]
    calc
      _ ≤ |derivWithin a S η * correction P (c η) x| +
          |a η * correction P (derivWithin c S η) x| := abs_add_le _ _
      _ ≤ D * (B * ‖v η‖) + D * ((J * B) * N) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul ha₁ (hcorr x).1 (abs_nonneg _) hD.le)
          (mul_le_mul ha₀ hparam (abs_nonneg _) hD.le)
      _ ≤ D * (B * N) + D * ((J * B) * N) := by
        apply add_le_add_left
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvN hB.le) hD.le
      _ = T * N := by dsimp [T]; ring
      _ ≤ C * N := mul_le_mul_of_nonneg_right hTC hN
  · intro x hx
    exact mul_pos (hpos η hη) (((hspec (d η) hm).2.2.2 x).2 hx)

/-- Change from the heat-switch normalization to a patch at radius `q*K`. -/
noncomputable def radiusRatioCLM (q : ℝ) : Coeff →L[ℝ] Coeff :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ![v 0, v 1 / q, v 2 / (q * Real.sqrt q)]
      map_add' := fun u v => by
        ext i
        fin_cases i <;> simp [Pi.add_apply, add_div]
      map_smul' := fun r v => by
        ext i
        fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, mul_div_assoc] }

theorem scaledDebt_radiusRatio (q K : ℝ) (hq : 0 < q) (d : Coeff) :
    scaledDebt (q * K) d = radiusRatioCLM q (scaledDebt K d) := by
  ext i
  fin_cases i
  · rfl
  · change d 1 / (q * K) = (d 1 / K) / q
    rw [div_div, mul_comm K q]
  · change d 2 / (q * K * Real.sqrt (2 * (q * K))) =
      (d 2 / (K * Real.sqrt (2 * K))) / (q * Real.sqrt q)
    rw [show 2 * (q * K) = q * (2 * K) by ring, Real.sqrt_mul hq.le, div_div]
    congr 1
    ring

theorem radiusRatio_derivWithin (q : ℝ) {S : Set ℝ} {v : ℝ → Coeff} {η : ℝ}
    (huniq : UniqueDiffWithinAt ℝ S η) (hv : DifferentiableWithinAt ℝ v S η) :
    derivWithin (fun θ => radiusRatioCLM q (v θ)) S η =
      radiusRatioCLM q (derivWithin v S η) :=
  ((radiusRatioCLM q).hasFDerivAt.comp_hasDerivWithinAt η hv.hasDerivWithinAt).derivWithin huniq

/-- The fixed ratio costs one bounded linear operator in both the value and
the actual parameter derivative. -/
theorem scaled_family_ratio_bounds (q : ℝ) (hq : 0 < q)
    {S : Set ℝ} (huniq : UniqueDiffOn ℝ S) (d : ℝ → ℝ → Coeff)
    (B : ℝ) (hB : 0 < B)
    (hreg : ∀ K : ℝ, 1 ≤ K → ContDiffOn ℝ ∞ (fun η => scaledDebt K (d K η)) S)
    (hbound : ∀ K : ℝ, 1 ≤ K → ∀ η ∈ S,
      ‖scaledDebt K (d K η)‖ ≤ B / K ∧
      ‖derivWithin (fun θ => scaledDebt K (d K θ)) S η‖ ≤ B / K) :
    ∃ Bq : ℝ, 0 < Bq ∧ ∀ K : ℝ, 1 ≤ K →
      ContDiffOn ℝ ∞ (fun η => scaledDebt (q * K) (d K η)) S ∧
      ∀ η ∈ S, ‖scaledDebt (q * K) (d K η)‖ ≤ Bq / K ∧
        ‖derivWithin (fun θ => scaledDebt (q * K) (d K θ)) S η‖ ≤ Bq / K := by
  let L : Coeff →L[ℝ] Coeff := radiusRatioCLM q
  let C : ℝ := ‖L‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hLC : ‖L‖ ≤ C := by dsimp [C]; linarith
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  intro K hK
  have heq : (fun η => scaledDebt (q * K) (d K η)) =
      (fun η => L (scaledDebt K (d K η))) :=
    funext fun η => scaledDebt_radiusRatio q K hq (d K η)
  rw [heq]
  refine ⟨L.contDiff.comp_contDiffOn (hreg K hK), ?_⟩
  intro η hη
  have hnorm : ∀ v : Coeff, ‖L v‖ ≤ C * ‖v‖ := fun v =>
    (L.le_opNorm v).trans (mul_le_mul_of_nonneg_right hLC (norm_nonneg v))
  constructor
  · rw [scaledDebt_radiusRatio q K hq]
    exact (hnorm _).trans
      (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hbound K hK η hη).1 hC.le)
  · rw [radiusRatio_derivWithin q (huniq η hη)
      (((hreg K hK) η hη).differentiableWithinAt (by simp))]
    exact (hnorm _).trans
      (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hbound K hK η hη).2 hC.le)

/-- Uniform `O(1/K)` value and derivative bounds for a nonconstant physical
debt family give exact compensation with the same first-jet cost. -/
theorem exists_compensation_for_scaled_family (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam)
    (q : ℝ) (hq : 0 < q) {S : Set ℝ} (hS : IsCompact S) (huniq : UniqueDiffOn ℝ S)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a S) (hpos : ∀ η ∈ S, 0 < a η)
    (d : ℝ → ℝ → Coeff) (B : ℝ) (hB : 0 < B)
    (hreg : ∀ K : ℝ, 1 ≤ K → ContDiffOn ℝ ∞ (fun η => scaledDebt (q * K) (d K η)) S)
    (hbound : ∀ K : ℝ, 1 ≤ K → ∀ η ∈ S,
      ‖scaledDebt (q * K) (d K η)‖ ≤ B / K ∧
      ‖derivWithin (fun θ => scaledDebt (q * K) (d K θ)) S η‖ ≤ B / K) :
    ∃ K₀ C : ℝ, 0 < K₀ ∧ 0 < C ∧ ∀ K : ℝ, K₀ ≤ K →
      ∃ c : ℝ → Coeff, ContDiffOn ℝ ∞ c S ∧ ∀ η ∈ S,
        physicalMoments P lam (q * K) (a η) (c η) + d K η = 0 ∧
        ‖c η‖ ≤ C / K ∧ ‖derivWithin c S η‖ ≤ C / K ∧
        FirstJetWithinBound P a c S η (C / K) ∧
        ∀ X : ℝ, 0 < X → 0 < physicalProfile P lam (q * K) (a η) (c η) X := by
  obtain ⟨ε, C₁, hε, hC₁, hsolve⟩ := exists_variable_compensation P lam hlam hS huniq a ha hpos
  let K₀ : ℝ := max 1 (1 + B / ε)
  have hK₀ : 0 < K₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨K₀, 2 * C₁ * B, hK₀, by positivity, ?_⟩
  intro K hlarge
  have hKone : 1 ≤ K := (le_max_left _ _).trans hlarge
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hKone
  have hqK : 0 < q * K := mul_pos hq hK
  let v : ℝ → Coeff := fun η => scaledDebt (q * K) (d K η)
  have hsmall : B / K < ε := by
    apply (div_lt_iff₀ hK).mpr
    have hk' : B / ε < K := by
      have ht := (le_max_right 1 (1 + B / ε)).trans hlarge
      linarith
    have ht := (div_lt_iff₀ hε).mp hk'
    simpa only [mul_comm] using ht
  obtain ⟨c, hc, hspec⟩ := hsolve v (hreg K hKone)
    (fun η hη => ((hbound K hKone η hη).1).trans_lt hsmall)
  refine ⟨c, hc, ?_⟩
  intro η hη
  have hs := hspec η hη
  have hv : ‖v η‖ ≤ B / K := (hbound K hKone η hη).1
  have hvd : ‖derivWithin v S η‖ ≤ B / K := (hbound K hKone η hη).2
  have hcost : C₁ * (‖v η‖ + ‖derivWithin v S η‖) ≤ 2 * C₁ * B / K := by
    calc
      _ ≤ C₁ * (B / K + B / K) := mul_le_mul_of_nonneg_left (add_le_add hv hvd) hC₁.le
      _ = _ := by ring
  have hcost₀ : C₁ * ‖v η‖ ≤ 2 * C₁ * B / K :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) hC₁.le).trans hcost
  have hmoment : momentMap P lam (c η) = normalizedDebt (q * K) (a η) (d K η) := by
    rw [normalizedDebt_eq]
    exact hs.1
  refine ⟨physicalMoments_cancel P lam (q * K) (a η) hqK (hpos η hη) (c η) (d K η) hmoment,
    hs.2.1.trans hcost₀, hs.2.2.1.trans hcost, hs.2.2.2.1.mono hcost, ?_⟩
  intro X hX
  exact hs.2.2.2.2 (X / (q * K)) (div_pos hX hqK)

/-- Input may be normalized at the heat switch itself; the proved ratio map
transports both required bounds to the reserved patch. -/
theorem exists_compensation_for_switch_family (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam)
    (q : ℝ) (hq : 0 < q) {S : Set ℝ} (hS : IsCompact S) (huniq : UniqueDiffOn ℝ S)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a S) (hpos : ∀ η ∈ S, 0 < a η)
    (d : ℝ → ℝ → Coeff) (B : ℝ) (hB : 0 < B)
    (hreg : ∀ K : ℝ, 1 ≤ K → ContDiffOn ℝ ∞ (fun η => scaledDebt K (d K η)) S)
    (hbound : ∀ K : ℝ, 1 ≤ K → ∀ η ∈ S,
      ‖scaledDebt K (d K η)‖ ≤ B / K ∧
      ‖derivWithin (fun θ => scaledDebt K (d K θ)) S η‖ ≤ B / K) :
    ∃ K₀ C : ℝ, 0 < K₀ ∧ 0 < C ∧ ∀ K : ℝ, K₀ ≤ K →
      ∃ c : ℝ → Coeff, ContDiffOn ℝ ∞ c S ∧ ∀ η ∈ S,
        physicalMoments P lam (q * K) (a η) (c η) + d K η = 0 ∧
        ‖c η‖ ≤ C / K ∧ ‖derivWithin c S η‖ ≤ C / K ∧
        FirstJetWithinBound P a c S η (C / K) ∧
        ∀ X : ℝ, 0 < X → 0 < physicalProfile P lam (q * K) (a η) (c η) X := by
  obtain ⟨Bq, hBq, hdata⟩ := scaled_family_ratio_bounds q hq huniq d B hB hreg hbound
  exact exists_compensation_for_scaled_family P lam hlam q hq hS huniq a ha hpos d Bq hBq
    (fun K hK => (hdata K hK).1) (fun K hK => (hdata K hK).2)

/-- Inside the parameter domain these bounds are on ordinary derivatives. -/
theorem interior_first_jet {P : Patch} {S : Set ℝ} {a : ℝ → ℝ} {c : ℝ → Coeff}
    {η L : ℝ} (hS : S ∈ 𝓝 η) (hc : ‖derivWithin c S η‖ ≤ L)
    (hE : FirstJetWithinBound P a c S η L) :
    ‖deriv c η‖ ≤ L ∧ FirstJetBound P a c η L := by
  exact ⟨by simpa only [derivWithin_of_mem_nhds hS] using hc, hE.toFirstJetBound hS⟩

theorem scaled_triple_contDiffOn {S : Set ℝ} (K : ℝ) {p e i : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ p S) (he : ContDiffOn ℝ ∞ e S) (hi : ContDiffOn ℝ ∞ i S) :
    ContDiffOn ℝ ∞ (fun η => scaledDebt K ![p η, e η, i η]) S := by
  apply contDiffOn_pi.mpr
  intro j
  fin_cases j
  · exact hp
  · exact he.div_const K
  · exact hi.div_const (K * Real.sqrt (2 * K))

theorem angular_scaling_bound {K B u : ℝ} (hK : 0 < K) (hB : 0 ≤ B)
    (hu : |u| ≤ B * Real.sqrt K) : |u / (K * Real.sqrt (2 * K))| ≤ B / K := by
  have hroot : 0 < Real.sqrt (2 * K) := Real.sqrt_pos.2 (by positivity)
  have hden : 0 < K * Real.sqrt (2 * K) := mul_pos hK hroot
  rw [abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  calc
    |u| ≤ B * Real.sqrt K := hu
    _ ≤ B * Real.sqrt (2 * K) := mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by linarith)) hB
    _ = (B / K) * (K * Real.sqrt (2 * K)) := by field_simp

theorem scaled_triple_norm_bound {K B p e i : ℝ} (hK : 0 < K) (hB : 0 ≤ B)
    (hp : |p| ≤ B / K) (he : |e| ≤ B) (hi : |i| ≤ B * Real.sqrt K) :
    ‖scaledDebt K ![p, e, i]‖ ≤ B / K := by
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hB hK.le)).mpr
  intro j
  fin_cases j
  · exact hp
  · change |e / K| ≤ B / K
    rw [abs_div, abs_of_pos hK]
    exact div_le_div_of_nonneg_right he hK.le
  · exact angular_scaling_bound hK hB hi

theorem scaled_triple_derivWithin {S : Set ℝ} (K : ℝ) {p e i : ℝ → ℝ} {η : ℝ}
    (huniq : UniqueDiffWithinAt ℝ S η)
    (hp : DifferentiableWithinAt ℝ p S η) (he : DifferentiableWithinAt ℝ e S η)
    (hi : DifferentiableWithinAt ℝ i S η) :
    derivWithin (fun θ => scaledDebt K ![p θ, e θ, i θ]) S η =
      scaledDebt K ![derivWithin p S η, derivWithin e S η, derivWithin i S η] := by
  apply HasDerivWithinAt.derivWithin _ huniq
  apply hasDerivWithinAt_pi.mpr
  intro j
  fin_cases j
  · exact hp.hasDerivWithinAt
  · exact he.hasDerivWithinAt.div_const K
  · exact hi.hasDerivWithinAt.div_const (K * Real.sqrt (2 * K))

/-- Scalar physical estimates at their natural three scales give the vector
estimate required by the compensation solver, including the actual derivative. -/
theorem scaled_triple_first_jet_bound {S : Set ℝ} {K B : ℝ} {p e i : ℝ → ℝ} {η : ℝ}
    (hK : 0 < K) (hB : 0 ≤ B) (huniq : UniqueDiffWithinAt ℝ S η)
    (hp : DifferentiableWithinAt ℝ p S η) (he : DifferentiableWithinAt ℝ e S η)
    (hi : DifferentiableWithinAt ℝ i S η)
    (hpb : |p η| ≤ B / K ∧ |derivWithin p S η| ≤ B / K)
    (heb : |e η| ≤ B ∧ |derivWithin e S η| ≤ B)
    (hib : |i η| ≤ B * Real.sqrt K ∧ |derivWithin i S η| ≤ B * Real.sqrt K) :
    ‖scaledDebt K ![p η, e η, i η]‖ ≤ B / K ∧
      ‖derivWithin (fun θ => scaledDebt K ![p θ, e θ, i θ]) S η‖ ≤ B / K := by
  refine ⟨scaled_triple_norm_bound hK hB hpb.1 heb.1 hib.1, ?_⟩
  rw [scaled_triple_derivWithin K huniq hp he hi]
  exact scaled_triple_norm_bound hK hB hpb.2 heb.2 hib.2

/-- The actual three physical debts use the diffusion parameter `1-η²`. -/
noncomputable def physicalDebt (T : OutgoingTail.TailData) (K η : ℝ) : Coeff :=
  ![ParametricHeatTail.physicalPressure T K η,
    ParametricHeatTail.physicalEnergy T K η,
    ParametricHeatTail.physicalAngular T K η]

theorem physicalDebt_eq_actual (T : OutgoingTail.TailData) (K η : ℝ) :
    physicalDebt T K η =
      ![HeatTailEdit.pressureDebt (HeatTailEdit.outgoingProfile T K η) T.h (1 - η ^ 2) K,
        HeatTailEdit.energyDebt (HeatTailEdit.outgoingProfile T K η) T.h (1 - η ^ 2) K,
        HeatTailEdit.angularDebt (HeatTailEdit.outgoingProfile T K η) T.h (1 - η ^ 2) K] := rfl

theorem physical_scaled_debt_contDiffOn (T : OutgoingTail.TailData) {K : ℝ} (hK : 1 ≤ K) :
    ContDiffOn ℝ ∞ (fun η => scaledDebt K (physicalDebt T K η)) (Icc (-1 : ℝ) 1) :=
  scaled_triple_contDiffOn K (ParametricHeatTail.physicalPressure_contDiffOn T hK)
    (ParametricHeatTail.physicalEnergy_contDiffOn T hK)
    (ParametricHeatTail.physicalAngular_contDiffOn T hK)

/-- Both estimates concern the actual nonconstant physical debt. -/
theorem physical_scaled_debt_C1_bounds (T : OutgoingTail.TailData) :
    ∃ B : ℝ, 0 < B ∧ ∀ K : ℝ, 1 ≤ K → ∀ η ∈ Icc (-1 : ℝ) 1,
      ‖scaledDebt K (physicalDebt T K η)‖ ≤ B / K ∧
      ‖derivWithin (fun θ => scaledDebt K (physicalDebt T K θ)) (Icc (-1 : ℝ) 1) η‖ ≤ B / K := by
  obtain ⟨B, hB, hb⟩ := ParametricHeatTail.exists_physical_debt_C1_bounds T
  refine ⟨B, hB, ?_⟩
  intro K hK η hη
  rcases hb K hK η hη with ⟨hp, hp', he, he', hi, hi'⟩
  exact scaled_triple_first_jet_bound (lt_of_lt_of_le zero_lt_one hK) hB.le
    ((uniqueDiffOn_Icc (by norm_num)) η hη)
    (((ParametricHeatTail.physicalPressure_contDiffOn T hK) η hη).differentiableWithinAt (by simp))
    (((ParametricHeatTail.physicalEnergy_contDiffOn T hK) η hη).differentiableWithinAt (by simp))
    (((ParametricHeatTail.physicalAngular_contDiffOn T hK) η hη).differentiableWithinAt (by simp))
    ⟨hp, hp'⟩ ⟨he, he'⟩ ⟨hi, hi'⟩

/-- The physical heat edit with diffusion `1-η²` allows exact three-moment
compensation, including the closed parameter endpoints and uniform first jets. -/
theorem exists_physical_heat_compensation (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam)
    (T : OutgoingTail.TailData) (q : ℝ) (hq : 0 < q)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a (Icc (-1 : ℝ) 1))
    (hpos : ∀ η ∈ Icc (-1 : ℝ) 1, 0 < a η) :
    ∃ K₀ C : ℝ, 0 < K₀ ∧ 0 < C ∧ ∀ K : ℝ, K₀ ≤ K →
      ∃ c : ℝ → Coeff, ContDiffOn ℝ ∞ c (Icc (-1 : ℝ) 1) ∧
        ∀ η ∈ Icc (-1 : ℝ) 1,
          physicalMoments P lam (q * K) (a η) (c η) + physicalDebt T K η = 0 ∧
          ‖c η‖ ≤ C / K ∧ ‖derivWithin c (Icc (-1 : ℝ) 1) η‖ ≤ C / K ∧
          FirstJetWithinBound P a c (Icc (-1 : ℝ) 1) η (C / K) ∧
          ∀ X : ℝ, 0 < X → 0 < physicalProfile P lam (q * K) (a η) (c η) X := by
  obtain ⟨B, hB, hb⟩ := physical_scaled_debt_C1_bounds T
  exact exists_compensation_for_switch_family P lam hlam q hq isCompact_Icc
    (uniqueDiffOn_Icc (by norm_num)) a ha hpos (physicalDebt T) B hB
    (fun K hK => physical_scaled_debt_contDiffOn T hK) hb

end NavierStokes.ParametricTerminalCompensation
