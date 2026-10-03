/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HmAdapter
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DissipationCoordinateL2
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.WordLinearCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateClassicalFamily
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureGradientDiffusion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoordinateProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordDiffusion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales

/-! # Per-iterate spatial jets of the S-amplitude

The AMNR engine consumes `L²` bounds on the spatial words of `amnrTGradient (T i) p` over the
time-cell product measure, for every partial iterate `T i`, `i ≤ Nstar β`.  Upstream supplies
the dissipation `spaceTimeGradNormSq` of the iterate spatial words of `θprev` (profile) and of
the increments `V_j = T j - T (j-1)` (amplitude theorem).  This file proves the adapter:

* a single-function bridge from a spatial dissipation bound to the `L²` bound of the actual
  `amnrWord` of `amnrTGradient u p`, for any `u` that is smooth up to the initial time;
* telescoping `T i = ∑_{j ≤ i} V_j` at the level of `eLpNorm`;
* the scalar bookkeeping at the scales `ε_{m-1}` and the final adapter
  `relative_iterate_gradient_jets`. -/

@[expose] public section

noncomputable section

open Homogenization MeasureTheory Set

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section4

/-- The time-cell product measure on `(0,1] × (0,1)²`. -/
abbrev unitCellMeasure : Measure AmnrSpace :=
  (volume.restrict (uIoc (0 : ℝ) 1)).prod (volume.restrict unitCube)

theorem iterateSpatialWord_eq_amnrSpaceWord (w : List (Fin 2)) (f : Vec 2 → ℝ) :
    iterateSpatialWord w f = amnrSpaceWord w f := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    simp only [iterateSpatialWord, amnrSpaceWord, ih]
    rfl

theorem spaceTimeGradNormSq_nonneg (Dθ : ℝ → Vec 2 → Vec 2) : 0 ≤ spaceTimeGradNormSq Dθ := by
  apply integral_nonneg
  intro z
  unfold vecNormSq vecDot
  exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

/-- The actual gradient is smooth on the open positive-time domain once the function
is smooth up to the initial time. -/
theorem tGradient_contDiffOn {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (p : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (amnrTGradient u p) (Ioi (0 : ℝ) ×ˢ univ) :=
  (amnr_energy_spatial_partial_smooth_up_to_initial hu p).mono
    (prod_mono Ioi_subset_Ici_self subset_rfl)

/-- On the product measure, the actual spatial word of the gradient is the coordinate
of the gradient of the spatial word of the slices. -/
theorem amnrWord_tGradient_ae_eq {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (b : AmnrSpace → Vec 2) (p : Fin 2) (α : List (Fin 2)) :
    amnrWord b (α.map some) (amnrTGradient u p) =ᵐ[unitCellMeasure]
      (fun z : AmnrSpace => spaceGrad (amnrSpaceWord α (u z.1)) z.2 p) := by
  have hμ := amnr_time_cell_product_absolutelyContinuous (T := 1) zero_le_one
  apply ((ae_restrict_mem (isOpen_Ioi.prod isOpen_univ).measurableSet).filter_mono
    hμ.ae_le).mono
  intro z hz
  have hz0 : (0 : ℝ) < z.1 := hz.1
  have hs : ContDiff ℝ (⊤ : ℕ∞) (u z.1) := hu.comp_contDiff
    (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (z.1, x)))
    (fun x => ⟨hz0.le, mem_univ x⟩)
  exact (amnrWord_spatial_slice_on_vertical_domain (isOpen_Ioi.prod isOpen_univ)
    (tGradient_contDiffOn hu p) b α z.1 (fun x => ⟨hz.1, mem_univ x⟩) z.2).trans
      (congrFun (amnrSpaceWord_coordinate_derivative hs α p) z.2)

/-- Bridge: the spatial dissipation of `u` bounds the `L²` norm of every actual spatial word
of its gradient on the unit time-cell product. -/
theorem amnrWord_tGradient_eLpNorm_le {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (b : AmnrSpace → Vec 2) (p : Fin 2) (α : List (Fin 2)) :
    eLpNorm (amnrWord b (α.map some) (amnrTGradient u p)) 2 unitCellMeasure ≤
      ENNReal.ofReal (Real.sqrt (spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord α (u t))))) := by
  have hT : (0 : ℝ) ≤ 1 := zero_le_one
  have hw := amnrSpaceWord_smooth_up_to_initial hu α
  have hg := amnr_energy_spatial_partial_smooth_up_to_initial hw p
  have hm : AEStronglyMeasurable (fun z : AmnrSpace =>
      spaceGrad (amnrSpaceWord α (u z.1)) z.2 p) unitCellMeasure :=
    (hg.continuousOn.aestronglyMeasurable (measurableSet_Ici.prod MeasurableSet.univ)
      (μ := volume)).mono_ac (amnr_time_cell_product_absolutelyContinuous_closed hT)
  have hint : Integrable (fun z : AmnrSpace => vecNormSq
      (spaceGrad (amnrSpaceWord α (u z.1)) z.2)) unitCellMeasure := by
    apply amnr_time_cell_product_integrable _ hT
    exact continuousOn_finsetSum Finset.univ
      (fun q _ => (amnr_energy_spatial_partial_smooth_up_to_initial hw q).continuousOn.mul
        (amnr_energy_spatial_partial_smooth_up_to_initial hw q).continuousOn)
  have hSTG : (∫ z, vecNormSq (spaceGrad (amnrSpaceWord α (u z.1)) z.2) ∂unitCellMeasure) =
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord α (u t))) := by
    unfold spaceTimeGradNormSq unitCellMeasure
    simp only [iterateSpatialWord_eq_amnrSpaceWord]
    rw [amnr_product_measure_eq_timeCube]
  have hh := amnr_coordinate_eLpNorm_two_le_of_dissipation
    (g := fun z : AmnrSpace => spaceGrad (amnrSpaceWord α (u z.1)) z.2) p hm hint
    (Real.sqrt_nonneg _)
    (by rw [hSTG, Real.sq_sqrt (spaceTimeGradNormSq_nonneg _)])
  rw [eLpNorm_congr_ae (amnrWord_tGradient_ae_eq hu b p α)]
  exact hh

/-- A finite decomposition of a temperature into smooth pieces decomposes every actual
spatial word of its gradient on the positive-time domain. -/
theorem amnrWord_tGradient_sum_eqOn {V : ℕ → ℝ → Vec 2 → ℝ} {T : ℝ → Vec 2 → ℝ}
    (s : Finset ℕ)
    (hV : ∀ j ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => V j z.1 z.2)
      (Ici (0 : ℝ) ×ˢ univ))
    (hT : ∀ t x, T t x = ∑ j ∈ s, V j t x)
    (b : AmnrSpace → Vec 2) (p : Fin 2) (α : List (Fin 2)) :
    EqOn (amnrWord b (α.map some) (amnrTGradient T p))
      (∑ j ∈ s, amnrWord b (α.map some) (amnrTGradient (V j) p))
      (Ioi (0 : ℝ) ×ˢ univ) := by
  let U : Set AmnrSpace := Ioi (0 : ℝ) ×ˢ univ
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hgrad : EqOn (amnrTGradient T p) (∑ j ∈ s, amnrTGradient (V j) p) U := by
    intro z hz
    have hz0 : (0 : ℝ) < z.1 := hz.1
    have hd : ∀ j ∈ s, DifferentiableAt ℝ (V j z.1) z.2 := by
      intro j hj
      exact ((hV j hj).comp_contDiff
        (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (z.1, x)))
        (fun x => ⟨hz0.le, mem_univ x⟩)).differentiable (by simp) z.2
    have hfun : T z.1 = fun x => ∑ j ∈ s, V j z.1 x := funext (hT z.1)
    simp only [Finset.sum_apply, amnrTGradient, spaceGrad]
    rw [hfun, fderiv_fun_sum hd]
    simp only [sum_apply]
  have hb : ContDiffOn ℝ ((α.length : ℕ) : WithTop ℕ∞)
      (fun _ : AmnrSpace => (0 : Vec 2)) U := contDiffOn_const
  have h1 := amnrWord_congr (b := fun _ => (0 : Vec 2)) hU hgrad (α.map some)
  have h2 := amnrWord_sum hU hb s (fun j => amnrTGradient (V j) p)
    (fun j hj => ((tGradient_contDiffOn (hV j hj) p).of_le (by simp)))
    (α.map some) (by simp)
  intro z hz
  rw [amnrWord_spatial_independent b (fun _ => (0 : Vec 2)), h1 hz, h2 hz]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrFun (amnrWord_spatial_independent (fun _ => (0 : Vec 2)) b α _) z

/-- Telescoped `L²` bound: the gradient word of `T` is bounded by the sum of the
dissipation bounds of the pieces. -/
theorem amnrWord_tGradient_eLpNorm_sum_le {V : ℕ → ℝ → Vec 2 → ℝ} {T : ℝ → Vec 2 → ℝ}
    (s : Finset ℕ)
    (hV : ∀ j ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => V j z.1 z.2)
      (Ici (0 : ℝ) ×ˢ univ))
    (hT : ∀ t x, T t x = ∑ j ∈ s, V j t x)
    (b : AmnrSpace → Vec 2) (p : Fin 2) (α : List (Fin 2)) :
    eLpNorm (amnrWord b (α.map some) (amnrTGradient T p)) 2 unitCellMeasure ≤
      ∑ j ∈ s, ENNReal.ofReal (Real.sqrt (spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord α (V j t))))) := by
  have hμ := amnr_time_cell_product_absolutelyContinuous (T := 1) zero_le_one
  have hae : amnrWord b (α.map some) (amnrTGradient T p) =ᵐ[unitCellMeasure]
      ∑ j ∈ s, amnrWord b (α.map some) (amnrTGradient (V j) p) := by
    apply ((ae_restrict_mem (isOpen_Ioi.prod isOpen_univ).measurableSet).filter_mono
      hμ.ae_le).mono
    intro z hz
    exact amnrWord_tGradient_sum_eqOn s hV hT b p α hz
  rw [eLpNorm_congr_ae hae]
  refine (eLpNorm_sum_le (by norm_num)).trans ?_
  exact Finset.sum_le_sum (fun j hj => amnrWord_tGradient_eLpNorm_le (hV j hj) b p α)

/-! ### Scalar bookkeeping -/

/-- At the profile scale `E^{1+γ/2} ≤ Rθ` the two maxima in the amplitude theorem collapse. -/
theorem iterate_jets_scale_simplify {e γ R C : ℝ} (he : 0 < e) (hC : 0 < C)
    (hscale : e ^ (1 + γ / 2) ≤ R) :
    max 1 (e ^ (2 + γ) * R ^ (-2 : ℤ)) = 1 ∧
      max (C * e ^ (-1 - γ / 2)) (C / R) = C * e ^ (-1 - γ / 2) := by
  have hrp : 0 < e ^ (1 + γ / 2) := Real.rpow_pos_of_pos he _
  have hR : 0 < R := hrp.trans_le hscale
  have hid : e ^ (2 + γ) = (e ^ (1 + γ / 2)) ^ 2 := by
    rw [← Real.rpow_mul_natCast he.le]
    congr 1
    push_cast
    ring
  have hs := pow_le_pow_left₀ hrp.le hscale 2
  constructor
  · apply max_eq_left
    rw [hid, zpow_neg, zpow_two, ← pow_two, mul_inv_le_iff₀ (sq_pos_of_pos hR)]
    simpa only [one_mul] using hs
  · apply max_eq_left
    have hneg : e ^ (-1 - γ / 2) = (e ^ (1 + γ / 2))⁻¹ := by
      rw [← Real.rpow_neg he.le]
      congr 1
      ring
    rw [hneg, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hrp hscale) hC.le

/-- `ε^δ ≤ K⁻¹` once `Λ ≥ K^{1/δ}`. -/
theorem iterate_jets_epsilon_rpow_delta_le {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) {m : ℕ} (hm : 1 ≤ m) {K : ℝ} (hK : 0 < K)
    (hbig : K ^ (1 / delta β) ≤ (Λ : ℝ)) :
    epsilon β Λ m ^ delta β ≤ K⁻¹ := by
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  have hΛ0 : (0 : ℝ) < Λ := by
    have : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
    linarith
  have hε := LeftToShow.epsilon_le_inv_Lambda hβ hβ' hΛ hm
  have hε0 : 0 ≤ epsilon β Λ m := (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le
  have h1 : epsilon β Λ m ^ delta β ≤ ((Λ : ℝ)⁻¹) ^ delta β :=
    Real.rpow_le_rpow hε0 hε hδ.le
  have h4 : K ≤ (Λ : ℝ) ^ delta β := by
    have := Real.rpow_le_rpow (by positivity) hbig hδ.le
    rwa [← Real.rpow_mul hK.le, one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one] at this
  rw [Real.inv_rpow hΛ0.le] at h1
  exact h1.trans (inv_anti₀ hK h4)

/-- The amplitude profile is at most one for a smallness parameter in `[0,1]`. -/
theorem iterateAmplitude_le_one {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (i : ℕ) :
    iterateAmplitude η i ≤ 1 := by
  unfold iterateAmplitude
  split_ifs
  · exact le_rfl
  · exact h1
  · exact Real.rpow_le_one h0 h1 (by positivity)

theorem iterateAnalyticWeight_le {n i k : ℕ} {L : ℝ} (hL : 0 ≤ L) (hn : n ≤ k) (hi : i ≤ k) :
    iterateAnalyticWeight n i L ≤ ((3 * k).factorial : ℝ) * L ^ n := by
  unfold iterateAnalyticWeight
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL n)
  exact_mod_cast Nat.factorial_le (by omega)

theorem iterateAnalyticWeight_nonneg {n i : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ iterateAnalyticWeight n i L := by
  unfold iterateAnalyticWeight
  positivity

/-- Dissipation bound from the profile shape, in square-root form. -/
theorem sqrt_stg_le_of_profile {G N κ W : ℝ} (hN : 0 ≤ N) (hκ : 0 < κ)
    (hW : 0 ≤ W) (h : G ≤ (N / Real.sqrt κ) ^ 2 * W ^ 2) :
    Real.sqrt G ≤ N / Real.sqrt κ * W := by
  have hy : 0 ≤ N / Real.sqrt κ * W := by positivity
  rw [Real.sqrt_le_iff]
  exact ⟨hy, by rw [mul_pow]; exact h⟩

/-- Dissipation bound from the amplitude shape. -/
theorem sqrt_stg_le_of_amplitude {G P N κ A W : ℝ} (hP : 0 ≤ P)
    (hN : 0 ≤ N) (hκ : 0 < κ) (hW : 0 ≤ W) (hA : A ≤ 1)
    (h : P + Real.sqrt κ * G ≤ N * A * W) :
    G ≤ N / Real.sqrt κ * W := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have h1 : Real.sqrt κ * G ≤ N * W := by
    have : N * A * W ≤ N * W := by
      have : A * (N * W) ≤ 1 * (N * W) :=
        mul_le_mul_of_nonneg_right hA (mul_nonneg hN hW)
      linarith only [this]
    linarith only [h, hP, this]
  rw [div_mul_eq_mul_div, le_div_iff₀ hs]
  linarith only [h1]

/-! ### Regularity of the increments -/

/-- Every increment `V_j = T j - T (j-1)` (with `V_0 = θprev`) is smooth up to the initial time. -/
theorem iterateIncrement_contDiffOn {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) {j : ℕ} (hj : j ≤ Nstar β) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => iterateIncrement T j z.1 z.2)
      (Ici (0 : ℝ) ×ˢ univ) := by
  cases j with
  | zero =>
    rw [iterateIncrement_zero, hT.1]
    exact hθ.1
  | succ j =>
    obtain ⟨_, h1⟩ := amnr_tIterates_classical_family I hΦ hθ hT (j + 1) hj
    obtain ⟨_, h0⟩ := amnr_tIterates_classical_family I hΦ hθ hT j (by omega)
    rw [iterateIncrement_succ]
    exact h1.1.sub h0.1

/-! ### The adapter -/

/-- **Relative step inputs.** The θ profile and the V-increment amplitude conclusion supply the
positive spatial jets of the gradient of every partial iterate `T i`, `i ≤ Nstar β`, in
the form consumed by the AMNR engine. -/
theorem relative_iterate_gradient_jets (β Cs : ℝ) (hCs : 0 < Cs) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∃ Λ₀ : ℝ, ∀ I : Ingredients β, Λ₀ ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, ∀ M : ℕ, ∀ m : ℕ, 2 ≤ m →
      ∀ (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        0 < I.kappaSeq κ M m → 0 < I.kappaSeq κ M (m - 1) →
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
      ∀ (N Rθ : ℝ), 0 ≤ N →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ →
        Infra.Section4.iterateCoordinateEnergyProfile θprev (I.kappaSeq κ M (m - 1)) N
          (Cs * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0 →
        (∀ i, 1 ≤ i → i ≤ Nstar β → ∀ v w : List (Fin 2), v.length = w.length →
          ∀ s, 0 ≤ s → s ≤ 1 →
          Real.sqrt (l2NormSq (Infra.Section4.iterateSpatialWord v
              (Infra.Section4.iterateIncrement T i s))) +
            Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq
              (fun t => spaceGrad (Infra.Section4.iterateSpatialWord w
                (Infra.Section4.iterateIncrement T i t)))) ≤
          N * Infra.Section4.iterateAmplitude
            (Cs ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
              max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * Rθ ^ (-2 : ℤ))) i *
            Infra.Section4.iterateAnalyticWeight v.length i
              (max (Cs * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (Cs / Rθ))) →
      ∀ i, i ≤ Nstar β → ∀ (p : Fin 2) (α : List (Fin 2)), α.length ≤ Nstar β →
        eLpNorm (Infra.Section4.amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
            (α.map some) (Infra.Section4.amnrTGradient (T i) p)) 2
          ((volume.restrict (Set.uIoc 0 1)).prod (volume.restrict unitCube)) ≤
        ENNReal.ofReal (Cg * N / Real.sqrt (I.kappaSeq κ M (m - 1)) *
          (max Cs 1 * epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ α.length) := by
  refine ⟨((Nstar β : ℝ) + 1) * ((3 * Nstar β).factorial : ℝ), by positivity,
    (max 1 (Cs ^ 3)) ^ (1 / delta β), ?_⟩
  intro I hΛ Φ hΦ κ M m hm θ₀ θprev T _ hκp hθ hT N Rθ hN hRθ hTheta hV i hi p α hα
  have hE : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hK : 0 < max 1 (Cs ^ 3) := lt_max_of_lt_left one_pos
  have hεδ := iterate_jets_epsilon_rpow_delta_le I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1) (by omega) hK hΛ
  have hε1 : epsilon β I.Λ (m - 1) ≤ 1 := by
    have h1 := LeftToShow.epsilon_le_inv_Lambda I.one_lt_beta I.beta_lt I.two_pow_seven_le
      (m := m - 1) (by omega)
    have h128 : (1 : ℝ) ≤ I.Λ := by
      have : (128 : ℝ) ≤ I.Λ := by exact_mod_cast I.two_pow_seven_le
      linarith only [this]
    exact h1.trans (inv_le_one_of_one_le₀ h128)
  have hδ := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hρ0 : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) := Real.rpow_nonneg hE.le _
  have hρ : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ epsilon β I.Λ (m - 1) ^ delta β := by
    apply Real.rpow_le_rpow_of_exponent_ge hE hε1
    linarith only [hδ]
  have hη1 : Cs ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 := by
    have h1 : Cs ^ 3 ≤ max 1 (Cs ^ 3) := le_max_right _ _
    calc Cs ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β)
        ≤ max 1 (Cs ^ 3) * (max 1 (Cs ^ 3))⁻¹ :=
          mul_le_mul h1 (hρ.trans hεδ) hρ0 hK.le
      _ = 1 := mul_inv_cancel₀ hK.ne'
  have hη0 : 0 ≤ Cs ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by positivity
  obtain ⟨hmax1, hmax2⟩ := iterate_jets_scale_simplify hE hCs hRθ
  rw [hmax1] at hV
  rw [hmax2] at hV
  set κp := I.kappaSeq κ M (m - 1) with hκp_def
  set E := epsilon β I.Λ (m - 1) with hE_def
  set L := Cs * E ^ (-1 - gamma β / 2) with hL_def
  have hL : 0 < L := by positivity
  have hLle : L ≤ max Cs 1 * E ^ (-(1 + gamma β / 2)) := by
    have : -1 - gamma β / 2 = -(1 + gamma β / 2) := by ring
    rw [hL_def, this]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hE.le _)
  -- the pieces
  have hfact : (0 : ℝ) ≤ ((3 * Nstar β).factorial : ℝ) := by positivity
  have hpiece : ∀ j ∈ Finset.range (i + 1), Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord α (iterateIncrement T j t)))) ≤
        N / Real.sqrt κp * (((3 * Nstar β).factorial : ℝ) * L ^ α.length) := by
    intro j hj
    have hjN : j ≤ Nstar β := by have := Finset.mem_range.mp hj; omega
    have hW := iterateAnalyticWeight_le (i := j) hL.le hα hjN
    have hWn := iterateAnalyticWeight_nonneg (n := α.length) (i := j) hL.le
    have hc : 0 ≤ N / Real.sqrt κp := by positivity
    by_cases hj0 : j = 0
    · subst hj0
      rw [iterateIncrement_zero, hT.1]
      exact (sqrt_stg_le_of_profile hN hκp hWn (hTheta.2 α)).trans
        (mul_le_mul_of_nonneg_left hW hc)
    · have h := hV j (by omega) hjN α α rfl 0 le_rfl zero_le_one
      exact (sqrt_stg_le_of_amplitude (Real.sqrt_nonneg _) hN hκp hWn
        (iterateAmplitude_le_one hη0 (by simpa only [mul_one] using hη1) j)
        (by simpa only [mul_one] using h)).trans (mul_le_mul_of_nonneg_left hW hc)
  have hsum := amnrWord_tGradient_eLpNorm_sum_le (V := fun j => iterateIncrement T j)
    (T := T i) (Finset.range (i + 1))
    (fun j hj => iterateIncrement_contDiffOn I hΦ hθ hT (by have := Finset.mem_range.mp hj; omega))
    (fun t x => iterate_eq_sum_increments T i t x)
    (fun y => streamVel (Φ (m - 1)) y.1 y.2) p α
  refine hsum.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hB : 0 ≤ N / Real.sqrt κp * (((3 * Nstar β).factorial : ℝ) * L ^ α.length) := by positivity
  have hcard : (∑ j ∈ Finset.range (i + 1), Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord α (iterateIncrement T j t))))) ≤
      ((i : ℝ) + 1) * (N / Real.sqrt κp * (((3 * Nstar β).factorial : ℝ) * L ^ α.length)) := by
    refine (Finset.sum_le_sum hpiece).trans ?_
    simp
  refine hcard.trans ?_
  have hi' : ((i : ℝ) + 1) ≤ (Nstar β : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hi
  have hLn : L ^ α.length ≤ (max Cs 1 * E ^ (-(1 + gamma β / 2))) ^ α.length :=
    pow_le_pow_left₀ hL.le hLle _
  have hX : 0 ≤ N / Real.sqrt κp := by positivity
  calc ((i : ℝ) + 1) * (N / Real.sqrt κp * (((3 * Nstar β).factorial : ℝ) * L ^ α.length))
      ≤ ((Nstar β : ℝ) + 1) * (N / Real.sqrt κp * (((3 * Nstar β).factorial : ℝ) *
          (max Cs 1 * E ^ (-(1 + gamma β / 2))) ^ α.length)) := by
        apply mul_le_mul hi' _ hB (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLn hfact) hX
    _ = ((Nstar β : ℝ) + 1) * ((3 * Nstar β).factorial : ℝ) * N / Real.sqrt κp *
          (max Cs 1 * E ^ (-(1 + gamma β / 2))) ^ α.length := by ring

end AVenhance.Infra.Section5.RelativeError
