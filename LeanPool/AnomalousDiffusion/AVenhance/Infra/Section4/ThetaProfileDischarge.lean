/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaAnalyticTrace
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaZeroBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesThetaGradientBase
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesComponentEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesBudgetConstantChoice
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermissibleSet
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeq

/-! Discharge the stream-regularity/diffusivity-recursion data and convert theta derivative
    estimates
to the order-zero coordinate profile. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Topology

namespace AVenhance.Infra.Section4

theorem ThetaProfileDischarge.iterateSpatialWord_eq_classicalWordDerivative
    (w : List (Fin 2)) (f : Vec 2 → ℝ) :
    iterateSpatialWord w f = classicalWordDerivative w f := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [iterateSpatialWord, classicalWordDerivative,
    Classical.classicalWordDerivative, ih]

/-- Stream-regularity and diffusivity-recursion data extracted from the conclusions.
The second stream-regularity display and both diffusivity bounds are retained verbatim. -/
theorem theta_A3_A5_data_of_frozen
    {β : ℝ} {M : ℕ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : AVenhance.IsStreamSeq I Φ)
    (κ : ℝ) (hM : 1 ≤ M)
    (hPerm : κ ∈ AVenhance.permittedInterval β I.Λ M) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      (∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
        AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
          (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
          AVenhance.epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) ∧
      (∀ j : ℕ, 1 ≤ j → j < M →
        c * (AVenhance.a β I.Λ j * AVenhance.epsilon β I.Λ j ^
          (2 + AVenhance.gamma β)) ≤ I.kappaAt κ j (M - j) ∧
        I.kappaAt κ j (M - j) ≤
          C * (AVenhance.a β I.Λ j * AVenhance.epsilon β I.Λ j ^
            (2 + AVenhance.gamma β))) := by
  let Ccut := max I.Czeta (max I.Cxi I.Chat)
  have hz : I.Czeta ≤ Ccut := le_max_left _ _
  have hxi : I.Cxi ≤ Ccut := le_trans (le_max_left _ _) (le_max_right _ _)
  have hh : I.Chat ≤ Ccut := le_trans (le_max_right _ _) (le_max_right _ _)
  have hpermissible : κ ∈ AVenhance.permissibleSet β I.Λ := by
    refine Set.mem_iUnion.mpr ⟨M, ?_⟩
    exact Set.mem_iUnion.mpr ⟨hM, hPerm⟩
  obtain ⟨_, _, hstream⟩ := AVenhance.stream_regularity β
  obtain ⟨c, C, hc, hcC, hrec⟩ := AVenhance.l_recurse β Ccut
  refine ⟨c, C, hc, hcC, ?_, ?_⟩
  · intro j hj t n hn
    exact (hstream I Φ hΦ j hj t).2.1 n hn
  · intro j hj hjM
    exact (hrec I hz hxi hh κ hpermissible M hM hPerm).1 j hj hjM

/-- The original analytic energy bound with stream-regularity and diffusivity-recursion discharged
    by the
conclusions. The diffusivity-recursion constants remain explicit outputs for downstream
radius bookkeeping. -/
theorem theta_analytic_energy_bound_of_frozen_A3_A5
    {β : ℝ} {M m : ℕ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : AVenhance.IsStreamSeq I Φ)
    (hm : 2 ≤ m) (hmM : m ≤ M) {κ R : ℝ} (hR : 0 < R)
    (hPerm : κ ∈ AVenhance.permittedInterval β I.Λ M)
    {θ₀ : Vec 2 → ℝ} (hθ₀ : AVenhance.IsThetaAnalytic R θ₀)
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel (fun t => Φ (m - 1) t))
      (AVenhance.Ingredients.kappaSeq I κ M (m - 1))
      (fun _ _ => 0) θ₀ θ) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ n : ℕ,
        thetaEnergyLevel θ (AVenhance.Ingredients.kappaSeq I κ M (m - 1)) n ≤
          2 * Real.sqrt (AVenhance.l2NormSq θ₀) * (n.factorial : ℝ) *
            thetaAnalyticRadius c (AVenhance.epsilon β I.Λ (m - 1))
              (AVenhance.gamma β) R ^ n := by
  have hM : 1 ≤ M := by omega
  obtain ⟨c, C, hc, hcC, hA3, hA5⟩ :=
    theta_A3_A5_data_of_frozen I Φ hΦ κ hM hPerm
  exact ⟨c, C, hc, hcC, fun n =>
    theta_analytic_energy_bound_of_A3_A5 I Φ hΦ hm hmM hR hθ₀ hA3
      ⟨hc, hcC, hA5⟩ hsol n⟩

theorem ThetaProfileDischarge.theta_initial_trace_of_analytic
    {B R : ℝ} {θ₀ : Vec 2 → ℝ}
    (hθ₀ : AVenhance.IsThetaAnalytic R θ₀)
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F : ℝ → Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol b κ F θ₀ θ)
    (hB : Real.sqrt (AVenhance.l2NormSq θ₀) ≤ B)
    (hR : 0 < R) :
    ∀ w : List (Fin 2),
      Real.sqrt (∫ x in AVenhance.unitCube,
        (classicalWordDerivative w θ₀ x) ^ 2) ≤
      B * ((w.length.factorial : ℝ) / R ^ w.length) := by
  intro w
  have hbase := theta_initial_word_l2_le_of_analytic hθ₀ hsol w
  have hfactor : 0 ≤ (w.length.factorial : ℝ) / R ^ w.length := by
    positivity
  exact hbase.trans (mul_le_mul_of_nonneg_right hB hfactor)

theorem ThetaProfileDischarge.theta_profile_source_radius_le
    {β c R C₀ : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
    (hscale : AVenhance.epsilon β I.Λ (m - 1) ^
      (1 + AVenhance.gamma β / 2) ≤ R)
    (hC₀ : 8 * max (thetaAnalyticRadiusBase c) 2 ≤ C₀) :
    8 * thetaAnalyticRadius c (AVenhance.epsilon β I.Λ (m - 1))
        (AVenhance.gamma β) R ≤
      C₀ * AVenhance.epsilon β I.Λ (m - 1) ^
        (-1 - AVenhance.gamma β / 2) := by
  let e := AVenhance.epsilon β I.Λ (m - 1)
  let γ := AVenhance.gamma β
  let p := 1 + γ / 2
  have he : 0 < e := AVenhance.Infra.Cutoff.epsilon_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hepow : 0 < e ^ p := Real.rpow_pos_of_pos he p
  have hRpow : e ^ p ≤ R := by simpa [e, p, γ] using hscale
  have hinv := div_le_div_of_nonneg_left
    (by norm_num : (0 : ℝ) ≤ 1) hepow hRpow
  have hinvPow : e ^ (-p) = (e ^ p)⁻¹ := Real.rpow_neg he.le p
  have hsecond : 2 / R ≤ 2 * e ^ (-p) := by
    have hmul := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
    simpa [div_eq_mul_inv, hinvPow] using hmul
  have hpowNonneg : 0 ≤ e ^ (-p) := (Real.rpow_pos_of_pos he _).le
  have hcoef' : max (thetaAnalyticRadiusBase c) 2 * 8 ≤ C₀ := by
    nlinarith only [hC₀]
  have hcoef : max (thetaAnalyticRadiusBase c) 2 ≤ C₀ / 8 :=
    (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).2 hcoef'
  have hfirst : thetaAnalyticRadiusBase c * e ^ (-p) ≤
      max (thetaAnalyticRadiusBase c) 2 * e ^ (-p) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hpowNonneg
  have hsecond' : 2 / R ≤
      max (thetaAnalyticRadiusBase c) 2 * e ^ (-p) :=
    hsecond.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpowNonneg)
  have hradius : thetaAnalyticRadius c e γ R ≤
      max (thetaAnalyticRadiusBase c) 2 * e ^ (-p) := by
    dsimp [thetaAnalyticRadius]
    apply max_le
    · have hexp : (-1 : ℝ) - AVenhance.gamma β / 2 =
          -p := by dsimp [p]; ring
      rw [hexp]
      exact hfirst
    · exact hsecond'
  calc
    8 * thetaAnalyticRadius c e γ R ≤
        8 * (max (thetaAnalyticRadiusBase c) 2 * e ^ (-p)) :=
      mul_le_mul_of_nonneg_left hradius (by norm_num)
    _ = (8 * max (thetaAnalyticRadiusBase c) 2) * e ^ (-p) := by ring
    _ ≤ C₀ * e ^ (-p) := mul_le_mul_of_nonneg_right hC₀ hpowNonneg
    _ = C₀ * e ^ (-1 - γ / 2) := by
      congr 2
      dsimp [p, γ]
      ring
    _ = C₀ * AVenhance.epsilon β I.Λ (m - 1) ^
          (-1 - AVenhance.gamma β / 2) := by rfl

/-- The source constant passed to the next estimate absorbs the analytic theta radius
when `Cθ` is chosen from the diffusivity-recursion constant. -/
theorem theta_profile_radius_absorbed_by_source_constant
    {cProfile Cθ Csource Rflow C₀ : ℝ}
    (hTheta : 4 * max (thetaAnalyticRadiusBase cProfile) 2 ≤ Cθ)
    (hSource : iterateSourceConstant Csource Rflow Cθ ≤ C₀) :
    8 * max (thetaAnalyticRadiusBase cProfile) 2 ≤ C₀ := by
  have htheta2 :
      8 * max (thetaAnalyticRadiusBase cProfile) 2 ≤ 2 * Cθ := by
    nlinarith only [hTheta]
  have hCθ : 2 * Cθ ≤ iterateSourceConstant Csource Rflow Cθ :=
    (iterate_source_constant_bounds Csource Rflow Cθ).2.2.2.1
  exact htheta2.trans (hCθ.trans hSource)

/-- Convert the generic analytic energy estimate into the order-zero profile
required by the actual T upgrade. The only input from the initial datum is the
explicit all-orders wordwise L² trace bound. -/
theorem theta_iterate_profile_of_initial_trace_A3_A5
    {β : ℝ} {M m : ℕ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : AVenhance.IsStreamSeq I Φ)
    (hm : 2 ≤ m) (hmM : m ≤ M) {κ : ℝ}
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    {c C B R C₀ : ℝ} (hc : 0 < c) (hC : c < C)
    (hB : 0 < B) (hR : 0 < R)
    (hRadius : 8 * max (thetaAnalyticRadiusBase c) 2 ≤ C₀)
    (hscale : AVenhance.epsilon β I.Λ (m - 1) ^
      (1 + AVenhance.gamma β / 2) ≤ R)
    (hzero : AVenhance.Ingredients.kappaSeq I κ M (m - 1) *
      AVenhance.spaceTimeGradNormSq (fun t => AVenhance.spaceGrad (θ t)) ≤ B ^ 2)
    (hTrace : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in AVenhance.unitCube,
        (classicalWordDerivative w θ₀ x) ^ 2) ≤
      B * ((w.length.factorial : ℝ) / R ^ w.length))
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (hA5 : ∀ j : ℕ, 1 ≤ j → j < M →
      c * (AVenhance.a β I.Λ j * AVenhance.epsilon β I.Λ j ^
        (2 + AVenhance.gamma β)) ≤ I.kappaAt κ j (M - j) ∧
      I.kappaAt κ j (M - j) ≤
        C * (AVenhance.a β I.Λ j * AVenhance.epsilon β I.Λ j ^
          (2 + AVenhance.gamma β)))
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel (fun t => Φ (m - 1) t))
      (AVenhance.Ingredients.kappaSeq I κ M (m - 1))
      (fun _ _ => 0) θ₀ θ) :
    iterateCoordinateEnergyProfile θ
      (AVenhance.Ingredients.kappaSeq I κ M (m - 1)) B
      (C₀ * AVenhance.epsilon β I.Λ (m - 1) ^
        (-1 - AVenhance.gamma β / 2)) 0 := by
  let κm := AVenhance.Ingredients.kappaSeq I κ M (m - 1)
  let r := thetaAnalyticRadius c (AVenhance.epsilon β I.Λ (m - 1))
    (AVenhance.gamma β) R
  let l := 2 * r
  let L := C₀ * AVenhance.epsilon β I.Λ (m - 1) ^
    (-1 - AVenhance.gamma β / 2)
  have henergy := theta_analytic_positive_energy_bound_of_initial_trace_A3_A5
    I Φ hΦ hm hmM hc hC hB hR hzero hTrace hA3 hA5 hsol
  have henergy' : ∀ n : ℕ, 1 ≤ n →
      thetaEnergyLevel θ κm n ≤ 2 * B * (n.factorial : ℝ) * r ^ n := by
    intro n hn
    simpa [κm, r] using henergy n hn
  have hκpos : 0 < κm := by
    have hmpos : 1 ≤ m - 1 := by omega
    have hindex : m - 1 < M := by omega
    have hlow := hA5 (m - 1) hmpos hindex
    have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
      AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have ha : 0 < AVenhance.a β I.Λ (m - 1) := by
      rw [AVenhance.a]
      exact Real.rpow_pos_of_pos he _
    have hfactor : 0 < AVenhance.a β I.Λ (m - 1) *
        AVenhance.epsilon β I.Λ (m - 1) ^ (2 + AVenhance.gamma β) := by
      exact mul_pos ha (Real.rpow_pos_of_pos he _)
    simpa [κm, AVenhance.Ingredients.kappaSeq] using
      (mul_pos hc hfactor).trans_le hlow.1
  have hradius := ThetaProfileDischarge.theta_profile_source_radius_le I hscale hRadius
  have hL : 4 * l ≤ L := by
    calc
      4 * l = 8 * r := by dsimp [l]; ring
      _ ≤ L := by simpa [r, L] using hradius
  have hrpos : 0 < r := by
    dsimp [r, thetaAnalyticRadius]
    positivity
  have hsource : ∀ v w : List (Fin 2), 1 ≤ v.length →
      w.length = v.length + 1 → ∀ s, 0 ≤ s → s ≤ 1 →
      Real.sqrt (AVenhance.l2NormSq (iterateSpatialWord v (θ s))) +
        Real.sqrt κm * Real.sqrt
          (∫ z in AVenhance.timeCube,
            (iterateSpatialWord w (θ z.1) z.2) ^ 2) ≤
        2 * B * (v.length.factorial : ℝ) * l ^ v.length := by
    intro v w hv hw s hs hs1
    cases w with
    | nil => simp at hw
    | cons j tail =>
      have hlen : tail.length = v.length := by simp at hw; omega
      let iv : Fin v.length → Fin 2 := fun k => v.get k
      let it : Fin tail.length → Fin 2 := fun k => tail.get k
      have hwordv : thetaCoordinateWord iv = v := List.ofFn_get v
      have hwordt : thetaCoordinateWord it = tail := List.ofFn_get tail
      have hlevelv := thetaEnergyLevel_le_of_coordinate θ κm v.length iv
      rw [hwordv] at hlevelv
      have hboundv := henergy' v.length hv
      have hfirst : Real.sqrt
          (AVenhance.l2NormSq (iterateSpatialWord v (θ s))) ≤
          2 * B * (v.length.factorial : ℝ) * r ^ v.length := by
        have hspace : AVenhance.l2NormSq (iterateSpatialWord v (θ s)) =
            thetaWordSpatialEnergy θ v s := by
          simp only [AVenhance.l2NormSq, thetaWordSpatialEnergy]
          rw [ThetaProfileDischarge.iterateSpatialWord_eq_classicalWordDerivative]
        have hspatial := theta_word_spatial_energy_le_sup_of_classical
          hsol v ⟨hs, hs1⟩
        have hspatial' :
            AVenhance.l2NormSq (iterateSpatialWord v (θ s)) ≤
              thetaWordSpatialEnergySup θ v := by
          rw [hspace]
          exact hspatial
        have hroot : Real.sqrt (AVenhance.l2NormSq
            (iterateSpatialWord v (θ s))) ≤
            Real.sqrt (thetaWordSpatialEnergySup θ v) :=
          Real.sqrt_le_sqrt hspatial'
        have hlevel := hlevelv.trans hboundv
        have hgradnonneg : 0 ≤ Real.sqrt κm *
            Real.sqrt (thetaWordSpaceTimeGradientEnergy θ v) :=
          mul_nonneg (Real.sqrt_nonneg κm) (Real.sqrt_nonneg _)
        calc
          _ ≤ Real.sqrt (thetaWordSpatialEnergySup θ v) := hroot
          _ ≤ 2 * B * (v.length.factorial : ℝ) * r ^ v.length := by
            linarith only [hlevel, hgradnonneg]
      have hlevelt := thetaEnergyLevel_le_of_coordinate θ κm tail.length it
      rw [hwordt] at hlevelt
      have hboundt := henergy' tail.length (by simpa [hlen] using hv)
      have hcomponent := iterate_word_gradient_component_energy_bound
        hsol.1 tail j
      have hcomponent' :
          (∫ z in AVenhance.timeCube,
            (iterateSpatialWord (j :: tail) (θ z.1) z.2) ^ 2) ≤
          thetaWordSpaceTimeGradientEnergy θ tail := by
        calc
          _ ≤ AVenhance.spaceTimeGradNormSq
              (fun t => AVenhance.spaceGrad (iterateSpatialWord tail (θ t))) := hcomponent
          _ = thetaWordSpaceTimeGradientEnergy θ tail := by
            simp [thetaWordSpaceTimeGradientEnergy, AVenhance.spaceTimeGradNormSq,
              ThetaProfileDischarge.iterateSpatialWord_eq_classicalWordDerivative]
      have hsecond : Real.sqrt κm * Real.sqrt
          (∫ z in AVenhance.timeCube,
            (iterateSpatialWord (j :: tail) (θ z.1) z.2) ^ 2) ≤
          2 * B * (v.length.factorial : ℝ) * r ^ v.length := by
        have hroot := Real.sqrt_le_sqrt hcomponent'
        have hlevel := hlevelt.trans hboundt
        have hspatialNonneg : 0 ≤ Real.sqrt (thetaWordSpatialEnergySup θ tail) :=
          Real.sqrt_nonneg _
        have hboundGrad : Real.sqrt κm *
            Real.sqrt (thetaWordSpaceTimeGradientEnergy θ tail) ≤
            2 * B * (tail.length.factorial : ℝ) * r ^ tail.length := by
          linarith only [hlevel, hspatialNonneg]
        simpa [hlen] using
          (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg κm)).trans hboundGrad
      have hsum := add_le_add hfirst hsecond
      have hdouble := iterate_positive_order_radius_double hrpos.le le_rfl hv
      calc
        _ ≤ 4 * B * (v.length.factorial : ℝ) * r ^ v.length := by
          calc
            _ ≤ (2 * B * (v.length.factorial : ℝ) * r ^ v.length) +
                (2 * B * (v.length.factorial : ℝ) * r ^ v.length) := hsum
            _ = 4 * B * (v.length.factorial : ℝ) * r ^ v.length := by ring
        _ ≤ 2 * B * (v.length.factorial : ℝ) * l ^ v.length := by
          calc
            _ = (2 * B * (v.length.factorial : ℝ)) * (2 * r ^ v.length) := by ring
            _ ≤ (2 * B * (v.length.factorial : ℝ)) * (2 * r) ^ v.length :=
              mul_le_mul_of_nonneg_left hdouble (by positivity)
            _ = 2 * B * (v.length.factorial : ℝ) * l ^ v.length := by
              simp [l]
  have hBnonneg : 0 ≤ B := hB.le
  exact iterate_theta_gradient_base_profile hsol.1 hκpos hBnonneg
    (mul_nonneg (by norm_num) hrpos.le) hL hzero hsource

theorem ThetaProfileDischarge.theta_iterate_profile_of_zero_data
    {φ : ℝ → Vec 2 → ℝ} {κ L : ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) (hκ : 0 < κ)
    (hsol : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ
      (fun _ _ => 0) (fun _ => 0) θ) :
    iterateCoordinateEnergyProfile θ κ 0 L 0 := by
  constructor
  · intro w hw s hs hs1
    have hwpos : 1 ≤ w.length := by
      rcases hw with hwpos | hi
      · exact hwpos
      · omega
    have hsp := theta_zero_word_spatial_energy_eq_zero hφ hκ hsol w hs
    have hnorm : AVenhance.l2NormSq (iterateSpatialWord w (θ s)) = 0 := by
      simpa [AVenhance.l2NormSq, thetaWordSpatialEnergy,
        ThetaProfileDischarge.iterateSpatialWord_eq_classicalWordDerivative] using hsp
    rw [hnorm]
    simp [iterateAnalyticWeight]
  · intro w
    have hgrad := theta_zero_word_spacetime_gradient_energy_eq_zero hφ hκ hsol w
    have hgrad' : AVenhance.spaceTimeGradNormSq
        (fun t => AVenhance.spaceGrad (iterateSpatialWord w (θ t))) = 0 := by
      simpa [thetaWordSpaceTimeGradientEnergy, AVenhance.spaceTimeGradNormSq,
        ThetaProfileDischarge.iterateSpatialWord_eq_classicalWordDerivative] using hgrad
    rw [hgrad']
    simp [iterateAnalyticWeight]

end AVenhance.Infra.Section4

end
