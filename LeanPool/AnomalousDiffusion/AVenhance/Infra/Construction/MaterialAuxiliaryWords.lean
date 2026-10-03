/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialAuxiliaryProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamMixedSum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamMixedCurrentRates

/-! Source increment bounds with independent spatial and material cutoffs.
The spatial stream-regularity and inverse-flow bounds hold at every order; only cutoff-time
orders use the literal `Nstar`. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Construction
open AVenhance.Infra.Section4

theorem MaterialAuxiliaryWords.material_aux_amnrSpaceWord_abs_le_iteratedFDeriv
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (α : List (Fin 2)) (x : Vec 2) :
    |amnrSpaceWord α f x| ≤ ‖iteratedFDeriv ℝ α.length f x‖ := by
  rw [amnrSpaceWord_eq_iteratedFDeriv hf α]
  have hp : ∏ j : Fin α.length, ‖amnrSpatialDirections α j‖ = 1 := by
    rw [amnrSpatialDirections_eq]
    have hb (p : Fin 2) : ‖basisVec p‖ = 1 := by
      fin_cases p <;> simp [basisVec, Pi.norm_single]
    simp only [hb, Finset.prod_const_one]
  have hd := (iteratedFDeriv ℝ α.length f x).le_opNorm
    (amnrSpatialDirections α)
  rw [hp, mul_one, Real.norm_eq_abs] at hd
  exact hd

/-- A transported recursion summand has arbitrary auxiliary spatial order,
while its time-cutoff derivative stays within `Nstar`. -/
theorem material_aux_nextStreamTerm_mixed_abs_le_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (k : ℤ) (α : List (Fin 2)) (ell : ℕ) {Nspace : ℕ}
    (hα : α.length ≤ Nspace) (hell : ell ≤ AVenhance.Nstar β)
    (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (α.map some ++ List.replicate ell none)
      (fun y => I.nextStreamTerm m (Φ (m - 1)) (hΦ.adm_pred m) y.1 y.2 k) z| ≤
      ((2 : ℝ) ^ ell * I.Chat * I.Czeta) *
        (amnrTransportSpatialConstant Nspace * AVenhance.a β I.Λ m *
          AVenhance.epsilon β I.Λ m ^ 2 *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length) *
        (AVenhance.tau β I.Λ m)⁻¹ ^ ell := by
  by_cases ht : |z.1 - (AVenhance.lIdx β I.Λ m k : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m
  · rw [amnr_nextStreamTerm_mixed_word I hΦ m k α ell z, abs_mul]
    let l := AVenhance.lIdx β I.Λ m k
    have hb := material_aux_transportProfile_iteratedFDeriv_norm_le_of_A3
      I hΦ hreg hm k l z.1 z.2 ht
      (N := Nspace) α.length hα
    have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (z.1, y)) := by
      fun_prop
    have hXslice : ContDiff ℝ (⊤ : ℕ∞) (I.xFlowInv hΦ m l z.1) :=
      (amnr_xFlowInv_joint_contDiff_infty I hΦ m l).comp hslice
    have hψslice : ContDiff ℝ (⊤ : ℕ∞)
        (fun y => AVenhance.psi β I.Λ m k (I.xFlowInv hΦ m l z.1 y)) :=
      (amnr_psi_contDiff I m k).comp hXslice
    have hsp := MaterialAuxiliaryWords.material_aux_amnrSpaceWord_abs_le_iteratedFDeriv hψslice α
        z.2
    have hbword := hsp.trans hb
    have hc := amnr_stream_timeAmplitude_derivative_abs_le I hm k ell hell z.1
    have hnonneg := (abs_nonneg _).trans hc
    have hh := mul_le_mul hc hbword (abs_nonneg _) hnonneg
    convert hh using 1; ring
  · rw [amnr_nextStreamTerm_word_zero_off_large I (hΦ.adm_pred m) hm k _ _ z
      (lt_of_not_ge ht), abs_zero]
    have hK := amnrTransportSpatialConstant_pos Nspace
    have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m :=
        m)
    have hτ := I.tau_pos' m
    have hChat : 0 < I.Chat := lt_of_lt_of_le zero_lt_one I.one_le_Chat
    have hCzeta : 0 < I.Czeta := lt_of_lt_of_le zero_lt_one I.one_le_Czeta
    positivity

/-- The three locally active recursion summands give the mixed stream
increment bound at independent spatial and material orders. -/
theorem material_aux_streamIncrement_mixed_abs_le_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (α : List (Fin 2)) (ell : ℕ) {Nspace : ℕ}
    (hα : α.length ≤ Nspace) (hell : ell ≤ AVenhance.Nstar β)
    (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (α.map some ++ List.replicate ell none)
      (fun y => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2) z| ≤
      3 * (((2 : ℝ) ^ ell * I.Chat * I.Czeta) *
        (amnrTransportSpatialConstant Nspace * AVenhance.a β I.Λ m *
          AVenhance.epsilon β I.Λ m ^ 2 *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length) *
        (AVenhance.tau β I.Λ m)⁻¹ ^ ell) := by
  obtain ⟨s, hcard, heq⟩ := amnr_streamIncrement_word_sum I hΦ hm
    (α.map some ++ List.replicate ell none) z
  rw [heq]
  let B := ((2 : ℝ) ^ ell * I.Chat * I.Czeta) *
    (amnrTransportSpatialConstant Nspace * AVenhance.a β I.Λ m *
      AVenhance.epsilon β I.Λ m ^ 2 * (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length) *
    (AVenhance.tau β I.Λ m)⁻¹ ^ ell
  have hB : 0 ≤ B := by
    have hK := amnrTransportSpatialConstant_pos Nspace
    have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m :=
        m)
    have hτ := I.tau_pos' m
    have hChat : 0 < I.Chat := lt_of_lt_of_le zero_lt_one I.one_le_Chat
    have hCzeta : 0 < I.Czeta := lt_of_lt_of_le zero_lt_one I.one_le_Czeta
    dsimp [B]
    positivity
  calc
    _ ≤ ∑ k ∈ s, |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (α.map some ++ List.replicate ell none)
        (fun y => I.nextStreamTerm m (Φ (m - 1)) (hΦ.adm_pred m) y.1 y.2 k) z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ s, B := Finset.sum_le_sum (fun k _ =>
      material_aux_nextStreamTerm_mixed_abs_le_of_A3 I hΦ hreg hm k α ell hα hell z)
    _ = (s.card : ℝ) * B := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB

/-- The mixed stream increment has its current material amplitude, with an
auxiliary spatial order and literal cutoff-time order. -/
def materialAuxStreamMixedCurrentConstant {β : ℝ}
    (I : AVenhance.Ingredients β) (Nspace : ℕ) : ℝ :=
  3 * I.Chat * I.Czeta * amnrTransportSpatialConstant Nspace *
    (2 * max 1 (amnrFineMaterialConstant β)) ^ AVenhance.Nstar β

theorem materialAuxStreamMixedCurrentConstant_nonneg {β : ℝ}
    (I : AVenhance.Ingredients β) (Nspace : ℕ) :
    0 ≤ materialAuxStreamMixedCurrentConstant I Nspace := by
  unfold materialAuxStreamMixedCurrentConstant
  have hChat : 0 ≤ I.Chat := le_trans (by norm_num) I.one_le_Chat
  have hCzeta : 0 ≤ I.Czeta := le_trans (by norm_num) I.one_le_Czeta
  have hT := amnrTransportSpatialConstant_pos Nspace
  have hK : 0 ≤ max 1 (amnrFineMaterialConstant β) :=
    le_trans (by norm_num) (le_max_left _ _)
  positivity

theorem material_aux_streamIncrement_mixed_current_abs_le_of_A3
    {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (α : List (Fin 2)) (ell : ℕ) {Nspace : ℕ}
    (hα : α.length ≤ Nspace) (hell : ell ≤ AVenhance.Nstar β)
    (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (amnrMixedWord α ell)
      (fun y => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2) z| ≤
      (materialAuxStreamMixedCurrentConstant I Nspace * AVenhance.a β I.Λ m *
        AVenhance.epsilon β I.Λ m ^ 2) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ ell := by
  have hh := material_aux_streamIncrement_mixed_abs_le_of_A3 I hΦ hreg hm α ell hα hell z
  have hp := amnr_fine_time_power_le_current I hm
    (N := AVenhance.Nstar β) (by omega : ell ≤ AVenhance.Nstar β)
  have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hbase : 0 ≤ (3 * I.Chat * I.Czeta * amnrTransportSpatialConstant Nspace) *
      AVenhance.a β I.Λ m * AVenhance.epsilon β I.Λ m ^ 2 *
      (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length := by
    have hChat : 0 ≤ I.Chat := le_trans (by norm_num) I.one_le_Chat
    have hCzeta : 0 ≤ I.Czeta := le_trans (by norm_num) I.one_le_Czeta
    have hT := amnrTransportSpatialConstant_pos Nspace
    have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m :=
        m)
    have hInv : 0 ≤ (AVenhance.epsilon β I.Λ m)⁻¹ := inv_nonneg.mpr hE.le
    positivity
  have hd := mul_le_mul_of_nonneg_left hp hbase
  refine hh.trans ?_
  calc
    _ = (3 * I.Chat * I.Czeta * amnrTransportSpatialConstant Nspace) *
          ((2 : ℝ) ^ ell * (AVenhance.tau β I.Λ m)⁻¹ ^ ell) *
          AVenhance.a β I.Λ m * AVenhance.epsilon β I.Λ m ^ 2 *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length := by ring
    _ ≤ (3 * I.Chat * I.Czeta * amnrTransportSpatialConstant Nspace) *
          ((2 * max 1 (amnrFineMaterialConstant β)) ^ AVenhance.Nstar β *
            AVenhance.a β I.Λ m ^ ell) *
          AVenhance.a β I.Λ m * AVenhance.epsilon β I.Λ m ^ 2 *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length := by
      convert hd using 1 <;> ring
    _ = _ := by
      unfold materialAuxStreamMixedCurrentConstant
      ring

end AVenhance.Infra.Construction

end
