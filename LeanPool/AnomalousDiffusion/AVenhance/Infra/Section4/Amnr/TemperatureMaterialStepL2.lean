/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureMaterialWordEquation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.NormalOrderUniformCutoff

/-! One material level from lower canonical gradient and flux jets. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

theorem amnr_gradient_material_step_L2 {U : Set AmnrSpace} (hU : IsOpen U)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict U)
    {b : AmnrSpace → Vec 2} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    {g F : Fin 2 → AmnrSpace → ℝ} (hg : ∀ p, ContDiffOn ℝ (⊤ : ℕ∞) (g p) U)
    {N r : ℕ} (hF : ∀ q, ContDiffOn ℝ N (F q) U)
    {κ S H G GF Cb : ℝ} (hκ : 0 ≤ κ) (hS : 0 < S) (hH : 0 < H)
    (hG : 0 ≤ G) (hGF : 0 ≤ GF) (hCb : 0 ≤ Cb)
    (hgb : ∀ p α n, α.length + 2 * n ≤ N → n ≤ r →
      eLpNorm (amnrWord b (amnrMixedWord α n) (g p)) 2 μ ≤
        ENNReal.ofReal (G * amnrWeight S H (amnrMixedWord α n)))
    (hFb : ∀ q α n, α.length + 2 * n ≤ N → n ≤ r →
      eLpNorm (amnrWord b (amnrMixedWord α n) (F q)) 2 μ ≤
        ENNReal.ofReal (GF * amnrWeight S H (amnrMixedWord α n)))
    (hBb : ∀ q p α n, α.length + 2 * n + 2 ≤ N → ∀ z ∈ U,
      |amnrWord b (amnrMixedWord α n) (amnrVelocityGradient b q p) z| ≤
        (Cb * H) * amnrWeight S H (amnrMixedWord α n))
    (p : Fin 2)
    (hEq : EqOn (amnrOp b none (g p))
      (fun z => κ * (∑ q : Fin 2, amnrWord b [some q, some q] (g p) z) +
        (∑ q : Fin 2, amnrWord b [some p, some q] (F q) z) -
        ∑ q : Fin 2, amnrVelocityGradient b q p z * g q z) U)
    (α : List (Fin 2)) (hbudget : α.length + 2 * (r + 1) ≤ N) :
    eLpNorm (amnrWord b (amnrMixedWord α (r + 1)) (g p)) 2 μ ≤
      ENNReal.ofReal (((2 * κ * amnrNormalOrderConstant N Cb N *
          (amnrCanonicalSamples N N).card * G +
        2 * amnrNormalOrderConstant N Cb N * (amnrCanonicalSamples N N).card * GF) * S ^ 2 +
        (2 : ℝ) ^ (N + 1) * Cb * H * G) * amnrWeight S H (amnrMixedWord α r)) := by
  let w := amnrMixedWord α r
  let K := amnrNormalOrderConstant N Cb N * (amnrCanonicalSamples N N).card
  have hK : 0 ≤ K := mul_nonneg
    (le_trans (by norm_num) (amnrNormalOrderConstant_one_le hCb N)) (Nat.cast_nonneg _)
  have hw : amnrBudget w + 2 ≤ N := by dsimp [w]; rw [amnrMixedWord_budget]; omega
  have hwl : w.length + 2 ≤ N := by have hh := amnrBudget_length_le w; omega
  have hrN : r ≤ N := by omega
  have hword := amnr_gradient_material_word_equation hU hb.contDiffOn hg hF p hEq w hwl
  have hshift : amnrMixedWord α (r + 1) = w ++ [none] := by
    dsimp [w, amnrMixedWord]
    rw [List.replicate_succ', List.append_assoc]
  have heq : amnrWord b (amnrMixedWord α (r + 1)) (g p) =ᵐ[μ]
      (fun z => κ * (∑ q : Fin 2, amnrWord b (w ++ [some q, some q]) (g p) z) +
        (∑ q : Fin 2, amnrWord b (w ++ [some p, some q]) (F q) z) -
        amnrWord b w (fun y => ∑ q : Fin 2, amnrVelocityGradient b q p y * g q y) z) := by
    rw [hshift]
    apply ((ae_restrict_mem hU.measurableSet).filter_mono hμ.ae_le).mono
    exact fun z hz => hword hz
  have hWeight (a q : Fin 2) : amnrWeight S H (w ++ [some a, some q]) = amnrWeight S H w * S ^ 2
      := by
    simp only [amnrWeight, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  have hD (q : Fin 2) : eLpNorm (amnrWord b (w ++ [some q, some q]) (g p)) 2 μ ≤
      ENNReal.ofReal (K * G * amnrWeight S H w * S ^ 2) := by
    have hh := amnr_word_L2_le_uniform_cut hU hμ hrN hb ((hg p).of_le (by simp)) hS hH hG hCb
      (hgb p) (fun q p α n _ hn => hBb q p α n hn) (w ++ [some q, some q])
      (amnr_temperature_material_step_budget α hbudget q q).1
      (amnr_temperature_material_step_budget α hbudget q q).2.1
    rw [hWeight] at hh
    simpa only [K, mul_assoc] using hh
  have hFlux (q : Fin 2) : eLpNorm (amnrWord b (w ++ [some p, some q]) (F q)) 2 μ ≤
      ENNReal.ofReal (K * GF * amnrWeight S H w * S ^ 2) := by
    have hh := amnr_word_L2_le_uniform_cut hU hμ hrN hb (hF q) hS hH hGF hCb
      (hFb q) (fun q p α n _ hn => hBb q p α n hn) (w ++ [some p, some q])
      (amnr_temperature_material_step_budget α hbudget p q).1
      (amnr_temperature_material_step_budget α hbudget p q).2.1
    rw [hWeight] at hh
    simpa only [K, mul_assoc] using hh
  have hSum {f : Fin 2 → AmnrSpace → ℝ} {V : ℝ} (hV : 0 ≤ V)
      (hf : ∀ q, eLpNorm (f q) 2 μ ≤ ENNReal.ofReal V) :
      eLpNorm (fun z => ∑ q : Fin 2, f q z) 2 μ ≤ ENNReal.ofReal (2 * V) := by
    have hh := (eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)).trans
      (Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin 2))) => hf q))
    simp only [Fin.sum_univ_two, ← ENNReal.ofReal_add hV hV] at hh
    simp only [Fin.sum_univ_two]
    change eLpNorm (f 0 + f 1) 2 μ ≤ ENNReal.ofReal (2 * V)
    simpa only [two_mul] using hh
  have hW := amnrWeight_nonneg hS.le hH.le w
  have hDs := hSum (V := K * G * amnrWeight S H w * S ^ 2) (by positivity) hD
  have hFs := hSum (V := K * GF * amnrWeight S H w * S ^ 2) (by positivity) hFlux
  have hBs := amnrWord_sum_mul_L2_le (M := N) (N := N) hU hμ le_rfl (hb.of_le (by simp)).contDiffOn
    (fun q => (amnrVelocityGradient_contDiffOn_infty hU hb.contDiffOn q p).of_le (by simp))
    (fun q => (hg q).of_le (by simp)) hS.le hH.le (mul_nonneg hCb hH.le) hG w (by omega)
    (fun q v hv => by
      obtain ⟨η, s, rfl, hs, hbud⟩ := amnrMixedWord_subword_normalForm hv
      exact hBb q p η s (by rw [amnrMixedWord_budget] at hw; omega))
    (fun q v hv => by
      obtain ⟨η, s, rfl, hs, hbud⟩ := amnrMixedWord_subword_normalForm hv
      exact hgb q η s (by rw [amnrMixedWord_budget] at hw; omega) hs)
  rw [eLpNorm_congr_ae heq]
  have hκDs : eLpNorm (fun z => κ * ∑ q : Fin 2, amnrWord b (w ++ [some q, some q]) (g p) z) 2 μ ≤
      ENNReal.ofReal (κ * (2 * (K * G * amnrWeight S H w * S ^ 2))) := by
    change eLpNorm (κ • (fun z => ∑ q : Fin 2, amnrWord b (w ++ [some q, some q]) (g p) z)) 2 μ ≤ _
    rw [eLpNorm_const_smul, Real.enorm_of_nonneg hκ]
    exact (mul_le_mul_right hDs _).trans_eq (ENNReal.ofReal_mul hκ).symm
  refine (eLpNorm_sub_le (by norm_num : (1 : ENNReal) ≤ 2)).trans
    ((add_le_add ((eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)).trans
      (add_le_add hκDs hFs)) hBs).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp [K, w]
  ring

end AVenhance.Infra.Section4
