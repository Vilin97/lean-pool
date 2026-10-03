/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.NormalOrderFields

/-! One quantitative adjacent material/spatial commutator step. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- An adjacent swap is controlled by its ordered term and strictly smaller
weighted budgets. This calculus helper retains both finite induction indices. -/
theorem amnr_normal_order_adjacent_abs_le_of_lower_bounds
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {N cut q : ℕ} {S H F Cb : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hF : 0 ≤ F) (hCb : 0 ≤ Cb) (z : AmnrSpace)
    (a : Option (Fin 2 × Fin 2)) (u v : List (Option (Fin 2))) (i : Fin 2)
    (hbudget : amnrBudget (u ++ none :: some i :: v) + amnrNormalFieldCost a ≤ q + 1)
    (hq : q + 1 ≤ N)
    (hcut : amnrMaterialCount (u ++ none :: some i :: v) + amnrNormalFieldReserve a ≤ cut)
    (hlower : ∀ a w, amnrBudget w + amnrNormalFieldCost a ≤ q →
      amnrMaterialCount w + amnrNormalFieldReserve a ≤ cut →
      |amnrWord b w (amnrNormalField b f a) z| ≤
        amnrNormalOrderConstant N Cb q * amnrNormalFieldAmplitude F Cb H a * amnrWeight S H w)
    (hswap : |amnrWord b (u ++ some i :: none :: v) (amnrNormalField b f a) z| ≤
      amnrNormalFieldAmplitude F Cb H a * amnrWeight S H (u ++ none :: some i :: v) *
        amnrNormalOrderSwapFactor N Cb q ^ amnrWordInversions (u ++ some i :: none :: v)) :
    |amnrWord b (u ++ none :: some i :: v) (amnrNormalField b f a) z| ≤
      amnrNormalFieldAmplitude F Cb H a * amnrWeight S H (u ++ none :: some i :: v) *
        amnrNormalOrderSwapFactor N Cb q ^ amnrWordInversions (u ++ none :: some i :: v) := by
  let K := amnrNormalOrderConstant N Cb q
  let A := amnrNormalFieldAmplitude F Cb H a
  let g := amnrWord b v (amnrNormalField b f a)
  have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans (amnrNormalOrderConstant_one_le hCb q)
  have hA : 0 ≤ A := amnrNormalFieldAmplitude_nonneg hF hCb hH a
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiffOn_univ.mp
    (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn
      (amnrNormalField_contDiff hb hf a).contDiffOn v)
  have hfirst : |amnrWord b (u ++ [some i, none]) g z| ≤
      A * amnrWeight S H (u ++ none :: some i :: v) *
        amnrNormalOrderSwapFactor N Cb q ^ amnrWordInversions (u ++ some i :: none :: v) := by
    change |amnrWord b (u ++ [some i, none]) (amnrWord b v (amnrNormalField b f a)) z| ≤ _
    rw [← amnrWord_append]
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hswap
  have hBsub : ∀ p s, s.Sublist u →
      |amnrWord b s (amnrVelocityGradient b p i) z| ≤ (K * (Cb * H)) * amnrWeight S H s := by
    intro p s hs
    have hbud := (amnrAdjacent_subword_budgets u v i p hs (amnrNormalFieldCost a)).1
    have hmat := (amnrAdjacent_subword_material_counts u v i p hs).1
    have hh := hlower (some (p, i)) s (by simp only [amnrNormalFieldCost]; omega)
      (by simp only [amnrNormalFieldReserve]; omega)
    exact hh
  have hGsub : ∀ p s, s.Sublist u →
      |amnrWord b s (amnrOp b (some p) g) z| ≤
        (K * A * S * amnrWeight S H v) * amnrWeight S H s := by
    intro p s hs
    have hbud := (amnrAdjacent_subword_budgets u v i p hs (amnrNormalFieldCost a)).2
    have hmat := (amnrAdjacent_subword_material_counts u v i p hs).2
    have hh := hlower a (s ++ some p :: v) (by omega) (by omega)
    change |amnrWord b s (amnrWord b [some p] (amnrWord b v (amnrNormalField b f a))) z| ≤ _
    rw [← amnrWord_append, ← amnrWord_append]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine hh.trans_eq ?_
    rw [amnrWeight_append]
    simp only [amnrWeight, List.map_cons, List.prod_cons]
    ring
  have hh := amnr_word_material_spatial_abs_le_of_bounds hb hg u i z hS hH
    (show 0 ≤ K * (Cb * H) by positivity)
    (show 0 ≤ K * A * S * amnrWeight S H v by have := amnrWeight_nonneg hS hH v; positivity)
    hfirst hBsub hGsub
  have hu : u.length ≤ N := by
    have hb := amnrBudget_length_le u
    have hbu : amnrBudget u ≤ amnrBudget (u ++ none :: some i :: v) := by
      rw [amnrBudget_append]
      omega
    omega
  have hpow : (2 : ℝ) ^ (u.length + 1) ≤ (2 : ℝ) ^ (N + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hd := mul_le_mul_of_nonneg_right hpow
    (show 0 ≤ K ^ 2 * Cb * A * amnrWeight S H (u ++ none :: some i :: v) by
      have := amnrWeight_nonneg hS hH (u ++ none :: some i :: v)
      positivity)
  have hc : (2 : ℝ) ^ (u.length + 1) * (K * (Cb * H)) *
      (K * A * S * amnrWeight S H v) * amnrWeight S H u ≤
        A * amnrWeight S H (u ++ none :: some i :: v) *
          ((2 : ℝ) ^ (N + 1) * Cb * K ^ 2) := by
    convert hd using 1 <;> rw [amnrAdjacent_weight_factor] <;> ring
  change |amnrWord b u (amnrWord b [none, some i]
    (amnrWord b v (amnrNormalField b f a))) z| ≤ _ at hh
  rw [← amnrWord_append, ← amnrWord_append] at hh
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hh
  refine (hh.trans (add_le_add le_rfl hc)).trans ?_
  have hAbs := mul_le_mul_of_nonneg_left
    (amnrNormalOrderSwapFactor_absorb (N := N) (q := q) hCb
      (amnrWordInversions (u ++ some i :: none :: v)))
    (show 0 ≤ A * amnrWeight S H (u ++ none :: some i :: v) by
      exact mul_nonneg hA (amnrWeight_nonneg hS hH _))
  rw [amnrWordInversions_swap]
  convert hAbs using 1
  ring

end AVenhance.Infra.Section4
