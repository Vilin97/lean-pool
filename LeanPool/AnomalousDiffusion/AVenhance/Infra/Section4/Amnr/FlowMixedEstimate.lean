/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SourceJetAdvance

/-! Higher mixed flow bounds from actual transport and primitive jets. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Exact flow transport and lower gradient jets control every canonical
mixed flow word. This helper estimates the actual differentiated products. -/
theorem amnr_flow_mixed_abs_le_of_primitive_jets {b : AmnrSpace → Vec 2}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (G : Fin 2 → AmnrSpace → ℝ)
    (hG : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (G p))
    (heq : ∀ p z, amnrOp b none (G p) z =
      ∑ q : Fin 2, G q z * amnrVelocityGradient b p q z)
    {N : ℕ} {S H Cg Cb : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hCg : 0 ≤ Cg) (hCb : 0 ≤ Cb) (z : AmnrSpace)
    (hGb : ∀ p (η : List (Fin 2)), η.length ≤ N →
      |amnrWord b (η.map some) (G p) z| ≤ Cg * S ^ η.length)
    (hBb : ∀ i p w, IsAmnrMixedWord w → amnrBudget w + 2 ≤ N →
      |amnrWord b w (amnrVelocityGradient b i p) z| ≤ Cb * H * amnrWeight S H w)
    (α : List (Fin 2)) (n : ℕ) (hbudget : α.length + 2 * n ≤ N) (p : Fin 2) :
    |amnrWord b (amnrMixedWord α n) (G p) z| ≤
      (2 : ℝ) ^ (α.length + 1) * Cg * (1 + (2 : ℝ) ^ (N + 1) * Cb) ^ n *
        S ^ α.length * H ^ n := by
  let M := fun q => amnrFlowMaterialCoefficient b n q p
  let R := 1 + (2 : ℝ) ^ (N + 1) * Cb
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hM (q : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (M q) := amnrFlowMaterialCoefficient_contDiff hb n q p
  have hweight (η : List (Fin 2)) : amnrWeight S H (η.map some) = S ^ η.length := by
    simp [amnrWeight, List.map_map, Function.comp_def, List.prod_replicate]
  have hproduct (q : Fin 2) :
      |amnrWord b (α.map some) (G q * M q) z| ≤
        (2 : ℝ) ^ α.length * Cg * (R ^ n * H ^ n) * S ^ α.length := by
    have hwb : amnrBudget (α.map some) ≤ N := by
      have he : α.map some = amnrMixedWord α 0 := by simp [amnrMixedWord]
      rw [he, amnrMixedWord_budget]
      omega
    have hh := amnrWord_mul_abs_le_at isOpen_univ
      (hb.of_le (show (N : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffOn
      ((hG q).of_le (show (N : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffOn
      ((hM q).of_le (show (N : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffOn
      hS hH hCg (show 0 ≤ R ^ n * H ^ n by positivity) (α.map some) hwb (mem_univ z)
      (fun v hv => by
        obtain ⟨η, hη, rfl⟩ := List.sublist_map_iff.mp hv
        rw [hweight]
        exact hGb q η (hη.length_le.trans (by omega)))
      (fun v hv => by
        obtain ⟨η, hη, rfl⟩ := List.sublist_map_iff.mp hv
        have hηlen := hη.length_le
        have hh := amnrFlowMaterialCoefficient_mixed_abs_le_of_gradient_bounds hb hS hH hCb hBb n
          (amnrMixedWord η 0) (amnrMixedWord_mixed η 0)
          (by rw [amnrMixedWord_budget]; omega) q p
        simp only [amnrMixedWord, List.replicate_zero, List.append_nil] at hh
        exact hh)
    simpa only [List.length_map, hweight] using hh
  have ht := amnrWord_material_transport hb G (fun p => (hG p).of_le (by simp)) heq n p
  have he : (fun y => ∑ q : Fin 2, G q y * M q y) = G 0 * M 0 + G 1 * M 1 := by
    funext y
    rw [Fin.sum_univ_two]
    rfl
  rw [amnrMixedWord, amnrWord_append, ht]
  change |amnrWord b (α.map some) (fun y => ∑ q : Fin 2, G q y * M q y) z| ≤ _
  have hprod0 : ContDiff ℝ (⊤ : ℕ∞) (G 0 * M 0) := (hG 0).mul (hM 0)
  have hprod1 : ContDiff ℝ (⊤ : ℕ∞) (G 1 * M 1) := (hG 1).mul (hM 1)
  rw [he, amnrWord_add_global hb hprod0 hprod1]
  simp only [Pi.add_apply]
  exact (abs_add_le _ _).trans ((add_le_add (hproduct 0) (hproduct 1)).trans_eq
    (by dsimp [R]; rw [pow_succ]; ring))

end AVenhance.Infra.Section4
