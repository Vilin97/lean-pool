/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionIdentity

/-!
# Decomposition SWSBasic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

theorem decomposition_laplacian_hasCompactSupport_sws {ψ : Vec3 → ℝ}
    (hψc : HasCompactSupport ψ) : HasCompactSupport (spatialLaplacian ψ) := by
  have hdiag (i : Fin 3) : HasCompactSupport
      (spatialDeriv (spatialDeriv ψ i) i) :=
    (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)).fderiv_apply
      (𝕜 := ℝ) (basisVec i)
  have h01 : HasCompactSupport (fun y : Vec3 =>
      spatialDeriv (spatialDeriv ψ 0) 0 y + spatialDeriv (spatialDeriv ψ 1) 1 y) := by
    convert (hdiag 0).add (hdiag 1) using 1
  have hsum : HasCompactSupport (fun y : Vec3 =>
      spatialDeriv (spatialDeriv ψ 0) 0 y + spatialDeriv (spatialDeriv ψ 1) 1 y +
        spatialDeriv (spatialDeriv ψ 2) 2 y) := by
    convert h01.add (hdiag 2) using 1
  change HasCompactSupport (fun y : Vec3 =>
    ∑ i : Fin 3, spatialDeriv (spatialDeriv ψ i) i y)
  simpa only [Fin.sum_univ_three] using hsum

theorem decomposition_full_of_on_sws {Ω : Set Vec3} {g : Vec3 → ℝ}
    (hg : IntegrableOn g Ω volume) (hΩ : tsupport g ⊆ Ω) : Integrable g volume := by
    exact hg.integrable_of_forall_notMem_eq_zero (fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hxt => hx (hΩ hxt)))

theorem decomposition_ts_support_sum₂_sws {Ω : Set Vec3}
    {F : Fin 3 → Fin 3 → Vec3 → ℝ} (hF : ∀ i j, tsupport (F i j) ⊆ Ω) :
    tsupport (fun x => ∑ i, ∑ j, F i j x) ⊆ Ω := by
  have hrow : ∀ i, tsupport (fun x => ∑ j, F i j x) ⊆ Ω := by
    intro i
    rw [show (fun x => ∑ j, F i j x) =
      (fun x => F i 0 x + F i 1 x + F i 2 x) by
        funext x; simp only [Fin.sum_univ_three]]
    apply (tsupport_add _ _).trans
    exact union_subset ((tsupport_add _ _).trans (union_subset (hF i 0) (hF i 1))) (hF i 2)
  rw [show (fun x => ∑ i, ∑ j, F i j x) =
      (fun x => (∑ j, F 0 j x) + (∑ j, F 1 j x) + (∑ j, F 2 j x)) by
        funext x; simp only [Fin.sum_univ_three]]
  apply (tsupport_add _ _).trans
  exact union_subset ((tsupport_add _ _).trans (union_subset (hrow 0) (hrow 1))) (hrow 2)

theorem decomposition_ts_support_sum₃_sws {Ω : Set Vec3}
    {F : Fin 3 → Vec3 → ℝ} (hF : ∀ i, tsupport (F i) ⊆ Ω) :
    tsupport (fun x => ∑ i, F i x) ⊆ Ω := by
  simpa only [show (fun x => ∑ i, F i x) =
      (fun x => F 0 x + F 1 x + F 2 x) by
        funext x; simp only [Fin.sum_univ_three]] using
    ((tsupport_add _ _).trans (union_subset ((tsupport_add _ _).trans
      (union_subset (hF 0) (hF 1))) (hF 2)))

end CKN
