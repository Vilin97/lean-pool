/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FluxDivergence

/-! Coordinate Piola formula for a corrected push-forward matrix. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

/-- The divergence of `Q (g ∘ M)` is the pulled-back divergence of `g` when
the columns of `Q` are divergence-free and `Q` is the inverse chain matrix.
These are the two coordinate Piola identities needed from a smooth
volume-preserving change of variables. -/
theorem vecDiv_correctedPiola
    {M g : Vec 2 → Vec 2} {Q : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {x : Vec 2}
    {LQ : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    {LM : Vec 2 →L[ℝ] Vec 2} {Lg : Vec 2 →L[ℝ] Vec 2}
    (hQ : ∀ i j, HasFDerivAt (fun y => Q y i j) (LQ i j) x)
    (hM : HasFDerivAt M LM x)
    (hg : HasFDerivAt g Lg (M x))
    (hPiolaDiv : ∀ j : Fin 2,
      ∑ i : Fin 2, (LQ i j) (basisVec i) = 0)
    (hPiolaChain : ∀ j k : Fin 2,
      ∑ i : Fin 2, Q x i j * (LM (basisVec i)) k = if j = k then 1 else 0) :
    vecDiv (fun y => (Q y).mulVec (g (M y))) x = vecDiv g (M x) := by
  have hcomp : HasFDerivAt (fun y => g (M y)) (Lg.comp LM) x := by
    exact hg.comp x hM
  rw [vecDiv_matrixMulVec hQ hcomp]
  have hfirst :
      (∑ j : Fin 2, ∑ i : Fin 2,
        (LQ i j) (basisVec i) * g (M x) j) = 0 := by
    calc
      (∑ j : Fin 2, ∑ i : Fin 2,
          (LQ i j) (basisVec i) * g (M x) j) =
        ∑ j : Fin 2, (∑ i : Fin 2, (LQ i j) (basisVec i)) * g (M x) j := by
          congr 1
          funext j
          rw [← Finset.sum_mul]
      _ = 0 := by simp [hPiolaDiv]
  have hsecond :
      (∑ i : Fin 2, ∑ j : Fin 2,
        Q x i j * ((Lg.comp LM) (basisVec i)) j) =
        ∑ j : Fin 2, (Lg (basisVec j)) j := by
    have hdecomp (i : Fin 2) :
        LM (basisVec i) = ∑ k : Fin 2, (LM (basisVec i)) k • basisVec k := by
      funext k
      fin_cases k <;> simp [basisVec, Fin.sum_univ_two]
    have hcoord (i j : Fin 2) :
        ((Lg.comp LM) (basisVec i)) j =
          ∑ k : Fin 2, (LM (basisVec i)) k * (Lg (basisVec k)) j := by
      change (Lg (LM (basisVec i))) j = _
      rw [hdecomp i, map_sum]
      simp [map_smul, smul_eq_mul]
    let F : Fin 2 → Fin 2 → Fin 2 → ℝ := fun i j k =>
      (Q x i j * (LM (basisVec i)) k) * (Lg (basisVec k)) j
    calc
      (∑ i : Fin 2, ∑ j : Fin 2,
          Q x i j * ((Lg.comp LM) (basisVec i)) j) =
        ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, F i j k := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [hcoord]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          simp [F, mul_assoc]
      _ = ∑ j : Fin 2, ∑ k : Fin 2, ∑ i : Fin 2, F i j k := by
          calc
            (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, F i j k) =
              ∑ j : Fin 2, ∑ i : Fin 2, ∑ k : Fin 2, F i j k := by
                rw [Finset.sum_comm]
            _ = ∑ j : Fin 2, ∑ k : Fin 2, ∑ i : Fin 2, F i j k := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [Finset.sum_comm]
      _ = ∑ j : Fin 2, ∑ k : Fin 2,
          (∑ i : Fin 2, Q x i j * (LM (basisVec i)) k) *
            (Lg (basisVec k)) j := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          rw [← Finset.sum_mul]
      _ = ∑ j : Fin 2, ∑ k : Fin 2,
          (if j = k then 1 else 0) * (Lg (basisVec k)) j := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          rw [hPiolaChain j k]
      _ = ∑ j : Fin 2, (Lg (basisVec j)) j := by
          simp
  calc
    (∑ i : Fin 2, ∑ j : Fin 2,
        ((LQ i j) (basisVec i) * g (M x) j +
          Q x i j * ((Lg.comp LM) (basisVec i)) j)) =
      (∑ j : Fin 2, ∑ i : Fin 2,
        (LQ i j) (basisVec i) * g (M x) j) +
      ∑ i : Fin 2, ∑ j : Fin 2,
        Q x i j * ((Lg.comp LM) (basisVec i)) j := by
          simp_rw [Finset.sum_add_distrib]
          rw [Finset.sum_comm]
    _ = 0 + ∑ j : Fin 2, (Lg (basisVec j)) j := by rw [hfirst, hsecond]
    _ = vecDiv g (M x) := by
      rw [zero_add]
      unfold vecDiv
      apply Finset.sum_congr rfl
      intro j hj
      rw [spaceGrad, fderiv_apply hg.differentiableAt, hg.fderiv]
      simp [ContinuousLinearMap.comp_apply]

end AVenhance.Infra.Section5
