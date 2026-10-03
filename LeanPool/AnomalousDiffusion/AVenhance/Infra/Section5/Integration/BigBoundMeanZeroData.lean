/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Representation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBoundRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.PulledFluxSmooth

/-! Smoothness and periodicity of the two actual source errors used by `tiny`.
-/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

theorem BigBoundMeanZeroData.meanZeroData_matrixMulVec_contDiff
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : Vec 2 → Vec 2}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (A x).mulVec (V x)) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ j : Fin 2, A x i j * V x j)
  apply ContDiff.sum
  intro j hj
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul (contDiff_pi.mp hV j)

/-- At a positive time, `sourceErrorD` and `iterateError` are smooth and
periodic under the actual big-bound estimate classical and iterate premises. -/
theorem actual_sourceErrors_regular_of_iterates {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (hm : 1 ≤ m) (κm κprev : ℝ) (θ₀ : Vec 2 → ℝ)
    (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ)
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    {t : ℝ} (ht : 0 < t) :
    (ContDiff ℝ (⊤ : ℕ∞) (sourceErrorD I hΦ m κm (T (Nstar β)) t) ∧
      IsZ2Periodic (sourceErrorD I hΦ m κm (T (Nstar β)) t)) ∧
    (ContDiff ℝ (⊤ : ℕ∞) (iterateError I hΦ m κm κprev T t) ∧
      IsZ2Periodic (iterateError I hΦ m κm κprev T t)) := by
  classical
  let Tlast : ℝ → Vec 2 → ℝ := T (Nstar β)
  have hTsm : ContDiff ℝ (⊤ : ℕ∞) (Tlast t) :=
    Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.le
  have hTper : IsZ2Periodic (Tlast t) :=
    Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.le
  have hGradSm : ContDiff ℝ (⊤ : ℕ∞) (spaceGrad (Tlast t)) :=
    Infra.Section4.iterate_gradient_smooth hTsm
  have hGradPer : IsZ2Periodic (spaceGrad (Tlast t)) :=
    Infra.Section4.iterate_gradient_periodic (hTsm.of_le (by simp)) hTper
  have hFlowSm (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact (Infra.Section4.amnr_flowGrad_joint_contDiff_infty I hΦ m l i j).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hFlowPer (l : ℤ) : IsZ2Periodic (I.flowGrad hΦ m l t) := by
    intro z x
    ext i j
    exact Infra.Section4.amnr_flowGrad_spatial_periodic I hΦ m l t i j z x
  let main : Vec 2 → Vec 2 := fun y =>
    ∑' l : ℤ, I.hatXiML m l t •
      ((I.flowGrad hΦ m l t y).transpose.mulVec
        ((I.Jhat κm m t - I.flux κm m t).mulVec
          ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (Tlast t) y))))
  have hMainSm : ContDiff ℝ (⊤ : ℕ∞) main :=
    LeftJacobian.contDiff_pulledGapFlux I hΦ m hm (I.Jhat κm m t - I.flux κm m t) Tlast t hTsm
  have hMainPer : IsZ2Periodic main := by
    intro z x
    refine tsum_congr fun l => ?_
    rw [hFlowPer l z x, hGradPer z x]
  have hAmnrCont (n : ℕ) (i j k : Fin 2) :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun x => I.Amnr hΦ m κm n Tlast (Jcut β) t x i j k) :=
    amnr_slice_contDiff_infty I hΦ hm hθprev hT n (Jcut β) i j k ht
  have hAmnrPer : ∀ n (i j k : Fin 2) (z : Fin 2 → ℤ) (x : Vec 2),
      I.Amnr hΦ m κm n Tlast (Jcut β) t (x + latticeShift z) i j k =
        I.Amnr hΦ m κm n Tlast (Jcut β) t x i j k := by
    have hper := amnr_periodic_of_iterates I hΦ hm hθprev hT
    intro n i j k z x
    exact hper (Jcut β) t ht n z x i j k
  let tail : Vec 2 → Vec 2 := fun x i =>
      ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κm n Tlast (Jcut β) t x i j k *
          I.qMNR κm m n (Jcut β) t j k
  have hTailSm : ContDiff ℝ (⊤ : ℕ∞) tail := by
    apply contDiff_pi.mpr
    intro i
    apply ContDiff.sum
    intro n hn
    apply ContDiff.sum
    intro j hj
    apply ContDiff.sum
    intro k hk
    exact (hAmnrCont n i j k).mul contDiff_const
  have hTailPer : IsZ2Periodic tail := by
    intro z x
    funext i
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [hAmnrPer n i j k z x]
  have hSourceSm : ContDiff ℝ (⊤ : ℕ∞)
      (sourceErrorD I hΦ m κm Tlast t) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => main x + tail x)
    exact hMainSm.add hTailSm
  have hSourcePer : IsZ2Periodic (sourceErrorD I hΦ m κm Tlast t) := by
    intro z x
    change main (x + latticeShift z) + tail (x + latticeShift z) =
      main x + tail x
    rw [hMainPer z x, hTailPer z x]
  have hPrevIndex : Nstar β - 1 ≤ Nstar β := by omega
  have hPrevSm : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β - 1) t) :=
    Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev hPrevIndex ht.le
  have hPrevPer : IsZ2Periodic (T (Nstar β - 1) t) :=
    Infra.Section4.tIterate_periodic I hΦ hT hθprev hPrevIndex ht.le
  have hPrevGradSm : ContDiff ℝ (⊤ : ℕ∞)
      (spaceGrad (T (Nstar β - 1) t)) :=
    Infra.Section4.iterate_gradient_smooth hPrevSm
  have hPrevGradPer : IsZ2Periodic (spaceGrad (T (Nstar β - 1) t)) :=
    Infra.Section4.iterate_gradient_periodic (hPrevSm.of_le (by simp)) hPrevPer
  have hSmatSm : ContDiff ℝ (⊤ : ℕ∞) (I.sMat hΦ m κm t) :=
    sMat_spatial_contDiff I hΦ m hm κm t hFlowSm
  have hSmatPer : IsZ2Periodic (I.sMat hΦ m κm t) := by
    exact (Infra.Section4.sMat_coarseCoeffForm I hΦ m κm).periodic t hFlowPer
  let M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun x =>
    I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      I.sMat hΦ m κm t x
  let gradDiff : Vec 2 → Vec 2 := fun x =>
    spaceGrad (T (Nstar β - 1) t) x - spaceGrad (T (Nstar β) t) x
  have hMsm : ContDiff ℝ (⊤ : ℕ∞) M := by
    dsimp [M]
    exact (contDiff_const.sub contDiff_const).add hSmatSm
  have hMper : IsZ2Periodic M := by
    intro z x
    dsimp [M]
    rw [hSmatPer z x]
  have hGradDiffSm : ContDiff ℝ (⊤ : ℕ∞) gradDiff := by
    exact hPrevGradSm.sub hGradSm
  have hGradDiffPer : IsZ2Periodic gradDiff := by
    intro z x
    dsimp [gradDiff]
    rw [hPrevGradPer z x, hGradPer z x]
  have hIterateSm : ContDiff ℝ (⊤ : ℕ∞)
      (iterateError I hΦ m κm κprev T t) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => (M x).mulVec (gradDiff x))
    exact BigBoundMeanZeroData.meanZeroData_matrixMulVec_contDiff hMsm hGradDiffSm
  have hIteratePer : IsZ2Periodic (iterateError I hΦ m κm κprev T t) := by
    intro z x
    change (M (x + latticeShift z)).mulVec (gradDiff (x + latticeShift z)) = _
    rw [hMper z x, hGradDiffPer z x]
    simp only [iterateError, M, gradDiff]
  exact ⟨⟨by simpa [Tlast] using hSourceSm,
      by simpa [Tlast] using hSourcePer⟩, ⟨hIterateSm, hIteratePer⟩⟩

end AVenhance.Infra.Section5.Integration

end
