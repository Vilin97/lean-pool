/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.FluxComparisonBridges
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspNegativeLocalization

/-!
# Root-to-descendant localization for the Chapter 3 flux defect

This is the exact localization step which identifies the generic smooth-dual
negative-norm descendant average with the source-facing flux-defect average.
-/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open scoped ENNReal

noncomputable section

/-- The root scalar-comparator defect localizes to the exact normalized
average of its descendant flux defects. -/
theorem centeredCubeRootFluxDefectL2Field_negativeWspSmoothDual_localize
    {d : ℕ} [NeZero d] (m n : ℤ) (hnm : n < m)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
    (sigma0 : ℝ) (u : H1Function (openCubeSet (originCube d m)))
    (s : FractionalOrder) (p : FiniteLpExponent) :
    cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
        (centeredCubeRootFluxDefectL2Field m a sigma0 u) ≤
      ENNReal.ofReal (Real.rpow 3 (s.1 * (((m - n : ℤ) : ℝ)))) *
        centeredCubeLocalFluxDefectSmoothDualLpAverage
          m n hnm a sigma0 u s p := by
  let j : ℕ := Int.toNat (m - n)
  have hscale : descendantsAtScale (originCube d m) n =
      descendantsAtDepth (originCube d m) j := by
    simpa [originCube, j] using
      descendantsAtScale_eq_descendantsAtDepth (originCube d m) (le_of_lt hnm)
  have hj : (j : ℝ) = ((m - n : ℤ) : ℝ) := by
    change ((Int.toNat (m - n) : ℕ) : ℝ) = ((m - n : ℤ) : ℝ)
    norm_cast
    exact Int.toNat_of_nonneg (by omega)
  have hlocal :
      descendantsENNAverage (originCube d m) j (fun R =>
        if hR : R ∈ descendantsAtDepth (originCube d m) j then
          cubeEuclideanNegativeWspSmoothDualENorm R s p
            ((centeredCubeRootFluxDefectL2Field m a sigma0 u).restrictToSubcube
              (openCubeSet_subset_of_mem_descendantsAtDepth hR)) ^
              p.exponent.toReal
        else 0) ^ p.exponent.toReal⁻¹ =
        centeredCubeLocalFluxDefectSmoothDualLpAverage m n hnm a sigma0 u s p := by
    let D := descendantsAtDepth (originCube d m) j
    let S := descendantsAtScale (originCube d m) n
    let e : {R // R ∈ D} ≃ {R // R ∈ S} :=
      Equiv.subtypeEquivRight fun R => by
        change R ∈ descendantsAtDepth (originCube d m) j ↔
          R ∈ descendantsAtScale (originCube d m) n
        rw [hscale]
    have he_mem (R : {R // R ∈ D}) : e R ∈ S.attach := by
      simp only [Finset.mem_attach]
    have hsum :
        ∑ R ∈ D.attach,
          cubeEuclideanNegativeWspSmoothDualENorm R.1 s p
            ((centeredCubeRootFluxDefectL2Field m a sigma0 u).restrictToSubcube
              (openCubeSet_subset_of_mem_descendantsAtDepth R.2)) ^
              p.exponent.toReal =
        ∑ R ∈ S.attach,
          cubeEuclideanNegativeWspSmoothDualENorm R.1 s p
            (centeredCubeLocalFluxDefectL2Field m n hnm a sigma0 u R.1 R.2) ^
              p.exponent.toReal := by
      refine Finset.sum_bij (fun R _ => e R) ?_ ?_ ?_ ?_
      · intro R hR
        exact he_mem R
      · intro R₁ _ R₂ _ hR
        exact e.injective hR
      · intro R hR
        refine ⟨e.symm R, by simp only [Finset.mem_attach], ?_⟩
        exact e.apply_symm_apply R
      · intro R hR
        have hR' : R.1 ∈ D := R.2
        simp only [e]
        change cubeEuclideanNegativeWspSmoothDualENorm R.1 s p
            ((centeredCubeRootFluxDefectL2Field m a sigma0 u).restrictToSubcube
              (openCubeSet_subset_of_mem_descendantsAtDepth hR')) ^
              p.exponent.toReal =
          cubeEuclideanNegativeWspSmoothDualENorm R.1 s p
            (centeredCubeLocalFluxDefectL2Field m n hnm a sigma0 u R.1
              ((e R).property)) ^ p.exponent.toReal
        rfl
    unfold descendantsENNAverage centeredCubeLocalFluxDefectSmoothDualLpAverage
    simp only [D] at hsum
    rw [← hsum]
    rw [hscale]
    rw [← Finset.sum_attach]
    congr 2
    apply Finset.sum_congr rfl
    intro R hR
    simp only [dif_pos R.2]
  have hmain := cubeEuclideanNegativeWspSmoothDualENorm_le_descendantsENNAverage
    (originCube d m) j s p (centeredCubeRootFluxDefectL2Field m a sigma0 u)
  rw [hj, hlocal] at hmain
  rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 3)] at hmain
  simpa only [mul_comm] using! hmain

end

end ABK26
end Ch03
end Book
end Homogenization
