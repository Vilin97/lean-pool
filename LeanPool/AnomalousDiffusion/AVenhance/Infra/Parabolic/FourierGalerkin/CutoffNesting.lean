/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData

/-!
# Nested finite real Fourier spaces

This module transfers a coefficient vector from a cutoff into any larger symmetric cutoff. Both its
scalar synthesis and its gradient synthesis are preserved. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Extend a finite coefficient vector by zero along the injection into a larger Fourier cutoff. -/
def realFourierCoefficientsLift {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension M)) : Coefficients (RealFourierDimension N) :=
  WithLp.toLp 2 (fun j =>
    ∑ i : Fin (RealFourierDimension M),
      if realFourierIndexLiftFin hMN i = j then c i else 0)

theorem CutoffNesting.realFourierIndexLiftFin_injective {M N : ℕ} (hMN : M ≤ N) :
    Function.Injective (realFourierIndexLiftFin hMN) := by
  intro i j hij
  have hsource : (realFourierIndexEquivFin M).symm i =
      (realFourierIndexEquivFin M).symm j := by
    apply realFourierIndexLift_injective hMN
    apply (realFourierIndexEquivFin N).injective
    exact hij
  exact (realFourierIndexEquivFin M).symm.injective hsource

@[simp]
theorem realFourierCoefficientsLift_apply_lift {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension M)) (i : Fin (RealFourierDimension M)) :
    realFourierCoefficientsLift hMN c (realFourierIndexLiftFin hMN i) = c i := by
  classical
  change (∑ j : Fin (RealFourierDimension M),
      (if realFourierIndexLiftFin hMN j = realFourierIndexLiftFin hMN i then c j else 0)) = c i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hne : realFourierIndexLiftFin hMN j ≠ realFourierIndexLiftFin hMN i := by
      intro heq
      exact hji (CutoffNesting.realFourierIndexLiftFin_injective hMN heq)
    simp [hne]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Pointwise finite Fourier synthesis is unchanged by zero-extending its coefficients to a larger
cutoff. -/
theorem scalarExpansion_lift {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension M)) (x : Torus) :
    modeExpansion (RealFourierDimension N) (realFourierModeFin N)
        (realFourierCoefficientsLift hMN c) x =
      modeExpansion (RealFourierDimension M) (realFourierModeFin M) c x := by
  classical
  change (∑ j : Fin (RealFourierDimension N),
      (∑ i : Fin (RealFourierDimension M),
        if realFourierIndexLiftFin hMN i = j then c i else 0) * realFourierModeFin N j x) =
    ∑ i : Fin (RealFourierDimension M), c i * realFourierModeFin M i x
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    ∑ j : Fin (RealFourierDimension N),
        (if realFourierIndexLiftFin hMN i = j then c i else 0) *
          realFourierModeFin N j x =
      c i * realFourierModeFin N (realFourierIndexLiftFin hMN i) x := by
        rw [Finset.sum_eq_single (realFourierIndexLiftFin hMN i)]
        · simp
        · intro j hj hne
          have hne' : realFourierIndexLiftFin hMN i ≠ j := Ne.symm hne
          simp [hne']
        · intro hmem
          exact (hmem (Finset.mem_univ _)).elim
    _ = c i * realFourierModeFin M i x := by rw [realFourierModeFin_lift hMN]

/-- Scalar synthesis commutes with embedding a cutoff into a larger one. -/
theorem realFourierScalarMap_lift {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension M)) :
    realFourierScalarMap N (realFourierCoefficientsLift hMN c) =
      realFourierScalarMap M c := by
  apply Lp.ext
  filter_upwards [realFourierScalarMap_coeFn N (realFourierCoefficientsLift hMN c),
    realFourierScalarMap_coeFn M c] with x hN hM
  calc
    (realFourierScalarMap N (realFourierCoefficientsLift hMN c)) x =
        modeExpansion (RealFourierDimension N) (realFourierModeFin N)
          (realFourierCoefficientsLift hMN c) x := hN
    _ = modeExpansion (RealFourierDimension M) (realFourierModeFin M) c x :=
      scalarExpansion_lift hMN c x
    _ = (realFourierScalarMap M c) x := hM.symm

theorem CutoffNesting.gradientExpansion_lift {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension M)) (x : Torus) :
    (∑ j : Fin (RealFourierDimension N),
        (realFourierCoefficientsLift hMN c j) • realFourierModeGradFin N j x) =
      ∑ i : Fin (RealFourierDimension M), c i • realFourierModeGradFin M i x := by
  classical
  change (∑ j : Fin (RealFourierDimension N),
      (∑ i : Fin (RealFourierDimension M),
        if realFourierIndexLiftFin hMN i = j then c i else 0) •
          realFourierModeGradFin N j x) = _
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    ∑ j : Fin (RealFourierDimension N),
        (if realFourierIndexLiftFin hMN i = j then c i else 0) •
          realFourierModeGradFin N j x =
      c i • realFourierModeGradFin N (realFourierIndexLiftFin hMN i) x := by
        rw [Finset.sum_eq_single (realFourierIndexLiftFin hMN i)]
        · simp
        · intro j hj hne
          have hne' : realFourierIndexLiftFin hMN i ≠ j := Ne.symm hne
          simp [hne']
        · intro hmem
          exact (hmem (Finset.mem_univ _)).elim
    _ = c i • realFourierModeGradFin M i x := by rw [realFourierModeGradFin_lift hMN]

/-- Finite gradient synthesis commutes with embedding a cutoff into a larger one. -/
theorem realFourierGradientMap_lift {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension M)) :
    realFourierGradientMap N (realFourierCoefficientsLift hMN c) =
      realFourierGradientMap M c := by
  apply Lp.ext
  filter_upwards [realFourierGradientMap_coeFn N (realFourierCoefficientsLift hMN c),
    realFourierGradientMap_coeFn M c] with x hN hM
  calc
    ((realFourierGradientMap N (realFourierCoefficientsLift hMN c)) x : SpatialVector) =
        WithLp.toLp 2
          (∑ j : Fin (RealFourierDimension N),
            (realFourierCoefficientsLift hMN c j) • realFourierModeGradFin N j x) := hN
    _ = WithLp.toLp 2
        (∑ i : Fin (RealFourierDimension M), c i • realFourierModeGradFin M i x) :=
      congrArg (WithLp.toLp 2) (CutoffNesting.gradientExpansion_lift hMN c x)
    _ = ((realFourierGradientMap M c) x : SpatialVector) := hM.symm

end AVenhance.Infra.Parabolic.FourierGalerkin

end
