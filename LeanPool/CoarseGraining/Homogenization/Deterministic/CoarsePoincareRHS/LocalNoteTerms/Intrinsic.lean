/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.LocalNoteTerms.Bounded

/-! # Intrinsic -/

namespace Homogenization

noncomputable section

namespace ZeroTraceDirichletCorrectorData

variable {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}

theorem sq_cubeBesovNegativeVectorSeminormTwo_le_descendantsAverage_add_intrinsicAbsorbedLocalError_two_two_of_childBddAbove
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ} (s : ℝ) {η : ℝ}
    (hs : 0 < s) (hη : 0 < η) (hη_lt : η < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : MemVectorL2 (cubeSet Q) u)
    (hgrad :
      CubeAverageGradientEnergyControl Q a (fun x => w.toH1.grad x)
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hmem : MemVectorL2 (cubeSet Q) g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hgradρ : MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
      (2 : ENNReal) (normalizedCubeMeasure Q))
    (hBg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s
        (fun x => g x - cubeAverageVec Q g))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x)))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g)))
    (hchildBdd :
      ∀ R ∈ descendantsAtDepth Q 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N u)) :
    (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2) +
      coarsePoincareRHSIntrinsicAbsorbedLocalError Q a g u s η := by
  have hchild :
      ∀ R ∈ descendantsAtDepth Q 1, ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminormTwo R s N u ≤
          cubeBesovNegativeVectorSeminormTwo R s u := by
    intro R hR N
    exact
      cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
        R s u (hchildBdd R hR) N
  have hmain :=
    ρ.sq_cubeBesovNegativeVectorSeminormTwo_le_descendantsAverage_add_uCoeffEnergy_add_absorbed_uSq_gSq_two_two_of_partialChildBounds
      (u := u) w s (Bchild := fun R => cubeBesovNegativeVectorSeminormTwo R s u)
      hs hη hη_lt hEll hu hgrad hsum huw
      hmem hg hgradρ hBg huBdd hwBdd hgBdd hchild
  simpa [coarsePoincareRHSIntrinsicAbsorbedLocalError,
    coarsePoincareRHSIntrinsicLocalEnergyError,
    coarsePoincareRHSIntrinsicLocalForceMultiplier,
    coarsePoincareRHSLocalCenteredForceSeminorm,
    coarsePoincareRHSLocalCoeff, add_assoc] using hmain

theorem sq_cubeBesovNegativeVectorSeminormTwo_le_discount_next_add_intrinsicAbsorbedLocalError_noteEta_of_parent_potential_solenoidal
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {n : ℕ}
    {a : CoeffField d} {g u : Vec d → Vec d} {lam Lam s : ℝ}
    (hs : 0 < s)
    (hu_potential : IsPotentialOn (cubeSet Q) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x))
    (hR : R ∈ descendantsAtDepth Q n)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hLocalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N g)) :
    (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
      coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
      coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s
        (coarsePoincareRHSNoteEta s) := by
  have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEll.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hgR :
      MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure R) :=
    memLp_on_descendant_of_memLp_generic (E := Vec d) hR hg
  have hgMemR : MemVectorL2 (cubeSet R) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R hgR
  have hu_potential_R : IsPotentialOn (cubeSet R) u :=
    hu_potential.restrict_cubeSet_of_mem_descendantsAtDepth hR
  have huMemR : MemVectorL2 (cubeSet R) u := by
    rcases hu_potential_R with ⟨v, hv⟩
    simpa [← hv] using v.grad_memVectorL2
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hsum :
      Summable (fun m : ℕ =>
        geometricWeight s 2 m *
          maxDescendantSigmaStarInvNormAtScale R (R.scale - (m : ℤ)) a) :=
    summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
      (Q := R) (a := a) s hs hEllR hOrigin
  rcases
      ZeroTraceDirichletCorrectorData.exists_corrector_aHarmonicRemainder_of_parent_potential_solenoidal
        (Q := Q) (R := R) (n := n) (a := a) (g := g) (u := u)
        (lam := lam) (Lam := Lam)
        hu_potential hu_residual hR hEllR huMemR hgMemR with
    ⟨ρ, w, huw⟩
  have hgradScalar :
      CubeAverageGradientEnergyControl R a (fun x => w.toH1.grad x)
        (fun x => scalarVariationEnergyIntegrand a w x) :=
    cubeAverageGradientEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
      (Q := R) (a := a) hEllR w hOrigin
  have hgradCoeff :
      CubeAverageGradientEnergyControl R a (fun x => w.toH1.grad x)
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)) := by
    simpa [coefficientEnergyDensity, scalarVariationEnergyIntegrand] using! hgradScalar
  have hη_pos : 0 < coarsePoincareRHSNoteEta s :=
    coarsePoincareRHSNoteEta_pos hs
  have hη_lt_one : coarsePoincareRHSNoteEta s < 1 := by
    have hη_lt_half := coarsePoincareRHSNoteEta_lt_half hs
    linarith
  have huLp :
      MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R huMemR
  have hwLp :
      MeasureTheory.MemLp (fun x => w.toH1.grad x) (2 : ENNReal)
        (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R w.toH1.grad_memVectorL2
  have hgradρ :
      MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
        (2 : ENNReal) (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R
      ρ.toH10.toH1Function.grad_memVectorL2
  have huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo R s N u) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs u huLp
  have hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo R s N
          (fun x => w.toH1.grad x)) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs
      (fun x => w.toH1.grad x) hwLp
  have hchildBdd :
      ∀ S ∈ descendantsAtDepth R 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo S s N u) := by
    intro S hS
    have huS :
        MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure S) :=
      memLp_on_descendant_of_memLp_generic (E := Vec d) hS huLp
    exact cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp S hs u huS
  have hmemDesc :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth R j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S) := by
    intro j S hS
    exact memLp_on_descendant_of_memLp_generic (E := Vec d) hS hgR
  have hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N
          (fun x => g x - cubeAverageVec R g)) := by
    rcases hLocalBdd with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro x ⟨N, rfl⟩
    change
      cubeBesovPositiveVectorPartialSeminormTwo R s N
          (fun x => g x - cubeAverageVec R g) ≤ B
    rw [cubeBesovPositiveVectorPartialSeminormTwo_sub_const R s N g
      (cubeAverageVec R g) (fun j _ S hS => hmemDesc j S hS)]
    exact hB ⟨N, rfl⟩
  have hBg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo R s
        (fun x => g x - cubeAverageVec R g) :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove
      R s (fun x => g x - cubeAverageVec R g) hgBdd
  have hmain :=
    ρ.sq_cubeBesovNegativeVectorSeminormTwo_le_descendantsAverage_add_intrinsicAbsorbedLocalError_two_two_of_childBddAbove
      (u := u) w s hs hη_pos hη_lt_one hEllR huMemR hgradCoeff hsum huw
      hgMemR hgR hgradρ hBg huBdd hwBdd hgBdd hchildBdd
  simpa [coarsePoincareRHSDiscount, coarsePoincareRHSRn] using hmain


end ZeroTraceDirichletCorrectorData

end

end Homogenization
