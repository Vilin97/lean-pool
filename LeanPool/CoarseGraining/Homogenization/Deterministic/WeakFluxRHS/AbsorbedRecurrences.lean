/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AbsorbedComponentBounds

/-! # Absorbed Recurrences -/

namespace Homogenization

noncomputable section

namespace MeanZeroNeumannCorrectorData

variable {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}

/-- Local weak-flux recurrence packaged with the explicit corrector-energy
local-error envelope. -/
theorem sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_correctorEnergyLocalError_of_childBddAbove
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (s : ℝ) (hs : 0 < s)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_mem : MemVectorL2 (cubeSet Q) u)
    (hg : MemVectorL2 (cubeSet Q) g)
    (hflux :
      CubeAverageFluxEnergyControl Q a
        (fun x => matVecMul (a x) (w.toH1.grad x))
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    (hchildBdd :
      ∀ R ∈ descendantsAtDepth Q 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (u x)))) :
    (cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (u x))) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R =>
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => matVecMul (a x) (u x))) ^ 2) +
      weakFluxRHSCorrectorEnergyLocalError Q a u
        (fun x => ω.toH1MeanZero.toH1Function.grad x) s := by
  have hstep :=
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_correctorCoeffEnergy_of_childBddAbove
      (u := u) w s hs hEll hu_mem hg hflux hsum huw hchildBdd
  simpa [weakFluxRHSCorrectorEnergyLocalError, add_assoc] using hstep

/-- Local absorbed weak-flux recurrence packaged with the explicit absorbed
local-error envelope. -/
theorem sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_absorbedLocalError_of_childBddAbove
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (s : ℝ) {η : ℝ} (hs : 0 < s) (hη : 0 < η)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_mem : MemVectorL2 (cubeSet Q) u)
    (hg_mem : MemVectorL2 (cubeSet Q) g)
    (hflux :
      CubeAverageFluxEnergyControl Q a
        (fun x => matVecMul (a x) (w.toH1.grad x))
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    (hchildBdd :
      ∀ R ∈ descendantsAtDepth Q 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (u x))))
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
          (fun x => g x - cubeAverageVec Q g))) :
    (cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (u x))) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R =>
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => matVecMul (a x) (u x))) ^ 2) +
      weakFluxRHSAbsorbedLocalError Q a g u (fun x => w.toH1.grad x) s η := by
  have hstep :=
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_eta_uSq_eta_wSq_invEta_gSq_of_childBddAbove
      (u := u) w s hs hη hEll hu_mem hg_mem hflux hsum huw
      hchildBdd huBdd hwBdd hgBdd
  simpa [weakFluxRHSAbsorbedLocalError, add_assoc] using hstep

end MeanZeroNeumannCorrectorData

/-- Descendant-cube coefficient-energy recurrence with the explicit
corrector-energy local-error envelope. -/
theorem exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepCorrectorEnergyLocalError_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
    {d : ℕ} [NeZero d] {P R : TriadicCube d} (a : CoeffField d)
    {n : ℕ} {lam Lam s : ℝ} {u g : Vec d → Vec d}
    (hs : 0 < s)
    (hu_potential : IsPotentialOn (cubeSet P) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet P) (fun x => matVecMul (a x) (u x) - g x))
    (hR : R ∈ descendantsAtDepth P n)
    (hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_memR : MemVectorL2 (cubeSet R) u)
    (hg_memR : MemVectorL2 (cubeSet R) g)
    (hC : H1CoerciveEstimate (cubeSet R))
    (hDataR : OpenCubeDescendantDeterministicCoarseData R a)
    (hsum :
      Summable (fun m : ℕ =>
        geometricWeight s 2 m *
          maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a))
    (hchildBdd :
      ∀ S ∈ descendantsAtDepth R 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo S s N
            (fun x => matVecMul (a x) (u x)))) :
    ∃ ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g),
      ∃ w : AHarmonicFunction a (cubeSet R),
        (∀ x ∈ cubeSet R,
          u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (cubeBesovNegativeVectorSeminormTwo R s
            (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSCorrectorEnergyLocalError R a u
            (fun x => ω.toH1MeanZero.toH1Function.grad x) s := by
  rcases
      MeanZeroNeumannCorrectorData.exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepCoeffEnergy_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
        (P := P) (R := R) (a := a) (n := n)
        (lam := lam) (Lam := Lam) (s := s) (u := u) (g := g)
        hs hu_potential hu_residual hR hEllR hu_memR hg_memR hC hDataR
        hsum hchildBdd with
    ⟨ω, w, huw, hstep⟩
  refine ⟨ω, w, huw, ?_⟩
  simpa [weakFluxRHSCorrectorEnergyLocalError, add_assoc] using hstep

/--
Choose Neumann-corrector gradients on all descendants of a parent cube and
package the local corrected-energy weak-flux recurrence in the global-selector
shape consumed by the public corrected route.
-/
theorem exists_correctorGradientSelector_fluxSeminormStepCorrectorEnergyLocalError_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    {s lam Lam : ℝ} {u g : Vec d → Vec d}
    (hs : 0 < s)
    (hu_potential : IsPotentialOn (cubeSet Q) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x))
    (hEll :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_mem :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) u)
    (hg_mem :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) g)
    (hC :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        H1CoerciveEstimate (cubeSet R))
    (hData :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        OpenCubeDescendantDeterministicCoarseData R a)
    (hsum :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        Summable (fun m : ℕ =>
          geometricWeight s 2 m *
            maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a))
    (hchildBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        ∀ S ∈ descendantsAtDepth R 1,
          BddAbove (Set.range fun N : ℕ =>
            cubeBesovNegativeVectorPartialSeminormTwo S s N
              (fun x => matVecMul (a x) (u x)))) :
    ∃ z : TriadicCube d → Vec d → Vec d,
      (∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        ∃ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          z R = (fun x => ω.toH1MeanZero.toH1Function.grad x)) ∧
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSCorrectorEnergyLocalError R a u (z R) s := by
  classical
  let IsDescendantOfQ : TriadicCube d → Prop :=
    fun R => ∃ n : ℕ, R ∈ descendantsAtDepth Q n
  have hlocal :
      ∀ R : TriadicCube d, IsDescendantOfQ R →
        ∃ ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g),
          ∃ w : AHarmonicFunction a (cubeSet R),
            (∀ x ∈ cubeSet R,
              u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
            (cubeBesovNegativeVectorSeminormTwo R s
                (fun x => matVecMul (a x) (u x))) ^ 2 ≤
              Real.rpow (3 : ℝ) (-2 * s) *
                descendantsAverage R 1
                  (fun S =>
                    (cubeBesovNegativeVectorSeminormTwo S s
                      (fun x => matVecMul (a x) (u x))) ^ 2) +
              weakFluxRHSCorrectorEnergyLocalError R a u
                (fun x => ω.toH1MeanZero.toH1Function.grad x) s := by
    intro R hRdesc
    rcases hRdesc with ⟨n, hR⟩
    exact
      exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepCorrectorEnergyLocalError_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
        (P := Q) (R := R) (a := a) (n := n)
        (lam := lam) (Lam := Lam) (s := s) (u := u) (g := g)
        hs hu_potential hu_residual hR
        (hEll R ⟨n, hR⟩) (hu_mem R ⟨n, hR⟩) (hg_mem R ⟨n, hR⟩)
        (hC R ⟨n, hR⟩) (hData R ⟨n, hR⟩) (hsum R ⟨n, hR⟩)
        (hchildBdd R ⟨n, hR⟩)
  let z : TriadicCube d → Vec d → Vec d :=
    fun R =>
      if hR : IsDescendantOfQ R then
        fun x => (Classical.choose (hlocal R hR)).toH1MeanZero.toH1Function.grad x
      else
        0
  refine ⟨z, ?_, ?_⟩
  · intro R hRdesc
    let ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g) :=
      Classical.choose (hlocal R hRdesc)
    have hz :
        z R = fun x => ω.toH1MeanZero.toH1Function.grad x := by
      change
        (if hR : IsDescendantOfQ R then
          fun x => (Classical.choose (hlocal R hR)).toH1MeanZero.toH1Function.grad x
        else 0) = fun x => ω.toH1MeanZero.toH1Function.grad x
      rw [dif_pos hRdesc]
    exact ⟨ω, hz⟩
  · intro j R hR
    have hRdesc : IsDescendantOfQ R := ⟨j, hR⟩
    let ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g) :=
      Classical.choose (hlocal R hRdesc)
    have hz :
        z R = fun x => ω.toH1MeanZero.toH1Function.grad x := by
      change
        (if hR : IsDescendantOfQ R then
          fun x => (Classical.choose (hlocal R hR)).toH1MeanZero.toH1Function.grad x
        else 0) = fun x => ω.toH1MeanZero.toH1Function.grad x
      rw [dif_pos hRdesc]
    have hstep :=
      (Classical.choose_spec (Classical.choose_spec (hlocal R hRdesc))).2
    rw [hz]
    exact hstep

/-- Descendant-cube absorbed recurrence with the explicit absorbed local-error
envelope. -/
theorem exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepAbsorbedLocalError_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
    {d : ℕ} [NeZero d] {P R : TriadicCube d} (a : CoeffField d)
    {n : ℕ} {lam Lam s η : ℝ} {u g : Vec d → Vec d}
    (hs : 0 < s) (hη : 0 < η)
    (hu_potential : IsPotentialOn (cubeSet P) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet P) (fun x => matVecMul (a x) (u x) - g x))
    (hR : R ∈ descendantsAtDepth P n)
    (hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_memR : MemVectorL2 (cubeSet R) u)
    (hg_memR : MemVectorL2 (cubeSet R) g)
    (hC : H1CoerciveEstimate (cubeSet R))
    (hDataR : OpenCubeDescendantDeterministicCoarseData R a)
    (hsum :
      Summable (fun m : ℕ =>
        geometricWeight s 2 m *
          maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a))
    (hchildBdd :
      ∀ S ∈ descendantsAtDepth R 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo S s N
            (fun x => matVecMul (a x) (u x))))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo R s N u))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N
          (fun x => g x - cubeAverageVec R g))) :
    ∃ ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g),
      ∃ w : AHarmonicFunction a (cubeSet R),
        (∀ x ∈ cubeSet R,
          u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => w.toH1.grad x)) →
        (cubeBesovNegativeVectorSeminormTwo R s
            (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSAbsorbedLocalError R a g u (fun x => w.toH1.grad x) s η) := by
  rcases
      MeanZeroNeumannCorrectorData.exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepAbsorbedShortTerm_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
        (P := P) (R := R) (a := a) (n := n)
        (lam := lam) (Lam := Lam) (s := s) (η := η) (u := u) (g := g)
        hs hη hu_potential hu_residual hR hEllR hu_memR hg_memR hC hDataR
        hsum hchildBdd huBdd hgBdd with
    ⟨ω, w, huw, hstep⟩
  refine ⟨ω, w, huw, ?_⟩
  intro hwBdd
  simpa [weakFluxRHSAbsorbedLocalError, add_assoc] using hstep hwBdd

/--
Choose harmonic remainders on all descendants of a parent cube and package the
absorbed weak-flux local recurrence in the global-iteration shape.

The only remaining local assumption after the selector is chosen is
boundedness of the selected harmonic remainder's finite negative Besov
partials, exactly the boundedness input required by the local absorbed step.
-/
theorem exists_harmonicRemainderSelector_fluxSeminormStepAbsorbedLocalError_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    {s η lam Lam : ℝ} {u g : Vec d → Vec d}
    (hs : 0 < s) (hη : 0 < η)
    (hu_potential : IsPotentialOn (cubeSet Q) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x))
    (hEll :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_mem :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) u)
    (hg_mem :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) g)
    (hC :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        H1CoerciveEstimate (cubeSet R))
    (hData :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        OpenCubeDescendantDeterministicCoarseData R a)
    (hsum :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        Summable (fun m : ℕ =>
          geometricWeight s 2 m *
            maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a))
    (hchildBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        ∀ S ∈ descendantsAtDepth R 1,
          BddAbove (Set.range fun N : ℕ =>
            cubeBesovNegativeVectorPartialSeminormTwo S s N
              (fun x => matVecMul (a x) (u x))))
    (huBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N u))
    (hgBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N
            (fun x => g x - cubeAverageVec R g))) :
    ∃ v : TriadicCube d → Vec d → Vec d,
      (∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N (v R))) →
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSAbsorbedLocalError R a g u (v R) s η := by
  classical
  let IsDescendantOfQ : TriadicCube d → Prop :=
    fun R => ∃ n : ℕ, R ∈ descendantsAtDepth Q n
  have hlocal :
      ∀ R : TriadicCube d, IsDescendantOfQ R →
        ∃ ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g),
          ∃ w : AHarmonicFunction a (cubeSet R),
            (∀ x ∈ cubeSet R,
              u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
            (BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => w.toH1.grad x)) →
            (cubeBesovNegativeVectorSeminormTwo R s
                (fun x => matVecMul (a x) (u x))) ^ 2 ≤
              Real.rpow (3 : ℝ) (-2 * s) *
                descendantsAverage R 1
                  (fun S =>
                    (cubeBesovNegativeVectorSeminormTwo S s
                      (fun x => matVecMul (a x) (u x))) ^ 2) +
              weakFluxRHSAbsorbedLocalError R a g u (fun x => w.toH1.grad x) s η) := by
    intro R hRdesc
    rcases hRdesc with ⟨n, hR⟩
    exact
      exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepAbsorbedLocalError_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
        (P := Q) (R := R) (a := a) (n := n)
        (lam := lam) (Lam := Lam) (s := s) (η := η) (u := u) (g := g)
        hs hη hu_potential hu_residual hR
        (hEll R ⟨n, hR⟩) (hu_mem R ⟨n, hR⟩) (hg_mem R ⟨n, hR⟩)
        (hC R ⟨n, hR⟩) (hData R ⟨n, hR⟩) (hsum R ⟨n, hR⟩)
        (hchildBdd R ⟨n, hR⟩) (huBdd R ⟨n, hR⟩) (hgBdd R ⟨n, hR⟩)
  let v : TriadicCube d → Vec d → Vec d :=
    fun R =>
      if hR : IsDescendantOfQ R then
        fun x => (Classical.choose (Classical.choose_spec (hlocal R hR))).toH1.grad x
      else
        0
  refine ⟨v, ?_⟩
  intro hvBdd j R hR
  have hRdesc : IsDescendantOfQ R := ⟨j, hR⟩
  let ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g) :=
    Classical.choose (hlocal R hRdesc)
  let w : AHarmonicFunction a (cubeSet R) :=
    Classical.choose (Classical.choose_spec (hlocal R hRdesc))
  have hv :
      v R = fun x => w.toH1.grad x := by
    simp [v, hRdesc, w]
  have hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo R s N
          (fun x => w.toH1.grad x)) := by
    simpa [hv] using hvBdd R hRdesc
  have hspec :
      (∀ x ∈ cubeSet R,
        u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
      (BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo R s N
          (fun x => w.toH1.grad x)) →
      (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
        Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage R 1
            (fun S =>
              (cubeBesovNegativeVectorSeminormTwo S s
                (fun x => matVecMul (a x) (u x))) ^ 2) +
        weakFluxRHSAbsorbedLocalError R a g u (fun x => w.toH1.grad x) s η) := by
    simpa [ω, w] using
      Classical.choose_spec (Classical.choose_spec (hlocal R hRdesc))
  simpa [hv] using hspec.2 hwBdd

/--
Choose harmonic remainders on all descendants and also expose that each
selected value is the gradient of one of the local harmonic remainders produced
by the centered Neumann-corrector construction.
-/
theorem exists_harmonicRemainderSelector_fluxSeminormStepAbsorbedLocalError_with_decomposition_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    {s η lam Lam : ℝ} {u g : Vec d → Vec d}
    (hs : 0 < s) (hη : 0 < η)
    (hu_potential : IsPotentialOn (cubeSet Q) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x))
    (hEll :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_mem :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) u)
    (hg_mem :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) g)
    (hC :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        H1CoerciveEstimate (cubeSet R))
    (hData :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        OpenCubeDescendantDeterministicCoarseData R a)
    (hsum :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        Summable (fun m : ℕ =>
          geometricWeight s 2 m *
            maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a))
    (hchildBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        ∀ S ∈ descendantsAtDepth R 1,
          BddAbove (Set.range fun N : ℕ =>
            cubeBesovNegativeVectorPartialSeminormTwo S s N
              (fun x => matVecMul (a x) (u x))))
    (huBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N u))
    (hgBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N
            (fun x => g x - cubeAverageVec R g))) :
    ∃ v : TriadicCube d → Vec d → Vec d,
      (∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        ∃ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∃ w : AHarmonicFunction a (cubeSet R),
            v R = (fun x => w.toH1.grad x) ∧
            ∀ x ∈ cubeSet R,
              u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
      ((∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N (v R))) →
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSAbsorbedLocalError R a g u (v R) s η) := by
  classical
  let IsDescendantOfQ : TriadicCube d → Prop :=
    fun R => ∃ n : ℕ, R ∈ descendantsAtDepth Q n
  have hlocal :
      ∀ R : TriadicCube d, IsDescendantOfQ R →
        ∃ ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g),
          ∃ w : AHarmonicFunction a (cubeSet R),
            (∀ x ∈ cubeSet R,
              u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
            (BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => w.toH1.grad x)) →
            (cubeBesovNegativeVectorSeminormTwo R s
                (fun x => matVecMul (a x) (u x))) ^ 2 ≤
              Real.rpow (3 : ℝ) (-2 * s) *
                descendantsAverage R 1
                  (fun S =>
                    (cubeBesovNegativeVectorSeminormTwo S s
                      (fun x => matVecMul (a x) (u x))) ^ 2) +
              weakFluxRHSAbsorbedLocalError R a g u (fun x => w.toH1.grad x) s η) := by
    intro R hRdesc
    rcases hRdesc with ⟨n, hR⟩
    exact
      exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepAbsorbedLocalError_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
        (P := Q) (R := R) (a := a) (n := n)
        (lam := lam) (Lam := Lam) (s := s) (η := η) (u := u) (g := g)
        hs hη hu_potential hu_residual hR
        (hEll R ⟨n, hR⟩) (hu_mem R ⟨n, hR⟩) (hg_mem R ⟨n, hR⟩)
        (hC R ⟨n, hR⟩) (hData R ⟨n, hR⟩) (hsum R ⟨n, hR⟩)
        (hchildBdd R ⟨n, hR⟩) (huBdd R ⟨n, hR⟩) (hgBdd R ⟨n, hR⟩)
  let v : TriadicCube d → Vec d → Vec d :=
    fun R =>
      if hR : IsDescendantOfQ R then
        fun x => (Classical.choose (Classical.choose_spec (hlocal R hR))).toH1.grad x
      else
        0
  refine ⟨v, ?_, ?_⟩
  · intro R hRdesc
    let ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g) :=
      Classical.choose (hlocal R hRdesc)
    let w : AHarmonicFunction a (cubeSet R) :=
      Classical.choose (Classical.choose_spec (hlocal R hRdesc))
    have hv :
        v R = fun x => w.toH1.grad x := by
      change
        (if hR : IsDescendantOfQ R then
          fun x => (Classical.choose (Classical.choose_spec (hlocal R hR))).toH1.grad x
        else 0) = fun x => w.toH1.grad x
      rw [dif_pos hRdesc]
    have hspec :
        (∀ x ∈ cubeSet R,
          u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => w.toH1.grad x)) →
        (cubeBesovNegativeVectorSeminormTwo R s
            (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSAbsorbedLocalError R a g u (fun x => w.toH1.grad x) s η) := by
      simpa [ω, w] using
        Classical.choose_spec (Classical.choose_spec (hlocal R hRdesc))
    exact ⟨ω, w, hv, hspec.1⟩
  · intro hvBdd j R hR
    have hRdesc : IsDescendantOfQ R := ⟨j, hR⟩
    let ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g) :=
      Classical.choose (hlocal R hRdesc)
    let w : AHarmonicFunction a (cubeSet R) :=
      Classical.choose (Classical.choose_spec (hlocal R hRdesc))
    have hv :
        v R = fun x => w.toH1.grad x := by
      change
        (if hR : IsDescendantOfQ R then
          fun x => (Classical.choose (Classical.choose_spec (hlocal R hR))).toH1.grad x
        else 0) = fun x => w.toH1.grad x
      rw [dif_pos hRdesc]
    have hwBdd :
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => w.toH1.grad x)) := by
      simpa [hv] using hvBdd R hRdesc
    have hspec :
        (∀ x ∈ cubeSet R,
          u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => w.toH1.grad x)) →
        (cubeBesovNegativeVectorSeminormTwo R s
            (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSAbsorbedLocalError R a g u (fun x => w.toH1.grad x) s η) := by
      simpa [ω, w] using
        Classical.choose_spec (Classical.choose_spec (hlocal R hRdesc))
    simpa [hv] using hspec.2 hwBdd

/-- PDE-facing coefficient-energy recurrence with the explicit
corrector-energy local-error envelope. -/
theorem exists_centeredNeumannCorrector_aHarmonicRemainder_fluxSeminormStepCorrectorEnergyLocalError_of_h1DirichletRhsWeakSolutionOn_of_coarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) (u : H1Function (cubeSet Q)) {s lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hg : MemVectorL2 (cubeSet Q) g)
    (hC : H1CoerciveEstimate (cubeSet Q))
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a))
    (hchildBdd :
      ∀ R ∈ descendantsAtDepth Q 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (u.grad x)))) :
    ∃ ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g),
      ∃ w : AHarmonicFunction a (cubeSet Q),
        (∀ x ∈ cubeSet Q,
          u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul (a x) (u.grad x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R =>
                (cubeBesovNegativeVectorSeminormTwo R s
                  (fun x => matVecMul (a x) (u.grad x))) ^ 2) +
          weakFluxRHSCorrectorEnergyLocalError Q a u.grad
            (fun x => ω.toH1MeanZero.toH1Function.grad x) s := by
  rcases
      exists_centeredNeumannCorrector_aHarmonicRemainder_fluxSeminormStepCoeffEnergy_of_h1DirichletRhsWeakSolutionOn_of_coarseData
        (Q := Q) (a := a) (g := g) (u := u)
        (s := s) (lam := lam) (Lam := Lam)
        hs hEll hu hg hC hData hsum hchildBdd with
    ⟨ω, w, huw, hstep⟩
  refine ⟨ω, w, huw, ?_⟩
  simpa [weakFluxRHSCorrectorEnergyLocalError, add_assoc] using hstep

/-- PDE-facing absorbed recurrence with the explicit absorbed local-error
envelope. -/
theorem exists_centeredNeumannCorrector_aHarmonicRemainder_fluxSeminormStepAbsorbedLocalError_of_h1DirichletRhsWeakSolutionOn_of_coarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) (u : H1Function (cubeSet Q)) {s η lam Lam : ℝ}
    (hs : 0 < s) (hη : 0 < η)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hg : MemVectorL2 (cubeSet Q) g)
    (hC : H1CoerciveEstimate (cubeSet Q))
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a))
    (hchildBdd :
      ∀ R ∈ descendantsAtDepth Q 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (u.grad x))))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u.grad))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    ∃ ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g),
      ∃ w : AHarmonicFunction a (cubeSet Q),
        (∀ x ∈ cubeSet Q,
          u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo Q s N
            (fun x => w.toH1.grad x)) →
        (cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul (a x) (u.grad x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R =>
                (cubeBesovNegativeVectorSeminormTwo R s
                  (fun x => matVecMul (a x) (u.grad x))) ^ 2) +
          weakFluxRHSAbsorbedLocalError Q a g u.grad (fun x => w.toH1.grad x) s η) := by
  rcases
      exists_centeredNeumannCorrector_aHarmonicRemainder_fluxSeminormStepAbsorbedShortTerm_of_h1DirichletRhsWeakSolutionOn_of_coarseData
        (Q := Q) (a := a) (g := g) (u := u)
        (s := s) (η := η) (lam := lam) (Lam := Lam)
        hs hη hEll hu hg hC hData hsum hchildBdd huBdd hgBdd with
    ⟨ω, w, huw, hstep⟩
  refine ⟨ω, w, huw, ?_⟩
  intro hwBdd
  simpa [weakFluxRHSAbsorbedLocalError, add_assoc] using hstep hwBdd

end

end Homogenization
