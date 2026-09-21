/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalEstimate.Split

/-! # Cutoff -/

namespace Homogenization

/-!
# Local energy estimate: cutoff-localized exact RHS bridge
-/

noncomputable section

open scoped BigOperators ENNReal

/-- Exact local Caccioppoli estimate on a descendant cube using a cutoff
constructed on the parent cube.  This is the small-cube local form of the
Chapter 3 proof: the cube being averaged is `R`, while the cutoff transition
still comes from the annulus between the two radii of `Q`. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_parentQuantitativeCutoff_on_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (a : CoeffField d) (s : ℝ) {ρ₁ ρ₂ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u (scalarCutoffGradientField η)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s (scalarCutoffGradientField η) Acirc1 AcircS
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u (scalarCutoffGradientField η) energy
        Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  have hξLp :
      MeasureTheory.MemLp (scalarCutoffGradientField η) ∞ (normalizedCubeMeasure R) :=
    quantitativeCubeCutoff_memLp_top_gradientField_on_descendant hR η
  have hvector :
      CoarseCaccioppoliVectorCutoffControls R s u G (scalarCutoffGradientField η) energy
        Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)) C :=
    CoarseCaccioppoliVectorCutoffControls.of_quantitativeCubeCutoff_on_descendant
      (Q := Q) (R := R) (j := j) hR (s := s) (u := u) (G := G)
      (energy := energy) (η := η) hB hAcircS hBgConst hBgCent hC
      hproj hGcirc1 hGcircS
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_vectorControls
      (Q := R) (a := a) (s := s) (flux := flux) (u := u) (G := G)
      (ξ := scalarCutoffGradientField η) (energy := energy)
      (Acirc1 := Acirc1) (AcircS := AcircS)
      (B := quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
      (C := C) hs0 hs1 hfluxMem hu hG hξLp hfluxEnergy hvector

/-- Exact local Caccioppoli estimate on a cube using the arbitrary-center local
canonical cutoff.  This is the single-cube bridge needed by the boundary
radius profile in the notes, where the cutoff lives on `center + rho cu_{m-1}`
rather than on a cube centered at the parent cube center. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_localCanonicalCutoff_on_cube
    {d : ℕ} (Q R : TriadicCube d) (center : Vec d)
    (a : CoeffField d) (s : ℝ) {rhoInner rhoOuter : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS C : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤
        quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          Acirc1 AcircS (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R
        (fun x =>
          vecDot (flux x)
            (u x •
              scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
        energy Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  have hξLp :
      MeasureTheory.MemLp
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
        ∞ (normalizedCubeMeasure R) :=
    coarseCaccioppoliLocalCanonicalFun_memLp_top_gradientField_on_cube
      Q R center hinner hinnerOuter
  have hvector :
      CoarseCaccioppoliVectorCutoffControls R s u G
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
        energy Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
        C :=
    CoarseCaccioppoliVectorCutoffControls.of_localCanonicalCutoff_on_cube
      Q R center s hinner hinnerOuter u G energy hB hAcircS hBgConst
      hBgCent hC hproj hGcirc1 hGcircS
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_vectorControls
      (Q := R) (a := a) (s := s) (flux := flux) (u := u) (G := G)
      (ξ := scalarCutoffGradientField
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS)
      (B := quantitativeCubeCutoffHessianConst d /
        (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
      (C := C) hs0 hs1 hfluxMem hu hG hξLp hfluxEnergy hvector

/-- Local exact-RHS estimate for the arbitrary-center canonical cutoff, with
the RHS energy localized to a larger arbitrary-center local cube, on the branch
where the averaged cube is contained in that larger local cube. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_localCanonicalCutoff_on_cube_of_cubeSet_subset
    {d : ℕ} {Q R : TriadicCube d} (center : Vec d)
    (a : CoeffField d) (s : ℝ) {rhoInner rhoOuter rho : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS C : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hsub : cubeSet R ⊆ coarseCaccioppoliLocalClosedCube Q center rho)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤
        quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          Acirc1 AcircS (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R
        (fun x =>
          vecDot (flux x)
            (u x •
              scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
        ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
        Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  have havg :
      cubeAverage R ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy) =
        cubeAverage R energy :=
    cubeAverage_indicator_coarseCaccioppoliLocalClosedCube_eq_cubeAverage_of_cubeSet_subset
      (Q := Q) (R := R) center rho energy hsub
  have hfluxEnergy_indicator :
      CoarseCaccioppoliFluxEnergyControls R a s flux
        ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy) :=
    hfluxEnergy.indicator_coarseCaccioppoliLocalClosedCube_of_cubeSet_subset
      center rho hsub
  have hBgCent_indicator :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          Acirc1 AcircS
          (Real.sqrt
            (cubeAverage R
              ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C) := by
    simpa [havg] using hBgCent
  have hGcirc1_indicator : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 *
          Real.sqrt
            (cubeAverage R
              ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)) := by
    intro i N
    simpa [havg] using hGcirc1 i N
  have hGcircS_indicator : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤
          AcircS *
            Real.sqrt
              (cubeAverage R
                ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)) := by
    intro i N
    simpa [havg] using hGcircS i N
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_localCanonicalCutoff_on_cube
      (Q := Q) (R := R) (center := center) (a := a) (s := s)
      (rhoInner := rhoInner) (rhoOuter := rhoOuter)
      (flux := flux) (u := u) (G := G)
      (energy := (coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
      (Acirc1 := Acirc1) (AcircS := AcircS) (C := C)
      hinner hinnerOuter hs0 hs1 hfluxMem hu hG hfluxEnergy_indicator hB hAcircS
      hBgConst hBgCent_indicator hC hproj hGcirc1_indicator hGcircS_indicator

/-- Local exact-RHS estimate for descendant cubes outside the support of the
arbitrary-center canonical cutoff.  The pairing vanishes pointwise on the
averaged cube. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_localCanonicalCutoff_on_cube_of_forall_notMem_localClosedCube
    {d : ℕ} {Q R : TriadicCube d} (center : Vec d)
    (a : CoeffField d) {s : ℝ} {rhoInner rhoOuter rho : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hout : ∀ x ∈ cubeSet R, x ∉ coarseCaccioppoliLocalClosedCube Q center rhoOuter)
    (hs : 0 < s) (hAcirc1 : 0 ≤ Acirc1) (hAcircS : 0 ≤ AcircS)
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    |cubeAverage R
        (fun x =>
          vecDot (flux x)
            (u x •
              scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
        ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
        Acirc1 AcircS B C := by
  have hpair_zero :
      cubeAverage R
          (fun x =>
            vecDot (flux x)
              (u x •
                scalarCutoffGradientField
                  (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x)) =
        0 := by
    rw [← cubeAverage_const (Q := R) (c := 0)]
    apply cubeAverage_congr_on_cubeSet
    intro x hxR
    have hξ :
        scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x = 0 :=
      scalarCutoffGradientField_coarseCaccioppoliLocalCanonicalFun_eq_zero_of_notMem_localClosedCube
        hinner hinnerOuter (hout x hxR)
    simp [hξ, vecDot_zero_right]
  rw [hpair_zero, abs_zero]
  exact
    coarseCaccioppoliFluxEnergyExactRhs_nonneg
      R a u
      (scalarCutoffGradientField
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
      ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
      hs hAcirc1 hAcircS hB hC

/-- Buffered local exact-RHS estimate for the arbitrary-center canonical
cutoff.  A descendant either misses the local cutoff support or, if it touches
the support, the buffer hypothesis forces it into the larger local energy cube. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_localCanonicalCutoff_on_descendant_of_support_buffer
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (_hR : R ∈ descendantsAtDepth Q j)
    (center : Vec d) (a : CoeffField d) (s : ℝ) {rhoInner rhoOuter rho : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS C : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hgap : cubeScaleFactor R ≤ (rho - rhoOuter) * (cubeRadius Q / 3))
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤
        quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
    (hAcirc1 : 0 ≤ Acirc1)
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          Acirc1 AcircS
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R
        (fun x =>
          vecDot (flux x)
            (u x •
              scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
        ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
        Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  by_cases hinter :
      ∃ y ∈ cubeSet R, y ∈ coarseCaccioppoliLocalClosedCube Q center rhoOuter
  · have hsub : cubeSet R ⊆ coarseCaccioppoliLocalClosedCube Q center rho :=
      cubeSet_subset_coarseCaccioppoliLocalClosedCube_of_intersects_of_scaleFactor_le_gap
        (Q := Q) (R := R) (center := center)
        (rhoInner := rhoOuter) (rhoOuter := rho) hgap hinter
    exact
      abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_localCanonicalCutoff_on_cube_of_cubeSet_subset
        (Q := Q) (R := R) (center := center) (a := a) (s := s)
        (rhoInner := rhoInner) (rhoOuter := rhoOuter) (rho := rho)
        (flux := flux) (u := u) (G := G) (energy := energy)
        (Acirc1 := Acirc1) (AcircS := AcircS) (C := C)
        hinner hinnerOuter hsub hs0 hs1 hfluxMem hu hG hfluxEnergy hB hAcircS
        hBgConst hBgCent hC hproj hGcirc1 hGcircS
  · have hout :
        ∀ x ∈ cubeSet R, x ∉ coarseCaccioppoliLocalClosedCube Q center rhoOuter := by
      intro x hxR hxrhoOuter
      exact hinter ⟨x, hxR, hxrhoOuter⟩
    exact
      abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_localCanonicalCutoff_on_cube_of_forall_notMem_localClosedCube
        (Q := Q) (R := R) (center := center) (a := a) (s := s)
        (rhoInner := rhoInner) (rhoOuter := rhoOuter) (rho := rho)
        (flux := flux) (u := u) (energy := energy)
        (Acirc1 := Acirc1) (AcircS := AcircS)
        (B := quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
        (C := (Fintype.card (Fin d) : ℝ) * C)
        hinner hinnerOuter hout hs0 hAcirc1 hAcircS hB
        (mul_nonneg (by positivity) hC)

/-- Local exact-RHS estimate with an outer localized energy density, for
descendant cubes contained in the localization region.

This is the support-localized version of
`abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_parentQuantitativeCutoff_on_descendant`
on the easy branch: when `cubeSet R` is contained in the outer scaled cube,
the localized indicator agrees with the original energy on every descendant
of `R`, so the flux-energy controls and the scalar bounds transfer by
cube-average congruence. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_parentQuantitativeCutoff_on_descendant_of_cubeSet_subset
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (a : CoeffField d) (s : ℝ) {ρ₁ ρ₂ ρ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C : ℝ}
    (hsub : cubeSet R ⊆ scaledClosedCubeSet Q ρ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u (scalarCutoffGradientField η)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s (scalarCutoffGradientField η) Acirc1 AcircS
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u (scalarCutoffGradientField η)
        ((scaledClosedCubeSet Q ρ).indicator energy)
        Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  have havg :
      cubeAverage R ((scaledClosedCubeSet Q ρ).indicator energy) =
        cubeAverage R energy :=
    cubeAverage_indicator_scaledClosedCubeSet_eq_cubeAverage_of_cubeSet_subset
      (Q := Q) (R := R) ρ energy hsub
  have hfluxEnergy_indicator :
      CoarseCaccioppoliFluxEnergyControls R a s flux
        ((scaledClosedCubeSet Q ρ).indicator energy) :=
    hfluxEnergy.indicator_scaledClosedCubeSet_of_cubeSet_subset ρ hsub
  have hBgCent_indicator :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s (scalarCutoffGradientField η) Acirc1 AcircS
          (Real.sqrt (cubeAverage R ((scaledClosedCubeSet Q ρ).indicator energy)))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C) := by
    simpa [havg] using hBgCent
  have hGcirc1_indicator : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 *
          Real.sqrt (cubeAverage R ((scaledClosedCubeSet Q ρ).indicator energy)) := by
    intro i N
    simpa [havg] using hGcirc1 i N
  have hGcircS_indicator : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤
          AcircS *
            Real.sqrt (cubeAverage R ((scaledClosedCubeSet Q ρ).indicator energy)) := by
    intro i N
    simpa [havg] using hGcircS i N
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_parentQuantitativeCutoff_on_descendant
      (Q := Q) (R := R) (j := j) hR (a := a) (s := s) (flux := flux) (u := u)
      (G := G) (energy := (scaledClosedCubeSet Q ρ).indicator energy) (η := η)
      (Acirc1 := Acirc1) (AcircS := AcircS) (C := C)
      hs0 hs1 hfluxMem hu hG hfluxEnergy_indicator hB hAcircS hBgConst
      hBgCent_indicator hC hproj hGcirc1_indicator hGcircS_indicator

/-- Local exact-RHS estimate with an outer localized energy density, for
descendant cubes outside the support region of the parent cutoff.  In this
branch the pairing vanishes pointwise on the averaged cube. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_parentQuantitativeCutoff_on_descendant_of_forall_notMem_scaledClosedCubeSet
    {d : ℕ} {Q R : TriadicCube d}
    (a : CoeffField d) {s : ℝ} {ρ₁ ρ₂ ρ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS B C : ℝ}
    (hout : ∀ x ∈ cubeSet R, x ∉ scaledClosedCubeSet Q ρ₂)
    (hs : 0 < s) (hAcirc1 : 0 ≤ Acirc1) (hAcircS : 0 ≤ AcircS)
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    |cubeAverage R
        (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u
        (scalarCutoffGradientField η)
        ((scaledClosedCubeSet Q ρ).indicator energy)
        Acirc1 AcircS B C := by
  have hpair_zero :
      cubeAverage R
          (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x)) =
        0 := by
    rw [← cubeAverage_const (Q := R) (c := 0)]
    apply cubeAverage_congr_on_cubeSet
    intro x hxR
    have hξ :
        scalarCutoffGradientField (η : Vec d → ℝ) x = 0 :=
      η.scalarCutoffGradientField_eq_zero_of_notMem_scaledClosedCubeSet
        (hout x hxR)
    simp [hξ, vecDot_zero_right]
  rw [hpair_zero, abs_zero]
  exact
    coarseCaccioppoliFluxEnergyExactRhs_nonneg
      R a u (scalarCutoffGradientField η)
      ((scaledClosedCubeSet Q ρ).indicator energy)
      hs hAcirc1 hAcircS hB hC

/-- Buffered local exact-RHS estimate.  The cutoff is supported in
`scaledClosedCubeSet Q ρ₂`, while the energy is localized on a larger radius
`ρ`.  If the descendant side length fits in the buffer `ρ - ρ₂`, then every
descendant either misses the cutoff support, or is entirely contained in the
larger localization cube. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_parentQuantitativeCutoff_on_descendant_of_support_buffer
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (a : CoeffField d) (s : ℝ) {ρ₁ ρ₂ ρ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C : ℝ}
    (hgap : cubeScaleFactor R ≤ (ρ - ρ₂) * cubeRadius Q)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcirc1 : 0 ≤ Acirc1)
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u (scalarCutoffGradientField η)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s (scalarCutoffGradientField η) Acirc1 AcircS
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u (scalarCutoffGradientField η)
        ((scaledClosedCubeSet Q ρ).indicator energy)
        Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  by_cases hinter : ∃ y ∈ cubeSet R, y ∈ scaledClosedCubeSet Q ρ₂
  · have hsub : cubeSet R ⊆ scaledClosedCubeSet Q ρ :=
      cubeSet_subset_scaledClosedCubeSet_of_intersects_scaledClosedCubeSet_of_scaleFactor_le_gap
        (Q := Q) (R := R) (ρinner := ρ₂) (ρouter := ρ) hgap hinter
    exact
      abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_parentQuantitativeCutoff_on_descendant_of_cubeSet_subset
        (Q := Q) (R := R) (j := j) hR (a := a) (s := s) (ρ := ρ)
        (flux := flux) (u := u) (G := G) (energy := energy) (η := η)
        (Acirc1 := Acirc1) (AcircS := AcircS) (C := C)
        hsub hs0 hs1 hfluxMem hu hG hfluxEnergy hB hAcircS hBgConst hBgCent
        hC hproj hGcirc1 hGcircS
  · have hout : ∀ x ∈ cubeSet R, x ∉ scaledClosedCubeSet Q ρ₂ := by
      intro x hxR hxρ₂
      exact hinter ⟨x, hxR, hxρ₂⟩
    exact
      abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_parentQuantitativeCutoff_on_descendant_of_forall_notMem_scaledClosedCubeSet
        (Q := Q) (R := R) (a := a) (s := s) (ρ := ρ)
        (flux := flux) (u := u) (energy := energy) (η := η)
        (Acirc1 := Acirc1) (AcircS := AcircS)
        (B := quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
        (C := (Fintype.card (Fin d) : ℝ) * C)
        hout hs0 hAcirc1 hAcircS hB
        (mul_nonneg (by positivity) hC)

end

end Homogenization
