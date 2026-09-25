/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.Bridges

/-! # Theory -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public Coarse Caccioppoli with RHS Theory

This file is split mechanically out of `CoarseCaccioppoliRHS.lean`.

## Audit tag

Claim: expose the single public boundary coarse Caccioppoli-with-RHS theorem
package and assemble it from the proved parent-`L²` corrector bound.

Downstream target: note-facing Ch3 theorem consumers.  This is the only public
`CoarseCaccioppoliRHSTheory` surface; new variants must amend the Ch3 surface
contract first.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- Public theorem package for the boundary coarse-grained Caccioppoli estimate
with right-hand side. -/
structure CoarseCaccioppoliRHSTheory (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ}
        {x : Vec d} {g : Vec d → Vec d}
        (u : BoundaryForcedCaccioppoliDatum Q a x g),
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
          x ∈ openCubeSet Q → ForceBesovRegularity Q (2 * t) g →
            boundaryForcedCaccioppoliCoreEnergy u ≤
              boundaryCaccioppoliWithRHSRHS C s t u

/-- Conditional package constructor for the boundary coarse-grained Caccioppoli
estimate with right-hand side.  This is the public assembly point consumed once
the theorem-specific Caccioppoli estimate is available. -/
private theorem coarseCaccioppoliRHSTheory_of_bound
    {d : ℕ} [NeZero d] {C : ℝ} (hC_pos : 0 < C)
    (hbound :
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ}
        {x : Vec d} {g : Vec d → Vec d}
        (u : BoundaryForcedCaccioppoliDatum Q a x g),
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
          x ∈ openCubeSet Q → ForceBesovRegularity Q (2 * t) g →
            boundaryForcedCaccioppoliCoreEnergy u ≤
              boundaryCaccioppoliWithRHSRHS C s t u) :
    CoarseCaccioppoliRHSTheory d := by
  exact ⟨⟨C, hC_pos, hbound⟩⟩

/-- If the zero-trace corrector parent `L²` bound is available, the full public
Caccioppoli-with-RHS theorem follows.

This theorem is the current assembly apex: homogeneous Caccioppoli, the
zero-Dirichlet RHS estimate, the forced split, and the scalar absorptions are
all wired in here. -/
private theorem coarseCaccioppoliRHSTheory_of_parentL2_bound
    {d : ℕ} [NeZero d]
    (hbound :
      ∃ K : ℝ, 0 < K ∧
        ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
          {g : Vec d → Vec d}
          (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g),
          0 < t → t < 1 / 2 → ForceBesovRegularity Q (2 * t) g →
            Ch02.lambdaS Q t a *
                Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                normalizedL2SqOnSet (openCubeSet Q)
                  (boundaryForcedCaccioppoliCorrectorOpenH10
                    (Q := Q) (a := a) ρ).toH1Function.toFun ≤
              K *
                ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
                  Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
                  (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2)) :
    CoarseCaccioppoliRHSTheory d := by
  rcases hbound with ⟨K, _hK_pos, hbound_parentL2⟩
  rcases (coarseCaccioppoliTheory d).exists_constant with
    ⟨C_hom, hC_hom_pos, hboundary, _hinterior⟩
  let Kbig : ℝ := max 1 K
  let C₀base : ℝ :=
    Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
      ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1))
  let C₀ : ℝ := max 1 C₀base
  let Z : ℝ :=
    (2 * (18 : ℝ) ^ d) * ((25 * Real.exp 4) * (((d : ℝ) * C₀) ^ 2))
  let C_inner : ℝ :=
    max 1 (max (4 * C_hom) (max ((4 * Kbig) * C_hom) Z))
  let C_final : ℝ := 3 * C_inner
  have hKbig_one : 1 ≤ Kbig := by
    dsimp [Kbig]
    exact le_max_left 1 K
  have hK_le_Kbig : K ≤ Kbig := by
    dsimp [Kbig]
    exact le_max_right 1 K
  have hK_enlarge : 1 ≤ 4 * Kbig := by nlinarith
  have hC_hom_nonneg : 0 ≤ C_hom := le_of_lt hC_hom_pos
  have hC₀_nonneg : 0 ≤ C₀ := by
    dsimp [C₀]
    exact le_trans zero_le_one (le_max_left 1 C₀base)
  have hC₀_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C₀ := by
    dsimp [C₀, C₀base]
    exact le_max_right 1 C₀base
  have hC_inner_one : 1 ≤ C_inner := by
    dsimp [C_inner]
    exact le_max_left 1 (max (4 * C_hom) (max ((4 * Kbig) * C_hom) Z))
  have h4_hom_inner : 4 * C_hom ≤ C_inner := by
    dsimp [C_inner]
    calc
      4 * C_hom ≤ max (4 * C_hom) (max ((4 * Kbig) * C_hom) Z) :=
        le_max_left _ _
      _ ≤ max 1 (max (4 * C_hom) (max ((4 * Kbig) * C_hom) Z)) :=
        le_max_right _ _
  have hcorrector_inner : (4 * Kbig) * C_hom ≤ C_inner := by
    dsimp [C_inner]
    calc
      (4 * Kbig) * C_hom ≤ max ((4 * Kbig) * C_hom) Z :=
        le_max_left _ _
      _ ≤ max (4 * C_hom) (max ((4 * Kbig) * C_hom) Z) :=
        le_max_right _ _
      _ ≤ max 1 (max (4 * C_hom) (max ((4 * Kbig) * C_hom) Z)) :=
        le_max_right _ _
  have hZ_inner : Z ≤ C_inner := by
    dsimp [C_inner]
    calc
      Z ≤ max ((4 * Kbig) * C_hom) Z := le_max_right _ _
      _ ≤ max (4 * C_hom) (max ((4 * Kbig) * C_hom) Z) :=
        le_max_right _ _
      _ ≤ max 1 (max (4 * C_hom) (max ((4 * Kbig) * C_hom) Z)) :=
        le_max_right _ _
  have hinner_le_sq : C_inner ≤ C_inner ^ 2 := by
    nlinarith [sq_nonneg (C_inner - 1)]
  have hzero_inner :
      (2 * (18 : ℝ) ^ d) *
        ((25 * Real.exp 4) * (((d : ℝ) * C₀) ^ 2)) ≤
        C_inner ^ 2 := by
    dsimp [Z] at hZ_inner
    exact hZ_inner.trans hinner_le_sq
  have h3_inner_final : 3 * C_inner ≤ C_final := by
    rfl
  have hC_final_pos : 0 < C_final := by
    dsimp [C_final]
    nlinarith
  refine
    coarseCaccioppoliRHSTheory_of_bound
      (d := d) (C := C_final) hC_final_pos ?_
  intro Q a s t x g u hs hs_lt ht ht_lt hst hx hg
  let hg_mem : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_forceBesovRegularity hg
  let ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g :=
    zeroTraceDirichletCorrectorData_publicCoeffField Q a hg_mem
  have hhom :
      boundaryCaccioppoliCoreEnergy
          (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem) ≤
        boundaryCaccioppoliRHS C_hom s t
          (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem) :=
    hboundary
      (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem)
      hs ht hst hx
  have hscaledK :
      Ch02.lambdaS Q t a *
          Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
          normalizedL2SqOnSet (openCubeSet Q)
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun ≤
        K *
          ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
            Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
            (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2) :=
    hbound_parentL2 ρ ht ht_lt hg
  have hforce_nonneg :
      0 ≤
        (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2 :=
    boundaryCaccioppoliWithRHS_forceTerm_nonneg
      (Q := Q) (a := a) (t := t) (g := g) ht ht_lt
  have hscaled :
      Ch02.lambdaS Q t a *
          Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
          normalizedL2SqOnSet (openCubeSet Q)
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun ≤
        Kbig *
          ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
            Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
            (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2) := by
    exact hscaledK.trans
      (mul_le_mul_of_nonneg_right hK_le_Kbig hforce_nonneg)
  exact
    boundaryForcedCaccioppoliCoreEnergy_le_RHS_of_correctorParent_scaled_force_bound
      (K := Kbig) (C_hom := C_hom) (C₀ := C₀) (C_inner := C_inner)
      (C_final := C_final)
      hK_enlarge hC_hom_nonneg hC₀_nonneg hC₀_zero
      hC_inner_one h4_hom_inner hcorrector_inner hzero_inner h3_inner_final
      (Q := Q) (a := a) (s := s) (t := t) (x := x) (g := g)
      u ρ hg_mem hs hs_lt ht ht_lt hst hx hg hhom hscaled

/-- Proved public coarse-grained boundary Caccioppoli estimate with right-hand
side. -/
theorem coarseCaccioppoliRHSTheory
    {d : ℕ} [NeZero d] :
    CoarseCaccioppoliRHSTheory d :=
  coarseCaccioppoliRHSTheory_of_parentL2_bound
    zeroTraceCorrectorParentL2_le_forceScale

end

end Ch03
end Book
end Homogenization
