/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.PublicRHSMonotonicity

/-! # Final Bounds -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Final Boundary Bounds for Coarse Caccioppoli with RHS

This file is split mechanically out of `CoarseCaccioppoliRHS.lean`.

## Audit tag

Claim: combine homogeneous Caccioppoli, zero-trace corrector bounds, and scalar
absorptions into the final public boundary with-RHS estimate.

Downstream target: `CoarseCaccioppoliRHS/Bridges.lean`.  This file should stay
as final-bound assembly, with no extra public `*Theory` surface.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- Coarse-form absorption of the zero-trace corrector parent `L²` term.

This is the scalar bridge matching the LaTeX proof after the corrector parent
`L²` estimate has been stated with the coarse lower ellipticity:
`lambdaS * scale^{-2} * ||ρ||² <= K * forceTerm`.  No uniform ellipticity
constant appears in the conclusion. -/
theorem boundaryForcedCaccioppoliCorrector_parentL2_term_le_RHS_of_scaled_force_bound
    {d : ℕ} [NeZero d] {K C_hom C_final : ℝ}
    (hM : 1 ≤ 4 * K)
    (hC_hom_nonneg : 0 ≤ C_hom)
    (hMC : (4 * K) * C_hom ≤ C_final)
    {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hs : 0 < s) (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hst : s + t < 1)
    (hscaled :
      Ch02.lambdaS Q t a *
          Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
          normalizedL2SqOnSet (openCubeSet Q)
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun ≤
        K *
          ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
            Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
            (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2)) :
    4 * caccioppoliPrefactor C_hom Q a s t *
        normalizedL2SqOnSet (openCubeSet Q)
          (boundaryForcedCaccioppoliCorrectorOpenH10
            (Q := Q) (a := a) ρ).toH1Function.toFun ≤
      boundaryCaccioppoliWithRHSRHS C_final s t u := by
  let P : ℝ := caccioppoliWithRHSPrefactor C_hom Q a s t
  let Pfinal : ℝ := caccioppoliWithRHSPrefactor C_final Q a s t
  let L : ℝ := Ch02.lambdaS Q t a
  let S : ℝ := Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ)))
  let R0 : ℝ :=
    normalizedL2SqOnSet (openCubeSet Q)
      (boundaryForcedCaccioppoliCorrectorOpenH10
        (Q := Q) (a := a) ρ).toH1Function.toFun
  let A : ℝ :=
    L * S * boundaryForcedCaccioppoliParentL2Sq u
  let F : ℝ :=
    (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
      Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
      (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact caccioppoliWithRHSPrefactor_nonneg hC_hom_nonneg hs ht hst
  have hF_nonneg : 0 ≤ F := by
    dsimp [F]
    exact boundaryCaccioppoliWithRHS_forceTerm_nonneg
      (Q := Q) (a := a) (t := t) (g := g) ht ht_lt
  have hscaled' : L * S * R0 ≤ K * F := by
    dsimp [L, S, R0, F]
    exact hscaled
  have hterm :
      4 * caccioppoliPrefactor C_hom Q a s t * R0 ≤
        (4 * K * P) * F := by
    have hid :=
      caccioppoliPrefactor_eq_caccioppoliWithRHSPrefactor_mul_lambdaS_scale
        (C := C_hom) (Q := Q) (a := a) hs ht hst
    have hp_scaled : P * (L * S * R0) ≤ P * (K * F) :=
      mul_le_mul_of_nonneg_left hscaled' hP_nonneg
    calc
      4 * caccioppoliPrefactor C_hom Q a s t * R0 =
          4 * (P * (L * S * R0)) := by
            dsimp [P, L, S, R0]
            rw [hid]
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ 4 * (P * (K * F)) :=
            mul_le_mul_of_nonneg_left hp_scaled
              (by norm_num : (0 : ℝ) ≤ 4)
      _ = (4 * K * P) * F := by ring
  have hC_final_nonneg : 0 ≤ C_final := by
    have hM_nonneg : 0 ≤ 4 * K := le_trans (by norm_num) hM
    exact (mul_nonneg hM_nonneg hC_hom_nonneg).trans hMC
  have hPfinal_nonneg : 0 ≤ Pfinal := by
    dsimp [Pfinal]
    exact caccioppoliWithRHSPrefactor_nonneg hC_final_nonneg hs ht hst
  have hA_nonneg : 0 ≤ A := by
    have hL : 0 ≤ L := by
      dsimp [L]
      unfold Ch02.lambdaS
      exact (Ch02.lambdaSq_finite_pos Q a ht
        (by norm_num : (1 : ℝ) ≤ 1)).le
    have hS : 0 ≤ S := by
      dsimp [S]
      exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    have hparent :
        0 ≤ boundaryForcedCaccioppoliParentL2Sq u :=
      normalizedL2SqOnSet_nonneg (openCubeSet Q) u.toH1.toFun
        (measurableSet_openCubeSet Q)
    dsimp [A]
    exact mul_nonneg (mul_nonneg hL hS) hparent
  have hpref :
      (4 * K) * P ≤ Pfinal := by
    dsimp [P, Pfinal]
    exact caccioppoliWithRHSPrefactor_mul_const_le_of_mul_constant_le
      (M := 4 * K) (C₁ := C_hom) (C₂ := C_final)
      hM hC_hom_nonneg hMC hs ht hst
  have hforce_to_rhs :
      (4 * K * P) * F ≤ boundaryCaccioppoliWithRHSRHS C_final s t u := by
    calc
      (4 * K * P) * F =
          ((4 * K) * P) * F := by ring
      _ ≤ Pfinal * F := mul_le_mul_of_nonneg_right hpref hF_nonneg
      _ ≤ Pfinal * (A + F) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA_nonneg)
            hPfinal_nonneg
      _ = boundaryCaccioppoliWithRHSRHS C_final s t u := by
          rfl
  exact hterm.trans hforce_to_rhs

/-- The first forced RHS summand absorbs a constant multiple of the homogeneous
parent contribution after enlarging the public dimension constant. -/
theorem caccioppoliPrefactor_const_mul_forcedParentL2_le_boundaryCaccioppoliWithRHSRHS
    {d : ℕ} [NeZero d] {M C₁ C₂ : ℝ}
    {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (hM : 1 ≤ M) (hC₁ : 0 ≤ C₁) (hMC₁C₂ : M * C₁ ≤ C₂)
    (hs : 0 < s) (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hst : s + t < 1) :
    M * caccioppoliPrefactor C₁ Q a s t *
        boundaryForcedCaccioppoliParentL2Sq u ≤
      boundaryCaccioppoliWithRHSRHS C₂ s t u := by
  have hC₂_nonneg : 0 ≤ C₂ := by
    have hM_nonneg : 0 ≤ M := le_trans (by norm_num) hM
    exact (mul_nonneg hM_nonneg hC₁).trans hMC₁C₂
  have hpref :
      M * caccioppoliPrefactor C₁ Q a s t ≤
        caccioppoliPrefactor C₂ Q a s t :=
    caccioppoliPrefactor_mul_const_le_of_mul_constant_le
      hM hC₁ hMC₁C₂ hs ht hst
  have hparent :
      0 ≤ boundaryForcedCaccioppoliParentL2Sq u :=
    normalizedL2SqOnSet_nonneg (openCubeSet Q) u.toH1.toFun
      (measurableSet_openCubeSet Q)
  calc
    M * caccioppoliPrefactor C₁ Q a s t *
        boundaryForcedCaccioppoliParentL2Sq u
        ≤ caccioppoliPrefactor C₂ Q a s t *
            boundaryForcedCaccioppoliParentL2Sq u :=
          mul_le_mul_of_nonneg_right hpref hparent
    _ ≤ boundaryCaccioppoliWithRHSRHS C₂ s t u :=
      caccioppoliPrefactor_mul_forcedParentL2_le_boundaryCaccioppoliWithRHSRHS
        u hC₂_nonneg hs ht ht_lt hst

/-- Exact split after subtracting the zero-trace corrector and applying the
homogeneous Caccioppoli estimate to the harmonic remainder.

This is the PDE assembly core.  The remaining work for the final theorem is
pure scalar absorption of the two corrector terms into the displayed forced
right-hand side. -/
theorem boundaryForcedCaccioppoliCoreEnergy_le_split_homogeneous_corrector
    {d : ℕ} [NeZero d] {C : ℝ} {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hg_mem : MemVectorL2 (cubeSet Q) g)
    (hC_nonneg : 0 ≤ C)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hhom :
      boundaryCaccioppoliCoreEnergy
          (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem) ≤
        boundaryCaccioppoliRHS C s t
          (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem)) :
    boundaryForcedCaccioppoliCoreEnergy u ≤
      4 * caccioppoliPrefactor C Q a s t *
          boundaryForcedCaccioppoliParentL2Sq u +
        4 * caccioppoliPrefactor C Q a s t *
          normalizedL2SqOnSet (openCubeSet Q)
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun +
        2 * localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q)
          (boundaryForcedCaccioppoliCorrectorOpenH10
            (Q := Q) (a := a) ρ).toH1Function := by
  let wDatum : BoundaryCaccioppoliDatum Q a x :=
    boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem
  let ρOpen : H10Function (Ch02.cubeDomain Q : Set (Vec d)) :=
    boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) ρ
  let P : ℝ := caccioppoliPrefactor C Q a s t
  let U0 : ℝ := boundaryForcedCaccioppoliParentL2Sq u
  let R0 : ℝ := normalizedL2SqOnSet (openCubeSet Q) ρOpen.toH1Function.toFun
  let Eρ : ℝ :=
    localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q)
      ρOpen.toH1Function
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact caccioppoliPrefactor_nonneg hC_nonneg hs ht hst
  have hcore_split :
      boundaryForcedCaccioppoliCoreEnergy u ≤
        2 * boundaryCaccioppoliCoreEnergy wDatum + 2 * Eρ := by
    dsimp [wDatum, Eρ, ρOpen]
    exact
      boundaryForcedCaccioppoliCoreEnergy_le_two_mul_remainder_add_corrector
        (Q := Q) (a := a) (x := x) (g := g) u ρ hg_mem
  have hparent_split :
      boundaryCaccioppoliParentL2Sq wDatum ≤ 2 * U0 + 2 * R0 := by
    dsimp [wDatum, U0, R0, ρOpen]
    exact
      boundaryForcedCaccioppoliRemainder_parentL2_le_two_mul_forced_add_corrector
        (Q := Q) (a := a) (x := x) (g := g) u ρ hg_mem
  have hhom_split :
      boundaryCaccioppoliCoreEnergy wDatum ≤ P * (2 * U0 + 2 * R0) := by
    calc
      boundaryCaccioppoliCoreEnergy wDatum
          ≤ boundaryCaccioppoliRHS C s t wDatum := by
            simpa [wDatum] using hhom
      _ ≤ P * (2 * U0 + 2 * R0) := by
            unfold boundaryCaccioppoliRHS
            exact mul_le_mul_of_nonneg_left hparent_split hP_nonneg
  calc
    boundaryForcedCaccioppoliCoreEnergy u
        ≤ 2 * boundaryCaccioppoliCoreEnergy wDatum + 2 * Eρ := hcore_split
    _ ≤ 2 * (P * (2 * U0 + 2 * R0)) + 2 * Eρ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hhom_split (by norm_num : (0 : ℝ) ≤ 2))
          (le_refl (2 * Eρ))
    _ =
      4 * P * U0 + 4 * P * R0 + 2 * Eρ := by ring
    _ =
      4 * caccioppoliPrefactor C Q a s t *
          boundaryForcedCaccioppoliParentL2Sq u +
        4 * caccioppoliPrefactor C Q a s t *
          normalizedL2SqOnSet (openCubeSet Q)
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun +
        2 * localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q)
          (boundaryForcedCaccioppoliCorrectorOpenH10
            (Q := Q) (a := a) ρ).toH1Function := by
        rfl

/-- Split form with the corrector core energy already bounded by the public
zero-Dirichlet RHS estimate.  The only analytic term still not absorbed is the
corrector parent `L²` contribution. -/
theorem boundaryForcedCaccioppoliCoreEnergy_le_split_homogeneous_zeroDirichlet
    {d : ℕ} [NeZero d] {C C₀ : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC₀_nonneg : 0 ≤ C₀)
    (hC₀_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C₀)
    {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hg_mem : MemVectorL2 (cubeSet Q) g)
    (hs : 0 < s) (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hst : s + t < 1) (hx : x ∈ openCubeSet Q)
    (hg : ForceBesovRegularity Q (2 * t) g)
    (hhom :
      boundaryCaccioppoliCoreEnergy
          (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem) ≤
        boundaryCaccioppoliRHS C s t
          (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem)) :
    boundaryForcedCaccioppoliCoreEnergy u ≤
      4 * caccioppoliPrefactor C Q a s t *
          boundaryForcedCaccioppoliParentL2Sq u +
        4 * caccioppoliPrefactor C Q a s t *
          normalizedL2SqOnSet (openCubeSet Q)
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun +
        2 * ((18 : ℝ) ^ d *
          (zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C₀) Q a t g) ^ 2) := by
  let ρOpen : H10Function (Ch02.cubeDomain Q : Set (Vec d)) :=
    boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) ρ
  let Eρ : ℝ :=
    localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q)
      ρOpen.toH1Function
  have hsplit :=
    boundaryForcedCaccioppoliCoreEnergy_le_split_homogeneous_corrector
      (C := C) (Q := Q) (a := a) (s := s) (t := t) (x := x) (g := g)
      u ρ hg_mem hC_nonneg hs ht hst hhom
  have hcoreρ :
      Eρ ≤ (18 : ℝ) ^ d *
          (zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C₀) Q a t g) ^ 2 := by
    dsimp [Eρ, ρOpen]
    exact
      boundaryForcedCaccioppoliCorrector_coreEnergy_le_eighteen_pow_mul_zeroDirichletEnergyWithRHSRHS_sq
        (C := C₀) hC₀_nonneg hC₀_zero
        (Q := Q) (a := a) (t := t) (x := x) (g := g)
        ρ ht ht_lt hx hg
  have hscaled :
      2 * Eρ ≤
        2 * ((18 : ℝ) ^ d *
          (zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C₀) Q a t g) ^ 2) :=
    mul_le_mul_of_nonneg_left hcoreρ (by norm_num : (0 : ℝ) ≤ 2)
  calc
    boundaryForcedCaccioppoliCoreEnergy u
        ≤
      4 * caccioppoliPrefactor C Q a s t *
          boundaryForcedCaccioppoliParentL2Sq u +
        4 * caccioppoliPrefactor C Q a s t *
          normalizedL2SqOnSet (openCubeSet Q)
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun +
        2 * Eρ := by
        simpa [Eρ, ρOpen] using hsplit
    _ ≤
      4 * caccioppoliPrefactor C Q a s t *
          boundaryForcedCaccioppoliParentL2Sq u +
        4 * caccioppoliPrefactor C Q a s t *
          normalizedL2SqOnSet (openCubeSet Q)
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun +
        2 * ((18 : ℝ) ^ d *
          (zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C₀) Q a t g) ^ 2) := by
        exact add_le_add_right hscaled _

/-- Conditional final assembly for the forced boundary Caccioppoli estimate.

All PDE and scalar pieces have been discharged here except the genuinely
analytic input controlling the zero-trace corrector's parent `L²` term.  Once
that bridge is supplied in the `hcorrectorParent` hypothesis, the displayed
public RHS follows after one last constant enlargement. -/
theorem boundaryForcedCaccioppoliCoreEnergy_le_RHS_of_correctorParent_absorption
    {d : ℕ} [NeZero d] {C_hom C₀ C_inner C_final : ℝ}
    (hC_hom_nonneg : 0 ≤ C_hom)
    (hC₀_nonneg : 0 ≤ C₀)
    (hC₀_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C₀)
    (hC_inner_one : 1 ≤ C_inner)
    (h4_hom_inner : 4 * C_hom ≤ C_inner)
    (hzero_inner :
      (2 * (18 : ℝ) ^ d) *
        ((25 * Real.exp 4) * (((d : ℝ) * C₀) ^ 2)) ≤ C_inner ^ 2)
    (h3_inner_final : 3 * C_inner ≤ C_final)
    {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hg_mem : MemVectorL2 (cubeSet Q) g)
    (hs : 0 < s) (hs_lt : s < 1) (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hst : s + t < 1) (hx : x ∈ openCubeSet Q)
    (hg : ForceBesovRegularity Q (2 * t) g)
    (hhom :
      boundaryCaccioppoliCoreEnergy
          (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem) ≤
        boundaryCaccioppoliRHS C_hom s t
          (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem))
    (hcorrectorParent :
      4 * caccioppoliPrefactor C_hom Q a s t *
          normalizedL2SqOnSet (openCubeSet Q)
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun ≤
        boundaryCaccioppoliWithRHSRHS C_inner s t u) :
    boundaryForcedCaccioppoliCoreEnergy u ≤
      boundaryCaccioppoliWithRHSRHS C_final s t u := by
  let A : ℝ :=
    4 * caccioppoliPrefactor C_hom Q a s t *
      boundaryForcedCaccioppoliParentL2Sq u
  let B : ℝ :=
    4 * caccioppoliPrefactor C_hom Q a s t *
      normalizedL2SqOnSet (openCubeSet Q)
        (boundaryForcedCaccioppoliCorrectorOpenH10
          (Q := Q) (a := a) ρ).toH1Function.toFun
  let D : ℝ :=
    2 * ((18 : ℝ) ^ d *
      (zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C₀) Q a t g) ^ 2)
  let R : ℝ := boundaryCaccioppoliWithRHSRHS C_inner s t u
  have hsplit :
      boundaryForcedCaccioppoliCoreEnergy u ≤ A + B + D := by
    dsimp [A, B, D]
    exact
      boundaryForcedCaccioppoliCoreEnergy_le_split_homogeneous_zeroDirichlet
        (C := C_hom) (C₀ := C₀)
        hC_hom_nonneg hC₀_nonneg hC₀_zero
        (Q := Q) (a := a) (s := s) (t := t) (x := x) (g := g)
        u ρ hg_mem hs ht ht_lt hst hx hg hhom
  have hA : A ≤ R := by
    dsimp [A, R]
    simpa using
      caccioppoliPrefactor_const_mul_forcedParentL2_le_boundaryCaccioppoliWithRHSRHS
        (M := (4 : ℝ)) (C₁ := C_hom) (C₂ := C_inner)
        (Q := Q) (a := a) (s := s) (t := t) (x := x) (g := g)
        u (by norm_num : (1 : ℝ) ≤ 4) hC_hom_nonneg h4_hom_inner
        hs ht ht_lt hst
  have hB : B ≤ R := by
    dsimp [B, R]
    exact hcorrectorParent
  have hD : D ≤ R := by
    dsimp [D, R]
    exact
      boundaryCaccioppoliWithRHS_zeroDirichletSqTerm_le_RHS
        (C := C_inner) (C₀ := (d : ℝ) * C₀)
        (Q := Q) (a := a) (s := s) (t := t) (x := x) (g := g)
        u hzero_inner hC_inner_one hs hs_lt ht ht_lt hst
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact boundaryCaccioppoliWithRHSRHS_nonneg
      u (le_trans zero_le_one hC_inner_one) hs ht ht_lt hst
  have hsum : A + B + D ≤ 3 * R := by
    calc
      A + B + D ≤ R + R + R := add_le_add (add_le_add hA hB) hD
      _ = 3 * R := by ring
  have hfinal :
      3 * R ≤ boundaryCaccioppoliWithRHSRHS C_final s t u := by
    dsimp [R]
    exact boundaryCaccioppoliWithRHSRHS_mul_const_le_of_mul_constant_le
      (M := (3 : ℝ)) (C₁ := C_inner) (C₂ := C_final)
      (Q := Q) (a := a) (s := s) (t := t) (x := x) (g := g)
      u (by norm_num : (1 : ℝ) ≤ 3) (le_trans zero_le_one hC_inner_one)
      h3_inner_final hs ht ht_lt hst
  exact hsplit.trans (hsum.trans hfinal)

/-- Conditional final assembly using the coarse-scaled parent `L²` estimate for
the zero-trace corrector.

Compared with
`boundaryForcedCaccioppoliCoreEnergy_le_RHS_of_correctorParent_absorption`, this
is the theorem-shape reduction that remains faithful to the displayed
Caccioppoli-with-RHS estimate: the remaining analytic input is precisely a
bound for `lambdaS * scale^{-2} * ||ρ||²_parent` by a dimension-only multiple
of the forcing summand. -/
theorem boundaryForcedCaccioppoliCoreEnergy_le_RHS_of_correctorParent_scaled_force_bound
    {d : ℕ} [NeZero d] {K C_hom C₀ C_inner C_final : ℝ}
    (hK_enlarge : 1 ≤ 4 * K)
    (hC_hom_nonneg : 0 ≤ C_hom)
    (hC₀_nonneg : 0 ≤ C₀)
    (hC₀_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C₀)
    (hC_inner_one : 1 ≤ C_inner)
    (h4_hom_inner : 4 * C_hom ≤ C_inner)
    (hcorrector_inner : (4 * K) * C_hom ≤ C_inner)
    (hzero_inner :
      (2 * (18 : ℝ) ^ d) *
        ((25 * Real.exp 4) * (((d : ℝ) * C₀) ^ 2)) ≤ C_inner ^ 2)
    (h3_inner_final : 3 * C_inner ≤ C_final)
    {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hg_mem : MemVectorL2 (cubeSet Q) g)
    (hs : 0 < s) (hs_lt : s < 1) (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hst : s + t < 1) (hx : x ∈ openCubeSet Q)
    (hg : ForceBesovRegularity Q (2 * t) g)
    (hhom :
      boundaryCaccioppoliCoreEnergy
          (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem) ≤
        boundaryCaccioppoliRHS C_hom s t
          (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem))
    (hcorrectorScaled :
      Ch02.lambdaS Q t a *
          Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
          normalizedL2SqOnSet (openCubeSet Q)
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun ≤
        K *
          ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
            Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
            (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2)) :
    boundaryForcedCaccioppoliCoreEnergy u ≤
      boundaryCaccioppoliWithRHSRHS C_final s t u := by
  have hcorrectorParent :
      4 * caccioppoliPrefactor C_hom Q a s t *
          normalizedL2SqOnSet (openCubeSet Q)
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun ≤
        boundaryCaccioppoliWithRHSRHS C_inner s t u := by
    exact
      boundaryForcedCaccioppoliCorrector_parentL2_term_le_RHS_of_scaled_force_bound
        (K := K) (C_hom := C_hom) (C_final := C_inner)
        hK_enlarge hC_hom_nonneg hcorrector_inner
        (Q := Q) (a := a) (s := s) (t := t) (x := x) (g := g)
        u ρ hs ht ht_lt hst hcorrectorScaled
  exact
    boundaryForcedCaccioppoliCoreEnergy_le_RHS_of_correctorParent_absorption
      (C_hom := C_hom) (C₀ := C₀) (C_inner := C_inner)
      (C_final := C_final)
      hC_hom_nonneg hC₀_nonneg hC₀_zero hC_inner_one h4_hom_inner
      hzero_inner h3_inner_final
      (Q := Q) (a := a) (s := s) (t := t) (x := x) (g := g)
      u ρ hg_mem hs hs_lt ht ht_lt hst hx hg hhom hcorrectorParent

end

end Ch03
end Book
end Homogenization
