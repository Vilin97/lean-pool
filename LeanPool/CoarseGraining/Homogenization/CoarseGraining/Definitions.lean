/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.BlockMatrix
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockFormalism
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic.Linarith

/-! # Definitions -/

@[expose] public section

namespace Homogenization

noncomputable def volumeAverage {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  (MeasureTheory.volume U).toReal⁻¹ * ∫ x in U, f x ∂MeasureTheory.volume

noncomputable def volumeAverageVec {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Vec d :=
  fun i => volumeAverage U (fun x => f x i)

noncomputable def volumeAverageMat {d : ℕ} (U : Set (Vec d)) (f : Vec d → Mat d) : Mat d :=
  fun i j => volumeAverage U (fun x => f x i j)

theorem volumeAverage_eq_zero_of_integral_eq_zero {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ}
    (h : ∫ x in U, f x ∂MeasureTheory.volume = 0) :
    volumeAverage U f = 0 := by
  unfold volumeAverage
  rw [h]
  simp

noncomputable def muValueSet {d : ℕ} (U : Set (Vec d)) (P : BlockVec d)
    (a : CoeffField d) : Set ℝ :=
  { m | ∃ X : BlockState d, IsBlockMuAdmissible U P X ∧ m = volumeAverage U (blockEnergyDensity a X) }

noncomputable def Mu {d : ℕ} (U : Set (Vec d)) (P : BlockVec d) (a : CoeffField d) : ℝ :=
  sInf (muValueSet U P a)

theorem muValueSet_mem {d : ℕ} {U : Set (Vec d)} {P : BlockVec d} {a : CoeffField d}
    {X : BlockState d} (hX : IsBlockMuAdmissible U P X) :
    volumeAverage U (blockEnergyDensity a X) ∈ muValueSet U P a :=
  ⟨X, hX, rfl⟩

theorem muValueSet_nonempty {d : ℕ} (U : Set (Vec d)) (P : BlockVec d) (a : CoeffField d) :
    (muValueSet U P a).Nonempty := by
  let X : BlockState d :=
    { potential := fun _ => P.1
      flux := fun _ => P.2 }
  refine ⟨volumeAverage U (blockEnergyDensity a X), ?_⟩
  refine muValueSet_mem ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hzero : (fun x => X.potential x - P.1) = (0 : Vec d → Vec d) := by
      funext x
      simp [X]
    rw [hzero]
    exact
      (MeasureTheory.MemLp.zero : MeasureTheory.MemLp (0 : Vec d → Vec d) 2 (volumeMeasureOn U))
  · have hzero : (fun x => X.potential x - P.1) = (0 : Vec d → Vec d) := by
      funext x
      simp [X]
    rw [hzero]
    exact isPotentialZeroTraceOn_zero (U := U)
  · have hzero : (fun x => X.flux x - P.2) = (0 : Vec d → Vec d) := by
      funext x
      simp [X]
    rw [hzero]
    exact
      (MeasureTheory.MemLp.zero : MeasureTheory.MemLp (0 : Vec d → Vec d) 2 (volumeMeasureOn U))
  · have hzero : (fun x => X.flux x - P.2) = (0 : Vec d → Vec d) := by
      funext x
      simp [X]
    rw [hzero]
    exact isSolenoidalZeroNormalTraceOn_zero (U := U)

theorem le_Mu_of_forall_mem_muValueSet {d : ℕ} {U : Set (Vec d)} {P : BlockVec d}
    {a : CoeffField d} {c : ℝ}
    (hc : ∀ m ∈ muValueSet U P a, c ≤ m) :
    c ≤ Mu U P a := by
  unfold Mu
  exact le_csInf (muValueSet_nonempty U P a) hc

theorem le_Mu_of_forall_isBlockMuAdmissible {d : ℕ} {U : Set (Vec d)} {P : BlockVec d}
    {a : CoeffField d} {c : ℝ}
    (hc : ∀ X : BlockState d, IsBlockMuAdmissible U P X →
      c ≤ volumeAverage U (blockEnergyDensity a X)) :
    c ≤ Mu U P a := by
  apply le_Mu_of_forall_mem_muValueSet
  intro m hm
  rcases hm with ⟨X, hX, rfl⟩
  exact hc X hX

noncomputable def blockResponseIntegrand {d : ℕ} (a : CoeffField d) (P Q : BlockVec d)
    (X : BlockState d) : Vec d → ℝ :=
  fun x =>
    -blockEnergyDensity a X x
      - blockVecDot P (blockMatVecMul (blockCoeffField a x) (X.eval x))
      + blockVecDot Q (X.eval x)

structure BlockResponseIntegrabilityData {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (X : BlockState d) : Prop where
  flux_memL2 : MemVectorL2 U X.flux
  energyIntegrable : MeasureTheory.IntegrableOn (blockEnergyDensity a X) U

noncomputable def blockJValueSet {d : ℕ} (U : Set (Vec d)) (P Q : BlockVec d)
    (a : CoeffField d) : Set ℝ :=
  { m |
      ∃ X : BlockState d, BlockResponseSpace a U X ∧
        BlockResponseIntegrabilityData U a X ∧
        m = volumeAverage U (blockResponseIntegrand a P Q X) }

noncomputable def BlockJ {d : ℕ} (U : Set (Vec d)) (P Q : BlockVec d) (a : CoeffField d) : ℝ :=
  sSup (blockJValueSet U P Q a)

noncomputable def scalarResponseIntegrand {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (p q : Vec d) (u : AHarmonicFunction a U) : Vec d → ℝ :=
  fun x =>
    -((1 / 2 : ℝ) * vecDot (u.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x)))
      - vecDot p (matVecMul (a x) (u.toH1.grad x))
      + vecDot q (u.toH1.grad x)

noncomputable def responseJValueSet {d : ℕ} (U : Set (Vec d)) (p q : Vec d)
    (a : CoeffField d) : Set ℝ :=
  { m |
      ∃ u : AHarmonicFunction a U,
        m = volumeAverage U (scalarResponseIntegrand U a p q u) }

noncomputable def ResponseJ {d : ℕ} (U : Set (Vec d)) (p q : Vec d) (a : CoeffField d) : ℝ :=
  sSup (responseJValueSet U p q a)

def IsCoarseBlockMatrix {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) (Abar : BlockMat d) : Prop :=
  IsSymmetricBlockMat Abar ∧
    ∀ P : BlockVec d, Mu U P a = (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul Abar P)

/--
`Mu` is quadratic in the note-faithful sense: after passing to the full `2d`-dimensional
coordinate space, it is one half of a quadratic form.
-/
def HasQuadraticMu {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) : Prop :=
  ∃ Q : QuadraticForm ℝ (FullBlockVec d),
    ∀ P : BlockVec d, Mu U P a = (1 / 2 : ℝ) * Q (toFullBlockVec P)

private noncomputable def coarseBlockEntry {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (α β : BlockCoord d) : ℝ :=
  if _h : α = β then
    2 * Mu U (blockBasis α) a
  else
    Mu U (blockBasis α + blockBasis β) a - Mu U (blockBasis α) a - Mu U (blockBasis β) a

noncomputable def coarseBlockMatrix {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) : BlockMat d :=
  { upperLeft := fun i j => coarseBlockEntry U a (Sum.inl i) (Sum.inl j)
    upperRight := fun i j => coarseBlockEntry U a (Sum.inl i) (Sum.inr j)
    lowerLeft := fun i j => coarseBlockEntry U a (Sum.inr i) (Sum.inl j)
    lowerRight := fun i j => coarseBlockEntry U a (Sum.inr i) (Sum.inr j) }

theorem blockEnergyDensity_restrictCoeffField_eq_of_mem {d : ℕ} {U : Set (Vec d)}
    (a : CoeffField d) (X : BlockState d) {x : Vec d} (hx : x ∈ U) :
    blockEnergyDensity (restrictCoeffField U a) X x = blockEnergyDensity a X x := by
  simp [blockEnergyDensity, blockCoeffField, restrictCoeffField, hx]

theorem volumeAverage_blockEnergyDensity_restrictCoeffField_eq {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (a : CoeffField d) (X : BlockState d) :
    volumeAverage U (blockEnergyDensity (restrictCoeffField U a) X) =
      volumeAverage U (blockEnergyDensity a X) := by
  unfold volumeAverage
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
  exact blockEnergyDensity_restrictCoeffField_eq_of_mem a X hx

theorem muValueSet_restrictCoeffField_eq {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (P : BlockVec d) (a : CoeffField d) :
    muValueSet U P (restrictCoeffField U a) = muValueSet U P a := by
  ext m
  constructor
  · rintro ⟨X, hX, hm⟩
    refine ⟨X, hX, ?_⟩
    calc
      m = volumeAverage U (blockEnergyDensity (restrictCoeffField U a) X) := hm
      _ = volumeAverage U (blockEnergyDensity a X) :=
        volumeAverage_blockEnergyDensity_restrictCoeffField_eq hU a X
  · rintro ⟨X, hX, hm⟩
    refine ⟨X, hX, ?_⟩
    calc
      m = volumeAverage U (blockEnergyDensity a X) := hm
      _ = volumeAverage U (blockEnergyDensity (restrictCoeffField U a) X) :=
        (volumeAverage_blockEnergyDensity_restrictCoeffField_eq hU a X).symm

theorem Mu_restrictCoeffField_eq {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (P : BlockVec d) (a : CoeffField d) :
    Mu U P (restrictCoeffField U a) = Mu U P a := by
  unfold Mu
  rw [muValueSet_restrictCoeffField_eq hU P a]

theorem coarseBlockMatrix_eq_of_mu_eq {d : ℕ} {U V : Set (Vec d)}
    {a b : CoeffField d} (hmu : ∀ P : BlockVec d, Mu U P a = Mu V P b) :
    coarseBlockMatrix U a = coarseBlockMatrix V b := by
  refine blockMat_ext ?_ ?_ ?_ ?_
  · funext i j
    by_cases h : (Sum.inl i : BlockCoord d) = Sum.inl j
    · have hij : i = j := Sum.inl.inj h
      subst hij
      simp [coarseBlockMatrix, coarseBlockEntry, hmu]
    · simp [coarseBlockMatrix, coarseBlockEntry, hmu]
  · funext i j
    by_cases h : (Sum.inl i : BlockCoord d) = Sum.inr j
    · cases h
    · simp [coarseBlockMatrix, coarseBlockEntry, hmu]
  · funext i j
    by_cases h : (Sum.inr i : BlockCoord d) = Sum.inl j
    · cases h
    · simp [coarseBlockMatrix, coarseBlockEntry, hmu]
  · funext i j
    by_cases h : (Sum.inr i : BlockCoord d) = Sum.inr j
    · have hij : i = j := Sum.inr.inj h
      subst hij
      simp [coarseBlockMatrix, coarseBlockEntry, hmu]
    · simp [coarseBlockMatrix, coarseBlockEntry, hmu]

theorem coarseBlockMatrix_restrictCoeffField_eq {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (a : CoeffField d) :
    coarseBlockMatrix U (restrictCoeffField U a) = coarseBlockMatrix U a :=
  coarseBlockMatrix_eq_of_mu_eq (U := U) (V := U)
    (a := restrictCoeffField U a)
    (b := a)
    (fun P => Mu_restrictCoeffField_eq hU P a)

private theorem coarseBlockEntry_eq_of_isCoarseBlockMatrix {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {Abar : BlockMat d} (hA : IsCoarseBlockMatrix U a Abar)
    (α β : BlockCoord d) :
    coarseBlockEntry U a α β = blockMatEntry Abar α β := by
  rcases hA with ⟨hsymm, hmu⟩
  by_cases h : α = β
  · subst β
    have hdiag := hmu (blockBasis α)
    simp [coarseBlockEntry]
    rw [blockBasis_pairing] at hdiag
    linarith
  · simp [coarseBlockEntry, h]
    have hsum := hmu (blockBasis α + blockBasis β)
    have hdiagα := hmu (blockBasis α)
    have hdiagβ := hmu (blockBasis β)
    rw [blockBasis_sum_pairing] at hsum
    rw [blockBasis_pairing] at hdiagα
    rw [blockBasis_pairing] at hdiagβ
    have hsymm' := hsymm α β
    linarith

theorem eq_coarseBlockMatrix_of_isCoarseBlockMatrix {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {Abar : BlockMat d} (hA : IsCoarseBlockMatrix U a Abar) :
    Abar = coarseBlockMatrix U a := by
  refine blockMat_ext ?_ ?_ ?_ ?_
  · funext i j
    symm
    exact coarseBlockEntry_eq_of_isCoarseBlockMatrix hA (Sum.inl i) (Sum.inl j)
  · funext i j
    symm
    exact coarseBlockEntry_eq_of_isCoarseBlockMatrix hA (Sum.inl i) (Sum.inr j)
  · funext i j
    symm
    exact coarseBlockEntry_eq_of_isCoarseBlockMatrix hA (Sum.inr i) (Sum.inl j)
  · funext i j
    symm
    exact coarseBlockEntry_eq_of_isCoarseBlockMatrix hA (Sum.inr i) (Sum.inr j)

theorem isCoarseBlockMatrix_coarseBlockMatrix {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) :
    IsCoarseBlockMatrix U a (coarseBlockMatrix U a) := by
  rcases hex with ⟨Abar, hA⟩
  rw [← eq_coarseBlockMatrix_of_isCoarseBlockMatrix hA]
  exact hA

theorem Mu_eq_half_blockVecDot_coarseBlockMatrix {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) (P : BlockVec d) :
    Mu U P a = (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) :=
  (isCoarseBlockMatrix_coarseBlockMatrix hex).2 P

theorem existsUnique_coarseBlockMatrix {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) :
    ∃! Abar : BlockMat d, IsCoarseBlockMatrix U a Abar := by
  rcases hex with ⟨Abar, hA⟩
  refine ⟨Abar, hA, ?_⟩
  intro Bbar hB
  rw [eq_coarseBlockMatrix_of_isCoarseBlockMatrix hA,
    eq_coarseBlockMatrix_of_isCoarseBlockMatrix hB]

theorem isCoarseBlockMatrix_of_mu_eq_half_quadraticForm {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {Q : QuadraticForm ℝ (FullBlockVec d)}
    (hmu : ∀ P : BlockVec d, Mu U P a = (1 / 2 : ℝ) * Q (toFullBlockVec P)) :
    IsCoarseBlockMatrix U a (ofFullBlockMat Q.toMatrix') := by
  refine ⟨isSymmetricBlockMat_of_isSymm (QuadraticForm.isSymm_toMatrix' Q), ?_⟩
  intro P
  rw [hmu P]
  congr 1
  calc
    Q (toFullBlockVec P)
      = Q.associated (toFullBlockVec P) (toFullBlockVec P) := by
          symm
          exact QuadraticMap.associated_eq_self_apply (S := ℝ) (Q := Q) (toFullBlockVec P)
    _ = Matrix.toLinearMap₂' ℝ Q.toMatrix' (toFullBlockVec P) (toFullBlockVec P) := by
          rw [QuadraticForm.toMatrix', Matrix.toLinearMap₂'_toMatrix']
    _ = blockVecDot P (blockMatVecMul (ofFullBlockMat Q.toMatrix') P) := by
          symm
          simpa using
            (blockVecDot_blockMatVecMul_eq_toLinearMap₂'
              (A := ofFullBlockMat Q.toMatrix') (X := P) (Y := P))

theorem eq_coarseBlockMatrix_of_mu_eq_half_quadraticForm {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {Q : QuadraticForm ℝ (FullBlockVec d)}
    (hmu : ∀ P : BlockVec d, Mu U P a = (1 / 2 : ℝ) * Q (toFullBlockVec P)) :
    ofFullBlockMat Q.toMatrix' = coarseBlockMatrix U a := by
  exact eq_coarseBlockMatrix_of_isCoarseBlockMatrix
    (isCoarseBlockMatrix_of_mu_eq_half_quadraticForm hmu)

theorem exists_coarseBlockMatrix_of_hasQuadraticMu {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hquad : HasQuadraticMu U a) :
    ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar := by
  rcases hquad with ⟨Q, hmu⟩
  exact ⟨ofFullBlockMat Q.toMatrix', isCoarseBlockMatrix_of_mu_eq_half_quadraticForm hmu⟩

theorem existsUnique_coarseBlockMatrix_of_hasQuadraticMu {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} (hquad : HasQuadraticMu U a) :
    ∃! Abar : BlockMat d, IsCoarseBlockMatrix U a Abar :=
  existsUnique_coarseBlockMatrix (exists_coarseBlockMatrix_of_hasQuadraticMu hquad)

theorem Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} (hquad : HasQuadraticMu U a) (P : BlockVec d) :
    Mu U P a = (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) :=
  Mu_eq_half_blockVecDot_coarseBlockMatrix
    (exists_coarseBlockMatrix_of_hasQuadraticMu hquad) P

/-- The note-faithful `\mathbf A_*^{-1}(U; a)` obtained from `\mathbf A(U; a)` by reflection. -/
noncomputable def coarseStarredBlockMatrixInv {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) :
    BlockMat d :=
  blockReflect (coarseBlockMatrix U a)

def IsSigmaStarCoarse {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) (sigmaStar : Mat d) : Prop :=
  sigmaStar.IsSymm ∧
    ∀ q : Vec d, ResponseJ U 0 q a = (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q)

def IsKappaCoarse {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (sigmaStar kappa : Mat d) : Prop :=
  ∀ p q : Vec d,
    ResponseJ U p q a - ResponseJ U p 0 a - ResponseJ U 0 q a + vecDot p q =
      vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa p))

def IsSigmaCoarse {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (sigma sigmaStar kappa : Mat d) : Prop :=
  sigma.IsSymm ∧
    ∀ p : Vec d,
      ResponseJ U p 0 a
        - (1 / 2 : ℝ) * vecDot p (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹
            (matVecMul kappa p)))
          =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigma p)

def IsSigmaStarInvCoarse {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) (sigmaStarInv : Mat d) : Prop :=
  sigmaStarInv.IsSymm ∧
    ∀ q : Vec d, ResponseJ U 0 q a = (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStarInv q)

private noncomputable def sigmaStarInvEntry {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (i j : Fin d) : ℝ :=
  if _h : i = j then
    2 * ResponseJ U 0 (Pi.single i 1) a
  else
    ResponseJ U 0 (Pi.single i 1 + Pi.single j 1) a
      - ResponseJ U 0 (Pi.single i 1) a
      - ResponseJ U 0 (Pi.single j 1) a

noncomputable def sigmaStarInvCoarse {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) : Mat d :=
  fun i j => sigmaStarInvEntry U a i j

@[simp] theorem sigmaStarInvCoarse_apply_same {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (i : Fin d) :
    sigmaStarInvCoarse U a i i = 2 * ResponseJ U 0 (Pi.single i 1) a := by
  simp [sigmaStarInvCoarse, sigmaStarInvEntry]

@[simp] theorem sigmaStarInvCoarse_apply_of_ne {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    {i j : Fin d} (hij : i ≠ j) :
    sigmaStarInvCoarse U a i j =
      ResponseJ U 0 (Pi.single i 1 + Pi.single j 1) a
        - ResponseJ U 0 (Pi.single i 1) a
        - ResponseJ U 0 (Pi.single j 1) a := by
  simp [sigmaStarInvCoarse, sigmaStarInvEntry, hij]

private theorem sigmaStarInvEntry_eq_of_isSigmaStarInvCoarse {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {sigmaStarInv : Mat d} (hS : IsSigmaStarInvCoarse U a sigmaStarInv)
    (i j : Fin d) :
    sigmaStarInvEntry U a i j = sigmaStarInv i j := by
  rcases hS with ⟨hsymm, hresp⟩
  by_cases h : i = j
  · subst j
    have hdiag := hresp (Pi.single i 1)
    simp [sigmaStarInvEntry, vecDot_single_left, matVecMul_single] at hdiag ⊢
    linarith
  · simp [sigmaStarInvEntry, h]
    have hsum := hresp (Pi.single i 1 + Pi.single j 1)
    have hdiag_i := hresp (Pi.single i 1)
    have hdiag_j := hresp (Pi.single j 1)
    rw [basis_sum_pairing] at hsum
    simp [vecDot_single_left, matVecMul_single] at hdiag_i hdiag_j
    have hsymm' := hsymm.apply i j
    linarith

theorem eq_sigmaStarInvCoarse_of_isSigmaStarInvCoarse {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {sigmaStarInv : Mat d} (hS : IsSigmaStarInvCoarse U a sigmaStarInv) :
    sigmaStarInv = sigmaStarInvCoarse U a := by
  funext i j
  symm
  exact sigmaStarInvEntry_eq_of_isSigmaStarInvCoarse hS i j

theorem isSigmaStarInvCoarse_sigmaStarInvCoarse {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ sigmaStarInv : Mat d, IsSigmaStarInvCoarse U a sigmaStarInv) :
    IsSigmaStarInvCoarse U a (sigmaStarInvCoarse U a) := by
  rcases hex with ⟨sigmaStarInv, hS⟩
  rw [← eq_sigmaStarInvCoarse_of_isSigmaStarInvCoarse hS]
  exact hS

theorem existsUnique_sigmaStarInvCoarse {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ sigmaStarInv : Mat d, IsSigmaStarInvCoarse U a sigmaStarInv) :
    ∃! sigmaStarInv : Mat d, IsSigmaStarInvCoarse U a sigmaStarInv := by
  rcases hex with ⟨sigmaStarInv, hS⟩
  refine ⟨sigmaStarInv, hS, ?_⟩
  intro sigmaStarInv' hS'
  rw [eq_sigmaStarInvCoarse_of_isSigmaStarInvCoarse hS,
    eq_sigmaStarInvCoarse_of_isSigmaStarInvCoarse hS']

theorem isSigmaStarInvCoarse_of_isSigmaStarCoarse {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigmaStar : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar) :
    IsSigmaStarInvCoarse U a sigmaStar⁻¹ := by
  rcases hS with ⟨hsymm, hresp⟩
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsSymm.ext_iff]
    intro i j
    have hT := Matrix.transpose_nonsing_inv (A := sigmaStar)
    simpa [hsymm.eq] using congrFun (congrFun hT i) j
  · simpa using hresp

theorem sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {sigmaStar : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar) :
    sigmaStarInvCoarse U a = sigmaStar⁻¹ := by
  symm
  exact eq_sigmaStarInvCoarse_of_isSigmaStarInvCoarse
    (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS)

noncomputable def sigmaStarCoarse {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) : Mat d :=
  (sigmaStarInvCoarse U a)⁻¹

theorem eq_sigmaStarCoarse_of_isSigmaStarCoarse {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigmaStar : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar) (hdet : IsUnit sigmaStar.det) :
    sigmaStarCoarse U a = sigmaStar := by
  unfold sigmaStarCoarse
  rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS, Matrix.nonsing_inv_nonsing_inv _ hdet]

theorem sigmaStarCoarse_isSymm_of_isSigmaStarCoarse {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {sigmaStar : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar)
    (hdet : IsUnit sigmaStar.det) :
    (sigmaStarCoarse U a).IsSymm := by
  rw [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet]
  exact hS.1

def IsSigmaStarInvKappaCoarse {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) (M : Mat d) : Prop :=
  ∀ p q : Vec d,
    ResponseJ U p q a - ResponseJ U p 0 a - ResponseJ U 0 q a + vecDot p q =
      vecDot q (matVecMul M p)

noncomputable def sigmaStarInvKappaCoarse {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) : Mat d :=
  fun i j =>
    ResponseJ U (Pi.single j 1) (Pi.single i 1) a
      - ResponseJ U (Pi.single j 1) 0 a
      - ResponseJ U 0 (Pi.single i 1) a
      + vecDot (Pi.single j 1) (Pi.single i 1)

private theorem sigmaStarInvKappaEntry_eq_of_isSigmaStarInvKappaCoarse {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {M : Mat d}
    (hM : IsSigmaStarInvKappaCoarse U a M) (i j : Fin d) :
    sigmaStarInvKappaCoarse U a i j = M i j := by
  have hij := hM (Pi.single j 1) (Pi.single i 1)
  simp [sigmaStarInvKappaCoarse, vecDot_single_left, matVecMul_single, vecDot_single_right] at hij ⊢
  exact hij

theorem eq_sigmaStarInvKappaCoarse_of_isSigmaStarInvKappaCoarse {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {M : Mat d}
    (hM : IsSigmaStarInvKappaCoarse U a M) :
    M = sigmaStarInvKappaCoarse U a := by
  funext i j
  symm
  exact sigmaStarInvKappaEntry_eq_of_isSigmaStarInvKappaCoarse hM i j

theorem isSigmaStarInvKappaCoarse_sigmaStarInvKappaCoarse {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ M : Mat d, IsSigmaStarInvKappaCoarse U a M) :
    IsSigmaStarInvKappaCoarse U a (sigmaStarInvKappaCoarse U a) := by
  rcases hex with ⟨M, hM⟩
  rw [← eq_sigmaStarInvKappaCoarse_of_isSigmaStarInvKappaCoarse hM]
  exact hM

theorem existsUnique_sigmaStarInvKappaCoarse {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ M : Mat d, IsSigmaStarInvKappaCoarse U a M) :
    ∃! M : Mat d, IsSigmaStarInvKappaCoarse U a M := by
  rcases hex with ⟨M, hM⟩
  refine ⟨M, hM, ?_⟩
  intro M' hM'
  rw [eq_sigmaStarInvKappaCoarse_of_isSigmaStarInvKappaCoarse hM,
    eq_sigmaStarInvKappaCoarse_of_isSigmaStarInvKappaCoarse hM']

theorem isSigmaStarInvKappaCoarse_of_isKappaCoarse {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigmaStar kappa : Mat d} (hK : IsKappaCoarse U a sigmaStar kappa) :
    IsSigmaStarInvKappaCoarse U a (sigmaStar⁻¹ * kappa) := by
  intro p q
  rw [hK p q]
  rw [matVecMul_mul]

theorem sigmaStarInvKappaCoarse_eq_mul_of_isKappaCoarse {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {sigmaStar kappa : Mat d} (hK : IsKappaCoarse U a sigmaStar kappa) :
    sigmaStarInvKappaCoarse U a = sigmaStar⁻¹ * kappa := by
  symm
  exact eq_sigmaStarInvKappaCoarse_of_isSigmaStarInvKappaCoarse
    (isSigmaStarInvKappaCoarse_of_isKappaCoarse hK)

noncomputable def kappaCoarse {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) : Mat d :=
  sigmaStarCoarse U a * sigmaStarInvKappaCoarse U a

theorem eq_kappaCoarse_of_isKappaCoarse {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigmaStar kappa : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa) (hdet : IsUnit sigmaStar.det) :
    kappaCoarse U a = kappa := by
  unfold kappaCoarse
  rw [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    sigmaStarInvKappaCoarse_eq_mul_of_isKappaCoarse hK]
  simpa [Matrix.mul_assoc] using Matrix.mul_nonsing_inv_cancel_left (A := sigmaStar) kappa hdet

noncomputable def sigmaCorrectedResponse {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (p : Vec d) : ℝ :=
  ResponseJ U p 0 a
    - (1 / 2 : ℝ) * vecDot p
        (matVecMul (matTranspose (kappaCoarse U a))
          (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)))

def IsSigmaCanonicalCoarse {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) (sigma : Mat d) : Prop :=
  sigma.IsSymm ∧
    ∀ p : Vec d,
      sigmaCorrectedResponse U a p = (1 / 2 : ℝ) * vecDot p (matVecMul sigma p)

private noncomputable def sigmaEntry {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (i j : Fin d) : ℝ :=
  if _h : i = j then
    2 * sigmaCorrectedResponse U a (Pi.single i 1)
  else
    sigmaCorrectedResponse U a (Pi.single i 1 + Pi.single j 1)
      - sigmaCorrectedResponse U a (Pi.single i 1)
      - sigmaCorrectedResponse U a (Pi.single j 1)

noncomputable def sigmaCoarse {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) : Mat d :=
  fun i j => sigmaEntry U a i j

@[simp] theorem sigmaCoarse_apply_same {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (i : Fin d) :
    sigmaCoarse U a i i = 2 * sigmaCorrectedResponse U a (Pi.single i 1) := by
  simp [sigmaCoarse, sigmaEntry]

@[simp] theorem sigmaCoarse_apply_of_ne {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    {i j : Fin d} (hij : i ≠ j) :
    sigmaCoarse U a i j =
      sigmaCorrectedResponse U a (Pi.single i 1 + Pi.single j 1)
        - sigmaCorrectedResponse U a (Pi.single i 1)
        - sigmaCorrectedResponse U a (Pi.single j 1) := by
  simp [sigmaCoarse, sigmaEntry, hij]

private theorem sigmaEntry_eq_of_isSigmaCanonicalCoarse {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {sigma : Mat d} (hSigma : IsSigmaCanonicalCoarse U a sigma)
    (i j : Fin d) :
    sigmaEntry U a i j = sigma i j := by
  rcases hSigma with ⟨hsymm, hresp⟩
  by_cases h : i = j
  · subst j
    have hdiag := hresp (Pi.single i 1)
    simp [sigmaEntry, vecDot_single_left, matVecMul_single] at hdiag ⊢
    linarith
  · simp [sigmaEntry, h]
    have hsum := hresp (Pi.single i 1 + Pi.single j 1)
    have hdiag_i := hresp (Pi.single i 1)
    have hdiag_j := hresp (Pi.single j 1)
    rw [basis_sum_pairing] at hsum
    simp [vecDot_single_left, matVecMul_single] at hdiag_i hdiag_j
    have hsymm' := hsymm.apply i j
    linarith

theorem eq_sigmaCoarse_of_isSigmaCanonicalCoarse {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {sigma : Mat d} (hSigma : IsSigmaCanonicalCoarse U a sigma) :
    sigma = sigmaCoarse U a := by
  funext i j
  symm
  exact sigmaEntry_eq_of_isSigmaCanonicalCoarse hSigma i j

theorem isSigmaCanonicalCoarse_sigmaCoarse {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ sigma : Mat d, IsSigmaCanonicalCoarse U a sigma) :
    IsSigmaCanonicalCoarse U a (sigmaCoarse U a) := by
  rcases hex with ⟨sigma, hSigma⟩
  rw [← eq_sigmaCoarse_of_isSigmaCanonicalCoarse hSigma]
  exact hSigma

theorem existsUnique_sigmaCoarse {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ sigma : Mat d, IsSigmaCanonicalCoarse U a sigma) :
    ∃! sigma : Mat d, IsSigmaCanonicalCoarse U a sigma := by
  rcases hex with ⟨sigma, hSigma⟩
  refine ⟨sigma, hSigma, ?_⟩
  intro sigma' hSigma'
  rw [eq_sigmaCoarse_of_isSigmaCanonicalCoarse hSigma,
    eq_sigmaCoarse_of_isSigmaCanonicalCoarse hSigma']

theorem isSigmaCanonicalCoarse_of_isSigmaCoarse {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det) :
    IsSigmaCanonicalCoarse U a sigma := by
  rcases hSigma with ⟨hsymm, hresp⟩
  refine ⟨hsymm, ?_⟩
  intro p
  rw [sigmaCorrectedResponse, eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
  exact hresp p

theorem sigmaCoarse_eq_of_isSigmaCoarse {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det) :
    sigmaCoarse U a = sigma := by
  symm
  exact eq_sigmaCoarse_of_isSigmaCanonicalCoarse
    (isSigmaCanonicalCoarse_of_isSigmaCoarse hS hK hSigma hdet)

theorem sigmaCoarse_isSymm_of_isSigmaCoarse {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det) :
    (sigmaCoarse U a).IsSymm := by
  rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet]
  exact hSigma.1

noncomputable def bCoarse {d : ℕ} (sigma sigmaStar kappa : Mat d) : Mat d :=
  sigma + (matTranspose kappa) * sigmaStar⁻¹ * kappa

theorem bCoarse_smul {d : ℕ} {sigma sigmaStar kappa : Mat d}
    (hdet : IsUnit sigmaStar.det) {lam : ℝ} (hlam : 0 < lam) :
    bCoarse (lam • sigma) (lam • sigmaStar) (lam • kappa) = lam • bCoarse sigma sigmaStar kappa := by
  unfold bCoarse
  rw [nonsing_inv_smul lam hlam.ne' hdet]
  calc
    lam • sigma + (matTranspose (lam • kappa)) * (lam⁻¹ • sigmaStar⁻¹) * (lam • kappa) =
        lam • sigma + (matTranspose (lam • kappa)) * (sigmaStar⁻¹ * kappa) := by
          rw [mul_assoc]
          congr 1
          rw [smul_mul_assoc, mul_smul_comm]
          simp [smul_smul, inv_mul_cancel₀ hlam.ne']
    _ = lam • sigma + lam • ((matTranspose kappa) * (sigmaStar⁻¹ * kappa)) := by
          have htranspose : matTranspose (lam • kappa) = lam • matTranspose kappa := by
            simp [matTranspose]
          rw [htranspose, smul_mul_assoc]
    _ = lam • bCoarse sigma sigmaStar kappa := by
          simp [bCoarse, smul_add, mul_assoc]

theorem bCoarse_isSymm_of_isSigmaCoarse {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    (bCoarse sigma sigmaStar kappa).IsSymm := by
  rcases hSigma with ⟨hSigmaSymm, _⟩
  have hSInvSymm : (sigmaStar⁻¹).IsSymm :=
    (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS).1
  have hCorrSymm : (((matTranspose kappa) * sigmaStar⁻¹ * kappa)).IsSymm :=
    transpose_mul_symm_mul_isSymm kappa sigmaStar⁻¹ hSInvSymm
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp [bCoarse, hSigmaSymm.apply i j, hCorrSymm.apply i j]

noncomputable def aCoarse {d : ℕ} (sigma kappa : Mat d) : Mat d :=
  sigma - matTranspose kappa

noncomputable def aStarCoarse {d : ℕ} (sigmaStar kappa : Mat d) : Mat d :=
  sigmaStar - matTranspose kappa

end Homogenization
