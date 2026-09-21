/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Common

/-! # Scalar Chain -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace Pigeonhole

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Scalar-chain input for the Section 5.4 pigeonhole lemma

The manuscript pigeonhole argument uses monotonicity of the scalar annealed
coefficients.  The current Ch4 endpoint proves this from full coarse-block
integrability; this file records the exact Section 5.4-facing consequence
without making it part of the public pigeonhole theorem statement.
-/

/-- Component-wise scalar-chain monotonicity obtained from the existing Ch4
full-block integrability endpoint. -/
theorem scalarChain_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {n m : ℤ} (hn_nonneg : 0 ≤ n) (hnm : n ≤ m)
    (hParentBlockInt :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d m)) P)
    (hChildBlockInt :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P)
    (hDescBlockInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P) :
    hP.barSigmaStarAtScale hStruct n ≤ hP.barSigmaStarAtScale hStruct m ∧
      (hP.barSigmaStarAtScale hStruct m)⁻¹ ≤
        (hP.barSigmaStarAtScale hStruct n)⁻¹ ∧
      hP.barSigmaAtScale hStruct m ≤ hP.barSigmaAtScale hStruct n := by
  let scalarization :=
    Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct
  let hPrim_m :=
    Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct m
  let hPrim_n :=
    Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n
  have hStarInv_m_pos : 0 < hPrim_m.barSigmaStarInv :=
    Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube
      hP hPrim_m hParentBlockInt
  have hStarInv_n_pos : 0 < hPrim_n.barSigmaStarInv :=
    Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube
      hP hPrim_n hChildBlockInt
  have hContrast_m : 1 ≤ hPrim_m.contrast :=
    Ch04.RestrictionLawCarrier.Internal.one_le_primitive_contrast_of_integrable_coarseFullBlockMatrixAtCube
      hP hPrim_m hParentBlockInt
  have hChain :=
    Ch04.RestrictionLawCarrier.Internal.scalar_chain_of_primitive_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct.stationary hn_nonneg hnm scalarization hPrim_m hPrim_n
      hParentBlockInt hDescBlockInt hStarInv_m_pos hContrast_m
  have hStar_nm :
      hP.barSigmaStarAtScale hStruct n ≤ hP.barSigmaStarAtScale hStruct m := by
    simpa [Ch04.RestrictionLawCarrier.barSigmaStarAtScale, scalarization] using hChain.1
  have hSigma_mn :
      hP.barSigmaAtScale hStruct m ≤ hP.barSigmaAtScale hStruct n := by
    simpa [Ch04.RestrictionLawCarrier.barSigmaAtScale, scalarization] using hChain.2.2
  have hStar_m_pos : 0 < hP.barSigmaStarAtScale hStruct m := by
    rw [hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct m]
    simpa [Ch04.RestrictionLawCarrier.barSigmaStarInvAtScale, hPrim_m] using inv_pos.mpr hStarInv_m_pos
  have hStar_n_pos : 0 < hP.barSigmaStarAtScale hStruct n := by
    rw [hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct n]
    simpa [Ch04.RestrictionLawCarrier.barSigmaStarInvAtScale, hPrim_n] using inv_pos.mpr hStarInv_n_pos
  refine ⟨hStar_nm, ?_, hSigma_mn⟩
  exact (inv_le_inv₀ hStar_m_pos hStar_n_pos).2 hStar_nm

/-- Component-wise scalar-chain monotonicity with the full-block
integrability supplied by `(P4)`. -/
theorem scalarChain_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {n m : ℕ} (hnm : n ≤ m) :
    hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
        hP.barSigmaStarAtScale hStruct (m : ℤ) ∧
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ ≤
        (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹ ∧
      hP.barSigmaAtScale hStruct (m : ℤ) ≤
        hP.barSigmaAtScale hStruct (n : ℤ) := by
  have hn_nonneg : 0 ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have hnm_int : (n : ℤ) ≤ (m : ℤ) := by exact_mod_cast hnm
  have hParentBlockInt :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hChildBlockInt :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 n
  have hDescBlockInt :
      ∀ R, R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ) →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P := by
    intro R hR
    exact
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hStruct.stationary hn_nonneg hnm_int hR hChildBlockInt
  exact
    scalarChain_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct hn_nonneg hnm_int hParentBlockInt hChildBlockInt hDescBlockInt

/-- Under `(P4)`, the starred scalar coefficient is positive at every
nonnegative scale. -/
theorem barSigmaStarAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < hP.barSigmaStarAtScale hStruct (m : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hInv : 0 < hP.barSigmaStarInvAtScale hStruct (m : ℤ) := by
    simpa [Ch04.RestrictionLawCarrier.barSigmaStarInvAtScale] using
      Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube
        hP
        (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw
          hP hStruct (m : ℤ))
        hBlock
  rw [hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct (m : ℤ)]
  exact inv_pos.mpr hInv

/-- Under `(P4)`, the inverse starred scalar coefficient is positive at every
nonnegative scale. -/
theorem barSigmaStarAtScale_inv_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
  inv_pos.mpr (barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m)

/-- Under `(P4)`, the upper scalar coefficient is positive at every
nonnegative scale. -/
theorem barSigmaAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < hP.barSigmaAtScale hStruct (m : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have htheta :=
    Section52.one_le_thetaAtScale_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct (m : ℤ) hBlock
  have hstar_pos := barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hprod_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) *
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ := by
    exact lt_of_lt_of_le zero_lt_one (by
      simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale] using htheta)
  exact pos_of_mul_pos_left hprod_pos (inv_pos.mpr hstar_pos).le

end

end Pigeonhole
end Section54
end Ch05
end Book
end Homogenization
