/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Definitions
import LeanPool.CoarseGraining.Homogenization.Probability.RandomField

/-! # Basic Identities -/

namespace Homogenization

noncomputable section

/-!
# BlockResponse Foundations -- basic deterministic identities

blockResponse_zero membership in responseSpace, isEllipticFieldOn for
adjointCoeffField, blockMatVecMul_blockCoeffField_pair identities,
symmPart algebra and pointwiseBlockEnergy_pair_eq_symmPart_sum plus
the lowerImage / upperImage orthogonality and responseSpace_smul lemmas.
-/

theorem blockResponse_zero_mem_responseSpace {d : ℕ} (a : CoeffField d) (U : Set (Vec d)) :
    BlockResponseSpace a U ({ potential := 0, flux := 0 } : BlockState d) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsBlockPotentialOn
    exact ⟨0, rfl⟩
  · unfold IsBlockSolenoidalOn IsSolenoidalOn
    intro φ
    rw [show (fun x => vecDot ((0 : Vec d → Vec d) x) (φ.toH1Function.grad x)) = 0 by
          funext x
          change vecDot (0 : Vec d) (φ.toH1Function.grad x) = 0
          simpa using vecDot_zero_left (φ.toH1Function.grad x)]
    simp
  intro Y hY
  rw [show
      (fun x =>
        blockVecDot (Y.eval x)
          (blockMatVecMul (blockCoeffField a x)
            (({ potential := 0, flux := 0 } : BlockState d).eval x))) = 0 by
        funext x
        simp [BlockState.eval, blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_right]]
  simp

theorem isEllipticFieldOn_adjointCoeffField {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) := by
  refine ⟨?_, ?_⟩
  · refine (measurable_pi_iff).2 ?_
    intro i
    refine (measurable_pi_iff).2 ?_
    intro j
    simpa [Homogenization.adjointCoeffField, matTranspose] using
      (measurable_pi_iff.mp (measurable_pi_iff.mp hEll.1 j) i)
  · intro x hx
    simpa [Homogenization.adjointCoeffField, matTranspose] using
      isEllipticMatrix_transpose (hEll.2 x hx)

theorem blockMatVecMul_blockCoeffField_pair_of_isUnit_det_symmPart {d : ℕ}
    (a : CoeffField d) (x : Vec d) (hdet : IsUnit (symmPart (a x)).det)
    (ξ η : Vec d) :
    blockMatVecMul (blockCoeffField a x)
        (ξ + η, matVecMul (a x) ξ - matVecMul (matTranspose (a x)) η) =
      (matVecMul (a x) ξ + matVecMul (matTranspose (a x)) η, ξ - η) := by
  have hprimal :=
    blockMatVecMul_blockMatrixOfCoeff_primal_of_isUnit_det_symmPart (a x) hdet ξ
  have hadjoint :=
    blockMatVecMul_blockMatrixOfCoeff_adjoint_of_isUnit_det_symmPart (a x) hdet η
  calc
    blockMatVecMul (blockCoeffField a x)
        (ξ + η, matVecMul (a x) ξ - matVecMul (matTranspose (a x)) η) =
      blockMatVecMul (blockCoeffField a x)
        ((ξ, matVecMul (a x) ξ) + (η, -matVecMul (matTranspose (a x)) η)) := by
          simp [sub_eq_add_neg]
    _ = blockMatVecMul (blockCoeffField a x) (ξ, matVecMul (a x) ξ) +
          blockMatVecMul (blockCoeffField a x) (η, -matVecMul (matTranspose (a x)) η) := by
            rw [blockMatVecMul_add]
    _ = (matVecMul (a x) ξ, ξ) + (matVecMul (matTranspose (a x)) η, -η) := by
          simp [blockCoeffField, hprimal, hadjoint]
    _ = (matVecMul (a x) ξ + matVecMul (matTranspose (a x)) η, ξ - η) := by
          simp [sub_eq_add_neg]

theorem blockMatVecMul_blockCoeffField_pair_of_isEllipticFieldOn {d : ℕ}
    (a : CoeffField d) {lam Lam : ℝ} {U : Set (Vec d)} (hEll : IsEllipticFieldOn lam Lam U a)
    {x : Vec d} (hx : x ∈ U) (ξ η : Vec d) :
    blockMatVecMul (blockCoeffField a x)
        (ξ + η, matVecMul (a x) ξ - matVecMul (matTranspose (a x)) η) =
      (matVecMul (a x) ξ + matVecMul (matTranspose (a x)) η, ξ - η) := by
  exact blockMatVecMul_blockCoeffField_pair_of_isUnit_det_symmPart a x
    (isUnit_det_symmPart_of_isEllipticMatrix (hEll.2 x hx)) ξ η

def pointwiseScalarResponseIntegrand {d : ℕ} (A : Mat d)
    (p q ξ : Vec d) : ℝ :=
  -((1 / 2 : ℝ) * vecDot ξ (matVecMul (symmPart A) ξ))
    - vecDot p (matVecMul A ξ)
    + vecDot q ξ

theorem vecDot_matVecMul_self_eq_symmPart {d : ℕ} (A : Mat d) (ξ : Vec d) :
    vecDot ξ (matVecMul A ξ) = vecDot ξ (matVecMul (symmPart A) ξ) := by
  have htranspose :
      vecDot ξ (matVecMul (matTranspose A) ξ) = vecDot ξ (matVecMul A ξ) := by
    calc
      vecDot ξ (matVecMul (matTranspose A) ξ) = vecDot (matVecMul A ξ) ξ := by
        rw [vecDot_matVecMul_transpose]
      _ = vecDot ξ (matVecMul A ξ) := by
        rw [vecDot_comm]
  rw [symmPart_eq_smul_add_transpose, smul_matVecMul, add_matVecMul, vecDot_smul_right,
    vecDot_add_right, htranspose]
  ring

theorem pointwiseBlockEnergy_pair_eq_symmPart_sum_of_isUnit_det_symmPart {d : ℕ}
    (A : Mat d) (hdet : IsUnit (symmPart A).det) (ξ η : Vec d) :
    (1 / 2 : ℝ) * blockVecDot
        (ξ + η, matVecMul A ξ - matVecMul (matTranspose A) η)
        (blockMatVecMul (blockMatrixOfCoeff A)
          (ξ + η, matVecMul A ξ - matVecMul (matTranspose A) η)) =
      vecDot ξ (matVecMul (symmPart A) ξ) +
        vecDot η (matVecMul (symmPart A) η) := by
  have himage :
      blockMatVecMul (blockMatrixOfCoeff A)
          (ξ + η, matVecMul A ξ - matVecMul (matTranspose A) η) =
        (matVecMul A ξ + matVecMul (matTranspose A) η, ξ - η) := by
    calc
      blockMatVecMul (blockMatrixOfCoeff A)
          (ξ + η, matVecMul A ξ - matVecMul (matTranspose A) η) =
        blockMatVecMul (blockMatrixOfCoeff A)
          ((ξ, matVecMul A ξ) + (η, -matVecMul (matTranspose A) η)) := by
            simp [sub_eq_add_neg]
      _ = blockMatVecMul (blockMatrixOfCoeff A) (ξ, matVecMul A ξ) +
            blockMatVecMul (blockMatrixOfCoeff A) (η, -matVecMul (matTranspose A) η) := by
              rw [blockMatVecMul_add]
      _ = (matVecMul A ξ, ξ) + (matVecMul (matTranspose A) η, -η) := by
            rw [blockMatVecMul_blockMatrixOfCoeff_primal_of_isUnit_det_symmPart A hdet ξ,
              blockMatVecMul_blockMatrixOfCoeff_adjoint_of_isUnit_det_symmPart A hdet η]
      _ = (matVecMul A ξ + matVecMul (matTranspose A) η, ξ - η) := by
            simp [sub_eq_add_neg]
  have hcross :
      vecDot ξ (matVecMul (matTranspose A) η) = vecDot η (matVecMul A ξ) := by
    calc
      vecDot ξ (matVecMul (matTranspose A) η) = vecDot (matVecMul A ξ) η := by
        rw [vecDot_matVecMul_transpose]
      _ = vecDot η (matVecMul A ξ) := by
        rw [vecDot_comm]
  rw [himage]
  have hquadξ : vecDot ξ (matVecMul A ξ) = vecDot ξ (matVecMul (symmPart A) ξ) :=
    vecDot_matVecMul_self_eq_symmPart A ξ
  have hquadη :
      vecDot η (matVecMul (matTranspose A) η) = vecDot η (matVecMul (symmPart A) η) := by
    rw [vecDot_matVecMul_self_eq_symmPart (matTranspose A) η, symmPart_matTranspose]
  have hdiagξ' : vecDot (matVecMul A ξ) ξ = vecDot ξ (matVecMul (symmPart A) ξ) := by
    rw [vecDot_comm, hquadξ]
  have hdiagη' :
      vecDot (matVecMul (matTranspose A) η) η = vecDot η (matVecMul (symmPart A) η) := by
    rw [vecDot_comm, hquadη]
  have hcross_left : vecDot (matVecMul A ξ) η = vecDot η (matVecMul A ξ) := by
    rw [vecDot_comm]
  have hcross_right :
      vecDot (matVecMul (matTranspose A) η) ξ = vecDot η (matVecMul A ξ) := by
    rw [vecDot_comm, hcross]
  have hfirst :
      vecDot (ξ + η) (matVecMul A ξ + matVecMul (matTranspose A) η) =
        vecDot ξ (matVecMul (symmPart A) ξ) +
          2 * vecDot η (matVecMul A ξ) +
          vecDot η (matVecMul (symmPart A) η) := by
    simp [vecDot_add_left, vecDot_add_right, hcross, hquadξ, hquadη]
    ring
  have hlast :
      vecDot (matVecMul A ξ - matVecMul (matTranspose A) η) (ξ - η) =
        vecDot ξ (matVecMul (symmPart A) ξ) +
          vecDot η (matVecMul (symmPart A) η) -
          2 * vecDot η (matVecMul A ξ) := by
    calc
      vecDot (matVecMul A ξ - matVecMul (matTranspose A) η) (ξ - η) =
          vecDot (matVecMul A ξ) ξ - vecDot (matVecMul A ξ) η -
            vecDot (matVecMul (matTranspose A) η) ξ +
            vecDot (matVecMul (matTranspose A) η) η := by
              simp [sub_eq_add_neg, vecDot_add_left, vecDot_add_right, vecDot_neg_left,
                vecDot_neg_right]
              ring
      _ = vecDot ξ (matVecMul (symmPart A) ξ) - vecDot η (matVecMul A ξ) -
            vecDot η (matVecMul A ξ) +
            vecDot η (matVecMul (symmPart A) η) := by
              rw [hdiagξ', hcross_left, hcross_right, hdiagη']
      _ = vecDot ξ (matVecMul (symmPart A) ξ) +
            vecDot η (matVecMul (symmPart A) η) -
            2 * vecDot η (matVecMul A ξ) := by
              ring
  rw [show
      blockVecDot (ξ + η, matVecMul A ξ - matVecMul (matTranspose A) η)
        (matVecMul A ξ + matVecMul (matTranspose A) η, ξ - η) =
        vecDot (ξ + η) (matVecMul A ξ + matVecMul (matTranspose A) η) +
          vecDot (matVecMul A ξ - matVecMul (matTranspose A) η) (ξ - η) by
            rfl]
  rw [hfirst, hlast]
  ring

theorem blockResponse_mem_responseSpace_smul {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {X : BlockState d} (hX : BlockResponseSpace a U X) (c : ℝ) :
    BlockResponseSpace a U (c • X) := by
  rcases hX with ⟨hpot, hsol, horth⟩
  refine ⟨?_, ?_, ?_⟩
  · exact isPotentialOn_smul hpot c
  · exact isSolenoidalOn_smul hsol c
  · intro Y hY
    rw [show
        (fun x =>
          blockVecDot (Y.eval x)
            (blockMatVecMul (blockCoeffField a x) ((c • X).eval x))) =
          fun x =>
            c * blockVecDot (Y.eval x)
              (blockMatVecMul (blockCoeffField a x) (X.eval x)) by
            funext x
            rw [BlockState.eval_smul, blockMatVecMul_smul, blockVecDot_smul_right]]
    rw [MeasureTheory.integral_const_mul, horth Y hY]
    simp

theorem blockResponse_upperImage_orthogonal_of_mem_responseSpace {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    (hX : BlockResponseSpace a U X) {Y : Vec d → Vec d}
    (hY : IsPotentialZeroTraceOn U Y) :
    ∫ x in U, vecDot (Y x) ((blockMatVecMul (blockCoeffField a x) (X.eval x)).1)
        ∂MeasureTheory.volume = 0 := by
  rcases hX with ⟨_, _, horth⟩
  let Z : BlockState d := { potential := Y, flux := 0 }
  have hZ : IsBlockTestOn U Z := by
    refine ⟨hY, ?_⟩
    simpa [Z] using! (isSolenoidalZeroNormalTraceOn_zero (U := U))
  have hzero := horth Z hZ
  have hrewrite :
      ∫ x in U,
          blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))
            ∂MeasureTheory.volume =
        ∫ x in U, vecDot (Y x) ((blockMatVecMul (blockCoeffField a x) (X.eval x)).1)
            ∂MeasureTheory.volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp [Z, BlockState.eval, blockVecDot, vecDot_zero_left]
  rw [hrewrite] at hzero
  exact hzero

theorem blockResponse_lowerImage_orthogonal_of_mem_responseSpace {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    (hX : BlockResponseSpace a U X) {Y : Vec d → Vec d}
    (hY : IsSolenoidalZeroNormalTraceOn U Y) :
    ∫ x in U, vecDot (Y x) ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)
        ∂MeasureTheory.volume = 0 := by
  rcases hX with ⟨_, _, horth⟩
  let Z : BlockState d := { potential := 0, flux := Y }
  have hZ : IsBlockTestOn U Z := by
    refine ⟨?_, hY⟩
    simpa [Z] using! (isPotentialZeroTraceOn_zero (U := U))
  have hzero := horth Z hZ
  have hrewrite :
      ∫ x in U,
          blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))
            ∂MeasureTheory.volume =
        ∫ x in U, vecDot (Y x) ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)
            ∂MeasureTheory.volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp [Z, BlockState.eval, blockVecDot, vecDot_zero_left]
  rw [hrewrite] at hzero
  exact hzero

structure BlockJIntegrabilityData {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (P Q : BlockVec d) : Prop where
  response :
    ∀ X : BlockState d, BlockResponseSpace a U X →
      MeasureTheory.IntegrableOn (blockResponseIntegrand a P Q X) U

structure BlockResponseLowerImageMemVectorL2Data {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) : Prop where
  lowerImage_memVectorL2 :
    ∀ X : BlockState d, BlockResponseSpace a U X →
      MemVectorL2 U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2)

theorem blockResponse_potential_memL2_of_mem_responseSpace {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    (hX : BlockResponseSpace a U X) :
    MemVectorL2 U X.potential := by
  rcases hX.1 with ⟨u, hu⟩
  simpa [hu] using u.grad_memVectorL2

theorem blockResponse_upperImage_isSolenoidalOn_of_mem_responseSpace {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    (hX : BlockResponseSpace a U X) :
    IsSolenoidalOn U (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) := by
  intro φ
  have hzero :=
    blockResponse_upperImage_orthogonal_of_mem_responseSpace
      (hX := hX) (Y := φ.toH1Function.grad) φ.isPotentialZeroTraceOn
  simpa [vecDot_comm] using hzero

theorem blockResponse_lowerImage_isPotential_of_mem_responseSpace_of_memVectorL2_of_hodgeConverseCriterion {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hHodge : HodgeConverseCriterion U)
    (hX : BlockResponseSpace a U X)
    (hLowerL2 :
      MemVectorL2 U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) :
    IsPotentialOn U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
  refine
    IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
      hHodge hLowerL2 ?_
  intro g hg hsol
  exact blockResponse_lowerImage_orthogonal_of_mem_responseSpace (hX := hX) (Y := g) hsol

theorem blockResponse_lowerImage_isPotential_of_mem_responseSpace_of_memVectorL2
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    [HasHodgeConverse U]
    (hX : BlockResponseSpace a U X)
    (hLowerL2 :
      MemVectorL2 U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) :
    IsPotentialOn U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
  exact
    blockResponse_lowerImage_isPotential_of_mem_responseSpace_of_memVectorL2_of_hodgeConverseCriterion
      (U := U)
      (hHodge := HasHodgeConverse.hodgeConverseCriterion (U := U))
      hX hLowerL2

/-- Preferred convex-domain wrapper for promoting the lower image of a response
state to a potential field. This is the Chapter-2-facing surface to use when
the domain is a bounded open convex set. -/
theorem blockResponse_lowerImage_isPotential_of_mem_responseSpace_of_memVectorL2_of_isOpenBoundedConvexDomain
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hX : BlockResponseSpace a U X)
    (hLowerL2 :
      MemVectorL2 U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) :
    IsPotentialOn U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
  exact
    blockResponse_lowerImage_isPotential_of_mem_responseSpace_of_memVectorL2_of_hodgeConverseCriterion
      (U := U)
      (hHodge := hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      hX hLowerL2

theorem blockResponse_memBlockL2_of_mem_responseSpace_of_integrabilityData {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hX : BlockResponseSpace a U X) (hInt : BlockResponseIntegrabilityData U a X) :
    MemBlockL2 U X.eval := by
  simpa [BlockState.eval, blockField] using!
    memBlockL2_blockField
      (blockResponse_potential_memL2_of_mem_responseSpace hX)
      hInt.flux_memL2

end

end Homogenization
