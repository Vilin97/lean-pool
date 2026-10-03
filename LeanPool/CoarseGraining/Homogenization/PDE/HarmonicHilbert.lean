/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientFieldHilbert
public import LeanPool.CoarseGraining.Homogenization.PDE.Harmonic
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Hodge

/-! # Harmonic Hilbert -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Hilbert realization of `A`-harmonic gradients

This file starts the Stage 6 bridge from the response-maximizer direct method
to the concrete `AHarmonicFunction` API.  The closed Hilbert subspace below
models gradients `F` such that `F ∈ Lpot(U)` and `a F ∈ Lsol(U)`.
-/

namespace AHarmonicGradientHilbert

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
variable {M : PotentialSolenoidalL2Data U} {hEll : IsEllipticFieldOn lam Lam U a}

private theorem vecDot_matVecMul_symmPart_comm_local (A : Mat d) (ξ η : Vec d) :
    vecDot ξ (matVecMul (symmPart A) η) = vecDot η (matVecMul (symmPart A) ξ) := by
  calc
    vecDot ξ (matVecMul (symmPart A) η)
        = vecDot ξ (matVecMul (matTranspose (symmPart A)) η) := by
            simp
    _ = vecDot (matVecMul (symmPart A) ξ) η := by
          rw [vecDot_matVecMul_transpose]
    _ = vecDot η (matVecMul (symmPart A) ξ) := by
          rw [vecDot_comm]

/-- The closed Hilbert subspace of vector `L²` fields whose plain representative
lies in the packaged potential space and whose coefficient-weighted
representative lies in the packaged solenoidal space. -/
noncomputable def closedSubmodule (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) : ClosedSubmodule ℝ (HilbertVectorL2 U) :=
  (M.potential.comap (hilbertVectorL2ToVectorL2 (U := U))) ⊓
    (M.solenoidal.comap
      ((hilbertVectorL2ToVectorL2 (U := U)).comp (hilbertCoeffOperator hEll)))

/-- The Hilbert carrier for `A`-harmonic gradients. -/
noncomputable abbrev Space (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) :=
  (closedSubmodule (U := U) (a := a) M hEll).toSubmodule

noncomputable instance instSeminormedAddCommGroup (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    SeminormedAddCommGroup (Space (U := U) (a := a) M hEll) :=
  inferInstanceAs
    (SeminormedAddCommGroup ((closedSubmodule (U := U) (a := a) M hEll).toSubmodule))

noncomputable instance instNormedAddCommGroup (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    NormedAddCommGroup (Space (U := U) (a := a) M hEll) :=
  inferInstanceAs
    (NormedAddCommGroup ((closedSubmodule (U := U) (a := a) M hEll).toSubmodule))

noncomputable instance instNormedSpace (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    NormedSpace ℝ (Space (U := U) (a := a) M hEll) :=
  inferInstanceAs
    (NormedSpace ℝ ((closedSubmodule (U := U) (a := a) M hEll).toSubmodule))

noncomputable instance instInnerProductSpace (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    InnerProductSpace ℝ (Space (U := U) (a := a) M hEll) :=
  inferInstanceAs
    (InnerProductSpace ℝ ((closedSubmodule (U := U) (a := a) M hEll).toSubmodule))

noncomputable instance instCompleteSpace (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    CompleteSpace (Space (U := U) (a := a) M hEll) := by
  simpa [Space, closedSubmodule] using!
    (closedSubmodule (U := U) (a := a) M hEll).isClosed.completeSpace_coe

/-- The ambient Hilbert-vector `L²` field represented by a harmonic-gradient
Hilbert element. -/
abbrev field {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z : Space (U := U) (a := a) M hEll) : HilbertVectorL2 U :=
  z

/-- The plain vector-valued `L²` representative of a harmonic-gradient Hilbert
element. -/
noncomputable abbrev vectorField {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z : Space (U := U) (a := a) M hEll) : VectorL2 U :=
  hilbertVectorL2ToVectorL2 (U := U) (field z)

/-- The coefficient-weighted Hilbert-vector `L²` field associated to a
harmonic-gradient Hilbert element. -/
noncomputable abbrev coeffField {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z : Space (U := U) (a := a) M hEll) : HilbertVectorL2 U :=
  hilbertCoeffOperator hEll (field z)

/-- The plain vector-valued representative of the coefficient-weighted field. -/
noncomputable abbrev coeffVectorField {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z : Space (U := U) (a := a) M hEll) : VectorL2 U :=
  hilbertVectorL2ToVectorL2 (U := U) (coeffField z)

theorem mem_potential {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z : Space (U := U) (a := a) M hEll) :
    vectorField z ∈ M.potential := by
  have hz := z.2
  change (z : HilbertVectorL2 U) ∈
    (M.potential.comap (hilbertVectorL2ToVectorL2 (U := U))) ⊓
      (M.solenoidal.comap
        ((hilbertVectorL2ToVectorL2 (U := U)).comp (hilbertCoeffOperator hEll))) at hz
  exact (ClosedSubmodule.mem_comap).1 (ClosedSubmodule.mem_inf.mp hz).1

theorem mem_solenoidal {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z : Space (U := U) (a := a) M hEll) :
    coeffVectorField z ∈ M.solenoidal := by
  have hz := z.2
  change (z : HilbertVectorL2 U) ∈
    (M.potential.comap (hilbertVectorL2ToVectorL2 (U := U))) ⊓
      (M.solenoidal.comap
        ((hilbertVectorL2ToVectorL2 (U := U)).comp (hilbertCoeffOperator hEll))) at hz
  exact (ClosedSubmodule.mem_comap).1 (ClosedSubmodule.mem_inf.mp hz).2

/-- A concrete `A`-harmonic function determines an element of the closed
Hilbert realization of `A`-harmonic gradients. -/
noncomputable def ofAHarmonicFunction (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) (u : AHarmonicFunction a U) :
    Space (U := U) (a := a) M hEll := by
  refine ⟨u.toH1.gradToHilbertVectorL2, ?_⟩
  change u.toH1.gradToHilbertVectorL2 ∈
    (closedSubmodule (U := U) (a := a) M hEll)
  change u.toH1.gradToHilbertVectorL2 ∈
    (M.potential.comap (hilbertVectorL2ToVectorL2 (U := U))) ⊓
      (M.solenoidal.comap
        ((hilbertVectorL2ToVectorL2 (U := U)).comp (hilbertCoeffOperator hEll)))
  rw [ClosedSubmodule.mem_inf]
  constructor
  · rw [ClosedSubmodule.mem_comap]
    simpa [H1Function.gradToHilbertVectorL2, H1Function.gradToVectorL2] using!
      M.mem_potential u.toH1.grad_memVectorL2 u.isHarmonic.1
  · rw [ClosedSubmodule.mem_comap]
    let hcoeff :
        MemVectorL2 U (fun x => matVecMul (a x) (u.toH1.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
    have hfield :
        hilbertVectorL2ToVectorL2 (U := U)
            (hilbertCoeffOperator hEll u.toH1.gradToHilbertVectorL2) =
          toVectorL2 hcoeff := by
      change hilbertVectorL2ToVectorL2 (U := U)
          (hilbertCoeffOperator hEll (toHilbertVectorL2OfVecField u.toH1.grad_memVectorL2)) =
        toVectorL2 hcoeff
      rw [hilbertCoeffOperator_toHilbertVectorL2OfVecField hEll u.toH1.grad_memVectorL2]
      exact hilbertVectorL2ToVectorL2_toHilbertVectorL2 (U := U) hcoeff
    change
      hilbertVectorL2ToVectorL2 (U := U)
          (hilbertCoeffOperator hEll u.toH1.gradToHilbertVectorL2) ∈
        M.solenoidal
    rw [hfield]
    exact M.mem_solenoidal hcoeff u.isHarmonic.2

@[simp] theorem field_ofAHarmonicFunction (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) (u : AHarmonicFunction a U) :
    field (ofAHarmonicFunction (U := U) (a := a) M hEll u) =
      u.toH1.gradToHilbertVectorL2 :=
  rfl

@[simp] theorem vectorField_ofAHarmonicFunction (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) (u : AHarmonicFunction a U) :
    vectorField (ofAHarmonicFunction (U := U) (a := a) M hEll u) =
      u.toH1.gradToVectorL2 := by
  change hilbertVectorL2ToVectorL2 (U := U) u.toH1.gradToHilbertVectorL2 =
    u.toH1.gradToVectorL2
  simpa [H1Function.gradToHilbertVectorL2, H1Function.gradToVectorL2] using
    hilbertVectorL2ToVectorL2_toHilbertVectorL2 (U := U) u.toH1.grad_memVectorL2

/-- The inclusion of the closed harmonic-gradient space into ambient
Hilbert-vector `L²`. -/
noncomputable def fieldCLM (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Space (U := U) (a := a) M hEll →L[ℝ] HilbertVectorL2 U :=
  (closedSubmodule (U := U) (a := a) M hEll).toSubmodule.subtypeL

@[simp] theorem fieldCLM_apply (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (z : Space (U := U) (a := a) M hEll) :
    fieldCLM (U := U) (a := a) M hEll z = field z :=
  rfl

theorem field_eq_toHilbertVectorL2OfVecField {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z : Space (U := U) (a := a) M hEll) :
    field z =
      toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField z)) := by
  calc
    field z = vectorL2ToHilbertVectorL2 (U := U) (vectorField z) := by
      symm
      exact vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 (U := U) (field z)
    _ =
        vectorL2ToHilbertVectorL2 (U := U)
          (toVectorL2 (MeasureTheory.Lp.memLp (vectorField z))) := by
            congr 1
            exact
              (MeasureTheory.Lp.toLp_coeFn
                (vectorField z)
                (MeasureTheory.Lp.memLp (vectorField z))).symm
    _ = toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField z)) := by
          rfl

/-- The symmetric coefficient-weighted field associated to a harmonic-gradient
Hilbert element. -/
noncomputable abbrev symmCoeffField {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z : Space (U := U) (a := a) M hEll) : HilbertVectorL2 U :=
  hilbertSymmCoeffOperator hEll (field z)

/-- The continuous symmetric-coefficient field map on the closed
harmonic-gradient space. -/
noncomputable def symmCoeffFieldCLM (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Space (U := U) (a := a) M hEll →L[ℝ] HilbertVectorL2 U :=
  (hilbertSymmCoeffOperator hEll).comp (fieldCLM (U := U) (a := a) M hEll)

/-- The symmetric energy bilinear form on the closed `A`-harmonic-gradient
Hilbert space. -/
noncomputable def symmCoeffBilin (M : PotentialSolenoidalL2Data U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Space (U := U) (a := a) M hEll →L[ℝ]
      Space (U := U) (a := a) M hEll →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (symmCoeffFieldCLM (U := U) (a := a) M hEll)
    (fieldCLM (U := U) (a := a) M hEll)

@[simp] theorem symmCoeffBilin_apply {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z w : Space (U := U) (a := a) M hEll) :
    symmCoeffBilin (U := U) (a := a) M hEll z w =
      inner ℝ (hilbertSymmCoeffOperator hEll (field z)) (field w) := by
  simp [symmCoeffBilin, symmCoeffFieldCLM, ContinuousLinearMap.bilinearComp_apply, field]

theorem symmCoeffBilin_apply_eq_integral {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z w : Space (U := U) (a := a) M hEll) :
    symmCoeffBilin (U := U) (a := a) M hEll z w =
      ∫ x in U,
        vecDot (matVecMul (symmPart (a x)) (vectorField z x)) (vectorField w x)
          ∂MeasureTheory.volume := by
  have hzField :
      field z = toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField z)) :=
    field_eq_toHilbertVectorL2OfVecField z
  have hwField :
      field w = toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField w)) :=
    field_eq_toHilbertVectorL2OfVecField w
  have hA :
      hilbertSymmCoeffOperator hEll (field z) =
        toHilbertVectorL2OfVecField
          (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll
            (MeasureTheory.Lp.memLp (vectorField z))) := by
    rw [hzField]
    exact
      hilbertSymmCoeffOperator_toHilbertVectorL2OfVecField
        (U := U) (a := a) (lam := lam) (Lam := Lam) hEll
        (MeasureTheory.Lp.memLp (vectorField z))
  calc
    symmCoeffBilin (U := U) (a := a) M hEll z w
        = inner ℝ (hilbertSymmCoeffOperator hEll (field z)) (field w) := by
            simp [symmCoeffBilin_apply]
    _ =
        inner ℝ
          (toHilbertVectorL2OfVecField
            (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll
              (MeasureTheory.Lp.memLp (vectorField z))))
          (toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField w))) := by
            rw [hA, hwField]
    _ =
        ∫ x in U,
          vecDot (matVecMul (symmPart (a x)) (vectorField z x)) (vectorField w x)
            ∂MeasureTheory.volume := by
              exact inner_toHilbertVectorL2OfVecField_eq_integral
                (U := U)
                (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll
                  (MeasureTheory.Lp.memLp (vectorField z)))
                (MeasureTheory.Lp.memLp (vectorField w))

theorem symmCoeffBilin_apply_eq_integral_comm {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z w : Space (U := U) (a := a) M hEll) :
    symmCoeffBilin (U := U) (a := a) M hEll z w =
      ∫ x in U,
        vecDot (vectorField w x) (matVecMul (symmPart (a x)) (vectorField z x))
          ∂MeasureTheory.volume := by
  rw [symmCoeffBilin_apply_eq_integral]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [] with x
  exact vecDot_comm _ _

theorem symmCoeffBilin_symm {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z w : Space (U := U) (a := a) M hEll) :
    symmCoeffBilin (U := U) (a := a) M hEll z w =
      symmCoeffBilin (U := U) (a := a) M hEll w z := by
  rw [symmCoeffBilin_apply_eq_integral_comm, symmCoeffBilin_apply_eq_integral_comm]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [] with x
  exact vecDot_matVecMul_symmPart_comm_local (a x) (vectorField w x) (vectorField z x)

theorem symmCoeffBilin_self_ge_lam_mul_norm_sq {M : PotentialSolenoidalL2Data U}
    {hEll : IsEllipticFieldOn lam Lam U a}
    (z : Space (U := U) (a := a) M hEll) :
    lam * ‖z‖ ^ 2 ≤ symmCoeffBilin (U := U) (a := a) M hEll z z := by
  have hsqInt :
      MeasureTheory.IntegrableOn
        (fun x => vecNormSq (vectorField z x)) U := by
    simpa [vecNormSq] using
      (integrableOn_vecDot_of_memVectorL2
        (MeasureTheory.Lp.memLp (vectorField z))
        (MeasureTheory.Lp.memLp (vectorField z)))
  have henergyInt :
      MeasureTheory.IntegrableOn
        (fun x =>
          vecDot (matVecMul (symmPart (a x)) (vectorField z x)) (vectorField z x)) U := by
    exact
      integrableOn_vecDot_of_memVectorL2
        (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll
          (MeasureTheory.Lp.memLp (vectorField z)))
        (MeasureTheory.Lp.memLp (vectorField z))
  have hmem :
      ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  have hpoint :
      ∀ᵐ x ∂ volumeMeasureOn U,
        lam * vecNormSq (vectorField z x) ≤
          vecDot (matVecMul (symmPart (a x)) (vectorField z x)) (vectorField z x) := by
    filter_upwards [hmem] with x hx
    simpa [vecDot_comm] using
      lowerBound_symmPart_of_isEllipticMatrix (hEll.2 x hx) (vectorField z x)
  have hnormSq :
      ‖z‖ ^ 2 =
        ∫ x in U, vecNormSq (vectorField z x) ∂MeasureTheory.volume := by
    calc
      ‖z‖ ^ 2 = inner ℝ (field z) (field z) := by
            simp [field]
      _ =
          inner ℝ
            (toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField z)))
            (toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField z))) := by
              rw [field_eq_toHilbertVectorL2OfVecField z]
      _ =
          ∫ x in U, vecDot (vectorField z x) (vectorField z x) ∂MeasureTheory.volume := by
            exact inner_toHilbertVectorL2OfVecField_eq_integral
              (U := U)
              (MeasureTheory.Lp.memLp (vectorField z))
              (MeasureTheory.Lp.memLp (vectorField z))
      _ = ∫ x in U, vecNormSq (vectorField z x) ∂MeasureTheory.volume := by
            simp [vecNormSq]
  calc
    lam * ‖z‖ ^ 2
        = lam * ∫ x in U, vecNormSq (vectorField z x) ∂MeasureTheory.volume := by
            rw [hnormSq]
    _ = ∫ x in U, lam * vecNormSq (vectorField z x) ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_const_mul]
    _ ≤
        ∫ x in U,
          vecDot (matVecMul (symmPart (a x)) (vectorField z x)) (vectorField z x)
            ∂MeasureTheory.volume :=
      MeasureTheory.integral_mono_ae (hsqInt.const_mul lam) henergyInt hpoint
    _ = symmCoeffBilin (U := U) (a := a) M hEll z z := by
          symm
          exact symmCoeffBilin_apply_eq_integral (U := U) (a := a) z z

theorem isCoercive_symmCoeffBilin {M : PotentialSolenoidalL2Data U}
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a) :
    IsCoercive (symmCoeffBilin (U := U) (a := a) M hEll) := by
  rcases hne with ⟨x, hx⟩
  refine ⟨lam, (hEll.2 x hx).1, ?_⟩
  intro z
  simpa [pow_two, mul_assoc] using
    symmCoeffBilin_self_ge_lam_mul_norm_sq (U := U) (a := a) (M := M) z

noncomputable def vectorPairingCLM [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) :
    VectorL2 U →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (HilbertVectorL2 U) (toHilbertVectorL2OfVecField hg)).comp
    ((continuousLinearEquivVectorL2 (U := U)).toContinuousLinearMap)

theorem vectorPairingCLM_apply_eq_integral
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) (F : VectorL2 U) :
    vectorPairingCLM (U := U) hg F =
      ∫ x in U, vecDot (g x) (F x) ∂MeasureTheory.volume := by
  have hF :
      (continuousLinearEquivVectorL2 (U := U)) F =
        toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp F) := by
    calc
      (continuousLinearEquivVectorL2 (U := U)) F
          = vectorL2ToHilbertVectorL2 (U := U) F := by
              rfl
      _ =
          vectorL2ToHilbertVectorL2 (U := U)
            (toVectorL2 (MeasureTheory.Lp.memLp F)) := by
              congr 1
              exact (MeasureTheory.Lp.toLp_coeFn F (MeasureTheory.Lp.memLp F)).symm
      _ = toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp F) := by
            rfl
  calc
    vectorPairingCLM (U := U) hg F
        = inner ℝ
            (toHilbertVectorL2OfVecField hg)
            ((continuousLinearEquivVectorL2 (U := U)) F) := by
              simp [vectorPairingCLM]
    _ =
        inner ℝ
          (toHilbertVectorL2OfVecField hg)
          (toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp F)) := by
            rw [hF]
    _ = ∫ x in U, vecDot (g x) (F x) ∂MeasureTheory.volume := by
          exact inner_toHilbertVectorL2OfVecField_eq_integral
            (U := U) hg (MeasureTheory.Lp.memLp F)

theorem integral_vecDot_eq_zero_of_mem_potential_closure
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (F : VectorL2 U)
    (hF : F ∈ (PotentialSolenoidalL2Data.ofSubmoduleClosures U).potential)
    {g : Vec d → Vec d} (hg : MemVectorL2 U g)
    (hsol : IsSolenoidalZeroNormalTraceOn U g) :
    ∫ x in U, vecDot (g x) (F x) ∂MeasureTheory.volume = 0 := by
  let ℓ : VectorL2 U →L[ℝ] ℝ := vectorPairingCLM (U := U) hg
  have hKClosed : IsClosed ((LinearMap.ker ℓ.toLinearMap : Submodule ℝ (VectorL2 U)) :
      Set (VectorL2 U)) := by
    simpa [LinearMap.mem_ker] using!
      isClosed_singleton.preimage (ContinuousLinearMap.continuous ℓ)
  let K : ClosedSubmodule ℝ (VectorL2 U) :=
    ⟨LinearMap.ker ℓ.toLinearMap, hKClosed⟩
  have hsub :
      PotentialSolenoidalL2Data.potentialSubmodule U ≤ LinearMap.ker ℓ.toLinearMap := by
    intro X hX
    rcases hX with ⟨f, hf, rfl, hpot⟩
    change ℓ (toVectorL2 hf) = 0
    rcases hpot with ⟨u, hu⟩
    have hpair :
        ∫ x in U, vecDot (g x) ((toVectorL2 hf) x) ∂MeasureTheory.volume =
          ∫ x in U, vecDot (g x) (f x) ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [coeFn_toVectorL2 hf] with x hx
      rw [hx]
    calc
      ℓ (toVectorL2 hf) =
          ∫ x in U, vecDot (g x) ((toVectorL2 hf) x) ∂MeasureTheory.volume :=
        vectorPairingCLM_apply_eq_integral (U := U) hg (toVectorL2 hf)
      _ = ∫ x in U, vecDot (g x) (f x) ∂MeasureTheory.volume := hpair
      _ = 0 := by simpa [hu] using hsol u
  have hclosure :
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U).potential ≤
        LinearMap.ker ℓ.toLinearMap := by
    exact (Submodule.closure_le (s := PotentialSolenoidalL2Data.potentialSubmodule U)
      (t := K)).2 hsub
  have hkerF : F ∈ LinearMap.ker ℓ.toLinearMap := hclosure hF
  have hzero : ℓ F = 0 := by
    exact hkerF
  calc
    ∫ x in U, vecDot (g x) (F x) ∂MeasureTheory.volume = ℓ F := by
      symm
      exact vectorPairingCLM_apply_eq_integral (U := U) hg F
    _ = 0 := hzero

theorem integral_vecDot_eq_zero_of_mem_solenoidal_closure
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (G : VectorL2 U)
    (hG : G ∈ (PotentialSolenoidalL2Data.ofSubmoduleClosures U).solenoidal)
    (φ : H10Function U) :
    ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) ∂MeasureTheory.volume = 0 := by
  exact
    PotentialSolenoidalL2Data.isSolenoidalOn_of_mem_solenoidal_ofSubmoduleClosures
      (U := U) G hG φ

theorem isPotentialOn_vectorField_of_hodgeConverseCriterion
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hHodge : HodgeConverseCriterion U)
    (z : Space (U := U) (a := a) (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hEll) :
    IsPotentialOn U (vectorField z) :=
  hHodge (MeasureTheory.Lp.memLp (vectorField z)) fun hg hsol =>
    integral_vecDot_eq_zero_of_mem_potential_closure
      (U := U) (vectorField z) (mem_potential z) hg hsol

theorem isSolenoidalOn_coeffVectorField
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (z : Space (U := U) (a := a) (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hEll) :
    IsSolenoidalOn U (coeffVectorField z) := by
  intro φ
  exact integral_vecDot_eq_zero_of_mem_solenoidal_closure
    (U := U) (coeffVectorField z) (mem_solenoidal z) φ

theorem ae_coeffVectorField_eq_matVecMul_vectorField
    (z : Space (U := U) (a := a) M hEll) :
    coeffVectorField z =ᵐ[volumeMeasureOn U]
      fun x => matVecMul (a x) (vectorField z x) := by
  filter_upwards
      [coeFn_hilbertVectorL2ToVectorL2 (U := U) (f := coeffField z),
       ae_hilbertCoeffOperator_apply hEll (field z),
       coeFn_hilbertVectorL2ToVectorL2 (U := U) (f := field z)]
    with x hcoeffVec hcoeff hvec
  rw [hcoeffVec, hcoeff, hvec]
  simp [HilbertVec.applyMat_apply]

theorem isSolenoidalOn_matVecMul_vectorField
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (z : Space (U := U) (a := a) (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hEll) :
    IsSolenoidalOn U (fun x => matVecMul (a x) (vectorField z x)) := by
  intro φ
  calc
    ∫ x in U, vecDot (matVecMul (a x) (vectorField z x)) (φ.toH1Function.grad x)
        ∂MeasureTheory.volume =
        ∫ x in U, vecDot (coeffVectorField z x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [ae_coeffVectorField_eq_matVecMul_vectorField (z := z)] with x hx
          rw [hx]
    _ = 0 := isSolenoidalOn_coeffVectorField (U := U) (a := a) z φ

theorem isAHarmonicGradient_vectorField_of_hodgeConverseCriterion
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hHodge : HodgeConverseCriterion U)
    (z : Space (U := U) (a := a) (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hEll) :
    IsAHarmonicGradient a U (vectorField z) :=
  ⟨isPotentialOn_vectorField_of_hodgeConverseCriterion (U := U) (a := a) hHodge z,
    isSolenoidalOn_matVecMul_vectorField (U := U) (a := a) z⟩

/-- Recover a concrete `AHarmonicFunction` from a Hilbert element in the closed
`A`-harmonic gradient space, using the Hodge converse to recover the potential
representative. -/
noncomputable def toAHarmonicFunction
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hHodge : HodgeConverseCriterion U)
    (z : Space (U := U) (a := a) (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hEll) :
    AHarmonicFunction a U := by
  let hpot : IsPotentialOn U (vectorField z) :=
    isPotentialOn_vectorField_of_hodgeConverseCriterion (U := U) (a := a) hHodge z
  let u : H1Function U := Classical.choose hpot
  have hu : u.grad = vectorField z := Classical.choose_spec hpot
  exact
    { toH1 := u
      isHarmonic := by
        simpa [u, hu] using
          isAHarmonicGradient_vectorField_of_hodgeConverseCriterion
            (U := U) (a := a) hHodge z }

@[simp] theorem grad_toAHarmonicFunction
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hHodge : HodgeConverseCriterion U)
    (z : Space (U := U) (a := a) (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hEll) :
    (toAHarmonicFunction (U := U) (a := a) hHodge z).toH1.grad = vectorField z := by
  unfold toAHarmonicFunction
  exact Classical.choose_spec
    (isPotentialOn_vectorField_of_hodgeConverseCriterion (U := U) (a := a) hHodge z)

end AHarmonicGradientHilbert

end

end Homogenization
