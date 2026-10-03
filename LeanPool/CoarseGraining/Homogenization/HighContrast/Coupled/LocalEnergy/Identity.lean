/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.LocalEnergy.Integrability
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.LocalEnergy.Pointwise
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.Representation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Recovery

/-!
# Local block energy: the test identity

Testing the coupled weak form `CoupledWeakForm` at the smooth pair
`(η²u, η²u*)` and expanding both sides gives the paper's
`e.local.block.test.identity`:

`𝓔 := ∫_U η²(V·sV + V*·sV*)
    = ∫_U η²(q − ½ap)·V − ½∫_U η²(aᵀp)·V*
      + ∫_U u(q − a∇v)·∇(η²) − ∫_U u*(aᵀ∇v*)·∇(η²)`,

where `V = ∇v − ½p`, `V* = ∇v* − ½p`, `u = v − ½p·x − c`, `u* = v* − ½p·x + c`.

The engine is a single *pointwise* algebraic identity
(`pointwise_energy_test_identity`) that rewrites the energy density as the sum
of the bulk density, the cutoff density and the weak-form defect
`(a∇v·∇φ + aᵀ∇v*·∇φ*) − q·∇φ`; integrating and cancelling the defect via the
weak form yields the identity.  No `EuclideanSpace`.
-/

@[expose] public section

namespace Homogenization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The pointwise test-identity density -/

/-- Pointwise algebraic identity underlying `e.local.block.test.identity`.
With `V = gv − ½p`, `V* = gvs − ½p` the energy density equals the bulk density
plus the cutoff density plus the weak-form defect. -/
theorem pointwise_energy_test_identity (A : Mat d) (gv gvs p q gS : Vec d)
    (η2 uu uus : ℝ) :
    η2 * (vecDot (gv - (1/2:ℝ)•p) (matVecMul (symmPart A) (gv - (1/2:ℝ)•p))
        + vecDot (gvs - (1/2:ℝ)•p) (matVecMul (symmPart A) (gvs - (1/2:ℝ)•p)))
      = (η2 * (vecDot (q - (1/2:ℝ)•matVecMul A p) (gv - (1/2:ℝ)•p)
            - (1/2:ℝ) * vecDot (matVecMul (matTranspose A) p) (gvs - (1/2:ℝ)•p)))
        + (uu * vecDot (q - matVecMul A gv) gS
            - uus * vecDot (matVecMul (matTranspose A) gvs) gS)
        + (vecDot (η2•(gv - (1/2:ℝ)•p) + uu•gS) (matVecMul A gv)
            + vecDot (η2•(gvs - (1/2:ℝ)•p) + uus•gS) (matVecMul (matTranspose A) gvs)
            - vecDot q (η2•(gv - (1/2:ℝ)•p) + uu•gS)) := by
  rw [← vecDot_matVecMul_eq_symmPart A (gv - (1/2:ℝ)•p)]
  rw [show vecDot (gvs - (1/2:ℝ)•p) (matVecMul (symmPart A) (gvs - (1/2:ℝ)•p))
        = vecDot (gvs - (1/2:ℝ)•p) (matVecMul (matTranspose A) (gvs - (1/2:ℝ)•p)) from by
      rw [← symmPart_matTranspose A]
      exact (vecDot_matVecMul_eq_symmPart (matTranspose A) _).symm]
  have hfluxV : matVecMul A gv
      = matVecMul A (gv - (1/2:ℝ)•p) + (1/2:ℝ)•matVecMul A p := by
    rw [← matVecMul_smul, ← matVecMul_add]; congr 1; abel
  have hfluxVs : matVecMul (matTranspose A) gvs
      = matVecMul (matTranspose A) (gvs - (1/2:ℝ)•p)
        + (1/2:ℝ)•matVecMul (matTranspose A) p := by
    rw [← matVecMul_smul, ← matVecMul_add]; congr 1; abel
  rw [hfluxV, hfluxVs]
  set V := gv - (1/2:ℝ)•p with hVdef
  set Vstar := gvs - (1/2:ℝ)•p with hVsdef
  simp only [sub_eq_add_neg, vecDot_add_left, vecDot_add_right,
    vecDot_smul_left, vecDot_smul_right, vecDot_neg_left]
  rw [vecDot_comm (matVecMul A p) V, vecDot_comm (matVecMul (matTranspose A) p) Vstar,
    vecDot_comm (matVecMul A V) gS, vecDot_comm (matVecMul A p) gS,
    vecDot_comm (matVecMul (matTranspose A) Vstar) gS,
    vecDot_comm (matVecMul (matTranspose A) p) gS]
  ring

section Integral

variable [NeZero d] {m : ℤ}

local notation "U" => openCubeSet (originCube d m)

/-- The energy density `η²(V·sV + V*·sV*)` with `V = ∇v − ½p`, `s = symmPart a`. -/
def energyIntegrand (a : CoeffField d) (v vstar : H1Function U) (P : BlockVec d)
    (η : Vec d → ℝ) : Vec d → ℝ := fun x =>
  sqCutoff η x
    * (vecDot (v.grad x - (1/2:ℝ)•P.1) (matVecMul (symmPart (a x)) (v.grad x - (1/2:ℝ)•P.1))
      + vecDot (vstar.grad x - (1/2:ℝ)•P.1)
          (matVecMul (symmPart (a x)) (vstar.grad x - (1/2:ℝ)•P.1)))

/-- The bulk density `η²((q − ½ap)·V − ½(aᵀp)·V*)`. -/
def bulkIntegrand (a : CoeffField d) (v vstar : H1Function U) (P : BlockVec d)
    (η : Vec d → ℝ) : Vec d → ℝ := fun x =>
  sqCutoff η x
    * (vecDot (P.2 - (1/2:ℝ)•matVecMul (a x) P.1) (v.grad x - (1/2:ℝ)•P.1)
      - (1/2:ℝ) * vecDot (matVecMul (matTranspose (a x)) P.1) (vstar.grad x - (1/2:ℝ)•P.1))

/-- The cutoff density `u(q − a∇v)·∇(η²) − u*(aᵀ∇v*)·∇(η²)`. -/
def cutoffIntegrand (a : CoeffField d) (v vstar : H1Function U) (P : BlockVec d)
    (c : ℝ) (η : Vec d → ℝ) : Vec d → ℝ := fun x =>
  (centeredPotential m v P.1 c).toFun x
      * vecDot (P.2 - matVecMul (a x) (v.grad x))
          (fun i => fderiv ℝ (sqCutoff η) x (basisVec i))
    - (centeredPotential m vstar P.1 (-c)).toFun x
      * vecDot (matVecMul (matTranspose (a x)) (vstar.grad x))
          (fun i => fderiv ℝ (sqCutoff η) x (basisVec i))

/-! ## Integrability of the four densities -/

section Integrability

omit [NeZero d] in
/-- `L∞` control of `η²`. -/
theorem memLpTop_sqCutoff_cube {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (sqCutoff η) (⊤ : ENNReal) (volumeMeasureOn (openCubeSet (originCube d m))) :=
  sqCutoff_memLpTop hη hIcc

omit [NeZero d] in
/-- `L∞` control of `∂ᵢ(η²)`. -/
theorem memLpTop_fderiv_sqCutoff_cube {η : Vec d → ℝ} {Gη : ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη) (i : Fin d) :
    MemLp (fun x => fderiv ℝ (sqCutoff η) x (basisVec i)) (⊤ : ENNReal)
      (volumeMeasureOn (openCubeSet (originCube d m))) :=
  sqCutoff_fderiv_memLpTop hη hIcc hGη i

omit [NeZero d] in
/-- `V = ∇v − ½p ∈ L²`. -/
theorem memVectorL2_centeredGrad (v : H1Function U) (P : BlockVec d) :
    MemVectorL2 U (fun x => v.grad x - (1/2:ℝ)•P.1) := by
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  exact v.grad_memVectorL2.sub (memVectorL2_const ((1/2:ℝ)•P.1))

omit [NeZero d] in
theorem integrableOn_energyIntegrand {a : CoeffField d} {Θ : ℝ}
    {v vstar : H1Function U} {P : BlockVec d} {η : Vec d → ℝ}
    (hEllO : IsEllipticFieldOn 1 Θ U a)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) :
    IntegrableOn (energyIntegrand a v vstar P η) U := by
  have hE : energyIntegrand a v vstar P η
      = fun x => sqCutoff η x
          * vecDot (v.grad x - (1/2:ℝ)•P.1)
              (matVecMul (symmPart (a x)) (v.grad x - (1/2:ℝ)•P.1))
        + sqCutoff η x
          * vecDot (vstar.grad x - (1/2:ℝ)•P.1)
              (matVecMul (symmPart (a x)) (vstar.grad x - (1/2:ℝ)•P.1)) := by
    funext x; simp only [energyIntegrand]; ring
  rw [hE]
  refine (integrableOn_memLpTop_mul_vecDot (memLpTop_sqCutoff_cube hη hIcc)
      (memVectorL2_centeredGrad v P)
      (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEllO
        (memVectorL2_centeredGrad v P))).add ?_
  exact integrableOn_memLpTop_mul_vecDot (memLpTop_sqCutoff_cube hη hIcc)
    (memVectorL2_centeredGrad vstar P)
    (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEllO
      (memVectorL2_centeredGrad vstar P))

omit [NeZero d] in
theorem integrableOn_bulkIntegrand {a : CoeffField d} {Θ : ℝ}
    {v vstar : H1Function U} {P : BlockVec d} {η : Vec d → ℝ}
    (hEllO : IsEllipticFieldOn 1 Θ U a)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) :
    IntegrableOn (bulkIntegrand a v vstar P η) U := by
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  have hE : bulkIntegrand a v vstar P η
      = fun x => sqCutoff η x
          * vecDot (P.2 - (1/2:ℝ)•matVecMul (a x) P.1) (v.grad x - (1/2:ℝ)•P.1)
        - sqCutoff η x
          * vecDot ((1/2:ℝ)•matVecMul (matTranspose (a x)) P.1) (vstar.grad x - (1/2:ℝ)•P.1) := by
    funext x; simp only [bulkIntegrand, vecDot_smul_left]; ring
  rw [hE]
  have hF1 : MemVectorL2 U (fun x => P.2 - (1/2:ℝ)•matVecMul (a x) P.1) := by
    have h2 : MemVectorL2 U (fun x => (1/2:ℝ)•matVecMul (a x) P.1) := by
      simpa using!
        (memVectorL2_matVecMul_of_isEllipticFieldOn hEllO (memVectorL2_const P.1)).const_smul (1/2:ℝ)
    simpa using! (memVectorL2_const P.2).sub h2
  have hF2 : MemVectorL2 U (fun x => (1/2:ℝ)•matVecMul (matTranspose (a x)) P.1) := by
    have hEllAdj : IsEllipticFieldOn 1 Θ U (Homogenization.adjointCoeffField a) :=
      isEllipticFieldOn_adjointCoeffField hEllO
    have hb : MemVectorL2 U (fun x => matVecMul (matTranspose (a x)) P.1) := by
      simpa [Homogenization.adjointCoeffField] using
        memVectorL2_matVecMul_of_isEllipticFieldOn hEllAdj (memVectorL2_const P.1)
    simpa using! hb.const_smul (1/2:ℝ)
  refine (integrableOn_memLpTop_mul_vecDot (memLpTop_sqCutoff_cube hη hIcc) hF1
      (memVectorL2_centeredGrad v P)).sub ?_
  exact integrableOn_memLpTop_mul_vecDot (memLpTop_sqCutoff_cube hη hIcc) hF2
    (memVectorL2_centeredGrad vstar P)

omit [NeZero d] in
theorem integrableOn_cutoffIntegrand {a : CoeffField d} {Θ : ℝ}
    {v vstar : H1Function U} {P : BlockVec d} {η : Vec d → ℝ} {Gη : ℝ}
    (hEllO : IsEllipticFieldOn 1 Θ U a)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη) (c : ℝ) :
    IntegrableOn (cutoffIntegrand a v vstar P c η) U := by
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  have hEllAdj : IsEllipticFieldOn 1 Θ U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEllO
  have hu : MemScalarL2 U (centeredPotential m v P.1 c).toFun := (centeredPotential m v P.1 c).memL2
  have hus : MemScalarL2 U (centeredPotential m vstar P.1 (-c)).toFun :=
    (centeredPotential m vstar P.1 (-c)).memL2
  have hF1 : MemVectorL2 U (fun x => P.2 - matVecMul (a x) (v.grad x)) :=
    (memVectorL2_const P.2).sub (memVectorL2_matVecMul_of_isEllipticFieldOn hEllO v.grad_memVectorL2)
  have hF2 : MemVectorL2 U (fun x => matVecMul (matTranspose (a x)) (vstar.grad x)) := by
    simpa [Homogenization.adjointCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEllAdj vstar.grad_memVectorL2
  refine (integrableOn_scalarL2_mul_vecDot_memLpTop hu hF1
      (fun i => memLpTop_fderiv_sqCutoff_cube hη hIcc hGη i)).sub ?_
  exact integrableOn_scalarL2_mul_vecDot_memLpTop hus hF2
    (fun i => memLpTop_fderiv_sqCutoff_cube hη hIcc hGη i)

end Integrability

/-! ## The integral test identity -/

omit [NeZero d] in
/-- **The test identity.**  With the weak form and the
`η²·u` test pair, the energy integral equals the bulk integral plus the cutoff
integral. -/
theorem energyIntegral_eq_bulk_add_cutoff
    {a : CoeffField d} {Θ : ℝ} {v vstar : H1Function U} {P : BlockVec d}
    {η : Vec d → ℝ} {Gη : ℝ} {c : ℝ}
    (hEllO : IsEllipticFieldOn 1 Θ U a)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη)
    (hWeak : CoupledWeakForm a U P.2 v vstar)
    (hTrace : MemH10 U (fun x => v.toFun x + vstar.toFun x - vecDot P.1 x)) :
    (∫ x in U, energyIntegrand a v vstar P η x)
      = (∫ x in U, bulkIntegrand a v vstar P η x)
        + (∫ x in U, cutoffIntegrand a v vstar P c η x) := by
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  classical
  -- the smooth test pair and its admissibility
  set φ := testFun hη hIcc hGη (centeredPotential m v P.1 c) with hφdef
  set φstar := testFun hη hIcc hGη (centeredPotential m vstar P.1 (-c)) with hφsdef
  have hadm : MemH10 U (fun x => φ.toFun x + φstar.toFun x) :=
    memH10_testPair_sum hη hIcc hGη hTrace
  have hweak := hWeak φ φstar hadm
  -- the gradient of the test functions as explicit vectors
  have hφg : ∀ x, φ.grad x
      = sqCutoff η x • (v.grad x - (1/2:ℝ)•P.1)
        + (centeredPotential m v P.1 c).toFun x
          • (fun i => fderiv ℝ (sqCutoff η) x (basisVec i)) := by
    intro x; funext i
    rw [hφdef, testFun_grad, centeredPotential_grad]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  have hφsg : ∀ x, φstar.grad x
      = sqCutoff η x • (vstar.grad x - (1/2:ℝ)•P.1)
        + (centeredPotential m vstar P.1 (-c)).toFun x
          • (fun i => fderiv ℝ (sqCutoff η) x (basisVec i)) := by
    intro x; funext i
    rw [hφsdef, testFun_grad, centeredPotential_grad]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  -- pointwise identity: energy = bulk + cutoff + weak-form defect
  have hpt : ∀ x, energyIntegrand a v vstar P η x
      = bulkIntegrand a v vstar P η x + cutoffIntegrand a v vstar P c η x
        + (vecDot (φ.grad x) (matVecMul (a x) (v.grad x))
            + vecDot (φstar.grad x) (matVecMul (matTranspose (a x)) (vstar.grad x))
            - vecDot P.2 (φ.grad x)) := by
    intro x
    have h := pointwise_energy_test_identity (a x) (v.grad x) (vstar.grad x) P.1 P.2
      (fun i => fderiv ℝ (sqCutoff η) x (basisVec i)) (sqCutoff η x)
      ((centeredPotential m v P.1 c).toFun x) ((centeredPotential m vstar P.1 (-c)).toFun x)
    rw [hφg x, hφsg x]
    simpa only [energyIntegrand, bulkIntegrand, cutoffIntegrand] using h
  -- integrability of the pieces
  have hIe : IntegrableOn (energyIntegrand a v vstar P η) U :=
    integrableOn_energyIntegrand hEllO hη hIcc
  have hIb : IntegrableOn (bulkIntegrand a v vstar P η) U :=
    integrableOn_bulkIntegrand hEllO hη hIcc
  have hIc : IntegrableOn (cutoffIntegrand a v vstar P c η) U :=
    integrableOn_cutoffIntegrand hEllO hη hIcc hGη c
  have hIL1 : IntegrableOn (fun x => vecDot (φ.grad x) (matVecMul (a x) (v.grad x))) U :=
    integrableOn_vecDot_of_memVectorL2 φ.grad_memVectorL2
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEllO v.grad_memVectorL2)
  have hIL2 : IntegrableOn
      (fun x => vecDot (φstar.grad x) (matVecMul (matTranspose (a x)) (vstar.grad x))) U := by
    have hEllAdj : IsEllipticFieldOn 1 Θ U (Homogenization.adjointCoeffField a) :=
      isEllipticFieldOn_adjointCoeffField hEllO
    have hF : MemVectorL2 U (fun x => matVecMul (matTranspose (a x)) (vstar.grad x)) := by
      simpa [Homogenization.adjointCoeffField] using
        memVectorL2_matVecMul_of_isEllipticFieldOn hEllAdj vstar.grad_memVectorL2
    exact integrableOn_vecDot_of_memVectorL2 φstar.grad_memVectorL2 hF
  have hIR : IntegrableOn (fun x => vecDot P.2 (φ.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 (memVectorL2_const P.2) φ.grad_memVectorL2
  -- the weak-form defect density and its vanishing integral
  set F : Vec d → ℝ := fun x => vecDot (φ.grad x) (matVecMul (a x) (v.grad x))
      + vecDot (φstar.grad x) (matVecMul (matTranspose (a x)) (vstar.grad x))
      - vecDot P.2 (φ.grad x) with hFdef
  have hdefect : IntegrableOn F U := (hIL1.add hIL2).sub hIR
  have hFzero : (∫ x in U, F x) = 0 := by
    have h1 : (∫ x in U, F x)
        = (∫ x in U, (vecDot (φ.grad x) (matVecMul (a x) (v.grad x))
            + vecDot (φstar.grad x) (matVecMul (matTranspose (a x)) (vstar.grad x))))
          - ∫ x in U, vecDot P.2 (φ.grad x) := by
      rw [hFdef]; exact integral_sub (hIL1.add hIL2) hIR
    have h2 : (∫ x in U, (vecDot (φ.grad x) (matVecMul (a x) (v.grad x))
          + vecDot (φstar.grad x) (matVecMul (matTranspose (a x)) (vstar.grad x))))
        = (∫ x in U, vecDot (φ.grad x) (matVecMul (a x) (v.grad x)))
          + ∫ x in U, vecDot (φstar.grad x) (matVecMul (matTranspose (a x)) (vstar.grad x)) :=
      integral_add hIL1 hIL2
    rw [h1, h2, hweak]; ring
  -- integrate the pointwise identity and split
  have hcongr : (∫ x in U, energyIntegrand a v vstar P η x)
      = ∫ x in U, (bulkIntegrand a v vstar P η x + cutoffIntegrand a v vstar P c η x + F x) :=
    setIntegral_congr_fun (measurableSet_openCubeSet _) (fun x _ => hpt x)
  have hsplit1 : (∫ x in U,
        (bulkIntegrand a v vstar P η x + cutoffIntegrand a v vstar P c η x + F x))
      = (∫ x in U, (bulkIntegrand a v vstar P η x + cutoffIntegrand a v vstar P c η x))
        + ∫ x in U, F x :=
    integral_add (hIb.add hIc) hdefect
  have hsplit2 : (∫ x in U, (bulkIntegrand a v vstar P η x + cutoffIntegrand a v vstar P c η x))
      = (∫ x in U, bulkIntegrand a v vstar P η x)
        + ∫ x in U, cutoffIntegrand a v vstar P c η x :=
    integral_add hIb hIc
  rw [hcongr, hsplit1, hsplit2, hFzero, add_zero]

end Integral

end

end Homogenization
