/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric.AverageFormulas
public import LeanPool.CoarseGraining.Homogenization.PDE.Harmonic
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.ZeroTraceAverages

/-! # Variational Problems -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Dirichlet and Neumann predicates for the symmetric split

This file introduces the PDE-facing predicates used to state the
Dirichlet-Neumann interpretation of the symmetric coarse-graining identities.
Existence and variational minimality are intentionally left to later files; the
predicates here record the boundary conditions and harmonicity in the existing
Sobolev/solenoidal language.
-/

private theorem volumeAverageVec_eq_const_of_integral_sub_const_eq_zero
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) (p : Vec d)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hzero :
      (fun i => ∫ x in U, (f x - p) i ∂MeasureTheory.volume) = 0) :
    volumeAverageVec U f = p := by
  ext i
  have hzero_i :
      ∫ x in U, (f x - p) i ∂MeasureTheory.volume = 0 := by
    simpa using congrFun hzero i
  have hf_int : MeasureTheory.IntegrableOn (fun x => f x i) U :=
    CorrectionFieldData.integrableOn_coord_of_memVectorL2 (U := U) hf i
  have hconst_int : MeasureTheory.IntegrableOn (fun _ : Vec d => p i) U := by
    simp [MeasureTheory.IntegrableOn]
  have hsub :
      ∫ x in U, (f x - p) i ∂MeasureTheory.volume =
        ∫ x in U, f x i ∂MeasureTheory.volume -
          ∫ x in U, p i ∂MeasureTheory.volume := by
    rw [show (fun x => (f x - p) i) = fun x => f x i - p i by
      funext x
      rfl]
    exact MeasureTheory.integral_sub hf_int hconst_int
  have hconst :
      ∫ x in U, p i ∂MeasureTheory.volume =
        (MeasureTheory.volume U).toReal * p i := by
    rw [MeasureTheory.integral_const, smul_eq_mul]
    have hμ₁ :
        (MeasureTheory.volume.restrict U).real Set.univ = MeasureTheory.volume.real U := by
      exact MeasureTheory.measureReal_restrict_apply_univ (μ := MeasureTheory.volume) U
    have hμ₂ : MeasureTheory.volume.real U = (MeasureTheory.volume U).toReal := rfl
    rw [hμ₁, hμ₂]
  have hf_integral :
      ∫ x in U, f x i ∂MeasureTheory.volume =
        (MeasureTheory.volume U).toReal * p i := by
    linarith
  unfold volumeAverageVec volumeAverage
  rw [hf_integral]
  field_simp [hvol]

/-- Affine Dirichlet solution with slope `p`: the gradient is `a`-harmonic and
differs from the constant gradient `p` by a zero-trace potential gradient. -/
def IsAffineDirichletSolution {d : ℕ} (a : CoeffField d) (U : Set (Vec d))
    (p : Vec d) (u : H1Function U) : Prop :=
  IsAHarmonicGradient a U u.grad ∧
    IsPotentialZeroTraceOn U (fun x => u.grad x - p)

namespace IsAffineDirichletSolution

theorem isAHarmonicGradient {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {p : Vec d} {u : H1Function U}
    (hu : IsAffineDirichletSolution a U p u) :
    IsAHarmonicGradient a U u.grad :=
  hu.1

theorem isPotentialZeroTraceOn_grad_sub_const {d : ℕ} {a : CoeffField d}
    {U : Set (Vec d)} {p : Vec d} {u : H1Function U}
    (hu : IsAffineDirichletSolution a U p u) :
    IsPotentialZeroTraceOn U (fun x => u.grad x - p) :=
  hu.2

theorem averageGradient_eq {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {p : Vec d}
    {u : H1Function U} (hu : IsAffineDirichletSolution a U p u)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0) :
    volumeAverageVec U u.grad = p := by
  exact
    volumeAverageVec_eq_const_of_integral_sub_const_eq_zero
      (f := u.grad) u.grad_memVectorL2 p hvol
      (IsPotentialZeroTraceOn.integral_eq_zero
        hu.isPotentialZeroTraceOn_grad_sub_const)

/-- Forget the affine boundary condition and retain the associated
`a`-harmonic function. -/
def toAHarmonicFunction {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {p : Vec d} {u : H1Function U}
    (hu : IsAffineDirichletSolution a U p u) :
    AHarmonicFunction a U where
  toH1 := u
  isHarmonic := hu.isAHarmonicGradient

@[simp] theorem toAHarmonicFunction_toH1 {d : ℕ} {a : CoeffField d}
    {U : Set (Vec d)} {p : Vec d} {u : H1Function U}
    (hu : IsAffineDirichletSolution a U p u) :
    hu.toAHarmonicFunction.toH1 = u :=
  rfl

@[simp] theorem toAHarmonicFunction_grad {d : ℕ} {a : CoeffField d}
    {U : Set (Vec d)} {p : Vec d} {u : H1Function U}
    (hu : IsAffineDirichletSolution a U p u) :
    hu.toAHarmonicFunction.toH1.grad = u.grad :=
  rfl

theorem firstVariation_integral_eq_zero_of_isSymmetricCoeffField {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)} {p : Vec d}
    {u : H1Function U} (hu : IsAffineDirichletSolution a U p u)
    (ha : IsSymmetricCoeffField a) (w : AHarmonicFunction a U) :
    ∫ x in U,
      scalarFirstVariationIntegrand U a (-p) 0 hu.toAHarmonicFunction w x
        ∂MeasureTheory.volume = 0 := by
  rcases hu.isPotentialZeroTraceOn_grad_sub_const with ⟨φ, hφ⟩
  have hzero :
      ∫ x in U,
        vecDot (matVecMul (a x) (w.toH1.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume = 0 :=
    w.isHarmonic.2 φ
  have hfun :
      scalarFirstVariationIntegrand U a (-p) 0 hu.toAHarmonicFunction w =
        fun x =>
          -vecDot (matVecMul (a x) (w.toH1.grad x)) (φ.toH1Function.grad x) := by
    funext x
    have hsymm :
        vecDot (w.toH1.grad x) (matVecMul (a x) (u.grad x)) =
          vecDot (matVecMul (a x) (w.toH1.grad x)) (u.grad x) := by
      calc
        vecDot (w.toH1.grad x) (matVecMul (a x) (u.grad x)) =
            vecDot (u.grad x) (matVecMul (a x) (w.toH1.grad x)) :=
          vecDot_matVecMul_comm_of_isSymm (ha x) (w.toH1.grad x) (u.grad x)
        _ = vecDot (matVecMul (a x) (w.toH1.grad x)) (u.grad x) := by
          rw [vecDot_comm]
    have hsymmPart : symmPart (a x) = a x :=
      symmPart_eq_self_of_isSymmetricCoeffField ha x
    calc
      scalarFirstVariationIntegrand U a (-p) 0 hu.toAHarmonicFunction w x =
          vecDot p (matVecMul (a x) (w.toH1.grad x)) -
            vecDot (w.toH1.grad x) (matVecMul (a x) (u.grad x)) := by
            simp [scalarFirstVariationIntegrand, hsymmPart, vecDot_zero_left,
              vecDot_neg_left]
      _ =
          vecDot (matVecMul (a x) (w.toH1.grad x)) p -
            vecDot (matVecMul (a x) (w.toH1.grad x)) (u.grad x) := by
            rw [vecDot_comm p, hsymm]
      _ = -vecDot (matVecMul (a x) (w.toH1.grad x)) (u.grad x - p) := by
            simp [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]
      _ = -vecDot (matVecMul (a x) (w.toH1.grad x)) (φ.toH1Function.grad x) := by
            rw [hφ]
  have hzero_neg :
      ∫ x in U,
        -vecDot (matVecMul (a x) (w.toH1.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume = 0 := by
    rw [MeasureTheory.integral_neg, hzero]
    simp
  simpa [hfun] using hzero_neg

theorem isResponseMaximizer_of_isSymmetricCoeffField_of_isEllipticFieldOn {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {p : Vec d}
    {u : H1Function U} (hu : IsAffineDirichletSolution a U p u)
    (ha : IsSymmetricCoeffField a) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsResponseMaximizer U (-p) 0 a hu.toAHarmonicFunction := by
  apply isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn U a hEll
  intro w
  exact
    volumeAverage_eq_zero_of_integral_eq_zero
      (hu.firstVariation_integral_eq_zero_of_isSymmetricCoeffField ha w)

theorem averageFlux_eq_sigmaCoarse_mul_of_isResponseMaximizer {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {p : Vec d}
    {u : H1Function U} (hu : IsAffineDirichletSolution a U p u)
    (hmax : IsResponseMaximizer U (-p) 0 a hu.toAHarmonicFunction)
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    volumeAverageVec U (fun x => matVecMul (a x) (u.grad x)) =
      matVecMul (sigmaCoarse U a) p := by
  let v : ScalarCanonicalMaximizer U (-p) 0 a :=
    ScalarCanonicalMaximizer.ofIsResponseMaximizer hu.toAHarmonicFunction hmax
  have hAvg :=
    ScalarCanonicalMaximizer.averageFluxFormulaCanonical_p_zero_of_isSymmetricCoeffField
      (v := v) (ha := ha) (hA := hA) (hS := hS) (hK := hK)
      (hSigma := hSigma) (hdet := hdet) (hInt := hInt) vFlux
  simpa [v, volumeAverageVec, matVecMul_neg, neg_matVecMul] using! hAvg

theorem averageFlux_eq_sigmaCoarse_mul_of_isSymmetricCoeffField_of_isEllipticFieldOn {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {p : Vec d}
    {u : H1Function U} (hu : IsAffineDirichletSolution a U p u)
    (ha : IsSymmetricCoeffField a) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    volumeAverageVec U (fun x => matVecMul (a x) (u.grad x)) =
      matVecMul (sigmaCoarse U a) p := by
  exact
    hu.averageFlux_eq_sigmaCoarse_mul_of_isResponseMaximizer
      (hu.isResponseMaximizer_of_isSymmetricCoeffField_of_isEllipticFieldOn ha hEll)
      ha hA hS hK hSigma hdet hInt vFlux

theorem energy_eq_vecDot_sigmaCoarse_of_isSymmetricCoeffField_of_isEllipticFieldOn {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {p : Vec d}
    {u : H1Function U} (hu : IsAffineDirichletSolution a U p u)
    (ha : IsSymmetricCoeffField a) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    volumeAverage U (scalarVariationEnergyIntegrand a hu.toAHarmonicFunction) =
      vecDot p (matVecMul (sigmaCoarse U a) p) := by
  let hInt : ResponseLinearIntegrabilityData U a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hmax :
      IsResponseMaximizer U (-p) 0 a hu.toAHarmonicFunction :=
    hu.isResponseMaximizer_of_isSymmetricCoeffField_of_isEllipticFieldOn ha hEll
  have hEnergy :=
    responseJ_energy_of_isResponseMaximizer U a (-p) 0 hu.toAHarmonicFunction hmax
      (hInt.weakFlux hu.toAHarmonicFunction)
      (hInt.response (-p) 0 hu.toAHarmonicFunction)
      (hInt.firstVariation (-p) 0 hu.toAHarmonicFunction hu.toAHarmonicFunction)
      (hInt.energy hu.toAHarmonicFunction)
  have hResp :=
    responseJ_p_zero_eq_half_vecDot_sigmaCoarse_of_isSymmetricCoeffField
      ha hA hS hK hSigma hdet (-p)
  rw [hResp] at hEnergy
  have hquad :
      vecDot (-p) (matVecMul (sigmaCoarse U a) (-p)) =
        vecDot p (matVecMul (sigmaCoarse U a) p) := by
    simp [matVecMul_neg, vecDot_neg_left, vecDot_neg_right]
  rw [hquad] at hEnergy
  linarith

end IsAffineDirichletSolution

/-- Mean-zero Neumann solution with constant flux `q`: the function is
`a`-harmonic and its excess flux `a ∇u - q` has zero normal trace. -/
def IsConstantFluxNeumannSolution {d : ℕ} (a : CoeffField d) (U : Set (Vec d))
    (q : Vec d) (u : H1MeanZeroFunction U) : Prop :=
  IsAHarmonicGradient a U u.toH1Function.grad ∧
    IsSolenoidalZeroNormalTraceOn U
      (fun x => matVecMul (a x) (u.toH1Function.grad x) - q)

namespace IsConstantFluxNeumannSolution

theorem isAHarmonicGradient {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {q : Vec d} {u : H1MeanZeroFunction U}
    (hu : IsConstantFluxNeumannSolution a U q u) :
    IsAHarmonicGradient a U u.toH1Function.grad :=
  hu.1

theorem isSolenoidalZeroNormalTraceOn_flux_sub_const {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)} {q : Vec d}
    {u : H1MeanZeroFunction U}
    (hu : IsConstantFluxNeumannSolution a U q u) :
    IsSolenoidalZeroNormalTraceOn U
      (fun x => matVecMul (a x) (u.toH1Function.grad x) - q) :=
  hu.2

theorem averageFlux_eq {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {q : Vec d}
    {u : H1MeanZeroFunction U} (hu : IsConstantFluxNeumannSolution a U q u)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hU : IsSobolevRegularDomain U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0) :
    volumeAverageVec U (fun x => matVecMul (a x) (u.toH1Function.grad x)) = q := by
  exact
    volumeAverageVec_eq_const_of_integral_sub_const_eq_zero
      (f := fun x => matVecMul (a x) (u.toH1Function.grad x))
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1Function.grad_memVectorL2)
      q hvol
      (IsSolenoidalZeroNormalTraceOn.integral_eq_zero hU
        hu.isSolenoidalZeroNormalTraceOn_flux_sub_const)

/-- Forget the constant-flux boundary condition and retain the associated
`a`-harmonic function. -/
def toAHarmonicFunction {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {q : Vec d} {u : H1MeanZeroFunction U}
    (hu : IsConstantFluxNeumannSolution a U q u) :
    AHarmonicFunction a U where
  toH1 := u.toH1Function
  isHarmonic := hu.isAHarmonicGradient

@[simp] theorem toAHarmonicFunction_toH1 {d : ℕ} {a : CoeffField d}
    {U : Set (Vec d)} {q : Vec d} {u : H1MeanZeroFunction U}
    (hu : IsConstantFluxNeumannSolution a U q u) :
    hu.toAHarmonicFunction.toH1 = u.toH1Function :=
  rfl

@[simp] theorem toAHarmonicFunction_grad {d : ℕ} {a : CoeffField d}
    {U : Set (Vec d)} {q : Vec d} {u : H1MeanZeroFunction U}
    (hu : IsConstantFluxNeumannSolution a U q u) :
    hu.toAHarmonicFunction.toH1.grad = u.toH1Function.grad :=
  rfl

theorem firstVariation_integral_eq_zero_of_isSymmetricCoeffField {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)} {q : Vec d}
    {u : H1MeanZeroFunction U} (hu : IsConstantFluxNeumannSolution a U q u)
    (ha : IsSymmetricCoeffField a) (w : AHarmonicFunction a U) :
    ∫ x in U,
      scalarFirstVariationIntegrand U a 0 q hu.toAHarmonicFunction w x
        ∂MeasureTheory.volume = 0 := by
  have hzero :
      ∫ x in U,
        vecDot (matVecMul (a x) (u.toH1Function.grad x) - q) (w.toH1.grad x)
          ∂MeasureTheory.volume = 0 :=
    hu.isSolenoidalZeroNormalTraceOn_flux_sub_const w.toH1
  have hfun :
      scalarFirstVariationIntegrand U a 0 q hu.toAHarmonicFunction w =
        fun x =>
          -vecDot (matVecMul (a x) (u.toH1Function.grad x) - q) (w.toH1.grad x) := by
    funext x
    have hsymmPart : symmPart (a x) = a x :=
      symmPart_eq_self_of_isSymmetricCoeffField ha x
    calc
      scalarFirstVariationIntegrand U a 0 q hu.toAHarmonicFunction w x =
          vecDot q (w.toH1.grad x) -
            vecDot (w.toH1.grad x) (matVecMul (a x) (u.toH1Function.grad x)) := by
            simp [scalarFirstVariationIntegrand, hsymmPart, vecDot_zero_left]
      _ =
          vecDot q (w.toH1.grad x) -
            vecDot (matVecMul (a x) (u.toH1Function.grad x)) (w.toH1.grad x) := by
            rw [vecDot_comm (w.toH1.grad x)]
      _ =
          -vecDot (matVecMul (a x) (u.toH1Function.grad x) - q) (w.toH1.grad x) := by
            simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  have hzero_neg :
      ∫ x in U,
        -vecDot (matVecMul (a x) (u.toH1Function.grad x) - q) (w.toH1.grad x)
          ∂MeasureTheory.volume = 0 := by
    rw [MeasureTheory.integral_neg, hzero]
    simp
  simpa [hfun] using hzero_neg

theorem isResponseMaximizer_of_isSymmetricCoeffField_of_isEllipticFieldOn {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {q : Vec d}
    {u : H1MeanZeroFunction U} (hu : IsConstantFluxNeumannSolution a U q u)
    (ha : IsSymmetricCoeffField a) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsResponseMaximizer U 0 q a hu.toAHarmonicFunction := by
  apply isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn U a hEll
  intro w
  exact
    volumeAverage_eq_zero_of_integral_eq_zero
      (hu.firstVariation_integral_eq_zero_of_isSymmetricCoeffField ha w)

theorem averageGradient_eq_sigmaStarInvCoarse_mul_of_isResponseMaximizer {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {q : Vec d}
    {u : H1MeanZeroFunction U} (hu : IsConstantFluxNeumannSolution a U q u)
    (hmax : IsResponseMaximizer U 0 q a hu.toAHarmonicFunction)
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    volumeAverageVec U u.toH1Function.grad =
      matVecMul (sigmaStarInvCoarse U a) q := by
  let v : ScalarCanonicalMaximizer U 0 q a :=
    ScalarCanonicalMaximizer.ofIsResponseMaximizer hu.toAHarmonicFunction hmax
  have hAvg :=
    ScalarCanonicalMaximizer.averageGradientFormulaCanonical_zero_q_of_isSymmetricCoeffField
      (v := v) (ha := ha) (hA := hA) (hS := hS) (hK := hK)
      (hdet := hdet) (hInt := hInt) vGrad
  simpa [v, volumeAverageVec] using! hAvg

theorem averageGradient_eq_sigmaStarInvCoarse_mul_of_isSymmetricCoeffField_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {q : Vec d}
    {u : H1MeanZeroFunction U} (hu : IsConstantFluxNeumannSolution a U q u)
    (ha : IsSymmetricCoeffField a) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    volumeAverageVec U u.toH1Function.grad =
      matVecMul (sigmaStarInvCoarse U a) q := by
  exact
    hu.averageGradient_eq_sigmaStarInvCoarse_mul_of_isResponseMaximizer
      (hu.isResponseMaximizer_of_isSymmetricCoeffField_of_isEllipticFieldOn ha hEll)
      ha hA hS hK hdet hInt vGrad

theorem energy_eq_vecDot_sigmaStarInvCoarse_of_isSymmetricCoeffField_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {q : Vec d}
    {u : H1MeanZeroFunction U} (hu : IsConstantFluxNeumannSolution a U q u)
    (ha : IsSymmetricCoeffField a) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    {sigmaStar : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar) :
    volumeAverage U (scalarVariationEnergyIntegrand a hu.toAHarmonicFunction) =
      vecDot q (matVecMul (sigmaStarInvCoarse U a) q) := by
  let hInt : ResponseLinearIntegrabilityData U a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hmax :
      IsResponseMaximizer U 0 q a hu.toAHarmonicFunction :=
    hu.isResponseMaximizer_of_isSymmetricCoeffField_of_isEllipticFieldOn ha hEll
  have hEnergy :=
    responseJ_energy_of_isResponseMaximizer U a 0 q hu.toAHarmonicFunction hmax
      (hInt.weakFlux hu.toAHarmonicFunction)
      (hInt.response 0 q hu.toAHarmonicFunction)
      (hInt.firstVariation 0 q hu.toAHarmonicFunction hu.toAHarmonicFunction)
      (hInt.energy hu.toAHarmonicFunction)
  have hResp :=
    responseJ_zero_q_eq_half_vecDot_sigmaStarInvCoarse_of_isSigmaStarCoarse hS q
  rw [hResp] at hEnergy
  linarith

end IsConstantFluxNeumannSolution

section DirichletNeumannSplit

/-- The harmonic response obtained by subtracting the affine Dirichlet solution
from the constant-flux Neumann solution. This is the Lean object behind the
informal formula `v(p,q) = u_q^N - u_p^D` in the symmetric case. -/
noncomputable def dirichletNeumannSplitOfIsEllipticFieldOn {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) {p q : Vec d}
    {uD : H1Function U} {uN : H1MeanZeroFunction U}
    (huD : IsAffineDirichletSolution a U p uD)
    (huN : IsConstantFluxNeumannSolution a U q uN) :
    AHarmonicFunction a U := by
  let hInt : ResponseLinearIntegrabilityData U a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  exact
    AHarmonicFunction.subOfIntegrable huN.toAHarmonicFunction huD.toAHarmonicFunction
      (hInt.weakFlux huN.toAHarmonicFunction)
      (hInt.weakFlux huD.toAHarmonicFunction)

@[simp] theorem dirichletNeumannSplitOfIsEllipticFieldOn_grad {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) {p q : Vec d}
    {uD : H1Function U} {uN : H1MeanZeroFunction U}
    (huD : IsAffineDirichletSolution a U p uD)
    (huN : IsConstantFluxNeumannSolution a U q uN) :
    (dirichletNeumannSplitOfIsEllipticFieldOn hEll huD huN).toH1.grad =
      uN.toH1Function.grad - uD.grad := by
  funext x
  simp [dirichletNeumannSplitOfIsEllipticFieldOn]

theorem isResponseMaximizer_dirichletNeumannSplitOfIsEllipticFieldOn_of_isSymmetricCoeffField
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) {p q : Vec d}
    {uD : H1Function U} {uN : H1MeanZeroFunction U}
    (huD : IsAffineDirichletSolution a U p uD)
    (huN : IsConstantFluxNeumannSolution a U q uN)
    (ha : IsSymmetricCoeffField a) :
    IsResponseMaximizer U p q a
      (dirichletNeumannSplitOfIsEllipticFieldOn hEll huD huN) := by
  let hInt : ResponseLinearIntegrabilityData U a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hmaxN :
      IsResponseMaximizer U 0 q a huN.toAHarmonicFunction :=
    huN.isResponseMaximizer_of_isSymmetricCoeffField_of_isEllipticFieldOn ha hEll
  have hmaxD :
      IsResponseMaximizer U (-p) 0 a huD.toAHarmonicFunction :=
    huD.isResponseMaximizer_of_isSymmetricCoeffField_of_isEllipticFieldOn ha hEll
  have hsplit :=
    basic_cg_identities_sub_isResponseMaximizer_of_isResponseMaximizer
      U a 0 q (-p) 0 hInt huN.toAHarmonicFunction huD.toAHarmonicFunction
      hmaxN hmaxD
  simpa [dirichletNeumannSplitOfIsEllipticFieldOn, hInt, sub_eq_add_neg] using hsplit

end DirichletNeumannSplit

end

end Homogenization
