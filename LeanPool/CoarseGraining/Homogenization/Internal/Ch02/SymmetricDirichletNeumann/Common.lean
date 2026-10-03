/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumannDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.PotentialSolenoidal
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric.Bracketing
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric.OpenBoundedConvex
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric.VariationalProblems
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.GradientUniqueness
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.MatrixExtraction
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Representatives
public import LeanPool.CoarseGraining.Homogenization.PDE.EnergyIdentities
public import LeanPool.CoarseGraining.Homogenization.PDE.DirichletRHS
public import LeanPool.CoarseGraining.Homogenization.PDE.NeumannRHS
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareMeanZero
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Realization

/-! # Common -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-!
# Common Symmetric Dirichlet-Neumann Helpers

This file is split mechanically out of `Internal.Ch02.SymmetricDirichletNeumann`.
-/

theorem memVectorL2_neg_matVecMul_const {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (p : Vec d) :
    MemVectorL2 U (fun x => -matVecMul (a x) p) := by
  have hp : MemVectorL2 U (fun _ : Vec d => p) := by
    simpa using
      (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal))
        (c := p))
  have hbase : MemVectorL2 U (fun x => matVecMul (a x) p) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hp
  simpa [Pi.smul_apply] using! hbase.const_smul (-1 : ℝ)

theorem memVectorL2_const_vec {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (q : Vec d) :
    MemVectorL2 U (fun _ : Vec d => q) := by
  simpa using
    (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal))
      (c := q))

theorem potentialZeroTraceFieldOn_of_isPotentialZeroTraceOn {d : ℕ}
    {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn U f) :
    Book.Ch01.PotentialZeroTraceFieldOn U f := by
  rcases hf with ⟨φ, rfl⟩
  exact Book.Ch01.potentialZeroTraceFieldOn_of_h10 φ

theorem isSymmetricDirichletAdmissible_of_isAffineDirichletSolution
    {d : ℕ} (U : Domain d) (a : CoeffOn U) {p : Vec d}
    {u : H1Function (U : Set (Vec d))}
    (hu : IsAffineDirichletSolution a.toCoeffField (U : Set (Vec d)) p u) :
    IsSymmetricDirichletAdmissible U p u :=
  potentialZeroTraceFieldOn_of_isPotentialZeroTraceOn
    hu.isPotentialZeroTraceOn_grad_sub_const

theorem exists_zeroTraceGradientAE_of_dirichlet_difference
    {d : ℕ} (U : Domain d) (a : CoeffOn U) {p : Vec d}
    {u w : H1Function (U : Set (Vec d))}
    (hu : IsAffineDirichletSolution a.toCoeffField (U : Set (Vec d)) p u)
    (hw : IsSymmetricDirichletAdmissible U p w) :
    ∃ θ : H10Function (U : Set (Vec d)),
      (w - u).grad =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        θ.toH1Function.grad := by
  rcases hw with ⟨_hwMem, ψ, hψ⟩
  rcases hu.isPotentialZeroTraceOn_grad_sub_const with ⟨φ, hφ⟩
  refine ⟨ψ - φ, ?_⟩
  filter_upwards [hψ] with x hx
  have hz :
      (w - u).grad x = w.grad x - u.grad x := by
    simp
  have hθ :
      (ψ - φ).toH1Function.grad x =
        ψ.toH1Function.grad x - φ.toH1Function.grad x := by
    change (ψ.toH1Function - φ.toH1Function).grad x =
      ψ.toH1Function.grad x - φ.toH1Function.grad x
    simp
  rw [hz, hθ, ← hx]
  have hφx :
      φ.toH1Function.grad x = u.grad x - p := by
    simpa using congrFun hφ x
  rw [hφx]
  ext i
  simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

theorem meanZeroOn_of_h1MeanZeroFunction {d : ℕ} {U : Set (Vec d)}
    (u : H1MeanZeroFunction U) :
    MeanZeroOn U u.toH1Function.toFun :=
  u.meanZero

theorem integrableOn_h1_coefficientEnergyDensity {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (u : H1Function U) :
    MeasureTheory.IntegrableOn
      (fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))) U := by
  refine
    (integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn
      hEll u.grad_memVectorL2).congr_fun ?_ (measurableSet_of_isEllipticFieldOn hEll)
  intro x _hx
  exact coefficientEnergyDensity_eq_unsymmetrized a u.grad x

theorem integrableOn_vecDot_const_h1Grad {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (q : Vec d) (u : H1Function U) :
    MeasureTheory.IntegrableOn (fun x => vecDot q (u.grad x)) U :=
  integrableOn_vecDot_of_memVectorL2 (memVectorL2_const_vec (U := U) q)
    u.grad_memVectorL2

theorem integrableOn_symmetricNeumannIntegrand_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (q : Vec d)
    (u : H1Function U) :
    MeasureTheory.IntegrableOn
      (fun x =>
        vecDot q (u.grad x) -
          (1 / 2 : ℝ) * vecDot (u.grad x) (matVecMul (a x) (u.grad x))) U := by
  exact
    (integrableOn_vecDot_const_h1Grad q u).sub
      ((integrableOn_h1_coefficientEnergyDensity hEll u).const_mul (1 / 2 : ℝ))

theorem integrableOn_symmetricDirichletIntegrand_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (u : H1Function U) :
    MeasureTheory.IntegrableOn
      (fun x =>
        (1 / 2 : ℝ) * vecDot (u.grad x) (matVecMul (a x) (u.grad x))) U :=
  (integrableOn_h1_coefficientEnergyDensity hEll u).const_mul (1 / 2 : ℝ)

theorem h1_grad_eq_zero_ae_of_volumeAverage_energy_eq_zero {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (u : H1Function (U : Set (Vec d)))
    (hEnergyInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
        (U : Set (Vec d)))
    (hEnergyAvg :
      volumeAverage (U : Set (Vec d))
        (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x))) = 0) :
    u.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))] 0 := by
  have hvolPos : 0 < MeasureTheory.volume (U : Set (Vec d)) :=
    U.isOpen.measure_pos MeasureTheory.volume U.nonempty
  have hvolNeZero : MeasureTheory.volume (U : Set (Vec d)) ≠ 0 :=
    ne_of_gt hvolPos
  have hvolNeTop : MeasureTheory.volume (U : Set (Vec d)) ≠ ⊤ := by
    have htop :
        volumeMeasureOn (U : Set (Vec d)) Set.univ ≠ ⊤ :=
      MeasureTheory.measure_ne_top (μ := volumeMeasureOn (U : Set (Vec d))) Set.univ
    simpa [volumeMeasureOn] using htop
  have hvolRealPos : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    ENNReal.toReal_pos hvolNeZero hvolNeTop
  have hvolRealNe : (MeasureTheory.volume (U : Set (Vec d))).toReal ≠ 0 :=
    ne_of_gt hvolRealPos
  have hIntegral :
      ∫ x in (U : Set (Vec d)),
          vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x))
            ∂MeasureTheory.volume = 0 := by
    unfold volumeAverage at hEnergyAvg
    exact (mul_eq_zero.mp hEnergyAvg).resolve_left (inv_ne_zero hvolRealNe)
  have hNonnegAE :
      ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
        0 ≤ vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)) := by
    filter_upwards
        [MeasureTheory.ae_restrict_mem (measurableSet_of_isEllipticFieldOn hEll)] with x hxU
    have hnonneg :=
      coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll u.grad x hxU
    simpa [coefficientEnergyDensity_eq_unsymmetrized] using hnonneg
  have hEnergyAE :
      (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
        =ᵐ[volumeMeasureOn (U : Set (Vec d))] 0 := by
    exact
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
        hNonnegAE hEnergyInt.integrable).1 (by
          simpa [volumeMeasureOn] using hIntegral)
  filter_upwards
      [hEnergyAE,
        MeasureTheory.ae_restrict_mem (measurableSet_of_isEllipticFieldOn hEll)] with
    x hEnergyZero hxU
  have hA := hEll.2 x hxU
  have hlower :=
    lowerBound_symmPart_of_isEllipticMatrix hA (u.grad x)
  have hEnergyPoint :
      vecDot (u.grad x)
          (matVecMul (symmPart (a.toCoeffField x)) (u.grad x)) = 0 := by
    simpa [vecDot_matVecMul_symmPart] using hEnergyZero
  have hnormNonneg : 0 ≤ vecNormSq (u.grad x) :=
    vecNormSq_nonneg (u.grad x)
  have hnormZero : vecNormSq (u.grad x) = 0 := by
    nlinarith [hA.1, hlower, hEnergyPoint, hnormNonneg]
  exact vecNormSq_eq_zero hnormZero

theorem h1AverageGradient_eq_of_grad_ae {d : ℕ} (U : Domain d)
    {u v : H1Function (U : Set (Vec d))}
    (hgrad :
      u.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))] v.grad) :
    h1AverageGradient U u = h1AverageGradient U v := by
  ext i
  unfold h1AverageGradient averageVec average
  congr 1
  exact MeasureTheory.integral_congr_ae <|
    hgrad.mono fun x hx => congrArg (fun y : Vec d => y i) hx

theorem h1AverageFlux_eq_of_grad_ae {d : ℕ} (U : Domain d)
    (a : CoeffOn U) {u v : H1Function (U : Set (Vec d))}
    (hgrad :
      u.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))] v.grad) :
    h1AverageFlux U a u = h1AverageFlux U a v := by
  ext i
  unfold h1AverageFlux averageVec average
  congr 1
  exact MeasureTheory.integral_congr_ae <|
    hgrad.mono fun x hx => by
      simp [hx]

theorem symmetricDirichletNu_eq_of_minimizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U} {p : Vec d}
    {u : H1Function (U : Set (Vec d))}
    (hu : IsSymmetricDirichletMinimizer U a p u) :
    symmetricDirichletNu U a p = symmetricDirichletEnergyValue U a u := by
  unfold symmetricDirichletNu
  exact
    (show IsLeast (symmetricDirichletValueSet U a p)
        (symmetricDirichletEnergyValue U a u) from by
      constructor
      · exact ⟨u, hu.1, rfl⟩
      · intro y hy
        rcases hy with ⟨w, hw, rfl⟩
        exact hu.2 w hw).csInf_eq

theorem symmetricNeumannNu_eq_of_maximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U} {q : Vec d}
    {u : H1Function (U : Set (Vec d))}
    (hu : IsSymmetricNeumannMaximizer U a q u) :
    symmetricNeumannNu U a q = symmetricNeumannEnergyValue U a q u := by
  unfold symmetricNeumannNu
  exact
    (show IsGreatest (symmetricNeumannValueSet U a q)
        (symmetricNeumannEnergyValue U a q u) from by
      constructor
      · exact ⟨u, rfl⟩
      · intro y hy
        rcases hy with ⟨w, rfl⟩
        exact hu w).csSup_eq

end BookCh02

end

end Ch02
end Internal
end Homogenization
