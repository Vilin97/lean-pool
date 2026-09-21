/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.SymmetricDirichletNeumann.Common

/-! # Dirichlet -/

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-!
# Dirichlet Side

This file is split mechanically out of `Internal.Ch02.SymmetricDirichletNeumann`.
-/

/-- Construct the old affine Dirichlet solution predicate from the zero-trace
Dirichlet RHS solver on a bounded open convex domain. This is an internal
bridge toward the public symmetric Dirichlet minimizer package. -/
theorem exists_isAffineDirichletSolution_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p : Vec d) :
    ∃ u : H1Function (U : Set (Vec d)),
      IsAffineDirichletSolution a.toCoeffField (U : Set (Vec d)) p u := by
  let Uset : Set (Vec d) := (U : Set (Vec d))
  let hSob : IsSobolevRegularDomain Uset := U.isDomain.isSobolevRegularDomain
  let uAff : H1Function Uset :=
    H1Function.affineOnIsSobolevRegularDomain hSob p
  let g : Vec d → Vec d := fun x => -matVecMul (a.toCoeffField x) p
  have hg : MemVectorL2 Uset g := by
    simpa [Uset, g] using memVectorL2_neg_matVecMul_const hEll p
  have hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization Uset :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      (U := Uset) U.isDomain
  let φ : H10Function Uset :=
    zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
      (a := a.toCoeffField) (U := Uset) (g := g) (lam := a.lam) (Lam := a.Lam)
      hg hRealize (by simpa [Uset] using U.nonempty) hEll
  have hφ :
      IsZeroTraceDirichletRhsWeakSolution a.toCoeffField Uset φ g :=
    isZeroTraceDirichletRhsWeakSolution_zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
      (a := a.toCoeffField) (U := Uset) (g := g) (lam := a.lam) (Lam := a.Lam)
      hg hRealize (by simpa [Uset] using U.nonempty) hEll
  let u : H1Function Uset := uAff + φ.toH1Function
  refine ⟨u, ?_⟩
  constructor
  · constructor
    · exact u.isPotentialOn
    · intro ψ
      have hpMem : MemVectorL2 Uset (fun x => matVecMul (a.toCoeffField x) p) := by
        have hp : MemVectorL2 Uset (fun _ : Vec d => p) :=
          memVectorL2_const_vec p
        exact memVectorL2_matVecMul_of_isEllipticFieldOn hEll hp
      have hφFluxMem :
          MemVectorL2 Uset
            (fun x => matVecMul (a.toCoeffField x) (φ.toH1Function.grad x)) :=
        memVectorL2_matVecMul_of_isEllipticFieldOn hEll
          φ.toH1Function.grad_memVectorL2
      have hpInt :
          MeasureTheory.IntegrableOn
            (fun x =>
              vecDot (matVecMul (a.toCoeffField x) p)
                (ψ.toH1Function.grad x)) Uset :=
        integrableOn_vecDot_of_memVectorL2 hpMem ψ.toH1Function.grad_memVectorL2
      have hφInt :
          MeasureTheory.IntegrableOn
            (fun x =>
              vecDot (matVecMul (a.toCoeffField x) (φ.toH1Function.grad x))
                (ψ.toH1Function.grad x)) Uset :=
        integrableOn_vecDot_of_memVectorL2 hφFluxMem
          ψ.toH1Function.grad_memVectorL2
      have hsplit :
          (fun x =>
              vecDot
                (matVecMul (a.toCoeffField x) (u.grad x))
                (ψ.toH1Function.grad x)) =
            fun x =>
              vecDot (matVecMul (a.toCoeffField x) p)
                  (ψ.toH1Function.grad x) +
                vecDot
                  (matVecMul (a.toCoeffField x) (φ.toH1Function.grad x))
                  (ψ.toH1Function.grad x) := by
        funext x
        simp [u, uAff, H1Function.affineOnIsSobolevRegularDomain_grad,
          matVecMul_add, vecDot_add_left]
      calc
        ∫ x in Uset,
            vecDot (matVecMul (a.toCoeffField x) (u.grad x))
              (ψ.toH1Function.grad x) ∂MeasureTheory.volume
            =
              ∫ x in Uset,
                (vecDot (matVecMul (a.toCoeffField x) p)
                    (ψ.toH1Function.grad x) +
                  vecDot
                    (matVecMul (a.toCoeffField x) (φ.toH1Function.grad x))
                    (ψ.toH1Function.grad x)) ∂MeasureTheory.volume := by
                rw [hsplit]
        _ =
              ∫ x in Uset,
                vecDot (matVecMul (a.toCoeffField x) p)
                  (ψ.toH1Function.grad x) ∂MeasureTheory.volume +
              ∫ x in Uset,
                vecDot
                  (matVecMul (a.toCoeffField x) (φ.toH1Function.grad x))
                  (ψ.toH1Function.grad x) ∂MeasureTheory.volume := by
                rw [MeasureTheory.integral_add hpInt hφInt]
        _ =
              ∫ x in Uset,
                vecDot (matVecMul (a.toCoeffField x) p)
                  (ψ.toH1Function.grad x) ∂MeasureTheory.volume +
              ∫ x in Uset,
                vecDot (g x) (ψ.toH1Function.grad x) ∂MeasureTheory.volume := by
                rw [hφ ψ]
        _ = 0 := by
              have hgDef :
                  (fun x => vecDot (g x) (ψ.toH1Function.grad x)) =
                    fun x =>
                      -vecDot (matVecMul (a.toCoeffField x) p)
                        (ψ.toH1Function.grad x) := by
                    funext x
                    simp [g, vecDot_neg_left]
              rw [hgDef, MeasureTheory.integral_neg]
              ring
  · have hgrad :
        (fun x => u.grad x - p) = φ.toH1Function.grad := by
      funext x
      simp [u, uAff, H1Function.affineOnIsSobolevRegularDomain_grad,
        sub_eq_add_neg, add_assoc]
    simpa [hgrad] using φ.isPotentialZeroTraceOn

theorem symmetricDirichletEnergyValue_eq_of_isAffineDirichletSolution
    {d : ℕ} (U : Domain d) (a : CoeffOn U) {p : Vec d}
    {u w : H1Function (U : Set (Vec d))}
    (hu : IsAffineDirichletSolution a.toCoeffField (U : Set (Vec d)) p u)
    (hw : IsSymmetricDirichletAdmissible U p w)
    (ha : IsSymmetricCoeffField a.toCoeffField)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    symmetricDirichletEnergyValue U a w =
      symmetricDirichletEnergyValue U a u +
        (1 / 2 : ℝ) *
          volumeAverage (U : Set (Vec d))
            (fun x =>
              vecDot ((w - u).grad x)
                (matVecMul (a.toCoeffField x) ((w - u).grad x))) := by
  let Uset : Set (Vec d) := (U : Set (Vec d))
  let z : H1Function Uset := w - u
  let fU : Vec d → ℝ :=
    fun x =>
      (1 / 2 : ℝ) * vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x))
  let fW : Vec d → ℝ :=
    fun x =>
      (1 / 2 : ℝ) * vecDot (w.grad x) (matVecMul (a.toCoeffField x) (w.grad x))
  let fCross : Vec d → ℝ :=
    fun x =>
      vecDot (matVecMul (a.toCoeffField x) (u.grad x)) (z.grad x)
  let fZ : Vec d → ℝ :=
    fun x =>
      vecDot (z.grad x) (matVecMul (a.toCoeffField x) (z.grad x))
  have hfU : MeasureTheory.IntegrableOn fU Uset := by
    simpa [fU, Uset] using
      integrableOn_symmetricDirichletIntegrand_of_isEllipticFieldOn
        (U := Uset) hEll u
  have hfW : MeasureTheory.IntegrableOn fW Uset := by
    simpa [fW, Uset] using
      integrableOn_symmetricDirichletIntegrand_of_isEllipticFieldOn
        (U := Uset) hEll w
  have hfluxMem :
      MemVectorL2 Uset
        (fun x => matVecMul (a.toCoeffField x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hfCross : MeasureTheory.IntegrableOn fCross Uset := by
    simpa [fCross, Uset] using
      integrableOn_vecDot_of_memVectorL2 hfluxMem z.grad_memVectorL2
  have hfZ : MeasureTheory.IntegrableOn fZ Uset := by
    simpa [fZ, Uset] using
      integrableOn_h1_coefficientEnergyDensity hEll z
  rcases exists_zeroTraceGradientAE_of_dirichlet_difference U a hu hw with
    ⟨θ, hθ⟩
  have hcrossZero : volumeAverage Uset fCross = 0 := by
    apply volumeAverage_eq_zero_of_integral_eq_zero
    calc
      ∫ x in Uset, fCross x ∂MeasureTheory.volume =
          ∫ x in Uset,
            vecDot (matVecMul (a.toCoeffField x) (u.grad x))
              (θ.toH1Function.grad x) ∂MeasureTheory.volume := by
            refine MeasureTheory.integral_congr_ae ?_
            exact hθ.mono fun x hx => by
              have hxz : z.grad x = θ.toH1Function.grad x := by
                simpa [z] using hx
              simp [fCross, hxz]
      _ = 0 := hu.isAHarmonicGradient.2 θ
  have hpoint :
      fW =
        fun x => fU x + fCross x + (1 / 2 : ℝ) * fZ x := by
    funext x
    have hgradW : w.grad x = u.grad x + z.grad x := by
      have hz :
          z.grad x = w.grad x - u.grad x := by
        simp [z]
      rw [hz]
      simp [sub_eq_add_neg]
    have hsymm :
        vecDot (u.grad x)
            (matVecMul (a.toCoeffField x) (z.grad x)) =
          vecDot (matVecMul (a.toCoeffField x) (u.grad x))
            (z.grad x) := by
      calc
        vecDot (u.grad x) (matVecMul (a.toCoeffField x) (z.grad x))
            =
          vecDot (z.grad x) (matVecMul (a.toCoeffField x) (u.grad x)) :=
              vecDot_matVecMul_comm_of_isSymm (ha x) (u.grad x) (z.grad x)
        _ =
          vecDot (matVecMul (a.toCoeffField x) (u.grad x)) (z.grad x) := by
              rw [vecDot_comm]
    have hcommZu :
        vecDot (z.grad x) (matVecMul (a.toCoeffField x) (u.grad x)) =
          vecDot (matVecMul (a.toCoeffField x) (u.grad x)) (z.grad x) := by
      rw [vecDot_comm]
    simp [fU, fW, fCross, fZ, hgradW, matVecMul_add, vecDot_add_left,
      vecDot_add_right, hsymm, hcommZu]
    ring_nf
  have hvalue :
      symmetricDirichletEnergyValue U a w =
        symmetricDirichletEnergyValue U a u +
          (1 / 2 : ℝ) * volumeAverage Uset fZ := by
    calc
      symmetricDirichletEnergyValue U a w =
          volumeAverage Uset fW := rfl
      _ =
          volumeAverage Uset
            (fun x => fU x + fCross x + (1 / 2 : ℝ) * fZ x) := by
            rw [hpoint]
      _ =
          volumeAverage Uset fU +
            volumeAverage Uset fCross +
              volumeAverage Uset ((1 / 2 : ℝ) • fZ) := by
            have hfU_add_cross : MeasureTheory.IntegrableOn (fU + fCross) Uset :=
              hfU.add hfCross
            have hfZ_smul :
                MeasureTheory.IntegrableOn ((1 / 2 : ℝ) • fZ) Uset := by
              simpa [Pi.smul_apply, smul_eq_mul] using!
                (hfZ.const_mul (1 / 2 : ℝ))
            change
              volumeAverage Uset ((fU + fCross) + ((1 / 2 : ℝ) • fZ)) =
                volumeAverage Uset fU +
                  volumeAverage Uset fCross +
                    volumeAverage Uset ((1 / 2 : ℝ) • fZ)
            rw [volumeAverage_add hfU_add_cross hfZ_smul]
            rw [volumeAverage_add hfU hfCross]
      _ =
          symmetricDirichletEnergyValue U a u +
            (1 / 2 : ℝ) * volumeAverage Uset fZ := by
            rw [hcrossZero, volumeAverage_smul]
            change
              volumeAverage Uset fU + 0 + (1 / 2 : ℝ) * volumeAverage Uset fZ =
                volumeAverage Uset fU + (1 / 2 : ℝ) * volumeAverage Uset fZ
            ring
  simpa [fZ, z, Uset] using hvalue

theorem isSymmetricDirichletMinimizer_of_isAffineDirichletSolution
    {d : ℕ} (U : Domain d) (a : CoeffOn U) {p : Vec d}
    {u : H1Function (U : Set (Vec d))}
    (hu : IsAffineDirichletSolution a.toCoeffField (U : Set (Vec d)) p u)
    (ha : IsSymmetricCoeffField a.toCoeffField)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    IsSymmetricDirichletMinimizer U a p u := by
  refine ⟨isSymmetricDirichletAdmissible_of_isAffineDirichletSolution U a hu, ?_⟩
  intro w hw
  let Uset : Set (Vec d) := (U : Set (Vec d))
  let z : H1Function Uset := w - u
  let fZ : Vec d → ℝ :=
    fun x =>
      vecDot (z.grad x) (matVecMul (a.toCoeffField x) (z.grad x))
  have hvalue :=
    symmetricDirichletEnergyValue_eq_of_isAffineDirichletSolution
      U a hu hw ha hEll
  have hvalue' :
      symmetricDirichletEnergyValue U a w =
        symmetricDirichletEnergyValue U a u +
          (1 / 2 : ℝ) * volumeAverage Uset fZ := by
    simpa [fZ, z, Uset] using hvalue
  have hZNonneg : 0 ≤ volumeAverage Uset fZ := by
    apply volumeAverage_nonneg_of_nonneg_on
      (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    have hnonneg :=
      coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll z.grad x hx
    simpa [fZ, coefficientEnergyDensity_eq_unsymmetrized] using hnonneg
  nlinarith [hvalue', hZNonneg]

theorem sameGradientAE_of_isSymmetricDirichletMinimizer_of_isAffineDirichletSolution
    {d : ℕ} (U : Domain d) (a : CoeffOn U) {p : Vec d}
    {u w : H1Function (U : Set (Vec d))}
    (hu : IsAffineDirichletSolution a.toCoeffField (U : Set (Vec d)) p u)
    (ha : IsSymmetricCoeffField a.toCoeffField)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (hw : IsSymmetricDirichletMinimizer U a p w) :
    w.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))] u.grad := by
  let Uset : Set (Vec d) := (U : Set (Vec d))
  let z : H1Function Uset := w - u
  let fZ : Vec d → ℝ :=
    fun x =>
      vecDot (z.grad x) (matVecMul (a.toCoeffField x) (z.grad x))
  have hvalue :=
    symmetricDirichletEnergyValue_eq_of_isAffineDirichletSolution
      U a hu hw.1 ha hEll
  have hvalue' :
      symmetricDirichletEnergyValue U a w =
        symmetricDirichletEnergyValue U a u +
          (1 / 2 : ℝ) * volumeAverage Uset fZ := by
    simpa [fZ, z, Uset] using hvalue
  have hselAdm : IsSymmetricDirichletAdmissible U p u :=
    isSymmetricDirichletAdmissible_of_isAffineDirichletSolution U a hu
  have hZNonneg : 0 ≤ volumeAverage Uset fZ := by
    apply volumeAverage_nonneg_of_nonneg_on
      (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    have hnonneg :=
      coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll z.grad x hx
    simpa [fZ, coefficientEnergyDensity_eq_unsymmetrized] using hnonneg
  have hZLeZero : volumeAverage Uset fZ ≤ 0 := by
    have hmin := hw.2 u hselAdm
    nlinarith [hvalue']
  have hZZero : volumeAverage Uset fZ = 0 :=
    le_antisymm hZLeZero hZNonneg
  have hfZ : MeasureTheory.IntegrableOn fZ Uset := by
    simpa [fZ, z, Uset] using
      integrableOn_h1_coefficientEnergyDensity hEll z
  have hzZero : z.grad =ᵐ[volumeMeasureOn Uset] 0 := by
    simpa [fZ, Uset] using
      h1_grad_eq_zero_ae_of_volumeAverage_energy_eq_zero U a hEll z hfZ hZZero
  filter_upwards [hzZero] with x hx
  have hz :
      z.grad x = w.grad x - u.grad x := by
    simp [z]
  rw [hz] at hx
  exact sub_eq_zero.mp hx

end BookCh02

end

end Ch02
end Internal
end Homogenization
