/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation

/-! # Helpers -/

namespace Homogenization

noncomputable section

/-!
# BlockResponse Equalities -- helpers and existence / volumeAverage

Private blockResponse_upper-add / upper-sub-flux equalities, the big
exists_blockResponsePairHalfState_ae_eq_of_mem_responseSpace_of_lowerImage_isPotential
theorem, and the matching volumeAverage_blockResponseIntegrand_eq_scalarResponse_sum
theorem.
-/

private theorem blockResponse_upper_add_flux_eq_matVecMul_potential_add_lowerImage_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {X : BlockState d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a) {x : Vec d} (hx : x ∈ U) :
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 + X.flux x =
      matVecMul (a x)
        (X.potential x + (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
  let lower :=
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).2
  have hsnd :
      lower =
        matVecMul ((symmPart (a x))⁻¹)
          (X.flux x - matVecMul (skewPart (a x)) (X.potential x)) := by
    simpa [lower, BlockState.eval, blockCoeffField] using
      blockMatVecMul_blockMatrixOfCoeff_snd
        (A := a x) (p := X.potential x) (q := X.flux x)
  have hfst :
      (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 =
        matVecMul (symmPart (a x)) (X.potential x) +
          matVecMul (skewPart (a x)) lower := by
    simpa [lower, hsnd] using!
      blockMatVecMul_blockMatrixOfCoeff_fst
        (A := a x) (p := X.potential x) (q := X.flux x)
  have hflux :
      X.flux x =
        matVecMul (symmPart (a x)) lower +
          matVecMul (skewPart (a x)) (X.potential x) := by
    simpa [lower, BlockState.eval, blockCoeffField] using
      blockMatVecMul_blockMatrixOfCoeff_snd_recover_flux_of_isEllipticMatrix
        (A := a x) (hEll.2 x hx) (p := X.potential x) (q := X.flux x)
  have hsplit : a x = symmPart (a x) + skewPart (a x) := by
    ext i j
    simp [symmPart, skewPart, sub_eq_add_neg]
    ring
  calc
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 + X.flux x =
        (matVecMul (symmPart (a x)) (X.potential x) +
            matVecMul (skewPart (a x)) lower) +
          (matVecMul (symmPart (a x)) lower +
            matVecMul (skewPart (a x)) (X.potential x)) := by
      rw [hfst, hflux]
    _ = matVecMul (symmPart (a x)) (X.potential x + lower) +
          matVecMul (skewPart (a x)) (X.potential x + lower) := by
      rw [matVecMul_add, matVecMul_add]
      abel
    _ = matVecMul ((symmPart (a x)) + skewPart (a x)) (X.potential x + lower) := by
      rw [add_matVecMul]
    _ = matVecMul (a x) (X.potential x + lower) := by
      rw [← hsplit]
    _ = matVecMul (a x)
          (X.potential x + (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
      rfl

private theorem blockResponse_upper_sub_flux_eq_matVecMul_adjoint_potential_sub_lowerImage_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {X : BlockState d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a) {x : Vec d} (hx : x ∈ U) :
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 - X.flux x =
      matVecMul (matTranspose (a x))
        (X.potential x - (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
  let lower :=
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).2
  have hsnd :
      lower =
        matVecMul ((symmPart (a x))⁻¹)
          (X.flux x - matVecMul (skewPart (a x)) (X.potential x)) := by
    simpa [lower, BlockState.eval, blockCoeffField] using
      blockMatVecMul_blockMatrixOfCoeff_snd
        (A := a x) (p := X.potential x) (q := X.flux x)
  have hfst :
      (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 =
        matVecMul (symmPart (a x)) (X.potential x) +
          matVecMul (skewPart (a x)) lower := by
    simpa [lower, hsnd] using!
      blockMatVecMul_blockMatrixOfCoeff_fst
        (A := a x) (p := X.potential x) (q := X.flux x)
  have hflux :
      X.flux x =
        matVecMul (symmPart (a x)) lower +
          matVecMul (skewPart (a x)) (X.potential x) := by
    simpa [lower, BlockState.eval, blockCoeffField] using
      blockMatVecMul_blockMatrixOfCoeff_snd_recover_flux_of_isEllipticMatrix
        (A := a x) (hEll.2 x hx) (p := X.potential x) (q := X.flux x)
  have hsplit :
      matTranspose (a x) = symmPart (a x) - skewPart (a x) := by
    ext i j
    simp [symmPart, skewPart, matTranspose, sub_eq_add_neg]
    ring
  calc
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 - X.flux x =
        (matVecMul (symmPart (a x)) (X.potential x) +
            matVecMul (skewPart (a x)) lower) -
          (matVecMul (symmPart (a x)) lower +
            matVecMul (skewPart (a x)) (X.potential x)) := by
      rw [hfst, hflux]
    _ = matVecMul (symmPart (a x)) (X.potential x - lower) +
          matVecMul (-(skewPart (a x))) (X.potential x - lower) := by
      simp [sub_eq_add_neg, matVecMul_add, matVecMul_neg, neg_matVecMul]
      abel
    _ = matVecMul (symmPart (a x) + -(skewPart (a x))) (X.potential x - lower) := by
      rw [add_matVecMul]
    _ = matVecMul (matTranspose (a x)) (X.potential x - lower) := by
      simpa [sub_eq_add_neg] using
        congrArg (fun A => matVecMul A (X.potential x - lower)) hsplit.symm
    _ = matVecMul (matTranspose (a x))
          (X.potential x - (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
      rfl

theorem exists_blockResponsePairHalfState_ae_eq_of_mem_responseSpace_of_lowerImage_isPotential_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {X : BlockState d} {lam Lam : ℝ} (hU : MeasurableSet U)
    (hX : BlockResponseSpace a U X)
    (hLower :
      IsPotentialOn U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2))
    (hEll : IsEllipticFieldOn lam Lam U a) :
    ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (Homogenization.adjointCoeffField a) U,
        (fun x => (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn U] X.eval := by
  rcases hX.1 with ⟨φ, hφ⟩
  rcases hLower with ⟨ψ, hψ⟩
  let upper : Vec d → Vec d := fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1
  let lower : Vec d → Vec d := fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2
  let ξ : Vec d → Vec d := fun x => φ.grad x + ψ.grad x
  let η : Vec d → Vec d := fun x => φ.grad x - ψ.grad x
  have hLowerPot :
      IsPotentialOn U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := ⟨ψ, hψ⟩
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  have hφL2 : MemVectorL2 U φ.grad := φ.grad_memVectorL2
  have hψL2 : MemVectorL2 U ψ.grad := ψ.grad_memVectorL2
  have hξL2 : MemVectorL2 U ξ := by
    simpa [ξ] using! hφL2.add hψL2
  have hηL2 : MemVectorL2 U η := by
    simpa [η, sub_eq_add_neg] using! hφL2.sub hψL2
  have hξPot : IsPotentialOn U ξ := by
    simpa [ξ, hφ, hψ] using! isPotentialOn_add hX.1 hLowerPot
  have hηPot : IsPotentialOn U η := by
    simpa [η, sub_eq_add_neg, hφ, hψ] using!
      isPotentialOn_add hX.1 (isPotentialOn_smul hLowerPot (-1 : ℝ))
  have hFluxL2 : MemVectorL2 U X.flux :=
    blockResponse_flux_memL2_of_lowerImage_isPotential_of_mem_responseSpace_of_isEllipticFieldOn
      hX hLowerPot hEll
  have hAξL2 : MemVectorL2 U (fun x => matVecMul (a x) (ξ x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hξL2
  have hATηL2 :
      MemVectorL2 U (fun x => matVecMul (matTranspose (a x)) (η x)) := by
    simpa [Homogenization.adjointCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEllAdj hηL2
  have hUpperEq :
      upper =ᵐ[volumeMeasureOn U] fun x => matVecMul (a x) (ξ x) - X.flux x := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    have hφx : φ.grad x = X.potential x := congrFun hφ x
    have hψx : ψ.grad x = lower x := congrFun hψ x
    apply (eq_sub_iff_add_eq).2
    simpa [upper, ξ, lower, hφx, hψx, sub_eq_add_neg] using
      blockResponse_upper_add_flux_eq_matVecMul_potential_add_lowerImage_of_isEllipticFieldOn
        (X := X) hEll hx
  have hUpperL2 : MemVectorL2 U upper := by
    have hUpper' : MemVectorL2 U (fun x => matVecMul (a x) (ξ x) - X.flux x) := by
      simpa [sub_eq_add_neg] using! hAξL2.sub hFluxL2
    have hUpperMeas :
        MeasureTheory.AEStronglyMeasurable upper (volumeMeasureOn U) :=
      hUpper'.1.congr hUpperEq.symm
    refine hUpper'.congr_norm hUpperMeas ?_
    filter_upwards [hUpperEq] with x hx
    simpa using congrArg norm hx.symm
  have hFluxInt :
      ∀ θ : H10Function U,
        MeasureTheory.IntegrableOn
          (fun x => vecDot (X.flux x) (θ.toH1Function.grad x)) U := by
    intro θ
    exact integrableOn_vecDot_of_memVectorL2 hFluxL2 θ.toH1Function.grad_memVectorL2
  have hUpperInt :
      ∀ θ : H10Function U,
        MeasureTheory.IntegrableOn
          (fun x => vecDot (upper x) (θ.toH1Function.grad x)) U := by
    intro θ
    exact integrableOn_vecDot_of_memVectorL2 hUpperL2 θ.toH1Function.grad_memVectorL2
  have hATηEq :
      (fun x => matVecMul (matTranspose (a x)) (η x)) =ᵐ[volumeMeasureOn U]
        (fun x => upper x - X.flux x) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    have hφx : φ.grad x = X.potential x := congrFun hφ x
    have hψx : ψ.grad x = lower x := congrFun hψ x
    simpa [η, hφx, hψx, lower, upper, sub_eq_add_neg] using
      (blockResponse_upper_sub_flux_eq_matVecMul_adjoint_potential_sub_lowerImage_of_isEllipticFieldOn
        (X := X) hEll hx
      ).symm
  have hξSol : IsSolenoidalOn U (fun x => matVecMul (a x) (ξ x)) := by
    intro θ
    have hsum :
        IsSolenoidalOn U (fun x => upper x + X.flux x) :=
      isSolenoidalOn_add
        (blockResponse_upperImage_isSolenoidalOn_of_mem_responseSpace (hX := hX))
        hX.2.1 hUpperInt hFluxInt
    have hEqInt :
        ∫ x in U, vecDot (matVecMul (a x) (ξ x)) (θ.toH1Function.grad x) ∂MeasureTheory.volume =
          ∫ x in U, vecDot ((upper x + X.flux x)) (θ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
      have hφx : φ.grad x = X.potential x := congrFun hφ x
      have hψx : ψ.grad x = lower x := congrFun hψ x
      have hx' :=
        blockResponse_upper_add_flux_eq_matVecMul_potential_add_lowerImage_of_isEllipticFieldOn
          (X := X) hEll hx
      simpa [ξ, hφx, hψx, lower, upper, vecDot_add_left] using
        congrArg (fun z => vecDot z (θ.toH1Function.grad x)) hx'.symm
    rw [hEqInt]
    exact hsum θ
  have hηSol : IsSolenoidalOn U (fun x => matVecMul (matTranspose (a x)) (η x)) := by
    have hNegFluxInt :
        ∀ θ : H10Function U,
          MeasureTheory.IntegrableOn
            (fun x => vecDot ((-1 : ℝ) • X.flux x) (θ.toH1Function.grad x)) U := by
      intro θ
      have hneg :
          MeasureTheory.IntegrableOn
            (fun x => -(vecDot (X.flux x) (θ.toH1Function.grad x))) U := by
        exact (hFluxInt θ).neg
      simpa [Pi.smul_apply, vecDot_neg_left] using hneg
    intro θ
    have hsum :
        IsSolenoidalOn U (fun x => upper x + (-1 : ℝ) • X.flux x) :=
      isSolenoidalOn_add
        (blockResponse_upperImage_isSolenoidalOn_of_mem_responseSpace (hX := hX))
        (isSolenoidalOn_smul hX.2.1 (-1 : ℝ)) hUpperInt hNegFluxInt
    have hEqInt :
        ∫ x in U, vecDot (matVecMul (matTranspose (a x)) (η x)) (θ.toH1Function.grad x)
            ∂MeasureTheory.volume =
          ∫ x in U, vecDot (upper x + (-1 : ℝ) • X.flux x) (θ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hU, hATηEq] with x hx hEq
      simpa [upper, vecDot_add_left, vecDot_smul_left, sub_eq_add_neg] using
        congrArg (fun z => vecDot z (θ.toH1Function.grad x)) hEq
    rw [hEqInt]
    simpa [Pi.smul_apply, vecDot_add_left, vecDot_smul_left] using hsum θ
  let u : AHarmonicFunction a U :=
    { toH1 := φ + ψ
      isHarmonic := by
        simpa [ξ] using! And.intro hξPot hξSol }
  let v : AHarmonicFunction (Homogenization.adjointCoeffField a) U :=
    { toH1 := φ + (-1 : ℝ) • ψ
      isHarmonic := by
        have hηPot' :
            IsPotentialOn U ((φ + (-1 : ℝ) • ψ).grad) := by
          change IsPotentialOn U (fun x => φ.grad x + (-1 : ℝ) • ψ.grad x)
          simpa [η, sub_eq_add_neg, Pi.smul_apply] using hηPot
        have hηSol' :
            IsSolenoidalOn U
              (fun x =>
                matVecMul ((Homogenization.adjointCoeffField a) x)
                  ((φ + (-1 : ℝ) • ψ).grad x)) := by
          change IsSolenoidalOn U
            (fun x => matVecMul (matTranspose (a x)) (φ.grad x + (-1 : ℝ) • ψ.grad x))
          simpa [Homogenization.adjointCoeffField, η, sub_eq_add_neg, Pi.smul_apply] using hηSol
        exact ⟨hηPot', hηSol'⟩ }
  have hPairPotEqAt :
      ∀ x, (blockResponsePairHalfState a u v).potential x = X.potential x := by
    intro x
    ext i
    have hφxi : φ.grad x i = X.potential x i := congrArg (fun z => z i) (congrFun hφ x)
    change
      (1 / 2 : ℝ) *
          ((φ.grad x i + ψ.grad x i) + (φ.grad x i + (-1 : ℝ) * ψ.grad x i)) =
        X.potential x i
    ring_nf
    exact hφxi
  have hHalfGradDiffEq :
      (fun x => (1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x)) = ψ.grad := by
    funext x
    ext i
    change
      (1 / 2 : ℝ) *
          ((φ.grad x i + ψ.grad x i) - (φ.grad x i + (-1 : ℝ) * ψ.grad x i)) =
        ψ.grad x i
    ring
  have hLowerPair :
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((blockResponsePairHalfState a u v).eval x)).2) =ᵐ[volumeMeasureOn U]
        ψ.grad := by
    exact
      (blockResponse_lowerImage_pair_half_ae_eq_gradDiff_of_isEllipticFieldOn
        (a := a) hEll u v).trans (Filter.EventuallyEq.of_eq hHalfGradDiffEq)
  have hPairFluxEq :
      (blockResponsePairHalfState a u v).flux =ᵐ[volumeMeasureOn U] X.flux := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU, hLowerPair] with x hx hLowerX
    have hψx : ψ.grad x = lower x := congrFun hψ x
    have hRecoverPair :
        (blockResponsePairHalfState a u v).flux x =
          matVecMul (symmPart (a x))
              ((blockMatVecMul (blockCoeffField a x)
                ((blockResponsePairHalfState a u v).eval x)).2) +
            matVecMul (skewPart (a x)) ((blockResponsePairHalfState a u v).potential x) := by
      simpa [BlockState.eval, blockCoeffField] using
        blockMatVecMul_blockMatrixOfCoeff_snd_recover_flux_of_isEllipticMatrix
          (A := a x) (hEll.2 x hx)
          (p := (blockResponsePairHalfState a u v).potential x)
          (q := (blockResponsePairHalfState a u v).flux x)
    have hRecoverX :
        X.flux x =
          matVecMul (symmPart (a x))
              ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2) +
            matVecMul (skewPart (a x)) (X.potential x) := by
      simpa [BlockState.eval, blockCoeffField] using
        blockMatVecMul_blockMatrixOfCoeff_snd_recover_flux_of_isEllipticMatrix
          (A := a x) (hEll.2 x hx) (p := X.potential x) (q := X.flux x)
    calc
      (blockResponsePairHalfState a u v).flux x =
          matVecMul (symmPart (a x))
              ((blockMatVecMul (blockCoeffField a x)
                ((blockResponsePairHalfState a u v).eval x)).2) +
            matVecMul (skewPart (a x)) ((blockResponsePairHalfState a u v).potential x) := hRecoverPair
      _ = matVecMul (symmPart (a x)) (ψ.grad x) + matVecMul (skewPart (a x)) (X.potential x) := by
            rw [hLowerX, hPairPotEqAt x]
      _ = X.flux x := by
            symm
            simpa [hψx, lower] using hRecoverX
  have hPairPotEq :
      (blockResponsePairHalfState a u v).potential = X.potential := by
    funext x
    exact hPairPotEqAt x
  have hPairEvalEq :
      (fun x => (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn U] X.eval := by
    filter_upwards [hPairFluxEq] with x hflux
    exact Prod.ext (congrFun hPairPotEq x) hflux
  exact ⟨u, v, hPairEvalEq⟩

/-- Preferred convex-domain reverse-inclusion wrapper for response states whose
lower image is known to be `L²`. This is the note-facing way to reconstruct the
primal/adjoint harmonic half-pair from a block-response state without manually
supplying a lower-image potential representative. -/
theorem exists_blockResponsePairHalfState_ae_eq_of_mem_responseSpace_of_lowerImage_memVectorL2_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {X : BlockState d} (hConv : IsOpenBoundedConvexDomain U)
    (hX : BlockResponseSpace a U X)
    (hLowerL2 :
      MemVectorL2 U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2))
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a) :
    ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (Homogenization.adjointCoeffField a) U,
        (fun x => (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn U] X.eval := by
  have hLower :
      IsPotentialOn U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) :=
    blockResponse_lowerImage_isPotential_of_mem_responseSpace_of_memVectorL2_of_isOpenBoundedConvexDomain
      (U := U) hConv hX hLowerL2
  exact
    exists_blockResponsePairHalfState_ae_eq_of_mem_responseSpace_of_lowerImage_isPotential_of_isEllipticFieldOn
      (a := a) hConv.isOpen.measurableSet hX hLower hEll

/-- Preferred convex-domain reverse-inclusion wrapper for integrable response
states. Since `BlockResponseIntegrabilityData` supplies the flux `L²` control,
this packages the lower-image promotion and half-pair reconstruction into one
standalone theorem. -/
theorem exists_blockResponsePairHalfState_ae_eq_of_mem_responseSpace_of_integrabilityData_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {X : BlockState d} (hConv : IsOpenBoundedConvexDomain U)
    (hX : BlockResponseSpace a U X)
    (hInt : BlockResponseIntegrabilityData U a X)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a) :
    ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (Homogenization.adjointCoeffField a) U,
        (fun x => (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn U] X.eval := by
  have hLowerL2 :
      MemVectorL2 U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) :=
    blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
      hX hInt.flux_memL2 hEll
  exact
    exists_blockResponsePairHalfState_ae_eq_of_mem_responseSpace_of_lowerImage_memVectorL2_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (a := a) hConv hX hLowerL2 hEll

theorem volumeAverage_blockResponseIntegrand_eq_scalarResponse_sum_of_mem_responseSpace_of_lowerImage_isPotential_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {X : BlockState d} {lam Lam : ℝ} (hU : MeasurableSet U)
    (hX : BlockResponseSpace a U X)
    (hLower :
      IsPotentialOn U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2))
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p pStar q qStar : Vec d) :
    ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (Homogenization.adjointCoeffField a) U,
        volumeAverage U (blockResponseIntegrand a (p, q) (qStar, pStar) X) =
          (1 / 2 : ℝ) * volumeAverage U (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) +
            (1 / 2 : ℝ) *
              volumeAverage U
                (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
                  (pStar + p) (qStar + q) v) := by
  rcases hX.1 with ⟨φ, hφ⟩
  rcases hLower with ⟨ψ, hψ⟩
  let upper : Vec d → Vec d := fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1
  let lower : Vec d → Vec d := fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2
  let ξ : Vec d → Vec d := fun x => φ.grad x + ψ.grad x
  let η : Vec d → Vec d := fun x => φ.grad x - ψ.grad x
  have hLowerPot :
      IsPotentialOn U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := ⟨ψ, hψ⟩
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  have hφL2 : MemVectorL2 U φ.grad := φ.grad_memVectorL2
  have hψL2 : MemVectorL2 U ψ.grad := ψ.grad_memVectorL2
  have hξL2 : MemVectorL2 U ξ := by
    simpa [ξ] using! hφL2.add hψL2
  have hηL2 : MemVectorL2 U η := by
    simpa [η, sub_eq_add_neg] using! hφL2.sub hψL2
  have hξPot : IsPotentialOn U ξ := by
    simpa [ξ, hφ, hψ] using! isPotentialOn_add hX.1 hLowerPot
  have hηPot : IsPotentialOn U η := by
    simpa [η, sub_eq_add_neg, hφ, hψ] using!
      isPotentialOn_add hX.1 (isPotentialOn_smul hLowerPot (-1 : ℝ))
  have hFluxL2 : MemVectorL2 U X.flux :=
    blockResponse_flux_memL2_of_lowerImage_isPotential_of_mem_responseSpace_of_isEllipticFieldOn
      hX hLowerPot hEll
  have hAξL2 : MemVectorL2 U (fun x => matVecMul (a x) (ξ x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hξL2
  have hATηL2 :
      MemVectorL2 U (fun x => matVecMul (matTranspose (a x)) (η x)) := by
    simpa [Homogenization.adjointCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEllAdj hηL2
  have hUpperEq :
      upper =ᵐ[volumeMeasureOn U] fun x => matVecMul (a x) (ξ x) - X.flux x := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    have hφx : φ.grad x = X.potential x := congrFun hφ x
    have hψx : ψ.grad x = lower x := congrFun hψ x
    apply (eq_sub_iff_add_eq).2
    simpa [upper, ξ, lower, hφx, hψx, sub_eq_add_neg] using
      blockResponse_upper_add_flux_eq_matVecMul_potential_add_lowerImage_of_isEllipticFieldOn
        (X := X) hEll hx
  have hUpperL2 : MemVectorL2 U upper := by
    have hUpper' : MemVectorL2 U (fun x => matVecMul (a x) (ξ x) - X.flux x) := by
      simpa [sub_eq_add_neg] using! hAξL2.sub hFluxL2
    have hUpperMeas :
        MeasureTheory.AEStronglyMeasurable upper (volumeMeasureOn U) :=
      hUpper'.1.congr hUpperEq.symm
    refine hUpper'.congr_norm hUpperMeas ?_
    filter_upwards [hUpperEq] with x hx
    simpa using congrArg norm hx.symm
  have hFluxInt :
      ∀ θ : H10Function U,
        MeasureTheory.IntegrableOn
          (fun x => vecDot (X.flux x) (θ.toH1Function.grad x)) U := by
    intro θ
    exact integrableOn_vecDot_of_memVectorL2 hFluxL2 θ.toH1Function.grad_memVectorL2
  have hUpperInt :
      ∀ θ : H10Function U,
        MeasureTheory.IntegrableOn
          (fun x => vecDot (upper x) (θ.toH1Function.grad x)) U := by
    intro θ
    exact integrableOn_vecDot_of_memVectorL2 hUpperL2 θ.toH1Function.grad_memVectorL2
  have hATηEq :
      (fun x => matVecMul (matTranspose (a x)) (η x)) =ᵐ[volumeMeasureOn U]
        (fun x => upper x - X.flux x) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    have hφx : φ.grad x = X.potential x := congrFun hφ x
    have hψx : ψ.grad x = lower x := congrFun hψ x
    simpa [η, hφx, hψx, lower, upper, sub_eq_add_neg] using
      (blockResponse_upper_sub_flux_eq_matVecMul_adjoint_potential_sub_lowerImage_of_isEllipticFieldOn
        (X := X) hEll hx
      ).symm
  have hξSol : IsSolenoidalOn U (fun x => matVecMul (a x) (ξ x)) := by
    intro θ
    have hsum :
        IsSolenoidalOn U (fun x => upper x + X.flux x) :=
      isSolenoidalOn_add
        (blockResponse_upperImage_isSolenoidalOn_of_mem_responseSpace (hX := hX))
        hX.2.1 hUpperInt hFluxInt
    have hEqInt :
        ∫ x in U, vecDot (matVecMul (a x) (ξ x)) (θ.toH1Function.grad x) ∂MeasureTheory.volume =
          ∫ x in U, vecDot ((upper x + X.flux x)) (θ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
      have hφx : φ.grad x = X.potential x := congrFun hφ x
      have hψx : ψ.grad x = lower x := congrFun hψ x
      have hx' :=
        blockResponse_upper_add_flux_eq_matVecMul_potential_add_lowerImage_of_isEllipticFieldOn
          (X := X) hEll hx
      simpa [ξ, hφx, hψx, lower, upper, vecDot_add_left] using
        congrArg (fun z => vecDot z (θ.toH1Function.grad x)) hx'.symm
    rw [hEqInt]
    exact hsum θ
  have hηSol : IsSolenoidalOn U (fun x => matVecMul (matTranspose (a x)) (η x)) := by
    have hNegFluxInt :
        ∀ θ : H10Function U,
          MeasureTheory.IntegrableOn
            (fun x => vecDot ((-1 : ℝ) • X.flux x) (θ.toH1Function.grad x)) U := by
      intro θ
      have hneg :
          MeasureTheory.IntegrableOn
            (fun x => -(vecDot (X.flux x) (θ.toH1Function.grad x))) U := by
        exact (hFluxInt θ).neg
      simpa [Pi.smul_apply, vecDot_neg_left] using hneg
    intro θ
    have hsum :
        IsSolenoidalOn U (fun x => upper x + (-1 : ℝ) • X.flux x) :=
      isSolenoidalOn_add
        (blockResponse_upperImage_isSolenoidalOn_of_mem_responseSpace (hX := hX))
        (isSolenoidalOn_smul hX.2.1 (-1 : ℝ)) hUpperInt hNegFluxInt
    have hEqInt :
        ∫ x in U, vecDot (matVecMul (matTranspose (a x)) (η x)) (θ.toH1Function.grad x)
            ∂MeasureTheory.volume =
          ∫ x in U, vecDot (upper x + (-1 : ℝ) • X.flux x) (θ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hU, hATηEq] with x hx hEq
      simpa [upper, vecDot_add_left, vecDot_smul_left, sub_eq_add_neg] using
        congrArg (fun z => vecDot z (θ.toH1Function.grad x)) hEq
    rw [hEqInt]
    simpa [Pi.smul_apply, vecDot_add_left, vecDot_smul_left] using hsum θ
  let u : AHarmonicFunction a U :=
    { toH1 := φ + ψ
      isHarmonic := by
        simpa [ξ] using! And.intro hξPot hξSol }
  let v : AHarmonicFunction (Homogenization.adjointCoeffField a) U :=
    { toH1 := φ + (-1 : ℝ) • ψ
      isHarmonic := by
        have hηPot' :
            IsPotentialOn U ((φ + (-1 : ℝ) • ψ).grad) := by
          change IsPotentialOn U (fun x => φ.grad x + (-1 : ℝ) • ψ.grad x)
          simpa [η, sub_eq_add_neg, Pi.smul_apply] using hηPot
        have hηSol' :
            IsSolenoidalOn U
              (fun x =>
                matVecMul ((Homogenization.adjointCoeffField a) x)
                  ((φ + (-1 : ℝ) • ψ).grad x)) := by
          change IsSolenoidalOn U
            (fun x => matVecMul (matTranspose (a x)) (φ.grad x + (-1 : ℝ) • ψ.grad x))
          simpa [Homogenization.adjointCoeffField, η, sub_eq_add_neg, Pi.smul_apply] using hηSol
        exact ⟨hηPot', hηSol'⟩ }
  have hPairPotEqAt :
      ∀ x, (blockResponsePairHalfState a u v).potential x = X.potential x := by
    intro x
    ext i
    have hφxi : φ.grad x i = X.potential x i := congrArg (fun z => z i) (congrFun hφ x)
    change
      (1 / 2 : ℝ) *
          ((φ.grad x i + ψ.grad x i) + (φ.grad x i + (-1 : ℝ) * ψ.grad x i)) =
        X.potential x i
    ring_nf
    exact hφxi
  have hHalfGradDiffEq :
      (fun x => (1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x)) = ψ.grad := by
    funext x
    ext i
    change
      (1 / 2 : ℝ) *
          ((φ.grad x i + ψ.grad x i) - (φ.grad x i + (-1 : ℝ) * ψ.grad x i)) =
        ψ.grad x i
    ring
  have hLowerPair :
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((blockResponsePairHalfState a u v).eval x)).2) =ᵐ[volumeMeasureOn U]
        ψ.grad := by
    exact
      (blockResponse_lowerImage_pair_half_ae_eq_gradDiff_of_isEllipticFieldOn
        (a := a) hEll u v).trans (Filter.EventuallyEq.of_eq hHalfGradDiffEq)
  have hPairFluxEq :
      (blockResponsePairHalfState a u v).flux =ᵐ[volumeMeasureOn U] X.flux := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU, hLowerPair] with x hx hLowerX
    have hψx : ψ.grad x = lower x := congrFun hψ x
    have hRecoverPair :
        (blockResponsePairHalfState a u v).flux x =
          matVecMul (symmPart (a x))
              ((blockMatVecMul (blockCoeffField a x)
                ((blockResponsePairHalfState a u v).eval x)).2) +
            matVecMul (skewPart (a x)) ((blockResponsePairHalfState a u v).potential x) := by
      simpa [BlockState.eval, blockCoeffField] using
        blockMatVecMul_blockMatrixOfCoeff_snd_recover_flux_of_isEllipticMatrix
          (A := a x) (hEll.2 x hx)
          (p := (blockResponsePairHalfState a u v).potential x)
          (q := (blockResponsePairHalfState a u v).flux x)
    have hRecoverX :
        X.flux x =
          matVecMul (symmPart (a x))
              ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2) +
            matVecMul (skewPart (a x)) (X.potential x) := by
      simpa [BlockState.eval, blockCoeffField] using
        blockMatVecMul_blockMatrixOfCoeff_snd_recover_flux_of_isEllipticMatrix
          (A := a x) (hEll.2 x hx) (p := X.potential x) (q := X.flux x)
    calc
      (blockResponsePairHalfState a u v).flux x =
          matVecMul (symmPart (a x))
              ((blockMatVecMul (blockCoeffField a x)
                ((blockResponsePairHalfState a u v).eval x)).2) +
            matVecMul (skewPart (a x)) ((blockResponsePairHalfState a u v).potential x) := hRecoverPair
      _ = matVecMul (symmPart (a x)) (ψ.grad x) + matVecMul (skewPart (a x)) (X.potential x) := by
            rw [hLowerX, hPairPotEqAt x]
      _ = X.flux x := by
            symm
            simpa [hψx, lower] using hRecoverX
  have hPairPotEq :
      (blockResponsePairHalfState a u v).potential = X.potential := by
    funext x
    exact hPairPotEqAt x
  have hPairEvalEq :
      (fun x => (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn U] X.eval := by
    filter_upwards [hPairFluxEq] with x hflux
    exact Prod.ext (congrFun hPairPotEq x) hflux
  have hIntegrandEq :
      blockResponseIntegrand a (p, q) (qStar, pStar) (blockResponsePairHalfState a u v) =ᵐ[volumeMeasureOn U]
        blockResponseIntegrand a (p, q) (qStar, pStar) X := by
    filter_upwards [hPairEvalEq] with x hx
    simpa [blockResponseIntegrand, blockEnergyDensity] using congrArg
      (fun z => -(1 / 2 : ℝ) * blockVecDot z (blockMatVecMul (blockCoeffField a x) z)
        - blockVecDot (p, q) (blockMatVecMul (blockCoeffField a x) z) +
          blockVecDot (qStar, pStar) z) hx
  refine ⟨u, v, ?_⟩
  have hAvgEq :
      volumeAverage U
          (blockResponseIntegrand a (p, q) (qStar, pStar) (blockResponsePairHalfState a u v)) =
        volumeAverage U (blockResponseIntegrand a (p, q) (qStar, pStar) X) := by
    unfold volumeAverage
    congr 1
    exact MeasureTheory.integral_congr_ae hIntegrandEq
  rw [← hAvgEq]
  exact
    volumeAverage_blockResponseIntegrand_pair_half_eq_scalarResponse_sum_of_isEllipticFieldOn
      (a := a) hU hEll p pStar q qStar u v


end

end Homogenization
