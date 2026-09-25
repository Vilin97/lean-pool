/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# The direct rotation as an exponential: `U = exp (J Θ)`

Davis--Kahan close Section 3 with the statement that the direct rotation is the
exponential of `J Θ`.  This module proves it in the finite-dimensional setting,
for the `J` of `DavisKahan/FiniteDimensional/DirectRotation.lean`.

The proof is the classical one, carried out on the eigenbasis of `sin Θ`:

* `angleComplexStructure_comp_angleOperator_comp_self` — `(J Θ)² = -Θ²`, from
  `J² = -(sin Θ)(sin Θ)⁺` (`angleComplexStructure_comp_self`) together with the
  fact that the Penrose projection `(sin Θ)(sin Θ)⁺` fixes `Θ`;
* `directRotationCosine_eq_calculus` — `cos Θ` really is the cosine of `Θ`: it is
  the functional calculus of `s ↦ cos (arcsin s)` applied to `sin Θ`, which needs
  the spectral bound `sinAngleOperator_eigenvalues_mem_Icc`;
* the exponential series then splits into its even and odd parts, which are the
  power series of `cos` and `sin` evaluated at the principal angles.

Everything is stated on `E →L[𝕜] E`, since that — and not `E →ₗ[𝕜] E` — is where
Mathlib's `NormedSpace.exp` lives.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators Nat
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

section AngleSpectrum

variable (U V : Submodule 𝕜 E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- `sin Θ` is self-adjoint: it is the modulus of the self-adjoint difference of
the two orthogonal projections. -/
theorem isSymmetric_sinAngleOperator : (sinAngleOperator U V).IsSymmetric :=
  (TauCeti.isPositive_operatorAbs (projection U - projection V)).isSymmetric

/-- `Θ` is the arcsine functional calculus of `sin Θ`.  This is the definition of
`angleOperator`, restated so that it can be used with any symmetry witness. -/
theorem angleOperator_eq_calculus (hsin : (sinAngleOperator U V).IsSymmetric) :
    angleOperator U V = TauCeti.selfAdjointFunctionalCalculus hsin Real.arcsin :=
  rfl

/-- Operator Pythagoras in the solved form `cos²Θ = 1 - sin²Θ`. -/
theorem directRotationCosine_comp_self_eq :
    directRotationCosine U V ∘ₗ directRotationCosine U V =
      LinearMap.id - sinAngleOperator U V ∘ₗ sinAngleOperator U V :=
  eq_sub_of_add_eq' (sq_sinAngleOperator_add_sq_directRotationCosine U V)

/-- `1 - sin²Θ` is a positive operator: it is `cos²Θ`, and `cos Θ` is self-adjoint. -/
theorem isPositive_one_sub_sq_sinAngleOperator :
    (LinearMap.id - sinAngleOperator U V ∘ₗ sinAngleOperator U V : E →ₗ[𝕜] E).IsPositive := by
  rw [← directRotationCosine_comp_self_eq U V]
  have hCsym : (directRotationCosine U V).IsSymmetric :=
    (TauCeti.isPositive_operatorAbs (canonicalIntertwiner U V)).isSymmetric
  have h := LinearMap.isPositive_adjoint_comp_self (directRotationCosine U V)
  rwa [hCsym.adjoint_eq] at h

/-- **Every eigenvalue of `sin Θ` lies in `[-1, 1]`.**

The Pythagoras identity makes `1 - sin²Θ` positive, and testing it against a unit
eigenvector of `sin Θ` with eigenvalue `λ` gives `0 ≤ 1 - λ²`.  This is what lets
`arcsin` be inverted on the spectrum. -/
theorem sinAngleOperator_eigenvalues_mem_Icc
    (hsin : (sinAngleOperator U V).IsSymmetric) (i : Fin (finrank 𝕜 E)) :
    hsin.eigenvalues rfl i ∈ Set.Icc (-1 : ℝ) 1 := by
  have hpos := isPositive_one_sub_sq_sinAngleOperator U V
  have hAb : sinAngleOperator U V (hsin.eigenvectorBasis rfl i) =
      ((hsin.eigenvalues rfl i : ℝ) : 𝕜) • hsin.eigenvectorBasis rfl i :=
    hsin.apply_eigenvectorBasis rfl i
  have hbb : ⟪hsin.eigenvectorBasis rfl i, hsin.eigenvectorBasis rfl i⟫_𝕜 = 1 := by
    simp
  have hval : (LinearMap.id - sinAngleOperator U V ∘ₗ sinAngleOperator U V : E →ₗ[𝕜] E)
      (hsin.eigenvectorBasis rfl i) =
      ((1 - (hsin.eigenvalues rfl i : ℝ) ^ 2 : ℝ) : 𝕜) • hsin.eigenvectorBasis rfl i := by
    simp [LinearMap.sub_apply, LinearMap.comp_apply, hAb, smul_smul, sub_smul, sq]
  have hnn := hpos.re_inner_nonneg_left (hsin.eigenvectorBasis rfl i)
  rw [hval, inner_smul_left, RCLike.conj_ofReal, hbb, mul_one, RCLike.ofReal_re] at hnn
  constructor
  · nlinarith [hnn]
  · nlinarith [hnn]

/-- **`cos Θ` is the cosine of `Θ`.**

The positive cosine `|S|` is the functional calculus of `s ↦ cos (arcsin s)`
applied to `sin Θ`.  Both operators are positive and both square to `1 - sin²Θ`,
so uniqueness of the positive square root identifies them.  Squaring the calculus
uses `cos (arcsin λ)² = 1 - λ²`, which needs `|λ| ≤ 1`. -/
theorem directRotationCosine_eq_calculus (hsin : (sinAngleOperator U V).IsSymmetric) :
    directRotationCosine U V =
      TauCeti.selfAdjointFunctionalCalculus hsin (fun s => Real.cos (Real.arcsin s)) := by
  set F := TauCeti.selfAdjointFunctionalCalculus hsin (fun s => Real.cos (Real.arcsin s)) with hF
  have hTpos := isPositive_one_sub_sq_sinAngleOperator U V
  have hCpos : (directRotationCosine U V).IsPositive :=
    TauCeti.isPositive_operatorAbs (canonicalIntertwiner U V)
  have hFpos : F.IsPositive := by
    refine TauCeti.selfAdjointFunctionalCalculus_isPositive hsin fun i => ?_
    rw [Real.cos_arcsin]
    exact Real.sqrt_nonneg _
  have hFsq : F ∘ₗ F = LinearMap.id - sinAngleOperator U V ∘ₗ sinAngleOperator U V := by
    rw [hF, TauCeti.selfAdjointFunctionalCalculus_comp]
    have hcongr : TauCeti.selfAdjointFunctionalCalculus hsin
          (fun s => Real.cos (Real.arcsin s) * Real.cos (Real.arcsin s)) =
        TauCeti.selfAdjointFunctionalCalculus hsin (fun s => 1 - s ^ 2) := by
      refine TauCeti.selfAdjointFunctionalCalculus_congr hsin fun i => ?_
      have hi := sinAngleOperator_eigenvalues_mem_Icc U V hsin i
      rw [Real.cos_arcsin, Real.mul_self_sqrt]
      nlinarith [hi.1, hi.2]
    rw [hcongr]
    have hadd := TauCeti.selfAdjointFunctionalCalculus_add hsin
      (fun s => 1 - s ^ 2) (fun s => s ^ 2)
    have hone : ((fun s : ℝ => 1 - s ^ 2) + fun s : ℝ => s ^ 2) = fun _ : ℝ => (1 : ℝ) := by
      funext s; simp
    rw [hone, TauCeti.selfAdjointFunctionalCalculus_one,
      TauCeti.selfAdjointFunctionalCalculus_pow hsin 2] at hadd
    have hsq : (sinAngleOperator U V) ^ 2 =
        sinAngleOperator U V ∘ₗ sinAngleOperator U V := by
      rw [pow_two]; rfl
    rw [hsq] at hadd
    exact eq_sub_of_add_eq hadd.symm
  have hCsq := directRotationCosine_comp_self_eq U V
  rw [LinearMap.IsPositive.sqrt_unique hTpos hCpos hCsq,
    LinearMap.IsPositive.sqrt_unique hTpos hFpos hFsq]

/-- The Penrose projection of `sin Θ` fixes `Θ`.

`Θ = arcsin (sin Θ)` vanishes wherever `sin Θ` does, so it takes values in the
range of `sin Θ`, which is exactly where `(sin Θ)(sin Θ)⁺` is the identity. -/
theorem sinAngleOperator_comp_moorePenroseInverse_comp_angleOperator
    (hsin : (sinAngleOperator U V).IsSymmetric) :
    (sinAngleOperator U V ∘ₗ
        TauCeti.moorePenroseInverse (sinAngleOperator U V)) ∘ₗ angleOperator U V =
      angleOperator U V := by
  apply (hsin.eigenvectorBasis rfl).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis]
  have hTheta : angleOperator U V (hsin.eigenvectorBasis rfl i) =
      ((Real.arcsin (hsin.eigenvalues rfl i) : ℝ) : 𝕜) • hsin.eigenvectorBasis rfl i := by
    rw [angleOperator_eq_calculus U V hsin]
    exact TauCeti.selfAdjointFunctionalCalculus_apply_eigenvectorBasis hsin Real.arcsin i
  have hAb : sinAngleOperator U V (hsin.eigenvectorBasis rfl i) =
      ((hsin.eigenvalues rfl i : ℝ) : 𝕜) • hsin.eigenvectorBasis rfl i :=
    hsin.apply_eigenvectorBasis rfl i
  by_cases hzero : hsin.eigenvalues rfl i = 0
  · rw [LinearMap.comp_apply, hTheta, hzero, Real.arcsin_zero]
    simp
  · have hpre : sinAngleOperator U V
        ((((hsin.eigenvalues rfl i : ℝ) : 𝕜))⁻¹ • hsin.eigenvectorBasis rfl i) =
        hsin.eigenvectorBasis rfl i := by
      rw [map_smul, hAb, smul_smul,
        inv_mul_cancel₀ (RCLike.ofReal_ne_zero.mpr hzero), one_smul]
    have hfix : (sinAngleOperator U V ∘ₗ
        TauCeti.moorePenroseInverse (sinAngleOperator U V))
          (hsin.eigenvectorBasis rfl i) = hsin.eigenvectorBasis rfl i := by
      calc (sinAngleOperator U V ∘ₗ
            TauCeti.moorePenroseInverse (sinAngleOperator U V))
              (hsin.eigenvectorBasis rfl i)
          = (sinAngleOperator U V ∘ₗ
              TauCeti.moorePenroseInverse (sinAngleOperator U V))
                (sinAngleOperator U V
                  ((((hsin.eigenvalues rfl i : ℝ) : 𝕜))⁻¹ •
                    hsin.eigenvectorBasis rfl i)) := by rw [hpre]
        _ = (sinAngleOperator U V ∘ₗ
              TauCeti.moorePenroseInverse (sinAngleOperator U V) ∘ₗ sinAngleOperator U V)
                ((((hsin.eigenvalues rfl i : ℝ) : 𝕜))⁻¹ • hsin.eigenvectorBasis rfl i) := rfl
        _ = sinAngleOperator U V
                ((((hsin.eigenvalues rfl i : ℝ) : 𝕜))⁻¹ • hsin.eigenvectorBasis rfl i) :=
              LinearMap.congr_fun
                (TauCeti.comp_moorePenroseInverse_comp (sinAngleOperator U V)) _
        _ = hsin.eigenvectorBasis rfl i := hpre
    rw [LinearMap.comp_apply, hTheta, map_smul, hfix]

end AngleSpectrum

section Exponential

variable (U V : Submodule 𝕜 E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **`(J Θ)² = -Θ²`.**

`J` commutes with `Θ`, so `(JΘ)² = J²Θ²`; and `J² = -(sin Θ)(sin Θ)⁺` while the
Penrose projection `(sin Θ)(sin Θ)⁺` fixes `Θ`.  This is the identity that makes
the exponential series collapse to a cosine and a sine. -/
theorem angleComplexStructure_comp_angleOperator_comp_self (hacute : IsAcute U V) :
    (angleComplexStructure U V hacute ∘ₗ angleOperator U V) ∘ₗ
        (angleComplexStructure U V hacute ∘ₗ angleOperator U V) =
      -(angleOperator U V ∘ₗ angleOperator U V) := by
  have hmul : ∀ f g : E →ₗ[𝕜] E, f ∘ₗ g = f * g := fun _ _ => rfl
  have hsin := isSymmetric_sinAngleOperator U V
  have hcomm : angleComplexStructure U V hacute * angleOperator U V =
      angleOperator U V * angleComplexStructure U V hacute := by
    simpa [hmul] using angleOperator_comm_angleComplexStructure U V hacute
  have hJJ : angleComplexStructure U V hacute * angleComplexStructure U V hacute =
      -(sinAngleOperator U V * TauCeti.moorePenroseInverse (sinAngleOperator U V)) := by
    simpa [hmul] using angleComplexStructure_comp_self U V hacute
  have hPT : (sinAngleOperator U V *
      TauCeti.moorePenroseInverse (sinAngleOperator U V)) * angleOperator U V =
      angleOperator U V := by
    simpa [hmul] using
      sinAngleOperator_comp_moorePenroseInverse_comp_angleOperator U V hsin
  simp only [hmul]
  calc angleComplexStructure U V hacute * angleOperator U V *
        (angleComplexStructure U V hacute * angleOperator U V)
      = angleComplexStructure U V hacute *
        (angleOperator U V * angleComplexStructure U V hacute) * angleOperator U V := by
        noncomm_ring
    _ = angleComplexStructure U V hacute *
        (angleComplexStructure U V hacute * angleOperator U V) * angleOperator U V := by
        rw [hcomm]
    _ = (angleComplexStructure U V hacute * angleComplexStructure U V hacute) *
        (angleOperator U V * angleOperator U V) := by noncomm_ring
    _ = -((sinAngleOperator U V *
        TauCeti.moorePenroseInverse (sinAngleOperator U V)) *
          (angleOperator U V * angleOperator U V)) := by rw [hJJ]; noncomm_ring
    _ = -(((sinAngleOperator U V *
        TauCeti.moorePenroseInverse (sinAngleOperator U V)) * angleOperator U V) *
          angleOperator U V) := by noncomm_ring
    _ = -(angleOperator U V * angleOperator U V) := by rw [hPT]

/-- **Davis--Kahan's exponential form of the direct rotation: `U = exp (J Θ)`.**

Both sides are computed on the eigenbasis of `sin Θ`.  There `Θ` acts by the
principal angle `θ = arcsin λ` and `(J Θ)²` acts by `-θ²`, so the exponential
series splits into the power series of `cos θ` and of `sin θ`; the first
reassembles `cos Θ` by `directRotationCosine_eq_calculus` and the second
`J sin Θ` because `sin (arcsin λ) = λ`.  The result is `cos Θ + J sin Θ`, which is
the direct rotation by `directRotation_eq_cos_add_J_sin`.

Continuous linear maps carry the statement because that is where Mathlib's
`NormedSpace.exp` is defined; `LinearMap.toContinuousLinearMap` is the
finite-dimensional identification. -/
theorem directRotation_eq_exp_angleComplexStructure_comp_angleOperator
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap.toContinuousLinearMap =
      NormedSpace.exp
        ((angleComplexStructure U V hacute ∘ₗ angleOperator U V).toContinuousLinearMap) := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hsin := isSymmetric_sinAngleOperator U V
  set b := hsin.eigenvectorBasis rfl with hbdef
  set Y : E →ₗ[𝕜] E := angleComplexStructure U V hacute ∘ₗ angleOperator U V with hYdef
  set X : E →L[𝕜] E := Y.toContinuousLinearMap with hXdef
  -- Powers of the continuous map are the powers of the underlying linear map.
  have hXY : ∀ x : E, X x = Y x := fun x => rfl
  have hpow : ∀ (n : ℕ) (x : E), (X ^ n) x = (Y ^ n) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ, pow_succ]
        change (X ^ k) (X x) = (Y ^ k) (Y x)
        rw [hXY, ih]
  -- The exponential series, evaluated at a vector.
  have hexp : ∀ x : E, HasSum (fun n : ℕ => ((n ! : 𝕜))⁻¹ • (Y ^ n) x)
      (NormedSpace.exp X x) := by
    intro x
    have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) X
    have h2 := (ContinuousLinearMap.apply 𝕜 E x).hasSum h
    simpa [hpow] using h2
  have hY2 : Y * Y = -(angleOperator U V * angleOperator U V) :=
    angleComplexStructure_comp_angleOperator_comp_self U V hacute
  have hkey : ∀ i : Fin (finrank 𝕜 E),
      NormedSpace.exp X (b i) = (directRotation U V hacute).toLinearMap (b i) := by
    intro i
    set l : ℝ := hsin.eigenvalues rfl i with hldef
    set θ : ℝ := Real.arcsin l with hθdef
    have hli := sinAngleOperator_eigenvalues_mem_Icc U V hsin i
    have hTheta : angleOperator U V (b i) = ((θ : ℝ) : 𝕜) • b i := by
      rw [angleOperator_eq_calculus U V hsin, hbdef]
      exact TauCeti.selfAdjointFunctionalCalculus_apply_eigenvectorBasis hsin Real.arcsin i
    have hAb : sinAngleOperator U V (b i) = ((l : ℝ) : 𝕜) • b i :=
      hsin.apply_eigenvectorBasis rfl i
    have hYb : Y (b i) = ((θ : ℝ) : 𝕜) • angleComplexStructure U V hacute (b i) := by
      rw [hYdef, LinearMap.comp_apply, hTheta, map_smul]
    -- `(Y²)ᵏ` acts on the eigenvector by `(-θ²)ᵏ`.
    have hstep : (Y * Y) (b i) = ((-(θ ^ 2) : ℝ) : 𝕜) • b i := by
      rw [hY2]
      change -(angleOperator U V (angleOperator U V (b i))) = _
      rw [hTheta, map_smul, hTheta, smul_smul,
        show ((-(θ ^ 2) : ℝ) : 𝕜) = -(((θ : ℝ) : 𝕜) * ((θ : ℝ) : 𝕜)) by push_cast; ring,
        neg_smul]
    have hsqpow : ∀ k : ℕ, ((Y * Y) ^ k) (b i) = (((-(θ ^ 2)) ^ k : ℝ) : 𝕜) • b i := by
      intro k
      induction k with
      | zero => simp
      | succ m ih =>
          rw [pow_succ]
          change ((Y * Y) ^ m) ((Y * Y) (b i)) = _
          rw [hstep, map_smul, ih, smul_smul]
          congr 1
          push_cast
          ring
    have heven : ∀ k : ℕ, (Y ^ (2 * k)) (b i) = (((-(θ ^ 2)) ^ k : ℝ) : 𝕜) • b i := by
      intro k
      rw [pow_mul, pow_two]
      exact hsqpow k
    have hodd : ∀ k : ℕ, (Y ^ (2 * k + 1)) (b i) =
        (((-(θ ^ 2)) ^ k : ℝ) : 𝕜) • Y (b i) := by
      intro k
      rw [pow_succ']
      change Y ((Y ^ (2 * k)) (b i)) = _
      rw [heven k, map_smul]
    -- The even part sums to `cos θ`, the odd part to `sin θ`.
    have hcos : HasSum (fun k : ℕ => (((2 * k)! : 𝕜))⁻¹ • (Y ^ (2 * k)) (b i))
        (((Real.cos θ : ℝ) : 𝕜) • b i) := by
      have hbase :=
        ((RCLike.ofRealCLM (K := 𝕜)).hasSum (Real.hasSum_cos θ)).smul_const (b i)
      simp only [RCLike.ofRealCLM_apply] at hbase
      have hfun : ∀ k : ℕ, (((2 * k)! : 𝕜))⁻¹ • (Y ^ (2 * k)) (b i)
          = (((((-1 : ℝ)) ^ k * θ ^ (2 * k) / ((2 * k)! : ℝ) : ℝ)) : 𝕜) • b i := by
        intro k
        rw [heven k, smul_smul]
        congr 1
        rw [neg_pow, ← pow_mul]
        push_cast
        ring
      simp only [hfun]
      exact hbase
    have hsinsum : HasSum (fun k : ℕ => (((2 * k + 1)! : 𝕜))⁻¹ • (Y ^ (2 * k + 1)) (b i))
        (((Real.sin θ : ℝ) : 𝕜) • angleComplexStructure U V hacute (b i)) := by
      have hbase := ((RCLike.ofRealCLM (K := 𝕜)).hasSum (Real.hasSum_sin θ)).smul_const
        (angleComplexStructure U V hacute (b i))
      simp only [RCLike.ofRealCLM_apply] at hbase
      have hfun : ∀ k : ℕ, (((2 * k + 1)! : 𝕜))⁻¹ • (Y ^ (2 * k + 1)) (b i)
          = (((((-1 : ℝ)) ^ k * θ ^ (2 * k + 1) / ((2 * k + 1)! : ℝ) : ℝ)) : 𝕜) •
              angleComplexStructure U V hacute (b i) := by
        intro k
        rw [hodd k, hYb, smul_smul, smul_smul]
        congr 1
        rw [neg_pow, ← pow_mul]
        push_cast
        ring
      simp only [hfun]
      exact hbase
    have hsum := HasSum.even_add_odd
      (f := fun n : ℕ => ((n ! : 𝕜))⁻¹ • (Y ^ n) (b i)) hcos hsinsum
    have huniq := (hexp (b i)).unique hsum
    rw [huniq, directRotation_eq_cos_add_J_sin U V hacute]
    have hC : directRotationCosine U V (b i) = ((Real.cos θ : ℝ) : 𝕜) • b i := by
      rw [directRotationCosine_eq_calculus U V hsin, hbdef]
      exact TauCeti.selfAdjointFunctionalCalculus_apply_eigenvectorBasis hsin
        (fun s => Real.cos (Real.arcsin s)) i
    have hlsin : Real.sin θ = l := Real.sin_arcsin hli.1 hli.2
    rw [LinearMap.add_apply, hC, LinearMap.comp_apply, hAb, map_smul, hlsin]
  have hLeq : (directRotation U V hacute).toLinearMap =
      (NormedSpace.exp X).toLinearMap := by
    apply (hsin.eigenvectorBasis rfl).toBasis.ext
    intro i
    rw [OrthonormalBasis.coe_toBasis]
    exact (hkey i).symm
  ext x
  have h := LinearMap.congr_fun hLeq x
  simpa using h

end Exponential

end DavisKahan.FiniteDimensional
end TauCeti
