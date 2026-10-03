/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier.Fourier

/-!
# The doubled phase realization over `RCLike`

Seam 3 of 4: the field-uniform half.  A complex phase acts on two orthogonal
copies of a `𝕜`-Hilbert space as a real rotation, so a complex Fourier
interpolation descends to a doubled orbit certificate over `ℝ` and `ℂ` at once —
which is what makes the sharp constant available over the reals, where the
undoubled certificate is refuted (see the obstruction in the root module).

* `basisDoubledPhaseRotation`, the `𝕜`-linear norm-preserving rotation, and the
  scalar actions `doubledComplexScalarMapAction` / `doubledPhaseMapAction`;
* `HasDoubledReciprocalOrbitInterpolation` and its construction from a finite
  Fourier interpolation;
* `finiteUnitaryOrbitCertificate_orthogonalBlockSum_of_doubledInterpolation`, the
  certificate on the doubled space, and the two Ky Fan bounds it yields directly
  (`kyFan_reciprocalMultiplier_le_of_approximateFourierInterpolation` and
  `…_of_integrableKernel`).

## Provenance

*Split, not restated.*  This module was part of
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/Internal/ReciprocalMultiplier.lean`
before that 2887-line file was divided — the largest in
the library, and nearly 3x Tau Ceti's stated 1000-line limit for a new file
(`ForTauCeti/README.md` §4) — along its four mathematical seams.  **No statement,
signature, proof, attribute or declaration name changed**; the split is a file
boundary plus the imports it forces.  The file itself had carried
`set_option linter.style.longFile 2900` and a note saying a split "is not a
migration lane's business"; SPLIT-1K is the lane whose business it is, and the
option is gone from all four parts.

That file in turn was
`DavisKahan/FiniteDimensional/Sylvester/Internal/ReciprocalMultiplier.lean`
before the sin-Θ closure moved into the staging layer.

Literature bridge for the group as a whole:
`prose/distilled_literature/AlbeverioMakarovMotovilov2001_sylvester_fourier_pi_over_two.tex`.
-/

@[expose] public section

namespace TauCeti

open TauCeti
open scoped InnerProductSpace BigOperators ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-! ### Generic doubled phase realization over `RCLike`

A complex phase `exp (i θ)` acts on two orthogonal copies of a `𝕜`-Hilbert
space as the rotation with matrix `[[cos θ, -sin θ], [sin θ, cos θ]]`, whose
entries are real scalars embedded in `𝕜`.  This realization is `𝕜`-linear,
norm-preserving, and available uniformly over `ℝ` and `ℂ`, so a finite
complex Fourier interpolation of the reciprocal descends to a doubled orbit
certificate over every `RCLike` field at once.  Combined with singular-value
duplication on `orthogonalBlockSum`, it recovers the sharp generic Ky Fan
reciprocal-multiplier estimate without any exact undoubled certificate. -/



omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Coordinatewise doubled phase rotations realize addition of the left and
right phase angles on a doubled coordinate matrix unit, over any `RCLike`
field. -/
theorem basisDoubledPhaseRotation_comp_basisMatrixUnit
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (thetaF : Fin (Module.finrank 𝕜 F) → ℝ)
    (thetaE : Fin (Module.finrank 𝕜 E) → ℝ)
    (i : Fin (Module.finrank 𝕜 F))
    (j : Fin (Module.finrank 𝕜 E)) :
    (basisDoubledPhaseRotation eF thetaF).toLinearMap ∘ₗ
        UnitarilyInvariantSeminorm.orthogonalBlockSum
          (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) ∘ₗ
        (basisDoubledPhaseRotation eE thetaE).toLinearMap =
      doubledPhaseMapAction (thetaF i + thetaE j)
        (basisMatrixUnit eF eE i j) := by
  apply (eE.prod eE).toBasis.ext
  intro q
  rcases q with q | q
  · by_cases hq : j = q
    · subst q
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [basisDoubledPhaseRotation_apply,
          UnitarilyInvariantSeminorm.orthogonalBlockSum_apply,
          doubledPhaseMapAction_apply, basisMatrixUnit_apply,
          Real.cos_add, Real.sin_add, RCLike.ofReal_mul,
          RCLike.ofReal_sub, RCLike.ofReal_add] <;> module
    · apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [basisDoubledPhaseRotation_apply,
          UnitarilyInvariantSeminorm.orthogonalBlockSum_apply,
          doubledPhaseMapAction_apply, basisMatrixUnit_apply, eE.inner_eq_ite, hq]
  · by_cases hq : j = q
    · subst q
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [basisDoubledPhaseRotation_apply,
          UnitarilyInvariantSeminorm.orthogonalBlockSum_apply,
          doubledPhaseMapAction_apply, basisMatrixUnit_apply,
          inner_smul_right, Real.cos_add, Real.sin_add, RCLike.ofReal_mul,
          RCLike.ofReal_sub, RCLike.ofReal_add] <;> module
    · apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [basisDoubledPhaseRotation_apply,
          UnitarilyInvariantSeminorm.orthogonalBlockSum_apply,
          doubledPhaseMapAction_apply, basisMatrixUnit_apply, eE.inner_eq_ite,
          inner_smul_right, hq]

/-- A reciprocal interpolation on coordinate matrix units after doubling both
`𝕜`-Hilbert spaces.  Complex Fourier coefficients are replaced by real
weights and coordinatewise doubled phase rotations. -/
def HasDoubledReciprocalOrbitInterpolation
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    (δ mass : ℝ) : Prop :=
  ∃ q : ℕ, ∃ w : Fin q → ℝ,
    ∃ U : Fin q → WithLp 2 (F × F) ≃ₗᵢ[𝕜] WithLp 2 (F × F),
      ∃ V : Fin q → WithLp 2 (E × E) ≃ₗᵢ[𝕜] WithLp 2 (E × E),
        (∀ i j,
          ((δ : ℝ) : 𝕜) •
              UnitarilyInvariantSeminorm.orthogonalBlockSum
                (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) =
            (((α i - β j : ℝ) : 𝕜)) •
              ((∑ r, ((w r : ℝ) : 𝕜) • unitaryOrbitAction (U r) (V r))
                (UnitarilyInvariantSeminorm.orthogonalBlockSum
                  (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)))) ∧
        ∑ r, |w r| ≤ mass

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- A finite complex Fourier interpolation descends exactly to the doubled
`𝕜`-spaces: the coefficient norm becomes the real orbit weight and its
argument is absorbed into the left phase rotation.  This is the generic
replacement for the impossible exact undoubled real certificate. -/
theorem hasDoubledReciprocalOrbitInterpolation_of_finiteFourierInterpolation
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    {δ mass : ℝ}
    (h : HasFiniteReciprocalFourierInterpolation α β δ mass) :
    HasDoubledReciprocalOrbitInterpolation eF eE α β δ mass := by
  classical
  rcases h with ⟨q, a, t, hscalar, hmass⟩
  let w : Fin q → ℝ := fun r => ‖a r‖
  let U : Fin q → WithLp 2 (F × F) ≃ₗᵢ[𝕜] WithLp 2 (F × F) := fun r =>
    basisDoubledPhaseRotation eF fun i => Complex.arg (a r) + t r * α i
  let V : Fin q → WithLp 2 (E × E) ≃ₗᵢ[𝕜] WithLp 2 (E × E) := fun r =>
    basisDoubledPhaseRotation eE fun j => -(t r * β j)
  refine ⟨q, w, U, V, ?_, ?_⟩
  · intro i j
    let T : E →ₗ[𝕜] F := basisMatrixUnit eF eE i j
    let d : ℝ := α i - β j
    have horbit :
        ((∑ r, ((w r : ℝ) : 𝕜) • unitaryOrbitAction (U r) (V r))
            (UnitarilyInvariantSeminorm.orthogonalBlockSum T T)) =
          doubledComplexScalarMapAction
            (∑ r, a r * Complex.exp ((((t r * d : ℝ) : ℂ) * Complex.I))) T := by
      calc
        ((∑ r, ((w r : ℝ) : 𝕜) • unitaryOrbitAction (U r) (V r))
            (UnitarilyInvariantSeminorm.orthogonalBlockSum T T)) =
            ∑ r, ((‖a r‖ : ℝ) : 𝕜) •
              doubledPhaseMapAction (Complex.arg (a r) + t r * d) T := by
                simp only [LinearMap.sum_apply, LinearMap.smul_apply, w]
                apply Finset.sum_congr rfl
                intro r _
                rw [unitaryOrbitAction_apply]
                -- names the application so the norm bound applies to it directly.
                change ((‖a r‖ : ℝ) : 𝕜) •
                    ((basisDoubledPhaseRotation eF
                        (fun i => Complex.arg (a r) + t r * α i)).toLinearMap ∘ₗ
                      UnitarilyInvariantSeminorm.orthogonalBlockSum T T ∘ₗ
                        (basisDoubledPhaseRotation eE
                          (fun j => -(t r * β j))).toLinearMap) = _
                rw [show T = basisMatrixUnit eF eE i j from rfl,
                  basisDoubledPhaseRotation_comp_basisMatrixUnit]
                congr 2
                dsimp only [d]
                ring
        _ = doubledComplexScalarMapAction
            (∑ r, a r * Complex.exp ((((t r * d : ℝ) : ℂ) * Complex.I))) T := by
              exact sum_norm_smul_doubledPhaseMapAction_arg_add
                a (fun r => t r * d) T
    rw [← doubledComplexScalarMapAction_ofReal δ T, horbit,
      doubledComplexScalarMapAction_real_smul]
    congr 1
    exact hscalar i j
  · simpa only [w, abs_of_nonneg (norm_nonneg _)] using hmass

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- A doubled reciprocal interpolation recombines from matrix units into an
exact finite unitary-orbit certificate for the doubled maps, over any
`RCLike` field. -/
theorem finiteUnitaryOrbitCertificate_orthogonalBlockSum_of_doubledInterpolation
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    {X C : E →ₗ[𝕜] F} {δ mass : ℝ}
    (hinterp : HasDoubledReciprocalOrbitInterpolation eF eE α β δ mass)
    (hcoeff : ∀ i j,
      (((α i : ℝ) : 𝕜) - ((β j : ℝ) : 𝕜)) *
          ⟪X (eE j), eF i⟫_𝕜 =
        ⟪C (eE j), eF i⟫_𝕜) :
    UnitarilyInvariantSeminorm.HasFiniteUnitaryOrbitCertificate
      mass
      (((δ : ℝ) : 𝕜) • UnitarilyInvariantSeminorm.orthogonalBlockSum X X)
      (UnitarilyInvariantSeminorm.orthogonalBlockSum C C) := by
  classical
  rcases hinterp with ⟨q, w, U, V, hinterp, hmass⟩
  let S :
      (WithLp 2 (E × E) →ₗ[𝕜] WithLp 2 (F × F)) →ₗ[𝕜]
        (WithLp 2 (E × E) →ₗ[𝕜] WithLp 2 (F × F)) :=
    ∑ r, ((w r : ℝ) : 𝕜) • unitaryOrbitAction (U r) (V r)
  have hunit (i : Fin (Module.finrank 𝕜 F))
      (j : Fin (Module.finrank 𝕜 E)) :
      ((δ : ℝ) : 𝕜) • UnitarilyInvariantSeminorm.orthogonalBlockSum
          (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) =
        (((α i - β j : ℝ) : 𝕜)) •
          S (UnitarilyInvariantSeminorm.orthogonalBlockSum
            (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)) := by
    exact hinterp i j
  have hcoeff' (i : Fin (Module.finrank 𝕜 F))
      (j : Fin (Module.finrank 𝕜 E)) :
      ((((α i - β j : ℝ) : 𝕜)) *
          ⟪eF i, X (eE j)⟫_𝕜) =
        ⟪eF i, C (eE j)⟫_𝕜 := by
    simpa only [map_mul, map_sub, RCLike.conj_ofReal, inner_conj_symm,
      RCLike.ofReal_sub] using
      congrArg (starRingEnd 𝕜) (hcoeff i j)
  let blockDiagonal := UnitarilyInvariantSeminorm.orthogonalBlockSumDiagonal
    (𝕜 := 𝕜) (E₁ := E) (F₁ := F)
  have hblock (A : E →ₗ[𝕜] F) :
      UnitarilyInvariantSeminorm.orthogonalBlockSum A A =
        ∑ i, ∑ j, ⟪eF i, A (eE j)⟫_𝕜 •
          UnitarilyInvariantSeminorm.orthogonalBlockSum
            (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) := by
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change blockDiagonal A = _
    conv_lhs => rw [sum_basisMatrixUnit eF eE A]
    simp only [map_sum, map_smul, blockDiagonal]
    rfl
  refine ⟨q, fun r => ((w r : ℝ) : 𝕜), U, V, ?_, ?_⟩
  · calc
      ((δ : ℝ) : 𝕜) • UnitarilyInvariantSeminorm.orthogonalBlockSum X X =
          ((δ : ℝ) : 𝕜) • ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_𝕜 •
            UnitarilyInvariantSeminorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) := by
        rw [hblock X]
      _ = ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_𝕜 •
            (((δ : ℝ) : 𝕜) • UnitarilyInvariantSeminorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_smul, smul_smul, mul_comm]
      _ = ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_𝕜 •
            ((((α i - β j : ℝ) : 𝕜)) •
              S (UnitarilyInvariantSeminorm.orthogonalBlockSum
                (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hunit i j]
      _ = ∑ i, ∑ j, ⟪eF i, C (eE j)⟫_𝕜 •
            S (UnitarilyInvariantSeminorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [← hcoeff' i j, smul_smul, mul_comm]
      _ = S (∑ i, ∑ j, ⟪eF i, C (eE j)⟫_𝕜 •
            UnitarilyInvariantSeminorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)) := by
        simp only [map_sum, map_smul]
      _ = S (UnitarilyInvariantSeminorm.orthogonalBlockSum C C) := by
        rw [← hblock C]
      _ = ∑ r, ((w r : ℝ) : 𝕜) • ((U r).toLinearMap ∘ₗ
          UnitarilyInvariantSeminorm.orthogonalBlockSum C C ∘ₗ
            (V r).toLinearMap) := by
        simp only [S, LinearMap.sum_apply, LinearMap.smul_apply,
          unitaryOrbitAction_apply]
  · calc
      (∑ r, ‖((w r : ℝ) : 𝕜)‖) = ∑ r, |w r| := by
        apply Finset.sum_congr rfl
        intro r _
        rw [RCLike.norm_ofReal]
      _ ≤ mass := hmass

/-- **Generic sharp Ky Fan reciprocal-multiplier estimate from approximate
Fourier interpolation.**  The complex coefficients descend to doubled phase
rotations over `𝕜`; duplication of every singular value on the orthogonal
block sum cancels the factor two. -/
theorem kyFan_reciprocalMultiplier_le_of_approximateFourierInterpolation
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    {X C : E →ₗ[𝕜] F} {δ : ℝ} (hδ : 0 < δ)
    (hfourier : ∀ ε : ℝ, 0 < ε →
      HasFiniteReciprocalFourierInterpolation
        α β δ (Real.pi / 2 + ε))
    (hcoeff : ∀ i j,
      (((α i : ℝ) : 𝕜) - ((β j : ℝ) : 𝕜)) *
          ⟪X (eE j), eF i⟫_𝕜 =
        ⟪C (eE j), eF i⟫_𝕜)
    (k : ℕ) :
    δ * TauCeti.kyFanSum k X ≤
      (Real.pi / 2) *
        TauCeti.kyFanSum k C := by
  let K := TauCeti.kyFanSum k C
  have hK0 : 0 ≤ K := by
    dsimp [K, TauCeti.kyFanSum]
    exact Finset.sum_nonneg fun i _ => C.singularValues_nonneg (i : ℕ)
  apply le_of_forall_pos_le_add
  intro eta heta
  let eps := eta / (K + 1)
  have hdenom : 0 < K + 1 := by positivity
  have heps : 0 < eps := div_pos heta hdenom
  have hinterp :=
    hasDoubledReciprocalOrbitInterpolation_of_finiteFourierInterpolation
      eF eE α β (hfourier eps heps)
  have hcert :=
    finiteUnitaryOrbitCertificate_orthogonalBlockSum_of_doubledInterpolation
      eF eE α β hinterp hcoeff
  have hbound :=
    TauCeti.UnitarilyInvariantSeminorm.kyFanSum_le_of_finiteUnitaryOrbitCertificate
      (2 * k) hcert
  have hscale :
      TauCeti.kyFanSum (2 * k)
          (((δ : ℝ) : 𝕜) •
            UnitarilyInvariantSeminorm.orthogonalBlockSum X X) =
        δ * TauCeti.kyFanSum (2 * k)
          (UnitarilyInvariantSeminorm.orthogonalBlockSum X X) :=
    TauCeti.kyFanSum_real_smul
      (2 * k) (UnitarilyInvariantSeminorm.orthogonalBlockSum X X) hδ.le
  rw [hscale,
    TauCeti.UnitarilyInvariantSeminorm.kyFanSum_orthogonalBlockSum_self,
    TauCeti.UnitarilyInvariantSeminorm.kyFanSum_orthogonalBlockSum_self]
      at hbound
  have hbound' :
      δ * TauCeti.kyFanSum k X ≤
        (Real.pi / 2 + eps) * K := by
    dsimp only [K] at hbound ⊢
    nlinarith
  have hepsK : eps * K ≤ eta := by
    rw [show eps = eta / (K + 1) from rfl, div_mul_eq_mul_div,
      div_le_iff₀ hdenom]
    nlinarith
  calc
    δ * TauCeti.kyFanSum k X ≤
        (Real.pi / 2 + eps) * K := hbound'
    _ = (Real.pi / 2) * K + eps * K := by ring
    _ ≤ (Real.pi / 2) * K + eta := by gcongr

/-- **Generic sharp Ky Fan reciprocal-multiplier estimate from the integrable
kernel**, uniformly over `RCLike` scalars through the doubled phase descent. -/
theorem kyFan_reciprocalMultiplier_le_of_integrableKernel
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    {X C : E →ₗ[𝕜] F} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i j, δ ≤ |α i - β j|)
    (hkernel : HasIntegrableReciprocalFourierKernel (Real.pi / 2))
    (hcoeff : ∀ i j,
      (((α i : ℝ) : 𝕜) - ((β j : ℝ) : 𝕜)) *
          ⟪X (eE j), eF i⟫_𝕜 =
        ⟪C (eE j), eF i⟫_𝕜)
    (k : ℕ) :
    δ * TauCeti.kyFanSum k X ≤
      (Real.pi / 2) *
        TauCeti.kyFanSum k C := by
  apply kyFan_reciprocalMultiplier_le_of_approximateFourierInterpolation
    eF eE α β hδ _ hcoeff k
  intro eps heps
  apply hasFiniteReciprocalFourierInterpolation_of_normalized α β hδ
  apply hasFiniteReciprocalFourierInterpolation_pi_div_two_add_eps_of_integrableKernel
    (fun i => α i / δ) (fun j => β j / δ) _ heps hkernel
  intro i j
  rw [show α i / δ - β j / δ = (α i - β j) / δ by ring]
  rw [abs_div, abs_of_pos hδ]
  exact (le_div_iff₀ hδ).2 (by simpa using hgap i j)

end TauCeti
