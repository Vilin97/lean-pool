/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSum

/-!
# Standard unitarily invariant seminorms

The operator norm, Frobenius norm, Ky Fan seminorms and nuclear norm are instances of the
same rectangular structure. Adjoint transport reverses the domain and codomain.
Frobenius evaluation is independent of the orthonormal basis of the domain.

Ky Fan dominance is equivalent to comparison in every seminorm of this structure.
The singular-value variational principles used to construct these instances live in
`ForTauCeti.Analysis.InnerProductSpace.KyFan`, without a norm-structure dependency.

## Provenance

Adapted from the square and rectangular norm-instance modules in the Davis--Kahan/DKPS
formalization (Kitware, Inc.).
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [FiniteDimensional 𝕜 G]

namespace UnitarilyInvariantSeminorm

variable (N : UnitarilyInvariantSeminorm 𝕜 E F)

/- `Module ℝ (E →ₗ[𝕜] F)` is a *local* instance in `Basic`, so it does not survive the
import.  Re-enable it here; making it global would put a second `Module ℝ` structure on
every `𝕜`-linear map space, which is why it is local in the first place. -/
attribute [local instance] realModuleLinearMap


/-- Adjoint transport to the transposed rectangular norm. -/
noncomputable def adjointTransport
    (N : UnitarilyInvariantSeminorm 𝕜 E F) :
    UnitarilyInvariantSeminorm 𝕜 F E where
  toSeminorm := Seminorm.of
    (fun A => N A.adjoint)
    (fun A B => by
      simpa only [map_add] using N.add_le A.adjoint B.adjoint)
    (fun a A => by
      rw [map_smulₛₗ]
      calc
        N ((starRingEnd 𝕜) a • A.adjoint) =
            ‖(starRingEnd 𝕜) a‖ * N A.adjoint :=
          N.smul_eq ((starRingEnd 𝕜) a) A.adjoint
        _ = ‖a‖ * N A.adjoint := by
          congr 1
          -- names the application so the norm bound applies to it directly.
          change ‖star a‖ = ‖a‖
          exact norm_star a)
  unitary_invariant' :=
    TauCeti.UnitarilyInvariantSeminorm.unitary_invariant_of_isometry
      (fun U V A => by
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        change N (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).adjoint = N A.adjoint
        simpa only [LinearMap.adjoint_comp,
          V.adjoint_toLinearMap_eq_symm, U.adjoint_toLinearMap_eq_symm,
          LinearMap.comp_assoc] using
          N.invariant V.symm U.symm A.adjoint)

/-- The transported norm evaluated at an adjoint returns the original norm of
the operator — the defining property of `adjointTransport`.

Stated in the **coerced** form, which is how call sites write it: a `.toFun` form cannot be
rewritten with at a call site that says `(adjointTransport N) A.adjoint`, because the goal
carries the `CoeFun` application rather than the projection. -/
@[simp] theorem adjointTransport_apply (A : E →ₗ[𝕜] F) :
    (adjointTransport N) A.adjoint = N A := by
  change N A.adjoint.adjoint = N A
  rw [LinearMap.adjoint_adjoint]

/-- The transported norm of a *negated* adjoint.

`adjointTransport_coe_apply` cannot fire on this: it matches an argument of the
form `A.adjoint`, and `-C.adjoint` has `Neg.neg` at the head, so simp sees no
adjoint to cancel.  Callers that reverse a Sylvester equation land on exactly
this shape — the reversal introduces the sign — and before 2026-07-30 two proofs
in `Sylvester/Interval.lean` each carried an eight-line comment explaining the
failure followed by the same `change`/`map_neg`/`adjoint_adjoint` fix by hand. -/
theorem adjointTransport_neg_adjoint_apply (C : E →ₗ[𝕜] F) :
    (adjointTransport N) (-C.adjoint) = N C := by
  change N ((-C.adjoint).adjoint) = N C
  rw [map_neg, LinearMap.adjoint_adjoint, N.apply_neg]


/-- Left ideal property.  This is Fan dominance applied to the pointwise
singular-value bound for composition by a bounded left factor. -/
theorem comp_le_opNorm_mul (C : F →ₗ[𝕜] F) (A : E →ₗ[𝕜] F) :
    N (C ∘ₗ A) ≤ ‖C.toContinuousLinearMap‖ * N A := by
  let c : ℝ := ‖C.toContinuousLinearMap‖
  have hc : 0 ≤ c := norm_nonneg _
  calc
    N (C ∘ₗ A) ≤ N (((c : 𝕜)) • A) :=
      N.apply_le_of_singularValues_le fun i => by
        rw [singularValues_real_smul A hc i]
        exact singularValues_comp_le hc
          (fun y => C.toContinuousLinearMap.le_opNorm y) A i
    _ = c * N A := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hc]
    _ = ‖C.toContinuousLinearMap‖ * N A := by rfl

/-- Right ideal property, obtained from the left ideal property by adjoint
transport. -/
theorem comp_le_mul_opNorm (A : E →ₗ[𝕜] F) (C : E →ₗ[𝕜] E) :
    N (A ∘ₗ C) ≤ N A * ‖C.toContinuousLinearMap‖ := by
  have h := comp_le_opNorm_mul (adjointTransport N) C.adjoint A.adjoint
  rw [← LinearMap.adjoint_comp, adjointTransport_apply,
    adjointTransport_apply, LinearMap.adjoint_toContinuousLinearMap,
    LinearIsometryEquiv.norm_map] at h
  simpa only [mul_comm] using h

/-- Operator norm as a rectangular UI norm. -/
@[expose]
noncomputable def opNorm : UnitarilyInvariantSeminorm 𝕜 E F where
  toSeminorm := Seminorm.of
    (fun A => ‖A.toContinuousLinearMap‖)
    (fun A B => by
      rw [map_add]
      exact norm_add_le _ _)
    (fun a A => by
      rw [map_smul]
      exact norm_smul a _)
  unitary_invariant' :=
    TauCeti.UnitarilyInvariantSeminorm.unitary_invariant_of_isometry
      (f := fun A : E →ₗ[𝕜] F => ‖A.toContinuousLinearMap‖)
      (fun U V A => by
        have hcomp :
            (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).toContinuousLinearMap =
              (U : F →L[𝕜] F) ∘L A.toContinuousLinearMap ∘L (V : E →L[𝕜] E) := by
          ext x
          simp
        change ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).toContinuousLinearMap‖
            = ‖A.toContinuousLinearMap‖
        rw [hcomp]
        simp)

/-- The rectangular operator norm is the ordinary operator norm of the
continuous-linear-map view, definitionally. -/
@[simp] theorem opNorm_apply (A : E →ₗ[𝕜] F) :
    opNorm A = ‖A.toContinuousLinearMap‖ := (rfl)

/-- Minkowski inequality for the square root of a finite sum of squares. -/
theorem sqrt_sum_add_sq_le {m : ℕ} (f g : Fin m → ℝ) :
    Real.sqrt (∑ i, (f i + g i) ^ 2)
      ≤ Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2) := by
  let x : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm f
  let y : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm g
  have hnx : ‖x‖ = Real.sqrt (∑ i, f i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by
      rw [show x i = f i from rfl, Real.norm_eq_abs, sq_abs])
  have hny : ‖y‖ = Real.sqrt (∑ i, g i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by
      rw [show y i = g i from rfl, Real.norm_eq_abs, sq_abs])
  have hnxy : ‖x + y‖ = Real.sqrt (∑ i, (f i + g i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by
      rw [PiLp.add_apply, show x i = f i from rfl, show y i = g i from rfl,
        Real.norm_eq_abs, sq_abs])
  rw [← hnx, ← hny, ← hnxy]
  exact norm_add_le x y

/-- Frobenius/Hilbert--Schmidt norm as a rectangular UI norm. -/
@[expose]
noncomputable def frobenius : UnitarilyInvariantSeminorm 𝕜 E F where
  toSeminorm := Seminorm.of
    (fun A => Real.sqrt
      (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2))
    (fun A B => by
      have hmono :
          Real.sqrt (∑ i, ‖(A + B) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) ≤
            Real.sqrt (∑ i, (‖A (stdOrthonormalBasis 𝕜 E i)‖ +
              ‖B (stdOrthonormalBasis 𝕜 E i)‖) ^ 2) := by
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        rw [LinearMap.add_apply]
        exact norm_add_le _ _
      exact hmono.trans (UnitarilyInvariantSeminorm.sqrt_sum_add_sq_le _ _))
    (fun a A => by
      have h : ∀ i, ‖(a • A) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 =
          ‖a‖ ^ 2 * ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 := fun i => by
        rw [LinearMap.smul_apply, norm_smul, mul_pow]
      rw [show (∑ i, ‖(a • A) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) =
          ‖a‖ ^ 2 * ∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => h i,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg a)])
  unitary_invariant' :=
    TauCeti.UnitarilyInvariantSeminorm.unitary_invariant_of_isometry
      (f := fun A : E →ₗ[𝕜] F => Real.sqrt
        (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2))
      (fun U V A => by
        change Real.sqrt (∑ i, ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
              (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
            = Real.sqrt (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
        have key : ∀ i,
            ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
                (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 =
              ‖A (V (stdOrthonormalBasis 𝕜 E i))‖ ^ 2 := fun i => by
          rw [show (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
              (stdOrthonormalBasis 𝕜 E i) =
              U (A (V (stdOrthonormalBasis 𝕜 E i))) from rfl,
            U.norm_map]
        rw [show (∑ i, ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
              (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) =
            ∑ i, ‖A (V (stdOrthonormalBasis 𝕜 E i))‖ ^ 2 from
            Finset.sum_congr rfl fun i _ => key i,
          sum_sq_norm_apply_unitary_comp A V rfl (stdOrthonormalBasis 𝕜 E)])

/-- Ky Fan `k`-norm. -/
@[expose]
noncomputable def kyFan (k : ℕ) : UnitarilyInvariantSeminorm 𝕜 E F where
  toSeminorm := Seminorm.of
    (fun A => kyFanSum k A)
    (fun A B => kyFanSum_add_le k A B)
    (fun a A => by
      unfold kyFanSum
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => singularValues_smul_apply a A (i : ℕ))
  unitary_invariant' :=
    TauCeti.UnitarilyInvariantSeminorm.unitary_invariant_of_isometry
      (f := fun A : E →ₗ[𝕜] F => kyFanSum k A)
      (fun U V A => by
        unfold kyFanSum
        rw [singularValues_unitary_comp, singularValues_comp_unitary])

/-- Nuclear/trace norm. -/
@[expose]
noncomputable def nuclear : UnitarilyInvariantSeminorm 𝕜 E F :=
  kyFan (finrank 𝕜 E)


/-- The Frobenius norm evaluated in the standard orthonormal basis. -/
@[simp]
theorem frobenius_apply (A : E →ₗ[𝕜] F) :
    frobenius A = Real.sqrt (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) :=
  rfl

/-- Basis independence of the rectangular Frobenius norm. -/
theorem frobenius_apply_basis {n : ℕ} (A : E →ₗ[𝕜] F)
    (hn : finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) :
    frobenius A = Real.sqrt (∑ i, ‖A (b i)‖ ^ 2) := by
  subst n
  rw [frobenius_apply, ← sum_sq_singularValues A rfl (stdOrthonormalBasis 𝕜 E),
    ← sum_sq_singularValues A rfl b]

/-- Squared Frobenius norm as the sum of squared column norms in any orthonormal basis. -/
theorem frobenius_sq {n : ℕ} (A : E →ₗ[𝕜] F)
    (hn : finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) :
    frobenius A ^ 2 = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [frobenius_apply_basis A hn b,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]


/-- Postcomposition by a linear isometry preserves the Frobenius norm. -/
theorem frobenius_linearIsometry_comp
    (ι : F →ₗᵢ[𝕜] G) (A : E →ₗ[𝕜] F) :
    frobenius (ι.toLinearMap ∘ₗ A) = frobenius A := by
  rw [frobenius_apply_basis _ rfl (stdOrthonormalBasis 𝕜 E),
    frobenius_apply_basis _ rfl (stdOrthonormalBasis 𝕜 E)]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, ι.norm_map]

/-- Orthogonal projection on the codomain is contractive for the Frobenius norm. -/
theorem frobenius_projection_comp_le
    (U : Submodule 𝕜 F) [U.HasOrthogonalProjection] (A : E →ₗ[𝕜] F) :
    frobenius (((U.starProjection : F →L[𝕜] F) : F →ₗ[𝕜] F) ∘ₗ A) ≤ frobenius A := by
  rw [frobenius_apply_basis _ rfl (stdOrthonormalBasis 𝕜 E),
    frobenius_apply_basis _ rfl (stdOrthonormalBasis 𝕜 E)]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (U.norm_starProjection_apply_le _) 2

/-- Passing from a subtype-valued map to its ambient inclusion preserves the
Frobenius norm. -/
theorem frobenius_subtype_comp
    (U : Submodule 𝕜 F) (A : E →ₗ[𝕜] U) :
    frobenius (U.subtypeₗᵢ.toLinearMap ∘ₗ A) = frobenius A :=
  frobenius_linearIsometry_comp U.subtypeₗᵢ A

/-- The Ky Fan norm evaluates to the prefix sum of singular values.
-/
@[simp]
theorem kyFan_apply (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFan k A = kyFanSum k A :=
  (rfl)

/-- Ky Fan domination is equivalent to comparison in every rectangular UI seminorm. -/
theorem kyFanSum_le_iff_forall_seminorm {A B : E →ₗ[𝕜] F} :
    (∀ k, kyFanSum k A ≤ kyFanSum k B) ↔
      ∀ N : UnitarilyInvariantSeminorm 𝕜 E F, N A ≤ N B := by
  constructor
  · intro h N
    exact N.apply_le_of_kyFanSum_le h
  · intro h k
    exact h (kyFan k)

/-- A finite two-sided unitary-orbit certificate bounds every rectangular
Ky Fan prefix by the same certificate mass.

This is the exact bridge used by the arbitrary-spectrum Sylvester theorem. -/
theorem kyFanSum_le_of_finiteUnitaryOrbitCertificate
    {mass : ℝ} {X C : E →ₗ[𝕜] F} (k : ℕ)
    (hcert : HasFiniteUnitaryOrbitCertificate mass X C) :
    kyFanSum k X ≤ mass * kyFanSum k C := by
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change kyFan k X ≤ mass * kyFan k C
  exact (kyFan k).apply_le_of_finiteUnitaryOrbitCertificate hcert

/-- The nuclear norm is the full domain-length singular-value sum; singular
values past the rank are zero automatically. -/
@[simp]
theorem nuclear_apply (A : E →ₗ[𝕜] F) :
    nuclear A = ∑ i : Fin (finrank 𝕜 E), A.singularValues (i : ℕ) :=
  (rfl)

/-- The rectangular Frobenius norm is the Euclidean norm of the complete
finite singular-value list. -/
theorem frobenius_eq_sqrt_sum_sq_singularValues (A : E →ₗ[𝕜] F) :
    frobenius A = Real.sqrt
      (∑ i : Fin (finrank 𝕜 E), A.singularValues (i : ℕ) ^ 2) := by
  rw [frobenius_apply_basis A rfl (stdOrthonormalBasis 𝕜 E),
    sum_sq_singularValues A rfl (stdOrthonormalBasis 𝕜 E)]



/-- The nuclear norm of a Gram operator is the squared Frobenius energy, written
as a column-norm sum in any orthonormal basis. -/
theorem nuclear_adjoint_comp_self_eq_sum_sq_norm
    (A : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    nuclear (A.adjoint ∘ₗ A) = ∑ i, ‖A (b i)‖ ^ 2 := by
  let G := A.adjoint ∘ₗ A
  have hG : G.IsPositive := LinearMap.isPositive_adjoint_comp_self A
  have hGabs : TauCeti.operatorAbs G = G := by
    symm
    exact (LinearMap.isPositive_adjoint_comp_self G).sqrt_unique hG (by
      rw [hG.adjoint_eq])
  rw [nuclear_apply,
    ← sum_re_inner_abs_self_eq_sum_singularValues G rfl b,
    hGabs]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [G, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq]

/-- The nuclear norm is bounded by the square root of the domain dimension
times the Frobenius norm.  This is the finite Cauchy--Schwarz inequality for
the complete singular-value list, including its trailing zeros. -/
theorem nuclear_le_sqrt_finrank_mul_frobenius (A : E →ₗ[𝕜] F) :
    nuclear A ≤ Real.sqrt (finrank 𝕜 E) * frobenius A := by
  rw [nuclear_apply, frobenius_eq_sqrt_sum_sq_singularValues]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (s := Finset.univ)
    (f := fun _ : Fin (finrank 𝕜 E) => (1 : ℝ))
    (g := fun i : Fin (finrank 𝕜 E) => A.singularValues (i : ℕ))
  simpa [one_mul, one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    using hcs

end UnitarilyInvariantSeminorm

end TauCeti
