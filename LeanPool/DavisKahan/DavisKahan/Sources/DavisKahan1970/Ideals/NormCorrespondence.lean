/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.UnitaryInvariantNormDefinite
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.KyFan

/-!
# Exact correspondence with the norm class of Davis--Kahan 1970

The paper quantifies over one normalized symmetric norming function applied to
finite singular-value lists.  The implementation uses an equivalent coherent
family of finite-dimensional unitarily invariant norms.  This file records both
objects and the two conversions explicitly.

Weak-majorization monotonicity is carried in the symmetric-gauge record as a
derived law.  It is not an additional choice and it is exactly the finite Fan
dominance theorem proved by the T-transform argument.  Bundling the law keeps
the reverse construction independent of matrix coordinates.

The bridge in both directions rests on one computation: the singular values of
a real diagonal operator are the decreasing rearrangement of the absolute
values of its diagonal.  That is established here as
`exists_perm_singularValues_diagOp`, from the Gram identity for diagonal
operators together with the basis-permutation unitary.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators

noncomputable section

/-! ### Singular values of a real diagonal operator -/

section DiagonalSingularValues

variable {n : ℕ}

/-- A diagonal operator and the diagonal operator of its absolute values have
the same Gram operator, hence exactly the same singular values. -/
theorem singularValues_diagOp_abs
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (x : Fin n → ℝ) :
    (TauCeti.diagOp b x).singularValues =
      (TauCeti.diagOp b fun i => |x i|).singularValues := by
  apply TauCeti.singularValues_eq_of_gram_eq
  rw [TauCeti.adjoint_diagOp, TauCeti.adjoint_diagOp,
    TauCeti.diagOp_comp, TauCeti.diagOp_comp]
  congr 1
  funext i
  simp [abs_mul_abs_self]

private theorem coe_toLinearMap_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E ≃ₗᵢ[ℂ] E) (v : E) : U.toLinearMap v = U v := rfl

/-- Permuting the diagonal conjugates a diagonal operator by the
basis-permutation unitary, so the singular values are unchanged. -/
theorem singularValues_diagOp_comp_perm
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    (TauCeti.diagOp b (x ∘ π)).singularValues =
      (TauCeti.diagOp b x).singularValues := by
  have hconj : TauCeti.diagOp b (x ∘ π)
      = (↑(b.equiv b π).symm.toLinearEquiv :
            EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) ∘ₗ
          (TauCeti.diagOp b x ∘ₗ
            (↑(b.equiv b π).toLinearEquiv :
              EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))) := by
    refine b.toBasis.ext fun j => ?_
    rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
      LinearMap.comp_apply]
    change TauCeti.diagOp b (x ∘ π) (b j) =
      (b.equiv b π).symm (TauCeti.diagOp b x ((b.equiv b π) (b j)))
    rw [OrthonormalBasis.equiv_apply_basis, TauCeti.diagOp_apply_basis,
      TauCeti.diagOp_apply_basis, map_smul, Function.comp_apply]
    congr 1
    rw [← OrthonormalBasis.equiv_apply_basis b b π j,
      LinearIsometryEquiv.symm_apply_apply]
  rw [hconj, TauCeti.singularValues_unitary_comp,
    TauCeti.singularValues_comp_unitary]

/-- Every real vector can be permuted so that its absolute values decrease. -/
theorem exists_perm_abs_antitone (x : Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), Antitone fun i => |x (π i)| := by
  refine ⟨Tuple.sort fun i => -|x i|, fun i j hij => ?_⟩
  have h := Tuple.monotone_sort (fun i => -|x i|) hij
  simpa using h

/-- **The singular values of a real diagonal operator are a rearrangement of
the absolute values of its diagonal.**  This is the whole content of the
correspondence between symmetric gauges and unitarily invariant norms. -/
theorem exists_perm_singularValues_diagOp
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (x : Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), ∀ i : Fin n,
      (TauCeti.diagOp b x).singularValues (i : ℕ) = |x (π i)| := by
  obtain ⟨π, hπ⟩ := exists_perm_abs_antitone x
  refine ⟨π, fun i => ?_⟩
  have hsorted := TauCeti.singularValues_diagOp
    (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n)) finrank_euclideanSpace_fin b
    (x := fun i => |x (π i)|) hπ (fun i => abs_nonneg _) i
  have hcomp : (fun i => |x (π i)|) = (fun i => |x i|) ∘ π := rfl
  rw [← hsorted, hcomp, singularValues_diagOp_comp_perm b (fun i => |x i|) π,
    ← singularValues_diagOp_abs b x]

end DiagonalSingularValues

/-! ### Gauge laws valid for every finite unitarily invariant norm -/

section UnitarilyInvariantGauge

variable {n : ℕ}
  (N : TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n)) (EuclideanSpace ℂ (Fin n)))
  (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))

/-- The gauge of any unitarily invariant norm ignores the signs of the
diagonal. -/
theorem uinGauge_abs (x : Fin n → ℝ) :
    N.gauge b (fun i => |x i|) = N.gauge b x := by
  have h1 := N.apply_eq_gauge finrank_euclideanSpace_fin b (TauCeti.diagOp b x)
  have h2 := N.apply_eq_gauge finrank_euclideanSpace_fin b
    (TauCeti.diagOp b fun i => |x i|)
  rw [singularValues_diagOp_abs b x] at h1
  exact h2.trans h1.symm

/-- The gauge of any unitarily invariant norm vanishes on the zero vector. -/
@[simp]
theorem uinGauge_zero : N.gauge b (0 : Fin n → ℝ) = 0 := by
  simpa using N.gauge_real_smul b 0 (0 : Fin n → ℝ)

end UnitarilyInvariantGauge

/-- Singular values scale by the modulus of a complex scalar. -/
theorem singularValues_smul_complex {n : ℕ} (a : ℂ)
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (i : ℕ) :
    (a • A).singularValues i = ‖a‖ * A.singularValues i :=
  TauCeti.singularValues_smul_apply
    a A i

namespace SymmetricNormingFunction

/-- **Normalization forces definiteness**: every coordinate of a vector is
dominated by its source gauge.  Only `normalized` and `zero_pad` are used, via
the gauge value one of a coordinate indicator. -/
theorem abs_le_finiteGauge (N : SymmetricNormingFunction) {n : ℕ}
    (x : Fin n → ℝ) (j : Fin n) : |x j| ≤ N.finiteGauge n x := by
  match n, x, j with
  | 0, _, j => exact j.elim0
  | (m + 1), x, j =>
    have hone : N.finiteGauge (m + 1)
        (Function.update (0 : Fin (m + 1) → ℝ) j 1) = 1 := by
      have hsw : Function.update (0 : Fin (m + 1) → ℝ) j 1
          = firstCoordinateVector m ∘ (Equiv.swap 0 j) := by
        funext i
        rcases eq_or_ne i j with rfl | hij
        · simp [firstCoordinateVector, Equiv.swap_apply_right]
        · rw [Function.update_of_ne hij]
          simp only [Function.comp_apply, Pi.zero_apply, firstCoordinateVector]
          rcases eq_or_ne i 0 with rfl | hi0
          · rw [Equiv.swap_apply_left]
            have hj : (j : ℕ) ≠ 0 := fun h => hij (Fin.ext h).symm
            simp [hj]
          · rw [Equiv.swap_apply_of_ne_of_ne hi0 hij]
            have hi : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
            simp [hi]
      rw [finiteGauge, hsw,
        (N.finiteNorm (m + 1)).gauge_perm
          (EuclideanSpace.basisFun (Fin (m + 1)) ℂ) _ (Equiv.swap 0 j)]
      exact N.finiteGauge_firstCoordinateVector m
    have hupd : Function.update (0 : Fin (m + 1) → ℝ) j |x j|
        = |x j| • Function.update (0 : Fin (m + 1) → ℝ) j 1 := by
      funext i
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [Function.update_of_ne hij]
    have hval : N.finiteGauge (m + 1)
        (Function.update (0 : Fin (m + 1) → ℝ) j |x j|) = |x j| := by
      rw [hupd, N.finiteGauge_smul, hone, mul_one, abs_abs]
    have hmono : N.finiteGauge (m + 1)
        (Function.update (0 : Fin (m + 1) → ℝ) j |x j|)
          ≤ N.finiteGauge (m + 1) (fun i => |x i|) := by
      apply (N.finiteNorm (m + 1)).gauge_mono
        (EuclideanSpace.basisFun (Fin (m + 1)) ℂ)
      · intro i
        rcases eq_or_ne i j with rfl | hij
        · simp
        · simp [Function.update_of_ne hij]
      · intro i
        rcases eq_or_ne i j with rfl | hij
        · simp
        · simp [Function.update_of_ne hij, abs_nonneg]
    rw [hval] at hmono
    exact hmono.trans_eq
      (uinGauge_abs (N.finiteNorm (m + 1))
        (EuclideanSpace.basisFun (Fin (m + 1)) ℂ) x)

/-- The source gauge vanishes only on the zero vector. -/
theorem finiteGauge_eq_zero_iff (N : SymmetricNormingFunction) {n : ℕ}
    (x : Fin n → ℝ) : N.finiteGauge n x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    have h := N.abs_le_finiteGauge x i
    rw [hx] at h
    have hxi : x i = 0 := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    simpa using hxi
  · rintro rfl
    exact uinGauge_zero _ _

end SymmetricNormingFunction

/-- A dimension-coherent normalized symmetric norming function, in the exact
finite-list sense used in the paper. -/
structure SymmetricNormingFunction.Axiomatic where
  /-- The symmetric norm gauge on finite real coordinate lists of every length. -/
  gauge : ∀ n : ℕ, (Fin n → ℝ) → ℝ
  nonneg : ∀ {n} (x : Fin n → ℝ), 0 ≤ gauge n x
  definite : ∀ {n} (x : Fin n → ℝ), gauge n x = 0 ↔ x = 0
  add_le : ∀ {n} (x y : Fin n → ℝ),
    gauge n (x + y) ≤ gauge n x + gauge n y
  smul : ∀ {n} (c : ℝ) (x : Fin n → ℝ),
    gauge n (c • x) = |c| * gauge n x
  perm : ∀ {n} (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)),
    gauge n (x ∘ π) = gauge n x
  abs : ∀ {n} (x : Fin n → ℝ),
    gauge n (fun i => |x i|) = gauge n x
  zero_pad : ∀ {n} (x : Fin n → ℝ),
    gauge (n + 1) (zeroPad x) = gauge n x
  normalized : gauge 1 (fun _ => 1) = 1
  weak_majorization : ∀ {n} {x y : Fin n → ℝ},
    Antitone x → (∀ i, 0 ≤ x i) → (∀ i, 0 ≤ y i) →
    (∀ m : ℕ,
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), x i) ≤
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), y i)) →
    gauge n x ≤ gauge n y

namespace SymmetricNormingFunction.Axiomatic

/-- Two source symmetric norming functions with the same gauge agree. -/
theorem ext {Φ Ψ : SymmetricNormingFunction.Axiomatic}
    (h : ∀ n x, Φ.gauge n x = Ψ.gauge n x) : Φ = Ψ := by
  cases Φ
  cases Ψ
  congr 1
  funext n x
  exact h n x

/-- The symmetric norming function extracted from the coherent operator norms. -/
noncomputable def ofNormingFunction (N : SymmetricNormingFunction) :
    SymmetricNormingFunction.Axiomatic where
  gauge := N.finiteGauge
  nonneg := N.finiteGauge_nonneg
  definite := N.finiteGauge_eq_zero_iff
  add_le := N.finiteGauge_add_le
  smul := N.finiteGauge_smul
  perm := by
    intro n x π
    exact (N.finiteNorm n).gauge_perm
      (EuclideanSpace.basisFun (Fin n) ℂ) x π
  abs := by
    intro n x
    exact uinGauge_abs (N.finiteNorm n)
      (EuclideanSpace.basisFun (Fin n) ℂ) x
  zero_pad := N.finiteGauge_zeroPad
  normalized := N.finiteGauge_one
  weak_majorization := by
    intro n x y hx h0x h0y hpre
    exact (N.finiteNorm n).gauge_le_gauge_of_prefix_sums_le
      (EuclideanSpace.basisFun (Fin n) ℂ) hx h0x h0y hpre

/-- Operator value determined by a symmetric norming function. -/
def finiteOperatorValue (Φ : SymmetricNormingFunction.Axiomatic) (n : ℕ)
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) : ℝ :=
  Φ.gauge n (fun i => A.singularValues (i : ℕ))

/-- A source symmetric gauge induces the finite-dimensional unitarily
invariant norm used by the implementation. -/
noncomputable def finiteNorm (Φ : SymmetricNormingFunction.Axiomatic) (n : ℕ) :
    TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n)) (EuclideanSpace ℂ (Fin n)) where
  toSeminorm := Seminorm.of
    (Φ.finiteOperatorValue n)
    (fun A B => by
      have hmaj : ∀ m : ℕ,
          (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m),
              (A + B).singularValues (i : ℕ)) ≤
            ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m),
              (A.singularValues (i : ℕ) + B.singularValues (i : ℕ)) := by
        intro m
        rw [Finset.sum_add_distrib]
        rcases le_or_gt m n with hm | hm
        · rw [TauCeti.sum_filter_lt_eq_sum_fin hm
              (fun k => (A + B).singularValues k),
            TauCeti.sum_filter_lt_eq_sum_fin hm (fun k => A.singularValues k),
            TauCeti.sum_filter_lt_eq_sum_fin hm (fun k => B.singularValues k),
            ← TauCeti.kyFanSum_eq_sum_fin, ← TauCeti.kyFanSum_eq_sum_fin,
            ← TauCeti.kyFanSum_eq_sum_fin]
          exact TauCeti.kyFanSum_add_le m A B
        · have huniv :
              (Finset.univ.filter fun i : Fin n => (i : ℕ) < m) = Finset.univ :=
            Finset.filter_true_of_mem fun i _ => lt_trans i.isLt hm
          rw [huniv, ← TauCeti.kyFanSum_eq_sum_fin,
            ← TauCeti.kyFanSum_eq_sum_fin, ← TauCeti.kyFanSum_eq_sum_fin]
          exact TauCeti.kyFanSum_add_le n A B
      change Φ.gauge n (fun i : Fin n => (A + B).singularValues (i : ℕ)) ≤
        Φ.gauge n (fun i : Fin n => A.singularValues (i : ℕ)) +
          Φ.gauge n (fun i : Fin n => B.singularValues (i : ℕ))
      calc
        Φ.gauge n (fun i : Fin n => (A + B).singularValues (i : ℕ))
            ≤ Φ.gauge n (fun i : Fin n =>
                A.singularValues (i : ℕ) + B.singularValues (i : ℕ)) := by
          apply Φ.weak_majorization
          · exact fun i j hij =>
              (A + B).singularValues_antitone (Fin.le_def.mp hij)
          · exact fun i => (A + B).singularValues_nonneg _
          · exact fun i =>
              add_nonneg (A.singularValues_nonneg _) (B.singularValues_nonneg _)
          · exact hmaj
        _ ≤ Φ.gauge n (fun i : Fin n => A.singularValues (i : ℕ)) +
              Φ.gauge n (fun i : Fin n => B.singularValues (i : ℕ)) :=
          Φ.add_le _ _)
    (fun c A => by
      have hs : (fun i : Fin n => (c • A).singularValues (i : ℕ)) =
          ‖c‖ • (fun i : Fin n => A.singularValues (i : ℕ)) := by
        funext i
        rw [singularValues_smul_complex c A (i : ℕ)]
        rfl
      change Φ.gauge n (fun i : Fin n => (c • A).singularValues (i : ℕ)) =
        ‖c‖ * Φ.gauge n (fun i : Fin n => A.singularValues (i : ℕ))
      rw [hs, Φ.smul, abs_of_nonneg (norm_nonneg c)])
  unitary_invariant' :=
    TauCeti.UnitarilyInvariantSeminorm.unitary_invariant_of_isometry
      (fun U V A => by
        have h : (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).singularValues =
            A.singularValues := by
          rw [show (U.toLinearMap :
                  EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
                = ↑U.toLinearEquiv from rfl,
            show (V.toLinearMap :
                  EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
                = ↑V.toLinearEquiv from rfl,
            TauCeti.singularValues_unitary_comp,
            TauCeti.singularValues_comp_unitary]
        change Φ.gauge n (fun i : Fin n =>
            (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).singularValues (i : ℕ)) =
          Φ.gauge n (fun i : Fin n => A.singularValues (i : ℕ))
        rw [h])

/-- **The induced finite norm has exactly the source gauge.**  Both the
normalization and the zero-padding law of the reconstructed family reduce to
the corresponding source law through this identity. -/
theorem finiteNorm_gauge (Φ : SymmetricNormingFunction.Axiomatic) (n : ℕ)
    (x : Fin n → ℝ) :
    (Φ.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x =
      Φ.gauge n x := by
  obtain ⟨π, hπ⟩ :=
    exists_perm_singularValues_diagOp (EuclideanSpace.basisFun (Fin n) ℂ) x
  change Φ.gauge n (fun i : Fin n =>
      (TauCeti.diagOp (EuclideanSpace.basisFun (Fin n) ℂ) x).singularValues
        (i : ℕ)) = Φ.gauge n x
  have hfun : (fun i : Fin n =>
      (TauCeti.diagOp (EuclideanSpace.basisFun (Fin n) ℂ) x).singularValues
        (i : ℕ)) = (fun i => |x i|) ∘ π := by
    funext i
    exact hπ i
  rw [hfun, Φ.perm, Φ.abs]

/-- Reconstruct the coherent operator-norm family from a source symmetric
norming function. -/
noncomputable def toNormingFunction (Φ : SymmetricNormingFunction.Axiomatic) :
    SymmetricNormingFunction where
  finiteNorm := Φ.finiteNorm
  normalized := by
    rw [Φ.finiteNorm_gauge]
    exact Φ.normalized
  zero_pad := by
    intro n x
    rw [Φ.finiteNorm_gauge, Φ.finiteNorm_gauge]
    exact Φ.zero_pad x

/-- The transported paper norm has finite gauge, so it lands in the ideal. -/
theorem toNormingFunction_finiteGauge (Φ : SymmetricNormingFunction.Axiomatic) (n : ℕ)
    (x : Fin n → ℝ) :
    Φ.toNormingFunction.finiteGauge n x = Φ.gauge n x :=
  Φ.finiteNorm_gauge n x

/-- Extracting the source gauge after reconstruction returns it exactly. -/
theorem ofNormingFunction_toNormingFunction (Φ : SymmetricNormingFunction.Axiomatic) :
    ofNormingFunction Φ.toNormingFunction = Φ :=
  ext fun n x => Φ.finiteNorm_gauge n x

/-- The finite operator values of the reconstructed family agree with the
original coherent family. -/
theorem toNormingFunction_ofNormingFunction_finite_apply
    (N : SymmetricNormingFunction) (n : ℕ)
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    ((ofNormingFunction N).toNormingFunction.finiteNorm n) A = (N.finiteNorm n) A :=
  ((N.finiteNorm n).apply_eq_gauge finrank_euclideanSpace_fin
    (EuclideanSpace.basisFun (Fin n) ℂ) A).symm

/-- The coherent finite operator family is completely determined by its source
symmetric norming function. -/
theorem ext_finiteGauge
    {N M : SymmetricNormingFunction}
    (h : ∀ n x, N.finiteGauge n x = M.finiteGauge n x) : N = M := by
  cases N with
  | mk Nf Nnorm Nz =>
    cases M with
    | mk Mf Mnorm Mz =>
      congr 1
      funext n
      apply TauCeti.UnitarilyInvariantSeminorm.ext
      intro A
      rw [(Nf n).apply_eq_gauge finrank_euclideanSpace_fin
          (EuclideanSpace.basisFun (Fin n) ℂ) A,
        (Mf n).apply_eq_gauge finrank_euclideanSpace_fin
          (EuclideanSpace.basisFun (Fin n) ℂ) A]
      exact h n _

/-- The current paper norm object and normalized symmetric norming functions
are equivalent, so the universal theorem excludes no norm in the source class. -/
noncomputable def equiv :
    SymmetricNormingFunction ≃ SymmetricNormingFunction.Axiomatic where
  toFun := ofNormingFunction
  invFun := toNormingFunction
  left_inv N := by
    apply ext_finiteGauge
    intro n x
    exact (ofNormingFunction N).finiteNorm_gauge n x
  right_inv := ofNormingFunction_toNormingFunction

end SymmetricNormingFunction.Axiomatic

end

end ExactSinTheta
end DavisKahan
end TauCeti
