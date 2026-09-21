/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.HopkinsLevitzki
import LeanPool.Stafford38.Stafford38.Characteristic.SourceActionCommutatorExpansion
import Mathlib.RingTheory.Finiteness.NilpotentKer

/-!
# Actual traces using coefficient-field corrections

The first-order source equations can be chosen with correction coefficients
in the coefficient field. Their commutators then have their actual matrix
traces. The remaining source matrix has arbitrary special-fibre coefficients,
but sends each basis vector to a strictly deeper maximal-ideal layer. This
is sufficient to kill its diagonal without replacing coefficients by residues.
-/

namespace Stafford38.Characteristic.BGab001CoefficientFieldTrace

open Matrix
open Stafford38.Characteristic.ArtinianAdaptedBasisTraceAdapter
open Stafford38.Characteristic.ConcreteEquation33SourceMatrices
open Stafford38.Characteristic.ConcreteInducedZAction
open Stafford38.Characteristic.SourceActionCommutatorExpansion

noncomputable section

universe u
variable {K R V : Type u} [Field K] [CommRing R] [Algebra K R]
variable [IsLocalRing R] [AddCommGroup V] [Module K V] [Module R V]
variable [IsScalarTower K R V] {n : ℕ}
local notation "ι" => Fin (n + 1)

/-- An arbitrary ring coefficient cannot bring a vector from a deeper adic
layer back to the diagonal of an adapted basis. -/
theorem repr_smul_eq_zero_of_level_lt
    (b : Module.Basis ι K V) (level : ι → ℕ)
    (hb : IsMaximalIdealFiltrationAdapted (IsLocalRing.maximalIdeal R) b level)
    (a : R) (i j : ι) (hij : level i < level j) :
    b.repr (a • b j) i = 0 := by
  have hj : b j ∈ (IsLocalRing.maximalIdeal R) ^ level j •
      (⊤ : Submodule R V) := by
    have hs : b j ∈ Submodule.span K (b '' {l | level j ≤ level l}) :=
      (b.self_mem_span_image).mpr (show level j ≤ level j from le_rfl)
    rw [← hb.power_span (level j)] at hs
    exact hs
  have ha := ((IsLocalRing.maximalIdeal R) ^ level j •
      (⊤ : Submodule R V)).smul_mem a hj
  have hs : a • b j ∈ Submodule.span K (b '' {l | level j ≤ level l}) := by
    rw [← hb.power_span (level j)]
    exact ha
  by_contra hne
  have hi := b.repr_support_subset_of_mem_span _ hs
    (Finsupp.mem_support_iff.mpr hne)
  exact (not_le_of_gt hij) hi

/-- The diagonal of a whole source row vanishes when every nonzero entry
points to a strictly deeper layer. No term is reduced to the residue field. -/
theorem repr_deeper_source_row_diagonal_eq_zero
    (b : Module.Basis ι K V) (level : ι → ℕ)
    (hb : IsMaximalIdealFiltrationAdapted (IsLocalRing.maximalIdeal R) b level)
    (M : Matrix ι ι R)
    (hM : ∀ i j, level j ≤ level i → M i j = 0) (i : ι) :
    b.repr (∑ j, M i j • b j) i = 0 := by
  rw [map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : level j ≤ level i
  · simp [hM i j hij]
  · exact repr_smul_eq_zero_of_level_lt b level hb _ i j (lt_of_not_ge hij)

/-- Actual action trace from a deeper-layer remainder and a coefficient-field
correction. This consumes action on basis vectors, not a residue matrix. -/
theorem actual_trace_eq_correction_trace
    (b : Module.Basis ι K V) (level : ι → ℕ)
    (hb : IsMaximalIdealFiltrationAdapted (IsLocalRing.maximalIdeal R) b level)
    (T : Module.End K V) (M : Matrix ι ι R) (Q : Matrix ι ι K)
    (hM : ∀ i j, level j ≤ level i → M i j = 0)
    (hT : ∀ i, T (b i) = (∑ j, M i j • b j) + ∑ j, Q i j • b j) :
    Matrix.trace (LinearMap.toMatrix b b T) = Matrix.trace Q := by
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  change LinearMap.toMatrix b b T i i = Q i i
  rw [LinearMap.toMatrix_apply, hT i, map_add, Finsupp.add_apply,
    repr_deeper_source_row_diagonal_eq_zero b level hb M hM i, zero_add]
  simp [Finsupp.single_apply]

/-- Both correction commutators have trace zero over the coefficient field. -/
theorem actual_trace_eq_zero_of_coefficientField_corrections
    (b : Module.Basis ι K V) (level : ι → ℕ)
    (hb : IsMaximalIdealFiltrationAdapted (IsLocalRing.maximalIdeal R) b level)
    (T : Module.End K V) (M : Matrix ι ι R)
    (A B Gamma Theta : Matrix ι ι K)
    (hM : ∀ i j, level j ≤ level i → M i j = 0)
    (hT : ∀ i, T (b i) = (∑ j, M i j • b j) +
      ∑ j, (B * Gamma - Gamma * B + (Theta * A - A * Theta)) i j • b j) :
    Matrix.trace (LinearMap.toMatrix b b T) = 0 := by
  rw [actual_trace_eq_correction_trace b level hb T M _ hM hT,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_mul_comm B Gamma, Matrix.trace_mul_comm Theta A]
  ring

/-- The source-row matrix of a maximal-ideal action points strictly deeper
in the adapted filtration, independently of the ordering within a layer. -/
theorem source_coefficients_deeper
    (b : Module.Basis ι K V) (level : ι → ℕ)
    (hb : IsMaximalIdealFiltrationAdapted (IsLocalRing.maximalIdeal R) b level)
    (a : R) (ha : a ∈ IsLocalRing.maximalIdeal R) :
    ∀ i j, level j ≤ level i → b.repr (a • b i) j = 0 := by
  intro i j hij
  have hi : b i ∈ (IsLocalRing.maximalIdeal R) ^ level i •
      (⊤ : Submodule R V) := by
    have hs : b i ∈ Submodule.span K (b '' {l | level i ≤ level l}) :=
      (b.self_mem_span_image).mpr (show level i ≤ level i from le_rfl)
    rw [← hb.power_span (level i)] at hs
    exact hs
  have hs : a • b i ∈ Submodule.span K (b '' {l | level i + 1 ≤ level l}) := by
    rw [← hb.power_span (level i + 1)]
    exact maximalIdeal_smul_mem_succ_power ha hi
  by_contra hne
  have hj := b.repr_support_subset_of_mem_span _ hs
    (Finsupp.mem_support_iff.mpr hne)
  change level i + 1 ≤ level j at hj
  omega

section SourceRing
variable {B W : Type u} [Ring B] [AddCommGroup W] [Module B W]

private theorem deeper_mul
    (level : ι → ℕ) (M N : Matrix ι ι B)
    (hM : ∀ i j, level j ≤ level i → M i j = 0)
    (hN : ∀ i j, level j ≤ level i → N i j = 0) :
    ∀ i j, level j ≤ level i → (M * N) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : level l ≤ level i
  · rw [hM i l hl, zero_mul]
  · rw [hN l j (hij.trans (le_of_lt (lt_of_not_ge hl))), mul_zero]

/-- Gabber's local trace step from the actual square-zero module. Both
first-order correction matrices are produced over the coefficient field;
all parameter cofactors are produced with their deeper-layer support. -/
theorem actual_commutator_cofactor_trace_eq_zero
    (S : LeftPrincipalParameterReduction (B := B) (Abar := R))
    (rho : W →+ V) (hrho : Function.Surjective rho)
    (hact : ∀ a w, rho (a • w) = S.modParameter a • rho w)
    (hker : AddMonoidHom.ker rho =
      AddMonoidHom.range (parameterAct (W := W) S.parameter))
    (hexact : AddMonoidHom.ker (parameterAct (W := W) S.parameter) =
      AddMonoidHom.range (parameterAct (W := W) S.parameter))
    (hc2 : S.parameter * S.parameter = 0)
    (b : Module.Basis ι K V) (level : ι → ℕ)
    (hb : IsMaximalIdealFiltrationAdapted (IsLocalRing.maximalIdeal R) b level)
    (x y z : B) (hx : S.modParameter x ∈ IsLocalRing.maximalIdeal R)
    (hy : S.modParameter y ∈ IsLocalRing.maximalIdeal R)
    (hxy : x * y - y * x = S.parameter * z) :
    Matrix.trace (LinearMap.toMatrix b b
      (leftMultiplicationEnd (K := K) (V := V) (S.modParameter z))) = 0 := by
  classical
  let Ax := leftMultiplicationEnd (K := K) (V := V) (S.modParameter x)
  let By := leftMultiplicationEnd (K := K) (V := V) (S.modParameter y)
  let A0 := (LinearMap.toMatrix b b Ax)ᵀ
  let B0 := (LinearMap.toMatrix b b By)ᵀ
  let A := liftedSourceActionMatrix S b Ax
  let Bm := liftedSourceActionMatrix S b By
  have hAmap : A.map S.modParameter = A0.map (algebraMap K R) := by
    rw [liftedSourceActionMatrix_map, sourceActionCoefficients_eq_transpose_toMatrix_map]
  have hBmap : Bm.map S.modParameter = B0.map (algebraMap K R) := by
    rw [liftedSourceActionMatrix_map, sourceActionCoefficients_eq_transpose_toMatrix_map]
  obtain ⟨Gamma, GammaK, hGamma, heqx⟩ :=
    exists_firstOrderSourceActionMatrix_over_coefficientField S rho hrho hact hker hc2 b x
  obtain ⟨Theta, ThetaK, hTheta, heqy⟩ :=
    exists_firstOrderSourceActionMatrix_over_coefficientField S rho hrho hact hker hc2 b y
  have hAz : ∀ i j, level j ≤ level i → A i j = 0 := by
    intro i j hij
    simp [A, liftedSourceActionMatrix, liftMatrix, sourceActionCoefficients, Ax,
      source_coefficients_deeper b level hb _ hx i j hij]
  have hBz : ∀ i j, level j ≤ level i → Bm i j = 0 := by
    intro i j hij
    simp [Bm, liftedSourceActionMatrix, liftMatrix, sourceActionCoefficients, By,
      source_coefficients_deeper b level hb _ hy i j hij]
  have hcomm : Bm.map S.modParameter * A.map S.modParameter =
      A.map S.modParameter * Bm.map S.modParameter := by
    rw [hAmap, hBmap, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    dsimp [A0, B0]
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul,
      ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
    congr 2
    ext v
    exact smul_comm _ _ v
  let X := factorMatrix S (scalarMatrixCommutator x Bm)
  let Y := factorMatrix S (scalarMatrixCommutator y A)
  let Omega := factorMatrix S (sourceMatrixCommutator Bm A)
  have hXz : ∀ i j, level j ≤ level i → X i j = 0 := by
    intro i j hij
    simp [X, factorMatrix, scalarMatrixCommutator, hBz i j hij]
  have hYz : ∀ i j, level j ≤ level i → Y i j = 0 := by
    intro i j hij
    simp [Y, factorMatrix, scalarMatrixCommutator, hAz i j hij]
  have hOz : ∀ i j, level j ≤ level i → Omega i j = 0 := by
    intro i j hij
    simp [Omega, factorMatrix, sourceMatrixCommutator,
      deeper_mul level Bm A hBz hAz i j hij, deeper_mul level A Bm hAz hBz i j hij]
  let Rem := (X - Y + Omega).map S.modParameter
  have hRem : ∀ i j, level j ≤ level i → Rem i j = 0 := by
    intro i j hij
    simp [Rem, Matrix.map_apply, hXz i j hij, hYz i j hij, hOz i j hij]
  have hfc : S.modParameter S.parameter = 0 := by
    apply (S.kernel_left _).mpr
    exact ⟨1, mul_one _⟩
  have heq (i : ι) := rho_commutator_on_source_equations
    S.parameter x y z S.modParameter rho S.parameter_comm hc2 hfc hxy hact hexact
    A Bm Gamma Theta X Y Omega (liftedBasisVector rho hrho b) heqx heqy
    (parameter_mul_factorMatrix S _ (scalarMatrixCommutator_map_eq_zero S x Bm))
    (parameter_mul_factorMatrix S _ (scalarMatrixCommutator_map_eq_zero S y A))
    (parameter_mul_factorMatrix S _ (sourceMatrixCommutator_map_eq_zero S Bm A hcomm)) i
  let Q := B0 * GammaK - GammaK * B0 + (ThetaK * A0 - A0 * ThetaK)
  have hmap : (sourceExpansionMatrix X Y Omega A Bm Gamma Theta).map S.modParameter =
      Rem + Q.map (algebraMap K R) := by
    have hAe i j := congrArg (fun M : Matrix ι ι R ↦ M i j) hAmap
    have hBe i j := congrArg (fun M : Matrix ι ι R ↦ M i j) hBmap
    have hGe i j := congrArg (fun M : Matrix ι ι R ↦ M i j) hGamma
    have hTe i j := congrArg (fun M : Matrix ι ι R ↦ M i j) hTheta
    simp only [Matrix.map_apply] at hAe hBe hGe hTe
    ext i j
    simp only [sourceExpansionMatrix, Rem, Q, Matrix.map_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.mul_apply, map_add, map_sub, map_sum, map_mul,
      hAe, hBe, hGe, hTe]
    abel
  apply actual_trace_eq_zero_of_coefficientField_corrections b level hb _ Rem
    A0 B0 GammaK ThetaK hRem
  intro i
  have heqi := heq i
  simp only [rho_liftedBasisVector] at heqi
  exact heqi.trans (by
    change (∑ j, ((sourceExpansionMatrix X Y Omega A Bm Gamma Theta).map
      S.modParameter) i j • b j) = _
    rw [hmap]
    simp only [Matrix.add_apply, Matrix.map_apply, add_smul, Finset.sum_add_distrib,
      IsScalarTower.algebraMap_smul]
    simp only [Q, Matrix.add_apply, add_smul, Finset.sum_add_distrib])

/-- The local membership conclusion after choosing a coefficient field and
an adapted basis. The residue scalar is forced to zero by the actual trace. -/
theorem commutator_cofactor_mem_maximalIdeal
    [CharZero K] [IsArtinianRing R]
    (S : LeftPrincipalParameterReduction (B := B) (Abar := R))
    (rho : W →+ V) (hrho : Function.Surjective rho)
    (hact : ∀ a w, rho (a • w) = S.modParameter a • rho w)
    (hker : AddMonoidHom.ker rho =
      AddMonoidHom.range (parameterAct (W := W) S.parameter))
    (hexact : AddMonoidHom.ker (parameterAct (W := W) S.parameter) =
      AddMonoidHom.range (parameterAct (W := W) S.parameter))
    (hc2 : S.parameter * S.parameter = 0)
    (b : Module.Basis ι K V) (level : ι → ℕ)
    (hb : IsMaximalIdealFiltrationAdapted (IsLocalRing.maximalIdeal R) b level)
    (hcoeff : Function.Surjective
      ((IsLocalRing.residue R).comp (algebraMap K R)))
    (x y z : B) (hx : S.modParameter x ∈ IsLocalRing.maximalIdeal R)
    (hy : S.modParameter y ∈ IsLocalRing.maximalIdeal R)
    (hxy : x * y - y * x = S.parameter * z) :
    S.modParameter z ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨q, hq⟩ := hcoeff (IsLocalRing.residue R (S.modParameter z))
  let r := S.modParameter z - algebraMap K R q
  have hr : r ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    change IsLocalRing.residue R (S.modParameter z - algebraMap K R q) = 0
    rw [map_sub, show IsLocalRing.residue R (algebraMap K R q) =
      IsLocalRing.residue R (S.modParameter z) from hq, sub_self]
  have hz : S.modParameter z = algebraMap K R q + r := by dsimp [r]; ring
  have htrace := actual_commutator_cofactor_trace_eq_zero
    S rho hrho hact hker hexact hc2 b level hb x y z hx hy hxy
  have hq0 := Stafford38.Characteristic.ArtinianTriangularTrace.scalar_eq_zero_of_trace_identity
    q _ _ (leftMultiplicationMatrix_isNilpotent b hr) htrace
    (leftMultiplicationMatrix_decomposition b q r (S.modParameter z) hz).symm
  simpa [r, hq0] using hr

/-- An Artinian local algebra is finite over a coefficient field. -/
theorem finite_over_coefficientField [IsArtinianRing R]
    (hcoeff : Function.Surjective
      ((IsLocalRing.residue R).comp (algebraMap K R))) : Module.Finite K R := by
  let m := IsLocalRing.maximalIdeal R
  let : Module.Finite K (R ⧸ m) :=
    Module.Finite.of_surjective (Algebra.linearMap K (R ⧸ m)) hcoeff
  apply Module.finite_of_surjective_of_ker_le_nilradical
    (Ideal.Quotient.mkₐ K m) Ideal.Quotient.mk_surjective
  · have hker : RingHom.ker (Ideal.Quotient.mkₐ K m) = m := by
      ext z
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [hker]
    exact (Ideal.FG.isNilpotent_iff_le_nilradical
      (IsNoetherian.noetherian m)).mp
      (Stafford38.Characteristic.ArtinianCoefficientField.maximalIdeal_isNilpotent (R := R))
  · exact IsNoetherian.noetherian _

/-- Local Gabber membership with the finite-dimensional basis constructed
from the finite special-fibre module. No action matrix or trace is supplied. -/
theorem artinian_local_commutator_cofactor_mem_maximalIdeal
    [CharZero K] [IsArtinianRing R] [Module.Finite R V] [Nontrivial V]
    (S : LeftPrincipalParameterReduction (B := B) (Abar := R))
    (rho : W →+ V) (hrho : Function.Surjective rho)
    (hact : ∀ a w, rho (a • w) = S.modParameter a • rho w)
    (hker : AddMonoidHom.ker rho =
      AddMonoidHom.range (parameterAct (W := W) S.parameter))
    (hexact : AddMonoidHom.ker (parameterAct (W := W) S.parameter) =
      AddMonoidHom.range (parameterAct (W := W) S.parameter))
    (hc2 : S.parameter * S.parameter = 0)
    (hcoeff : Function.Surjective
      ((IsLocalRing.residue R).comp (algebraMap K R)))
    (x y z : B) (hx : S.modParameter x ∈ IsLocalRing.maximalIdeal R)
    (hy : S.modParameter y ∈ IsLocalRing.maximalIdeal R)
    (hxy : x * y - y * x = S.parameter * z) :
    S.modParameter z ∈ IsLocalRing.maximalIdeal R := by
  let : Module.Finite K R := finite_over_coefficientField hcoeff
  let : Module.Finite K V := Module.Finite.trans R V
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (ne_of_gt (Module.finrank_pos (R := K) (M := V)))
  obtain ⟨b, level, hb⟩ :=
    Characteristic.ArtinianAdaptedBasisExistence.exists_maximalIdealFiltrationAdaptedBasis
      (K := K) (R := R) (V := V) hn
  exact commutator_cofactor_mem_maximalIdeal S rho hrho hact hker hexact hc2
    b level hb hcoeff x y z hx hy hxy

end SourceRing

section CoefficientFieldProduction

variable {B W : Type u}
variable [Ring B] [AddCommGroup W] [Module B W]

omit [Algebra K R] [Module K V] [IsScalarTower K R V] in
/-- Proposition 3.2 for a nonzero finite special fibre: the coefficient
field, finite basis, source corrections, and actual trace are all produced. -/
theorem artinian_local_cofactor_mem_maximalIdeal
    (F : Type u) [Field F] [CharZero F] [Algebra F R]
    [IsArtinianRing R] [Module.Finite R V] [Nontrivial V]
    (S : LeftPrincipalParameterReduction (B := B) (Abar := R))
    (rho : W →+ V) (hrho : Function.Surjective rho)
    (hact : ∀ a w, rho (a • w) = S.modParameter a • rho w)
    (hker : AddMonoidHom.ker rho =
      AddMonoidHom.range (parameterAct (W := W) S.parameter))
    (hexact : AddMonoidHom.ker (parameterAct (W := W) S.parameter) =
      AddMonoidHom.range (parameterAct (W := W) S.parameter))
    (hc2 : S.parameter * S.parameter = 0)
    (x y z : B) (hx : S.modParameter x ∈ IsLocalRing.maximalIdeal R)
    (hy : S.modParameter y ∈ IsLocalRing.maximalIdeal R)
    (hxy : x * y - y * x = S.parameter * z) :
    S.modParameter z ∈ IsLocalRing.maximalIdeal R := by
  let κ := IsLocalRing.ResidueField R
  obtain ⟨s, hs⟩ := Stafford38.Characteristic.ArtinianCoefficientField.exists_residue_section F R
  let : CharZero κ := charZero_of_injective_algebraMap (algebraMap F κ).injective
  let : Algebra κ R := s.toRingHom.toAlgebra
  let : Module κ V := Module.compHom V (algebraMap κ R)
  let : IsScalarTower κ R V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hcoeff : Function.Surjective
      ((IsLocalRing.residue R).comp (algebraMap κ R)) := fun a ↦ ⟨a, hs a⟩
  exact artinian_local_commutator_cofactor_mem_maximalIdeal
    S rho hrho hact hker hexact hc2 hcoeff x y z hx hy hxy

end CoefficientFieldProduction


end
end Stafford38.Characteristic.BGab001CoefficientFieldTrace
