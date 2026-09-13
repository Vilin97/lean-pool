/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.Basic
public import LeanPool.RiemannRochFunctionFields.LocalResidue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Riemann–Roch spaces `L(D)`

This file defines the Riemann–Roch space of a divisor on a function field and its dimension
`ℓ(D)`.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace FunctionField.Chart

lemma exp_neg_mul_lt_one_iff_le (x : ℤᵐ⁰) (n : ℤ) :
    WithZero.exp (-n) * x < 1 ↔ x ≤ WithZero.exp (n - 1) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [← WithZero.log_lt_log (mul_ne_zero WithZero.exp_ne_zero hx) one_ne_zero]
  rw [WithZero.log_mul WithZero.exp_ne_zero hx, WithZero.log_exp, WithZero.log_one]
  rw [← WithZero.log_le_iff_le_exp hx]
  omega

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

/-- The classical decidable equality on `k(X)` used by the coordinate places. -/
local instance instDecidableEqRatFuncRRspace : DecidableEq k⟮X⟯ := Classical.decEq _

omit [Algebra k K] [IsScalarTower k k[X] K] in
theorem nonempty_placeA : Nonempty (PlaceA k K) := by
  let P : Ideal k[X] := Ideal.span {Polynomial.X}
  let : P.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
  obtain ⟨Q, hQprime, hQunder⟩ :=
    P.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := ringOfIntegers k K) (by simp)
  have hQ0 : Q ≠ ⊥ := by
    intro hQ
    have hP : P = ⊥ := by simpa [hQ] using hQunder.symm
    have hX : Polynomial.X ∈ P := Ideal.subset_span (Set.mem_singleton _)
    rw [hP, Ideal.mem_bot] at hX
    exact Polynomial.X_ne_zero hX
  exact ⟨Sum.inl ⟨Q, hQprime, hQ0⟩⟩

/-- A function belongs to the Riemann–Roch space of `D` when its valuation at every place `v`
is at most `WithZero.exp (D v)`, i.e. `ord_v f ≥ -D v` in additive notation. The zero function
belongs trivially since its valuation is `0`. -/
def memRRspace (D : DivisorA k K) (f : K) : Prop :=
  ∀ v, placeValuation k K v f ≤ WithZero.exp (D v)

namespace memRRspace

variable {D : DivisorA k K}

omit [Algebra k K] [IsScalarTower k k[X] K] in
theorem zero_mem (D : DivisorA k K) : memRRspace k K D 0 := fun v => by
  rw [map_zero]
  exact zero_le

omit [Algebra k K] [IsScalarTower k k[X] K] in
theorem add_mem {f g : K} (hf : memRRspace k K D f) (hg : memRRspace k K D g) :
    memRRspace k K D (f + g) := fun v =>
  le_trans (Valuation.map_add _ f g) (max_le (hf v) (hg v))

theorem smul_mem (c : k) {f : K} (hf : memRRspace k K D f) :
    memRRspace k K D (c • f) := fun v => by
  rw [Algebra.smul_def, map_mul]
  calc placeValuation k K v (algebraMap k K c) * placeValuation k K v f
      ≤ 1 * WithZero.exp (D v) :=
        mul_le_mul' (placeValuation_algebraMap_le_one k K v c) (hf v)
    _ = WithZero.exp (D v) := one_mul _

omit [Algebra k K] [IsScalarTower k k[X] K] in
theorem one_mem : memRRspace k K 0 1 := fun v => by
  rw [Valuation.map_one (placeValuation k K v)]
  change (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp ((0 : DivisorA k K) v)
  rw [Finsupp.zero_apply, ← WithZero.exp_zero]

omit [Algebra k K] [IsScalarTower k k[X] K] in
theorem mul_mem {D E : DivisorA k K} {f g : K} (hf : memRRspace k K D f)
    (hg : memRRspace k K E g) :
    memRRspace k K (D + E) (f * g) := fun v => by
  rw [Valuation.map_mul (placeValuation k K v), Finsupp.add_apply]
  calc placeValuation k K v f * placeValuation k K v g
        ≤ WithZero.exp (D v) * WithZero.exp (E v) := mul_le_mul' (hf v) (hg v)
    _ = WithZero.exp (D v + E v) := by rw [← WithZero.exp_add]

omit [Algebra k K] [IsScalarTower k k[X] K] in
theorem memRRspace_mono {D E : DivisorA k K} (h : D ≤ E) {f : K} (hf : memRRspace k K D f) :
    memRRspace k K E f := fun v =>
  (hf v).trans (WithZero.exp_le_exp.mpr (h v))

omit [Algebra k K] [IsScalarTower k k[X] K] in
theorem pow_mem {D : DivisorA k K} {f : K} (hf : memRRspace k K D f) :
    ∀ n : ℕ, memRRspace k K (n • D) (f ^ n) := by
  intro n
  induction n with
  | zero =>
      simpa using one_mem (k := k) (K := K)
  | succ n ih =>
      rw [succ_nsmul, pow_succ]
      exact mul_mem (k := k) (K := K) ih hf

end memRRspace

/-- The Riemann–Roch space `L(D)`. -/
def RRspace (D : DivisorA k K) : Submodule k K where
  carrier := {f | memRRspace k K D f}
  zero_mem' := memRRspace.zero_mem (k := k) (K := K) D
  add_mem' hf hg := memRRspace.add_mem (k := k) (K := K) hf hg
  smul_mem' c _ hf := memRRspace.smul_mem (k := k) (K := K) c hf

/-- The dimension `ℓ(D)`. -/
noncomputable def ell (D : DivisorA k K) : ℕ :=
  Module.finrank k (RRspace k K D)

@[simp]
theorem mem_RRspace_iff (D : DivisorA k K) (f : K) :
    f ∈ RRspace k K D ↔ memRRspace k K D f := by
  simp [RRspace]

theorem RRspace_mono {D D' : DivisorA k K} (h : D ≤ D') :
    RRspace k K D ≤ RRspace k K D' := by
  intro f hf
  rw [mem_RRspace_iff] at hf ⊢
  exact fun v => (hf v).trans (WithZero.exp_le_exp.mpr (h v))

/-- Multiplication by a nonzero function identifies `L(D + (x))` with `L(D)`. -/
noncomputable def RRspaceAddPrincipalEquiv (D : DivisorA k K) (x : Kˣ) :
    RRspace k K (D + principalDivisorA k K (Additive.ofMul x)) ≃ₗ[k]
      RRspace k K D where
  toFun f := ⟨(x : K) * f.val, by
    intro v
    change placeValuation k K v ((x : K) * f.val) ≤ WithZero.exp (D v)
    rw [map_mul]
    have hxval := placeValuation_eq_exp_neg_principalDivisor k K (Additive.ofMul x) v
    change placeValuation k K v (x : K) =
      WithZero.exp (-(principalDivisorA k K (Additive.ofMul x) v)) at hxval
    rw [hxval]
    have hf := f.property v
    rw [Finsupp.add_apply, WithZero.exp_add] at hf
    calc
      WithZero.exp (-(principalDivisorA k K (Additive.ofMul x) v)) *
          placeValuation k K v f.val ≤
          WithZero.exp (-(principalDivisorA k K (Additive.ofMul x) v)) *
            (WithZero.exp (D v) *
              WithZero.exp (principalDivisorA k K (Additive.ofMul x) v)) :=
        mul_le_mul_right hf _
      _ = WithZero.exp (D v) := by
        rw [← WithZero.exp_add, ← WithZero.exp_add]
        congr 1
        ring⟩
  invFun f := ⟨((x⁻¹ : Kˣ) : K) * f.val, by
    intro v
    change placeValuation k K v (((x⁻¹ : Kˣ) : K) * f.val) ≤
      WithZero.exp ((D + principalDivisorA k K (Additive.ofMul x)) v)
    rw [map_mul]
    have hxinv := placeValuation_eq_exp_neg_principalDivisor k K
      (Additive.ofMul (x⁻¹ : Kˣ)) v
    have hxinv' : placeValuation k K v ((x⁻¹ : Kˣ) : K) =
        WithZero.exp (principalDivisorA k K (Additive.ofMul x) v) := by
      change placeValuation k K v ((x⁻¹ : Kˣ) : K) = _ at hxinv ⊢
      simpa using hxinv
    rw [hxinv', Finsupp.add_apply, WithZero.exp_add]
    calc
      WithZero.exp (principalDivisorA k K (Additive.ofMul x) v) *
          placeValuation k K v f.val ≤
          WithZero.exp (principalDivisorA k K (Additive.ofMul x) v) *
            WithZero.exp (D v) := mul_le_mul_right (f.property v) _
      _ = WithZero.exp (D v) *
          WithZero.exp (principalDivisorA k K (Additive.ofMul x) v) := mul_comm _ _⟩
  left_inv f := Subtype.ext (by
    change ((x⁻¹ : Kˣ) : K) * ((x : K) * f.val) = f.val
    rw [← mul_assoc, Units.inv_mul, one_mul])
  right_inv f := Subtype.ext (by
    change (x : K) * (((x⁻¹ : Kˣ) : K) * f.val) = f.val
    rw [← mul_assoc, Units.mul_inv, one_mul])
  map_add' f g := by
    apply Subtype.ext
    exact mul_add (x : K) f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    change (x : K) * (c • f.val) = c • ((x : K) * f.val)
    simp only [Algebra.smul_def]
    ring

/-- Riemann–Roch dimensions are invariant under adding a principal divisor. -/
theorem ell_add_principal (D : DivisorA k K) (x : Kˣ) :
    ell k K (D + principalDivisorA k K (Additive.ofMul x)) = ell k K D := by
  exact (RRspaceAddPrincipalEquiv k K D x).finrank_eq

/-- The rank of the quotient `L(D') / L(D)` (with intersection semantics when unordered). -/
noncomputable def finrankRRspaceDiff (D D' : DivisorA k K) : ℕ := by
  letI : AddCommGroup (RRspace k K D') := Submodule.addCommGroup _
  letI : Module k (RRspace k K D') := Submodule.module _
  exact Module.finrank k <|
    (RRspace k K D') ⧸
      Submodule.comap (RRspace k K D').subtype (RRspace k K D)

/-- One-step local residue map at a finite coordinate place. -/
noncomputable def finiteLocalResidueMap (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    RRspace k K (D + Finsupp.single (Sum.inl v) 1) →ₗ[k] v.asIdeal.ResidueField := by
  let A := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v
  letI : Algebra k A :=
    ((algebraMap (ringOfIntegers k K) A).comp
      (algebraMap k (ringOfIntegers k K))).toAlgebra
  letI : IsScalarTower k (ringOfIntegers k K) A :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let π : K := Classical.choose (v.valuation_exists_uniformizer K)
  let n : ℤ := D (Sum.inl v) + 1
  let toA : RRspace k K (D + Finsupp.single (Sum.inl v) 1) → A := fun f =>
    ⟨π ^ n * (f : K), by
      change π ^ n * (f : K) ∈
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v
      rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
        Valuation.mem_valuationSubring_iff]
      have hπpow : v.valuation K (π ^ n) = WithZero.exp (-1) ^ n := by
        rw [map_zpow₀, Classical.choose_spec (v.valuation_exists_uniformizer K)]
      rw [map_mul, hπpow]
      have hf : v.valuation K (f : K) ≤ WithZero.exp n := by
        simpa [placeValuation, n] using f.property (Sum.inl v)
      calc
        WithZero.exp (-1) ^ n * v.valuation K (f : K)
            ≤ WithZero.exp (-1) ^ n * WithZero.exp n := mul_le_mul_right hf _
        _ = 1 := by
          rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
          convert WithZero.exp_zero
          simp⟩
  exact
    { toFun := fun f =>
        IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v (toA f)
      map_add' := fun f g => by
        rw [← map_add]
        congr 1
        apply Subtype.ext
        simp [toA, mul_add]
      map_smul' := fun c f => by
        have hz : toA (c • f) = algebraMap k A c * toA f := by
          apply Subtype.ext
          simp only [toA, Submodule.coe_smul_of_tower, Algebra.smul_def]
          change π ^ n * (algebraMap k K c * (f : K)) =
            (↑(algebraMap k A c) : K) * (π ^ n * (f : K))
          have hcA : (↑(algebraMap k A c) : K) = algebraMap k K c := by
            calc
              (↑(algebraMap k A c) : K) =
                  ↑(algebraMap (ringOfIntegers k K) A
                    (algebraMap k (ringOfIntegers k K) c)) := by
                rw [IsScalarTower.algebraMap_apply k (ringOfIntegers k K) A]
              _ = algebraMap (ringOfIntegers k K) K
                  (algebraMap k (ringOfIntegers k K) c) := rfl
              _ = algebraMap k K c :=
                (IsScalarTower.algebraMap_apply k (ringOfIntegers k K) K c).symm
          rw [hcA]
          ring
        rw [hz, map_mul]
        rw [Algebra.smul_def]
        congr 1
        rw [IsScalarTower.algebraMap_apply k (ringOfIntegers k K) A]
        rw [IsDedekindDomain.HeightOneSpectrum.residueHom, IsLocalization.lift_eq]
        exact (IsScalarTower.algebraMap_apply k (ringOfIntegers k K)
          v.asIdeal.ResidueField c).symm }

theorem finiteLocalResidueMap_ker (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    (finiteLocalResidueMap k K D v).ker =
      Submodule.comap (RRspace k K (D + Finsupp.single (Sum.inl v) 1)).subtype
        (RRspace k K D) := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype,
    mem_RRspace_iff]
  change IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v
      ⟨(Classical.choose (v.valuation_exists_uniformizer K)) ^
          (D (Sum.inl v) + 1) * (f : K), _⟩ = 0 ↔
    ∀ w, placeValuation k K w (f : K) ≤ WithZero.exp (D w)
  rw [IsDedekindDomain.HeightOneSpectrum.residueHom_eq_zero_iff]
  have hπ := Classical.choose_spec (v.valuation_exists_uniformizer K)
  rw [map_mul, map_zpow₀, hπ]
  rw [← WithZero.exp_zsmul]
  have hnsmul : (D (Sum.inl v) + 1) • (-1 : ℤ) = -(D (Sum.inl v) + 1) := by
    simp
  rw [hnsmul]
  have hlocal : WithZero.exp (-(D (Sum.inl v) + 1)) * v.valuation K (f : K) < 1 ↔
      v.valuation K (f : K) ≤ WithZero.exp (D (Sum.inl v)) := by
    simpa using exp_neg_mul_lt_one_iff_le
      (v.valuation K (f : K)) (D (Sum.inl v) + 1)
  rw [hlocal]
  constructor
  · intro hv w
    by_cases hw : w = Sum.inl v
    · subst w
      exact hv
    · have hf := f.property w
      simpa [placeValuation, hw] using hf
  · intro hf
    simpa [placeValuation] using hf (Sum.inl v)

/-- The residue field at a finite coordinate place as a `k`-linear copy of the quotient
`ringOfIntegers k K ⧸ v.asIdeal`. -/
noncomputable def finiteResidueFieldEquiv
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    (ringOfIntegers k K ⧸ v.asIdeal) ≃ₗ[k] v.asIdeal.ResidueField :=
  LinearEquiv.ofBijective
    ((Algebra.linearMap (ringOfIntegers k K ⧸ v.asIdeal)
      v.asIdeal.ResidueField).restrictScalars k)
    (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal)

/-- The residue field at an infinite coordinate place as a `k`-linear copy of the quotient
`infiniteIntegers k K ⧸ v.asIdeal`. -/
noncomputable def infiniteResidueFieldEquiv
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    (infiniteIntegers k K ⧸ v.asIdeal) ≃ₗ[k] v.asIdeal.ResidueField :=
  LinearEquiv.ofBijective
    ((Algebra.linearMap (infiniteIntegers k K ⧸ v.asIdeal)
      v.asIdeal.ResidueField).restrictScalars k)
    (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal)

theorem finrankRRspaceDiff_single_finite_le (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    finrankRRspaceDiff k K D (D + Finsupp.single (Sum.inl v) 1) ≤
      placeDegree k K (Sum.inl v) := by
  let f := finiteLocalResidueMap k K D v
  let e : (ringOfIntegers k K ⧸ v.asIdeal) ≃ₗ[k] v.asIdeal.ResidueField :=
    finiteResidueFieldEquiv k K v
  let : FiniteDimensional k v.asIdeal.ResidueField := e.finiteDimensional
  have hker := finiteLocalResidueMap_ker k K D v
  rw [finrankRRspaceDiff, ← hker, f.quotKerEquivRange.finrank_eq]
  calc
    Module.finrank k f.range ≤ Module.finrank k v.asIdeal.ResidueField :=
      f.range.finrank_le
    _ = Module.finrank k (ringOfIntegers k K ⧸ v.asIdeal) := by
      exact e.finrank_eq.symm
    _ = placeDegree k K (Sum.inl v) := rfl

/-- One-step local residue map at an infinite coordinate place. -/
noncomputable def infiniteLocalResidueMap (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    RRspace k K (D + Finsupp.single (Sum.inr v) 1) →ₗ[k] v.asIdeal.ResidueField := by
  let A := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v
  letI : Algebra k A :=
    ((algebraMap (infiniteIntegers k K) A).comp
      (algebraMap k (infiniteIntegers k K))).toAlgebra
  letI : IsScalarTower k (infiniteIntegers k K) A :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let π : K := Classical.choose (v.valuation_exists_uniformizer K)
  let n : ℤ := D (Sum.inr v) + 1
  let toA : RRspace k K (D + Finsupp.single (Sum.inr v) 1) → A := fun f =>
    ⟨π ^ n * (f : K), by
      change π ^ n * (f : K) ∈
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v
      rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
        Valuation.mem_valuationSubring_iff]
      have hπpow : v.valuation K (π ^ n) = WithZero.exp (-1) ^ n := by
        rw [map_zpow₀, Classical.choose_spec (v.valuation_exists_uniformizer K)]
      rw [map_mul, hπpow]
      have hf : v.valuation K (f : K) ≤ WithZero.exp n := by
        simpa [placeValuation, n] using f.property (Sum.inr v)
      calc
        WithZero.exp (-1) ^ n * v.valuation K (f : K)
            ≤ WithZero.exp (-1) ^ n * WithZero.exp n := mul_le_mul_right hf _
        _ = 1 := by
          rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
          convert WithZero.exp_zero
          simp⟩
  exact
    { toFun := fun f =>
        IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v (toA f)
      map_add' := fun f g => by
        rw [← map_add]
        congr 1
        apply Subtype.ext
        simp [toA, mul_add]
      map_smul' := fun c f => by
        have hz : toA (c • f) = algebraMap k A c * toA f := by
          apply Subtype.ext
          simp only [toA, Submodule.coe_smul_of_tower, Algebra.smul_def]
          change π ^ n * (algebraMap k K c * (f : K)) =
            (↑(algebraMap k A c) : K) * (π ^ n * (f : K))
          have hcA : (↑(algebraMap k A c) : K) = algebraMap k K c := by
            calc
              (↑(algebraMap k A c) : K) =
                  ↑(algebraMap (infiniteIntegers k K) A
                    (algebraMap k (infiniteIntegers k K) c)) := by
                rw [IsScalarTower.algebraMap_apply k (infiniteIntegers k K) A]
              _ = algebraMap (infiniteIntegers k K) K
                  (algebraMap k (infiniteIntegers k K) c) := rfl
              _ = algebraMap k K c :=
                (IsScalarTower.algebraMap_apply k (infiniteIntegers k K) K c).symm
          rw [hcA]
          ring
        rw [hz, map_mul]
        rw [Algebra.smul_def]
        congr 1
        rw [IsScalarTower.algebraMap_apply k (infiniteIntegers k K) A]
        rw [IsDedekindDomain.HeightOneSpectrum.residueHom, IsLocalization.lift_eq]
        exact (IsScalarTower.algebraMap_apply k (infiniteIntegers k K)
          v.asIdeal.ResidueField c).symm }

theorem infiniteLocalResidueMap_ker (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    (infiniteLocalResidueMap k K D v).ker =
      Submodule.comap (RRspace k K (D + Finsupp.single (Sum.inr v) 1)).subtype
        (RRspace k K D) := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype,
    mem_RRspace_iff]
  change IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v
      ⟨(Classical.choose (v.valuation_exists_uniformizer K)) ^
          (D (Sum.inr v) + 1) * (f : K), _⟩ = 0 ↔
    ∀ w, placeValuation k K w (f : K) ≤ WithZero.exp (D w)
  rw [IsDedekindDomain.HeightOneSpectrum.residueHom_eq_zero_iff]
  have hπ := Classical.choose_spec (v.valuation_exists_uniformizer K)
  rw [map_mul, map_zpow₀, hπ]
  rw [← WithZero.exp_zsmul]
  have hnsmul : (D (Sum.inr v) + 1) • (-1 : ℤ) = -(D (Sum.inr v) + 1) := by
    simp
  rw [hnsmul]
  have hlocal : WithZero.exp (-(D (Sum.inr v) + 1)) * v.valuation K (f : K) < 1 ↔
      v.valuation K (f : K) ≤ WithZero.exp (D (Sum.inr v)) := by
    simpa using exp_neg_mul_lt_one_iff_le
      (v.valuation K (f : K)) (D (Sum.inr v) + 1)
  rw [hlocal]
  constructor
  · intro hv w
    by_cases hw : w = Sum.inr v
    · subst w
      exact hv
    · have hf := f.property w
      simpa [placeValuation, hw] using hf
  · intro hf
    simpa [placeValuation] using hf (Sum.inr v)

theorem finrankRRspaceDiff_single_infinite_le (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    finrankRRspaceDiff k K D (D + Finsupp.single (Sum.inr v) 1) ≤
      placeDegree k K (Sum.inr v) := by
  let f := infiniteLocalResidueMap k K D v
  let e : (infiniteIntegers k K ⧸ v.asIdeal) ≃ₗ[k] v.asIdeal.ResidueField :=
    infiniteResidueFieldEquiv k K v
  let : FiniteDimensional k v.asIdeal.ResidueField := e.finiteDimensional
  have hker := infiniteLocalResidueMap_ker k K D v
  rw [finrankRRspaceDiff, ← hker, f.quotKerEquivRange.finrank_eq]
  calc
    Module.finrank k f.range ≤ Module.finrank k v.asIdeal.ResidueField :=
      f.range.finrank_le
    _ = Module.finrank k (infiniteIntegers k K ⧸ v.asIdeal) := by
      exact e.finrank_eq.symm
    _ = placeDegree k K (Sum.inr v) := rfl

theorem finiteDimensional_add_single_one (D : DivisorA k K) (v : PlaceA k K)
    [FiniteDimensional k (RRspace k K D)] :
    FiniteDimensional k (RRspace k K (D + Finsupp.single v 1)) := by
  classical
  have hle : RRspace k K D ≤ RRspace k K (D + Finsupp.single v 1) := by
    apply RRspace_mono k K
    intro w
    simp only [Finsupp.add_apply]
    exact le_add_of_nonneg_right (by
      simp only [Finsupp.single_apply]
      split <;> omega)
  let p := Submodule.comap (RRspace k K (D + Finsupp.single v 1)).subtype
    (RRspace k K D)
  let : Module.Finite k p :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hle).symm
  rcases v with v | v
  · let f := finiteLocalResidueMap k K D v
    let e : (ringOfIntegers k K ⧸ v.asIdeal) ≃ₗ[k] v.asIdeal.ResidueField :=
      finiteResidueFieldEquiv k K v
    let : FiniteDimensional k v.asIdeal.ResidueField := e.finiteDimensional
    let : Module.Finite k f.range := inferInstance
    have hqker : Module.Finite k
        (RRspace k K (D + Finsupp.single (Sum.inl v) 1) ⧸ f.ker) :=
      Module.Finite.equiv f.quotKerEquivRange.symm
    have hqp : Module.Finite k
        (RRspace k K (D + Finsupp.single (Sum.inl v) 1) ⧸ p) := by
      exact Module.Finite.equiv (Submodule.quotEquivOfEq f.ker p
        (finiteLocalResidueMap_ker k K D v))
    exact Module.Finite.of_submodule_quotient p
  · let f := infiniteLocalResidueMap k K D v
    let e : (infiniteIntegers k K ⧸ v.asIdeal) ≃ₗ[k] v.asIdeal.ResidueField :=
      infiniteResidueFieldEquiv k K v
    let : FiniteDimensional k v.asIdeal.ResidueField := e.finiteDimensional
    let : Module.Finite k f.range := inferInstance
    have hqker : Module.Finite k
        (RRspace k K (D + Finsupp.single (Sum.inr v) 1) ⧸ f.ker) :=
      Module.Finite.equiv f.quotKerEquivRange.symm
    have hqp : Module.Finite k
        (RRspace k K (D + Finsupp.single (Sum.inr v) 1) ⧸ p) := by
      exact Module.Finite.equiv (Submodule.quotEquivOfEq f.ker p
        (infiniteLocalResidueMap_ker k K D v))
    exact Module.Finite.of_submodule_quotient p

theorem finiteDimensional_add_single_nat (D : DivisorA k K) (v : PlaceA k K)
    (n : ℕ) [FiniteDimensional k (RRspace k K D)] :
    FiniteDimensional k (RRspace k K (D + Finsupp.single v (n : ℤ))) := by
  induction n with
  | zero =>
      have heq : D + Finsupp.single v ((0 : ℕ) : ℤ) = D := by simp
      rw [heq]
      infer_instance
  | succ n ih =>
      let : FiniteDimensional k
          (RRspace k K (D + Finsupp.single v (n : ℤ))) := ih
      have hfin := finiteDimensional_add_single_one k K
        (D + Finsupp.single v (n : ℤ)) v
      have heq : D + Finsupp.single v ((n + 1 : ℕ) : ℤ) =
          (D + Finsupp.single v (n : ℤ)) + Finsupp.single v 1 := by
        classical
        ext w
        simp only [Finsupp.add_apply, Finsupp.single_apply]
        split <;> omega
      rw [heq]
      exact hfin

theorem finrankRRspaceDiff_add_finrank_of_finite {D D' : DivisorA k K}
    (h : D ≤ D') [FiniteDimensional k (RRspace k K D')] :
    finrankRRspaceDiff k K D D' + Module.finrank k (RRspace k K D) =
      Module.finrank k (RRspace k K D') := by
  let : AddCommGroup (RRspace k K D') := Submodule.addCommGroup _
  let : Module k (RRspace k K D') := Submodule.module _
  rw [finrankRRspaceDiff,
    ← (Submodule.comapSubtypeEquivOfLe (RRspace_mono k K h)).finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _

theorem finrankRRspaceDiff_single_one_le (D : DivisorA k K) (v : PlaceA k K) :
    finrankRRspaceDiff k K D (D + Finsupp.single v 1) ≤ placeDegree k K v := by
  rcases v with v | v
  · exact finrankRRspaceDiff_single_finite_le k K D v
  · exact finrankRRspaceDiff_single_infinite_le k K D v

theorem finrankRRspaceDiff_single_nat_le (D : DivisorA k K) (v : PlaceA k K)
    (n : ℕ) [FiniteDimensional k (RRspace k K D)] :
    finrankRRspaceDiff k K D (D + Finsupp.single v (n : ℤ)) ≤
      n * placeDegree k K v := by
  induction n with
  | zero =>
      simp only [Nat.cast_zero, Finsupp.single_zero, add_zero, zero_mul]
      rw [finrankRRspaceDiff]
      have hp : Submodule.comap (RRspace k K D).subtype (RRspace k K D) = ⊤ := by
        ext f
        simp
      rw [hp]
      have h := Submodule.finrank_quotient_add_finrank
        (⊤ : Submodule k (RRspace k K D))
      simp only [finrank_top] at h
      omega
  | succ n ih =>
      let M := D + Finsupp.single v (n : ℤ)
      let N := M + Finsupp.single v 1
      let : FiniteDimensional k (RRspace k K M) :=
        finiteDimensional_add_single_nat k K D v n
      let : FiniteDimensional k (RRspace k K N) :=
        finiteDimensional_add_single_one k K M v
      have hDM : D ≤ M := by
        intro w
        dsimp only [M]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          classical
          simp only [Finsupp.single_apply]
          split <;> omega)
      have hMN : M ≤ N := by
        intro w
        dsimp only [N]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          classical
          simp only [Finsupp.single_apply]
          split <;> omega)
      have hDN : D ≤ N := hDM.trans hMN
      have hsumDM := finrankRRspaceDiff_add_finrank_of_finite k K hDM
      have hsumMN := finrankRRspaceDiff_add_finrank_of_finite k K hMN
      have hsumDN := finrankRRspaceDiff_add_finrank_of_finite k K hDN
      have hstep := finrankRRspaceDiff_single_one_le k K M v
      change finrankRRspaceDiff k K D M ≤ n * placeDegree k K v at ih
      change finrankRRspaceDiff k K M N ≤ placeDegree k K v at hstep
      have htotal : finrankRRspaceDiff k K D N ≤
          n * placeDegree k K v + placeDegree k K v := by omega
      have heq : D + Finsupp.single v ((n + 1 : ℕ) : ℤ) = N := by
        classical
        ext w
        simp only [N, M, Finsupp.add_apply, Finsupp.single_apply]
        split <;> omega
      rw [heq]
      simpa [Nat.succ_mul] using htotal

theorem finiteDimensional_add_effective (D E : DivisorA k K)
    (hE : IsEffective k K E) [FiniteDimensional k (RRspace k K D)] :
    FiniteDimensional k (RRspace k K (D + E)) := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero =>
      rw [add_zero]
      infer_instance
  | single_add a b f ha hb ih =>
      have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
      have hff : IsEffective k K f := by
        intro w
        by_cases hw : w = a
        · subst w
          rw [hfa]
        · have hwE := hE w
          simpa [Finsupp.single_apply, hw] using hwE
      have hb0 : 0 ≤ b := by
        have haE := hE a
        simpa [Finsupp.single_apply, hfa] using haE
      let : FiniteDimensional k (RRspace k K (D + f)) := ih D hff
      have hsingle := finiteDimensional_add_single_nat k K (D + f) a b.toNat
      have hbcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
      have heq : D + (Finsupp.single a b + f) =
          (D + f) + Finsupp.single a (b.toNat : ℤ) := by
        rw [hbcast]
        abel
      rw [heq]
      exact hsingle

theorem finrankRRspaceDiff_add_effective_le (D E : DivisorA k K)
    (hE : IsEffective k K E) [FiniteDimensional k (RRspace k K D)] :
    finrankRRspaceDiff k K D (D + E) ≤ (deg k K E).toNat := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero =>
      rw [add_zero, finrankRRspaceDiff]
      have hp : Submodule.comap (RRspace k K D).subtype (RRspace k K D) = ⊤ := by
        ext f
        simp
      rw [hp, deg_zero]
      have h := Submodule.finrank_quotient_add_finrank
        (⊤ : Submodule k (RRspace k K D))
      simp only [finrank_top] at h
      omega
  | single_add a b f ha hb ih =>
      have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
      have hff : IsEffective k K f := by
        intro w
        by_cases hw : w = a
        · subst w
          rw [hfa]
        · have hwE := hE w
          simpa [Finsupp.single_apply, hw] using hwE
      have hb0 : 0 ≤ b := by
        have haE := hE a
        simpa [Finsupp.single_apply, hfa] using haE
      let M := D + f
      let N := M + Finsupp.single a (b.toNat : ℤ)
      let : FiniteDimensional k (RRspace k K M) :=
        finiteDimensional_add_effective k K D f hff
      let : FiniteDimensional k (RRspace k K N) :=
        finiteDimensional_add_single_nat k K M a b.toNat
      have hDM : D ≤ M := by
        intro w
        dsimp only [M]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (hff w)
      have hMN : M ≤ N := by
        intro w
        dsimp only [N]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      have hDN : D ≤ N := hDM.trans hMN
      have hsumDM := finrankRRspaceDiff_add_finrank_of_finite k K hDM
      have hsumMN := finrankRRspaceDiff_add_finrank_of_finite k K hMN
      have hsumDN := finrankRRspaceDiff_add_finrank_of_finite k K hDN
      have hfirst := ih D hff
      change finrankRRspaceDiff k K D M ≤ (deg k K f).toNat at hfirst
      have hsecond := finrankRRspaceDiff_single_nat_le k K M a b.toNat
      change finrankRRspaceDiff k K M N ≤ b.toNat * placeDegree k K a at hsecond
      have hbcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
      have hdegf : 0 ≤ deg k K f := deg_nonneg k K hff
      have hdegE : deg k K (Finsupp.single a b + f) =
          b * (placeDegree k K a : ℤ) + deg k K f := by
        rw [deg_add]
        simp [deg]
      have hdegE0 : 0 ≤ deg k K (Finsupp.single a b + f) := deg_nonneg k K hE
      have hdegNat : (deg k K (Finsupp.single a b + f)).toNat =
          b.toNat * placeDegree k K a + (deg k K f).toNat := by
        have hfcast : ((deg k K f).toNat : ℤ) = deg k K f :=
          Int.toNat_of_nonneg hdegf
        have hEcast : ((deg k K (Finsupp.single a b + f)).toNat : ℤ) =
            deg k K (Finsupp.single a b + f) := Int.toNat_of_nonneg hdegE0
        apply Int.ofNat_injective
        change ((deg k K (Finsupp.single a b + f)).toNat : ℤ) =
          ((b.toNat * placeDegree k K a + (deg k K f).toNat : ℕ) : ℤ)
        rw [hEcast, Nat.cast_add, Nat.cast_mul, hbcast, hfcast]
        exact hdegE
      have htotal : finrankRRspaceDiff k K D N ≤
          (deg k K (Finsupp.single a b + f)).toNat := by omega
      have heq : D + (Finsupp.single a b + f) = N := by
        dsimp only [N, M]
        rw [hbcast]
        abel
      rw [heq]
      exact htotal

omit [Algebra k K] [IsScalarTower k k[X] K] in
theorem deg_principalDivisor_eq_zero (x : Kˣ) :
    deg k K (principalDivisorA k K (Additive.ofMul x)) = 0 := by
  exact deg_principalDivisorA_eq_zero k K x

theorem RRspace_neg_deg {D : DivisorA k K} (h : deg k K D < 0) :
    RRspace k K D = ⊥ := by
  apply le_antisymm
  · intro f hf
    rw [Submodule.mem_bot]
    by_contra hf0
    let x : Kˣ := Units.mk0 f hf0
    have hdiv : -D ≤ principalDivisorA k K (Additive.ofMul x) := by
      intro v
      have hv := hf v
      have hxval := placeValuation_eq_exp_neg_principalDivisor k K (Additive.ofMul x) v
      change placeValuation k K v f ≤ WithZero.exp (D v) at hv
      change placeValuation k K v f =
        WithZero.exp (-(principalDivisorA k K (Additive.ofMul x) v)) at hxval
      rw [hxval] at hv
      have hexp := WithZero.exp_le_exp.mp hv
      simp only [Finsupp.neg_apply]
      omega
    have hdeg := deg_mono k K hdiv
    rw [deg_neg, deg_principalDivisor_eq_zero k K x] at hdeg
    omega
  · exact bot_le

theorem RRspace_neg_deg_ell {D : DivisorA k K} (h : deg k K D < 0) : ell k K D = 0 := by
  change Module.finrank k (RRspace k K D) = 0
  rw [RRspace_neg_deg k K h]
  exact finrank_bot k K

theorem finiteDimensional_RRspace_aux (D : DivisorA k K) :
    FiniteDimensional k (RRspace k K D) := by
  classical
  let v : PlaceA k K := Classical.choice (nonempty_placeA k K)
  let n : ℕ := (deg k K D).toNat + 1
  let D₀ : DivisorA k K := D - Finsupp.single v (n : ℤ)
  have hdegSingle : deg k K (Finsupp.single v (n : ℤ)) =
      (n : ℤ) * placeDegree k K v := by
    simp [deg]
  have hnpos : 0 < (n : ℤ) := by
    dsimp only [n]
    omega
  have hvpos : 0 < (placeDegree k K v : ℤ) := by
    exact_mod_cast placeDegree_pos k K v
  have hdegDle : deg k K D < (n : ℤ) * placeDegree k K v := by
    by_cases hdeg0 : 0 ≤ deg k K D
    · have hcast : ((deg k K D).toNat : ℤ) = deg k K D :=
        Int.toNat_of_nonneg hdeg0
      have hdlt : deg k K D < (n : ℤ) := by
        dsimp only [n]
        push_cast
        omega
      have hnle : (n : ℤ) ≤ (n : ℤ) * placeDegree k K v := by
        have hvone : (1 : ℤ) ≤ placeDegree k K v := by omega
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hvone hnpos.le
      exact hdlt.trans_le hnle
    · have hprod : 0 < (n : ℤ) * placeDegree k K v :=
        mul_pos hnpos hvpos
      omega
  have hD₀neg : deg k K D₀ < 0 := by
    dsimp only [D₀]
    rw [deg_sub, hdegSingle]
    omega
  have hbot := RRspace_neg_deg k K hD₀neg
  let : FiniteDimensional k (RRspace k K D₀) := by
    rw [hbot]
    infer_instance
  have hfin := finiteDimensional_add_single_nat k K D₀ v n
  have heq : D₀ + Finsupp.single v (n : ℤ) = D := by
    dsimp only [D₀]
    abel
  rw [heq] at hfin
  exact hfin

/-- The local residue-field estimate for an increment of Riemann–Roch spaces. -/
theorem finrank_RRspace_quotient_le {D D' : DivisorA k K} (h : D ≤ D') :
    finrankRRspaceDiff k K D D' ≤ (deg k K (D' - D)).toNat := by
  let : FiniteDimensional k (RRspace k K D) := finiteDimensional_RRspace_aux k K D
  have hE : IsEffective k K (D' - D) := (le_iff_sub_effective k K).mp h
  have hrank := finrankRRspaceDiff_add_effective_le k K D (D' - D) hE
  have heq : D + (D' - D) = D' := by abel
  rw [heq] at hrank
  exact hrank

/-- A function integral at every coordinate place is algebraic over the constant field. -/
theorem isAlgebraic_of_placeValuation_le_one (f : K)
    (hf : ∀ v : PlaceA k K, placeValuation k K v f ≤ 1) : IsAlgebraic k f := by
  by_cases hf0 : f = 0
  · subst f
    exact isAlgebraic_zero
  have hfin := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := ringOfIntegers k K) K f (fun v => hf (Sum.inl v))
  have hinf := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := infiniteIntegers k K) K f (fun v => hf (Sum.inr v))
  obtain ⟨a, ha⟩ := hfin
  obtain ⟨b, hb⟩ := hinf
  let p : k[X][X] := minpoly k[X] a
  let q : (inftyValuationSubring k)[X] := minpoly (inftyValuationSubring k) b
  have hpmap : minpoly k⟮X⟯ f = p.map (algebraMap k[X] k⟮X⟯) := by
    rw [← ha]
    exact minpoly.isIntegrallyClosed_eq_field_fractions k⟮X⟯ K
      (Algebra.IsIntegral.isIntegral a)
  have hqmap : minpoly k⟮X⟯ f =
      q.map (algebraMap (inftyValuationSubring k) k⟮X⟯) := by
    rw [← hb]
    exact minpoly.isIntegrallyClosed_eq_field_fractions k⟮X⟯ K
      (Algebra.IsIntegral.isIntegral b)
  have hpcoeff : ∀ i, p.coeff i ∈ Set.range (Polynomial.C : k →+* k[X]) := by
    intro i
    let c := p.coeff i
    have hcval : RatFunc.inftyValuation k (algebraMap k[X] k⟮X⟯ c) ≤ 1 := by
      have hc : algebraMap k[X] k⟮X⟯ c =
          algebraMap (inftyValuationSubring k) k⟮X⟯ (q.coeff i) := by
        have hc' := congrArg (fun r : k⟮X⟯[X] => r.coeff i) (hpmap.symm.trans hqmap)
        simpa [p, q, c] using hc'
      rw [hc]
      exact (q.coeff i).property
    by_cases hc0 : c = 0
    · refine ⟨0, ?_⟩
      change Polynomial.C 0 = c
      simp [hc0]
    have hdeg : c.natDegree = 0 := by
      rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial (F := k) hc0,
        ← WithZero.exp_zero, WithZero.exp_le_exp] at hcval
      omega
    exact ⟨c.coeff 0, (Polynomial.eq_C_of_natDegree_eq_zero hdeg).symm⟩
  have hprange : p ∈ (Polynomial.mapRingHom (Polynomial.C : k →+* k[X])).range := by
    rw [Polynomial.mem_map_range]
    exact hpcoeff
  obtain ⟨P, hP⟩ := hprange
  have hP0 : P ≠ 0 := by
    intro hP0
    rw [hP0, map_zero] at hP
    have hpmonic : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral a)
    exact hpmonic.ne_zero hP.symm
  refine ⟨P, hP0, ?_⟩
  have hroot : Polynomial.aeval a p = 0 := minpoly.aeval _ _
  rw [← hP] at hroot
  change Polynomial.aeval a (P.map (Polynomial.C : k →+* k[X])) = 0 at hroot
  calc
    Polynomial.aeval f P = Polynomial.aeval f
        (P.map (Polynomial.C : k →+* k[X])) := by
      symm
      exact Polynomial.aeval_map_algebraMap k[X] f P
    _ = algebraMap (ringOfIntegers k K) K
        (Polynomial.aeval a (P.map (Polynomial.C : k →+* k[X]))) := by
      rw [← ha]
      symm
      simp
    _ = 0 := by rw [hroot, map_zero]

theorem ell_zero [IsFullConstantField k K] : ell k K (0 : DivisorA k K) = 1 := by
  let φ : k →ₗ[k] RRspace k K (0 : DivisorA k K) :=
    { toFun := fun c => ⟨algebraMap k K c, by
        intro v
        simpa using placeValuation_algebraMap_le_one k K v c⟩
      map_add' := fun x y => Subtype.ext (map_add (algebraMap k K) x y)
      map_smul' := fun c x => Subtype.ext (by simp [Algebra.smul_def]) }
  have hφ : Function.Bijective φ := by
    constructor
    · intro c d hcd
      apply (algebraMap k K).injective
      exact congrArg Subtype.val hcd
    · intro f
      have hfalg : IsAlgebraic k (f : K) := by
        apply isAlgebraic_of_placeValuation_le_one k K f
        intro v
        simpa [memRRspace] using f.property v
      obtain ⟨c, hc⟩ := IsFullConstantField.algebraic_mem
        (k := k) (K := K) (f : K) hfalg
      refine ⟨c, Subtype.ext ?_⟩
      exact hc.symm
  let e : k ≃ₗ[k] RRspace k K (0 : DivisorA k K) := LinearEquiv.ofBijective φ hφ
  change Module.finrank k (RRspace k K (0 : DivisorA k K)) = 1
  rw [← e.finrank_eq]
  exact Module.finrank_self k

instance finiteDimensional_RRspace (D : DivisorA k K) :
    FiniteDimensional k (RRspace k K D) := by
  exact finiteDimensional_RRspace_aux k K D

/-- Rank-nullity for an inclusion of Riemann–Roch spaces. -/
theorem finrankRRspaceDiff_add_ell {D D' : DivisorA k K} (h : D ≤ D') :
    finrankRRspaceDiff k K D D' + ell k K D = ell k K D' := by
  let : AddCommGroup (RRspace k K D') := Submodule.addCommGroup _
  let : Module k (RRspace k K D') := Submodule.module _
  rw [finrankRRspaceDiff, ell, ell,
    ← (Submodule.comapSubtypeEquivOfLe (RRspace_mono k K h)).finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _

theorem ell_le [IsFullConstantField k K] (D : DivisorA k K) :
    (ell k K D : ℤ) ≤ deg k K (D ⊔ 0) + 1 := by
  let E := D ⊔ 0
  have h0E : (0 : DivisorA k K) ≤ E := le_sup_right
  have hDE : D ≤ E := le_sup_left
  have hdegE : 0 ≤ deg k K E := deg_nonneg k K h0E
  have hq := finrank_RRspace_quotient_le k K h0E
  have hsum := finrankRRspaceDiff_add_ell k K h0E
  have hmono : ell k K D ≤ ell k K E := by
    exact Submodule.finrank_mono (RRspace_mono k K hDE)
  rw [ell_zero k K] at hsum
  have htoNat : ((deg k K E).toNat : ℤ) = deg k K E := Int.toNat_of_nonneg hdegE
  have hqZ : (finrankRRspaceDiff k K 0 E : ℤ) ≤
      ((deg k K (E - 0)).toNat : ℤ) := by exact_mod_cast hq
  simp only [sub_zero] at hqZ
  rw [htoNat] at hqZ
  change (ell k K D : ℤ) ≤ deg k K E + 1
  omega

theorem ell_le_nonneg [IsFullConstantField k K] {D : DivisorA k K} (hD : 0 ≤ D) :
    (ell k K D : ℤ) ≤ deg k K D + 1 := by
  simpa [sup_eq_left.mpr hD] using ell_le k K D

theorem defect_mono {D D' : DivisorA k K} (h : D ≤ D') :
    deg k K D - ell k K D ≤ deg k K D' - ell k K D' := by
  have hdeg : 0 ≤ deg k K (D' - D) :=
    deg_nonneg k K ((le_iff_sub_effective k K).mp h)
  have hq := finrank_RRspace_quotient_le k K h
  have hsum := finrankRRspaceDiff_add_ell k K h
  have htoNat : ((deg k K (D' - D)).toNat : ℤ) = deg k K (D' - D) :=
    Int.toNat_of_nonneg hdeg
  have hqZ : (finrankRRspaceDiff k K D D' : ℤ) ≤
      ((deg k K (D' - D)).toNat : ℤ) := by exact_mod_cast hq
  rw [deg_sub] at htoNat
  rw [deg_sub] at hqZ
  rw [htoNat] at hqZ
  omega

end FunctionField.Chart
