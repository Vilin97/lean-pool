/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLeadingTermCancellation
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannSpace
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.Tactic

/-!
# Riemann-space increments from a local residue map

A local scaling order determines regularity and the residue kernel. Finite and infinite
places supply their local rings and order identities to this common dimension argument.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped nonZeroDivisors Polynomial BigOperators
open IsDedekindDomain

noncomputable section

section LocalLift

variable {K R L : Type*} [Field K] [CommRing R]
  [IsDedekindDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra K R] [Algebra R L] [Algebra K L]
  [IsScalarTower K R L] [IsFractionRing R L]

variable (T : Submodule K L) (a : L)
variable (hregular : ∀ x : T, ∃ r : R, a * x.1 = algebraMap R L r)

/-- A normalized lift of a finite-place residue class into the local ring. -/
noncomputable def localNormalizedLift (x : T) : R :=
  Classical.choose (hregular x)

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] [Algebra K R] [IsScalarTower K R L]
  [IsFractionRing R L] in
theorem localNormalizedLift_spec (x : T) :
    a * x.1 = algebraMap R L (localNormalizedLift T a hregular x) :=
  Classical.choose_spec (hregular x)

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] [Algebra K R] [IsScalarTower K R L] in
theorem localNormalizedLift_add (x y : T) :
    localNormalizedLift T a hregular (x + y) =
      localNormalizedLift T a hregular x + localNormalizedLift T a hregular y := by
  apply IsFractionRing.injective R L
  rw [map_add]
  rw [← localNormalizedLift_spec T a hregular]
  rw [← localNormalizedLift_spec T a hregular]
  rw [← localNormalizedLift_spec T a hregular]
  simp only [Submodule.coe_add]
  ring

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] in
theorem localNormalizedLift_smul (c : K) (x : T) :
    localNormalizedLift T a hregular (c • x) =
      c • localNormalizedLift T a hregular x := by
  apply IsFractionRing.injective R L
  rw [show algebraMap R L (c • localNormalizedLift T a hregular x) =
      c • algebraMap R L (localNormalizedLift T a hregular x) by
    exact map_smul (IsScalarTower.toAlgHom K R L) c _]
  rw [← localNormalizedLift_spec T a hregular]
  rw [← localNormalizedLift_spec T a hregular]
  simp only [Submodule.coe_smul]
  rw [Algebra.smul_def, Algebra.smul_def]
  ring

/-- The linear map sending a residue class to its normalized local lift. -/
noncomputable def localNormalizedLiftLinearMap : T →ₗ[K] R where
  toFun := localNormalizedLift T a hregular
  map_add' := localNormalizedLift_add T a hregular
  map_smul' := localNormalizedLift_smul T a hregular

/-- The linear map extracting the leading residue of a local element. -/
noncomputable def localLeadingResidueLinearMap :
    T →ₗ[K] IsLocalRing.ResidueField R :=
  (Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal R)).toLinearMap.comp
    (localNormalizedLiftLinearMap T a hregular)

theorem localLeadingResidueLinearMap_eq_zero_iff (x : T) :
    localLeadingResidueLinearMap T a hregular x = 0 ↔
      localNormalizedLift T a hregular x ∈ IsLocalRing.maximalIdeal R := by
  exact IsLocalRing.residue_eq_zero_iff _

theorem mem_heightOneSpectrum_of_one_le_finitePlaceOrder_algebraMap
    (v : HeightOneSpectrum R) (r : R)
    (horder : (1 : ℤ) ≤ finitePlaceOrder v (algebraMap R L r)) :
    r ∈ v.asIdeal := by
  by_cases hr : r = 0
  · simp [hr]
  · have hrMap : algebraMap R L r ≠ 0 :=
      by simpa using (IsFractionRing.injective R L).ne hr
    have hvaluation :=
      valuation_eq_exp_neg_finitePlaceOrder v (algebraMap R L r) hrMap
    rw [HeightOneSpectrum.valuation_of_algebraMap] at hvaluation
    rw [← v.intValuation_lt_one_iff_mem]
    rw [hvaluation, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

end LocalLift

/-- A normalized lift has zero residue exactly when its local order is positive. -/
theorem localNormalizedLift_mem_maximalIdeal_iff
    {K R L : Type*} [Field K] [CommRing R]
    [IsDedekindDomain R] [IsDiscreteValuationRing R]
    [Field L] [Algebra R L] [Algebra K L]
    [IsFractionRing R L]
    (T : Submodule K L) (a : L)
    (hregular : ∀ x : T, ∃ r : R, a * x.1 = algebraMap R L r) (x : T) :
    localNormalizedLift T a hregular x ∈ IsLocalRing.maximalIdeal R ↔
      (1 : WithTop ℤ) ≤ finitePlaceOrderTop
        (IsDiscreteValuationRing.maximalIdeal R) (a * x.1) := by
  rw [localNormalizedLift_spec (R := R) T a hregular x]
  let r := localNormalizedLift (R := R) T a hregular x
  by_cases hr : r = 0
  · simp only [show localNormalizedLift T a hregular x = 0 from hr,
      map_zero, Submodule.zero_mem, true_iff]
    simp [finitePlaceOrderTop]
  · have hrMap : algebraMap R L r ≠ 0 :=
      by simpa using (IsFractionRing.injective R L).ne hr
    rw [finitePlaceOrderTop_eq_coe _ _ hrMap]
    constructor
    · intro hmem
      exact_mod_cast one_le_finitePlaceOrder_algebraMap_of_mem (R := R) (L := L)
        (IsDiscreteValuationRing.maximalIdeal R) r hmem hr
    · intro horder
      exact mem_heightOneSpectrum_of_one_le_finitePlaceOrder_algebraMap (R := R) (L := L)
        (IsDiscreteValuationRing.maximalIdeal R) r (by exact_mod_cast horder)


/-- A residue map with the prescribed kernel bounds a finite Riemann-space extension. -/
theorem riemannSpace_finite_and_finrank_le_of_residue_map
    {k E F : Type*} [Field k] [AddCommGroup E] [Module k E]
    [AddCommGroup F] [Module k F] [Module.Finite k F]
    (S T : Submodule k E) [Module.Finite k S] (hST : S ≤ T)
    (f : T →ₗ[k] F) (hker : f.ker = Submodule.comap T.subtype S) :
    Module.Finite k T ∧ Module.finrank k T ≤ Module.finrank k S + Module.finrank k F := by
  let : Module.Finite k f.range := inferInstance
  let : Module.Finite k f.ker := by
    rw [hker]
    exact Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hST).symm
  let : Module.Finite k (T ⧸ f.ker) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  let hTFinite : Module.Finite k T := Module.Finite.of_submodule_quotient f.ker
  have hkerRank : Module.finrank k f.ker = Module.finrank k S := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hST).finrank_eq
  refine ⟨hTFinite, ?_⟩
  calc
    Module.finrank k T = Module.finrank k f.range + Module.finrank k f.ker :=
      f.finrank_range_add_finrank_ker.symm
    _ ≤ Module.finrank k F + Module.finrank k S :=
      Nat.add_le_add f.range.finrank_le (le_of_eq hkerRank)
    _ = Module.finrank k S + Module.finrank k F := Nat.add_comm _ _


section ResidueIncrement

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

/-- The constant-field algebra induced by the canonical maps from `K` through `RatFunc K`. -/
local instance residueIncrementConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp (algebraMap K (RatFunc K)))

/-- A scaling order at a local DVR determines the one-place residue kernel and rank bound. -/
theorem finiteExtensionRiemannSpace_increment_of_local_order
    {R : Type*} [CommRing R] [IsDedekindDomain R] [IsDiscreteValuationRing R]
    [Algebra K R] [Algebra R L] [IsScalarTower K R L] [IsFractionRing R L]
    [Module.Finite K (IsLocalRing.ResidueField R)]
    (D : FiniteExtensionDivisor K L) (Q : FiniteExtensionPlace K L) (a : L)
    [Module.Finite K (finiteExtensionRiemannSpace K L D)]
    (hscaleOrder : ∀ x : L, x ≠ 0 →
      finitePlaceOrderTop (IsDiscreteValuationRing.maximalIdeal R) (a * x) =
        ((D Q + 1 + finiteExtensionPrincipalDivisor K L x Q : ℤ) : WithTop ℤ)) :
    Module.Finite K (finiteExtensionRiemannSpace K L (D + Finsupp.single Q 1)) ∧
      Module.finrank K (finiteExtensionRiemannSpace K L (D + Finsupp.single Q 1)) ≤
        Module.finrank K (finiteExtensionRiemannSpace K L D) +
          Module.finrank K (IsLocalRing.ResidueField R) := by
  let S := finiteExtensionRiemannSpace K L D
  let T := finiteExtensionRiemannSpace K L (D + Finsupp.single Q 1)
  have hregular : ∀ x : T, ∃ r : R, a * x.1 = algebraMap R L r := by
    intro x
    apply finitePlaceOrderTop_exists_lift_of_nonnegative
    by_cases hx0 : x.1 = 0
    · simp [hx0]
    · rw [hscaleOrder x.1 hx0]
      have hxmem := (mem_finiteExtensionRiemannSpace (K := K) (L := L)).mp x.2
      rcases hxmem with hxmem | ⟨_, hxorders⟩
      · exact (hx0 hxmem).elim
      · have hxQ := hxorders Q
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hxQ
        exact_mod_cast (show 0 ≤ D Q + 1 + finiteExtensionPrincipalDivisor K L x.1 Q by
          omega)
  let f := localLeadingResidueLinearMap (K := K) (R := R) (L := L) T a hregular
  have hST : S ≤ T := by
    apply finiteExtensionRiemannSpace_mono
    intro v
    classical
    by_cases hv : v = Q <;> simp [hv]
  have hkerPoint (x : T) : f x = 0 ↔ x.1 ∈ S := by
    rw [localLeadingResidueLinearMap_eq_zero_iff
      (K := K) (R := R) (L := L) T a hregular, localNormalizedLift_mem_maximalIdeal_iff]
    constructor
    · intro haxOrder
      by_cases hx0 : x.1 = 0
      · simp [hx0]
      · rw [hscaleOrder x.1 hx0] at haxOrder
        have haxOrderInt : 1 ≤ D Q + 1 + finiteExtensionPrincipalDivisor K L x.1 Q := by
          exact_mod_cast haxOrder
        rw [mem_finiteExtensionRiemannSpace]
        refine Or.inr ⟨hx0, ?_⟩
        intro v
        by_cases hv : v = Q
        · subst v
          omega
        · have hxmem := (mem_finiteExtensionRiemannSpace (K := K) (L := L)).mp x.2
          rcases hxmem with hxmem | ⟨_, hxorders⟩
          · exact (hx0 hxmem).elim
          · have hxv := hxorders v
            simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hv] at hxv
            simpa using hxv
    · intro hxS
      by_cases hx0 : x.1 = 0
      · simp [hx0]
      · rw [hscaleOrder x.1 hx0]
        have hxmem := (mem_finiteExtensionRiemannSpace (K := K) (L := L)).mp hxS
        rcases hxmem with hxmem | ⟨_, hxorders⟩
        · exact (hx0 hxmem).elim
        · have hxQ := hxorders Q
          exact_mod_cast (show 1 ≤ D Q + 1 + finiteExtensionPrincipalDivisor K L x.1 Q by
            omega)
  have hker : f.ker = Submodule.comap T.subtype S := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    exact hkerPoint x
  exact riemannSpace_finite_and_finrank_le_of_residue_map S T hST f hker

end ResidueIncrement

end
end BGS.HasseWeil
