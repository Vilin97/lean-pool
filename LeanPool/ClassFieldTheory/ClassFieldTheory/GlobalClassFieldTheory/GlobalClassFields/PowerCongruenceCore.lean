/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.LocalResidueArithmetic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlacePowerIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.NormContainment
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.SupportedIdeleIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.SupportedPrincipalQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.PrimePowerKummerIndex
/-!
# Power congruence subgroups inside finite-index idele-class subgroups

Let `H` be a closed finite-index subgroup of the idele class group and let
`n = [C_K : H]`.  Every `n`-th power belongs to `H`.  If a finite set of
finite places contains the support of a congruence subgroup lying in `H`,
the ideles which are local `n`-th powers on that set and integral units
away from it therefore also map into `H`.

This is the concrete power-congruence core used in the existence proof for
global class fields.
-/

@[expose] public section

open scoped NumberField
noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain
open GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- Let `n = [C_K : H]`.  If `S` contains the support of the canonical
congruence subgroup lying in a closed finite-index subgroup `H`, then the
idele-class power-congruence subgroup `C_K(n, S, ∅)` is contained in `H`.

The proof assembles the finitely many prescribed local `n`-th roots into
one idele.  Dividing by its `n`-th power leaves an idele in the canonical
ray congruence subgroup. -/
theorem ideleClassPowerLocalUnitSubgroup_le_closedFiniteIndexSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      (RayClass.modulusInsideClosedFiniteIndex H hclosed).finitePart.support ⊆ S) :
    ideleClassPowerLocalUnitSubgroup
        (K := K)
        ⟨H.index,
          Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩
        S ∅ ≤
      H := by
  let n : ℕ+ :=
    ⟨H.index,
      Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩
  let m : RayClass.Modulus K :=
    RayClass.modulusInsideClosedFiniteIndex H hclosed
  let q : IdeleGroup K →* IdeleClassGroup K :=
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
  rintro _ ⟨a, ha, rfl⟩
  have ha' :=
    (mem_idelePowerLocalUnitSubgroup_iff
      (K := K) n S ∅ a).1 ha
  choose bInf hbInf using ha'.1
  choose bS hbS using
    fun v : ↥S => ha'.2.1 v.1 v.2
  let b : IdeleGroup K :=
    (ContinuousMulEquiv.piUnits.symm bInf,
      IdeleGroup.finiteIdeleOfFinset S bS)
  let u : IdeleGroup K :=
    a * (b ^ (n : ℕ))⁻¹
  have hbInfComponent (w : InfinitePlace K) :
      IdeleGroup.infiniteComponent w b = bInf w := by
    change
      ContinuousMulEquiv.piUnits
          (ContinuousMulEquiv.piUnits.symm bInf) w =
        bInf w
    exact congrFun
      (ContinuousMulEquiv.piUnits.apply_symm_apply bInf) w
  have hbInfPow (w : InfinitePlace K) :
      (bInf w) ^ (n : ℕ) =
        IdeleGroup.infiniteComponent w a := by
    exact hbInf w
  have hbFiniteComponent
      (v : ↥S) :
      IdeleGroup.finiteComponent v.1 b = bS v := by
    exact IdeleGroup.finiteIdeleOfFinset_apply_mem S bS v
  have hbFinitePow
      (v : ↥S) :
      (bS v) ^ (n : ℕ) =
        IdeleGroup.finiteComponent v.1 a := by
    exact hbS v
  have huInfinite :
      u.1 ∈ m.infiniteCongruenceSubgroup := by
    rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff_local]
    intro w
    have huComponent :
        IdeleGroup.infiniteComponent w u = 1 := by
      calc
        IdeleGroup.infiniteComponent w u =
            IdeleGroup.infiniteComponent w a *
              (IdeleGroup.infiniteComponent w b ^
                (n : ℕ))⁻¹ := by
          simp only [u, map_mul, map_inv, map_pow]
        _ = 1 := by
           rw [hbInfComponent, hbInfPow]
           simp
    change IdeleGroup.infiniteComponent w u ∈
      m.localInfiniteCongruenceSubgroup w
    rw [huComponent]
    exact Subgroup.one_mem _
  have huFinite :
      u.2 ∈ RayClass.finiteCongruenceSubgroup m.finitePart := by
    rw [RayClass.mem_finiteCongruenceSubgroup_iff]
    intro v
    by_cases hv : v ∈ S
    · let vS : ↥S := ⟨v, hv⟩
      have huComponent :
          IdeleGroup.finiteComponent v u = 1 := by
        calc
          IdeleGroup.finiteComponent v u =
              IdeleGroup.finiteComponent v a *
                (IdeleGroup.finiteComponent v b ^
                  (n : ℕ))⁻¹ := by
            simp only [u, map_mul, map_inv, map_pow]
          _ = 1 := by
            change
              IdeleGroup.finiteComponent vS.1 a *
                (IdeleGroup.finiteComponent vS.1 b ^
                  (n : ℕ))⁻¹ = 1
            rw [hbFiniteComponent vS, hbFinitePow vS]
            simp
      change IdeleGroup.finiteComponent v u ∈
        RayClass.localHigherUnitGroup v (m.finitePart v)
      rw [huComponent]
      exact Subgroup.one_mem _
    · have hmv : m.finitePart v = 0 := by
        by_contra hmv
        exact hv (hS (Finsupp.mem_support_iff.mpr hmv))
      have hbComponent :
          IdeleGroup.finiteComponent v b = 1 := by
        exact
          IdeleGroup.finiteIdeleOfFinset_apply_notMem
            S bS v hv
      have huComponent :
          IdeleGroup.finiteComponent v u =
            IdeleGroup.finiteComponent v a := by
        simp only [u, map_mul, map_inv, map_pow,
          hbComponent, one_pow, inv_one, mul_one]
      change IdeleGroup.finiteComponent v u ∈
        RayClass.localHigherUnitGroup v (m.finitePart v)
      rw [hmv, RayClass.localHigherUnitGroup_zero,
        huComponent]
      exact ha'.2.2 v (by simpa only [Finset.union_empty] using hv)
  have huCongruence :
      u ∈ RayClass.Modulus.ideleCongruenceSubgroup m :=
    ⟨huInfinite, huFinite⟩
  have hquCongruence :
      q u ∈ RayClass.Modulus.congruenceSubgroup m := by
    exact
      ⟨u, Subgroup.mem_sup_left huCongruence, rfl⟩
  have hquH : q u ∈ H := by
    apply
      RayClass.modulusInsideClosedFiniteIndex_spec
        H hclosed
    simpa only [m] using hquCongruence
  have hbPowH : q (b ^ (n : ℕ)) ∈ H := by
    change q (b ^ H.index) ∈ H
    rw [map_pow]
    let : IsMulCommutative (IdeleClassGroup K) :=
      ⟨⟨fun x y => mul_comm x y⟩⟩
    let : H.Normal := H.normal_of_isMulCommutative
    exact H.pow_index_mem (q b)
  have haDecomposition :
      a = b ^ (n : ℕ) * u := by
    dsimp only [u]
    calc
      a = a *
          ((b ^ (n : ℕ)) * (b ^ (n : ℕ))⁻¹) := by
        simp
      _ = b ^ (n : ℕ) *
          (a * (b ^ (n : ℕ))⁻¹) := by
        ac_rfl
  rw [haDecomposition, map_mul]
  exact H.mul_mem hbPowH hquH

end GlobalClassFields
end GlobalClassFieldTheory
