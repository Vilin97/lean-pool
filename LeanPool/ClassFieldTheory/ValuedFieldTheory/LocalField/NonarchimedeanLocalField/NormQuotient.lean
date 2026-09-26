/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NormUnits
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Norm.Basic
/-!
# Quotients by local norm subgroups

Constructs `Kˣ/N(Lˣ)`, its universal maps and comparison equivalences, and
relates its finite cardinality to the index of the norm subgroup.
-/

@[expose] public section

namespace LocalFieldTheory

noncomputable
section

universe u v

/-- The norm subgroup N_{L/K}(Lˣ) ≤ Kˣ. -/
def localNormSubgroup (K L : Type u) [Field K] [Field L] [Algebra K L] : Subgroup Kˣ :=
  (normUnits K L).range

/-- Units modulo field norms. -/
def NormQuotient (K L : Type u) [Field K] [Field L] [Algebra K L] : Type u :=
  Kˣ ⧸ localNormSubgroup K L

/-- Field units modulo the local norm subgroup form a commutative group. -/
instance normQuotientCommGroup (K L : Type u) [Field K] [Field L] [Algebra K L] :
    CommGroup (NormQuotient K L) := by
  change CommGroup (Kˣ ⧸ localNormSubgroup K L)
  infer_instance

/-- The explicit boundary to the concrete quotient implementation.  Clients
that need quotient-level constructions should use this equivalence instead of
unfolding `NormQuotient`. -/
def normQuotientConcreteEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    NormQuotient K L ≃* Kˣ ⧸ localNormSubgroup K L := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* Kˣ ⧸ localNormSubgroup K L
  exact MulEquiv.refl _

/-- Defines `normClass`. -/
def normClass (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Kˣ →* NormQuotient K L := by
  change Kˣ →* Kˣ ⧸ localNormSubgroup K L
  let N := localNormSubgroup K L
  exact QuotientGroup.mk' N

/-- The concrete quotient equivalence sends a norm class to the quotient class of its
representative. -/
@[simp]
theorem normQuotientConcreteEquiv_normClass
    (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ) :
    normQuotientConcreteEquiv K L (normClass K L x) =
      QuotientGroup.mk x := by
  rfl

/-- Define a homomorphism out of a norm quotient from a homomorphism on
`Kˣ` that kills every local norm. -/
def normQuotientLift {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (h : localNormSubgroup K L ≤ f.ker) :
    NormQuotient K L →* M := by
  change (Kˣ ⧸ localNormSubgroup K L) →* M
  let N := localNormSubgroup K L
  exact QuotientGroup.lift N f h

/-- A homomorphism descended through the norm quotient agrees with the original homomorphism on
representatives. -/
@[simp]
theorem normQuotientLift_normClass {K L : Type u} {M : Type v} [Field K] [Field L]
    [Algebra K L] [Group M] (f : Kˣ →* M)
    (h : localNormSubgroup K L ≤ f.ker) (x : Kˣ) :
    normQuotientLift f h (normClass K L x) = f x := by
  rfl

/-- A map obtained by descending a surjective homomorphism through the norm
quotient is still surjective. -/
theorem normQuotientLift_surjective {K L : Type u} {M : Type v} [Field K] [Field L]
    [Algebra K L] [Group M] (f : Kˣ →* M)
    (h : localNormSubgroup K L ≤ f.ker) (hf : Function.Surjective f) :
    Function.Surjective (normQuotientLift f h) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨normClass K L x, normQuotientLift_normClass f h x⟩

/-- Identify a norm quotient with any concrete quotient once its defining
subgroup has been identified.  This is the sole public boundary for such
representation changes. -/
def normQuotientEquivOfSubgroupEq
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (N : Subgroup Kˣ) (h : localNormSubgroup K L = N) :
    NormQuotient K L ≃* Kˣ ⧸ N := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* (Kˣ ⧸ N)
  exact QuotientGroup.quotientMulEquivOfEq h

/-- After identifying the norm subgroup with another subgroup, a norm class maps to the
corresponding quotient class. -/
@[simp]
theorem normQuotientEquivOfSubgroupEq_normClass
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (N : Subgroup Kˣ) (h : localNormSubgroup K L = N) (x : Kˣ) :
    normQuotientEquivOfSubgroupEq K L N h (normClass K L x) =
      QuotientGroup.mk x := by
  change QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact QuotientGroup.quotientMulEquivOfEq_mk h x

/-- Identify two norm quotients when their defining norm subgroups agree. -/
def normQuotientEquivOfNormSubgroupEq
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L = localNormSubgroup K M) :
    NormQuotient K L ≃* NormQuotient K M := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* (Kˣ ⧸ localNormSubgroup K M)
  exact QuotientGroup.quotientMulEquivOfEq h

/-- An equality of norm subgroups identifies norm classes represented by the same base-field unit.
An equality of norm subgroups identifies norm classes represented by the same base-field unit. -/
@[simp]
theorem normQuotientEquivOfNormSubgroupEq_normClass
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L = localNormSubgroup K M) (x : Kˣ) :
    normQuotientEquivOfNormSubgroupEq K L M h (normClass K L x) =
      normClass K M x := by
  change QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact QuotientGroup.quotientMulEquivOfEq_mk h x

/-- First isomorphism theorem with an opaque norm quotient as its source. -/
def normQuotientEquivOfSurjective
    {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
    (hker : f.ker = localNormSubgroup K L) : NormQuotient K L ≃* M := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* M
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The first-isomorphism equivalence sends a norm class to the image of its representative. -/
@[simp]
theorem normQuotientEquivOfSurjective_normClass
    {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
    (hker : f.ker = localNormSubgroup K L) (x : Kˣ) :
    normQuotientEquivOfSurjective f hf hker (normClass K L x) = f x := by
  change
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf))
        (QuotientGroup.mk x) = f x
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- Eliminate a norm-quotient class through the canonical quotient map,
without exposing the quotient representation to clients. -/
protected theorem NormQuotient.inductionOn {K L : Type u} [Field K] [Field L]
    [Algebra K L] {motive : NormQuotient K L → Prop}
    (q : NormQuotient K L)
    (h : ∀ x : Kˣ, motive (normClass K L x)) : motive q := by
  change motive (show Kˣ ⧸ localNormSubgroup K L from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

/-- The quotient class of any extension-unit norm is the identity norm class. -/
theorem mk_normUnits_eq_one (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ) :
    normClass K L (normUnits K L x) = 1 := by
  exact (QuotientGroup.eq_one_iff (normUnits K L x)).2 ⟨x, rfl⟩

/-- A base-field unit has trivial norm class exactly when it lies in the local norm subgroup. -/
theorem normClass_eq_one_iff (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x : Kˣ) :
    normClass K L x = 1 ↔ ∃ y : Lˣ, normUnits K L y = x := by
  rw [← MonoidHom.mem_range]
  exact QuotientGroup.eq_one_iff x

/-- Two units have the same norm class exactly when their quotient is a local norm. -/
theorem normClass_eq_iff_div_mem (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      x / y ∈ localNormSubgroup K L :=
  by
    let N := localNormSubgroup K L
    exact QuotientGroup.eq_iff_div_mem (N := N)

/-- The kernel of the norm-class homomorphism is the local norm subgroup. -/
theorem normClass_ker (K L : Type u) [Field K] [Field L] [Algebra K L] :
    MonoidHom.ker (normClass K L) = localNormSubgroup K L :=
  by
    let N := localNormSubgroup K L
    exact QuotientGroup.ker_mk' (N := N)

/-- Membership in the kernel of the norm-class map is equivalent to membership in the local norm
subgroup. -/
theorem normClass_mem_ker_iff (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x : Kˣ) :
    x ∈ MonoidHom.ker (normClass K L) ↔ x ∈ localNormSubgroup K L := by
  rw [normClass_ker K L]

/-- A norm class is one exactly when its representative is a local norm. -/
theorem normClass_eq_one_iff_mem (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x : Kˣ) :
    normClass K L x = 1 ↔ x ∈ localNormSubgroup K L := by
  rw [← normClass_mem_ker_iff K L x]
  rfl

/-- The map of norm quotients induced by inclusion of their norm subgroups. -/
def normQuotientMapOfLE
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L ≤ localNormSubgroup K M) :
    NormQuotient K L →* NormQuotient K M :=
  normQuotientLift (normClass K M) fun x hx =>
    (normClass_eq_one_iff_mem K M x).2 (h hx)

/-- The quotient map induced by inclusion of norm subgroups preserves representatives. -/
@[simp]
theorem normQuotientMapOfLE_normClass
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L ≤ localNormSubgroup K M) (x : Kˣ) :
    normQuotientMapOfLE K L M h (normClass K L x) = normClass K M x := by
  exact normQuotientLift_normClass (normClass K M) _ x

/-- Over the identity extension, the unit norm fixes every base-field unit. -/
theorem normUnits_self_apply (K : Type u) [Field K] (x : Kˣ) :
    normUnits K K x = x := by
  ext
  simp [normUnits]

/-- For the identity extension, every base-field unit is a norm. -/
theorem localNormSubgroup_self (K : Type u) [Field K] :
    localNormSubgroup K K = ⊤ := by
  ext x
  constructor
  · intro _
    exact Subgroup.mem_top x
  · intro _
    exact ⟨x, normUnits_self_apply K x⟩

/-- Every norm class for the identity extension is the identity. -/
theorem normQuotient_self_eq_one (K : Type u) [Field K] (x : NormQuotient K K) :
    x = 1 := by
  refine NormQuotient.inductionOn (motive := fun q => q = 1) x ?_
  intro a
  exact (normClass_eq_one_iff_mem K K a).2 (by
    rw [localNormSubgroup_self K]
    exact Subgroup.mem_top a)

/-- The norm quotient of a field over itself is a subsingleton. -/
instance normQuotient_self_subsingleton (K : Type u) [Field K] :
    Subsingleton (NormQuotient K K) where
  allEq x y := by
    rw [normQuotient_self_eq_one K x, normQuotient_self_eq_one K y]

/-- A representative from the local norm subgroup has trivial norm class. -/
theorem normClass_eq_one_of_mem (K L : Type u) [Field K] [Field L]
    [Algebra K L] {x : Kˣ} (hx : x ∈ localNormSubgroup K L) :
    normClass K L x = 1 :=
  (normClass_eq_one_iff_mem K L x).2 hx

/-- An integral power of a unit norm has trivial norm class. -/
theorem normClass_normUnits_zpow_eq_one
    (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ) (n : Int) :
    normClass K L ((normUnits K L x) ^ n) = 1 := by
  rw [map_zpow, mk_normUnits_eq_one, one_zpow]

/-- Two norm classes agree exactly when their representatives differ by a unit norm. -/
theorem normClass_eq_iff_exists_norm_div (K L : Type u)
    [Field K] [Field L] [Algebra K L] (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      ∃ z : Lˣ, x / y = normUnits K L z := by
  rw [normClass_eq_iff_div_mem K L x y]
  change x / y ∈ (normUnits K L).range ↔ _
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩

/-- Multiplying a representative on the left by a unit norm leaves its norm class unchanged. -/
theorem normClass_normUnits_mul (K L : Type u)
    [Field K] [Field L] [Algebra K L] (z : Lˣ) (x : Kˣ) :
    normClass K L (normUnits K L z * x) = normClass K L x := by
  rw [map_mul, mk_normUnits_eq_one]
  exact one_mul (normClass K L x)

/-- Multiplying a representative on the right by a unit norm leaves its norm class unchanged. -/
theorem normClass_mul_normUnits (K L : Type u)
    [Field K] [Field L] [Algebra K L] (x : Kˣ) (z : Lˣ) :
    normClass K L (x * normUnits K L z) = normClass K L x := by
  rw [map_mul, mk_normUnits_eq_one]
  exact mul_one (normClass K L x)

/-- Left multiplication by an integral power of a unit norm leaves a norm class unchanged. -/
theorem normClass_normUnits_zpow_mul (K L : Type u)
    [Field K] [Field L] [Algebra K L] (z : Lˣ) (n : Int) (x : Kˣ) :
    normClass K L ((normUnits K L z) ^ n * x) =
      normClass K L x := by
  rw [map_mul, normClass_normUnits_zpow_eq_one K L z n]
  exact one_mul (normClass K L x)

/-- Right multiplication by an integral power of a unit norm leaves a norm class unchanged. -/
theorem normClass_mul_normUnits_zpow (K L : Type u)
    [Field K] [Field L] [Algebra K L] (x : Kˣ) (z : Lˣ) (n : Int) :
    normClass K L (x * (normUnits K L z) ^ n) =
      normClass K L x := by
  rw [map_mul, normClass_normUnits_zpow_eq_one K L z n]
  exact mul_one (normClass K L x)

/-! ### Surjectivity and equality refinements for norm quotients -/

/-- A representative obtained by multiplying another by a unit norm defines the same norm class. -/
theorem normClass_eq_of_eq_normUnits_mul (K L : Type u)
    [Field K] [Field L] [Algebra K L] {x y : Kˣ} (z : Lˣ)
    (h : x = normUnits K L z * y) :
    normClass K L x = normClass K L y := by
  rw [h, normClass_normUnits_mul]

/-- Two norm classes agree exactly when one representative times the other's inverse is a local
norm. -/
theorem normClass_eq_iff_mul_inv_mem (K L : Type u)
    [Field K] [Field L] [Algebra K L] (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      x * y⁻¹ ∈ localNormSubgroup K L := by
  simpa [div_eq_mul_inv] using normClass_eq_iff_div_mem K L x y

/-- Two norm classes agree exactly when a unit norm converts the second representative to the first
on the left. -/
theorem normClass_eq_iff_exists_norm_mul_left (K L : Type u)
    [Field K] [Field L] [Algebra K L] (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      ∃ z : Lˣ, x = normUnits K L z * y := by
  constructor
  · intro hxy
    rcases (normClass_eq_iff_exists_norm_div K L x y).1 hxy with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [← hz]
    exact (div_mul_cancel x y).symm
  · rintro ⟨z, hz⟩
    exact normClass_eq_of_eq_normUnits_mul K L z hz

/-- Two norm classes agree exactly when a unit norm converts the second representative to the first
on the right. -/
theorem normClass_eq_iff_exists_norm_mul_right (K L : Type u)
    [Field K] [Field L] [Algebra K L] (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      ∃ z : Lˣ, x = y * normUnits K L z := by
  constructor
  · intro hxy
    rcases (normClass_eq_iff_exists_norm_mul_left K L x y).1 hxy with ⟨z, hz⟩
    exact ⟨z, by simpa [mul_comm] using hz⟩
  · rintro ⟨z, hz⟩
    rw [hz]
    exact normClass_mul_normUnits K L y z

/-- If the unit norm is surjective, all base-field units have the same norm class. -/
theorem normClass_eq_all_of_normUnits_surjective (K L : Type u)
    [Field K] [Field L] [Algebra K L]
    (h : Function.Surjective (normUnits K L)) (x y : Kˣ) :
    normClass K L x = normClass K L y := by
  apply (normClass_eq_iff_div_mem K L x y).2
  exact MonoidHom.mem_range.mpr (h (x / y))

/-- If every base-field unit is a local norm, all norm classes coincide. -/
theorem normClass_eq_of_localNormSubgroup_eq_top (K L : Type u)
    [Field K] [Field L] [Algebra K L] (h : localNormSubgroup K L = ⊤) (x y : Kˣ) :
    normClass K L x = normClass K L y :=
  (normClass_eq_iff_div_mem K L x y).2 (by
    rw [h]
    exact Subgroup.mem_top (x / y))

end
end LocalFieldTheory
