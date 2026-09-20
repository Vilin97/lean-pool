/-
Copyright (c) 2026 Arnaud Mayeux, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arnaud Mayeux, Jujian Zhang
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.DirectSum.Basic

/-!
# Dilatations of commutative rings and semirings

From Arnaud Mayeux, *Dilatations of categories, via their Lean formalization*,
https://arxiv.org/abs/2608.09305, and `rndmx/DilCat` at commit
`604559654c948566675da3f7709b8ad3126bd487` (Apache-2.0).
The ring construction includes work by Arnaud Mayeux and Jujian Zhang from
`ProjConstruction/Proj` (Apache-2.0).
-/

@[expose] public section

noncomputable section

open Finset

namespace CategoryTheory.Dilatations

/-! ### §5.0.2 : Dilatations of commutative rings and semirings

The ring-theoretic dilatation `A[{Mᵢ/aᵢ}]` from [M], matching `Multicenter A` below to the
paper's `{[Mᵢ, aᵢ]}ᵢ∈I` (ported from `ProjConstruction/Proj`). -/
section RingDilatation

/-! #### Vendored from `Project/Dilatation/lemma.lean` -/
variable {ι A' B' F' : Type*} [CommSemiring A'] [CommSemiring B'] [FunLike F' A' B']
  [RingHomClass F' A' B']

namespace Ideal

lemma prod_span' (f : ι → A') (s : Finset ι) :
    Ideal.span {∏ i ∈ s, f i} = ∏ i ∈ s, Ideal.span {f i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, ← Ideal.span_singleton_mul_span_singleton, ih,
      Finset.prod_insert hi]

lemma prod_map (f : ι → Ideal A') (s : Finset ι) (χ : F') :
    Ideal.map χ (∏ i ∈ s, f i) = ∏ i ∈ s, Ideal.map χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Ideal.map_mul, Finset.prod_insert hi, ih]

end Ideal

/-! #### Vendored from `Project/Dilatation/Family.lean` -/
section

variable {A' G : Type*} [CommMonoid A'] [Zero G] [Pow A' G]
variable {ι : Type*}
/-- The finite product of a family raised to finitely supported exponents. -/
def familyPow (f : ι → A') (v : ι →₀ G) : A' := v.prod fun i k ↦ f i ^ k

/-- Scoped exponent notation for finite products of a family. -/
@[instance_reducible]
def instFamilyPow : HPow (ι → A') (ι →₀ G) A' where
  hPow f v := familyPow f v

scoped[CategoryTheory.Dilatations.Family] attribute [instance]
  CategoryTheory.Dilatations.instFamilyPow

open Family

lemma familyPow_def (f : ι → A') (v : ι →₀ G) : f ^ v = v.prod fun i k ↦ f i ^ k := rfl

lemma familyPow_add (f : ι → A') (v w : ι →₀ ℕ) : f ^ (v + w) = f ^ v * f ^ w := by
  classical
  simp only [familyPow_def]
  rw [Finsupp.prod_add_index (by simp) (by simp [pow_add])]

@[simp]
lemma familyPow_zero (f : ι → A') : f ^ (0 : ι →₀ ℕ) = (1 : A') := by
  simp only [familyPow_def]
  rw [Finsupp.prod_zero_index]

/-- A family-power raised to an ordinary `ℕ`-power is the family-power at the scaled exponent :
`(f ^ ν) ^ k = f ^ (k•ν)`. Used to relate a "power of a power" to a single flattened exponent. -/
lemma familyPow_nsmul (f : ι → A') (ν : ι →₀ ℕ) (k : ℕ) : (f ^ ν) ^ k = f ^ (k • ν) := by
  induction k with
  | zero => simp
  | succ n ih => rw [succ_nsmul, familyPow_add, pow_succ, ih]

/-- Flattening a finite `ℕ`-combination `μ` of exponent profiles and taking a single family-power
agrees with taking the family-power at each profile first and combining : `μ.prod (fun ν k ↦
(f ^ ν) ^ k) = f ^ (μ.sum fun ν k ↦ k•ν)`. This is the key identity behind reindexing a
    multi-center by
exponent profiles (`Multicenter.reindex_LargeIdeal_pow`, `Multicenter.reindex_elem_pow` below). -/
lemma family_pow_flatten (f : ι → A') (μ : (ι →₀ ℕ) →₀ ℕ) :
    μ.prod (fun ν k => (f ^ ν) ^ k) = f ^ (μ.sum fun ν k => k • ν) := by
  induction μ using Finsupp.induction with
  | zero => simp
  | single_add ν0 k0 μ' hν0 hk0 ih =>
    rw [Finsupp.prod_add_index' (by simp) (fun ν k k' => by rw [pow_add]),
        Finsupp.sum_add_index' (by simp) (fun ν k k' => by rw [add_smul]),
        Finsupp.prod_single_index (by simp), Finsupp.sum_single_index (by simp),
        familyPow_add, ih, familyPow_nsmul]

end

namespace Ideal

variable {A' : Type*} [CommSemiring A']
variable {ι : Type*} (M : ι → Ideal A') (a : ι → A')

open Family

lemma familyPow_def (v : ι →₀ ℕ) : M ^ v = v.prod fun i k ↦ M i ^ k := rfl

variable {M} in
lemma mem_familyPow_add {v w : ι →₀ ℕ} {x y : A'} (hx : x ∈ M ^ v) (hy : y ∈ M ^ w) :
  x * y ∈ M ^ (v+w) := by
  classical
  rw [familyPow_add]
  exact Ideal.mul_mem_mul hx hy

variable {M a} in
lemma mem_familyPow_of_mem {v : ι →₀ ℕ} (mem : ∀ i ∈ v.support, a i ∈ M i) : a ^ v ∈ M ^ v :=
  Ideal.prod_mem_prod fun _ hi ↦ Ideal.pow_mem_pow (mem _ hi) _

end Ideal

/-! #### Vendored from `Project/Dilatation/Multicenter.lean` (live, non-commented-out part only) -/
open DirectSum Family

section defs

variable (A' : Type*) [CommSemiring A']

/-- A family of ideals and corresponding denominator elements in a commutative semiring. -/
structure Multicenter where
  /-- The index type of the ideal-denominator pairs. -/
  (index : Type*)
  /-- The ideal of permitted numerators at each index. -/
  (ideal : index → Ideal A')
  /-- The denominator element at each index. -/
  (elem : index → A')
end defs

namespace Multicenter

section semiring

variable {A' : Type*} [CommSemiring A'] (M : Multicenter A')

/-- Finitely supported natural-number exponent profiles on a multicenter. -/
scoped notation : max M"^ℕ"  => Multicenter.index M  →₀ ℕ

/-- Enlarge the numerator ideal by the principal ideal of its denominator. -/
def LargeIdeal (i : M.index) : Ideal A' := M.ideal i + Ideal.span {M.elem i}

lemma elem_mem_LargeIdeal (i : M.index) : M.elem i ∈ M.LargeIdeal i := by
  suffices inequality : Ideal.span {M.elem i} ≤ M.LargeIdeal i by
   apply inequality
   exact Ideal.mem_span_singleton_self (M.elem i)
  simp only [LargeIdeal, Submodule.add_eq_sup, le_sup_right]

/-- The product of enlarged numerator ideals at an exponent profile. -/
abbrev prodLargeIdealPower (v : M^ℕ) : Ideal A' :=
  v.prod fun i k ↦ M.LargeIdeal i ^ k

lemma elem_pow_mem_LargeIdealPow (ν : M^ℕ) : M.elem ^ ν ∈ M.LargeIdeal ^ ν :=
  Ideal.mem_familyPow_of_mem fun i _ => elem_mem_LargeIdeal M i

/-- The `ν`-indexed reindexing of `M`: index type `M^ℕ` (exponent profiles), ideal `L ^ ν` at `ν`,
element `a ^ ν` at `ν`. Dilating by this center gives back the same ring as dilating by `M`
directly (`reindexRingEquiv` below, inside `Dilatation`). -/
@[reducible] def reindex : Multicenter A' where
  index := M^ℕ
  ideal := M.prodLargeIdealPower
  elem := fun ν => M.elem ^ ν

/-- `reindex`'s large ideal at `ν` is just `L ^ ν` itself : the `+span{a ^ ν}` correction is already
absorbed, since `a ^ ν ∈ L ^ ν` (`elem_pow_mem_LargeIdealPow`). -/
lemma reindex_LargeIdeal (ν : M^ℕ) : (M.reindex).LargeIdeal ν = M.LargeIdeal ^ ν := by
  change M.prodLargeIdealPower ν + Ideal.span {M.elem ^ ν} = M.prodLargeIdealPower ν
  rw [Submodule.add_eq_sup, sup_eq_left, Ideal.span_le, Set.singleton_subset_iff]
  exact elem_pow_mem_LargeIdealPow M ν

/-- Flatten a finite `ℕ`-combination of exponent profiles into a single exponent profile :
`μ ↦ Σ_ν μ(ν)•ν`. This is the comparison map between `reindex`'s own exponent profiles
(`(M^ℕ) →₀ ℕ`) and `M`'s (`M^ℕ`). -/
noncomputable def flatten (μ : (M^ℕ) →₀ ℕ) : M^ℕ := μ.sum (fun ν k => k • ν)

lemma flatten_add (μ μ' : (M^ℕ) →₀ ℕ) : M.flatten (μ + μ') = M.flatten μ + M.flatten μ' := by
  unfold flatten
  refine Finsupp.sum_add_index' (fun ν => ?_) (fun ν k k' => ?_)
  · simp
  · rw [add_smul]

lemma flatten_zero : M.flatten 0 = 0 := by
  unfold flatten
  exact Finsupp.sum_zero_index

lemma flatten_single (ν0 : M^ℕ) : M.flatten (Finsupp.single ν0 1) = ν0 := by
  unfold flatten
  rw [Finsupp.sum_single_index (by simp), one_smul]

lemma flatten_surjective : Function.Surjective (M.flatten) :=
  fun ν0 => ⟨Finsupp.single ν0 1, flatten_single M ν0⟩

lemma reindex_LargeIdeal_pow (μ : (M^ℕ) →₀ ℕ) :
    (M.reindex).LargeIdeal ^ μ = M.LargeIdeal ^ (M.flatten μ) := by
  change μ.prod (fun ν k => ((M.reindex).LargeIdeal ν) ^ k) = _
  simp_rw [reindex_LargeIdeal]
  exact family_pow_flatten M.LargeIdeal μ

lemma reindex_elem_pow (μ : (M^ℕ) →₀ ℕ) :
    (M.reindex).elem ^ μ = M.elem ^ (M.flatten μ) :=
  family_pow_flatten M.elem μ

/-- A fraction representative with numerator in the corresponding product ideal. -/
structure PreDil where
  /-- The finitely supported exponent profile of the denominator. -/
  pow : M^ℕ
  /-- The numerator of the representative. -/
  num : A'
  num_mem : num ∈ M.LargeIdeal ^pow

/-- Equality after cross-multiplication and multiplication by another denominator. -/
def r : M.PreDil → M.PreDil → Prop := fun x y =>
  ∃ β : M^ℕ, x.num * M.elem ^ (β + y.pow) = y.num * M.elem ^ (β + x.pow)

variable {M}

lemma r_refl (x : M.PreDil) : M.r x x := by simp [r]

lemma r_symm (x y : M.PreDil) : M.r x y → M.r y x := by
  intro h
  rcases h with ⟨β, hβ⟩
  use β
  rw [hβ.symm]

lemma r_trans (x y z : M.PreDil) : M.r x y → M.r y z → M.r x z := by
  intro h g
  rcases h with ⟨β, hβ⟩
  rcases g with ⟨γ, gγ⟩
  use β+γ+y.pow
  rw [show β + γ + y.pow + z.pow = (β + y.pow) + (γ + z.pow) by abel,
    familyPow_add, ← mul_assoc, hβ, mul_assoc, mul_comm (M.elem ^ (_ : M^ℕ)), ← mul_assoc, gγ,
    mul_assoc, ← familyPow_add]
  congr 2
  abel

/-- The equivalence relation on fraction representatives. -/
def setoid : Setoid (M.PreDil) where
  r := M.r
  iseqv :=
  { refl := r_refl
    symm {x y} := r_symm x y
    trans {x y z} := r_trans x y z }

variable (M) in
/-- The quotient of permitted fraction representatives by cross-multiplication. -/
def Dilatation := _root_.Quotient M.setoid

/-- The dilatation of a commutative semiring at a multicenter. -/
scoped notation : max ring"["multicenter"]" => Dilatation (A' := ring) multicenter
namespace Dilatation

/-- Map a fraction representative to its class in the dilatation. -/
def mk (x : M.PreDil) : A'[M] := _root_.Quotient.mk _ x

lemma mk_eq_mk (x y : M.PreDil) : mk x = mk y ↔ M.r x y := by
  erw [_root_.Quotient.eq]
  rfl

@[elab_as_elim]
lemma induction_on {P : A'[M] → Prop} (x : A'[M]) (h : ∀ x : M.PreDil, P (mk x)) : P x := by
  induction x using _root_.Quotient.inductionOn with | h a =>
  exact h a

/-- Descend a relation-respecting function on representatives to the quotient. -/
def descFun {B' : Type*} (f : M.PreDil → B') (hf : ∀ x y, M.r x y → f x = f y) : A'[M] → B' :=
  _root_.Quotient.lift f hf

/-- Descend a binary function that respects equality of representatives. -/
def descFun₂ {B' : Type*} (f : M.PreDil → M.PreDil → B')
    (hf : ∀ a b x y, M.r a b → M.r x y → f a x = f b y) :
    A'[M] → A'[M] → B' :=
  _root_.Quotient.lift₂ f <| fun a x b y ↦ hf a b x y

@[simp]
lemma descFun_mk {B' : Type*} (f : M.PreDil → B') (hf : ∀ x y, M.r x y → f x = f y)
    (x : M.PreDil) :
    descFun f hf (mk x) = f x := rfl

@[simp]
lemma descFun₂_mk_mk {B' : Type*} (f : M.PreDil → M.PreDil → B')
    (hf : ∀ a b x y, M.r a b → M.r x y → f a x = f b y) (x y : M.PreDil) :
    descFun₂ f hf (mk x) (mk y) = f x y := rfl

/-- Addition of representatives using a common denominator. -/
@[simps]
def add' (x y : M.PreDil) : M.PreDil where
 pow := x.pow + y.pow
 num := M.elem ^ y.pow * x.num + M.elem ^ x.pow * y.num
 num_mem := Ideal.add_mem _
  (by
    rw [add_comm, familyPow_add]
    exact Ideal.mul_mem_mul (Ideal.mem_familyPow_of_mem fun i _ ↦ elem_mem_LargeIdeal M i)
      x.num_mem)
  (by
    rw [familyPow_add]
    exact Ideal.mul_mem_mul (Ideal.mem_familyPow_of_mem fun i _ ↦ elem_mem_LargeIdeal M i)
      y.num_mem)

lemma add'_respects {x x' y y' : M.PreDil} (hx : M.r x x') (hy : M.r y y') :
    M.r (add' x y) (add' x' y') := by
  obtain ⟨α, hα⟩ := hx
  obtain ⟨β, hβ⟩ := hy
  refine ⟨α + β, ?_⟩
  change (M.elem ^ y.pow * x.num + M.elem ^ x.pow * y.num) *
      M.elem ^ (α + β + (x'.pow + y'.pow)) =
    (M.elem ^ y'.pow * x'.num + M.elem ^ x'.pow * y'.num) *
      M.elem ^ (α + β + (x.pow + y.pow))
  calc
    _ = (x.num * M.elem ^ (α + x'.pow)) * M.elem ^ (β + y'.pow + y.pow) +
        (y.num * M.elem ^ (β + y'.pow)) * M.elem ^ (α + x'.pow + x.pow) := by
      simp only [familyPow_add]
      ring
    _ = (x'.num * M.elem ^ (α + x.pow)) * M.elem ^ (β + y'.pow + y.pow) +
        (y'.num * M.elem ^ (β + y.pow)) * M.elem ^ (α + x'.pow + x.pow) := by
      rw [hα, hβ]
    _ = _ := by
      simp only [familyPow_add]
      ring

instance : Add A'[M] where
  add := descFun₂ (fun x y => mk (add' x y)) fun _ _ _ _ hx hy =>
    (mk_eq_mk _ _).mpr (add'_respects hx hy)

lemma mk_add_mk (x y : M.PreDil) : mk x + mk y = mk (add' x y) := rfl

/-- Multiplication of representatives by multiplying their numerators. -/
@[simps]
def mul' (x y : M.PreDil) : M.PreDil where
  pow := x.pow + y.pow
  num := x.num * y.num
  num_mem := Ideal.mem_familyPow_add x.num_mem y.num_mem

lemma dist' (x y z : M.PreDil) : M.r (mul' x (add' y z))
                                (add' (mul' x y) (mul' x z))  := by
  use 0
  simp [familyPow_add]
  ring

instance : Mul A'[M] where
  mul := descFun₂ (fun x y ↦ mk <| mul' x y) <| by
    rintro a b x y ⟨α, hα⟩ ⟨β, hβ⟩
    rw [mk_eq_mk]
    use α + β
    simp only [mul'_num, mul'_pow]
    rw [show α + β + (b.pow + y.pow) = (α + b.pow) + (β + y.pow) by abel, familyPow_add,
      show a.num * x.num * (M.elem ^ (α + b.pow) * M.elem ^ (β + y.pow)) =
        (a.num * M.elem ^ (α + b.pow)) * (x.num * M.elem ^ (β + y.pow)) by ring, hα, hβ,
      show b.num * M.elem ^ (α + a.pow) * (y.num * M.elem ^ (β + x.pow)) =
        b.num * y.num * (M.elem ^ (α + a.pow) * M.elem ^ (β + x.pow)) by ring, ← familyPow_add]
    congr 2
    abel

lemma mk_mul_mk (x y : M.PreDil) : mk x * mk y = mk (mul' x y) := rfl

instance : Zero A'[M] where
  zero := mk {
    pow := 0
    num := 0
    num_mem := by exact Submodule.zero_mem (M.prodLargeIdealPower 0)
  }

lemma zero_def :  (0 :A'[M]) =  (mk {
    pow := 0
    num := 0
    num_mem := by simp only [Submodule.zero_mem]
  } :A'[M]):= rfl

instance : One A'[M] where
  one := mk {
    pow := 0
    num := 1
    num_mem := by exact Submodule.one_le.mp fun ⦃x⦄ a ↦ a
  }

lemma one_def :  (1 :A'[M]) =  (mk {
  pow := 0
  num := 1
  num_mem := by simp
} :A'[M]):= rfl

instance : AddCommMonoid A'[M] where
  add_assoc := by
   intro a b c
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
   induction c using induction_on with |h z =>
    simp only [mk_add_mk, mk_eq_mk]
    use 0
    simp only [add'_num, add'_pow, familyPow_add, zero_add]
    ring
  zero_add := by
   intro a
   induction a using induction_on with |h x=>
    simp only [zero_def, mk_add_mk, mk_eq_mk]
    use 0
    simp []
  add_zero := by
   intro a
   induction a using induction_on with |h x=>
    simp only [zero_def, mk_add_mk, mk_eq_mk]
    use 0
    simp []
  add_comm := by
   intro a b
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
    simp only [mk_add_mk, mk_eq_mk]
    use 0
    simp [familyPow_add]
    ring
  nsmul := nsmulRec

instance monoid : Monoid A'[M] where
  mul_assoc := by
   intro a b c
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
   induction c using induction_on with |h z =>
    simp only [mk_mul_mk, mk_eq_mk]
    use 0
    simp only [mul'_num, mul'_pow, zero_add, familyPow_add]
    ring
  one_mul := by
   intro a
   induction a using induction_on with |h x =>
    simp only [one_def, mk_mul_mk, mk_eq_mk]
    use 0
    simp []
  mul_one := by
   intro a
   induction a using induction_on with |h x =>
    simp only [one_def, mk_mul_mk, mk_eq_mk]
    use 0
    simp []

instance instCommSemiring : CommSemiring A'[M] where
  __ := monoid
  left_distrib := by
   rintro a b c
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
   induction c using induction_on with |h z =>
    simp only [mk_add_mk, mk_mul_mk, mk_eq_mk]
    use 0
    simp only [mul'_num, add'_num, add'_pow, mul'_pow, zero_add, familyPow_add]
    ring
  right_distrib := by
   rintro a b c
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
   induction c using induction_on with |h z =>
    simp only [mk_add_mk, mk_mul_mk, mk_eq_mk]
    use 0
    simp only [mul'_num, add'_num, add'_pow, mul'_pow, zero_add, familyPow_add]
    ring
  zero_mul := by
   rintro a
   induction a using induction_on with |h x =>
    simp only [zero_def, mk_mul_mk, mk_eq_mk]
    use 0
    simp []
  mul_zero := by
   rintro a
   induction a using induction_on with |h x =>
    simp only [zero_def, mk_mul_mk, mk_eq_mk]
    use 0
    simp []
  mul_comm := by
   intro a b
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
    simp only [mk_mul_mk, mk_eq_mk]
    use 0
    simp only [mul'_num, mul'_pow, zero_add, familyPow_add]
    ring

variable (M) in
/-- The canonical ring homomorphism sending a base element to denominator one. -/
@[simps]
def fromBaseRing : A' →+* A'[M] where
  toFun x := .mk
        { pow := 0
          num := x
          num_mem := by simp }
  map_one' := by simp [one_def]
  map_mul' _ _ := by simp only [mk_mul_mk, mk_eq_mk]; use 0; simp
  map_zero' := by simp [zero_def]
  map_add' _ _ := by simp only [mk_add_mk, mk_eq_mk]; use 0; simp

instance : Algebra A' A'[M] := RingHom.toAlgebra (fromBaseRing M)

lemma algebraMap_eq : (algebraMap A' A'[M]) = fromBaseRing M := rfl

lemma algebraMap_apply (x : A') : algebraMap A' A'[M] x = mk {
  pow := 0
  num := x
  num_mem := by simp
} := rfl

lemma smul_mk (x : A') (y : M.PreDil) : x • mk y = mk {
    pow := y.pow
    num := x * y.num
    num_mem := Ideal.mul_mem_left _ _ y.num_mem } := by
  simp only [Algebra.smul_def, algebraMap_apply, mk_mul_mk, mk_eq_mk]
  use 0
  simp

/-- The fraction of a permitted numerator by a denominator exponent profile. -/
abbrev frac (ν : M^ℕ) (m : M.LargeIdeal ^ ν) : A'[M]:=
  mk {
    pow := ν
    num := m
    num_mem := by simp
    }

/-- Fraction notation with an explicit multicenter. -/
scoped notation : max m"/.[" M"]"ν => frac (M := M) ν m

/-- Fraction notation with the multicenter inferred from the numerator type. -/
scoped notation : max m"/."ν => frac ν m

lemma frac_add_frac (v w : M^ℕ) (m : M.LargeIdeal ^ v) (n : M.LargeIdeal ^ w) :
    (m/.v) + (n/.w) =
    (⟨(m : A') * M.elem ^ w + (n : A') * M.elem ^ v, Ideal.add_mem _
      (Ideal.mem_familyPow_add m.2 (Ideal.mem_familyPow_of_mem fun i _ ↦ elem_mem_LargeIdeal M i))
      (add_comm v w ▸
        Ideal.mem_familyPow_add n.2 (Ideal.mem_familyPow_of_mem fun i _ ↦ elem_mem_LargeIdeal
          M i))⟩) /. (v + w) := by
  simp only [frac, mk_add_mk, mk_eq_mk]
  use 0
  simp only [add'_num, zero_add, familyPow_add, add'_pow]
  ring

lemma frac_mul_frac (v w : M^ℕ) (m : M.LargeIdeal ^ v) (n : M.LargeIdeal ^ w) :
    (m/.v) * (n/.w) =
    (⟨m * n, Ideal.mem_familyPow_add m.2 n.2⟩)/.(v + w) := by
  simp only [frac, mk_mul_mk, mk_eq_mk]
  use 0
  simp

lemma smul_frac (a : A') (v : M^ℕ) (m : M.LargeIdeal ^ v) : a • (m/.v) = (a • m)/.v := by
  simp only [frac, smul_mk, mk_eq_mk]
  use 0
  simp

lemma nonzerodiv_image (v : M^ℕ) :
   algebraMap A' A'[M] (M.elem ^ v) ∈ nonZeroDivisors A'[M] := by
    have key : ∀ x : A'[M], x * algebraMap A' A'[M] (M.elem ^ v) = 0 → x = 0 := by
      intro x h
      induction x using induction_on with |h x =>
      simp only [algebraMap_apply, mk_mul_mk, zero_def, mk_eq_mk] at h
      rcases h with ⟨ α, hα ⟩
      simp only [mul'_num, add_zero, mul'_pow, zero_mul] at hα
      simp only [zero_def, mk_eq_mk]
      use v + α
      simp [familyPow_add, ← mul_assoc, hα]
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

variable (M) in
/-- Each denominator becomes a non-zero-divisor in the dilatation. -/
lemma nonzerodiv_image_single (i : M.index) :
    algebraMap A' A'[M] (M.elem i) ∈ nonZeroDivisors A'[M] := by
  simpa [familyPow_def] using nonzerodiv_image (M := M) (Finsupp.single i 1)

lemma image_elem_LargeIdeal_equal (v : M^ℕ) :
 Ideal.span ({algebraMap A' A'[M] (M.elem ^ v)}) =
    Ideal.map (algebraMap A' A'[M]) (M.LargeIdeal ^ v):= by
    refine le_antisymm ?_  ?_
    · rw [Ideal.span_le]
      simp only [Set.singleton_subset_iff, SetLike.mem_coe]
      apply Ideal.mem_map_of_mem
      apply Ideal.mem_familyPow_of_mem
      intros
      exact elem_mem_LargeIdeal M _
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have eq : algebraMap A' A'[M] x =
       algebraMap A' A'[M] (M.elem ^ v) * ⟨ x, hx⟩  /.v := by
       simp only [algebraMap_apply, frac, mk_mul_mk, mk_eq_mk]
       use 0
       simp [mul_comm]
      simp only [Ideal.mem_comap]
      rw [eq]
      apply Ideal.mul_mem_right
      apply Ideal.subset_span
      simp only [Set.mem_singleton_iff]

/-! ##### Reindexing invariance : `A'[M.reindex] ≃+* A'[M]`

A purely ring-theoretic fact, independent of the comparison with categories : dilating by the
`ν`-indexed reindexing of `M` (`Multicenter.reindex`) gives back the same ring as dilating by `M`
directly. The forward map sends a `ν`-indexed generator `⟨μ,m,hm⟩` to `⟨flatten μ, m,_⟩`; the
backward map sends `⟨ν,m,hm⟩` to the singleton-profile generator `⟨single ν 1, m,_⟩`. -/
/-- The forward direction on representatives : `⟨μ,m,hm⟩ ↦ ⟨flatten μ, m, _⟩`. -/
noncomputable def toPreDil (x : (M.reindex).PreDil) : M.PreDil where
  pow := M.flatten x.pow
  num := x.num
  num_mem := reindex_LargeIdeal_pow M x.pow ▸ x.num_mem

lemma toPreDil_respects {x y : (M.reindex).PreDil} (h : (M.reindex).r x y) :
    M.r (toPreDil x) (toPreDil y) := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨M.flatten β, ?_⟩
  change x.num * M.elem ^ (M.flatten β + M.flatten y.pow) =
    y.num * M.elem ^ (M.flatten β + M.flatten x.pow)
  rw [← flatten_add, ← flatten_add, ← reindex_elem_pow, ← reindex_elem_pow]
  exact hβ

/-- Flatten exponent profiles to map the reindexed dilatation to the original. -/
noncomputable def toDilatation : A'[M.reindex] → A'[M] :=
  descFun (M := M.reindex) (fun x => mk (toPreDil x))
    (fun _ _ hxy => (mk_eq_mk _ _).mpr (toPreDil_respects hxy))

/-- The backward direction on representatives : `⟨ν,m,hm⟩ ↦ ⟨single ν 1, m, _⟩`. -/
noncomputable def toPreDil' (x : M.PreDil) : (M.reindex).PreDil where
  pow := Finsupp.single x.pow 1
  num := x.num
  num_mem := by
    rw [reindex_LargeIdeal_pow, flatten_single]
    exact x.num_mem

lemma toPreDil'_respects {x y : M.PreDil} (h : M.r x y) :
    (M.reindex).r (toPreDil' x) (toPreDil' y) := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨Finsupp.single β 1, ?_⟩
  change x.num * (M.reindex).elem ^ (Finsupp.single β 1 + Finsupp.single y.pow 1) =
    y.num * (M.reindex).elem ^ (Finsupp.single β 1 + Finsupp.single x.pow 1)
  rw [reindex_elem_pow, reindex_elem_pow]
  simp only [flatten_add, flatten_single]
  exact hβ

/-- Embed representatives using singleton profiles in the reindexed dilatation. -/
noncomputable def toDilatation' : A'[M] → A'[M.reindex] :=
  descFun (M := M) (fun x => mk (toPreDil' x))
    (fun _ _ hxy => (mk_eq_mk _ _).mpr (toPreDil'_respects hxy))

lemma toPreDil_toPreDil' (x : M.PreDil) : toPreDil (toPreDil' x) = x := by
  unfold toPreDil toPreDil'
  simp only [flatten_single]

lemma toPreDil'_toPreDil (y : (M.reindex).PreDil) :
    (M.reindex).r (toPreDil' (toPreDil y)) y := by
  refine ⟨0, ?_⟩
  change y.num * (M.reindex).elem ^ (0 + y.pow) =
    y.num * (M.reindex).elem ^ (0 + Finsupp.single (M.flatten y.pow) 1)
  rw [zero_add, zero_add, reindex_elem_pow, reindex_elem_pow, flatten_single]

lemma toDilatation_toDilatation' (x : A'[M]) :
    toDilatation (toDilatation' x) = x := by
  induction x using induction_on with
  | h x => change mk (toPreDil (toPreDil' x)) = mk x; rw [toPreDil_toPreDil']

lemma toDilatation'_toDilatation (y : A'[M.reindex]) :
    toDilatation' (toDilatation y) = y := by
  induction y using induction_on with
  | h y =>
    change mk (toPreDil' (toPreDil y)) = mk y
    exact (mk_eq_mk _ _).mpr (toPreDil'_toPreDil y)

lemma toPreDil_add' (x y : (M.reindex).PreDil) :
    toPreDil (add' x y) = add' (toPreDil x) (toPreDil y) := by
  refine PreDil.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · exact flatten_add M x.pow y.pow
  · change (M.reindex).elem ^ y.pow * x.num + (M.reindex).elem ^ x.pow * y.num =
      M.elem ^ (M.flatten y.pow) * x.num + M.elem ^ (M.flatten x.pow) * y.num
    rw [reindex_elem_pow, reindex_elem_pow]

lemma toPreDil_mul' (x y : (M.reindex).PreDil) :
    toPreDil (mul' x y) = mul' (toPreDil x) (toPreDil y) := by
  refine PreDil.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · exact flatten_add M x.pow y.pow
  · rfl

lemma toDilatation_zero : toDilatation (0 : A'[M.reindex]) = 0 := by
  change mk (toPreDil _) = _
  congr 1

lemma toDilatation_one : toDilatation (1 : A'[M.reindex]) = 1 := by
  change mk (toPreDil _) = _
  congr 1

lemma toDilatation_add (x y : A'[M.reindex]) :
    toDilatation (x + y) = toDilatation x + toDilatation y := by
  induction x using induction_on with
  | h x =>
    induction y using induction_on with
    | h y =>
      change mk (toPreDil (add' x y)) = mk (toPreDil x) + mk (toPreDil y)
      rw [mk_add_mk, toPreDil_add']

lemma toDilatation_mul (x y : A'[M.reindex]) :
    toDilatation (x * y) = toDilatation x * toDilatation y := by
  induction x using induction_on with
  | h x =>
    induction y using induction_on with
    | h y =>
      change mk (toPreDil (mul' x y)) = mk (toPreDil x) * mk (toPreDil y)
      rw [mk_mul_mk, toPreDil_mul']

/-- **Ring-theoretic reindexing invariance.** Dilating by the `ν`-indexed reindexing of `M`
(`Multicenter.reindex`) gives back the same ring as dilating by `M` directly. -/
noncomputable def reindexRingEquiv : A'[M.reindex] ≃+* A'[M] where
  toFun := toDilatation
  invFun := toDilatation'
  left_inv := toDilatation'_toDilatation
  right_inv := toDilatation_toDilatation'
  map_add' := toDilatation_add
  map_mul' := toDilatation_mul

lemma algebraMap_mul_fraction (ν : M^ℕ) (num : A') (hnum : num ∈ M.LargeIdeal ^ ν) :
    algebraMap A' A'[M] (M.elem ^ ν) * frac ν ⟨num, hnum⟩ = algebraMap A' A'[M] num := by
  simp only [algebraMap_apply, frac, mk_mul_mk, mk_eq_mk]
  exact ⟨0, by simp [mul_comm]⟩

end Dilatation

end semiring

section ring

namespace Dilatation

variable {A' : Type*} [CommRing A'] {M : Multicenter A'}

/-- Negation of a representative by negating its numerator. -/
@[simps]
def neg' (x : M.PreDil) : M.PreDil where
  pow := x.pow
  num := -x.num
  num_mem := neg_mem x.num_mem

instance : Neg A'[M] where
  neg := descFun (mk ∘ neg') <| by
    rintro x y ⟨α, hα⟩
    simp only [Function.comp_apply, mk_eq_mk]
    use α
    simp [hα]

lemma mk_neg (x : M.PreDil) : -mk x = mk (neg' x) := rfl

instance : CommRing A'[M] where
  __ := instCommSemiring
  zsmul := zsmulRec
  neg_add_cancel := by
    intro a
    induction a using induction_on with |h x =>
    simp only [mk_neg, mk_add_mk, zero_def, mk_eq_mk]
    use 0
    simp

lemma neg_frac (v : M^ℕ) (m : M.LargeIdeal ^ v) : -(m/.v) = (-m)/.v := by
  simp only [frac, mk_neg, mk_eq_mk]
  use 0
  simp

end Dilatation

end ring

section universal_property

variable {A' B' : Type*} [CommRing A'] [CommRing B'] (M : Multicenter A')

lemma cond_univ_implies_large_cond [Algebra A' B']
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B')
      (M.LargeIdeal i)) :
    (∀ (ν : M^ℕ), (Ideal.span {(algebraMap A' B') (M.elem ^ ν)} = Ideal.map (algebraMap A' B')
      (M.LargeIdeal ^ ν))) := by
     classical
     intro v
     simp only [familyPow_def, Finsupp.prod, map_prod, map_pow]
     rw [Ideal.prod_span']
     simp [← Ideal.span_singleton_pow, gen]
     simp [Ideal.prod_map, Ideal.map_pow]

lemma equ_trivial_image_divisor_ring [Algebra A' B'] :
    ∀ i, Ideal.map (algebraMap A' B') (Ideal.span {M.elem i})=
      Ideal.span {(algebraMap A' B') (M.elem i)} := by
      intro i
      rw [Ideal.map_span, Set.image_singleton]

lemma equiv_small_big_cond [Algebra A' B'] :
(    ∀ i, Ideal.map (algebraMap A' B') (Ideal.span {M.elem i}) = Ideal.map (algebraMap A' B')
    (M.LargeIdeal i)) ↔
(    ∀ i, Ideal.map (algebraMap A' B') (Ideal.span {M.elem i}) ≥  Ideal.map (algebraMap A' B')
    (M.ideal i)) := by
  simp only [LargeIdeal, Submodule.add_eq_sup, Ideal.map_sup]
  exact forall_congr' fun _ => eq_comm.trans sup_eq_right

lemma lemma_exists_in_image [Algebra A' B']
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B')
      (M.LargeIdeal i)) :
    (∀ (ν : M^ℕ) (m : M.LargeIdeal ^ ν),  (∃! bm : B',  (algebraMap A' B') (M.elem ^ ν) * bm =
      (algebraMap A' B') (m) )):= by
      intro v m
      have mem : (algebraMap A' B') m ∈  (M.LargeIdeal ^ v).map (algebraMap A' B') := by
          apply Ideal.mem_map_of_mem
          exact m.2
      rw [← cond_univ_implies_large_cond M gen] at mem
      rw [Ideal.mem_span_singleton'] at mem
      rcases mem with ⟨bm, eq_bm⟩
      use bm
      rw [mul_comm] at eq_bm
      use eq_bm
      intro bm' eq
      rw [← eq_bm] at eq
      rw [mul_cancel_left_mem_nonZeroDivisors] at eq
      · exact eq
      · simp only [familyPow_def, Finsupp.prod, map_prod, map_pow]
        apply prod_mem
        intro i hi
        apply pow_mem
        apply non_zero_divisor

/-- The unique quotient of a mapped numerator by its mapped denominator. -/
def fractionValue [Algebra A' B'] (v : M^ℕ) (m : M.LargeIdeal ^ v)
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B')
      (M.LargeIdeal i)): B' :=
     (lemma_exists_in_image M non_zero_divisor gen v m).choose

lemma fractionValue_spec [Algebra A' B'] (v : M^ℕ) (m : M.LargeIdeal ^ v)
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B')
      (M.LargeIdeal i)) :
    (algebraMap A' B') (M.elem ^ v) * fractionValue M v m non_zero_divisor gen = (algebraMap
      A' B') m := by
    apply (lemma_exists_in_image M non_zero_divisor gen v m).choose_spec.1

lemma fractionValue_unique [Algebra A' B'] (v : M^ℕ) (m : M.LargeIdeal ^ v)
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B')
      (M.LargeIdeal i)) :
    ∀ bm : B', (algebraMap A' B') (M.elem ^ v) * bm = (algebraMap A' B') m → fractionValue M
      v m non_zero_divisor gen = bm := by
    intro bm hbm
    apply ((lemma_exists_in_image M non_zero_divisor gen v m).choose_spec.2 bm hbm).symm

/-- The algebra homomorphism determined by the universal property of ring dilatations. -/
def desc [Algebra A' B']
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B')
      (M.LargeIdeal i)) :
     A'[M] →ₐ[A'] B' where
  toFun := Dilatation.descFun (fun x ↦ fractionValue M x.pow ⟨x.num, x.num_mem⟩
    non_zero_divisor gen)
    (by
      intro x y h
      rcases h with ⟨β, hβ⟩
      apply fractionValue_unique
      apply_fun (fun z => (algebraMap A' B') (M.elem ^  (β + y.pow)) * z)
      · simp only []
        rw [← map_mul, mul_comm _ x.num]
        rw [hβ]
        simp only [map_mul]
        rw [← fractionValue_spec M y.pow ⟨y.num, y.num_mem⟩ non_zero_divisor gen]
        simp only [familyPow_add, map_mul]
        ring
      · intro x y hx
        simp only at hx
        rwa [mul_cancel_left_mem_nonZeroDivisors] at hx
        simp only [familyPow_def, Finsupp.prod, Finsupp.coe_add,
          Pi.add_apply, map_prod, map_pow]
        apply prod_mem
        intro i hi
        apply pow_mem
        apply non_zero_divisor)
  map_one' := by
    simp only [Dilatation.descFun, Dilatation.one_def]
    apply fractionValue_unique
    simp
  map_mul' := by
    intro x y
    induction x using Dilatation.induction_on with |h x =>
    induction y using Dilatation.induction_on with |h y =>
    simp only [Dilatation.mk_mul_mk]
    apply fractionValue_unique
    · exact non_zero_divisor
    · exact gen
    · simp only [Dilatation.mul'_pow, Dilatation.descFun_mk, Dilatation.mul'_num, map_mul]
      rw [familyPow_add]
      rw [← fractionValue_spec M y.pow ⟨y.num, y.num_mem⟩ non_zero_divisor gen]
      rw [← fractionValue_spec M x.pow ⟨x.num, x.num_mem⟩ non_zero_divisor gen]
      simp only [map_mul]
      ring
  map_zero' := by
    simp only [Dilatation.descFun]
    apply fractionValue_unique
    simp
  map_add' :=  by
    intro x y
    induction x using Dilatation.induction_on with |h x =>
    induction y using Dilatation.induction_on with |h y =>
    simp only [Dilatation.mk_add_mk]
    apply fractionValue_unique
    · exact non_zero_divisor
    · exact gen
    · simp only [Dilatation.add'_pow, Dilatation.descFun_mk, Dilatation.add'_num, map_add, map_mul]
      rw [familyPow_add]
      rw [← fractionValue_spec M y.pow ⟨y.num, y.num_mem⟩ non_zero_divisor gen]
      rw [← fractionValue_spec M x.pow ⟨x.num, x.num_mem⟩ non_zero_divisor gen]
      simp only [map_mul]
      ring
  commutes' := by
    intro x
    simp only [Dilatation.descFun]
    apply fractionValue_unique
    simp

open Multicenter
open Dilatation
lemma dsc_spec [Algebra A' B'] (v : M^ℕ) (m : M.LargeIdeal ^ v)
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B')
      (M.LargeIdeal i)) :
    (algebraMap A' B') (M.elem ^ v) * desc M non_zero_divisor gen (m/.v) = (algebraMap A' B')
      m := by
    apply (lemma_exists_in_image M non_zero_divisor gen v m).choose_spec.1

lemma lemma_exists_unique_morphism [Algebra A' B']
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B')
      (M.LargeIdeal i))
    (χ' : A'[M] →ₐ[A'] B') : χ' = desc M non_zero_divisor gen := by
  ext x
  induction x using induction_on with
  | h x =>
    change χ' (frac x.pow ⟨x.num, x.num_mem⟩) =
      fractionValue M x.pow ⟨x.num, x.num_mem⟩ non_zero_divisor gen
    symm
    apply fractionValue_unique
    rw [← AlgHom.commutes χ', ← map_mul, algebraMap_mul_fraction, AlgHom.commutes]

open Dilatation
open Multicenter
lemma reciprocal_for_univ [Algebra A' B'] (M : Multicenter A')
    (χ' : A'[M] →ₐ[A'] B') (i : M.index) :
    Ideal.span {algebraMap A' B' (M.elem i)} =
      Ideal.map (algebraMap A' B') (M.LargeIdeal i) := by
  have h := congrArg (Ideal.map χ'.toRingHom)
    (image_elem_LargeIdeal_equal (M := M) (Finsupp.single i 1))
  simpa [familyPow_def, Ideal.map_span, Ideal.map_map, AlgHom.comp_algebraMap] using h

end universal_property

end Multicenter

end RingDilatation

end CategoryTheory.Dilatations
