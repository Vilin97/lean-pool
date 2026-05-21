/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.CertifyKernel
import LeanPool.RingOfIntegersProject.DedekindCriteria
import LeanPool.RingOfIntegersProject.Semilinear
import Mathlib.Data.ZMod.Basic

/-!

# Certify Maximality

With `O` a commutative ring and `Iₚ` the radical of `pO`, we construct the associated
objects, maps, and bases that will help us certify the `p`-maximality of `O`.

## Main definitions
- `basis_radical_of_linear_independent_ker_im` : an explicit basis for `Iₚ / pIₚ`
- `map_to_end_lin` : a linear map from `O / pO` to the linear endomorphisms of `Iₚ / pIₚ`.

## Main results
- `radical_eq_kernel_iter_frob_aux` : the kernel of the iterated Frobenius map is `Iₚ / pIₚ`.
- `p_maximal_of_trivial_ker_map_to_end_lin` : Under certain hypothesis,
    if the kernel of `map_to_end_lin` is trivial, then `O` is p-maximal.
- `ker_map_to_end_lin_eq_bot_of_mul_ne_zero'` : a way to certify that the kernel
  of `map_to_end_lin` is trivial.
- `ker_map_to_end_lin_eq_bot_of_mul_ne_zero_of_single_eval` : another way to certify that the
  kernel of `map_to_end_lin` is trivial using less operations.    -/


open BigOperators Pointwise

lemma smul_int_coe_eq_mul {S R : Type* } [CommRing R]
    [CommRing S] [Module S R] (n : ℤ) {x : R} : (n : S) • x = ↑n * x := by
  rw [(Int.smul_one_eq_cast n).symm, smul_assoc, one_smul, zsmul_eq_mul]

/-- The Frobenius map as an `(ZMod p)`-linear map· -/
def Frob (R : Type*) (p : ℕ) [CommRing R] [Module (ZMod p) R]
    [CharP R p] [hp : Fact $ Nat.Prime p] : R →ₗ[(ZMod p)] R :=
{ toFun := frobenius R p
  map_add' := by simp only [map_add, forall_const]
  map_smul' := by
    intros r x
    simp only [RingHom.id_apply]
    have : r = ((r.val : ℤ) : ZMod p) := by simp only [ZMod.natCast_val, ZMod.intCast_cast,
      ZMod.cast_id', id_eq]
    rw [this, smul_int_coe_eq_mul, smul_int_coe_eq_mul, map_mul]
    congr
    rw [map_intCast (frobenius R p)] }

/-- Iterating Frob `n` times is equal to raising to the `p ^ n` power· -/
lemma iter_Frob (R : Type*) (p : ℕ) [CommRing R]
    [Module (ZMod p) R] [CharP R p] [hp : Fact $ Nat.Prime p] (x : R) (n : ℕ) :
    ( (Frob R p) ^ n) x = x ^ (p ^ n) := by {erw [LinearMap.pow_apply, iterate_frobenius ] }

/--If `M` is an `R`-submodule, then an element is in `y • ⊤` if and only if it can be written as `y • a` for `a` in `M`· -/
lemma smul_top_mem_iff_eq_smul {R M : Type*} [AddCommGroup M][CommRing R][Module R M](y : R) (x : M) :
   x ∈ y • (⊤ : Submodule R M ) ↔ ∃ (a : M), y • a = x := by
  constructor
  · rintro ⟨a, _, ha⟩
    simp only [DistribMulAction.toLinearMap_apply] at ha
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    use a
    simp only [ * , Submodule.top_coe, Set.mem_univ, DistribMulAction.toLinearMap_apply, eq_self_iff_true, and_self]

/-- An `R` basis for the ideal `p • O` given an `R`-basis for `O`.
  We don't assume `O` is a domain, so we don't make use of `Ideal.ringBasis` -/
noncomputable def idealSmulNatBasis {O τ R: Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (p : R) (hp : p ≠ 0) [CommRing O] [Algebra R O]
    [NoZeroSMulDivisors R O] (b : Basis τ R O ) :
    Basis τ R ((algebraMap R O p) • ⊤ : Ideal O ) := by
  have := (LinearEquiv.ofInjective (LinearMap.lsmul R O p) ?_).symm
  have heq : LinearMap.range ((LinearMap.lsmul R O p)) =
    Submodule.restrictScalars R ((algebraMap R O p) • ⊤ : Ideal O ) := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.restrictScalars_mem, smul_top_mem_iff_eq_smul]
    constructor
    · intro hx
      rw [←  hx.choose_spec]
      use hx.choose
      exact algebraMap_smul O p (Exists.choose hx)
    · intro hx
      rw [←  hx.choose_spec]
      use hx.choose
      exact algebra_compatible_smul O p (Exists.choose hx)
  let e : Submodule.restrictScalars R ((algebraMap R O p) • ⊤ : Ideal O ) ≃ₗ[R]
    ((algebraMap R O p) • ⊤ : Ideal O ) := LinearEquiv.refl R _
  let aux := LinearEquiv.trans ( LinearEquiv.trans  e.symm (LinearEquiv.ofEq _ _ heq.symm)) this
  exact Basis.ofRepr (LinearEquiv.trans aux b.repr)
  · exact LinearMap.lsmul_injective hp

/-- The radical of an ideal with full rank has full rank· We don't assume `O` is a domain· -/
noncomputable def radicalFullRank {O τ R: Type*} [CommRing R] [IsDomain R][IsPrincipalIdealRing R]
    [Fintype τ] [CommRing O] [Algebra R O] [NoZeroSMulDivisors R O] (I : Ideal O) (b : Basis τ R O )
    (b' : Basis τ R I):
  Basis τ R I.radical := by
  haveI : Module.Finite R O := Module.Finite.of_basis b
  obtain ⟨n, B⟩ := Submodule.basisOfPid b (Submodule.restrictScalars R I.radical)
  haveI : Module.Finite R (Submodule.restrictScalars R I.radical) := Module.Finite.of_basis B
  have aux0 := Submodule.finrank_le (Submodule.restrictScalars R I.radical)
  have aux1 : (Submodule.restrictScalars R I) ≤ (Submodule.restrictScalars R I.radical) := by
    intro x hx
    simp only [Submodule.restrictScalars_mem] at hx ⊢
    exact Ideal.le_radical hx
  have aux2 := Submodule.finrank_mono aux1
  erw [Module.finrank_eq_card_basis b'] at aux2
  rw [Module.finrank_eq_card_basis b] at aux0
  have aux3 := LE.le.antisymm aux0 aux2
  rw [Module.finrank_eq_card_basis B] at aux3
  exact Basis.reindex B (Fintype.equivOfCardEq aux3)

/-- A basis for the radical of `p • O`· -/
noncomputable def radicalSmulFullRank {O τ R: Type*} [CommRing R] [IsDomain R][IsPrincipalIdealRing R]
    (p : R) (hp : p ≠ 0) [Fintype τ] [CommRing O] [Algebra R O] [NoZeroSMulDivisors R O]
    (b : Basis τ R O ) : Basis τ R ((algebraMap R O p) • ⊤ : Ideal O ).radical :=
  radicalFullRank ((algebraMap R O p) • ⊤ : Ideal O ) b (idealSmulNatBasis p hp b)

lemma smul_top_eq_span_singleton {R : Type*} [CommRing R] (y : R) :
     y • (⊤ : Submodule R R ) = Submodule.span R ({y} : Set R) := by
  ext x
  simp_rw [Submodule.mem_span_singleton, Algebra.id.smul_eq_mul, mul_comm, ← Algebra.id.smul_eq_mul]
  exact smul_top_mem_iff_eq_smul y x

section Part0

/- NOTE:
 We want `O/pO` to have the instance of a ring· For this we need `pO` to be of type
`ideal O`· On the other hand, `Iₚ`, the radical of `pO`, is not a ring, so we may take
`pIₚ` to be just an additive subgroup of type `(submodule ℤ Iₚ)`.
 To unify these two approaches and not have duplicates of essentially the same proofs, we note that
 `Ideal O` is definitionally equal to `Submodule O O`· Hence, for an abelian additive group `M`
 we formalize the quotient `M/nM` using a commutative ring `R` as a parameter
 (such that `M` is an `R-module`), with the definition `M ⧸ (n : R) • (⊤ : submodule R M ) `·  -/

variable (R M : Type*) (n: ℕ) [AddCommGroup M] [CommRing R] [Module R M]

local notation M "mod'" n =>  M ⧸ (n: R) • (⊤ : Submodule R M )
local notation x "mod" n => (@Submodule.Quotient.mk R M _ _ _ ((n: R) • (⊤ : Submodule R M ) )) x

lemma smul_p_eq_zero (b : M mod' n) :  n • b = 0 := by
  choose c hc using (Submodule.Quotient.mk_surjective _ b)
  rw [← hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul R]
  rw [smul_top_mem_iff_eq_smul _ _]
  use c

/-- The `(ZMod n)-module` instance on `M/nM`· -/
instance module_modp_is_zmodp_module [NeZero n] :
Module (ZMod n) (M mod' n) := by
exact
{ smul := fun ( s : ZMod n) (x : M mod' n ) => (s.val) • x
  one_smul := by
    · by_cases ho : 1 < n
      · haveI : Fact (1 < n) := { out := ho }
        intro s
        show (1 : ZMod n).val • s = s
        rw [ZMod.val_one , one_smul]
      · have : n = 1 :=
          Eq.symm (Nat.le_antisymm (NeZero.one_le ) (not_lt.1 ho))
        intro s
        show (1 : ZMod n).val • s = s
        haveI : Subsingleton (M mod' n) := by
          rw [this, Nat.cast_one, one_smul]
          infer_instance
        rw [Subsingleton.eq_zero s, smul_zero]
  mul_smul := by
    · intros x y b
      show (x * y).val • b = x.val • y.val • b
      rw [ZMod.val_mul, ← mul_smul]
      nth_rw 2 [← Nat.mod_add_div (x.val * y.val) n]
      rw [add_smul, mul_smul, smul_p_eq_zero R M n, add_zero]
  smul_zero := by
    · intro a
      show a.val • (0 : M mod' n) = 0
      refine smul_zero _
  add_smul := by
    · intros r s x
      show (r + s).val • x = r.val • x + s.val • x
      rw [← add_smul, ZMod.val_add]
      nth_rw 2 [← Nat.mod_add_div (r.val + s.val) n]
      rw [add_smul, mul_smul, smul_p_eq_zero R M n, add_zero]
  zero_smul := by
    · intro x
      show (0 : ZMod n).val • x = 0
      rw [ZMod.val_zero, zero_smul]
  smul_add := by
    · intro a x y
      show a.val • (x + y) = a.val • x + a.val • y
      exact smul_add _ _ _ }


lemma zmodp_smul_def [NeZero n] (x : M mod' n) (r : ZMod n) :
  r • x = (r.val) • x := rfl

@[simp]
lemma zsmul_eq_zmod_smul [NeZero n] (x : M) (r : ℤ ) :
    ((r • x) mod n) = (r : ZMod n) • (x mod n) := by
  rw [Submodule.Quotient.mk_smul, zmodp_smul_def]
  nth_rw 1 [← Int.emod_add_ediv r n]
  rw [add_smul, mul_smul]
  norm_cast
  rw [smul_p_eq_zero R M n, add_zero, ← ZMod.val_intCast]
  norm_cast

/-- The quotient map `M → M/nM` as a `ℤ → (ZMod n)`- semilinear map· -/
def quotientMkToSemilinear [NeZero n] : M →ₛₗ[Int.castRingHom (ZMod n)] (M mod' n) := by
exact
 {toFun := (@Submodule.Quotient.mk R M _ _ _ ((n : R) • (⊤ : Submodule R M ) ))
  map_add' := by simp only [Submodule.Quotient.mk_add, forall_const]
  map_smul' := by simp only [zsmul_eq_zmod_smul, eq_intCast, eq_self_iff_true, forall_const]  }

lemma quotientMkToSemilinear_apply [NeZero n] (x : M) :
  quotientMkToSemilinear R M n x = (@Submodule.Quotient.mk R M _ _ _ ((n : R) • (⊤ : Submodule R M ) )) x := rfl

instance : RingHomSurjective (Int.castRingHom (ZMod n)) :=
  ⟨ZMod.ringHom_surjective (Int.castRingHom (ZMod n))⟩

noncomputable def quotientMkToSemilinear_f' [NeZero n] : (M mod' n) → M  :=
  (Function.Surjective.hasRightInverse
    (Submodule.Quotient.mk_surjective (((n : R) • (⊤ : Submodule R M ) )))).choose

def quotientMkToSemilinear_g' [NeZero n] : ZeroHom (ZMod n) ℤ :=
  ⟨ZMod.valMinAbs , ZMod.valMinAbs_zero  n⟩

lemma quotientMkToSemilinear_f_rightInverse [NeZero n] :
    Function.RightInverse (quotientMkToSemilinear_f' R M n) (quotientMkToSemilinear R M n) :=
  (Function.Surjective.hasRightInverse
    (Submodule.Quotient.mk_surjective (((n : R) • (⊤ : Submodule R M ) )))).choose_spec

lemma quotientMkToSemilinear_g_rightInverse [NeZero n] :
    Function.RightInverse (quotientMkToSemilinear_g' n) (Int.castRingHom (ZMod n)) := by
  intro x
  unfold quotientMkToSemilinear_g'
  simp only [ZeroHom.coe_mk, eq_intCast, ZMod.coe_valMinAbs]

lemma semilinear_ker_le_ker [NeZero n] :
    LinearMap.ker (quotientMkToSemilinear R M n) ≤ RingHom.ker (Int.castRingHom (ZMod n)) • (⊤ : Submodule ℤ M) := by
  intros x hx
  erw [LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero, smul_top_mem_iff_eq_smul ]  at hx
  obtain ⟨a, ha⟩ := hx
  have : (↑ (↑n : ℤ ) : R) = (↑n : R) := by norm_cast
  rw [← this, Int.cast_smul_eq_zsmul _ (n : ℤ) a] at ha
  rw [← ha]
  refine Submodule.smul_mem_smul  ?_ (Submodule.mem_top )
  rw [ZMod.ker_intCastRingHom]
  exact Ideal.mem_span_singleton_self (↑n : ℤ)

/-- If `{bᵢ ∣ i ∈ τ }` is a `ℤ`-basis for `M`, we get a `(ZMod n)`-basis for `M/nM` by taking
`{bᵢ mod n ∣ i ∈ τ }`· -/
noncomputable def zmodpBasisOfIntBasis [NeZero n] {τ : Type*} (b : Basis τ ℤ M) :
    Basis τ (ZMod n) (M mod' n) :=
  Basis.comp_semilinear _ (quotientMkToSemilinear_g' n)
  (quotientMkToSemilinear_g_rightInverse n) (quotientMkToSemilinear R M n)
  (quotientMkToSemilinear_f' R M n) (quotientMkToSemilinear_f_rightInverse R M n) b (semilinear_ker_le_ker R M n)

end Part0

open Polynomial

section Part1

/- Let `O` be a commutative ring and `p` a nonzero natural number.
  We let `R` denote the ring `O/pO`· We denote by `x mod p` the
  image of `x` under `O → O/pO`· -/

variable (O : Type*) [CommRing O] (p : ℕ)

local notation "R" =>  O ⧸ (p : O) • (⊤ : Submodule O O)
local notation x "mod" p => (Ideal.Quotient.mk ((p : O) • (⊤ : Submodule O O))) x

/-- The `(ZMod p)`-algebra instance of `O/pO`· -/
instance ringModpIsZModpAlgebra [NeZero p] : Algebra (ZMod p) R := by
refine Algebra.ofModule ?_ ?_
· intros r x y
  rw [zmodp_smul_def , zmodp_smul_def]
  simp only [nsmul_eq_mul, ZMod.natCast_val, mul_assoc]
· intros r x y
  rw [zmodp_smul_def , zmodp_smul_def]
  simp only [nsmul_eq_mul, ZMod.natCast_val]
  ring

-- It's good to have a version of this for the ideal quotient map.
-- which is def_eq to the submodule quotient map, but we can use the map API·  -/

@[simp]
lemma zsmul_map_zmodsmul [NeZero p] (x : O) (m : ℤ) :
  ((m • x) mod p ) = (m : ZMod p) • (x mod p) := zsmul_eq_zmod_smul O O p x m

lemma zmod_smul_eq_mul [NeZero p] (x : R) (m : ZMod p) :
    m • x = ((m.val : O) mod p) * x := by
  obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective x
  erw [← hq, ← ZMod.intCast_zmod_cast m , ← zsmul_map_zmodsmul, zsmul_eq_mul, map_mul]
  simp only [ZMod.intCast_cast, ZMod.cast_id', id_eq, ZMod.natCast_val]


/-- The ring `O / pO`, with `p` prime, has characteristic equal to `p`· -/
instance char_R_eq_p [hp : Fact $ Nat.Prime p] [Nontrivial R]: CharP R p := by
  rw [← RingHom.charP_iff_charP  (algebraMap (ZMod p) R) p]
  exact ZMod.charP p

/-- If `O` is nontrivial, free as a ℤ module, and `p ≠ 0, 1`, then `O / pO` is nontrivial·  -/
instance nontrivial_R [NeZero p] (hpo : p ≠ 1)
    [Nontrivial O] [Module.Free ℤ O]  : Nontrivial R  := by
  by_contra h
  erw [not_nontrivial_iff_subsingleton, Submodule.subsingleton_quotient_iff_eq_top] at h
  let b := Module.Free.chooseBasis ℤ O
  let τ := Module.Free.ChooseBasisIndex ℤ O
  haveI := Classical.inhabited_of_nonempty (Basis.index_nonempty b)
  let i := Classical.arbitrary τ
  have : b i ∈ (⊤ : Ideal O) := Submodule.mem_top
  rw [← h] at this
  cases this
  case _ a ha =>
  · simp only [Submodule.top_coe, Set.mem_univ, DistribMulAction.toLinearMap_apply,
    Algebra.id.smul_eq_mul, true_and] at ha
    apply_fun b.coord i at ha
    simp only [Basis.coord_apply, Basis.repr_self,
    Finsupp.single_eq_same, ← nsmul_eq_mul, map_nsmul] at ha
    rw [nsmul_eq_mul] at ha
    have := isUnit_of_mul_eq_one _ _ ha
    rw [Int.ofNat_isUnit, Nat.isUnit_iff ] at this
    exact hpo this

instance nontrivial_R_prime [hp : Fact $ Nat.Prime p]
    [Nontrivial O] [Module.Free ℤ O] : Nontrivial R := by
  refine nontrivial_R O p (Nat.Prime.ne_one hp.out)

/-- A `ZMod p`-basis for `O / pO` obtained by reducing a basis for `O`· -/
@[irreducible]
noncomputable def basis_zmodp_algebra [NeZero p] {τ : Type* } (b : Basis τ ℤ O )  :
  Basis τ (ZMod p) R := zmodpBasisOfIntBasis O O p b

lemma basis_is_modp [NeZero p] {τ : Type* } (b : Basis τ ℤ O ) (i : τ) :
    (basis_zmodp_algebra O p b) i = (b i mod p) := by
  · unfold basis_zmodp_algebra
    unfold zmodpBasisOfIntBasis
    erw [Basis.mk_apply] ; rfl

/-- Reducing modulo `p` the coordinates of an element in `O` gives the coordinates
  of the image of such element in `O / pO`, with respect to `basis_zmodp_algebra`·  -/
lemma basis_zmodp_repr_eq_zmodp_basis_repr {τ : Type* } [NeZero p] (b : Basis τ ℤ O ) (x : O) :
    (algebraMap ℤ (ZMod p)) ∘ (b.repr x) = (basis_zmodp_algebra O p b).repr (x mod p) := by
  unfold basis_zmodp_algebra
  unfold zmodpBasisOfIntBasis
  have : (x mod p) = quotientMkToSemilinear O O p x := rfl
  rw [this]
  haveI : RingHomSurjective (Int.castRingHom (ZMod p)) := ⟨ZMod.ringHom_surjective (Int.castRingHom (ZMod p))⟩
  erw [← Basis.comp_semilinear_repr]
  rfl

lemma basis_zmodp_repr_mul_eq_zmodp_basis_repr_mul {τ : Type* } [NeZero p]
    (b : Basis τ ℤ O ) (i j k : τ) :
    (basis_zmodp_algebra O p b).repr (((basis_zmodp_algebra O p b) i) * ((basis_zmodp_algebra O p b) j)) k
    =  ((algebraMap ℤ (ZMod p)) ∘ (b.repr ((b i) * (b j)))) k := by
  rw [basis_is_modp O p b i, basis_is_modp O p b j, ← map_mul, ← basis_zmodp_repr_eq_zmodp_basis_repr ]


end Part1

section PartIII

variable (O : Type*) [CommRing O] (p : ℕ)

-- This is `I / pO` as a submodule of `O / pO`
local notation I "mod'" p => Submodule.map (quotientMkToSemilinear O O p) (Submodule.restrictScalars ℤ I)

local notation "R" =>  O ⧸ (p : O) • (⊤ : Submodule O O)
local notation x "mod p"  => (Ideal.Quotient.mk ((p : O) • (⊤ : Submodule O O))) x
local notation "Ip" => Ideal.radical ((p : O) • (⊤ : Submodule O O) : Ideal O)

/- `x` is in `Ip / pO` if and only if `x ^ (p ^ j) = 0` with ` n ≤ p ^ j`· -/
lemma radical_eq_kernel_iter_frob_aux (n j: ℕ) [Fact $ Nat.Prime p]
    (b : Basis (Fin n) ℤ O ) (hle : n ≤ p ^ j) (x : R) :
    x ∈ (Ip mod' p) ↔ x ^ (p ^ j) = 0 := by
  haveI := Module.Finite.of_basis (basis_zmodp_algebra O p b)
  constructor
  swap
  · intro hx
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective x
    rw [← hy, ← map_pow, Ideal.Quotient.eq_zero_iff_mem ] at hx
    have hymem : y ∈ Ideal.radical ((p : O) • (⊤ : Submodule O O) : Ideal O) := ⟨p^j, hx⟩
    exact ⟨y, hymem, hy⟩
  · rintro ⟨y, ⟨m, hyn ⟩ , hy⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← Ideal.Quotient.mk_eq_mk , ←quotientMkToSemilinear_apply,  hy] at hyn
    have hmin : minpoly (ZMod p) x ∣ X ^ m := by
      apply minpoly.dvd
      rw [aeval_X_pow, hyn]
    let f := LinearMap.mulLeft (ZMod p) x
    have hmin2 : minpoly (ZMod p) x ∣ f.charpoly := by
      apply minpoly.dvd
      let M : Polynomial (ZMod p) → Prop := λ q => (aeval f q 1 = aeval (f 1) q)
      have :  M f.charpoly := by
        refine Polynomial.induction_on' (f.charpoly) ?_ ?_
        · intros p' q hp hq
          simp only [M, *, aeval_add, LinearMap.add_apply]
        · intros n a
          simp only [M, f, aeval_monomial, LinearMap.pow_mulLeft, LinearMap.mul_apply, LinearMap.mulLeft_apply, mul_one,
            Module.algebraMap_end_apply, Algebra.smul_def _ _]
      simp only [M, f, LinearMap.mulLeft_apply, mul_one] at this
      rw [← this, LinearMap.aeval_self_charpoly f, LinearMap.zero_apply]
    rw [← LinearMap.charpoly_toMatrix f (basis_zmodp_algebra O p b)] at hmin2
    have hle2 := Polynomial.natDegree_le_of_dvd hmin2 ?_
    · rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin n] at hle2
      obtain ⟨r, hrm, hr⟩ := ( dvd_prime_pow Polynomial.prime_X m ).1 hmin
      replace hr := Polynomial.eq_of_monic_of_associated (minpoly.monic ?_) (Polynomial.monic_X_pow r) hr
      swap
      · use (X ^ m : Polynomial $ ZMod p)
        refine ⟨Polynomial.monic_X_pow m, ?_⟩
        · simp only [eval₂_X_pow] ; exact hyn
      · rw [hr, Polynomial.natDegree_X_pow ] at hle2
        apply pow_eq_zero_of_le hle
        apply pow_eq_zero_of_le hle2
        rw [← minpoly.aeval (ZMod p) x, hr]
        exact (aeval_X_pow x).symm
    refine Polynomial.Monic.ne_zero ?_
    exact Matrix.charpoly_monic _

/- The kernel of the iterated Frobenius map is equal to `Ip / pO`· -/
lemma radical_eq_kernel_iter_frob (n j : ℕ) [Fact $ Nat.Prime p] [Nontrivial O] [Module.Free ℤ O]
    (b : Basis (Fin n) ℤ O ) (hle : n ≤ p ^ j) : (Ip mod' p) = LinearMap.ker ((Frob R p) ^ j) := by
  { ext x ; erw [LinearMap.mem_ker ,  iter_Frob]; exact radical_eq_kernel_iter_frob_aux O p n j b hle x }

end PartIII


section PartIV

variable (O : Type*) (p : ℕ) [CommRing O] [hpI : Fact $ Nat.Prime p]

local notation "Ip" =>  Ideal.radical ((p : O) • (⊤ : Submodule O O) : Ideal O)

-- This is I / pI
local notation I "mod' p"  =>  I ⧸ (p : ℤ ) • (⊤ : Submodule ℤ I )
local notation x "mod p"  => (@Submodule.Quotient.mk ℤ Ip _ _ _ ((p : ℤ) • (⊤ : Submodule ℤ Ip ))) x
local notation "R" =>   O ⧸ (p : O) • (⊤ : Submodule O O)
local notation x "mod'' p"  => (Ideal.Quotient.mk ((p : O) • (⊤ : Submodule O O))) x

-- This is I / pO as a submodule of O/pO
local notation I "mod'''" p => Submodule.map (quotientMkToSemilinear O O p) (Submodule.restrictScalars ℤ I)

lemma p_smul_top' (y : O) (x : O) :
    x ∈  (y : O) • (⊤ : Submodule O O) ↔ ∃ (a : O), y * a = x := by
  simp only [smul_top_mem_iff_eq_smul , Algebra.id.smul_eq_mul]

lemma p_smul_top (y : O) (x : O) :
    x ∈  (y : O) • (⊤ : Submodule O O) ↔ ∃ (a : O), y • a = x := by
  exact smul_top_mem_iff_eq_smul y x

omit hpI in
lemma ideal_span_eq_smul_top :
    Ideal.span ({↑p } : Set O) = (↑p : O) • (⊤ : Submodule O O) := by
  exact (smul_top_eq_span_singleton (p : O)).symm

/-- If the reduction of `a` in `O/ pO` is in `Ip / pO` (as the image of `Ip` through the
  reduction map), then `a` is in `Ip`·  -/
lemma in_radical_of_in_radical_mod {a : O} :
     (a mod'' p) ∈ (Ip mod''' p) → a ∈ Ip := by
  intro hrad
  obtain ⟨k, hk1, hk2⟩ := hrad
  simp only [Submodule.coe_restrictScalars, SetLike.mem_coe] at hk1
  rw [quotientMkToSemilinear_apply, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq] at hk2
  rw [(sub_sub_self k a).symm]
  refine Ideal.sub_mem _ hk1 (Ideal.le_radical hk2)

lemma in_radical_mod_of_mod_eq  (b1 : Ip mod''' p) (b : O) :
    b1.1 = (b mod'' p) →  (b mod'' p) ∈ (Ip mod''' p) := by
  intro heq1'
  simp_rw [← heq1']
  simp only [SetLike.coe_mem]

variable [Nontrivial O] [Module.Free ℤ O]

 /-- If `O` has rank `m + n` and `{b₁, …, bₘ, b'₁, …, b'ₙ}` are elements in `O` such that
 their image in `O / pO` is a `(ZMod p)`-basis, and the reductions of `{b₁, …, bₘ}`
 are a `(ZMod p)`-basis for the subspace `Iₚ / pO`, then the reductions of
 `{b₁, …, bₘ, p • b'₁, …, p • b'ₙ}` in `Iₚ / pIₚ` are a `(ZMod p)`-basis for this space· -/
noncomputable def basis_radical_of_basis_radical_mod [NoZeroSMulDivisors ℤ O]{n m : ℕ}
    [Nonempty (Fin m ⊕ Fin n)](b : Fin m → O ) (b' : Fin n → O )
    (b1 : Basis (Fin m) (ZMod p) (Ip mod''' p))
    (b2 : Basis (Fin m ⊕ Fin n) (ZMod p) R) (b3 : Basis (Fin (m + n)) ℤ O)
    (heq1' : ∀ (i : Fin m), (b1 i).1  = ((b i) mod'' p) )
    (heq2 : ∀ (i : Fin m), b2 (Sum.inl i) = (b i mod'' p))
    (heq3 : ∀ (i : Fin n), b2 (Sum.inr i) = (b' i mod'' p)):
    Basis (Fin m ⊕ Fin n) (ZMod p) (Ip mod' p) := by
  refine basisSubmoduleModOfBasisMod (I := Submodule.restrictScalars ℤ Ip)
    (ZMod.ker_intCastRingHom p) (NeZero.natCast_ne p ℤ) (quotientMkToSemilinear_g' p)
    (quotientMkToSemilinear_g_rightInverse p) (quotientMkToSemilinear O O p)
    (semilinear_ker_le_ker O O p) ?_ (Ip mod''' p) (quotientMkToSemilinear ℤ Ip p)
    (quotientMkToSemilinear_f' ℤ Ip p) (quotientMkToSemilinear_f_rightInverse ℤ Ip p)
    (semilinear_ker_le_ker ℤ Ip p) ?_ b b' b1 b2 ?_ ?_ ?_ ?_
  · rw [(ZMod.ker_intCastRingHom p), Submodule.ideal_span_singleton_smul]
    intro x hx
    rw [Submodule.restrictScalars_mem]
    refine Ideal.le_radical ?_
    simp only [smul_top_mem_iff_eq_smul, zsmul_eq_mul, Int.cast_natCast, smul_eq_mul] at hx ⊢
    exact_mod_cast hx
  · rfl
  · have aux : (p : O) = algebraMap ℤ O (p : ℤ) := by simp only [algebraMap_int_eq, map_natCast]
    rw [aux]
    exact radicalSmulFullRank (p : ℤ) (NeZero.natCast_ne p ℤ) b3
  · exact heq1'
  · exact heq2
  · exact heq3


omit [Nontrivial O] in
lemma basis_radical_def_left {n m : ℕ}[Nonempty (Fin m ⊕ Fin n)]
    (b : Fin m → O ) (b' : Fin n → O ) (b1 : Basis (Fin m) (ZMod p) (Ip mod''' p))
    (b2 : Basis (Fin m ⊕ Fin n) (ZMod p) R)(b3 : Basis (Fin (m + n)) ℤ O)
    (heq1' : ∀ (i : Fin m), (b1 i).1  = ((b i) mod'' p) )
    (heq2 : ∀ (i : Fin m), b2 (Sum.inl i) = (b i mod'' p))
    (heq3 : ∀ (i : Fin n), b2 (Sum.inr i) = (b' i mod'' p)) (i : Fin m) :
    (basis_radical_of_basis_radical_mod O p b b' b1 b2 b3 heq1' heq2 heq3) (Sum.inl i)
    = (⟨b i, in_radical_of_in_radical_mod O p (in_radical_mod_of_mod_eq O p _ _ (heq1' i))⟩ mod p) := by
  unfold basis_radical_of_basis_radical_mod
  unfold basisSubmoduleModOfBasisMod
  erw [Basis.mk_apply]
  rfl


omit [Nontrivial O] in
lemma basis_radical_def_right {n m : ℕ} [Nonempty (Fin m ⊕ Fin n)]
    (b : Fin m → O) (b' : Fin n → O) (b1 : Basis (Fin m) (ZMod p) (Ip mod''' p))
    (b2 : Basis (Fin m ⊕ Fin n) (ZMod p) R) (b3 : Basis (Fin (m + n)) ℤ O)
    (heq1' : ∀ (i : Fin m), (b1 i).1  = (b i) mod'' p)
    (heq2 : ∀ (i : Fin m), b2 (Sum.inl i) = (b i mod'' p))
    (heq3 : ∀ (i : Fin n), b2 (Sum.inr i) = (b' i mod'' p)) (j : Fin n) :
    (basis_radical_of_basis_radical_mod O p b b' b1 b2 b3 heq1' heq2 heq3) (Sum.inr j) =
    (⟨(p : ℤ) • b' j, Ideal.le_radical ((smul_top_mem_iff_eq_smul (p : O) ((p : ℤ)  • b' j)).2
      ⟨b' j, by simp only [smul_eq_mul, zsmul_eq_mul, Int.cast_natCast]⟩)⟩ mod p):= by
  unfold basis_radical_of_basis_radical_mod
  unfold basisSubmoduleModOfBasisMod
  erw [Basis.mk_apply]
  rfl

/-- Constructs an explicit basis for `Iₚ / pIₚ` using elements in the kernel of the iterated
  Frobenius map·  -/
noncomputable def basis_radical_of_linear_independent_ker_im [NoZeroSMulDivisors ℤ O]
    {n m j : ℕ} [Nonempty (Fin m ⊕ Fin n)] (b : Fin m → O ) (b' : Fin n → O )
    (v : Fin m → R) (v' : Fin n → R ) (hmod1 : ∀ (i : Fin m), v i = (b i mod'' p))
    (hmod2 : ∀ (j : Fin n), v' j = (b' j mod'' p)) (hlin1 : LinearIndependent (ZMod p) v)
    (hlin2 : LinearIndependent (ZMod p) (((Frob R p) ^ j : R →ₗ[ZMod p] R ) ∘ v'))
    (hker : ∀ i, ((Frob R p) ^ j) (v i) = 0) (hle : m + n ≤ p ^ j)
    (b3 : Basis (Fin (m + n)) ℤ O):
    Basis (Fin m ⊕ Fin n) (ZMod p) (Ip mod' p) := by
  have hfin_card : Fintype.card (Fin m) + Fintype.card (Fin n) = Fintype.card (Fin (m + n)) :=
  by simp only [Fintype.card_fin]
  let b1 : Basis (Fin m) (ZMod p) (Ip mod''' p) := by
    let e := LinearEquiv.ofEq _ _ (radical_eq_kernel_iter_frob O p (m + n) j b3 hle).symm
    have := (@basisKernelOfLinearIndependentKerIm R (ZMod p) _ R _ _ _ _ (Fin m) (Fin n) (Fin (m + n))
    _ _ _ hfin_card (basis_zmodp_algebra O p b3) ((Frob R p) ^ j) v v' hlin1 hlin2 hker).map e
    convert this
  have aux : ∀ i, (b1 i).1  = v i := by
    intro i
    simp only [b1, Basis.map_apply, LinearEquiv.coe_ofEq_apply]
    exact basisKernelOfLinearIndependentKerImEq_apply hfin_card (basis_zmodp_algebra O p b3)
      ((Frob R p) ^ j) v v' hlin1 hlin2 hker i
  let b2 : Basis (Fin m ⊕ Fin n) (ZMod p) R :=
  basisExtensionKernelOfLinearIndependentKerIm hfin_card
    (basis_zmodp_algebra O p b3) ((Frob R p) ^ j) v v' hlin1 hlin2 hker
  refine basis_radical_of_basis_radical_mod O p b b' b1 b2 b3 ?_ ?_ ?_
  · intro i
    rw [aux, hmod1]
  · intro i
    erw [basisExtensionKernelOfLinearIndependentKerIm_apply_inl]
    exact hmod1 i
  · intro i
    erw [basisExtensionKernelOfLinearIndependentKerIm_apply_inr]
    exact hmod2 i


lemma basis_radical_of_linear_independent_ker_im_in_b_Ip [NoZeroSMulDivisors ℤ O]
    {n m j : ℕ}[Nonempty (Fin m ⊕ Fin n)](b : Fin m → O ) (_b' : Fin n → O )
    (v : Fin m → R) (v' : Fin n → R ) (hmod1 : ∀ (i : Fin m), v i = (b i mod'' p))
    (hlin1 : LinearIndependent (ZMod p) v)
    (hlin2 : LinearIndependent (ZMod p) (((Frob R p) ^ j : R →ₗ[ZMod p] R ) ∘ v'))
    (hker : ∀ i, ((Frob R p) ^ j) (v i) = 0)
    (hle : m + n ≤ p ^ j) (b3 : Basis (Fin (m + n)) ℤ O)(i : Fin m) :
    (b i) ∈ Ip  := by
  have hfin_card : Fintype.card (Fin m) + Fintype.card (Fin n) = Fintype.card (Fin (m + n)) :=  by
    simp only [Fintype.card_fin]
  let b1 : Basis (Fin m) (ZMod p) (Ip mod''' p) := by
    let e := LinearEquiv.ofEq _ _ (radical_eq_kernel_iter_frob O p (m + n) j b3 hle).symm
    have := (@basisKernelOfLinearIndependentKerIm R (ZMod p) _ R _ _ _ _ (Fin m) (Fin n) (Fin (m + n))
    _ _ _ hfin_card (basis_zmodp_algebra O p b3) ((Frob R p) ^ j) v v' hlin1 hlin2 hker).map e
    convert this
  have heq' : ∀ i, (b1 i).1  = v i := by
    intro i
    simp only [b1, Basis.map_apply, LinearEquiv.coe_ofEq_apply]
    exact basisKernelOfLinearIndependentKerImEq_apply hfin_card
      (basis_zmodp_algebra O p b3) ((Frob R p) ^ j) v v' hlin1 hlin2 hker i
  simp_rw [hmod1] at heq'
  exact in_radical_of_in_radical_mod O p (in_radical_mod_of_mod_eq O p _ _ (heq' i))


lemma basis_radical_of_linear_independent_ker_im_def_in_Ip [NoZeroSMulDivisors ℤ O]
    {n m j : ℕ} [Nonempty (Fin m ⊕ Fin n)] (b : Fin m → O ) (b' : Fin n → O )
    (v : Fin m → R) (v' : Fin n → R ) (hmod1 : ∀ (i : Fin m), v i = (b i mod'' p))
    (hlin1 : LinearIndependent (ZMod p) v)
    (hlin2 : LinearIndependent (ZMod p) (((Frob R p) ^ j : R →ₗ[ZMod p] R ) ∘ v'))
    (hker : ∀ i, ((Frob R p) ^ j) (v i) = 0)
    (hle : m + n ≤ p ^ j) (b3 : Basis (Fin (m + n)) ℤ O) (k : (Fin m) ⊕ (Fin n)) :
    Sum.elim b (↑(p : Fin n → O) * b') k ∈ Ip := by
  cases k with
  | inl k =>
  · exact basis_radical_of_linear_independent_ker_im_in_b_Ip O p b b' v v' hmod1 hlin1 hlin2 hker hle b3 k
  | inr k =>
  · exact Ideal.le_radical ((p_smul_top' O ↑p _ ).2 ⟨b' k, rfl⟩)

local notation "ba" => basis_radical_of_linear_independent_ker_im O p

/-- An explicit description of the basis for `Iₚ / pIₚ` constructed with
 `basis_radical_of_linear_independent_ker_im` -/
lemma basis_radical_of_linear_independent_ker_im_app [NoZeroSMulDivisors ℤ O]
    {n m j : ℕ}[Nonempty (Fin m ⊕ Fin n)]
    (b : Fin m → O ) (b' : Fin n → O )(v : Fin m → R) (v' : Fin n → R )
    (hmod1 : ∀ (i : Fin m), v i = (b i mod'' p))
    (hmod2 : ∀ (j : Fin n), v' j = (b' j mod'' p))
    (hlin1 : LinearIndependent (ZMod p) v) (hlin2 : LinearIndependent (ZMod p)
    (((Frob R p) ^ j : R →ₗ[ZMod p] R ) ∘ v'))
    (hker : ∀ i, ((Frob R p) ^ j) (v i) = 0) (hle : m + n ≤ p ^ j)
    (b3 : Basis (Fin (m + n)) ℤ O)  (k : (Fin m) ⊕ (Fin n)) :
    (ba b b' v v' hmod1 hmod2 hlin1 hlin2 hker hle b3) k =
      (⟨Sum.elim b (↑(p : Fin n → O) * b') k,
      basis_radical_of_linear_independent_ker_im_def_in_Ip O p b b' v v'
        hmod1 hlin1 hlin2 hker hle b3 k⟩  mod p) := by
  cases k with
  | inl k =>
    · simp only [Pi.natCast_def, Sum.elim_inl]
      unfold basis_radical_of_linear_independent_ker_im
      simp only [id_eq, eq_mpr_eq_cast, cast_eq]
      simp_rw [basis_radical_def_left]
  | inr k =>
    · simp only [Pi.natCast_def, Sum.elim_inr]
      unfold basis_radical_of_linear_independent_ker_im
      simp only [id_eq, eq_mpr_eq_cast, cast_eq, Pi.mul_apply]
      simp_rw [basis_radical_def_right]
      simp only [zsmul_eq_mul, Int.cast_natCast]

lemma basis_radical_of_linear_independent_ker_im_in_Ip [NoZeroSMulDivisors ℤ O]
    {n m j : ℕ} [Nonempty (Fin m ⊕ Fin n)]
    (b : Fin m → O ) (b' : Fin n → O ) (v : Fin m → R) (v' : Fin n → R )
    (hmod1 : ∀ (i : Fin m), v i = (b i mod'' p))
    (hlin1 : LinearIndependent (ZMod p) v) (hlin2 : LinearIndependent (ZMod p)
    (((Frob R p) ^ j : R →ₗ[ZMod p] R ) ∘ v'))
    (hker : ∀ i, ((Frob R p) ^ j) (v i) = 0) (hle : m + n ≤ p ^ j)
    (b3 : Basis (Fin (m + n)) ℤ O)  (s : Fin m → ℤ ) (t : Fin n → ℤ ) :
     Finset.univ.sum (λ i => (s i ) • b i) + Finset.univ.sum (λ j => (t j ) • (p * b' j)) ∈ Ip  := by
  refine Ideal.add_mem _ (Ideal.sum_mem _ ?_) (Ideal.sum_mem _ ?_)
  · intros c _
    rw [zsmul_eq_mul]
    refine Ideal.mul_mem_left _ _ (basis_radical_of_linear_independent_ker_im_in_b_Ip O p b b'
      v v' hmod1 hlin1 hlin2 hker hle b3 c)
  · intros c _
    rw [zsmul_eq_mul]
    refine Ideal.mul_mem_left _ _ ?_
    exact Ideal.le_radical ((p_smul_top' O ↑p _ ).2 ⟨b' c, rfl⟩)


/-- The coordinates of the image of `∑ sᵢ • bᵢ + ∑ tⱼ • (p * b'ⱼ)` in `Iₚ / pO`
  with respect to the basis `basis_radical_of_linear_independent_ker_im`·  -/
lemma basis_radical_of_linear_independent_ker_im_in_repr [NoZeroSMulDivisors ℤ O]
    {n m j : ℕ}[Nonempty (Fin m ⊕ Fin n)]
    (b : Fin m → O ) (b' : Fin n → O )(v : Fin m → R) (v' : Fin n → R )
    (hmod1 : ∀ (i : Fin m), v i = (b i mod'' p))
    (hmod2 : ∀ (j : Fin n), v' j = (b' j mod'' p))
    (hlin1 : LinearIndependent (ZMod p) v) (hlin2 : LinearIndependent (ZMod p)
    (((Frob R p) ^ j : R →ₗ[ZMod p] R ) ∘ v'))
    (hker : ∀ i, ((Frob R p) ^ j) (v i) = 0) (hle : m + n ≤ p ^ j)
    (b3 : Basis (Fin (m + n)) ℤ O) (s : Fin m → ℤ ) (t : Fin n → ℤ ):
    (algebraMap ℤ (ZMod p)) ∘ Sum.elim s t =
    ((ba b b' v v' hmod1 hmod2 hlin1 hlin2 hker hle b3).repr
    (( ⟨ Finset.univ.sum (λ i => (s i ) • b i) + Finset.univ.sum (λ j => (t j ) • (p * b' j)) ,
      basis_radical_of_linear_independent_ker_im_in_Ip O p b b' v v' hmod1 hlin1 hlin2 hker hle b3 s t ⟩ : Ip) mod p) )  := by
  have aux1: ∀ i, b i ∈ Ip :=
    basis_radical_of_linear_independent_ker_im_in_b_Ip O p b b' v v' hmod1 hlin1 hlin2 hker hle b3
  have aux2 : ∀ j, ↑p * (b' j) ∈ Ip := by
    intro j
    exact Ideal.le_radical ((p_smul_top' O ↑p _ ).2 ⟨b' j, rfl⟩)
  have aux3 : (( ⟨ Finset.univ.sum (λ i => (s i ) • b i) +
    Finset.univ.sum (λ j => (t j ) • (p * b' j)) , basis_radical_of_linear_independent_ker_im_in_Ip
      O p b b' v v' hmod1 hlin1 hlin2 hker hle b3 s t ⟩ : Ip) mod p ) =
    Finset.univ.sum (λ i => (↑(s i  : ZMod p) • (⟨b i, aux1 i ⟩ mod p ))) +
      Finset.univ.sum (λ j => (↑(t j  : ZMod p) • (⟨ p * b' j, aux2 j ⟩ mod p) ) ) := by
    simp_rw [← zsmul_eq_zmod_smul, ← Submodule.mkQ_apply]
    rw [← map_sum, ← map_sum, ← map_add]
    congr
    simp only [zsmul_eq_mul, AddSubmonoidClass.coe_finset_sum,
      Submodule.coe_toAddSubmonoid, Submodule.coe_smul_of_tower]
    simp
  have aux4 : Finset.univ.sum (λ i => (↑(s i  : ZMod p) • (⟨b i, aux1 i ⟩ mod p ))) +
    Finset.univ.sum (λ j => (↑(t j  : ZMod p) • (⟨ p * b' j, aux2 j ⟩ mod p) ) ) =
      Finset.univ.sum (λ (k : (Fin m) ⊕ (Fin n)) => ( ↑(((algebraMap ℤ (ZMod p)) ∘ Sum.elim s t) k) •
        ((ba b b' v v' hmod1 hmod2 hlin1 hlin2 hker hle b3) k)) ) := by
    simp only [algebraMap_int_eq, Int.coe_castRingHom, Function.comp_apply,
      Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr]
    congr
    · ext
      unfold basis_radical_of_linear_independent_ker_im
      simp only [id_eq, eq_mpr_eq_cast, cast_eq]
      simp_rw [basis_radical_def_left ]
    · ext
      unfold basis_radical_of_linear_independent_ker_im
      simp only [id_eq, eq_mpr_eq_cast, cast_eq, Pi.mul_apply]
      simp_rw [basis_radical_def_right ]
      simp only [zsmul_eq_mul, Int.cast_natCast]
  rw [aux3, aux4]
  symm
  exact Basis.repr_sum_self _ _

--------------------------------------------------------------------
-- Construction of the linear map `O / pO → ((Iₚ / pIₚ) → (Iₚ / pIₚ))`

/-- The map `Iₚ → Iₚ / pIₚ ` sending `β ↦ α * β` -/
def mul_α_aux (α : O) : Ip → (Ip mod' p) :=
  λ β => (⟨ (α * β.val), Ideal.mul_mem_left _ α β.2 ⟩ : Ip)  mod p

omit hpI [Nontrivial O] [Module.Free ℤ O] in
lemma mul_α_aux_def (α : O) (β : Ip) : (mul_α_aux O p α ) β  =
  ((⟨ (α * β.val), Ideal.mul_mem_left _ α β.2 ⟩ : Ip)  mod p ) := rfl

omit hpI [Nontrivial O] [Module.Free ℤ O] in
lemma mul_α_aux_map_add {α : O} {β γ : Ip} :
  (mul_α_aux O p α) (β + γ) = (mul_α_aux O p α) β + (mul_α_aux O p α) γ := by
  rw [mul_α_aux_def, mul_α_aux_def, mul_α_aux_def, ← Submodule.Quotient.mk_add]
  simp only [AddMemClass.coe_add]
  congr
  ring

/-- The lift of `mul_α_aux` to a map  `Iₚ / pIₚ → Iₚ / pIₚ `· -/
def map_mul_α (α : O) : (Ip mod' p) → (Ip mod' p) := by
  refine @Quotient.lift _ _ (Submodule.quotientRel ((p : ℤ ) • (⊤ : Submodule ℤ Ip ))) (mul_α_aux O p α) ?_
  intros a b hab
  have := (@Submodule.quotientRel_def _ _ _ _ _ ((p : ℤ ) • (⊤ : Submodule ℤ Ip )) a b).1 hab
  erw [Submodule.Quotient.eq ((p : ℤ )  • (⊤ : Submodule ℤ Ip ))]
  have aux1 : α * a - α * b  ∈ Ip := by
    exact Ideal.sub_mem _  (Ideal.mul_mem_left _ _ a.2) (Ideal.mul_mem_left _ _ b.2)
  have aux2 : (⟨α * a - α * b, aux1 ⟩ : Ip) ∈ ((p : ℤ )  • (⊤ : Submodule ℤ Ip )) := by
    simp_rw [← mul_sub]
    obtain ⟨i, _, hip⟩ := this
    simp only [DistribMulAction.toLinearMap_apply, natCast_zsmul] at hip
    norm_cast
    simp_rw [← hip]
    simp only [Submodule.coe_smul_of_tower, nsmul_eq_mul]
    simp_rw [← mul_assoc]
    use ⟨α * i, ?_⟩
    constructor
    · simp only [Submodule.top_coe, Set.mem_univ]
    · rw [←Subtype.coe_inj ]
      simp only [DistribMulAction.toLinearMap_apply, natCast_zsmul,
        Submodule.coe_smul_of_tower, nsmul_eq_mul]
      ring
      · exact Ideal.mul_mem_left _ _ i.2
  convert aux2

omit hpI [Nontrivial O] [Module.Free ℤ O] in
lemma map_mul_α_aux2 (α : O) (β : Ip) :
  (map_mul_α O p α) (β mod p) = (mul_α_aux O p α ) β := rfl

/-- The map `map_mul_α ` as a linear map· -/
def mul_α (α : O) : (Ip mod' p) →ₗ[(ZMod p)] (Ip mod' p) where
  toFun := map_mul_α O p α
  map_add' := by
    rintro ⟨a, ha⟩ ⟨b , hb⟩
    erw [← Submodule.Quotient.mk_add ]
    simp only [map_mul_α_aux2]
    refine mul_α_aux_map_add _ _
  map_smul' := by
    rintro r ⟨a, ha⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, RingHom.id_apply]
    have aux : ((r.val : ℤ) : ZMod p) = r := by
      simp only [ZMod.natCast_val, ZMod.intCast_cast,
      ZMod.cast_id', id_eq]
    erw [← aux, ← zsmul_eq_zmod_smul, map_mul_α_aux2, map_mul_α_aux2]
    rw [mul_α_aux_def] ;  erw [mul_α_aux_def, ← zsmul_eq_zmod_smul]
    congr
    simp only [Submodule.coe_smul_of_tower, zsmul_eq_mul,
      ZMod.intCast_cast, Submodule.coe_toAddSubgroup]
    ring

omit [Nontrivial O] [Module.Free ℤ O] in
lemma map_mul_α_def (α : O) (β : Ip) :
  (mul_α O p α) (β mod p) = (mul_α_aux O p α ) β := rfl

/-- The map sending `O` to an endomorphism of `Iₚ / pIₚ`· -/
def map_to_end : O → ((Ip mod' p)  →ₗ[(ZMod p)] (Ip mod' p)) :=
  λ (α : O) => mul_α O p α

omit [Nontrivial O] [Module.Free ℤ O] in
lemma map_to_end_eq (a : O) : map_to_end O p a = mul_α O p a := rfl

omit [Nontrivial O] [Module.Free ℤ O] in
lemma map_to_end_eq_zero (t : O) : map_to_end O p (↑p * t) = 0 := by
  rw [map_to_end_eq ]
  apply LinearMap.ext
  rintro ⟨β, hb⟩
  simp only [Submodule.Quotient.quot_mk_eq_mk, LinearMap.zero_apply]
  rw [map_mul_α_def, mul_α_aux_def, Submodule.Quotient.mk_eq_zero ]
  use ⟨t * β, ?_⟩
  constructor
  · simp only [Submodule.top_coe, Set.mem_univ]
  · rw [←Subtype.coe_inj ]
    simp only [DistribMulAction.toLinearMap_apply,
    natCast_zsmul, Submodule.coe_smul_of_tower, nsmul_eq_mul]
    ring
    · exact Ideal.mul_mem_left _ _ hb

omit [Nontrivial O] [Module.Free ℤ O] in
lemma map_to_end_zero :  map_to_end O p 0 = 0 := by
   rw [← mul_zero (↑p : O)]
   exact map_to_end_eq_zero O p 0

omit [Nontrivial O] [Module.Free ℤ O] in
lemma map_to_end_add (a b : O) :
    map_to_end O p (a + b) = (map_to_end O p a) + (map_to_end O p b) := by
  repeat erw [map_to_end_eq]
  apply LinearMap.ext
  rintro ⟨β, hb⟩
  simp only [Submodule.Quotient.quot_mk_eq_mk, LinearMap.add_apply]
  erw [map_mul_α_def, mul_α_aux_def, ← Submodule.Quotient.mk_add]
  congr
  ring

omit [Nontrivial O] [Module.Free ℤ O] in
/-- The lift of `map_to_end` to a map from `O / pO` to an endomorphism of `Iₚ / pIₚ` -/
def map_to_end_mod : R → (((Ip mod' p)  →ₗ[(ZMod p)] (Ip mod' p))) := by
  apply @Quotient.lift _ _ (Submodule.quotientRel ((p : O) • (⊤ : Submodule O O)) ) (map_to_end O p)
  intros a b hab
  have := (@Submodule.quotientRel_def _ _ _ _ _ ((p : O) • (⊤ : Submodule O O)) a b).1 hab
  obtain ⟨t, ht⟩ := (p_smul_top' O _ _).1
    ((Submodule.quotientRel_def ((p : O) • (⊤ : Submodule O O))).1 hab)
  replace ht := eq_add_of_sub_eq  ht.symm
  rw [ht, map_to_end_add, map_to_end_eq_zero, zero_add ]

omit [Nontrivial O] [Module.Free ℤ O] in
lemma map_to_end_mod_def {x : O} :
    map_to_end_mod O p ((Ideal.Quotient.mk ((p : O) • (⊤ : Submodule O O))) x)
  = (map_to_end O p) x := rfl

omit [Nontrivial O] [Module.Free ℤ O] in
lemma map_add' {x y : R} :
    map_to_end_mod O p (x + y) = map_to_end_mod O p x +  map_to_end_mod O p y := by
  rcases x with ⟨a⟩
  rcases y with ⟨b⟩
  erw [← Submodule.Quotient.mk_add]
  erw [ map_to_end_mod_def O p, map_to_end_mod_def O p, map_to_end_mod_def O p]
  exact map_to_end_add O p _ _

-- Shortcut instances to avoid timeouts
instance : DistribMulAction (ZMod p) (Ip mod' p) := inferInstance
instance : SMulCommClass (ZMod p) (ZMod p) (Ip mod' p) := inferInstance

omit [Nontrivial O] [Module.Free ℤ O] in
lemma map_smul' {r : ZMod p} {x : R} :
    map_to_end_mod O p (r • x) = r • (map_to_end_mod O p x) := by
  rcases x with ⟨a⟩
  dsimp [Submodule.Quotient.quot_mk_eq_mk]
  refine LinearMap.ext ?_
  rintro ⟨b⟩
  rw [map_to_end_mod_def, LinearMap.smul_apply, map_to_end_eq]
  erw [map_mul_α_def, map_mul_α_def, mul_α_aux_def, mul_α_aux_def, zmodp_smul_def,  ]
  simp only [Submodule.Quotient.quot_mk_eq_mk, nsmul_eq_mul, ZMod.natCast_val]
  congr
  simp only [Submodule.coe_toAddSubgroup, AddSubmonoidClass.mk_nsmul, nsmul_eq_mul, ZMod.natCast_val]
  ring

/-- The map `map_to_end_mod` as a linear map· -/
def map_to_end_lin : R →ₗ[(ZMod p)] ((Ip mod' p) →ₗ[ZMod p] (Ip mod' p)) where
  toFun := map_to_end_mod O p
  map_add' := by { intro x y ; exact map_add' O p }
  map_smul' := by { intro r x  ; exact map_smul' O p }

omit [Nontrivial O] [Module.Free ℤ O] in
lemma map_to_end_lin_def (x : R) : map_to_end_lin O p x = map_to_end_mod O p x := rfl

omit [Nontrivial O] [Module.Free ℤ O] in
lemma mul_ideal_in_p_mul_of_kernel (α : O) :
    (α mod'' p) ∈ LinearMap.ker (map_to_end_lin O p) ↔
    ∀ (x : O), x ∈ Ip → (∃ (j : O), j ∈ Ip ∧ α * x = p * j ) := by
  rw [LinearMap.mem_ker, map_to_end_lin_def O p, map_to_end_mod_def O p, map_to_end_eq  O p]
  constructor
  · intros ha x hx
    have :  (mul_α O p α) ((⟨x, hx⟩ : Ip)  mod p) = 0 := by
      simp only [ha, LinearMap.zero_apply]
    rw [map_mul_α_def, mul_α_aux_def,Submodule.Quotient.mk_eq_zero ] at this
    choose j _ hj2 using this
    simp only [DistribMulAction.toLinearMap_apply, natCast_zsmul, Subtype.ext_iff_val] at hj2
    use j
    rw [← nsmul_eq_mul, ← hj2]
    constructor
    · simp only [Submodule.coe_mem]
    · simp only [Submodule.coe_smul_of_tower, nsmul_eq_mul]
  · intro h
    apply LinearMap.ext
    rintro ⟨x⟩
    dsimp [Submodule.Quotient.quot_mk_eq_mk]
    simp_rw [map_mul_α_def]
    rw [mul_α_aux_def, Submodule.Quotient.mk_eq_zero]
    obtain ⟨j, hj1, hj2⟩ := h x.1 x.2
    simp_rw [hj2]
    use ⟨j, ?_⟩
    constructor
    . simp only [Submodule.top_coe, Set.mem_univ]
    . dsimp
      rw [← Subtype.coe_inj]
      simp only [natCast_zsmul, Submodule.coe_smul_of_tower, nsmul_eq_mul]
      · exact hj1

omit [Nontrivial O] in
/-- If `Iₚ = pO`, then the kernel of `map_to_end_mod` is trivial· -/
lemma ker_map_to_end_lin_eq_bot_of_rad_eq_smul
    (hradeq : Ip = (p : O) • (⊤ : Submodule O O)) :
    LinearMap.ker (map_to_end_lin O p) = ⊥ := by
  rw [← le_bot_iff]
  intro x hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
  rw [← ha, mul_ideal_in_p_mul_of_kernel, hradeq] at hx
  obtain ⟨j ,hj1, hj2⟩ := hx (p : O) (by use 1 ; simp only [Submodule.top_coe, Set.mem_univ,
    DistribMulAction.toLinearMap_apply, smul_eq_mul, mul_one, and_self])
  rw [mul_comm, ← nsmul_eq_mul, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ, smul_right_inj] at hj2
  rw [← ha]
  simp only [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, hj2, hj1]
  exact NeZero.natCast_ne p ℤ

omit [Nontrivial O] [Module.Free ℤ O] in
/-- A way to certify that the kernel of `map_to_end_lin` is trivial by, essentially,
  looking at the entries of the matrix representations of the image of a tuple `v`
  of elements in `O`· -/
lemma ker_map_to_end_lin_eq_bot_of_mul_ne_zero' {τ₁ τ₂: Type*} [Fintype τ₁] [Fintype τ₂]
    (v : τ₁ → O ) (w : τ₂ → O)
    (br : Basis τ₁ (ZMod p) R) (b : Basis τ₂ (ZMod p) (Ip mod' p)) (hw' : ∀ i, w i  ∈ Ip  )
    (heq2 : ∀ i, b i = (⟨w i, (hw' i)⟩  mod p)) :
    (∀ i, (∃ j k,  b.repr (⟨(v i) * (w j), Ideal.mul_mem_left _ _ (hw' j) ⟩ mod p) k ≠ 0
    ∧ (∀ l, l ≠ i →  b.repr (⟨(v l) * (w j), Ideal.mul_mem_left _ _ (hw' j) ⟩ mod p) k = 0 ) )  )
  → LinearMap.ker (map_to_end_lin O p) = ⊥ := by
  intro h
  set v' := λ i => v i mod'' p
  refine ker_eq_bot_of_linearMap_to_linearMaps (map_to_end_lin O p) br b b v' ?_
  simp only [v']
  simp_rw [Function.comp_apply, map_to_end_lin_def, map_to_end_mod_def,
  map_to_end_eq, heq2, map_mul_α_def, mul_α_aux_def ]
  exact h

omit [Nontrivial O] [Module.Free ℤ O] in
/-- A way to certify that the kernel of `map_to_end_lin` is trivial by
  looking at the image of a tuple `v` of elements in `O`, and evaluating the
  endomorphisms at an element `w` in `Iₚ /pIₚ ` · -/
lemma ker_map_to_end_lin_eq_bot_of_mul_ne_zero_of_single_eval {τ₁ τ₂: Type*} [Fintype τ₁]
  [Fintype τ₂] (v : τ₁ → O ) (w : O) (hw : w ∈ Ip )
    (br : Basis τ₁ (ZMod p) R) (b : Basis τ₂ (ZMod p) (Ip mod' p))
    (hi : ∀ (i : τ₁) , (∃ (j : τ₂) , b.repr (⟨(v i) * w, Ideal.mul_mem_left _ _ hw ⟩ mod p) j ≠ 0
    ∧ (∀ (k : τ₁), k ≠ i → b.repr (⟨(v k) * w, Ideal.mul_mem_left _ _ hw ⟩ mod p) j = 0 ) ) ) :
  LinearMap.ker (map_to_end_lin O p) = ⊥ := by
  set v' := λ i => v i mod'' p
  refine ker_eq_bot_of_linearMap_to_linearMaps_eval (map_to_end_lin O p) br b v' (⟨w, hw⟩ mod p) ?_
  simp only [v']
  simp_rw [Function.comp_apply, map_to_end_lin_def, map_to_end_mod_def, map_to_end_eq,
  map_mul_α_def, mul_α_aux_def ]
  exact hi


end PartIV


variable {K : Type*} [CommRing K] [NoZeroSMulDivisors ℤ K]
variable (O : Subalgebra ℤ K) (p : ℕ) [hpI : Fact $ Nat.Prime p]


local notation "Ip" => Ideal.radical (Ideal.span {(p : O)} )
local notation I "mod'" p =>  I ⧸ ((p : ℤ ) • (⊤ : Submodule ℤ I ) )
local notation x "mod" p => (@Submodule.Quotient.mk ℤ Ip _ _ _ ((p : ℤ ) • (⊤ : Submodule ℤ Ip ))) x
local notation "R" =>  O ⧸ Ideal.span {(p : O)}
local notation x "mod''" p => (Ideal.Quotient.mk (Ideal.span {(p : O)} )) x


/-- If the kernel of `map_to_end_lin` is trivial, then `O` equals the multiplier ring of `Iₚ`·  -/
theorem mult_ring_eq_ring_of_trivial_ker_map_to_end_lin
    (hk : LinearMap.ker (map_to_end_lin O p) = ⊥ ) :
    O = multiplierRing Ip := by
refine le_antisymm (subalgebra_le_multiplierRing Ip) ?_
· intros α ha
  rw [multiplierRing_mem] at ha
  have hpsmul : p • α ∈ O := by
    obtain ⟨j, _, hj2⟩ := ha (p : O) (by {use 1 ; rw [pow_one] ;  exact Ideal.mem_span_singleton_self (p : O) })
    rw [nsmul_eq_mul]
    erw [hj2]
    simp only [SetLike.coe_mem]
  have hmem : ∀ (x : O), x ∈ Ip → (∃ (j : O), j ∈ Ip ∧ (⟨(p • α), hpsmul⟩ : O) * x = p * j ) := by
    intros x hx
    obtain ⟨j, hj1, hj2⟩ := ha x hx
    refine ⟨j, hj1, ?_⟩
    rw [← Subtype.val_inj]
    simp only [nsmul_eq_mul, MulMemClass.coe_mul, Subsemiring.coe_toSubmonoid, Subalgebra.coe_toSubsemiring,
      SubringClass.coe_natCast]
    rw [← hj2]
    ring
  rw [ideal_span_eq_smul_top] at hmem
  have := ( mul_ideal_in_p_mul_of_kernel O p ⟨(p • α), hpsmul⟩ ).2 hmem
  simp only [nsmul_eq_mul, hk, Submodule.mem_bot] at this
  erw [Submodule.Quotient.mk_eq_zero, ← ideal_span_eq_smul_top, Ideal.mem_span_singleton] at this
  choose k hk using this
  rw [← Subtype.val_inj] at hk
  simp only [MulMemClass.coe_mul, Subsemiring.coe_toSubmonoid, Subalgebra.coe_toSubsemiring, SubringClass.coe_natCast] at hk
  rw [← Int.cast_natCast, ← zsmul_eq_mul,  ← zsmul_eq_mul, smul_right_inj] at hk
  rw [hk] ; refine SetLike.coe_mem _
  exact NeZero.natCast_ne p ℤ

variable {Om : Subalgebra ℤ K}(hm : O ≤ Om) {ι : Type* } [Fintype ι]

local notation "O*" => Subalgebra.toSubmodule (AlgHom.range (Subalgebra.inclusion hm))

/-- If the kernel of `map_to_end_lin` is trivial, then `O` is `p`-maximal· -/
lemma p_maximal_of_trivial_ker_map_to_end_lin [Module.Free ℤ Om] [Module.Finite ℤ Om]
    (heqr : Module.rank ℤ O = Module.rank ℤ Om)
    (hker : LinearMap.ker (map_to_end_lin O p) = ⊥) : piMaximal (p : ℤ) O* := by
  refine order_piMaximal_of_order_eq_multiplierRing hm (Nat.prime_iff_prime_int.mp hpI.out) heqr ?_
  have : (algebraMap ℤ O p) = (p : O) := by norm_num
  rw [this]
  exact mult_ring_eq_ring_of_trivial_ker_map_to_end_lin O p hker
