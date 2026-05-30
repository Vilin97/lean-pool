/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.AlgebraAuxiliaryLemmas
import LeanPool.RingOfIntegersProject.LinearAlgebraAuxiliaryLemmas
import LeanPool.RingOfIntegersProject.PolynomialsAsLists
import LeanPool.RingOfIntegersProject.TimesTable.Defs
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.IsAdjoinRoot

/-!
# Subalgebra Builder for Adjoin Root

Here we introduce a structure called `SubalgebraBuilder`.
Let `R` be a ring and `Q` its field of fractions· Let `K` be a `Q`-algebra constructed by
adjoining a root of a polynomial· Given a basis for an `R`-subalgebra of `K` in
upper triangular form, together with the certifying data of its multiplication table,
with the structure `SubalgebraBuilder` we construct the corresponding subalgebra of `K`.
We also give an expression for the discriminant of this subalgebra.


## Main definitions:
- `SubalgebraBuilder` : builds a subalgebra from an `R`-basis
- `SubalgebraBuilderLists` : a version of `SubalgebraBuilder` using
  lists for polynomial arithmetic.
-

## Main results:
- `OfBuilderList_discr_eq_prod_discr'` : an expression for the discriminant of the
  subalgebra constructed with `SubalgebraBuilderLists` in terms of the discriminant
  of a power basis· -/


open Module BigOperators Pointwise Polynomial

lemma TimesTable.coord_basis_of_equivFun {R M : Type*} {n : ℕ} [CommRing R] [CommRing M]
    [Module R M] (Ba : Basis (Fin n) R M)
    (T : TimesTable (Fin n) R M) (h : T.basis = Ba) {f : Fin n → R} :
    T.coord ((Ba.equivFun.symm).toFun f) = f := by
  unfold TimesTable.coord
  erw [h, LinearEquiv.toFun_eq_coe, Basis.equivFun_symm_eq_repr_symm']
  simp

section PartI

variable {Q K : Type*} [Field Q] [CommRing K] [Algebra Q K]
  {R ι : Type*} [Fintype ι] [CommRing R] [Algebra R Q] [Algebra R K] [IsScalarTower R Q K]

variable (T : Q[X]) (h : IsAdjoinRoot K T)

lemma mul_poly_eq_poly_of_poly (p q r s : Q[X])
    (hp : p * q = r - T * s) :
  h.map p * h.map q = h.map r := by
  rw [← map_mul, hp]
  simp only [map_sub, map_mul, IsAdjoinRoot.map_self, zero_mul, sub_zero]

variable (b : ι → Q[X]) (s : ι → ι → Q[X]) (a : ι → ι → ι → R)
  (hc : ∀ i j, (b i) * (b j) = ∑ k, (C (algebraMap R Q (a i j k))) * (b k) - T * (s i j))

include hc in
lemma mul_is_closed (i j : ι) :
    h.map (b i) * h.map (b j) ∈ Submodule.span R (Set.range (fun i => h.map (b i))) := by
  specialize hc i j
  apply_fun h.map at hc
  simp only [map_mul, map_sub, map_sum, IsAdjoinRoot.map_self, zero_mul, sub_zero] at hc
  have : ∀ (t : Q), h.map (C t) = algebraMap Q K t :=
  fun t => (IsAdjoinRoot.algebraMap_apply h t).symm
  simp_rw [this, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def] at hc
  rw [hc]
  apply Submodule.sum_mem
  intro c _
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self c)

variable (j : ι) (hone : b j = 1)

/-- Imported declaration. -/
def subalgebraOfPolys : Subalgebra R K := by
  refine Submodule.toSubalgebra (Submodule.span R (Set.range (fun i => h.map (b i)))) ?_ ?_
  · rw [← map_one (f := h.map), ← hone]
    exact Submodule.subset_span (Set.mem_range_self j)
  · rw [span_closed_multiplication_iff_closed_mul_mems']
    exact mul_is_closed T h b s a hc

lemma subalgebraOfPolys_mem (i : ι) : h.map (b i) ∈ subalgebraOfPolys T h b s a hc j hone := by
  unfold subalgebraOfPolys
  simp only [Submodule.mem_toSubalgebra]
  exact Submodule.subset_span (Set.mem_range_self _)

local notation "O" =>  subalgebraOfPolys T h b s a hc j hone

lemma subalgebraOfPolys_linearIndependent [IsFractionRing R Q]
    (hlin : LinearIndependent Q (fun i => h.map (b i))) :
    LinearIndependent R  (fun i => (⟨ h.map (b i),
      subalgebraOfPolys_mem T h b s a hc j hone i⟩ : O)) := by
  have : Subtype.val ∘ (fun i => (⟨ h.map (b i), subalgebraOfPolys_mem T h b s a hc j hone i⟩ : O))
    = (fun i => h.map (b i)) := by rfl
  apply LinearIndependent.of_comp (SMulMemClass.subtype O)
  rw [SMulMemClass.coe_subtype, this, LinearIndependent.iff_fractionRing R Q]
  exact hlin

lemma subalgebraOfPolys_top_le :
    ⊤ ≤ Submodule.span R (Set.range (fun i => (⟨ h.map (b i),
      subalgebraOfPolys_mem T h b s a hc j hone i⟩ : O))) := by
  have : Function.Injective (SMulMemClass.subtype O) := by
    rw [SMulMemClass.coe_subtype]
    exact Subtype.coe_injective
  rw [← Submodule.map_le_map_iff_of_injective this, ← Submodule.span_image]
  have aux : Subtype.val '' (Set.range (fun i => (⟨ h.map (b i),
    subalgebraOfPolys_mem T h b s a hc j hone i⟩ : O))) = Set.range (fun i => h.map (b i)) := by
    rw [← Set.range_comp]
    rfl
  erw [aux, Submodule.map_top]
  intros x hx
  rw [← SetLike.mem_coe, LinearMap.coe_range, SMulMemClass.coe_subtype, Subtype.range_coe_subtype,
      Set.mem_setOf_eq, ← Subalgebra.mem_carrier] at hx
  rw [← SetLike.mem_coe]
  convert hx

/-- Imported declaration. -/
noncomputable def basisSubalgebraOfPolys [IsFractionRing R Q]
    (hlin : LinearIndependent Q (fun i => h.map (b i))) :
    Basis ι R O := by
  refine Basis.mk (subalgebraOfPolys_linearIndependent T h b s a hc j hone hlin)
    (subalgebraOfPolys_top_le T h b s a hc j hone)

lemma basisSubalgebraOfPolys_apply [IsFractionRing R Q]
    (hlin : LinearIndependent Q (fun i => h.map (b i)))
    (i : ι) :
    (basisSubalgebraOfPolys T h b s a hc j hone hlin) i =
      (⟨ h.map (b i), subalgebraOfPolys_mem T h b s a hc j hone i⟩ : O) := by
    unfold basisSubalgebraOfPolys
    simp only [Basis.coe_mk]

variable [IsFractionRing R Q] (hlin : LinearIndependent Q (fun i => h.map (b i)))

local notation "Ba" => basisSubalgebraOfPolys T h b s a hc j hone hlin

lemma basisSubalgebraOfPolysTable (i i' k : ι) :
    Basis.repr Ba (Ba i * Ba i') k = a i i' k := by
  simp only [basisSubalgebraOfPolys_apply, MulMemClass.mk_mul_mk, ← map_mul, hc i i']
  simp only [map_sub, map_sum, map_mul, IsAdjoinRoot.map_self, zero_mul, sub_zero]
  rw [← congr_fun (Basis.repr_sum_self Ba (a i i')) k]
  refine congr_fun ?_ k
  simp only [DFunLike.coe_fn_eq]
  refine congr_arg _ ?_
  simp_rw [basisSubalgebraOfPolys_apply, ← Subtype.val_inj]
  simp only [SetLike.mk_smul_mk, ← Subalgebra.val_apply]
  simp only [map_sum, Subalgebra.coe_val]
  have : ∀ x, h.map (C ((algebraMap R Q) (a i i' x))) * h.map (b x) =  a i i' x • h.map (b x) := by
    intro x
    rw [← IsAdjoinRoot.algebraMap_apply, ← Algebra.smul_def]
    simp only [algebraMap_smul]
  simp_rw [this]

end PartI

section IntPoly

variable {Q K : Type*} [Field Q] [CommRing K] [Algebra Q K]
{R ι : Type*} [Fintype ι] [CommRing R] [Algebra R Q] [Algebra R K] [IsScalarTower R Q K]


variable
  (T : R[X])
  (B : ι → R[X]) (d : R) (hd : d ≠ 0) (s : ι → ι → R[X]) (a : ι → ι → ι → R)
  (hc : ∀ i j, (B i) * (B j) = ∑ k, (C (d * (a i j k))) * (B k) - T * (s i j))

include hd

lemma algebra_map_d_ne_zero [IsFractionRing R Q] : ((algebraMap R Q) d)⁻¹ ≠ 0 :=
  inv_ne_zero ((map_ne_zero_iff (algebraMap R Q) (IsFractionRing.injective R Q)).mpr hd)

local notation "b" => fun i => C (algebraMap R Q d)⁻¹ * map (algebraMap R Q) (B i)
local notation "s'" => fun i j => (C (algebraMap R Q d)⁻¹) ^ 2 * map (algebraMap R Q) (s i j)

include hc

lemma poly_identities_aux [IsFractionRing R Q] (i j : ι) :
  (b i) * (b j) =
    ∑ k, (C (algebraMap R Q (a i j k))) *
      ((fun i => C (algebraMap R Q d)⁻¹ * map (algebraMap R Q) (B i)) k) - (map (algebraMap R Q) T)
        * (s' i j) := by
  have : algebraMap R Q d ≠ 0 := (map_ne_zero_iff (algebraMap R Q) (IsFractionRing.injective R
    Q)).mpr hd
  dsimp
  rw [mul_assoc, mul_comm (C (algebraMap R Q d)⁻¹) _,
  mul_comm (C (algebraMap R Q d)⁻¹) _, ← mul_assoc, ← Polynomial.map_mul, hc i j]
  simp only [map_mul, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_sum]
  rw [mul_assoc, sq, sub_mul, mul_comm, mul_assoc, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · congr
    refine funext ?_
    intro l
    rw [Polynomial.map_C, mul_assoc (C ((algebraMap R Q) d)) _ (map (algebraMap R Q) (B l)),
      ← mul_assoc (C ((algebraMap R Q) d)⁻¹) (C ((algebraMap R Q) d)) _, ←Polynomial.C_mul,
        inv_mul_cancel₀ this]
    simp only [map_one, map_C, one_mul]
    ring
  · ring

variable (h : IsAdjoinRoot K (map (algebraMap R Q) T)) (j : ι) (honed : B j = C d)

include honed

omit [Fintype ι] hc in
lemma hone_aux [IsFractionRing R Q] : b j = 1 := by
  have : algebraMap R Q d ≠ 0 := (map_ne_zero_iff (algebraMap R Q) (IsFractionRing.injective R
    Q)).mpr hd
  simp_rw [honed, Polynomial.map_C, ←Polynomial.C_mul]
  rw [inv_mul_cancel₀ _, map_one]
  exact this

/-- Imported declaration. -/
noncomputable def subalgebraOfPolysInt [IsFractionRing R Q] : Subalgebra R K := by
  have : algebraMap R Q d ≠ 0 := (map_ne_zero_iff (algebraMap R Q) (IsFractionRing.injective R
    Q)).mpr hd
  refine subalgebraOfPolys (R := R) (map (algebraMap R Q) T) h b s' a ?_ j ?_
  · exact poly_identities_aux T B d hd s a hc
  · exact hone_aux _ _ hd _ honed

local notation "O" => subalgebraOfPolysInt T B d hd s a hc h j honed

lemma subalgebraOfPolysInt_mem [IsFractionRing R Q] (i : ι) :
  h.map (b i) ∈ O := by
  unfold subalgebraOfPolysInt
  unfold subalgebraOfPolys
  simp only [Submodule.mem_toSubalgebra]
  exact Submodule.subset_span (Set.mem_range_self _)

variable (hlin : LinearIndependent Q (fun i => h.map (map (algebraMap R Q) (B i))))

example {q : Q} (h : q ≠ 0) :IsUnit q := by
  exact Ne.isUnit h

/-- Imported declaration. -/
noncomputable def basisSubalgebraOfPolysInt [IsFractionRing R Q] :
  Basis ι R O := by
  refine basisSubalgebraOfPolys (R := R) (map (algebraMap R Q) T) h b s' a
    (poly_identities_aux T B d hd s a hc) j (hone_aux B d hd j honed) ?_
  simp only [map_mul, ← IsAdjoinRoot.algebraMap_apply]
  simp_rw [← Algebra.smul_def]
  convert LinearIndependent.units_smul hlin (fun _ => IsUnit.unit (Ne.isUnit (algebra_map_d_ne_zero
    d hd)))

local notation "BB" => basisSubalgebraOfPolysInt T B d hd s a hc h j honed hlin

lemma basisSubalgebraOfPolysInt_apply [IsFractionRing R Q] (i : ι) :
   BB i = ⟨ h.map (b i), subalgebraOfPolysInt_mem T B d hd s a hc h j honed i⟩ := by
  exact basisSubalgebraOfPolys_apply (R := R) (map (algebraMap R Q) T) h b s' a _ _ _ _ i

lemma basisSubalgebraOfPolysIntTable [IsFractionRing R Q] (i i' k : ι) :
    Basis.repr BB (BB i * BB i') k = a i i' k := by
  exact basisSubalgebraOfPolysTable (R := R) (map (algebraMap R Q) T) h b s' a _ _ _ _ i i' k

end IntPoly


section LinInd

variable {Q K : Type*} [Field Q] [CommRing K] [Algebra Q K]
{R : Type*} [CommRing R] [Algebra R Q] [Algebra R K] [IsScalarTower R Q K]

variable
  {n : ℕ}
  (c : Matrix (Fin n) (Fin n) R)

lemma is_det_ne_zero_of_upper_triangular [IsDomain R] (hc : ∀ i j, j < i → c i j = 0)
  (hin : ∀ i, c i i ≠ 0) :
  c.det ≠ 0 := by
have : Matrix.BlockTriangular c id := by
  intro i j
  simp only [id_eq]
  exact hc i j
rw [Matrix.det_of_upperTriangular this, Finset.prod_ne_zero_iff]
simp only [Finset.mem_univ, ne_eq, forall_true_left]
exact hin

variable
  (B : Fin n → R[X])
  (hpoly : ∀ j, B j = ∑ i : Fin n, C (c i j) * X ^ (i : ℕ))
  (T : R[X])
  (hm : Monic T)
  (hdeg : T.natDegree = n)
  (hdet : c.det ≠ 0)
  (h : IsAdjoinRoot K (map (algebraMap R Q) T))

include hm hdeg hpoly hdet in
lemma linearIndependentOfUpperTriangular [IsFractionRing R Q] :
  LinearIndependent Q (fun i => h.map (map (algebraMap R Q) (B i))) := by
  have heq : (map (algebraMap R Q) T).natDegree = n := by
    rw [Polynomial.Monic.natDegree_map hm (algebraMap R Q) ]
    exact hdeg
  let Ba := Basis.reindex (IsAdjoinRootMonic.basis ⟨h, Polynomial.Monic.map (algebraMap R Q) hm⟩)
    (Fin.castOrderIso heq).toEquiv
  set f := (LinearMap.toMatrix Ba Ba).symm (fun i j => algebraMap R Q (c i j)) with hf
  let feq : K ≃ₗ[Q] K := by
    refine LinearEquiv.ofIsUnitDet (f := f) (v := Ba) (v' := Ba) (ι := Fin n) ?_
    rw [hf]
    simp only [LinearMap.toMatrix_symm, LinearMap.toMatrix_toLin]
    have auxeq : RingHom.mapMatrix (algebraMap R Q) c =  fun i j => (algebraMap R Q) (c i j) := rfl
    rw [← auxeq, ← RingHom.map_det]
    apply Ne.isUnit
    apply (map_ne_zero_iff (algebraMap R Q) (IsFractionRing.injective R Q)).mpr hdet
  have aux : ∀ i, feq (Ba i) = h.map (map (algebraMap R Q) (B i)) := by
    intro i
    rw [LinearEquiv.ofIsUnitDet_apply, hpoly, hf]
    simp only [LinearMap.toMatrix_symm, Matrix.toLin_self, algebraMap_smul]
    rw [Polynomial.map_sum, map_sum]
    simp_rw [Polynomial.map_mul, Polynomial.map_C, map_mul,
      ← IsAdjoinRoot.algebraMap_apply, ← Algebra.smul_def]
    simp only [Basis.coe_reindex, Function.comp_apply,
      IsAdjoinRootMonic.basis_apply, Polynomial.map_pow, map_X, map_pow,
      IsAdjoinRoot.map_X, algebraMap_smul, Ba]
    simp
  have : (fun i => h.map (map (algebraMap R Q) (B i))) = f ∘ Ba := by ext i; rw [← aux]; rfl
  rw [this, LinearMap.linearIndependent_iff]
  · exact Basis.linearIndependent Ba
  · rw [LinearMap.ker_eq_bot]
    exact LinearEquiv.injective feq

/-- Imported declaration. -/
def toSymmFun {α A : Type*} [LinearOrder α] (f : α → α → A) : α → α → A :=
  fun i j => if i ≤ j then f i j else f j i

lemma toSymmFun_apply {α A : Type*} [LinearOrder α] (f : α → α → A) (i j : α) (h : i ≤ j) :
  toSymmFun f i j = f i j := by
  unfold toSymmFun
  simp only [ite_true, h]

lemma toSymmFun_apply_eq {α A : Type*} [LinearOrder α] (f : α → α → A) (i j : α) :
  toSymmFun f i j = toSymmFun f j i := by
  have : ∀ i j, i ≤ j → toSymmFun f i j = toSymmFun f j i := by
    intro i j h
    · unfold toSymmFun
      by_cases h' : i = j
      · simp only [le_refl, ite_self, h']
      · have := not_le.2 (lt_of_le_of_ne h h')
        simp only [ite_true, ite_false, this, h]
  exact if h : i ≤ j then this i j h
  else (this j i (le_of_lt (not_le.mp h))).symm

lemma hc_aux {d : R}
  {a : Fin n → Fin n → Fin n → R}
  {s : Fin n → Fin n → R[X]}
  (hsymma : ∀ i j, a i j = a j i)
  (hc_le : ∀ i j, i ≤ j → (B i) * (B j) = ∑ k, (C (d * (a i j k))) * (B k) - T * (s i j)) :
   ∀ i j, (B i) * (B j) =  ∑ k, (C (d * (a i j k))) * (B k) - T * (toSymmFun s i j) := by
  intro i j
  by_cases h : i ≤ j
  · rw [toSymmFun_apply s i j h]
    exact hc_le i j h
  · push Not at h
    rw [mul_comm, hsymma i j, toSymmFun_apply_eq, toSymmFun_apply s j i (le_of_lt h) ]
    exact hc_le j i (le_of_lt h)


end LinInd


/-- The subalgebra builder for `K = Q[θ]`, with `θ` a root of a polynomial  `T` of degree `n`.
  The basis for the subalgebra is given as `wⱼ = (1/d) Bⱼ(θ) `
  with `Bⱼ(X) = ∑ Cᵢⱼ X ^ i` polynomials ∈ `R[X]` :

- `d` : the common denominator for the `R`-basis
- `B` : the list of polynomials defining the basis
- `a` : the multiplication table for the subalgebra with respect to this basis
- `s` : polynomials certifying the multiplication table
- `c` : a matrix with the coefficients of `B` -/
structure SubalgebraBuilder
    (n : ℕ) [NeZero n] (R Q K : Type*) [CommRing R] [IsDomain R]
    [Field Q] [CommRing K] [Algebra Q K] [Algebra R Q] [Algebra R K] [IsScalarTower R Q K]
      [IsFractionRing R Q] (T : R[X]) where
  /-- Imported declaration. -/
  (d : R)
  (hdeg : T.natDegree = n)
  (hm : coeff T n = 1)
  /-- Imported declaration. -/
  (B : Fin n →  R[X])
  /-- Imported declaration. -/
  (a : Fin n → Fin n → Fin n → R)
  /-- Imported declaration. -/
  (s : Fin n → Fin n → R[X])
  /-- Imported declaration. -/
  (c : Matrix (Fin n) (Fin n) R)
  /-- Imported declaration. -/
  (h : IsAdjoinRoot K (map (algebraMap R Q) T))
  (honed : B 0 = C d)
  (hd : d ≠ 0)
  (hpoly : ∀ j, B j = ∑ i : Fin n, C (c i j) * X ^ (i : ℕ))
  (hcc : ∀ i j, j < i → c i j = 0)
  (hin : ∀ i, c i i ≠ 0)
  (hsymma : ∀ i j, a i j = a j i)
  (hc_le : ∀ i j, i ≤ j → (B i) * (B j) =  ∑ k, (C (d * (a i j k))) * (B k) - T * (s i j))


/-- The version of `SubalgebraBuilder` using lists for polynomial arithmetic.
Let `K = Q[θ]`, with `θ` a root of a polynomial  `T` of degree `n`.
The basis for the subalgebra is given as `wⱼ = (1/d) Bⱼ(θ) ` with `Bⱼ(X)` polynomials in `R[X]` :

- `d` : the common denominator for the `R`-basis
- `B` : the matrix with coefficients of the polynomials `Bⱼ`as rows.
- `a` : the multiplication table for the subalgebra with respect to this basis
- `s` : polynomials, as lists, certifying the multiplication table· -/
structure SubalgebraBuilderLists
  (n : ℕ) [NeZero n] (R Q K : Type*) [CommRing R] [IsDomain R]
  [DecidableEq R] [Field Q] [CommRing K] [Algebra Q K]
  [Algebra R Q] [Algebra R K] [IsScalarTower R Q K] [IsFractionRing R Q] (T : R[X]) (l : List R)
    where
  /-- Imported declaration. -/
  (d : R)
  (hlen : l.length = n + 1)
  (htr : l = l.dropTrailingZeros')
  (hofL : T = ofList l)
  (hm : l.getLast (List.ne_nil_of_length_eq_add_one hlen) = 1)
  /-- Imported declaration. -/
  (B : Fin n → (Fin n → R))
  /-- Imported declaration. -/
  (a : Fin n → Fin n → Fin n → R)
  /-- Imported declaration. -/
  (s : Fin n → Fin n → List R)
  /-- Imported declaration. -/
  (h : IsAdjoinRoot K (map (algebraMap R Q) T))
  (honed : (List.ofFn (B 0)).dropTrailingZeros' = [d])
  (hd : d ≠ 0)
  (hcc : ∀ i j, j < i → B j i = 0)
  (hin : ∀ i, B i i ≠ 0)
  (hsymma : ∀ i j, a i j = a j i)
  (hc_le : ∀ i j, i ≤ j → ((List.ofFn (B i)) * (List.ofFn (B j))).dropTrailingZeros' =
    ((List.ofFn (fun k => [(d * (a i j k))] * (List.ofFn (B k)))).sum - l *
      (s i j)).dropTrailingZeros')


variable {n : ℕ} [NeZero n] {R Q K : Type*} [CommRing R] [IsDomain R]
[Field Q] [CommRing K] [Algebra Q K] [Algebra R Q] [Algebra R K] [IsScalarTower R Q K]
[IsFractionRing R Q]

/-- The subalgebra obtained from the `SubalgebraBuilder`· -/
noncomputable def subalgebraOfBuilder
  (T : R[X])
  (A : SubalgebraBuilder n R Q K T) : Subalgebra R K :=
  subalgebraOfPolysInt T A.B A.d A.hd (toSymmFun A.s) A.a (hc_aux A.B T A.hsymma A.hc_le) A.h 0
    A.honed

/-- The basis for the subalgebra constructed with `SubalgebraBuilder`. -/
noncomputable def basisOfBuilder
  (T : R[X])
  (A : SubalgebraBuilder n R Q K T) : Basis (Fin n) R (subalgebraOfBuilder T A) := by
  refine basisSubalgebraOfPolysInt T A.B A.d A.hd (toSymmFun A.s) A.a (hc_aux A.B T A.hsymma
    A.hc_le) A.h 0 A.honed ?_
  exact linearIndependentOfUpperTriangular A.c A.B A.hpoly T
    (Polynomial.monic_of_natDegree_le_of_coeff_eq_one n (le_of_eq A.hdeg) A.hm) A.hdeg
    (is_det_ne_zero_of_upper_triangular A.c A.hcc A.hin) A.h

/-- The basis is precisely `wⱼ  = (1/d) * Bⱼ(θ) ` -/
lemma basisOfBuilder_apply (T : R[X]) (A : SubalgebraBuilder n R Q K T) (i : Fin n) :
  ((basisOfBuilder T A) i).val =  (A.h).map (C (algebraMap R Q A.d)⁻¹ *
    map (algebraMap R Q) (A.B i)) := by
  unfold basisOfBuilder
  have := basisSubalgebraOfPolysInt_apply T A.B A.d A.hd (toSymmFun A.s) A.a
    (hc_aux A.B T A.hsymma A.hc_le) A.h 0 A.honed
    (linearIndependentOfUpperTriangular A.c A.B A.hpoly T
    (Polynomial.monic_of_natDegree_le_of_coeff_eq_one n (le_of_eq A.hdeg) A.hm) A.hdeg
    (is_det_ne_zero_of_upper_triangular A.c A.hcc A.hin) A.h) i
  rw [← Subtype.val_inj] at this
  dsimp at this
  rw [← this]
  rfl

/-- The times table for the subalgebra constructed from the `SubalgebraBuilder` -/
noncomputable def timesTableOfSubalgebraBuilder
  (T : R[X])
  (A : SubalgebraBuilder n R Q K T) : TimesTable (Fin n) R (subalgebraOfBuilder T A) where
    basis := basisOfBuilder T A
    table := A.a
    basis_mul_basis := basisSubalgebraOfPolysIntTable T A.B A.d _ (toSymmFun A.s) A.a _ A.h _ _
      (linearIndependentOfUpperTriangular A.c A.B A.hpoly T
      (Polynomial.monic_of_natDegree_le_of_coeff_eq_one n (le_of_eq A.hdeg) A.hm) A.hdeg
      (is_det_ne_zero_of_upper_triangular A.c A.hcc A.hin) A.h)

/-- Certifies that the subalgebra contains `θ` -/
lemma root_in_subalgebra (T : R[X]) (A : SubalgebraBuilder n R Q K T)
  (a : Fin n → R) (g : R[X]) (h : ∑ i, C (a i) * (A.B i) = C (A.d) * X - T * g) :
  (A.h).root ∈ subalgebraOfBuilder T A := by
  apply_fun map (algebraMap R Q) at h
  simp only [Polynomial.map_sum, Polynomial.map_sub,
    Polynomial.map_mul, map_C, map_X] at h
  apply_fun (A.h).map at h
  simp only [map_sum, map_mul, ← IsAdjoinRoot.algebraMap_apply, map_sub, IsAdjoinRoot.map_X,
    IsAdjoinRoot.map_self, zero_mul, sub_zero, ] at h
  apply_fun (fun y => algebraMap Q K (algebraMap R Q A.d)⁻¹ * y) at h
  conv at h =>
    right
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (((map_ne_zero_iff (algebraMap R Q)
      (IsFractionRing.injective R Q)).mpr A.hd)),
     map_one, one_mul]
  have : ∀ x,  (algebraMap Q K) ((algebraMap R Q) x) =
    (algebraMap Q K).comp (algebraMap R Q) x := by
    intro x
    simp only [RingHom.coe_comp, Function.comp_apply]
  simp_rw [this, ← IsScalarTower.algebraMap_eq, Finset.mul_sum] at h
  conv at h =>
    left; right; intro i
    rw [← mul_assoc, mul_comm _ ((algebraMap R K) (a i)), mul_assoc, ← Algebra.smul_def]
  rw [← h]
  apply sum_mem
  intro c _
  · refine Subalgebra.smul_mem _ ?_ (a c)
    convert (basisOfBuilder T A c).2
    rw [basisOfBuilder_apply T A, IsAdjoinRoot.algebraMap_apply A.h, map_mul]

/-- Constructs the corresponding term `SubalgebraBuilder` from `SubalgebraBuilderLists`· -/
noncomputable def SubalgebraBuilderOfList [DecidableEq R] (T : R[X]) (l : List R)
  (A : SubalgebraBuilderLists n R Q K T l) : SubalgebraBuilder n R Q K T :=
  { d := A.d,
    hdeg := by
      have hne : l ≠ 0 := List.ne_nil_of_length_eq_add_one A.hlen
      have hdrop : l = l.dropTrailingZeros := by
        rw [dropTrailingZeros_eq_dropTrailingZeros']
        exact A.htr
      rw [← Nat.succ_inj, ← Nat.add_one, A.hofL, natDegree_ofList l hne hdrop,
        A.hlen],
    hm := by
      rw [A.hofL, ofList_coeff _ n (by simp only [A.hlen, lt_add_iff_pos_right, zero_lt_one])]
      have aux := A.hm
      rw [List.getLast_eq_getElem] at aux
      convert aux
      rw [A.hlen, add_tsub_cancel_right],
    B := fun i => ofList (List.ofFn (A.B i)),
    a := A.a,
    s := fun i j => ofList (A.s i j),
    h := A.h,
    c := fun i => fun j => A.B j i,
    honed := by
      rw [← ofList_dropTrailingZeros_eq_ofList, dropTrailingZeros_eq_dropTrailingZeros', A.honed]
      simp only [ofList_singleton],
    hd := A.hd,
    hpoly := by
      intro j
      exact ofList_eq_sum' n (A.B j),
    hcc := A.hcc,
    hin := A.hin,
    hsymma := A.hsymma,
    hc_le := by
      intro i j hle
      erw [← ofList_convolve_eq_mul, ← ofList_dropTrailingZeros_eq_ofList,
        dropTrailingZeros_eq_dropTrailingZeros', A.hc_le i j hle,
        ← dropTrailingZeros_eq_dropTrailingZeros',
        ofList_dropTrailingZeros_eq_ofList, ofList_addPointwise_eq_add, list_sum_eq_ofList_sum,
        List.neg_eq_neg_one_mul,  ofList_convolve_eq_mul, ofList_convolve_eq_mul, ← A.hofL]
      simp only [ofList_convolve_eq_mul, ofList_singleton, map_neg,
        map_one, neg_mul, one_mul, map_mul, sub_eq_add_neg] }

/-- The subalgebra obtained from the `SubalgebraBuilderLists`· -/
noncomputable def subalgebraOfBuilderLists [DecidableEq R] (T : R[X]) (l : List R)
    (A : SubalgebraBuilderLists n R Q K T l) : Subalgebra R K :=
    subalgebraOfBuilder T (SubalgebraBuilderOfList T l A)

/-- The basis for the subalgebra obtained from the `SubalgebraBuilderLists`· -/
noncomputable def basisOfBuilderLists [DecidableEq R] (T : R[X]) (l : List R)
    (A : SubalgebraBuilderLists n R Q K T l) : Basis (Fin n) R (subalgebraOfBuilderLists T l A) :=
    basisOfBuilder T (SubalgebraBuilderOfList T l A)

/-- The basis is precisely `wⱼ  = (1/d) * Bⱼ(θ) ` -/
lemma basisOfBuilderLists_apply [DecidableEq R] (T : R[X]) (l : List R)
    (A : SubalgebraBuilderLists n R Q K T l) (i : Fin n) :
    ((basisOfBuilderLists T l A) i).val =
    (A.h).map (C (algebraMap R Q A.d)⁻¹ * map (algebraMap R Q) (ofList (List.ofFn (A.B i)))) := by
  erw [basisOfBuilder_apply]
  rfl

/-- The times table for the subalgebra constructed from the `SubalgebraBuilderLists` -/
noncomputable def timesTableOfSubalgebraBuilderLists [DecidableEq R]
    (T : R[X]) (l : List R)
    (A : SubalgebraBuilderLists n R Q K T l) : TimesTable (Fin n) R (subalgebraOfBuilderLists T l
      A) :=
  timesTableOfSubalgebraBuilder T (SubalgebraBuilderOfList T l A)

lemma root_in_subalgebra_lists [DecidableEq R] (T : R[X]) (l : List R)
    (A : SubalgebraBuilderLists n R Q K T l) (a : Fin n → R) (g : List R)
    (h : (List.sum (List.ofFn (fun i => [a i] * (List.ofFn (A.B i))))).dropTrailingZeros' =
    ([(A.d)] * [0, 1] - l * g).dropTrailingZeros') :
    (A.h).root ∈ subalgebraOfBuilderLists T l A := by
  let A' := (SubalgebraBuilderOfList T l A)
  refine root_in_subalgebra T A' a (ofList g) ?_
  apply_fun Polynomial.ofList at h
  simp only [← dropTrailingZeros_eq_dropTrailingZeros', ofList_dropTrailingZeros_eq_ofList,
    list_sum_eq_ofList_sum, ofList_convolve_eq_mul, ofList_singleton] at h
  convert h
  erw [ofList_addPointwise_eq_add, List.neg_eq_neg_one_mul, ofList_convolve_eq_mul,
  ofList_convolve_eq_mul, ofList_convolve_eq_mul, ← A.hofL]
  simp only [ofList_cons, ofList_nil, mul_zero, add_zero, map_zero,
   map_one, mul_one, zero_add, map_neg, neg_mul,
    one_mul]
  rfl

--------------------------------------------------------------------------------
-- Results on the discriminant of the subalgebra constructed with `SubalgebraBuilder` -/

variable [DecidableEq R] {T : R[X]} {l : List R} [CommRing O] [Algebra R O]
  (A : SubalgebraBuilderLists n R Q K T l)

local notation "Oₖ" => subalgebraOfBuilderLists T l A

/-- Imported declaration. -/
def isAMK : IsAdjoinRootMonic K (T.map (algebraMap R Q)) where
  toIsAdjoinRoot := A.h
  monic := Monic.map (algebraMap R Q)
    (Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
    (le_of_eq (SubalgebraBuilderOfList _ _ A).hdeg) ((SubalgebraBuilderOfList _ _ A).hm))

/-- The discriminant over `Q` of a basis for the subalgebra `subalgebraOfBuilderLists` is equal to
  `(1/d ∏ᵢ Bᵢᵢ) ^ 2 * D`, with `D` the discriminant of `1, θ, θ ^ 2, …, θ ^ (n - 1)`· -/
lemma OfBuilderList_discr_eq_prod_discr' :
  algebraMap R Q ((Algebra.discr R (basisOfBuilderLists T l A))) =
    ((algebraMap R Q (A.d ^ n))⁻¹ * (algebraMap R Q (∏ i, (A.B i i)))) ^ 2 *
       (Algebra.discr Q ((isAMK A).powerBasis).basis) := by
  haveI : FiniteDimensional Q K := Module.Basis.finiteDimensional_of_finite (isAMK A).powerBasis.3
  have hMonic : Monic T := by
    exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
     (le_of_eq (SubalgebraBuilderOfList _ _ A).hdeg) (SubalgebraBuilderOfList _ _ A).hm
  have hdegeq : (map (algebraMap R Q) T).natDegree = T.natDegree := by
    rw [natDegree_map_eq_iff, hMonic]
    simp only [map_one, ne_eq, one_ne_zero, not_false_eq_true, true_or]
  have hkdim : Module.finrank Q K = n := by
    rw [← (SubalgebraBuilderOfList T l A).hdeg, Module.finrank_eq_card_basis
    (isAMK A).powerBasis.3, IsAdjoinRootMonic.powerBasis_dim, Fintype.card_fin]
    exact hdegeq
  have pbdim : (isAMK A).powerBasis.dim = n := by
    rw [IsAdjoinRootMonic.powerBasis_dim, hdegeq,  (SubalgebraBuilderOfList T l A).hdeg]
  rw [discr_eq_discr_fraction_field hkdim]
  let AdjM : IsAdjoinRootMonic _ T :=
    { toIsAdjoinRoot := Algebra.adjoin_isAdjoinRootOfIsAdjoinRoot _ hMonic A.h
      monic := hMonic }
  let B := AdjM.powerBasis.3
  let B' := B.reindex (finCongr (Eq.trans (IsAdjoinRootMonic.powerBasis_dim AdjM)
   ((SubalgebraBuilderOfList T l A).hdeg)))
  let M : Matrix (Fin n) (Fin n) Q := ((algebraMap R Q A.d)⁻¹ • (fun i j => (algebraMap R Q)
  (A.B i j) : Matrix (Fin n) (Fin n) Q))
  have : (Oₖ).val ∘ (basisOfBuilderLists T l A) =  Matrix.mulVec (M.map (algebraMap Q K))
    ((Algebra.adjoin R {A.h.root}).val ∘ B') := by
    ext i
    unfold Matrix.mulVec dotProduct
    simp only [Subalgebra.coe_val, Function.comp_apply, basisOfBuilderLists_apply, map_mul,
      Matrix.map_apply, Pi.smul_apply, smul_eq_mul, IsAdjoinRootMonic.powerBasis_dim,
      IsAdjoinRootMonic.powerBasis_basis, Basis.coe_reindex, finCongr_symm, finCongr_apply,
      IsAdjoinRootMonic.basis_apply, Fin.val_cast,       SubmonoidClass.coe_pow, M, B', B]
    rw [ofList_eq_sum', Polynomial.map_sum, map_sum, Finset.mul_sum]
    simp only [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, map_mul, map_pow,
      IsAdjoinRoot.map_X, ← IsAdjoinRoot.algebraMap_apply]
    congr; ext j
    rw [mul_assoc]
    congr
    exact (Algebra.adjoin_isAdjoinRoot_root T hMonic A.h.root (by
      rw [IsAdjoinRoot.minpoly_root A.h (Monic.ne_zero (Monic.map (algebraMap R Q) hMonic)),
        Monic.map _ hMonic, inv_one, map_one, mul_one])).symm
  have hdet : M.det = (algebraMap R Q (A.d ^ n))⁻¹ * (algebraMap R Q (∏ i, (A.B i i))) := by
    have hlower : M.BlockTriangular ⇑OrderDual.toDual := by
      intro i j hij
      simp only [OrderDual.toDual_lt_toDual] at hij
      simp only [Pi.smul_apply, hij, A.hcc, map_zero, smul_eq_mul, mul_zero, M]
    rw [Matrix.det_of_lowerTriangular M hlower]
    simp only [M, Pi.smul_apply, smul_eq_mul, map_pow, map_prod]
    rw [← Finset.pow_card_mul_prod, ← map_prod, inv_pow]
    congr
    exact Finset.card_fin n
  rw [this, Algebra.discr_of_matrix_mulVec, hdet]
  rw [← Algebra.discr_reindex _ (((isAMK A).powerBasis).basis) (finCongr pbdim)]
  congr
  · ext i
    simp only [Subalgebra.coe_val, IsAdjoinRootMonic.powerBasis_dim,
      IsAdjoinRootMonic.powerBasis_basis, Basis.coe_reindex, finCongr_symm, Function.comp_apply,
      finCongr_apply, IsAdjoinRootMonic.basis_apply,
      Fin.val_cast, SubmonoidClass.coe_pow, isAMK, B', B]
    rw [show (↑AdjM.root : K) = A.h.root by
      exact (Algebra.adjoin_isAdjoinRoot_root T hMonic A.h.root (by
        rw [IsAdjoinRoot.minpoly_root A.h (Monic.ne_zero (Monic.map (algebraMap R Q) hMonic)),
          Monic.map _ hMonic, inv_one, map_one, mul_one]))]
    exact (IsAdjoinRootMonic.basis_apply (isAMK A) ((finCongr pbdim).symm i)).symm


/-- An expression for the discriminant over `R` of a basis for
  the subalgebra `subalgebraOfBuilderLists` -/
lemma OfBuilderList_discr_eq_prod_discr (f : IsAdjoinRootMonic O T) :
  algebraMap R Q ((Algebra.discr R (basisOfBuilderLists T l A))) =
    ((algebraMap R Q (A.d ^ n))⁻¹ * (algebraMap R Q (∏ i, (A.B i i)))) ^ 2 *
       algebraMap R Q ((Algebra.discr R (f.powerBasis).basis)) := by
  rw [discr_eq_discr_fraction_field_powerBasis O T (SubalgebraBuilderOfList _ _ A).hdeg f (isAMK A)]
  exact OfBuilderList_discr_eq_prod_discr' _

/-- An expression for the discriminant over `ℤ` of a basis for
  the subalgebra `subalgebraOfBuilderLists` -/
lemma OfBuilderList_discr_eq_prod_discr_int {K : Type*} [CommRing K] [Algebra ℚ K]
    [IsScalarTower ℤ ℚ K]
  (T : ℤ[X]) (l : List ℤ) (A : SubalgebraBuilderLists n ℤ ℚ K T l)
  (f : IsAdjoinRootMonic O T) :
    Algebra.discr ℤ (basisOfBuilderLists T l A) =
      ((∏ i, (A.B i i)) ^ 2  * (Algebra.discr ℤ (f.powerBasis).basis)) / A.d ^ (2 * n) := by
  symm
  have haux : A.d ^ (2 * n) ≠ 0 := by
    simp only [ne_eq, pow_eq_zero_iff', A.hd, mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
    false_and, not_false_eq_true]
  refine Int.ediv_eq_of_eq_mul_left ?_ ?_
  · exact haux
  · apply_fun (algebraMap ℤ ℚ) using RingHom.injective_int (algebraMap ℤ ℚ)
    rw [map_mul, map_mul, OfBuilderList_discr_eq_prod_discr A f, mul_pow]
    cancel_denoms
    ring_nf
    have hauxQ : (A.d : ℚ) ^ (n * 2) ≠ 0 :=
      pow_ne_zero _ (Int.cast_ne_zero.mpr A.hd)
    rw [inv_pow, mul_assoc, mul_inv_cancel₀ hauxQ, mul_one]
