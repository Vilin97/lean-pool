/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.FiniteCoefficientLaurent
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
/-!
# The equal-characteristic completed-unramified construction: finite unramified coefficient
  extensions in equal characteristic

For a finite extension `l / k` of finite fields, coefficientwise extension
makes `l((T))` a finite extension of `k((T))` of the same degree.  Every
automorphism of `l / k` extends coefficientwise, and these extensions exhaust
the Galois group of `l((T)) / k((T))`.  In particular, arithmetic Frobenius
on `l` gives the genuine Frobenius automorphism of this finite Laurent-series
base change and fixes `T`.

This is the finite unramified source used to model the completed maximal
unramified field in the equal-characteristic completed-unramified construction.  The
  construction is coefficientwise and does not
postulate an abstract unramified extension.
-/

@[expose] public section

noncomputable section


open scoped LaurentSeries PowerSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

variable {k : Type u} {l : Type v}

/-- The coefficientwise map `k((T)) -> l((T))` induced by a ring map
`k -> l`. -/
noncomputable def laurentSeriesCoefficientMap
    {k : Type u} {l : Type v} [Field k] [Field l]
    (f : k →+* l) : k⸨X⸩ →+* l⸨X⸩ where
  toFun x := HahnSeries.map x f
  map_zero' := by
    change HahnSeries.map (0 : k⸨X⸩) f.toZeroHom = 0
    exact HahnSeries.map_zero (Γ := ℤ) f.toZeroHom
  map_one' := by
    change HahnSeries.map (1 : k⸨X⸩) f.toMonoidWithZeroHom = 1
    exact HahnSeries.map_one (Γ := ℤ) f.toMonoidWithZeroHom
  map_add' x y := by
    change HahnSeries.map (x + y) f.toAddMonoidHom =
      HahnSeries.map x f.toAddMonoidHom + HahnSeries.map y f.toAddMonoidHom
    exact HahnSeries.map_add (Γ := ℤ) f.toAddMonoidHom
  map_mul' x y := by
    change HahnSeries.map (x * y) f.toNonUnitalRingHom =
      HahnSeries.map x f.toNonUnitalRingHom * HahnSeries.map y f.toNonUnitalRingHom
    exact HahnSeries.map_mul (Γ := ℤ) f.toNonUnitalRingHom

/-- Mapping Laurent-series coefficients applies the ring homomorphism coefficientwise. -/
@[simp]
theorem laurentSeriesCoefficientMap_coeff
    [Field k] [Field l] (f : k →+* l) (x : k⸨X⸩) (m : ℤ) :
    (laurentSeriesCoefficientMap f x).coeff m = f (x.coeff m) :=
  rfl

/-- The coefficient map sends a constant series to the mapped constant series. -/
theorem laurentSeriesCoefficientMap_C
    [Field k] [Field l] (f : k →+* l) (a : k) :
    laurentSeriesCoefficientMap f (HahnSeries.C (Γ := ℤ) a) =
      HahnSeries.C (Γ := ℤ) (f a) := by
  change HahnSeries.map (HahnSeries.C (Γ := ℤ) a) f = _
  exact HahnSeries.map_C a f

/-- The coefficient map fixes the Laurent uniformizer monomial. -/
@[simp]
theorem laurentSeriesCoefficientMap_single_one
    [Field k] [Field l] (f : k →+* l) :
    laurentSeriesCoefficientMap f (HahnSeries.single (1 : ℤ) 1) =
      (HahnSeries.single (1 : ℤ) 1 : l⸨X⸩) := by
  ext m
  by_cases h : m = 1
  · subst m
    simp
  · simp [HahnSeries.coeff_single_of_ne h]

/-- The induced `k((T))`-algebra structure on `l((T))`. -/
@[reducible]
noncomputable def laurentSeriesCoefficientAlgebra
    [Field k] [Field l] [Algebra k l] : Algebra k⸨X⸩ l⸨X⸩ :=
  RingHom.toAlgebra
    (laurentSeriesCoefficientMap (algebraMap k l))

/-- The induced Laurent-series algebra map is the coefficientwise scalar map. -/
theorem laurentSeriesCoefficientAlgebra_algebraMap
    [Field k] [Field l] [Algebra k l] :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    algebraMap k⸨X⸩ l⸨X⸩ =
      laurentSeriesCoefficientMap (algebraMap k l) :=
  rfl

attribute [local instance] laurentSeriesCoefficientAlgebra

/-- One coefficient coordinate of a Laurent series with respect to a basis
of the coefficient extension. -/
noncomputable def laurentSeriesCoefficientCoord
    [Field k] [Field l] [Algebra k l]
    {ι : Type*} (b : Module.Basis ι k l)
    (x : l⸨X⸩) (i : ι) : k⸨X⸩ :=
  HahnSeries.ofSuppBddBelow
    (fun m : ℤ ↦ b.repr (x.coeff m) i)
    (by
      refine ⟨x.order, ?_⟩
      intro m hm
      by_contra hnot
      have hxzero : x.coeff m = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_order (not_le.mp hnot)
      exact hm (by simp [hxzero]))

/-- A Laurent coordinate series records the corresponding basis coordinate coefficientwise. -/
@[simp]
theorem laurentSeriesCoefficientCoord_coeff
    [Field k] [Field l] [Algebra k l]
    {ι : Type*} (b : Module.Basis ι k l)
    (x : l⸨X⸩) (i : ι) (m : ℤ) :
    (laurentSeriesCoefficientCoord b x i).coeff m =
      b.repr (x.coeff m) i := by
  rfl

section FiniteBasis

variable [Field k] [Field l] [Algebra k l]
  {ι : Type*} [Fintype ι]

omit [Fintype ι] in
private theorem laurentSeriesCoefficientBasis_linearIndependent [Finite ι]
    (b : Module.Basis ι k l) :
    LinearIndependent k⸨X⸩
      (fun i : ι ↦ (HahnSeries.C (Γ := ℤ) (b i) : l⸨X⸩)) := by
  classical
  let := Fintype.ofFinite ι
  let : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  ext m
  have hcoeff := congrArg (fun x : l⸨X⸩ ↦ x.coeff m) hg
  have halgebraMap_coeff (x : k⸨X⸩) :
      (algebraMap k⸨X⸩ l⸨X⸩ x).coeff m =
        algebraMap k l (x.coeff m) := by
    change
      (laurentSeriesCoefficientMap (algebraMap k l) x).coeff m =
        algebraMap k l (x.coeff m)
    exact laurentSeriesCoefficientMap_coeff (algebraMap k l) x m
  have hsum :
      ∑ j : ι, algebraMap k l ((g j).coeff m) * b j = 0 := by
    simpa [Algebra.smul_def, laurentSeriesCoefficientAlgebra,
      laurentSeriesCoefficientMap, halgebraMap_coeff, mul_comm] using hcoeff
  have hrepr : ∀ j : ι, (g j).coeff m = 0 := by
    intro j
    have hb := Fintype.linearIndependent_iff.mp b.linearIndependent
      (fun t : ι ↦ (g t).coeff m) (by
        simpa [Algebra.smul_def] using hsum) j
    exact hb
  exact hrepr i

omit [Fintype ι] in
private theorem laurentSeriesCoefficientBasis_span [Finite ι]
    (b : Module.Basis ι k l) :
    Submodule.span k⸨X⸩
        (Set.range (fun i : ι ↦
          (HahnSeries.C (Γ := ℤ) (b i) : l⸨X⸩))) = ⊤ := by
  classical
  let := Fintype.ofFinite ι
  let : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  classical
  rw [eq_top_iff]
  intro x _hx
  let coord : ι → k⸨X⸩ := fun i ↦ laurentSeriesCoefficientCoord b x i
  have hsum :
      (∑ i : ι, coord i •
        (HahnSeries.C (Γ := ℤ) (b i) : l⸨X⸩)) = x := by
    ext m
    rw [HahnSeries.coeff_sum]
    calc
      (∑ i : ι, (coord i •
          (HahnSeries.C (Γ := ℤ) (b i) : l⸨X⸩) : l⸨X⸩).coeff m) =
          ∑ i : ι, algebraMap k l (b.repr (x.coeff m) i) * b i := by
        apply Finset.sum_congr rfl
        intro i _
        change
          ((HahnSeries.map (coord i) (algebraMap k l)) *
            (HahnSeries.C (Γ := ℤ) (b i) : l⸨X⸩)).coeff m = _
        rw [mul_comm]
        simp [coord, mul_comm]
      _ = x.coeff m := by
        simpa [Algebra.smul_def] using b.sum_repr (x.coeff m)
  rw [← hsum]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ (coord i)
      (Submodule.subset_span ⟨i, rfl⟩)

/-- A finite coefficient basis extends coefficientwise to a Laurent-series
basis. -/
noncomputable def laurentSeriesCoefficientBasis
    (b : Module.Basis ι k l) : Module.Basis ι k⸨X⸩ l⸨X⸩ := by
  letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  exact Module.Basis.mk
    (laurentSeriesCoefficientBasis_linearIndependent b)
    (laurentSeriesCoefficientBasis_span b).ge

/-- The induced Laurent-series basis consists of constant images of the coefficient basis. -/
@[simp]
theorem laurentSeriesCoefficientBasis_apply
    (b : Module.Basis ι k l) (i : ι) :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    laurentSeriesCoefficientBasis b i =
      (HahnSeries.C (Γ := ℤ) (b i) : l⸨X⸩) := by
  let : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  exact Module.Basis.mk_apply _ _ _

end FiniteBasis

/-- Finite-dimensionality is preserved by coefficientwise Laurent-series
extension. -/
theorem laurentSeriesCoefficient_finiteDimensional
    [Field k] [Field l] [Algebra k l] [FiniteDimensional k l] :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    FiniteDimensional k⸨X⸩ l⸨X⸩ := by
  let : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  let b : Module.Basis (Fin (Module.finrank k l)) k l := Module.finBasis k l
  exact (laurentSeriesCoefficientBasis b).finiteDimensional_of_finite

/-- Coefficient extension does not change the finite extension degree. -/
theorem laurentSeriesCoefficient_finrank
    [Field k] [Field l] [Algebra k l] [FiniteDimensional k l] :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    Module.finrank k⸨X⸩ l⸨X⸩ = Module.finrank k l := by
  let : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  let b : Module.Basis (Fin (Module.finrank k l)) k l := Module.finBasis k l
  let B := laurentSeriesCoefficientBasis b
  let : FiniteDimensional k⸨X⸩ l⸨X⸩ :=
    B.finiteDimensional_of_finite
  simpa [B] using Module.finrank_eq_card_basis B

/-- A coefficient-field ring equivalence extends coefficientwise to Laurent
series. -/
noncomputable def laurentSeriesCoefficientRingEquiv
    [Field k] [Field l] (e : k ≃+* l) : k⸨X⸩ ≃+* l⸨X⸩ where
  toFun := laurentSeriesCoefficientMap e.toRingHom
  invFun := laurentSeriesCoefficientMap e.symm.toRingHom
  left_inv x := by
    ext m
    simp
  right_inv x := by
    ext m
    simp
  map_add' := map_add (laurentSeriesCoefficientMap e.toRingHom)
  map_mul' := map_mul (laurentSeriesCoefficientMap e.toRingHom)

/-- A coefficientwise ring equivalence applies the base equivalence at every exponent. -/
@[simp]
theorem laurentSeriesCoefficientRingEquiv_coeff
    [Field k] [Field l] (e : k ≃+* l) (x : k⸨X⸩) (m : ℤ) :
    (laurentSeriesCoefficientRingEquiv e x).coeff m = e (x.coeff m) :=
  rfl

/-- An automorphism of the coefficient extension acts coefficientwise as an
automorphism over the Laurent-series base. -/
noncomputable def laurentSeriesCoefficientAlgEquiv
    [Field k] [Field l] [Algebra k l]
    (e : l ≃ₐ[k] l) : l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩ := by
  letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  refine
    { laurentSeriesCoefficientRingEquiv e.toRingEquiv with
      commutes' := ?_ }
  intro x
  change laurentSeriesCoefficientMap e.toRingHom
      (laurentSeriesCoefficientMap (algebraMap k l) x) =
    laurentSeriesCoefficientMap (algebraMap k l) x
  ext m
  change e (algebraMap k l (x.coeff m)) = algebraMap k l (x.coeff m)
  exact e.commutes (x.coeff m)

/-- A coefficientwise algebra equivalence applies the base automorphism at every exponent. -/
@[simp]
theorem laurentSeriesCoefficientAlgEquiv_coeff
    [Field k] [Field l] [Algebra k l]
    (e : l ≃ₐ[k] l) (x : l⸨X⸩) (m : ℤ) :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    (laurentSeriesCoefficientAlgEquiv e x).coeff m = e (x.coeff m) :=
  rfl

/-- Coefficientwise extension is faithful on automorphisms. -/
theorem laurentSeriesCoefficientAlgEquiv_injective
    [Field k] [Field l] [Algebra k l] :
    Function.Injective
      (fun e : l ≃ₐ[k] l ↦
        letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
        laurentSeriesCoefficientAlgEquiv e) := by
  intro e f hef
  apply AlgEquiv.ext
  intro x
  have h := DFunLike.congr_fun hef (HahnSeries.C (Γ := ℤ) x : l⸨X⸩)
  have hc := congrArg (fun y : l⸨X⸩ ↦ y.coeff 0) h
  simpa using hc

/-- Coefficientwise extension as a homomorphism between the two Galois
groups. -/
noncomputable def laurentSeriesCoefficientGalHom
    [Field k] [Field l] [Algebra k l] :
    (l ≃ₐ[k] l) →* (l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩) := by
  letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
  exact
    { toFun := laurentSeriesCoefficientAlgEquiv
      map_one' := by
        apply AlgEquiv.ext
        intro x
        ext m
        simp
      map_mul' := by
        intro e f
        apply AlgEquiv.ext
        intro x
        ext m
        simp }

/-- The Galois homomorphism sends an automorphism to its coefficientwise Laurent action. -/
@[simp]
theorem laurentSeriesCoefficientGalHom_apply
    [Field k] [Field l] [Algebra k l]
    (e : l ≃ₐ[k] l) :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    laurentSeriesCoefficientGalHom e = laurentSeriesCoefficientAlgEquiv e :=
  rfl

/-- Distinct coefficient automorphisms induce distinct Laurent-series automorphisms. -/
theorem laurentSeriesCoefficientGalHom_injective
    [Field k] [Field l] [Algebra k l] :
    Function.Injective
      (letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
       laurentSeriesCoefficientGalHom :
        (l ≃ₐ[k] l) → (l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩)) :=
  laurentSeriesCoefficientAlgEquiv_injective

section FiniteFields

variable [Field k] [Finite k] [Field l] [Finite l] [Algebra k l]

omit [Finite k] in
/-- For finite coefficient fields, all Laurent-series automorphisms come
from coefficient automorphisms. -/
theorem laurentSeriesCoefficientGalHom_surjective :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    Function.Surjective (laurentSeriesCoefficientGalHom :
      (l ≃ₐ[k] l) → (l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩)) := by
  let : Module.Finite k l := Module.Finite.of_finite
  let : FiniteDimensional k⸨X⸩ l⸨X⸩ :=
    laurentSeriesCoefficient_finiteDimensional
  have hcard :
      Nat.card (l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩) ≤ Nat.card (l ≃ₐ[k] l) := by
    calc
      Nat.card (l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩) ≤
          Module.finrank k⸨X⸩ l⸨X⸩ := by
        simpa only [Nat.card_eq_fintype_card] using
          (AlgEquiv.card_le (F := k⸨X⸩) (K := l⸨X⸩))
      _ = Module.finrank k l := laurentSeriesCoefficient_finrank
      _ = Nat.card (l ≃ₐ[k] l) :=
        (IsGalois.card_aut_eq_finrank k l).symm
  have hbijective : Function.Bijective
      (laurentSeriesCoefficientGalHom :
        (l ≃ₐ[k] l) → (l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩)) :=
    Function.Injective.bijective_of_nat_card_le
      laurentSeriesCoefficientGalHom_injective hcard
  exact hbijective.2

omit [Finite k] in
/-- The coefficient Laurent-series extension is Galois. -/
theorem laurentSeriesCoefficient_isGalois :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    IsGalois k⸨X⸩ l⸨X⸩ := by
  let : Module.Finite k l := Module.Finite.of_finite
  let : FiniteDimensional k⸨X⸩ l⸨X⸩ :=
    laurentSeriesCoefficient_finiteDimensional
  apply IsGalois.of_card_aut_eq_finrank
  apply Nat.le_antisymm
  · simpa only [Nat.card_eq_fintype_card] using
      (AlgEquiv.card_le (F := k⸨X⸩) (K := l⸨X⸩))
  · calc
      Module.finrank k⸨X⸩ l⸨X⸩ = Nat.card (l ≃ₐ[k] l) := by
        exact laurentSeriesCoefficient_finrank.trans
          (IsGalois.card_aut_eq_finrank k l).symm
      _ ≤ Nat.card (l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩) :=
        Nat.card_le_card_of_injective
          (laurentSeriesCoefficientGalHom :
            (l ≃ₐ[k] l) → (l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩))
          laurentSeriesCoefficientGalHom_injective

/-- Arithmetic Frobenius on the coefficient field, extended to Laurent
series. -/
noncomputable def equalCharacteristicLaurentFrobenius :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    l⸨X⸩ ≃ₐ[k⸨X⸩] l⸨X⸩ := by
  letI : Fintype k := Fintype.ofFinite k
  exact laurentSeriesCoefficientAlgEquiv
    (k := k) (l := l)
    (FiniteField.frobeniusAlgEquivOfAlgebraic k l)

/-- Laurent Frobenius raises each coefficient to the residue-field cardinality. -/
@[simp]
theorem equalCharacteristicLaurentFrobenius_coeff
    (x : l⸨X⸩) (m : ℤ) :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    (equalCharacteristicLaurentFrobenius (k := k) (l := l) x).coeff m =
      (x.coeff m) ^ Nat.card k := by
  let : Fintype k := Fintype.ofFinite k
  simp [equalCharacteristicLaurentFrobenius,
    Nat.card_eq_fintype_card]

/-- Laurent Frobenius fixes the Laurent uniformizer. -/
@[simp]
theorem equalCharacteristicLaurentFrobenius_single_one :
    letI : Algebra k⸨X⸩ l⸨X⸩ := laurentSeriesCoefficientAlgebra
    equalCharacteristicLaurentFrobenius (k := k) (l := l)
        (HahnSeries.single (1 : ℤ) 1 : l⸨X⸩) =
      HahnSeries.single (1 : ℤ) 1 := by
  let : Fintype k := Fintype.ofFinite k
  ext m
  by_cases h : m = 1
  · subst m
    simp
  · simp [HahnSeries.coeff_single_of_ne h]

end FiniteFields

section ChosenFiniteExtension

variable (k : Type u) [Field k] [Finite k]
  (p n : ℕ) [Fact p.Prime] [CharP k p] [NeZero n]

/-- The finite unramified Laurent-series extension obtained from the chosen
degree-`n` extension of the residue field. -/
def equalCharacteristicFiniteUnramifiedExtension :=
  (FiniteField.Extension k p n)⸨X⸩

/-- The finite unramified Laurent-series extension is a field. -/
instance equalCharacteristicFiniteUnramifiedExtensionField :
    Field (equalCharacteristicFiniteUnramifiedExtension k p n) := by
  change Field ((FiniteField.Extension k p n)⸨X⸩)
  infer_instance

/-- The finite unramified extension is an algebra over the base Laurent field. -/
noncomputable instance equalCharacteristicFiniteUnramifiedAlgebra :
    Algebra k⸨X⸩ (equalCharacteristicFiniteUnramifiedExtension k p n) :=
  laurentSeriesCoefficientAlgebra

section

/-- The finite unramified Laurent extension carries the module structure of its coefficient
algebra. -/
local instance equalCharacteristicFiniteUnramifiedModule :
    @Module k⸨X⸩ (equalCharacteristicFiniteUnramifiedExtension k p n)
      (inferInstance : DivisionRing k⸨X⸩).toRing.toSemiring
      (inferInstance : AddCommGroup
        (equalCharacteristicFiniteUnramifiedExtension k p n)).toAddCommMonoid :=
  @Algebra.toModule k⸨X⸩ (equalCharacteristicFiniteUnramifiedExtension k p n)
    _ _ (equalCharacteristicFiniteUnramifiedAlgebra k p n)

/-- The finite unramified Laurent extension is finite-dimensional over the base. -/
instance equalCharacteristicFiniteUnramifiedFiniteDimensional :
    FiniteDimensional k⸨X⸩
      (equalCharacteristicFiniteUnramifiedExtension k p n) :=
  laurentSeriesCoefficient_finiteDimensional

end

/-- Comparison with the Laurent-series presentation over the chosen finite
coefficient extension. -/
def equalCharacteristicFiniteUnramifiedExtensionEquivLaurentSeries :
    equalCharacteristicFiniteUnramifiedExtension k p n ≃+*
      (FiniteField.Extension k p n)⸨X⸩ :=
  RingEquiv.refl _

/-- Algebra-linear comparison with the Laurent-series presentation.  This is
the degree-preserving bridge for the named finite unramified extension. -/
def equalCharacteristicFiniteUnramifiedExtensionAlgEquivLaurentSeries :
    equalCharacteristicFiniteUnramifiedExtension k p n ≃ₐ[k⸨X⸩]
      (FiniteField.Extension k p n)⸨X⸩ := by
  change (FiniteField.Extension k p n)⸨X⸩ ≃ₐ[k⸨X⸩]
    (FiniteField.Extension k p n)⸨X⸩
  exact AlgEquiv.refl

/-- Construct a named finite unramified element from a Laurent series. -/
def equalCharacteristicFiniteUnramifiedExtensionOfLaurentSeries :
    (FiniteField.Extension k p n)⸨X⸩ →+*
      equalCharacteristicFiniteUnramifiedExtension k p n :=
  (equalCharacteristicFiniteUnramifiedExtensionEquivLaurentSeries
    k p n).symm.toRingHom

/-- Read a named finite unramified element as a Laurent series. -/
def equalCharacteristicFiniteUnramifiedExtensionToLaurentSeries :
    equalCharacteristicFiniteUnramifiedExtension k p n →+*
      (FiniteField.Extension k p n)⸨X⸩ :=
  (equalCharacteristicFiniteUnramifiedExtensionEquivLaurentSeries
    k p n).toRingHom

/-- The coefficient of a named finite unramified Laurent element. -/
def equalCharacteristicFiniteUnramifiedExtensionCoeff
    (x : equalCharacteristicFiniteUnramifiedExtension k p n) (m : ℤ) :
    FiniteField.Extension k p n :=
  (equalCharacteristicFiniteUnramifiedExtensionToLaurentSeries
    k p n x).coeff m

/-- The chosen coefficient extension has exactly the requested Laurent
degree. -/
theorem equalCharacteristicFiniteUnramifiedExtension_finrank :
    Module.finrank k⸨X⸩
      (equalCharacteristicFiniteUnramifiedExtension k p n) = n := by
  calc
    Module.finrank k⸨X⸩
        (equalCharacteristicFiniteUnramifiedExtension k p n) =
        Module.finrank k⸨X⸩ (FiniteField.Extension k p n)⸨X⸩ :=
      (equalCharacteristicFiniteUnramifiedExtensionAlgEquivLaurentSeries
        k p n).toLinearEquiv.finrank_eq
    _ = Module.finrank k (FiniteField.Extension k p n) :=
      laurentSeriesCoefficient_finrank
    _ = n := FiniteField.finrank_extension k p n

/-- The chosen finite unramified Laurent-series extension is Galois. -/
theorem equalCharacteristicFiniteUnramifiedExtension_isGalois :
    IsGalois k⸨X⸩
      (equalCharacteristicFiniteUnramifiedExtension k p n) :=
  laurentSeriesCoefficient_isGalois

/-- Its distinguished arithmetic Frobenius. -/
noncomputable def equalCharacteristicFiniteUnramifiedFrobenius :
    Gal(equalCharacteristicFiniteUnramifiedExtension k p n/k⸨X⸩) :=
  laurentSeriesCoefficientGalHom (FiniteField.Extension.frob k p n)

/-- Finite unramified Frobenius applies finite-field Frobenius coefficientwise. -/
@[simp]
theorem equalCharacteristicFiniteUnramifiedFrobenius_coeff
    (x : equalCharacteristicFiniteUnramifiedExtension k p n) (m : ℤ) :
    equalCharacteristicFiniteUnramifiedExtensionCoeff k p n
        (equalCharacteristicFiniteUnramifiedFrobenius k p n x) m =
      (equalCharacteristicFiniteUnramifiedExtensionCoeff k p n x m) ^
        Nat.card k :=
  by
    change ((FiniteField.Extension.frob k p n)
      (equalCharacteristicFiniteUnramifiedExtensionCoeff k p n x m)) = _
    exact FiniteField.Extension.frob_apply k p n

/-- Every automorphism of the chosen unramified factor is a power of its
arithmetic Frobenius. -/
theorem equalCharacteristicFiniteUnramifiedFrobenius_pow_surjective
    (σ : Gal(equalCharacteristicFiniteUnramifiedExtension k p n/k⸨X⸩)) :
    ∃ i < n, equalCharacteristicFiniteUnramifiedFrobenius k p n ^ i = σ := by
  obtain ⟨τ, rfl⟩ := (laurentSeriesCoefficientGalHom_surjective
    (k := k) (l := FiniteField.Extension k p n)) σ
  obtain ⟨i, hi, hτ⟩ := FiniteField.Extension.exists_frob_pow_eq k p n τ
  refine ⟨i, hi, ?_⟩
  rw [← hτ]
  exact (map_pow laurentSeriesCoefficientGalHom
    (FiniteField.Extension.frob k p n) i).symm

end ChosenFiniteExtension

end EqualCharacteristic
end LubinTate
