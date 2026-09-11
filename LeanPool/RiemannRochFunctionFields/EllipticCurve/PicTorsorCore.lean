/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.EllipticCurve.GenusOne
public import LeanPool.RiemannRochFunctionFields.EllipticCurve.DegreeOneDictionary
public import LeanPool.RiemannRochFunctionFields.RiemannRochTheorem.Corollaries
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Group
import Mathlib.Tactic.Convert
import Mathlib.Tactic.ByContra

/-!
# Core construction of the degree-one Picard torsor

This file constructs the divisor-class map, proves its bijectivity by Riemann–Roch, and
identifies it with the ideal-class map on rational Weierstrass points.
-/

@[expose] public section

open FunctionField
open FunctionField.Chart
open scoped Polynomial RatFunc nonZeroDivisors

namespace WeierstrassCurve.Affine.Chart

noncomputable section

variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]

/-- Classical decidable equality used to instantiate the Weierstrass point group law. -/
local instance instDecidableEqRiemannRoch : DecidableEq k := Classical.decEq k

/-- A degree-one divisor on a genus-one function field has Riemann–Roch dimension one. -/
lemma ell_eq_one_of_deg_one {W₀ : DivisorA k K} (hW₀ : IsCanonical k K W₀)
    (D : DivisorA k K) (hg : genus k K = 1)
    (hdeg : deg k K D = 1) : ell k K D = 1 := by
  have hWdeg := deg_canonical k K hW₀
  have hneg : deg k K (W₀ - D) < 0 := by
    rw [deg_sub, hWdeg, hg, hdeg]
    norm_num
  have hzero := RRspace_neg_deg_ell k K hneg
  have hRR := riemann_roch k K hW₀ D
  rw [hzero, hg, hdeg] at hRR
  omega

/- Implementation detail of the degree-one Picard torsor: the class-group plumbing over the
finite and infinite places, together with the core equivalence `picTorsor'` and its group-law
compatibility. These declarations remain in the chart's `Internal` namespace; the public API over
intrinsic places is defined in `RiemannRoch.CoordinateFree.EllipticCurve`. -/
namespace Internal

/-- The ideal class group of the finite-integer ring of `K/k`. -/
abbrev FiniteClassGroup := ClassGroup (ringOfIntegers k K)

/-- Restriction of an adelic divisor to its finite-place component. -/
noncomputable def finitePart (D : DivisorA k K) :
    IsDedekindDomain.Divisor (ringOfIntegers k K) :=
  (Finsupp.sumFinsuppAddEquivProdFinsupp D).1

omit [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
@[simp]
lemma finitePart_apply (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    finitePart (k := k) K D v = D (Sum.inl v) := rfl

/-- The ideal class represented by the finite part of an adelic divisor. -/
noncomputable def finiteDivisorClass : DivisorA k K →+
    Additive (FiniteClassGroup (k := k) K) where
  toFun D := Additive.ofMul <| ClassGroup.mk K <|
    (FractionalIdeal.divisorEquiv (R := ringOfIntegers k K) (K := K)).symm
      (finitePart (k := k) K D) |>.toMul
  map_zero' := by
    change Additive.ofMul (ClassGroup.mk K
      ((FractionalIdeal.divisorEquiv (R := ringOfIntegers k K) (K := K)).symm
        (finitePart (k := k) K 0)).toMul) = 0
    apply Additive.toMul.injective
    simp [finitePart]
  map_add' D E := by
    apply Additive.toMul.injective
    change ClassGroup.mk K
        ((FractionalIdeal.divisorEquiv (R := ringOfIntegers k K) (K := K)).symm
          (finitePart (k := k) K (D + E))).toMul =
      ClassGroup.mk K
          ((FractionalIdeal.divisorEquiv (R := ringOfIntegers k K) (K := K)).symm
            (finitePart (k := k) K D)).toMul *
        ClassGroup.mk K
          ((FractionalIdeal.divisorEquiv (R := ringOfIntegers k K) (K := K)).symm
            (finitePart (k := k) K E)).toMul
    rw [← map_mul]
    congr 1
    have hfin : finitePart (k := k) K (D + E) =
        finitePart (k := k) K D + finitePart (k := k) K E := by
      ext v
      simp [finitePart]
    rw [hfin]
    exact congrArg Additive.toMul
      (map_add (FractionalIdeal.divisorEquiv (R := ringOfIntegers k K) (K := K)).symm _ _)

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
lemma finiteDivisorClass_principal (u : Kˣ) :
    finiteDivisorClass (k := k) K (principalDivisorA k K (Additive.ofMul u)) = 0 := by
  let de := FractionalIdeal.divisorEquiv (R := ringOfIntegers k K) (K := K)
  let I := FractionalIdeal.principalFractionalIdeal (R := ringOfIntegers k K) (K := K) u
  have hpart : finitePart (k := k) K (principalDivisorA k K (Additive.ofMul u)) =
      FractionalIdeal.principalDivisor (R := ringOfIntegers k K) (K := K)
        (Additive.ofMul u) := by
    ext v
    exact principalDivisorA_apply_finite k K (Additive.ofMul u) v
  have hI : de.symm (finitePart (k := k) K (principalDivisorA k K (Additive.ofMul u))) =
      Additive.ofMul I := by
    apply de.injective
    rw [de.apply_symm_apply, hpart]
    rfl
  apply Additive.toMul.injective
  change ClassGroup.mk K
    (de.symm (finitePart (k := k) K (principalDivisorA k K (Additive.ofMul u)))).toMul = 1
  rw [hI]
  refine (ClassGroup.mk_eq_one_iff).2 ⟨⟨(u : K), ?_⟩⟩
  change (I : Submodule (ringOfIntegers k K) K) =
    Submodule.span (ringOfIntegers k K) {(u : K)}
  rw [← FractionalIdeal.coe_spanSingleton
    (R := ringOfIntegers k K) (S := (ringOfIntegers k K)⁰)]
  rfl

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
lemma eq_single_of_effective_deg_one {D : DivisorA k K}
    (hD : IsEffective k K D) (hdeg : deg k K D = 1) :
    ∃ v : PlaceA k K, placeDegree k K v = 1 ∧ D = Finsupp.single v 1 := by
  classical
  have hs : D.support.Nonempty := by
    by_contra hnone
    rw [Finset.not_nonempty_iff_eq_empty] at hnone
    have hzero : D = 0 := by
      apply Finsupp.ext
      intro v
      have : v ∉ D.support := by rw [hnone]; simp
      exact Finsupp.notMem_support_iff.mp this
    rw [hzero, deg_zero] at hdeg
    norm_num at hdeg
  let v := Classical.choose hs
  have hv : v ∈ D.support := Classical.choose_spec hs
  let g : PlaceA k K → ℤ := fun w => D w * (placeDegree k K w : ℤ)
  have hnonneg : ∀ w ∈ D.support, 0 ≤ g w := by
    intro w _
    exact mul_nonneg (hD w) (Int.natCast_nonneg _)
  have hsum : ∑ w ∈ D.support, g w = 1 := by
    simpa [deg, Finsupp.sum, g] using hdeg
  have hvcoeff : 0 < D v := lt_of_le_of_ne (hD v)
    (Ne.symm (Finsupp.mem_support_iff.mp hv))
  have hvdeg : 0 < (placeDegree k K v : ℤ) := by
    exact_mod_cast placeDegree_pos k K v
  have hvterm_le : g v ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum hnonneg hv
  have hDv : D v = 1 := by
    dsimp [g] at hvterm_le
    nlinarith
  have hdegV : placeDegree k K v = 1 := by
    dsimp [g] at hvterm_le
    norm_cast at hvdeg ⊢
    nlinarith
  have herase : ∑ w ∈ D.support.erase v, g w = 0 := by
    have hsplit := Finset.sum_erase_add D.support g hv
    rw [hsum] at hsplit
    dsimp [g] at hsplit
    rw [hDv, hdegV] at hsplit
    norm_num at hsplit ⊢
    omega
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun w hw => hnonneg w
    (Finset.mem_of_mem_erase hw))).1 herase
  refine ⟨v, hdegV, ?_⟩
  apply Finsupp.ext
  intro w
  by_cases hwv : w = v
  · subst w
    simp [hDv]
  · have hsingle : Finsupp.single v (1 : ℤ) w = 0 := by
      simp [hwv]
    rw [hsingle]
    by_cases hw : w ∈ D.support
    · have hwErase : w ∈ D.support.erase v := Finset.mem_erase.2 ⟨hwv, hw⟩
      have hgw := hall w hwErase
      dsimp [g] at hgw
      have hwdeg : 0 < (placeDegree k K w : ℤ) := by
        exact_mod_cast placeDegree_pos k K w
      nlinarith
    · exact Finsupp.notMem_support_iff.mp hw

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
lemma finiteDivisorClass_single_infinite
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) (n : ℤ) :
    finiteDivisorClass (k := k) K (Finsupp.single (Sum.inr v) n) = 0 := by
  apply Additive.toMul.injective
  change ClassGroup.mk K
    ((FractionalIdeal.divisorEquiv (R := ringOfIntegers k K) (K := K)).symm
      (finitePart (k := k) K (Finsupp.single (Sum.inr v) n))).toMul = 1
  have hpart : finitePart (k := k) K (Finsupp.single (Sum.inr v) n) = 0 := by
    ext w
    simp [finitePart]
  rw [hpart, map_zero]
  exact map_one (ClassGroup.mk K)

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
lemma finiteDivisorClass_single_finite
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    finiteDivisorClass (k := k) K (Finsupp.single (Sum.inl v) 1) =
      Additive.ofMul (ClassGroup.mk K (FractionalIdeal.mk0 K
        ⟨v.asIdeal, by
          rw [mem_nonZeroDivisors_iff_ne_zero]
          change v.asIdeal ≠ ⊥
          exact v.ne_bot⟩)) := by
  classical
  let de := FractionalIdeal.divisorEquiv (R := ringOfIntegers k K) (K := K)
  let I : (Ideal (ringOfIntegers k K))⁰ :=
    ⟨v.asIdeal, by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      change v.asIdeal ≠ ⊥
      exact v.ne_bot⟩
  have hdiv : de (Additive.ofMul (FractionalIdeal.mk0 K I)) = Finsupp.single v 1 := by
    ext w
    change FractionalIdeal.divisor (FractionalIdeal.mk0 K I) w = _
    rw [FractionalIdeal.divisor_apply]
    change FractionalIdeal.count K w (v.asIdeal :
      FractionalIdeal (ringOfIntegers k K)⁰ K) = _
    rw [FractionalIdeal.count_maximal]
    simp [Finsupp.single_apply]
  have hpart : finitePart (k := k) K (Finsupp.single (Sum.inl v) 1) =
      Finsupp.single v 1 := by
    ext w
    simp [finitePart, Finsupp.single_apply]
  change Additive.ofMul (ClassGroup.mk K (de.symm
    (finitePart (k := k) K (Finsupp.single (Sum.inl v) 1))).toMul) = _
  rw [hpart, ← hdiv, de.symm_apply_apply]
  rfl

section Transport

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S]

lemma classGroup_mulEquiv_mk0 (e : R ≃+* S) (I : (Ideal R)⁰) :
    ClassGroup.mulEquiv e (ClassGroup.mk0 I) =
      ClassGroup.mk0 ⟨I.1.map e,
        by
          rw [mem_nonZeroDivisors_iff_ne_zero]
          exact (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩ := by
  let : RingHomInvPair (e : R →+* S) e.symm :=
    RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair (e.symm : S →+* R) e :=
    RingHomInvPair.of_ringEquiv_symm e
  apply (ClassGroup.equiv (FractionRing S)).injective
  simp only [ClassGroup.mulEquiv, MulEquiv.trans_apply, ClassGroup.equiv_mk0,
    QuotientGroup.mk'_apply, MulEquiv.apply_symm_apply]
  refine congrArg QuotientGroup.mk ?_
  ext x
  change x ∈ Submodule.map
      (IsFractionRing.semilinearEquivOfRingEquiv (FractionRing R) (FractionRing S) e).toLinearMap
      (IsLocalization.coeSubmodule (FractionRing R) (I : Ideal R)) ↔
    x ∈ IsLocalization.coeSubmodule (FractionRing S) (Ideal.map e (I : Ideal R))
  rw [Submodule.mem_map, IsLocalization.mem_coeSubmodule]
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨r, hr, hrz⟩ :=
      (IsLocalization.mem_coeSubmodule (FractionRing R) (I : Ideal R)).mp hz
    refine ⟨e r, (Ideal.mem_map_of_equiv e (e r)).mpr ⟨r, hr, rfl⟩, ?_⟩
    rw [← hzx, ← hrz]
    exact (IsFractionRing.semilinearEquivOfRingEquiv_algebraMap
      (FractionRing R) (FractionRing S) e r).symm
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨r, hr, hrs⟩ :=
      (Ideal.mem_map_iff_of_surjective e e.surjective).mp hs
    refine ⟨algebraMap R (FractionRing R) r,
      (IsLocalization.mem_coeSubmodule (FractionRing R) (I : Ideal R)).mpr
        ⟨r, hr, rfl⟩, ?_⟩
    rw [← hsx, ← hrs]
    exact IsFractionRing.semilinearEquivOfRingEquiv_algebraMap
      (FractionRing R) (FractionRing S) e r

end Transport

/-- The coordinate-ring ideal class attached to a degree-one place. -/
noncomputable def degreeOneClass
    (z : {v : PlaceA k K // placeDegree k K v = 1}) :
    ClassGroup W.CoordinateRing :=
  (ClassGroup.mulEquiv (coordinateRingEquivIntegers W K).toRingEquiv).symm
    (Additive.toMul <| finiteDivisorClass (k := k) K (Finsupp.single z.1 1))

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
lemma degreeOneClass_placeOfPoint (P : W.Point) :
    degreeOneClass W K ⟨placeOfPoint W K P, placeOfPoint_deg_one W K P⟩ =
      Additive.toMul (Point.toClass P) := by
  classical
  let e := (coordinateRingEquivIntegers W K).toRingEquiv
  cases P with
  | zero =>
      change (ClassGroup.mulEquiv e).symm
          (Additive.toMul (finiteDivisorClass (k := k) K
            (Finsupp.single (infinityPlace K) 1))) = 1
      rw [show infinityPlace K = Sum.inr (infinityHeightOne (k := k) K) from rfl,
        finiteDivisorClass_single_infinite]
      exact map_one (ClassGroup.mulEquiv e).symm
  | some x y h =>
      let u := affineHeightOne W h
      let v := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e u
      let I : (Ideal W.CoordinateRing)⁰ :=
        ⟨u.asIdeal, by
          rw [mem_nonZeroDivisors_iff_ne_zero]
          change u.asIdeal ≠ ⊥
          exact u.ne_bot⟩
      let J : (Ideal (ringOfIntegers k K))⁰ :=
        ⟨v.asIdeal, by
          rw [mem_nonZeroDivisors_iff_ne_zero]
          change v.asIdeal ≠ ⊥
          exact v.ne_bot⟩
      have hv : placeOfPoint W K (.some x y h) = Sum.inl v := rfl
      have hmap : J = ⟨I.1.map e,
          by
            rw [mem_nonZeroDivisors_iff_ne_zero]
            exact (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩ := by
        apply Subtype.ext
        change v.asIdeal = u.asIdeal.map e
        exact Ideal.comap_symm e
      change (ClassGroup.mulEquiv e).symm
          (Additive.toMul (finiteDivisorClass (k := k) K
            (Finsupp.single (Sum.inl v) 1))) =
        ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' h)
      rw [finiteDivisorClass_single_finite (k := k) K v]
      change (ClassGroup.mulEquiv e).symm
          (ClassGroup.mk K (FractionalIdeal.mk0 K J)) = _
      rw [ClassGroup.mk_mk0, hmap, ← classGroup_mulEquiv_mk0 e I,
        MulEquiv.symm_apply_apply]
      rw [← ClassGroup.mk_mk0 (K := W.FunctionField) I]
      congr 1
      apply Units.ext
      exact CoordinateRing.XYIdeal'_eq h

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
lemma degreeOneClass_injective :
    Function.Injective (degreeOneClass W K) := by
  intro z w hzw
  obtain ⟨P, hP⟩ := exists_point_of_place_degree_one W K z.1 z.2
  obtain ⟨Q, hQ⟩ := exists_point_of_place_degree_one W K w.1 w.2
  have hz : z = ⟨placeOfPoint W K P, placeOfPoint_deg_one W K P⟩ :=
    Subtype.ext hP
  have hw : w = ⟨placeOfPoint W K Q, placeOfPoint_deg_one W K Q⟩ :=
    Subtype.ext hQ
  subst z
  subst w
  apply Subtype.ext
  apply congrArg (placeOfPoint W K)
  apply Point.toClass_injective
  apply Additive.toMul.injective
  rw [← degreeOneClass_placeOfPoint W K P,
    ← degreeOneClass_placeOfPoint W K Q]
  exact hzw

lemma degreeOneClass_surjective :
    Function.Surjective (degreeOneClass W K) := by
  classical
  intro c
  let e := (coordinateRingEquivIntegers W K).toRingEquiv
  let cfin : ClassGroup (ringOfIntegers k K) := ClassGroup.mulEquiv e c
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective cfin
  let de := FractionalIdeal.divisorEquiv (R := ringOfIntegers k K) (K := K)
  let E : IsDedekindDomain.Divisor (ringOfIntegers k K) :=
    de (Additive.ofMul (FractionalIdeal.mk0 K J))
  let Dfin : DivisorA k K :=
    Finsupp.sumFinsuppAddEquivProdFinsupp.symm (E, 0)
  let D : DivisorA k K := Dfin +
    Finsupp.single (infinityPlace K) (1 - deg k K Dfin)
  have hdegD : deg k K D = 1 := by
    simp only [D, deg_add, deg_single, infinityPlace_deg_one W K]
    ring
  have hellD : ell k K D = 1 :=
    ell_eq_one_of_deg_one (k := k) (K := K)
      (divOmega_invariant_differential W K) D
      (genus_eq_one W K) hdegD
  obtain ⟨f, heff⟩ := exists_effective_add_principal_of_ell_pos
    (k := k) (K := K) D (by omega)
  let Deff := D + principalDivisorA k K (Additive.ofMul f)
  have hdegEff : deg k K Deff = 1 := by
    simp only [Deff, deg_add, hdegD, deg_principalDivisorA_eq_zero, add_zero]
  obtain ⟨v, hvdeg, hv⟩ :=
    eq_single_of_effective_deg_one (k := k) K heff hdegEff
  let z : {v : PlaceA k K // placeDegree k K v = 1} := ⟨v, hvdeg⟩
  refine ⟨z, ?_⟩
  have hclassDfin : finiteDivisorClass (k := k) K Dfin =
      Additive.ofMul cfin := by
    apply Additive.toMul.injective
    change ClassGroup.mk K
        (de.symm (finitePart (k := k) K Dfin)).toMul = cfin
    have hpart : finitePart (k := k) K Dfin = E := by
      simp [finitePart, Dfin]
    rw [hpart]
    change ClassGroup.mk K (de.symm (de
      (Additive.ofMul (FractionalIdeal.mk0 K J)))).toMul = cfin
    rw [de.symm_apply_apply]
    change ClassGroup.mk K (FractionalIdeal.mk0 K J) = cfin
    rw [ClassGroup.mk_mk0, hJ]
  have hclassD : finiteDivisorClass (k := k) K D = Additive.ofMul cfin := by
    simp only [D, map_add, hclassDfin]
    change Additive.ofMul cfin + finiteDivisorClass (k := k) K
      (Finsupp.single (Sum.inr (infinityHeightOne (k := k) K))
        (1 - deg k K Dfin)) = Additive.ofMul cfin
    rw [finiteDivisorClass_single_infinite, add_zero]
  have hclassSingle : finiteDivisorClass (k := k) K
      (Finsupp.single v 1) = Additive.ofMul cfin := by
    rw [← hv]
    simp only [map_add, finiteDivisorClass_principal K f,
      add_zero, hclassD]
  change (ClassGroup.mulEquiv e).symm
      (Additive.toMul (finiteDivisorClass (k := k) K
        (Finsupp.single v 1))) = c
  rw [hclassSingle]
  change (ClassGroup.mulEquiv e).symm cfin = c
  exact (ClassGroup.mulEquiv e).symm_apply_apply c

/-- The core equivalence between degree-one places and coordinate-ring ideal classes. -/
noncomputable def picTorsor' :
    {v : PlaceA k K // placeDegree k K v = 1} ≃ ClassGroup W.CoordinateRing :=
  Equiv.ofBijective (degreeOneClass W K)
    ⟨degreeOneClass_injective W K, degreeOneClass_surjective W K⟩

lemma picTorsor'_compat_groupLaw {x y : k} (h : W.Nonsingular x y) :
    picTorsor' W K ⟨placeOfPoint W K (Point.some x y h),
        placeOfPoint_deg_one W K (Point.some x y h)⟩ =
      ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' h) := by
  change degreeOneClass W K
      ⟨placeOfPoint W K (Point.some x y h),
        placeOfPoint_deg_one W K (Point.some x y h)⟩ = _
  rw [degreeOneClass_placeOfPoint W K]
  rfl

end Internal

end
end WeierstrassCurve.Affine.Chart
