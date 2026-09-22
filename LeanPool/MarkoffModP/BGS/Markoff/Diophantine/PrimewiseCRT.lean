/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.Action
import Mathlib.Data.ZMod.QuotientRing

/-!
# Primewise puncturing and the Chinese remainder theorem

For a finite pairwise-coprime family of moduli, the Chinese remainder theorem identifies the
Markoff surface modulo their product with the product of the local Markoff surfaces.  There are
two different punctures on these objects:

* the naive puncture removes only the single global origin, and hence asks that *some* local
  component be nonzero;
* the primewise puncture used in Section 7 of Bourgain--Gamburd--Sarnak asks that *every* local
  component be nonzero.

This file keeps those carriers distinct and proves that CRT and all five standard Markoff moves
respect the primewise carrier.  No point-counting result is included here.
-/

namespace BGS.Markoff

universe u v

open scoped Function

/-- Apply a ring homomorphism coordinatewise to an affine point. -/
def Point.map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : Point R) : Point S :=
  ⟨f x.x1, f x.x2, f x.x3⟩

@[simp] theorem Point.map_x1 {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : Point R) : (x.map f).x1 = f x.x1 := rfl

@[simp] theorem Point.map_x2 {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : Point R) : (x.map f).x2 = f x.x2 := rfl

@[simp] theorem Point.map_x3 {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : Point R) : (x.map f).x3 = f x.x3 := rfl

@[simp] theorem Point.map_origin {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : (origin : Point R).map f = origin := by
  ext <;> simp [Point.map, origin]

@[simp] theorem markoffPolynomial_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : Point R) : markoffPolynomial (x.map f) = f (markoffPolynomial x) := by
  simp only [markoffPolynomial, Point.map, map_sub, map_add, map_mul, map_pow, map_ofNat]

/-- A ring equivalence transports affine three-space coordinatewise. -/
def pointRingEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Point R ≃ Point S where
  toFun := Point.map e
  invFun := Point.map e.symm
  left_inv x := by ext <;> simp [Point.map]
  right_inv x := by ext <;> simp [Point.map]

/-- A ring equivalence transports the original Markoff surface. -/
def markoffSurfaceRingEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) : MarkoffSurface R ≃ MarkoffSurface S where
  toFun x :=
    ⟨Point.map e.toRingHom x.val, by
      change markoffPolynomial (Point.map e.toRingHom x.val) = 0
      rw [markoffPolynomial_map, x.2, map_zero]⟩
  invFun x :=
    ⟨Point.map e.symm.toRingHom x.val, by
      change markoffPolynomial (Point.map e.symm.toRingHom x.val) = 0
      rw [markoffPolynomial_map, x.2, map_zero]⟩
  left_inv x := by apply Subtype.ext; exact (pointRingEquiv e).left_inv x.1
  right_inv x := by apply Subtype.ext; exact (pointRingEquiv e).right_inv x.1

@[simp] theorem coe_markoffSurfaceRingEquiv {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (e : R ≃+* S) (x : MarkoffSurface R) :
    ((markoffSurfaceRingEquiv e x : MarkoffSurface S) : Point S) =
      Point.map e.toRingHom x.1 := rfl

/-- A Markoff point over a product ring is the same thing as a family of local Markoff points. -/
def markoffSurfacePiEquiv {ι : Type*} {R : ι → Type u} [∀ i, CommRing (R i)] :
    MarkoffSurface (∀ i, R i) ≃ ∀ i, MarkoffSurface (R i) where
  toFun x i :=
    ⟨⟨x.1.x1 i, x.1.x2 i, x.1.x3 i⟩, by
      exact congrFun x.2 i⟩
  invFun x :=
    ⟨⟨fun i => (x i).1.x1, fun i => (x i).1.x2, fun i => (x i).1.x3⟩, by
      funext i
      exact (x i).2⟩
  left_inv x := by apply Subtype.ext; ext i <;> rfl
  right_inv x := by funext i; apply Subtype.ext; rfl

/-- CRT on the original Markoff surface, before imposing either notion of puncture. -/
noncomputable def markoffSurfaceCRTEquiv {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    MarkoffSurface (ZMod (∏ i, a i)) ≃ ∀ i, MarkoffSurface (ZMod (a i)) :=
  (markoffSurfaceRingEquiv (ZMod.prodEquivPi a coprime)).trans markoffSurfacePiEquiv

@[simp] theorem markoffSurfaceCRTEquiv_coordinate_one {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) (i : ι) :
    ((markoffSurfaceCRTEquiv a coprime x i : MarkoffSurface (ZMod (a i))) :
        Point (ZMod (a i))).x1 =
      ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) _ x.1.x1 := by
  exact ZMod.prodEquivPi_apply a coprime x.1.x1 i

@[simp] theorem markoffSurfaceCRTEquiv_coordinate_two {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) (i : ι) :
    ((markoffSurfaceCRTEquiv a coprime x i : MarkoffSurface (ZMod (a i))) :
        Point (ZMod (a i))).x2 =
      ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) _ x.1.x2 := by
  exact ZMod.prodEquivPi_apply a coprime x.1.x2 i

@[simp] theorem markoffSurfaceCRTEquiv_coordinate_three {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) (i : ι) :
    ((markoffSurfaceCRTEquiv a coprime x i : MarkoffSurface (ZMod (a i))) :
        Point (ZMod (a i))).x3 =
      ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) _ x.1.x3 := by
  exact ZMod.prodEquivPi_apply a coprime x.1.x3 i

@[simp] theorem markoffSurfaceCRTEquiv_origin {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a)) :
    markoffSurfaceCRTEquiv a coprime (surfaceOrigin (ZMod (∏ i, a i))) =
      fun i => surfaceOrigin (ZMod (a i)) := by
  funext i
  apply Subtype.ext
  ext <;> simp [surfaceOrigin, origin]

/-- A global point is naively punctured exactly when at least one CRT component is nonzero. -/
theorem ne_surfaceOrigin_iff_exists_crt_ne_surfaceOrigin {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) :
    x ≠ surfaceOrigin (ZMod (∏ i, a i)) ↔
      ∃ i, markoffSurfaceCRTEquiv a coprime x i ≠ surfaceOrigin (ZMod (a i)) := by
  constructor
  · contrapose!
    intro h
    apply (markoffSurfaceCRTEquiv a coprime).injective
    rw [markoffSurfaceCRTEquiv_origin]
    funext i
    exact h i
  · rintro ⟨i, hi⟩ rfl
    exact hi (congrFun (markoffSurfaceCRTEquiv_origin a coprime) i)

/-- The published Section 7 carrier: every local Markoff point is punctured. -/
abbrev PrimewisePuncturedMarkoffSurface {ι : Type*} (a : ι → ℕ) :=
  ∀ i, PuncturedMarkoffSurface (ZMod (a i))

/-- The primewise-puncture predicate on the single CRT residue ring. -/
def IsPrimewisePunctured {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) : Prop :=
  ∀ i, markoffSurfaceCRTEquiv a coprime x i ≠ surfaceOrigin (ZMod (a i))

/-- Global residue-ring presentation of the primewise-punctured carrier. -/
abbrev CRTPrimewisePuncturedMarkoffSurface {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :=
  {x : MarkoffSurface (ZMod (∏ i, a i)) // IsPrimewisePunctured a coprime x}

/-- CRT restricted to the primewise-punctured Markoff surface. -/
noncomputable def primewisePuncturedCRTEquiv {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    CRTPrimewisePuncturedMarkoffSurface a coprime ≃ PrimewisePuncturedMarkoffSurface a where
  toFun x i := ⟨markoffSurfaceCRTEquiv a coprime x.1 i, x.2 i⟩
  invFun x :=
    ⟨(markoffSurfaceCRTEquiv a coprime).symm (fun i => (x i).1), by
      intro i hi
      apply (x i).2
      have heq :=
        congrFun ((markoffSurfaceCRTEquiv a coprime).apply_symm_apply (fun j => (x j).1)) i
      exact heq.symm.trans hi⟩
  left_inv x := by
    apply Subtype.ext
    exact (markoffSurfaceCRTEquiv a coprime).symm_apply_apply x.1
  right_inv x := by
    funext i
    apply Subtype.ext
    exact congrFun ((markoffSurfaceCRTEquiv a coprime).apply_symm_apply (fun j => (x j).1)) i

/-- Every primewise-punctured global point is naively punctured, provided there is a local
factor.  The converse is false in general; see `exists_naivePunctured_not_primewisePunctured`. -/
def primewisePuncturedToNaive {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    CRTPrimewisePuncturedMarkoffSurface a coprime →
      PuncturedMarkoffSurface (ZMod (∏ i, a i)) :=
  fun x =>
    ⟨x.1, (ne_surfaceOrigin_iff_exists_crt_ne_surfaceOrigin a coprime x.1).2
      ⟨Classical.choice inferInstance, x.2 _⟩⟩

/-- The point `(1,1,1)` on the original Markoff surface. -/
def unitMarkoffPoint (R : Type u) [CommRing R] : MarkoffSurface R :=
  ⟨⟨1, 1, 1⟩, by
    simp only [IsMarkoff, markoffPolynomial]
    ring⟩

theorem unitMarkoffPoint_ne_surfaceOrigin {R : Type u} [CommRing R] [Nontrivial R] :
    unitMarkoffPoint R ≠ surfaceOrigin R := by
  intro h
  have := congrArg (fun x : MarkoffSurface R => x.1.x1) h
  change (1 : R) = 0 at this
  exact (one_ne_zero : (1 : R) ≠ 0) this

/-- With two distinct factors and one nontrivial local ring, the naive puncture is strictly
larger than the primewise puncture. -/
theorem exists_naivePunctured_not_primewisePunctured {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a)) {i j : ι} (hij : i ≠ j)
    (hj : a j ≠ 1) :
    ∃ x : PuncturedMarkoffSurface (ZMod (∏ k, a k)),
      ¬ IsPrimewisePunctured a coprime x.1 := by
  classical
  have : Nontrivial (ZMod (a j)) := ZMod.nontrivial_iff.mpr hj
  let localPoints : ∀ k, MarkoffSurface (ZMod (a k)) :=
    fun k => if k = i then surfaceOrigin (ZMod (a k)) else unitMarkoffPoint (ZMod (a k))
  let globalPoint := (markoffSurfaceCRTEquiv a coprime).symm localPoints
  have hglobal : globalPoint ≠ surfaceOrigin (ZMod (∏ k, a k)) := by
    apply (ne_surfaceOrigin_iff_exists_crt_ne_surfaceOrigin a coprime globalPoint).2
    refine ⟨j, ?_⟩
    rw [show markoffSurfaceCRTEquiv a coprime globalPoint j = localPoints j by
      exact congrFun ((markoffSurfaceCRTEquiv a coprime).apply_symm_apply localPoints) j]
    simp only [localPoints, ite_eq_right hij.symm]
    exact unitMarkoffPoint_ne_surfaceOrigin
  refine ⟨⟨globalPoint, hglobal⟩, ?_⟩
  intro hprimewise
  apply hprimewise i
  rw [show markoffSurfaceCRTEquiv a coprime globalPoint i = localPoints i by
    exact congrFun ((markoffSurfaceCRTEquiv a coprime).apply_symm_apply localPoints) i]
  simp [localPoints]

@[simp] theorem markoffSurfaceCRTEquiv_vieta1 {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) :
    markoffSurfaceCRTEquiv a coprime (vieta1SurfacePerm _ x) =
      fun i => vieta1SurfacePerm _ (markoffSurfaceCRTEquiv a coprime x i) := by
  funext i
  apply Subtype.ext
  have hdiv : a i ∣ ∏ k, a k := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  have hthree : (ZMod.cast (3 : ZMod (∏ k, a k)) : ZMod (a i)) = 3 :=
    ZMod.cast_natCast hdiv 3
  ext <;> simp [vieta1, ZMod.cast_sub hdiv, ZMod.cast_mul hdiv, hthree]

@[simp] theorem markoffSurfaceCRTEquiv_vieta2 {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) :
    markoffSurfaceCRTEquiv a coprime (vieta2SurfacePerm _ x) =
      fun i => vieta2SurfacePerm _ (markoffSurfaceCRTEquiv a coprime x i) := by
  funext i
  apply Subtype.ext
  have hdiv : a i ∣ ∏ k, a k := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  have hthree : (ZMod.cast (3 : ZMod (∏ k, a k)) : ZMod (a i)) = 3 :=
    ZMod.cast_natCast hdiv 3
  ext <;> simp [vieta2, ZMod.cast_sub hdiv, ZMod.cast_mul hdiv, hthree]

@[simp] theorem markoffSurfaceCRTEquiv_vieta3 {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) :
    markoffSurfaceCRTEquiv a coprime (vieta3SurfacePerm _ x) =
      fun i => vieta3SurfacePerm _ (markoffSurfaceCRTEquiv a coprime x i) := by
  funext i
  apply Subtype.ext
  have hdiv : a i ∣ ∏ k, a k := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  have hthree : (ZMod.cast (3 : ZMod (∏ k, a k)) : ZMod (a i)) = 3 :=
    ZMod.cast_natCast hdiv 3
  ext <;> simp [vieta3, ZMod.cast_sub hdiv, ZMod.cast_mul hdiv, hthree]

@[simp] theorem markoffSurfaceCRTEquiv_swap12 {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) :
    markoffSurfaceCRTEquiv a coprime (swap12SurfacePerm _ x) =
      fun i => swap12SurfacePerm _ (markoffSurfaceCRTEquiv a coprime x i) := by
  funext i
  apply Subtype.ext
  ext <;> simp [swap12]

@[simp] theorem markoffSurfaceCRTEquiv_swap23 {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) :
    markoffSurfaceCRTEquiv a coprime (swap23SurfacePerm _ x) =
      fun i => swap23SurfacePerm _ (markoffSurfaceCRTEquiv a coprime x i) := by
  funext i
  apply Subtype.ext
  ext <;> simp [swap23]

@[simp] theorem isPrimewisePunctured_vieta1_iff {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) :
    IsPrimewisePunctured a coprime (vieta1SurfacePerm _ x) ↔
      IsPrimewisePunctured a coprime x := by
  simp only [IsPrimewisePunctured, markoffSurfaceCRTEquiv_vieta1,
    vieta1SurfacePerm_ne_origin_iff]

@[simp] theorem isPrimewisePunctured_vieta2_iff {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) :
    IsPrimewisePunctured a coprime (vieta2SurfacePerm _ x) ↔
      IsPrimewisePunctured a coprime x := by
  simp only [IsPrimewisePunctured, markoffSurfaceCRTEquiv_vieta2,
    vieta2SurfacePerm_ne_origin_iff]

@[simp] theorem isPrimewisePunctured_vieta3_iff {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) :
    IsPrimewisePunctured a coprime (vieta3SurfacePerm _ x) ↔
      IsPrimewisePunctured a coprime x := by
  simp only [IsPrimewisePunctured, markoffSurfaceCRTEquiv_vieta3,
    vieta3SurfacePerm_ne_origin_iff]

@[simp] theorem isPrimewisePunctured_swap12_iff {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) :
    IsPrimewisePunctured a coprime (swap12SurfacePerm _ x) ↔
      IsPrimewisePunctured a coprime x := by
  simp only [IsPrimewisePunctured, markoffSurfaceCRTEquiv_swap12,
    swap12SurfacePerm_ne_origin_iff]

@[simp] theorem isPrimewisePunctured_swap23_iff {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : MarkoffSurface (ZMod (∏ i, a i))) :
    IsPrimewisePunctured a coprime (swap23SurfacePerm _ x) ↔
      IsPrimewisePunctured a coprime x := by
  simp only [IsPrimewisePunctured, markoffSurfaceCRTEquiv_swap23,
    swap23SurfacePerm_ne_origin_iff]

/-- The first global Vieta move restricted to the primewise-punctured CRT carrier. -/
noncomputable def vieta1CRTPrimewisePerm {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    Equiv.Perm (CRTPrimewisePuncturedMarkoffSurface a coprime) :=
  (vieta1SurfacePerm _).subtypeEquiv fun x => (isPrimewisePunctured_vieta1_iff a coprime x).symm

/-- The second global Vieta move restricted to the primewise-punctured CRT carrier. -/
noncomputable def vieta2CRTPrimewisePerm {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    Equiv.Perm (CRTPrimewisePuncturedMarkoffSurface a coprime) :=
  (vieta2SurfacePerm _).subtypeEquiv fun x => (isPrimewisePunctured_vieta2_iff a coprime x).symm

/-- The third global Vieta move restricted to the primewise-punctured CRT carrier. -/
noncomputable def vieta3CRTPrimewisePerm {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    Equiv.Perm (CRTPrimewisePuncturedMarkoffSurface a coprime) :=
  (vieta3SurfacePerm _).subtypeEquiv fun x => (isPrimewisePunctured_vieta3_iff a coprime x).symm

/-- The first coordinate swap restricted to the primewise-punctured CRT carrier. -/
noncomputable def swap12CRTPrimewisePerm {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    Equiv.Perm (CRTPrimewisePuncturedMarkoffSurface a coprime) :=
  (swap12SurfacePerm _).subtypeEquiv fun x => (isPrimewisePunctured_swap12_iff a coprime x).symm

/-- The second coordinate swap restricted to the primewise-punctured CRT carrier. -/
noncomputable def swap23CRTPrimewisePerm {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    Equiv.Perm (CRTPrimewisePuncturedMarkoffSurface a coprime) :=
  (swap23SurfacePerm _).subtypeEquiv fun x => (isPrimewisePunctured_swap23_iff a coprime x).symm

@[simp] theorem primewisePuncturedCRTEquiv_vieta1 {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : CRTPrimewisePuncturedMarkoffSurface a coprime) :
    primewisePuncturedCRTEquiv a coprime (vieta1CRTPrimewisePerm a coprime x) =
      fun i => vieta1PuncturedPerm _ (primewisePuncturedCRTEquiv a coprime x i) := by
  funext i
  apply Subtype.ext
  exact congrFun (markoffSurfaceCRTEquiv_vieta1 a coprime x.1) i

@[simp] theorem primewisePuncturedCRTEquiv_vieta2 {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : CRTPrimewisePuncturedMarkoffSurface a coprime) :
    primewisePuncturedCRTEquiv a coprime (vieta2CRTPrimewisePerm a coprime x) =
      fun i => vieta2PuncturedPerm _ (primewisePuncturedCRTEquiv a coprime x i) := by
  funext i
  apply Subtype.ext
  exact congrFun (markoffSurfaceCRTEquiv_vieta2 a coprime x.1) i

@[simp] theorem primewisePuncturedCRTEquiv_vieta3 {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : CRTPrimewisePuncturedMarkoffSurface a coprime) :
    primewisePuncturedCRTEquiv a coprime (vieta3CRTPrimewisePerm a coprime x) =
      fun i => vieta3PuncturedPerm _ (primewisePuncturedCRTEquiv a coprime x i) := by
  funext i
  apply Subtype.ext
  exact congrFun (markoffSurfaceCRTEquiv_vieta3 a coprime x.1) i

@[simp] theorem primewisePuncturedCRTEquiv_swap12 {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : CRTPrimewisePuncturedMarkoffSurface a coprime) :
    primewisePuncturedCRTEquiv a coprime (swap12CRTPrimewisePerm a coprime x) =
      fun i => swap12PuncturedPerm _ (primewisePuncturedCRTEquiv a coprime x i) := by
  funext i
  apply Subtype.ext
  exact congrFun (markoffSurfaceCRTEquiv_swap12 a coprime x.1) i

@[simp] theorem primewisePuncturedCRTEquiv_swap23 {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a))
    (x : CRTPrimewisePuncturedMarkoffSurface a coprime) :
    primewisePuncturedCRTEquiv a coprime (swap23CRTPrimewisePerm a coprime x) =
      fun i => swap23PuncturedPerm _ (primewisePuncturedCRTEquiv a coprime x i) := by
  funext i
  apply Subtype.ext
  exact congrFun (markoffSurfaceCRTEquiv_swap23 a coprime x.1) i

end BGS.Markoff
