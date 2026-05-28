/-
Copyright (c) 2026 Matevz Miščič, Maša Žaucer, Job Petrovčič. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matevz Miščič, Maša Žaucer, Job Petrovčič
-/
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import LeanPool.ArtinWedderburn.PrimeRing
import LeanPool.ArtinWedderburn.NonUnitalToUnital
import LeanPool.ArtinWedderburn.Auxiliary

/-!
# Corner subrings `eRe`

For an idempotent `e : R`, the *corner subring* `eRe` is the non-unital
subring of `R` consisting of elements of the form `e * x * e`. It becomes a
(unital) ring with `1 = e`. This file develops the basic theory: containment,
artinianness, primality, lifts and pushes of ideals, and isomorphisms between
corner subrings of equal idempotents.
-/

namespace LeanPool.ArtinWedderburn

variable {R : Type*} [Ring R]
variable {e : R}

/-- The carrier set of the corner ring `eRe`, defined as `{e * x * e | x : R}`. -/
def CornerRingSet (e : R) : Set R := both_mul e e

-- an element x of R is in the corner ring if and only if x = e * x * e
theorem corner_ring_set_mem {x : R} (idem_e : IsIdempotentElem e) :
    x ∈ CornerRingSet e ↔ x = e * x * e := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, idem_e]
    rw [← mul_assoc e x e, ← mul_assoc e (e * x) e, ← mul_assoc e e x, idem_e]
  · intro hx
    exact ⟨x, hx⟩

-- an element is in the set of corner ring if it can be written as e * y * e for some y
theorem x_in_corner_x_eq_e_y_e {x : R} (h : x ∈ CornerRingSet e) :
    ∃ (y : R), x = e * y * e := h

/-- The nonunital corner subring `eRe` as a `NonUnitalSubring`. -/
@[reducible]
def CornerSubringNonUnital (e : R) : NonUnitalSubring R where
  carrier := both_mul e e
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    use r + s
    rw [hr, hs]
    noncomm_ring
  neg_mem' := by
    rintro x ⟨r, hr⟩
    use -r
    rw [hr]
    noncomm_ring
  mul_mem' := by
    rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    use r * e * e * s
    rw [hr, hs]
    noncomm_ring

-- definition unfolding theorems
theorem corner_ring_carrier : (CornerSubringNonUnital e).carrier = both_mul e e := rfl

theorem el_in_corner_ring (x : R) : x ∈ both_mul e e ↔ x ∈ CornerSubringNonUnital e := Iff.rfl

-- reducing corner subring equality to set equality
theorem eq_carrier_eq_corner (x y : R) (h : both_mul x x = both_mul y y) :
    CornerSubringNonUnital x = CornerSubringNonUnital y := by
  apply NonUnitalSubring.ext
  simp only [← el_in_corner_ring, h, implies_true]

/-- The corner subring `eRe` packaged as a `NonUnitalSubring`, tagged with the
proof that `e` is idempotent. The proof argument lets later constructions
attach the unital ring structure on `eRe`. -/
@[reducible]
def CornerSubring (idem_e : IsIdempotentElem e) : NonUnitalSubring R :=
  have : IsIdempotentElem e := idem_e
  CornerSubringNonUnital e

theorem CornerSubringEq (idem_e idem_e' : IsIdempotentElem e) :
    CornerSubring idem_e = CornerSubring idem_e' := rfl

variable (idem_e : IsIdempotentElem e)

variable {x : R}

-- an element is in the corner subring if it stays the same when it is multiplied by e on both sides
theorem subring_mem_idem : x ∈ CornerSubring idem_e ↔ x = e * x * e := by
  rw [← corner_ring_set_mem]
  · rfl
  · exact idem_e

-- if x and y are in the corner ring, then so is x * w * y
-- note that e does not have to be an idempotent element
theorem corner_ring_both_mul_mem (x w y : R) (hx : x ∈ CornerSubringNonUnital e)
    (hy : y ∈ CornerSubringNonUnital e) : (x * w * y) ∈ CornerSubringNonUnital e := by
  have ⟨u, hx⟩ := hx
  have ⟨v, hy⟩ := hy
  use u * e * w * e * v
  rw [hx, hy]
  noncomm_ring

-- e is the left/right unit in the subring
theorem left_unit_mul (idem_e : IsIdempotentElem e) (h : x ∈ CornerSubringNonUnital e) :
    e * x = x := by
  rw [(corner_ring_set_mem idem_e).1 h]
  rw [← mul_assoc, ← mul_assoc, idem_e]

theorem right_unit_mul (idem_e : IsIdempotentElem e) (h : x ∈ CornerSubringNonUnital e) :
    x * e = x := by
  rw [(corner_ring_set_mem idem_e).1 h]
  rw [mul_assoc, mul_assoc, idem_e, mul_assoc]

open NonUnitalSubringClass

/-- The non-unital ring instance on the corner subring `eRe`. -/
abbrev CornerSubringIsNonUNitalRing := toNonUnitalRing (CornerSubringNonUnital e)

-- inclusion homomorphism of the corner subring
theorem corner_ring_hom (a b : CornerSubringNonUnital e) :
    (a * b : CornerSubringNonUnital e) = (a : R) * (b : R) := rfl

-- we can now start on adding the unit to the nonunital subring in the case when e is an idempotent
instance CornerRingOne (idem_e : IsIdempotentElem e) : One (CornerSubring idem_e) :=
  ⟨e, by rw [subring_mem_idem idem_e]; rw [idem_e, idem_e]⟩

theorem corner_ring_one (idem_e : IsIdempotentElem e) :
    (1 : CornerSubring idem_e) = e := rfl

-- e is the left/right unit but e is now written as 1
theorem is_left_unit : ∀ (x : CornerSubring idem_e), 1 * x = x := by
  rw [Subtype.forall]
  intro a hx
  apply Subtype.ext
  simp only [NonUnitalSubring.val_mul]
  rw [corner_ring_one, left_unit_mul idem_e hx]

theorem is_right_unit : ∀ (x : CornerSubring idem_e), x * 1 = x := by
  rw [Subtype.forall]
  intro a hx
  apply Subtype.ext
  simp only [NonUnitalSubring.val_mul]
  rw [corner_ring_one, right_unit_mul idem_e hx]

-- e is in the subring belonging to it
lemma e_in_corner_ring : e ∈ (CornerSubring idem_e) := by
  rw [subring_mem_idem]
  rw [IsIdempotentElem.eq idem_e, IsIdempotentElem.eq idem_e]

-- the underlying set of the corner subring defined by 1 is the whole ring
theorem both_mul_one_one_eq_R : both_mul (1 : R) 1 = ⊤ := by
  ext x
  constructor
  · intro ⟨_, _⟩
    trivial
  · intro _
    use x
    noncomm_ring

-- if a nonunital subring's carrier is R it is isomorphic to R
/-- A non-unital subring whose carrier is all of `R` is ring-isomorphic to `R`. -/
def top_subring_equiv_ring (S : NonUnitalSubring R) (h : S.carrier = ⊤) : S ≃+* R :=
  { toFun := fun a => a,
    invFun := fun a => ⟨a, by
      have ha : a ∈ S.carrier := by rw [h]; exact trivial
      exact ha⟩,
    left_inv := by intro a; simp
    right_inv := by intro a; simp
    map_mul' := by intro a b; simp
    map_add' := by intro a b; simp }

-- 1 R 1 is isomorphic to R
/-- The corner subring of `1` is ring-isomorphic to the ambient ring `R`. -/
def iso_corner_one :
    CornerSubring ((IsIdempotentElem.one : IsIdempotentElem (1 : R))) ≃+* R := by
  apply top_subring_equiv_ring
  unfold CornerSubring
  rw [corner_ring_carrier]
  exact both_mul_one_one_eq_R

-- a nonzero element in the corner subring is nonzero in R
lemma nonzero (x : CornerSubring idem_e) :
    (x : CornerSubring idem_e) ≠ 0 ↔ x.val ≠ 0 := by
  constructor
  · intro hnz hz
    apply hnz
    exact Subtype.ext hz
  · intro hnz hz
    rw [Subtype.ext_iff] at hz
    exact hnz hz

-- nonzero elements produces a non-zero corner subring
lemma e_nonzero_corner_nontrivial (R : Type*) [Ring R] {e : R} (idem_e : IsIdempotentElem e)
    (e_nonzero : e ≠ 0) : Nontrivial (CornerSubring idem_e) := by
  refine ⟨⟨⟨e, e_in_corner_ring idem_e⟩, 0, ?_⟩⟩
  exact (nonzero idem_e ⟨e, e_in_corner_ring idem_e⟩).mpr e_nonzero

lemma eq_iff_val (x y z : CornerSubring idem_e) :
    (x + y).val = z.val ↔ x.val + y.val = z.val := Eq.congr_right rfl

lemma e_x_e_in_corner : ∀ (x : R), e * x * e ∈ CornerSubring idem_e := by
  intro x
  rw [subring_mem_idem, eq_comm]
  calc _ = (e * e) * x * (e * e) := by noncomm_ring
        _ = e * x * e := by rw [idem_e]

-- The corner ring is a ring
instance CornerRingIsRing (idem_e : IsIdempotentElem e) : Ring (CornerSubring idem_e) :=
  non_unital_w_e_is_ring 1 (is_left_unit idem_e) (is_right_unit idem_e)

-- an element in the cornersubring of f (where f is in eRe) can be lifted to eRe
/-- Lift an element of the corner subring `fRf` (where `f` lies in `eRe`) to an element of
the outer corner subring `eRe`. -/
def coercion_to_eRe (e f : R) (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f)
    (f_mem : f ∈ CornerSubring idem_e) (x : CornerSubring idem_f) : CornerSubring idem_e := by
  refine ⟨x.val, ?_⟩
  have h : x.val ∈ both_mul e e := by
    let ⟨y, hy⟩ := f_mem
    let ⟨z, hz⟩ := x.property
    rw [hz, hy]
    refine ⟨y * e * z * e * y, ?_⟩
    noncomm_ring
  exact h

-- If eRe is a division ring then e is nonzero
lemma corner_ring_division_e_nonzero
    (idem_e : IsIdempotentElem e) (heRe : IsDivisionRing (CornerSubring idem_e)) : e ≠ 0 := by
  by_contra he
  have ha : ∀ (a : R), e * a * e = 0 := fun a ↦ mul_eq_zero_of_right (e * a) he
  have h_zero : ∀ (x : CornerSubring idem_e), x = 0 := by
    intro ⟨x, hx⟩
    apply x_in_corner_x_eq_e_y_e at hx
    obtain ⟨y, hy⟩ := hx
    specialize ha y
    rw [ha] at hy
    exact (NonUnitalSubring.coe_eq_zero_iff (CornerSubring idem_e)).mp hy
  obtain ⟨⟨x, hx⟩, _⟩ := heRe
  exact hx (h_zero x)

/-- If `e = f`, then the corner subrings `eRe` and `fRf` are ring-isomorphic via the
identity on carriers. -/
def eq_el_iso_corner (e f : R) (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f)
    (e_eq_f : e = f) : (CornerSubring idem_e) ≃+* (CornerSubring idem_f) :=
  { toFun := fun x => ⟨x.val, by
      let ⟨y, hy⟩ := x.property
      have h : x = (f : R) * y * f := by rw [← e_eq_f]; exact hy
      exact ⟨y, h⟩⟩,
    invFun := fun x => ⟨x.val, by
      let ⟨y, hy⟩ := x.property
      have h : x = (e : R) * y * e := by rw [e_eq_f]; exact hy
      exact ⟨y, h⟩⟩,
    left_inv := fun _ => rfl,
    right_inv := fun _ => rfl,
    map_mul' := fun _ _ => rfl,
    map_add' := fun _ _ => rfl }

/-- Equal idempotents induce a ring isomorphism between the matrix rings over their
corner subrings. -/
def equal_el_iso_matrix_rings' (e f : R) (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f)
    (e_eq_f : e = f) (n : ℕ) :
    Matrix (Fin n) (Fin n) (CornerSubring idem_e) ≃+*
      Matrix (Fin n) (Fin n) (CornerSubring idem_f) :=
  RingEquiv.mapMatrix (eq_el_iso_corner e f idem_e idem_f e_eq_f)

-- same element produce same Matrix rings over corner subrings
/-- Equal idempotents induce a ring isomorphism between matrix rings over their non-unital
corner subrings. -/
def equal_el_iso_matrix_rings (e f : R) (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f)
    (e_eq_f : e = f) (n : ℕ) :
    Matrix (Fin n) (Fin n) (CornerSubringNonUnital e) ≃+*
      Matrix (Fin n) (Fin n) (CornerSubringNonUnital f) := by
  let _ψ : (CornerSubringNonUnital e) ≃+* (CornerSubringNonUnital f) := by rw [e_eq_f]
  apply equal_el_iso_matrix_rings'
  · exact idem_e
  · exact idem_f
  · exact e_eq_f

-- coercions from Sets of CornerSubrings to Set of R
instance : CoeOut (Set (CornerSubring idem_e)) (Set R) :=
  { coe := fun X => Set.image Subtype.val X }

-- I left ideal in eRe -> RI is a left ideal in R
/-- Lift a (left) ideal of the corner subring `eRe` to a (left) ideal of `R` by taking the
`R`-span of its carrier. -/
def ideal_lift (I : Ideal (CornerSubring idem_e)) : Ideal R := Ideal.span (I.carrier)

-- coercion from Ideals of CornerSubrings to Ideals of R
instance : CoeOut (Ideal (CornerSubring idem_e)) (Ideal R) := { coe := ideal_lift idem_e }

-- I ⊆ J -> RI ⊆ RJ
theorem lift_monotonicity (I J : Ideal (CornerSubring idem_e)) :
    I ≤ J → (ideal_lift idem_e I) ≤ (ideal_lift idem_e J) := by
  intro I_leq_J
  apply Ideal.span_mono
  exact Set.image_mono I_leq_J

-- pushing an element into eRe: x |-> e x e
/-- Push an element `x : R` into the corner subring `eRe` via `x ↦ e * x * e`. -/
def el_push (x : R) : CornerSubring idem_e := ⟨e * x * e, e_x_e_in_corner idem_e x⟩

-- A left ideal I can be pushed down to eRe by eIe
/-- Push a (left) ideal of `R` down to a (left) ideal of `eRe` by taking the elementwise
image under `el_push`. -/
def ideal_push (idem_e : IsIdempotentElem e) (J : Ideal R) : Ideal (CornerSubring idem_e) where
  carrier := {el_push idem_e x | x ∈ J}
  zero_mem' := by
    refine ⟨0, Submodule.zero_mem J, ?_⟩
    apply Subtype.ext
    change e * 0 * e = (0 : R)
    noncomm_ring
  add_mem' := by
    rintro x y ⟨r, ⟨hr_mem, hr⟩⟩ ⟨s, ⟨hs_mem, hs⟩⟩
    refine ⟨r + s, (Submodule.add_mem_iff_right J hr_mem).mpr hs_mem, ?_⟩
    apply Subtype.ext
    change e * (r + s) * e = (x + y : CornerSubring idem_e).val
    rw [← hr, ← hs]
    change e * (r + s) * e = e * r * e + e * s * e
    noncomm_ring
  smul_mem' := by
    rintro ⟨c, ⟨a, hc⟩⟩ x ⟨r, ⟨hr_mem, hr⟩⟩
    refine ⟨a * e * e * r, Ideal.mul_mem_left J (a * e * e) hr_mem, ?_⟩
    apply Subtype.ext
    rw [← hr]
    simp only [smul_eq_mul, MulMemClass.mk_mul_mk, hc, el_push]
    noncomm_ring

-- pushing is an additive homomorphism
theorem add_el_push_eq_add (x y : R) :
    el_push idem_e x + el_push idem_e y = el_push idem_e (x + y) := by
  simp only [el_push]
  noncomm_ring
  simp only [AddMemClass.mk_add_mk]

-- multiplication by scalar keeps pushed element in ideal
lemma el_push_smul_in_I (a y : R) (I : Ideal (CornerSubring idem_e)) :
    y ∈ (I.carrier : Set R) → el_push idem_e (a • y) ∈ I := by
  intro hy
  obtain ⟨r, ⟨hr1, hr2⟩⟩ := hy
  obtain ⟨s, hs⟩ := r.2
  rw [← hr2]
  have h : e * (a • r) * e = (e * a * e) * r := by
    calc _ = e * a * r * e := by noncomm_ring
        _ = e * a * (e * s * e) * e := by rw [hs]
        _ = e * a * e * s * (e * e) := by noncomm_ring
        _ = e * a * (e * e) * s * e := by rw [idem_e, ← idem_e]
        _ = e * a * e * (e * s * e) := by noncomm_ring
        _ = (e * a * e) * r := by rw [← hs]
  let w : CornerSubring idem_e := ⟨e * a * e, e_x_e_in_corner idem_e a⟩
  have h' : w * r ∈ I := by
    have hr : r ∈ I := hr1
    exact Ideal.mul_mem_left I w hr
  let v : CornerSubring idem_e := el_push idem_e (a • r)
  have v_val : v.val = e * (a * r) * e := rfl
  have h'' : v = w * r := by
    rw [Subtype.ext_iff]
    rw [NonUnitalSubring.val_mul]
    simp only [v, w, el_push]
    exact h
  rw [← h''] at h'
  exact h'

-- if x in the lift of I then its push is in I
theorem ideal_push_pull_inclusion (I : Ideal (CornerSubring idem_e)) (x : R) :
    (x ∈ ideal_lift idem_e I) → (el_push idem_e x) ∈ I := by
  intro hx
  induction hx using Submodule.closure_induction with
  | zero =>
    have h0 : el_push idem_e 0 = (0 : CornerSubring idem_e) := by
      apply Subtype.ext
      change e * 0 * e = (0 : R)
      noncomm_ring
    rw [h0]
    exact I.zero_mem
  | add y z _ _ hyp hyz =>
    rw [← add_el_push_eq_add]
    exact (Submodule.add_mem_iff_right I hyp).mpr hyz
  | smul_mem a y hy => exact el_push_smul_in_I idem_e a y I hy

-- pushing and pulling an ideal brings us back to the same ideal
theorem push_pull (idem_e : IsIdempotentElem e) (I : Ideal (CornerSubring idem_e)) :
    ideal_push idem_e (ideal_lift idem_e I) = I := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy_mem, hy⟩⟩
    rw [← hy]
    exact ideal_push_pull_inclusion idem_e I y hy_mem
  · intro hx
    have h : (↑x : R) ∈ ideal_lift idem_e I := by
      unfold ideal_lift
      have hx1 : (↑x : R) ∈ (Subtype.val '' I.carrier : Set R) :=
        Set.mem_image_of_mem Subtype.val hx
      exact (Ideal.mem_span (↑x : R)).mpr fun _ a ↦ a hx1
    unfold ideal_push
    refine ⟨↑x, h, ?_⟩
    obtain ⟨y, hy⟩ := x.2
    have hx' : (↑x : R) ∈ CornerRingSet e := Subtype.coe_prop x
    apply (corner_ring_set_mem idem_e).1 at hx'
    unfold el_push
    symm
    exact SetLike.coe_eq_coe.mp hx'

theorem lift_strict_monotonicity (I J : Ideal (CornerSubring idem_e)) :
    I < J → (ideal_lift idem_e I) < (ideal_lift idem_e J) := by
  intro I_leq_J
  have I_neq_J : I ≠ J := ne_of_lt I_leq_J
  have lift_leq : (ideal_lift idem_e I) ≤ (ideal_lift idem_e J) :=
    lift_monotonicity idem_e I J (le_of_lt I_leq_J)
  have lift_neq : (ideal_lift idem_e I) ≠ (ideal_lift idem_e J) := by
    by_contra h_eq
    have h_eq : ideal_push idem_e (ideal_lift idem_e I) = ideal_push idem_e (ideal_lift idem_e J) :=
      congrArg (ideal_push idem_e) h_eq
    rw [push_pull, push_pull] at h_eq
    exact I_neq_J h_eq
  exact lt_of_le_of_ne lift_leq lift_neq

-- if the lift of an ideal is accesible then so is the ideal
theorem lift_acc_then_ideal_acc (idem_e : IsIdempotentElem e) (J : Ideal R)
    (h_J_is_lift : ∃ I3 : Ideal (CornerSubring idem_e), J = ideal_lift idem_e I3)
    (h_acc_J : Acc (fun x y => x < y) J) :
    Acc (fun x y => x < y) (ideal_push idem_e J) := by
  induction h_acc_J with
  | intro J2 _ hi =>
    obtain ⟨I, hI⟩ := h_J_is_lift
    rw [hI, push_pull idem_e I]
    have c1 : (I2 : Ideal (CornerSubring idem_e)) → I2 < I → Acc (fun x y => x < y) I2 := by
      intro I2 hI2
      rw [← push_pull idem_e I2]
      have subJ2 := (lift_strict_monotonicity idem_e I2 I) hI2
      rw [← hI] at subJ2
      exact hi (ideal_lift idem_e I2) subJ2 ⟨I2, rfl⟩
    exact Acc.intro I c1

-- Lemma 2.10
-- a) If R is artinian, then the corner ring is artinian
theorem corner_ring_artinian [h_ar : IsArtinian R R] :
    IsArtinian (CornerSubring idem_e) (CornerSubring idem_e) := by
  unfold IsArtinian at *
  unfold WellFoundedLT at *
  have Iacc : ∀ I : Ideal R, Acc (fun x y => x < y) I := fun I ↦ WellFounded.apply h_ar.wf I
  apply IsWellFounded.mk
  have allacc : ∀ I : Ideal (CornerSubring idem_e), Acc (fun x y => x < y) I := by
    intro I
    have h : Acc (fun x y => x < y) (ideal_push idem_e (ideal_lift idem_e I)) :=
      lift_acc_then_ideal_acc idem_e I ⟨I, rfl⟩ (Iacc (ideal_lift idem_e I))
    rw [push_pull idem_e I] at h
    exact h
  exact WellFounded.intro allacc

-- if we have two elements x y in the corners subring, then any element of the form x w y is
-- also in the corner
theorem corner_ring_both_mul_mem' (x y : CornerSubring idem_e) (w : R) :
    x * w * y ∈ CornerSubring idem_e := by
  apply corner_ring_both_mul_mem
  · exact x.property
  · exact y.property

-- if a and b in eRe, then a (e R e) b = a R b as sets
theorem both_mul_lift (x y : CornerSubring idem_e) :
    (both_mul (x : CornerSubring idem_e) y) = both_mul (x : R) (y : R) := by
  ext a
  constructor
  · rintro ⟨r, ⟨s, hs⟩, rfl⟩
    refine ⟨s, ?_⟩
    simp only [NonUnitalSubring.val_mul, hs]
  · rintro ⟨s, hs⟩
    rw [← is_right_unit idem_e ↑x, ← is_left_unit idem_e ↑y] at hs
    simp only [NonUnitalSubring.val_mul] at hs
    let sc : R := (1 : (CornerSubring idem_e)) * s * (1 : (CornerSubring idem_e))
    rw [← mul_assoc] at hs
    have ha : a = x * sc * y := by
      simp only [sc]
      rw [hs]
      simp only [mul_assoc]
    have hsc : sc ∈ CornerSubring idem_e := by
      simp only [sc]
      apply corner_ring_both_mul_mem'
    refine ⟨x * ⟨sc, hsc⟩ * y, ⟨⟨sc, hsc⟩, ?_⟩, ?_⟩
    · rfl
    · simp only [NonUnitalSubring.val_mul, ha]

-- b) If R is a prime ring, then the corner ring is prime
theorem corner_ring_prime (hRP : IsPrimeRing R) : IsPrimeRing (CornerSubring idem_e) := by
  rw [prime_ring_equiv]
  intro a b h
  have h_lift : ((both_mul a b) : Set R) = {0} := by
    rw [← both_mul_lift, congrArg (Set.image Subtype.val) h]
    exact Set.image_singleton
  have l := prime_ring_equiv.1 hRP _ _ h_lift
  simp only [ZeroMemClass.coe_eq_zero] at l
  exact l

-- if a cornersubring is a division subring then it is a division ring on its own
theorem div_subring_to_div_ring (e : R) (idem_e : IsIdempotentElem e)
    (h : IsDivisionSubring (CornerSubringNonUnital e) e) :
    IsDivisionRing (CornerSubring idem_e) := by
  obtain ⟨⟨a, ⟨a_mem, a_nz⟩⟩, h_inv⟩ := h
  have corner_nontrivial : Nontrivial (CornerSubring idem_e) := by
    refine ⟨⟨(⟨a, a_mem⟩ : CornerSubring idem_e),
      ⟨0, NonUnitalSubring.zero_mem (CornerSubring idem_e)⟩, ?_⟩⟩
    simp_all
  apply left_inv_implies_divring
  clear a a_mem a_nz
  intro x x_nz
  let ⟨y, ⟨y_mem, hy⟩⟩ := h_inv x (SetLike.coe_mem x) ((nonzero idem_e x).mp x_nz)
  refine ⟨⟨y, y_mem⟩, ?_⟩
  apply Subtype.ext
  exact hy

end LeanPool.ArtinWedderburn
