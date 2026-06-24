/-
Copyright (c) 2026 Matevz Miščič, Maša Žaucer, Job Petrovčič. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matevz Miščič, Maša Žaucer, Job Petrovčič
-/
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotent
import LeanPool.ArtinWedderburn.PrimeRing
import LeanPool.ArtinWedderburn.SetProd
import LeanPool.ArtinWedderburn.CornerRing
import LeanPool.ArtinWedderburn.MinIdeals
import LeanPool.ArtinWedderburn.Auxiliary

/-!
# Orthogonal idempotents and matrix units

Develops orthogonal idempotents, builds matrix units from a system of pairwise
orthogonal idempotents whose corner rings are division rings, and packages the
data as `OrtIdem` / `OrtIdemDiv` structures.
-/

namespace LeanPool.ArtinWedderburn

variable {R : Type*} [Ring R]
variable (I J : Ideal R)
variable {e f : R}

/-- Two elements are orthogonal when their products in both orders vanish. -/
def IsOrthogonal (e f : R) : Prop := e * f = 0 ∧ f * e = 0

/-- `e` and `f` are orthogonal idempotents when each is idempotent and they are orthogonal. -/
def AreOrthogonalIdempotents (e f : R) : Prop :=
  IsIdempotentElem e ∧ IsIdempotentElem f ∧ IsOrthogonal e f

theorem leq_neq_lt (I J : Ideal R) : I ≤ J → I ≠ J → I < J := by
  intro hleq hneq
  refine ⟨hleq, ?_⟩
  intro heq
  have h : I = J := le_antisymm hleq heq
  trivial

-- Lemma 2.9
theorem one_sub_e_larger_span_on_sub_e_sub_f (e f : R)
    (ef_ort_idem : AreOrthogonalIdempotents e f) (fnz : f ≠ 0) :
    Ideal.span {1 - e - f} < Ideal.span {1 - e} := by
  have hleq : Ideal.span {1 - e - f} ≤ Ideal.span {1 - e} := by
    apply Ideal.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    rw [SetLike.mem_coe]
    have factor : (1 - e - f) * (1 - e) = 1 - e - f := by
      calc
        (1 - e - f) * (1 - e) = 1 - e - f - e + (e * e) + (f * e) := by noncomm_ring
        _ = 1 - e - f - e + e + 0 := by
          rw [ef_ort_idem.left, ef_ort_idem.right.right.right]
        _ = 1 - e - f := by noncomm_ring
    rw [Eq.symm factor]
    have in_span : 1 - e ∈ Ideal.span {1 - e} := Ideal.mem_span_singleton_self (1 - e)
    exact Ideal.mul_mem_left (Ideal.span {1 - e}) (1 - e - f) in_span
  have hneq : Ideal.span {1 - e - f} ≠ Ideal.span {1 - e} := by
    intro heq
    have f_in_ideal : f ∈ Ideal.span {1 - e} := by
      have fact_f : f = f * (1 - e) := by
        calc
          f = f - f * e := by rw [ef_ort_idem.right.right.right]; noncomm_ring
          _ = f * (1 - e) := by noncomm_ring
      rw [fact_f]
      exact Ideal.mul_mem_left (Ideal.span {1 - e}) f (Ideal.mem_span_singleton_self (1 - e))
    rw [← heq] at f_in_ideal
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp f_in_ideal
    have fz : f = 0 := by
      calc
        f = r * (1 - e - f) := by rw [hr]
        _ = r * (1 - e - f - f + e * f + f * f) := by
          rw [ef_ort_idem.right.right.left, ef_ort_idem.right.left]; noncomm_ring
        _ = r * (1 - e - f) * (1 - f) := by noncomm_ring
        _ = f - f * f := by rw [hr]; noncomm_ring
        _ = 0 := by rw [ef_ort_idem.right.left]; noncomm_ring
    contradiction
  exact leq_neq_lt (Ideal.span {1 - e - f}) (Ideal.span {1 - e}) hleq hneq

theorem e_span_larger_e_sub_f (e f : R) (h : AreOrthogonalIdempotents (1 - e) f) (fnz : f ≠ 0) :
    Ideal.span {e - f} < Ideal.span {e} := by
  have h' := one_sub_e_larger_span_on_sub_e_sub_f (1 - e) f h fnz
  simp only [sub_sub_cancel] at h'
  exact h'

/-- `R` has a system of `n × n` matrix units when there exist `n^2` elements `es i j`
summing to `1` on the diagonal and multiplying like matrix units. -/
def HasMatrixUnits (R : Type*) [Ring R] (n : ℕ) : Prop :=
  ∃ (es : Fin n → Fin n → R), (∑ i, es i i = 1) ∧
    (∀ i j k l, es i j * es k l = (if j = k then es i l else 0))

/-- Kronecker delta valued in `R`: equal to `1` when `i = j` and `0` otherwise. -/
def kroneckerDelta (n : ℕ) (i j : Fin n) : R := if i = j then 1 else 0

/-- Two elements are pairwise orthogonal when both of their products vanish. -/
def PairwiseOrthogonal (a b : R) : Prop := a * b = 0 ∧ b * a = 0

-- Lemma 2.18
theorem OrtIdem_imply_MatUnits {n : ℕ} (hn : 0 < n)
    (diag_es : Fin n → R)
    (idem : (∀ i : Fin n, IsIdempotentElem (diag_es i)))
    (ort : (∀ i j : Fin n, i ≠ j → PairwiseOrthogonal (diag_es i) (diag_es j)))
    (sum_eq_one : ∑ i, diag_es i = 1)
    (row_es : Fin n → R)
    (row_in : ∀ i : Fin n, row_es i ∈ bothMul (diag_es ⟨0, hn⟩) (diag_es i))
    (col_es : Fin n → R)
    (col_in : ∀ i : Fin n, col_es i ∈ bothMul (diag_es i) (diag_es ⟨0, hn⟩))
    (comp1 : ∀ i, row_es i * col_es i = diag_es ⟨0, hn⟩)
    (comp2 : ∀ i, col_es i * row_es i = diag_es i) : HasMatrixUnits R n := by
  refine ⟨fun i j => (col_es i) * (row_es j), ?_, ?_⟩
  · simp_rw [comp2]
    exact sum_eq_one
  · intro i j k l
    split_ifs with h
    · rw [h]
      have col_mul_diag : col_es i * diag_es ⟨0, hn⟩ = col_es i := by
        obtain ⟨r, hr⟩ := col_in i
        calc
          col_es i * diag_es ⟨0, hn⟩ = diag_es i * r * (diag_es ⟨0, hn⟩ * diag_es ⟨0, hn⟩) := by
            rw [hr]; noncomm_ring
          _ = diag_es i * r * diag_es ⟨0, hn⟩ := by rw [idem ⟨0, hn⟩]
          _ = col_es i := by rw [hr]
      calc
        (col_es i * row_es k) * (col_es k * row_es l) =
            col_es i * (row_es k * col_es k) * row_es l := by noncomm_ring
        _ = col_es i * diag_es ⟨0, hn⟩ * row_es l := by rw [comp1 k]
        _ = col_es i * row_es l := by rw [col_mul_diag]
    · obtain ⟨r, hr⟩ := row_in j
      obtain ⟨s, hs⟩ := col_in k
      calc
        (col_es i * row_es j) * (col_es k * row_es l) =
            col_es i *
              (diag_es ⟨0, hn⟩ * r * (diag_es j * diag_es k) * s * diag_es ⟨0, hn⟩) *
              row_es l := by rw [hr, hs]; noncomm_ring
        _ = 0 := by rw [(ort j k h).left]; noncomm_ring

-- If e and f are nonzero elements and R is prime then eRf contains nonzero element
lemma eRf_nonzero (h : IsPrimeRing R) (e f : R) (he : e ≠ 0) (hf : f ≠ 0) :
    ∃ (a : R), e * a * f ≠ 0 := by
  by_contra ha
  push Not at ha
  have eRf_zero : bothMul e f = {0} := by
    ext x
    constructor
    · intro ⟨r, hr⟩
      specialize ha r
      exact Set.mem_of_eq_of_mem hr ha
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      refine ⟨0, ?_⟩
      rw [hx]
      noncomm_ring
  apply prime_ring_equiv.1 h at eRf_zero
  cases eRf_zero with
  | inl h => exact he h
  | inr h => exact hf h

-- multiplication with e and f preserves bothMul e f
lemma both_mul_e_f (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f) :
    ∀ x ∈ bothMul e f, e * x = x ∧ x * f = x := by
  rintro x ⟨y, hy⟩
  have he : e * x = x := by
    calc _ = (e * e) * y * f := by rw [hy]; noncomm_ring
      _ = e * y * f := by rw [idem_e]
      _ = x := Eq.symm hy
  have hf : x * f = x := by
    calc _ = e * y * (f * f) := by rw [hy]; noncomm_ring
      _ = e * y * f := by rw [idem_f]
      _ = x := Eq.symm hy
  exact ⟨he, hf⟩

-- bothMul is closed for addition
lemma both_mul_add :
    ∀ (x y : R), x ∈ bothMul e f → y ∈ bothMul e f → x + y ∈ bothMul e f := by
  intro x y ⟨a, ha⟩ ⟨b, hb⟩
  use (a + b)
  rw [ha, hb]
  noncomm_ring

-- bothMul is closed for multiplication
lemma both_mul_neg : ∀ (x : R), x ∈ bothMul e f → -x ∈ bothMul e f := by
  intro x ⟨a, ha⟩
  use -a
  rw [ha]
  noncomm_ring

-- bothMul is closed for additive inverses
lemma both_mul_sub :
    ∀ (x y : R), x ∈ bothMul e f → y ∈ bothMul e f → x - y ∈ bothMul e f := by
  intro x y ⟨a, ha⟩ ⟨b, hb⟩
  use (a - b)
  rw [ha, hb]
  noncomm_ring

lemma both_mul_mul :
    ∀ (x y : R), x ∈ bothMul e f → y ∈ bothMul f e → x * y ∈ bothMul e e := by
  intro x y ⟨a, ha⟩ ⟨b, hb⟩
  use (a * f * f * b)
  rw [ha, hb]
  noncomm_ring

/-- Witnesses for the "nice idempotents" property: elements `u ∈ eRf`, `v ∈ fRe`
with `u * v = e` and `v * u = f`. -/
structure twoNiceIdempotents (e f : R) where
  /-- The element of `eRf` whose product with `v` recovers `e`. -/
  u : R
  /-- The element of `fRe` whose product with `u` recovers `f`. -/
  v : R
  u_mem : u ∈ bothMul e f
  v_mem : v ∈ bothMul f e
  u_mul_v : u * v = e
  v_mul_u : v * u = f

-- Lemma 2.19 (a)
theorem lemma_2_19 (h : IsPrimeRing R) (e f : R)
    (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f)
    (heRe : IsDivisionRing (CornerSubring idem_e))
    (hfRf : IsDivisionRing (CornerSubring idem_f)) :
    ∃ u v : R, u ∈ bothMul e f ∧ v ∈ bothMul f e ∧ u * v = e ∧ v * u = f := by
  have he : e ≠ 0 := corner_ring_division_e_nonzero idem_e heRe
  have hf : f ≠ 0 := corner_ring_division_e_nonzero idem_f hfRf
  have ha : ∃ (a : R), e * a * f ≠ 0 := eRf_nonzero h e f he hf
  obtain ⟨a, ha⟩ := ha
  have hb : ∃ (b : R), e * a * f * b * e ≠ 0 := eRf_nonzero h (e * a * f) e ha he
  obtain ⟨b, hb⟩ := hb
  have hx : e * a * f * b * e ∈ CornerSubring idem_e := by
    rw [subring_mem_idem, eq_comm]
    calc e * (e * a * f * b * e) * e = (e * e) * a * f * b * (e * e) := by noncomm_ring
      _ = e * a * f * b * e := by rw [IsIdempotentElem.eq idem_e]
      _ = e * a * f * b * e := rfl
  let x : CornerSubring idem_e := ⟨e * a * f * b * e, hx⟩
  have x_val_eq : x.val = e * a * f * b * e := rfl
  have x_nonzero : (x : CornerSubring idem_e) ≠ 0 := by
    rwa [nonzero, x_val_eq]
  have x_inv : ∃ (y : CornerSubring idem_e), x * y = (1 : CornerSubring idem_e) := by
    obtain ⟨_, h'⟩ := heRe
    specialize h' x x_nonzero
    obtain ⟨y, ⟨_, hy₂⟩⟩ := h'
    exact ⟨y, hy₂⟩
  obtain ⟨y, hy⟩ := x_inv
  let e_corner : CornerSubring idem_e := ⟨e, e_in_corner_ring idem_e⟩
  have hxy : x * y = (e_corner : R) := by
    rw [Subtype.ext_iff] at hy
    exact hy
  have hc : ∃ (c : R), y = e * c * e := x_in_corner_x_eq_e_y_e y.2
  obtain ⟨c, hc⟩ := hc
  have y_val_eq : y.val = e * c * e := hc
  let v := f * (b * e * c) * e
  let u := e * a * f
  have hv_mem : v ∈ bothMul f e := ⟨b * e * c, rfl⟩
  have uv_calc : u * v = e := by
    change e * a * f * (f * (b * e * c) * e) = e
    have h1 : e * a * f * (f * (b * e * c) * e) = e * a * (f * f) * b * e * c * e := by
      noncomm_ring
    have h2 : e * a * (f * f) * b * e * c * e = e * a * f * b * e * c * e := by
      rw [IsIdempotentElem.eq idem_f]
    have h3 : (e * a * f * b * e) * (e * c * e) = e * a * f * b * (e * e) * c * e := by
      noncomm_ring
    have h4 : e * a * f * b * (e * e) * c * e = e * a * f * b * e * c * e := by
      rw [IsIdempotentElem.eq idem_e]
    calc e * a * f * (f * (b * e * c) * e)
        = e * a * f * b * e * c * e := by rw [h1, h2]
      _ = (e * a * f * b * e) * (e * c * e) := by rw [h3, h4]
      _ = x * y := by rw [x_val_eq, y_val_eq]
      _ = e := hxy
  refine ⟨u, v, ?_, hv_mem, uv_calc, ?_⟩
  · exact ⟨a, rfl⟩
  · have hu : u ∈ bothMul e f := ⟨a, rfl⟩
    have hv : v ∈ bothMul f e := hv_mem
    have fv_eq_v : f * v = (v : R) := (both_mul_e_f idem_f idem_e v hv).1
    have ve_eq_v : v * e = v := (both_mul_e_f idem_f idem_e v hv).2
    have uv_eq_e : u * v = e := uv_calc
    have vuv_eq_v : v * u * v = v := by
      calc _ = v * (u * v) := by noncomm_ring
        _ = v * e := by rw [uv_eq_e]
        _ = v := ve_eq_v
    by_contra h_neq
    push Not at h_neq
    have h_nonzero : v * u - f ≠ 0 := sub_ne_zero_of_ne h_neq
    have h_mem : v * u - f ∈ CornerSubring idem_f := by
      apply both_mul_sub
      · apply both_mul_mul
        · exact hv
        · exact hu
      · exact e_in_corner_ring idem_f
    let w : CornerSubring idem_f := ⟨v * u - f, h_mem⟩
    have w_val_eq : w.val = v * u - f := rfl
    have ⟨a, ha⟩ : ∃ (a : CornerSubring idem_f), a * w = (1 : CornerSubring idem_f) := by
      obtain ⟨a, ⟨h1, _⟩⟩ := hfRf.2 w (by rw [nonzero]; exact h_nonzero)
      exact ⟨a, h1⟩
    have wv_eq_zero : w * v = 0 := by
      calc _ = (v * u - f) * v := rfl
        _ = v * u * v - f * v := by noncomm_ring
        _ = 0 := by rw [vuv_eq_v, fv_eq_v]; simp
    have v_eq_zero : v = 0 := by
      calc _ = (1 : CornerSubring idem_f) * v := Eq.symm fv_eq_v
        _ = (a * w) * v := by rw [← ha]; simp
        _ = a * (w * v) := by noncomm_ring
        _ = 0 := by rw [wv_eq_zero]; simp
    have e_eq_zero : e = 0 := by
      calc _ = u * v := by rw [uv_eq_e]
        _ = 0 := by rw [v_eq_zero]; noncomm_ring
    exact he e_eq_zero

/-- Packaging of `lemma_2_19` as a `twoNiceIdempotents` structure. -/
noncomputable
def lemma219' (h : IsPrimeRing R) (e f : R)
    (idem_e : IsIdempotentElem e) (idem_f : IsIdempotentElem f)
    (heRe : IsDivisionRing (CornerSubring idem_e))
    (hfRf : IsDivisionRing (CornerSubring idem_f)) : twoNiceIdempotents e f := by
  have h := lemma_2_19 h e f idem_e idem_f heRe hfRf
  choose u v hu hv h1 h2 using h
  exact
    { u := u,
      v := v,
      u_mem := hu,
      v_mem := hv,
      u_mul_v := h1,
      v_mul_u := h2 }

theorem f_in_corner_othogonal (e f : R) (idem_e : IsIdempotentElem e)
    (f_mem : f ∈ bothMul (1 - e) (1 - e)) : IsOrthogonal e f := by
  obtain ⟨x, hx⟩ := f_mem
  refine ⟨?_, ?_⟩
  · rw [hx]
    calc _ = (e - e * e) * x * (1 - e) := by noncomm_ring
      _ = (e - e) * x * (1 - e) := by rw [idem_e]
      _ = 0 := by noncomm_ring
  · rw [hx]
    calc _ = (1 - e) * x * (e - e * e) := by noncomm_ring
      _ = (1 - e) * x * (e - e) := by rw [idem_e]
      _ = 0 := by noncomm_ring

lemma e_idem_to_e_val_idem {e : R} {idem_e : IsIdempotentElem e}
    {x : CornerSubring idem_e} (idem_x : IsIdempotentElem x) : IsIdempotentElem x.val := by
  have pl := congrArg Subtype.val idem_x
  simp only [NonUnitalSubring.val_mul] at pl
  exact pl

lemma sum_orthogonal_idem_is_idem (e f : R) (h : AreOrthogonalIdempotents e f) :
    IsIdempotentElem (e + f) := by
  let ⟨idem_e, idem_f, h1, h2⟩ := h
  calc
    (e + f) * (e + f) = e * e + e * f + f * e + f * f := by noncomm_ring
    _ = e + 0 + 0 + f := by rw [idem_e, idem_f, h1, h2]
    _ = e + f := by simp

lemma prod_orthogonal_idem_is_idem (e f : R) (_idem_e : IsIdempotentElem e)
    (idem_f : IsIdempotentElem f) (h : IsOrthogonal e f) :
    IsIdempotentElem (f * (1 - e)) := by
  unfold IsIdempotentElem
  calc _ = (f - (f * e)) * (f - (f * e)) := by noncomm_ring
    _ = f * f := by rw [h.2]; noncomm_ring
    _ = f - 0 := by rw [idem_f]; exact Eq.symm (sub_zero f)
    _ = f - f * e := by rw [h.2]
    _ = f * (1 - e) := Eq.symm (mul_one_sub f e)

lemma e_f_orhogonal_f_1_sub_e_eq_f (e f : R) (h : IsOrthogonal e f) :
    f * (1 - e) = f := by
  calc _ = f - f * e := by noncomm_ring
    _ = f := by rw [h.2]; noncomm_ring

lemma f_mem_corner_e_e_sub_f_idem (e : R) (idem_e : IsIdempotentElem e)
    (f : CornerSubring idem_e) (idem_f : IsIdempotentElem f) :
    IsIdempotentElem (e - f) := by
  have idem_one_sub_e : IsIdempotentElem (1 - e) := IsIdempotentElem.one_sub idem_e
  have one_sub_e_f_orthogonal : IsOrthogonal (1 - e) f :=
    f_in_corner_othogonal (1 - e) f idem_one_sub_e (by simp)
  have ef_eq_f : e * f = f := left_unit_mul idem_e f.property
  unfold IsIdempotentElem
  calc _ = (e * e) - e * f + (f * f) - f * e := by noncomm_ring
    _ = e - f + f - f * e := by rw [idem_e, ef_eq_f, (e_idem_to_e_val_idem idem_f)]
    _ = e - f + f * (1 - e) := by noncomm_ring
    _ = e - f := by rw [one_sub_e_f_orthogonal.2]; noncomm_ring

lemma ort_comm (e f : R) (ort : IsOrthogonal e f) : IsOrthogonal f e := by
  unfold IsOrthogonal at *
  rwa [and_comm]

lemma orth_coercion (e : R) (idem_e : IsIdempotentElem e) (x y : CornerSubring idem_e)
    (ort : IsOrthogonal x y) : IsOrthogonal x.val y.val := by
  let ⟨h1, h2⟩ := ort
  refine ⟨?_, ?_⟩
  · exact (AddSubmonoid.mk_eq_zero (CornerSubring idem_e).toAddSubmonoid).mp h1
  · exact (AddSubmonoid.mk_eq_zero (CornerSubring idem_e).toAddSubmonoid).mp h2

lemma iso_idem_to_idem (R' : Type*) [Ring R'] (φ : R ≃+* R') (e : R)
    (idem_e : IsIdempotentElem e) : IsIdempotentElem (φ e) := by
  unfold IsIdempotentElem at *
  rw [← RingEquiv.map_mul, idem_e]

lemma iso_orthogonal_to_orthogonal (R' : Type*) [Ring R'] (φ : R ≃+* R') (x y : R)
    (ort : IsOrthogonal x y) : IsOrthogonal (φ x) (φ y) := by
  let ⟨h1, h2⟩ := ort
  refine ⟨?_, ?_⟩
  · rw [← RingEquiv.map_mul, h1, RingEquiv.map_eq_zero_iff]
  · rw [← RingEquiv.map_mul, h2, RingEquiv.map_eq_zero_iff]

-- lemma 2.14
theorem artinian_ring_has_minimal_left_ideal_of_element [IsArtinian R R] [Nontrivial R] :
    ∃ I : Ideal R, IsAtom I := IsAtomic.exists_atom (Ideal R)

-- obtain an element to extend OrtIdem
theorem prime_and_artinian_esists_idem_corner_div [Nontrivial R]
    (h : IsPrimeRing R) (h' : IsArtinian R R) :
    ∃ (e : R), e ≠ 0 ∧ IsIdempotentElem e ∧ IsDivisionSubring (CornerSubringNonUnital e) e := by
  have ⟨I, hI⟩ : ∃ I : Ideal R, IsAtom I := artinian_ring_has_minimal_left_ideal_of_element
  have I_sq_nonzero : I * I ≠ ⊥ := by
    specialize h I I
    by_contra I_sq_zero
    specialize h I_sq_zero
    let I_neq_zero := hI.1
    have I_eq_zero : I = ⊥ := by aesop
    contradiction
  obtain ⟨e, _he_mem, henz, he_idem, _hspan, hdiv⟩ :=
    minimal_ideal_I_sq_nonzero_exists_idem_and_div I hI I_sq_nonzero
  exact ⟨e, henz, he_idem, hdiv⟩

/-- A finite system of pairwise orthogonal idempotents of `R` summing to `1`. -/
structure OrtIdem (R : Type*) [Ring R] where
  /-- Number of idempotents in the system. -/
  n : ℕ
  /-- The idempotents indexed by `Fin n`. -/
  f : Fin n → R
  h : (i : Fin n) → IsIdempotentElem (f i)
  sum_one : ∑ i, f i = 1
  orthogonal : ∀ i j, i ≠ j → IsOrthogonal (f i) (f j)

/-- An `OrtIdem` whose corner rings are all division rings. -/
structure OrtIdemDiv (R : Type*) [Ring R] extends OrtIdem R where
  div : ∀ i, IsDivisionRing (CornerSubring (h i))

-- A ring, isomorphic to OrtIdem ring, is itself OrtIdem
/-- Transport an `OrtIdem R` along a ring isomorphism `φ : R ≃+* R'`. -/
def isomorphicOrtIdem (R' : Type*) [Ring R'] (φ : R ≃+* R') (hoi : OrtIdem R) : OrtIdem R' :=
  { n := hoi.n,
    f := fun i => φ (hoi.f i),
    h := fun i => iso_idem_to_idem R' φ (hoi.f i) (hoi.h i)
    sum_one :=
      calc ∑ x : Fin hoi.n, φ (hoi.f x) = φ (∑ x : Fin hoi.n, (hoi.f x)) :=
            Eq.symm (RingEquiv.map_sum φ hoi.f Finset.univ)
        _ = φ (1) := by rw [hoi.sum_one]
        _ = 1 := RingEquiv.map_one φ
    orthogonal := fun i j hij => by
      apply iso_orthogonal_to_orthogonal
      exact hoi.orthogonal i j hij }

-- canonical isomorphism between corner rings
/-- A ring isomorphism `φ : R ≃+* R'` induces a ring isomorphism between the corner rings
of an idempotent and of its image under `φ`. -/
def ringIsoToCornerIso (R' : Type*) [Ring R'] (φ : R ≃+* R') (e : R)
    (idem_e : IsIdempotentElem e) :
    CornerSubring idem_e ≃+* CornerSubring (iso_idem_to_idem R' φ e idem_e) :=
  { toFun := fun x => ⟨φ x.val, by
      rw [subring_mem_idem]
      have hx : x = e * x * e := by
        apply (corner_ring_set_mem idem_e).mp
        exact Subtype.coe_prop x
      have hx' : φ x = φ (e * x * e) := congrArg (⇑φ) hx
      rw [RingEquiv.map_mul, RingEquiv.map_mul] at hx'
      exact hx'⟩,
    invFun := fun y => ⟨φ.symm y.val, by
      have h : y = φ e * y * φ e := by
        apply (corner_ring_set_mem ?idem_e).mp
        simp
      rw [h]
      have h' : φ.symm (φ e * ↑y * φ e) = e * φ.symm ↑y * e := by
        rw [RingEquiv.map_mul, RingEquiv.map_mul]
        rw [RingEquiv.symm_apply_apply φ e]
      exact ⟨φ.symm ↑y, by simp⟩⟩,
    left_inv := fun ⟨x, hx⟩ => by simp,
    right_inv := fun ⟨x, hx⟩ => by simp,
    map_mul' := by intro x y; simp,
    map_add' := by intro x y; simp }

-- A ring, isomorphic to OrtIdemDiv ring, is itself OrtIdemDiv
/-- Transport an `OrtIdemDiv R` along a ring isomorphism `φ : R ≃+* R'`. -/
def isomorphicOrtIdemDiv {R' : Type*} [Ring R'] (φ : R ≃+* R') (hoi : OrtIdemDiv R) :
    OrtIdemDiv R' :=
  { toOrtIdem := isomorphicOrtIdem R' φ hoi.toOrtIdem,
    div := fun i => by
      let ψ : (CornerSubring (hoi.h i)) ≃+*
        (CornerSubring ((isomorphicOrtIdem R' φ hoi.toOrtIdem).h i)) :=
        ringIsoToCornerIso R' φ (hoi.f i) (hoi.h i)
      apply isomorphic_ring_div ψ (hoi.div i) }

end LeanPool.ArtinWedderburn
