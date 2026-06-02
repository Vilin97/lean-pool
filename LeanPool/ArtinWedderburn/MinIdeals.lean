/-
Copyright (c) 2026 Matevz Miščič, Maša Žaucer, Job Petrovčič. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matevz Miščič, Maša Žaucer, Job Petrovčič
-/
import LeanPool.ArtinWedderburn.SetProd
import LeanPool.ArtinWedderburn.CornerRing
import LeanPool.ArtinWedderburn.Auxiliary

/-!
# Minimal left ideals and idempotents

For a minimal (atom) left ideal `I` with `I * I ≠ 0`, this file extracts an
idempotent generator `e` of `I` and shows that the corner subring `eRe` is a
division subring.
-/

namespace LeanPool.ArtinWedderburn

variable {R : Type*} [Ring R]
variable (I J : Ideal R)

-- the set Ia
/-- The set `I * a = {x * a | x ∈ I}` as a subset of `R`. -/
def subIdealSet (I : Ideal R) (a : R) : Set R := {r | ∃ x ∈ I, r = x * a}

/-- The left ideal `I * a` consisting of elements `x * a` for `x ∈ I`. -/
def subIdeal (I : Ideal R) (a : R) : Ideal R :=
  { carrier := subIdealSet I a,
    zero_mem' := by
      refine ⟨0, ?_, ?_⟩
      · exact Submodule.zero_mem I
      · simp,
    add_mem' := by
      rintro x y ⟨r, hr, hx⟩ ⟨s, hs, hy⟩
      refine ⟨r + s, ?_, ?_⟩
      · exact I.add_mem hr hs
      · rw [hx, hy]
        noncomm_ring,
    smul_mem' := by
      rintro c x ⟨r, hr, hx⟩
      refine ⟨c * r, ?_, ?_⟩
      · exact I.smul_mem c hr
      · rw [hx]
        noncomm_ring }

theorem sub_ideal_le_ideal (I : Ideal R) (a : R) (h : a ∈ I) : subIdeal I a ≤ I := by
  rintro x ⟨r, _, ha⟩
  rw [ha]
  exact Ideal.mul_mem_left I r h

open Pointwise Set

-- IJ is nonzero, then there are x in I and y in J, such that x * y ≠ 0
theorem mul_ne_zero_imply_set_ne_zero (I J : Ideal R) (h : I * J ≠ ⊥) :
    ∃ x ∈ I, ∃ y ∈ J, x * y ≠ 0 := by
  have hnzz : ∃ z, z ∈ (↑I : Set R) * (↑J : Set R) ∧ z ≠ 0 :=
    not_subset.mp ((not_iff_not.mpr Ideal.span_eq_bot).mp h)
  obtain ⟨z, ⟨⟨x, ⟨hx, ⟨y, ⟨hy, hz⟩⟩⟩⟩, hnz⟩⟩ := hnzz
  refine ⟨x, hx, y, hy, ?_⟩
  simp only at hz
  rw [hz]
  exact hnz

-- if I*I is nonzero, then there is y in I, such that Iy is nonzero
theorem ideal_sq_ne_bot_imply_subideal_ne_bot (I : Ideal R) (h : I * I ≠ ⊥) :
    ∃ y ∈ I, subIdeal I y ≠ ⊥ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := mul_ne_zero_imply_set_ne_zero I I h
  refine ⟨y, hy, ?_⟩
  refine (Submodule.ne_bot_iff (subIdeal I y)).mpr ?_
  refine ⟨x * y, ⟨x, hx, rfl⟩, hxy⟩

-- if I*I is nonzero, then there is y in I, such that Iy is nonzero and y ≠ 0
theorem ideal_sq_ne_bot_imply_subideal_ne_bot2 (I : Ideal R) (h : I * I ≠ ⊥) :
    ∃ y ∈ I, y ≠ 0 ∧ subIdeal I y ≠ ⊥ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := mul_ne_zero_imply_set_ne_zero I I h
  refine ⟨y, hy, ?_, ?_⟩
  · intro hc
    apply hxy
    rw [hc]
    simp
  · refine (Submodule.ne_bot_iff (subIdeal I y)).mpr ?_
    refine ⟨x * y, ⟨x, hx, rfl⟩, hxy⟩

-- if I <= J and not I < J, then I = J
theorem le_and_not_lt_eq (I J : Ideal R) (h1 : I ≤ J) (h2 : ¬ (I < J)) : I = J := by
  rw [lt_iff_le_and_ne] at h2
  push Not at h2
  exact h2 h1

-- if I is an atom, then there exists a nonzero element y in I, such that subIdeal I y = I
theorem minimal_ideal_I_sq_nonzero_exists_el (hI : IsAtom I) (hII : I * I ≠ ⊥) :
    ∃ y : R, y ∈ I ∧ subIdeal I y = I := by
  obtain ⟨y, ⟨hy, hyI⟩⟩ := ideal_sq_ne_bot_imply_subideal_ne_bot I hII
  refine ⟨y, hy, ?_⟩
  obtain ⟨_, hsi⟩ := hI
  have h1 := sub_ideal_le_ideal I y hy
  have h2 := fun b => hyI (hsi (subIdeal I y) b)
  exact le_and_not_lt_eq (subIdeal I y) I h1 h2

-- if I is an atom, then there exists a nonzero element y in I, such that subIdeal I y = I and y
-- is nonzero
theorem minimal_ideal_I_sq_nonzero_exists_el2 (hI : IsAtom I) (hII : I * I ≠ ⊥) :
    ∃ y : R, y ∈ I ∧ y ≠ 0 ∧ subIdeal I y = I := by
  obtain ⟨y, ⟨hy, ynz, hyI⟩⟩ := ideal_sq_ne_bot_imply_subideal_ne_bot2 I hII
  refine ⟨y, hy, ynz, ?_⟩
  obtain ⟨_, hsi⟩ := hI
  have h1 := sub_ideal_le_ideal I y hy
  have h2 := fun b => hyI (hsi (subIdeal I y) b)
  exact le_and_not_lt_eq (subIdeal I y) I h1 h2

theorem minimal_ideal_I_sq_nonzero_exists_els2 (hI : IsAtom I) (hII : I * I ≠ ⊥) :
    ∃ y : R, y ∈ I ∧ y ≠ 0 ∧ subIdeal I y = I ∧ ∃ e ∈ I, e ≠ 0 ∧ y = e * y := by
  obtain ⟨y, ⟨hy, ynz, hI⟩⟩ := minimal_ideal_I_sq_nonzero_exists_el2 I hI hII
  refine ⟨y, hy, ynz, hI, ?_⟩
  rw [← hI] at hy
  obtain ⟨e, ⟨he, hey⟩⟩ := hy
  refine ⟨e, he, ?_, hey⟩
  by_contra hez
  have yz : y = 0 := by
    calc y = e * y := hey
      _ = 0 * y := by rw [hez]
      _ = 0 := by noncomm_ring
  contradiction

theorem minimal_ideal_I_sq_nonzero_exists_els (hI : IsAtom I) (hII : I * I ≠ ⊥) :
    ∃ y : R, y ∈ I ∧ subIdeal I y = I ∧ ∃ e ∈ I, y = e * y := by
  obtain ⟨y, ⟨hy, hI⟩⟩ := minimal_ideal_I_sq_nonzero_exists_el I hI hII
  refine ⟨y, hy, hI, ?_⟩
  rw [← hI] at hy
  obtain ⟨e, ⟨he, hey⟩⟩ := hy
  exact ⟨e, he, hey⟩

/-- The left ideal of elements in `I` that annihilate `a` on the right. -/
def elemAnn (I : Ideal R) (a : R) : Ideal R :=
  { carrier := {x | x ∈ I ∧ x * a = 0},
    zero_mem' := by simp,
    add_mem' := by
      rintro x y hx hy
      refine ⟨Submodule.add_mem I hx.1 hy.1, ?_⟩
      rw [right_distrib, hx.2, hy.2, add_zero],
    smul_mem' := by
      rintro c x ⟨hx, hxa⟩
      refine ⟨Submodule.smul_mem I c hx, ?_⟩
      simp [mul_assoc, hxa] }

theorem elem_ann_le_ideal (I : Ideal R) (a : R) : elemAnn I a ≤ I := by
  rintro x ⟨hx, _⟩
  exact hx

theorem e_semiidem (I : Ideal R) (e y : R) (he : e ∈ I) (h : e * y = y) :
    (e * e - e) ∈ (elemAnn I y) := by
  refine ⟨?_, ?_⟩
  · have hde : e * e - e = (e - 1) * e := by noncomm_ring
    rw [hde]
    exact Ideal.mul_mem_left I (e - 1) he
  · calc
      (e * e - e) * y = e * (e * y - y) := by noncomm_ring
      _ = 0 := by rw [h]; noncomm_ring

theorem strict_contain (I J : Ideal R) (hleq : I ≤ J) (hneq : ∃ x, x ∈ J ∧ x ∉ I) : I < J := by
  refine ⟨hleq, ?_⟩
  rintro heq
  obtain ⟨x, hxJ, hxnI⟩ := hneq
  apply heq at hxJ
  contradiction

theorem ideal_neq_bot_if_has_nonzero_el (I : Ideal R) (h : ∃ x ∈ I, x ≠ 0) : I ≠ ⊥ := by
  by_contra hI
  obtain ⟨x, hx, xnz⟩ := h
  rw [hI] at hx
  contradiction

theorem nonzero_ideal_in_min_ideal (I J : Ideal R) (atom_I : IsAtom I) (Jnz : J ≠ ⊥)
    (hJsubI : J ≤ I) : J = I := by
  by_contra hcon
  have hJltI : J < I := lt_of_le_of_ne hJsubI hcon
  have span_eq_bot : J = ⊥ := atom_I.right J hJltI
  contradiction

theorem minimal_ideal_I_sq_nonzero_exists_idem (h_atom_I : IsAtom I) (hII : I * I ≠ ⊥) :
    ∃ e : R, e ∈ I ∧ e ≠ 0 ∧ IsIdempotentElem e ∧ Ideal.span {e} = I := by
  obtain ⟨y, ⟨hy, ynz, hyI, ⟨e, he, henz, hey⟩⟩⟩ :=
    minimal_ideal_I_sq_nonzero_exists_els2 I h_atom_I hII
  obtain hye : e * y = y := Eq.symm hey
  obtain h12 := e_semiidem I e y he hye
  have hneq : ∃ x, x ∈ I ∧ x ∉ elemAnn I y := by
    refine ⟨e, he, ?_⟩
    intro hcon
    obtain ⟨_, hey0⟩ := hcon
    rw [hye] at hey0
    exact ynz hey0
  have h_ann_sub : elemAnn I y < I :=
    strict_contain (elemAnn I y) I (elem_ann_le_ideal I y) hneq
  have ann_zero : elemAnn I y = ⊥ := h_atom_I.2 (elemAnn I y) h_ann_sub
  refine ⟨e, he, henz, ?_, ?_⟩
  · unfold IsIdempotentElem
    rw [ann_zero] at h12
    calc
      e * e = (e * e - e) + e := by noncomm_ring
        _ = 0 + e := by rw [h12]
        _ = e := by abel
  · have span_neq_bot : Ideal.span {e} ≠ ⊥ := by
      by_contra hRe
      have einspane : e ∈ Ideal.span {e} := Ideal.mem_span_singleton_self e
      rw [hRe] at einspane
      contradiction
    by_contra hcon
    have hspanltI : (Ideal.span {e} : Ideal R) < I :=
      lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem I).mpr he) hcon
    have span_eq_bot : Ideal.span {e} = ⊥ := h_atom_I.right (Ideal.span {e}) hspanltI
    contradiction

-- Lemma 2.12
-- hypothesis: I^2 ≠ ⊥ and I is a minimal left ideal
-- conclusion: there exists an idempotent e in I such that I = Re and eRe is a Division Ring
theorem corner_ring_div (h_atom_I : IsAtom I) (e : R) (e_in_I : e ∈ I) (henz : e ≠ 0)
    (he_idem : IsIdempotentElem e) : IsDivisionSubring (CornerSubringNonUnital e) e := by
  refine ⟨⟨e, ?_, henz⟩, ?_⟩
  · exact ⟨e, by rw [he_idem, he_idem]⟩
  · intro x hx
    unfold CornerSubringNonUnital at hx
    obtain ⟨r, _, _⟩ := hx
    intro erenz
    have hsubI : leftIdealOfElement (e * r * e) ≤ I := by
      rintro x ⟨y, hy⟩
      have hx : x = (y * e * r) * e := by
        calc
          x = y * (e * r * e) := hy
          _ = (y * e * r) * e := by noncomm_ring
      rw [hx]
      exact Ideal.mul_mem_left I (y * e * r) e_in_I
    have hnz : leftIdealOfElement (e * r * e) ≠ ⊥ := by
      refine ideal_neq_bot_if_has_nonzero_el (leftIdealOfElement (e * r * e)) ?_
      refine ⟨e * r * e, ⟨1, by simp⟩, erenz⟩
    have heq : leftIdealOfElement (e * r * e) = I :=
      nonzero_ideal_in_min_ideal I (leftIdealOfElement (e * r * e)) h_atom_I hnz hsubI
    obtain ⟨s, hs⟩ := (Ideal.ext_iff.mp heq e).mpr e_in_I
    refine ⟨e * s * e, ⟨s, rfl⟩, ?_⟩
    calc (e * s * e) * (e * r * e) = e * s * (e * e) * r * e := by noncomm_ring
      _ = e * (s * (e * r * e)) := by rw [he_idem]; noncomm_ring
      _ = e := by rw [← hs, he_idem]

-- The lemma of this file
theorem minimal_ideal_I_sq_nonzero_exists_idem_and_div (h_atom_I : IsAtom I) (hII : I * I ≠ ⊥) :
    ∃ e : R, e ∈ I ∧ e ≠ 0 ∧ IsIdempotentElem e ∧ Ideal.span {e} = I ∧
      IsDivisionSubring (CornerSubringNonUnital e) e := by
  obtain ⟨e, ⟨he, henz, he_idem, hspan⟩⟩ :=
    minimal_ideal_I_sq_nonzero_exists_idem I h_atom_I hII
  refine ⟨e, he, henz, he_idem, hspan, ?_⟩
  have h_atom_span : IsAtom (Ideal.span {e}) := hspan ▸ h_atom_I
  have he_span : e ∈ Ideal.span {e} := Ideal.mem_span_singleton_self e
  exact corner_ring_div (Ideal.span {e}) h_atom_span e he_span henz he_idem

end LeanPool.ArtinWedderburn
