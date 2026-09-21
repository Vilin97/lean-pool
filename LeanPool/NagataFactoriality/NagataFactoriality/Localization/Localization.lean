/-
Copyright (c) 2026 Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
import Mathlib.RingTheory.Localization.Basic
import LeanPool.NagataFactoriality.NagataFactoriality.Localization.MultSet

namespace NagataFactoriality

abbrev Localization {α : Type*} [CommRing α] (S : Submonoid α) := _root_.Localization S

namespace Localization

variable {α : Type*} [CommRing α] {S : Submonoid α}

def mk (a s : α) (hs : s ∈ S) : Localization S :=
  _root_.Localization.mk a ⟨s, hs⟩

def of (a : α) : Localization S :=
  algebraMap α (Localization S) a

@[simp] theorem mk_one (a : α) : mk (S := S) a 1 S.one_mem = of (S := S) a := by
  simpa [mk, of] using (_root_.Localization.mk_one_eq_algebraMap (M := S) a)

@[simp] theorem of_zero : of (S := S) (0 : α) = 0 := by
  simp [of]

@[simp] theorem of_one : of (S := S) (1 : α) = 1 := by
  simp [of]

@[simp] theorem of_add (a b : α) : of (S := S) (a + b) = of (S := S) a + of (S := S) b := by
  simp [of]

@[simp] theorem of_mul (a b : α) : of (S := S) (a * b) = of (S := S) a * of (S := S) b := by
  simp [of]

@[simp] theorem of_neg (a : α) : of (S := S) (-a) = -of (S := S) a := by
  simp [of]

@[simp] theorem mk_mul_den (a s : α) (hs : s ∈ S) :
    mk (S := S) a s hs * of (S := S) s = of (S := S) a := by
  rw [mk, of, _root_.Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_spec_mk (M := S) (S := Localization S) a s hs

@[simp] theorem den_mul_mk (a s : α) (hs : s ∈ S) :
    of (S := S) s * mk (S := S) a s hs = of (S := S) a := by
  rw [mul_comm]
  exact mk_mul_den (S := S) a s hs

theorem surj (z : Localization S) : ∃ a s, ∃ hs : s ∈ S, z = mk (S := S) a s hs := by
  obtain ⟨a, s, hs⟩ := IsLocalization.mk'_surjective (M := S) (S := Localization S) z
  exact ⟨a, s, s.property, by
    simpa [mk, _root_.Localization.mk_eq_mk'_apply] using hs.symm⟩

section Nonzero

variable [IsDomain α] [Fact ((0 : α) ∉ S)]

instance : IsDomain (Localization S) :=
  IsLocalization.isDomain_localization (M := S) (Submonoid.le_nonZeroDivisors (S := S))

theorem algebraMap_injective : Function.Injective (algebraMap α (Localization S)) :=
  IsLocalization.injective (M := S) (S := Localization S) (Submonoid.le_nonZeroDivisors (S := S))

theorem mk_eq_iff {a b s t : α} (hs : s ∈ S) (ht : t ∈ S) :
    mk (S := S) a s hs = mk (S := S) b t ht ↔ a * t = b * s := by
  constructor
  · intro h
    have h' :
        algebraMap α (Localization S) (a * t) = algebraMap α (Localization S) (b * s) := by
      have h'' :
          IsLocalization.mk' (Localization S) a ⟨s, hs⟩ =
            IsLocalization.mk' (Localization S) b ⟨t, ht⟩ := by
        simpa [mk, _root_.Localization.mk_eq_mk'_apply] using h
      exact (IsLocalization.mk'_eq_iff_eq' (M := S) (S := Localization S)).1 h''
    exact algebraMap_injective (S := S) <|
      by simpa [map_mul, mul_assoc, mul_left_comm, mul_comm] using h'
  · intro h
    have h' :
        IsLocalization.mk' (Localization S) a ⟨s, hs⟩ =
          IsLocalization.mk' (Localization S) b ⟨t, ht⟩ := by
      exact IsLocalization.mk'_eq_of_eq' (M := S) (S := Localization S) <|
        by simpa [mul_assoc, mul_left_comm, mul_comm] using h.symm
    simpa [mk, _root_.Localization.mk_eq_mk'_apply] using h'

theorem of_eq_iff (a b : α) : of (S := S) a = of (S := S) b ↔ a = b :=
  (algebraMap_injective (S := S)).eq_iff

theorem mk_eq_zero_iff {a s : α} (hs : s ∈ S) : mk (S := S) a s hs = 0 ↔ a = 0 := by
  have h := mk_eq_iff (S := S) (a := a) (b := 0) (s := s) (t := 1) hs S.one_mem
  simpa [of] using h

@[simp] theorem of_eq_zero_iff (a : α) : of (S := S) a = 0 ↔ a = 0 := by
  show algebraMap α (Localization S) a = 0 ↔ a = 0
  exact IsLocalization.to_map_eq_zero_iff (M := S) (S := Localization S) (x := a)
    (Submonoid.le_nonZeroDivisors (S := S))

end Nonzero

@[simp] theorem mk_mul_mk {a b s t : α} (hs : s ∈ S) (ht : t ∈ S) :
    mk (S := S) a s hs * mk (S := S) b t ht =
      mk (S := S) (a * b) (s * t) (S.mul_mem hs ht) := by
  simpa [mk, _root_.Localization.mk_eq_mk'_apply] using
    (IsLocalization.mk'_mul (M := S) (S := Localization S) a b ⟨s, hs⟩ ⟨t, ht⟩).symm

@[simp] theorem of_mul_mk (a b s : α) (hs : s ∈ S) :
    of (S := S) a * mk (S := S) b s hs = mk (S := S) (a * b) s hs := by
  simpa [mk, of, _root_.Localization.mk_eq_mk'_apply] using
    (IsLocalization.mul_mk'_eq_mk'_of_mul (M := S) (S := Localization S) a b ⟨s, hs⟩)

@[simp] theorem mk_mul_of (a b s : α) (hs : s ∈ S) :
    mk (S := S) a s hs * of (S := S) b = mk (S := S) (a * b) s hs := by
  calc
    mk (S := S) a s hs * of (S := S) b =
        of (S := S) b * mk (S := S) a s hs := by rw [mul_comm]
    _ = mk (S := S) (b * a) s hs := of_mul_mk (S := S) b a s hs
    _ = mk (S := S) (a * b) s hs := by rw [mul_comm]

theorem isUnit_mk_of_mem {a s : α} (ha : a ∈ S) (hs : s ∈ S) :
    IsUnit (mk (S := S) a s hs) := by
  apply isUnit_iff_exists_inv.2
  refine ⟨mk (S := S) s a ha, ?_⟩
  simpa [mk, _root_.Localization.mk_eq_mk'_apply] using
    (IsLocalization.mk'_mul_mk'_eq_one' (M := S) (S := Localization S) a ⟨s, hs⟩ ha)

theorem isUnit_of_mem {s : α} (hs : s ∈ S) : IsUnit (of (S := S) s) := by
  simpa [of] using (IsLocalization.map_units (S := Localization S) ⟨s, hs⟩)

theorem isUnit_of_isUnit {a : α} (ha : IsUnit a) : IsUnit (of (S := S) a) :=
  ha.map (algebraMap α (Localization S))

theorem isUnit_mk_of_isUnit {a s : α} (ha : IsUnit a) (hs : s ∈ S) :
    IsUnit (mk (S := S) a s hs) := by
  have hmk : mk (S := S) a s hs = of (S := S) a * mk (S := S) 1 s hs := by
    calc
      mk (S := S) a s hs = mk (S := S) (a * 1) s hs := by simp
      _ = of (S := S) a * mk (S := S) 1 s hs := by
        rw [← of_mul_mk (S := S) a 1 s hs]
  rw [hmk]
  exact isUnit_mul (isUnit_of_isUnit (S := S) ha) (isUnit_mk_of_mem (S := S) S.one_mem hs)

section Nonzero

variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem dvd_of_iff {a b : α} :
    of (S := S) a ∣ of (S := S) b ↔ ∃ s : α, s ∈ S ∧ a ∣ s * b := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨c, s, hs, rfl⟩ := surj (S := S) x
    refine ⟨s, hs, ?_⟩
    have hEq : of (S := S) b = mk (S := S) (a * c) s hs := by
      calc
        of (S := S) b = of (S := S) a * mk (S := S) c s hs := hx
        _ = mk (S := S) (a * c) s hs := of_mul_mk (S := S) a c s hs
    have hCross :
        algebraMap α (Localization S) (b * s) = algebraMap α (Localization S) (a * c) := by
      have hCross' :
          of (S := S) b * algebraMap α (Localization S) s =
            algebraMap α (Localization S) (a * c) := by
        exact (IsLocalization.eq_mk'_iff_mul_eq (M := S) (S := Localization S)
          (z := of (S := S) b) (x := a * c) (y := ⟨s, hs⟩)).1 <|
            by simpa [mk, of, _root_.Localization.mk_eq_mk'_apply] using hEq
      simpa [of, map_mul, mul_assoc, mul_left_comm, mul_comm] using hCross'
    have hEq' : b * s = a * c := (algebraMap_injective (S := S)) hCross
    exact ⟨c, by simpa [mul_comm] using hEq'⟩
  · rintro ⟨s, hs, c, hc⟩
    refine ⟨mk (S := S) c s hs, ?_⟩
    symm
    calc
      of (S := S) a * mk (S := S) c s hs = mk (S := S) (a * c) s hs :=
        of_mul_mk (S := S) a c s hs
      _ = of (S := S) b := by
        apply (mk_eq_iff (S := S) (hs := hs) (ht := S.one_mem)).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hc.symm

end Nonzero

end Localization

end NagataFactoriality
