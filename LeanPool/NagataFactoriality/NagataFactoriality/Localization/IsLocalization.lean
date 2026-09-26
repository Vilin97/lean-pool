/-
Copyright (c) 2026 the authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
module

public import Mathlib.RingTheory.Localization.Basic
public import LeanPool.NagataFactoriality.NagataFactoriality.Localization.MultSet


/-!
# IsLocalization

Supporting results for Nagata’s factoriality theorem.
-/

@[expose] public section

namespace NagataFactoriality

namespace IsLocalization

variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]

theorem mk'_mul_map (a s : α) (hs : s ∈ S) :
    _root_.IsLocalization.mk' β a ⟨s, hs⟩ * algebraMap α β s = algebraMap α β a := by
  exact _root_.IsLocalization.mk'_spec_mk (M := S) (S := β) a s hs

@[simp] theorem map_mul_mk' (a b s : α) (hs : s ∈ S) :
    algebraMap α β a * _root_.IsLocalization.mk' β b ⟨s, hs⟩ =
      _root_.IsLocalization.mk' β (a * b) ⟨s, hs⟩ := by
  simpa using (_root_.IsLocalization.mul_mk'_eq_mk'_of_mul (M := S) (S := β) a b ⟨s, hs⟩)

theorem surj (z : β) : ∃ a s, ∃ hs : s ∈ S, z = _root_.IsLocalization.mk' β a ⟨s, hs⟩ := by
  obtain ⟨⟨a, s⟩, hs⟩ := _root_.IsLocalization.mk'_surjective (M := S) (S := β) z
  exact ⟨a, s, s.property, hs.symm⟩

section Nonzero

variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem algebraMap_injective (S : Submonoid α) [Fact ((0 : α) ∉ S)] [_root_.IsLocalization S β] :
    Function.Injective (algebraMap α β) :=
  let hle : S ≤ nonZeroDivisors α := NagataFactoriality.Submonoid.le_nonZeroDivisors
  _root_.IsLocalization.injective (M := S) (S := β) hle

theorem mk'_eq_iff {a b s t : α} (hs : s ∈ S) (ht : t ∈ S) :
    _root_.IsLocalization.mk' β a ⟨s, hs⟩ = _root_.IsLocalization.mk' β b ⟨t, ht⟩ ↔
      a * t = b * s := by
  constructor
  · intro h
    have h' := (_root_.IsLocalization.mk'_eq_iff_eq' (M := S) (S := β)).1 h
    exact algebraMap_injective (α := α) (β := β) S <| by
      simpa [map_mul, mul_assoc, mul_left_comm, mul_comm] using h'
  · intro h
    exact _root_.IsLocalization.mk'_eq_of_eq' (M := S) (S := β) <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h.symm

theorem map_eq_iff (S : Submonoid α) [Fact ((0 : α) ∉ S)] [_root_.IsLocalization S β] (a b : α) :
    algebraMap α β a = algebraMap α β b ↔ a = b :=
  (algebraMap_injective (α := α) (β := β) S).eq_iff

theorem mk'_eq_zero_iff {a s : α} (hs : s ∈ S) :
    _root_.IsLocalization.mk' β a ⟨s, hs⟩ = 0 ↔ a = 0 := by
  have h := mk'_eq_iff (S := S) (β := β) (a := a) (b := 0) (s := s) (t := 1) hs S.one_mem
  simpa using h

theorem map_eq_zero_iff (S : Submonoid α) [Fact ((0 : α) ∉ S)] [_root_.IsLocalization S β]
    (a : α) : algebraMap α β a = 0 ↔ a = 0 := by
  let hle : S ≤ nonZeroDivisors α := NagataFactoriality.Submonoid.le_nonZeroDivisors
  exact _root_.IsLocalization.to_map_eq_zero_iff (M := S) (S := β) (x := a) hle

theorem dvd_map_iff {a b : α} :
    algebraMap α β a ∣ algebraMap α β b ↔ ∃ s : α, s ∈ S ∧ a ∣ s * b := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨c, s, hs, rfl⟩ := surj (S := S) (β := β) x
    refine ⟨s, hs, ?_⟩
    have hEq : algebraMap α β b = _root_.IsLocalization.mk' β (a * c) ⟨s, hs⟩ := by
      calc
        algebraMap α β b = algebraMap α β a * _root_.IsLocalization.mk' β c ⟨s, hs⟩ := hx
        _ = _root_.IsLocalization.mk' β (a * c) ⟨s, hs⟩ := map_mul_mk' (S := S) a c s hs
    have hCross : algebraMap α β (b * s) = algebraMap α β (a * c) := by
      have hCross' :
          algebraMap α β b * algebraMap α β s = algebraMap α β (a * c) := by
        exact (_root_.IsLocalization.eq_mk'_iff_mul_eq (M := S) (S := β)
          (z := algebraMap α β b) (x := a * c) (y := ⟨s, hs⟩)).1 hEq
      simpa [map_mul, mul_assoc, mul_left_comm, mul_comm] using hCross'
    refine ⟨c, ?_⟩
    exact by simpa [mul_comm] using (algebraMap_injective (α := α) (β := β) S hCross)
  · rintro ⟨s, hs, c, hc⟩
    refine ⟨_root_.IsLocalization.mk' β c ⟨s, hs⟩, ?_⟩
    symm
    calc
      algebraMap α β a * _root_.IsLocalization.mk' β c ⟨s, hs⟩ =
          _root_.IsLocalization.mk' β (a * c) ⟨s, hs⟩ := map_mul_mk' (S := S) a c s hs
      _ = _root_.IsLocalization.mk' β b ⟨1, S.one_mem⟩ := by
        apply (mk'_eq_iff (S := S) (β := β) (hs := hs) (ht := S.one_mem)).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hc.symm
      _ = algebraMap α β b := by
        convert (_root_.IsLocalization.mk'_one (M := S) (S := β) b) using 1

end Nonzero

@[simp] theorem isUnit_mk'_of_mem {a s : α} (ha : a ∈ S) (hs : s ∈ S) :
    IsUnit (_root_.IsLocalization.mk' β a ⟨s, hs⟩) := by
  apply isUnit_iff_exists_inv.2
  refine ⟨_root_.IsLocalization.mk' β s ⟨a, ha⟩, ?_⟩
  simpa using (_root_.IsLocalization.mk'_mul_mk'_eq_one' (M := S) (S := β) a ⟨s, hs⟩ ha)

theorem isUnit_map_of_mem {s : α} (hs : s ∈ S) : IsUnit (algebraMap α β s) := by
  simpa using (_root_.IsLocalization.map_units (S := β) ⟨s, hs⟩)

theorem isUnit_map_of_isUnit {a : α} (ha : IsUnit a) : IsUnit (algebraMap α β a) :=
  ha.map (algebraMap α β)

theorem isUnit_mk'_of_isUnit {a s : α} (ha : IsUnit a) (hs : s ∈ S) :
    IsUnit (_root_.IsLocalization.mk' β a ⟨s, hs⟩) := by
  have hmk :
      _root_.IsLocalization.mk' β a ⟨s, hs⟩ =
        algebraMap α β a * _root_.IsLocalization.mk' β 1 ⟨s, hs⟩ := by
    calc
      _root_.IsLocalization.mk' β a ⟨s, hs⟩ = _root_.IsLocalization.mk' β (a * 1) ⟨s, hs⟩ := by simp
      _ = algebraMap α β a * _root_.IsLocalization.mk' β 1 ⟨s, hs⟩ := by
        rw [← map_mul_mk' (S := S) a 1 s hs]
  rw [hmk]
  exact (isUnit_map_of_isUnit (β := β) ha).mul (isUnit_mk'_of_mem (β := β) S.one_mem hs)

end IsLocalization

end NagataFactoriality
