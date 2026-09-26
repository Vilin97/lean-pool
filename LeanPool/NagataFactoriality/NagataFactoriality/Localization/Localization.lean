/-
Copyright (c) 2026 the authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
module

public import LeanPool.NagataFactoriality.NagataFactoriality.Localization.IsLocalization


/-!
# Localization

Supporting results for Nagata’s factoriality theorem.
-/

@[expose] public section

namespace NagataFactoriality

/-- Localization of a commutative ring at a multiplicative submonoid. -/
abbrev Localization {α : Type*} [CommRing α] (S : Submonoid α) := _root_.Localization S

namespace Localization

variable {α : Type*} [CommRing α] {S : Submonoid α}

/-- The fraction with the given numerator and denominator in the submonoid. -/
def mk (a s : α) (hs : s ∈ S) : Localization S :=
  _root_.Localization.mk a ⟨s, hs⟩

/-- The canonical map from the ring into its localization. -/
def of (a : α) : Localization S :=
  algebraMap α (Localization S) a

@[simp] theorem mk_one (a : α) : mk (S := S) a 1 S.one_mem = of (S := S) a := by
  unfold mk of
  convert (_root_.Localization.mk_one_eq_algebraMap (M := S) a) using 1

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
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (M := S) (S := Localization S) z
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
  simpa only [mk, _root_.Localization.mk_eq_mk'_apply] using
    (NagataFactoriality.IsLocalization.mk'_eq_iff (S := S) (β := Localization S) hs ht)

theorem of_eq_iff (a b : α) : of (S := S) a = of (S := S) b ↔ a = b :=
  (algebraMap_injective (S := S)).eq_iff

theorem mk_eq_zero_iff {a s : α} (hs : s ∈ S) : mk (S := S) a s hs = 0 ↔ a = 0 := by
  simp only [mk, _root_.Localization.mk_eq_mk'_apply,
    NagataFactoriality.IsLocalization.mk'_eq_zero_iff (S := S) (β := Localization S) hs]

@[simp] theorem of_eq_zero_iff (a : α) : of (S := S) a = 0 ↔ a = 0 := by
  change algebraMap α (Localization S) a = 0 ↔ a = 0
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
  simp [mk, of, _root_.Localization.mk_eq_mk'_apply]

@[simp] theorem mk_mul_of (a b s : α) (hs : s ∈ S) :
    mk (S := S) a s hs * of (S := S) b = mk (S := S) (a * b) s hs := by
  calc
    mk (S := S) a s hs * of (S := S) b =
        of (S := S) b * mk (S := S) a s hs := by rw [mul_comm]
    _ = mk (S := S) (b * a) s hs := of_mul_mk (S := S) b a s hs
    _ = mk (S := S) (a * b) s hs := by rw [mul_comm]

theorem isUnit_mk_of_mem {a s : α} (ha : a ∈ S) (hs : s ∈ S) :
    IsUnit (mk (S := S) a s hs) := by
  simpa only [mk, _root_.Localization.mk_eq_mk'_apply] using
    (NagataFactoriality.IsLocalization.isUnit_mk'_of_mem (β := Localization S) ha hs)

theorem isUnit_of_mem {s : α} (hs : s ∈ S) : IsUnit (of (S := S) s) := by
  simpa [of] using (IsLocalization.map_units (S := Localization S) ⟨s, hs⟩)

theorem isUnit_of_isUnit {a : α} (ha : IsUnit a) : IsUnit (of (S := S) a) :=
  ha.map (algebraMap α (Localization S))

theorem isUnit_mk_of_isUnit {a s : α} (ha : IsUnit a) (hs : s ∈ S) :
    IsUnit (mk (S := S) a s hs) := by
  simpa only [mk, _root_.Localization.mk_eq_mk'_apply] using
    (NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit (β := Localization S) ha hs)

section Nonzero

variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem dvd_of_iff {a b : α} :
    of (S := S) a ∣ of (S := S) b ↔ ∃ s : α, s ∈ S ∧ a ∣ s * b := by
  exact NagataFactoriality.IsLocalization.dvd_map_iff (S := S) (β := Localization S)

end Nonzero

end Localization

end NagataFactoriality
