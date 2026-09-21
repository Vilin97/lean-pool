/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.GroupTheory.OrderOfElement
/-!
# Rigidity from a cyclic quotient and subgroup data

A finite abelian quotient is determined by its action on all intermediate
subgroups together with its action on a sufficiently large cyclic quotient.
The group-theoretic statement below isolates the part of uniqueness of a
coherent local Artin family that does not involve fields or valuations.
-/

namespace LocalClassFieldTheory

/-- Two homomorphisms into an abelian group coincide if every subgroup
containing a value of the first also contains the corresponding value of the
second, and if they agree after passage to a cyclic quotient whose generator
order annihilates the target. In the local Artin application the cyclic
quotient is supplied by an unramified extension. -/
theorem monoidHom_ext_of_cyclic_quotient_and_subgroups
    {A G C : Type*} [Group A] [Group G] [Group C]
    (f g : A →* G) (β : G →* C) (u : A)
    (hgenerator : Subgroup.zpowers (β (f u)) = ⊤)
    (hexponent : ∀ z : G, z ^ orderOf (β (f u)) = 1)
    (hsubgroups : ∀ (S : Subgroup G) (x : A), f x ∈ S → g x ∈ S)
    (hquotient : ∀ x : A, β (g x) = β (f x)) :
    f = g := by
  have hfix (x : A) (hx : β (f x) = β (f u)) : g x = f x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (hsubgroups (Subgroup.zpowers (f x)) x (Subgroup.mem_zpowers (f x)))
    have hpow : (β (f u)) ^ k = (β (f u)) ^ (1 : ℤ) := by
      calc
        (β (f u)) ^ k = (β (f x)) ^ k := by rw [hx]
        _ = β ((f x) ^ k) := (map_zpow β (f x) k).symm
        _ = β (g x) := congrArg β hk
        _ = β (f x) := hquotient x
        _ = β (f u) := hx
        _ = (β (f u)) ^ (1 : ℤ) := (zpow_one _).symm
    have hmod : k ≡ 1 [ZMOD orderOf (β (f u))] :=
      (zpow_eq_zpow_iff_modEq).mp hpow
    have hdiv : (orderOf (f x) : ℤ) ∣ k - 1 :=
      (Int.natCast_dvd_natCast.mpr
        (orderOf_dvd_of_pow_eq_one (hexponent (f x)))).trans hmod.symm.dvd
    calc
      g x = (f x) ^ k := hk.symm
      _ = (f x) ^ (1 : ℤ) := (orderOf_dvd_sub_iff_zpow_eq_zpow).mp hdiv
      _ = f x := zpow_one _
  have hu : g u = f u := hfix u rfl
  apply MonoidHom.ext
  intro x
  have hxmem : β (f x) ∈ Subgroup.zpowers (β (f u)) := by
    rw [hgenerator]
    exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hy : β (f (x * u ^ (1 - m))) = β (f u) := by
    calc
      β (f (x * u ^ (1 - m))) =
          β (f x) * (β (f u)) ^ (1 - m) := by
            rw [map_mul, map_zpow, map_mul, map_zpow]
      _ = (β (f u)) ^ m * (β (f u)) ^ (1 - m) := by rw [hm]
      _ = (β (f u)) ^ (m + (1 - m)) := (zpow_add ..).symm
      _ = β (f u) := by
        have hsum : m + (1 - m) = (1 : ℤ) := by omega
        rw [hsum, zpow_one]
  have hxy : g x * (f u) ^ (1 - m) = f x * (f u) ^ (1 - m) := by
    simpa only [map_mul, map_zpow, hu] using hfix (x * u ^ (1 - m)) hy
  exact (mul_right_cancel hxy).symm

end LocalClassFieldTheory
