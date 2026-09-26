/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Support


/-!
# Algebraic hyperplane restriction

For a finite module over a commutative ring, surjectivity of multiplication
by an element forces the module support to avoid the corresponding principal
hypersurface. The proof is the determinant trick and is independent of any
filtered or differential-operator application.
-/

@[expose] public section

namespace AlgebraicAnalysis.HyperplaneRestriction

open scoped Pointwise

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Degree-zero restriction to the principal hypersurface defined by `x`. -/
abbrev Restriction (x : R) : Type _ :=
  M ⧸ (Ideal.span {x} • (⊤ : Submodule R M))

/-- Restriction vanishes exactly when multiplication by `x` is surjective. -/
theorem restriction_subsingleton_iff_smul_surjective {x : R} :
    Subsingleton (Restriction (M := M) x) ↔
      Function.Surjective fun m : M ↦ x • m := by
  have hquotient :
      Subsingleton (Restriction (M := M) x) ↔
        Ideal.span {x} • (⊤ : Submodule R M) = ⊤ := by
    constructor
    · intro h
      apply Submodule.unique_quotient_iff_eq_top.mp
      exact ⟨{
        default := 0
        uniq := fun y ↦ h.elim y 0 }⟩
    · intro h
      obtain ⟨hunique⟩ := Submodule.unique_quotient_iff_eq_top.mpr h
      exact @Unique.instSubsingleton _ hunique
  rw [hquotient]
  constructor
  · intro htop m
    have hm : m ∈ x • (⊤ : Submodule R M) := by
      rw [← Submodule.ideal_span_singleton_smul, htop]
      exact Submodule.mem_top
    rw [← Submodule.singleton_set_smul] at hm
    obtain ⟨n, hn, hmn⟩ :=
      (Submodule.mem_singleton_set_smul (⊤ : Submodule R M) x m).mp hm
    exact ⟨n, hmn.symm⟩
  · intro hx
    apply top_unique
    intro m hm
    obtain ⟨n, rfl⟩ := hx m
    exact Submodule.smul_mem_smul
      (Ideal.subset_span (by simp))
      (Submodule.mem_top : n ∈ (⊤ : Submodule R M))

theorem restriction_subsingleton_of_smul_surjective {x : R}
    (hx : Function.Surjective fun m : M ↦ x • m) :
    Subsingleton (Restriction (M := M) x) :=
  restriction_subsingleton_iff_smul_surjective.mpr hx

/-- Determinant-trick certificate for a surjective scalar action. -/
theorem exists_annihilator_sub_one_mem_span_of_smul_surjective
    [Module.Finite R M] {x : R}
    (hx : Function.Surjective fun m : M ↦ x • m) :
    ∃ r : R, r - 1 ∈ Ideal.span {x} ∧ ∀ m : M, r • m = 0 := by
  obtain ⟨r, hr, hrann⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      (Ideal.span {x}) (⊤ : Submodule R M) Module.Finite.fg_top (by
        intro m hm
        obtain ⟨n, rfl⟩ := hx m
        exact Submodule.smul_mem_smul
          (Ideal.subset_span (by simp))
          (Submodule.mem_top : n ∈ (⊤ : Submodule R M)))
  exact ⟨r, hr, fun m ↦ hrann m Submodule.mem_top⟩

/-- A support prime containing `x` is impossible when `x` acts surjectively. -/
theorem not_mem_support_of_smul_surjective_of_mem
    [Module.Finite R M] {x : R}
    (hx : Function.Surjective fun m : M ↦ x • m)
    (p : PrimeSpectrum R) (hxp : x ∈ p.asIdeal) :
    p ∉ Module.support R M := by
  intro hp
  obtain ⟨r, hrspan, hrann⟩ :=
    exists_annihilator_sub_one_mem_span_of_smul_surjective hx
  have hrp : r ∈ p.asIdeal :=
    Module.annihilator_le_of_mem_support hp (Module.mem_annihilator.mpr hrann)
  have hsubp : r - 1 ∈ p.asIdeal :=
    (Ideal.span_le.mpr (by simpa using hxp)) hrspan
  have hone : (1 : R) ∈ p.asIdeal := by
    have := p.asIdeal.sub_mem hrp hsubp
    simpa using this
  exact p.2.ne_top ((Ideal.eq_top_iff_one p.asIdeal).mpr hone)

/-- The support of a finite module with surjective `x`-action avoids `V(x)`. -/
theorem support_disjoint_zeroLocus_of_smul_surjective
    [Module.Finite R M] {x : R}
    (hx : Function.Surjective fun m : M ↦ x • m) :
    Disjoint (Module.support R M) (PrimeSpectrum.zeroLocus ({x} : Set R)) := by
  rw [Set.disjoint_left]
  intro p hp hpx
  rw [PrimeSpectrum.mem_zeroLocus] at hpx
  exact not_mem_support_of_smul_surjective_of_mem hx p (hpx (by simp)) hp

/-- Restriction-vanishing form of support exclusion. -/
theorem support_disjoint_zeroLocus_of_restriction_subsingleton
    [Module.Finite R M] {x : R}
    (hx : Subsingleton (Restriction (M := M) x)) :
    Disjoint (Module.support R M) (PrimeSpectrum.zeroLocus ({x} : Set R)) :=
  support_disjoint_zeroLocus_of_smul_surjective
    (restriction_subsingleton_iff_smul_surjective.mp hx)

/-- Complement-inclusion form of support exclusion. -/
theorem support_subset_compl_zeroLocus_of_smul_surjective
    [Module.Finite R M] {x : R}
    (hx : Function.Surjective fun m : M ↦ x • m) :
    Module.support R M ⊆ (PrimeSpectrum.zeroLocus ({x} : Set R))ᶜ := by
  intro p hp hpx
  exact Set.disjoint_left.mp
    (support_disjoint_zeroLocus_of_smul_surjective hx) hp hpx


end AlgebraicAnalysis.HyperplaneRestriction
