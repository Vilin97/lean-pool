/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Noetherian.Filter


/-!
# Uniform vanishing of an ascending family of boundary maps

Pointwise eventual vanishing becomes uniform on a Noetherian source.  The
localized statement deliberately assumes Noetherianity only after
localization.
-/

@[expose] public section

open IsNoetherian

namespace AlgebraicAnalysis

theorem exists_uniform_zero_of_noetherian
    {R U : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
    {V : ℕ → Type*} [∀ r, AddCommMonoid (V r)] [∀ r, Module R (V r)]
    (b : ∀ r, U →ₗ[R] V r)
    (hmono : ∀ r s, r ≤ s → LinearMap.ker (b r) ≤ LinearMap.ker (b s))
    (hpoint : ∀ u, ∃ r, b r u = 0) [IsNoetherian R U] :
    ∃ r, b r = 0 := by
  let F : ℕ →o Submodule R U :=
    { toFun := fun r => LinearMap.ker (b r)
      monotone' := fun r s hrs => hmono r s hrs }
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance F
  refine ⟨n, LinearMap.ext fun u => ?_⟩
  obtain ⟨r, hr⟩ := hpoint u
  have hu : u ∈ F r := LinearMap.mem_ker.mpr hr
  have hu' : u ∈ F (max n r) :=
    (hmono r (max n r) (Nat.le_max_right _ _)) hu
  have heq : F n = F (max n r) := hn _ (Nat.le_max_left _ _)
  have : u ∈ F n := heq.symm ▸ hu'
  exact LinearMap.mem_ker.mp this

theorem exists_uniform_subsingleton_of_noetherian
    {R U : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
    {V : ℕ → Type*} [∀ r, AddCommMonoid (V r)] [∀ r, Module R (V r)]
    (b : ∀ r, U →ₗ[R] V r)
    (hmono : ∀ r s, r ≤ s → LinearMap.ker (b r) ≤ LinearMap.ker (b s))
    (hpoint : ∀ u, ∃ r, b r u = 0)
    (hsurj : ∀ r, Function.Surjective (b r)) [IsNoetherian R U] :
    ∃ r, Subsingleton (V r) := by
  obtain ⟨r, hr⟩ := exists_uniform_zero_of_noetherian b hmono hpoint
  refine ⟨r, ?_⟩
  constructor
  intro x y
  obtain ⟨u, rfl⟩ := hsurj r x
  obtain ⟨v, rfl⟩ := hsurj r y
  simp [hr]

section Localized

variable {R : Type*} [CommRing R] (S : Submonoid R)
variable {U : Type*} [AddCommMonoid U] [Module R U]
variable {V : ℕ → Type*} [∀ r, AddCommMonoid (V r)] [∀ r, Module R (V r)]

private theorem localized_ker_mono
    (b : ∀ r, U →ₗ[R] V r)
    (hmono : ∀ r s, r ≤ s → LinearMap.ker (b r) ≤ LinearMap.ker (b s))
    {r s : ℕ} (hrs : r ≤ s) :
    LinearMap.ker (LocalizedModule.map S (b r)) ≤
      LinearMap.ker (LocalizedModule.map S (b s)) := by
  intro z hz
  induction z using LocalizedModule.induction_on with
  | _ u t =>
      have hz' := LinearMap.mem_ker.mp hz
      rw [LocalizedModule.map_mk] at hz'
      change LocalizedModule.mk (b r u) t = 0 at hz'
      apply LinearMap.mem_ker.mpr
      rw [LocalizedModule.map_mk]
      change LocalizedModule.mk (b s u) t = 0
      rw [IsLocalizedModule.mk_eq_mk' (S := S)] at hz' ⊢
      rw [IsLocalizedModule.mk'_eq_zero' (LocalizedModule.mkLinearMap S (V r))] at hz'
      obtain ⟨a, ha⟩ := hz'
      have hscaled : b r (a • u) = 0 := by
        simpa [map_smul] using ha
      have hscaled' : b s (a • u) = 0 :=
        LinearMap.mem_ker.mp (hmono r s hrs (LinearMap.mem_ker.mpr hscaled))
      rw [IsLocalizedModule.mk'_eq_zero']
      exact ⟨a, by simpa [map_smul] using hscaled'⟩

theorem exists_uniform_zero_localized
    (b : ∀ r, U →ₗ[R] V r)
    (hmono : ∀ r s, r ≤ s → LinearMap.ker (b r) ≤ LinearMap.ker (b s))
    (hpoint : ∀ u, ∃ r, b r u = 0)
    [IsNoetherian (Localization S) (LocalizedModule S U)] :
    ∃ r, LocalizedModule.map S (b r) = 0 := by
  let B : ∀ r, LocalizedModule S U →ₗ[Localization S]
      LocalizedModule S (V r) := fun r => LocalizedModule.map S (b r)
  have hpoint' : ∀ u, ∃ r, B r u = 0 := by
    intro u
    induction u using LocalizedModule.induction_on with
    | _ m s =>
        obtain ⟨r, hr⟩ := hpoint m
        refine ⟨r, ?_⟩
        simp [B, LocalizedModule.map_mk, hr]
  obtain ⟨r, hr⟩ := exists_uniform_zero_of_noetherian B
    (fun r s hrs => by simpa only [B] using localized_ker_mono S b hmono hrs) hpoint'
  exact ⟨r, by simpa [B] using hr⟩

theorem exists_uniform_subsingleton_localized
    (b : ∀ r, U →ₗ[R] V r)
    (hmono : ∀ r s, r ≤ s → LinearMap.ker (b r) ≤ LinearMap.ker (b s))
    (hpoint : ∀ u, ∃ r, b r u = 0)
    (hsurj : ∀ r, Function.Surjective (b r))
    [IsNoetherian (Localization S) (LocalizedModule S U)] :
    ∃ r, Subsingleton (LocalizedModule S (V r)) := by
  let B : ∀ r, LocalizedModule S U →ₗ[Localization S]
      LocalizedModule S (V r) := fun r => LocalizedModule.map S (b r)
  have hsurj' : ∀ r, Function.Surjective (B r) := by
    intro r
    exact LocalizedModule.map_surjective S (b r) (hsurj r)
  exact exists_uniform_subsingleton_of_noetherian B
    (fun r s hrs => by simpa [B] using localized_ker_mono S b hmono hrs) (by
      intro u
      induction u using LocalizedModule.induction_on with
      | _ m s =>
          obtain ⟨r, hr⟩ := hpoint m
          refine ⟨r, ?_⟩
          simp [B, LocalizedModule.map_mk, hr]) hsurj'

end Localized


end AlgebraicAnalysis
