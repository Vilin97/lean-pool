/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Artin-Rees Convergence API

This file provides the topological consequence of the Artin-Rees lemma: in a noetherian
ring, surjective linear maps between f.g. modules admit controlled lifts through the
ideal filtration. Concretely, if `φ : M → N` is a surjective `R`-linear map of f.g.
modules over a noetherian ring, and `v ∈ I^{m+k₀} • ⊤ ⊓ N'` (where `N'` is a
submodule and `k₀` is the Artin-Rees constant), then there exists a preimage in
`I^m • ⊤`.

## Main results

* `ArtinRees.controlled_lift`: Given the Artin-Rees constant `k₀`, a surjective
  `R`-linear map `φ : M → N`, and `v ∈ I^{m+k₀} • ⊤ ⊓ K` (a submodule of the
  ambient module), there exists `c ∈ I^m • ⊤` with `φ(c) = v`.
* `ArtinRees.pi_smul_top_component`: Elements of `I^m • ⊤` in a Pi type have
  all components in `I^m`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §6, Lemma 8.31
-/

@[expose] public section

open Finset

universe u

namespace ArtinRees

variable {R : Type u} [CommRing R]

/-- Elements of `I^m • ⊤` in a Pi type have all components in `I^m`. -/
theorem pi_smul_top_component {ι : Type*} {I : Ideal R} {m : ℕ}
    {v : ι → R} (hv : v ∈ (I ^ m • ⊤ : Submodule R (ι → R))) (i : ι) :
    v i ∈ (I ^ m : Ideal R) := by
  refine Submodule.smul_induction_on
    (p := fun v => v i ∈ (I ^ m : Ideal R)) hv
    (fun r hr y _ => ?_) (fun x y hx hy => ?_)
  · change r * y i ∈ I ^ m
    exact (I ^ m).mul_mem_right (y i) hr
  · change x i + y i ∈ I ^ m
    exact (I ^ m).add_mem hx hy

/-- The surjection map from `Rᵏ` to a submodule `K` via generators `s`. -/
noncomputable def surjMap {l k : ℕ} {K : Submodule R (Fin l → R)}
    (s : Fin k → K) : (Fin k → R) →ₗ[R] K where
  toFun c := ∑ j : Fin k, c j • s j
  map_add' a b := by simp [add_smul, sum_add_distrib]
  map_smul' r a := by simp [smul_smul, smul_sum]

/-- The surjection map is surjective when the generators span the whole submodule. -/
theorem surjMap_surjective {l k : ℕ} {K : Submodule R (Fin l → R)}
    {s : Fin k → K} (hs : Submodule.span R (Set.range s) = ⊤) :
    Function.Surjective (surjMap s) := by
  intro x
  have hx : x ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  refine ⟨cf, ?_⟩
  simp only [surjMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← hcf, Finsupp.sum, ← sum_subset (subset_univ cf.support)]
  intro j _ hj; rw [Finsupp.notMem_support_iff.mp hj, zero_smul]

/-- The surjection map sends `I^m • ⊤` onto `I^m • ⊤` in the target. -/
theorem surjMap_image_smul {l k : ℕ} {K : Submodule R (Fin l → R)}
    {s : Fin k → K} (hs : Submodule.span R (Set.range s) = ⊤)
    (I : Ideal R) (m : ℕ) :
    (I ^ m • ⊤ : Submodule R (Fin k → R)).map (surjMap s) =
      (I ^ m • ⊤ : Submodule R K) := by
  rw [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (surjMap_surjective hs)]

/-- **Artin-Rees controlled lift.** Given the Artin-Rees constant `k₀` for ideal `I` and
submodule `K`, if `v ∈ K` has `↑v ∈ I^{m+k₀} • ⊤`, then `v` lies in the image of
`surjMap s` restricted to `I^m • ⊤`. In other words, there exists a tuple
`c ∈ I^m • ⊤` (in `Rᵏ`) such that `surjMap s c = v`. -/
theorem controlled_lift {l k : ℕ} (I : Ideal R) {K : Submodule R (Fin l → R)}
    (s : Fin k → K) (hs : Submodule.span R (Set.range s) = ⊤)
    (k₀ : ℕ) (hAR : ∀ n ≥ k₀, I ^ n • ⊤ ⊓ K = I ^ (n - k₀) • (I ^ k₀ • ⊤ ⊓ K))
    (m : ℕ) (v : K) (hv : (v : Fin l → R) ∈ (I ^ (m + k₀) • ⊤ : Submodule R (Fin l → R))) :
    ∃ c ∈ (I ^ m • ⊤ : Submodule R (Fin k → R)), surjMap s c = v := by
  have hv_inf : (v : Fin l → R) ∈ I ^ (m + k₀) • ⊤ ⊓ K := ⟨hv, v.prop⟩
  rw [hAR (m + k₀) (Nat.le_add_left k₀ m), Nat.add_sub_cancel] at hv_inf
  have hv_smul_K : (v : Fin l → R) ∈ I ^ m • K :=
    (Submodule.smul_mono le_rfl inf_le_right) hv_inf
  have hv_smul_top : v ∈ (I ^ m • ⊤ : Submodule R K) :=
    (Submodule.mem_smul_top_iff (I ^ m) K v).mpr hv_smul_K
  rw [← surjMap_image_smul hs I m] at hv_smul_top
  exact Submodule.mem_map.mp hv_smul_top

end ArtinRees
