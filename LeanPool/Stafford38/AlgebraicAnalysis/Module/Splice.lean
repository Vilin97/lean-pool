/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic

/-!
# Maximal-submodule splice

These are lattice-theoretic module lemmas used by finite-length correction
arguments.  They contain no finite-length, Ore, or differential-operator
assumption.  The hypotheses that construct the relevant submodules remain
with the application.
-/

namespace AlgebraicAnalysis.Splice

open Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- A simple layer turns a proper submodule whose sum with the layer is top
into a maximal submodule. -/
theorem isCoatom_of_covBy_sup_eq_top
    {N N' U : Submodule R M}
    (hNU : N ≤ U) (hNN' : N ⋖ N')
    (hsup : N' ⊔ U = ⊤) (hUtop : U ≠ ⊤) :
    IsCoatom U := by
  have hInfEq : N' ⊓ U = N := by
    apply le_antisymm
    · by_contra hnot
      have hNInf : N ≤ N' ⊓ U := le_inf hNN'.le hNU
      have hNe : N ≠ N' ⊓ U := by
        intro hEq
        apply hnot
        rw [hEq]
      rcases hNN'.eq_or_eq hNInf inf_le_left with hEq | hEq
      · exact hnot (by rw [hEq])
      · have hN'leU : N' ≤ U := by
          rw [← hEq]
          exact inf_le_right
        apply hUtop
        calc
          U = N' ⊔ U := (sup_eq_right.mpr hN'leU).symm
          _ = ⊤ := hsup
    · exact le_inf hNN'.le hNU
  have hInfCov : U ⊓ N' ⋖ N' := by
    simpa [inf_comm, hInfEq] using hNN'
  have hCov : U ⋖ U ⊔ N' := covBy_sup_of_inf_covBy_right hInfCov
  have hCov' : U ⋖ ⊤ := by
    simpa [sup_comm, hsup] using hCov
  exact hCov'.isCoatom

/--
The reusable maximal-submodule splice.  Once a combined submodule contains a
simple layer and one of the maximal submodules, it is the whole module.
-/
theorem maximal_submodule_splice
    {N N' U V H : Submodule R M}
    (hNU : N ≤ U) (hNV : N ≤ V) (hNN' : N ⋖ N')
    (hsupU : N' ⊔ U = ⊤) (hUtop : U ≠ ⊤)
    (hsupV : N' ⊔ V = ⊤) (hVtop : V ≠ ⊤)
    (hVU : V ≤ U) (hUH : U ≤ H) (hN'H : N' ≤ H) :
    H = ⊤ := by
  have hUcoat : IsCoatom U := isCoatom_of_covBy_sup_eq_top hNU hNN' hsupU hUtop
  have hVcoat : IsCoatom V := isCoatom_of_covBy_sup_eq_top hNV hNN' hsupV hVtop
  have hUV : U = V := by
    exact (hVcoat.le_iff_eq hUtop).mp hVU
  have hVH : V ≤ H := by
    rw [← hUV]
    exact hUH
  apply top_unique
  rw [← hsupV]
  exact sup_le hN'H hVH

/--
If `v` lies in `P` and some scalar multiple of a vector escapes `P`, then the
class of the corresponding affine correction generates the simple quotient.
-/
theorem exists_affine_correction_mod_simple_quotient
    {P : Submodule R M} (v : M) (hv : v ∈ P)
    (hsimple : IsSimpleModule R (M ⧸ P)) (alpha : R)
    (hescape : ∃ delta : M, alpha • delta ∉ P) :
    ∃ delta : M, span R {P.mkQ (v - alpha • delta)} = ⊤ := by
  obtain ⟨delta, hdelta⟩ := hescape
  have hne : P.mkQ (v - alpha • delta) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    intro hmem
    apply hdelta
    have hsub := P.sub_mem hv hmem
    simpa [sub_sub_cancel] using hsub
  refine ⟨delta, ?_⟩
  rw [LinearMap.span_singleton_eq_range, LinearMap.range_eq_top]
  exact IsSimpleModule.toSpanSingleton_surjective R hne


end AlgebraicAnalysis.Splice
