/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking

The proof architecture of the self-adjointness criterion below is adapted from
Adam Bornemann's proof of `Spectra.TomitaTakesaki.modularOp_isSelfAdjoint` in
`Spectra/Modular/TomitaTakesaki/VonNeumannTstarT.lean`, Spectra commit
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.  It is generalized here from the
modular operator to an arbitrary densely recoverable positive symmetric
partial operator.  The original and adapted files are Apache-2.0 licensed.
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
import Mathlib.Tactic

/-!
# A positive-surjective self-adjointness criterion

For a symmetric partial operator `A`, nonnegativity and surjectivity of
`A + 1` force self-adjointness.  The proof is the real von Neumann criterion:

* positivity plus surjectivity first proves that the domain is dense;
* symmetry gives `A ≤ A†`;
* surjectivity of `A + 1` kills the kernel of `A† + 1`;
* solving `(A + 1)x = (A† + 1)w` then proves `w ∈ D(A)` and `A w = A† w`.

This theorem is a central reusable target for the free-beam form realization.
A Lax--Milgram construction only has to produce the positive symmetric partial
operator and solve `(A + 1)x = h`; the theorem below supplies maximality.
-/

open scoped InnerProductSpace
open Set

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Abstract

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- Positivity and surjectivity of `A + 1` force density of the operator
 domain.  This is useful when a variational construction initially presents a
 domain but has not yet established density independently. -/
theorem dense_domain_of_nonnegative_one_add_surjective
    (A : H →ₗ.[𝕜] H)
    (hnonneg : ∀ x : A.domain,
      0 ≤ RCLike.re ⟪A x, (x : H)⟫_𝕜)
    (hsurj : ∀ h : H, ∃ x : A.domain, A x + (x : H) = h) :
    Dense (A.domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro h hh
  obtain ⟨g, hg⟩ := hsurj h
  have hortho : ⟪(g : H), h⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal _ h).1 hh (g : H) g.property
  rw [← hg, inner_add_right] at hortho
  have hpos : 0 ≤ RCLike.re ⟪(g : H), A g⟫_𝕜 := by
    rw [inner_re_symm]
    exact hnonneg g
  have hre : RCLike.re ⟪(g : H), A g⟫_𝕜 + ‖(g : H)‖ ^ 2 = 0 := by
    have hr := congrArg RCLike.re hortho
    rwa [map_add, map_zero, inner_self_eq_norm_sq] at hr
  have hg0 : (g : H) = 0 := by
    have hsq : ‖(g : H)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖(g : H)‖]
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  have g_eq_zero : g = 0 := Subtype.ext hg0
  rw [← hg, g_eq_zero]
  simp

/-- A symmetric nonnegative partial operator for which `A + 1` is onto is
 self-adjoint.  No prior density hypothesis is required. -/
theorem isSelfAdjoint_of_isFormalAdjoint_nonnegative_one_add_surjective
    (A : H →ₗ.[𝕜] H)
    (hsym : A.IsFormalAdjoint A)
    (hnonneg : ∀ x : A.domain,
      0 ≤ RCLike.re ⟪A x, (x : H)⟫_𝕜)
    (hsurj : ∀ h : H, ∃ x : A.domain, A x + (x : H) = h) :
    _root_.IsSelfAdjoint A := by
  have hdense : Dense (A.domain : Set H) :=
    dense_domain_of_nonnegative_one_add_surjective A hnonneg hsurj
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_ (hsym.le_adjoint hdense)
  have hker : ∀ w : A.adjoint.domain,
      A.adjoint w = -(w : H) → (w : H) = 0 := by
    intro w hw
    have hortho : ∀ v : A.domain,
        ⟪(w : H), A v + (v : H)⟫_𝕜 = 0 := by
      intro v
      have hfa : ⟪A.adjoint w, (v : H)⟫_𝕜 =
          ⟪(w : H), A v⟫_𝕜 :=
        LinearPMap.adjoint_isFormalAdjoint hdense w v
      rw [hw, inner_neg_left] at hfa
      rw [inner_add_right, ← hfa]
      ring
    obtain ⟨v, hv⟩ := hsurj (w : H)
    have hself : ⟪(w : H), (w : H)⟫_𝕜 = 0 := by
      have h := hortho v
      rwa [hv] at h
    exact inner_self_eq_zero.mp hself
  apply LinearPMap.le_of_eqLocus_ge
  intro w hw
  set W : A.adjoint.domain := ⟨w, hw⟩ with hWdef
  obtain ⟨x, hx⟩ := hsurj (A.adjoint W + w)
  have hxin : (x : H) ∈ A.adjoint.domain :=
    (hsym.le_adjoint hdense).1 x.property
  have hxeq :
      A.adjoint (⟨(x : H), hxin⟩ : A.adjoint.domain) = A x :=
    ((hsym.le_adjoint hdense).2
      (x := x) (y := ⟨(x : H), hxin⟩) rfl).symm
  set W' : A.adjoint.domain := W - ⟨(x : H), hxin⟩ with hW'def
  have hW'val : (W' : H) = w - (x : H) := rfl
  have hAW' : A.adjoint W' = -(W' : H) := by
    have e1 : A.adjoint W' = A.adjoint W - A x := by
      rw [hW'def, LinearPMap.map_sub, hxeq]
    rw [e1, hW'val]
    have hAx : A x = A.adjoint W + w - (x : H) := by
      rw [← hx]
      abel
    rw [hAx]
    abel
  have hwx : w = (x : H) := by
    have h0 : (W' : H) = 0 := hker W' hAW'
    rw [hW'val] at h0
    exact sub_eq_zero.mp h0
  subst hwx
  exact ⟨hw, x.property, hxeq⟩

/-- Closed-operator wrapper for the positive-surjective criterion. -/
theorem DavisKahanExt.PartialMap.isSelfAdjoint_of_nonnegative_one_add_surjective
    (A : H →ₗ.[𝕜] H)
    (hsym : TauCeti.LinearPMap.IsSymmetric A)
    (hnonneg : ∀ x : A.domain,
      0 ≤ RCLike.re ⟪A x, (x : H)⟫_𝕜)
    (hsurj : ∀ h : H, ∃ x : A.domain,
      A x + (x : H) = h) :
    IsSelfAdjoint A := by
  apply isSelfAdjoint_of_isFormalAdjoint_nonnegative_one_add_surjective
  · intro x y
    exact hsym x y
  · exact hnonneg
  · exact hsurj

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
