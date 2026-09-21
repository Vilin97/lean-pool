/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.HahnSeries.Cardinal

/-!
# Exponent-domain embeddings of Hahn series

Mathlib's exponent-domain embedding has a one-sided support inclusion. Injectivity of the order
embedding gives the exact support formula needed by the translation and nonpositive-series APIs.
-/

universe u v w

public section

namespace HahnSeries

variable {G : Type u} {H : Type v} {K : Type w}
  [PartialOrder G] [PartialOrder H] [Zero K]

/-- Extending the exponent domain maps the support exactly onto its image. -/
@[simp]
theorem support_embDomain (f : G ↪o H) (x : K⟦G⟧) :
    (embDomain f x).support = f '' x.support := by
  apply Set.Subset.antisymm support_embDomain_subset
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_support] at hg ⊢
  intro hzero
  exact hg (embDomain_coeff.symm.trans hzero)

/-- Restrict a Hahn series along an ordered embedding by retaining the coefficients in its
range. This is a left inverse to `embDomain`; it is also a right inverse when the original
series is supported in the embedding's range. -/
noncomputable def restrictDomain (f : G ↪o H) (x : K⟦H⟧) : K⟦G⟧ where
  coeff g := x.coeff (f g)
  isPWO_support' := by
    rw [Set.isPWO_iff_exists_monotone_subseq]
    intro a ha
    have hfa : ∀ n, f (a n) ∈ x.support := fun n ↦ ha n
    obtain ⟨g, hg⟩ := x.isPWO_support.exists_monotone_subseq hfa
    exact ⟨g, fun _ _ h ↦ f.le_iff_le.mp (hg h)⟩

@[simp]
theorem restrictDomain_coeff (f : G ↪o H) (x : K⟦H⟧) (g : G) :
    (restrictDomain f x).coeff g = x.coeff (f g) :=
  (rfl)

/-- Extending an exponent domain after restricting it recovers a series supported in the
embedding's range. -/
theorem embDomain_restrictDomain (f : G ↪o H) (x : K⟦H⟧)
    (hx : x.support ⊆ Set.range f) :
    embDomain f (restrictDomain f x) = x := by
  ext h
  by_cases hh : h ∈ Set.range f
  · obtain ⟨g, rfl⟩ := hh
    rw [embDomain_coeff, restrictDomain_coeff]
  · rw [embDomain_notin_range hh]
    have hzero : x.coeff h = 0 := by
      by_contra hne
      exact hh (hx hne)
    exact hzero.symm

/-- Restricting an extended Hahn series recovers the original series. -/
@[simp]
theorem restrictDomain_embDomain (f : G ↪o H) (x : K⟦G⟧) :
    restrictDomain f (embDomain f x) = x := by
  ext g
  rw [restrictDomain_coeff, embDomain_coeff]

section Cardinal

universe u' v'

variable {G' H' : Type u'} {K' : Type v'}
variable [PartialOrder G'] [PartialOrder H'] [Zero K']

/-- Extending the exponent domain along an order embedding preserves support cardinality. -/
theorem cardSupp_embDomain (f : G' ↪o H') (x : K'⟦G'⟧) :
    (embDomain f x).cardSupp = x.cardSupp := by
  rw [cardSupp, cardSupp, support_embDomain]
  exact Cardinal.mk_image_eq f.injective

end Cardinal

end HahnSeries
