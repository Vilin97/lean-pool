/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConnectionRank

/-!
# A factored connection pairing has bounded rank

The edge-rank hypothesis asks for the rank of the connection map to
be bounded.  A pairing that factors through a finite index set —
each row a combination of a fixed finite family of columns — has its
whole range inside the span of that family, so the rank is at most
the family's size.

This is the linear algebra behind writing a connection matrix as a
Gram matrix: a Gram factorization exhibits each row as a combination
of the columns indexed by the ambient space's coordinates.
-/

@[expose] public section

namespace RS



/-- **A pairing whose rows lie in a span has rank at most that
span's generating set.** -/
theorem rank_connectionMap_le_of_mem_span {f : ClosedFragment → ℂ}
    {t : ℕ} (s : Set (Fragment (Fin t) → ℂ))
    (hmem : ∀ F : Fragment (Fin t),
      (fun G => connectionPairing f t F G) ∈ Submodule.span ℂ s) :
    Module.rank ℂ (LinearMap.range (connectionMap f t))
      ≤ Cardinal.mk s := by
  refine le_trans (Submodule.rank_mono ?_) (rank_span_le s)
  rintro _ ⟨l, rfl⟩
  rw [connectionMap, Finsupp.lift_apply]
  exact Submodule.sum_mem _
    (fun F _ => Submodule.smul_mem _ _ (hmem F))

/-- **A pairing that factors through a finite index set has rank at
most that set's size.**  The row at `F` is the combination of the
columns `w x` with coefficients `u F x`. -/
theorem rank_connectionMap_le_of_factor {f : ClosedFragment → ℂ}
    {t : ℕ} {χ : Type} [Fintype χ]
    (u : Fragment (Fin t) → χ → ℂ)
    (w : χ → Fragment (Fin t) → ℂ)
    (hfac : ∀ (F G : Fragment (Fin t)),
      connectionPairing f t F G = ∑ x : χ, u F x * w x G) :
    Module.rank ℂ (LinearMap.range (connectionMap f t))
      ≤ (Fintype.card χ : Cardinal) := by
  refine le_trans (rank_connectionMap_le_of_mem_span
    (Set.range w) (fun F => ?_)) ?_
  · have hrow : (fun G => connectionPairing f t F G)
        = ∑ x : χ, u F x • w x := by
      funext G
      rw [hfac F G, Finset.sum_apply]
      exact Finset.sum_congr rfl (fun x _ => rfl)
    rw [hrow]
    exact Submodule.sum_mem _ (fun x _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨x, rfl⟩))
  · have hsurj : Function.Surjective
        (fun x : ULift.{1} χ => (⟨w x.down, ⟨x.down, rfl⟩⟩ :
          Set.range w)) := by
      rintro ⟨-, x, rfl⟩
      exact ⟨ULift.up x, rfl⟩
    refine le_trans (Cardinal.mk_le_of_surjective hsurj) ?_
    rw [Cardinal.mk_uLift, Cardinal.mk_fintype]
    simp

/-- **A factored pairing at every arity gives the edge-rank
bound.** -/
theorem edgeRankBounded_of_factor {f : ClosedFragment → ℂ} {R : ℕ}
    (χ : ℕ → Type) [∀ t, Fintype (χ t)]
    (hcard : ∀ t, Fintype.card (χ t) = R ^ t)
    (u : ∀ t, Fragment (Fin t) → χ t → ℂ)
    (w : ∀ t, χ t → Fragment (Fin t) → ℂ)
    (hfac : ∀ (t : ℕ) (F G : Fragment (Fin t)),
      connectionPairing f t F G = ∑ x : χ t, u t F x * w t x G) :
    EdgeRankBounded f R := by
  intro t
  refine le_trans
    (rank_connectionMap_le_of_factor (u t) (w t) (hfac t)) ?_
  rw [hcard t, Nat.cast_pow]

/-- **A Gram factorization gives the edge-rank bound.**  If the
connection pairing is the bilinear form `B` evaluated at vectors
attached to the two fragments, its rank is bounded by the ambient
space's dimension. -/
theorem edgeRankBounded_of_gram {f : ClosedFragment → ℂ} {R : ℕ}
    (χ : ℕ → Type) [∀ t, Fintype (χ t)]
    (hcard : ∀ t, Fintype.card (χ t) = R ^ t)
    (B : ∀ t, χ t → χ t → ℂ)
    (T : ∀ t, Fragment (Fin t) → χ t → ℂ)
    (hgram : ∀ (t : ℕ) (F G : Fragment (Fin t)),
      connectionPairing f t F G
        = ∑ x : χ t, ∑ y : χ t, B t x y * T t F x * T t G y) :
    EdgeRankBounded f R := by
  refine edgeRankBounded_of_factor χ hcard (fun t F x => T t F x)
    (fun t x G => ∑ y : χ t, B t x y * T t G y) (fun t F G => ?_)
  rw [hgram t F G]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun y _ => by ring)

end RS
