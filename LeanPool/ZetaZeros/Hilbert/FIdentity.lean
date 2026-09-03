/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Hilbert.Defs

/-!
# The two-variable kernel in terms of even and odd parts

The algebraic heart of `alphaCoeff_eq`: rewriting `F` so that the non-real points contribute
`g_z(u) g_z(v) - h_z(u) h_z(v)` rather than `f_z(u) f_z(v)`.

The rewrite is **not** termwise — `f_z(u) f_z(v)` exceeds `g_z(u)g_z(v) - h_z(u)h_z(v)` by the cross
term `i(g_z(u)h_z(v) + h_z(u)g_z(v))`. What makes it true is that conjugation is a fixed-point-free
involution of the non-real part under which the cross term is *odd*, since `gz` is
conjugation-invariant and `hz` anti-invariant. So the cross terms cancel in pairs and
`Finset.sum_involution` kills the whole sum at once.

This is the step that lets the source's factor of two over conjugate pairs disappear entirely.
-/

@[expose] public section

namespace ZetaZeros

variable {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}

/-- The support splits into its real and non-real parts. -/
theorem union_realPart_nonRealPart (hZ : IsConjInvariant Z m) :
    (simpleRealPart Z m ∪ multipleRealPart Z m) ∪ nonRealPart Z = Z := by
  ext x
  simp only [Finset.mem_union, simpleRealPart, multipleRealPart, nonRealPart,
    Finset.mem_filter]
  constructor
  · rintro ((⟨hx, -⟩ | ⟨hx, -⟩) | ⟨hx, -⟩) <;> exact hx
  · intro hx
    by_cases him : x.im = 0
    · have h1 := hZ.one_le x hx
      rcases eq_or_lt_of_le h1 with heq | hlt
      · exact Or.inl (Or.inl ⟨hx, him, heq.symm⟩)
      · exact Or.inl (Or.inr ⟨hx, him, hlt⟩)
    · exact Or.inr ⟨hx, him⟩

/-- The real and non-real parts are disjoint. -/
theorem disjoint_realPart_nonRealPart :
    Disjoint (simpleRealPart Z m ∪ multipleRealPart Z m) (nonRealPart Z) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_union, simpleRealPart, multipleRealPart, Finset.mem_filter] at hx
  simp only [nonRealPart, Finset.mem_filter] at hx'
  rcases hx with ⟨-, him, -⟩ | ⟨-, him, -⟩ <;> exact hx'.2 him

/-- The cross terms cancel over the non-real part: conjugation is a fixed-point-free involution
there, and the cross term is odd under it. -/
theorem sum_cross_eq_zero (hZ : IsConjInvariant Z m) (u v : ℝ) :
    ∑ z ∈ nonRealPart Z, (m z : ℂ) *
        (Complex.I * (gz eta z u * hz eta z v + hz eta z u * gz eta z v)) = 0 := by
  refine Finset.sum_involution (fun z _ => (starRingEnd ℂ) z) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [nonRealPart, Finset.mem_filter] at hz
    have hmem := hZ.conj_mem z hz.1
    have hmult := hZ.mult_conj z hz.1
    rw [hmult, gz_conj, hz_conj]
    ring
  · intro z hz _
    simp only [nonRealPart, Finset.mem_filter] at hz
    intro hcon
    apply hz.2
    have := Complex.conj_eq_iff_im.mp hcon
    exact this
  · intro z hz
    simp only [nonRealPart, Finset.mem_filter] at hz ⊢
    exact ⟨hZ.conj_mem z hz.1, by simpa using hz.2⟩
  · intro z _
    exact Complex.conj_conj z

/-- **The two-variable kernel in terms of even and odd parts.** -/
theorem bigF_eq (hZ : IsConjInvariant Z m) (u v : ℝ) :
    bigF eta Z m u v
      = (∑ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
          (m x : ℂ) * fz eta x u * fz eta x v)
        + ∑ z ∈ nonRealPart Z,
            (m z : ℂ) * (gz eta z u * gz eta z v - hz eta z u * hz eta z v) := by
  have hsplit : ∑ z ∈ Z, (m z : ℂ) * fz eta z u * fz eta z v
      = (∑ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
            (m x : ℂ) * fz eta x u * fz eta x v)
        + ∑ z ∈ nonRealPart Z, (m z : ℂ) * fz eta z u * fz eta z v := by
    rw [← Finset.sum_union disjoint_realPart_nonRealPart, union_realPart_nonRealPart hZ]
  rw [bigF, hsplit]
  congr 1
  have hpt : ∀ z : ℂ, (m z : ℂ) * fz eta z u * fz eta z v
      = (m z : ℂ) * (gz eta z u * gz eta z v - hz eta z u * hz eta z v)
        + (m z : ℂ) *
            (Complex.I * (gz eta z u * hz eta z v + hz eta z u * gz eta z v)) := by
    intro z
    rw [fz_eq_gz_add_I_mul_hz eta z u, fz_eq_gz_add_I_mul_hz eta z v]
    linear_combination ((m z : ℂ) * hz eta z u * hz eta z v) * Complex.I_sq
  calc ∑ z ∈ nonRealPart Z, (m z : ℂ) * fz eta z u * fz eta z v
      = ∑ z ∈ nonRealPart Z,
          ((m z : ℂ) * (gz eta z u * gz eta z v - hz eta z u * hz eta z v)
            + (m z : ℂ) *
                (Complex.I * (gz eta z u * hz eta z v + hz eta z u * gz eta z v))) :=
        Finset.sum_congr rfl fun z _ => hpt z
    _ = _ := by
        rw [Finset.sum_add_distrib, sum_cross_eq_zero hZ u v, add_zero]

end ZetaZeros
