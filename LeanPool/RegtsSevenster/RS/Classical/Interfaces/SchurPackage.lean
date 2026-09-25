/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.YoungDiagrams
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.PowerSums

/-!
# The symmetric-group Schur interface

`SchurPackage` bundles, as hypotheses, the classical representation
theory of the symmetric groups that the development consumes: for
each Young diagram `μ` a dimension `dim μ` and a character
`char μ : Perm (Fin μ.card) → ℂ`, such that the attached elements

    `e μ = (dim μ / μ.card !) • ∑ π, char μ π • π`

are central idempotents of the group algebra `ℂ[S_{μ.card}]` whose
blocks have dimension `(dim μ)²` and are faithfully represented or
killed as a whole (`block_faithful`); together with the branching
containment (`branching`), the growth of the square-diagram
dimension (`square_dim`), and the Frobenius character formula
stated against the Jacobi–Trudi determinant of
`SymFun/PowerSums.lean` (`frobenius`).

Everything here is standard — Fulton–Harris §4, Sagan, or
James–Kerber; the fields are exactly what the hook-confinement and
trace arguments of `Envelope/` consume, no more.  A term is
constructed from mathlib's linear algebra as `RS.schurPackage` in
`RS/Classical/SchurTheory/Package.lean`.
-/

@[expose] public section

namespace RS

universe u

open Equiv

/-- The complex group algebra of the symmetric group `S_n`. -/
abbrev SymGroupAlgebra (n : ℕ) : Type :=
  MonoidAlgebra ℂ (Equiv.Perm (Fin n))

/-- Extension of scalars of the group algebra along the standard
embedding `S_m ↪ S_n` (permutations extended by the identity),
for `m ≤ n`. -/
noncomputable def symCast {m n : ℕ} (h : m ≤ n) :
    SymGroupAlgebra m →ₐ[ℂ] SymGroupAlgebra n :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ
    (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h))

/-- The group-algebra element `(d / n!) • ∑ π, χ π • π` attached to
a prospective dimension `d` and character `χ`. -/
noncomputable def charIdempotent {n : ℕ} (d : ℕ) (χ : Perm (Fin n) → ℂ) :
    SymGroupAlgebra n :=
  ((d : ℂ) / (n.factorial : ℂ)) •
    ∑ π : Perm (Fin n), χ π • (MonoidAlgebra.of ℂ (Perm (Fin n)) π)

/-- The classical representation theory of the symmetric groups, as
consumed by this development.  A term of this structure is an input
of the development. -/
structure SchurPackage where
  /-- The dimension of the irreducible representation of shape `μ`. -/
  dim : YoungDiagram → ℕ
  /-- The irreducible character of shape `μ`. -/
  char : (μ : YoungDiagram) → Perm (Fin μ.card) → ℂ
  /-- Dimensions are positive. -/
  dim_pos : ∀ μ : YoungDiagram, 0 < dim μ
  /-- The attached idempotents are central. -/
  central : ∀ (μ : YoungDiagram) (x : SymGroupAlgebra μ.card),
    charIdempotent (dim μ) (char μ) * x = x * charIdempotent (dim μ) (char μ)
  /-- The attached elements are idempotent. -/
  idem : ∀ μ : YoungDiagram,
    charIdempotent (dim μ) (char μ) * charIdempotent (dim μ) (char μ) =
      charIdempotent (dim μ) (char μ)
  /-- The block of shape `μ` — the ideal `e μ * ℂ[S_n]` — has
  dimension `(dim μ)²`. -/
  block_rank : ∀ μ : YoungDiagram,
    Module.finrank ℂ
      (LinearMap.range (LinearMap.mulLeft ℂ (charIdempotent (dim μ) (char μ))))
        =
      dim μ ^ 2
  /-- Blocks are simple: an algebra morphism that does not kill
  `e μ` is injective on the block of `μ`. -/
  block_faithful : ∀ (μ : YoungDiagram) (B : Type u) [Ring B] [Algebra ℂ B]
    (φ : SymGroupAlgebra μ.card →ₐ[ℂ] B),
    φ (charIdempotent (dim μ) (char μ)) ≠ 0 →
    ∀ x : SymGroupAlgebra μ.card,
      φ (charIdempotent (dim μ) (char μ) * x) = 0 →
      charIdempotent (dim μ) (char μ) * x = 0
  /-- Branching containment: for `lam ⊆ mu` the element
  `e mu * (e lam ⊗ 1) * e mu` of the block of `mu` is nonzero. -/
  branching : ∀ (lam mu : YoungDiagram), lam ≤ mu →
    ∀ h : lam.card ≤ mu.card,
    charIdempotent (dim mu) (char mu) *
        symCast h (charIdempotent (dim lam) (char lam)) *
        charIdempotent (dim mu) (char mu) ≠ 0
  /-- The square-diagram dimensions outgrow every exponential
  `R ^ (s²)`. -/
  square_dim : ∀ R : ℕ, ∃ s : ℕ, R ^ (s ^ 2) < dim (squareDiagram s)
  /-- The Frobenius character formula, stated against the
  Jacobi–Trudi determinant: for every scalar sequence `t`,
  `(1/n!) ∑ π, char μ π · ∏_{c ∈ ρ(π)} t c = s_μ[t]`, where
  `ρ(π)` is the full cycle type including fixed points — the
  `cycleType` of mathlib excludes one-cycles, so the product is
  completed by `(t 1) ^ (#fixed points)`.  (The uncompleted form
  is false already at `n = 1`.) -/
  frobenius : ∀ (μ : YoungDiagram) (t : ℕ → ℂ),
    ((μ.card.factorial : ℂ))⁻¹ *
        ∑ π : Perm (Fin μ.card), char μ π *
          ((π.cycleType.map t).prod *
            (t 1) ^ (μ.card - π.cycleType.sum)) =
      diagramSchur μ t

namespace SchurPackage

/-- The central idempotent of shape `μ`. -/
noncomputable def e (P : SchurPackage) (μ : YoungDiagram) :
    SymGroupAlgebra μ.card :=
  charIdempotent (P.dim μ) (P.char μ)

/-- `e` unfolds to `charIdempotent` of the package's data. -/
theorem e_def (P : SchurPackage) (μ : YoungDiagram) :
    P.e μ = charIdempotent (P.dim μ) (P.char μ) :=
  rfl

end SchurPackage

end RS
