/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ConnectionRank

/-!
# Hom spaces of the skein category

The morphism spaces of the skein category of a graph parameter: the
free complex module on the `t`-fragments, quotiented by the kernel
of the full-closure pairing.  The edge-rank hypothesis bounds their
rank through the first isomorphism theorem: the quotient by the
kernel is equivalent to the range of the pairing map.
-/

namespace RS

/-- The Hom space of the skein category at arity `t`: the free
module on `t`-fragments modulo the kernel of the connection
pairing. -/
noncomputable def HomSpace (f : ClosedFragment → ℂ) (t : ℕ) : Type 1 :=
  (Fragment (Fin t) →₀ ℂ) ⧸ LinearMap.ker (connectionMap f t)

/-- Hom spaces are abelian groups, being quotients of free
modules. -/
noncomputable instance (f : ClosedFragment → ℂ) (t : ℕ) :
    AddCommGroup (HomSpace f t) :=
  Submodule.Quotient.addCommGroup _

/-- And ℂ-modules. -/
noncomputable instance (f : ClosedFragment → ℂ) (t : ℕ) :
    Module ℂ (HomSpace f t) :=
  Submodule.Quotient.module _

/-- The class of a single fragment in the Hom space. -/
noncomputable def HomSpace.ofFragment (f : ClosedFragment → ℂ)
    {t : ℕ} (F : Fragment (Fin t)) : HomSpace f t :=
  Submodule.Quotient.mk (Finsupp.single F 1)

/-- The Hom space embeds in the range of the connection pairing. -/
noncomputable def HomSpace.equivRange (f : ClosedFragment → ℂ)
    (t : ℕ) :
    HomSpace f t ≃ₗ[ℂ] LinearMap.range (connectionMap f t) :=
  LinearMap.quotKerEquivRange (connectionMap f t)

/-- **The Hom-space dimension bound**: the edge-rank hypothesis
caps the rank of every Hom space at `R ^ t`. -/
theorem HomSpace.rank_le {R : ℕ} (f : EdgeRankParameter R) (t : ℕ) :
    Module.rank ℂ (HomSpace f.val t) ≤ (R : Cardinal) ^ t := by
  rw [(HomSpace.equivRange f.val t).rank_eq]
  exact f.rank_bounded t

end RS
