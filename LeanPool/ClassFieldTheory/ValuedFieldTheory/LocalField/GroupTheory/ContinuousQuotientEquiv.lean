/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
/-!
# Continuous equivalences of quotient groups

This module supplies the quotient equivalence induced by a continuous
multiplicative equivalence.  It belongs to the general local-field support
layer and does not depend on the separate pro-\(C\) groups library.
-/

@[expose] public section

open scoped Topology

noncomputable
section

namespace LocalFieldTheory.QuotientGroup

universe u v

variable {G : Type u} {H : Type v}
variable [Group G] [TopologicalSpace G]
variable [Group H] [TopologicalSpace H]

/-- A continuous multiplicative equivalence descends to continuously
equivalent quotients when it maps one normal subgroup onto the other. -/
noncomputable def continuousCongr
    (N : Subgroup G) (M : Subgroup H) [N.Normal] [M.Normal]
    (e : G ≃ₜ* H) (h : N.map e.toMulEquiv.toMonoidHom = M) :
    G ⧸ N ≃ₜ* H ⧸ M := by
  let eAlg : G ⧸ N ≃* H ⧸ M :=
    QuotientGroup.congr (G' := N) (H' := M) e.toMulEquiv h
  refine
    { toMulEquiv := eAlg
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · refine (QuotientGroup.isQuotientMap_mk N).continuous_iff.2 ?_
    change Continuous fun x : G => QuotientGroup.mk' M (e x)
    exact continuous_quotient_mk'.comp e.continuous_toFun
  · refine (QuotientGroup.isQuotientMap_mk M).continuous_iff.2 ?_
    have hsymm : M.map e.symm.toMulEquiv.toMonoidHom = N :=
      (Subgroup.map_symm_eq_iff_map_eq (K := N) (H := M)
        (e := e.toMulEquiv)).mpr h
    change Continuous fun y : H => QuotientGroup.mk' N (e.symm y)
    exact continuous_quotient_mk'.comp e.symm.continuous_toFun

/-- The descended equivalence acts on quotient classes through the original
equivalence. -/
theorem continuousCongr_mk
    (N : Subgroup G) (M : Subgroup H) [N.Normal] [M.Normal]
    (e : G ≃ₜ* H) (h : N.map e.toMulEquiv.toMonoidHom = M) (g : G) :
    continuousCongr N M e h (QuotientGroup.mk' N g) =
      QuotientGroup.mk' M (e g) :=
  rfl

end LocalFieldTheory.QuotientGroup
