/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Topology.Algebra.Valued.ValuativeRel
/-!
# Valued-field topology and the induced valuative relation

This file records the topology bridge used when a nonarchimedean norm is
turned into a `ValuativeRel`: the topology already carried by a nontrivially
valued field is the valuative topology for that induced relation.
-/

@[expose] public section

noncomputable
section

namespace LocalFieldTheory

open scoped ValuativeRel

universe u v

/-- The topology of a nontrivially valued field is valuative for the
valuative relation induced by its distinguished valuation. -/
theorem isValuativeTopology_of_valued_ofValuation
    (F : Type u) (Γ : Type v)
    [Field F] [LinearOrderedCommGroupWithZero Γ]
    [Valued F Γ]
    [Valuation.IsNontrivial (Valued.v : Valuation F Γ)] :
    letI := ValuativeRel.ofValuation (Valued.v : Valuation F Γ)
    IsValuativeTopology F := by
  let v : Valuation F Γ := Valued.v
  let : ValuativeRel F := ValuativeRel.ofValuation v
  let : v.Compatible := Valuation.Compatible.ofValuation v
  let : ValuativeRel.IsNontrivial F :=
    (ValuativeRel.isNontrivial_iff_isNontrivial v).2 inferInstance
  apply IsValuativeTopology.of_zero
  intro s
  rw [Valued.mem_nhds_zero]
  constructor
  · rintro ⟨δ, hδ⟩
    refine
      ⟨δ.mapEquiv
          (ValuativeRel.ValueGroupWithZero.orderMonoidIso v).symm, ?_⟩
    intro z hz
    apply hδ
    exact
      (ValuativeRel.valuation_lt_symm_orderMonoidIso
        v (δ : MonoidWithZeroHom.ValueGroup₀ (.ofClass v)) z).1
        (by simpa using hz)
  · rintro ⟨γ, hγ⟩
    refine
      ⟨γ.mapEquiv
          (ValuativeRel.ValueGroupWithZero.orderMonoidIso v), ?_⟩
    intro z hz
    apply hγ
    have hz' :
        v.restrict z <
          (ValuativeRel.ValueGroupWithZero.orderMonoidIso v)
            (γ : ValuativeRel.ValueGroupWithZero F) := by
      exact hz
    exact
      (ValuativeRel.restrict_lt_orderMonoidIso
        v (γ : ValuativeRel.ValueGroupWithZero F) z).1 hz'

end LocalFieldTheory
