/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Multi-period Bicausal OT — history-space topology and measurability

  Blueprint: BLUEPRINT.md §3 (Phase 3 prerequisite D1). Recursive
  `TopologicalSpace` / `PolishSpace` / `MeasurableSpace` / `BorelSpace`
  instances for the nested-product history spaces `PairHist`, `XHist`,
  `YHist` of `BicausalOT.MultiPeriod`, plus continuity and measurability
  of the projections `projX`, `projY`.

  Design: every instance is defined by structural recursion on the time
  index; at each successor level it is *definitionally* the binary-product
  instance over the previous level (via `inferInstanceAs` on the product
  type), so all binary-product API applies definitionally to histories.
-/
module

public import LeanPool.BicausalOT.BicausalOT.MultiPeriod
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic


/-! ### Topological structure

The product topology on histories, by recursion on the time index. -/

@[expose] public section

open MeasureTheory

noncomputable section

namespace MultiPeriod

variable (X Y : ℕ → Type*)



section Topology

variable [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]

/-- Recursive product topology on pair-histories: at each successor level
    this is definitionally the product topology over the previous level. -/
instance instTopologicalSpacePairHist : ∀ t, TopologicalSpace (PairHist X Y t)
  | 0 => inferInstanceAs (TopologicalSpace (X 0 × Y 0))
  | t + 1 =>
    let := instTopologicalSpacePairHist t
    inferInstanceAs
      (TopologicalSpace (PairHist X Y t × (X (t + 1) × Y (t + 1))))

/-- Recursive product topology on X-side histories. -/
instance instTopologicalSpaceXHist : ∀ t, TopologicalSpace (XHist X t)
  | 0 => inferInstanceAs (TopologicalSpace (X 0))
  | t + 1 =>
    let := instTopologicalSpaceXHist t
    inferInstanceAs (TopologicalSpace (XHist X t × X (t + 1)))

/-- Recursive product topology on Y-side histories. -/
instance instTopologicalSpaceYHist : ∀ t, TopologicalSpace (YHist Y t)
  | 0 => inferInstanceAs (TopologicalSpace (Y 0))
  | t + 1 =>
    let := instTopologicalSpaceYHist t
    inferInstanceAs (TopologicalSpace (YHist Y t × Y (t + 1)))

variable {X Y}

/-- The X-side projection of a pair-history is continuous. -/
theorem continuous_projX : ∀ t, Continuous (projX (X := X) (Y := Y) t)
  | 0 => continuous_fst
  | t + 1 =>
    ((continuous_projX t).comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd)

/-- The Y-side projection of a pair-history is continuous. -/
theorem continuous_projY : ∀ t, Continuous (projY (X := X) (Y := Y) t)
  | 0 => continuous_snd
  | t + 1 =>
    ((continuous_projY t).comp continuous_fst).prodMk
      (continuous_snd.comp continuous_snd)

end Topology

/-! ### Polish structure

Histories of Polish coordinates are Polish (binary products of Polish
spaces are Polish). -/

section Polish

variable [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
variable [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]

/-- Pair-histories of Polish coordinates are Polish. -/
instance instPolishSpacePairHist : ∀ t, PolishSpace (PairHist X Y t)
  | 0 => inferInstanceAs (PolishSpace (X 0 × Y 0))
  | t + 1 =>
    let := instPolishSpacePairHist t
    inferInstanceAs (PolishSpace (PairHist X Y t × (X (t + 1) × Y (t + 1))))

/-- X-side histories of Polish coordinates are Polish. -/
instance instPolishSpaceXHist : ∀ t, PolishSpace (XHist X t)
  | 0 => inferInstanceAs (PolishSpace (X 0))
  | t + 1 =>
    let := instPolishSpaceXHist t
    inferInstanceAs (PolishSpace (XHist X t × X (t + 1)))

/-- Y-side histories of Polish coordinates are Polish. -/
instance instPolishSpaceYHist : ∀ t, PolishSpace (YHist Y t)
  | 0 => inferInstanceAs (PolishSpace (Y 0))
  | t + 1 =>
    let := instPolishSpaceYHist t
    inferInstanceAs (PolishSpace (YHist Y t × Y (t + 1)))

end Polish

/-! ### Measurable structure

The product σ-algebra on histories, by recursion on the time index. This
needs only the coordinate σ-algebras (no topology). -/

section Measurable

variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]

/-- Recursive product σ-algebra on pair-histories: at each successor level
    this is definitionally the product σ-algebra over the previous level. -/
instance instMeasurableSpacePairHist : ∀ t, MeasurableSpace (PairHist X Y t)
  | 0 => inferInstanceAs (MeasurableSpace (X 0 × Y 0))
  | t + 1 =>
    let := instMeasurableSpacePairHist t
    inferInstanceAs
      (MeasurableSpace (PairHist X Y t × (X (t + 1) × Y (t + 1))))

/-- Recursive product σ-algebra on X-side histories. -/
instance instMeasurableSpaceXHist : ∀ t, MeasurableSpace (XHist X t)
  | 0 => inferInstanceAs (MeasurableSpace (X 0))
  | t + 1 =>
    let := instMeasurableSpaceXHist t
    inferInstanceAs (MeasurableSpace (XHist X t × X (t + 1)))

/-- Recursive product σ-algebra on Y-side histories. -/
instance instMeasurableSpaceYHist : ∀ t, MeasurableSpace (YHist Y t)
  | 0 => inferInstanceAs (MeasurableSpace (Y 0))
  | t + 1 =>
    let := instMeasurableSpaceYHist t
    inferInstanceAs (MeasurableSpace (YHist Y t × Y (t + 1)))

variable {X Y}

/-- The X-side projection of a pair-history is measurable. -/
theorem measurable_projX : ∀ t, Measurable (projX (X := X) (Y := Y) t)
  | 0 => measurable_fst
  | t + 1 =>
    ((measurable_projX t).comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)

/-- The Y-side projection of a pair-history is measurable. -/
theorem measurable_projY : ∀ t, Measurable (projY (X := X) (Y := Y) t)
  | 0 => measurable_snd
  | t + 1 =>
    ((measurable_projY t).comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)

end Measurable

/-! ### Borel structure

The recursive product σ-algebra is the Borel σ-algebra of the recursive
product topology: binary products of Borel spaces are Borel when one
factor is second countable, and Polishness supplies second countability
at every level. -/

section Borel

variable [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
variable [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
variable [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
variable [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]

/-- Pair-histories of Polish Borel coordinates are Borel: the recursive
    product σ-algebra coincides with the Borel σ-algebra of the recursive
    product topology. -/
instance instBorelSpacePairHist : ∀ t, BorelSpace (PairHist X Y t)
  | 0 => inferInstanceAs (BorelSpace (X 0 × Y 0))
  | t + 1 =>
    let := instBorelSpacePairHist t
    inferInstanceAs (BorelSpace (PairHist X Y t × (X (t + 1) × Y (t + 1))))

/-- X-side histories of Polish Borel coordinates are Borel. -/
instance instBorelSpaceXHist : ∀ t, BorelSpace (XHist X t)
  | 0 => inferInstanceAs (BorelSpace (X 0))
  | t + 1 =>
    let := instBorelSpaceXHist t
    inferInstanceAs (BorelSpace (XHist X t × X (t + 1)))

/-- Y-side histories of Polish Borel coordinates are Borel. -/
instance instBorelSpaceYHist : ∀ t, BorelSpace (YHist Y t)
  | 0 => inferInstanceAs (BorelSpace (Y 0))
  | t + 1 =>
    let := instBorelSpaceYHist t
    inferInstanceAs (BorelSpace (YHist Y t × Y (t + 1)))

end Borel

end MultiPeriod

end
