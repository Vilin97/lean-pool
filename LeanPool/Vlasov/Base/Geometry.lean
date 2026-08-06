/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Ambient geometry for the optimal-transport / Vlasov development

Throughout, `d : ℕ` is the spatial dimension.  Single-particle physical space is
`ℝ^d` realised as a Euclidean space; single-particle phase space is its square
(position × velocity).  These are the shared ambient types that both the
optimal-transport layer and the kinetic (Vlasov) layer are built over. -/

namespace Vlasov

/-- Abbreviation for ℝ^d as a Euclidean space. -/
abbrev PhysSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Abbreviation for the single-particle phase space ℝ^d × ℝ^d. -/
abbrev PhaseSpace (d : ℕ) := PhysSpace d × PhysSpace d

end Vlasov
