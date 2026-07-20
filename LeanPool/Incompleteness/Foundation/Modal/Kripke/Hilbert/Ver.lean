/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomVer
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Soundness
import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown

/-! # Ver -/


namespace LO
namespace Modal

open Kripke

namespace Kripke

open Entailment

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢]

instance [Entailment.Ver 𝓢] : Canonical 𝓢 IsolatedFrameClass := ⟨by
  intro x y Rxy;
  have : (canonicalModel 𝓢) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr axiomVer!
  exact this x _ Rxy;
⟩

end Kripke


namespace Hilbert
namespace Ver

instance _root_.LO.Modal.Hilbert.Ver.Kripke.sound : Sound (Hilbert.Ver) IsolatedFrameClass := by
  have := FrameClass.definedBy_with_axiomK IsolatedFrameClass.DefinedByAxiomVer;
  infer_instance;

instance _root_.LO.Modal.Hilbert.Ver.Kripke.consistent : Entailment.Consistent (Hilbert.Ver) :=
  have := FrameClass.definedBy_with_axiomK IsolatedFrameClass.DefinedByAxiomVer;
  Kripke.Hilbert.consistent_of_FrameClass IsolatedFrameClass

instance _root_.LO.Modal.Hilbert.Ver.Kripke.complete : Complete (Hilbert.Ver) IsolatedFrameClass :=
  inferInstance

end Ver
end Hilbert

end Modal
end LO
