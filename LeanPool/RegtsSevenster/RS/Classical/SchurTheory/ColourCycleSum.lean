/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.CharClass
public import LeanPool.RegtsSevenster.RS.Common.PermCongr
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SigmaCycleType

/-!
# Discharge of the cycle-type transport hypotheses

`cycleType_permCongr` and `cycleType_sigmaCongrRight` discharge
the `PermCongrCT` and `SigmaCT` hypotheses: the colour cycle sum
and the Frobenius formula for the Jacobi–Trudi character hold
unconditionally.
-/

@[expose] public section

namespace RS

open Finset

/-- Transport preserves cycle type, discharging the colour cycle
sum's hypothesis. -/
theorem permCongrCT : PermCongrCT :=
  fun _ _ _ _ _ _ e σ => cycleType_permCongr e σ

/-- And so does the fibrewise congruence, discharging the Frobenius
formula's. -/
theorem sigmaCT : SigmaCT :=
  fun _ _ _ _ _ _ σ => cycleType_sigmaCongrRight σ

open scoped Classical in
/-- **The Frobenius formula for the Jacobi–Trudi character**,
unconditionally: its normalized cycle-weighted sum is the
Jacobi–Trudi determinant. -/
theorem jtChar_frobenius' (μ : YoungDiagram) (t : ℕ → ℂ) :
    ((μ.card.factorial : ℂ))⁻¹ *
        ∑ π : Equiv.Perm (Fin μ.card),
          jtChar μ π * cycleProd t π =
      diagramSchur μ t :=
  jtChar_frobenius permCongrCT sigmaCT μ t

end RS
