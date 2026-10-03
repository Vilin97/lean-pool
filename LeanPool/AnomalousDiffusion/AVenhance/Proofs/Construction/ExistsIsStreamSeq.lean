/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsStreamSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.NextStreamAdmissible

/-! Provider proof of existence of the recursively constructed stream sequence. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Proofs

/-- Stream-function estimates: recursively choose the zero stream and then apply the one-step
recursion, using stream-function estimates to keep every predecessor admissible. -/
theorem exists_isStreamSeq {β : ℝ} (I : Ingredients β) :
    ∃ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ := by
  let zeroStream : ℝ → Vec 2 → ℝ := fun _ _ => 0
  have hzero : IsAdmissibleStream zeroStream := by
    constructor
    · fun_prop
    · intro n k t x
      rfl
  let seq : ℕ → {ψ : ℝ → Vec 2 → ℝ // IsAdmissibleStream ψ} :=
    Nat.rec ⟨zeroStream, hzero⟩
      (fun m prev =>
        ⟨I.nextStream (m + 1) prev.1 prev.2,
          IsAdmissibleStream.nextStream_isAdmissible I (m + 1) (by omega)
            prev.1 prev.2⟩)
  let Φ : ℕ → ℝ → Vec 2 → ℝ := fun m => (seq m).1
  refine ⟨Φ, ?_⟩
  constructor
  · rfl
  · intro m hm
    refine ⟨(seq (m - 1)).2, ?_⟩
    have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel hm
    change (seq m).1 = I.nextStream m (seq (m - 1)).1 (seq (m - 1)).2
    rw [← hmEq]
    rfl

end AVenhance.Proofs

end
