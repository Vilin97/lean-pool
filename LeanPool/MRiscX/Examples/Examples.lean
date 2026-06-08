/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Basic
import LeanPool.MRiscX.Tactics.ApplySpec
/-!
New Code Proofs
-/

/-
An example of the first block of the otp implementation from `OtpProof.lean`.
We can use either actual numbers or variables as registers or values.
-/
example (p k c l : UInt64) :
    mriscx
      first:
          la x 0, p
          la x 1, k
          la x 2, c
          li x 3, l
    end
    /-
    The precondition ¬⸨terminated⸩ is a quite common one, as it assert that the terminated
    flag is false. Only then, the machinestate is in a legal state and the next instruction
    can be executed.
    -/
    ⦃¬⸨terminated⸩⦄
    /-
    The entry point of the program is the label **`first`**. As shown, label names can be used
    directly in Hoare triples as strings; during elaboration, these label names are resolved
    to concrete line numbers.

    The program currently looks as follows:
    mriscx
      first:
    line 0:  la x 0, p
    line 1:  la x 1, k
    line 2:  la x 2, c
    line 3:  li x 3, l

    line 4  ...
    end
    The goal is to stop execution after the instruction `li x 3, l`, with the program counter
    pointing to line 4. During execution, no lines other than 0–3 should be visited.


    However, the Hoare-style logic mathcal{L}_{AS} by Lundberg et al. treats the state
    before the first instruction is executed as the state where the program counter already
    points to line 0, and it only considers states after at least one execution step.
    Therefore, to prevent control flow from jumping back to the initial instruction, we must
    add line 0 (corresponding to the label `first`) to the blacklist. This guarantees that
    line 0 is not revisited during execution.
    Also, because the program counter points to line 4 after the execution of `li x 3, l`,
    we want to add n : UInt64 | n > 4 to the blacklist.
    -/
    "first" ↦ ⟨{"first" + 4} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > ("first" + 4)})⟩
    /-
    This postcondition asserts, that the registers have the correct values and addresses loaded
    after executing the program. Also, the machine state still is in a legal state since no
    illegal instruction was executed and we did not visit any line, which holds no instruction.

    In the current version, it is necessary to put the preconditions and postconditions in
    parentheses, with the exception of `¬⸨terminated⸩` (e.G.
    ⦃**(** x[0] = ∧ x[1] = 1 **)** ∧ ¬⸨terminated⸩⦄), in order to successfully apply the
    specification.
    -/
    ⦃(x[0] = p ∧ x[1] = k ∧ x[2] = c ∧ x[3] = l) ∧ ¬⸨terminated⸩⦄
  := by
  /- Too peel off the last instruction in order to be able to inspect that individually, we
    apply s_apply_seq''', a custom tactic which applies the rule `S-SEQ` and automatically
    solves some trivial goals. -/
  sapplySSeq P := ⦃¬⸨terminated⸩⦄ ,
                  R := ⦃(x[0] = p ∧ x[1] = k ∧ x[2] = c) ∧ ¬⸨terminated⸩⦄,
                  L_W := {3},
                  L_W' := {4},
                  L_B := ({n:UInt64| n > 3} ∪ {0}),
                  L_B' := ({n:UInt64| n ≠ 4})
  · sapplySSeq P := ⦃¬⸨terminated⸩⦄,
                    R := ⦃(x[0] = p ∧ x[1] = k) ∧ ¬⸨terminated⸩⦄,
                    L_W := {2},
                    L_W' := {3},
                    L_B := ({n:UInt64| n > 2} ∪ {0}),
                    L_B' := ({n:UInt64| n ≠ 3})
    · sapplySSeq -- P := ⦃¬⸨terminated⸩⦄ → can be omitted
                      R := ⦃(x[0] = p) ∧ ¬⸨terminated⸩⦄,
                      L_W := {1},
                      L_W' := {2},
                      L_B := ({n:UInt64| n ≠ 1}),
                      L_B' := ({n:UInt64| n ≠ 2})
      /- At this point, every instruction was isolated. Now we just have to show
        the correctness of each single instruction.
        We can do this, by applying the specification of the instruction respectively.
        For this, the tactic applySpec can be used. This custom tactic applies the
        specification and handles the generated goals.
        To apply the specification, we have to provide some values.
          l := The line the programcounter currently points to.
          r := The register which is being modified.
          v := The value we want to load into the register.
        The parameters differ to each specification.1 -/
      · applySpec specification_LoadAddress (pc := 0) (dst := 0) (addr := p)
      · applySpec specification_LoadAddress (pc := 1) (dst := 1) (addr := k)
    · applySpec specification_LoadAddress (pc := 2) (dst := 2) (addr := c)
  · applySpec specification_LoadImmediate (pc := 3) (dst := 3) (val := l)

/-- Whether four register indices are pairwise distinct; a convenience predicate
used to avoid repetition while writing the example Hoare triples. -/
def pairwiseDistinct (r₁ r₂ r₃ r₄ : UInt64) :=
  r₁ ≠ r₂
  ∧ r₁ ≠ r₃
  ∧ r₁ ≠ r₄
  ∧ r₂ ≠ r₃
  ∧ r₂ ≠ r₄
  ∧ r₃ ≠ r₄

/-
Use variables for registers and addresses / values
-/
example (r₁ r₂ r₃ r₄ : UInt64) (p k c l : UInt64) :
    mriscx
      first:
            la x r₁, p
            la x r₂, k
            la x r₃, c
            li x r₄, l
    end
    ⦃
      pairwiseDistinct r₁ r₂ r₃ r₄
      ∧ ¬⸨terminated⸩
    ⦄
    "first" ↦ ⟨{"first" + 4} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > ("first" + 4)})⟩
    ⦃((x[r₁] = p ∧ x[r₂] = k ∧ x[r₃] = c ∧ x[r₄] = l))
      ∧ ¬⸨terminated⸩⦄
  := by
  sapplySSeq
                  R := ⦃(x[r₁] = p ∧ x[r₂] = k ∧ x[r₃] = c
                        ∧ pairwiseDistinct r₁ r₂ r₃ r₄)
                        ∧ ¬⸨terminated⸩⦄,
                  L_W := {3},
                  L_W' := {4},
                  L_B := ({n:UInt64| n > 3} ∪ {0}),
                  L_B' := ({n:UInt64| n ≠ 4})
  · sapplySSeq
                    R := ⦃(x[r₁] = p ∧ x[r₂] = k
                          ∧ pairwiseDistinct r₁ r₂ r₃ r₄)
                          ∧ ¬⸨terminated⸩⦄,
                    L_W := {2},
                    L_W' := {3},
                    L_B := ({n:UInt64| n > 2} ∪ {0}),
                    L_B' := ({n:UInt64| n ≠ 3})
    · sapplySSeq
                      R := ⦃(x[r₁] = p
                            ∧ pairwiseDistinct r₁ r₂ r₃ r₄)
                            ∧ ¬⸨terminated⸩⦄,
                      L_W := {1},
                      L_W' := {2},
                      L_B := ({n:UInt64| n ≠ 1}),
                      L_B' := ({n:UInt64| n ≠ 2})
      · applySpec specification_LoadAddress (pc := 0) (dst := r₁) (addr := p)
      · applySpec specification_LoadAddress (pc := 1) (dst := r₂) (addr := k)
    · applySpec specification_LoadAddress (pc := 2) (dst := r₃) (addr := c)
  · applySpec specification_LoadImmediate (pc := 3) (dst := r₄) (val := l)


example :
    mriscx
      first:  li x 0, 2
              li x 1, 0
              la x 2, 0x123
    end
    -- Assert assignment of register as precondition
    ⦃¬⸨terminated⸩ ∧ x[4] = 123⦄
    "first" ↦ ⟨{3} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 3})⟩
    ⦃(x[0] = 2 ∧ x[1] = 0 ∧ x[2] = 0x123 ∧ x[4] = 123) ∧ ¬⸨terminated⸩⦄
  := by
  /-
  apply s_seq with automatically solve set equality
  -/
  sapplySSeq  P := _ ,
                  R := ⦃(x[0] = 2 ∧ x[1] = 0 ∧ x[4] = 123) ∧ ¬⸨terminated⸩⦄,
                  L_W := {2},
                  L_W' := {3},
                  L_B := ({n:UInt64| n > 2} ∪ {0}),
                  L_B' := ({n:UInt64| n ≠ 3})
    /-
    apply s_seq without automatically solve set equality
    -/
  · sapplySSeq''  R := ⦃(x[0] = 2 ∧ x[4] = 123) ∧ ¬⸨terminated⸩⦄,
                    L_W := {1},
                    L_W' := {2},
                    L_B := ({n:UInt64| n ≠ 1}),
                    L_B' := ({n:UInt64| n ≠ 2})
    · applySpec''
    · applySpec''
    · simpSetEq
  · applySpec''



example :
    mriscx
      first:  li x 0, 2
              li x 1, 0
              la x 2, 0x123
    end
    -- Assert assignment of register as precondition
    ⦃¬⸨terminated⸩ ∧ x[4] = 123⦄
    "first" ↦ ⟨{3} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 3})⟩
    ⦃(x[0] = 2 ∧ x[1] = 0 ∧ x[2] = 0x123 ∧ x[4] = 123) ∧ ¬⸨terminated⸩⦄
  := by
  /-
  apply s_seq with automatically solve set equality
  -/
  sapplySSeq  P := _ ,
                  R := ⦃(x[0] = 2 ∧ x[1] = 0 ∧ x[4] = 123) ∧ ¬⸨terminated⸩⦄,
                  L_W := {2},
                  L_W' := {3},
                  L_B := ({n:UInt64| n > 2} ∪ {0}),
                  L_B' := ({n:UInt64| n ≠ 3})
    /-
    apply s_seq without automatically solve set equality
    -/
  · sapplySSeq''  R := ⦃(x[0] = 2 ∧ x[4] = 123) ∧ ¬⸨terminated⸩⦄,
                    L_W := {1},
                    L_W' := {2},
                    L_B := ({n:UInt64| n ≠ 1}),
                    L_B' := ({n:UInt64| n ≠ 2})
    · applySpec''
    · applySpec specification_LoadImmediate (pc := 1) (dst := 1) (val := 0)
    · simpSetEq
  · applySpec specification_LoadAddress (pc := 2) (dst := 2) (addr := 0x123)


/-- An example program of type `Code`, used to demonstrate referring to a named
`Code` value inside a Hoare triple. -/
def code : Code :=
    mriscx
      first:  li x 0, 2
              li x 1, 0
              la x 2, 0x123
    end

example :
    code
    ⦃¬⸨terminated⸩⦄
    "first" ↦ ⟨{3} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 3})⟩
    ⦃(x[0] = 2 ∧ x[1] = 0 ∧ x[2] = 0x123) ∧ ¬⸨terminated⸩⦄
  := by
  -- Identifier needs to be unfolded
  unfold code
  sapplySSeq
                  R := ⦃(x[0] = 2 ∧ x[1] = 0 ) ∧ ¬⸨terminated⸩⦄,
                  L_W := {2},
                  L_W' := {3},
                  L_B := ({n:UInt64| n > 2} ∪ {0}),
                  L_B' := ({n:UInt64| n ≠ 3})
  · sapplySSeq
                    R := ⦃(x[0] = 2) ∧ ¬⸨terminated⸩⦄,
                    L_W := {1},
                    L_W' := {2},
                    L_B := ({n:UInt64| n ≠ 1}),
                    L_B' := ({n:UInt64| n ≠ 2})
    · applySpec''
    · applySpec''
  · applySpec' specification_LoadAddress



/--
Usage of autoSeq
-/
example :
    code
    ⦃¬⸨terminated⸩⦄
    "first" ↦ ⟨{3} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 3})⟩
    ⦃(x[0] = 2 ∧ x[1] = 0 ∧ x[2] = 0x123) ∧ ¬⸨terminated⸩⦄
  := by
  unfold code
  -- use tactic `autoSeq` which automatically applies S_SEQ and calcs missing values
  autoSeq
  · autoSeq
    · applySpec''
    · applySpec''
  · applySpec''


/--
Usage of autoSeq with variables
-/
example (r₀ r₁ p : UInt64) :
    r₀ ≠ r₁ →
    r₀ ≠ 2 →
    2 ≠ r₁ →
    mriscx
      first:  li x r₀, p
              li x r₁, 0
              la x 2, 0x123
    end
    ⦃¬⸨terminated⸩⦄
    "first" ↦ ⟨{3} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 3})⟩
    ⦃(x[r₀] = p ∧ x[r₁] = 0 ∧ x[2] = 0x123) ∧ ¬⸨terminated⸩⦄
  := by
  intros h₁ h₂ h₃
  autoSeq
  · autoSeq
    · applySpec specification_LoadImmediate (pc := 0) (dst := r₀) (val := p)
    · applySpec specification_LoadImmediate (pc := 1) (dst := r₁) (val := 0)
      -- TODO automate this:
      · have : (r₁ ↦ 0; (2 ↦ 291; s.registers)).get r₀ = p := by assumption
        rw [t_update_neq, t_update_neq] at this
        · exact this
        · apply Ne.symm
          exact h₂
        · apply Ne.symm
          assumption
      · rw [t_update_neq, t_update_eq]
        assumption
      -- /:
  · applySpec specification_LoadAddress (dst := 2) (pc := 2) (addr := 291)


example :
  mriscx
    first:  li x 0, 6
            li x 1, 123
            xor x 2, x 0, x 1
            la x 3, 0x321
            sw x 2, x 3
  end
  ⦃¬⸨terminated⸩⦄
  "first" ↦ ⟨{"first" + 5} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 5})⟩
  ⦃
    (x[0] = 6 ∧ x[1] = 123 ∧
    x[2] = x[0] ^^^ x[1] ∧ x[3] = 0x321 ∧ mem[x[3]] = x[2]) ∧
    ¬⸨terminated⸩⦄
:= by
  sapplySSeq
                -- P := P ,
                R := ⦃(x[0] = 6 ∧ x[1] = 123
                      ∧ x[2] = x[0] ^^^ x[1]
                      ∧ x[3] = 0x321)
                      ∧ ¬⸨terminated⸩⦄,
                L_W := {4},
                L_W' := {5},
                L_B := ({n:UInt64| n > 4} ∪ {0}),
                L_B' := ({n:UInt64| n ≠ 5})
  · sapplySSeq
                    -- P := P ,
                    R := ⦃(x[0] = 6 ∧ x[1] = 123
                          ∧ x[2] = x[0] ^^^ x[1])
                          ∧ ¬⸨terminated⸩⦄,
                    L_W := {3},
                    L_W' := {4},
                    L_B := ({n:UInt64| n > 3} ∪ {0}),
                    L_B' := ({n:UInt64| n ≠ 4})
    · sapplySSeq
                      -- P := P,
                      R := ⦃(x[0] = 6
                            ∧ x[1] = 123)
                            ∧ ¬⸨terminated⸩⦄,
                      L_W := {2},
                      L_W' := {3},
                      L_B := ({n:UInt64| n > 2} ∪ {0}),
                      L_B' := ({n:UInt64| n ≠ 3})
      · sapplySSeq
                        -- P := P,
                        R := ⦃(x[0] = 6) ∧ ¬⸨terminated⸩⦄,
                        L_W := {1},
                        L_W' := {2},
                        L_B := ({n:UInt64| n ≠ 1}),
                        L_B' := ({n:UInt64| n ≠ 2})
        · applySpec specification_LoadImmediate (pc := 0) (dst := 0) (val := 6)
        · applySpec specification_LoadImmediate (pc := 1) (dst := 1) (val := 123)
      · applySpec specification_XOR (pc := 2) (dst := 2) (reg1 := 0) (reg2 := 1)
    · applySpec specification_LoadAddress (pc := 3) (dst := 3) (addr := 0x321)
  · applySpec specification_StoreWordImmediate (pc := 4) (regWithValue := 2) (regWithAddr := 3)
