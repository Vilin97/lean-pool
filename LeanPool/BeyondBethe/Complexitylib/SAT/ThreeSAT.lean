/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.SAT.ThreeCNF
public import LeanPool.BeyondBethe.Complexitylib.SAT.Verifier

/-!
# Encoded CNF-SAT and 3SAT languages

This module names the existing encoded SAT problem as `CNFSAT` and defines
`ThreeSAT` by restricting decoded CNFs to clauses of exactly three literals.
It is a semantic and codec interface only; no complexity-class membership or
reduction claim is made here.

## Main definitions and results

- `CNF.decode3?` — decode a bit string only when it encodes an exact 3-CNF
- `CNFSAT.language` — compatibility name for the existing `SAT.language`
- `ThreeSAT.language` — satisfiable, exactly-three-literal CNF encodings
- `ThreeSAT.falseFormula` — a fixed unsatisfiable exact 3-CNF
- `ThreeSAT.fallbackEncoding` — valid no-instance output for malformed inputs
-/


@[expose] public section

namespace Complexity

namespace SAT

namespace CNF

/-- Decode a concrete SAT bit string and accept it only when every decoded
clause contains exactly three literals. -/
def decode3? (z : List Bool) : Option CNF := do
  let φ ← decode? z
  if φ.Is3CNF then some φ else none

/-- An exact 3-CNF survives encoding followed by restricted decoding. -/
@[simp] theorem decode3?_encode {φ : CNF} (h3 : φ.Is3CNF) :
    decode3? φ.encode = some φ := by
  simp [decode3?, h3]

/-- Restricted decoding is sound for both the concrete encoding and the
exact-three-literal shape. -/
theorem decode3?_sound {z : List Bool} {φ : CNF}
    (h : decode3? z = some φ) : z = φ.encode ∧ φ.Is3CNF := by
  cases hdecode : decode? z with
  | none =>
      simp [decode3?, hdecode] at h
  | some ψ =>
      by_cases h3 : ψ.Is3CNF
      · simp [decode3?, hdecode, h3] at h
        subst φ
        exact ⟨decode?_sound hdecode, h3⟩
      · simp [decode3?, hdecode, h3] at h

/-- Characterization of successful exact-3 decoding. -/
theorem decode3?_eq_some_iff {z : List Bool} {φ : CNF} :
    decode3? z = some φ ↔ z = φ.encode ∧ φ.Is3CNF := by
  constructor
  · exact decode3?_sound
  · rintro ⟨rfl, h3⟩
    exact decode3?_encode h3

/-- The concrete CNF encoding is injective. -/
theorem encode_injective : Function.Injective CNF.encode := by
  intro φ ψ h
  have hdecode := congrArg decode? h
  simpa using hdecode

end CNF

/-! ## CNF-SAT compatibility surface -/

namespace CNFSAT

/-- Compatibility name for the library's existing SAT language, whose inputs
are concrete encodings of satisfiable CNF formulas. -/
abbrev language : Language := Complexity.SAT.language

/-- The compatibility name denotes exactly the existing SAT language. -/
theorem language_eq_sat : language = Complexity.SAT.language := rfl

/-- Membership through the compatibility name is definitionally the existing
SAT membership predicate. -/
@[simp] theorem mem_language_iff_sat (z : List Bool) :
    z ∈ language ↔ z ∈ Complexity.SAT.language := Iff.rfl

/-- A bit string is in CNF-SAT exactly when it decodes to a satisfiable CNF. -/
theorem mem_language_iff_decode (z : List Bool) :
    z ∈ language ↔ ∃ φ : CNF, CNF.decode? z = some φ ∧ φ.Satisfiable := by
  constructor
  · rintro ⟨φ, rfl, hsat⟩
    exact ⟨φ, CNF.decode?_encode φ, hsat⟩
  · rintro ⟨φ, hdecode, hsat⟩
    exact ⟨φ, CNF.decode?_sound hdecode, hsat⟩

/-- Encoding a typed CNF is in CNF-SAT exactly when that formula is
satisfiable. -/
@[simp] theorem encode_mem_language_iff (φ : CNF) :
    φ.encode ∈ language ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨ψ, hencode, hsat⟩
    have hφψ : φ = ψ := CNF.encode_injective hencode
    simpa [hφψ] using hsat
  · exact fun hsat => ⟨φ, rfl, hsat⟩

end CNFSAT

/-! ## 3SAT -/

namespace ThreeSAT

/-- **3SAT** consists of concrete encodings of satisfiable CNFs in which every
clause has exactly three literals. -/
def language : Language :=
  {z | ∃ φ : CNF, z = φ.encode ∧ φ.Is3CNF ∧ φ.Satisfiable}

/-- A bit string is in 3SAT exactly when restricted decoding succeeds with a
satisfiable formula. -/
theorem mem_language_iff_decode3 (z : List Bool) :
    z ∈ language ↔ ∃ φ : CNF, CNF.decode3? z = some φ ∧ φ.Satisfiable := by
  constructor
  · rintro ⟨φ, rfl, h3, hsat⟩
    exact ⟨φ, CNF.decode3?_encode h3, hsat⟩
  · rintro ⟨φ, hdecode, hsat⟩
    obtain ⟨hz, h3⟩ := CNF.decode3?_sound hdecode
    exact ⟨φ, hz, h3, hsat⟩

/-- Encoding a typed CNF belongs to 3SAT exactly when it is an exact 3-CNF
and is satisfiable. -/
@[simp] theorem encode_mem_language_iff (φ : CNF) :
    φ.encode ∈ language ↔ φ.Is3CNF ∧ φ.Satisfiable := by
  constructor
  · rintro ⟨ψ, hencode, h3, hsat⟩
    have hφψ : φ = ψ := CNF.encode_injective hencode
    simpa [hφψ] using And.intro h3 hsat
  · rintro ⟨h3, hsat⟩
    exact ⟨φ, rfl, h3, hsat⟩

/-- Every 3SAT instance is, after forgetting the shape restriction, a CNF-SAT
instance. -/
theorem language_subset_cnfsat : language ⊆ CNFSAT.language := by
  rintro z ⟨φ, hz, _h3, hsat⟩
  exact ⟨φ, hz, hsat⟩

/-- A fixed unsatisfiable exact 3-CNF: one clause forces `x₀`, while the other
forces `¬x₀`. Repeated literals make both clauses have width exactly three. -/
def falseFormula : CNF :=
  [[{ sign := true, var := 0 }, { sign := true, var := 0 },
      { sign := true, var := 0 }],
    [{ sign := false, var := 0 }, { sign := false, var := 0 },
      { sign := false, var := 0 }]]

/-- `falseFormula` has exactly three literals in each clause. -/
@[simp] theorem falseFormula_is3CNF : falseFormula.Is3CNF := by
  decide

/-- `falseFormula` is unsatisfiable. -/
theorem falseFormula_not_satisfiable : ¬falseFormula.Satisfiable := by
  rintro ⟨α, hα⟩
  simp [falseFormula, CNF.eval, Clause.eval, Lit.eval] at hα

/-- A valid encoded 3-CNF no-instance suitable as the target of malformed or
otherwise invalid source inputs in later total reductions. -/
def fallbackEncoding : List Bool := falseFormula.encode

/-- The fallback encoding decodes successfully as `falseFormula`. -/
@[simp] theorem decode3?_fallbackEncoding :
    CNF.decode3? fallbackEncoding = some falseFormula := by
  exact CNF.decode3?_encode falseFormula_is3CNF

/-- The fallback encoding is not a member of 3SAT. -/
theorem fallbackEncoding_not_mem_language : fallbackEncoding ∉ language := by
  rw [fallbackEncoding, encode_mem_language_iff]
  exact fun h => falseFormula_not_satisfiable h.2

end ThreeSAT

end SAT

end Complexity
