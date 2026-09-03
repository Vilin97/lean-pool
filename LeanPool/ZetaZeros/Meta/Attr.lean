/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public meta import Lean

/-!
# The `zz_tag` attribute

`@[zz_tag "TAG"]` records which numbered result of the source paper a declaration formalizes, `TAG`
being that result's label (`def_f_z`, `lem_bessel_F`, `prop_simple_real_lower`, `thm_simple`, ...).
It is the analogue of Mathlib's `@[stacks TAG]`.

The tag goes on **every** declaration whose union states the result's content, not merely the first;
scaffolding — helper definitions, hypothesis bundles, proof-local lemmas — stays untagged.
-/

public meta section

open Lean

/-- `@[zz_tag "TAG"]` records which result of the source paper a declaration formalizes.

The syntax node is named `zzTag`, not `zz_tag`: the user-facing *token* keeps the underscore, to
match `@[stacks …]`, but Mathlib's `defsWithUnderscore` linter inspects the declaration name, so the
internal name must be lowerCamelCase. -/
syntax (name := zzTag) "zz_tag " str : attr

/-- Records which result of the source paper a declaration formalizes. -/
initialize zzTagAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `zzTag
    descr := "Records which result of the source paper a declaration formalizes."
    getParam := fun _ stx => do
      match stx with
      | `(attr| zz_tag $s:str) => return s.getString
      | _ => throwError
          "expected zz_tag applied to a single string literal, as in zz_tag \"lem_bessel_F\""
  }
