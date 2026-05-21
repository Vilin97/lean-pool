/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Lean
import LeanPool.HopfieldNet.SampCert.Extractor.Extension

open System IO.FS

namespace Lean.ToDafny

def destination : String := "Tests/SampCert.dfy"

def writeLn (ln : String) : IO Unit := do
  let h ← Handle.mk destination Mode.append
  h.putStr "\n"
  h.putStr ln
  h.putStr "\n"

elab "#print_dafny_exports" : command => do
  writeFile destination ""

  writeLn "module {:extern} Random {"
  writeLn "  class {:extern} Random {"
  writeLn "    static method {:extern \"UniformPowerOfTwoSample\"} ExternUniformPowerOfTwoSample(n: nat) returns (u: nat)"
  writeLn "  }"
  writeLn "}"

  writeLn "module {:extern} SampCert {"
  writeLn "  import Random"
  writeLn "  type pos = x: nat | x > 0 witness 1"

  writeLn "  class SLang {\n"

  writeLn "    method UniformPowerOfTwoSample(n: nat) returns (u: nat)"
  writeLn "      requires n >= 1"
  writeLn "    {"
  writeLn "      u := Random.Random.ExternUniformPowerOfTwoSample(n);"
  writeLn "    }"

  let { decls, .. } := extension.getState (← getEnv)
  for decl in decls.reverse do
    let h ← Handle.mk destination Mode.append
    h.putStr decl
  writeLn "}"
  writeLn "}"

end Lean.ToDafny
