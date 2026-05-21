/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Lean
import LeanPool.HopfieldNet.SampCert.Extractor.Extension

open System IO.FS

namespace Lean.ToDafny

def destination : String := "../src/DafnyVMCTrait.dfy"

def writeLn (ln : String) : IO Unit := do
  let h ← Handle.mk destination Mode.append
  h.putStr "\n"
  h.putStr ln
  h.putStr "\n"

elab "#print_vmc_exports" : command => do
  writeFile destination ""
  writeLn "module DafnyVMCTrait {"
  writeLn "  import UniformPowerOfTwo"
  writeLn "  import FisherYates"
  writeLn "  import opened Pos"
  writeLn "  import Uniform"

  writeLn "  trait {:termination false} RandomTrait extends  UniformPowerOfTwo.Interface.Trait, FisherYates.Implementation.Trait, Uniform.Interface.Trait {\n"

  let { decls, .. } := extension.getState (← getEnv)
  for decl in decls.reverse do
    --IO.println decl
    let h ← Handle.mk destination Mode.append
    h.putStr decl
  writeLn "}"
  writeLn "}"

end Lean.ToDafny
