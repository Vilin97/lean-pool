/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import Lean.Elab.Command
import Mathlib.Tactic.Sat.FromLRAT

/-! # Safe embedded LRAT elaboration

The command below reconstructs an LRAT resolution proof from embedded DIMACS
and certificate strings. It emits ordinary safe Lean theorems for both the
semantic SAT formula and its finite coverage side condition.
-/

namespace Erdos97Octagon

open Lean Elab Command Term

/--
Check an embedded DIMACS formula and split LRAT certificate, then emit safe
theorems for semantic unsatisfiability and a kernel-computed coverage fact.
-/
syntax "lrat_semantic " ident ident
  " semantic_formula " term " coverage_fact " term
  " dimacs " str* " lrat_first " str* " lrat_second " str* : command

elab_rules : command
  | `(lrat_semantic $unsatName:ident $coveredName:ident
        semantic_formula $formulaSyntax:term coverage_fact $coveredSyntax:term
        dimacs $dimacsSyntax:str* lrat_first $firstSyntax:str*
        lrat_second $secondSyntax:str*) => do
      let dimacsText := String.join (dimacsSyntax.toList.map fun part => part.getString)
      let firstText := String.join (firstSyntax.toList.map fun part => part.getString)
      let secondText := String.join (secondSyntax.toList.map fun part => part.getString)
      let certificateText := firstText ++ "\n" ++ secondText
      let unsatDeclarationName := (← getCurrNamespace) ++ unsatName.getId
      let coveredDeclarationName := (← getCurrNamespace) ++ coveredName.getId
      Command.liftTermElabM do
        withOptions (fun options => options.set `maxRecDepth (100000 : Nat)) do
          let semFormula ← elabTermEnsuringType formulaSyntax (mkConst ``Sat.Fmla)
          synthesizeSyntheticMVarsNoPostponing
          let semFormula ← instantiateMVars semFormula
          let coveredType ← elabType coveredSyntax
          synthesizeSyntheticMVarsNoPostponing
          let coveredType ← instantiateMVars coveredType
          let coveredProof ← elabTermEnsuringType (← `(by decide)) coveredType
          synthesizeSyntheticMVarsNoPostponing
          let coveredProof ← instantiateMVars coveredProof
          let (_, _, _, unsatProof) ←
            Mathlib.Tactic.Sat.fromLRATAux dimacsText certificateText unsatDeclarationName
          let unsatType := mkApp2 (mkConst ``Sat.Fmla.proof)
            semFormula (Mathlib.Tactic.Sat.buildClause #[])
          addDecl <| Declaration.thmDecl {
            name := unsatDeclarationName
            levelParams := []
            type := unsatType
            value := unsatProof
          }
          addDocStringCore unsatDeclarationName
            "Unsatisfiability of the semantic branch formula, reconstructed from embedded LRAT."
          addDecl <| Declaration.thmDecl {
            name := coveredDeclarationName
            levelParams := []
            type := coveredType
            value := coveredProof
          }
          addDocStringCore coveredDeclarationName
            "Kernel-computed coverage check for the embedded branch formula."

end Erdos97Octagon
