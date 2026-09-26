import Batteries.Tactic.Lint

/- Run the same slow declaration linters as Batteries' runLinter, importing
all owned modules together. Filter by module identity so each declaration
is covered exactly once even when one project imports another. -/
open Lean Core Batteries.Tactic.Lint

unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then throw <| IO.userError "no modules to lint"
  let modules := args.toArray.map String.toName
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let imports := (modules.push `Batteries.Tactic.Lint).map fun module =>
    ({ module } : Lean.Import)
  let env ← Lean.importModules imports {} (trustLevel := 1024) (loadExts := true)
  for module in modules do
    unless env.header.moduleNames.contains module do
      throw <| IO.userError s!"missing module in lint environment: {module}"
  let nolintsFile : System.FilePath := "scripts/nolints.json"
  let nolints : Array (Name × Name) ← if ← nolintsFile.pathExists then do
    let json ← IO.ofExcept (Json.parse (← IO.FS.readFile nolintsFile))
    IO.ofExcept (fromJson? json)
  else pure #[]
  let (failed, _) ← CoreM.toIO (ctx := { fileName := "", fileMap := default })
      (s := { env }) do
    let indices := env.header.moduleNames.map modules.contains
    let decls := env.constants.map₁.fold (init := #[]) fun decls name _ =>
      if indices[env.const2ModIdx[name]?.get!]! then decls.push name else decls
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
    let results ← lintCore decls linters (inIO := true) (currentModule := modules[0]!)
    let results := results.map fun (linter, findings) =>
      (linter, nolints.foldl (init := findings) fun findings (linter', declaration) =>
        if linter.name == linter' then findings.erase declaration else findings)
    if results.any (!·.2.isEmpty) then
      let message ← formatLinterResults results decls
        (groupByFilename := true) (useErrorFormat := true)
        s!"in {modules[0]!}" (runSlowLinters := true) .medium linters.size
      IO.println (← message.toString)
      return true
    IO.println s!"Lint passed for {modules.size} modules ({decls.size} declarations)."
    return false
  -- Match runLinter's exit shortcut around Lean IO finalizer races.
  IO.Process.exit (if failed then 1 else 0)
