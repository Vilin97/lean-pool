/-
Copyright (c) 2026 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import Lean

/-!
# CSV parser for atomic positions and user input

This file provides a small CSV/`Float` parsing layer used to read atomic positions and
simulation parameters from text input.
-/

namespace LeanLJ

/-- Parse a string such as `"-1.25"` into a `Float`, returning `none` on malformed input. -/
def parseFloatOpt (s : String) : Option Float := Id.run do
  let s := s.trimAscii.toString
  if s.isEmpty then return none
  let isNeg := s.startsWith "-"
  let s := if isNeg then (s.drop 1).toString else s
  if s.isEmpty then return none
  let parts := s.splitOn "."
  match parts with
  | [intStr] =>
    let some intVal ← intStr.toNat? | return none
    let val := intVal.toFloat
    return if isNeg then some (-val) else some val
  | [intStr, fracStr] =>
    if intStr.isEmpty && fracStr.isEmpty then return none
    let intVal := (intStr.toNat?).getD 0
    let fracVal := (fracStr.toNat?).getD 0
    let fracPow := 10.0 ^ (fracStr.length.toFloat)
    let val := intVal.toFloat + (fracVal.toFloat / fracPow)
    return if isNeg then some (-val) else some val
  | _ => return none

/-- Parse a string into a `Float`, defaulting to `0.0` on malformed input. -/
def stringToFloat (s : String) : Float :=
  match parseFloatOpt s with
  | some f => f
  | none => 0.0

/-- Parse a comma-separated line `"x,y,z"` into a 3-vector of `Float`s. -/
def parseLineToFin3 (line : String) : Option (Fin 3 → Float) :=
  match line.splitOn "," with
  | [x, y, z] =>
    let values := [stringToFloat x, stringToFloat y, stringToFloat z]
    some (fun i =>
      match i.val with
      | 0 => values.getD 0 0.0
      | 1 => values.getD 1 0.0
      | 2 => values.getD 2 0.0
      | _ => 0.0)
  | _ => none

/-- Parse an array of CSV lines into a list of 3-vectors, skipping malformed lines. -/
def parseCSVToFin3 (lines : Array String) : List (Fin 3 → Float) :=
  lines.foldl (fun acc line =>
    match parseLineToFin3 line with
    | some vec => vec :: acc
    | none => acc) [] |>.reverse

/-- Interactively read a single positive `Float` from standard input, re-prompting on
invalid input. -/
def readSinglePositiveFloat (prompt : String) : IO Float := do
  let stdout ← IO.getStdout
  let stdin ← IO.getStdin
  let mut validInput := false
  let mut value := 0.0
  while !validInput do
    stdout.putStrLn prompt
    let input := (← stdin.getLine).trimAscii.toString
    let parsed := stringToFloat input
    if parsed > 0 && !input.contains ',' then
      validInput := true
      value := parsed
    else
      stdout.putStrLn "Invalid input. Please enter a single positive float value."
  return value

/-- Interactively read three comma-separated positive `Float`s describing a box length,
re-prompting on invalid input. -/
def readBoxLength (prompt : String) : IO (Fin 3 → Float) := do
  let stdout ← IO.getStdout
  let stdin ← IO.getStdin
  let mut validInput := false
  let mut boxLength : Fin 3 → Float := fun _ => 0.0
  while !validInput do
    stdout.putStrLn prompt
    let input := (← stdin.getLine).trimAscii.toString
    let parts := input.splitOn ","
    if parts.length == 3 then
      let parsed := parts.map stringToFloat
      if parsed.all (· > 0) then
        validInput := true
        boxLength := fun i =>
          match i.val with
          | 0 => parsed.getD 0 0.0
          | 1 => parsed.getD 1 0.0
          | 2 => parsed.getD 2 0.0
          | _ => 0.0
      else
        stdout.putStrLn "Invalid input. All box length values must be positive."
    else
      stdout.putStrLn "Invalid input. Please enter exactly three comma-separated positive float values."
  return boxLength

end LeanLJ
