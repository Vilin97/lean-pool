/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.LRAT.Semantics

/-!
# Versioned packed LRAT format

Deletion records are omitted because retaining proved clauses is sound.  Each
addition stores an identifier delta, signed literals, and backward distances
to its antecedent clauses.  Natural numbers use unsigned base-128 varints and
the resulting bytes use unpadded base64.
-/

namespace Erdos97Octagon.LRAT

/-- Maximum number of bytes accepted for one packed natural number. -/
def packedVarintByteBound : ℕ := 16

/-- One reverse-unit-propagation addition. -/
structure Addition where
  /-- Strictly increasing LRAT clause identifier. -/
  identifier : ℕ
  /-- Signed DIMACS literals in the derived clause. -/
  literals : Array Int
  /-- Earlier clauses used for reverse unit propagation. -/
  antecedents : Array ℕ
deriving BEq

/-- The current position in a packed byte sequence. -/
structure Cursor where
  /-- Complete packed certificate byte sequence. -/
  bytes : ByteArray
  /-- Zero-based position of the next unread byte. -/
  position : ℕ

private def base64Byte (value : ℕ) : Except String UInt8 :=
  if value < 26 then
    pure (UInt8.ofNat (65 + value))
  else if value < 52 then
    pure (UInt8.ofNat (97 + value - 26))
  else if value < 62 then
    pure (UInt8.ofNat (48 + value - 52))
  else if value = 62 then
    pure 43
  else if value = 63 then
    pure 47
  else
    throw "base64 value exceeds six bits"

private def base64Value (character : UInt8) : Except String ℕ :=
  let value := character.toNat
  if 65 ≤ value ∧ value ≤ 90 then
    pure (value - 65)
  else if 97 ≤ value ∧ value ≤ 122 then
    pure (value - 97 + 26)
  else if 48 ≤ value ∧ value ≤ 57 then
    pure (value - 48 + 52)
  else if character = 43 then
    pure 62
  else if character = 47 then
    pure 63
  else
    throw s!"invalid base64 byte {value}"

/-- Encode bytes as unpadded base64. -/
def encodeBase64 (bytes : ByteArray) : Except String String := do
  let mut output := ByteArray.empty
  for block in [0:(bytes.size + 2) / 3] do
    let offset := 3 * block
    let some first := bytes[offset]?
      | throw "base64 encoder index is out of range"
    let a := first.toNat
    output := output.push (← base64Byte (a / 4))
    if offset + 1 = bytes.size then
      output := output.push (← base64Byte ((a % 4) * 16))
    else
      let some second := bytes[offset + 1]?
        | throw "base64 encoder second byte is missing"
      let b := second.toNat
      output := output.push (← base64Byte ((a % 4) * 16 + b / 16))
      if offset + 2 = bytes.size then
        output := output.push (← base64Byte ((b % 16) * 4))
      else
        let some third := bytes[offset + 2]?
          | throw "base64 encoder third byte is missing"
        let c := third.toNat
        output := output.push (← base64Byte ((b % 16) * 4 + c / 64))
        output := output.push (← base64Byte (c % 64))
  match String.fromUTF8? output with
  | some text => pure text
  | none => throw "base64 encoder produced invalid UTF-8"

/-- Decode unpadded base64. -/
def decodeBase64 (text : String) : Except String ByteArray := do
  let characters := text.toUTF8
  if characters.size % 4 = 1 then
    throw "invalid one-character base64 tail"
  let mut output := ByteArray.empty
  for block in [0:(characters.size + 3) / 4] do
    let offset := 4 * block
    let some first := characters[offset]?
      | throw "base64 decoder index is out of range"
    let some second := characters[offset + 1]?
      | throw "base64 decoder second byte is missing"
    let a ← base64Value first
    let b ← base64Value second
    output := output.push (UInt8.ofNat (a * 4 + b / 16))
    if offset + 2 < characters.size then
      let some third := characters[offset + 2]?
        | throw "base64 decoder third byte is missing"
      let c ← base64Value third
      output := output.push (UInt8.ofNat ((b % 16) * 16 + c / 4))
      if offset + 3 < characters.size then
        let some fourth := characters[offset + 3]?
          | throw "base64 decoder fourth byte is missing"
        let d ← base64Value fourth
        output := output.push (UInt8.ofNat ((c % 4) * 64 + d))
      else if c % 4 ≠ 0 then
        throw "nonzero padding bits in base64 tail"
    else if b % 16 ≠ 0 then
      throw "nonzero padding bits in base64 tail"
  pure output

private def appendVarintWithFuel :
    ℕ → ℕ → ByteArray → Except String ByteArray
  | 0, _, _ => throw "natural number exceeds packed varint bound"
  | fuel + 1, value, output =>
      if value < 128 then
        pure <| output.push (UInt8.ofNat value)
      else
        appendVarintWithFuel fuel (value / 128)
          (output.push (UInt8.ofNat (value % 128 + 128)))

private def appendVarint (value : ℕ) (output : ByteArray) :
    Except String ByteArray :=
  appendVarintWithFuel packedVarintByteBound value output

private def readByte (cursor : Cursor) : Except String (UInt8 × Cursor) :=
  match cursor.bytes[cursor.position]? with
  | none => throw "unexpected end of packed certificate"
  | some byte => pure (byte, { cursor with position := cursor.position + 1 })

private def readVarintWithFuel :
    ℕ → ℕ → ℕ → Cursor → Except String (ℕ × Cursor)
  | 0, _, _, _ => throw "packed varint exceeds decoder bound"
  | fuel + 1, multiplier, value, cursor => do
      let (byte, cursor) ← readByte cursor
      let payload := byte.toNat % 128
      let value := value + multiplier * payload
      if byte.toNat < 128 then
        pure (value, cursor)
      else
        readVarintWithFuel fuel (multiplier * 128) value cursor

private def readVarint (cursor : Cursor) : Except String (ℕ × Cursor) :=
  readVarintWithFuel packedVarintByteBound 1 0 cursor

private def literalCode (literal : Int) : Except String ℕ :=
  if literal = 0 then
    throw "zero is not a literal"
  else if literal < 0 then
    pure (2 * ((-literal).toNat - 1) + 1)
  else
    pure (2 * (literal.toNat - 1))

private def literalOfCode (code : ℕ) : Int :=
  if code % 2 = 0 then
    Int.ofNat (code / 2 + 1)
  else
    -Int.ofNat (code / 2 + 1)

private def appendLiterals
    (literals : Array Int) (output : ByteArray) : Except String ByteArray := do
  let mut output ← appendVarint literals.size output
  for literal in literals do
    output ← appendVarint (← literalCode literal) output
  pure output

private def appendAntecedents
    (identifier : ℕ) (antecedents : Array ℕ) (output : ByteArray) :
    Except String ByteArray := do
  let mut output ← appendVarint antecedents.size output
  for antecedent in antecedents do
    if antecedent = 0 ∨ identifier ≤ antecedent then
      throw s!"antecedent {antecedent} is not before clause {identifier}"
    output ← appendVarint (identifier - antecedent) output
  pure output

private def appendAddition
    (previous : ℕ) (addition : Addition) (output : ByteArray) :
    Except String ByteArray := do
  if addition.identifier ≤ previous then
    throw "clause identifiers are not strictly increasing"
  let output ← appendVarint (addition.identifier - previous) output
  let output ← appendLiterals addition.literals output
  appendAntecedents addition.identifier addition.antecedents output

/-- Pack additions after the initial clause range. -/
def encodeAdditions
    (initialClauseCount : ℕ) (additions : Array Addition) :
    Except String ByteArray := do
  let mut previous := initialClauseCount
  let mut output := ByteArray.empty
  for addition in additions do
    output ← appendAddition previous addition output
    previous := addition.identifier
  pure output

private def readLiterals
    (count : ℕ) (initialCursor : Cursor) :
    Except String (Array Int × Cursor) := do
  let mut cursor := initialCursor
  let mut result := Array.mkEmpty count
  for _ in [0:count] do
    let (code, nextCursor) ← readVarint cursor
    result := result.push (literalOfCode code)
    cursor := nextCursor
  pure (result, cursor)

private def readAntecedents
    (identifier count : ℕ) (initialCursor : Cursor) :
    Except String (Array ℕ × Cursor) := do
  let mut cursor := initialCursor
  let mut result := Array.mkEmpty count
  for _ in [0:count] do
    let (distance, nextCursor) ← readVarint cursor
    if distance = 0 ∨ identifier < distance then
      throw "invalid backward antecedent distance"
    result := result.push (identifier - distance)
    cursor := nextCursor
  pure (result, cursor)

private def readAddition
    (previous : ℕ) (cursor : Cursor) : Except String (Addition × Cursor) := do
  let (identifierDelta, cursor) ← readVarint cursor
  if identifierDelta = 0 then
    throw "zero clause identifier delta"
  let identifier := previous + identifierDelta
  let (literalCount, cursor) ← readVarint cursor
  let (literals, cursor) ← readLiterals literalCount cursor
  let (antecedentCount, cursor) ← readVarint cursor
  let (antecedents, cursor) ← readAntecedents identifier antecedentCount cursor
  pure ({ identifier, literals, antecedents }, cursor)

/-- Decode exactly `additionCount` packed additions and reject trailing bytes. -/
def decodeAdditions
    (initialClauseCount additionCount : ℕ) (bytes : ByteArray) :
    Except String (Array Addition) := do
  let mut previous := initialClauseCount
  let mut cursor : Cursor := { bytes, position := 0 }
  let mut additions := Array.mkEmpty additionCount
  for _ in [0:additionCount] do
    let (addition, nextCursor) ← readAddition previous cursor
    additions := additions.push addition
    previous := addition.identifier
    cursor := nextCursor
  if cursor.position = bytes.size then
    pure additions
  else
    throw "trailing bytes after packed certificate"

end Erdos97Octagon.LRAT
