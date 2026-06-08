/-
Copyright (c) 2026 Gerald Doussot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gerald Doussot
-/

/-!
# Hexadecimal String Conversions

This file provides conversions between `ByteArray` values and their hexadecimal
string representations: `Cryptography.HexString.parse` decodes a hex string into a
`ByteArray`, and the `Cryptography.HexString.ToHexString` class (with the
`ByteArray` instance) encodes a `ByteArray` back into a lowercase hex string.

These are convenience helpers for working with the SHA-3 test vectors and are not
intended for use in real cryptographic applications.
-/

namespace Cryptography

namespace HexString

/-- Decode a single hexadecimal character into its 4-bit value. -/
private def hexValue (c : Char) : Except String UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then
    .ok (c.val - '0'.val).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then
    .ok (c.val - 'a'.val + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then
    .ok (c.val - 'A'.val + 10).toUInt8
  else
    .error "invalid hex character"

/-- Decode a list of hexadecimal characters two at a time, appending each decoded
byte to `acc`. -/
private def decodeChars (chars : List Char) (acc : ByteArray) : Except String ByteArray :=
  match chars with
  | [] => .ok acc
  | [_] => .error "odd number of hex characters"
  | c1 :: c2 :: rest => do
    let u1 ← hexValue c1
    let u2 ← hexValue c2
    decodeChars rest (acc.push ((u1 <<< 4) + u2))

/-- Parse a hexadecimal string into a `ByteArray`. -/
def parse (s : String) : Except String ByteArray :=
  decodeChars s.toList (ByteArray.mk #[])

/-- A type whose values can be rendered as a hexadecimal string. -/
class ToHexString (α : Type u) where
  /-- Render a value as a hexadecimal string. -/
  toHexString : α → String

export ToHexString (toHexString)

/-- The lowercase hexadecimal digits, indexed by nibble value. -/
private def hexDigits : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
    'a', 'b', 'c', 'd', 'e', 'f']

/-- Render a `ByteArray` as a lowercase hexadecimal string. -/
private def byteArrayToHexString (bs : ByteArray) : String := Id.run do
  let mut res : String := ""
  for b in bs do
    let hi := (b.toNat &&& 0xf0) >>> 4
    let lo := b.toNat &&& 0x0f
    res := res.push <| hexDigits[hi]!
    res := res.push <| hexDigits[lo]!
  res

instance : ToHexString ByteArray where
  toHexString bs := byteArrayToHexString bs

end HexString

end Cryptography
