/-
Copyright (c) 2026 Gerald Doussot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gerald Doussot
-/

import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String


namespace HexString

-- parse hexadecimal string to ByteArray
private def hexChar : Parser UInt8 := do
  let c ← any
  if '0' ≤ c ∧ c ≤ '9' then
    pure $ (c.val - '0'.val).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then
    pure $ (c.val - 'a'.val + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then
    pure $ (c.val - 'A'.val + 10).toUInt8
  else
    fail "invalid hex character"

private def byteChar : Parser UInt8  := do
    let u1 ← hexChar; let u2 ← hexChar
    return  (u1 <<< 4) + u2

private partial def byteCore  (acc : ByteArray) : Parser ByteArray := do
  let some _ ← peek?
    | return acc
    byteCore (acc.push (← byteChar))

def parse (s : String) : Except String ByteArray :=
  match (byteCore (ByteArray.mk #[]) ⟨s, s.startPos⟩) with
  | ParseResult.success _ res => Except.ok res
  | ParseResult.error it err  => Except.error s!"offset {repr it.2.offset.byteIdx}: {err}"

-- ByteArray to String
class ToHexString (α : Type u) where
  toHexString : α → String

export ToHexString (toHexString)

private def chars := #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
                       'a', 'b', 'c', 'd', 'e', 'f']

private def ByteArrayToHexString (bs : ByteArray) : String := Id.run do
  let mut res : String := ""
  for b in bs do
    let hi := (b.toNat &&& 0xf0) >>> 4
    let lo := b.toNat &&& 0x0f
    res := res.push $ chars[hi]!
    res := res.push $ chars[lo]!
  res

instance : ToHexString ByteArray where
  toHexString bs := ByteArrayToHexString bs

--#eval parse "f00110"
--#eval parse ""
--#eval parse "f"

--#eval ToHexString.toHexString (ByteArray.mk #[0, 1, 128,  255])
--#eval toHexString (ByteArray.mk #[0, 1, 128,  255])
end HexString
