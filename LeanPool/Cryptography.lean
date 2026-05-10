/-
Copyright (c) 2026 Gerald Doussot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gerald Doussot
-/

import LeanPool.Cryptography.Hashes.SHA3.Basic
import LeanPool.Cryptography.Hashes.SHA3.Lemmas

/-!
# Cryptography Experiments In Lean 4: SHA-3 Implementation

Source: url:https://eprint.iacr.org/2024/1880
Authors: Gerald Doussot
Status: verified
Main declarations: `SHA3_224`, `SHA3_256`, `SHA3_384`, `SHA3_512`, `SHAKE128`, `SHAKE256`, `HashFunction.hashData`
Tags: cryptography, hash-functions, sha3
-/

/-!
## Overview

A pure Lean 4 implementation of the SHA-3 family of cryptographic hash
functions (SHA3-224, SHA3-256, SHA3-384, SHA3-512) and the
extendable-output functions SHAKE128 and SHAKE256, as standardised in
NIST FIPS 202. The library exposes both one-shot (`HashFunction.hashData`)
and streaming (`HashFunction.update` / `HashFunction.final`) APIs, and
all internal array accesses are formally proven to be within bounds.

## Provenance

Imported from <https://github.com/gdncc/cryptography>; ported from
Lean v4.27.0 to Lean Pool's v4.30.0-rc2. Test, example, and performance
binaries together with their `Std.Internal.Parsec`-based input parsers
(`CAVS`, `HexString`) are intentionally omitted: they are not part of
the verified library surface and rely on `partial def`s which are
forbidden in Lean Pool.
-/
