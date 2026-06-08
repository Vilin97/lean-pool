/-
Copyright (c) 2026 Gerald Doussot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gerald Doussot
-/

import LeanPool.Cryptography.Hashes.SHA3.Basic
import LeanPool.Cryptography.Data.HexString

/-!
# Cryptography Experiments in Lean 4: SHA-3 Implementation

Source: url:https://github.com/gdncc/cryptography
Authors: Gerald Doussot
Status: verified
Main declarations: `Cryptography.SHA3.sha256`, `Cryptography.HashFunction.hashData`
Tags: cryptography, sha-3, keccak, hash-functions
MSC: 94A60, 68P25
-/

/-!
## Mathematical overview

This project is a pure Lean 4 implementation of the SHA-3 family of cryptographic
functions: the four hash functions SHA3-224, SHA3-256, SHA3-384, and SHA3-512,
and the two extendable-output functions (XOFs) SHAKE128 and SHAKE256, all built
on the Keccak-p sponge permutation. It exposes one-shot (`HashFunction.hashData`)
and streaming (`HashFunction.update`/`HashFunction.final`, `XOF.absorb`/`XOF.squeeze`)
APIs operating on `ByteArray`.

A distinguishing feature is that every internal array access is formally proven to
be within bounds, using dependent types (`Fin`-indexed rates and capacities, size
subtypes for the state and buffer) and accompanying lemmas such as
`StateIndexWithinBounds55`. The implementation matches the NIST test vectors.

It is an educational resource and must not be used for real cryptographic
applications.
-/
