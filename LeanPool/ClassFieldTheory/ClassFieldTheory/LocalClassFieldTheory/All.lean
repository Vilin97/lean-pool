/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.All
/-!
# Local class field theory

This is the canonical root of the complete local class field theory library.
It reaches every supported implementation layer. Clients that need a smaller
dependency closure should import the semantic owner aggregate for the result
they use:

- `LocalClassFieldTheory.Finite.LocalReciprocity` for finite reciprocity;
- `LocalClassFieldTheory.Finite.Existence` for finite existence;
- `LocalClassFieldTheory.Infinite` for absolute and profinite reciprocity;
- `LocalClassFieldTheory.Kummer` for the local Kummer pairing;
- `LocalClassFieldTheory.LubinTateApplication` for Lubin--Tate applications.

The principal declarations live in the `LocalClassFieldTheory` namespace.
The abstract class-formation layer uses the `ClassFormation` namespace.

## Headline API

The finite reciprocity isomorphism and continuous Artin map:
- `LocalClassFieldTheory.localReciprocityEquiv`
- `LocalClassFieldTheory.localArtinMap`
- `LocalClassFieldTheory.localArtinMap_surjective`
- `LocalClassFieldTheory.localArtinMap_ker`

Finite local existence:
- `LocalClassFieldTheory.finiteAbelianNormSubgroupOrderIso`

Absolute and profinite reciprocity:
- `LocalClassFieldTheory.absoluteLocalArtinMap`
- `LocalClassFieldTheory.profiniteLocalReciprocity`
-/

