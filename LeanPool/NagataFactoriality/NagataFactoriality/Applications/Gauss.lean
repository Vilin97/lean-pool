/-
Copyright (c) 2026 the authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
module

public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.UniqueFactorization


/-!
# Gauss

Supporting results for Nagata’s factoriality theorem.
-/

@[expose] public section

namespace NagataFactoriality

open Polynomial

theorem polynomial_content_mul {R : Type*} [CommRing R] [StrongNormalizedGCDMonoid R]
    (p q : R[X]) : (p * q).content = p.content * q.content :=
  Polynomial.content_mul

theorem primitive_mul {R : Type*} [CommRing R] [NormalizedGCDMonoid R]
    {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) : (p * q).IsPrimitive :=
  hp.mul hq

theorem polynomial_uniqueFactorizationMonoid {R : Type*} [CommRing R]
    [UniqueFactorizationMonoid R] : UniqueFactorizationMonoid R[X] := by
  infer_instance

end NagataFactoriality
