/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.CompositumEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceAdicCompletionCongrEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivTopology
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.QuadraticReciprocity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SUnit.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.TensorProduct
/-!
# Algebraic number theory

Public root for the reusable global algebraic-number-theory layer used by
class field theory. It exports finite abelian composita, idèles and idèle
classes in extensions, normal-closure and splitting results, ray class groups,
S-units, and the ramification and degree results needed by global applications.
-/

@[expose] public section
