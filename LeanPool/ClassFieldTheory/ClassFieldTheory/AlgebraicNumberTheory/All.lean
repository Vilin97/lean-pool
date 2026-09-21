/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.All
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.All
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.CompositumEmbedding
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.All
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.All
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceAdicCompletionCongrEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivTopology
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.All
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.All
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.QuadraticReciprocity
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.All
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.All
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SUnit.All
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.TensorProduct
/-!
# Algebraic number theory

Public root for the reusable global algebraic-number-theory layer used by
class field theory. It exports finite abelian composita, idèles and idèle
classes in extensions, normal-closure and splitting results, ray class groups,
S-units, and the ramification and degree results needed by global applications.
-/
