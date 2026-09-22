/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
/-!
# The full conductor as a minimal modulus

Let `L/K` be finite abelian.  Its conductor is the least modulus whose ray
class field contains `L`.  Since the public interface makes no global choice
of ray class fields, the theorem asserts existence of this least modulus.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

open scoped Classical in
/-- A finite abelian extension has a conductor characterized by containment
in ray class fields. -/
theorem embedsInRayClassField_iff_conductor_le
    (K : Type) [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] :
    ∃ c : RayClassModulus K, IsAbelianConductor K L c := by
  let H := GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
    (K := K) (L := L)
  let c : RayClassModulus K :=
    { finitePart := H.fullConductor.finitePart
      infinitePart := H.fullConductor.infinitePart }
  exact ⟨c, normFullConductor_isAbelianConductor K L⟩

end ClassFieldTheory
