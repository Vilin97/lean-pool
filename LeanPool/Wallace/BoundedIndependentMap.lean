/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.FiniteCombinatorics

/-!
# Transport of bounded independence through injective homomorphisms
-/

open scoped BigOperators

namespace Wallace
namespace FiniteCombinatorics

noncomputable section

universe u v

/-- Bounded independence is reflected by an injective additive homomorphism. -/
theorem boundedIndependent_of_image
    {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H] [DecidableEq H]
    (f : G →+ H) (hf : Function.Injective f)
    {M : ℕ} {X : Finset G}
    (himage : BoundedIndependent M (X.image f)) :
    BoundedIndependent M X := by
  classical
  intro c hc hsum x hx
  let d : H → ℤ := fun y ↦ c (Function.invFun f y)
  have hinv (z : G) : Function.invFun f (f z) = z :=
    Function.leftInverse_invFun hf z
  have hd (y : H) (hy : y ∈ X.image f) : Int.natAbs (d y) ≤ M := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    simpa [d, hinv] using hc z hz
  have hsumImage : ∑ y ∈ X.image f, d y • y = 0 := by
    rw [Finset.sum_image]
    · calc
        ∑ z ∈ X, d (f z) • f z = f (∑ z ∈ X, c z • z) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro z hz
          simp only [map_zsmul, d, hinv]
        _ = 0 := by rw [hsum, map_zero]
    · exact hf.injOn
  have hzero := himage d hd hsumImage (f x) (Finset.mem_image_of_mem f hx)
  simpa [d, hinv] using hzero

end

end FiniteCombinatorics
end Wallace
