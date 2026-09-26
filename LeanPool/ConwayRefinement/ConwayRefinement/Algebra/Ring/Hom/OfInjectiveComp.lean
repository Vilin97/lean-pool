/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Ring homomorphisms detected through an injective homomorphism

A map `s : A → B` whose composite with an injective ring homomorphism `g : B →+* C` is a ring
homomorphism `A →+* C` is itself a ring homomorphism: each axiom for `s` is the corresponding
axiom for `g ∘ s`, read back through the injectivity of `g`.

This is how a homomorphism into a subring of a subring is built without elaborating the
homomorphism axioms inside the nested coercions: the axioms are checked after composing out to
an ambient ring where they are already known.
-/

public section

namespace RingHom

variable {A B C : Type*} [NonAssocSemiring A] [NonAssocSemiring B] [NonAssocSemiring C]

/-- The ring homomorphism `s : A → B` detected by an injective ring homomorphism `g : B →+* C`
through which it factors a ring homomorphism `f : A →+* C`, so that `g (s a) = f a`. -/
def ofInjectiveComp (g : B →+* C) (hg : Function.Injective g) (f : A →+* C) (s : A → B)
    (hs : ∀ a, g (s a) = f a) : A →+* B where
  toFun := s
  map_one' := hg <| by rw [hs, map_one, map_one]
  map_mul' x y := hg <| by rw [hs, map_mul, map_mul, hs, hs]
  map_zero' := hg <| by rw [hs, map_zero, map_zero]
  map_add' x y := hg <| by rw [hs, map_add, map_add, hs, hs]

/-- The detected homomorphism is the given map. -/
@[simp]
theorem ofInjectiveComp_apply (g : B →+* C) (hg : Function.Injective g) (f : A →+* C)
    (s : A → B) (hs : ∀ a, g (s a) = f a) (a : A) : ofInjectiveComp g hg f s hs a = s a :=
  (rfl)

/-- Composing the detected homomorphism with the detecting one recovers the factored
homomorphism. -/
theorem comp_ofInjectiveComp (g : B →+* C) (hg : Function.Injective g) (f : A →+* C)
    (s : A → B) (hs : ∀ a, g (s a) = f a) : g.comp (ofInjectiveComp g hg f s hs) = f :=
  RingHom.ext hs

end RingHom

end
