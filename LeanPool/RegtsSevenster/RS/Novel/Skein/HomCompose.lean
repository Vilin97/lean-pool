/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinIdealLeft

/-!
# Composition descends to the Hom spaces

With the pairing kernel a two-sided ideal (Lemma 3.3(a), both
halves), the bilinear composition of free modules descends to a
bilinear composition of Hom spaces — the composition of the skein
category.  On fragment classes it is composition of fragments.
-/

@[expose] public section

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The composition into the quotient, for a fixed left factor. -/
noncomputable def homComposeAux (s t u : ℕ)
    (x : Fragment (Fin (s + t)) →₀ ℂ) :
    HomSpace f.val (t + u) →ₗ[ℂ] HomSpace f.val (s + u) :=
  Submodule.liftQ _
    ((LinearMap.ker (connectionMap f.val (s + u))).mkQ.comp
      (composeFinsupp s t u x))
    (fun y hy => by
      refine LinearMap.mem_ker.mpr ?_
      change (LinearMap.ker (connectionMap f.val (s + u))).mkQ
        (composeFinsupp s t u x y) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact composeFinsupp_ker_right f.val f.iso_invariant x hy)

/-- The auxiliary composition on a fragment class. -/
theorem homComposeAux_mk (s t u : ℕ)
    (x : Fragment (Fin (s + t)) →₀ ℂ)
    (y : Fragment (Fin (t + u)) →₀ ℂ) :
    homComposeAux f s t u x
        ((LinearMap.ker (connectionMap f.val (t + u))).mkQ y) =
      (LinearMap.ker (connectionMap f.val (s + u))).mkQ
        (composeFinsupp s t u x y) := rfl

/-- **The descended composition** of the skein category: the
bilinear composition of Hom spaces. -/
noncomputable def HomSpace.comp (s t u : ℕ) :
    HomSpace f.val (s + t) →ₗ[ℂ]
      HomSpace f.val (t + u) →ₗ[ℂ] HomSpace f.val (s + u) :=
  Submodule.liftQ _
    { toFun := homComposeAux f s t u
      map_add' := fun x₁ x₂ => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        change homComposeAux f s t u (x₁ + x₂)
            ((LinearMap.ker (connectionMap f.val (t + u))).mkQ
              y) = _
        rw [homComposeAux_mk, map_add, LinearMap.add_apply,
          map_add]
        rfl
      map_smul' := fun c x => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        change homComposeAux f s t u (c • x)
            ((LinearMap.ker (connectionMap f.val (t + u))).mkQ
              y) = _
        rw [homComposeAux_mk, map_smul, LinearMap.smul_apply,
          map_smul]
        rfl }
    (fun x hx => by
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun q => ?_
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      change homComposeAux f s t u x
          ((LinearMap.ker (connectionMap f.val (t + u))).mkQ
            y) = 0
      rw [homComposeAux_mk]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (composeFinsupp_ker_left f.val f.iso_invariant hx y))

/-- The descended composition on quotient classes. -/
theorem HomSpace.comp_mk (s t u : ℕ)
    (x : Fragment (Fin (s + t)) →₀ ℂ)
    (y : Fragment (Fin (t + u)) →₀ ℂ) :
    HomSpace.comp f s t u
        ((LinearMap.ker (connectionMap f.val (s + t))).mkQ x)
        ((LinearMap.ker (connectionMap f.val (t + u))).mkQ y) =
      (LinearMap.ker (connectionMap f.val (s + u))).mkQ
        (composeFinsupp s t u x y) := rfl

/-- **Composition of fragment classes is the class of the
composition.** -/
theorem HomSpace.comp_ofFragment (s t u : ℕ)
    (F : Fragment (Fin (s + t))) (G : Fragment (Fin (t + u))) :
    HomSpace.comp f s t u (HomSpace.ofFragment f.val F)
        (HomSpace.ofFragment f.val G) =
      HomSpace.ofFragment f.val (F.compose G) := by
  change HomSpace.comp f s t u
      ((LinearMap.ker (connectionMap f.val (s + t))).mkQ
        (Finsupp.single F 1))
      ((LinearMap.ker (connectionMap f.val (t + u))).mkQ
        (Finsupp.single G 1)) = _
  rw [HomSpace.comp_mk, composeFinsupp_single, mul_one]
  rfl

end RS
