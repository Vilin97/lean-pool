/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorComm

/-!
# The monoidal product descends to the Hom spaces

With the tensor ideal two-sided (Lemma 3.3(b), both slots), the
bilinear tensor of free modules descends to a bilinear tensor of
Hom spaces — the monoidal product of the skein category.  On
fragment classes it is the tensor of fragments.
-/

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The tensor into the quotient, for a fixed left factor. -/
noncomputable def homTensorAux (s t u v : ℕ)
    (x : Fragment (Fin (s + t)) →₀ ℂ) :
    HomSpace f.val (u + v) →ₗ[ℂ]
      HomSpace f.val ((s + u) + (t + v)) :=
  Submodule.liftQ _
    ((LinearMap.ker (connectionMap f.val
        ((s + u) + (t + v)))).mkQ.comp
      (tensorFinsupp s t u v x))
    (fun y hy => by
      refine LinearMap.mem_ker.mpr ?_
      show (LinearMap.ker (connectionMap f.val
        ((s + u) + (t + v)))).mkQ
        (tensorFinsupp s t u v x y) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact tensorFinsupp_ker_right f.val f.iso_invariant x hy)

/-- The auxiliary tensor on a fragment class. -/
theorem homTensorAux_mk (s t u v : ℕ)
    (x : Fragment (Fin (s + t)) →₀ ℂ)
    (y : Fragment (Fin (u + v)) →₀ ℂ) :
    homTensorAux f s t u v x
        ((LinearMap.ker (connectionMap f.val (u + v))).mkQ y) =
      (LinearMap.ker (connectionMap f.val
        ((s + u) + (t + v)))).mkQ
        (tensorFinsupp s t u v x y) := rfl

/-- **The descended monoidal product** of the skein category. -/
noncomputable def HomSpace.tensor (s t u v : ℕ) :
    HomSpace f.val (s + t) →ₗ[ℂ]
      HomSpace f.val (u + v) →ₗ[ℂ]
        HomSpace f.val ((s + u) + (t + v)) :=
  Submodule.liftQ _
    { toFun := homTensorAux f s t u v
      map_add' := fun x₁ x₂ => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        show homTensorAux f s t u v (x₁ + x₂)
            ((LinearMap.ker (connectionMap f.val (u + v))).mkQ
              y) = _
        rw [homTensorAux_mk, map_add, LinearMap.add_apply,
          map_add]
        rfl
      map_smul' := fun c x => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        show homTensorAux f s t u v (c • x)
            ((LinearMap.ker (connectionMap f.val (u + v))).mkQ
              y) = _
        rw [homTensorAux_mk, map_smul, LinearMap.smul_apply,
          map_smul]
        rfl }
    (fun x hx => by
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun q => ?_
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      show homTensorAux f s t u v x
          ((LinearMap.ker (connectionMap f.val (u + v))).mkQ
            y) = 0
      rw [homTensorAux_mk]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (tensorFinsupp_ker_left f.val f.iso_invariant hx y))

/-- The descended tensor on quotient classes. -/
theorem HomSpace.tensor_mk (s t u v : ℕ)
    (x : Fragment (Fin (s + t)) →₀ ℂ)
    (y : Fragment (Fin (u + v)) →₀ ℂ) :
    HomSpace.tensor f s t u v
        ((LinearMap.ker (connectionMap f.val (s + t))).mkQ x)
        ((LinearMap.ker (connectionMap f.val (u + v))).mkQ y) =
      (LinearMap.ker (connectionMap f.val
        ((s + u) + (t + v)))).mkQ
        (tensorFinsupp s t u v x y) := rfl

/-- **Tensor of fragment classes is the class of the tensor.** -/
theorem HomSpace.tensor_ofFragment (s t u v : ℕ)
    (F : Fragment (Fin (s + t))) (G : Fragment (Fin (u + v))) :
    HomSpace.tensor f s t u v (HomSpace.ofFragment f.val F)
        (HomSpace.ofFragment f.val G) =
      HomSpace.ofFragment f.val (tensorFragment F G) := by
  show HomSpace.tensor f s t u v
      ((LinearMap.ker (connectionMap f.val (s + t))).mkQ
        (Finsupp.single F 1))
      ((LinearMap.ker (connectionMap f.val (u + v))).mkQ
        (Finsupp.single G 1)) = _
  rw [HomSpace.tensor_mk, tensorFinsupp_single, mul_one]
  rfl

end RS
