/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/

module
public import LeanPool.KrohnRhodes.Foundations.WreathProduct
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.PUnit

/-!
# Semigroup division: transitivity and embeddings

* `sgDiv_trans` — semigroup division is transitive;
* `sgDiv_of_injective_monoidHom` — an injective monoid homomorphism `A →* T` shows that
  `A` divides `T`;
* `instMulActionPUnit` — the trivial monoid acting on the one-point type;
* `sgDiv_of_injective_hom` — if `S` divides `T` and `T` embeds into `W` by an injective
  semigroup homomorphism, then `S` divides `W`.
-/

public section

namespace LeanPool.KrohnRhodes

universe u

variable {M : Type u} [Monoid M] [Finite M] [DecidableEq M]

/-! ### Transitivity and embeddings -/

/-- `SgDiv` is transitive. -/
theorem sgDiv_trans {S T U : Type u} [Mul S] [Mul T] [Mul U]
    (hST : SgDiv S T) (hTU : SgDiv T U) : SgDiv S U := by
  obtain ⟨V, φ, hφ⟩ := hST
  obtain ⟨W, ψ, hψ⟩ := hTU
  -- Pull `V ⊆ T` back along `ψ : W → T` to a subsemigroup of `U`.
  let W' : Subsemigroup U :=
    { carrier := {u | ∃ h : u ∈ W, ψ ⟨u, h⟩ ∈ V}
      mul_mem' := by
        rintro a b ⟨ha, hav⟩ ⟨hb, hbv⟩
        refine ⟨W.mul_mem ha hb, ?_⟩
        have : ψ ⟨a * b, W.mul_mem ha hb⟩ = ψ ⟨a, ha⟩ * ψ ⟨b, hb⟩ :=
          ψ.map_mul ⟨a, ha⟩ ⟨b, hb⟩
        rw [this]
        exact V.mul_mem hav hbv }
  refine ⟨W', ⟨fun u => φ ⟨ψ ⟨u.1, u.2.1⟩, u.2.2⟩, ?_⟩, ?_⟩
  · -- multiplicativity
    rintro ⟨a, ha, hav⟩ ⟨b, hb, hbv⟩
    have hψm : ψ ⟨a * b, W.mul_mem ha hb⟩ = ψ ⟨a, ha⟩ * ψ ⟨b, hb⟩ :=
      ψ.map_mul ⟨a, ha⟩ ⟨b, hb⟩
    change φ ⟨ψ ⟨a * b, W.mul_mem ha hb⟩, _⟩
      = φ ⟨ψ ⟨a, ha⟩, hav⟩ * φ ⟨ψ ⟨b, hb⟩, hbv⟩
    have : φ ⟨ψ ⟨a * b, W.mul_mem ha hb⟩, by rw [hψm]; exact V.mul_mem hav hbv⟩
        = φ (⟨ψ ⟨a, ha⟩, hav⟩ * ⟨ψ ⟨b, hb⟩, hbv⟩) := by
      congr 1
      apply Subtype.ext
      exact hψm
    rw [this, φ.map_mul]
  · -- surjectivity
    intro s
    obtain ⟨v, hv⟩ := hφ s
    obtain ⟨w, hw⟩ := hψ (v : T)
    have hw' : ψ ⟨(w : U), w.2⟩ = (v : T) := hw
    have hmem : ψ ⟨(w : U), w.2⟩ ∈ V := by rw [hw']; exact v.2
    refine ⟨⟨(w : U), w.2, hmem⟩, ?_⟩
    change φ ⟨ψ ⟨(w : U), w.2⟩, hmem⟩ = s
    have : φ ⟨ψ ⟨(w : U), w.2⟩, hmem⟩ = φ v := by
      congr 1
      exact Subtype.ext hw'
    rw [this, hv]

/-- An *injective* monoid homomorphism `f : A →* T` exhibits `A` as a
division of `T`: the subsemigroup `MonoidHom.mrange f` together with the
inverse (via `Function.invFun`) is a surjective `→ₙ*` onto `A`. -/
theorem sgDiv_of_injective_monoidHom {A T : Type u} [Monoid A] [Monoid T]
    (f : A →* T) (hf : Function.Injective f) : SgDiv A T := by
  refine ⟨(MonoidHom.mrange f).toSubsemigroup, ?_, ?_⟩
  · refine ⟨fun u => Function.invFun f u.1, ?_⟩
    intro a b
    obtain ⟨ma, ha⟩ := a.2
    obtain ⟨mb, hb⟩ := b.2
    show Function.invFun f _ = Function.invFun f _ * Function.invFun f _
    have hab : ((a * b : (MonoidHom.mrange f).toSubsemigroup) : T)
        = f (ma * mb) := by
      change (a : T) * (b : T) = f (ma * mb)
      rw [map_mul, ha, hb]
    rw [hab, Function.leftInverse_invFun hf (ma * mb),
        ← ha, Function.leftInverse_invFun hf ma,
        ← hb, Function.leftInverse_invFun hf mb]
  · intro m
    refine ⟨⟨f m, ⟨m, rfl⟩⟩, ?_⟩
    change Function.invFun f (f m) = m
    exact Function.leftInverse_invFun hf m

/-! ## Semigroup division along injective homomorphisms -/

/-- A trivial one-element monoid acts on a trivial one-element type. -/
instance instMulActionPUnit : MulAction PUnit.{u+1} PUnit.{u+1} :=
  Monoid.toMulAction (M := PUnit.{u+1})

/-- If `S` divides `T` and there is an injective semigroup homomorphism
`ι : T →ₙ* W`, then `S` divides `W`. -/
theorem sgDiv_of_injective_hom {S T W : Type u} [Mul S] [Mul T] [Mul W]
    (h : SgDiv S T) (ι : T →ₙ* W) (hι : Function.Injective ι) :
    SgDiv S W := by
  obtain ⟨U, φ, hφ⟩ := h
  -- `ι.subsemigroupMap U : U →ₙ* U.map ι` is bijective.
  have hbij : Function.Bijective (ι.subsemigroupMap U) := by
    refine ⟨?_, MulHom.subsemigroupMap_surjective ι U⟩
    intro a b hab
    apply Subtype.ext
    apply hι
    exact congrArg Subtype.val hab
  -- Hence `U ≃* U.map ι`.
  let e : U ≃* U.map ι := MulEquiv.ofBijective (ι.subsemigroupMap U) hbij
  -- Compose `φ` with the inverse iso to get a surjective hom `U.map ι →ₙ* S`.
  refine ⟨U.map ι, φ.comp e.symm.toMulHom, ?_⟩
  intro s
  obtain ⟨u, hu⟩ := hφ s
  refine ⟨e u, ?_⟩
  change φ (e.symm (e u)) = s
  rw [e.symm_apply_apply, hu]

end LeanPool.KrohnRhodes
