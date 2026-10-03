/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/

module
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Data.Fintype.EquivFin

/-!
# Monoid division and local divisors

* `MonoidDivides M N` — `M` is a quotient of a submonoid of `N`;
  `MonoidDivides.trans` shows division is transitive.
* `LocalDivisor M c` — the local divisor `M_c` of `M` at `c`: the set
  `cM ∩ Mc` with the product `x ∘ y = x · y₀` for `y = c · y₀` and identity `c`, with its
  `Monoid` and `Finite` instances; `LocalDivisor.localDivides` shows `M_c` divides `M`.

## References

* [V. Diekert, M. Kufleitner, B. Steinberg, *The Krohn–Rhodes Theorem and Local Divisors*,
  Fundamenta Informaticae 116 (2012); arXiv:1111.1585]
-/

public section

namespace LeanPool.KrohnRhodes

universe u

variable {α : Type u}

/-! ### Monoid division -/

/-- A monoid `M` divides a monoid `N` if `M` is a quotient of a submonoid of `N`.
Equivalently, there exists a surjective monoid homomorphism from a submonoid of `N` onto `M`. -/
@[expose]
def MonoidDivides (M : Type*) (N : Type*) [Monoid M] [Monoid N] : Prop :=
  ∃ (S : Submonoid N) (φ : S →* M), Function.Surjective φ

/-- **Monoid division is transitive.** If `M ≼ N` (witnessed by `S ≤ N`, `φ : S ↠ M`) and
`N ≼ P` (witnessed by `T ≤ P`, `ψ : T ↠ N`), then `M ≼ P`. The witnessing submonoid of `P` is
the image under `T ↪ P` of the pre-image `ψ⁻¹(S) ≤ T`; the surjection is `φ ∘ (ψ restricted) ∘
(the submonoid iso)`. This is the standard composition of "quotient of a submonoid"
relations. -/
theorem MonoidDivides.trans {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (h1 : MonoidDivides M N) (h2 : MonoidDivides N P) : MonoidDivides M P := by
  obtain ⟨S, φ, hφ⟩ := h1
  obtain ⟨T, ψ, hψ⟩ := h2
  -- `U := ψ⁻¹(S) ≤ T`; `ψ'` corestricts `ψ|U` to `S`.
  let U : Submonoid T := S.comap ψ
  let ψ' : U →* S := (ψ.comp U.subtype).codRestrict S (fun x => x.2)
  have hψ'_surj : Function.Surjective ψ' := by
    intro s
    obtain ⟨t, ht⟩ := hψ s
    refine ⟨⟨t, ?_⟩, Subtype.ext ht⟩
    change ψ t ∈ S
    rw [ht]
    exact s.2
  -- Transport `U` to a submonoid `V ≤ P` via the injective inclusion `T ↪ P`.
  let V : Submonoid P := U.map T.subtype
  let eUV : U ≃* V := Submonoid.equivMapOfInjective U T.subtype Subtype.val_injective
  exact ⟨V, (φ.comp ψ').comp eUV.symm.toMonoidHom,
    (hφ.comp hψ'_surj).comp eUV.symm.surjective⟩

/-! #### The local divisor `M_c = cM ∩ Mc`

For `c ∈ M`, the local divisor (Diekert–Kufleitner–Steinberg) is

> `M_c := cM ∩ Mc`, with the *twisted product* `x ∘ y := x · y₀` (any `y₀` with `y = c·y₀`),
> identity `c`.

The twisted product is well-defined because for `x ∈ Mc` and `y = c·y₀` the value `x·y₀` does
not depend on the choice of `y₀`. `M_c` divides `M` (`localDivides`). This is the larger
local divisor described in DKS Section 2.5; their decomposition uses the potentially smaller
submonoid `cMc ∪ {c}`. -/

/-- The carrier of the **local divisor** of a monoid `M` at `c`: the two-sided set
`cM ∩ Mc = {x | (∃ a, x = c*a) ∧ (∃ b, x = b*c)}`. As a subtype of `M`. -/
@[expose]
def LocalDivisor (M : Type*) [Monoid M] (c : M) : Type _ :=
  {x : M // (∃ a : M, x = c * a) ∧ (∃ b : M, x = b * c)}

namespace LocalDivisor

variable {M : Type*} [Monoid M] {c : M}

/-- The underlying element of `M` of a local-divisor element. -/
@[expose]
def val (x : LocalDivisor M c) : M := x.1

@[ext] theorem ext {x y : LocalDivisor M c} (h : x.val = y.val) : x = y := Subtype.ext h

theorem mem_left (x : LocalDivisor M c) : ∃ a : M, x.val = c * a := x.2.1
theorem mem_right (x : LocalDivisor M c) : ∃ b : M, x.val = b * c := x.2.2

/-- The **twisted product** `x ∘ y = x · y₀` where `y = c · y₀` (the value is independent of the
choice of `y₀`, by `x ∈ Mc`). Implemented via `Classical.choose` of the left-membership of `y`. -/
noncomputable instance : Mul (LocalDivisor M c) where
  mul x y :=
    ⟨x.val * (Classical.choose y.mem_left),
      by
        obtain ⟨a, ha⟩ := x.mem_left
        exact ⟨a * Classical.choose y.mem_left, by rw [ha, mul_assoc]⟩,
      by
        -- x.val * y₀ = (x.val) * y₀, and x.val ∈ Mc gives x.val = b*c, but we need *·c form.
        -- Use that x.val * y₀ = b * c * y₀ = b * (c * y₀) = b * y.val, and y.val ∈ Mc.
        obtain ⟨b, hb⟩ := x.mem_right
        obtain ⟨b', hb'⟩ := y.mem_right
        have hy0 : c * Classical.choose y.mem_left = y.val :=
          (Classical.choose_spec y.mem_left).symm
        refine ⟨b * b', ?_⟩
        rw [hb, mul_assoc, hy0, hb', ← mul_assoc]⟩

theorem mul_val (x y : LocalDivisor M c) :
    (x * y).val = x.val * Classical.choose y.mem_left := rfl

/-- The defining identity for the product: if `y.val = c * y₀` for *any* `y₀`, then
`(x * y).val = x.val * y₀`. (Independence of the chosen witness, using `x.val ∈ Mc`.) -/
theorem mul_val_of_eq (x y : LocalDivisor M c) {y₀ : M} (hy₀ : y.val = c * y₀) :
    (x * y).val = x.val * y₀ := by
  rw [mul_val]
  obtain ⟨b, hb⟩ := x.mem_right
  have hc : c * Classical.choose y.mem_left = c * y₀ := by
    rw [(Classical.choose_spec y.mem_left).symm, hy₀]
  calc x.val * Classical.choose y.mem_left
      = b * (c * Classical.choose y.mem_left) := by rw [hb, mul_assoc]
    _ = b * (c * y₀) := by rw [hc]
    _ = x.val * y₀ := by rw [hb, mul_assoc]

/-- The identity element of the local divisor is `c` itself (`c = c*1 = 1*c ∈ cM ∩ Mc`). -/
noncomputable instance : One (LocalDivisor M c) where
  one := ⟨c, ⟨1, (mul_one c).symm⟩, ⟨1, (one_mul c).symm⟩⟩

theorem one_val : (1 : LocalDivisor M c).val = c := rfl

noncomputable instance : Monoid (LocalDivisor M c) where
  mul_assoc x y z := by
    apply LocalDivisor.ext
    -- (x*y)*z and x*(y*z) both equal x.val * y₀ * z₀ where y=c y₀, z=c z₀.
    obtain ⟨z₀, hz₀⟩ := z.mem_left
    obtain ⟨y₀, hy₀⟩ := y.mem_left
    have hyz : (y * z).val = y.val * z₀ := mul_val_of_eq y z hz₀
    have hyz' : (y * z).val = c * (y₀ * z₀) := by rw [hyz, hy₀, mul_assoc]
    -- LHS: ((x*y)*z).val = (x*y).val * z₀ = (x.val*y₀)*z₀
    have hL : (x * y * z).val = x.val * y₀ * z₀ := by
      rw [mul_val_of_eq (x * y) z hz₀, mul_val_of_eq x y hy₀]
    -- RHS: (x*(y*z)).val = x.val*(y₀*z₀)
    have hR : (x * (y * z)).val = x.val * (y₀ * z₀) := mul_val_of_eq x (y * z) hyz'
    rw [hL, hR, mul_assoc]
  one_mul x := by
    apply LocalDivisor.ext
    obtain ⟨a, ha⟩ := x.mem_left
    rw [mul_val_of_eq 1 x ha, one_val, ← ha]
  mul_one x := by
    apply LocalDivisor.ext
    -- 1.val = c = c*1, so (x*1).val = x.val * 1 = x.val.
    rw [mul_val_of_eq x 1 (by rw [one_val, mul_one] : (1 : LocalDivisor M c).val = c * 1),
      mul_one]

/-- The local divisor is finite when `M` is (it is a subtype of `M`). -/
noncomputable instance [Finite M] : Finite (LocalDivisor M c) := Subtype.finite

/-- **The local divisor `M_c` divides `M`.** The witnessing submonoid is
`S = {t : M | c·t ∈ Mc}` (so that `c·t ∈ cM ∩ Mc`), and the surjection is `γ(t) = c·t`.
This is a monoid homomorphism for the twisted product, and every `x ∈ cM ∩ Mc` is `γ(a)` for the
witness `a` of `x ∈ cM`. -/
theorem localDivides : MonoidDivides (LocalDivisor M c) M := by
  -- The submonoid S = {t | c*t ∈ Mc} = {t | ∃ b, c*t = b*c}.
  let S : Submonoid M :=
    { carrier := {t : M | ∃ b : M, c * t = b * c}
      one_mem' := ⟨1, by rw [mul_one, one_mul]⟩
      mul_mem' := by
        rintro t t' ⟨b, hb⟩ ⟨b', hb'⟩
        -- c*(t*t') = (c*t)*t' = (b*c)*t' = b*(c*t') = b*(b'*c) = (b*b')*c
        refine ⟨b * b', ?_⟩
        rw [← mul_assoc, hb, mul_assoc, hb', ← mul_assoc, mul_assoc] }
  -- The map t ↦ c*t lands in LocalDivisor M c.
  have hmem : ∀ t : S, (∃ a : M, c * t.1 = c * a) ∧ (∃ b : M, c * t.1 = b * c) :=
    fun t => ⟨⟨t.1, rfl⟩, t.2⟩
  let γ : S → LocalDivisor M c := fun t => ⟨c * t.1, hmem t⟩
  have hγval : ∀ t : S, (γ t).val = c * t.1 := fun _ => rfl
  refine ⟨S, ?_, ?_⟩
  · refine { toFun := γ, map_one' := ?_, map_mul' := ?_ }
    · apply LocalDivisor.ext
      rw [hγval, one_val]; exact mul_one c
    · intro t t'
      apply LocalDivisor.ext
      -- γ(t*t').val = c*(t.1*t'.1); (γt * γt').val = (γt).val * t'.1 (since (γt').val = c*t'.1)
      have h1 : (γ (t * t')).val = c * (t.1 * t'.1) := hγval (t * t')
      have h2 : (γ t * γ t').val = c * t.1 * t'.1 := by
        rw [mul_val_of_eq (γ t) (γ t') (hγval t'), hγval t]
      rw [h1, h2, mul_assoc]
  · -- surjectivity: x ∈ cM∩Mc, x = c*a (witness of mem_left); a ∈ S and γ(a)=x.
    intro x
    obtain ⟨a, ha⟩ := x.mem_left
    obtain ⟨b, hb⟩ := x.mem_right
    refine ⟨⟨a, ⟨b, by rw [← ha, hb]⟩⟩, ?_⟩
    apply LocalDivisor.ext
    change c * a = x.val
    exact ha.symm

end LocalDivisor

end LeanPool.KrohnRhodes
