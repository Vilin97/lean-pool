/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/

module
public import LeanPool.KrohnRhodes.Foundations.MonoidWreathBridge
public import LeanPool.KrohnRhodes.Foundations.Division
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Tactic.Group

/-!
# The Krasner–Kaloujnine embedding

For a group `G` and a normal subgroup `N`, the Krasner–Kaloujnine homomorphism
`krasnerKaloujnineHom : G →* N ≀ᵣ (G ⧸ N)` into Mathlib's regular wreath product is
injective (`krasnerKaloujnine_injective`). Combined with the bridge of
`MonoidWreathBridge.lean`, `group_sgdiv_via_normal` shows that `G` divides
`WreathProduct N (G ⧸ N) (G ⧸ N)`; this is the step that splits a finite group along a
normal series.

## Implementation notes

The embedding needs a section `s : G ⧸ N → G` of the quotient map, obtained noncomputably
via `Function.surjInv`. The component `n_g(q) := s(q)⁻¹ * g * s(π(g)⁻¹ * q)` lies in `N`
because its image under `π` is `q⁻¹ * π(g) * π(g)⁻¹ * q = 1`.
-/

public section

namespace LeanPool.KrohnRhodes

universe u

variable {G : Type u} [Group G]

/-! ### Krasner-Kaloujnine universal embedding -/

section Krasner

variable (N : Subgroup G) [N.Normal]

/-- A noncomputable section `G ⧸ N → G` of the quotient map. -/
noncomputable def section_ : G ⧸ N → G :=
  Function.surjInv (QuotientGroup.mk'_surjective N)

/-- The section is a right inverse of the quotient map. -/
theorem section_apply (q : G ⧸ N) :
    QuotientGroup.mk' N (section_ N q) = q :=
  Function.surjInv_eq _ _

/-- The "left component" of the Krasner-Kaloujnine homomorphism, before showing
it lands in `N`. -/
@[expose]
noncomputable def krasnerLeftRaw (g : G) (q : G ⧸ N) : G :=
  (section_ N q)⁻¹ * g * section_ N ((QuotientGroup.mk' N g)⁻¹ * q)

/-- `krasnerLeftRaw g q` lies in `N` (kernel of the quotient map). -/
theorem krasnerLeftRaw_mem (g : G) (q : G ⧸ N) :
    krasnerLeftRaw N g q ∈ N := by
  -- N = ker(QuotientGroup.mk' N), so it suffices to show mk' applied to the element is 1.
  -- Compute: π(s(q)⁻¹ * g * s(π(g)⁻¹ * q)) = q⁻¹ * π(g) * (π(g)⁻¹ * q) = 1.
  have hone : QuotientGroup.mk' N (krasnerLeftRaw N g q) = 1 := by
    unfold krasnerLeftRaw
    rw [map_mul, map_mul, map_inv, section_apply, section_apply]
    group
  exact (QuotientGroup.eq_one_iff _).mp hone

/-- The "left component" of the Krasner-Kaloujnine homomorphism, valued in `N`. -/
@[expose]
noncomputable def krasnerLeft (g : G) (q : G ⧸ N) : N :=
  ⟨krasnerLeftRaw N g q, krasnerLeftRaw_mem N g q⟩

/-- The Krasner-Kaloujnine map `G → N ≀ᵣ (G ⧸ N)` (as bare data). -/
@[expose]
noncomputable def krasnerKaloujnineFun (g : G) : N ≀ᵣ (G ⧸ N) :=
  ⟨krasnerLeft N g, QuotientGroup.mk' N g⟩

/-- Multiplicativity of the Krasner-Kaloujnine map. -/
theorem krasnerKaloujnine_map_mul (g₁ g₂ : G) :
    krasnerKaloujnineFun N (g₁ * g₂) =
      krasnerKaloujnineFun N g₁ * krasnerKaloujnineFun N g₂ := by
  -- Right component:  π(g₁ g₂) = π(g₁) * π(g₂).
  -- Left component (pointwise at q):
  --   n_{g₁ g₂}(q) = s(q)⁻¹ * g₁ * g₂ * s(π(g₂)⁻¹ π(g₁)⁻¹ q)
  -- = s(q)⁻¹ * g₁ * s(π(g₁)⁻¹ q) * s(π(g₁)⁻¹ q)⁻¹ * g₂ * s(π(g₂)⁻¹ π(g₁)⁻¹ q)
  -- = n_{g₁}(q) * n_{g₂}(π(g₁)⁻¹ q)
  -- Mathlib's regular wreath multiplication: (a * b).left = a.left * (λx, b.left (a.right⁻¹ * x))
  refine RegularWreathProduct.ext ?_ ?_
  · -- left component
    funext q
    apply Subtype.ext
    change krasnerLeftRaw N (g₁ * g₂) q
        = krasnerLeftRaw N g₁ q * krasnerLeftRaw N g₂ ((QuotientGroup.mk' N g₁)⁻¹ * q)
    -- Manual rewriting to avoid timeouts.
    change (section_ N q)⁻¹ * (g₁ * g₂) *
        section_ N ((QuotientGroup.mk' N (g₁ * g₂))⁻¹ * q) =
      ((section_ N q)⁻¹ * g₁ * section_ N ((QuotientGroup.mk' N g₁)⁻¹ * q)) *
      ((section_ N ((QuotientGroup.mk' N g₁)⁻¹ * q))⁻¹ * g₂ *
        section_ N ((QuotientGroup.mk' N g₂)⁻¹ * ((QuotientGroup.mk' N g₁)⁻¹ * q)))
    have hquot :
        (QuotientGroup.mk' N (g₁ * g₂))⁻¹ * q =
        (QuotientGroup.mk' N g₂)⁻¹ * ((QuotientGroup.mk' N g₁)⁻¹ * q) := by
      rw [map_mul, mul_inv_rev]
      group
    rw [hquot]
    -- Now both sides have the same `section_` arguments.
    set a : G := section_ N q
    set b : G := section_ N ((QuotientGroup.mk' N g₁)⁻¹ * q)
    set c : G := section_ N ((QuotientGroup.mk' N g₂)⁻¹ * ((QuotientGroup.mk' N g₁)⁻¹ * q))
    change a⁻¹ * (g₁ * g₂) * c = (a⁻¹ * g₁ * b) * (b⁻¹ * g₂ * c)
    group
  · -- right component
    change QuotientGroup.mk' N (g₁ * g₂) = QuotientGroup.mk' N g₁ * QuotientGroup.mk' N g₂
    exact map_mul (QuotientGroup.mk' N) g₁ g₂

/-- Triviality at 1 of the Krasner-Kaloujnine map. -/
theorem krasnerKaloujnine_map_one :
    krasnerKaloujnineFun N 1 = 1 := by
  refine RegularWreathProduct.ext ?_ ?_
  · funext q
    apply Subtype.ext
    change (section_ N q)⁻¹ * 1 * section_ N ((QuotientGroup.mk' N 1)⁻¹ * q) = 1
    rw [map_one, inv_one, one_mul, mul_one]
    rw [inv_mul_cancel]
  · change QuotientGroup.mk' N 1 = 1
    exact map_one _

/-- The Krasner-Kaloujnine universal embedding `G →* N ≀ᵣ (G ⧸ N)`. -/
@[expose]
noncomputable def krasnerKaloujnineHom :
    G →* (N ≀ᵣ (G ⧸ N)) where
  toFun := krasnerKaloujnineFun N
  map_one' := krasnerKaloujnine_map_one N
  map_mul' := krasnerKaloujnine_map_mul N

@[simp] theorem krasnerKaloujnineHom_left (g : G) (q : G ⧸ N) :
    ((krasnerKaloujnineHom N g).left q : G) =
      (section_ N q)⁻¹ * g * section_ N ((QuotientGroup.mk' N g)⁻¹ * q) := rfl

/-- Injectivity of the Krasner-Kaloujnine embedding. -/
theorem krasnerKaloujnine_injective :
    Function.Injective (krasnerKaloujnineHom N) := by
  intro g₁ g₂ h
  -- From φ(g₁) = φ(g₂), read off π(g₁) = π(g₂) and the left components agree.
  have hright : QuotientGroup.mk' N g₁ = QuotientGroup.mk' N g₂ := by
    have := congrArg RegularWreathProduct.right h
    simpa [krasnerKaloujnineHom, krasnerKaloujnineFun] using this
  have hleft : ∀ q : G ⧸ N,
      (krasnerKaloujnineHom N g₁).left q = (krasnerKaloujnineHom N g₂).left q := by
    intro q
    have := congrArg RegularWreathProduct.left h
    exact congrFun this q
  -- Take q = 1.
  have h1 : (krasnerKaloujnineHom N g₁).left 1 = (krasnerKaloujnineHom N g₂).left 1 := hleft 1
  have hval : ((krasnerKaloujnineHom N g₁).left 1 : G) =
      ((krasnerKaloujnineHom N g₂).left 1 : G) := congrArg Subtype.val h1
  rw [krasnerKaloujnineHom_left, krasnerKaloujnineHom_left] at hval
  -- The (s(1))⁻¹ on the left and section_ N (mk'⁻¹ * 1) on the right cancel since π(g₁) = π(g₂).
  rw [hright] at hval
  -- s(1)⁻¹ * g₁ * s((mk' g₂)⁻¹) = s(1)⁻¹ * g₂ * s((mk' g₂)⁻¹)
  exact mul_left_cancel (mul_right_cancel hval)

end Krasner

/-! ### From the embedding to `SgDiv` -/

/-- For a group `G` with a normal subgroup `N`, `G` divides
`WreathProduct N (G/N) (G/N)` as a semigroup. -/
theorem group_sgdiv_via_normal {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal] :
    SgDiv G (WreathProduct N (G ⧸ N) (G ⧸ N)) := by
  exact sgDiv_of_injective_monoidHom
    ((regularWreathToMonoidWreath N (G ⧸ N)).comp (krasnerKaloujnineHom N))
    ((regularWreathToMonoidWreath_injective N (G ⧸ N)).comp
      (krasnerKaloujnine_injective N))

end LeanPool.KrohnRhodes
