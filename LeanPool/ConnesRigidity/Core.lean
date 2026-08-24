/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 42-242.
Modifications: extracted the minimal group, representation, regular-factor,
and tracial-equivalence vocabulary; changed namespace and narrowed the
interface to arXiv:2608.02327. See the upstream PORT_MAP.md.
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Dynamics.Flow

/-!
The core component of the Connes rigidity formalization.
-/

namespace Connes

universe u v w

/-- Countable discrete group carrier. Paper: §7. -/
structure CountableDiscreteGroup where
  /--
  The `Carrier` component of `CountableDiscreteGroup`.
  -/
  Carrier : Type u
  group : Group Carrier
  countable : Countable Carrier

namespace CountableDiscreteGroup

/-- Coercion from the group wrapper to its carrier. Paper: §7. -/
instance : CoeSort CountableDiscreteGroup (Type u) :=
  ⟨CountableDiscreteGroup.Carrier⟩

attribute [instance] group countable

end CountableDiscreteGroup

/-- ICC predicate boundary. Paper: §5. -/
def IsICC (G : CountableDiscreteGroup) : Prop :=
  Infinite G ∧ ∀ g : G, g ≠ 1 → Set.Infinite (conjugatesOf g)

/-- Unitary-representation carrier. Paper: §4. -/
abbrev UnitaryRepresentation
    (G : Type u) [Group G]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  G →* unitary (H →L[ℂ] H)

namespace UnitaryRepresentation

variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Invariant-vector predicate. Paper: §4. -/
def IsInvariant (π : UnitaryRepresentation G H) (ξ : H) : Prop :=
  ∀ g : G, (π g : H →L[ℂ] H) ξ = ξ

/-- Almost-invariant-vector predicate. Paper: §4. -/
def HasAlmostInvariantUnitVectors (π : UnitaryRepresentation G H) : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ g ∈ K, ‖(π g : H →L[ℂ] H) ξ - ξ‖ < ε

end UnitaryRepresentation

/-- Property-(T), universe-polymorphic in the representation carrier so concrete
`Type 0` groups are not restricted to `Type 0` Hilbert spaces. Paper: §4. -/
def HasKazhdanPropertyT (G : CountableDiscreteGroup.{u}) : Prop :=
  ∀ (H : Type v)
    (_ : NormedAddCommGroup H)
    (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H)
    (π : UnitaryRepresentation G H),
    π.HasAlmostInvariantUnitVectors →
      ∃ ξ : H, ξ ≠ 0 ∧ π.IsInvariant ξ

/-- Relative property-(T), universe-polymorphic in the representation carrier so
concrete `Type 0` groups are not restricted to `Type 0` Hilbert spaces. Paper: §4. -/
def HasRelativePropertyT
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G) : Prop :=
  ∀ (H : Type v)
    (_ : NormedAddCommGroup H)
    (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H)
    (π : UnitaryRepresentation G H),
    π.HasAlmostInvariantUnitVectors →
      ∃ ξ : H, ξ ≠ 0 ∧
        ∀ n : N, (π (n : G) : H →L[ℂ] H) ξ = ξ

noncomputable section

open scoped NNReal ENNReal

/-- Group-indexed Hilbert carrier. Paper: §3. -/
abbrev GroupL2 (G : Type u) := lp (fun _ : G ↦ ℂ) 2

/-- Reindexing an `ℓp` family along an equivalence preserves membership in `ℓp`. -/
theorem memℓp_reindex {α : Type u} {β : Type v} {E : Type w}
    [NormedAddCommGroup E] {p : ℝ≥0∞} (e : α ≃ β) (hp : 0 < p.toReal)
    (f : lp (fun _ : α ↦ E) p) : Memℓp (fun j : β ↦ f (e.symm j)) p := by
  rw [memℓp_gen_iff hp]
  exact (e.symm.summable_iff).2 ((lp.memℓp f).summable hp)

/-- Reindexing equivalence for group-indexed Hilbert spaces. Paper: §3. -/
def l2Reindex {α : Type u} {β : Type v} (e : α ≃ β) :
    GroupL2 α ≃ₗᵢ[ℂ] GroupL2 β where
  toLinearEquiv :=
    { toFun := fun f ↦ ⟨(fun j : β ↦ f (e.symm j)), memℓp_reindex e (by norm_num) f⟩
      invFun := fun f ↦ ⟨(fun j : α ↦ f (e j)), memℓp_reindex e.symm (by norm_num) f⟩
      left_inv := fun f ↦ by ext; simp
      right_inv := fun f ↦ by ext; simp
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
  norm_map' := by
    intro f
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun i ↦ ‖f i‖ ^ (2 : ℝ≥0∞).toReal)

/-- Left-regular unitary boundary. Paper: §3. -/
def leftRegularUnitary {G : Type u} [Group G] (g : G) :
    unitary (GroupL2 G →L[ℂ] GroupL2 G) :=
  Unitary.linearIsometryEquiv.symm (l2Reindex (Equiv.mulLeft g))

/-- Left-regular representation boundary. Paper: §3. -/
def leftRegularRepresentation (G : Type u) [Group G] :
    G →* unitary (GroupL2 G →L[ℂ] GroupL2 G) where
  toFun := leftRegularUnitary
  map_one' := by
    -- Pin `λ(g)f(h) = f(g⁻¹ * h)` before discharging the representation law.
    ext f h
    change f ((1 : G)⁻¹ * h) = f h
    simp
  map_mul' g h := by
    -- Pin the same left-action convention for multiplication.
    ext f k
    change f ((g * h)⁻¹ * k) = f (h⁻¹ * (g⁻¹ * k))
    simp [mul_assoc]

/-- Bicommutant presentation of the von Neumann closure boundary. Paper: §3. -/
def vonNeumannClosure
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Set (H →L[ℂ] H)) :
    VonNeumannAlgebra H :=
  ({ toStarSubalgebra := StarSubalgebra.centralizer ℂ S
     centralizer_centralizer' :=
       Set.centralizer_centralizer_centralizer (S ∪ star S) } :
    VonNeumannAlgebra H).commutant

/-- The von Neumann closure has the expected bicommutant carrier. -/
@[simp]
theorem coe_vonNeumannClosure
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Set (H →L[ℂ] H)) :
    (vonNeumannClosure S : Set (H →L[ℂ] H)) =
      (StarSubalgebra.centralizer ℂ
        (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H)) :
          Set (H →L[ℂ] H)) := by
  rfl

/-- Membership in the von Neumann closure is membership in the star-algebraic
bicommutant of the generating set. -/
@[simp]
theorem mem_vonNeumannClosure
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : Set (H →L[ℂ] H)} {x : H →L[ℂ] H} :
    x ∈ vonNeumannClosure S ↔
      x ∈ StarSubalgebra.centralizer ℂ
        (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H)) := by
  rfl

/-- Group von Neumann algebra boundary. Paper: §3. -/
def groupVonNeumannAlgebra (G : CountableDiscreteGroup.{u}) :
    VonNeumannAlgebra (GroupL2 G) :=
  vonNeumannClosure (Set.range fun g : G ↦
    (leftRegularRepresentation G g : GroupL2 G →L[ℂ] GroupL2 G))

/-- Group von Neumann algebra carrier. Paper: §3. -/
abbrev GroupVonNeumannAlgebra (G : CountableDiscreteGroup.{u}) :=
  (groupVonNeumannAlgebra G).toStarSubalgebra

/-- Point-mass basis vector boundary. Paper: §3. -/
def delta (G : CountableDiscreteGroup.{u}) (g : G) : GroupL2 G :=
  by
    classical
    exact lp.single 2 g 1

/-- Canonical trace boundary. Paper: §3. -/
def canonicalTrace (G : CountableDiscreteGroup.{u}) :
    GroupVonNeumannAlgebra G → ℂ :=
  fun x ↦ inner ℂ (delta G 1) ((x : GroupL2 G →L[ℂ] GroupL2 G) (delta G 1))

/-- Projection-supremum predicate boundary. Leastness is among projection upper bounds,
not all ambient upper bounds as in `IsLUB`. Paper: §3. -/
def IsProjectionSupremum {A : Type u} [Mul A] [Star A] [LE A]
    (S : Set A) (p : A) : Prop :=
  IsStarProjection p ∧
    (∀ q ∈ S, IsStarProjection q ∧ q ≤ p) ∧
    ∀ r, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r

namespace IsProjectionSupremum

/-- Construct a projection supremum from its projection, upper-bound, and leastness clauses. -/
theorem intro
    {A : Type u} [Mul A] [Star A] [LE A] {S : Set A} {p : A}
    (hp : IsStarProjection p)
    (hupper : ∀ q ∈ S, IsStarProjection q ∧ q ≤ p)
    (hleast : ∀ r, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r) :
    IsProjectionSupremum S p :=
  ⟨hp, hupper, hleast⟩

/-- The supremum candidate is a projection. -/
theorem isStarProjection
    {A : Type u} [Mul A] [Star A] [LE A] {S : Set A} {p : A}
    (h : IsProjectionSupremum S p) : IsStarProjection p :=
  h.1

/-- Every member is a projection below the supremum candidate. -/
theorem upper
    {A : Type u} [Mul A] [Star A] [LE A] {S : Set A} {p q : A}
    (h : IsProjectionSupremum S p) (hq : q ∈ S) :
    IsStarProjection q ∧ q ≤ p :=
  h.2.1 q hq

/-- The supremum candidate lies below every projection upper bound. -/
theorem least
    {A : Type u} [Mul A] [Star A] [LE A] {S : Set A} {p r : A}
    (h : IsProjectionSupremum S p) (hr : IsStarProjection r)
    (hupper : ∀ q ∈ S, q ≤ r) : p ≤ r :=
  h.2.2 r hr hupper

/-- Projection suprema are unique. -/
theorem unique
    {A : Type u} [Mul A] [Star A] [LE A]
    [Std.Antisymm (fun a b : A ↦ a ≤ b)]
    {S : Set A} {p q : A}
    (hp : IsProjectionSupremum S p) (hq : IsProjectionSupremum S q) : p = q := by
  exact antisymm (r := fun a b : A ↦ a ≤ b)
    (hp.least hq.isStarProjection fun r hr ↦ (hq.upper hr).2)
    (hq.least hp.isStarProjection fun r hr ↦ (hp.upper hr).2)

end IsProjectionSupremum

/-- Preservation of projection suprema by a star-algebra equivalence and its inverse,
relative to the supplied order relations. Paper: §3. -/
def IsNormalStarAlgEquiv
    {A : Type u} {B : Type v}
    [Add A] [Mul A] [SMul ℂ A] [Star A] [LE A]
    [Add B] [Mul B] [SMul ℂ B] [Star B] [LE B]
    (e : A ≃⋆ₐ[ℂ] B) : Prop :=
  (∀ (S : Set A) (p : A),
    IsProjectionSupremum S p →
    IsProjectionSupremum (e '' S) (e p)) ∧
  ∀ (S : Set B) (p : B),
    IsProjectionSupremum S p →
    IsProjectionSupremum (e.symm '' S) (e.symm p)

namespace IsNormalStarAlgEquiv

variable {A : Type u} {B : Type v}
  [Add A] [Mul A] [SMul ℂ A] [Star A] [LE A]
  [Add B] [Mul B] [SMul ℂ B] [Star B] [LE B]

/-- Construct normality from projection-supremum transport in both directions. -/
theorem intro
    {e : A ≃⋆ₐ[ℂ] B}
    (hmap : ∀ (S : Set A) (p : A),
      IsProjectionSupremum S p → IsProjectionSupremum (e '' S) (e p))
    (hsymm_map : ∀ (S : Set B) (p : B),
      IsProjectionSupremum S p →
        IsProjectionSupremum (e.symm '' S) (e.symm p)) :
    IsNormalStarAlgEquiv e :=
  ⟨hmap, hsymm_map⟩

/-- A normal star-algebra equivalence preserves projection suprema. -/
theorem map
    {e : A ≃⋆ₐ[ℂ] B} (h : IsNormalStarAlgEquiv e)
    {S : Set A} {p : A} (hp : IsProjectionSupremum S p) :
    IsProjectionSupremum (e '' S) (e p) :=
  h.1 S p hp

/-- The inverse of a normal star-algebra equivalence preserves projection suprema. -/
theorem symm_map
    {e : A ≃⋆ₐ[ℂ] B} (h : IsNormalStarAlgEquiv e)
    {S : Set B} {p : B} (hp : IsProjectionSupremum S p) :
    IsProjectionSupremum (e.symm '' S) (e.symm p) :=
  h.2 S p hp

/-- The identity star-algebra equivalence is normal. -/
theorem refl : IsNormalStarAlgEquiv (StarAlgEquiv.refl ℂ A) := by
  refine intro ?_ ?_
  · intro S p hp
    rw [StarAlgEquiv.coe_refl, Set.image_id]
    exact hp
  · intro S p hp
    rw [StarAlgEquiv.refl_symm, StarAlgEquiv.coe_refl, Set.image_id]
    exact hp

/-- The inverse of a normal star-algebra equivalence is normal. -/
theorem symm {e : A ≃⋆ₐ[ℂ] B} (h : IsNormalStarAlgEquiv e) :
    IsNormalStarAlgEquiv e.symm := by
  refine intro (fun _ _ ↦ h.symm_map) ?_
  intro S p hp
  rw [StarAlgEquiv.symm_symm]
  exact h.map hp

/-- A composite of normal star-algebra equivalences is normal. -/
theorem trans
    {C : Type*}
    [Add C] [Mul C] [SMul ℂ C] [Star C] [LE C]
    {e : A ≃⋆ₐ[ℂ] B} {f : B ≃⋆ₐ[ℂ] C}
    (he : IsNormalStarAlgEquiv e) (hf : IsNormalStarAlgEquiv f) :
    IsNormalStarAlgEquiv (e.trans f) := by
  refine intro ?_ ?_
  · intro S p hp
    -- `StarAlgEquiv.trans` exposes the composite function after reducing its coercion.
    change IsProjectionSupremum ((fun x ↦ f (e x)) '' S) (f (e p))
    simpa only [Set.image_image] using hf.map (he.map hp)
  · intro S p hp
    -- The inverse composite similarly reduces to the reversed pointwise composite.
    change IsProjectionSupremum ((fun x ↦ e.symm (f.symm x)) '' S)
      (e.symm (f.symm p))
    simpa only [Set.image_image] using he.symm_map (hf.symm_map hp)

end IsNormalStarAlgEquiv

/-- Trace-preserving factor-equivalence witness. Paper: §3. -/
structure TracialGroupFactorEquiv
    (G : CountableDiscreteGroup.{u}) (H : CountableDiscreteGroup.{v}) where
  /--
  The `toStarAlgEquiv` component of `TracialGroupFactorEquiv`.
  -/
  toStarAlgEquiv :
    GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H
  normal : IsNormalStarAlgEquiv toStarAlgEquiv
  trace_preserving :
    ∀ x, canonicalTrace H (toStarAlgEquiv x) = canonicalTrace G x

/-- Trace-preserving factor-isomorphism predicate. Paper: §3. -/
def TracialGroupFactorsIsomorphic
    (G : CountableDiscreteGroup.{u}) (H : CountableDiscreteGroup.{v}) : Prop :=
  Nonempty (TracialGroupFactorEquiv G H)

end

end Connes
