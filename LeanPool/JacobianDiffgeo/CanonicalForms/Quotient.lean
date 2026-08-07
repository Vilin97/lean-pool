/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CanonicalForms.OrdRes

/-!
# `MForm X`: meromorphic 1-forms as germ classes of chart-coefficient families (D1/D2/D4–D6)

Unit: canonical-forms (`docs/design/canonical-forms.md`, representational revision). This file is
the CC3-pattern fix for the raw-representation flaw documented in the previous unit root: raw
`MFormData` equality is too fine (meromorphic coefficients carry junk at poles, so
"`ord = ⊤` everywhere" does NOT force raw equality with `0`). Exactly as `ℳ X` quotients raw
meromorphic functions by codiscrete agreement (`Jacobian/Meromorphic/GermSpace.lean`), we set

* `MFormData.Eqv θ η := ∀ x, θ.coeffAt x =ᶠ[𝓝[≠] (chartAt ℂ x x)] η.coeffAt x` — germ agreement
  at every preferred-chart center. (By `compat`-transport this is equivalent to codiscrete
  agreement on every chart target; the center-germ form is chosen because every reading map of
  the unit — `ord`, `resAt`, `laurentCoeffAt`, `divisor` — is a germ-at-the-center functional,
  so descent is a one-line congruence.)
* `MForm X := Quotient` of `MFormData X` by `Eqv`, with `AddCommGroup`/`Module ℂ` descended
  pointwise from the raw instances.
* `MForm.ord`/`resAt`/`laurentCoeffAt`/`divisor`/`degree`: the D4/D6 exports, lifted.
* **D5, the global zero-dichotomy** `MForm.eq_zero_or_forall_ord_ne_top`: on the quotient this is
  the clopen argument of `Jacobian/Meromorphic/CodiscreteBridge.lean` run on `{x | ord = ⊤}`
  (open by `eventually_ord_eq_top`, closed because its complement is open by
  `eventually_ord_eq_zero`), and the `S = univ ⇒ θ = 0` step — FALSE for raw families — is now
  the literal definition of the quotient relation via `ord_eq_top_iff`. Corollary:
  `MForm.ord_ne_top`.
-/

open scoped ContDiff Manifold
open Set IsManifold Filter Topology

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MFormData

/-- Codiscrete/germ agreement of raw chart-coefficient families: the preferred-chart coefficients
agree on a punctured neighborhood of every chart center (CC3 pattern; see the module docstring
for why this is the right granularity). -/
def Eqv (θ η : MFormData X) : Prop :=
  ∀ x : X, θ.coeffAt x =ᶠ[𝓝[≠] (chartAt ℂ x x)] η.coeffAt x

theorem eqv_refl (θ : MFormData X) : Eqv θ θ := fun _ => Filter.EventuallyEq.rfl

theorem eqv_symm {θ η : MFormData X} (h : Eqv θ η) : Eqv η θ := fun x => (h x).symm

theorem eqv_trans {θ η ζ : MFormData X} (h₁ : Eqv θ η) (h₂ : Eqv η ζ) : Eqv θ ζ :=
  fun x => (h₁ x).trans (h₂ x)

instance instSetoid : Setoid (MFormData X) :=
  ⟨Eqv, ⟨eqv_refl, eqv_symm, eqv_trans⟩⟩

end MFormData

variable (X) in
/-- D1 (revised): a meromorphic 1-form on `X` — the quotient of raw chart-coefficient families
(`MFormData X`) by codiscrete/germ agreement, the same CC3 quotient pattern as `ℳ X`. -/
def MForm : Type _ := Quotient (MFormData.instSetoid (X := X))

namespace MForm

/-- The class of a raw chart-coefficient family. -/
def mk (θ : MFormData X) : MForm X := Quotient.mk MFormData.instSetoid θ

theorem exists_rep (Θ : MForm X) : ∃ θ : MFormData X, mk θ = Θ := Quotient.exists_rep Θ

@[elab_as_elim]
theorem ind {motive : MForm X → Prop} (h : ∀ θ : MFormData X, motive (mk θ)) (Θ : MForm X) :
    motive Θ := Quotient.ind h Θ

theorem sound {θ η : MFormData X} (h : MFormData.Eqv θ η) : mk θ = mk η := Quotient.sound h

theorem mk_eq_mk {θ η : MFormData X} : mk θ = mk η ↔ MFormData.Eqv θ η :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-! ### `ℂ`-algebra structure, descended pointwise -/

instance : Zero (MForm X) := ⟨mk 0⟩

instance : Add (MForm X) :=
  ⟨Quotient.map₂ (· + ·) fun θ θ' hθ η η' hη x => by
    filter_upwards [hθ x, hη x] with z h₁ h₂
    change θ.coeffAt x z + η.coeffAt x z = θ'.coeffAt x z + η'.coeffAt x z
    rw [h₁, h₂]⟩

instance : Neg (MForm X) :=
  ⟨Quotient.map (- ·) fun θ θ' hθ x => by
    filter_upwards [hθ x] with z h₁
    change -θ.coeffAt x z = -θ'.coeffAt x z
    rw [h₁]⟩

instance : Sub (MForm X) :=
  ⟨Quotient.map₂ (· - ·) fun θ θ' hθ η η' hη x => by
    filter_upwards [hθ x, hη x] with z h₁ h₂
    change θ.coeffAt x z - η.coeffAt x z = θ'.coeffAt x z - η'.coeffAt x z
    rw [h₁, h₂]⟩

instance : SMul ℂ (MForm X) :=
  ⟨fun c => Quotient.map (c • ·) fun θ θ' hθ x => by
    filter_upwards [hθ x] with z h₁
    change c * θ.coeffAt x z = c * θ'.coeffAt x z
    rw [h₁]⟩

@[simp] theorem mk_zero : (mk (0 : MFormData X)) = (0 : MForm X) := rfl

@[simp] theorem mk_add (θ η : MFormData X) : mk θ + mk η = mk (θ + η) := rfl

@[simp] theorem mk_neg (θ : MFormData X) : -mk θ = mk (-θ) := rfl

@[simp] theorem mk_sub (θ η : MFormData X) : mk θ - mk η = mk (θ - η) := rfl

@[simp] theorem mk_smul (c : ℂ) (θ : MFormData X) : c • mk θ = mk (c • θ) := rfl

instance : AddCommGroup (MForm X) where
  add_assoc a b c := Quotient.inductionOn₃ a b c fun θ η ζ => congrArg mk (add_assoc θ η ζ)
  zero_add a := ind (fun θ => congrArg mk (zero_add θ)) a
  add_zero a := ind (fun θ => congrArg mk (add_zero θ)) a
  add_comm a b := Quotient.inductionOn₂ a b fun θ η => congrArg mk (add_comm θ η)
  neg_add_cancel a := ind (fun θ => congrArg mk (neg_add_cancel θ)) a
  sub_eq_add_neg a b := Quotient.inductionOn₂ a b fun θ η => congrArg mk (sub_eq_add_neg θ η)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℂ (MForm X) where
  smul_zero c := congrArg mk (smul_zero c)
  smul_add c a b := Quotient.inductionOn₂ a b fun θ η => congrArg mk (smul_add c θ η)
  add_smul c d a := ind (fun θ => congrArg mk (add_smul c d θ)) a
  zero_smul a := ind (fun θ => congrArg mk (zero_smul ℂ θ)) a
  one_smul a := ind (fun θ => congrArg mk (one_smul ℂ θ)) a
  mul_smul c d a := ind (fun θ => congrArg mk (mul_smul c d θ)) a

/-- D3 on classes: assemble a meromorphic 1-form from compatible covering-chart-family data
(`MFormCoeffData`, mirrors `Form1CoeffData`); the class of the raw assembly. -/
noncomputable def ofCoeffs {ι : Type*} (D : MFormCoeffData X ι) : MForm X :=
  mk (MFormData.ofCoeffs D)

/-! ### `ord`, `resAt`, `laurentCoeffAt` (D4), lifted -/

/-- D4: the order of a meromorphic 1-form at `x` (read via the preferred chart at `x`; descends
because `meromorphicOrderAt` is a germ functional). -/
noncomputable def ord (Θ : MForm X) (x : X) : WithTop ℤ :=
  Quotient.liftOn Θ (fun θ => θ.ord x) fun _ _ h => meromorphicOrderAt_congr (h x)

@[simp] theorem ord_mk (θ : MFormData X) (x : X) : (mk θ).ord x = θ.ord x := rfl

/-- D4: the residue of a meromorphic 1-form at `x`. -/
noncomputable def resAt (Θ : MForm X) (x : X) : ℂ :=
  Quotient.liftOn Θ (fun θ => θ.resAt x) fun _ _ h => resAt_congr (h x)

@[simp] theorem resAt_mk (θ : MFormData X) (x : X) : (mk θ).resAt x = θ.resAt x := rfl

/-- The `k`-th Laurent coefficient of a meromorphic 1-form at `x`, read in the preferred chart
(consumed by `MLFormData.Realizes`, D13). -/
noncomputable def laurentCoeffAt (Θ : MForm X) (x : X) (k : ℤ) : ℂ :=
  Quotient.liftOn Θ (fun θ => RS.laurentCoeffAt (θ.coeffAt x) (chartAt ℂ x x) k)
    fun _ _ h => laurentCoeffAt_congr (h x) k

@[simp] theorem laurentCoeffAt_mk (θ : MFormData X) (x : X) (k : ℤ) :
    (mk θ).laurentCoeffAt x k = RS.laurentCoeffAt (θ.coeffAt x) (chartAt ℂ x x) k := rfl

theorem resAt_eq_laurentCoeffAt (Θ : MForm X) (x : X) :
    Θ.resAt x = Θ.laurentCoeffAt x (-1) := by
  obtain ⟨θ, rfl⟩ := exists_rep Θ
  rfl

@[simp] theorem ord_zero (x : X) : (0 : MForm X).ord x = ⊤ := by
  change meromorphicOrderAt (0 : ℂ → ℂ) (chartAt ℂ x x) = ⊤
  simp

/-! ### Order propagation and the divisor (D6), lifted -/

theorem eventually_ord_eq_top [T1Space X] {Θ : MForm X} {x : X} (h : Θ.ord x = ⊤) :
    ∀ᶠ y in 𝓝 x, Θ.ord y = ⊤ := by
  obtain ⟨θ, rfl⟩ := exists_rep Θ
  exact MFormData.eventually_ord_eq_top h

theorem eventually_ord_eq_zero {Θ : MForm X} {x : X} (h : Θ.ord x ≠ ⊤) :
    ∀ᶠ y in 𝓝[≠] x, Θ.ord y = 0 := by
  obtain ⟨θ, rfl⟩ := exists_rep Θ
  exact MFormData.eventually_ord_eq_zero h

/-- D6: the divisor of a meromorphic 1-form (lifted from `MFormData.divisor`; well-defined since
`ord` is). -/
noncomputable def divisor [T1Space X] (Θ : MForm X) : Divisor X :=
  Quotient.liftOn Θ MFormData.divisor fun θ η h =>
    Function.locallyFinsuppWithin.ext fun y => by
      change (θ.ord y).untop₀ = (η.ord y).untop₀
      have hord : θ.ord y = η.ord y := meromorphicOrderAt_congr (h y)
      rw [hord]

@[simp] theorem divisor_mk [T1Space X] (θ : MFormData X) :
    (mk θ).divisor = θ.divisor := rfl

@[simp] theorem divisor_apply [T1Space X] (Θ : MForm X) (x : X) :
    Θ.divisor x = (Θ.ord x).untop₀ := by
  obtain ⟨θ, rfl⟩ := exists_rep Θ
  rfl

/-- D6: the degree of the divisor. -/
noncomputable def degree [T1Space X] [T2Space X] [CompactSpace X] (Θ : MForm X) : ℤ :=
  Θ.divisor.degree

@[simp] theorem divisor_zero [T1Space X] :
    (0 : MForm X).divisor = 0 := MFormData.divisor_zero

/-! ### D5: the global zero-dichotomy

The step that is FALSE for raw families — "`ord = ⊤` everywhere forces the form to be zero" — is
the literal definition of the quotient relation. The clopen skeleton is
`MeromorphicOnX.eventuallyEq_zero_or_forall_ordAtX_ne_top`'s
(`Jacobian/Meromorphic/CodiscreteBridge.lean`); closedness of `{ord = ⊤}` is here even easier:
its complement is open directly by `eventually_ord_eq_zero`. -/

/-- **D5**: on a connected surface, a meromorphic 1-form is zero, or its order is finite
everywhere. -/
theorem eq_zero_or_forall_ord_ne_top [T1Space X] [ConnectedSpace X] (Θ : MForm X) :
    Θ = 0 ∨ ∀ x, Θ.ord x ≠ ⊤ := by
  set S : Set X := {x | Θ.ord x = ⊤} with hS_def
  have hSopen : IsOpen S := isOpen_iff_mem_nhds.2 fun x hx => eventually_ord_eq_top hx
  have hScompl : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have h₁ : ∀ᶠ y in 𝓝[≠] x, Θ.ord y = 0 := eventually_ord_eq_zero hx
    rw [eventually_nhdsWithin_iff] at h₁
    filter_upwards [h₁] with y hy
    rcases eq_or_ne y x with rfl | hyx
    · exact hx
    · change Θ.ord y ≠ ⊤
      rw [hy (by simpa using hyx)]
      simp
  rcases isClopen_iff.1 ⟨isOpen_compl_iff.1 hScompl, hSopen⟩ with hSempty | hSuniv
  · exact Or.inr fun x hx => Set.eq_empty_iff_forall_notMem.1 hSempty x hx
  · left
    obtain ⟨θ, rfl⟩ := exists_rep Θ
    refine sound fun x => ?_
    have hx : θ.ord x = ⊤ := Set.eq_univ_iff_forall.1 hSuniv x
    exact MFormData.ord_eq_top_iff.1 hx

/-- A nonzero meromorphic 1-form has finite order everywhere (D5 corollary; the input D8/D10/D11
consume). -/
theorem ord_ne_top [T1Space X] [ConnectedSpace X] {Θ : MForm X} (h : Θ ≠ 0) (x : X) :
    Θ.ord x ≠ ⊤ :=
  ((eq_zero_or_forall_ord_ne_top Θ).resolve_left h) x

/-- The zero class is characterized by `ord = ⊤` everywhere (junk-free, unlike the raw layer). -/
theorem eq_zero_iff_forall_ord_eq_top [T1Space X] [ConnectedSpace X] {Θ : MForm X} :
    Θ = 0 ↔ ∀ x, Θ.ord x = ⊤ := by
  constructor
  · rintro rfl x
    exact ord_zero x
  · intro h
    by_contra hne
    exact ord_ne_top hne (Classical.arbitrary X) (h _)

end MForm

end RS
