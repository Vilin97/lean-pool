/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
import LeanPool.CompositionAlgebras.Composition.Doubling
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dual.Lemmas


/-!
# Hurwitz's theorem: the dimension of a Euclidean composition algebra is 1, 2, 4 or 8

`finrank_eq_one_or_two_or_four_or_eight` : a finite-dimensional Euclidean composition algebra
has real dimension `1`, `2`, `4` or `8`. `Composition/Instances.lean` exhibits `ℝ`, `ℂ`, `ℍ`,
`𝕆` at each of the four, so all four occur.

## The argument, and where the bound actually comes from

Start with `A₀ = ℝ ∙ 1` and double: while the current composition subalgebra `A` is proper,
`exists_unit_orthogonal` produces a unit `u ⊥ A` and `Composition/Doubling.lean`'s three rules
make `A ⊕ A u` a composition subalgebra of twice the dimension. So `finrank C` is a power of
two, and the whole content of the theorem is that the fourth doubling is impossible.

★ The build plan said the doubling stops "because `CD D` composes only when `D` is
associative", and flagged that it had not written this out to the level where a Lean gap would
show. Written out, the mechanism is **not** the one the phrase suggests, and the difference
matters:

* Closure of `A ⊕ A u` is unconditional — `Doubling.lean` proves the three rules with no
  associativity hypothesis. So the doubling never fails to *close*.
* What fails is the *norm*. Inside `C` the norm form is multiplicative by hypothesis, so
  expanding `N(xy) = N x N y` on `x = a + bu`, `y = c + du` yields, after both adjoint
  identities, `⟪b, (da)c⟫ = ⟪b, d(ac)⟫` for all `b ∈ A` — and `A` is nondegenerate, so **`A`
  is associative**. That is `forced_assoc`, and it is a *hypothesis* on `A` extracted from the
  mere existence of `u`, not a property of a separately constructed `CD A`.

★ Finite-dimensionality enters twice, and both times as *counting*: in
`exists_unit_orthogonal`, to produce the normal at all, and in `finrank_double` and the chain of
the main theorem, for the dimension bookkeeping. It does **not** enter the algebra: the three
structural lemmas `forced_assoc`, `comm_of_assoc_double` and `le_span_one_of_comm_double` are
proved without it, as the `omit [FiniteDimensional ℝ C]` lines above them record.
★ An earlier draft of this paragraph said finite-dimensionality was used "in exactly one place".
That was false — `finrank_double` uses `Submodule.finrank_sup_add_finrank_inf_eq` and
`Submodule.equivMapOfInjective`, and its own `omit` line omits only `[Nontrivial C]`.

So the bound is a contrapositive: a composition subalgebra that is not associative has no unit
vector orthogonal to it, hence is everything. Two more steps localise the failure:
`comm_of_assoc_double` (if `A ⊕ A u` is associative then `A` is commutative) and
`le_span_one_of_comm_double` (if `A ⊕ A u` is commutative then `A ⊆ ℝ ∙ 1`). At the fourth
doubling these chain to `finrank A₁ ≤ 1`, contradicting `finrank A₁ = 2`.

## What is *not* proved here

The **classification** — that a Euclidean composition algebra is *isomorphic to* `ℝ`, `ℂ`, `ℍ`
or `𝕆` — is not proved *here*. Only the dimension is. Building the four isomorphisms needs the
chain to be identified with the concrete carriers step by step, which is a separate
construction: `Composition/Classification.lean`, `hurwitz_classification`. ★ That file re-runs
the chain below with an embedding carried alongside it; it does not derive the maps from the
dimension theorem, which it uses only once, to know the third double is everything.

## Scope

This file carries `finrank_eq_one_or_two_or_four_or_eight`, Hurwitz's theorem in
dimension form.
-/

namespace CompositionAlgebra

universe u

variable {C : Type u} [NonAssocRing C] [Module ℝ C]
  [IsScalarTower ℝ C C] [SMulCommClass ℝ C C] [CompositionAlgebra C] [Nontrivial C]

/-! ### Right multiplication by a unit vector -/

omit [CompositionAlgebra C] [Nontrivial C] in
/-- Right multiplication, as an `ℝ`-linear map. -/
def mulRightL (u : C) : C →ₗ[ℝ] C where
  toFun x := x * u
  map_add' x y := add_mul x y u
  map_smul' r x := smul_mul_assoc r x u

omit [SMulCommClass ℝ C C] [CompositionAlgebra C] [Nontrivial C] in
@[simp] theorem mulRightL_apply (u x : C) : mulRightL u x = x * u := rfl

omit [Nontrivial C] in
/-- Right multiplication by a unit vector is injective: it is a linear isometry of the norm
form. -/
theorem mulRight_injective {u : C} (hnu : nf u = 1) :
    Function.Injective (mulRightL u : C →ₗ[ℝ] C) := by
  intro x y hxy
  simp only [mulRightL_apply] at hxy
  have hz : (x - y) * u = 0 := by rw [sub_mul, hxy, sub_self]
  have h2 := comp (x - y) u
  rw [hz, hnu, mul_one] at h2
  have : nf (x - y) = 0 := by
    rw [← h2]; exact nf_eq_zero_iff.mpr rfl
  have := nf_eq_zero_iff.mp this
  linear_combination (norm := module) this

/-! ### A proper subspace has a unit normal -/

variable [FiniteDimensional ℝ C]

/-- The form, restricted to a subspace in its second slot. Its kernel is the orthogonal
complement of that subspace. -/
private def toDualOn (A : Submodule ℝ C) : C →ₗ[ℝ] (A →ₗ[ℝ] ℝ) where
  toFun x := (B x).comp A.subtype
  map_add' x y := by ext a; simp
  map_smul' r x := by ext a; simp

omit [Nontrivial C] in
/-- **Every proper subspace of a Euclidean composition algebra has a unit normal.** This is the
only place finite-dimensionality is used, and it is where the doubling gets its input. -/
theorem exists_unit_orthogonal {A : Submodule ℝ C} (hA : A ≠ ⊤) :
    ∃ u : C, (∀ a ∈ A, ip u a = 0) ∧ nf u = 1 := by
  have hrk : Module.finrank ℝ (LinearMap.ker (toDualOn A)) ≠ 0 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (toDualOn A)
    have h2 : Module.finrank ℝ (LinearMap.range (toDualOn A)) ≤ Module.finrank ℝ (A →ₗ[ℝ] ℝ) :=
      Submodule.finrank_le _
    have h3 : Module.finrank ℝ (A →ₗ[ℝ] ℝ) = Module.finrank ℝ A := by
      rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
    have h4 : Module.finrank ℝ A < Module.finrank ℝ C := Submodule.finrank_lt hA
    omega
  have hne : LinearMap.ker (toDualOn A) ≠ ⊥ := by
    intro h; rw [h] at hrk; simp at hrk
  obtain ⟨v, hvmem, hv0⟩ := Submodule.ne_bot_iff _ |>.mp hne
  have hvperp : ∀ a ∈ A, ip v a = 0 := by
    intro a ha
    have : toDualOn A v = 0 := hvmem
    have := congrArg (fun f => f ⟨a, ha⟩) this
    simpa [toDualOn, ip] using this
  have hpos : 0 < nf v := nf_pos hv0
  refine ⟨(Real.sqrt (nf v))⁻¹ • v, fun a ha => by simp [hvperp a ha], ?_⟩
  rw [nf_smul, inv_pow, Real.sq_sqrt (le_of_lt hpos)]
  field_simp

/-! ### The doubled subalgebra -/

/-- The Cayley–Dickson double of `A` inside `C`, along the unit vector `u`. -/
def double (A : Submodule ℝ C) (u : C) : Submodule ℝ C := A ⊔ A.map (mulRightL u)

omit [SMulCommClass ℝ C C] [CompositionAlgebra C] [Nontrivial C] [FiniteDimensional ℝ C] in
theorem mem_double_iff {A : Submodule ℝ C} {u x : C} :
    x ∈ double A u ↔ ∃ a ∈ A, ∃ b ∈ A, x = a + b * u := by
  simp only [double, Submodule.mem_sup, Submodule.mem_map, mulRightL_apply]
  constructor
  · rintro ⟨y, hy, z, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨y, hy, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b * u, ⟨b, hb, rfl⟩, rfl⟩

omit [SMulCommClass ℝ C C] [CompositionAlgebra C] [Nontrivial C] [FiniteDimensional ℝ C] in
theorem le_double (A : Submodule ℝ C) (u : C) : A ≤ double A u := le_sup_left

omit [SMulCommClass ℝ C C] [CompositionAlgebra C] [Nontrivial C] [FiniteDimensional ℝ C] in
theorem mem_double_of_mem {A : Submodule ℝ C} {u x : C} (hx : x ∈ A) : x ∈ double A u :=
  le_double A u hx

namespace IsCompSubalgebra

variable {A : Submodule ℝ C} (hA : IsCompSubalgebra A) {u : C}
  (hu : ∀ a ∈ A, ip u a = 0) (hnu : nf u = 1)

include hA

omit [Nontrivial C] [FiniteDimensional ℝ C] in
theorem unit_mem_double : u ∈ double A u := by
  rw [mem_double_iff]
  exact ⟨0, A.zero_mem, 1, hA.one_mem, by rw [one_mul, zero_add]⟩

include hu hnu

omit [FiniteDimensional ℝ C] in
/-- The doubled subalgebra is again a composition subalgebra. This is exactly the three
Cayley–Dickson rules of `Composition/Doubling.lean`, assembled. -/
theorem isCompSubalgebra_double : IsCompSubalgebra (double A u) where
  one_mem := mem_double_of_mem hA.one_mem
  mul_mem := by
    rintro x hx y hy
    rw [mem_double_iff] at hx hy ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨c, hc, d, hd, rfl⟩ := hy
    refine ⟨a * c - cstar d * b, A.sub_mem (hA.mul_mem ha hc) (hA.mul_mem (hA.cstar_mem hd) hb),
      d * a + b * cstar c, A.add_mem (hA.mul_mem hd ha) (hA.mul_mem hb (hA.cstar_mem hc)), ?_⟩
    rw [mul_add, add_mul, add_mul, hA.mul_mul_unit hu ha hd, hA.unit_mul_mul hu b hc,
      hA.unit_mul_unit hu hnu hb hd, add_mul]
    abel
  cstar_mem := by
    rintro x hx
    rw [mem_double_iff] at hx ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨cstar a, hA.cstar_mem ha, -b, A.neg_mem hb, ?_⟩
    rw [cstar_add, cstar_of_pure (hA.isPure_mul_unit hu hb), neg_mul]

omit [Nontrivial C] [FiniteDimensional ℝ C] in
/-- The norm of an element of the doubled algebra splits: `N(p + q u) = N p + N q`. -/
theorem nf_add_mul_unit {p : C} (hp : p ∈ A) {q : C} (hq : q ∈ A) :
    nf (p + q * u) = nf p + nf q := by
  rw [nf_add, ip_symm p (q * u), hA.ip_mul_unit hu hq hp, comp, hnu, mul_one]
  ring

omit [FiniteDimensional ℝ C] in
/-- **Forced associativity.** If some unit vector is orthogonal to the composition subalgebra
`A`, then `A` is associative.

This is where Hurwitz's dimension bound actually comes from. The hypothesis is the *existence*
of `u`, and the conclusion is a property of `A` alone: the norm form of `C`, restricted to
`A ⊕ A u`, is multiplicative for free, and multiplicativity there is equivalent to
associativity of `A`. -/
theorem forced_assoc : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, (x * y) * z = x * (y * z) := by
  have key : ∀ a ∈ A, ∀ c ∈ A, ∀ d ∈ A, ∀ b ∈ A,
      ip (d * a) (b * cstar c) = ip (a * c) (cstar d * b) := by
    intro a ha c hc d hd b hb
    have hP : a * c - cstar d * b ∈ A :=
      A.sub_mem (hA.mul_mem ha hc) (hA.mul_mem (hA.cstar_mem hd) hb)
    have hQ : d * a + b * cstar c ∈ A :=
      A.add_mem (hA.mul_mem hd ha) (hA.mul_mem hb (hA.cstar_mem hc))
    have hprod : (a + b * u) * (c + d * u)
        = (a * c - cstar d * b) + (d * a + b * cstar c) * u := by
      rw [mul_add, add_mul, add_mul, hA.mul_mul_unit hu ha hd, hA.unit_mul_mul hu b hc,
        hA.unit_mul_unit hu hnu hb hd, add_mul]
      abel
    have hmul := comp (a + b * u) (c + d * u)
    rw [hprod, hA.nf_add_mul_unit hu hnu hP hQ, hA.nf_add_mul_unit hu hnu ha hb,
      hA.nf_add_mul_unit hu hnu hc hd] at hmul
    simp only [nf_sub, nf_add, comp, nf_cstar] at hmul
    linear_combination hmul / 2
  intro x hx y hy z hz
  set v : C := (x * y) * z - x * (y * z) with hv
  have hvA : v ∈ A :=
    A.sub_mem (hA.mul_mem (hA.mul_mem hx hy) hz) (hA.mul_mem hx (hA.mul_mem hy hz))
  have hzero : ∀ b ∈ A, ip b v = 0 := by
    intro b hb
    have hk := key y hy z hz x hx b hb
    have hLb : ip (x * y) (b * cstar z) = ip b ((x * y) * z) := by
      rw [ip_symm, ip_mul_adj_right, cstar_cstar]
    have hRb : ip (y * z) (cstar x * b) = ip b (x * (y * z)) := by
      rw [ip_symm, ip_mul_adj_left, cstar_cstar]
    rw [hLb, hRb] at hk
    rw [hv, ip_sub_right, hk, sub_self]
  have hnv : nf v = 0 := by
    have h := hzero v hvA
    rwa [nf_eq_ip]
  have hv0 := nf_eq_zero_iff.mp hnv
  rw [hv] at hv0
  linear_combination (norm := module) hv0

/-! ### Dimension of the double -/

omit [Nontrivial C] in
/-- The doubling exactly doubles the dimension. -/
theorem finrank_double : Module.finrank ℝ (double A u) = 2 * Module.finrank ℝ A := by
  have hinj := mulRight_injective hnu
  have hmapdim : Module.finrank ℝ (A.map (mulRightL u)) = Module.finrank ℝ A :=
    ((Submodule.equivMapOfInjective (mulRightL u) hinj A).finrank_eq).symm
  have hinf : A ⊓ A.map (mulRightL u) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨hxA, b, hb, hbx⟩ := hx
    have h0 : ip (b * u) x = 0 := hA.ip_mul_unit hu hb hxA
    rw [mulRightL_apply] at hbx
    rw [hbx] at h0
    have hnx : nf x = 0 := h0
    simpa using nf_eq_zero_iff.mp hnx
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A (A.map (mulRightL u))
  rw [hinf, hmapdim] at hsum
  simp only [finrank_bot] at hsum
  change Module.finrank ℝ (A ⊔ A.map (mulRightL u) : Submodule ℝ C) =
    2 * Module.finrank ℝ A
  omega

/-! ### Where the chain stops -/

omit [FiniteDimensional ℝ C] in
/-- If the doubled algebra is associative, `A` is commutative. -/
theorem comm_of_assoc_double
    (h : ∀ x ∈ double A u, ∀ y ∈ double A u, ∀ z ∈ double A u, (x * y) * z = x * (y * z)) :
    ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  have step : ∀ a ∈ A, ∀ b ∈ A, a * cstar b = cstar b * a := by
    intro a hb' b hb
    have hass := h a (mem_double_of_mem hb') u (hA.unit_mem_double) b (mem_double_of_mem hb)
    have hub : u * b = cstar b * u := by
      have hc := hA.unit_comm hu (hA.cstar_mem hb)
      rw [cstar_cstar] at hc
      exact hc.symm
    rw [hA.unit_mul_mul hu a hb, hub, hA.mul_mul_unit hu hb' (hA.cstar_mem hb)] at hass
    exact mulRight_injective hnu hass
  intro x hx y hy
  have hs := step x hx (cstar y) (hA.cstar_mem hy)
  rwa [cstar_cstar] at hs

omit [FiniteDimensional ℝ C] in
/-- If the doubled algebra is commutative, `A` is the line through the unit. -/
theorem le_span_one_of_comm_double
    (h : ∀ x ∈ double A u, ∀ y ∈ double A u, x * y = y * x) :
    A ≤ Submodule.span ℝ {(1 : C)} := by
  intro a ha
  have hcomm := h a (mem_double_of_mem ha) u (hA.unit_mem_double)
  have hub : u * a = cstar a * u := by
    have hc := hA.unit_comm hu (hA.cstar_mem ha)
    rw [cstar_cstar] at hc
    exact hc.symm
  rw [hub] at hcomm
  have hae : a = cstar a := mulRight_injective hnu hcomm
  have hline : a = (ip a 1) • (1 : C) := by
    rw [cstar_apply] at hae
    linear_combination (norm := module) (2⁻¹ : ℝ) • hae
  rw [hline]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end IsCompSubalgebra

/-! ### The base of the chain -/

omit [FiniteDimensional ℝ C] in
/-- The line through the unit is a composition subalgebra. -/
theorem isCompSubalgebra_spanOne : IsCompSubalgebra (Submodule.span ℝ {(1 : C)}) where
  one_mem := Submodule.mem_span_singleton_self _
  mul_mem := by
    rintro a ha b hb
    rw [Submodule.mem_span_singleton] at ha hb ⊢
    obtain ⟨r, rfl⟩ := ha
    obtain ⟨s, rfl⟩ := hb
    exact ⟨r * s, by rw [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul]⟩
  cstar_mem := by
    rintro a ha
    rw [Submodule.mem_span_singleton] at ha ⊢
    obtain ⟨r, rfl⟩ := ha
    exact ⟨r, by rw [cstar_smul, cstar_one]⟩

/-! ### Hurwitz's theorem -/

/-- **Hurwitz's theorem (dimension form).** A finite-dimensional Euclidean composition algebra
has real dimension `1`, `2`, `4` or `8`.

`Composition/Instances.lean` exhibits `ℝ`, `ℂ`, `ℍ` and `𝕆` at the four values, so each is
attained. The *classification* — that those four are the only algebras, not just the only
dimensions — is `Composition/Classification.lean`'s `hurwitz_classification`, not this
theorem. -/
theorem finrank_eq_one_or_two_or_four_or_eight :
    Module.finrank ℝ C = 1 ∨ Module.finrank ℝ C = 2 ∨ Module.finrank ℝ C = 4 ∨
      Module.finrank ℝ C = 8 := by
  have hone : (1 : C) ≠ 0 := one_ne_zero
  let A0 : Submodule ℝ C := Submodule.span ℝ {(1 : C)}
  have hA0 : IsCompSubalgebra A0 := isCompSubalgebra_spanOne
  have hr0 : Module.finrank ℝ A0 = 1 := finrank_span_singleton hone
  by_cases h0 : A0 = ⊤
  · left; rw [← finrank_top ℝ C, ← h0]; exact hr0
  obtain ⟨u1, hu1, hnu1⟩ := exists_unit_orthogonal h0
  set A1 : Submodule ℝ C := double A0 u1 with hA1def
  have hA1 : IsCompSubalgebra A1 := hA0.isCompSubalgebra_double hu1 hnu1
  have hr1 : Module.finrank ℝ A1 = 2 := by
    rw [hA1def, hA0.finrank_double hu1 hnu1, hr0]
  by_cases h1 : A1 = ⊤
  · right; left; rw [← finrank_top ℝ C, ← h1]; exact hr1
  obtain ⟨u2, hu2, hnu2⟩ := exists_unit_orthogonal h1
  set A2 : Submodule ℝ C := double A1 u2 with hA2def
  have hA2 : IsCompSubalgebra A2 := hA1.isCompSubalgebra_double hu2 hnu2
  have hr2 : Module.finrank ℝ A2 = 4 := by
    rw [hA2def, hA1.finrank_double hu2 hnu2, hr1]
  by_cases h2 : A2 = ⊤
  · right; right; left; rw [← finrank_top ℝ C, ← h2]; exact hr2
  obtain ⟨u3, hu3, hnu3⟩ := exists_unit_orthogonal h2
  set A3 : Submodule ℝ C := double A2 u3 with hA3def
  have hA3 : IsCompSubalgebra A3 := hA2.isCompSubalgebra_double hu3 hnu3
  have hr3 : Module.finrank ℝ A3 = 8 := by
    rw [hA3def, hA2.finrank_double hu3 hnu3, hr2]
  by_cases h3 : A3 = ⊤
  · right; right; right; rw [← finrank_top ℝ C, ← h3]; exact hr3
  -- A fourth doubling is impossible.
  exfalso
  obtain ⟨u4, hu4, hnu4⟩ := exists_unit_orthogonal h3
  have hassoc : ∀ x ∈ A3, ∀ y ∈ A3, ∀ z ∈ A3, (x * y) * z = x * (y * z) :=
    hA3.forced_assoc hu4 hnu4
  rw [hA3def] at hassoc
  have hcomm2 : ∀ x ∈ A2, ∀ y ∈ A2, x * y = y * x :=
    hA2.comm_of_assoc_double hu3 hnu3 hassoc
  rw [hA2def] at hcomm2
  have hle : A1 ≤ Submodule.span ℝ {(1 : C)} :=
    hA1.le_span_one_of_comm_double hu2 hnu2 hcomm2
  have hlt : Module.finrank ℝ A1 ≤ 1 := by
    have hm := Submodule.finrank_mono hle
    rwa [finrank_span_singleton hone] at hm
  omega

end CompositionAlgebra
