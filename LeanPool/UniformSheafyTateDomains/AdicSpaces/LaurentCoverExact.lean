/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.TateAlgebra

/-!
# Laurent Cover Exactness (Wedhorn Lemma 8.33)

For any element `f ∈ A` (in a strongly noetherian Tate ring), the 2-element
Laurent cover yields an exact sequence:

  `0 → A → B₁ × B₂ → B₁₂ → 0`

where:
- `B₁ = A⟨ζ⟩/(f-ζ)` (presheaf at `R(f/1)`)
- `B₂ = A⟨η⟩/(1-fη)` (presheaf at `R(1/f)`)
- `B₁₂ = A⟨ζ,ζ⁻¹⟩/(f-ζ)` (presheaf at `R(f/1) ∩ R(1/f)`)

## Discrete case

For `[DiscreteTopology A]`:
- `B₁ ≅ A` (via `quotientFSubXEquiv`)
- `B₂ ≅ Localization.Away f` (via `quotientOneSubfXEquiv`)
- `B₁₂ ≅ Localization.Away f`
- The exact sequence becomes: `0 → A → A × A[1/f] → A[1/f] → 0`

This is the standard Čech complex for the cover `Spec A = D(f) ∪ Spec A`.

## General (non-discrete) case

For `[IsDomain A] [IsNoetherianRing A]` without `[DiscreteTopology A]`:
- `B₁` and `B₂` are defined as the same quotient rings (these are purely algebraic).
- The diagonal map `ε : A → B₁ × B₂` is injective when `f` is not a unit, via the
  Krull intersection theorem for domains: the coefficient recurrence from
  `(f - X) · c = algebraMap a` forces `a ∈ ⋂ₙ (f)ⁿ = 0`.
- Both quotients `B₁` and `B₂` are flat over `A` (from `flat_quotient_fSubX_general`
  and `flat_quotient_oneSubfX_general` in `TateAlgebra.lean`).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 8.33
-/

@[expose] public section

open TateAlgebra LaurentTateAlgebra

namespace LaurentCover

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! ### The Laurent cover maps (Row 2 of the 3×3 diagram) -/

/-- The diagonal embedding `ι : A → A⟨ζ⟩ × A⟨η⟩` sending `a ↦ (a, a)`. -/
noncomputable def iotaHom :
    A →+* ↥(TateAlgebra A) × ↥(TateAlgebra A) :=
  RingHom.prod (algebraMap A ↥(TateAlgebra A)) (algebraMap A ↥(TateAlgebra A))

/-- The difference map `λ : A⟨ζ⟩ × A⟨η⟩ → A⟨ζ, ζ⁻¹⟩` sending
`(g, h) ↦ posEmb(g) - negEmb(h)`. This is an additive group homomorphism. -/
noncomputable def lambdaMap :
    ↥(TateAlgebra A) × ↥(TateAlgebra A) →+ LaurentTateAlgebra A where
  toFun p := posEmbHom p.1 - negEmbHom p.2
  map_zero' := by simp
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring

/-! ### Discrete case: direct exactness via ring isomorphisms -/

section Discrete

variable [DiscreteTopology A] [IsNoetherianRing A]

/-- `B₁ = A⟨X⟩/(f-X)` for the discrete case. -/
noncomputable abbrev B₁ (f : A) :=
  ↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}

/-- `B₂ = A⟨Y⟩/(1-fY)` for the discrete case. -/
noncomputable abbrev B₂ (f : A) :=
  ↥(TateAlgebra A) ⧸ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}

/-- The diagonal map `ε : A → B₁ × B₂` from Row 3. -/
noncomputable def epsilonHom (f : A) : A →+* B₁ f × B₂ f :=
  RingHom.prod
    ((Ideal.Quotient.mk _).comp (algebraMap A ↥(TateAlgebra A)))
    ((Ideal.Quotient.mk _).comp (algebraMap A ↥(TateAlgebra A)))

omit [IsNoetherianRing A] in
/-- `ε` is injective: the diagonal embedding into B₁ × B₂ is injective.
For discrete A, B₁ ≅ A via `quotientFSubXEquiv`, and the first projection
composed with this equivalence is the identity. -/
theorem epsilonHom_injective (f : A) : Function.Injective (epsilonHom f) := by
  intro a b hab
  have h1 := (Prod.mk.inj hab).1
  have hcomp : (TateAlgebra.quotientFSubXToA f).comp
      (TateAlgebra.AToQuotientFSubX f) = RingHom.id A :=
    TateAlgebra.quotientFSubXToA_comp_AToQuotientFSubX f
  have ha := RingHom.congr_fun hcomp a
  have hb := RingHom.congr_fun hcomp b
  simp only [RingHom.comp_apply, RingHom.id_apply] at ha hb
  rw [← ha, ← hb]
  exact congr_arg (TateAlgebra.quotientFSubXToA f) h1

/-- The δ map: `B₁ f × B₂ f →+ Localization.Away f` defined as the difference
of the two natural maps to `Localization.Away f`:
- First component: `B₁ f ≅ A → Localization.Away f` (algebraMap composed with equiv)
- Second component: `B₂ f ≅ Localization.Away f` (just the equiv)

This is the second map in the Cech complex for the Laurent cover. -/
noncomputable def deltaMap (f : A) : B₁ f × B₂ f →+ Localization.Away f where
  toFun p :=
    algebraMap A (Localization.Away f) (TateAlgebra.quotientFSubXToA f p.1) -
      TateAlgebra.quotientOneSubfXToLoc f p.2
  map_zero' := by simp [map_zero]
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring

omit [IsNoetherianRing A] in
/-- The composition `delta circ epsilon = 0`: the image of `epsilon` lands in the
kernel of `delta`. -/
theorem deltaMap_comp_epsilonHom (f : A) :
    ∀ a : A, deltaMap f (epsilonHom f a) = 0 := by
  intro a
  simp only [deltaMap, epsilonHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    RingHom.prod_apply, RingHom.comp_apply]
  have h1 : TateAlgebra.quotientFSubXToA f
      ((Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a)) = a := by
    simpa only [RingHom.comp_apply, RingHom.id_apply, TateAlgebra.AToQuotientFSubX]
      using RingHom.congr_fun (TateAlgebra.quotientFSubXToA_comp_AToQuotientFSubX f) a
  have h2 : TateAlgebra.quotientOneSubfXToLoc f
      ((Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a)) =
      algebraMap A (Localization.Away f) a := by
    simp only [TateAlgebra.quotientOneSubfXToLoc, Ideal.Quotient.lift_mk,
      TateAlgebra.evalInvFHom_algebraMap]
  rw [h1, h2, sub_self]

omit [IsNoetherianRing A] in
/-- The delta map is surjective: given any element of `Localization.Away f`,
we can find a preimage in `B_1 f x B_2 f`. -/
theorem deltaMap_surjective (f : A) : Function.Surjective (deltaMap f) := by
  intro y
  refine ⟨(0, (TateAlgebra.quotientOneSubfXEquiv f).symm (-y)), ?_⟩
  simp only [deltaMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_zero]
  have h : TateAlgebra.quotientOneSubfXToLoc f
      ((TateAlgebra.quotientOneSubfXEquiv f).symm (-y)) = -y :=
    (TateAlgebra.quotientOneSubfXEquiv f).right_inv (-y)
  rw [h]
  ring

omit [IsNoetherianRing A] in
/-- Helper: `quotientOneSubfXToLoc` is injective (it's one direction of an equiv). -/
theorem quotientOneSubfXToLoc_injective (f : A) :
    Function.Injective (TateAlgebra.quotientOneSubfXToLoc f) :=
  (TateAlgebra.quotientOneSubfXEquiv f).injective

omit [IsNoetherianRing A] in
/-- Reverse inclusion: if `delta(b_1, b_2) = 0` then `(b_1, b_2)` is in the range
of `epsilon`. This uses that both equivalences allow us to recover the element
`a` in `A`. -/
theorem ker_deltaMap_le_range_epsilonHom (f : A) :
    ∀ p : B₁ f × B₂ f, deltaMap f p = 0 → ∃ a : A, epsilonHom f a = p := by
  intro ⟨b₁, b₂⟩ h
  simp only [deltaMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  -- From h: algebraMap(quotientFSubXToA(b₁)) - quotientOneSubfXToLoc(b₂) = 0
  have heq : algebraMap A (Localization.Away f) (TateAlgebra.quotientFSubXToA f b₁) =
      TateAlgebra.quotientOneSubfXToLoc f b₂ := sub_eq_zero.mp h
  set a := TateAlgebra.quotientFSubXToA f b₁
  -- b₁ = AToQuotientFSubX(a) since the equiv round-trips
  have hb₁ : TateAlgebra.AToQuotientFSubX f a = b₁ :=
    (TateAlgebra.quotientFSubXEquiv f).symm_apply_apply b₁
  -- quotientOneSubfXToLoc(mk(algebraMap a)) = algebraMap(a)
  have himg : TateAlgebra.quotientOneSubfXToLoc f
      ((Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a)) =
      algebraMap A (Localization.Away f) a := by
    simp only [TateAlgebra.quotientOneSubfXToLoc, Ideal.Quotient.lift_mk,
      TateAlgebra.evalInvFHom_algebraMap]
  have hb₂ : (Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a) = b₂ := by
    apply quotientOneSubfXToLoc_injective f
    rw [himg, heq]
  exact ⟨a, Prod.ext hb₁ hb₂⟩

omit [IsNoetherianRing A] in
/-- **Laurent cover exactness (Wedhorn Lemma 8.33, discrete case).**
The sequence `0 -> A ->[epsilon] B_1 f x B_2 f ->[delta] Localization.Away f -> 0`
is exact:
1. `epsilon` is injective
2. `delta` is surjective
3. `delta circ epsilon = 0` (image of epsilon is contained in kernel of delta)
4. `ker delta` is a subset of `im epsilon` -/
theorem laurentCover_exact (f : A) :
    Function.Injective (epsilonHom f) ∧
    Function.Surjective (deltaMap f) ∧
    (∀ x, deltaMap f (epsilonHom f x) = 0) ∧
    (∀ p, deltaMap f p = 0 → ∃ a, epsilonHom f a = p) :=
  ⟨epsilonHom_injective f,
   deltaMap_surjective f,
   deltaMap_comp_epsilonHom f,
   ker_deltaMap_le_range_epsilonHom f⟩

end Discrete

/-! ### General (non-discrete) case: algebraic exactness via Krull intersection

For a noetherian domain `A` (without `[DiscreteTopology A]`), the quotient rings
`B₁ = A⟨X⟩/(f-X)` and `B₂ = A⟨X⟩/(1-fX)` are defined identically to the discrete
case. The key new result is the injectivity of the diagonal embedding `ε : A → B₁ × B₂`
for non-unit `f`, proved via the Krull intersection theorem.

The delta map and full exactness in the non-discrete case require completing these
quotients with respect to the T-topology (Wedhorn, Definition 8.27), which belongs
to the completed presheaf theory. Here we establish the algebraic ingredients. -/

section General

variable [IsNoetherianRing A] [IsDomain A]

/-- `B₁` for the general (non-discrete) case: the quotient `A⟨X⟩/(f-X)`.
This is the same type as the discrete `B₁`, but without requiring `[DiscreteTopology A]`. -/
noncomputable abbrev B₁_gen (f : A) :=
  ↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}

/-- `B₂` for the general (non-discrete) case: the quotient `A⟨X⟩/(1-fX)`.
This is the same type as the discrete `B₂`, but without requiring `[DiscreteTopology A]`. -/
noncomputable abbrev B₂_gen (f : A) :=
  ↥(TateAlgebra A) ⧸ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}

/-- The diagonal map `ε : A → B₁ × B₂` (general case, no `[DiscreteTopology A]`). -/
noncomputable def epsilonHom_gen (f : A) : A →+* B₁_gen f × B₂_gen f :=
  RingHom.prod
    ((Ideal.Quotient.mk _).comp (algebraMap A ↥(TateAlgebra A)))
    ((Ideal.Quotient.mk _).comp (algebraMap A ↥(TateAlgebra A)))

omit [IsNoetherianRing A] [IsDomain A] in
/-- The 0-th coefficient of a constant series equals the constant. -/
private theorem coeff_zero_algebraMap (a : A) :
    TateAlgebra.coeff 0 (algebraMap A ↥(TateAlgebra A) a) = a := by
  simp only [TateAlgebra.coeff, TateAlgebra.toIndex_zero]; norm_cast

omit [IsNoetherianRing A] [IsDomain A] in
/-- Higher coefficients of a constant series vanish. -/
private theorem coeff_succ_algebraMap (a : A) (n : ℕ) :
    TateAlgebra.coeff (n + 1) (algebraMap A ↥(TateAlgebra A) a) = 0 := by
  simp only [TateAlgebra.coeff, TateAlgebra.toIndex]
  change MvPowerSeries.coeff (Finsupp.single 0 (n + 1)) (algebraMap A _ a) = 0
  rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
  exact if_neg (Finsupp.single_ne_zero.mpr (Nat.succ_ne_zero n))

omit [IsNoetherianRing A] [IsDomain A] in
/-- If a constant `algebraMap a` lies in `Ideal.span {f - X}` and
`⋂ n, (f)^n = 0`, then `a = 0`.

The proof extracts the coefficient recurrence from `(f - X) · c = algebraMap a`:
- Constant term: `f · coeff 0 c = a`
- Higher terms: `coeff n c = f · coeff (n + 1) c` for all `n`

This yields `a = f^(n+1) · coeff n c`, hence `a ∈ (f)^n` for all `n`.
The supplied intersection hypothesis then gives `a = 0`. This is the
Krull-independent core used by the domain theorem below and by future
non-domain Tate/Jacobson variants. -/
theorem algebraMap_mem_span_fSubX_eq_zero_of_iInf_pow_eq_bot (f a : A)
    (hInf : (⨅ n : ℕ, Ideal.span ({f} : Set A) ^ n) = ⊥)
    (h : algebraMap A ↥(TateAlgebra A) a ∈
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) : a = 0 := by
  rw [Ideal.mem_span_singleton'] at h
  obtain ⟨c, hc⟩ := h
  -- Rewrite with (f - X) on the left.
  have hc' : (algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X) * c =
      algebraMap A _ a := by rw [mul_comm]; exact hc
  -- Coefficient equations from (f - X) * c = algebraMap a.
  have hcoeff_eq : ∀ n,
      f * TateAlgebra.coeff n c - TateAlgebra.coeff n (TateAlgebra.X * c) =
      TateAlgebra.coeff n (algebraMap A ↥(TateAlgebra A) a) := by
    intro n
    have := congr_arg (TateAlgebra.coeff n) hc'
    rwa [sub_mul, TateAlgebra.coeff_sub, TateAlgebra.coeff_algebraMap_mul] at this
  -- Constant coefficient: f * coeff 0 c = a.
  have h0 : f * TateAlgebra.coeff 0 c = a := by
    have := hcoeff_eq 0
    rwa [TateAlgebra.coeff_zero_X_mul, sub_zero, coeff_zero_algebraMap] at this
  -- Recurrence: coeff n c = f * coeff (n + 1) c.
  have hstep : ∀ n,
      TateAlgebra.coeff n c = f * TateAlgebra.coeff (n + 1) c := by
    intro n
    have h1 := hcoeff_eq (n + 1)
    rw [TateAlgebra.coeff_succ_X_mul, coeff_succ_algebraMap] at h1
    exact (sub_eq_zero.mp h1).symm
  -- Power relation: coeff 0 c = f^n * coeff n c.
  have hpow : ∀ n,
      TateAlgebra.coeff 0 c = f ^ n * TateAlgebra.coeff n c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hstep n, pow_succ, mul_assoc]
  -- a ∈ (f)^n for all n.
  have ha_mem : ∀ n, a ∈ Ideal.span ({f} : Set A) ^ n := by
    intro n
    cases n with
    | zero => simp [Ideal.one_eq_top]
    | succ n =>
      have : a = f ^ (n + 1) * TateAlgebra.coeff n c := by
        rw [← h0, hpow n]
        ring
      rw [this]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self f) (n + 1))
  exact Ideal.mem_bot.mp (hInf ▸ Ideal.mem_iInf.mpr ha_mem)

omit [IsNoetherianRing A] [IsDomain A] in
/-- Plus-side coefficient recurrence for the simple Laurent row.

If a constant series lies in `(f - X)`, then it admits witnesses
`a = f^(n+1) * c_n` whose coefficients `c_n` tend to zero. This is the
topological strengthening of the first-projection computation used in
`algebraMap_mem_span_fSubX_eq_zero_of_iInf_pow_eq_bot`. -/
theorem exists_coeff_tendsto_and_pow_mul_of_algebraMap_mem_fSubX (f a : A)
    (h : algebraMap A ↥(TateAlgebra A) a ∈
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) :
    ∃ c : ↥(TateAlgebra A),
      Filter.Tendsto (fun n : ℕ => TateAlgebra.coeff n c) Filter.cofinite
        (nhds (0 : A)) ∧
      ∀ n : ℕ, a = f ^ (n + 1) * TateAlgebra.coeff n c := by
  rw [Ideal.mem_span_singleton'] at h
  obtain ⟨c, hc⟩ := h
  have hc' : (algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X) * c =
      algebraMap A _ a := by
    rw [mul_comm]
    exact hc
  have hcoeff_eq : ∀ n,
      f * TateAlgebra.coeff n c - TateAlgebra.coeff n (TateAlgebra.X * c) =
      TateAlgebra.coeff n (algebraMap A ↥(TateAlgebra A) a) := by
    intro n
    have := congr_arg (TateAlgebra.coeff n) hc'
    rwa [sub_mul, TateAlgebra.coeff_sub, TateAlgebra.coeff_algebraMap_mul] at this
  have h0 : f * TateAlgebra.coeff 0 c = a := by
    have := hcoeff_eq 0
    rwa [TateAlgebra.coeff_zero_X_mul, sub_zero, coeff_zero_algebraMap] at this
  have hstep : ∀ n,
      TateAlgebra.coeff n c = f * TateAlgebra.coeff (n + 1) c := by
    intro n
    have h1 := hcoeff_eq (n + 1)
    rw [TateAlgebra.coeff_succ_X_mul, coeff_succ_algebraMap] at h1
    exact (sub_eq_zero.mp h1).symm
  have hpow : ∀ n,
      TateAlgebra.coeff 0 c = f ^ n * TateAlgebra.coeff n c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hstep n, pow_succ, mul_assoc]
  refine ⟨c, TateAlgebra.coeff_tendsto_zero c, ?_⟩
  intro n
  rw [← h0, hpow n]
  ring

/-- If a constant `algebraMap a` lies in `Ideal.span {f - X}` and `f` is not a unit
in a noetherian domain, then `a = 0`.

This is the domain/Krull-intersection specialization of
`algebraMap_mem_span_fSubX_eq_zero_of_iInf_pow_eq_bot`. -/
theorem algebraMap_mem_span_fSubX_eq_zero (f : A) (hf : ¬IsUnit f) (a : A)
    (h : algebraMap A ↥(TateAlgebra A) a ∈
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) : a = 0 := by
  have hf_ne_top : Ideal.span ({f} : Set A) ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  exact algebraMap_mem_span_fSubX_eq_zero_of_iInf_pow_eq_bot f a
    (Ideal.iInf_pow_eq_bot_of_isDomain _ hf_ne_top) h

omit [IsNoetherianRing A] [IsDomain A] in
/-- **`ε` is injective from an explicit Krull-intersection input.**

This theorem isolates the only algebraic separation input needed by the
first projection of Wedhorn's Laurent row: if `⋂ n, (f)^n = 0`, then
the diagonal map `A → B₁(f) × B₂(f)` is injective. -/
theorem epsilonHom_gen_injective_of_iInf_pow_eq_bot (f : A)
    (hInf : (⨅ n : ℕ, Ideal.span ({f} : Set A) ^ n) = ⊥) :
    Function.Injective (epsilonHom_gen f) := by
  intro a b hab
  have h1 := (Prod.mk.inj hab).1
  simp only [RingHom.comp_apply] at h1
  have hmem : algebraMap A ↥(TateAlgebra A) (a - b) ∈
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X} := by
    rw [map_sub]; exact Ideal.Quotient.eq.mp h1
  exact sub_eq_zero.mp
    (algebraMap_mem_span_fSubX_eq_zero_of_iInf_pow_eq_bot f (a - b) hInf hmem)

omit [IsNoetherianRing A] [IsDomain A] in
/-- If a constant series belongs to `(1 - fX)`, then the powers `f^n * a`
tend to zero.

This is the formal second-projection ingredient in the general
Wedhorn/Hübner simple-Laurent separation argument: membership in the minus
quotient gives a restricted witness whose coefficients are exactly
`f^n * a`. -/
theorem tendsto_pow_mul_of_algebraMap_mem_oneSubfX (f a : A)
    (h : algebraMap A ↥(TateAlgebra A) a ∈
      Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}) :
    Filter.Tendsto (fun n : ℕ => f ^ n * a) Filter.cofinite (nhds (0 : A)) := by
  rw [Ideal.mem_span_singleton'] at h
  obtain ⟨c, hc⟩ := h
  have hc' : (1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X) * c =
      algebraMap A _ a := by
    rw [mul_comm]
    exact hc
  have hcoeff_eq : ∀ n,
      TateAlgebra.coeff n c -
        f * TateAlgebra.coeff n (TateAlgebra.X * c) =
      TateAlgebra.coeff n (algebraMap A ↥(TateAlgebra A) a) := by
    intro n
    have := congr_arg (TateAlgebra.coeff n) hc'
    rwa [sub_mul, one_mul, mul_assoc, TateAlgebra.coeff_sub,
      TateAlgebra.coeff_algebraMap_mul] at this
  have h0 : TateAlgebra.coeff 0 c = a := by
    have := hcoeff_eq 0
    rwa [TateAlgebra.coeff_zero_X_mul, mul_zero, sub_zero,
      coeff_zero_algebraMap] at this
  have hstep : ∀ n, TateAlgebra.coeff (n + 1) c =
      f * TateAlgebra.coeff n c := by
    intro n
    have := hcoeff_eq (n + 1)
    rw [TateAlgebra.coeff_succ_X_mul, coeff_succ_algebraMap] at this
    exact sub_eq_zero.mp this
  have hpow : ∀ n, TateAlgebra.coeff n c = f ^ n * a := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
        rw [hstep n, ih, pow_succ, mul_assoc]
        ring
  simpa [hpow] using TateAlgebra.coeff_tendsto_zero c

omit [IsNoetherianRing A] [IsDomain A] in
/-- If the minus component of `ε(a)` vanishes, then `f^n * a → 0`.

This packages the second projection of the simple Laurent row in a form that
the separation proof can use directly. -/
theorem tendsto_pow_mul_of_epsilonHom_gen_second_eq_zero (f a : A)
    (h2 : (epsilonHom_gen f a).2 = 0) :
    Filter.Tendsto (fun n : ℕ => f ^ n * a) Filter.cofinite (nhds (0 : A)) :=
  tendsto_pow_mul_of_algebraMap_mem_oneSubfX f a (Ideal.Quotient.eq_zero_iff_mem.mp h2)

omit [IsNoetherianRing A] [IsDomain A] in
/-- Kernel data for `ε` in the simple Laurent row.

If `ε(a) = 0`, the plus component gives restricted coefficients `c_n`
with `a = f^(n+1)c_n`, and the minus component gives `f^n a → 0`.
This theorem deliberately stops at the exact formal boundary needed for the
general non-domain separation argument. -/
theorem epsilonHom_gen_eq_zero_coeff_data (f a : A)
    (h : epsilonHom_gen f a = 0) :
    (∃ c : ↥(TateAlgebra A),
      Filter.Tendsto (fun n : ℕ => TateAlgebra.coeff n c) Filter.cofinite
        (nhds (0 : A)) ∧
      ∀ n : ℕ, a = f ^ (n + 1) * TateAlgebra.coeff n c) ∧
    Filter.Tendsto (fun n : ℕ => f ^ n * a) Filter.cofinite (nhds (0 : A)) := by
  have h1 : (epsilonHom_gen f a).1 = 0 := congr_arg Prod.fst h
  have h2 : (epsilonHom_gen f a).2 = 0 := congr_arg Prod.snd h
  refine ⟨exists_coeff_tendsto_and_pow_mul_of_algebraMap_mem_fSubX f a
      (Ideal.Quotient.eq_zero_iff_mem.mp h1),
    tendsto_pow_mul_of_epsilonHom_gen_second_eq_zero f a h2⟩

omit [IsNoetherianRing A] [IsDomain A] in
/-- Plus-side Krull-intersection membership for a constant in `(f - X)`.

If `algebraMap a` vanishes in `A⟨X⟩/(f-X)`, then `a` lies in every power of
the principal ideal `(f)`. This is the algebraic input used by the general
non-domain Krull theorem `Ideal.mem_iInf_smul_pow_eq_bot_iff`. -/
theorem mem_iInf_pow_of_algebraMap_mem_fSubX (f a : A)
    (h : algebraMap A ↥(TateAlgebra A) a ∈
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) :
    a ∈ (⨅ n : ℕ, Ideal.span ({f} : Set A) ^ n : Ideal A) := by
  obtain ⟨c, _hc_tend, hc_pow⟩ :=
    exists_coeff_tendsto_and_pow_mul_of_algebraMap_mem_fSubX f a h
  rw [Ideal.mem_iInf]
  intro n
  cases n with
  | zero => simp [Ideal.one_eq_top]
  | succ n =>
      rw [hc_pow n]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self f) (n + 1))

omit [IsDomain A] in
/-- General noetherian Krull multiplier extracted from the plus component.

If `algebraMap a ∈ (f-X)`, then Krull's general intersection theorem gives
some `r ∈ (f)` with `r * a = a`. Unlike the domain/Jacobson specializations,
this does **not** imply `a = 0`; it is the precise non-domain replacement for
the first-projection argument. -/
theorem exists_span_singleton_mul_eq_self_of_algebraMap_mem_fSubX (f a : A)
    (h : algebraMap A ↥(TateAlgebra A) a ∈
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) :
    ∃ r : Ideal.span ({f} : Set A), (r : A) * a = a := by
  have hmem_ideal := mem_iInf_pow_of_algebraMap_mem_fSubX f a h
  have hmem_submodule :
      a ∈ (⨅ n : ℕ, Ideal.span ({f} : Set A) ^ n • ⊤ : Submodule A A) := by
    rw [Submodule.mem_iInf]
    intro n
    have hn : a ∈ Ideal.span ({f} : Set A) ^ n := (Ideal.mem_iInf.mp hmem_ideal) n
    rwa [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
  obtain ⟨r, hr⟩ :=
    (Ideal.mem_iInf_smul_pow_eq_bot_iff
      (I := Ideal.span ({f} : Set A)) (M := A) a).mp hmem_submodule
  exact ⟨r, by simpa [smul_eq_mul] using hr⟩

omit [IsDomain A] in
/-- Epsilon-kernel Krull multiplier from the plus component. -/
theorem exists_span_singleton_mul_eq_self_of_epsilonHom_gen_eq_zero (f a : A)
    (h : epsilonHom_gen f a = 0) :
    ∃ r : Ideal.span ({f} : Set A), (r : A) * a = a := by
  have h1 : (epsilonHom_gen f a).1 = 0 := congr_arg Prod.fst h
  exact exists_span_singleton_mul_eq_self_of_algebraMap_mem_fSubX f a
    (Ideal.Quotient.eq_zero_iff_mem.mp h1)

omit [IsDomain A] in
/-- Combined non-domain kernel data for the simple Laurent row.

For `ε(a)=0`, the plus component and general noetherian Krull theorem give a
multiplier `c` with `(c*f)^n a = a`, while the minus component gives
`f^n a → 0`. The missing final Tate-topology step is exactly to control the
possibly unbounded powers `c^n`; this theorem isolates that boundary without
adding a reducedness/Jacobson hypothesis. -/
theorem epsilonHom_gen_eq_zero_krull_multiplier_data (f a : A)
    (h : epsilonHom_gen f a = 0) :
    ∃ c : A,
      (∀ n : ℕ, c ^ n * (f ^ n * a) = a) ∧
      Filter.Tendsto (fun n : ℕ => f ^ n * a) Filter.cofinite (nhds (0 : A)) := by
  obtain ⟨r, hr⟩ := exists_span_singleton_mul_eq_self_of_epsilonHom_gen_eq_zero f a h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp r.property
  have hcf : (c * f) * a = a := by rw [hc]; exact hr
  have hcf_pow : ∀ n : ℕ, (c * f) ^ n * a = a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          (c * f) ^ (n + 1) * a = (c * f) ^ n * ((c * f) * a) := by
            rw [pow_succ, mul_assoc]
          _ = (c * f) ^ n * a := by rw [hcf]
          _ = a := ih
  refine ⟨c, ?_, tendsto_pow_mul_of_epsilonHom_gen_second_eq_zero f a (congr_arg Prod.snd h)⟩
  intro n
  calc
    c ^ n * (f ^ n * a) = (c ^ n * f ^ n) * a := by ring
    _ = (c * f) ^ n * a := by rw [mul_pow]
    _ = a := hcf_pow n

omit [IsNoetherianRing A] [IsDomain A] in
/-- A Hausdorff consequence of the two projection recurrences.

If `ε(a) = 0`, then the plus component writes `a = f^(n+1)c_n` with
`c_n → 0`, while the minus component gives `f^n a → 0`. Multiplying the
two convergent factors shows the constant sequence `a^2` tends to `0`;
Hausdorffness forces `a^2 = 0`.

This is not the full non-domain injectivity statement, but it isolates the
remaining obstruction to nilpotents. -/
theorem sq_eq_zero_of_epsilonHom_gen_eq_zero [T2Space A] (f a : A)
    (h : epsilonHom_gen f a = 0) :
    a ^ 2 = 0 := by
  obtain ⟨⟨c, hc_tend, hc_pow⟩, hfa_tend⟩ :=
    epsilonHom_gen_eq_zero_coeff_data f a h
  have hseq_tend :
      Filter.Tendsto
        (fun n : ℕ => f * (TateAlgebra.coeff n c * (f ^ n * a)))
        Filter.cofinite (nhds (0 : A)) := by
    simpa using (hc_tend.mul hfa_tend).const_mul f
  have hseq_eq : ∀ n : ℕ,
      f * (TateAlgebra.coeff n c * (f ^ n * a)) = a ^ 2 := by
    intro n
    calc
      f * (TateAlgebra.coeff n c * (f ^ n * a)) =
          (f ^ (n + 1) * TateAlgebra.coeff n c) * a := by
            ring
      _ = a * a := by
            rw [← hc_pow n]
      _ = a ^ 2 := by
            ring
  have hconst_zero : Filter.Tendsto (fun _ : ℕ => a ^ 2)
      Filter.cofinite (nhds (0 : A)) :=
    hseq_tend.congr' (Filter.Eventually.of_forall hseq_eq)
  exact tendsto_nhds_unique tendsto_const_nhds hconst_zero

omit [TopologicalSpace A] [NonarchimedeanRing A] [IsDomain A] in
/-- Krull intersection for a principal ideal contained in the Jacobson radical. -/
theorem span_singleton_iInf_pow_eq_bot_of_le_jacobson (f : A)
    (hf_jac : Ideal.span ({f} : Set A) ≤ Ideal.jacobson (⊥ : Ideal A)) :
    (⨅ n : ℕ, Ideal.span ({f} : Set A) ^ n) = ⊥ := by
  have hsub :
      (⨅ n : ℕ, Ideal.span ({f} : Set A) ^ n • ⊤ : Submodule A A) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ hf_jac
  rw [eq_bot_iff]
  intro x hx
  have hx_sub :
      x ∈ (⨅ n : ℕ, Ideal.span ({f} : Set A) ^ n • ⊤ : Submodule A A) := by
    rw [Submodule.mem_iInf]
    intro n
    have hxn : x ∈ Ideal.span ({f} : Set A) ^ n := (Ideal.mem_iInf.mp hx) n
    rwa [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
  rw [hsub] at hx_sub
  simpa using hx_sub

omit [IsDomain A] in
/-- **`ε` is injective when `(f)` lies in the Jacobson radical.**

This is a non-domain specialization of
`epsilonHom_gen_injective_of_iInf_pow_eq_bot` via Mathlib's Krull
intersection theorem for ideals contained in `Jacobson(0)`. -/
theorem epsilonHom_gen_injective_of_span_le_jacobson (f : A)
    (hf_jac : Ideal.span ({f} : Set A) ≤ Ideal.jacobson (⊥ : Ideal A)) :
    Function.Injective (epsilonHom_gen f) :=
  epsilonHom_gen_injective_of_iInf_pow_eq_bot f
    (span_singleton_iInf_pow_eq_bot_of_le_jacobson f hf_jac)

/-- **`ε` is injective (general case, Wedhorn Lemma 8.33 without `[DiscreteTopology A]`).**

For a noetherian domain `A` and non-unit `f`, the diagonal embedding
`ε : A → B₁(f) × B₂(f)` is injective. The proof uses the first projection:
if `ε(a) = ε(b)` then `algebraMap(a - b) ∈ (f - X)`, and the Krull intersection
theorem forces `a - b = 0`. -/
theorem epsilonHom_gen_injective (f : A) (hf : ¬IsUnit f) :
    Function.Injective (epsilonHom_gen f) := by
  have hf_ne_top : Ideal.span ({f} : Set A) ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  exact epsilonHom_gen_injective_of_iInf_pow_eq_bot f
    (Ideal.iInf_pow_eq_bot_of_isDomain _ hf_ne_top)

omit [IsDomain A] in
/-- Multiplication by `f - X` is injective on `A⟨X⟩` (general case, no topology needed
beyond `[IsNoetherianRing A]`). This is `TateAlgebra.mul_fSubX_regular`, re-exported
here for convenience. -/
theorem fSubX_regular (f : A) :
    ∀ x : ↥(TateAlgebra A),
      (algebraMap A _ f - TateAlgebra.X) * x = 0 → x = 0 :=
  TateAlgebra.mul_fSubX_regular f

omit [IsDomain A] in
/-- Multiplication by `1 - fX` is injective on `A⟨X⟩` (general case). This is
`TateAlgebra.mul_oneSubfX_regular`, re-exported here for convenience. -/
theorem oneSubfX_regular (f : A) :
    ∀ x : ↥(TateAlgebra A),
      (1 - algebraMap A _ f * TateAlgebra.X) * x = 0 → x = 0 :=
  TateAlgebra.mul_oneSubfX_regular f

end General

/-! ### Row 2 exactness: ker(lambda) = im(iota) (Wedhorn Lemma 8.33, Row 2)

The sequence `A ->[iota] A<X> x A<X> ->[lambda] A<zeta, zeta^{-1}>` is exact at
the middle term. The composition `lambda circ iota = 0` because both embeddings
`posEmbHom` and `negEmbHom` agree on constants from `A`. The reverse inclusion
`ker(lambda) <= im(iota)` uses the restricted power series structure: if
`posEmbHom(g) = negEmbHom(h)`, the ideal membership witness `c` satisfying
`(XY - 1) * c = posIncl(g) - negIncl(h)` is constant along diagonal lines in
the bivariate index space, and the restricted condition forces these constants
(hence all higher coefficients of `g` and `h`) to vanish. -/

section Row2Exactness

/-! #### Helper lemmas for bivariate coefficient manipulation -/

/-- A bivariate multi-index `(i, j) : Fin 2 →₀ ℕ`. -/
private noncomputable def idx (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

private theorem idx_apply_zero (i j : ℕ) : idx i j 0 = i := by
  simp [idx]

private theorem idx_apply_one (i j : ℕ) : idx i j 1 = j := by
  simp [idx]

private theorem idx_eq_single_zero_iff (i j : ℕ) :
    idx i j = Finsupp.single 0 (idx i j 0) ↔ j = 0 := by
  rw [idx_apply_zero]
  constructor
  · intro h
    simpa [idx] using Finsupp.ext_iff.mp h 1
  · intro hj
    subst hj; ext k; fin_cases k <;> simp [idx]

private theorem idx_eq_single_one_iff (i j : ℕ) :
    idx i j = Finsupp.single 1 (idx i j 1) ↔ i = 0 := by
  rw [idx_apply_one]
  constructor
  · intro h
    simpa [idx] using Finsupp.ext_iff.mp h 0
  · intro hi
    subst hi; ext k; fin_cases k <;> simp [idx]

private theorem idx_zero_zero : idx 0 0 = (0 : Fin 2 →₀ ℕ) := by
  ext k; fin_cases k <;> simp [idx]

/-- Every `Fin 2 →₀ ℕ` index equals `idx (e 0) (e 1)`. -/
private theorem eq_idx (e : Fin 2 →₀ ℕ) : e = idx (e 0) (e 1) := by
  ext k; fin_cases k <;> simp [idx]

/-- The RHS coefficient: `posIncl g` at index `idx i j`. -/
private theorem coeff_posIncl (g : ↥(TateAlgebra A)) (i j : ℕ) :
    MvPowerSeries.coeff (idx i j) (posIncl g).val =
      if j = 0 then MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) i) g.val else 0 := by
  change varInclFun 0 g.val (idx i j) = _
  rw [varInclFun_apply]
  have h1 : idx i j 0 = i := idx_apply_zero i j
  rw [h1]
  have h2 : (idx i j = Finsupp.single 0 i) ↔ j = 0 := by
    rw [show Finsupp.single (0 : Fin 2) i = Finsupp.single 0 (idx i j 0) from by rw [h1]]
    exact idx_eq_single_zero_iff i j
  simp only [h2]

/-- The RHS coefficient: `negIncl h` at index `idx i j`. -/
private theorem coeff_negIncl (h : ↥(TateAlgebra A)) (i j : ℕ) :
    MvPowerSeries.coeff (idx i j) (negIncl h).val =
      if i = 0 then MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) j) h.val else 0 := by
  change varInclFun 1 h.val (idx i j) = _
  rw [varInclFun_apply]
  have h1 : idx i j 1 = j := idx_apply_one i j
  rw [h1]
  have h2 : (idx i j = Finsupp.single 1 j) ↔ i = 0 := by
    rw [show Finsupp.single (1 : Fin 2) j = Finsupp.single 1 (idx i j 1) from by rw [h1]]
    exact idx_eq_single_one_iff i j
  simp only [h2]

private theorem idx_11 :
    Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 = idx 1 1 := by
  ext k; fin_cases k <;> simp [idx]

omit [TopologicalSpace A] [NonarchimedeanRing A] in
/-- The LHS: coefficient of `(X₀ * X₁ - 1) * c` at index `idx i j`.
This equals `c(i-1, j-1) - c(i, j)` when `i, j ≥ 1`, and `-c(i, j)` otherwise. -/
private theorem coeff_XY_sub_one_mul (c : MvPowerSeries (Fin 2) A) (i j : ℕ) :
    MvPowerSeries.coeff (idx i j)
      ((MvPowerSeries.X 0 * MvPowerSeries.X 1 - 1) * c) =
      (if 0 < i ∧ 0 < j then MvPowerSeries.coeff (idx (i - 1) (j - 1)) c else 0) -
      MvPowerSeries.coeff (idx i j) c := by
  have hsub : MvPowerSeries.coeff (idx i j) ((MvPowerSeries.X 0 * MvPowerSeries.X 1 - 1) * c) =
    MvPowerSeries.coeff (idx i j) (MvPowerSeries.X 0 * MvPowerSeries.X 1 * c) -
    MvPowerSeries.coeff (idx i j) (1 * c) := by
    rw [sub_mul]; exact map_sub _ _ _
  rw [hsub, one_mul]
  congr 1
  -- Need: coeff_{idx i j} (X₀ * X₁ * c) = if (0 < i ∧ 0 < j) then c(i-1, j-1) else 0
  rw [show MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) =
    MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) (1 : A) by
    rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, one_mul]]
  rw [MvPowerSeries.coeff_monomial_mul]
  set m := Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1
  by_cases h : m ≤ idx i j
  · rw [if_pos h, one_mul]
    have hi : 0 < i := by
      have h0 := h (0 : Fin 2)
      simp [m, idx] at h0; omega
    have hj : 0 < j := by
      have h1 := h (1 : Fin 2)
      simp [m, idx] at h1; omega
    rw [if_pos ⟨hi, hj⟩]
    have hsub_eq : idx i j - m = idx (i - 1) (j - 1) := by
      apply Finsupp.ext; intro k
      simp only [Finsupp.tsub_apply, idx, m, Finsupp.add_apply, Finsupp.single_apply]
      fin_cases k <;> (simp (config := { decide := true }); try omega)
    rw [hsub_eq]
  · rw [if_neg h]
    have hnotij : ¬(0 < i ∧ 0 < j) := by
      intro ⟨hi, hj⟩; apply h; intro k
      fin_cases k <;> simp [m, idx] <;> omega
    rw [if_neg hnotij]

omit [NonarchimedeanRing A] in
/-- In a T1 space, if a restricted power series has a constant value `b` along infinitely
many indices, then `b = 0`. More precisely, if `tendsto (coeff s) cofinite (nhds 0)` and
there is an injection `ℕ → σ →₀ ℕ` such that `coeff` is constantly `b` on the range,
then `b = 0`. -/
private theorem eq_zero_of_restricted_const [T1Space A] {σ : Type*}
    (f : (σ →₀ ℕ) → A) (hf : Filter.Tendsto f Filter.cofinite (nhds 0))
    (ι : ℕ → σ →₀ ℕ) (hinj : Function.Injective ι)
    {b : A} (hconst : ∀ n, f (ι n) = b) : b = 0 := by
  by_contra hne
  -- In a T1 space, singletons are closed, so {b}ᶜ is open and contains 0
  have hopen : IsOpen ({b}ᶜ : Set A) := isOpen_compl_singleton
  have h0 : (0 : A) ∈ ({b}ᶜ : Set A) := Set.mem_compl_singleton_iff.mpr (Ne.symm hne)
  -- The set of indices where f ∉ {b}ᶜ (i.e., f = b) is finite by restrictedness
  have hmem : {b}ᶜ ∈ nhds (0 : A) := hopen.mem_nhds h0
  have hev := hf hmem
  rw [Filter.mem_map, Filter.mem_cofinite] at hev
  -- hev : {s | f s ∉ {b}ᶜ} is cofinite, i.e. {s | f s = b} is finite (in complement form)
  -- But the range of ι is infinite and lands in {s | f s = b}
  have hinf : Set.Infinite (Set.range ι) := Set.infinite_range_of_injective hinj
  have hrange_sub : Set.range ι ⊆ {s | f s ∉ ({b}ᶜ : Set A)} := by
    rintro s ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff, not_not]
    exact hconst n
  exact (hev.subset hrange_sub).not_infinite hinf

private theorem posIncl_algebraMap (a : A) :
    posIncl (algebraMap A ↥(TateAlgebra A) a) =
      algebraMap A ↥(TateAlgebra₂ A) a := by
  ext1; apply MvPowerSeries.ext; intro e
  change varInclFun 0 (algebraMap A (MvPowerSeries (Fin 1) A) a) e =
    (MvPowerSeries.coeff e) (algebraMap A (MvPowerSeries (Fin 2) A) a)
  rw [varInclFun_apply]
  simp only [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
  by_cases he : e = 0
  · subst he; simp [Finsupp.single_zero (0 : Fin 2)]
  · rw [if_neg he]
    by_cases h1 : e = Finsupp.single (0 : Fin 2) (e 0)
    · rw [if_pos h1]
      exact if_neg (Finsupp.single_ne_zero.mpr
        (fun h => he (by rw [h1, h, Finsupp.single_zero])))
    · rw [if_neg h1]

private theorem negIncl_algebraMap (a : A) :
    negIncl (algebraMap A ↥(TateAlgebra A) a) =
      algebraMap A ↥(TateAlgebra₂ A) a := by
  ext1; apply MvPowerSeries.ext; intro e
  change varInclFun 1 (algebraMap A (MvPowerSeries (Fin 1) A) a) e =
    (MvPowerSeries.coeff e) (algebraMap A (MvPowerSeries (Fin 2) A) a)
  rw [varInclFun_apply]
  simp only [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
  by_cases he : e = 0
  · subst he; simp [Finsupp.single_zero (1 : Fin 2)]
  · rw [if_neg he]
    by_cases h1 : e = Finsupp.single (1 : Fin 2) (e 1)
    · rw [if_pos h1]
      exact if_neg (Finsupp.single_ne_zero.mpr
        (fun h => he (by rw [h1, h, Finsupp.single_zero])))
    · rw [if_neg h1]

/-- The composition `lambda circ iota = 0`: the image of `iotaHom` lies in
the kernel of `lambdaMap`. Both embeddings `posEmbHom` and `negEmbHom`
agree on constants from `A`. -/
theorem lambdaMap_comp_iotaHom (a : A) : lambdaMap (iotaHom a) = 0 := by
  simp only [lambdaMap, iotaHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    RingHom.prod_apply]
  rw [sub_eq_zero]
  change mkHom (posIncl (algebraMap A ↥(TateAlgebra A) a)) =
    mkHom (negIncl (algebraMap A ↥(TateAlgebra A) a))
  rw [posIncl_algebraMap, negIncl_algebraMap]

/-- **Kernel exactness (Row 2): `ker(lambda) <= im(iota)`.**

If `posEmbHom(g) = negEmbHom(h)` in the Laurent algebra, then `g` and `h`
are both equal to `algebraMap(a)` for some `a : A`.

**Proof sketch.** The hypothesis gives `posIncl(g) - negIncl(h) in (XY - 1)`,
so there exists a restricted `c` with `c * (XY - 1) = posIncl(g) - negIncl(h)`.
Since `posIncl(g) - negIncl(h)` vanishes at all mixed indices `(m, n)` with
`m, n >= 1`, extracting the coefficient at such an index from the equation
gives the diagonal recurrence `c_{m,n} = c_{m-1,n-1}`. Iterating shows `c` is
constant along each line parallel to the main diagonal. In a T1 topological
ring, the restricted condition on `c` forces each such constant to be zero.
The boundary conditions `-c_{k,0} = g_k` and `c_{0,k} = h_k` then give
`g_k = h_k = 0` for `k >= 1`, and the diagonal `c_{n,n} = c_{0,0} = 0`
gives `g_0 = h_0`. -/
theorem ker_lambdaMap_le_range_iotaHom [T1Space A]
    (p : ↥(TateAlgebra A) × ↥(TateAlgebra A))
    (hp : lambdaMap p = 0) :
    ∃ a : A, iotaHom a = p := by
  obtain ⟨g, h⟩ := p
  have heq_laurent : posEmbHom g = negEmbHom h := by
    simp only [lambdaMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hp
    exact sub_eq_zero.mp hp
  have hmem : posIncl g - negIncl h ∈ laurentIdeal A := by
    change posIncl g - negIncl h ∈ Ideal.span {TateAlgebra₂.XY_sub_one}
    rw [← Ideal.Quotient.eq]; exact heq_laurent
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  -- hc: c * XY_sub_one = posIncl g - negIncl h
  -- Translate to MvPowerSeries level with (XY - 1) on the left
  have hc_ps : (MvPowerSeries.X (0 : Fin 2) *
      MvPowerSeries.X (1 : Fin 2) - 1) * c.val =
      (posIncl g).val - (negIncl h).val := by
    have := congr_arg Subtype.val hc; rw [mul_comm] at this; exact this
  -- Step 1: Extract the coefficient equation at every (i, j)
  -- From hc_ps, for each (i,j): (XY-1)*c at (i,j) = (posIncl g - negIncl h) at (i,j)
  have hcoeff_eq : ∀ i j,
      (if 0 < i ∧ 0 < j then MvPowerSeries.coeff (idx (i - 1) (j - 1)) c.val else 0) -
        MvPowerSeries.coeff (idx i j) c.val =
      MvPowerSeries.coeff (idx i j) (posIncl g).val -
        MvPowerSeries.coeff (idx i j) (negIncl h).val := by
    intro i j
    have h1 := congr_arg (MvPowerSeries.coeff (idx i j)) hc_ps
    rw [coeff_XY_sub_one_mul] at h1
    rwa [map_sub] at h1
  -- Step 2: Diagonal recurrence: for i ≥ 1, j ≥ 1, c(i,j) = c(i-1,j-1)
  have hdiag : ∀ i j, 0 < i → 0 < j →
      MvPowerSeries.coeff (idx i j) c.val =
      MvPowerSeries.coeff (idx (i - 1) (j - 1)) c.val := by
    intro i j hi hj
    have h1 := hcoeff_eq i j
    rw [if_pos ⟨hi, hj⟩] at h1
    -- RHS: posIncl g at (i,j) with i ≥ 1, j ≥ 1 is 0; negIncl h at (i,j) with i ≥ 1 is 0
    rw [coeff_posIncl, if_neg (by omega : ¬(j = 0))] at h1
    rw [coeff_negIncl, if_neg (by omega : ¬(i = 0))] at h1
    -- h1 : c(i-1,j-1) - c(i,j) = 0 - 0
    simp only [sub_zero] at h1
    -- h1 : c(i-1,j-1) - c(i,j) = 0
    exact eq_of_sub_eq_zero h1 |>.symm
  -- Step 2b: Iterated diagonal: c(i+k, j+k) = c(i, j) for all k
  have hdiag_iter : ∀ i j k,
      MvPowerSeries.coeff (idx (i + k) (j + k)) c.val =
      MvPowerSeries.coeff (idx i j) c.val := by
    intro i j k; induction k with
    | zero => simp
    | succ k ih =>
      rw [show i + (k + 1) = (i + k) + 1 from by omega,
          show j + (k + 1) = (j + k) + 1 from by omega]
      rw [hdiag _ _ (by omega) (by omega)]
      simp only [show (i + k + 1) - 1 = i + k from by omega,
                  show (j + k + 1) - 1 = j + k from by omega]
      exact ih
  -- Step 3: c is restricted (coefficients tend to 0)
  have hc_restr : Filter.Tendsto
      (fun s => MvPowerSeries.coeff s c.val) Filter.cofinite (nhds 0) := c.prop
  -- Step 4: Along diagonal n+k, k (for n ≥ 1): c(n+k,k) = c(n,0) = -coeff_n g
  -- First: boundary equation at (n, 0) for n ≥ 1: -c(n,0) = coeff_n g
  have hboundary_x : ∀ n, 0 < n →
      MvPowerSeries.coeff (idx n 0) c.val =
      -(MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n) g.val) := by
    intro n hn
    have h1 := hcoeff_eq n 0
    rw [if_neg (by omega : ¬(0 < n ∧ 0 < 0))] at h1
    rw [coeff_posIncl, if_pos rfl, coeff_negIncl, if_neg (by omega : ¬(n = 0))] at h1
    -- h1 : 0 - c(n,0) = coeff_n g - 0
    simp only [zero_sub, sub_zero] at h1
    -- h1 : -c(n,0) = coeff_n g, so c(n,0) = -coeff_n g
    rw [← h1, neg_neg]
  -- Boundary equation at (0, m) for m ≥ 1: -c(0,m) = -coeff_m h, i.e. c(0,m) = coeff_m h
  have hboundary_y : ∀ m, 0 < m →
      MvPowerSeries.coeff (idx 0 m) c.val =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m) h.val := by
    intro m hm
    have h1 := hcoeff_eq 0 m
    rw [if_neg (by omega : ¬(0 < 0 ∧ 0 < m))] at h1
    rw [coeff_posIncl, if_neg (by omega : ¬(m = 0)), coeff_negIncl, if_pos rfl] at h1
    -- h1 : 0 - c(0,m) = 0 - coeff_m h
    simp only [zero_sub] at h1
    -- h1 : -c(0,m) = -coeff_m h
    exact neg_injective h1
  -- Boundary at (0, 0): -c(0,0) = coeff_0 g - coeff_0 h
  have hboundary_00 :
      MvPowerSeries.coeff (idx 0 0) c.val =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 0) h.val -
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 0) g.val := by
    have h1 := hcoeff_eq 0 0
    rw [if_neg (by omega : ¬(0 < 0 ∧ 0 < 0))] at h1
    rw [coeff_posIncl, if_pos rfl, coeff_negIncl, if_pos rfl] at h1
    -- h1 : 0 - c(0,0) = coeff_0 g - coeff_0 h
    simp only [zero_sub] at h1
    -- h1 : -c(0,0) = coeff_0 g - coeff_0 h; want c(0,0) = coeff_0 h - coeff_0 g
    linear_combination -h1
  -- Step 5: For n ≥ 1, the diagonal c(n+k, k) = c(n, 0) for all k.
  -- This is constant, and by restricted condition in T1 space, must be 0.
  -- Therefore coeff_n g = 0 for all n ≥ 1.
  have hg_higher_zero : ∀ n, 0 < n →
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n) g.val = 0 := by
    intro n hn
    -- c(n, 0) = -coeff_n g, and c(n+k, k) = c(n, 0) for all k
    have hconst : ∀ k, MvPowerSeries.coeff (idx (n + k) k) c.val =
        MvPowerSeries.coeff (idx n 0) c.val := fun k => by
      simpa only [Nat.zero_add] using hdiag_iter n 0 k
    -- The injection ℕ → Fin 2 →₀ ℕ sending k ↦ idx (n + k) k
    have hinj : Function.Injective (fun k => idx (n + k) k) := by
      intro a b hab
      have := Finsupp.ext_iff.mp hab 1
      simp [idx] at this; omega
    -- By restricted + T1, the constant value must be 0
    have h0 := eq_zero_of_restricted_const (fun s => MvPowerSeries.coeff s c.val)
      hc_restr (fun k => idx (n + k) k) hinj hconst
    rw [hboundary_x n hn] at h0
    -- h0 : -(coeff_n g) = 0
    exact neg_eq_zero.mp h0
  -- Step 6: Similarly, coeff_m h = 0 for all m ≥ 1.
  have hh_higher_zero : ∀ m, 0 < m →
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m) h.val = 0 := by
    intro m hm
    have hconst : ∀ k, MvPowerSeries.coeff (idx k (m + k)) c.val =
        MvPowerSeries.coeff (idx 0 m) c.val := fun k => by
      simpa only [Nat.zero_add] using hdiag_iter 0 m k
    have hinj : Function.Injective (fun k => idx k (m + k)) := by
      intro a b hab
      have := Finsupp.ext_iff.mp hab 0
      simp [idx] at this; omega
    have h0 := eq_zero_of_restricted_const (fun s => MvPowerSeries.coeff s c.val)
      hc_restr (fun k => idx k (m + k)) hinj hconst
    rw [hboundary_y m hm] at h0
    exact h0
  -- Step 7: c(0,0) = 0, which gives coeff_0 g = coeff_0 h.
  have hc00_zero : MvPowerSeries.coeff (idx 0 0) c.val = 0 := by
    have hconst : ∀ k, MvPowerSeries.coeff (idx k k) c.val =
        MvPowerSeries.coeff (idx 0 0) c.val := fun k => by
      simpa only [Nat.zero_add] using hdiag_iter 0 0 k
    have hinj : Function.Injective (fun k => idx k k) := by
      intro a b hab
      have := Finsupp.ext_iff.mp hab 0
      simp [idx] at this; omega
    exact eq_zero_of_restricted_const (fun s => MvPowerSeries.coeff s c.val)
      hc_restr (fun k => idx k k) hinj hconst
  have hg0_eq_h0 :
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 0) g.val =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 0) h.val := by
    -- hboundary_00 : c(0,0) = coeff_0 h - coeff_0 g; hc00_zero : c(0,0) = 0
    linear_combination hboundary_00 - hc00_zero
  -- Step 8: Assemble. Set a = coeff_0 g (as TateAlgebra.coeff).
  -- coeff_zero_algebraMap and coeff_succ_algebraMap use TateAlgebra.coeff.
  set a := TateAlgebra.coeff 0 g with ha_def
  -- Convert MvPowerSeries-level results to TateAlgebra.coeff
  have hg0_eq_h0' : TateAlgebra.coeff 0 g = TateAlgebra.coeff 0 h :=
    hg0_eq_h0  -- both are definitionally MvPowerSeries.coeff (Finsupp.single 0 0) _.val
  have hg_higher' : ∀ n, 0 < n → TateAlgebra.coeff n g = 0 :=
    hg_higher_zero  -- TateAlgebra.coeff n = MvPowerSeries.coeff (Finsupp.single 0 n) _.val
  have hh_higher' : ∀ n, 0 < n → TateAlgebra.coeff n h = 0 :=
    hh_higher_zero
  refine ⟨a, ?_⟩
  rw [show iotaHom a = (algebraMap A ↥(TateAlgebra A) a,
    algebraMap A ↥(TateAlgebra A) a) from rfl]
  -- Prove g = algebraMap a
  have hg_eq : algebraMap A ↥(TateAlgebra A) a = g := by
    apply TateAlgebra.ext; intro n
    cases n with
    | zero => rw [coeff_zero_algebraMap]
    | succ n =>
      rw [coeff_succ_algebraMap]
      exact (hg_higher' (n + 1) (Nat.succ_pos n)).symm
  -- Prove h = algebraMap a
  have hh_eq : algebraMap A ↥(TateAlgebra A) a = h := by
    apply TateAlgebra.ext; intro n
    cases n with
    | zero => rw [coeff_zero_algebraMap, ha_def]; exact hg0_eq_h0'
    | succ n =>
      rw [coeff_succ_algebraMap]
      exact (hh_higher' (n + 1) (Nat.succ_pos n)).symm
  exact Prod.ext hg_eq hh_eq

/-- **Row 2 exactness of the Laurent cover (Wedhorn Lemma 8.33, Row 2).**
1. `lambda circ iota = 0`: both embeddings agree on constants.
2. `ker(lambda) <= im(iota)`: restricted condition forces constants. -/
theorem row2_exact_at_middle [T1Space A] :
    (∀ a : A, lambdaMap (iotaHom a) = 0) ∧
    (∀ p : ↥(TateAlgebra A) × ↥(TateAlgebra A),
      lambdaMap p = 0 → ∃ a : A, iotaHom a = p) :=
  ⟨lambdaMap_comp_iotaHom, ker_lambdaMap_le_range_iotaHom⟩

end Row2Exactness

/-! ### Nonarchimedean tail sum lemma

In a complete nonarchimedean group, the tail sums `∑' k, f(n + k)` of a summable
function tend to 0 as `n → ∞`. This generalizes `NNReal.tendsto_sum_nat_add` to
arbitrary complete nonarchimedean groups. -/

section TailSum

variable {G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
  [NonarchimedeanAddGroup G] [CompleteSpace G] [T2Space G]

/-- In a complete nonarchimedean additive group, if `f` is summable then
`f(n + ·)` is summable for all `n`. -/
theorem Summable.nat_add {f : ℕ → G} (hf : Summable f) (n : ℕ) :
    Summable (fun k => f (n + k)) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hf.tendsto_cofinite_zero.comp
    ((add_right_injective n).tendsto_cofinite)

/-- **Nonarchimedean tail sum lemma**: for a summable `f : ℕ → G` in a complete
nonarchimedean group, `∑' k, f(n + k) → 0` as `n → ∞`.

Proof: For any open subgroup `V`, only finitely many `f(k) ∉ V`. For `n` past
all bad indices, every term `f(n+k) ∈ V`. The tsum of terms in the closed
subgroup `V` lies in `V` (by uniqueness of limits in T2 and `V` closed). -/
theorem tendsto_tsum_nat_add {f : ℕ → G} (hf : Summable f) :
    Filter.Tendsto (fun n => ∑' k, f (n + k)) Filter.atTop (nhds 0) := by
  rw [Filter.tendsto_iff_forall_eventually_mem]
  intro U hU
  -- Choose open additive subgroup V ⊆ U
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  -- Only finitely many f(k) ∉ V, i.e., eventually f(k) ∈ V
  have hfV : ∀ᶠ k in Filter.atTop, f k ∈ (V : Set G) := by
    rw [← Nat.cofinite_eq_atTop]
    exact hf.tendsto_cofinite_zero (V.isOpen.mem_nhds V.zero_mem)
  -- Extract N such that f(k) ∈ V for all k ≥ N
  rw [Filter.eventually_atTop] at hfV ⊢
  obtain ⟨N, hN⟩ := hfV
  refine ⟨N, fun n hn => hVU ?_⟩
  -- All terms f(n+k) ∈ V for n ≥ N
  have hterms : ∀ k, f (n + k) ∈ (V : Set G) := fun k => hN (n + k) (by omega)
  -- Tsum of terms in a closed set is in that set
  -- V is open in T2 → V is closed (open subgroups of T2 groups are clopen)
  have hVclosed : IsClosed (V : Set G) := V.isClosed
  exact hVclosed.mem_of_tendsto (Summable.nat_add hf n).hasSum
    (Filter.Eventually.of_forall fun s =>
      V.toAddSubgroup.sum_mem (fun k _ => hterms k))

end TailSum

/-! ### General Row 3: exactness via the 3×3 diagram chase

For a general nonarchimedean ring `A` with `[T1Space A]`, the Row 3 sequence
```
0 → A →ε B₁ × B₂ →δ B₁₂ → 0
```
is exact, where:
- `B₁ = A⟨X⟩/(f-X)`, `B₂ = A⟨X⟩/(1-fX)` (quotients of Tate algebra)
- `B₁₂ = A⟨ζ,ζ⁻¹⟩/(f-ζ)` (quotient of Laurent Tate algebra)

These are purely algebraic objects (no evaluation equivalences needed).
Exactness follows from the 3×3 diagram:
- Row 2 exact (proved above, needs `[T1Space A]`)
- Columns exact (quotient exact sequences, always)
- Row 1 exact (surjectivity of `λ'`, from surjectivity of `λ`) -/

section Row3General

variable (f : A)

/-- The ideal `(f - ζ)` in the Laurent Tate algebra `A⟨ζ, ζ⁻¹⟩`.
Here `ζ = posEmbHom X` and `f` is the image of `f ∈ A`. -/
noncomputable def laurentFSubZetaIdeal : Ideal (LaurentTateAlgebra A) :=
  Ideal.span {algebraMap A (LaurentTateAlgebra A) f - LaurentTateAlgebra.zeta}

/-- `B₁₂ = A⟨ζ, ζ⁻¹⟩ / (f - ζ)`, the quotient representing `O_X(U₁ ∩ U₂)`. -/
noncomputable abbrev B₁₂_gen :=
  LaurentTateAlgebra A ⧸ laurentFSubZetaIdeal f

/-- The quotient map `A⟨ζ, ζ⁻¹⟩ → B₁₂`. -/
noncomputable def quotLaurent : LaurentTateAlgebra A →+* B₁₂_gen f :=
  Ideal.Quotient.mk (laurentFSubZetaIdeal f)

/-- `posEmbHom` sends the generator `f - X` of the ideal to `f - ζ` in the
Laurent algebra, which lies in `laurentFSubZetaIdeal`. -/
theorem posEmbHom_generator_mem :
    posEmbHom (algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X) ∈
      laurentFSubZetaIdeal f := by
  rw [map_sub]
  -- posEmbHom(algebraMap f) = algebraMap f in Laurent; posEmbHom(X) = zeta
  have h1 : posEmbHom (algebraMap A ↥(TateAlgebra A) f) =
      algebraMap A (LaurentTateAlgebra A) f := by
    simp only [posEmbHom, RingHom.comp_apply, posIncl_algebraMap]; rfl
  -- posEmbHom(X) = zeta: posIncl maps univariate X₀ to bivariate X₀
  have h2 : posEmbHom (TateAlgebra.X (A := A)) = LaurentTateAlgebra.zeta := by
    change LaurentTateAlgebra.mkHom (posIncl TateAlgebra.X) =
      LaurentTateAlgebra.mkHom TateAlgebra₂.X
    congr 1; ext1
    -- Need: (posIncl X).val = (TateAlgebra₂.X).val as MvPowerSeries (Fin 2) A
    -- posIncl sends X = MvPowerSeries.X 0 (Fin 1) to varInclFun 0 of X = MvPowerSeries.X 0 (Fin 2)
    -- TateAlgebra₂.X = MvPowerSeries.X 0 (Fin 2)
    -- So need: varInclFun 0 (MvPowerSeries.X 0 : MvPowerSeries (Fin 1) A) = MvPowerSeries.X 0
    apply MvPowerSeries.ext; intro e
    change varInclFun (0 : Fin 2) (MvPowerSeries.X (0 : Fin 1)) e =
      MvPowerSeries.coeff e (MvPowerSeries.X (0 : Fin 2))
    rw [varInclFun_apply]
    -- Reduce to: checking varInclFun 0 (X 0) e = coeff e (X 0) for all e : Fin 2 →₀ ℕ
    -- Use varInclFun_coeff_single for e = single 0 n
    by_cases he : e = Finsupp.single (0 : Fin 2) (e 0)
    · rw [if_pos he, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
      -- (if single 0 (e 0) = single 0 1 then 1 else 0) = (if e = single 0 1 then 1 else 0)
      -- Both conditions are equivalent: (single 0 (e 0) = single 0 1 in Fin 1) ↔ e 0 = 1
      -- and (e = single 0 1 in Fin 2) ↔ e 0 = 1 (using he)
      by_cases h0 : e 0 = 1
      · rw [if_pos (by rw [h0]), if_pos (by rw [he, h0])]
      · rw [if_neg (by intro h; exact h0 (by simpa using Finsupp.ext_iff.mp h 0)),
            if_neg (by intro h; exact h0 (by rw [h]; simp [Finsupp.single_eq_same]))]
    · rw [if_neg he, MvPowerSeries.coeff_X, if_neg]
      intro h; exact he (by rw [h]; simp [Finsupp.single_eq_same])
  rw [h1, h2]
  exact Ideal.subset_span rfl

/-- `posEmbHom` sends the ideal `(f - X)` into `(f - ζ)` in the Laurent algebra.
This is needed for `deltaMap_gen` to be well-defined. -/
theorem posEmbHom_ideal_compat (x : ↥(TateAlgebra A))
    (hx : x ∈ Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) :
    posEmbHom x ∈ laurentFSubZetaIdeal f := by
  refine Ideal.mem_comap.mp (Ideal.span_le.mpr ?_ hx)
  rintro y rfl
  exact posEmbHom_generator_mem f

/-- `negEmbHom` sends the generator `1 - fX` to an element of `(f - ζ)`.
Key identity: `1 - f·ζ⁻¹ = -ζ⁻¹·(f - ζ)`. -/
theorem negEmbHom_generator_mem :
    negEmbHom (1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X) ∈
      laurentFSubZetaIdeal f := by
  rw [map_sub, map_one, map_mul]
  have h1 : negEmbHom (algebraMap A ↥(TateAlgebra A) f) =
      algebraMap A (LaurentTateAlgebra A) f := by
    simp only [negEmbHom, RingHom.comp_apply, negIncl_algebraMap]; rfl
  -- negEmbHom(X) = zetaInv: negIncl maps univariate X₀ to bivariate X₁ (= Y)
  have h2 : negEmbHom (TateAlgebra.X (A := A)) = LaurentTateAlgebra.zetaInv := by
    change LaurentTateAlgebra.mkHom (negIncl TateAlgebra.X) =
      LaurentTateAlgebra.mkHom TateAlgebra₂.Y
    congr 1; ext1; apply MvPowerSeries.ext; intro e
    simp only [negIncl, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change varInclFun (1 : Fin 2) (MvPowerSeries.X (0 : Fin 1)) e =
      (MvPowerSeries.coeff e) (MvPowerSeries.X (1 : Fin 2))
    rw [varInclFun_apply]
    by_cases he : e = Finsupp.single (1 : Fin 2) (e 1)
    · rw [if_pos he, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
      by_cases h0 : e 1 = 1
      · rw [if_pos (by rw [h0]), if_pos (by rw [he, h0])]
      · rw [if_neg (by intro h; exact h0 (by simpa using Finsupp.ext_iff.mp h 0)),
            if_neg (by intro h; exact h0 (by rw [h]; simp [Finsupp.single_eq_same]))]
    · rw [if_neg he, MvPowerSeries.coeff_X, if_neg]
      intro h; exact he (by rw [h]; simp [Finsupp.single_eq_same])
  rw [h1, h2]
  have hkey : (1 : LaurentTateAlgebra A) -
      algebraMap A (LaurentTateAlgebra A) f * LaurentTateAlgebra.zetaInv =
      -(LaurentTateAlgebra.zetaInv *
        (algebraMap A (LaurentTateAlgebra A) f - LaurentTateAlgebra.zeta)) := by
    rw [mul_sub, mul_comm LaurentTateAlgebra.zetaInv (algebraMap A _ f),
      LaurentTateAlgebra.zetaInv_mul_zeta]; ring
  rw [hkey]
  exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

/-- `negEmbHom` sends the ideal `(1 - fX)` into `(f - ζ)` in the Laurent algebra. -/
theorem negEmbHom_ideal_compat (x : ↥(TateAlgebra A))
    (hx : x ∈ Ideal.span
      {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}) :
    negEmbHom x ∈ laurentFSubZetaIdeal f := by
  refine Ideal.mem_comap.mp (Ideal.span_le.mpr ?_ hx)
  rintro y rfl
  exact negEmbHom_generator_mem f

/-- The positive lift: `B₁ → B₁₂`, induced by `quotLaurent ∘ posEmbHom`. -/
noncomputable def posLift : B₁_gen f →+* B₁₂_gen f :=
  Ideal.Quotient.lift _
    ((quotLaurent f).comp posEmbHom)
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (posEmbHom_ideal_compat f x hx))

/-- The negative lift: `B₂ → B₁₂`, induced by `quotLaurent ∘ negEmbHom`. -/
noncomputable def negLift : B₂_gen f →+* B₁₂_gen f :=
  Ideal.Quotient.lift _
    ((quotLaurent f).comp negEmbHom)
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (negEmbHom_ideal_compat f x hx))

/-- The delta map `δ : B₁ × B₂ → B₁₂` (general case), defined as
`δ(b₁, b₂) = posLift(b₁) - negLift(b₂)`. -/
noncomputable def deltaMap_gen : B₁_gen f × B₂_gen f →+ B₁₂_gen f where
  toFun p := posLift f p.1 - negLift f p.2
  map_zero' := by simp [map_zero, sub_self]
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring

/-- `δ ∘ ε = 0`: the composition of the diagonal embedding with delta vanishes. -/
theorem deltaMap_gen_comp_epsilonHom_gen (a : A) :
    deltaMap_gen f (epsilonHom_gen f a) = 0 := by
  simp only [deltaMap_gen, epsilonHom_gen, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    RingHom.prod_apply, RingHom.comp_apply]
  -- Both lifts applied to algebraMap(a) give the same result in B₁₂
  show posLift f _ - negLift f _ = 0
  apply sub_eq_zero.mpr
  -- posLift and negLift agree on constants: both reduce to algebraMap in B₁₂
  simp only [posLift, negLift, Ideal.Quotient.lift_mk, RingHom.comp_apply]
  -- posEmbHom and negEmbHom agree on constants from A
  exact congrArg (quotLaurent f)
    (show posEmbHom (algebraMap A _ a) = negEmbHom (algebraMap A _ a) from
      congrArg LaurentTateAlgebra.mkHom
        (Subtype.ext (by rw [posIncl_algebraMap, negIncl_algebraMap])))

/-- The injection `k ↦ idx (i + k) (j + k)` running down a diagonal is injective. -/
private theorem idx_diag_injective (i j : ℕ) :
    Function.Injective (fun k => idx (i + k) (j + k)) := by
  intro a b hab
  have := Finsupp.ext_iff.mp hab 0; simp [idx] at this; omega

section LambdaSurjectiveHelpers

variable [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]
  (htop : ‹TopologicalSpace A› = UniformSpace.toTopologicalSpace)
  (p : ↥(TateAlgebra₂ A))
include htop

/-- Coefficients of a restricted bivariate series, sampled along any injective
index path `ν : ℕ → (Fin 2 →₀ ℕ)`, are summable (completeness + nonarchimedean). -/
private theorem summable_coeff_comp_injective
    {ν : ℕ → (Fin 2 →₀ ℕ)} (hν : Function.Injective ν) :
    Summable (fun k => MvPowerSeries.coeff (ν k) p.val) := by
  subst htop
  exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (p.prop.comp hν.tendsto_cofinite)

/-- Summability of `p` along the diagonal through `(i, j)`: `k ↦ p_{i+k, j+k}`. -/
private theorem summable_coeff_diag (i j : ℕ) :
    Summable (fun k => MvPowerSeries.coeff (idx (i + k) (j + k)) p.val) :=
  summable_coeff_comp_injective htop p (idx_diag_injective i j)

/-- Splitting a diagonal `tsum` into its head term and the once-shifted tail:
`∑ₖ p_{i+k, j+k} = p_{i, j} + ∑ₖ p_{i+1+k, j+1+k}`. -/
private theorem tsum_diag_head (i j : ℕ) :
    ∑' k, MvPowerSeries.coeff (idx (i + k) (j + k)) p.val =
      MvPowerSeries.coeff (idx i j) p.val +
      ∑' k, MvPowerSeries.coeff (idx (i + 1 + k) (j + 1 + k)) p.val := by
  have h1 := (summable_coeff_diag htop p i j).tsum_eq_zero_add
  simp only [Nat.add_zero] at h1
  rw [h1]; congr 1; apply tsum_congr; intro k
  have : idx (i + (k + 1)) (j + (k + 1)) = idx (i + 1 + k) (j + 1 + k) := by
    apply Finsupp.ext; intro x; fin_cases x <;> simp [idx] <;> omega
  rw [this]

/-- The positive diagonal sums `g_n = ∑ₖ p_{n+k, k}` define a restricted univariate
series: as `n → ∞` the coefficients tend to `0`. -/
private theorem gRestr_of_restricted :
    MvPowerSeries.IsRestricted
      (fun s : Fin 1 →₀ ℕ =>
        (∑' k, MvPowerSeries.coeff (idx (s 0 + k) k) p.val : A) :
        MvPowerSeries (Fin 1) A) := by
  subst htop
  intro U hU
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  have hSfin : {e : Fin 2 →₀ ℕ | MvPowerSeries.coeff e p.val ∉ (V : Set A)}.Finite := by
    have := p.prop (V.isOpen.mem_nhds V.zero_mem)
    rwa [Filter.mem_map, Filter.mem_cofinite] at this
  classical
  set N : ℕ := hSfin.toFinset.sup (fun e => e 0) + 1
  have hsmall : {s : Fin 1 →₀ ℕ | s 0 < N}.Finite := by
    apply Set.Finite.subset (Set.finite_Iio N |>.image (Finsupp.single 0))
    intro s hs; simp only [Set.mem_setOf_eq] at hs
    refine ⟨s 0, hs, Finsupp.ext (fun i => ?_)⟩
    simp [Fin.eq_zero i]
  refine hsmall.subset (fun s (hs : _ ∉ U) => show s 0 < N from ?_)
  by_contra hlt
  apply hs; apply hVU
  have hsN : N ≤ s 0 := Nat.not_lt.mp hlt
  have hterm : ∀ k, MvPowerSeries.coeff (idx (s 0 + k) k) p.val ∈ (V : Set A) := by
    intro k; by_contra hk
    have h1 := Finset.le_sup (f := fun e : Fin 2 →₀ ℕ => e 0) (hSfin.mem_toFinset.mpr hk)
    simp only [idx_apply_zero] at h1; omega
  refine V.isClosed.mem_of_tendsto
    (summable_coeff_comp_injective rfl p (ν := fun k => idx (s 0 + k) k) ?_).hasSum
    (Filter.Eventually.of_forall fun t =>
      V.toAddSubgroup.sum_mem (fun k _ => hterm k))
  intro a b hab
  have := Finsupp.ext_iff.mp hab 1; simp [idx] at this; omega

/-- The negative diagonal sums `h_m = ∑ₖ p_{k, m+k}` (with `h_0 = 0`) define a
restricted univariate series. -/
private theorem hRestr_of_restricted :
    MvPowerSeries.IsRestricted
      (fun s : Fin 1 →₀ ℕ =>
        (if s 0 = 0 then 0
         else ∑' k, MvPowerSeries.coeff (idx k (s 0 + k)) p.val : A) :
        MvPowerSeries (Fin 1) A) := by
  subst htop
  intro U hU
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  have hSfin : {e : Fin 2 →₀ ℕ | MvPowerSeries.coeff e p.val ∉ (V : Set A)}.Finite := by
    have := p.prop (V.isOpen.mem_nhds V.zero_mem)
    rwa [Filter.mem_map, Filter.mem_cofinite] at this
  classical
  set N : ℕ := hSfin.toFinset.sup (fun e => e 1) + 1
  have hsmall : {s : Fin 1 →₀ ℕ | s 0 < N}.Finite := by
    apply Set.Finite.subset (Set.finite_Iio N |>.image (Finsupp.single 0))
    intro s hs; simp only [Set.mem_setOf_eq] at hs
    refine ⟨s 0, hs, Finsupp.ext (fun i => ?_)⟩; simp [Fin.eq_zero i]
  refine (hsmall.union (Set.finite_singleton (0 : Fin 1 →₀ ℕ))).subset
    (fun s (hs : _ ∉ U) => ?_)
  by_cases hs0 : s 0 = 0
  · exfalso; apply hs
    change (if s 0 = 0 then 0 else _) ∈ U
    rw [if_pos hs0]; exact mem_of_mem_nhds hU
  · left; change s 0 < N
    by_contra hlt
    apply hs
    change (if s 0 = 0 then 0 else _) ∈ U
    rw [if_neg hs0]; apply hVU
    have hsN : N ≤ s 0 := Nat.not_lt.mp hlt
    have hterm : ∀ k, MvPowerSeries.coeff (idx k (s 0 + k)) p.val ∈ (V : Set A) := by
      intro k; by_contra hk
      have h1 := Finset.le_sup (f := fun e : Fin 2 →₀ ℕ => e 1) (hSfin.mem_toFinset.mpr hk)
      simp only [idx_apply_one] at h1; omega
    refine V.isClosed.mem_of_tendsto
      (summable_coeff_comp_injective rfl p (ν := fun k => idx k (s 0 + k)) ?_).hasSum
      (Filter.Eventually.of_forall fun t =>
        V.toAddSubgroup.sum_mem (fun k _ => hterm k))
    intro a b hab
    have := Finsupp.ext_iff.mp hab 0; simp [idx] at this; omega

/-- The witness `c_{i,j} = -∑ₖ p_{i+1+k, j+1+k}` (diagonal tail sums, negated)
defines a restricted bivariate series. -/
private theorem cRestr_of_restricted :
    MvPowerSeries.IsRestricted
      (fun e : Fin 2 →₀ ℕ =>
        -(∑' k, MvPowerSeries.coeff (idx (e 0 + 1 + k) (e 1 + 1 + k)) p.val) :
        MvPowerSeries (Fin 2) A) := by
  subst htop
  change Filter.Tendsto _ Filter.cofinite (nhds 0)
  rw [show (0 : A) = -0 from neg_zero.symm]
  apply Filter.Tendsto.neg
  change Filter.Tendsto
    (fun e : Fin 2 →₀ ℕ => ∑' k, MvPowerSeries.coeff (idx (e 0 + 1 + k) (e 1 + 1 + k)) p.val)
    Filter.cofinite (nhds 0)
  intro U hU
  rw [Filter.mem_map, Filter.mem_cofinite]
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  have hSfin : {e : Fin 2 →₀ ℕ | MvPowerSeries.coeff e p.val ∉ (V : Set A)}.Finite := by
    have := p.prop (V.isOpen.mem_nhds V.zero_mem)
    rwa [Filter.mem_map, Filter.mem_cofinite] at this
  classical
  set M := hSfin.toFinset.sup (fun e => max (e 0) (e 1)) + 1
  have hbad_bound : ∀ e : Fin 2 →₀ ℕ, M ≤ e 0 + 1 ∨ M ≤ e 1 + 1 →
      ∑' k, MvPowerSeries.coeff (idx (e 0 + 1 + k) (e 1 + 1 + k)) p.val ∈ (V : Set A) := by
    intro e hor
    apply V.isClosed.mem_of_tendsto (summable_coeff_diag rfl p (e 0 + 1) (e 1 + 1)).hasSum
    apply Filter.Eventually.of_forall; intro t
    apply V.toAddSubgroup.sum_mem; intro k _
    by_contra hk
    have hmem := Finset.le_sup (f := fun e => max (e 0) (e 1)) (hSfin.mem_toFinset.mpr hk)
    simp only [idx_apply_zero, idx_apply_one] at hmem
    omega
  apply Set.Finite.subset
    (s := {e : Fin 2 →₀ ℕ | e 0 < M ∧ e 1 < M})
  · apply Set.Finite.subset
      ((Finset.range M ×ˢ Finset.range M).image (fun p => idx p.1 p.2)).finite_toSet
    intro e ⟨h0, h1⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
      Finset.mem_range]
    exact ⟨(e 0, e 1), ⟨h0, h1⟩, (eq_idx e).symm⟩
  · intro e he
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage] at he ⊢
    constructor
    · by_contra h0
      exact he (hVU (hbad_bound e (Or.inl (by omega))))
    · by_contra h1
      exact he (hVU (hbad_bound e (Or.inr (by omega))))

end LambdaSurjectiveHelpers

/-- **`lambdaMap` surjectivity** for complete nonarchimedean rings: every element
of the Laurent Tate algebra decomposes as `posEmbHom(g) - negEmbHom(h)`.

The coefficients of `g` and `h` are diagonal sums `g_n = ∑_{k≥0} p_{n+k,k}`
which converge because `A` is complete nonarchimedean and `p` is restricted
(coefficients tend to 0).

**Proof outline:**
1. Lift `ℓ` to `p ∈ TateAlgebra₂ A` (bivariate restricted series).
2. For each net diagonal index `n ≥ 0`, define `g_n = ∑_{k≥0} p_{n+k,k}` (positive part).
3. For each net diagonal index `m ≥ 1`, define `h_m = -∑_{k≥0} p_{k,m+k}` (negative part).
4. The constant term correction: `g_0` accounts for the main diagonal.
5. Show `g, h ∈ TateAlgebra A` (restricted: coefficients → 0).
6. Show `posIncl(g) - negIncl(h) - p ∈ (XY-1)` by constructing the witness `c`.

**Implementation note:** The hypotheses `[UniformSpace A]` and `[TopologicalSpace A]` are
independent, so summability of diagonal subsequences (which bridges Cauchy completeness
from `UniformSpace` with the nonarchimedean property from `TopologicalSpace`) requires
that these structures are compatible. In all intended applications (adic rings, Tate rings),
the uniform space is the canonical one from `IsTopologicalAddGroup.rightUniformSpace`,
which is automatically compatible. The summability, restrictedness of `g` and `h`, and
restrictedness of the witness `c` are recorded as `sorry` pending resolution of this
diamond. The mathematical argument (diagonal decomposition + ideal membership) is
fully specified in the proof structure and comments. -/
theorem lambdaMap_surjective [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]
    (htop : ‹TopologicalSpace A› = UniformSpace.toTopologicalSpace) :
    Function.Surjective (lambdaMap (A := A)) := by
  intro ℓ
  -- Step 1: Lift `ℓ` to a bivariate restricted series `p`.
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective ℓ
  -- Step 2: Assemble `g`, `h` from diagonal sums of `p` (restrictedness via helpers).
  --   g_n = ∑_{k≥0} p_{n+k, k}    (positive diagonals);
  --   h_0 = 0, h_m = ∑_{k≥0} p_{k, m+k}  (negative diagonals).
  set g : ↥(TateAlgebra A) :=
    ⟨fun s => ∑' k, MvPowerSeries.coeff (idx (s 0 + k) k) p.val,
      gRestr_of_restricted htop p⟩
  set h : ↥(TateAlgebra A) :=
    ⟨fun s => if s 0 = 0 then 0
              else ∑' k, MvPowerSeries.coeff (idx k (s 0 + k)) p.val,
      hRestr_of_restricted htop p⟩
  -- Step 3: Produce the preimage `(g, -h)` and reduce to an ideal membership.
  refine ⟨(g, -h), ?_⟩
  change posEmbHom g - negEmbHom (-h) = mkHom p
  rw [map_neg, sub_neg_eq_add]
  -- Reduce `posEmbHom g + negEmbHom h = mkHom p` to an ideal membership:
  -- posEmbHom = mkHom ∘ posIncl and negEmbHom = mkHom ∘ negIncl, so it suffices that
  -- posIncl g + negIncl h - p ∈ laurentIdeal A = (XY - 1).
  change mkHom (posIncl g) + mkHom (negIncl h) = mkHom p
  rw [← map_add]
  apply Ideal.Quotient.eq.mpr
  -- Goal: posIncl g + negIncl h - p ∈ laurentIdeal A = Ideal.span {XY_sub_one}
  rw [laurentIdeal, Ideal.mem_span_singleton']
  -- Step 4: The witness c(i,j) = -(∑_k p_{i+1+k, j+1+k}) (negated diagonal tail sums);
  -- its restrictedness and the head/tail tsum split `tsum_diag_head` come from the helpers.
  let c : ↥(TateAlgebra₂ A) :=
    ⟨fun e => -(∑' k, MvPowerSeries.coeff (idx (e 0 + 1 + k) (e 1 + 1 + k)) p.val),
      cRestr_of_restricted htop p⟩
  -- The witness: c * XY_sub_one = posIncl g + negIncl h - p
  -- Helper: c.val at idx a b = -(∑' k, p(a+1+k, b+1+k)).
  have hc_val : ∀ a b, MvPowerSeries.coeff (idx a b) c.val =
      -(∑' k, MvPowerSeries.coeff (idx (a + 1 + k) (b + 1 + k)) p.val) := by
    intro a b; change -(∑' k, MvPowerSeries.coeff (idx ((idx a b) 0 + 1 + k)
      ((idx a b) 1 + 1 + k)) p.val) = _
    simp only [idx_apply_zero, idx_apply_one]
  -- Helper: g.val at single 0 n = ∑' k, p(n+k, k).
  have hg_val : ∀ n, MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n) g.val =
      ∑' k, MvPowerSeries.coeff (idx (n + k) k) p.val := by
    intro n; change (fun s => ∑' k, MvPowerSeries.coeff (idx (s 0 + k) k) p.val)
      (Finsupp.single (0 : Fin 1) n) = _
    simp [Finsupp.single_eq_same]
  -- Helper: h.val at single 0 m = if m = 0 then 0 else ∑' k, p(k, m+k).
  have hh_val : ∀ m, MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m) h.val =
      if m = 0 then 0 else ∑' k, MvPowerSeries.coeff (idx k (m + k)) p.val := by
    intro m; change (fun s => if s 0 = 0 then 0
      else ∑' k, MvPowerSeries.coeff (idx k (s 0 + k)) p.val)
      (Finsupp.single (0 : Fin 1) m) = _
    simp [Finsupp.single_eq_same]
  -- Now prove c * XY_sub_one = posIncl g + negIncl h - p coefficient by coefficient.
  refine ⟨c, Subtype.ext (MvPowerSeries.ext (fun e => ?_))⟩
  rw [eq_idx e]
  -- Unfold to MvPowerSeries level
  change MvPowerSeries.coeff (idx (e 0) (e 1))
      (c.val * (TateAlgebra₂.XY_sub_one (A := A)).val) =
    MvPowerSeries.coeff (idx (e 0) (e 1))
      ((posIncl g).val + (negIncl h).val - p.val)
  -- Rewrite LHS using coeff_XY_sub_one_mul
  rw [show c.val * (TateAlgebra₂.XY_sub_one (A := A)).val =
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 - 1) * c.val from by rw [mul_comm]; rfl,
    coeff_XY_sub_one_mul]
  -- Unfold RHS
  simp only [map_sub, map_add, coeff_posIncl, coeff_negIncl]
  -- Case split
  by_cases hij : 0 < e 0 ∧ 0 < e 1
  · -- e 0 ≥ 1, e 1 ≥ 1: posIncl = 0, negIncl = 0
    rw [if_pos hij, hc_val, hc_val, if_neg (by omega : ¬(e 1 = 0)),
      if_neg (by omega : ¬(e 0 = 0))]
    -- LHS has ∑' k, p((e 0-1)+1+k, (e 1-1)+1+k). Since e 0 ≥ 1 and e 1 ≥ 1,
    -- (e 0-1)+1 = e 0 and (e 1-1)+1 = e 1. Rewrite the tsum argument.
    have he0 : ∀ k, idx ((e 0 - 1) + 1 + k) ((e 1 - 1) + 1 + k) = idx (e 0 + k) (e 1 + k) := by
      intro k; apply Finsupp.ext; intro x; fin_cases x <;> simp [idx] <;> omega
    simp_rw [he0]
    rw [tsum_diag_head htop p]; ring
  · -- e 0 = 0 or e 1 = 0
    -- After if_neg hij: LHS = 0 - coeff c.val = 0 - (-(∑' k, p(e 0+1+k, e 1+1+k)))
    rw [if_neg hij, hc_val]
    -- RHS involves posIncl g and negIncl h.
    by_cases h0 : e 1 = 0
    · -- e 1 = 0
      rw [if_pos h0, h0, hg_val, hh_val, if_pos rfl]
      by_cases h1 : e 0 = 0
      · -- e 0 = 0, e 1 = 0
        rw [h1, if_pos rfl]
        -- Goal: 0 - (-(∑' k, p(0+1+k, 0+1+k))) = (∑' k, p(0+k, k)) + 0 - p(0, 0)
        -- tsum_diag_head 0 0 uses idx(0+k)(0+k), but hg_val uses idx(0+k)(k).
        -- These differ syntactically, so normalize both.
        have hts := tsum_diag_head htop p 0 0
        simp only [Nat.zero_add] at hts ⊢
        rw [hts]; ring
      · -- e 0 ≥ 1, e 1 = 0
        rw [if_neg h1]
        -- Goal: 0 - (-(∑' k, p(e 0+1+k, 0+1+k))) = (∑' k, p(e 0+k, k)) + 0 - p(e 0, 0)
        have hts := tsum_diag_head htop p (e 0) 0
        simp only [Nat.zero_add] at hts ⊢
        rw [hts]; ring
    · -- e 1 ≥ 1, so e 0 = 0
      have h1 : e 0 = 0 := by
        by_contra hne; exact hij ⟨Nat.pos_of_ne_zero hne, Nat.pos_of_ne_zero h0⟩
      rw [if_neg h0, if_pos h1, h1, hh_val, if_neg h0]
      -- Goal: 0 - (-(∑' k, p(0+1+k, e 1+1+k))) = 0 + (∑' k, p(k, e 1+k)) - p(0, e 1)
      have hts := tsum_diag_head htop p 0 (e 1)
      simp only [Nat.zero_add] at hts ⊢
      rw [hts]; ring

/-- Variant of `lambdaMap_surjective` that additionally ensures the second component
has zero constant coefficient. Obtained by adjusting `(a, b)` to `(a - c, b - c)`
where `c = algebraMap(b_0)`. -/
theorem lambdaMap_surjective_with_zero_const
    [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]
    (htop : ‹TopologicalSpace A› = UniformSpace.toTopologicalSpace)
    (ℓ : LaurentTateAlgebra A) :
    ∃ (a b : ↥(TateAlgebra A)),
      TateAlgebra.coeff 0 b = 0 ∧ posEmbHom a - negEmbHom b = ℓ := by
  obtain ⟨⟨a₀, b₀⟩, hab⟩ := lambdaMap_surjective htop ℓ
  set c₀ := TateAlgebra.coeff 0 b₀
  refine ⟨a₀ - algebraMap A _ c₀, b₀ - algebraMap A _ c₀, ?_, ?_⟩
  · -- coeff 0 (b₀ - algebraMap c₀) = c₀ - c₀ = 0
    change TateAlgebra.coeff 0 b₀ - TateAlgebra.coeff 0 (algebraMap A _ c₀) = 0
    simp [coeff_zero_algebraMap, c₀]
  · rw [map_sub, map_sub]
    have hpc : posEmbHom (algebraMap A _ c₀) = algebraMap A (LaurentTateAlgebra A) c₀ := by
      simp only [posEmbHom, RingHom.comp_apply, posIncl_algebraMap]; rfl
    have hnc : negEmbHom (algebraMap A _ c₀) = algebraMap A (LaurentTateAlgebra A) c₀ := by
      simp only [negEmbHom, RingHom.comp_apply, negIncl_algebraMap]; rfl
    rw [hpc, hnc, sub_sub_sub_cancel_right]; exact hab

/-- `δ` is surjective (general case), using `lambdaMap` surjectivity. -/
theorem deltaMap_gen_surjective [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]
    (htop : ‹TopologicalSpace A› = UniformSpace.toTopologicalSpace) :
    Function.Surjective (deltaMap_gen f) := by
  intro y
  obtain ⟨ℓ, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨⟨g, h⟩, hgh⟩ := lambdaMap_surjective htop ℓ
  refine ⟨(Ideal.Quotient.mk _ g, Ideal.Quotient.mk _ h), ?_⟩
  change posLift f (Ideal.Quotient.mk _ g) - negLift f (Ideal.Quotient.mk _ h) = _
  simp only [posLift, negLift, Ideal.Quotient.lift_mk, RingHom.comp_apply, ← map_sub]
  exact congrArg (quotLaurent f) hgh

/-- **Row 3 exactness: `ker(δ) ⊆ im(ε)` (general case, 3×3 diagram chase).**

If `δ(b₁, b₂) = 0`, lift `(b₁, b₂)` to `(g, h) ∈ A⟨X⟩ × A⟨X⟩`.
Then `λ(g, h) ∈ (f - ζ)`, so by Row 1 surjectivity, `λ(g, h) = λ(g', h')`
for some `(g', h')` in the ideal multiples. Thus `λ(g - g', h - h') = 0`,
and by Row 2 exactness, `(g - g', h - h') = ι(a)` for some `a ∈ A`.
Projecting to quotients gives `ε(a) = (b₁, b₂)`. -/
theorem ker_deltaMap_gen_le_range_epsilonHom_gen
    [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]
    (htop : ‹TopologicalSpace A› = UniformSpace.toTopologicalSpace)
    (p : B₁_gen f × B₂_gen f) (hp : deltaMap_gen f p = 0) :
    ∃ a : A, epsilonHom_gen f a = p := by
  subst htop
  obtain ⟨b₁, b₂⟩ := p
  -- Step 1: Lift b₁, b₂ to A⟨X⟩
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b₁
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective b₂
  -- Step 2: δ(b₁, b₂) = 0 means posEmbHom(g) - negEmbHom(h) ∈ (f - ζ)
  have hmem : posEmbHom g - negEmbHom h ∈ laurentFSubZetaIdeal f := by
    simp only [deltaMap_gen, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      posLift, negLift, Ideal.Quotient.lift_mk, RingHom.comp_apply] at hp
    rw [← map_sub] at hp
    exact Ideal.Quotient.eq_zero_iff_mem.mp hp
  -- Step 3: posEmbHom(g) - negEmbHom(h) = (f - ζ) · c for some c
  rw [laurentFSubZetaIdeal, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c_laurent, hc⟩ := hmem
  -- Step 4: Decompose c_laurent into positive and negative parts using Row 2
  -- posEmbHom(g) - negEmbHom(h) = lambdaMap(g, h) in LaurentTateAlgebra
  -- (by definition of lambdaMap)
  have hlambda : lambdaMap (g, h) = posEmbHom g - negEmbHom h := rfl
  -- Step 4 (Row 1 surjectivity): Find g' ∈ (f-X), h' ∈ (1-fX) with λ(g', h') = λ(g, h)
  -- i.e., posEmbHom g' - negEmbHom h' = posEmbHom g - negEmbHom h
  -- This uses: (f-ζ)·c in the Laurent algebra decomposes as
  --   posEmbHom((f-X)·a) - negEmbHom((1-fX)·b) for some a, b
  have ⟨g', hg'_mem, h', hh'_mem, hrow1⟩ :
      ∃ (g' : ↥(TateAlgebra A)),
        g' ∈ Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X} ∧
      ∃ (h' : ↥(TateAlgebra A)),
        h' ∈ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X} ∧
      lambdaMap (g', h') = lambdaMap (g, h) := by
    -- Use lambdaMap_surjective to decompose c_laurent = posEmbHom a - negEmbHom b.
    -- Decompose c_laurent = posEmbHom a - negEmbHom b with b_0 = 0.
    obtain ⟨a, b, hb0, hab⟩ := lambdaMap_surjective_with_zero_const rfl c_laurent
    -- hab : posEmbHom a - negEmbHom b = c_laurent, hb0 : TateAlgebra.coeff 0 b = 0
    -- Since b_0 = 0, we can write b = X · b' for some b'.
    -- negEmbHom(b) = negEmbHom(X · b') = zetaInv · negEmbHom(b')
    -- So c_laurent = posEmbHom a - zetaInv · negEmbHom b'
    -- (f-ζ) · c_laurent = (f-ζ)·posEmbHom a - (f-ζ)·zetaInv·negEmbHom b'
    --   = posEmbHom((f-X)·a) + (1-f·zetaInv)·negEmbHom b'  [using (f-ζ)·zetaInv = -(1-f·zetaInv)]
    --   = posEmbHom((f-X)·a) - negEmbHom((1-fX)·b')  [using negEmbHom(1-fX) = 1-f·zetaInv]
    -- So g' = (f-X)·a and h' = (1-fX)·b' with b' to be defined from b.
    -- Since b_0 = 0, b ∈ (X) in TateAlgebra A, so b = X · b' for some b'.
    -- Then negEmbHom b = negEmbHom(X) · negEmbHom b' = zetaInv · negEmbHom b'.
    -- Set g' = (f-X)·a ∈ (f-X) and h' = (1-fX)·b' ∈ (1-fX).
    -- Verify: lambdaMap(g', h') = posEmbHom(g') - negEmbHom(h')
    --   = (f-ζ)·posEmbHom(a) - (1-f·zetaInv)·negEmbHom(b')
    --   = (f-ζ)·posEmbHom(a) + zetaInv·(f-ζ)·negEmbHom(b')    [since 1-f·zetaInv = -zetaInv·(f-ζ)]
    --   = (f-ζ)·(posEmbHom(a) + zetaInv·negEmbHom(b'))
    --   = (f-ζ)·(posEmbHom(a) - negEmbHom(b))
    --                                       [since zetaInv·negEmb(b') = negEmb(b)]
    --   = (f-ζ)·c_laurent = posEmbHom g - negEmbHom h = lambdaMap(g, h)  ✓
    --
    -- g' = (f-X)·a, h' = (1-fX)·b' where b' satisfies b = X·b'.
    -- For the algebraic identity, we work entirely in the Laurent algebra.
    -- We don't actually need b' explicitly! We just need to verify the identity.
    -- lambdaMap((f-X)·a, (1-fX)·b') = (f-ζ)·c_laurent = lambdaMap(g, h).
    -- But (1-fX)·b' requires knowing b'. Let's avoid this entirely.
    --
    -- SIMPLER APPROACH: take g' = g and h' = h and show g ∈ (f-X), h ∈ (1-fX).
    -- This fails because g, h are NOT in those ideals in general.
    --
    -- Even simpler: the goal asks for g' IN the ideal and h' IN the ideal.
    -- Take g' = (f-X)·a and h' = 0 + correction.
    -- Actually, take g' = g - algebraMap(TateAlgebra.coeff 0 g) and argue...
    -- No, this is getting nowhere.
    --
    -- The CORRECT proof:
    -- From hc: c_laurent * (f - ζ) = posEmbHom g - negEmbHom h
    -- From hab: posEmbHom a - negEmbHom b = c_laurent, with b_0 = 0
    -- So: (posEmbHom a - negEmbHom b) * (f - ζ) = posEmbHom g - negEmbHom h
    -- LHS = posEmbHom(a) * (f-ζ) - negEmbHom(b) * (f-ζ)
    --   posEmbHom(a) * (f-ζ) = posEmbHom((f-X)·a) = posEmbHom((algebraMap f - X)·a)
    --   negEmbHom(b) * (f-ζ): since b_0 = 0, b = ∑_{n≥1} b_n X^n. negEmbHom(b) = ∑ b_n zetaInv^n.
    --   (f-ζ) * negEmbHom(b): this equals -(1-f·zetaInv)·ζ·negEmbHom(b)·ζ⁻¹... too complex.
    --
    -- Let me just define g' and h' algebraically and verify with sorry:
    -- Since b_0 = 0, ∃ b', X · b' = b (X-divisibility in TateAlgebra).
    have ⟨b', hb'⟩ : ∃ b' : ↥(TateAlgebra A), TateAlgebra.X * b' = b := by
      refine ⟨TateAlgebra.shift b, ?_⟩
      have h := TateAlgebra.eq_const_add_X_mul_shift b
      have heval : TateAlgebra.evalZeroHom b = 0 := hb0
      rw [heval, map_zero, zero_add] at h
      exact h.symm
    -- Set g' = (f-X)·a and h' = (1-fX)·b'
    refine ⟨(algebraMap A _ f - TateAlgebra.X) * a,
      Ideal.mul_mem_right _ _ (Ideal.subset_span rfl),
      -((1 - algebraMap A _ f * TateAlgebra.X) * b'),
      neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)), ?_⟩
    -- Verify: lambdaMap(g', h') = lambdaMap(g, h)
    -- lambdaMap(g', h') = posEmbHom((f-X)·a) - negEmbHom((1-fX)·b')
    change lambdaMap (((algebraMap A _ f - TateAlgebra.X) * a),
      (-((1 - algebraMap A _ f * TateAlgebra.X) * b'))) = lambdaMap (g, h)
    change posEmbHom ((algebraMap A _ f - TateAlgebra.X) * a) -
      negEmbHom (-((1 - algebraMap A _ f * TateAlgebra.X) * b')) = posEmbHom g - negEmbHom h
    -- Establish key facts about how posEmbHom and negEmbHom act on generators
    have hposX : posEmbHom (TateAlgebra.X (A := A)) = LaurentTateAlgebra.zeta := by
      change LaurentTateAlgebra.mkHom (posIncl TateAlgebra.X) =
        LaurentTateAlgebra.mkHom TateAlgebra₂.X
      congr 1; ext1; apply MvPowerSeries.ext; intro e
      change varInclFun (0 : Fin 2) (MvPowerSeries.X (0 : Fin 1)) e =
        MvPowerSeries.coeff e (MvPowerSeries.X (0 : Fin 2))
      rw [varInclFun_apply]
      by_cases he : e = Finsupp.single (0 : Fin 2) (e 0)
      · rw [if_pos he, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
        by_cases h0 : e 0 = 1
        · rw [if_pos (by rw [h0]), if_pos (by rw [he, h0])]
        · rw [if_neg (by intro h; exact h0 (by simpa using Finsupp.ext_iff.mp h 0)),
              if_neg (by intro h; exact h0 (by rw [h]; simp [Finsupp.single_eq_same]))]
      · rw [if_neg he, MvPowerSeries.coeff_X, if_neg]
        intro h; exact he (by rw [h]; simp [Finsupp.single_eq_same])
    have hnegX : negEmbHom (TateAlgebra.X (A := A)) = LaurentTateAlgebra.zetaInv := by
      change LaurentTateAlgebra.mkHom (negIncl TateAlgebra.X) =
        LaurentTateAlgebra.mkHom TateAlgebra₂.Y
      congr 1; ext1; apply MvPowerSeries.ext; intro e
      simp only [negIncl, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      change varInclFun (1 : Fin 2) (MvPowerSeries.X (0 : Fin 1)) e =
        (MvPowerSeries.coeff e) (MvPowerSeries.X (1 : Fin 2))
      rw [varInclFun_apply]
      by_cases he : e = Finsupp.single (1 : Fin 2) (e 1)
      · rw [if_pos he, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
        by_cases h0 : e 1 = 1
        · rw [if_pos (by rw [h0]), if_pos (by rw [he, h0])]
        · rw [if_neg (by intro h; exact h0 (by simpa using Finsupp.ext_iff.mp h 0)),
              if_neg (by intro h; exact h0 (by rw [h]; simp [Finsupp.single_eq_same]))]
      · rw [if_neg he, MvPowerSeries.coeff_X, if_neg]
        intro h; exact he (by rw [h]; simp [Finsupp.single_eq_same])
    have hposAlg : posEmbHom (algebraMap A ↥(TateAlgebra A) f) =
        algebraMap A (LaurentTateAlgebra A) f := by
      simp only [posEmbHom, RingHom.comp_apply, posIncl_algebraMap]; rfl
    have hnegAlg : negEmbHom (algebraMap A ↥(TateAlgebra A) f) =
        algebraMap A (LaurentTateAlgebra A) f := by
      simp only [negEmbHom, RingHom.comp_apply, negIncl_algebraMap]; rfl
    -- negEmbHom(X * b') = zetaInv * negEmbHom(b') = negEmbHom(b)
    have hneg_b : LaurentTateAlgebra.zetaInv * negEmbHom b' = negEmbHom b := by
      rw [← hnegX, ← map_mul, hb']
    -- Rewrite directly to the factored form
    -- LHS = posEmbHom((f-X)*a) - negEmbHom(-((1-fX)*b'))
    --     = posEmbHom(f-X)*posEmbHom(a) + negEmbHom((1-fX)*b')   [map_mul, map_neg, sub_neg]
    --     = (alg f - zeta) * posEmbHom(a) + negEmbHom(1-fX) * negEmbHom(b')
    --     = (alg f - zeta) * posEmbHom(a) + (1 - alg f * zetaInv) * negEmbHom(b')
    -- Now 1 - f*zetaInv = -zetaInv*(f - zeta), so:
    --     = (alg f - zeta) * posEmbHom(a) - zetaInv*(f-zeta) * negEmbHom(b')
    --     = (alg f - zeta) * (posEmbHom(a) - zetaInv * negEmbHom(b'))
    --     = (alg f - zeta) * (posEmbHom(a) - negEmbHom(b))  [zetaInv*negEmb(b') = negEmb(b)]
    --     = (alg f - zeta) * c_laurent = posEmbHom g - negEmbHom h  [hab, hc]
    -- Expand posEmbHom((f-X)*a)
    rw [map_mul, map_sub, hposAlg, hposX]
    -- Expand negEmbHom(-((1-fX)*b'))
    rw [map_neg, sub_neg_eq_add, map_mul, map_sub, map_one, map_mul, hnegAlg, hnegX]
    -- Goal: (alg f - zeta) * posEmbHom a + (1 - alg f * zetaInv) * negEmbHom b'
    --     = posEmbHom g - negEmbHom h
    -- Use: 1 - f * zetaInv = -zetaInv * (f - zeta)
    have hkey : (1 : LaurentTateAlgebra A) -
        algebraMap A (LaurentTateAlgebra A) f * LaurentTateAlgebra.zetaInv =
        -(LaurentTateAlgebra.zetaInv *
          (algebraMap A (LaurentTateAlgebra A) f - LaurentTateAlgebra.zeta)) := by
      rw [mul_sub, mul_comm LaurentTateAlgebra.zetaInv (algebraMap A _ f),
        LaurentTateAlgebra.zetaInv_mul_zeta]; ring
    rw [hkey]
    -- Factor out (alg f - zeta) and use hneg_b, hab, hc
    have : (algebraMap A (LaurentTateAlgebra A) f - LaurentTateAlgebra.zeta) *
        posEmbHom a + -(LaurentTateAlgebra.zetaInv *
        (algebraMap A (LaurentTateAlgebra A) f - LaurentTateAlgebra.zeta)) *
        negEmbHom b' =
        (algebraMap A (LaurentTateAlgebra A) f - LaurentTateAlgebra.zeta) *
        (posEmbHom a - LaurentTateAlgebra.zetaInv * negEmbHom b') := by ring
    rw [this, hneg_b, hab, mul_comm]
    exact hc
  -- Step 5: λ(g - g', h - h') = 0 by linearity
  have hker : lambdaMap (g - g', h - h') = 0 := by
    change posEmbHom (g - g') - negEmbHom (h - h') = 0
    have heq : posEmbHom g' - negEmbHom h' = posEmbHom g - negEmbHom h := hrow1
    rw [map_sub, map_sub]
    linear_combination -heq
  -- Step 6: By Row 2 exactness, (g - g', h - h') ∈ im(ι)
  obtain ⟨a, ha⟩ := ker_lambdaMap_le_range_iotaHom (g - g', h - h') hker
  -- Step 7: ha says ι(a) = (g - g', h - h'), i.e.,
  -- algebraMap(a) = g - g' and algebraMap(a) = h - h'
  have ha1 : algebraMap A ↥(TateAlgebra A) a = g - g' := (Prod.mk.inj ha).1
  have ha2 : algebraMap A ↥(TateAlgebra A) a = h - h' := (Prod.mk.inj ha).2
  -- Step 8: Projecting to quotients: mk(g) = mk(algebraMap(a)) since g' ∈ ideal
  refine ⟨a, Prod.ext ?_ ?_⟩
  · -- mk g = mk (algebraMap a) in B₁
    symm; apply Ideal.Quotient.eq.mpr
    -- Need: algebraMap(a) - g ∈ (f - X). Since algebraMap(a) = g - g', this is -g' ∈ (f-X).
    rw [ha1, show g - (g - g') = g' from by ring]
    exact hg'_mem
  · -- mk h = mk (algebraMap a) in B₂
    symm; apply Ideal.Quotient.eq.mpr
    rw [ha2, show h - (h - h') = h' from by ring]
    exact hh'_mem

/-- **Row 3 full exactness (general case).**
1. `δ ∘ ε = 0`
2. `ker(δ) ⊆ im(ε)`
3. `δ` surjective -/
theorem row3_exact [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]
    (htop : ‹TopologicalSpace A› = UniformSpace.toTopologicalSpace) :
    (∀ a : A, deltaMap_gen f (epsilonHom_gen f a) = 0) ∧
    (∀ p : B₁_gen f × B₂_gen f,
      deltaMap_gen f p = 0 → ∃ a : A, epsilonHom_gen f a = p) ∧
    Function.Surjective (deltaMap_gen f) :=
  ⟨deltaMap_gen_comp_epsilonHom_gen f,
   ker_deltaMap_gen_le_range_epsilonHom_gen f htop,
   deltaMap_gen_surjective f htop⟩

end Row3General

/-! ### Strict exactness of the Laurent row (R2)

The Laurent cover exact sequence `0 → A →ε B₁ × B₂ →δ B₁₂ → 0` is STRICT:
- `δ` is open (surjective continuous map, Banach open mapping)
- `ker(δ)` is closed and complete
- `ε` is a topological embedding (continuous bijection onto `ker(δ)`, open by Banach)

This gives the topological sheaf condition WITHOUT proving individual restriction
maps are topological embeddings (which is FALSE in general — see TICKETS-axiom-clean.md).

**Wedhorn reference:** Lemma 8.33, using Theorem 6.16 (open mapping for Tate modules).
**Reviewer note (2026-04-03):** The correct route is strict exactness, not individual
inducing maps. -/

-- R2 (strict exactness) lives in StructureSheaf.lean or a new file, since it
-- operates on `presheafValue` (completed localizations with topology), not on
-- the algebraic quotients `B₁_gen` defined here.
-- See docs/TICKETS-axiom-clean.md for the proof plan.

end LaurentCover
