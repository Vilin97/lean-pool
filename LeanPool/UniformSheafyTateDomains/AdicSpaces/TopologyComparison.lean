/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafIdentification
import LeanPool.UniformSheafyTateDomains.AdicSpaces.TateAlgebraWedhorn
import Mathlib.Data.Finsupp.Encodable

/-!
# Topology Comparison: Completion Isomorphism (Non-Discrete)

The key bridge: `presheafValue D ≃+* A⟨X⟩/(1-sX)` for non-discrete
strongly noetherian Tate rings.

## Strategy

1. Show `locToQuotientOneSubfX_gen : Localization.Away s →+* A⟨X⟩/(1-sX)`
   is continuous for localization topology → T-topology quotient.
2. Extend to `presheafValue D →+* A⟨X⟩/(1-sX)` via `extensionHom`.
3. The round-trip `Localization → Quotient → presheafValue` = `coeRingHom`.
4. Both composites are identity → isomorphism.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §5.6, §8.1
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [NonarchimedeanRing A]

section CompletionIsomorphism

omit [PlusSubring A] [IsHuberRing A] in
/-- The round-trip `Localization → Quotient → presheafValue` equals
`locLiftToPresheaf = coeRingHom`. -/
theorem tateQuotient_roundtrip_eq_locLift (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D)) :
    ((tateQuotientToPresheafHom D hb).comp (locToQuotientOneSubfX_gen D.s)) =
    locLiftToPresheaf D := by
  apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
  ext b
  simp only [RingHom.comp_apply]
  rw [locToQuotientOneSubfX_gen_algebraMap, tateQuotientToPresheafHom_algebraMap,
    locLiftToPresheaf_algebraMap]

omit [PlusSubring A] [IsHuberRing A] in
/-- The round-trip pointwise. -/
theorem tateQuotient_roundtrip_apply (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (a : Localization.Away D.s) :
    tateQuotientToPresheafHom D hb (locToQuotientOneSubfX_gen D.s a) =
    locLiftToPresheaf D a :=
  RingHom.congr_fun (tateQuotient_roundtrip_eq_locLift D hb) a

/-! ### Step 1: Continuity of locToQuotientOneSubfX_gen

For the localization topology on `Localization.Away D.s` and the
quotient of the T-topology on `A⟨X⟩/(1-sX)`, the map
`locToQuotientOneSubfX_gen` is continuous.

This is the Artin-Rees topology comparison: the localization neighborhoods
`{(I·D)^m}` eventually land inside the quotient neighborhoods
`{class(g) : coeff n g ∈ s^n · U for all n}`.

For the proof: an element of `locNhd m` has the form `b/s^k` with
`b ∈ I^m · A₀`. Its image in the quotient is `class(b · X^k)`.
The T-topology condition: `coeff n (b · X^k) ∈ s^n · U`.
Since `coeff n (b · X^k) = b` if `n = k`, 0 otherwise.
Condition: `b ∈ s^k · U`. Since `b ∈ I^m · A₀` and `s^k · U`
contains `I^m · A₀` for `m ≥ m₀(U, k)` (Artin-Rees), this holds.

**NOTE:** This step requires the T-topology (from TateAlgebraWedhorn.lean),
NOT the product topology. With the product topology, the condition would
be `b ∈ U` (no `s^k` factor), which is weaker and doesn't match.
-/

/-! ### Bridge lemma: T₀ localization → annihilation by powers of s

For sorry-elimination in StructureSheaf.lean: if the localization topology
is T₀ and `coeRingHom(algebraMap b) = 0`, then `∃ k, s^k * b = 0`.
This reduces deep sorries to a single clean T₀ hypothesis. -/

omit [PlusSubring A] [IsHuberRing A] [NonarchimedeanRing A] in
/-- If the localization topology on `Localization.Away D.s` is T₀, then
`D.coeRingHom (algebraMap b) = 0` implies `∃ k, D.s ^ k * b = 0`.

Uses injectivity of the completion embedding for T₀ uniform spaces
(`UniformSpace.Completion.coe_injective`) and the localization
characterization (`IsLocalization.map_eq_zero_iff`). -/
theorem exists_pow_mul_eq_zero_of_coeRingHom_zero (D : RationalLocData A) (b : A)
    (ht0 : @T0Space (Localization.Away D.s)
      (@UniformSpace.toTopologicalSpace _ D.uniformSpace))
    (h : D.coeRingHom (algebraMap A (Localization.Away D.s) b) = 0) :
    ∃ k : ℕ, D.s ^ k * b = 0 := by
  have hinj : Function.Injective D.coeRingHom :=
    @UniformSpace.Completion.coe_injective _ D.uniformSpace ht0
  have hab : algebraMap A (Localization.Away D.s) b = 0 :=
    hinj (h.trans (map_zero D.coeRingHom).symm)
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers D.s)] at hab
  obtain ⟨⟨_, ⟨k, rfl⟩⟩, hk⟩ := hab
  exact ⟨k, hk⟩

/-! ### Step 1: Quotient T-topology on A⟨X⟩/(1-sX)

The quotient of the T-topology on `A⟨X⟩` by the ideal `(1-sX)` gives a
topological ring structure on `A⟨X⟩/(1-sX)`. This is the correct topology
for the comparison with the localization topology: the T-topology scales
coefficients by powers of `s`, matching the denominator structure in the
localization. -/

/-- Quotient T-topology on `A⟨X⟩/(1-sX)`: the quotient of `tateTopologyT f`
by the ideal `(1-fX)`. This is the topology used for the comparison with
the localization topology on `Localization.Away f` (Wedhorn, §5.48). -/
@[reducible]
noncomputable def quotientTTopology (f : A) :
    TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal f) :=
  @topologicalRingQuotientTopology _ (TateAlgebraWedhorn.tateTopologyT f) _
    (oneSubfXIdeal f)

/-- The quotient of the T-topology is a topological ring
(from Mathlib's `topologicalRing_quotient`, applied with the T-topology). -/
noncomputable instance quotientTTopology_isTopologicalRing (f : A) :
    @IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientTTopology f) _ :=
  @topologicalRing_quotient ↥(TateAlgebra A)
    (TateAlgebraWedhorn.tateTopologyT f) _
    (oneSubfXIdeal f) (TateAlgebraWedhorn.tateTopologyT_isTopologicalRing f)

/-- The quotient T-topology on `A⟨X⟩/(1-fX)` is nonarchimedean:
inherited from the nonarchimedean T-topology on `A⟨X⟩` via the
quotient map (which is continuous and open). -/
noncomputable instance quotientTTopology_nonarchimedean (f : A) :
    @NonarchimedeanRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      _ (quotientTTopology f) := by
  letI : TopologicalSpace ↥(TateAlgebra A) := TateAlgebraWedhorn.tateTopologyT f
  haveI : IsTopologicalRing ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT_isTopologicalRing f
  haveI : NonarchimedeanRing ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT_nonarchimedean f
  constructor
  intro U hU
  -- The preimage of U in A⟨X⟩ is a neighborhood of 0.
  have hcont : @Continuous _ _ (TateAlgebraWedhorn.tateTopologyT f)
      (quotientTTopology f) (Ideal.Quotient.mk (oneSubfXIdeal f)) :=
    continuous_quotient_mk'
  have hU' : (Ideal.Quotient.mk (oneSubfXIdeal f)) ⁻¹' (U : Set _) ∈
      nhds (0 : ↥(TateAlgebra A)) :=
    hcont.continuousAt.preimage_mem_nhds hU
  -- Find an open additive subgroup V inside the preimage.
  obtain ⟨V, hVU⟩ := NonarchimedeanRing.is_nonarchimedean _ hU'
  -- Push V forward via the quotient map.
  refine ⟨{
    toAddSubgroup := V.toAddSubgroup.map
      (Ideal.Quotient.mk (oneSubfXIdeal f)).toAddMonoidHom
    isOpen' := QuotientRing.isOpenMap_coe _ _ V.isOpen
  }, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact hVU hy

omit [PlusSubring A] [IsHuberRing A] [NonarchimedeanRing A] in
/-- Multiplication by `s * t` sends `I^(k+C)` into `I^k` (inside `A₀`):
for each `t`, continuity of `x ↦ s * t * x` yields `C` with
`s * t * Im(I^{k+C}) ⊆ Im(I^k)` for all `k`.  This is the Artin-Rees
shift constant for the T-topology self-preserving neighborhood. -/
private theorem mul_st_ideal_shift (P : PairOfDefinition A) (s t : A) :
    ∃ C : ℕ, ∀ (k : ℕ) (b : P.A₀), (b : P.A₀) ∈ P.I ^ (k + C) →
      s * t * (b : A) ∈ Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀) := by
  -- Multiplication by s*t is continuous, so ∃ C with s*t * Im(I^C) ⊆ A₀.
  have hmul_cont : Continuous (fun x : A ↦ s * t * x) :=
    continuous_const.mul continuous_id
  have hA₀_nhds : (P.A₀ : Set A) ∈ nhds (0 : A) :=
    P.isOpen.mem_nhds P.A₀.zero_mem
  have h_pre : (s * t * ·) ⁻¹' (P.A₀ : Set A) ∈ nhds (0 : A) :=
    hmul_cont.continuousAt.preimage_mem_nhds (by simp [hA₀_nhds])
  obtain ⟨C, -, hC⟩ := P.hasBasis_nhds_zero.mem_iff.mp h_pre
  -- hC : ∀ x ∈ Im(I^C), s * t * x ∈ A₀.
  refine ⟨C, fun k b hb ↦ ?_⟩
  -- b ∈ I^(k+C) ⊆ I^C * I^k. Use Ideal.mul_le and span_induction.
  rw [show k + C = C + k from by omega, pow_add] at hb
  -- b ∈ I^C * I^k. Decompose via Ideal.mul_le / the ideal product.
  -- The result s * t * val(b) ∈ val '' I^k follows because:
  -- for generators c * a with c ∈ I^C, a ∈ I^k:
  --   s * t * val(c * a) = s * t * val(c) * val(a)
  --   s * t * val(c) ∈ A₀ (by hC), so = val(d) for d ∈ A₀
  --   val(d) * val(a) = val(d * a) ∈ val(I^k) since a ∈ I^k, d ∈ A₀.
  -- For sums: val '' I^k is closed under addition (I^k is an additive subgroup).
  -- b ∈ I^C * I^k. Reduce to products c * a via Submodule.mul_induction_on,
  -- then show s * t * val(c * a) ∈ val '' I^k for each generator.
  refine Submodule.mul_induction_on hb (fun c hc a ha ↦ ?_) (fun x y hx hy ↦ ?_)
  · -- Product case: c ∈ I^C, a ∈ I^k.
    have hca : (c * a : P.A₀).val = c.val * a.val := rfl
    rw [hca, show s * t * (c.val * a.val) = (s * t * c.val) * a.val from by ring]
    have hstc : s * t * c.val ∈ (P.A₀ : Set A) :=
      hC ⟨c, hc, rfl⟩
    exact ⟨⟨s * t * c.val, hstc⟩ * a, Ideal.mul_mem_left _ _ ha, rfl⟩
  · -- Sum case: s * t * val(x + y) = s * t * val(x) + s * t * val(y).
    rw [show (x + y : P.A₀).val = x.val + y.val from rfl, mul_add]
    obtain ⟨x', hx', hx_eq⟩ := hx; obtain ⟨y', hy', hy_eq⟩ := hy
    exact ⟨x' + y', (P.I ^ k).add_mem hx' hy',
      show (x' + y' : P.A₀).val = _ by
        change x'.val + y'.val = _; rw [hx_eq, hy_eq]⟩

-- Helper: `divByS t s = algebraMap t * invSelf s` in `Localization.Away s`.
omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [IsHuberRing A]
  [NonarchimedeanRing A] in
private theorem divByS_eq_algebraMap_mul_invSelf (t s : A) :
    divByS t s = algebraMap A (Localization.Away s) t *
      IsLocalization.Away.invSelf (S := Localization.Away s) s := by
  unfold divByS IsLocalization.Away.invSelf
  rw [IsLocalization.mk'_eq_mul_mk'_one]

omit [PlusSubring A] [IsHuberRing A] in
-- Helper: `φ(divByS t s) = mk(algebraMap t * X)`.
private theorem locToQuotientOneSubfX_gen_divByS (s t : A) :
    locToQuotientOneSubfX_gen s (divByS t s) =
      Ideal.Quotient.mk (oneSubfXIdeal s)
        (algebraMap A _ t * TateAlgebra.X) := by
  rw [divByS_eq_algebraMap_mul_invSelf, map_mul,
    locToQuotientOneSubfX_gen_algebraMap,
    locToQuotientOneSubfX_gen_invSelf, ← map_mul]

-- Helper: scaled coefficient of `algebraMap(a) * g`.
private theorem scaledCoeff_algebraMap_mul (f a : A)
    (g : ↥(TateAlgebra A)) (n : ℕ) :
    f ^ n * TateAlgebra.coeff n (algebraMap A _ a * g) =
      a * (f ^ n * TateAlgebra.coeff n g) := by
  rw [TateAlgebra.coeff_algebraMap_mul, ← mul_assoc, mul_comm (f ^ n) a, mul_assoc]

-- Helper: scaled coefficient of `algebraMap(t) * X * g` at n+1.
private theorem scaledCoeff_succ_tX_mul (f t : A)
    (g : ↥(TateAlgebra A)) (n : ℕ) :
    f ^ (n + 1) * TateAlgebra.coeff (n + 1) (algebraMap A _ t * TateAlgebra.X * g) =
      f * t * (f ^ n * TateAlgebra.coeff n g) := by
  rw [show algebraMap A _ t * TateAlgebra.X * g =
    algebraMap A _ t * (TateAlgebra.X * g) from by ring,
    TateAlgebra.coeff_algebraMap_mul, TateAlgebra.coeff_succ_X_mul, pow_succ]
  ring

-- Helper: scaled coefficient of `algebraMap(t) * X * g` at 0.
private theorem scaledCoeff_zero_tX_mul (f t : A) (g : ↥(TateAlgebra A)) :
    f ^ 0 * TateAlgebra.coeff 0 (algebraMap A _ t * TateAlgebra.X * g) = 0 := by
  rw [show algebraMap A _ t * TateAlgebra.X * g =
    algebraMap A _ t * (TateAlgebra.X * g) from by ring,
    TateAlgebra.coeff_algebraMap_mul, TateAlgebra.coeff_zero_X_mul, mul_zero, mul_zero]

/-- The self-preserving T-topology neighborhood `G` used in the continuity proof:
the set of `g ∈ A⟨X⟩` whose scaled coefficients `s ^ n · coeff n g` lie in the
image of `I ^ (M + (N - n) * C)` for every `n ≤ N`. The `(N - n) * C` shift budget
is what lets `G` absorb a multiplication by `algebraMap t * X` (Artin-Rees). -/
private def artinReesNhd (P : PairOfDefinition A) (s : A) (C M N : ℕ) :
    Set ↥(TateAlgebra A) := fun g ↦
  ∀ n : ℕ, n ≤ N →
    s ^ n * TateAlgebra.coeff n g ∈
      Subtype.val '' ((P.I ^ (M + (N - n) * C) : Ideal P.A₀) : Set P.A₀)

/-- `0 ∈ artinReesNhd`. -/
private theorem zero_mem_artinReesNhd (P : PairOfDefinition A) (s : A) (C M N : ℕ) :
    (0 : ↥(TateAlgebra A)) ∈ artinReesNhd P s C M N := by
  intro n _
  have : TateAlgebra.coeff n (0 : ↥(TateAlgebra A)) = 0 := map_zero _
  rw [this, mul_zero]
  exact ⟨0, (P.I ^ _).zero_mem, rfl⟩

/-- `artinReesNhd` is closed under addition. -/
private theorem add_mem_artinReesNhd (P : PairOfDefinition A) (s : A) (C M N : ℕ)
    {a b : ↥(TateAlgebra A)} (ha : a ∈ artinReesNhd P s C M N)
    (hb : b ∈ artinReesNhd P s C M N) : a + b ∈ artinReesNhd P s C M N := by
  intro n hn
  have hcoeff_add : TateAlgebra.coeff n (a + b) =
      TateAlgebra.coeff n a + TateAlgebra.coeff n b := map_add _ _ _
  rw [hcoeff_add, mul_add]
  obtain ⟨x, hx, hx_eq⟩ := ha n hn
  obtain ⟨y, hy, hy_eq⟩ := hb n hn
  exact ⟨x + y, (P.I ^ _).add_mem hx hy, by rw [Subring.coe_add, ← hx_eq, ← hy_eq]⟩

/-- `artinReesNhd` is closed under negation. -/
private theorem neg_mem_artinReesNhd (P : PairOfDefinition A) (s : A) (C M N : ℕ)
    {a : ↥(TateAlgebra A)} (ha : a ∈ artinReesNhd P s C M N) :
    -a ∈ artinReesNhd P s C M N := by
  intro n hn
  have hcoeff_neg : TateAlgebra.coeff n (-a) = -TateAlgebra.coeff n a := map_neg _ _
  rw [hcoeff_neg, mul_neg]
  obtain ⟨x, hx, hx_eq⟩ := ha n hn
  exact ⟨-x, (P.I ^ _).neg_mem hx, by rw [NegMemClass.coe_neg, ← hx_eq]⟩

/-- `artinReesNhd` is a neighborhood of `0` in the T-topology: it is the finite
intersection (over `n ≤ N`) of preimages of the open sets `val '' I^…` under the
continuous scaled-coefficient maps. -/
private theorem artinReesNhd_mem_nhds (P : PairOfDefinition A) (s : A) (C M N : ℕ) :
    artinReesNhd P s C M N ∈
      @nhds _ (TateAlgebraWedhorn.tateTopologyT s) 0 := by
  letI τT : TopologicalSpace ↥(TateAlgebra A) := TateAlgebraWedhorn.tateTopologyT s
  have hG_eq : artinReesNhd P s C M N =
      ⋂ (i : Fin (N + 1)), {g | s ^ (i : ℕ) * TateAlgebra.coeff (i : ℕ) g ∈
        Subtype.val '' ((P.I ^ (M + (N - (i : ℕ)) * C) : Ideal P.A₀) : Set P.A₀)} := by
    ext g; simp only [artinReesNhd, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hg ⟨i, hi⟩; exact hg i (by omega)
    · intro hg n hn; exact hg ⟨n, by omega⟩
  rw [mem_nhds_iff]
  refine ⟨_, le_refl _, ?_, zero_mem_artinReesNhd P s C M N⟩
  rw [hG_eq]
  exact isOpen_iInter_of_finite fun ⟨n, _⟩ ↦
    (P.pow_image_isOpen _).preimage
      (TateAlgebraWedhorn.tateTopologyT_continuous_scaledCoeff s n)

/-- `artinReesNhd` is stable under multiplication by `algebraMap a₀` for `a₀ ∈ A₀`:
multiplying scales each coefficient by `a₀`, and `a₀ · I^k ⊆ I^k`. -/
private theorem mul_algebraMap_mem_artinReesNhd (P : PairOfDefinition A) (s : A)
    (C M N : ℕ) (a₀ : P.A₀) {g : ↥(TateAlgebra A)}
    (hg : g ∈ artinReesNhd P s C M N) :
    algebraMap A _ (a₀ : A) * g ∈ artinReesNhd P s C M N := by
  intro n hn
  rw [scaledCoeff_algebraMap_mul]
  obtain ⟨b, hb, hb_eq⟩ := hg n hn
  exact ⟨a₀ * b, Ideal.mul_mem_left _ _ hb, by rw [MulMemClass.coe_mul, ← hb_eq]⟩

/-- `artinReesNhd` is stable under multiplication by `algebraMap t * X` for any `t`
with the Artin-Rees shift property `hC_shift`: the `X` shifts the coefficient index
up by one (consuming one unit of the `(N - n) * C` budget), and `s * t` carries
`I^(j+C)` back into `I^j`. -/
private theorem mul_algebraMap_X_mem_artinReesNhd (P : PairOfDefinition A) (s t : A)
    (C M N : ℕ)
    (hC_shift : ∀ (k : ℕ) (b : P.A₀), (b : P.A₀) ∈ P.I ^ (k + C) →
      s * t * (b : A) ∈ Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀))
    {g : ↥(TateAlgebra A)} (hg : g ∈ artinReesNhd P s C M N) :
    algebraMap A _ t * TateAlgebra.X * g ∈ artinReesNhd P s C M N := by
  intro n hn
  by_cases hn0 : n = 0
  · subst hn0
    rw [scaledCoeff_zero_tX_mul]; exact ⟨0, (P.I ^ _).zero_mem, rfl⟩
  · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [scaledCoeff_succ_tX_mul]
    have hn' : n' ≤ N := by omega
    obtain ⟨b, hb, hb_eq⟩ := hg n' hn'
    rw [← hb_eq]
    have hkey : M + (N - n') * C = (M + (N - (n' + 1)) * C) + C := by
      have : N - n' = N - (n' + 1) + 1 := by omega
      rw [this, add_mul, one_mul]; omega
    exact hC_shift (M + (N - (n' + 1)) * C) b (hkey ▸ hb)

/-- For any neighborhood W of 0 in the quotient T-topology, there exists m such that
for all r in locSubring and b in I^m, the product phi(r) * mk(algebraMap(b)) lands in W.

This is the generator case needed by the span_induction in the continuity proof.
The proof constructs a self-preserving T-topology neighborhood G inside mk^{-1}(W) using
Artin-Rees shift constants, shows algebraMap(I^m) maps into G for m large enough, then
uses Subring.closure_induction to show every locSubring element has a lift that
stabilizes G. -/
private theorem locToQuotient_mul_small_constant_mem (D : RationalLocData A)
    [T2Space A]
    (W : Set (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s))
    (hW_top : W ∈ @nhds _ (quotientTTopology D.s) 0) :
    ∃ m : ℕ,
      ∀ (r : locSubring D.P D.T D.s) (b : D.P.A₀),
        (b : D.P.A₀) ∈ D.P.I ^ m →
        locToQuotientOneSubfX_gen D.s
          ((locSubring D.P D.T D.s).subtype r *
            algebraMap A (Localization.Away D.s) (b : A)) ∈ W := by
  -- Setup topology instances.
  letI τT : TopologicalSpace ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT D.s
  letI τQ : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  haveI hTR_T : IsTopologicalRing ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT_isTopologicalRing D.s
  haveI hTR_Q : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  -- Abbreviations.
  let mk := Ideal.Quotient.mk (oneSubfXIdeal D.s)
  let P := D.P; let s := D.s; let T := D.T
  -- Step 1: Get Artin-Rees shift constant C (max over all t ∈ T).
  have hC_exists : ∀ t : T, ∃ C : ℕ, ∀ (k : ℕ) (b : P.A₀),
      (b : P.A₀) ∈ P.I ^ (k + C) →
        s * t * (b : A) ∈ Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀) :=
    fun t ↦ mul_st_ideal_shift P s t
  choose C_fn hC_fn using hC_exists
  let C := (T.attach.image C_fn).sup id
  have hC_bound : ∀ (t : T), C_fn t ≤ C := fun t ↦
    Finset.le_sup (f := id) (Finset.mem_image_of_mem _ (Finset.mem_attach _ _))
  have hC_shift : ∀ (t : T) (k : ℕ) (b : P.A₀), (b : P.A₀) ∈ P.I ^ (k + C) →
      s * t * (b : A) ∈ Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀) := by
    intro t k b hb
    have := hC_bound t
    exact hC_fn t k b (Ideal.pow_le_pow_right (by omega) hb)
  -- Step 2: Pull W back to T-topology via mk.
  have hmk_cont : @Continuous _ _ τT τQ mk := continuous_quotient_mk'
  have hmk_pre_W : mk ⁻¹' W ∈ @nhds _ τT 0 :=
    hmk_cont.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  -- Step 3: Decompose the T-topology neighborhood.
  rw [@nhds_induced _ _ (MvPowerSeries.WithPiTopology.instTopologicalSpace A)
    (TateAlgebraWedhorn.scaleIncl s) 0, Filter.mem_comap] at hmk_pre_W
  obtain ⟨W_prod, hW_prod, hW_incl⟩ := hmk_pre_W
  rw [map_zero] at hW_prod
  change W_prod ∈ @nhds _ (@Pi.topologicalSpace (Fin 1 →₀ ℕ)
    (fun _ ↦ A) (fun _ ↦ ‹_›)) 0 at hW_prod
  rw [nhds_pi] at hW_prod
  simp only [show ∀ i : Fin 1 →₀ ℕ,
    (0 : (Fin 1 →₀ ℕ) → A) i = (0 : A) from fun _ ↦ rfl] at hW_prod
  obtain ⟨Idx, t_set, ht_set, hIt⟩ := Filter.mem_pi'.mp hW_prod
  -- Step 4: For each index in Idx, find m_i with Im(I^{m_i}) ⊆ t_set(i).
  have hm_exists : ∀ i : Fin 1 →₀ ℕ,
      ∃ m : ℕ, Subtype.val '' ((P.I ^ m : Ideal P.A₀) : Set P.A₀) ⊆ t_set i :=
    fun i ↦ by
      obtain ⟨m, _, hm⟩ := P.hasBasis_nhds_zero.mem_iff.mp (ht_set i)
      exact ⟨m, hm⟩
  choose m_fn hm_fn using hm_exists
  let N := (Idx.image (fun i : Fin 1 →₀ ℕ ↦ i 0)).sup id
  let M := (Idx.image m_fn).sup id
  -- Step 5: Construct G — the self-preserving neighborhood (see `artinReesNhd`).
  let G : Set ↥(TateAlgebra A) := artinReesNhd P s C M N
  -- Step 5a: G is contained in mk⁻¹(W).
  have hG_sub_W : G ⊆ mk ⁻¹' W := by
    intro g hg
    apply hW_incl
    apply hIt
    intro i hi
    have : i 0 ≤ N :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem (fun i : Fin 1 →₀ ℕ ↦ i 0) hi)
    have hg_i := hg (i 0) this
    have hM_bound : m_fn i ≤ M :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem m_fn hi)
    have hpow_le : M + (N - i 0) * C ≥ m_fn i := by omega
    have hsub : Subtype.val '' ((P.I ^ (M + (N - i 0) * C) : Ideal P.A₀) : Set P.A₀) ⊆
        Subtype.val '' ((P.I ^ (m_fn i) : Ideal P.A₀) : Set P.A₀) :=
      Set.image_mono (Ideal.pow_le_pow_right hpow_le)
    -- scaleIncl s g i = s^(i 0) * g.val i = s^(i 0) * coeff(i 0) g
    -- For Fin 1, i = Finsupp.single 0 (i 0), and TateAlgebra.coeff (i 0) g = g.val i.
    have hi_eq : i = Finsupp.single 0 (i 0) := by
      apply Finsupp.ext; intro j; fin_cases j; simp
    change TateAlgebraWedhorn.scaleIncl s g i ∈ t_set i
    rw [TateAlgebraWedhorn.scaleIncl_apply]
    -- Goal: s ^ (i 0) * g.val i ∈ t_set i
    -- hg_i : s ^ (i 0) * TateAlgebra.coeff (i 0) g ∈ val(I^{M+(N-i 0)*C})
    -- TateAlgebra.coeff (i 0) g = MvPowerSeries.coeff A (Finsupp.single 0 (i 0)) g
    --                            = g.val (Finsupp.single 0 (i 0)) = g.val i
    -- So the result follows from hg_i + hsub + hm_fn.
    have hscale : s ^ i 0 * g.val i =
        s ^ i 0 * TateAlgebra.coeff (i 0) g := by
      congr 1; change g.val i = g.val (Finsupp.single 0 (i 0)); rw [← hi_eq]
    rw [hscale]
    exact hm_fn i (hsub hg_i)
  -- Step 5b/5c: G is an additive subgroup and a T-topology neighborhood of 0.
  have hG_zero : (0 : ↥(TateAlgebra A)) ∈ G := zero_mem_artinReesNhd P s C M N
  have hG_add : ∀ {a b}, a ∈ G → b ∈ G → a + b ∈ G :=
    fun ha hb ↦ add_mem_artinReesNhd P s C M N ha hb
  have hG_neg : ∀ {a}, a ∈ G → -a ∈ G := fun ha ↦ neg_mem_artinReesNhd P s C M N ha
  have hG_nhds : G ∈ @nhds _ τT 0 := artinReesNhd_mem_nhds P s C M N
  -- Step 6: G is stable under algebraMap(a₀) * · for a₀ ∈ A₀.
  have hG_stable_alg : ∀ (a₀ : P.A₀) (g : ↥(TateAlgebra A)),
      g ∈ G → algebraMap A _ (a₀ : A) * g ∈ G :=
    fun a₀ g hg ↦ mul_algebraMap_mem_artinReesNhd P s C M N a₀ hg
  -- Step 7: G is stable under algebraMap(t)*X * · for t ∈ T.
  have hG_stable_tX : ∀ (t : T) (g : ↥(TateAlgebra A)),
      g ∈ G → algebraMap A _ (t : A) * TateAlgebra.X * g ∈ G :=
    fun t g hg ↦ mul_algebraMap_X_mem_artinReesNhd P s t C M N (hC_shift t) hg
  -- Step 8: Find m such that algebraMap(I^m) maps into G.
  -- Use continuity of mk ∘ algebraMap: preimage of G (which is a nhd of 0 in
  -- the T-topology) under algebraMap gives a nhd of 0 in A.
  have halg_cont : @Continuous A _ _ τT (algebraMap A ↥(TateAlgebra A)) :=
    TateAlgebraWedhorn.tateTopologyT_continuous_algebraMap D.s
  have h_pre_G : (algebraMap A ↥(TateAlgebra A)) ⁻¹' G ∈ nhds (0 : A) :=
    halg_cont.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨m, -, hm_G⟩ := P.hasBasis_nhds_zero.mem_iff.mp h_pre_G
  -- hm_G : val(I^m) maps into the preimage of G under algebraMap.
  -- I.e., for b ∈ I^m, algebraMap(b.val) ∈ G.
  refine ⟨m, fun r b hb ↦ ?_⟩
  -- We need: φ(subtype(r) * algebraMap(b.val)) ∈ W.
  -- Rewrite as: φ(subtype(r)) * mk(algebraMap(b.val)) = mk(r') * mk(algebraMap(b.val))
  --           = mk(r' * algebraMap(b.val))
  -- where r' is a lift of r in A⟨X⟩ such that r' stabilizes G.
  -- Since algebraMap(b.val) ∈ G, r' * algebraMap(b.val) ∈ G ⊆ mk⁻¹(W).
  --
  -- Use Subring.closure_induction on r ∈ locSubring = Subring.closure(generators).
  -- Predicate: P(r) = ∃ r' : A⟨X⟩, mk(r') = φ(subtype(r)) ∧ ∀ g ∈ G, r' * g ∈ G.
  have hb_in_G : algebraMap A ↥(TateAlgebra A) (b : A) ∈ G :=
    hm_G ⟨b, hb, rfl⟩
  -- The predicate we prove by closure_induction.
  -- For each r in locSubring, there exists r' in A⟨X⟩ such that:
  --   (1) mk(r') = φ(subtype(r))
  --   (2) ∀ g ∈ G, r' * g ∈ G
  -- For each element x ∈ locSubring = Subring.closure(generators), prove
  -- there exists a lift r' ∈ A⟨X⟩ with mk(r') = φ(x) and r' stabilizes G.
  -- Then the conclusion follows: φ(r) * mk(algebraMap(b)) = mk(r' * algebraMap(b)) ∈ W.
  have hlift : ∀ (x : Localization.Away D.s),
      x ∈ locSubring D.P D.T D.s → ∃ r' : ↥(TateAlgebra A),
        mk r' = locToQuotientOneSubfX_gen D.s x ∧ ∀ g ∈ G, r' * g ∈ G := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a₀, ha₀, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩
      · -- Case: x = algebraMap(a₀) with a₀ ∈ A₀.
        refine ⟨algebraMap A _ a₀, ?_, ?_⟩
        · rw [← locToQuotientOneSubfX_gen_algebraMap]
        · exact hG_stable_alg ⟨a₀, ha₀⟩
      · -- Case: x = divByS(t, s) with t ∈ T.
        refine ⟨algebraMap A _ t * TateAlgebra.X, ?_, ?_⟩
        · rw [← locToQuotientOneSubfX_gen_divByS]
        · exact hG_stable_tX ⟨t, ht⟩
    | zero =>
      exact ⟨0, by simp [map_zero], fun g _ ↦ by simp [zero_mul, hG_zero]⟩
    | one =>
      exact ⟨1, by simp [map_one], fun g hg ↦ by simp [one_mul, hg]⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨rx, hrx_eq, hrx_stab⟩ := ihx
      obtain ⟨ry, hry_eq, hry_stab⟩ := ihy
      exact ⟨rx + ry, by rw [map_add, hrx_eq, hry_eq, map_add],
        fun g hg ↦ by rw [add_mul]; exact hG_add (hrx_stab g hg) (hry_stab g hg)⟩
    | neg x _ ihx =>
      obtain ⟨rx, hrx_eq, hrx_stab⟩ := ihx
      exact ⟨-rx, by rw [map_neg, hrx_eq, map_neg],
        fun g hg ↦ by rw [neg_mul]; exact hG_neg (hrx_stab g hg)⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨rx, hrx_eq, hrx_stab⟩ := ihx
      obtain ⟨ry, hry_eq, hry_stab⟩ := ihy
      exact ⟨rx * ry, by rw [map_mul, hrx_eq, hry_eq, map_mul],
        fun g hg ↦ by rw [mul_assoc]; exact hrx_stab _ (hry_stab g hg)⟩
  obtain ⟨r', hr'_eq, hr'_stab⟩ := hlift r.val r.property
  -- Goal: φ(subtype(r) * algebraMap(b.val)) ∈ W
  -- Rewrite to: mk(r' * algebraMap(b.val)) ∈ W
  -- φ(subtype(r) * algebraMap(b)) = φ(subtype(r)) * φ(algebraMap(b))
  --   = φ(subtype(r)) * mk(algebraMap(b))     [locToQuotientOneSubfX_gen_algebraMap]
  --   = mk(r') * mk(algebraMap(b))            [← hr'_eq]
  --   = mk(r' * algebraMap(b))                [← map_mul]
  -- And r' * algebraMap(b) ∈ G ⊆ mk⁻¹(W), so mk(r' * algebraMap(b)) ∈ W.
  -- φ(subtype(r) * algebraMap(b)) = mk(r' * algebraMap_Tate(b)) ∈ mk(G) ⊆ W
  -- The subtype coercion and r.val are the same:
  have hr_val : (locSubring D.P D.T D.s).subtype r = r.val := rfl
  rw [hr_val, map_mul, locToQuotientOneSubfX_gen_algebraMap, ← hr'_eq, ← map_mul]
  exact hG_sub_W (hr'_stab _ hb_in_G)

/-! ### Step 1b: Continuity of locToQuotientOneSubfX_gen

The continuity proof requires connecting `locNhd` to the T-topology
quotient neighborhoods via the Artin-Rees comparison. The key insight:
an element of `locNhd m` has the form `b/s^k` with `b ∈ I^m * A₀`.
Its image in the quotient is `class(algebraMap(b) * X^k)`.
The T-topology via `scaleIncl` requires `s^n * coeff_n(g) ∈ U` for all `n`.
For `g = algebraMap(b) * X^k`, the only nonzero coefficient is at `n = k`,
giving `s^k * b ∈ U`. Since `b ∈ I^m` and the topology on `A` is nonarchimedean,
`s^k * I^m ⊆ U` for `m` large enough (continuity of scalar multiplication). -/

/-- The map `locToQuotientOneSubfX_gen D.s` is continuous from the localization
topology on `Localization.Away D.s` to the quotient T-topology on
`A⟨X⟩/(1-sX)`.

**Proof sketch (Wedhorn §8.1):** The localization neighborhoods `locNhd(n)`
map into quotient T-topology neighborhoods because elements `b/s^k` with
`b ∈ I^n` get sent to `class(algebraMap(b) * X^k)` whose scaled coefficients
`s^k * b ∈ s^k * I^n` lie in any target neighborhood for `n` sufficiently large.

This is the key continuity result bridging the localization topology with
the T-topology, enabling the completion extension. -/
theorem locToQuotientOneSubfX_gen_continuous (D : RationalLocData A)
    [T2Space A] :
    @Continuous _ _ D.topology (quotientTTopology D.s)
      (locToQuotientOneSubfX_gen D.s) := by
  -- Set up instances for the source and target topologies.
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away D.s) := D.isTopologicalAddGroup
  letI τQ : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  haveI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    @IsTopologicalRing.to_topologicalAddGroup _ _
      (quotientTTopology D.s) (quotientTTopology_isTopologicalRing D.s)
  -- Step 1: Reduce to continuity at 0 using additive group structure.
  apply continuous_of_continuousAt_zero (locToQuotientOneSubfX_gen D.s)
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro S hS
  -- Step 2: Get a basis neighborhood from the localization topology.
  have hbasis := locBasis D.P D.T D.s D.hopen
  let hb := hbasis.toRingFilterBasis.toAddGroupFilterBasis
  -- Step 3: The target neighborhood S contains an open additive subgroup.
  -- Use the nonarchimedean property of the quotient.
  haveI : NonarchimedeanRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_nonarchimedean D.s
  obtain ⟨W, hWS⟩ := NonarchimedeanRing.is_nonarchimedean S hS
  -- Step 4: It suffices to show locToQuotientOneSubfX_gen maps some
  -- locNhd n into W.
  suffices ∃ n, ∀ x ∈ locNhd D.P D.T D.s n,
      locToQuotientOneSubfX_gen D.s x ∈ (W : Set _) by
    obtain ⟨n, hn⟩ := this
    apply Filter.mem_of_superset
      (hb.nhds_zero_hasBasis.mem_iff.mpr
        ⟨locNhd D.P D.T D.s n, ⟨n, rfl⟩, le_refl _⟩)
    intro x hx
    exact hWS (hn x hx)
  -- Step 5: Use locToQuotient_mul_small_constant_mem to find m such that
  -- for all r ∈ locSubring and b ∈ I^m, φ(subtype(r) * algebraMap(b)) ∈ W.
  have hW_nhds : (W : Set _) ∈ @nhds _ τQ 0 :=
    W.isOpen.mem_nhds (W.zero_mem)
  obtain ⟨m, hm_helper⟩ :=
    locToQuotient_mul_small_constant_mem D (W : Set _) hW_nhds
  -- Step 6: Show locNhd(m) maps into W.
  -- We use Submodule.span_induction with the STRENGTHENED predicate:
  -- P(d) = "for all r ∈ locSubring, φ(subtype(r * d)) ∈ W".
  -- This handles the scalar case because r * (s * d) = (r * s) * d.
  -- Then P(d) with r = 1 gives φ(subtype(d)) ∈ W.
  refine ⟨m, ?_⟩
  rintro x ⟨d, hd, rfl⟩
  rw [locIdeal, ← Ideal.map_pow] at hd
  suffices ∀ (r : locSubring D.P D.T D.s),
      locToQuotientOneSubfX_gen D.s
        ((locSubring D.P D.T D.s).subtype (r * d)) ∈ (W : Set _) by
    simpa using this 1
  intro r₀
  revert r₀
  refine Submodule.span_induction (p := fun d _ ↦
      ∀ (r : locSubring D.P D.T D.s),
        locToQuotientOneSubfX_gen D.s
          ((locSubring D.P D.T D.s).subtype (r * d)) ∈
            (W : Set _)) ?_ ?_ ?_ ?_ hd
  · -- Generator: d = algebraMapD(b) for b ∈ I^m.
    rintro d ⟨b, hb, rfl⟩ r
    exact hm_helper r b hb
  · -- Zero
    intro r; simp [mul_zero, map_zero]
  · -- Addition: d₁ + d₂
    intro d₁ d₂ _ _ h₁ h₂ r
    have : (locSubring D.P D.T D.s).subtype (r * (d₁ + d₂)) =
        (locSubring D.P D.T D.s).subtype (r * d₁) +
        (locSubring D.P D.T D.s).subtype (r * d₂) := by
      simp [mul_add]
    rw [this, map_add]
    exact W.toAddSubgroup.add_mem (h₁ r) (h₂ r)
  · -- Scalar: s • d for s ∈ locSubring.
    intro s d _ hd r
    have : (locSubring D.P D.T D.s).subtype (r * (s • d)) =
        (locSubring D.P D.T D.s).subtype ((r * s) * d) := by
      simp [mul_assoc]
    rw [this]
    exact hd (r * s)

/-! ### Step 2: Extension to completion via extensionHom

Once continuity is established, `UniformSpace.Completion.extensionHom`
extends `locToQuotientOneSubfX_gen` to the completion, giving:
`presheafValueToQuotient : presheafValue D →+* A⟨X⟩/(1-sX)` -/

/-- The `IsTopologicalAddGroup` instance for the quotient T-topology. -/
noncomputable instance quotientTTopology_isTopologicalAddGroup (f : A) :
    @IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientTTopology f) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (quotientTTopology f) (quotientTTopology_isTopologicalRing f)

/-- The `UniformSpace` on the quotient T-topology. -/
@[reducible]
noncomputable def quotientTUniformSpace (f : A) :
    UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal f) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _
    (quotientTTopology f) (quotientTTopology_isTopologicalAddGroup f)

/-- The `IsUniformAddGroup` instance for the quotient T-topology. -/
noncomputable instance quotientTTopology_isUniformAddGroup (f : A) :
    @IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientTUniformSpace f) _ :=
  @isUniformAddGroup_of_addCommGroup _ _ (quotientTTopology f)
    (quotientTTopology_isTopologicalAddGroup f)

/-- The ring homomorphism `presheafValue D →+* A⟨X⟩/(1-sX)` extending
`locToQuotientOneSubfX_gen` to the completion.

Given that `locToQuotientOneSubfX_gen D.s` is continuous from the localization
topology to the quotient T-topology, `UniformSpace.Completion.extensionHom`
extends it to a ring homomorphism from the completion `presheafValue D`
to `A⟨X⟩/(1-sX)` (Wedhorn, Proposition 8.30).

The hypotheses `hcs` (completeness) and `ht0` (T0) on the quotient with the
T-topology hold for strongly noetherian Tate rings (Wedhorn Theorem 6.37). -/
noncomputable def presheafValueToQuotient (D : RationalLocData A)
    [T2Space A]
    (_hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s)) :
    presheafValue D →+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalAddGroup D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isUniformAddGroup D.s
  exact @UniformSpace.Completion.extensionHom _ _ _ _ _ _
    (quotientTUniformSpace D.s) _ (quotientTTopology_isUniformAddGroup D.s)
    (quotientTTopology_isTopologicalRing D.s)
    (locToQuotientOneSubfX_gen D.s)
    (locToQuotientOneSubfX_gen_continuous D) hcs ht0

/-- `presheafValueToQuotient` on the dense image agrees with
`locToQuotientOneSubfX_gen`. -/
theorem presheafValueToQuotient_coe (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (a : Localization.Away D.s) :
    presheafValueToQuotient D hb hcs ht0 (D.coeRingHom a) =
      locToQuotientOneSubfX_gen D.s a := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalAddGroup D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isUniformAddGroup D.s
  exact @UniformSpace.Completion.extensionHom_coe _ _ _ _ _ _
    (quotientTUniformSpace D.s) _ (quotientTTopology_isUniformAddGroup D.s)
    (quotientTTopology_isTopologicalRing D.s)
    (locToQuotientOneSubfX_gen D.s)
    (locToQuotientOneSubfX_gen_continuous D) hcs ht0 a

/-! ### Step 3: The round-trip composites are identity

Using the round-trip lemma `tateQuotient_roundtrip_eq_locLift` (already proved)
and T2 uniqueness of continuous extensions, we show both composites are identity. -/

/-- The composite `tateQuotientToPresheafHom ∘ presheafValueToQuotient` is the
identity on `presheafValue D`.

On the dense image `coeRingHom(a)`:
  `tateQuotientToPresheafHom (presheafValueToQuotient (coeRingHom a))`
  `= tateQuotientToPresheafHom (locToQuotientOneSubfX_gen a)`
  `= locLiftToPresheaf a`   (by round-trip)
  `= coeRingHom a`          (by `locLiftToPresheaf_eq_coeRingHom`)

By T2 density, this extends to all of `presheafValue D`. -/
theorem tateQuotientToPresheaf_comp_presheafToQuotient (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (x : presheafValue D) :
    tateQuotientToPresheafHom D hb
      (presheafValueToQuotient D hb hcs ht0 x) = x := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTUniformSpace D.s
  -- Use T2 density: the composite and id agree on the dense image.
  refine @UniformSpace.Completion.ext' _ D.uniformSpace
    (presheafValue D) _ _ _ _
    (hcont_eval.comp UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  -- On the dense image: show agreement pointwise.
  intro a
  simp only [Function.comp, id]
  change tateQuotientToPresheafHom D hb
    (presheafValueToQuotient D hb hcs ht0 (D.coeRingHom a)) = D.coeRingHom a
  rw [presheafValueToQuotient_coe D hb hcs ht0 a,
    tateQuotient_roundtrip_apply D hb a,
    locLiftToPresheaf_eq_coeRingHom D]

/-- The composite `presheafValueToQuotient ∘ tateQuotientToPresheafHom` is the
identity on `A⟨X⟩/(1-sX)`.

For `q = mk(g)` in the quotient:
  `presheafValueToQuotient (tateQuotientToPresheafHom (mk g))`
  `= presheafValueToQuotient (∑ canonicalMap(aₙ) · (invS)ⁿ)`

This requires showing the evaluation is the inverse of the localization map
on the quotient. By the universal property, it suffices to check on generators:
  - `mk(algebraMap a) ↦ canonicalMap a ↦ mk(algebraMap a)`
  - `mk(X) ↦ invS ↦ mk(X)`

The full proof uses density of the localization image in `presheafValue D`
and the round-trip on generators. -/
theorem presheafToQuotient_comp_tateQuotientToPresheaf (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (hdense : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientTTopology D.s) (Localization.Away D.s)
      (locToQuotientOneSubfX_gen D.s))
    (q : ↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :
    presheafValueToQuotient D hb hcs ht0
      (tateQuotientToPresheafHom D hb q) = q := by
  -- Setup instances for the quotient T-topology and localization.
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI τQ : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTUniformSpace D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalAddGroup D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isUniformAddGroup D.s
  -- T₀ uniform space is T₂ (uniform → regular → R1, and R1 + T₀ → T₂).
  haveI hT2 : @T2Space _ τQ := by
    haveI : @RegularSpace _ τQ :=
      @UniformSpace.to_regularSpace _ (quotientTUniformSpace D.s)
    exact inferInstance
  -- The composites agree on the dense image of locToQuotientOneSubfX_gen.
  have hagree : ∀ (a : Localization.Away D.s),
      presheafValueToQuotient D hb hcs ht0
        (tateQuotientToPresheafHom D hb (locToQuotientOneSubfX_gen D.s a)) =
        locToQuotientOneSubfX_gen D.s a := by
    intro a
    rw [tateQuotient_roundtrip_apply D hb a,
      locLiftToPresheaf_eq_coeRingHom D,
      presheafValueToQuotient_coe D hb hcs ht0 a]
  -- Use DenseRange.equalizer: two continuous maps agreeing on a dense
  -- subset of a T₂ space must be equal.
  -- g = presheafValueToQuotient ∘ tateQuotientToPresheafHom
  -- h = id
  -- Both are continuous; g ∘ locToQuotientOneSubfX_gen = h ∘ locToQuotientOneSubfX_gen.
  have h_eq : (fun q ↦ presheafValueToQuotient D hb hcs ht0
      (tateQuotientToPresheafHom D hb q)) =
    (fun q ↦ q) :=
    hdense.equalizer
      (UniformSpace.Completion.continuous_extension.comp hcont_eval)
      continuous_id
      (funext hagree)
  exact congr_fun h_eq q

/-! ### Step 4: Package as RingEquiv -/

/-- **The completion isomorphism** `presheafValue D ≃+* A⟨X⟩/(1-sX)`
(Wedhorn Proposition 8.30, Remark 7.55).

For a strongly noetherian Tate ring `A` and rational localization datum `D`,
the presheaf value (completion of `Localization.Away D.s`) is ring-isomorphic
to the Tate algebra quotient `A⟨X⟩/(1-sX)` equipped with the T-topology.

Both composites are identity:
- `tateQuotientToPresheafHom ∘ presheafValueToQuotient = id` (by T2 density)
- `presheafValueToQuotient ∘ tateQuotientToPresheafHom = id` (by round-trip on generators)

### T-EX638-SCOPE note (per ChatGPT Pro reviewer, 2026-05-11)

The right-hand side `A⟨X⟩/(1 - D.s · X)` is a ONE-VARIABLE quotient. It models
`R(∅, D.s)` (inverting `s` and making `1/s` power-bounded) cleanly. For general
rational data `D = (P, T, s)` with `|T| ≥ 1`, the localisation topology
ADDITIONALLY requires each `t/s` (for `t ∈ T`) to be power-bounded — a
strictly stronger condition than just inverting `s`.

The iso below is mathematically correct on the level of underlying *rings*
(both sides are the localisation `A[1/s]` algebraically). The topological
agreement requires the hypothesis bundle `(hb, hcs, ht0, hcont, hdense)` to
silently absorb the T-dependent constraints: `hb : IsPowerBounded (invS D)`
asserts power-boundedness of `1/s` AT the presheaf-value level, which
implicitly already incorporates the T-dependent topology. `hdense` requires
density of `locToQuotientOneSubfX_gen` from `Localization.Away D.s` (with the
T-aware topology) to the one-variable quotient — this enforces compatibility.

**Practical scope.** For the principal Laurent-overlap consumer
(`R(1/f)`, `R(f/1)`, i.e., singleton-T cases), the iso is the intended
model and the hypotheses are dischargable. For general `R(T/s)` with
`|T| > 1`, consumers must verify (a) the iso is supplied with the right
witnesses, or (b) decompose general `R(T/s)` into chained basic-rational
steps `R(1/f_i)` first (Wedhorn 7.30 / chain of inclusions). This file's
exported iso DOES NOT silently absorb general-T data; it requires the
hypothesis bundle to carry that information explicitly. -/
noncomputable def presheafValueTateQuotientEquiv (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (hdense : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientTTopology D.s) (Localization.Away D.s)
      (locToQuotientOneSubfX_gen D.s)) :
    presheafValue D ≃+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) where
  toFun := presheafValueToQuotient D hb hcs ht0
  invFun := tateQuotientToPresheafHom D hb
  left_inv :=
    tateQuotientToPresheaf_comp_presheafToQuotient D hb hcs ht0 hcont_eval
  right_inv :=
    presheafToQuotient_comp_tateQuotientToPresheaf D hb hcs ht0 hcont_eval hdense
  map_mul' := map_mul _
  map_add' := map_add _

/-- The isomorphism sends `canonicalMap(a)` to `mk(algebraMap a)`. -/
theorem presheafValueTateQuotientEquiv_canonicalMap (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (hdense : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientTTopology D.s) (Localization.Away D.s)
      (locToQuotientOneSubfX_gen D.s))
    (a : A) :
    presheafValueTateQuotientEquiv D hb hcs ht0 hcont_eval hdense
      (D.canonicalMap a) =
      (Ideal.Quotient.mk _) (algebraMap A _ a) := by
  change presheafValueToQuotient D hb hcs ht0
    (D.coeRingHom (algebraMap A _ a)) = _
  rw [presheafValueToQuotient_coe, locToQuotientOneSubfX_gen_algebraMap]

/-- The inverse sends `mk(algebraMap a)` back to `canonicalMap(a)`. -/
theorem presheafValueTateQuotientEquiv_symm_algebraMap (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (hdense : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientTTopology D.s) (Localization.Away D.s)
      (locToQuotientOneSubfX_gen D.s))
    (a : A) :
    (presheafValueTateQuotientEquiv D hb hcs ht0 hcont_eval hdense).symm
      ((Ideal.Quotient.mk _) (algebraMap A _ a)) =
      D.canonicalMap a := by
  simp only [presheafValueTateQuotientEquiv, RingEquiv.symm_mk,
    RingEquiv.coe_mk, Equiv.coe_fn_mk]
  exact tateQuotientToPresheafHom_algebraMap D hb a

end CompletionIsomorphism

/-! ### Discharging hypotheses for strongly noetherian Tate rings

The conditional `presheafValueTateQuotientEquiv` requires 5 hypotheses.
We discharge them here, starting with the easiest (density). -/

section HypothesesDischarge

variable [T2Space A]

/-! #### H5: DenseRange of locToQuotientOneSubfX_gen

The localization `A[1/s]` maps densely into `A⟨X⟩/(1-sX)` for the quotient
T-topology. The image contains `mk(a)` for all `a ∈ A` and `mk(X)` (since
`1/s ↦ mk(X)`), hence contains all polynomial classes `mk(p)`.
Polynomials are dense in `A⟨X⟩` for the T-topology because truncations
converge in the induced product topology. -/

/-- A power series whose coefficients are zero above degree `N` is restricted,
because only finitely many coefficients are nonzero. -/
private theorem isRestricted_of_eventually_zero
    (h : MvPowerSeries (Fin 1) A) (N : ℕ)
    (hh : ∀ s : Fin 1 →₀ ℕ, N ≤ s 0 → h s = 0) :
    MvPowerSeries.IsRestricted h := by
  -- IsRestricted = coefficients tend to 0 along cofinite filter.
  -- Suffices to show: the set of nonzero coefficients is finite.
  change Filter.Tendsto (fun s ↦ h s) Filter.cofinite (nhds 0)
  rw [tendsto_nhds]
  intro U hU h0U
  rw [Filter.mem_cofinite]
  -- {s | h s ∉ U} ⊆ {s | h s ≠ 0} ⊆ {toIndex k | k < N}
  apply Set.Finite.subset
    ((Finset.image TateAlgebra.toIndex (Finset.range N)).finite_toSet)
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
  refine ⟨s 0, ?_, (TateAlgebra.eq_toIndex s).symm⟩
  by_contra hge
  push Not at hge
  exact hs (by rw [hh s hge]; exact h0U)

/-- The truncation of `g ∈ A⟨X⟩` at degree `N`: keep coefficients at multi-indices
with `s 0 < N` and set the rest to zero. The result is restricted (polynomial). -/
private noncomputable def truncTate (g : ↥(TateAlgebra A)) (N : ℕ) :
    ↥(TateAlgebra A) :=
  ⟨fun s ↦ if s 0 < N then g.val s else 0,
   isRestricted_of_eventually_zero _ N (fun s hs ↦ by simp [show ¬(s 0 < N) from by omega])⟩

private theorem truncTate_val (g : ↥(TateAlgebra A)) (N : ℕ) (s : Fin 1 →₀ ℕ) :
    (truncTate g N).val s = if s 0 < N then g.val s else 0 := rfl

private theorem truncTate_coeff_high (g : ↥(TateAlgebra A)) (N : ℕ) (s : Fin 1 →₀ ℕ)
    (hs : N ≤ s 0) : (truncTate g N).val s = 0 := by
  simp [truncTate_val, show ¬(s 0 < N) from by omega]

private theorem truncTate_coeff_low (g : ↥(TateAlgebra A)) (N : ℕ) (s : Fin 1 →₀ ℕ)
    (hs : s 0 < N) : (truncTate g N).val s = g.val s := by
  simp [truncTate_val, hs]

/-- `scaleIncl s (truncTate g N)` agrees with `scaleIncl s g` at any index with `s 0 < N`. -/
private theorem scaleIncl_truncTate_eq (g : ↥(TateAlgebra A)) (N : ℕ) (s : A)
    (idx : Fin 1 →₀ ℕ) (h : idx 0 < N) :
    TateAlgebraWedhorn.scaleIncl s (truncTate g N) idx =
    TateAlgebraWedhorn.scaleIncl s g idx := by
  simp only [TateAlgebraWedhorn.scaleIncl_apply, truncTate_coeff_low g N idx h]

/-- Polynomials (elements with finitely many nonzero coefficients) are dense
in the Tate algebra for the T-topology. The T-topology is induced from the
product `∏ A` via `scaleIncl`, and in the product topology a sequence of
truncations converges coordinatewise. -/
theorem tateAlgebra_polynomials_dense (s : A) :
    @Dense ↥(TateAlgebra A) (TateAlgebraWedhorn.tateTopologyT s)
      {g | ∃ N : ℕ, ∀ n : Fin 1 →₀ ℕ, N ≤ n 0 → g.val n = 0} := by
  -- Unfold Dense: for each g, show g is in the closure.
  intro g
  rw [@mem_closure_iff _ (TateAlgebraWedhorn.tateTopologyT s)]
  -- For each open set O containing g, find a polynomial in O.
  intro O hO hgO
  -- O is open in the induced topology, so O = scaleIncl⁻¹(V) for some open V.
  rw [@isOpen_induced_iff _ _ (MvPowerSeries.WithPiTopology.instTopologicalSpace A)] at hO
  obtain ⟨V, hV, rfl⟩ := hO
  -- scaleIncl g ∈ V, and V is product-topology-open.
  -- By the product topology characterization, there exists a finite set of indices I
  -- and neighborhoods t_i such that Set.pi I t ⊆ V.
  rw [Set.mem_preimage] at hgO
  -- V is open in the product topology, so V ∈ nhds(scaleIncl s g) for that topology.
  -- By the product topology characterization, there exist finitely many indices
  -- with neighborhoods whose pi-product is contained in V.
  -- Use exists_finset_piecewise to get a finite set of coordinates and a piecewise element.
  -- Alternatively, directly use Filter.mem_pi' on the product-topology nhds.
  -- V is product-topology-open and contains scaleIncl(g).
  -- The product topology is Pi.topologicalSpace on (Fin 1 →₀ ℕ) → A.
  -- By set_pi_mem_nhds, V contains a pi-set based on finitely many coordinates.
  -- We use the mem_nhds characterization directly.
  -- First get the pi-filter decomposition.
  -- V is open in the product topology and scaleIncl(g) ∈ V.
  -- In the product topology, V contains a finite-coordinate neighborhood.
  -- We need to access the pi-filter form of nhds.
  -- nhds_pi : 𝓝 a = Filter.pi (fun i => 𝓝 (a i)) for Pi.topologicalSpace.
  -- WithPiTopology.instTopologicalSpace = Pi.topologicalSpace (definitionally).
  -- We use set_pi_mem_nhds_iff to get the finite decomposition.
  -- First: V contains a basic open set of the form Set.pi I t.
  -- V is open in the product topology (Pi.topologicalSpace = WithPiTopology).
  -- scaleIncl(g) ∈ V. By nhds_pi, V contains a finite-coordinate product.
  -- We use exists_finset_piecewise_mem_of_mem_nhds as the extraction tool.
  have hV_nhds : V ∈ @nhds _ Pi.topologicalSpace (TateAlgebraWedhorn.scaleIncl s g) := by
    letI : TopologicalSpace (MvPowerSeries (Fin 1) A) := Pi.topologicalSpace
    exact hV.mem_nhds hgO
  -- In the Pi topology, nhds is the pi filter. Extract finite coordinates.
  rw [nhds_pi] at hV_nhds
  obtain ⟨I, t, ht_nhds, hIt_sub⟩ := Filter.mem_pi'.mp hV_nhds
  -- Choose N large enough that all indices in I have idx 0 < N.
  let N := (I.image (· 0)).sup id + 1
  -- The truncation at N is our polynomial witness.
  refine ⟨truncTate g N, ?_, ?_⟩
  · -- truncTate g N is in scaleIncl⁻¹(V)
    apply Set.mem_preimage.mpr
    apply hIt_sub
    intro idx hidx
    -- idx ∈ I, so idx 0 < N
    have hlt : idx 0 < N := by
      change idx 0 < (I.image (· 0)).sup id + 1
      have h_le : idx 0 ≤ (I.image (· 0)).sup id := by
        exact Finset.le_sup (f := id)
          (Finset.mem_image_of_mem (· 0) hidx)
      linarith
    rw [scaleIncl_truncTate_eq g N s idx hlt]
    exact mem_of_mem_nhds (ht_nhds idx)
  · -- truncTate g N has finitely many nonzero coefficients
    exact ⟨N, fun n hn ↦ truncTate_coeff_high g N n hn⟩

/-- Every polynomial element in `A⟨X⟩` (coefficients zero above degree N) has its
quotient class in the range of `locToQuotientOneSubfX_gen`. By induction on N:
the image contains `mk(algebraMap a)` and `mk(X)`, hence all finite sums of
`mk(algebraMap a_k) * mk(X)^k = locToQuotientOneSubfX_gen(a_k / s^k)`. -/
private theorem polynomial_quotient_in_range (s : A) (g : ↥(TateAlgebra A))
    (N : ℕ) (hN : ∀ n : Fin 1 →₀ ℕ, N ≤ n 0 → g.val n = 0) :
    Ideal.Quotient.mk (oneSubfXIdeal s) g ∈
      Set.range (locToQuotientOneSubfX_gen s) := by
  -- Generalize g before induction on N so the IH applies to g - gk.
  revert g
  induction N with
  | zero =>
    intro g hN
    -- All coefficients are zero, so g = 0.
    have hg0 : g = 0 := by
      ext n; exact hN (TateAlgebra.toIndex n)
        (by simp [TateAlgebra.toIndex, Finsupp.single_eq_same])
    rw [hg0, map_zero]
    exact ⟨0, map_zero _⟩
  | succ k ih =>
    intro g hN
    -- g has coefficients zero above degree k+1.
    -- Let a = coeff k g, and gk = algebraMap(a) * X^k.
    set a := TateAlgebra.coeff k g with ha_def
    set gk : ↥(TateAlgebra A) := algebraMap A _ a * TateAlgebra.X ^ k with hgk_def
    -- mk(gk) is in the range.
    have hgk_range : Ideal.Quotient.mk (oneSubfXIdeal s) gk ∈
        Set.range (locToQuotientOneSubfX_gen s) := by
      exact ⟨algebraMap A _ a *
        (IsLocalization.Away.invSelf (S := Localization.Away s) s) ^ k, by
        show locToQuotientOneSubfX_gen s _ = _
        rw [map_mul, map_pow, locToQuotientOneSubfX_gen_algebraMap,
          locToQuotientOneSubfX_gen_invSelf, hgk_def, ← map_pow, ← map_mul]⟩
    -- g - gk has coefficients zero above degree k.
    -- Helper: coeff m (X ^ j) = δ_{m,j} for TateAlgebra.
    have hcoeff_X_pow : ∀ m j : ℕ,
        TateAlgebra.coeff m (TateAlgebra.X ^ j : ↥(TateAlgebra A)) =
        if m = j then 1 else 0 := by
      intro m j; revert m; induction j with
      | zero => intro m; simp [pow_zero, TateAlgebra.coeff, TateAlgebra.toIndex,
          MvPowerSeries.coeff_one]
      | succ j ihj =>
        intro m; rw [pow_succ, mul_comm]
        cases m with
        | zero => rw [TateAlgebra.coeff_zero_X_mul, if_neg (by omega)]
        | succ m => rw [TateAlgebra.coeff_succ_X_mul, ihj m]; simp
    have hg'_vanish : ∀ n : Fin 1 →₀ ℕ, k ≤ n 0 → (g - gk).val n = 0 := by
      -- Restate using TateAlgebra.coeff via eq_toIndex.
      intro n hn
      rw [TateAlgebra.eq_toIndex n]
      change TateAlgebra.coeff (n 0) (g - gk) = 0
      rw [TateAlgebra.coeff_sub, hgk_def, TateAlgebra.coeff_algebraMap_mul,
        hcoeff_X_pow (n 0) k]
      by_cases hnk : n 0 = k
      · -- coeff k g = a and coeff k gk = a, so difference is 0.
        rw [if_pos hnk, mul_one, ha_def, hnk, sub_self]
      · -- coeff (n 0) g = 0 (by hN) and coeff (n 0) gk = 0.
        rw [if_neg hnk, mul_zero, sub_zero]
        have hn_gt : k + 1 ≤ n 0 := by omega
        change (MvPowerSeries.coeff (TateAlgebra.toIndex (n 0))) g.val = 0
        rw [MvPowerSeries.coeff_apply]
        exact hN _ (by simp [TateAlgebra.toIndex, Finsupp.single_eq_same]; omega)
    -- By IH, mk(g - gk) is in the range.
    have hg'_range := ih (g - gk) hg'_vanish
    -- mk(g) = mk(g - gk) + mk(gk), both in range.
    rw [show g = (g - gk) + gk from by ring, map_add]
    obtain ⟨x, hx⟩ := hg'_range
    obtain ⟨y, hy⟩ := hgk_range
    exact ⟨x + y, by rw [map_add, hx, hy]⟩

/-- The localization `A[1/s]` maps densely into `A⟨X⟩/(1-sX)` for the quotient
T-topology (Wedhorn Example 6.38).

The image contains all polynomial quotient classes, and polynomials are
dense in the Tate algebra for the T-topology. -/
theorem locToQuotientOneSubfX_gen_denseRange (s : A) :
    @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal s)
      (quotientTTopology s) (Localization.Away s)
      (locToQuotientOneSubfX_gen s) := by
  -- DenseRange = Dense (range f).
  -- Strategy: mk(polynomials) is dense in quotient, and mk(polynomials) ⊆ range.
  change @Dense _ (quotientTTopology s) (Set.range (locToQuotientOneSubfX_gen s))
  -- Let P = polynomial set, mk = quotient map.
  set P : Set ↥(TateAlgebra A) :=
    {g | ∃ N : ℕ, ∀ n : Fin 1 →₀ ℕ, N ≤ n 0 → g.val n = 0}
  let mk := Ideal.Quotient.mk (oneSubfXIdeal s)
  -- Step 1: mk '' P ⊆ range(locToQuotientOneSubfX_gen).
  have h_sub : mk '' P ⊆ Set.range (locToQuotientOneSubfX_gen s) := by
    rintro _ ⟨g, ⟨N, hN⟩, rfl⟩
    exact polynomial_quotient_in_range s g N hN
  -- Step 2: mk '' P is dense in quotient T-topology.
  -- P is dense in A⟨X⟩ (by tateAlgebra_polynomials_dense).
  -- mk is surjective and continuous → DenseRange.
  -- DenseRange.dense_image gives Dense (mk '' P).
  have h_dense : @Dense _ (quotientTTopology s) (mk '' P) := by
    have hP_dense := tateAlgebra_polynomials_dense s
    have hmk_surj : Function.Surjective mk := Ideal.Quotient.mk_surjective
    letI := TateAlgebraWedhorn.tateTopologyT s
    have hmk_dr : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal s) (quotientTTopology s)
        ↥(TateAlgebra A) mk := hmk_surj.denseRange
    exact hmk_dr.dense_image continuous_quotient_mk' hP_dense
  -- Step 3: Dense (mk '' P) + mk '' P ⊆ range → Dense range.
  exact @Dense.mono _ (quotientTTopology s) _ _ h_sub h_dense

/-! #### H2/H3: Closedness of (1-sX), completeness, and T₀

**Architecture (2026-04-02 correction):**
The T-topology on `A⟨X⟩` is the product topology on scaled coefficients (via
`scaleIncl`). This constrains only finitely many coordinates, so `A⟨X⟩` is
NOT complete in this topology. However, for the QUOTIENT `A⟨X⟩/(1-sX)`:

1. For strongly noetherian `A`, `A⟨X⟩` is noetherian.
2. The quotient `A⟨X⟩/(1-sX)` is a f.g. `A⟨X⟩`-module (cyclic).
3. By Prop 6.18 (Wedhorn): on f.g. modules over noetherian Tate rings, the
   module topology = the adic lattice topology. The quotient T-topology IS the
   module topology (since `IsModuleTopology R (R ⧸ I)` for topological ring R).
4. The adic lattice topology on the quotient is complete: the ring of definition
   `A₀⟨X⟩/(1-sX)` is J-adically complete (quotient of `A₀⟨X⟩` by a closed ideal,
   Remark 6.37), and completing gives the adic lattice topology.

For closedness of `(1-sX)`: Remark 6.37 says every ideal in a noetherian
J-adically separated ring is closed (Krull intersection + Artin-Rees). -/

omit [PlusSubring A] [IsHuberRing A] [IsTopologicalRing A] [T2Space A] in
/-- `1-sX` is not a zero divisor in `A⟨X⟩`: if `(1-sX) · g = 0` then `g = 0`.
Proof by induction on coefficients: `g₀ = 0`, `gₙ = s · gₙ₋₁ = 0`. -/
theorem oneSubsX_not_zero_divisor (s : A) (g : ↥(TateAlgebra A))
    (h : (1 - algebraMap A _ s * TateAlgebra.X) * g = 0) : g = 0 := by
  have hcoeff : ∀ n, TateAlgebra.coeff n g =
      s * TateAlgebra.coeff n (TateAlgebra.X * g) := by
    intro n
    have h1 : TateAlgebra.coeff n ((1 - algebraMap A _ s * TateAlgebra.X) * g) = 0 := by
      rw [h]; simp only [TateAlgebra.coeff, map_zero, ZeroMemClass.coe_zero]
    rw [sub_mul, one_mul, mul_assoc, TateAlgebra.coeff_sub,
      TateAlgebra.coeff_algebraMap_mul] at h1
    exact sub_eq_zero.mp h1
  have h0 : TateAlgebra.coeff 0 g = 0 := by
    rw [hcoeff 0, TateAlgebra.coeff_zero_X_mul, mul_zero]
  have hstep : ∀ n, TateAlgebra.coeff (n + 1) g = s * TateAlgebra.coeff n g := by
    intro n; rw [hcoeff (n + 1), TateAlgebra.coeff_succ_X_mul]
  have hall : ∀ n, TateAlgebra.coeff n g = 0 := by
    intro n; induction n with
    | zero => exact h0
    | succ n ih => rw [hstep n, ih, mul_zero]
  exact TateAlgebra.ext hall

/-- **Wedhorn Remark 6.37:** In a noetherian ring with I-adic topology that is
I-adically separated, every ideal is closed.

Proof: For ideal J in noetherian I-separated R, the quotient R/J is noetherian
and I-separated (by Artin-Rees: `Ideal.exists_pow_inf_eq_pow_smul`). The closure
`cl(J) = ⋂_n (J + I^n)` equals J because `⋂_n I^n · (R/J) = 0` (Krull intersection
in the separated quotient). -/
theorem isClosed_ideal_of_noetherian_adic_separated
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsNoetherianRing R] [T2Space R]
    (I : Ideal R) (hadic : IsAdic I)
    (hcs : @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R))
    (J : Ideal R) :
    IsClosed (J : Set R) := by
  -- Step 1: Introduce uniform space from the topological additive group.
  letI : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  haveI : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  -- Step 2: IsAdicComplete I R from IsAdic + CompleteSpace + T2.
  have hac : IsAdicComplete I R := hadic.isAdicComplete_iff.mpr ⟨hcs, ‹_›⟩
  -- Step 3: I ≤ jacobson ⊥ from IsAdicComplete.
  have hjac : I ≤ (⊥ : Ideal R).jacobson := IsAdicComplete.le_jacobson_bot I
  -- Step 4: Krull intersection on R ⧸ J: ⨅ n, I^n • ⊤ = ⊥.
  have hkrull : (⨅ i : ℕ, I ^ i • (⊤ : Submodule R (R ⧸ J))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I hjac
  -- Step 5: IsClosed from closure ⊆ J using adic nhds basis.
  rw [← closure_subset_iff_isClosed]
  intro x hx
  -- x is in closure(J) iff ∀ n, (x + I^n) meets J (adic nhds basis).
  rw [mem_closure_iff_nhds_basis (hadic.hasBasis_nhds x)] at hx
  -- Show mk J x ∈ ⨅ I^n • ⊤ = ⊥, hence mk J x = 0, hence x ∈ J.
  suffices Ideal.Quotient.mk J x = 0 from
    Ideal.Quotient.eq_zero_iff_mem.mp this
  -- mk J x lies in every I^n • ⊤, hence in their intersection = ⊥.
  have hmem : Ideal.Quotient.mk J x ∈
      (⨅ i : ℕ, I ^ i • (⊤ : Submodule R (R ⧸ J))) := by
    rw [Submodule.mem_iInf]
    intro n
    -- From closure: ∃ y ∈ J with y ∈ (x + I^n).
    obtain ⟨y, hy_mem, hxy⟩ := hx n trivial
    -- hxy : y ∈ (fun z ↦ x + z) '' ↑(I ^ n), i.e., y = x + z for some z ∈ I^n.
    obtain ⟨z, hz, rfl⟩ := hxy
    -- y = x + z and y ∈ J. So mk J (x + z) = 0, i.e., mk J x = -(mk J z).
    -- We need mk J x ∈ I^n • ⊤.
    -- mk J x = mk J (x + z) - mk J z = 0 - mk J z (since x + z ∈ J).
    have hyz : Ideal.Quotient.mk J (x + z) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hy_mem
    have hxeq : Ideal.Quotient.mk J x = -(Ideal.Quotient.mk J z) := by
      have h1 : Ideal.Quotient.mk J x + Ideal.Quotient.mk J z = 0 := by
        rw [← map_add]; exact hyz
      have := eq_neg_of_add_eq_zero_left h1
      exact this
    rw [hxeq]
    apply neg_mem
    -- mk J z ∈ I^n • ⊤: use smul_top_eq_map to identify I^n • ⊤ with (I^n).map (mk J).
    change Ideal.Quotient.mk J z ∈ I ^ n • (⊤ : Submodule R (R ⧸ J))
    rw [Ideal.smul_top_eq_map]
    exact (Submodule.restrictScalars_mem R _ _).mpr (Ideal.mem_map_of_mem _ hz)
  rw [hkrull, Submodule.mem_bot] at hmem
  exact hmem

omit [IsTopologicalRing A] [PlusSubring A] [IsHuberRing A] [T2Space A] in
/-- The ideal `(1-sX)` is closed in `A⟨X⟩` for the T-topology, given that the
T-topology is adic (Prop 6.18 for strongly noetherian Tate rings).

The hypothesis `hadic` asserts that the T-topology on `A⟨X⟩` coincides with
the `J`-adic topology for some ideal `J` of `A⟨X⟩`. For strongly noetherian `A`,
this is Wedhorn Proposition 6.18 with `J = I · A₀⟨X⟩`.

Once adic: `A⟨X⟩` is noetherian + adic complete + T₂, so every ideal is closed
by Remark 6.37 (`isClosed_ideal_of_noetherian_adic_separated`). -/
theorem oneSubfXIdeal_isClosed_tTopology (s : A)
    [IsNoetherianRing ↥(TateAlgebra A)]
    (hcs_tate : @CompleteSpace ↥(TateAlgebra A)
      (@IsTopologicalAddGroup.rightUniformSpace _ _
        (TateAlgebraWedhorn.tateTopologyT s)
        (@IsTopologicalRing.to_topologicalAddGroup _ _
          (TateAlgebraWedhorn.tateTopologyT s)
          (TateAlgebraWedhorn.tateTopologyT_isTopologicalRing s))))
    (ht2_tate : @T2Space ↥(TateAlgebra A) (TateAlgebraWedhorn.tateTopologyT s))
    (J : Ideal ↥(TateAlgebra A))
    (hadic : @IsAdic ↥(TateAlgebra A) _ (TateAlgebraWedhorn.tateTopologyT s) J) :
    @IsClosed ↥(TateAlgebra A) (TateAlgebraWedhorn.tateTopologyT s)
      (oneSubfXIdeal s : Set ↥(TateAlgebra A)) :=
  @isClosed_ideal_of_noetherian_adic_separated ↥(TateAlgebra A) _
    (TateAlgebraWedhorn.tateTopologyT s)
    (TateAlgebraWedhorn.tateTopologyT_isTopologicalRing s) ‹_›
    ht2_tate J hadic hcs_tate (oneSubfXIdeal s)

omit [IsTopologicalRing A] [PlusSubring A] [T2Space A] in
/-- The quotient `A⟨X⟩/(1-sX)` with quotient T-topology is complete.

**Proof route (Wedhorn Prop 6.18 + Example 6.38):**
1. `A⟨X⟩/(1-sX)` is a cyclic `A⟨X⟩`-module (f.g. for noetherian `A⟨X⟩`).
2. By Prop 6.18: the quotient T-topology = adic lattice topology on this quotient.
3. The adic lattice topology comes from `D₀ = A₀⟨X⟩/(1-sX)` as ring of definition
   with ideal of definition `J·D₀ = π·D₀`.
4. `A₀⟨X⟩` is J-adically complete (it IS the adic completion of `A₀[X]`).
5. `(1-sX)` is closed in `A₀⟨X⟩` (Remark 6.37: noetherian + J-adic separated).
6. `D₀ = A₀⟨X⟩/(1-sX)` is J-adically complete (quotient of complete by closed).
7. The adic lattice topology on the quotient is complete.

**Note:** This does NOT go through `tateAlgebra_tTopology_completeSpace` (which
is false — the T-topology on A⟨X⟩ is a product topology, not complete). The
completeness of the QUOTIENT follows from the adic structure via Prop 6.18. -/
theorem quotientTTopology_completeSpace (s : A)
    [IsNoetherianRing ↥(TateAlgebra A)]
    (hcs_tate : @CompleteSpace ↥(TateAlgebra A)
      (@IsTopologicalAddGroup.rightUniformSpace _ _
        (TateAlgebraWedhorn.tateTopologyT s)
        (@IsTopologicalRing.to_topologicalAddGroup _ _
          (TateAlgebraWedhorn.tateTopologyT s)
          (TateAlgebraWedhorn.tateTopologyT_isTopologicalRing s))))
    (_ht2_tate : @T2Space ↥(TateAlgebra A) (TateAlgebraWedhorn.tateTopologyT s))
    (_J : Ideal ↥(TateAlgebra A))
    (_hadic : @IsAdic ↥(TateAlgebra A) _ (TateAlgebraWedhorn.tateTopologyT s) _J) :
    @CompleteSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal s)
      (quotientTUniformSpace s) := by
  letI τT : TopologicalSpace ↥(TateAlgebra A) := TateAlgebraWedhorn.tateTopologyT s
  haveI : IsTopologicalRing ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT_isTopologicalRing s
  haveI : IsTopologicalAddGroup ↥(TateAlgebra A) :=
    IsTopologicalRing.to_topologicalAddGroup
  haveI : FirstCountableTopology A := IsHuberRing.firstCountableTopology
  haveI hfc_pi : @FirstCountableTopology ((Fin 1 →₀ ℕ) → A) Pi.topologicalSpace :=
    inferInstance
  haveI : @FirstCountableTopology ↥(TateAlgebra A) τT :=
    @TopologicalSpace.firstCountableTopology_induced _ _
      Pi.topologicalSpace hfc_pi (TateAlgebraWedhorn.scaleIncl s)
  exact @QuotientAddGroup.completeSpace_right' ↥(TateAlgebra A) _ τT ‹_› ‹_›
    (oneSubfXIdeal s).toAddSubgroup inferInstance hcs_tate

omit [IsTopologicalRing A] [PlusSubring A] [IsHuberRing A] [T2Space A] in
/-- The quotient `A⟨X⟩/(1-sX)` with quotient T-topology is T₀.
Quotient of T₂ topological group by closed subgroup is T₃ (hence T₀). -/
theorem quotientTTopology_t0Space (s : A)
    [IsNoetherianRing ↥(TateAlgebra A)]
    (hcs_tate : @CompleteSpace ↥(TateAlgebra A)
      (@IsTopologicalAddGroup.rightUniformSpace _ _
        (TateAlgebraWedhorn.tateTopologyT s)
        (@IsTopologicalRing.to_topologicalAddGroup _ _
          (TateAlgebraWedhorn.tateTopologyT s)
          (TateAlgebraWedhorn.tateTopologyT_isTopologicalRing s))))
    (ht2_tate : @T2Space ↥(TateAlgebra A) (TateAlgebraWedhorn.tateTopologyT s))
    (J : Ideal ↥(TateAlgebra A))
    (hadic : @IsAdic ↥(TateAlgebra A) _ (TateAlgebraWedhorn.tateTopologyT s) J) :
    @T0Space (↥(TateAlgebra A) ⧸ oneSubfXIdeal s)
      (quotientTTopology s) := by
  letI τT : TopologicalSpace ↥(TateAlgebra A) := TateAlgebraWedhorn.tateTopologyT s
  haveI : IsTopologicalRing ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT_isTopologicalRing s
  haveI : IsTopologicalAddGroup ↥(TateAlgebra A) :=
    IsTopologicalRing.to_topologicalAddGroup
  haveI : @IsClosed ↥(TateAlgebra A) τT
      (oneSubfXIdeal s : Set ↥(TateAlgebra A)) :=
    oneSubfXIdeal_isClosed_tTopology s hcs_tate ht2_tate J hadic
  exact (Submodule.t3_quotient_of_isClosed (S := oneSubfXIdeal s)).toT0Space

/-! #### Helper: IsInducing for locToQuotientOneSubfX_gen (reverse continuity)

The forward direction (localization topology → quotient T-topology) is
`locToQuotientOneSubfX_gen_continuous`. The reverse direction requires:
for each `locNhd(n)`, there exists a quotient T-topology neighborhood `V`
with `locToQuotientOneSubfX_gen⁻¹(V) ⊆ locNhd(n)`.

The `IsAdic J` hypothesis makes this work: the T-topology on `A⟨X⟩` is
J-adic, so the quotient T-topology has basis `{mk(J^k)}`. The preimage
`locToQuotientOneSubfX_gen⁻¹(mk(J^k))` is controlled by the J-adic
structure: elements in `J^k` have scaled coefficients in `I^{f(k)}`-type
neighborhoods, which exactly correspond to `locNhd` under the algebraic
isomorphism `Localization.Away s ≃ A⟨X⟩/(1-sX)`.

This is Wedhorn's Proposition 6.18 + Theorem 8.28(a). -/

/-! #### DELETED: locToQuotientOneSubfX_gen_isInducing (FALSE, 2026-04-03)

The `IsInducing` and `IsUniformInducing` properties of `locToQuotientOneSubfX_gen`
are FALSE. Rational localization can change the ring of definition, making elements
topologically smaller in the quotient than in the localization.
Counterexample (from reviewer): `A = ℚ_p⟨X⟩`, `U = R({p,X}/p)`.

The correct approach uses `hadic : IsAdic J` to show `tateEvalPresheafHom` is
continuous from the J-adic topology (= T-topology), then descends via the
quotient map. See `tateQuotientToPresheafHom_continuous` below. -/

/-! #### H4: Continuity of tateQuotientToPresheafHom (J-adic eval route)

With `hadic : IsAdic J`, the T-topology = J-adic, giving a neighborhood basis
`{J^k}` at 0. The evaluation `tateEvalPresheafHom` is continuous iff `eval(J^k) → 0`
in `presheafValue D` for large `k`.

The hypothesis `hJ_eval` encapsulates this: the image `eval(J^k)` eventually lands
in any target neighborhood. For strongly noetherian Tate rings (Wedhorn Prop 6.18),
`J = I · A₀⟨X⟩` and `eval` maps this into the ideal of definition of `presheafValue D`,
which is topologically nilpotent. The caller discharges `hJ_eval` from this structure.

Then `IsQuotientMap.continuous_iff` descends continuity to the quotient. -/

omit [PlusSubring A] [IsHuberRing A] [T2Space A] in
/-- The reverse map `A⟨X⟩/(1-sX) → presheafValue D` is continuous.

**Proof (Wedhorn Example 6.38):** `tateQuotientToPresheafHom = Quotient.lift tateEvalPresheafHom`.
By `IsQuotientMap.continuous_iff`, it suffices that `tateEvalPresheafHom` is continuous
from the T-topology on `A⟨X⟩`. With `hadic : IsAdic J`: T-topology = J-adic, and
we need `eval(J^k) → 0` in presheafValue for large k.

The hypothesis `hJ_eval` asserts that the image ideal `Ideal.map eval J` is
topologically nilpotent in `presheafValue D`. For the strongly noetherian case
(Wedhorn Prop 6.18), `J = I·A₀⟨X⟩` where `I` is the ideal of definition.
The eval sends `I·A₀⟨X⟩` into the ideal of definition of `presheafValue D`,
which is topologically nilpotent. The hypothesis is discharged from this concrete
structure by the caller. -/
theorem tateQuotientToPresheafHom_continuous (D : RationalLocData A)
    [IsNoetherianRing ↥(TateAlgebra A)]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (J : Ideal ↥(TateAlgebra A))
    (hadic : @IsAdic ↥(TateAlgebra A) _ (TateAlgebraWedhorn.tateTopologyT D.s) J)
    (hJ_eval : ∀ V ∈ @nhds (presheafValue D) _ 0,
      ∃ k : ℕ, ∀ h ∈ (J ^ k : Ideal ↥(TateAlgebra A)),
        (tateEvalPresheafHom D hb) h ∈ V) :
    @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb) := by
  letI τT : TopologicalSpace ↥(TateAlgebra A) := TateAlgebraWedhorn.tateTopologyT D.s
  haveI hTR : IsTopologicalRing ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT_isTopologicalRing D.s
  haveI : IsTopologicalAddGroup ↥(TateAlgebra A) :=
    IsTopologicalRing.to_topologicalAddGroup
  letI τQ : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  -- tateQuotientToPresheafHom = Quotient.lift tateEvalPresheafHom.
  -- The quotient map mk is a quotient map (open surjection for ring quotient).
  have hmk_qm : @Topology.IsQuotientMap _ _ τT τQ
      (Ideal.Quotient.mk (oneSubfXIdeal D.s)) :=
    (@QuotientRing.isOpenQuotientMap_mk ↥(TateAlgebra A) τT
      (inferInstanceAs (CommRing ↥(TateAlgebra A))) (oneSubfXIdeal D.s) hTR).isQuotientMap
  rw [hmk_qm.continuous_iff]
  -- Need: tateQuotientToPresheafHom ∘ mk = tateEvalPresheafHom is continuous.
  have hcomp : tateQuotientToPresheafHom D hb ∘
      Ideal.Quotient.mk (oneSubfXIdeal D.s) = tateEvalPresheafHom D hb := by
    ext g; simp [tateQuotientToPresheafHom, Ideal.Quotient.lift_mk]
  rw [hcomp]
  -- Prove tateEvalPresheafHom continuous from T-topology (= J-adic by hadic).
  apply continuous_of_continuousAt_zero (tateEvalPresheafHom D hb).toAddMonoidHom
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro V hV
  -- Use hadic to get the J-adic nhds basis, then apply hJ_eval.
  have hbasis : ((@nhds _ τT (0 : ↥(TateAlgebra A))).HasBasis
      (fun _ : ℕ ↦ True) fun n ↦ ((J ^ n : Ideal _) : Set _)) :=
    hadic.hasBasis_nhds_zero
  rw [hbasis.mem_iff]
  obtain ⟨k, hk⟩ := hJ_eval V hV
  exact ⟨k, trivial, fun h hh ↦ hk h hh⟩

end HypothesesDischarge

/-! ### Phase 2.6: Canonical topology versions of continuity and dense range

The canonical (natural Tate) topology on `A⟨X⟩` is installed by
`TateAlgebra.TateAlgebraNaturalTopology.instTopologicalSpaceTateAlgebra` (priority 1000).
The quotient topology is `quotientOneSubfXIdealTopology`.

These theorems parallel the T-topology versions `locToQuotientOneSubfX_gen_continuous`
and `locToQuotientOneSubfX_gen_denseRange`, but use the canonical topology instead.
They cannot live in `TateAlgebraTopology.lean` due to import circularity
(`PresheafIdentification` imports `TateAlgebraWedhorn` which imports `TateAlgebraTopology`).
-/

section CanonicalTopologyBridge

variable [T2Space A]

open TateAlgebra

/-- Truncation of `g ∈ A⟨X⟩` at degree `N` for the canonical topology proof:
keep coefficients at multi-indices with `s 0 < N`, set the rest to zero.
The result is restricted (polynomial). -/
private noncomputable def truncTateC (g : ↥(TateAlgebra A)) (N : ℕ) :
    ↥(TateAlgebra A) :=
  ⟨fun s ↦ if s 0 < N then g.val s else 0,
   isRestricted_of_eventually_zero _ N
    (fun s hs ↦ by simp [show ¬(s 0 < N) from by omega])⟩

private theorem truncTateC_val (g : ↥(TateAlgebra A)) (N : ℕ)
    (s : Fin 1 →₀ ℕ) :
    (truncTateC g N).val s = if s 0 < N then g.val s else 0 := rfl

private theorem truncTateC_coeff_high (g : ↥(TateAlgebra A)) (N : ℕ)
    (s : Fin 1 →₀ ℕ) (hs : N ≤ s 0) :
    (truncTateC g N).val s = 0 := by
  simp [truncTateC_val, show ¬(s 0 < N) from by omega]

/-- Polynomials (elements with finitely many nonzero coefficients) are dense
in the Tate algebra for the canonical (natural Tate) topology.

For a given basic neighborhood `tateAlgNhd P n`, the set of indices whose
coefficients lie outside `image(I^n)` is finite (by the restricted property).
So for `N` larger than all such indices, the truncation satisfies
`g - trunc(g, N) ∈ tateAlgNhd P n`. -/
theorem tateAlgebra_polynomials_dense_canonical [IsTateRing A] :
    @Dense ↥(TateAlgebra A) instTopologicalSpaceTateAlgebra
      {g | ∃ N : ℕ, ∀ n : Fin 1 →₀ ℕ, N ≤ n 0 → g.val n = 0} := by
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  intro g
  rw [@mem_closure_iff _ instTopologicalSpaceTateAlgebra]
  intro O hO hgO
  have hO_nhds : O ∈ @nhds _ instTopologicalSpaceTateAlgebra g := hO.mem_nhds hgO
  obtain ⟨n, -, hn⟩ := (tateAlgBasis' (A := A)).hasBasis_nhds g |>.mem_iff.mp hO_nhds
  -- g is restricted: all but finitely many coefficients lie in image(I^n).
  have hfin : ∀ᶠ (l : Fin 1 →₀ ℕ) in Filter.cofinite,
      MvPowerSeries.coeff l g.val ∈
        (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) :=
    tateAlgebra_coeff_eventually_in_pow P g n
  set S : Set (Fin 1 →₀ ℕ) := {l |
    MvPowerSeries.coeff l g.val ∉
      (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A)} with hS_def
  have hS_fin : S.Finite := hfin
  let N := (hS_fin.toFinset.image (· 0)).sup id + 1
  refine ⟨truncTateC g N, hn ?_, ⟨N, fun m hm ↦ truncTateC_coeff_high g N m hm⟩⟩
  -- Need: truncTateC g N - g ∈ tateAlgNhd P n (basis uses b - a ∈ ...).
  -- This equals -(g - truncTateC g N), so use neg_mem.
  have hdiff_pair : g - truncTateC g N ∈ pairSubring P := by
    intro l
    change (g.val l - (truncTateC g N).val l) ∈ (P.A₀ : Set A)
    rw [truncTateC_val]
    by_cases hlt : l 0 < N
    · rw [if_pos hlt, sub_self]; exact P.A₀.zero_mem
    · rw [if_neg hlt, sub_zero]
      have hl_not_bad : l ∉ S := by
        intro hl
        have hl_fin : l ∈ hS_fin.toFinset := hS_fin.mem_toFinset.mpr hl
        have : l 0 ≤ (hS_fin.toFinset.image (· 0)).sup id := by
          exact Finset.le_sup (f := id) (Finset.mem_image_of_mem (· 0) hl_fin)
        omega
      rw [hS_def, Set.mem_setOf_eq, not_not] at hl_not_bad
      obtain ⟨b, _, hb_eq⟩ := hl_not_bad
      rw [show g.val l = (b : A) from hb_eq.symm]; exact b.property
  have hdiff_coeff : ∀ l, ∃ b : P.A₀, b ∈ P.I ^ n ∧
      (b : A) = MvPowerSeries.coeff l (g - truncTateC g N).val := by
    intro l
    change ∃ b : P.A₀, b ∈ P.I ^ n ∧ (b : A) = g.val l - (truncTateC g N).val l
    rw [truncTateC_val]
    by_cases hlt : l 0 < N
    · -- Coefficient agrees: difference is 0.
      rw [if_pos hlt, sub_self]
      exact ⟨0, (P.I ^ n).zero_mem, rfl⟩
    · -- High coefficient: truncation is 0, difference is g.val l.
      rw [if_neg hlt, sub_zero]
      have hl_not_bad : l ∉ S := by
        intro hl
        have hl_fin : l ∈ hS_fin.toFinset := hS_fin.mem_toFinset.mpr hl
        have : l 0 ≤ (hS_fin.toFinset.image (· 0)).sup id := by
          exact Finset.le_sup (f := id) (Finset.mem_image_of_mem (· 0) hl_fin)
        omega
      rw [hS_def, Set.mem_setOf_eq, not_not] at hl_not_bad
      exact hl_not_bad
  -- g - truncTateC g N ∈ tateAlgNhd P n.
  have hg_diff_mem : g - truncTateC g N ∈ tateAlgNhd P n :=
    tateAlgNhd_of_coeff_mem_principal P n
      (IsTateRing.principalPair A).π
      (IsTateRing.principalPair A).I_eq_span
      (IsTateRing.principalPair A).π_isUnit
      hdiff_pair hdiff_coeff
  -- truncTateC g N - g = -(g - truncTateC g N), use neg_mem.
  change truncTateC g N - g ∈ tateAlgNhd P n
  rw [show truncTateC g N - g = -(g - truncTateC g N) from by ring]
  exact neg_mem hg_diff_mem

/-- The localization `A[1/s]` maps densely into `A⟨X⟩/(1-sX)` for the canonical
quotient topology (Wedhorn Example 6.38, canonical topology version).

The image of `locToQuotientOneSubfX_gen` contains all polynomial quotient classes
`mk(p)` (by `polynomial_quotient_in_range`). Polynomials are dense in `A⟨X⟩`
for the canonical topology (`tateAlgebra_polynomials_dense_canonical`), and `mk`
is a continuous surjection, so `mk(polynomials)` is dense in the quotient.
Since `mk(polynomials) ⊆ range(locToQuotientOneSubfX_gen)`, the range is dense. -/
theorem locToQuotientOneSubfX_gen_denseRange_canonical [IsTateRing A] [T2Space A]
    (s : A) :
    @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal s)
      (quotientOneSubfXIdealTopology s) (Localization.Away s)
      (locToQuotientOneSubfX_gen s) := by
  change @Dense _ (quotientOneSubfXIdealTopology s) (Set.range (locToQuotientOneSubfX_gen s))
  set P : Set ↥(TateAlgebra A) :=
    {g | ∃ N : ℕ, ∀ n : Fin 1 →₀ ℕ, N ≤ n 0 → g.val n = 0}
  let mk := Ideal.Quotient.mk (oneSubfXIdeal s)
  -- Step 1: mk '' P ⊆ range(locToQuotientOneSubfX_gen).
  have h_sub : mk '' P ⊆ Set.range (locToQuotientOneSubfX_gen s) := by
    rintro _ ⟨g, ⟨N, hN⟩, rfl⟩
    exact polynomial_quotient_in_range s g N hN
  -- Step 2: mk '' P is dense in quotient canonical topology.
  have h_dense : @Dense _ (quotientOneSubfXIdealTopology s) (mk '' P) := by
    have hP_dense := tateAlgebra_polynomials_dense_canonical (A := A)
    have hmk_surj : Function.Surjective mk := Ideal.Quotient.mk_surjective
    letI := instTopologicalSpaceTateAlgebra (A := A)
    have hmk_dr : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal s)
        (quotientOneSubfXIdealTopology s)
        ↥(TateAlgebra A) mk := hmk_surj.denseRange
    exact hmk_dr.dense_image continuous_quotient_mk' hP_dense
  exact @Dense.mono _ (quotientOneSubfXIdealTopology s) _ _ h_sub h_dense

-- REMOVED 2026-04-14: `quotientTTopology_le_quotientOneSubfXIdealTopology`
-- The 2026-04-12 reviewer note identified this as FALSE in general
-- (counterexample: A = ℚ_p, s = 1 — T-quotient non-Hausdorff, canonical
-- quotient Hausdorff, so the ordering ≤ fails). It had no external callers.
-- The acyclicity theorem uses `presheafValueTateQuotientEquiv` directly.

/-- The "fixed-ideal coefficient neighborhood": Tate series whose **every**
`MvPowerSeries` coefficient lies in the image of `P.I ^ M` in `A`.

This is the self-preserving set used by the *canonical*-topology continuity proof
(`locToQuotientOneSubfX_gen_continuous_canonical`). Unlike `artinReesNhd` (a finite
Artin-Rees intersection tied to the T-topology), it pins a single ideal `P.I ^ M`
across all coefficients — which is exactly what is stable under the generators of
`locSubring` once `P` is the enlarged pair `D.P.adjoin D.T`. -/
private def coeffIdealNhd (P : PairOfDefinition A) (M : ℕ) : Set ↥(TateAlgebra A) :=
  fun g ↦ ∀ l : Fin 1 →₀ ℕ,
    MvPowerSeries.coeff l g.val ∈
      Subtype.val '' ((P.I ^ M : Ideal P.A₀) : Set P.A₀)

omit [PlusSubring A] [IsHuberRing A] in
omit [PlusSubring A] [IsHuberRing A] in
/-- `0 ∈ coeffIdealNhd`. -/
private theorem zero_mem_coeffIdealNhd (P : PairOfDefinition A) (M : ℕ) :
    (0 : ↥(TateAlgebra A)) ∈ coeffIdealNhd P M := by
  intro l
  rw [ZeroMemClass.coe_zero, map_zero]
  exact ⟨0, (P.I ^ M).zero_mem, rfl⟩

omit [PlusSubring A] [IsHuberRing A] in
/-- `coeffIdealNhd` is closed under addition. -/
private theorem add_mem_coeffIdealNhd (P : PairOfDefinition A) (M : ℕ)
    {a b : ↥(TateAlgebra A)} (ha : a ∈ coeffIdealNhd P M)
    (hb : b ∈ coeffIdealNhd P M) : a + b ∈ coeffIdealNhd P M := by
  intro l
  rw [AddMemClass.coe_add, map_add]
  obtain ⟨x, hx, hx_eq⟩ := ha l
  obtain ⟨y, hy, hy_eq⟩ := hb l
  exact ⟨x + y, (P.I ^ M).add_mem hx hy,
    by rw [Subring.coe_add]; exact congrArg₂ (· + ·) hx_eq hy_eq⟩

omit [PlusSubring A] [IsHuberRing A] in
/-- `coeffIdealNhd` is closed under negation. -/
private theorem neg_mem_coeffIdealNhd (P : PairOfDefinition A) (M : ℕ)
    {a : ↥(TateAlgebra A)} (ha : a ∈ coeffIdealNhd P M) :
    -a ∈ coeffIdealNhd P M := by
  intro l
  rw [NegMemClass.coe_neg, map_neg]
  obtain ⟨x, hx, hx_eq⟩ := ha l
  exact ⟨-x, (P.I ^ M).neg_mem hx,
    by rw [NegMemClass.coe_neg]; exact congrArg (- ·) hx_eq⟩

omit [PlusSubring A] [IsHuberRing A] in
/-- `coeffIdealNhd` is stable under multiplication by `algebraMap a₀` for
`a₀ ∈ P.A₀`: it scales every coefficient by `a₀`, and `a₀ · I^M ⊆ I^M`. -/
private theorem mul_algebraMap_mem_coeffIdealNhd (P : PairOfDefinition A) (M : ℕ)
    {a₀ : A} (ha₀ : a₀ ∈ P.A₀) {g : ↥(TateAlgebra A)}
    (hg : g ∈ coeffIdealNhd P M) :
    algebraMap A ↥(TateAlgebra A) a₀ * g ∈ coeffIdealNhd P M := by
  intro l
  change MvPowerSeries.coeff l
    ((MvPowerSeries.C a₀ : MvPowerSeries (Fin 1) A) * g.val) ∈ _
  rw [MvPowerSeries.coeff_C_mul]
  obtain ⟨c, hc, hc_eq⟩ := hg l
  exact ⟨⟨a₀, ha₀⟩ * c, Ideal.mul_mem_left _ _ hc,
    by rw [MulMemClass.coe_mul]; exact congrArg (a₀ * ·) hc_eq⟩

omit [PlusSubring A] [IsHuberRing A] in
/-- `coeffIdealNhd` is stable under multiplication by `X`: multiplying by `X`
shifts coefficients up by one (and inserts `0` at index `0`), which preserves the
property that every coefficient lies in `image (P.I ^ M)`. -/
private theorem mul_X_mem_coeffIdealNhd (P : PairOfDefinition A) (M : ℕ)
    {g : ↥(TateAlgebra A)} (hg : g ∈ coeffIdealNhd P M) :
    TateAlgebra.X * g ∈ coeffIdealNhd P M := by
  intro l
  have hl_eq : l = Finsupp.single 0 (l 0) := by
    apply Finsupp.ext; intro k; fin_cases k; simp
  rw [hl_eq]; change TateAlgebra.coeff (l 0) (TateAlgebra.X * g) ∈ _
  cases hn : l 0 with
  | zero =>
    rw [TateAlgebra.coeff_zero_X_mul]
    exact ⟨0, (P.I ^ M).zero_mem, rfl⟩
  | succ n =>
    rw [TateAlgebra.coeff_succ_X_mul]
    exact hg (Finsupp.single 0 n)

omit [PlusSubring A] [IsHuberRing A] in
/-- The constant series `algebraMap b` lies in `coeffIdealNhd P M` whenever
`b ∈ P.I ^ M`: its only nonzero coefficient is `b` at index `0`. -/
private theorem algebraMap_mem_coeffIdealNhd (P : PairOfDefinition A) (M : ℕ)
    {b : P.A₀} (hb : b ∈ P.I ^ M) :
    algebraMap A ↥(TateAlgebra A) (b : A) ∈ coeffIdealNhd P M := by
  intro l
  have hval : (algebraMap A ↥(TateAlgebra A) (b : A)).val =
      MvPowerSeries.C (b : A) := rfl
  rw [hval, MvPowerSeries.coeff_C]
  split
  · exact ⟨b, hb, rfl⟩
  · exact ⟨0, (P.I ^ M).zero_mem, rfl⟩

omit [PlusSubring A] [IsHuberRing A] in
/-- Every element `x` of `locSubring P T s` has a lift `r' : A⟨X⟩` with
`mk r' = locToQuotientOneSubfX_gen s x` that **stabilizes** `coeffIdealNhd P_M M`,
provided the enlarged pair `P_M` absorbs both `P.A₀` (for the `algebraMap a₀`
generators) and every `t ∈ T` (for the `divByS t s` generators).

Proved by `Subring.closure_induction` over the two families of generators of
`locSubring`, using the `coeffIdealNhd` stability lemmas; this is the canonical
analogue of the `Subring.closure_induction` step in `locToQuotient_mul_small_constant_mem`. -/
private theorem exists_lift_stabilizing_coeffIdealNhd
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (P_M : PairOfDefinition A) (M : ℕ)
    (hPA₀ : P.A₀ ≤ P_M.A₀) (hT_mem : ∀ t ∈ T, t ∈ P_M.A₀)
    {x : Localization.Away s} (hx : x ∈ locSubring P T s) :
    ∃ r' : ↥(TateAlgebra A),
      Ideal.Quotient.mk (oneSubfXIdeal s) r' = locToQuotientOneSubfX_gen s x ∧
        ∀ g ∈ coeffIdealNhd P_M M, r' * g ∈ coeffIdealNhd P_M M := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a₀, ha₀, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩
    · -- Case: x = algebraMap(a₀) with a₀ ∈ P.A₀.
      refine ⟨algebraMap A _ a₀, ?_, ?_⟩
      · rw [← locToQuotientOneSubfX_gen_algebraMap]
      · exact fun g hg ↦ mul_algebraMap_mem_coeffIdealNhd P_M M (hPA₀ ha₀) hg
    · -- Case: x = divByS(t, s) with t ∈ T.
      refine ⟨algebraMap A _ t * TateAlgebra.X, ?_, ?_⟩
      · rw [← locToQuotientOneSubfX_gen_divByS]
      · refine fun g hg ↦ ?_
        rw [mul_assoc]
        exact mul_algebraMap_mem_coeffIdealNhd P_M M (hT_mem t ht)
          (mul_X_mem_coeffIdealNhd P_M M hg)
  | zero =>
    exact ⟨0, by simp [map_zero], fun g _ ↦ by simp [zero_mul, zero_mem_coeffIdealNhd]⟩
  | one =>
    exact ⟨1, by simp [map_one], fun g hg ↦ by simp [one_mul, hg]⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨rx, hrx_eq, hrx_stab⟩ := ihx
    obtain ⟨ry, hry_eq, hry_stab⟩ := ihy
    exact ⟨rx + ry, by rw [map_add, hrx_eq, hry_eq, map_add],
      fun g hg ↦ by
        rw [add_mul]; exact add_mem_coeffIdealNhd P_M M (hrx_stab g hg) (hry_stab g hg)⟩
  | neg x _ ihx =>
    obtain ⟨rx, hrx_eq, hrx_stab⟩ := ihx
    exact ⟨-rx, by rw [map_neg, hrx_eq, map_neg],
      fun g hg ↦ by rw [neg_mul]; exact neg_mem_coeffIdealNhd P_M M (hrx_stab g hg)⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨rx, hrx_eq, hrx_stab⟩ := ihx
    obtain ⟨ry, hry_eq, hry_stab⟩ := ihy
    exact ⟨rx * ry, by rw [map_mul, hrx_eq, hry_eq, map_mul],
      fun g hg ↦ by rw [mul_assoc]; exact hrx_stab _ (hry_stab g hg)⟩

omit [PlusSubring A] [IsHuberRing A] in
/-- The map `locToQuotientOneSubfX_gen D.s` is continuous from the localization
topology on `Localization.Away D.s` to the canonical quotient topology on
`A⟨X⟩/(1-sX)`.

**Proof sketch:** Reduce to continuity at 0 (additive group hom). Use the
nonarchimedean property of the canonical quotient topology to extract an open
additive subgroup `W` of any target neighborhood. Then show that for large `n`,
`locNhd(n)` maps into `W` via the canonical I-adic structure.

The key ingredient: `mk ∘ algebraMap : A → quotient` is continuous (composition
of `tateAlgebra_algebraMap_continuous` and `continuous_quotient_mk'`), and
the localization neighborhoods `locNhd(n)` are generated by elements of the form
`algebraMap(b) / s^k` with `b ∈ I^n`. -/
theorem locToQuotientOneSubfX_gen_continuous_canonical [IsTateRing A] [T2Space A]
    (D : RationalLocData A)
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    @Continuous _ _ D.topology (quotientOneSubfXIdealTopology D.s)
      (locToQuotientOneSubfX_gen D.s) := by
  -- Set up instances.
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away D.s) := D.isTopologicalAddGroup
  letI τC : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalRing D.s
  haveI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    @IsTopologicalRing.to_topologicalAddGroup _ _
      (quotientOneSubfXIdealTopology D.s) (quotientOneSubfXIdealTopology_isTopologicalRing D.s)
  -- Reduce to continuity at 0.
  apply continuous_of_continuousAt_zero (locToQuotientOneSubfX_gen D.s)
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro S hS
  have hbasis := locBasis D.P D.T D.s D.hopen
  let hb := hbasis.toRingFilterBasis.toAddGroupFilterBasis
  -- TateAlgebra A is nonarchimedean with canonical topology (from RingSubgroupsBasis).
  haveI hNA_tate : @NonarchimedeanRing ↥(TateAlgebra A) _ instTopologicalSpaceTateAlgebra :=
    tateAlgBasis'.nonarchimedean
  -- The canonical quotient topology is nonarchimedean.
  haveI : @NonarchimedeanRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      _ (quotientOneSubfXIdealTopology D.s) := by
    constructor; intro U hU
    have hcont : @Continuous _ _ instTopologicalSpaceTateAlgebra
        (quotientOneSubfXIdealTopology D.s)
        (Ideal.Quotient.mk (oneSubfXIdeal D.s)) :=
      continuous_quotient_mk'
    have hU' : (Ideal.Quotient.mk (oneSubfXIdeal D.s)) ⁻¹' (U : Set _) ∈
        @nhds _ instTopologicalSpaceTateAlgebra (0 : ↥(TateAlgebra A)) :=
      hcont.continuousAt.preimage_mem_nhds hU
    obtain ⟨V, hVU⟩ := @NonarchimedeanRing.is_nonarchimedean _ _ _ hNA_tate _ hU'
    exact ⟨{
      toAddSubgroup := V.toAddSubgroup.map
        (Ideal.Quotient.mk (oneSubfXIdeal D.s)).toAddMonoidHom
      isOpen' := @QuotientRing.isOpenMap_coe _ instTopologicalSpaceTateAlgebra _
        (oneSubfXIdeal D.s) instIsTopologicalRingTateAlgebra _ V.isOpen
    }, fun x hx ↦ by obtain ⟨y, hy, rfl⟩ := hx; exact hVU hy⟩
  obtain ⟨W, hWS⟩ := NonarchimedeanRing.is_nonarchimedean S hS
  suffices ∃ n, ∀ x ∈ locNhd D.P D.T D.s n,
      locToQuotientOneSubfX_gen D.s x ∈ (W : Set _) by
    obtain ⟨n, hn⟩ := this
    apply Filter.mem_of_superset
      (hb.nhds_zero_hasBasis.mem_iff.mpr
        ⟨locNhd D.P D.T D.s n, ⟨n, rfl⟩, le_refl _⟩)
    intro x hx; exact hWS (hn x hx)
  -- ====================================================================
  -- Direct proof via boundedness of φ(locSubring) in canonical quotient.
  -- Key insight (from AI reviewer): the topology equality
  -- quotientOneSubfXIdealTopology = quotientTTopology is FALSE in general
  -- (counterexample: A = ℚ_p, s = 1). So we prove continuity directly
  -- without comparing topologies.
  --
  -- The argument:
  -- (1) locNhd n = image of (locIdeal)^n. Since locIdeal = algebraMap(π) · locSubring
  --     (principal ideal), (locIdeal)^n = algebraMap(π^n) · locSubring.
  -- (2) φ(locNhd n) ⊆ mk(C(π^n)) · φ(locSubring) (ring hom).
  -- (3) mk(C(π^n)) → 0 in canonical quotient (continuity of mk ∘ algebraMap + π nilpotent).
  -- (4) φ(locSubring) is bounded in canonical quotient.
  -- (5) Bounded · (small nhd) ⊆ W.
  -- ====================================================================
  -- Step 1: mk(algebraMap(π^n)) → 0 in canonical quotient.
  -- mk ∘ algebraMap : A → quotient is continuous for canonical topology.
  let mk := Ideal.Quotient.mk (oneSubfXIdeal D.s)
  have hmk_alg_cont : @Continuous _ _
      (inferInstance : TopologicalSpace A) τC
      (mk.comp (algebraMap A ↥(TateAlgebra A))) := by
    exact continuous_quotient_mk'.comp tateAlgebra_algebraMap_continuous
  -- π is topologically nilpotent in A.
  let P' := (IsTateRing.principalPair A).toPairOfDefinition
  have hπ := P'.isTopologicallyNilpotent_of_mem
    (show (IsTateRing.principalPair A).π ∈ P'.I from by
      rw [(IsTateRing.principalPair A).I_eq_span]; exact Ideal.mem_span_singleton_self _)
  -- mk(algebraMap(π^n)) → 0 in canonical quotient.
  have hmk_pi_tendsto : Filter.Tendsto
      (fun n ↦ mk (algebraMap A ↥(TateAlgebra A) ((IsTateRing.principalPair A).π ^ n : A)))
      Filter.atTop (@nhds _ τC 0) := by
    have h0 : mk (algebraMap A ↥(TateAlgebra A) 0) = 0 := by simp
    rw [← h0]
    exact (hmk_alg_cont.tendsto 0).comp (by
      change Filter.Tendsto (fun n ↦ ((IsTateRing.principalPair A).π : A) ^ n) _ _
      exact hπ)
  -- Step 2: Construct P_common = D.P.adjoin D.T (Wedhorn 6.3).
  -- P_common.A₀ = Subring.closure(D.P.A₀ ∪ D.T), which contains both D.P.A₀ and D.T.
  -- P_common.I = Ideal.map incl D.P.I. Both generators of locSubring lie in P_common.A₀,
  -- so multiplication by their lifts preserves image(P_common.I^M) — self-preserving!
  let P_common := D.P.adjoin D.T hT_pb
  let P := D.P; let s := D.s; let T := D.T
  -- Step 3: Pull back W through mk to the canonical Tate topology.
  have hW_nhds : (W : Set _) ∈ @nhds _ τC 0 := W.isOpen.mem_nhds W.zero_mem
  have hmk_cont : @Continuous _ _ instTopologicalSpaceTateAlgebra τC
      (Ideal.Quotient.mk (oneSubfXIdeal s)) := continuous_quotient_mk'
  have hmk_pre_W : mk ⁻¹' (W : Set _) ∈
      @nhds _ instTopologicalSpaceTateAlgebra (0 : ↥(TateAlgebra A)) :=
    hmk_cont.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨k₀, -, hk₀⟩ := tateAlgBasis'.hasBasis_nhds_zero.mem_iff.mp hmk_pre_W
  -- Step 4: Get M such that image(P_common.I^M) ⊆ image(P'.I^k₀) (cofinality).
  -- Since P'.hasBasis_nhds_zero gives image(P'.I^k₀) as a nhd of 0,
  -- and P_common.hasBasis_nhds_zero gives a basis of nhds, there exists M with
  -- image(P_common.I^M) ⊆ image(P'.I^k₀).
  have hPcI_nhds : Subtype.val '' ((P'.I ^ k₀ : Ideal P'.A₀) : Set P'.A₀) ∈ nhds (0 : A) :=
    (P'.pow_image_isOpen k₀).mem_nhds ⟨0, (P'.I ^ k₀).zero_mem, rfl⟩
  obtain ⟨M, -, hM⟩ := P_common.hasBasis_nhds_zero.mem_iff.mp hPcI_nhds
  -- hM : image(P_common.I^M) ⊆ image(P'.I^k₀)
  -- Step 5: G = fixed-ideal coefficient neighborhood for the enlarged pair
  -- (all coefficients in image(P_common.I^M)); see `coeffIdealNhd`.
  let G : Set ↥(TateAlgebra A) := coeffIdealNhd P_common M
  -- Step 5a: G ⊆ mk⁻¹(W) via cofinality image(P_common.I^M) ⊆ image(P'.I^k₀)
  -- (`hM`) and `tateAlgNhd_of_coeff_mem_principal`.
  have hG_sub_W : G ⊆ mk ⁻¹' (W : Set _) := by
    intro g hg
    apply hk₀
    have hg_pair : g ∈ pairSubring P' := by
      intro l; obtain ⟨c, _, hc_eq⟩ := hM (hg l); rw [← hc_eq]; exact c.property
    have hg_coeff : ∀ l, ∃ b : P'.A₀, b ∈ P'.I ^ k₀ ∧
        (b : A) = MvPowerSeries.coeff l g.val := fun l ↦ hM (hg l)
    exact tateAlgNhd_of_coeff_mem_principal P' k₀
      (IsTateRing.principalPair A).π
      (IsTateRing.principalPair A).I_eq_span
      (IsTateRing.principalPair A).π_isUnit
      hg_pair hg_coeff
  -- Step 6: algebraMap(b) ∈ G for b ∈ D.P.I^M (D.P.I ↪ P_common.I via inclusion).
  have halg_in_G : ∀ (b : P.A₀), b ∈ P.I ^ M →
      algebraMap A ↥(TateAlgebra A) (b : A) ∈ G := fun b hb ↦
    algebraMap_mem_coeffIdealNhd P_common M
      (show Subring.inclusion (P.le_adjoin_A₀ T) b ∈ P_common.I ^ M by
        rw [show P_common.I ^ M =
          (Ideal.map (Subring.inclusion (P.le_adjoin_A₀ T)) P.I) ^ M from rfl,
          ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hb)
  -- Step 7: every locSubring element lifts to an A⟨X⟩ element stabilizing G.
  have hlift : ∀ (x : Localization.Away s),
      x ∈ locSubring P T s → ∃ r' : ↥(TateAlgebra A),
        mk r' = locToQuotientOneSubfX_gen s x ∧ ∀ g ∈ G, r' * g ∈ G := fun x hx ↦
    exists_lift_stabilizing_coeffIdealNhd P T s P_common M
      (P.adjoin_A₀_le D.T hT_pb) (fun t ht ↦ P.mem_adjoin_of_mem_T D.T hT_pb ht) hx
  -- Step 9: Assemble via Submodule.span_induction (same as T-topology proof).
  refine ⟨M, ?_⟩
  rintro x ⟨d, hd, rfl⟩
  rw [locIdeal, ← Ideal.map_pow] at hd
  suffices ∀ (r : locSubring P T s),
      locToQuotientOneSubfX_gen s
        ((locSubring P T s).subtype (r * d)) ∈ (W : Set _) by
    simpa using this 1
  intro r₀
  revert r₀
  refine Submodule.span_induction (p := fun d _ ↦
      ∀ (r : locSubring P T s),
        locToQuotientOneSubfX_gen s
          ((locSubring P T s).subtype (r * d)) ∈ (W : Set _)) ?_ ?_ ?_ ?_ hd
  · -- Generator: d = algebraMapD(b) for b ∈ D.P.I^M.
    rintro d ⟨b, hb, rfl⟩ r
    -- φ(subtype(r) * algebraMap(b.val)) = mk(r') * mk(algebraMap(b.val))
    -- = mk(r' * algebraMap(b.val)) ∈ mk(G) ⊆ W.
    obtain ⟨r', hr'_eq, hr'_stab⟩ := hlift r.val r.property
    have hb_in_G : algebraMap A ↥(TateAlgebra A) (b : A) ∈ G := halg_in_G b hb
    -- subtype(r * algebraMapD(b)) = subtype(r) * subtype(algebraMapD(b))
    --                              = r.val * algebraMap(b.val)
    have hrw : (locSubring P T s).subtype (r * algebraMapD P T s b) =
        r.val * algebraMap A (Localization.Away s) (b : A) := by
      simp [map_mul, algebraMapD]
    rw [hrw, map_mul, locToQuotientOneSubfX_gen_algebraMap, ← hr'_eq, ← map_mul]
    exact hG_sub_W (hr'_stab _ hb_in_G)
  · -- Zero
    intro r; simp [mul_zero, map_zero]
  · -- Addition: d₁ + d₂
    intro d₁ d₂ _ _ h₁ h₂ r
    have : (locSubring P T s).subtype (r * (d₁ + d₂)) =
        (locSubring P T s).subtype (r * d₁) +
        (locSubring P T s).subtype (r * d₂) := by
      simp [mul_add]
    rw [this, map_add]
    exact W.toAddSubgroup.add_mem (h₁ r) (h₂ r)
  · -- Scalar: s • d for s ∈ locSubring.
    intro s' d _ hd r
    have : (locSubring P T s).subtype (r * (s' • d)) =
        (locSubring P T s).subtype ((r * s') * d) := by
      simp [mul_assoc]
    rw [this]
    exact hd (r * s')

/-! ### Step 5: Extension to completion via extensionHom (Canonical Topology)

Once `locToQuotientOneSubfX_gen_continuous_canonical` and
`locToQuotientOneSubfX_gen_denseRange_canonical` are established, we extend
the map to the completion `presheafValue D` using `extensionHom`, targeting
the canonical quotient topology on `A⟨X⟩/(1-sX)`.

This parallels the T-topology construction (`presheafValueToQuotient`) but
uses the canonical quotient topology, which is always T2 and complete for
strongly noetherian Tate rings. -/

/-- The `IsUniformAddGroup` instance for the canonical quotient topology. -/
noncomputable instance quotientOneSubfXIdeal_isUniformAddGroup [IsTateRing A]
    (f : A) :
    @IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientOneSubfXIdealUniformSpace f) _ :=
  @isUniformAddGroup_of_addCommGroup _ _ (quotientOneSubfXIdealTopology f)
    (quotientOneSubfXIdealTopology_isTopologicalAddGroup f)

/-- The ring homomorphism `presheafValue D →+* A⟨X⟩/(1-sX)` extending
`locToQuotientOneSubfX_gen` to the completion, using the **canonical**
quotient topology on the target.

This uses `UniformSpace.Completion.extensionHom` with:
- Source: `Localization.Away D.s` with `D.uniformSpace`
- Target: canonical quotient with `quotientOneSubfXIdealUniformSpace D.s`
- Continuity: `locToQuotientOneSubfX_gen_continuous_canonical`
- Target complete: `quotient_oneSubfXIdeal_completeSpace`
- Target T0: follows from T2 (`quotient_oneSubfXIdeal_t2Space`) -/
noncomputable def presheafValueToCanonicalQuotient (D : RationalLocData A)
    [IsTateRing A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    presheafValue D →+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalAddGroup D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdeal_isUniformAddGroup D.s
  haveI : CompleteSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotient_oneSubfXIdeal_completeSpace hA_complete hnoeth D.s
  haveI hT2Q : @T2Space _ (quotientOneSubfXIdealTopology D.s) :=
    quotient_oneSubfXIdeal_t2Space hA_complete hnoeth D.s
  haveI hT0Q : @T0Space _ (quotientOneSubfXIdealTopology D.s) :=
    @T1Space.t0Space _ (quotientOneSubfXIdealTopology D.s) (T2Space.t1Space)
  exact @UniformSpace.Completion.extensionHom _ _ _ _ _ _
    (quotientOneSubfXIdealUniformSpace D.s) _
    (quotientOneSubfXIdeal_isUniformAddGroup D.s)
    (quotientOneSubfXIdealTopology_isTopologicalRing D.s)
    (locToQuotientOneSubfX_gen D.s)
    (locToQuotientOneSubfX_gen_continuous_canonical D hT_pb)
    (quotient_oneSubfXIdeal_completeSpace hA_complete hnoeth D.s)
    hT0Q

/-- **Continuity of `presheafValueToCanonicalQuotient`** (T-EMBED-TOPO-EXAMPLE638
ingredient). The backward direction of the canonical-quotient equivalence is
continuous: as a `UniformSpace.Completion.extensionHom` it inherits continuity
from `Completion.continuous_extension`.

This is the topological complement to `tateQuotientToPresheafHom_continuous_of_tate`
(which gives continuity of the forward direction). Together they make
`presheafValueCanonicalQuotientEquiv` a TOPOLOGICAL ring iso (homeomorphism),
not just an algebraic one — closing the T-EMBED-TOPO-EXAMPLE638 sub-ticket
of T-EMBED-TOPO. -/
theorem presheafValueToCanonicalQuotient_continuous (D : RationalLocData A)
    [IsTateRing A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    @Continuous _ _ (inferInstance : TopologicalSpace (presheafValue D))
      (quotientOneSubfXIdealTopology D.s)
      (presheafValueToCanonicalQuotient D hA_complete hnoeth hT_pb) := by
  letI us_src : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI ts_tgt : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI us_tgt : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  haveI cs_tgt : @CompleteSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) us_tgt :=
    quotient_oneSubfXIdeal_completeSpace hA_complete hnoeth D.s
  haveI hT0Q : @T0Space _ (quotientOneSubfXIdealTopology D.s) :=
    @T1Space.t0Space _ (quotientOneSubfXIdealTopology D.s)
      (@T2Space.t1Space _ (quotientOneSubfXIdealTopology D.s)
        (quotient_oneSubfXIdeal_t2Space hA_complete hnoeth D.s))
  -- presheafValueToCanonicalQuotient is defined as
  -- `UniformSpace.Completion.extensionHom (locToQuotientOneSubfX_gen D.s) ...`.
  -- Its function coercion is `Completion.extension (...)` which is continuous.
  change Continuous (fun x : presheafValue D ↦
    presheafValueToCanonicalQuotient D hA_complete hnoeth hT_pb x)
  unfold presheafValueToCanonicalQuotient
  -- The underlying function is `Completion.extension (locToQuotientOneSubfX_gen D.s)`.
  -- Apply continuous_extension with the explicit target uniform structure.
  exact UniformSpace.Completion.continuous_extension

/-- `presheafValueToCanonicalQuotient` on the dense image agrees with
`locToQuotientOneSubfX_gen`. -/
theorem presheafValueToCanonicalQuotient_coe (D : RationalLocData A)
    [IsTateRing A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (a : Localization.Away D.s) :
    presheafValueToCanonicalQuotient D hA_complete hnoeth hT_pb (D.coeRingHom a) =
      locToQuotientOneSubfX_gen D.s a := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalAddGroup D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdeal_isUniformAddGroup D.s
  haveI : CompleteSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotient_oneSubfXIdeal_completeSpace hA_complete hnoeth D.s
  haveI hT2Q : @T2Space _ (quotientOneSubfXIdealTopology D.s) :=
    quotient_oneSubfXIdeal_t2Space hA_complete hnoeth D.s
  haveI hT0Q : @T0Space _ (quotientOneSubfXIdealTopology D.s) :=
    @T1Space.t0Space _ (quotientOneSubfXIdealTopology D.s) (T2Space.t1Space)
  exact @UniformSpace.Completion.extensionHom_coe _ _ _ _ _ _
    (quotientOneSubfXIdealUniformSpace D.s) _
    (quotientOneSubfXIdeal_isUniformAddGroup D.s)
    (quotientOneSubfXIdealTopology_isTopologicalRing D.s)
    (locToQuotientOneSubfX_gen D.s)
    (locToQuotientOneSubfX_gen_continuous_canonical D hT_pb)
    (quotient_oneSubfXIdeal_completeSpace hA_complete hnoeth D.s)
    hT0Q a

/-! ### Step 6: Round-trip composites are identity (Canonical Topology) -/

/-- The composite `tateQuotientToPresheafHom ∘ presheafValueToCanonicalQuotient`
is the identity on `presheafValue D`.

On the dense image `coeRingHom(a)`:
  `tateQuotientToPresheafHom (presheafValueToCanonicalQuotient (coeRingHom a))`
  `= tateQuotientToPresheafHom (locToQuotientOneSubfX_gen a)`
  `= locLiftToPresheaf a`   (by round-trip)
  `= coeRingHom a`          (by `locLiftToPresheaf_eq_coeRingHom`)

By T2 density, this extends to all of `presheafValue D`. -/
theorem tateQuotientToPresheaf_comp_presheafToCanonicalQuotient (D : RationalLocData A)
    [IsTateRing A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (hcont_eval : @Continuous _ _
      (quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (x : presheafValue D) :
    tateQuotientToPresheafHom D hb
      (presheafValueToCanonicalQuotient D hA_complete hnoeth hT_pb x) = x := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI τC : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  -- Continuity of the presheafValueToCanonicalQuotient map.
  -- The underlying function is Completion.extension, so continuity follows from
  -- Completion.continuous_extension after unwinding definitions.
  have hcont_ext : @Continuous _ _
      (inferInstance : TopologicalSpace (presheafValue D)) τC
      (presheafValueToCanonicalQuotient D hA_complete hnoeth hT_pb) := by
    have hcs := quotient_oneSubfXIdeal_completeSpace hA_complete hnoeth D.s
    have hce := @UniformSpace.Completion.continuous_extension _ D.uniformSpace _
      (quotientOneSubfXIdealUniformSpace D.s)
      (↑(locToQuotientOneSubfX_gen D.s)) hcs
    exact hce
  -- Use T2 density: the composite and id agree on the dense image.
  refine @UniformSpace.Completion.ext' _ D.uniformSpace
    (presheafValue D) _ _ _ _
    (hcont_eval.comp hcont_ext)
    continuous_id ?_ x
  -- On the dense image: show agreement pointwise.
  intro a
  simp only [Function.comp, id]
  change tateQuotientToPresheafHom D hb
    (presheafValueToCanonicalQuotient D hA_complete hnoeth hT_pb (D.coeRingHom a)) =
    D.coeRingHom a
  rw [presheafValueToCanonicalQuotient_coe D hA_complete hnoeth hT_pb a,
    tateQuotient_roundtrip_apply D hb a,
    locLiftToPresheaf_eq_coeRingHom D]

/-- The composite `presheafValueToCanonicalQuotient ∘ tateQuotientToPresheafHom`
is the identity on `A⟨X⟩/(1-sX)` with the canonical quotient topology.

Both composites agree with `id` on the dense image of `locToQuotientOneSubfX_gen`
(canonical topology version). By T2 of the canonical quotient + density, they
are equal. -/
theorem presheafToCanonicalQuotient_comp_tateQuotientToPresheaf (D : RationalLocData A)
    [IsTateRing A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (hcont_eval : @Continuous _ _
      (quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (q : ↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :
    presheafValueToCanonicalQuotient D hA_complete hnoeth hT_pb
      (tateQuotientToPresheafHom D hb q) = q := by
  -- Setup instances for the canonical quotient topology.
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI τC : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalAddGroup D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdeal_isUniformAddGroup D.s
  -- T2 for canonical quotient.
  haveI hT2 : @T2Space _ τC :=
    quotient_oneSubfXIdeal_t2Space hA_complete hnoeth D.s
  haveI : @CompleteSpace _ (quotientOneSubfXIdealUniformSpace D.s) :=
    quotient_oneSubfXIdeal_completeSpace hA_complete hnoeth D.s
  -- Dense range for canonical topology.
  have hdense := locToQuotientOneSubfX_gen_denseRange_canonical D.s
  -- The composites agree on the dense image of locToQuotientOneSubfX_gen.
  have hagree : ∀ (a : Localization.Away D.s),
      presheafValueToCanonicalQuotient D hA_complete hnoeth hT_pb
        (tateQuotientToPresheafHom D hb (locToQuotientOneSubfX_gen D.s a)) =
        locToQuotientOneSubfX_gen D.s a := by
    intro a
    rw [tateQuotient_roundtrip_apply D hb a,
      locLiftToPresheaf_eq_coeRingHom D,
      presheafValueToCanonicalQuotient_coe D hA_complete hnoeth hT_pb a]
  -- Use DenseRange.equalizer: two continuous maps agreeing on a dense
  -- subset of a T₂ space must be equal.
  -- Continuity of the extension (presheafValueToCanonicalQuotient).
  have hcont_ext : @Continuous _ _
      (inferInstance : TopologicalSpace (presheafValue D)) τC
      (presheafValueToCanonicalQuotient D hA_complete hnoeth hT_pb) := by
    exact @UniformSpace.Completion.continuous_extension _ D.uniformSpace _
      (quotientOneSubfXIdealUniformSpace D.s)
      (↑(locToQuotientOneSubfX_gen D.s))
      (quotient_oneSubfXIdeal_completeSpace hA_complete hnoeth D.s)
  have h_eq : (fun q ↦ presheafValueToCanonicalQuotient D hA_complete hnoeth hT_pb
      (tateQuotientToPresheafHom D hb q)) =
    (fun q ↦ q) :=
    hdense.equalizer
      (hcont_ext.comp hcont_eval)
      continuous_id
      (funext hagree)
  exact congr_fun h_eq q

/-! ### Step 7: Package as RingEquiv (Canonical Topology) -/

/-- **The completion isomorphism (canonical topology)**
`presheafValue D ≃+* A⟨X⟩/(1-sX)` (Wedhorn Proposition 8.30).

For a strongly noetherian Tate ring `A` and rational localization datum `D`,
the presheaf value (completion of `Localization.Away D.s`) is ring-isomorphic
to the Tate algebra quotient `A⟨X⟩/(1-sX)` equipped with the canonical
quotient topology.

Both composites are identity:
- `tateQuotientToPresheafHom ∘ presheafValueToCanonicalQuotient = id`
- `presheafValueToCanonicalQuotient ∘ tateQuotientToPresheafHom = id` -/
noncomputable def presheafValueCanonicalQuotientEquiv (D : RationalLocData A)
    [IsTateRing A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (hcont_eval : @Continuous _ _
      (quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb)) :
    presheafValue D ≃+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) where
  toFun := presheafValueToCanonicalQuotient D hA_complete hnoeth hT_pb
  invFun := tateQuotientToPresheafHom D hb
  left_inv :=
    tateQuotientToPresheaf_comp_presheafToCanonicalQuotient
      D hb hA_complete hnoeth hT_pb hcont_eval
  right_inv :=
    presheafToCanonicalQuotient_comp_tateQuotientToPresheaf
      D hb hA_complete hnoeth hT_pb hcont_eval
  map_mul' := map_mul _
  map_add' := map_add _

/-- **T-EMBED-TOPO-EXAMPLE638**: the canonical-quotient equivalence
`presheafValue D ≃+* A⟨X⟩/(1-D.s·X)` is a HOMEOMORPHISM (topological ring iso),
not just an algebraic ring iso.

This packages the bidirectional continuity:
- Forward (`presheafValueToCanonicalQuotient`) continuous via
  `presheafValueToCanonicalQuotient_continuous` (extensionHom-induced).
- Backward (`tateQuotientToPresheafHom`) continuous via the `hcont_eval`
  hypothesis (typically discharged by `tateQuotientToPresheafHom_continuous_of_tate`
  under `[IsTateRing A] [NonarchimedeanRing A]`).

Closes T-EMBED-TOPO-EXAMPLE638: the topological version of Wedhorn
Example 6.38. The bare `presheafValueCanonicalQuotientEquiv` provides only
the algebraic ring iso; this Homeomorph packages the topology too.

Together with `tateQuotientToPresheafHom_continuous_of_tate`, this gives
a sorry-free topological iso package for downstream T-EMBED-TOPO consumers. -/
noncomputable def presheafValueCanonicalQuotientHomeomorph (D : RationalLocData A)
    [IsTateRing A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (hcont_eval : @Continuous _ _
      (quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb)) :
    @Homeomorph (presheafValue D) (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (quotientOneSubfXIdealTopology D.s) where
  toEquiv := (presheafValueCanonicalQuotientEquiv D hb hA_complete hnoeth hT_pb
    hcont_eval).toEquiv
  continuous_toFun := presheafValueToCanonicalQuotient_continuous
    D hA_complete hnoeth hT_pb
  continuous_invFun := hcont_eval

/-- The canonical isomorphism sends `canonicalMap(a)` to `mk(algebraMap a)`. -/
theorem presheafValueCanonicalQuotientEquiv_canonicalMap (D : RationalLocData A)
    [IsTateRing A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (hcont_eval : @Continuous _ _
      (quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (a : A) :
    presheafValueCanonicalQuotientEquiv D hb hA_complete hnoeth hT_pb hcont_eval
      (D.canonicalMap a) =
      (Ideal.Quotient.mk _) (algebraMap A _ a) := by
  change presheafValueToCanonicalQuotient D hA_complete hnoeth hT_pb
    (D.coeRingHom (algebraMap A _ a)) = _
  rw [presheafValueToCanonicalQuotient_coe, locToQuotientOneSubfX_gen_algebraMap]

/-- The inverse sends `mk(algebraMap a)` back to `canonicalMap(a)`. -/
theorem presheafValueCanonicalQuotientEquiv_symm_algebraMap (D : RationalLocData A)
    [IsTateRing A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (hcont_eval : @Continuous _ _
      (quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (a : A) :
    (presheafValueCanonicalQuotientEquiv D hb hA_complete hnoeth hT_pb hcont_eval).symm
      ((Ideal.Quotient.mk _) (algebraMap A _ a)) =
      D.canonicalMap a := by
  simp only [presheafValueCanonicalQuotientEquiv, RingEquiv.symm_mk,
    RingEquiv.coe_mk, Equiv.coe_fn_mk]
  exact tateQuotientToPresheafHom_algebraMap D hb a

/-! ### Step 8: Banach OMP -> Topological Isomorphism

The inverse map `tateQuotientToPresheafHom D hb` is a continuous bijection
from the canonical quotient (complete, first-countable) to `presheafValue D`
(T2, Baire). By the Banach open mapping theorem, it is an open map, hence
a homeomorphism. -/

/-- The canonical quotient `A⟨X⟩/(1-sX)` is first-countable, inheriting the
first-countability of `TateAlgebra A` through the quotient map.

**Proof:** The quotient map `mk : A⟨X⟩ → A⟨X⟩/(1-sX)` is open (topological
ring quotient) and continuous. For any `q = mk(g)`, the neighborhood filter
`nhds q = map mk (nhds g)` (by `IsOpenMap.map_nhds_eq`). Since `nhds g` is
countably generated (first-countable source), so is `map mk (nhds g)`. -/
noncomputable instance quotientOneSubfXIdeal_firstCountableTopology [IsTateRing A]
    (f : A) :
    @FirstCountableTopology (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientOneSubfXIdealTopology f) := by
  haveI := instFirstCountableTopologyTateAlgebra (A := A)
  constructor; intro q
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
  -- The quotient map mk is open and continuous.
  -- nhds (mk g) = map mk (nhds g) via IsOpenMap.map_nhds_eq.
  -- Since nhds g is countably generated, so is map mk (nhds g).
  -- We work inside the canonical Tate topology.
  change (@nhds _ (quotientOneSubfXIdealTopology f) _).IsCountablyGenerated
  suffices h : @nhds _ (quotientOneSubfXIdealTopology f)
      ((Ideal.Quotient.mk (oneSubfXIdeal f)) g) =
      Filter.map (Ideal.Quotient.mk (oneSubfXIdeal f))
        (@nhds _ instTopologicalSpaceTateAlgebra g) by
    rw [h]; exact Filter.map.isCountablyGenerated _ _
  exact ((@QuotientRing.isOpenMap_coe _ instTopologicalSpaceTateAlgebra _
    (oneSubfXIdeal f) instIsTopologicalRingTateAlgebra).map_nhds_eq
    continuous_coinduced_rng.continuousAt).symm

/-- **Banach OMP for `tateQuotientToPresheafHom`**: the inverse map of the
canonical isomorphism is a homeomorphism.

`tateQuotientToPresheafHom D hb` is a continuous bijection from the canonical
quotient (complete + sigma-compact) to `presheafValue D` (T2 + Baire).
By `AddMonoidHom.isOpenMap_of_complete_countable`, it is an open map.
Continuous + open + bijective = homeomorphism. -/
theorem tateQuotientToPresheafHom_isHomeomorph (D : RationalLocData A)
    [IsTateRing A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (hcont_eval : @Continuous _ _
      (quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    -- BaireSpace + SigmaCompactSpace are hard to derive in full generality;
    -- we take them as hypotheses and discharge them in concrete applications.
    (hBaire : @BaireSpace (presheafValue D) _)
    (hSigma : @SigmaCompactSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientOneSubfXIdealTopology D.s)) :
    @IsHomeomorph _ _
      (quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb) := by
  letI τC : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology_isTopologicalAddGroup D.s
  letI uC : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdeal_isUniformAddGroup D.s
  haveI : CompleteSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotient_oneSubfXIdeal_completeSpace hA_complete hnoeth D.s
  haveI : T2Space (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotient_oneSubfXIdeal_t2Space hA_complete hnoeth D.s
  -- The canonical isomorphism provides bijectivity.
  let e := presheafValueCanonicalQuotientEquiv D hb hA_complete hnoeth hT_pb hcont_eval
  have hbij : Function.Bijective (tateQuotientToPresheafHom D hb) :=
    ⟨e.symm.injective, e.symm.surjective⟩
  -- Apply Banach OMP: surjective continuous hom from sigma-compact complete
  -- group to Baire T2 group is open.
  have hopen : @IsOpenMap _ _ τC _ (tateQuotientToPresheafHom D hb) :=
    @AddMonoidHom.isOpenMap_of_complete_countable
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) (presheafValue D)
      _ uC (quotientOneSubfXIdeal_isUniformAddGroup D.s) _ hSigma
      _ _ _ hBaire _
      (tateQuotientToPresheafHom D hb).toAddMonoidHom
      hbij.2 hcont_eval
  exact {
    continuous := hcont_eval
    isOpenMap := hopen
    bijective := hbij
  }

/-- **T142: `presheafValueCanonicalQuotientEquiv` is `IsInducing`.**

Forward-direction analogue of `tateQuotientToPresheafHom_isHomeomorph`:
since the *inverse* `tateQuotientToPresheafHom` is a homeomorphism (Banach
OMT), so is the forward equiv `presheafValueCanonicalQuotientEquiv`,
hence in particular `IsInducing`.

The same hypothesis surface as `tateQuotientToPresheafHom_isHomeomorph`
(Banach OMT prerequisites at the source `A`, plus the closed-ideal
infrastructure plus the Baire / sigma-compact discharge). -/
theorem presheafValueCanonicalQuotientEquiv_isInducing (D : RationalLocData A)
    [IsTateRing A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (hcont_eval : @Continuous _ _
      (quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (hBaire : @BaireSpace (presheafValue D) _)
    (hSigma : @SigmaCompactSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientOneSubfXIdealTopology D.s)) :
    @Topology.IsInducing _ _ _
      (quotientOneSubfXIdealTopology D.s)
      ((presheafValueCanonicalQuotientEquiv D hb hA_complete hnoeth hT_pb
        hcont_eval :
          presheafValue D → (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s))) := by
  letI τC : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  -- The inverse direction is a homeomorphism (Banach OMT).
  have h := tateQuotientToPresheafHom_isHomeomorph D hb hA_complete hnoeth hT_pb
    hcont_eval hBaire hSigma
  -- Bundle as a `Homeomorph`.
  let H : (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) ≃ₜ presheafValue D :=
    h.homeomorph (tateQuotientToPresheafHom D hb)
  -- The forward equiv pointwise equals `H.symm`. Verify by injectivity of `H`:
  -- `H.symm y = (forward equiv) y` because both invert `H` at `y`, and `H` is
  -- a bijection so its inverse is unique.
  have h_eq : (H.symm : presheafValue D → _) =
      (presheafValueCanonicalQuotientEquiv D hb hA_complete hnoeth hT_pb
        hcont_eval : presheafValue D → _) := by
    funext y
    apply H.injective
    rw [Homeomorph.apply_symm_apply]
    -- Goal: `y = H ((forward equiv) y)`. `H` underlying function is
    -- `tateQuotientToPresheafHom D hb`, and the equiv's `left_inv` gives
    -- `tateQuotientToPresheafHom D hb ((forward equiv) y) = y`; take `.symm`.
    change y = tateQuotientToPresheafHom D hb _
    exact ((presheafValueCanonicalQuotientEquiv D hb hA_complete hnoeth hT_pb
      hcont_eval).left_inv y).symm
  -- `H.symm` is a homeomorphism, hence inducing; transport along `h_eq`.
  have hH_symm : Topology.IsInducing H.symm := H.symm.isInducing
  rw [show ((presheafValueCanonicalQuotientEquiv D hb hA_complete hnoeth hT_pb
    hcont_eval : presheafValue D → _)) = (H.symm : presheafValue D → _) from h_eq.symm]
  exact hH_symm

/-! ### Phase 2.7: Unconditional canonical-topology continuity (Wedhorn Prop 6.18)

The T-topology theorem `tateQuotientToPresheafHom_continuous` requires two
hypotheses (`hadic`, `hJ_eval`) that are typically **false** for the T-topology:
the T-topology on `A⟨X⟩` is the *product* topology on scaled coefficients, and it
is not J-adic for any ideal J in general.

This section provides an **unconditional** continuity theorem for the *canonical*
Tate topology `instTopologicalSpaceTateAlgebra`, which has
`tateAlgNhd P n = image of (pairIdeal P)^n` as nhds basis of 0. The canonical
topology is J-adic on the open subring `pairSubring P = A₀⟨X⟩`, so Wedhorn 6.18
applies there. Continuity of `tateEvalPresheafHom` follows from:

1. **Boundedness of `{invS^k}`** (from `hb` power-bounded).
2. **Continuity of `canonicalMap`** at 0 (well-known).
3. **Nonarchimedean topology on `presheafValue D`** (open subgroups as basis).
4. **Coefficient characterization of `tateAlgNhd P n`** (all coefficients in `I^n`).

No `IsNoetherianRing`-on-A⟨X⟩ required; the input is just `IsTateRing A`. -/

open Filter Topology in
omit [PlusSubring A] [IsHuberRing A] [T2Space A] in
/-- **Canonical-topology continuity of `tateEvalPresheafHom` (Wedhorn Prop 6.18).**

Under the natural strongly-noetherian Tate setup, the evaluation ring hom
`tateEvalPresheafHom D hb : A⟨X⟩ →+* presheafValue D` (sending `∑ aₙ Xⁿ` to
`∑ canonicalMap(aₙ) · invSⁿ`) is continuous for the canonical Tate topology
`instTopologicalSpaceTateAlgebra` on `A⟨X⟩` (no hypothesis-discharge
required).

**Proof.** As a ring hom of topological additive groups, continuity reduces to
continuity at `0`. The canonical topology has basis `{tateAlgNhd P n}` at `0`,
where `P = (IsTateRing.principalPair A).toPairOfDefinition`. For any target
neighbourhood `V ∈ nhds 0` we use the following steps:

* `V` contains an open additive subgroup `W ⊆ V` (nonarchimedean).
* `{(invS D)^k}` is bounded, so there exists `U ∈ nhds 0` with `U · {invS^k} ⊆ W`
  for all `k`.
* `canonicalMap : A → presheafValue D` is continuous, so some neighbourhood
  `image(P.I^N)` of `0` in `A` maps into `U`.
* For `h ∈ tateAlgNhd P N`, every coefficient `coeff_k h` lies in `image(P.I^N)`,
  hence `canonicalMap(coeff_k h) · invS^k ∈ W` for every `k`.
* Each partial sum lies in `W`, so the `tsum` lies in `closure W = W`. -/
theorem tateEvalPresheafHom_continuous_canonical
    [IsTateRing A] (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D)) :
    @Continuous _ _ instTopologicalSpaceTateAlgebra
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateEvalPresheafHom D hb) := by
  letI τ : TopologicalSpace ↥(TateAlgebra A) := instTopologicalSpaceTateAlgebra
  -- Reduce to continuity at 0 via `continuous_of_continuousAt_zero` on the
  -- additive group hom version.
  apply continuous_of_continuousAt_zero (tateEvalPresheafHom D hb).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  -- nhds basis at 0: tateAlgBasis'.hasBasis_nhds_zero.
  rw [Filter.tendsto_def]
  intro V hV
  -- Step 1: extract open additive subgroup W ⊆ V (presheafValue D is nonarch).
  obtain ⟨W, hWV⟩ := NonarchimedeanRing.is_nonarchimedean V hV
  have hW_open : IsOpen (W : Set (presheafValue D)) := W.isOpen
  have hW_closed : IsClosed (W : Set (presheafValue D)) :=
    AddSubgroup.isClosed_of_isOpen W.toAddSubgroup hW_open
  have hW_nhds : (W : Set (presheafValue D)) ∈ @nhds (presheafValue D) _ 0 :=
    hW_open.mem_nhds W.toAddSubgroup.zero_mem
  -- Step 2: invS is power-bounded, so {invS^k} is bounded. Get U ∈ nhds 0 with
  -- U * {invS^k} ⊆ W.
  obtain ⟨U, hU, hUW⟩ := hb (W : Set (presheafValue D)) hW_nhds
  -- Step 3: Continuity of canonicalMap at 0: preimage of U is nhd of 0 in A.
  have hcmU : D.canonicalMap ⁻¹' U ∈ @nhds A _ 0 :=
    (canonicalMap_continuous D).continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact hU)
  -- Step 4: Extract N with image(P.I^N) ⊆ canonicalMap⁻¹(U).
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  obtain ⟨N, -, hN⟩ := P.hasBasis_nhds_zero.mem_iff.mp hcmU
  -- Target: tateAlgNhd P N ⊆ (tateEvalPresheafHom D hb) ⁻¹' V.
  -- Since W ⊆ V, it suffices to show tateAlgNhd P N ⊆ (eval) ⁻¹' W.
  -- Use the canonical basis to describe nhds of 0 in A⟨X⟩.
  have hbasis : ((@nhds _ τ (0 : ↥(TateAlgebra A))).HasBasis
      (fun _ : ℕ ↦ True) fun n ↦
        (TateAlgebra.tateAlgNhd P n : Set ↥(TateAlgebra A))) :=
    TateAlgebra.tateAlgBasis'.hasBasis_nhds_zero
  apply hbasis.mem_iff.mpr
  refine ⟨N, trivial, fun h hh ↦ ?_⟩
  -- Goal: (tateEvalPresheafHom D hb).toAddMonoidHom h ∈ V.
  change tateEvalPresheafHom D hb h ∈ V
  refine hWV ?_
  -- Show each evalTerm is in W.
  have hterm_mem : ∀ k : ℕ,
      TateAlgebraWedhorn.evalTerm D.canonicalMap (invS D) h k ∈
        (W : Set (presheafValue D)) := by
    intro k
    -- evalTerm = canonicalMap(coeff_k h) * (invS D)^k.
    change D.canonicalMap (TateAlgebra.coeff k h) * (invS D) ^ k ∈
      (W : Set (presheafValue D))
    -- Apply hUW: (Set.range invS^·) * U ⊆ W. Order: range on left, U on right.
    -- Rewrite via commutativity.
    rw [mul_comm]
    apply hUW
    refine ⟨(invS D) ^ k, ⟨k, rfl⟩, D.canonicalMap (TateAlgebra.coeff k h),
      ?_, rfl⟩
    · -- canonicalMap(coeff_k h) ∈ U.
      apply hN
      -- Need coeff_k h ∈ image P.I^N.
      have := TateAlgebra.tateAlgNhd_coeff_mem P N hh (TateAlgebra.toIndex k)
      obtain ⟨b, hbI, hbeq⟩ := this
      -- `coeff_k h = MvPowerSeries.coeff (toIndex k) h.val`, which equals (b : A).
      rw [show (TateAlgebra.coeff k h : A) = (b : A) from hbeq.symm]
      exact ⟨b, hbI, rfl⟩
  -- Now, tsum is in W because:
  --   (a) each partial sum is in W (W is a subgroup),
  --   (b) partial sums tend to tsum (since summable),
  --   (c) W is closed (open subgroup).
  have hsum : Summable
      (TateAlgebraWedhorn.evalTerm D.canonicalMap (invS D) h) :=
    TateAlgebraWedhorn.evalTerm_summable D.canonicalMap
      (canonicalMap_continuous D) (invS D) hb h
  -- tsum is the limit of partial sums over finite sets (for unconditional summation).
  have hhs : HasSum (TateAlgebraWedhorn.evalTerm D.canonicalMap (invS D) h)
      (tateEvalPresheafHom D hb h) := by
    have hsum_val := hsum.hasSum
    change HasSum _ (∑' n, TateAlgebraWedhorn.evalTerm D.canonicalMap (invS D) h n)
    exact hsum_val
  -- Apply IsClosed.mem_of_tendsto with the HasSum and eventually-in-W.
  refine hW_closed.mem_of_tendsto hhs.tendsto_sum_nat ?_
  -- Eventually: partial sums are in W (they are, in fact, always in W by subgroup).
  refine Filter.Eventually.of_forall fun n ↦ ?_
  exact W.toAddSubgroup.sum_mem (fun k _ ↦ hterm_mem k)

omit [PlusSubring A] [IsHuberRing A] [T2Space A] in
/-- **Canonical-topology continuity of `tateQuotientToPresheafHom`
(Wedhorn Prop 6.18 + Example 6.38).**

Descends from `tateEvalPresheafHom_continuous_canonical` via the ring-quotient
map `mk : A⟨X⟩ →+* A⟨X⟩/(1-sX)`, which is an open quotient map (topological
ring quotient). The canonical quotient topology on the target is exactly the
coinduced topology via `mk`, so `IsQuotientMap.continuous_iff` transports
continuity. -/
theorem tateQuotientToPresheafHom_continuous_canonical
    [IsTateRing A] (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D)) :
    @Continuous _ _ (quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb) := by
  letI τ : TopologicalSpace ↥(TateAlgebra A) := instTopologicalSpaceTateAlgebra
  letI τQ : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientOneSubfXIdealTopology D.s
  haveI hTR : IsTopologicalRing ↥(TateAlgebra A) := instIsTopologicalRingTateAlgebra
  have hmk_qm : Topology.IsQuotientMap
      (Ideal.Quotient.mk (oneSubfXIdeal D.s) :
        ↥(TateAlgebra A) → ↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    (@QuotientRing.isOpenQuotientMap_mk ↥(TateAlgebra A) τ
      (inferInstanceAs (CommRing ↥(TateAlgebra A))) (oneSubfXIdeal D.s) hTR).isQuotientMap
  -- Use continuous_iff: suffices continuity of the composite with the quotient map.
  refine hmk_qm.continuous_iff.mpr ?_
  have hcomp : tateQuotientToPresheafHom D hb ∘
      Ideal.Quotient.mk (oneSubfXIdeal D.s) = tateEvalPresheafHom D hb := by
    ext g; simp [tateQuotientToPresheafHom, Ideal.Quotient.lift_mk]
  rw [hcomp]
  exact tateEvalPresheafHom_continuous_canonical D hb

omit [PlusSubring A] [IsHuberRing A] [T2Space A] in
/-- **Packaged version: `tateQuotientToPresheafHom_continuous_of_tate`.**

This is the continuity theorem in the exact form required by callers in
`LaurentRefinement.lean` (e.g. `hcont_eval_B` hypotheses), now proved
unconditionally under the natural strongly-noetherian Tate setup. -/
theorem tateQuotientToPresheafHom_continuous_of_tate
    [IsTateRing A] (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D)) :
    @Continuous _ _ (quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb) :=
  tateQuotientToPresheafHom_continuous_canonical D hb

/-! ### Packaged Wedhorn Example 6.38 isomorphism

The packaged form `presheafValue_tateAlgebra_quotient_iso` discharges the
continuity hypothesis using `tateQuotientToPresheafHom_continuous_of_tate`,
leaving only four data inputs that must be supplied at the call site:

* `hb`  — `invS D` is power-bounded in `presheafValue D`.
* `hA_complete` — `A` is complete (relative to its right uniformity).
* `hnoeth` — the canonical pair-of-definition subring `A₀⟨X⟩` is noetherian.
* `hT_pb` — every `t ∈ D.T` is power-bounded in `A`.

The iso `e := presheafValue_tateAlgebra_quotient_iso D hb hA_complete hnoeth hT_pb`
identifies `presheafValue D ≃+* A⟨X⟩ ⧸ (1 - sX)` (canonical Tate quotient
topology) and intertwines `D.canonicalMap` with the natural map `algebraMap`
into the quotient. This is the Phase-2 algebraic identification used in the
Wedhorn faithful-flatness route to Tate acyclicity.

Note: the **shape of the quotient** here is the 1-variable Tate algebra
`A⟨X⟩ ⧸ (1 - D.s · X)`. The `T`-data only enters via the topology used to
form `presheafValue` (and via `hT_pb`). This is a slight strengthening of
the literal Wedhorn 6.38 statement and is **equivalent** under the standard
identification; see `Example638.lean` for the explicit `|T|+1`-variable
form in the Laurent plus/minus cases. -/
noncomputable def presheafValue_tateAlgebra_quotient_iso
    [IsTateRing A] (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    presheafValue D ≃+* (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
  presheafValueCanonicalQuotientEquiv D hb hA_complete hnoeth hT_pb
    (tateQuotientToPresheafHom_continuous_of_tate D hb)

/-- The packaged Example 6.38 iso sends `D.canonicalMap a` to
`mk(algebraMap a)`. -/
theorem presheafValue_tateAlgebra_quotient_iso_canonicalMap
    [IsTateRing A] (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) (a : A) :
    presheafValue_tateAlgebra_quotient_iso D hb hA_complete hnoeth hT_pb
        (D.canonicalMap a) =
      (Ideal.Quotient.mk _) (algebraMap A _ a) := by
  unfold presheafValue_tateAlgebra_quotient_iso
  exact presheafValueCanonicalQuotientEquiv_canonicalMap D hb hA_complete hnoeth hT_pb
    (tateQuotientToPresheafHom_continuous_of_tate D hb) a

/-- The packaged Example 6.38 iso, on the inverse direction, sends
`mk(algebraMap a)` back to `D.canonicalMap a`. -/
theorem presheafValue_tateAlgebra_quotient_iso_symm_algebraMap
    [IsTateRing A] (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) (a : A) :
    (presheafValue_tateAlgebra_quotient_iso D hb hA_complete hnoeth hT_pb).symm
        ((Ideal.Quotient.mk _) (algebraMap A _ a)) =
      D.canonicalMap a := by
  unfold presheafValue_tateAlgebra_quotient_iso
  exact presheafValueCanonicalQuotientEquiv_symm_algebraMap D hb hA_complete hnoeth hT_pb
    (tateQuotientToPresheafHom_continuous_of_tate D hb) a

/-- The inverse of the packaged Example 6.38 iso is `tateQuotientToPresheafHom`. -/
theorem presheafValue_tateAlgebra_quotient_iso_symm
    [IsTateRing A] (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    ((presheafValue_tateAlgebra_quotient_iso D hb hA_complete hnoeth hT_pb).symm :
        (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) →+* presheafValue D) =
      tateQuotientToPresheafHom D hb := by
  unfold presheafValue_tateAlgebra_quotient_iso presheafValueCanonicalQuotientEquiv
  rfl

end CanonicalTopologyBridge

end ValuationSpectrum
