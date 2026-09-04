/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Combinatorics.EndHomogeneousErdosRado
/-!
# Finite-arity Erdős–Rado: the induction scaffold

The finite-arity induction toward the bounded finite-arity Erdős–Rado theorem:
the cardinal ladder `finiteERBound` (with its arithmetic validated against the beth scale),
the validated API (`FiniteArityHomogeneousUpTo`, `FiniteArityErdosRadoBounded`), the easy
arities `0`, `1`, `2` (`finiteArityHomogeneousUpTo_zero`/`_one`/`_two`), the last consuming the
proven generalized pair theorem `pairErdosRado_general_of_large`, the hard `n → n+1` induction
step `finiteArityHomogeneousUpTo_step` (end-homogenization via
`exists_endHomogeneous_of_large` + the induced top-arity color fed to the IH), and the
assembled bounded theorem `finiteArityErdosRadoBounded` with its `ℶ₁` instance.

The previously envisaged continuation
`FiniteArityErdosRadoBounded ℶ₁ → FiniteArityErdosRadoOmega1 ℶ₁ → morley_hanf` is DEAD at the
first arrow (statement audit 2026-07-07): the all-arity `FiniteArityErdosRadoOmega1` is
refutable in ZFC — it is the Erdős-cardinal partition relation `ℶ_ω₁ → (ω₁)^{<ω}`, whose
order-type-`ω` weakening already requires the inaccessible `κ(ω) ≤ ℶ_ω₁` (see the fences on
`FiniteArityErdosRadoOmega1` and `PureColoringHypothesis`). The obstruction the earlier
docstring flagged (per-`N` outputs cannot be iterated; an `ω`-schedule of passes needs an
infinite descending sequence of ladder levels) is that refutation's shadow. The bounded
theorem here is instead the per-stage approximation supply of the classical Morley/Hanf
template route (Marker §5.2): instantiating the color/output parameter at `κ := ℶ_α` gives
`ℶ_α⁺`-sized homogeneous-up-to-`N` suborders for the consistency-property certification, with
the indiscernible sequence materializing in the constructed model, not in the source.

## The ladder

Level `N` of `finiteERBound κ` is enough source to homogenize all arities `≤ N` with output
`κ⁺`. The recursion `level (n+2) = succ (2 ^ level (n+1))` is sized so that generalized pair
ER at color bound `finiteERBound κ (n+1)`, applied to a source of size `finiteERBound κ (n+2)`,
outputs a suborder of size `succ (finiteERBound κ (n+1))` — ample source for stage `n+1`.
At `κ = ℶ₁` every level sits below `ℶ_{ω₁}` (`finiteERBound_le_beth_omega1`): each ladder step
`succ ∘ (2 ^ ·)` is absorbed by two beth steps (`finiteERBound_beth_one_le`).
-/

open FirstOrder.Combinatorics.PairERGen
open FirstOrder.Combinatorics.EndHomogER

/-! ## The cardinal ladder -/

/-- Source-size ladder; level `N` is enough source to homogenize all arities `≤ N` with
output `κ⁺`. Level `0`/`1` = `κ⁺` (nothing to do / point pigeonhole);
level `n+2` = `succ (2 ^ level (n+1))`, sized so that generalized pair ER **at color bound
`finiteERBound κ (n+1)`** applied to a source of size `finiteERBound κ (n+2)` outputs a
suborder of size `succ (finiteERBound κ (n+1))`, ample source for stage `n+1`. -/
private noncomputable def finiteERBound (κ : Cardinal.{0}) : ℕ → Cardinal.{0}
  | 0 => Order.succ κ
  | 1 => Order.succ κ
  | (n + 2) => Order.succ ((2 : Cardinal.{0}) ^ finiteERBound κ (n + 1))

/-! ## Ladder lemmas -/

section LadderLemmas

/-- Ladder level `0` is `κ⁺`. -/
private theorem finiteERBound_zero (κ : Cardinal.{0}) : finiteERBound κ 0 = Order.succ κ := rfl



/-- The ladder recursion, as an equality: level `n+2` is exactly the generalized-pair-ER
source bound for color bound `finiteERBound κ (n+1)`. -/
private theorem finiteERBound_succ_succ (κ : Cardinal.{0}) (n : ℕ) :
    finiteERBound κ (n + 2) = Order.succ ((2 : Cardinal.{0}) ^ finiteERBound κ (n + 1)) := rfl

/-- Every ladder level dominates `κ⁺`. -/
private theorem succ_le_finiteERBound (κ : Cardinal.{0}) : ∀ n : ℕ, Order.succ κ ≤ finiteERBound κ n
  | 0 => le_rfl
  | 1 => le_rfl
  | (n + 2) => by
    rw [finiteERBound_succ_succ]
    have hκ : κ ≤ (2 : Cardinal.{0}) ^ finiteERBound κ (n + 1) :=
      ((Order.le_succ κ).trans (succ_le_finiteERBound κ (n + 1))).trans (Cardinal.cantor _).le
    exact Order.succ_le_succ hκ



/-- Every ladder level of index `≥ 2` dominates the generalized pair-ER source bound
`succ (2 ^ κ)` — this is what lets the arity-2 theorem consume any level `≥ 2`. -/
private theorem pair_source_le_finiteERBound (κ : Cardinal.{0}) (n : ℕ) :
    Order.succ ((2 : Cardinal.{0}) ^ κ) ≤ finiteERBound κ (n + 2) := by
  rw [finiteERBound_succ_succ]
  have hκ : κ ≤ finiteERBound κ (n + 1) :=
    (Order.le_succ κ).trans (succ_le_finiteERBound κ (n + 1))
  exact Order.succ_le_succ (Cardinal.power_le_power_left two_ne_zero hκ)



/-- `ℶ_{o+1} = 2 ^ ℶ_o`, with the successor index written additively. -/
private lemma beth_add_one (o : Ordinal.{0}) :
    Cardinal.beth (o + 1) = 2 ^ Cardinal.beth o := by
  rw [← Order.succ_eq_add_one, Cardinal.beth_succ]

/-- `(ℶ_o)⁺ ≤ ℶ_{o+1}`: one beth step absorbs a cardinal successor (Cantor). -/
private lemma succ_beth_le (o : Ordinal.{0}) :
    Order.succ (Cardinal.beth o) ≤ Cardinal.beth (o + 1) := by
  rw [beth_add_one]
  exact succ_le_two_power _

/-- At `κ = ℶ₁`, ladder level `n` is bounded by `ℶ_{2n+2}`: each ladder step
`succ ∘ (2 ^ ·)` costs strictly more than one beth step (the inner `succ`), but two beth
steps absorb it. -/
private theorem finiteERBound_beth_one_le :
    ∀ n : ℕ, finiteERBound (Cardinal.beth 1) n ≤ Cardinal.beth ((2 * n + 2 : ℕ) : Ordinal)
  | 0 => by
    have h : ((2 * 0 + 2 : ℕ) : Ordinal.{0}) = (1 : Ordinal) + 1 := by
      rw [show (2 * 0 + 2 : ℕ) = 2 from rfl, Nat.cast_ofNat, one_add_one_eq_two]
    rw [finiteERBound_zero, h]
    exact succ_beth_le 1
  | 1 => by
    have h0 : finiteERBound (Cardinal.beth 1) 0 ≤ Cardinal.beth ((2 * 0 + 2 : ℕ) : Ordinal) :=
      finiteERBound_beth_one_le 0
    have hle : ((2 * 0 + 2 : ℕ) : Ordinal.{0}) ≤ ((2 * 1 + 2 : ℕ) : Ordinal.{0}) :=
      Nat.mono_cast (by omega)
    exact h0.trans (Cardinal.beth_le_beth.mpr hle)
  | (n + 2) => by
    have ih : finiteERBound (Cardinal.beth 1) (n + 1)
        ≤ Cardinal.beth ((2 * (n + 1) + 2 : ℕ) : Ordinal) := finiteERBound_beth_one_le (n + 1)
    calc finiteERBound (Cardinal.beth 1) (n + 2)
        = Order.succ (2 ^ finiteERBound (Cardinal.beth 1) (n + 1)) :=
          finiteERBound_succ_succ _ n
      _ ≤ Order.succ (2 ^ Cardinal.beth ((2 * (n + 1) + 2 : ℕ) : Ordinal)) :=
          Order.succ_le_succ (Cardinal.power_le_power_left two_ne_zero ih)
      _ = Order.succ (Cardinal.beth (((2 * (n + 1) + 2 : ℕ) : Ordinal) + 1)) := by
          rw [beth_add_one]
      _ ≤ Cardinal.beth ((((2 * (n + 1) + 2 : ℕ) : Ordinal) + 1) + 1) := succ_beth_le _
      _ = Cardinal.beth ((2 * (n + 2) + 2 : ℕ) : Ordinal) := by
          -- `↑(2*(n+1)+2) + 1 + 1` and `↑(2*(n+2)+2)` are definitionally equal ordinals.
          congr 1

/-- At `κ = ℶ₁`, every ladder level is strictly below `ℶ_{ω₁}` — the source size the
Morley–Hanf chain supplies dominates every finite stage. -/
private theorem finiteERBound_lt_beth_omega1 (n : ℕ) :
    finiteERBound (Cardinal.beth 1) n < Cardinal.beth (Ordinal.omega 1) :=
  (finiteERBound_beth_one_le n).trans_lt (Cardinal.beth_lt_beth.mpr
    ((Ordinal.natCast_lt_omega0 _).trans Ordinal.omega0_lt_omega_one))

/-- At `κ = ℶ₁`, every ladder level is at most `ℶ_{ω₁}` (the form consumed when feeding a
`ℶ_{ω₁}`-sized source into a finite ladder stage). -/
private theorem finiteERBound_le_beth_omega1 (n : ℕ) :
    finiteERBound (Cardinal.beth 1) n ≤ Cardinal.beth (Ordinal.omega 1) :=
  (finiteERBound_lt_beth_omega1 n).le

/-- **The general beth-scheduled ladder bound**: at `κ = ℶ_α`, ladder level `N` is bounded by
`ℶ_{α + 2N + 2}` — each ladder step `succ ∘ (2 ^ ·)` is absorbed by two beth steps, uniformly
in the base index `α` (the `α = 1` bound above is the sharper special case; this one is loose
on purpose — the goal is a reusable scheduled estimate, not sharpness). This is the arithmetic
behind the Marker-style consistency-property schedule: per-arity Erdős–Rado approximations at
every base `ℶ_α`, `α < ω₁`, all fed from a `ℶ_{ω₁}`-sized source. -/
private theorem finiteERBound_beth_le (α : Ordinal.{0}) :
    ∀ N : ℕ, finiteERBound (Cardinal.beth α) N ≤ Cardinal.beth (α + ((2 * N + 2 : ℕ) : Ordinal))
  | 0 => by
    rw [finiteERBound_zero]
    have h1 : (1 : Ordinal.{0}) ≤ ((2 * 0 + 2 : ℕ) : Ordinal) := by simp
    exact (succ_beth_le α).trans (Cardinal.beth_le_beth.mpr (add_le_add le_rfl h1))
  | 1 => by
    have h0 : finiteERBound (Cardinal.beth α) 0
        ≤ Cardinal.beth (α + ((2 * 0 + 2 : ℕ) : Ordinal)) := finiteERBound_beth_le α 0
    have hle : ((2 * 0 + 2 : ℕ) : Ordinal.{0}) ≤ ((2 * 1 + 2 : ℕ) : Ordinal) :=
      Nat.mono_cast (by omega)
    exact h0.trans (Cardinal.beth_le_beth.mpr (add_le_add le_rfl hle))
  | (n + 2) => by
    have ih : finiteERBound (Cardinal.beth α) (n + 1)
        ≤ Cardinal.beth (α + ((2 * (n + 1) + 2 : ℕ) : Ordinal)) := finiteERBound_beth_le α (n + 1)
    calc finiteERBound (Cardinal.beth α) (n + 2)
        = Order.succ (2 ^ finiteERBound (Cardinal.beth α) (n + 1)) :=
          finiteERBound_succ_succ _ n
      _ ≤ Order.succ (2 ^ Cardinal.beth (α + ((2 * (n + 1) + 2 : ℕ) : Ordinal))) :=
          Order.succ_le_succ (Cardinal.power_le_power_left two_ne_zero ih)
      _ = Order.succ (Cardinal.beth ((α + ((2 * (n + 1) + 2 : ℕ) : Ordinal)) + 1)) := by
          rw [beth_add_one]
      _ ≤ Cardinal.beth ((α + ((2 * (n + 1) + 2 : ℕ) : Ordinal)) + 1 + 1) := succ_beth_le _
      _ = Cardinal.beth (α + ((2 * (n + 2) + 2 : ℕ) : Ordinal)) := by
          have h : ((2 * (n + 2) + 2 : ℕ) : Ordinal.{0})
              = ((2 * (n + 1) + 2 : ℕ) : Ordinal) + 1 + 1 := by
            rw [show (2 * (n + 2) + 2 : ℕ) = (2 * (n + 1) + 2) + 1 + 1 from by omega,
              Nat.cast_add, Nat.cast_add, Nat.cast_one]
          rw [h, ← add_assoc, ← add_assoc]

end LadderLemmas

/-! ## The API -/

/-- Homogeneity up to arity `N`: the exact statement the finite-arity induction will prove.
Any well-ordered source of size `≥ finiteERBound κ N` and any `ℕ`-indexed family of colorings
with color types of size `≤ κ` admit a single `κ⁺`-suborder homogeneous for **all** arities
`≤ N` simultaneously. The family is `ℕ`-indexed from the start, per the design note that the
all-arity theorem must recurse internally over arity, not iterate over the external
sequence. -/
private def FiniteArityHomogeneousUpTo (κ : Cardinal.{0}) (N : ℕ) : Prop :=
  ∀ (I : Type) [LinearOrder I] [WellFoundedLT I],
    Cardinal.mk I ≥ finiteERBound κ N →
    ∀ (C : ℕ → Type) (_ : ∀ n, Cardinal.mk (C n) ≤ κ) (c : ∀ n, (Fin n ↪o I) → C n),
    ∃ e : (Order.succ κ).ord.ToType ↪o I,
      ∀ n, n ≤ N → ∀ t t' : Fin n ↪o I,
        (∀ k, t k ∈ Set.range e) → (∀ k, t' k ∈ Set.range e) →
        c n t = c n t'

/-- The bounded finite-arity residual: homogeneity up to every finite arity, each stage fed
by its own ladder level. This is the target of the finite-arity induction; the arrow
`FiniteArityErdosRadoBounded ℶ₁ → FiniteArityErdosRadoOmega1 ℶ₁` (one `ω₁`-suborder for all
arities at once from a `ℶ_{ω₁}`-sized source) is a separate, careful step — the per-`N`
outputs cannot be iterated. -/
def FiniteArityErdosRadoBounded (κ : Cardinal.{0}) : Prop :=
  ∀ N : ℕ, FiniteArityHomogeneousUpTo κ N

/-! ## Small utilities: arity-0/1/2 order embeddings and no-max output -/

section Utilities

variable {I : Type*} [LinearOrder I]

instance : Subsingleton (Fin 0 ↪o I) :=
  ⟨fun t t' => DFunLike.ext t t' fun k => k.elim0⟩

/-- The one-point order embedding `Fin 1 ↪o I` at `x` (strict monotonicity is vacuous on the
subsingleton `Fin 1`). -/
private def singletonOE (x : I) : Fin 1 ↪o I :=
  OrderEmbedding.ofStrictMono (fun _ => x) fun a b hab =>
    absurd (Subsingleton.elim a b) (ne_of_lt hab)

/-- Every `Fin 1 ↪o I` is the one-point embedding at its value. -/
private theorem orderEmbedding_fin_one_eq (t : Fin 1 ↪o I) : t = singletonOE (t 0) := by
  refine DFunLike.ext t _ fun k => ?_
  rw [Fin.eq_zero k]
  rfl

/-- Every `Fin 2 ↪o I` with prescribed endpoint values is the corresponding `pairEmbed`
(stated flexibly so the `<`-proof can be supplied through the endpoints of any suborder). -/
private theorem orderEmbedding_fin_two_eq_pairEmbed (t : Fin 2 ↪o I) {u v : I} (h : u < v)
    (h0 : t 0 = u) (h1 : t 1 = v) : t = pairEmbed h := by
  refine DFunLike.ext t _ fun k => ?_
  match k with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1

/-- The output order `(succ κ).ord.ToType` has no maximum for infinite `κ`: `(succ κ).ord`
is closed under ordinal successor (`succ_lt_ord_of_lt`), so every element has a strict
upper bound. Supplies the second pair element the arity-1 endgame of the arity-2 theorem
needs. -/
private theorem exists_gt_succOrdToType {κ : Cardinal.{0}} (hκ : Cardinal.aleph0 ≤ κ)
    (x : (Order.succ κ).ord.ToType) : ∃ y : (Order.succ κ).ord.ToType, x < y := by
  set d : Set.Iio (Order.succ κ).ord := Ordinal.ToType.mk.symm x
  have hδ : d.1 < (Order.succ κ).ord := d.2
  have hsucc : Order.succ d.1 < (Order.succ κ).ord := succ_lt_ord_of_lt hκ hδ
  refine ⟨Ordinal.ToType.mk ⟨Order.succ d.1, hsucc⟩, ?_⟩
  have hx : x = Ordinal.ToType.mk d := (Ordinal.ToType.mk.apply_symm_apply x).symm
  rw [hx]
  exact Ordinal.ToType.mk.lt_iff_lt.mpr
    (show d < ⟨Order.succ d.1, hsucc⟩ from Order.lt_succ d.1)

end Utilities

/-! ## Tuple factoring and decomposition -/

section Factoring

/-- Factor a finite tuple through an order embedding: a tuple whose values lie in the range
of `f : J ↪o I` is the `f`-image of a (unique) tuple in `J`. The order structure transports
back through `f.lt_iff_lt`, so the preimage tuple is again an order embedding. -/
theorem exists_orderEmbedding_factor {J I : Type*} [LinearOrder J] [LinearOrder I]
    {m : ℕ} (f : J ↪o I) (t : Fin m ↪o I) (ht : ∀ k, t k ∈ Set.range f) :
    ∃ s : Fin m ↪o J, s.trans f = t := by
  choose g hg using ht
  have hmono : StrictMono g := fun a b hab =>
    f.lt_iff_lt.mp (by rw [hg a, hg b]; exact t.strictMono hab)
  exact ⟨OrderEmbedding.ofStrictMono g hmono, DFunLike.ext _ _ hg⟩

/-- Every `(n+2)`-tuple is its `castSucc`-prefix extended by its last point — the
decomposition through which end-homogeneity reaches an arbitrary top-arity tuple. -/
private theorem eq_appendLastOE {I : Type*} [LinearOrder I] {n : ℕ} (t : Fin (n + 2) ↪o I) :
    t = appendLastOE (Fin.castSuccOrderEmb.trans t) (t (Fin.last (n + 1)))
      (fun k => t.strictMono (Fin.castSucc_lt_last k)) := by
  refine DFunLike.ext _ _ fun k => ?_
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [appendLastOE_last (Fin.castSuccOrderEmb.trans t) (t (Fin.last (n + 1)))
      (fun k => t.strictMono (Fin.castSucc_lt_last k))]
  · rw [appendLastOE_castSucc (Fin.castSuccOrderEmb.trans t) (t (Fin.last (n + 1)))
      (fun k => t.strictMono (Fin.castSucc_lt_last k))]
    rfl

end Factoring

/-! ## The easy arities: `0`, `1`, `2` -/

/-- **Arity `≤ 0`.** Homogeneity up to arity `0` from a `κ⁺`-sized source: there is nothing
to homogenize (`Fin 0 ↪o I` is a subsingleton), so any `κ⁺`-suborder works. -/
private theorem finiteArityHomogeneousUpTo_zero (κ : Cardinal.{0}) (_hκ : Cardinal.aleph0 ≤ κ) :
    FiniteArityHomogeneousUpTo κ 0 := by
  intro I _ _ hI C hC c
  have hI' : Order.succ κ ≤ Cardinal.mk I := hI
  obtain ⟨e⟩ := exists_ordToType_embedding_of_card_ge hI'
  refine ⟨e, ?_⟩
  intro n hn t t' ht ht'
  match n, hn with
  | 0, _ => exact congrArg (c 0) (Subsingleton.elim t t')
  | (m + 1), h => exact absurd h (by omega)

/-- **Arity `≤ 1`.** Homogeneity up to arity `1` from a `κ⁺`-sized source: point pigeonhole
(`exists_large_fiber_of_small_codomain`) on the point coloring `x ↦ c 1 (singletonOE x)`
yields a `κ⁺`-sized monochromatic fiber, which re-well-orders into a `κ⁺`-suborder. -/
private theorem finiteArityHomogeneousUpTo_one (κ : Cardinal.{0}) (hκ : Cardinal.aleph0 ≤ κ) :
    FiniteArityHomogeneousUpTo κ 1 := by
  intro I _ _ hI C hC c
  have hI' : Order.succ κ ≤ Cardinal.mk I := hI
  obtain ⟨b, hb⟩ := exists_large_fiber_of_small_codomain hκ hI' (hC 1)
    (fun x => c 1 (singletonOE x))
  obtain ⟨e₀⟩ := exists_ordToType_embedding_of_card_ge hb
  refine ⟨e₀.trans (OrderEmbedding.subtype _), ?_⟩
  have key : ∀ t : Fin 1 ↪o I,
      (∀ k, t k ∈ Set.range (e₀.trans (OrderEmbedding.subtype _))) → c 1 t = b := by
    intro t ht
    obtain ⟨m, hm⟩ := ht 0
    have hmem : c 1 (singletonOE (t 0)) = b := by
      rw [← hm]
      exact (e₀ m).2
    rw [orderEmbedding_fin_one_eq t]
    exact hmem
  intro n hn t t' ht ht'
  match n, hn with
  | 0, _ => exact congrArg (c 0) (Subsingleton.elim t t')
  | 1, _ => rw [key t ht, key t' ht']
  | (m + 2), h => exact absurd h (by omega)

/-- **Arity `≤ 2`.** Homogeneity up to arity `2` from a `finiteERBound κ 2`-sized source:
pack the pair color and the induced point color into `C 2 × C 1` (still of size `≤ κ`),
apply the generalized pair theorem `pairErdosRado_general_of_large`, and read the two
components back off the homogeneous suborder — arity `1` via the no-max lemma
(`exists_gt_succOrdToType` supplies a second pair element above any given point). -/
private theorem finiteArityHomogeneousUpTo_two (κ : Cardinal.{0}) (hκ : Cardinal.aleph0 ≤ κ) :
    FiniteArityHomogeneousUpTo κ 2 := by
  intro I _ _ hI C hC c
  have hD : Cardinal.mk (C 2 × C 1) ≤ κ := by
    calc Cardinal.mk (C 2 × C 1)
        = Cardinal.mk (C 2) * Cardinal.mk (C 1) := by simp
      _ ≤ κ * κ := mul_le_mul' (hC 2) (hC 1)
      _ = κ := Cardinal.mul_eq_self hκ
  have hI' : Order.succ ((2 : Cardinal.{0}) ^ κ) ≤ Cardinal.mk I :=
    (pair_source_le_finiteERBound κ 0).trans hI
  obtain ⟨f, b, hb⟩ := pairErdosRado_general_of_large κ hκ hD hI'
    (fun t => (c 2 t, c 1 (singletonOE (t 0))))
  refine ⟨f, ?_⟩
  have key1 : ∀ t : Fin 1 ↪o I, (∀ k, t k ∈ Set.range f) → c 1 t = b.2 := by
    intro t ht
    obtain ⟨x, hx⟩ := ht 0
    obtain ⟨y, hxy⟩ := exists_gt_succOrdToType hκ x
    have hcp := hb hxy
    have h0 : pairEmbed (f.strictMono hxy) 0 = f x := rfl
    rw [orderEmbedding_fin_one_eq t, ← hx, ← h0]
    exact congrArg Prod.snd hcp
  have key2 : ∀ t : Fin 2 ↪o I, (∀ k, t k ∈ Set.range f) → c 2 t = b.1 := by
    intro t ht
    obtain ⟨x, hx⟩ := ht 0
    obtain ⟨y, hy⟩ := ht 1
    have ht01 : t 0 < t 1 := t.strictMono (by decide)
    have hxy : x < y := f.lt_iff_lt.mp (by rw [hx, hy]; exact ht01)
    rw [orderEmbedding_fin_two_eq_pairEmbed t (f.strictMono hxy) hx.symm hy.symm]
    exact congrArg Prod.fst (hb hxy)
  intro n hn t t' ht ht'
  match n, hn with
  | 0, _ => exact congrArg (c 0) (Subsingleton.elim t t')
  | 1, _ => rw [key1 t ht, key1 t' ht']
  | 2, _ => rw [key2 t ht, key2 t' ht']
  | (m + 3), h => exact absurd h (by omega)

/-! ## The induction step -/

/-- **The induction step.** Homogeneity up to arity `n+1` implies homogeneity up to arity
`n+2`, from the next ladder level: end-homogenize the top-arity coloring with the engine
(`exists_endHomogeneous_of_large` at `lam := finiteERBound κ (n+1)` — the ladder recursion
is sized exactly so the level-`n+2` source meets the engine's `succ (2 ^ lam)` demand and
the engine's `lam⁺`-sized output meets the level-`n+1` demand), pull the coloring family
back to the end-homogeneous suborder together with the **induced top-arity color**
`ind s := c (n+2) (s ⌢ chosen-point-above)` — well-defined by end-homogeneity plus the
no-max lemma `exists_gt_succOrdToType` — and feed everything to the inductive hypothesis.
An arity-`(n+2)` tuple from the final suborder is then handled by decomposing it as
prefix-plus-last (`eq_appendLastOE`), swapping the last point for the chosen point above
its prefix (end-homogeneity), and reading off the induced color's constancy from the IH. -/
private theorem finiteArityHomogeneousUpTo_step (κ : Cardinal.{0}) (hκ : Cardinal.aleph0 ≤ κ) (n : ℕ)
    (ih : FiniteArityHomogeneousUpTo κ (n + 1)) : FiniteArityHomogeneousUpTo κ (n + 2) := by
  intro I _ _ hI C hC c
  set lam := finiteERBound κ (n + 1) with hlam_def
  have hκlam : κ ≤ lam := (Order.le_succ κ).trans (succ_le_finiteERBound κ (n + 1))
  have hlam : Cardinal.aleph0 ≤ lam := hκ.trans hκlam
  have hI' : Order.succ ((2 : Cardinal.{0}) ^ lam) ≤ Cardinal.mk I := by
    simpa [hlam_def, finiteERBound_succ_succ] using hI
  -- End-homogenize the top-arity coloring.
  obtain ⟨f, hf⟩ := exists_endHomogeneous_of_large lam hlam ((hC (n + 2)).trans hκlam) n hI'
    (c (n + 2))
  -- The no-max choice on the engine's output order.
  choose nxt hnxt using exists_gt_succOrdToType hlam
  have habove : ∀ (s : Fin (n + 1) ↪o (Order.succ lam).ord.ToType) (k : Fin (n + 1)),
      s k < nxt (s (Fin.last n)) :=
    fun s k => (s.monotone (Fin.le_last k)).trans_lt (hnxt _)
  -- The induced top-arity color of an `(n+1)`-tuple in the suborder.
  let ind : (Fin (n + 1) ↪o (Order.succ lam).ord.ToType) → C (n + 2) := fun s =>
    c (n + 2) (appendLastOE (s.trans f) (f (nxt (s (Fin.last n))))
      (fun k => f.strictMono (habove s k)))
  -- The second component of the pulled-back family: the induced color at arity `n+1`,
  -- `none` elsewhere.
  let extra : ∀ m, (Fin m ↪o (Order.succ lam).ord.ToType) → Option (C (n + 2)) :=
    Function.update (fun _ _ => none) (n + 1) (fun s => some (ind s))
  have hextra : extra (n + 1) = fun s => some (ind s) := Function.update_self _ _ _
  have hD : ∀ m, Cardinal.mk (C m × Option (C (n + 2))) ≤ κ := by
    intro m
    calc Cardinal.mk (C m × Option (C (n + 2)))
        = Cardinal.mk (C m) * (Cardinal.mk (C (n + 2)) + 1) := by
          simp [Cardinal.mk_option]
      _ ≤ κ * (κ + 1) := mul_le_mul' (hC m) (add_le_add (hC (n + 2)) le_rfl)
      _ = κ * κ := by rw [Cardinal.add_one_eq hκ]
      _ = κ := Cardinal.mul_eq_self hκ
  have hJ : Cardinal.mk ((Order.succ lam).ord.ToType) ≥ finiteERBound κ (n + 1) := by
    rw [Cardinal.mk_ord_toType]
    exact Order.le_succ lam
  -- Feed the pulled-back family (original colors + induced color) to the IH.
  obtain ⟨e, he⟩ := ih ((Order.succ lam).ord.ToType) hJ
    (fun m => C m × Option (C (n + 2))) hD
    (fun m s => (c m (s.trans f), extra m s))
  refine ⟨e.trans f, ?_⟩
  -- Factor a tuple from the final suborder through the composite embedding.
  have factor : ∀ {m : ℕ} (t : Fin m ↪o I), (∀ k, t k ∈ Set.range (e.trans f)) →
      ∃ s : Fin m ↪o (Order.succ lam).ord.ToType,
        (∀ k, s k ∈ Set.range e) ∧ s.trans f = t := by
    intro m t ht
    obtain ⟨w, hw⟩ := exists_orderEmbedding_factor (e.trans f) t ht
    exact ⟨w.trans e, fun k => ⟨w k, rfl⟩, hw⟩
  -- Every top-arity tuple from the suborder carries the induced color of its prefix.
  have key : ∀ (t : Fin (n + 2) ↪o I), (∀ k, t k ∈ Set.range (e.trans f)) →
      ∃ s : Fin (n + 1) ↪o (Order.succ lam).ord.ToType,
        (∀ k, s k ∈ Set.range e) ∧ c (n + 2) t = ind s := by
    intro t ht
    obtain ⟨s, hsr, hs⟩ := factor (Fin.castSuccOrderEmb.trans t) (fun k => ht k.castSucc)
    refine ⟨s, hsr, ?_⟩
    have hxlt : ∀ k : Fin (n + 1), (s.trans f) k < t (Fin.last (n + 1)) := fun k => by
      rw [DFunLike.congr_fun hs k]
      exact t.strictMono (Fin.castSucc_lt_last k)
    obtain ⟨u, hu⟩ := ht (Fin.last (n + 1))
    calc c (n + 2) t
        = c (n + 2) (appendLastOE (Fin.castSuccOrderEmb.trans t) (t (Fin.last (n + 1)))
            (fun k => t.strictMono (Fin.castSucc_lt_last k))) :=
          congrArg (c (n + 2)) (eq_appendLastOE t)
      _ = c (n + 2) (appendLastOE (s.trans f) (t (Fin.last (n + 1))) hxlt) :=
          congrArg (c (n + 2))
            (appendLastOE_congr (fun k => (DFunLike.congr_fun hs k).symm) rfl _ _)
      _ = c (n + 2) (appendLastOE (s.trans f) (f (nxt (s (Fin.last n))))
            (fun k => f.strictMono (habove s k))) :=
          hf (s.trans f) (t (Fin.last (n + 1))) (f (nxt (s (Fin.last n))))
            (fun k => ⟨s k, rfl⟩) ⟨e u, hu⟩ ⟨nxt (s (Fin.last n)), rfl⟩
            hxlt (fun k => f.strictMono (habove s k))
      _ = ind s := rfl
  -- The homogeneity conclusion, per arity.
  intro m hm t t' ht ht'
  obtain hlt | rfl := hm.lt_or_eq
  · -- Arities `≤ n+1`: the first component of the pulled-back family through the IH.
    have hm' : m ≤ n + 1 := Nat.lt_succ_iff.mp hlt
    obtain ⟨s, hsr, hs⟩ := factor t ht
    obtain ⟨s', hsr', hs'⟩ := factor t' ht'
    have h1 : c m (s.trans f) = c m (s'.trans f) :=
      congrArg Prod.fst (he m hm' s s' hsr hsr')
    rw [← hs, ← hs']
    exact h1
  · -- Arity `n+2`: end-homogeneity reduces to the induced color, constant by the IH.
    obtain ⟨s, hsr, hcs⟩ := key t ht
    obtain ⟨s', hsr', hcs'⟩ := key t' ht'
    have h2 : extra (n + 1) s = extra (n + 1) s' :=
      congrArg Prod.snd (he (n + 1) le_rfl s s' hsr hsr')
    have hxs : extra (n + 1) s = some (ind s) := congrFun hextra s
    have hxs' : extra (n + 1) s' = some (ind s') := congrFun hextra s'
    rw [hcs, hcs']
    exact Option.some_inj.mp ((hxs.symm.trans h2).trans hxs')

/-! ## The bounded finite-arity theorem -/

/-- Homogeneity up to every finite arity: ladder levels `0`/`1` are the proven base cases
and each higher level is one application of the induction step. (The step at `n = 0`
subsumes the independently validated `finiteArityHomogeneousUpTo_two`, which is kept as a
regression check on the statement.) -/
private theorem finiteArityHomogeneousUpTo_all (κ : Cardinal.{0}) (hκ : Cardinal.aleph0 ≤ κ) :
    ∀ N : ℕ, FiniteArityHomogeneousUpTo κ N
  | 0 => finiteArityHomogeneousUpTo_zero κ hκ
  | 1 => finiteArityHomogeneousUpTo_one κ hκ
  | (n + 2) =>
    finiteArityHomogeneousUpTo_step κ hκ n (finiteArityHomogeneousUpTo_all κ hκ (n + 1))

/-- **The bounded finite-arity Erdős–Rado theorem**: for every infinite color bound `κ` and
every finite arity bound `N`, any well-ordered source of size `≥ finiteERBound κ N` and any
`ℕ`-indexed coloring family with color types of size `≤ κ` admit a single `κ⁺`-suborder
homogeneous for all arities `≤ N` simultaneously. -/
theorem finiteArityErdosRadoBounded (κ : Cardinal.{0}) (hκ : Cardinal.aleph0 ≤ κ) :
    FiniteArityErdosRadoBounded κ :=
  finiteArityHomogeneousUpTo_all κ hκ



/-- **The Marker-stage Erdős–Rado supply**: from a source of size `≥ ℶ_{α + 2N + 2}` and any
`ℕ`-indexed coloring family with color types of size `≤ ℶ_α`, one `(ℶ_α)⁺`-suborder
homogeneous for all arities `≤ N` simultaneously.

This is the TRUE replacement for the false all-arity jump
(`FiniteArityErdosRadoOmega1` — refutable in ZFC, see its docstring and
`PureColoringHypothesis`): per-`α`, per-finite-`N` approximations, NOT one `ω₁`-suborder
homogeneous for all arities at once. It is exactly the per-stage lemma the classical
Morley/Hanf consistency-property schedule consumes [Marker, *Lectures on Infinitary Model
Theory*, §5.2]: for each finite formula/arity budget `N` and cofinally many `α < ω₁`, a
`ℶ_{ω₁}`-sized source dominates the demanded `ℶ_{α + 2N + 2}` (the beth index stays below
`ω₁`), yielding `ℶ_α`-large approximations of the EM template; the indiscernible sequence
itself materializes only in the model built by Model Existence, never in the source. -/
theorem finiteArityHomogeneousUpTo_beth_stage (α : Ordinal.{0}) (N : ℕ)
    {I : Type} [LinearOrder I] [WellFoundedLT I]
    (hI : Cardinal.beth (α + ((2 * N + 2 : ℕ) : Ordinal)) ≤ Cardinal.mk I)
    (C : ℕ → Type) (hC : ∀ n, Cardinal.mk (C n) ≤ Cardinal.beth α)
    (c : ∀ n, (Fin n ↪o I) → C n) :
    ∃ e : (Order.succ (Cardinal.beth α)).ord.ToType ↪o I,
      ∀ n, n ≤ N → ∀ t t' : Fin n ↪o I,
        (∀ k, t k ∈ Set.range e) → (∀ k, t' k ∈ Set.range e) →
        c n t = c n t' :=
  finiteArityHomogeneousUpTo_all (Cardinal.beth α) (Cardinal.aleph0_le_beth α) N I
    ((finiteERBound_beth_le α N).trans hI) C hC c
