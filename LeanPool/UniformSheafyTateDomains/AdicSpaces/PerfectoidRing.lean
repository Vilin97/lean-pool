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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PseudoUniformizer
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Uniform
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Valuation.Integers

/-!
# Perfectoid Rings and Fields

We define **perfectoid rings** and **perfectoid fields** following Scholze's
*Perfectoid Spaces* (2012), Definition 3.5.

## Main definitions

* `IsPerfectoidRing p A` : A Tate ring `A` is perfectoid (for a prime `p`) if it is
  complete, separated, uniform, and admits a pseudo-uniformizer `ϖ` such that `ϖ^p | p`
  in `A°` and the Frobenius is surjective on `A°/ϖ`.
* `IsPerfectoidField p K` : A perfectoid field is a perfectoid ring that is also a field.

## Implementation notes

The Frobenius surjectivity condition is expressed directly as:
for all power-bounded `x`, there exists power-bounded `y` and `z` with `x = y^p + ϖ·z`
and `z` power-bounded. This avoids forming the quotient ring `A°/ϖ` and establishing
`CharP` on it, which would require considerable typeclass infrastructure.

The condition `ϖ^p | p` is expressed as: there exists a power-bounded `c` with
`(p : A) = c * ϖ^p`. This says `p/ϖ^p ∈ A°`, which is the standard formulation.

## References

* [P. Scholze, *Perfectoid Spaces*][scholze2012perfectoid], Definition 3.5
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7
-/

@[expose] public section

open TopologicalRing ValuationSpectrum

universe u

-- `A°` (`powerBoundedSubring.toSubring`) and the power-bounded `A°`-subring API are now stated
-- with `[NonarchimedeanAddGroup A]`. For the genuine linear-topology setting used in this file,
-- that follows from `[IsLinearTopology A A]` (open ideals are open additive subgroups). Kept
-- file-`local` so it does not affect typeclass search in other modules.
attribute [local instance] IsLinearTopology.nonarchimedeanAddGroup

/-! ### Perfectoid rings -/

/-- A Tate ring `A` is a **perfectoid ring** (for a prime `p`) if:

1. `A` is complete and separated (T₀),
2. `A` is uniform (A° is bounded),
3. there exists a pseudo-uniformizer `ϖ` that is power-bounded, such that `ϖ^p | p`
   in `A°` (i.e., `p = c · ϖ^p` for some power-bounded `c`), and
4. the `p`-th power (Frobenius) map is surjective on `A°/p` (i.e., for every
   power-bounded `x`, there exist power-bounded `y, z` with `x = y^p + p · z`).

Condition (4) uses the Scholze formulation (Frobenius on `A°/(p)`), which is what
`surjective_fontaineTheta` requires. The Wedhorn formulation (Frobenius on `A°/(ϖ)`)
is a consequence; see `perfectoidPseudoUniformizer_frobenius_surj_varpi`.

(Scholze, *Perfectoid Spaces*, Definition 3.5) -/
class IsPerfectoidRing (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] : Prop
    extends IsTateRing A where
  /-- The uniform space is compatible with the additive group structure, and its
  topology agrees with `[TopologicalSpace A]`. -/
  uniformAddGroup : IsUniformAddGroup A
  /-- The uniform space topology agrees with the given topology. -/
  topologyEq : ‹UniformSpace A›.toTopologicalSpace = ‹TopologicalSpace A›
  /-- The ring is complete with respect to its uniform structure. -/
  complete : CompleteSpace A
  /-- The topology is T₀ (separated). -/
  t0 : T0Space A
  /-- The ring is uniform: `A°` is bounded. -/
  uniform : IsUniform A
  /-- There exists a pseudo-uniformizer `ϖ` that is power-bounded, with `ϖ^p | p` in `A°`. -/
  exists_pseudoUniformizer :
    ∃ (ϖ : PseudoUniformizer A),
      -- ϖ is power-bounded
      IsPowerBounded (ϖ.val : A) ∧
      -- ϖ^p divides p in A°: there exists power-bounded c with p = c · ϖ^p
      (∃ c : A, IsPowerBounded c ∧ (p : A) = c * ((ϖ.val : A) ^ p))
  /-- The Frobenius map is surjective on `A°/(p)`: for every power-bounded `x`, there
  exist power-bounded `y, z` with `x = y^p + p · z`.
  (Scholze, *Perfectoid Spaces*, Definition 3.5, condition (iv).) -/
  frobenius_surj : ∀ x : A, IsPowerBounded x →
    ∃ y : A, IsPowerBounded y ∧ ∃ z : A, IsPowerBounded z ∧ x = y ^ p + (p : A) * z

/-! ### Perfectoid fields -/

/-- A **perfectoid field** is a field that is also a perfectoid ring, whose topology
is induced by a rank-1 valuation with integer ring equal to the power-bounded subring.

The `exists_valuation` field records the existence of a `Valuation K ℝ≥0` whose
valuation ring is `K° = powerBoundedSubring.toSubring K`. This is guaranteed by
Wedhorn Proposition 6.1: every nonarchimedean field with non-discrete valuation
has a unique such valuation. Including it in the class avoids reconstructing it
from the topological data each time.

(Scholze, *Perfectoid Spaces*, Definition 3.5; Wedhorn, *Adic Spaces*, Prop 6.1) -/
class IsPerfectoidField (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [UniformSpace K] [IsLinearTopology K K] : Prop
    extends IsPerfectoidRing p K where
  /-- The topology on a perfectoid field is induced by a rank-1 valuation whose
  integer ring is the power-bounded subring `K°`. -/
  exists_valuation : ∃ (v : Valuation K NNReal), v.Integers ↥(powerBoundedSubring.toSubring K)

/-! ### Basic properties -/

namespace IsPerfectoidRing

/-- Extract a pseudo-uniformizer with the perfectoid property from a perfectoid ring. -/
noncomputable def perfectoidPseudoUniformizer (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] :
    PseudoUniformizer A :=
  (IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)).choose

/-- The perfectoid pseudo-uniformizer is power-bounded. -/
theorem perfectoidPseudoUniformizer_isPowerBounded (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] :
    IsPowerBounded ((perfectoidPseudoUniformizer p A).val : A) :=
  (IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)).choose_spec.1

/-- The perfectoid pseudo-uniformizer satisfies ϖ^p | p. -/
theorem perfectoidPseudoUniformizer_divides_p (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] :
    ∃ c : A, IsPowerBounded c ∧
      (p : A) = c * (((perfectoidPseudoUniformizer p A).val : A) ^ p) :=
  (IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)).choose_spec.2

/-- Frobenius is surjective on `A°/(ϖ)` (Wedhorn formulation).
This follows from the class field `frobenius_surj` (surjectivity on `A°/(p)`)
together with `p = c · ϖ^p`: if `x = y^p + p·z = y^p + c·ϖ^p·z = y^p + ϖ·(c·ϖ^{p-1}·z)`,
then `z' := c · ϖ^{p-1} · z` is power-bounded. -/
theorem perfectoidPseudoUniformizer_frobenius_surj_varpi (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] :
    ∀ x : A, IsPowerBounded x →
      ∃ y : A, IsPowerBounded y ∧
        ∃ z : A, IsPowerBounded z ∧
          x = y ^ p + ((perfectoidPseudoUniformizer p A).val : A) * z := by
  intro x hx
  obtain ⟨y, hy, z, hz, hxyz⟩ := IsPerfectoidRing.frobenius_surj (p := p) x hx
  obtain ⟨c, hc, hpc⟩ := perfectoidPseudoUniformizer_divides_p p A
  let ϖ := (perfectoidPseudoUniformizer p A).val
  have hϖ_pb := perfectoidPseudoUniformizer_isPowerBounded p A
  refine ⟨y, hy, c * (ϖ : A) ^ (p - 1) * z, ?_, ?_⟩
  · exact isPowerBounded_mul (isPowerBounded_mul hc
      ((powerBoundedSubring.toSubring A).pow_mem hϖ_pb (p - 1))) hz
  · rw [hxyz, hpc]
    simp only [ϖ]
    have hp_pos := (Fact.out : Nat.Prime p).pos
    set w := (perfectoidPseudoUniformizer p A).val.val
    have : w ^ p = w ^ (p - 1) * w := by
      have : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp_pos
      rw [← pow_succ]; congr 1; linarith
    rw [this]; ring

/-! ### p-adic completeness of A° -/

/-- **The power-bounded subring of a perfectoid ring is `p`-adically complete.**

Mathematically, this follows from three facts:
1. The `(p)`-adic filtration `p^n · A°` is cofinal with the `ϖ`-adic filtration
   (since `p = c · ϖ^p` with `c, ϖ ∈ A°`).
2. The `ϖ`-adic topology on `A°` agrees with the subspace topology from `A`.
3. `A°` is complete in the subspace topology (it is closed in the complete ring `A`).

The proof of `IsHausdorff` uses: if `x ∈ p^n A°` for all `n`, then
`x ∈ ϖ^{np} · A°` for all `n`, and since `ϖ` is top. nilpotent and `A°` is
bounded, `x` is in every neighborhood of `0`, hence `x = 0` by T₀.

The proof of `IsPrecomplete` uses: a `p`-adic Cauchy sequence is also Cauchy
in the subspace topology (by the cofinality above), hence converges in `A°`.

(Scholze, *Perfectoid Spaces*, implicit in §3) -/
private abbrev PBSubring (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] := ↥(powerBoundedSubring.toSubring A)

private abbrev pIdeal (p : ℕ) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] :=
  Ideal.span {(p : PBSubring A)}

/-- **IsHausdorff**: `⋂_n p^n A° = {0}`.

If `x ∈ p^n A°` for all `n`, then `(x : A) = (c·ϖ^p)^n · yₙ` for power-bounded
`yₙ`. Since `ϖ` is topologically nilpotent and `A°` is bounded, `(x : A)` is in
every neighborhood of 0, hence `(x : A) = 0` by T₀. -/
private theorem isHausdorff_pIdeal (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] [Nontrivial A] :
    IsHausdorff (pIdeal p A) (PBSubring A) := by
  constructor
  intro x hx
  -- Extract perfectoid data: ϖ (top. nilp. unit), c (power-bounded), p = c * ϖ^p
  obtain ⟨ϖ, _, ⟨c, hc_pb, hpc⟩⟩ :=
    IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)
  -- x ∈ (Ideal.span {p})^n • ⊤ for all n, i.e., p^n | x in A°
  have hx_mem : ∀ n : ℕ, (x : A) ∈ (Set.range (fun y : PBSubring A ↦ (p : A) ^ n * (y : A))) := by
    intro n
    have := (SModEq.sub_mem.mp (hx n))
    simp only [sub_zero] at this
    -- x ∈ (Ideal.span {p})^n • ⊤ in A°, i.e. p^n ∣ x in A°
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at this
    obtain ⟨y, hy⟩ := this
    exact ⟨y, by push_cast [hy]; ring⟩
  -- Show (x : A) is in every neighborhood of 0
  -- Using: (x : A) = (c * ϖ^p)^n * y_n, A° is bounded, ϖ top. nilp.
  have hx_zero : (x : A) = 0 := by
    -- Show 0 ∈ closure {(x : A)}, hence x = 0 by T₁ (from T₀ + UniformSpace)
    haveI := IsPerfectoidRing.t0 (p := p) (A := A)
    haveI := IsPerfectoidRing.uniform (p := p) (A := A)
    suffices h_mem_nhds : ∀ U ∈ nhds (0 : A), (x : A) ∈ U by
      have h0 : (0 : A) ∈ closure ({(x : A)} : Set A) :=
        mem_closure_iff_nhds.mpr fun U hU ↦ ⟨(x : A), h_mem_nhds U hU, Set.mem_singleton _⟩
      rwa [IsClosed.closure_eq isClosed_singleton, Set.mem_singleton_iff, eq_comm] at h0
    intro U hU
    -- A° is bounded: ∃ V ∈ nhds 0, A° * V ⊆ U
    obtain ⟨V, hV, hAV⟩ :=
      IsUniform.isBounded_powerBounded (A := A) U hU
    -- ϖ^p is topologically nilpotent (since ϖ is, and (ϖ^p)^n = ϖ^{pn} → 0)
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    have hϖp_tn : IsTopologicallyNilpotent ((ϖ.val : A) ^ p) := by
      rw [IsTopologicallyNilpotent]; simp_rw [← pow_mul]
      exact (ϖ.property).comp
        (Filter.tendsto_atTop_atTop_of_monotone (fun _ _ h ↦ Nat.mul_le_mul_left p h)
          fun b ↦ ⟨b, Nat.le_mul_of_pos_left _ hp_pos⟩)
    -- c^n is power-bounded for all n (A° is a subring, c ∈ A°)
    have hcn_pb : ∀ m : ℕ, IsPowerBounded (c ^ m) := by
      intro m; induction m with
      | zero => simpa using isPowerBounded_one
      | succ k ih => simpa [pow_succ] using isPowerBounded_mul ih hc_pb
    -- Pick n with (ϖ^p)^n ∈ V
    obtain ⟨n, hn⟩ := hϖp_tn.exists_pow_mem_of_mem_nhds hV
    -- (x : A) = (p : A)^n * y for some y ∈ A°
    obtain ⟨y, hy⟩ := hx_mem n
    -- c^n * y ∈ A° (product of power-bounded elements)
    have hcy_pb : IsPowerBounded (c ^ n * (y : A)) := isPowerBounded_mul (hcn_pb n) y.property
    -- Rewrite: (x : A) = (c * ϖ^p)^n * y = (c^n * y) * (ϖ^p)^n
    have hx_eq : (x : A) = c ^ n * (y : A) * ((ϖ.val : A) ^ p) ^ n := by
      rw [← hy, hpc]; ring
    -- (c^n * y) * (ϖ^p)^n ∈ A° * V ⊆ U
    rw [hx_eq]; exact hAV (Set.mul_mem_mul hcy_pb hn)
  -- Conclude x = 0 in A°
  exact Subtype.val_injective hx_zero

/-- In a uniform ring with linear topology, the limit of a sequence of power-bounded
elements (in the topology of A) is power-bounded, provided A° is bounded. -/
private theorem isPowerBounded_of_tendsto_of_powerBounded
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [IsUniform A] {f : ℕ → A} {L : A}
    (hf : ∀ n, IsPowerBounded (f n)) (hL : Filter.Tendsto f Filter.atTop (nhds L)) :
    IsPowerBounded L := by
  intro U hU
  -- Pick open ideal J ⊆ U
  obtain ⟨J, hJopen, hJU⟩ :=
    (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hU
  -- Pick V ∈ nhds 0 with A° * V ⊆ J (using A° bounded)
  obtain ⟨V, hV, hAV⟩ :=
    IsUniform.isBounded_powerBounded (A := A) (J : Set A) (hJopen.mem_nhds J.zero_mem)
  -- Pick open ideal J' ⊆ V ∩ J
  obtain ⟨J', hJ'open, hJ'VJ⟩ :=
    (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp
      (Filter.inter_mem hV (hJopen.mem_nhds J.zero_mem))
  have hJ'V : (J' : Set A) ⊆ V := fun x hx ↦ (hJ'VJ hx).1
  have hJ'J : (J' : Set A) ⊆ (J : Set A) := fun x hx ↦ (hJ'VJ hx).2
  -- Pick N such that f N - L ∈ J'
  have hJ'nhds : {x | x - L ∈ (J' : Set A)} ∈ nhds L :=
    (continuous_sub_right L).continuousAt.preimage_mem_nhds
      (by simpa using hJ'open.mem_nhds J'.zero_mem)
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp (hL hJ'nhds)
  have hLfN : L - f N ∈ (J' : Set A) := by
    have h := hN N le_rfl
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at h
    rw [show L - f N = -(f N - L) from by ring]; exact J'.neg_mem h
  -- For all k: L^k - (f N)^k ∈ J' (J' is an ideal, L - f N ∈ J')
  have hLk : ∀ k : ℕ, L ^ k - (f N) ^ k ∈ (J' : Set A) := by
    intro k; induction k with
    | zero => simp [J'.zero_mem]
    | succ k ih =>
      have : L ^ (k + 1) - (f N) ^ (k + 1) =
          L ^ k * (L - f N) + (L ^ k - (f N) ^ k) * f N := by ring
      rw [this]; exact J'.add_mem (J'.mul_mem_left _ hLfN) (J'.mul_mem_right _ ih)
  -- Witness: V' = J' works for {L^k | k} * J' ⊆ J ⊆ U
  refine ⟨(J' : Set A), hJ'open.mem_nhds J'.zero_mem, ?_⟩
  rintro _ ⟨_, ⟨k, rfl⟩, v, hv, rfl⟩
  apply hJU
  change L ^ k * v ∈ (J : Set A)
  have hsplit : L ^ k * v = (f N) ^ k * v + (L ^ k - (f N) ^ k) * v := by ring
  rw [hsplit]; apply J.add_mem
  · -- (f N)^k * v ∈ A° * V ⊆ J
    have hfNk : IsPowerBounded ((f N) ^ k) := by
      apply (hf N).subset; rintro _ ⟨m, rfl⟩
      exact ⟨k * m, show f N ^ (k * m) = (f N ^ k) ^ m from pow_mul _ _ _⟩
    exact hAV (Set.mul_mem_mul hfNk (hJ'V hv))
  · -- (L^k - (f N)^k) * v ∈ J' ⊆ J
    exact hJ'J (J'.mul_mem_right _ (hLk k))

/-- `(p : A) ^ m` is power-bounded, using the perfectoid factorization `p = c · ϖ^p`
with `c` and `ϖ` power-bounded. -/
private theorem isPowerBounded_p_pow {p : ℕ}
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] {ϖ c : A} (hϖ_pb : IsPowerBounded ϖ) (hc_pb : IsPowerBounded c)
    (hpc : (p : A) = c * ϖ ^ p) (m : ℕ) : IsPowerBounded ((p : A) ^ m) := by
  rw [hpc, mul_pow]
  exact isPowerBounded_mul ((powerBoundedSubring.toSubring A).pow_mem hc_pb m)
    ((powerBoundedSubring.toSubring A).pow_mem
      ((powerBoundedSubring.toSubring A).pow_mem hϖ_pb p) m)

/-- **Smallness of `p`-power multiples.** In a uniform ring with linear topology, if `ϖ`
is a topologically nilpotent power-bounded element with `p = c · ϖ^p` (`c` power-bounded),
then for every neighborhood `W` of `0` there is a threshold `M` past which `(p : A) ^ j` times
*any* power-bounded element lands in `W`. This is the common engine behind the Cauchy estimates
for both the original sequence and its telescoping partial sums. -/
private theorem mul_p_pow_eventually_mem_nhds {p : ℕ} (hp_pos : 0 < p)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsUniform A] {ϖ c : A}
    (hϖ_tn : IsTopologicallyNilpotent ϖ) (hc_pb : IsPowerBounded c)
    (hpc : (p : A) = c * ϖ ^ p) {W : Set A} (hW : W ∈ nhds (0 : A)) :
    ∃ M, ∀ a : A, IsPowerBounded a → ∀ j, M ≤ j → (p : A) ^ j * a ∈ W := by
  obtain ⟨V, hV, hAV⟩ := IsUniform.isBounded_powerBounded (A := A) W hW
  obtain ⟨J, hJopen, hJV⟩ :=
    (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hV
  obtain ⟨M, hM⟩ :=
    (isTopologicallyNilpotent_pow hϖ_tn hp_pos).exists_pow_mem_of_mem_nhds
      (hJopen.mem_nhds J.zero_mem)
  refine ⟨M, fun a ha j hj ↦ ?_⟩
  have hϖpj : (ϖ ^ p) ^ j ∈ V := by
    apply hJV
    rw [show (ϖ ^ p) ^ j = (ϖ ^ p) ^ (j - M) * (ϖ ^ p) ^ M by
      rw [← pow_add, Nat.sub_add_cancel hj]]
    exact J.mul_mem_left _ hM
  have hcj_pb : IsPowerBounded (c ^ j * a) :=
    isPowerBounded_mul ((powerBoundedSubring.toSubring A).pow_mem hc_pb j) ha
  rw [show (p : A) ^ j * a = c ^ j * a * (ϖ ^ p) ^ j by rw [hpc]; ring]
  exact hAV (Set.mul_mem_mul hcj_pb hϖpj)

/-- **Cauchy from eventually-small symmetric differences.** A sequence `g` whose differences
`g m - g n` lie in any neighborhood of `0` once both indices pass a threshold (uniformly) is
Cauchy in the uniform-space structure on `A`. The smallness is phrased in the given ring
topology and transported across `htop`. -/
private theorem cauchySeq_of_sub_eventually_mem_nhds
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsUniformAddGroup A] {g : ℕ → A}
    (htop : ‹UniformSpace A›.toTopologicalSpace = ‹TopologicalSpace A›)
    (hsym : ∀ W ∈ nhds (0 : A), ∃ N, ∀ m n, N ≤ m → N ≤ n → g m - g n ∈ W) :
    CauchySeq g := by
  rw [CauchySeq, IsUniformAddGroup.cauchy_map_iff_tendsto_swapped]
  refine ⟨Filter.atTop_neBot, ?_⟩
  rw [Filter.Tendsto, Filter.map_le_iff_le_comap]
  intro U hU
  obtain ⟨W, hW, hWU⟩ := Filter.mem_comap.mp hU
  rw [htop] at hW
  obtain ⟨N, hN⟩ := hsym W hW
  rw [Filter.prod_atTop_atTop_eq, Filter.mem_atTop_sets]
  exact ⟨(N, N), fun ⟨m, n⟩ ⟨hm, hn⟩ ↦ hWU (hN n m hn hm)⟩

/-- **Cauchyness of partial sums with eventually-small terms.** Let `S n N = ∑_{j < N} t n j`
be the partial sums of a doubly-indexed family `t`. If every term `t n j` lies in any
neighborhood of `0` once `j` is large enough (uniformly in `n`), then for each `n` the
sequence `N ↦ S n N` is Cauchy. A difference of partial sums is a sum over an `Finset.Ico`
interval whose indices all exceed the smallness threshold, hence lands in an open ideal
`⊆ W` (open ideals being closed under finite sums and negation); the result then follows from
`cauchySeq_of_sub_eventually_mem_nhds`. -/
private theorem cauchySeq_partialSum_of_term_eventually_mem_nhds
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsUniformAddGroup A]
    {S : ℕ → ℕ → A} {t : ℕ → ℕ → A}
    (hS : ∀ n N, S n N = ∑ j ∈ Finset.range N, t n j)
    (htop : ‹UniformSpace A›.toTopologicalSpace = ‹TopologicalSpace A›)
    (hsmall : ∀ W ∈ nhds (0 : A), ∃ M, ∀ n j, M ≤ j → t n j ∈ W) (n : ℕ) :
    CauchySeq (S n) := by
  refine cauchySeq_of_sub_eventually_mem_nhds A htop (fun W hW ↦ ?_)
  -- Pick an open ideal K ⊆ W (K is closed under finite sums and negation).
  obtain ⟨K, hKopen, hKW⟩ :=
    (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hW
  obtain ⟨M, hM⟩ := hsmall (K : Set A) (hKopen.mem_nhds K.zero_mem)
  -- Every `Finset.Ico` sum above the threshold lands in `K ⊆ W`.
  have hsub : ∀ a b, M ≤ a → a ≤ b → ∑ j ∈ Finset.Ico a b, t n j ∈ (K : Set A) :=
    fun a b ha _ ↦ Submodule.sum_mem _ fun j hj ↦ hM n j (le_trans ha (Finset.mem_Ico.mp hj).1)
  refine ⟨M, fun N₂ N₁ hN₂ hN₁ ↦ ?_⟩
  rcases le_total N₂ N₁ with h | h
  · -- S n N₂ - S n N₁ = -(Σ Ico N₂ N₁)
    have heq := Finset.sum_range_add_sum_Ico (fun j ↦ t n j) h
    have hS_diff : S n N₁ - S n N₂ = ∑ j ∈ Finset.Ico N₂ N₁, t n j := by
      simp only [hS]; rw [← heq]; ring
    rw [show S n N₂ - S n N₁ = -(S n N₁ - S n N₂) from by ring, hS_diff]
    exact hKW (K.neg_mem (hsub N₂ N₁ hN₂ h))
  · -- S n N₂ - S n N₁ = Σ Ico N₁ N₂
    have heq := Finset.sum_range_add_sum_Ico (fun j ↦ t n j) h
    have hS_diff : S n N₂ - S n N₁ = ∑ j ∈ Finset.Ico N₁ N₂, t n j := by
      simp only [hS]; rw [← heq]; ring
    rw [hS_diff]; exact hKW (hsub N₁ N₂ hN₁ h)

/-- **Telescoping identity.** If consecutive differences of `a` factor as
`a k - a (k+1) = (p : A)^k · b k`, then `(p : A)^n` times the partial sum
`∑_{j < N} (p : A)^j · b (n+j)` collapses to `a n - a (n+N)`. -/
private theorem p_pow_mul_partialSum_eq_sub {p : ℕ}
    {A : Type u} [CommRing A] {a b : ℕ → A}
    (hab : ∀ k, a k - a (k + 1) = (p : A) ^ k * b k) (n N : ℕ) :
    (p : A) ^ n * ∑ j ∈ Finset.range N, (p : A) ^ j * b (n + j) = a n - a (n + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h2 : (p : A) ^ n * ((p : A) ^ N * b (n + N)) = (p : A) ^ (n + N) * b (n + N) := by
      rw [pow_add]; ring
    rw [h2, ← hab (n + N), show n + (N + 1) = n + N + 1 from by omega]; ring

/-- **Passing the telescoping identity to the limit.** Fix `c, x : A`. If the partial sums
`s N` converge to `ls`, the tails `r N` converge to `lr`, and `c · s N = x - r N` for all `N`,
then `c · ls = x - lr`. This is limit-uniqueness for `N ↦ c · s N`, continuous in `s`. -/
private theorem mul_lim_eq_sub_of_telescope
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    {s r : ℕ → A} {ls lr c x : A} (hs : Filter.Tendsto s Filter.atTop (nhds ls))
    (hr : Filter.Tendsto r Filter.atTop (nhds lr)) (htel : ∀ N, c * s N = x - r N) :
    c * ls = x - lr := by
  have hlhs : Filter.Tendsto (fun N ↦ c * s N) Filter.atTop (nhds (c * ls)) :=
    (continuous_const.mul continuous_id).continuousAt.tendsto.comp hs
  have hrhs : Filter.Tendsto (fun N ↦ x - r N) Filter.atTop (nhds (x - lr)) := hr.const_sub x
  rw [show (fun N ↦ c * s N) = fun N ↦ x - r N from funext htel] at hlhs
  exact tendsto_nhds_unique hlhs hrhs

/-- **IsPrecomplete**: `p`-adic Cauchy sequences in `A°` converge.

The proof proceeds in four steps:
1. Extract the divisibility content of the Cauchy condition.
2. Show the coerced sequence `(f n : A)` is Cauchy in the uniform space on `A`.
3. Obtain a limit `L : A` from `CompleteSpace A`, show `L ∈ A°` using the helper lemma.
4. Verify the `SModEq` condition: `p^n | (f n - L)` in `A°`. -/
private theorem isPrecomplete_pIdeal (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] [Nontrivial A] :
    IsPrecomplete (pIdeal p A) (PBSubring A) := by
  haveI := IsPerfectoidRing.complete (p := p) (A := A)
  haveI := IsPerfectoidRing.t0 (p := p) (A := A)
  haveI := IsPerfectoidRing.uniform (p := p) (A := A)
  -- Extract perfectoid data
  obtain ⟨ϖ, hϖ_pb, ⟨c, hc_pb, hpc⟩⟩ :=
    IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  constructor
  intro f hf
  -- Step 1: Extract divisibility from the Cauchy condition
  have hf_div : ∀ m n, m ≤ n → ∃ y : PBSubring A, f m - f n = (p : PBSubring A) ^ m * y := by
    intro m n hmn
    have := SModEq.sub_mem.mp (hf hmn)
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at this
    exact this
  -- Step 1b: Divisibility in A
  have hf_divA : ∀ m n, m ≤ n →
      (f m : A) - (f n : A) ∈ Set.range (fun y : PBSubring A ↦ (p : A) ^ m * (y : A)) := by
    intro m n hmn
    obtain ⟨y, hy⟩ := hf_div m n hmn
    exact ⟨y, by have := congr_arg (Subtype.val) hy; push_cast at this ⊢; exact this.symm⟩
  -- Step 2: Show (f n : A) is Cauchy in A.
  -- Since `(f m : A) - (f n : A) = p^m * y` for power-bounded `y` (Step 1b), the smallness
  -- engine `mul_p_pow_eventually_mem_nhds` puts the difference in any nhds of 0 for large `m`.
  have hf_small : ∀ W ∈ nhds (0 : A), ∃ N, ∀ m n, N ≤ m → m ≤ n →
      (f m : A) - (f n : A) ∈ W := by
    intro W hW
    obtain ⟨N, hN⟩ :=
      mul_p_pow_eventually_mem_nhds hp_pos A ϖ.isTopologicallyNilpotent hc_pb hpc hW
    refine ⟨N, fun m n hNm hmn ↦ ?_⟩
    obtain ⟨y, hy⟩ := hf_divA m n hmn
    rw [← hy]; exact hN (y : A) y.property m hNm
  -- Step 3: Show CauchySeq and get limit.
  haveI : IsUniformAddGroup A := IsPerfectoidRing.uniformAddGroup (p := p) (A := A)
  have htop := IsPerfectoidRing.topologyEq (p := p) (A := A)
  -- Symmetrize `hf_small`: an open ideal is closed under negation, so the one-sided estimate
  -- extends to all `m, n ≥ N`.
  have hf_sym : ∀ W ∈ nhds (0 : A), ∃ N, ∀ m n, N ≤ m → N ≤ n →
      (f m : A) - (f n : A) ∈ W := by
    intro W hW
    obtain ⟨J, hJopen, hJW⟩ :=
      (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hW
    obtain ⟨N, hN⟩ := hf_small (J : Set A) (hJopen.mem_nhds J.zero_mem)
    exact ⟨N, fun m n hm hn ↦ by
      rcases le_total m n with hmn | hmn
      · exact hJW (hN m n hm hmn)
      · rw [show (f m : A) - (f n : A) = -((f n : A) - (f m : A)) from by ring]
        exact hJW (J.neg_mem (hN n m hn hmn))⟩
  -- The coerced sequence is Cauchy in A.
  have hCauchy : CauchySeq (fun n ↦ (f n : A)) :=
    cauchySeq_of_sub_eventually_mem_nhds A htop hf_sym
  -- Get limit from CompleteSpace
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hCauchy
  -- Convert hL to use the given topology
  have hL' : Filter.Tendsto (fun n ↦ (f n : A)) Filter.atTop
      (@nhds A ‹TopologicalSpace A› L) := by rwa [htop] at hL
  -- Step 4: L is power-bounded
  have hL_pb : IsPowerBounded L :=
    isPowerBounded_of_tendsto_of_powerBounded (fun n ↦ (f n).property) hL'
  -- Step 5: Verify SModEq condition via telescoping series.
  -- Extract differences d_k ∈ A° with f(k) - f(k+1) = p^k * d_k.
  have hd_ex : ∀ k, ∃ d : PBSubring A, f k - f (k + 1) = (p : PBSubring A) ^ k * d :=
    fun k ↦ hf_div k (k + 1) (Nat.le_succ k)
  choose d hd using hd_ex
  -- Define partial sums in A: S(n, N) = Σ_{j<N} p^j * d(n+j)
  let S : ℕ → ℕ → A := fun n N ↦
    ∑ j ∈ Finset.range N, (p : A) ^ j * (d (n + j) : A)
  -- Telescoping identity p^n * S(n, N) = (f n : A) - (f(n+N) : A), from the coerced differences.
  have hd_val : ∀ k, (f k : A) - (f (k + 1) : A) = (p : A) ^ k * (d k : A) := by
    intro k; exact_mod_cast congr_arg (Subtype.val) (hd k)
  have htelescope : ∀ n N, (p : A) ^ n * S n N = (f n : A) - (f (n + N) : A) :=
    fun n N ↦ p_pow_mul_partialSum_eq_sub hd_val n N
  -- Each partial sum S(n, N) is power-bounded.
  have hS_pb : ∀ n N, IsPowerBounded (S n N) := by
    intro n N; induction N with
    | zero => simp only [S, Finset.sum_range_zero]; exact isPowerBounded_zero
    | succ N ih =>
      simp only [S, Finset.sum_range_succ]
      exact isPowerBounded_add ih
        (isPowerBounded_mul (isPowerBounded_p_pow A hϖ_pb hc_pb hpc N) (d (n + N)).property)
  -- Each term `p^j * d(n+j)` is in any neighborhood of 0 for large `j` (smallness engine).
  have hterm_small : ∀ W ∈ nhds (0 : A), ∃ M, ∀ n j, M ≤ j →
      (p : A) ^ j * (d (n + j) : A) ∈ W := by
    intro W hW
    obtain ⟨M, hM⟩ :=
      mul_p_pow_eventually_mem_nhds hp_pos A ϖ.isTopologicallyNilpotent hc_pb hpc hW
    exact ⟨M, fun n j hj ↦ hM (d (n + j) : A) (d (n + j)).property j hj⟩
  -- The partial sums S(n, ·) form a Cauchy sequence.
  have hS_cauchy_unif : ∀ n, CauchySeq (S n) := by
    haveI : IsUniformAddGroup A := IsPerfectoidRing.uniformAddGroup (p := p) (A := A)
    exact fun n ↦ cauchySeq_partialSum_of_term_eventually_mem_nhds A
      (S := S) (t := fun n j ↦ (p : A) ^ j * (d (n + j) : A))
      (hS := fun _ _ ↦ rfl) (htop := htop) (hsmall := hterm_small) n
  -- Get limits of S(n, ·) from CompleteSpace
  have hS_lim : ∀ n, ∃ sn : A, Filter.Tendsto (S n) Filter.atTop
      (@nhds A ‹UniformSpace A›.toTopologicalSpace sn) := by
    intro n; exact cauchySeq_tendsto_of_complete (hS_cauchy_unif n)
  choose sn hsn using hS_lim
  -- Convert limits to given topology
  have hsn' : ∀ n, Filter.Tendsto (S n) Filter.atTop (@nhds A ‹TopologicalSpace A› (sn n)) := by
    intro n; rw [htop] at hsn; exact hsn n
  -- Each sn is power-bounded (limit of PB sequence)
  have hsn_pb : ∀ n, IsPowerBounded (sn n) := by
    intro n; exact isPowerBounded_of_tendsto_of_powerBounded (fun N ↦ hS_pb n N) (hsn' n)
  -- p^n * sn(n) = (f n : A) - L, by passing the telescoping identity to the limit.
  have hpn_sn : ∀ n, (p : A) ^ n * sn n = (f n : A) - L := fun n ↦
    mul_lim_eq_sub_of_telescope (hsn' n)
      (hL'.comp (Filter.tendsto_atTop_atTop_of_monotone
        (fun _ _ h ↦ Nat.add_le_add_left h n) fun b ↦ ⟨b, Nat.le_add_left b n⟩))
      (htelescope n)
  -- Construct the limit in A° and verify SModEq
  refine ⟨⟨L, hL_pb⟩, fun n ↦ ?_⟩
  rw [SModEq.sub_mem]
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨⟨sn n, hsn_pb n⟩, Subtype.val_injective ?_⟩
  push_cast; exact (hpn_sn n).symm

instance instIsAdicComplete (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] [Nontrivial A] :
    IsAdicComplete (pIdeal p A) (PBSubring A) :=
  { toIsHausdorff := isHausdorff_pIdeal p A
    toIsPrecomplete := isPrecomplete_pIdeal p A }

/-! ### Sorry'd deep theorems -/

/-- **Perfectoid rings are stably uniform** (Scholze, *Perfectoid Spaces*, Theorem 5.2).

This is a deep result: the key step is to show that for any rational localization
`R(T/s)` of a perfectoid ring, the completed localization is again uniform. The
proof goes through almost mathematics and tilting. -/
theorem toIsStablyUniform (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]
    [PlusSubring A] [IsHuberRing A] :
    IsStablyUniform A := sorry

/-- **Perfectoid rings are sheafy** (Scholze, *Perfectoid Spaces*, Theorem 6.3).

This follows from stable uniformity: Buzzard--Verberkmoes showed that stably
uniform Tate rings are sheafy. -/
theorem toIsSheafy (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]
    [PlusSubring A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] :
    IsSheafy A := sorry

end IsPerfectoidRing
