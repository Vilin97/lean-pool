/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul

/-! # Basic -/

@[expose] public section



universe u

open Multiset Finset

/-!
## Chip-firing graphs

A *chip-firing graph* (`CFGraph`) is a loopless undirected multigraph with bundled vertex type
$V(G)$, implemented as `G.V` and assumed to be finite, decidably equal, and nonempty.
Edges are stored as a multiset of ordered pairs; `numEdges G v w` counts the total edge
multiplicity between $v$ and $w$, including both $(v,w)$ and $(w,v)$ entries.

We define the *degree* (valence) of a vertex as the sum of edge multiplicities at that vertex,
and the *genus* (cyclomatic number) $g = |E| - |V(G)| + 1$, which plays a central role in the
Riemann-Roch theorem for graphs.

Many main theorems in this library require connectivity; see `graphConnected`. In those cases, a
proof of connectivity must be provided as an additional argument.
-/

/-- A *chip-firing graph* is a loopless multigraph.
It is not assumed connected by default, though many of our main theorems pertain to
connected graphs. -/
structure CFGraph  where
  /-- The finite nonempty type of graph vertices. -/
  V : Type u
  [instDecidableEq : DecidableEq V]
  [instFintype : Fintype V]
  [instNonempty : Nonempty V]
  /-- The multiset of endpoint pairs encoding edges, including their multiplicities. -/
  (edges : Multiset (V × V))
  (loopless : ∀ v, (v, v) ∉ edges)

attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty

/-- The edge multiplicity between vertices $v$ and $w$.

When working with chip-firing graphs in this repository, prefer this function to the
underlying multiset of edges. -/
def numEdges (G : CFGraph) (v w : G.V) : ℕ :=
  Multiset.card (G.edges.filter (λ e => e = (v, w) ∨ e = (w, v)))

/-- A graph is *connected* if its vertices cannot be partitioned into two nonempty sets
with no edges between them.

This is equivalent to saying that there is a path between any two vertices, but the
partition formulation is more convenient in this repository. -/
def graphConnected (G : CFGraph) : Prop :=
  ∀ S : Finset G.V, (∃ (v w : G.V), v ∈ S ∧ w ∉ S) →
    (∃ v ∈ S, ∃ w ∉ S, numEdges G v w > 0)

/-- The genus of a graph is its cyclomatic number, $|E| - |V| + 1$. -/
def genus (G : CFGraph) : ℤ :=
  Multiset.card G.edges - Fintype.card G.V + 1

/-- The number of edges between two vertices is symmetric (the graph is undirected). -/
lemma num_edges_symmetric (G : CFGraph) (v w : G.V) :
  numEdges G v w = numEdges G w v := by
  simp only [numEdges, Or.comm]

/-- Numerical version of *loopless*: the number of edges from a vertex to itself is zero. -/
@[simp] lemma num_edges_self_zero (G : CFGraph) (v : G.V) :
  numEdges G v v = 0 := by
  rw [numEdges, Multiset.card_eq_zero]
  refine Multiset.filter_eq_nil.mpr ?_
  intro e h_inE h_eq
  rw [or_self] at h_eq
  rcases e with ⟨a, b⟩
  cases h_eq
  exact G.loopless v h_inE

/-- The degree, or valence, of a vertex as an integer. -/
def vertexDegree (G : CFGraph) (v : G.V) : ℤ :=
  ∑ u : G.V, (numEdges G v u : ℤ)

/-!
## The divisor group

A *divisor* (`CFDiv G`) is an integer-valued function on the vertices of a chip-firing graph,
representing a distribution of chips (possibly negative, i.e. debt) across vertices.
The divisor group $\operatorname{Div}(G)$ is implemented as `CFDiv G`, the abelian group
of functions $V(G) \to \mathbb{Z}$ under pointwise addition.

This section establishes basic operations on divisors: pointwise arithmetic lemmas, the
*firing move* at a single vertex (lending chips to all neighbors), the *borrowing move*
(the inverse operation), and the generalization to *set firing*. The firing vector
`firingVector G v` is the principal divisor produced by firing vertex $v$ once.

See:
- [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 1.3.
- [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definitions 1.5-1.6.
-/

/-- A *divisor* is a function from vertices to integers.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 1.3. -/
abbrev CFDiv (G : CFGraph) := G.V → ℤ

/-- The divisor with one chip at a specified vertex $v_{\mathrm{chip}}$ and zero chips elsewhere. -/
def oneChip {G : CFGraph} (v_chip : G.V) : CFDiv G :=
  fun v => if v = v_chip then 1 else 0

-- Canonical simplifications for evaluations of oneChip.
@[simp] lemma one_chip_apply_v {G : CFGraph} (v : G.V) : oneChip v v = 1 := by
  exact ite_eq_left rfl
@[simp] lemma one_chip_apply_other {G : CFGraph} (v w : G.V) : v ≠ w → oneChip v w = 0 := by
  simp only [ne_eq, oneChip, ite_eq_right_iff, one_ne_zero, imp_false]
  intro h
  contrapose! h
  rw [h]
@[simp] lemma one_chip_apply_other' {G : CFGraph} (v w : G.V) : w ≠ v → oneChip v w = 0 := by
  simp only [ne_eq, oneChip, ite_eq_right_iff, one_ne_zero, imp_false, imp_self]


-- Properties of divisor arithmetic (add_apply, sub_apply, zero_apply, neg_apply, smul_apply
-- are provided by Mathlib for Pi types)

/-- The result of firing a vertex $v$, starting from the divisor $D$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 1.5. -/
def firingMove (G : CFGraph) (D : CFDiv G) (v : G.V) : CFDiv G :=
  λ w => if w = v then D v - vertexDegree G v else D w + numEdges G v w

/-- The result of borrowing at a vertex $v$, starting from a divisor $D$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 1.5. -/
def borrowingMove (G : CFGraph) (D : CFDiv G) (v : G.V) : CFDiv G :=
  λ w => if w = v then D v + vertexDegree G v else D w - numEdges G v w

/-- The out-degree of `v` relative to `S`, counted with edge multiplicity. -/
def outdegreeSet (G : CFGraph) (S : Finset G.V) (v : G.V) : ℤ :=
  ∑ w ∈ (univ \ S), (numEdges G v w : ℤ)

@[simp] theorem outdeg_S_eq_sum_filter (G : CFGraph) (S : Finset G.V) (v : G.V) :
    outdegreeSet G S v = ∑ w ∈ Finset.univ.filter (fun x => x ∉ S),
      (numEdges G v w : ℤ) := by
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext w
  simp

theorem outdeg_S_nonneg (G : CFGraph) (S : Finset G.V) (v : G.V) :
    0 ≤ outdegreeSet G S v := by
  unfold outdegreeSet
  exact Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _

theorem outdeg_S_antitone (G : CFGraph) {S T : Finset G.V} (h : S ⊆ T) (v : G.V) :
    outdegreeSet G T v ≤ outdegreeSet G S v := by
  unfold outdegreeSet
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.compl_subset_compl.mpr h)
    (fun _ _ _ => Int.natCast_nonneg _)

/-- The result of firing a set $S$ of vertices, starting from a divisor $D$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 1.6. -/
def setFiring (G : CFGraph) (D : CFDiv G) (S : Finset G.V) : CFDiv G :=
  λ w => if w ∈ S then D w - outdegreeSet G S w else D w + outdegreeSet G Sᶜ w

theorem set_firing_apply_of_mem (G : CFGraph) (D : CFDiv G) {S : Finset G.V}
    {v : G.V} (hv : v ∈ S) :
    setFiring G D S v = D v - outdegreeSet G S v := by
  simp [setFiring, hv]

theorem set_firing_apply_of_not_mem (G : CFGraph) (D : CFDiv G)
    {S : Finset G.V} {v : G.V} (hv : v ∉ S) :
    setFiring G D S v = D v + outdegreeSet G Sᶜ v := by
  simp [setFiring, hv]

theorem le_set_firing_apply_of_not_mem (G : CFGraph) (D : CFDiv G)
    {S : Finset G.V} {v : G.V} (hv : v ∉ S) :
    D v ≤ setFiring G D S v := by
  rw [set_firing_apply_of_not_mem G D hv]
  exact le_add_of_nonneg_right (outdeg_S_nonneg G Sᶜ v)

/-- The principal divisor associated to firing a single vertex. -/
def firingVector (G : CFGraph) (v : G.V) : CFDiv G :=
  λ w => if w = v then -vertexDegree G v else numEdges G v w

/-!
## Principal divisors and linear equivalence

A *firing script* (`firingScript G = G.V → ℤ`) assigns an integer firing level to each vertex.
The associated *principal divisor* `prin G σ` records the net chip flow at each vertex when
the script $\sigma$ is applied:
$$
(\operatorname{prin}_G \sigma)(v) =
\sum_u (\sigma(u)-\sigma(v)) \operatorname{num\_edges}_G(v,u).
$$

The subgroup of *principal divisors* `principalDivisors G` is generated by the firing vectors
`firingVector G v` for all $v$. Two divisors $D$ and $D'$ are *linearly equivalent*
(`linearEquiv G D D'`) if their difference is a principal divisor. This defines an
equivalence relation on $\operatorname{Div}(G)$, and linearly equivalent
divisors have the same degree (see `linear_equiv_preserves_deg`).
-/

/-- The subgroup of principal divisors is generated by firing vectors at individual vertices. -/
def principalDivisors (G : CFGraph) : AddSubgroup (CFDiv G) :=
  AddSubgroup.closure (Set.range (firingVector G))

/-- Two divisors are *linearly equivalent* if their difference is a principal divisor.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 1.8. -/
def linearEquiv (G : CFGraph) (D D' : CFDiv G) : Prop :=
  D' - D ∈ principalDivisors G

/-- Principal divisors contain the firing vector at a vertex. -/
private lemma mem_principal_divisors_firing_vector (G : CFGraph) (v : G.V) :
  firingVector G v ∈ principalDivisors G := AddSubgroup.subset_closure (Set.mem_range_self v)

/-- Linear equivalence is reflexive. -/
@[refl] lemma linearEquiv.refl (G : CFGraph) (D : CFDiv G) : linearEquiv G D D := by
  unfold linearEquiv
  simp only [sub_self, zero_mem]

/-- Linear equivalence is symmetric. -/
@[symm] lemma linearEquiv.symm {G : CFGraph} {D D' : CFDiv G} :
  linearEquiv G D D' → linearEquiv G D' D := by
  intro h
  unfold linearEquiv at *
  simpa only [sub_eq_add_neg, neg_add_rev, neg_neg]
      using AddSubgroup.neg_mem (principalDivisors G) h

/-- Linear equivalence is transitive. -/
@[trans] lemma linearEquiv.trans {G : CFGraph} {D₁ D₂ D₃ : CFDiv G} :
  linearEquiv G D₁ D₂ → linearEquiv G D₂ D₃ → linearEquiv G D₁ D₃ := by
  intro h1 h2
  unfold linearEquiv at *
  simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_neg_cancel_comm_assoc] using
    AddSubgroup.add_mem (principalDivisors G) h2 h1

/-- Linear equivalence is an equivalence relation on $\operatorname{Div}(G)$. -/
theorem linear_equiv_is_equivalence (G : CFGraph) : Equivalence (linearEquiv G) :=
  ⟨linearEquiv.refl G, linearEquiv.symm, linearEquiv.trans⟩

/-- A *firing script* is an integer-valued function on vertices, recording how many times
each vertex is fired. Negative values represent borrowing.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 2.2. -/
abbrev firingScript (G : CFGraph) := G.V → ℤ

/-- The firing script that fires exactly the vertices in `S`, once each. -/
def indicatorScript (G : CFGraph) (S : Finset G.V) : firingScript G :=
  fun v => if v ∈ S then 1 else 0

/-- The group homomorphism sending a firing script $\sigma$ to the principal divisor
$$
(\operatorname{prin}_G \sigma)(v) =
\sum_u (\sigma(u)-\sigma(v)) \operatorname{num\_edges}_G(v,u).
$$

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 2.3;
`prin G σ` is the *negative* of the divisor $\operatorname{div}(\sigma)$ defined there,
since they implement a firing script as $D \mapsto D - \operatorname{div}(\sigma)$. -/
def prin (G : CFGraph) : firingScript G →+ CFDiv G :=
  {
    toFun := fun σ v => ∑ u : G.V, (σ u - σ v) * (numEdges G v u),
    map_zero' := by
      funext v
      simp only [Pi.zero_apply, sub_self, zero_mul, sum_const_zero],
    map_add' := by
      intro σ₁ σ₂
      funext v
      dsimp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro u _
      ring,
  }

@[simp] theorem prin_apply (G : CFGraph) (σ : firingScript G) (v : G.V) :
    prin G σ v = ∑ u : G.V, (σ u - σ v) * (numEdges G v u : ℤ) := rfl

/-- Constant firing scripts have zero principal divisor. -/
@[simp] theorem prin_const (G : CFGraph) (c : ℤ) :
    prin G (fun _ : G.V => c) = 0 := by
  funext v
  rw [prin_apply]
  simp

@[simp] theorem prin_sub_const (G : CFGraph) (σ : firingScript G) (c : ℤ) :
    prin G (fun v => σ v - c) = prin G σ := by
  funext v
  rw [prin_apply, prin_apply]
  apply Finset.sum_congr rfl
  intro u hu
  ring

/-- Firing a set once is the same as adding the principal divisor of its indicator script. -/
theorem set_firing_eq_add_prin_indicator_script (G : CFGraph) (D : CFDiv G)
    (S : Finset G.V) :
    setFiring G D S = D + prin G (indicatorScript G S) := by
  classical
  funext v
  by_cases hv : v ∈ S
  · simp [setFiring, indicatorScript, prin_apply, outdegreeSet, hv]
    simp only [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib]
    have hs : S.sum (fun x => (numEdges G v x : ℤ)) =
        (univ : Finset G.V).sum (fun x =>
          (if x ∈ S then 1 else 0) * (numEdges G v x : ℤ)) := by simp
    rw [← hs]
    ring
  · simp [setFiring, indicatorScript, prin_apply, outdegreeSet, hv]

/-- A divisor is principal if and only if it equals `prin G σ` for some firing script `σ`.
This gives a concrete characterization of the subgroup `principalDivisors G`. -/
lemma principal_iff_eq_prin (G : CFGraph) (D : CFDiv G) :
  D ∈ principalDivisors G ↔ ∃ σ : firingScript G, D = prin G σ := by
  unfold principalDivisors
  constructor
  · -- Forward direction
    intro h_inp
    -- Use the defining property of a subgroup closure
    refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ h_inp
    . -- Case 1: h_inp is a firing vector
      intro x h_firing
      rcases h_firing with ⟨v, rfl⟩
      let σ : firingScript G := λ u => if u = v then 1 else 0
      use σ
      unfold firingVector prin
      funext w
      dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, σ]
      by_cases h_eq : w = v
      . -- Case w = v
        simp only [h_eq, ↓reduceIte]
        unfold vertexDegree
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro u _
        by_cases h_eq2 : u = v <;> simp only [h_eq2, num_edges_self_zero, CharP.cast_eq_zero,
            neg_zero, ↓reduceIte, sub_self, mul_zero, zero_sub, Int.reduceNeg, neg_mul, one_mul]
      . -- Case w ≠ v
        simp only [h_eq, ↓reduceIte, num_edges_symmetric G v w, sub_zero, ite_mul, one_mul,
            zero_mul, sum_ite_eq', mem_univ]
    . -- Case 2: h_inp is zero divisor
      use 0
      simp only [_root_.map_zero]
    . -- Case 3: h_inp is a sum of two principal divisors
      intros x y _ _ h_x_prin h_y_prin
      rcases h_x_prin with ⟨σ₁, h_x_eq⟩
      rcases h_y_prin with ⟨σ₂, h_y_eq⟩
      rw [h_x_eq, h_y_eq]
      use σ₁ + σ₂
      simp only [_root_.map_add]
    . -- Case 4: h_inp is negation of a principal divisor
      intro x _ h_x_prin
      rcases h_x_prin with ⟨σ, h_x_eq⟩
      use -σ
      rw [h_x_eq]
      simp only [map_neg]
  . -- Backward direction
    intro h_prin
    rcases h_prin with ⟨σ, h_eq⟩
    unfold prin at h_eq
    let D₁ := ∑ u : G.V, (σ u) • (firingVector G u)
    have D1_principal :D₁ ∈ principalDivisors G := by
      apply AddSubgroup.sum_mem _ _
      intro u _
      apply AddSubgroup.zsmul_mem _ _
      exact mem_principal_divisors_firing_vector G u
    have D_eq : D₁ = D := by
      rw [h_eq]
      funext v
      -- expand the definition of D₁
      dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, D₁]
      unfold firingVector
      -- Move that v into the sum on the left side
      simp only [Finset.sum_apply]
      simp only [Pi.smul_apply, Int.zsmul_eq_mul, mul_ite, mul_neg]
      have: ∀ (u : G.V), (σ u - σ v) * ↑(numEdges G v u) =
          σ u * ↑(numEdges G v u) - σ v * ↑(numEdges G v u) := by
        intro u; ring
      simp only [this]

      have h (x : G.V) : (if v = x then -(σ x * vertexDegree G x) else σ x * ↑(numEdges G x v) ) = σ
        x * (↑(numEdges G x v) ) - σ x * ( (if v = x then vertexDegree G x else 0))  := by
        by_cases h : v = x <;> simp only [h, ↓reduceIte, mul_zero, sub_zero, num_edges_self_zero,
            CharP.cast_eq_zero, zero_sub]

      simp only [h]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      suffices ∑ x : G.V, σ x * (if v = x then vertexDegree G x else 0) = ∑ x : G.V, (σ v *
        ↑(numEdges G v x)) by
        rw [this]
        simp only [num_edges_symmetric]

      dsimp only [vertexDegree]
      rw [← Finset.mul_sum]
      simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
    rw [← D_eq]
    exact D1_principal

/-!
## Effective divisors and winnability

A divisor is *effective* if it assigns a nonnegative number of chips to every vertex.
The divisor group carries a natural partial order, where $D_1 \le D_2$ if and only if
$D_1(v) \le D_2(v)$ for all vertices $v$. Effectivity is equivalent to $D \ge 0$.
The submonoid of effective divisors is denoted `Eff G`.

A divisor $D$ is *winnable* if it is linearly equivalent to some effective divisor.
Equivalently, the players can collectively win the dollar game starting from position $D$.
-/

/-- A divisor is *effective* if it assigns a nonnegative integer to every vertex.
Equivalently, it is at least $0$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 1.13. -/
def effective {G : CFGraph} (D : CFDiv G) : Prop :=
  ∀ v : G.V, D v ≥ 0


/-- The submonoid of effective divisors is denoted `Eff G`. -/
def Eff (G : CFGraph) : AddSubmonoid (CFDiv G) :=
  { carrier := {D : CFDiv G | effective D},
    zero_mem' := by
      simp only [effective, ge_iff_le, Set.mem_ofPred_eq, Pi.zero_apply, Std.le_refl, implies_true]
    add_mem' := by
      intro D₁ D₂ h_eff1 h_eff2 v
      exact add_nonneg (h_eff1 v) (h_eff2 v) }

@[simp] lemma mem_Eff {G : CFGraph} {D : CFDiv G} : D ∈ Eff G ↔ effective D := Iff.rfl

/-- A one-chip divisor is effective. -/
lemma eff_one_chip {G : CFGraph} (v : G.V) : effective (oneChip v) := by
  intro w
  dsimp only [oneChip]
  by_cases h_eq : w = v <;> simp only [h_eq, ↓reduceIte, ge_iff_le, Std.le_refl, zero_le_one]

/-- The divisor $D_1-D_2$ is effective if and only if $D_1 \ge D_2$. -/
lemma sub_eff_iff_geq {G : CFGraph} (D₁ D₂ : CFDiv G) : effective (D₁ - D₂) ↔ D₁ ≥ D₂ :=
  forall_congr' (fun _ => sub_nonneg)

/-- A divisor is winnable if it is linearly equivalent to an effective divisor.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 1.14. -/
def winnable (G : CFGraph) (D : CFDiv G) : Prop :=
  ∃ D' ∈ Eff G, linearEquiv G D D'


/-!
## The degree homomorphism and the Laplacian

The *degree* of a divisor $D$ is $\deg(D) = \sum_v D(v)$, the total number of chips.
It is a group homomorphism $\mathrm{Div}(G) \to \mathbb{Z}$.
Principal divisors have degree zero, so linearly equivalent divisors have equal degree.

The *Laplacian matrix* `laplacianMatrix G` is the matrix $L = \mathrm{Deg}(G) - A$, where
$\mathrm{Deg}(G)$ is the diagonal degree matrix and $A$ is the adjacency matrix.
Applying the Laplacian to a firing script produces the corresponding principal divisor.
-/

/-- The degree of a divisor is the sum of its values over all vertices.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 1.4. -/
def deg {G : CFGraph} : CFDiv G →+ ℤ := {
  toFun := λ D => ∑ v, D v,
  map_zero' := by
    simp only [Pi.zero_apply, sum_const_zero],
  map_add' := by
    intro D₁ D₂
    simp only [Pi.add_apply, sum_add_distrib],
}

@[simp] lemma deg_one_chip {G : CFGraph} (v : G.V) : deg (oneChip v) = 1 := by
  simp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk, oneChip, sum_ite_eq', mem_univ, ↓reduceIte]

/-- Effective divisors have nonnegative degree. -/
lemma deg_of_eff_nonneg (D : CFDiv G) :
  effective D → deg D ≥ 0 := by
  intro h_eff
  exact Finset.sum_nonneg fun v _ => h_eff v

/-- The only effective divisor of degree 0 is 0. -/
lemma eff_degree_zero (D : CFDiv G) : effective D → deg D = 0 → D = 0 := by
  intro h_eff h_deg
  funext v
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => h_eff w)).1
    (by simpa only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using h_deg) v (Finset.mem_univ v)

/-- The degree of a firing vector is zero. -/
private lemma deg_firing_vector_eq_zero (G : CFGraph) (v_fire : G.V) :
  deg (firingVector G v_fire) = 0 := by
  dsimp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk, firingVector]
  rw [Finset.sum_ite]
  have h_filter_eq_single : Finset.filter (fun x => x = v_fire) univ = {v_fire} := by
    ext x; simp only [eq_comm, Finset.mem_filter, mem_univ, true_and, Finset.mem_singleton]
  rw [h_filter_eq_single, Finset.sum_singleton]
  have h_filter_eq_erase :
      Finset.filter (fun x => ¬x = v_fire) univ = Finset.univ.erase v_fire := by
    ext x
    simp only [Finset.mem_filter, mem_univ, true_and, mem_erase, and_true]
  rw [h_filter_eq_erase]
  simp only [vertexDegree, mem_univ, sum_erase_eq_sub, num_edges_self_zero, CharP.cast_eq_zero,
      sub_zero, neg_add_cancel]

/-- Every principal divisor has degree zero. -/
private lemma degree_of_principal_divisor_is_zero (G : CFGraph) (h : CFDiv G) :
  h ∈ principalDivisors G → deg h = 0 := by
  intro h_mem_princ
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ h_mem_princ
  · rintro x ⟨v, rfl⟩
    exact deg_firing_vector_eq_zero G v
  · simp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, sum_const_zero]
  · intro x y _ _ hx hy
    rw [deg.map_add, hx, hy, add_zero]
  · intro x _ hx
    rw [deg.map_neg, hx, neg_zero]

/-- Linearly equivalent divisors have the same degree.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Proposition 1.15. -/
theorem linear_equiv_preserves_deg (G : CFGraph) (D D' : CFDiv G) (h_equiv : linearEquiv G D D') :
  deg D = deg D' := by
  unfold linearEquiv at h_equiv
  apply degree_of_principal_divisor_is_zero at h_equiv
  rw [map_sub] at h_equiv
  linarith

/-- An effective divisor of degree $k_1+k_2$ can be decomposed into a sum of two effective
divisors of degrees $k_1$ and $k_2$, respectively. -/
lemma effective_divisor_decomposition (G : CFGraph) (E'' : CFDiv G) (k₁ k₂ : ℕ)
  (h_effective : effective E'') (h_deg : deg E'' = k₁ + k₂) :
  ∃ (E₁ E₂ : CFDiv G),
    effective E₁ ∧ effective E₂ ∧
    deg E₁ = k₁ ∧ deg E₂ = k₂ ∧
    E'' = E₁ + E₂ := by

  let can_split (E : CFDiv G) (a b : ℕ): Prop :=
    ∃ (E₁ E₂ : CFDiv G),
      effective E₁ ∧ effective E₂ ∧
      deg E₁ = a ∧ deg E₂ = b ∧
      E = E₁ + E₂

  let P (a b : ℕ) : Prop := ∀ (E : CFDiv G),
    effective E → deg E = a + b → can_split E a b

  have h_ind (a b : ℕ): P a b := by
    induction a with
    | zero =>
    . -- Base case: a = 0
      intro E h_eff h_deg
      use (0 : CFDiv G), E
      constructor
      -- E₁ is effective
      dsimp only [effective, Pi.zero_apply]
      intro v
      linarith
      -- E₂ is effective
      constructor
      exact h_eff
      -- deg E₁ = 0
      constructor
      simp only [_root_.map_zero, CharP.cast_eq_zero]
      -- deg E₂ = b
      constructor
      rw[h_deg]
      simp only [CharP.cast_eq_zero, zero_add]
      -- E = 0 + E
      simp only [zero_add]
    | succ a ha =>
    . -- Inductive step: assume P a b holds, prove P (a+1) b
      dsimp only [Int.natCast_add, Int.cast_ofNat_Int, P] at *
      intro E E_effective E_deg
      have ex_v : ∃ (v : G.V), E v ≥ 1 := by
        by_contra h_contra
        push Not at h_contra
        have h_sum : deg E = 0 := by
          dsimp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          rw [Finset.sum_eq_zero_iff_of_nonneg (fun v _ => E_effective v)]
          intro v hv
          have h_nonneg : 0 ≤ E v := E_effective v
          specialize h_contra v
          linarith
        rw [h_sum] at E_deg
        linarith
      rcases ex_v with ⟨v, hv_ge_one⟩
      let E' := E - oneChip v
      have h_E'_effective : effective E' := by
        intro w
        dsimp only [Pi.sub_apply, E']
        by_cases hw : w = v
        · rw [hw]
          specialize hv_ge_one
          dsimp only [oneChip]
          simp only [↓reduceIte, Int.sub_nonneg]
          linarith
        · specialize E_effective w
          dsimp only [oneChip]
          simp only [hw, ↓reduceIte, sub_zero, ge_iff_le]
          linarith
      specialize ha E' h_E'_effective
      have h_deg_E' : deg E' = a + b := by
        dsimp only [E']; simp only [map_sub, deg_one_chip]; omega
      apply ha at h_deg_E'
      rcases h_deg_E' with ⟨E₁, E₂, h_E1_eff, h_E2_eff, h_deg_E1, h_deg_E2, h_eq_split⟩
      use E₁ + oneChip v, E₂
      -- Check E₁ + oneChip v is effective
      constructor
      apply (Eff G).add_mem
      -- E₁ is effective
      exact h_E1_eff
      -- oneChip v is effective
      intro w
      dsimp only [oneChip]
      simp only [ge_iff_le]
      by_cases hw : w = v
      rw [hw]
      simp only [↓reduceIte, zero_le_one]
      simp only [hw, ↓reduceIte, Std.le_refl]
      -- E₂ is effective
      constructor
      exact h_E2_eff
      -- deg (E₁ + oneChip v) = a + 1
      constructor
      simp only [_root_.map_add, h_deg_E1, deg_one_chip, Nat.cast_add, Nat.cast_one]
      -- deg E₂ = b
      constructor
      exact h_deg_E2
      -- E = (E₁ + oneChip v) + E₂
      dsimp only [E'] at h_eq_split
      rw [add_assoc, add_comm (oneChip v), ← add_assoc, ← h_eq_split]
      abel

  exact h_ind k₁ k₂ E'' h_effective h_deg

open Matrix

/-- The Laplacian matrix of a CFGraph.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 2.6. -/
def laplacianMatrix (G : CFGraph) : Matrix G.V G.V ℤ :=
  λ i j => if i = j then vertexDegree G i else - (numEdges G i j)

-- Note: The Laplacian matrix L is given by Deg(G) - A, where Deg(G) is the diagonal
-- matrix of degrees and A is the adjacency matrix.
-- This matrix can be used to represent the effect of a firing script on a divisor.

/-- Applies the Laplacian matrix to a firing script and a current divisor to obtain a
new divisor. -/
def applyLaplacian (G : CFGraph) (σ : firingScript G) (D: CFDiv G) : CFDiv G :=
  fun v => (D v) - (laplacianMatrix G).mulVec σ v

/-!
## q-effective divisors

Fix a vertex $q$. A divisor $D$ is *$q$-effective* if $D(v) \geq 0$ for all $v \neq q$;
it may have an arbitrary (possibly negative) value at $q$ itself. The structure `qEffectiveDivisor`
packages such a divisor with its proof of $q$-effectivity.

A key fact for connected graphs is that every divisor is linearly equivalent to a
$q$-effective divisor (`q_effective_exists`). The proof goes via the notion of a
*benevolent* set: a set $S$ is benevolent if any divisor can be made to have all its
debt concentrated on $S$ via firing moves.
-/

/-- A divisor is *$q$-effective* if it has a nonnegative number of chips at every vertex
except possibly $q$. -/
def qEffective {G : CFGraph} (q : G.V) (D : CFDiv G) : Prop :=
  ∀ v : G.V, v ≠ q → D v ≥ 0

/-- A divisor bundled with a proof that it is $q$-effective. -/
structure qEffectiveDivisor (G : CFGraph) (q : G.V) where
  /-- The underlying divisor, effective away from the distinguished vertex. -/
  (D : CFDiv G) (h_eff : qEffective q D)

/-- A set of vertices is benevolent if it is possible to concentrate all debt on this set. -/
def benevolent (G : CFGraph) (S : Finset G.V) : Prop :=
  ∀ (D : CFDiv G), ∃ (E : CFDiv G), linearEquiv G D E ∧ (∀ (v : G.V), E v < 0 → v ∈ S)

/-- In a connected graph, any nonempty set is benevolent. -/
lemma benevolent_of_nonempty {G : CFGraph} (h_conn : graphConnected G) (S : Finset G.V) (h_nonempty
    : S.Nonempty) :
  benevolent G S := by
  by_cases h : S = Finset.univ
  · -- Case: S = G.V
    intro D
    use D
    -- Verify the first part of the conjunction
    constructor
    exact linearEquiv.refl G D
    -- Verify second part
    intro v h_neg
    rw [h]
    simp only [mem_univ]
  · -- Case: S ≠ G.V
    let h_conn' := h_conn -- Unsimplified copy for later
    dsimp only [graphConnected] at h_conn
    specialize h_conn S
    have : ∃ (v w : G.V), v ∈ S ∧ w ∉ S := by
      let v := Classical.choose h_nonempty
      have v_in_S : v ∈ S := Classical.choose_spec h_nonempty
      have : (univ \ S).Nonempty := by
        contrapose! h
        simp only [sdiff_eq_empty_iff_subset, univ_subset_iff] at h
        exact h
      let w := Classical.choose this
      have h_vw : w ∉ S := by
        have := Classical.choose_spec this
        simp only [mem_sdiff, mem_univ, true_and] at this
        exact this
      use v, w
    have h_vw := h_conn this
    rcases h_vw with ⟨v,h_v,w,h_w,h_edge⟩
    let T := insert w S
    have h_T_nonempty : T.Nonempty := by
      use w
      simp only [mem_insert, true_or, T]
    have ih := benevolent_of_nonempty h_conn' T h_T_nonempty
    intro D
    specialize ih D
    rcases ih with ⟨E1, h_lequiv_1, h_eff_S⟩
    -- Now need to adjust E1 to get E
    have : ∃ E : CFDiv G, linearEquiv G E1 E ∧ (∀ v : G.V, E v < 0 → v ∈ S) := by
      let fire := firingVector G v
      have p_f : fire ∈ principalDivisors G := mem_principal_divisors_firing_vector G v
      let k := max 0 (-(E1 w))
      let E := E1 + k • fire
      use E
      constructor
      · -- Verify linear equivalence
        unfold linearEquiv
        have h_diff : E - E1 = k • fire := by
          simp only [zsmul_eq_mul, add_sub_cancel_left, E]
        rw [h_diff]
        exact AddSubgroup.zsmul_mem _ p_f k
      · -- Verify effectiveness outside S
        intro x h_E_neg
        by_cases h_x_eq_w : x = w
        · -- Case x = w
          exfalso
          rw [h_x_eq_w] at h_E_neg
          dsimp only [Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul, E] at h_E_neg
          contrapose! h_E_neg
          simp only [k]
          by_cases h : -(E1 w) ≥ 0
          . -- Case : E1 w nonpositive
            have : max 0 (-(E1 w)) = -(E1 w) := by
              simp only [sup_eq_right, Int.neg_nonneg]; linarith
            rw [this]
            have : E1 w + -E1 w * fire w = (-E1 w) * (fire w -1) := by ring
            rw [this]
            apply mul_nonneg h
            -- Goal: fire w -1 ≥ 0
            dsimp only [firingVector, fire]
            have : ¬ (w = v) := by
              contrapose! h_w
              rw [← h_w] at h_v
              exact h_v
            simp only [this, ↓reduceIte, Int.sub_nonneg, Nat.one_le_cast, ge_iff_le]
            linarith [h_edge]
          . -- Case : E1 w positive
            push Not at h
            dsimp only [max, Int.neg_nonneg]
            split_ifs at * with hle
            · linarith
            · simp only [zero_mul, add_zero] at *; linarith
        . -- Case : x ≠ w
          have h_T := h_eff_S x
          by_contra! x_nin_S
          have h_xT : x ∉ T := by
            contrapose! x_nin_S with x_in_T
            dsimp only [T] at x_in_T
            simp only [mem_insert, h_x_eq_w, false_or] at x_in_T
            exact x_in_T
          specialize h_eff_S x
          contrapose! h_eff_S
          simp only [h_xT, not_false_eq_true, and_true]
          contrapose! h_E_neg with h_E1
          -- Goal: 0 ≤ E x
          dsimp only [Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul, E]
          apply add_nonneg h_E1
          -- Goal : 0 ≤ k * fire x
          apply mul_nonneg
          -- Show 0 ≤ k
          dsimp only [k]
          simp only [le_sup_left]
          -- Show 0 ≤ fire x
          dsimp only [firingVector, fire]
          have : ¬ (x = v) := by
            contrapose! x_nin_S with x_eq_v
            rw [x_eq_v]
            exact h_v
          simp only [this, ↓reduceIte, Nat.cast_nonneg]
    rcases this with ⟨E, h_lequiv_2, h_eff_S_final⟩
    use E
    constructor
    · -- Verify linear equivalence
      exact h_lequiv_1.trans h_lequiv_2
    · -- Verify effectiveness outside S
      exact h_eff_S_final
termination_by ((univ : Finset G.V).card - S.card)
decreasing_by
  have h_succ: (insert w S).card = S.card + 1 := by
    apply Finset.card_eq_succ.mpr
    use w, S
  rw [h_succ]
  refine Nat.sub_succ_lt_self univ.card S.card ?_
  have : (insert w S).card ≤ (univ : Finset G.V).card := by
    simpa only [card_univ] using Finset.card_le_univ (insert w S)
  linarith

/-- In a connected graph, every divisor is linearly equivalent to a $q$-effective divisor.

Equivalently, every divisor can have all of its debt concentrated at $q$. -/
theorem q_effective_exists {G : CFGraph} (h_conn : graphConnected G) (q : G.V) (D : CFDiv G) :
  ∃ (E : CFDiv G), qEffective q E ∧ linearEquiv G D E := by
  have h_bene := benevolent_of_nonempty h_conn {q} (by use q; simp only [Finset.mem_singleton]) D
  rcases h_bene with ⟨E,h_equiv, h_eff⟩
  have : qEffective q E := by
    intro v v_ne_q
    specialize h_eff v
    contrapose! h_eff
    simp only [h_eff, Finset.mem_singleton, true_and]
    exact v_ne_q
  exact ⟨E,this, h_equiv⟩


/-!
## The q-reduction partial order

A firing script $\sigma$ is a *$q$-reducer* if $\sigma(q) \leq \sigma(v)$ for all $v$,
meaning $q$ is fired the least (or not at all relative to the others). The relation
`reducesTo G q D₁ D₂` holds when $D_2$ is obtained from $D_1$ by applying a $q$-reducer
script, i.e. $D_2 = D_1 + \mathrm{prin}(\sigma)$ for some $q$-reducer $\sigma$.

This relation is reflexive and transitive, and in connected graphs it is also antisymmetric
(`reduces_to_antisymmetric`), making it a partial order on $q$-effective divisors. The
antisymmetry relies on the fact that a firing script with trivial principal divisor must
be constant (`constant_script_of_zero_prin`).

Two further facts about this order do most of the work in the next section: the number of
chips at $q$ is monotone along the order (`reduces_to_q_mono`), and a script that is a
$q$-reducer in both directions has zero principal divisor
(`prin_eq_zero_of_two_sided_reducer`) — a connectivity-free shadow of antisymmetry.
-/

/-- A firing script $\sigma$ is a *$q$-reducer* if $q$ is fired the minimum number of times:
$\sigma(q) \le \sigma(v)$ for all vertices $v$. -/
def qReducer (G : CFGraph) (q : G.V) (σ : firingScript G) : Prop :=
  ∀ v : G.V, σ q ≤ σ v

/-- The relation `reducesTo G q D₁ D₂` holds when $D_2$ is obtained from $D_1$ by
applying a $q$-reducer script:
$$
D_2 = D_1 + \operatorname{prin}_G(\sigma)
$$
for some $\sigma$ with $\sigma(q) \le \sigma(v)$ for all vertices $v$. -/
def reducesTo (G : CFGraph) (q : G.V) (D₁ D₂: CFDiv G) : Prop :=
  ∃ σ : firingScript G, qReducer G q σ ∧ D₂ = D₁ + prin G σ

/-- The `reducesTo` relation is reflexive: any divisor reduces to itself via the zero script. -/
private lemma reduces_to_reflexive (G : CFGraph) (q : G.V) (D : CFDiv G) :
  reducesTo G q D D := by
  refine ⟨0, by simp only [qReducer, Pi.zero_apply, Std.le_refl, implies_true],
      by simp only [_root_.map_zero, add_zero]⟩

/-- The `reducesTo` relation is transitive: composing two $q$-reducer scripts yields a
$q$-reducer script. -/
private lemma reduces_to_transitive (G : CFGraph) (q : G.V) (D₁ D₂ D₃ : CFDiv G) :
  reducesTo G q D₁ D₂ → reducesTo G q D₂ D₃ → reducesTo G q D₁ D₃ := by
  rintro ⟨σ₁, h_reducer_1, h_D2_eq⟩ ⟨σ₂, h_reducer_2, h_D3_eq⟩
  use σ₁ + σ₂
  refine ⟨?_, ?_⟩
  ·
    intro v
    repeat rw [Pi.add_apply]
    apply add_le_add (h_reducer_1 v) (h_reducer_2 v)
  ·
    rw [(prin G).map_add, ← add_assoc]
    rw [← h_D2_eq, ← h_D3_eq]

/-- Along the $q$-reduction order, the number of chips at $q$ is monotone non-decreasing:
a $q$-reducer script sends a nonnegative number of chips toward $q$. -/
private lemma reduces_to_q_mono (G : CFGraph) (q : G.V) {D₁ D₂ : CFDiv G} :
  reducesTo G q D₁ D₂ → D₁ q ≤ D₂ q := by
  rintro ⟨σ, h_reducer, h_eq⟩
  have h_prin_q : (prin G σ) q ≥ 0 := by
    rw [prin_apply]
    apply Finset.sum_nonneg
    intro e _
    apply mul_nonneg
    linarith [h_reducer e]
    exact Int.natCast_nonneg _
  rw [h_eq, Pi.add_apply]
  linarith

/-- In a connected graph, a firing script with zero principal divisor must be constant.
This is the key step in proving antisymmetry of `reducesTo`. -/
private lemma constant_script_of_zero_prin {G : CFGraph} (h_conn : graphConnected G) (σ :
    firingScript G) : prin G σ = 0 → ∀ (v w : G.V), σ v = σ w := by
  intro zero_eq
  let min_exists := Finset.exists_min_image Finset.univ σ
    (by use Classical.arbitrary G.V; simp only [mem_univ])
  rcases min_exists with ⟨q, ⟨_,h_reducer⟩⟩
  have h_reducer : ∀ v : G.V, σ q ≤ σ v := by
    intro v; specialize h_reducer v
    simp only [mem_univ, forall_const] at h_reducer; exact h_reducer
  let S := Finset.univ.filter (λ v => σ v = σ q)
  have q_in_S : q ∈ S := by
    dsimp only [S]
    simp only [Finset.mem_filter, mem_univ, and_self]
  have S_full : ∀ v : G.V, v ∈ S := by
    by_contra! v_nin_S
    rcases v_nin_S with ⟨v, h_v⟩
    have h : ∃ (u v : G.V), u ∈ S ∧ v ∉ S := by
      use q, v
    have := h_conn S h
    rcases this with ⟨u, h_u_in_S, w, h_w_nin_S, h_edge⟩
    have nonneg_terms: ∀ w : G.V, (σ w - σ u) * (numEdges G u w : ℤ) ≥ 0 := by
      intro w
      have h_σw_ge_σu : σ w - σ u ≥ 0 := by
        dsimp only [S] at h_u_in_S h_w_nin_S
        simp only [Finset.mem_filter, mem_univ, true_and] at h_u_in_S
        specialize h_reducer w
        linarith
      apply Int.mul_nonneg h_σw_ge_σu (Nat.cast_nonneg _)
    have pos_term : ∃ (w : G.V), (σ w - σ u) * (numEdges G u w : ℤ) > 0 := by
      use w
      apply Int.mul_pos
      · -- Show σ w - σ u > 0
        dsimp only [S] at h_u_in_S h_w_nin_S
        simp only [Finset.mem_filter, mem_univ, true_and] at h_u_in_S h_w_nin_S
        specialize h_reducer w
        rw [h_u_in_S]
        apply lt_of_le_of_ne at h_reducer
        have : ¬ σ q = σ w := by
          contrapose! h_w_nin_S
          rw [← h_w_nin_S]
        apply h_reducer at this
        linarith
      · -- Show numEdges G u w > 0
        simp only [Int.natCast_pos, h_edge]
    have : ∑ u_1 : G.V, (σ u_1 - σ u) * ↑(numEdges G u u_1) >0 := by
      apply Finset.sum_pos'
      intro i _
      exact nonneg_terms i
      rcases pos_term with ⟨w, h_pos⟩
      use w
      simp only [mem_univ, true_and]
      exact h_pos
    -- apply zero_eq at u
    have zero_eq_at_u: (prin G) σ u = 0 := by
      simp only [zero_eq, Pi.zero_apply]
    rw [prin_apply] at zero_eq_at_u
    linarith [zero_eq_at_u]
  intro v w
  have eq_q : ∀ v : G.V, σ v = σ q := by
    intro v; specialize S_full v
    dsimp only [S] at S_full; simp only [Finset.mem_filter, mem_univ, true_and] at S_full
    exact S_full
  rw [eq_q v, eq_q w]

/-- A script that is a $q$-reducer in both directions is constant, and hence has zero
principal divisor. This is antisymmetry at the level of scripts; unlike
`reduces_to_antisymmetric` it requires no connectivity hypothesis. -/
private lemma prin_eq_zero_of_two_sided_reducer (G : CFGraph) (q : G.V) (σ : firingScript G)
  (h₁ : qReducer G q σ) (h₂ : qReducer G q (-σ)) : prin G σ = 0 := by
  have h_const : ∀ v : G.V, σ v = σ q := by
    intro v
    have hv₂ := h₂ v
    repeat rw [Pi.neg_apply] at hv₂
    linarith [h₁ v]
  rw [show σ = (fun _ : G.V => σ q) from funext h_const, prin_const]

/-- In a connected graph, the `reducesTo` relation is antisymmetric, completing the proof
that it is a partial order on $q$-effective divisors. -/
private lemma reduces_to_antisymmetric {G : CFGraph} (h_conn : graphConnected G) (q : G.V) (D₁ D₂ :
    CFDiv G) :
  reducesTo G q D₁ D₂ → reducesTo G q D₂ D₁ → D₁ = D₂ := by
  intro h_red_12 h_red_21
  rcases h_red_12 with ⟨σ₁, h_reducer_1, h_D2_eq⟩
  rcases h_red_21 with ⟨σ₂, h_reducer_2, h_D1_eq⟩
  rw [h_D2_eq, add_assoc, ← (prin G).map_add] at h_D1_eq
  let σ := σ₁ + σ₂
  have prin_sum_zero : prin G (σ) = 0 := by
    simp only [_root_.map_add, left_eq_add] at h_D1_eq
    rw [← (prin G).map_add] at h_D1_eq
    exact h_D1_eq

  apply constant_script_of_zero_prin h_conn at prin_sum_zero

  -- σ₁ is a q-reducer in both directions, since σ₁ + σ₂ is constant
  have h_reducer_1' : qReducer G q (-σ₁) := by
    intro v
    repeat rw [Pi.neg_apply]
    specialize h_reducer_2 v
    dsimp only [Pi.add_apply, σ] at prin_sum_zero
    specialize prin_sum_zero q v
    linarith
  have h_prin_zero : prin G σ₁ = 0 :=
    prin_eq_zero_of_two_sided_reducer G q σ₁ h_reducer_1 h_reducer_1'
  rw [h_prin_zero] at h_D2_eq
  rw [h_D2_eq]
  simp only [add_zero]

/-!
## q-reduced divisors

A $q$-effective divisor $D$ is *$q$-reduced* if, for every nonempty set
$S \subseteq V(G) \setminus \{q\}$, some vertex in $S$ would go into debt if $S$ were fired.
Equivalently, $D$ is the maximum element of its linear equivalence class in the $q$-reduction
partial order.

The main results of this section are:
- Every divisor has a unique $q$-reduced representative (`exists_q_reduced_representative`,
  `q_reduced_unique`).
- A divisor is winnable if and only if its $q$-reduced representative is effective
  (`winnable_iff_q_reduced_effective`).

The existence proof proceeds by defining an `active` vertex (one that can still be fired
while maintaining $q$-effectivity) and showing that the `reductionExcess` — the total chips
at active vertices — strictly decreases at each reduction step.
-/

/-- A set of vertices is legal for `D` if firing it leaves every vertex in the set
nonnegative. -/
def legalSet (G : CFGraph) (D : CFDiv G) (S : Finset G.V) : Prop :=
  ∀ v ∈ S, outdegreeSet G S v ≤ D v

instance (G : CFGraph) (D : CFDiv G) (S : Finset G.V) :
    Decidable (legalSet G D S) := by
  unfold legalSet
  infer_instance

@[simp] theorem legal_set_empty (G : CFGraph) (D : CFDiv G) :
    legalSet G D (∅ : Finset G.V) := by
  intro v hv
  simp at hv

theorem effective_set_firing_of_legal_set (G : CFGraph) {D : CFDiv G}
    {S : Finset G.V} (hD : effective D) (hS : legalSet G D S) :
    effective (setFiring G D S) := by
  intro v
  by_cases hv : v ∈ S
  · rw [set_firing_apply_of_mem G D hv]
    have h := hS v hv
    omega
  · exact le_trans (hD v) (le_set_firing_apply_of_not_mem G D hv)

/-- Firing a legal set preserves effectivity away from a distinguished vertex. -/
theorem q_effective_set_firing_of_legal_set (G : CFGraph) {q : G.V} {D : CFDiv G}
    {S : Finset G.V} (hD : qEffective q D) (hS : legalSet G D S) :
    qEffective q (setFiring G D S) := by
  intro v hvq
  by_cases hv : v ∈ S
  · rw [set_firing_apply_of_mem G D hv]
    exact sub_nonneg.mpr (hS v hv)
  · exact le_trans (hD v hvq) (le_set_firing_apply_of_not_mem G D hv)

theorem legal_set_union (G : CFGraph) {D : CFDiv G} {S T : Finset G.V}
    (hS : legalSet G D S) (hT : legalSet G D T) :
    legalSet G D (S ∪ T) := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact le_trans (outdeg_S_antitone G Finset.subset_union_left v) (hS v hv)
  · exact le_trans (outdeg_S_antitone G Finset.subset_union_right v) (hT v hv)

/-- A divisor is $q$-reduced if it is effective away from $q$, and firing any nonempty
set of vertices disjoint from $q$ puts some vertex of that set into debt.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 3.4. -/
def qReduced (G : CFGraph) (q : G.V) (D : CFDiv G) : Prop :=
  qEffective q D ∧
  ∀ S : Finset G.V, q ∉ S → S.Nonempty → ¬ legalSet G D S

/-- A nonempty set avoiding `q` contains a vertex that would go into debt when fired
from a `q`-reduced divisor. -/
theorem qReduced.exists_lt_outdeg {G : CFGraph} {q : G.V} {D : CFDiv G}
    (hred : qReduced G q D) {S : Finset G.V} (hq : q ∉ S) (hS : S.Nonempty) :
    ∃ v ∈ S, D v < outdegreeSet G S v := by
  by_contra! h
  exact hred.2 S hq hS h



/-- Any firing script $\sigma$ attains its maximum on a nonempty set $S$, and applying
$\sigma$ removes at least $\operatorname{outdeg}_S(v)$ chips from each $v \in S$. -/
private lemma maxset_of_script (G : CFGraph) (σ : firingScript G) : ∃ S : Finset G.V, S.Nonempty ∧ ∀
    v ∈ S, (∀ w : G.V, σ w ≤ σ v ∧ (w ∈ S → σ w = σ v)) ∧ -(prin G σ v) ≥ outdegreeSet G S v := by
  let max_exists := Finset.exists_max_image Finset.univ σ
    (by use Classical.arbitrary G.V; simp only [mem_univ])
  rcases max_exists with ⟨w, ⟨_,w_argmax⟩⟩
  let S := Finset.univ.filter (σ · = σ w)
  use S
  constructor
  -- Show S is nonempty
  use w; dsimp only [S]; simp only [Finset.mem_filter, mem_univ, and_self]
  intro x x_in_S
  have h_x : σ x = σ w := by
    dsimp only [S] at x_in_S; simp only [Finset.mem_filter, mem_univ,
        true_and] at x_in_S; exact x_in_S

  constructor
  -- Maximality condition
  intro y
  constructor
  · -- Show σ y ≤ σ x
    specialize w_argmax y (by simp only [mem_univ])
    rw [h_x]; exact w_argmax
  · -- Show that if y ∈ S, then σ y = σ x
    intro y_in_S
    dsimp only [S] at y_in_S; simp only [Finset.mem_filter, mem_univ, true_and] at y_in_S
    rw [h_x]; exact y_in_S
  -- Show the outdegree inequality
  rw [prin_apply]
  rw [outdeg_S_eq_sum_filter]
  simp only [ge_iff_le]
  rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun x ↦ x ∉ S)]

  have : ∑ x_1 ∈ Finset.filter (fun x ↦ ¬x ∉ S) univ, -((σ x_1 - σ x) * ↑(numEdges G x x_1)) =
      0 := by
    apply Finset.sum_eq_zero
    intro y h_y
    have h_y : y ∈ S := by simp only [Decidable.not_not, subset_univ,
        filter_mem_eq_of_subset] at h_y; exact h_y
    have h_σy : σ y = σ x := by
      dsimp only [S] at h_y; simp only [Finset.mem_filter, mem_univ, true_and] at h_y
      rw [h_x, h_y]
    simp only [h_σy, sub_self, zero_mul, neg_zero]
  rw [this, Int.add_zero]
  apply Finset.sum_le_sum
  intro u h_u_notin_S
  by_cases h : numEdges G x u = 0
  · -- Case: numEdges G x u = 0
    simp only [h, CharP.cast_eq_zero, mul_zero, neg_zero, Std.le_refl]
  . -- Case: numEdges G x u ≠ 0
    have h : numEdges G x u > 0 := by
      exact Nat.pos_iff_ne_zero.mpr h
    suffices 1 ≤ σ x - σ u by
      rw [neg_mul_eq_neg_mul]
      simp only [neg_sub, Int.natCast_pos, h, le_mul_iff_one_le_left, this]
    suffices 0 < σ x - σ u by
      exact Int.le_of_sub_one_lt this
    dsimp only [S] at h_u_notin_S; simp only [Finset.mem_filter, mem_univ, true_and] at h_u_notin_S
    rw [h_x]
    specialize w_argmax u (by simp only [mem_univ])
    linarith [lt_of_le_of_ne w_argmax h_u_notin_S]

/-- If applying a script $\sigma$ to a $q$-effective divisor yields a $q$-reduced divisor,
then $\sigma$ is a $q$-reducer: a $q$-reduced divisor can only be reached from a
$q$-effective one by firing $q$ the least. -/
private lemma q_reducer_of_add_princ_reduced (G : CFGraph) (q : G.V) (D : CFDiv G) (σ : firingScript
    G) :
  qReduced G q (D + prin G σ) → qEffective q D → qReducer G q σ := by
  intro h_q_reduced h_q_effective v
  have h_eff := h_q_reduced.1
  rcases (maxset_of_script G (-σ)) with ⟨S, ⟨w, h_w⟩, h_S⟩
  have q_S : q ∈ S := by
    contrapose! h_q_effective with q_nin_S
    rcases h_q_reduced.exists_lt_outdeg q_nin_S ⟨w, h_w⟩ with
      ⟨v, v_in_S, h_debt⟩
    have dv_neg := lt_of_lt_of_le h_debt (h_S v v_in_S).2
    simp only [Pi.add_apply, map_neg, Pi.neg_apply, neg_neg, add_lt_iff_neg_right] at dv_neg
    unfold qEffective; push Not; use v
    suffices v ≠ q by simp only [ne_eq, this, not_false_eq_true, dv_neg, and_self]
    contrapose! q_nin_S
    rw [← q_nin_S]; exact v_in_S
  have ineq : (-σ) v ≤ (-σ) q := ((h_S q q_S).1 v).1
  repeat rw [Pi.neg_apply] at ineq
  linarith

/-- Alternative description of $q$-reduced divisors: they are the maximal $q$-effective
divisors in their linear equivalence classes with respect to the $q$-reduction order. -/
private lemma maximum_of_q_reduced (G : CFGraph) {q : G.V} {D : CFDiv G} : qReduced G q D → ∀ D' :
    CFDiv G, linearEquiv G D D' → qEffective q D' → reducesTo G q D' D := by
  intro h_q_reduced D' h_lequiv h_eff
  unfold linearEquiv at h_lequiv
  obtain ⟨σ, hσ⟩ := (principal_iff_eq_prin G (D'-D)).mp h_lequiv
  have D_eq : D = D' + (prin G) (-σ) := by
    rw [map_neg, ←hσ]
    abel
  have hred := q_reducer_of_add_princ_reduced G q D' (-σ) (by rwa [← D_eq]) h_eff
  use (-σ), hred, D_eq

/-- In a connected graph, every maximal $q$-effective divisor in the $q$-reduction partial
order is $q$-reduced. This fact is not needed for future results, but is included for context. -/
private lemma q_reduced_of_maximal {G : CFGraph} (h_conn : graphConnected G) {q : G.V} {D : CFDiv G}
    (q_eff : qEffective q D) :  (∀ D' : CFDiv G, linearEquiv G D D' → qEffective q D' → reducesTo G
    q D' D) →  qReduced G q D := by
  intro h_maximal
  unfold qReduced
  constructor
  · -- Show qEffective holds
    exact q_eff
  · -- Show there is no nonempty legal set avoiding q
    intro S q_nin_S h_S_nonempty
    contrapose! h_maximal with h_reduces
    let σ := indicatorScript G S
    have h_reducer : qReducer G q σ := by
      intro v
      dsimp only [σ, indicatorScript]
      simp only [q_nin_S, ↓reduceIte]
      by_cases h : v ∈ S <;> simp only [h, ↓reduceIte, Std.le_refl, zero_le_one]
    use D + prin G σ
    constructor
    · -- Show linear equivalence
      unfold linearEquiv; simp only [add_sub_cancel_left]
      apply (principal_iff_eq_prin G (prin G σ)).mpr
      use σ
    constructor
    · -- Show qEffective
      rw [show σ = indicatorScript G S from rfl,
        ← set_firing_eq_add_prin_indicator_script]
      exact q_effective_set_firing_of_legal_set G q_eff h_reduces
    . -- Show ¬ reducesTo
      by_contra! h_reduces
      have h' : reducesTo G q D (D + prin G σ) := by use σ
      have : D = D + prin G σ := by
        exact reduces_to_antisymmetric h_conn q D (D + prin G σ) h' h_reduces
      have prin_zero : prin G σ = 0 := by
        calc
          prin G σ = -D + (D + prin G σ) := by abel
          _ = -D + D := by rw [← this]
          _ = 0 := by abel
      apply constant_script_of_zero_prin h_conn  at prin_zero
      let v := Classical.choose h_S_nonempty
      let h_v := Classical.choose_spec h_S_nonempty
      have v_S : v ∈ S := by exact h_v
      specialize prin_zero v q
      dsimp only [σ, indicatorScript] at prin_zero
      simp only [v_S, ↓reduceIte, q_nin_S, one_ne_zero] at prin_zero

/-- The $q$-reduced representative of an effective divisor is effective.

A $q$-reduced divisor is maximal in its class for the $q$-reduction order, so $E$ reduces
to $E'$; the number of chips at $q$ only increases along this order, and $E'$ is
nonnegative away from $q$ by definition. -/
private lemma q_reduced_of_effective_is_effective (G : CFGraph) (q : G.V) (E E' : CFDiv G) :
  effective E → linearEquiv G E E' → qReduced G q E' → effective E' := by
  intro h_eff h_equiv h_qred
  -- E' is the maximum of its class, so E reduces to E'; chips at q only increase along
  -- the order, and chips away from q are nonnegative since E' is q-effective.
  have h_qeff : qEffective q E := fun v _ => h_eff v
  have h_red : reducesTo G q E E' :=
    maximum_of_q_reduced G h_qred E h_equiv.symm h_qeff
  intro v
  by_cases hvq : v = q
  · rw [hvq]
    linarith [h_eff q, reduces_to_q_mono G q h_red]
  · exact h_qred.1 v hvq

/-- A winnable $q$-reduced divisor is effective. -/
lemma effective_of_winnable_and_q_reduced (G : CFGraph) (q : G.V) (D : CFDiv G) :
  winnable G D → qReduced G q D → effective D := by
  intro h_winnable h_qred
  rcases h_winnable with ⟨E, h_eff_E, h_equiv⟩
  exact q_reduced_of_effective_is_effective G q E D h_eff_E h_equiv.symm h_qred

/-- The $q$-reduced representative of a divisor class is unique.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 3.6,
part 2 (uniqueness). -/
theorem q_reduced_unique (G : CFGraph) (q : G.V) (D₁ D₂ : CFDiv G) :
  qReduced G q D₁ ∧ qReduced G q D₂ ∧ linearEquiv G D₁ D₂ → D₁ = D₂ := by
  intro ⟨h_qred_1,h_qred_2,h_lequiv⟩
  unfold linearEquiv at h_lequiv
  simp only [principal_iff_eq_prin] at h_lequiv
  rcases h_lequiv with ⟨σ, h_D2_eq⟩
  have h_reducer_1 : qReducer G q σ := by
    apply q_reducer_of_add_princ_reduced G q D₁ σ
    rw [← h_D2_eq]
    simp only [add_sub_cancel]
    exact h_qred_2
    exact h_qred_1.left
  have h_reducer_2 : qReducer G q (-σ) := by
    apply q_reducer_of_add_princ_reduced G q D₂ (-σ)
    rw [(prin G).map_neg, ← sub_eq_add_neg]
    simp only [← h_D2_eq, sub_sub_cancel]
    exact h_qred_1
    exact h_qred_2.left
  have h_zero : prin G σ = 0 :=
    prin_eq_zero_of_two_sided_reducer G q σ h_reducer_1 h_reducer_2
  rw [h_zero] at h_D2_eq
  apply sub_eq_zero.mp at h_D2_eq
  rw [h_D2_eq]



/-- A vertex is *active* if there exists a firing script that leaves the divisor effective
away from $q$, fires $q$ minimally, and fires this vertex strictly more than $q$. -/
def active (G : CFGraph) (q : G.V) (D : CFDiv G) (v : G.V) : Prop :=
  ∃ σ : firingScript G, qReducer G q σ ∧ qEffective q (D + prin G σ) ∧ σ q < σ v

/-- A $q$-effective divisor with no active vertices is $q$-reduced. -/
private lemma q_reduced_of_no_active (G :CFGraph) {q : G.V} {D : CFDiv G} (h_eff : qEffective q D)
    (h_no_active : ∀ v : G.V, ¬ active G q D v) :
  qReduced G q D := by
  contrapose! h_no_active with h_not_q_reduced
  dsimp only [qReduced, ne_eq] at h_not_q_reduced
  push Not at h_not_q_reduced
  rcases h_not_q_reduced h_eff with ⟨S, q_nin_S, h_S_nonempty, h_outdeg⟩
  -- Construct a firing script that fires all vertices in S
  let σ := indicatorScript G S
  have h_reducer : qReducer G q σ := by
    intro v
    dsimp only [σ, indicatorScript]
    simp only [q_nin_S, ↓reduceIte]
    by_cases h : v ∈ S
    simp only [h, ↓reduceIte, zero_le_one]; simp only [h, ↓reduceIte, Std.le_refl]
  use Classical.choose h_S_nonempty
  let h := Classical.choose_spec h_S_nonempty
  dsimp only [active]
  use σ
  refine ⟨h_reducer, ?_, ?_⟩
  · rw [show σ = indicatorScript G S from rfl,
      ← set_firing_eq_add_prin_indicator_script]
    exact q_effective_set_firing_of_legal_set G h_eff h_outdeg
  · simp only [σ, indicatorScript, q_nin_S, ↓reduceIte, h, zero_lt_one]

/-- The total number of chips held at active vertices of $D$.

This quantity strictly decreases at each step of the $q$-reduction algorithm, providing
the termination measure for
`q_effective_to_q_reduced`. -/
noncomputable def reductionExcess (G : CFGraph) (q : G.V) (D : CFDiv G) : ℤ := by
  classical
  exact (∑ v : G.V, if active G q D v then D v else 0)


/-- The reduction excess is nonnegative for $q$-effective divisors, since active vertices
satisfy $v \ne q$ and hence $D(v) \ge 0$. -/
private lemma reduction_excess_nonneg (G : CFGraph) {q : G.V} {D : CFDiv G} (h_eff : qEffective q D)
    :
  0 ≤ reductionExcess G q D := by
  dsimp only [reductionExcess]
  apply Finset.sum_nonneg
  intro v _
  by_cases h_active : active G q D v
  · -- Case: v is active
    simp only [h_active, ↓reduceIte]
    apply h_eff
    intro h_contra
    rw [h_contra] at h_active
    dsimp only [active] at h_active
    rcases h_active with ⟨σ, h_reducer, h_eff', h_ineq⟩
    simp only [lt_self_iff_false] at h_ineq
  · -- Case: v is not active
    simp only [h_active, ↓reduceIte, Std.le_refl]

/-- In a connected graph, every $q$-effective divisor is linearly equivalent to a $q$-reduced
divisor.

The proof is by induction on `reductionExcess`. -/
theorem q_effective_to_q_reduced {G : CFGraph} (h_conn : graphConnected G) {q : G.V} {D : CFDiv G}
    (h_eff : qEffective q D) :
  ∃ E : CFDiv G, qReduced G q E ∧ linearEquiv G D E := by
  -- Use induction on reductionExcess
  classical -- In order to filter using the undecidable "active"
  let S := Finset.univ.filter (λ v : G.V => active G q D v)
  have q_nin_S : q ∉ S := by
    intro h_contra
    dsimp only [S] at h_contra
    simp only [Finset.mem_filter, mem_univ, true_and] at h_contra
    dsimp only [active] at h_contra
    rcases h_contra with ⟨σ, h_reducer, h_ineq⟩
    simp only [lt_self_iff_false, and_false] at h_ineq
  by_cases h_S_empty : S = ∅
  · -- Case: No active vertices, so D is already q-reduced
    use D
    constructor
    · -- q-reducedness
      apply q_reduced_of_no_active G h_eff
      intro v h_contra
      have : v ∈ S := by
        dsimp only [S]
        simp only [Finset.mem_filter, mem_univ, h_contra, and_self]
      rw [h_S_empty] at this
      -- "this" is not v ∈ ∅, a contradiction
      simp only [notMem_empty] at this
    . -- Linear equivalence
      exact linearEquiv.refl G D
  · -- Case: There are active vertices. Choose one on the boundary.
    have : ∃ v : G.V, active G q D v := by
      contrapose! h_S_empty with h_no_active
      dsimp only [S]
      simp only [h_no_active, Finset.filter_false]
    rcases this with ⟨v_active, h_v_active⟩
    have : ∃ (v q : G.V), v ∈ S ∧ q ∉ S := by
      use v_active, q
      simp only [q_nin_S, not_false_eq_true, and_true]
      simp only [Finset.mem_filter, mem_univ, true_and, S]
      exact h_v_active
    have := h_conn S this
    rcases this with ⟨v, v_in_S, w, w_nin_S, h_edge⟩
    -- Fire involving v to get a new divisor D'
    simp only [Finset.mem_filter, mem_univ, true_and, S] at v_in_S
    dsimp only [active] at v_in_S
    rcases v_in_S with ⟨σ, h_reducer, h_eff_S, h_ineq⟩
    let D' := D + prin G (σ)
    have D_equiv_D' : linearEquiv G D D' := by
      unfold linearEquiv
      have : D' - D = prin G σ := by
        simp only [add_sub_cancel_left, D']
      rw [this]
      apply (principal_iff_eq_prin G (prin G σ)).mpr ⟨σ,rfl⟩

    -- Facts about D', needed for induction
    have h_eff' : qEffective q D' := by
      intro x x_ne_q
      dsimp only [Pi.add_apply, D']
      exact h_eff_S x x_ne_q

    have h_active_shrinks (x : G.V): active G q D' x → active G q D x := by
      intro h_active_D'
      dsimp only [active]
      rcases h_active_D' with ⟨σ', h_reducer', h_eff'', h_ineq'⟩
      use σ + σ'
      constructor
      · -- Show qReducer
        intro y
        repeat rw [Pi.add_apply]
        apply add_le_add (h_reducer y) (h_reducer' y)
      constructor
      · -- Show qEffective
        intro z z_ne_q
        dsimp only [D'] at h_eff''
        specialize h_eff'' z z_ne_q
        rw [(prin G).map_add, ← add_assoc]
        exact h_eff''
      · -- Show chips are fired from x
        repeat rw [Pi.add_apply]
        apply add_lt_add_of_le_of_lt
        exact h_reducer x
        exact h_ineq'

    have chips_to_inactive_per_edge (u x : G.V) : ¬ active G q D x → (σ u - σ x) * ↑(numEdges G x u)
      ≥ 0 := by
      intro h_inactive_D
      simp only [ge_iff_le]
      apply mul_nonneg
      · -- Show σ u - σ x ≥ 0
        have : σ x ≤ σ q := by
          dsimp only [active] at h_inactive_D
          push Not at h_inactive_D
          specialize h_inactive_D σ
          exact h_inactive_D h_reducer h_eff'
        have : σ u ≥ σ q := by
          specialize h_reducer u
          linarith
        linarith
      · -- Show numEdges G x u ≥ 0
        simp only [Nat.cast_nonneg]

    have chips_to_inactive (x : G.V) : ¬ active G q D x → D x ≤ D' x := by
      -- Goal: 0 ≤ ∑ (σ u - σ x) * numEdges G x u
      intro h_inactive_D
      simp only [Pi.add_apply, prin_apply, D']
      simp only [le_add_iff_nonneg_right]
      apply Finset.sum_nonneg
      intro u _
      exact chips_to_inactive_per_edge u x h_inactive_D

    have h_smaller : reductionExcess G q D' < reductionExcess G q D := by
      dsimp only [reductionExcess]
      repeat rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      -- First, pass to a sum over non-active vertices
      have h (D : CFDiv G) :
          ∑ x ∈ Finset.filter (active G q D) univ, D x =
            deg D - ∑ x ∈ Finset.filter (fun v => ¬ active G q D v) univ, D x := by
        dsimp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [← Finset.sum_filter_add_sum_filter_not univ (fun v => active G q D v)]
        simp only [add_sub_cancel_right]
      rw [h D', h D]
      have : deg D = deg D' :=
        linear_equiv_preserves_deg G D D' D_equiv_D'
      rw [← this]
      simp only [sub_lt_sub_iff_left, gt_iff_lt]
      -- Write as a sum over all vertices in order to compare terms
      have h (D : CFDiv G) :
          ∑ x ∈ Finset.filter (fun v => ¬ active G q D v) univ, D x =
            ∑ x : G.V, if ¬ active G q D x then D x else 0 := by
        rw [Finset.sum_filter]
      rw [h D', h D]
      -- Now compare term-by-term
      apply Finset.sum_lt_sum
      -- Show each term is ≤ the corresponding term
      intro x _
      by_cases h_active_D' : active G q D' x
      · -- Case: x is active in D'. Then already active in D.
        have h_active_D := h_active_shrinks x h_active_D'
        simp only [h_active_D, not_true_eq_false, ↓reduceIte, h_active_D', Std.le_refl]
      · -- Case: x is not active in D'.
        simp only [ite_not, h_active_D', not_false_eq_true, ↓reduceIte]
        by_cases h_active_D : active G q D x
        · -- Subcase: x is active in D
          simp only [h_active_D, ↓reduceIte]
          -- Show 0 ≤ D' x
          apply h_eff' x
          intro h_contra
          rw [h_contra] at h_active_D
          dsimp only [S] at q_nin_S
          simp only [Finset.mem_filter, mem_univ, true_and] at q_nin_S
          contradiction
        · -- Subcase: x is not active in D either
          simp only [h_active_D, ↓reduceIte]
          -- Show D x ≤ D' x
          exact chips_to_inactive x h_active_D
      -- Now, show that strict inequality holds for at least one term
      use w
      have h_inactive_D : ¬ active G q D w := by
        dsimp only [S] at w_nin_S
        simp only [Finset.mem_filter, mem_univ, true_and] at w_nin_S
        exact w_nin_S
      have h_active_D' : ¬ active G q D' w := by
        contrapose! h_inactive_D with h_active_D'
        exact (h_active_shrinks w) h_active_D'
      simp only [mem_univ, h_inactive_D, not_false_eq_true, ↓reduceIte, h_active_D', true_and,
          gt_iff_lt]
      -- Show D w < D' w
      simp only [Pi.add_apply, prin_apply, D']
      simp only [lt_add_iff_pos_right]
      -- Goal: 0 < ∑ (σ u - σ w) * numEdges
      apply Finset.sum_pos'
      -- Show each term is nonnegative
      intro u _
      exact chips_to_inactive_per_edge u w h_inactive_D
      -- Show at least one term is positive
      use v
      simp only [mem_univ, true_and]
      -- Goal: (σ v - σ w) * numEdges G w v > 0
      apply Int.mul_pos
      · -- Show σ v - σ w > 0
        have : σ w ≤ σ q := by
          dsimp only [active] at h_inactive_D
          push Not at h_inactive_D
          specialize h_inactive_D σ
          exact h_inactive_D h_reducer h_eff'
        linarith [this, h_ineq]
      . -- Show numEdges G w v > 0
        rw [← num_edges_symmetric G v w]
        simp only [Int.natCast_pos, h_edge]
    have ih := q_effective_to_q_reduced h_conn h_eff'
    rcases ih with ⟨E, h_q_reduced, h_lequiv⟩
    use E
    constructor
    · -- q-reducedness
      exact h_q_reduced
    · -- Linear equivalence
      exact D_equiv_D'.trans h_lequiv
termination_by (reductionExcess G q D).toNat
decreasing_by
  -- Some effort needed to deal with ℤ versus ℕ
  rw [Int.toNat_lt]
  simp only [Int.ofNat_toNat, lt_sup_iff]
  dsimp only [D'] at h_smaller
  left
  exact h_smaller
  exact reduction_excess_nonneg G h_eff'

/-- Every divisor is linearly equivalent to some $q$-reduced divisor.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 3.6,
part 1 (existence). -/
theorem exists_q_reduced_representative {G : CFGraph} (h_conn : graphConnected G) (q : G.V) (D :
    CFDiv G) :
  ∃ D' : CFDiv G, linearEquiv G D D' ∧ qReduced G q D' :=
by
  rcases q_effective_exists h_conn q D with ⟨D_eff, h_eff, h_equiv⟩
  rcases q_effective_to_q_reduced h_conn h_eff with ⟨D_qred, h_qred, h_lequiv'⟩
  use D_qred
  constructor
  · -- Show linear equivalence
    exact h_equiv.trans h_lequiv'
  · -- Show q-reduced property
    exact h_qred

/-- Every divisor is linearly equivalent to exactly one $q$-reduced divisor.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 3.6
(existence and uniqueness combined). -/
lemma unique_q_reduced {G : CFGraph} (h_conn : graphConnected G) (q : G.V) (D : CFDiv G) :
  ∃! D' : CFDiv G, linearEquiv G D D' ∧ qReduced G q D' := by
  -- Prove existence and uniqueness separately
  have h_exists : ∃ D' : CFDiv G, linearEquiv G D D' ∧ qReduced G q D' := by
    exact exists_q_reduced_representative h_conn q D

  -- Combine existence and uniqueness using the standard constructor
  obtain ⟨D', hD'⟩ := h_exists
  refine ExistsUnique.intro D' hD' (fun y hy => ?_)
  exact q_reduced_unique G q y D' ⟨hy.2, hD'.2, hy.1.symm.trans hD'.1⟩

/-- A divisor is winnable if and only if its $q$-reduced representative is effective.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 3.7,
rephrased. -/
theorem winnable_iff_q_reduced_effective {G : CFGraph} (h_conn : graphConnected G) (q : G.V) (D :
    CFDiv G) :
  winnable G D ↔ ∃ D' : CFDiv G, linearEquiv G D D' ∧ qReduced G q D' ∧ effective D' := by
  constructor
  { -- Forward direction
    intro h_win
    rcases h_win with ⟨E, h_eff, h_equiv⟩
    rcases unique_q_reduced h_conn q D with ⟨D', h_D'⟩
    use D'
    constructor
    · exact h_D'.1.1  -- D is linearly equivalent to D'
    constructor
    · exact h_D'.1.2  -- D' is q-reduced
    · -- D' is effective: E ~ D ~ D', and the q-reduced form of an effective divisor
      -- is effective
      exact q_reduced_of_effective_is_effective G q E D' h_eff
        (h_equiv.symm.trans h_D'.1.1) h_D'.1.2
  }
  { -- Reverse direction
    intro h
    rcases h with ⟨D', h_equiv, h_qred, h_eff⟩
    use D'
    exact ⟨h_eff, h_equiv⟩
  }

/-!
## The handshaking theorem

The classical handshaking theorem for loopless multigraphs: the sum of all vertex degrees
is twice the number of edges (`sum_vertex_degree_eq_twice_card_edges`). The proof double
counts vertex-edge incidences, via the general counting lemma `sum_card_filter_eq_mul`.
These facts concern only the graph itself, not its divisor theory; they are collected here
for independent use. In this library, the handshaking theorem computes the degree of the
canonical divisor (see `degree_of_canonical_divisor` in `Orientation.lean`).
-/

/-- Rewrites a sum of filtered multiset cardinalities as a sum over mapped incidence counts. -/
private lemma sum_filter_eq_map (G : CFGraph) (M : Multiset (G.V × G.V)) (crit  : G.V → G.V × G.V →
    Prop)
    [∀ v e, Decidable (crit v e)] :
  ∑ v : G.V, Multiset.card (M.filter (crit v))
    = Multiset.sum (M.map (λ e => (Finset.univ.filter (λ v => (crit v e) )).card)) := by
  -- Define P and g using Prop for clarity in the proof - Available throughout
  let P : G.V → G.V × G.V → Prop := fun v e => crit v e
  let g : G.V × G.V → ℕ := fun e => (Finset.univ.filter (P · e)).card

  -- Rewrite the goal using P and g for proof readability
  suffices goal_rewritten : ∑ v : G.V, Multiset.card (M.filter (P v)) = Multiset.sum (M.map g) by
    exact goal_rewritten -- The goal is now exactly the statement `goal_rewritten`

  -- Prove the rewritten goal by induction on the multiset G.edges
  induction M using Multiset.induction_on with
  | empty =>
    simp only [filter_zero, Multiset.card_zero, sum_const_zero, Multiset.map_zero,
        sum_zero] -- Use _zero lemmas
  | cons e_head s_tail ih_s_tail =>
    -- Rewrite RHS: sum(map(g, e_head::s_tail)) = g e_head + sum(map(g, s_tail))
    rw [Multiset.map_cons, Multiset.sum_cons]

    -- Rewrite LHS: ∑ v, card(filter(P v, e_head::s_tail))
    simp_rw [← Multiset.countP_eq_card_filter]
    simp only [countP_cons]
    rw [Finset.sum_add_distrib]

    -- Simplify the second sum (∑ v, ite (P v e_head) 1 0) to g e_head
    have h_sum_ite_eq_card : ∑ v : G.V, ite (P v e_head) 1 0 = g e_head := by
      rw [← Finset.card_filter] -- This completes the proof for h_sum_ite_eq_card
    rw [h_sum_ite_eq_card]

    simp_rw [Multiset.countP_eq_card_filter]
    rw [add_comm, ih_s_tail]

/-- If every element of $M$ matches exactly $c$ vertices under `crit`, then summing the
filtered counts over all vertices gives $c$ times the size of $M$. -/
lemma sum_card_filter_eq_mul (G : CFGraph) (M : Multiset (G.V × G.V))
    (crit : G.V → G.V × G.V → Prop) [∀ v e, Decidable (crit v e)] (c : ℕ)
    (h_count : ∀ e ∈ M, (Finset.univ.filter (λ v => crit v e)).card = c) :
  ∑ v : G.V, Multiset.card (M.filter (crit v)) = c * Multiset.card M := by
  rw [sum_filter_eq_map G M crit, Multiset.map_congr rfl h_count, Multiset.map_const',
    Multiset.sum_replicate, Nat.nsmul_eq_mul, Nat.mul_comm]

/-- In a loopless graph, each edge has distinct endpoints. -/
private lemma edge_endpoints_distinct (G : CFGraph) (e : G.V × G.V) (he : e ∈ G.edges) :
    e.1 ≠ e.2 := by
  by_contra eq_endpoints
  rcases e with ⟨u,v⟩
  have : u = v := eq_endpoints
  rw [this] at he
  exact G.loopless v he

/-- Each edge is incident to exactly two vertices. -/
private lemma edge_incident_vertices_count (G : CFGraph) (e : G.V × G.V) (he : e ∈ G.edges) :
    (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card = 2 := by
  rw [Finset.card_eq_two]
  refine ⟨e.1, e.2, edge_endpoints_distinct G e he, ?_⟩
  ext v
  simp only [eq_comm, Finset.mem_filter, mem_univ, true_and, mem_insert, Finset.mem_singleton]

/-- Rewrites degree in terms of edge counts from each direction. -/
private lemma degree_eq_total_flow {T : Type*} [DecidableEq T] [Fintype T] :
    ∀ (S : Multiset (T × T)) (v : T), (∀ e ∈ S, e.1 ≠ e.2) →
      ∑ u : T, Multiset.card (Multiset.filter (fun e ↦ e = (v, u) ∨ e = (u, v)) S) =
        Multiset.card (S.filter (λ e => e.fst = v ∨ e.snd = v)) := by
  -- Induct on the multiset S
  intro S v h_loopless
  induction S using Multiset.induction_on with
  | empty =>
    simp only [filter_zero, Multiset.card_zero, sum_const_zero]
  | cons e_head s_tail ih_s_tail =>
    -- Rewrite both sides using the head and tail
    simp only [Multiset.filter_cons, card_add, sum_add_distrib]
    rw [ih_s_tail]
    -- Cancel the like terms in a + b = a + c
    suffices h :
        ∑ x : T, Multiset.card (if e_head = (v, x) ∨ e_head = (x, v) then {e_head} else 0) =
          Multiset.card (if e_head.1 = v ∨ e_head.2 = v then {e_head} else 0) by
      linarith

    rcases e_head with ⟨e, f⟩
    by_cases h_ev : e = v
    · subst h_ev
      have h_ef : e ≠ f := h_loopless (e, f) (by simp only [Multiset.mem_cons, true_or])
      have h_fv : f ≠ e := by simpa only [ne_eq, eq_comm] using h_ef
      rw [Finset.sum_eq_single f]
      · simp only [Prod.mk.injEq, true_or, ↓reduceIte, Multiset.card_singleton]
      · intro x _ h_x
        have h_fx : f ≠ x := fun h => h_x h.symm
        simp only [Prod.mk.injEq, h_fx, and_false, h_fv, or_self, ↓reduceIte, Multiset.card_zero]
      · simp only [mem_univ, not_true_eq_false, Prod.mk.injEq, true_or, ↓reduceIte,
          Multiset.card_singleton, one_ne_zero, imp_self]
    · by_cases h_fv : f = v
      · subst h_fv
        rw [Finset.sum_eq_single e]
        · simp only [Prod.mk.injEq, or_true, ↓reduceIte, Multiset.card_singleton]
        · intro x _ h_x
          have h_ex : e ≠ x := fun h => h_x h.symm
          simp only [Prod.mk.injEq, h_ev, false_and, h_ex, and_true, or_self, ↓reduceIte,
              Multiset.card_zero]
        · simp only [mem_univ, not_true_eq_false, Prod.mk.injEq, or_true, ↓reduceIte,
            Multiset.card_singleton, one_ne_zero, imp_self]
      · simp only [Prod.mk.injEq, h_ev, false_and, h_fv, and_false, or_self, ↓reduceIte,
          Multiset.card_zero, sum_const_zero]
    intro e
    specialize h_loopless e
    intro h_tail
    apply h_loopless
    simp only [Multiset.mem_cons, h_tail, or_true]

-- Key lemma for handshaking theorem: Sum of edge counts equals incident edge count
private lemma sum_num_edges_eq_filter_count (G : CFGraph) (v : G.V) :
  ∑ u, numEdges G v u = Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v)) := by
  dsimp only [numEdges]
  have h_loopless: ∀ e ∈ G.edges, e.1 ≠ e.2 := by
    intro e he
    exact edge_endpoints_distinct G e he
  exact degree_eq_total_flow G.edges v (h_loopless)

/--
**Handshaking theorem:** In a loopless multigraph $G$,
the sum of the degrees of all vertices is twice the number of edges:

$$
\sum_{v \in V(G)} \deg(v) = 2 |E(G)|.
$$
-/
theorem sum_vertex_degree_eq_twice_card_edges (G : CFGraph) :
    ∑ v, vertexDegree G v = 2 * ↑(Multiset.card G.edges) := by
  calc ∑ v, vertexDegree G v
    = ∑ v, ∑ u, (numEdges G v u : ℤ) := by simp_rw [vertexDegree]
    _ = ∑ v, ↑(∑ u, numEdges G v u) := by simp_rw [← Nat.cast_sum]
    _ = ∑ v, ↑(Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v)))  := by
      simp_rw [sum_num_edges_eq_filter_count G]
    _ = ↑(∑ v, Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v)))  := by
      rw [← Nat.cast_sum]
    _ = ↑(2 * Multiset.card G.edges) := by
      -- Each edge is incident to exactly two vertices
      rw [sum_card_filter_eq_mul G G.edges (λ v e => e.fst = v ∨ e.snd = v) 2
        (edge_incident_vertices_count G)]
    _ = 2 * ↑(Multiset.card G.edges) := by rw [Nat.cast_mul, Nat.cast_two]
