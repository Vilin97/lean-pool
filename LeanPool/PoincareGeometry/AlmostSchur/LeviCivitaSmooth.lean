/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaRegularityTwo

/-!
# Smooth regularity of a metric-compatible torsion-free connection

The Koszul identity lowers the differentiability order by one.  This file
packages that observation at arbitrary finite orders and then uses
`contMDiffAt_infty` to obtain the smooth covariant-derivative class.
-/

@[expose] public noncomputable section
open Bundle FiberBundle VectorField Set
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
local notation "TM" => (TangentSpace I : M → Type _)

local instance smoothMetricAt (n : ℕ) :
    IsContMDiffRiemannianBundle I (↑(n : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by
    exact WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))

local instance smoothVectorBundleAt (n : ℕ) :
    ContMDiffVectorBundle (↑(n : ℕ)) E TM I :=
  ContMDiffVectorBundle.of_le (n := ∞) (by
    exact WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))

local instance smoothMetricAtSucc (n : ℕ) :
    IsContMDiffRiemannianBundle I ((n : ℕ∞ω) + 1) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by
    exact_mod_cast (le_top : (n + 1 : ℕ∞) ≤ ⊤))

local instance smoothVectorBundleAtSucc (n : ℕ) :
    ContMDiffVectorBundle ((n : ℕ∞ω) + 1) E TM I :=
  ContMDiffVectorBundle.of_le (n := ∞) (by
    exact_mod_cast (le_top : (n + 1 : ℕ∞) ≤ ⊤))

/-! ## One finite Koszul step -/

theorem contMDiffAt_koszul_pairing_of_order (n : ℕ)
    (cov : CovariantDerivative I E TM)
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {X Y Z : Π y, TM y} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 1) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 1) (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 1) (T% Z) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun y ↦ inner ℝ (cov Y y (X y)) (Z y)) x := by
  letI : IsManifold I (minSmoothness ℝ (n + 1 : ℕ∞)) M :=
    IsManifold.of_le (n := ∞) (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (n + 1 : ℕ∞) ≤ ⊤ from le_top))
  letI : IsManifold I ((n + 1 : ℕ∞) + 1) M :=
    IsManifold.of_le (n := ∞) (by
      exact WithTop.coe_le_coe.mpr (show ((n + 1 : ℕ∞) + 1) ≤ ⊤ from le_top))
  -- The vector-field hypotheses use the outer `WithTop ENat` order
  -- `↑n + 1`, rather than the definitionally different `↑(n + 1) + 1`.
  -- Register that exact manifold order for the neighborhood characterization.
  letI : IsManifold I ((n : ℕ∞ω) + 1) M :=
    IsManifold.of_le (n := ∞) (by
      exact_mod_cast (le_top : (n + 1 : ℕ∞) ≤ ⊤))
  letI : IsManifold I (minSmoothness ℝ (2 : ℕ∞)) M :=
    IsManifold.of_le (n := ∞) (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  letI : IsContMDiffRiemannianBundle I ((n : ℕ∞ω) + 1) E TM :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by
      exact WithTop.coe_le_coe.mpr (show ((n : ℕ∞) + 1) ≤ ⊤ from le_top))
  letI : IsContMDiffRiemannianBundle I (n : ℕ∞ω) E TM :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by
      exact WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))
  letI : ContMDiffVectorBundle (n : ℕ∞ω) E TM I :=
    ContMDiffVectorBundle.of_le (n := ∞) (by
      exact WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))
  letI : ContMDiffVectorBundle ((n : ℕ∞ω) + 1) E TM I :=
    ContMDiffVectorBundle.of_le (n := ∞) (by
      exact WithTop.coe_le_coe.mpr (show ((n : ℕ∞) + 1) ≤ ⊤ from le_top))
  have hiHigh {U V : Π y, TM y}
      (hU : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((n : ℕ∞ω) + 1) (T% U) x)
      (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((n : ℕ∞ω) + 1) (T% V) x) :
      ContMDiffAt I 𝓘(ℝ, ℝ) ((n : ℕ∞ω) + 1)
        (fun y ↦ inner ℝ (U y) (V y)) x :=
    @ContMDiffAt.inner_bundle E _ _ H _ I ((n : ℕ∞ω) + 1) M _ _ E _ _ TM _
      (fun y ↦ inferInstance) (fun y ↦ inferInstance) _ _ E _ _ H _ I M _ _ _
      (fun y ↦ y) U V x hU hV
  have hiLow {U V : Π y, TM y}
      (hU : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n : ℕ∞ω) (T% U) x)
      (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n : ℕ∞ω) (T% V) x) :
      ContMDiffAt I 𝓘(ℝ, ℝ) (n : ℕ∞ω)
        (fun y ↦ inner ℝ (U y) (V y)) x :=
    @ContMDiffAt.inner_bundle E _ _ H _ I (n : ℕ∞ω) M _ _ E _ _ TM _
      (fun y ↦ inferInstance) (fun y ↦ inferInstance) _ _ E _ _ H _ I M _ _ _
      (fun y ↦ y) U V x hU hV
  have hd {f : M → ℝ} {V : Π y, TM y}
      (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ((n : ℕ∞ω) + 1) f x)
      (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((n : ℕ∞ω) + 1) (T% V) x) :
      ContMDiffAt I 𝓘(ℝ, ℝ) (n : ℕ∞ω)
        (fun y ↦ mvfderiv I f y (V y)) x := by
    have h := ContMDiffAt.clm_bundle_apply (F₁ := E) (E₁ := TM)
      (F₂ := ℝ) (E₂ := fun _ : M ↦ ℝ)
      (contMDiffAt_differential n hf)
      (hV.of_le (by
        exact_mod_cast (Nat.le_succ n) :
          (n : ℕ∞ω) ≤ (n : ℕ∞ω) + 1))
    exact ((contMDiffAt_totalSpace).mp h).2
  have hb (U V : Π y, TM y)
      (hU : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((n : ℕ∞ω) + 1) (T% U) x)
      (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((n : ℕ∞ω) + 1) (T% V) x) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n : ℕ∞ω) (T% (mlieBracket I U V)) x :=
    hU.mlieBracket_vectorField hV (m := n) (n := n + 1) (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (n + 1 : ℕ∞) ≤ n + 1 from le_rfl))
  have hr := (((((hd (hiHigh hY hZ) hX).add (hd (hiHigh hX hZ) hY)).sub
    (hd (hiHigh hX hY) hZ)).sub
    (hiLow (hX.of_le (by
      exact_mod_cast (Nat.le_succ n) : (n : ℕ∞ω) ≤ (n : ℕ∞ω) + 1))
      (hb Y Z hY hZ))).add
    (hiLow (hY.of_le (by
      exact_mod_cast (Nat.le_succ n) : (n : ℕ∞ω) ≤ (n : ℕ∞ω) + 1))
      (hb Z X hZ hX))).add
    (hiLow (hZ.of_le (by
      exact_mod_cast (Nat.le_succ n) : (n : ℕ∞ω) ≤ (n : ℕ∞ω) + 1))
      (hb X Y hX hY))
  apply (((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).contMDiff.contMDiffAt.comp x hr).congr_of_eventuallyEq
  filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hX,
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hY,
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hZ] with y hXy hYy hZy
  have he := koszul_formula cov hm ht X Y Z y
    (hXy.mdifferentiableAt (by norm_num)) (hYy.mdifferentiableAt (by norm_num))
    (hZy.mdifferentiableAt (by norm_num))
  change inner ℝ (cov Y y (X y)) (Z y) = (1 / 2 : ℝ) *
    (mvfderiv I (fun z ↦ inner ℝ (Y z) (Z z)) y (X y) +
      mvfderiv I (fun z ↦ inner ℝ (X z) (Z z)) y (Y y) -
      mvfderiv I (fun z ↦ inner ℝ (X z) (Y z)) y (Z y) -
      inner ℝ (X y) (mlieBracket I Y Z y) +
      inner ℝ (Y y) (mlieBracket I Z X y) + inner ℝ (Z y) (mlieBracket I X Y y))
  linarith

/-! ## Smooth metric-dual reconstruction -/

theorem contMDiffAt_chartScalarCoordinate_of_order
    (n : ℕ) {ι : Type*} (b : Module.Basis ι ℝ E) (c x : M)
    (hx : x ∈ (chartAt H c).source) (i : ι) :
    ContMDiffAt I 𝓘(ℝ, ℝ) (n + 1)
      (chartScalarCoordinate (I := I) b c i) x := by
  letI : IsManifold I ((n : ℕ∞ω) + 1) M :=
    IsManifold.of_le (n := ∞) (by
      exact_mod_cast (le_top : (n + 1 : ℕ∞) ≤ ⊤))
  exact (b.coord i).toContinuousLinearMap.contMDiff.contMDiffAt.comp x
    (contMDiffAt_extChartAt' (n := (n : ℕ∞ω) + 1) hx)

theorem contMDiffAt_metricDualFrame_of_order
    (n : ℕ) {ι : Type*} (b : Module.Basis ι ℝ E) (c x : M)
    (hx : x ∈ (chartAt H c).source) (i : ι) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (T% (metricDualFrame (I := I) b c i)) x := by
  exact contMDiffAt_gradient (I := I) n
    (contMDiffAt_chartScalarCoordinate_of_order (I := I) n b c x hx i)

theorem contMDiffAt_section_of_inner_localFrame_of_order
    (n : ℕ) {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℝ E) (c x : M) (hx : x ∈ (chartAt H c).source)
    (W : Π y, TM y)
    (hW : ∀ i, ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun y ↦ inner ℝ (W y) ((trivializationAt E TM c).localFrame b i y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (T% W) x := by
  have hs : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (T% (fun y ↦ ∑ i, inner ℝ (W y) ((trivializationAt E TM c).localFrame b i y) •
        metricDualFrame (I := I) b c i y)) x :=
    ContMDiffAt.sum_section (fun i _ ↦
      (hW i).smul_section (contMDiffAt_metricDualFrame_of_order (I := I) n b c x hx i))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(chartAt H c).open_source.mem_nhds hx] with y hy
  exact congrArg (TotalSpace.mk' E y)
    (eq_sum_inner_localFrame_smul_metricDualFrame b c y hy (W y))

/-! ## Arbitrary finite regularity of a metric-compatible torsion-free derivative -/

theorem contMDiffAt_covariantAlong_of_metric_torsion_of_order
    (n : ℕ) (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) {X Y : Π y, TM y} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 1) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 1) (T% Y) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (T% (fun y ↦ cov Y y (X y))) x := by
  let b := Module.finBasis ℝ E
  apply contMDiffAt_section_of_inner_localFrame_of_order (I := I) n b x x
    (mem_chart_source H x)
  intro i
  exact contMDiffAt_koszul_pairing_of_order (I := I) n cov hm ht hX hY
    (contMDiffAt_localFrame_of_mem (n + 1) (trivializationAt E TM x) b i
      (mem_baseSet_trivializationAt E TM x))

theorem contMDiffAt_covariantDerivative_of_metric_torsion_of_order
    (n : ℕ) (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) {Y : Π y, TM y} {x : M}
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 1) (T% Y) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z ↦ TM z →L[ℝ] TM z) y (cov Y y)) x := by
  classical
  let b := Module.finBasis ℝ E
  let e := trivializationAt E TM x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E TM x
  let W (i : Fin (Module.finrank ℝ E)) (y : M) :=
    cov Y y (e.localFrame b i y)
  have hW (i) : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (T% (W i)) x :=
    contMDiffAt_covariantAlong_of_metric_torsion_of_order (I := I) n cov hm ht
      (contMDiffAt_localFrame_of_mem (n + 1) e b i hx) hY
  have hC (i) := (e.contMDiffAt_section_iff hx).mp (hW i)
  have hsum : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) n
      (fun y ↦ ∑ i, ContinuousLinearMap.smulRightL ℝ E E (b.coord i).toContinuousLinearMap
        ((e ⟨y, W i y⟩).2)) x :=
    ContMDiffAt.sum (fun i _ ↦
      (ContinuousLinearMap.smulRightL ℝ E E (b.coord i).toContinuousLinearMap).contMDiff.contMDiffAt.comp x (hC i))
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, hsum.congr_of_eventuallyEq ?_⟩
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  apply ContinuousLinearMap.coe_injective
  apply b.ext
  intro j
  change ContinuousLinearMap.inCoordinates E TM E TM x y x y (cov Y y) (b j) =
    (∑ i, ContinuousLinearMap.smulRightL ℝ E E (b.coord i).toContinuousLinearMap
      ((e ⟨y, W i y⟩).2)) (b j)
  simp only [sum_apply, ContinuousLinearMap.smulRightL_apply_apply]
  change _ = ∑ i, b.coord i (b j) • (e ⟨y, W i y⟩).2
  simp [Module.Basis.coord_apply, Finsupp.single_apply]
  rw [ContinuousLinearMap.inCoordinates_eq hy hy]
  simp [W, e, localFrame_eq_symmL, ContinuousLinearMap.comp_apply,
    e.symmL_apply (R := ℝ) hy]

theorem contMDiffCovariantDerivative_of_metric_torsion_of_order
    (n : ℕ) (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) : cov.ContMDiffCovariantDerivative n := by
  refine ⟨⟨?_⟩⟩
  intro Y hY
  apply ContMDiff.contMDiffOn
  intro x
  exact contMDiffAt_covariantDerivative_of_metric_torsion_of_order (I := I) n cov hm ht
    (contMDiffOn_univ.mp hY x)

instance leviCivitaConnection_contMDiffCovariantDerivative_infty :
    (leviCivitaConnection (I := I) (M := M)).ContMDiffCovariantDerivative ∞ := by
  refine ⟨⟨?_⟩⟩
  intro Y hY
  apply ContMDiff.contMDiffOn
  intro x
  rw [contMDiffAt_infty]
  intro n
  exact contMDiffAt_covariantDerivative_of_metric_torsion_of_order (I := I) n
    (leviCivitaConnection (I := I) (M := M))
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion
    ((contMDiffOn_univ.mp hY x).of_le (by
      exact_mod_cast (show (n + 1 : ℕ∞) ≤ ⊤ from le_top)))

end AlmostSchur
