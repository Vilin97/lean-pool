/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.MetricDualFrameTwo
public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.KoszulFormula

/-! # C² connection regularity from differentiated Koszul pairings

The proof does not require regularity of the pointwise seed chart choice.
It reconstructs the derivative from its scalar metric pairings.
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
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _ ) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  -- C³ metric data supplies the differentiated Koszul coefficients.
  [IsContMDiffRiemannianBundle I 3 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)

/-- Koszul pairings are C² for C³ fields and a C³ metric. -/
theorem contMDiffAt_koszul_pairing_two (cov : CovariantDerivative I E TM)
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {X Y Z : Π y, TM y} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ inner ℝ (cov Y y (X y)) (Z y)) x := by
  letI : IsManifold I (minSmoothness ℝ (3 : ℕ∞)) M :=
    IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
  letI : IsManifold I ((3 : ℕ∞) + 1) M :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast (le_top : (3 + 1 : ℕ∞) ≤ ⊤))
  have hi {n : ℕ∞ω} [IsContMDiffRiemannianBundle I n E TM]
      {U V : Π y, TM y}
      (hU : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (T% U) x)
      (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (T% V) x) :
      ContMDiffAt I 𝓘(ℝ, ℝ) n (fun y ↦ inner ℝ (U y) (V y)) x :=
    @ContMDiffAt.inner_bundle E _ _ H _ I n M _ _ E _ _ TM _
      (fun y ↦ inferInstance) (fun y ↦ inferInstance) _ _ E _ _ H _ I M _ _ _
      (fun y ↦ y) U V x hU hV
  have hd {f : M → ℝ} {V : Π y, TM y}
      (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 3 f x)
      (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% V) x) :
      ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y ↦ mvfderiv I f y (V y)) x := by
    have h := ContMDiffAt.clm_bundle_apply (F₁ := E) (E₁ := TM)
      (F₂ := ℝ) (E₂ := fun _ : M ↦ ℝ) (contMDiffAt_differential 2 hf)
      (hV.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3))
    exact ((contMDiffAt_totalSpace).mp h).2
  have hb (U V : Π y, TM y)
      (hU : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% U) x)
      (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% V) x) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% (mlieBracket I U V)) x :=
    hU.mlieBracket_vectorField hV (m := 2) (n := 3) (by norm_num)
  have hr := (((((hd (hi hY hZ) hX).add (hd (hi hX hZ) hY)).sub
    (hd (hi hX hY) hZ)).sub
    (hi (hX.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)) (hb Y Z hY hZ))).add
    (hi (hY.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)) (hb Z X hZ hX))).add
    (hi (hZ.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)) (hb X Y hX hY))
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

/-- The covariant derivative along a C³ field is locally C². -/
theorem contMDiffAt_covariantAlong_of_metric_torsion_two
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) {X Y : Π y, TM y} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% (fun y ↦ cov Y y (X y))) x := by
  let b := Module.finBasis ℝ E
  apply contMDiffAt_section_of_inner_localFrame_two b x x (mem_chart_source H x)
  intro i
  exact contMDiffAt_koszul_pairing_two cov hm ht hX hY
    (contMDiffAt_localFrame_of_mem 3 (trivializationAt E TM x) b i
      (mem_baseSet_trivializationAt E TM x))

/-- Scalar-frame reconstruction gives regularity of the full hom-bundle section. -/
theorem contMDiffAt_covariantDerivative_of_metric_torsion_two
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) {Y : Π y, TM y} {x : M}
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := fun z ↦ TM z →L[ℝ] TM z) y (cov Y y)) x := by
  classical
  let b := Module.finBasis ℝ E
  let e := trivializationAt E TM x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E TM x
  let W (i : Fin (Module.finrank ℝ E)) (y : M) := cov Y y (e.localFrame b i y)
  have hW (i) : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% (W i)) x :=
    contMDiffAt_covariantAlong_of_metric_torsion_two cov hm ht
      (contMDiffAt_localFrame_of_mem 3 e b i hx) hY
  have hC (i) := (e.contMDiffAt_section_iff hx).mp (hW i)
  have hsum : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) 2
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

/-- Every metric-compatible torsion-free derivative is C² for a C³ metric. -/
theorem contMDiffCovariantDerivative_of_metric_torsion_two
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) : cov.ContMDiffCovariantDerivative 2 := by
  refine ⟨⟨?_⟩⟩
  intro Y hY
  apply ContMDiff.contMDiffOn
  intro x
  exact contMDiffAt_covariantDerivative_of_metric_torsion_two cov hm ht
    (contMDiffOn_univ.mp hY x)

/-- Regularity of the explicitly constructed Levi–Civita connection. -/
instance leviCivitaConnection_contMDiffCovariantDerivative_two :
    (leviCivitaConnection (I := I) (M := M)).ContMDiffCovariantDerivative 2 :=
  contMDiffCovariantDerivative_of_metric_torsion_two _
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion

end AlmostSchur
