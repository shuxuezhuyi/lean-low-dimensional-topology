module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicLength
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeHyperbolicBounds
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegion.CollarWidth
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Crossing original closed geodesics and their actual lengths

An intersection on the original surface gives intersecting lifted axes after
an actual deck conjugation of one full-period covering matrix. The resulting
translation bound transports to the full original rectifiable period lengths,
including every proper-power traversal.
-/

public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Fuchsian

/-- Distinct intersecting original geodesic images give the sharp product
bound for their actual full-period hyperbolic covering matrices. -/
theorem OriginalClosedGeodesic.crossing_translation_product_of_covers
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q r : OriginalClosedGeodesic M)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAΓ : A ∈ Γ) (hBΓ : B ∈ Γ)
    (htA : 4 < (Matrix.trace A.val) ^ 2) (htB : 4 < (Matrix.trace B.val) ^ 2)
    (hcovA : LiZhongQC.Covers M.halfPlaneCover A q.toLoop)
    (hcovB : LiZhongQC.Covers M.halfPlaneCover B r.toLoop)
    (hneq : range q.curve ≠ range r.curve)
    (hcross : ¬ Disjoint (range q.curve) (range r.curve)) :
    1 ≤ Real.sinh (hTranslationLength (hSLIsometry A) / 2) *
      Real.sinh (hTranslationLength (hSLIsometry B) / 2) := by
  let := R.toRiemannAtlas.toChartedSpace
  have hA : realSLMobius A ≠ 1 := by
    intro he
    have hh := hSL_trace_sq_of_projection_one A he
    linarith
  have hB : realSLMobius B ≠ 1 := by
    intro he
    have hh := hSL_trace_sq_of_projection_one B he
    linarith
  have hq := q.trace_eq_axis_image_of_covers hp A hAΓ hA htA hcovA
  have hr := r.trace_eq_axis_image_of_covers hp B hBΓ hB htB hcovB
  obtain ⟨x, hxq, hxr⟩ := Set.not_disjoint_iff.mp hcross
  rw [hq] at hxq
  rw [hr] at hxr
  obtain ⟨u, hu, hpu⟩ := hxq
  obtain ⟨v, hv, hpv⟩ := hxr
  obtain ⟨C, hC, hCu⟩ := (hp.2.2.2 u v).mp (hpu.trans hpv.symm)
  let D := C * A * C⁻¹
  have hDΓ : D ∈ Γ := Γ.mul_mem (Γ.mul_mem hC hAΓ) (Γ.inv_mem hC)
  have hD : realSLMobius D ≠ 1 := hSL_nontrivial_conjugation A C hA
  have htD : 4 < (Matrix.trace D.val) ^ 2 := by
    dsimp only [D]
    rwa [hSL_trace_conjugation]
  have haxisD : (hHyperbolicAxis D hD htD).carrier =
      (fun z : ℍ => C • z) '' (hHyperbolicAxis A hA htA).carrier := by
    rw [hHyperbolicAxis_conjugation A C hA htA, HalfPlaneLine.realGLMap_carrier]
    rfl
  have hvD : v ∈ (hHyperbolicAxis D hD htD).carrier := by
    rw [haxisD]
    exact ⟨u, hu, hCu⟩
  have hprojectD : M.halfPlaneCover '' (hHyperbolicAxis D hD htD).carrier =
      M.halfPlaneCover '' (hHyperbolicAxis A hA htA).carrier := by
    rw [haxisD, ← Set.image_comp]
    have he : M.halfPlaneCover ∘ (fun z : ℍ => C • z) = M.halfPlaneCover := by
      funext z
      exact LiZhongQC.s30a_p_smul hp hC z
    rw [he]
  have haxes : hHyperbolicAxis D hD htD ≠ hHyperbolicAxis B hB htB := by
    intro he
    apply hneq
    calc
      range q.curve = M.halfPlaneCover '' (hHyperbolicAxis A hA htA).carrier := hq
      _ = M.halfPlaneCover '' (hHyperbolicAxis D hD htD).carrier := hprojectD.symm
      _ = M.halfPlaneCover '' (hHyperbolicAxis B hB htB).carrier := by rw [he]
      _ = range r.curve := hr.symm
  have hG : IsEllipticFree (Γ.map realSLMobius) := by
    intro f hf
    obtain ⟨E, hEΓ, hEf⟩ := Subgroup.mem_map.mp f.property
    have hEll : MobiusElliptic (realSLMobius E) := by
      rw [hEf]
      exact hf
    have htr := (realSLMobius_elliptic_iff E hEll.1).mp hEll
    have hsmall : |E 0 0 + E 1 1| < 2 := by
      apply abs_lt_of_sq_lt_sq ?_ (by norm_num)
      simpa only [Matrix.trace_fin_two, show (2 : ℝ) ^ 2 = 4 by norm_num] using htr
    obtain ⟨τ, hτ⟩ := LiZhongQC.s27g_elliptic_fixed hsmall
    rcases LiZhongQC.s27g_actsFreely hp E hEΓ τ hτ with he | he
    · rw [he] at htr
      norm_num [Matrix.trace_fin_two] at htr
    · rw [he] at htr
      norm_num [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_fin_two] at htr
  have hDm : realSLMobius D ∈ Γ.map realSLMobius :=
    Subgroup.mem_map.mpr ⟨D, hDΓ, rfl⟩
  have hBm : realSLMobius B ∈ Γ.map realSLMobius :=
    Subgroup.mem_map.mpr ⟨B, hBΓ, rfl⟩
  have hprod := hEllipticFree_hyperbolic_crossing_translation_product
    (Γ.map realSLMobius) hG D B hDm hBm hD hB htD htB v hvD hv haxes
  simpa only [D, hSL_translationLength_conjugation] using hprod

/-- The same crossing bound uses the full original rectifiable period lengths,
with the given covering matrices retaining all traversal multiplicities. -/
theorem OriginalClosedGeodesic.crossing_length_product_of_covers
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q r : OriginalClosedGeodesic M)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAΓ : A ∈ Γ) (hBΓ : B ∈ Γ)
    (htA : 4 < (Matrix.trace A.val) ^ 2) (htB : 4 < (Matrix.trace B.val) ^ 2)
    (hcovA : LiZhongQC.Covers M.halfPlaneCover A q.toLoop)
    (hcovB : LiZhongQC.Covers M.halfPlaneCover B r.toLoop)
    (hneq : range q.curve ≠ range r.curve)
    (hcross : ¬ Disjoint (range q.curve) (range r.curve)) :
    1 ≤ Real.sinh (q.length.toReal / 2) * Real.sinh (r.length.toReal / 2) := by
  have hA : realSLMobius A ≠ 1 := by
    intro he
    have hh := hSL_trace_sq_of_projection_one A he
    linarith
  have hB : realSLMobius B ≠ 1 := by
    intro he
    have hh := hSL_trace_sq_of_projection_one B he
    linarith
  have hTA := hHyperbolic_translationLength_pos A hA htA
  have hTB := hHyperbolic_translationLength_pos B hB htB
  rw [q.length_eq_translationLength_of_covers hp A hAΓ htA hcovA,
    r.length_eq_translationLength_of_covers hp B hBΓ htB hcovB,
    ENNReal.toReal_ofReal hTA.le, ENNReal.toReal_ofReal hTB.le]
  exact q.crossing_translation_product_of_covers r hp A B hAΓ hBΓ htA htB
    hcovA hcovB hneq hcross

/-- Distinct intersecting original geodesics obey the product bound for their
full period lengths. Both actual matrices are constructed in one covering group. -/
theorem OriginalClosedGeodesic.crossing_length_product
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q r : OriginalClosedGeodesic M)
    (hneq : range q.curve ≠ range r.curve)
    (hcross : ¬ Disjoint (range q.curve) (range r.curve)) :
    1 ≤ Real.sinh (q.length.toReal / 2) * Real.sinh (r.length.toReal / 2) := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨A, hAΓ, hcovA, _hA, htA⟩ := q.exists_actual_hyperbolic_cover hp
  obtain ⟨B, hBΓ, hcovB, _hB, htB⟩ := r.exists_actual_hyperbolic_cover hp
  exact q.crossing_length_product_of_covers r hp A B hAΓ hBΓ htA htB
    hcovA hcovB hneq hcross

/-- A short full original period forces equality of the geometric images or
disjointness. The lengths retain every traversal in the given periods. -/
theorem OriginalClosedGeodesic.trace_eq_or_disjoint_of_length_lt_collar
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q r : OriginalClosedGeodesic M)
    (hshort : r.length.toReal < 2 * collarHalfWidth q.length.toReal) :
    range q.curve = range r.curve ∨ Disjoint (range q.curve) (range r.curve) := by
  by_cases heq : range q.curve = range r.curve
  · exact Or.inl heq
  · refine Or.inr ?_
    by_contra hcross
    have hprod := q.crossing_length_product r heq hcross
    have hstrip := (lt_collarHalfWidth_iff q.length_toReal_pos
      (r.length.toReal / 2)).mp (by linarith)
    exact (not_le_of_gt hstrip) (by simpa only [mul_comm] using hprod)

end LowDimensionalTopology.Geometry.Surfaces
