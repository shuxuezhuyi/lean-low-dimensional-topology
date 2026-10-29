module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.IntrinsicLocallyMinimizingArcs
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ClosedGeodesicExistence
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.EquivariantArcTrace

/-!
# Geometric uniqueness of original rectifiable closed geodesics

Closed geodesics use the original atlas, full rectifiable local minimum,
actual local arc injectivity and an ordinary periodic real parametrization.
No global geodesic lift or axis belongs to the structure. The actual covering
matrix is derived from the nontrivial original loop; actual free homotopy
aligns both constructed lifts to that same matrix. Their geometric images
therefore equal the same projected axis, including proper-power classes.
No original parametrization is required to have unit speed or to be AC.
-/

public section
noncomputable section
open Set
open scoped UpperHalfPlane unitInterval MatrixGroups

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- An actual rectifiable closed geodesic in the original surface. Period one
only fixes the domain convention; smaller subperiods and proper powers remain
allowed. Local minimality compares every original-atlas rectifiable curve. -/
structure OriginalClosedGeodesic
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) where
  curve : ℝ → X
  locallyMinimizing : IsOriginalLocallyMinimizingArc M curve
  periodic : Function.Periodic curve 1

theorem OriginalClosedGeodesic.continuous
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) : Continuous q.curve := by
  obtain ⟨hc, _hloc⟩ := q.locallyMinimizing
  exact hc

/-- The actual original loop traversed during one whole given period. -/
@[expose] def OriginalClosedGeodesic.toLoop
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) : LiZhongQC.Loop X :=
  ⟨q.curve 0,
    { toContinuousMap := ⟨fun t => q.curve (t : ℝ), q.continuous.comp continuous_subtype_val⟩
      source' := rfl
      target' := by simpa only [Set.Icc.coe_one, zero_add] using q.periodic 0 }⟩

private theorem local_injectivity_of_projected_arc
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    (f : ℝ → ℍ) (hproj : ∀ t : ℝ, M.halfPlaneCover (f t) = q.curve t) :
    IsLocallyInjective f := by
  obtain ⟨_hc, hlocal⟩ := q.locallyMinimizing
  intro x
  obtain ⟨_U, a, b, _hUopen, _hxU, hax, hxb, _hU, hinj, _hmin⟩ := hlocal x
  refine ⟨Ioo a b, isOpen_Ioo, ⟨hax, hxb⟩, ?_⟩
  intro s hs t ht he
  apply hinj hs ht
  exact (hproj s).symm.trans ((congrArg M.halfPlaneCover he).trans (hproj t))

private theorem projected_arc_trace_eq_source_axis
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R)
    [ChartedSpace ℂ X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAΓ : A ∈ Γ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (α : LiZhongQC.Loop X) (hcov : LiZhongQC.Covers M.halfPlaneCover A α)
    (q : OriginalClosedGeodesic M) (hfree : LiZhongQC.FreelyHomotopic α q.toLoop) :
    range q.curve = M.halfPlaneCover '' (hHyperbolicAxis A hA ht).carrier := by
  obtain ⟨f, S, hproj, hS, hfS⟩ := q.locallyMinimizing.exists_hLine_lift
  have hfinj := local_injectivity_of_projected_arc q f hproj
  let d : C(I, ℍ) := ⟨fun t => f (t : ℝ), f.continuous.comp continuous_subtype_val⟩
  have hd (t : I) : M.halfPlaneCover (d t) = q.toLoop.2 t := hproj t
  obtain ⟨C, hC, hend⟩ := LiZhongQC.s30a_fh_fwd hp hAΓ hcov hfree d hd
  change f 1 = (C * A * C⁻¹) • f 0 at hend
  let η : ℝ → ℍ := fun t => C⁻¹ • f t
  have hηcont : Continuous η := (continuous_const_smul C⁻¹).comp f.continuous
  have hηproj (t : ℝ) : M.halfPlaneCover (η t) = q.curve t := by
    change M.halfPlaneCover (C⁻¹ • f t) = q.curve t
    rw [LiZhongQC.s30a_p_smul hp (Γ.inv_mem hC), hproj]
  have hηend : η 1 = A • η 0 := by
    change C⁻¹ • f 1 = A • (C⁻¹ • f 0)
    rw [hend]
    simp only [mul_smul, inv_smul_smul]
  have hperiod : ∀ t : ℝ, η (t + 1) = A • η t := by
    have hwhole : (fun t : ℝ => η (t + 1)) = (fun t => A • η t) := by
      apply hp.1.eq_of_comp_eq
        (hηcont.comp (continuous_id.add continuous_const))
        ((continuous_const_smul A).comp hηcont) ?_ 0 ?_
      · funext t
        change M.halfPlaneCover (η (t + 1)) = M.halfPlaneCover (A • η t)
        rw [hηproj, LiZhongQC.s30a_p_smul hp hAΓ, hηproj, q.periodic t]
      · change η (0 + 1) = A • η 0
        simpa only [zero_add] using hηend
    exact fun t => congrFun hwhole t
  have hηinj : IsLocallyInjective η := by
    intro x
    obtain ⟨U, hUopen, hxU, hUinj⟩ := hfinj x
    refine ⟨U, hUopen, hxU, ?_⟩
    intro s hs t ht' he
    apply hUinj hs ht'
    exact (isometry_smul ℍ C⁻¹).injective he
  obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_isHLine hS
  obtain ⟨N, hN⟩ := LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine
    (show Isometry (fun z : ℍ => C⁻¹ • z) from isometry_smul ℍ C⁻¹) L
  have hηN : range η ⊆ N.carrier := by
    rintro _ ⟨t, rfl⟩
    rw [← hN]
    exact ⟨f t, hL.symm ▸ hfS (mem_range_self t), rfl⟩
  have htrace := equivariant_arc_projected_trace_eq_axis hp A hAΓ hA ht
    hηcont hηinj N.isHLine hηN 1 hperiod
  have heq : M.halfPlaneCover ∘ η = q.curve := funext hηproj
  simpa only [heq] using htrace

/-- The actual image of an original closed geodesic is the projection of the
axis of its given hyperbolic full-period covering matrix. -/
theorem OriginalClosedGeodesic.trace_eq_axis_image_of_covers
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAΓ : A ∈ Γ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (hcov : LiZhongQC.Covers M.halfPlaneCover A q.toLoop) :
    range q.curve = M.halfPlaneCover '' (hHyperbolicAxis A hA ht).carrier := by
  let := R.toRiemannAtlas.toChartedSpace
  exact projected_arc_trace_eq_source_axis M hp A hAΓ hA ht
    q.toLoop hcov q (LiZhongQC.s30b_fh_of_eq (fun _ => rfl))

/-- Two genuine original-atlas rectifiable closed geodesics in the same
nontrivial free homotopy class have the same geometric image. All covering,
axis and parameter-regularity facts are derived, and the actual source loop
retains proper-power multiplicities in its covering matrix. -/
theorem OriginalClosedGeodesic.trace_eq_of_freelyHomotopic
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (α β : OriginalClosedGeodesic M)
    (hnon : ¬ IsNullHomotopicLoop α.toLoop)
    (hfree : LiZhongQC.FreelyHomotopic α.toLoop β.toLoop) :
    range α.curve = range β.curve := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨A, hAΓ, hcov, _hhyper, hA, ht⟩ :=
    exists_hyperbolic_cover_of_not_null hp α.toLoop hnon
  have hα := projected_arc_trace_eq_source_axis M hp A hAΓ hA ht α.toLoop hcov α
    (LiZhongQC.s30b_fh_of_eq (fun _ => rfl))
  have hβ := projected_arc_trace_eq_source_axis M hp A hAΓ hA ht α.toLoop hcov β hfree
  exact hα.trans hβ.symm

end LowDimensionalTopology.Geometry.Surfaces
