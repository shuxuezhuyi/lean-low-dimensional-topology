module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.LocalExtension
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.IsometryClassification
public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HalfPlaneUniformization

/-!
# Complete lifts of locally projected unit-speed geodesics

Locality means actual equality on a neighborhood with the projection of a
complete unit-speed hyperbolic geodesic. Covering injectivity and the actual
orbit description of fibers turn each such neighborhood into a geodesic germ
of any continuous lift. The local extension theorem then gives a complete
unit-speed lift, rather than assuming one as a structure field.

This explicitly uses the covering-chart definition. Equivalence with an
intrinsic locally length-minimizing definition on the original surface is a
separate mathematical interface, not an assumption hidden in this definition.
-/

public section
noncomputable section
open Set Filter
open scoped UpperHalfPlane Topology MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A curve is locally a projected unit-speed geodesic if this holds on a
genuine parameter neighborhood of every point. No global lift is specified. -/
@[expose] def IsLocallyProjectedUnitGeodesic
    {X : Type*} [TopologicalSpace X] (p : ℍ → X) (α : ℝ → X) : Prop :=
  ∀ x : ℝ, ∃ γ : ℝ → ℍ,
    IsHGeodesicParam γ ∧ α =ᶠ[𝓝 x] (fun t => p (γ t))

private theorem isHGeodesicParam_deck_smul
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) {γ : ℝ → ℍ}
    (hγ : IsHGeodesicParam γ) : IsHGeodesicParam (fun t => A • γ t) := by
  have his : Isometry (fun z : ℍ => A • z) := isometry_smul ℍ A
  obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_isHLine hγ.2
  obtain ⟨M, hM⟩ := LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine his L
  refine ⟨his.comp hγ.1, ?_⟩
  have hrange : range (fun t => A • γ t) = M.carrier := by
    change range ((fun z : ℍ => A • z) ∘ γ) = M.carrier
    rw [range_comp, ← hL, hM]
  exact hrange.symm ▸ M.isHLine

/-- Continuity follows from the actual neighborhood geodesics. -/
theorem IsLocallyProjectedUnitGeodesic.continuous
    {X : Type*} [TopologicalSpace X] {p : ℍ → X} (hp : Continuous p)
    {α : ℝ → X} (hα : IsLocallyProjectedUnitGeodesic p α) : Continuous α := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨γ, hγ, hloc⟩ := hα x
  exact (hp.comp hγ.1.continuous).continuousAt.congr_of_eventuallyEq hloc

/-- Any actual continuous lift of a locally projected unit-speed geodesic is
a complete unit-speed hyperbolic geodesic. -/
theorem IsLocallyProjectedUnitGeodesic.isHGeodesicParam_lift
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : LiZhongQC.IsUniformization Γ p)
    {α : ℝ → X} (hα : IsLocallyProjectedUnitGeodesic p α)
    {f : ℝ → ℍ} (hf : Continuous f) (hproj : ∀ t : ℝ, p (f t) = α t) :
    IsHGeodesicParam f := by
  apply isHGeodesicParam_of_locally
  intro x
  obtain ⟨γ, hγ, hloc⟩ := hα x
  have hx : p (γ x) = p (f x) :=
    hloc.eq_of_nhds.symm.trans (hproj x).symm
  obtain ⟨A, hA, hAx⟩ := (hp.2.2.2 (γ x) (f x)).1 hx
  let η : ℝ → ℍ := fun t => A • γ t
  have hη : IsHGeodesicParam η := isHGeodesicParam_deck_smul A hγ
  have hηx : η x = f x := hAx
  obtain ⟨U, hUopen, hxU, hUinj⟩ := hp.1.isLocalHomeomorph.isLocallyInjective (f x)
  have hfU : ∀ᶠ t in 𝓝 x, f t ∈ U :=
    hf.continuousAt.eventually (hUopen.mem_nhds hxU)
  have hηU : ∀ᶠ t in 𝓝 x, η t ∈ U :=
    hη.1.continuous.continuousAt.eventually (hUopen.mem_nhds (hηx.symm ▸ hxU))
  refine ⟨η, hη, ?_⟩
  filter_upwards [hfU, hηU, hloc] with t hft hηt hlocal
  apply hUinj hft hηt
  calc
    p (f t) = α t := hproj t
    _ = p (γ t) := hlocal
    _ = p (η t) := (LiZhongQC.s30a_p_smul hp hA (γ t)).symm

/-- A locally projected unit-speed geodesic has a complete unit-speed lift;
the lift is constructed by the ordinary simply connected covering-lift API. -/
theorem IsLocallyProjectedUnitGeodesic.exists_complete_lift
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : LiZhongQC.IsUniformization Γ p)
    {α : ℝ → X} (hα : IsLocallyProjectedUnitGeodesic p α) :
    ∃ γ : ℝ → ℍ, IsHGeodesicParam γ ∧ ∀ t : ℝ, p (γ t) = α t := by
  obtain ⟨z, hz⟩ := hp.2.2.1 (α 0)
  let a : C(ℝ, X) := ⟨α, hα.continuous hp.1.continuous⟩
  obtain ⟨F, ⟨_hF0, hpF⟩, _hFu⟩ := hp.1.existsUnique_continuousMap_lifts a 0 z hz
  have hproj (t : ℝ) : p (F t) = α t := congrFun hpF t
  exact ⟨F, hα.isHGeodesicParam_lift hp F.continuous hproj, hproj⟩

/-- Every actual period of a locally projected unit-speed geodesic is the
equivariant period of its constructed complete lift for an actual deck matrix.
The whole period is retained, without choosing a primitive traversal. -/
theorem IsLocallyProjectedUnitGeodesic.exists_complete_lift_with_period
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : LiZhongQC.IsUniformization Γ p)
    {α : ℝ → X} (hα : IsLocallyProjectedUnitGeodesic p α)
    {T : ℝ} (hperiod : Function.Periodic α T) :
    ∃ (γ : ℝ → ℍ) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      IsHGeodesicParam γ ∧ (∀ t : ℝ, p (γ t) = α t) ∧ A ∈ Γ ∧
      ∀ t : ℝ, γ (t + T) = A • γ t := by
  obtain ⟨γ, hγ, hproj⟩ := hα.exists_complete_lift hp
  have hx : p (γ 0) = p (γ T) := by
    rw [hproj, hproj]
    simpa only [zero_add] using (hperiod 0).symm
  obtain ⟨A, hA, hAx⟩ := (hp.2.2.2 (γ 0) (γ T)).1 hx
  have hwhole : (fun t : ℝ => γ (t + T)) = (fun t => A • γ t) := by
    apply hp.1.eq_of_comp_eq
      (hγ.1.continuous.comp (continuous_id.add continuous_const))
      ((continuous_const_smul A).comp hγ.1.continuous) ?_ 0 ?_
    · funext t
      change p (γ (t + T)) = p (A • γ t)
      rw [hproj, LiZhongQC.s30a_p_smul hp hA, hproj, hperiod t]
    · change γ (0 + T) = A • γ 0
      simpa only [zero_add] using hAx.symm
  exact ⟨γ, A, hγ, hproj, hA, fun t => congrFun hwhole t⟩

end LowDimensionalTopology.Geometry.Hyperbolic

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- The same original surface model supplies the complete lift and actual
periodic deck matrix. No separate uniformization or global geodesic lift is
assumed by this original-surface interface. -/
theorem HyperbolicSurfaceModel.exists_complete_lift_of_locally_projected_geodesic
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) {α : ℝ → X}
    (hα : IsLocallyProjectedUnitGeodesic M.halfPlaneCover α)
    {T : ℝ} (hperiod : Function.Periodic α T) :
    ∃ (γ : ℝ → ℍ) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      IsHGeodesicParam γ ∧ (∀ t : ℝ, M.halfPlaneCover (γ t) = α t) ∧
      (∀ z : ℍ, M.halfPlaneCover (A • z) = M.halfPlaneCover z) ∧
      ∀ t : ℝ, γ (t + T) = A • γ t := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨γ, A, hγ, hproj, hA, hdeckperiod⟩ := hα.exists_complete_lift_with_period hp hperiod
  exact ⟨γ, A, hγ, hproj, (hΓ A).1 hA, hdeckperiod⟩

end LowDimensionalTopology.Geometry.Surfaces
