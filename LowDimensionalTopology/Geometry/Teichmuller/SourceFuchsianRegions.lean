module

public import LowDimensionalTopology.Geometry.Fuchsian.Action.SourceHalfPlaneGroup
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.NativeGeometricCovolume
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.HalfPlaneRegion
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeneralizedFundamentalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S22_RiemannSurfaces
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedNativeTarget

/-!
# Genuine native half-plane regions for the original source groups

The source compact-hit condition descends through the actual special-linear
projection. Its ineffective signs both give the identity Mobius map. Hence
source freeness yields a genuine free center, and the existing geometric
Dirichlet construction supplies an open fundamental region for this same
whole group, in the actual half-plane coordinate and planar boundary measure.
-/

public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open DiscreteGroups Fuchsian Hyperbolic Mobius

local instance sourceRegionSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex :=
  borel Mobius.ExtendedComplex
local instance sourceRegionSphereBorel : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- The original compact-hit condition descends to the actual Mobius image,
without selecting any homomorphic special-linear lift of that image. -/
theorem sourceFuchsian_image_discontinuous (hΓ : LiZhongQC.IsFuchsian Γ) :
    IsMobiusDiscontinuousOn (Γ.map realSLMobius) openHalfPlaneSet := by
  exact Fuchsian.sourceFuchsian_image_discontinuous hΓ

/-- The original Fuchsian condition supplies the actual native half-plane
structure on its exact entire projective image. -/
theorem sourceHalfPlaneFuchsianGroup (hΓ : LiZhongQC.IsFuchsian Γ) :
    HalfPlaneFuchsianGroup (Γ.map realSLMobius) where
  preserves := (Fuchsian.sourceHalfPlaneFuchsianGroup hΓ).preserves
  discrete := (Fuchsian.sourceHalfPlaneFuchsianGroup hΓ).discrete

/-- Source freeness modulo the two ineffective signs is genuine freeness of
the exact native Mobius image action. -/
theorem sourceHalfPlaneFuchsianGroup_free (hΓ : LiZhongQC.IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) (g : Γ.map realSLMobius) (z : ℍ) :
    letI := (sourceHalfPlaneFuchsianGroup hΓ).nativeAction
    g • z = z → g = 1 := by
  let P := sourceHalfPlaneFuchsianGroup hΓ
  let := P.nativeAction
  intro hgz
  obtain ⟨A, hA, hAg⟩ := Subgroup.mem_map.mp g.property
  have hAz : A • z = z := (P.nativeAction_realSL g A hAg z).symm.trans hgz
  apply Subtype.ext
  rcases hfree A hA z hAz with h | h
  · rw [← hAg, h, map_one]
    rfl
  · rw [← hAg, h, realSLMobius_neg, map_one]
    rfl

/-- The existing genuine geometric Dirichlet construction gives an open
fundamental region in the same native coordinate, with planar-null frontier. -/
theorem exists_sourceHalfPlaneFundamentalRegion (hΓ : LiZhongQC.IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) :
    ∃ F : Set ℍ, IsHalfPlaneFundamentalRegion (sourceHalfPlaneFuchsianGroup hΓ) F := by
  let P := sourceHalfPlaneFuchsianGroup hΓ
  let := P.nativeAction
  let w := (halfPlaneGeometricChart P).symm UpperHalfPlane.I
  have hw : ∀ g : Γ.map realSLMobius, g • w.val = w.val → g = 1 := by
    intro g hg
    apply sourceHalfPlaneFuchsianGroup_free hΓ hfree g (halfPlaneGeometricChart P w)
    have hgw : g • w = w := Subtype.ext hg
    exact (halfPlaneGeometricChart_equivariant P g w).symm.trans
      (congrArg (halfPlaneGeometricChart P) hgw)
  let S := geometricPolygonDomain P.asFuchsianDisc w.val hw
  have hS : DiscreteGroups.Action.IsFundamentalDomain (Γ.map realSLMobius)
      (fuchsianGeometricDomain P.asFuchsianDisc).carrier (geometricModelArea P.asFuchsianDisc) S :=
    geometricPolygonDomain_interior_fundamental P.asFuchsianDisc w hw
  refine ⟨halfPlaneGeometricChart P '' S, ?_⟩
  exact P.isHalfPlaneFundamentalRegion_of_native _
    (halfPlaneGeometricChart_fundamental_image P S hS)

/-- Both the native group and its actual open-region data are supplied from
the original source hypotheses, with no independent geometric-data premise. -/
theorem exists_nativeHalfPlaneFundamentalRegion (hΓ : LiZhongQC.IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) :
    ∃ (P : HalfPlaneFuchsianGroup (Γ.map realSLMobius)) (F : Set ℍ),
      IsHalfPlaneFundamentalRegion P F := by
  obtain ⟨F, hF⟩ := exists_sourceHalfPlaneFundamentalRegion hΓ hfree
  exact ⟨sourceHalfPlaneFuchsianGroup hΓ, F, hF⟩

/-- In particular, every original coefficient has genuine region data for
its exact normalized deformed group. Freeness comes from that actual cover. -/
theorem exists_deformedHalfPlaneFundamentalRegion
    {X : Type*} [TopologicalSpace X] (R : Surfaces.ClosedRiemannSurface X)
    {g : ℕ} (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (ν : GammaMeasurableBeltrami.Ball Γ) :
    ∃ (P : HalfPlaneFuchsianGroup
        ((NormalizedCoefficientTransport.deformedGroup hΓ ν).map realSLMobius))
      (F : Set ℍ), IsHalfPlaneFundamentalRegion P F :=
  exists_nativeHalfPlaneFundamentalRegion
    (NormalizedCoefficientTransport.deformedGroup_spec hΓ ν).1
    (NormalizedCoefficientTransport.deformedNativeSurface_actsFreely R hgenus hΓ hp ν)

end LowDimensionalTopology.Geometry.Teichmuller
