module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.CosetRegion
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ConvexFundamentalPolygons
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeometricFuchsianModels
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Function.Jacobian

/-! Actual coset-region fundamental domains and their original orbit selectors. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped Pointwise OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section
local instance cosetSphereMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance cosetSphereBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩






/-- The genuine inverse Klein coordinate is ordinarily differentiable at every interior point. -/
theorem coset_inverseKlein_differentiableAt {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℝ _root_.LowDimensionalTopology.Geometry.Hyperbolic.inverseKleinFormula z := by
  have hN : DifferentiableAt ℝ (fun u : ℂ => ‖u‖ ^ 2) z :=
    differentiableAt_id.norm_sq ℝ
  have hp : 1 - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
  have hR := ((differentiableAt_const (1 : ℝ)).sub hN).sqrt hp
  have hC : DifferentiableAt ℝ (fun u : ℂ =>
      ((1 / (1 + Real.sqrt (1 - ‖u‖ ^ 2)) : ℝ) : ℂ)) z := by
    have hSum : DifferentiableAt ℝ (fun u : ℂ => 1 + Real.sqrt (1 - ‖u‖ ^ 2)) z :=
      (differentiableAt_const (1 : ℝ)).add hR
    have hden : 1 + Real.sqrt (1 - ‖z‖ ^ 2) ≠ 0 := by positivity
    have hInv : DifferentiableAt ℝ (fun u : ℂ => (1 + Real.sqrt (1 - ‖u‖ ^ 2))⁻¹) z :=
      hSum.inv hden
    simp only [one_div]
    exact Complex.ofRealCLM.differentiableAt.comp z hInv
  exact hC.mul differentiableAt_id

/-- Every actual hyperbolically convex native region has null genuine density-area frontier. -/
theorem coset_discHConvex_frontier_area_zero {S : Set 𝔻} (hS :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (frontier S) = 0 := by
  have hK : Convex ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ''
    S) := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex S).mp hS
  have hsub : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' frontier S ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S) := by
    rintro _ ⟨z,hz,rfl⟩
    refine ⟨?_,?_⟩
    · have hh := mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate hz.1
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.klein_image_closure] at hh
      exact hh.1
    · intro hi
      have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ⁻¹' interior (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S) = interior S := by
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap.preimage_interior_eq_interior_preimage
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_kleinCoordinate,preimage_image_eq _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective]
      exact hz.2 (Set.ext_iff.mp he z |>.mp hi)
  have hzero : volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' frontier S) = 0 :=
    measure_mono_null hsub (hK.addHaar_frontier volume)
  have hdiff : DifferentiableOn ℝ _root_.LowDimensionalTopology.Geometry.Hyperbolic.inverseKleinFormula (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' frontier S) := by
    rintro _ ⟨z,_hz,rfl⟩
    exact (coset_inverseKlein_differentiableAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein
      z).norm_lt_one).differentiableWithinAt
  have him : _root_.LowDimensionalTopology.Geometry.Hyperbolic.inverseKleinFormula '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' frontier S) =
      ((↑) : 𝔻 → ℂ) '' frontier S := by
    rw [image_image]
    apply Set.image_congr
    intro z _
    exact congrArg (fun u : 𝔻 => (u :
      ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinToPoincare_poincareToKlein z)
  have hz := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hzero
  rw [him] at hz
  exact withDensity_absolutelyContinuous volume _ hz

/-- Actual convex region frontiers are null for the original Fuchsian density area. -/
theorem UnitDiscFuchsianGroup.convex_frontier_area_zero
    {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup G)
    {S : Set P.domain.carrier} (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate
      '' S)) :
    P.area (frontier S) = 0 := by
  rw [P.area_apply _ isClosed_frontier.measurableSet,P.finiteCoordinate.image_frontier]
  exact coset_discHConvex_frontier_area_zero hS

/-- A genuine subgroup polygon intersected with a stable coset region is a full-group domain. -/
theorem isFundamentalDomain_inter_of_cosetStable_orbit_cover {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup G)
    (H : Subgroup G) (D S : Set P.domain.carrier)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H P.domain.carrier P.area D)
    (hDlf : LocallyFinite (fun h : H => h • closure D))
    (hDconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' D))
    (hSo : IsOpen S) (hSconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' S))
    (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsCosetStableRegion H S)
    (hcover : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit G P.domain.carrier (closure
      S)) :
    IsFuchsianFundamentalDomain P (D ∩ S) := by
  let cosetDomainContinuous : ContinuousConstSMul G P.domain.carrier :=
    _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  let cosetDomainSubgroupContinuous : ContinuousConstSMul H P.domain.carrier :=
    ⟨fun h => continuous_const_smul h.val⟩
  have hc : (⋃ h : H, h • closure D) = univ :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.iUnion_image_closure_eq_univ H P.domain.carrier hD
  have hMeet := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.coset_region_closure_meetsEveryOrbit H D S hSo hS.invariant hDlf hc hcover
  have hn : (D ∩ S).Nonempty := by
    obtain ⟨g,hg⟩ := hMeet (P.finiteCoordinate.symm 0)
    rcases eq_empty_or_nonempty (D ∩ S) with he | hn
    · rw [he,closure_empty] at hg
      exact False.elim hg
    · exact hn
  have hconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' (D ∩ S)) := by
    rw [image_inter P.finiteCoordinate.injective]
    intro z hz w hw u hu
    exact ⟨hDconv z hz.1 w hw.1 hu,hSconv z hz.2 w hw.2 hu⟩
  refine ⟨hD.isOpen.inter hSo,?_,?_,P.convex_frontier_area_zero hconv⟩
  · exact ⟨hn,P.finiteCoordinate.isEmbedding.isInducing.isPreconnected_image.mp hconv.isPreconnected⟩
  · apply exists_fundamentalSet_between _ _ subset_closure hMeet
    intro x hx y hy hxy
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.coset_region_orbit_unique H D S hS
      (fun _ hx _ hy he => _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.eq_of_mem H
        P.domain.carrier hD hx hy he)
      hx hy hxy

/-- The actual topological-measure coset construction, retaining the genuine orbit-selector definition. -/
theorem coset_intersection_fundamental {G X : Type*} [Group G] [TopologicalSpace X]
    [MeasurableSpace X] [Nonempty X] [MulAction G X] [ContinuousConstSMul G X]
    (H : Subgroup G) (μ : Measure X) (D S : Set X)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H X μ D)
    (hl : LocallyFinite (fun h : H => h • closure D))
    (ho : IsOpen S) (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsCosetStableRegion H S)
    (hcover : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit G X (closure S))
    (hconn : IsPreconnected (D ∩ S)) (hzero : μ (frontier (D ∩ S)) = 0) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain G X μ (D ∩ S) := by
  let cosetIntersectionSubgroupContinuous : ContinuousConstSMul H X :=
    ⟨fun h => continuous_const_smul h.val⟩
  have hc : (⋃ h : H, h • closure D) = univ :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.iUnion_image_closure_eq_univ H X hD
  have hMeet := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.coset_region_closure_meetsEveryOrbit H D S ho hS.invariant hl hc hcover
  have hn : (D ∩ S).Nonempty := by
    obtain ⟨g,hg⟩ := hMeet (Classical.arbitrary X)
    rcases eq_empty_or_nonempty (D ∩ S) with he | hn
    · rw [he,closure_empty] at hg
      exact False.elim hg
    · exact hn
  refine ⟨hD.isOpen.inter ho,⟨hn,hconn⟩,?_,hzero⟩
  apply exists_fundamentalSet_between _ _ subset_closure hMeet
  intro x hx y hy hxy
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.coset_region_orbit_unique H D S hS
    (fun _ hx _ hy he => _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.eq_of_mem H X
      hD hx hy he) hx hy hxy

/-- The same coset theorem in every actual original invariant disc, with its genuine transported area. -/
theorem geometric_isFundamentalDomain_inter_of_cosetStable_orbit_cover {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (E : FuchsianDisc G)
    (H : Subgroup G) (D S : Set (fuchsianGeometricDomain E).carrier)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      E).carrier (geometricModelArea E) D)
    (hl : LocallyFinite (fun h : H => h • closure D))
    (hDconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex ((geometricDiscData E).finiteCoordinate ''
      (geometricDiscHomeomorph E '' D)))
    (ho : IsOpen S)
    (hSconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex ((geometricDiscData E).finiteCoordinate ''
      (geometricDiscHomeomorph E '' S)))
    (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsCosetStableRegion H S)
    (hcover : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit G (fuchsianGeometricDomain
      E).carrier (closure S)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain G (fuchsianGeometricDomain E).carrier (geometricModelArea E) (D ∩ S) := by
  let C := (geometricDiscHomeomorph E).trans (geometricDiscData E).finiteCoordinate
  let cosetGeometricNonempty : Nonempty (fuchsianGeometricDomain E).carrier := ⟨C.symm 0⟩
  let cosetGeometricContinuous : ContinuousConstSMul G (fuchsianGeometricDomain E).carrier :=
    _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul (fuchsianGeometricDomain E)
  have hconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (C '' (D ∩ S)) := by
    have hD' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (C '' D) := by
      have he : C '' D = (geometricDiscData E).finiteCoordinate '' (geometricDiscHomeomorph E '' D) :=
        (image_image (geometricDiscData E).finiteCoordinate (geometricDiscHomeomorph E) D).symm
      exact he.symm ▸ hDconv
    have hS' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (C '' S) := by
      have he : C '' S = (geometricDiscData E).finiteCoordinate '' (geometricDiscHomeomorph E '' S) :=
        (image_image (geometricDiscData E).finiteCoordinate (geometricDiscHomeomorph E) S).symm
      exact he.symm ▸ hSconv
    rw [image_inter C.injective]
    intro z hz w hw u hu
    exact ⟨hD' z hz.1 w hw.1 hu,hS' z hz.2 w hw.2 hu⟩
  apply coset_intersection_fundamental H _ D S hD hl ho hS hcover
    (C.isEmbedding.isInducing.isPreconnected_image.mp hconv.isPreconnected)
  rw [geometricModelArea_apply E _ isClosed_frontier.measurableSet]
  have he : (geometricDiscData E).finiteCoordinate '' (geometricDiscHomeomorph E '' frontier (D ∩ S)) =
      frontier (C '' (D ∩ S)) := by
    rw [image_image]
    exact C.image_frontier (D ∩ S)
  rw [he]
  exact coset_discHConvex_frontier_area_zero hconv

/-- The original indexed coset-tile covering implies the exact orbit-covering condition. -/
theorem coset_cover_meetsEveryOrbit {G X ι : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (r : ι → G) (S : Set X)
    (hc : (⋃ i : ι, r i • closure S) = univ) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit G X (closure S) := by
  intro x
  have hx : x ∈ ⋃ i : ι, r i • closure S := by rw [hc];trivial
  obtain ⟨i,y,hy,he⟩ := mem_iUnion.mp hx
  refine ⟨(r i)⁻¹,?_⟩
  rw [←he]
  rwa [inv_smul_smul]

/-- The literal indexed-translate form of the original coset construction. -/
theorem isFundamentalDomain_inter_of_cosetStable_translate_cover {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (H : Subgroup G) (D S : Set P.domain.carrier)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H P.domain.carrier P.area D)
    (hDlf : LocallyFinite (fun h : H => h • closure D))
    (hDconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' D))
    (hSo : IsOpen S) (hSconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' S))
    (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsCosetStableRegion H S) {ι : Type*} (r : ι → G)
    (hcover : (⋃ i : ι, r i • closure S) = univ) :
    IsFuchsianFundamentalDomain P (D ∩ S) :=
  isFundamentalDomain_inter_of_cosetStable_orbit_cover P H D S hD hDlf hDconv hSo hSconv hS
    (coset_cover_meetsEveryOrbit r S hcover)

end
end LowDimensionalTopology.Geometry.Fuchsian
