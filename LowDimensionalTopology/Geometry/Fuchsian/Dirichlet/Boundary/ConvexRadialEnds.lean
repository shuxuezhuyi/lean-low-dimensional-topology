module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.ConvexRadial
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletBoundaryEndpoints
public import Mathlib.Analysis.Normed.Module.Normalize
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian










/-- Actual spherical order in the genuine normalized Klein coordinate is
equivalent to the original hyperbolic radial order. -/
theorem tanh_radial_order_iff (s t : ℝ) : Real.tanh s ≤ Real.tanh t ↔ s ≤ t := by
  have h := Real.artanh_le_artanh_iff
    ⟨Real.neg_one_lt_tanh s,Real.tanh_lt_one s⟩
    ⟨Real.neg_one_lt_tanh t,Real.tanh_lt_one t⟩
  simpa only [Real.artanh_tanh] using h.symm

open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Any genuine convex locally finite polygon has a finite preconnected cover
outside every positive original hyperbolic radius. Finiteness of sides and finite
generation are neither assumed nor inferred in this local radial statement. -/
theorem fuchsian_polygon_exterior_finite_preconnected_cover
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (w : P.domain.carrier) (hw : w ∈ D) (R : ℝ) (hR : 0 < R) :
    ∃ B : Set (Set P.domain.carrier), B.Finite ∧
      D ∩ {x | R ≤ P.hyperbolicDist w x} = ⋃ V ∈ B, V ∧
      (∀ V ∈ B, IsPreconnected V) := by
  let f := normalizedPolygonKleinCoordinate P w
  let U : Set ℂ := f '' D
  let r := Real.tanh R
  have hf := normalizedPolygonKleinCoordinate_isOpenEmbedding P w
  have hconv : Convex ℝ U := by
    have hh := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex
      _).mp (hD.pointCoordinate_smul_convex w (1:H))
    change Convex ℝ ((fun x => _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      ((polygonPointCoordinate P w) x)) '' D)
    simpa only [one_smul,image_image] using hh
  have h0 : (0:ℂ) ∈ U := ⟨w,hw,normalizedPolygonKleinCoordinate_self P w⟩
  have hr : 0 < r := by
    apply lt_of_not_ge
    intro h
    have hh := (tanh_radial_order_iff R 0).mp (by simpa only [Real.tanh_zero] using h)
    exact (not_le_of_gt hR) hh
  let S := D ∩ {x | P.hyperbolicDist w x = R}
  let C := (fun x => connectedComponentIn S x) '' S
  have hC : C.Finite := fuchsian_polygon_circle_inter_finite_components hD w R hR
  let F := (fun A => f '' A) '' C
  have hF : F.Finite := hC.image _
  have hsubC : ∀ A ∈ C, A ⊆ S := by
    rintro A ⟨x,hx,rfl⟩
    exact connectedComponentIn_subset _ _
  have hslice : U ∩ {x | ‖x‖ = r} = f '' S := by
    apply subset_antisymm
    · rintro z ⟨⟨x,hx,rfl⟩,hn⟩
      refine ⟨x,⟨hx,?_⟩,rfl⟩
      apply Real.tanh_injective
      rw [←normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist P w x]
      exact hn
    · rintro z ⟨x,⟨hx,hxR⟩,rfl⟩
      refine ⟨⟨x,hx,rfl⟩,?_⟩
      change ‖normalizedPolygonKleinCoordinate P w x‖ = Real.tanh R
      rw [normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist]
      exact congrArg Real.tanh hxR
  have hcover : U ∩ {x | ‖x‖ = r} ⊆ ⋃ A ∈ F, A := by
    rw [hslice]
    rintro z ⟨x,hx,rfl⟩
    exact mem_iUnion₂.mpr ⟨f '' connectedComponentIn S x,
      ⟨connectedComponentIn S x,⟨x,hx,rfl⟩,rfl⟩,x,mem_connectedComponentIn hx,rfl⟩
  have hsub : ∀ A ∈ F, A ⊆ U ∩ {x | ‖x‖ = r} := by
    rintro A ⟨V,hV,rfl⟩
    rw [hslice]
    exact image_mono (hsubC V hV)
  have hpre : ∀ A ∈ F, IsPreconnected A := by
    rintro A ⟨V,⟨x,hx,rfl⟩,rfl⟩
    exact isPreconnected_connectedComponentIn.image f hf.continuous.continuousOn
  obtain ⟨E,hE,hEc,hEp⟩ := _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.convex_radial_exterior_finite_preconnected_cover hconv h0 r hr F hF hcover hsub hpre
  have hExt : f ⁻¹' (U ∩ {x | r ≤ ‖x‖}) = D ∩ {x | R ≤ P.hyperbolicDist w x} := by
    ext x
    change (f x ∈ f '' D ∧ r ≤ ‖f x‖) ↔ (x ∈ D ∧ R ≤ P.hyperbolicDist w x)
    rw [hf.injective.mem_set_image,
      normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist P w x,tanh_radial_order_iff]
  let B := (fun V => f ⁻¹' V) '' E
  refine ⟨B,hE.image _,?_,?_⟩
  · rw [←hExt,hEc,preimage_iUnion₂]
    ext x
    constructor
    · intro hx
      obtain ⟨V,hV,hx⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨f ⁻¹' V,⟨V,hV,rfl⟩,hx⟩
    · intro hx
      obtain ⟨_,⟨V,hV,rfl⟩,hx⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨V,hV,hx⟩
  · rintro V ⟨A,hA,rfl⟩
    apply hf.isEmbedding.isInducing.isPreconnected_image.mp
    have hArange : A ⊆ range f := by
      intro z hz
      have hzE : z ∈ U ∩ {x | r ≤ ‖x‖} := by
        rw [hEc]
        exact mem_iUnion₂.mpr ⟨A,hA,hz⟩
      exact image_subset_range f D hzE.1
    rw [image_preimage_eq_of_subset hArange]
    exact hEp A hA

/-- The actual original convex locally finite polygon has finitely many true
connected components outside every positive original hyperbolic radius. -/
theorem fuchsian_polygon_exterior_components_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (w : P.domain.carrier) (hw : w ∈ D) (R : ℝ) (hR : 0 < R) :
    ((fun x => connectedComponentIn (D ∩ {y | R ≤ P.hyperbolicDist w y}) x) ''
      (D ∩ {x | R ≤ P.hyperbolicDist w x})).Finite := by
  obtain ⟨B,hB,hBc,hBp⟩ := fuchsian_polygon_exterior_finite_preconnected_cover hD w hw R hR
  apply _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.finite_connectedComponentIn_image_of_finite_preconnected_cover _ B hB
  · rw [hBc]
  · intro V hV x hx
    rw [hBc]
    exact mem_iUnion₂.mpr ⟨V,hV,hx⟩
  · exact hBp

end LowDimensionalTopology.Geometry.Fuchsian
