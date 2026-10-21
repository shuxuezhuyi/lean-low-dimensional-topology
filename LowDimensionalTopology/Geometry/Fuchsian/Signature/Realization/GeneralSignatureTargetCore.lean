/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureNoncutChamber
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetCoreCompactness
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSignature
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.FiniteHullCuspBounds
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetNonElementary
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetBoundaryAxes
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- A compact set of original representatives outside an invariant closed core
forces a genuine positive distance maximum if the saturation leaves that core.
The maximum is interior when its entire frontier lies in the core. -/
theorem tileSaturation_subset_closedCore_of_compact_defect
    (G : Subgroup (ℍ ≃ᵢ ℍ)) (Q N C : Set ℍ)
    (hC : IsClosed C) (hCne : C.Nonempty) (hNC : N ⊆ C)
    (hCinv : ∀ a ∈ G, (a : ℍ ≃ᵢ ℍ) '' C = C)
    (hcompact : IsCompact (Q \ N))
    (hfrontier : frontier (⋃ a ∈ G, a '' Q) ⊆ C)
    (hno : ∀ x ∉ C, ¬ IsLocalMax (fun z => Metric.infDist z C) x) :
    (⋃ a ∈ G, a '' Q) ⊆ C := by
  let S : Set ℍ := ⋃ a ∈ G, a '' Q
  have hinf (a : ℍ ≃ᵢ ℍ) (ha : a ∈ G) (x : ℍ) :
      Metric.infDist (a x) C = Metric.infDist x C := by
    calc
      _ = Metric.infDist (a x) (a '' C) := congrArg (Metric.infDist (a x)) (hCinv a ha).symm
      _ = Metric.infDist x C := Metric.infDist_image a.isometry
  intro z hz
  by_contra hzC
  obtain ⟨a, ha, y, hy, rfl⟩ := mem_iUnion₂.mp hz
  have hyC : y ∉ C := by
    intro h
    exact hzC ((hCinv a ha) ▸ mem_image_of_mem a h)
  have hyK : y ∈ Q \ N := ⟨hy, fun h => hyC (hNC h)⟩
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn ⟨y, hyK⟩
    (Metric.continuous_infDist_pt C).continuousOn
  have hypos : 0 < Metric.infDist y C := by
    apply (Metric.infDist_pos_iff_notMem_closure hCne).mp
    simpa only [hC.closure_eq] using hyC
  have hxpos : 0 < Metric.infDist x C := hypos.trans_le (hmax hyK)
  have hxC : x ∉ C := by
    intro h
    rw [Metric.infDist_zero_of_mem h] at hxpos
    exact lt_irrefl 0 hxpos
  have hxS : x ∈ S := by
    refine mem_iUnion₂.mpr ⟨1, G.one_mem, x, hx.1, ?_⟩
    rfl
  have hxint : x ∈ interior S :=
    (mem_interior_iff_notMem_frontier hxS).mpr (fun h => hxC (hfrontier h))
  have hmaxS : IsMaxOn (fun z => Metric.infDist z C) S x := by
    intro w hw
    obtain ⟨b, hb, u, hu, rfl⟩ := mem_iUnion₂.mp hw
    change Metric.infDist (b u) C ≤ Metric.infDist x C
    rw [hinf b hb]
    by_cases huN : u ∈ N
    · rw [Metric.infDist_zero_of_mem (hNC huN)]
      exact Metric.infDist_nonneg
    · exact hmax ⟨hu, huN⟩
  exact hno x hxC (hmaxS.isLocalMax (Filter.mem_of_superset (isOpen_interior.mem_nhds hxint)
    interior_subset))

/-- True geodesic convexity and both actual ideal closure endpoints force
the whole finite geodesic into the ordinary closure. -/
theorem halfPlaneLine_subset_closure_of_ideal_closure
    (T : Set ℍ)
    (hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex T)
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hends : L.idealEndpoints ⊆ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' T)) :
    L.carrier ⊆ closure T := by
  have hmodel (A : Set ℍ) (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel)
      (hp : p.val ∈ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' A)) :
      p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure A := by
    change p.val ∈ closure ((fun z : ℍ => ((z : ℂ) : Mobius.ExtendedComplex)) '' A) at hp
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure_ambient] at hp
    obtain ⟨q, hq, he⟩ := hp
    exact Subtype.ext he ▸ hq
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneHConvex (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure T) := by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHalfPlaneHConvex_iff_cayley _).mpr
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_image_closure]
    exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex T).mp hT).closedModelClosure
  obtain ⟨a, b, _, hab, ha, hb, he, _⟩ := L.exists_idealEndpoints_pair
  have haL : a ∈ L.idealEndpoints := he ▸ (by simp)
  have hbL : b ∈ L.idealEndpoints := he ▸ (by simp)
  have haC : a ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHalfPlaneSet := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHalfPlaneSet_eq_open_union_boundary]
    exact Or.inr ha
  have hbC : b ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHalfPlaneSet := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHalfPlaneSet_eq_open_union_boundary]
    exact Or.inr hb
  let p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel := ⟨a, haC⟩
  let q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel := ⟨b, hbC⟩
  have hpT := hmodel T p (hends haL)
  have hqT := hmodel T q (hends hbL)
  have hpL : p ∈ L.closedCarrier := hmodel L.carrier p haL.1
  have hqL : q ∈ L.closedCarrier := hmodel L.carrier q hbL.1
  have hline : L.closedCarrier ⊆ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure T := by
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelHSegment_ideal_endpoints L p q ha hb
      (fun hpq => hab (congrArg Subtype.val hpq)) hpL hqL]
    exact hc p hpT q hqT
  intro z hz
  change z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneRelativeClosure T
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneRelativeClosure_eq_preimage]
  exact hline (subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel hz))

section ActualTarget
variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
local notation "P₀" => generalCoreTargetMobiusData g orders s t ho hdef d hd hb
local notation "H₀" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "K₀" => generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb
local notation "U₀" => generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I
local notation "D₀" => _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.asFuchsianDisc P₀

/-- The source-defined Nielsen region lies in the actual retained chamber,
by the original least invariant open convex set theorem. -/
theorem generalCoreTarget_nielsen_subset_chamber
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) ⊆ U₀ := by
  let D := (P₀).asFuchsianDisc
  let T := _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' U₀
  have hTD : T ⊆ D.carrier := by
    change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' U₀ ⊆ _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_range]
    exact image_subset_range _ _
  have hI : UpperHalfPlane.I ∈ U₀ := by
    apply mem_connectedComponentIn
    exact generalCoreAux_interior_avoids_cutWalls g orders s t ho hdef d hd hb _
      (generalCoreAux_center_mem_interior g orders s t ho hdef d hd hb)
  have hc : D.HyperbolicallyConvex T := by
    apply (D.hyperbolicallyConvex_halfPlane rfl U₀).mpr
    apply generalCoreCutChamber_hConvex
    exact generalCoreAux_interior_avoids_cutWalls g orders s t ho hdef d hd hb _
      (generalCoreAux_center_mem_interior g orders s t ho hdef d hd hb)
  have hi : ∀ a : K₀, ∀ p ∈ T, a • p ∈ T := by
    intro a p hp
    obtain ⟨z, hz, rfl⟩ := hp
    let E := generalCoreTargetMobiusEquiv g orders s t ho hdef d hd hb
    let f := E.symm a
    have hfu : f.val z ∈ U₀ := by
      rw [← generalCoreTargetGroup_chamber_image g orders s t ho hdef d hd hb f.val f.property]
      exact mem_image_of_mem f.val hz
    refine ⟨f.val z, hfu, ?_⟩
    let originalTargetNativeAction := (P₀).nativeAction
    have hact := generalCoreTargetMobiusEquiv_action g orders s t ho hdef d hd hb f z
    have he : E f = a := E.apply_symm_apply a
    rw [he] at hact
    exact (congrArg _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint hact).symm.trans ((P₀).nativeAction_boundary a z).symm
  have hmin : D.nielsenRegion hNE ⊆ T :=
    (D.nielsenRegion_isLeast_nonempty_open_invariant_convex hNE).2 ⟨hTD, ⟨_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint UpperHalfPlane.I,
      mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint hI⟩,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.isOpenMap _
        (generalCoreCutChamber_isOpen g orders s t ho hdef d hd hb _), hc, hi⟩
  intro z hz
  obtain ⟨y, hy, he⟩ := hmin hz
  exact _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective he ▸ hy

/-- The same whole native target preserves its actual source Nielsen region. -/
theorem generalCoreTarget_nielsen_image (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀)
    (a : ℍ ≃ᵢ ℍ) (ha : a ∈ H₀) :
    a '' (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) =
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) := by
  let N := _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE
  have hf (f : H₀) (z : ℍ) (hz : z ∈ N) : f.val z ∈ N := by
    let E := generalCoreTargetMobiusEquiv g orders s t ho hdef d hd hb
    have hp := ((D₀).nielsenRegion_properties hNE).2.2.2.2 (E f)
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z) hz
    change (generalCoreTargetMobiusHom g orders s t ho hdef d hd hb f).val
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z) ∈ (D₀).nielsenRegion hNE at hp
    unfold generalCoreTargetMobiusHom at hp
    rw [nativeConformalSubgroupMobiusHom_action H₀
      (generalCoreTargetGroup_conformal g orders s t ho hdef d hd hb) f z] at hp
    exact hp
  apply subset_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hf ⟨a, ha⟩ z hz
  · intro z hz
    exact ⟨a.symm z, hf ⟨a⁻¹, (H₀).inv_mem ha⟩ z hz, a.apply_symm_apply z⟩

/-- The closure of the actual Nielsen region is invariant under the entire
actual target, not merely the displayed side generators. -/
theorem generalCoreTarget_nielsen_closure_image
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀)
    (a : ℍ ≃ᵢ ℍ) (ha : a ∈ H₀) :
    a '' closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) =
      closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) := by
  calc
    _ = closure (a '' (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE)) :=
      a.toHomeomorph.image_closure _
    _ = _ := congrArg closure (generalCoreTarget_nielsen_image g orders s t ho hdef d hd hb hNE a ha)

/-- The source core is nonempty in the unchanged native upper half-plane. -/
theorem generalCoreTarget_nielsen_nonempty
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE).Nonempty := by
  obtain ⟨p, hp⟩ := ((D₀).nielsenRegion_properties hNE).2.1
  have hpD := ((D₀).nielsenRegion_properties hNE).1 hp
  change p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet at hpD
  rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_range] at hpD
  obtain ⟨z, rfl⟩ := hpD
  exact ⟨z, hp⟩

/-- Minimality places the true closed Nielsen core inside the saturation of
the original polygon, using the proved geometric chamber equality. -/
theorem generalCoreTarget_nielsen_closure_subset_tileSaturation
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) ⊆
      generalCoreTargetTileSaturation g orders s t ho hdef d hd hb := by
  rw [generalCoreTargetTileSaturation_eq_chamber_closure]
  exact closure_mono (generalCoreTarget_nielsen_subset_chamber g orders s t ho hdef d hd hb hNE)

/-- Every actual target hyperbolic axis lies in the genuine source Nielsen
core closure. Its fixed endpoints are true whole-group limit points. -/
theorem generalCoreTarget_hyperbolic_axis_subset_nielsen_closure
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ K₀)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (htA : 4 < (Matrix.trace A.val)^2) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier ⊆
      closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) := by
  let N := _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE
  let R := (D₀).nielsenRegion hNE
  have hprops := (D₀).nielsenRegion_properties hNE
  have he : _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' N = R := by
    rw [image_preimage_eq_inter_range, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_range]
    exact inter_eq_left.mpr hprops.1
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex N := by
    apply ((D₀).hyperbolicallyConvex_halfPlane rfl N).mp
    change (D₀).HyperbolicallyConvex (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' N)
    rw [he]
    exact hprops.2.2.2.1
  have hlim : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet K₀ ⊆ closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' N) := by
    rw [he]
    exact nielsen_limitSet_subset_closure K₀ hNE R hprops.2.1 hprops.2.2.2.2
  apply halfPlaneLine_subset_closure_of_ideal_closure N hc
  apply Subset.trans _ hlim
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints]
  intro p hp
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_fixed_mem_limitSet K₀ hNE ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, hmem⟩
    (Or.inr ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr htA).1) p hp

/-- The complete geodesic supporting each original cut is inside the true
closed Nielsen core of the retained group; no boundary-core premise is added. -/
theorem generalCoreTarget_boundary_axis_subset_nielsen_closure
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀)
    (j : Fin t) :
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
        (generalCoreTheta_mem g orders s t ho hdef) hd hb)
      (generalCoreBoundarySideIndex g orders s t j 1)).carrier ⊆
        closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) := by
  obtain ⟨A, _, hmem, hA, htA, haxis⟩ :=
    generalCoreTarget_boundary_matrix_axis g orders s t ho hdef d hd hb j
  rw [← haxis]
  exact generalCoreTarget_hyperbolic_axis_subset_nielsen_closure
    g orders s t ho hdef d hd hb hNE A hmem hA htA

/-- Every finite frontier point of the actual retained saturation belongs
to the genuine Nielsen core closure. The actual cut-incidence theorem
supplies the entire frontier, rather than assuming a boundary description. -/
theorem generalCoreTargetTileSaturation_frontier_subset_nielsen_closure
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    frontier (generalCoreTargetTileSaturation g orders s t ho hdef d hd hb) ⊆
      closure (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE) := by
  intro x hx
  have hxA := generalCoreTargetTileSaturation_frontier_subset_axes g orders s t ho hdef d hd hb hx
  obtain ⟨a, ha, y, hy, rfl⟩ := mem_iUnion₂.mp hxA
  obtain ⟨j, hy⟩ := mem_iUnion.mp hy
  have hyC := generalCoreTarget_boundary_axis_subset_nielsen_closure
    g orders s t ho hdef d hd hb hNE j hy
  rw [← generalCoreTarget_nielsen_closure_image g orders s t ho hdef d hd hb hNE a ha]
  exact mem_image_of_mem a hyC

end ActualTarget

end LowDimensionalTopology.Geometry.Fuchsian
