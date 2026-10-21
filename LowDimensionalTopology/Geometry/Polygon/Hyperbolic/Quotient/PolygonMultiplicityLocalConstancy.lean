module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonBoundaryMates
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.FiniteLocalPairSums
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
open Set Filter Topology
open scoped UpperHalfPlane Pointwise

/-- Every finite superset of the actual incident translate labels gives the exact
original angular sum; labels absent at the point contribute zero geometrically. -/
theorem nativePolygonAngularMultiplicityRadians_eq_sum_superset
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] (P : Set ℍ) (hP : IsCompact P)
    (z : ℍ) (I : Finset H) (hI : ∀g : H,z∈g • P →g∈I) :
    nativePolygonAngularMultiplicityRadians H P z=∑g∈I,nativeLocalAngle P (g⁻¹ • z) := by
  classical
  let J:=((_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite H hP).point_finite
    z).toFinset
  rw [nativePolygonAngularMultiplicityRadians_eq_sum H P hP z]
  trans ∑g∈J,nativeLocalAngle P (g⁻¹ • z)
  · apply Finset.sum_congr rfl
    intro g _
    have hh:=nativeLocalAngle_isometry g.val P (g⁻¹ • z)
    change nativeLocalAngle (g • P) (g • (g⁻¹ • z))=nativeLocalAngle P (g⁻¹ • z) at hh
    simpa only [smul_inv_smul] using hh
  · have hJI : J⊆I := by
      intro g hg
      apply hI g
      simpa only [J,Set.Finite.mem_toFinset,mem_ofPred_eq] using hg
    apply Finset.sum_subset hJI
    intro g _ hg
    apply nativeLocalAngle_of_not_mem_closure
    rw [hP.isClosed.closure_eq]
    intro hm
    apply hg
    rw [Set.Finite.mem_toFinset]
    exact mem_smul_set_iff_inv_smul_mem.mpr hm

/-- The genuine total angle is locally constant off the actual translated vertices.
All original boundary labels are finitely and involutively paired, while every other
actual translate has locally stable full or zero angle. -/
theorem NativeGeodesicPolygonGeometry.angularMultiplicity_locally_constant_away_vertices
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉V →S.OppositeSideNeighborhoods s x)
    (z : ℍ) (hAvoid : ∀g : S.Generated,z∉g • V) :
    ∀ᶠy in 𝓝 z,nativePolygonAngularMultiplicityRadians S.Generated P.carrier y=
      nativePolygonAngularMultiplicityRadians S.Generated P.carrier z := by
  classical
  let : Fintype (S.BoundaryCopy z):=(S.boundaryCopies_finite hP z).fintype
  obtain ⟨N,hN,hf⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite S.Generated hP z
  let I:=hf.toFinset
  let label : S.BoundaryCopy z→S.Generated:=fun a=>a.val.1
  let w (g : S.Generated) (y : ℍ):=nativeLocalAngle P.carrier (g⁻¹ • y)
  have htheta : ∀ᶠy in 𝓝 z,nativePolygonAngularMultiplicityRadians S.Generated P.carrier y=
      ∑g∈I,w g y := by
    filter_upwards [hN] with y hy
    apply nativePolygonAngularMultiplicityRadians_eq_sum_superset S.Generated P.carrier hP y I
    intro g hg
    exact hf.mem_toFinset.mpr ⟨y,hg,hy⟩
  have hinj : Function.Injective label := by
    intro a b he
    apply Subtype.ext
    exact S.copy_eq_of_evaluation_same_index he (a.property.1.trans b.property.1.symm)
  have hlabelI (a : S.BoundaryCopy z) : label a∈I := by
    apply hf.mem_toFinset.mpr
    exact ⟨z,⟨a.val.2.val,a.val.2.property,a.property.1⟩,mem_of_mem_nhds hN⟩
  have hStable (g : S.Generated) (_hg : g∈I) (hB : g∉range label) :
      ∀ᶠy in 𝓝 z,w g y=w g z := by
    let f : ℍ→ℍ:=fun y=>g⁻¹ • y
    have hc : Continuous f:=g.val.symm.continuous
    have hnotB : f z∉P.boundary := by
      intro hb
      let a : S.BoundaryCopy z:=⟨(g,⟨f z,Or.inr hb⟩),smul_inv_smul _ _,hb⟩
      exact hB ⟨a,rfl⟩
    by_cases hm : f z∈P.carrier
    · have hi : f z∈P.interior:=hm.resolve_right hnotB
      have hNf:=hc.continuousAt.preimage_mem_nhds (G.interior_open.mem_nhds hi)
      filter_upwards [hNf] with y hy
      change nativeLocalAngle P.carrier (f y)=nativeLocalAngle P.carrier (f z)
      rw [nativeLocalAngle_of_interior (by rw [G.carrier_closure,G.regular_open];exact hy),
        nativeLocalAngle_of_interior (by rw [G.carrier_closure,G.regular_open];exact hi)]
    · have hNf:=hc.continuousAt.preimage_mem_nhds (hP.isClosed.isOpen_compl.mem_nhds hm)
      filter_upwards [hNf] with y hy
      change nativeLocalAngle P.carrier (f y)=nativeLocalAngle P.carrier (f z)
      rw [nativeLocalAngle_of_not_mem_closure (by rwa [hP.isClosed.closure_eq]),
        nativeLocalAngle_of_not_mem_closure (by rwa [hP.isClosed.closure_eq])]
  have hpairs (a : S.BoundaryCopy z) :
      ∀ᶠy in 𝓝 z,w (label a) y+w (label (S.boundaryCopyMate a)) y=2*Real.pi :=
    S.boundaryCopyMate_local_angle_sum G hV hAvoid hOpp a
  have hsum:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.finite_local_sum_constant_of_paired_labels I label hinj hlabelI
    S.boundaryCopyMate (S.boundaryCopyMate_involutive G hAvoid) w z (2*Real.pi) hpairs hStable
  filter_upwards [htheta,hsum] with y hy hysum
  exact hy.trans (hysum.trans htheta.self_of_nhds.symm)

/-- The original Jordan polygon and actual original side intervals give local
constancy of its true entire angular multiplicity away from translated vertices. -/
theorem nativeJordan_angularMultiplicity_locally_constant_away_vertices
    {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices →S.OppositeSideNeighborhoods s x)
    (z : ℍ) (hAvoid : ∀g : S.Generated,z∉g • D.vertices) :
    ∀ᶠy in 𝓝 z,nativePolygonAngularMultiplicityRadians S.Generated P.carrier y=
      nativePolygonAngularMultiplicityRadians S.Generated P.carrier z :=
  (nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary
    D).angularMultiplicity_locally_constant_away_vertices S hP (D.pairing_preserves_vertices S) hOpp z hAvoid

end LowDimensionalTopology.Geometry.Polygon
