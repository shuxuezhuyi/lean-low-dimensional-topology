module
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativePolygonSideAngles
public import Mathlib.Tactic
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.OriginalJordanPolygonPoincare
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeSideEndpointTransport
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- Away from its actual supporting geodesic, membership in the actual closed
component is interior membership, proved from the genuine affine Klein cut. -/
theorem closedHHalfPlane_mem_interior_of_not_line (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u z : ℍ)
    (hu : u∉L.carrier) (hz : z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u) (hzL :
      z∉L.carrier) :
    z∈interior (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u) := by
  obtain ⟨n,t,hn,hLine⟩:=L.klein_affine_equation
  have hc : Continuous (fun w : ℍ=>inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
    w)):=
    continuous_const.inner _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous
  have hne : inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
    z)≠t:=fun h=>hzL ((hLine z).mpr h)
  rcases _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closed_halfPlane_cases L n t hn hLine u hu with he | he
  · have hle : inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) ≤ t:=by simpa only [he,mem_ofPred_eq] using hz
    have hlt : inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
      z)<t:=lt_of_le_of_ne hle hne
    apply mem_interior_iff_mem_nhds.mpr
    rw [he]
    exact mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds hlt) (fun _ hw=>hw.le)
  · have hle : t ≤ inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z):=by simpa only [he,mem_ofPred_eq] using hz
    have hlt : t < inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
      z):=lt_of_le_of_ne hle hne.symm
    apply mem_interior_iff_mem_nhds.mpr
    rw [he]
    exact mem_of_superset ((isOpen_lt continuous_const hc).mem_nhds hlt) (fun _ hw=>hw.le)

/-- Two genuine closed components whose overlap lies in their common line are the
opposite components, so their actual union is the entire physical plane. -/
theorem closedHHalfPlanes_union_of_inter_subset_line (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u v : ℍ)
    (hu : u∉L.carrier) (hv : v∉L.carrier)
    (hInter : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L
      u∩_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L v⊆L.carrier) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u∪_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L v=univ := by
  obtain ⟨n,t,hn,hLine⟩:=L.klein_affine_equation
  have huC : u∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u:=subset_closure (mem_connectedComponentIn hu)
  rcases _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closed_halfPlane_cases L n t hn hLine u hu with heU | heU <;>
    rcases _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closed_halfPlane_cases L n t hn hLine v hv with heV | heV
  · have hvC : u∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L v:=by simpa only [heV,←heU] using huC
    exact (hu (hInter ⟨huC,hvC⟩)).elim
  · rw [heU,heV]
    ext z
    exact iff_true_intro (le_total (inner ℝ n
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)) t)
  · rw [heU,heV]
    ext z
    exact iff_true_intro (le_total t (inner ℝ n
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)))
  · have hvC : u∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L v:=by simpa only [heV,←heU] using huC
    exact (hu (hInter ⟨huC,hvC⟩)).elim

/-- Actual opposite geodesic components have a constant full-angle sum at every
physical point, including their shared supporting line. -/
theorem nativeLocalAngle_opposite_halfPlanes (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u v
  : ℍ)
    (hu : u∉L.carrier) (hv : v∉L.carrier)
    (hUnion : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L
      u∪_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L v=univ)
    (hInter : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L
      u∩_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L v⊆L.carrier) (z : ℍ) :
    nativeLocalAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u) z+
      nativeLocalAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L v) z=2*Real.pi := by
  by_cases hzL : z∈L.carrier
  · rw [nativeLocalAngle_closedHHalfPlane L u z hu hzL,
      nativeLocalAngle_closedHHalfPlane L v z hv hzL]
    ring
  · have hz : z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u ∪_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L v:=by rw [hUnion];trivial
    rcases hz with hzu | hzv
    · have hnot : z∉_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L v:=fun h=>hzL (hInter ⟨hzu,h⟩)
      have hncl : z∉closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L v):=by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane,closure_closure] using hnot
      rw [nativeLocalAngle_of_interior (closedHHalfPlane_mem_interior_of_not_line L u z hu hzu hzL),
        nativeLocalAngle_of_not_mem_closure hncl,add_zero]
    · have hnot : z∉_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u:=fun h=>hzL (hInter ⟨h,hzv⟩)
      have hncl : z∉closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u):=by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane,closure_closure] using hnot
      rw [nativeLocalAngle_of_not_mem_closure hncl,
        nativeLocalAngle_of_interior (closedHHalfPlane_mem_interior_of_not_line L v z hv hzv hzL),zero_add]

/-- Opposite actual local half-plane germs give a constant full-angle sum on a true
neighborhood of the original point. The sets themselves need not be globally convex. -/
theorem nativeLocalAngle_add_of_opposite_germs (A B : Set ℍ) (x : ℍ)
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u v : ℍ) (hu : u∉L.carrier) (hv :
      v∉L.carrier)
    (hxL : x∈L.carrier)
    (hA : ∀ᶠz in 𝓝 x,z∈A ↔z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u)
    (hB : ∀ᶠz in 𝓝 x,z∈B ↔z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L v)
    (hCover : A∪B∈𝓝 x) :
    ∀ᶠz in 𝓝 x,nativeLocalAngle A z+nativeLocalAngle B z=2*Real.pi := by
  have hComp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u∪_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L v∈𝓝 x := by
    filter_upwards [hA,hB,hCover] with z hzA hzB hz
    exact hz.elim (fun h=>Or.inl (hzA.mp h)) (fun h=>Or.inr (hzB.mp h))
  obtain ⟨n,t,hn,hLine⟩:=L.klein_affine_equation
  have hInter:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closed_halfPlanes_opposite L n t hn hLine u v x hu hv hxL hComp
  have hUnion:=closedHHalfPlanes_union_of_inter_subset_line L u v hu hv hInter.le
  filter_upwards [eventually_eventually_nhds.mpr hA,eventually_eventually_nhds.mpr hB]
    with z hzA hzB
  rw [nativeLocalAngle_congr hzA,nativeLocalAngle_congr hzB]
  exact nativeLocalAngle_opposite_halfPlanes L u v hu hv hUnion hInter.le z

theorem nativeLocalAngle_isometry (f : ℍ≃ᵢℍ) (A : Set ℍ) (z : ℍ) :
    nativeLocalAngle (f '' A) (f z)=nativeLocalAngle A z := by
  unfold nativeLocalAngle
  rw [nativeLocalAngularFraction_isometry]

theorem nativeLocalAngle_preimage_isometry (f : ℍ≃ᵢℍ) (A : Set ℍ) (z : ℍ) :
    nativeLocalAngle (f ⁻¹' A) z=nativeLocalAngle A (f z) := by
  have he:=nativeLocalAngle_isometry f.symm A (f z)
  have hset : f.symm '' A=f ⁻¹' A:=f.symm.toEquiv.image_eq_preimage_symm A
  simpa only [f.symm_apply_apply,hset] using he

/-- The original opposite-side convention gives the actual local full-angle pair.
The original polygon need not be convex, and no local tiling or angle sum is assumed. -/
theorem NativeGeodesicPolygonGeometry.paired_side_local_angle_sum
    {P : PoincarePolygon ℍ} {V : Set ℍ} (D : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hV : ∀z∈V,∀t : P.Side,z∈t.val →S.element t z∈V)
    (x : P.Point) (s : P.Side) (hx : x.val∈s.val) (hv : x.val∉V)
    (hOpp : S.OppositeSideNeighborhoods s x.val) :
    ∀ᶠz in 𝓝 x.val,nativeLocalAngle P.carrier z+
      nativeLocalAngle P.carrier (S.element s z)=2*Real.pi := by
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  let f:=S.element s
  let N:=D.line s
  let M:=D.line (S.paired s)
  have hySide : f x.val∈(S.paired s).val := by
    rw [←S.side_image]
    exact ⟨x.val,hx,rfl⟩
  let y : P.Point:=⟨f x.val,P.side_subset_carrier (S.paired s) hySide⟩
  have hyv : y.val∉V := by
    intro hyV
    have he:=hV y.val hyV (S.paired s) hySide
    change S.element (S.paired s) (f x.val)∈V at he
    rw [S.element_paired] at he
    change f.symm (f x.val)∈V at he
    rw [f.symm_apply_apply] at he
    exact hv he
  obtain ⟨u,hu,r₀,hr₀,h₀⟩:=D.component_germ x s hx hv
  obtain ⟨v,hvM,r₁,hr₁,h₁⟩:=D.component_germ y (S.paired s) hySide hyv
  have hLines : f '' N.carrier=M.carrier:=D.pairing_line_image S s
  let w:=f.symm v
  have hw : w∉N.carrier := by
    intro hw
    apply hvM
    rw [←hLines]
    exact ⟨w,hw,f.apply_symm_apply v⟩
  have hImage : f '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N w=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane M v := by
    simpa only [w,f.apply_symm_apply] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_image_closed_halfPlane f N M hLines w hw
  have hPull (z : ℍ) : f z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane M v ↔z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N w := by
    rw [←hImage]
    exact f.injective.mem_set_image
  have hA : ∀ᶠz in 𝓝 x.val,z∈P.carrier ↔z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N u := by
    filter_upwards [Metric.ball_mem_nhds x.val hr₀] with z hz
    exact h₀ z hz
  have hB : ∀ᶠz in 𝓝 x.val,z∈f ⁻¹' P.carrier ↔z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane N w := by
    filter_upwards [Metric.ball_mem_nhds x.val hr₁] with z hz
    have hd : dist (f z) y.val<r₁ := by
      change dist (f z) (f x.val)<r₁
      rwa [f.isometry.dist_eq]
    exact (h₁ (f z) hd).trans (hPull z)
  have hCover : P.carrier∪f ⁻¹' P.carrier∈𝓝 x.val:=
    (S.oppositeSideNeighborhoods_iff s x.val).mp hOpp
  have hh:=nativeLocalAngle_add_of_opposite_germs P.carrier (f ⁻¹' P.carrier) x.val
    N u w hu hw (D.side_subset_line s hx) hA hB hCover
  filter_upwards [hh] with z hz
  rwa [nativeLocalAngle_preimage_isometry f] at hz

/-- The original Jordan polygon and literal side intervals give the actual neighboring
full-angle sum from the original opposite-side convention alone. Endpoint preservation
and both original half-plane germs are proved from the original geometry. -/
theorem nativeJordan_paired_side_local_angle_sum {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    (x : P.Point) (s : P.Side) (hx : x.val∈s.val) (hv : x.val∉D.vertices)
    (hOpp : S.OppositeSideNeighborhoods s x.val) :
    ∀ᶠz in 𝓝 x.val,nativeLocalAngle P.carrier z+
      nativeLocalAngle P.carrier (S.element s z)=2*Real.pi :=
  (nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D).paired_side_local_angle_sum
    S (D.pairing_preserves_vertices S) x s hx hv hOpp

end LowDimensionalTopology.Geometry.Polygon
