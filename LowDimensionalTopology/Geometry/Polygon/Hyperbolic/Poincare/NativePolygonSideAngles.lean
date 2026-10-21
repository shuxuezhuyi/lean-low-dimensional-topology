module
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.HalfPlaneLocalAngularMeasure
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeAngularMultiplicity
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeGeodesicPolygonGeometry
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped Complex.UnitDisc UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- Native local angles depend only on the original local germ. -/
theorem nativeLocalAngle_congr {P Q : Set ℍ} {z : ℍ}
    (h : ∀ᶠw in 𝓝 z,w∈P ↔w∈Q) : nativeLocalAngle P z=nativeLocalAngle Q z := by
  have hh : ∀ᶠw in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph z),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm w∈P ↔_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm w∈Q := by
    have h' : ∀ᶠw in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph z)),w∈P ↔w∈Q := by
      simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm_apply_apply] using h
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm.continuous.tendsto
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph z)).eventually h'
  have he : ∀ᶠw in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph z),w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph '' P ↔w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph '' Q := by
    have hmem (A : Set ℍ) (w : Complex.UnitDisc) :
        w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph '' A ↔_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm w∈A := by
      constructor
      · rintro ⟨v,hv,rfl⟩
        simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm_apply_apply] using hv
      · intro hw
        exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm
          w,hw,_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.apply_symm_apply w⟩
    filter_upwards [hh] with w hw
    exact (hmem P w).trans (hw.trans (hmem Q w).symm)
  unfold nativeLocalAngle nativeLocalAngularFraction
  congr 2
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction_congr he

/-- The original half-plane component at I has the true straight angle. -/
theorem nativeLocalAngle_closedHHalfPlane_I (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u :
  ℍ)
    (hu : u∉L.carrier) (hI : UpperHalfPlane.I∈L.carrier) :
    nativeLocalAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u) UpperHalfPlane.I=Real.pi := by
  have h0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I=(0 : Complex.UnitDisc) := by
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane (0 : Complex.UnitDisc)
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHalfPlane L.toDiscLine (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc u) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph '' closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane L u)=closure _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.image_closure]
    change closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ''
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane L u)=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayley_image_openHHalfPlane L u hu]
  have huD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc u∉L.toDiscLine.carrier := by
    rw [L.toDiscLine_carrier,L.discCarrier_eq_cayley_image]
    intro h
    obtain ⟨w,hw,heq⟩:=h
    exact hu (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective heq ▸ hw)
  have hLD : (0 : Complex.UnitDisc)∈L.toDiscLine.carrier := by
    rw [L.toDiscLine_carrier,L.discCarrier_eq_cayley_image]
    exact ⟨UpperHalfPlane.I,hI,h0⟩
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I)=Real.pi
  rw [he,h0]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngle_closedDiscHalfPlane_origin L.toDiscLine _ huD hLD

/-- Every actual geodesic boundary point has the true straight angle in either actual
closed half-plane component. Its direction and position are not extra model hypotheses. -/
theorem nativeLocalAngle_closedHHalfPlane (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u z :
  ℍ)
    (hu : u∉L.carrier) (hz : z∈L.carrier) :
    nativeLocalAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u) z=Real.pi := by
  let f : ℍ≃ᵢℍ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry z.toSL2R⁻¹
  have hfz : f z=UpperHalfPlane.I := by
    change z.toSL2R⁻¹ • z=UpperHalfPlane.I
    calc
      z.toSL2R⁻¹ • z=z.toSL2R⁻¹ • (z.toSL2R • UpperHalfPlane.I):=
        congrArg (fun w : ℍ=>z.toSL2R⁻¹ • w) (UpperHalfPlane.toSL2R_smul_I z).symm
      _=UpperHalfPlane.I:=inv_smul_smul _ _
  obtain ⟨M,hM⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine f.isometry L
  have hfu : f u∉M.carrier := by
    rw [←hM]
    intro hm
    obtain ⟨v,hv,he⟩:=hm
    exact hu (f.injective he ▸ hv)
  have hMI : UpperHalfPlane.I∈M.carrier := by
    rw [←hM]
    exact ⟨z,hz,hfz⟩
  have he:=nativeLocalAngularFraction_isometry f (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L
    u) z
  have ha : nativeLocalAngle (f '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u) (f z)=
      nativeLocalAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane L u) z := by
    unfold nativeLocalAngle
    rw [he]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_image_closed_halfPlane f L M hM u hu,hfz] at ha
  exact ha.symm.trans (nativeLocalAngle_closedHHalfPlane_I M (f u) hfu hMI)

/-- A genuine original nonvertex side has angle pi, including nonconvex original
polygons. The local half-plane germ is proved from the actual original geometry. -/
theorem NativeGeodesicPolygonGeometry.nonvertex_localAngle {P : PoincarePolygon ℍ}
    {V : Set ℍ} (D : NativeGeodesicPolygonGeometry P V) (x : P.Point) (s : P.Side)
    (hx : x.val∈s.val) (hv : x.val∉V) : nativeLocalAngle P.carrier x.val=Real.pi := by
  obtain ⟨u,hu,r,hr,hg⟩:=D.component_germ x s hx hv
  have he : nativeLocalAngle P.carrier x.val=nativeLocalAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHHalfPlane (D.line s) u) x.val := by
    apply nativeLocalAngle_congr
    filter_upwards [Metric.ball_mem_nhds x.val hr] with w hw
    exact hg w hw
  exact he.trans (nativeLocalAngle_closedHHalfPlane (D.line s) u x.val hu (D.side_subset_line s hx))

end LowDimensionalTopology.Geometry.Polygon
