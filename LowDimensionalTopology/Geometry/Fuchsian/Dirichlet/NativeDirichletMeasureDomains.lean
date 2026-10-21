module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.NativeClosedDirichletCover
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeIsometryFreeCenters
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Quotient.PolygonVertexAngularMultiplicity
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.NativeIsometryMeasure
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PerpendicularBisectors
public import Mathlib.MeasureTheory.Group.FundamentalDomain
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon

/-- The literal closed native Dirichlet comparison set is Borel measurable. -/
theorem nativeClosedDirichlet_isClosed (H : Subgroup (ℍ≃ᵢℍ)) (w : ℍ) :
    IsClosed (nativeClosedDirichlet H w) := by
  have he : nativeClosedDirichlet H w=⋂g : H,{z : ℍ | dist z w≤dist z (g.val w)} := by
    ext z
    simp [nativeClosedDirichlet]
  rw [he]
  exact isClosed_iInter (fun _=>isClosed_le (by fun_prop) (by fun_prop))

/-- Every point in an actual Dirichlet translate is at least as close to its own
actual orbit center as to every other original center. -/
theorem nativeClosedDirichlet_translate_comparison
    (H : Subgroup (ℍ≃ᵢℍ)) (w : ℍ) (g h : H) {z : ℍ}
    (hz : z∈g • nativeClosedDirichlet H w) : dist z (g • w)≤dist z (h • w) := by
  obtain ⟨u,hu,rfl⟩:=hz
  have he : g • ((g⁻¹*h) • w)=h • w := by simp [mul_smul]
  calc
    dist (g • u) (g • w)=dist u w:=g.val.dist_eq _ _
    _≤dist u ((g⁻¹*h) • w):=hu (g⁻¹*h)
    _=dist (g • u) (h • w):=by rw [←he];exact (g.val.dist_eq _ _).symm

/-- Actual distinct orbit centers have an area-null equidistant locus. -/
theorem native_equidistant_volume_zero {a b : ℍ} (hab : a≠b) :
    volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HEquidistantLocus a b)=0 := by
  obtain ⟨L,hL⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_hEquidistantLine hab
  rw [←hL]
  exact L.volume_zero

/-- A free actual center makes the literal closed Dirichlet domain a genuine
Mathlib measure fundamental domain, for full native groups including reflections. -/
theorem nativeClosedDirichlet_measureFundamentalDomain
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] (w : ℍ)
    (hw : ∀g : H,g • w=w →g=1) :
    MeasureTheory.IsFundamentalDomain H (nativeClosedDirichlet H w) volume := by
  refine ⟨(nativeClosedDirichlet_isClosed H w).measurableSet.nullMeasurableSet,
    Filter.Eventually.of_forall (nativeClosedDirichlet_meets_orbit H
      (nativeIsometrySubgroup_discontinuous H) w),?_⟩
  intro g h hne
  have hcent : g • w≠h • w := by
    intro he
    have hh : (h⁻¹*g) • w=w := by rw [mul_smul,he,inv_smul_smul]
    have hk:=hw (h⁻¹*g) hh
    exact hne (inv_mul_eq_one.mp hk).symm
  apply measure_mono_null (t:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HEquidistantLocus (g • w) (h • w)) _
    (native_equidistant_volume_zero hcent)
  rintro z ⟨hg,hh⟩
  exact le_antisymm (nativeClosedDirichlet_translate_comparison H w g h hg)
    (nativeClosedDirichlet_translate_comparison H w h g hh)

/-- The actual quotient area agrees with the area of any literal free-center
Dirichlet domain; the Mathlib covolume has a genuine fundamental domain here. -/
theorem nativeClosedDirichlet_covolume
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] (w : ℍ)
    (hw : ∀g : H,g • w=w →g=1) :
    MeasureTheory.covolume H ℍ volume=volume (nativeClosedDirichlet H w) := by
  let : Countable H:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeDiscreteIsometrySubgroup_countable H
  let : ContinuousConstSMul H ℍ:=⟨fun g=>g.val.continuous⟩
  exact (nativeClosedDirichlet_measureFundamentalDomain H w hw).covolume_eq_volume volume

/-- A genuine measure on the actual full-native orbit quotient, obtained by
pushing the original hyperbolic volume on the literal closed Dirichlet region. -/
def nativeDirichletQuotientMeasure (H : Subgroup (ℍ≃ᵢℍ)) (w : ℍ) :
    Measure (Quotient (MulAction.orbitRel H ℍ)) :=
  (volume.restrict (nativeClosedDirichlet H w)).map (Quotient.mk _)

/-- The measure on the literal orbit quotient is independent of the chosen
free center, and indeed of the chosen genuine measure fundamental domain. -/
theorem nativeDirichletQuotientMeasure_eq
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] (w : ℍ)
    (hw : ∀g : H,g • w=w →g=1) (Q : Set ℍ)
    (hQ : MeasureTheory.IsFundamentalDomain H Q volume) :
    nativeDirichletQuotientMeasure H w=
      (volume.restrict Q).map (Quotient.mk (MulAction.orbitRel H ℍ)) := by
  let : Countable H:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeDiscreteIsometrySubgroup_countable H
  let : ContinuousConstSMul H ℍ:=⟨fun g=>g.val.continuous⟩
  exact (nativeClosedDirichlet_measureFundamentalDomain H w hw).quotientMeasure_eq volume hQ

/-- The total area of the actual orbit quotient is precisely the canonical
Mathlib covolume, rather than an independently assigned numerical formula. -/
theorem nativeDirichletQuotientMeasure_univ
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] (w : ℍ)
    (hw : ∀g : H,g • w=w →g=1) :
    nativeDirichletQuotientMeasure H w univ=MeasureTheory.covolume H ℍ volume := by
  have hm : Measurable (Quotient.mk (MulAction.orbitRel H ℍ)):=
    fun _ h=>measurableSet_quotient.mp h
  rw [nativeDirichletQuotientMeasure,Measure.map_apply hm MeasurableSet.univ]
  simp only [preimage_univ,Measure.restrict_apply_univ]
  exact (nativeClosedDirichlet_covolume H w hw).symm

/-- Away from an actual null union of original translated boundaries, the true
local angular sum equals the literal orbital membership count. -/
theorem _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry.ae_angularMultiplicity_eq_orbital
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    ∀ᵐz : ℍ∂volume,_root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity H P.interior z=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitalCoverMultiplicity H P.interior z := by
  have ha : ∀ᵐz : ℍ∂volume,z∉⋃g : H,g • P.boundary:=
    (measure_eq_zero_iff_ae_notMem).mp (G.translated_boundary_volume_zero H)
  filter_upwards [ha] with z hz
  apply _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity_eq_orbital_off_frontiers
  intro g hg
  change z∈frontier (g.val.toHomeomorph '' P.interior) at hg
  rw [←g.val.toHomeomorph.image_frontier,G.frontier_boundary] at hg
  exact hz (mem_iUnion.mpr ⟨g,hg⟩)

/-- Integrating the genuinely proved angular multiplicity yields the area of the
original open polygon as the integer multiple of the actual quotient covolume. -/
theorem _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry.area_eq_integer_mul_covolume
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] (w : ℍ)
    (hw : ∀g : H,g • w=w →g=1) (k : ℕ)
    (hk : ∀z : ℍ,_root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity H P.interior z=k) :
    volume P.interior=(k : ℝ≥0∞)*MeasureTheory.covolume H ℍ volume := by
  let : Countable H:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeDiscreteIsometrySubgroup_countable H
  let : ContinuousConstSMul H ℍ:=⟨fun g=>g.val.continuous⟩
  have ha : ∀ᵐz : ℍ∂volume,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitalCoverMultiplicity H P.interior z=k := by
    filter_upwards [G.ae_angularMultiplicity_eq_orbital H] with z hz
    exact hz.symm.trans (hk z)
  rw [nativeClosedDirichlet_covolume H w hw]
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.measure_eq_mul_of_ae_orbitalCoverMultiplicity volume
    (nativeClosedDirichlet_measureFundamentalDomain H w hw) G.interior_open.measurableSet k
    (ae_restrict_of_ae ha)

/-- Every actual discrete full native isometry group has a genuine hyperbolic
measure fundamental domain; the existence is proved and not assumed. -/
theorem nativeDiscreteIsometrySubgroup_hasFundamentalDomain
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    MeasureTheory.HasFundamentalDomain H ℍ volume := by
  obtain ⟨w,hw⟩:=nativeDiscreteIsometrySubgroup_exists_free_point H
  exact (nativeClosedDirichlet_measureFundamentalDomain H w hw).hasFundamentalDomain volume

/-- The genuine hyperbolic measure on the actual full-native orbit quotient.
A free center exists by the null fixed-locus argument; the following theorem
shows that this measure is independent of every genuine fundamental-domain choice. -/
def nativeHyperbolicQuotientMeasure
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    Measure (Quotient (MulAction.orbitRel H ℍ)) :=
  nativeDirichletQuotientMeasure H (nativeDiscreteIsometrySubgroup_exists_free_point H).choose

/-- The actual quotient measure is the push-forward of original hyperbolic
volume restricted to any genuine measure fundamental domain. -/
theorem nativeHyperbolicQuotientMeasure_eq
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] (Q : Set ℍ)
    (hQ : MeasureTheory.IsFundamentalDomain H Q volume) :
    nativeHyperbolicQuotientMeasure H=
      (volume.restrict Q).map (Quotient.mk (MulAction.orbitRel H ℍ)) :=
  nativeDirichletQuotientMeasure_eq H _
    (nativeDiscreteIsometrySubgroup_exists_free_point H).choose_spec Q hQ

/-- The area of the actual hyperbolic orbit quotient equals the canonical
covolume and is thus independent of all choices of free center and domain. -/
theorem nativeHyperbolicQuotientMeasure_univ
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    nativeHyperbolicQuotientMeasure H univ=MeasureTheory.covolume H ℍ volume :=
  nativeDirichletQuotientMeasure_univ H _
    (nativeDiscreteIsometrySubgroup_exists_free_point H).choose_spec

/--
For the original open Jordan polygon and original side
pairing: the same positive integer gives the entire actual angular sum at every
physical point and multiplies the genuine area of the actual orbit quotient.
-/
theorem nativeJordan_exists_positive_constant_angularMultiplicity_and_area_eq_multiple_quotient
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ}
    (C : Set ℂ) (hC : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C) (hbound :
      C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=_root_.LowDimensionalTopology.Geometry.Polygon.nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicSideIntervals P) (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices →S.OppositeSideNeighborhoods s x) :
    ∃k : ℕ,0<k ∧
      (∀z : ℍ,_root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity S.Generated P.interior z=k
        ∧
        _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicityRadians S.Generated P.interior z=2*Real.pi*(k : ℝ)) ∧
      volume P.interior=(k : ℝ≥0∞)*nativeHyperbolicQuotientMeasure S.Generated univ := by
  obtain ⟨k,hk,hAll⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeJordan_angularMultiplicity_positive_integer C hC hbound
    hInside hBoundary D S hP hOpp
  refine ⟨k,hk,hAll,?_⟩
  let G:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  obtain ⟨w,hw⟩:=nativeDiscreteIsometrySubgroup_exists_free_point S.Generated
  rw [nativeHyperbolicQuotientMeasure_univ]
  exact G.area_eq_integer_mul_covolume S.Generated w hw k (fun z=>(hAll z).1)

end LowDimensionalTopology.Geometry.Fuchsian
