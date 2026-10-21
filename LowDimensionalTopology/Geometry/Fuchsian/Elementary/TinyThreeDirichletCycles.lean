/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Elementary.DihedralParabolicPacking
public import LowDimensionalTopology.Geometry.Fuchsian.Elementary.TinyDihedralCone
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.NativeDirichletNearestCycles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Both physical points of the tiny family lie strictly outside the whole closed real cone. -/
theorem tinyDihedral_points_outside_realCone (t:ℝ) (ht:1<t) (htu:t<2) :
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (tinyDihedralVertex t ht
      htu)∉dihedralRealCone ∧
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (tinyDihedralCenter t ht htu)∉dihedralRealCone := by
  have hx:0<(t-1)/2:=by linarith only [ht]
  have hx1:(t-1)/2<1:=by linarith only [htu]
  have hy1:1≤t-((t-1)/2)^2:=by
    have hm:=mul_pos (sub_pos.mpr ht) (show 0<5-t by linarith only [htu])
    nlinarith only [hm]
  have hy:1≤Real.sqrt (t-((t-1)/2)^2):=by
    have hs:=Real.sq_sqrt (show 0≤t-((t-1)/2)^2 by linarith only [hy1])
    have hn:=Real.sqrt_nonneg (t-((t-1)/2)^2)
    nlinarith only [hs,hn,hy1]
  constructor
  · rw [_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint,coe_mem_dihedralRealCone]
    change ¬(|Real.sqrt (t-((t-1)/2)^2)|≤|(t-1)/2|)
    rw [abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos hx]
    linarith only [hy,hx1]
  · rw [_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint,coe_mem_dihedralRealCone]
    change ¬(|Real.sqrt (t-((t-1)/2)^2)|≤|-((t-1)/2)|)
    rw [abs_of_nonneg (Real.sqrt_nonneg _),abs_neg,abs_of_pos hx]
    linarith only [hy,hx1]

theorem tinyDihedral_points_mem_packingAnnulus (t:ℝ) (ht:1<t) (htu:t<2) :
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (tinyDihedralVertex t ht
      htu)∈dihedralPackingAnnulus (t^2) ∧
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (tinyDihedralCenter t ht htu)∈dihedralPackingAnnulus (t^2) := by
  simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint,coe_mem_dihedralPackingAnnulus,
    Real.sqrt_sq (show 0≤t by linarith only [ht])] using tinyDihedral_vertex_center_annulus t ht htu

/-- An actual parabolic extension preserves the genuine tiny circle's nearest-orbit property. -/
theorem tinyDihedral_extension_nearest (t:ℝ) (ht:1<t) (htu:t<2)
    (p ε:ℝ) (hε:0<ε)
    (hloc:(packingLocalizedDomain p ε hε)ᶜ⊆dihedralPackingAnnulus (t^2)∩dihedralRealCone)
    (hcone:∀u:ℍ,u.im≤|u.re|→dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu)<
      dist (tinyDihedralCenter t ht htu) u)
    (u:ℍ) (hu:_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint u∈MulAction.orbit
      (dihedralParabolicGroup (t^2) (by positivity) p ε hε)
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (tinyDihedralVertex t ht htu))) :
    dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu)≤
      dist (tinyDihedralCenter t ht htu) u := by
  obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp hu
  change g.val.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (tinyDihedralVertex t ht
    htu))=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint u at hg
  have hd:1<t^2:=by nlinarith only [ht]
  rcases dihedralParabolicGroup_orbit_cone (t^2) hd p ε hε hloc _
      (tinyDihedral_points_mem_packingAnnulus t ht htu).1
      (tinyDihedral_points_outside_realCone t ht htu).1 g with hc|⟨a,ha,he⟩
  · rw [hg,_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint,coe_mem_dihedralRealCone] at hc
    exact (hcone u (by simpa only [UpperHalfPlane.coe_im,UpperHalfPlane.coe_re,abs_of_pos u.im_pos] using hc)).le
  · apply tinyDihedral_nearest_orbit t ht htu u
    exact MulAction.mem_orbit_iff.mpr ⟨⟨a,ha⟩,he.trans hg⟩

/-- The entire enlarged original-group orbit still meets the actual nearest circle in exactly three points. -/
theorem tinyDihedral_extension_circle_eq_range (t:ℝ) (ht:1<t) (htu:t<2)
    (p ε:ℝ) (hε:0<ε)
    (hloc:(packingLocalizedDomain p ε hε)ᶜ⊆dihedralPackingAnnulus (t^2)∩dihedralRealCone)
    (hcone:∀u:ℍ,u.im≤|u.re|→dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu)<
      dist (tinyDihedralCenter t ht htu) u) :
    {u:ℍ | _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint u∈MulAction.orbit
      (dihedralParabolicGroup (t^2) (by positivity) p ε hε)
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (tinyDihedralVertex t ht htu)) ∧
      dist (tinyDihedralCenter t ht htu) u=dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu)}=
      Set.range (tinyDihedralCyclePoints t ht htu) := by
  ext u
  rw [←tinyDihedral_nearest_orbit_eq_range t ht htu]
  constructor
  · rintro ⟨hu,hr⟩
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp hu
    change g.val.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (tinyDihedralVertex t ht
      htu))=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint u at hg
    have hd:1<t^2:=by nlinarith only [ht]
    refine ⟨?_,hr⟩
    rcases dihedralParabolicGroup_orbit_cone (t^2) hd p ε hε hloc _
        (tinyDihedral_points_mem_packingAnnulus t ht htu).1
        (tinyDihedral_points_outside_realCone t ht htu).1 g with hc|⟨a,ha,he⟩
    · rw [hg,_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint,coe_mem_dihedralRealCone] at hc
      have h:=hcone u (by simpa only [UpperHalfPlane.coe_im,UpperHalfPlane.coe_re,abs_of_pos u.im_pos] using hc)
      exact (not_lt_of_ge hr.le h).elim
    · exact MulAction.mem_orbit_iff.mpr ⟨⟨a,ha⟩,he.trans hg⟩
  · rintro ⟨hu,hr⟩
    obtain ⟨a,ha⟩:=MulAction.mem_orbit_iff.mp hu
    exact ⟨MulAction.mem_orbit_iff.mpr
      ⟨⟨a.val,canonicalDihedralGroup_le_dihedralParabolicGroup (t^2) (by positivity) p ε hε a.property⟩,ha⟩,hr⟩

/--
genuine non-elementary original Dirichlet vertex cycles of length three
have no positive universal radius bound. The group, center, vertex and complete cycle are constructed.
-/
theorem exists_tiny_nonElementary_Dirichlet_three_cycle (δ:ℝ) (hδ:0<δ) :
    ∃H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃P:UnitDiscFuchsianGroup H,
      ∃w z:P.domain.carrier,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H ∧ IsDirichletCenter P w ∧
      IsConvexFuchsianPolygon P (dirichletDomain P w) ∧
      IsFuchsianPolygonVertex P (dirichletDomain P w) z ∧
      IsAccidentalFuchsianPoint P z ∧
      fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) z)=3 ∧
      0<P.hyperbolicDist w z ∧ P.hyperbolicDist w z<δ := by
  obtain ⟨t,ht,htu,hr,hcone⟩:=tinyDihedral_radius_avoids_real_cone δ hδ
  have hd:1<t^2:=by nlinarith only [ht]
  obtain ⟨p,ε,hε,_hp,_hp',hloc,P,hNE,hdata⟩:=exists_dihedralParabolicPacking (t^2) hd
  let H:=dihedralParabolicGroup (t^2) (by positivity) p ε hε
  let w:=tinyDihedralCenter t ht htu
  let z:=tinyDihedralVertex t ht htu
  let nativeTinyAction:=P.nativeAction
  have hzA:= (tinyDihedral_points_mem_packingAnnulus t ht htu).1
  have hwA:= (tinyDihedral_points_mem_packingAnnulus t ht htu).2
  have hzC:= (tinyDihedral_points_outside_realCone t ht htu).1
  have hwC:= (tinyDihedral_points_outside_realCone t ht htu).2
  have hwfree:∀g:H,g • w=w→g=1:=by
    intro g hg
    apply (hdata _ hwA hwC).2 g
    rw [P.nativeAction_boundary,hg]
  have hzfree:∀g:H,g • z=z→g=1:=by
    intro g hg
    apply (hdata _ hzA hzC).2 g
    rw [P.nativeAction_boundary,hg]
  have hmin:∀g:H,dist z w≤dist (g • z) w:=by
    intro g
    rw [dist_comm z w,dist_comm (g • z) w]
    exact tinyDihedral_extension_nearest t ht htu p ε hε hloc hcone (g • z)
      ((P.native_orbit_iff_sphere z _).mp (MulAction.mem_orbit _ _))
  have hcircle:{u:ℍ | u∈MulAction.orbit H z ∧ dist u w=dist z w}=
      range (tinyDihedralCyclePoints t ht htu):=by
    rw [←tinyDihedral_extension_circle_eq_range t ht htu p ε hε hloc hcone]
    ext u
    simp only [mem_ofPred_eq]
    rw [P.native_orbit_iff_sphere]
    simp only [w,z,dist_comm]
  obtain ⟨hcenter,hpoly,hvertex,hcard⟩:=P.cayley_three_cycle w z hwfree hmin
    (tinyDihedralCyclePoints t ht htu) (tinyDihedralCyclePoints_injective t ht htu) rfl hcircle
  refine ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H,P.cayleyData,
    P.cayleyCoordinate w,P.cayleyCoordinate z,hNE.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius,hcenter,hpoly,hvertex,
    (isAccidentalFuchsianPoint_iff_no_stabilizer _ _).mpr (P.cayleyCoordinate_free z hzfree),
    hcard,?_,?_⟩
  · rw [P.cayleyCoordinate_hyperbolicDist]
    apply dist_pos.mpr
    intro he
    have hh:=congrArg UpperHalfPlane.re he
    change -((t-1)/2)=(t-1)/2 at hh
    linarith only [hh,ht]
  · rw [P.cayleyCoordinate_hyperbolicDist]
    exact hr

end LowDimensionalTopology.Geometry.Fuchsian
