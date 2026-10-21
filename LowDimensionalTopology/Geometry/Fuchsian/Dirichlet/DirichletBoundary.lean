/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriQuadrilaterals
@[expose] public section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane Complex.UnitDisc RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
noncomputable section

theorem dirichlet_closedTile_intersection_subset_bisector {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (g : H) :
    closure (dirichletDomain P w)∩fuchsianDomainTile P (dirichletDomain P w) g⊆dirichletBisector P w g := by
  rintro x ⟨hx,u,hu,rfl⟩
  have he:=dirichlet_closed_orbit_equal_distance P w u g hu hx
  change P.hyperbolicDist (g • u) w=P.hyperbolicDist (g • u) (g • w)
  rw [P.hyperbolicDist_smul]
  exact he.symm

theorem dirichlet_side_bisector {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) {S : Set P.domain.carrier}
    (hS : IsFuchsianPolygonSide P (dirichletDomain P w) S) :
    ∃g : H,g≠1 ∧ S⊆dirichletBisector P w g := by
  obtain ⟨⟨g,hg,rfl⟩,_⟩:=hS
  exact ⟨g,hg,dirichlet_closedTile_intersection_subset_bisector P w g⟩

theorem dirichlet_center_orbit_injective {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    Function.Injective (fun g : H=>g • w) := by
  intro g h he
  change g • w=h • w at he
  have hfix : (h⁻¹*g) • w=w:=by rw [mul_smul,he,inv_smul_smul]
  have hh:=hw (h⁻¹*g) hfix
  exact (eq_of_inv_mul_eq_one hh).symm

theorem dirichlet_vertex_bisectors {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    {x : P.domain.carrier} (hx : IsFuchsianPolygonVertex P (dirichletDomain P w) x) :
    ∃g h : H,g≠1 ∧ h≠1 ∧ g≠h ∧ g • w≠h • w ∧
      x∈dirichletBisector P w g∩dirichletBisector P w h := by
  obtain ⟨g,h,hg,hh,hgh,he⟩:=hx
  have hxT : x∈closure (dirichletDomain P w)∩fuchsianDomainTile P (dirichletDomain P w) g∩
      fuchsianDomainTile P (dirichletDomain P w) h:=by rw [he]; exact mem_singleton x
  exact ⟨g,h,hg,hh,hgh,fun heq=>hgh (dirichlet_center_orbit_injective P w hw heq),
    dirichlet_closedTile_intersection_subset_bisector P w g hxT.1,
    dirichlet_closedTile_intersection_subset_bisector P w h ⟨hxT.1.1,hxT.2⟩⟩

/-- Two heights on the vertical axis determine the two scalar coefficients of a bisector. -/
theorem vertical_bisector_profile {a b : ℍ}
    (h1 : dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 1 (by norm_num)) a=dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 1 (by norm_num)) b)
    (h2 : dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 2 (by norm_num)) a=dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 2 (by norm_num)) b) :
    a.im=b.im ∧ a.re^2=b.re^2 := by
  have hc1:=congrArg Real.cosh h1
  have hc2:=congrArg Real.cosh h2
  simp only [UpperHalfPlane.cosh_dist'] at hc1 hc2
  change ((0-a.re)^2+1^2+a.im^2)/(2*1*a.im)=((0-b.re)^2+1^2+b.im^2)/(2*1*b.im) at hc1
  change ((0-a.re)^2+2^2+a.im^2)/(2*2*a.im)=((0-b.re)^2+2^2+b.im^2)/(2*2*b.im) at hc2
  norm_num at hc1 hc2
  have hh1 : (a.re^2+1+a.im^2)*b.im=(b.re^2+1+b.im^2)*a.im:=by
    field_simp at hc1
    nlinarith only [hc1]
  have hh2 : (a.re^2+4+a.im^2)*b.im=(b.re^2+4+b.im^2)*a.im:=by
    field_simp at hc2
    nlinarith only [hc2]
  have hi : a.im=b.im:=by linarith
  refine ⟨hi,?_⟩
  rw [hi] at hh1
  exact mul_right_cancel₀ b.im_ne_zero (by nlinarith only [hh1])


theorem hEquidistantLocus_right_injective {a b c : ℍ} (hab : a≠b) (hac : a≠c)
    (he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HEquidistantLocus a b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HEquidistantLocus a c) : b=c := by
  obtain ⟨L,hL⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_hEquidistantLine hab
  obtain ⟨g,_hg,hg⟩:=L.exists_normalizer
  have hp (t : ℝ) (ht : 0<t) : g⁻¹ • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht∈L.carrier:=by
    rw [hg]
    change (g • (g⁻¹ • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht)).re=0
    rw [smul_inv_smul]
    rfl
  have hprof (t : ℝ) (ht : 0<t) :
      dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht) (g •
        a)=dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht) (g • b) ∧
      dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht) (g • a)=dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht) (g • c):=by
    have hb : g⁻¹ • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.HEquidistantLocus a b:=hL ▸ hp t ht
    have hc : g⁻¹ • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.HEquidistantLocus a c:=he ▸ hb
    change dist (g⁻¹ • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht) a=dist (g⁻¹ •
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht) b at hb
    change dist (g⁻¹ • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht) a=dist (g⁻¹ •
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht) c at hc
    rw [←(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).dist_eq (g⁻¹ •
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht) a,
      ←(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).dist_eq (g⁻¹ •
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht) b,smul_inv_smul] at hb
    rw [←(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).dist_eq (g⁻¹ •
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht) a,
      ←(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).dist_eq (g⁻¹ •
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht) c,smul_inv_smul] at hc
    exact ⟨hb,hc⟩
  have hb:=vertical_bisector_profile (hprof 1 (by norm_num)).1 (hprof 2 (by norm_num)).1
  have hc:=vertical_bisector_profile (hprof 1 (by norm_num)).2 (hprof 2 (by norm_num)).2
  have hbNe : (g • a).re≠(g • b).re:=by
    intro hr
    apply hab
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).injective
    exact UpperHalfPlane.ext (Complex.ext hr hb.1)
  have hcNe : (g • a).re≠(g • c).re:=by
    intro hr
    apply hac
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).injective
    exact UpperHalfPlane.ext (Complex.ext hr hc.1)
  have hbF : ((g • a).re-(g • b).re)*((g • a).re+(g • b).re)=0:=by nlinarith only [hb.2]
  have hcF : ((g • a).re-(g • c).re)*((g • a).re+(g • c).re)=0:=by nlinarith only [hc.2]
  have hbS:=(mul_eq_zero.mp hbF).resolve_left (sub_ne_zero.mpr hbNe)
  have hcS:=(mul_eq_zero.mp hcF).resolve_left (sub_ne_zero.mpr hcNe)
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).injective
  have hr : (g • b).re=(g • c).re:=by linarith only [hbS,hcS]
  exact UpperHalfPlane.ext (Complex.ext hr (hb.1.symm.trans hc.1))

theorem dirichletBisector_label_injective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    {g h : H} (hg : g≠1) (hh : h≠1) (he : dirichletBisector P w g=dirichletBisector P w h) : g=h := by
  have hgW : P.halfPlaneCoordinate w≠P.halfPlaneCoordinate (g • w):=by
    intro heq
    exact hg (hw g (P.halfPlaneCoordinate.injective heq).symm)
  have hhW : P.halfPlaneCoordinate w≠P.halfPlaneCoordinate (h • w):=by
    intro heq
    exact hh (hw h (P.halfPlaneCoordinate.injective heq).symm)
  have hEq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HEquidistantLocus (P.halfPlaneCoordinate
    w) (P.halfPlaneCoordinate (g • w))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HEquidistantLocus (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate (h • w)):=by
    rw [←dirichletBisector_halfPlane_image,←dirichletBisector_halfPlane_image,he]
  apply dirichlet_center_orbit_injective P w hw
  exact P.halfPlaneCoordinate.injective (hEquidistantLocus_right_injective hgW hhW hEq)

theorem dirichlet_vertex_distinct_bisectors {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    {x : P.domain.carrier} (hx : IsFuchsianPolygonVertex P (dirichletDomain P w) x) :
    ∃g h : H,g≠1 ∧ h≠1 ∧ dirichletBisector P w g≠dirichletBisector P w h ∧
      x∈dirichletBisector P w g∩dirichletBisector P w h := by
  obtain ⟨g,h,hg,hh,hgh,_hw,hxB⟩:=dirichlet_vertex_bisectors P w hw hx
  exact ⟨g,h,hg,hh,fun he=>hgh (dirichletBisector_label_injective P w hw hg hh he),hxB⟩

end
end LowDimensionalTopology.Geometry.Fuchsian
