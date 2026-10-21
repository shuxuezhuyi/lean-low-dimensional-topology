/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Gram.DirichletHorocycleGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonIdealCycles
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GenericDirichletCenters
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GenericDirichletParabolic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped UpperHalfPlane MatrixGroups OnePoint Complex.UnitDisc Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
local instance genericHorocycleSphereMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance genericHorocycleSphereBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- A genuine determinant-one lift of each original action in the fixed half-plane chart. -/
def UnitDiscFuchsianGroup.dirichletRealLift {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  Classical.choose (P.halfPlaneAction_real_lift g)

theorem UnitDiscFuchsianGroup.dirichletRealLift_projection {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (P.dirichletRealLift g)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*g.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius :=
  (Classical.choose_spec (P.halfPlaneAction_real_lift g)).1

theorem UnitDiscFuchsianGroup.dirichletRealLift_action {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (w : P.domain.carrier) :
    P.dirichletRealLift g • P.halfPlaneCoordinate w=P.halfPlaneCoordinate (g • w) := by
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.dirichletRealLift,(Classical.choose_spec
    (P.halfPlaneAction_real_lift g)).2,P.halfPlaneAction_apply,
    P.halfPlaneCoordinate.symm_apply_apply]

/-- The independently proved genuine density-area null locus transports to the original domain. -/
theorem UnitDiscFuchsianGroup.horocycleGram_area_zero {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hP : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLHorocycleGramBivariate A B≠0) :
    P.area {w | _root_.LowDimensionalTopology.Geometry.Hyperbolic.horocycleMetricGram (P.halfPlaneCoordinate w)
      (A • P.halfPlaneCoordinate w) (B • P.halfPlaneCoordinate w)=0}=0 := by
  have hc : IsClosed {z : ℍ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.horocycleMetricGram z (A • z) (B •
    z)=0} :=
    isClosed_eq (by unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.horocycleMetricGram;fun_prop) continuous_const
  have hm : MeasurableSet {w | _root_.LowDimensionalTopology.Geometry.Hyperbolic.horocycleMetricGram
    (P.halfPlaneCoordinate w)
      (A • P.halfPlaneCoordinate w) (B • P.halfPlaneCoordinate w)=0} :=
    hc.measurableSet.preimage P.halfPlaneCoordinate.continuous.measurable
  rw [P.area_eq_halfPlane_volume _ hm]
  have he : P.halfPlaneCoordinate '' {w | _root_.LowDimensionalTopology.Geometry.Hyperbolic.horocycleMetricGram
    (P.halfPlaneCoordinate w)
      (A • P.halfPlaneCoordinate w) (B • P.halfPlaneCoordinate w)=0}=
      {z : ℍ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.horocycleMetricGram z (A • z) (B • z)=0} :=
    by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact hw
      · intro hz
        refine ⟨P.halfPlaneCoordinate.symm z,?_,P.halfPlaneCoordinate.apply_symm_apply z⟩
        change _root_.LowDimensionalTopology.Geometry.Hyperbolic.horocycleMetricGram z (A • z) (B • z)=0 at hz
        change _root_.LowDimensionalTopology.Geometry.Hyperbolic.horocycleMetricGram (P.halfPlaneCoordinate
          (P.halfPlaneCoordinate.symm z))
          (A • P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z))
          (B • P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z))=0
        simpa only [P.halfPlaneCoordinate.apply_symm_apply] using hz
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLHorocycleGram_volume_zero A B hP

/-- The exceptional centres use only a countable pair of original elements, never an uncountable union over ideal points. -/
def dirichletHorocycleBadCenters {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : Set P.domain.carrier :=
  ⋃g : H,⋃h : H,{w | _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLHorocycleGramBivariate (P.dirichletRealLift
    g) (P.dirichletRealLift h)≠0 ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.horocycleMetricGram (P.halfPlaneCoordinate w)
      (P.halfPlaneCoordinate (g • w)) (P.halfPlaneCoordinate (h • w))=0}

theorem dirichletHorocycleBadCenters_area_zero {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : P.area (dirichletHorocycleBadCenters P)=0 := by
  classical
  let : Countable H:=P.countable
  apply measure_iUnion_null
  intro g
  apply measure_iUnion_null
  intro h
  by_cases hQ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLHorocycleGramBivariate (P.dirichletRealLift
    g) (P.dirichletRealLift h)=0
  · simp [hQ]
  · have hn:=P.horocycleGram_area_zero (P.dirichletRealLift g) (P.dirichletRealLift h) hQ
    simpa only [hQ,ne_eq,not_false_eq_true,true_and,P.dirichletRealLift_action] using hn

/-- At every nonexceptional centre, a true common horocycle forces the actual independently defined Gram polynomial to vanish. -/
theorem dirichlet_good_center_horocycle_polynomial_zero {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : w∉dirichletHorocycleBadCenters P)
    (g h : H) {ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} {S : Set ℍ} (hS :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHorocycleAt ξ S)
    (hwS : P.halfPlaneCoordinate w∈S) (hgwS : P.halfPlaneCoordinate (g • w)∈S)
    (hhwS : P.halfPlaneCoordinate (h • w)∈S) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLHorocycleGramBivariate (P.dirichletRealLift g) (P.dirichletRealLift h)=0 := by
  by_contra hQ
  apply hw
  exact mem_iUnion.mpr ⟨g,mem_iUnion.mpr ⟨h,hQ,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.horocycleMetricGram_eq_zero_of_horocycle hS hwS hgwS hhwS⟩⟩



/-- An original nonidentity element has a nonidentity genuine projective lift. -/
theorem UnitDiscFuchsianGroup.dirichletRealLift_ne_one {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (hg : g≠1) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (P.dirichletRealLift g)≠1 := by
  intro he
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*g.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius=1:=(P.dirichletRealLift_projection g).symm.trans he
  have hh:=congrArg (fun f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*f*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹) hc
  have hv : g.val=1:=by simpa [mul_assoc] using hh
  exact hg (Subtype.ext hv)

/-- Distinct original elements remain distinct genuine projective lifts. -/
theorem UnitDiscFuchsianGroup.dirichletRealLift_ne {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g h : H) (hne : g≠h) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (P.dirichletRealLift g)≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (P.dirichletRealLift h) := by
  intro he
  apply hne
  apply Subtype.ext
  have hh:=(P.dirichletRealLift_projection g).symm.trans (he.trans (P.dirichletRealLift_projection h))
  exact mul_left_cancel (mul_right_cancel hh)

/-- For a genuine free centre outside the countable null union, three actual orbit points on a genuine horocycle force the actual ideal centre to be fixed. -/
theorem dirichlet_good_center_horocycle_fixed {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (hgood : w∉dirichletHorocycleBadCenters P) (g h : H) (hg : g≠1) (hh : h≠1) (hgh : g≠h)
    {ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} {S : Set ℍ} (hS :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHorocycleAt ξ S)
    (hwS : P.halfPlaneCoordinate w∈S) (hgwS : P.halfPlaneCoordinate (g • w)∈S)
    (hhwS : P.halfPlaneCoordinate (h • w)∈S) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (P.dirichletRealLift g)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (P.dirichletRealLift h)) ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (P.dirichletRealLift g)).val ξ=ξ ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (P.dirichletRealLift h)).val ξ=ξ := by
  have hQ:=dirichlet_good_center_horocycle_polynomial_zero P w hgood g h hS hwS hgwS hhwS
  have hgw : w≠g • w:=by intro he;exact hg (hw g he.symm)
  have hhw : w≠h • w:=by intro he;exact hh (hw h he.symm)
  have hghw : g • w≠h • w:=(dirichlet_center_orbit_injective P w hw).ne hgh
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLHorocycleGram_zero_fixes_horocycle_center (P.dirichletRealLift g) (P.dirichletRealLift h)
    (P.dirichletRealLift_ne_one g hg) (P.dirichletRealLift_ne_one h hh) (P.dirichletRealLift_ne g h hgh) hQ hS
    (P.halfPlaneCoordinate w)
  · rw [P.dirichletRealLift_action]
    exact P.halfPlaneCoordinate.injective.ne hgw
  · rw [P.dirichletRealLift_action]
    exact P.halfPlaneCoordinate.injective.ne hhw
  · rw [P.dirichletRealLift_action,P.dirichletRealLift_action]
    exact P.halfPlaneCoordinate.injective.ne hghw
  · exact hwS
  · rwa [P.dirichletRealLift_action]
  · rwa [P.dirichletRealLift_action]

/-- The required good centres form a genuine full-area set for the original invariant density. -/
theorem dirichletHorocycle_ae_good {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H) :
    ∀ᵐw : P.domain.carrier ∂P.area,IsDirichletCenter P w ∧ w∉dirichletHorocycleBadCenters P := by
  have hf:=(measure_eq_zero_iff_ae_notMem.mp (fuchsianEllipticPoints_area_zero P))
  have hg:=(measure_eq_zero_iff_ae_notMem.mp (dirichletHorocycleBadCenters_area_zero P))
  filter_upwards [hf,hg] with w hw hgood
  exact ⟨not_not.mp hw,hgood⟩



/-- A literal finite Euclidean closure endpoint of the true disc carrier is an actual ideal endpoint. -/
theorem discLine_idealEndpoint_of_euclideanClosure (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (u :
  Circle)
    (hu : (u:ℂ)∈closure (((↑):𝔻→ℂ) '' L.carrier)) : ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈L.idealEndpoints := by
  refine ⟨?_,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary _).mpr
    (Circle.norm_coe u)⟩
  have him : ((↑):ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' closure (((↑):𝔻→ℂ) '' L.carrier) ⊆
      closure (((↑):ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' (((↑):𝔻→ℂ) '' L.carrier)) :=
    image_closure_subset_closure_image OnePoint.continuous_coe
  have he:=him ⟨(u:ℂ),hu,rfl⟩
  simpa only [image_image,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscPoint] using he

/-- A true endpoint of an actual Dirichlet side lies on the genuine horocycle shared by the centre and that side's actual orbit label. -/
theorem dirichlet_side_endpoint_horocycle {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (g : H) (hg : g≠1) (S : Set P.domain.carrier) (hS : S⊆dirichletBisector P w g)
    (u : Circle) (hu : IsFuchsianSideIdealEndpoint P S u) :
    ∃U : Set 𝔻,_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscHorocycleAt ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) U ∧
      P.finiteCoordinate w∈U ∧ P.finiteCoordinate (g • w)∈U := by
  have hgw : w≠g • w:=by intro he;exact hg (hw g he.symm)
  have hab : P.finiteCoordinate w≠P.finiteCoordinate (g • w):=P.finiteCoordinate.injective.ne hgw
  obtain ⟨N,hN,_hunique⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discPerpendicularBisector hab
  have hsub : P.finiteCoordinate '' S⊆N.carrier := by
    rintro _ ⟨x,hx,rfl⟩
    rw [hN.carrier_eq hab]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.finiteCoordinate x) (P.finiteCoordinate w)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (P.finiteCoordinate x) (P.finiteCoordinate (g • w))
    rw [←P.hyperbolicDist_eq_discPathDist,←P.hyperbolicDist_eq_discPathDist]
    exact hS hx
  have hcl : (u:ℂ)∈closure (((↑):𝔻→ℂ) '' N.carrier) := by
    apply closure_mono _ hu
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨P.finiteCoordinate x,hsub ⟨x,hx,rfl⟩,rfl⟩
  have hend:=discLine_idealEndpoint_of_euclideanClosure N u hcl
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discParabolicPencil_perpendicularBisector_iff
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary _).mpr (Circle.norm_coe
      u)) hab hN).mp hend



/-- A genuine proper ideal Dirichlet vertex at a good centre is fixed by an actual nonidentity parabolic side label. -/
theorem dirichlet_good_proper_vertex_parabolic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (hgood : w∉dirichletHorocycleBadCenters P) (u : Circle)
    (hu : IsProperFuchsianInfiniteVertex P (dirichletDomain P w) u) :
    ∃g : H,g≠1 ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val ∧ g.val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  obtain ⟨_huIdeal,S,T,hS,hT,hST,huS,huT⟩:=hu
  obtain ⟨g,hg,hSeq⟩:=hS.1
  obtain ⟨h,hh,hTeq⟩:=hT.1
  have hgh : g≠h := by intro he;apply hST;rw [hSeq,hTeq,he]
  have hsubS : S⊆dirichletBisector P w g := by rw [hSeq];exact dirichlet_closedTile_intersection_subset_bisector P w g
  have hsubT : T⊆dirichletBisector P w h := by rw [hTeq];exact dirichlet_closedTile_intersection_subset_bisector P w h
  obtain ⟨U,hU,hwU,hgwU⟩:=dirichlet_side_endpoint_horocycle P w hw g hg S hsubS u huS
  obtain ⟨V,hV,hwV,hhwV⟩:=dirichlet_side_endpoint_horocycle P w hw h hh T hsubT u huT
  let ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  have hUH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHorocycleAt ξ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' U):=hU.cayley_inverse_image
  have hVH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHorocycleAt ξ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' V):=hV.cayley_inverse_image
  have hwUH : P.halfPlaneCoordinate w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' U:=⟨P.finiteCoordinate w,hwU,rfl⟩
  have hgwUH : P.halfPlaneCoordinate (g •
    w)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' U:=⟨P.finiteCoordinate (g • w),hgwU,rfl⟩
  have hwVH : P.halfPlaneCoordinate w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' V:=⟨P.finiteCoordinate w,hwV,rfl⟩
  have hhwVH : P.halfPlaneCoordinate (h •
    w)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' V:=⟨P.finiteCoordinate (h • w),hhwV,rfl⟩
  obtain ⟨W,_hW,hunique⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_hHorocycleAt_through ξ hUH.center_mem_idealBoundary (P.halfPlaneCoordinate w)
  have hVU : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' V=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' U :=
    (hunique _ ⟨hVH,hwVH⟩).trans (hunique _ ⟨hUH,hwUH⟩).symm
  rw [hVU] at hhwVH
  obtain ⟨hAg,_hAh,hAf,_hBf⟩:=dirichlet_good_center_horocycle_fixed P w hw hgood g h hg hh hgh hUH hwUH hgwUH hhwVH
  have hconj : IsConj g.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (P.dirichletRealLift g)) := by
    apply isConj_iff.mpr
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹,?_⟩
    simpa only [inv_inv] using (P.dirichletRealLift_projection g).symm
  have hpara : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj hconj).mpr hAg
  have hξ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ξ=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=_
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.apply_symm_apply _
  rw [P.dirichletRealLift_projection] at hAf
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm (g.val.val
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ξ))=ξ at hAf
  have hfixed:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val hAf
  rw [Equiv.apply_symm_apply,hξ] at hfixed
  exact ⟨g,hg,hpara,hfixed⟩

/-- The genuine ideal vertex itself belongs to its literal original orbit cycle. -/
theorem proper_dirichlet_vertex_mem_idealCycle {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (u : Circle)
    (hu : IsProperFuchsianInfiniteVertex P (dirichletDomain P w) u) :
    ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈fuchsianPolygonIdealCycle P (dirichletDomain P w) ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  refine ⟨⟨(u:ℂ),hu.1,rfl⟩,MulAction.mem_orbit_self _⟩

/-- The proper ideal-vertex clause, for the original density area and the literal original ideal cycle. -/
theorem ae_dirichlet_proper_ideal_vertex_parabolic_fixer_and_singleton_cycle {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) :
    ∀ᵐw : P.domain.carrier ∂P.area,IsDirichletCenter P w ∧
      ∀u : Circle,IsProperFuchsianInfiniteVertex P (dirichletDomain P w) u→
        ∃g : H,g≠1 ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val ∧ g.val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
          fuchsianPolygonIdealCycle P (dirichletDomain P w) ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)={((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)} := by
  filter_upwards [dirichletHorocycle_ae_good P,ae_dirichlet_parabolic_fixed_cycle_singleton_proper_vertex
    P] with w hw hp
  refine ⟨hw.1,?_⟩
  intro u hu
  obtain ⟨g,hg,hpara,hfix⟩:=dirichlet_good_proper_vertex_parabolic P w hw.1 hw.2 u hu
  obtain ⟨v,he,_hv⟩:=hp.2 g hpara ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hfix
  have huCycle:=proper_dirichlet_vertex_mem_idealCycle P w u hu
  rw [he,mem_singleton_iff] at huCycle
  exact ⟨g,hg,hpara,hfix,he.trans (congrArg Set.singleton huCycle.symm)⟩

end LowDimensionalTopology.Geometry.Fuchsian
