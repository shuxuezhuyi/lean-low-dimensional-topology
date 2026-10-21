/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.CrossingAxisHalfTurns
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.FuchsianDisplacementInvariants
public import LowDimensionalTopology.Geometry.Fuchsian.Geodesic.SimpleClosedCurves
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The genuine original-disc half-turn at an actual original point. -/
def FuchsianDisc.pointHalfTurn
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (x:(fuchsianGeometricDomain D).carrier) : Mobius.complexMobiusGroup :=
  D.halfPlaneNormalizer⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x))*
    D.halfPlaneNormalizer

theorem FuchsianDisc.pointHalfTurn_order
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (x:(fuchsianGeometricDomain D).carrier) : orderOf (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D x)=2 := by
  have hs:SemiconjBy D.halfPlaneNormalizer (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D x)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x))):=by
    change D.halfPlaneNormalizer*(D.halfPlaneNormalizer⁻¹*_*D.halfPlaneNormalizer)=
      _*D.halfPlaneNormalizer
    group
  exact (SemiconjBy.orderOf_eq _ hs).trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at _).1

theorem FuchsianDisc.pointHalfTurn_fixed
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (x:(fuchsianGeometricDomain D).carrier) : (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D x).val x.val=x.val := by
  have he:_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x)=
      D.halfPlaneNormalizer.val x.val:=geometricHalfPlaneChart_extended D _ _ x
  change (D.halfPlaneNormalizer⁻¹).val
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x))).val
      (D.halfPlaneNormalizer.val x.val))=x.val
  have hf:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x))).val
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x))=
      _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x):=by
    simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_fixed] using
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x))
        (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x)
  rw [←he,hf,he]
  exact inv_smul_smul D.halfPlaneNormalizer x.val

theorem FuchsianDisc.pointHalfTurn_preserves
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (x:(fuchsianGeometricDomain D).carrier) :
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D x).val '' D.carrier=D.carrier := by
  apply D.halfPlaneNormalizer.val.injective.image_injective
  rw [←_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image,D.halfPlaneNormalizer_image]
  have he:D.halfPlaneNormalizer*_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D x*D.halfPlaneNormalizer⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x)):=by
    dsimp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn]
    group
  rw [he]
  exact realSLMobius_image_openHalfPlane _

/-- Membership of a genuine original axis is exactly membership in its constructed native axis. -/
theorem FuchsianAxisModel.hyperbolicCoordinate_mem
    {H:Subgroup Mobius.complexMobiusGroup}
    {D:FuchsianDisc H} {f:Mobius.complexMobiusGroup} (M:FuchsianAxisModel D f)
    (x:(fuchsianGeometricDomain D).carrier) (hx:x.val∈M.carrier) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x∈M.line.carrier := by
  have he:_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x)=
      D.halfPlaneNormalizer.val x.val:=geometricHalfPlaneChart_extended D _ _ x
  have hm:D.halfPlaneNormalizer.val x.val∈M.nativeCarrier:=by
    rw [←M.carrier_image]
    exact mem_image_of_mem _ hx
  obtain ⟨z,hz,hzx⟩:=hm
  have hh:z=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x:=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective (hzx.trans he.symm)
  exact hh ▸ hz

/-- Actual canonical half-turns pull back along the whole original-disc chart. -/
theorem FuchsianDisc.pointHalfTurn_chart
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (y:ℍ) : _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D ((_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).symm y)=
      D.halfPlaneNormalizer⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL y)*D.halfPlaneNormalizer := by
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn,
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).apply_symm_apply]


/-- The source translation length as an actual displacement infimum over the original whole disc. -/
def FuchsianDisc.translationLength
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (f:H) : ℝ:=
  sInf (Set.range (fun x:(fuchsianGeometricDomain D).carrier=>_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D x (f•x)))

theorem FuchsianAxisModel.coordinate_action
    {H:Subgroup Mobius.complexMobiusGroup}
    {D:FuchsianDisc H} (f:H) (M:FuchsianAxisModel D f.val)
    (x:(fuchsianGeometricDomain D).carrier) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D (f•x)=M.matrix•_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x := by
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  change (((geometricHalfPlaneChart D D.halfPlaneNormalizer _ (f•x):ℍ):ℂ):Mobius.ExtendedComplex)=
    (((M.matrix•geometricHalfPlaneChart D D.halfPlaneNormalizer _ x:ℍ):ℂ):Mobius.ExtendedComplex)
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action, geometricHalfPlaneChart_extended,
    geometricHalfPlaneChart_extended, M.projection]
  change D.halfPlaneNormalizer•(f.val•x.val)=
    (D.halfPlaneNormalizer*f.val*D.halfPlaneNormalizer⁻¹)•(D.halfPlaneNormalizer•x.val)
  simp only [mul_smul,inv_smul_smul]

theorem FuchsianAxisModel.translationLength
    {H:Subgroup Mobius.complexMobiusGroup}
    {D:FuchsianDisc H} (f:H) (M:FuchsianAxisModel D f.val) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry M.matrix) := by
  have he:(fun x:(fuchsianGeometricDomain D).carrier=>_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D x (f•x))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry M.matrix) ∘ _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D:=by
    funext x
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist,
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.coordinate_action f M]
    rfl
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength,he,range_comp,
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).surjective.range_eq,image_univ]

/-- The original arbitrary-disc crossing-axis construction. All true half-turns, original centers,
whole-group containment, relative index and discreteness are derived, without supplied real lifts. -/
theorem fuchsian_crossingAxis_halfturn_extension
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (M:FuchsianAxisModel D f.val) (N:FuchsianAxisModel D g.val)
    (x:(fuchsianGeometricDomain D).carrier) (hxM:x.val∈M.carrier) (hxN:x.val∈N.carrier) :
    ∃y z:(fuchsianGeometricDomain D).carrier,
      let a:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D x
      let b:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D y
      let c:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D z
      orderOf a=2 ∧ orderOf b=2 ∧ orderOf c=2 ∧
      a.val x.val=x.val ∧ b.val y.val=y.val ∧ c.val z.val=z.val ∧
      a.val '' D.carrier=D.carrier ∧ b.val '' D.carrier=D.carrier ∧ c.val '' D.carrier=D.carrier ∧
      f.val=b*a ∧ g.val=c*a ∧
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f=2*_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D x y ∧
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D g=2*_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D x z ∧
      let G:=Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup)
      let K:=Subgroup.closure ({a,b,c}:Set Mobius.complexMobiusGroup)
      G≤K ∧ (G.relIndex K=1 ∨ G.relIndex K=2) ∧ _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K := by
  let q:=D.halfPlaneNormalizer
  let G:=Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup)
  have hGH:G≤H:=(Subgroup.closure_le H).mpr (by
    intro s hs
    rcases hs with rfl|rfl
    · exact f.property
    · exact g.property)
  have hdG:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G:=discreteMobius_subgroup_of_le H G D.discrete hGH
  have hmap:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set Mobius.complexMobiusGroup):=by
    change G.map (MulAut.conj q).toMonoidHom=_
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation, ←M.projection,
      ←N.projection]
  have hdN:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set Mobius.complexMobiusGroup)):=by
    let originalCrossingPairDiscrete:DiscreteTopology G:=hdG
    have hh:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q G
    change DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G) at hh
    rwa [hmap] at hh
  let u:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x
  have huM:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis M.matrix M.nontrivial M.trace_gt).carrier:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem M x hxM
  have huN:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis N.matrix N.nontrivial N.trace_gt).carrier:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem N x hxN
  obtain ⟨v,w,_hv,_hw,hv,hw,hef,heg,_hle,_hi,_hdisc⟩:=crossingAxis_halfturn_extension
    M.matrix N.matrix M.nontrivial N.nontrivial M.trace_gt N.trace_gt u huM huN hdN
  let y:=(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).symm v
  let z:=(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).symm w
  let a:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D x
  let b:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D y
  let c:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D z
  have hef':f.val=b*a:=by
    dsimp only [b,a,y]
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn_chart,
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn]
    change f.val=q⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL v)*q*(q⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL u)*q)
    calc
      f.val=q⁻¹*(q*f.val*q⁻¹)*q:=by group
      _=q⁻¹*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL v)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL u))*q:=by rw [←M.projection,hef]
      _=_:=by group
  have heg':g.val=c*a:=by
    dsimp only [c,a,z]
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn_chart,
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn]
    change g.val=q⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)*q*(q⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL u)*q)
    calc
      g.val=q⁻¹*(q*g.val*q⁻¹)*q:=by group
      _=q⁻¹*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL u))*q:=by rw [←N.projection,heg]
      _=_:=by group
  have hself (p:(fuchsianGeometricDomain D).carrier):
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D p*_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D p=1:=by
    have hh:=pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D p)
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn_order] at hh
    simpa only [pow_two] using hh
  have hindex:=three_involutions_pair_relIndex a b c (hself x) (hself y) (hself z)
  have hdK:=three_involutions_pair_discrete a b c (hself x) (hself y) (hself z)
  rw [←hef',←heg'] at hindex hdK
  refine ⟨y,z,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn_order D x,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn_order D y,
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn_order D z,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn_fixed D x,
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn_fixed D y,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn_fixed D z,
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn_preserves D x,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn_preserves D y,
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn_preserves D z,hef',heg',?_,?_,hindex.1,hindex.2,hdK hdG⟩
  · rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength f M,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist]
    simpa only [y,
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).apply_symm_apply] using hv
  · rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength g N,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist]
    simpa only [z,
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).apply_symm_apply] using hw


/-- A true original hyperbolic element has an actual axis model, constructed without any supplied lift. -/
def FuchsianDisc.chosenAxisModel
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (f:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val) : FuchsianAxisModel D f.val:=
  Classical.choice (D.axisModel_exists f.val f.property hf)

/-- Actual axis intersection on the original whole geometric invariant disc. -/
def FuchsianDisc.AxesCross
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (f g:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val) : Prop:=
  ∃x:(fuchsianGeometricDomain D).carrier,
    x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf).carrier ∧
      x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg).carrier

/-- The full original source half-turn extension for arbitrary hyperbolic elements and arbitrary
original geometric invariant discs; the genuine real axis models are constructed internally. -/
theorem fuchsian_crossingAxes_exists_halfturn_extension
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (f g:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (hcross:_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.AxesCross D f g hf hg) :
    ∃x y z:(fuchsianGeometricDomain D).carrier,
      let a:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D x
      let b:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D y
      let c:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.pointHalfTurn D z
      orderOf a=2 ∧ orderOf b=2 ∧ orderOf c=2 ∧
      a.val x.val=x.val ∧ b.val y.val=y.val ∧ c.val z.val=z.val ∧
      a.val '' D.carrier=D.carrier ∧ b.val '' D.carrier=D.carrier ∧ c.val '' D.carrier=D.carrier ∧
      f.val=b*a ∧ g.val=c*a ∧
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f=2*_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D x y ∧
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D g=2*_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D x z ∧
      let G:=Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup)
      let K:=Subgroup.closure ({a,b,c}:Set Mobius.complexMobiusGroup)
      G≤K ∧ (G.relIndex K=1 ∨ G.relIndex K=2) ∧ _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K := by
  obtain ⟨x,hxf,hxg⟩:=hcross
  obtain ⟨y,z,h⟩:=fuchsian_crossingAxis_halfturn_extension D f g
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf) (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg) x hxf hxg
  exact ⟨x,y,z,h⟩

end LowDimensionalTopology.Geometry.Fuchsian
