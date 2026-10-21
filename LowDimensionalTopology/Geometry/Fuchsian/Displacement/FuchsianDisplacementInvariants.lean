/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalSurfaceRegions
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicProducts
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeometricFuchsianCharts
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane OnePoint MatrixGroups Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The constructed true half-plane coordinate of the entire original
geometric invariant disc, with its actual native hyperbolic metric. -/
def FuchsianDisc.hyperbolicCoordinate {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) : (fuchsianGeometricDomain D).carrier ≃ₜ ℍ :=
  geometricHalfPlaneChart D D.halfPlaneNormalizer D.halfPlaneNormalizer_image

/-- Any two genuine whole-disc charts differ by an actual real
Möbius isometry of the genuine native half-plane. -/
theorem FuchsianDisc.halfPlaneChart_transition {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (q r:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq:q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) (hr:r.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    ∃A:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀x:(fuchsianGeometricDomain D).carrier,geometricHalfPlaneChart D r hr x=A•geometricHalfPlaneChart D q hq x := by
  have hp:(r*q⁻¹).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    conv_lhs=>rw [←hq,image_image]
    change (fun z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>r•(q⁻¹•(q•z))) '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    simpa only [inv_smul_smul] using (show (fun z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>r•z) ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet from hr)
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL (r*q⁻¹) hp
  refine ⟨A,?_⟩
  intro x
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  change (((geometricHalfPlaneChart D r hr x:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
    (((A•geometricHalfPlaneChart D q hq x:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A]
  rw [geometricHalfPlaneChart_extended,geometricHalfPlaneChart_extended,hA]
  change r•x.val=(r*q⁻¹)•(q•x.val)
  simp only [mul_smul,inv_smul_smul]

/-- The actual hyperbolic metric on original points, expressed using
the constructed true whole-domain chart. Independence of all chart
choices is proved below. -/
def FuchsianDisc.hyperbolicDist {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (x y:(fuchsianGeometricDomain D).carrier) : ℝ :=
  dist (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D
    x) (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D y)

/-- Every genuine whole-disc half-plane chart gives the very same
original hyperbolic distance. -/
theorem FuchsianDisc.hyperbolicDist_eq_chart {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq:q.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (x y:(fuchsianGeometricDomain D).carrier) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D x y=
      dist (geometricHalfPlaneChart D q hq x) (geometricHalfPlaneChart D q hq y) := by
  obtain ⟨A,hA⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.halfPlaneChart_transition D D.halfPlaneNormalizer q
    D.halfPlaneNormalizer_image hq
  rw [hA x,hA y]
  exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A).isometry.dist_eq _ _).symm

/-- The original action is equivariant with the actual chosen real
matrix lift under the constructed whole-disc hyperbolic coordinate. -/
theorem FuchsianDisc.hyperbolicCoordinate_action {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (x:(fuchsianGeometricDomain D).carrier) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D (f•x)=
      D.normalizedLift f•_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x := by
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  change (((geometricHalfPlaneChart D D.halfPlaneNormalizer D.halfPlaneNormalizer_image
    (f•x):ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
    (((D.normalizedLift f•geometricHalfPlaneChart D D.halfPlaneNormalizer D.halfPlaneNormalizer_image
      x:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,geometricHalfPlaneChart_extended,geometricHalfPlaneChart_extended,
    D.normalizedLift_spec]
  change D.halfPlaneNormalizer•(f.val•x.val)=
    (D.halfPlaneNormalizer*f.val*D.halfPlaneNormalizer⁻¹)•(D.halfPlaneNormalizer•x.val)
  simp only [mul_smul,inv_smul_smul]

/-- Every original group element preserves this actual, coordinate
independent hyperbolic metric on the original geometric disc. -/
theorem FuchsianDisc.hyperbolicDist_action {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (x y:(fuchsianGeometricDomain D).carrier) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D (f•x) (f•y)=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D x y := by
  unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate_action,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate_action]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (D.normalizedLift f)).isometry.dist_eq _ _

/-- Original half-distance sinh displacement on actual original points. -/
def FuchsianDisc.sinhDisplacement {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (x:(fuchsianGeometricDomain D).carrier) : ℝ :=
  Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D x (f•x)/2)

/-- The native computation is exactly the original pointwise displacement. -/
theorem FuchsianDisc.sinhDisplacement_eq_native {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f:H) (x:(fuchsianGeometricDomain D).carrier) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.sinhDisplacement D f x=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (D.normalizedLift f)) (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x) := by
  unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.sinhDisplacement _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate_action]
  rfl

/-- The actual product displacement infimum over the whole original
geometric invariant disc, before any normalization. -/
def FuchsianDisc.displacementP {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) : ℝ :=
  ⨅x:(fuchsianGeometricDomain
    D).carrier,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.sinhDisplacement D f x*
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.sinhDisplacement D g x

/-- The actual maximum displacement infimum over the whole original
geometric invariant disc, before any normalization. -/
def FuchsianDisc.displacementM {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) : ℝ :=
  ⨅x:(fuchsianGeometricDomain
    D).carrier,max (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.sinhDisplacement D f x)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.sinhDisplacement D g x)

/-- The genuine original product infimum equals the genuine native
infimum; the original coordinate is surjective, so no points are lost. -/
theorem FuchsianDisc.displacementP_eq_native {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP D f g=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (D.normalizedLift f)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (D.normalizedLift g)) := by
  unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP
  simp_rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.sinhDisplacement_eq_native]
  apply congrArg sInf
  ext t
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x,rfl⟩
  · rintro ⟨y,rfl⟩
    obtain ⟨x,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).surjective y
    exact ⟨x,rfl⟩

/-- The genuine original maximum infimum equals the genuine native
infimum, with the same full-domain surjectivity. -/
theorem FuchsianDisc.displacementM_eq_native {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (D.normalizedLift f)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (D.normalizedLift g)) := by
  unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
  simp_rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.sinhDisplacement_eq_native]
  apply congrArg sInf
  ext t
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x,rfl⟩
  · rintro ⟨y,rfl⟩
    obtain ⟨x,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).surjective y
    exact ⟨x,rfl⟩

/-- The actual generated original pair transports to exactly the pair
of its actual normalized lifts. -/
theorem FuchsianDisc.generated_normalized_pair {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate D.halfPlaneNormalizer
      (Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))=
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift g)}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
  change (Subgroup.closure _).map _=_
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,←D.normalizedLift_spec
    f,←D.normalizedLift_spec g]

/-- The universal quarter product bound holds over the full actual
original invariant disc, with no native-model or supplied-lift premise. -/
theorem FuchsianDisc.parabolic_pair_displacementP_quarter {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/4≤_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP D f g := by
  let q:=D.halfPlaneNormalizer
  let K:=Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hKH:K≤H:=(Subgroup.closure_le H).mpr (by
    intro x hx
    rcases hx with rfl|hx
    · exact f.property
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ g.property)
  have hdK:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K:=discreteMobius_subgroup_of_le H K D.discrete hKH
  have hdN:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift g)}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    let fuchsianDisplacementOriginalPairDiscrete : DiscreteTopology K:=hdK
    have hn:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q K
    change DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      K) at hn
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.generated_normalized_pair D] at hn
    exact hn
  have hnN:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift g)}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    have hn:=hne.conjugation q
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate D.halfPlaneNormalizer (Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) at hn
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.generated_normalized_pair D] at hn
    exact hn
  have hfN:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift f)):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
  have hgN:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift g)) ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift g)):=by
    rw [D.normalizedLift_spec]
    rcases hg with hg|hg
    · exact Or.inl ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp
      hg)
    · exact Or.inr (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward g.val q hg)
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP_eq_native]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.parabolic_pair_displacementP_quarter _ _ hfN hgN hdN hnN

/-- The original model's actual hyperbolic metric, retaining exactly
its already existing sphere-subspace topology. -/
@[instance_reducible]
def FuchsianDisc.hyperbolicMetricSpace {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) : MetricSpace (fuchsianGeometricDomain D).carrier :=
  Topology.IsEmbedding.comapMetricSpace (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).isEmbedding

/-- The named actual metric has the original topology definitionally. -/
theorem FuchsianDisc.hyperbolicMetricSpace_topology {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) :
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicMetricSpace
      D).toUniformSpace.toTopologicalSpace=
      inferInstanceAs (TopologicalSpace (fuchsianGeometricDomain D).carrier) := rfl

/-- The named metric's distance is the same original coordinate
independent hyperbolic distance used by both displacement infima. -/
theorem FuchsianDisc.hyperbolicMetricSpace_dist {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (x y:(fuchsianGeometricDomain D).carrier) :
    letI:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicMetricSpace D
    dist x y=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicDist D x y := rfl

/-- The actual original model is isometric to the native path-metric
half-plane by the constructed whole-domain chart, with the original
topology and without imposing a global new metric instance. -/
def FuchsianDisc.hyperbolicCoordinateIsometry {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) :
    letI:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicMetricSpace D
    (fuchsianGeometricDomain D).carrier ≃ᵢ ℍ := by
  letI:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicMetricSpace D
  exact ⟨(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D).toEquiv,by intro x y;rfl⟩

end LowDimensionalTopology.Geometry.Fuchsian
