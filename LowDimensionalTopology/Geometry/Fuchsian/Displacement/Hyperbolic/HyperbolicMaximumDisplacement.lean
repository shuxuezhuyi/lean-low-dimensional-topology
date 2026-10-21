/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleHyperbolicAxisSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Hyperbolic.NonsimpleHyperbolicDisplacement
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticHyperbolicDisplacementBounds
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A non-elementary partner cannot preserve the actual hyperbolic axis. -/
theorem nonElementary_hyperbolic_axis_image_ne
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (htA:4<(Matrix.trace A.val)^2)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA≠
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ B) := by
  intro he
  apply hne
  apply _root_.LowDimensionalTopology.Geometry.Mobius.mobiusIteration_elementary_of_preserves _ _ hA
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
  have hpos:0<(Matrix.SpecialLinearGroup.mapGL ℝ B).val.det:=by
    change 0<B.val.det
    rw [B.det_coe]
    norm_num
  have hEnds: (L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ B)).idealEndpoints=
      _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ B)) '' L.idealEndpoints:=
    L.idealEndpoints_realGL_image _ _ hpos (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier])
  have hfrac:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val=_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ B)):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius,MonoidHom.comp_apply,_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_matrix]
  rw [←hfrac,←he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints] at hEnds
  exact hEnds.symm

/-- Actual axis-image distance is bounded by twice the point-to-axis distance
plus the true displacement, using the genuine perpendicular foot. -/
theorem halfPlaneLine_image_distance_le_twice_pointDist
    (L:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (B:Matrix.SpecialLinearGroup (Fin 2) ℝ) (z:ℍ) :
    L.lineDist (L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ B))≤
      2*L.pointDist z+dist z (B•z) := by
  let p:=L.orthogonalFoot z
  have hBp:B•p∈(L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ B)).carrier:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    exact mem_image_of_mem _ (L.orthogonalFoot_mem z)
  have hdist:=L.lineDist_le_dist (L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ B))
    (L.orthogonalFoot_mem z) hBp
  have htri:dist p (B•p)≤dist p z+dist z (B•z)+dist (B•z) (B•p):=
    by linarith only [dist_triangle p z (B•p),dist_triangle z (B•z) (B•p)]
  rw [(isometry_smul ℍ B).dist_eq,←L.pointDist_eq_orthogonalFoot z,dist_comm p z,
    ←L.pointDist_eq_orthogonalFoot z] at htri
  linarith only [hdist,htri]

/-- Simplicity forces a lower bound for the true maximum displacement with
every non-elementary partner, without a type hypothesis on that partner. -/
theorem HalfPlaneFuchsianGroup.simple_hyperbolic_displacementM_eighth
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (htA:4<(Matrix.trace A.val)^2)
    (hs:IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)) (hBm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/Real.sqrt 8≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
  let d:=L.lineDist (L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ B))
  let S:=Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)
  have hS:0≤S:=Real.sinh_nonneg_iff.mpr (by linarith only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos A hA htA])
  have hc:1/2≤S*Real.sinh (d/2):=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_hyperbolic_axis_collar P A hA htA hs B hBm
      (nonElementary_hyperbolic_axis_image_ne A B hA htA hne)
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_lower_bound _ _ _).mpr
  intro z
  let a:=dist z (B•z)/2
  let b:=L.pointDist z
  have hd:d/2≤a+b:=by
    have hh:=halfPlaneLine_image_distance_le_twice_pointDist L B z
    change d≤2*b+dist z (B•z) at hh
    dsimp only [a]
    linarith only [hh]
  have hsep:1/2≤S*1*Real.cosh (a+b):=by
    rw [mul_one]
    exact hc.trans (mul_le_mul_of_nonneg_left
      ((Real.sinh_le_sinh.mpr hd).trans (Real.sinh_lt_cosh _).le) hS)
  have hb:0≤b:=L.pointDist_nonneg z
  have hbound:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_hyperbolic_radial_max_eighth S 1 a b hS (by norm_num)
    (by norm_num) (by dsimp only [a];positivity) hb hsep
  have hfirst:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z=S*Real.cosh b:=by
    change Real.sinh (dist z (A•z)/2)=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolic_half_displacement A hA htA,mul_comm]
  have hsecond:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z=Real.sinh a:=rfl
  rw [hfirst,hsecond]
  apply (sq_le_sq₀ (show 0≤1/Real.sqrt 8 by positivity)
    (le_max_of_le_left (mul_nonneg hS (Real.cosh_pos _).le))).mp
  have he:(1/Real.sqrt (8:ℝ))^2=(1:ℝ)/8:=by norm_num [div_pow,Real.sq_sqrt]
  simpa only [one_mul,he] using hbound

/-- The original discrete group gives this bound for every genuine hyperbolic
element and every non-elementary partner, in both simple and nonsimple cases. -/
theorem HalfPlaneFuchsianGroup.hyperbolic_displacementM_eighth
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hBm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/Real.sqrt 8≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  have htA:4<(Matrix.trace A.val)^2:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A
    hA.1.1).mp hA
  by_cases hs:IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
  · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_hyperbolic_displacementM_eighth P A B hA.1.1 htA hs hBm hne
  · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nonsimple_displacementM_eighth P A (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) hAm hA.1.1 htA hs

/-- A genuine hyperbolic member and any genuine non-elementary partner have the
bound for the actual maximum-displacement infimum on the entire original disc. -/
theorem fuchsian_hyperbolic_displacementM_eighth
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D:FuchsianDisc H) (f g:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/Real.sqrt 8≤_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g := by
  let A:=D.normalizedLift f
  let B:=D.normalizedLift g
  let q:=D.halfPlaneNormalizer
  have P:HalfPlaneFuchsianGroup D.normalizedGroup:=
    ⟨fun u=>D.normalizedGroup_preserves_halfPlane u.val u.property,D.normalizedGroup_discrete⟩
  have hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation f.val q).mpr hf
  have hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈D.normalizedGroup:=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨f.val,f.property,rfl⟩
  have hBm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈D.normalizedGroup:=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨g.val,g.property,rfl⟩
  have hPair:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.generated_normalized_pair D f g]
    exact hne.conjugation q
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM_eq_native]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.hyperbolic_displacementM_eighth P A B hAm hBm hA hPair

end LowDimensionalTopology.Geometry.Fuchsian
