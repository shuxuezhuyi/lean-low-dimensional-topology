/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticHyperbolicDisplacementBounds
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicEllipticBounds
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PointLineFormulas
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleHyperbolicAxisSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.FuchsianDisplacementInvariants
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

/-- The actual elliptic center and actual vertical-axis distance recover the literal
negative off-diagonal product, without a center or angle supplied as a model. -/
theorem elliptic_axis0_center_distance_sine_square
    (B:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
    (Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)*
      Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).pointDist u))^2= -B 0 1*B 1 0 := by
  let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  have hb: B 0 1= -B 1 0*(u.re^2+u.im^2):=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_center_coefficients B hB).2.2.1
  dsimp only
  rw [elliptic_actual_angle_height,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalLine_pointDist_cosh]
  change (|B 1 0| *u.im*(‖(u:ℂ)-(0:ℂ)‖/u.im))^2= -B 0 1*B 1 0
  rw [sub_zero]
  have he:|B 1 0| *u.im*(‖(u:ℂ)‖/u.im)=|B 1 0| *‖(u:ℂ)‖:=by field_simp
  rw [he,mul_pow,sq_abs,←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  change B 1 0^2*(u.re*u.re+u.im*u.im)= -B 0 1*B 1 0
  rw [hb]
  ring

/-- The genuine elliptic center-to-axis factor is the cosh of half the distance to
its actual disjoint image, when the proved matrix image-distance formula is supplied. -/
theorem elliptic_axis0_center_distance_image_half
    (B:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (d:ℝ) (had:B 0 0*B 1 1≤0)
    (hd:Real.cosh d=|B 0 0*B 1 1+B 0 1*B 1 0|) :
    let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
    Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)*
      Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).pointDist u)=Real.cosh (d/2) := by
  have hdet: B 0 0*B 1 1-B 0 1*B 1 0=1:=by simpa only [Matrix.det_fin_two] using B.det_coe
  rw [abs_of_nonpos (by linarith only [had,hdet])] at hd
  have hs:0<Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2):=
    Real.sin_pos_of_pos_of_lt_pi (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo B hB).1
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo B hB).2
  have he:=elliptic_axis0_center_distance_sine_square B hB
  have hh:Real.cosh d=2*Real.cosh (d/2)^2-1:=by
    have hh:=Real.cosh_two_mul (d/2)
    rw [show 2*(d/2)=d by ring] at hh
    nlinarith only [hh,Real.cosh_sq_sub_sinh_sq (d/2)]
  apply (sq_eq_sq₀ (mul_nonneg hs.le (Real.cosh_pos _).le) (Real.cosh_pos _).le).mp
  nlinarith only [he,hh,hd,hdet]

/-- Actual simplicity and the genuine non-elementary partner construct the entire
center-axis constraint, hence the true source bound, in a diagonal chart. -/
theorem HalfPlaneFuchsianGroup.simple_logDilation_elliptic_displacementM_eighth
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (t:ℝ) (ht:0<t) (hD:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)≠1)
    (htD:4<(Matrix.trace (hLogDilationSL t).val)^2)
    (hs:IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)))
    (B:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hBm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/Real.sqrt 8≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (hLogDilationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  let A:=hLogDilationSL t
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0
  let M:=logDilationAxisImage t hD htD B
  let d:=L.lineDist M
  have haxis:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hD htD=L:=hLogDilationSL_hyperbolic_axis t ht hD htD
  have hdis:Disjoint L.carrier ((B•·:ℍ→ℍ) '' L.carrier):=
    hSimple_axis0_translate_disjoint H A B hD htD haxis hs hBm hne
  have hImage:((B•·:ℍ→ℍ) '' L.carrier)=M.carrier:=by
    dsimp only [M,logDilationAxisImage]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation (hLogDilationSL t) B hD htD,
      haxis,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  have hLM:L≠M:=by
    intro he
    rw [hImage,←he] at hdis
    exact Set.disjoint_left.mp hdis (show UpperHalfPlane.I∈L.carrier from rfl) rfl
  have hBC:B 0 1*B 1 0<0:=by
    have htr: (Matrix.trace B.val)^2<4:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B
      hB.1).mp hB
    rw [Matrix.trace_fin_two] at htr
    have hd:=B.det_coe
    rw [Matrix.det_fin_two] at hd
    nlinarith only [htr,hd,sq_nonneg (B 0 0-B 1 1)]
  have had:B 0 0*B 1 1≤0:=by
    have hh:=hSL_imaginaryAxis_translate_disjoint_product_nonneg B hdis
    by_contra hn
    have hneg:=mul_neg_of_pos_of_neg (lt_of_not_ge hn) hBC
    linarith only [hh,hneg]
  have hd:Real.cosh d=|B 0 0*B 1 1+B 0 1*B 1 0|:=
    logDilation_axis_image_cosh t ht hD htD B
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_logDilation_image_hDisjoint P t ht
        hD htD hs B hBm hLM)
  have hcenter:=elliptic_axis0_center_distance_image_half B hB d had hd
  have hcollar:1/2≤Real.sinh t*Real.sinh (d/2):=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_logDilation_axis_collar P t ht hD htD hs B hBm hLM
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_hyperbolic_displacementM_eighth_of_separation A B hD htD hB
  rw [haxis,hLogDilationSL_sinh_half_translation t ht hD htD,mul_assoc,hcenter]
  exact hcollar.trans (mul_le_mul_of_nonneg_left (Real.sinh_lt_cosh (d/2)).le
    (Real.sinh_pos_iff.mpr ht).le)

/-- The genuine source simple-axis branch for any actual hyperbolic/elliptic pair.
The positive diagonal chart, the entire conjugate group and all partner data are constructed. -/
theorem HalfPlaneFuchsianGroup.simple_hyperbolic_elliptic_displacementM_eighth
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)) (hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hs:IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)) (hBm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/Real.sqrt 8≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  obtain ⟨q,t,ht,hq⟩:=realSLMobius_hyperbolic_positive_log_normal_form A hA
  let D:=hLogDilationSL t
  let C:=q*B*q⁻¹
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H
  have PK:HalfPlaneFuchsianGroup K:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.realSLConjugateData P q
  have hDQ:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)):=by
    simpa only [map_mul,map_inv] using
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hA
  have hDH:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D):=hq ▸ hDQ
  have hD:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D≠1:=hDH.1.1
  have htD:4<(Matrix.trace D.val)^2:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff D
    hD).mp hDH
  have hsQ:IsSimple K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)):=by
    simpa only [map_mul,map_inv] using hs.conjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
  have hsD:IsSimple K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D):=hq ▸ hsQ
  have hCm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈K:=by
    dsimp only [C,K]
    rw [map_mul,map_mul,map_inv]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _
      _).mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,hBm,rfl⟩
  have hC:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C):=by
    simpa only [C,map_mul,map_inv] using
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hB
  have hPair:=hne.conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation] at hPair
  have hqa:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D:=by
    simpa only [map_mul,map_inv] using hq
  have hqb:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C:=by
    simp only [C,map_mul,map_inv]
  have hPairK:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    simpa only [hqa,hqb] using hPair
  have hM:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_logDilation_elliptic_displacementM_eighth
    PK t ht hD htD hsD C hCm hC hPairK
  have hNative:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry D:=hSLIsometry_eq_of_realSLMobius_eq _ _ hq
  rw [←hNative,hSLIsometry_conjugation A q] at hM
  dsimp only [C] at hM
  rwa [hSLIsometry_conjugation B q,_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_conjugation] at hM

/--
The original-disc simple-axis branch, with the original
whole-group simplicity and actual whole-disc displacement infimum. No real lift,
normalizer, center-axis separation or supplied numerical bound is assumed.
-/
theorem fuchsian_simple_hyperbolic_elliptic_displacementM_eighth
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D:FuchsianDisc H) (f g:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val)
    (hs:IsSimple H f.val)
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
  have hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation g.val q).mpr hg
  have hsN:IsSimple D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    exact hs.conjugate q
  have hBm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈D.normalizedGroup:=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨g.val,g.property,rfl⟩
  have hPair:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.generated_normalized_pair D f g]
    exact hne.conjugation q
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM_eq_native]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_hyperbolic_elliptic_displacementM_eighth P A B hA hB hsN hBm hPair

end LowDimensionalTopology.Geometry.Fuchsian
