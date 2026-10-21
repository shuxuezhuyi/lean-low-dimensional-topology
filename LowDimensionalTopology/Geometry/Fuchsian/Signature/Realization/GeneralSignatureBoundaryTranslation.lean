module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.SignatureHyperbolicBoundaryBlock
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureRightCornerGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleCongruence
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.CommonOrthogonals
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- The genuine reflection taking the lower endpoint to the higher one is the
actual concentric midpoint mirror, rather than a supplied axis-preserver. -/
theorem generalSignature_reflection_from_axis_pair (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (l : ℝ) (hl : 0<l)
    (hL : L.reflection UpperHalfPlane.I=_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam l) :
    L=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 (Real.sqrt (Real.exp l))
      (Real.sqrt_pos.mpr (Real.exp_pos l)) := by
  have hk : 1<Real.exp l:=Real.one_lt_exp_iff.mpr hl
  cases L with
  | vertical c=>
    have hi:=congrArg (fun z:ℍ=>z.im) hL
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection c UpperHalfPlane.I).im=Real.exp l at hi
    have hc:=congrArg Complex.im (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_coe c UpperHalfPlane.I)
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection c UpperHalfPlane.I).im=_ at hc
    norm_num at hc
    linarith only [hi,hc,hk]
  | circle c r hr=>
    have he:=congrArg (fun z:ℍ=>(z:ℂ)) hL
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection c r hr UpperHalfPlane.I:ℂ)=_ at he
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe] at he
    have hdiv : (r:ℂ)^2/(conj (UpperHalfPlane.I:ℂ)-(c:ℂ))=
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam l:ℂ)-(c:ℂ):=by linear_combination he
    have hm:=(div_eq_iff (_root_.LowDimensionalTopology.Geometry.Hyperbolic.conj_sub_real_ne_zero c UpperHalfPlane.I)).mp hdiv
    have hR:=congrArg Complex.re hm
    have hI:=congrArg Complex.im hm
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam,Complex.mul_re,Complex.mul_im,
      Complex.sub_re,Complex.sub_im,pow_two] at hR hI
    have hc:c=0:=by nlinarith only [hI,hk]
    subst c
    have hr2:r^2=Real.exp l:=by nlinarith only [hR]
    have heq:r=Real.sqrt (Real.exp l):=by
      nlinarith only [hr2,Real.sq_sqrt (Real.exp_pos l).le,hr,
        Real.sqrt_nonneg (Real.exp l)]
    subst r
    rfl

/-- A right-corner cut and its actual reflected endpoint pair give a positive
translation of the entire actual cut axis. The paired-map formula is derived. -/
theorem generalSignature_boundary_reflection_translation
    (R M K : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u v : ℍ) (huv:u≠v)
    (hR:R.OrthogonalAt K u) (hv:v∈K.carrier) (hM:M.reflection u=v) :
    ∃q:Matrix.SpecialLinearGroup (Fin 2) ℝ,∃l:ℝ,0<l ∧
      q • u=UpperHalfPlane.I ∧ q • v=_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam l ∧
      K.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 ∧
      (∀z:ℍ,q • M.reflection (R.reflection z)=signatureBoundaryShift l (q • z)) := by
  obtain ⟨q,k,hk,hqu,hqv⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_sl2_normalized_pair u v huv
  let l:=Real.log k
  have hl:0<l:=Real.log_pos hk
  have hqv':q • v=_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam l:=by
    rw [hqv]
    apply UpperHalfPlane.ext
    change (⟨0,k⟩:ℂ)=⟨0,Real.exp (Real.log k)⟩
    rw [Real.exp_log (zero_lt_one.trans hk)]
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ q
  have hK:K.realGLMap g=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.eq_of_two_points _ _
      (show q • u≠q • v from (MulAction.injective q).ne huv)
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier];exact ⟨u,hR.2.1,rfl⟩
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier];exact ⟨v,hv,rfl⟩
    · rw [hqu];rfl
    · rw [hqv'];change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam l).re=0;rfl
  have hRO: (R.realGLMap g).Orthogonal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0):=by
    rw [←hK]
    exact R.orthogonal_isometry_image K (R.realGLMap g) (K.realGLMap g)
      (g • ·) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g) (R.realGLMap_carrier g).symm
      (K.realGLMap_carrier g).symm ⟨u,hR⟩
  obtain ⟨r,hr,hRR⟩:=(R.realGLMap g).orthogonal_vertical_zero hRO
  have hIR:UpperHalfPlane.I∈(R.realGLMap g).carrier:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    exact ⟨u,hR.1,hqu⟩
  rw [hRR] at hIR
  change ‖(UpperHalfPlane.I:ℂ)-(0:ℂ)‖=r at hIR
  norm_num at hIR
  have hR1:R.realGLMap g=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 (by norm_num):=by
    simpa only [←hIR] using hRR
  have hMI:(M.realGLMap g).reflection UpperHalfPlane.I=_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam l:=by
    rw [←M.reflection_realGL_conjugation g]
    change q • M.reflection (q⁻¹ • UpperHalfPlane.I)=_
    rw [←hqu,inv_smul_smul,hM,hqv']
  have hMM:=generalSignature_reflection_from_axis_pair (M.realGLMap g) l hl hMI
  refine ⟨q,l,hl,hqu,hqv',hK,?_⟩
  intro z
  have hprod:=congrFun (_root_.LowDimensionalTopology.Geometry.Hyperbolic.dilation_reflection_factor (Real.exp l) 1
    (Real.exp_pos l) (by norm_num)) (q • z)
  simp only [mul_one] at hprod
  change q • M.reflection (R.reflection z)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (Real.exp l) (Real.exp_pos l) • (q • z)
  rw [hprod]
  change g • M.reflection (R.reflection z)=_
  rw [←hMM,←hR1]
  simp only [Function.comp_apply]
  rw [←M.reflection_realGL_conjugation g,←R.reflection_realGL_conjugation g]
  rw [show q • z=g • z from rfl]
  simp only [inv_smul_smul]

/-- The original canonical boundary triple gives the actual positive
hyperbolic generator along its actual finite cut, without any supplied axis
or hyperbolicity assertion. Other polygon vertices may be ideal. -/
theorem generalSignature_boundary_triple_translation {n:ℕ} (θ:Fin n→ℝ) (d:ℝ)
    (hθ:∀i,θ i∈Ico (0:ℝ) Real.pi) (hd:0<d)
    (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d=Real.pi) (i:Fin n)
    (hk:θ (finRotate n i)=Real.pi/2)
    (hj:θ (finRotate n (finRotate n i))=Real.pi/2) :
    let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let k:=finRotate n i
    let j:=finRotate n k
    ∃u v:ℍ,∃q:Matrix.SpecialLinearGroup (Fin 2) ℝ,∃l:ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc u)=Q.vertices k ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc v)=Q.vertices j ∧ u≠v ∧ 0<l ∧
      q • u=UpperHalfPlane.I ∧ q • v=_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam l ∧
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q k).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 ∧
      (∀z:ℍ,q • cofiniteTangentPairingElement θ d hθ hd hb i j z=
        signatureBoundaryShift l (q • z)) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let k:=finRotate n i
  let j:=finRotate n k
  let M:=triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)
  obtain ⟨u,v,hu,hv,huv,hR,hvR,hMu,_hMv,L,hLM,_hLI⟩:=
    generalSignature_right_corner_geometry θ d hθ hd hb i hk hj
  have hML:M=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L:=hLM.symm
  have hLu:L.reflection u=v:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L u=v
    rw [hLM]
    exact hMu
  obtain ⟨q,l,hl,hqu,hqv,hK,ht⟩:=generalSignature_boundary_reflection_translation
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i) L (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q k) u v huv hR hvR.1 hLu
  refine ⟨u,v,q,l,hu,hv,huv,hl,hqu,hqv,hK,?_⟩
  intro z
  change q • M ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).reflection z)=_
  rw [hML]
  exact ht z

end LowDimensionalTopology.Geometry.Fuchsian
