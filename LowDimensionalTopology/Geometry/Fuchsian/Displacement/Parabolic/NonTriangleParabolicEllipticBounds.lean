/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.NonTriangleHalfProducts
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicEllipticBounds
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The exact radial quotient has the sharp universal third bound at the genuine trace-six height constraint. -/
theorem parabolic_radial_quotient_third (s C v:ℝ) (hs:0<s) (hs1:s≤1) (hC:0<C) (hv:0<v)
    (hheight:2*v≤s*C) : 1/3≤s*C^2/(4*v*(s*v+C)) := by
  have hd:0<4*v*(s*v+C):=by positivity
  have hsq:(2*v)^2≤(s*C)^2:=(sq_le_sq₀ (by positivity) (by positivity)).mpr hheight
  have hm:=mul_le_mul_of_nonneg_left hsq hs.le
  have hl:=mul_le_mul_of_nonneg_right hheight (show 0≤2*C by positivity)
  have hss:s^2≤1:=by nlinarith only [mul_nonneg (sub_nonneg.mpr hs1) (show 0≤1+s by positivity)]
  have hm':=mul_le_mul_of_nonneg_right hss (show 0≤s*C^2 by positivity)
  apply (le_div_iff₀ hd).mpr
  nlinarith only [hm,hl,hm']

/-- The trace-six constraint gives the exact universal third bound for any genuine translation/elliptic pair. -/
theorem translation_elliptic_displacementM_third_of_trace_six
    (B:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (t:ℝ) (ht:t≠0)
    (htrace:6≤Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      t*B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹*B⁻¹).val) :
    1/3≤(_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2 := by
  let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  let s:=Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2)
  have hs:0<s:=Real.sin_pos_of_pos_of_lt_pi
    (by linarith only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_pos B hB])
    (by linarith only [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec B hB).1.2])
  have hc:2≤|t*B 1 0|:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_commutator_trace] at htrace
    nlinarith only [htrace,sq_abs (t*B 1 0),abs_nonneg (t*B 1 0)]
  have he:s=|B 1 0| *u.im:=elliptic_actual_angle_height B hB
  have hheight:2*u.im≤s*|t|:=by
    have hh:=mul_le_mul_of_nonneg_right hc u.im_pos.le
    rw [abs_mul] at hh
    simpa only [mul_assoc,←he,mul_comm] using hh
  rw [translation_elliptic_displacementM_square B hB t ht,←sq_abs t]
  exact parabolic_radial_quotient_third s |t| u.im hs (Real.sin_le_one _)
    (abs_pos.mpr ht) u.im_pos hheight

/-- The same sharp third bound holds for every actual parabolic/elliptic pair with the genuine trace-six gap. -/
theorem parabolic_elliptic_displacementM_third_of_trace_six
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)) (hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (htrace:6≤Matrix.trace (A*B*A⁻¹*B⁻¹).val) :
    1/3≤(_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2 := by
  obtain ⟨q,t,ht,hnorm⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  have hT:6≤Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*(q*B*q⁻¹)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹*(q*B*q⁻¹)⁻¹).val:=by
    rwa [parabolic_normalization_commutator_trace A B q t hnorm] at htrace
  have hBq:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)):=by
    have hh:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hB
    simpa only [map_mul,map_inv] using hh
  have hb:=translation_elliptic_displacementM_third_of_trace_six (q*B*q⁻¹) hBq t ht hT
  have hnormI:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t):=by
    rcases hnorm with he|he
    · rw [he]
    · rw [he]
      apply IsometryEquiv.ext
      intro z
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_neg_smul _ z
  rw [←hnormI,hSLIsometry_conjugation A q,hSLIsometry_conjugation B
    q,_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_conjugation] at hb
  exact hb

/--
The universal part for the actual original nontriangle pair,
with no additional order, fixed-point height or commutator hypothesis.
-/
theorem fuchsian_nontriangle_parabolic_elliptic_displacementM_sqrt_three
    (f g:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D:FuchsianDisc (Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      f) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hnt:¬IsMobiusTriangleGroup (Subgroup.closure ({f,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/Real.sqrt 3≤_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D
      ⟨f,Subgroup.subset_closure (by simp)⟩ ⟨g,Subgroup.subset_closure (by simp)⟩ := by
  let F:Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=⟨f,Subgroup.subset_closure (by simp)⟩
  let G:Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=⟨g,Subgroup.subset_closure (by simp)⟩
  let A:=D.normalizedLift F
  let B:=D.normalizedLift G
  let q:=D.halfPlaneNormalizer
  have hfN:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
  have hgN:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation g q).mpr hg
  have hcomm:_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((Matrix.trace (A*B*A⁻¹*B⁻¹).val:ℝ):ℂ):=by
    rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_commutatorTrace_conjugation f g q,
      ←D.normalizedLift_spec F,←D.normalizedLift_spec G,realSLMobius_commutatorTrace]
  have h6:6≤Matrix.trace (A*B*A⁻¹*B⁻¹).val:=by
    have hh:=fuchsian_one_parabolic_nontriangle_trace_ge_six f g D hf hne hnt
    rw [hcomm] at hh
    simpa only [Complex.ofReal_re] using hh
  have hsq:=parabolic_elliptic_displacementM_third_of_trace_six A B hfN hgN h6
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM_eq_native]
  apply (sq_le_sq₀ (show 0≤1/Real.sqrt 3 by positivity) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)).mp
  have he:(1/Real.sqrt (3:ℝ))^2=(1:ℝ)/3:=by norm_num [div_pow,Real.sq_sqrt]
  rwa [he]


/-- The actual half-turn Schottky family has this exact whole-plane maximum-displacement infimum. -/
theorem halfTurnSchottky_elliptic_displacementM (v:ℝ) (hv:0<v) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv))=
      1/Real.sqrt (4*v*(v+1)) := by
  have hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)):=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at v hv).elliptic
  have hM:=translation_elliptic_displacementM_square (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv) hB 1 (by norm_num)
  rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at v hv).rotation_angle,Real.sin_pi_div_two,
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at v hv).center_eq] at hM
  have hIm:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 v hv).im=v:=rfl
  have hsq:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)))^2=
      1/(4*v*(v+1)):=by simpa only [hIm,one_pow,one_mul,abs_one] using hM
  apply (sq_eq_sq₀ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _) (by positivity:0≤1/Real.sqrt (4*v*(v+1)))).mp
  rw [hsq,div_pow,one_pow,Real.sq_sqrt (show 0≤4*v*(v+1) by positivity)]

/--
The nontriangle universal constant is sharp already at order two,
for actual whole generated groups proved discrete, non-elementary and of the second kind.
-/
theorem nontriangle_parabolic_halfTurn_displacementM_sharpness (δ:ℝ) (hδ:0<δ) :
    ∃v:ℝ,∃hv:0<v,∃_hvu:v<1/2,
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (halfTurnSchottkyGroup v hv) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (halfTurnSchottkyGroup v hv) ∧
      ¬IsMobiusTriangleGroup (halfTurnSchottkyGroup v hv) ∧
      orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv))=2 ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv))<1/Real.sqrt 3+δ := by
  let F:ℝ→ℝ:=fun v=>1/Real.sqrt (4*v*(v+1))
  have hc:ContinuousAt F (1/2):=by
    dsimp only [F]
    fun_prop (disch:=norm_num)
  have he:F (1/2)=1/Real.sqrt 3:=by norm_num [F]
  have ht:Tendsto F (𝓝[<] (1/2)) (𝓝 (1/Real.sqrt 3)):=by
    rw [←he]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hEvent:∀ᶠv:ℝ in 𝓝[<] (1/2),0<v ∧ v<1/2 ∧ F v<1/Real.sqrt 3+δ:=by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num:(0:ℝ)<1/2)),
      self_mem_nhdsWithin,ht.eventually (Iio_mem_nhds (show 1/Real.sqrt (3:ℝ)<1/Real.sqrt 3+δ by linarith only [hδ]))] with v hv hvu hF
    exact ⟨hv,hvu,hF⟩
  obtain ⟨v,hv,hvu,hF⟩:=hEvent.exists
  refine ⟨v,hv,hvu,(halfTurnSchottkyGroup_data v hv hvu).discrete,
    halfTurnSchottkyGroup_nonElementary v hv,halfTurnSchottkyGroup_not_triangle v hv hvu,
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at v hv).1,?_⟩
  rw [halfTurnSchottky_elliptic_displacementM v hv]
  exact hF

end LowDimensionalTopology.Geometry.Fuchsian
