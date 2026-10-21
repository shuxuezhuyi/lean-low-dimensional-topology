/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.NontriangleEllipticTraceBounds
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ArbitraryTriangleDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleSupergroups
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint Pointwise Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The determinant-one trace polarization used by the original conjugate pair. -/
theorem ellipticTrace_trace_polarization (A C:Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (A*C).val+Matrix.trace (A*C⁻¹).val=
      Matrix.trace A.val*Matrix.trace C.val := by
  have hc : C.val+(C⁻¹).val=(Matrix.trace C.val) • (1:Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.trace_fin_two,add_comm]
  have ht:=congrArg (fun M:Matrix (Fin 2) (Fin 2) ℝ=>Matrix.trace (A.val*M)) hc
  simpa only [Matrix.mul_add,Matrix.trace_add,Matrix.mul_smul,Matrix.trace_smul,
    Matrix.mul_one,Matrix.SpecialLinearGroup.coe_mul,smul_eq_mul,mul_comm] using ht

/-- The genuine conjugate pair has a trace complementary to the actual commutator. -/
theorem ellipticTrace_conjugate_product_trace (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (A*(B*A*B⁻¹)).val=(Matrix.trace A.val)^2-
      Matrix.trace (A*B*A⁻¹*B⁻¹).val := by
  have ht:=ellipticTrace_trace_polarization A (B*A*B⁻¹)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation,
    show A*(B*A*B⁻¹)⁻¹=A*B*A⁻¹*B⁻¹ by group] at ht
  nlinarith only [ht]

/-- An actual elliptic first map always gives a real commutator trace at least two. -/
theorem ellipticTrace_commutator_ge_two (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    2≤Matrix.trace (A*B*A⁻¹*B⁻¹).val := by
  have ht:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_commutator_trace A B hA
  have hp:=mul_nonneg
    (sq_nonneg (Real.sinh (dist
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
      (B • _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))/2)))
    (sq_nonneg (Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA/2)))
  dsimp only at ht
  nlinarith only [ht,hp]

/-- Failure of the source trace threshold creates an actual elliptic
product of the original map and its actual conjugate. -/
theorem ellipticTrace_small_commutator_conjugate_product
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hu:B • _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
    (hs:Matrix.trace (A*B*A⁻¹*B⁻¹).val<2+(Matrix.trace A.val)^2) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*(B*A*B⁻¹))) := by
  have hC:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B*A*B⁻¹)):=native_elliptic_realSL_conjugate A B hA
  have hn:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter (B*A*B⁻¹) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hC.1).mp hC) := by
    rw [native_elliptic_realSL_conjugate_center A B hA hC]
    exact hu.symm
  have ht:=ellipticTrace_conjugate_product_trace A B
  have hlow:=ellipticTrace_commutator_ge_two A B hA
  have ha:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA
  have hl:-(2:ℝ)<Matrix.trace (A*(B*A*B⁻¹)).val:=by linarith only [ht,hs]
  have hh:Matrix.trace (A*(B*A*B⁻¹)).val<2:=by linarith only [ht,hlow,ha]
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_ne_one_of_centers_ne A _ hA hC hn)).mpr
  nlinarith only [hl,hh]

/-- Actual real conformal conjugation preserves the signed elliptic angle. -/
theorem ellipticTrace_conjugate_angle (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hC:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B*A*B⁻¹))) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle (B*A*B⁻¹) hC=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA := by
  obtain ⟨q,a,b,hu,hq,_hb,hr⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_normal_form A hA
  have hqc : (q*B⁻¹) • _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter (B*A*B⁻¹)
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hC.1).mp hC)=UpperHalfPlane.I := by
    rw [native_elliptic_realSL_conjugate_center A B hA hC,mul_smul,inv_smul_smul]
    exact hq
  have hrc : (q*B⁻¹)*(B*A*B⁻¹)*(q*B⁻¹)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hu := by
    calc
      _=q*A*q⁻¹:=by group
      _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL a b hu:=hr
  have heA:=realSL_normalizer_multiplier_actual_angle A q hA a b hu hq hr
  have heC:=realSL_normalizer_multiplier_actual_angle (B*A*B⁻¹) (q*B⁻¹) hC a b hu hqc hrc
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.rotation_exp_injective_Ico (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec _ hC).1
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).1 (heC.symm.trans heA)

/-- The actual commutator trace decreases when the actual moved-center distance decreases. -/
theorem ellipticTrace_commutator_mono_center (A B F:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hd:dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (F • _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))≤
      dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (B • _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))) :
    Matrix.trace (A*F*A⁻¹*F⁻¹).val≤Matrix.trace (A*B*A⁻¹*B⁻¹).val := by
  have hF:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_commutator_trace A F hA
  have hB:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_commutator_trace A B hA
  have hs:=Real.sinh_le_sinh.mpr (div_le_div_of_nonneg_right hd (by norm_num : (0:ℝ)≤2))
  have hz:0≤Real.sinh (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
      (F • _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))/2) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hsq:=sq_le_sq₀ hz (hz.trans hs) |>.mpr hs
  have hprod:=mul_le_mul_of_nonneg_right hsq
    (sq_nonneg (Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA/2)))
  dsimp only at hF hB
  nlinarith only [hF,hB,hprod]

/-- The failed source estimate produces a true closest conjugate-center
triangle with both original angles π/n and its full original pair group. -/
theorem HalfPlaneFuchsianGroup.ellipticTrace_minimal_conjugate_triangle
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (_hAH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hBH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (n:ℕ) (hn:3≤n) (hangle:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA=2*Real.pi/n)
    (hs:Matrix.trace (A*B*A⁻¹*B⁻¹).val<2+(Matrix.trace A.val)^2) :
    ∃ F:Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F∈H ∧
      ∃hAE:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*(F*A*F⁻¹))),∃T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle,
        T.a=F • _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ∧
        T.c=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ∧
        T.b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter (A*(F*A*F⁻¹)) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hAE.1).mp hAE) ∧
        T.gamma=Real.pi/n ∧T.alpha=Real.pi/n ∧
        (Matrix.trace (A*(F*A*F⁻¹)).val)^2=4*(Real.cos T.beta)^2 ∧
        Subgroup.closure ({
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F*A*F⁻¹)}:Set (ℍ≃ᵢℍ))=
          triangleConformalGroup T.toClosedHTriangle ∧
        (∀Q:Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Q∈H→Q •
          T.a≠T.c→
          dist T.c T.a≤dist T.c (Q • T.a)) := by
  let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let v:=B • u
  have hv:v≠u:=by
    intro he
    apply hNE
    apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_elementary_of_common_fixed _ _ ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=(((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ u).mpr rfl]
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val (((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=(((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action]
      exact congrArg (fun z:ℍ=>((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) he
  obtain ⟨D,hDH,hDv,hmin⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.closest_distinct_native_orbit P u v hv.symm
  let F:=D*B
  have hFH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F∈H:=by rw [map_mul];exact H.mul_mem hDH hBH
  have hFu:F • u≠u:=by simpa only [F,mul_smul,v] using hDv
  have hd:dist u (F • u)≤dist u (B • u):=by
    have h:=hmin 1 (by rw [map_one];exact H.one_mem) (by simpa only [one_smul] using hv)
    simpa only [one_smul,F,mul_smul,v] using h
  have hsF:Matrix.trace (A*F*A⁻¹*F⁻¹).val<2+(Matrix.trace A.val)^2:=
    (ellipticTrace_commutator_mono_center A B F hA hd).trans_lt hs
  have hAE:=ellipticTrace_small_commutator_conjugate_product A F hA hFu hsF
  have hE:=native_elliptic_realSL_conjugate A F hA
  have hcenter:=native_elliptic_realSL_conjugate_center A F hA hE
  have hangleE:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle (F*A*F⁻¹) hE=2*Real.pi/n:=
    (ellipticTrace_conjugate_angle A F hA hE).trans hangle
  have hhalf:Real.pi/(n:ℝ)∈Ioc 0 (Real.pi/2):=by
    have hnR:(2:ℝ)≤n:=by exact_mod_cast (show 2≤n by omega)
    have hn0:(0:ℝ)<n:=by linarith only [hnR]
    exact ⟨div_pos Real.pi_pos hn0,div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR⟩
  have hc:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter (F*A*F⁻¹) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hE.1).mp hE):=by
    rw [hcenter]
    exact hFu.symm
  obtain ⟨T,haT,hcT,hbT,hγ,hα,htr,hgen⟩:=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_pair_actual_triangle_positive_angles A (F*A*F⁻¹) hA hE hc hAE
      (Real.pi/n) (Real.pi/n) hhalf hhalf
      (by rw [hangle];ring) (by rw [hangleE];ring)
  refine ⟨F,hFH,hAE,T,haT.trans hcenter,hcT,hbT,hγ,hα,htr,hgen,?_⟩
  intro Q hQH hQne
  rw [haT,hcenter,hcT] at hQne ⊢
  have hQDH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (Q*D)∈H:=by rw [map_mul];exact H.mul_mem hQH hDH
  have hh:=hmin (Q*D) hQDH (by simpa only [F,mul_smul,v] using hQne)
  simpa only [F,mul_smul,v] using hh

/-- Integral angles of the actual pair triangle give its actual original-disc signature. -/
theorem ellipticTrace_triangle_pair_signature
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ) (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (p q r:ℕ) (hp:2≤p) (hq:2≤q) (hr:2≤r)
    (hα:T.alpha=Real.pi/p) (hβ:T.beta=Real.pi/q) (hγ:T.gamma=Real.pi/r)
    (hAH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hBH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hgen:Subgroup.closure ({
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B}:Set (ℍ≃ᵢℍ))=
      triangleConformalGroup T.toClosedHTriangle) :
    ∃hKH:closedTriangleMobiusGroup T.toClosedHTriangle≤H,
      IsMobiusTriangleGroup (closedTriangleMobiusGroup T.toClosedHTriangle) ∧
      HasCofiniteFuchsianSignature
        (fuchsianDiscRestrict P.asFuchsianDisc _ hKH) 0 [p,q,r] 0 := by
  have he:closedTriangleMobiusGroup T.toClosedHTriangle=
      Subgroup.closure ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=
    native_pair_mobius_range_eq_closure A B _ inf_le_right hgen
  have hKH:closedTriangleMobiusGroup T.toClosedHTriangle≤H:=by
    rw [he]
    apply (Subgroup.closure_le H).mpr
    rintro f (rfl|rfl)
    · exact hAH
    · exact hBH
  have ha:IsIntegralTriangleAngle T.toClosedHTriangle.alpha:=
    Or.inr ⟨p,hp,T.closed_angles.1.trans hα⟩
  have hb:IsIntegralTriangleAngle T.toClosedHTriangle.beta:=
    Or.inr ⟨q,hq,T.closed_angles.2.1.trans hβ⟩
  have hc:IsIntegralTriangleAngle T.toClosedHTriangle.gamma:=
    Or.inr ⟨r,hr,T.closed_angles.2.2.trans hγ⟩
  have ht:IsTriangleGroup (triangleConformalGroup T.toClosedHTriangle):=by
    refine ⟨(p:ℕ∞),(q:ℕ∞),(r:ℕ∞),?_,?_,?_,T.toClosedHTriangle,?_,?_,?_,rfl⟩
    · exact_mod_cast hp
    · exact_mod_cast hq
    · exact_mod_cast hr
    · rw [T.closed_angles.1,hα,triangleOrderAngle_nat]
    · rw [T.closed_angles.2.1,hβ,triangleOrderAngle_nat]
    · rw [T.closed_angles.2.2,hγ,triangleOrderAngle_nat]
  refine ⟨hKH,isMobiusTriangleGroup_native_image _ inf_le_right ht,?_⟩
  exact closedTriangle_actual_signature_finite T.toClosedHTriangle p q r hp hq hr
    (T.closed_angles.1.trans hα) (T.closed_angles.2.1.trans hβ) (T.closed_angles.2.2.trans hγ)
    (closedTriangleMobiusData _ ha hb hc)

/-- Two different original finite vertices cannot be interchanged inside
this actual reciprocal-angle triangle group. -/
theorem ellipticTrace_triangle_transporter_not_mem (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (ha:IsIntegralTriangleAngle T.toClosedHTriangle.alpha)
    (hb:IsIntegralTriangleAngle T.toClosedHTriangle.beta)
    (hc:IsIntegralTriangleAngle T.toClosedHTriangle.gamma)
    (F:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hm:F • T.c=T.a) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F∉closedTriangleMobiusGroup T.toClosedHTriangle := by
  rintro ⟨g,hg⟩
  have heval:g.val T.c=F • T.c:=by
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    have he:=nativeConformalSubgroupMobiusHom_action _ inf_le_right g T.c
    change (nativeConformalSubgroupMobiusHom (triangleConformalGroup T.toClosedHTriangle)
      inf_le_right g).val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint
        T.c)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (g.val T.c) at he
    rw [hg] at he
    exact he.symm.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action F T.c)
  let x:(closedTrianglePoincarePolygon T.toClosedHTriangle).Point:=⟨T.c,by
    rw [closedTrianglePoincarePolygon_carrier,T.interior_toClosedHTriangle]
    exact T.c_mem_closure_interior⟩
  let y:(closedTrianglePoincarePolygon T.toClosedHTriangle).Point:=⟨T.a,by
    rw [closedTrianglePoincarePolygon_carrier,T.interior_toClosedHTriangle]
    exact T.a_mem_closure_interior⟩
  have hxy:=closedTriangle_closed_chamber_orbit_unique T.toClosedHTriangle ha hb hc
    x y g.val g.property.1 (heval.trans hm)
  exact T.c_ne_a hxy

/-- The actual zero-trace product gives an original right triangle
with exactly the two specified reciprocal angles. -/
theorem ellipticTrace_halfturn_pair_signature
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)) (hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hAH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hBH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (huv:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (p q:ℕ) (hp:2≤p) (hq:2≤q)
    (hangleA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA=2*Real.pi/p)
    (hangleB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB=2*Real.pi/q)
    (hzero:Matrix.trace (A*B).val=0) :
    ∃K:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃hKH:K≤H,IsMobiusTriangleGroup K ∧
      HasCofiniteFuchsianSignature (fuchsianDiscRestrict P.asFuchsianDisc K hKH) 0 [p,q,2] 0 := by
  have hsmall (m:ℕ) (hm:2≤m) : Real.pi/(m:ℝ)∈Ioc 0 (Real.pi/2):=by
    have hmR:(2:ℝ)≤m:=by exact_mod_cast hm
    have hm0:(0:ℝ)<m:=by linarith only [hmR]
    exact ⟨div_pos Real.pi_pos hm0,
      div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hmR⟩
  have hAB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B)):=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_ne_one_of_centers_ne A B hA hB huv)).mpr
      (by rw [hzero];norm_num)
  obtain ⟨T,_ha,_hc,_hb,hγ,hα,htr,hgen⟩:=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_pair_actual_triangle_positive_angles A B hA hB huv hAB
      (Real.pi/p) (Real.pi/q) (hsmall p hp) (hsmall q hq)
      (by rw [hangleA];ring) (by rw [hangleB];ring)
  have hcos:Real.cos T.beta=0:=by rw [hzero] at htr;nlinarith only [htr]
  have hβ:T.beta=Real.pi/2:=Real.strictAntiOn_cos.injOn
    ⟨T.angles_mem_Ioo.2.1.1.le,T.angles_mem_Ioo.2.1.2.le⟩
    ⟨by positivity,by linarith only [Real.pi_pos]⟩ (by rw [Real.cos_pi_div_two];exact hcos)
  obtain ⟨hKH,htri,hSig⟩:=ellipticTrace_triangle_pair_signature P A B T q 2 p hq (by omega) hp
    hα hβ hγ hAH hBH hgen
  refine ⟨closedTriangleMobiusGroup T.toClosedHTriangle,hKH,htri,hSig.perm_orders ?_⟩
  exact List.perm_append_comm (l₁:=[p]) (l₂:=[q,2])

/-- Failure of the source trace threshold produces one of its two true
reciprocal-angle triangle signatures inside the original group. The
isosceles triangle is a proper subgroup, witnessed by the original
center transporter and literal closed-chamber orbit uniqueness. -/
theorem HalfPlaneFuchsianGroup.ellipticTrace_failed_bound_triangle_signatures
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hAH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hBH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (n:ℕ) (hn:3≤n) (hangle:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA=2*Real.pi/n)
    (hs:Matrix.trace (A*B*A⁻¹*B⁻¹).val<2+(Matrix.trace A.val)^2) :
    ∃r:ℕ,2≤r ∧∃K:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃hKH:K≤H,IsMobiusTriangleGroup K ∧
      ((HasCofiniteFuchsianSignature (fuchsianDiscRestrict P.asFuchsianDisc K hKH) 0 [n,r,n] 0 ∧K≠H) ∨
        HasCofiniteFuchsianSignature (fuchsianDiscRestrict P.asFuchsianDisc K hKH) 0 [n,r,2] 0) := by
  obtain ⟨F,hFH,hAE,T,ha,hc,hb,hγ,hα,htr,hgen,hmin⟩:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ellipticTrace_minimal_conjugate_triangle P A B hA hAH hBH hNE n hn hangle hs
  let E:=F*A*F⁻¹
  have hE:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E):=native_elliptic_realSL_conjugate A F hA
  have hEH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E∈H:=by
    simp only [E,map_mul,map_inv]
    exact H.mul_mem (H.mul_mem hFH hAH) (H.inv_mem hFH)
  have hEc:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter E ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff E hE.1).mp hE)=T.a:=
    (native_elliptic_realSL_conjugate_center A F hA hE).trans ha.symm
  have hEa:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle E hE=2*Real.pi/n:=
    (ellipticTrace_conjugate_angle A F hA hE).trans hangle
  have hAEH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*E)∈H:=by rw [map_mul];exact H.mul_mem hAH hEH
  have hTangle:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough T.b T.c T.b_ne_c)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough T.b T.a
        T.a_ne_b.symm)=T.beta:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _ _
  obtain ⟨C,hC,hCH,hlC,hcenterC,hcut⟩:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.minimal_center_primitive_cut_of_trace P T.b T.c T.a T.b_ne_c T.a_ne_b.symm
      (A*E) hAE hAEH hb.symm (by rwa [hTangle]) hmin
  let r:=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)
  have hr:2≤r:=least_elliptic_realSL_order_two_le C hC hlC
  refine ⟨r,hr,?_⟩
  rcases hcut with hfirst|⟨hsecond,_hcollision,hrad⟩
  · have hβ:T.beta=Real.pi/r:=by rwa [hTangle] at hfirst
    obtain ⟨hKH,htri,hSig⟩:=ellipticTrace_triangle_pair_signature P A E T n r n
      (by omega) hr (by omega) hα hβ hγ hAH hEH hgen
    refine ⟨closedTriangleMobiusGroup T.toClosedHTriangle,hKH,htri,Or.inl ⟨hSig,?_⟩⟩
    have hm:F • T.c=T.a:=by rw [hc,←ha]
    have hnot:=ellipticTrace_triangle_transporter_not_mem T
      (Or.inr ⟨n,by omega,T.closed_angles.1.trans hα⟩)
      (Or.inr ⟨r,hr,T.closed_angles.2.1.trans hβ⟩)
      (Or.inr ⟨n,by omega,T.closed_angles.2.2.trans hγ⟩) F hm
    intro heq
    exact hnot (heq.symm ▸hFH)
  · have hβ:T.beta=2*Real.pi/r:=by rwa [hTangle] at hsecond
    obtain ⟨R,hRC,hR,_hlR,hcenterR,horderR,_hcyclicR,hangleR⟩:=
      least_elliptic_positive_orientation C hC hlC
    have hRH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R∈H:=by
      rcases hRC with rfl|rfl
      · exact hCH
      · rw [map_inv];exact H.inv_mem hCH
    have hcenterRT:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter R ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff R hR.1).mp hR)=T.b:=
      hcenterR.trans hcenterC
    let U:=T.cyclic.cyclic
    have hUβ:U.beta=T.alpha:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _ _
    have hUγ:U.gamma=T.beta:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _ _
    have hBa:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle E hE=2*U.beta:=by rw [hUβ,hα,hEa];ring
    have hRa:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle R hR=U.gamma:=by rw [hUγ,hβ];simpa only [horderR] using hangleR
    have hzero:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_isosceles_fold_product_trace_zero U hrad E R hE hR hEc hcenterRT hBa hRa
    have hne:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter E ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff E hE.1).mp hE)≠
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter R ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff R hR.1).mp hR):=by
      rw [hEc,hcenterRT];exact T.a_ne_b
    obtain ⟨K,hKH,htri,hSig⟩:=ellipticTrace_halfturn_pair_signature P E R hE hR hEH hRH
      hne n r (by omega) hr hEa (by simpa only [horderR] using hangleR) hzero
    exact ⟨K,hKH,htri,Or.inr hSig⟩

/-- Reversing the original elliptic generator preserves the actual commutator trace. -/
theorem ellipticTrace_commutator_inverse_left (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (A⁻¹*B*A*B⁻¹).val=Matrix.trace (A*B*A⁻¹*B⁻¹).val := by
  calc
    _=Matrix.trace (A⁻¹*(A*B*A⁻¹*B⁻¹)⁻¹*(A⁻¹)⁻¹).val:=by congr 2;group
    _=Matrix.trace ((A*B*A⁻¹*B⁻¹)⁻¹).val:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation _ _
    _=Matrix.trace (A*B*A⁻¹*B⁻¹).val:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_inverse _

/-- The original least-angle elliptic can have either orientation in the
chosen half-plane. Reversing it preserves both the original pair group
and the source trace, so the actual triangle signatures still follow. -/
theorem HalfPlaneFuchsianGroup.ellipticTrace_failed_least_bound_triangle_signatures
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hlA:HasLeastEllipticRotation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hAH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hBH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (n:ℕ) (hn:3≤n) (horder:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=n)
    (hs:Matrix.trace (A*B*A⁻¹*B⁻¹).val<2+4*(Real.cos (Real.pi/n))^2) :
    ∃r:ℕ,2≤r ∧∃K:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃hKH:K≤H,IsMobiusTriangleGroup K ∧
      ((HasCofiniteFuchsianSignature (fuchsianDiscRestrict P.asFuchsianDisc K hKH) 0 [n,r,n] 0 ∧K≠H) ∨
        HasCofiniteFuchsianSignature (fuchsianDiscRestrict P.asFuchsianDisc K hKH) 0 [n,r,2] 0) := by
  obtain ⟨R,hRA,hR,hlR,_hcenterR,horderR,_hcyclicR,hangleR⟩:=
    least_elliptic_positive_orientation A hA hlA
  have hRH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R∈H:=by
    rcases hRA with rfl|rfl
    · exact hAH
    · rw [map_inv];exact H.inv_mem hAH
  have hNER:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    rcases hRA with rfl|rfl
    · exact hNE
    · rwa [map_inv,closure_pair_inverse_left]
  have hcomm:Matrix.trace (R*B*R⁻¹*B⁻¹).val=Matrix.trace (A*B*A⁻¹*B⁻¹).val:=by
    rcases hRA with rfl|rfl
    · rfl
    · simpa only [inv_inv] using ellipticTrace_commutator_inverse_left A B
  have htr:(Matrix.trace R.val)^2=4*(Real.cos (Real.pi/n))^2:=by
    have h:=hlR.squaredTrace_order
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,horderR,horder] at h
    exact Complex.ofReal_injective h
  apply _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ellipticTrace_failed_bound_triangle_signatures P R B hR hRH hBH hNER n hn
  · simpa only [horderR,horder] using hangleR
  · rw [hcomm,htr];exact hs

end LowDimensionalTopology.Geometry.Fuchsian
