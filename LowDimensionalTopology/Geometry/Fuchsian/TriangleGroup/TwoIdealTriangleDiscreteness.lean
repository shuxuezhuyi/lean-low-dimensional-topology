/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.OneIdealTriangleDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDiscreteness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

def twoIdealHeckeParameter (p : ℕ) : ℝ:=2*Real.cos (Real.pi/(2*p:ℕ))

theorem twoIdealHeckeParameter_pos (p : ℕ) (hp : 2≤p) : 0<twoIdealHeckeParameter p := by
  have hh:=heckeCorner_re_pos (2*p) (by omega)
  change 0<Real.cos (Real.pi/(2*p:ℕ)) at hh
  exact mul_pos (by norm_num) hh

theorem twoIdealHeckeParameter_sq (p : ℕ) (hp : 2≤p) :
    (twoIdealHeckeParameter p)^2=2+2*Real.cos (Real.pi/(p:ℝ)) := by
  have hp0 : (p:ℝ)≠0:=by positivity
  have hangle : 2*(Real.pi/(2*p:ℕ))=Real.pi/(p:ℝ):=by
    push_cast
    field_simp
  have hh:=Real.cos_two_mul (Real.pi/(2*p:ℕ))
  rw [hangle] at hh
  unfold twoIdealHeckeParameter
  nlinarith

def twoIdealIntegralTriangle (p : ℕ) (hp : 2≤p) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle:=
  prescribedIdealHTriangle (Real.pi/(p:ℝ)) 0 (by positivity) (by norm_num) (by
    have hpR : (2:ℝ)≤(p:ℝ):=by exact_mod_cast hp
    rw [add_zero]
    apply (div_lt_iff₀ (by positivity : 0<(p:ℝ))).mpr
    nlinarith [Real.pi_pos])

def twoIdealHeckeConjugator (p : ℕ) (hp : 2≤p) : GL (Fin 2) ℝ:=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![-twoIdealHeckeParameter p,1;0,1] (by
    rw [Matrix.det_fin_two]
    change (-twoIdealHeckeParameter p)*1-1*0≠0
    simpa only [mul_one,mul_zero,sub_zero] using neg_ne_zero.mpr (twoIdealHeckeParameter_pos p hp).ne')

def twoIdealRightSL : Matrix.SpecialLinearGroup
    (Fin 2) ℝ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 2*modularInversionSL

def twoIdealLeftSL (p : ℕ) : Matrix.SpecialLinearGroup (Fin 2) ℝ:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-2*Real.cos (Real.pi/(p:ℝ)))*modularInversionSL

theorem twoIdealIntegralTriangle_right_product (p : ℕ) (hp : 2≤p) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL (twoIdealIntegralTriangle p hp).sideLineA
      (twoIdealIntegralTriangle p hp).sideLineC=twoIdealRightSL := by
  rw [twoIdealIntegralTriangle,prescribedIdealHTriangle_sideA,prescribedIdealHTriangle_circle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,twoIdealRightSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem twoIdealIntegralTriangle_left_product (p : ℕ) (hp : 2≤p) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL (twoIdealIntegralTriangle p hp).sideLineB
      (twoIdealIntegralTriangle p hp).sideLineC=twoIdealLeftSL p := by
  rw [twoIdealIntegralTriangle,prescribedIdealHTriangle_sideB,prescribedIdealHTriangle_circle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,twoIdealLeftSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,
      Matrix.mul_apply,Fin.sum_univ_two]

/-- A real matrix intertwiner gives conjugacy of the actual native transformations,
allowing a negative-determinant conjugating isometry. -/
theorem native_hGL_hSL_conjugation_of_intertwiner (M : GL (Fin 2) ℝ)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hM : M*Matrix.SpecialLinearGroup.mapGL ℝ A=Matrix.SpecialLinearGroup.mapGL ℝ B*M) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry M*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry M)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B := by
  have hh : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry M*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry M:=by
    apply IsometryEquiv.ext
    intro z
    change M • (Matrix.SpecialLinearGroup.mapGL ℝ A • z)=
      Matrix.SpecialLinearGroup.mapGL ℝ B • (M • z)
    rw [←mul_smul,←mul_smul,hM]
  rw [hh]
  group

theorem twoIdealHeckeConjugator_parabolic (p : ℕ) (hp : 2≤p) :
    twoIdealHeckeConjugator p hp*Matrix.SpecialLinearGroup.mapGL ℝ
      (modularInversionSL*standardHeckeCornerSL (2*p))=
    Matrix.SpecialLinearGroup.mapGL ℝ (-twoIdealRightSL)*twoIdealHeckeConjugator p hp := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoIdealHeckeConjugator,twoIdealRightSL,standardHeckeCornerSL,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,Matrix.SpecialLinearGroup.coe_neg,
      Matrix.mul_apply,Fin.sum_univ_two,twoIdealHeckeParameter]
  ring

theorem twoIdealHeckeConjugator_elliptic (p : ℕ) (hp : 2≤p) :
    twoIdealHeckeConjugator p hp*Matrix.SpecialLinearGroup.mapGL ℝ
      (standardHeckeCornerSL (2*p)^2)=
    Matrix.SpecialLinearGroup.mapGL ℝ (-twoIdealLeftSL p)*twoIdealHeckeConjugator p hp := by
  have he:=twoIdealHeckeParameter_sq p hp
  have he3:=congrArg (fun x : ℝ=>x*twoIdealHeckeParameter p) he
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoIdealHeckeConjugator,twoIdealLeftSL,standardHeckeCornerSL,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,Matrix.SpecialLinearGroup.coe_neg,pow_two,
      Matrix.mul_apply,Fin.sum_univ_two] <;>
    dsimp only [twoIdealHeckeParameter] at he he3 ⊢ <;>
    simp only [Nat.cast_mul,Nat.cast_ofNat] at he he3 ⊢ <;> nlinarith

theorem twoIdealIntegralTriangle_angles (p : ℕ) (hp : 2≤p) :
    (twoIdealIntegralTriangle p hp).alpha=Real.pi/(p:ℝ) ∧
      (twoIdealIntegralTriangle p hp).beta=0 ∧ (twoIdealIntegralTriangle p hp).gamma=0 :=
  prescribedIdealHTriangle_angles _ _ _ _ _

/-- The original two-ideal triangle group lies in an explicitly conjugated genuine Hecke group. -/
theorem twoIdealIntegralTriangle_conformal_le_hecke (p : ℕ) (hp : 2≤p) :
    triangleConformalGroup (twoIdealIntegralTriangle p hp)≤_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry (twoIdealHeckeConjugator p hp))
      (standardHeckeGroup (2*p:ℕ) (by exact_mod_cast (show 3≤2*p by omega))) := by
  let H:=standardHeckeGroup (2*p:ℕ) (by exact_mod_cast (show 3≤2*p by omega))
  let e:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry (twoIdealHeckeConjugator p hp)
  have hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL∈H:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL∈standardHeckeGroup (2*p:ℕ) _
    rw [standardHeckeGroup_cyclic_sup (2*p) (by omega)]
    exact (show Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL)≤
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL)⊔Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL (2*p))) from le_sup_left)
      (Subgroup.mem_zpowers _)
  have hU : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL (2*p))∈H:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL (2*p))∈standardHeckeGroup (2*p:ℕ) _
    rw [standardHeckeGroup_cyclic_sup (2*p) (by omega)]
    exact (show Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL (2*p)))≤
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL)⊔Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL (2*p))) from le_sup_right)
      (Subgroup.mem_zpowers _)
  have hP : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (modularInversionSL*standardHeckeCornerSL (2*p))∈H:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_*_)∈H
    rw [map_mul]
    exact H.mul_mem hS hU
  have hQ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL (2*p)^2)∈H:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_^2)∈H
    rw [map_pow]
    exact H.pow_mem hU 2
  have hx:=native_hGL_hSL_conjugation_of_intertwiner (twoIdealHeckeConjugator p hp)
    (modularInversionSL*standardHeckeCornerSL (2*p)) (-twoIdealRightSL)
    (twoIdealHeckeConjugator_parabolic p hp)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_neg] at hx
  have hy:=native_hGL_hSL_conjugation_of_intertwiner (twoIdealHeckeConjugator p hp)
    (standardHeckeCornerSL (2*p)^2) (-twoIdealLeftSL p)
    (twoIdealHeckeConjugator_elliptic p hp)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_neg] at hy
  have hxMem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry twoIdealRightSL∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e H:=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff e H _).mpr ⟨_,hP,hx⟩
  have hyMem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (twoIdealLeftSL p)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e H:=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff e H _).mpr ⟨_,hQ,hy⟩
  rw [triangleConformalGroup_eq_crossPairProducts,reflectionProductSL_native,
    reflectionProductSL_native,twoIdealIntegralTriangle_left_product,twoIdealIntegralTriangle_right_product]
  apply (Subgroup.closure_le _).mpr
  rintro g (rfl|he)
  · exact hyMem
  · exact mem_singleton_iff.mp he ▸ hxMem

theorem twoIdealIntegralTriangle_conformal_discrete (p : ℕ) (hp : 2≤p) :
    DiscreteTopology (triangleConformalGroup (twoIdealIntegralTriangle p hp)) := by
  let H:=standardHeckeGroup (2*p:ℕ) (by exact_mod_cast (show 3≤2*p by omega))
  let e:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry (twoIdealHeckeConjugator p hp)
  let : DiscreteTopology H:=standardHeckeGroup_finite_discrete (2*p) (by omega)
  let : DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e H):=native_subgroupConjugate_discrete e H
  let F : triangleConformalGroup (twoIdealIntegralTriangle p hp)→_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e H:=
    fun f=>⟨f.val,twoIdealIntegralTriangle_conformal_le_hecke p hp f.property⟩
  have hcont : Continuous F:=continuous_subtype_val.subtype_mk _
  have hinj : Function.Injective F:=by
    intro f g he
    exact Subtype.ext (congrArg (fun z : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e H=>z.val) he)
  exact DiscreteTopology.of_continuous_injective hcont hinj

/-- Every original two-ideal reciprocal-angle triangle has a discrete original conformal subgroup. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_two_ideal
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p : ℕ) (hp : 2≤p) (ha : T.alpha=Real.pi/(p:ℝ)) (hb : T.beta=0) (hc : T.gamma=0) :
    DiscreteTopology (triangleConformalGroup T) := by
  let U:=twoIdealIntegralTriangle p hp
  have hu:=twoIdealIntegralTriangle_angles p hp
  obtain ⟨e,he⟩:=equal_angle_triangle_conformalGroups_conjugate T U
    (ha.trans hu.1.symm) (hb.trans hu.2.1.symm) (hc.trans hu.2.2.symm)
  let : DiscreteTopology (triangleConformalGroup U):=twoIdealIntegralTriangle_conformal_discrete p hp
  have hd : DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e⁻¹ (triangleConformalGroup U)):=
    native_subgroupConjugate_discrete e⁻¹ (triangleConformalGroup U)
  rw [←he,native_subgroupConjugate_compose,inv_mul_cancel,native_subgroupConjugate_one] at hd
  exact hd

/-- Its entire original three-mirror group is genuinely discrete in the native topology. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_two_ideal
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p : ℕ) (hp : 2≤p) (ha : T.alpha=Real.pi/(p:ℝ)) (hb : T.beta=0) (hc : T.gamma=0) :
    DiscreteTopology (triangleReflectionGroup T) :=
  (triangle_discrete_full_iff_conformal T).mpr
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_two_ideal T p hp ha hb hc)

end LowDimensionalTopology.Geometry.Fuchsian
