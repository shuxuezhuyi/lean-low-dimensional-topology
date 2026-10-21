/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeInfiniteCounterexample
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.FullDisplacementDetermination
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
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

/-- Conjugacy by either orientation preserves the actual conformal subgroup. -/
theorem native_conjugate_conformal_mem (e f : ℍ≃ᵢℍ)
    (hf : f∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) : e*f*e⁻¹∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  obtain ⟨g,_hg,rfl⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_normalized_hGLIsometry e
  obtain ⟨A,rfl⟩:=hf
  have hdet : (g.val*A.val*(g⁻¹).val).det=1 := by
    rw [Matrix.det_mul,Matrix.det_mul,A.det_coe,mul_one]
    have h:=congrArg Matrix.det g.mul_inv
    simpa only [Matrix.det_mul,Matrix.det_one] using h
  let B : Matrix.SpecialLinearGroup (Fin 2) ℝ:=⟨g.val*A.val*(g⁻¹).val,hdet⟩
  refine ⟨B,?_⟩
  have hB : Matrix.SpecialLinearGroup.mapGL ℝ B=
      g*Matrix.SpecialLinearGroup.mapGL ℝ A*g⁻¹ := by
    apply Units.ext
    rfl
  apply IsometryEquiv.ext
  intro z
  change (Matrix.SpecialLinearGroup.mapGL ℝ B) • z=
    g • ((Matrix.SpecialLinearGroup.mapGL ℝ A) • (g⁻¹ • z))
  rw [hB,mul_smul,mul_smul]

theorem native_conjugate_conformal_group (e : ℍ≃ᵢℍ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  apply le_antisymm
  · intro f hf
    obtain ⟨g,hg,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff e _ f).mp hf
    exact native_conjugate_conformal_mem e g hg
  · intro f hf
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff e _ f).mpr
    refine ⟨e⁻¹*f*e,?_,by group⟩
    simpa only [inv_inv] using native_conjugate_conformal_mem e⁻¹ f hf

theorem equal_angle_triangle_conformalGroups_conjugate
    (T S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα : T.alpha=S.alpha) (hβ : T.beta=S.beta) (hγ : T.gamma=S.gamma) :
    ∃e : ℍ≃ᵢℍ,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (triangleConformalGroup T)=
      triangleConformalGroup S := by
  obtain ⟨e,he⟩:=equal_angle_triangle_reflectionGroups_conjugate T S hα hβ hγ
  refine ⟨e,?_⟩
  unfold triangleConformalGroup _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
  rw [Subgroup.map_inf _ _ _ (MulAut.conj e).injective]
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (triangleReflectionGroup T) ⊓
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup= _
  rw [he,native_conjugate_conformal_group]

theorem hecke_order_angle_bounds (q : ℕ∞) (hq : 3≤q) :
    0≤triangleOrderAngle q ∧ triangleOrderAngle q≤Real.pi/3 := by
  induction q using ENat.recTopCoe with
  | top => rw [triangleOrderAngle_top];exact ⟨le_rfl,by positivity⟩
  | coe q =>
    have hqN : 3≤q:=by exact_mod_cast hq
    rw [triangleOrderAngle_nat]
    refine ⟨by positivity,?_⟩
    exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
      (by exact_mod_cast hqN)

def standardHeckeTriangle (q : ℕ∞) (hq : 3≤q) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle :=
  prescribedIdealHTriangle (Real.pi/2) (triangleOrderAngle q) (by positivity)
    (hecke_order_angle_bounds q hq).1
    (by have h:=(hecke_order_angle_bounds q hq).2;linarith only [h,Real.pi_pos])

theorem standardHeckeTriangle_angles (q : ℕ∞) (hq : 3≤q) :
    (standardHeckeTriangle q hq).alpha=Real.pi/2 ∧
      (standardHeckeTriangle q hq).beta=triangleOrderAngle q ∧
      (standardHeckeTriangle q hq).gamma=0 :=
  prescribedIdealHTriangle_angles _ _ _ _ _

def standardHeckeGroup (q : ℕ∞) (hq : 3≤q) : Subgroup (ℍ≃ᵢℍ) :=
  triangleConformalGroup (standardHeckeTriangle q hq)

theorem standardHeckeGroup_isHecke (q : ℕ∞) (hq : 3≤q) :
    IsHeckeGroup (standardHeckeGroup q hq) := by
  refine ⟨q,hq,by norm_num,le_trans (by norm_num : (2:ℕ∞)≤3) hq,by simp,?_⟩
  have htwo : triangleOrderAngle 2=Real.pi/2 := by norm_num [triangleOrderAngle]
  rw [htwo,triangleOrderAngle_top]
  exact ⟨standardHeckeTriangle q hq,(standardHeckeTriangle_angles q hq).1,
    (standardHeckeTriangle_angles q hq).2.1,(standardHeckeTriangle_angles q hq).2.2,rfl⟩

/-- Every original Hecke group, including the two-cusp case, is conjugate to its
actual standard triangle group. No discreteness or conjugator is assumed. -/
theorem IsHeckeGroup.conjugate_standard {G : Subgroup (ℍ≃ᵢℍ)} (hG : IsHeckeGroup G) :
    ∃q : ℕ∞,∃hq : 3≤q,∃e : ℍ≃ᵢℍ,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e G=standardHeckeGroup q hq := by
  obtain ⟨q,hq,_,_,_,T,hα,hβ,hγ,rfl⟩:=hG
  have htwo : triangleOrderAngle 2=Real.pi/2 := by norm_num [triangleOrderAngle]
  rw [htwo] at hα
  rw [triangleOrderAngle_top] at hγ
  obtain ⟨e,he⟩:=equal_angle_triangle_conformalGroups_conjugate T
    (standardHeckeTriangle q hq)
    (hα.trans (standardHeckeTriangle_angles q hq).1.symm)
    (hβ.trans (standardHeckeTriangle_angles q hq).2.1.symm)
    (hγ.trans (standardHeckeTriangle_angles q hq).2.2.symm)
  exact ⟨q,hq,e,he⟩

theorem standardHeckeTriangle_first_matrix (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL (standardHeckeTriangle q hq).sideLineA
      (standardHeckeTriangle q hq).sideLineB=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (triangleOrderAngle q)) := by
  rw [standardHeckeTriangle,prescribedIdealHTriangle_sideA,prescribedIdealHTriangle_sideB,
    Real.cos_pi_div_two,neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.mul_apply,Fin.sum_univ_two]

theorem standardHeckeTriangle_second_matrix (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL (standardHeckeTriangle q hq).sideLineC
      (standardHeckeTriangle q hq).sideLineB= -modularInversionSL := by
  rw [standardHeckeTriangle,prescribedIdealHTriangle_circle,prescribedIdealHTriangle_sideB,
    Real.cos_pi_div_two,neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,modularInversionSL,
      Matrix.SpecialLinearGroup.coe_neg,Matrix.mul_apply,Fin.sum_univ_two]

theorem standardHeckeGroup_generators (q : ℕ∞) (hq : 3≤q) :
    standardHeckeGroup q hq=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (triangleOrderAngle q))),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL}:Set (ℍ≃ᵢℍ)) := by
  rw [standardHeckeGroup,triangleConformalGroup_eq_pairProductGroup]
  change Subgroup.closure _=Subgroup.closure _
  rw [reflectionProductSL_native,reflectionProductSL_native,
    standardHeckeTriangle_first_matrix,standardHeckeTriangle_second_matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_neg]

theorem native_subgroupConjugate_eq_of_mem (H : Subgroup (ℍ≃ᵢℍ)) (e : ℍ≃ᵢℍ)
    (he : e∈H) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e H=H := by
  apply le_antisymm
  · intro f hf
    obtain ⟨g,hg,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff e H f).mp hf
    exact H.mul_mem (H.mul_mem he hg) (H.inv_mem he)
  · intro f hf
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff e H f).mpr
      ⟨e⁻¹*f*e,H.mul_mem (H.mul_mem (H.inv_mem he) hf) he,by group⟩

theorem triangle_conformal_normalized_by_reflectionGroup
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (e : ℍ≃ᵢℍ) (he : e∈triangleReflectionGroup T) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (triangleConformalGroup T)=triangleConformalGroup T := by
  unfold triangleConformalGroup _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
  rw [Subgroup.map_inf _ _ _ (MulAut.conj e).injective]
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (triangleReflectionGroup T) ⊓
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup= _
  rw [native_subgroupConjugate_eq_of_mem _ e he,native_conjugate_conformal_group]

theorem standardHeckeGroup_axis_conjugate (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0))
      (standardHeckeGroup q hq)=standardHeckeGroup q hq := by
  apply triangle_conformal_normalized_by_reflectionGroup
  have hB : (standardHeckeTriangle q hq).sideLineB=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 := by
    rw [standardHeckeTriangle,prescribedIdealHTriangle_sideB,Real.cos_pi_div_two,neg_zero]
  apply Subgroup.subset_closure
  refine ⟨(standardHeckeTriangle q hq).sideLineB,?_,?_⟩
  · simp [triangleReflectionSides]
  · rw [hB]

theorem native_conformal_or_axis_mul_conformal (e : ℍ≃ᵢℍ) :
    e∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup ∨
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0)*e∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  obtain ⟨A,hA|hA⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isometry_exists_sl2_or_reflected e.isometry
  · left
    refine ⟨A,?_⟩
    apply IsometryEquiv.ext
    intro z
    exact (congrFun hA z).symm
  · right
    let R:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0)
    have he : e=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A*R := by
      apply IsometryEquiv.ext
      intro z
      change e z=A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection 0 z
      have hJ : UpperHalfPlane.J • z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection 0 z := by
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.coe_J_smul,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_coe]
        norm_num
      exact (congrFun hA z).trans (congrArg (fun w : ℍ=>A • w) hJ)
    rw [he]
    have h:=native_conjugate_conformal_mem R (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) ⟨A,rfl⟩
    rw [show R⁻¹=R from halfPlaneLineReflectionIsometry_inv _,mul_assoc] at h
    exact h

/-- The standardization can be achieved by a genuine conformal isometry even if
an initial equal-angle conjugator reverses orientation. -/
theorem IsHeckeGroup.conformal_conjugate_standard {G : Subgroup (ℍ≃ᵢℍ)}
    (hG : IsHeckeGroup G) :
    ∃q : ℕ∞,∃hq : 3≤q,∃e : ℍ≃ᵢℍ,e∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e G=standardHeckeGroup q hq := by
  obtain ⟨q,hq,e,he⟩:=hG.conjugate_standard
  rcases native_conformal_or_axis_mul_conformal e with hc|hc
  · exact ⟨q,hq,e,hc,he⟩
  · refine ⟨q,hq,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0)*e,hc,?_⟩
    rw [←native_subgroupConjugate_compose,he,standardHeckeGroup_axis_conjugate]

end LowDimensionalTopology.Geometry.Fuchsian
