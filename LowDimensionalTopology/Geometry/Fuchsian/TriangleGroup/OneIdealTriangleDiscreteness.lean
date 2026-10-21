/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckePingPongGeometry
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativePoincarePolygons
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckePingPongGroups
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDiscreteness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Pointwise ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- The actual mirror in the imaginary axis. -/
def idealTriangleAxisMirror : ℍ ≃ᵢ ℍ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0)

theorem idealTriangleAxisMirror_coe (z : ℍ) :
    (idealTriangleAxisMirror z:ℂ)= -conj (z:ℂ) := by
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection 0 z:ℂ)= -conj (z:ℂ)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_coe]
  simp

theorem idealTriangleAxisMirror_re (z : ℍ) : (idealTriangleAxisMirror z).re= -z.re := by
  exact congrArg Complex.re (idealTriangleAxisMirror_coe z)

theorem idealTriangleAxisMirror_I : idealTriangleAxisMirror UpperHalfPlane.I=UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [idealTriangleAxisMirror_coe]
  norm_num [UpperHalfPlane.coe_I]

theorem idealTriangleAxisMirror_inv : idealTriangleAxisMirror⁻¹=idealTriangleAxisMirror :=
  halfPlaneLineReflectionIsometry_inv _

def idealTriangleLeftSector (p : ℕ) (hp : 3≤p) : Set ℍ:=
  idealTriangleAxisMirror ⁻¹' heckePingPongSector p hp

def idealTriangleMiddleGap (p q : ℕ) (hp : 3≤p) (hq : 3≤q) : Set ℍ:=
  idealTriangleLeftSector p hp∩heckePingPongSector q hq

theorem idealTriangleLeftSector_isOpen (p : ℕ) (hp : 3≤p) :
    IsOpen (idealTriangleLeftSector p hp) :=
  (heckePingPongSector_isOpen p hp).preimage idealTriangleAxisMirror.continuous

theorem idealTriangleLeftSector_contains_nonnegative (p : ℕ) (hp : 3≤p)
    (z : ℍ) (hz : 0≤z.re) : z∈idealTriangleLeftSector p hp := by
  apply heckePingPongSector_contains_nonpositive p hp (idealTriangleAxisMirror z)
  rw [idealTriangleAxisMirror_re]
  linarith

theorem idealTriangleLeftSector_compl_negative (p : ℕ) (hp : 3≤p)
    (z : ℍ) (hz : z∉idealTriangleLeftSector p hp) : z.re<0 := by
  by_contra he
  exact hz (idealTriangleLeftSector_contains_nonnegative p hp z (not_lt.mp he))

theorem idealTriangleMiddleGap_isOpen (p q : ℕ) (hp : 3≤p) (hq : 3≤q) :
    IsOpen (idealTriangleMiddleGap p q hp hq) :=
  (idealTriangleLeftSector_isOpen p hp).inter (heckePingPongSector_isOpen q hq)

theorem idealTriangleMiddleGap_I (p q : ℕ) (hp : 3≤p) (hq : 3≤q) :
    UpperHalfPlane.I∈idealTriangleMiddleGap p q hp hq := by
  constructor
  · exact idealTriangleLeftSector_contains_nonnegative p hp _ (by norm_num)
  · exact heckePingPongSector_contains_nonpositive q hq _ (by norm_num)

theorem idealTriangleMiddleGap_nonempty (p q : ℕ) (hp : 3≤p) (hq : 3≤q) :
    (idealTriangleMiddleGap p q hp hq).Nonempty :=
  ⟨UpperHalfPlane.I,idealTriangleMiddleGap_I p q hp hq⟩

end LowDimensionalTopology.Geometry.Fuchsian
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  Set
  Topology
open scoped UpperHalfPlane Pointwise MatrixGroups

def idealTriangleLeftConjugation : (ℍ≃ᵢℍ)→* (ℍ≃ᵢℍ):=
  (MulAut.conj idealTriangleAxisMirror).toMonoidHom

def idealTriangleLeftCyclic (p : ℕ) : Subgroup (ℍ≃ᵢℍ):=
  (Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL p))).map idealTriangleLeftConjugation

def idealTriangleRightCyclic (q : ℕ) : Subgroup (ℍ≃ᵢℍ):=
  Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q))

def idealTriangleCyclicSup (p q : ℕ) : Subgroup (ℍ≃ᵢℍ):=
  idealTriangleLeftCyclic p⊔idealTriangleRightCyclic q

theorem idealTriangleAxisMirror_involutive (z : ℍ) :
    idealTriangleAxisMirror (idealTriangleAxisMirror z)=z :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).reflection_involutive z

theorem idealTriangleLeftConjugation_mirror (g : ℍ≃ᵢℍ) (z : ℍ) :
    idealTriangleAxisMirror (idealTriangleLeftConjugation g z)=g (idealTriangleAxisMirror z) := by
  change idealTriangleAxisMirror (idealTriangleAxisMirror (g (idealTriangleAxisMirror⁻¹ z)))=_
  rw [idealTriangleAxisMirror_involutive,idealTriangleAxisMirror_inv]

theorem idealTriangleLeftSector_disjoint_translate (p : ℕ) (hp : 3≤p)
    (g : ℍ≃ᵢℍ) (hg : g∈idealTriangleLeftCyclic p) (hne : g≠1) :
    Disjoint (g • idealTriangleLeftSector p hp) (idealTriangleLeftSector p hp) := by
  obtain ⟨a,ha,he⟩:=hg
  have ha1 : a≠1:=by
    intro h1
    rw [h1,map_one] at he
    exact hne he.symm
  have hdis:=heckePingPongSector_disjoint_translate p hp a ha ha1
  apply disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ hzx
  apply disjoint_left.mp hdis
  · refine ⟨idealTriangleAxisMirror x,hx,?_⟩
    change a (idealTriangleAxisMirror x)=idealTriangleAxisMirror (g x)
    rw [←he,idealTriangleLeftConjugation_mirror]
  · exact hzx

/-- Two genuine elliptic sectors at distinct finite vertices supply a true open wandering gap. -/
theorem idealTriangleCyclicSup_discrete (p q : ℕ) (hp : 3≤p) (hq : 3≤q) :
    DiscreteTopology (idealTriangleCyclicSup p q) := by
  apply discreteTopology_sup_of_two_pingPong (idealTriangleLeftCyclic p) (idealTriangleRightCyclic q)
    (idealTriangleLeftSector p hp)ᶜ (heckePingPongSector q hq)ᶜ
    (idealTriangleMiddleGap p q hp hq)
    (idealTriangleMiddleGap_isOpen p q hp hq) (idealTriangleMiddleGap_nonempty p q hp hq)
  · intro g hg hne
    rintro z ⟨x,hx,rfl⟩
    intro hz
    have hxLeft : x∈idealTriangleLeftSector p hp:=by
      apply idealTriangleLeftSector_contains_nonnegative p hp x
      exact (heckePingPongSector_compl_positive q hq x hx).le
    exact disjoint_left.mp (idealTriangleLeftSector_disjoint_translate p hp g hg hne)
      ⟨x,hxLeft,rfl⟩ hz
  · intro g hg hne
    rintro z ⟨x,hx,rfl⟩
    intro hz
    have hxRight : x∈heckePingPongSector q hq:=by
      apply heckePingPongSector_contains_nonpositive q hq x
      exact (idealTriangleLeftSector_compl_negative p hp x hx).le
    exact disjoint_left.mp (heckePingPongSector_disjoint_translate q hq g hg hne)
      ⟨x,hxRight,rfl⟩ hz
  · intro g hg hne
    rintro z ⟨x,hx,rfl⟩
    intro hz
    exact disjoint_left.mp (idealTriangleLeftSector_disjoint_translate p hp g hg hne)
      ⟨x,hx.1,rfl⟩ hz
  · intro g hg hne
    rintro z ⟨x,hx,rfl⟩
    intro hz
    exact disjoint_left.mp (heckePingPongSector_disjoint_translate q hq g hg hne)
      ⟨x,hx.2,rfl⟩ hz
  · apply disjoint_left.mpr
    intro z hz hzu
    exact hz hzu.1
  · apply disjoint_left.mpr
    intro z hz hzu
    exact hz hzu.2

end LowDimensionalTopology.Geometry.Fuchsian
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  Set
  Topology
open scoped UpperHalfPlane Pointwise MatrixGroups ComplexConjugate

theorem idealTriangleLeftConjugation_inversion :
    idealTriangleLeftConjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL := by
  apply IsometryEquiv.ext
  intro z
  apply UpperHalfPlane.ext
  change (idealTriangleAxisMirror (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL (idealTriangleAxisMirror⁻¹ z)):ℂ)=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL z:ℂ)
  rw [idealTriangleAxisMirror_inv,idealTriangleAxisMirror_coe]
  change -conj ((modularInversionSL • idealTriangleAxisMirror z:ℍ):ℂ)=((modularInversionSL • z:ℍ):ℂ)
  rw [modularInversionSL_action_coe,idealTriangleAxisMirror_coe,modularInversionSL_action_coe]
  simp [div_eq_mul_inv]

theorem idealTriangleLeftConjugation_corner (p : ℕ) :
    idealTriangleLeftConjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL p))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-2*Real.cos (Real.pi/(p:ℝ)))*modularInversionSL) := by
  have hT : idealTriangleLeftConjugation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(p:ℝ)))))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-2*Real.cos (Real.pi/(p:ℝ)))):=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(p:ℝ))))*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0))⁻¹=_
    simpa only [neg_mul] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_axis_reflection_conjugation (2*Real.cos (Real.pi/(p:ℝ)))
  change idealTriangleLeftConjugation
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(p:ℝ)))*modularInversionSL))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-2*Real.cos (Real.pi/(p:ℝ)))*modularInversionSL)
  rw [map_mul,map_mul,map_mul]
  change idealTriangleLeftConjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos (Real.pi/(p:ℝ)))))*
    idealTriangleLeftConjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL)=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-2*Real.cos (Real.pi/(p:ℝ))))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL
  rw [hT,idealTriangleLeftConjugation_inversion]

theorem oneIdealIntegerAngles_sum (p q : ℕ) (hp : 3≤p) (hq : 3≤q) :
    Real.pi/(p:ℝ)+Real.pi/(q:ℝ)<Real.pi := by
  have hpR : (3:ℝ)≤(p:ℝ):=by exact_mod_cast hp
  have hqR : (3:ℝ)≤(q:ℝ):=by exact_mod_cast hq
  have hpPos : 0<(p:ℝ):=by positivity
  have hqPos : 0<(q:ℝ):=by positivity
  have ha : Real.pi/(p:ℝ)≤Real.pi/3:=(div_le_div_iff₀ hpPos (by norm_num)).mpr (by nlinarith [Real.pi_pos])
  have hb : Real.pi/(q:ℝ)≤Real.pi/3:=(div_le_div_iff₀ hqPos (by norm_num)).mpr (by nlinarith [Real.pi_pos])
  linarith [Real.pi_pos]

def oneIdealIntegralTriangle
    (p q : ℕ)
    (hp : 3≤p)
    (hq : 3≤q) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle:=
  prescribedIdealHTriangle (Real.pi/(p:ℝ)) (Real.pi/(q:ℝ))
    (by positivity) (by positivity) (oneIdealIntegerAngles_sum p q hp hq)

theorem oneIdealIntegralTriangle_right_product (p q : ℕ) (hp : 3≤p) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL (oneIdealIntegralTriangle p q hp hq).sideLineA
      (oneIdealIntegralTriangle p q hp hq).sideLineC=standardHeckeCornerSL q := by
  rw [oneIdealIntegralTriangle,prescribedIdealHTriangle_sideA,prescribedIdealHTriangle_circle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,standardHeckeCornerSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem oneIdealIntegralTriangle_left_product (p q : ℕ) (hp : 3≤p) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL (oneIdealIntegralTriangle p q hp hq).sideLineB
      (oneIdealIntegralTriangle p q hp hq).sideLineC=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-2*Real.cos (Real.pi/(p:ℝ)))*modularInversionSL := by
  rw [oneIdealIntegralTriangle,prescribedIdealHTriangle_sideB,prescribedIdealHTriangle_circle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,
      Matrix.mul_apply,Fin.sum_univ_two]

end LowDimensionalTopology.Geometry.Fuchsian
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  Set
  Topology
open scoped UpperHalfPlane Pointwise MatrixGroups

/-- The same original conformal triangle group may use the two actual products through its third side. -/
theorem triangleConformalGroup_eq_crossPairProducts
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    triangleConformalGroup T=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB*_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA*_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC}:Set (ℍ≃ᵢℍ)) := by
  rw [triangleConformalGroup_eq_pairProductGroup]
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB
  let c:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC
  let K:=Subgroup.closure ({b*c,a*c}:Set (ℍ≃ᵢℍ))
  have hb : b⁻¹=b:=halfPlaneLineReflectionIsometry_inv _
  have hc : c⁻¹=c:=halfPlaneLineReflectionIsometry_inv _
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro g (rfl|he)
    · have hbc : b*c∈K:=Subgroup.subset_closure (by simp)
      have hac : a*c∈K:=Subgroup.subset_closure (by simp)
      have hh:=K.mul_mem hac (K.inv_mem hbc)
      change a*b∈K
      have he : (a*c)*(b*c)⁻¹=a*b:=by
        calc (a*c)*(b*c)⁻¹=a*b⁻¹:=by group
             _=a*b:=by rw [hb]
      rwa [he] at hh
    · have hcb : c*b∈K:=by
        have hh:=K.inv_mem (Subgroup.subset_closure (show b*c∈({b*c,a*c}:Set (ℍ≃ᵢℍ)) by simp))
        simpa only [mul_inv_rev,hb,hc] using hh
      exact mem_singleton_iff.mp he ▸ hcb
  · apply (Subgroup.closure_le _).mpr
    rintro g (rfl|he)
    · exact trianglePairProductGroup_pair_mem T T.sideLineB T.sideLineC
        (by simp [triangleReflectionSides]) (by simp [triangleReflectionSides])
    · have hg:=trianglePairProductGroup_pair_mem T T.sideLineA T.sideLineC
        (by simp [triangleReflectionSides]) (by simp [triangleReflectionSides])
      exact mem_singleton_iff.mp he ▸ hg

theorem oneIdealIntegralTriangle_conformal_eq (p q : ℕ) (hp : 3≤p) (hq : 3≤q) :
    triangleConformalGroup (oneIdealIntegralTriangle p q hp hq)=idealTriangleCyclicSup p q := by
  rw [triangleConformalGroup_eq_crossPairProducts,reflectionProductSL_native,
    reflectionProductSL_native,oneIdealIntegralTriangle_left_product,
    oneIdealIntegralTriangle_right_product,←idealTriangleLeftConjugation_corner]
  change Subgroup.closure _=(Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL p))).map
    idealTriangleLeftConjugation⊔Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q))
  rw [MonoidHom.map_zpowers]
  rw [←Set.singleton_union,Subgroup.closure_union,←Subgroup.zpowers_eq_closure,←Subgroup.zpowers_eq_closure]

/-- The original one-ideal triangle with two reciprocal finite angles has a genuinely discrete conformal group. -/
theorem oneIdealIntegralTriangle_conformal_discrete (p q : ℕ) (hp : 3≤p) (hq : 3≤q) :
    DiscreteTopology (triangleConformalGroup (oneIdealIntegralTriangle p q hp hq)) := by
  rw [oneIdealIntegralTriangle_conformal_eq]
  exact idealTriangleCyclicSup_discrete p q hp hq

/-- Its full original three-mirror group is discrete in the actual native boundary topology. -/
theorem oneIdealIntegralTriangle_reflection_discrete (p q : ℕ) (hp : 3≤p) (hq : 3≤q) :
    DiscreteTopology (triangleReflectionGroup (oneIdealIntegralTriangle p q hp hq)) :=
  (triangle_discrete_full_iff_conformal _).mpr (oneIdealIntegralTriangle_conformal_discrete p q hp hq)

end LowDimensionalTopology.Geometry.Fuchsian
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set
  Topology
open scoped UpperHalfPlane Pointwise MatrixGroups

/-- Genuine equal-angle conjugacy transports discreteness to every original one-ideal triangle. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_one_ideal_integral
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p q : ℕ) (hp : 3≤p) (hq : 3≤q)
    (ha : T.alpha=Real.pi/(p:ℝ)) (hb : T.beta=Real.pi/(q:ℝ)) (hc : T.gamma=0) :
    DiscreteTopology (triangleConformalGroup T) := by
  let U:=oneIdealIntegralTriangle p q hp hq
  have hU : U.alpha=Real.pi/(p:ℝ) ∧ U.beta=Real.pi/(q:ℝ) ∧ U.gamma=0:=
    prescribedIdealHTriangle_angles _ _ _ _ _
  obtain ⟨e,he⟩:=equal_angle_triangle_conformalGroups_conjugate T U
    (ha.trans hU.1.symm) (hb.trans hU.2.1.symm) (hc.trans hU.2.2.symm)
  let : DiscreteTopology (triangleConformalGroup U):=oneIdealIntegralTriangle_conformal_discrete p q hp hq
  have hd : DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e⁻¹ (triangleConformalGroup U)):=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete e⁻¹ (triangleConformalGroup U)
  rw [←he,native_subgroupConjugate_compose,inv_mul_cancel,native_subgroupConjugate_one] at hd
  exact hd

/-- The complete actual original mirror group has the same genuine discreteness. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_one_ideal_integral
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p q : ℕ) (hp : 3≤p) (hq : 3≤q)
    (ha : T.alpha=Real.pi/(p:ℝ)) (hb : T.beta=Real.pi/(q:ℝ)) (hc : T.gamma=0) :
    DiscreteTopology (triangleReflectionGroup T) :=
  (triangle_discrete_full_iff_conformal T).mpr
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_one_ideal_integral T p q hp hq ha hb hc)

end LowDimensionalTopology.Geometry.Fuchsian
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  Set
  Topology
open scoped UpperHalfPlane

/-- The right-angle one-ideal case is the genuine Hecke triangle, without a model hypothesis. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_one_ideal_right
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (q : ℕ) (hq : 3≤q) (ha : T.alpha=Real.pi/2)
    (hb : T.beta=Real.pi/(q:ℝ)) (hc : T.gamma=0) :
    DiscreteTopology (triangleConformalGroup T) := by
  have hG : IsHeckeGroup (triangleConformalGroup T):=by
    apply (isHeckeGroup_iff _).mpr
    refine ⟨(q:ℕ∞),by exact_mod_cast hq,T,ha,?_,hc,rfl⟩
    rw [triangleOrderAngle_nat]
    exact hb
  exact hG.discrete

/-- Every original one-ideal reciprocal-angle triangle has a discrete conformal group,
including either possible right-angle location. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_one_ideal_integral_all
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p q : ℕ) (hp : 2≤p) (hq : 2≤q)
    (ha : T.alpha=Real.pi/(p:ℝ)) (hb : T.beta=Real.pi/(q:ℝ)) (hc : T.gamma=0) :
    DiscreteTopology (triangleConformalGroup T) := by
  have hnot : ¬(p=2 ∧ q=2):=by
    rintro ⟨rfl,rfl⟩
    have hs:=T.angle_sum_lt_pi
    rw [ha,hb,hc] at hs
    norm_num at hs
  by_cases hp2 : p=2
  · subst p
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_one_ideal_right T q (by omega) (by simpa using ha) hb hc
  · by_cases hq2 : q=2
    · subst q
      let U:=swapClosedTriangle T
      have hu:=swapClosedTriangle_angles T
      have hd:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_one_ideal_right U p (by omega)
        (hu.1.trans (by simpa using hb)) (hu.2.1.trans ha) (hu.2.2.trans hc)
      have he : triangleConformalGroup U=triangleConformalGroup T:=by
        change triangleReflectionGroup (swapClosedTriangle T)⊓_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup=_
        rw [triangleReflectionGroup_swap]
        rfl
      rwa [he] at hd
    · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_one_ideal_integral T p q (by omega) (by omega) ha hb hc

/-- The full original three-reflection group has the same discreteness, with no orientation hypothesis. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.reflection_discrete_of_one_ideal_integral_all
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p q : ℕ) (hp : 2≤p) (hq : 2≤q)
    (ha : T.alpha=Real.pi/(p:ℝ)) (hb : T.beta=Real.pi/(q:ℝ)) (hc : T.gamma=0) :
    DiscreteTopology (triangleReflectionGroup T) :=
  (triangle_discrete_full_iff_conformal T).mpr
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_one_ideal_integral_all T p q hp hq ha hb hc)

end LowDimensionalTopology.Geometry.Fuchsian
