/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianSimplicity
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicAxes
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.Geodesic
@[expose] public section
noncomputable section
open Set
open scoped OnePoint UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Agreement on the actual open half-plane determines the entire genuine sphere map. -/
theorem mobius_ext_on_halfPlane (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (h : ∀ z : ℍ, f.val (z:ℂ)=g.val (z:ℂ)) : f=g := by
  let a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 1 (by norm_num)
  let b := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 1 1 (by norm_num)
  let c := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 2 1 (by norm_num)
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.TripleDistinct ((a:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ((b:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ((c:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    constructor
    · intro he
      have hr := congrArg (fun z : ℂ => z.re) (OnePoint.coe_eq_coe.mp he)
      norm_num [a,b,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hr
    · constructor
      · intro he
        have hr := congrArg (fun z : ℂ => z.re) (OnePoint.coe_eq_coe.mp he)
        norm_num [a,c,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hr
      · intro he
        have hr := congrArg (fun z : ℂ => z.re) (OnePoint.coe_eq_coe.mp he)
        norm_num [b,c,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hr
  exact _root_.LowDimensionalTopology.Geometry.Mobius.mobius_eq_of_agree_triple f g _ _ _ hd (h a) (h b) (h c)

/-- The positive diagonal SL matrix lifts the entire genuine real dilation. -/
theorem realSLMobius_verticalDilation (k : ℝ) (hk : 0<k) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk)=
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.mk0 (k:ℂ) (Complex.ofReal_ne_zero.mpr hk.ne')) := by
  apply mobius_ext_on_halfPlane
  intro z
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe]
  rfl

/-- A real determinant-one matrix preserves the entire actual open half-plane. -/
theorem realSLMobius_image_openHalfPlane (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  apply le_antisymm
  · rintro p ⟨_,⟨z,hz,rfl⟩,rfl⟩
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A (⟨z,hz⟩:ℍ)]
    exact ⟨(A•(⟨z,hz⟩:ℍ):ℍ), (A•(⟨z,hz⟩:ℍ):ℍ).im_pos,rfl⟩
  · rintro p ⟨z,hz,rfl⟩
    let w : ℍ := A⁻¹•(⟨z,hz⟩:ℍ)
    refine ⟨(w:ℂ),⟨(w:ℂ),w.im_pos,rfl⟩,?_⟩
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action]
    change (((A•(A⁻¹•(⟨z,hz⟩:ℍ)):ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [smul_inv_smul]

/-- The actual Cayley sphere map sends the entire open half-plane to the entire unit disc. -/
theorem cayleyMobius_image_openHalfPlane :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_image_openHalfPlane]
  change ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' Metric.ball (0:ℂ) 1=
    ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z : ℂ | ‖z‖<1}
  congr 1
  ext z
  simp only [Metric.mem_ball,dist_zero_right,mem_ofPred_eq]

/-- Every genuine geometric disc admits an actual whole-domain half-plane normalizer. -/
theorem IsComplexOpenDisc.halfPlane_normalizer {D : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D) : ∃ q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, q.val '' D=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  obtain ⟨u,hu⟩ := hD.normalize
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*u,?_⟩
  change ((fun z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex =>
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹•(u•z)) ''
    D)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
  rw [←image_image]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val '' (u.val ''
    D)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
  rw [hu,←cayleyMobius_image_openHalfPlane,image_image]
  change (fun z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex => _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius•z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
  simp only [inv_smul_smul,image_id']

/-- A complex scaling preserving the whole half-plane has a strictly positive real coefficient. -/
theorem scaling_preserves_halfPlane_positive (a : ℂˣ)
    (hH : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    ∃ k : ℝ, ∃ hk : 0<k, a=Units.mk0 (k:ℂ) (Complex.ofReal_ne_zero.mpr hk.ne') := by
  have hb := _root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_mobius_boundary_preserved (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a) hH
  have h1 : (((1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary 1).mpr (by simp)
  have haB : (((a:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary := by
    have h := hb ▸ Set.mem_image_of_mem (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a).val h1
    simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,mul_one] using h
  have hai : (a:ℂ).im=0 := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary _).mp haB
  have hI : (((Complex.I:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet :=
    ⟨Complex.I,by simp,rfl⟩
  have haI : ((((a:ℂ)*Complex.I):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    have h := hH ▸ Set.mem_image_of_mem (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a).val hI
    simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe] using h
  have har : 0<(a:ℂ).re := by
    have h := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_openHalfPlaneSet _).mp haI
    simpa only [Complex.mul_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero] using h
  refine ⟨(a:ℂ).re,har,?_⟩
  apply Units.ext
  exact Complex.ext rfl hai

/-- Preservation of the actual half-plane constructs a genuine real determinant-one lift. -/
theorem mobius_preserves_halfPlane_exists_SL (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=f := by
  have hb := _root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_mobius_boundary_preserved f hH
  have h0 : f.val (0:ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary :=
    hb ▸ Set.mem_image_of_mem f.val ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary 0).mpr (by simp))
  have hinf : f.val ∞ ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary := hb ▸ Set.mem_image_of_mem f.val (by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary])
  obtain ⟨q,hq0,hqinf⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_boundary_pair_normalizer (f.val
    (0:ℂ)) (f.val ∞)
    h0 hinf (fun he => OnePoint.coe_ne_infty (0:ℂ) (f.val.injective he))
  let g := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*f
  have hg0 : g.val (0:ℂ)=(0:ℂ) := hq0
  have hginf : g.val ∞=∞ := hqinf
  obtain ⟨a,ha⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_fix_zero_infty_eq_scaling g hg0 hginf
  have hgH : g.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    calc
      g.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q).val '' (f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) := by
        rw [image_image]
        rfl
      _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by rw [hH,realSLMobius_image_openHalfPlane]
  obtain ⟨k,hk,rfl⟩ := scaling_preserves_halfPlane_positive a (ha ▸ hgH)
  have hproj : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*f=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk) :=
    ha.trans (realSLMobius_verticalDilation k hk).symm
  refine ⟨q⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk,?_⟩
  rw [map_mul,map_inv,←hproj]
  group


/-- The whole original Fuchsian group and the entire invariant disc are normalized together. -/
theorem FuchsianDisc.halfPlane_normalizer_exists {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : ∃ q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,
      q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H,
        ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=f := by
  obtain ⟨q,hq⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.IsComplexOpenDisc.halfPlane_normalizer D.isDisc
  refine ⟨q,hq,?_⟩
  intro f hf
  obtain ⟨g,hg,rfl⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
    H f).mp hf
  apply mobius_preserves_halfPlane_exists_SL
  rw [←hq,_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image,D.image_eq ⟨g,hg⟩,hq]

/-- A fixed genuine geometric normalizer, chosen from the proved whole-group construction. -/
def FuchsianDisc.halfPlaneNormalizer {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D
  : FuchsianDisc H) :
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := Classical.choose D.halfPlane_normalizer_exists

theorem FuchsianDisc.halfPlaneNormalizer_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc
      H) : D.halfPlaneNormalizer.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet :=
  (Classical.choose_spec D.halfPlane_normalizer_exists).1

/-- The actual conjugate subgroup is the image of the entire original group. -/
def FuchsianDisc.normalizedGroup {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) :
    Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate D.halfPlaneNormalizer H

theorem FuchsianDisc.normalizedGroup_exists_realSL {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f ∈
      D.normalizedGroup) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=f :=
  (Classical.choose_spec D.halfPlane_normalizer_exists).2 f hf

/-- The full real determinant-one preimage includes both signs of each genuine lift. -/
def FuchsianDisc.normalizedRealGroup {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D
  : FuchsianDisc H) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2)
      ℝ) := D.normalizedGroup.comap _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius

/-- Every original actual normalized Mobius transformation has an actual real matrix lift. -/
theorem FuchsianDisc.normalizedRealGroup_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : D.normalizedRealGroup.map _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius=D.normalizedGroup := by
  apply le_antisymm
  · exact Subgroup.map_comap_le _ _
  · intro f hf
    obtain ⟨A,hA⟩ := D.normalizedGroup_exists_realSL f hf
    exact Subgroup.mem_map.mpr ⟨A,by change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ D.normalizedGroup; rwa [hA],hA⟩

/-- Actual normalized maps preserve the whole physical domain. -/
theorem FuchsianDisc.normalizedGroup_preserves_halfPlane {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f ∈
      D.normalizedGroup) :
    f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  obtain ⟨A,rfl⟩ := D.normalizedGroup_exists_realSL f hf
  exact realSLMobius_image_openHalfPlane A

/-- The actual conjugate subgroup retains its inherited discrete topology. -/
theorem FuchsianDisc.normalizedGroup_discrete {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup D.normalizedGroup := by
  let : DiscreteTopology H := D.discrete
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete D.halfPlaneNormalizer H

end LowDimensionalTopology.Geometry.Fuchsian
