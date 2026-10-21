/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeneralizedReflectionGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GeneralizedDirichletPolygons
@[expose] public section
open Set
open scoped Topology OnePoint Pointwise UpperHalfPlane MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- The genuine affine sphere map normalizing a positive-radius circle to the unit circle. -/
def circleNormalizingMobius (c : ℂ) (r : ℝ) (hr :
  0<r) : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup:=
  _root_.LowDimensionalTopology.Geometry.Mobius.affineMobius ((r : ℂ)⁻¹) (-c/(r : ℂ)) (inv_ne_zero
    (Complex.ofReal_ne_zero.mpr hr.ne'))

theorem circleNormalizingMobius_coe (c z : ℂ) (r : ℝ) (hr : 0<r) :
    (circleNormalizingMobius c r hr).val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(((z-c)/(r : ℂ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
  rw [circleNormalizingMobius,_root_.LowDimensionalTopology.Geometry.Mobius.affineMobius_coe]
  change (((r : ℂ)⁻¹*z+ -c/(r : ℂ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=_
  congr 1
  ring

theorem circleNormalizingMobius_infty (c : ℂ) (r : ℝ) (hr : 0<r) :
    (circleNormalizingMobius c r hr).val ∞=∞:=by
  rw [circleNormalizingMobius,_root_.LowDimensionalTopology.Geometry.Mobius.affineMobius_coe]
  exact _root_.LowDimensionalTopology.Geometry.Mobius.affineHomeomorph_infty _ _ _

theorem circleNormalizingMobius_preimage_circle (c : ℂ) (r : ℝ) (hr : 0<r) :
    (circleNormalizingMobius c r hr).val ⁻¹' _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle 0 1=_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle c r:=by
  ext ξ
  induction ξ using OnePoint.rec with
  | infty => simp [circleNormalizingMobius_infty]
  | coe z =>
    simp only [mem_preimage,circleNormalizingMobius_coe,_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe,sub_zero,norm_div,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact div_eq_one_iff_eq hr.ne'

theorem circleNormalizingMobius_image_circle (c : ℂ) (r : ℝ) (hr : 0<r) :
    (circleNormalizingMobius c r hr).val '' _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle c r=_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle 0 1:=by
  rw [←circleNormalizingMobius_preimage_circle c r hr]
  exact (circleNormalizingMobius c r hr).val.image_preimage _

/-- The exterior component at infinity is the actual spherical component of the circle complement. -/
theorem circle_complement_component_infty_image (c : ℂ) (r : ℝ) (hr : 0<r) :
    (circleNormalizingMobius c r
      hr).val '' connectedComponentIn (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle c r)ᶜ ∞=
      _root_.LowDimensionalTopology.Geometry.Mobius.extendedUnitDiscExterior:=by
  have he:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph (circleNormalizingMobius c r
    hr)).image_connectedComponentIn
    (show (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈(_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle c r)ᶜ from _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_infty c r)
  change (circleNormalizingMobius c r
    hr).val '' connectedComponentIn (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle c r)ᶜ ∞=
    connectedComponentIn ((circleNormalizingMobius c r hr).val ''
      (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle c r)ᶜ)
      ((circleNormalizingMobius c r hr).val ∞) at he
  rw [(circleNormalizingMobius c r hr).val.image_compl,circleNormalizingMobius_image_circle,
    circleNormalizingMobius_infty,_root_.LowDimensionalTopology.Geometry.Mobius.connectedComponentIn_unitCircle_compl_of_mem_exterior
      _root_.LowDimensionalTopology.Geometry.Mobius.infty_mem_extendedUnitDiscExterior] at he
  exact he

/-- Its finite points are precisely the strict Euclidean exterior, under the actual sphere topology. -/
theorem mem_circle_complement_component_infty (c z : ℂ) (r : ℝ) (hr : 0<r) :
    (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈connectedComponentIn (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle c r)ᶜ ∞ ↔ r<‖z-c‖:=by
  have he:=circle_complement_component_infty_image c r hr
  have hm : (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈connectedComponentIn (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle c r)ᶜ ∞ ↔
      (circleNormalizingMobius c r hr).val z∈_root_.LowDimensionalTopology.Geometry.Mobius.extendedUnitDiscExterior:=by
    rw [←he]
    constructor
    · exact fun hz=>⟨z,hz,rfl⟩
    · rintro ⟨w,hw,he⟩
      exact (circleNormalizingMobius c r hr).val.injective he ▸ hw
  rw [hm,circleNormalizingMobius_coe,_root_.LowDimensionalTopology.Geometry.Mobius.coe_mem_extendedUnitDiscExterior,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,lt_div_iff₀ hr]
  simp only [one_mul]

/-- The literal normalized half-plane at infinity is exactly the strict classical circle exterior. -/
theorem normalizedDirichletHalfPlane_infty_formula
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (hD :
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (g : H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=g.val)
    (hc : A 1 0≠0) (hmoved : g.val.val ∞≠∞) (z : ℍ) :
    ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈normalizedDirichletHalfPlane D.carrier D.isDisc g.val (D.image_eq g) ∞ hmoved ↔
      1<‖realSLDenominator A z‖:=by
  have hb : _root_.LowDimensionalTopology.Geometry.Mobius.geometricModelBoundary D.carrier D.isDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryCircle:=by
    apply Subtype.ext
    change frontier D.carrier=_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis
    rw [hD,nielsen_openHalfPlane_frontier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary_eq_realAxis]
  have hspec : _root_.LowDimensionalTopology.Geometry.Mobius.IsGeometricNormalizedReflectionFactor (_root_.LowDimensionalTopology.Geometry.Mobius.geometricModelBoundary D.carrier D.isDisc)
      g.val ∞ (fordCircleMirror A hc).extendedCircle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.fordVerticalMirror A hc).extendedCircle:=by
    rw [hb,←hA]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.isHNormalizedReflectionFactor_iff_geometric A ∞ _
      _).mp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_ford_normalized_factor A hc)
  have he:=_root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors_eq_of_spec D.carrier D.isDisc g.val (D.image_eq g) ∞ hmoved
    (fordCircleMirror A hc).extendedCircle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.fordVerticalMirror A
      hc).extendedCircle hspec
  unfold normalizedDirichletHalfPlane
  rw [←he]
  change (((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈D.carrier ∧
    ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈connectedComponentIn (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle ((-A 1 1/A 1 0 : ℝ) : ℂ)
      (1/|A 1 0|))ᶜ ∞) ↔ 1<‖realSLDenominator A z‖
  rw [hD]
  have hz : ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_mem z
  simp only [hz,true_and]
  rw [mem_circle_complement_component_infty _ _ _ (div_pos zero_lt_one (abs_pos.mpr hc))]
  exact (Set.ext_iff.mp (realSLDenominator_strict_circle A hc) z).symm

/-- The original normalized-reflection polygon at infinity is literally the strict common circle exterior. -/
theorem generalizedDirichletPolygon_infty_eq_strictFordRegion
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (hD :
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hfree : ∀g : H,g • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞→g=1) :
    {z : ℍ | ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈generalizedDirichletPolygon D ∞ hfree}=strictFordRegion H:=by
  ext z
  constructor
  · intro hz A hA hc
    let g : H:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hA⟩
    have hg : g≠1:=by
      intro he
      have hfix : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞=∞:=by
        have hproj:=congrArg Subtype.val he
        change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=1 at hproj
        rw [hproj]
        rfl
      exact hc ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mp hfix)
    exact (normalizedDirichletHalfPlane_infty_formula D hD g A rfl hc
      (freeMobiusCenter_moved ∞ hfree g hg) z).mp (hz.2 g hg)
  · intro hz
    have hzD : ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈D.carrier:=by rw [hD];exact _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_mem z
    refine ⟨hzD,?_⟩
    intro g hg
    have hpres : g.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by rw [←hD];exact D.image_eq g
    obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL g.val hpres
    have hc : A 1 0≠0:=by
      intro hc
      apply hg
      apply hfree g
      change g.val.val ∞=∞
      rw [←hA]
      exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mpr hc
    exact (normalizedDirichletHalfPlane_infty_formula D hD g A hA hc
      (freeMobiusCenter_moved ∞ hfree g hg) z).mpr (hz A (hA ▸ g.property) hc)

/-- The original infinity-centered generalized polygon has the genuine fundamental-domain conclusion. -/
theorem generalizedDirichletPolygon_halfPlane_infty_fundamental
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (hD :
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (hinf : (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H)
    (hfree : ∀g : H,g • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞→g=1) :
    letI :=(_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc D hD).nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ MeasureTheory.volume
      {z : ℍ | ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈generalizedDirichletPolygon D ∞ hfree}:=by
  rw [generalizedDirichletPolygon_infty_eq_strictFordRegion D hD hfree]
  exact strictFordRegion_isFundamentalDomain_of_infty_ordinary_free (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc D hD) hinf hfree

/-- The containing-component cut at infinity is an actual native hyperbolic half-plane component. -/
theorem normalizedDirichletHalfPlane_infty_isHalfPlane
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (hD :
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (g : H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=g.val)
    (hc : A 1 0≠0) (hmoved : g.val.val ∞≠∞) :
    ∃p : ℍ,p∉(fordCircleMirror A hc).carrier ∧
      {z : ℍ | ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈normalizedDirichletHalfPlane
        D.carrier D.isDisc g.val (D.image_eq g) ∞ hmoved}=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane (fordCircleMirror A hc) p:=by
  let c:=-A 1 1/A 1 0
  let r:=1/|A 1 0|
  have hr : 0<r:=div_pos zero_lt_one (abs_pos.mpr hc)
  let p:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe c (r+1) (by linarith)
  have hp : r<‖(p : ℂ)-(c : ℂ)‖:=by
    have he : (p : ℂ)-(c : ℂ)=((r+1 : ℝ) : ℂ)*Complex.I:=by
      apply Complex.ext <;> simp [p,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
    rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
    linarith
  refine ⟨p,ne_of_gt hp,?_⟩
  change _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane (.circle c r hr) p
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane_circle_outside c r hr p hp]
  ext z
  change (((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈normalizedDirichletHalfPlane
    D.carrier D.isDisc g.val (D.image_eq g) ∞ hmoved) ↔ r<‖(z : ℂ)-(c : ℂ)‖
  rw [normalizedDirichletHalfPlane_infty_formula D hD g A hA hc hmoved z]
  exact Set.ext_iff.mp (realSLDenominator_strict_circle A hc) z

end
end LowDimensionalTopology.Geometry.Fuchsian
