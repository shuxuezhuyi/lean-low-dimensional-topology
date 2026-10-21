/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.GeneralizedModelSides
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

/-- Reflection in the actual real boundary is precisely the genuine sphere complex conjugation. -/
theorem circleReflectionAction_halfPlaneBoundary :
    _root_.LowDimensionalTopology.Geometry.Mobius.circleReflectionAction _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryCircle=_root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation:=by
  let a:=_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates Complex.I
  have ha : a≠0:=(_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates.map_ne_zero_iff).mpr Complex.I_ne_zero
  let r:=_root_.LowDimensionalTopology.Geometry.Inversive.planeReflectionHomeomorph a 0 ha
  have hr : _root_.LowDimensionalTopology.Geometry.Inversive.IsReflection r:=_root_.LowDimensionalTopology.Geometry.Inversive.planeReflection_isReflection a 0 ha
  have hfix : Function.fixedPoints (_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom r)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryCircle.val:=by
    have h:=_root_.LowDimensionalTopology.Geometry.Mobius.complexLine_reflection Complex.I 0 Complex.I_ne_zero
    rw [←_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis_eq_line] at h
    exact h
  have hcanon:=_root_.LowDimensionalTopology.Geometry.Mobius.geometricCircleReflection_unique _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryCircle r hr hfix
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.circleReflectionAction,←hcanon]
  apply Equiv.ext
  intro ξ
  induction ξ using OnePoint.rec with
  | infty =>
    change _root_.LowDimensionalTopology.Geometry.Mobius.extendedComplexEuclideanHomeomorph.symm (r ∞)=∞
    rw [show r ∞=∞ by rfl]
    rfl
  | coe z =>
    change _root_.LowDimensionalTopology.Geometry.Mobius.extendedComplexEuclideanHomeomorph.symm
      (r (_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates z :
        _root_.LowDimensionalTopology.Geometry.Inversive.ExtendedEuclidean 2))=((conj z : ℂ) :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [show r (_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates z :
      _root_.LowDimensionalTopology.Geometry.Inversive.ExtendedEuclidean 2)=
      (_root_.LowDimensionalTopology.Geometry.Inversive.planeReflectionFinite a 0 (_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates z) : _root_.LowDimensionalTopology.Geometry.Inversive.ExtendedEuclidean 2) by rfl]
    change ((_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates.symm
      (_root_.LowDimensionalTopology.Geometry.Inversive.planeReflectionFinite a 0
      (_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates z)) : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=_
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.ReflectionBridge.planeReflection_complex_formula Complex.I z 0
      Complex.I_ne_zero]
    simp [Complex.conj_I]

/-- The source's reflection in the actual boundary circle of the original model. -/
def modelBoundaryReflection (P : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hP :
  _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc
  P) : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
  _root_.LowDimensionalTopology.Geometry.Mobius.circleReflectionAction (_root_.LowDimensionalTopology.Geometry.Mobius.geometricModelBoundary P hP)

theorem geometricModelBoundary_normalization (P : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hP
  : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc P) :
    ∃q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,q.val '' P=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      (_root_.LowDimensionalTopology.Geometry.Mobius.geometricModelBoundary P hP).image q=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryCircle:=by
  obtain ⟨q,hq⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.IsComplexOpenDisc.halfPlane_normalizer hP
  refine ⟨q,hq,?_⟩
  apply Subtype.ext
  change q.val '' frontier P=_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis
  calc
    q.val '' frontier P=frontier (q.val '' P):=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
      q).image_frontier P
    _=_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis:=by rw [hq,nielsen_openHalfPlane_frontier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary_eq_realAxis]

/-- This is the actual reflected point in normalized coordinates, including poles and infinity. -/
theorem modelBoundaryReflection_coordinate (P : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hP :
  _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc P)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hb :
      (_root_.LowDimensionalTopology.Geometry.Mobius.geometricModelBoundary P hP).image
      q=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryCircle)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    q.val (modelBoundaryReflection P hP ξ)=_root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation (q.val ξ):=by
  have he:=_root_.LowDimensionalTopology.Geometry.Mobius.circleReflectionAction_image (_root_.LowDimensionalTopology.Geometry.Mobius.geometricModelBoundary P hP) q
  rw [hb,circleReflectionAction_halfPlaneBoundary] at he
  have h:=congrArg (fun f : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>f (q.val
    ξ)) he.symm
  change q.val (modelBoundaryReflection P hP (q.val.symm (q.val
    ξ)))=_root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation (q.val ξ) at h
  rwa [q.val.symm_apply_apply] at h

/-- Every original conformal isometry commutes with the genuine boundary reflection. -/
theorem modelBoundaryReflection_commutes (P : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hP :
  _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc P)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hpres : g.val '' P=P) (ξ :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    g.val (modelBoundaryReflection P hP ξ)=modelBoundaryReflection P hP (g.val ξ):=by
  obtain ⟨q,hq,hb⟩:=geometricModelBoundary_normalization P hP
  have hnorm : (q*g*q⁻¹).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    rw [←hq,_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image,hpres,hq]
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL (q*g*q⁻¹) hnorm
  have hg (η : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : q.val (g.val η)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (q.val η):=by
    rw [hA]
    change q.val (g.val η)=q.val (g.val (q.val.symm (q.val η)))
    rw [q.val.symm_apply_apply]
  apply q.val.injective
  rw [hg,modelBoundaryReflection_coordinate P hP q
    hb,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_complexConjugation,
    modelBoundaryReflection_coordinate P hP q hb,hg]

/-- A reflected original nonfixed center is still moved, without imposing any new condition. -/
theorem modelBoundaryReflection_moved (P : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hP :
  _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc P)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hpres : g.val '' P=P) (ξ :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hmoved : g.val ξ≠ξ) :
    g.val (modelBoundaryReflection P hP ξ)≠modelBoundaryReflection P hP ξ:=by
  intro he
  apply hmoved
  apply (modelBoundaryReflection P hP).injective
  rwa [modelBoundaryReflection_commutes P hP g hpres ξ] at he

/-- Orthogonality to the boundary makes complete mirror membership invariant under the genuine boundary reflection. -/
theorem orthogonalMirror_boundaryReflection_mem
    (P : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hP :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc P) (S :
      _root_.LowDimensionalTopology.Geometry.Mobius.ComplexGeneralizedCircle)
    (hS : _root_.LowDimensionalTopology.Geometry.Mobius.ComplexCirclesOrthogonal S
      (_root_.LowDimensionalTopology.Geometry.Mobius.geometricModelBoundary P hP)) (ξ :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    modelBoundaryReflection P hP ξ∈S.val ↔ ξ∈S.val:=by
  obtain ⟨q,hq,hb⟩:=geometricModelBoundary_normalization P hP
  have hSq:=hS.image _ _ q
  rw [hb] at hSq
  obtain ⟨L,hL⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_halfPlaneLine_of_orthogonal_boundary (S.image
    q) hSq
  have hmem (η : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : η∈S.val ↔ q.val η∈L.extendedCircle.val:=by
    rw [hL]
    constructor
    · exact fun hη=>⟨η,hη,rfl⟩
    · rintro ⟨ζ,hζ,he⟩
      exact q.val.injective he ▸ hζ
  calc
    modelBoundaryReflection P hP ξ∈S.val ↔ q.val (modelBoundaryReflection P hP ξ)∈L.extendedCircle.val:=hmem _
    _↔_root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation (q.val ξ)∈L.extendedCircle.val:=by rw [modelBoundaryReflection_coordinate P hP q hb]
    _↔q.val ξ∈L.extendedCircle.val:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.mem_extendedCircle_conjugation L _
    _↔ξ∈S.val:=(hmem ξ).symm

/-- The two actual normalized mirrors are unchanged when the center is reflected across the original model boundary. -/
theorem geometricNormalizedMirrors_boundaryReflection
    (P : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hP :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc P) (g :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hpres : g.val '' P=P)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hmoved : g.val ξ≠ξ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors P hP g hpres (modelBoundaryReflection P hP
      ξ)
      (modelBoundaryReflection_moved P hP g hpres ξ hmoved)=
      _root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors P hP g hpres ξ hmoved:=by
  symm
  apply _root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors_eq_of_spec
  have h:=_root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors_spec P hP g hpres ξ hmoved
  exact ⟨h.1,h.2.1,h.2.2.1,(orthogonalMirror_boundaryReflection_mem P hP _ h.2.1 ξ).mpr h.2.2.2⟩

/-- Native complete-mirror components do not distinguish a point from its reflection in the real boundary. -/
theorem halfPlaneLine_component_conjugation (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (ξ :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hξ : ξ∉L.extendedCircle.val) :
    connectedComponentIn L.extendedCircle.valᶜ (_root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation ξ)=connectedComponentIn L.extendedCircle.valᶜ ξ:=by
  have hmem : _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation ξ∈connectedComponentIn L.extendedCircle.valᶜ ξ:=by
    induction ξ using OnePoint.rec with
    | infty => exact mem_connectedComponentIn hξ
    | coe z =>
      cases L with
      | vertical x =>
        have hne : z.re≠x:=by
          intro he
          apply hξ
          change (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.Mobius.complexLine 1 x
          rw [_root_.LowDimensionalTopology.Geometry.Mobius.complexLine_coe]
          simpa only [Complex.inner,one_mul,Complex.conj_re] using he
        change ((conj z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈connectedComponentIn (_root_.LowDimensionalTopology.Geometry.Mobius.complexLine 1 x)ᶜ (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
        rcases lt_or_gt_of_ne hne with hi|ho
        · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalCircle_component_left x _
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.mirrorLeftSide_coe x z).mpr hi)]
          exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.mirrorLeftSide_coe x _).mpr hi
        · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalCircle_component_right x _
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.mirrorRightSide_coe x z).mpr ho)]
          exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.mirrorRightSide_coe x _).mpr ho
      | circle c r hr =>
        have hne : ‖z-(c : ℂ)‖≠r:=by
          intro he
          exact hξ ((_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe c z r).mpr he)
        have hn : ‖conj z-(c : ℂ)‖=‖z-(c : ℂ)‖:=by
          calc
            ‖conj z-(c : ℂ)‖=‖conj (z-(c : ℂ))‖:=by rw [map_sub,Complex.conj_ofReal]
            _=‖z-(c : ℂ)‖:=Complex.norm_conj _
        change ((conj z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈connectedComponentIn (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle (c : ℂ) r)ᶜ (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
        rcases lt_or_gt_of_ne hne with hi|ho
        · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.mem_circle_complement_component_inside _ _ _ _ hr
          hi).mpr (hn ▸ hi)
        · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circle_complement_component_outside_eq_infty _ _ _ hr
          ho]
          exact (mem_circle_complement_component_infty _ _ _ hr).mpr (hn ▸ ho)
  exact (connectedComponentIn_eq hmem).symm

/-- The genuine containing spherical side of any original orthogonal mirror is unchanged by boundary reflection of the center. -/
theorem geometricContainingSide_boundaryReflection
    (P : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hP :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc P) (S :
      _root_.LowDimensionalTopology.Geometry.Mobius.ComplexGeneralizedCircle)
    (hS : _root_.LowDimensionalTopology.Geometry.Mobius.ComplexCirclesOrthogonal S
      (_root_.LowDimensionalTopology.Geometry.Mobius.geometricModelBoundary P hP))
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hξ : ξ∉S.val) :
    geometricContainingSide S (modelBoundaryReflection P hP ξ)=geometricContainingSide S ξ:=by
  obtain ⟨q,hq,hb⟩:=geometricModelBoundary_normalization P hP
  have hSq:=hS.image _ _ q
  rw [hb] at hSq
  obtain ⟨L,hL⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_halfPlaneLine_of_orthogonal_boundary (S.image
    q) hSq
  have hξq : q.val ξ∉L.extendedCircle.val:=by
    intro he
    rw [hL] at he
    obtain ⟨η,hη,he⟩:=he
    exact hξ (q.val.injective he ▸ hη)
  have hτξ : modelBoundaryReflection P hP ξ∉S.val:=
    fun he=>hξ ((orthogonalMirror_boundaryReflection_mem P hP S hS ξ).mp he)
  apply q.val.injective.image_injective
  rw [geometricContainingSide_image S _ hτξ q,geometricContainingSide_image S ξ hξ q,←hL,
    modelBoundaryReflection_coordinate P hP q hb]
  exact halfPlaneLine_component_conjugation L (q.val ξ) hξq

/-- Every actual source half-plane is invariant when the original center is reflected across the original model boundary. -/
theorem normalizedDirichletHalfPlane_boundaryReflection
    (P : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hP :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc P) (g :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hpres : g.val '' P=P)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hmoved : g.val ξ≠ξ) :
    normalizedDirichletHalfPlane P hP g hpres (modelBoundaryReflection P hP ξ)
      (modelBoundaryReflection_moved P hP g hpres ξ hmoved)=
      normalizedDirichletHalfPlane P hP g hpres ξ hmoved:=by
  unfold normalizedDirichletHalfPlane
  rw [geometricNormalizedMirrors_boundaryReflection P hP g hpres ξ hmoved]
  rw [geometricContainingSide_boundaryReflection P hP _
    (_root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors_spec P hP g hpres ξ hmoved).1 ξ
    (_root_.LowDimensionalTopology.Geometry.Mobius.geometricNormalizedMirrors_first_avoids P hP g hpres ξ hmoved)]

/-- The reflected center satisfies precisely the same original trivial-stabilizer convention. -/
theorem boundaryReflected_free_center {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D
  : FuchsianDisc H)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfree : ∀g : H,g • ξ=ξ→g=1) :
    ∀g : H,g • modelBoundaryReflection D.carrier D.isDisc ξ=modelBoundaryReflection D.carrier D.isDisc ξ→g=1:=by
  intro g hg
  apply hfree g
  apply (modelBoundaryReflection D.carrier D.isDisc).injective
  change modelBoundaryReflection D.carrier D.isDisc (g.val.val ξ)=modelBoundaryReflection D.carrier D.isDisc ξ
  rw [←modelBoundaryReflection_commutes D.carrier D.isDisc g.val (D.image_eq g) ξ]
  exact hg

/-- (the center-reflection identity, distinct from ): actual original polygons are unchanged. -/
theorem generalizedDirichletPolygon_boundaryReflection
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfree : ∀g : H,g • ξ=ξ→g=1) :
    generalizedDirichletPolygon D (modelBoundaryReflection D.carrier D.isDisc ξ)
      (boundaryReflected_free_center D ξ hfree)=generalizedDirichletPolygon D ξ hfree:=by
  ext z
  constructor
  · intro hz
    refine ⟨hz.1,?_⟩
    intro g hg
    have hzg:=hz.2 g hg
    have he:=normalizedDirichletHalfPlane_boundaryReflection D.carrier D.isDisc g.val (D.image_eq g) ξ
      (freeMobiusCenter_moved ξ hfree g hg)
    rwa [he] at hzg
  · intro hz
    refine ⟨hz.1,?_⟩
    intro g hg
    have he:=normalizedDirichletHalfPlane_boundaryReflection D.carrier D.isDisc g.val (D.image_eq g) ξ
      (freeMobiusCenter_moved ξ hfree g hg)
    rw [he]
    exact hz.2 g hg

/-- The actual unit-boundary reflection exchanges infinity with the genuine disc origin. -/
theorem circleReflectionAction_discBoundary_infty :
    _root_.LowDimensionalTopology.Geometry.Mobius.circleReflectionAction _root_.LowDimensionalTopology.Geometry.Hyperbolic.discBoundaryCircle ∞=((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
  let r:=_root_.LowDimensionalTopology.Geometry.Inversive.sphereInversionHomeomorph (_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates (0 : ℂ)) 1 (by norm_num)
  have hr : _root_.LowDimensionalTopology.Geometry.Inversive.IsReflection r:=_root_.LowDimensionalTopology.Geometry.Inversive.sphereInversion_isReflection _ 1 (by norm_num)
  have hfix : Function.fixedPoints (_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom
    r)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discBoundaryCircle.val:=
    _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_reflection 0 1 zero_lt_one
  have hcanon:=_root_.LowDimensionalTopology.Geometry.Mobius.geometricCircleReflection_unique _root_.LowDimensionalTopology.Geometry.Hyperbolic.discBoundaryCircle r hr hfix
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.circleReflectionAction,←hcanon]
  change _root_.LowDimensionalTopology.Geometry.Mobius.extendedComplexEuclideanHomeomorph.symm (r ∞)=((0 : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  rw [show r ∞=(_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates (0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Inversive.ExtendedEuclidean 2) by rfl]
  change (((_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates.symm
    (_root_.LowDimensionalTopology.Geometry.Mobius.complexPlaneCoordinates (0 : ℂ)) : ℂ)) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=_
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem modelBoundaryReflection_unitDisc_infty {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hD : D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    modelBoundaryReflection D.carrier D.isDisc ∞=((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
  have hb : _root_.LowDimensionalTopology.Geometry.Mobius.geometricModelBoundary D.carrier D.isDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discBoundaryCircle:=by
    apply Subtype.ext
    change frontier D.carrier=_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle 0 1
    rw [hD,_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle]
  rw [modelBoundaryReflection,hb,circleReflectionAction_discBoundary_infty]

/-- The unit-disc origin is automatically a free center when infinity is an original free center. -/
theorem unitDisc_zero_free_of_infty {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hD : D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hfree : ∀g : H,g • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞→g=1) :
    ∀g : H,g • ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→g=1:=by
  have h:=boundaryReflected_free_center D ∞ hfree
  rwa [modelBoundaryReflection_unitDisc_infty D hD] at h

/-- Center equality transports the dependent trivial-stabilizer proof without changing the actual polygon. -/
theorem generalizedDirichletPolygon_center_congr
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (ξ η :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (he : ξ=η)
    (hfree : ∀g : H,g • ξ=ξ→g=1) (hfree' : ∀g : H,g • η=η→g=1) :
    generalizedDirichletPolygon D ξ hfree=generalizedDirichletPolygon D η hfree':=by
  subst η
  rfl

/-- The actual generalized disc polygons centered at infinity and at zero coincide. -/
theorem generalizedDirichletPolygon_unitDisc_infty_eq_zero
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (hD :
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hfree : ∀g : H,g • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞→g=1) :
    generalizedDirichletPolygon D ∞ hfree=generalizedDirichletPolygon D ((0 : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      (unitDisc_zero_free_of_infty D hD hfree):=by
  have h:=generalizedDirichletPolygon_boundaryReflection D ∞ hfree
  exact h.symm.trans (generalizedDirichletPolygon_center_congr D _ _
    (modelBoundaryReflection_unitDisc_infty D hD) _ _)

end
end LowDimensionalTopology.Geometry.Fuchsian
