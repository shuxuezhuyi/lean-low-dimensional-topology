/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Reflection.FordNormalizedReflections
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordFundamentalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenConvexity
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.IsometricCircle.GeneralizedIsometricCircles
@[expose] public section
open Set
open scoped Topology OnePoint Pointwise UpperHalfPlane MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- The unique genuine real reflection with the prescribed complete complex circle as mirror. -/
def geometricCircleReflection (S : ComplexGeneralizedCircle) : Inversive.ExtendedHomeomorph 2:=
  Classical.choose S.property.exists_reflection

theorem geometricCircleReflection_isReflection (S : ComplexGeneralizedCircle) :
    Inversive.IsReflection (geometricCircleReflection S):=(Classical.choose_spec S.property.exists_reflection).1

theorem geometricCircleReflection_fixedPoints (S : ComplexGeneralizedCircle) :
    Function.fixedPoints (euclideanToComplexHom (geometricCircleReflection S))=S.val:=
  (Classical.choose_spec S.property.exists_reflection).2

theorem geometricCircleReflection_unique (S : ComplexGeneralizedCircle) (r : Inversive.ExtendedHomeomorph 2)
    (hr : Inversive.IsReflection r) (hfix : Function.fixedPoints (euclideanToComplexHom r)=S.val) :
    r=geometricCircleReflection S := by
  apply hr.eq_of_fixedPoints (geometricCircleReflection_isReflection S)
  apply extendedComplexEuclideanHomeomorph.surjective.preimage_injective
  rw [←complexReflection_fixedPoints,←complexReflection_fixedPoints,hfix,geometricCircleReflection_fixedPoints]

/-- The canonical circle reflection acts on the entire extended complex sphere. -/
def circleReflectionAction (S : ComplexGeneralizedCircle) : Equiv.Perm ExtendedComplex:=
  euclideanToComplexHom (geometricCircleReflection S)

theorem circleReflectionAction_fixedPoints (S : ComplexGeneralizedCircle) :
    Function.fixedPoints (circleReflectionAction S)=S.val:=geometricCircleReflection_fixedPoints S

theorem circleReflectionAction_native (L : Hyperbolic.HalfPlaneLine) :
    circleReflectionAction L.extendedCircle=euclideanToComplexHom L.realReflection:=by
  exact (congrArg euclideanToComplexHom
    (geometricCircleReflection_unique L.extendedCircle L.realReflection L.realReflection_isReflection
      L.realReflection_fixedPoints)).symm

/-- The actual generating reflection conjugates with its actual complete geometric mirror. -/
theorem circleReflectionAction_image (S : ComplexGeneralizedCircle) (q : complexMobiusGroup) :
    circleReflectionAction (S.image q)=q.val*circleReflectionAction S*q.val⁻¹:=by
  obtain ⟨u,hu,he⟩:=q.property.1
  let r:=u*geometricCircleReflection S*u⁻¹
  have hr : Inversive.IsReflection r:=Inversive.generalMobius_conjugate_isReflection hu
    (geometricCircleReflection_isReflection S)
  have hhom : euclideanToComplexHom r=q.val*circleReflectionAction S*q.val⁻¹:=by
    dsimp only [r,circleReflectionAction]
    rw [map_mul,map_mul,map_inv,he]
  have hfix : Function.fixedPoints (euclideanToComplexHom r)=(S.image q).val:=by
    rw [hhom]
    ext ξ
    change q.val (circleReflectionAction S (q.val.symm ξ))=ξ ↔ ξ∈q.val '' S.val
    constructor
    · intro hξ
      refine ⟨q.val.symm ξ,?_,q.val.apply_symm_apply ξ⟩
      rw [←circleReflectionAction_fixedPoints S]
      exact q.val.injective (hξ.trans (q.val.apply_symm_apply ξ).symm)
    · rintro ⟨η,hη,rfl⟩
      rw [q.val.symm_apply_apply]
      rw [←circleReflectionAction_fixedPoints S] at hη
      exact congrArg q.val hη
  rw [circleReflectionAction,←geometricCircleReflection_unique (S.image q) r hr hfix]
  exact hhom

/-- The source factorization uses genuine complete geometric mirrors perpendicular to the actual model boundary. -/
def IsGeometricNormalizedReflectionFactor (B : ComplexGeneralizedCircle)
    (g : complexMobiusGroup) (ξ : ExtendedComplex) (S T : ComplexGeneralizedCircle) : Prop:=
  ComplexCirclesOrthogonal S B ∧ ComplexCirclesOrthogonal T B ∧
  g.val=circleReflectionAction T*circleReflectionAction S ∧ ξ∈T.val

/-- The complete geometric factorization conjugates by every actual complex Mobius map. -/
theorem IsGeometricNormalizedReflectionFactor.conjugation
    {B S T : ComplexGeneralizedCircle} {g : complexMobiusGroup} {ξ : ExtendedComplex}
    (h : IsGeometricNormalizedReflectionFactor B g ξ S T) (q : complexMobiusGroup) :
    IsGeometricNormalizedReflectionFactor (B.image q) (q*g*q⁻¹) (q.val ξ) (S.image q) (T.image q) := by
  refine ⟨h.1.image _ _ q,h.2.1.image _ _ q,?_,⟨ξ,h.2.2.2,rfl⟩⟩
  rw [circleReflectionAction_image,circleReflectionAction_image]
  change q.val*g.val*q.val⁻¹=_
  rw [h.2.2.1]
  group

/-- In H the intrinsic whole-sphere factorization is exactly the native normalized factorization. -/
theorem isHNormalizedReflectionFactor_iff_geometric
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ξ : ExtendedComplex) (L M : Hyperbolic.HalfPlaneLine) :
    Hyperbolic.IsHNormalizedReflectionFactor A ξ L M ↔
      IsGeometricNormalizedReflectionFactor Hyperbolic.halfPlaneBoundaryCircle (Hyperbolic.realSLMobius A) ξ
        L.extendedCircle M.extendedCircle := by
  constructor
  · intro h
    refine ⟨L.extendedCircle_orthogonal_boundary,M.extendedCircle_orthogonal_boundary,?_,h.2⟩
    rw [circleReflectionAction_native,circleReflectionAction_native]
    exact Hyperbolic.realSL_reflection_factor_global A L M h.1
  · intro h
    refine ⟨?_,h.2.2.2⟩
    funext z
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    have he:=congrArg (fun f : Equiv.Perm ExtendedComplex=>f ((z : ℂ) : ExtendedComplex)) h.2.2.1
    rw [circleReflectionAction_native,circleReflectionAction_native] at he
    change (Hyperbolic.realSLMobius A).val ((z : ℂ) : ExtendedComplex)=
      euclideanToComplexHom M.realReflection (euclideanToComplexHom L.realReflection ((z : ℂ) : ExtendedComplex)) at he
    rw [Hyperbolic.realSLMobius_action,L.realReflection_coe,M.realReflection_coe] at he
    exact he

/-- In the actual standard half-plane, the complete geometric normalized mirrors exist uniquely. -/
theorem existsUnique_geometricNormalizedReflectionFactor_halfPlane
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ξ : ExtendedComplex)
    (hmoved : (Hyperbolic.realSLMobius A).val ξ≠ξ) :
    ∃!ST : ComplexGeneralizedCircle×ComplexGeneralizedCircle,
      IsGeometricNormalizedReflectionFactor Hyperbolic.halfPlaneBoundaryCircle (Hyperbolic.realSLMobius A) ξ ST.1
        ST.2 := by
  obtain ⟨LM,hLM,_⟩:=Hyperbolic.existsUnique_hNormalizedReflectionFactor A ξ hmoved
  refine ⟨⟨LM.1.extendedCircle,LM.2.extendedCircle⟩,
    (isHNormalizedReflectionFactor_iff_geometric A ξ LM.1 LM.2).mp hLM,?_⟩
  intro ST hST
  obtain ⟨L,hL⟩:=Hyperbolic.exists_halfPlaneLine_of_orthogonal_boundary ST.1 hST.1
  obtain ⟨M,hM⟩:=Hyperbolic.exists_halfPlaneLine_of_orthogonal_boundary ST.2 hST.2.1
  have hnative : Hyperbolic.IsHNormalizedReflectionFactor A ξ L M:=by
    apply (isHNormalizedReflectionFactor_iff_geometric A ξ L M).mpr
    simpa only [hL,hM] using hST
  have he:=Hyperbolic.hNormalizedReflectionFactor_unique A ξ hmoved hnative hLM
  exact Prod.ext (hL.symm.trans (congrArg Hyperbolic.HalfPlaneLine.extendedCircle he.1))
    (hM.symm.trans (congrArg Hyperbolic.HalfPlaneLine.extendedCircle he.2))

/-- The boundary circle is the actual topological frontier of the geometric model. -/
def geometricModelBoundary (P : Set ExtendedComplex) (hP : IsComplexOpenDisc P) : ComplexGeneralizedCircle:=
  ⟨frontier P,complexDisc_frontier_isGeneralized hP⟩

theorem geometricModelBoundary_image (P : Set ExtendedComplex) (hP : IsComplexOpenDisc P)
    (q : complexMobiusGroup) :
    (geometricModelBoundary P hP).image q=
      geometricModelBoundary (q.val '' P) (hP.image q) := by
  apply Subtype.ext
  exact (mobiusBoundaryHomeomorph q).image_frontier P

theorem geometricModelBoundary_halfPlane (hP : IsComplexOpenDisc Hyperbolic.openHalfPlaneSet) :
    geometricModelBoundary Hyperbolic.openHalfPlaneSet hP=Hyperbolic.halfPlaneBoundaryCircle:=by
  apply Subtype.ext
  exact Fuchsian.nielsen_openHalfPlane_frontier.trans Hyperbolic.halfPlaneIdealBoundary_eq_realAxis

/-- The original normalized reflection pair exists uniquely in every actual geometric model. -/
theorem existsUnique_geometricNormalizedReflectionFactor
    (P : Set ExtendedComplex) (hP : IsComplexOpenDisc P)
    (g : complexMobiusGroup) (hpres : g.val '' P=P)
    (ξ : ExtendedComplex) (hmoved : g.val ξ≠ξ) :
    ∃!ST : ComplexGeneralizedCircle×ComplexGeneralizedCircle,
      IsGeometricNormalizedReflectionFactor (geometricModelBoundary P hP) g ξ ST.1 ST.2 := by
  obtain ⟨q,hq⟩:=Fuchsian.IsComplexOpenDisc.halfPlane_normalizer hP
  have hb : (geometricModelBoundary P hP).image q=Hyperbolic.halfPlaneBoundaryCircle:=by
    apply Subtype.ext
    change q.val '' frontier P=complexRealAxis
    calc
      q.val '' frontier P=frontier (q.val '' P):=(mobiusBoundaryHomeomorph q).image_frontier P
      _=complexRealAxis:=by
        rw [hq,Fuchsian.nielsen_openHalfPlane_frontier,Hyperbolic.halfPlaneIdealBoundary_eq_realAxis]
  have hnorm : (q*g*q⁻¹).val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet:=by
    rw [←hq,stableAxis_conjugate_image,hpres,hq]
  obtain ⟨A,hA⟩:=Fuchsian.mobius_preserves_halfPlane_exists_SL (q*g*q⁻¹) hnorm
  have hpoint : (q*g*q⁻¹).val (q.val ξ)=q.val (g.val ξ):=by
    change q.val (g.val (q.val.symm (q.val ξ)))=q.val (g.val ξ)
    rw [q.val.symm_apply_apply]
  have hmovedA : (Hyperbolic.realSLMobius A).val (q.val ξ)≠q.val ξ:=by
    intro he
    rw [hA,hpoint] at he
    exact hmoved (q.val.injective he)
  obtain ⟨ST,hST,hunique⟩:=existsUnique_geometricNormalizedReflectionFactor_halfPlane A (q.val ξ) hmovedA
  have hback:=hST.conjugation q⁻¹
  have hbback : Hyperbolic.halfPlaneBoundaryCircle.image q⁻¹=geometricModelBoundary P hP:=by
    rw [←hb,Hyperbolic.complexCircle_image_inverse]
  have hgback : q⁻¹*Hyperbolic.realSLMobius A*(q⁻¹)⁻¹=g:=by rw [hA];group
  have hξback : (q⁻¹).val (q.val ξ)=ξ:=q.val.symm_apply_apply ξ
  rw [hbback,hgback,hξback] at hback
  refine ⟨⟨ST.1.image q⁻¹,ST.2.image q⁻¹⟩,hback,?_⟩
  intro UV hUV
  have hforward:=hUV.conjugation q
  rw [hb,←hA] at hforward
  have he:=hunique ⟨UV.1.image q,UV.2.image q⟩ hforward
  apply Prod.ext
  · have h1:=congrArg (fun V : ComplexGeneralizedCircle=>V.image q⁻¹) (congrArg Prod.fst he)
    simpa only [Hyperbolic.complexCircle_image_inverse] using h1
  · have h2:=congrArg (fun V : ComplexGeneralizedCircle=>V.image q⁻¹) (congrArg Prod.snd he)
    simpa only [Hyperbolic.complexCircle_image_inverse] using h2

/-- The first true complete mirror avoids the original nonfixed center in every model. -/
theorem IsGeometricNormalizedReflectionFactor.first_mirror_avoids_center
    {B S T : ComplexGeneralizedCircle} {g : complexMobiusGroup} {ξ : ExtendedComplex}
    (h : IsGeometricNormalizedReflectionFactor B g ξ S T) (hmoved : g.val ξ≠ξ) : ξ∉S.val := by
  intro hξS
  have hS : circleReflectionAction S ξ=ξ:=by rwa [←circleReflectionAction_fixedPoints S] at hξS
  have hT : circleReflectionAction T ξ=ξ:=by
    have hξT:=h.2.2.2
    rwa [←circleReflectionAction_fixedPoints T] at hξT
  apply hmoved
  rw [h.2.2.1]
  change circleReflectionAction T (circleReflectionAction S ξ)=ξ
  rw [hS,hT]

/-- The unique source-normalized complete mirror pair, defined intrinsically in the original model. -/
def geometricNormalizedMirrors (P : Set ExtendedComplex) (hP : IsComplexOpenDisc P)
    (g : complexMobiusGroup) (hpres : g.val '' P=P)
    (ξ : ExtendedComplex) (hmoved : g.val ξ≠ξ) : ComplexGeneralizedCircle×ComplexGeneralizedCircle:=
  Classical.choose (existsUnique_geometricNormalizedReflectionFactor P hP g hpres ξ hmoved)

theorem geometricNormalizedMirrors_spec (P : Set ExtendedComplex) (hP : IsComplexOpenDisc P)
    (g : complexMobiusGroup) (hpres : g.val '' P=P)
    (ξ : ExtendedComplex) (hmoved : g.val ξ≠ξ) :
    IsGeometricNormalizedReflectionFactor (geometricModelBoundary P hP) g ξ
      (geometricNormalizedMirrors P hP g hpres ξ hmoved).1
      (geometricNormalizedMirrors P hP g hpres ξ hmoved).2:=
  (Classical.choose_spec (existsUnique_geometricNormalizedReflectionFactor P hP g hpres ξ hmoved)).1

/-- Any verified normalized pair is equal to the intrinsically chosen pair; no normalizer choice survives. -/
theorem geometricNormalizedMirrors_eq_of_spec
    (P : Set ExtendedComplex) (hP : IsComplexOpenDisc P)
    (g : complexMobiusGroup) (hpres : g.val '' P=P)
    (ξ : ExtendedComplex) (hmoved : g.val ξ≠ξ) (S T : ComplexGeneralizedCircle)
    (h : IsGeometricNormalizedReflectionFactor (geometricModelBoundary P hP) g ξ S T) :
    (S,T)=geometricNormalizedMirrors P hP g hpres ξ hmoved:=
  (Classical.choose_spec (existsUnique_geometricNormalizedReflectionFactor P hP g hpres ξ hmoved)).2 (S,T) h

theorem mobius_conjugate_preserves_model (P : Set ExtendedComplex) (g : complexMobiusGroup)
    (hpres : g.val '' P=P) (q : complexMobiusGroup) :
    (q*g*q⁻¹).val '' (q.val '' P)=q.val '' P:=by
  rw [stableAxis_conjugate_image,hpres]

theorem mobius_conjugate_moves_center (g q : complexMobiusGroup) (ξ : ExtendedComplex)
    (hmoved : g.val ξ≠ξ) : (q*g*q⁻¹).val (q.val ξ)≠q.val ξ:=by
  intro he
  apply hmoved
  apply q.val.injective
  change q.val (g.val ξ)=q.val ξ
  change q.val (g.val (q.val.symm (q.val ξ)))=q.val ξ at he
  rwa [q.val.symm_apply_apply] at he

/-- The intrinsic actual mirrors conjugate in every original geometric model, including ideal centers. -/
theorem geometricNormalizedMirrors_conjugation
    (P : Set ExtendedComplex) (hP : IsComplexOpenDisc P)
    (g : complexMobiusGroup) (hpres : g.val '' P=P)
    (ξ : ExtendedComplex) (hmoved : g.val ξ≠ξ) (q : complexMobiusGroup) :
    geometricNormalizedMirrors (q.val '' P) (hP.image q) (q*g*q⁻¹)
      (mobius_conjugate_preserves_model P g hpres q) (q.val ξ)
      (mobius_conjugate_moves_center g q ξ hmoved)=
      ((geometricNormalizedMirrors P hP g hpres ξ hmoved).1.image q,
       (geometricNormalizedMirrors P hP g hpres ξ hmoved).2.image q) := by
  symm
  apply geometricNormalizedMirrors_eq_of_spec
  have h:=(geometricNormalizedMirrors_spec P hP g hpres ξ hmoved).conjugation q
  rwa [geometricModelBoundary_image] at h

/-- The defining pair has a first mirror that avoids the moved normalization center. -/
theorem geometricNormalizedMirrors_first_avoids
    (P : Set ExtendedComplex) (hP : IsComplexOpenDisc P)
    (g : complexMobiusGroup) (hpres : g.val '' P=P)
    (ξ : ExtendedComplex) (hmoved : g.val ξ≠ξ) :
    ξ∉(geometricNormalizedMirrors P hP g hpres ξ hmoved).1.val:=
  (geometricNormalizedMirrors_spec P hP g hpres ξ hmoved).first_mirror_avoids_center hmoved

end
end LowDimensionalTopology.Geometry.Mobius
