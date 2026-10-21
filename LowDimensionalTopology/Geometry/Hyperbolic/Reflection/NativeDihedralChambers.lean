/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.Angle.PositiveCone
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.AngleNormalForms
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteDihedralConeGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeDihedralReflectionGroups
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology InnerProductGeometry
open scoped NNReal
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon Set Topology InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc NNReal
local instance triangleVertexChartDiscMetric : MetricSpace 𝔻:=discHyperbolicMetric

/-- The true Klein direction is a positive multiple of the actual normalized Cayley tip. -/
theorem triangleVertex_kleinDirection_unit (R : HRayAt UpperHalfPlane.I) :
    ∃c : ℝ,0<c ∧ R.kleinDirection=c • (triangleVertexUnitDirection R:ℂ) := by
  obtain ⟨r,hr,he⟩:=kleinCoordinate_positive_smul (halfPlaneToDisc R.directionPoint)
  have htip : ‖(halfPlaneToDisc R.directionPoint:ℂ)‖ • (triangleVertexUnitDirection R:ℂ)=
      (halfPlaneToDisc R.directionPoint:ℂ):=by
    simpa only [Complex.real_smul,triangleVertexUnitDirection] using _root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection_reconstruct
      ⟨(halfPlaneToDisc R.directionPoint:ℂ),triangleVertexTip_ne_zero R⟩
  refine ⟨r*‖(halfPlaneToDisc R.directionPoint:ℂ)‖,
    mul_pos hr (norm_pos_iff.mpr (triangleVertexTip_ne_zero R)),?_⟩
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.kleinDirection,halfPlaneKleinCoordinate_I_zero,sub_zero]
  change kleinCoordinate (halfPlaneToDisc R.directionPoint)=_
  calc
    kleinCoordinate (halfPlaneToDisc R.directionPoint)=r • (halfPlaneToDisc R.directionPoint:ℂ):=he
    _=r • (‖(halfPlaneToDisc R.directionPoint:ℂ)‖ • (triangleVertexUnitDirection R:ℂ)):=congrArg (fun z : ℂ=>r •
      z) htip.symm
    _=_:=by rw [smul_smul]

/-- One actual rotational chart simultaneously normalizes the original closed angle and both mirrors. -/
theorem triangleVertex_angle_chart_at_I (R S : HRayAt UpperHalfPlane.I)
    (hne : R.supportLine≠S.supportLine) (n : ℕ) (hn : 2≤n)
    (hangle : hInteriorAngleMeasure R S=Real.pi/(n:ℝ)) :
    ∃L : ℂ ≃ₗᵢ[ℝ] ℂ,
      (∀z : ℍ,z∈closure (properHAngleInterior R S) ↔
        discOrthogonalIsometry L (halfPlaneToDisc z)∈discDihedralChamber n) ∧
      ({L*_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap ((triangleVertexUnitDirection
        R)*(triangleVertexUnitDirection R)) true*L⁻¹,
         L*_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap ((triangleVertexUnitDirection
           S)*(triangleVertexUnitDirection S)) true*L⁻¹} :
          Set (ℂ ≃ₗᵢ[ℝ] ℂ))=
        {_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap 1 true,_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) true} := by
  have hnR : (2:ℝ)≤(n:ℝ):=by exact_mod_cast hn
  have hnpos : 0<(n:ℝ):=by positivity
  have hθπ : Real.pi/(n:ℝ)<Real.pi:=by
    apply (div_lt_iff₀ hnpos).mpr
    nlinarith [Real.pi_pos]
  have hP : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod (2*n)=Real.pi/(n:ℝ):=by
    simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
  have hPH : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n/2=Real.pi/(n:ℝ):=by
    dsimp only [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod]
    ring
  let U:=triangleVertexUnitDirection R
  let V:=triangleVertexUnitDirection S
  obtain ⟨L,hL⟩:=_root_.LowDimensionalTopology.Geometry.Euclidean.circle_pair_rotation_normal_form U V (Real.pi/(n:ℝ))
    ((triangleVertexUnitDirection_angle R S).trans hangle) hθπ
  have hcone (z : ℍ) : z∈closure (properHAngleInterior R S) ↔
      (halfPlaneToDisc z:ℂ)∈Submodule.span ℝ≥0 {(U:ℂ),(V:ℂ)}:=by
    have hh : z∈closure (properHAngleInterior R S) ↔
        halfPlaneToDisc z∈halfPlaneToDisc '' closure (properHAngleInterior R S):=by
      constructor
      · intro hz
        exact ⟨z,hz,rfl⟩
      · rintro ⟨w,hw,he⟩
        exact cayleyHomeomorph.injective he ▸ hw
    rw [cayley_closure_properHAngleInterior_I R S hne] at hh
    obtain ⟨a,ha,hR⟩:=triangleVertex_kleinDirection_unit R
    obtain ⟨b,hb,hS⟩:=triangleVertex_kleinDirection_unit S
    change z∈closure (properHAngleInterior R S) ↔
      (halfPlaneToDisc z:ℂ)∈Submodule.span ℝ≥0 {R.kleinDirection,S.kleinDirection} at hh
    rw [hR,hS] at hh
    exact hh.trans (_root_.LowDimensionalTopology.Geometry.Euclidean.positiveCone_span_smul_mem_iff a b ha hb)
  refine ⟨L,?_,?_⟩
  · intro z
    rw [hcone]
    change _ ↔ L (halfPlaneToDisc
      z:ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector (2*n)
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector_eq_span (2*n) (by omega),hP]
    have hh:=_root_.LowDimensionalTopology.Geometry.Euclidean.planar_isometry_positive_cone L (U:ℂ) (V:ℂ) (halfPlaneToDisc z:ℂ)
    rcases hL with ⟨h1,h2⟩|⟨h1,h2⟩
    · rwa [h1,h2] at hh
    · rwa [h1,h2,Set.pair_comm (Circle.exp (Real.pi/(n:ℝ)):ℂ) (1:ℂ)] at hh
  · rw [_root_.LowDimensionalTopology.Geometry.Euclidean.planar_reflection_conjugation,_root_.LowDimensionalTopology.Geometry.Euclidean.planar_reflection_conjugation]
    have he (W : Circle) (h : L (W:ℂ)=(Circle.exp (Real.pi/(n:ℝ)):ℂ)) :
        _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap ((_root_.LowDimensionalTopology.Geometry.Euclidean.planarUnitDirection L W)*(_root_.LowDimensionalTopology.Geometry.Euclidean.planarUnitDirection L W)) true=
          _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) true:=by
      have hu : _root_.LowDimensionalTopology.Geometry.Euclidean.planarUnitDirection L W=Circle.exp (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n/2):=
        Circle.ext (h.trans (congrArg (fun t : ℝ=>(Circle.exp t:ℂ)) hPH).symm)
      rw [hu,←pow_two,_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_half_square]
    have he1 (W : Circle) (h : L (W:ℂ)=1) :
        _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap ((_root_.LowDimensionalTopology.Geometry.Euclidean.planarUnitDirection L W)*(_root_.LowDimensionalTopology.Geometry.Euclidean.planarUnitDirection L W)) true=
          _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap 1 true:=by
      have hu : _root_.LowDimensionalTopology.Geometry.Euclidean.planarUnitDirection L W=1:=Circle.ext h
      rw [hu,one_mul]
    rcases hL with ⟨h1,h2⟩|⟨h1,h2⟩
    · rw [he1 U h1,he V h2]
    · rw [he U h2,he1 V h1,Set.pair_comm]

end LowDimensionalTopology.Geometry.Hyperbolic
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon Set Topology
open scoped UpperHalfPlane Complex.UnitDisc
local instance triangleVertexConjugationDiscMetric : MetricSpace 𝔻:=discHyperbolicMetric

/-- Transport of actual native isometries along the actual hyperbolic coordinate isometry. -/
def nativeDiscConjugation (e : ℍ ≃ᵢ 𝔻) : (ℍ ≃ᵢ ℍ)→* (𝔻 ≃ᵢ 𝔻) where
  toFun f:=(e.symm.trans f).trans e
  map_one':=by
    apply IsometryEquiv.ext
    intro z
    exact e.apply_symm_apply z
  map_mul':=by
    intro f g
    apply IsometryEquiv.ext
    intro z
    change e (f (g (e.symm z)))=e (f (e.symm (e (g (e.symm z)))))
    rw [e.symm_apply_apply]

theorem nativeDiscConjugation_apply (e : ℍ ≃ᵢ 𝔻) (f : ℍ ≃ᵢ ℍ) (z : ℍ) :
    nativeDiscConjugation e f (e z)=e (f z) := by
  change e (f (e.symm (e z)))=e (f z)
  rw [e.symm_apply_apply]

theorem nativeDiscConjugation_orthogonal (L P : ℂ ≃ₗᵢ[ℝ] ℂ) :
    nativeDiscConjugation (triangleVertexCayleyIsometry.trans (discOrthogonalIsometry L))
      (triangleVertexOrthogonalHom P)=discOrthogonalHom (L*P*L⁻¹) := by
  apply IsometryEquiv.ext
  intro z
  change discOrthogonalMap L (halfPlaneToDisc (discToHalfPlane
    (discOrthogonalMap P (halfPlaneToDisc (discToHalfPlane (discOrthogonalMap L.symm z))))))=
      discOrthogonalMap (L*P*L⁻¹) z
  rw [halfPlaneToDisc_discToHalfPlane,halfPlaneToDisc_discToHalfPlane]
  apply Subtype.ext
  rfl

/-- The actual original two-reflection group and original mirror pair are normalized together. -/
theorem triangleVertex_group_chart_at_I (R S : HRayAt UpperHalfPlane.I)
    (hne : R.supportLine≠S.supportLine) (n : ℕ) (hn : 2≤n)
    (hangle : hInteriorAngleMeasure R S=Real.pi/(n:ℝ)) :
    ∃e : ℍ ≃ᵢ 𝔻,e UpperHalfPlane.I=0 ∧
      (∀z : ℍ,z∈closure (properHAngleInterior R S) ↔ e z∈discDihedralChamber n) ∧
      (Subgroup.closure ({halfPlaneLineReflectionIsometry R.supportLine,
        halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ))).map
          (nativeDiscConjugation e)=discDihedralGroup n ∧
      nativeDiscConjugation e ''
        ({halfPlaneLineReflectionIsometry R.supportLine,
          halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ))=
        {discOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap 1 true),
          discOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) true)} := by
  obtain ⟨L,hcone,hmirrors⟩:=triangleVertex_angle_chart_at_I R S hne n hn hangle
  let e:=triangleVertexCayleyIsometry.trans (discOrthogonalIsometry L)
  have hPair : nativeDiscConjugation e ''
        ({halfPlaneLineReflectionIsometry R.supportLine,
          halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ))=
        {discOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap 1 true),
          discOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) true)}:=by
    rw [Set.image_pair,triangleVertex_reflection_cayley R,triangleVertex_reflection_cayley S,
      nativeDiscConjugation_orthogonal,nativeDiscConjugation_orthogonal]
    have hh:=congrArg (fun A : Set (ℂ ≃ₗᵢ[ℝ] ℂ)=>discOrthogonalHom '' A) hmirrors
    rwa [Set.image_pair,Set.image_pair] at hh
  refine ⟨e,?_,hcone,?_,hPair⟩
  · change discOrthogonalMap L (halfPlaneToDisc UpperHalfPlane.I)=0
    have hz : halfPlaneToDisc UpperHalfPlane.I=0:=by
      apply discToHalfPlane_injective
      rw [discToHalfPlane_halfPlaneToDisc,discToHalfPlane_zero]
    rw [hz,discOrthogonalMap_zero]
  · rw [MonoidHom.map_closure,hPair]
    change Subgroup.closure _=(_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarDihedralGroup
      n).map discOrthogonalHom
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarDihedralGroup,MonoidHom.map_closure,Set.image_pair]
    rfl

end LowDimensionalTopology.Geometry.Hyperbolic
namespace LowDimensionalTopology.Geometry.Hyperbolic
open Set Topology
open scoped UpperHalfPlane MatrixGroups

/-- Distinct original ray supports remain distinct under a genuine native isometry. -/
theorem ray_support_ne_realGLMap {p : ℍ} (R S : HRayAt p)
    (hne : R.supportLine≠S.supportLine) (g : GL (Fin 2) ℝ) :
    (R.realGLMap g).supportLine≠(S.realGLMap g).supportLine := by
  intro he
  apply hne
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
  apply (Homeomorph.smul g : ℍ ≃ₜ ℍ).injective.image_injective
  change (g • · : ℍ→ℍ) '' R.supportLine.carrier=(g • · : ℍ→ℍ) '' S.supportLine.carrier
  rw [R.realGLMap_support,S.realGLMap_support,he]

/-- The actual chosen side of a full ray support is transported by the real native isometry. -/
theorem hAngleSide_realGL_image {p : ℍ} (R S : HRayAt p)
    (hne : R.supportLine≠S.supportLine) (g : GL (Fin 2) ℝ) :
    (g • · : ℍ→ℍ) '' hAngleSide R S=hAngleSide (R.realGLMap g) (S.realGLMap g) := by
  have htip : g • S.directionPoint∈(S.realGLMap g).val\{g • p}:=
    ⟨S.realGLMap_tip_mem g,(realGL_isometry g).injective.ne S.directionPoint_mem.2⟩
  rw [hAngleSide_eq_component R S hne S.directionPoint_mem,
    hAngleSide_eq_component (R.realGLMap g) (S.realGLMap g)
      (ray_support_ne_realGLMap R S hne g) htip]
  change (g • · : ℍ→ℍ) '' connectedComponentIn R.supportLine.carrierᶜ S.directionPoint=
    connectedComponentIn (R.realGLMap g).supportLine.carrierᶜ (g • S.directionPoint)
  have hc:=(Homeomorph.smul g : ℍ ≃ₜ ℍ).image_connectedComponentIn
    (R.punctured_subset_compl_support S hne S.directionPoint_mem)
  change (g • · : ℍ→ℍ) '' connectedComponentIn R.supportLine.carrierᶜ S.directionPoint=
    connectedComponentIn ((g • · : ℍ→ℍ) '' R.supportLine.carrierᶜ) (g • S.directionPoint) at hc
  rw [hc]
  congr 1
  rw [←R.realGLMap_support,image_compl_eq_range_sdiff_image (realGL_isometry g).injective]
  simp only [Set.range_eq_univ.mpr (MulAction.surjective g)]
  ext z
  simp

/-- Native real isometries carry the original proper angle interior as an actual set. -/
theorem properHAngleInterior_realGL_image {p : ℍ} (R S : HRayAt p)
    (hne : R.supportLine≠S.supportLine) (g : GL (Fin 2) ℝ) :
    (g • · : ℍ→ℍ) '' properHAngleInterior R S=
      properHAngleInterior (R.realGLMap g) (S.realGLMap g) := by
  rw [properHAngleInterior,image_inter (realGL_isometry g).injective,
    hAngleSide_realGL_image R S hne g,hAngleSide_realGL_image S R (Ne.symm hne) g]
  rfl

/-- This transports the genuine whole closed angle, including both original boundary rays. -/
theorem closure_properHAngleInterior_realGL_image {p : ℍ} (R S : HRayAt p)
    (hne : R.supportLine≠S.supportLine) (g : GL (Fin 2) ℝ) :
    (g • · : ℍ→ℍ) '' closure (properHAngleInterior R S)=
      closure (properHAngleInterior (R.realGLMap g) (S.realGLMap g)) := by
  rw [←properHAngleInterior_realGL_image R S hne g]
  exact (Homeomorph.smul g : ℍ ≃ₜ ℍ).image_closure _

end LowDimensionalTopology.Geometry.Hyperbolic
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon Set Topology
open scoped UpperHalfPlane Complex.UnitDisc MatrixGroups
local instance triangleVertexGeneralChartDiscMetric : MetricSpace 𝔻:=discHyperbolicMetric

/-- The same genuine coordinate isometry identifies both the entire original closed sector
and its original two-reflection group, at an arbitrary native vertex. -/
theorem triangleVertex_group_chart {p : ℍ} (R S : HRayAt p)
    (hne : R.supportLine≠S.supportLine) (n : ℕ) (hn : 2≤n)
    (hangle : hInteriorAngleMeasure R S=Real.pi/(n:ℝ)) :
    ∃e : ℍ ≃ᵢ 𝔻,e p=0 ∧
      (∀z : ℍ,z∈closure (properHAngleInterior R S) ↔ e z∈discDihedralChamber n) ∧
      (Subgroup.closure ({halfPlaneLineReflectionIsometry R.supportLine,
        halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ))).map
          (nativeDiscConjugation e)=discDihedralGroup n ∧
      nativeDiscConjugation e ''
        ({halfPlaneLineReflectionIsometry R.supportLine,
          halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ))=
        {discOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap 1 true),
          discOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) true)} := by
  obtain ⟨q,hq⟩:=MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) ℝ) p UpperHalfPlane.I
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ q
  let R':=R.realGLMap g
  let S':=S.realGLMap g
  have hAux : ∀(z : ℍ)(A B : HRayAt z),z=UpperHalfPlane.I → A.supportLine≠B.supportLine →
      hInteriorAngleMeasure A B=Real.pi/(n:ℝ) →
      ∃e : ℍ ≃ᵢ 𝔻,e z=0 ∧
        (∀w : ℍ,w∈closure (properHAngleInterior A B) ↔ e w∈discDihedralChamber n) ∧
        (Subgroup.closure ({halfPlaneLineReflectionIsometry A.supportLine,
          halfPlaneLineReflectionIsometry B.supportLine}:Set (ℍ ≃ᵢ ℍ))).map
          (nativeDiscConjugation e)=discDihedralGroup n ∧
          nativeDiscConjugation e ''
            ({halfPlaneLineReflectionIsometry A.supportLine,
              halfPlaneLineReflectionIsometry B.supportLine}:Set (ℍ ≃ᵢ ℍ))=
            {discOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap 1 true),
              discOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) true)}:=by
    intro z A B hz hne' hθ
    subst z
    exact triangleVertex_group_chart_at_I A B hne' n hn hθ
  obtain ⟨e,he0,heCone,heG,hePair⟩:=hAux _ R' S' hq (ray_support_ne_realGLMap R S hne g)
    ((hInteriorAngleMeasure_realGLMap R S g).trans hangle)
  let f:=(hSLIsometry q).trans e
  let k : (ℍ ≃ᵢ ℍ)→* (ℍ ≃ᵢ ℍ):=(MulAut.conj (hSLIsometry q)).toMonoidHom
  have hHom : nativeDiscConjugation f=(nativeDiscConjugation e).comp k:=by
    apply MonoidHom.ext
    intro a
    apply IsometryEquiv.ext
    intro z
    change e (q • (a (q⁻¹ • e.symm z)))=e (q • (a (q⁻¹ • e.symm z)))
    rfl
  refine ⟨f,he0,?_,?_,?_⟩
  · intro z
    have hh : z∈closure (properHAngleInterior R S) ↔
        q • z∈closure (properHAngleInterior R' S'):=by
      rw [←closure_properHAngleInterior_realGL_image R S hne g]
      constructor
      · intro hz
        exact ⟨z,hz,rfl⟩
      · rintro ⟨w,hw,he⟩
        exact (realGL_isometry g).injective he ▸ hw
    exact hh.trans (heCone (q • z))
  · have hK : (Subgroup.closure ({halfPlaneLineReflectionIsometry R.supportLine,
        halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ))).map k=
        Subgroup.closure ({halfPlaneLineReflectionIsometry R'.supportLine,
          halfPlaneLineReflectionIsometry S'.supportLine}:Set (ℍ ≃ᵢ ℍ)):=by
      rw [MonoidHom.map_closure,Set.image_pair]
      have hR : k (halfPlaneLineReflectionIsometry R.supportLine)=
          halfPlaneLineReflectionIsometry R'.supportLine:=native_ray_reflection_conjugation R q
      have hS : k (halfPlaneLineReflectionIsometry S.supportLine)=
          halfPlaneLineReflectionIsometry S'.supportLine:=native_ray_reflection_conjugation S q
      rw [hR,hS]
    rw [hHom,←Subgroup.map_map,hK]
    exact heG
  · rw [hHom,MonoidHom.coe_comp,Set.image_comp]
    have hPair : k ''
        ({halfPlaneLineReflectionIsometry R.supportLine,
          halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ))=
        {halfPlaneLineReflectionIsometry R'.supportLine,
          halfPlaneLineReflectionIsometry S'.supportLine}:=by
      rw [Set.image_pair]
      have hR : k (halfPlaneLineReflectionIsometry R.supportLine)=
          halfPlaneLineReflectionIsometry R'.supportLine:=native_ray_reflection_conjugation R q
      have hS : k (halfPlaneLineReflectionIsometry S.supportLine)=
          halfPlaneLineReflectionIsometry S'.supportLine:=native_ray_reflection_conjugation S q
      rw [hR,hS]
    rw [hPair]
    exact hePair

end LowDimensionalTopology.Geometry.Hyperbolic
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon Set Topology
open scoped UpperHalfPlane Complex.UnitDisc
local instance triangleVertexGeometryDiscMetric : MetricSpace 𝔻:=discHyperbolicMetric

theorem nativeDiscConjugation_injective (e : ℍ ≃ᵢ 𝔻) :
    Function.Injective (nativeDiscConjugation e) := by
  intro a b he
  apply IsometryEquiv.ext
  intro z
  apply e.injective
  exact (nativeDiscConjugation_apply e a z).symm.trans
    ((congrArg (fun f : 𝔻 ≃ᵢ 𝔻=>f (e z)) he).trans (nativeDiscConjugation_apply e b z))

/-- The real two-mirror images of the genuine closed angle fill each actual ball about its vertex. -/
theorem triangleVertex_closed_angle_ball_cover {p : ℍ} (R S : HRayAt p)
    (hne : R.supportLine≠S.supportLine) (n : ℕ) (hn : 2≤n)
    (hangle : hInteriorAngleMeasure R S=Real.pi/(n:ℝ)) (r : ℝ) (y : ℍ)
    (hy : y∈Metric.ball p r) :
    ∃g : ℍ ≃ᵢ ℍ,g∈Subgroup.closure ({halfPlaneLineReflectionIsometry R.supportLine,
        halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ)) ∧
      ∃x : ℍ,x∈closure (properHAngleInterior R S) ∧ x∈Metric.ball p r ∧ g x=y := by
  obtain ⟨e,he0,heCone,heG,_⟩:=triangleVertex_group_chart R S hne n hn hangle
  have hyD : e y∈Metric.ball (0:𝔻) r:=by
    rw [←he0]
    change dist (e y) (e p)<r
    rw [e.dist_eq]
    exact hy
  have hh : e y∈⋃(i : Fin n)(b : Bool),discDihedralAction n i b ''
      (discDihedralChamber n∩Metric.ball (0:𝔻) r):=by
    rw [discDihedral_closed_chamber_ball_cover n (by omega)]
    exact hyD
  obtain ⟨i,hh⟩:=mem_iUnion.mp hh
  obtain ⟨b,v,⟨hv,hvr⟩,hvy⟩:=mem_iUnion.mp hh
  have hAction : discDihedralAction n i b∈
      (Subgroup.closure ({halfPlaneLineReflectionIsometry R.supportLine,
        halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ))).map (nativeDiscConjugation e):=by
    rw [heG]
    exact discDihedralAction_mem n i b
  obtain ⟨g,hg,hge⟩:=hAction
  let x:=e.symm v
  have hx : e x=v:=e.apply_symm_apply v
  refine ⟨g,hg,x,(heCone x).mpr (hx ▸ hv),?_,?_⟩
  · change dist x p<r
    rw [←e.dist_eq x p,he0,hx]
    exact hvr
  · apply e.injective
    rw [←nativeDiscConjugation_apply e g x,hge,hx]
    exact hvy

/-- No two distinct original chamber points lie in the same actual two-reflection orbit. -/
theorem triangleVertex_closed_angle_orbit_unique {p : ℍ} (R S : HRayAt p)
    (hne : R.supportLine≠S.supportLine) (n : ℕ) (hn : 2≤n)
    (hangle : hInteriorAngleMeasure R S=Real.pi/(n:ℝ)) (g : ℍ ≃ᵢ ℍ)
    (hg : g∈Subgroup.closure ({halfPlaneLineReflectionIsometry R.supportLine,
        halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ)))
    (x y : ℍ) (hx : x∈closure (properHAngleInterior R S))
    (hy : y∈closure (properHAngleInterior R S)) (he : g x=y) : x=y := by
  obtain ⟨e,_,heCone,heG,_⟩:=triangleVertex_group_chart R S hne n hn hangle
  have hgD : nativeDiscConjugation e g∈discDihedralGroup n:=by
    rw [←heG]
    exact ⟨g,hg,rfl⟩
  have hxy : nativeDiscConjugation e g (e x)=(1:𝔻 ≃ᵢ 𝔻) (e y):=by
    rw [nativeDiscConjugation_apply,he]
    rfl
  exact e.injective (discDihedral_chamber_coincidence n (by omega)
    (nativeDiscConjugation e g) 1 hgD (discDihedralGroup n).one_mem
    (e x) (e y) ((heCone x).mp hx) ((heCone y).mp hy) hxy).1

/-- A nonvertex chamber stabilizer is an original boundary mirror or the identity. -/
theorem triangleVertex_closed_angle_stabilizer {p : ℍ} (R S : HRayAt p)
    (hne : R.supportLine≠S.supportLine) (n : ℕ) (hn : 2≤n)
    (hangle : hInteriorAngleMeasure R S=Real.pi/(n:ℝ)) (g : ℍ ≃ᵢ ℍ)
    (hg : g∈Subgroup.closure ({halfPlaneLineReflectionIsometry R.supportLine,
        halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ)))
    (x : ℍ) (hx : x∈closure (properHAngleInterior R S)) (he : g x=x) :
    x=p ∨ g=1 ∨ (g=halfPlaneLineReflectionIsometry R.supportLine ∨
      g=halfPlaneLineReflectionIsometry S.supportLine) := by
  obtain ⟨e,he0,heCone,heG,hePair⟩:=triangleVertex_group_chart R S hne n hn hangle
  have hgD : nativeDiscConjugation e g∈discDihedralGroup n:=by
    rw [←heG]
    exact ⟨g,hg,rfl⟩
  have hxy : nativeDiscConjugation e g (e x)=(1:𝔻 ≃ᵢ 𝔻) (e x):=by
    rw [nativeDiscConjugation_apply,he]
    rfl
  have hcases:=(discDihedral_chamber_coincidence n (by omega)
    (nativeDiscConjugation e g) 1 hgD (discDihedralGroup n).one_mem
    (e x) (e x) ((heCone x).mp hx) ((heCone x).mp hx) hxy).2
  rcases hcases with hx0|h1|⟨L,hL,_,hgL⟩
  · exact Or.inl (e.injective (hx0.trans he0.symm))
  · right;left
    apply nativeDiscConjugation_injective e
    rw [map_one]
    exact h1
  · right;right
    have himg : nativeDiscConjugation e g∈nativeDiscConjugation e ''
        ({halfPlaneLineReflectionIsometry R.supportLine,
          halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ)):=by
      rw [hePair]
      rw [one_mul] at hgL
      rcases hL with rfl|rfl
      · exact Or.inl hgL
      · exact Or.inr (mem_singleton_iff.mpr hgL)
    obtain ⟨a,ha,heq⟩:=himg
    have hag : a=g:=nativeDiscConjugation_injective e heq
    rw [hag] at ha
    exact ha

end LowDimensionalTopology.Geometry.Hyperbolic
