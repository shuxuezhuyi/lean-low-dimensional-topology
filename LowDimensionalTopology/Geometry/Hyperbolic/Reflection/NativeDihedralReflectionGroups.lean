/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.PlanarReflectionConjugacy
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.DiscOrthogonalActions
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeLineReflections
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ParabolicReflectionPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.FiniteAngleNormalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
open scoped UpperHalfPlane Complex.UnitDisc MatrixGroups
local instance triangleVertexReflectionDiscMetric : MetricSpace 𝔻:=discHyperbolicMetric

def triangleVertexCayleyIsometry : ℍ ≃ᵢ 𝔻 where
  toEquiv:=cayleyHomeomorph.toEquiv
  isometry_toFun:=cayley_isometry

def triangleVertexOrthogonalIsometry (L : ℂ ≃ₗᵢ[ℝ] ℂ) : ℍ ≃ᵢ ℍ :=
  (triangleVertexCayleyIsometry.trans (discOrthogonalIsometry L)).trans triangleVertexCayleyIsometry.symm

def triangleVertexOrthogonalHom : (ℂ ≃ₗᵢ[ℝ] ℂ)→* (ℍ ≃ᵢ ℍ) where
  toFun:=triangleVertexOrthogonalIsometry
  map_one':=by
    apply IsometryEquiv.ext
    intro z
    exact discToHalfPlane_halfPlaneToDisc z
  map_mul':=by
    intro L M
    apply IsometryEquiv.ext
    intro z
    change discToHalfPlane (discOrthogonalMap (L*M) (halfPlaneToDisc z))=
      discToHalfPlane (discOrthogonalMap L (halfPlaneToDisc
        (discToHalfPlane (discOrthogonalMap M (halfPlaneToDisc z)))))
    rw [halfPlaneToDisc_discToHalfPlane]
    rfl

theorem triangleVertexTip_ne_zero (R : HRayAt UpperHalfPlane.I) :
    ((halfPlaneToDisc R.directionPoint:𝔻):ℂ)≠0 := by
  intro he
  have heD : halfPlaneToDisc R.directionPoint=0:=Subtype.ext he
  have heH:=congrArg discToHalfPlane heD
  rw [discToHalfPlane_halfPlaneToDisc,discToHalfPlane_zero] at heH
  exact R.directionPoint_mem.2 heH

def triangleVertexUnitDirection (R : HRayAt UpperHalfPlane.I) : Circle :=
  _root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨(halfPlaneToDisc
    R.directionPoint:ℂ),triangleVertexTip_ne_zero R⟩

/-- The original native geometric mirror is exactly the transported genuine planar mirror. -/
theorem triangleVertex_reflection_cayley (R : HRayAt UpperHalfPlane.I) :
    halfPlaneLineReflectionIsometry R.supportLine=
      triangleVertexOrthogonalHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap
        ((triangleVertexUnitDirection R)*(triangleVertexUnitDirection R)) true) := by
  let D:=R.supportLine.toDiscLine
  have h0 : (0:𝔻)∈D.carrier:=by
    rw [DiscLine.mem_carrier,HalfPlaneLine.toDiscLine_toHalfPlane,discToHalfPlane_zero]
    exact R.start_mem_support
  have htip : halfPlaneToDisc R.directionPoint∈D.carrier:=by
    rw [DiscLine.mem_carrier,HalfPlaneLine.toDiscLine_toHalfPlane,discToHalfPlane_halfPlaneToDisc]
    exact R.subset_support R.directionPoint_mem.1
  have hcoef:=D.reflection_zero_direction h0 (halfPlaneToDisc R.directionPoint) htip (triangleVertexTip_ne_zero R)
  apply IsometryEquiv.ext
  intro z
  change R.supportLine.reflection z=discToHalfPlane (discOrthogonalMap
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap
      ((triangleVertexUnitDirection R)*(triangleVertexUnitDirection R)) true) (halfPlaneToDisc z))
  apply cayleyHomeomorph.injective
  change halfPlaneToDisc (R.supportLine.reflection z)=halfPlaneToDisc (discToHalfPlane
    (discOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap
      ((triangleVertexUnitDirection R)*(triangleVertexUnitDirection R)) true) (halfPlaneToDisc z)))
  rw [halfPlaneToDisc_discToHalfPlane]
  have he := hcoef (halfPlaneToDisc z)
  have heD : D.reflection (halfPlaneToDisc z)=
      discOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap
        ((triangleVertexUnitDirection R)*(triangleVertexUnitDirection R)) true) (halfPlaneToDisc z):=
    Subtype.ext he
  change halfPlaneToDisc (D.toHalfPlane.reflection (discToHalfPlane (halfPlaneToDisc z)))=_ at heD
  rwa [HalfPlaneLine.toDiscLine_toHalfPlane,discToHalfPlane_halfPlaneToDisc] at heD

/-- The ordinary angle of the actual normalized unit directions is the independent native ray angle. -/
theorem triangleVertexUnitDirection_angle (R S : HRayAt UpperHalfPlane.I) :
    InnerProductGeometry.angle (triangleVertexUnitDirection R:ℂ) (triangleVertexUnitDirection S:ℂ)=
      hInteriorAngleMeasure R S := by
  have hR : ‖(halfPlaneToDisc R.directionPoint:ℂ)‖ • (triangleVertexUnitDirection R:ℂ)=
      (halfPlaneToDisc R.directionPoint:ℂ):=by
    simpa only [Complex.real_smul,triangleVertexUnitDirection] using _root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection_reconstruct
      ⟨(halfPlaneToDisc R.directionPoint:ℂ),triangleVertexTip_ne_zero R⟩
  have hS : ‖(halfPlaneToDisc S.directionPoint:ℂ)‖ • (triangleVertexUnitDirection S:ℂ)=
      (halfPlaneToDisc S.directionPoint:ℂ):=by
    simpa only [Complex.real_smul,triangleVertexUnitDirection] using _root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection_reconstruct
      ⟨(halfPlaneToDisc S.directionPoint:ℂ),triangleVertexTip_ne_zero S⟩
  have hθ:=hInteriorAngleMeasure_I_cayley R S R.directionPoint_mem.1 R.directionPoint_mem.2
    S.directionPoint_mem.1 S.directionPoint_mem.2
  rw [←hR,←hS,InnerProductGeometry.angle_smul_left_of_pos _ _ (norm_pos_iff.mpr (triangleVertexTip_ne_zero R)),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (norm_pos_iff.mpr (triangleVertexTip_ne_zero S))] at hθ
  exact hθ.symm

/-- Two original native reflections at angle pi/n generate a finite actual subgroup. -/
theorem native_reflections_finite_at_I (R S : HRayAt UpperHalfPlane.I) (n : ℕ) (hn : 2≤n)
    (hangle : hInteriorAngleMeasure R S=Real.pi/(n:ℝ)) :
    (Subgroup.closure ({halfPlaneLineReflectionIsometry R.supportLine,
      halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ)) : Set (ℍ ≃ᵢ ℍ)).Finite := by
  have hfin:=_root_.LowDimensionalTopology.Geometry.Euclidean.planarMirrorGroup_finite_of_angle n hn (triangleVertexUnitDirection R) (triangleVertexUnitDirection S)
    ((triangleVertexUnitDirection_angle R S).trans hangle)
  have he : Subgroup.closure ({halfPlaneLineReflectionIsometry R.supportLine,
      halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ))=
      (_root_.LowDimensionalTopology.Geometry.Euclidean.planarMirrorGroup (triangleVertexUnitDirection R)
        (triangleVertexUnitDirection S)).map
        triangleVertexOrthogonalHom := by
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.planarMirrorGroup,MonoidHom.map_closure,Set.image_pair,
      ←triangleVertex_reflection_cayley R,←triangleVertex_reflection_cayley S]
  rw [he]
  exact hfin.image triangleVertexOrthogonalHom

/-- Native reflection conjugacy follows the actual image ray support. -/
theorem native_ray_reflection_conjugation {p : ℍ} (R : HRayAt p)
    (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    hSLIsometry q*halfPlaneLineReflectionIsometry R.supportLine*(hSLIsometry q)⁻¹=
      halfPlaneLineReflectionIsometry (R.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)).supportLine := by
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ q
  have hline : R.supportLine.realGLMap g=(R.realGLMap g).supportLine:=
    HalfPlaneLine.carrier_injective ((R.supportLine.realGLMap_carrier g).trans (R.realGLMap_support g))
  apply IsometryEquiv.ext
  intro z
  change q • R.supportLine.reflection (q⁻¹ • z)=_
  change g • R.supportLine.reflection ((Matrix.SpecialLinearGroup.mapGL ℝ q⁻¹) • z)=_
  rw [map_inv,R.supportLine.reflection_realGL_conjugation g,hline]
  rfl

/-- Two original actual mirrors at any native vertex, with angle pi/n, generate a finite subgroup. -/
theorem native_reflections_finite_of_angle {p : ℍ} (R S : HRayAt p) (n : ℕ) (hn : 2≤n)
    (hangle : hInteriorAngleMeasure R S=Real.pi/(n:ℝ)) :
    (Subgroup.closure ({halfPlaneLineReflectionIsometry R.supportLine,
      halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ)) : Set (ℍ ≃ᵢ ℍ)).Finite := by
  obtain ⟨q,hq⟩:=MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) ℝ) p UpperHalfPlane.I
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ q
  let R':=R.realGLMap g
  let S':=S.realGLMap g
  have hfinite : (Subgroup.closure ({halfPlaneLineReflectionIsometry R'.supportLine,
      halfPlaneLineReflectionIsometry S'.supportLine}:Set (ℍ ≃ᵢ ℍ)) : Set (ℍ ≃ᵢ ℍ)).Finite:=by
    have haux : ∀(z : ℍ)(A B : HRayAt z),z=UpperHalfPlane.I →
        hInteriorAngleMeasure A B=Real.pi/(n:ℝ) →
        (Subgroup.closure ({halfPlaneLineReflectionIsometry A.supportLine,
          halfPlaneLineReflectionIsometry B.supportLine}:Set (ℍ ≃ᵢ ℍ)) : Set (ℍ ≃ᵢ ℍ)).Finite:=by
      intro z A B hz hθ
      subst z
      exact native_reflections_finite_at_I A B n hn hθ
    exact haux _ R' S' hq ((hInteriorAngleMeasure_realGLMap R S g).trans hangle)
  let f : (ℍ ≃ᵢ ℍ)→* (ℍ ≃ᵢ ℍ):=(MulAut.conj (hSLIsometry q)).toMonoidHom
  have hle : Subgroup.closure ({halfPlaneLineReflectionIsometry R.supportLine,
      halfPlaneLineReflectionIsometry S.supportLine}:Set (ℍ ≃ᵢ ℍ))≤
      (Subgroup.closure ({halfPlaneLineReflectionIsometry R'.supportLine,
        halfPlaneLineReflectionIsometry S'.supportLine}:Set (ℍ ≃ᵢ ℍ))).comap f:=by
    apply (Subgroup.closure_le _).mpr
    rintro a (rfl|ha)
    · change hSLIsometry q*halfPlaneLineReflectionIsometry R.supportLine*(hSLIsometry q)⁻¹∈
        Subgroup.closure ({halfPlaneLineReflectionIsometry R'.supportLine,
          halfPlaneLineReflectionIsometry S'.supportLine}:Set (ℍ ≃ᵢ ℍ))
      rw [native_ray_reflection_conjugation]
      exact Subgroup.subset_closure (Or.inl rfl)
    · have he : a=halfPlaneLineReflectionIsometry S.supportLine:=mem_singleton_iff.mp ha
      subst a
      change hSLIsometry q*halfPlaneLineReflectionIsometry S.supportLine*(hSLIsometry q)⁻¹∈
        Subgroup.closure ({halfPlaneLineReflectionIsometry R'.supportLine,
          halfPlaneLineReflectionIsometry S'.supportLine}:Set (ℍ ≃ᵢ ℍ))
      rw [native_ray_reflection_conjugation]
      exact Subgroup.subset_closure (Or.inr (mem_singleton _))
  exact (hfinite.preimage (MulAut.conj (hSLIsometry q)).injective.injOn).subset hle

end LowDimensionalTopology.Geometry.Hyperbolic
