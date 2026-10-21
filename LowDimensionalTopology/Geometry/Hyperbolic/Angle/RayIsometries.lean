/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleCongruence
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.ClosedHalfPlane

@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

def HRayAt.realGLMap {z : ℍ} (R : HRayAt z) (g : GL (Fin 2) ℝ) : HRayAt (g • z) :=
  hRayThrough (g • z) (g • R.directionPoint)
    ((realGL_isometry g).injective.ne (Ne.symm (show R.directionPoint ≠ z from R.directionPoint_mem.2)))

theorem HRayAt.realGLMap_tip_mem {z : ℍ} (R : HRayAt z) (g : GL (Fin 2) ℝ) :
    g • R.directionPoint ∈ (R.realGLMap g).val := hRayThrough_mem _ _ _

theorem HRayAt.realGLMap_support {z : ℍ} (R : HRayAt z) (g : GL (Fin 2) ℝ) :
    (g • · : ℍ → ℍ) '' R.supportLine.carrier = (R.realGLMap g).supportLine.carrier :=
  realGL_image_line_of_corresponding_points g R.supportLine (R.realGLMap g).supportLine
    (Ne.symm (show R.directionPoint ≠ z from R.directionPoint_mem.2)) R.start_mem_support (R.subset_support
      R.directionPoint_mem.1)
    (R.realGLMap g).start_mem_support ((R.realGLMap g).subset_support (R.realGLMap_tip_mem g))

/-- A genuine fractional-linear isometry maps the full actual forward ray, not merely its support. -/
theorem HRayAt.realGLMap_carrier {z : ℍ} (R : HRayAt z) (g : GL (Fin 2) ℝ) :
    (g • · : ℍ → ℍ) '' R.val = (R.realGLMap g).val := by
  have htip : g • R.directionPoint ∈ (R.realGLMap g).val \ {g • z} :=
    ⟨R.realGLMap_tip_mem g,(realGL_isometry g).injective.ne R.directionPoint_mem.2⟩
  have hc := (Homeomorph.smul g : ℍ ≃ₜ ℍ).image_connectedComponentIn
    (show R.directionPoint ∈ R.supportLine.carrier \ {z} from
      ⟨R.subset_support R.directionPoint_mem.1,R.directionPoint_mem.2⟩)
  rw [← R.punctured_eq_component R.directionPoint_mem] at hc
  change (g • · : ℍ → ℍ) '' (R.val \ {z}) =
    connectedComponentIn ((g • · : ℍ → ℍ) '' (R.supportLine.carrier \ {z}))
      (g • R.directionPoint) at hc
  have hdom : (g • · : ℍ → ℍ) '' (R.supportLine.carrier \ {z}) =
      (R.realGLMap g).supportLine.carrier \ {g • z} := by
    rw [image_sdiff (realGL_isometry g).injective,R.realGLMap_support,image_singleton]
  rw [hdom,← (R.realGLMap g).punctured_eq_component htip] at hc
  have hR : R.val = insert z (R.val \ {z}) := by
    ext x
    by_cases hx : x = z
    · subst x
      simp [R.start_mem]
    · simp [hx]
  have hS : (R.realGLMap g).val = insert (g • z) ((R.realGLMap g).val \ {g • z}) := by
    ext x
    by_cases hx : x = g • z
    · subst x
      simp [(R.realGLMap g).start_mem]
    · simp [hx]
  rw [hR,hS,image_insert_eq,hc]

/-- Metric isometries preserve the genuine Euclidean forward-tangent angle of arbitrary rays. -/
theorem hInteriorAngleMeasure_realGLMap {z : ℍ} (R S : HRayAt z) (g : GL (Fin 2) ℝ) :
    hInteriorAngleMeasure (R.realGLMap g) (S.realGLMap g) = hInteriorAngleMeasure R S := by
  have h₁ := hInteriorAngleMeasure_cosine_rule R S R.directionPoint_mem.1
    R.directionPoint_mem.2 S.directionPoint_mem.1 S.directionPoint_mem.2
  have h₂ := hInteriorAngleMeasure_cosine_rule (R.realGLMap g) (S.realGLMap g)
    (R.realGLMap_tip_mem g) ((realGL_isometry g).injective.ne R.directionPoint_mem.2)
    (S.realGLMap_tip_mem g) ((realGL_isometry g).injective.ne S.directionPoint_mem.2)
  rw [(realGL_isometry g).dist_eq,(realGL_isometry g).dist_eq,(realGL_isometry g).dist_eq] at h₂
  exact angle_eq_of_hyperbolic_cosine_rule
    (dist_pos.mpr (Ne.symm (show R.directionPoint ≠ z from R.directionPoint_mem.2)))
    (dist_pos.mpr (Ne.symm (show S.directionPoint ≠ z from S.directionPoint_mem.2)))
    ⟨angle_nonneg _ _,angle_le_pi _ _⟩ ⟨angle_nonneg _ _,angle_le_pi _ _⟩ h₂ h₁

def HRayAt.mapIsometry {z : ℍ} (R : HRayAt z) (f : ℍ → ℍ) (hf : Isometry f) : HRayAt (f z) :=
  hRayThrough (f z) (f R.directionPoint)
    (hf.injective.ne (Ne.symm (show R.directionPoint ≠ z from R.directionPoint_mem.2)))

theorem HRayAt.mapIsometry_carrier {z : ℍ} (R : HRayAt z) (f : ℍ → ℍ) (hf : Isometry f) :
    f '' R.val = (R.mapIsometry f hf).val := by
  obtain ⟨g,rfl⟩ := isometry_exists_realGL hf
  exact R.realGLMap_carrier g

theorem hInteriorAngleMeasure_mapIsometry {z : ℍ} (R S : HRayAt z) (f : ℍ → ℍ) (hf : Isometry f) :
    hInteriorAngleMeasure (R.mapIsometry f hf) (S.mapIsometry f hf) = hInteriorAngleMeasure R S := by
  obtain ⟨g,rfl⟩ := isometry_exists_realGL hf
  exact hInteriorAngleMeasure_realGLMap R S g

theorem discPathIsometry_conjugate {f : 𝔻 → 𝔻}
    (hf : ∀ z w, discPathDist (f z) (f w) = discPathDist z w) :
    Isometry (fun z : ℍ => discToHalfPlane (f (halfPlaneToDisc z))) := by
  apply Isometry.of_dist_eq
  intro z w
  have he := hf (halfPlaneToDisc z) (halfPlaneToDisc w)
  simpa only [discPathDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc] using he

def DiscTriangle.mapPathIsometry (T : DiscTriangle) (f : 𝔻 → 𝔻)
    (hf : ∀ z w, discPathDist (f z) (f w) = discPathDist z w) : DiscTriangle :=
  (T.toHalfPlane.mapIsometry (fun z => discToHalfPlane (f (halfPlaneToDisc z)))
    (discPathIsometry_conjugate hf)).toDiscTriangle

theorem DiscTriangle.mapPathIsometry_vertices (T : DiscTriangle) (f : 𝔻 → 𝔻)
    (hf : ∀ z w, discPathDist (f z) (f w) = discPathDist z w) :
    (T.mapPathIsometry f hf).a = f T.a ∧ (T.mapPathIsometry f hf).b = f T.b ∧
      (T.mapPathIsometry f hf).c = f T.c := by
  change halfPlaneToDisc (discToHalfPlane (f (halfPlaneToDisc (discToHalfPlane T.a)))) = f T.a ∧
    halfPlaneToDisc (discToHalfPlane (f (halfPlaneToDisc (discToHalfPlane T.b)))) = f T.b ∧
    halfPlaneToDisc (discToHalfPlane (f (halfPlaneToDisc (discToHalfPlane T.c)))) = f T.c
  simp only [halfPlaneToDisc_discToHalfPlane,and_self]

theorem DiscTriangle.mapPathIsometry_lengths (T : DiscTriangle) (f : 𝔻 → 𝔻)
    (hf : ∀ z w, discPathDist (f z) (f w) = discPathDist z w) :
    (T.mapPathIsometry f hf).lengthA = T.lengthA ∧
      (T.mapPathIsometry f hf).lengthB = T.lengthB ∧
        (T.mapPathIsometry f hf).lengthC = T.lengthC := by
  simp only [DiscTriangle.lengthA,DiscTriangle.lengthB,DiscTriangle.lengthC,
    (T.mapPathIsometry_vertices f hf).1,(T.mapPathIsometry_vertices f hf).2.1,
    (T.mapPathIsometry_vertices f hf).2.2,hf,and_self]

theorem DiscTriangle.mapPathIsometry_angles (T : DiscTriangle) (f : 𝔻 → 𝔻)
    (hf : ∀ z w, discPathDist (f z) (f w) = discPathDist z w) :
    (T.mapPathIsometry f hf).alpha = T.alpha ∧
      (T.mapPathIsometry f hf).beta = T.beta ∧
        (T.mapPathIsometry f hf).gamma = T.gamma := by
  let F : ℍ → ℍ := fun z => discToHalfPlane (f (halfPlaneToDisc z))
  let U := T.toHalfPlane.mapIsometry F (discPathIsometry_conjugate hf)
  have hU := U.toDiscTriangle.angles_eq_halfPlane
  rw [U.toDiscTriangle_toHalfPlane] at hU
  have hA := T.toHalfPlane.mapIsometry_angles F (discPathIsometry_conjugate hf)
  exact ⟨hU.1.trans (hA.1.trans T.angles_eq_halfPlane.1.symm),
    hU.2.1.trans (hA.2.1.trans T.angles_eq_halfPlane.2.1.symm),
    hU.2.2.trans (hA.2.2.trans T.angles_eq_halfPlane.2.2.symm)⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
