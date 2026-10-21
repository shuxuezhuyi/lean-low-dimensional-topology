/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Isometry

/-!
# Orthogonal spatial actions in the Lorentz model

Original determinant and orientation lemmas supporting.
The actual projective ball action is identified with the spatial orthogonal
action; the criterion for the special subgroup is proved for these matrices.
-/

@[expose] public section
noncomputable section
open Set Matrix
open scoped MatrixGroups RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n : ℕ}

def lorentzSpatialLinearMap (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) :
    LorentzVector n →ₗ[ℝ] LorentzVector n :=
  LinearMap.prodMap LinearMap.id L.toLinearMap

theorem lorentzSpatialLinearMap_apply (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n)
    (x : LorentzVector n) : lorentzSpatialLinearMap L x=(x.1,L x.2) := rfl

theorem lorentzRowMatrix_det (T : LorentzVector n →ₗ[ℝ] LorentzVector n) :
    (lorentzRowMatrix T).det=LinearMap.det T := by
  rw [lorentzRowMatrix,Matrix.det_transpose,LinearMap.det_toMatrix']
  exact LinearMap.det_conj T (lorentzCoordinates n)

def lorentzSpatialMatrix (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ := lorentzRowMatrix (lorentzSpatialLinearMap L)

theorem lorentzSpatialMatrix_det (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) :
    (lorentzSpatialMatrix L).det=LinearMap.det L.toLinearMap := by
  rw [lorentzSpatialMatrix,lorentzRowMatrix_det,lorentzSpatialLinearMap,LinearMap.det_prodMap]
  simp

theorem lorentzSpatialMatrix_det_ne_zero (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) :
    (lorentzSpatialMatrix L).det≠0 := by
  rw [lorentzSpatialMatrix_det]
  exact L.toLinearEquiv.isUnit_det'.ne_zero

theorem lorentzSpatialMatrix_preserves_form (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n)
    (x y : LorentzVector n) :
    lorentzForm (lorentzRowLinearMap (lorentzSpatialMatrix L) x)
      (lorentzRowLinearMap (lorentzSpatialMatrix L) y)=lorentzForm x y := by
  rw [lorentzSpatialMatrix,lorentzRowLinearMap_rowMatrix]
  simp only [lorentzSpatialLinearMap_apply,lorentzForm,L.inner_map_map]

theorem lorentzSpatialMatrix_timeTime (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) :
    lorentzSpatialMatrix L 0 0=1 := by
  rw [← lorentzRowLinearMap_timeUnit_time (lorentzSpatialMatrix L),lorentzSpatialMatrix,lorentzRowLinearMap_rowMatrix]
  rfl

def lorentzSpatialGroup (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) :
    lorentzPositiveOrthogonalGroup n := by
  let A : GL (Fin (n+1)) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (lorentzSpatialMatrix L) (lorentzSpatialMatrix_det_ne_zero L)
  refine ⟨A,(mem_lorentzPositiveOrthogonalGroup A).mpr ⟨?_,?_⟩⟩
  · exact (lorentz_matrix_identity_iff_preserves_form _).mpr
      (lorentzSpatialMatrix_preserves_form L)
  · change 0<lorentzSpatialMatrix L 0 0
    rw [lorentzSpatialMatrix_timeTime]
    norm_num

theorem lorentzSpatialGroup_matrix (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) :
    (lorentzSpatialGroup L).val.val=lorentzSpatialMatrix L := rfl

theorem lorentzSpatialGroup_det (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) :
    (lorentzSpatialGroup L).val.val.det=LinearMap.det L.toLinearMap :=
  lorentzSpatialMatrix_det L

theorem lorentzSpatialGroup_apply_val (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n)
    (x : Hyperboloid n) :
    (lorentzHyperboloidMap (lorentzSpatialGroup L) x).val=(x.val.1,L x.val.2) := by
  change lorentzRowLinearMap (lorentzSpatialMatrix L) x.val=_
  rw [lorentzSpatialMatrix,lorentzRowLinearMap_rowMatrix]
  rfl

theorem hyperboloidProject_lorentzSpatialGroup (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n)
    (x : Hyperboloid n) :
    hyperboloidProject (lorentzHyperboloidMap (lorentzSpatialGroup L) x)=
      ballHomeomorph (Inversive.cartanLinearExtensionHom L) (Inversive.cartanLinearExtension_preservesUnitBall L)
        (hyperboloidProject x) := by
  apply Subtype.ext
  rw [ballHomeomorph_val]
  change hyperboloidProjectRaw (lorentzHyperboloidMap (lorentzSpatialGroup L) x).val=
    L (hyperboloidProjectRaw x.val)
  rw [lorentzSpatialGroup_apply_val,hyperboloidProjectRaw,hyperboloidProjectRaw,L.map_smul]

theorem pureTranslation_preservesOrientation [NeZero n] (a : unitBallDomain n) :
    Inversive.PreservesOrientation (Inversive.pureTranslation a) := by
  by_cases ha : a.val=0
  · rw [Inversive.pureTranslation,dite_eq_left ha]
    exact (Inversive.orientationPreservingMobiusGroup n).one_mem.2
  · apply (Inversive.generalMobius_preservesOrientation_iff_even_word
      (Inversive.pureTranslation_mem_generalMobiusGroup a)).mpr
    refine ⟨[Inversive.planeReflectionHomeomorph a.val 0 ha,Inversive.pureTranslationSphere a ha],?_,?_,?_⟩
    · intro f hf
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl | rfl
      · exact Inversive.planeReflection_isReflection a.val 0 ha
      · exact Inversive.pureTranslationSphere_isReflection a ha
    · simp [Inversive.pureTranslation,ha]
    · norm_num

theorem cartanLinearExtension_preservesOrientation_iff_det
    (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) :
    Inversive.PreservesOrientation (Inversive.cartanLinearExtensionHom L) ↔ 0<LinearMap.det L.toLinearMap := by
  have he : Inversive.finiteEuclideanPart (Inversive.cartanLinearExtensionHom L)=(L : Inversive.Euclidean n →
    Inversive.Euclidean n) := by
    funext x
    simp [Inversive.finiteEuclideanPart,Inversive.cartanLinearExtensionHom_coe]
  have hd (x : Inversive.Euclidean n) :
      HasFDerivAt (Inversive.finiteEuclideanPart (Inversive.cartanLinearExtensionHom L))
        (L : Inversive.Euclidean n →L[ℝ] Inversive.Euclidean n) x := by
    rw [he]
    exact (L : Inversive.Euclidean n →L[ℝ] Inversive.Euclidean n).hasFDerivAt
  have hdet : (L : Inversive.Euclidean n →L[ℝ] Inversive.Euclidean n).toLinearMap=L.toLinearMap := by
    ext x
    rfl
  constructor
  · intro h
    have hz:=h 0 (by rw [Inversive.cartanLinearExtensionHom_coe]; exact OnePoint.coe_ne_infty _)
    simpa only [(hd 0).fderiv,hdet] using hz.2
  · intro h x _
    refine ⟨⟨L,hd x,L.toLinearIsometry.isConformalMap⟩,?_⟩
    simpa only [(hd x).fderiv,hdet] using h

theorem lorentzSpatialGroup_mem_special_iff_det (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) :
    (lorentzSpatialGroup L).val∈lorentzSpecialPositiveOrthogonalGroup n ↔
      LinearMap.det L.toLinearMap=1 := by
  rw [mem_lorentzSpecialPositiveOrthogonalGroup]
  have h:=(mem_lorentzPositiveOrthogonalGroup (lorentzSpatialGroup L).val).mp
    (lorentzSpatialGroup L).property
  simp only [h.1,h.2,lorentzSpatialGroup_det,true_and,and_true]

theorem lorentzSpatialGroup_mem_special_iff_preservesOrientation
    (L : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) :
    (lorentzSpatialGroup L).val∈lorentzSpecialPositiveOrthogonalGroup n ↔
      Inversive.PreservesOrientation (Inversive.cartanLinearExtensionHom L) := by
  rw [lorentzSpatialGroup_mem_special_iff_det,cartanLinearExtension_preservesOrientation_iff_det]
  have h:=lorentzOrthogonal_det_eq_one_or_neg_one
    ((mem_lorentzPositiveOrthogonalGroup (lorentzSpatialGroup L).val).mp
      (lorentzSpatialGroup L).property).1
  rw [lorentzSpatialGroup_det] at h
  rcases h with h | h <;> rw [h] <;> norm_num

end LowDimensionalTopology.Geometry.Hyperbolic
