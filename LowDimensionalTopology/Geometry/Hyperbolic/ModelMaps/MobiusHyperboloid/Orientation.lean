/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.UnitBall.Subgroup
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.SpatialIsometry
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.MobiusHyperboloid.Topology
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareExtensionOrientation

/-!
# Lorentz determinants and Mobius orientation

Original proof of the orientation clause. The canonical
multiplicative matrix uses the inverse of its row-action matrix. The actual
finite-chart Jacobian criterion agrees with membership in SO+(1,n+1).
-/

@[expose] public section
noncomputable section
open Set Matrix
open scoped MatrixGroups RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n : ℕ}

theorem lorentzPositive_det_inv (A : lorentzPositiveOrthogonalGroup n) :
    (A⁻¹).val.val.det=A.val.val.det := by
  have h : (A⁻¹).val.val.det*A.val.val.det=1 := by
    rw [← Matrix.det_mul]
    change (A.val⁻¹.val*A.val.val).det=1
    rw [A.val.inv_mul,Matrix.det_one]
  rcases lorentzOrthogonal_det_eq_one_or_neg_one
    ((mem_lorentzPositiveOrthogonalGroup A.val).mp A.property).1 with he | he
  · rw [he] at h ⊢
    linarith
  · rw [he] at h ⊢
    linarith

theorem lorentzPositive_mem_special_iff_det (A : lorentzPositiveOrthogonalGroup n) :
    A.val∈lorentzSpecialPositiveOrthogonalGroup n ↔ A.val.val.det=1 := by
  rw [mem_lorentzSpecialPositiveOrthogonalGroup]
  have h:=(mem_lorentzPositiveOrthogonalGroup A.val).mp A.property
  simp only [h.1,h.2,true_and,and_true]

section BoundaryTopology
variable [NeZero n]
attribute [local instance] Inversive.pureTranslationBoundaryChordalMetric Inversive.pureTranslationBoundaryMobiusMetric
  Inversive.pureTranslationBallMobiusMetric Inversive.pureTranslationBallPseudoMetric
  Inversive.pureTranslationBallPseudoEMetric
  Inversive.pureTranslationBallDist Inversive.pureTranslationBallEDist Inversive.pureTranslationBallUniform
  Inversive.pureTranslationBallTopology

omit [NeZero n] in
theorem pureTranslationBall_origin :
    Inversive.pureTranslationBall (ballOrigin (n+1))=(1 : Inversive.ballPreservingSubgroup n) := by
  apply Subtype.ext
  apply Subtype.ext
  exact Inversive.pureTranslation_origin (n+1)

theorem ballMobiusLorentzMatrix_det_continuous :
    Continuous (fun f : Inversive.ballPreservingSubgroup n=>(ballMobiusLorentzMatrix f).val.val.det) :=
  ballMobiusLorentzMatrix_val_continuous.matrix_det

theorem ballMobiusLorentzMatrix_pureTranslation_det (a : unitBallDomain (n+1)) :
    (ballMobiusLorentzMatrix (Inversive.pureTranslationBall a)).val.val.det=1 := by
  let D : unitBallDomain (n+1) → ℝ:=
    fun a=>(ballMobiusLorentzMatrix (Inversive.pureTranslationBall a)).val.val.det
  have hc : Continuous D:=ballMobiusLorentzMatrix_det_continuous.comp Inversive.pureTranslationBall_continuous
  have he (a : unitBallDomain (n+1)) : D a=1 ∨ D a= -1 :=
    lorentzOrthogonal_det_eq_one_or_neg_one
      ((mem_lorentzPositiveOrthogonalGroup (ballMobiusLorentzMatrix (Inversive.pureTranslationBall a)).val).mp
        (ballMobiusLorentzMatrix (Inversive.pureTranslationBall a)).property).1
  have hb : D (ballOrigin (n+1))=1 := by
    dsimp only [D]
    rw [pureTranslationBall_origin,ballMobiusLorentzMatrix_one]
    exact Matrix.det_one
  have hp : 0<D a := isPreconnected_univ.lt_of_ne hc.continuousOn
    (fun a _=>by rcases he a with h | h <;> rw [h] <;> norm_num)
    ⟨ballOrigin (n+1),mem_univ _,by rw [hb]; norm_num⟩ (mem_univ a)
  rcases he a with h | h
  · exact h
  · rw [h] at hp
    norm_num at hp

omit [NeZero n] in
theorem ballMobiusLorentzMatrix_orthogonal
    (L : Inversive.Euclidean (n+1) ≃ₗᵢ[ℝ] Inversive.Euclidean (n+1)) :
    ballMobiusLorentzMatrix (Inversive.orthogonalBallMap L)=(lorentzSpatialGroup L)⁻¹ := by
  apply inv_injective
  apply lorentzHyperboloidMap_injective (n+1)
  funext x
  rw [ballMobiusLorentzMatrix_spec,inv_inv]
  apply (hyperboloidBallHomeomorph (n+1)).injective
  rw [ballMobiusHyperboloidMap,Homeomorph.apply_symm_apply]
  change ballMobiusEvaluation (Inversive.orthogonalBallMap L) (hyperboloidProject x)=
    hyperboloidProject (lorentzHyperboloidMap (lorentzSpatialGroup L) x)
  rw [hyperboloidProject_lorentzSpatialGroup]
  apply Subtype.ext
  apply OnePoint.coe_injective
  rw [ballMobiusEvaluation_coe,ballHomeomorph_coe,Inversive.orthogonalBallMap_coe]

omit [NeZero n] in
theorem ballMobiusLorentzMatrix_orthogonal_det
    (L : Inversive.Euclidean (n+1) ≃ₗᵢ[ℝ] Inversive.Euclidean (n+1)) :
    (ballMobiusLorentzMatrix (Inversive.orthogonalBallMap L)).val.val.det=LinearMap.det L.toLinearMap := by
  rw [ballMobiusLorentzMatrix_orthogonal,lorentzPositive_det_inv,lorentzSpatialGroup_det]

theorem ballMobiusLorentzMatrix_decomposition_det
    (p : (Inversive.Euclidean (n+1) ≃ₗᵢ[ℝ] Inversive.Euclidean (n+1)) × unitBallDomain (n+1)) :
    (ballMobiusLorentzMatrix (Inversive.orthogonalPureTranslationMap p)).val.val.det=
      LinearMap.det p.1.toLinearMap := by
  rw [Inversive.orthogonalPureTranslationMap_mul,ballMobiusLorentzMatrix_mul]
  change ((ballMobiusLorentzMatrix (Inversive.orthogonalBallMap p.1)).val.val *
    (ballMobiusLorentzMatrix (Inversive.pureTranslationBall p.2)).val.val).det=_
  rw [Matrix.det_mul,ballMobiusLorentzMatrix_orthogonal_det,
    ballMobiusLorentzMatrix_pureTranslation_det,mul_one]

omit [NeZero n] in
theorem orthogonalPureTranslationMap_preservesOrientation_iff
    (p : (Inversive.Euclidean (n+1) ≃ₗᵢ[ℝ] Inversive.Euclidean (n+1)) × unitBallDomain (n+1)) :
    Inversive.PreservesOrientation (Inversive.orthogonalPureTranslationMap p).val.val ↔
      Inversive.PreservesOrientation (Inversive.cartanLinearExtensionHom p.1) := by
  have hT : Inversive.pureTranslation p.2∈Inversive.orientationPreservingMobiusGroup (n+1):=
    ⟨Inversive.pureTranslation_mem_generalMobiusGroup p.2,pureTranslation_preservesOrientation p.2⟩
  have hL : Inversive.cartanLinearExtensionHom p.1∈Inversive.generalMobiusGroup (n+1):=
    Inversive.extendedIsometry_mem_generalMobiusGroup p.1.toIsometryEquiv
  change Inversive.PreservesOrientation (Inversive.cartanLinearExtensionHom p.1*Inversive.pureTranslation p.2) ↔ _
  constructor
  · intro h
    have hm : Inversive.cartanLinearExtensionHom p.1*Inversive.pureTranslation p.2∈
        Inversive.orientationPreservingMobiusGroup (n+1):=
      ⟨(Inversive.generalMobiusGroup (n+1)).mul_mem hL hT.1,h⟩
    have hp:=(Inversive.orientationPreservingMobiusGroup (n+1)).mul_mem hm
      ((Inversive.orientationPreservingMobiusGroup (n+1)).inv_mem hT)
    simpa only [mul_assoc,mul_inv_cancel,mul_one] using hp.2
  · intro h
    exact ((Inversive.orientationPreservingMobiusGroup (n+1)).mul_mem ⟨hL,h⟩ hT).2

theorem ballMobiusLorentzMatrix_mem_special_iff_preservesOrientation
    (f : Inversive.ballPreservingSubgroup n) :
    (ballMobiusLorentzMatrix f).val∈lorentzSpecialPositiveOrthogonalGroup (n+1) ↔
      Inversive.PreservesOrientation f.val.val := by
  obtain ⟨p,rfl⟩:=(Inversive.orthogonalPureTranslationEquiv n).surjective f
  change (ballMobiusLorentzMatrix (Inversive.orthogonalPureTranslationMap p)).val∈
    lorentzSpecialPositiveOrthogonalGroup (n+1) ↔
    Inversive.PreservesOrientation (Inversive.orthogonalPureTranslationMap p).val.val
  rw [lorentzPositive_mem_special_iff_det,ballMobiusLorentzMatrix_decomposition_det,
    orthogonalPureTranslationMap_preservesOrientation_iff]
  exact (lorentzSpatialGroup_mem_special_iff_det p.1).symm.trans
    (lorentzSpatialGroup_mem_special_iff_preservesOrientation p.1)

theorem cayleyPoincareLorentz_mem_special_iff_preservesOrientation (f : Inversive.GM n) :
    (ballMobiusLorentzMatrix (cayleyPoincareEquiv f)).val∈
      lorentzSpecialPositiveOrthogonalGroup (n+1) ↔
      Inversive.PreservesOrientation (f : Inversive.ExtendedHomeomorph n) :=
  (ballMobiusLorentzMatrix_mem_special_iff_preservesOrientation (cayleyPoincareEquiv f)).trans
    (cayleyPoincareEquiv_preservesOrientation_iff f)

end BoundaryTopology
end LowDimensionalTopology.Geometry.Hyperbolic
