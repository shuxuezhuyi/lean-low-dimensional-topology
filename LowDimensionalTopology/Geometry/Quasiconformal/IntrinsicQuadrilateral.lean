module

public import LowDimensionalTopology.Geometry.Quasiconformal.QuadrilateralModules
public import LowDimensionalTopology.Unproved.Quasiconformal.JordanBoundaryOrderComparison

/-!
# Intrinsic quadrilateral models and quasiconformality under boundary order

Existing actual Jordan uniformization and boundary extension reduce the
presentation comparison to the explicitly named unproved order theorem.
All subsequent statements retain that concrete hypothesis in their signatures.
-/

@[expose] public section
noncomputable section

open Set Metric MeasureTheory
open scoped Topology OnePoint

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The same raw rectangle-ratio supremum, before choosing any presentation. -/
def intrinsicQuadrilateralModulus (Q : IntrinsicQuadrilateral) : ℝ :=
  LiZhongQC.quadModulusOf Q.dom Q.vert

/-- The geometric modulus condition quantified over every intrinsic Jordan quad. -/
def IsIntrinsicallyKQuasiconformal (f : ℂ → ℂ) (D : Set ℂ) (K : ℝ) : Prop :=
  IsOpen D ∧ 1 ≤ K ∧ LiZhongQC.IsHomeomorphOnto f D (f '' D) ∧
    ∀ Q : IntrinsicQuadrilateral, closure (LiZhongQC.toExt Q.dom) ⊆ LiZhongQC.toExt D →
      ∃ Q' : IntrinsicQuadrilateral, Q.IsImageUnder Q' f ∧
        intrinsicQuadrilateralModulus Q' ≤ K * intrinsicQuadrilateralModulus Q

/-- Existing analytic existence results reduce the full presentation comparison
to the concrete boundary-order theorem, without assuming a rectangle model. -/
theorem intrinsicQuadrilateral_iff_presented
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    {D : Set ℂ} {v : Fin 4 → LiZhongQC.ExtPlane} (hb : Bornology.IsBounded D) :
    IsIntrinsicQuadrilateral D v ↔ LiZhongQC.IsTopQuad D v := by
  constructor
  · rintro ⟨hD, _, hv, hpos⟩
    obtain ⟨φ, hφ, Φ, hΦ⟩ := LiZhongQC.uq_exists_uniformizer hD
    obtain ⟨ψ, Ψ, x, hψ, hΨ, hx⟩ :=
      LiZhongQC.exists_uniformizer_finite_vertices hD.1 hφ hΦ hv
    exact ⟨hD, hv, ψ, Ψ, x, hψ, hΨ,
      (hHard D v hD hb hv ψ Ψ x hψ hΨ hx).1 hpos, hx⟩
  · rintro ⟨hD, hv, φ, Φ, x, hφ, hΦ, hx, hvx⟩
    exact ⟨hD, hb, hv, (hHard D v hD hb hv φ Φ x hφ hΦ hvx).2 hx⟩

/-- The existing rectangular-model proof applies to every intrinsic quad once
the independent boundary-order comparison has been established. -/
theorem intrinsic_quadrilateral_rectangular_model
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    (Q : IntrinsicQuadrilateral) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∃ (f : ℂ → ℂ) (F : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane),
        LiZhongQC.IsConformalOnto f Q.dom (LiZhongQC.rectangle a b) ∧
          LiZhongQC.IsHomeoExtension f Q.dom (LiZhongQC.rectangle a b) F ∧
            ∀ i, F (Q.vert i) = LiZhongQC.rectVert a b i := by
  let P : LiZhongQC.TopQuad := ⟨Q.dom, Q.vert,
    (intrinsicQuadrilateral_iff_presented hHard Q.isIntrinsic.2.1).1 Q.isIntrinsic⟩
  exact quadrilateral_rectangular_model P

/-- The raw modulus is positive on every actual intrinsic quadrilateral. -/
theorem intrinsicQuadrilateralModulus_pos
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    (Q : IntrinsicQuadrilateral) : 0 < intrinsicQuadrilateralModulus Q := by
  let P : LiZhongQC.TopQuad := ⟨Q.dom, Q.vert,
    (intrinsicQuadrilateral_iff_presented hHard Q.isIntrinsic.2.1).1 Q.isIntrinsic⟩
  exact quadrilateralModulus_pos P

/-- Every tested quadrilateral has compact planar closure, hence is bounded. -/
theorem isBounded_of_quad_closure_subset {U D : Set ℂ}
    (hU : closure (LiZhongQC.toExt U) ⊆ LiZhongQC.toExt D) :
    Bornology.IsBounded U := by
  apply LiZhongQC.isBounded_of_extInf_notMem_closure_toExt
  intro h
  obtain ⟨z, _, hz⟩ := hU h
  exact OnePoint.coe_ne_infty z hz

/-- Intrinsic geometric quasiconformality implies the presented-quad condition. -/
theorem intrinsic_quasiconformal_to_presented
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : IsIntrinsicallyKQuasiconformal f D K) : LiZhongQC.IsKQC f D K := by
  refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
  intro Q hQ
  have hQi : IsIntrinsicQuadrilateral Q.dom Q.vert :=
    (intrinsicQuadrilateral_iff_presented hHard (isBounded_of_quad_closure_subset hQ)).2
      Q.isTopQuad
  let P : IntrinsicQuadrilateral := ⟨Q.dom, Q.vert, hQi⟩
  obtain ⟨P', hP', hbound⟩ := hf.2.2.2 P hQ
  let Q' : LiZhongQC.TopQuad := ⟨P'.dom, P'.vert,
    (intrinsicQuadrilateral_iff_presented hHard P'.isIntrinsic.2.1).1 P'.isIntrinsic⟩
  exact ⟨Q', hP', hbound⟩

/-- The converse uses the full intrinsic presentation comparison on every test
and on its actual image, preserving precisely the original distortion constant. -/
theorem presented_quasiconformal_to_intrinsic
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : LiZhongQC.IsKQC f D K) :
    IsIntrinsicallyKQuasiconformal f D K := by
  refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
  intro P hP
  let Q : LiZhongQC.TopQuad := ⟨P.dom, P.vert,
    (intrinsicQuadrilateral_iff_presented hHard P.isIntrinsic.2.1).1 P.isIntrinsic⟩
  obtain ⟨Q', hQ', hbound⟩ := hf.2.2.2 Q hP
  have hQ'closure : closure (LiZhongQC.toExt Q'.dom) ⊆ LiZhongQC.toExt (f '' D) := by
    rw [hQ'.1]
    exact LiZhongQC.closure_toExt_image_subset hf.2.2.1.1 hP subset_rfl
  let P' : IntrinsicQuadrilateral := ⟨Q'.dom, Q'.vert,
    (intrinsicQuadrilateral_iff_presented hHard
      (isBounded_of_quad_closure_subset hQ'closure)).2 Q'.isTopQuad⟩
  exact ⟨P', hQ', hbound⟩

/-- The actual intrinsic geometric and analytic conditions are equivalent once
the explicit boundary-order theorem is supplied. -/
theorem intrinsic_geometric_iff_analytic
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} :
    IsIntrinsicallyKQuasiconformal f D K ↔ IsAnalyticallyKQuasiconformal f D K :=
  ⟨fun hf => geometric_iff_analytic.mp (intrinsic_quasiconformal_to_presented hHard hf),
    fun hf => presented_quasiconformal_to_intrinsic hHard (geometric_iff_analytic.mpr hf)⟩

/-- The actual intrinsic geometric condition implies ACL regularity. -/
theorem intrinsic_geometric_quasiconformal_isACL
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : IsIntrinsicallyKQuasiconformal f D K) : LiZhongQC.IsACL f D :=
  geometric_quasiconformal_isACL (intrinsic_quasiconformal_to_presented hHard hf)

/-- The actual intrinsic geometric condition implies the exact a.e. derivative bound. -/
theorem intrinsic_geometric_quasiconformal_derivative_inequality
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : IsIntrinsicallyKQuasiconformal f D K) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict D),
      ‖LiZhongQC.dz f z‖ + ‖LiZhongQC.dzbar f z‖ ≤
        K * (‖LiZhongQC.dz f z‖ - ‖LiZhongQC.dzbar f z‖) :=
  geometric_quasiconformal_derivative_inequality
    (intrinsic_quasiconformal_to_presented hHard hf)

end LowDimensionalTopology.Geometry.Quasiconformal
