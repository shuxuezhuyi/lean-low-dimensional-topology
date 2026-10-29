/-
The normalized-solution, symmetric-extension and Jordan-domain uniqueness
theorems used below are due to Wu Xiaobin, Li-Zhong-QC-formalization, fixed
commit 1c0d5473c020b66ed5106331a38a61536760b9b2. Apache-2.0 attribution is
retained in the external source and THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch10.S33_BersEmbedding
public import Mathlib.Tactic.FinCases

/-!
# Canonical normalized Beltrami self-maps of the upper half-plane

The maps are genuine homeomorphisms of the original upper half-plane. Their
complex dilatation is the given measurable coefficient almost everywhere, and
an actual homeomorphic extension of the compactified closure fixes zero, one
and infinity. Uniqueness compares every original quasiconformal map satisfying
these conditions, without a prescribed extra distortion bound or regularity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- A normalized Beltrami map of the upper half-plane has the actual prescribed
coefficient and a genuine homeomorphic boundary extension fixing zero, one
and infinity. Boundary normalization uses the actual continuous extension,
without an additional differentiability condition. -/
def IsNormalizedHalfPlaneBeltramiMap (μ : ℂ → ℂ)
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane) : Prop :=
  IsQuasiconformal (liftToC F) upperHalf ∧
    (complexDilatation (liftToC F) =ᵐ[volume.restrict upperHalf] μ) ∧
    ∃ E : ExtPlane → ExtPlane, IsHomeoExtension (liftToC F) upperHalf upperHalf E ∧
      E ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      E ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ E extInf = extInf

private theorem liftToC_upperHalf_image (F : UpperHalfPlane ≃ₜ UpperHalfPlane) :
    liftToC F '' upperHalf = upperHalf := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [h23l_liftToC_eq F hw]
    exact (F (UpperHalfPlane.ofComplex w)).coe_im_pos
  · intro hz
    let w := F.symm ⟨z, hz⟩
    refine ⟨(w : ℂ), w.coe_im_pos, ?_⟩
    simp only [liftToC, dite_eq_left w.coe_im_pos]
    exact congrArg UpperHalfPlane.coe (F.apply_symm_apply ⟨z, hz⟩)

/-- Every two original normalized upper-half-plane solutions for the same
coefficient are equal as actual homeomorphisms of the upper half-plane. -/
theorem normalizedHalfPlaneBeltramiMap_unique {μ : ℂ → ℂ}
    {F G : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hF : IsNormalizedHalfPlaneBeltramiMap μ F)
    (hG : IsNormalizedHalfPlaneBeltramiMap μ G) : F = G := by
  obtain ⟨hFqc, hFμ, E, hE, hE0, hE1, hEinf⟩ := hF
  obtain ⟨hGqc, hGμ, J, hJ, hJ0, hJ1, hJinf⟩ := hG
  let p : Fin 3 → ExtPlane :=
    ![((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [p] at hij ⊢
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (OnePoint.coe_injective hij)
  have hpf : ∀ i, p i ∈ frontier (toExt upperHalf) := by
    intro i
    fin_cases i
    · change ((0 : ℂ) : ExtPlane) ∈ frontier (toExt upperHalf)
      simpa only [Complex.ofReal_zero] using scExt_ofReal_mem_frontier_toExt_upperHalf 0
    · change ((1 : ℂ) : ExtPlane) ∈ frontier (toExt upperHalf)
      simpa only [Complex.ofReal_one] using scExt_ofReal_mem_frontier_toExt_upperHalf 1
    · exact scExt_infty_mem_frontier_toExt_upperHalf
  have hboundary : ∀ i, E (p i) = J (p i) := by
    intro i
    fin_cases i
    · exact hE0.trans hJ0.symm
    · exact hE1.trans hJ1.symm
    · exact hEinf.trans hJinf.symm
  have heq : EqOn (liftToC F) (liftToC G) upperHalf :=
    thm13_4_uniqueness isJordanDomain_upperHalf isJordanDomain_upperHalf
      hFqc hGqc (liftToC_upperHalf_image F) (liftToC_upperHalf_image G)
      (Filter.EventuallyEq.trans hFμ (Filter.EventuallyEq.symm hGμ)) hE hJ hp hpf hboundary
  apply Homeomorph.ext
  intro z
  apply UpperHalfPlane.ext
  simpa only [liftToC, dite_eq_left z.coe_im_pos] using heq z.coe_im_pos

/-- Every bounded measurable coefficient on the original upper half-plane has
a normalized solution, with the sharp quasiconformal bound. The uniqueness
clause ranges over every original normalized quasiconformal solution. -/
theorem normalizedHalfPlaneBeltramiMap_existsUnique
    {μ : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hμ : IsBeltramiCoeff μ upperHalf k) :
    ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane,
      IsNormalizedHalfPlaneBeltramiMap μ F ∧
      IsKQC (liftToC F) upperHalf ((1 + k) / (1 - k)) ∧
      (∀ z : UpperHalfPlane, (F z : ℂ) = fMuSym μ z) ∧
      ∀ G : UpperHalfPlane ≃ₜ UpperHalfPlane,
        IsNormalizedHalfPlaneBeltramiMap μ G → G = F := by
  obtain ⟨_hσ, hnormal, hglobal, _hglobalUnique⟩ := bg_sym_spec hk0 hk1 hμ
  obtain ⟨himage, _hreal, _hsym, hqc, hdil⟩ := fMuSym_upperHalf hk0 hk1 hμ
  obtain ⟨F, hF⟩ := b33_d_homeo_upper hglobal hnormal.2.1 himage
  have hEq : EqOn (liftToC F) (fMuSym μ) upperHalf := by
    intro z hz
    rw [h23l_liftToC_eq F hz, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    exact hF ⟨z, hz⟩
  have hFqc : IsKQC (liftToC F) upperHalf ((1 + k) / (1 - k)) :=
    ad_isKQC_congr hqc hEq
  have hFμ : complexDilatation (liftToC F) =ᵐ[volume.restrict upperHalf] μ := by
    filter_upwards [hdil, ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz hzU
    exact (abR_t_complexDilatation_congr isOpen_upperHalf hEq hzU).trans hz
  obtain ⟨e, he⟩ := t1_homeomorph hglobal hnormal.2.1
  have hEraw := s13x_de_isHomeoExtension_homeomorph e upperHalf
  rw [he, himage] at hEraw
  have hE : IsHomeoExtension (liftToC F) upperHalf upperHalf e.onePointCongr := by
    refine ⟨?_, hEraw.2⟩
    intro z hz
    exact (hEraw.1 z hz).trans
      (congrArg (fun w : ℂ => (w : ExtPlane)) (hEq hz).symm)
  have hE0 : e.onePointCongr ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) := by
    change ((e 0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane)
    rw [congrFun he 0, hnormal.2.2.1]
  have hE1 : e.onePointCongr ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
    change ((e 1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)
    rw [congrFun he 1, hnormal.2.2.2.1]
  have hFin : IsNormalizedHalfPlaneBeltramiMap μ F :=
    ⟨⟨_, hFqc⟩, hFμ, e.onePointCongr, hE, hE0, hE1, rfl⟩
  exact ⟨F, hFin, hFqc, hF, fun G hG => normalizedHalfPlaneBeltramiMap_unique hG hFin⟩

/-- Changing the actual coefficient only on a null subset of the original
upper half-plane preserves exactly the same normalized maps. -/
theorem isNormalizedHalfPlaneBeltramiMap_congr_ae {μ ν : ℂ → ℂ}
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (h : μ =ᵐ[volume.restrict upperHalf] ν) :
    IsNormalizedHalfPlaneBeltramiMap μ F ↔ IsNormalizedHalfPlaneBeltramiMap ν F := by
  constructor
  · rintro ⟨hqc, hdil, hboundary⟩
    exact ⟨hqc, Filter.EventuallyEq.trans hdil h, hboundary⟩
  · rintro ⟨hqc, hdil, hboundary⟩
    exact ⟨hqc, Filter.EventuallyEq.trans hdil (Filter.EventuallyEq.symm h), hboundary⟩

/-- The normalized actual map depends only on the original coefficient class
modulo planar measure on the upper half-plane. -/
theorem normalizedHalfPlaneBeltramiMap_unique_of_coefficients_ae {μ ν : ℂ → ℂ}
    {F G : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (h : μ =ᵐ[volume.restrict upperHalf] ν)
    (hF : IsNormalizedHalfPlaneBeltramiMap μ F)
    (hG : IsNormalizedHalfPlaneBeltramiMap ν G) : F = G :=
  normalizedHalfPlaneBeltramiMap_unique hF
    ((isNormalizedHalfPlaneBeltramiMap_congr_ae h).mpr hG)

end LowDimensionalTopology.Geometry.Quasiconformal
