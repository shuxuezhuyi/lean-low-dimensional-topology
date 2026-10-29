module

public import LowDimensionalTopology.Geometry.Quasiconformal.AnalyticGeometric

/-!
# Conformal changes of solutions of a Beltrami equation

Conformal postcomposition preserves the actual almost-everywhere complex
dilatation. Conversely, two quasiconformal maps with the same coefficient have
an actual conformal relative map between their possibly different target domains.
Neither assertion assumes the desired conformal factor as part of the solution.

The analytic existence and similarity proofs reused here are due to Wu Xiaobin,
from commit 1c0d5473c020b66ed5106331a38a61536760b9b2. Their provenance and
license are preserved with the fixed external source.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Conformal postcomposition retains both K and the literal a.e. coefficient. -/
theorem conformal_postcompose_preserves_dilatation
    {f h : ℂ → ℂ} {D E : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K)
    (hh : LiZhongQC.IsConformalOnto h (f '' D) E) :
    LiZhongQC.IsKQC (h ∘ f) D K ∧
      LiZhongQC.complexDilatation (h ∘ f) =ᵐ[volume.restrict D]
        LiZhongQC.complexDilatation f := by
  refine ⟨quasiconformal_conformal_postcompose hf hh, ?_⟩
  have hU : IsOpen (f '' D) := LiZhongQC.isOpen_image_of_isKQC hf
  filter_upwards [LiZhongQC.thm9_3_differentiable_ae hf,
    ae_restrict_mem hf.1.measurableSet] with z hfz hz
  have hzf : f z ∈ f '' D := mem_image_of_mem f hz
  have hhz : DifferentiableAt ℂ h (f z) := hh.1.differentiableAt (hU.mem_nhds hzf)
  have hder : deriv h (f z) ≠ 0 :=
    LiZhongQC.deriv_ne_zero_of_injOn hU hh.1 hh.2.1 hzf
  exact LiZhongQC.complexDilatation_comp_conformal_left hfz hhz hder

/-- Equal actual complex coefficients imply conformality of the actual relative
map, without requiring equal image domains or equal distortion constants. -/
theorem equal_dilatation_relative_conformal
    {f g : ℂ → ℂ} {D : Set ℂ} {K L : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hg : LiZhongQC.IsKQC g D L)
    (hcoeff : LiZhongQC.complexDilatation f =ᵐ[volume.restrict D]
      LiZhongQC.complexDilatation g) :
    LiZhongQC.IsConformalOnto (g ∘ Function.invFunOn f D) (f '' D) (g '' D) := by
  obtain ⟨hμ, hfsol⟩ := LiZhongQC.thm10_2_genHomeoSolution_of_isKQC hf
  have hgsol : LiZhongQC.IsGenHomeoSolution g (LiZhongQC.complexDilatation f) D 2 :=
    LiZhongQC.nxS_genHomeoSolution_congr
      (LiZhongQC.thm10_2_genHomeoSolution_of_isKQC hg).2
      (Filter.EventuallyEq.symm hcoeff)
  have hK : 1 ≤ K := hf.2.1
  have hk : (K - 1) / (K + 1) < 1 := by
    apply (div_lt_one (by linarith : 0 < K + 1)).mpr
    linarith
  have hleft : LeftInvOn (Function.invFunOn f D) f D :=
    hf.2.2.1.2.1.leftInvOn_invFunOn
  refine ⟨LiZhongQC.similarity_comp_inv_holomorphic hf.1 hk hμ hfsol hgsol.2, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ hzw
    simp only [Function.comp_apply, hleft hz, hleft hw] at hzw
    exact congrArg f (hg.2.2.1.2.1 hz hw hzw)
  · calc
      (g ∘ Function.invFunOn f D) '' (f '' D) =
          g '' (Function.invFunOn f D '' (f '' D)) :=
            (Set.image_image g (Function.invFunOn f D) (f '' D)).symm
      _ = g '' D := by rw [hleft.image_image]

/-- Two quasiconformal solutions for the same measurable coefficient differ by
an actual conformal map of their image domains. -/
theorem common_beltrami_coefficient_relative_conformal
    {f g μ : ℂ → ℂ} {D : Set ℂ} {K L : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hg : LiZhongQC.IsKQC g D L)
    (hfμ : LiZhongQC.complexDilatation f =ᵐ[volume.restrict D] μ)
    (hgμ : LiZhongQC.complexDilatation g =ᵐ[volume.restrict D] μ) :
    LiZhongQC.IsConformalOnto (g ∘ Function.invFunOn f D) (f '' D) (g '' D) :=
  equal_dilatation_relative_conformal hf hg
    (Filter.EventuallyEq.trans hfμ (Filter.EventuallyEq.symm hgμ))

end LowDimensionalTopology.Geometry.Quasiconformal
