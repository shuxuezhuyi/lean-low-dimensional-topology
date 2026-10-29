module

public import LowDimensionalTopology.External.LiZhongQC.Lemmas.DEDescent
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Real smoothness of the actual Douady–Earle representative

The forward regularity here is derived from the real-analytic disk extension.
The inverse uses the actual homeomorphism inverse and the nondegenerate
Wirtinger differential. No boundary differentiability or smoothing hypothesis
is assumed.

This draft targets the fixed QC migration whose namespace remains `LiZhongQC`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Complex
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open LiZhongQC

/-- The half-plane map specified by the actual Cayley conjugate of the
Douady–Earle extension is real smooth in its original planar coordinates. -/
theorem de_upper_contDiffOn (φ : Circle → Circle)
    (hφ : Function.Bijective φ) (hφc : Continuous φ)
    (E : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hE : ∀ τ : UpperHalfPlane, cayley (E τ) = extension φ (cayley τ)) :
    ContDiffOn ℝ ∞ (liftToC E) upperHalf := by
  have hC : ContDiffOn ℝ ∞ cayley upperHalf := by
    have h : ContDiffOn ℂ ∞ (fun z : ℂ => (z - I) / (z + I)) upperHalf :=
      (contDiffOn_id.sub contDiffOn_const).div
        (contDiffOn_id.add contDiffOn_const)
        (fun z hz => cayley_den_ne_zero hz)
    exact h.restrict_scalars ℝ
  have hI : ContDiffOn ℝ ∞ cayleyInv (Metric.ball (0 : ℂ) 1) := by
    have h : ContDiffOn ℂ ∞ (fun w : ℂ => I * (1 + w) / (1 - w))
        (Metric.ball (0 : ℂ) 1) :=
      (contDiffOn_const.mul (contDiffOn_const.add contDiffOn_id)).div
        (contDiffOn_const.sub contDiffOn_id)
        (fun w hw => cayleyInv_den_ne_zero (mem_ball_zero_iff.mp hw))
    exact h.restrict_scalars ℝ
  have hΦ : ContDiffOn ℝ ∞ (extension φ) (Metric.ball (0 : ℂ) 1) :=
    (extension_analyticOn_disk φ hφ hφc).contDiffOn (n := ∞)
      Metric.isOpen_ball.uniqueDiffOn
  have hmC : MapsTo cayley upperHalf (Metric.ball (0 : ℂ) 1) :=
    fun z hz => cayley_mem_unitDisc hz
  have hmΦ : MapsTo (extension φ) (Metric.ball (0 : ℂ) 1)
      (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    exact mem_ball_zero_iff.mpr
      (extension_mem_disk φ hφ hφc w (mem_ball_zero_iff.mp hw))
  have hG : ContDiffOn ℝ ∞
      (fun z : ℂ => cayleyInv (extension φ (cayley z))) upperHalf :=
    hI.comp (hΦ.comp hC hmC) (hmΦ.comp hmC)
  refine hG.congr ?_
  intro z hz
  rw [h23l_liftToC_eq E hz]
  have hz' : 0 < z.im := hz
  have hcoe : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  calc
    (E (UpperHalfPlane.ofComplex z) : ℂ) =
        cayleyInv (cayley (E (UpperHalfPlane.ofComplex z))) :=
      (cayleyInv_cayley (E (UpperHalfPlane.ofComplex z)).coe_im_pos).symm
    _ = cayleyInv (extension φ (cayley z)) := by rw [hE, hcoe]

/-- Inverse calculus on the actual half-plane. This helper is applied only to
forward regularity just proved from the real-analytic DE formula. -/
private theorem upper_homeomorph_symm_contDiffOn
    (E : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hE : ContDiffOn ℝ ∞ (liftToC E) upperHalf)
    (hj : ∀ z ∈ upperHalf, ‖dzbar (liftToC E) z‖ < ‖dz (liftToC E) z‖) :
    ContDiffOn ℝ ∞ (liftToC E.symm) upperHalf := by
  intro z hz
  set x : ℂ := liftToC E.symm z with hxdef
  have hx : x ∈ upperHalf := by
    rw [hxdef, h23l_liftToC_eq E.symm hz]
    exact (E.symm (UpperHalfPlane.ofComplex z)).coe_im_pos
  have hEx : liftToC E x = z := by
    have hz' : 0 < z.im := hz
    rw [hxdef, h23l_liftToC_eq E.symm hz, h23l_liftToC_coe,
      Homeomorph.apply_symm_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  have hf : ContDiffAt ℝ ∞ (liftToC E) x :=
    hE.contDiffAt (isOpen_upperHalf.mem_nhds hx)
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hne :
      ‖(fderiv ℝ (liftToC E) x) 1 + I * (fderiv ℝ (liftToC E) x) I‖ ≠
        ‖(fderiv ℝ (liftToC E) x) 1 - I * (fderiv ℝ (liftToC E) x) I‖ := by
    intro heq
    have h := hj x hx
    unfold dzbar dz at h
    rw [norm_div, norm_div, heq] at h
    exact (lt_irrefl _) h
  obtain ⟨L, hL⟩ := WirtInv.exists_equiv_of_wirtinger
    (fderiv ℝ (liftToC E) x) hne
  have hfd : HasFDerivAt (liftToC E) (L : ℂ →L[ℝ] ℂ) x := by
    rw [hL]
    exact (hf.differentiableAt hn).hasFDerivAt
  have hs : HasStrictFDerivAt (liftToC E) (L : ℂ →L[ℝ] ℂ) x :=
    hf.hasStrictFDerivAt' hfd hn
  have hleft : ∀ᶠ w in 𝓝 x, liftToC E.symm (liftToC E w) = w := by
    filter_upwards [isOpen_upperHalf.mem_nhds hx] with w hw
    have hw' : 0 < w.im := hw
    rw [h23l_liftToC_eq E hw, h23l_liftToC_coe,
      Homeomorph.symm_apply_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
  have hlocal : ContDiffAt ℝ ∞ (hf.localInverse hfd hn) (liftToC E x) :=
    hf.to_localInverse hfd hn
  have heq : liftToC E.symm =ᶠ[𝓝 (liftToC E x)] hf.localInverse hfd hn :=
    hs.localInverse_unique hleft
  have hInv : ContDiffAt ℝ ∞ (liftToC E.symm) (liftToC E x) :=
    hlocal.congr_of_eventuallyEq heq
  rw [hEx] at hInv
  exact hInv.contDiffWithinAt

/-- The actual DE half-plane representative is smooth in both directions,
with positive real Jacobian. The C1 conclusion of `s24q_de_upper` is not used
to establish C∞: the stronger regularity is derived from its DE formula. -/
theorem de_upper_exists_smooth (φ : Circle → Circle)
    (hφ : Function.Bijective φ) (hφc : Continuous φ) (hor : HasIncreasingLift φ) :
    ∃ E : UpperHalfPlane ≃ₜ UpperHalfPlane,
      (∀ τ : UpperHalfPlane, cayley (E τ) = extension φ (cayley τ)) ∧
      ContDiffOn ℝ ∞ (liftToC E) upperHalf ∧
      ContDiffOn ℝ ∞ (liftToC E.symm) upperHalf ∧
      (∀ z ∈ upperHalf, ‖dzbar (liftToC E) z‖ < ‖dz (liftToC E) z‖) := by
  obtain ⟨E, hE, _, hj⟩ := s24q_de_upper φ hφ hφc hor
  have hSmooth := de_upper_contDiffOn φ hφ hφc E hE
  exact ⟨E, hE, hSmooth, upper_homeomorph_symm_contDiffOn E hSmooth hj, hj⟩

end LowDimensionalTopology.Geometry.Teichmuller
