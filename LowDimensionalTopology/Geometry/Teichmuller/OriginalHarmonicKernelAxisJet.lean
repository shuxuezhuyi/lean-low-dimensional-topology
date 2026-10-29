module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonHarmonicVariations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The first real parameter jet of the actual harmonic deformation kernel -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami HarmonicFirstVariation LiZhongQC

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : IsFuchsian Γ)

local notation "q" => nativeWeilPeterssonHarmonicFrame R hp hg hgenus hΓ
local notation "K" => nativeWeilPeterssonDeformationKernel R hp hg hgenus hΓ

/-- The full real jet of the same normalized-map kernel along an actual
harmonic coordinate axis, with both upper-half-plane arguments retained. -/
theorem nativeWeilPeterssonDeformationKernel_axis_firstJet
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (l : Fin (3 * g - 3)) :
    let ψ := Classical.choose (hjets X R Γ p hp (q l))
    ∀ z ζ : ℍ,
      DifferentiableAt ℝ
        (fun s : ℂ => K (Pi.single l s) (z : ℂ) (conj (ζ : ℂ))) 0 ∧
      ∀ a : ℂ,
        fderiv ℝ
          (fun s : ℂ => K (Pi.single l s) (z : ℂ) (conj (ζ : ℂ))) 0 a =
          (eichlerDzJet ψ z a + conj (eichlerDzJet ψ ζ a)) /
              ((z : ℂ) - conj (ζ : ℂ)) ^ 2 -
            2 * (eichlerPointJet ψ z a - conj (eichlerPointJet ψ ζ a)) /
              ((z : ℂ) - conj (ζ : ℂ)) ^ 3 := by
  classical
  dsimp only
  intro z ζ
  obtain ⟨_, _, _, _, _, _, ⟨ε, hε, hC1⟩, hψ⟩ :=
    Classical.choose_spec (hjets X R Γ p hp (q l))
  let μ := NativeHarmonicBeltrami.ofQuadratic R p hp (q l)
  have hraw : IsBeltramiCoeff (harmonicPlane R p (q l)) upperHalf ‖μ.val‖ := by
    have hμ := planeRepresentative_isBeltramiCoeff μ.val
    have hae : planeRepresentative μ.val =ᵐ[volume.restrict upperHalf]
        harmonicPlane R p (q l) :=
      NativeHarmonicBeltrami.planeRepresentative_ofQuadratic_ae R p hp (q l)
    refine ⟨hμ.1.congr hae, ?_⟩
    filter_upwards [hae, hμ.2] with w hw hb
    rwa [← hw]
  have hsmall : ∀ᶠ s : ℂ in 𝓝 0, ‖s‖ * ‖μ.val‖ < 1 :=
    (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).mem_nhds (by simp)
  have hspatial : ∀ᶠ s : ℂ in 𝓝 0, ‖s‖ < ε :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hε)
  have hreflect : ∀ᶠ s : ℂ in 𝓝 0,
      K (Pi.single l s) (z : ℂ) (conj (ζ : ℂ)) =
        dz (canonicalFamily R p (q l) s) z *
            conj (dz (canonicalFamily R p (q l) s) ζ) *
          ((canonicalFamily R p (q l) s z -
            conj (canonicalFamily R p (q l) s ζ)) ^ 2)⁻¹ := by
    filter_upwards [hsmall, hspatial] with s hs hsε
    have hcoeff : IsBeltramiCoeff
        (fun w => s * harmonicPlane R p (q l) w) upperHalf (‖s‖ * ‖μ.val‖) := by
      refine ⟨hraw.1.const_mul s, ?_⟩
      filter_upwards [hraw.2] with w hw
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left hw (norm_nonneg s)
    have hsym : ∀ w, canonicalFamily R p (q l) s (conj w) =
        conj (canonicalFamily R p (q l) s w) :=
      (fMuSym_upperHalf
        (mul_nonneg (norm_nonneg s) (norm_nonneg μ.val)) hs hcoeff).2.2.1
    have hd : DifferentiableAt ℝ (canonicalFamily R p (q l) s) (ζ : ℂ) :=
      ((hC1 s hsε).differentiableOn_one ζ ζ.im_pos).differentiableAt
        (isOpen_upperHalf.mem_nhds ζ.im_pos)
    have hd' : DifferentiableAt ℝ (canonicalFamily R p (q l) s)
        (conj (conj (ζ : ℂ))) := by simpa only [Complex.conj_conj] using hd
    have hfun : (fun w => conj (canonicalFamily R p (q l) s (conj w))) =
        canonicalFamily R p (q l) s := by
      funext w
      rw [hsym, Complex.conj_conj]
    have hdz := (abR_x_dz_dzbar_conj hd').2.1
    rw [hfun, Complex.conj_conj] at hdz
    simp only [nativeWeilPeterssonDeformationKernel, coordinateFamily_axis,
      hsym, hdz, div_eq_mul_inv]
  obtain ⟨hpz, hdz, _⟩ := hψ z
  obtain ⟨hpζ, hdζ, _⟩ := hψ ζ
  have hcp := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp 0 hpζ
  have hcd := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp 0 hdζ
  have hv (w : ℍ) : canonicalFamily R p (q l) 0 w = (w : ℂ) :=
    congrFun (canonicalFamily_zero R p (q l)) w
  have hz (w : ℍ) : dz (canonicalFamily R p (q l) 0) w = 1 := by
    rw [canonicalFamily_zero R p (q l)]
    norm_num [dz, fderiv_id]
  have hc : (z : ℂ) - conj (ζ : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im (sub_eq_zero.mp h)
    simp only [Complex.conj_im, UpperHalfPlane.coe_im] at hi
    linarith [z.im_pos, ζ.im_pos]
  have hden := (hpz.sub hcp).pow 2
  have hden0 : (canonicalFamily R p (q l) 0 z -
      conj (canonicalFamily R p (q l) 0 ζ)) ^ 2 ≠ 0 := by
    rw [hv, hv]
    exact pow_ne_zero 2 hc
  have hinv := (hasFDerivAt_inv' (𝕜 := ℝ) hden0).comp 0 hden
  have hprod := (hdz.mul hcd).mul hinv
  have hactual := hprod.congr_of_eventuallyEq hreflect
  refine ⟨hactual.differentiableAt, fun a => ?_⟩
  rw [hactual.fderiv]
  simp [hv, hz, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
    smul_eq_mul, nsmul_eq_mul, div_eq_mul_inv];
    field_simp [hc]; ring

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
