module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistNativeInfinitesimal
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchySeriesThirdDerivative
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# The actual upper-half-plane angular Petersson series

Real Mobius conjugation transports the proved lower-half-plane derivative
series. The same finite sums therefore have a genuine HasSum, pointwise
absolute convergence and local uniform convergence on the upper half-plane.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped Topology UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem squaredLogDeriv_mobius_conj (γ : Deck) {z : ℂ}
    (hz : z ∈ LiZhongQC.upperHalf) :
    let m := LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
    (deriv m (conj z) / m (conj z)) ^ 2 =
      conj ((deriv m z / m z) ^ 2) := by
  have hw : conj z ∈ LiZhongQC.lowerHalf := by
    change (conj z).im < 0
    rw [Complex.conj_im]
    exact neg_lt_zero.mpr hz
  have hd : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 :=
    GammaMeasurableBeltrami.denominator_ne_zero γ ⟨z, hz⟩
  have hz' := LiZhongQC.hasDerivAt_mobiusFn
    (a := (γ 0 0 : ℂ)) (b := (γ 0 1 : ℂ)) hd
  have hw' := LiZhongQC.hasDerivAt_mobiusFn
    (a := (γ 0 0 : ℂ)) (b := (γ 0 1 : ℂ)) (LiZhongQC.bg2_a_den_ne γ hw)
  rw [LiZhongQC.h23l_b_det γ] at hz' hw'
  dsimp only
  rw [hw'.deriv, hz'.deriv, LiZhongQC.b33_e_mobius_conj]
  simp only [map_pow, map_div₀, map_one, map_add, map_mul, Complex.conj_ofReal]

/-- For every genuine choice of right-coset representatives, the actual
upper-half-plane Petersson series converges absolutely and locally uniformly. -/
theorem rightCosetPeterssonSeries_upperHalf
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) [Countable Γ]
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension θ Γ s v ζ ≠ 0 → u = v) :
    let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
    let m : Γ → ℂ → ℂ := fun γ =>
      LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
    ∀ ρ : C → Γ, (∀ u : C, Quotient.mk _ (ρ u) = u) →
      (∀ z : ℂ, z ∈ LiZhongQC.upperHalf →
        HasSum (fun u : C => (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
          (∑' u : C, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2) ∧
        Summable (fun u : C => ‖(deriv (m (ρ u)) z / m (ρ u) z) ^ 2‖)) ∧
      TendstoLocallyUniformlyOn
        (fun (E : Finset C) (z : ℂ) =>
          ∑ u ∈ E, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
        (fun z => ∑' u : C, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
        (atTop : Filter (Finset C)) LiZhongQC.upperHalf := by
  let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
  let m : Γ → ℂ → ℂ := fun γ =>
    LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
  let ν := rightCosetInfinitesimalSum θ Γ s
  let k : ℂ := Complex.I / (2 * (Real.pi : ℂ))
  dsimp only
  intro ρ hρ
  let term : C → ℂ → ℂ := fun u z => (deriv (m (ρ u)) z / m (ρ u) z) ^ 2
  let F₃ := iteratedDeriv 3 (LiZhongQC.ahVar ν)
  let L : ℂ → ℂ := fun z => conj (k⁻¹ * F₃ (conj z))
  have hk : k ≠ 0 := div_ne_zero Complex.I_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hmap : MapsTo conj LiZhongQC.upperHalf LiZhongQC.lowerHalf := by
    intro z hz
    change (conj z).im < 0
    rw [Complex.conj_im]
    exact neg_lt_zero.mpr hz
  have hterm (u : C) {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
      term u (conj z) = conj (term u z) :=
    squaredLogDeriv_mobius_conj (ρ u).val hz
  obtain ⟨hlocal, hpoint⟩ :=
    (rightCosetCauchySeries_thirdDerivative θ Γ s hsep).2 ρ hρ
  have hsum (z : ℂ) (hz : z ∈ LiZhongQC.upperHalf) :
      HasSum (fun u : C => term u z) (L z) := by
    have hlo : HasSum (fun u : C => k⁻¹ * (k * term u (conj z)))
        (k⁻¹ * F₃ (conj z)) :=
      (hpoint (conj z) (hmap hz)).1.mul_left k⁻¹
    have hlo' : HasSum (fun u : C => term u (conj z)) (k⁻¹ * F₃ (conj z)) :=
      hlo.congr_fun (fun u => (inv_mul_cancel_left₀ hk (term u (conj z))).symm)
    have hconj : HasSum (fun u : C => conj (term u (conj z))) (L z) :=
      Complex.hasSum_conj'.2 hlo'
    exact hconj.congr_fun (fun u =>
      ((congrArg conj (hterm u hz)).trans (Complex.conj_conj (term u z))).symm)
  have hg : UniformContinuous (fun w : ℂ => conj (k⁻¹ * w)) :=
    Complex.isometry_conj.uniformContinuous.comp (uniformContinuous_mul_left' k⁻¹)
  have hupper : TendstoLocallyUniformlyOn
      (fun (E : Finset C) (z : ℂ) => ∑ u ∈ E, term u z) L
      (atTop : Filter (Finset C)) LiZhongQC.upperHalf := by
    have hpre := hlocal.comp conj hmap Complex.continuous_conj.continuousOn
    have hpost := hg.comp_tendstoLocallyUniformlyOn hpre
    refine hpost.congr ?_
    intro E z hz
    change conj (k⁻¹ * (k * ∑ u ∈ E, term u (conj z))) = ∑ u ∈ E, term u z
    rw [inv_mul_cancel_left₀ hk]
    simp only [map_sum]
    exact Finset.sum_congr rfl (fun u _hu => by rw [hterm u hz, Complex.conj_conj])
  refine ⟨?_, hupper.congr_right ?_⟩
  · intro z hz
    exact ⟨(hsum z hz).summable.hasSum, (hsum z hz).summable.norm⟩
  · intro z hz
    exact (hsum z hz).tsum_eq.symm

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
