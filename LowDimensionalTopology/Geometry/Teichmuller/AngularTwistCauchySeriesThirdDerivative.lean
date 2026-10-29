module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchySeriesUniform
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistBolIdentity
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The third derivative of the same actual angular integral series

The actual bounded zero-extended coefficients make each intrinsic integral
holomorphic on the lower half-plane. Local uniform convergence of the same
finite integral sums then gives local uniform convergence after three
derivatives. The accepted finite Bol identity identifies the result for
every actual choice of right-coset representatives.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

private theorem differentiableOn_rightCosetCauchyTerm_lowerHalf
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ)
    (u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))) :
    DifferentiableOn ℂ (rightCosetCauchyTerm θ Γ s u) LiZhongQC.lowerHalf := by
  refine Quotient.inductionOn u ?_
  intro γ
  change DifferentiableOn ℂ (pullbackCauchyTerm θ γ.val) LiZhongQC.lowerHalf
  let μ : ℂ → ℂ := pullbackInfinitesimalZeroExtension θ γ.val
  let B : ℝ := 1 / (4 * (θ : ℝ))
  have hB : 0 ≤ B := one_div_nonneg.mpr (mul_nonneg (by norm_num) θ.property.1.le)
  have hm : AEStronglyMeasurable μ (volume.restrict LiZhongQC.upperHalf) :=
    (measurable_pullbackInfinitesimalZeroExtension θ γ.val).aestronglyMeasurable.restrict
  have hb : ∀ᵐ ζ ∂(volume.restrict LiZhongQC.upperHalf), ‖μ ζ‖ ≤ B :=
    ae_restrict_of_ae (Eventually.of_forall (norm_pullbackInfinitesimalZeroExtension_le θ γ.val))
  have hzero : ∀ z : ℂ, z.im ≤ 0 → μ z = 0 := fun _ hz =>
    pullbackInfinitesimalZeroExtension_eq_zero_of_im_nonpos θ γ.val hz
  have he : pullbackCauchyTerm θ γ.val = fun w =>
      -(1 / (Real.pi : ℂ)) * ∫ ζ in LiZhongQC.upperHalf, μ ζ * LiZhongQC.ahKer w ζ :=
    (LiZhongQC.b36_p_normalizedCauchyT_eq_ahVar hzero).symm.trans
      (LiZhongQC.b36_p_normalizedCauchyT_eq μ)
  rw [he]
  intro z hz
  have hd := ((LiZhongQC.b36_p_hasDerivAt_N hB hm hb hz).2).const_mul
    (-(1 / (Real.pi : ℂ)))
  exact hd.differentiableAt.differentiableWithinAt

/-- The actual third-derivative series converges locally uniformly on the
lower half-plane and has the Bol expression for every actual representative choice. -/
theorem rightCosetCauchySeries_thirdDerivative
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) [Countable Γ]
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension θ Γ s v ζ ≠ 0 → u = v) :
    let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
    let ν : ℂ → ℂ := fun ζ =>
      ∑' u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ
    let m : Γ → ℂ → ℂ := fun γ =>
      LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
    TendstoLocallyUniformlyOn
      (fun (F : Finset C) (z : ℂ) =>
        ∑ u ∈ F, iteratedDeriv 3 (rightCosetCauchyTerm θ Γ s u) z)
      (iteratedDeriv 3 (LiZhongQC.ahVar ν)) (atTop : Filter (Finset C))
      LiZhongQC.lowerHalf ∧
      ∀ ρ : C → Γ, (∀ u : C, Quotient.mk _ (ρ u) = u) →
        TendstoLocallyUniformlyOn
          (fun (F : Finset C) (z : ℂ) =>
            (Complex.I / (2 * (Real.pi : ℂ))) *
              ∑ u ∈ F, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
          (iteratedDeriv 3 (LiZhongQC.ahVar ν)) (atTop : Filter (Finset C))
          LiZhongQC.lowerHalf ∧
        ∀ z : ℂ, z ∈ LiZhongQC.lowerHalf →
          HasSum (fun u : C => (Complex.I / (2 * (Real.pi : ℂ))) *
            (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
            (iteratedDeriv 3 (LiZhongQC.ahVar ν) z) ∧
          iteratedDeriv 3 (LiZhongQC.ahVar ν) z =
            (Complex.I / (2 * (Real.pi : ℂ))) *
              ∑' u : C, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2 := by
  let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
  let ν : ℂ → ℂ := fun ζ =>
    ∑' u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ
  let m : Γ → ℂ → ℂ := fun γ =>
    LiZhongQC.mobiusFn (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1)
  let P : Finset C → ℂ → ℂ := fun F z => ∑ u ∈ F, rightCosetCauchyTerm θ Γ s u z
  have hU : IsOpen LiZhongQC.lowerHalf := LiZhongQC.isOpen_lowerHalf
  have hterm (u : C) :
      DifferentiableOn ℂ (rightCosetCauchyTerm θ Γ s u) LiZhongQC.lowerHalf :=
    differentiableOn_rightCosetCauchyTerm_lowerHalf θ Γ s u
  have hP (F : Finset C) : DifferentiableOn ℂ (P F) LiZhongQC.lowerHalf :=
    DifferentiableOn.fun_sum (fun u _hu => hterm u)
  have hP₁ (F : Finset C) : DifferentiableOn ℂ (deriv (P F)) LiZhongQC.lowerHalf :=
    (hP F).deriv hU
  have hP₂ (F : Finset C) :
      DifferentiableOn ℂ (deriv (deriv (P F))) LiZhongQC.lowerHalf :=
    (hP₁ F).deriv hU
  have h₀ : TendstoLocallyUniformlyOn P (LiZhongQC.ahVar ν)
      (atTop : Filter (Finset C)) LiZhongQC.lowerHalf :=
    ((rightCosetCauchySeries_tendstoLocallyUniformlyOn θ Γ s hsep).2).mono (subset_univ _)
  have h₁ := h₀.deriv (Eventually.of_forall hP) hU
  have h₂ := h₁.deriv (Eventually.of_forall hP₁) hU
  have h₃ := h₂.deriv (Eventually.of_forall hP₂) hU
  have hi : TendstoLocallyUniformlyOn (fun F : Finset C => iteratedDeriv 3 (P F))
      (iteratedDeriv 3 (LiZhongQC.ahVar ν)) (atTop : Filter (Finset C))
      LiZhongQC.lowerHalf := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_def] using h₃
  have hfinite (F : Finset C) (z : ℂ) (hz : z ∈ LiZhongQC.lowerHalf) :
      iteratedDeriv 3 (P F) z =
        ∑ u ∈ F, iteratedDeriv 3 (rightCosetCauchyTerm θ Γ s u) z := by
    apply iteratedDeriv_fun_sum
    intro u _hu
    exact ((hterm u).contDiffOn hU).contDiffAt (hU.mem_nhds hz)
  have hd : TendstoLocallyUniformlyOn
      (fun (F : Finset C) (z : ℂ) =>
        ∑ u ∈ F, iteratedDeriv 3 (rightCosetCauchyTerm θ Γ s u) z)
      (iteratedDeriv 3 (LiZhongQC.ahVar ν)) (atTop : Filter (Finset C))
      LiZhongQC.lowerHalf :=
    hi.congr (fun F z hz => hfinite F z hz)
  refine ⟨hd, ?_⟩
  intro ρ hρ
  let k : ℂ := Complex.I / (2 * (Real.pi : ℂ))
  have hrep (u : C) (z : ℂ) (hz : z ∈ LiZhongQC.lowerHalf) :
      iteratedDeriv 3 (rightCosetCauchyTerm θ Γ s u) z =
        k * (deriv (m (ρ u)) z / m (ρ u) z) ^ 2 := by
    have he : rightCosetCauchyTerm θ Γ s u = pullbackCauchyTerm θ (ρ u).val :=
      (congrArg (rightCosetCauchyTerm θ Γ s) (hρ u)).symm.trans
        (rightCosetCauchyTerm_mk θ Γ s (ρ u))
    rw [he]
    exact iteratedDeriv_three_pullbackCauchyTerm θ (ρ u).val hz
  have he (F : Finset C) (z : ℂ) (hz : z ∈ LiZhongQC.lowerHalf) :
      (∑ u ∈ F, iteratedDeriv 3 (rightCosetCauchyTerm θ Γ s u) z) =
        k * ∑ u ∈ F, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun u _hu => hrep u z hz)
  have hscaled : TendstoLocallyUniformlyOn
      (fun (F : Finset C) (z : ℂ) =>
        k * ∑ u ∈ F, (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
      (iteratedDeriv 3 (LiZhongQC.ahVar ν)) (atTop : Filter (Finset C))
      LiZhongQC.lowerHalf :=
    hd.congr (fun F z hz => he F z hz)
  refine ⟨hscaled, ?_⟩
  intro z hz
  have hs : HasSum (fun u : C => k * (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
      (iteratedDeriv 3 (LiZhongQC.ahVar ν) z) := by
    change Tendsto
      (fun F : Finset C => ∑ u ∈ F, k * (deriv (m (ρ u)) z / m (ρ u) z) ^ 2)
      atTop (𝓝 (iteratedDeriv 3 (LiZhongQC.ahVar ν) z))
    simpa only [Finset.mul_sum] using hscaled.tendsto_at hz
  refine ⟨hs, ?_⟩
  calc
    _ = ∑' u : C, k * (deriv (m (ρ u)) z / m (ρ u) z) ^ 2 := hs.tsum_eq.symm
    _ = _ := tsum_mul_left

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
