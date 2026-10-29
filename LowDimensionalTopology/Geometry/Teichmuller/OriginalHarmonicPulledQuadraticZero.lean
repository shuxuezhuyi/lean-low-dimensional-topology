module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonHarmonicVariations
public import Mathlib.Tactic.Ring

/-! # The exact original value of the harmonic pulled-quadratic integral -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces HarmonicFirstVariation QuadraticBergman LiZhongQC

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : IsFuchsian Γ)

local notation "q" => nativeWeilPeterssonHarmonicFrame R hp hg hgenus hΓ
local notation "K" => nativeWeilPeterssonDeformationKernel R hp hg hgenus hΓ

/-- At the original parameter, the actual normalized-map kernel is the
literal upper-half-plane Cauchy kernel. -/
theorem nativeWeilPeterssonDeformationKernel_zero (z ζ : ℂ) :
    K 0 z ζ = 1 / (z - ζ) ^ 2 := by
  have hf : coordinateFamily R p q 0 =
      canonicalFamily R p (0 : HolomorphicQuadraticDifferential R.toRiemannAtlas) 0 := by
    simp only [coordinateFamily, canonicalFamily, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero]
  have hzero : coordinateFamily R p q 0 = id :=
    hf.trans (canonicalFamily_zero R p 0)
  norm_num [nativeWeilPeterssonDeformationKernel, hzero, dz, fderiv_id]

/-- The full original integral converges absolutely and reproduces exactly
the original quadratic coefficient, with its unchanged factor `12/π`. -/
theorem nativeWeilPeterssonPulledQuadratic_zero
    (j : Fin (3 * g - 3)) (z : ℍ) :
    IntegrableOn (fun ζ : ℂ => K 0 (z : ℂ) (conj ζ) ^ 2 *
      conj (harmonicPlane R p (q j) ζ)) upperHalf ∧
      nativeWeilPeterssonPulledQuadratic R hp hg hgenus hΓ j 0 z =
        nativeWeilPeterssonBaseQuadratic R hp hg hgenus hΓ j z := by
  have hrep := uniformizedQuadratic_reproducing R p hp (q j) (z : ℂ) z.im_pos
  have heq (ζ : ℂ) : K 0 (z : ℂ) (conj ζ) ^ 2 *
        conj (harmonicPlane R p (q j) ζ) =
      (ζ.im : ℂ) ^ 2 * uniformizedQuadratic R p (q j) ζ /
        (conj ζ - (z : ℂ)) ^ 4 := by
    rw [nativeWeilPeterssonDeformationKernel_zero]
    have hpow : (1 / ((z : ℂ) - conj ζ) ^ 2) ^ 2 =
        1 / (conj ζ - (z : ℂ)) ^ 4 := by
      rw [div_pow, one_pow, ← pow_mul]
      norm_num only [Nat.reduceMul]
      rw [show ((z : ℂ) - conj ζ) ^ 4 = (conj ζ - (z : ℂ)) ^ 4 by ring]
    rw [hpow]
    simp only [harmonicPlane, map_mul, map_pow, Complex.conj_ofReal,
      Complex.conj_conj]
    ring
  refine ⟨hrep.1.congr_fun (fun ζ _ => (heq ζ).symm)
    isOpen_upperHalf.measurableSet, ?_⟩
  unfold nativeWeilPeterssonPulledQuadratic nativeWeilPeterssonBaseQuadratic
  rw [integral_congr_ae (Filter.Eventually.of_forall heq)]
  exact hrep.2.symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
