/-
The normalized solution, conformal inverse, parameter variation and Schwarzian
APIs reuse Wu Xiaobin's Li-Zhong-QC-formalization, pinned commit
1c0d5473c020b66ed5106331a38a61536760b9b2, under Apache 2.0.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.NonsymmetricBersKernel
public import LowDimensionalTopology.Geometry.Quasiconformal.AffineBersVariation
public import LowDimensionalTopology.Geometry.Quasiconformal.SchwarzianConformal

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Filter Topology

namespace LowDimensionalTopology.Geometry.Quasiconformal.CanonicalBersVariation

private theorem baseInverse_conformal (μ : LiZhongQC.BeltramiH) :
    LiZhongQC.IsConformalOnto (baseInverse μ) (lowerImage μ) LiZhongQC.lowerHalf := by
  refine ⟨baseInverse_differentiableOn μ, ?_, ?_⟩
  · intro x hx y hy hxy
    exact (baseMap_rightInverse μ x).symm.trans
      ((congrArg (baseMap μ) hxy).trans (baseMap_rightInverse μ y))
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact baseInverse_mapsTo_lowerHalf μ hw
    · intro hz
      exact ⟨baseMap μ z, ⟨z, hz, rfl⟩, baseMap_leftInverse μ z⟩

/-- Every bounded upper-supported affine direction has the literal arbitrary-base
Bers integral derivative for the original nonsymmetric normalized map. -/
theorem hasDerivAt_bersFunction_affine (μ : LiZhongQC.BeltramiH)
    {η : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hη : LiZhongQC.IsBeltramiCoeff η univ M)
    (hzero : ∀ ζ : ℂ, ζ.im ≤ 0 → η ζ = 0)
    {z : ℂ} (hz : z ∈ LiZhongQC.lowerHalf) :
    HasDerivAt
      (fun t : ℂ => LiZhongQC.bersFunction (fun ζ => μ.val ζ + t * η ζ) z)
      ((-(6 / Real.pi : ℂ) * ∫ ζ in LiZhongQC.upperHalf, originalFourthKernel μ η z ζ) *
        deriv (baseMap μ) z ^ 2) 0 := by
  obtain ⟨k₀, hk₀0, hk₀1, hμ⟩ := μ.property.1
  have htransport := transportedDirection_isBeltramiCoeff μ hk₀0 hk₀1 hμ hη
  have hbound : 0 ≤ M / (1 - k₀ ^ 2) := div_nonneg hM (by nlinarith)
  have hzL : baseMap μ z ∈ lowerImage μ := ⟨z, hz, rfl⟩
  have hthird := (OffSupportCauchy.firstVariation_thirdDerivative_and_integrable
    (upperImage_isOpen μ).measurableSet hbound htransport
    (Eventually.of_forall (transportedDirection_eq_zero_off_upperImage μ hzero))
    (lowerImage_subset_interior_compl_upperImage μ hzL)).2
  have hq := hasDerivAt_schwarzian_affineQuotient μ hM hη hzero hzL
  change HasDerivAt
    (fun t : ℂ => LiZhongQC.schwarzian
      (LiZhongQC.normalizedSolution (fun ζ => μ.val ζ + t * η ζ) ∘ baseInverse μ) (baseMap μ z))
    (iteratedDeriv 3 (LiZhongQC.ahVar (transportedDirection μ η)) (baseMap μ z)) 0 at hq
  rw [hthird, (fourthKernel_change_of_variables μ hM hη hzero hz).2] at hq
  have hd := (hq.mul_const (deriv (baseMap μ) z ^ 2)).add_const
    (LiZhongQC.schwarzian (baseMap μ) z)
  obtain ⟨r, hr, k, hk0, hk1, hb⟩ := exists_affine_common_bound μ hM hη
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t ht
  let μt : LiZhongQC.BeltramiH := ⟨fun ζ => μ.val ζ + t * η ζ,
    ⟨⟨k, hk0, hk1, hb t ht⟩, fun ζ hζ => by
      change μ.val ζ + t * η ζ = 0
      rw [μ.property.2 ζ hζ, hzero ζ hζ, mul_zero, add_zero]⟩⟩
  have hconf : LiZhongQC.IsConformalOnto (baseMap μt ∘ baseInverse μ)
      (lowerImage μ) (lowerImage μt) :=
    LiZhongQC.IsConformalOnto.comp (LiZhongQC.ut_conformal_lowerHalf μt) (baseInverse_conformal μ)
  have hcomp : (baseMap μt ∘ baseInverse μ) ∘ baseMap μ = baseMap μt := by
    funext w
    exact congrArg (baseMap μt) (baseMap_leftInverse μ w)
  have hs := schwarzian_conformal_comp LiZhongQC.isOpen_lowerHalf
    (LiZhongQC.ut_conformal_lowerHalf μ) hconf z hz
  change LiZhongQC.schwarzian ((baseMap μt ∘ baseInverse μ) ∘ baseMap μ) z =
    LiZhongQC.schwarzian (baseMap μt ∘ baseInverse μ) (baseMap μ z) *
      deriv (baseMap μ) z ^ 2 + LiZhongQC.schwarzian (baseMap μ) z at hs
  rw [hcomp] at hs
  rw [LiZhongQC.bersFunction, indicator_of_mem hz]
  exact hs

/-- The literal nonzero-base kernel is absolutely integrable before it is used
as the actual derivative; neither conclusion is supplied as an input. -/
theorem bersFunction_affine_integral_derivative (μ : LiZhongQC.BeltramiH)
    {η : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hη : LiZhongQC.IsBeltramiCoeff η univ M)
    (hzero : ∀ ζ : ℂ, ζ.im ≤ 0 → η ζ = 0)
    {z : ℂ} (hz : z ∈ LiZhongQC.lowerHalf) :
    IntegrableOn (fun ζ => η ζ * LiZhongQC.dz (baseMap μ) ζ ^ 2 /
        (baseMap μ ζ - baseMap μ z) ^ 4) LiZhongQC.upperHalf ∧
      HasDerivAt
        (fun t : ℂ => LiZhongQC.bersFunction (fun ζ => μ.val ζ + t * η ζ) z)
        ((-(6 / Real.pi : ℂ) * ∫ ζ in LiZhongQC.upperHalf,
            η ζ * LiZhongQC.dz (baseMap μ) ζ ^ 2 / (baseMap μ ζ - baseMap μ z) ^ 4) *
          deriv (baseMap μ) z ^ 2) 0 :=
  ⟨(fourthKernel_change_of_variables μ hM hη hzero hz).1,
    hasDerivAt_bersFunction_affine μ hM hη hzero hz⟩

end LowDimensionalTopology.Geometry.Quasiconformal.CanonicalBersVariation
