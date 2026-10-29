module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSourceKernels
public import Mathlib.Tactic.Ring

/-!
# Finite directions for the literal WP principal values

Finite weighted sums preserve the actual punctured-integral limits.
The original tangent coefficients expand only almost everywhere; exact
invariance of each truncated integral then gives the bilinear source formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Manifold ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open LiZhongQC GammaMeasurableBeltrami

/-- Each finite weighted combination retains the punctured integrability
and converges to the same finite combination of actual principal values. -/
theorem principalValueExists_finset_linear_combination
    {ι : Type} (T : Finset ι) (c : ι → ℂ) (f : ι → ℂ → ℂ) (ξ : ℂ)
    (hf : ∀ i ∈ T, PrincipalValueExists (f i) ξ) :
    PrincipalValueExists (fun η => ∑ i ∈ T, c i * f i η) ξ ∧
      hilbertHSmooth (fun η => ∑ i ∈ T, c i * f i η) ξ =
        ∑ i ∈ T, c i * hilbertHSmooth (f i) ξ := by
  classical
  let F : ℂ → ℂ := fun η => ∑ i ∈ T, c i * f i η
  have hsplit (η : ℂ) : F η / (η - ξ) ^ 2 =
      ∑ i ∈ T, c i * (f i η / (η - ξ) ^ 2) := by
    simp only [F, Finset.sum_div, mul_div_assoc]
  have hfinite (r : ℝ) (hr : 0 < r) :
      IntegrableOn (fun η => F η / (η - ξ) ^ 2) {η : ℂ | r < ‖η - ξ‖} := by
    simp only [hsplit]
    exact integrable_finsetSum T (fun i hi => ((hf i hi).1 r hr).const_mul (c i))
  have htrunc (r : ℝ) (hr : 0 < r) :
      -(1 / (Real.pi : ℂ)) *
        (∫ η in {η : ℂ | r < ‖η - ξ‖}, F η / (η - ξ) ^ 2) =
      ∑ i ∈ T, c i * (-(1 / (Real.pi : ℂ)) *
        ∫ η in {η : ℂ | r < ‖η - ξ‖}, f i η / (η - ξ) ^ 2) := by
    simp_rw [hsplit]
    rw [integral_finsetSum T (fun i hi => ((hf i hi).1 r hr).const_mul (c i))]
    simp only [integral_const_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hlim : Tendsto
      (fun r : ℝ => -(1 / (Real.pi : ℂ)) *
        ∫ η in {η : ℂ | r < ‖η - ξ‖}, F η / (η - ξ) ^ 2)
      (𝓝[>] 0) (𝓝 (∑ i ∈ T, c i * hilbertHSmooth (f i) ξ)) := by
    apply (tendsto_finsetSum T (fun i hi => ((hf i hi).2.const_mul (c i)))).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (htrunc r hr).symm
  have hvalue : hilbertHSmooth F ξ = ∑ i ∈ T, c i * hilbertHSmooth (f i) ξ :=
    hlim.limUnder_eq
  refine ⟨⟨hfinite, ?_⟩, hvalue⟩
  rw [hvalue]
  exact hlim

private theorem upperExtension_congr_ae {μ ν : ℍ → ℂ}
    (h : μ =ᵐ[flatArea] ν) : upperExtension μ =ᵐ[volume] upperExtension ν := by
  apply ae_of_ae_restrict_of_ae_restrict_compl upperHalf
  · rw [← map_flat_coe, UpperHalfPlane.measurableEmbedding_coe.ae_map_iff]
    filter_upwards [h] with η hη
    simp only [upperExtension, hη]
  · apply ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet.compl
    intro η hη
    simp only [upperExtension, show ¬0 < η.im from hη, dite_false]

private theorem innerInput_congr_ae {μ ν : ℍ → ℂ}
    (h : μ =ᵐ[flatArea] ν) (z : ℍ) :
    innerInput μ z =ᵐ[volume] innerInput ν z := by
  apply upperExtension_congr_ae
  filter_upwards [h] with η hη
  simp only [hη]

private theorem bilinear_congr_ae {μ μ' ν ν' : ℍ → ℂ}
    (hμ : μ =ᵐ[flatArea] μ') (hν : ν =ᵐ[flatArea] ν') (ζ z : ℍ) :
    bilinear μ ν ζ z = bilinear μ' ν' ζ z := by
  have hinner := hilbertHSmooth_congr_ae (innerInput_congr_ae hν z)
  have houter : outerInput μ ν z =ᵐ[volume] outerInput μ' ν' z := by
    apply upperExtension_congr_ae
    filter_upwards [hμ] with η hη
    rw [hη, hinner]
  unfold bilinear
  rw [hilbertHSmooth_congr_ae houter]

private theorem innerInput_finset {ι : Type} (T : Finset ι) (c : ι → ℂ)
    (μ : ι → ℍ → ℂ) (z : ℍ) :
    innerInput (fun η => ∑ i ∈ T, c i * μ i η) z =
      fun η => ∑ i ∈ T, c i * innerInput (μ i) z η := by
  funext η
  by_cases hη : 0 < η.im
  · simp only [innerInput, upperExtension, dite_eq_left hη, Finset.sum_mul, mul_assoc]
  · simp only [innerInput, upperExtension, dite_eq_right hη, mul_zero, Finset.sum_const_zero]

private theorem bilinear_finset {ι κ : Type} (T : Finset ι) (U : Finset κ)
    (c : ι → ℂ) (d : κ → ℂ) (μ : ι → ℍ → ℂ) (ν : κ → ℍ → ℂ)
    (ζ z : ℍ)
    (hinner : ∀ k ∈ U, ∀ ξ : ℍ, PrincipalValueExists (innerInput (ν k) z) ξ)
    (houter : ∀ j ∈ T, ∀ k ∈ U,
      PrincipalValueExists (outerInput (μ j) (ν k) z) (conj (ζ : ℂ))) :
    bilinear (fun η => ∑ j ∈ T, c j * μ j η)
        (fun η => ∑ k ∈ U, d k * ν k η) ζ z =
      ∑ j ∈ T, ∑ k ∈ U, c j * d k * bilinear (μ j) (ν k) ζ z := by
  classical
  let V : ℍ → ℂ := fun η => ∑ k ∈ U, d k * ν k η
  have hinside (ξ : ℍ) : hilbertHSmooth (innerInput V z) ξ =
      ∑ k ∈ U, d k * hilbertHSmooth (innerInput (ν k) z) ξ := by
    rw [show innerInput V z =
      (fun η => ∑ k ∈ U, d k * innerInput (ν k) z η) from innerInput_finset U d ν z]
    exact (principalValueExists_finset_linear_combination U d
      (fun k => innerInput (ν k) z) ξ (fun k hk => hinner k hk ξ)).2
  have hfun : outerInput (fun η => ∑ j ∈ T, c j * μ j η) V z =
      fun η => ∑ j ∈ T, c j * (∑ k ∈ U, d k * outerInput (μ j) (ν k) z η) := by
    funext η
    by_cases hη : 0 < η.im
    · simp only [outerInput, upperExtension, dite_eq_left hη]
      rw [hinside ⟨η, hη⟩, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    · simp only [outerInput, upperExtension, dite_eq_right hη, mul_zero,
        Finset.sum_const_zero]
  have hs (j : ι) (hj : j ∈ T) :=
    principalValueExists_finset_linear_combination U d
      (fun k => outerInput (μ j) (ν k) z) (conj (ζ : ℂ)) (houter j hj)
  have hall := principalValueExists_finset_linear_combination T c
    (fun j η => ∑ k ∈ U, d k * outerInput (μ j) (ν k) z η)
    (conj (ζ : ℂ)) (fun j hj => (hs j hj).1)
  unfold bilinear
  rw [hfun, hall.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(hs j hj).2, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

variable (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

/-- The actual chosen tangent representatives have their coordinate
expansion almost everywhere in the original Euclidean area measure. -/
theorem nativeWeilPeterssonSourceDirection_finset_ae (u : E) :
    μ ν P F hF u =ᵐ[flatArea]
      fun z => ∑ j : I, u j * μ ν P F hF (Pi.single j 1) z := by
  classical
  let := C
  let T₀ := (TH ν P F hF hsmooth).toLinearMap.comp (K (β ν.val)).symm.toLinearMap
  let T : E →ₗ[ℂ] GammaMeasurableBeltrami.Ambient :=
    { toFun := fun v => (T₀ v).val.val
      map_add' := by
        intro v w
        simp only [map_add, Submodule.coe_add]
        exact AddMemClass.coe_add (compatibleClosedSubmodule (deformedGroup hΓ ν)) _ _
      map_smul' := by
        intro c v
        simp only [map_smul, Submodule.coe_smul]
        exact SetLike.val_smul (compatibleClosedSubmodule (deformedGroup hΓ ν)) c _ }
  have hvec : u = ∑ j : I, u j • Pi.single j (1 : ℂ) := by
    simp only [← Pi.single_smul, smul_eq_mul, mul_one, Finset.univ_sum_single]
  have hsum : T u = ∑ j : I, u j • T (Pi.single j 1) := by
    calc
      _ = T (∑ j : I, u j • Pi.single j (1 : ℂ)) := congrArg T hvec
      _ = _ := by simp only [map_sum, map_smul]
  apply ae_hyperbolic_iff.mp
  change (fun z : ℍ => T u z) =ᵐ[volume]
    fun z => ∑ j : I, u j * T (Pi.single j 1) z
  have hscalar (j : I) :
      (fun z : ℍ => (u j • T (Pi.single j 1)) z) =ᵐ[volume]
        fun z => u j * T (Pi.single j 1) z :=
    Lp.coeFn_smul (𝕜 := ℂ) (u j) (T (Pi.single j 1))
  have ha := (Lp.coeFn_finsetSum Finset.univ
    (fun j : I => u j • T (Pi.single j 1))).trans
      (eventuallyEq_sum (fun j _ => hscalar j))
  filter_upwards [ha] with z hz
  simpa only [← hsum, Finset.sum_apply] using hz

/-- The actual bilinear principal-value kernel expands in the original
coordinate directions once its genuine inner and lower outer limits exist. -/
theorem nativeWeilPeterssonSourceBilinear_finset
    (u v : E) (ζ z : ℍ)
    (hinner : ∀ k : I, ∀ ξ : ℍ,
      SourceKernel.PrincipalValueExists (SourceKernel.innerInput (μ ν P F hF (Pi.single k 1)) z) ξ)
    (houter : ∀ j k : I,
      SourceKernel.PrincipalValueExists
        (SourceKernel.outerInput (μ ν P F hF (Pi.single j 1))
          (μ ν P F hF (Pi.single k 1)) z) (conj (ζ : ℂ))) :
    SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF v) ζ z =
      ∑ j : I, ∑ k : I, u j * v k *
        SourceKernel.bilinear (μ ν P F hF (Pi.single j 1))
          (μ ν P F hF (Pi.single k 1)) ζ z := by
  classical
  exact (SourceKernel.bilinear_congr_ae
    (nativeWeilPeterssonSourceDirection_finset_ae R hp hg hgenus hΓ hfree hsmooth ν P F hF u)
    (nativeWeilPeterssonSourceDirection_finset_ae R hp hg hgenus hΓ hfree hsmooth ν P F hF v)
    ζ z).trans
      (SourceKernel.bilinear_finset Finset.univ Finset.univ u v
        (fun j => μ ν P F hF (Pi.single j 1))
        (fun k => μ ν P F hF (Pi.single k 1)) ζ z
        (fun k _ => hinner k) (fun j _ k _ => houter j k))

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
