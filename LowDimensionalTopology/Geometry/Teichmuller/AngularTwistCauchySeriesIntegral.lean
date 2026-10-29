module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyFiniteSums
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistOriginalCollarSupport
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The actual angular coset integral series

The actual one-support condition bounds the measurable sum coefficient.
The genuine finite norm-integral estimates give absolute summability before
the existing integral-series theorem identifies its normalized Cauchy integral.
The source-facing consumer derives one-support and countability from the same
original closed geodesic and covering.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open LowDimensionalTopology.Geometry.Surfaces

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The actual one-support coefficients give a genuine absolutely convergent integral
series. The geometric one-support input is explicit in this intermediate adapter. -/
theorem rightCosetCauchySeries_hasSum
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) [Countable Γ]
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension θ Γ s v ζ ≠ 0 → u = v) :
    let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
    let ν : ℂ → ℂ := fun ζ => ∑' u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ
    Measurable ν ∧ (∀ ζ : ℂ, ‖ν ζ‖ ≤ 1 / (4 * (θ : ℝ))) ∧
      ∀ z : ℂ,
        Integrable (fun ζ : ℂ => ν ζ * Quasiconformal.firstVariationKernel z ζ)
          (volume : Measure ℂ) ∧
        Summable (fun u : C => ‖rightCosetCauchyTerm θ Γ s u z‖) ∧
        HasSum (fun u : C => rightCosetCauchyTerm θ Γ s u z) (LiZhongQC.ahVar ν z) := by
  classical
  let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
  let ν : ℂ → ℂ := fun ζ => ∑' u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ
  have hm : Measurable ν :=
    Measurable.tsum (fun u => measurable_rightCosetInfinitesimalZeroExtension θ Γ s u)
  have hb (ζ : ℂ) : ‖ν ζ‖ ≤ 1 / (4 * (θ : ℝ)) := by
    by_cases h : ∃ u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0
    · obtain ⟨u, hu⟩ := h
      have he : ν ζ = rightCosetInfinitesimalZeroExtension θ Γ s u ζ := by
        apply tsum_eq_single u
        intro v hv
        by_contra hnv
        exact hv (hsep ζ v u hnv hu)
      rw [he]
      exact norm_rightCosetInfinitesimalZeroExtension_le θ Γ s u ζ
    · have hz : ∀ u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ = 0 := by
        intro u
        exact not_ne_iff.mp (fun hu => h ⟨u, hu⟩)
      simp only [ν, hz, tsum_zero, norm_zero]
      exact one_div_nonneg.mpr (mul_nonneg (by norm_num) θ.property.1.le)
  refine ⟨hm, hb, ?_⟩
  intro z
  let f : C → ℂ → ℂ := fun u ζ => rightCosetInfinitesimalZeroExtension θ Γ s u ζ *
    Quasiconformal.firstVariationKernel z ζ
  let k : ℂ := -(1 / (Real.pi : ℂ))
  have hf (u : C) : Integrable (f u) (volume : Measure ℂ) :=
    integrable_rightCosetInfinitesimalZeroExtension_mul_firstVariationKernel θ Γ s u z
  have hs := summable_integral_norm_rightCoset_kernel θ Γ s hsep z
  have hν : Integrable (fun ζ : ℂ => ν ζ * Quasiconformal.firstVariationKernel z ζ)
      (volume : Measure ℂ) :=
    (LiZhongQC.ah_ker_integrable z).bdd_mul hm.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  have hi : Summable (fun u : C => ‖∫ ζ : ℂ, f u ζ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun _ => norm_integral_le_integral_norm _) hs
  have hn : Summable (fun u : C => ‖rightCosetCauchyTerm θ Γ s u z‖) := by
    change Summable (fun u : C => ‖k * ∫ ζ : ℂ, f u ζ‖)
    simpa only [norm_mul] using hi.mul_left ‖k‖
  have heq : (fun ζ : ℂ => ∑' u : C, f u ζ) =
      (fun ζ => ν ζ * Quasiconformal.firstVariationKernel z ζ) := by
    funext ζ
    exact tsum_mul_right
  have hsum := (hasSum_integral_of_summable_integral_norm hf hs).mul_left k
  rw [heq] at hsum
  exact ⟨hν, hn, hsum⟩

/-- The same original period-circle geodesic produces a normalized coordinate in
which its actual angular coset series is absolutely convergent and equals the integral. -/
theorem originalClosedGeodesic_exists_normalized_angular_integral_series
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    ∃ (A Q : Deck) (s : ℝ) (hs : 0 < s), A ∈ Γ ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
        Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s) ∧
      let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
      let θ := canonicalBandWidth s hs
      let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s))
      let ν : ℂ → ℂ := fun ζ => ∑' u : C, rightCosetInfinitesimalZeroExtension θ ΓQ s u ζ
      Measurable ν ∧ (∀ ζ : ℂ, ‖ν ζ‖ ≤ 1 / (4 * (θ : ℝ))) ∧
        ∀ z : ℂ,
          Integrable (fun ζ : ℂ => ν ζ * Quasiconformal.firstVariationKernel z ζ)
            (volume : Measure ℂ) ∧
          Summable (fun u : C => ‖rightCosetCauchyTerm θ ΓQ s u z‖) ∧
          HasSum (fun u : C => rightCosetCauchyTerm θ ΓQ s u z) (LiZhongQC.ahVar ν z) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.t2Space
  obtain ⟨A, Q, s, hs, hA, hcov, hQA, hsep⟩ :=
    originalClosedGeodesic_exists_normalized_angular_one_support q hp hcircle
  refine ⟨A, Q, s, hs, hA, hcov, hQA, ?_⟩
  let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
  have hcount : (ΓQ : Set Deck).Countable := by
    rw [Subgroup.coe_map]
    exact (LiZhongQC.h36p_countable (LiZhongQC.utm_x2_isFuchsian hp)).image _
  let : Countable ΓQ := hcount.to_subtype
  exact rightCosetCauchySeries_hasSum (canonicalBandWidth s hs) ΓQ s hsep

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
