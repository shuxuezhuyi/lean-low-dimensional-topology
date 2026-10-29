module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCanonicalCoefficientCurve
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchySeriesUniform
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyNormalization
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# The same original angular deformation and its actual Cauchy series

One original period-circle geodesic chooses one full-period covering
matrix and positive normalized coordinate. The actual coefficient family,
its canonical plane derivative and its absolutely convergent Cauchy series
all use those same choices. Splitting the identity coset gives the angular
and logarithmic first term. Each fixed matrix representative has its
existing concrete polynomial formula for the same intrinsic integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open LowDimensionalTopology.Geometry.Surfaces

local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

open scoped Classical in
/-- The same original closed geodesic and covering give the canonical plane
variation, the identity-separated actual integral series and each fixed
representative's polynomial expression. -/
theorem originalClosedGeodesic_exists_canonical_angular_variation_series
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup Deck}
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
      let ν : ℂ → ℂ := fun ζ =>
        ∑' u : C, rightCosetInfinitesimalZeroExtension θ ΓQ s u ζ
      let e : C := Quotient.mk _ (1 : ΓQ)
      let T : C → ℂ → ℂ := fun u z =>
        if u = e then 0 else rightCosetCauchyTerm θ ΓQ s u z
      ∃ μ : ℝ → MeasurableBeltramiBall,
        (∀ t : ℝ, ((μ t).val : ℂ → ℂ) =ᵐ[volume]
          rightCosetCoefficientSum θ ΓQ s t) ∧
        (μ 0).val = 0 ∧
        TendstoLocallyUniformly
          (fun t w =>
            (MeasurableBeltramiBall.normalizedSolution (μ t) w - w) / (t : ℂ))
          (LiZhongQC.ahVar ν) (𝓝[≠] (0 : ℝ)) ∧
        (∀ w : ℂ,
          HasDerivAt (fun t : ℝ => MeasurableBeltramiBall.normalizedSolution (μ t) w)
            (LiZhongQC.ahVar ν w) 0) ∧
        (∀ z : ℂ,
          Summable (fun u : C => ‖rightCosetCauchyTerm θ ΓQ s u z‖) ∧
          HasSum (fun u : C => rightCosetCauchyTerm θ ΓQ s u z) (LiZhongQC.ahVar ν z) ∧
          Summable (fun u : C => ‖T u z‖) ∧
          HasSum (fun u : C => T u z)
            (LiZhongQC.ahVar ν z - firstCauchyClosedForm θ z) ∧
          LiZhongQC.ahVar ν z = firstCauchyClosedForm θ z + ∑' u : C, T u z) ∧
        TendstoLocallyUniformlyOn
          (fun (F : Finset C) (z : ℂ) =>
            firstCauchyClosedForm θ z + ∑ u ∈ F, T u z)
          (LiZhongQC.ahVar ν) (atTop : Filter (Finset C)) Set.univ ∧
        ∀ (γ : ΓQ) (z : ℂ),
          rightCosetCauchyTerm θ ΓQ s (Quotient.mk _ γ) z =
            weightedFirstCauchyTerm θ γ.val z +
              (Complex.I / (2 * (Real.pi : ℂ))) *
                (cauchyNormalizationPolynomial θ γ.val).eval z := by
  classical
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
  let θ := canonicalBandWidth s hs
  let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s))
  let ν : ℂ → ℂ := fun ζ =>
    ∑' u : C, rightCosetInfinitesimalZeroExtension θ ΓQ s u ζ
  let e : C := Quotient.mk _ (1 : ΓQ)
  let T : C → ℂ → ℂ := fun u z =>
    if u = e then 0 else rightCosetCauchyTerm θ ΓQ s u z
  obtain ⟨_v, μ, _ε, _hv, _hvnorm, hμ, _hdecomp, _hε, hzero, hvar, hderiv⟩ :=
    exists_rightCosetCoefficientSum_canonical_variation θ ΓQ s hsep
  have hseries := rightCosetCauchySeries_hasSum θ ΓQ s hsep
  have hid (z : ℂ) : rightCosetCauchyTerm θ ΓQ s e z = firstCauchyClosedForm θ z :=
    (congrFun (rightCosetCauchyTerm_identity θ ΓQ s) z).trans
      (firstCauchyTerm_eq_closedForm θ z)
  have hnorm (u : C) (z : ℂ) : ‖T u z‖ ≤ ‖rightCosetCauchyTerm θ ΓQ s u z‖ := by
    by_cases hu : u = e
    · simp only [T, ite_eq_left hu, norm_zero]
      exact norm_nonneg _
    · simp only [T, ite_eq_right hu, le_refl]
  have hpoint (z : ℂ) :
      Summable (fun u : C => ‖rightCosetCauchyTerm θ ΓQ s u z‖) ∧
      HasSum (fun u : C => rightCosetCauchyTerm θ ΓQ s u z) (LiZhongQC.ahVar ν z) ∧
      Summable (fun u : C => ‖T u z‖) ∧
      HasSum (fun u : C => T u z) (LiZhongQC.ahVar ν z - firstCauchyClosedForm θ z) ∧
      LiZhongQC.ahVar ν z = firstCauchyClosedForm θ z + ∑' u : C, T u z := by
    have hdata := hseries.2.2 z
    have hs : HasSum (fun u : C => rightCosetCauchyTerm θ ΓQ s u z)
        (LiZhongQC.ahVar ν z) := hdata.2.2
    have ht : HasSum (fun u : C => T u z)
        (LiZhongQC.ahVar ν z - rightCosetCauchyTerm θ ΓQ s e z) :=
      hasSum_ite_sub_hasSum hs e
    rw [hid z] at ht
    have hn : Summable (fun u : C => ‖T u z‖) :=
      Summable.of_nonneg_of_le (fun u => norm_nonneg (T u z)) (fun u => hnorm u z)
        hdata.2.1
    have he := hs.summable.tsum_eq_add_tsum_ite e
    rw [hs.tsum_eq, hid z] at he
    exact ⟨hdata.2.1, hs, hn, ht, he⟩
  have hpartial (F : Finset C) (hF : e ∈ F) (z : ℂ) :
      firstCauchyClosedForm θ z + ∑ u ∈ F, T u z =
        ∑ u ∈ F, rightCosetCauchyTerm θ ΓQ s u z := by
    have hTe : T e z = 0 := by simp only [T, ite_eq_left (rfl : e = e)]
    have hsum : (∑ u ∈ F, T u z) =
        ∑ u ∈ F.erase e, rightCosetCauchyTerm θ ΓQ s u z := by
      calc
        _ = ∑ u ∈ F.erase e, T u z := (Finset.sum_erase F hTe).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro u hu
          exact ite_eq_right (Finset.mem_erase.mp hu).1
    rw [hsum, ← hid z]
    exact Finset.add_sum_erase F (fun u : C => rightCosetCauchyTerm θ ΓQ s u z) hF
  have hconv := (rightCosetCauchySeries_tendstoLocallyUniformlyOn θ ΓQ s hsep).2
  have hsplitconv : TendstoLocallyUniformlyOn
      (fun (F : Finset C) (z : ℂ) => firstCauchyClosedForm θ z + ∑ u ∈ F, T u z)
      (LiZhongQC.ahVar ν) (atTop : Filter (Finset C)) Set.univ := by
    apply hconv.congr_inseparable
    filter_upwards [eventually_ge_atTop ({e} : Finset C)] with F hF z _hz
    exact Inseparable.of_eq (hpartial F (hF (Finset.mem_singleton_self e)) z).symm
  refine ⟨μ, hμ, hzero, hvar, hderiv, hpoint, hsplitconv, ?_⟩
  intro γ z
  rw [rightCosetCauchyTerm_mk, pullbackCauchyTerm_eq_weighted_add_polynomial]

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
