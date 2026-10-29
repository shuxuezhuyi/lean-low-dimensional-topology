module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticProngNaturalChart
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticOrdinarySmooth
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticNaturalCoordinateProjection
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticZeroSet
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticRamifiedDevelopment
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalQuadraticFoliation
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The actual finite prong model of the original quadratic differential

Rescaling the ordinary center chart gives the coefficient-one monomial model.
Actual plane branch charts compose with that center chart to give genuine
flat charts of the same original differential, in its original smooth structure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
    {q : HolomorphicQuadraticDifferential R.toRiemannAtlas} {p : X}

private theorem scaledProngBranch_isQuadraticNatural
    (D : QuadraticNaturalCoordinateData R q p) (a : OpenPartialHomeomorph ℂ ℂ)
    (ha : IsProngNaturalChart D.order 1 a) :
    IsQuadraticNaturalLeafChart R q
      ((D.ordinaryNeighborhood.transHomeomorph
        (Homeomorph.mulLeft₀ (quadraticZeroScaling D.order)
          (quadraticZeroScaling_ne_zero D.order))).trans a) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.isManifold
  let k := quadraticZeroScaling D.order
  let H := D.ordinaryNeighborhood.transHomeomorph
    (Homeomorph.mulLeft₀ k (quadraticZeroScaling_ne_zero D.order))
  let E := H.trans a
  have hH0 : H p = 0 := by
    change k * D.ordinaryNeighborhood p = 0
    rw [D.ordinaryNeighborhood_data.2.1, mul_zero]
  have hkpow : k ^ (D.order + 2) = ((D.order + 2 : ℂ) / 2) ^ 2 := by
    simpa only [k, quadraticZeroExponent, Nat.cast_add, Nat.cast_ofNat] using
      quadraticZeroScaling_pow D.order
  have hregular (y : X) (hy : y ∈ E.source) :
      LiZhongQC.IsRegularPoint (q : X → ℂ → ℂ) y := by
    have hy' : y ∈ (chartAt ℂ p).source ∧ chartAt ℂ p y ∈ D.ordinaryChart.source := hy.1.1
    have hyp : y ≠ p := by
      intro h
      apply ha.1
      simpa only [h, hH0] using (show H y ∈ a.source from hy.2)
    have hne : chartAt ℂ p y ≠ chartAt ℂ p p := fun h =>
      hyp ((chartAt ℂ p).injOn hy'.1 (mem_chart_source ℂ p) h)
    simpa only [(chartAt ℂ p).left_inv hy'.1] using
      (LiZhongQC.s26d_a_isRegularPoint_iff q.property p
        ((chartAt ℂ p).map_source hy'.1)).mpr
          (D.normal.ne_zero (chartAt ℂ p y) hy'.2 hne)
  refine ⟨fun y hy => hregular y hy, ?_⟩
  intro y hy
  have hy' : y ∈ (chartAt ℂ p).source ∧ chartAt ℂ p y ∈ D.ordinaryChart.source := hy.1.1
  have hyA : k * D.ordinaryChart (chartAt ℂ p y) ∈ a.source := hy.2
  have hmul : AnalyticAt ℂ (fun ξ : ℂ => k * ξ)
      (D.ordinaryChart (chartAt ℂ p y)) := analyticAt_const.mul analyticAt_id
  have hbranch : AnalyticAt ℂ (fun ξ => a (k * ξ)) (D.ordinaryChart (chartAt ℂ p y)) ∧
      ∀ᶠ ξ in 𝓝 (D.ordinaryChart (chartAt ℂ p y)),
        deriv (fun ξ => a (k * ξ)) ξ ^ 2 = ((D.order + 2 : ℂ) / 2) ^ 2 * ξ ^ D.order := by
    refine ⟨(ha.2.1 _ hyA).comp hmul, ?_⟩
    filter_upwards [hmul.continuousAt.tendsto.eventually (a.open_source.mem_nhds hyA)] with ξ hξ
    have hderiv : deriv (fun ξ => a (k * ξ)) ξ = deriv (a : ℂ → ℂ) (k * ξ) * k := by
      simpa only [mul_one, Function.comp_def] using
        ((ha.2.1 _ hξ).differentiableAt.hasDerivAt.comp ξ
          ((hasDerivAt_id ξ).const_mul k)).deriv
    rw [hderiv, mul_pow, ha.2.2 _ hξ, one_mul, mul_pow, ← hkpow, pow_add]
    ring
  have hW : AnalyticAt ℂ (fun z => E ((chartAt ℂ y).symm z)) (chartAt ℂ y y) ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ y y),
        deriv (fun z => E ((chartAt ℂ y).symm z)) z ^ 2 = (q : X → ℂ → ℂ) y z :=
    LiZhongQC.s26d_a_W_natural q.property D.normal hy'.1 hy'.2
      (h := fun ξ => a (k * ξ)) hbranch.1 hbranch.2
  have hsq : ∀ᶠ z in 𝓝 (chartAt ℂ y y),
      deriv (fun z => E ((chartAt ℂ y).symm z) - E y) z ^ 2 = (q : X → ℂ → ℂ) y z :=
    hW.2.mono fun z hz => by simpa only [deriv_sub_const] using hz
  refine ⟨hW.1.sub analyticAt_const, ?_, ?_, hsq⟩
  · simp only [(chartAt ℂ y).left_inv (mem_chart_source ℂ y), sub_self]
  · intro hzero
    have hqzero : (q : X → ℂ → ℂ) y (chartAt ℂ y y) = 0 := by
      rw [← hsq.self_of_nhds, hzero, zero_pow (by decide)]
    exact hregular y hy hqzero

/-- The actual scaled ordinary center chart gives the exact positive-order prong model. -/
theorem QuadraticNaturalCoordinateData.ordinaryNeighborhood_scaledProngModel
    (D : QuadraticNaturalCoordinateData R q p) (hp : p ∈ quadraticZeroSet R q) :
    let C : Set (OpenPartialHomeomorph X ℂ) :=
      {e | IsQuadraticNaturalLeafChart R q e ∧ IsRealSmoothFoliationChart R e}
    let h := D.ordinaryNeighborhood.transHomeomorph
      (Homeomorph.mulLeft₀ (quadraticZeroScaling D.order)
        (quadraticZeroScaling_ne_zero D.order))
    0 < D.order ∧ h.source ∩ quadraticZeroSet R q = {p} ∧
      MatchesProngModel R C D.order 1 h p := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let k := quadraticZeroScaling D.order
  let H := D.ordinaryNeighborhood.transHomeomorph
    (Homeomorph.mulLeft₀ k (quadraticZeroScaling_ne_zero D.order))
  let C : Set (OpenPartialHomeomorph X ℂ) :=
    {e | IsQuadraticNaturalLeafChart R q e ∧ IsRealSmoothFoliationChart R e}
  have hm : 0 < D.order := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hp (D.normal.regular_iff.mpr hzero)
  have hpH : p ∈ H.source := D.ordinaryNeighborhood_data.1
  have hH0 : H p = 0 := by
    change k * D.ordinaryNeighborhood p = 0
    rw [D.ordinaryNeighborhood_data.2.1, mul_zero]
  have hD := D.ordinaryNeighborhood_isRealSmooth
  have hM : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : ℂ => k * z) :=
    (show ContDiff ℝ ∞ (fun z : ℂ => k * z) from contDiff_const.mul contDiff_id).contMDiff
  have hMi : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : ℂ => k⁻¹ * z) :=
    (show ContDiff ℝ ∞ (fun z : ℂ => k⁻¹ * z) from contDiff_const.mul contDiff_id).contMDiff
  have hH : IsRealSmoothFoliationChart R H :=
    ⟨hM.comp_contMDiffOn hD.1, hD.2.comp hMi.contMDiffOn (fun _ hz => hz)⟩
  have hsing : H.source ∩ quadraticZeroSet R q = {p} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨hy, hyzero⟩
      have hy' : y ∈ (chartAt ℂ p).source ∧ chartAt ℂ p y ∈ D.ordinaryChart.source := hy.1
      change ¬ LiZhongQC.IsRegularPoint (q : X → ℂ → ℂ) y at hyzero
      have hcoord : chartAt ℂ p y = chartAt ℂ p p := by
        by_contra hne
        apply hyzero
        simpa only [(chartAt ℂ p).left_inv hy'.1] using
          (LiZhongQC.s26d_a_isRegularPoint_iff q.property p
            ((chartAt ℂ p).map_source hy'.1)).mpr
              (D.normal.ne_zero (chartAt ℂ p y) hy'.2 hne)
      exact Set.mem_singleton_iff.mpr
        ((chartAt ℂ p).injOn hy'.1 (mem_chart_source ℂ p) hcoord)
    · intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact ⟨hpH, hp⟩
  refine ⟨hm, hsing, hH, hpH, hH0, ?_⟩
  intro x hx hxp
  have hzx : H x ≠ 0 := by
    intro hz
    exact hxp (H.injOn hx hpH (hz.trans hH0.symm))
  obtain ⟨a, hax, ha⟩ := exists_quadraticProngNaturalChart D.order hm (H x) hzx
  let E := H.trans a
  have hEx : x ∈ E.source := ⟨hx, hax⟩
  have hEnatural : IsQuadraticNaturalLeafChart R q E :=
    scaledProngBranch_isQuadraticNatural D a ha
  have hAa : AnalyticOnNhd ℂ (a : ℂ → ℂ) a.source := ha.2.1
  have hAia : AnalyticOnNhd ℂ (a.symm : ℂ → ℂ) a.target :=
    openPartialHomeomorph_analytic_inverse a hAa
  have hAs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (a : ℂ → ℂ) a.source :=
    ((hAa.contDiffOn (n := ∞) a.open_source.uniqueDiffOn).restrict_scalars ℝ).contMDiffOn
  have hAis : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (a.symm : ℂ → ℂ) a.target :=
    ((hAia.contDiffOn (n := ∞) a.open_target.uniqueDiffOn).restrict_scalars ℝ).contMDiffOn
  have hEs : IsRealSmoothFoliationChart R E :=
    ⟨hAs.comp' hH.1, hH.2.comp' hAis⟩
  have hEC : E ∈ C := ⟨hEnatural, hEs⟩
  refine ⟨E, hEC, a, ha, E.source, E.open_source, hEx,
    fun y hy => ⟨hy, hy⟩, ?_⟩
  exact fun _ _ _ _ => Iff.rfl

end LowDimensionalTopology.Geometry.Teichmuller
