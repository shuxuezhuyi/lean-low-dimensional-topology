module

public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiComposition
public import LowDimensionalTopology.Geometry.Teichmuller.RealizedBeltrami
public import LowDimensionalTopology.Unproved.Teichmuller.QuasiconformalSmoothing
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Quantitative smooth representatives from global quasiconformal smoothing

The composition estimate is unconditional and uses the actual original-chart
Beltrami law. The approximation theorem displays its one outstanding analytic
input: quantitative global smoothing of actual quasiconformal homeomorphisms.
-/

@[expose] public section
noncomputable section

open Set Topology
open scoped ContDiff Manifold ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

/-- A pointwise consequence of the actual phase-bearing composition fraction. -/
theorem beltrami_fraction_sub_norm_le {a b θ : ℂ} {k : ℝ}
    (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ k) (hθ : ‖θ‖ = 1)
    (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ‖(a + b * θ) / (1 + conj a * b * θ) - a‖ ≤ 2 * k / (1 - k) := by
  have hprod : ‖conj a * b * θ‖ ≤ k := by
    rw [norm_mul, norm_mul, Complex.norm_conj, hθ, mul_one]
    calc
      ‖a‖ * ‖b‖ ≤ 1 * ‖b‖ := mul_le_mul_of_nonneg_right ha.le (norm_nonneg b)
      _ ≤ k := by simpa using hb
  have hden : 1 - k ≤ ‖(1 : ℂ) + conj a * b * θ‖ := by
    calc
      1 - k ≤ 1 - ‖conj a * b * θ‖ := sub_le_sub_left hprod 1
      _ ≤ ‖(1 : ℂ) + conj a * b * θ‖ := by
        simpa using norm_sub_norm_le (1 : ℂ) (-(conj a * b * θ))
  have hkpos : 0 < 1 - k := sub_pos.mpr hk1
  have hdenpos : 0 < ‖(1 : ℂ) + conj a * b * θ‖ := hkpos.trans_le hden
  have hdenne : (1 : ℂ) + conj a * b * θ ≠ 0 := norm_pos_iff.mp hdenpos
  have hsub : (a + b * θ) / (1 + conj a * b * θ) - a =
      (b * θ - a * conj a * b * θ) / (1 + conj a * b * θ) := by
    apply (eq_div_iff hdenne).2
    rw [sub_mul, div_mul_cancel₀ _ hdenne]
    ring
  have ha2 : ‖a‖ * ‖a‖ ≤ 1 := by nlinarith [norm_nonneg a]
  have hnum : ‖b * θ - a * conj a * b * θ‖ ≤ 2 * k := by
    calc
      ‖b * θ - a * conj a * b * θ‖ ≤
          ‖b * θ‖ + ‖a * conj a * b * θ‖ := norm_sub_le _ _
      _ = ‖b‖ + (‖a‖ * ‖a‖) * ‖b‖ := by
        simp only [norm_mul, Complex.norm_conj, hθ, mul_one]
      _ ≤ k + k := add_le_add hb
        ((mul_le_mul_of_nonneg_right ha2 (norm_nonneg b)).trans (by simpa using hb))
      _ = 2 * k := by ring
  rw [hsub, norm_div]
  apply (div_le_div_iff₀ hdenpos hkpos).2
  exact (mul_le_mul_of_nonneg_right hnum hkpos.le).trans
    (mul_le_mul_of_nonneg_left hden (mul_nonneg (by norm_num) hk0))

namespace SmoothSurfaceEquiv

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactSpace X]
    {R : RiemannSurface X} {S : RiemannSurface Y} {T : RiemannSurface Z}

/-- Small distortion of the second map gives an actual uniform tensor difference. -/
theorem beltrami_trans_difference_bound
    (f : SmoothSurfaceEquiv R S) (g : SmoothSurfaceEquiv S T)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation S.toRiemannAtlas T.toRiemannAtlas g.toHomeomorph)
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hk : ∀ (b : BeltramiDifferential.Chart S.toRiemannAtlas) (z : b.val.target),
      ‖(g.beltrami hg).coeff b z‖ ≤ k) :
    ‖BeltramiDifferential.ofTensor ((f.trans g).beltrami
        (hg.comp hf f.toHomeomorph.continuous)) -
      BeltramiDifferential.ofTensor (f.beltrami hf)‖ ≤ 2 * k / (1 - k) := by
  change ‖(BeltramiDifferential.ofTensor ((f.trans g).beltrami
        (hg.comp hf f.toHomeomorph.continuous))).val -
      (BeltramiDifferential.ofTensor (f.beltrami hf)).val‖ ≤ 2 * k / (1 - k)
  apply (BoundedContinuousFunction.norm_le
    (div_nonneg (mul_nonneg (by norm_num) hk0) (sub_pos.mpr hk1).le)).2
  rintro ⟨a, z⟩
  obtain ⟨b, hb, hy⟩ := S.cover (f.toHomeomorph (a.val.symm z.val))
  obtain ⟨c, hc, hz⟩ := T.cover (g.toHomeomorph (f.toHomeomorph (a.val.symm z.val)))
  let B : BeltramiDifferential.Chart S.toRiemannAtlas := ⟨b, hb⟩
  let C : BeltramiDifferential.Chart T.toRiemannAtlas := ⟨c, hc⟩
  let F := riemannChartMap a.val f.toHomeomorph b
  let q : b.target := ⟨F z.val, b.map_source hy⟩
  have hFz : LiZhongQC.dz F z.val ≠ 0 := norm_pos_iff.mp
    (lt_of_le_of_lt (norm_nonneg _)
      (f.chartMap_wirtinger_lt hf a.val a.property b hb ⟨z.property, hy⟩))
  have hphase : ‖conj (LiZhongQC.dz F z.val) / LiZhongQC.dz F z.val‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hFz)]
  change ‖((f.trans g).beltrami (hg.comp hf f.toHomeomorph.continuous)).coeff a z -
    (f.beltrami hf).coeff a z‖ ≤ _
  rw [beltrami_trans_coeff f g hf hg a B C z hy hz]
  exact beltrami_fraction_sub_norm_le
    (f.beltrami_coeff_norm_lt_one hf a z) (hk B q) hphase hk0 hk1

end SmoothSurfaceEquiv

namespace MarkedRiemannSurface

universe u
variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The quantitative smoothing hypothesis gives an actual native marking in
the desired class with a proved Banach-distance bound from the fixed marking. -/
theorem exists_close_marking_of_quasiconformal_smoothing
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})
    (M N : MarkedRiemannSurface.{u, u} R) (f : M.carrier ≃ₜ N.carrier)
    {K ε : ℝ} (hK : 1 ≤ K)
    (hf : let := M.surface.toRiemannAtlas.toChartedSpace
      let := N.surface.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsKQCRS f K)
    (hhom : ContinuousMap.Homotopic
      ((_root_.toContinuousMap f).comp M.markingMap) N.markingMap)
    (hε : 0 < ε) (hsmall : (K - 1) / (K + 1) + ε < 1) :
    ∃ P : MarkedRiemannSurface.{u, u} R,
      TeichmullerSpace.mk P = TeichmullerSpace.mk N ∧
      ‖P.beltramiCoefficient - M.beltramiCoefficient‖ ≤
        2 * ((K - 1) / (K + 1) + ε) / (1 - ((K - 1) / (K + 1) + ε)) := by
  let := R.compactSpace
  let := M.surface.compactSpace
  obtain ⟨F, hF, hFhom, hFnorm⟩ := hsmooth M.surface N.surface f K hK hf ε hε
  let P : MarkedRiemannSurface.{u, u} R :=
    { carrier := N.carrier
      topology := N.topology
      surface := N.surface
      marking := M.marking.trans F
      orientation_preserving := hF.comp M.orientation_preserving
        M.marking.toHomeomorph.continuous }
  have hPN : Equivalent P N := by
    refine ⟨Homeomorph.refl _, RiemannAnalyticMap.id _, ?_⟩
    change ContinuousMap.Homotopic P.markingMap N.markingMap
    exact ((hFhom.comp (ContinuousMap.Homotopic.refl M.markingMap)).trans hhom)
  refine ⟨P, (TeichmullerSpace.mk_eq_mk_iff P N).2 hPN, ?_⟩
  have hk0 : 0 ≤ (K - 1) / (K + 1) + ε :=
    add_nonneg (div_nonneg (sub_nonneg.mpr hK) (by linarith)) hε.le
  exact M.marking.beltrami_trans_difference_bound F M.orientation_preserving hF hk0 hsmall
    (fun b z => ((F.beltrami hF).coeff_norm_le_supNorm b z).trans hFnorm)

end MarkedRiemannSurface
end LowDimensionalTopology.Geometry.Teichmuller
