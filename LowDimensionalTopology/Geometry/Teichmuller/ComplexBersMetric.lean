module

public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBersCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBersInverse
public import Mathlib.Tactic.Linarith

/-!
# Equality of the explicit QC metric and Bers coordinate topologies

The actual native full-log QC metric is homeomorphic, by the actual Bers
coordinate map, to its finite-dimensional open coordinate image. This compares
two explicit topological structures. It does not identify either of them with
the independently coinduced realized-coefficient topology.
-/

@[expose] public section
noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces

universe u

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

/-- Coordinate differences also bound the actual weighted Bers supremum above. -/
theorem bersCoordinates_norm_upper : ∃ d > 0,
    ∀ a b : TeichmullerSpace.{u, u} R,
      LiZhongQC.bersNormL
        (LiZhongQC.bersMapGamma Γ (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a) -
          LiZhongQC.bersMapGamma Γ (gammaEquiv R hg hgenus hPresentation hΓ hfree hp b)) ≤
      ENNReal.ofReal (d * ‖bersCoordinates R hg hgenus hPresentation hΓ hfree hp a -
        bersCoordinates R hg hgenus hPresentation hΓ hfree hp b‖) := by
  have hn : 0 < 3 * g - 3 := by omega
  obtain ⟨c, d, _, hd, hcompare⟩ := LiZhongQC.s33dim_coordinate_comparison hn
    (linearBersCoordinates R hg hgenus hPresentation hΓ hp)
    (linearBersCoordinates_spec R hg hgenus hPresentation hΓ hp).1
  refine ⟨d, hd, fun a b => ?_⟩
  simpa only [bersCoordinates, map_sub, Submodule.coe_sub] using
    (hcompare (⟨LiZhongQC.bersMapGamma Γ
      (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a),
        (LiZhongQC.bersMapGamma_mem hΓ _).1⟩ -
      ⟨LiZhongQC.bersMapGamma Γ
        (gammaEquiv R hg hgenus hPresentation hΓ hfree hp b),
        (LiZhongQC.bersMapGamma_mem hΓ _).1⟩)).2

/-- Actual coordinate epsilon control implies the actual full-log QC distance
control; the factor two comes from the proved source/native normalization. -/
theorem bersCoordinates_inverse_epsilon (a : TeichmullerSpace.{u, u} R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b : TeichmullerSpace.{u, u} R,
      ‖bersCoordinates R hg hgenus hPresentation hΓ hfree hp b -
        bersCoordinates R hg hgenus hPresentation hΓ hfree hp a‖ < δ →
      fromQCDistance R a b < ε := by
  obtain ⟨d, hd, hupper⟩ :=
    bersCoordinates_norm_upper R hg hgenus hPresentation hΓ hfree hp
  obtain ⟨δB, hδB, hB⟩ := bersMapGamma_inverse_epsilon hΓ
    (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a)
    (ε := ε / 2) (by linarith)
  refine ⟨δB / d, div_pos hδB hd, fun b hb => ?_⟩
  have hprod : d * ‖bersCoordinates R hg hgenus hPresentation hΓ hfree hp b -
      bersCoordinates R hg hgenus hPresentation hΓ hfree hp a‖ < δB := by
    have h := (lt_div_iff₀ hd).1 hb
    simpa only [mul_comm] using h
  have hnorm : LiZhongQC.bersNormL
      (LiZhongQC.bersMapGamma Γ (gammaEquiv R hg hgenus hPresentation hΓ hfree hp b) -
        LiZhongQC.bersMapGamma Γ (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a)) <
      ENNReal.ofReal δB :=
    (hupper b a).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδB).2 hprod)
  have hdist := hB (gammaEquiv R hg hgenus hPresentation hΓ hfree hp b) hnorm
  rw [fromQCDistance_eq_two_mul_gamma R hg hgenus hPresentation hΓ hfree hp]
  linarith

/-- The actual Bers map is a homeomorphism from the full-log QC metric space
onto its actual bounded connected open coordinate image. -/
def fromQCBersCoordinateHomeomorph :
    let : MetricSpace (TeichmullerSpace.{u, u} R) :=
      fromQCMetricSpace R hg hgenus hPresentation
    TeichmullerSpace.{u, u} R ≃ₜ
      range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) := by
  let : MetricSpace (TeichmullerSpace.{u, u} R) :=
    fromQCMetricSpace R hg hgenus hPresentation
  let E : TeichmullerSpace.{u, u} R ≃
      range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) :=
    Equiv.ofInjective (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)
      (bersCoordinates_injective R hg hgenus hPresentation hΓ hfree hp)
  refine { E with continuous_toFun := ?_, continuous_invFun := ?_ }
  · exact (continuous_bersCoordinates_fromQC R hg hgenus
      hPresentation hΓ hfree hp).subtype_mk (fun a => mem_range_self a)
  · apply continuous_iff_continuousAt.2
    intro y
    apply Metric.continuousAt_iff.2
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ :=
      bersCoordinates_inverse_epsilon R hg hgenus hPresentation hΓ hfree hp (E.symm y) hε
    refine ⟨δ, hδ, fun z hz => ?_⟩
    rw [dist_comm]
    change fromQCDistance R (E.symm y) (E.symm z) < ε
    apply hbound (E.symm z)
    have hy : bersCoordinates R hg hgenus hPresentation hΓ hfree hp (E.symm y) =
        (y : Fin (3 * g - 3) → ℂ) :=
      congrArg Subtype.val (E.apply_symm_apply y)
    have hzc : bersCoordinates R hg hgenus hPresentation hΓ hfree hp (E.symm z) =
        (z : Fin (3 * g - 3) → ℂ) :=
      congrArg Subtype.val (E.apply_symm_apply z)
    rw [hzc, hy]
    simpa only [Subtype.dist_eq, dist_eq_norm] using hz

/-- Equality of the topology generated by the actual full-log QC metric and
that induced by the actual Bers coordinates. No third topology is involved. -/
theorem fromQCMetricSpace_topology_eq_bersTopology :
    (fromQCMetricSpace R hg hgenus hPresentation).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      bersTopology R hg hgenus hPresentation hΓ hfree hp := by
  let : MetricSpace (TeichmullerSpace.{u, u} R) :=
    fromQCMetricSpace R hg hgenus hPresentation
  let H := fromQCBersCoordinateHomeomorph R hg hgenus hPresentation hΓ hfree hp
  have he : Topology.IsEmbedding
      (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) := by
    change Topology.IsEmbedding (Subtype.val ∘ H)
    exact Topology.IsEmbedding.subtypeVal.comp H.isEmbedding
  exact he.isInducing.eq_induced

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
