module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricIsothermalRealization
public import LowDimensionalTopology.Geometry.Teichmuller.MarkedTargetUniverse
public import LowDimensionalTopology.Geometry.Teichmuller.MarkedMetricQuotient

/-!
# The full strong raw-metric quotient from actual isothermal markings

Every original raw metric gives an actual marked target in any requested
target universe. Its independently selected corresponding metric has the
same literal coefficients in all original charts, hence is strongly conformal
to the original metric by the actual identity automorphism. Thus the existing
marked-class map is onto the entire original raw-metric quotient. Its existing
injectivity gives a set equivalence with that very same forward map.

The existing regularity statement remains an explicit hypothesis. No weak
metric quotient, moduli classification or topological equivalence is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u v
variable {X : Type u} [TopologicalSpace X]

/-- The corresponding metric of the actual transported isothermal target
is strongly equivalent to the original raw metric, without metric-object equality. -/
theorem rawMetricIsothermalRetarget_correspondingMetric_stronglyEquivalent
    (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    RawMetricStronglyEquivalent R
      (MarkedRiemannSurface.retargetUniverse.{u, u, v}
        (rawMetricMarkedRiemannSurface R hreg g)).correspondingMetric g := by
  let M := rawMetricMarkedRiemannSurface R hreg g
  let N : MarkedRiemannSurface.{u, v} R :=
    MarkedRiemannSurface.retargetUniverse.{u, u, v} M
  change RawMetricStronglyEquivalent R N.correspondingMetric g
  apply RawMetricStronglyEquivalent.of_beltrami_eq R
  intro e x hx
  calc
    metricBeltramiInOriginalChart N.correspondingMetric e x hx =
        N.marking.rawBeltramiCoefficient e (e.val x) :=
      N.correspondingMetric_beltrami e x hx
    _ = M.marking.rawBeltramiCoefficient e (e.val x) :=
      MarkedRiemannSurface.retargetUniverse_rawBeltramiCoefficient.{u, u, v}
        M e ⟨e.val x, e.val.map_source hx⟩
    _ = metricBeltramiInOriginalChart g e x hx :=
      (rawMetricIsothermalMarking_metricBeltrami R.toRiemannSurface hreg g e x hx).symm

namespace TeichmullerSpace

/-- Every class of every original raw smooth metric is attained by the
existing marked-class map, in any requested target universe. -/
theorem toRawMetricStrongQuotient_surjective_of_regularity
    (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity) :
    Function.Surjective (toRawMetricStrongQuotient.{u, v} (R := R)) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro g
  let N : MarkedRiemannSurface.{u, v} R :=
    MarkedRiemannSurface.retargetUniverse.{u, u, v} (rawMetricMarkedRiemannSurface R hreg g)
  refine ⟨mk N, ?_⟩
  rw [toRawMetricStrongQuotient_mk]
  exact (RawMetricStrongQuotient.mk_eq_mk_iff N.correspondingMetric g).2
    (rawMetricIsothermalRetarget_correspondingMetric_stronglyEquivalent.{u, v} R hreg g)

/-- The original marked-class map gives a set equivalence with the full
strong quotient of all original smooth metrics, under the explicit regularity. -/
def equivRawMetricStrongQuotient_of_regularity
    (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity) :
    TeichmullerSpace.{u, v} R ≃ RawMetricStrongQuotient R :=
  Equiv.ofBijective (toRawMetricStrongQuotient.{u, v} (R := R))
    ⟨toRawMetricStrongQuotient_injective, toRawMetricStrongQuotient_surjective_of_regularity R hreg⟩

/-- Its forward function is literally the already defined original map. -/
@[simp]
theorem equivRawMetricStrongQuotient_of_regularity_apply
    (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (p : TeichmullerSpace.{u, v} R) :
    equivRawMetricStrongQuotient_of_regularity R hreg p = toRawMetricStrongQuotient p := rfl

end TeichmullerSpace
end LowDimensionalTopology.Geometry.Teichmuller
