module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricStrongQuotientRealization
public import LowDimensionalTopology.Geometry.Teichmuller.Moduli
public import LowDimensionalTopology.Geometry.Teichmuller.MarkedMetricQuotient

/-!
# The original Moduli quotient and the full weak raw-metric quotient

An actual positive conformal reference automorphism between corresponding
metrics gives a genuine biholomorphic change of the marked targets. Thus the
original Moduli class maps injectively to the weak class of its corresponding
metric. The actual forgetful maps commute, so the full strong surjection and
the existing strong-to-weak surjection give full weak surjectivity under the
same explicit regularity hypothesis. The result is a set equivalence on the
existing native Moduli carrier, with its actual corresponding-metric map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u v
variable {X : Type u} [TopologicalSpace X]

namespace MarkedRiemannSurface

variable {R : ClosedRiemannSurface X}

/-- A genuine weak conformal witness gives a biholomorphic target map;
no homotopy-identity condition on that witness is needed. -/
theorem targetEquivalent_of_correspondingMetric_equivalent
    {M N : MarkedRiemannSurface.{u, v} R}
    (hMN : RawMetricEquivalent R M.correspondingMetric N.correspondingMetric) :
    TargetEquivalent M N := by
  let := R.toRiemannAtlas.toChartedSpace
  let := M.surface.toRiemannAtlas.toChartedSpace
  let := N.surface.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := M.surface.toRiemannAtlas.isRealManifold
  let := N.surface.toRiemannAtlas.isRealManifold
  obtain ⟨a, ha⟩ := hMN
  let f := SmoothSurfaceEquiv.trans
    (SmoothSurfaceEquiv.trans (SmoothSurfaceEquiv.symm M.marking) a.smooth) N.marking
  have hf : PreservesComplexOrientation M.surface.toRiemannAtlas
      N.surface.toRiemannAtlas f.toHomeomorph :=
    N.orientation_preserving.comp
      (a.orientation_preserving.comp
        (PreservesComplexOrientation.homeomorph_symm M.marking.toHomeomorph
          M.orientation_preserving) M.marking.toHomeomorph.symm.continuous)
      (a.toHomeomorph.continuous.comp M.marking.toHomeomorph.symm.continuous)
  have hconf : IsMetricConformal M.compatibleTargetMetric N.compatibleTargetMetric f :=
    (((IsRawMetricConformal.pullback M.marking M.compatibleTargetMetric.metric).symm).trans
      ha).trans
        (IsRawMetricConformal.pullback N.marking N.compatibleTargetMetric.metric)
  exact ⟨f.toHomeomorph, AtlasInducedMetric.analytic_of_metricConformal
    M.compatibleTargetMetric N.compatibleTargetMetric f hf hconf⟩

/-- Weak equivalence of the actual corresponding metrics is exactly the
original biholomorphic-target relation, without any marking homotopy. -/
theorem correspondingMetric_equivalent_iff (M N : MarkedRiemannSurface.{u, v} R) :
    RawMetricEquivalent R M.correspondingMetric N.correspondingMetric ↔
      TargetEquivalent M N := by
  constructor
  · exact targetEquivalent_of_correspondingMetric_equivalent
  · rintro ⟨h, han⟩
    exact correspondingMetric_equivalent_of_analytic_target M N h han

end MarkedRiemannSurface

namespace ModuliSpace

variable {R : ClosedRiemannSurface X}

/-- The original target class maps to the full weak conformal class of its
actual corresponding smooth metric on the original reference surface. -/
def toRawMetricQuotient : ModuliSpace.{u, v} R → RawMetricQuotient R :=
  Quotient.lift (fun M => RawMetricQuotient.mk M.correspondingMetric) (by
    intro M N hMN
    exact Quotient.sound ((MarkedRiemannSurface.correspondingMetric_equivalent_iff M N).2 hMN))

@[simp]
theorem toRawMetricQuotient_mk (M : MarkedRiemannSurface.{u, v} R) :
    toRawMetricQuotient (mk M) = RawMetricQuotient.mk M.correspondingMetric := rfl

/-- Equality of weak metric classes recovers the original Moduli class. -/
theorem toRawMetricQuotient_injective :
    Function.Injective (toRawMetricQuotient.{u, v} (R := R)) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro M N hMN
  apply Quotient.sound
  exact (MarkedRiemannSurface.correspondingMetric_equivalent_iff M N).1
    (Quotient.exact hMN)

/-- Forgetting the actual marking commutes with the actual raw metric maps. -/
theorem toRawMetricQuotient_forgetMarking (p : TeichmullerSpace.{u, v} R) :
    toRawMetricQuotient (TeichmullerSpace.forgetMarking p) =
      TeichmullerSpace.toRawMetricQuotient p := by
  refine Quotient.inductionOn p ?_
  intro M
  rfl

/-- Every class of every original raw metric is attained, using the actual
strong surjection and the original strong-to-weak forgetful map. -/
theorem toRawMetricQuotient_surjective_of_regularity
    (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity) :
    Function.Surjective (toRawMetricQuotient.{u, v} (R := R)) := by
  intro q
  obtain ⟨s, hs⟩ := RawMetricStrongQuotient.toWeak_surjective (R := R) q
  obtain ⟨p, hp⟩ :=
    TeichmullerSpace.toRawMetricStrongQuotient_surjective_of_regularity.{u, v} R hreg s
  refine ⟨TeichmullerSpace.forgetMarking p, ?_⟩
  rw [toRawMetricQuotient_forgetMarking]
  change RawMetricStrongQuotient.toWeak (TeichmullerSpace.toRawMetricStrongQuotient p) = q
  rw [hp]
  exact hs

/-- The original Moduli carrier and the full weak raw-metric quotient are
set-equivalent under precisely the existing explicit regularity hypothesis. -/
def equivRawMetricQuotient_of_regularity
    (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity) :
    ModuliSpace.{u, v} R ≃ RawMetricQuotient R :=
  Equiv.ofBijective (toRawMetricQuotient.{u, v} (R := R))
    ⟨toRawMetricQuotient_injective, toRawMetricQuotient_surjective_of_regularity R hreg⟩

/-- Its forward function is literally the corresponding-metric class map. -/
@[simp]
theorem equivRawMetricQuotient_of_regularity_apply
    (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (p : ModuliSpace.{u, v} R) :
    equivRawMetricQuotient_of_regularity R hreg p = toRawMetricQuotient p := rfl

end ModuliSpace
end LowDimensionalTopology.Geometry.Teichmuller
