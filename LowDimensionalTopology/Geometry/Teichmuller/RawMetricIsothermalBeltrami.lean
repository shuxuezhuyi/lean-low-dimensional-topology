module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricIsothermalRealization
public import LowDimensionalTopology.Geometry.Teichmuller.RealizedBeltrami

/-!
# The original metric coefficient as an actual Beltrami tensor

Use the actual isothermal marking and the existing continuous tensor model.
Every valid original chart reads the literal coefficient of the same raw
metric, so its coordinate law is a proved output. For an originally closed
reference, the same marked target supplies its existing uniform Banach
coefficient and compactness gives the strict uniform bound. No coefficient
space or metric quotient is replaced or classified here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X]

/-- The existing tensor of the actual positive smooth isothermal marking.
No compactness is needed to construct this continuous tensor. -/
def rawMetricIsothermalBeltramiTensor (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) : BeltramiDifferential R.toRiemannAtlas :=
  (rawMetricIsothermalMarking R hreg g).beltrami
    (rawMetricIsothermalMarking_preservesComplexOrientation R hreg g)

/-- Every valid original chart reads the literal Gram coefficient of the
same original raw metric, not merely of a selected family of charts. -/
theorem rawMetricIsothermalBeltramiTensor_coeff (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R) (x : X)
    (hx : x ∈ e.val.source) :
    (rawMetricIsothermalBeltramiTensor R hreg g).coeff e
      ⟨e.val x, e.val.map_source hx⟩ = metricBeltramiInOriginalChart g e x hx := by
  change (rawMetricIsothermalMarking R hreg g).rawBeltramiCoefficient e (e.val x) = _
  exact (rawMetricIsothermalMarking_metricBeltrami R hreg g e x hx).symm

/-- The same equality at every actual point of the original chart target. -/
theorem rawMetricIsothermalBeltramiTensor_coeff_target (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R) (z : e.val.target) :
    (rawMetricIsothermalBeltramiTensor R hreg g).coeff e z =
      metricBeltramiInOriginalChart g e (e.val.symm z.val) (e.val.map_target z.property) := by
  have h := rawMetricIsothermalBeltramiTensor_coeff R hreg g e
    (e.val.symm z.val) (e.val.map_target z.property)
  simpa only [e.val.right_inv z.property] using h

/-- The literal original metric coefficients obey the actual (-1,1) law
on every original chart overlap. -/
theorem rawMetricIsothermalBeltrami_source_change (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (e f : OriginalComplexChart R) (x : X)
    (hxe : x ∈ e.val.source) (hxf : x ∈ f.val.source) :
    metricBeltramiInOriginalChart g e x hxe =
      metricBeltramiInOriginalChart g f x hxf *
        conj (deriv (e.val.symm.trans f.val) (e.val x)) /
          deriv (e.val.symm.trans f.val) (e.val x) := by
  have h := (rawMetricIsothermalBeltramiTensor R hreg g).compatible e f x hxe hxf
  rw [rawMetricIsothermalBeltramiTensor_coeff R hreg g e x hxe,
    rawMetricIsothermalBeltramiTensor_coeff R hreg g f x hxf] at h
  exact h

/-- Closing the actual target does not change its marking tensor. -/
theorem rawMetricMarkedRiemannSurface_beltramiTensor (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    (rawMetricMarkedRiemannSurface R hreg g).beltramiTensor =
      rawMetricIsothermalBeltramiTensor R.toRiemannSurface hreg g := rfl

/-- The existing Banach coefficient of the same actual marked target.
Its carrier and norm are exactly the original continuous tensor Banach model. -/
def rawMetricIsothermalBeltramiCoefficient (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    BeltramiDifferential.BanachSpace R.toRiemannAtlas :=
  (rawMetricMarkedRiemannSurface R hreg g).beltramiCoefficient

/-- Compact Banach packaging changes none of the original tensor coefficients. -/
theorem rawMetricIsothermalBeltramiCoefficient_toTensor (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    BeltramiDifferential.toTensor (rawMetricIsothermalBeltramiCoefficient R hreg g) =
      rawMetricIsothermalBeltramiTensor R.toRiemannSurface hreg g := by
  let := R.compactSpace
  change BeltramiDifferential.toTensor
      (BeltramiDifferential.ofTensor (rawMetricMarkedRiemannSurface R hreg g).beltramiTensor) = _
  rw [BeltramiDifferential.toTensor_ofTensor, rawMetricMarkedRiemannSurface_beltramiTensor]

/-- Every actual original chart evaluates the Banach coefficient to the same
literal original metric formula at every valid original point. -/
theorem rawMetricIsothermalBeltramiCoefficient_apply (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source) :
    (rawMetricIsothermalBeltramiCoefficient R hreg g).val
      ⟨e, ⟨e.val x, e.val.map_source hx⟩⟩ = metricBeltramiInOriginalChart g e x hx := by
  change (BeltramiDifferential.toTensor (rawMetricIsothermalBeltramiCoefficient R hreg g)).coeff
    e ⟨e.val x, e.val.map_source hx⟩ = _
  rw [rawMetricIsothermalBeltramiCoefficient_toTensor]
  exact rawMetricIsothermalBeltramiTensor_coeff R.toRiemannSurface hreg g e x hx

/-- Original compactness and the actual positive marking give one uniform
strict subunit bound; it is not supplied as an extra premise. -/
theorem rawMetricIsothermalBeltramiCoefficient_norm_lt_one (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    ‖rawMetricIsothermalBeltramiCoefficient R hreg g‖ < 1 :=
  (rawMetricMarkedRiemannSurface R hreg g).beltramiCoefficient_norm_lt_one

end LowDimensionalTopology.Geometry.Teichmuller
