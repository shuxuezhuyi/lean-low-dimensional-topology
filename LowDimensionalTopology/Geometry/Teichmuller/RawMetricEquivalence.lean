module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricConformality
public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricConformalScale

/-!
# Weak and strong conformal quotients of all original smooth metrics

The weak relation uses an arbitrary actual orientation-preserving smooth
reference automorphism. The strong relation restricts that same witness to
the existing subgroup of automorphisms freely homotopic to the identity.
Both relations retain the globally smooth exponential scale on the full
original tangent bundle. Their quotient types contain every raw smooth metric.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- Literal conformal pullback between arbitrary raw metrics, along an actual
orientation-preserving smooth reference automorphism. -/
def RawMetricConformal (g h : SmoothSurfaceMetric R.toRiemannSurface)
    (f : OrientedSurfaceAut R) : Prop := IsRawMetricConformal g h f.smooth

/-- Two arbitrary raw smooth metrics are equivalent if one actual
orientation-preserving smooth reference automorphism is conformal between them. -/
def RawMetricEquivalent (g h : SmoothSurfaceMetric R.toRiemannSurface) : Prop :=
  ∃ f : OrientedSurfaceAut R, RawMetricConformal R g h f

/-- Strong equivalence restricts the same conformal reference automorphism
to the actual homotopy-identity subgroup. -/
def RawMetricStronglyEquivalent (g h : SmoothSurfaceMetric R.toRiemannSurface) : Prop :=
  ∃ f : OrientedSurfaceAut R,
    f ∈ OrientedSurfaceAut.homotopyIdentitySubgroup R ∧ RawMetricConformal R g h f

/-- The actual identity is conformal for every raw smooth metric. -/
theorem RawMetricConformal.refl (g : SmoothSurfaceMetric R.toRiemannSurface) :
    RawMetricConformal R g g 1 := IsRawMetricConformal.refl g

/-- Inverting the actual automorphism reverses conformal pullback. -/
theorem RawMetricConformal.symm
    {g h : SmoothSurfaceMetric R.toRiemannSurface} {f : OrientedSurfaceAut R}
    (hf : RawMetricConformal R g h f) : RawMetricConformal R h g f⁻¹ :=
  IsRawMetricConformal.symm hf

/-- With the actual group convention, the composite witness is `j * f`,
whose underlying map is `j ∘ f`. -/
theorem RawMetricConformal.trans
    {g h k : SmoothSurfaceMetric R.toRiemannSurface} {f j : OrientedSurfaceAut R}
    (hf : RawMetricConformal R g h f) (hj : RawMetricConformal R h k j) :
    RawMetricConformal R g k (j * f) := IsRawMetricConformal.trans hf hj

/-- The weak relation is reflexive on the full raw metric space. -/
theorem RawMetricEquivalent.refl (g : SmoothSurfaceMetric R.toRiemannSurface) :
    RawMetricEquivalent R g g := ⟨1, RawMetricConformal.refl R g⟩

/-- The inverse automorphism witnesses symmetry of weak equivalence. -/
theorem RawMetricEquivalent.symm {g h : SmoothSurfaceMetric R.toRiemannSurface}
    (hgh : RawMetricEquivalent R g h) : RawMetricEquivalent R h g := by
  obtain ⟨f, hf⟩ := hgh
  exact ⟨f⁻¹, RawMetricConformal.symm R hf⟩

/-- Actual automorphism composition witnesses transitivity of weak equivalence. -/
theorem RawMetricEquivalent.trans {g h k : SmoothSurfaceMetric R.toRiemannSurface}
    (hgh : RawMetricEquivalent R g h) (hhk : RawMetricEquivalent R h k) :
    RawMetricEquivalent R g k := by
  obtain ⟨f, hf⟩ := hgh
  obtain ⟨j, hj⟩ := hhk
  exact ⟨j * f, RawMetricConformal.trans R hf hj⟩

/-- The actual identity belongs to the homotopy-identity subgroup. -/
theorem RawMetricStronglyEquivalent.refl (g : SmoothSurfaceMetric R.toRiemannSurface) :
    RawMetricStronglyEquivalent R g g :=
  ⟨1, (OrientedSurfaceAut.homotopyIdentitySubgroup R).one_mem,
    RawMetricConformal.refl R g⟩

/-- The inverse remains in the actual homotopy-identity subgroup. -/
theorem RawMetricStronglyEquivalent.symm {g h : SmoothSurfaceMetric R.toRiemannSurface}
    (hgh : RawMetricStronglyEquivalent R g h) : RawMetricStronglyEquivalent R h g := by
  obtain ⟨f, hfid, hf⟩ := hgh
  exact ⟨f⁻¹, (OrientedSurfaceAut.homotopyIdentitySubgroup R).inv_mem hfid,
    RawMetricConformal.symm R hf⟩

/-- Composition remains in the actual homotopy-identity subgroup. -/
theorem RawMetricStronglyEquivalent.trans
    {g h k : SmoothSurfaceMetric R.toRiemannSurface}
    (hgh : RawMetricStronglyEquivalent R g h) (hhk : RawMetricStronglyEquivalent R h k) :
    RawMetricStronglyEquivalent R g k := by
  obtain ⟨f, hfid, hf⟩ := hgh
  obtain ⟨j, hjid, hj⟩ := hhk
  exact ⟨j * f, (OrientedSurfaceAut.homotopyIdentitySubgroup R).mul_mem hjid hfid,
    RawMetricConformal.trans R hf hj⟩

/-- Strong equivalence refines weak equivalence without dropping its scale. -/
theorem RawMetricStronglyEquivalent.equivalent
    {g h : SmoothSurfaceMetric R.toRiemannSurface}
    (hgh : RawMetricStronglyEquivalent R g h) : RawMetricEquivalent R g h := by
  obtain ⟨f, _, hf⟩ := hgh
  exact ⟨f, hf⟩

/-- On the actual identity automorphism, full conformality is exactly equality
of the literal coefficient in every original complex chart. -/
theorem rawMetricConformal_one_iff_beltrami_eq
    (g h : SmoothSurfaceMetric R.toRiemannSurface) :
    RawMetricConformal R g h 1 ↔
      ∀ (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source),
        metricBeltramiInOriginalChart g e x hx = metricBeltramiInOriginalChart h e x hx := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change IsRawMetricConformal g h (SmoothSurfaceEquiv.refl R.toRiemannSurface) ↔ _
  constructor
  · rintro ⟨φ, hφ, hscale⟩
    apply (rawMetric_beltrami_eq_iff_smooth_scale g h).mpr
    refine ⟨φ, hφ, ?_⟩
    intro x a b
    have hs := hscale x a b
    change h.inner x
      (surfaceDifferential _ _ (SmoothSurfaceEquiv.refl R.toRiemannSurface) x a)
      (surfaceDifferential _ _ (SmoothSurfaceEquiv.refl R.toRiemannSurface) x b) = _ at hs
    simpa only [surfaceDifferential_refl_apply] using hs
  · intro hμ
    obtain ⟨φ, hφ, hscale⟩ := (rawMetric_beltrami_eq_iff_smooth_scale g h).mp hμ
    refine ⟨φ, hφ, ?_⟩
    intro x a b
    change h.inner x
      (surfaceDifferential _ _ (SmoothSurfaceEquiv.refl R.toRiemannSurface) x a)
      (surfaceDifferential _ _ (SmoothSurfaceEquiv.refl R.toRiemannSurface) x b) = _
    simpa only [surfaceDifferential_refl_apply] using hscale x a b

/-- Same actual coefficients give a strong-equivalence witness using the
actual identity reference automorphism. -/
theorem RawMetricStronglyEquivalent.of_beltrami_eq
    {g h : SmoothSurfaceMetric R.toRiemannSurface}
    (hμ : ∀ (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source),
      metricBeltramiInOriginalChart g e x hx = metricBeltramiInOriginalChart h e x hx) :
    RawMetricStronglyEquivalent R g h :=
  ⟨1, (OrientedSurfaceAut.homotopyIdentitySubgroup R).one_mem,
    (rawMetricConformal_one_iff_beltrami_eq R g h).mpr hμ⟩

/-- The exact weak equivalence relation on every original raw smooth metric. -/
def rawMetricSetoid : Setoid (SmoothSurfaceMetric R.toRiemannSurface) where
  r := RawMetricEquivalent R
  iseqv := ⟨RawMetricEquivalent.refl R, RawMetricEquivalent.symm R,
    RawMetricEquivalent.trans R⟩

/-- The exact strong equivalence relation on every original raw smooth metric. -/
def rawMetricStrongSetoid : Setoid (SmoothSurfaceMetric R.toRiemannSurface) where
  r := RawMetricStronglyEquivalent R
  iseqv := ⟨RawMetricStronglyEquivalent.refl R, RawMetricStronglyEquivalent.symm R,
    RawMetricStronglyEquivalent.trans R⟩

/-- The weak conformal quotient of the entire original smooth metric space. -/
def RawMetricQuotient := Quotient (rawMetricSetoid R)

/-- The strong conformal quotient of the entire original smooth metric space. -/
def RawMetricStrongQuotient := Quotient (rawMetricStrongSetoid R)

namespace RawMetricQuotient

variable {R}

/-- The weak conformal class of an arbitrary original smooth metric. -/
def mk (g : SmoothSurfaceMetric R.toRiemannSurface) : RawMetricQuotient R :=
  Quotient.mk (rawMetricSetoid R) g

/-- Equality in the weak quotient is precisely the original one-map relation. -/
theorem mk_eq_mk_iff (g h : SmoothSurfaceMetric R.toRiemannSurface) :
    mk g = mk h ↔ RawMetricEquivalent R g h := by
  constructor
  · exact Quotient.exact
  · intro hgh
    exact @Quotient.sound _ (rawMetricSetoid R) g h hgh

end RawMetricQuotient

namespace RawMetricStrongQuotient

variable {R}

/-- The strong conformal class of an arbitrary original smooth metric. -/
def mk (g : SmoothSurfaceMetric R.toRiemannSurface) : RawMetricStrongQuotient R :=
  Quotient.mk (rawMetricStrongSetoid R) g

/-- Equality in the strong quotient is precisely the original Diff₀ relation. -/
theorem mk_eq_mk_iff (g h : SmoothSurfaceMetric R.toRiemannSurface) :
    mk g = mk h ↔ RawMetricStronglyEquivalent R g h := by
  constructor
  · exact Quotient.exact
  · intro hgh
    exact @Quotient.sound _ (rawMetricStrongSetoid R) g h hgh

/-- Forgetting the restriction on the actual reference automorphism gives the
natural map from the strong quotient onto the weak quotient. -/
def toWeak : RawMetricStrongQuotient R → RawMetricQuotient R :=
  Quotient.lift RawMetricQuotient.mk (by
    intro g h hgh
    exact Quotient.sound (RawMetricStronglyEquivalent.equivalent R hgh))

@[simp]
theorem toWeak_mk (g : SmoothSurfaceMetric R.toRiemannSurface) :
    toWeak (mk g) = RawMetricQuotient.mk g := rfl

/-- Every weak class contains the image of its actual metric representative. -/
theorem toWeak_surjective : Function.Surjective (toWeak (R := R)) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro g
  exact ⟨mk g, rfl⟩

end RawMetricStrongQuotient
end LowDimensionalTopology.Geometry.Teichmuller
