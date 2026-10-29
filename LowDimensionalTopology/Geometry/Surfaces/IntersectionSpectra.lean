module

public import LowDimensionalTopology.Geometry.Surfaces.GeometricIntersectionNumber
public import LowDimensionalTopology.Geometry.Surfaces.ProjectiveSpectra

/-!
# Weighted geometric intersection spectra on the original curve classes

The attained finite geometric intersection counts give a nonnegative spectrum
with at least one positive coordinate. Positive weighting preserves nonvanishing,
and the existing projective quotient identifies every positive weighting with
the original spectrum's ray.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
variable (hGeom : Unproved.Surfaces.ClosedCurveIntersectionGeometry R hg hgenus)

/-- The actual geometric intersection function, with the whole zero function excluded. -/
def intersectionSpectrum (a : EssentialSimpleFreeClass X) : NonzeroNonnegativeSpectrum X := by
  refine ⟨fun b => ⟨(geometricIntersectionNumber R hg hgenus hGeom a b : ℝ),
    Nat.cast_nonneg _⟩, ?_⟩
  intro hzero
  obtain ⟨b, hb⟩ := exists_geometricIntersectionNumber_pos R hg hgenus hGeom a
  have hpos : (0 : ℝ) < geometricIntersectionNumber R hg hgenus hGeom a b :=
    Nat.cast_pos.mpr hb
  have hcoord : (geometricIntersectionNumber R hg hgenus hGeom a b : ℝ) = 0 :=
    congrArg (fun f : NonnegativeSpectrum X => (f b : ℝ)) hzero
  exact (ne_of_gt hpos) hcoord

/-- Each real coordinate is the same finite natural geometric intersection count. -/
theorem intersectionSpectrum_apply (a b : EssentialSimpleFreeClass X) :
    ((intersectionSpectrum R hg hgenus hGeom a).val b : ℝ) =
      geometricIntersectionNumber R hg hgenus hGeom a b := rfl

/-- Multiply every original class coordinate by one common strictly positive real weight. -/
def weightedIntersectionSpectrum
    (p : Set.Ioi (0 : ℝ) × EssentialSimpleFreeClass X) : NonzeroNonnegativeSpectrum X := by
  let s := intersectionSpectrum R hg hgenus hGeom p.2
  refine ⟨fun b => ⟨p.1.val * (s.val b : ℝ),
    mul_nonneg p.1.property.le (s.val b).property⟩, ?_⟩
  intro hzero
  apply s.property
  funext b
  apply Subtype.ext
  have hb : p.1.val * (s.val b : ℝ) = 0 :=
    congrArg (fun f : NonnegativeSpectrum X => (f b : ℝ)) hzero
  exact (mul_eq_zero.mp hb).resolve_left (ne_of_gt p.1.property)

/-- The weighted coordinate is exactly the source weight times the original count. -/
theorem weightedIntersectionSpectrum_apply
    (w : Set.Ioi (0 : ℝ)) (a b : EssentialSimpleFreeClass X) :
    ((weightedIntersectionSpectrum R hg hgenus hGeom (w, a)).val b : ℝ) =
      w.val * geometricIntersectionNumber R hg hgenus hGeom a b := rfl

/-- Weight one recovers the unchanged original intersection spectrum. -/
@[simp] theorem weightedIntersectionSpectrum_one (a : EssentialSimpleFreeClass X) :
    weightedIntersectionSpectrum R hg hgenus hGeom (⟨1, zero_lt_one⟩, a) =
      intersectionSpectrum R hg hgenus hGeom a := by
  apply Subtype.ext
  funext b
  apply Subtype.ext
  change 1 * ((intersectionSpectrum R hg hgenus hGeom a).val b : ℝ) =
    ((intersectionSpectrum R hg hgenus hGeom a).val b : ℝ)
  exact one_mul _

/-- The ray lies in the existing projective nonnegative spectrum quotient. -/
def projectiveIntersectionSpectrum (a : EssentialSimpleFreeClass X) :
    ProjectiveNonnegativeSpectrum X :=
  projectivizeNonnegativeSpectrum (intersectionSpectrum R hg hgenus hGeom a)

/-- Every strictly positive weighting gives the same literal projective ray. -/
theorem projectivize_weightedIntersectionSpectrum
    (w : Set.Ioi (0 : ℝ)) (a : EssentialSimpleFreeClass X) :
    projectivizeNonnegativeSpectrum (weightedIntersectionSpectrum R hg hgenus hGeom (w, a)) =
      projectiveIntersectionSpectrum R hg hgenus hGeom a := by
  change projectivizeNonnegativeSpectrum
      (weightedIntersectionSpectrum R hg hgenus hGeom (w, a)) =
    projectivizeNonnegativeSpectrum (intersectionSpectrum R hg hgenus hGeom a)
  apply (projectivizeNonnegativeSpectrum_eq_iff _ _).mpr
  exact ⟨w.val, w.property, fun b => rfl⟩

end LowDimensionalTopology.Geometry.Surfaces
