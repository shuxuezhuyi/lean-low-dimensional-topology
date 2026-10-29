module

public import LowDimensionalTopology.Geometry.Surfaces.MeasuredFoliationProjectivization
public import LowDimensionalTopology.Geometry.Surfaces.MeasuredFoliationIntersectionModel
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.ENNReal.Real

/-!
# One positive scale in actual measured-foliation intersection coordinates

The same actual partition and original curve represent every scaled cost.
Positive finite multiplication preserves even empty extended-real infima.
The resulting common coordinate factor descends to the actual projective quotient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The same arc or leaf piece has precisely its original cost times one common factor. -/
theorem measuredFoliationRegularPieceCost_scale_iff
    (a : Set.Ioi (0 : ℝ)) (F : SingularMeasuredFoliation R)
    {x y : X} (γ : Path x y) (m : ℝ≥0∞) :
    IsMeasuredFoliationRegularPieceCost (scaleSingularMeasuredFoliation a F) γ m ↔
      ∃ u : ℝ≥0∞, IsMeasuredFoliationRegularPieceCost F γ u ∧
        m = ENNReal.ofReal a.val * u := by
  constructor
  · rintro (⟨α, hα, hm⟩ | ⟨hleaf, hm⟩)
    · refine ⟨F.transverse.measure α Set.univ, Or.inl ⟨α, hα, rfl⟩, ?_⟩
      simpa only [scaleSingularMeasuredFoliation, Measure.smul_apply, smul_eq_mul] using hm
    · exact ⟨0, Or.inr ⟨hleaf, rfl⟩, by simpa only [mul_zero] using hm⟩
  · rintro ⟨u, hu, hm⟩
    rcases hu with ⟨α, hα, hu⟩ | ⟨hleaf, hu⟩
    · refine Or.inl ⟨α, hα, ?_⟩
      simpa only [scaleSingularMeasuredFoliation, Measure.smul_apply, smul_eq_mul, hu]
        using hm
    · exact Or.inr ⟨hleaf, by simpa only [hu, mul_zero] using hm⟩

/-- All actual partition costs scale, retaining the same original circle and partition. -/
theorem measuredFoliationRegularCosts_scale_iff
    (a : Set.Ioi (0 : ℝ)) (F : nondegenerateMeasuredFoliation R)
    (L : EssentialSimpleCircle X) (m : ℝ≥0∞) :
    m ∈ measuredFoliationRegularCosts (scaleNondegenerateMeasuredFoliation a F) L ↔
      ∃ u ∈ measuredFoliationRegularCosts F L, m = ENNReal.ofReal a.val * u := by
  constructor
  · rintro ⟨P, w, hpieces, rfl⟩
    have hcosts : ∀ i : Fin P.n, ∃ u : ℝ≥0∞,
        IsMeasuredFoliationRegularPieceCost F.val (measuredFoliationLoopPiece L P i) u ∧
          w i = ENNReal.ofReal a.val * u := fun i =>
      (measuredFoliationRegularPieceCost_scale_iff a F.val _ (w i)).mp (hpieces i)
    choose u hu hwu using hcosts
    refine ⟨∑ i, u i, ⟨P, u, hu, rfl⟩, ?_⟩
    have hsum : (∑ i : Fin P.n, w i) = ∑ i : Fin P.n, ENNReal.ofReal a.val * u i :=
      Finset.sum_congr rfl (fun i _ => hwu i)
    simpa only [Finset.mul_sum] using hsum
  · rintro ⟨u, ⟨P, w, hpieces, hu⟩, hm⟩
    refine ⟨P, fun i => ENNReal.ofReal a.val * w i, fun i => ?_, ?_⟩
    · exact (measuredFoliationRegularPieceCost_scale_iff a F.val _ _).mpr
        ⟨w i, hpieces i, rfl⟩
    · simpa only [hu, Finset.mul_sum] using hm

/-- The raw infimum scales faithfully, including empty fibers and infinite costs. -/
theorem measuredFoliationRegularIntersection_scale
    (a : Set.Ioi (0 : ℝ)) (F : nondegenerateMeasuredFoliation R)
    (β : EssentialSimpleFreeClass X) :
    measuredFoliationRegularIntersection (scaleNondegenerateMeasuredFoliation a F) β =
      ENNReal.ofReal a.val * measuredFoliationRegularIntersection F β := by
  let c : ℝ≥0∞ := ENNReal.ofReal a.val
  let S : Set ℝ≥0∞ := {m | ∃ L : EssentialSimpleCircle X,
    L.freeClass = β ∧ m ∈ measuredFoliationRegularCosts F L}
  have hset : {m | ∃ L : EssentialSimpleCircle X, L.freeClass = β ∧
      m ∈ measuredFoliationRegularCosts (scaleNondegenerateMeasuredFoliation a F) L} =
        (fun u => c * u) '' S := by
    ext m
    constructor
    · rintro ⟨L, hL, hm⟩
      obtain ⟨u, hu, hmu⟩ := (measuredFoliationRegularCosts_scale_iff a F L m).mp hm
      exact ⟨u, ⟨L, hL, hu⟩, hmu.symm⟩
    · rintro ⟨u, ⟨L, hL, hu⟩, hmu⟩
      exact ⟨L, hL, (measuredFoliationRegularCosts_scale_iff a F L m).mpr
        ⟨u, hu, hmu.symm⟩⟩
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr a.property).ne'
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  change sInf {m | ∃ L : EssentialSimpleCircle X, L.freeClass = β ∧
    m ∈ measuredFoliationRegularCosts (scaleNondegenerateMeasuredFoliation a F) L} = c * sInf S
  rw [hset, sInf_image', sInf_eq_iInf', ENNReal.mul_iInf_of_ne hc0 hctop]

variable (R)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
variable (hCurve : Unproved.Surfaces.ClosedCurveIntersectionGeometry R hg hgenus)
variable (H : Unproved.Surfaces.OriginalMeasuredFoliationIntersectionGeometry R hg hgenus hCurve)

/-- One common real factor scales every actual quotient-spectrum coordinate. -/
theorem measuredFoliationIntersectionSpectrum_scale
    (a : Set.Ioi (0 : ℝ)) (q : NondegenerateMeasuredFoliationQuotient R)
    (β : EssentialSimpleFreeClass X) :
    ((measuredFoliationIntersectionSpectrum R hg hgenus hCurve H
      (scaleNondegenerateMeasuredFoliationQuotient a q)).val β : ℝ) =
        a.val * ((measuredFoliationIntersectionSpectrum R hg hgenus hCurve H q).val β : ℝ) := by
  refine Quotient.inductionOn q ?_
  intro F
  change ((measuredFoliationIntersectionSpectrum R hg hgenus hCurve H
    (nondegenerateMeasuredFoliationQuotientMk (scaleNondegenerateMeasuredFoliation a F))).val β :
      ℝ) = a.val * ((measuredFoliationIntersectionSpectrum R hg hgenus hCurve H
        (nondegenerateMeasuredFoliationQuotientMk F)).val β : ℝ)
  have hcoord : ((measuredFoliationIntersectionSpectrum R hg hgenus hCurve H
      (nondegenerateMeasuredFoliationQuotientMk (scaleNondegenerateMeasuredFoliation a F))).val β :
        ℝ≥0∞) = ENNReal.ofReal a.val *
          ((measuredFoliationIntersectionSpectrum R hg hgenus hCurve H
            (nondegenerateMeasuredFoliationQuotientMk F)).val β : ℝ≥0∞) := by
    rw [measuredFoliationIntersectionSpectrum_apply,
      measuredFoliationIntersectionSpectrum_apply, measuredFoliationRegularIntersection_scale]
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal a.property.le] using congrArg ENNReal.toReal hcoord

/-- Actual common scaling gives the same projective intersection profile. -/
theorem projectivize_measuredFoliationIntersectionSpectrum_scale
    (a : Set.Ioi (0 : ℝ)) (q : NondegenerateMeasuredFoliationQuotient R) :
    projectivizeNonnegativeSpectrum (measuredFoliationIntersectionSpectrum R hg hgenus hCurve H
      (scaleNondegenerateMeasuredFoliationQuotient a q)) =
        projectivizeNonnegativeSpectrum
          (measuredFoliationIntersectionSpectrum R hg hgenus hCurve H q) := by
  apply (projectivizeNonnegativeSpectrum_eq_iff _ _).mpr
  exact ⟨a.val, a.property, fun β =>
    measuredFoliationIntersectionSpectrum_scale R hg hgenus hCurve H a q β⟩

/-- Every finite chain of actual projective scaling steps preserves the actual ray. -/
theorem projectiveMeasuredFoliationIntersectionSpectrum_eq_of_eqvGen
    {q r : NondegenerateMeasuredFoliationQuotient R}
    (h : Relation.EqvGen (measuredFoliationProjectiveStep (R := R)) q r) :
    projectivizeNonnegativeSpectrum (measuredFoliationIntersectionSpectrum R hg hgenus hCurve H q) =
      projectivizeNonnegativeSpectrum (measuredFoliationIntersectionSpectrum R hg hgenus hCurve H r)
      := by
  induction h with
  | rel q _ h =>
    obtain ⟨a, rfl⟩ := h
    exact (projectivize_measuredFoliationIntersectionSpectrum_scale R hg hgenus hCurve H a q).symm
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The original measured-foliation projective quotient carries its actual spectrum ray. -/
def projectiveMeasuredFoliationIntersectionSpectrum :
    ProjectiveNondegenerateMeasuredFoliationQuotient R → ProjectiveNonnegativeSpectrum X :=
  Quotient.lift
    (fun q => projectivizeNonnegativeSpectrum
      (measuredFoliationIntersectionSpectrum R hg hgenus hCurve H q))
    (fun _ _ h => projectiveMeasuredFoliationIntersectionSpectrum_eq_of_eqvGen
      R hg hgenus hCurve H h)

/-- The map uses the same literal quotient representative and every one of its coordinates. -/
theorem projectiveMeasuredFoliationIntersectionSpectrum_mk
    (q : NondegenerateMeasuredFoliationQuotient R) :
    projectiveMeasuredFoliationIntersectionSpectrum R hg hgenus hCurve H
      (projectivizeNondegenerateMeasuredFoliation q) =
        projectivizeNonnegativeSpectrum
          (measuredFoliationIntersectionSpectrum R hg hgenus hCurve H q) := rfl

end LowDimensionalTopology.Geometry.Surfaces
