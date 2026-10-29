/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicLength
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableSubarcs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.Compact

/-!
# Arclength phase between two feet on an oriented simple cuff

The supplied periodic geodesic fixes the orientation. Its parameter is used
to locate the two actual feet; their displacement uses full original-atlas
BV hyperbolic prefix lengths. Passing to the arclength quotient and its
canonical unit-circle map gives the normalized phase.

The construction concerns this given oriented parametrization and these
given feet. No family of target seams or global real branch is selected.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped unitInterval ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces

variable {Y : Type} [TopologicalSpace Y] {R : RiemannSurface Y}
variable {B : HyperbolicSurfaceModel R}

/-- The actual original geodesic prefix, with only an affine change to the
unit parameter interval. The given parametrization may be singular. -/
def originalCuffPrefixPiece (q : OriginalClosedGeodesic B) (r : I) :
    RiemannSurfaceRectifiableCurvePiece R :=
  RiemannSurfaceRectifiableCurvePiece.ofInterval q.curve q.continuous 0 r r.property.1 (by
    simpa only [Function.comp_id] using
      q.chartwiseBVOn_period.comp_monotone id continuousOn_id
        (monotone_id.monotoneOn (Icc (0 : ℝ) (r : ℝ)))
        (show MapsTo id (Icc (0 : ℝ) (r : ℝ)) (Icc (0 : ℝ) 1) from
          fun _ ht => ⟨ht.1, ht.2.trans r.property.2⟩))

/-- Each actual prefix has finite hyperbolic BV length. Compactness of its
covering lift bounds the density on its actual arclength factor. -/
theorem originalCuffPrefixPiece_length_ne_top (q : OriginalClosedGeodesic B) (r : I) :
    B.rectifiableCurveLength (originalCuffPrefixPiece q r) ≠ ∞ := by
  let p := originalCuffPrefixPiece q r
  let c := B.rectifiableCurveLift p
  obtain ⟨ha, hb, hpos, _hproj⟩ := B.rectifiableCurveLift_spec p
  have hc : ContinuousOn c.curve (Icc (0 : ℝ) 1) := by
    simpa only [c, ha, hb] using c.continuous
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, le_rfl, zero_le_one⟩)
    (Complex.continuous_im.comp_continuousOn hc)
  have hm : 0 < (c.curve t₀).im := hpos t₀ ht₀
  obtain ⟨_hL, _hclockCont, _hclockMono, _hclockZero, hclockImage⟩ := c.clock_spec
  have hbound : ∀ s ∈ Ioo (0 : ℝ) c.euclideanLength,
      ENNReal.ofReal (1 / (c.arclengthFactor s).im) ≤
        ENNReal.ofReal (1 / (c.curve t₀).im) := by
    intro s hs
    have hs' : s ∈ c.clock '' Icc c.a c.b := by
      rw [hclockImage]
      exact ⟨hs.1.le, hs.2.le⟩
    obtain ⟨t, ht, hct⟩ := hs'
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [c, ha, hb] using ht
    have hfactor : c.curve t = c.arclengthFactor s := by
      simpa only [Function.comp_apply, hct] using c.arclengthFactor_spec.2.1 ht
    rw [← hfactor]
    exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le hm (hmin ht'))
  have hle : c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) ≤
      ∫⁻ _s in Ioo (0 : ℝ) c.euclideanLength,
        ENNReal.ofReal (1 / (c.curve t₀).im) := by
    apply lintegral_mono_ae
    exact ae_restrict_of_forall_mem measurableSet_Ioo hbound
  have hfinite : (∫⁻ _s in Ioo (0 : ℝ) c.euclideanLength,
      ENNReal.ofReal (1 / (c.curve t₀).im)) < ∞ := by
    rw [setLIntegral_const, Real.volume_Ioo]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  change c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) ≠ ∞
  exact ne_of_lt (hle.trans_lt hfinite)

/-- A foot on the given simple cuff has exactly one original parameter in
the half-open fundamental interval. -/
theorem originalCuffPointTime_existsUnique (q : OriginalClosedGeodesic B)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → Y))
    (c : range q.curve) :
    ∃! r : Ico (0 : ℝ) 1, q.curve r = c.val := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨a, ha⟩ := c.property
  let r := AddCircle.equivIco (1 : ℝ) 0 (a : AddCircle (1 : ℝ))
  have hr : (r : ℝ) ∈ Ico (0 : ℝ) 1 := by
    simpa only [zero_add] using r.property
  have hquot : ((r : ℝ) : AddCircle (1 : ℝ)) = (a : AddCircle (1 : ℝ)) := by
    exact AddCircle.coe_equivIco
  have hpoint : q.curve r = c.val := by
    calc
      q.curve r = q.periodic.lift ((r : ℝ) : AddCircle (1 : ℝ)) :=
        (q.periodic.lift_coe (r : ℝ)).symm
      _ = q.periodic.lift (a : AddCircle (1 : ℝ)) := congrArg q.periodic.lift hquot
      _ = q.curve a := q.periodic.lift_coe a
      _ = c.val := ha
  refine ⟨⟨r, hr⟩, hpoint, ?_⟩
  intro s hs
  apply Subtype.ext
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ))
    (by simpa only [zero_add] using s.property)
    (by simpa only [zero_add] using hr)).mp
  apply hq
  calc
    q.periodic.lift ((s : ℝ) : AddCircle (1 : ℝ)) = q.curve s := q.periodic.lift_coe s
    _ = c.val := hs
    _ = q.curve r := hpoint.symm
    _ = q.periodic.lift ((r : ℝ) : AddCircle (1 : ℝ)) :=
      (q.periodic.lift_coe (r : ℝ)).symm

/-- The unique half-open original parameter of the specified actual foot. -/
def originalCuffPointTime (q : OriginalClosedGeodesic B)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → Y))
    (c : range q.curve) : Ico (0 : ℝ) 1 :=
  (originalCuffPointTime_existsUnique q hq c).choose

theorem originalCuffPointTime_spec (q : OriginalClosedGeodesic B)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → Y))
    (c : range q.curve) : q.curve (originalCuffPointTime q hq c) = c.val :=
  (originalCuffPointTime_existsUnique q hq c).choose_spec.1

/-- The actual hyperbolic prefix length at the specified foot. Its finiteness
is supplied by the actual prefix-length theorem. -/
def originalCuffLengthCoordinate (q : OriginalClosedGeodesic B)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → Y))
    (c : range q.curve) : ℝ :=
  let u := originalCuffPointTime q hq c
  (B.rectifiableCurveLength
    (originalCuffPrefixPiece q ⟨u, u.property.1, u.property.2.le⟩)).toReal

/-- Signed hyperbolic arclength from the first foot to the second, modulo the
full cuff length, in the direction fixed by the supplied periodic geodesic. -/
def originalCuffSignedDisplacement (q : OriginalClosedGeodesic B)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → Y))
    (c₀ c₁ : range q.curve) : AddCircle q.length.toReal :=
  ((originalCuffLengthCoordinate q hq c₁ -
    originalCuffLengthCoordinate q hq c₀ : ℝ) : AddCircle q.length.toReal)

/-- The canonical normalized angular phase of that same arclength class. -/
def originalCuffTwistPhase (q : OriginalClosedGeodesic B)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → Y))
    (c₀ c₁ : range q.curve) : Circle :=
  AddCircle.toCircle (originalCuffSignedDisplacement q hq c₀ c₁)

theorem originalCuffSignedDisplacement_self (q : OriginalClosedGeodesic B)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → Y))
    (c : range q.curve) : originalCuffSignedDisplacement q hq c c = 0 := by
  simp only [originalCuffSignedDisplacement, sub_self, AddCircle.coe_zero]

theorem originalCuffSignedDisplacement_reverse (q : OriginalClosedGeodesic B)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → Y))
    (c₀ c₁ : range q.curve) :
    originalCuffSignedDisplacement q hq c₁ c₀ =
      -originalCuffSignedDisplacement q hq c₀ c₁ := by
  simp only [originalCuffSignedDisplacement, AddCircle.coe_sub, neg_sub]

theorem originalCuffTwistPhase_self (q : OriginalClosedGeodesic B)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → Y))
    (c : range q.curve) : originalCuffTwistPhase q hq c c = 1 := by
  simp only [originalCuffTwistPhase, originalCuffSignedDisplacement_self,
    AddCircle.toCircle_zero]

theorem originalCuffTwistPhase_reverse (q : OriginalClosedGeodesic B)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → Y))
    (c₀ c₁ : range q.curve) :
    originalCuffTwistPhase q hq c₁ c₀ = (originalCuffTwistPhase q hq c₀ c₁)⁻¹ := by
  exact (congrArg AddCircle.toCircle
      (originalCuffSignedDisplacement_reverse q hq c₀ c₁)).trans
    (AddCircle.toCircle_neg (originalCuffSignedDisplacement q hq c₀ c₁))

end LowDimensionalTopology.Geometry.Surfaces
