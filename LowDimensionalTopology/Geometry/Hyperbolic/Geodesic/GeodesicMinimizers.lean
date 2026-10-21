/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicSegments
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.MinimizingCurves
public import Mathlib.Tactic

/-!
# All minimizing piecewise C¹ curves

The class of admissible curves includes pauses. Accordingly the exact traversal
condition uses nondecreasing parameters and does not impose injectivity.
-/

@[expose] public section

open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- A genuine continuous nondecreasing traversal of a complete unit-speed h-line.
The scalar parameter may stay constant on an interval, as permitted for admissible C¹ pieces. -/
def C1CurvePiece.MonotoneGeodesic (c : C1CurvePiece) (γ : ℝ → ℍ) : Prop :=
  ∃ σ : ℝ → ℝ, ContinuousOn σ (Icc c.a c.b) ∧ MonotoneOn σ (Icc c.a c.b) ∧
    ∀ t ∈ Icc c.a c.b, c.curve t = γ (σ t)

/-- Every smooth piece traverses the same geodesic in the same direction. -/
def PiecewiseC1Curve.MonotoneGeodesic {z w : ℍ} (γ : ℝ → ℍ) : PiecewiseC1Curve z w → Prop
  | .nil _ => True
  | .cons p tail => p.MonotoneGeodesic γ ∧ tail.MonotoneGeodesic γ

/-- Exact normalization criterion for the full finite-piecewise-C¹ admissible class. -/
theorem PiecewiseC1Curve.length_eq_dist_iff_normalized {z w : ℍ} (c : PiecewiseC1Curve z w)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hr : (g • z).re = (g • w).re) (hi : (g • z).im ≤ (g • w).im) :
    c.length = dist z w ↔ (c.mapGLPos g hg).VerticalNondecreasing (g • z).re := by
  have h := (c.mapGLPos g hg).length_eq_dist_iff_verticalNondecreasing hr hi
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.mapGLPos_length,
    realGL_distance] using h

/-- The chart's inverse genuinely cancels its real Möbius normalizer. -/
theorem smul_normalizerGeodesic (g : GL (Fin 2) ℝ) (t : ℝ) :
    g • normalizerGeodesic g t = imaginaryAxisParam t := by
  exact smul_inv_smul g (imaginaryAxisParam t)

/-- The geometric monotone traversal criterion for one piece, including constant pieces. -/
theorem C1CurvePiece.mapGLPos_forwardVertical_iff_monotoneGeodesic (c : C1CurvePiece)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (hz : (g • c.curve c.a).re = 0) :
    (c.mapGLPos g hg).ForwardVertical ↔ c.MonotoneGeodesic (normalizerGeodesic g) := by
  constructor
  · intro h
    have hgeom := h.geometry
    let σ : ℝ → ℝ := fun t => Real.log (g • c.curve t).im
    have hr (t : ℝ) (ht : t ∈ Icc c.a c.b) : (g • c.curve t).re = 0 :=
      (hgeom.1 t ht).trans hz
    refine ⟨σ, ?_, ?_, ?_⟩
    · exact ((UpperHalfPlane.continuous_im.comp_continuousOn
        (c.mapGLPos g hg).continuous_curve).log (fun t _ => (g • c.curve t).im_ne_zero))
    · intro s hs t ht hst
      exact Real.log_le_log (g • c.curve s).im_pos (hgeom.2 hs ht hst)
    · intro t ht
      exact (normalizerGeodesic_parameter g (c.curve t) (hr t ht)).symm
  · rintro ⟨σ, _, hmono, heq⟩
    have hr (t : ℝ) (ht : t ∈ Icc c.a c.b) : (g • c.curve t).re = 0 := by
      rw [heq t ht, smul_normalizerGeodesic]
      rfl
    apply (c.mapGLPos g hg).forwardVertical_of_geometry
    · intro t ht
      exact (hr t ht).trans hz.symm
    · intro s hs t ht hst
      change (g • c.curve s).im ≤ (g • c.curve t).im
      rw [heq s hs, heq t ht, smul_normalizerGeodesic, smul_normalizerGeodesic]
      exact Real.exp_le_exp.mpr (hmono hs ht hst)

/-- Exact geometric traversal criterion for every finite number of smooth pieces. -/
theorem PiecewiseC1Curve.mapGLPos_forwardVertical_iff_monotoneGeodesic {z w : ℍ}
    (c : PiecewiseC1Curve z w) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hz : (g • z).re = 0) :
    (c.mapGLPos g hg).ForwardVertical ↔ c.MonotoneGeodesic (normalizerGeodesic g) := by
  revert hz
  induction c with
  | nil z => intro _; exact iff_of_true trivial trivial
  | @cons p w tail ih =>
    intro hz
    change (p.mapGLPos g hg).ForwardVertical ∧ (tail.mapGLPos g hg).ForwardVertical ↔
      p.MonotoneGeodesic (normalizerGeodesic g) ∧ tail.MonotoneGeodesic (normalizerGeodesic g)
    have hpiff := p.mapGLPos_forwardVertical_iff_monotoneGeodesic g hg hz
    constructor
    · rintro ⟨hp, ht⟩
      have hend : (g • p.curve p.b).re = 0 :=
        (hp.geometry.1 p.b (right_mem_Icc.mpr p.ordered)).trans hz
      exact ⟨hpiff.mp hp, (ih hend).mp ht⟩
    · rintro ⟨hp, ht⟩
      have hpf := hpiff.mpr hp
      have hend : (g • p.curve p.b).re = 0 :=
        (hpf.geometry.1 p.b (right_mem_Icc.mpr p.ordered)).trans hz
      exact ⟨hpf, (ih hend).mpr ht⟩

/--
Corrected in an actual normalizing h-line chart: precisely the continuous
nondecreasing traversals are minimizing, with no injectivity assumption excluding allowed pauses.
-/
theorem PiecewiseC1Curve.length_eq_dist_iff_monotoneGeodesic {z w : ℍ}
    (c : PiecewiseC1Curve z w) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hz : (g • z).re = 0) (hw : (g • w).re = 0) (hi : (g • z).im ≤ (g • w).im) :
    c.length = dist z w ↔ c.MonotoneGeodesic (normalizerGeodesic g) := by
  have h := (c.mapGLPos g hg).length_eq_dist_iff_forwardVertical (hz.trans hw.symm) hi
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.mapGLPos_length, realGL_distance,
    c.mapGLPos_forwardVertical_iff_monotoneGeodesic g hg hz] using h

/-- No normalizer is assumed to exist: every distinct endpoint pair has an actual one,
and the same complete geodesic chart characterizes all its admissible minimizing curves. -/
theorem exists_normalizer_minimizer_classification (z w : ℍ) (hzw : z ≠ w) :
    ∃ g : GL (Fin 2) ℝ, 0 < g.val.det ∧ Isometry (normalizerGeodesic g) ∧
      IsHalfPlaneHLine (range (normalizerGeodesic g)) ∧
      (g • z).re = 0 ∧ (g • w).re = 0 ∧ (g • z).im < (g • w).im ∧
      ∀ c : PiecewiseC1Curve z w,
        c.length = dist z w ↔ c.MonotoneGeodesic (normalizerGeodesic g) := by
  obtain ⟨a, b, g, _, _, _, hg, _, _, hz, hw, hi⟩ := exists_ordered_ideal_normalizer z w hzw
  exact ⟨g, hg, normalizerGeodesic_isometry g hg, normalizerGeodesic_isHLine g hg,
    hz, hw, hi, fun c => c.length_eq_dist_iff_monotoneGeodesic g hg hz hw hi.le⟩

/-- A finite-partition curve transformed without discarding its single global parametrization. -/
def PartitionedC1Curve.mapGLPos (c : PartitionedC1Curve) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.val.det) : PartitionedC1Curve where
  n := c.n
  times := c.times
  curve t := g • c.curve t
  velocity i t := ((g.val.det : ℂ) / (UpperHalfPlane.denom g (c.curve t)) ^ 2) * c.velocity i t
  ordered := c.ordered
  continuous_curve i hi := ((c.piece i hi).mapGLPos g hg).continuous_curve
  continuous_velocity i hi := ((c.piece i hi).mapGLPos g hg).continuous_velocity
  hasDerivWithin i hi := ((c.piece i hi).mapGLPos g hg).hasDerivWithin

/-- Transforming the global finite partition gives exactly the independently transformed C¹ pieces. -/
theorem PartitionedC1Curve.mapGLPos_piece (c : PartitionedC1Curve) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.val.det) (i : ℕ) (hi : i < c.n) :
    (c.mapGLPos g hg).piece i hi = (c.piece i hi).mapGLPos g hg := rfl

/-- Every original weighted-speed integral is preserved, before taking any path-distance infimum. -/
theorem PartitionedC1Curve.mapGLPos_integral_sum (c : PartitionedC1Curve) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.val.det) :
    (∑ i ∈ Finset.range c.n, ∫ t in c.times i..c.times (i + 1),
      weightedSpeed (c.mapGLPos g hg).curve ((c.mapGLPos g hg).velocity i) t) =
      ∑ i ∈ Finset.range c.n, ∫ t in c.times i..c.times (i + 1),
        weightedSpeed c.curve (c.velocity i) t := by
  apply Finset.sum_congr rfl
  intro i hi
  exact (c.piece i (Finset.mem_range.mp hi)).mapGLPos_length g hg

theorem PiecewiseC1Curve.append_monotoneGeodesic_iff {x y z : ℍ}
    (c : PiecewiseC1Curve x y) (d : PiecewiseC1Curve y z) (γ : ℝ → ℍ) :
    (c.append d).MonotoneGeodesic γ ↔ c.MonotoneGeodesic γ ∧ d.MonotoneGeodesic γ := by
  induction c with
  | nil _ => simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.append,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.MonotoneGeodesic]
  | cons p tail ih =>
    change p.MonotoneGeodesic γ ∧ (tail.append d).MonotoneGeodesic γ ↔
      (p.MonotoneGeodesic γ ∧ tail.MonotoneGeodesic γ) ∧ d.MonotoneGeodesic γ
    rw [ih d, and_assoc]

theorem PartitionedC1Curve.prefix_monotoneGeodesic_iff (c : PartitionedC1Curve)
    (γ : ℝ → ℍ) (k : ℕ) (hk : k ≤ c.n) :
    (c.prefix k hk).MonotoneGeodesic γ ↔ ∀ i (hi : i < k),
      (c.piece i (Nat.lt_of_lt_of_le hi hk)).MonotoneGeodesic γ := by
  induction k with
  | zero => simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PartitionedC1Curve.prefix,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.MonotoneGeodesic]
  | succ k ih =>
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PartitionedC1Curve.prefix]
    erw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.append_monotoneGeodesic_iff]
    rw [ih (Nat.le_trans (Nat.le_succ k) hk)]
    change (∀ i (hi : i < k), _) ∧ ((c.piece k _).MonotoneGeodesic γ ∧ True) ↔ _
    constructor
    · rintro ⟨h, hp, _⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hp
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self k)), h k (Nat.lt_succ_self k), trivial⟩

/-- The source's one global finite-partition curve, with its original raw integral sum,
satisfies precisely the same exact geometric minimizing criterion. -/
theorem PartitionedC1Curve.integral_sum_eq_dist_iff_monotoneGeodesic
    (c : PartitionedC1Curve) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hz : (g • c.curve (c.times 0)).re = 0) (hw : (g • c.curve (c.times c.n)).re = 0)
    (hi : (g • c.curve (c.times 0)).im ≤ (g • c.curve (c.times c.n)).im) :
    (∑ i ∈ Finset.range c.n, ∫ t in c.times i..c.times (i + 1),
      weightedSpeed c.curve (c.velocity i) t) =
        dist (c.curve (c.times 0)) (c.curve (c.times c.n)) ↔
      ∀ i (hi : i < c.n), (c.piece i hi).MonotoneGeodesic (normalizerGeodesic g) := by
  rw [← c.prefix_length c.n le_rfl,
    (c.prefix c.n le_rfl).length_eq_dist_iff_monotoneGeodesic g hg hz hw hi,
    c.prefix_monotoneGeodesic_iff (normalizerGeodesic g) c.n le_rfl]

/-- The actual point trace of a finite concatenation, including all joins and endpoints. -/
def PiecewiseC1Curve.trace {z w : ℍ} : PiecewiseC1Curve z w → Set ℍ
  | .nil z => {z}
  | .cons p tail => p.curve '' Icc p.a p.b ∪ tail.trace

theorem normalizerGeodesic_logHeight (g : GL (Fin 2) ℝ) (t : ℝ) :
    Real.log (g • normalizerGeodesic g t).im = t := by
  rw [smul_normalizerGeodesic]
  exact Real.log_exp t

/-- A monotone traversal of a complete actual h-line covers the entire interval between its ends. -/
theorem C1CurvePiece.MonotoneGeodesic.image_eq (c : C1CurvePiece) (g : GL (Fin 2) ℝ)
    (h : c.MonotoneGeodesic (normalizerGeodesic g)) :
    c.curve '' Icc c.a c.b = normalizerGeodesic g ''
      Icc (Real.log (g • c.curve c.a).im) (Real.log (g • c.curve c.b).im) := by
  obtain ⟨σ, hcont, hmono, heq⟩ := h
  have ha : Real.log (g • c.curve c.a).im = σ c.a := by
    rw [heq c.a (left_mem_Icc.mpr c.ordered), normalizerGeodesic_logHeight]
  have hb : Real.log (g • c.curve c.b).im = σ c.b := by
    rw [heq c.b (right_mem_Icc.mpr c.ordered), normalizerGeodesic_logHeight]
  rw [ha, hb, ← hcont.image_Icc_of_monotoneOn c.ordered hmono, image_image]
  apply Set.image_congr
  intro t ht
  exact heq t ht

theorem C1CurvePiece.MonotoneGeodesic.logHeight_mono (c : C1CurvePiece) (g : GL (Fin 2) ℝ)
    (h : c.MonotoneGeodesic (normalizerGeodesic g)) :
    Real.log (g • c.curve c.a).im ≤ Real.log (g • c.curve c.b).im := by
  obtain ⟨σ, _, hm, heq⟩ := h
  rw [heq c.a (left_mem_Icc.mpr c.ordered), heq c.b (right_mem_Icc.mpr c.ordered),
    normalizerGeodesic_logHeight, normalizerGeodesic_logHeight]
  exact hm (left_mem_Icc.mpr c.ordered) (right_mem_Icc.mpr c.ordered) c.ordered

theorem PiecewiseC1Curve.MonotoneGeodesic.logHeight_mono {z w : ℍ} (c : PiecewiseC1Curve z w)
    (g : GL (Fin 2) ℝ) (h : c.MonotoneGeodesic (normalizerGeodesic g)) :
    Real.log (g • z).im ≤ Real.log (g • w).im := by
  induction c with
  | nil _ => exact le_rfl
  | cons p tail ih => exact (C1CurvePiece.MonotoneGeodesic.logHeight_mono p g h.1).trans (ih h.2)

/-- The full trace covers exactly the endpoint interval, with no missing points or backtracking. -/
theorem PiecewiseC1Curve.MonotoneGeodesic.trace_eq {z w : ℍ} (c : PiecewiseC1Curve z w)
    (g : GL (Fin 2) ℝ) (hz : (g • z).re = 0)
    (h : c.MonotoneGeodesic (normalizerGeodesic g)) :
    c.trace = normalizerGeodesic g '' Icc (Real.log (g • z).im) (Real.log (g • w).im) := by
  revert hz h
  induction c with
  | nil z =>
    intro hz _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.trace, Icc_self, image_singleton,
      normalizerGeodesic_parameter g z hz]
  | cons p tail ih =>
    rintro hz ⟨hp, ht⟩
    obtain ⟨σ, hc, hm, heq⟩ := hp
    have hp' : p.MonotoneGeodesic (normalizerGeodesic g) := ⟨σ, hc, hm, heq⟩
    have hb : (g • p.curve p.b).re = 0 := by
      rw [heq p.b (right_mem_Icc.mpr p.ordered), smul_normalizerGeodesic]
      rfl
    change p.curve '' Icc p.a p.b ∪ tail.trace = _
    rw [C1CurvePiece.MonotoneGeodesic.image_eq p g hp', ih hb ht, ← image_union,
      Icc_union_Icc_eq_Icc (C1CurvePiece.MonotoneGeodesic.logHeight_mono p g hp')
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.MonotoneGeodesic.logHeight_mono tail g ht)]

/-- Every minimizing admissible curve has exactly the actual geometric closed h-segment as its trace. -/
theorem PiecewiseC1Curve.trace_eq_closedHSegment_of_minimizing {z w : ℍ}
    (c : PiecewiseC1Curve z w) (hzw : z ≠ w) (hmin : c.length = dist z w) :
    c.trace = closedHSegment z w := by
  obtain ⟨a, b, g, _, _, _, hg, _, _, hz, hw, hi⟩ := exists_ordered_ideal_normalizer z w hzw
  have htrav := (c.length_eq_dist_iff_monotoneGeodesic g hg hz hw hi.le).mp hmin
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.MonotoneGeodesic.trace_eq c g hz htrav]
  have heq := closedHSegment_eq_image_Icc
    (show IsHGeodesicParam (normalizerGeodesic g) from
      ⟨normalizerGeodesic_isometry g hg, normalizerGeodesic_isHLine g hg⟩)
    (Real.log_lt_log (g • z).im_pos hi)
  rw [normalizerGeodesic_parameter g z hz, normalizerGeodesic_parameter g w hw] at heq
  exact heq.symm

/-- Every distinct endpoint pair has a genuine chart in which the exact corrected criterion
includes both nondecreasing traversal and coverage of the entire closed h-segment. -/
theorem exists_geodesic_minimizer_classification_with_trace (z w : ℍ) (hzw : z ≠ w) :
    ∃ γ : ℝ → ℍ, IsHGeodesicParam γ ∧
      ∀ c : PiecewiseC1Curve z w, c.length = dist z w ↔
        c.MonotoneGeodesic γ ∧ c.trace = closedHSegment z w := by
  obtain ⟨g, hg, hγ, hline, hz, hw, hi, hclass⟩ := exists_normalizer_minimizer_classification z w hzw
  refine ⟨normalizerGeodesic g, ⟨hγ, hline⟩, ?_⟩
  intro c
  exact ⟨fun h => ⟨(hclass c).mp h, c.trace_eq_closedHSegment_of_minimizing hzw h⟩,
    fun h => (hclass c).mpr h.1⟩

/-- A nondegenerate constant C¹ piece is allowed by the original admissible curve class. -/
def constantPausePiece (z : ℍ) : C1CurvePiece where
  a := -1
  b := 0
  ordered := by norm_num
  curve _ := z
  velocity _ := 0
  continuous_curve := continuousOn_const
  continuous_velocity := continuousOn_const
  hasDerivWithin _ _ := hasDerivWithinAt_const _ _ _

theorem constantPausePiece_length (z : ℍ) : (constantPausePiece z).length = 0 := by
  simp [C1CurvePiece.length, weightedSpeed, constantPausePiece]

/-- Insert an actual constant interval before any admissible curve, retaining its weighted length. -/
def PiecewiseC1Curve.withPause {z w : ℍ} (c : PiecewiseC1Curve z w) : PiecewiseC1Curve z w :=
  .cons (constantPausePiece z) c

theorem PiecewiseC1Curve.withPause_length {z w : ℍ} (c : PiecewiseC1Curve z w) :
    c.withPause.length = c.length := by
  change (constantPausePiece z).length + c.length = c.length
  rw [constantPausePiece_length, zero_add]

/-- The permitted constant interval is explicitly noninjective on its actual parameter interval. -/
theorem constantPausePiece_not_injOn (z : ℍ) :
    ¬Set.InjOn (constantPausePiece z).curve (Icc (constantPausePiece z).a (constantPausePiece z).b) := by
  intro h
  have he := h (show (-1 : ℝ) ∈ Icc (constantPausePiece z).a (constantPausePiece z).b by
      change (-1 : ℝ) ∈ Icc (-1 : ℝ) 0; norm_num)
    (show (0 : ℝ) ∈ Icc (constantPausePiece z).a (constantPausePiece z).b by
      change (0 : ℝ) ∈ Icc (-1 : ℝ) 0; norm_num) rfl
  norm_num at he

/-- A formal counterexample to imposing injectivity on every admissible minimizing parametrization:
for any distinct endpoints, a genuine minimizing finite curve may contain a constant nonzero interval. -/
theorem exists_minimizing_curve_with_noninjective_pause (z w : ℍ) :
    ∃ c : PiecewiseC1Curve z w, c.withPause.length = dist z w ∧
      ¬Set.InjOn (constantPausePiece z).curve (Icc (-1 : ℝ) 0) := by
  obtain ⟨p, rfl, rfl, hp⟩ := exists_length_minimizing_piece z w
  let c := _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.cons p (.nil (p.curve p.b))
  refine ⟨c, ?_, constantPausePiece_not_injOn (p.curve p.a)⟩
  rw [c.withPause_length]
  exact (add_zero p.length).trans hp

/-- A single global parameter function that pauses until zero, then traverses a C¹ piece. -/
def pauseThenPieceCurve (p : C1CurvePiece) (t : ℝ) : ℍ :=
  if t ≤ 0 then p.curve 0 else p.curve t

theorem pauseThenPieceCurve_left (p : C1CurvePiece) :
    EqOn (pauseThenPieceCurve p) (fun _ => p.curve 0) (Icc (-1 : ℝ) 0) := by
  intro t ht
  exact ite_eq_left ht.2

theorem pauseThenPieceCurve_right (p : C1CurvePiece) :
    EqOn (pauseThenPieceCurve p) p.curve (Icc (0 : ℝ) 1) := by
  intro t ht
  by_cases ht0 : t ≤ 0
  · have he : t = 0 := le_antisymm ht0 ht.1
    subst t
    simp [pauseThenPieceCurve]
  · exact ite_eq_right ht0

/-- The pause is inserted in a true global finite-partition curve, rather than merely a list of paths. -/
def pauseThenPartitionedCurve (p : C1CurvePiece) (ha : p.a = 0) (hb : p.b = 1) :
    PartitionedC1Curve where
  n := 2
  times i := if i = 0 then -1 else if i = 1 then 0 else 1
  curve := pauseThenPieceCurve p
  velocity i t := if i = 0 then 0 else p.velocity t
  ordered i hi := by
    interval_cases i <;> norm_num
  continuous_curve i hi := by
    interval_cases i
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => p.curve 0)
        (Icc (-1 : ℝ) 0)).congr (pauseThenPieceCurve_left p)
    · simpa [ha, hb] using p.continuous_curve.congr
        (show EqOn (pauseThenPieceCurve p) p.curve (Icc p.a p.b) by
          simpa only [ha, hb] using pauseThenPieceCurve_right p)
  continuous_velocity i hi := by
    interval_cases i
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ)) (Icc (-1 : ℝ) 0))
    · simpa [ha, hb] using p.continuous_velocity
  hasDerivWithin i hi t ht := by
    interval_cases i
    · have ht' : t ∈ Icc (-1 : ℝ) 0 := by simpa using ht
      have he (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 0) :
          (pauseThenPieceCurve p u : ℂ) = (p.curve 0 : ℂ) :=
        congrArg UpperHalfPlane.coe (pauseThenPieceCurve_left p hu)
      simpa using (hasDerivWithinAt_const t (Icc (-1 : ℝ) 0) (p.curve 0 : ℂ)).congr_of_mem he ht'
    · have ht' : t ∈ Icc p.a p.b := by simpa [ha, hb] using ht
      have he (u : ℝ) (hu : u ∈ Icc p.a p.b) :
          (pauseThenPieceCurve p u : ℂ) = (p.curve u : ℂ) :=
        congrArg UpperHalfPlane.coe (pauseThenPieceCurve_right p (by simpa [ha, hb] using hu))
      simpa [ha, hb] using (p.hasDerivWithin t ht').congr_of_mem he ht'

/-- The actual global-curve weighted integral sum is unchanged by the nonzero pause interval. -/
theorem pauseThenPartitionedCurve_integral_sum (p : C1CurvePiece) (ha : p.a = 0) (hb : p.b = 1) :
    (∑ i ∈ Finset.range (pauseThenPartitionedCurve p ha hb).n,
      ∫ t in (pauseThenPartitionedCurve p ha hb).times i..
        (pauseThenPartitionedCurve p ha hb).times (i + 1),
        weightedSpeed (pauseThenPartitionedCurve p ha hb).curve
          ((pauseThenPartitionedCurve p ha hb).velocity i) t) = p.length := by
  norm_num only [pauseThenPartitionedCurve, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, ite_true, ite_false]
  have hz : (∫ t in (-1 : ℝ)..0, weightedSpeed (pauseThenPieceCurve p) (fun _ => 0) t) = 0 := by
    simp [weightedSpeed]
  rw [hz, zero_add]
  change (∫ t in (0 : ℝ)..1, weightedSpeed (pauseThenPieceCurve p) p.velocity t) = p.length
  rw [C1CurvePiece.length, ha, hb]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  rw [weightedSpeed, pauseThenPieceCurve_right p ht']
  rfl

/-- A single global admissible curve with a nonzero pause interval is not injective. -/
theorem pauseThenPartitionedCurve_not_injOn (p : C1CurvePiece) (ha : p.a = 0) (hb : p.b = 1) :
    ¬Set.InjOn (pauseThenPartitionedCurve p ha hb).curve (Icc (-1 : ℝ) 1) := by
  intro h
  have he := h (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
    (show (pauseThenPartitionedCurve p ha hb).curve (-1) =
      (pauseThenPartitionedCurve p ha hb).curve 0 by
      simp [pauseThenPartitionedCurve, pauseThenPieceCurve])
  norm_num at he

/-- The same actual nondecreasing geodesic traversal condition for disc C¹ pieces. -/
def DiscC1CurvePiece.MonotoneGeodesic (c : DiscC1CurvePiece) (γ : ℝ → 𝔻) : Prop :=
  ∃ σ : ℝ → ℝ, ContinuousOn σ (Icc c.a c.b) ∧ MonotoneOn σ (Icc c.a c.b) ∧
    ∀ t ∈ Icc c.a c.b, c.curve t = γ (σ t)

def DiscPiecewiseC1Curve.MonotoneGeodesic {z w : 𝔻} (γ : ℝ → 𝔻) :
    DiscPiecewiseC1Curve z w → Prop
  | .nil _ => True
  | .cons p tail => p.MonotoneGeodesic γ ∧ tail.MonotoneGeodesic γ

theorem DiscC1CurvePiece.toHalfPlane_monotoneGeodesic_iff (c : DiscC1CurvePiece) (γ : ℝ → ℍ) :
    c.toHalfPlane.MonotoneGeodesic γ ↔ c.MonotoneGeodesic (halfPlaneToDisc ∘ γ) := by
  constructor
  · rintro ⟨σ, hc, hm, heq⟩
    refine ⟨σ, hc, hm, ?_⟩
    intro t ht
    have he := congrArg halfPlaneToDisc (heq t ht)
    simpa only [DiscC1CurvePiece.toHalfPlane, halfPlaneToDisc_discToHalfPlane,
      Function.comp_def] using he
  · rintro ⟨σ, hc, hm, heq⟩
    refine ⟨σ, hc, hm, ?_⟩
    intro t ht
    have he := congrArg discToHalfPlane (heq t ht)
    simpa only [DiscC1CurvePiece.toHalfPlane, discToHalfPlane_halfPlaneToDisc,
      Function.comp_def] using he

theorem DiscPiecewiseC1Curve.toHalfPlane_monotoneGeodesic_iff {z w : 𝔻}
    (c : DiscPiecewiseC1Curve z w) (γ : ℝ → ℍ) :
    c.toHalfPlane.MonotoneGeodesic γ ↔ c.MonotoneGeodesic (halfPlaneToDisc ∘ γ) := by
  induction c with
  | nil _ => exact iff_of_true trivial trivial
  | cons p tail ih =>
    change p.toHalfPlane.MonotoneGeodesic γ ∧ tail.toHalfPlane.MonotoneGeodesic γ ↔
      p.MonotoneGeodesic (halfPlaneToDisc ∘ γ) ∧ tail.MonotoneGeodesic (halfPlaneToDisc ∘ γ)
    rw [p.toHalfPlane_monotoneGeodesic_iff, ih]

/-- The full disc admissible finite-piecewise class, for the genuine disc weighted integrals. -/
theorem DiscPiecewiseC1Curve.length_eq_dist_iff_monotoneGeodesic {z w : 𝔻}
    (c : DiscPiecewiseC1Curve z w) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hz : (g • discToHalfPlane z).re = 0) (hw : (g • discToHalfPlane w).re = 0)
    (hi : (g • discToHalfPlane z).im ≤ (g • discToHalfPlane w).im) :
    c.length = discPathDist z w ↔
      c.MonotoneGeodesic (halfPlaneToDisc ∘ normalizerGeodesic g) := by
  rw [← c.toHalfPlane_length, discPathDist_eq_halfPlane,
    c.toHalfPlane.length_eq_dist_iff_monotoneGeodesic g hg hz hw hi,
    c.toHalfPlane_monotoneGeodesic_iff]

/-- The actual disc point trace includes all pieces and joins. -/
def DiscPiecewiseC1Curve.trace {z w : 𝔻} : DiscPiecewiseC1Curve z w → Set 𝔻
  | .nil z => {z}
  | .cons p tail => p.curve '' Icc p.a p.b ∪ tail.trace

theorem DiscPiecewiseC1Curve.trace_eq_cayley_image_halfPlane {z w : 𝔻}
    (c : DiscPiecewiseC1Curve z w) : c.trace = halfPlaneToDisc '' c.toHalfPlane.trace := by
  induction c with
  | nil z => simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve.trace,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve.toHalfPlane,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.trace, halfPlaneToDisc_discToHalfPlane]
  | cons p tail ih =>
    change p.curve '' Icc p.a p.b ∪ tail.trace =
      halfPlaneToDisc '' (p.toHalfPlane.curve '' Icc p.a p.b ∪ tail.toHalfPlane.trace)
    rw [image_union, ← ih, image_image]
    have he : (fun t => halfPlaneToDisc (p.toHalfPlane.curve t)) = p.curve := by
      funext t
      exact halfPlaneToDisc_discToHalfPlane (p.curve t)
    rw [he]

/-- Actual disc minimizing curves cover exactly the geometric Cayley h-segment. -/
theorem DiscPiecewiseC1Curve.trace_eq_closedDiscHSegment_of_minimizing {z w : 𝔻}
    (c : DiscPiecewiseC1Curve z w) (hzw : z ≠ w) (hmin : c.length = discPathDist z w) :
    c.trace = closedDiscHSegment z w := by
  have hZW : discToHalfPlane z ≠ discToHalfPlane w := fun h => hzw (cayleyHomeomorph.symm.injective h)
  have hmin' : c.toHalfPlane.length = dist (discToHalfPlane z) (discToHalfPlane w) := by
    rw [c.toHalfPlane_length, ← discPathDist_eq_halfPlane]
    exact hmin
  rw [c.trace_eq_cayley_image_halfPlane,
    c.toHalfPlane.trace_eq_closedHSegment_of_minimizing hZW hmin', closedDiscHSegment_eq_cayley_image]

theorem verticalPiece_length_eq_dist (x p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (verticalPiece x p q hp hq).length = dist ((verticalPiece x p q hp hq).curve 0)
      ((verticalPiece x p q hp hq).curve 1) := by
  rw [verticalPiece_length, verticalPiece_start, verticalPiece_finish]
  have hr : (UpperHalfPlane.mk ⟨x, p⟩ hp).re = (UpperHalfPlane.mk ⟨x, q⟩ hq).re := rfl
  rw [UpperHalfPlane.dist_of_re_eq hr, Real.dist_eq]
  exact abs_sub_comm (Real.log q) (Real.log p)

/--
An explicit global finite-partition counterexample to an injectivity requirement:
the curve is constant on [-1,0], then goes from i to exp(1)i, and still has minimal genuine length.
-/
theorem exists_minimizing_partitioned_curve_with_noninjective_pause :
    ∃ c : PartitionedC1Curve, c.times 0 = -1 ∧ c.times c.n = 1 ∧
      c.curve (c.times 0) ≠ c.curve (c.times c.n) ∧
      (∑ i ∈ Finset.range c.n, ∫ t in c.times i..c.times (i + 1),
        weightedSpeed c.curve (c.velocity i) t) = dist (c.curve (c.times 0)) (c.curve (c.times c.n)) ∧
      ¬Set.InjOn c.curve (Icc (c.times 0) (c.times c.n)) := by
  let p := verticalPiece 0 1 (Real.exp 1) zero_lt_one (Real.exp_pos 1)
  let c := pauseThenPartitionedCurve p rfl rfl
  have hstart : c.curve (c.times 0) = p.curve 0 := by
    change pauseThenPieceCurve p (-1) = p.curve 0
    simp [pauseThenPieceCurve]
  have hfinish : c.curve (c.times c.n) = p.curve 1 := by
    change pauseThenPieceCurve p 1 = p.curve 1
    simp [pauseThenPieceCurve]
  have hne : p.curve 0 ≠ p.curve 1 := by
    intro he
    dsimp [p] at he
    rw [verticalPiece_start, verticalPiece_finish] at he
    have him := congrArg UpperHalfPlane.im he
    change 1 = Real.exp 1 at him
    have hgt : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  refine ⟨c, rfl, rfl, ?_, ?_, pauseThenPartitionedCurve_not_injOn p rfl rfl⟩
  · rwa [hstart, hfinish]
  · rw [hstart, hfinish]
    exact (pauseThenPartitionedCurve_integral_sum p rfl rfl).trans
      (verticalPiece_length_eq_dist 0 1 (Real.exp 1) zero_lt_one (Real.exp_pos 1))

/-- Every distinct disc endpoint pair admits a genuine Cayley geodesic chart characterizing all
actual disc piecewise-C¹ minimizers, with equality of the entire point trace. -/
theorem exists_disc_geodesic_minimizer_classification_with_trace (z w : 𝔻) (hzw : z ≠ w) :
    letI := discHyperbolicMetric
    ∃ γ : ℝ → 𝔻, Isometry γ ∧
      (∃ δ : ℝ → ℍ, IsHGeodesicParam δ ∧ γ = halfPlaneToDisc ∘ δ) ∧
      ∀ c : DiscPiecewiseC1Curve z w, c.length = discPathDist z w ↔
        c.MonotoneGeodesic γ ∧ c.trace = closedDiscHSegment z w := by
  let := discHyperbolicMetric
  have hZW : discToHalfPlane z ≠ discToHalfPlane w := fun h => hzw (cayleyHomeomorph.symm.injective h)
  obtain ⟨g, hg, hγ, hline, hz, hw, hi, _⟩ :=
    exists_normalizer_minimizer_classification (discToHalfPlane z) (discToHalfPlane w) hZW
  refine ⟨halfPlaneToDisc ∘ normalizerGeodesic g, cayley_isometry.comp hγ,
    ⟨normalizerGeodesic g, ⟨hγ, hline⟩, rfl⟩, ?_⟩
  intro c
  have hclass := c.length_eq_dist_iff_monotoneGeodesic g hg hz hw hi.le
  exact ⟨fun h => ⟨hclass.mp h, c.trace_eq_closedDiscHSegment_of_minimizing hzw h⟩,
    fun h => hclass.mpr h.1⟩

end

end LowDimensionalTopology.Geometry.Hyperbolic
