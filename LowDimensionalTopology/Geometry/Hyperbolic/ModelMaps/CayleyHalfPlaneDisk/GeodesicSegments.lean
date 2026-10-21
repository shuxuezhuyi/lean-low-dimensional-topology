/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.Geodesic
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicMinimizers
public import Mathlib.Tactic

/-!
# Native disc segments and minimizing curves

The disc line in these statements is a genuine Euclidean circle or diameter
orthogonal to the unit circle. Segments use the source's actual compact-closure
connected-component criterion before comparison with the Cayley intervals.
-/

@[expose] public section

open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- A native Euclidean disc line has exactly the actual Cayley image carrier of its H presentation. -/
theorem DiscLine.carrier_eq_cayley_image_halfPlane (L : DiscLine) :
    L.carrier = halfPlaneToDisc '' L.toHalfPlane.carrier := by
  calc
    L.carrier = L.toHalfPlane.toDiscLine.carrier := congrArg DiscLine.carrier L.toHalfPlane_spec.symm
    _ = halfPlaneToDisc '' L.toHalfPlane.carrier := by
      rw [HalfPlaneLine.toDiscLine_carrier, HalfPlaneLine.discCarrier_eq_cayley_image]

/-- Every distinct endpoint pair on a native disc line admits a genuine ordered real Mobius normalizer
whose actual complete geodesic chart covers precisely that native carrier. -/
theorem DiscLine.exists_ordered_normalizer (L : DiscLine) {z w : 𝔻}
    (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    ∃ g : GL (Fin 2) ℝ, 0 < g.val.det ∧
      (g • discToHalfPlane z).re = 0 ∧ (g • discToHalfPlane w).re = 0 ∧
      (g • discToHalfPlane z).im < (g • discToHalfPlane w).im ∧
      range (halfPlaneToDisc ∘ normalizerGeodesic g) = L.carrier := by
  have hZW : discToHalfPlane z ≠ discToHalfPlane w := fun h => hzw (discToHalfPlane_injective h)
  obtain ⟨a, b, g, _, _, _, hg, _, _, hgz, hgw, hi⟩ :=
    exists_ordered_ideal_normalizer (discToHalfPlane z) (discToHalfPlane w) hZW
  have hrange : range (normalizerGeodesic g) = L.toHalfPlane.carrier :=
    isHLine_eq_of_two_points (normalizerGeodesic_isHLine g hg) L.toHalfPlane.isHLine hZW
      ⟨Real.log (g • discToHalfPlane z).im, normalizerGeodesic_parameter g _ hgz⟩
      ⟨Real.log (g • discToHalfPlane w).im, normalizerGeodesic_parameter g _ hgw⟩
      ((L.mem_carrier z).mp hz) ((L.mem_carrier w).mp hw)
  refine ⟨g, hg, hgz, hgw, hi, ?_⟩
  rw [range_comp, hrange, L.carrier_eq_cayley_image_halfPlane]

/-- A native disc line has an actual ordered, complete unit-speed parameter through any distinct pair. -/
theorem DiscLine.exists_ordered_param (L : DiscLine) {z w : 𝔻}
    (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    ∃ (δ : ℝ → ℍ) (s t : ℝ), IsHGeodesicParam δ ∧ s < t ∧
      halfPlaneToDisc (δ s) = z ∧ halfPlaneToDisc (δ t) = w ∧
      range (halfPlaneToDisc ∘ δ) = L.carrier := by
  obtain ⟨g, hg, hgz, hgw, hi, hrange⟩ := L.exists_ordered_normalizer hzw hz hw
  refine ⟨normalizerGeodesic g, Real.log (g • discToHalfPlane z).im,
    Real.log (g • discToHalfPlane w).im,
    ⟨normalizerGeodesic_isometry g hg, normalizerGeodesic_isHLine g hg⟩,
    Real.log_lt_log (g • discToHalfPlane z).im_pos hi, ?_, ?_, hrange⟩
  · rw [normalizerGeodesic_parameter g _ hgz, halfPlaneToDisc_discToHalfPlane]
  · rw [normalizerGeodesic_parameter g _ hgw, halfPlaneToDisc_discToHalfPlane]

/-- The native source definition: points in the punctured native h-line whose actual component
has compact closure in the actual disc model topology. -/
def nativeDiscOpenSegment (L : DiscLine) (z w : 𝔻) : Set 𝔻 :=
  {u | u ∈ L.carrier \ {z, w} ∧
    IsCompact (closure (connectedComponentIn (L.carrier \ {z, w}) u))}

/-- Add the two actual endpoints to obtain the native geometric closed segment. -/
def nativeDiscClosedSegment (L : DiscLine) (z w : 𝔻) : Set 𝔻 :=
  insert z (insert w (nativeDiscOpenSegment L z w))

/-- The source's native Euclidean/connected-component definition agrees with the actual Cayley segment. -/
theorem nativeDiscOpenSegment_eq (L : DiscLine) {z w : 𝔻}
    (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    nativeDiscOpenSegment L z w = openDiscHSegment z w := by
  obtain ⟨δ, s, t, hδ, hst, hs, ht, hrange⟩ := L.exists_ordered_param hzw hz hw
  let := discHyperbolicMetric
  have hγ := cayley_isometry.comp hδ.1
  ext u
  change (u ∈ L.carrier \ {z, w} ∧
    IsCompact (closure (connectedComponentIn (L.carrier \ {z, w}) u))) ↔ _
  rw [← hrange, ← hs, ← ht]
  constructor
  · rintro ⟨⟨⟨r, rfl⟩, hne⟩, hc⟩
    have hr : r ∈ puncturedParameterLine s t := by
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
      exact ⟨fun h => hne.1 (congrArg (halfPlaneToDisc ∘ δ) h),
        fun h => hne.2 (congrArg (halfPlaneToDisc ∘ δ) h)⟩
    exact (mem_openDiscHSegment_iff_compact_component hδ hst hr).mpr hc
  · intro hu
    have hu' := hu
    rw [openDiscHSegment_eq_image_Ioo hδ hst] at hu'
    obtain ⟨r, hr, rfl⟩ := hu'
    have hrP : r ∈ puncturedParameterLine s t := ⟨ne_of_gt hr.1, ne_of_lt hr.2⟩
    refine ⟨⟨mem_range_self r, ?_⟩,
      (mem_openDiscHSegment_iff_compact_component hδ hst hrP).mp hu⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hγ.injective.ne (ne_of_gt hr.1), hγ.injective.ne (ne_of_lt hr.2)⟩

/-- Closed H segments are exactly the open component with its two endpoints restored. -/
theorem closedHSegment_eq_insert_open {z w : ℍ} (hzw : z ≠ w) :
    closedHSegment z w = insert z (insert w (openHSegment z w)) := by
  ext u
  by_cases huz : u = z
  · subst u
    exact iff_of_true ((dist_triangle_eq_iff_mem_closedHSegment hzw).mp (by simp))
      (mem_insert z _)
  · by_cases huw : u = w
    · subst u
      exact iff_of_true ((dist_triangle_eq_iff_mem_closedHSegment hzw).mp (by simp))
        (mem_insert_of_mem z (mem_insert w _))
    · constructor
      · intro hu
        exact Or.inr (Or.inr ((mem_openHSegment_iff hzw).mpr ⟨hu, huz, huw⟩))
      · intro hu
        rcases hu with hu | hu | hu
        · exact (huz hu).elim
        · exact (huw hu).elim
        · exact ((mem_openHSegment_iff hzw).mp hu).1

theorem closedDiscHSegment_eq_insert_open {z w : 𝔻} (hzw : z ≠ w) :
    closedDiscHSegment z w = insert z (insert w (openDiscHSegment z w)) := by
  have hZW : discToHalfPlane z ≠ discToHalfPlane w := fun h => hzw (discToHalfPlane_injective h)
  rw [closedDiscHSegment_eq_cayley_image, closedHSegment_eq_insert_open hZW,
    image_insert_eq, image_insert_eq, halfPlaneToDisc_discToHalfPlane,
    halfPlaneToDisc_discToHalfPlane, ← openDiscHSegment_eq_cayley_image]

/-- The native closed segment agrees with the already proved actual geometric Cayley interval. -/
theorem nativeDiscClosedSegment_eq (L : DiscLine) {z w : 𝔻}
    (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    nativeDiscClosedSegment L z w = closedDiscHSegment z w := by
  rw [nativeDiscClosedSegment, nativeDiscOpenSegment_eq L hzw hz hw,
    ← closedDiscHSegment_eq_insert_open hzw]

/-- In the native Euclidean disc model, with the independently defined source segment. -/
theorem nativeDisc_triangle_eq_iff (L : DiscLine) {z w u : 𝔻}
    (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    discPathDist z u + discPathDist u w = discPathDist z w ↔ u ∈ nativeDiscClosedSegment L z w := by
  rw [nativeDiscClosedSegment_eq L hzw hz hw]
  exact disc_triangle_eq_iff_mem_closedDiscHSegment hzw

/-- The actual closed native h-segment is compact. -/
theorem isCompact_nativeDiscClosedSegment (L : DiscLine) {z w : 𝔻}
    (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    IsCompact (nativeDiscClosedSegment L z w) := by
  rw [nativeDiscClosedSegment_eq L hzw hz hw]
  exact isCompact_closedDiscHSegment hzw

/-- The actual disc-topological closure of the native open component restores both endpoints. -/
theorem closure_nativeDiscOpenSegment (L : DiscLine) {z w : 𝔻}
    (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    closure (nativeDiscOpenSegment L z w) = nativeDiscClosedSegment L z w := by
  rw [nativeDiscOpenSegment_eq L hzw hz hw, closure_openDiscHSegment hzw,
    nativeDiscClosedSegment_eq L hzw hz hw]

/-- All actual nonempty components in the native punctured line. -/
def nativeDiscPuncturedComponents (L : DiscLine) (z w : 𝔻) : Set (Set 𝔻) :=
  {C | ∃ u ∈ L.carrier \ {z, w}, C = connectedComponentIn (L.carrier \ {z, w}) u}

/-- Exactly three genuine connected components remain in a native h-line. -/
theorem ncard_nativeDiscPuncturedComponents (L : DiscLine) {z w : 𝔻}
    (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    (nativeDiscPuncturedComponents L z w).ncard = 3 := by
  obtain ⟨δ, s, t, hδ, hst, hs, ht, hrange⟩ := L.exists_ordered_param hzw hz hw
  let := discHyperbolicMetric
  change ({C | ∃ u ∈ L.carrier \ {z, w}, C = connectedComponentIn (L.carrier \ {z, w}) u} :
    Set (Set 𝔻)).ncard = 3
  rw [← hrange, ← hs, ← ht]
  exact ncard_hLinePuncturedComponents (cayley_isometry.comp hδ.1) hst

/-- Exactly one actual component has compact closure in the actual disc model topology. -/
theorem existsUnique_compact_nativeDisc_component (L : DiscLine) {z w : 𝔻}
    (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    ∃! C : Set 𝔻, C ∈ nativeDiscPuncturedComponents L z w ∧ IsCompact (closure C) := by
  obtain ⟨δ, s, t, hδ, hst, hs, ht, hrange⟩ := L.exists_ordered_param hzw hz hw
  let := discHyperbolicMetric
  change ∃! C : Set 𝔻, (∃ u ∈ L.carrier \ {z, w},
    C = connectedComponentIn (L.carrier \ {z, w}) u) ∧ IsCompact (closure C)
  rw [← hrange, ← hs, ← ht]
  exact existsUnique_compact_hLine_component (cayley_isometry.comp hδ.1) hst

/-- The source's between relation and half-open endpoint conventions in the native disc line. -/
def NativeDiscBetween (L : DiscLine) (z u w : 𝔻) : Prop := u ∈ nativeDiscOpenSegment L z w

def nativeDiscLeftClosedSegment (L : DiscLine) (z w : 𝔻) : Set 𝔻 :=
  nativeDiscClosedSegment L z w \ {w}

def nativeDiscRightClosedSegment (L : DiscLine) (z w : 𝔻) : Set 𝔻 :=
  nativeDiscClosedSegment L z w \ {z}

/--
Corrected for native disc h-lines: every admissible finite-piecewise C1 curve
is minimizing exactly when it traverses the actual native closed segment continuously without
backtracking, allowing the pauses admitted by the original curve class.
-/
theorem DiscLine.exists_minimizer_classification (L : DiscLine) {z w : 𝔻}
    (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    letI := discHyperbolicMetric
    ∃ γ : ℝ → 𝔻, Isometry γ ∧ range γ = L.carrier ∧
      ∀ c : DiscPiecewiseC1Curve z w, c.length = discPathDist z w ↔
        c.MonotoneGeodesic γ ∧ c.trace = nativeDiscClosedSegment L z w := by
  let := discHyperbolicMetric
  obtain ⟨g, hg, hgz, hgw, hi, hrange⟩ := L.exists_ordered_normalizer hzw hz hw
  refine ⟨halfPlaneToDisc ∘ normalizerGeodesic g,
    cayley_isometry.comp (normalizerGeodesic_isometry g hg), hrange, ?_⟩
  intro c
  have hclass := c.length_eq_dist_iff_monotoneGeodesic g hg hgz hgw hi.le
  constructor
  · intro h
    refine ⟨hclass.mp h, ?_⟩
    rw [c.trace_eq_closedDiscHSegment_of_minimizing hzw h, nativeDiscClosedSegment_eq L hzw hz hw]
  · exact fun h => hclass.mpr h.1

/-- A single global disc curve with a finite C¹ partition, retaining one-sided endpoint derivatives. -/
structure DiscPartitionedC1Curve where
  n : ℕ
  times : ℕ → ℝ
  curve : ℝ → 𝔻
  velocity : ℕ → ℝ → ℂ
  ordered : ∀ i < n, times i ≤ times (i + 1)
  continuous_curve : ∀ i < n, ContinuousOn curve (Icc (times i) (times (i + 1)))
  continuous_velocity : ∀ i < n, ContinuousOn (velocity i) (Icc (times i) (times (i + 1)))
  hasDerivWithin : ∀ i < n, ∀ t ∈ Icc (times i) (times (i + 1)),
    HasDerivWithinAt (fun s => (curve s : ℂ)) (velocity i t) (Icc (times i) (times (i + 1))) t

def DiscPartitionedC1Curve.piece (c : DiscPartitionedC1Curve) (i : ℕ) (hi : i < c.n) :
    DiscC1CurvePiece where
  a := c.times i
  b := c.times (i + 1)
  ordered := c.ordered i hi
  curve := c.curve
  velocity := c.velocity i
  continuous_curve := c.continuous_curve i hi
  continuous_velocity := c.continuous_velocity i hi
  hasDerivWithin := c.hasDerivWithin i hi

/-- Apply the actual inverse Cayley map to the entire global parametrization and its derivatives. -/
def DiscPartitionedC1Curve.toHalfPlane (c : DiscPartitionedC1Curve) : PartitionedC1Curve where
  n := c.n
  times := c.times
  curve t := discToHalfPlane (c.curve t)
  velocity i t := ((2 * Complex.I) / (1 - (c.curve t : ℂ)) ^ 2) * c.velocity i t
  ordered := c.ordered
  continuous_curve i hi := (c.piece i hi).toHalfPlane.continuous_curve
  continuous_velocity i hi := (c.piece i hi).toHalfPlane.continuous_velocity
  hasDerivWithin i hi := (c.piece i hi).toHalfPlane.hasDerivWithin

theorem DiscPartitionedC1Curve.toHalfPlane_piece (c : DiscPartitionedC1Curve)
    (i : ℕ) (hi : i < c.n) : c.toHalfPlane.piece i hi = (c.piece i hi).toHalfPlane := rfl

/-- Preserve the original global curve's actual weighted integrals, before taking any infimum. -/
theorem DiscPartitionedC1Curve.toHalfPlane_integral_sum (c : DiscPartitionedC1Curve) :
    (∑ i ∈ Finset.range c.n, ∫ t in c.times i..c.times (i + 1),
      weightedSpeed c.toHalfPlane.curve (c.toHalfPlane.velocity i) t) =
      ∑ i ∈ Finset.range c.n, ∫ t in c.times i..c.times (i + 1),
        discWeightedSpeed c.curve (c.velocity i) t := by
  apply Finset.sum_congr rfl
  intro i hi
  exact (c.piece i (Finset.mem_range.mp hi)).toHalfPlane_length

/-- The minimizing-curve characterization also applies to the original one-function finite-partition disc class, using its raw disc-weighted integral sum, not just a substituted distance functional. -/
theorem DiscPartitionedC1Curve.integral_sum_eq_dist_iff_monotoneGeodesic
    (c : DiscPartitionedC1Curve) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hz : (g • discToHalfPlane (c.curve (c.times 0))).re = 0)
    (hw : (g • discToHalfPlane (c.curve (c.times c.n))).re = 0)
    (hi : (g • discToHalfPlane (c.curve (c.times 0))).im ≤
      (g • discToHalfPlane (c.curve (c.times c.n))).im) :
    (∑ i ∈ Finset.range c.n, ∫ t in c.times i..c.times (i + 1),
      discWeightedSpeed c.curve (c.velocity i) t) =
        discPathDist (c.curve (c.times 0)) (c.curve (c.times c.n)) ↔
      ∀ i (hi : i < c.n), (c.piece i hi).MonotoneGeodesic
        (halfPlaneToDisc ∘ normalizerGeodesic g) := by
  have h := c.toHalfPlane.integral_sum_eq_dist_iff_monotoneGeodesic g hg hz hw hi
  change (∑ i ∈ Finset.range c.n, ∫ t in c.times i..c.times (i + 1),
    weightedSpeed c.toHalfPlane.curve (c.toHalfPlane.velocity i) t) =
      dist (discToHalfPlane (c.curve (c.times 0))) (discToHalfPlane (c.curve (c.times c.n))) ↔
      ∀ i (hi : i < c.n), c.toHalfPlane.piece i hi |>.MonotoneGeodesic (normalizerGeodesic g) at h
  simpa only [c.toHalfPlane_integral_sum, ← discPathDist_eq_halfPlane, c.toHalfPlane_piece,
    DiscC1CurvePiece.toHalfPlane_monotoneGeodesic_iff] using h

/-- Every native disc-line endpoint pair has an actual chart applying uniformly to all global
finite-partition C¹ disc curves with those endpoints. -/
theorem DiscLine.exists_global_minimizer_classification (L : DiscLine) {z w : 𝔻}
    (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    letI := discHyperbolicMetric
    ∃ γ : ℝ → 𝔻, Isometry γ ∧ range γ = L.carrier ∧
      ∀ c : DiscPartitionedC1Curve, c.curve (c.times 0) = z → c.curve (c.times c.n) = w →
        ((∑ i ∈ Finset.range c.n, ∫ t in c.times i..c.times (i + 1),
          discWeightedSpeed c.curve (c.velocity i) t) = discPathDist z w ↔
            ∀ i (hi : i < c.n), (c.piece i hi).MonotoneGeodesic γ) := by
  let := discHyperbolicMetric
  obtain ⟨g, hg, hgz, hgw, hi, hrange⟩ := L.exists_ordered_normalizer hzw hz hw
  refine ⟨halfPlaneToDisc ∘ normalizerGeodesic g,
    cayley_isometry.comp (normalizerGeodesic_isometry g hg), hrange, ?_⟩
  intro c hc0 hc1
  have hz' : (g • discToHalfPlane (c.curve (c.times 0))).re = 0 := by rwa [hc0]
  have hw' : (g • discToHalfPlane (c.curve (c.times c.n))).re = 0 := by rwa [hc1]
  have hi' : (g • discToHalfPlane (c.curve (c.times 0))).im ≤
      (g • discToHalfPlane (c.curve (c.times c.n))).im := by rw [hc0, hc1]; exact hi.le
  simpa only [hc0, hc1] using c.integral_sum_eq_dist_iff_monotoneGeodesic g hg hz' hw' hi'

/-- The native source open segment itself is exactly the unique actual component with compact closure. -/
theorem nativeDiscOpenSegment_unique_compact_component (L : DiscLine) {z w : 𝔻}
    (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    nativeDiscOpenSegment L z w ∈ nativeDiscPuncturedComponents L z w ∧
      IsCompact (closure (nativeDiscOpenSegment L z w)) ∧
      ∀ C ∈ nativeDiscPuncturedComponents L z w, IsCompact (closure C) →
        C = nativeDiscOpenSegment L z w := by
  obtain ⟨δ, s, t, hδ, hst, hs, ht, hrange⟩ := L.exists_ordered_param hzw hz hw
  let := discHyperbolicMetric
  have hγ := cayley_isometry.comp hδ.1
  have hopen : nativeDiscOpenSegment L z w = (halfPlaneToDisc ∘ δ) '' Ioo s t := by
    rw [nativeDiscOpenSegment_eq L hzw hz hw, ← hs, ← ht, openDiscHSegment_eq_image_Ioo hδ hst]
  have hcomponents : nativeDiscPuncturedComponents L z w =
      hLinePuncturedComponents (halfPlaneToDisc ∘ δ) s t := by
    unfold nativeDiscPuncturedComponents hLinePuncturedComponents
    rw [hrange]
    simp only [Function.comp_def, hs, ht]
  rw [hopen, hcomponents]
  have hmem : (halfPlaneToDisc ∘ δ) '' Ioo s t ∈
      hLinePuncturedComponents (halfPlaneToDisc ∘ δ) s t := by
    rw [hLinePuncturedComponents_eq hγ hst]
    exact mem_insert_of_mem _ (mem_insert _ _)
  have hcompact : IsCompact (closure ((halfPlaneToDisc ∘ δ) '' Ioo s t)) := by
    rw [hγ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hγ.continuous,
      closure_Ioo hst.ne]
    exact isCompact_Icc.image hγ.continuous
  obtain ⟨C, _, huniq⟩ := existsUnique_compact_hLine_component hγ hst
  have hmid := huniq ((halfPlaneToDisc ∘ δ) '' Ioo s t) ⟨hmem, hcompact⟩
  exact ⟨hmem, hcompact, fun D hD hDc => (huniq D ⟨hD, hDc⟩).trans hmid.symm⟩

end

end LowDimensionalTopology.Geometry.Hyperbolic
