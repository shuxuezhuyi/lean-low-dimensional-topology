/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.Geodesic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.MinimizingCurves
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

/-!
# Actual h-segments and equality in the triangle inequality
-/

@[expose] public section

open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- Equality in the triangle inequality on a vertical h-line forces the actual intermediate point
onto the height-ordered Euclidean interval; the proof uses genuine minimizing C¹ paths. -/
theorem dist_triangle_eq_iff_vertical_between {z w u : ℍ}
    (hr : z.re = w.re) (hi : z.im ≤ w.im) :
    dist z u + dist u w = dist z w ↔
      u.re = z.re ∧ z.im ≤ u.im ∧ u.im ≤ w.im := by
  constructor
  · intro heq
    obtain ⟨p, hp0, hp1, hp⟩ := exists_length_minimizing_piece z u
    obtain ⟨q, hq0, hq1, hq⟩ := exists_length_minimizing_piece u w
    have hpl := p.logHeightChange_le_length
    have hql := q.logHeightChange_le_length
    dsimp [C1CurvePiece.logHeightChange] at hpl hql
    rw [hp0, hp1] at hpl
    rw [hq0, hq1] at hql
    have hzw := metric_vertical_distance_of_im_le hr hi
    have hpe : p.length = p.logHeightChange := by
      dsimp [C1CurvePiece.logHeightChange]
      rw [hp0, hp1]
      linarith
    have hqe : q.length = q.logHeightChange := by
      dsimp [C1CurvePiece.logHeightChange]
      rw [hq0, hq1]
      linarith
    have hpg := (p.length_eq_logHeightChange_iff.mp hpe).geometry
    have hqg := (q.length_eq_logHeightChange_iff.mp hqe).geometry
    have hpre := hpg.1 p.b (right_mem_Icc.mpr p.ordered)
    have hpim := hpg.2 (left_mem_Icc.mpr p.ordered)
      (right_mem_Icc.mpr p.ordered) p.ordered
    have hqim := hqg.2 (left_mem_Icc.mpr q.ordered)
      (right_mem_Icc.mpr q.ordered) q.ordered
    simpa only [hp0, hp1, hq0, hq1] using And.intro hpre (And.intro hpim hqim)
  · rintro ⟨hu, hzu, huw⟩
    rw [metric_vertical_distance_of_im_le hu.symm hzu,
      metric_vertical_distance_of_im_le (hu.trans hr) huw,
      metric_vertical_distance_of_im_le hr hi]
    ring

/-- A real isometric parametrization whose image is an actual Euclidean h-line. -/
def IsHGeodesicParam (γ : ℝ → ℍ) : Prop :=
  Isometry γ ∧ IsHalfPlaneHLine (range γ)

/-- The closed segment is the image of an actual closed parameter interval of an h-line.
Its agreement with the source's connected-component presentation is a separate theorem. -/
def closedHSegment (z w : ℍ) : Set ℍ :=
  {u | ∃ (γ : ℝ → ℍ), IsHGeodesicParam γ ∧ ∃ s t : ℝ,
    s ≤ t ∧ γ s = z ∧ γ t = w ∧ u ∈ γ '' Icc s t}

/-- The open segment uses the corresponding open parameter interval. -/
def openHSegment (z w : ℍ) : Set ℍ :=
  {u | ∃ (γ : ℝ → ℍ), IsHGeodesicParam γ ∧ ∃ s t : ℝ,
    s < t ∧ γ s = z ∧ γ t = w ∧ u ∈ γ '' Ioo s t}

/-- The real-line version of the ordered triangle-equality criterion. -/
theorem real_dist_triangle_eq_iff_mem_Icc {s t r : ℝ} (hst : s ≤ t) :
    dist s r + dist r t = dist s t ↔ r ∈ Icc s t := by
  rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)]
  constructor
  · intro h
    by_cases hsr : s ≤ r
    · by_cases hrt : r ≤ t
      · exact ⟨hsr, hrt⟩
      · rw [abs_of_nonpos (sub_nonpos.mpr hsr), abs_of_pos (sub_pos.mpr (lt_of_not_ge hrt))] at h
        constructor <;> linarith
    · rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hsr)),
        abs_of_nonpos (sub_nonpos.mpr ((lt_of_not_ge hsr).le.trans hst))] at h
      constructor <;> linarith
  · rintro ⟨hsr, hrt⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hsr), abs_of_nonpos (sub_nonpos.mpr hrt)]
    ring

/-- Every actual segment point gives equality in the genuine hyperbolic triangle inequality. -/
theorem dist_triangle_eq_of_mem_closedHSegment {z w u : ℍ} (hu : u ∈ closedHSegment z w) :
    dist z u + dist u w = dist z w := by
  obtain ⟨γ, hγ, s, t, hst, rfl, rfl, r, hr, rfl⟩ := hu
  rw [hγ.1.dist_eq, hγ.1.dist_eq, hγ.1.dist_eq]
  exact (real_dist_triangle_eq_iff_mem_Icc hst).mpr hr

/-- Every triangle-equality point on distinct endpoints lies in an actual parametrized h-segment. -/
theorem mem_closedHSegment_of_dist_triangle_eq {z w u : ℍ} (hzw : z ≠ w)
    (heq : dist z u + dist u w = dist z w) : u ∈ closedHSegment z w := by
  obtain ⟨a, b, g, ha, hb, hab, hg, hga, hgb, hz, hw, hi⟩ :=
    exists_ordered_ideal_normalizer z w hzw
  have heq' : dist (g • z) (g • u) + dist (g • u) (g • w) = dist (g • z) (g • w) := by
    simpa only [realGL_distance] using heq
  have hu := (dist_triangle_eq_iff_vertical_between (hz.trans hw.symm) hi.le).mp heq'
  have hu0 : (g • u).re = 0 := hu.1.trans hz
  refine ⟨normalizerGeodesic g,
    ⟨normalizerGeodesic_isometry g hg, normalizerGeodesic_isHLine g hg⟩,
    Real.log (g • z).im, Real.log (g • w).im,
    (Real.log_lt_log (g • z).im_pos hi).le, normalizerGeodesic_parameter g z hz,
    normalizerGeodesic_parameter g w hw, Real.log (g • u).im, ?_,
    normalizerGeodesic_parameter g u hu0⟩
  exact ⟨Real.log_le_log (g • z).im_pos hu.2.1,
    Real.log_le_log (g • u).im_pos hu.2.2⟩

/--
For the actual parametrized h-segment. The component-definition adapter is
established separately, rather than defining the segment by triangle equality.
-/
theorem dist_triangle_eq_iff_mem_closedHSegment {z w u : ℍ} (hzw : z ≠ w) :
    dist z u + dist u w = dist z w ↔ u ∈ closedHSegment z w :=
  ⟨mem_closedHSegment_of_dist_triangle_eq hzw, dist_triangle_eq_of_mem_closedHSegment⟩

/-- Two actual h-line carriers sharing two distinct points coincide. -/
theorem isHLine_eq_of_two_points {S T : Set ℍ} (hS : IsHalfPlaneHLine S)
    (hT : IsHalfPlaneHLine T) {z w : ℍ} (hzw : z ≠ w)
    (hzS : z ∈ S) (hwS : w ∈ S) (hzT : z ∈ T) (hwT : w ∈ T) : S = T := by
  obtain ⟨L, rfl⟩ := exists_halfPlaneLine_of_isHLine hS
  obtain ⟨M, rfl⟩ := exists_halfPlaneLine_of_isHLine hT
  exact congrArg HalfPlaneLine.carrier (L.eq_of_two_points M hzw hzS hwS hzT hwT)

/-- The interval description is independent of the chosen actual unit-speed h-line chart. -/
theorem closedHSegment_eq_image_Icc {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    {s t : ℝ} (hst : s < t) : closedHSegment (γ s) (γ t) = γ '' Icc s t := by
  ext u
  constructor
  · intro hu
    obtain ⟨δ, hδ, a, b, hab, has, hbt, v, hv, hvu⟩ := hu
    have hzw : γ s ≠ γ t := hγ.1.injective.ne hst.ne
    have he := isHLine_eq_of_two_points hδ.2 hγ.2 hzw
      (has ▸ mem_range_self a) (hbt ▸ mem_range_self b) (mem_range_self s) (mem_range_self t)
    have hur : u ∈ range γ := he ▸ (hvu ▸ mem_range_self v)
    obtain ⟨r, rfl⟩ := hur
    refine ⟨r, ?_, rfl⟩
    have hsum := dist_triangle_eq_of_mem_closedHSegment
      (show γ r ∈ closedHSegment (γ s) (γ t) from
        ⟨δ, hδ, a, b, hab, has, hbt, v, hv, hvu⟩)
    rw [hγ.1.dist_eq, hγ.1.dist_eq, hγ.1.dist_eq] at hsum
    exact (real_dist_triangle_eq_iff_mem_Icc hst.le).mp hsum
  · intro hu
    exact ⟨γ, hγ, s, t, hst.le, rfl, rfl, hu⟩

/-- Open segment points are precisely closed segment points distinct from both endpoints. -/
theorem mem_openHSegment_iff {z w u : ℍ} (hzw : z ≠ w) :
    u ∈ openHSegment z w ↔ u ∈ closedHSegment z w ∧ u ≠ z ∧ u ≠ w := by
  constructor
  · rintro ⟨γ, hγ, s, t, hst, rfl, rfl, r, hr, rfl⟩
    refine ⟨⟨γ, hγ, s, t, hst.le, rfl, rfl, r, ⟨hr.1.le, hr.2.le⟩, rfl⟩, ?_, ?_⟩
    · exact hγ.1.injective.ne (ne_of_gt hr.1)
    · exact hγ.1.injective.ne (ne_of_lt hr.2)
  · rintro ⟨⟨γ, hγ, s, t, hst, hs, ht, r, hr, rfl⟩, huz, huw⟩
    have hst' : s < t := lt_of_le_of_ne hst (fun h => hzw (hs.symm.trans ((congrArg γ h).trans ht)))
    refine ⟨γ, hγ, s, t, hst', hs, ht, r, ?_, rfl⟩
    constructor
    · exact lt_of_le_of_ne hr.1 (fun h => huz ((congrArg γ h.symm).trans hs))
    · exact lt_of_le_of_ne hr.2 (fun h => huw ((congrArg γ h).trans ht))

theorem openHSegment_eq_image_Ioo {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    {s t : ℝ} (hst : s < t) : openHSegment (γ s) (γ t) = γ '' Ioo s t := by
  ext u
  rw [mem_openHSegment_iff (hγ.1.injective.ne hst.ne), closedHSegment_eq_image_Icc hγ hst]
  constructor
  · rintro ⟨⟨r, hr, rfl⟩, hrs, hrt⟩
    refine ⟨r, ⟨lt_of_le_of_ne hr.1 ?_, lt_of_le_of_ne hr.2 ?_⟩, rfl⟩
    · exact fun h => hrs (congrArg γ h.symm)
    · exact fun h => hrt (congrArg γ h)
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, ⟨hr.1.le, hr.2.le⟩, rfl⟩,
      hγ.1.injective.ne (ne_of_gt hr.1), hγ.1.injective.ne (ne_of_lt hr.2)⟩

/-- The genuine closed segment is compact in the actual hyperbolic model topology. -/
theorem isCompact_closedHSegment {z w : ℍ} (hzw : z ≠ w) :
    IsCompact (closedHSegment z w) := by
  obtain ⟨a, b, γ, s, t, _, _, _, hγ, hline, hst, rfl, rfl, _⟩ :=
    exists_ordered_geodesic_distance_crossRatio z w hzw
  rw [closedHSegment_eq_image_Icc ⟨hγ, hline⟩ hst]
  exact isCompact_Icc.image hγ.continuous

/-- The actual ambient closure of the open segment is the closed segment. -/
theorem closure_openHSegment {z w : ℍ} (hzw : z ≠ w) :
    closure (openHSegment z w) = closedHSegment z w := by
  obtain ⟨a, b, γ, s, t, _, _, _, hγ, hline, hst, rfl, rfl, _⟩ :=
    exists_ordered_geodesic_distance_crossRatio z w hzw
  rw [openHSegment_eq_image_Ioo ⟨hγ, hline⟩ hst,
    hγ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hγ.continuous,
    closure_Ioo hst.ne, closedHSegment_eq_image_Icc ⟨hγ, hline⟩ hst]

/-- The real parameter line with the two ordered endpoints removed. -/
def puncturedParameterLine (s t : ℝ) : Set ℝ := {r | r ≠ s ∧ r ≠ t}

/-- The middle component of the punctured real parameter line is the open interval. -/
theorem connectedComponentIn_punctured_middle {s t r : ℝ} (hr : r ∈ Ioo s t) :
    connectedComponentIn (puncturedParameterLine s t) r = Ioo s t := by
  have hrP : r ∈ puncturedParameterLine s t := ⟨ne_of_gt hr.1, ne_of_lt hr.2⟩
  have hrC := mem_connectedComponentIn hrP
  have horder := (isPreconnected_connectedComponentIn
    (F := puncturedParameterLine s t) (x := r)).ordConnected
  apply subset_antisymm
  · intro x hx
    constructor
    · by_contra h
      have hsC := horder.out hx hrC (show s ∈ Icc x r from ⟨not_lt.mp h, hr.1.le⟩)
      exact (connectedComponentIn_subset _ _ hsC).1 rfl
    · by_contra h
      have htC := horder.out hrC hx (show t ∈ Icc r x from ⟨hr.2.le, not_lt.mp h⟩)
      exact (connectedComponentIn_subset _ _ htC).2 rfl
  · exact isPreconnected_Ioo.subset_connectedComponentIn hr
      (fun x hx => ⟨ne_of_gt hx.1, ne_of_lt hx.2⟩)

/-- The lower component is the open lower ray. -/
theorem connectedComponentIn_punctured_left {s t r : ℝ} (hst : s < t) (hr : r < s) :
    connectedComponentIn (puncturedParameterLine s t) r = Iio s := by
  have hrP : r ∈ puncturedParameterLine s t := ⟨ne_of_lt hr, ne_of_lt (hr.trans hst)⟩
  have hrC := mem_connectedComponentIn hrP
  have horder := (isPreconnected_connectedComponentIn
    (F := puncturedParameterLine s t) (x := r)).ordConnected
  apply subset_antisymm
  · intro x hx
    by_contra h
    have hsC := horder.out hrC hx (show s ∈ Icc r x from ⟨hr.le, not_lt.mp h⟩)
    exact (connectedComponentIn_subset _ _ hsC).1 rfl
  · exact isPreconnected_Iio.subset_connectedComponentIn hr
      (fun x hx => ⟨ne_of_lt hx, ne_of_lt (hx.trans hst)⟩)

/-- The upper component is the open upper ray. -/
theorem connectedComponentIn_punctured_right {s t r : ℝ} (hst : s < t) (hr : t < r) :
    connectedComponentIn (puncturedParameterLine s t) r = Ioi t := by
  have hrP : r ∈ puncturedParameterLine s t := ⟨ne_of_gt (hst.trans hr), ne_of_gt hr⟩
  have hrC := mem_connectedComponentIn hrP
  have horder := (isPreconnected_connectedComponentIn
    (F := puncturedParameterLine s t) (x := r)).ordConnected
  apply subset_antisymm
  · intro x hx
    by_contra h
    have htC := horder.out hx hrC (show t ∈ Icc x r from ⟨not_lt.mp h, hr.le⟩)
    exact (connectedComponentIn_subset _ _ htC).2 rfl
  · exact isPreconnected_Ioi.subset_connectedComponentIn hr
      (fun x hx => ⟨ne_of_gt (hst.trans hx), ne_of_gt hx⟩)

/-- Isometric embeddings carry actual connected components in subsets to the corresponding components. -/
theorem isometry_image_connectedComponentIn {X : Type*} [MetricSpace X] {γ : ℝ → X} (hγ : Isometry γ)
    (S : Set ℝ) {r : ℝ} (hr : r ∈ S) :
    γ '' connectedComponentIn S r = connectedComponentIn (γ '' S) (γ r) := by
  apply subset_antisymm
  · exact hγ.continuous.continuousOn.image_connectedComponentIn_subset hr
  · let C := connectedComponentIn (γ '' S) (γ r)
    have hCsub : C ⊆ range γ := (connectedComponentIn_subset _ _).trans (image_subset_range _ _)
    have himage : γ '' (γ ⁻¹' C) = C := image_preimage_eq_of_subset hCsub
    have hpre : IsPreconnected (γ ⁻¹' C) := hγ.isEmbedding.isInducing.isPreconnected_image.mp
      (himage.symm ▸ isPreconnected_connectedComponentIn)
    have hrC : r ∈ γ ⁻¹' C := mem_connectedComponentIn (mem_image_of_mem γ hr)
    have hpreS : γ ⁻¹' C ⊆ S := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := connectedComponentIn_subset (γ '' S) (γ r) hx
      simpa only [hγ.injective hyx] using hy
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hCsub hy
    exact ⟨x, hpre.subset_connectedComponentIn hrC hpreS hy, rfl⟩

/-- Removing two actual h-line points corresponds exactly to puncturing the real parameter line. -/
theorem image_puncturedParameterLine {X : Type*} [MetricSpace X] {γ : ℝ → X} (hγ : Isometry γ) (s t : ℝ) :
    γ '' puncturedParameterLine s t = range γ \ {γ s, γ t} := by
  ext u
  constructor
  · rintro ⟨r, ⟨hrs, hrt⟩, rfl⟩
    refine ⟨mem_range_self r, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hγ.injective.ne hrs, hγ.injective.ne hrt⟩
  · rintro ⟨⟨r, rfl⟩, hr⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hr
    exact ⟨r, ⟨fun h => hr.1 (congrArg γ h), fun h => hr.2 (congrArg γ h)⟩, rfl⟩

/-- Exhaustive classification of all components after removing two real endpoints. -/
theorem connectedComponentIn_punctured_cases {s t r : ℝ} (hst : s < t)
    (hr : r ∈ puncturedParameterLine s t) :
    connectedComponentIn (puncturedParameterLine s t) r = Iio s ∨
      connectedComponentIn (puncturedParameterLine s t) r = Ioo s t ∨
      connectedComponentIn (puncturedParameterLine s t) r = Ioi t := by
  by_cases hrs : r < s
  · exact Or.inl (connectedComponentIn_punctured_left hst hrs)
  · have hsr : s < r := lt_of_le_of_ne (not_lt.mp hrs) hr.1.symm
    by_cases hrt : r < t
    · exact Or.inr (Or.inl (connectedComponentIn_punctured_middle ⟨hsr, hrt⟩))
    · exact Or.inr (Or.inr (connectedComponentIn_punctured_right hst
        (lt_of_le_of_ne (not_lt.mp hrt) hr.2.symm)))

theorem not_isCompact_real_Iic (s : ℝ) : ¬IsCompact (Iic s) := by
  intro h
  obtain ⟨b, hb⟩ := h.bddBelow
  have hp := hb (show min b s - 1 ∈ Iic s by
    change min b s - 1 ≤ s
    linarith [min_le_right b s])
  linarith [min_le_left b s]

theorem not_isCompact_real_Ici (s : ℝ) : ¬IsCompact (Ici s) := by
  intro h
  obtain ⟨b, hb⟩ := h.bddAbove
  have hp := hb (show max b s + 1 ∈ Ici s by
    change s ≤ max b s + 1
    linarith [le_max_right b s])
  linarith [le_max_left b s]

/-- Precisely the middle real component has compact closure. -/
theorem isCompact_closure_punctured_component_iff {s t r : ℝ} (hst : s < t)
    (hr : r ∈ puncturedParameterLine s t) :
    IsCompact (closure (connectedComponentIn (puncturedParameterLine s t) r)) ↔ r ∈ Ioo s t := by
  by_cases hrs : r < s
  · rw [connectedComponentIn_punctured_left hst hrs, closure_Iio]
    exact iff_of_false (not_isCompact_real_Iic s) (fun h => (not_lt_of_ge hrs.le) h.1)
  · have hsr : s < r := lt_of_le_of_ne (not_lt.mp hrs) hr.1.symm
    by_cases hrt : r < t
    · rw [connectedComponentIn_punctured_middle ⟨hsr, hrt⟩, closure_Ioo hst.ne]
      exact iff_of_true isCompact_Icc ⟨hsr, hrt⟩
    · have htr : t < r := lt_of_le_of_ne (not_lt.mp hrt) hr.2.symm
      rw [connectedComponentIn_punctured_right hst htr, closure_Ioi]
      exact iff_of_false (not_isCompact_real_Ici t) (fun h => (not_lt_of_ge htr.le) h.2)

/-- The source's middle connected component, in the actual h-line minus its endpoints. -/
theorem connectedComponentIn_hLine_middle {X : Type*} [MetricSpace X] {γ : ℝ → X} (hγ : Isometry γ)
    {s t r : ℝ} (hr : r ∈ Ioo s t) :
    connectedComponentIn (range γ \ {γ s, γ t}) (γ r) = γ '' Ioo s t := by
  rw [← image_puncturedParameterLine hγ s t,
    ← isometry_image_connectedComponentIn hγ (puncturedParameterLine s t)
      (show r ∈ puncturedParameterLine s t from ⟨ne_of_gt hr.1, ne_of_lt hr.2⟩),
    connectedComponentIn_punctured_middle hr]

/-- The source's compact-closure criterion holds in the actual hyperbolic model topology. -/
theorem isCompact_closure_hLine_component_iff {X : Type*} [MetricSpace X] {γ : ℝ → X} (hγ : Isometry γ)
    {s t r : ℝ} (hst : s < t) (hr : r ∈ puncturedParameterLine s t) :
    IsCompact (closure (connectedComponentIn (range γ \ {γ s, γ t}) (γ r))) ↔ r ∈ Ioo s t := by
  rw [← image_puncturedParameterLine hγ s t,
    ← isometry_image_connectedComponentIn hγ (puncturedParameterLine s t) hr,
    hγ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hγ.continuous,
    ← hγ.isEmbedding.isCompact_iff]
  exact isCompact_closure_punctured_component_iff hst hr

/-- The geometric open segment agrees with the unique component having compact closure, exactly as
in the source definition. No metric-interval assumption is used in this adapter. -/
theorem mem_openHSegment_iff_compact_component {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    {s t r : ℝ} (hst : s < t) (hr : r ∈ puncturedParameterLine s t) :
    γ r ∈ openHSegment (γ s) (γ t) ↔
      IsCompact (closure (connectedComponentIn (range γ \ {γ s, γ t}) (γ r))) := by
  rw [openHSegment_eq_image_Ioo hγ hst,
    isCompact_closure_hLine_component_iff hγ.1 hst hr]
  exact hγ.1.injective.mem_set_image

/-- The two unbounded components are also the actual Euclidean-parameter rays. -/
theorem connectedComponentIn_hLine_left {X : Type*} [MetricSpace X] {γ : ℝ → X} (hγ : Isometry γ)
    {s t r : ℝ} (hst : s < t) (hr : r < s) :
    connectedComponentIn (range γ \ {γ s, γ t}) (γ r) = γ '' Iio s := by
  rw [← image_puncturedParameterLine hγ s t,
    ← isometry_image_connectedComponentIn hγ (puncturedParameterLine s t)
      (show r ∈ puncturedParameterLine s t from ⟨ne_of_lt hr, ne_of_lt (hr.trans hst)⟩),
    connectedComponentIn_punctured_left hst hr]

theorem connectedComponentIn_hLine_right {X : Type*} [MetricSpace X] {γ : ℝ → X} (hγ : Isometry γ)
    {s t r : ℝ} (hst : s < t) (hr : t < r) :
    connectedComponentIn (range γ \ {γ s, γ t}) (γ r) = γ '' Ioi t := by
  rw [← image_puncturedParameterLine hγ s t,
    ← isometry_image_connectedComponentIn hγ (puncturedParameterLine s t)
      (show r ∈ puncturedParameterLine s t from ⟨ne_of_gt (hst.trans hr), ne_of_gt hr⟩),
    connectedComponentIn_punctured_right hst hr]

/-- The collection of actual nonempty components in the punctured h-line. -/
def hLinePuncturedComponents {X : Type*} [TopologicalSpace X] (γ : ℝ → X) (s t : ℝ) : Set (Set X) :=
  {C | ∃ u ∈ range γ \ {γ s, γ t}, C = connectedComponentIn (range γ \ {γ s, γ t}) u}

/-- There are no further components beyond the lower ray, middle interval, and upper ray. -/
theorem hLinePuncturedComponents_eq {X : Type*} [MetricSpace X] {γ : ℝ → X} (hγ : Isometry γ)
    {s t : ℝ} (hst : s < t) :
    hLinePuncturedComponents γ s t = {γ '' Iio s, γ '' Ioo s t, γ '' Ioi t} := by
  ext C
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [← image_puncturedParameterLine hγ s t] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    rw [← image_puncturedParameterLine hγ s t,
      ← isometry_image_connectedComponentIn hγ (puncturedParameterLine s t) hr]
    rcases connectedComponentIn_punctured_cases hst hr with h | h | h
    · rw [h]; exact mem_insert _ _
    · rw [h]; exact mem_insert_of_mem _ (mem_insert _ _)
    · rw [h]; exact mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _))
  · intro hC
    simp only [mem_insert_iff, mem_singleton_iff] at hC
    rcases hC with rfl | rfl | rfl
    · have hr : s - 1 < s := by linarith
      refine ⟨γ (s - 1), ?_, (connectedComponentIn_hLine_left hγ hst hr).symm⟩
      rw [← image_puncturedParameterLine hγ s t]
      exact mem_image_of_mem γ ⟨ne_of_lt hr, ne_of_lt (hr.trans hst)⟩
    · have hr : (s + t) / 2 ∈ Ioo s t := by constructor <;> linarith
      refine ⟨γ ((s + t) / 2), ?_, (connectedComponentIn_hLine_middle hγ hr).symm⟩
      rw [← image_puncturedParameterLine hγ s t]
      exact mem_image_of_mem γ ⟨ne_of_gt hr.1, ne_of_lt hr.2⟩
    · have hr : t < t + 1 := by linarith
      refine ⟨γ (t + 1), ?_, (connectedComponentIn_hLine_right hγ hst hr).symm⟩
      rw [← image_puncturedParameterLine hγ s t]
      exact mem_image_of_mem γ ⟨ne_of_gt (hst.trans hr), ne_of_gt hr⟩

/-- The source's count of three components is an exact finite cardinality statement. -/
theorem ncard_hLinePuncturedComponents {X : Type*} [MetricSpace X] {γ : ℝ → X} (hγ : Isometry γ)
    {s t : ℝ} (hst : s < t) : (hLinePuncturedComponents γ s t).ncard = 3 := by
  apply Set.ncard_eq_three.mpr
  refine ⟨γ '' Iio s, γ '' Ioo s t, γ '' Ioi t, ?_, ?_, ?_, hLinePuncturedComponents_eq hγ hst⟩
  · intro h
    have he := hγ.injective.image_injective h
    have hx : s - 1 ∈ Iio s := by change s - 1 < s; linarith
    have hx' : s - 1 ∈ Ioo s t := he ▸ hx
    linarith [hx'.1]
  · intro h
    have he := hγ.injective.image_injective h
    have hx : s - 1 ∈ Iio s := by change s - 1 < s; linarith
    have hx' : s - 1 ∈ Ioi t := he ▸ hx
    change t < s - 1 at hx'
    linarith
  · intro h
    have he := hγ.injective.image_injective h
    have hx : (s + t) / 2 ∈ Ioo s t := by constructor <;> linarith
    have hx' : (s + t) / 2 ∈ Ioi t := he ▸ hx
    change t < (s + t) / 2 at hx'
    linarith

/-- There is exactly one component whose actual ambient closure is compact. -/
theorem existsUnique_compact_hLine_component {X : Type*} [MetricSpace X]
    {γ : ℝ → X} (hγ : Isometry γ) {s t : ℝ} (hst : s < t) :
    ∃! C : Set X, C ∈ hLinePuncturedComponents γ s t ∧ IsCompact (closure C) := by
  refine ⟨γ '' Ioo s t, ⟨?_, ?_⟩, ?_⟩
  · rw [hLinePuncturedComponents_eq hγ hst]
    exact mem_insert_of_mem _ (mem_insert _ _)
  · rw [hγ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hγ.continuous,
      closure_Ioo hst.ne]
    exact isCompact_Icc.image hγ.continuous
  · rintro C ⟨⟨u, hu, hC⟩, hcompact⟩
    rw [← image_puncturedParameterLine hγ s t] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    have hmid := (isCompact_closure_hLine_component_iff hγ hst hr).mp (hC ▸ hcompact)
    exact hC.trans (connectedComponentIn_hLine_middle hγ hmid)

/-- The source's characterization of the open h-segment as the unique compact-closure component. -/
theorem openHSegment_unique_compact_component {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    {s t : ℝ} (hst : s < t) :
    openHSegment (γ s) (γ t) ∈ hLinePuncturedComponents γ s t ∧
      IsCompact (closure (openHSegment (γ s) (γ t))) ∧
      ∀ C ∈ hLinePuncturedComponents γ s t, IsCompact (closure C) →
        C = openHSegment (γ s) (γ t) := by
  rw [openHSegment_eq_image_Ioo hγ hst]
  obtain ⟨C, hC, huniq⟩ := existsUnique_compact_hLine_component hγ.1 hst
  have hmid : C = γ '' Ioo s t := by
    obtain ⟨u, hu, heq⟩ := hC.1
    rw [← image_puncturedParameterLine hγ.1 s t] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    exact heq.trans (connectedComponentIn_hLine_middle hγ.1
      ((isCompact_closure_hLine_component_iff hγ.1 hst hr).mp (heq ▸ hC.2)))
  subst C
  exact ⟨hC.1, hC.2, fun D hD hcompact => huniq D ⟨hD, hcompact⟩⟩

/-- The actual between relation, using the geometric open segment. -/
def HBetween (z u w : ℍ) : Prop := u ∈ openHSegment z w

def leftClosedHSegment (z w : ℍ) : Set ℍ := closedHSegment z w \ {w}

def rightClosedHSegment (z w : ℍ) : Set ℍ := closedHSegment z w \ {z}

theorem closedHSegment_comm {z w : ℍ} (hzw : z ≠ w) :
    closedHSegment z w = closedHSegment w z := by
  ext u
  rw [← dist_triangle_eq_iff_mem_closedHSegment hzw,
    ← dist_triangle_eq_iff_mem_closedHSegment hzw.symm]
  simp only [dist_comm w u, dist_comm u z, dist_comm w z, add_comm]

theorem openHSegment_comm {z w : ℍ} (hzw : z ≠ w) :
    openHSegment z w = openHSegment w z := by
  ext u
  rw [mem_openHSegment_iff hzw, mem_openHSegment_iff hzw.symm, closedHSegment_comm hzw]
  tauto

/-- Between means precisely triangle equality at an actual point distinct from both endpoints. -/
theorem hBetween_iff_dist_triangle_eq {z w u : ℍ} (hzw : z ≠ w) :
    HBetween z u w ↔ dist z u + dist u w = dist z w ∧ u ≠ z ∧ u ≠ w := by
  rw [HBetween, mem_openHSegment_iff hzw, ← dist_triangle_eq_iff_mem_closedHSegment hzw]

/-- The actual disc segment transported by the fixed Cayley homeomorphism.
The direct Euclidean disc h-line presentation is recorded as a separate model adapter. -/
def closedDiscHSegment (z w : 𝔻) : Set 𝔻 :=
  {u | discToHalfPlane u ∈ closedHSegment (discToHalfPlane z) (discToHalfPlane w)}

def openDiscHSegment (z w : 𝔻) : Set 𝔻 :=
  {u | discToHalfPlane u ∈ openHSegment (discToHalfPlane z) (discToHalfPlane w)}

def DiscHBetween (z u w : 𝔻) : Prop := u ∈ openDiscHSegment z w

theorem closedDiscHSegment_eq_cayley_image (z w : 𝔻) :
    closedDiscHSegment z w = halfPlaneToDisc ''
      closedHSegment (discToHalfPlane z) (discToHalfPlane w) := by
  ext u
  constructor
  · intro hu
    exact ⟨discToHalfPlane u, hu, halfPlaneToDisc_discToHalfPlane u⟩
  · rintro ⟨v, hv, rfl⟩
    simpa only [closedDiscHSegment, mem_ofPred_eq, discToHalfPlane_halfPlaneToDisc] using hv

theorem openDiscHSegment_eq_cayley_image (z w : 𝔻) :
    openDiscHSegment z w = halfPlaneToDisc ''
      openHSegment (discToHalfPlane z) (discToHalfPlane w) := by
  ext u
  constructor
  · intro hu
    exact ⟨discToHalfPlane u, hu, halfPlaneToDisc_discToHalfPlane u⟩
  · rintro ⟨v, hv, rfl⟩
    simpa only [openDiscHSegment, mem_ofPred_eq, discToHalfPlane_halfPlaneToDisc] using hv

/-- The same true weighted-path triangle equality in the actual disc model. -/
theorem disc_triangle_eq_iff_mem_closedDiscHSegment {z w u : 𝔻} (hzw : z ≠ w) :
    discPathDist z u + discPathDist u w = discPathDist z w ↔ u ∈ closedDiscHSegment z w := by
  have hZW : discToHalfPlane z ≠ discToHalfPlane w := fun h => hzw (cayleyHomeomorph.symm.injective h)
  simp only [discPathDist_eq_halfPlane]
  exact dist_triangle_eq_iff_mem_closedHSegment hZW

theorem isCompact_closedDiscHSegment {z w : 𝔻} (hzw : z ≠ w) :
    IsCompact (closedDiscHSegment z w) := by
  rw [closedDiscHSegment_eq_cayley_image]
  exact (isCompact_closedHSegment
    (fun h => hzw (cayleyHomeomorph.symm.injective h))).image cayleyHomeomorph.continuous

theorem closure_openDiscHSegment {z w : 𝔻} (hzw : z ≠ w) :
    closure (openDiscHSegment z w) = closedDiscHSegment z w := by
  have hZW : discToHalfPlane z ≠ discToHalfPlane w := fun h => hzw (cayleyHomeomorph.symm.injective h)
  rw [openDiscHSegment_eq_cayley_image, closedDiscHSegment_eq_cayley_image]
  change closure (cayleyHomeomorph '' _) = cayleyHomeomorph '' _
  rw [← cayleyHomeomorph.image_closure, closure_openHSegment hZW]

theorem closedDiscHSegment_eq_image_Icc {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    {s t : ℝ} (hst : s < t) :
    closedDiscHSegment (halfPlaneToDisc (γ s)) (halfPlaneToDisc (γ t)) =
      (halfPlaneToDisc ∘ γ) '' Icc s t := by
  rw [closedDiscHSegment_eq_cayley_image, discToHalfPlane_halfPlaneToDisc,
    discToHalfPlane_halfPlaneToDisc, closedHSegment_eq_image_Icc hγ hst, image_image]
  rfl

theorem openDiscHSegment_eq_image_Ioo {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    {s t : ℝ} (hst : s < t) :
    openDiscHSegment (halfPlaneToDisc (γ s)) (halfPlaneToDisc (γ t)) =
      (halfPlaneToDisc ∘ γ) '' Ioo s t := by
  rw [openDiscHSegment_eq_cayley_image, discToHalfPlane_halfPlaneToDisc,
    discToHalfPlane_halfPlaneToDisc, openHSegment_eq_image_Ioo hγ hst, image_image]
  rfl

/-- The actual disc trace has exactly the same three connected components after removing endpoints. -/
theorem ncard_disc_hLinePuncturedComponents {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    {s t : ℝ} (hst : s < t) :
    (hLinePuncturedComponents (halfPlaneToDisc ∘ γ) s t).ncard = 3 := by
  let := discHyperbolicMetric
  exact ncard_hLinePuncturedComponents (cayley_isometry.comp hγ.1) hst

/-- The disc segment also agrees with the source's compact-closure component criterion,
in the actual disc topology, rather than a newly declared discrete topology. -/
theorem mem_openDiscHSegment_iff_compact_component {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    {s t r : ℝ} (hst : s < t) (hr : r ∈ puncturedParameterLine s t) :
    halfPlaneToDisc (γ r) ∈ openDiscHSegment (halfPlaneToDisc (γ s)) (halfPlaneToDisc (γ t)) ↔
      IsCompact (closure (connectedComponentIn
        (range (halfPlaneToDisc ∘ γ) \ {halfPlaneToDisc (γ s), halfPlaneToDisc (γ t)})
          (halfPlaneToDisc (γ r)))) := by
  let := discHyperbolicMetric
  have hi := cayley_isometry.comp hγ.1
  rw [openDiscHSegment_eq_image_Ioo hγ hst]
  change (halfPlaneToDisc ∘ γ) r ∈ (halfPlaneToDisc ∘ γ) '' Ioo s t ↔
    IsCompact (closure (connectedComponentIn
      (range (halfPlaneToDisc ∘ γ) \ {(halfPlaneToDisc ∘ γ) s, (halfPlaneToDisc ∘ γ) t})
        ((halfPlaneToDisc ∘ γ) r)))
  rw [isCompact_closure_hLine_component_iff hi hst hr]
  exact hi.injective.mem_set_image

end

end LowDimensionalTopology.Geometry.Hyperbolic
