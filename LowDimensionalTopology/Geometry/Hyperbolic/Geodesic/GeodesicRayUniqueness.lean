/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicRays
public import Mathlib.Tactic

/-!
# Chart-independent rays and canonical ideal-end segments
-/

@[expose] public section

open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- The actual real parameter line with one point removed. -/
def puncturedParameterPoint (s : ℝ) : Set ℝ := {r | r ≠ s}

theorem connectedComponentIn_puncturedPoint_left {s r : ℝ} (hr : r < s) :
    connectedComponentIn (puncturedParameterPoint s) r = Iio s := by
  have hrP : r ∈ puncturedParameterPoint s := ne_of_lt hr
  have hrC := mem_connectedComponentIn hrP
  have horder := (isPreconnected_connectedComponentIn
    (F := puncturedParameterPoint s) (x := r)).ordConnected
  apply subset_antisymm
  · intro x hx
    by_contra h
    have hsC := horder.out hrC hx (show s ∈ Icc r x from ⟨hr.le, not_lt.mp h⟩)
    exact connectedComponentIn_subset _ _ hsC rfl
  · exact isPreconnected_Iio.subset_connectedComponentIn hr (fun _ hx => ne_of_lt hx)

theorem connectedComponentIn_puncturedPoint_right {s r : ℝ} (hr : s < r) :
    connectedComponentIn (puncturedParameterPoint s) r = Ioi s := by
  have hrP : r ∈ puncturedParameterPoint s := ne_of_gt hr
  have hrC := mem_connectedComponentIn hrP
  have horder := (isPreconnected_connectedComponentIn
    (F := puncturedParameterPoint s) (x := r)).ordConnected
  apply subset_antisymm
  · intro x hx
    by_contra h
    have hsC := horder.out hx hrC (show s ∈ Icc x r from ⟨not_lt.mp h, hr.le⟩)
    exact connectedComponentIn_subset _ _ hsC rfl
  · exact isPreconnected_Ioi.subset_connectedComponentIn hr (fun _ hx => ne_of_gt hx)

theorem image_puncturedParameterPoint {γ : ℝ → ℍ} (hγ : Isometry γ) (s : ℝ) :
    γ '' puncturedParameterPoint s = range γ \ {γ s} := by
  have he := image_puncturedParameterLine hγ s s
  simpa only [puncturedParameterPoint, puncturedParameterLine, and_self, pair_eq_singleton] using he

theorem connectedComponentIn_hLine_puncturedPoint_left {γ : ℝ → ℍ} (hγ : Isometry γ)
    {s r : ℝ} (hr : r < s) :
    connectedComponentIn (range γ \ {γ s}) (γ r) = γ '' Iio s := by
  rw [← image_puncturedParameterPoint hγ s,
    ← isometry_image_connectedComponentIn hγ (puncturedParameterPoint s) (ne_of_lt hr),
    connectedComponentIn_puncturedPoint_left hr]

theorem connectedComponentIn_hLine_puncturedPoint_right {γ : ℝ → ℍ} (hγ : Isometry γ)
    {s r : ℝ} (hr : s < r) :
    connectedComponentIn (range γ \ {γ s}) (γ r) = γ '' Ioi s := by
  rw [← image_puncturedParameterPoint hγ s,
    ← isometry_image_connectedComponentIn hγ (puncturedParameterPoint s) (ne_of_gt hr),
    connectedComponentIn_puncturedPoint_right hr]

/-- Two genuine charts of the same full h-line and the same starting point give the same two rays,
possibly with the orientation exchanged. This is proved using actual connected components. -/
theorem forwardHLineRay_eq_one_of_same_range {γ δ : ℝ → ℍ} (hγ : Isometry γ) (hδ : Isometry δ)
    (hrange : range γ = range δ) {s t : ℝ} (hbase : γ s = δ t) :
    forwardHLineRay δ t = forwardHLineRay γ s ∨ forwardHLineRay δ t = backwardHLineRay γ s := by
  have hplus : t < t + 1 := by linarith
  have hδC := connectedComponentIn_hLine_puncturedPoint_right hδ hplus
  obtain ⟨r, hr⟩ : δ (t + 1) ∈ range γ := hrange.symm ▸ mem_range_self (t + 1)
  have hne : r ≠ s := by
    intro he
    have hbad : δ (t + 1) = δ t := hr.symm.trans ((congrArg γ he).trans hbase)
    have he' := hδ.injective hbad
    linarith
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · have hγC := connectedComponentIn_hLine_puncturedPoint_left hγ hrs
    rw [hrange, hbase, hr] at hγC
    have he := congrArg closure (hδC.symm.trans hγC)
    rw [hδ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hδ.continuous,
      hγ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hγ.continuous,
      closure_Ioi, closure_Iio] at he
    exact Or.inr he
  · have hγC := connectedComponentIn_hLine_puncturedPoint_right hγ hsr
    rw [hrange, hbase, hr] at hγC
    have he := congrArg closure (hδC.symm.trans hγC)
    rw [hδ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hδ.continuous,
      hγ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hγ.continuous,
      closure_Ioi, closure_Ioi] at he
    exact Or.inl he

/-- The same independence statement for the backward chart orientation. -/
theorem backwardHLineRay_eq_one_of_same_range {γ δ : ℝ → ℍ} (hγ : Isometry γ) (hδ : Isometry δ)
    (hrange : range γ = range δ) {s t : ℝ} (hbase : γ s = δ t) :
    backwardHLineRay δ t = forwardHLineRay γ s ∨ backwardHLineRay δ t = backwardHLineRay γ s := by
  have hminus : t - 1 < t := by linarith
  have hδC := connectedComponentIn_hLine_puncturedPoint_left hδ hminus
  obtain ⟨r, hr⟩ : δ (t - 1) ∈ range γ := hrange.symm ▸ mem_range_self (t - 1)
  have hne : r ≠ s := by
    intro he
    have hbad : δ (t - 1) = δ t := hr.symm.trans ((congrArg γ he).trans hbase)
    have he' := hδ.injective hbad
    linarith
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · have hγC := connectedComponentIn_hLine_puncturedPoint_left hγ hrs
    rw [hrange, hbase, hr] at hγC
    have he := congrArg closure (hδC.symm.trans hγC)
    rw [hδ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hδ.continuous,
      hγ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hγ.continuous,
      closure_Iio, closure_Iio] at he
    exact Or.inr he
  · have hγC := connectedComponentIn_hLine_puncturedPoint_right hγ hsr
    rw [hrange, hbase, hr] at hγC
    have he := congrArg closure (hδC.symm.trans hγC)
    rw [hδ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hδ.continuous,
      hγ.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hγ.continuous,
      closure_Iio, closure_Ioi] at he
    exact Or.inl he

theorem hTraceIdealEndpoints_mono {S T : Set ℍ} (h : S ⊆ T) :
    hTraceIdealEndpoints S ⊆ hTraceIdealEndpoints T :=
  inter_subset_inter_left _ (closure_mono (image_mono h))

theorem IsHLineRay.idealEndpoints_eq {z : ℍ} {a : OnePoint ℂ} {R : Set ℍ}
    (h : IsHLineRay z a R) : hTraceIdealEndpoints R = {a} := by
  obtain ⟨_, _, _, _, _, he⟩ := h
  exact he

theorem IsHLineRay.start_mem {z : ℍ} {a : OnePoint ℂ} {R : Set ℍ}
    (h : IsHLineRay z a R) : z ∈ R := by
  obtain ⟨γ, _, s, hs, hor, _⟩ := h
  rw [← hs]
  rcases hor with rfl | rfl
  · exact mem_image_of_mem γ (mem_Ici.mpr le_rfl)
  · exact mem_image_of_mem γ (mem_Iic.mpr le_rfl)

/-- A genuine ray lies on an actual h-line through its start and its actual ideal endpoint. -/
theorem IsHLineRay.exists_containing_line {z : ℍ} {a : OnePoint ℂ} {R : Set ℍ}
    (h : IsHLineRay z a R) :
    ∃ L : HalfPlaneLine, z ∈ L.carrier ∧ a ∈ L.idealEndpoints ∧ R ⊆ L.carrier := by
  obtain ⟨γ, hγ, s, hs, hor, he⟩ := h
  obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_isHLine hγ.2
  have hsub : R ⊆ L.carrier := by
    rw [hL]
    rcases hor with rfl | rfl <;> exact image_subset_range _ _
  have ha : a ∈ hTraceIdealEndpoints R := he.symm ▸ mem_singleton a
  refine ⟨L, ?_, hTraceIdealEndpoints_mono hsub ha, hsub⟩
  rw [hL, ← hs]
  exact mem_range_self s

/-- Any chart-defined ray on a prescribed actual line is one of the two canonical chart half-lines. -/
theorem IsHLineRay.eq_one_of_rays_at {z : ℍ} {a : OnePoint ℂ} {R : Set ℍ}
    (h : IsHLineRay z a R) (L : HalfPlaneLine) (hz : z ∈ L.carrier) (ha : a ∈ L.idealEndpoints)
    (γ : ℝ → ℍ) (hγ : Isometry γ) (hrange : range γ = L.carrier) (s : ℝ) (hs : γ s = z) :
    R = forwardHLineRay γ s ∨ R = backwardHLineRay γ s := by
  obtain ⟨δ, hδ, t, ht, hor, he⟩ := h
  obtain ⟨M, hM⟩ := exists_halfPlaneLine_of_isHLine hδ.2
  have hsub : R ⊆ M.carrier := by
    rw [hM]
    rcases hor with rfl | rfl <;> exact image_subset_range _ _
  have hzM : z ∈ M.carrier := by rw [hM, ← ht]; exact mem_range_self t
  have haM : a ∈ M.idealEndpoints :=
    hTraceIdealEndpoints_mono hsub (he.symm ▸ mem_singleton a)
  have hML : M = L := M.eq_of_shared_ideal_and_interior L z hzM hz a haM ha
  have hrange' : range γ = range δ := hrange.trans ((congrArg HalfPlaneLine.carrier hML).symm.trans hM)
  have hbase : γ s = δ t := hs.trans ht.symm
  rcases hor with rfl | rfl
  · exact forwardHLineRay_eq_one_of_same_range hγ hδ.1 hrange' hbase
  · exact backwardHLineRay_eq_one_of_same_range hγ hδ.1 hrange' hbase

/-- The actual start and actual ideal endpoint determine one point-set ray, independently of charts. -/
theorem IsHLineRay.eq_of_same_start_ideal {z : ℍ} {a : OnePoint ℂ} {R S : Set ℍ}
    (hR : IsHLineRay z a R) (hS : IsHLineRay z a S) : R = S := by
  obtain ⟨L, hz, ha, _⟩ := hR.exists_containing_line
  obtain ⟨b, c, γ, s, hbc, _, hγ, hrange, hs, hB, hF, _, _⟩ := L.exists_rays_at z hz
  have hne : hTraceIdealEndpoints (backwardHLineRay γ s) ≠
      hTraceIdealEndpoints (forwardHLineRay γ s) := by
    intro he
    exact hbc (Set.singleton_injective (hB.idealEndpoints_eq.symm.trans (he.trans hF.idealEndpoints_eq)))
  have hRcases := hR.eq_one_of_rays_at L hz ha γ hγ.1 hrange s hs
  have hScases := hS.eq_one_of_rays_at L hz ha γ hγ.1 hrange s hs
  rcases hRcases with rfl | rfl <;> rcases hScases with rfl | rfl
  · rfl
  · exact (hne (hS.idealEndpoints_eq.trans hR.idealEndpoints_eq.symm)).elim
  · exact (hne (hR.idealEndpoints_eq.trans hS.idealEndpoints_eq.symm)).elim
  · rfl

/-- A unique genuine ray exists from each interior point toward each actual ideal point. -/
theorem existsUnique_hLineRay (z : ℍ) (a : OnePoint ℂ) (ha : a ∈ halfPlaneIdealBoundary) :
    ∃! R : Set ℍ, IsHLineRay z a R := by
  obtain ⟨R, hR⟩ := exists_hLineRay z a ha
  exact ⟨R, hR, fun S hS => hS.eq_of_same_start_ideal hR⟩

/-- The canonical geometric ray [z,a), defined by the proved chart-independent geometric relation. -/
def hRay (z : ℍ) (a : OnePoint ℂ) : Set ℍ := {u | ∃ R : Set ℍ, IsHLineRay z a R ∧ u ∈ R}

theorem hRay_eq_of_isHLineRay {z : ℍ} {a : OnePoint ℂ} {R : Set ℍ}
    (hR : IsHLineRay z a R) : hRay z a = R := by
  ext u
  constructor
  · rintro ⟨S, hS, hu⟩
    exact hS.eq_of_same_start_ideal hR ▸ hu
  · intro hu
    exact ⟨R, hR, hu⟩

theorem isHLineRay_hRay (z : ℍ) (a : OnePoint ℂ) (ha : a ∈ halfPlaneIdealBoundary) :
    IsHLineRay z a (hRay z a) := by
  obtain ⟨R, hR⟩ := exists_hLineRay z a ha
  rw [hRay_eq_of_isHLineRay hR]
  exact hR

theorem hRay_start_mem (z : ℍ) (a : OnePoint ℂ) (ha : a ∈ halfPlaneIdealBoundary) : z ∈ hRay z a :=
  (isHLineRay_hRay z a ha).start_mem

theorem hRay_idealEndpoints (z : ℍ) (a : OnePoint ℂ) (ha : a ∈ halfPlaneIdealBoundary) :
    hTraceIdealEndpoints (hRay z a) = {a} := (isHLineRay_hRay z a ha).idealEndpoints_eq

theorem hRay_isClosed (z : ℍ) (a : OnePoint ℂ) (ha : a ∈ halfPlaneIdealBoundary) :
    IsClosed (hRay z a) := by
  obtain ⟨γ, hγ, s, _, hor, _⟩ := isHLineRay_hRay z a ha
  rcases hor with he | he
  · rw [he]; exact forwardHLineRay_isClosed hγ.1 s
  · rw [he]; exact backwardHLineRay_isClosed hγ.1 s

theorem hRay_subset_line (L : HalfPlaneLine) (z : ℍ) (hz : z ∈ L.carrier)
    (a : OnePoint ℂ) (ha : a ∈ L.idealEndpoints) : hRay z a ⊆ L.carrier := by
  obtain ⟨R, hR, hsub⟩ := L.exists_ray_to_idealEndpoint z hz a ha
  rw [hRay_eq_of_isHLineRay hR]
  exact hsub

/-- The source's two-ray decomposition now uses canonical rays independent of every chart choice. -/
theorem HalfPlaneLine.exists_canonical_rays_at (L : HalfPlaneLine) (z : ℍ) (hz : z ∈ L.carrier) :
    ∃ a b : OnePoint ℂ, a ≠ b ∧ L.idealEndpoints = {a, b} ∧
      hRay z a ∪ hRay z b = L.carrier ∧ hRay z a ∩ hRay z b = {z} := by
  obtain ⟨a, b, γ, s, hab, he, _, _, _, hA, hB, hu, hi⟩ := L.exists_rays_at z hz
  exact ⟨a, b, hab, he, by rwa [hRay_eq_of_isHLineRay hA, hRay_eq_of_isHLineRay hB],
    by rwa [hRay_eq_of_isHLineRay hA, hRay_eq_of_isHLineRay hB]⟩

end

end LowDimensionalTopology.Geometry.Hyperbolic
