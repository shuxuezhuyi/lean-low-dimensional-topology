/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.GeodesicBoundary
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicRayUniqueness
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk.GeodesicSegments

/-!
# Native disc collinearity, ideal segments, and canonical rays

All ideal ends use actual closure in the complex one-point compactification.
The geodesic charts cover native Euclidean circles or diameters.
-/

@[expose] public section

open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- Actual ideal accumulation set of a disc trace. -/
def discTraceIdealEndpoints (S : Set 𝔻) : Set (OnePoint ℂ) :=
  closure (extendedDiscPoint '' S) ∩ extendedDiscIdealBoundary

theorem discTraceIdealEndpoints_cayley_image (S : Set ℍ) :
    discTraceIdealEndpoints (halfPlaneToDisc '' S) = extendedCayley '' hTraceIdealEndpoints S := by
  have he : extendedDiscPoint '' (halfPlaneToDisc '' S) =
      extendedCayley '' (extendedHalfPlanePoint '' S) := by
    rw [image_image, image_image]
    apply Set.image_congr
    intro z _
    exact (extendedCayley_halfPlane z).symm
  rw [discTraceIdealEndpoints, he, ← extendedCayley.image_closure,
    ← image_inter_preimage, extendedCayley_preimage_idealBoundary]
  rfl

theorem cayley_image_inverse_image (S : Set 𝔻) :
    halfPlaneToDisc '' (discToHalfPlane '' S) = S := by
  rw [image_image]
  simp only [halfPlaneToDisc_discToHalfPlane, image_id']

theorem inverse_cayley_image_image (S : Set ℍ) :
    discToHalfPlane '' (halfPlaneToDisc '' S) = S := by
  rw [image_image]
  simp only [discToHalfPlane_halfPlaneToDisc, image_id']

/-- A genuine complete unit-speed chart of a native Euclidean disc h-line. -/
def IsNativeDiscGeodesicParam (γ : ℝ → 𝔻) : Prop :=
  (letI := discHyperbolicMetric; Isometry γ) ∧ ∃ L : DiscLine, range γ = L.carrier

theorem inverse_cayley_isometry :
    letI := discHyperbolicMetric; Isometry discToHalfPlane := by
  let := discHyperbolicMetric
  exact Isometry.of_dist_eq (fun _ _ => rfl)

theorem IsHGeodesicParam.toNativeDisc {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ) :
    IsNativeDiscGeodesicParam (halfPlaneToDisc ∘ γ) := by
  let := discHyperbolicMetric
  obtain ⟨L,hL⟩ := exists_halfPlaneLine_of_isHLine hγ.2
  refine ⟨cayley_isometry.comp hγ.1,L.toDiscLine,?_⟩
  rw [range_comp, ← hL, HalfPlaneLine.toDiscLine_carrier,
    HalfPlaneLine.discCarrier_eq_cayley_image]

theorem IsNativeDiscGeodesicParam.toHalfPlane {γ : ℝ → 𝔻}
    (hγ : IsNativeDiscGeodesicParam γ) : IsHGeodesicParam (discToHalfPlane ∘ γ) := by
  let := discHyperbolicMetric
  obtain ⟨hiso,L,hL⟩ := hγ
  refine ⟨inverse_cayley_isometry.comp hiso,?_⟩
  have hr : range (discToHalfPlane ∘ γ) = L.toHalfPlane.carrier := by
    rw [range_comp, hL, L.carrier_eq_cayley_image_halfPlane, inverse_cayley_image_image]
  rw [hr]
  exact L.toHalfPlane.isHLine

/-- A native disc half-line trace with its actual ideal accumulation singleton. -/
def IsDiscHLineRay (z : 𝔻) (a : OnePoint ℂ) (R : Set 𝔻) : Prop :=
  ∃ γ : ℝ → 𝔻, IsNativeDiscGeodesicParam γ ∧ ∃ s : ℝ, γ s = z ∧
    (R = γ '' Ici s ∨ R = γ '' Iic s) ∧ discTraceIdealEndpoints R = {a}

theorem IsHLineRay.toDisc {z : ℍ} {a : OnePoint ℂ} {R : Set ℍ}
    (h : IsHLineRay z a R) :
    IsDiscHLineRay (halfPlaneToDisc z) (extendedCayley a) (halfPlaneToDisc '' R) := by
  obtain ⟨γ,hγ,s,hs,hor,he⟩ := h
  refine ⟨halfPlaneToDisc ∘ γ,hγ.toNativeDisc,s,congrArg halfPlaneToDisc hs,?_,?_⟩
  · rcases hor with hR | hR
    · exact Or.inl (by rw [hR, forwardHLineRay, image_image]; rfl)
    · exact Or.inr (by rw [hR, backwardHLineRay, image_image]; rfl)
  · rw [discTraceIdealEndpoints_cayley_image, he, image_singleton]

theorem IsDiscHLineRay.toHalfPlane {z : 𝔻} {a : OnePoint ℂ} {R : Set 𝔻}
    (h : IsDiscHLineRay z a R) :
    IsHLineRay (discToHalfPlane z) (extendedCayley.symm a) (discToHalfPlane '' R) := by
  obtain ⟨γ,hγ,s,hs,hor,he⟩ := h
  refine ⟨discToHalfPlane ∘ γ,hγ.toHalfPlane,s,congrArg discToHalfPlane hs,?_,?_⟩
  · rcases hor with hR | hR
    · exact Or.inl (by rw [hR, forwardHLineRay, image_image]; rfl)
    · exact Or.inr (by rw [hR, backwardHLineRay, image_image]; rfl)
  · apply (Set.image_injective.mpr extendedCayley.injective)
    rw [← discTraceIdealEndpoints_cayley_image, cayley_image_inverse_image, he,
      image_singleton, extendedCayley.apply_symm_apply]

theorem IsDiscHLineRay.eq_of_same_start_ideal {z : 𝔻} {a : OnePoint ℂ} {R S : Set 𝔻}
    (hR : IsDiscHLineRay z a R) (hS : IsDiscHLineRay z a S) : R = S := by
  apply (Set.image_injective.mpr discToHalfPlane_injective)
  exact hR.toHalfPlane.eq_of_same_start_ideal hS.toHalfPlane

theorem existsUnique_discHLineRay (z : 𝔻) (a : OnePoint ℂ)
    (ha : a ∈ extendedDiscIdealBoundary) : ∃! R : Set 𝔻, IsDiscHLineRay z a R := by
  have haH : extendedCayley.symm a ∈ halfPlaneIdealBoundary :=
    (idealBoundary_cayley_iff _).mpr (by simpa only [extendedCayley.apply_symm_apply] using ha)
  obtain ⟨R,hR⟩ := exists_hLineRay (discToHalfPlane z) (extendedCayley.symm a) haH
  have hD := hR.toDisc
  simp only [halfPlaneToDisc_discToHalfPlane, extendedCayley.apply_symm_apply] at hD
  exact ⟨halfPlaneToDisc '' R,hD,fun S hS => hS.eq_of_same_start_ideal hD⟩

/-- The canonical native disc ray; its geometric existence and uniqueness are proved above. -/
def discHRay (z : 𝔻) (a : OnePoint ℂ) : Set 𝔻 :=
  {u | ∃ R : Set 𝔻, IsDiscHLineRay z a R ∧ u ∈ R}

theorem discHRay_eq_of_isDiscHLineRay {z : 𝔻} {a : OnePoint ℂ} {R : Set 𝔻}
    (hR : IsDiscHLineRay z a R) : discHRay z a = R := by
  ext u
  constructor
  · rintro ⟨S,hS,hu⟩
    exact hS.eq_of_same_start_ideal hR ▸ hu
  · intro hu
    exact ⟨R,hR,hu⟩

theorem isDiscHLineRay_discHRay (z : 𝔻) (a : OnePoint ℂ) (ha : a ∈ extendedDiscIdealBoundary) :
    IsDiscHLineRay z a (discHRay z a) := by
  obtain ⟨R,hR,_⟩ := existsUnique_discHLineRay z a ha
  rw [discHRay_eq_of_isDiscHLineRay hR]
  exact hR

theorem discHRay_eq_cayley_image (z : 𝔻) (a : OnePoint ℂ) (ha : a ∈ extendedDiscIdealBoundary) :
    discHRay z a = halfPlaneToDisc '' hRay (discToHalfPlane z) (extendedCayley.symm a) := by
  have haH : extendedCayley.symm a ∈ halfPlaneIdealBoundary :=
    (idealBoundary_cayley_iff _).mpr (by simpa only [extendedCayley.apply_symm_apply] using ha)
  have hD := (isHLineRay_hRay (discToHalfPlane z) (extendedCayley.symm a) haH).toDisc
  simp only [halfPlaneToDisc_discToHalfPlane, extendedCayley.apply_symm_apply] at hD
  exact discHRay_eq_of_isDiscHLineRay hD

theorem discHRay_start_mem (z : 𝔻) (a : OnePoint ℂ) (ha : a ∈ extendedDiscIdealBoundary) :
    z ∈ discHRay z a := by
  rw [discHRay_eq_cayley_image z a ha]
  refine ⟨discToHalfPlane z,hRay_start_mem _ _ ?_,halfPlaneToDisc_discToHalfPlane z⟩
  exact (idealBoundary_cayley_iff _).mpr (by simpa only [extendedCayley.apply_symm_apply] using ha)

theorem discHRay_idealEndpoints (z : 𝔻) (a : OnePoint ℂ) (ha : a ∈ extendedDiscIdealBoundary) :
    discTraceIdealEndpoints (discHRay z a) = {a} := by
  obtain ⟨γ,hγ,s,hs,hor,he⟩ := isDiscHLineRay_discHRay z a ha
  exact he

theorem discHRay_isClosed (z : 𝔻) (a : OnePoint ℂ) (ha : a ∈ extendedDiscIdealBoundary) :
    IsClosed (discHRay z a) := by
  rw [discHRay_eq_cayley_image z a ha]
  apply cayleyHomeomorph.isClosedMap
  apply hRay_isClosed
  exact (idealBoundary_cayley_iff _).mpr (by simpa only [extendedCayley.apply_symm_apply] using ha)

/-- Collinearity is containment in one actual native Euclidean disc h-line. -/
def DiscHCollinear {ι : Type*} (p : ι → 𝔻) : Prop := ∃ L : DiscLine, ∀ i, p i ∈ L.carrier

theorem discHCollinear_iff {ι : Type*} (p : ι → 𝔻) :
    DiscHCollinear p ↔ HCollinear (discToHalfPlane ∘ p) := by
  constructor
  · rintro ⟨L,hL⟩
    exact ⟨L.toHalfPlane,fun i => (L.mem_carrier (p i)).mp (hL i)⟩
  · rintro ⟨L,hL⟩
    refine ⟨L.toDiscLine,fun i => ?_⟩
    rw [HalfPlaneLine.toDiscLine_carrier, HalfPlaneLine.discCarrier_eq_cayley_image]
    exact ⟨discToHalfPlane (p i),hL i,halfPlaneToDisc_discToHalfPlane (p i)⟩

theorem HalfPlaneLine.toDiscLine_idealEndpoints (L : HalfPlaneLine) :
    L.toDiscLine.idealEndpoints = extendedCayley '' L.idealEndpoints := by
  change discTraceIdealEndpoints L.toDiscLine.carrier = _
  rw [HalfPlaneLine.toDiscLine_carrier, HalfPlaneLine.discCarrier_eq_cayley_image,
    discTraceIdealEndpoints_cayley_image]
  rfl

theorem DiscLine.idealEndpoints_pair_inverse (L : DiscLine) {a b : OnePoint ℂ}
    (he : L.idealEndpoints = {a,b}) :
    L.toHalfPlane.idealEndpoints = {extendedCayley.symm a,extendedCayley.symm b} := by
  apply (Set.image_injective.mpr extendedCayley.injective)
  rw [← L.idealEndpoints_eq_cayley_image, he, image_pair,
    extendedCayley.apply_symm_apply, extendedCayley.apply_symm_apply]

/-- The ideal-to-ideal native disc segment is defined using genuine carrier endpoints. -/
def idealDiscHSegment (a b : OnePoint ℂ) : Set 𝔻 :=
  {z | ∃ L : DiscLine, L.idealEndpoints = {a,b} ∧ z ∈ L.carrier}

theorem idealDiscHSegment_eq_carrier (L : DiscLine) {a b : OnePoint ℂ}
    (he : L.idealEndpoints = {a,b}) : idealDiscHSegment a b = L.carrier := by
  ext z
  constructor
  · rintro ⟨M,hM,hz⟩
    have hML : M = L := DiscLine.idealEndpoints_injective (hM.trans he.symm)
    exact hML ▸ hz
  · intro hz
    exact ⟨L,he,hz⟩

theorem existsUnique_discLine_of_idealEndpoints (a b : OnePoint ℂ)
    (ha : a ∈ extendedDiscIdealBoundary) (hb : b ∈ extendedDiscIdealBoundary) (hab : a ≠ b) :
    ∃! L : DiscLine, L.idealEndpoints = {a,b} := by
  have haH : extendedCayley.symm a ∈ halfPlaneIdealBoundary :=
    (idealBoundary_cayley_iff _).mpr (by simpa only [extendedCayley.apply_symm_apply] using ha)
  have hbH : extendedCayley.symm b ∈ halfPlaneIdealBoundary :=
    (idealBoundary_cayley_iff _).mpr (by simpa only [extendedCayley.apply_symm_apply] using hb)
  obtain ⟨L,hL,_⟩ := existsUnique_halfPlaneLine_of_idealEndpoints
    (extendedCayley.symm a) (extendedCayley.symm b) haH hbH (extendedCayley.symm.injective.ne hab)
  have hD : L.toDiscLine.idealEndpoints = {a,b} := by
    rw [L.toDiscLine_idealEndpoints, hL, image_pair,
      extendedCayley.apply_symm_apply, extendedCayley.apply_symm_apply]
  exact ⟨L.toDiscLine,hD,fun M hM => DiscLine.idealEndpoints_injective (hM.trans hD.symm)⟩

theorem idealDiscHSegment_eq_cayley_image (a b : OnePoint ℂ)
    (ha : a ∈ extendedDiscIdealBoundary) (hb : b ∈ extendedDiscIdealBoundary) (hab : a ≠ b) :
    idealDiscHSegment a b = halfPlaneToDisc ''
      idealHSegment (extendedCayley.symm a) (extendedCayley.symm b) := by
  obtain ⟨L,he,_⟩ := existsUnique_discLine_of_idealEndpoints a b ha hb hab
  rw [idealDiscHSegment_eq_carrier L he,
    idealHSegment_eq_carrier L.toHalfPlane (extendedCayley.symm a) (extendedCayley.symm b)
      (L.idealEndpoints_pair_inverse he),
    L.carrier_eq_cayley_image_halfPlane]

theorem existsUnique_discLine_through_point_and_idealEndpoint (z : 𝔻) (a : OnePoint ℂ)
    (ha : a ∈ extendedDiscIdealBoundary) :
    ∃! L : DiscLine, z ∈ L.carrier ∧ a ∈ L.idealEndpoints := by
  have haH : extendedCayley.symm a ∈ halfPlaneIdealBoundary :=
    (idealBoundary_cayley_iff _).mpr (by simpa only [extendedCayley.apply_symm_apply] using ha)
  obtain ⟨L,⟨hz,hE⟩,_⟩ := existsUnique_halfPlaneLine_through_point_and_idealEndpoint
    (discToHalfPlane z) (extendedCayley.symm a) haH
  have hzD : z ∈ L.toDiscLine.carrier := by
    rw [HalfPlaneLine.toDiscLine_carrier, HalfPlaneLine.discCarrier_eq_cayley_image]
    exact ⟨discToHalfPlane z,hz,halfPlaneToDisc_discToHalfPlane z⟩
  have haD : a ∈ L.toDiscLine.idealEndpoints := by
    rw [L.toDiscLine_idealEndpoints]
    exact ⟨extendedCayley.symm a,hE,extendedCayley.apply_symm_apply a⟩
  exact ⟨L.toDiscLine,⟨hzD,haD⟩,fun M hM =>
    M.eq_of_shared_ideal_and_interior L.toDiscLine z hM.1 hzD a hM.2 haD⟩

theorem discHRay_subset_line (L : DiscLine) (z : 𝔻) (hz : z ∈ L.carrier)
    (a : OnePoint ℂ) (ha : a ∈ L.idealEndpoints) : discHRay z a ⊆ L.carrier := by
  have haD : a ∈ extendedDiscIdealBoundary := ha.2
  rw [discHRay_eq_cayley_image z a haD, L.carrier_eq_cayley_image_halfPlane]
  apply Set.image_mono
  apply hRay_subset_line L.toHalfPlane _ ((L.mem_carrier z).mp hz)
  rw [L.idealEndpoints_eq_cayley_image] at ha
  obtain ⟨b,hb,hba⟩ := ha
  simpa only [← hba, extendedCayley.symm_apply_apply] using hb

theorem DiscLine.exists_canonical_rays_at (L : DiscLine) (z : 𝔻) (hz : z ∈ L.carrier) :
    ∃ a b : OnePoint ℂ, a ≠ b ∧ L.idealEndpoints = {a,b} ∧
      discHRay z a ∪ discHRay z b = L.carrier ∧ discHRay z a ∩ discHRay z b = {z} := by
  obtain ⟨a,b,hab,he,hu,hi⟩ := L.toHalfPlane.exists_canonical_rays_at
    (discToHalfPlane z) ((L.mem_carrier z).mp hz)
  have ha : a ∈ halfPlaneIdealBoundary := (he.symm ▸ (mem_insert a {b})).2
  have hb : b ∈ halfPlaneIdealBoundary := (he.symm ▸ (mem_insert_of_mem a (mem_singleton b))).2
  have haD := (idealBoundary_cayley_iff a).mp ha
  have hbD := (idealBoundary_cayley_iff b).mp hb
  have hRa : discHRay z (extendedCayley a) = halfPlaneToDisc '' hRay (discToHalfPlane z) a := by
    simpa only [extendedCayley.symm_apply_apply] using discHRay_eq_cayley_image z _ haD
  have hRb : discHRay z (extendedCayley b) = halfPlaneToDisc '' hRay (discToHalfPlane z) b := by
    simpa only [extendedCayley.symm_apply_apply] using discHRay_eq_cayley_image z _ hbD
  refine ⟨extendedCayley a,extendedCayley b,extendedCayley.injective.ne hab,?_,?_,?_⟩
  · rw [L.idealEndpoints_eq_cayley_image, he, image_pair]
  · rw [hRa,hRb,← image_union,hu,L.carrier_eq_cayley_image_halfPlane]
  · rw [hRa,hRb,← image_inter (show Function.Injective halfPlaneToDisc from
    cayleyHomeomorph.injective),hi,image_singleton,
      halfPlaneToDisc_discToHalfPlane]

end
end LowDimensionalTopology.Geometry.Hyperbolic
