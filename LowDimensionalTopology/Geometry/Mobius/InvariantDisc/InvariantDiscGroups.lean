/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier

public import LowDimensionalTopology.Geometry.Mobius.Classification.MobiusTypes
public import LowDimensionalTopology.Geometry.Mobius.Trace.DiscTraces
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.Mobius

/-!
# Actual invariant discs and fixed-point locations
-/

@[expose] public section

open Set Function
open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Mobius

open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

noncomputable section

theorem frontier_extendedUnitDisc_eq_circle :
    frontier Hyperbolic.extendedUnitDisc = complexCircle 0 1 := by
  have hcl : closure Hyperbolic.extendedUnitDisc ⊆ Hyperbolic.extendedClosedUnitDisc :=
    closure_minimal Hyperbolic.extendedUnitDisc_subset_closed Hyperbolic.isClosed_extendedClosedUnitDisc
  rw [frontier, isOpen_extendedUnitDisc.interior_eq]
  ext z
  induction z using OnePoint.rec with
  | infty =>
    constructor
    · rintro ⟨hz, _⟩
      have hh := hcl hz
      simp [Hyperbolic.extendedClosedUnitDisc] at hh
    · intro hz
      simp at hz
  | coe z =>
    simp only [mem_sdiff, complexCircle_coe, sub_zero]
    constructor
    · rintro ⟨hz, hn⟩
      exact le_antisymm ((Hyperbolic.coe_mem_extendedClosedUnitDisc z).mp (hcl hz))
        (le_of_not_gt (fun hh => hn ((Hyperbolic.coe_mem_extendedUnitDisc z).mpr hh)))
    · intro hz
      exact ⟨Hyperbolic.unitCircle_mem_closure_extendedUnitDisc hz,
        fun hh => (lt_irrefl (1 : ℝ)) (hz ▸ (Hyperbolic.coe_mem_extendedUnitDisc z).mp hh)⟩

theorem mem_complexUnitCircle_iff (z : ExtendedComplex) :
    z ∈ complexCircle 0 1 ↔ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ z = (ζ : ExtendedComplex) := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => simp only [complexCircle_coe, sub_zero, OnePoint.coe_eq_coe]; aesop

theorem complexDisc_frontier_normalize {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D) :
    ∃ q : complexMobiusGroup,
      (q : Equiv.Perm ExtendedComplex) '' D = Hyperbolic.extendedUnitDisc ∧
      (q : Equiv.Perm ExtendedComplex) '' frontier D = complexCircle 0 1 := by
  obtain ⟨q, hq⟩ := hD.normalize
  refine ⟨q, hq, ?_⟩
  change (mobiusBoundaryHomeomorph q) '' frontier D = _
  rw [Homeomorph.image_frontier]
  change frontier ((q : Equiv.Perm ExtendedComplex) '' D) = _
  rw [hq, frontier_extendedUnitDisc_eq_circle]

theorem complexDisc_frontier_isGeneralized {D : Set ExtendedComplex}
    (hD : IsComplexOpenDisc D) : IsComplexGeneralizedCircle (frontier D) := by
  obtain ⟨q, _, hq⟩ := complexDisc_frontier_normalize hD
  have hc := (complexCircle_isGeneralized 0 1 zero_lt_one).image (q⁻¹).property.1
  have he : ((q⁻¹ : complexMobiusGroup) : Equiv.Perm ExtendedComplex) '' complexCircle 0 1 = frontier D := by
    rw [← hq, image_image]
    simp
  rwa [he] at hc

theorem mobius_disc_conjugate_preserves {D : Set ExtendedComplex} (f q : complexMobiusGroup)
    (hq : (q : Equiv.Perm ExtendedComplex) '' D = Hyperbolic.extendedUnitDisc)
    (hf : (f : Equiv.Perm ExtendedComplex) '' D = D) :
    ((q * f * q⁻¹ : complexMobiusGroup) : Equiv.Perm ExtendedComplex) '' Hyperbolic.extendedUnitDisc =
      Hyperbolic.extendedUnitDisc := by
  rw [← hq]
  have he : (fun z => ((q * f * q⁻¹ : complexMobiusGroup) : Equiv.Perm ExtendedComplex)
      ((q : Equiv.Perm ExtendedComplex) z)) =
      (fun z => (q : Equiv.Perm ExtendedComplex) ((f : Equiv.Perm ExtendedComplex) z)) := by
    funext z
    change (q : Equiv.Perm ExtendedComplex) ((f : Equiv.Perm ExtendedComplex)
      ((q : Equiv.Perm ExtendedComplex).symm ((q : Equiv.Perm ExtendedComplex) z))) = _
    rw [Equiv.symm_apply_apply]
  rw [image_image, he, ← image_image, hf]

theorem mobius_disc_conjugate_fixed (f q : complexMobiusGroup) {z : ExtendedComplex}
    (hz : (f : Equiv.Perm ExtendedComplex) z = z) :
    ((q * f * q⁻¹ : complexMobiusGroup) : Equiv.Perm ExtendedComplex)
      ((q : Equiv.Perm ExtendedComplex) z) = (q : Equiv.Perm ExtendedComplex) z := by
  change (q : Equiv.Perm ExtendedComplex) ((f : Equiv.Perm ExtendedComplex)
    ((q : Equiv.Perm ExtendedComplex).symm ((q : Equiv.Perm ExtendedComplex) z))) = _
  rw [Equiv.symm_apply_apply, hz]

/-- The boundary-location statement for hyperbolic maps and every actual invariant disc. -/
theorem mobiusHyperbolic_fixed_mem_disc_frontier (f : complexMobiusGroup)
    (hf : MobiusHyperbolic f) {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' D = D) {z : ExtendedComplex}
    (hz : (f : Equiv.Perm ExtendedComplex) z = z) : z ∈ frontier D := by
  obtain ⟨q, hq, hqfront⟩ := complexDisc_frontier_normalize hD
  obtain ⟨r, hr, htrace⟩ := (mobius_hyperbolic_iff_squaredTrace_real_gt_four f hf.1.1).mp hf
  have ht : 4 < (mobiusSquaredTrace (q * f * q⁻¹)).re := by
    rw [mobiusSquaredTrace_conjugation, htrace, Complex.ofReal_re]
    exact hr
  obtain ⟨ζ, hζ, hqz⟩ := Mobius.mobius_disc_trace_gt_four_fixed_circle (q * f * q⁻¹)
    (mobius_disc_conjugate_preserves f q hq hpres) ht (mobius_disc_conjugate_fixed f q hz)
  have hm : (q : Equiv.Perm ExtendedComplex) z ∈
      (q : Equiv.Perm ExtendedComplex) '' frontier D := by
    rw [hqfront, hqz]
    simpa only [complexCircle_coe, sub_zero] using hζ
  obtain ⟨w, hw, hwz⟩ := hm
  exact (q : Equiv.Perm ExtendedComplex).injective hwz ▸ hw

/-- Elliptic fixed points avoid the boundary of every actual invariant disc. -/
theorem mobiusElliptic_fixed_not_mem_disc_frontier (f : complexMobiusGroup)
    (hf : MobiusElliptic f) {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' D = D) {z : ExtendedComplex}
    (hz : (f : Equiv.Perm ExtendedComplex) z = z) : z ∉ frontier D := by
  intro hmem
  obtain ⟨q, hq, hqfront⟩ := complexDisc_frontier_normalize hD
  obtain ⟨r, _, hr, htrace⟩ := (mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four f hf.1).mp hf
  have ht : (mobiusSquaredTrace (q * f * q⁻¹)).re < 4 := by
    rw [mobiusSquaredTrace_conjugation, htrace, Complex.ofReal_re]
    exact hr
  have hc : (q : Equiv.Perm ExtendedComplex) z ∈ complexCircle 0 1 := by
    rw [← hqfront]
    exact mem_image_of_mem _ hmem
  obtain ⟨ζ, hζ, hqz⟩ := (mem_complexUnitCircle_iff _).mp hc
  have hfix := mobius_disc_conjugate_fixed f q hz
  rw [hqz] at hfix
  exact Mobius.mobius_disc_trace_lt_four_not_fixed_circle (q * f * q⁻¹)
    (mobius_disc_conjugate_preserves f q hq hpres) ht hζ hfix

/-- Exact intertwining of the actual complex action with its real Euclidean representative. -/
theorem mobiusRealRepresentative_apply_complex (f : complexMobiusGroup) (z : ExtendedComplex) :
    (mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2) (extendedComplexEuclideanHomeomorph z) =
      extendedComplexEuclideanHomeomorph ((f : Equiv.Perm ExtendedComplex) z) := by
  have h := congrArg (fun k : Equiv.Perm ExtendedComplex => k z)
    (mobiusRealRepresentative_coordinates f)
  apply extendedComplexEuclideanHomeomorph.symm.injective
  simpa only [euclideanToComplexHom_apply, Homeomorph.symm_apply_apply] using h

theorem mobiusRealRepresentative_image_complex (f : complexMobiusGroup) (S : Set ExtendedComplex) :
    (mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2) ''
        (extendedComplexEuclideanHomeomorph '' S) =
      extendedComplexEuclideanHomeomorph '' ((f : Equiv.Perm ExtendedComplex) '' S) := by
  rw [image_image, image_image]
  congr 1
  funext z
  exact mobiusRealRepresentative_apply_complex f z

/-- Parabolic fixed points lie on every actual preserved disc boundary. -/
theorem mobiusParabolic_fixed_mem_disc_frontier (f : complexMobiusGroup)
    (hf : MobiusParabolic f) {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' D = D) {z : ExtendedComplex}
    (hz : (f : Equiv.Perm ExtendedComplex) z = z) : z ∈ frontier D := by
  let e := extendedComplexEuclideanHomeomorph
  have hround : Inversive.IsGeneralizedSphere (frontier (e '' D)) := by
    rw [← e.image_frontier]
    exact complexDisc_frontier_isGeneralized hD
  have hinv : (mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2) '' (e '' D) = e '' D := by
    rw [mobiusRealRepresentative_image_complex, hpres]
  have hz' : (mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2) (e z) = e z := by
    rw [mobiusRealRepresentative_apply_complex, hz]
  have hmem := Mobius.mobiusBoundaryParabolic_fixed_mem_boundary f hf
    (mobiusRealRepresentative f) (mobiusRealRepresentative f).property
    (mobiusRealRepresentative_coordinates f) (e '' D) hround hinv hz'
  rw [← e.image_frontier] at hmem
  obtain ⟨w, hw, hwz⟩ := hmem
  exact e.injective hwz ▸ hw

/-- Inversion in the actual disc boundary carries fixed points to fixed points. -/
theorem mobius_fixed_inverse_pair_of_preserved_disc (f : complexMobiusGroup)
    {D : Set ExtendedComplex}
    (hpres : (f : Equiv.Perm ExtendedComplex) '' D = D) {z w : ExtendedComplex}
    (hzw : Inversive.IsInversePair (extendedComplexEuclideanHomeomorph '' frontier D)
      (extendedComplexEuclideanHomeomorph z) (extendedComplexEuclideanHomeomorph w))
    (hz : (f : Equiv.Perm ExtendedComplex) z = z) :
    (f : Equiv.Perm ExtendedComplex) w = w := by
  let e := extendedComplexEuclideanHomeomorph
  have hinv : (mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2) '' (e '' frontier D) =
      e '' frontier D := by
    rw [mobiusRealRepresentative_image_complex]
    change e '' ((mobiusBoundaryHomeomorph f) '' frontier D) = _
    rw [Homeomorph.image_frontier]
    change e '' frontier ((f : Equiv.Perm ExtendedComplex) '' D) = _
    rw [hpres]
  have hz' : (mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2) (e z) = e z := by
    rw [mobiusRealRepresentative_apply_complex, hz]
  have hw := Mobius.inverse_pair_fixed_of_invariant_sphere (mobiusRealRepresentative f)
    (mobiusRealRepresentative f).property (e '' frontier D) hinv hzw hz'
  rw [mobiusRealRepresentative_apply_complex] at hw
  exact e.injective hw

/-- Every elliptic boundary fixed point has a distinct fixed inverse point in the actual round boundary. -/
theorem mobiusElliptic_fixed_has_distinct_inverse (f : complexMobiusGroup)
    (hf : MobiusElliptic f) {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' D = D) {z : ExtendedComplex}
    (hz : (f : Equiv.Perm ExtendedComplex) z = z) :
    ∃ w : ExtendedComplex, z ≠ w ∧
      Inversive.IsInversePair (extendedComplexEuclideanHomeomorph '' frontier D)
        (extendedComplexEuclideanHomeomorph z) (extendedComplexEuclideanHomeomorph w) ∧
      (f : Equiv.Perm ExtendedComplex) w = w := by
  let e := extendedComplexEuclideanHomeomorph
  have hround : Inversive.IsGeneralizedSphere (e '' frontier D) := complexDisc_frontier_isGeneralized hD
  obtain ⟨R, hR, hRS⟩ := (Inversive.isGeneralizedSphere_iff_fixedPoints_reflection _).mp hround
  let w := e.symm (R (e z))
  have hwz : z ≠ w := by
    intro heq
    have hfixed : R (e z) = e z := by
      have he := congrArg e heq
      dsimp only [w] at he
      rw [e.apply_symm_apply] at he
      exact he.symm
    have hm : e z ∈ e '' frontier D := by rw [← hRS]; exact hfixed
    obtain ⟨v, hv, hvz⟩ := hm
    have hzmem : z ∈ frontier D := e.injective hvz ▸ hv
    exact mobiusElliptic_fixed_not_mem_disc_frontier f hf hD hpres hz hzmem
  have hpair : Inversive.IsInversePair (e '' frontier D) (e z) (e w) := by
    refine ⟨R, hR, hRS, ?_⟩
    exact (e.apply_symm_apply (R (e z))).symm
  exact ⟨w, hwz, hpair, mobius_fixed_inverse_pair_of_preserved_disc f hpres hpair hz⟩

/-- These two inverse points exhaust the fixed points of the nonidentity actual Mobius map. -/
theorem mobiusElliptic_fixed_inverse_pair_complete (f : complexMobiusGroup)
    (hf : MobiusElliptic f) {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' D = D) {z : ExtendedComplex}
    (hz : (f : Equiv.Perm ExtendedComplex) z = z) :
    ∃ w : ExtendedComplex, z ≠ w ∧
      Inversive.IsInversePair (extendedComplexEuclideanHomeomorph '' frontier D)
        (extendedComplexEuclideanHomeomorph z) (extendedComplexEuclideanHomeomorph w) ∧
      ∀ v, (f : Equiv.Perm ExtendedComplex) v = v ↔ v = z ∨ v = w := by
  obtain ⟨w, hzw, hpair, hw⟩ := mobiusElliptic_fixed_has_distinct_inverse f hf hD hpres hz
  refine ⟨w, hzw, hpair, fun v => ?_⟩
  constructor
  · intro hv
    by_contra hn
    have hvz : v ≠ z := fun h => hn (Or.inl h)
    have hvw : v ≠ w := fun h => hn (Or.inr h)
    have heq := mobius_eq_of_agree_triple f 1 z w v ⟨hzw, hvz.symm, hvw.symm⟩
      (by simpa using hz) (by simpa using hw) (by simpa using hv)
    exact hf.1 heq
  · rintro (rfl | rfl)
    · exact hz
    · exact hw

/-- Both actual elliptic fixed points exist, are inverse points, and avoid the preserved boundary. -/
theorem mobiusElliptic_fixed_pair_of_preserved_disc (f : complexMobiusGroup)
    (hf : MobiusElliptic f) {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' D = D) :
    ∃ z w : ExtendedComplex, z ≠ w ∧ z ∉ frontier D ∧ w ∉ frontier D ∧
      Inversive.IsInversePair (extendedComplexEuclideanHomeomorph '' frontier D)
        (extendedComplexEuclideanHomeomorph z) (extendedComplexEuclideanHomeomorph w) ∧
      ∀ v, (f : Equiv.Perm ExtendedComplex) v = v ↔ v = z ∨ v = w := by
  obtain ⟨z, hz⟩ := Mobius.Classification.exists_fixedPoint (complexMobiusEquivFractionalLinear f)
  have hz' : (f : Equiv.Perm ExtendedComplex) z = z := by
    simpa only [complexMobiusEquivFractionalLinear_apply] using hz
  obtain ⟨w, hzw, hpair, hfixed⟩ := mobiusElliptic_fixed_inverse_pair_complete f hf hD hpres hz'
  exact ⟨z, w, hzw, mobiusElliptic_fixed_not_mem_disc_frontier f hf hD hpres hz',
    mobiusElliptic_fixed_not_mem_disc_frontier f hf hD hpres ((hfixed w).mpr (Or.inr rfl)),
    hpair, hfixed⟩

/-- The literal group-invariant geometric-disc condition. -/
def HasInvariantComplexDisc (H : Subgroup complexMobiusGroup) : Prop :=
  ∃ D : Set ExtendedComplex, IsComplexOpenDisc D ∧
    ∀ f : H, (f.val : Equiv.Perm ExtendedComplex) '' D = D

/-- The necessary direction holds for all groups. -/
theorem HasInvariantComplexDisc.no_strictly_loxodromic (H : Subgroup complexMobiusGroup)
    (h : HasInvariantComplexDisc H) : ∀ f : H, ¬MobiusStrictlyLoxodromic f.val := by
  obtain ⟨D, hD, hinv⟩ := h
  intro f hf
  exact hf.2 ⟨hf.1, D, hD, hinv f⟩

end
end LowDimensionalTopology.Geometry.Mobius
