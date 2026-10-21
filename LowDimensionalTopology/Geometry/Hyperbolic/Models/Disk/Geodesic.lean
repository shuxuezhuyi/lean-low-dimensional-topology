module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Mobius.Circle.ComplexCircles
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicOrthogonality

/-!
# Native Euclidean h-lines in the disc

. A native disc line is the actual arc of a genuine generalized
circle geometrically orthogonal to the unit circle. The native carriers are
proved exactly equal to the Cayley images of the existing half-plane h-lines.
Incidence, genuine Euclidean reflections, and perpendicularity are established
for these carriers; reflection isometry uses the actual weighted metric.
-/

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane Complex.UnitDisc OnePoint RealInnerProductSpace ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius

/-- The unit circle, with its actual finite geometric carrier. -/
def discBoundaryCircle : Mobius.ComplexGeneralizedCircle :=
  ⟨Mobius.complexCircle 0 1, Mobius.complexCircle_isGeneralized 0 1 zero_lt_one⟩

/-- The completed real axis, with its actual finite and infinite points. -/
def halfPlaneBoundaryCircle : Mobius.ComplexGeneralizedCircle :=
  ⟨Mobius.complexRealAxis, Mobius.complexRealAxis_isGeneralized⟩

/-- The exact Cayley map as an element of the actual orientation-preserving Möbius group. -/
def cayleyMobius : Mobius.complexMobiusGroup := Mobius.mobiusMatrixProjection extendedCayleyMatrix

@[simp] theorem cayleyMobius_apply (z : Mobius.ExtendedComplex) :
    (cayleyMobius : Equiv.Perm Mobius.ExtendedComplex) z = extendedCayley z := rfl

theorem halfPlaneBoundaryCircle_realModel : halfPlaneBoundaryCircle.realModel =
    Inversive.planeGeneralizedSphere (Mobius.complexPlaneCoordinates Complex.I) 0
      ((Mobius.complexPlaneCoordinates.map_ne_zero_iff).mpr Complex.I_ne_zero) := by
  apply Subtype.ext
  change Mobius.extendedComplexEuclideanHomeomorph '' Mobius.complexRealAxis = _
  rw [Mobius.complexRealAxis_eq_line]
  exact Mobius.complexChart_image_preimage _

theorem discBoundaryCircle_realModel : discBoundaryCircle.realModel =
    Inversive.euclideanGeneralizedSphere (0 : Inversive.Euclidean 2) 1 zero_lt_one := by
  apply Subtype.ext
  change Mobius.extendedComplexEuclideanHomeomorph '' Mobius.complexCircle 0 1 = Inversive.extendedSphere (0 :
    Inversive.Euclidean 2) 1
  simpa only [Mobius.complexCircle, map_zero] using Mobius.complexChart_image_preimage (Inversive.extendedSphere (0 :
    Inversive.Euclidean 2) 1)

theorem halfPlaneIdealBoundary_eq_realAxis : halfPlaneIdealBoundary = Mobius.complexRealAxis := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [halfPlaneIdealBoundary]
  | coe z => simp [coe_mem_halfPlaneIdealBoundary]

theorem extendedDiscIdealBoundary_eq_circle : extendedDiscIdealBoundary = Mobius.complexCircle 0 1 := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [extendedDiscIdealBoundary]
  | coe z => simp [coe_mem_extendedDiscIdealBoundary]

theorem cayley_image_boundary : halfPlaneBoundaryCircle.image cayleyMobius = discBoundaryCircle := by
  apply Subtype.ext
  change (cayleyMobius : Equiv.Perm Mobius.ExtendedComplex) '' Mobius.complexRealAxis = Mobius.complexCircle 0 1
  rw [← halfPlaneIdealBoundary_eq_realAxis, ← extendedDiscIdealBoundary_eq_circle]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (idealBoundary_cayley_iff w).mp hw
  · intro hz
    refine ⟨extendedCayley.symm z, ?_, by simp⟩
    apply (idealBoundary_cayley_iff _).mpr
    simpa using hz

/-- The complete Euclidean generalized circle underlying a half-plane h-line. -/
def HalfPlaneLine.extendedCircle : HalfPlaneLine → Mobius.ComplexGeneralizedCircle
  | .vertical x => ⟨Mobius.complexLine 1 x, Mobius.complexLine_isGeneralized 1 x one_ne_zero⟩
  | .circle c r hr => ⟨Mobius.complexCircle c r, Mobius.complexCircle_isGeneralized c r hr⟩

@[simp] theorem HalfPlaneLine.mem_extendedCircle (L : HalfPlaneLine) (z : ℍ) :
    ((z : ℂ) : Mobius.ExtendedComplex) ∈ L.extendedCircle.val ↔ z ∈ L.carrier := by
  cases L with
  | vertical x => simp [HalfPlaneLine.extendedCircle, HalfPlaneLine.carrier, Complex.inner]
  | circle c r hr => exact Mobius.complexCircle_coe c z r

theorem complexLine_realModel (a : ℂ) (t : ℝ) (ha : a ≠ 0) :
    Mobius.ComplexGeneralizedCircle.realModel ⟨Mobius.complexLine a t, Mobius.complexLine_isGeneralized a t ha⟩ =
      Inversive.planeGeneralizedSphere (Mobius.complexPlaneCoordinates
        a) t ((Mobius.complexPlaneCoordinates.map_ne_zero_iff).mpr ha) := by
  apply Subtype.ext
  exact Mobius.complexChart_image_preimage _

theorem complexCircle_realModel (c : ℂ) (r : ℝ) (hr : 0 < r) :
    Mobius.ComplexGeneralizedCircle.realModel ⟨Mobius.complexCircle c r, Mobius.complexCircle_isGeneralized c r hr⟩ =
      Inversive.euclideanGeneralizedSphere (Mobius.complexPlaneCoordinates c) r hr := by
  apply Subtype.ext
  exact Mobius.complexChart_image_preimage _

theorem HalfPlaneLine.extendedCircle_orthogonal_boundary (L : HalfPlaneLine) :
    Mobius.ComplexCirclesOrthogonal L.extendedCircle halfPlaneBoundaryCircle := by
  rw [Mobius.complexCirclesOrthogonal_iff_inversiveProduct_zero, halfPlaneBoundaryCircle_realModel]
  cases L with
  | vertical x =>
    rw [HalfPlaneLine.extendedCircle, complexLine_realModel 1 x one_ne_zero, Inversive.inversiveProduct_plane_plane]
    simp [Mobius.complexPlaneCoordinates.inner_map_map, Complex.inner]
  | circle c r hr =>
    rw [HalfPlaneLine.extendedCircle, complexCircle_realModel c r hr, Inversive.inversiveProduct_sphere_plane]
    simp [Mobius.complexPlaneCoordinates.inner_map_map, Complex.inner]

/-- The actual generalized circle of a disc h-line, obtained by the geometric Cayley map. -/
def HalfPlaneLine.discCircle (L : HalfPlaneLine) : Mobius.ComplexGeneralizedCircle :=
  L.extendedCircle.image cayleyMobius

theorem HalfPlaneLine.discCircle_orthogonal_boundary (L : HalfPlaneLine) :
    Mobius.ComplexCirclesOrthogonal L.discCircle discBoundaryCircle := by
  rw [← cayley_image_boundary]
  exact L.extendedCircle_orthogonal_boundary.image _ _ cayleyMobius

/-- The native point set of this disc circle, before any appeal to a transported metric. -/
def HalfPlaneLine.discCarrier (L : HalfPlaneLine) : Set 𝔻 :=
  {z | ((z : ℂ) : Mobius.ExtendedComplex) ∈ L.discCircle.val}

theorem HalfPlaneLine.mem_discCarrier (L : HalfPlaneLine) (z : 𝔻) :
    z ∈ L.discCarrier ↔ discToHalfPlane z ∈ L.carrier := by
  have hp : (cayleyMobius : Equiv.Perm Mobius.ExtendedComplex)
      (((discToHalfPlane z : ℍ) : ℂ) : Mobius.ExtendedComplex) = ((z : ℂ) : Mobius.ExtendedComplex) := by
    rw [cayleyMobius_apply, extendedCayley_halfPlane, halfPlaneToDisc_discToHalfPlane]
  change ((z : ℂ) : Mobius.ExtendedComplex) ∈ (cayleyMobius : Equiv.Perm
    Mobius.ExtendedComplex) '' L.extendedCircle.val ↔ _
  rw [← hp]
  constructor
  · rintro ⟨w, hw, he⟩
    have he' := (cayleyMobius : Equiv.Perm Mobius.ExtendedComplex).injective he
    rw [he'] at hw
    exact (L.mem_extendedCircle _).mp hw
  · intro hz
    exact ⟨_, (L.mem_extendedCircle _).mpr hz, rfl⟩

theorem HalfPlaneLine.discCarrier_eq_cayley_image (L : HalfPlaneLine) :
    L.discCarrier = halfPlaneToDisc '' L.carrier := by
  ext z
  rw [L.mem_discCarrier]
  constructor
  · intro hz
    exact ⟨discToHalfPlane z, hz, halfPlaneToDisc_discToHalfPlane z⟩
  · rintro ⟨w, hw, rfl⟩
    simpa only [discToHalfPlane_halfPlaneToDisc] using hw

/-- The actual Euclidean circle condition for perpendicularity to the unit circle. -/
theorem complexCircle_orthogonal_discBoundary_iff (c : ℂ) (r : ℝ) (hr : 0 < r) :
    Mobius.ComplexCirclesOrthogonal ⟨Mobius.complexCircle c r, Mobius.complexCircle_isGeneralized c r
      hr⟩ discBoundaryCircle ↔
      ‖c‖ ^ 2 = r ^ 2 + 1 := by
  rw [Mobius.complexCirclesOrthogonal_iff_inversiveProduct_zero, complexCircle_realModel c r hr,
    discBoundaryCircle_realModel, Inversive.inversiveProduct_sphere_sphere]
  simp only [sub_zero, Mobius.complexPlaneCoordinates.norm_map, one_pow, mul_one, abs_eq_zero,
    div_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, hr.ne', or_self, or_false]
  constructor <;> intro h <;> nlinarith

/-- The actual Euclidean line condition is that the line is a diameter. -/
theorem complexLine_orthogonal_discBoundary_iff (a : ℂ) (t : ℝ) (ha : a ≠ 0) :
    Mobius.ComplexCirclesOrthogonal ⟨Mobius.complexLine a t, Mobius.complexLine_isGeneralized a t
      ha⟩ discBoundaryCircle ↔ t = 0 := by
  rw [Mobius.complexCirclesOrthogonal_iff_inversiveProduct_zero, complexLine_realModel a t ha,
    discBoundaryCircle_realModel, Inversive.inversiveProduct_comm, Inversive.inversiveProduct_sphere_plane]
  simp [Mobius.complexPlaneCoordinates.norm_map, norm_ne_zero_iff.mpr ha, div_eq_zero_iff]

theorem complexCircle_orthogonal_halfPlaneBoundary_iff (c : ℂ) (r : ℝ) (hr : 0 < r) :
    Mobius.ComplexCirclesOrthogonal ⟨Mobius.complexCircle c r, Mobius.complexCircle_isGeneralized c r
      hr⟩ halfPlaneBoundaryCircle ↔
      c.im = 0 := by
  rw [Mobius.complexCirclesOrthogonal_iff_inversiveProduct_zero, complexCircle_realModel c r hr,
    halfPlaneBoundaryCircle_realModel, Inversive.inversiveProduct_sphere_plane]
  simp [Mobius.complexPlaneCoordinates.inner_map_map, Mobius.complexPlaneCoordinates.norm_map,
    hr.ne', div_eq_zero_iff]

theorem complexLine_orthogonal_halfPlaneBoundary_iff (a : ℂ) (t : ℝ) (ha : a ≠ 0) :
    Mobius.ComplexCirclesOrthogonal ⟨Mobius.complexLine a t, Mobius.complexLine_isGeneralized a t
      ha⟩ halfPlaneBoundaryCircle ↔
      a.im = 0 := by
  rw [Mobius.complexCirclesOrthogonal_iff_inversiveProduct_zero, complexLine_realModel a t ha,
    halfPlaneBoundaryCircle_realModel, Inversive.inversiveProduct_plane_plane]
  simp [Mobius.complexPlaneCoordinates.inner_map_map, Mobius.complexPlaneCoordinates.norm_map,
    norm_ne_zero_iff.mpr ha, div_eq_zero_iff]

theorem complexLine_real_normal (a : ℂ) (t : ℝ) (ha : a ≠ 0) (hai : a.im = 0) :
    Mobius.complexLine a t = Mobius.complexLine 1 (t / a.re) := by
  have har : a.re ≠ 0 := by
    intro hz
    apply ha
    exact Complex.ext hz hai
  ext z
  induction z using OnePoint.rec with
  | infty => simp
  | coe z =>
    simp only [Mobius.complexLine_coe, _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,
      Complex.one_re, Complex.one_im,
      hai, mul_zero, add_zero, mul_one]
    exact (eq_div_iff har).symm

/-- Every complete generalized circle perpendicular to the real axis is one of the genuine half-plane h-line circles. -/
theorem exists_halfPlaneLine_of_orthogonal_boundary (S : Mobius.ComplexGeneralizedCircle)
    (hS : Mobius.ComplexCirclesOrthogonal S halfPlaneBoundaryCircle) :
    ∃ L : HalfPlaneLine, L.extendedCircle = S := by
  rcases (Mobius.isComplexGeneralizedCircle_iff S.val).mp S.property with ⟨c, r, hr, he⟩ | ⟨a, t, ha, he⟩
  · have hs : S = ⟨Mobius.complexCircle c r, Mobius.complexCircle_isGeneralized c r hr⟩ := Subtype.ext he
    rw [hs] at hS
    have hc := (complexCircle_orthogonal_halfPlaneBoundary_iff c r hr).mp hS
    have hce : (c.re : ℂ) = c := Complex.ext (by simp) (by simpa using hc.symm)
    refine ⟨.circle c.re r hr, ?_⟩
    apply Subtype.ext
    change Mobius.complexCircle (c.re : ℂ) r = S.val
    rw [hce, he]
  · have hs : S = ⟨Mobius.complexLine a t, Mobius.complexLine_isGeneralized a t ha⟩ := Subtype.ext he
    rw [hs] at hS
    have hai := (complexLine_orthogonal_halfPlaneBoundary_iff a t ha).mp hS
    refine ⟨.vertical (t / a.re), ?_⟩
    apply Subtype.ext
    change Mobius.complexLine 1 (t / a.re) = S.val
    rw [he, complexLine_real_normal a t ha hai]

theorem complexCircle_image_inverse (f : Mobius.complexMobiusGroup) (S : Mobius.ComplexGeneralizedCircle) :
    (S.image f).image f⁻¹ = S := by
  apply Subtype.ext
  change (f⁻¹ : Mobius.complexMobiusGroup).val '' (f.val '' S.val) = S.val
  ext z
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, he⟩
    have he' : u = z := by simpa using he
    rwa [← he']
  · intro hz
    exact ⟨f.val z, ⟨z, hz, rfl⟩, by simp⟩

theorem complexCircle_inverse_image (f : Mobius.complexMobiusGroup) (S : Mobius.ComplexGeneralizedCircle) :
    (S.image f⁻¹).image f = S := by
  simpa only [inv_inv] using complexCircle_image_inverse f⁻¹ S

/-- The native circle classification is exhaustive: every circle orthogonal to the disc boundary is an actual Cayley h-line circle. -/
theorem exists_halfPlaneLine_of_discCircle (S : Mobius.ComplexGeneralizedCircle)
    (hS : Mobius.ComplexCirclesOrthogonal S discBoundaryCircle) :
    ∃ L : HalfPlaneLine, L.discCircle = S := by
  have hb : discBoundaryCircle.image cayleyMobius⁻¹ = halfPlaneBoundaryCircle := by
    rw [← cayley_image_boundary, complexCircle_image_inverse]
  have hT : Mobius.ComplexCirclesOrthogonal (S.image cayleyMobius⁻¹) halfPlaneBoundaryCircle := by
    have h := hS.image _ _ cayleyMobius⁻¹
    rwa [hb] at h
  obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_orthogonal_boundary (S.image cayleyMobius⁻¹) hT
  refine ⟨L, ?_⟩
  have he := congrArg (fun T : Mobius.ComplexGeneralizedCircle => T.image cayleyMobius) hL
  rw [complexCircle_inverse_image] at he
  exact he

/-- A native disc h-line is a genuine generalized circle geometrically perpendicular to the actual unit circle. -/
abbrev DiscLine := {S : Mobius.ComplexGeneralizedCircle // Mobius.ComplexCirclesOrthogonal S discBoundaryCircle}

/-- Its actual subset of the open complex unit disc. -/
def DiscLine.carrier (L : DiscLine) : Set 𝔻 := {z | ((z : ℂ) : Mobius.ExtendedComplex) ∈ L.val.val}

/-- Cayley transports an actual half-plane line into the native geometric disc-line type. -/
def HalfPlaneLine.toDiscLine (L : HalfPlaneLine) : DiscLine := ⟨L.discCircle, L.discCircle_orthogonal_boundary⟩

@[simp] theorem HalfPlaneLine.toDiscLine_carrier (L : HalfPlaneLine) : L.toDiscLine.carrier = L.discCarrier := rfl

theorem HalfPlaneLine.toDiscLine_surjective : Function.Surjective HalfPlaneLine.toDiscLine := by
  intro S
  obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_discCircle S.val S.property
  exact ⟨L, Subtype.ext hL⟩

/-- The source geometric definition of an h-line, applied to the actual disc model. -/
def IsDiscHLine (S : Set 𝔻) : Prop := ∃ L : DiscLine, S = L.carrier

/-- The same source definition written solely with Euclidean circle/diameter equations. -/
theorem isDiscHLine_iff_euclidean (S : Set 𝔻) :
    IsDiscHLine S ↔
      (∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ ‖c‖ ^ 2 = r ^ 2 + 1 ∧ S = {z : 𝔻 | ‖(z : ℂ) - c‖ = r}) ∨
      (∃ a : ℂ, a ≠ 0 ∧ S = {z : 𝔻 | inner ℝ (z : ℂ) a = 0}) := by
  constructor
  · rintro ⟨L, rfl⟩
    rcases (Mobius.isComplexGeneralizedCircle_iff L.val.val).mp L.val.property with ⟨c, r, hr, he⟩ | ⟨a, t, ha, he⟩
    · have hs : L.val = ⟨Mobius.complexCircle c r, Mobius.complexCircle_isGeneralized c r hr⟩ := Subtype.ext he
      have ho := L.property
      rw [hs] at ho
      refine Or.inl ⟨c, r, hr, (complexCircle_orthogonal_discBoundary_iff c r hr).mp ho, ?_⟩
      ext z
      change ((z : ℂ) : Mobius.ExtendedComplex) ∈ L.val.val ↔ _
      rw [he, Mobius.complexCircle_coe]
      rfl
    · have hs : L.val = ⟨Mobius.complexLine a t, Mobius.complexLine_isGeneralized a t ha⟩ := Subtype.ext he
      have ho := L.property
      rw [hs] at ho
      have ht := (complexLine_orthogonal_discBoundary_iff a t ha).mp ho
      refine Or.inr ⟨a, ha, ?_⟩
      ext z
      change ((z : ℂ) : Mobius.ExtendedComplex) ∈ L.val.val ↔ _
      rw [he, Mobius.complexLine_coe, ht]
      rfl
  · rintro (⟨c, r, hr, hnorm, rfl⟩ | ⟨a, ha, rfl⟩)
    · let L : DiscLine := ⟨⟨Mobius.complexCircle c r, Mobius.complexCircle_isGeneralized c r hr⟩,
        (complexCircle_orthogonal_discBoundary_iff c r hr).mpr hnorm⟩
      refine ⟨L, ?_⟩
      ext z
      exact (Mobius.complexCircle_coe c z r).symm
    · let L : DiscLine := ⟨⟨Mobius.complexLine a 0, Mobius.complexLine_isGeneralized a 0 ha⟩,
        (complexLine_orthogonal_discBoundary_iff a 0 ha).mpr rfl⟩
      refine ⟨L, ?_⟩
      ext z
      exact (Mobius.complexLine_coe a z 0).symm

/-- Native Euclidean disc lines are exactly Cayley images of the actual half-plane h-lines. -/
theorem isDiscHLine_iff_cayley_image (S : Set 𝔻) :
    IsDiscHLine S ↔ ∃ L : HalfPlaneLine, S = halfPlaneToDisc '' L.carrier := by
  constructor
  · rintro ⟨D, rfl⟩
    obtain ⟨L, rfl⟩ := HalfPlaneLine.toDiscLine_surjective D
    exact ⟨L, L.discCarrier_eq_cayley_image⟩
  · rintro ⟨L, rfl⟩
    exact ⟨L.toDiscLine, L.discCarrier_eq_cayley_image.symm⟩

theorem discToHalfPlane_injective : Function.Injective discToHalfPlane := by
  intro z w h
  have hc := congrArg halfPlaneToDisc h
  simpa only [halfPlaneToDisc_discToHalfPlane] using hc

theorem DiscLine.eq_of_two_points (L M : DiscLine) {z w : 𝔻} (hzw : z ≠ w)
    (hzL : z ∈ L.carrier) (hwL : w ∈ L.carrier) (hzM : z ∈ M.carrier) (hwM : w ∈ M.carrier) : L = M := by
  obtain ⟨A, rfl⟩ := HalfPlaneLine.toDiscLine_surjective L
  obtain ⟨B, rfl⟩ := HalfPlaneLine.toDiscLine_surjective M
  have hzw' : discToHalfPlane z ≠ discToHalfPlane w := discToHalfPlane_injective.ne hzw
  have he : A = B := A.eq_of_two_points B hzw'
    ((A.mem_discCarrier z).mp hzL) ((A.mem_discCarrier w).mp hwL)
    ((B.mem_discCarrier z).mp hzM) ((B.mem_discCarrier w).mp hwM)
  rw [he]

/-- now for the native Euclidean disc carriers. -/
theorem existsUnique_discLine_through (z w : 𝔻) (hzw : z ≠ w) :
    ∃! L : DiscLine, z ∈ L.carrier ∧ w ∈ L.carrier := by
  obtain ⟨L, hL, _⟩ := existsUnique_halfPlaneLine_through (discToHalfPlane z) (discToHalfPlane w)
    (discToHalfPlane_injective.ne hzw)
  refine ⟨L.toDiscLine, ⟨(L.mem_discCarrier z).mpr hL.1, (L.mem_discCarrier w).mpr hL.2⟩, ?_⟩
  intro M hM
  exact M.eq_of_two_points _ hzw hM.1 hM.2 ((L.mem_discCarrier z).mpr hL.1) ((L.mem_discCarrier w).mpr hL.2)

/-- For native circle arcs and diameters. -/
theorem DiscLine.inter_subsingleton {L M : DiscLine} (hLM : L ≠ M) : (L.carrier ∩ M.carrier).Subsingleton := by
  intro z hz w hw
  by_contra hzw
  exact hLM (L.eq_of_two_points M hzw hz.1 hw.1 hz.2 hw.2)

/-- The actual real Euclidean reflection in the complete h-line circle. -/
def HalfPlaneLine.realReflection : HalfPlaneLine → Inversive.ExtendedHomeomorph 2
  | .vertical x => Inversive.planeReflectionHomeomorph (Mobius.complexPlaneCoordinates 1) x
      ((Mobius.complexPlaneCoordinates.map_ne_zero_iff).mpr one_ne_zero)
  | .circle c r hr => Inversive.sphereInversionHomeomorph (Mobius.complexPlaneCoordinates (c : ℂ)) r hr.ne'

theorem HalfPlaneLine.realReflection_isReflection (L : HalfPlaneLine) : Inversive.IsReflection L.realReflection := by
  cases L with
  | vertical x => exact Inversive.planeReflection_isReflection _ _ _
  | circle c r hr => exact Inversive.sphereInversion_isReflection _ _ hr

theorem HalfPlaneLine.realReflection_fixedPoints (L : HalfPlaneLine) :
    Function.fixedPoints (Mobius.euclideanToComplexHom L.realReflection) = L.extendedCircle.val := by
  cases L with
  | vertical x => exact Mobius.complexLine_reflection 1 x one_ne_zero
  | circle c r hr => exact Mobius.complexCircle_reflection c r hr

/-- The existing hyperbolic reflection is exactly the restriction of the genuine Euclidean reflection. -/
theorem HalfPlaneLine.realReflection_coe (L : HalfPlaneLine) (z : ℍ) :
    Mobius.euclideanToComplexHom L.realReflection ((z : ℂ) : Mobius.ExtendedComplex) =
      ((L.reflection z : ℂ) : Mobius.ExtendedComplex) := by
  cases L with
  | vertical x =>
    simp only [HalfPlaneLine.realReflection, Mobius.euclideanToComplexHom_apply,
      Mobius.extendedComplexEuclideanHomeomorph_coe, Inversive.planeReflectionHomeomorph_apply,
      Inversive.planeReflection_coe, Mobius.complexEuclidean_symm_coe, HalfPlaneLine.reflection]
    rw [Mobius.ReflectionBridge.planeReflection_complex_formula 1 z x one_ne_zero, verticalReflection_coe]
    simp
    ring
  | circle c r hr =>
    have hz : (z : ℂ) ≠ (c : ℂ) := by
      intro h
      have hi := congrArg Complex.im h
      simp only [UpperHalfPlane.coe_im, Complex.ofReal_im] at hi
      exact z.im_pos.ne' hi
    have he : Mobius.complexPlaneCoordinates (z : ℂ) ≠ Mobius.complexPlaneCoordinates (c : ℂ) :=
      Mobius.complexPlaneCoordinates.injective.ne hz
    simp only [HalfPlaneLine.realReflection, Mobius.euclideanToComplexHom_apply,
      Mobius.extendedComplexEuclideanHomeomorph_coe, Inversive.sphereInversionHomeomorph_apply]
    rw [Inversive.sphereInversion_coe _ _ he, Mobius.complexEuclidean_symm_coe,
      Mobius.ReflectionBridge.inversion_complex_formula c z r hz]
    change ((c : ℂ) + (r : ℂ)^2 / conj ((z : ℂ) - (c : ℂ)) : Mobius.ExtendedComplex) = _
    rw [map_sub, Complex.conj_ofReal, HalfPlaneLine.reflection, circleReflection_coe]

/-- Choose the unique half-plane presentation of a native geometric disc line. -/
def DiscLine.toHalfPlane (L : DiscLine) : HalfPlaneLine :=
  Classical.choose (HalfPlaneLine.toDiscLine_surjective L)

theorem DiscLine.toHalfPlane_spec (L : DiscLine) : L.toHalfPlane.toDiscLine = L :=
  Classical.choose_spec (HalfPlaneLine.toDiscLine_surjective L)

theorem DiscLine.mem_carrier (L : DiscLine) (z : 𝔻) :
    z ∈ L.carrier ↔ discToHalfPlane z ∈ L.toHalfPlane.carrier := by
  have h := L.toHalfPlane.mem_discCarrier z
  change z ∈ L.toHalfPlane.toDiscLine.carrier ↔ _ at h
  rwa [L.toHalfPlane_spec] at h

/-- Reflection in the native geometric disc line, on actual points of the disc. -/
def DiscLine.reflection (L : DiscLine) (z : 𝔻) : 𝔻 :=
  halfPlaneToDisc (L.toHalfPlane.reflection (discToHalfPlane z))

/-- The full-plane reflection inducing the disc reflection is a genuine Euclidean circle/line reflection. -/
theorem DiscLine.exists_geometric_reflection (L : DiscLine) :
    ∃ r : Inversive.ExtendedHomeomorph 2, Inversive.IsReflection r ∧
      Function.fixedPoints (Mobius.euclideanToComplexHom r) = L.val.val ∧
      ∀ z : 𝔻, Mobius.euclideanToComplexHom r ((z : ℂ) : Mobius.ExtendedComplex) =
        ((L.reflection z : ℂ) : Mobius.ExtendedComplex) := by
  obtain ⟨g, hg, _, he⟩ := (Mobius.mem_complexMobiusGroup_iff_real cayleyMobius).mp cayleyMobius.property
  let r := g * L.toHalfPlane.realReflection * g⁻¹
  have hr : Inversive.IsReflection r :=
    Inversive.generalMobius_conjugate_isReflection hg L.toHalfPlane.realReflection_isReflection
  have hhom : Mobius.euclideanToComplexHom r = cayleyMobius.val *
      Mobius.euclideanToComplexHom L.toHalfPlane.realReflection * cayleyMobius.val⁻¹ := by
    simp only [r, map_mul, map_inv, he]
  have hfix : Function.fixedPoints (Mobius.euclideanToComplexHom r) = L.val.val := by
    have hs : L.toHalfPlane.discCircle = L.val := congrArg Subtype.val L.toHalfPlane_spec
    rw [hhom]
    change Function.fixedPoints (cayleyMobius.val * Mobius.euclideanToComplexHom L.toHalfPlane.realReflection *
      cayleyMobius.val⁻¹) = _
    have hx : Function.fixedPoints (cayleyMobius.val * Mobius.euclideanToComplexHom L.toHalfPlane.realReflection *
      cayleyMobius.val⁻¹) =
        cayleyMobius.val '' Function.fixedPoints (Mobius.euclideanToComplexHom L.toHalfPlane.realReflection) := by
      ext z
      constructor
      · intro hz
        refine ⟨cayleyMobius.val⁻¹ z, ?_, by simp⟩
        have h := congrArg (fun w => cayleyMobius.val⁻¹ w) hz
        change cayleyMobius.val.symm (cayleyMobius.val
          (Mobius.euclideanToComplexHom L.toHalfPlane.realReflection (cayleyMobius.val.symm
            z))) = cayleyMobius.val.symm z at h
        rw [cayleyMobius.val.symm_apply_apply] at h
        exact h
      · rintro ⟨w, hw, rfl⟩
        change cayleyMobius.val (Mobius.euclideanToComplexHom L.toHalfPlane.realReflection (cayleyMobius.val⁻¹
          (cayleyMobius.val w))) = cayleyMobius.val w
        change cayleyMobius.val (Mobius.euclideanToComplexHom L.toHalfPlane.realReflection
          (cayleyMobius.val.symm (cayleyMobius.val w))) = cayleyMobius.val w
        rw [cayleyMobius.val.symm_apply_apply]
        exact congrArg cayleyMobius.val hw
    rw [hx, L.toHalfPlane.realReflection_fixedPoints]
    exact congrArg Subtype.val hs
  refine ⟨r, hr, hfix, ?_⟩
  intro z
  rw [hhom]
  have hp : cayleyMobius.val⁻¹ ((z : ℂ) : Mobius.ExtendedComplex) =
      ((discToHalfPlane z : ℂ) : Mobius.ExtendedComplex) := by
    change cayleyMobius.val.symm ((z : ℂ) : Mobius.ExtendedComplex) = _
    apply cayleyMobius.val.symm_apply_eq.mpr
    rw [cayleyMobius_apply, extendedCayley_halfPlane, halfPlaneToDisc_discToHalfPlane]
  change cayleyMobius.val (Mobius.euclideanToComplexHom L.toHalfPlane.realReflection
    (cayleyMobius.val⁻¹ ((z : ℂ) : Mobius.ExtendedComplex))) = _
  rw [hp, L.toHalfPlane.realReflection_coe, cayleyMobius_apply, extendedCayley_halfPlane]
  rfl

/-- reflection in the actual native Euclidean disc circle is a hyperbolic isometry. -/
theorem DiscLine.reflection_isometry (L : DiscLine) :
    letI := discHyperbolicMetric
    Isometry L.reflection := by
  let := discHyperbolicMetric
  have hc : Isometry halfPlaneToDisc := cayley_isometry
  have hi : Isometry discToHalfPlane := by
    apply Isometry.of_dist_eq
    intro z w
    have h := hc.dist_eq (discToHalfPlane z) (discToHalfPlane w)
    simpa only [halfPlaneToDisc_discToHalfPlane] using h.symm
  exact hc.comp (L.toHalfPlane.reflection_isometry.comp hi)

/-- For complete h-line circles, ambient geometric normal orthogonality agrees with actual half-plane tangent orthogonality. -/
theorem HalfPlaneLine.extendedCircle_orthogonal_iff (L M : HalfPlaneLine) :
    Mobius.ComplexCirclesOrthogonal L.extendedCircle M.extendedCircle ↔ L.Orthogonal M := by
  rw [L.orthogonal_iff_coefficients, Mobius.complexCirclesOrthogonal_iff_inversiveProduct_zero]
  cases L with
  | vertical x =>
    cases M with
    | vertical y =>
      rw [HalfPlaneLine.extendedCircle, HalfPlaneLine.extendedCircle,
        complexLine_realModel 1 x one_ne_zero, complexLine_realModel 1 y one_ne_zero,
        Inversive.inversiveProduct_plane_plane]
      simp [HalfPlaneLine.OrthogonalCoefficients, Mobius.complexPlaneCoordinates.norm_map]
    | circle c r hr =>
      rw [HalfPlaneLine.extendedCircle, HalfPlaneLine.extendedCircle,
        complexLine_realModel 1 x one_ne_zero, complexCircle_realModel c r hr,
        Inversive.inversiveProduct_comm, Inversive.inversiveProduct_sphere_plane]
      simp [HalfPlaneLine.OrthogonalCoefficients, Mobius.complexPlaneCoordinates.inner_map_map,
        Mobius.complexPlaneCoordinates.norm_map, Complex.inner, hr.ne', div_eq_zero_iff, sub_eq_zero, eq_comm]
  | circle c r hr =>
    cases M with
    | vertical x =>
      rw [HalfPlaneLine.extendedCircle, HalfPlaneLine.extendedCircle,
        complexCircle_realModel c r hr, complexLine_realModel 1 x one_ne_zero,
        Inversive.inversiveProduct_sphere_plane]
      simp [HalfPlaneLine.OrthogonalCoefficients, Mobius.complexPlaneCoordinates.inner_map_map,
        Mobius.complexPlaneCoordinates.norm_map, Complex.inner, hr.ne', div_eq_zero_iff, sub_eq_zero]
    | circle d t ht =>
      rw [HalfPlaneLine.extendedCircle, HalfPlaneLine.extendedCircle,
        complexCircle_realModel c r hr, complexCircle_realModel d t ht,
        Inversive.inversiveProduct_sphere_sphere]
      simp only [← map_sub, Mobius.complexPlaneCoordinates.norm_map, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, abs_eq_zero]
      have hden : 2 * r * t ≠ 0 := by positivity
      rw [div_eq_zero_iff]
      simp only [hden, or_false, HalfPlaneLine.OrthogonalCoefficients]
      constructor <;> intro h <;> linarith

/-- Cayley preserves the geometric orthogonality of the actual complete line circles. -/
theorem HalfPlaneLine.discCircle_orthogonal_iff (L M : HalfPlaneLine) :
    Mobius.ComplexCirclesOrthogonal L.discCircle M.discCircle ↔ L.Orthogonal M := by
  constructor
  · intro h
    have hi := h.image _ _ cayleyMobius⁻¹
    change Mobius.ComplexCirclesOrthogonal ((L.extendedCircle.image cayleyMobius).image cayleyMobius⁻¹)
      ((M.extendedCircle.image cayleyMobius).image cayleyMobius⁻¹) at hi
    rw [complexCircle_image_inverse, complexCircle_image_inverse] at hi
    exact (L.extendedCircle_orthogonal_iff M).mp hi
  · intro h
    exact ((L.extendedCircle_orthogonal_iff M).mpr h).image _ _ cayleyMobius

/-- Native circle normal orthogonality; its actual interior intersection is established below. -/
def DiscLine.Orthogonal (L M : DiscLine) : Prop := Mobius.ComplexCirclesOrthogonal L.val M.val

theorem DiscLine.orthogonal_iff_halfPlane (L M : DiscLine) :
    L.Orthogonal M ↔ L.toHalfPlane.Orthogonal M.toHalfPlane := by
  have hL : L.toHalfPlane.discCircle = L.val := congrArg Subtype.val L.toHalfPlane_spec
  have hM : M.toHalfPlane.discCircle = M.val := congrArg Subtype.val M.toHalfPlane_spec
  change Mobius.ComplexCirclesOrthogonal L.val M.val ↔ _
  rw [← hL, ← hM]
  exact L.toHalfPlane.discCircle_orthogonal_iff M.toHalfPlane

/-- Native orthogonal circles have an actual common point in the open disc. -/
theorem DiscLine.Orthogonal.exists_intersection {L M : DiscLine} (h : L.Orthogonal M) :
    ∃ z : 𝔻, z ∈ L.carrier ∧ z ∈ M.carrier := by
  obtain ⟨w, hwL, hwM, _⟩ := (L.orthogonal_iff_halfPlane M).mp h
  refine ⟨halfPlaneToDisc w, ?_, ?_⟩
  · rw [L.mem_carrier, discToHalfPlane_halfPlaneToDisc]
    exact hwL
  · rw [M.mem_carrier, discToHalfPlane_halfPlaneToDisc]
    exact hwM

/-- exactly one native Euclidean disc h-line through an arbitrary point is perpendicular to a given line. -/
theorem DiscLine.existsUnique_perpendicular (L : DiscLine) (w : 𝔻) :
    ∃! M : DiscLine, w ∈ M.carrier ∧ L.Orthogonal M := by
  obtain ⟨A, hA, huniq⟩ := L.toHalfPlane.existsUnique_perpendicular (discToHalfPlane w)
  refine ⟨A.toDiscLine, ⟨(A.mem_discCarrier w).mpr hA.1, ?_⟩, ?_⟩
  · have hL : L.toHalfPlane.discCircle = L.val := congrArg Subtype.val L.toHalfPlane_spec
    change Mobius.ComplexCirclesOrthogonal L.val A.discCircle
    rw [← hL]
    exact (L.toHalfPlane.discCircle_orthogonal_iff A).mpr hA.2
  · intro M hM
    have he : M.toHalfPlane = A := huniq M.toHalfPlane
      ⟨(M.mem_carrier w).mp hM.1, (L.orthogonal_iff_halfPlane M).mp hM.2⟩
    rw [← M.toHalfPlane_spec, he]

/-- The actual nonzero Euclidean normal at a native disc h-line point. -/
def DiscLine.normalAt (L : DiscLine) (z : 𝔻) : Inversive.Euclidean 2 :=
  Inversive.sphereCoefficientNormal (Inversive.generalizedSphereCoefficients
    L.val.realModel) (Mobius.complexPlaneCoordinates (z : ℂ))

/-- Orthogonality of actual Euclidean normals at an actual common disc point. -/
def DiscLine.OrthogonalAt (L M : DiscLine) (z : 𝔻) : Prop :=
  z ∈ L.carrier ∧ z ∈ M.carrier ∧ inner ℝ (L.normalAt z) (M.normalAt z) = 0

/-- The global native-circle criterion equals perpendicularity at the actual common interior point. -/
theorem DiscLine.orthogonalAt_iff (L M : DiscLine) (z : 𝔻) (hzL : z ∈ L.carrier) (hzM : z ∈ M.carrier) :
    L.OrthogonalAt M z ↔ L.Orthogonal M := by
  have hmem (U : DiscLine) (hzU : z ∈ U.carrier) :
      ((Mobius.complexPlaneCoordinates (z : ℂ)) : Inversive.ExtendedEuclidean 2) ∈ U.val.realModel.val := by
    exact ⟨((z : ℂ) : Mobius.ExtendedComplex), hzU, rfl⟩
  have hn (U : DiscLine) : Inversive.generalizedSphereCoefficients U.val.realModel ≠ 0 := by
    intro he
    have hpos := Inversive.generalizedSphereCoefficients_pos U.val.realModel
    rw [he, Inversive.sphereDiscriminant_zero] at hpos
    exact lt_irrefl _ hpos
  have h := Inversive.inversiveProduct_eq_zero_iff_normals_orthogonal L.val.realModel M.val.realModel
    (Inversive.generalizedSphereCoefficients L.val.realModel) (Inversive.generalizedSphereCoefficients M.val.realModel)
    (hn L) (hn M) (Inversive.generalizedSphereCoefficients_carrier _) (Inversive.generalizedSphereCoefficients_carrier
      _)
    (Mobius.complexPlaneCoordinates (z : ℂ)) (hmem L hzL) (hmem M hzM)
  change (z ∈ L.carrier ∧ z ∈ M.carrier ∧ _) ↔ _
  simp only [hzL, hzM, true_and]
  rw [DiscLine.Orthogonal, Mobius.complexCirclesOrthogonal_iff_inversiveProduct_zero]
  exact h.symm

/-- Native disc-circle orthogonality really occurs in the open disc. -/
theorem DiscLine.orthogonal_iff_exists_orthogonalAt (L M : DiscLine) :
    L.Orthogonal M ↔ ∃ z : 𝔻, L.OrthogonalAt M z := by
  constructor
  · intro h
    obtain ⟨z, hzL, hzM⟩ := h.exists_intersection
    exact ⟨z, (L.orthogonalAt_iff M z hzL hzM).mpr h⟩
  · rintro ⟨z, hzL, hzM, hi⟩
    exact (L.orthogonalAt_iff M z hzL hzM).mp ⟨hzL, hzM, hi⟩

/-- A real Möbius transformation, conjugated by the actual Cayley model map. -/
def discRealGL (g : GL (Fin 2) ℝ) (z : 𝔻) : 𝔻 := halfPlaneToDisc (g • discToHalfPlane z)

theorem discRealGL_isometry (g : GL (Fin 2) ℝ) :
    letI := discHyperbolicMetric
    Isometry (discRealGL g) := by
  let := discHyperbolicMetric
  have hc : Isometry halfPlaneToDisc := cayley_isometry
  have hi : Isometry discToHalfPlane := by
    apply Isometry.of_dist_eq
    intro z w
    have h := hc.dist_eq (discToHalfPlane z) (discToHalfPlane w)
    simpa only [halfPlaneToDisc_discToHalfPlane] using h.symm
  exact hc.comp ((realGL_isometry g).comp hi)

/-- actual native disc h-lines are related by a hyperbolic isometry. -/
theorem DiscLine.exists_isometry_map (L M : DiscLine) :
    ∃ g : GL (Fin 2) ℝ, 0 < g.val.det ∧
      discRealGL g '' L.carrier = M.carrier := by
  obtain ⟨g, hg, himage⟩ := L.toHalfPlane.exists_mobius_map M.toHalfPlane
  refine ⟨g, hg, ?_⟩
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [M.mem_carrier]
    change discToHalfPlane (halfPlaneToDisc (g • discToHalfPlane w)) ∈ M.toHalfPlane.carrier
    rw [discToHalfPlane_halfPlaneToDisc, ← himage]
    exact ⟨discToHalfPlane w, (L.mem_carrier w).mp hw, rfl⟩
  · intro hz
    have hh := (M.mem_carrier z).mp hz
    rw [← himage] at hh
    obtain ⟨w, hw, he⟩ := hh
    refine ⟨halfPlaneToDisc w, ?_, ?_⟩
    · rw [L.mem_carrier, discToHalfPlane_halfPlaneToDisc]
      exact hw
    · change halfPlaneToDisc (g • discToHalfPlane (halfPlaneToDisc w)) = z
      change g • w = discToHalfPlane z at he
      rw [discToHalfPlane_halfPlaneToDisc, he, halfPlaneToDisc_discToHalfPlane]

/-- The native normal cannot vanish at a point of the actual disc line. -/
theorem DiscLine.normalAt_ne_zero (L : DiscLine) (z : 𝔻) (hz : z ∈ L.carrier) : L.normalAt z ≠ 0 := by
  have hmem : ((Mobius.complexPlaneCoordinates (z : ℂ)) : Inversive.ExtendedEuclidean 2) ∈
      Inversive.sphereCoefficientCarrier (Inversive.generalizedSphereCoefficients L.val.realModel) := by
    rw [Inversive.generalizedSphereCoefficients_carrier]
    exact ⟨((z : ℂ) : Mobius.ExtendedComplex), hz, rfl⟩
  have hs := Inversive.sphereCoefficientNormal_norm_sq (Inversive.generalizedSphereCoefficients L.val.realModel)
    (Mobius.complexPlaneCoordinates (z : ℂ)) hmem
  have hp := Inversive.generalizedSphereCoefficients_pos L.val.realModel
  change ‖L.normalAt z‖ ^ 2 = _ at hs
  intro he
  rw [he, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hs
  linarith

/-- The Cayley-conjugated real Möbius map is onto the actual unit disc as well as distance-preserving. -/
theorem discRealGL_bijective (g : GL (Fin 2) ℝ) : Function.Bijective (discRealGL g) := by
  constructor
  · intro z w he
    have h := congrArg (discRealGL g⁻¹) he
    simpa only [discRealGL, discToHalfPlane_halfPlaneToDisc, inv_smul_smul,
      halfPlaneToDisc_discToHalfPlane] using h
  · intro z
    refine ⟨discRealGL g⁻¹ z, ?_⟩
    simp only [discRealGL, discToHalfPlane_halfPlaneToDisc, smul_inv_smul,
      halfPlaneToDisc_discToHalfPlane]

/-- The native geometric reflection is involutive on actual disc points. -/
theorem DiscLine.reflection_involutive (L : DiscLine) : Function.Involutive L.reflection := by
  obtain ⟨r, hr, _, hpoint⟩ := L.exists_geometric_reflection
  have hrr : r * r = 1 := by
    calc
      r * r = r⁻¹ * r := by rw [hr.inv_eq]
      _ = 1 := inv_mul_cancel r
  have hh : Mobius.euclideanToComplexHom r * Mobius.euclideanToComplexHom r = 1 := by
    rw [← map_mul, hrr, map_one]
  intro z
  have h := congrArg (fun f : Equiv.Perm Mobius.ExtendedComplex => f ((z : ℂ) : Mobius.ExtendedComplex)) hh
  change Mobius.euclideanToComplexHom r (Mobius.euclideanToComplexHom r ((z : ℂ) : Mobius.ExtendedComplex)) = ((z : ℂ) :
    Mobius.ExtendedComplex) at h
  rw [hpoint z, hpoint (L.reflection z)] at h
  apply Subtype.ext
  exact OnePoint.coe_eq_coe.mp h

/-- A native h-line reflection is onto the actual disc. -/
theorem DiscLine.reflection_bijective (L : DiscLine) : Function.Bijective L.reflection :=
  L.reflection_involutive.bijective

end LowDimensionalTopology.Geometry.Hyperbolic
