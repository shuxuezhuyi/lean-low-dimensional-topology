module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleBoundary
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Tactic.Linarith

/-!
# Radial strong deformation of a punctured canonical handle quotient

The homotopy is constructed on the actual closed disk and descended through the
actual side pairing. Its continuity on the punctured quotient follows from the
closed quotient projection restricted over the punctured target and the
quotient-product theorem for the compact unit interval.
-/

@[expose] public section

noncomputable section

open Set Metric Topology unitInterval
open scoped ContinuousMap

namespace LowDimensionalTopology.Geometry.Surfaces.HandlePunctured

open HandlePresentation

abbrev PrePunctured (g : ℕ) := ↥((projection g) ⁻¹' punctured g)

/-- The coordinate form of the shared exact center-fiber statement. -/
theorem projection_eq_center_val_iff (g : ℕ) (z : Disc) :
    projection g z = center g ↔ z.val = 0 := by
  rw [HandlePresentation.projection_eq_center_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The interpolation scale is nonnegative even at the totalized origin. -/
def radialScale (t : I) (z : Disc) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) / ‖z.val‖

theorem radialScale_nonneg (t : I) (z : Disc) : 0 ≤ radialScale t z :=
  add_nonneg (sub_nonneg.mpr t.property.2) (div_nonneg t.property.1 (norm_nonneg _))

/-- The actual radial interpolation remains in the closed disk. -/
def radialDisc (t : I) (z : Disc) : Disc :=
  ⟨radialScale t z • z.val, mem_closedBall_zero_iff.mpr (by
    rw [norm_smul, Real.norm_of_nonneg (radialScale_nonneg t z)]
    have hz : ‖z.val‖ ≤ 1 := mem_closedBall_zero_iff.mp z.property
    by_cases hzero : ‖z.val‖ = 0
    · simp [hzero]
    · have hc : (t : ℝ) / ‖z.val‖ * ‖z.val‖ = (t : ℝ) := div_mul_cancel₀ _ hzero
      have hn := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hz)
      dsimp only [radialScale]
      nlinarith)⟩

theorem radialDisc_norm (t : I) (z : Disc) (hz : z.val ≠ 0) :
    ‖(radialDisc t z).val‖ = (1 - (t : ℝ)) * ‖z.val‖ + (t : ℝ) := by
  change ‖radialScale t z • z.val‖ = _
  rw [norm_smul, Real.norm_of_nonneg (radialScale_nonneg t z)]
  dsimp only [radialScale]
  rw [add_mul, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]

theorem radialDisc_ne_zero (t : I) (z : Disc) (hz : z.val ≠ 0) :
    (radialDisc t z).val ≠ 0 := by
  apply norm_pos_iff.mp
  rw [radialDisc_norm t z hz]
  have hr : 0 < ‖z.val‖ := norm_pos_iff.mpr hz
  have hle : ‖z.val‖ ≤ 1 := mem_closedBall_zero_iff.mp z.property
  have hn := mul_nonneg t.property.1 (sub_nonneg.mpr hle)
  nlinarith

@[simp]
theorem radialDisc_zero (z : Disc) : radialDisc 0 z = z := by
  apply Subtype.ext
  simp [radialDisc, radialScale]

theorem radialDisc_fixed (t : I) (z : Disc) (hz : ‖z.val‖ = 1) :
    radialDisc t z = z := by
  apply Subtype.ext
  change radialScale t z • z.val = z.val
  simp [radialScale, hz]

theorem radialDisc_one_norm (z : Disc) (hz : z.val ≠ 0) :
    ‖(radialDisc 1 z).val‖ = 1 := by
  rw [radialDisc_norm 1 z hz]
  simp

/-- Joint continuity holds away from the actual disk center. -/
theorem radialDisc_continuous {T : Type*} [TopologicalSpace T]
    {t : T → I} {z : T → Disc} (ht : Continuous t) (hz : Continuous z)
    (hzero : ∀ x, (z x).val ≠ 0) : Continuous fun x => radialDisc (t x) (z x) := by
  apply Continuous.subtype_mk
  have htc : Continuous fun x => (t x : ℝ) := continuous_subtype_val.comp ht
  have hzc : Continuous fun x => (z x).val := continuous_subtype_val.comp hz
  exact ((continuous_const.sub htc).add
    (htc.div hzc.norm (fun x => norm_ne_zero_iff.mpr (hzero x)))).smul hzc

/-- The actual side pairing only identifies boundary points, which the interpolation fixes. -/
def radial (g : ℕ) (t : I) : PolygonQuotient g → PolygonQuotient g :=
  Quot.lift (fun z => projection g (radialDisc t z)) (by
    intro z w hzw
    have hn : ‖z.val‖ = 1 ∧ ‖w.val‖ = 1 := by
      cases hzw <;> exact ⟨handleBoundaryPoint_norm _, handleBoundaryPoint_norm _⟩
    rw [radialDisc_fixed t z hn.1, radialDisc_fixed t w hn.2]
    exact Quot.sound hzw)

@[simp]
theorem radial_projection (g : ℕ) (t : I) (z : Disc) :
    radial g t (projection g z) = projection g (radialDisc t z) := rfl

@[simp]
theorem radial_zero (g : ℕ) (x : PolygonQuotient g) : radial g 0 x = x := by
  refine Quot.inductionOn x ?_
  intro z
  change radial g 0 (projection g z) = projection g z
  rw [radial_projection, radialDisc_zero]

theorem radial_boundary (g : ℕ) (t : I) (x : Boundary g) : radial g t x.val = x.val := by
  obtain ⟨z, hz, he⟩ := x.property
  rw [← he, radial_projection, radialDisc_fixed t z hz]

theorem radial_ne_center (g : ℕ) (t : I) :
    ∀ x : PolygonQuotient g, x ≠ center g → radial g t x ≠ center g := by
  intro x
  refine Quot.inductionOn x ?_
  intro z hz
  change projection g z ≠ center g at hz
  change radial g t (projection g z) ≠ center g
  rw [radial_projection]
  exact (projection_eq_center_val_iff g _).not.mpr
    (radialDisc_ne_zero t z ((projection_eq_center_val_iff g z).not.mp hz))

/-- Restrict the actual quotient projection over the punctured target. -/
def projectionPunctured (g : ℕ) : PrePunctured g → Punctured g :=
  (punctured g).restrictPreimage (projection g)

theorem projectionPunctured_surjective (g : ℕ) :
    Function.Surjective (projectionPunctured g) := by
  intro x
  refine ⟨⟨x.val.out, ?_⟩, ?_⟩
  · change Quot.mk (CanonicalHandleIdent g) x.val.out ≠ center g
    rw [Quot.out_eq]
    exact x.property
  · exact Subtype.ext (Quot.out_eq x.val)

theorem projectionPunctured_isQuotientMap (g : ℕ) :
    Topology.IsQuotientMap (projectionPunctured g) := by
  have hc : Continuous (projection g) := continuous_quot_mk
  exact ((HandleCW.quotient_projection_closedMap g).restrictPreimage (punctured g)).isQuotientMap
    hc.restrictPreimage (projectionPunctured_surjective g)

/-- The descended radial homotopy on the actual punctured quotient. -/
def radialPunctured (g : ℕ) (p : I × Punctured g) : Punctured g :=
  ⟨radial g p.1 p.2.val, radial_ne_center g p.1 p.2.val p.2.property⟩

theorem radialPunctured_continuous (g : ℕ) : Continuous (radialPunctured g) := by
  apply (projectionPunctured_isQuotientMap g).continuous_lift_prod_right
  apply Continuous.subtype_mk
  change Continuous fun p : I × PrePunctured g => projection g (radialDisc p.1 p.2.val)
  apply (show Continuous (projection g) from continuous_quot_mk).comp
  apply radialDisc_continuous continuous_fst (continuous_subtype_val.comp continuous_snd)
  intro p
  exact (projection_eq_center_val_iff g p.2.val).not.mp p.2.property

theorem radial_one_mem_boundary (g : ℕ) (x : Punctured g) :
    radial g 1 x.val ∈ boundary g := by
  have hout : projection g x.val.out = x.val := Quot.out_eq x.val
  have hzero : x.val.out.val ≠ 0 := by
    apply (projection_eq_center_val_iff g x.val.out).not.mp
    rw [hout]
    exact x.property
  refine ⟨radialDisc 1 x.val.out, radialDisc_one_norm _ hzero, ?_⟩
  exact (radial_projection g 1 x.val.out).symm.trans (congrArg (radial g 1) hout)

/-- The actual radial retraction to the quotient boundary. -/
def retraction (g : ℕ) (x : Punctured g) : Boundary g :=
  ⟨radial g 1 x.val, radial_one_mem_boundary g x⟩

theorem retraction_continuous (g : ℕ) : Continuous (retraction g) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp
    ((radialPunctured_continuous g).comp (continuous_const.prodMk continuous_id))

def retractionMap (g : ℕ) : C(Punctured g, Boundary g) :=
  ⟨retraction g, retraction_continuous g⟩

/-- The actual identity-to-retraction homotopy. -/
def deformation (g : ℕ) : ContinuousMap.Homotopy (ContinuousMap.id (Punctured g))
    ((boundaryInclusion g).comp (retractionMap g)) where
  toFun := radialPunctured g
  continuous_toFun := radialPunctured_continuous g
  map_zero_left x := Subtype.ext (radial_zero g x.val)
  map_one_left _ := rfl

/-- Every boundary point remains fixed throughout the actual homotopy. -/
theorem deformation_fixed_boundary (g : ℕ) (t : I) (x : Boundary g) :
    deformation g (t, boundaryInclusion g x) = boundaryInclusion g x :=
  Subtype.ext (radial_boundary g t x)

@[simp]
theorem retraction_inclusion (g : ℕ) (x : Boundary g) :
    retraction g (boundaryInclusion g x) = x :=
  Subtype.ext (radial_boundary g 1 x)

/-- The punctured canonical quotient is genuinely homotopy equivalent to its boundary. -/
def homotopyEquivBoundary (g : ℕ) : Punctured g ≃ₕ Boundary g where
  toFun := retractionMap g
  invFun := boundaryInclusion g
  left_inv := ⟨(deformation g).symm⟩
  right_inv := by
    have he : (retractionMap g).comp (boundaryInclusion g) = ContinuousMap.id (Boundary g) :=
      ContinuousMap.ext (fun x => retraction_inclusion g x)
    rw [he]

/-- The actual positive real radial point in the closed disk. -/
def positiveRealDisc (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) : Disc :=
  ⟨(ρ : ℂ), mem_closedBall_zero_iff.mpr (by
    rw [Complex.norm_real, Real.norm_of_nonneg hρ₀]
    exact hρ₁)⟩

def positiveRealPoint (g : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) : Punctured g :=
  ⟨projection g (positiveRealDisc ρ hρ.le hρ₁),
    (projection_eq_center_val_iff g _).not.mpr (Complex.ofReal_ne_zero.mpr hρ.ne')⟩

/-- The based radial retraction sends every positive real radial point to the same boundary vertex. -/
theorem retraction_positiveRealPoint (g : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    retraction g (positiveRealPoint g ρ hρ hρ₁) = boundaryBase g := by
  apply Subtype.ext
  change radial g 1 (projection g (positiveRealDisc ρ hρ.le hρ₁)) = projection g (handleBoundaryPoint 0)
  rw [radial_projection]
  apply congrArg (projection g)
  apply Subtype.ext
  have hone : (handleBoundaryPoint 0).val = (1 : ℂ) := by simp [handleBoundaryPoint]
  rw [hone]
  change (((1 : ℝ) - 1) + 1 / ‖(ρ : ℂ)‖) • (ρ : ℂ) = (1 : ℂ)
  rw [sub_self, zero_add, Complex.norm_real, Real.norm_of_nonneg hρ.le,
    Complex.real_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ hρ.ne', Complex.ofReal_one]

end LowDimensionalTopology.Geometry.Surfaces.HandlePunctured
