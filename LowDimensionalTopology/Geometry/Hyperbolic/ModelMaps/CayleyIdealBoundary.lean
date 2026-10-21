/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk
public import LowDimensionalTopology.Geometry.Mobius.FractionalLinear
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Tactic

/-!
# –7.2: ideal boundaries and the closed models

The half-plane compactification is a subspace of the extended complex plane.
The extra finite real boundary points are retained; it is not the one-point
compactification of the open upper half-plane itself.
-/

@[expose] public section

open Set Filter
open scoped UpperHalfPlane Complex.UnitDisc OnePoint Topology ComplexConjugate

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius

/-- An invertible matrix for the exact Cayley fractional linear map. -/
def extendedCayleyMatrix : Mobius.FractionalLinearMatrix := Mobius.coefficientMatrix 1 (-Complex.I) 1 Complex.I
  (by intro h; have hi := congrArg Complex.im h; norm_num at hi)

/-- The Cayley map on the actual one-point compactification of the complex plane. -/
def extendedCayley : OnePoint ℂ ≃ₜ OnePoint ℂ := Mobius.fractionalLinearHomeomorph extendedCayleyMatrix

theorem extendedCayley_coe (z : ℂ) (hz : z + Complex.I ≠ 0) :
    extendedCayley z = (cayleyFormula z : OnePoint ℂ) := by
  change Mobius.fractionalLinearOfCoefficients 1 (-Complex.I) 1 Complex.I _ z = _
  rw [Mobius.fractionalLinearOfCoefficients_coe]
  simp only [one_mul, hz, ite_false, cayleyFormula, sub_eq_add_neg]

theorem extendedCayley_infty : extendedCayley ∞ = ((1 : ℂ) : OnePoint ℂ) := by
  change Mobius.fractionalLinearOfCoefficients 1 (-Complex.I) 1 Complex.I _ ∞ = _
  rw [Mobius.fractionalLinearOfCoefficients_infty]
  simp

theorem extendedCayley_pole : extendedCayley ((-Complex.I : ℂ) : OnePoint ℂ) = ∞ := by
  change Mobius.fractionalLinearOfCoefficients 1 (-Complex.I) 1 Complex.I _ (-Complex.I : ℂ) = _
  rw [Mobius.fractionalLinearOfCoefficients_coe]
  simp

theorem cayley_norm_le_one_iff (z : ℂ) (hz : z + Complex.I ≠ 0) :
    ‖cayleyFormula z‖ ≤ 1 ↔ 0 ≤ z.im := by
  rw [cayleyFormula, norm_div, div_le_one (norm_pos_iff.mpr hz),
    ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  constructor <;> intro h <;> nlinarith

theorem cayley_norm_lt_one_iff (z : ℂ) (hz : z + Complex.I ≠ 0) :
    ‖cayleyFormula z‖ < 1 ↔ 0 < z.im := by
  rw [cayleyFormula, norm_div, div_lt_one (norm_pos_iff.mpr hz),
    ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  constructor <;> intro h <;> nlinarith

theorem cayley_norm_eq_one_iff (z : ℂ) (hz : z + Complex.I ≠ 0) :
    ‖cayleyFormula z‖ = 1 ↔ z.im = 0 := by
  constructor
  · intro h
    have hp := (cayley_norm_le_one_iff z hz).mp h.le
    have hn : ¬0 < z.im := by
      intro hi
      have hc := (cayley_norm_lt_one_iff z hz).mpr hi
      linarith
    linarith
  · intro h
    apply le_antisymm ((cayley_norm_le_one_iff z hz).mpr h.ge)
    apply le_of_not_gt
    intro hc
    have hi := (cayley_norm_lt_one_iff z hz).mp hc
    linarith

/-- The open half-plane as a subspace of the extended complex plane. -/
def openHalfPlaneSet : Set (OnePoint ℂ) := ((↑) : ℂ → OnePoint ℂ) '' {z : ℂ | 0 < z.im}

/-- The closed half-plane model includes the real axis and infinity. -/
def closedHalfPlaneSet : Set (OnePoint ℂ) :=
  insert ∞ (((↑) : ℂ → OnePoint ℂ) '' {z : ℂ | 0 ≤ z.im})

/-- The half-plane ideal boundary is the real axis together with infinity. -/
def halfPlaneIdealBoundary : Set (OnePoint ℂ) :=
  insert ∞ (((↑) : ℂ → OnePoint ℂ) '' {z : ℂ | z.im = 0})

/-- The unit disc inside the extended complex plane. -/
def extendedOpenDisc : Set (OnePoint ℂ) :=
  ((↑) : ℂ → OnePoint ℂ) '' Metric.ball (0 : ℂ) 1

/-- The closed disc has only finite points in this chart. -/
def extendedClosedDisc : Set (OnePoint ℂ) :=
  ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (0 : ℂ) 1

/-- The disc ideal boundary is the unit circle. -/
def extendedDiscIdealBoundary : Set (OnePoint ℂ) :=
  ((↑) : ℂ → OnePoint ℂ) '' Metric.sphere (0 : ℂ) 1

theorem coe_mem_openHalfPlaneSet (z : ℂ) :
    (z : OnePoint ℂ) ∈ openHalfPlaneSet ↔ 0 < z.im := by simp [openHalfPlaneSet]

theorem coe_mem_closedHalfPlaneSet (z : ℂ) :
    (z : OnePoint ℂ) ∈ closedHalfPlaneSet ↔ 0 ≤ z.im := by simp [closedHalfPlaneSet]

theorem coe_mem_halfPlaneIdealBoundary (z : ℂ) :
    (z : OnePoint ℂ) ∈ halfPlaneIdealBoundary ↔ z.im = 0 := by simp [halfPlaneIdealBoundary]

theorem coe_mem_extendedOpenDisc (z : ℂ) :
    (z : OnePoint ℂ) ∈ extendedOpenDisc ↔ ‖z‖ < 1 := by simp [extendedOpenDisc, Metric.mem_ball]

theorem coe_mem_extendedClosedDisc (z : ℂ) :
    (z : OnePoint ℂ) ∈ extendedClosedDisc ↔ ‖z‖ ≤ 1 := by
  simp [extendedClosedDisc, Metric.mem_closedBall]

theorem coe_mem_extendedDiscIdealBoundary (z : ℂ) :
    (z : OnePoint ℂ) ∈ extendedDiscIdealBoundary ↔ ‖z‖ = 1 := by
  simp [extendedDiscIdealBoundary]

/-- The exact map identifies the full closed models, including their exceptional points. -/
theorem closedHalfPlaneSet_cayley_iff (p : OnePoint ℂ) :
    p ∈ closedHalfPlaneSet ↔ extendedCayley p ∈ extendedClosedDisc := by
  cases p with
  | infty => simp [closedHalfPlaneSet, extendedCayley_infty, coe_mem_extendedClosedDisc]
  | coe z =>
    by_cases hz : z + Complex.I = 0
    · have hz' : z = -Complex.I := eq_neg_of_add_eq_zero_left hz
      subst z
      simp [coe_mem_closedHalfPlaneSet, extendedCayley_pole, extendedClosedDisc]
    · rw [coe_mem_closedHalfPlaneSet, extendedCayley_coe z hz, coe_mem_extendedClosedDisc,
        cayley_norm_le_one_iff z hz]

/-- The map also identifies the open models. -/
theorem openHalfPlaneSet_cayley_iff (p : OnePoint ℂ) :
    p ∈ openHalfPlaneSet ↔ extendedCayley p ∈ extendedOpenDisc := by
  cases p with
  | infty => simp [openHalfPlaneSet, extendedCayley_infty, coe_mem_extendedOpenDisc]
  | coe z =>
    by_cases hz : z + Complex.I = 0
    · have hz' : z = -Complex.I := eq_neg_of_add_eq_zero_left hz
      subst z
      simp [coe_mem_openHalfPlaneSet, extendedCayley_pole, extendedOpenDisc]
    · rw [coe_mem_openHalfPlaneSet, extendedCayley_coe z hz, coe_mem_extendedOpenDisc,
        cayley_norm_lt_one_iff z hz]

/-- The half-plane ideal boundary is mapped onto the actual unit circle. -/
theorem idealBoundary_cayley_iff (p : OnePoint ℂ) :
    p ∈ halfPlaneIdealBoundary ↔ extendedCayley p ∈ extendedDiscIdealBoundary := by
  cases p with
  | infty => simp [halfPlaneIdealBoundary, extendedCayley_infty, coe_mem_extendedDiscIdealBoundary]
  | coe z =>
    by_cases hz : z + Complex.I = 0
    · have hz' : z = -Complex.I := eq_neg_of_add_eq_zero_left hz
      subst z
      simp [coe_mem_halfPlaneIdealBoundary, extendedCayley_pole, extendedDiscIdealBoundary]
    · rw [coe_mem_halfPlaneIdealBoundary, extendedCayley_coe z hz,
        coe_mem_extendedDiscIdealBoundary, cayley_norm_eq_one_iff z hz]

theorem closedHalfPlaneSet_eq_preimage :
    closedHalfPlaneSet = extendedCayley ⁻¹' extendedClosedDisc := by
  ext p
  exact closedHalfPlaneSet_cayley_iff p

theorem openHalfPlaneSet_eq_preimage :
    openHalfPlaneSet = extendedCayley ⁻¹' extendedOpenDisc := by
  ext p
  exact openHalfPlaneSet_cayley_iff p

theorem halfPlaneIdealBoundary_eq_preimage :
    halfPlaneIdealBoundary = extendedCayley ⁻¹' extendedDiscIdealBoundary := by
  ext p
  exact idealBoundary_cayley_iff p

theorem extendedCayley_image_closedHalfPlane :
    extendedCayley '' closedHalfPlaneSet = extendedClosedDisc := by
  rw [closedHalfPlaneSet_eq_preimage, Set.image_preimage_eq _ extendedCayley.surjective]

theorem extendedCayley_image_openHalfPlane :
    extendedCayley '' openHalfPlaneSet = extendedOpenDisc := by
  rw [openHalfPlaneSet_eq_preimage, Set.image_preimage_eq _ extendedCayley.surjective]

theorem extendedCayley_image_idealBoundary :
    extendedCayley '' halfPlaneIdealBoundary = extendedDiscIdealBoundary := by
  rw [halfPlaneIdealBoundary_eq_preimage, Set.image_preimage_eq _ extendedCayley.surjective]

theorem closedHalfPlaneSet_eq_open_union_boundary :
    closedHalfPlaneSet = openHalfPlaneSet ∪ halfPlaneIdealBoundary := by
  ext p
  cases p with
  | infty => simp [closedHalfPlaneSet, halfPlaneIdealBoundary]
  | coe z =>
    simp only [coe_mem_closedHalfPlaneSet, Set.mem_union, coe_mem_openHalfPlaneSet,
      coe_mem_halfPlaneIdealBoundary]
    constructor
    · intro h
      rcases eq_or_lt_of_le h with heq | hlt
      · exact Or.inr heq.symm
      · exact Or.inl hlt
    · rintro (h | h) <;> linarith

theorem halfPlaneIdealBoundary_eq_real_infty :
    halfPlaneIdealBoundary = insert ∞ (Set.range (fun t : ℝ => ((t : ℂ) : OnePoint ℂ))) := by
  ext p
  cases p with
  | infty => simp [halfPlaneIdealBoundary]
  | coe z =>
    rw [coe_mem_halfPlaneIdealBoundary]
    simp only [Set.mem_insert_iff, OnePoint.coe_ne_infty, false_or, Set.mem_range,
      OnePoint.coe_eq_coe]
    constructor
    · intro h
      exact ⟨z.re, Complex.ext rfl h.symm⟩
    · rintro ⟨t, rfl⟩
      rfl

theorem isCompact_extendedClosedDisc : IsCompact extendedClosedDisc :=
  (isCompact_closedBall (0 : ℂ) 1).image OnePoint.continuous_coe

theorem isCompact_closedHalfPlaneSet : IsCompact closedHalfPlaneSet := by
  rw [closedHalfPlaneSet_eq_preimage]
  exact extendedCayley.isCompact_preimage.mpr isCompact_extendedClosedDisc

theorem extendedClosedDisc_eq_open_union_boundary :
    extendedClosedDisc = extendedOpenDisc ∪ extendedDiscIdealBoundary := by
  ext p
  cases p with
  | infty => simp [extendedClosedDisc, extendedOpenDisc, extendedDiscIdealBoundary]
  | coe z =>
    rw [coe_mem_extendedClosedDisc, Set.mem_union, coe_mem_extendedOpenDisc,
      coe_mem_extendedDiscIdealBoundary]
    exact le_iff_lt_or_eq

theorem disjoint_halfPlane_idealBoundary : Disjoint openHalfPlaneSet halfPlaneIdealBoundary := by
  rw [Set.disjoint_left]
  intro p hp hb
  cases p with
  | infty => simp [openHalfPlaneSet] at hp
  | coe z =>
    have hi := (coe_mem_openHalfPlaneSet z).mp hp
    have he := (coe_mem_halfPlaneIdealBoundary z).mp hb
    linarith

theorem disjoint_disc_idealBoundary : Disjoint extendedOpenDisc extendedDiscIdealBoundary := by
  rw [Set.disjoint_left]
  intro p hp hb
  cases p with
  | infty => simp [extendedOpenDisc] at hp
  | coe z =>
    have hi := (coe_mem_extendedOpenDisc z).mp hp
    have he := (coe_mem_extendedDiscIdealBoundary z).mp hb
    linarith

theorem isCompact_extendedDiscIdealBoundary : IsCompact extendedDiscIdealBoundary :=
  (isCompact_sphere (0 : ℂ) 1).image OnePoint.continuous_coe

theorem isCompact_halfPlaneIdealBoundary : IsCompact halfPlaneIdealBoundary := by
  rw [halfPlaneIdealBoundary_eq_preimage]
  exact extendedCayley.isCompact_preimage.mpr isCompact_extendedDiscIdealBoundary

/-- The genuine closed half-plane model, with real boundary points and infinity. -/
abbrev ClosedHalfPlaneModel := {p : OnePoint ℂ // p ∈ closedHalfPlaneSet}

instance closedHalfPlaneCompactSpace : CompactSpace ClosedHalfPlaneModel :=
  isCompact_iff_compactSpace.mp isCompact_closedHalfPlaneSet

/-- The standard closed disc is compact in its original Euclidean subspace topology. -/
instance closedDiscCompactSpace : CompactSpace 𝕔𝔻 :=
  inferInstanceAs (CompactSpace (Metric.closedBall (0 : ℂ) 1))

def closedDiscToExtended (z : 𝕔𝔻) : OnePoint ℂ := ((z : ℂ) : OnePoint ℂ)

theorem isEmbedding_closedDiscToExtended : Topology.IsEmbedding closedDiscToExtended :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.comp Complex.UnitClosedDisc.isEmbedding_coe

theorem range_closedDiscToExtended : Set.range closedDiscToExtended = extendedClosedDisc := by
  ext p
  cases p with
  | infty => simp [closedDiscToExtended, extendedClosedDisc]
  | coe z =>
    rw [coe_mem_extendedClosedDisc]
    simp only [Set.mem_range, closedDiscToExtended, OnePoint.coe_eq_coe]
    constructor
    · rintro ⟨w, rfl⟩
      exact w.norm_le_one
    · intro h
      exact ⟨Complex.UnitClosedDisc.mk z h, rfl⟩

def closedDiscExtendedHomeomorph : 𝕔𝔻 ≃ₜ extendedClosedDisc :=
  isEmbedding_closedDiscToExtended.toHomeomorph.trans (Homeomorph.setCongr range_closedDiscToExtended)

/-- The extended Cayley map restricts to a homeomorphism of the actual closed models. -/
def closedModelCayleyHomeomorph : ClosedHalfPlaneModel ≃ₜ 𝕔𝔻 :=
  (extendedCayley.subtype closedHalfPlaneSet_cayley_iff).trans closedDiscExtendedHomeomorph.symm

/-- In particular the ideal boundary is homeomorphic to the actual unit circle in the extended chart. -/
def idealBoundaryCayleyHomeomorph : halfPlaneIdealBoundary ≃ₜ extendedDiscIdealBoundary :=
  extendedCayley.subtype idealBoundary_cayley_iff

def halfPlaneToClosedModel (z : ℍ) : ClosedHalfPlaneModel :=
  ⟨((z : ℂ) : OnePoint ℂ), (coe_mem_closedHalfPlaneSet (z : ℂ)).mpr z.im_pos.le⟩

theorem isEmbedding_halfPlaneToClosedModel : Topology.IsEmbedding halfPlaneToClosedModel := by
  apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  exact OnePoint.isOpenEmbedding_coe.isEmbedding.comp UpperHalfPlane.isEmbedding_coe

def discToClosedModel (z : 𝔻) : 𝕔𝔻 := Complex.UnitClosedDisc.mk (z : ℂ) z.norm_lt_one.le

theorem isEmbedding_discToClosedModel : Topology.IsEmbedding discToClosedModel := by
  apply Complex.UnitClosedDisc.isEmbedding_coe.of_comp_iff.mp
  exact Complex.UnitDisc.isEmbedding_coe

theorem closedModelCayley_toExtended (p : ClosedHalfPlaneModel) :
    closedDiscToExtended (closedModelCayleyHomeomorph p) = extendedCayley p.1 := by
  exact congrArg Subtype.val
    (closedDiscExtendedHomeomorph.apply_symm_apply
      ⟨extendedCayley p.1, (closedHalfPlaneSet_cayley_iff p.1).mp p.2⟩)

theorem closedModelCayley_on_interior (z : ℍ) :
    closedModelCayleyHomeomorph (halfPlaneToClosedModel z) = discToClosedModel (halfPlaneToDisc z) := by
  apply isEmbedding_closedDiscToExtended.injective
  rw [closedModelCayley_toExtended]
  change extendedCayley ((z : ℂ) : OnePoint ℂ) = (cayleyFormula z : OnePoint ℂ)
  exact extendedCayley_coe z (cayley_denom_ne_zero z)


/-- The open disc is dense in its actual closed disc in the extended plane. -/
theorem closure_extendedOpenDisc : closure extendedOpenDisc = extendedClosedDisc := by
  apply le_antisymm
  · apply closure_minimal _ isCompact_extendedClosedDisc.isClosed
    exact Set.image_mono Metric.ball_subset_closedBall
  · have h := image_closure_subset_closure_image (f := ((↑) : ℂ → OnePoint ℂ))
      OnePoint.continuous_coe (s := Metric.ball (0 : ℂ) 1)
    rw [closure_ball (0 : ℂ) one_ne_zero] at h
    exact h

/-- The closed half-plane model is exactly the closure in the extended complex plane. -/
theorem closure_openHalfPlaneSet : closure openHalfPlaneSet = closedHalfPlaneSet := by
  rw [openHalfPlaneSet_eq_preimage, ← extendedCayley.preimage_closure,
    closure_extendedOpenDisc, ← closedHalfPlaneSet_eq_preimage]

/-- closure within the open hyperbolic half-plane. -/
def halfPlaneRelativeClosure (s : Set ℍ) : Set ℍ := closure s

/-- closure within the closed half-plane model. -/
def halfPlaneClosedModelClosure (s : Set ℍ) : Set ClosedHalfPlaneModel :=
  closure (halfPlaneToClosedModel '' s)

/-- The open-disc version of relative hyperbolic closure. -/
def discRelativeClosure (s : Set 𝔻) : Set 𝔻 := closure s

/-- The closed-disc version of closure, allowing ideal boundary limit points. -/
def discClosedModelClosure (s : Set 𝔻) : Set 𝕔𝔻 := closure (discToClosedModel '' s)

theorem halfPlaneRelativeClosure_eq_preimage (s : Set ℍ) :
    halfPlaneRelativeClosure s = halfPlaneToClosedModel ⁻¹' halfPlaneClosedModelClosure s :=
  isEmbedding_halfPlaneToClosedModel.closure_eq_preimage_closure_image s

theorem discRelativeClosure_eq_preimage (s : Set 𝔻) :
    discRelativeClosure s = discToClosedModel ⁻¹' discClosedModelClosure s :=
  isEmbedding_discToClosedModel.closure_eq_preimage_closure_image s

theorem isClosedEmbedding_closedHalfPlaneVal :
    Topology.IsClosedEmbedding (Subtype.val : ClosedHalfPlaneModel → OnePoint ℂ) :=
  continuous_subtype_val.isClosedEmbedding Subtype.val_injective

theorem isClosedEmbedding_closedDiscToExtended : Topology.IsClosedEmbedding closedDiscToExtended :=
  isEmbedding_closedDiscToExtended.continuous.isClosedEmbedding
    isEmbedding_closedDiscToExtended.injective

/-- Closed-model closure agrees with ambient extended-plane closure, under the actual embedding. -/
theorem halfPlaneClosedModelClosure_ambient (s : Set ℍ) :
    (Subtype.val : ClosedHalfPlaneModel → OnePoint ℂ) '' halfPlaneClosedModelClosure s =
      closure ((fun z : ℍ => ((z : ℂ) : OnePoint ℂ)) '' s) := by
  rw [halfPlaneClosedModelClosure, ← isClosedEmbedding_closedHalfPlaneVal.closure_image_eq,
    Set.image_image]
  rfl

/-- The corresponding ambient-plane statement for the closed disc. -/
theorem discClosedModelClosure_ambient (s : Set 𝔻) :
    closedDiscToExtended '' discClosedModelClosure s =
      closure ((fun z : 𝔻 => ((z : ℂ) : OnePoint ℂ)) '' s) := by
  rw [discClosedModelClosure, ← isClosedEmbedding_closedDiscToExtended.closure_image_eq,
    Set.image_image]
  rfl

theorem isCompact_halfPlaneClosedModelClosure (s : Set ℍ) :
    IsCompact (halfPlaneClosedModelClosure s) := isClosed_closure.isCompact

theorem isCompact_discClosedModelClosure (s : Set 𝔻) :
    IsCompact (discClosedModelClosure s) := isClosed_closure.isCompact

/-- Cayley preserves compactified closure, as well as the open-model topology. -/
theorem closedModelCayley_image_closure (s : Set ℍ) :
    closedModelCayleyHomeomorph '' halfPlaneClosedModelClosure s =
      discClosedModelClosure (halfPlaneToDisc '' s) := by
  rw [halfPlaneClosedModelClosure, closedModelCayleyHomeomorph.image_closure,
    Set.image_image]
  change closure ((fun z => closedModelCayleyHomeomorph (halfPlaneToClosedModel z)) '' s) = _
  simp_rw [closedModelCayley_on_interior]
  rw [discClosedModelClosure, Set.image_image]

theorem range_halfPlaneToClosedModel_ambient :
    (Subtype.val : ClosedHalfPlaneModel → OnePoint ℂ) '' Set.range halfPlaneToClosedModel =
      openHalfPlaneSet := by
  rw [← Set.range_comp]
  ext p
  cases p with
  | infty => simp [halfPlaneToClosedModel, openHalfPlaneSet]
  | coe z =>
    rw [coe_mem_openHalfPlaneSet]
    simp only [Set.mem_range, Function.comp_def, halfPlaneToClosedModel, OnePoint.coe_eq_coe]
    constructor
    · rintro ⟨w, rfl⟩
      exact w.im_pos
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩

theorem range_discToClosedModel_ambient :
    closedDiscToExtended '' Set.range discToClosedModel = extendedOpenDisc := by
  rw [← Set.range_comp]
  ext p
  cases p with
  | infty => simp [closedDiscToExtended, discToClosedModel, extendedOpenDisc]
  | coe z =>
    rw [coe_mem_extendedOpenDisc]
    simp only [Set.mem_range, Function.comp_def, closedDiscToExtended, discToClosedModel,
      OnePoint.coe_eq_coe]
    constructor
    · rintro ⟨w, rfl⟩
      exact w.norm_lt_one
    · intro hz
      exact ⟨Complex.UnitDisc.mk z hz, rfl⟩

/-- Every closed-model point is a limit of genuine half-plane points. -/
theorem denseRange_halfPlaneToClosedModel : DenseRange halfPlaneToClosedModel := by
  apply dense_iff_closure_eq.mpr
  apply isClosedEmbedding_closedHalfPlaneVal.injective.image_injective
  rw [← isClosedEmbedding_closedHalfPlaneVal.closure_image_eq,
    range_halfPlaneToClosedModel_ambient, closure_openHalfPlaneSet]
  simp

/-- Every closed-disc point is a limit of genuine open-disc points. -/
theorem denseRange_discToClosedModel : DenseRange discToClosedModel := by
  apply dense_iff_closure_eq.mpr
  apply isEmbedding_closedDiscToExtended.injective.image_injective
  rw [← isClosedEmbedding_closedDiscToExtended.closure_image_eq,
    range_discToClosedModel_ambient, closure_extendedOpenDisc]
  simp only [Set.image_univ, range_closedDiscToExtended]

/-- The genuine disc path metric uses exactly the original Euclidean subspace topology. -/
theorem disc_metric_topology_eq_induced :
    discHyperbolicMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced Complex.UnitDisc.coe (inferInstance : TopologicalSpace ℂ) := rfl

/-- The embedding into the closed model detects the genuine half-plane metric topology. -/
theorem halfPlane_metric_topology_eq_closed_model_induced :
    (inferInstance : MetricSpace ℍ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced halfPlaneToClosedModel
        (inferInstance : TopologicalSpace ClosedHalfPlaneModel) :=
  isEmbedding_halfPlaneToClosedModel.eq_induced

/-- The embedding into the closed disc detects the genuine disc path-metric topology. -/
theorem disc_metric_topology_eq_closed_model_induced :
    discHyperbolicMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced discToClosedModel (inferInstance : TopologicalSpace 𝕔𝔻) :=
  isEmbedding_discToClosedModel.eq_induced

end

end LowDimensionalTopology.Geometry.Hyperbolic
