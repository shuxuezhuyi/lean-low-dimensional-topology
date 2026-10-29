module

public import LowDimensionalTopology.Geometry.Surfaces.MeasuredFoliationWhiteheadQuotient

/-!
# Positive scaling of the specified geometric foliation quotient

One finite positive real scales every actual transverse measure. The atlas and
all geometric move witnesses are retained. Scaling therefore descends to the
Whitehead quotient, whose positive projective set quotient is defined here.
No topology or intersection-spectrum identification is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal Topology

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- Scale every actual transverse measure by the same positive real, retaining the atlas. -/
def scaleSingularMeasuredFoliation (a : Set.Ioi (0 : ℝ))
    (F : SingularMeasuredFoliation R) : SingularMeasuredFoliation R where
  atlas := F.atlas
  transverse :=
    { measure := fun α => ENNReal.ofReal a.val • F.transverse.measure α
      finite := by
        intro α
        simpa only [Measure.smul_apply, smul_eq_mul] using
          ENNReal.mul_lt_top (show ENNReal.ofReal a.val < ∞ from ENNReal.ofReal_lt_top)
            (F.transverse.finite α)
      reparametrize := by
        intro α β ρ hρ
        rw [Measure.map_smul (ENNReal.ofReal a.val) ρ.continuous.measurable.aemeasurable]
        exact congrArg (fun μ : Measure unitInterval => ENNReal.ofReal a.val • μ)
          (F.transverse.reparametrize α β ρ hρ)
      subarc := by
        intro α β s t hst σ hσ hcurve
        rw [Measure.map_smul (ENNReal.ofReal a.val) σ.continuous.measurable.aemeasurable,
          Measure.restrict_smul]
        exact congrArg (fun μ : Measure unitInterval => ENNReal.ofReal a.val • μ)
          (F.transverse.subarc α β s t hst σ hσ hcurve)
      holonomy := by
        intro α β H hH
        exact congrArg (fun μ : Measure unitInterval => ENNReal.ofReal a.val • μ)
          (F.transverse.holonomy α β H hH) }

/-- Positive scaling preserves atomlessness and full support on every original arc. -/
def scaleNondegenerateMeasuredFoliation (a : Set.Ioi (0 : ℝ))
    (F : nondegenerateMeasuredFoliation R) : nondegenerateMeasuredFoliation R := by
  refine ⟨scaleSingularMeasuredFoliation a F.val, ?_⟩
  intro α
  constructor
  · intro t
    change (ENNReal.ofReal a.val • F.val.transverse.measure α) {t} = 0
    rw [Measure.smul_apply, (F.property α).1 t, smul_zero]
  · intro U hU hne
    change 0 < (ENNReal.ofReal a.val • F.val.transverse.measure α) U
    rw [Measure.smul_apply]
    exact ENNReal.mul_pos_iff.mpr
      ⟨ENNReal.ofReal_pos.mpr a.property, (F.property α).2 U hU hne⟩

/-- Each arc has exactly the same common positive measure factor. -/
theorem scaleNondegenerateMeasuredFoliation_measure (a : Set.Ioi (0 : ℝ))
    (F : nondegenerateMeasuredFoliation R) (α : F.val.atlas.TransverseArc) :
    (scaleNondegenerateMeasuredFoliation a F).val.transverse.measure α =
      ENNReal.ofReal a.val • F.val.transverse.measure α := rfl

/-- Complement transport keeps its actual charts and arc images after common scaling. -/
theorem IsMeasuredFoliationTransportOutside.scale (a : Set.Ioi (0 : ℝ))
    {F G : SingularMeasuredFoliation R} {c : C(X, X)} {K L : Set X}
    (h : IsMeasuredFoliationTransportOutside F G c K L) :
    IsMeasuredFoliationTransportOutside (scaleSingularMeasuredFoliation a F)
      (scaleSingularMeasuredFoliation a G) c K L := by
  rcases h with ⟨hcharts, hforward, hbackward, hmeasure⟩
  refine ⟨hcharts, hforward, hbackward, ?_⟩
  intro α β hα hβ
  exact congrArg (fun μ : Measure unitInterval => ENNReal.ofReal a.val • μ)
    (hmeasure α β hα hβ)

/-- The same ambient isotopy and endpoint homeomorphism witness the scaled move. -/
theorem MeasuredFoliationIsotopyStep.scale (a : Set.Ioi (0 : ℝ))
    {F G : SingularMeasuredFoliation R} (h : MeasuredFoliationIsotopyStep F G) :
    MeasuredFoliationIsotopyStep (scaleSingularMeasuredFoliation a F)
      (scaleSingularMeasuredFoliation a G) := by
  rcases h with ⟨f, ⟨hsingular, htransport⟩, H, hH⟩
  exact ⟨f, ⟨hsingular, IsMeasuredFoliationTransportOutside.scale a htransport⟩, H, hH⟩

/-- The connection uses the unchanged atlas, endpoints, path and local leaf conditions. -/
def scaleMeasuredFoliationSaddleConnection (a : Set.Ioi (0 : ℝ))
    {F : SingularMeasuredFoliation R} (γ : MeasuredFoliationSaddleConnection F) :
    MeasuredFoliationSaddleConnection (scaleSingularMeasuredFoliation a F) where
  start := γ.start
  finish := γ.finish
  start_ne_finish := γ.start_ne_finish
  start_singular := γ.start_singular
  finish_singular := γ.finish_singular
  curve := γ.curve
  isEmbedding := γ.isEmbedding
  interior_regular := γ.interior_regular
  locally_leafwise := γ.locally_leafwise

/-- The same disk, collapse, collapsed point and complement homeomorphism witness scaling. -/
theorem MeasuredFoliationWhiteheadCollapse.scale (a : Set.Ioi (0 : ℝ))
    {F G : SingularMeasuredFoliation R} (h : MeasuredFoliationWhiteheadCollapse F G) :
    MeasuredFoliationWhiteheadCollapse (scaleSingularMeasuredFoliation a F)
      (scaleSingularMeasuredFoliation a G) := by
  rcases h with ⟨γ, d, c, p, h⟩
  rcases h with ⟨hd, hK, hlocal, hfix, hmaps, hquotient, hfiber, hhomeo, hsingular, htrans⟩
  refine ⟨scaleMeasuredFoliationSaddleConnection a γ, d, c, p,
    hd, hK, hlocal, hfix, hmaps, hquotient, hfiber, hhomeo, hsingular, ?_⟩
  exact IsMeasuredFoliationTransportOutside.scale a htrans

/-- Every actual elementary move is covariant under the same positive scaling. -/
theorem measuredFoliationElementaryStep_scale (a : Set.Ioi (0 : ℝ))
    {F G : nondegenerateMeasuredFoliation R} (h : measuredFoliationElementaryStep F G) :
    measuredFoliationElementaryStep (scaleNondegenerateMeasuredFoliation a F)
      (scaleNondegenerateMeasuredFoliation a G) := by
  rcases h with h | h
  · exact Or.inl (MeasuredFoliationIsotopyStep.scale a h)
  · exact Or.inr (MeasuredFoliationWhiteheadCollapse.scale a h)

/-- Common scaling respects every finite chain generating the geometric quotient. -/
theorem measuredFoliationEqvGen_scale (a : Set.Ioi (0 : ℝ))
    {F G : nondegenerateMeasuredFoliation R}
    (h : Relation.EqvGen measuredFoliationElementaryStep F G) :
    Relation.EqvGen measuredFoliationElementaryStep
      (scaleNondegenerateMeasuredFoliation a F) (scaleNondegenerateMeasuredFoliation a G) := by
  let S : nondegenerateMeasuredFoliation R → nondegenerateMeasuredFoliation R :=
    scaleNondegenerateMeasuredFoliation a
  induction h with
  | rel F G h =>
    exact Relation.EqvGen.rel (S F) (S G) (measuredFoliationElementaryStep_scale a h)
  | refl F => exact Relation.EqvGen.refl (S F)
  | symm F G _ ih => exact Relation.EqvGen.symm (S F) (S G) ih
  | trans F G H _ _ hFG hGH => exact Relation.EqvGen.trans (S F) (S G) (S H) hFG hGH

/-- The actual positive scaling on classes, descended from the actual measure formula. -/
def scaleNondegenerateMeasuredFoliationQuotient (a : Set.Ioi (0 : ℝ)) :
    NondegenerateMeasuredFoliationQuotient R → NondegenerateMeasuredFoliationQuotient R :=
  Quotient.lift
    (fun F => nondegenerateMeasuredFoliationQuotientMk (scaleNondegenerateMeasuredFoliation a F))
    (by
      intro F G h
      exact Quotient.sound (measuredFoliationEqvGen_scale a h))

/-- The descended value has exactly the scaled original representative. -/
@[simp] theorem scaleNondegenerateMeasuredFoliationQuotient_mk (a : Set.Ioi (0 : ℝ))
    (F : nondegenerateMeasuredFoliation R) :
    scaleNondegenerateMeasuredFoliationQuotient a (nondegenerateMeasuredFoliationQuotientMk F) =
      nondegenerateMeasuredFoliationQuotientMk (scaleNondegenerateMeasuredFoliation a F) := by
  rfl

/-- A projective generator uses one common strictly positive real factor. -/
def measuredFoliationProjectiveStep
    (p q : NondegenerateMeasuredFoliationQuotient R) : Prop :=
  ∃ a : Set.Ioi (0 : ℝ), q = scaleNondegenerateMeasuredFoliationQuotient a p

/-- Positive scaling generates the projective relation on the actual geometric classes. -/
def measuredFoliationProjectiveSetoid (R : ClosedRiemannSurface X) :
    Setoid (NondegenerateMeasuredFoliationQuotient R) :=
  Relation.EqvGen.setoid (measuredFoliationProjectiveStep (R := R))

/-- The projective set quotient; no topology on foliation data is introduced. -/
def ProjectiveNondegenerateMeasuredFoliationQuotient (R : ClosedRiemannSurface X) :=
  Quotient (measuredFoliationProjectiveSetoid R)

/-- Project the same actual geometric class into the positive projective set quotient. -/
def projectivizeNondegenerateMeasuredFoliation
    (p : NondegenerateMeasuredFoliationQuotient R) :
    ProjectiveNondegenerateMeasuredFoliationQuotient R :=
  Quotient.mk (measuredFoliationProjectiveSetoid R) p

/-- Every supplied common positive scaling has the same actual projective class. -/
theorem projectivizeNondegenerateMeasuredFoliation_scale (a : Set.Ioi (0 : ℝ))
    (p : NondegenerateMeasuredFoliationQuotient R) :
    projectivizeNondegenerateMeasuredFoliation (scaleNondegenerateMeasuredFoliationQuotient a p) =
      projectivizeNondegenerateMeasuredFoliation p := by
  apply Quotient.sound
  apply Relation.EqvGen.symm
  exact Relation.EqvGen.rel _ _ ⟨a, rfl⟩

end LowDimensionalTopology.Geometry.Surfaces
