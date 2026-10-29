module

public import LowDimensionalTopology.Geometry.Surfaces.MeasuredFoliationWhiteheadQuotient
public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleFreeClasses
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import Mathlib.Topology.Subpath
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Actual finite transverse costs in original curve-class fibers

Every cost comes from actual transverse-arc measures or actual leaf pieces.
The curve and its original free class are retained. General pieces may have
singular vertices; open-end transverse costs are suprema of the given measures
on actual compact interior subpaths. Empty infimum fibers retain infinity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal Topology BigOperators

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- One actual circle representative traversed by the fixed once-around circle loop. -/
def measuredFoliationCircleLoop (L : EssentialSimpleCircle X) : Path (L.val 1) (L.val 1) :=
  Circle.expLoop.map L.val.continuous

/-- A genuine increasing finite partition of the complete unit parameter interval. -/
structure MeasuredFoliationUnitPartition where
  n : ℕ
  positive : 0 < n
  cuts : Fin (n + 1) → unitInterval
  strictMono : StrictMono cuts
  left : cuts 0 = 0
  right : cuts (Fin.last n) = 1

/-- The piece is the actual subpath of the same original representative. -/
def measuredFoliationLoopPiece (L : EssentialSimpleCircle X)
    (P : MeasuredFoliationUnitPartition) (i : Fin P.n) :
    Path (measuredFoliationCircleLoop L (P.cuts i.castSucc))
      (measuredFoliationCircleLoop L (P.cuts i.succ)) :=
  (measuredFoliationCircleLoop L).subpath (P.cuts i.castSucc) (P.cuts i.succ)

/-- A regular leaf piece locally has one constant actual plaque coordinate. -/
def IsMeasuredFoliationRegularLeafPiece (F : SingularMeasuredFoliation R)
    {x y : X} (γ : Path x y) : Prop :=
  ∀ t : unitInterval, ∃ e ∈ F.atlas.charts, ∃ J : Set unitInterval,
    IsOpen J ∧ t ∈ J ∧
      ∀ s ∈ J, γ s ∈ e.source ∧ (e (γ s)).im = (e (γ t)).im

/-- Interior leaf pieces allow singular vertices without assigning them a new measure. -/
def IsMeasuredFoliationInteriorLeafPiece (F : SingularMeasuredFoliation R)
    {x y : X} (γ : Path x y) : Prop :=
  ∀ t ∈ Ioo (0 : unitInterval) 1,
    ∃ e ∈ F.atlas.charts, ∃ J : Set unitInterval,
      IsOpen J ∧ t ∈ J ∧ J ⊆ Ioo 0 1 ∧
        ∀ s ∈ J, γ s ∈ e.source ∧ (e (γ s)).im = (e (γ t)).im

/-- Every compact interior subpath is an actual embedded transverse arc. -/
def IsMeasuredFoliationInteriorTransversePiece (F : SingularMeasuredFoliation R)
    {x y : X} (γ : Path x y) : Prop :=
  Topology.IsEmbedding (γ : unitInterval → X) ∧
    (∀ t ∈ Ioo (0 : unitInterval) 1, γ t ∉ F.atlas.singular) ∧
    ∀ a b : unitInterval, 0 < a → a < b → b < 1 →
      ∃ α : F.atlas.TransverseArc, ∀ t, α.curve t = γ.subpath a b t

/-- The open-end cost uses all actual compact interior transverse measures. -/
def measuredFoliationInteriorTransverseMass (F : SingularMeasuredFoliation R)
    {x y : X} (γ : Path x y) : ℝ≥0∞ :=
  sSup {m | ∃ a b : unitInterval, 0 < a ∧ a < b ∧ b < 1 ∧
    ∃ α : F.atlas.TransverseArc, (∀ t, α.curve t = γ.subpath a b t) ∧
      m = F.transverse.measure α Set.univ}

/-- A regular piece costs its actual transverse measure, or zero along its actual leaf. -/
def IsMeasuredFoliationRegularPieceCost (F : SingularMeasuredFoliation R)
    {x y : X} (γ : Path x y) (m : ℝ≥0∞) : Prop :=
  (∃ α : F.atlas.TransverseArc, (∀ t, α.curve t = γ t) ∧
    m = F.transverse.measure α Set.univ) ∨
      (IsMeasuredFoliationRegularLeafPiece F γ ∧ m = 0)

/-- General pieces also allow genuine leaf or transverse endpoints at singular vertices. -/
def IsMeasuredFoliationGeneralPieceCost (F : SingularMeasuredFoliation R)
    {x y : X} (γ : Path x y) (m : ℝ≥0∞) : Prop :=
  IsMeasuredFoliationRegularPieceCost F γ m ∨
    (IsMeasuredFoliationInteriorLeafPiece F γ ∧ m = 0) ∨
      (IsMeasuredFoliationInteriorTransversePiece F γ ∧
        m = measuredFoliationInteriorTransverseMass F γ)

/-- All regular finite-partition costs of this same actual original representative. -/
def measuredFoliationRegularCosts (F : nondegenerateMeasuredFoliation R)
    (L : EssentialSimpleCircle X) : Set ℝ≥0∞ :=
  {m | ∃ P : MeasuredFoliationUnitPartition, ∃ w : Fin P.n → ℝ≥0∞,
    (∀ i, IsMeasuredFoliationRegularPieceCost F.val (measuredFoliationLoopPiece L P i) (w i)) ∧
      m = ∑ i, w i}

/-- All finite-partition costs also admitting the specified actual singular vertices. -/
def measuredFoliationGeneralCosts (F : nondegenerateMeasuredFoliation R)
    (L : EssentialSimpleCircle X) : Set ℝ≥0∞ :=
  {m | ∃ P : MeasuredFoliationUnitPartition, ∃ w : Fin P.n → ℝ≥0∞,
    (∀ i, IsMeasuredFoliationGeneralPieceCost F.val (measuredFoliationLoopPiece L P i) (w i)) ∧
      m = ∑ i, w i}

/-- The regular adapted infimum over every actual representative in the original class fiber. -/
def measuredFoliationRegularIntersection (F : nondegenerateMeasuredFoliation R)
    (β : EssentialSimpleFreeClass X) : ℝ≥0∞ :=
  sInf {m | ∃ L : EssentialSimpleCircle X,
    L.freeClass = β ∧ m ∈ measuredFoliationRegularCosts F L}

/-- The corresponding actual infimum allowing the specified singular vertices. -/
def measuredFoliationGeneralIntersection (F : nondegenerateMeasuredFoliation R)
    (β : EssentialSimpleFreeClass X) : ℝ≥0∞ :=
  sInf {m | ∃ L : EssentialSimpleCircle X,
    L.freeClass = β ∧ m ∈ measuredFoliationGeneralCosts F L}

/-- A supplied actual regular partition is also a general partition with the same cost. -/
theorem measuredFoliationRegularCosts_subset_general
    (F : nondegenerateMeasuredFoliation R) (L : EssentialSimpleCircle X) :
    measuredFoliationRegularCosts F L ⊆ measuredFoliationGeneralCosts F L := by
  rintro m ⟨P, w, hpieces, hm⟩
  exact ⟨P, w, fun i => Or.inl (hpieces i), hm⟩

/-- Every supplied actual regular cost bounds the same-class regular infimum above. -/
theorem measuredFoliationRegularIntersection_le_cost
    (F : nondegenerateMeasuredFoliation R) (β : EssentialSimpleFreeClass X)
    (L : EssentialSimpleCircle X) (hL : L.freeClass = β)
    {m : ℝ≥0∞} (hm : m ∈ measuredFoliationRegularCosts F L) :
    measuredFoliationRegularIntersection F β ≤ m := by
  exact sInf_le ⟨L, hL, hm⟩

/-- Allowing singular vertices enlarges the actual cost set and lowers its infimum. -/
theorem measuredFoliationGeneralIntersection_le_regular
    (F : nondegenerateMeasuredFoliation R) (β : EssentialSimpleFreeClass X) :
    measuredFoliationGeneralIntersection F β ≤ measuredFoliationRegularIntersection F β := by
  apply le_sInf
  rintro m ⟨L, hL, hm⟩
  exact sInf_le ⟨L, hL, measuredFoliationRegularCosts_subset_general F L hm⟩

end LowDimensionalTopology.Geometry.Surfaces
