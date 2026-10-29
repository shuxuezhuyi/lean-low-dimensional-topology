module

public import LowDimensionalTopology.Unproved.Surfaces.MeasuredFoliationIntersectionGeometry

/-!
# Actual intersection coordinates on the geometric measured-foliation quotient

Endpoint regularization identifies the two actual infima. Finite conversion,
nonvanishing and descent construct the spectrum map from those same infima.
The conditional range is the independently defined weighted curve-spectrum cone.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
variable (hCurve : Unproved.Surfaces.ClosedCurveIntersectionGeometry R hg hgenus)
variable (H : Unproved.Surfaces.OriginalMeasuredFoliationIntersectionGeometry R hg hgenus hCurve)

include H in
/-- A genuinely finite regular cost makes the same-class infimum finite. -/
theorem measuredFoliationRegularIntersection_lt_top
    (F : nondegenerateMeasuredFoliation R) (β : EssentialSimpleFreeClass X) :
    measuredFoliationRegularIntersection F β < ∞ := by
  obtain ⟨L, m, hL, hm, hfinite⟩ := H.1 F β
  exact lt_of_le_of_lt (measuredFoliationRegularIntersection_le_cost F β L hL hm) hfinite

include H in
/-- Actual finite-prong endpoint regularization equates the two same-class infima. -/
theorem measuredFoliationRegularIntersection_eq_general
    (F : nondegenerateMeasuredFoliation R) (β : EssentialSimpleFreeClass X) :
    measuredFoliationRegularIntersection F β = measuredFoliationGeneralIntersection F β := by
  apply le_antisymm
  · apply le_sInf
    rintro m ⟨L, hL, hm⟩
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hmfinite
    have hεreal : 0 < (ε : ℝ) := NNReal.coe_pos.mpr hε
    obtain ⟨L', m', hm', hL', hbound⟩ := H.2.1 F L m hm ε hεreal
    have hregular := measuredFoliationRegularIntersection_le_cost F β L'
      (hL'.trans hL) hm'
    simpa only [ENNReal.ofReal_coe_nnreal] using hregular.trans hbound
  · exact measuredFoliationGeneralIntersection_le_regular F β

include H in
/-- Move invariance propagates along the actual finite Whitehead-equivalence chain. -/
theorem measuredFoliationRegularIntersection_eq_of_eqvGen
    {F G : nondegenerateMeasuredFoliation R}
    (h : Relation.EqvGen measuredFoliationElementaryStep F G)
    (β : EssentialSimpleFreeClass X) :
    measuredFoliationRegularIntersection F β = measuredFoliationRegularIntersection G β := by
  induction h with
  | rel F G h => exact H.2.2.1 F G h β
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The actual nonzero finite profile, formed from the measured infimum coordinates. -/
def measuredFoliationRepresentativeIntersectionSpectrum
    (F : nondegenerateMeasuredFoliation R) : NonzeroNonnegativeSpectrum X := by
  refine ⟨fun β => (measuredFoliationRegularIntersection F β).toNNReal, ?_⟩
  intro hzero
  obtain ⟨β, hpos⟩ := H.2.2.2.1 F
  have hfinite := measuredFoliationRegularIntersection_lt_top R hg hgenus hCurve H F β
  have hzeroβ : (measuredFoliationRegularIntersection F β).toNNReal = 0 :=
    congrFun hzero β
  have hJzero : measuredFoliationRegularIntersection F β = 0 := by
    calc
      measuredFoliationRegularIntersection F β =
          ((measuredFoliationRegularIntersection F β).toNNReal : ℝ≥0∞) :=
        (ENNReal.coe_toNNReal hfinite.ne).symm
      _ = 0 := by
        simpa only [ENNReal.coe_zero] using
          congrArg (fun t : NNReal => (t : ℝ≥0∞)) hzeroβ
  exact (ne_of_gt hpos) hJzero

/-- Finite conversion retains the exact original measured infimum at every coordinate. -/
theorem measuredFoliationRepresentativeIntersectionSpectrum_apply
    (F : nondegenerateMeasuredFoliation R) (β : EssentialSimpleFreeClass X) :
    ((measuredFoliationRepresentativeIntersectionSpectrum R hg hgenus hCurve H F).val β :
      ℝ≥0∞) = measuredFoliationRegularIntersection F β := by
  change ((measuredFoliationRegularIntersection F β).toNNReal : ℝ≥0∞) = _
  exact ENNReal.coe_toNNReal
    (measuredFoliationRegularIntersection_lt_top R hg hgenus hCurve H F β).ne

/-- The concrete representative profile respects the actual geometric equivalence. -/
theorem measuredFoliationRepresentativeIntersectionSpectrum_eq_of_eqvGen
    {F G : nondegenerateMeasuredFoliation R}
    (h : Relation.EqvGen measuredFoliationElementaryStep F G) :
    measuredFoliationRepresentativeIntersectionSpectrum R hg hgenus hCurve H F =
      measuredFoliationRepresentativeIntersectionSpectrum R hg hgenus hCurve H G := by
  apply Subtype.ext
  funext β
  apply ENNReal.coe_injective
  rw [measuredFoliationRepresentativeIntersectionSpectrum_apply,
    measuredFoliationRepresentativeIntersectionSpectrum_apply]
  exact measuredFoliationRegularIntersection_eq_of_eqvGen R hg hgenus hCurve H h β

/-- The actual spectrum map descends from the constructed representative coordinates. -/
def measuredFoliationIntersectionSpectrum :
    NondegenerateMeasuredFoliationQuotient R → NonzeroNonnegativeSpectrum X :=
  Quotient.lift (measuredFoliationRepresentativeIntersectionSpectrum R hg hgenus hCurve H)
    (fun _ _ h => measuredFoliationRepresentativeIntersectionSpectrum_eq_of_eqvGen
      R hg hgenus hCurve H h)

/-- The quotient map retains the same original foliation and its measured coordinates. -/
theorem measuredFoliationIntersectionSpectrum_apply
    (F : nondegenerateMeasuredFoliation R) (β : EssentialSimpleFreeClass X) :
    ((measuredFoliationIntersectionSpectrum R hg hgenus hCurve H
      (nondegenerateMeasuredFoliationQuotientMk F)).val β : ℝ≥0∞) =
        measuredFoliationRegularIntersection F β :=
  measuredFoliationRepresentativeIntersectionSpectrum_apply R hg hgenus hCurve H F β

/-- These same quotient coordinates also equal the infimum allowing singular vertices. -/
theorem measuredFoliationIntersectionSpectrum_apply_general
    (F : nondegenerateMeasuredFoliation R) (β : EssentialSimpleFreeClass X) :
    ((measuredFoliationIntersectionSpectrum R hg hgenus hCurve H
      (nondegenerateMeasuredFoliationQuotientMk F)).val β : ℝ≥0∞) =
        measuredFoliationGeneralIntersection F β := by
  exact (measuredFoliationIntersectionSpectrum_apply R hg hgenus hCurve H F β).trans
    (measuredFoliationRegularIntersection_eq_general R hg hgenus hCurve H F β)

/-- The independent nonzero cone in the original weighted curve-intersection closure. -/
def OriginalMeasuredFoliationSpectrumCone :=
  {f : NonzeroNonnegativeSpectrum X //
    f.val ∈ closure (Set.range (fun w : Set.Ioi (0 : ℝ) × EssentialSimpleFreeClass X =>
      (weightedIntersectionSpectrum R hg hgenus hCurve w).val))}

/-- Package the actual descended spectrum in that independently defined cone. -/
def measuredFoliationIntersectionConeMap (q : NondegenerateMeasuredFoliationQuotient R) :
    OriginalMeasuredFoliationSpectrumCone R hg hgenus hCurve := by
  refine ⟨measuredFoliationIntersectionSpectrum R hg hgenus hCurve H q, ?_⟩
  refine Quotient.inductionOn q ?_
  intro F
  exact ((H.2.2.2.2.2 _).mpr ⟨F, fun β =>
    measuredFoliationIntersectionSpectrum_apply R hg hgenus hCurve H F β⟩).2

/-- Cone packaging preserves every literal original measured coordinate. -/
theorem measuredFoliationIntersectionConeMap_apply
    (F : nondegenerateMeasuredFoliation R) (β : EssentialSimpleFreeClass X) :
    (((measuredFoliationIntersectionConeMap R hg hgenus hCurve H
      (nondegenerateMeasuredFoliationQuotientMk F)).val.val β) : ℝ≥0∞) =
        measuredFoliationRegularIntersection F β :=
  measuredFoliationIntersectionSpectrum_apply R hg hgenus hCurve H F β

/-- Equal concrete cone coordinates force equality in the actual geometric quotient. -/
theorem measuredFoliationIntersectionConeMap_injective :
    Function.Injective (measuredFoliationIntersectionConeMap R hg hgenus hCurve H) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro F G hFG
  apply Quotient.sound
  apply H.2.2.2.2.1 F G
  intro β
  calc
    measuredFoliationRegularIntersection F β =
        (((measuredFoliationIntersectionConeMap R hg hgenus hCurve H
          (nondegenerateMeasuredFoliationQuotientMk F)).val.val β) : ℝ≥0∞) :=
      (measuredFoliationIntersectionConeMap_apply R hg hgenus hCurve H F β).symm
    _ = (((measuredFoliationIntersectionConeMap R hg hgenus hCurve H
        (nondegenerateMeasuredFoliationQuotientMk G)).val.val β) : ℝ≥0∞) :=
      congrArg (fun z : OriginalMeasuredFoliationSpectrumCone R hg hgenus hCurve =>
        (z.val.val β : ℝ≥0∞)) hFG
    _ = measuredFoliationRegularIntersection G β :=
      measuredFoliationIntersectionConeMap_apply R hg hgenus hCurve H G β

/-- Every independent nonzero closure spectrum has an actual foliation representative. -/
theorem measuredFoliationIntersectionConeMap_surjective :
    Function.Surjective (measuredFoliationIntersectionConeMap R hg hgenus hCurve H) := by
  rintro ⟨f, hf⟩
  obtain ⟨F, hF⟩ := (H.2.2.2.2.2 f.val).mp ⟨f.property, hf⟩
  refine ⟨nondegenerateMeasuredFoliationQuotientMk F, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext β
  apply ENNReal.coe_injective
  exact (measuredFoliationIntersectionConeMap_apply R hg hgenus hCurve H F β).trans
    (hF β).symm

/-- The equivalence is induced by the actual intersection-coordinate map. -/
def measuredFoliationIntersectionConeEquiv :
    NondegenerateMeasuredFoliationQuotient R ≃
      OriginalMeasuredFoliationSpectrumCone R hg hgenus hCurve :=
  Equiv.ofBijective (measuredFoliationIntersectionConeMap R hg hgenus hCurve H)
    ⟨measuredFoliationIntersectionConeMap_injective R hg hgenus hCurve H,
      measuredFoliationIntersectionConeMap_surjective R hg hgenus hCurve H⟩

end LowDimensionalTopology.Geometry.Surfaces
