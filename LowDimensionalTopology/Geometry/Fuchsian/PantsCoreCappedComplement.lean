module
public import LowDimensionalTopology.Geometry.Fuchsian.PantsCoreBoundaryComponents
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSurface

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Fuchsian

section ActualCappedCore
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation
variable {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
  {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
  (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
  (hfin : {T : Set P.domain.carrier | IsFuchsianPolygonSide P D T}.Finite)
  (w : P.domain.carrier) (hwD : w ∈ D) (hwN : w ∈ fuchsianNielsenCore P hNE)
  (J : Moise.PolygonalCircle)
  (hc : J.carrier = Polygon.discPolygonKleinPlane ''
    (⋃ s : NielsenBoundarySide hD hNE, s.carrier))
  (hv : ∀ p, J.IsVertexPoint p ↔ p ∈ Polygon.discPolygonKleinPlane ''
    nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n : ℕ} (S : Polygon.CyclicDiscPolygonSupportData n)
  (hr : S.toCenteredData.kleinRegion =
    fuchsianPolygonCompactKlein P (D ∩ fuchsianNielsenCore P hNE))
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "W" => FiniteCyclicPresentation.PolygonalRealization (Pcap) (valid)
local notation "A" => {f : FiniteCyclicPresentation.Face (Pcap) //
  f ≠ nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "E" => nielsenWholeCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "first" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "cap" => nielsenActualCapDisc hD hNE hFG hfin w hwD hwN J hc hv
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv
local notation "qclock" => nielsenCappedOriginalQuotientClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "clockCore" => nielsenCappedQuotientClockInCore hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "cycle" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "caps" => ⋃ f : A, range (cap f)

/-- The same closed-core embedding detects an actual physical cap precisely
on its corresponding original projected boundary cycle. -/
theorem nielsenWholeCoreCappedEmbedding_mem_cap_iff
    (q : threeBoundaryClosedCore P hNE) (f : A) :
    E q ∈ range (cap f) ↔ q.val ∈ cycle (capCycle f.val f.property) := by
  rw [nielsenActualCapDisc_range hD hNE hFG hfin w hwD hwN J hc hv f]
  have hE := nielsenWholeCoreCappedEmbedding_isEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr
  have hfirst : E q ∈ range first :=
    ((nielsenWholeCoreCappedEmbedding_range hD hNE hFG hfin w hwD hwN J hc hv S hr) ▸ mem_range_self q).1
  constructor
  · intro hcap
    have hclock : E q ∈ range (clock f.val) := by
      rw [nielsenCappedCapClock_range hD hNE hFG hfin w hwD hwN J hc hv f.val f.property]
      exact ⟨hcap, hfirst⟩
    obtain ⟨z, hz⟩ := hclock
    have hq : clockCore f z = q := hE.injective
      ((nielsenWholeCoreCappedEmbedding_clock hD hNE hFG hfin w hwD hwN J hc hv S hr f z).trans hz)
    have hcycle : qclock f z ∈ cycle (capCycle f.val f.property) := by
      rw [← nielsenCappedOriginalQuotientClock_range hD hNE hFG hfin w hwD hwN J hc hv S hr f]
      exact mem_range_self z
    exact congrArg Subtype.val hq ▸ hcycle
  · intro hcycle
    rw [← nielsenCappedOriginalQuotientClock_range hD hNE hFG hfin w hwD hwN J hc hv S hr f] at hcycle
    obtain ⟨z, hz⟩ := hcycle
    have hq : clockCore f z = q := Subtype.ext hz
    rw [← hq, nielsenWholeCoreCappedEmbedding_clock]
    exact ((nielsenCappedCapClock_range hD hNE hFG hfin w hwD hwN J hc hv f.val f.property) ▸
      mem_range_self z).1

/-- All full physical caps meet the original closed core exactly along its
actual frontier; the cycle-cover and cap/cycle equivalence retain the marking. -/
theorem nielsenWholeCoreCappedEmbedding_mem_caps_iff
    (q : threeBoundaryClosedCore P hNE) :
    E q ∈ caps ↔ q.val ∈ frontier (threeBoundaryOpenCore P hNE) := by
  rw [← nielsenProjectedBoundaryCycles_eq_openCore_frontier hD hNE hFG hfin w hwD hwN J hc hv]
  let e := nielsenCappedCapBoundaryCycleEquiv hD hNE hFG hfin w hwD hwN J hc hv
  constructor
  · intro hq
    obtain ⟨f, hf⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨e f,
      (nielsenWholeCoreCappedEmbedding_mem_cap_iff hD hNE hFG hfin w hwD hwN J hc hv S hr q f).mp hf⟩
  · intro hq
    obtain ⟨c, hcycle⟩ := mem_iUnion.mp hq
    obtain ⟨f, rfl⟩ := e.surjective c
    exact mem_iUnion.mpr ⟨f,
      (nielsenWholeCoreCappedEmbedding_mem_cap_iff hD hNE hFG hfin w hwD hwN J hc hv S hr q f).mpr hcycle⟩

/-- Restrict the actual closed-core embedding to the original open core. -/
def nielsenOpenCoreCappedEmbedding (q : threeBoundaryOpenCore P hNE) : W :=
  E ⟨q.val, threeBoundaryOpenCore_subset_closed P hNE q.property⟩
local notation "Eopen" => nielsenOpenCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenOpenCoreCappedEmbedding_isEmbedding : Topology.IsEmbedding Eopen := by
  have hi : Topology.IsEmbedding (fun q : threeBoundaryOpenCore P hNE =>
      (⟨q.val, threeBoundaryOpenCore_subset_closed P hNE q.property⟩ : threeBoundaryClosedCore P hNE)) :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp Topology.IsEmbedding.subtypeVal
  exact (nielsenWholeCoreCappedEmbedding_isEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr).comp hi

/-- With no actual cusp classes, the image of the original open core is the
complement of all the same closed physical cap discs, including their circles. -/
theorem nielsenOpenCoreCappedEmbedding_range
    [IsEmpty (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)] :
    range Eopen = capsᶜ := by
  classical
  have hErange : range E = range first := by
    simpa only [Set.range_eq_empty, Set.sdiff_empty] using
      nielsenWholeCoreCappedEmbedding_range hD hNE hFG hfin w hwD hwN J hc hv S hr
  ext y
  constructor
  · rintro ⟨q, rfl⟩ hcap
    have hfront := (nielsenWholeCoreCappedEmbedding_mem_caps_iff hD hNE hFG hfin w hwD hwN J hc hv S hr
      ⟨q.val, threeBoundaryOpenCore_subset_closed P hNE q.property⟩).mp hcap
    rw [(isOpen_threeBoundaryOpenCore P hNE).frontier_eq] at hfront
    exact hfront.2 q.property
  · intro hy
    have hfirst : y ∈ range first := by
      by_contra hnot
      have hopen : y ∈ ⋃ f : A,
          range (nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv f.val) := by
        rw [← nielsenCappedFirstFace_complement_eq hD hNE hFG hfin w hwD hwN J hc hv]
        exact hnot
      obtain ⟨f, z, hz⟩ := mem_iUnion.mp hopen
      exact hy (mem_iUnion.mpr ⟨f, Hyperbolic.discToClosedModel z, hz⟩)
    obtain ⟨q, hq⟩ := hErange.symm ▸ hfirst
    have hU : q.val ∈ threeBoundaryOpenCore P hNE := by
      by_contra hnot
      have hfront : q.val ∈ frontier (threeBoundaryOpenCore P hNE) := by
        rw [(isOpen_threeBoundaryOpenCore P hNE).frontier_eq, closure_threeBoundaryOpenCore]
        exact ⟨q.property, hnot⟩
      exact hy (hq ▸ (nielsenWholeCoreCappedEmbedding_mem_caps_iff hD hNE hFG hfin w hwD hwN J hc hv S hr q).mpr hfront)
    exact ⟨⟨q.val, hU⟩, hq⟩

/-- The actual original open core is homeomorphic to the complement of the
same physical closed caps in the actual capped realization. -/
def nielsenOpenCoreCappedComplementHomeomorph
    [IsEmpty (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)] :
    threeBoundaryOpenCore P hNE ≃ₜ ↥(capsᶜ) :=
  (nielsenOpenCoreCappedEmbedding_isEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr).toHomeomorph.trans
    (Homeomorph.setCongr (nielsenOpenCoreCappedEmbedding_range hD hNE hFG hfin w hwD hwN J hc hv S hr))

end ActualCappedCore
end LowDimensionalTopology.Geometry.Fuchsian
