module
public import LowDimensionalTopology.Geometry.Fuchsian.PantsCoreCappedComplement

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Fuchsian
open LeanEval.Topology.ClassificationOfSurfaces

/-- Retain the signature's actual capped realization and its three physical
closed caps. The open-core complement homeomorphism assumes no classification
of marked discs, and the zero-genus homeomorphism retains the same realization. -/
theorem HasNielsenFuchsianSignature.openCore_capped_complement
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {hNE : DiscreteGroups.IsNonElementary H} {hFG : H.FG}
    (h : HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3) :
    ∃ w : P.domain.carrier, ∃ hw : IsDirichletCenter P w,
    ∃ hwN : w ∈ fuchsianNielsenCore P hNE,
      let hD := dirichletDomain_isConvexFuchsianPolygon P w hw
      let hfin := finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
      let hwD := dirichletDomain_center_mem P w hw
      ∃ J : Moise.PolygonalCircle,
      ∃ hc : J.carrier = Polygon.discPolygonKleinPlane ''
        (⋃ s : NielsenBoundarySide hD hNE, s.carrier),
      ∃ hv : ∀ p, J.IsVertexPoint p ↔ p ∈ Polygon.discPolygonKleinPlane ''
        nielsenCanonicalBoundaryMarks hD hNE hFG,
      ∃ n : ℕ, ∃ S : Polygon.CyclicDiscPolygonSupportData n,
      ∃ _hr : S.toCenteredData.kleinRegion =
        fuchsianPolygonCompactKlein P (dirichletDomain P w ∩ fuchsianNielsenCore P hNE),
        let Pcap := nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
        let W := Pcap.PolygonalRealization
          (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)
        let A := {f : Pcap.Face //
          f ≠ nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
        Nonempty (W ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
          Nat.card A = 3 ∧
          Nonempty (threeBoundaryOpenCore P hNE ≃ₜ
            ↥((⋃ f : A, range (nielsenActualCapDisc hD hNE hFG hfin w hwD hwN J hc hv f))ᶜ)) := by
  obtain ⟨w, hw, hwN, J, hc, hv, n, S, hr, hg, _ho, hp, hb⟩ := h
  let hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  let hfin := finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
  let hwD := dirichletDomain_center_mem P w hw
  have hf := finite_sided_polygon_parabolic_classes_finite hD hfin
  let : IsEmpty (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) :=
    (Nat.card_eq_zero.mp hp.symm).resolve_right hf.not_infinite
  refine ⟨w, hw, hwN, J, hc, hv, n, S, hr, ?_, ?_, ?_⟩
  · exact Surfaces.hasTopologicalGenus_zero_iff.mp hg
  · exact (nielsenCappedCapFaceCount_eq hD hNE hFG hfin w hwD hwN J hc hv).trans hb.symm
  · exact ⟨nielsenOpenCoreCappedComplementHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr⟩

end LowDimensionalTopology.Geometry.Fuchsian
