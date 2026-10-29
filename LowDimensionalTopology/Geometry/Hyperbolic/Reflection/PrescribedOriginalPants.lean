module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.PrescribedAnnularMirrors
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ThreePeripheralMatrices
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairRecognizedCore
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularOriginalFrontierWords
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
open Set Fuchsian Surfaces
noncomputable section

/-- Two explicit prerequisites give prescribed ordered original boundary geodesics
on the same actual annular quotient, with its pants core and all frontier components. -/
theorem exists_prescribed_original_annular_pants
    (hRecognition : LowDimensionalTopology.Unproved.Fuchsian.AnnularPairBoundaryRecognition)
    (hDiscs : LowDimensionalTopology.Unproved.Surfaces.ThreeSphericalDiscs)
    (a1 a2 a3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    ∃ E r x : ℝ, ∃ hE : 1 < E, ∃ hr : 0 < r,
      ∃ hin : 1 + r < x, ∃ hout : x + r < E,
      let P := HalfPlaneFuchsianGroup.cayleyData
        (annularPairReflectionHalfPlaneData E r x hE hr hin hout)
      let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
      let M := threeBoundaryQuotientModel P
        (annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout)
      ∃ q : Fin 3 → OriginalClosedGeodesic M,
        IsHyperbolicPairOfPants M (threeBoundaryOpenCore P hNE) ∧
        IsCompact (threeBoundaryClosedCore P hNE) ∧
        (∀ i, LiZhongQC.Covers M.halfPlaneCover
            (annularPeripheralMatrix E r x (zero_lt_one.trans hE) hr (![0, 2, 1] i))
            (q i).toLoop ∧
          Function.Injective ((q i).periodic.lift :
            AddCircle (1 : ℝ) → MobiusDomainQuotient P.domain) ∧
          (q i).length = ENNReal.ofReal (![a1, a2, a3] i)) ∧
        Function.Injective (fun i => range (q i).curve) ∧
        range (fun i => range (q i).curve) =
          {S | ∃ z ∈ frontier (threeBoundaryOpenCore P hNE),
            connectedComponentIn (frontier (threeBoundaryOpenCore P hNE)) z = S} := by
  classical
  obtain ⟨E, r, x, hE0, hr, hE, hin, hout, hdata⟩ :=
    exists_prescribed_annular_three_mirrors (a1 / 2) (a3 / 2) (a2 / 2)
      (by positivity) (by positivity) (by positivity)
  dsimp only at hdata
  obtain ⟨h01, h02, h12, l01, l02, l12⟩ := hdata
  let P := HalfPlaneFuchsianGroup.cayleyData
    (annularPairReflectionHalfPlaneData E r x hE hr hin hout)
  let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let hno := annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout
  let M := threeBoundaryQuotientModel P hno
  let A := annularPeripheralMatrix E r x (zero_lt_one.trans hE) hr
  obtain ⟨hB, _hArea⟩ := hRecognition E r x hE hr hin hout
  have hsig := annularPair_hasNielsenSignature_of_boundaryRecognition
    hRecognition E r x hE hr hin hout
  have hcore := annularPair_originalCore_isPants_and_closedCore_compact
    hRecognition hDiscs E r x hE hr hin hout
  dsimp only at hcore
  have hproj : ∀ i, cayleyMobius * realSLMobius (A i) * cayleyMobius⁻¹ =
      (annularDiscPeripheralWord E r x hE hr hin hout i).val := by
    intro i
    exact annularPeripheralMatrix_disc E r x hE hr hin hout i
  obtain ⟨q, hq, hInjective, hAll⟩ :=
    annularDiscPeripheralWords_all_frontier_components E r x hE hr hin hout
      hB hsig A hproj
  have htype := annularPeripheralMatrix_type_length E r x hE hr
    a1 a2 a3 h01 h02 h12 l01 l02 l12
  let sigma : Fin 3 ≃ Fin 3 := {
    toFun := ![0, 2, 1]
    invFun := ![0, 2, 1]
    left_inv := by intro i; fin_cases i <;> rfl
    right_inv := by intro i; fin_cases i <;> rfl }
  let ordered : Fin 3 → OriginalClosedGeodesic M := fun i => q (sigma i)
  refine ⟨E, r, x, hE, hr, hin, hout, ordered, hcore.1, hcore.2, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hq (sigma i)).1, (hq (sigma i)).2.1, ?_⟩
    change (q (sigma i)).length = ENNReal.ofReal (![a1, a2, a3] i)
    rw [(hq (sigma i)).2.2, (htype (sigma i)).2]
    fin_cases i <;> rfl
  · exact hInjective.comp sigma.injective
  · exact (sigma.surjective.range_comp (fun i => range (q i).curve)).trans hAll

end
end LowDimensionalTopology.Geometry.Hyperbolic
