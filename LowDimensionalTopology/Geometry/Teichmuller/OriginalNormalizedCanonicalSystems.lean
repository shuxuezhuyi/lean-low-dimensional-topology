module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCanonicalModelCutChange
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCanonicalModelPathTransport
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCanonicalCutQCTransport
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGeneratorComparison
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalWordDeck
public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalGlobalFricke
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedTeichmuller

/-!
# The full normalized canonical system of an original marked surface

The actual original point and every ordered based class are retained. A
supplied native model is transported through one genuine common path; changing
the cut at that point preserves every matrix. Given-model dynamic rigidity
then determines the entire projective system and its full covering group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation Hyperbolic

/-- The complete ordered projective system together with its generated group. -/
abbrev OriginalCanonicalSystemData (g : ℕ) :=
  (Edge g → Mobius.complexMobiusGroup) × Subgroup Mobius.complexMobiusGroup

/-- The system is realized on the unchanged original surface by its prescribed
classes. The same full matrix stabilizer uniformizes the actual model cover. -/
def IsOriginalNormalizedCanonicalSystem {g : ℕ} (hg : 1 < g)
    (N : OriginalGeneratorMarkedSurface g) (s : OriginalCanonicalSystemData g) : Prop :=
  letI : ChartedSpace ℂ (MarkedRiemannSurface.refl N.surface).carrier :=
    (MarkedRiemannSurface.refl N.surface).surface.toRiemannAtlas.toChartedSpace
  s.2 = Subgroup.closure (Set.range s.1) ∧
    ∃ E : OriginalOrientedCanonicalCut N.surface g
        (lt_trans Nat.zero_lt_one hg) N.point,
      E.family = N.classes ∧
      ∃ P : NormalizedCanonicalFuchsianModel hg E.polygon
          (MarkedRiemannSurface.refl N.surface),
        (∀ i, s.1 i = realSLMobius (P.matrices i)) ∧
        ∃ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ),
          (∀ A, A ∈ Γ ↔ ∀ z : ℍ,
            P.model.halfPlaneCover (A • z) = P.model.halfPlaneCover z) ∧
          LiZhongQC.IsUniformization Γ P.model.halfPlaneCover ∧
          LiZhongQC.IsFuchsian Γ ∧ s.2 = Γ.map realSLMobius

private theorem givenModel_full_projective_group
    {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
    {g : ℕ} {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
    {m : MarkedRiemannSurface.{0, 0} R}
    (P : NormalizedCanonicalFuchsianModel hg e m) :
    letI := m.surface.toRiemannAtlas.toChartedSpace
    ∃ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ A, A ∈ Γ ↔ ∀ z : ℍ,
        P.model.halfPlaneCover (A • z) = P.model.halfPlaneCover z) ∧
      LiZhongQC.IsUniformization Γ P.model.halfPlaneCover ∧
      LiZhongQC.IsFuchsian Γ ∧
      Γ.map realSLMobius = Subgroup.closure (Set.range (fun i => realSLMobius (P.matrices i))) := by
  let := m.surface.toRiemannAtlas.toChartedSpace
  let := m.surface.toRiemannAtlas.isManifold
  let := m.surface.t2Space
  let := m.surface.connectedSpace
  let := m.surface.compactSpace
  obtain ⟨Γ, hΓ, hp⟩ := P.model.exists_halfPlaneCover_uniformization
  obtain ⟨ρ, hρ⟩ := P.exists_deckMarking
  let C := Subgroup.closure (Set.range (fun i => realSLMobius (P.matrices i)))
  let π : FreeGroup (StandardLabels g) →* LiZhongQC.surfaceGroup g :=
    PresentedGroup.mk {standardRelator g}
  let σ : FreeGroup (StandardLabels g) →* Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s))
  let aSL := MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin 2) ℝ) ℍ
  let aDeck := MulAction.toPermHom (deck P.model.halfPlaneCover) ℍ
  have ha : aSL.comp σ = aDeck.comp (ρ.toMonoidHom.comp π) := by
    apply FreeGroup.ext_hom
    intro s
    apply Equiv.ext
    intro z
    change (FreeGroup.lift (fun t => P.matrices ((edgeLabelEquiv g).symm t))
      (FreeGroup.of s)) • z = ρ (PresentedGroup.of s) • z
    rw [FreeGroup.lift_apply_of]
    simpa only [Equiv.apply_symm_apply] using hρ ((edgeLabelEquiv g).symm s) z
  have hσ : σ.range ≤ C.comap realSLMobius := by
    apply FreeGroup.range_lift_le
    rintro _ ⟨s, rfl⟩
    exact Subgroup.subset_closure ⟨(edgeLabelEquiv g).symm s, rfl⟩
  refine ⟨Γ, hΓ, hp, LiZhongQC.utm_x_isFuchsian hp, ?_⟩
  apply le_antisymm
  · rintro _ ⟨A, hA, rfl⟩
    let hAHomeo : ℍ ≃ₜ ℍ :=
      { toFun := fun z => A • z
        invFun := fun z => A⁻¹ • z
        left_inv := inv_smul_smul A
        right_inv := smul_inv_smul A
        continuous_toFun := continuous_const_smul A
        continuous_invFun := continuous_const_smul A⁻¹ }
    let dA : deck P.model.halfPlaneCover :=
      ⟨hAHomeo, by
        funext z
        exact (hΓ A).mp hA z⟩
    obtain ⟨a, ha'⟩ := ρ.surjective dA
    obtain ⟨w, hw⟩ := PresentedGroup.mk_surjective {standardRelator g} a
    have hacts (z : ℍ) : σ w • z = A • z := by
      have h := congrArg (fun f : FreeGroup (StandardLabels g) →* Equiv.Perm ℍ => (f w) z) ha
      change σ w • z = ρ (π w) • z at h
      change π w = a at hw
      rw [hw, ha'] at h
      exact h
    have hproj := realSLMobius_eq_of_native_action (σ w) A hacts
    rw [← hproj]
    exact hσ ⟨w, rfl⟩
  · apply (Subgroup.closure_le (Γ.map realSLMobius)).mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨P.matrices i, (hΓ (P.matrices i)).mpr ?_, rfl⟩
    intro z
    rw [P.represents i z]
    exact deck.proj_smul _ z

private def nativeOriginalRealization {g : ℕ}
    (B N : OriginalGeneratorMarkedSurface g)
    (F : SmoothSurfaceEquiv B.surface.toRiemannSurface N.surface.toRiemannSurface)
    (hF : PreservesComplexOrientation B.surface.toRiemannAtlas
      N.surface.toRiemannAtlas F.toHomeomorph) : MarkedRiemannSurface.{0, 0} B.surface where
  carrier := N.carrier
  topology := N.topology
  surface := N.surface
  marking := F
  orientation_preserving := hF

private theorem generators_eq_of_originalRealization
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (D : OriginalOrientedCanonicalCut B.surface g
      (lt_trans Nat.zero_lt_one hg) B.point)
    (hD : D.family = B.classes)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable B.surface hg D.polygon)
    (N : OriginalGeneratorMarkedSurface g) (s : OriginalCanonicalSystemData g)
    (hs : IsOriginalNormalizedCanonicalSystem hg N s)
    (F : SmoothSurfaceEquiv B.surface.toRiemannSurface N.surface.toRiemannSurface)
    (hF : PreservesComplexOrientation B.surface.toRiemannAtlas
      N.surface.toRiemannAtlas F.toHomeomorph)
    (c : Path (F.toHomeomorph B.point) N.point)
    (hc : ∀ i : Edge g,
      FundamentalGroup.fundamentalGroupMulEquivOfPath c
        (FundamentalGroup.map
          (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
          B.point (B.classes i)) = N.classes i) :
    ∀ i, realSLMobius
      ((chosenCanonicalModel hA (nativeOriginalRealization B N F hF)).matrices i) = s.1 i := by
  obtain ⟨_hGroup, E, hE, P, hTuple, _hΓ⟩ := hs
  let P₀ := chosenCanonicalModel hA (nativeOriginalRealization B N F hF)
  obtain ⟨_L, Q, _hL, _hL₀, _hL₁, _hModel, hMatrices⟩ :=
    NormalizedCanonicalFuchsianModel.exists_transportOriginalCanonicalPath
      hg B N D hD E hE F hF c hc P₀
  have hQP := Q.generators_eq P
    (MarkedRiemannSurface.equivalent_refl (MarkedRiemannSurface.refl N.surface))
  intro i
  calc
    realSLMobius (P₀.matrices i) = realSLMobius (Q.matrices i) :=
      congrArg realSLMobius (congrFun hMatrices.symm i)
    _ = realSLMobius (P.matrices i) := hQP i
    _ = s.1 i := (hTuple i).symm

private theorem comparison_eq_of_originalRealization
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (hTransport : Unproved.Teichmuller.OriginalCanonicalFamilyMarkingTransport hg B)
    (N : OriginalGeneratorMarkedSurface g)
    (F : SmoothSurfaceEquiv B.surface.toRiemannSurface N.surface.toRiemannSurface)
    (hF : PreservesComplexOrientation B.surface.toRiemannAtlas
      N.surface.toRiemannAtlas F.toHomeomorph)
    (c : Path (F.toHomeomorph B.point) N.point)
    (hc : ∀ i : Edge g,
      FundamentalGroup.fundamentalGroupMulEquivOfPath c
        (FundamentalGroup.map
          (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
          B.point (B.classes i)) = N.classes i) :
    originalGeneratorComparison hg B hTransport
      (TeichmullerSpace.mk (nativeOriginalRealization B N F hF)) =
        OriginalGeneratorTeichmullerSpace.mk N := by
  change OriginalGeneratorTeichmullerSpace.mk
      (originalGeneratorMarkedTarget hg B hTransport (nativeOriginalRealization B N F hF)) =
    OriginalGeneratorTeichmullerSpace.mk N
  apply Quotient.sound
  apply OriginalGeneratorMarkedSurface.equivalent_symm
  refine ⟨Homeomorph.refl N.carrier, RiemannAnalyticMap.id _, c, ?_⟩
  intro i
  change FundamentalGroup.fundamentalGroupMulEquivOfPath c
    (FundamentalGroup.map (ContinuousMap.id N.carrier) (F.toHomeomorph B.point)
      (FundamentalGroup.map
        (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
        B.point (B.classes i))) = N.classes i
  rw [FundamentalGroup.map_id]
  change FundamentalGroup.fundamentalGroupMulEquivOfPath c
    (FundamentalGroup.map
      (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
      B.point (B.classes i)) = N.classes i
  exact hc i

/-- Every original geometrically marked surface has a unique complete
normalized projective system and its actual full covering group. -/
theorem existsUnique_originalNormalizedCanonicalSystem
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (D : OriginalOrientedCanonicalCut B.surface g
      (lt_trans Nat.zero_lt_one hg) B.point)
    (hD : D.family = B.classes)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable B.surface hg D.polygon)
    (hRealize : Unproved.Teichmuller.OriginalGeneratorPrescribedPositiveSmoothRealization hg B)
    (N : OriginalGeneratorMarkedSurface g) :
    ∃! s : OriginalCanonicalSystemData g, IsOriginalNormalizedCanonicalSystem hg N s := by
  obtain ⟨E, hE⟩ : HasOriginalCanonicalCut N.surface g
      (lt_trans Nat.zero_lt_one hg) N.point N.classes := by
    cases g with
    | zero => omega
    | succ n => exact N.canonical
  obtain ⟨F, hF, c, hc⟩ := hRealize N
  let P₀ := chosenCanonicalModel hA (nativeOriginalRealization B N F hF)
  obtain ⟨_L, P, _hL, _hL₀, _hL₁, _hModel, _hMatrices⟩ :=
    NormalizedCanonicalFuchsianModel.exists_transportOriginalCanonicalPath
      hg B N D hD E hE F hF c hc P₀
  obtain ⟨Γ, hΓ, hp, hFuchsian, hRange⟩ := givenModel_full_projective_group P
  let γ : Edge g → Mobius.complexMobiusGroup := fun i => realSLMobius (P.matrices i)
  let s : OriginalCanonicalSystemData g := (γ, Subgroup.closure (Set.range γ))
  refine ⟨s, ⟨rfl, E, hE, P, fun _ => rfl, Γ, hΓ, hp, hFuchsian, hRange.symm⟩, ?_⟩
  intro t ht
  obtain ⟨hGroup, E', hE', P', hTuple, _hΓ⟩ := ht
  obtain ⟨Q, _hModel, _hLift, hMatrices⟩ :=
    NormalizedCanonicalFuchsianModel.exists_changeOriginalCanonicalCut
      hg N E E' (hE.trans hE'.symm) P
  have hQP := Q.generators_eq P'
    (MarkedRiemannSurface.equivalent_refl (MarkedRiemannSurface.refl N.surface))
  have hTupleEq : t.1 = γ := by
    funext i
    calc
      t.1 i = realSLMobius (P'.matrices i) := hTuple i
      _ = realSLMobius (Q.matrices i) := (hQP i).symm
      _ = realSLMobius (P.matrices i) := congrArg realSLMobius (congrFun hMatrices i)
      _ = γ i := rfl
  exact Prod.ext hTupleEq
    (hGroup.trans (congrArg (fun f => Subgroup.closure (Set.range f)) hTupleEq))

/-- The complete system and generated group depend only on the original
marked equivalence class. One genuine common path is used for every slot. -/
theorem originalNormalizedCanonicalSystem_eq_of_equivalent
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (D : OriginalOrientedCanonicalCut B.surface g
      (lt_trans Nat.zero_lt_one hg) B.point)
    (hD : D.family = B.classes)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable B.surface hg D.polygon)
    (hRealize : Unproved.Teichmuller.OriginalGeneratorPrescribedPositiveSmoothRealization hg B)
    (hGeom : Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport
      B.surface hg B.point D)
    {M N : OriginalGeneratorMarkedSurface g} (hMN : M.Equivalent N)
    {s t : OriginalCanonicalSystemData g}
    (hs : IsOriginalNormalizedCanonicalSystem hg M s)
    (ht : IsOriginalNormalizedCanonicalSystem hg N t) : s = t := by
  let hTransport := originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport
    hg B D hD hGeom
  obtain ⟨F, hF, c, hc⟩ := hRealize M
  obtain ⟨G, hG, d, hd⟩ := hRealize N
  have hM := comparison_eq_of_originalRealization hg B hTransport M F hF c hc
  have hN := comparison_eq_of_originalRealization hg B hTransport N G hG d hd
  have hclasses : TeichmullerSpace.mk (nativeOriginalRealization B M F hF) =
      TeichmullerSpace.mk (nativeOriginalRealization B N G hG) := by
    apply (originalGeneratorComparison_bijective hg B hTransport hRealize).1
    exact hM.trans ((Quotient.sound hMN).trans hN.symm)
  have hNative := (TeichmullerSpace.mk_eq_mk_iff
    (nativeOriginalRealization B M F hF) (nativeOriginalRealization B N G hG)).mp hclasses
  let PM := chosenCanonicalModel hA (nativeOriginalRealization B M F hF)
  let PN := chosenCanonicalModel hA (nativeOriginalRealization B N G hG)
  have hProj := PM.generators_eq PN hNative
  have hSM := generators_eq_of_originalRealization hg B D hD hA M s hs F hF c hc
  have hTN := generators_eq_of_originalRealization hg B D hD hA N t ht G hG d hd
  have hTupleEq : s.1 = t.1 := by
    funext i
    exact (hSM i).symm.trans ((hProj i).trans (hTN i))
  have hsGroup : s.2 = Subgroup.closure (Set.range s.1) := hs.1
  have htGroup : t.2 = Subgroup.closure (Set.range t.1) := ht.1
  exact Prod.ext hTupleEq
    (hsGroup.trans ((congrArg (fun f => Subgroup.closure (Set.range f)) hTupleEq).trans htGroup.symm))

end LowDimensionalTopology.Geometry.Teichmuller
