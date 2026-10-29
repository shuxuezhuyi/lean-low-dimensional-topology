module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalFrickeGenerators
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGroupPresentationPositive
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange

/-!
# Actual positive polygon sides in the computed surface presentation

The existing surface presentation is computed through the actual puncture/disc
cover and then changes basepoint along a path in the actual punctured polygon.
The positive geometric sides therefore give the inverse standard letters up to
one common conjugation, obtained from the retraction of that same path.
The loop classes below are actual included polygon-side paths.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology

namespace LowDimensionalTopology.Geometry.Surfaces.HandlePresentation

private theorem liftEquiv_symm_apply {G H : Type*} [Group G] [Group H]
    (N : Subgroup G) [N.Normal] {f : G →* H}
    (hf : Function.Surjective f) (hN : N = f.ker) (x : G) :
    (QuotientGroup.liftEquiv N hf hN).symm (f x) = QuotientGroup.mk x :=
  (MulEquiv.symm_apply_eq (QuotientGroup.liftEquiv N hf hN)).mpr rfl

private theorem liftEquiv_symm_congr_trans_apply
    {G H K L : Type*} [Group G] [Group H] [Group K] [Group L]
    (N : Subgroup G) [N.Normal] {f : G →* H}
    (hf : Function.Surjective f) (hN : N = f.ker)
    (M : Subgroup K) [M.Normal] (e : G ≃* K) (he : N.map e.toMonoidHom = M)
    (q : (K ⧸ M) ≃* L) (x : G) :
    ((QuotientGroup.liftEquiv N hf hN).symm.trans
      ((QuotientGroup.congr N M e he).trans q)) (f x) =
      q (QuotientGroup.mk (e x)) := by
  exact (congrArg (fun y : G ⧸ N => q (QuotientGroup.congr N M e he y))
    (liftEquiv_symm_apply N hf hN x)).trans
      (congrArg q (QuotientGroup.congr_mk N M e he x))

/-- The actual quotient homomorphism from the geometric boundary group. -/
def boundarySurfaceHom (g : ℕ) (hg : 0 < g) :
    FundamentalGroup (Boundary g) (boundaryBase g) →* LiZhongQC.surfaceGroup g :=
  (boundaryRelationQuotientEquivSurfaceGroup g hg).toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.normalClosure
      ({pathClass (boundaryLoop g)} : Set (FundamentalGroup (Boundary g) (boundaryBase g)))))

private theorem boundarySurfaceHom_apply (g : ℕ) (hg : 0 < g)
    (γ : FundamentalGroup (Boundary g) (boundaryBase g)) :
    boundarySurfaceHom g hg γ =
      PresentedGroup.mk ({standardRelator g} : Set (FreeGroup (StandardLabels g)))
        (edgeFreeGroupEquiv g (boundaryFundamentalGroupMulEquiv g hg γ)) := rfl

/-- The actual positive geometric side has exactly its inverse standard label
under the boundary quotient map. -/
theorem boundarySurfaceHom_sideLoop (g : ℕ) (hg : 0 < g) (d : Edge g) :
    boundarySurfaceHom g hg (pathClass (sideLoop (HandleCW.edgeSide d))) =
      (PresentedGroup.of (edgeLabelEquiv g d) : LiZhongQC.surfaceGroup g)⁻¹ := by
  rw [boundarySurfaceHom_apply, boundaryFundamentalGroupMulEquiv_sideLoop,
    edgeFreeGroupEquiv_of, map_inv]
  rfl

/-- Inclusion of a boundary loop into the original polygon, through its actual
punctured-subspace inclusion. -/
def polygonBoundaryClass (g : ℕ) :
    FundamentalGroup (Boundary g) (boundaryBase g) →*
      FundamentalGroup (PolygonQuotient g) (boundaryBase g).val :=
  (FundamentalGroup.map (ContinuousMap.subtypeVal (punctured g))
    (boundaryInclusion g (boundaryBase g))).comp
      (FundamentalGroup.map (boundaryInclusion g) (boundaryBase g))

/-- The two actual inclusions equal the direct boundary inclusion on loop classes. -/
theorem polygonBoundaryClass_eq_map (g : ℕ)
    (γ : FundamentalGroup (Boundary g) (boundaryBase g)) :
    polygonBoundaryClass g γ =
      FundamentalGroup.map (ContinuousMap.subtypeVal (boundary g)) (boundaryBase g) γ := by
  have h := TauCeti.FundamentalGroup.mapOfEq_comp
    (ContinuousMap.subtypeVal (punctured g)) (boundaryInclusion g) rfl rfl γ
  change FundamentalGroup.map (ContinuousMap.subtypeVal (punctured g))
      (boundaryInclusion g (boundaryBase g))
      (FundamentalGroup.map (boundaryInclusion g) (boundaryBase g) γ) =
    FundamentalGroup.map
      ((ContinuousMap.subtypeVal (punctured g)).comp (boundaryInclusion g))
      (boundaryBase g) γ
  simpa only [TauCeti.FundamentalGroup.mapOfEq_rfl] using h

private theorem polygonFundamentalGroup_inclusion (g : ℕ) (hg : 0 < g)
    (γ : FundamentalGroup (Punctured g)
      (HandlePunctureBoundary.overlapToPunctured g (HandlePunctureBoundary.overlapBase g))) :
    polygonFundamentalGroupMulEquivSurfaceGroup g hg
      (FundamentalGroup.map (ContinuousMap.subtypeVal (punctured g))
        (HandlePunctureBoundary.overlapToPunctured g
          (HandlePunctureBoundary.overlapBase g)) γ) =
      boundarySurfaceHom g hg
        (FundamentalGroup.mapOfEq (HandlePunctured.retractionMap g)
          (HandlePunctureBoundary.boundaryFromOverlap_base g) γ) := by
  let a : Punctured g := HandlePunctureBoundary.overlapToPunctured g
    (HandlePunctureBoundary.overlapBase g)
  let c : FundamentalGroup (Punctured g) a :=
    FundamentalGroup.map (HandlePunctureBoundary.overlapToPunctured g)
      (HandlePunctureBoundary.overlapBase g) (HandlePunctureBoundary.overlapGenerator g)
  let N : Subgroup (FundamentalGroup (Punctured g) a) :=
    Subgroup.normalClosure ({c} : Set (FundamentalGroup (Punctured g) a))
  let M : Subgroup (FundamentalGroup (Boundary g) (boundaryBase g)) :=
    Subgroup.normalClosure ({pathClass (boundaryLoop g)} :
      Set (FundamentalGroup (Boundary g) (boundaryBase g)))
  dsimp only [polygonFundamentalGroupMulEquivSurfaceGroup, discCoverQuotientEquiv]
  exact liftEquiv_symm_congr_trans_apply
    (G := FundamentalGroup (Punctured g) a)
    (H := FundamentalGroup (PolygonQuotient g) a.val)
    (K := FundamentalGroup (Boundary g) (boundaryBase g))
    (L := LiZhongQC.surfaceGroup g) N _ _ M
    (puncturedFundamentalGroupMulEquivBoundary g a
      (HandlePunctureBoundary.boundaryFromOverlap_base g)) _
    (boundaryRelationQuotientEquivSurfaceGroup g hg) γ

private theorem mapOfEq_basepoint_symm_natural
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a b : A} (p : Path a b) {ya yb : B}
    (ha : f a = ya) (hb : f b = yb) (γ : FundamentalGroup A b) :
    FundamentalGroup.mapOfEq f ha ((FundamentalGroup.fundamentalGroupMulEquivOfPath p).symm γ) =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((p.map f.continuous).cast ha.symm hb.symm)).symm
          (FundamentalGroup.mapOfEq f hb γ) := by
  cases ha
  cases hb
  rcases γ with ⟨γ⟩
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    apply CategoryTheory.End.ext
    simp only [FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply,
      FundamentalGroup.mapOfEq_apply, Path.cast_rfl_rfl,
      Path.Homotopic.Quotient.cast_rfl_rfl,
      ← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_symm,
      ← Path.Homotopic.Quotient.mk_map, Path.map_trans, ← Path.map_symm]

/-- The explicit existing polygon presentation carries every positive
geometric side to its inverse standard letter under one common conjugation.
The conjugator comes from its real punctured basepoint path. -/
theorem polygonBoundary_sideLoop_images_up_to_common_conjugation
    (g : ℕ) (hg : 0 < g) :
    ∃ c : LiZhongQC.surfaceGroup g, ∀ d : Edge g,
      polygonBoundaryFundamentalGroupMulEquivSurfaceGroup g hg
        (polygonBoundaryClass g (pathClass (sideLoop (HandleCW.edgeSide d)))) =
      c * Inv.inv (α := LiZhongQC.surfaceGroup g) (PresentedGroup.of (edgeLabelEquiv g d)) * c⁻¹ := by
  let := puncturedPathConnected g hg
  let a := HandlePunctureBoundary.overlapToPunctured g
    (HandlePunctureBoundary.overlapBase g)
  let b := boundaryInclusion g (boundaryBase g)
  let p : Path a b := PathConnectedSpace.somePath a b
  let j := ContinuousMap.subtypeVal (punctured g)
  let r := HandlePunctured.retractionMap g
  have ha : r a = boundaryBase g := HandlePunctureBoundary.boundaryFromOverlap_base g
  have hb : r b = boundaryBase g := HandlePunctured.retraction_inclusion g (boundaryBase g)
  let rp : Path (boundaryBase g) (boundaryBase g) := (p.map r.continuous).cast ha.symm hb.symm
  let q := boundarySurfaceHom g hg
  have hri : r.comp (boundaryInclusion g) = ContinuousMap.id (Boundary g) :=
    ContinuousMap.ext (HandlePunctured.retraction_inclusion g)
  have hret (β : FundamentalGroup (Boundary g) (boundaryBase g)) :
      FundamentalGroup.mapOfEq r ha
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath p).symm
          (FundamentalGroup.map (boundaryInclusion g) (boundaryBase g) β)) =
        (FundamentalGroup.fundamentalGroupMulEquivOfPath rp).symm β := by
    have hinv : FundamentalGroup.mapOfEq r hb
        (FundamentalGroup.map (boundaryInclusion g) (boundaryBase g) β) = β := by
      have hi := TauCeti.FundamentalGroup.mapOfEq_mapOfEq_of_comp_eq_id
        r (boundaryInclusion g) rfl hb hri β
      simpa only [TauCeti.FundamentalGroup.mapOfEq_rfl] using hi
    exact (mapOfEq_basepoint_symm_natural r p ha hb
      (FundamentalGroup.map (boundaryInclusion g) (boundaryBase g) β)).trans
        (congrArg (FundamentalGroup.fundamentalGroupMulEquivOfPath rp).symm hinv)
  have hincl (β : FundamentalGroup (Boundary g) (boundaryBase g)) :
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map j.continuous)).symm
        (polygonBoundaryClass g β) =
      FundamentalGroup.map j a
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath p).symm
          (FundamentalGroup.map (boundaryInclusion g) (boundaryBase g) β)) := by
    have hn := mapOfEq_basepoint_symm_natural j p rfl rfl
      (FundamentalGroup.map (boundaryInclusion g) (boundaryBase g) β)
    change (FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map j.continuous)).symm
        (FundamentalGroup.map j b
          (FundamentalGroup.map (boundaryInclusion g) (boundaryBase g) β)) =
      FundamentalGroup.map j a
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath p).symm
          (FundamentalGroup.map (boundaryInclusion g) (boundaryBase g) β))
    simpa only [TauCeti.FundamentalGroup.mapOfEq_rfl, Path.cast_rfl_rfl] using hn.symm
  have hformula (β : FundamentalGroup (Boundary g) (boundaryBase g)) :
      polygonBoundaryFundamentalGroupMulEquivSurfaceGroup g hg (polygonBoundaryClass g β) =
        q ((FundamentalGroup.fundamentalGroupMulEquivOfPath rp).symm β) := by
    change polygonFundamentalGroupMulEquivSurfaceGroup g hg
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map j.continuous)).symm
        (polygonBoundaryClass g β)) = _
    rw [hincl, polygonFundamentalGroup_inclusion, hret]
  refine ⟨(q (pathClass rp))⁻¹, ?_⟩
  intro d
  rw [hformula, FundamentalGroup.fundamentalGroupMulEquivOfPath_eq_conj,
    MulAut.conj_symm_apply]
  change q ((pathClass rp)⁻¹ * pathClass (sideLoop (HandleCW.edgeSide d)) * pathClass rp) = _
  rw [map_mul, map_mul, map_inv, boundarySurfaceHom_sideLoop]
  simp only [inv_inv]
  rfl

/-- Actual included positive polygon side loops have the required full-list
noncommutation. Inversion and the one common basepoint conjugation preserve it. -/
theorem polygon_side_ne_commute_final_b {g : ℕ} (hg : 1 < g) (d : Edge g)
    (hd : edgeLabelEquiv g d ≠ Sum.inr
      (LowDimensionalTopology.Geometry.Teichmuller.finalHandle hg)) :
    ¬Commute
      (polygonBoundaryClass g (pathClass (sideLoop (HandleCW.edgeSide d))))
      (polygonBoundaryClass g (pathClass (sideLoop
        (HandleCW.edgeSide (LowDimensionalTopology.Geometry.Teichmuller.finalHandle hg,
          (1 : Fin 2)))))) := by
  let hpos : 0 < g := by omega
  obtain ⟨c, hc⟩ := polygonBoundary_sideLoop_images_up_to_common_conjugation g hpos
  intro h
  have hm := h.map (polygonBoundaryFundamentalGroupMulEquivSurfaceGroup g hpos)
  have hb : polygonBoundaryFundamentalGroupMulEquivSurfaceGroup g hpos
      (polygonBoundaryClass g (pathClass (sideLoop
        (HandleCW.edgeSide (LowDimensionalTopology.Geometry.Teichmuller.finalHandle hg,
          (1 : Fin 2)))))) =
      c * Inv.inv (α := LiZhongQC.surfaceGroup g) (PresentedGroup.of (Sum.inr
        (LowDimensionalTopology.Geometry.Teichmuller.finalHandle hg))) * c⁻¹ := by
    simpa only [edgeLabelEquiv_b] using
      hc (LowDimensionalTopology.Geometry.Teichmuller.finalHandle hg, (1 : Fin 2))
  have hconj : Commute
      (c * Inv.inv (α := LiZhongQC.surfaceGroup g) (PresentedGroup.of (edgeLabelEquiv g d)) * c⁻¹)
      (c * Inv.inv (α := LiZhongQC.surfaceGroup g) (PresentedGroup.of (Sum.inr
        (LowDimensionalTopology.Geometry.Teichmuller.finalHandle hg))) * c⁻¹) :=
    (congrArg₂ (fun a b : LiZhongQC.surfaceGroup g => Commute a b) (hc d) hb).mp hm
  have hinv : Commute
      (Inv.inv (α := LiZhongQC.surfaceGroup g) (PresentedGroup.of (edgeLabelEquiv g d)))
      (Inv.inv (α := LiZhongQC.surfaceGroup g) (PresentedGroup.of (Sum.inr
        (LowDimensionalTopology.Geometry.Teichmuller.finalHandle hg)))) :=
    Commute.of_map (MulAut.conj c).injective hconj
  exact LowDimensionalTopology.Geometry.Teichmuller.surface_generator_ne_commute_final_b
    hg (edgeLabelEquiv g d) hd (Commute.inv_inv_iff.mp hinv)

end LowDimensionalTopology.Geometry.Surfaces.HandlePresentation
