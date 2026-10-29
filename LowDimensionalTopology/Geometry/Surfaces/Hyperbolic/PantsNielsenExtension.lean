module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HyperbolicPairOfPants
public import LowDimensionalTopology.Geometry.Fuchsian.Geodesic.AxisOrbitCurves
public import LowDimensionalTopology.Geometry.Surfaces.Topology.PairOfPantsConnectivity
public import LowDimensionalTopology.Geometry.Surfaces.Covering.DiscUniversalDeck
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The chosen-lift construction of the pants Nielsen extension and kernel

The extension uses the whole original disk with the exact subgroup stabilizing
the chosen connected lift. The kernel is its actual projected lift, identified
analytically with the same original pants in the inherited complex structures.
-/

public section
noncomputable section
open Set
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The existing pants predicate implies actual path connectedness of its open carrier. -/
theorem IsHyperbolicPairOfPants.isPathConnected {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} {M : HyperbolicSurfaceModel R} {P : Set X}
    (hP : IsHyperbolicPairOfPants M P) : IsPathConnected P := by
  obtain ⟨e⟩ := hP.2.2.1
  let : PathConnectedSpace pantsPlanarRegion :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pantsPlanarRegion
  let : PathConnectedSpace P := e.symm.pathConnectedSpace
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

private theorem discCover_component_image {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (M : HyperbolicSurfaceModel R) (P : Set X)
    (hP : IsPathConnected P) (z : M.discCover ⁻¹' P) :
    M.discCover '' connectedComponentIn (M.discCover ⁻¹' P) z.val = P := by
  let : PathConnectedSpace P := isPathConnected_iff_pathConnectedSpace.mp hP
  have hs := IsCoveringMap.comp_subtypeVal_pathComponent_surjective
    (M.discCover_covering.restrictPreimage P) z
  apply Subset.antisymm
  · rintro y ⟨u, hu, rfl⟩
    exact connectedComponentIn_subset (M.discCover ⁻¹' P) z.val hu
  · intro y hy
    obtain ⟨v, hv⟩ := hs ⟨y, hy⟩
    refine ⟨v.val.val, ?_, congrArg Subtype.val hv⟩
    rw [connectedComponentIn_eq_image z.property]
    exact ⟨v.val, pathComponent_subset_component z v.property, rfl⟩

private theorem component_translate {E : Type*} [TopologicalSpace E] (U : Set E) (x : U)
    (e : E ≃ₜ E) (hU : e '' U = U) :
    e '' connectedComponentIn U x.val = connectedComponentIn U x.val ∨
      Disjoint (e '' connectedComponentIn U x.val) (connectedComponentIn U x.val) := by
  rw [e.image_connectedComponentIn x.property, hU]
  by_cases h : connectedComponentIn U (e x.val) = connectedComponentIn U x.val
  · exact Or.inl h
  · right
    exact Set.disjoint_left.mpr fun _ h₁ h₂ =>
      h ((connectedComponentIn_eq h₁).trans (connectedComponentIn_eq h₂).symm)

variable {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
  (M : HyperbolicSurfaceModel R) (P : Set X) (z : M.discCover ⁻¹' P)
local notation "D" => unitDiscMobiusInvariantDomain M.group M.invariant
local notation "U" => M.discCover ⁻¹' P
local notation "C" => connectedComponentIn U z.val

/-- The sphere carrier of the chosen actual connected lift of P. -/
@[expose] def pantsNielsenLiftCarrier : Set ExtendedComplex := Subtype.val '' C
local notation "S" => pantsNielsenLiftCarrier M P z

/-- The selected actual lift remains inside the unchanged original disk. -/
theorem pantsNielsenLiftCarrier_subset : S ⊆ (D).carrier := by
  rintro _ ⟨u, _, rfl⟩
  exact u.property

private theorem lift_stable : MobiusStableSet M.group S := by
  intro g hg
  let a : M.group := ⟨g, hg⟩
  let e : (D).carrier ≃ₜ (D).carrier := Homeomorph.smul a
  have hp (b : M.group) (w : (D).carrier) : M.discCover (b • w) = M.discCover w := by
    change M.homeomorph.symm (mobiusDomainProjection D (b • w)) = _
    rw [mobiusDomainProjection_smul]
    rfl
  have heU : e '' U = U := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      change M.discCover (a • v) ∈ P
      rwa [hp]
    · intro hw
      refine ⟨a⁻¹ • w, ?_, by simp [e]⟩
      change M.discCover (a⁻¹ • w) ∈ P
      rwa [hp]
  have heS : g.val '' S = Subtype.val '' (e '' C) := by
    change g.val '' (Subtype.val '' C) = _
    rw [image_image, image_image]
    rfl
  rw [heS]
  rcases component_translate U z e heU with h | h
  · exact Or.inl (congrArg (fun V : Set (D).carrier => Subtype.val '' V) h)
  · exact Or.inr (Set.disjoint_image_of_injective Subtype.val_injective h)

private def originalLift : MobiusStableSubset D :=
  ⟨S, pantsNielsenLiftCarrier_subset M P z, lift_stable M P z⟩
local notation "S₀" => originalLift M P z
local notation "S₁" => stabilizerStableSubset D S (pantsNielsenLiftCarrier_subset M P z)

/-- The exact subgroup of the original group carrying the chosen lift onto itself. -/
@[expose] def pantsNielsenStabilizer : Subgroup complexMobiusGroup := mobiusSetStabilizer M.group S

/-- The unchanged whole disk acted on by the chosen lift's exact stabilizer. -/
@[expose] def pantsNielsenExtensionDomain : MobiusInvariantDomain (pantsNielsenStabilizer M P z) :=
  restrictMobiusDomain D (pantsNielsenStabilizer M P z) (mobiusSetStabilizer_le M.group S)

/-- The Nielsen extension's actual whole-disk orbit quotient. -/
abbrev PantsNielsenExtension := MobiusDomainQuotient (pantsNielsenExtensionDomain M P z)

/-- The actual image of the chosen open lift inside its whole-disk extension. -/
@[expose] def pantsNielsenKernel : Set (PantsNielsenExtension M P z) := (S₁).quotientImage

/-- The extension carries the existing genuine quotient Riemann surface. -/
def pantsNielsenExtensionRiemannSurface : RiemannSurface (PantsNielsenExtension M P z) :=
  mobiusQuotientRiemannSurface (pantsNielsenExtensionDomain M P z)
    (restrictMobiusDomain_discontinuous D (pantsNielsenStabilizer M P z)
      (mobiusSetStabilizer_le M.group S) M.discontinuous)

private theorem lift_open (hP : IsOpen P) : IsOpen S := by
  let := discRiemannSurface.toRiemannAtlas.locallyPathConnectedSpace
  exact (D).isOpen.isOpenMap_subtype_val _
    (hP.preimage M.discCover_covering.continuous).connectedComponentIn

private theorem originalLift_open (hP : IsOpen P) :
    IsOpen (Subtype.val ⁻¹' (S₀).carrier : Set (D).carrier) :=
  (lift_open M P z hP).preimage continuous_subtype_val

private theorem extensionLift_open (hP : IsOpen P) :
    IsOpen (Subtype.val ⁻¹' (S₁).carrier :
      Set (restrictMobiusDomain D (mobiusSetStabilizer M.group S)
        (mobiusSetStabilizer_le M.group S)).carrier) :=
  (lift_open M P z hP).preimage continuous_subtype_val

/-- The actual kernel is open in the whole-disk extension. -/
theorem isOpen_pantsNielsenKernel (hP : IsHyperbolicPairOfPants M P) :
    IsOpen (pantsNielsenKernel M P z) :=
  (S₁).quotientImage_isOpen (lift_open M P z hP.1)

private theorem original_image (hconn : IsPathConnected P) : (S₀).quotientImage = M.homeomorph '' P := by
  ext q
  constructor
  · rintro ⟨⟨_, ⟨u, hu, rfl⟩⟩, rfl⟩
    refine ⟨M.discCover u, connectedComponentIn_subset U z.val hu, ?_⟩
    exact M.homeomorph.apply_symm_apply _
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨u, hu, hup⟩ := (discCover_component_image M P hconn z).symm ▸ hp
    refine ⟨⟨u.val, ⟨u, hu, rfl⟩⟩, ?_⟩
    change mobiusDomainProjection D u = M.homeomorph p
    rw [← hup]
    exact (M.homeomorph.apply_symm_apply _).symm

private def liftOrbitHomeomorph : (S₀).Quotient ≃ₜ (S₁).Quotient :=
  Homeomorph.Quotient.congrRight fun _ _ => by
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨⟨g.val, ⟨g.property, g.property.2⟩⟩, hg⟩
    · rintro ⟨g, hg⟩
      exact ⟨⟨g.val, g.property.1⟩, hg⟩

private def originalImageHomeomorph (hconn : IsPathConnected P) : P ≃ₜ (S₀).quotientImage :=
  (M.homeomorph.image P).trans (Homeomorph.setCongr (original_image M P z hconn).symm)

/-- The SAME original pants is identified with the actual projected-lift kernel. -/
def pantsNielsenKernelHomeomorph (hP : IsHyperbolicPairOfPants M P)
    : P ≃ₜ pantsNielsenKernel M P z :=
  (originalImageHomeomorph M P z hP.isPathConnected).trans
    (((S₀).openQuotientHomeomorph (originalLift_open M P z hP.1)).symm.trans
      ((liftOrbitHomeomorph M P z).trans
        ((S₁).openQuotientHomeomorph (extensionLift_open M P z hP.1))))

/-- The identification commutes with the original cover and the extension's
literal projection, at every point of the SAME selected connected lift. -/
theorem pantsNielsenKernelHomeomorph_projection (hP : IsHyperbolicPairOfPants M P)
    (u : C) :
    ((pantsNielsenKernelHomeomorph M P z hP)
      ⟨M.discCover u.val, connectedComponentIn_subset U z.val u.property⟩).val =
      mobiusDomainProjection (pantsNielsenExtensionDomain M P z) u.val := by
  let s : S := ⟨u.val.val, ⟨u.val, u.property, rfl⟩⟩
  let p : P := ⟨M.discCover u.val, connectedComponentIn_subset U z.val u.property⟩
  let q₀ := (S₀).openQuotientHomeomorph (originalLift_open M P z hP.1)
  let q₁ := (S₁).openQuotientHomeomorph (extensionLift_open M P z hP.1)
  have hOld : originalImageHomeomorph M P z hP.isPathConnected p = q₀ (Quotient.mk _ s) := by
    apply Subtype.ext
    exact M.homeomorph.apply_symm_apply _
  have hcancel : q₀.symm (originalImageHomeomorph M P z hP.isPathConnected p) = Quotient.mk _ s :=
    q₀.symm_apply_eq.mpr hOld
  let F : (S₀).Quotient → PantsNielsenExtension M P z :=
    fun t => (q₁ (liftOrbitHomeomorph M P z t)).val
  have hFirst : ((pantsNielsenKernelHomeomorph M P z hP) p).val =
      F (Quotient.mk _ s) := congrArg F hcancel
  have hSecond : F (Quotient.mk _ s) =
      mobiusDomainProjection (pantsNielsenExtensionDomain M P z) u.val := by
    change (((S₁).openQuotientHomeomorph (extensionLift_open M P z hP.1))
      (Quotient.mk _ s)).val = _
    exact congrArg Subtype.val ((S₁).openQuotientHomeomorph_apply_mk
      (extensionLift_open M P z hP.1) s)
  exact Eq.trans hFirst hSecond


/-- The original pants has precisely its inherited open-subset complex atlas. -/
@[expose] def pantsOriginalRiemannSurface (hP : IsHyperbolicPairOfPants M P) : RiemannSurface P where
  toRiemannAtlas := R.toRiemannAtlas.liftLocalHomeomorph (Subtype.val : P → X)
    hP.1.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  t2Space := by
    let : T2Space X := R.t2Space
    infer_instance
  connectedSpace := Subtype.connectedSpace hP.isPathConnected.isConnected

/-- The kernel has its actual inherited atlas from the whole-disk extension. -/
@[expose] def pantsNielsenKernelRiemannSurface (hP : IsHyperbolicPairOfPants M P) :
    RiemannSurface (pantsNielsenKernel M P z) where
  toRiemannAtlas := (pantsNielsenExtensionRiemannSurface M P z).toRiemannAtlas.liftLocalHomeomorph
    (Subtype.val : pantsNielsenKernel M P z → PantsNielsenExtension M P z)
    (isOpen_pantsNielsenKernel M P z hP).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  t2Space := by
    let : T2Space (PantsNielsenExtension M P z) := (pantsNielsenExtensionRiemannSurface M P z).t2Space
    infer_instance
  connectedSpace := by
    let : ConnectedSpace P := (pantsOriginalRiemannSurface M P hP).connectedSpace
    exact (pantsNielsenKernelHomeomorph M P z hP).surjective.connectedSpace
      (pantsNielsenKernelHomeomorph M P z hP).continuous

/-- The original pants retains exactly its inherited open-subset atlas. -/
theorem pantsOriginalRiemannSurface_toRiemannAtlas
    (hP : IsHyperbolicPairOfPants M P) :
    (pantsOriginalRiemannSurface M P hP).toRiemannAtlas =
      R.toRiemannAtlas.liftLocalHomeomorph (Subtype.val : P → X)
        hP.1.isOpenEmbedding_subtypeVal.isLocalHomeomorph := rfl

/-- The original OWN kernel atlas is unchanged when its whole extension is
presented by another actual hyperbolic model of the SAME Riemann surface. -/
theorem pantsNielsenKernelRiemannSurface_eq_original
    (hP : IsHyperbolicPairOfPants M P)
    (B : HyperbolicSurfaceModel (pantsNielsenExtensionRiemannSurface M P z))
    (hC : IsHyperbolicPairOfPants B (pantsNielsenKernel M P z)) :
    pantsOriginalRiemannSurface B (pantsNielsenKernel M P z) hC =
      pantsNielsenKernelRiemannSurface M P z hP := rfl

private def pantsLiftProjection (u : C) : P :=
  ⟨M.discCover u.val, connectedComponentIn_subset U z.val u.property⟩

/-- The same-P identification is analytic in the actual inherited atlases.
Analyticity descends from the literal extension projection along the original cover. -/
theorem pantsNielsenKernelHomeomorph_analytic (hP : IsHyperbolicPairOfPants M P) :
    RiemannAnalyticMap (pantsOriginalRiemannSurface M P hP).toRiemannAtlas
      (pantsNielsenKernelRiemannSurface M P z hP).toRiemannAtlas
      (pantsNielsenKernelHomeomorph M P z hP) := by
  let := discRiemannSurface.toRiemannAtlas.locallyPathConnectedSpace
  have hC : IsOpen C := (hP.1.preimage M.discCover_covering.continuous).connectedComponentIn
  let A := discRiemannSurface.toRiemannAtlas.liftLocalHomeomorph
    (Subtype.val : C → extendedUnitDisc) hC.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  let p := pantsLiftProjection M P z
  let f := pantsNielsenKernelHomeomorph M P z hP
  have hc : Continuous p :=
    (M.discCover_covering.continuous.comp continuous_subtype_val).subtype_mk _
  have hp : RiemannAnalyticMap A (pantsOriginalRiemannSurface M P hP).toRiemannAtlas p :=
    RiemannAnalyticMap.liftLocalHomeomorph
      (Subtype.val : C → extendedUnitDisc) (Subtype.val : P → X)
      hC.isOpenEmbedding_subtypeVal.isLocalHomeomorph
      hP.1.isOpenEmbedding_subtypeVal.isLocalHomeomorph M.discCover p M.discCover_analytic hc (fun _ => rfl)
  have hpl : IsLocalHomeomorph p := IsLocalHomeomorph.of_comp
    (f := p) (g := (Subtype.val : P → X))
    (M.discCover_covering.isLocalHomeomorph.comp hC.isOpenEmbedding_subtypeVal.isLocalHomeomorph)
    hP.1.isOpenEmbedding_subtypeVal.isLocalHomeomorph hc
  have hps : Function.Surjective p := by
    intro a
    have ha : (a : X) ∈ M.discCover '' C := by
      rw [discCover_component_image M P hP.isPathConnected z]
      exact a.property
    obtain ⟨u, hu, hua⟩ := ha
    exact ⟨⟨u, hu⟩, Subtype.ext hua⟩
  have hF : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas
      (pantsNielsenExtensionRiemannSurface M P z).toRiemannAtlas
      (mobiusDomainProjection (pantsNielsenExtensionDomain M P z)) :=
    mobiusDomainProjection_analytic (pantsNielsenExtensionDomain M P z)
      (restrictMobiusDomain_discontinuous D (pantsNielsenStabilizer M P z)
        (mobiusSetStabilizer_le M.group S) M.discontinuous)
  have hcomp : RiemannAnalyticMap A (pantsNielsenKernelRiemannSurface M P z hP).toRiemannAtlas
      (f ∘ p) := RiemannAnalyticMap.liftLocalHomeomorph
    (Subtype.val : C → extendedUnitDisc)
    (Subtype.val : pantsNielsenKernel M P z → PantsNielsenExtension M P z)
    hC.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    (isOpen_pantsNielsenKernel M P z hP).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    (mobiusDomainProjection (pantsNielsenExtensionDomain M P z)) (f ∘ p) hF
    (f.continuous.comp hc) (fun u => pantsNielsenKernelHomeomorph_projection M P z hP u)
  exact RiemannAnalyticMap.of_comp_surjective_localHomeomorph hp hpl hps f.continuous hcomp

/-- The inverse is analytic in the same inherited complex structures. -/
theorem pantsNielsenKernelHomeomorph_symm_analytic (hP : IsHyperbolicPairOfPants M P) :
    RiemannAnalyticMap (pantsNielsenKernelRiemannSurface M P z hP).toRiemannAtlas
      (pantsOriginalRiemannSurface M P hP).toRiemannAtlas
      (pantsNielsenKernelHomeomorph M P z hP).symm :=
  riemannAnalyticMap_homeomorph_symm (pantsNielsenKernelHomeomorph M P z hP)
    (pantsNielsenKernelHomeomorph_analytic M P z hP)

/-- The actual original pants and its actual Nielsen kernel are conformally equivalent. -/
theorem pantsNielsenKernel_conformallyEquivalent (hP : IsHyperbolicPairOfPants M P) :
    RiemannConformallyEquivalent (pantsOriginalRiemannSurface M P hP)
      (pantsNielsenKernelRiemannSurface M P z hP) :=
  ⟨pantsNielsenKernelHomeomorph M P z hP, pantsNielsenKernelHomeomorph_analytic M P z hP,
    (pantsNielsenKernelHomeomorph M P z hP).bijective⟩

/-- The same original pants embeds as an open subsurface of the extension. -/
theorem pantsNielsenKernelHomeomorph_isOpenEmbedding (hP : IsHyperbolicPairOfPants M P) :
    Topology.IsOpenEmbedding (fun p : P => (pantsNielsenKernelHomeomorph M P z hP p).val) :=
  (isOpen_pantsNielsenKernel M P z hP).isOpenEmbedding_subtypeVal.comp
    (pantsNielsenKernelHomeomorph M P z hP).isOpenEmbedding

end LowDimensionalTopology.Geometry.Surfaces
