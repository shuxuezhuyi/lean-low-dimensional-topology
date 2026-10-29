module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.AbelianHyperbolicSurfaceModels
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.CyclicHyperbolicAnnulus
public import LowDimensionalTopology.Geometry.Surfaces.Cusp.GeneralParabolicCusps
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannSphereTopology
public import LowDimensionalTopology.Geometry.Surfaces.Topology.RadialDomainFundamentalGroups

/-!
# The seven conformal types with abelian fundamental group

The classification concerns an arbitrary original Riemann surface and its
actual based fundamental group. The plane/sphere cases reuse the proved
uniformization classification. In the hyperbolic case, the genuine quotient
group is derived to be cyclic, then its trivial, parabolic, and hyperbolic
alternatives give the ordinary disc, punctured disc, and finite round annulus.
The converse computes the actual fundamental groups of these ordinary models.
-/

public section
noncomputable section

open Set Topology

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry
open Hyperbolic Mobius Fuchsian DiscreteGroups DiscreteGroups.Action Module

/-- The whole actual invariant domain is a stable subset of itself. -/
private def wholeDomainStableSubset {H : Subgroup Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) : MobiusStableSubset D where
  carrier := D.carrier
  subset_domain := Subset.rfl
  stable := by
    intro g hg
    left
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact D.invariant ⟨g, hg⟩ z hz
    · intro z hz
      exact ⟨g⁻¹ • z, D.invariant ⟨g⁻¹, H.inv_mem hg⟩ z hz, smul_inv_smul g z⟩

private theorem wholeDomainStableSubset_stabilizer
    {H : Subgroup Mobius.complexMobiusGroup} (D : MobiusInvariantDomain H) :
    (wholeDomainStableSubset D).stabilizer = H := by
  apply le_antisymm
  · exact (wholeDomainStableSubset D).stabilizer_le
  · intro g hg
    exact ⟨hg, ((wholeDomainStableSubset D).stable g hg).resolve_right (by
      intro hd
      obtain ⟨z, hz⟩ := D.isConnected.nonempty
      have hi := D.invariant ⟨g⁻¹, H.inv_mem hg⟩ z hz
      exact Set.disjoint_left.mp hd ⟨g⁻¹ • z, hi, smul_inv_smul g z⟩ hz)⟩

/-- The whole-domain image is the original full quotient, analytically in
its existing atlas, through the actual inclusion. -/
private theorem wholeDomainStableSubset_image_conformallyEquivalent
    {H : Subgroup Mobius.complexMobiusGroup} (D : MobiusInvariantDomain H)
    (hD : IsMobiusDiscontinuousOn H D.carrier)
    (ho : IsOpen (wholeDomainStableSubset D).carrier)
    (hc : IsConnected (wholeDomainStableSubset D).carrier) :
    RiemannConformallyEquivalent
      ((wholeDomainStableSubset D).openImageRiemannSurface hD ho hc)
      (mobiusQuotientRiemannSurface D hD) := by
  let S := wholeDomainStableSubset D
  refine ⟨Subtype.val, ?_, Subtype.val_injective, ?_⟩
  · exact RiemannAtlas.liftLocalHomeomorph_projection_analytic
      (mobiusQuotientRiemannSurface D hD).toRiemannAtlas Subtype.val
        (S.quotientImage_isOpen ho).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  · intro q
    obtain ⟨z, hz⟩ := mobiusDomainProjection_surjective D q
    exact ⟨⟨q, ⟨z, hz⟩⟩, rfl⟩

/-- A whole original parabolic cyclic quotient is biholomorphic to the
ordinary unit punctured disc; the full quotient atlas is retained. -/
theorem parabolic_cyclic_domain_conformallyEquivalent_unit_punctured_disc
    {H : Subgroup Mobius.complexMobiusGroup} (D : MobiusInvariantDomain H)
    (hD : IsMobiusDiscontinuousOn H D.carrier) (f : Mobius.complexMobiusGroup)
    (hf : Mobius.MobiusParabolic f) (hdisc : Mobius.IsComplexOpenDisc D.carrier)
    (hgroup : H = Subgroup.zpowers f) :
    RiemannConformallyEquivalent (mobiusQuotientRiemannSurface D hD)
      (stableCuspPuncturedDiscRiemannSurface 0) := by
  let S := wholeDomainStableSubset D
  have hS : S.stabilizer = Subgroup.zpowers f :=
    (wholeDomainStableSubset_stabilizer D).trans hgroup
  obtain ⟨ho, hc, he⟩ := parabolic_stable_disc_quotient_conformal_unit_punctured_disc
    S hD f hf hdisc hS
  exact (wholeDomainStableSubset_image_conformallyEquivalent D hD ho hc).symm.trans he

private theorem cyclic_subgroup_eq_zpowers {G : Type*} [Group G]
    (H : Subgroup G) (hH : IsCyclic H) : ∃ f : H, H = Subgroup.zpowers f.val := by
  obtain ⟨f, hf⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := H)).mp hH
  refine ⟨f, le_antisymm ?_ (Subgroup.zpowers_le.mpr f.property)⟩
  intro g hg
  have hg' : (⟨g, hg⟩ : H) ∈ Subgroup.zpowers f := by rw [hf]; trivial
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg'
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
    simpa only [Subgroup.coe_zpow] using congrArg (fun h : H => h.val) hn⟩

/-- An arbitrary hyperbolic-type original surface with abelian fundamental
group has one of the three ordinary cyclic conformal model types.
No compactness, genus, supplied generator, or matrix-sign lift is assumed. -/
theorem IsHyperbolicType.cyclic_conformal_trichotomy_of_fundamentalGroup_commute
    {X : Type*} [TopologicalSpace X] (R : RiemannSurface X)
    (hR : IsHyperbolicType R) (x : X)
    (hcomm : ∀ a b : FundamentalGroup X x, Commute a b) :
    RiemannConformallyEquivalent R discRiemannSurface ∨
      RiemannConformallyEquivalent R (stableCuspPuncturedDiscRiemannSurface 0) ∨
      ∃ (r : ℝ) (hr : 1 < r), RiemannConformallyEquivalent R (roundAnnulusSurface r hr) := by
  obtain ⟨H, hInv, hD, hno, hcyc, hmodel⟩ :=
    IsHyperbolicType.exists_cyclic_quotient_of_fundamentalGroup_commute R hR x hcomm
  let D := unitDiscMobiusInvariantDomain H hInv
  obtain ⟨f, hf⟩ := cyclic_subgroup_eq_zpowers H hcyc
  by_cases hf1 : f.val = 1
  · left
    have hH : H = ⊥ := hf.trans (by rw [hf1]; exact Subgroup.zpowers_one_eq_bot)
    exact hmodel.trans (mobius_trivialQuotient_conformallyEquivalent_domain H hH D hD)
  · have P : FuchsianDisc H :=
      ⟨extendedUnitDisc, extendedUnitDisc_isComplexOpenDisc, hInv, hD⟩
    rcases mobius_nonidentity_type_trichotomy f.val hf1 with hpar | hlox | hell
    · right
      left
      exact hmodel.trans (parabolic_cyclic_domain_conformallyEquivalent_unit_punctured_disc
        D hD f.val hpar extendedUnitDisc_isComplexOpenDisc hf)
    · right
      right
      obtain ⟨F, hF, hbij⟩ := hmodel
      let M : HyperbolicSurfaceModel R :=
        ⟨H, hInv, hD, hno, hF.toHomeomorph hbij, hF⟩
      obtain ⟨A, B, lam, hlam, e, _hA, he, _hlength, _hcoordinate⟩ :=
        M.annulusHomeomorph_of_hyperbolic_cyclic_group f.val (P.loxodromic_hyperbolic f hlox) hf
      exact ⟨dilationAnnulusRadius lam, dilationAnnulusRadius_one_lt hlam, e, he, e.bijective⟩
    · exact (hno f.val f.property hf1 hell).elim

/-- These are the seven genuine conformal types: sphere, plane, punctured
plane, arbitrary period-lattice torus, disc, punctured disc, and round annulus. -/
def RiemannSurface.HasAbelianConformalModel {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) : Prop :=
  RiemannConformallyEquivalent R sphereRiemannSurface ∨
    RiemannConformallyEquivalent R complexPlaneRiemannSurface ∨
    RiemannConformallyEquivalent R puncturedPlaneRiemannSurface ∨
    (∃ b : Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b,
      RiemannConformallyEquivalent R T.surface) ∨
    RiemannConformallyEquivalent R discRiemannSurface ∨
    RiemannConformallyEquivalent R (stableCuspPuncturedDiscRiemannSurface 0) ∨
    ∃ (r : ℝ) (hr : 1 < r), RiemannConformallyEquivalent R (roundAnnulusSurface r hr)

/-- The full seven-type forward classification, on the original surface and atlas. -/
theorem RiemannSurface.hasAbelianConformalModel_of_fundamentalGroup_commute
    {X : Type*} [TopologicalSpace X] (R : RiemannSurface X) (x : X)
    (hcomm : ∀ a b : FundamentalGroup X x, Commute a b) : R.HasAbelianConformalModel := by
  rcases riemannSurface_conformal_classification R with hs | hp | hpun | ht | hh
  · exact Or.inl hs
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl hpun))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ht)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (IsHyperbolicType.cyclic_conformal_trichotomy_of_fundamentalGroup_commute R hh x hcomm))))

/-- Forgetting only the nested subtype wrappers identifies the ordinary unit
punctured-disc carrier with its literal circular band. -/
private def unitPuncturedDiscBandHomeomorph : stableCuspPuncturedDisc 0 ≃ₜ
    {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} where
  toFun z := ⟨z.val.val, norm_pos_iff.mpr z.val.property,
    by
      have hz : ‖z.val.val‖ < stableCuspRadius 0 := z.property
      simpa only [stableCuspRadius_zero] using hz⟩
  invFun z := ⟨⟨z.val, norm_pos_iff.mp z.property.1⟩,
    by
      change ‖z.val‖ < stableCuspRadius 0
      rw [stableCuspRadius_zero]
      exact z.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem fundamentalGroup_commute_of_conformallyEquivalent
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y} (h : RiemannConformallyEquivalent R S)
    (hcomm : ∀ y, ∀ a b : FundamentalGroup Y y, Commute a b)
    (x : X) (a b : FundamentalGroup X x) : Commute a b := by
  obtain ⟨f, hf, hbij⟩ := h
  let E := hf.toHomeomorph hbij
  let j := fundamentalGroupHomeomorphMulEquiv E x
  exact Commute.of_map j.injective (hcomm (E x) (j a) (j b))

private theorem simplyConnected_fundamentalGroup_commute
    {Y : Type*} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (y : Y) (a b : FundamentalGroup Y y) : Commute a b :=
  show a * b = b * a from Subsingleton.elim _ _

/-- Every one of the seven genuine conformal models has abelian actual
fundamental group, at any original basepoint. -/
theorem RiemannSurface.HasAbelianConformalModel.fundamentalGroup_commute
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (hR : R.HasAbelianConformalModel) (x : X) (a b : FundamentalGroup X x) : Commute a b := by
  rcases hR with hs | hp | hpun | ht | hd | hpd | hann
  · let := riemannSphere_simplyConnected
    exact fundamentalGroup_commute_of_conformallyEquivalent hs
      simplyConnected_fundamentalGroup_commute x a b
  · exact fundamentalGroup_commute_of_conformallyEquivalent hp
      simplyConnected_fundamentalGroup_commute x a b
  · exact fundamentalGroup_commute_of_conformallyEquivalent hpun
      puncturedPlaneFundamentalGroup_commute x a b
  · obtain ⟨basis, T, he⟩ := ht
    exact fundamentalGroup_commute_of_conformallyEquivalent he
      torusProductFundamentalGroup_commute x a b
  · let := discRiemannSurface_simplyConnected
    exact fundamentalGroup_commute_of_conformallyEquivalent hd
      simplyConnected_fundamentalGroup_commute x a b
  · apply fundamentalGroup_commute_of_conformallyEquivalent hpd _ x a b
    intro y c d
    let E := unitPuncturedDiscBandHomeomorph
    let j := fundamentalGroupHomeomorphMulEquiv E y
    exact Commute.of_map j.injective
      (circularBandFundamentalGroup_commute 0 1 le_rfl zero_lt_one (E y) (j c) (j d))
  · obtain ⟨r, hr, he⟩ := hann
    exact fundamentalGroup_commute_of_conformallyEquivalent he
      (circularBandFundamentalGroup_commute 1 r zero_le_one hr) x a b

/-- An arbitrary original Riemann surface has abelian fundamental group if
and only if it has one of the seven literal conformal types. -/
theorem RiemannSurface.fundamentalGroup_commute_iff_seven_conformal_types
    {X : Type*} [TopologicalSpace X] (R : RiemannSurface X) (x : X) :
    (∀ a b : FundamentalGroup X x, Commute a b) ↔ R.HasAbelianConformalModel :=
  ⟨R.hasAbelianConformalModel_of_fundamentalGroup_commute x,
    fun h => h.fundamentalGroup_commute x⟩

end LowDimensionalTopology.Geometry.Surfaces
