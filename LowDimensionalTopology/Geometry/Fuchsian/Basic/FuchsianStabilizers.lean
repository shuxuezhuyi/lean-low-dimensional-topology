/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscCyclicGroups
public import LowDimensionalTopology.Geometry.Surfaces.Quotient.Mobius
public import LowDimensionalTopology.Geometry.Mobius.InvariantDisc.InvariantDiscConverse
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteDilationGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenAxes
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.LimitSets
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteTranslationGroups
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- An invariant genuine disc with the actual compact-hit condition, rather than a separate abstract action. -/
structure FuchsianDisc (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) where
  carrier : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
  isDisc : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc carrier
  invariant : ∀ (g : H) z, z ∈ carrier → g • z ∈ carrier
  discontinuous : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H carrier

theorem fuchsianDisc_exists_iff (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    Nonempty (FuchsianDisc H) ↔ _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup H := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.carrier, D.isDisc, D.invariant, D.discontinuous⟩
  · rintro ⟨D, hD, hi, hd⟩
    exact ⟨⟨D, hD, hi, hd⟩⟩

theorem FuchsianDisc.discrete {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) :
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_invariant_discrete H D.carrier D.invariant
    D.isDisc.isConnected.nonempty D.discontinuous

theorem FuchsianDisc.image_eq {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) (g : H) :
    g.val.val '' D.carrier = D.carrier := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact D.invariant g z hz
  · intro z hz
    exact ⟨g⁻¹ • z, D.invariant g⁻¹ z hz, smul_inv_smul g z⟩

/-- Every subgroup retains the original discrete topology inherited from the actual Mobius group. -/
theorem discreteMobius_subgroup_of_le (H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hle : K ≤
      H) : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K :=
  isDiscrete_iff_discreteTopology.mp ((isDiscrete_iff_discreteTopology.mpr hd).mono hle)

/-- In a genuine invariant disc, every loxodromic element is hyperbolic. -/
theorem FuchsianDisc.loxodromic_hyperbolic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (g : H) (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic
      g.val) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val :=
  ⟨hg, D.carrier, D.isDisc, D.image_eq g⟩

/-- The non-elementary limit-set definition of lies on the actual invariant circle. -/
theorem FuchsianDisc.loxodromic_limit_subset_frontier {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H ⊆ frontier D.carrier := by
  apply closure_minimal _ isClosed_frontier
  rintro z ⟨g, hg, hz⟩
  exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier g.val (D.loxodromic_hyperbolic g hg)
    D.isDisc (D.image_eq g) hz

/-- Any subgroup fixing a point off the invariant circle consists of elliptics and the identity. -/
theorem invariantDisc_off_frontier_all_elliptic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    {D : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (hp : ∀ f : H, f.val.val '' D = D) (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hw : w ∉
      frontier D)
    (hfix : ∀ f ∈ H, f.val w = w) : ∀ f ∈ H, f ≠ 1 → _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f := by
  intro f hf hn
  rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy f hn with hpa | hl | he
  · exact False.elim (hw (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_fixed_mem_disc_frontier f hpa hD
    (hp ⟨f, hf⟩) (hfix f hf)))
  · exact False.elim (hw (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier f
      ⟨hl, D, hD, hp ⟨f, hf⟩⟩ hD (hp ⟨f, hf⟩) (hfix f hf)))
  · exact he

/-- The off-circle stabilizer conclusion is finite cyclic, including points in either complementary disc. -/
theorem discrete_invariantDisc_off_frontier_cyclic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) {D : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (hp : ∀ f : H, f.val.val '' D = D) (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hw : w ∉
      frontier D)
    (hfix : ∀ f ∈ H, f.val w = w) : Finite H ∧ IsCyclic H := by
  obtain ⟨q, hq⟩ := (_root_.LowDimensionalTopology.Geometry.Mobius.all_nonidentity_elliptic_iff_common_halfSpace_fixedPoint H).mp
    (invariantDisc_off_frontier_all_elliptic H hD hp w hw hfix)
  let : Finite H := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_finite_of_common_H3_fixed H hd q hq
  exact ⟨inferInstance, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.finiteMobius_fix_boundary_isCyclic H w
    hfix⟩

/-- Actual translations along one real line form a cyclic group whenever their Mobius subgroup is discrete. -/
theorem discrete_real_translations_isCyclic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hT : ∀ f ∈ H, ∃ r : ℝ, f = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (r : ℂ)) : IsCyclic H := by
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_real_translations_isCyclic H hd hT

/-- Without nonidentity elliptics, the logarithmic modulus embeds a discrete endpoint-fixing group in a cyclic real subgroup. -/
theorem discrete_dilation_no_elliptics_isCyclic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer)
    (hz : ∀ f ∈ H, f.val (0 : ℂ) = (0 : ℂ))
    (hno : ∀ f ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) : IsCyclic H := by
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_dilation_no_elliptics_isCyclic H hd hi hz hno

/-- With a common boundary fixed point, a loxodromic element forces the other endpoint to be fixed as well. -/
theorem discrete_loxodromic_common_fixed_cyclic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hfix : ∀ f ∈ H, f.val w = w) (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hgH : g ∈ H)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic g) (hno : ∀ f ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) : IsCyclic H := by
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_loxodromic_common_fixed_cyclic H hd w hfix g hgH hg hno

/-- Genuine common invariant discs survive arbitrary actual subgroup conjugation. -/
theorem invariantDisc_conjugate (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (h :
      _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H) :
    _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.invariantDisc_conjugate H q h

theorem fuchsian_unitTranslation_eq_standard : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement 1 := by
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.fuchsian_unitTranslation_eq_standard

theorem fuchsian_standardTranslation_fixed (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hz : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement 1).val z = z) : z = ∞ := by
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.fuchsian_standardTranslation_fixed z hz

/-- A parabolic-containing discrete disc group with a common fixed point and no elliptics is cyclic. -/
theorem discrete_parabolic_common_fixed_cyclic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H)
    (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfix : ∀ f ∈ H, f.val w = w)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hpH : p ∈ H) (hp :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic p)
    (hno : ∀ f ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) : IsCyclic H := by
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_parabolic_common_fixed_cyclic H hd hD w hfix p hpH hp hno

/-- The actual stabilizer of every extended-plane point is cyclic. -/
theorem FuchsianDisc.stabilizer_isCyclic {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : IsCyclic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H w) := by
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H w
  have hle : K ≤ H := fun f hf => ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H
    w f).mp hf).1
  have hfix : ∀ f ∈ K, f.val w = w :=
    fun f hf => ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H w f).mp hf).2
  have hkd := discreteMobius_subgroup_of_le H K D.discrete hle
  have hp : ∀ f : K, f.val.val '' D.carrier = D.carrier :=
    fun f => D.image_eq ⟨f.val, hle f.property⟩
  by_cases hw : w ∈ frontier D.carrier
  · have hno : ∀ f ∈ K, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f := by
      intro f hf he
      exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_fixed_not_mem_disc_frontier f he D.isDisc (hp
        ⟨f, hf⟩) (hfix f hf) hw
    by_cases hP : ∃ p ∈ K, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic p
    · obtain ⟨p, hpK, hpP⟩ := hP
      exact discrete_parabolic_common_fixed_cyclic K hkd ⟨D.carrier, D.isDisc, hp⟩ w hfix p hpK hpP hno
    by_cases hL : ∃ f ∈ K, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic f
    · obtain ⟨f, hfK, hfL⟩ := hL
      exact discrete_loxodromic_common_fixed_cyclic K hkd w hfix f hfK hfL hno
    have hone : ∀ f : K, f = 1 := by
      intro f
      by_contra hn
      have hfn : f.val ≠ 1 := fun he => hn (Subtype.ext he)
      rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy f.val hfn with hp | hl | he
      · exact hP ⟨f.val, f.property, hp⟩
      · exact hL ⟨f.val, f.property, hl⟩
      · exact hno f.val f.property he
    let : Subsingleton K := ⟨fun a b => (hone a).trans (hone b).symm⟩
    infer_instance
  · exact (discrete_invariantDisc_off_frontier_cyclic K hkd D.isDisc hp w hw hfix).2

/-- With exactly the original Fuchsian-group hypothesis and every sphere point. -/
theorem boundary_stabilizer_cyclic_of_fuchsian (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hH :
  _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup H)
    (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : IsCyclic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H w) := by
  obtain ⟨D, hD, hi, hd⟩ := hH
  exact (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.mk D hD hi hd).stabilizer_isCyclic w

end LowDimensionalTopology.Geometry.Fuchsian
