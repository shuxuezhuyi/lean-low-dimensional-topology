module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Surfaces.Cusp.GeneralParabolicCusps
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology TopologicalSpace
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Cross-cusp Shimizu only needs the conjugate parabolic to belong to the group. -/
theorem multipleCusp_shimizu_cross (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (hBT :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection (B *
      _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift * B⁻¹) ∈ G)
    (hc : B 1 0 ≠ 0) : 1 ≤ ‖B 1 0‖ := by
  have hs : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenStep _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift B 1 0 ≠ 0 := by
    rw [(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenStep_parabolic B).2.2.1]
    exact neg_ne_zero.mpr (pow_ne_zero 2 hc)
  have hh := stableCuspShimizu_lowerLeft G hd hT (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenStep
    _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift B) hBT hs
  rw [(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenStep_parabolic B).2.2.1, norm_neg, norm_pow] at hh
  nlinarith [norm_nonneg (B 1 0)]

/-- The actual change between two original cusp normalization coordinates. -/
def multipleCuspChange {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    {S T : MobiusStableSubset D} {w v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (E : MobiusCuspNormalization T v) (g :
      G) : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  C.normalizer * g.val * E.normalizer⁻¹

theorem multipleCuspChange_infty {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    {S T : MobiusStableSubset D} {w v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (E : MobiusCuspNormalization T v) (g : G) :
    (multipleCuspChange C E g).val ∞ = C.normalizer.val (g.val.val v) := by
  change C.normalizer • (g.val • (E.normalizer⁻¹ • (∞ :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))) = _
  exact congrArg (fun p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex => C.normalizer • (g.val •
    p)) E.inverse_cusp

theorem multipleCuspChange_infty_iff {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D
  : MobiusInvariantDomain G}
    {S T : MobiusStableSubset D} {w v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (E : MobiusCuspNormalization T v) (g : G) :
    (multipleCuspChange C E g).val ∞ = ∞ ↔ g.val.val v = w := by
  rw [multipleCuspChange_infty, ← C.cusp_eq]
  exact C.normalizer.val.injective.eq_iff

theorem multipleCuspChange_parabolic_mem {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    {S T : MobiusStableSubset D} {w v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (E : MobiusCuspNormalization T v) (g : G) :
    multipleCuspChange C E g * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 * (multipleCuspChange C E g)⁻¹ ∈
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer G := by
  obtain ⟨k, hk, hkT⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
    E.normalizer G _).mp E.normalized_translation_mem
  apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff C.normalizer G
    _).mpr
  refine ⟨g.val * k * g.val⁻¹, G.mul_mem (G.mul_mem g.property hk) (G.inv_mem g.property), ?_⟩
  rw [← hkT]
  dsimp [multipleCuspChange]
  group

theorem multipleCuspChange_maps_domain {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    {S T : MobiusStableSubset D} {w v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (E : MobiusCuspNormalization T v) (g : G)
    {z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hz : z ∈ (D.conjugate E.normalizer).carrier) :
    (multipleCuspChange C E g).val z ∈ (D.conjugate C.normalizer).carrier := by
  obtain ⟨a, ha, rfl⟩ := hz
  refine ⟨g.val.val a, D.invariant g a ha, ?_⟩
  change C.normalizer • (g.val • a) =
    (C.normalizer * g.val * E.normalizer⁻¹) • (E.normalizer • a)
  simp only [mul_smul, inv_smul_smul]

/-- Distinct actual cusp orbits force a uniformly nonzero cross-matrix coefficient. -/
theorem multipleCuspChange_lowerLeft {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D
  : MobiusInvariantDomain G}
    {S T : MobiusStableSubset D} {w v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (E : MobiusCuspNormalization T v)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hne :
      ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex w v)
    (g : G) (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B = multipleCuspChange C E g) :
    1 ≤ ‖B 1 0‖ := by
  have hDi := D.conjugate_discontinuous C.normalizer hD
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer G) :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_invariant_discrete _ _ (D.conjugate
      C.normalizer).invariant
      (D.conjugate C.normalizer).isConnected.nonempty hDi
  have hc : B 1 0 ≠ 0 := by
    intro hz
    have hi : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B).val ∞ = ∞ := by
      rw [_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
        _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_infty]
      exact ite_eq_left hz
    rw [hB] at hi
    exact hne ⟨g, (multipleCuspChange_infty_iff C E g).mp hi⟩
  apply multipleCusp_shimizu_cross _ hd C.normalized_translation_mem B _ hc
  rw [map_mul, map_mul, map_inv, stableCuspShimizu_translation_projection, hB]
  exact multipleCuspChange_parabolic_mem C E g

/-- The image of the other cusp is outside the original normalized domain. -/
theorem multipleCuspChange_infty_not_mem {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    {S T : MobiusStableSubset D} {w v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (E : MobiusCuspNormalization T v)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (g : G) :
    (multipleCuspChange C E g).val ∞ ∉ (D.conjugate C.normalizer).carrier := by
  rw [multipleCuspChange_infty]
  rintro ⟨a, ha, he⟩
  exact E.orbit_cusp_not_mem hD g (C.normalizer.val.injective he ▸ ha)

/-- Both finite endpoints of a cross-cusp matrix lie below the relevant cusp discs. -/
theorem multipleCuspChange_matrix_ends_below {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    {S T : MobiusStableSubset D} {w v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (E : MobiusCuspNormalization T v)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hne :
      ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex w v)
    (g : G) (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B = multipleCuspChange C E g) :
    (B 0 0 / B 1 0).im ≤ C.height ∧ (-(B 1 1) / B 1 0).im ≤ E.height := by
  have hcn := multipleCuspChange_lowerLeft C E hD hne g B hB
  have hc : B 1 0 ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hcn)
  constructor
  · by_contra! hz
    have hm : ((B 0 0 / B 1 0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ (D.conjugate
      C.normalizer).carrier :=
      (S.conjugate C.normalizer).subset_domain
        (by rw [C.normalized_disc_eq]; exact ⟨_, hz, rfl⟩)
    have hf : (multipleCuspChange C E g).val ∞ = ((B 0 0 / B 1 0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
      rw [← hB, _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
        _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_infty]
      exact ite_eq_right hc
    exact multipleCuspChange_infty_not_mem C E hD g (hf.symm ▸ hm)
  · by_contra! hz
    have hm : ((-(B 1 1) / B 1 0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ (D.conjugate
      E.normalizer).carrier :=
      (T.conjugate E.normalizer).subset_domain
        (by rw [E.normalized_disc_eq]; exact ⟨_, hz, rfl⟩)
    have hf : (multipleCuspChange C E g).val ((-(B 1 1) / B 1 0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ∞ := by
      rw [← hB, _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
        _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe]
      exact ite_eq_left ((_root_.LowDimensionalTopology.Geometry.Mobius.denominator_eq_zero_iff _ _ _ hc).mpr rfl)
    have hi : (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∉ (D.conjugate
      C.normalizer).carrier :=
      stableCusp_orbit_infty_not_mem _ (D.conjugate C.normalizer)
        (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem 1
    exact hi (hf ▸ multipleCuspChange_maps_domain C E g hm)

/-- A genuine original finite cusp tail, expressed as a subset of the actual sphere. -/
def MobiusCuspNormalization.finiteTail {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (t : ℝ) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  C.normalizer.val ⁻¹' stableCuspSphere t

/-- Uniform separation of every translate of two distinct cusp-orbit tails.
No simultaneous-end separation assumption is added: it follows from cross-cusp Shimizu. -/
theorem multipleCusp_finiteTails_disjoint {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    {S T : MobiusStableSubset D} {w v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (E : MobiusCuspNormalization T v)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hne :
      ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex w v)
    (g : G) :
    Disjoint (C.finiteTail (C.height + 1)) (g.val.val '' E.finiteTail (E.height + 1)) := by
  apply Set.disjoint_left.mpr
  intro p hp hgp
  obtain ⟨a, ha, hap⟩ := hp
  obtain ⟨b, hb, hbp⟩ := hgp
  obtain ⟨z, hz, hzb⟩ := hb
  obtain ⟨B, hB⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection_surjective (multipleCuspChange C E g)
  have hcn := multipleCuspChange_lowerLeft C E hD hne g B hB
  obtain ⟨hcenter, hpole⟩ := multipleCuspChange_matrix_ends_below C E hD hne g B hB
  obtain ⟨hden, hdist⟩ := stableCusp_matrix_distance B E.height (E.height + 1) z hcn (lt_add_one _) hz hpole
  have hdist' : dist ((B 0 0 * z + B 0 1) / (B 1 0 * z + B 1 1)) (B 0 0 / B 1 0) < 1 := by
    simpa only [add_sub_cancel_left, inv_one] using hdist
  have he : (multipleCuspChange C E g).val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rw [hzb]
    change C.normalizer • (g.val • (E.normalizer⁻¹ • (E.normalizer • b))) = _
    rw [inv_smul_smul]
    exact (congrArg C.normalizer.val hbp).trans hap.symm
  have hf : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B).val (z :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      (((B 0 0 * z + B 0 1) / (B 1 0 * z + B 1 1) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
      _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe]
    exact ite_eq_right hden
  have hza : (B 0 0 * z + B 0 1) / (B 1 0 * z + B 1 1) = a :=
    OnePoint.coe_injective (hf.symm.trans ((congrArg (fun f :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => f.val (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) hB).trans he))
  rw [hza] at hdist'
  have him : a.im - (B 0 0 / B 1 0).im ≤ dist a (B 0 0 / B 1 0) := by
    rw [dist_eq_norm, ← Complex.sub_im]
    exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
  change C.height + 1 < a.im at ha
  linarith


/-- Different cusp-orbit representatives have disjoint actual full-group orbits. -/
theorem multipleCusp_orbit_points_ne {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {w
  v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (hne : ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex w v) (g k : G) : g.val.val w ≠ k.val.val v := by
  intro he
  apply hne
  refine ⟨g⁻¹ * k, ?_⟩
  change (g⁻¹ * k) • v = w
  rw [mul_smul]
  have hh : g • w = k • v := he
  rw [← hh, inv_smul_smul]

/-- The literal sphere domain obtained by adjoining all specified actual cusp orbits. -/
def MultipleCuspAugmentedDomain {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (_C : ∀ i, MobiusCuspNormalization (S i) (w i)) :=
  {p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex // p ∈ D.carrier ∨ ∃ (i : ι) (g : G), g.val.val (w
    i) = p}

def multipleCuspAugmentedSphere {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w
      i)) : MultipleCuspAugmentedDomain C → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := Subtype.val

def multipleCuspAugmentedOld {ι : Type*} {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) : D.carrier → MultipleCuspAugmentedDomain C :=
  fun p => ⟨p.val, Or.inl p.property⟩

/-- Every original one-orbit augmented domain is included without changing sphere coordinates. -/
def multipleCuspAugmentedPiece {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) :
    MobiusCuspAugmentedDomain (S i) (w i) (C i) → MultipleCuspAugmentedDomain C :=
  fun p => ⟨p.val, p.property.imp id (fun ⟨g, hg⟩ => ⟨i, g, hg⟩)⟩

instance multipleCuspAugmentedTopology {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) : TopologicalSpace (MultipleCuspAugmentedDomain C) :=
  TopologicalSpace.coinduced (multipleCuspAugmentedOld C) inferInstance ⊔
    ⨆ i : ι, TopologicalSpace.coinduced (multipleCuspAugmentedPiece C i) inferInstance

theorem multipleCuspAugmented_isOpen_iff {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (U : Set (MultipleCuspAugmentedDomain C)) :
    IsOpen U ↔ IsOpen ((multipleCuspAugmentedOld C) ⁻¹' U) ∧
      ∀ i : ι, IsOpen ((multipleCuspAugmentedPiece C i) ⁻¹' U) :=
  isOpen_sup.trans (and_congr Iff.rfl isOpen_iSup_iff)

theorem multipleCuspAugmentedOld_continuous {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) : Continuous (multipleCuspAugmentedOld C) := by
  apply continuous_def.mpr
  intro U hU
  exact ((multipleCuspAugmented_isOpen_iff C U).mp hU).1

theorem multipleCuspAugmentedPiece_continuous {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) : Continuous (multipleCuspAugmentedPiece C i) := by
  apply continuous_def.mpr
  intro U hU
  exact ((multipleCuspAugmented_isOpen_iff C U).mp hU).2 i

theorem multipleCuspAugmentedPiece_injective {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) : Function.Injective (multipleCuspAugmentedPiece C i) :=
  fun _ _ h => Subtype.ext (congrArg (fun p : MultipleCuspAugmentedDomain C => p.val) h)

/-- On another orbit's one-point piece, an open piece restricts to its original finite domain. -/
theorem multipleCuspAugmentedPiece_preimage_image_ne {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    {i j : ι} (hij : i ≠ j) (U : Set (MobiusCuspAugmentedDomain (S i) (w i) (C i))) :
    multipleCuspAugmentedPiece C j ⁻¹' (multipleCuspAugmentedPiece C i '' U) =
      mobiusCuspAugmentedOld (C j) '' (mobiusCuspAugmentedOld (C i) ⁻¹' U) := by
  ext p
  constructor
  · rintro ⟨a, ha, he⟩
    have hv : a.val = p.val := congrArg Subtype.val he
    have hp : p.val ∈ D.carrier := by
      rcases p.property with hp | ⟨g, hg⟩
      · exact hp
      · rcases a.property with ha | ⟨k, hk⟩
        · exact ((C j).orbit_cusp_not_mem hD g (hg ▸ hv ▸ ha)).elim
        · exact (multipleCusp_orbit_points_ne (hne hij) k g ((hk.trans hv).trans hg.symm)).elim
    refine ⟨⟨p.val, hp⟩, ?_, Subtype.ext rfl⟩
    have hea : mobiusCuspAugmentedOld (C i) ⟨p.val, hp⟩ = a := Subtype.ext hv.symm
    change mobiusCuspAugmentedOld (C i) ⟨p.val, hp⟩ ∈ U
    exact hea.symm ▸ ha
  · rintro ⟨z, hz, rfl⟩
    exact ⟨mobiusCuspAugmentedOld (C i) z, hz, Subtype.ext rfl⟩

/-- Each actual single-orbit augmented domain is a genuine open subspace of the simultaneous one. -/
theorem multipleCuspAugmentedPiece_isOpenEmbedding {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j))) (i : ι) :
    Topology.IsOpenEmbedding (multipleCuspAugmentedPiece C i) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (multipleCuspAugmentedPiece_continuous C i) (multipleCuspAugmentedPiece_injective C i)
  intro U hU
  apply (multipleCuspAugmented_isOpen_iff C _).mpr
  constructor
  · have he : multipleCuspAugmentedOld C ⁻¹' (multipleCuspAugmentedPiece C i '' U) =
        mobiusCuspAugmentedOld (C i) ⁻¹' U := by
      ext z
      constructor
      · rintro ⟨a, ha, he⟩
        have hea : a = mobiusCuspAugmentedOld (C i) z := Subtype.ext (congrArg (fun p : MultipleCuspAugmentedDomain C =>
          p.val) he)
        change mobiusCuspAugmentedOld (C i) z ∈ U
        exact hea ▸ ha
      · intro hz
        exact ⟨mobiusCuspAugmentedOld (C i) z, hz, rfl⟩
    rw [he]
    exact hU.preimage (mobiusCuspAugmentedOld_continuous (C i))
  · intro j
    by_cases hij : i = j
    · subst j
      rw [Set.preimage_image_eq _ (multipleCuspAugmentedPiece_injective C i)]
      exact hU
    · rw [multipleCuspAugmentedPiece_preimage_image_ne C hD hne hij]
      exact ((C j).old_isOpenEmbedding hD).isOpenMap _
        (hU.preimage (mobiusCuspAugmentedOld_continuous (C i)))

theorem MobiusCuspNormalization.augmentedSphere_continuous {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) : Continuous (mobiusCuspAugmentedSphere C) := by
  have he : mobiusCuspAugmentedSphere C = (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
    C.normalizer).symm ∘
      stableCuspAugmentedSphere (S.conjugate C.normalizer) C.height C.normalized_disc_eq ∘ C.augmentedHomeomorph := by
    funext p
    exact (C.normalizer.val.symm_apply_apply p.val).symm
  rw [he]
  exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph C.normalizer).symm.continuous.comp
    ((stableCuspAugmentedSphere_continuous _ _ _).comp C.augmentedHomeomorph.continuous)

theorem multipleCuspAugmentedSphere_continuous {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) : Continuous (multipleCuspAugmentedSphere C) := by
  apply continuous_def.mpr
  intro U hU
  apply (multipleCuspAugmented_isOpen_iff C _).mpr
  constructor
  · exact hU.preimage continuous_subtype_val
  · intro i
    exact hU.preimage (C i).augmentedSphere_continuous

theorem multipleCuspAugmented_t2Space {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) : T2Space (MultipleCuspAugmentedDomain C) := by
  constructor
  intro p q hpq
  have hne : multipleCuspAugmentedSphere C p ≠ multipleCuspAugmentedSphere C q :=
    fun he => hpq (Subtype.ext he)
  obtain ⟨U, V, hU, hV, hp, hq, hd⟩ := t2_separation hne
  exact ⟨(multipleCuspAugmentedSphere C) ⁻¹' U, (multipleCuspAugmentedSphere C) ⁻¹' V,
    hU.preimage (multipleCuspAugmentedSphere_continuous C),
    hV.preimage (multipleCuspAugmentedSphere_continuous C), hp, hq, hd.preimage _⟩

/-- The original finite domain retains its topology in the simultaneous construction. -/
theorem multipleCuspAugmentedOld_isOpenEmbedding {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) :
    Topology.IsOpenEmbedding (multipleCuspAugmentedOld C) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (multipleCuspAugmentedOld_continuous C)
    (fun _ _ h => Subtype.ext (congrArg (fun p : MultipleCuspAugmentedDomain C => p.val) h))
  intro U hU
  apply (multipleCuspAugmented_isOpen_iff C _).mpr
  constructor
  · have hi : Function.Injective (multipleCuspAugmentedOld C) :=
      fun _ _ h => Subtype.ext (congrArg (fun p : MultipleCuspAugmentedDomain C => p.val) h)
    rw [Set.preimage_image_eq U hi]
    exact hU
  · intro i
    have he : multipleCuspAugmentedPiece C i ⁻¹' (multipleCuspAugmentedOld C '' U) =
        mobiusCuspAugmentedOld (C i) '' U := by
      ext p
      constructor
      · rintro ⟨z, hz, he⟩
        exact ⟨z, hz, Subtype.ext (congrArg (fun p : MultipleCuspAugmentedDomain C => p.val) he)⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [he]
    exact ((C i).old_isOpenEmbedding hD).isOpenMap _ hU

instance multipleCuspAugmentedAction {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) : MulAction G (MultipleCuspAugmentedDomain C) where
  smul g p := ⟨g • p.val, by
    rcases p.property with hp | ⟨i, k, hk⟩
    · exact Or.inl (D.invariant g p.val hp)
    · refine Or.inr ⟨i, g * k, ?_⟩
      change (g * k) • w i = g • p.val
      rw [mul_smul]
      exact congrArg (fun z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex => g • z) hk⟩
  one_smul p := Subtype.ext (one_smul G p.val)
  mul_smul g k p := Subtype.ext (mul_smul g k p.val)

theorem multipleCuspAugmentedPiece_equivariant {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) (g : G)
    (p : MobiusCuspAugmentedDomain (S i) (w i) (C i)) :
    multipleCuspAugmentedPiece C i (g • p) = g • multipleCuspAugmentedPiece C i p := rfl

instance multipleCuspAugmentedContinuousConstSMul {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) : ContinuousConstSMul G (MultipleCuspAugmentedDomain C) where
  continuous_const_smul g := by
    apply continuous_def.mpr
    intro U hU
    apply (multipleCuspAugmented_isOpen_iff C _).mpr
    constructor
    · change IsOpen (((fun p : MultipleCuspAugmentedDomain C => g • p) ∘ multipleCuspAugmentedOld C) ⁻¹' U)
      have he : (fun p : MultipleCuspAugmentedDomain C => g • p) ∘ multipleCuspAugmentedOld C =
          multipleCuspAugmentedOld C ∘ (fun z : D.carrier => g • z) := rfl
      rw [he]
      exact hU.preimage ((multipleCuspAugmentedOld_continuous C).comp (continuous_const_smul g))
    · intro i
      change IsOpen (((fun p : MultipleCuspAugmentedDomain C => g • p) ∘ multipleCuspAugmentedPiece C i) ⁻¹' U)
      have he : (fun p : MultipleCuspAugmentedDomain C => g • p) ∘ multipleCuspAugmentedPiece C i =
          multipleCuspAugmentedPiece C i ∘ (fun z : MobiusCuspAugmentedDomain (S i) (w i) (C i) => g • z) := rfl
      rw [he]
      exact hU.preimage ((multipleCuspAugmentedPiece_continuous C i).comp (continuous_const_smul g))

/-- The genuine simultaneous full-group orbit quotient. -/
abbrev MultipleCuspAugmentedQuotient {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) :=
  Quotient (MulAction.orbitRel G (MultipleCuspAugmentedDomain C))

/-- Each original single-orbit quotient maps to the actual simultaneous orbit quotient. -/
def multipleCuspQuotientPiece {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) :
    MobiusCuspAugmentedQuotient (C i) → MultipleCuspAugmentedQuotient C :=
  Quotient.map' (multipleCuspAugmentedPiece C i) (by
    rintro a b ⟨g, hg⟩
    exact ⟨g, congrArg (multipleCuspAugmentedPiece C i) hg⟩)

theorem multipleCuspQuotientPiece_continuous {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) : Continuous (multipleCuspQuotientPiece C i) :=
  (multipleCuspAugmentedPiece_continuous C i).quotient_map' _

theorem multipleCuspQuotientPiece_injective {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) : Function.Injective (multipleCuspQuotientPiece C i) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      obtain ⟨g, hg⟩ := Quotient.exact hab
      apply Quotient.sound
      refine ⟨g, ?_⟩
      apply multipleCuspAugmentedPiece_injective C i
      exact hg

/-- Equivariant maps induce the genuine native maps between orbit quotients. -/
def equivariantOrbitQuotientMap {Γ A B : Type*} [Group Γ] [MulAction Γ A] [MulAction Γ B]
    (e : A → B) (he : ∀ (g : Γ) (a : A), e (g • a) = g • e a) :
    Quotient (MulAction.orbitRel Γ A) → Quotient (MulAction.orbitRel Γ B) :=
  Quotient.map' e (by
    rintro a b ⟨g, hg⟩
    exact ⟨g, (he g b).symm.trans (congrArg e hg)⟩)

/-- An equivariant open embedding induces an open embedding of actual orbit quotients. -/
theorem equivariantOrbitQuotientMap_isOpenEmbedding {Γ A B : Type*} [Group Γ]
    [TopologicalSpace A] [TopologicalSpace B] [MulAction Γ A] [MulAction Γ B]
    [ContinuousConstSMul Γ A] [ContinuousConstSMul Γ B]
    (e : A → B) (he : ∀ (g : Γ) (a : A), e (g • a) = g • e a) (heO : Topology.IsOpenEmbedding e) :
    Topology.IsOpenEmbedding (equivariantOrbitQuotientMap e he) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (heO.continuous.quotient_map' _)
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        obtain ⟨g, hg⟩ := Quotient.exact hab
        exact Quotient.sound ⟨g, heO.injective ((he g b).trans hg)⟩
  · intro U hU
    apply (MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := B)).isQuotientMap.isOpen_preimage.mp
    have hpre : (Quotient.mk (MulAction.orbitRel Γ B)) ⁻¹' (equivariantOrbitQuotientMap e he '' U) =
        e '' ((Quotient.mk (MulAction.orbitRel Γ A)) ⁻¹' U) := by
      ext b
      constructor
      · rintro ⟨a, ha, hab⟩
        induction a using Quotient.inductionOn with
        | h a =>
          obtain ⟨g, hg⟩ := Quotient.exact hab.symm
          refine ⟨g • a, ?_, (he g a).trans hg⟩
          have hga : Quotient.mk (MulAction.orbitRel Γ A) (g • a) = Quotient.mk _ a :=
            Quotient.sound ⟨g, rfl⟩
          change Quotient.mk (MulAction.orbitRel Γ A) (g • a) ∈ U
          rw [hga]
          exact ha
      · rintro ⟨a, ha, rfl⟩
        exact ⟨Quotient.mk _ a, ha, rfl⟩
    change IsOpen ((Quotient.mk (MulAction.orbitRel Γ B)) ⁻¹' (equivariantOrbitQuotientMap e he '' U))
    rw [hpre]
    exact heO.isOpenMap _ (hU.preimage continuous_quot_mk)

theorem multipleCuspQuotientPiece_isOpenEmbedding {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j))) (i : ι) :
    Topology.IsOpenEmbedding (multipleCuspQuotientPiece C i) :=
  equivariantOrbitQuotientMap_isOpenEmbedding (multipleCuspAugmentedPiece C i)
    (multipleCuspAugmentedPiece_equivariant C i) (multipleCuspAugmentedPiece_isOpenEmbedding C hD hne i)

/-- The old quotient is canonically included through its unchanged original representatives. -/
def multipleCuspQuotientOld {ι : Type*} {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) : MobiusDomainQuotient D → MultipleCuspAugmentedQuotient C :=
  equivariantOrbitQuotientMap (multipleCuspAugmentedOld C) (fun _ _ => rfl)

theorem multipleCuspQuotientOld_isOpenEmbedding {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) :
    Topology.IsOpenEmbedding (multipleCuspQuotientOld C) :=
  equivariantOrbitQuotientMap_isOpenEmbedding (multipleCuspAugmentedOld C) (fun _ _ => rfl)
    (multipleCuspAugmentedOld_isOpenEmbedding C hD)

theorem multipleCuspQuotientPiece_old {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (i : ι) (x : MobiusDomainQuotient D) :
    multipleCuspQuotientPiece C i ((C i).oldQuotientEmbedding hD x) = multipleCuspQuotientOld C x := by
  obtain ⟨z, rfl⟩ := mobiusDomainProjection_surjective D x
  rw [(C i).oldQuotientEmbedding_projection]
  rfl

/-- The actual new quotient point of the specified cusp orbit. -/
def multipleCuspNewPoint {ι : Type*} {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) : MultipleCuspAugmentedQuotient C :=
  multipleCuspQuotientPiece C i (C i).cuspQuotient

/-- Each new orbit produces precisely its own new quotient point. -/
theorem multipleCuspNewPoint_ne {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i))
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    {i j : ι} (hij : i ≠ j) : multipleCuspNewPoint C i ≠ multipleCuspNewPoint C j := by
  intro he
  obtain ⟨g, hg⟩ := Quotient.exact he
  have hv := congrArg (multipleCuspAugmentedSphere C) hg
  change g • ((1 : G) • w j) = (1 : G) • w i at hv
  rw [one_smul, one_smul] at hv
  exact hne hij ⟨g, hv⟩

theorem multipleCuspNewPoint_not_mem_old {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (i : ι) :
    multipleCuspNewPoint C i ∉ Set.range (multipleCuspQuotientOld C) := by
  rintro ⟨x, hx⟩
  rw [← multipleCuspQuotientPiece_old C hD i x] at hx
  exact (C i).cuspQuotient_not_mem_old hD
    ⟨x, multipleCuspQuotientPiece_injective C i hx⟩

/-- There are no additional points beyond the old quotient and the selected cusp orbits. -/
theorem multipleCuspQuotient_old_or_new {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (x : MultipleCuspAugmentedQuotient C) :
    x ∈ Set.range (multipleCuspQuotientOld C) ∨ ∃ i : ι, x = multipleCuspNewPoint C i := by
  induction x using Quotient.inductionOn with
  | h p =>
    rcases p.property with hp | ⟨i, g, hg⟩
    · exact Or.inl ⟨mobiusDomainProjection D ⟨p.val, hp⟩, rfl⟩
    · refine Or.inr ⟨i, Quotient.sound ⟨g, Subtype.ext ?_⟩⟩
      change g • ((1 : G) • w i) = p.val
      rw [one_smul]
      exact hg

theorem multipleCuspQuotientPiece_range {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (i : ι) :
    Set.range (multipleCuspQuotientPiece C i) =
      Set.range (multipleCuspQuotientOld C) ∪ {multipleCuspNewPoint C i} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rcases (C i).quotient_old_or_cusp hD a with ⟨b, hb⟩ | hb
    · exact Or.inl ⟨b, (multipleCuspQuotientPiece_old C hD i b).symm.trans
        (congrArg (multipleCuspQuotientPiece C i) hb)⟩
    · exact Or.inr (congrArg (multipleCuspQuotientPiece C i) hb)
  · rintro (⟨a, rfl⟩ | hx)
    · exact ⟨(C i).oldQuotientEmbedding hD a, multipleCuspQuotientPiece_old C hD i a⟩
    · exact ⟨(C i).cuspQuotient, hx.symm⟩

theorem MobiusCuspNormalization.finiteTail_subset_domain {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (t : ℝ) (ht : C.height ≤ t) : C.finiteTail t ⊆ D.carrier := by
  rintro p ⟨z, hz, hzp⟩
  apply S.subset_domain
  have hp : C.normalizer.val p ∈ C.normalizer.val '' S.carrier := by
    rw [C.disc_eq]
    exact ⟨z, ht.trans_lt hz, hzp⟩
  obtain ⟨a, ha, he⟩ := hp
  exact C.normalizer.val.injective he ▸ ha

theorem MobiusCuspNormalization.heightTail_one_cases {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (t : ℝ) (p : MobiusCuspAugmentedDomain S w C)
    (hp : p ∈ mobiusCuspAugmentedHeightTail C 1 t) : p.val = w ∨ p.val ∈ C.finiteTail t := by
  rcases hp with hp | ⟨z, hz, he⟩
  · exact Or.inl hp
  · refine Or.inr ⟨z, hz, ?_⟩
    change C.normalizer.val.symm (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = p.val at he
    exact (C.normalizer.val.apply_symm_apply (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)).symm.trans (congrArg C.normalizer.val he)

/-- Different deep cusp neighborhoods never identify under the full actual group. -/
theorem multipleCusp_deep_orbit_ne {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    {i j : ι} (hij : i ≠ j)
    (a : MobiusCuspAugmentedDomain (S i) (w i) (C i))
    (b : MobiusCuspAugmentedDomain (S j) (w j) (C j))
    (ha : a ∈ mobiusCuspAugmentedHeightTail (C i) 1 ((C i).height + 1))
    (hb : b ∈ mobiusCuspAugmentedHeightTail (C j) 1 ((C j).height + 1)) :
    ¬MulAction.orbitRel G (MultipleCuspAugmentedDomain C)
      (multipleCuspAugmentedPiece C i a) (multipleCuspAugmentedPiece C j b) := by
  rintro ⟨g, hg⟩
  have hv : g • b.val = a.val := congrArg (multipleCuspAugmentedSphere C) hg
  rcases (C i).heightTail_one_cases _ a ha with hai | hai
  · rcases (C j).heightTail_one_cases _ b hb with hbj | hbj
    · exact hne hij ⟨g, hbj ▸ hai ▸ hv⟩
    · have hbd : b.val ∈ D.carrier := (C j).finiteTail_subset_domain _ (le_add_of_nonneg_right (by norm_num)) hbj
      have had : w i ∈ D.carrier := hai ▸ hv ▸ D.invariant g b.val hbd
      exact (C i).orbit_cusp_not_mem hD 1 had
  · rcases (C j).heightTail_one_cases _ b hb with hbj | hbj
    · have had : a.val ∈ D.carrier := (C i).finiteTail_subset_domain _ (le_add_of_nonneg_right (by norm_num)) hai
      have hgv : g.val.val (w j) = a.val := hbj ▸ hv
      exact (C j).orbit_cusp_not_mem hD g (hgv.symm ▸ had)
    · exact Set.disjoint_left.mp (multipleCusp_finiteTails_disjoint (C i) (C j) hD (hne hij) g)
        hai ⟨b.val, hbj, hv⟩

/-- The actual quotient neighborhood supplied by one whole cusp orbit. -/
def multipleCuspDeepNeighborhood {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) : Set (MultipleCuspAugmentedQuotient C) :=
  (Quotient.mk (MulAction.orbitRel G (MultipleCuspAugmentedDomain C))) ''
    (multipleCuspAugmentedPiece C i '' mobiusCuspAugmentedHeightTail (C i) 1 ((C i).height + 1))

theorem multipleCuspDeepNeighborhood_isOpen {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    (hfix : ∀ i, ∀ f ∈ G, f.val (w i) = w i → f ∈ (S i).stabilizer) (i : ι) :
    IsOpen (multipleCuspDeepNeighborhood C i) := by
  apply (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := MultipleCuspAugmentedDomain C)).isOpenMap
  apply (multipleCuspAugmentedPiece_isOpenEmbedding C hD hne i).isOpenMap
  rw [mobiusCuspAugmentedHeightTail_eq_image (C i) 1 _ (lt_add_one _)]
  exact ((C i).cusp_isOpenEmbedding hD (hfix i) 1).isOpenMap _ (stableCuspCompletionTail_isOpen _ _)

theorem multipleCuspNewPoint_mem_deep {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) :
    multipleCuspNewPoint C i ∈ multipleCuspDeepNeighborhood C i := by
  refine ⟨multipleCuspAugmentedPiece C i (mobiusCuspAugmentedCusp (C i) 1 (stableCuspCompletionInfinity (C i).height)),
    ⟨mobiusCuspAugmentedCusp (C i) 1 (stableCuspCompletionInfinity (C i).height), Or.inl rfl, rfl⟩, rfl⟩

theorem multipleCuspDeepNeighborhood_disjoint {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    {i j : ι} (hij : i ≠ j) : Disjoint (multipleCuspDeepNeighborhood C i) (multipleCuspDeepNeighborhood C j) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨_, ⟨a, ha, rfl⟩, hax⟩ ⟨_, ⟨b, hb, rfl⟩, hbx⟩
  exact multipleCusp_deep_orbit_ne C hD hne hij a b ha hb (Quotient.exact (hax.trans hbx.symm))

/-- Hausdorff separation within a genuine open subspace requires no ambient Hausdorff assumption. -/
theorem isOpenEmbedding_separation_on_range {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [T2Space A] (f : A → B) (hf : Topology.IsOpenEmbedding f) (x y : B)
    (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) (hxy : x ≠ y) :
    ∃ U V : Set B, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : a ≠ b := fun h => hxy (congrArg f h)
  obtain ⟨U, V, hU, hV, ha, hb, hd⟩ := t2_separation hab
  exact ⟨f '' U, f '' V, hf.isOpenMap _ hU, hf.isOpenMap _ hV,
    ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, (Set.disjoint_image_iff hf.injective).mpr hd⟩

/-- The actual simultaneous orbit quotient is Hausdorff; distinct ends are separated
by the proved cross-cusp neighborhoods, not by an added topological hypothesis. -/
theorem multipleCuspQuotient_t2Space {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    (hfix : ∀ i, ∀ f ∈ G, f.val (w i) = w i → f ∈ (S i).stabilizer) :
    T2Space (MultipleCuspAugmentedQuotient C) := by
  have : T2Space (MobiusDomainQuotient D) := (mobiusQuotientRiemannSurface D hD).t2Space
  constructor
  intro x y hxy
  rcases multipleCuspQuotient_old_or_new C x with hx | ⟨i, hx⟩
  · rcases multipleCuspQuotient_old_or_new C y with hy | ⟨i, hy⟩
    · exact isOpenEmbedding_separation_on_range _ (multipleCuspQuotientOld_isOpenEmbedding C hD) x y hx hy hxy
    · have : T2Space (MobiusCuspAugmentedQuotient (C i)) := ((C i).filledQuotientRiemannSurface hD (hfix i)).t2Space
      apply isOpenEmbedding_separation_on_range _ (multipleCuspQuotientPiece_isOpenEmbedding C hD hne i) x y _ _ hxy
      · rw [multipleCuspQuotientPiece_range C hD i]
        exact Or.inl hx
      · exact ⟨(C i).cuspQuotient, hy.symm⟩
  · rcases multipleCuspQuotient_old_or_new C y with hy | ⟨j, hy⟩
    · have : T2Space (MobiusCuspAugmentedQuotient (C i)) := ((C i).filledQuotientRiemannSurface hD (hfix i)).t2Space
      apply isOpenEmbedding_separation_on_range _ (multipleCuspQuotientPiece_isOpenEmbedding C hD hne i) x y _ _ hxy
      · exact ⟨(C i).cuspQuotient, hx.symm⟩
      · rw [multipleCuspQuotientPiece_range C hD i]
        exact Or.inl hy
    · by_cases hij : i = j
      · subst j
        exact (hxy (hx.trans hy.symm)).elim
      · exact ⟨multipleCuspDeepNeighborhood C i, multipleCuspDeepNeighborhood C j,
          multipleCuspDeepNeighborhood_isOpen C hD hne hfix i,
          multipleCuspDeepNeighborhood_isOpen C hD hne hfix j,
          hx.symm ▸ multipleCuspNewPoint_mem_deep C i, hy.symm ▸ multipleCuspNewPoint_mem_deep C j,
          multipleCuspDeepNeighborhood_disjoint C hD hne hij⟩

/-- All the filled quotient pieces remain connected through the unchanged original quotient. -/
theorem multipleCuspQuotient_connectedSpace {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hfix : ∀ i, ∀ f ∈ G, f.val (w i) = w i → f ∈ (S i).stabilizer) :
    ConnectedSpace (MultipleCuspAugmentedQuotient C) := by
  have : ConnectedSpace (MobiusDomainQuotient D) := (mobiusQuotientRiemannSurface D hD).connectedSpace
  let x₀ : MobiusDomainQuotient D := Classical.choice inferInstance
  let V : Option ι → Set (MultipleCuspAugmentedQuotient C) :=
    Option.rec (Set.range (multipleCuspQuotientOld C)) (fun i => Set.range (multipleCuspQuotientPiece C i))
  have hV : ∀ i, IsPreconnected (V i) := by
    intro i
    cases i with
    | none => exact (isConnected_range (multipleCuspQuotientOld_isOpenEmbedding C hD).continuous).isPreconnected
    | some i =>
      have : ConnectedSpace (MobiusCuspAugmentedQuotient (C i)) := ((C i).filledQuotientRiemannSurface hD (hfix
        i)).connectedSpace
      exact (isConnected_range (multipleCuspQuotientPiece_continuous C i)).isPreconnected
  have hInt : (⋂ i, V i).Nonempty := by
    refine ⟨multipleCuspQuotientOld C x₀, Set.mem_iInter.mpr ?_⟩
    intro i
    cases i with
    | none => exact ⟨x₀, rfl⟩
    | some i => exact ⟨(C i).oldQuotientEmbedding hD x₀, multipleCuspQuotientPiece_old C hD i x₀⟩
  have hUnion : ⋃ i, V i = Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro x _hx
    rcases multipleCuspQuotient_old_or_new C x with hx | ⟨i, hx⟩
    · exact Set.mem_iUnion.mpr ⟨none, hx⟩
    · exact Set.mem_iUnion.mpr ⟨some i, ⟨(C i).cuspQuotient, hx.symm⟩⟩
  apply connectedSpace_iff_univ.mpr
  refine ⟨⟨multipleCuspQuotientOld C x₀, Set.mem_univ _⟩, ?_⟩
  rw [← hUnion]
  exact isPreconnected_iUnion hInt hV

/-- Literal simultaneous-cusp height tails in the original sphere coordinates. -/
def multipleCuspHeightTail {ι : Type*} {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) (g : G) (t : ℝ) :
    Set (MultipleCuspAugmentedDomain C) :=
  {p | p.val = g.val.val (w i) ∨ ∃ z : ℂ, t < z.im ∧
    g.val.val ((C i).normalizer.val.symm (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = p.val}

theorem multipleCuspHeightTail_eq_image {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) (g : G) (t : ℝ) (ht : (C i).height < t) :
    multipleCuspHeightTail C i g t = multipleCuspAugmentedPiece C i '' mobiusCuspAugmentedHeightTail (C i) g t := by
  ext p
  constructor
  · rintro (hp | ⟨z, hz, he⟩)
    · exact ⟨mobiusCuspAugmentedCusp (C i) g (stableCuspCompletionInfinity (C i).height),
        Or.inl rfl, Subtype.ext hp.symm⟩
    · let zH : stableCuspHalfPlane (C i).height := ⟨z, ht.trans hz⟩
      exact ⟨mobiusCuspAugmentedCusp (C i) g (stableCuspCompletionSome (C i).height zH),
        Or.inr ⟨z, hz, rfl⟩, Subtype.ext he⟩
  · rintro ⟨a, ha, rfl⟩
    exact ha

/-- Every added orbit has exactly the original literal uniform-height neighborhood filter. -/
theorem multipleCusp_mem_nhds_iff {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    (hfix : ∀ i, ∀ f ∈ G, f.val (w i) = w i → f ∈ (S i).stabilizer)
    (i : ι) (g : G) (U : Set (MultipleCuspAugmentedDomain C)) :
    U ∈ 𝓝 (multipleCuspAugmentedPiece C i
        (mobiusCuspAugmentedCusp (C i) g (stableCuspCompletionInfinity (C i).height))) ↔
      ∃ t : ℝ, (C i).height < t ∧ multipleCuspHeightTail C i g t ⊆ U := by
  rw [← (multipleCuspAugmentedPiece_isOpenEmbedding C hD hne i).map_nhds_eq
    (mobiusCuspAugmentedCusp (C i) g (stableCuspCompletionInfinity (C i).height))]
  change multipleCuspAugmentedPiece C i ⁻¹' U ∈
    𝓝 (mobiusCuspAugmentedCusp (C i) g (stableCuspCompletionInfinity (C i).height)) ↔ _
  rw [(C i).augmented_mem_nhds_iff hD (hfix i)]
  constructor
  · rintro ⟨t, ht, hsub⟩
    refine ⟨t, ht, ?_⟩
    rw [multipleCuspHeightTail_eq_image C i g t ht]
    exact Set.image_subset_iff.mpr hsub
  · rintro ⟨t, ht, hsub⟩
    rw [multipleCuspHeightTail_eq_image C i g t ht] at hsub
    exact ⟨t, ht, Set.image_subset_iff.mp hsub⟩

/-- No actual added point becomes locally compact when other cusp orbits are adjoined. -/
theorem multipleCusp_no_compact_nhds {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    (hfix : ∀ i, ∀ f ∈ G, f.val (w i) = w i → f ∈ (S i).stabilizer) (i : ι) (g : G) :
    ¬∃ K : Set (MultipleCuspAugmentedDomain C), IsCompact K ∧
      K ∈ 𝓝 (multipleCuspAugmentedPiece C i
        (mobiusCuspAugmentedCusp (C i) g (stableCuspCompletionInfinity (C i).height))) := by
  rintro ⟨K, hKc, hKn⟩
  have : T2Space (MultipleCuspAugmentedDomain C) := multipleCuspAugmented_t2Space C
  obtain ⟨L, hLc, hLn⟩ := isOpenEmbedding_compact_nhds_pullback _
    (multipleCuspAugmentedPiece_isOpenEmbedding C hD hne i)
    (mobiusCuspAugmentedCusp (C i) g (stableCuspCompletionInfinity (C i).height)) K hKc hKn
  exact (C i).augmented_no_compact_nhds hD (hfix i) g ⟨L, hLc, hLn⟩


/-- An analytic full-source open embedding gives the actual analytic coordinate partial homeomorphism. -/
theorem riemannFullSourceChart_analytic {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (R : RiemannAtlas A) (T : RiemannAtlas X) (J : OpenPartialHomeomorph A X) (hJ : J.source = Set.univ)
    (ha : RiemannAnalyticMap R T J) (e : OpenPartialHomeomorph A ℂ) (he : e ∈ R.charts)
    (f : OpenPartialHomeomorph X ℂ) (hf : f ∈ T.charts) :
    AnalyticOnNhd ℂ (e.symm.trans (J.trans f)) (e.symm.trans (J.trans f)).source := by
  have hd : riemannChartMapDomain e J f = (e.symm.trans (J.trans f)).source := by
    ext z
    change (z ∈ e.target ∧ J (e.symm z) ∈ f.source) ↔
      (z ∈ e.target ∧ e.symm z ∈ J.source ∧ J (e.symm z) ∈ f.source)
    rw [hJ]
    simp only [Set.mem_univ, true_and]
  have hh := ha.2 e he f hf
  rw [hd] at hh
  exact hh

/-- Genuine analytic atlas gluing across a common analytic open subspace.
No derivative condition is assumed: the inverse coordinate map is proved analytic. -/
theorem riemannCharts_commonOpen_analyticAt
    {A X Z Y : Type*} [TopologicalSpace A] [TopologicalSpace X]
    [TopologicalSpace Z] [TopologicalSpace Y]
    (R : RiemannAtlas A) (T : RiemannAtlas X) (U : RiemannAtlas Z)
    (J : OpenPartialHomeomorph A X) (K : OpenPartialHomeomorph A Z)
    (F : OpenPartialHomeomorph X Y) (H : OpenPartialHomeomorph Z Y)
    (hJ : J.source = Set.univ) (hK : K.source = Set.univ)
    (hF : F.source = Set.univ) (hH : H.source = Set.univ)
    (hJa : RiemannAnalyticMap R T J) (hKa : RiemannAnalyticMap R U K)
    (hcomm : ∀ a : A, F (J a) = H (K a))
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ T.charts)
    (f : OpenPartialHomeomorph Z ℂ) (hf : f ∈ U.charts)
    (z : ℂ) (hz : z ∈ ((F.symm.trans e).symm.trans (H.symm.trans f)).source)
    (a : A) (ha : F (J a) = (F.symm.trans e).symm z) :
    AnalyticAt ℂ ((F.symm.trans e).symm.trans (H.symm.trans f)) z := by
  have hJs : ∀ b : A, b ∈ J.source := by intro b; rw [hJ]; trivial
  have hKs : ∀ b : A, b ∈ K.source := by intro b; rw [hK]; trivial
  have hFs : ∀ b : X, b ∈ F.source := by intro b; rw [hF]; trivial
  have hHs : ∀ b : Z, b ∈ H.source := by intro b; rw [hH]; trivial
  have hpa : F.symm ((F.symm.trans e).symm z) = J a := by
    rw [← ha, F.left_inv (hFs _)]
  have hqa : H.symm ((F.symm.trans e).symm z) = K a := by
    rw [← ha, hcomm, H.left_inv (hHs _)]
  have hae : J a ∈ e.source := by
    have hp := (F.symm.trans e).map_target hz.1
    change _ ∈ F.target ∧ F.symm _ ∈ e.source at hp
    exact hpa ▸ hp.2
  have haf : K a ∈ f.source := by
    have hp := hz.2
    change _ ∈ H.target ∧ H.symm _ ∈ f.source at hp
    exact hqa ▸ hp.2
  have hea : e (J a) = z := by
    have hp := (F.symm.trans e).right_inv hz.1
    change e (F.symm ((F.symm.trans e).symm z)) = z at hp
    rwa [hpa] at hp
  obtain ⟨k, hk, hka⟩ := R.cover a
  let L := k.symm.trans (J.trans e)
  let M := k.symm.trans (K.trans f)
  have hL := riemannFullSourceChart_analytic R T J hJ hJa k hk e he
  have hM := riemannFullSourceChart_analytic R U K hK hKa k hk f hf
  have hLs : k a ∈ L.source := by
    refine ⟨k.map_source hka, ?_⟩
    change k.symm (k a) ∈ J.source ∧ J (k.symm (k a)) ∈ e.source
    rw [k.left_inv hka]
    exact ⟨hJs a, hae⟩
  have hMs : k a ∈ M.source := by
    refine ⟨k.map_source hka, ?_⟩
    change k.symm (k a) ∈ K.source ∧ K (k.symm (k a)) ∈ f.source
    rw [k.left_inv hka]
    exact ⟨hKs a, haf⟩
  have hLka : L (k a) = z := by
    change e (J (k.symm (k a))) = z
    rw [k.left_inv hka]
    exact hea
  have hzt : z ∈ L.target := hLka ▸ L.map_source hLs
  have hLsz : L.symm z = k a := by rw [← hLka, L.left_inv hLs]
  have hInv := openPartialHomeomorph_analytic_inverse L hL
  have hcomp : AnalyticAt ℂ (M ∘ L.symm) z := by
    apply AnalyticAt.comp
    · rw [hLsz]
      exact hM _ hMs
    · exact hInv z hzt
  apply hcomp.congr
  filter_upwards [L.open_target.mem_nhds hzt] with q hq
  have hLq := L.map_target hq
  have heq : J (k.symm (L.symm q)) ∈ e.source := hLq.2.2
  have hv : e (J (k.symm (L.symm q))) = q := L.right_inv hq
  have heInv : e.symm q = J (k.symm (L.symm q)) :=
    (congrArg e.symm hv.symm).trans (e.left_inv heq)
  change f (K (k.symm (L.symm q))) = f (H.symm (F (e.symm q)))
  rw [heInv, hcomm, H.left_inv (hHs _)]

/-- Analytic atlases glue across genuine open covers whose different pieces meet only
in their common analytic open subspace. This constructs the full overlap proofs. -/
def riemannAtlasOfCommonOpenCover {ι A Y : Type*} {X : ι → Type*}
    [TopologicalSpace A] [TopologicalSpace Y] [∀ i, TopologicalSpace (X i)]
    (R : RiemannAtlas A) (T : ∀ i, RiemannAtlas (X i))
    (F : ∀ i, OpenPartialHomeomorph (X i) Y) (J : ∀ i, OpenPartialHomeomorph A (X i))
    (hF : ∀ i, (F i).source = Set.univ) (hJ : ∀ i, (J i).source = Set.univ)
    (hJa : ∀ i, RiemannAnalyticMap R (T i) (J i))
    (P : A → Y) (hcomm : ∀ (i : ι) (a : A), F i (J i a) = P a)
    (hcover : ∀ y : Y, ∃ (i : ι) (x : X i), F i x = y)
    (hcross : ∀ i j : ι, i ≠ j → ∀ y : Y,
      y ∈ Set.range (F i) → y ∈ Set.range (F j) → y ∈ Set.range P) : RiemannAtlas Y where
  charts := {e | ∃ (i : ι) (f : OpenPartialHomeomorph (X i) ℂ), f ∈ (T i).charts ∧ e = (F i).symm.trans f}
  cover y := by
    obtain ⟨i, x, rfl⟩ := hcover y
    obtain ⟨f, hf, hfx⟩ := (T i).cover x
    refine ⟨(F i).symm.trans f, ⟨i, f, hf, rfl⟩, ?_⟩
    have hx : x ∈ (F i).source := by rw [hF]; trivial
    exact ⟨(F i).map_source hx, by change (F i).symm (F i x) ∈ f.source; rwa [(F i).left_inv hx]⟩
  compatible := by
    rintro _ ⟨i, e, he, rfl⟩ _ ⟨j, f, hf, rfl⟩ z hz
    by_cases hij : i = j
    · subst j
      exact riemannCharts_commonOpen_analyticAt (T i) (T i) (T i)
        (OpenPartialHomeomorph.refl (X i)) (OpenPartialHomeomorph.refl (X i)) (F i) (F i)
        rfl rfl (hF i) (hF i) (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.id (T
          i)) (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.id (T i))
        (fun _ => rfl) e he f hf z hz (e.symm z) rfl
    · let p := ((F i).symm.trans e).symm z
      have hpi : p ∈ Set.range (F i) := ⟨e.symm z, rfl⟩
      have hpj : p ∈ Set.range (F j) := ⟨(F j).symm p, (F j).right_inv hz.2.1⟩
      obtain ⟨a, ha⟩ := hcross i j hij p hpi hpj
      exact riemannCharts_commonOpen_analyticAt R (T i) (T j) (J i) (J j) (F i) (F j)
        (hJ i) (hJ j) (hF i) (hF j) (hJa i) (hJa j)
        (fun b => (hcomm i b).trans (hcomm j b).symm) e he f hf z hz a ((hcomm i a).trans ha)

/-- The unchanged common analytic open subspace includes analytically in the glued atlas. -/
theorem riemannAtlasOfCommonOpenCover_inclusion_analytic {ι A Y : Type*} {X : ι → Type*}
    [TopologicalSpace A] [TopologicalSpace Y] [∀ i, TopologicalSpace (X i)]
    (R : RiemannAtlas A) (T : ∀ i, RiemannAtlas (X i))
    (F : ∀ i, OpenPartialHomeomorph (X i) Y) (J : ∀ i, OpenPartialHomeomorph A (X i))
    (hF : ∀ i, (F i).source = Set.univ) (hJ : ∀ i, (J i).source = Set.univ)
    (hJa : ∀ i, RiemannAnalyticMap R (T i) (J i))
    (P : A → Y) (hcomm : ∀ (i : ι) (a : A), F i (J i a) = P a)
    (hcover : ∀ y : Y, ∃ (i : ι) (x : X i), F i x = y)
    (hcross : ∀ i j : ι, i ≠ j → ∀ y : Y,
      y ∈ Set.range (F i) → y ∈ Set.range (F j) → y ∈ Set.range P) (hP : Continuous P) :
    RiemannAnalyticMap R (riemannAtlasOfCommonOpenCover R T F J hF hJ hJa P hcomm hcover hcross) P := by
  refine ⟨hP, ?_⟩
  rintro e he _ ⟨i, f, hf, rfl⟩
  have hFs : ∀ x : X i, x ∈ (F i).source := by intro x; rw [hF]; trivial
  have hEq : ∀ a : A, (F i).symm (P a) = J i a := by
    intro a
    rw [← hcomm i a, (F i).left_inv (hFs _)]
  have hMem : ∀ a : A, P a ∈ (F i).target := by
    intro a
    rw [← hcomm i a]
    exact (F i).map_source (hFs _)
  have hd : riemannChartMapDomain e P ((F i).symm.trans f) = riemannChartMapDomain e (J i) f := by
    ext z
    change (z ∈ e.target ∧ P (e.symm z) ∈ (F i).target ∧ (F i).symm (P (e.symm z)) ∈ f.source) ↔
      (z ∈ e.target ∧ J i (e.symm z) ∈ f.source)
    simp only [hEq, hMem, true_and]
  have heq : riemannChartMap e P ((F i).symm.trans f) = riemannChartMap e (J i) f := by
    funext z
    exact congrArg f (hEq (e.symm z))
  rw [hd, heq]
  exact (hJa i).2 e he f hf

/-- The old quotient together with all actual single-orbit filled quotient pieces. -/
def MultipleCuspAtlasPiece {ι : Type*} {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) : Option ι → Type _ :=
  Option.rec (MobiusDomainQuotient D) (fun i => MobiusCuspAugmentedQuotient (C i))

instance multipleCuspAtlasPieceTopology {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (o : Option ι) :
    TopologicalSpace (MultipleCuspAtlasPiece C o) := by
  cases o with
  | none => exact inferInstanceAs (TopologicalSpace (MobiusDomainQuotient D))
  | some i => exact inferInstanceAs (TopologicalSpace (MobiusCuspAugmentedQuotient (C i)))

def multipleCuspPieceSurface {ι : Type*} {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hfix : ∀ i, ∀ f ∈ G, f.val (w i) = w i → f ∈ (S i).stabilizer) (o : Option ι) :
    RiemannSurface (MultipleCuspAtlasPiece C o) := by
  cases o with
  | none => exact mobiusQuotientRiemannSurface D hD
  | some i => exact (C i).filledQuotientRiemannSurface hD (hfix i)

/-- The actual open cover maps, bundled as full-source partial homeomorphisms. -/
def multipleCuspPieceOph {ι : Type*} {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j))) (o : Option ι) :
    OpenPartialHomeomorph (MultipleCuspAtlasPiece C o) (MultipleCuspAugmentedQuotient C) := by
  cases o with
  | none =>
    let z : D.carrier := ⟨D.isConnected.nonempty.some, D.isConnected.nonempty.some_mem⟩
    have : Nonempty (MobiusDomainQuotient D) := ⟨mobiusDomainProjection D z⟩
    have : Nonempty (MultipleCuspAtlasPiece C none) := ⟨mobiusDomainProjection D z⟩
    exact (multipleCuspQuotientOld_isOpenEmbedding C hD).toOpenPartialHomeomorph (multipleCuspQuotientOld C)
  | some i =>
    have : Nonempty (MultipleCuspAtlasPiece C (some i)) := ⟨(C i).cuspQuotient⟩
    exact (multipleCuspQuotientPiece_isOpenEmbedding C hD hne i).toOpenPartialHomeomorph (multipleCuspQuotientPiece C i)

/-- The original quotient sits analytically in each actual filled piece. -/
def multipleCuspPieceOldOph {ι : Type*} {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (o : Option ι) :
    OpenPartialHomeomorph (MobiusDomainQuotient D) (MultipleCuspAtlasPiece C o) := by
  cases o with
  | none => exact OpenPartialHomeomorph.refl _
  | some i =>
    let z : D.carrier := ⟨D.isConnected.nonempty.some, D.isConnected.nonempty.some_mem⟩
    have : Nonempty (MobiusDomainQuotient D) := ⟨mobiusDomainProjection D z⟩
    exact ((C i).oldQuotientEmbedding_isOpenEmbedding hD).toOpenPartialHomeomorph ((C i).oldQuotientEmbedding hD)

theorem multipleCuspPieceOph_source {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j))) (o : Option ι) :
    (multipleCuspPieceOph C hD hne o).source = Set.univ := by
  cases o <;> rfl

theorem multipleCuspPieceOldOph_source {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (o : Option ι) :
    (multipleCuspPieceOldOph C hD o).source = Set.univ := by
  cases o <;> rfl

theorem multipleCuspPieceOldOph_analytic {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hfix : ∀ i, ∀ f ∈ G, f.val (w i) = w i → f ∈ (S i).stabilizer) (o : Option ι) :
    RiemannAnalyticMap (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
      (multipleCuspPieceSurface C hD hfix o).toRiemannAtlas (multipleCuspPieceOldOph C hD o) := by
  cases o with
  | none => exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.id _
  | some i => exact (C i).oldQuotientEmbedding_analytic hD (hfix i)

theorem multipleCuspPieceOph_old {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    (o : Option ι) (x : MobiusDomainQuotient D) :
    multipleCuspPieceOph C hD hne o (multipleCuspPieceOldOph C hD o x) = multipleCuspQuotientOld C x := by
  cases o with
  | none => rfl
  | some i => exact multipleCuspQuotientPiece_old C hD i x

theorem multipleCuspPieceOph_cover {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    (x : MultipleCuspAugmentedQuotient C) :
    ∃ (o : Option ι) (a : MultipleCuspAtlasPiece C o), multipleCuspPieceOph C hD hne o a = x := by
  rcases multipleCuspQuotient_old_or_new C x with ⟨a, ha⟩ | ⟨i, hi⟩
  · exact ⟨none, a, ha⟩
  · exact ⟨some i, (C i).cuspQuotient, hi.symm⟩

theorem multipleCuspPieceOph_cross {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    (o p : Option ι) (hop : o ≠ p) (x : MultipleCuspAugmentedQuotient C)
    (hx : x ∈ Set.range (multipleCuspPieceOph C hD hne o))
    (hy : x ∈ Set.range (multipleCuspPieceOph C hD hne p)) : x ∈ Set.range (multipleCuspQuotientOld C) := by
  cases o with
  | none => exact hx
  | some i =>
    cases p with
    | none => exact hy
    | some j =>
      have hij : i ≠ j := fun h => hop (congrArg some h)
      change x ∈ Set.range (multipleCuspQuotientPiece C i) at hx
      change x ∈ Set.range (multipleCuspQuotientPiece C j) at hy
      rw [multipleCuspQuotientPiece_range C hD i] at hx
      rw [multipleCuspQuotientPiece_range C hD j] at hy
      rcases hx with hx | hx
      · exact hx
      · rcases hy with hy | hy
        · exact hy
        · exact (multipleCuspNewPoint_ne C hne hij (hx.symm.trans hy)).elim

/-- The common analytic atlas on the genuine simultaneous full-group orbit quotient. -/
def multipleCuspRiemannAtlas {ι : Type*} {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    (hfix : ∀ i, ∀ f ∈ G, f.val (w i) = w i → f ∈ (S i).stabilizer) :
    RiemannAtlas (MultipleCuspAugmentedQuotient C) :=
  riemannAtlasOfCommonOpenCover (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
    (fun o => (multipleCuspPieceSurface C hD hfix o).toRiemannAtlas)
    (multipleCuspPieceOph C hD hne) (multipleCuspPieceOldOph C hD)
    (multipleCuspPieceOph_source C hD hne) (multipleCuspPieceOldOph_source C hD)
    (multipleCuspPieceOldOph_analytic C hD hfix) (multipleCuspQuotientOld C)
    (multipleCuspPieceOph_old C hD hne) (multipleCuspPieceOph_cover C hD hne) (multipleCuspPieceOph_cross C hD hne)

/-- Simultaneously filling arbitrary different actual cusp orbits gives a genuine Riemann surface. -/
def multipleCuspRiemannSurface {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    (hfix : ∀ i, ∀ f ∈ G, f.val (w i) = w i → f ∈ (S i).stabilizer) :
    RiemannSurface (MultipleCuspAugmentedQuotient C) where
  toRiemannAtlas := multipleCuspRiemannAtlas C hD hne hfix
  t2Space := multipleCuspQuotient_t2Space C hD hne hfix
  connectedSpace := multipleCuspQuotient_connectedSpace C hD hfix

theorem multipleCuspQuotientOld_analytic {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    (hfix : ∀ i, ∀ f ∈ G, f.val (w i) = w i → f ∈ (S i).stabilizer) :
    RiemannAnalyticMap (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
      (multipleCuspRiemannSurface C hD hne hfix).toRiemannAtlas (multipleCuspQuotientOld C) :=
  riemannAtlasOfCommonOpenCover_inclusion_analytic (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
    (fun o => (multipleCuspPieceSurface C hD hfix o).toRiemannAtlas)
    (multipleCuspPieceOph C hD hne) (multipleCuspPieceOldOph C hD)
    (multipleCuspPieceOph_source C hD hne) (multipleCuspPieceOldOph_source C hD)
    (multipleCuspPieceOldOph_analytic C hD hfix) (multipleCuspQuotientOld C)
    (multipleCuspPieceOph_old C hD hne) (multipleCuspPieceOph_cover C hD hne) (multipleCuspPieceOph_cross C hD hne)
    (multipleCuspQuotientOld_isOpenEmbedding C hD).continuous

/-- The ordinary filled-disc chart at each actual new orbit point. -/
def multipleCuspNewChart {ι : Type*} {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j))) (i : ι) :
    OpenPartialHomeomorph (MultipleCuspAugmentedQuotient C) ℂ :=
  (multipleCuspPieceOph C hD hne (some i)).symm.trans ((C i).newChart hD)

theorem multipleCuspNewChart_mem {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    (hfix : ∀ i, ∀ f ∈ G, f.val (w i) = w i → f ∈ (S i).stabilizer) (i : ι) :
    multipleCuspNewChart C hD hne i ∈ (multipleCuspRiemannSurface C hD hne hfix).charts :=
  ⟨some i, (C i).newChart hD, (C i).newChart_mem hD (hfix i), rfl⟩

theorem multipleCuspNewChart_target {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j))) (i : ι) :
    (multipleCuspNewChart C hD hne i).target = Metric.ball 0 (stableCuspRadius (C i).height) := by
  rw [multipleCuspNewChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    multipleCuspPieceOph_source, preimage_univ, inter_univ, (C i).newChart_target]

theorem multipleCuspNewChart_newPoint_source {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j))) (i : ι) :
    multipleCuspNewPoint C i ∈ (multipleCuspNewChart C hD hne i).source := by
  have hs : (C i).cuspQuotient ∈ (multipleCuspPieceOph C hD hne (some i)).source := by
    rw [multipleCuspPieceOph_source]; trivial
  refine ⟨(multipleCuspPieceOph C hD hne (some i)).map_source hs, ?_⟩
  change (multipleCuspPieceOph C hD hne (some i)).symm
    (multipleCuspPieceOph C hD hne (some i) (C i).cuspQuotient) ∈ ((C i).newChart hD).source
  rw [(multipleCuspPieceOph C hD hne (some i)).left_inv hs]
  exact (C i).newChart_cusp_source hD 1

theorem multipleCuspNewChart_newPoint {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j))) (i : ι) :
    multipleCuspNewChart C hD hne i (multipleCuspNewPoint C i) = 0 := by
  change (C i).newChart hD ((multipleCuspPieceOph C hD hne (some i)).symm
    (multipleCuspPieceOph C hD hne (some i) (C i).cuspQuotient)) = 0
  rw [(multipleCuspPieceOph C hD hne (some i)).left_inv (by rw [multipleCuspPieceOph_source]; trivial)]
  exact (C i).newChart_cusp hD 1

theorem multipleCuspNewPoint_projection {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (i : ι) (g : G) :
    Quotient.mk _ (multipleCuspAugmentedPiece C i
      (mobiusCuspAugmentedCusp (C i) g (stableCuspCompletionInfinity (C i).height))) = multipleCuspNewPoint C i :=
  congrArg (multipleCuspQuotientPiece C i) ((C i).cuspQuotient_eq g)

theorem multipleCuspQuotientOld_projection {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (z : D.carrier) :
    multipleCuspQuotientOld C (mobiusDomainProjection D z) = Quotient.mk _ (multipleCuspAugmentedOld C z) := rfl

/-- The genuine simultaneous filled coordinate retains the literal original exponential. -/
theorem multipleCuspNewChart_exponential {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : ι → MobiusStableSubset D} {w : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : ∀ i, MobiusCuspNormalization (S i) (w i)) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j))) (i : ι)
    (z : stableCuspHalfPlane (C i).height) :
    multipleCuspNewChart C hD hne i
      (multipleCuspQuotientOld C (mobiusDomainProjection D
        ⟨((C i).coordinateToSubset z).val, (S i).subset_domain ((C i).coordinateToSubset z).property⟩)) =
          (complexPeriodExponential 1 z.val).val := by
  rw [← multipleCuspPieceOph_old C hD hne (some i)]
  change (C i).newChart hD ((multipleCuspPieceOph C hD hne (some i)).symm
    (multipleCuspPieceOph C hD hne (some i) ((C i).oldQuotientEmbedding hD _))) = _
  rw [(multipleCuspPieceOph C hD hne (some i)).left_inv (by rw [multipleCuspPieceOph_source]; trivial),
    (C i).oldQuotientEmbedding_projection]
  exact (C i).newChart_exponential hD z

/--
Pairwise inequivalent parabolic cusp orbits admit simultaneous analytic fillings.
Normalization data come from the stable discs, and each full cusp stabilizer is
assumed to preserve its chosen disc.
-/
theorem pairwise_inequivalent_parabolic_cusps_simultaneous_filling_exists {ι : Type*} {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : ι → MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (f : ι →
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : ∀ i, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (f i)) (hDisc : ∀ i,
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc (S i).carrier)
    (hK : ∀ i, (S i).stabilizer = Subgroup.zpowers (f i))
    (w : ι → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hw : ∀ i, (f i).val (w i) = w i)
    (hne : Pairwise (fun i j => ¬MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex (w
      i) (w j)))
    (hfix : ∀ i, ∀ g ∈ G, g.val (w i) = w i → g ∈ (S i).stabilizer) :
    ∃ C : ∀ i, MobiusCuspNormalization (S i) (w i),
    let R := multipleCuspRiemannSurface C hD hne hfix
    RiemannAnalyticMap (mobiusQuotientRiemannSurface D hD).toRiemannAtlas R.toRiemannAtlas (multipleCuspQuotientOld C) ∧
      Topology.IsOpenEmbedding (multipleCuspQuotientOld C) ∧
      Topology.IsOpenEmbedding (multipleCuspAugmentedOld C) ∧
      (∀ z : D.carrier, multipleCuspQuotientOld C (mobiusDomainProjection D z) =
        Quotient.mk _ (multipleCuspAugmentedOld C z)) ∧
      (∀ x : MultipleCuspAugmentedQuotient C,
        x ∈ Set.range (multipleCuspQuotientOld C) ∨ ∃ i, x = multipleCuspNewPoint C i) ∧
      Function.Injective (multipleCuspNewPoint C) ∧
      ∀ i : ι,
        multipleCuspNewPoint C i ∉ Set.range (multipleCuspQuotientOld C) ∧
        (multipleCuspNewChart C hD hne i ∈ R.charts ∧
          (multipleCuspNewChart C hD hne i).target = Metric.ball 0 (stableCuspRadius (C i).height) ∧
          multipleCuspNewPoint C i ∈ (multipleCuspNewChart C hD hne i).source ∧
          multipleCuspNewChart C hD hne i (multipleCuspNewPoint C i) = 0) ∧
        ∀ g : G,
          (¬∃ K : Set (MultipleCuspAugmentedDomain C), IsCompact K ∧
            K ∈ 𝓝 (multipleCuspAugmentedPiece C i
              (mobiusCuspAugmentedCusp (C i) g (stableCuspCompletionInfinity (C i).height)))) ∧
          ∀ U : Set (MultipleCuspAugmentedDomain C),
            U ∈ 𝓝 (multipleCuspAugmentedPiece C i
              (mobiusCuspAugmentedCusp (C i) g (stableCuspCompletionInfinity (C i).height))) ↔
              ∃ t : ℝ, (C i).height < t ∧ multipleCuspHeightTail C i g t ⊆ U := by
  let C : ∀ i, MobiusCuspNormalization (S i) (w i) := fun i =>
    Classical.choice (mobiusCuspNormalization_exists (S i) (f i) (hf i) (hDisc i) (hK i) (w i) (hw i))
  refine ⟨C, multipleCuspQuotientOld_analytic C hD hne hfix,
    multipleCuspQuotientOld_isOpenEmbedding C hD, multipleCuspAugmentedOld_isOpenEmbedding C hD,
    multipleCuspQuotientOld_projection C, multipleCuspQuotient_old_or_new C, ?_, ?_⟩
  · intro i j hij
    by_contra hneij
    exact multipleCuspNewPoint_ne C hne hneij hij
  · intro i
    exact ⟨multipleCuspNewPoint_not_mem_old C hD i,
      ⟨multipleCuspNewChart_mem C hD hne hfix i, multipleCuspNewChart_target C hD hne i,
        multipleCuspNewChart_newPoint_source C hD hne i, multipleCuspNewChart_newPoint C hD hne i⟩,
      fun g => ⟨multipleCusp_no_compact_nhds C hD hne hfix i g, multipleCusp_mem_nhds_iff C hD hne hfix i g⟩⟩

end LowDimensionalTopology.Geometry.Surfaces
