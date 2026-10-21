module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Surfaces.Cusp.CuspFilling
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfSpace.ParabolicHoroballs
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteDihedralGroups
@[expose] public section
noncomputable section
open Set Filter Topology TopologicalSpace
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces

/-- Actual conjugation transports the actual image of every sphere subset. -/
theorem cusp_conjugate_image (q f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (D : Set
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    ((q * f * q⁻¹ : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Equiv.Perm
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
        ((q : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D) =
      (q : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' ((f : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  funext z
  change (q * f * q⁻¹) • (q • z) = q • (f • z)
  simp only [mul_smul, inv_smul_smul]

/-- The holomorphic half-turn reverses the distinguished translation generator. -/
theorem cusp_negScaling_conjugation :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1) * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 * (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1))⁻¹ =
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹ := by
  have hs : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1))⁻¹ = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1) := by
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_inv]
    congr 1
  rw [hs, ← _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_neg]
  apply Subtype.ext
  apply Equiv.ext
  intro z
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    (-1)).val ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1).val
    ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)).val z)) = _
  induction z using OnePoint.rec with
  | infty => simp only [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty,
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty]
  | coe z =>
    simp only [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe, Units.val_neg, Units.val_one,
      neg_one_mul]
    congr 1
    ring

/-- The same genuine holomorphic half-turn exchanges lower and upper horizontal discs. -/
theorem cusp_negScaling_image_lower (h : ℝ) :
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1) : Equiv.Perm
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
      (((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z | z.im < h}) = stableCuspSphere (-h) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨-z, ?_, ?_⟩
    · change -h < (-z).im
      simpa only [Complex.neg_im] using (neg_lt_neg hz)
    · simp only [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe, Units.val_neg, Units.val_one,
      neg_one_mul]
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨((-z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ⟨-z, ?_, rfl⟩, ?_⟩
    · change (-z).im < h
      change -h < z.im at hz
      simpa only [Complex.neg_im, neg_neg] using (neg_lt_neg hz)
    · simp only [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe, Units.val_neg, Units.val_one,
      neg_one_mul, neg_neg]

/-- A genuine disc preserved by a parabolic is normalized to the literal upper
horizontal model. The specified generator may become the inverse translation. -/
theorem parabolic_disc_signed_normalization (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) {D : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (hstable : (f : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D = D) :
    ∃ (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (h : ℝ),
      (q : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D = stableCuspSphere h ∧
      (q * f * q⁻¹ = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∨ q * f * q⁻¹ = (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹) := by
  obtain ⟨a, ha⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.parabolic_translation_conjugate f hf
  let q := a⁻¹
  have hq : q * f * q⁻¹ = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 := by
    dsimp only [q]
    rw [ha]
    group
  have hpres : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 : Equiv.Perm
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
      ((q : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D) = (q : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D := by
    rw [← hq, cusp_conjugate_image, hstable]
  obtain ⟨h, hu | hl⟩ := parabolicTranslationDisc_eq_halfPlane (hD.image q) hpres
  · exact ⟨q, h, hu, Or.inl hq⟩
  · refine ⟨_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1) * q, -h, ?_, Or.inr ?_⟩
    · change ((fun z => (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)).val (q.val z)) '' D) = _
      rw [← Set.image_image, hl, cusp_negScaling_image_lower]
    · calc
        (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1) *
          q) * f * (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1) * q)⁻¹ =
            _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1) * (q * f * q⁻¹) * (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1))⁻¹ := by group
        _ = (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹ := by rw [hq, cusp_negScaling_conjugation]

/-- The same normalization identifies the original cyclic group exactly, including
when the preferred generator is reversed by the lower-half-plane branch. -/
theorem parabolic_disc_cyclic_normalization (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) {D : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (hstable : (f : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D = D) :
    ∃ (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (h : ℝ),
      (q : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D = stableCuspSphere h ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (Subgroup.zpowers f) = stableTranslationGroup := by
  obtain ⟨q, h, hD', hg⟩ := parabolic_disc_signed_normalization f hf hD hstable
  refine ⟨q, h, hD', ?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate, MonoidHom.map_zpowers]
  change Subgroup.zpowers (q * f *
    q⁻¹) = Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)
  rcases hg with hg | hg
  · rw [hg]
  · rw [hg, Subgroup.zpowers_inv]

/-- Actual conjugation of an entire invariant sphere domain and its acting subgroup. -/
def MobiusInvariantDomain.conjugate {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    MobiusInvariantDomain (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      G) where
  carrier := q.val '' D.carrier
  isOpen := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).isOpenMap _ D.isOpen
  isConnected := D.isConnected.image q.val (_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary
    q).continuousOn
  invariant f p hp := by
    obtain ⟨g, hg, hgf⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q G f.val).mp f.property
    obtain ⟨z, hz, rfl⟩ := hp
    refine ⟨g.val z, D.invariant ⟨g, hg⟩ z hz, ?_⟩
    change q.val (g.val z) = f.val.val (q.val z)
    rw [← hgf]
    change q • (g • z) = (q * g * q⁻¹) • (q • z)
    simp only [mul_smul, inv_smul_smul]

def MobiusInvariantDomain.conjugateHomeomorph {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : D.carrier ≃ₜ (D.conjugate q).carrier :=
  (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).isEmbedding.homeomorphImage D.carrier

theorem MobiusInvariantDomain.conjugateHomeomorph_equivariant {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (g : G) (z :
      D.carrier) :
    D.conjugateHomeomorph q (g • z) =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q G g • D.conjugateHomeomorph q z := by
  apply Subtype.ext
  change q • (g.val • z.val) = (q * g.val * q⁻¹) • (q • z.val)
  simp only [mul_smul, inv_smul_smul]

theorem MobiusInvariantDomain.conjugate_discontinuous {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G) (D.conjugate q).carrier := by
  have hd : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous G D.carrier :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_iff_subtype G D.carrier
      D.invariant).mp hD
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_iff_subtype
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G)
    (D.conjugate q).carrier (D.conjugate q).invariant).mpr
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous.transport
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q G).toEquiv
        (D.conjugateHomeomorph q) (D.conjugateHomeomorph_equivariant q) hd)

/-- Genuine stable subsets and their original full-group separation are conjugated together. -/
def MobiusStableSubset.conjugate {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : MobiusStableSubset (D.conjugate q) where
  carrier := q.val '' S.carrier
  subset_domain := Set.image_mono S.subset_domain
  stable f hf := by
    obtain ⟨g, hg, rfl⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q G f).mp hf
    rw [cusp_conjugate_image]
    rcases S.stable g hg with hs | hd
    · exact Or.inl (congrArg (Set.image q.val) hs)
    · right
      apply Set.disjoint_left.mpr
      rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
      have huv := q.val.injective he
      subst v
      exact Set.disjoint_left.mp hd hu hv

theorem MobiusStableSubset.conjugate_stabilizer {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    (S.conjugate q).stabilizer = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q S.stabilizer := by
  ext f
  constructor
  · intro hf
    have hfG := (S.conjugate q).stabilizer_le hf
    obtain ⟨g, hgG, hgf⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q G f).mp hfG
    refine (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
      S.stabilizer f).mpr ⟨g, ?_, hgf⟩
    apply (mem_mobiusSetStabilizer G S.carrier g).mpr
    refine ⟨hgG, ?_⟩
    have hs := ((mem_mobiusSetStabilizer _ _ f).mp hf).2
    change f.val '' (q.val '' S.carrier) = q.val '' S.carrier at hs
    rw [← hgf, cusp_conjugate_image] at hs
    exact (Set.image_injective.mpr q.val.injective) hs
  · intro hf
    obtain ⟨g, hg, rfl⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q S.stabilizer f).mp hf
    apply (mem_mobiusSetStabilizer _ _ _).mpr
    constructor
    · exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q G
      _).mpr ⟨g, S.stabilizer_le hg, rfl⟩
    · change (q * g * q⁻¹).val '' (q.val '' S.carrier) = q.val '' S.carrier
      rw [cusp_conjugate_image, ((mem_mobiusSetStabilizer _ _ g).mp hg).2]

/-- Conjugation identifies the original full-group orbit quotient topologically. -/
def MobiusInvariantDomain.conjugateQuotientHomeomorph {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    MobiusDomainQuotient D ≃ₜ MobiusDomainQuotient (D.conjugate q) := by
  let e := D.conjugateHomeomorph q
  let φ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q G
  apply Homeomorph.Quotient.congr e
  intro z w
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨φ g, (D.conjugateHomeomorph_equivariant q g w).symm.trans (congrArg e hg)⟩
  · rintro ⟨g, hg⟩
    refine ⟨φ.symm g, ?_⟩
    apply e.injective
    exact (D.conjugateHomeomorph_equivariant q (φ.symm g) w).trans
      ((congrArg (fun k => k • e w) (φ.apply_symm_apply g)).trans hg)

theorem MobiusInvariantDomain.conjugateQuotientHomeomorph_projection {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (z :
      D.carrier) :
    D.conjugateQuotientHomeomorph q (mobiusDomainProjection D z) =
      mobiusDomainProjection (D.conjugate q) (D.conjugateHomeomorph q z) := rfl

/-- A source normalizer followed by an actual Mobius map gives the exact pulled-back disc. -/
theorem mobiusNormalizedDisc_mul_preimage (a q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (r :
  ℝ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc (a * q) r = q.val ⁻¹' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc a r := by
  ext z
  constructor
  · intro hz
    obtain ⟨u, hu, hqu⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusNormalizedDisc (a * q) r
      z).mp hz
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusNormalizedDisc a r (q.val z)).mpr ⟨u, hu,
      hqu⟩
  · intro hz
    obtain ⟨u, hu, hqu⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusNormalizedDisc a r (q.val
      z)).mp hz
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusNormalizedDisc (a * q) r z).mpr ⟨u, hu, hqu⟩

theorem MobiusQuotientChartData.chart_projection_finite {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (C : MobiusQuotientChartData D) (z : C.disc) :
    C.chart (mobiusDomainProjection D ⟨z.val, C.disc_subset z.property⟩) =
      sphereFiniteChart (C.normalizer.val z.val) ^ C.degree := by
  have hc : sphereFiniteChart (C.normalizer.val z.val) = (C.coordinate z).val := by
    simpa only [sphereFiniteChart_coe] using congrArg sphereFiniteChart (C.coordinate_coe z)
  exact (C.chart_apply_projection z).trans (congrArg (fun w : ℂ => w ^ C.degree) hc.symm)

/-- Actual full-group conjugation is analytic for both original branched quotient atlases,
including elliptic branch values. -/
theorem MobiusInvariantDomain.conjugateQuotientHomeomorph_analytic {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) :
    RiemannAnalyticMap (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
      (mobiusQuotientRiemannSurface (D.conjugate q) (D.conjugate_discontinuous q hD)).toRiemannAtlas
      (D.conjugateQuotientHomeomorph q) := by
  let F := D.conjugateQuotientHomeomorph q
  refine ⟨F.continuous, ?_⟩
  rintro _ ⟨C, rfl⟩ _ ⟨B, rfl⟩
  let f := F.toOpenPartialHomeomorph.trans B.chart
  have hN : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc (B.normalizer * q) B.radius ⊆ D.carrier := by
    intro z hz
    rw [mobiusNormalizedDisc_mul_preimage] at hz
    obtain ⟨w, hw, he⟩ := B.disc_subset hz
    exact q.val.injective he ▸ hw
  have hfS : f.source = Set.range (fun z : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc
    (B.normalizer * q) B.radius =>
      mobiusDomainProjection D ⟨z.val, hN z.property⟩) := by
    ext p
    change (p ∈ Set.univ ∧ F p ∈ B.chart.source) ↔ _
    constructor
    · rintro ⟨_, hp⟩
      obtain ⟨b, hb⟩ := B.chart_source ▸ hp
      obtain ⟨z, hz⟩ := (D.conjugateHomeomorph q).surjective ⟨b.val, B.disc_subset b.property⟩
      have hzv : q.val z.val = b.val := congrArg Subtype.val hz
      have hzn : z.val ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc (B.normalizer * q) B.radius := by
        rw [mobiusNormalizedDisc_mul_preimage]
        change q.val z.val ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc B.normalizer B.radius
        exact hzv.symm ▸ b.property
      refine ⟨⟨z.val, hzn⟩, ?_⟩
      apply F.injective
      exact (D.conjugateQuotientHomeomorph_projection q z).trans
        ((congrArg (mobiusDomainProjection (D.conjugate q)) hz).trans hb)
    · rintro ⟨z, rfl⟩
      refine ⟨Set.mem_univ _, ?_⟩
      rw [D.conjugateQuotientHomeomorph_projection]
      rw [B.chart_source]
      refine ⟨⟨q.val z.val, ?_⟩, rfl⟩
      exact (Set.ext_iff.mp (mobiusNormalizedDisc_mul_preimage B.normalizer q B.radius) z.val).mp z.property
  have hfP : ∀ z : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc (B.normalizer *
    q) B.radius,
      f (mobiusDomainProjection D ⟨z.val, hN z.property⟩) =
        sphereFiniteChart ((B.normalizer * q).val z.val) ^ B.degree := by
    intro z
    change B.chart (F (mobiusDomainProjection D ⟨z.val, hN z.property⟩)) = _
    rw [D.conjugateQuotientHomeomorph_projection]
    let b : B.disc := ⟨q.val z.val,
      (Set.ext_iff.mp (mobiusNormalizedDisc_mul_preimage B.normalizer q B.radius) z.val).mp z.property⟩
    exact B.chart_projection_finite b
  have ha := mobius_power_quotient_charts_compatible D C.normalizer (B.normalizer * q)
    C.radius B.radius B.radius_pos C.degree B.degree C.degree_pos.ne' C.disc_subset hN
    C.chart f C.chart_source hfS C.chart_projection_finite hfP
  have hd : riemannChartMapDomain C.chart F B.chart = (C.chart.symm.trans f).source := by
    ext z
    change (z ∈ C.chart.target ∧ F (C.chart.symm z) ∈ B.chart.source) ↔
      (z ∈ C.chart.target ∧ C.chart.symm z ∈ Set.univ ∧ F (C.chart.symm z) ∈ B.chart.source)
    simp only [Set.mem_univ, true_and]
  rw [hd]
  exact ha

/-- Genuine normalization data for an arbitrary original stable parabolic disc and cusp. -/
structure MobiusCuspNormalization {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) where
  normalizer : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup
  height : ℝ
  disc_eq : normalizer.val '' S.carrier = stableCuspSphere height
  stabilizer_eq : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate normalizer S.stabilizer = stableTranslationGroup
  cusp_eq : normalizer.val w = ∞

theorem MobiusCuspNormalization.normalized_disc_eq {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) :
    (S.conjugate C.normalizer).carrier = stableCuspSphere C.height := C.disc_eq

/-- Every original stable genuine parabolic disc has the full normalized data, including
its specified actual fixed cusp and its precise cyclic stabilizer. -/
theorem mobiusCuspNormalization_exists {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hDisc : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc S.carrier) (hK : S.stabilizer =
      Subgroup.zpowers f)
    (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hw : f.val w = w) : Nonempty (MobiusCuspNormalization S w) := by
  have hfK : f ∈ S.stabilizer := hK.symm ▸ Subgroup.mem_zpowers f
  have hpres := ((mem_mobiusSetStabilizer _ _ f).mp hfK).2
  obtain ⟨q, h, hQ, hC⟩ := parabolic_disc_cyclic_normalization f hf hDisc hpres
  have hKq : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q S.stabilizer = stableTranslationGroup := by rw [hK]; exact hC
  have hfc : q * f * q⁻¹ ∈ stableTranslationGroup := hKq ▸
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q S.stabilizer
      _).mpr ⟨f, hfK, rfl⟩
  obtain ⟨n, hn⟩ := (stableTranslationGroup_mem _).mp hfc
  have hfix : (q * f * q⁻¹).val ∞ = ∞ := by rw [hn]; exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty _
  have hw0 := (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_conjugate_boundary_fixed_iff f q ∞).mp hfix
  obtain ⟨a, ha⟩ := hf.2
  have hww : w = q.val.symm ∞ := ((ha w).mp hw).trans ((ha (q.val.symm ∞)).mp hw0).symm
  exact ⟨⟨q, h, hQ, hKq, by rw [hww, Equiv.apply_symm_apply]⟩⟩

theorem MobiusCuspNormalization.normalized_stabilizer {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) :
    (S.conjugate C.normalizer).stabilizer = stableTranslationGroup :=
  (S.conjugate_stabilizer C.normalizer).trans C.stabilizer_eq

/-- The necessary full-cusp stabilizer repair is preserved by actual full-group normalization. -/
theorem MobiusCuspNormalization.cusp_stabilizer_condition {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w)
    (hfix : ∀ f ∈ G, f.val w = w → f ∈ S.stabilizer) :
    ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer G, f.val ∞ = ∞ → f ∈ stableTranslationGroup := by
  intro f hf hfi
  obtain ⟨g, hg, hgf⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
    C.normalizer G f).mp hf
  have hgw : g.val w = w := by
    apply C.normalizer.val.injective
    have he : f.val (C.normalizer.val w) = C.normalizer.val (g.val w) := by
      rw [← hgf]
      change C.normalizer • (g • (C.normalizer⁻¹ • (C.normalizer • w))) = C.normalizer • (g • w)
      rw [inv_smul_smul]
    exact he.symm.trans (by rw [C.cusp_eq]; exact hfi)
  exact C.stabilizer_eq ▸ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff C.normalizer S.stabilizer f).mpr
    ⟨g, hfix g hg hgw, hgf⟩

theorem MobiusCuspNormalization.inverse_cusp {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) : C.normalizer.val.symm ∞ = w := by
  apply C.normalizer.val.injective
  rw [Equiv.apply_symm_apply, C.cusp_eq]

/-- Literal finite cusp coordinates in the original original stable disc. -/
def MobiusCuspNormalization.coordinateToSubset {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (z : stableCuspHalfPlane C.height) : S.carrier := by
  refine ⟨C.normalizer.val.symm (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ?_⟩
  have hz : (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ C.normalizer.val '' S.carrier := by
    rw [C.disc_eq]
    exact ⟨z.val, z.property, rfl⟩
  obtain ⟨a, ha, he⟩ := hz
  have hea : a = C.normalizer.val.symm (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
    C.normalizer.val.injective (he.trans (C.normalizer.val.apply_symm_apply _).symm)
  exact hea ▸ ha

theorem MobiusCuspNormalization.conjugate_cusp {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (g : G) :
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer G
      g).val.val ∞ =
      C.normalizer.val (g.val.val w) := by
  change (C.normalizer * g.val * C.normalizer⁻¹) • (∞ :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = C.normalizer • (g.val • w)
  calc
    _ = (C.normalizer * g.val * C.normalizer⁻¹) • (C.normalizer • w) :=
      congrArg (fun x => (C.normalizer * g.val * C.normalizer⁻¹) • x) C.cusp_eq.symm
    _ = C.normalizer • (g.val • w) := by simp only [mul_smul, inv_smul_smul]

/-- The genuine physical augmented carrier is carried to the genuine normalized carrier. -/
theorem MobiusCuspNormalization.augmented_carrier_iff {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    (p ∈ D.carrier ∨ ∃ g : G, g.val.val w = p) ↔
      (C.normalizer.val p ∈ (D.conjugate C.normalizer).carrier ∨
        ∃ k : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer G, k.val.val ∞ = C.normalizer.val p) := by
  constructor
  · rintro (hp | ⟨g, hg⟩)
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
      C.normalizer G g,
        (C.conjugate_cusp g).trans (congrArg C.normalizer.val hg)⟩
  · rintro (⟨a, ha, he⟩ | ⟨k, hk⟩)
    · exact Or.inl (C.normalizer.val.injective he ▸ ha)
    · obtain ⟨g, hg⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer G).surjective k
      refine Or.inr ⟨g, C.normalizer.val.injective ?_⟩
      exact (C.conjugate_cusp g).symm.trans ((congrArg (fun f => f.val.val ∞) hg).trans hk)

/-- The arbitrary original domain with the actual full orbit of its actual cusp adjoined. -/
def MobiusCuspAugmentedDomain {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (_S : MobiusStableSubset D) (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (_C :
      MobiusCuspNormalization _S w) :=
  {p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex // p ∈ D.carrier ∨ ∃ g : G, g.val.val w = p}

def mobiusCuspAugmentedSphere {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    {S : MobiusStableSubset D} {w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (C :
      MobiusCuspNormalization S w) :
    MobiusCuspAugmentedDomain S w C → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := Subtype.val

/-- The actual sphere-coordinate bijection is the original Mobius normalization. -/
def MobiusCuspNormalization.augmentedEquiv {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) :
    MobiusCuspAugmentedDomain S w C ≃
      StableCuspAugmentedDomain (S.conjugate C.normalizer) C.height C.normalized_disc_eq where
  toFun p := ⟨C.normalizer.val p.val, (C.augmented_carrier_iff p.val).mp p.property⟩
  invFun p := ⟨C.normalizer.val.symm p.val, (C.augmented_carrier_iff _).mpr
    (by simpa only [Equiv.apply_symm_apply] using p.property)⟩
  left_inv p := Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv p := Subtype.ext (Equiv.apply_symm_apply _ _)

/-- Original finite points are included without changing their sphere coordinates. -/
def mobiusCuspAugmentedOld {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    {S : MobiusStableSubset D} {w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (C :
      MobiusCuspNormalization S w) :
    D.carrier → MobiusCuspAugmentedDomain S w C := fun z => ⟨z.val, Or.inl z.property⟩

/-- The actual original cusp charts use g applied after the inverse normalizer. -/
def mobiusCuspAugmentedCusp {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    {S : MobiusStableSubset D} {w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (C :
      MobiusCuspNormalization S w) (g : G) :
    StableCuspCompletion C.height → MobiusCuspAugmentedDomain S w C :=
  Option.rec ⟨g.val.val w, Or.inr ⟨g, rfl⟩⟩
    (fun z => ⟨g.val.val (C.coordinateToSubset z).val,
      Or.inl (D.invariant g _ (S.subset_domain (C.coordinateToSubset z).property))⟩)

/-- The original augmented topology is generated by the original finite domain and its
actual translated completed cusp charts. -/
instance mobiusCuspAugmentedTopology {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) : TopologicalSpace (MobiusCuspAugmentedDomain S w C) :=
  TopologicalSpace.coinduced (mobiusCuspAugmentedOld C) inferInstance ⊔
    ⨆ g : G, TopologicalSpace.coinduced (mobiusCuspAugmentedCusp C g) inferInstance

theorem mobiusCuspAugmented_isOpen_iff {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (U : Set (MobiusCuspAugmentedDomain S w C)) :
    IsOpen U ↔ IsOpen ((mobiusCuspAugmentedOld C) ⁻¹' U) ∧
      ∀ g : G, IsOpen ((mobiusCuspAugmentedCusp C g) ⁻¹' U) :=
  isOpen_sup.trans (and_congr Iff.rfl isOpen_iSup_iff)

theorem mobiusCuspAugmentedOld_continuous {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) : Continuous (mobiusCuspAugmentedOld C) := by
  apply continuous_def.mpr
  intro U hU
  exact ((mobiusCuspAugmented_isOpen_iff C U).mp hU).1

theorem mobiusCuspAugmentedCusp_continuous {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (g : G) : Continuous (mobiusCuspAugmentedCusp C g) := by
  apply continuous_def.mpr
  intro U hU
  exact ((mobiusCuspAugmented_isOpen_iff C U).mp hU).2 g

theorem MobiusCuspNormalization.augmentedEquiv_old {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (z : D.carrier) :
    C.augmentedEquiv (mobiusCuspAugmentedOld C z) =
      stableCuspAugmentedOld (S.conjugate C.normalizer) C.height C.normalized_disc_eq
        (D.conjugateHomeomorph C.normalizer z) := rfl

theorem MobiusCuspNormalization.augmentedEquiv_cusp {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (g : G) (p : StableCuspCompletion C.height) :
    C.augmentedEquiv (mobiusCuspAugmentedCusp C g p) =
      stableCuspAugmentedCusp (S.conjugate C.normalizer) C.height C.normalized_disc_eq
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer G g) p := by
  cases p with
  | none => exact Subtype.ext (C.conjugate_cusp g).symm
  | some z =>
    apply Subtype.ext
    change C.normalizer • (g.val • (C.normalizer⁻¹ • (z.val :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))) =
      (C.normalizer * g.val * C.normalizer⁻¹) • (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    simp only [mul_smul]

theorem MobiusCuspNormalization.augmentedEquiv_symm_old {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (z : (D.conjugate C.normalizer).carrier) :
    C.augmentedEquiv.symm (stableCuspAugmentedOld (S.conjugate C.normalizer) C.height C.normalized_disc_eq z) =
      mobiusCuspAugmentedOld C ((D.conjugateHomeomorph C.normalizer).symm z) := by
  apply C.augmentedEquiv.injective
  rw [Equiv.apply_symm_apply, C.augmentedEquiv_old, Homeomorph.apply_symm_apply]

theorem MobiusCuspNormalization.augmentedEquiv_symm_cusp {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (g :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer G)
    (p : StableCuspCompletion C.height) :
    C.augmentedEquiv.symm (stableCuspAugmentedCusp (S.conjugate C.normalizer) C.height C.normalized_disc_eq g p) =
      mobiusCuspAugmentedCusp C ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer G).symm g) p := by
  apply C.augmentedEquiv.injective
  rw [Equiv.apply_symm_apply, C.augmentedEquiv_cusp, MulEquiv.apply_symm_apply]

/-- Actual normalization is a homeomorphism for the actual original and normalized
augmented-domain topologies, not merely a bijection of abstract models. -/
def MobiusCuspNormalization.augmentedHomeomorph {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) :
    MobiusCuspAugmentedDomain S w C ≃ₜ
      StableCuspAugmentedDomain (S.conjugate C.normalizer) C.height C.normalized_disc_eq where
  toEquiv := C.augmentedEquiv
  continuous_toFun := by
    apply continuous_def.mpr
    intro U hU
    apply (mobiusCuspAugmented_isOpen_iff C _).mpr
    constructor
    · have he : C.augmentedEquiv ∘ mobiusCuspAugmentedOld C =
          stableCuspAugmentedOld (S.conjugate C.normalizer) C.height C.normalized_disc_eq ∘
            D.conjugateHomeomorph C.normalizer := funext C.augmentedEquiv_old
      change IsOpen ((C.augmentedEquiv ∘ mobiusCuspAugmentedOld C) ⁻¹' U)
      rw [he]
      exact hU.preimage ((stableCuspAugmentedOld_continuous _ _ _).comp
        (D.conjugateHomeomorph C.normalizer).continuous)
    · intro g
      have he : C.augmentedEquiv ∘ mobiusCuspAugmentedCusp C g =
          stableCuspAugmentedCusp (S.conjugate C.normalizer) C.height C.normalized_disc_eq
            (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
              C.normalizer G g) := funext (C.augmentedEquiv_cusp g)
      change IsOpen ((C.augmentedEquiv ∘ mobiusCuspAugmentedCusp C g) ⁻¹' U)
      rw [he]
      exact hU.preimage (stableCuspAugmentedCusp_continuous _ _ _ _)
  continuous_invFun := by
    apply continuous_def.mpr
    intro U hU
    apply (stableCuspAugmented_isOpen_iff (S.conjugate C.normalizer) C.height C.normalized_disc_eq _).mpr
    constructor
    · have he : C.augmentedEquiv.symm ∘ stableCuspAugmentedOld (S.conjugate
      C.normalizer) C.height C.normalized_disc_eq =
          mobiusCuspAugmentedOld C ∘ (D.conjugateHomeomorph C.normalizer).symm :=
        funext C.augmentedEquiv_symm_old
      change IsOpen ((C.augmentedEquiv.symm ∘ stableCuspAugmentedOld (S.conjugate C.normalizer) C.height
        C.normalized_disc_eq) ⁻¹' U)
      rw [he]
      exact hU.preimage ((mobiusCuspAugmentedOld_continuous C).comp
        (D.conjugateHomeomorph C.normalizer).symm.continuous)
    · intro g
      have he : C.augmentedEquiv.symm ∘ stableCuspAugmentedCusp (S.conjugate
        C.normalizer) C.height C.normalized_disc_eq g =
          mobiusCuspAugmentedCusp C ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer G).symm g) :=
        funext (C.augmentedEquiv_symm_cusp g)
      change IsOpen ((C.augmentedEquiv.symm ∘ stableCuspAugmentedCusp (S.conjugate C.normalizer) C.height
        C.normalized_disc_eq g) ⁻¹' U)
      rw [he]
      exact hU.preimage (mobiusCuspAugmentedCusp_continuous C _)

/-- The original actual full group acts on the original augmented sphere domain. -/
instance mobiusCuspAugmentedAction {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) : MulAction G (MobiusCuspAugmentedDomain S w C) where
  smul g p := ⟨g • p.val, by
    rcases p.property with hp | ⟨k, hk⟩
    · exact Or.inl (D.invariant g p.val hp)
    · refine Or.inr ⟨g * k, ?_⟩
      change (g * k) • w = g • p.val
      rw [mul_smul]
      exact congrArg (fun z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex => g • z) hk⟩
  one_smul p := Subtype.ext (one_smul G p.val)
  mul_smul g k p := Subtype.ext (mul_smul g k p.val)

theorem MobiusCuspNormalization.augmentedHomeomorph_equivariant {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (g : G) (p : MobiusCuspAugmentedDomain S w C) :
    C.augmentedHomeomorph (g • p) =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer G g • C.augmentedHomeomorph p := by
  apply Subtype.ext
  change C.normalizer • (g.val • p.val) =
    (C.normalizer * g.val * C.normalizer⁻¹) • (C.normalizer • p.val)
  simp only [mul_smul, inv_smul_smul]

instance mobiusCuspAugmentedContinuousConstSMul {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) : ContinuousConstSMul G (MobiusCuspAugmentedDomain S w C) where
  continuous_const_smul g := by
    let E := C.augmentedHomeomorph
    let φ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer G
    have hn : Continuous (fun z : StableCuspAugmentedDomain (S.conjugate C.normalizer) C.height C.normalized_disc_eq =>
        φ g • z) := continuous_const_smul (φ g)
    have he : (fun p : MobiusCuspAugmentedDomain S w C => g • p) =
        E.symm ∘ (fun z => φ g • z) ∘ E := by
      funext p
      apply E.injective
      exact (C.augmentedHomeomorph_equivariant g p).trans (E.apply_symm_apply _).symm
    rw [he]
    exact E.symm.continuous.comp (hn.comp E.continuous)

/-- The actual original extended-action orbit quotient. -/
abbrev MobiusCuspAugmentedQuotient {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) := Quotient (MulAction.orbitRel G (MobiusCuspAugmentedDomain S w C))

/-- Actual normalization identifies the actual original full-group augmented orbit quotient. -/
def MobiusCuspNormalization.augmentedQuotientHomeomorph {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) :
    MobiusCuspAugmentedQuotient C ≃ₜ
      StableCuspAugmentedQuotient (S.conjugate C.normalizer) C.height C.normalized_disc_eq := by
  let φ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer G
  let E := C.augmentedHomeomorph
  have he : ∀ p q : MobiusCuspAugmentedDomain S w C,
      MulAction.orbitRel G (MobiusCuspAugmentedDomain S w C) p q ↔
        MulAction.orbitRel (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
          C.normalizer G)
          (StableCuspAugmentedDomain (S.conjugate C.normalizer) C.height C.normalized_disc_eq) (E p) (E q) := by
    intro p q
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨φ g, (C.augmentedHomeomorph_equivariant g q).symm.trans (congrArg E hg)⟩
    · rintro ⟨g, hg⟩
      refine ⟨φ.symm g, ?_⟩
      apply E.injective
      exact (C.augmentedHomeomorph_equivariant (φ.symm g) q).trans
        ((congrArg (fun k => k • E q) (φ.apply_symm_apply g)).trans hg)
  exact (Homeomorph.Quotient.congr E he).trans
    (stableCuspAugmentedNativeQuotientHomeomorph (S.conjugate C.normalizer) C.height C.normalized_disc_eq)

theorem MobiusCuspNormalization.augmentedQuotientHomeomorph_projection {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (p : MobiusCuspAugmentedDomain S w C) :
    C.augmentedQuotientHomeomorph (Quotient.mk _ p) = Quotient.mk _ (C.augmentedHomeomorph p) := rfl

theorem MobiusCuspNormalization.normalized_open {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) : IsOpen (S.conjugate C.normalizer).carrier := by
  rw [C.normalized_disc_eq]
  exact stableCuspSphere_isOpen C.height

theorem MobiusCuspNormalization.normalized_connected {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) : IsConnected (S.conjugate C.normalizer).carrier := by
  rw [C.normalized_disc_eq]
  exact stableCuspSphere_isConnected C.height

theorem MobiusCuspNormalization.normalized_translation_mem {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer G := by
  apply (S.conjugate C.normalizer).stabilizer_le
  rw [C.normalized_stabilizer]
  exact (stableTranslationGroup_mem _).mpr ⟨1, by norm_num⟩

/-- The previously constructed genuine normalized filled quotient surface. -/
def MobiusCuspNormalization.normalizedFilledSurface {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hfix : ∀ f ∈ G, f.val w = w → f ∈ S.stabilizer) :
    RiemannSurface (StableCuspAugmentedQuotient (S.conjugate C.normalizer) C.height C.normalized_disc_eq) :=
  stableCuspAugmentedQuotientRiemannSurface (S.conjugate C.normalizer)
    (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
    C.normalized_stabilizer C.normalized_open C.normalized_connected (C.cusp_stabilizer_condition hfix)

/-- The actual original augmented full-group quotient is a genuine Riemann surface. -/
def MobiusCuspNormalization.filledQuotientRiemannSurface {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hfix : ∀ f ∈ G, f.val w = w → f ∈ S.stabilizer) : RiemannSurface (MobiusCuspAugmentedQuotient C) := by
  let R := C.normalizedFilledSurface hD hfix
  let E := C.augmentedQuotientHomeomorph
  letI : T2Space (StableCuspAugmentedQuotient (S.conjugate C.normalizer) C.height C.normalized_disc_eq) := R.t2Space
  letI : ConnectedSpace (StableCuspAugmentedQuotient (S.conjugate C.normalizer) C.height
    C.normalized_disc_eq) := R.connectedSpace
  exact { R.toRiemannAtlas.liftLocalHomeomorph E E.isOpenEmbedding.isLocalHomeomorph with
    t2Space := E.isEmbedding.t2Space
    connectedSpace := E.symm.surjective.connectedSpace E.symm.continuous }

/-- The canonical old quotient inclusion is induced by the actual original representatives. -/
def MobiusCuspNormalization.oldQuotientEmbedding {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) :
    MobiusDomainQuotient D → MobiusCuspAugmentedQuotient C :=
  C.augmentedQuotientHomeomorph.symm ∘
    stableCuspAugmentedQuotientOld (S.conjugate C.normalizer)
      (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
      C.normalized_stabilizer C.normalized_open C.normalized_connected ∘
    D.conjugateQuotientHomeomorph C.normalizer

theorem MobiusCuspNormalization.oldQuotientEmbedding_projection {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (z : D.carrier) :
    C.oldQuotientEmbedding hD (mobiusDomainProjection D z) =
      Quotient.mk _ (mobiusCuspAugmentedOld C z) := by
  apply C.augmentedQuotientHomeomorph.injective
  change C.augmentedQuotientHomeomorph (C.augmentedQuotientHomeomorph.symm _) = _
  rw [Homeomorph.apply_symm_apply, Function.comp_apply, D.conjugateQuotientHomeomorph_projection,
    stableCuspAugmentedQuotientOld_projection, C.augmentedQuotientHomeomorph_projection]
  exact congrArg (Quotient.mk _) (C.augmentedEquiv_old z).symm

theorem MobiusCuspNormalization.oldQuotientEmbedding_isOpenEmbedding {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) :
    Topology.IsOpenEmbedding (C.oldQuotientEmbedding hD) :=
  C.augmentedQuotientHomeomorph.symm.isOpenEmbedding.comp
    ((stableCuspAugmentedQuotientOld_isOpenEmbedding (S.conjugate C.normalizer)
      (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
      C.normalized_stabilizer C.normalized_open C.normalized_connected).comp
        (D.conjugateQuotientHomeomorph C.normalizer).isOpenEmbedding)

theorem MobiusCuspNormalization.oldQuotientEmbedding_analytic {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hfix : ∀ f ∈ G, f.val w = w → f ∈ S.stabilizer) :
    RiemannAnalyticMap (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
      (C.filledQuotientRiemannSurface hD hfix).toRiemannAtlas (C.oldQuotientEmbedding hD) := by
  have hp := (C.normalizedFilledSurface hD hfix).toRiemannAtlas.liftLocalHomeomorph_projection_analytic
    C.augmentedQuotientHomeomorph C.augmentedQuotientHomeomorph.isOpenEmbedding.isLocalHomeomorph
  have ha := (stableCuspAugmentedQuotientOld_analytic (S.conjugate C.normalizer)
    (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
    C.normalized_stabilizer C.normalized_open C.normalized_connected (C.cusp_stabilizer_condition hfix)).comp
      (D.conjugateQuotientHomeomorph_analytic C.normalizer hD)
  have heq : C.augmentedQuotientHomeomorph ∘ C.oldQuotientEmbedding hD =
      stableCuspAugmentedQuotientOld (S.conjugate C.normalizer)
        (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
        C.normalized_stabilizer C.normalized_open C.normalized_connected ∘
      D.conjugateQuotientHomeomorph C.normalizer := by
    funext x
    exact C.augmentedQuotientHomeomorph.apply_symm_apply _
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_localHomeomorph hp
    C.augmentedQuotientHomeomorph.isOpenEmbedding.isLocalHomeomorph
    (C.oldQuotientEmbedding_isOpenEmbedding hD).continuous
  rw [heq]
  exact ha

theorem MobiusCuspNormalization.cusp_isOpenEmbedding {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hfix : ∀ f ∈ G, f.val w = w → f ∈ S.stabilizer) (g : G) :
    Topology.IsOpenEmbedding (mobiusCuspAugmentedCusp C g) := by
  have he : mobiusCuspAugmentedCusp C g = C.augmentedHomeomorph.symm ∘
      stableCuspAugmentedCusp (S.conjugate C.normalizer) C.height C.normalized_disc_eq
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer G g) := by
    funext p
    apply C.augmentedHomeomorph.injective
    exact (C.augmentedEquiv_cusp g p).trans (C.augmentedHomeomorph.apply_symm_apply _).symm
  rw [he]
  exact C.augmentedHomeomorph.symm.isOpenEmbedding.comp
    (stableCuspAugmentedCusp_isOpenEmbedding (S.conjugate C.normalizer)
      (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
      C.normalized_stabilizer (C.cusp_stabilizer_condition hfix) _)

theorem MobiusCuspNormalization.old_isOpenEmbedding {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) :
    Topology.IsOpenEmbedding (mobiusCuspAugmentedOld C) := by
  have he : mobiusCuspAugmentedOld C = C.augmentedHomeomorph.symm ∘
      stableCuspAugmentedOld (S.conjugate C.normalizer) C.height C.normalized_disc_eq ∘
        D.conjugateHomeomorph C.normalizer := by
    funext z
    apply C.augmentedHomeomorph.injective
    exact (C.augmentedEquiv_old z).trans (C.augmentedHomeomorph.apply_symm_apply _).symm
  rw [he]
  exact C.augmentedHomeomorph.symm.isOpenEmbedding.comp
    ((stableCuspAugmentedOld_isOpenEmbedding (S.conjugate C.normalizer)
      (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq).comp
        (D.conjugateHomeomorph C.normalizer).isOpenEmbedding)

/-- The literal original-point all-group height tail in its actual normalization coordinate. -/
def mobiusCuspAugmentedHeightTail {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (g : G) (t : ℝ) : Set (MobiusCuspAugmentedDomain S w C) :=
  {p | p.val = g.val.val w ∨ ∃ z : ℂ, t < z.im ∧
    g.val.val (C.normalizer.val.symm (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = p.val}

theorem mobiusCuspAugmentedHeightTail_eq_image {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (g : G) (t : ℝ) (ht : C.height < t) :
    mobiusCuspAugmentedHeightTail C g t = mobiusCuspAugmentedCusp C g '' stableCuspCompletionTail C.height t := by
  ext p
  constructor
  · rintro (hp | ⟨z, hz, he⟩)
    · exact ⟨stableCuspCompletionInfinity C.height, stableCuspCompletionTail_none C.height t,
        Subtype.ext hp.symm⟩
    · let zH : stableCuspHalfPlane C.height := ⟨z, ht.trans hz⟩
      exact ⟨stableCuspCompletionSome C.height zH, (stableCuspCompletionTail_some C.height t zH).mpr hz,
        Subtype.ext he⟩
  · rintro ⟨q, hq, rfl⟩
    cases q with
    | none => exact Or.inl rfl
    | some z => exact Or.inr ⟨z.val, (stableCuspCompletionTail_some C.height t z).mp hq, rfl⟩

theorem MobiusCuspNormalization.augmented_mem_nhds_iff {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hfix : ∀ f ∈ G, f.val w = w → f ∈ S.stabilizer) (g : G)
    (U : Set (MobiusCuspAugmentedDomain S w C)) :
    U ∈ 𝓝 (mobiusCuspAugmentedCusp C g (stableCuspCompletionInfinity C.height)) ↔
      ∃ t : ℝ, C.height < t ∧ mobiusCuspAugmentedHeightTail C g t ⊆ U := by
  rw [← (C.cusp_isOpenEmbedding hD hfix g).map_nhds_eq (stableCuspCompletionInfinity C.height)]
  change (mobiusCuspAugmentedCusp C g) ⁻¹' U ∈ 𝓝 (stableCuspCompletionInfinity C.height) ↔ _
  rw [stableCuspCompletion_mem_nhds_iff]
  constructor
  · rintro ⟨t, ht, hsub⟩
    refine ⟨t, ht, ?_⟩
    rw [mobiusCuspAugmentedHeightTail_eq_image C g t ht]
    exact Set.image_subset_iff.mpr hsub
  · rintro ⟨t, ht, hsub⟩
    rw [mobiusCuspAugmentedHeightTail_eq_image C g t ht] at hsub
    exact ⟨t, ht, Set.image_subset_iff.mp hsub⟩

/-- Every actual original added cusp has no compact neighborhood. -/
theorem MobiusCuspNormalization.augmented_no_compact_nhds {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hfix : ∀ f ∈ G, f.val w = w → f ∈ S.stabilizer) (g : G) :
    ¬∃ K : Set (MobiusCuspAugmentedDomain S w C), IsCompact K ∧
      K ∈ 𝓝 (mobiusCuspAugmentedCusp C g (stableCuspCompletionInfinity C.height)) := by
  rintro ⟨K, hKc, hKn⟩
  have hKimage := hKc.image C.augmentedHomeomorph.continuous
  have hKnhds := C.augmentedHomeomorph.isOpenMap.image_mem_nhds hKn
  have he : C.augmentedHomeomorph (mobiusCuspAugmentedCusp C g (stableCuspCompletionInfinity C.height)) =
      stableCuspAugmentedCusp (S.conjugate C.normalizer) C.height C.normalized_disc_eq
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer
          G g) (stableCuspCompletionInfinity C.height) :=
    C.augmentedEquiv_cusp g _
  rw [he] at hKnhds
  exact stableCuspAugmented_no_compact_nhds (S.conjugate C.normalizer)
    (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
    C.normalized_stabilizer (C.cusp_stabilizer_condition hfix) _ ⟨_, hKimage, hKnhds⟩

theorem MobiusStableSubset.conjugate_quotientImage {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    D.conjugateQuotientHomeomorph q '' S.quotientImage = (S.conjugate q).quotientImage := by
  ext p
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨z, hz⟩ := ha
    let zD : D.carrier := ⟨z.val, S.subset_domain z.property⟩
    let b : (S.conjugate q).carrier := ⟨q.val z.val, ⟨z.val, z.property, rfl⟩⟩
    refine ⟨b, ?_⟩
    exact (D.conjugateQuotientHomeomorph_projection q zD).symm.trans
      (congrArg (D.conjugateQuotientHomeomorph q) hz)
  · rintro ⟨b, hb⟩
    obtain ⟨z, hz, hzb⟩ := b.property
    let zD : D.carrier := ⟨z, S.subset_domain hz⟩
    refine ⟨mobiusDomainProjection D zD, ⟨⟨z, hz⟩, rfl⟩, ?_⟩
    exact (D.conjugateQuotientHomeomorph_projection q zD).trans
      ((congrArg (mobiusDomainProjection (D.conjugate q)) (Subtype.ext hzb)).trans hb)

/-- The original stable-cusp image is identified using the original full quotient map. -/
def MobiusStableSubset.conjugateQuotientImageHomeomorph {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    S.quotientImage ≃ₜ (S.conjugate q).quotientImage :=
  ((D.conjugateQuotientHomeomorph q).isEmbedding.homeomorphImage S.quotientImage).trans
    (Homeomorph.setCongr (S.conjugate_quotientImage q))

theorem MobiusStableSubset.conjugateQuotientImageHomeomorph_analytic {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hSo : IsOpen
      S.carrier) (hSc : IsConnected S.carrier) :
    RiemannAnalyticMap (S.openImageRiemannSurface hD hSo hSc).toRiemannAtlas
      ((S.conjugate q).openImageRiemannSurface (D.conjugate_discontinuous q hD)
        ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).isOpenMap _ hSo)
        (hSc.image q.val (_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary
          q).continuousOn)).toRiemannAtlas
      (S.conjugateQuotientImageHomeomorph q) := by
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.liftLocalHomeomorph Subtype.val Subtype.val
    (S.quotientImage_isOpen hSo).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    ((S.conjugate q).quotientImage_isOpen ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
      q).isOpenMap _ hSo)).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    (D.conjugateQuotientHomeomorph q) (S.conjugateQuotientImageHomeomorph q)
    (D.conjugateQuotientHomeomorph_analytic q hD)
    (S.conjugateQuotientImageHomeomorph q).continuous (fun _ => rfl)

theorem MobiusCuspNormalization.original_open {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) : IsOpen S.carrier := by
  have h := C.normalized_open.preimage (_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary
    C.normalizer)
  change IsOpen (C.normalizer.val ⁻¹' (C.normalizer.val '' S.carrier)) at h
  rw [Set.preimage_image_eq S.carrier C.normalizer.val.injective] at h
  exact h

theorem MobiusCuspNormalization.original_connected {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) : IsConnected S.carrier := by
  have : ConnectedSpace (S.conjugate C.normalizer).carrier :=
    isConnected_iff_connectedSpace.mp C.normalized_connected
  let E : S.carrier ≃ₜ (S.conjugate C.normalizer).carrier :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
      C.normalizer).isEmbedding.homeomorphImage S.carrier
  have : ConnectedSpace S.carrier := E.symm.surjective.connectedSpace E.symm.continuous
  exact isConnected_iff_connectedSpace.mpr inferInstance

/-- The arbitrary original stable parabolic-disc image is genuinely conformal to its
ordinary punctured-disc model, with no cusp-stabilizer repair needed for this part. -/
theorem MobiusCuspNormalization.punctured_conformallyEquivalent {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) :
    RiemannConformallyEquivalent (S.openImageRiemannSurface hD C.original_open C.original_connected)
      (stableCuspPuncturedDiscRiemannSurface C.height) := by
  let E := (S.conjugateQuotientImageHomeomorph C.normalizer).trans
    (stableCuspImageHomeomorph (S.conjugate C.normalizer) C.height C.normalized_disc_eq
      C.normalized_stabilizer C.normalized_open C.normalized_connected)
  refine ⟨E, ?_, E.bijective⟩
  exact (stableCuspImageHomeomorph_analytic (S.conjugate C.normalizer)
    (D.conjugate_discontinuous C.normalizer hD) C.height C.normalized_disc_eq C.normalized_stabilizer
    C.normalized_open C.normalized_connected).comp
      (S.conjugateQuotientImageHomeomorph_analytic C.normalizer hD C.original_open C.original_connected)

/-- The genuine filled coordinate on the actual original augmented orbit quotient. -/
def MobiusCuspNormalization.newChart {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) :
    OpenPartialHomeomorph (MobiusCuspAugmentedQuotient C) ℂ :=
  C.augmentedQuotientHomeomorph.toOpenPartialHomeomorph.trans
    (stableCuspAugmentedNewChart (S.conjugate C.normalizer)
      (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
      C.normalized_stabilizer C.normalized_open C.normalized_connected)

theorem MobiusCuspNormalization.newChart_mem {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hfix : ∀ f ∈ G, f.val w = w → f ∈ S.stabilizer) :
    C.newChart hD ∈ (C.filledQuotientRiemannSurface hD hfix).charts := by
  exact ⟨C.augmentedQuotientHomeomorph.toOpenPartialHomeomorph, rfl,
    stableCuspAugmentedNewChart (S.conjugate C.normalizer)
      (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
      C.normalized_stabilizer C.normalized_open C.normalized_connected,
    stableCuspAugmentedNewChart_mem (S.conjugate C.normalizer)
      (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
      C.normalized_stabilizer C.normalized_open C.normalized_connected (C.cusp_stabilizer_condition hfix), rfl⟩

theorem MobiusCuspNormalization.newChart_target {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) :
    (C.newChart hD).target = Metric.ball 0 (stableCuspRadius C.height) := by
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization.newChart,
    OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, preimage_univ, inter_univ,
    stableCuspAugmentedNewChart_target]

theorem MobiusCuspNormalization.augmentedQuotientHomeomorph_cusp {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (g : G) (p : StableCuspCompletion C.height) :
    C.augmentedQuotientHomeomorph (Quotient.mk _ (mobiusCuspAugmentedCusp C g p)) =
      Quotient.mk _ (stableCuspAugmentedCusp (S.conjugate C.normalizer) C.height C.normalized_disc_eq
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer
          G g) p) :=
  (C.augmentedQuotientHomeomorph_projection _).trans (congrArg (Quotient.mk _) (C.augmentedEquiv_cusp g p))

theorem MobiusCuspNormalization.newChart_cusp {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (g : G) :
    C.newChart hD (Quotient.mk _ (mobiusCuspAugmentedCusp C g (stableCuspCompletionInfinity C.height))) = 0 := by
  change stableCuspAugmentedNewChart (S.conjugate C.normalizer)
    (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
    C.normalized_stabilizer C.normalized_open C.normalized_connected
      (C.augmentedQuotientHomeomorph _) = 0
  rw [C.augmentedQuotientHomeomorph_cusp]
  exact stableCuspAugmentedNewChart_cusp (S.conjugate C.normalizer)
    (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
    C.normalized_stabilizer C.normalized_open C.normalized_connected _

theorem MobiusCuspNormalization.newChart_cusp_source {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (g : G) :
    Quotient.mk _ (mobiusCuspAugmentedCusp C g (stableCuspCompletionInfinity C.height)) ∈
      (C.newChart hD).source := by
  change _ ∈ C.augmentedQuotientHomeomorph.toOpenPartialHomeomorph.source ∧ _
  refine ⟨Set.mem_univ _, ?_⟩
  change C.augmentedQuotientHomeomorph _ ∈ (stableCuspAugmentedNewChart (S.conjugate C.normalizer)
    (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
    C.normalized_stabilizer C.normalized_open C.normalized_connected).source
  rw [C.augmentedQuotientHomeomorph_cusp]
  exact stableCuspAugmentedNewChart_cusp_source (S.conjugate C.normalizer)
    (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
    C.normalized_stabilizer C.normalized_open C.normalized_connected _

/-- On the actual original finite points, the filled chart is the normalized exponential. -/
theorem MobiusCuspNormalization.newChart_exponential {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (z : stableCuspHalfPlane C.height) :
    C.newChart hD (Quotient.mk _ (mobiusCuspAugmentedOld C
      ⟨(C.coordinateToSubset z).val, S.subset_domain (C.coordinateToSubset z).property⟩)) =
        (complexPeriodExponential 1 z.val).val := by
  change stableCuspAugmentedNewChart (S.conjugate C.normalizer)
    (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
    C.normalized_stabilizer C.normalized_open C.normalized_connected
      (C.augmentedQuotientHomeomorph _) = _
  rw [C.augmentedQuotientHomeomorph_projection]
  have he := C.augmentedEquiv_old
    ⟨(C.coordinateToSubset z).val, S.subset_domain (C.coordinateToSubset z).property⟩
  change C.augmentedHomeomorph _ = _ at he
  rw [he]
  have hz : D.conjugateHomeomorph C.normalizer
      ⟨(C.coordinateToSubset z).val, S.subset_domain (C.coordinateToSubset z).property⟩ =
        ⟨(z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), (S.conjugate
          C.normalizer).subset_domain
          (by rw [C.normalized_disc_eq]; exact ⟨z.val, z.property, rfl⟩)⟩ := by
    apply Subtype.ext
    exact C.normalizer.val.apply_symm_apply _
  rw [hz]
  exact stableCuspAugmentedNewChart_exponential (S.conjugate C.normalizer)
    (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem C.height C.normalized_disc_eq
    C.normalized_stabilizer C.normalized_open C.normalized_connected z

/--
The punctured-disc assertion under its original hypotheses.
The necessary additional cusp-stabilizer condition concerns only the filling assertion.
-/
theorem parabolic_stable_disc_quotient_conformal_punctured_disc {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (f :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hDisc : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc S.carrier) (hK : S.stabilizer =
      Subgroup.zpowers f) :
    ∃ hSo : IsOpen S.carrier, ∃ hSc : IsConnected S.carrier, ∃ h : ℝ,
      RiemannConformallyEquivalent (S.openImageRiemannSurface hD hSo hSc)
        (stableCuspPuncturedDiscRiemannSurface h) := by
  obtain ⟨w, hw⟩ := hf.2
  obtain ⟨C⟩ := mobiusCuspNormalization_exists S f hf hDisc hK w ((hw w).mpr rfl)
  exact ⟨C.original_open, C.original_connected, C.height, C.punctured_conformallyEquivalent hD⟩

/-- The single new quotient point represented by the specified actual original cusp. -/
def MobiusCuspNormalization.cuspQuotient {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) : MobiusCuspAugmentedQuotient C :=
  Quotient.mk _ (mobiusCuspAugmentedCusp C 1 (stableCuspCompletionInfinity C.height))

theorem MobiusCuspNormalization.cuspQuotient_eq {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (g : G) :
    Quotient.mk _ (mobiusCuspAugmentedCusp C g (stableCuspCompletionInfinity C.height)) =
      C.cuspQuotient := by
  apply Quotient.sound
  refine ⟨g, Subtype.ext ?_⟩
  change g • ((1 : G) • w) = g • w
  rw [one_smul]

/-- Every ideal orbit point is genuinely new: none belongs to the original domain. -/
theorem MobiusCuspNormalization.orbit_cusp_not_mem {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (g : G) :
    g.val.val w ∉ D.carrier := by
  intro hg
  have hn := stableCusp_orbit_infty_not_mem (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer G)
    (D.conjugate C.normalizer) (D.conjugate_discontinuous C.normalizer hD) C.normalized_translation_mem
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence C.normalizer G
        g)
  rw [C.conjugate_cusp g] at hn
  exact hn ⟨g.val.val w, hg, rfl⟩

/-- The actual filled orbit quotient adds precisely one point to the original quotient. -/
theorem MobiusCuspNormalization.quotient_old_or_cusp {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (x : MobiusCuspAugmentedQuotient C) : x ∈ Set.range (C.oldQuotientEmbedding hD) ∨ x = C.cuspQuotient := by
  induction x using Quotient.inductionOn with
  | h p =>
    rcases p.property with hp | ⟨g, hg⟩
    · refine Or.inl ⟨mobiusDomainProjection D ⟨p.val, hp⟩, ?_⟩
      exact (C.oldQuotientEmbedding_projection hD ⟨p.val, hp⟩).trans
        (congrArg (Quotient.mk _) (Subtype.ext rfl))
    · have he : p = mobiusCuspAugmentedCusp C g (stableCuspCompletionInfinity C.height) :=
        Subtype.ext hg.symm
      exact Or.inr ((congrArg (Quotient.mk _) he).trans (C.cuspQuotient_eq g))

theorem MobiusCuspNormalization.cuspQuotient_not_mem_old {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) :
    C.cuspQuotient ∉ Set.range (C.oldQuotientEmbedding hD) := by
  rintro ⟨x, hx⟩
  obtain ⟨z, rfl⟩ := mobiusDomainProjection_surjective D x
  have he := (C.oldQuotientEmbedding_projection hD z).symm.trans hx
  obtain ⟨g, hg⟩ := Quotient.exact he
  have hh : g.val.val w = z.val := by
    have hv := congrArg (fun p : MobiusCuspAugmentedDomain S w C => p.val) hg
    change g • ((1 : G) • w) = z.val at hv
    rw [one_smul] at hv
    change g.val.val w = z.val at hv
    exact hv
  exact C.orbit_cusp_not_mem hD g (hh.symm ▸ z.property)

/--
Adjoining the parabolic cusp orbit with its height-tail topology gives an
analytic filling of the quotient puncture. The full cusp stabilizer is assumed
to preserve the chosen stable disc.
-/
theorem parabolic_cusp_compatible_conformal_filling_exists {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (f :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hDisc : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc S.carrier) (hK : S.stabilizer =
      Subgroup.zpowers f)
    (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hw : f.val w = w)
    (hfix : ∀ g ∈ G, g.val w = w → g ∈ S.stabilizer) :
    ∃ C : MobiusCuspNormalization S w,
    let R := C.filledQuotientRiemannSurface hD hfix
    let J := C.oldQuotientEmbedding hD
    let e := C.newChart hD
    RiemannConformallyEquivalent (S.openImageRiemannSurface hD C.original_open C.original_connected)
        (stableCuspPuncturedDiscRiemannSurface C.height) ∧
      RiemannAnalyticMap (mobiusQuotientRiemannSurface D hD).toRiemannAtlas R.toRiemannAtlas J ∧
      Topology.IsOpenEmbedding J ∧ Topology.IsOpenEmbedding (mobiusCuspAugmentedOld C) ∧
      (∀ z : D.carrier, J (mobiusDomainProjection D z) = Quotient.mk _ (mobiusCuspAugmentedOld C z)) ∧
      C.cuspQuotient ∉ Set.range J ∧
      (∀ x : MobiusCuspAugmentedQuotient C, x ∈ Set.range J ∨ x = C.cuspQuotient) ∧
      e ∈ R.charts ∧ e.target = Metric.ball 0 (stableCuspRadius C.height) ∧
      (∀ z : stableCuspHalfPlane C.height,
        e (Quotient.mk _ (mobiusCuspAugmentedOld C
          ⟨(C.coordinateToSubset z).val, S.subset_domain (C.coordinateToSubset z).property⟩)) =
            (complexPeriodExponential 1 z.val).val) ∧
      ∀ g : G,
        (Quotient.mk _ (mobiusCuspAugmentedCusp C g (stableCuspCompletionInfinity C.height)) ∈ e.source ∧
          e (Quotient.mk _ (mobiusCuspAugmentedCusp C g (stableCuspCompletionInfinity C.height))) = 0) ∧
        (¬∃ K : Set (MobiusCuspAugmentedDomain S w C), IsCompact K ∧
          K ∈ 𝓝 (mobiusCuspAugmentedCusp C g (stableCuspCompletionInfinity C.height))) ∧
        ∀ U : Set (MobiusCuspAugmentedDomain S w C),
          U ∈ 𝓝 (mobiusCuspAugmentedCusp C g (stableCuspCompletionInfinity C.height)) ↔
            ∃ t : ℝ, C.height < t ∧ mobiusCuspAugmentedHeightTail C g t ⊆ U := by
  obtain ⟨C⟩ := mobiusCuspNormalization_exists S f hf hDisc hK w hw
  exact ⟨C, C.punctured_conformallyEquivalent hD, C.oldQuotientEmbedding_analytic hD hfix,
    C.oldQuotientEmbedding_isOpenEmbedding hD, C.old_isOpenEmbedding hD,
    C.oldQuotientEmbedding_projection hD, C.cuspQuotient_not_mem_old hD, C.quotient_old_or_cusp hD,
    C.newChart_mem hD hfix, C.newChart_target hD,
    C.newChart_exponential hD, fun g => ⟨⟨C.newChart_cusp_source hD g, C.newChart_cusp hD g⟩,
      C.augmented_no_compact_nhds hD hfix g, C.augmented_mem_nhds_iff hD hfix g⟩⟩

/-- The literal horizontal sequence in the original normalized cusp coordinate. -/
def MobiusCuspNormalization.horizontalSequence {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (g : G) (y : ℝ) (hy : C.height < y) (n : ℕ) :
    MobiusCuspAugmentedDomain S w C :=
  mobiusCuspAugmentedCusp C g (stableCuspCompletionSome C.height
    ⟨(n : ℂ) + (y : ℂ) * Complex.I, by
      change C.height < ((n : ℂ) + (y : ℂ) * Complex.I).im
      simpa only [Complex.add_im, Complex.natCast_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] using hy⟩)

/--
The horizontal sequence from does not converge to the added cusp,
even though its ordinary sphere coordinates approach that point.
-/
theorem MobiusCuspNormalization.horizontalSequence_not_tendsto {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} {S : MobiusStableSubset D} {w :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : MobiusCuspNormalization S w) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier)
    (hfix : ∀ f ∈ G, f.val w = w → f ∈ S.stabilizer) (g : G) (y : ℝ) (hy : C.height < y) :
    ¬Tendsto (C.horizontalSequence g y hy) atTop
      (𝓝 (mobiusCuspAugmentedCusp C g (stableCuspCompletionInfinity C.height))) := by
  intro hlim
  have ht : C.height < y + 1 := lt_trans hy (lt_add_one y)
  have hU := (C.augmented_mem_nhds_iff hD hfix g
    (mobiusCuspAugmentedHeightTail C g (y + 1))).mpr ⟨y + 1, ht, Set.Subset.rfl⟩
  obtain ⟨n, hn⟩ := (hlim.eventually hU).exists
  have hn' := (Set.ext_iff.mp (mobiusCuspAugmentedHeightTail_eq_image C g (y + 1) ht)
    (C.horizontalSequence g y hy n)).mp hn
  obtain ⟨p, hp, hpn⟩ := hn'
  have he := (C.cusp_isOpenEmbedding hD hfix g).injective hpn
  rw [he] at hp
  have hi := (stableCuspCompletionTail_some C.height (y + 1) _).mp hp
  change y + 1 < ((n : ℂ) + (y : ℂ) * Complex.I).im at hi
  simp only [Complex.add_im, Complex.natCast_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hi
  linarith

theorem stableCuspRadius_zero : stableCuspRadius 0 = 1 := by simp [stableCuspRadius]

/-- Positive real scaling identifies the genuine punctured disc with the unit punctured disc. -/
def stableCuspUnitPuncturedDiscHomeomorph (h : ℝ) :
    stableCuspPuncturedDisc h ≃ₜ stableCuspPuncturedDisc 0 where
  toFun z := ⟨⟨(stableCuspRadius h : ℂ)⁻¹ * z.val.val,
    mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr (stableCuspRadius_pos h).ne')) z.val.property⟩, by
      change ‖(stableCuspRadius h : ℂ)⁻¹ * z.val.val‖ < stableCuspRadius 0
      rw [stableCuspRadius_zero]
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (stableCuspRadius_pos h)]
      simpa only [div_eq_inv_mul] using (div_lt_one (stableCuspRadius_pos h)).mpr z.property⟩
  invFun z := ⟨⟨(stableCuspRadius h : ℂ) * z.val.val,
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (stableCuspRadius_pos h).ne') z.val.property⟩, by
      change ‖(stableCuspRadius h : ℂ) * z.val.val‖ < stableCuspRadius h
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (stableCuspRadius_pos h)]
      have hz : ‖z.val.val‖ < stableCuspRadius 0 := z.property
      rw [stableCuspRadius_zero] at hz
      simpa only [mul_one] using mul_lt_mul_of_pos_left hz (stableCuspRadius_pos h)⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (stableCuspRadius_pos h).ne') z.val.val
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr (stableCuspRadius_pos h).ne') z.val.val
  continuous_toFun := (continuous_const.mul (continuous_subtype_val.comp
    continuous_subtype_val)).subtype_mk _ |>.subtype_mk _
  continuous_invFun := (continuous_const.mul (continuous_subtype_val.comp
    continuous_subtype_val)).subtype_mk _ |>.subtype_mk _

theorem stableCuspUnitPuncturedDiscHomeomorph_analytic (h : ℝ) :
    RiemannAnalyticMap (stableCuspPuncturedDiscRiemannSurface h).toRiemannAtlas
      (stableCuspPuncturedDiscRiemannSurface 0).toRiemannAtlas (stableCuspUnitPuncturedDiscHomeomorph h) := by
  have hs : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas
      complexPlaneRiemannSurface.toRiemannAtlas (fun z : ℂ => (stableCuspRadius h : ℂ)⁻¹ * z) := by
    apply (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.globalChart_iff
      (OpenPartialHomeomorph.refl ℂ) rfl
      (OpenPartialHomeomorph.refl ℂ) rfl _).mpr
    refine ⟨continuous_const.mul continuous_id, ?_⟩
    intro z _hz
    exact analyticAt_const.mul analyticAt_id
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_localHomeomorph (stableCuspPuncturedDiscInclusion_analytic 0)
    (stableCuspPuncturedDiscInclusion_isOpenEmbedding 0).isLocalHomeomorph
    (stableCuspUnitPuncturedDiscHomeomorph h).continuous
    (hs.comp (stableCuspPuncturedDiscInclusion_analytic h))

theorem stableCuspPuncturedDisc_conformallyEquivalent_unit (h : ℝ) :
    RiemannConformallyEquivalent (stableCuspPuncturedDiscRiemannSurface h)
      (stableCuspPuncturedDiscRiemannSurface 0) :=
  ⟨stableCuspUnitPuncturedDiscHomeomorph h, stableCuspUnitPuncturedDiscHomeomorph_analytic h,
    (stableCuspUnitPuncturedDiscHomeomorph h).bijective⟩

/-- The original arbitrary stable-disc quotient is conformally the unit punctured disc. -/
theorem parabolic_stable_disc_quotient_conformal_unit_punctured_disc {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (f :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hDisc : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc S.carrier) (hK : S.stabilizer =
      Subgroup.zpowers f) :
    ∃ hSo : IsOpen S.carrier, ∃ hSc : IsConnected S.carrier,
      RiemannConformallyEquivalent (S.openImageRiemannSurface hD hSo hSc)
        (stableCuspPuncturedDiscRiemannSurface 0) := by
  obtain ⟨hSo, hSc, h, he⟩ := parabolic_stable_disc_quotient_conformal_punctured_disc S hD f hf hDisc hK
  exact ⟨hSo, hSc, he.trans (stableCuspPuncturedDisc_conformallyEquivalent_unit h)⟩

end LowDimensionalTopology.Geometry.Surfaces
