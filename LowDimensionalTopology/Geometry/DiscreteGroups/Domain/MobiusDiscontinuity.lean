/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Topology
public import LowDimensionalTopology.Geometry.Mobius.HyperbolicExtension
public import LowDimensionalTopology.Geometry.Mobius.Classification.MobiusTypes
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.Discontinuity
@[expose] public section
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- The genuine hyperbolic distance retains the original quaternion-manifold topology. -/
@[instance_reducible]
def upperHalfSpaceHyperbolicMetricSpace : MetricSpace Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  @Topology.IsEmbedding.comapMetricSpace Hyperbolic.QuaternionHalfSpace.UpperHalfSpace
    (Hyperbolic.HyperbolicHalfSpace 2)
    inferInstance (Hyperbolic.halfSpaceMetricSpace 2) Mobius.upperHalfSpaceHyperbolicHomeomorph
      Mobius.upperHalfSpaceHyperbolicHomeomorph.isEmbedding

theorem upperHalfSpaceHyperbolicMetricSpace_topology :
    upperHalfSpaceHyperbolicMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) := rfl

theorem upperHalfSpaceHyperbolicMetricSpace_dist (q r : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    @dist Hyperbolic.QuaternionHalfSpace.UpperHalfSpace upperHalfSpaceHyperbolicMetricSpace.toDist q r =
      Mobius.upperHalfSpacePathDist q r := by
  change @dist (Hyperbolic.HyperbolicHalfSpace 2) (Hyperbolic.halfSpaceMetricSpace 2).toDist
    (Mobius.upperHalfSpaceHyperbolicHomeomorph q) (Mobius.upperHalfSpaceHyperbolicHomeomorph r) = _
  exact Hyperbolic.halfSpaceMetricSpace_dist _ _

theorem upperHalfSpacePathDist_right_continuous (r : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    Continuous (fun q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => Mobius.upperHalfSpacePathDist q r) := by
  have h := (@continuous_dist (Hyperbolic.HyperbolicHalfSpace 2)
    (Hyperbolic.halfSpaceMetricSpace 2).toPseudoMetricSpace).comp
      (Mobius.upperHalfSpaceHyperbolicHomeomorph.continuous.prodMk
        (continuous_const (y := Mobius.upperHalfSpaceHyperbolicHomeomorph r)))
  simpa only [Hyperbolic.halfSpaceMetricSpace_dist, Function.comp_def, Mobius.upperHalfSpacePathDist] using h

theorem upperHalfSpacePathDist_nonneg (q r : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    0 ≤ Mobius.upperHalfSpacePathDist q r :=
  (Hyperbolic.halfSpacePathDist_metric_axioms
    (Mobius.upperHalfSpaceHyperbolicHomeomorph q) (Mobius.upperHalfSpaceHyperbolicHomeomorph r)
      (Mobius.upperHalfSpaceHyperbolicHomeomorph r)).1

theorem upperHalfSpacePathDist_comm (q r : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    Mobius.upperHalfSpacePathDist q r = Mobius.upperHalfSpacePathDist r q :=
  (Hyperbolic.halfSpacePathDist_metric_axioms
    (Mobius.upperHalfSpaceHyperbolicHomeomorph q) (Mobius.upperHalfSpaceHyperbolicHomeomorph r)
      (Mobius.upperHalfSpaceHyperbolicHomeomorph r)).2.2.1

theorem upperHalfSpacePathDist_triangle (q r s : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    Mobius.upperHalfSpacePathDist q s ≤ Mobius.upperHalfSpacePathDist q r + Mobius.upperHalfSpacePathDist r s :=
  (Hyperbolic.halfSpacePathDist_metric_axioms
    (Mobius.upperHalfSpaceHyperbolicHomeomorph q) (Mobius.upperHalfSpaceHyperbolicHomeomorph r)
      (Mobius.upperHalfSpaceHyperbolicHomeomorph s)).2.2.2

theorem discreteMobius_isDiscontinuous_H3 (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) : DiscreteGroups.Action.IsDiscontinuous H
      Hyperbolic.QuaternionHalfSpace.UpperHalfSpace := by
  intro K hK
  obtain ⟨R, hR⟩ := hK.bddAbove_image (upperHalfSpacePathDist_right_continuous
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).continuousOn
  let T := max R 0
  have hT : 0 ≤ T := le_max_right R 0
  have hbound (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (hq : q ∈ K) : Mobius.upperHalfSpacePathDist q
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ≤ T :=
    (hR ⟨q, hq, rfl⟩).trans (le_max_left R 0)
  let B := Real.sqrt (2 * Real.cosh (2 * T))
  apply (Mobius.discreteMobius_norm_sublevel_finite H hH B).subset
  rintro g ⟨_, ⟨x, hx, rfl⟩, hgx⟩
  have hd : Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ (g.val •
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) ≤ 2 * T := by
    calc
      _ ≤ Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ (g.val • x) +
        Mobius.upperHalfSpacePathDist (g.val • x) (g.val • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) :=
          upperHalfSpacePathDist_triangle _ _ _
      _ = Mobius.upperHalfSpacePathDist (g.val • x) Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ +
        Mobius.upperHalfSpacePathDist x Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
          rw [upperHalfSpacePathDist_comm Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ,
            Mobius.upperHalfSpacePathDist_smul]
      _ ≤ 2 * T := by linarith [hbound x hx, hbound (g.val • x) hgx]
  have hc : Real.cosh (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ (g.val •
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)) ≤
      Real.cosh (2 * T) := by
    apply Real.cosh_le_cosh.mpr
    rwa [abs_of_nonneg (upperHalfSpacePathDist_nonneg _ _), abs_of_nonneg (by positivity)]
  have hn := Mobius.mobiusNormalizedNorm_sq_eq_two_cosh_origin_displacement g.val
  have hnnon : 0 ≤ Mobius.mobiusNormalizedNorm g.val := by
    obtain ⟨A, he⟩ := Mobius.mobiusSpecialLinearProjection_surjective g.val
    rw [← he, Mobius.mobiusNormalizedNorm_specialLinearProjection]
    exact Auxiliary.Algebra.matrixNorm_nonneg _
  change Mobius.mobiusNormalizedNorm g.val ≤ B
  have hB : B ^ 2 = 2 * Real.cosh (2 * T) := Real.sq_sqrt (by positivity)
  have hBnon : 0 ≤ B := Real.sqrt_nonneg _
  nlinarith

/-- Uniform convergence to the identity gives convergence of the actual H3 orbit of j. -/
theorem mobius_tendsto_H3_j {α : Type*} {l : Filter α} (f : α → Mobius.complexMobiusGroup)
    (hf : Tendsto f l (𝓝 1)) :
    Tendsto (fun i => f i • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) l (𝓝
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) := by
  have hnorm := (Mobius.mobiusNormalizedNorm_continuous.pow 2).continuousAt.tendsto.comp hf
  change Tendsto (fun i => Mobius.mobiusNormalizedNorm (f i) ^ 2) l
    (𝓝 (Mobius.mobiusNormalizedNorm 1 ^ 2)) at hnorm
  have hI : Mobius.mobiusNormalizedNorm 1 ^ 2 = 2 := by
    rw [Mobius.mobiusNormalizedNorm_sq_eq_two_cosh_origin_displacement, one_smul, ←
      upperHalfSpaceHyperbolicMetricSpace_dist,
      @dist_self _ upperHalfSpaceHyperbolicMetricSpace.toPseudoMetricSpace, Real.cosh_zero, mul_one]
  rw [hI] at hnorm
  apply Mobius.upperHalfSpaceHyperbolicHomeomorph.isEmbedding.tendsto_nhds_iff.mpr
  apply (@Metric.tendsto_nhds (Hyperbolic.HyperbolicHalfSpace 2) α
    (Hyperbolic.halfSpaceMetricSpace 2).toPseudoMetricSpace l
      (fun i => Mobius.upperHalfSpaceHyperbolicHomeomorph (f i • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ))
        (Mobius.upperHalfSpaceHyperbolicHomeomorph Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)).mpr
  intro ε hε
  have hc : 2 < 2 * Real.cosh ε := by
    have h := Real.one_lt_cosh.mpr hε.ne'
    linarith
  filter_upwards [hnorm.eventually (Iio_mem_nhds hc)] with i hi
  rw [Mobius.mobiusNormalizedNorm_sq_eq_two_cosh_origin_displacement] at hi
  have hd : Real.cosh (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ (f i •
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)) < Real.cosh ε := by
    linarith
  have hdist := Real.cosh_lt_cosh.mp hd
  rw [abs_of_nonneg (upperHalfSpacePathDist_nonneg _ _), abs_of_pos hε] at hdist
  rw [Hyperbolic.halfSpaceMetricSpace_dist]
  exact (upperHalfSpacePathDist_comm _ _).le.trans_lt hdist

section OrbitConvergence

variable {G X : Type*} [Group G] [TopologicalSpace G] [T1Space G]
  [TopologicalSpace X] [MulAction G X]

/-- A discontinuous action turns simultaneous identity/orbit convergence into eventual equality. -/
theorem Action.IsDiscontinuous.eventually_eq_one_of_tendsto (h : DiscreteGroups.Action.IsDiscontinuous G X)
    (u : ℕ → G) (hu : Tendsto u atTop (𝓝 1)) (x : X)
    (hx : Tendsto (fun n => u n • x) atTop (𝓝 x)) :
    ∀ᶠ n in atTop, u n = 1 := by
  let K := insert x (Set.range (fun n => u n • x))
  have hK : IsCompact K := hx.isCompact_insert_range
  have hfinite : (Set.range u).Finite := (h K hK).subset (by
    rintro g ⟨n, rfl⟩
    exact ⟨u n • x, ⟨x, Or.inl rfl, rfl⟩, Or.inr ⟨n, rfl⟩⟩)
  have hclosed : IsClosed (Set.range u \ {1}) := (hfinite.sdiff).isClosed
  have he := hu.eventually (hclosed.isOpen_compl.mem_nhds (by simp))
  filter_upwards [he] with n hn
  by_contra hne
  exact hn ⟨Set.mem_range_self n, hne⟩
end OrbitConvergence

theorem isDiscontinuous_H3_discreteMobius (H : Subgroup Mobius.complexMobiusGroup)
    (hH : DiscreteGroups.Action.IsDiscontinuous H Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
      Mobius.IsDiscreteMobiusSubgroup H := by
  apply (DiscreteGroups.MatrixGroups.discrete_iff_identity_sequences H).mpr
  intro u hu
  apply hH.eventually_eq_one_of_tendsto u
    (Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr hu) Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
  exact mobius_tendsto_H3_j (fun n => (u n).val) hu

/-- For the actual Mobius action on the original H3 manifold. -/
theorem discrete_iff_discontinuous_halfSpace (H : Subgroup Mobius.complexMobiusGroup) :
    Mobius.IsDiscreteMobiusSubgroup H ↔ DiscreteGroups.Action.IsDiscontinuous H
      Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  ⟨discreteMobius_isDiscontinuous_H3 H, isDiscontinuous_H3_discreteMobius H⟩




/-- The compact-set discontinuity condition on an ambient subset of the sphere. -/
def IsMobiusDiscontinuousOn (H : Subgroup Mobius.complexMobiusGroup)
    (S : Set Mobius.ExtendedComplex) : Prop :=
  ∀ K : Set Mobius.ExtendedComplex, IsCompact K → K ⊆ S →
    {g : H | (((g.val : Equiv.Perm Mobius.ExtendedComplex) '' K) ∩ K).Nonempty}.Finite

/-- On an invariant set, the ambient condition is exactly discontinuity of the restricted action. -/
theorem isMobiusDiscontinuousOn_iff_subtype (H : Subgroup Mobius.complexMobiusGroup)
    (S : Set Mobius.ExtendedComplex) (hS : ∀ (g : H) x, x ∈ S → g • x ∈ S) :
    IsMobiusDiscontinuousOn H S ↔
      @DiscreteGroups.Action.IsDiscontinuous H S _ _ (DiscreteGroups.Action.invariantSubsetMulAction S hS) := by
  let sphereInvariantAction : MulAction H S := DiscreteGroups.Action.invariantSubsetMulAction S hS
  constructor
  · intro h K hK
    refine (h (Subtype.val '' K) (hK.image continuous_subtype_val) (by
      rintro _ ⟨x, _, rfl⟩; exact x.property)).subset ?_
    rintro g ⟨_, ⟨x, hx, rfl⟩, hgx⟩
    exact ⟨g • x.val, ⟨x.val, ⟨x, hx, rfl⟩, rfl⟩, g • x, hgx, rfl⟩
  · intro h K hK hKS
    have hkr : K ⊆ Set.range (Subtype.val : S → Mobius.ExtendedComplex) := by
      simpa only [Subtype.range_coe] using hKS
    have hL : IsCompact (Subtype.val ⁻¹' K : Set S) :=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hkr
    refine (h (Subtype.val ⁻¹' K) hL).subset ?_
    rintro g ⟨_, ⟨x, hx, rfl⟩, hgx⟩
    exact ⟨g • (⟨x, hKS hx⟩ : S), ⟨⟨x, hKS hx⟩, hx, rfl⟩, hgx⟩

/-- A nonempty invariant subset with a discontinuous action forces discreteness. -/
theorem isMobiusDiscontinuousOn_invariant_discrete (H : Subgroup Mobius.complexMobiusGroup)
    (S : Set Mobius.ExtendedComplex) (hS : ∀ (g : H) x, x ∈ S → g • x ∈ S)
    (hne : S.Nonempty) (h : IsMobiusDiscontinuousOn H S) : Mobius.IsDiscreteMobiusSubgroup H := by
  let sphereInvariantAction : MulAction H S := DiscreteGroups.Action.invariantSubsetMulAction S hS
  have hd : DiscreteGroups.Action.IsDiscontinuous H S := (isMobiusDiscontinuousOn_iff_subtype H S hS).mp h
  obtain ⟨z, hz⟩ := hne
  let x : S := ⟨z, hz⟩
  apply (DiscreteGroups.MatrixGroups.discrete_iff_identity_sequences H).mpr
  intro u hu
  apply hd.eventually_eq_one_of_tendsto u
    (Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr hu) x
  apply Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr
  change Tendsto (fun n => ((u n).val : Equiv.Perm Mobius.ExtendedComplex) z) atTop (𝓝 z)
  have ht := (Mobius.mobiusLocal_eval_continuous z).continuousAt.tendsto.comp hu
  exact ht

/-- The sphere-domain criterion also applies when the open subset is not invariant. -/
theorem isMobiusDiscontinuousOn_open_discrete (H : Subgroup Mobius.complexMobiusGroup)
    (S : Set Mobius.ExtendedComplex) (hS : IsOpen S) (hne : S.Nonempty)
    (h : IsMobiusDiscontinuousOn H S) : Mobius.IsDiscreteMobiusSubgroup H := by
  classical
  obtain ⟨z, hz⟩ := hne
  apply (DiscreteGroups.MatrixGroups.discrete_iff_identity_sequences H).mpr
  intro u hu
  have hx : Tendsto (fun n => ((u n).val : Equiv.Perm Mobius.ExtendedComplex) z) atTop (𝓝 z) :=
    (Mobius.mobiusLocal_eval_continuous z).continuousAt.tendsto.comp hu
  have he : ∀ᶠ n in atTop, ((u n).val : Equiv.Perm Mobius.ExtendedComplex) z ∈ S :=
    hx.eventually (hS.mem_nhds hz)
  let v : ℕ → Mobius.ExtendedComplex := fun n =>
    if ((u n).val : Equiv.Perm Mobius.ExtendedComplex) z ∈ S then
      ((u n).val : Equiv.Perm Mobius.ExtendedComplex) z else z
  have hv : Tendsto v atTop (𝓝 z) := hx.congr' (by
    filter_upwards [he] with n hn
    simp only [v, ite_eq_left hn])
  let K := insert z (Set.range v)
  have hK : IsCompact K := hv.isCompact_insert_range
  have hKS : K ⊆ S := by
    rintro x (rfl | ⟨n, rfl⟩)
    · exact hz
    · dsimp only [v]
      split_ifs with hn
      · exact hn
      · exact hz
  let F : Set H := {g | (((g.val : Equiv.Perm Mobius.ExtendedComplex) '' K) ∩ K).Nonempty}
  have hF : F.Finite := h K hK hKS
  have hclosed : IsClosed (F \ {1}) := hF.sdiff.isClosed
  have huH : Tendsto u atTop (𝓝 (1 : H)) :=
    Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr hu
  have havoid := huH.eventually (hclosed.isOpen_compl.mem_nhds (by simp))
  filter_upwards [he, havoid] with n hn ha
  by_contra hne
  apply ha
  refine ⟨?_, hne⟩
  refine ⟨((u n).val : Equiv.Perm Mobius.ExtendedComplex) z, ⟨z, Or.inl rfl, rfl⟩,
    Or.inr ⟨n, ?_⟩⟩
  simp only [v, ite_eq_left hn]

/-- A finite point stabilizer makes every element fixing that point have finite order. -/
theorem isOfFinOrder_of_finite_stabilizer {G X : Type*} [Group G] [MulAction G X]
    (g : G) (x : X) (hfinite : (MulAction.stabilizer G x : Set G).Finite)
    (hfix : g • x = x) : IsOfFinOrder g := by
  let discontinuityFiniteStabilizer : Finite (MulAction.stabilizer G x) := hfinite.to_subtype
  let a : MulAction.stabilizer G x := ⟨g, hfix⟩
  obtain ⟨n, hn, he⟩ := (isOfFinOrder_of_finite a).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg Subtype.val he⟩

/-- The ambient compact-set condition already makes the stabilizer of any included point finite. -/
theorem IsMobiusDiscontinuousOn.finite_stabilizer {H : Subgroup Mobius.complexMobiusGroup}
    {S : Set Mobius.ExtendedComplex} (h : IsMobiusDiscontinuousOn H S) (z : Mobius.ExtendedComplex)
    (hz : z ∈ S) : (MulAction.stabilizer H z : Set H).Finite := by
  refine (h {z} isCompact_singleton (Set.singleton_subset_iff.mpr hz)).subset ?_
  intro g hg
  exact ⟨z, ⟨z, rfl, MulAction.mem_stabilizer_iff.mp hg⟩, rfl⟩

/-- A fixed point of an infinite-order element prevents ambient discontinuity on every containing set. -/
theorem mobius_infinite_order_fixed_not_discontinuousOn (H : Subgroup Mobius.complexMobiusGroup)
    (S : Set Mobius.ExtendedComplex) (g : H) (hg : ¬IsOfFinOrder g.val)
    (z : Mobius.ExtendedComplex) (hz : z ∈ S)
    (hfix : (g.val : Equiv.Perm Mobius.ExtendedComplex) z = z) :
    ¬IsMobiusDiscontinuousOn H S := by
  intro h
  have hf := isOfFinOrder_of_finite_stabilizer g z (h.finite_stabilizer z hz) hfix
  obtain ⟨n, hn, he⟩ := hf.exists_pow_eq_one
  exact hg (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg Subtype.val he⟩)

/-- Neither a genuine parabolic nor a genuine loxodromic transformation has finite order. -/
theorem mobius_parabolic_or_loxodromic_not_isOfFinOrder (f : Mobius.complexMobiusGroup)
    (hf : Mobius.MobiusParabolic f ∨ Mobius.MobiusLoxodromic f) : ¬IsOfFinOrder f := by
  intro hfin
  rcases hf with hp | hl
  · exact (Mobius.mobius_finite_order_elliptic f hp.1 hfin).not_parabolic hp
  · exact hl.not_elliptic (Mobius.mobius_finite_order_elliptic f hl.1 hfin)

/-- With no openness or invariance requirement on the containing set. -/
theorem not_discontinuous_on_set_containing_parabolic_or_loxodromic_fixedPoint (H : Subgroup Mobius.complexMobiusGroup)
    (S : Set Mobius.ExtendedComplex) (g : H) (hg : Mobius.MobiusParabolic g.val ∨ Mobius.MobiusLoxodromic g.val)
    (z : Mobius.ExtendedComplex) (hz : z ∈ S)
    (hfix : (g.val : Equiv.Perm Mobius.ExtendedComplex) z = z) :
    ¬IsMobiusDiscontinuousOn H S :=
  mobius_infinite_order_fixed_not_discontinuousOn H S g
    (mobius_parabolic_or_loxodromic_not_isOfFinOrder g.val hg) z hz hfix


end
end LowDimensionalTopology.Geometry.DiscreteGroups
