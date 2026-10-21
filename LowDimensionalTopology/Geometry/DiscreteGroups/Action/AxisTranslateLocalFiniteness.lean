/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.CosetRegion
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.TranslatedSubsets
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
public import LowDimensionalTopology.Geometry.Fuchsian.Geodesic.SimpleClosedCurves
public import Mathlib.Topology.MetricSpace.HausdorffDistance
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology Pointwise UpperHalfPlane
namespace LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace





/-- The strict nearest-translate region compares with genuinely different translated subsets. -/
def axisVoronoiRegion {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
    (S : Set X) : Set X :=
  {x | ∀ T ∈ translatedSubsetFamily (G := G) S, T ≠ S → Metric.infDist x S < Metric.infDist x T}

/-- Compact-core local finiteness makes the actual strict nearest-axis region open. -/
theorem axisVoronoiRegion_isOpen {G X : Type*} [Group G]
    [MetricSpace X] [ProperSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] (S C : Set X) (K : Subgroup G)
    (hS : IsClosed S) (hne : S.Nonempty) (hC : IsCompact C)
    (hstable : ∀ k : K, (k.val • ·) '' S = S)
    (hcover : ∀ x ∈ S, ∃ k : K, ∃ c ∈ C, k.val • c = x) :
    IsOpen (axisVoronoiRegion (G := G) S) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let J := {T | T ∈ translatedSubsetFamily (G := G) S ∧ T ≠ S ∧
    Metric.infDist x T ≤ Metric.infDist x S+2}
  have hJ : J.Finite := (finite_translated_subsets_distance_le S C K hS hne hC hstable hcover x
    (Metric.infDist x S+2)).subset (fun _ h => ⟨h.1,h.2.2⟩)
  have hV : (⋂ T ∈ J, {y | Metric.infDist y S < Metric.infDist y T}) ∈ 𝓝 x :=
    (biInter_mem hJ).mpr (fun T hT =>
      (isOpen_lt (Metric.continuous_infDist_pt S) (Metric.continuous_infDist_pt T)).mem_nhds
        (hx T hT.1 hT.2.1))
  apply Filter.mem_of_superset (inter_mem (Metric.ball_mem_nhds x zero_lt_one) hV)
  rintro y ⟨hyB,hyV⟩ T hT hneT
  by_cases hTJ : T ∈ J
  · exact mem_iInter₂.mp hyV T hTJ
  · have hfar : Metric.infDist x S+2 < Metric.infDist x T :=
      lt_of_not_ge (fun hh => hTJ ⟨hT,hneT,hh⟩)
    have hleft := Metric.infDist_le_infDist_add_dist (x := y) (y := x) (s := S)
    have hright := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := T)
    rw [dist_comm x y] at hright
    have hclose : dist y x < 1 := hyB
    linarith

/-- Pairwise disjoint closed translates put every point of the actual axis in its strict region. -/
theorem subset_axisVoronoiRegion_of_disjoint {G X : Type*} [Group G]
    [MetricSpace X] [MulAction G X] [ContinuousConstSMul G X]
    (S : Set X) (hS : IsClosed S) (hne : S.Nonempty)
    (hdis : ∀ T ∈ translatedSubsetFamily (G := G) S, T ≠ S → Disjoint S T) :
    S ⊆ axisVoronoiRegion (G := G) S := by
  intro x hx T hT hneT
  rw [Metric.infDist_zero_of_mem hx]
  obtain ⟨g,rfl⟩ := hT
  apply (Metric.infDist_pos_iff_notMem_closure (hne.image _)).mp
  rw [(isClosedMap_smul g S hS).closure_eq]
  exact fun hxt => Set.disjoint_left.mp (hdis _ ⟨g,rfl⟩ hneT) hx hxt

/-- An actual translation on a continuous line has a compact fundamental core, even when the full set stabilizer is larger. -/
theorem compact_core_of_line_translation {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (γ : ℝ → X) (hγ : Continuous γ) (p : G) (l : ℝ) (hl : l ≠ 0)
    (hstep : ∀ t, p • γ t = γ (t+l)) :
    ∃ C : Set X, IsCompact C ∧ C ⊆ Set.range γ ∧
      (∀ k : Subgroup.zpowers p, (k.val • ·) '' Set.range γ = Set.range γ) ∧
      (∀ x ∈ Set.range γ, ∃ k : Subgroup.zpowers p, ∃ c ∈ C, k.val • c = x) := by
  have hinv (t : ℝ) : p⁻¹ • γ t = γ (t-l) := by
    calc
      p⁻¹ • γ t = p⁻¹ • γ ((t-l)+l) := by congr 2;ring
      _ = p⁻¹ • (p • γ (t-l)) := by rw [hstep]
      _ = γ (t-l) := inv_smul_smul p _
  have hpow (n : ℤ) (t : ℝ) : p^n • γ t = γ (t+(n:ℝ)*l) := by
    induction n using Int.induction_on generalizing t with
    | zero => simp
    | succ n ih =>
      rw [zpow_add,zpow_one,mul_smul,hstep,ih]
      congr 1
      push_cast
      ring
    | pred n ih =>
      rw [zpow_sub,zpow_one,mul_smul,hinv,ih]
      congr 1
      push_cast
      ring
  let C := γ '' Icc (-|l|) |l|
  refine ⟨C,isCompact_Icc.image hγ,Set.image_subset_range _ _,?_,?_⟩
  · intro k
    obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp k.property
    rw [←hn]
    ext x
    constructor
    · rintro ⟨y,⟨t,rfl⟩,rfl⟩
      exact ⟨t+(n:ℝ)*l,(hpow n t).symm⟩
    · rintro ⟨t,rfl⟩
      refine ⟨γ (t-(n:ℝ)*l),⟨_,rfl⟩,?_⟩
      change p^n • γ (t-(n:ℝ)*l) = γ t
      rw [hpow]
      congr 1
      ring
  · rintro x ⟨t,rfl⟩
    let n : ℤ := ⌊t/l⌋
    let r := Int.fract (t/l)*l
    have hr : |r| ≤ |l| := by
      dsimp [r]
      rw [abs_mul,abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (abs_nonneg l) (Int.fract_lt_one _).le
    have hrt : r+(n:ℝ)*l=t := by
      simpa only [n,zsmul_eq_mul] using Int.fract_div_mul_self_add_zsmul_eq l t hl
    refine ⟨⟨p^n,(Subgroup.zpowers p).zpow_mem (Subgroup.mem_zpowers p) n⟩,γ r,?_,?_⟩
    · exact ⟨r,(abs_le.mp hr),rfl⟩
    · rw [hpow,hrt]

/-- The actual native half-plane action inherits proper discontinuity from the original sphere group, including elementary groups. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.native_properlyDiscontinuous
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.HalfPlaneFuchsianGroup H) :
    letI := P.nativeAction
    ProperlyDiscontinuousSMul H ℍ := by
  let nativeAxisHalfPlaneAction := P.nativeAction
  let Q := P.cayleyData
  let nativeAxisConjugateProper : ProperlyDiscontinuousSMul
      (DiscreteGroups.Action.Actions.subgroupConjugate Hyperbolic.cayleyMobius H) Q.domain.carrier :=
    Surfaces.mobiusDomain_properlyDiscontinuous Q.domain Q.discontinuous
  refine ⟨fun {K L} hK hL => ?_⟩
  let e := DiscreteGroups.Action.Actions.subgroupConjugateEquivalence Hyperbolic.cayleyMobius H
  have hfin : {g : DiscreteGroups.Action.Actions.subgroupConjugate Hyperbolic.cayleyMobius H |
      ((g • ·) '' (P.cayleyCoordinate '' K) ∩ P.cayleyCoordinate '' L).Nonempty}.Finite :=
    finite_disjoint_inter_image (hK.image P.cayleyCoordinate.continuous)
      (hL.image P.cayleyCoordinate.continuous)
  apply (hfin.preimage e.injective.injOn).subset
  rintro g ⟨y,⟨x,hx,rfl⟩,hy⟩
  refine ⟨P.cayleyCoordinate (g • x),?_,mem_image_of_mem _ hy⟩
  exact ⟨P.cayleyCoordinate x,mem_image_of_mem _ hx,(P.cayleyCoordinate_equivariant g x).symm⟩

/-- A positive real dilation is literal translation in the actual logarithmic axis parameter. -/
theorem imaginaryAxisParam_dilation_step (k : ℝ) (hk : 0 < k) (t : ℝ) :
    Hyperbolic.verticalDilationSL k hk • Hyperbolic.imaginaryAxisParam t =
      Hyperbolic.imaginaryAxisParam (t+Real.log k) := by
  apply UpperHalfPlane.ext
  rw [Hyperbolic.verticalDilationSL_coe,Hyperbolic.imaginaryAxisParam_coe,Hyperbolic.imaginaryAxisParam_coe,
    Real.exp_add,Real.exp_log hk,Complex.ofReal_mul]
  ring

/-- Every genuine hyperbolic axis has an actual compact core under the element's own cyclic subgroup, with no restriction on other elliptics in the group. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.hyperbolic_axis_compact_core
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Hyperbolic.realSLMobius A ∈ H) (hf : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2) :
    letI := P.nativeAction
    ∃ C : Set ℍ, IsCompact C ∧ C ⊆ (Hyperbolic.hHyperbolicAxis A hf ht).carrier ∧
      (∀ k : Subgroup.zpowers (⟨Hyperbolic.realSLMobius A,hA⟩ : H),
        (k.val • ·) '' (Hyperbolic.hHyperbolicAxis A hf ht).carrier = (Hyperbolic.hHyperbolicAxis A hf ht).carrier) ∧
      (∀ x ∈ (Hyperbolic.hHyperbolicAxis A hf ht).carrier,
        ∃ k : Subgroup.zpowers (⟨Hyperbolic.realSLMobius A,hA⟩ : H), ∃ c ∈ C, k.val • c = x) := by
  let nativeAxisCoreAction := P.nativeAction
  obtain ⟨s,k,hk,hk1,hL,_hT,hact⟩ := Hyperbolic.hHyperbolicAxis_normalizer A hf ht
  let γ : ℝ → ℍ := fun t => s⁻¹ • Hyperbolic.imaginaryAxisParam t
  have hγ : Continuous γ := (isometry_smul ℍ s⁻¹).continuous.comp Hyperbolic.imaginaryAxisParam_isometry.continuous
  have hrange : Set.range γ = (Hyperbolic.hHyperbolicAxis A hf ht).carrier := by
    rw [hL]
    exact Hyperbolic.range_normalizerGeodesic (Matrix.SpecialLinearGroup.mapGL ℝ s)
  have hstep (t : ℝ) : (⟨Hyperbolic.realSLMobius A,hA⟩ : H) • γ t = γ (t+Real.log k) := by
    rw [P.nativeAction_realSL _ A rfl]
    change A • (s⁻¹ • Hyperbolic.imaginaryAxisParam t) = s⁻¹ • Hyperbolic.imaginaryAxisParam (t+Real.log k)
    apply (MulAction.injective s)
    change s • (A • (s⁻¹ • Hyperbolic.imaginaryAxisParam t)) = s • (s⁻¹ • Hyperbolic.imaginaryAxisParam (t+Real.log k))
    rw [smul_inv_smul]
    have he : s • (A • (s⁻¹ • Hyperbolic.imaginaryAxisParam t)) =
        (s*A*s⁻¹) • Hyperbolic.imaginaryAxisParam t := by simp only [mul_smul]
    rw [he,hact,imaginaryAxisParam_dilation_step]
  obtain ⟨C,hC,hCS,hstable,hcover⟩ := compact_core_of_line_translation γ hγ
    (⟨Hyperbolic.realSLMobius A,hA⟩ : H) (Real.log k) (Real.log_ne_zero_of_pos_of_ne_one hk hk1) hstep
  exact ⟨C,hC,hrange ▸ hCS,hrange ▸ hstable,hrange ▸ hcover⟩

/-- Compact subsets meet only finitely many distinct actual translates of a hyperbolic axis. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.hyperbolic_axis_translates_compact_finite
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Hyperbolic.realSLMobius A ∈ H) (hf : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (B : Set ℍ) (hB : IsCompact B) :
    letI := P.nativeAction
    {T | T ∈ translatedSubsetFamily (G := H) (Hyperbolic.hHyperbolicAxis A hf ht).carrier ∧
      (T ∩ B).Nonempty}.Finite := by
  let nativeAxisCompactAction := P.nativeAction
  let nativeAxisCompactProper := P.native_properlyDiscontinuous
  obtain ⟨C,hC,_hCS,hstable,hcover⟩ := P.hyperbolic_axis_compact_core A hA hf ht
  exact finite_translated_subsets_meeting_compact _ C B _ hC hB hstable hcover

/-- Only finitely many distinct actual axis translates are within any given native hyperbolic distance. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.hyperbolic_axis_translates_distance_finite
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Hyperbolic.realSLMobius A ∈ H) (hf : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (x : ℍ) (R : ℝ) :
    letI := P.nativeAction
    {T | T ∈ translatedSubsetFamily (G := H) (Hyperbolic.hHyperbolicAxis A hf ht).carrier ∧
      Metric.infDist x T ≤ R}.Finite := by
  let nativeAxisBoundAction := P.nativeAction
  let nativeAxisBoundProper := P.native_properlyDiscontinuous
  let nativeAxisBoundIsometric : IsIsometricSMul H ℍ := ⟨fun g => (P.nativeHom g).isometry⟩
  obtain ⟨C,hC,_hCS,hstable,hcover⟩ := P.hyperbolic_axis_compact_core A hA hf ht
  obtain ⟨z,_w,hz,_hw,_hzw⟩ := (Hyperbolic.hHyperbolicAxis A hf ht).exists_two_points
  exact finite_translated_subsets_distance_le _ C _ (Hyperbolic.hHyperbolicAxis A hf ht).isClosed_carrier
    ⟨z,hz⟩ hC hstable hcover x R

/-- Every point has a closest actual translated hyperbolic axis, including groups with axis-reversing half-turns. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.exists_closest_hyperbolic_axis
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Hyperbolic.realSLMobius A ∈ H) (hf : Hyperbolic.realSLMobius A ≠ 1)
    (ht : 4 < (Matrix.trace A.val)^2) (x : ℍ) :
    letI := P.nativeAction
    ∃ T ∈ translatedSubsetFamily (G := H) (Hyperbolic.hHyperbolicAxis A hf ht).carrier,
      ∀ U ∈ translatedSubsetFamily (G := H) (Hyperbolic.hHyperbolicAxis A hf ht).carrier,
        Metric.infDist x T ≤ Metric.infDist x U := by
  let nativeAxisClosestAction := P.nativeAction
  let nativeAxisClosestProper := P.native_properlyDiscontinuous
  let nativeAxisClosestIsometric : IsIsometricSMul H ℍ := ⟨fun g => (P.nativeHom g).isometry⟩
  obtain ⟨C,hC,_hCS,hstable,hcover⟩ := P.hyperbolic_axis_compact_core A hA hf ht
  obtain ⟨z,_w,hz,_hw,_hzw⟩ := (Hyperbolic.hHyperbolicAxis A hf ht).exists_two_points
  exact exists_closest_translated_subset _ C _ (Hyperbolic.hHyperbolicAxis A hf ht).isClosed_carrier
    ⟨z,hz⟩ hC hstable hcover x

/-- The literal actual axis-distance Voronoi region is open with no torsion exclusion. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.hyperbolic_axisVoronoi_isOpen
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Hyperbolic.realSLMobius A ∈ H) (hf : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2) :
    letI := P.nativeAction
    IsOpen (axisVoronoiRegion (G := H) (Hyperbolic.hHyperbolicAxis A hf ht).carrier) := by
  let nativeAxisOpenAction := P.nativeAction
  let nativeAxisOpenProper := P.native_properlyDiscontinuous
  let nativeAxisOpenIsometric : IsIsometricSMul H ℍ := ⟨fun g => (P.nativeHom g).isometry⟩
  obtain ⟨C,hC,_hCS,hstable,hcover⟩ := P.hyperbolic_axis_compact_core A hA hf ht
  obtain ⟨z,_w,hz,_hw,_hzw⟩ := (Hyperbolic.hHyperbolicAxis A hf ht).exists_two_points
  exact axisVoronoiRegion_isOpen _ C _ (Hyperbolic.hHyperbolicAxis A hf ht).isClosed_carrier
    ⟨z,hz⟩ hC hstable hcover

/-- The actual native simplicity condition controls different entire axis translates. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_axis_translates_disjoint
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (hs : Fuchsian.IsSimple H (Hyperbolic.realSLMobius A)) :
    letI := P.nativeAction
    ∀ T ∈ translatedSubsetFamily (G := H) (Hyperbolic.hHyperbolicAxis A hf ht).carrier,
      T ≠ (Hyperbolic.hHyperbolicAxis A hf ht).carrier → Disjoint (Hyperbolic.hHyperbolicAxis A hf ht).carrier T := by
  let nativeSimpleAxisAction := P.nativeAction
  have hstab := ((Hyperbolic.isSimple_iff_native_axis_stable H A hf ht (fun g hg =>
    Fuchsian.mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩))).mp hs).2
  intro T hT hne
  obtain ⟨g,rfl⟩ := hT
  have he : Hyperbolic.extendedHalfPlanePoint '' ((g • ·) '' (Hyperbolic.hHyperbolicAxis A hf ht).carrier) =
      g.val.val '' (Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.hHyperbolicAxis A hf ht).carrier) := by
    rw [image_image,image_image]
    apply Set.image_congr
    intro z _hz
    exact (P.nativeAction_boundary g z).symm
  rcases hstab g.val g.property with hsame | hdis
  · exact (hne (Hyperbolic.halfPlaneSpherePoint_injective.image_injective (he.trans hsame))).elim
  · apply (Set.disjoint_image_iff Hyperbolic.halfPlaneSpherePoint_injective).mp
    rw [he]
    exact hdis.symm

/-- The entire original simple hyperbolic axis lies in its true open nearest-axis region. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_axis_subset_Voronoi
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (hs : Fuchsian.IsSimple H (Hyperbolic.realSLMobius A)) :
    letI := P.nativeAction
    (Hyperbolic.hHyperbolicAxis A hf ht).carrier ⊆
      axisVoronoiRegion (G := H) (Hyperbolic.hHyperbolicAxis A hf ht).carrier := by
  let nativeSimpleVoronoiAction := P.nativeAction
  let nativeSimpleVoronoiIsometric : IsIsometricSMul H ℍ := ⟨fun g => (P.nativeHom g).isometry⟩
  obtain ⟨z,_w,hz,_hw,_hzw⟩ := (Hyperbolic.hHyperbolicAxis A hf ht).exists_two_points
  exact subset_axisVoronoiRegion_of_disjoint _ (Hyperbolic.hHyperbolicAxis A hf ht).isClosed_carrier
    ⟨z,hz⟩ (P.simple_axis_translates_disjoint A hf ht hs)

/-- The literal nearest-axis region is stable under the full set stabilizer, including any axis-reversing elements. -/
theorem axisVoronoiRegion_coset_stable {G X : Type*} [Group G] [MetricSpace X]
    [MulAction G X] [IsIsometricSMul G X] (S : Set X) :
    IsCosetStableRegion (MulAction.stabilizer G S) (axisVoronoiRegion (G := G) S) := by
  let K := MulAction.stabilizer G S
  have hdist (g : G) (x : X) (T : Set X) :
      Metric.infDist (g • x) (g • T) = Metric.infDist x T :=
    Metric.infDist_image (isometry_smul X g)
  have hmap (h : K) : h • axisVoronoiRegion (G := G) S ⊆ axisVoronoiRegion (G := G) S := by
    rintro _ ⟨x,hx,rfl⟩ T hT hn
    have hfix : h.val • S = S := h.property
    have hU : h.val⁻¹ • T ∈ translatedSubsetFamily (G := G) S := by
      obtain ⟨g,rfl⟩ := hT
      refine ⟨h.val⁻¹*g,?_⟩
      change h.val⁻¹ • (g • S) = (h.val⁻¹*g) • S
      exact (mul_smul _ _ _).symm
    have hUn : h.val⁻¹ • T ≠ S := by
      intro he
      have he' := congrArg (fun U : Set X => h.val • U) he
      rw [smul_inv_smul,hfix] at he'
      exact hn he'
    have hi := hx _ hU hUn
    have hleft : Metric.infDist (h.val • x) S = Metric.infDist x S := by
      calc _ = Metric.infDist (h.val • x) (h.val • S) := by rw [hfix]
           _ = _ := hdist _ _ _
    have hright : Metric.infDist (h.val • x) T = Metric.infDist x (h.val⁻¹ • T) := by
      calc _ = Metric.infDist (h.val • x) (h.val • (h.val⁻¹ • T)) := by rw [smul_inv_smul]
           _ = _ := hdist _ _ _
    change Metric.infDist (h.val • x) S < Metric.infDist (h.val • x) T
    rw [hleft,hright]
    exact hi
  refine ⟨?_,?_⟩
  · intro h
    apply Subset.antisymm (hmap h)
    intro x hx
    exact ⟨h⁻¹ • x,hmap h⁻¹ ⟨x,hx,rfl⟩,smul_inv_smul h x⟩
  · intro g hg
    have hn : g • S ≠ S := hg
    have hni : g⁻¹ • S ≠ S := by
      intro he
      apply hn
      have hh := congrArg (fun U : Set X => g • U) he
      rw [smul_inv_smul] at hh
      exact hh.symm
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ hy
    have h1 := hy (g • S) ⟨g,rfl⟩ hn
    have h2 := hx (g⁻¹ • S) ⟨g⁻¹,rfl⟩ hni
    rw [hdist] at h1
    have he : Metric.infDist (g • x) S = Metric.infDist x (g⁻¹ • S) := by
      calc _ = Metric.infDist (g • x) (g • (g⁻¹ • S)) := by rw [smul_inv_smul]
           _ = _ := hdist _ _ _
    rw [he] at h1
    exact h1.not_ge h2.le

end LowDimensionalTopology.Geometry.DiscreteGroups.Action
