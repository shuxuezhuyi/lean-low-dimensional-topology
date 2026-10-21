module
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSideInteriors
public import Mathlib.LinearAlgebra.Ray
public import Mathlib.Tactic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Surfaces


theorem three_real_products_one_nonnegative (a b c : ℝ) :
    0 ≤ a*b ∨ 0 ≤ a*c ∨ 0 ≤ b*c := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · exact Or.inl (mul_nonneg ha hb)
    · by_cases hc : 0 ≤ c
      · exact Or.inr (Or.inl (mul_nonneg ha hc))
      · exact Or.inr (Or.inr (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hb) (le_of_not_ge hc)))
  · by_cases hb : 0 ≤ b
    · by_cases hc : 0 ≤ c
      · exact Or.inr (Or.inr (mul_nonneg hb hc))
      · exact Or.inr (Or.inl (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ha) (le_of_not_ge hc)))
    · exact Or.inl (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ha) (le_of_not_ge hb))

theorem three_vectors_in_planar_kernel_sameRay (n p q r : ℂ) (hn : n ≠ 0)
    (hp : inner ℝ n p = 0) (hq : inner ℝ n q = 0) (hr : inner ℝ n r = 0) :
    SameRay ℝ p q ∨ SameRay ℝ p r ∨ SameRay ℝ q r := by
  obtain ⟨a,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_orthogonal_eq_real_smul n p hn hp
  obtain ⟨b,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_orthogonal_eq_real_smul n q hn hq
  obtain ⟨c,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_orthogonal_eq_real_smul n r hn hr
  rcases three_real_products_one_nonnegative a b c with h | h | h
  · exact Or.inl (sameRay_smul_smul_of_mul_nonneg h)
  · exact Or.inr (Or.inl (sameRay_smul_smul_of_mul_nonneg h))
  · exact Or.inr (Or.inr (sameRay_smul_smul_of_mul_nonneg h))

theorem kernel_halfplane_pair_sameRay_or_equal (n m p q : ℂ) (hn : n ≠ 0) (hm : m ≠ 0)
    (hp : inner ℝ n p = 0) (hq : inner ℝ n q = 0)
    (hpM : inner ℝ m p ≤ 0) (hqM : inner ℝ m q ≤ 0) :
    SameRay ℝ p q ∨ ∀ z : ℂ, inner ℝ n z = 0 ↔ inner ℝ m z = 0 := by
  obtain ⟨a,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_orthogonal_eq_real_smul n p hn hp
  obtain ⟨b,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_orthogonal_eq_real_smul n q hn hq
  by_cases hab : 0 ≤ a*b
  · exact Or.inl (sameRay_smul_smul_of_mul_nonneg hab)
  · have hab' : a*b < 0 := lt_of_not_ge hab
    let d := inner ℝ m (Complex.I*n)
    change inner ℝ m (a • (Complex.I*n)) ≤ 0 at hpM
    change inner ℝ m (b • (Complex.I*n)) ≤ 0 at hqM
    rw [real_inner_smul_right] at hpM hqM
    have hd : d = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hd | hd
      · have ha0 : 0 ≤ a := nonneg_of_mul_nonpos_left hpM hd
        have hb0 : 0 ≤ b := nonneg_of_mul_nonpos_left hqM hd
        exact hab (mul_nonneg ha0 hb0)
      · have ha0 : a ≤ 0 := nonpos_of_mul_nonpos_left hpM hd
        have hb0 : b ≤ 0 := nonpos_of_mul_nonpos_left hqM hd
        exact hab (mul_nonneg_of_nonpos_of_nonpos ha0 hb0)
    right
    intro z
    have horth : inner ℝ n (Complex.I*n) = 0 := by simp [Complex.inner]; ring
    exact _root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points hn hm
      (Ne.symm (mul_ne_zero Complex.I_ne_zero hn)) (by simp) horth (by simp) hd

/-- Three nonzero boundary directions of a true planar two-half-plane cone contain a repeated ray. -/
theorem two_halfplanes_three_boundary_directions_sameRay (n m p q r : ℂ)
    (hn : n ≠ 0) (hm : m ≠ 0)
    (hp : inner ℝ n p ≤ 0 ∧ inner ℝ m p ≤ 0 ∧ (inner ℝ n p = 0 ∨ inner ℝ m p = 0))
    (hq : inner ℝ n q ≤ 0 ∧ inner ℝ m q ≤ 0 ∧ (inner ℝ n q = 0 ∨ inner ℝ m q = 0))
    (hr : inner ℝ n r ≤ 0 ∧ inner ℝ m r ≤ 0 ∧ (inner ℝ n r = 0 ∨ inner ℝ m r = 0)) :
    SameRay ℝ p q ∨ SameRay ℝ p r ∨ SameRay ℝ q r := by
  have hpair (n m p q r : ℂ) (hn : n ≠ 0) (hm : m ≠ 0)
      (hp : inner ℝ n p = 0) (hq : inner ℝ n q = 0)
      (hpM : inner ℝ m p ≤ 0) (hqM : inner ℝ m q ≤ 0)
      (hr : inner ℝ n r = 0 ∨ inner ℝ m r = 0) :
      SameRay ℝ p q ∨ SameRay ℝ p r ∨ SameRay ℝ q r := by
    rcases kernel_halfplane_pair_sameRay_or_equal n m p q hn hm hp hq hpM hqM with h | he
    · exact Or.inl h
    · have hrN : inner ℝ n r = 0 := hr.elim id ((he r).mpr)
      exact three_vectors_in_planar_kernel_sameRay n p q r hn hp hq hrN
  by_cases hpN : inner ℝ n p = 0
  · by_cases hqN : inner ℝ n q = 0
    · exact hpair n m p q r hn hm hpN hqN hp.2.1 hq.2.1 hr.2.2
    · have hqM := hq.2.2.resolve_left hqN
      by_cases hrN : inner ℝ n r = 0
      · rcases hpair n m p r q hn hm hpN hrN hp.2.1 hr.2.1 hq.2.2 with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h.symm)
      · have hrM := hr.2.2.resolve_left hrN
        rcases hpair m n q r p hm hn hqM hrM hq.1 hr.1 (Or.inr hpN) with h | h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inl h.symm)
  · have hpM := hp.2.2.resolve_left hpN
    by_cases hqM : inner ℝ m q = 0
    · exact hpair m n p q r hm hn hpM hqM hp.1 hq.1 (hr.2.2.symm)
    · have hqN := hq.2.2.resolve_right hqM
      by_cases hrM : inner ℝ m r = 0
      · rcases hpair m n p r q hm hn hpM hrM hp.1 hr.1 (Or.inr hqN) with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h.symm)
      · have hrN := hr.2.2.resolve_right hrM
        rcases hpair n m q r p hn hm hqN hrN hq.2.1 hr.2.1 (Or.inr hpM) with h | h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inl h.symm)

theorem mem_frontier_two_halfplanes_constraints (n m z : ℂ)
    (hz : z ∈ frontier {w : ℂ | inner ℝ n w ≤ 0 ∧ inner ℝ m w ≤ 0}) :
    inner ℝ n z ≤ 0 ∧ inner ℝ m z ≤ 0 ∧ (inner ℝ n z = 0 ∨ inner ℝ m z = 0) := by
  let C : Set ℂ := {w | inner ℝ n w ≤ 0 ∧ inner ℝ m w ≤ 0}
  have hnC : Continuous (fun w : ℂ => inner ℝ n w) := continuous_const.inner continuous_id
  have hmC : Continuous (fun w : ℂ => inner ℝ m w) := continuous_const.inner continuous_id
  have hclosed : IsClosed C := by
    change IsClosed ({w : ℂ | inner ℝ n w ≤ 0} ∩ {w : ℂ | inner ℝ m w ≤ 0})
    exact (isClosed_le hnC continuous_const).inter (isClosed_le hmC continuous_const)
  have hzC : z ∈ C := hclosed.closure_eq ▸ frontier_subset_closure hz
  refine ⟨hzC.1,hzC.2, ?_⟩
  by_contra hn
  push Not at hn
  have hzN : z ∈ {w : ℂ | inner ℝ n w < 0 ∧ inner ℝ m w < 0} :=
    ⟨lt_of_le_of_ne hzC.1 hn.1,lt_of_le_of_ne hzC.2 hn.2⟩
  have hN : IsOpen {w : ℂ | inner ℝ n w < 0 ∧ inner ℝ m w < 0} := by
    change IsOpen ({w : ℂ | inner ℝ n w < 0} ∩ {w : ℂ | inner ℝ m w < 0})
    exact (isOpen_lt hnC continuous_const).inter (isOpen_lt hmC continuous_const)
  have hi : z ∈ interior C := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hN.mem_nhds hzN) (fun _ h => ⟨h.1.le,h.2.le⟩))
  exact hz.2 hi

theorem IsFuchsianPolygonSide.normalizedKlein_convex
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S : Set P.domain.carrier} (hS : IsFuchsianPolygonSide P D S) (x : P.domain.carrier) :
    Convex ℝ (normalizedPolygonKleinCoordinate P x '' S) := by
  have hconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (polygonPointCoordinate P x '' S) := by
    have he : polygonPointCoordinate P x '' S =
        discOriginNormalizer (P.finiteCoordinate x) '' (P.finiteCoordinate '' S) := by
      rw [image_image]; rfl
    rw [he]
    exact hS.2.1.1.isometry_image (discOriginNormalizer_isometry _)
  have heF : normalizedPolygonKleinCoordinate P x '' S =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P x '' S) := by rw [image_image]; rfl
  rw [heF]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp hconv

theorem IsConvexFuchsianPolygon.distinct_sides_inter_subsingleton
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S T : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hS : IsFuchsianPolygonSide P D S) (hT : IsFuchsianPolygonSide P D T) (hST : S ≠ T) :
    (S ∩ T).Subsingleton := by
  obtain ⟨g,hg,rfl,_⟩ := hD.side_iff.mp hS
  obtain ⟨h,hh,rfl,_⟩ := hD.side_iff.mp hT
  have hgh : g ≠ h := by rintro rfl; exact hST rfl
  intro x hx y hy
  exact hD.closed_tile_triple_subsingleton hg hh hgh ⟨hx.1,hx.2.2⟩ ⟨hy.1,hy.2.2⟩

theorem exists_small_smul_mem_open (v : ℂ) (N : Set ℂ) (hN : IsOpen N) (h0N : (0 : ℂ) ∈ N) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t • v ∈ N := by
  have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
  have hpre : (fun t : ℝ => t • v) ⁻¹' N ∈ 𝓝 (0 : ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa only [zero_smul] using hN.mem_nhds h0N
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hpre
  let t := min (r/2) (1/2)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htr : t < r := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨t,ht,(min_le_right _ _).trans_lt (by norm_num), ?_⟩
  exact hball (by rwa [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht])

theorem IsFuchsianPolygonSide.exists_normalized_near_point
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S : Set P.domain.carrier} (hS : IsFuchsianPolygonSide P D S)
    {x : P.domain.carrier} (hxS : x ∈ S) (N : Set ℂ) (hN : IsOpen N) (h0N : (0 : ℂ) ∈ N) :
    ∃ p : ℂ, p ≠ 0 ∧ p ∈ normalizedPolygonKleinCoordinate P x '' S ∧ p ∈ N := by
  obtain ⟨a,ha,hax⟩ := hS.2.2.exists_ne x
  let F := normalizedPolygonKleinCoordinate P x
  have hF := normalizedPolygonKleinCoordinate_isOpenEmbedding P x
  have hFa : F a ≠ 0 := by
    intro he
    exact hax (hF.injective (he.trans (normalizedPolygonKleinCoordinate_self P x).symm))
  obtain ⟨t,ht,ht1,htN⟩ := exists_small_smul_mem_open (F a) N hN h0N
  have hz : (0 : ℂ) ∈ F '' S := ⟨x,hxS,normalizedPolygonKleinCoordinate_self P x⟩
  exact ⟨t • F a,smul_ne_zero ht.ne' hFa,
    (hS.normalizedKlein_convex x).smul_mem_of_zero_mem hz ⟨a,ha,rfl⟩ ⟨ht.le,ht1.le⟩,htN⟩

theorem IsConvexFuchsianPolygon.sides_eq_of_sameRay
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S T : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hS : IsFuchsianPolygonSide P D S) (hT : IsFuchsianPolygonSide P D T)
    {x : P.domain.carrier} (hxS : x ∈ S) (hxT : x ∈ T)
    {p q : ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpS : p ∈ normalizedPolygonKleinCoordinate P x '' S)
    (hqT : q ∈ normalizedPolygonKleinCoordinate P x '' T) (hray : SameRay ℝ p q) : S = T := by
  let F := normalizedPolygonKleinCoordinate P x
  obtain ⟨a,b,ha,hb,he⟩ := hray.exists_pos hp hq
  let d := a+b+1
  have hd : 0 < d := by dsimp [d]; positivity
  let α := a/d
  let β := b/d
  have hα : 0 < α := div_pos ha hd
  have hβ : 0 < β := div_pos hb hd
  have hα1 : α ≤ 1 := (div_le_one hd).mpr (by dsimp [d]; linarith)
  have hβ1 : β ≤ 1 := (div_le_one hd).mpr (by dsimp [d]; linarith)
  have hw : α • p = β • q := by
    have hh := congrArg (fun z : ℂ => d⁻¹ • z) he
    simpa only [α,β,smul_smul,div_eq_mul_inv,mul_comm] using hh
  have hzS : (0 : ℂ) ∈ F '' S := ⟨x,hxS,normalizedPolygonKleinCoordinate_self P x⟩
  have hzT : (0 : ℂ) ∈ F '' T := ⟨x,hxT,normalizedPolygonKleinCoordinate_self P x⟩
  have hwS : α • p ∈ F '' S := (hS.normalizedKlein_convex x).smul_mem_of_zero_mem hzS hpS ⟨hα.le,hα1⟩
  have hwT : α • p ∈ F '' T := hw.symm ▸
    (hT.normalizedKlein_convex x).smul_mem_of_zero_mem hzT hqT ⟨hβ.le,hβ1⟩
  obtain ⟨u,huS,huF⟩ := hwS
  obtain ⟨v,hvT,hvF⟩ := hwT
  have huv : u = v := (normalizedPolygonKleinCoordinate_isOpenEmbedding P x).injective (huF.trans hvF.symm)
  have huT : u ∈ T := huv.symm ▸ hvT
  by_contra hST
  have hux : u = x := hD.distinct_sides_inter_subsingleton hS hT hST ⟨huS,huT⟩ ⟨hxS,hxT⟩
  have hwzero : α • p = (0 : ℂ) := by
    rw [← huF,hux]
    exact normalizedPolygonKleinCoordinate_self P x
  exact (smul_ne_zero hα.ne' hp) hwzero

/-- No actual boundary point can belong to three distinct original sides. -/
theorem IsConvexFuchsianPolygon.three_incident_sides_eq
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S T U : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hS : IsFuchsianPolygonSide P D S) (hT : IsFuchsianPolygonSide P D T)
    (hU : IsFuchsianPolygonSide P D U) {x : P.domain.carrier}
    (hxS : x ∈ S) (hxT : x ∈ T) (hxU : x ∈ U) : S = T ∨ S = U ∨ T = U := by
  have hx := hS.subset_frontier hD.locallyFinite.fundamental hxS
  obtain ⟨n,m,_a,N,hn,hm,hN,h0N,_hna,_hma,he⟩ := hD.local_two_halfplanes x hx
  obtain ⟨p,hp,hpS,hpN⟩ := hS.exists_normalized_near_point hxS N hN h0N
  obtain ⟨q,hq,hqT,hqN⟩ := hT.exists_normalized_near_point hxT N hN h0N
  obtain ⟨r,hr,hrU,hrN⟩ := hU.exists_normalized_near_point hxU N hN h0N
  have hboundary (V : Set P.domain.carrier) (hV : IsFuchsianPolygonSide P D V)
      (z : ℂ) (hzV : z ∈ normalizedPolygonKleinCoordinate P x '' V) (hzN : z ∈ N) :
      inner ℝ n z ≤ 0 ∧ inner ℝ m z ≤ 0 ∧ (inner ℝ n z = 0 ∨ inner ℝ m z = 0) := by
    obtain ⟨y,hy,hey⟩ := hzV
    have hyfront := hV.subset_frontier hD.locallyFinite.fundamental hy
    have hzfront : z ∈ frontier (normalizedPolygonKleinCoordinate P x '' closure D) :=
      hey ▸ (hD.normalizedKlein_frontier_iff x y).mpr hyfront
    have hg := frontiers_equal_on_open_germ hN he
    have hzC : z ∈ frontier {w : ℂ | inner ℝ n w ≤ 0 ∧ inner ℝ m w ≤ 0} :=
      (hg ▸ (show z ∈ frontier (normalizedPolygonKleinCoordinate P x '' closure D) ∩ N from ⟨hzfront,hzN⟩)).1
    exact mem_frontier_two_halfplanes_constraints n m z hzC
  rcases two_halfplanes_three_boundary_directions_sameRay n m p q r hn hm
    (hboundary S hS p hpS hpN) (hboundary T hT q hqT hqN) (hboundary U hU r hrU hrN) with h | h | h
  · exact Or.inl (hD.sides_eq_of_sameRay hS hT hxS hxT hp hq hpS hqT h)
  · exact Or.inr (Or.inl (hD.sides_eq_of_sameRay hS hU hxS hxU hp hr hpS hrU h))
  · exact Or.inr (Or.inr (hD.sides_eq_of_sameRay hT hU hxT hxU hq hr hqT hrU h))

theorem IsConvexFuchsianPolygon.side_normalizedKlein_support
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hS : IsFuchsianPolygonSide P D S) {x : P.domain.carrier} (hxS : x ∈ S) :
    ∃ n : ℂ, n ≠ 0 ∧ ∀ y ∈ S, inner ℝ n (normalizedPolygonKleinCoordinate P x y) = 0 := by
  obtain ⟨g,hg,heS,_⟩ := hD.side_iff.mp hS
  let F := normalizedPolygonKleinCoordinate P x
  let U : H → Set ℂ := fun h => F '' (h • D)
  have hF := normalizedPolygonKleinCoordinate_isOpenEmbedding P x
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hDn := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hUc (h : H) : Convex ℝ (U h) := by
    have heU : U h = _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P x '' (h • D)) := by rw [image_image]; rfl
    rw [heU]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp (hD.pointCoordinate_smul_convex x h)
  have hUo (h : H) : IsOpen (U h) := hF.isOpenMap _ ((Homeomorph.smul h).isOpenMap D hDo)
  have hUn (h : H) : (U h).Nonempty := (hDn.image (fun y => h • y)).image F
  have hdis : Disjoint (U 1) (U g) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨a,ha,haz⟩ ⟨b,hb,hbz⟩
    have hab := hF.injective (haz.trans hbz.symm)
    exact hg (hD.locallyFinite.fundamental.tile_intersection_eq (hab ▸ hb) ha)
  obtain ⟨n,t,hn,hl,hr⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.convex_open_disjoint_strict_separator
    (hUc 1) (hUo 1) (hUn 1) (hUc g) (hUo g) (hUn g) hdis
  have hclosed (h : H) : F '' fuchsianDomainTile P D h ⊆ closure (U h) := by
    change F '' (h • closure D) ⊆ _
    have he : h • closure D = closure (h • D) := (Homeomorph.smul h).image_closure D
    rw [he]
    exact image_closure_subset_closure_image hF.continuous
  have hzero (y : P.domain.carrier) (hy : y ∈ S) : inner ℝ n (F y) = t := by
    rw [heS] at hy
    exact _root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hl hr
      ⟨hclosed 1 ⟨y,by simpa only [fuchsianDomainTile,one_smul] using hy.1,rfl⟩,
        hclosed g ⟨y,hy.2,rfl⟩⟩
  have ht : t = 0 := by
    have hx := hzero x hxS
    change inner ℝ n (normalizedPolygonKleinCoordinate P x x) = t at hx
    rw [normalizedPolygonKleinCoordinate_self,inner_zero_right] at hx
    exact hx.symm
  exact ⟨n,hn,fun y hy => (hzero y hy).trans ht⟩

theorem planar_kernel_angle_zero_or_pi (n u v : ℂ) (hn : n ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hnu : inner ℝ n u = 0) (hnv : inner ℝ n v = 0) :
    InnerProductGeometry.angle u v = 0 ∨ InnerProductGeometry.angle u v = Real.pi := by
  obtain ⟨a,ha⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_orthogonal_eq_real_smul n u hn hnu
  obtain ⟨b,hb⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_orthogonal_eq_real_smul n v hn hnv
  have ha0 : a ≠ 0 := by intro h; rw [ha,h,zero_smul] at hu; exact hu rfl
  have hb0 : b ≠ 0 := by intro h; rw [hb,h,zero_smul] at hv; exact hv rfl
  have he : v = (b/a) • u := by rw [ha,hb,smul_smul,div_mul_cancel₀ b ha0]
  have hr : b/a ≠ 0 := div_ne_zero hb0 ha0
  rcases lt_or_gt_of_ne hr with hr | hr
  · exact Or.inr (InnerProductGeometry.angle_eq_pi_iff.mpr ⟨hu,b/a,hr,he⟩)
  · exact Or.inl (InnerProductGeometry.angle_eq_zero_iff.mpr ⟨hu,b/a,hr,he⟩)

theorem exists_two_pos_smul_mem_open (u v : ℂ) (N : Set ℂ) (hN : IsOpen N) (h0N : (0 : ℂ) ∈ N) :
    ∃ t : ℝ, 0 < t ∧ t • u ∈ N ∧ t • v ∈ N := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hN.mem_nhds h0N)
  let d := ‖u‖+‖v‖+1
  have hd : 0 < d := by dsimp [d]; positivity
  let t := r/(2*d)
  have ht : 0 < t := div_pos hr (mul_pos (by norm_num) hd)
  have he : t*d = r/2 := by dsimp [t]; field_simp
  have hnorm (z : ℂ) (hz : ‖z‖ ≤ d) : ‖t • z‖ < r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    calc
      _ ≤ t*d := mul_le_mul_of_nonneg_left hz ht.le
      _ = r/2 := he
      _ < r := by linarith
  exact ⟨t,ht,hball (by rw [Metric.mem_ball,dist_zero_right]; exact hnorm u (by dsimp [d]; linarith [norm_nonneg v])),
    hball (by rw [Metric.mem_ball,dist_zero_right]; exact hnorm v (by dsimp [d]; linarith [norm_nonneg u]))⟩

theorem IsConvexFuchsianPolygon.point_of_normalized_frontier_germ
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (x : P.domain.carrier)
    (C N : Set ℂ) (hN : IsOpen N)
    (he : (normalizedPolygonKleinCoordinate P x '' closure D) ∩ N = C ∩ N)
    (O : Set P.domain.carrier) (z : ℂ) (hzC : z ∈ frontier C) (hzN : z ∈ N)
    (hzO : z ∈ normalizedPolygonKleinCoordinate P x '' O) :
    ∃ y ∈ frontier D ∩ O, normalizedPolygonKleinCoordinate P x y = z := by
  obtain ⟨y,hyO,hey⟩ := hzO
  have hg := frontiers_equal_on_open_germ hN he
  have hzA : z ∈ frontier (normalizedPolygonKleinCoordinate P x '' closure D) :=
    (hg.symm ▸ (show z ∈ frontier C ∩ N from ⟨hzC,hzN⟩)).1
  exact ⟨y,⟨(hD.normalizedKlein_frontier_iff x y).mp (hey.symm ▸ hzA),hyO⟩,hey⟩

/-- If the actual boundary near a point lies on one side, that point is strictly inside its actual geodesic interval. -/
theorem IsConvexFuchsianPolygon.side_interior_of_boundary_subset_near
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hS : IsFuchsianPolygonSide P D S) {x : P.domain.carrier} (hxS : x ∈ S)
    (O : Set P.domain.carrier) (hOo : IsOpen O) (hxO : x ∈ O)
    (hnear : frontier D ∩ O ⊆ S) : IsFuchsianPolygonSideInterior P D x := by
  have hx := hS.subset_frontier hD.locallyFinite.fundamental hxS
  let F := normalizedPolygonKleinCoordinate P x
  have hF := normalizedPolygonKleinCoordinate_isOpenEmbedding P x
  have h0FO : (0 : ℂ) ∈ F '' O := ⟨x,hxO,normalizedPolygonKleinCoordinate_self P x⟩
  rcases hD.boundary_geometric_angle x hx with ⟨q,N,hq,hN,h0N,he,_hangle⟩ |
    ⟨u,v,N,hu,hv,hθpos,hθ,hN,h0N,he,_hangle⟩
  · let v := Complex.I*q
    have hv : v ≠ 0 := mul_ne_zero Complex.I_ne_zero hq
    have hqv : inner ℝ q v = 0 := by simp [v,Complex.inner]; ring
    obtain ⟨t,ht,htv,htneg⟩ := exists_two_pos_smul_mem_open v (-v) (N ∩ (F '' O))
      (hN.inter (hF.isOpenMap O hOo)) ⟨h0N,h0FO⟩
    have hline (z : ℂ) (hz : inner ℝ q z = 0) : z ∈ frontier {w : ℂ | inner ℝ q w ≤ 0} :=
      mem_frontier_of_supporting_halfplane hq (subset_refl _) hz.le hz
    obtain ⟨a,ha,haF⟩ := hD.point_of_normalized_frontier_germ x _ N hN he O (t • v)
      (hline _ (by rw [real_inner_smul_right,hqv,mul_zero])) htv.1 htv.2
    obtain ⟨b,hb,hbF⟩ := hD.point_of_normalized_frontier_germ x _ N hN he O (t • (-v))
      (hline _ (by rw [real_inner_smul_right,inner_neg_right,hqv,neg_zero,mul_zero])) htneg.1 htneg.2
    have hab : a ≠ b := by
      intro hab
      have heq : t • v = -(t • v) := by
        simpa only [smul_neg] using haF.symm.trans
          ((congrArg (normalizedPolygonKleinCoordinate P x) hab).trans hbF)
      have hre := congrArg Complex.re heq
      have him := congrArg Complex.im heq
      simp only [Complex.neg_re] at hre
      simp only [Complex.neg_im] at him
      have hz : t • v = (0 : ℂ) := Complex.ext (by simp only [Complex.zero_re]; linarith)
        (by simp only [Complex.zero_im]; linarith)
      exact (smul_ne_zero ht.ne' hv) hz
    refine ⟨S,hS,a,hnear ha,b,hnear hb,hab, ?_⟩
    rw [normalizedPolygonKleinCoordinate_self,haF,hbF]
    exact ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,by simp⟩
  · let C : Set ℂ := {z | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • u + β • v}
    obtain ⟨t,ht,htu,htv⟩ := exists_two_pos_smul_mem_open u v (N ∩ (F '' O))
      (hN.inter (hF.isOpenMap O hOo)) ⟨h0N,h0FO⟩
    have hCu : t • u ∈ frontier C := positive_cone_boundary_ray u v hu t ht.le
    have hCv : t • v ∈ frontier C := by
      have hh := positive_cone_boundary_ray v u hv t ht.le
      have hswap : {z : ℂ | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • v + β • u} = C := by
        ext z
        constructor <;> rintro ⟨α,hα,β,hβ,rfl⟩ <;> exact ⟨β,hβ,α,hα,add_comm _ _⟩
      exact hswap ▸ hh
    obtain ⟨a,ha,haF⟩ := hD.point_of_normalized_frontier_germ x C N hN he O (t • u) hCu htu.1 htu.2
    obtain ⟨b,hb,hbF⟩ := hD.point_of_normalized_frontier_germ x C N hN he O (t • v) hCv htv.1 htv.2
    obtain ⟨n,hn,hline⟩ := hD.side_normalizedKlein_support hS hxS
    have hnu : inner ℝ n u = 0 := by
      have hh := hline a (hnear ha)
      rw [haF,real_inner_smul_right] at hh
      exact (mul_eq_zero.mp hh).resolve_left ht.ne'
    have hnv : inner ℝ n v = 0 := by
      have hh := hline b (hnear hb)
      rw [hbF,real_inner_smul_right] at hh
      exact (mul_eq_zero.mp hh).resolve_left ht.ne'
    rcases planar_kernel_angle_zero_or_pi n u v hn hu hv hnu hnv with heq | heq
    · exact False.elim (hθpos.ne' heq)
    · exact False.elim (hθ.ne heq)

theorem IsConvexFuchsianPolygon.vertex_exists_two_sides
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {x : P.domain.carrier} (hx : IsFuchsianPolygonVertex P D x) :
    ∃ S T : Set P.domain.carrier, IsFuchsianPolygonSide P D S ∧ IsFuchsianPolygonSide P D T ∧
      S ≠ T ∧ x ∈ S ∧ x ∈ T := by
  classical
  have hxfront := hx.mem_frontier hD.locallyFinite.fundamental
  obtain ⟨S,hS,hxS⟩ := hD.boundary_mem_side hxfront
  by_contra hnone
  have huniq (T : Set P.domain.carrier) (hT : IsFuchsianPolygonSide P D T) (hxT : x ∈ T) : T = S := by
    by_contra hTS
    exact hnone ⟨S,T,hS,hT,Ne.symm hTS,hxS,hxT⟩
  obtain ⟨N,_hNc,hNx,_hf,_hcover,hd⟩ := hD.locallyFinite.finite_neighborhood_star x
  obtain ⟨O,hON,hOo,hxO⟩ := mem_nhds_iff.mp hNx
  have hnear : frontier D ∩ O ⊆ S := by
    rintro y ⟨hyfront,hyO⟩
    obtain ⟨T,hT,hyT⟩ := hD.boundary_mem_side hyfront
    obtain ⟨g,hg,heT,_⟩ := hD.side_iff.mp hT
    have hyt : y ∈ fuchsianDomainTile P D g := (heT ▸ hyT).2
    have hxt : x ∈ fuchsianDomainTile P D g := by
      by_contra hn
      exact Set.disjoint_left.mp (hd g hn) (hON hyO) hyt
    have hxT : x ∈ T := heT.symm ▸ ⟨frontier_subset_closure hxfront,hxt⟩
    exact huniq T hT hxT ▸ hyT
  exact hD.vertex_not_side_interior hx (hD.side_interior_of_boundary_subset_near hS hxS O hOo hxO hnear)

/-- Every original vertex belongs to exactly two genuine sides and is the endpoint of each. -/
theorem IsConvexFuchsianPolygon.vertex_exactly_two_sides
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {x : P.domain.carrier} (hx : IsFuchsianPolygonVertex P D x) :
    ∃ S T : Set P.domain.carrier, IsFuchsianPolygonSide P D S ∧ IsFuchsianPolygonSide P D T ∧
      S ≠ T ∧ x ∈ S ∧ x ∈ T ∧
      (∀ U : Set P.domain.carrier, (IsFuchsianPolygonSide P D U ∧ x ∈ U) ↔ U = S ∨ U = T) ∧
      IsFuchsianPolygonSideEndpoint P S x ∧ IsFuchsianPolygonSideEndpoint P T x := by
  obtain ⟨S,T,hS,hT,hST,hxS,hxT⟩ := hD.vertex_exists_two_sides hx
  refine ⟨S,T,hS,hT,hST,hxS,hxT, ?_,hD.vertex_side_endpoint hx hS hxS,hD.vertex_side_endpoint hx hT hxT⟩
  intro U
  constructor
  · rintro ⟨hU,hxU⟩
    rcases hD.three_incident_sides_eq hS hT hU hxS hxT hxU with he | he | he
    · exact False.elim (hST he)
    · exact Or.inl he.symm
    · exact Or.inr he.symm
  · rintro (rfl | rfl)
    · exact ⟨hS,hxS⟩
    · exact ⟨hT,hxT⟩

/-- The original immediate consequence of properties(5)-(6): three distinct sides have empty intersection. -/
theorem IsConvexFuchsianPolygon.three_distinct_sides_inter_empty
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S T U : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hS : IsFuchsianPolygonSide P D S) (hT : IsFuchsianPolygonSide P D T)
    (hU : IsFuchsianPolygonSide P D U) (hST : S ≠ T) (hSU : S ≠ U) (hTU : T ≠ U) :
    S ∩ T ∩ U = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases hD.three_incident_sides_eq hS hT hU hx.1.1 hx.1.2 hx.2 with he | he | he
  · exact hST he
  · exact hSU he
  · exact hTU he

end LowDimensionalTopology.Geometry.Fuchsian
