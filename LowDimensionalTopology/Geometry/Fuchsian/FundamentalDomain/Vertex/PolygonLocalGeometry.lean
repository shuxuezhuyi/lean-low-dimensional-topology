module
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSidePairing
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonAngles
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.PositiveConeAngularMeasure
public import Mathlib.Tactic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped Complex.UnitDisc Pointwise NNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Surfaces

/-- A genuine finite convex covering determines the central tile locally by its actual supporting half-planes. -/
theorem finite_convex_cover_germ {ι : Type*} (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ s)
    (U : ι → Set ℂ) (hc : ∀ i ∈ s, Convex ℝ (U i)) (ho : ∀ i ∈ s, IsOpen (U i))
    (hn : ∀ i ∈ s, (U i).Nonempty) (hd : ∀ i ∈ s, i ≠ i₀ → Disjoint (U i₀) (U i))
    (hz : ∀ i ∈ s, (0 : ℂ) ∈ closure (U i))
    (N : Set ℂ) (hN : IsOpen N) (h0N : (0 : ℂ) ∈ N)
    (hcover : N ⊆ ⋃ i ∈ s, closure (U i)) :
    ∃ n : {i // i ∈ s ∧ i ≠ i₀} → ℂ,
      (∀ i, n i ≠ 0 ∧ (∀ z ∈ U i₀, inner ℝ (n i) z < 0) ∧
        (∀ z ∈ U i.val, 0 < inner ℝ (n i) z)) ∧
      (0 : ℂ) ∈ N ∧ closure (U i₀) ∩ N = {z | ∀ i, inner ℝ (n i) z ≤ 0} ∩ N := by
  have hsep (i : {i // i ∈ s ∧ i ≠ i₀}) :
      ∃ n : ℂ, n ≠ 0 ∧ (∀ z ∈ U i₀, inner ℝ n z < 0) ∧
        (∀ z ∈ U i.val, 0 < inner ℝ n z) := by
    obtain ⟨n, t, hnn, hleft, hright⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.convex_open_disjoint_strict_separator
      (hc i₀ hi₀) (ho i₀ hi₀) (hn i₀ hi₀) (hc i.val i.property.1)
      (ho i.val i.property.1) (hn i.val i.property.1) (hd i.val i.property.1 i.property.2)
    have ht : t = 0 := by
      have h := _root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hleft hright ⟨hz i₀ hi₀, hz i.val i.property.1⟩
      simpa only [inner_zero_right] using h.symm
    exact ⟨n, hnn, ht ▸ hleft, ht ▸ hright⟩
  choose n hn' using hsep
  refine ⟨n, hn', h0N, ?_⟩
  apply subset_antisymm
  · rintro z ⟨hzU, hzN⟩
    refine ⟨fun i => ?_, hzN⟩
    exact (closure_minimal (fun u hu => (hn' i).2.1 u hu |>.le)
      (isClosed_le (continuous_const.inner continuous_id) continuous_const)) hzU
  · rintro z ⟨hzQ, hzN⟩
    refine ⟨?_, hzN⟩
    obtain ⟨a, ha⟩ := hn i₀ hi₀
    let f : ℝ → ℂ := fun t => (1 - t) • z + t • a
    have hf : Continuous f := (continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const)
    have hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 z) := by
      convert hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
      simp [f]
    have hNevent : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), f t ∈ N := hlim.eventually (hN.mem_nhds hzN)
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    have hlt : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have hmem : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), f t ∈ closure (U i₀) := by
      filter_upwards [hNevent, hpos, hlt] with t htN ht0 ht1
      obtain ⟨i, hi, hfi⟩ := mem_iUnion₂.mp (hcover htN)
      by_cases hie : i = i₀
      · simpa only [hie] using hfi
      · let j : {i // i ∈ s ∧ i ≠ i₀} := ⟨i, hi, hie⟩
        have hright : 0 ≤ inner ℝ (n j) (f t) :=
          (closure_minimal (fun u hu => ((hn' j).2.2 u hu).le)
            (isClosed_le continuous_const (continuous_const.inner continuous_id))) hfi
        have he : inner ℝ (n j) (f t) =
            (1 - t) * inner ℝ (n j) z + t * inner ℝ (n j) a := by
          simp only [f, inner_add_right, real_inner_smul_right]
        have hneg := mul_neg_of_pos_of_neg ht0 ((hn' j).2.1 a ha)
        have hnonpos := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1.le) (hzQ j)
        rw [he] at hright
        exact (by linarith : False).elim
    exact isClosed_closure.mem_of_tendsto hlim hmem

/-- Genuine original-disc coordinates, normalized at the actual point, followed by the genuine Klein map. -/
def normalizedPolygonKleinCoordinate {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) : P.domain.carrier → ℂ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ∘ polygonPointCoordinate P x

theorem normalizedPolygonKleinCoordinate_isOpenEmbedding
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) :
    Topology.IsOpenEmbedding (normalizedPolygonKleinCoordinate P x) :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_kleinCoordinate.comp (polygonPointCoordinate P x).isOpenEmbedding

theorem normalizedPolygonKleinCoordinate_self
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) : normalizedPolygonKleinCoordinate P x x = 0 := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (polygonPointCoordinate P x x) = 0
  rw [polygonPointCoordinate_self]
  simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]

/-- Every actual closed polygon has a genuine finite homogeneous-half-plane germ at every one of its points. -/
theorem IsConvexFuchsianPolygon.local_finite_cone
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) (hx : x ∈ closure D) :
    ∃ (s : Finset H) (n : {g // g ∈ s ∧ g ≠ 1} → ℂ) (N : Set ℂ),
      IsOpen N ∧ (0 : ℂ) ∈ N ∧
      (∀ i, n i ≠ 0) ∧
      (∀ i, ∀ a ∈ normalizedPolygonKleinCoordinate P x '' D, inner ℝ (n i) a < 0) ∧
      ((normalizedPolygonKleinCoordinate P x '' closure D) ∩ N =
        {z | ∀ i, inner ℝ (n i) z ≤ 0} ∩ N) ∧
      (∀ g : H, g ∈ s ↔ x ∈ fuchsianDomainTile P D g) := by
  classical
  let F := normalizedPolygonKleinCoordinate P x
  have hF := normalizedPolygonKleinCoordinate_isOpenEmbedding P x
  have hFx : F x = 0 := normalizedPolygonKleinCoordinate_self P x
  let U : H → Set ℂ := fun g => F '' (g • D)
  let s := (hD.locallyFinite.incident_finite x).toFinset
  have hs (g : H) : g ∈ s ↔ x ∈ fuchsianDomainTile P D g := Set.Finite.mem_toFinset _
  have hi₀ : (1 : H) ∈ s := (hs 1).mpr (by simpa only [fuchsianDomainTile, one_smul] using hx)
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hDn := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hUc (g : H) : Convex ℝ (U g) := by
    have he : U g = _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P x '' (g • D)) := by
      rw [image_image]
      rfl
    rw [he]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp (hD.pointCoordinate_smul_convex x g)
  have hUo (g : H) : IsOpen (U g) := hF.isOpenMap _ ((Homeomorph.smul g).isOpenMap D hDo)
  have hUn (g : H) : (U g).Nonempty := (hDn.image (fun y => g • y)).image F
  have him (g : H) : F '' fuchsianDomainTile P D g ⊆ closure (U g) := by
    have he : fuchsianDomainTile P D g = closure (g • D) := (Homeomorph.smul g).image_closure D
    rw [he]
    exact image_closure_subset_closure_image hF.continuous
  have hUz (g : H) (hg : g ∈ s) : (0 : ℂ) ∈ closure (U g) :=
    him g ⟨x, (hs g).mp hg, hFx⟩
  have hUd (g : H) (_hg : g ∈ s) (hg : g ≠ 1) : Disjoint (U 1) (U g) := by
    change Disjoint (F '' (1 • D)) (F '' (g • D))
    rw [one_smul]
    exact (hD.locallyFinite.fundamental.disjoint_image hg).symm.image hF.injective.injOn
      (subset_univ _) (subset_univ _)
  obtain ⟨K, _hK, hKx, _hI, hcoverK, _havoid⟩ := hD.locallyFinite.finite_neighborhood_star x
  obtain ⟨O, hOK, hOo, hxO⟩ := mem_nhds_iff.mp hKx
  let N := F '' O
  have hN : IsOpen N := hF.isOpenMap O hOo
  have h0N : (0 : ℂ) ∈ N := ⟨x, hxO, hFx⟩
  have hcover : N ⊆ ⋃ g ∈ s, closure (U g) := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨g, hg, hgy⟩ := mem_iUnion₂.mp (hcoverK (hOK hy))
    exact mem_iUnion₂.mpr ⟨g, (hs g).mpr hg, him g (mem_image_of_mem F hgy)⟩
  obtain ⟨n, hn, _h0, he⟩ := finite_convex_cover_germ s 1 hi₀ U (fun g _ => hUc g)
    (fun g _ => hUo g) (fun g _ => hUn g) hUd hUz N hN h0N hcover
  refine ⟨s, n, N, hN, h0N, fun i => (hn i).1, ?_, ?_, hs⟩
  · intro i a ha
    apply (hn i).2.1 a
    simpa only [U, one_smul] using ha
  · have hU₁ : U 1 = F '' D := by simp only [U, one_smul]
    rw [hU₁] at he
    calc
      (F '' closure D) ∩ N = closure (F '' D) ∩ N := by
        apply subset_antisymm
        · exact inter_subset_inter_left N (image_closure_subset_closure_image hF.continuous)
        · rintro z ⟨hzcl, hzN⟩
          obtain ⟨y, hyO, hyz⟩ := hzN
          refine ⟨⟨y, ?_, hyz⟩, ⟨y, hyO, hyz⟩⟩
          rw [hF.isEmbedding.closure_eq_preimage_closure_image]
          change F y ∈ closure (F '' D)
          exact hyz.symm ▸ hzcl
      _ = _ := he

/-- A finite family of genuine planar half-plane constraints with a common strict interior direction is determined by two extreme slopes. -/
theorem finite_negative_linear_constraints_two_extremes {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (ha : ∀ i, a i < 0) :
    ∃ i j : ι, ∀ s t : ℝ,
      (∀ k, a k * s + b k * t ≤ 0) ↔
        (a i * s + b i * t ≤ 0 ∧ a j * s + b j * t ≤ 0) := by
  classical
  let k : ι → ℝ := fun i => -(b i) / a i
  have he (i : ι) (s t : ℝ) : a i * s + b i * t ≤ 0 ↔ k i * t ≤ s := by
    have hid : a i * (s - k i * t) = a i * s + b i * t := by
      dsimp [k]
      field_simp [(ha i).ne]
      ring
    rw [← hid]
    constructor
    · intro hh
      by_contra hle
      have hneg : s - k i * t < 0 := by linarith
      exact hh.not_gt (mul_pos_of_neg_of_neg (ha i) hneg)
    · intro hle
      exact mul_nonpos_of_nonpos_of_nonneg (ha i).le (sub_nonneg.mpr hle)
  obtain ⟨i, _hi, hmin⟩ := Finset.exists_min_image Finset.univ k Finset.univ_nonempty
  obtain ⟨j, _hj, hmax⟩ := Finset.exists_max_image Finset.univ k Finset.univ_nonempty
  refine ⟨i, j, fun s t => ?_⟩
  simp only [he]
  constructor
  · intro h; exact ⟨h i, h j⟩
  · rintro ⟨hi, hj⟩ l
    by_cases ht : 0 ≤ t
    · exact (mul_le_mul_of_nonneg_right (hmax l (Finset.mem_univ l)) ht).trans hj
    · exact (mul_le_mul_of_nonpos_right (hmin l (Finset.mem_univ l)) (le_of_lt (lt_of_not_ge ht))).trans hi


/-- The actual finite supporting half-planes in the plane reduce to two of the actual normals. -/
theorem finite_planar_halfplanes_two_extremes {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ι → ℂ) (v : ℂ) (hv : ∀ i, inner ℝ (n i) v < 0) :
    ∃ i j : ι, ∀ z : ℂ,
      (∀ k, inner ℝ (n k) z ≤ 0) ↔
        (inner ℝ (n i) z ≤ 0 ∧ inner ℝ (n j) z ≤ 0) := by
  have hvn : v ≠ 0 := by
    intro h
    have he := hv (Classical.arbitrary ι)
    simp only [h, inner_zero_right, lt_self_iff_false] at he
  obtain ⟨i, j, he⟩ := finite_negative_linear_constraints_two_extremes
    (fun i => inner ℝ (n i) v) (fun i => inner ℝ (n i) (Complex.I * v)) hv
  refine ⟨i, j, fun z => ?_⟩
  obtain ⟨s, t, rfl⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_basis_direction_representation v z hvn
  simpa only [inner_add_right, real_inner_smul_right, mul_comm] using he s t

/-- Every actual boundary point has a genuine two-supporting-half-plane germ, including the straight-angle case. -/
theorem IsConvexFuchsianPolygon.local_two_halfplanes
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) (hx : x ∈ frontier D) :
    ∃ (n m : ℂ) (a : ℂ) (N : Set ℂ), n ≠ 0 ∧ m ≠ 0 ∧ IsOpen N ∧ (0 : ℂ) ∈ N ∧
      inner ℝ n a < 0 ∧ inner ℝ m a < 0 ∧
      ((normalizedPolygonKleinCoordinate P x '' closure D) ∩ N =
        {z | inner ℝ n z ≤ 0 ∧ inner ℝ m z ≤ 0} ∩ N) := by
  classical
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hfront : x ∈ closure D ∧ x ∉ D := by
    simpa only [frontier, hDo.interior_eq, Set.mem_sdiff] using hx
  obtain ⟨s, n, N, hN, h0N, hnn, hnstrict, he, _hincident⟩ := hD.local_finite_cone x hfront.1
  let I := {g : H // g ∈ s ∧ g ≠ 1}
  have hIfinite : Finite I := Finite.of_injective
    (fun i : I => (⟨i.val, i.property.1⟩ : s)) (by intro a b he; apply Subtype.ext; exact congrArg (fun q : s => q.val) he)
  let : Finite I := hIfinite
  let : Fintype I := Fintype.ofFinite I
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    obtain ⟨a, ha⟩ := (((isFuchsianFundamentalDomain_iff P D).mp
      hD.locallyFinite.fundamental).2.1.nonempty).image (normalizedPolygonKleinCoordinate P x)
    obtain ⟨i, j, hij⟩ := finite_planar_halfplanes_two_extremes n a (fun i => hnstrict i a ha)
    refine ⟨n i, n j, a, N, hnn i, hnn j, hN, h0N, hnstrict i a ha, hnstrict j a ha, ?_⟩
    rw [he]
    congr 1
    ext z
    exact hij z
  · let : IsEmpty I := not_nonempty_iff.mp hI
    let F := normalizedPolygonKleinCoordinate P x
    have hF := normalizedPolygonKleinCoordinate_isOpenEmbedding P x
    have hFx : F x = 0 := normalizedPolygonKleinCoordinate_self P x
    have hpre : F ⁻¹' N ∈ 𝓝 x := hF.continuous.continuousAt (by change N ∈ 𝓝 (F x); rw [hFx]; exact hN.mem_nhds h0N)
    have hsub : F ⁻¹' N ⊆ closure D := by
      intro y hy
      have hq : F y ∈ {z | ∀ i, inner ℝ (n i) z ≤ 0} ∩ N :=
        ⟨fun i => isEmptyElim (i : I), hy⟩
      rw [← he] at hq
      obtain ⟨z, hz, hez⟩ := hq.1
      exact hF.injective hez ▸ hz
    have hxic : x ∈ interior (closure D) :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hpre hsub)
    rw [hD.interior_closure] at hxic
    exact (hfront.2 hxic).elim

theorem kleinRadial_halfplane_sign (r : Ioo (0 : ℝ) 1) (u : Circle) (n : ℂ) :
    inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (discRadialPoint r u)) ≤ 0 ↔ inner ℝ n (u : ℂ) ≤ 0 := by
  rw [kleinCoordinate_discRadialPoint]
  change inner ℝ n ((2 * r.val / (1 + r.val ^ 2)) • (u : ℂ)) ≤ 0 ↔ _
  rw [real_inner_smul_right]
  have hp : 0 < 2 * r.val / (1 + r.val ^ 2) :=
    div_pos (mul_pos (by norm_num) r.property.1) (by positivity)
  exact ⟨fun h => nonpos_of_mul_nonpos_right h hp,
    fun h => mul_nonpos_of_nonneg_of_nonpos hp.le h⟩

/-- A genuine Klein half-plane germ determines the original native radial directions exactly. -/
theorem discRadialDirections_of_klein_halfplane_germ {S : Set Complex.UnitDisc}
    (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S) (h0 : (0 : Complex.UnitDisc) ∈ S)
    (n m : ℂ) (N : Set ℂ) (hN : IsOpen N) (h0N : (0 : ℂ) ∈ N)
    (he : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S) ∩ N = {z | inner ℝ n z ≤ 0 ∧ inner ℝ m z ≤ 0} ∩ N) :
    discRadialDirections S = {u : Circle | inner ℝ n (u : ℂ) ≤ 0 ∧ inner ℝ m (u : ℂ) ≤ 0} := by
  have hkn0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0 : Complex.UnitDisc) = 0 := by
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  have hNtest (u : Circle) : ∀ᶠ j : ℕ in atTop,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (discRadialPoint (discRadialTestRadius j) u) ∈ N := by
    have ht := _root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_kleinCoordinate.continuousAt.tendsto.comp (tendsto_discRadialTestPoint u)
    exact ht.eventually (by rw [hkn0]; exact hN.mem_nhds h0N)
  ext u
  constructor
  · rintro ⟨r, hr⟩
    have ht := ((continuous_norm.comp Complex.UnitDisc.continuous_coe).continuousAt.tendsto).comp
      (tendsto_discRadialTestPoint u)
    have htr : Tendsto (fun j => (discRadialTestRadius j).val) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, discRadialPoint_norm, Complex.UnitDisc.coe_zero, norm_zero] using ht
    obtain ⟨j, hjN, hjr⟩ := ((hNtest u).and (htr.eventually (gt_mem_nhds r.property.1))).exists
    have hjs := discRadialPoint_mem_of_le hS h0 hjr.le u hr
    have hq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (discRadialPoint (discRadialTestRadius j) u) ∈
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S) ∩ N := ⟨mem_image_of_mem _ hjs, hjN⟩
    rw [he] at hq
    exact ⟨(kleinRadial_halfplane_sign _ _ _).mp hq.1.1, (kleinRadial_halfplane_sign _ _ _).mp hq.1.2⟩
  · rintro ⟨hun, hum⟩
    obtain ⟨j, hjN⟩ := (hNtest u).exists
    have hq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (discRadialPoint (discRadialTestRadius j) u) ∈
        {z | inner ℝ n z ≤ 0 ∧ inner ℝ m z ≤ 0} ∩ N :=
      ⟨⟨(kleinRadial_halfplane_sign _ _ _).mpr hun, (kleinRadial_halfplane_sign _ _ _).mpr hum⟩, hjN⟩
    rw [← he] at hq
    obtain ⟨w, hw, hew⟩ := hq.1
    refine ⟨discRadialTestRadius j, ?_⟩
    have hew' : w = discRadialPoint (discRadialTestRadius j) u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective hew
    have hm : discRadialPoint (discRadialTestRadius j) u ∈ S := hew' ▸ hw
    exact hm

/-- The actual original polygon angle at every boundary point is determined by two genuine supporting directions. -/
theorem IsConvexFuchsianPolygon.boundary_directions_two_halfplanes
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) (hx : x ∈ frontier D) :
    ∃ n m a : ℂ, n ≠ 0 ∧ m ≠ 0 ∧ inner ℝ n a < 0 ∧ inner ℝ m a < 0 ∧
      fuchsianTileDirections P D x 1 =
        {u : Circle | inner ℝ n (u : ℂ) ≤ 0 ∧ inner ℝ m (u : ℂ) ≤ 0} := by
  obtain ⟨n, m, a, N, hnn, hmn, hN, h0N, hna, hma, he⟩ := hD.local_two_halfplanes x hx
  let S := polygonPointCoordinate P x '' closure D
  have hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S := by
    have heS : S = discOriginNormalizer (P.finiteCoordinate x) '' (P.finiteCoordinate '' closure D) := by
      rw [image_image]
      rfl
    rw [heS]
    exact hD.closure_convex.isometry_image (discOriginNormalizer_isometry _)
  have h0S : (0 : Complex.UnitDisc) ∈ S :=
    ⟨x, frontier_subset_closure hx, polygonPointCoordinate_self P x⟩
  have heS : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S) ∩ N = {z | inner ℝ n z ≤ 0 ∧ inner ℝ m z ≤ 0} ∩ N := by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P x '' closure D)) ∩ N = _
    rw [image_image]
    exact he
  refine ⟨n, m, a, hnn, hmn, hna, hma, ?_⟩
  change discRadialDirections (polygonPointCoordinate P x '' (1 • closure D)) = _
  rw [one_smul]
  exact discRadialDirections_of_klein_halfplane_germ hS h0S n m N hN h0N heS

theorem negative_planar_linear_constraint (a b s t : ℝ) (ha : a < 0) :
    a * s + b * t ≤ 0 ↔ (-b / a) * t ≤ s := by
  have he : a * (s - (-b / a) * t) = a * s + b * t := by
    field_simp [ha.ne]
    ring
  rw [← he]
  constructor
  · intro hh
    by_contra hle
    exact hh.not_gt (mul_pos_of_neg_of_neg ha (by linarith))
  · intro hh
    exact mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr hh)

theorem two_slope_constraints_positive_coordinates (k l s t : ℝ) (hkl : k < l) :
    (k * t ≤ s ∧ l * t ≤ s) ↔
      ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧
        s = l * α - k * β ∧ t = α - β := by
  have hd : 0 < l - k := sub_pos.mpr hkl
  constructor
  · rintro ⟨hk, hl⟩
    refine ⟨(s-k*t)/(l-k), div_nonneg (sub_nonneg.mpr hk) hd.le,
      (s-l*t)/(l-k), div_nonneg (sub_nonneg.mpr hl) hd.le, ?_, ?_⟩
    · field_simp [hd.ne']; ring
    · field_simp [hd.ne']; ring
  · rintro ⟨α, hα, β, hβ, rfl, rfl⟩
    constructor <;> nlinarith

theorem complex_basis_direction_unique (v : ℂ) (hv : v ≠ 0) (s t a b : ℝ)
    (he : s • v + t • (Complex.I * v) = a • v + b • (Complex.I * v)) :
    s = a ∧ t = b := by
  have he' : ((s : ℂ) + (t : ℂ) * Complex.I) * v =
      ((a : ℂ) + (b : ℂ) * Complex.I) * v := by
    simpa only [Complex.real_smul, add_mul, mul_assoc] using he
  have hq := mul_right_cancel₀ hv he'
  exact ⟨by simpa using congrArg Complex.re hq, by simpa using congrArg Complex.im hq⟩

theorem two_halfplanes_are_halfplane_or_positive_cone (n m a : ℂ)
    (hna : inner ℝ n a < 0) (hma : inner ℝ m a < 0) :
    (∃ q : ℂ, q ≠ 0 ∧ {z : ℂ | inner ℝ n z ≤ 0 ∧ inner ℝ m z ≤ 0} =
      {z : ℂ | inner ℝ q z ≤ 0}) ∨
    ∃ u v : ℂ, u ≠ 0 ∧ v ≠ 0 ∧ 0 < InnerProductGeometry.angle u v ∧ InnerProductGeometry.angle u v < Real.pi ∧
      {z : ℂ | inner ℝ n z ≤ 0 ∧ inner ℝ m z ≤ 0} =
        {z | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • u + β • v} := by
  have ha : a ≠ 0 := by rintro rfl; simp at hna
  let k := -inner ℝ n (Complex.I * a) / inner ℝ n a
  let l := -inner ℝ m (Complex.I * a) / inner ℝ m a
  have hn (s t : ℝ) : inner ℝ n (s • a + t • (Complex.I * a)) ≤ 0 ↔ k*t ≤ s := by
    simpa only [k, inner_add_right, real_inner_smul_right, mul_comm] using
      negative_planar_linear_constraint (inner ℝ n a) (inner ℝ n (Complex.I*a)) s t hna
  have hm (s t : ℝ) : inner ℝ m (s • a + t • (Complex.I * a)) ≤ 0 ↔ l*t ≤ s := by
    simpa only [l, inner_add_right, real_inner_smul_right, mul_comm] using
      negative_planar_linear_constraint (inner ℝ m a) (inner ℝ m (Complex.I*a)) s t hma
  have hproper (k l : ℝ) (hkl : k < l) :
      ∃ u v : ℂ, u ≠ 0 ∧ v ≠ 0 ∧ 0 < InnerProductGeometry.angle u v ∧ InnerProductGeometry.angle u v < Real.pi ∧
        {z : ℂ | ∃ s t : ℝ, z = s • a + t • (Complex.I*a) ∧ k*t ≤ s ∧ l*t ≤ s} =
          {z | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • u + β • v} := by
    let u := l • a + Complex.I*a
    let v := (-k) • a - Complex.I*a
    have hu : u ≠ 0 := by
      intro h
      have hh := complex_basis_direction_unique a ha l 1 0 0 (by simpa [u] using h)
      norm_num at hh
    have hv : v ≠ 0 := by
      intro h
      have hh := complex_basis_direction_unique a ha (-k) (-1) 0 0 (by simpa [v, sub_eq_add_neg] using h)
      norm_num at hh
    have hpos : 0 < InnerProductGeometry.angle u v := by
      apply lt_of_le_of_ne (InnerProductGeometry.angle_nonneg _ _)
      intro he
      obtain ⟨_hu, r, hr, hvr⟩ := InnerProductGeometry.angle_eq_zero_iff.mp he.symm
      have hh := complex_basis_direction_unique a ha (-k) (-1) (r*l) r (by
        simpa only [v, u, sub_eq_add_neg, neg_smul, one_smul, smul_add, smul_smul] using hvr)
      linarith [hh.2]
    have hangle : InnerProductGeometry.angle u v < Real.pi := by
      apply lt_of_le_of_ne (InnerProductGeometry.angle_le_pi _ _)
      intro he
      obtain ⟨_hu, r, hr, hvr⟩ := InnerProductGeometry.angle_eq_pi_iff.mp he
      have hh := complex_basis_direction_unique a ha (-k) (-1) (r*l) r (by
        simpa only [v, u, sub_eq_add_neg, neg_smul, one_smul, smul_add, smul_smul] using hvr)
      have hrr : r = -1 := by linarith [hh.2]
      rw [hrr] at hh
      linarith [hh.1]
    refine ⟨u, v, hu, hv, hpos, hangle, ?_⟩
    ext z
    constructor
    · rintro ⟨s, t, rfl, hks, hls⟩
      obtain ⟨α, hα, β, hβ, hs, ht⟩ :=
        (two_slope_constraints_positive_coordinates k l s t hkl).mp ⟨hks, hls⟩
      refine ⟨α, hα, β, hβ, ?_⟩
      rw [hs, ht]
      simp only [u, v, sub_smul, smul_add, smul_sub, smul_smul]
      module
    · rintro ⟨α, hα, β, hβ, rfl⟩
      refine ⟨l*α-k*β, α-β, ?_, ?_⟩
      · simp only [u, v, sub_smul, smul_add, smul_sub, smul_smul]
        module
      · exact (two_slope_constraints_positive_coordinates k l _ _ hkl).mpr
          ⟨α, hα, β, hβ, rfl, rfl⟩
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · right
    obtain ⟨u,v,hu,hv,hθpos,hθ,he⟩ := hproper k l hkl
    refine ⟨u,v,hu,hv,hθpos,hθ, ?_⟩
    rw [← he]
    ext z
    obtain ⟨s,t,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_basis_direction_representation a z ha
    simp only [mem_ofPred_eq, hn, hm]
    constructor
    · rintro ⟨hs,ht⟩; exact ⟨s,t,rfl,hs,ht⟩
    · rintro ⟨s',t',he',hs,ht⟩
      obtain ⟨rfl,rfl⟩ := complex_basis_direction_unique a ha s t s' t' he'
      exact ⟨hs,ht⟩
  · left
    refine ⟨n, ?_, ?_⟩
    · intro h; simp [h] at hna
    · ext z
      obtain ⟨s,t,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_basis_direction_representation a z ha
      simp only [mem_ofPred_eq, hn, hm, hkl, and_self]
  · right
    obtain ⟨u,v,hu,hv,hθpos,hθ,he⟩ := hproper l k hlk
    refine ⟨u,v,hu,hv,hθpos,hθ, ?_⟩
    rw [← he]
    ext z
    obtain ⟨s,t,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_basis_direction_representation a z ha
    simp only [mem_ofPred_eq, hn, hm]
    constructor
    · rintro ⟨hs,ht⟩; exact ⟨s,t,rfl,ht,hs⟩
    · rintro ⟨s',t',he',ht,hs⟩
      obtain ⟨rfl,rfl⟩ := complex_basis_direction_unique a ha s t s' t' he'
      exact ⟨hs,ht⟩

/-- Every genuine Euclidean tangent half-plane has the usual straight angle. -/
theorem polygonDirectionMeasure_halfplane_radians (n : ℂ) (hn : n ≠ 0) :
    2 * Real.pi * (polygonDirectionMeasure {u : Circle | inner ℝ n (u : ℂ) ≤ 0}).toReal =
      Real.pi := by
  let S : Set Circle := {u | inner ℝ n (u : ℂ) ≤ 0}
  let T : Set Circle := {u | 0 ≤ inner ℝ n (u : ℂ)}
  let e : Circle ≃ₜ Circle := Homeomorph.mulLeft (-1)
  have hneg (u : Circle) : inner ℝ n ((e u : Circle) : ℂ) = -inner ℝ n (u : ℂ) := by
    change inner ℝ n ((-1 : ℂ) * (u : ℂ)) = _
    rw [neg_one_mul, inner_neg_right]
  have hT : T = e '' S := by
    ext u
    constructor
    · intro hu
      refine ⟨e u, ?_, ?_⟩
      · change inner ℝ n ((e u : Circle) : ℂ) ≤ 0
        rw [hneg]
        exact neg_nonpos.mpr hu
      · change (-1 : Circle) * ((-1) * u) = u
        simp
    · rintro ⟨v, hv, rfl⟩
      change 0 ≤ inner ℝ n ((e v : Circle) : ℂ)
      rw [hneg]
      exact neg_nonneg.mpr hv
  have hm : polygonDirectionMeasure T = polygonDirectionMeasure S := by
    rw [hT]
    exact polygonDirectionMeasure_image_homeomorph e
      (MeasureTheory.measurePreserving_mul_left _ (-1)) S
  have hU : S ∪ T = univ := by
    ext u
    simp only [S,T,mem_union,mem_ofPred_eq,mem_univ,iff_true]
    exact le_total _ _
  have hZ : polygonDirectionMeasure (S ∩ T) = 0 := by
    apply MeasureTheory.measure_mono_null (show S ∩ T ⊆ {u : Circle | inner ℝ (u : ℂ) n = 0} from ?_)
      ((finite_circle_orthogonal n hn).measure_zero _)
    intro u hu
    change inner ℝ (u : ℂ) n = 0
    rw [real_inner_comm]
    exact le_antisymm hu.1 hu.2
  have hTm : MeasurableSet T :=
    (isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)).measurableSet
  have he := MeasureTheory.measure_union_add_inter (μ := polygonDirectionMeasure) S hTm
  rw [hU, polygonDirectionMeasure_univ, hZ, add_zero, hm] at he
  have hf : polygonDirectionMeasure S ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_one, ENNReal.toReal_add hf hf] at hr
  change 2 * Real.pi * (polygonDirectionMeasure S).toReal = Real.pi
  calc
    _ = Real.pi * ((polygonDirectionMeasure S).toReal + (polygonDirectionMeasure S).toReal) := by ring
    _ = Real.pi := by rw [← hr,mul_one]

theorem fuchsianPolygonAngle_eq_tileDirections
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (x : P.domain.carrier) :
    fuchsianPolygonAngle P D x =
      2 * Real.pi * (polygonDirectionMeasure (fuchsianTileDirections P D x 1)).toReal := by
  have h := fuchsianTileDirections_measure_eq P D x 1
  simp only [inv_one, one_smul] at h
  rw [fuchsianPolygonAngle, ← h]

theorem complex_positive_cone_mem_iff (u v z : ℂ) :
    (∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • u + β • v) ↔
      z ∈ Submodule.span ℝ≥0 {u,v} := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨α,hα,β,hβ,he⟩
    exact ⟨⟨α,hα⟩,⟨β,hβ⟩,he.symm⟩
  · rintro ⟨α,β,he⟩
    exact ⟨α,α.property,β,β.property,he.symm⟩

/-- Every original boundary angle is the genuine geometric angle of its actual local half-plane or proper two-ray cone. -/
theorem IsConvexFuchsianPolygon.boundary_geometric_angle
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) (hx : x ∈ frontier D) :
    (∃ (q : ℂ) (N : Set ℂ), q ≠ 0 ∧ IsOpen N ∧ (0 : ℂ) ∈ N ∧
      ((normalizedPolygonKleinCoordinate P x '' closure D) ∩ N =
        {z | inner ℝ q z ≤ 0} ∩ N) ∧ fuchsianPolygonAngle P D x = Real.pi) ∨
    ∃ (u v : ℂ) (N : Set ℂ), u ≠ 0 ∧ v ≠ 0 ∧
      0 < InnerProductGeometry.angle u v ∧ InnerProductGeometry.angle u v < Real.pi ∧
      IsOpen N ∧ (0 : ℂ) ∈ N ∧
      ((normalizedPolygonKleinCoordinate P x '' closure D) ∩ N =
        {z | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • u + β • v} ∩ N) ∧
      fuchsianPolygonAngle P D x = InnerProductGeometry.angle u v := by
  obtain ⟨n,m,a,N,hn,hm,hN,h0N,hna,hma,he⟩ := hD.local_two_halfplanes x hx
  let S := polygonPointCoordinate P x '' closure D
  have hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S := by
    have heS : S = discOriginNormalizer (P.finiteCoordinate x) '' (P.finiteCoordinate '' closure D) := by
      rw [image_image]; rfl
    rw [heS]
    exact hD.closure_convex.isometry_image (discOriginNormalizer_isometry _)
  have h0S : (0 : Complex.UnitDisc) ∈ S :=
    ⟨x,frontier_subset_closure hx,polygonPointCoordinate_self P x⟩
  have heS : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S) ∩ N = {z | inner ℝ n z ≤ 0 ∧ inner ℝ m z ≤ 0} ∩ N := by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P x '' closure D)) ∩ N = _
    rw [image_image]
    exact he
  have hdirs : fuchsianTileDirections P D x 1 =
      {u : Circle | inner ℝ n (u : ℂ) ≤ 0 ∧ inner ℝ m (u : ℂ) ≤ 0} := by
    change discRadialDirections (polygonPointCoordinate P x '' (1 • closure D)) = _
    rw [one_smul]
    exact discRadialDirections_of_klein_halfplane_germ hS h0S n m N hN h0N heS
  rcases two_halfplanes_are_halfplane_or_positive_cone n m a hna hma with
    ⟨q,hq,heq⟩ | ⟨u,v,hu,hv,hθpos,hθ,heq⟩
  · left
    refine ⟨q,N,hq,hN,h0N, ?_, ?_⟩
    · rw [heq] at he
      exact he
    · rw [fuchsianPolygonAngle_eq_tileDirections, hdirs]
      have hpre := congrArg (fun T : Set ℂ => (fun u : Circle => (u : ℂ)) ⁻¹' T) heq
      change {u : Circle | inner ℝ n (u : ℂ) ≤ 0 ∧ inner ℝ m (u : ℂ) ≤ 0} =
        {u : Circle | inner ℝ q (u : ℂ) ≤ 0} at hpre
      rw [hpre]
      exact polygonDirectionMeasure_halfplane_radians q hq
  · right
    refine ⟨u,v,N,hu,hv,hθpos,hθ,hN,h0N, ?_, ?_⟩
    · rw [heq] at he
      exact he
    · have hpre := congrArg (fun T : Set ℂ => (fun w : Circle => (w : ℂ)) ⁻¹' T) heq
      change {w : Circle | inner ℝ n (w : ℂ) ≤ 0 ∧ inner ℝ m (w : ℂ) ≤ 0} =
        {w : Circle | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ (w : ℂ) = α • u + β • v} at hpre
      have hdir : fuchsianTileDirections P D x 1 = discRadialDirections (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPositiveCone u v) := by
        rw [hdirs,hpre]
        change {w : Circle | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ (w : ℂ) = α • u + β • v} =
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPositiveCone u v)
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_positiveCone]
        ext w
        exact complex_positive_cone_mem_iff u v (w : ℂ)
      rw [fuchsianPolygonAngle_eq_tileDirections, hdir]
      have hg := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_positiveCone hu hv hθ
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction_zero] at hg
      exact hg

/-- The actual two tangent directions give exactly the previously formalized forward-tangent ray angle. -/
theorem complex_angle_eq_HRay_angle (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ R S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt UpperHalfPlane.I,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (discRadialPoint (discRadialTestRadius 0) (Circle.exp (Complex.arg u))) ∈ R.val ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (discRadialPoint (discRadialTestRadius 0) (Circle.exp (Complex.arg v))) ∈ S.val ∧
      InnerProductGeometry.angle u v = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S := by
  let U := Circle.exp (Complex.arg u)
  let V := Circle.exp (Complex.arg v)
  let w := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (discRadialPoint (discRadialTestRadius 0) U)
  let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (discRadialPoint (discRadialTestRadius 0) V)
  have hw : w ≠ UpperHalfPlane.I := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_radialPoint_ne_I _ _
  have hz : z ≠ UpperHalfPlane.I := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_radialPoint_ne_I _ _
  obtain ⟨R,hR,_⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_hRayAt_through UpperHalfPlane.I w hw.symm
  obtain ⟨S,hS,_⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_hRayAt_through UpperHalfPlane.I z hz.symm
  refine ⟨R,S,hR,hS, ?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_I_cayley R S hR hw hS hz,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  have hU : ‖u‖ • (U : ℂ) = u := by
    simpa only [U,Complex.real_smul,Circle.coe_exp] using Complex.norm_mul_exp_arg_mul_I u
  have hV : ‖v‖ • (V : ℂ) = v := by
    simpa only [V,Complex.real_smul,Circle.coe_exp] using Complex.norm_mul_exp_arg_mul_I v
  change InnerProductGeometry.angle u v =
    InnerProductGeometry.angle ((discRadialTestRadius 0).val • (U : ℂ))
      ((discRadialTestRadius 0).val • (V : ℂ))
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (discRadialTestRadius 0).property.1,
    InnerProductGeometry.angle_smul_right_of_pos _ _ (discRadialTestRadius 0).property.1,
    ← hU, ← hV,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (norm_pos_iff.mpr hu),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (norm_pos_iff.mpr hv)]

theorem mem_frontier_of_supporting_halfplane {C : Set ℂ} {n z : ℂ} (hn : n ≠ 0)
    (hC : C ⊆ {w | inner ℝ n w ≤ 0}) (hz : z ∈ C) (hnz : inner ℝ n z = 0) :
    z ∈ frontier C := by
  refine ⟨subset_closure hz, ?_⟩
  intro hi
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hi)
  let t := r / (2 * ‖n‖)
  have ht : 0 < t := div_pos hr (mul_pos (by norm_num) (norm_pos_iff.mpr hn))
  have hm : t * ‖n‖ = r / 2 := by dsimp [t]; field_simp
  have hd : dist (z + t • n) z < r := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht,hm]
    linarith
  have hh := hC (interior_subset (hball hd))
  change inner ℝ n (z + t • n) ≤ 0 at hh
  rw [inner_add_right,real_inner_smul_right,hnz,zero_add,real_inner_self_eq_norm_sq] at hh
  exact hh.not_gt (mul_pos ht (sq_pos_of_pos (norm_pos_iff.mpr hn)))

theorem positive_cone_boundary_ray (u v : ℂ) (hu : u ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    t • u ∈ frontier {z : ℂ | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • u + β • v} := by
  let n := Complex.I * u
  have hn : n ≠ 0 := mul_ne_zero Complex.I_ne_zero hu
  have hnu : inner ℝ n u = 0 := by
    simp [n,Complex.inner]
    ring
  let q := if inner ℝ n v ≤ 0 then n else -n
  have hq : q ≠ 0 := by dsimp only [q]; split_ifs <;> simpa using hn
  have hqu : inner ℝ q u = 0 := by
    dsimp only [q]; split_ifs <;> simp only [hnu,inner_neg_left,neg_zero]
  have hqv : inner ℝ q v ≤ 0 := by
    dsimp only [q]; split_ifs with hh
    · exact hh
    · rw [inner_neg_left]; linarith
  apply mem_frontier_of_supporting_halfplane hq
  · rintro z ⟨α,hα,β,hβ,rfl⟩
    simp only [mem_ofPred_eq,inner_add_right,real_inner_smul_right,hqu,mul_zero,zero_add]
    exact mul_nonpos_of_nonneg_of_nonpos hβ hqv
  · exact ⟨t,ht,0,le_rfl,by simp⟩
  · rw [real_inner_smul_right,hqu,mul_zero]

theorem frontiers_equal_on_open_germ {A B N : Set ℂ} (hN : IsOpen N)
    (he : A ∩ N = B ∩ N) : frontier A ∩ N = frontier B ∩ N := by
  rw [← frontier_inter_open_inter hN,he,frontier_inter_open_inter hN]

/-- Actual boundary half-rays of the original polygon's genuine local cone carry the pre-existing HRay angle. -/
theorem IsConvexFuchsianPolygon.boundary_geometric_angle_with_rays
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) (hx : x ∈ frontier D) :
    fuchsianPolygonAngle P D x = Real.pi ∨
    ∃ (u v : ℂ) (N : Set ℂ) (R S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt UpperHalfPlane.I), u ≠ 0 ∧ v ≠ 0 ∧
      0 < InnerProductGeometry.angle u v ∧ InnerProductGeometry.angle u v < Real.pi ∧
      IsOpen N ∧ (0 : ℂ) ∈ N ∧
      ((normalizedPolygonKleinCoordinate P x '' closure D) ∩ N =
        {z | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • u + β • v} ∩ N) ∧
      (∀ t : ℝ, 0 ≤ t → t • u ∈ N →
        t • u ∈ frontier (normalizedPolygonKleinCoordinate P x '' closure D)) ∧
      (∀ t : ℝ, 0 ≤ t → t • v ∈ N →
        t • v ∈ frontier (normalizedPolygonKleinCoordinate P x '' closure D)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (discRadialPoint (discRadialTestRadius 0) (Circle.exp (Complex.arg u))) ∈ R.val ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (discRadialPoint (discRadialTestRadius 0) (Circle.exp (Complex.arg v))) ∈ S.val ∧
      fuchsianPolygonAngle P D x = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S := by
  rcases hD.boundary_geometric_angle x hx with ⟨q,N,hq,hN,h0N,he,hangle⟩ |
    ⟨u,v,N,hu,hv,hθpos,hθ,hN,h0N,he,hangle⟩
  · exact Or.inl hangle
  · obtain ⟨R,S,hR,hS,hRS⟩ := complex_angle_eq_HRay_angle u v hu hv
    right
    refine ⟨u,v,N,R,S,hu,hv,hθpos,hθ,hN,h0N,he, ?_, ?_, hR,hS,hangle.trans hRS⟩
    · intro t ht htN
      have hg := frontiers_equal_on_open_germ hN he
      exact (hg.symm ▸ (show t • u ∈ frontier
        {z : ℂ | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • u + β • v} ∩ N from
          ⟨positive_cone_boundary_ray u v hu t ht,htN⟩)).1
    · intro t ht htN
      have hg := frontiers_equal_on_open_germ hN he
      have hr := positive_cone_boundary_ray v u hv t ht
      have hec : {z : ℂ | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • v + β • u} =
          {z : ℂ | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • u + β • v} := by
        ext z
        constructor <;> rintro ⟨α,hα,β,hβ,rfl⟩ <;> exact ⟨β,hβ,α,hα,add_comm _ _⟩
      rw [hec] at hr
      exact (hg.symm ▸ (show t • v ∈ frontier
        {z : ℂ | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • u + β • v} ∩ N from ⟨hr,htN⟩)).1

theorem IsConvexFuchsianPolygon.nonvertex_incident_unique
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {x : P.domain.carrier} (hx : x ∈ frontier D) (hnv : ¬ IsFuchsianPolygonVertex P D x) :
    ∃! g : H, g ≠ 1 ∧ x ∈ fuchsianDomainTile P D g := by
  obtain ⟨g,hg,hgx⟩ := hD.boundary_mate hx
  have hj : g⁻¹ ≠ 1 := inv_ne_one.mpr hg
  have hxj : x ∈ fuchsianDomainTile P D g⁻¹ :=
    ⟨g • x,frontier_subset_closure hgx,inv_smul_smul g x⟩
  refine ⟨g⁻¹,⟨hj,hxj⟩, ?_⟩
  rintro h ⟨hh,hxh⟩
  by_contra hne
  exact hnv ⟨g⁻¹,h,hj,hh,Ne.symm hne,
    (hD.closed_tile_triple_subsingleton hj hh (Ne.symm hne)).eq_singleton_of_mem
      ⟨⟨frontier_subset_closure hx,hxj⟩,hxh⟩⟩

/-- Every actual side point which is not a polygon vertex has the ordinary straight angleπ. -/
theorem IsConvexFuchsianPolygon.nonvertex_angle_eq_pi
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {x : P.domain.carrier} (hx : x ∈ frontier D) (hnv : ¬ IsFuchsianPolygonVertex P D x) :
    fuchsianPolygonAngle P D x = Real.pi := by
  classical
  obtain ⟨g,⟨hg,hxg⟩,hgUnique⟩ := hD.nonvertex_incident_unique hx hnv
  obtain ⟨s,n,N,hN,h0N,hn,hnstrict,he,hincident⟩ := hD.local_finite_cone x (frontier_subset_closure hx)
  let i₀ : {g // g ∈ s ∧ g ≠ 1} := ⟨g,(hincident g).mpr hxg,hg⟩
  have hi (i : {g // g ∈ s ∧ g ≠ 1}) : i = i₀ := by
    apply Subtype.ext
    exact hgUnique i.val ⟨i.property.2,(hincident i.val).mp i.property.1⟩
  have hQ : {z : ℂ | ∀ i, inner ℝ (n i) z ≤ 0} = {z | inner ℝ (n i₀) z ≤ 0 ∧ inner ℝ (n i₀) z ≤ 0} := by
    ext z
    constructor
    · intro hz; exact ⟨hz i₀,hz i₀⟩
    · intro hz i
      rw [hi i]
      exact hz.1
  rw [hQ] at he
  let S := polygonPointCoordinate P x '' closure D
  have hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S := by
    have heS : S = discOriginNormalizer (P.finiteCoordinate x) '' (P.finiteCoordinate '' closure D) := by
      rw [image_image]; rfl
    rw [heS]
    exact hD.closure_convex.isometry_image (discOriginNormalizer_isometry _)
  have h0S : (0 : Complex.UnitDisc) ∈ S :=
    ⟨x,frontier_subset_closure hx,polygonPointCoordinate_self P x⟩
  have heS : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S) ∩ N =
      {z | inner ℝ (n i₀) z ≤ 0 ∧ inner ℝ (n i₀) z ≤ 0} ∩ N := by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P x '' closure D)) ∩ N = _
    rw [image_image]
    exact he
  have hdirs : fuchsianTileDirections P D x 1 =
      {u : Circle | inner ℝ (n i₀) (u : ℂ) ≤ 0} := by
    change discRadialDirections (polygonPointCoordinate P x '' (1 • closure D)) = _
    rw [one_smul]
    simpa only [and_self] using
      discRadialDirections_of_klein_halfplane_germ hS h0S (n i₀) (n i₀) N hN h0N heS
  rw [fuchsianPolygonAngle_eq_tileDirections,hdirs]
  exact polygonDirectionMeasure_halfplane_radians (n i₀) (hn i₀)

end LowDimensionalTopology.Geometry.Fuchsian
