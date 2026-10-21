/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.FiniteIdealTriangleAdapters

/-!
# Actual finite corners of finite/ideal triangles
-/

@[expose] public section
open Set Filter Module
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem ClosedDiscTriangle.b_mem_sideLineA (T : ClosedDiscTriangle) : T.b ∈ T.sideLineA.closedCarrier :=
  (existsUnique_discLine_closedCarrier T.b T.c T.b_ne_c).exists.choose_spec.1

theorem ClosedDiscTriangle.c_mem_sideLineA (T : ClosedDiscTriangle) : T.c ∈ T.sideLineA.closedCarrier :=
  (existsUnique_discLine_closedCarrier T.b T.c T.b_ne_c).exists.choose_spec.2

theorem ClosedDiscTriangle.a_not_mem_sideLineA (T : ClosedDiscTriangle) : T.a ∉ T.sideLineA.closedCarrier :=
  fun ha => T.noncollinear ⟨T.sideLineA,ha,T.b_mem_sideLineA,T.c_mem_sideLineA⟩

theorem ClosedDiscTriangle.a_mem_sideLineC (T : ClosedDiscTriangle) : T.a ∈ T.sideLineC.closedCarrier :=
  (existsUnique_discLine_closedCarrier T.a T.b T.a_ne_b).exists.choose_spec.1

theorem ClosedDiscTriangle.b_mem_sideLineC (T : ClosedDiscTriangle) : T.b ∈ T.sideLineC.closedCarrier :=
  (existsUnique_discLine_closedCarrier T.a T.b T.a_ne_b).exists.choose_spec.2

theorem ClosedDiscTriangle.c_not_mem_sideLineC (T : ClosedDiscTriangle) : T.c ∉ T.sideLineC.closedCarrier :=
  fun hc => T.noncollinear ⟨T.sideLineC,T.a_mem_sideLineC,T.b_mem_sideLineC,hc⟩

theorem ClosedDiscTriangle.klein_reconstruction (T : ClosedDiscTriangle) (x : 𝕔𝔻) :
    closedKleinCoordinate x = closedKleinCoordinate T.a +
      (T.coordinate x).1 • (closedKleinCoordinate T.b - closedKleinCoordinate T.a) +
      (T.coordinate x).2 • (closedKleinCoordinate T.c - closedKleinCoordinate T.a) := by
  have he := T.kleinBasis.sum_repr (closedKleinCoordinate x - closedKleinCoordinate T.a)
  rw [Fin.sum_univ_two,T.kleinBasis_zero,T.kleinBasis_one] at he
  change (T.coordinate x).1 • (closedKleinCoordinate T.b - closedKleinCoordinate T.a) +
    (T.coordinate x).2 • (closedKleinCoordinate T.c - closedKleinCoordinate T.a) =
      closedKleinCoordinate x - closedKleinCoordinate T.a at he
  calc
    _ = (T.coordinate x).1 • (closedKleinCoordinate T.b - closedKleinCoordinate T.a) +
      (T.coordinate x).2 • (closedKleinCoordinate T.c - closedKleinCoordinate T.a) +
        closedKleinCoordinate T.a := sub_eq_iff_eq_add.mp he.symm
    _ = _ := by abel


theorem ClosedDiscTriangle.inner_klein_reconstruction (T : ClosedDiscTriangle) (n : ℂ) (x : 𝕔𝔻) :
    inner ℝ n (closedKleinCoordinate x) = inner ℝ n (closedKleinCoordinate T.a) +
      (T.coordinate x).1 * (inner ℝ n (closedKleinCoordinate T.b) - inner ℝ n (closedKleinCoordinate T.a)) +
      (T.coordinate x).2 * (inner ℝ n (closedKleinCoordinate T.c) - inner ℝ n (closedKleinCoordinate T.a)) := by
  conv_lhs => rw [T.klein_reconstruction x]
  simp only [inner_add_right,inner_smul_right,inner_sub_right]

theorem ClosedDiscTriangle.sideLineC_iff_coordinate (T : ClosedDiscTriangle) (x : 𝕔𝔻) :
    x ∈ T.sideLineC.closedCarrier ↔ (T.coordinate x).2 = 0 := by
  obtain ⟨n,t,_,hL⟩ := T.sideLineC.closedKlein_affine_equation
  have ha := (hL T.a).mp T.a_mem_sideLineC
  have hb := (hL T.b).mp T.b_mem_sideLineC
  have hc : inner ℝ n (closedKleinCoordinate T.c) ≠ t :=
    fun he => T.c_not_mem_sideLineC ((hL T.c).mpr he)
  have he := T.inner_klein_reconstruction n x
  rw [ha,hb] at he
  rw [hL x]
  constructor
  · intro hx
    have hm : (T.coordinate x).2 * (inner ℝ n (closedKleinCoordinate T.c) - t) = 0 := by nlinarith
    exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hc)
  · intro hx
    rw [hx] at he
    nlinarith

theorem ClosedDiscTriangle.sideLineB_iff_coordinate (T : ClosedDiscTriangle) (x : 𝕔𝔻) :
    x ∈ T.sideLineB.closedCarrier ↔ (T.coordinate x).1 = 0 := by
  obtain ⟨n,t,_,hL⟩ := T.sideLineB.closedKlein_affine_equation
  have ha := (hL T.a).mp T.a_mem_sideLineB
  have hc := (hL T.c).mp T.c_mem_sideLineB
  have hb : inner ℝ n (closedKleinCoordinate T.b) ≠ t :=
    fun he => T.b_not_mem_sideLineB ((hL T.b).mpr he)
  have he := T.inner_klein_reconstruction n x
  rw [ha,hc] at he
  rw [hL x]
  constructor
  · intro hx
    have hm : (T.coordinate x).1 * (inner ℝ n (closedKleinCoordinate T.b) - t) = 0 := by nlinarith
    exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hb)
  · intro hx
    rw [hx] at he
    nlinarith

theorem ClosedDiscTriangle.sideLineA_iff_coordinate (T : ClosedDiscTriangle) (x : 𝕔𝔻) :
    x ∈ T.sideLineA.closedCarrier ↔ (T.coordinate x).1 + (T.coordinate x).2 = 1 := by
  obtain ⟨n,t,_,hL⟩ := T.sideLineA.closedKlein_affine_equation
  have hb := (hL T.b).mp T.b_mem_sideLineA
  have hc := (hL T.c).mp T.c_mem_sideLineA
  have ha : inner ℝ n (closedKleinCoordinate T.a) ≠ t :=
    fun he => T.a_not_mem_sideLineA ((hL T.a).mpr he)
  have he := T.inner_klein_reconstruction n x
  rw [hb,hc] at he
  rw [hL x]
  constructor
  · intro hx
    have hm : ((T.coordinate x).1 + (T.coordinate x).2 - 1) *
        (t - inner ℝ n (closedKleinCoordinate T.a)) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr ha.symm))
  · intro hx
    have hm : (T.coordinate x).1 * (t - inner ℝ n (closedKleinCoordinate T.a)) +
        (T.coordinate x).2 * (t - inner ℝ n (closedKleinCoordinate T.a)) =
          t - inner ℝ n (closedKleinCoordinate T.a) := by
      rw [← add_mul,hx,one_mul]
    linarith




theorem HRayAt.image_punctured_firstAxis_of_positive_point {z : ℍ} (R : HRayAt z) (F : ℍ → ℝ × ℝ)
    (hF : Topology.IsEmbedding F) (hconv : Convex ℝ (range F)) (hz : F z = 0)
    (haxis : ∀ x, (F x).2 = 0 ↔ x ∈ R.supportLine.carrier)
    {u : ℍ} (hu : u ∈ R.val \ {z}) (hpositive : 0 < (F u).1) :
    F '' (R.val \ {z}) = range F ∩ {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = 0} := by
  let φ : ℍ → ℝ := fun x => (F x).1
  have hφc : Continuous φ := continuous_fst.comp hF.continuous
  have hφne (x : ℍ) (hx : x ∈ R.val \ {z}) : φ x ≠ 0 := by
    intro he
    have hx2 := (haxis x).mpr (R.subset_support hx.1)
    have hx0 : F x = 0 := Prod.ext he hx2
    exact hx.2 (hF.injective (hx0.trans hz.symm))
  have hpos (x : ℍ) (hx : x ∈ R.val \ {z}) : 0 < φ x := by
    by_contra! hle
    have hlt : φ x < 0 := lt_of_le_of_ne hle (hφne x hx)
    have hpre := (R.punctured_isPreconnected.image φ hφc.continuousOn).ordConnected
    have htI : φ u ∈ φ '' (R.val \ {z}) := mem_image_of_mem φ hu
    obtain ⟨u,hu,he⟩ := hpre.out (mem_image_of_mem φ hx) htI
      (show (0 : ℝ) ∈ Icc (φ x) (φ u) from ⟨hlt.le,hpositive.le⟩)
    exact hφne u hu he
  let T : Set ℍ := F ⁻¹' {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = 0}
  have him : F '' T = range F ∩ {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = 0} := by
    rw [image_preimage_eq_inter_range,inter_comm]
  have hTc : IsPreconnected T := by
    apply hF.isInducing.isPreconnected_image.mp
    rw [him]
    exact (hconv.inter ((convex_halfSpace_gt (LinearMap.fst ℝ ℝ ℝ).isLinear (0 : ℝ)).inter
      (convex_hyperplane (LinearMap.snd ℝ ℝ ℝ).isLinear (0 : ℝ)))).isPreconnected
  have hTsub : T ⊆ R.supportLine.carrier \ {z} := by
    intro x hx
    refine ⟨(haxis x).mp hx.2,?_⟩
    intro hxz
    have he : (F x).1 = 0 := by rw [hxz,hz]; rfl
    exact (ne_of_gt hx.1) he
  have htipT : u ∈ T := ⟨hpositive,(haxis u).mpr (R.subset_support hu.1)⟩
  have hTcomp := hTc.subset_connectedComponentIn htipT hTsub
  rw [← R.punctured_eq_component hu] at hTcomp
  apply subset_antisymm
  · rintro p ⟨x,hx,rfl⟩
    exact ⟨mem_range_self x,hpos x hx,(haxis x).mpr (R.subset_support hx.1)⟩
  · intro p hp
    rw [← him] at hp
    exact image_mono hTcomp hp



def ClosedDiscTriangle.halfPlaneCoordinate (T : ClosedDiscTriangle) (x : ℍ) : ℝ × ℝ :=
  T.discCoordinate (halfPlaneToDisc x)

def ClosedDiscTriangle.openCoordinateDomain (T : ClosedDiscTriangle) : Set (ℝ × ℝ) :=
  T.coordinateHomeomorph '' Metric.ball (0 : ℂ) 1

theorem ClosedDiscTriangle.halfPlaneCoordinate_isOpenEmbedding (T : ClosedDiscTriangle) :
    Topology.IsOpenEmbedding T.halfPlaneCoordinate := by
  change Topology.IsOpenEmbedding (T.coordinateHomeomorph ∘ halfPlaneKleinCoordinate)
  exact T.coordinateHomeomorph.isOpenEmbedding.comp isOpenEmbedding_halfPlaneKleinCoordinate

theorem ClosedDiscTriangle.halfPlaneCoordinate_range (T : ClosedDiscTriangle) :
    range T.halfPlaneCoordinate = T.openCoordinateDomain := by
  change range (T.coordinateHomeomorph ∘ halfPlaneKleinCoordinate) = _
  rw [range_comp,range_halfPlaneKleinCoordinate]
  rfl

theorem ClosedDiscTriangle.openCoordinateDomain_isOpen (T : ClosedDiscTriangle) : IsOpen T.openCoordinateDomain :=
  T.coordinateHomeomorph.isOpenMap _ Metric.isOpen_ball

theorem ClosedDiscTriangle.openCoordinateDomain_convex (T : ClosedDiscTriangle) : Convex ℝ T.openCoordinateDomain := by
  have he : T.openCoordinateDomain = T.coordinateLinear ''
      ((fun x : ℂ => -closedKleinCoordinate T.a + x) '' Metric.ball (0 : ℂ) 1) := by
    rw [image_image]
    apply image_congr
    intro x _
    change T.coordinateLinear (x - closedKleinCoordinate T.a) =
      T.coordinateLinear (-closedKleinCoordinate T.a + x)
    congr 1
    abel
  rw [he]
  exact ((convex_ball (0 : ℂ) 1).translate (-closedKleinCoordinate T.a)).linear_image T.coordinateLinear.toLinearMap

theorem ClosedDiscTriangle.halfPlaneCoordinate_first_line (T : ClosedDiscTriangle) (x : ℍ) :
    (T.halfPlaneCoordinate x).2 = 0 ↔ x ∈ T.sideLineC.toHalfPlane.carrier := by
  change (T.coordinate (discToClosedModel (halfPlaneToDisc x))).2 = 0 ↔ _
  rw [← T.sideLineC_iff_coordinate, T.sideLineC.closedCarrier_mem_interior_iff,
    T.sideLineC.mem_carrier,discToHalfPlane_halfPlaneToDisc]

theorem ClosedDiscTriangle.halfPlaneCoordinate_second_line (T : ClosedDiscTriangle) (x : ℍ) :
    (T.halfPlaneCoordinate x).1 = 0 ↔ x ∈ T.sideLineB.toHalfPlane.carrier := by
  change (T.coordinate (discToClosedModel (halfPlaneToDisc x))).1 = 0 ↔ _
  rw [← T.sideLineB_iff_coordinate,T.sideLineB.closedCarrier_mem_interior_iff,
    T.sideLineB.mem_carrier,discToHalfPlane_halfPlaneToDisc]

theorem ClosedDiscTriangle.halfPlaneCoordinate_opposite_line (T : ClosedDiscTriangle) (x : ℍ) :
    (T.halfPlaneCoordinate x).1 + (T.halfPlaneCoordinate x).2 = 1 ↔
      x ∈ T.sideLineA.toHalfPlane.carrier := by
  change (T.coordinate (discToClosedModel (halfPlaneToDisc x))).1 +
    (T.coordinate (discToClosedModel (halfPlaneToDisc x))).2 = 1 ↔ _
  rw [← T.sideLineA_iff_coordinate,T.sideLineA.closedCarrier_mem_interior_iff,
    T.sideLineA.mem_carrier,discToHalfPlane_halfPlaneToDisc]


theorem HRayAt.image_punctured_secondAxis_of_positive_point {z : ℍ} (R : HRayAt z)
    (F : ℍ → ℝ × ℝ) (hF : Topology.IsEmbedding F) (hconv : Convex ℝ (range F))
    (hz : F z = 0) (haxis : ∀ x, (F x).1 = 0 ↔ x ∈ R.supportLine.carrier)
    {u : ℍ} (hu : u ∈ R.val \ {z}) (hpositive : 0 < (F u).2) :
    F '' (R.val \ {z}) = range F ∩ {p : ℝ × ℝ | p.1 = 0 ∧ 0 < p.2} := by
  let G := Prod.swap ∘ F
  have hG : Topology.IsEmbedding G := (Homeomorph.prodComm ℝ ℝ).isEmbedding.comp hF
  have hrG : range G = Prod.swap '' range F := range_comp Prod.swap F
  have hcG : Convex ℝ (range G) := by
    rw [hrG]
    exact hconv.linear_image (LinearEquiv.prodComm ℝ ℝ ℝ).toLinearMap
  have hzG : G z = 0 := by change Prod.swap (F z) = 0; rw [hz]; rfl
  have hi := R.image_punctured_firstAxis_of_positive_point G hG hcG hzG haxis hu hpositive
  apply Prod.swap_injective.image_injective
  rw [image_image]
  change G '' (R.val \ {z}) = _
  rw [hi,hrG,image_inter Prod.swap_injective]
  have he : Prod.swap '' {p : ℝ × ℝ | p.1 = 0 ∧ 0 < p.2} =
      {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = 0} := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ⟨hq.2,hq.1⟩
    · intro hp
      exact ⟨p.swap,⟨hp.2,hp.1⟩,Prod.swap_swap p⟩
  rw [he]

theorem exists_hRayAt_positive_firstAxis (F : ℍ → ℝ × ℝ) (hF : Topology.IsOpenEmbedding F)
    (hc : Convex ℝ (range F)) {z : ℍ} (hz : F z = 0) (L : HalfPlaneLine)
    (haxis : ∀ x, (F x).2 = 0 ↔ x ∈ L.carrier) :
    ∃ (t : ℝ) (u : ℍ) (R : HRayAt z), 0 < t ∧ t < 1 ∧ F u = (t,0) ∧
      u ∈ R.val \ {z} ∧ R.supportLine = L ∧
      F '' (R.val \ {z}) = range F ∩ {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = 0} := by
  have h0 : (0 : ℝ × ℝ) ∈ range F := hz ▸ mem_range_self z
  have he : ∀ᶠ t : ℝ in 𝓝 0, (t,0) ∈ range F :=
    (continuous_id.prodMk continuous_const).tendsto 0 (hF.isOpen_range.mem_nhds h0)
  have he' := (he.and (isOpen_Iio.mem_nhds (show (0 : ℝ) < 1 by norm_num))).filter_mono
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  obtain ⟨t,⟨htD,ht1⟩,ht0⟩ := (he'.and self_mem_nhdsWithin).exists
  obtain ⟨u,hu⟩ := htD
  have hzu : z ≠ u := by
    intro heq
    rw [← heq,hz] at hu
    have hh := congrArg Prod.fst hu
    change (0 : ℝ) = t at hh
    linarith
  let R := hRayThrough z u hzu
  have huR : u ∈ R.val \ {z} := ⟨hRayThrough_mem _ _ _,hzu.symm⟩
  have hL : R.supportLine = L := R.supportLine.eq_of_two_points L hzu
    R.start_mem_support (R.subset_support huR.1)
    ((haxis z).mp (by rw [hz]; rfl)) ((haxis u).mp (by rw [hu]))
  refine ⟨t,u,R,ht0,ht1,hu,huR,hL,?_⟩
  exact R.image_punctured_firstAxis_of_positive_point F hF.isEmbedding hc hz
    (fun x => by rw [hL]; exact haxis x) huR (by rw [hu]; exact ht0)

theorem exists_hRayAt_positive_secondAxis (F : ℍ → ℝ × ℝ) (hF : Topology.IsOpenEmbedding F)
    (hc : Convex ℝ (range F)) {z : ℍ} (hz : F z = 0) (L : HalfPlaneLine)
    (haxis : ∀ x, (F x).1 = 0 ↔ x ∈ L.carrier) :
    ∃ (t : ℝ) (u : ℍ) (R : HRayAt z), 0 < t ∧ t < 1 ∧ F u = (0,t) ∧
      u ∈ R.val \ {z} ∧ R.supportLine = L ∧
      F '' (R.val \ {z}) = range F ∩ {p : ℝ × ℝ | p.1 = 0 ∧ 0 < p.2} := by
  let G := Prod.swap ∘ F
  have hG : Topology.IsOpenEmbedding G := (Homeomorph.prodComm ℝ ℝ).isOpenEmbedding.comp hF
  have hcG : Convex ℝ (range G) := by
    rw [show range G = Prod.swap '' range F from range_comp Prod.swap F]
    exact hc.linear_image (LinearEquiv.prodComm ℝ ℝ ℝ).toLinearMap
  have hzG : G z = 0 := by change Prod.swap (F z) = 0; rw [hz]; rfl
  obtain ⟨t,u,R,ht0,ht1,hu,huR,hL,_⟩ := exists_hRayAt_positive_firstAxis G hG hcG hzG L haxis
  have huF : F u = (0,t) := by
    apply Prod.swap_injective
    exact hu
  refine ⟨t,u,R,ht0,ht1,huF,huR,hL,?_⟩
  exact R.image_punctured_secondAxis_of_positive_point F hF.isEmbedding hc hz
    (fun x => by rw [hL]; exact haxis x) huR (by rw [huF]; exact ht0)


theorem ClosedDiscTriangle.halfPlaneCoordinate_at_a (T : ClosedDiscTriangle) {z : ℍ}
    (ha : T.a = discToClosedModel (halfPlaneToDisc z)) : T.halfPlaneCoordinate z = 0 := by
  change T.coordinate (discToClosedModel (halfPlaneToDisc z)) = 0
  rw [← ha,T.coordinate_a]
  rfl

theorem ClosedDiscTriangle.sideLineC_ne_sideLineB (T : ClosedDiscTriangle) :
    T.sideLineC ≠ T.sideLineB := by
  intro he
  exact T.b_not_mem_sideLineB (he ▸ T.b_mem_sideLineC)

theorem ClosedDiscTriangle.sideLineC_toHalfPlane_ne_sideLineB (T : ClosedDiscTriangle) :
    T.sideLineC.toHalfPlane ≠ T.sideLineB.toHalfPlane := by
  intro he
  apply T.sideLineC_ne_sideLineB
  have hh := congrArg HalfPlaneLine.toDiscLine he
  simpa only [DiscLine.toHalfPlane_spec] using hh

/-- Genuine forward rays along the two actual sides at a finite vertex. The two other
vertices are arbitrary points of the actual closed disc, and may be ideal. -/
structure ClosedDiscTriangle.FiniteCorner (T : ClosedDiscTriangle) (z : ℍ) where
  rayAB : HRayAt z
  rayAC : HRayAt z
  supportAB : rayAB.supportLine = T.sideLineC.toHalfPlane
  supportAC : rayAC.supportLine = T.sideLineB.toHalfPlane
  imageAB : T.halfPlaneCoordinate '' (rayAB.val \ {z}) =
    range T.halfPlaneCoordinate ∩ {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = 0}
  imageAC : T.halfPlaneCoordinate '' (rayAC.val \ {z}) =
    range T.halfPlaneCoordinate ∩ {p : ℝ × ℝ | p.1 = 0 ∧ 0 < p.2}

theorem ClosedDiscTriangle.finiteCorner_nonempty (T : ClosedDiscTriangle) (z : ℍ)
    (ha : T.a = discToClosedModel (halfPlaneToDisc z)) : Nonempty (T.FiniteCorner z) := by
  have hc : Convex ℝ (range T.halfPlaneCoordinate) := by
    rw [T.halfPlaneCoordinate_range]
    exact T.openCoordinateDomain_convex
  obtain ⟨t,u,R,_,_,_,_,hR,hiR⟩ := exists_hRayAt_positive_firstAxis
    T.halfPlaneCoordinate T.halfPlaneCoordinate_isOpenEmbedding hc
    (T.halfPlaneCoordinate_at_a ha) T.sideLineC.toHalfPlane T.halfPlaneCoordinate_first_line
  obtain ⟨t,u,S,_,_,_,_,hS,hiS⟩ := exists_hRayAt_positive_secondAxis
    T.halfPlaneCoordinate T.halfPlaneCoordinate_isOpenEmbedding hc
    (T.halfPlaneCoordinate_at_a ha) T.sideLineB.toHalfPlane T.halfPlaneCoordinate_second_line
  exact ⟨⟨R,S,hR,hS,hiR,hiS⟩⟩

def ClosedDiscTriangle.finiteCornerAtA (T : ClosedDiscTriangle) (z : ℍ)
    (ha : T.a = discToClosedModel (halfPlaneToDisc z)) : T.FiniteCorner z :=
  Classical.choice (T.finiteCorner_nonempty z ha)

theorem ClosedDiscTriangle.FiniteCorner.proper {T : ClosedDiscTriangle} {z : ℍ}
    (C : T.FiniteCorner z) : C.rayAB.supportLine ≠ C.rayAC.supportLine := by
  rw [C.supportAB,C.supportAC]
  exact T.sideLineC_toHalfPlane_ne_sideLineB

theorem ClosedDiscTriangle.FiniteCorner.firstSide_image {T : ClosedDiscTriangle} {z : ℍ}
    (C : T.FiniteCorner z) :
    T.halfPlaneCoordinate '' hAngleSide C.rayAB C.rayAC =
      T.openCoordinateDomain ∩ {p : ℝ × ℝ | 0 < p.2} := by
  let F := T.halfPlaneCoordinate
  have hF := T.halfPlaneCoordinate_isOpenEmbedding.isEmbedding
  have hcomp : F '' C.rayAB.supportLine.carrierᶜ =
      T.openCoordinateDomain ∩ {p : ℝ × ℝ | p.2 ≠ 0} := by
    have he : C.rayAB.supportLine.carrierᶜ = F ⁻¹' {p : ℝ × ℝ | p.2 ≠ 0} := by
      ext x
      rw [C.supportAB]
      exact (not_congr (T.halfPlaneCoordinate_first_line x)).symm
    rw [he,image_preimage_eq_inter_range,inter_comm,T.halfPlaneCoordinate_range]
  rw [hAngleSide_eq_component C.rayAB C.rayAC C.proper C.rayAC.directionPoint_mem]
  change F '' connectedComponentIn C.rayAB.supportLine.carrierᶜ C.rayAC.directionPoint = _
  rw [embedding_image_connectedComponentIn hF
    (C.rayAB.punctured_subset_compl_support C.rayAC C.proper C.rayAC.directionPoint_mem),hcomp]
  apply connectedComponentIn_positive_linear_cut T.openCoordinateDomain_convex
    (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hp := mem_image_of_mem T.halfPlaneCoordinate C.rayAC.directionPoint_mem
  rw [C.imageAC] at hp
  exact ⟨T.halfPlaneCoordinate_range ▸ hp.1,hp.2.2⟩

theorem ClosedDiscTriangle.FiniteCorner.secondSide_image {T : ClosedDiscTriangle} {z : ℍ}
    (C : T.FiniteCorner z) :
    T.halfPlaneCoordinate '' hAngleSide C.rayAC C.rayAB =
      T.openCoordinateDomain ∩ {p : ℝ × ℝ | 0 < p.1} := by
  let F := T.halfPlaneCoordinate
  have hF := T.halfPlaneCoordinate_isOpenEmbedding.isEmbedding
  have hcomp : F '' C.rayAC.supportLine.carrierᶜ =
      T.openCoordinateDomain ∩ {p : ℝ × ℝ | p.1 ≠ 0} := by
    have he : C.rayAC.supportLine.carrierᶜ = F ⁻¹' {p : ℝ × ℝ | p.1 ≠ 0} := by
      ext x
      rw [C.supportAC]
      exact (not_congr (T.halfPlaneCoordinate_second_line x)).symm
    rw [he,image_preimage_eq_inter_range,inter_comm,T.halfPlaneCoordinate_range]
  rw [hAngleSide_eq_component C.rayAC C.rayAB (Ne.symm C.proper) C.rayAB.directionPoint_mem]
  change F '' connectedComponentIn C.rayAC.supportLine.carrierᶜ C.rayAB.directionPoint = _
  rw [embedding_image_connectedComponentIn hF
    (C.rayAC.punctured_subset_compl_support C.rayAB (Ne.symm C.proper) C.rayAB.directionPoint_mem),hcomp]
  apply connectedComponentIn_positive_linear_cut T.openCoordinateDomain_convex
    (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hp := mem_image_of_mem T.halfPlaneCoordinate C.rayAB.directionPoint_mem
  rw [C.imageAB] at hp
  exact ⟨T.halfPlaneCoordinate_range ▸ hp.1,hp.2.1⟩

theorem ClosedDiscTriangle.FiniteCorner.interior_image {T : ClosedDiscTriangle} {z : ℍ}
    (C : T.FiniteCorner z) :
    T.halfPlaneCoordinate '' properHAngleInterior C.rayAB C.rayAC =
      T.openCoordinateDomain ∩ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} := by
  rw [properHAngleInterior,image_inter T.halfPlaneCoordinate_isOpenEmbedding.injective,
    C.firstSide_image,C.secondSide_image]
  ext p
  simp only [mem_inter_iff,mem_ofPred]
  tauto


def ClosedDiscTriangle.halfPlaneInterior (T : ClosedDiscTriangle) : Set ℍ :=
  halfPlaneToDisc ⁻¹' T.interior

theorem ClosedDiscTriangle.halfPlaneCoordinate_image_interior (T : ClosedDiscTriangle) :
    T.halfPlaneCoordinate '' T.halfPlaneInterior = standardOpenTriangle := by
  change (T.discCoordinate ∘ halfPlaneToDisc) '' (halfPlaneToDisc ⁻¹' T.interior) = _
  calc
    _ = T.discCoordinate '' (halfPlaneToDisc '' (halfPlaneToDisc ⁻¹' T.interior)) :=
      (image_image T.discCoordinate halfPlaneToDisc _).symm
    _ = _ := by
      rw [show halfPlaneToDisc '' (halfPlaneToDisc ⁻¹' T.interior) = T.interior from
        cayleyHomeomorph.image_preimage _,T.discCoordinate_image_interior]

theorem ClosedDiscTriangle.mem_halfPlaneInterior_iff (T : ClosedDiscTriangle) (x : ℍ) :
    x ∈ T.halfPlaneInterior ↔ 0 < (T.halfPlaneCoordinate x).1 ∧
      0 < (T.halfPlaneCoordinate x).2 ∧
        (T.halfPlaneCoordinate x).1 + (T.halfPlaneCoordinate x).2 < 1 := by
  change x ∈ T.halfPlaneInterior ↔ T.halfPlaneCoordinate x ∈ standardOpenTriangle
  rw [← T.halfPlaneCoordinate_image_interior]
  exact T.halfPlaneCoordinate_isOpenEmbedding.injective.mem_set_image.symm

theorem ClosedDiscTriangle.FiniteCorner.mem_interior_iff {T : ClosedDiscTriangle} {z : ℍ}
    (C : T.FiniteCorner z) (x : ℍ) :
    x ∈ properHAngleInterior C.rayAB C.rayAC ↔
      0 < (T.halfPlaneCoordinate x).1 ∧ 0 < (T.halfPlaneCoordinate x).2 := by
  have he : x ∈ properHAngleInterior C.rayAB C.rayAC ↔
      T.halfPlaneCoordinate x ∈ T.openCoordinateDomain ∩
        {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} := by
    rw [← C.interior_image]
    exact T.halfPlaneCoordinate_isOpenEmbedding.injective.mem_set_image.symm
  rw [he]
  exact and_iff_right (T.halfPlaneCoordinate_range ▸ mem_range_self x)

theorem ClosedDiscTriangle.FiniteCorner.locally_interior {T : ClosedDiscTriangle} {z : ℍ}
    (C : T.FiniteCorner z) (ha : T.a = discToClosedModel (halfPlaneToDisc z)) :
    ∃ r > 0, Metric.ball z r ∩ T.halfPlaneInterior =
      Metric.ball z r ∩ properHAngleInterior C.rayAB C.rayAC := by
  have ho : IsOpen {x : ℍ | (T.halfPlaneCoordinate x).1 +
      (T.halfPlaneCoordinate x).2 < 1} :=
    isOpen_lt ((continuous_fst.comp T.halfPlaneCoordinate_isOpenEmbedding.continuous).add
      (continuous_snd.comp T.halfPlaneCoordinate_isOpenEmbedding.continuous)) continuous_const
  have hz : z ∈ {x : ℍ | (T.halfPlaneCoordinate x).1 +
      (T.halfPlaneCoordinate x).2 < 1} := by
    rw [mem_ofPred,T.halfPlaneCoordinate_at_a ha]
    norm_num
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp ho z hz
  refine ⟨r,hr,?_⟩
  ext x
  rw [mem_inter_iff,mem_inter_iff,T.mem_halfPlaneInterior_iff,C.mem_interior_iff]
  constructor
  · rintro ⟨hx,hx1,hx2,_⟩
    exact ⟨hx,hx1,hx2⟩
  · rintro ⟨hx,hx1,hx2⟩
    exact ⟨hx,hx1,hx2,hsub hx⟩


theorem ClosedDiscTriangle.coordinate_injective (T : ClosedDiscTriangle) :
    Function.Injective T.coordinate := fun _ _ h =>
  closedKleinCoordinate_injective (T.coordinateHomeomorph.injective h)

theorem ClosedDiscTriangle.mem_closedSegment_iff_coordinate (T : ClosedDiscTriangle) (p q x : 𝕔𝔻) :
    x ∈ closedModelDiscHSegment p q ↔ T.coordinate x ∈ segment ℝ (T.coordinate p) (T.coordinate q) := by
  rw [← T.coordinate_image_segment]
  exact T.coordinate_injective.mem_set_image.symm

theorem segment_zero_firstUnit :
    segment ℝ (0 : ℝ × ℝ) (1,0) = {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0} := by
  ext p
  constructor
  · rintro ⟨a,b,ha,hb,hab,hp⟩
    have he : p = (b,0) := by rw [← hp]; ext <;> simp
    rw [he]
    exact ⟨hb,by linarith,rfl⟩
  · rintro ⟨hp0,hp1,hp2⟩
    refine ⟨1-p.1,p.1,by linarith,hp0,by ring,?_⟩
    ext <;> simp_all

theorem segment_zero_secondUnit :
    segment ℝ (0 : ℝ × ℝ) (0,1) = {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ p.1 = 0} := by
  ext p
  constructor
  · rintro ⟨a,b,ha,hb,hab,hp⟩
    have he : p = (0,b) := by rw [← hp]; ext <;> simp
    rw [he]
    exact ⟨hb,by linarith,rfl⟩
  · rintro ⟨hp0,hp1,hp2⟩
    refine ⟨1-p.2,p.2,by linarith,hp0,by ring,?_⟩
    ext <;> simp_all

theorem ClosedDiscTriangle.mem_sideC_iff_coordinate (T : ClosedDiscTriangle) (x : 𝕔𝔻) :
    x ∈ T.sideC ↔ 0 ≤ (T.coordinate x).1 ∧ (T.coordinate x).1 ≤ 1 ∧ (T.coordinate x).2 = 0 := by
  change x ∈ closedModelDiscHSegment T.a T.b ↔ _
  rw [T.mem_closedSegment_iff_coordinate,T.coordinate_a,T.coordinate_b]
  change T.coordinate x ∈ segment ℝ (0 : ℝ × ℝ) (1,0) ↔ _
  rw [segment_zero_firstUnit]
  rfl

theorem ClosedDiscTriangle.mem_sideB_iff_coordinate (T : ClosedDiscTriangle) (x : 𝕔𝔻) :
    x ∈ T.sideB ↔ 0 ≤ (T.coordinate x).2 ∧ (T.coordinate x).2 ≤ 1 ∧ (T.coordinate x).1 = 0 := by
  change x ∈ closedModelDiscHSegment T.c T.a ↔ _
  rw [T.mem_closedSegment_iff_coordinate,T.coordinate_c,T.coordinate_a,segment_symm]
  change T.coordinate x ∈ segment ℝ (0 : ℝ × ℝ) (0,1) ↔ _
  rw [segment_zero_secondUnit]
  rfl

theorem ClosedDiscTriangle.FiniteCorner.sideC_finite_subset {T : ClosedDiscTriangle} {z : ℍ}
    (C : T.FiniteCorner z) (ha : T.a = discToClosedModel (halfPlaneToDisc z)) :
    {x : ℍ | discToClosedModel (halfPlaneToDisc x) ∈ T.sideC} ⊆ C.rayAB.val := by
  intro x hx
  by_cases hxz : x = z
  · exact hxz.symm ▸ C.rayAB.start_mem
  have hp := (T.mem_sideC_iff_coordinate _).mp hx
  change 0 ≤ (T.halfPlaneCoordinate x).1 ∧ (T.halfPlaneCoordinate x).1 ≤ 1 ∧
    (T.halfPlaneCoordinate x).2 = 0 at hp
  have hpos : 0 < (T.halfPlaneCoordinate x).1 := by
    have hne : (T.halfPlaneCoordinate x).1 ≠ 0 := by
      intro he
      apply hxz
      apply T.halfPlaneCoordinate_isOpenEmbedding.injective
      rw [T.halfPlaneCoordinate_at_a ha]
      exact Prod.ext he hp.2.2
    exact lt_of_le_of_ne hp.1 hne.symm
  have him : T.halfPlaneCoordinate x ∈ T.halfPlaneCoordinate '' (C.rayAB.val \ {z}) := by
    rw [C.imageAB]
    exact ⟨mem_range_self x,hpos,hp.2.2⟩
  exact (T.halfPlaneCoordinate_isOpenEmbedding.injective.mem_set_image.mp him).1

theorem ClosedDiscTriangle.FiniteCorner.sideB_finite_subset {T : ClosedDiscTriangle} {z : ℍ}
    (C : T.FiniteCorner z) (ha : T.a = discToClosedModel (halfPlaneToDisc z)) :
    {x : ℍ | discToClosedModel (halfPlaneToDisc x) ∈ T.sideB} ⊆ C.rayAC.val := by
  intro x hx
  by_cases hxz : x = z
  · exact hxz.symm ▸ C.rayAC.start_mem
  have hp := (T.mem_sideB_iff_coordinate _).mp hx
  change 0 ≤ (T.halfPlaneCoordinate x).2 ∧ (T.halfPlaneCoordinate x).2 ≤ 1 ∧
    (T.halfPlaneCoordinate x).1 = 0 at hp
  have hpos : 0 < (T.halfPlaneCoordinate x).2 := by
    have hne : (T.halfPlaneCoordinate x).2 ≠ 0 := by
      intro he
      apply hxz
      apply T.halfPlaneCoordinate_isOpenEmbedding.injective
      rw [T.halfPlaneCoordinate_at_a ha]
      exact Prod.ext hp.2.2 he
    exact lt_of_le_of_ne hp.1 hne.symm
  have him : T.halfPlaneCoordinate x ∈ T.halfPlaneCoordinate '' (C.rayAC.val \ {z}) := by
    rw [C.imageAC]
    exact ⟨mem_range_self x,hp.2.2,hpos⟩
  exact (T.halfPlaneCoordinate_isOpenEmbedding.injective.mem_set_image.mp him).1

def ClosedDiscTriangle.finiteHalfPlaneCornerAtDiscA (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) : T.FiniteCorner (discToHalfPlane z) :=
  T.finiteCornerAtA (discToHalfPlane z) (by rwa [halfPlaneToDisc_discToHalfPlane])

def ClosedDiscTriangle.cornerRayABAtA (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) : DiscRayAt z :=
  (T.finiteHalfPlaneCornerAtDiscA z ha).rayAB.toDiscAt z

def ClosedDiscTriangle.cornerRayACAtA (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) : DiscRayAt z :=
  (T.finiteHalfPlaneCornerAtDiscA z ha).rayAC.toDiscAt z

theorem ClosedDiscTriangle.cornerRayABAtA_toHalfPlane (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) :
    (T.cornerRayABAtA z ha).toHalfPlane = (T.finiteHalfPlaneCornerAtDiscA z ha).rayAB :=
  (discRayHalfPlaneEquiv z).apply_symm_apply _

theorem ClosedDiscTriangle.cornerRayACAtA_toHalfPlane (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) :
    (T.cornerRayACAtA z ha).toHalfPlane = (T.finiteHalfPlaneCornerAtDiscA z ha).rayAC :=
  (discRayHalfPlaneEquiv z).apply_symm_apply _

theorem ClosedDiscTriangle.cornerRayABAtA_support (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) : (T.cornerRayABAtA z ha).supportLine = T.sideLineC := by
  rw [DiscRayAt.supportLine,T.cornerRayABAtA_toHalfPlane,
    (T.finiteHalfPlaneCornerAtDiscA z ha).supportAB,T.sideLineC.toHalfPlane_spec]

theorem ClosedDiscTriangle.cornerRayACAtA_support (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) : (T.cornerRayACAtA z ha).supportLine = T.sideLineB := by
  rw [DiscRayAt.supportLine,T.cornerRayACAtA_toHalfPlane,
    (T.finiteHalfPlaneCornerAtDiscA z ha).supportAC,T.sideLineB.toHalfPlane_spec]

theorem ClosedDiscTriangle.cornerAtA_proper (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) :
    (T.cornerRayABAtA z ha).supportLine ≠ (T.cornerRayACAtA z ha).supportLine := by
  rw [T.cornerRayABAtA_support,T.cornerRayACAtA_support]
  exact T.sideLineC_ne_sideLineB


theorem ClosedDiscTriangle.cornerAtA_sideC_finite_subset (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) :
    {x : 𝔻 | discToClosedModel x ∈ T.sideC} ⊆ (T.cornerRayABAtA z ha).val := by
  intro x hx
  have hh : discToHalfPlane x ∈ (T.finiteHalfPlaneCornerAtDiscA z ha).rayAB.val := by
    apply (T.finiteHalfPlaneCornerAtDiscA z ha).sideC_finite_subset
      (by rwa [halfPlaneToDisc_discToHalfPlane])
    change discToClosedModel (halfPlaneToDisc (discToHalfPlane x)) ∈ T.sideC
    rwa [halfPlaneToDisc_discToHalfPlane]
  exact ⟨discToHalfPlane x,hh,halfPlaneToDisc_discToHalfPlane x⟩

theorem ClosedDiscTriangle.cornerAtA_sideB_finite_subset (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) :
    {x : 𝔻 | discToClosedModel x ∈ T.sideB} ⊆ (T.cornerRayACAtA z ha).val := by
  intro x hx
  have hh : discToHalfPlane x ∈ (T.finiteHalfPlaneCornerAtDiscA z ha).rayAC.val := by
    apply (T.finiteHalfPlaneCornerAtDiscA z ha).sideB_finite_subset
      (by rwa [halfPlaneToDisc_discToHalfPlane])
    change discToClosedModel (halfPlaneToDisc (discToHalfPlane x)) ∈ T.sideB
    rwa [halfPlaneToDisc_discToHalfPlane]
  exact ⟨discToHalfPlane x,hh,halfPlaneToDisc_discToHalfPlane x⟩

theorem ClosedDiscTriangle.cornerAtA_interior_cayley (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) :
    properDiscAngleInterior (T.cornerRayABAtA z ha) (T.cornerRayACAtA z ha) =
      halfPlaneToDisc '' properHAngleInterior (T.finiteHalfPlaneCornerAtDiscA z ha).rayAB
        (T.finiteHalfPlaneCornerAtDiscA z ha).rayAC := by
  rw [properDiscAngleInterior,T.cornerRayABAtA_toHalfPlane,T.cornerRayACAtA_toHalfPlane]

theorem ClosedDiscTriangle.cornerAtA_locally_interior (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) :
    let := discHyperbolicMetric
    ∃ r > 0, Metric.ball z r ∩ T.interior = Metric.ball z r ∩
      properDiscAngleInterior (T.cornerRayABAtA z ha) (T.cornerRayACAtA z ha) := by
  let := discHyperbolicMetric
  obtain ⟨r,hr,he⟩ := (T.finiteHalfPlaneCornerAtDiscA z ha).locally_interior
    (by rwa [halfPlaneToDisc_discToHalfPlane])
  have hi : halfPlaneToDisc '' T.halfPlaneInterior = T.interior := cayleyHomeomorph.image_preimage _
  have him := congrArg (fun U : Set ℍ => halfPlaneToDisc '' U) he
  rw [image_inter (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective),
    image_inter (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective),
    cayley_image_ball_at_disc,hi,← T.cornerAtA_interior_cayley] at him
  exact ⟨r,hr,him⟩

def ClosedDiscTriangle.cornerAngleAtA (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) : DiscAngle z :=
  s(T.cornerRayABAtA z ha,T.cornerRayACAtA z ha)

theorem ClosedDiscTriangle.cornerAngleAtA_interior (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) :
    (T.cornerAngleAtA z ha).interior =
      some (properDiscAngleInterior (T.cornerRayABAtA z ha) (T.cornerRayACAtA z ha)) :=
  discAngleInteriorPair_proper _ _ (T.cornerAtA_proper z ha)

end
end LowDimensionalTopology.Geometry.Hyperbolic
